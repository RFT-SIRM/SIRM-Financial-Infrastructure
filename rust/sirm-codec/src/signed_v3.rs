//! Signed-request layer v3 (proposal, not adopted): the v2 suite registry carrying request
//! encoding v2 (`crate::request_v2`: v1 plus the arbiter operation `resolve`). Reference:
//! `scripts/signed_request_v3_reference.py`; vectors:
//! `engineering/canonical_encoding/results/signed_request_v3_vectors.json`; spec:
//! `engineering/canonical_encoding/SPEC_signed_request_v3.md`.
//!
//! ```text
//! key id:          SHA-256("SIRM/KID/v1\0" | suite u16 | public key)
//! signing message: "SIRM/SIG/v3\0" (12) | chain id u64 | suite u16 | key id (32) | request encoding v2
//! wire format:     "SIRM/SRQ/v3\0" (12) | chain id u64 | suite u16 | request encoding v2 | signature
//! ```
//!
//! Verification order: wire domain, suite known, wire length, operation tag, request decode, chain
//! equals the node's, principal has a registered key, suite matches the registered key, suite allowed,
//! signature. Any failure stops before the machine.
//!
//! **Only Ed25519 (suite 0x0001, deprecated) is verified here.** ML-DSA-65 and the hybrid have no
//! verifier in this crate (no post-quantum library has been chosen, see
//! `docs/PQ_RUST_LIBRARY_EVALUATION.md`): after every structural check they return
//! [`SignedError::VerifierUnavailable`], which is a rejection, never an acceptance. The structure,
//! the downgrade defence and every check before the signature are identical for all suites.

use crate::integrated::{Machine, Outcome};
use crate::request_v2::{decode as decode_request, encoded_len, DecodeError, WireRequest};
use ed25519_dalek::{Signature, VerifyingKey};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;

pub const SIG_DOMAIN: [u8; 12] = *b"SIRM/SIG/v3\0";
pub const WIRE_DOMAIN: [u8; 12] = *b"SIRM/SRQ/v3\0";
const KID_DOMAIN: &[u8] = b"SIRM/KID/v1\0";
/// Offset of the operation tag in the wire: wire header 22, request domain 12, id 32, principal 4, nonce 8.
const TAG_AT: usize = 22 + 12 + 32 + 4 + 8;

pub const ED25519: u16 = 0x0001;
pub const ML_DSA_65: u16 = 0x0002;
pub const HYBRID: u16 = 0x0101;
pub const SLH_DSA_128S: u16 = 0x0003;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Status {
    Proposed,
    Active,
    Deprecated,
}

/// (public key length, signature length, status) of a known suite.
pub fn suite_info(suite: u16) -> Option<(usize, usize, Status)> {
    Some(match suite {
        ED25519 => (32, 64, Status::Deprecated),
        ML_DSA_65 => (1952, 3309, Status::Active),
        HYBRID => (32 + 1952, 64 + 3309, Status::Active),
        SLH_DSA_128S => (32, 7856, Status::Proposed),
        _ => return None,
    })
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SignedError {
    BadDomain,
    Truncated,
    UnknownSuite,
    UnknownOperation(u8),
    TrailingBytes,
    BadRequest(DecodeError),
    WrongChain,
    UnknownPrincipal,
    SuiteMismatch,
    SuiteNotAllowed,
    BadSignature,
    /// The suite is well formed and allowed but this crate has no verifier for it: rejected.
    VerifierUnavailable,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvalidKey;

#[derive(Debug, Clone, Default)]
pub struct KeyRegistry {
    keys: BTreeMap<u32, (u16, Vec<u8>)>,
}

impl KeyRegistry {
    pub fn new() -> KeyRegistry {
        KeyRegistry::default()
    }

    /// Registers a key for a principal. The suite must be known, the key length must match and an
    /// Ed25519 key must be a valid curve point.
    pub fn insert(&mut self, principal: u32, suite: u16, public: &[u8]) -> Result<(), InvalidKey> {
        let (pk_len, _, _) = suite_info(suite).ok_or(InvalidKey)?;
        if public.len() != pk_len {
            return Err(InvalidKey);
        }
        if suite == ED25519 {
            let arr: [u8; 32] = public.try_into().map_err(|_| InvalidKey)?;
            VerifyingKey::from_bytes(&arr).map_err(|_| InvalidKey)?;
        }
        self.keys.insert(principal, (suite, public.to_vec()));
        Ok(())
    }

    pub fn get(&self, principal: u32) -> Option<(u16, &[u8])> {
        self.keys.get(&principal).map(|(s, k)| (*s, k.as_slice()))
    }
}

pub fn key_id(suite: u16, public: &[u8]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(KID_DOMAIN);
    h.update(suite.to_be_bytes());
    h.update(public);
    h.finalize().into()
}

/// The bytes that are signed (request bytes are the request encoding v2).
pub fn signing_message(chain: u64, suite: u16, key_id: &[u8; 32], request: &[u8]) -> Vec<u8> {
    let mut v = SIG_DOMAIN.to_vec();
    v.extend_from_slice(&chain.to_be_bytes());
    v.extend_from_slice(&suite.to_be_bytes());
    v.extend_from_slice(key_id);
    v.extend_from_slice(request);
    v
}

pub fn encode_wire(chain: u64, suite: u16, request: &[u8], signature: &[u8]) -> Vec<u8> {
    let mut v = WIRE_DOMAIN.to_vec();
    v.extend_from_slice(&chain.to_be_bytes());
    v.extend_from_slice(&suite.to_be_bytes());
    v.extend_from_slice(request);
    v.extend_from_slice(signature);
    v
}

pub fn verify(
    wire: &[u8],
    expected_chain: u64,
    keys: &KeyRegistry,
    allow_deprecated: bool,
) -> Result<WireRequest, SignedError> {
    if !wire.starts_with(&WIRE_DOMAIN) {
        return Err(SignedError::BadDomain);
    }
    if wire.len() < 22 {
        return Err(SignedError::Truncated);
    }
    let suite = u16::from_be_bytes([wire[20], wire[21]]);
    let (_, sig_len, status) = suite_info(suite).ok_or(SignedError::UnknownSuite)?;
    if wire.len() <= TAG_AT {
        return Err(SignedError::Truncated);
    }
    let tag = wire[TAG_AT];
    let end = 22 + encoded_len(tag).ok_or(SignedError::UnknownOperation(tag))?;
    if wire.len() < end + sig_len {
        return Err(SignedError::Truncated);
    }
    if wire.len() > end + sig_len {
        return Err(SignedError::TrailingBytes);
    }
    let request = decode_request(&wire[22..end]).map_err(SignedError::BadRequest)?;
    let chain = u64::from_be_bytes(wire[12..20].try_into().unwrap());
    if chain != expected_chain {
        return Err(SignedError::WrongChain);
    }
    let (reg_suite, public) = keys
        .get(request.request.principal)
        .ok_or(SignedError::UnknownPrincipal)?;
    if suite != reg_suite {
        return Err(SignedError::SuiteMismatch);
    }
    if !(status == Status::Active || (status == Status::Deprecated && allow_deprecated)) {
        return Err(SignedError::SuiteNotAllowed);
    }
    if suite != ED25519 {
        return Err(SignedError::VerifierUnavailable);
    }
    let message = signing_message(chain, suite, &key_id(suite, public), &wire[22..end]);
    let key = VerifyingKey::from_bytes(public.try_into().unwrap())
        .map_err(|_| SignedError::BadSignature)?;
    let signature = Signature::from_bytes(wire[end..].try_into().unwrap());
    key.verify_strict(&message, &signature)
        .map_err(|_| SignedError::BadSignature)?;
    Ok(request)
}

/// A node: one chain id, a key registry and the integrated machine. Only requests that verify reach
/// the machine.
#[derive(Debug, Clone)]
pub struct Node {
    pub chain_id: u64,
    pub keys: KeyRegistry,
    pub allow_deprecated: bool,
    pub machine: Machine,
}

impl Node {
    pub fn submit(&mut self, wire: &[u8]) -> Result<Outcome, SignedError> {
        let w = verify(wire, self.chain_id, &self.keys, self.allow_deprecated)?;
        Ok(self.machine.process(w.request_id, w.request))
    }
}
