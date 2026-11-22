//! Signed-request layer v0 (checked by SIRM): chain id binding and an Ed25519
//! signature in front of the request encoding. Executable reference:
//! `scripts/signed_request_reference.py`; vectors:
//! `engineering/canonical_encoding/results/signed_request_vectors_v0.json`.
//!
//! ```text
//! signing message: "SIRM/SIG/v0\0" (12) | chain_id u64 | request encoding (85 | 81)
//! wire format:     "SIRM/SRQ/v0\0" (12) | chain_id u64 | request encoding | signature (64)
//! ```
//!
//! The public key is not in the message: the node's [`KeyRegistry`] maps each principal to its
//! key. Verification order: wire decode, request decode, chain id equals the node's, key exists
//! for the principal, strict signature check (`verify_strict`: also rejects non-canonical `S`
//! and small-order keys). Any failure stops before the processor: no receipt, no cache entry,
//! no nonce change. Replay protection stays with the processor (request ID and nonce).
//!
//! This layer has no counterpart in Lean, which abstracts "the principal acts" in its
//! authorization policy; here it is an explicit assumption-discharging step in front of that
//! model. Key custody, rotation, revocation, thresholds and expiry are not modelled.

use crate::machine::{self, Outcome, Processor};
use crate::{decode as decode_request, encode as encode_request, DecodeError, Op, Request};
use ed25519_dalek::{Signature, VerifyingKey};
use std::collections::BTreeMap;

pub const SIG_DOMAIN: [u8; 12] = *b"SIRM/SIG/v0\0";
pub const WIRE_DOMAIN: [u8; 12] = *b"SIRM/SRQ/v0\0";
pub const SIGNATURE_LEN: usize = 64;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SignedError {
    BadDomain,
    Truncated,
    TrailingBytes,
    UnknownOperation(u8),
    BadRequest(DecodeError),
    WrongChain,
    UnknownPrincipal,
    BadSignature,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvalidPublicKey;

/// Principal index to Ed25519 verifying key.
#[derive(Debug, Clone, Default)]
pub struct KeyRegistry {
    keys: BTreeMap<u32, VerifyingKey>,
}

impl KeyRegistry {
    pub fn new() -> KeyRegistry {
        KeyRegistry::default()
    }

    /// Rejects byte strings that are not a valid curve point.
    pub fn insert(&mut self, principal: u32, public: [u8; 32]) -> Result<(), InvalidPublicKey> {
        let key = VerifyingKey::from_bytes(&public).map_err(|_| InvalidPublicKey)?;
        self.keys.insert(principal, key);
        Ok(())
    }

    pub fn get(&self, principal: u32) -> Option<&VerifyingKey> {
        self.keys.get(&principal)
    }
}

/// The exact bytes that are signed.
pub fn signing_message(chain_id: u64, request: &Request) -> Vec<u8> {
    let mut out = Vec::with_capacity(12 + 8 + 85);
    out.extend_from_slice(&SIG_DOMAIN);
    out.extend_from_slice(&chain_id.to_be_bytes());
    out.extend_from_slice(&encode_request(request));
    out
}

/// The transmitted bytes for a request already signed over [`signing_message`].
pub fn encode_wire(chain_id: u64, request: &Request, signature: &[u8; SIGNATURE_LEN]) -> Vec<u8> {
    let mut out = Vec::with_capacity(12 + 8 + 85 + SIGNATURE_LEN);
    out.extend_from_slice(&WIRE_DOMAIN);
    out.extend_from_slice(&chain_id.to_be_bytes());
    out.extend_from_slice(&encode_request(request));
    out.extend_from_slice(signature);
    out
}

/// Verify a wire message for the node's `expected_chain`; returns the authenticated request.
pub fn verify(
    bytes: &[u8],
    expected_chain: u64,
    keys: &KeyRegistry,
) -> Result<Request, SignedError> {
    if !bytes.starts_with(&WIRE_DOMAIN) {
        return Err(SignedError::BadDomain);
    }
    let start = WIRE_DOMAIN.len() + 8;
    // request domain 12 + request id 32 + principal 4 + nonce 8, then the operation tag
    let tag_at = start + 12 + 32 + 4 + 8;
    if bytes.len() <= tag_at {
        return Err(SignedError::Truncated);
    }
    let req_len = match bytes[tag_at] {
        0 | 1 => 85,
        2 => 81,
        t => return Err(SignedError::UnknownOperation(t)),
    };
    let end = start + req_len;
    if bytes.len() < end + SIGNATURE_LEN {
        return Err(SignedError::Truncated);
    }
    if bytes.len() > end + SIGNATURE_LEN {
        return Err(SignedError::TrailingBytes);
    }
    let chain = u64::from_be_bytes(bytes[WIRE_DOMAIN.len()..start].try_into().unwrap());
    let request = decode_request(&bytes[start..end]).map_err(SignedError::BadRequest)?;
    if chain != expected_chain {
        return Err(SignedError::WrongChain);
    }
    let key = keys
        .get(request.principal)
        .ok_or(SignedError::UnknownPrincipal)?;
    let signature = Signature::from_bytes(bytes[end..].try_into().unwrap());
    key.verify_strict(&signing_message(chain, &request), &signature)
        .map_err(|_| SignedError::BadSignature)?;
    Ok(request)
}

fn to_machine(r: &Request) -> (machine::RequestId, machine::Request) {
    let operation = match r.op {
        Op::Transfer {
            source,
            destination,
            asset,
            amount,
        } => machine::Operation::Transfer {
            source,
            destination,
            asset,
            amount,
        },
        Op::Issue {
            issuer,
            recipient,
            asset,
            amount,
        } => machine::Operation::Issue {
            issuer,
            recipient,
            asset,
            amount,
        },
        Op::Burn {
            holder,
            asset,
            amount,
        } => machine::Operation::Burn {
            holder,
            asset,
            amount,
        },
    };
    (
        r.request_id,
        machine::Request {
            principal: r.principal,
            nonce: r.nonce,
            operation,
        },
    )
}

/// A node: one chain id, a key registry and the integrated processor. Only requests that
/// verify reach the processor.
#[derive(Debug, Clone)]
pub struct Node {
    pub chain_id: u64,
    pub keys: KeyRegistry,
    pub processor: Processor,
}

impl Node {
    pub fn submit(&mut self, wire: &[u8]) -> Result<Outcome, SignedError> {
        let request = verify(wire, self.chain_id, &self.keys)?;
        let (id, req) = to_machine(&request);
        Ok(self.processor.process(id, req))
    }
}
