//! State commitment v1 (proposal, not adopted): the v0 root (balances, supply, nonces) plus the
//! key registry, the suite registry and a protocol header. Reference:
//! `scripts/state_commitment_v1_reference.py`; vectors:
//! `engineering/canonical_encoding/results/state_commitment_v1_vectors.json`.
//!
//! ```text
//! suite value = kind u8 | status u8 | pk_len u32 | sig_len u32 | activation u64
//!               | deprecation u64 | disable u64                    (34 bytes; no height = u64::MAX)
//! key value   = suite u16 | key id 32 | flags u8 (1 frozen, 2 revoked, 4 pq bound)
//!               | recovery flag u8 | recovery key id 32 | pending flag u8 | pending key id 32
//!               | pending start u64                                (109 bytes; absent = zero fill)
//! header hash = SHA256("SIRM/HDR/v1\0" | chain id u64 | version u16 | hash suite u16 | suite root)
//! state root  = SHA256("SIRM/STC/v1\0" | accounts u32 | assets u32 | balance root | supply root
//!                      | nonce root | key root | header hash)
//! ```
//!
//! Not covered (still outside any root): receipts and the request-id cache, account and asset
//! registries, authorization grants and account control, fee parameters, governance state,
//! escrow, time-lock, dispute, migration and residual state. This is not a commitment to the
//! complete protocol state. No Lean counterpart.

use crate::commit::{root, state_trees, Hash};
use crate::machine::Processor;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;

const D_STATE: &[u8] = b"SIRM/STC/v1\0";
const D_HDR: &[u8] = b"SIRM/HDR/v1\0";
pub const NO_HEIGHT: u64 = u64::MAX;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SuiteEntry {
    pub kind: u8,
    pub status: u8,
    pub pk_len: u32,
    pub sig_len: u32,
    pub activation: u64,
    pub deprecation: u64,
    pub disable: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KeyAccount {
    pub suite: u16,
    pub key_id: [u8; 32],
    pub frozen: bool,
    pub revoked: bool,
    pub pq_bound: bool,
    pub recovery: Option<[u8; 32]>,
    pub pending: Option<([u8; 32], u64)>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Header {
    pub chain_id: u64,
    pub version: u16,
    pub hash_suite: u16,
}

pub fn suite_value(e: &SuiteEntry) -> Vec<u8> {
    let mut v = vec![e.kind, e.status];
    v.extend_from_slice(&e.pk_len.to_be_bytes());
    v.extend_from_slice(&e.sig_len.to_be_bytes());
    for x in [e.activation, e.deprecation, e.disable] {
        v.extend_from_slice(&x.to_be_bytes());
    }
    v
}

pub fn key_value(a: &KeyAccount) -> Vec<u8> {
    let mut v = a.suite.to_be_bytes().to_vec();
    v.extend_from_slice(&a.key_id);
    v.push(u8::from(a.frozen) | (u8::from(a.revoked) << 1) | (u8::from(a.pq_bound) << 2));
    match a.recovery {
        Some(r) => {
            v.push(1);
            v.extend_from_slice(&r);
        }
        None => v.extend_from_slice(&[0u8; 33]),
    }
    match a.pending {
        Some((k, start)) => {
            v.push(1);
            v.extend_from_slice(&k);
            v.extend_from_slice(&start.to_be_bytes());
        }
        None => v.extend_from_slice(&[0u8; 41]),
    }
    v
}

pub fn suite_root(suites: &BTreeMap<u16, SuiteEntry>) -> Hash {
    let m: BTreeMap<u64, Vec<u8>> = suites
        .iter()
        .map(|(k, e)| (*k as u64, suite_value(e)))
        .collect();
    root(&m)
}

pub fn key_root(keys: &BTreeMap<u32, KeyAccount>) -> Hash {
    let m: BTreeMap<u64, Vec<u8>> = keys
        .iter()
        .map(|(k, a)| (*k as u64, key_value(a)))
        .collect();
    root(&m)
}

pub fn header_hash(h: &Header, suite_root: &Hash) -> Hash {
    let mut s = Sha256::new();
    s.update(D_HDR);
    s.update(h.chain_id.to_be_bytes());
    s.update(h.version.to_be_bytes());
    s.update(h.hash_suite.to_be_bytes());
    s.update(suite_root);
    s.finalize().into()
}

pub fn state_root_v1(
    p: &Processor,
    header: &Header,
    suites: &BTreeMap<u16, SuiteEntry>,
    keys: &BTreeMap<u32, KeyAccount>,
) -> Hash {
    let (bal, sup, non) = state_trees(p);
    let mut s = Sha256::new();
    s.update(D_STATE);
    s.update(p.ledger.accounts().to_be_bytes());
    s.update(p.ledger.assets().to_be_bytes());
    s.update(root(&bal));
    s.update(root(&sup));
    s.update(root(&non));
    s.update(key_root(keys));
    s.update(header_hash(header, &suite_root(suites)));
    s.finalize().into()
}
