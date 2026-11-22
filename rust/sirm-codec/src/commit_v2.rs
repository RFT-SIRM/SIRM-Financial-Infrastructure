//! State commitment v2 (checked by SIRM): the v1 root plus the request-id cache (receipts
//! and cached denials), the authorization policy (grants and account control) and the
//! account/asset registry. Reference: `scripts/state_commitment_v2_reference.py`; vectors:
//! `engineering/canonical_encoding/results/state_commitment_v2_vectors.json`.
//!
//! These components are committed as **ordered list hashes**, not sparse trees: there is no
//! inclusion proof for them, and request ids are 32 bytes, wider than the tree key.
//!
//! ```text
//! cache entry  = request id 32 | principal u32 | nonce u64 | op u8 (0 transfer, 1 issue, 2 burn)
//!                | a u32 | b u32 | asset u32 | amount u128 | stored tag u8 (0 accepted, 1 denied)
//!                | u64 | u64          (accepted: accepted nonce, next nonce;
//!                                      denied: expected nonce, reason code 0..4)
//! cache commit = SHA256("SIRM/CAC/v2\0" | count u64 | entries ascending by request id)
//! grant entry  = principal u32 | scope u8 | a u32 | b u32 | asset u32 | limit u128
//!                (transfer: source, destination; issue: issuer, recipient; burn: holder, 0)
//! policy commit = SHA256("SIRM/POL/v2\0" | n u64 | grant entries ascending bytewise
//!                        | m u64 | control entries (principal u32 | account u32) ascending bytewise)
//! account meta = class u8 | status u8 | network u32
//! asset meta   = symbol len u32 | symbol utf8 | decimals u32 | issuer u32 | status u8 | network u32
//! registry commit = SHA256("SIRM/REG/v2\0" | n u32 | account metas by index | m u32 | asset metas by index)
//! state root v2 = SHA256("SIRM/STC/v2\0" | accounts u32 | assets u32 | balance root | supply root
//!                        | nonce root | key root | header hash | cache | policy | registry)
//! ```
//!
//! Still not covered: fee parameters, governance state, escrow, time-lock, dispute, migration and
//! residual state, threshold policies. Not a commitment to the complete protocol state. No Lean
//! counterpart.

use crate::auth::{Policy, Scope};
use crate::commit::{root, state_trees, Hash};
use crate::commit_v1::{header_hash, key_root, suite_root, Header, KeyAccount, SuiteEntry};
use crate::machine::{DenialReason, Operation, Processor, Stored};
use crate::registry::{AccountMeta, AssetMeta, Registry};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;

const D_STATE: &[u8] = b"SIRM/STC/v2\0";
const D_CACHE: &[u8] = b"SIRM/CAC/v2\0";
const D_POL: &[u8] = b"SIRM/POL/v2\0";
const D_REG: &[u8] = b"SIRM/REG/v2\0";

fn sha(parts: &[&[u8]]) -> Hash {
    let mut s = Sha256::new();
    for p in parts {
        s.update(p);
    }
    s.finalize().into()
}

fn reason_code(r: DenialReason) -> u64 {
    match r {
        DenialReason::TransferAuthorizationDenied => 0,
        DenialReason::IssueAuthorizationDenied => 1,
        DenialReason::BurnAuthorizationDenied => 2,
        DenialReason::TransferInsufficientFunds => 3,
        DenialReason::BurnInsufficientFunds => 4,
    }
}

pub fn cache_entry(id: &[u8; 32], req: &crate::machine::Request, stored: &Stored) -> Vec<u8> {
    let (op, a, b, asset, amount) = match req.operation {
        Operation::Transfer {
            source,
            destination,
            asset,
            amount,
        } => (0u8, source, destination, asset, amount),
        Operation::Issue {
            issuer,
            recipient,
            asset,
            amount,
        } => (1, issuer, recipient, asset, amount),
        Operation::Burn {
            holder,
            asset,
            amount,
        } => (2, holder, 0, asset, amount),
    };
    let mut v = id.to_vec();
    v.extend_from_slice(&req.principal.to_be_bytes());
    v.extend_from_slice(&req.nonce.to_be_bytes());
    v.push(op);
    for x in [a, b, asset] {
        v.extend_from_slice(&x.to_be_bytes());
    }
    v.extend_from_slice(&amount.to_be_bytes());
    let (tag, x, y) = match stored {
        Stored::Accepted {
            accepted_nonce,
            next_nonce,
        } => (0u8, *accepted_nonce, *next_nonce),
        Stored::Denied {
            expected_nonce,
            reason,
        } => (1, *expected_nonce, reason_code(*reason)),
    };
    v.push(tag);
    v.extend_from_slice(&x.to_be_bytes());
    v.extend_from_slice(&y.to_be_bytes());
    v
}

pub fn cache_commit(p: &Processor) -> Hash {
    let entries: Vec<Vec<u8>> = p
        .cache_entries()
        .map(|(id, r, s)| cache_entry(id, r, s))
        .collect(); // BTreeMap order: ascending request id
    let mut s = Sha256::new();
    s.update(D_CACHE);
    s.update((entries.len() as u64).to_be_bytes());
    for e in &entries {
        s.update(e);
    }
    s.finalize().into()
}

pub fn grant_entry(principal: u32, scope: Scope, asset: u32, limit: u128) -> Vec<u8> {
    let (tag, a, b) = match scope {
        Scope::Transfer {
            source,
            destination,
        } => (0u8, source, destination),
        Scope::Issue { issuer, recipient } => (1, issuer, recipient),
        Scope::Burn { holder } => (2, holder, 0),
    };
    let mut v = principal.to_be_bytes().to_vec();
    v.push(tag);
    for x in [a, b, asset] {
        v.extend_from_slice(&x.to_be_bytes());
    }
    v.extend_from_slice(&limit.to_be_bytes());
    v
}

pub fn policy_commit(policy: &Policy) -> Hash {
    // Sorted bytewise, independent of the in-memory key order.
    let mut gs: Vec<Vec<u8>> = policy
        .grants()
        .map(|(p, s, a, m)| grant_entry(p, s, a, m))
        .collect();
    gs.sort();
    let mut cs: Vec<Vec<u8>> = policy
        .control_pairs()
        .map(|(p, a)| [p.to_be_bytes(), a.to_be_bytes()].concat())
        .collect();
    cs.sort();
    let mut s = Sha256::new();
    s.update(D_POL);
    s.update((gs.len() as u64).to_be_bytes());
    for g in &gs {
        s.update(g);
    }
    s.update((cs.len() as u64).to_be_bytes());
    for c in &cs {
        s.update(c);
    }
    s.finalize().into()
}

pub fn account_meta(a: &AccountMeta) -> Vec<u8> {
    let mut v = vec![a.class as u8, a.status as u8];
    v.extend_from_slice(&a.network.0.to_be_bytes());
    v
}

pub fn asset_meta(a: &AssetMeta) -> Vec<u8> {
    let mut v = (a.symbol.len() as u32).to_be_bytes().to_vec();
    v.extend_from_slice(a.symbol.as_bytes());
    v.extend_from_slice(&a.decimals.to_be_bytes());
    v.extend_from_slice(&a.issuer.to_be_bytes());
    v.push(a.status as u8);
    v.extend_from_slice(&a.network.0.to_be_bytes());
    v
}

pub fn registry_commit(r: &Registry) -> Hash {
    let mut s = Sha256::new();
    s.update(D_REG);
    s.update((r.accounts().len() as u32).to_be_bytes());
    for a in r.accounts() {
        s.update(account_meta(a));
    }
    s.update((r.assets().len() as u32).to_be_bytes());
    for a in r.assets() {
        s.update(asset_meta(a));
    }
    s.finalize().into()
}

pub fn state_root_v2(
    p: &Processor,
    header: &Header,
    suites: &BTreeMap<u16, SuiteEntry>,
    keys: &BTreeMap<u32, KeyAccount>,
    registry: &Registry,
) -> Hash {
    let (bal, sup, non) = state_trees(p);
    sha(&[
        D_STATE,
        &p.ledger.accounts().to_be_bytes(),
        &p.ledger.assets().to_be_bytes(),
        &root(&bal),
        &root(&sup),
        &root(&non),
        &key_root(keys),
        &header_hash(header, &suite_root(suites)),
        &cache_commit(p),
        &policy_commit(p.policy()),
        &registry_commit(registry),
    ])
}
