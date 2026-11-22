//! State commitment v5 (checked by SIRM): one commitment for the integrated state machine
//! (`crate::integrated`), which has a single shared ledger. Reference:
//! `scripts/state_commitment_v5_reference.py`; vectors:
//! `engineering/canonical_encoding/results/state_commitment_v5_vectors.json`.
//!
//! ```text
//! state root v5 = SHA256("SIRM/STC/v5\0" | accounts u32 | assets u32 | balance root | supply root
//!                        | nonce root | config | cache | escrow | now u64
//!                        | total source u128 | total target u128 | dust u128)
//! config        = SHA256("SIRM/CFG/v5\0" | accounts u32 | assets u32 | vault flag u8 + u32
//!                        | n u32 + deadlines u64 | migration flag u8 + holder u32 + recipient u32
//!                        + source u32 + destination u32 + numerator u128 + denominator u128
//!                        | controls | limits | ids | clock)
//!                 each policy list: n u32 + entries sorted bytewise
//!                 control (principal u32, account u32); limit (principal u32, tag u8, a u32,
//!                 b flag u8 + u32, asset u32, limit u128); id (principal u32, tag u8, id u32);
//!                 clock principal u32
//! cache         = SHA256("SIRM/CAC/v5\0" | n u32 | entries by request id)
//!                 entry = request encoding v1 (id included) | stored outcome (11 bytes)
//!                 stored = flag u8 (1 accepted, 2 denied) | kind tag u8 | cause u8 | nonce u64
//!                 (accepted: the nonce consumed, kind and cause 0; denied: the expected nonce)
//! escrow        = SHA256("SIRM/ESC/v5\0" | n u32 | n id entries)   (entry as in v3, 55 bytes)
//! ```
//!
//! Balance, supply and nonce roots are the sparse trees of v0; the escrow vault is an ordinary
//! account of the shared ledger. The migration totals are zero when no stream is configured.
//!
//! A cached request whose escrow id does not fit in `u32` cannot be encoded; the root is then `None`.
//! The same holds for a cached `resolve` request: request encoding v1 has no resolve operation yet,
//! so a machine that has seen one has no state root until a later encoding version exists (the kind
//! tag 10 and the cause code 15 are reserved for it).
//! Inclusion proofs exist only for the three trees; the other parts are list hashes. Not a
//! commitment to the complete protocol state (no keys, suites, registry, governance).

use crate::commit::{root, Hash};
use crate::commit_v3::holdings_roots;
use crate::integrated::{Cause, Kind, Machine, Stored};
use crate::request_v1::{encode, WireRequest};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;

const D_STATE: &[u8] = b"SIRM/STC/v5\0";
const D_CFG: &[u8] = b"SIRM/CFG/v5\0";
const D_CAC: &[u8] = b"SIRM/CAC/v5\0";
const D_ESC: &[u8] = b"SIRM/ESC/v5\0";

fn kind_tag(k: Kind) -> u8 {
    match k {
        Kind::Transfer => 0,
        Kind::Issue => 1,
        Kind::Burn => 2,
        Kind::Open => 3,
        Kind::Release => 4,
        Kind::Cancel => 5,
        Kind::Expire => 6,
        Kind::Dispute => 7,
        Kind::Advance => 8,
        Kind::Migrate => 9,
        Kind::Resolve => 10,
    }
}

fn cause_code(c: Cause) -> u8 {
    match c {
        Cause::Auth => 0,
        Cause::Reserved => 1,
        Cause::VaultOrOverflow => 2,
        Cause::Frozen => 3,
        Cause::UnknownId => 4,
        Cause::IdInUse => 5,
        Cause::NotPending => 6,
        Cause::DeadlinePassed => 7,
        Cause::DeadlineNotReached => 8,
        Cause::ZeroAmount => 9,
        Cause::UnknownAccount => 10,
        Cause::Insufficient => 11,
        Cause::TimeNotForward => 12,
        Cause::AlreadyFiled => 13,
        Cause::ClaimantNotParty => 14,
        Cause::NotDisputed => 15,
    }
}

fn sha(parts: &[&[u8]]) -> Hash {
    let mut s = Sha256::new();
    for p in parts {
        s.update(p);
    }
    s.finalize().into()
}

fn list(mut entries: Vec<Vec<u8>>) -> Vec<u8> {
    entries.sort();
    let mut v = (entries.len() as u32).to_be_bytes().to_vec();
    for e in entries {
        v.extend_from_slice(&e);
    }
    v
}

pub fn stored_bytes(s: &Stored) -> [u8; 11] {
    let mut v = [0u8; 11];
    match s {
        Stored::Accepted { nonce } => {
            v[0] = 1;
            v[3..].copy_from_slice(&nonce.to_be_bytes());
        }
        Stored::Denied {
            denial,
            expected_nonce,
        } => {
            v[0] = 2;
            v[1] = kind_tag(denial.kind);
            v[2] = cause_code(denial.cause);
            v[3..].copy_from_slice(&expected_nonce.to_be_bytes());
        }
    }
    v
}

pub fn config_commit(m: &Machine) -> Option<Hash> {
    let c = m.config();
    let mut v = Vec::new();
    v.extend_from_slice(&c.accounts.to_be_bytes());
    v.extend_from_slice(&c.assets.to_be_bytes());
    match c.vault {
        Some(x) => {
            v.push(1);
            v.extend_from_slice(&x.to_be_bytes());
        }
        None => v.extend_from_slice(&[0u8; 5]),
    }
    v.extend_from_slice(&(c.deadlines.len() as u32).to_be_bytes());
    for d in &c.deadlines {
        v.extend_from_slice(&d.to_be_bytes());
    }
    match c.migration {
        Some(g) => {
            v.push(1);
            for x in [g.holder, g.recipient, g.src, g.dst] {
                v.extend_from_slice(&x.to_be_bytes());
            }
            v.extend_from_slice(&g.num.to_be_bytes());
            v.extend_from_slice(&g.den.to_be_bytes());
        }
        None => v.extend_from_slice(&[0u8; 49]),
    }
    let p = &c.policy;
    let controls = p
        .controls
        .iter()
        .map(|(a, b)| [a.to_be_bytes(), b.to_be_bytes()].concat())
        .collect();
    let limits = p
        .limits
        .iter()
        .map(|(&(pr, k, a, b, s), &l)| {
            let mut e = pr.to_be_bytes().to_vec();
            e.push(kind_tag(k));
            e.extend_from_slice(&a.to_be_bytes());
            match b {
                Some(b) => {
                    e.push(1);
                    e.extend_from_slice(&b.to_be_bytes());
                }
                None => e.extend_from_slice(&[0u8; 5]),
            }
            e.extend_from_slice(&s.to_be_bytes());
            e.extend_from_slice(&l.to_be_bytes());
            e
        })
        .collect();
    let mut ids = Vec::new();
    for &(pr, k, id) in &p.ids {
        let id = u32::try_from(id).ok()?;
        let mut e = pr.to_be_bytes().to_vec();
        e.push(kind_tag(k));
        e.extend_from_slice(&id.to_be_bytes());
        ids.push(e);
    }
    let clock = p.clock.iter().map(|x| x.to_be_bytes().to_vec()).collect();
    for part in [list(controls), list(limits), list(ids), list(clock)] {
        v.extend_from_slice(&part);
    }
    Some(sha(&[D_CFG, &v]))
}

pub fn cache_commit(m: &Machine) -> Option<Hash> {
    let mut entries: Vec<([u8; 32], Vec<u8>)> = Vec::new();
    for (id, req, stored) in m.cache_entries() {
        let w = WireRequest {
            request_id: *id,
            request: *req,
        };
        let mut e = encode(&w).ok()?;
        e.extend_from_slice(&stored_bytes(stored));
        entries.push((*id, e));
    }
    entries.sort();
    let mut v = (entries.len() as u32).to_be_bytes().to_vec();
    for (_, e) in entries {
        v.extend_from_slice(&e);
    }
    Some(sha(&[D_CAC, &v]))
}

pub fn escrow_commit(m: &Machine) -> Hash {
    let c = m.config();
    let mut v = (c.deadlines.len() as u32).to_be_bytes().to_vec();
    for (id, d) in c.deadlines.iter().enumerate() {
        v.extend_from_slice(&d.to_be_bytes());
        match m.record(id) {
            Some(r) => {
                v.push(1);
                v.extend_from_slice(&r.depositor.to_be_bytes());
                v.extend_from_slice(&r.beneficiary.to_be_bytes());
                v.extend_from_slice(&r.asset.to_be_bytes());
                v.extend_from_slice(&r.amount.to_be_bytes());
                v.push(r.phase as u8);
            }
            None => v.extend_from_slice(&[0u8; 30]),
        }
        match m.filing(id) {
            Some(f) => {
                v.push(1);
                v.extend_from_slice(&f.principal.to_be_bytes());
                v.extend_from_slice(&f.claimant.to_be_bytes());
                v.extend_from_slice(&f.filed_at.to_be_bytes());
            }
            None => v.extend_from_slice(&[0u8; 17]),
        }
    }
    sha(&[D_ESC, &v])
}

/// (balance root, supply root, nonce root).
pub fn trees(m: &Machine) -> (Hash, Hash, Hash) {
    let (bal, sup) = holdings_roots(&m.ledger);
    let non: BTreeMap<u64, Vec<u8>> = m
        .nonces()
        .iter()
        .filter(|(_, &n)| n != 0)
        .map(|(&p, &n)| (p as u64, n.to_be_bytes().to_vec()))
        .collect();
    (bal, sup, root(&non))
}

pub fn state_root_v5(m: &Machine) -> Option<Hash> {
    let (bal, sup, non) = trees(m);
    let (ts, tt, dust) = m.migration_totals();
    let mut s = Sha256::new();
    s.update(D_STATE);
    s.update(m.ledger.accounts().to_be_bytes());
    s.update(m.ledger.assets().to_be_bytes());
    s.update(bal);
    s.update(sup);
    s.update(non);
    s.update(config_commit(m)?);
    s.update(cache_commit(m)?);
    s.update(escrow_commit(m));
    s.update(m.now().to_be_bytes());
    for x in [ts, tt, dust] {
        s.update(x.to_be_bytes());
    }
    Some(s.finalize().into())
}
