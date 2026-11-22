//! State commitment v3 (checked by SIRM): the v2 root plus the escrow / time-lock /
//! dispute component. Reference: `scripts/state_commitment_v3_reference.py`; vectors:
//! `engineering/canonical_encoding/results/state_commitment_v3_vectors.json`.
//!
//! ```text
//! id entry      = deadline u64 | record flag u8 | depositor u32 | beneficiary u32 | asset u32
//!                 | amount u128 | phase u8 | filing flag u8 | principal u32 | claimant u32
//!                 | filed at u64                       (55 bytes; absent parts are flag 0 + zero fill)
//!                 phase: 1 pending, 2 released, 3 cancelled, 4 expired
//! escrow commit = SHA256("SIRM/ESC/v3\0" | accounts u32 | assets u32 | balance root | supply root
//!                        | vault u32 | now u64 | ids u32 | id entries in id order)
//! state root v3 = SHA256("SIRM/STC/v3\0" | accounts u32 | assets u32 | balance root | supply root
//!                        | nonce root | key root | header hash | cache | policy | registry | escrow)
//! ```
//!
//! The escrow machine keeps its own holdings, separate from the integrated processor's; the escrow
//! commit therefore carries its own balance and supply roots. Sharing one ledger between the two is
//! future integration and is not modelled here.
//!
//! Still not covered: fee parameters, governance state, migration and residual state, threshold
//! policies. Not a commitment to the complete protocol state. No Lean counterpart.

use crate::commit::{root, Hash};
use crate::commit_v1::{header_hash, key_root, suite_root, Header, KeyAccount, SuiteEntry};
use crate::commit_v2::{cache_commit, policy_commit, registry_commit};
use crate::dispute::DisputedEscrow;
use crate::ledger::Holdings;
use crate::machine::Processor;
use crate::registry::Registry;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;

const D_STATE: &[u8] = b"SIRM/STC/v3\0";
const D_ESC: &[u8] = b"SIRM/ESC/v3\0";

/// Balance and supply roots of a holdings state (same trees as the v0 processor roots).
pub fn holdings_roots(h: &Holdings) -> (Hash, Hash) {
    let (mut bal, mut sup) = (BTreeMap::new(), BTreeMap::new());
    for a in 0..h.accounts() {
        for s in 0..h.assets() {
            let v = h.balance(a, s);
            if v != 0 {
                bal.insert(((a as u64) << 32) | s as u64, v.to_be_bytes().to_vec());
            }
        }
    }
    for s in 0..h.assets() {
        let t = h.supply(s);
        if (t.minted, t.burned, t.outstanding) != (0, 0, 0) {
            let mut v = Vec::with_capacity(48);
            for x in [t.minted, t.burned, t.outstanding] {
                v.extend_from_slice(&x.to_be_bytes());
            }
            sup.insert(s as u64, v);
        }
    }
    (root(&bal), root(&sup))
}

pub fn id_entry(e: &DisputedEscrow, id: usize) -> Vec<u8> {
    let mut v = e.escrow.deadline(id).unwrap_or(0).to_be_bytes().to_vec();
    match e.escrow.record(id) {
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
    match e.filing(id) {
        Some(f) => {
            v.push(1);
            v.extend_from_slice(&f.principal.to_be_bytes());
            v.extend_from_slice(&f.claimant.to_be_bytes());
            v.extend_from_slice(&f.filed_at.to_be_bytes());
        }
        None => v.extend_from_slice(&[0u8; 17]),
    }
    v
}

pub fn escrow_commit(e: &DisputedEscrow) -> Hash {
    let h = &e.escrow.holdings;
    let (bal, sup) = holdings_roots(h);
    let mut s = Sha256::new();
    s.update(D_ESC);
    s.update(h.accounts().to_be_bytes());
    s.update(h.assets().to_be_bytes());
    s.update(bal);
    s.update(sup);
    s.update(e.escrow.vault().to_be_bytes());
    s.update(e.escrow.now().to_be_bytes());
    s.update((e.escrow.ids() as u32).to_be_bytes());
    for id in 0..e.escrow.ids() {
        s.update(id_entry(e, id));
    }
    s.finalize().into()
}

pub fn state_root_v3(
    p: &Processor,
    header: &Header,
    suites: &BTreeMap<u16, SuiteEntry>,
    keys: &BTreeMap<u32, KeyAccount>,
    registry: &Registry,
    escrow: &DisputedEscrow,
) -> Hash {
    let (bal, sup, non) = crate::commit::state_trees(p);
    let mut s = Sha256::new();
    s.update(D_STATE);
    s.update(p.ledger.accounts().to_be_bytes());
    s.update(p.ledger.assets().to_be_bytes());
    s.update(root(&bal));
    s.update(root(&sup));
    s.update(root(&non));
    s.update(key_root(keys));
    s.update(header_hash(header, &suite_root(suites)));
    s.update(cache_commit(p));
    s.update(policy_commit(p.policy()));
    s.update(registry_commit(registry));
    s.update(escrow_commit(escrow));
    s.finalize().into()
}
