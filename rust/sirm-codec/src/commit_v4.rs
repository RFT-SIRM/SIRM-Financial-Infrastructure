//! State commitment v4 (checked by SIRM): the v3 root plus the asset-migration component.
//! Reference: `scripts/state_commitment_v4_reference.py`; vectors:
//! `engineering/canonical_encoding/results/state_commitment_v4_vectors.json`.
//!
//! ```text
//! migration commit = SHA256("SIRM/MIG/v4\0" | accounts u32 | assets u32 | balance root | supply root
//!                           | source holder u32 | recipient u32 | source asset u32 | dest asset u32
//!                           | numerator u128 | denominator u128 | total source u128 | total target u128
//!                           | dust u128 | n u32 | (principal u32, next nonce u64) for nonces != 0,
//!                           ascending by principal)
//! state root v4 = SHA256("SIRM/STC/v4\0" | accounts u32 | assets u32 | balance root | supply root
//!                        | nonce root | key root | header hash | cache | policy | registry
//!                        | escrow | migration)
//! ```
//!
//! Like the escrow machine, the migration machine keeps its own holdings, so its commit carries its
//! own balance and supply roots. Fees have no persistent state of their own in this code (a fee
//! transfer only moves holdings), and there is no governance module, so there is nothing further to
//! commit for them. Not a commitment to the complete protocol state. No Lean counterpart.

use crate::commit::{root, state_trees, Hash};
use crate::commit_v1::{header_hash, key_root, suite_root, Header, KeyAccount, SuiteEntry};
use crate::commit_v2::{cache_commit, policy_commit, registry_commit};
use crate::commit_v3::{escrow_commit, holdings_roots};
use crate::dispute::DisputedEscrow;
use crate::machine::Processor;
use crate::migration::Migration;
use crate::registry::Registry;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;

const D_STATE: &[u8] = b"SIRM/STC/v4\0";
const D_MIG: &[u8] = b"SIRM/MIG/v4\0";

pub fn migration_commit(m: &Migration) -> Hash {
    let h = &m.holdings;
    let (bal, sup) = holdings_roots(h);
    let (num, den) = m.rate();
    let nonces: Vec<(u32, u64)> = m.nonces().collect();
    let mut s = Sha256::new();
    s.update(D_MIG);
    s.update(h.accounts().to_be_bytes());
    s.update(h.assets().to_be_bytes());
    s.update(bal);
    s.update(sup);
    for x in [
        m.source_holder(),
        m.recipient(),
        m.source_asset(),
        m.dest_asset(),
    ] {
        s.update(x.to_be_bytes());
    }
    for x in [num, den, m.total_source(), m.total_target(), m.dust()] {
        s.update(x.to_be_bytes());
    }
    s.update((nonces.len() as u32).to_be_bytes());
    for (p, n) in nonces {
        s.update(p.to_be_bytes());
        s.update(n.to_be_bytes());
    }
    s.finalize().into()
}

pub fn state_root_v4(
    p: &Processor,
    header: &Header,
    suites: &BTreeMap<u16, SuiteEntry>,
    keys: &BTreeMap<u32, KeyAccount>,
    registry: &Registry,
    escrow: &DisputedEscrow,
    migration: &Migration,
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
    s.update(cache_commit(p));
    s.update(policy_commit(p.policy()));
    s.update(registry_commit(registry));
    s.update(escrow_commit(escrow));
    s.update(migration_commit(migration));
    s.finalize().into()
}
