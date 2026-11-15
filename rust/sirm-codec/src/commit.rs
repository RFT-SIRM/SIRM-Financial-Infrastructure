//! State commitment v0 (proposal, not adopted): a depth-64 sparse Merkle tree (SMT) over
//! `u64` keys with SHA-256, and a state root over three trees (balances, supply, nonces).
//! Executable reference: `scripts/state_commitment_reference.py`; vectors:
//! `engineering/canonical_encoding/results/state_commitment_vectors_v0.json`.
//!
//! ```text
//! empty leaf  = SHA256("SIRM/SMT/E/v0\0")
//! leaf        = SHA256("SIRM/SMT/L/v0\0" | key u64 | len u16 | value)
//! node        = SHA256("SIRM/SMT/N/v0\0" | left | right)       (bit 63 of the key at the top)
//! state root  = SHA256("SIRM/STC/v0\0" | accounts u32 | assets u32
//!                      | balance root | supply root | nonce root)
//! ```
//!
//! Zero balances, all-zero supply and zero nonces are not stored: absent equals empty. The
//! response cache is not part of the commitment. No Lean counterpart.

use crate::machine::Processor;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;

pub const DEPTH: usize = 64;
const D_EMPTY: &[u8] = b"SIRM/SMT/E/v0\0";
const D_LEAF: &[u8] = b"SIRM/SMT/L/v0\0";
const D_NODE: &[u8] = b"SIRM/SMT/N/v0\0";
const D_STATE: &[u8] = b"SIRM/STC/v0\0";

pub type Hash = [u8; 32];

fn h(parts: &[&[u8]]) -> Hash {
    let mut s = Sha256::new();
    for p in parts {
        s.update(p);
    }
    s.finalize().into()
}

/// Hashes of all-empty subtrees, from the leaf level (index 0) to the root (index `DEPTH`).
pub fn empty_levels() -> Vec<Hash> {
    let mut v = vec![h(&[D_EMPTY])];
    for i in 0..DEPTH {
        let e = v[i];
        v.push(h(&[D_NODE, &e, &e]));
    }
    v
}

pub fn leaf(key: u64, value: &[u8]) -> Hash {
    assert!(!value.is_empty() && value.len() < 65536);
    h(&[
        D_LEAF,
        &key.to_be_bytes(),
        &(value.len() as u16).to_be_bytes(),
        value,
    ])
}

/// Root of the tree holding exactly `entries` (values must be non-empty).
pub fn root(entries: &BTreeMap<u64, Vec<u8>>) -> Hash {
    let items: Vec<(&u64, &Vec<u8>)> = entries.iter().collect();
    let empty = empty_levels();
    fn go(items: &[(&u64, &Vec<u8>)], level: usize, empty: &[Hash]) -> Hash {
        if items.is_empty() {
            return empty[level];
        }
        if level == 0 {
            return leaf(*items[0].0, items[0].1);
        }
        let bit = level - 1;
        let mid = items.partition_point(|(k, _)| (**k >> bit) & 1 == 0);
        let (l, r) = (
            go(&items[..mid], level - 1, empty),
            go(&items[mid..], level - 1, empty),
        );
        h(&[D_NODE, &l, &r])
    }
    go(&items, DEPTH, &empty)
}

/// Siblings from the leaf level upward for `key`.
pub fn prove(entries: &BTreeMap<u64, Vec<u8>>, key: u64) -> Vec<Hash> {
    let empty = empty_levels();
    let mut level: BTreeMap<u64, Hash> = entries.iter().map(|(k, v)| (*k, leaf(*k, v))).collect();
    let mut sibs = Vec::with_capacity(DEPTH);
    for e in empty.iter().take(DEPTH) {
        sibs.push(level.get(&((key >> sibs.len()) ^ 1)).copied().unwrap_or(*e));
        let mut next = BTreeMap::new();
        for k in level.keys().map(|k| k >> 1) {
            let l = level.get(&(2 * k)).copied().unwrap_or(*e);
            let r = level.get(&(2 * k + 1)).copied().unwrap_or(*e);
            next.insert(k, h(&[D_NODE, &l, &r]));
        }
        level = next;
    }
    sibs
}

/// `value = None` proves absence.
pub fn verify(rt: &Hash, key: u64, value: Option<&[u8]>, sibs: &[Hash]) -> bool {
    if sibs.len() != DEPTH {
        return false;
    }
    let mut cur = match value {
        None => empty_levels()[0],
        Some(v) if v.is_empty() || v.len() >= 65536 => return false,
        Some(v) => leaf(key, v),
    };
    for (i, s) in sibs.iter().enumerate() {
        cur = if (key >> i) & 1 == 1 {
            h(&[D_NODE, s, &cur])
        } else {
            h(&[D_NODE, &cur, s])
        };
    }
    &cur == rt
}

pub type Trees = (
    BTreeMap<u64, Vec<u8>>,
    BTreeMap<u64, Vec<u8>>,
    BTreeMap<u64, Vec<u8>>,
);

/// The three trees of a processor: balances, supply, nonces.
pub fn state_trees(p: &Processor) -> Trees {
    let (mut bal, mut sup, mut non) = (BTreeMap::new(), BTreeMap::new(), BTreeMap::new());
    for a in 0..p.ledger.accounts() {
        for s in 0..p.ledger.assets() {
            let v = p.ledger.balance(a, s);
            if v != 0 {
                bal.insert(((a as u64) << 32) | s as u64, v.to_be_bytes().to_vec());
            }
        }
    }
    for s in 0..p.ledger.assets() {
        let t = p.ledger.supply(s);
        if (t.minted, t.burned, t.outstanding) != (0, 0, 0) {
            let mut v = Vec::with_capacity(48);
            for x in [t.minted, t.burned, t.outstanding] {
                v.extend_from_slice(&x.to_be_bytes());
            }
            sup.insert(s as u64, v);
        }
    }
    for (principal, n) in p.nonces() {
        if n != 0 {
            non.insert(principal as u64, n.to_be_bytes().to_vec());
        }
    }
    (bal, sup, non)
}

/// Combine dimensions and the three roots.
pub fn combine(accounts: u32, assets: u32, bal: &Hash, sup: &Hash, non: &Hash) -> Hash {
    h(&[
        D_STATE,
        &accounts.to_be_bytes(),
        &assets.to_be_bytes(),
        bal,
        sup,
        non,
    ])
}

pub fn state_root(p: &Processor) -> Hash {
    let (b, s, n) = state_trees(p);
    combine(
        p.ledger.accounts(),
        p.ledger.assets(),
        &root(&b),
        &root(&s),
        &root(&n),
    )
}
