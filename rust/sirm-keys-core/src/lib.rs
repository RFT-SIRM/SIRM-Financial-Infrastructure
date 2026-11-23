//! The decision core of `sirm_codec::keys::{keys_distinct, threshold_accepts}` without closures,
//! iterators or collections, so that Charon and Aeneas can extract it to Lean
//! (see `refinement/README.md`). The refinement proof is a separate step and is NOT done yet: this crate
//! only fixes the shape of the code that will be proved against `SIRM/ThresholdAuth.lean`.
//!
//! `valid[i]` says that the signature set holds a verified signature for index `i` under a permitted
//! suite; the caller computes it (the verifier is abstract in the Lean model).

#[derive(Clone, Copy)]
pub struct Key {
    pub suite: u16,
    pub key: u64,
}

/// No key value is registered at two indices (`KeysDistinct` in `ThresholdAuth.lean`).
pub fn keys_distinct(keys: &[Key]) -> bool {
    let mut i = 0;
    while i < keys.len() {
        let mut j = i + 1;
        while j < keys.len() {
            if keys[i].key == keys[j].key {
                return false;
            }
            j += 1;
        }
        i += 1;
    }
    true
}

/// Number of indices with a valid signature (`validIndices` length in `ThresholdAuth.lean`).
pub fn count_valid(valid: &[bool]) -> usize {
    let mut n = 0;
    let mut i = 0;
    while i < valid.len() {
        if valid[i] {
            n += 1;
        }
        i += 1;
    }
    n
}

/// k-of-n decision: `0 < k` and `k <= count` (`thresholdAccepts`).
pub fn accepts(valid: &[bool], k: usize) -> bool {
    k > 0 && k <= count_valid(valid)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn k(key: u64) -> Key {
        Key { suite: 2, key }
    }

    #[test]
    fn distinct() {
        assert!(keys_distinct(&[]));
        assert!(keys_distinct(&[k(1), k(2), k(3)]));
        assert!(!keys_distinct(&[k(1), k(2), k(1)]));
    }

    #[test]
    fn threshold() {
        assert!(!accepts(&[true, true], 0));
        assert!(accepts(&[true, false, true], 2));
        assert!(!accepts(&[true, false, true], 3));
        assert!(!accepts(&[], 1));
    }
}
