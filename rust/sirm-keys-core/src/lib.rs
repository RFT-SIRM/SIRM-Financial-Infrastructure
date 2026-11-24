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
    // no `return` inside the nested loops: Aeneas does not support that yet, so a flag is used
    let mut distinct = true;
    let mut i = 0;
    while i < keys.len() {
        let mut j = i + 1;
        while j < keys.len() {
            if keys[i].key == keys[j].key {
                distinct = false;
            }
            j += 1;
        }
        i += 1;
    }
    distinct
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

/// What the integrated pipeline does with a request nonce, given the sender's expected nonce.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum NonceClass {
    /// The nonce is behind the counter, or equals a counter that has reached `u64::MAX` and cannot advance.
    Stale,
    /// The nonce is ahead of the counter.
    Future,
    /// The nonce equals the counter and the counter can advance.
    Proceed,
}

/// Order of the checks of `IntegratedPipeline.processCapped` (with `N = 2^64 - 1`) after the request-id
/// lookup: stale, then future, then the ceiling.
pub fn nonce_class(request: u64, expected: u64) -> NonceClass {
    if request < expected {
        NonceClass::Stale
    } else if request > expected {
        NonceClass::Future
    } else if expected == u64::MAX {
        NonceClass::Stale
    } else {
        NonceClass::Proceed
    }
}

/// The counter after an accepted or denied-and-cached request; only called when `nonce_class` said `Proceed`.
pub fn next_nonce(expected: u64) -> u64 {
    expected + 1
}

/// The migration accumulator `amount * num + dust`, or `None` when either step overflows `u128`
/// (the `checked_mul` / `checked_add` pair of the validation, written without them so that Aeneas can extract it).
pub fn migrate_acc(amount: u128, num: u128, dust: u128) -> Option<u128> {
    if num != 0 && amount > u128::MAX / num {
        None
    } else {
        let prod = amount * num;
        if dust > u128::MAX - prod {
            None
        } else {
            Some(prod + dust)
        }
    }
}

/// `a + b`, or `None` when the sum exceeds `u128::MAX` (the `checked_add` decision written with a comparison).
pub fn add_ok(a: u128, b: u128) -> Option<u128> {
    if a > u128::MAX - b {
        None
    } else {
        Some(a + b)
    }
}

/// `a - b`, or `None` when `b > a` (the `checked_sub` decision written with a comparison).
pub fn sub_ok(a: u128, b: u128) -> Option<u128> {
    if b > a {
        None
    } else {
        Some(a - b)
    }
}

/// Released amount and carried remainder: `(acc / den, acc % den)`; `den` must not be zero.
pub fn migrate_split(acc: u128, den: u128) -> (u128, u128) {
    (acc / den, acc % den)
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

    #[test]
    fn nonce_classes() {
        assert_eq!(nonce_class(3, 5), NonceClass::Stale);
        assert_eq!(nonce_class(7, 5), NonceClass::Future);
        assert_eq!(nonce_class(5, 5), NonceClass::Proceed);
        assert_eq!(nonce_class(u64::MAX, u64::MAX), NonceClass::Stale);
        assert_eq!(nonce_class(u64::MAX - 1, u64::MAX), NonceClass::Stale);
        assert_eq!(nonce_class(u64::MAX, u64::MAX - 1), NonceClass::Future);
        assert_eq!(nonce_class(u64::MAX - 1, u64::MAX - 1), NonceClass::Proceed);
        assert_eq!(next_nonce(u64::MAX - 1), u64::MAX);
    }

    #[test]
    fn add_ok_agrees_with_checked_add() {
        let vals = [
            0u128,
            1,
            2,
            1 << 64,
            u128::MAX / 2,
            u128::MAX - 1,
            u128::MAX,
        ];
        for &a in &vals {
            for &b in &vals {
                assert_eq!(add_ok(a, b), a.checked_add(b), "{a} {b}");
            }
        }
    }

    #[test]
    fn sub_ok_agrees_with_checked_sub() {
        let vals = [
            0u128,
            1,
            2,
            1 << 64,
            u128::MAX / 2,
            u128::MAX - 1,
            u128::MAX,
        ];
        for &a in &vals {
            for &b in &vals {
                assert_eq!(sub_ok(a, b), a.checked_sub(b), "{a} {b}");
            }
        }
    }

    #[test]
    fn migrate_arithmetic_agrees_with_checked_ops() {
        let vals = [
            0u128,
            1,
            2,
            3,
            7,
            1 << 64,
            u128::MAX / 2,
            u128::MAX - 1,
            u128::MAX,
        ];
        for &a in &vals {
            for &n in &vals {
                for &d in &vals {
                    assert_eq!(
                        migrate_acc(a, n, d),
                        a.checked_mul(n).and_then(|p| p.checked_add(d)),
                        "{a} {n} {d}"
                    );
                }
            }
        }
        for &acc in &vals {
            for &den in &vals[1..] {
                assert_eq!(migrate_split(acc, den), (acc / den, acc % den));
            }
        }
    }
}
