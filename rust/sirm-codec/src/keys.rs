//! Key lifecycle state machine (proposal): registration, rotation, freeze, revocation, recovery
//! with a delay, and k-of-n threshold acceptance. A port of the Lean models
//! `SIRM/KeyRegistry.lean`, `SIRM/RecoveryDelay.lean` and `SIRM/ThresholdAuth.lean`, checked
//! against the independent Python reference `scripts/key_registry_reference.py`.
//!
//! One explicit difference from the Lean `DelayState` (one account plus its pending recovery):
//! here the registry holds all accounts, and initiate, cancel and finalize on a principal without
//! an account fail with `UnknownAccount` first.
//!
//! The actor (current key or recovery key) is the outcome of an earlier signature check. Nothing
//! here verifies signatures, and the clock is a caller-supplied `now`. No Lean refinement proof is
//! claimed, only differential tests.

use std::collections::BTreeMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Actor {
    Current,
    Recovery,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct KeyRecord {
    pub suite: u16,
    pub key: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Account {
    pub key: KeyRecord,
    pub recovery: Option<KeyRecord>,
    pub frozen: bool,
    pub revoked: bool,
    pub pq_bound: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KeyError {
    UnknownAccount,
    AlreadyRegistered,
    Frozen,
    Revoked,
    NotAuthorized,
    NoRecovery,
    PqDowngrade,
    AlreadyPending,
    NoPending,
    TooEarly,
    /// Finalization reached the recover step and it refused.
    Rejected(&'static str),
}

impl KeyError {
    /// Stable code, the same strings as the Python reference.
    pub fn code(&self) -> String {
        match self {
            KeyError::UnknownAccount => "unknownAccount".into(),
            KeyError::AlreadyRegistered => "alreadyRegistered".into(),
            KeyError::Frozen => "frozen".into(),
            KeyError::Revoked => "revoked".into(),
            KeyError::NotAuthorized => "notAuthorized".into(),
            KeyError::NoRecovery => "noRecovery".into(),
            KeyError::PqDowngrade => "pqDowngrade".into(),
            KeyError::AlreadyPending => "alreadyPending".into(),
            KeyError::NoPending => "noPending".into(),
            KeyError::TooEarly => "tooEarly".into(),
            KeyError::Rejected(c) => format!("rejected:{c}"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct KeyRegistry {
    pub accounts: BTreeMap<u32, Account>,
    pub pending: BTreeMap<u32, (KeyRecord, u64)>,
    is_pq: fn(u16) -> bool,
    delay: u64,
}

impl KeyRegistry {
    pub fn new(is_pq: fn(u16) -> bool, delay: u64) -> KeyRegistry {
        KeyRegistry {
            accounts: BTreeMap::new(),
            pending: BTreeMap::new(),
            is_pq,
            delay,
        }
    }

    /// The legacy-key invariant: an account bound to a post-quantum key holds one.
    pub fn pq_sound(&self) -> bool {
        self.accounts
            .values()
            .all(|a| !a.pq_bound || (self.is_pq)(a.key.suite))
    }

    pub fn register(
        &mut self,
        p: u32,
        key: KeyRecord,
        recovery: Option<KeyRecord>,
    ) -> Result<(), KeyError> {
        if self.accounts.contains_key(&p) {
            return Err(KeyError::AlreadyRegistered);
        }
        let pq = (self.is_pq)(key.suite);
        self.accounts.insert(
            p,
            Account {
                key,
                recovery,
                frozen: false,
                revoked: false,
                pq_bound: pq,
            },
        );
        Ok(())
    }

    pub fn rotate(&mut self, actor: Actor, p: u32, new: KeyRecord) -> Result<(), KeyError> {
        let new_pq = (self.is_pq)(new.suite);
        let a = self.accounts.get_mut(&p).ok_or(KeyError::UnknownAccount)?;
        if actor != Actor::Current {
            return Err(KeyError::NotAuthorized);
        }
        if a.revoked {
            return Err(KeyError::Revoked);
        }
        if a.frozen {
            return Err(KeyError::Frozen);
        }
        if a.pq_bound && !new_pq {
            return Err(KeyError::PqDowngrade);
        }
        a.key = new;
        a.pq_bound = a.pq_bound || new_pq;
        Ok(())
    }

    pub fn freeze(&mut self, p: u32) -> Result<(), KeyError> {
        let a = self.accounts.get_mut(&p).ok_or(KeyError::UnknownAccount)?;
        a.frozen = true;
        Ok(())
    }

    pub fn revoke(&mut self, actor: Actor, p: u32) -> Result<(), KeyError> {
        let a = self.accounts.get_mut(&p).ok_or(KeyError::UnknownAccount)?;
        if actor != Actor::Recovery {
            return Err(KeyError::NotAuthorized);
        }
        if a.recovery.is_none() {
            return Err(KeyError::NoRecovery);
        }
        a.frozen = true;
        a.revoked = true;
        Ok(())
    }

    /// The immediate recover primitive (used by `finalize`).
    pub fn recover(&mut self, actor: Actor, p: u32, new: KeyRecord) -> Result<(), KeyError> {
        let new_pq = (self.is_pq)(new.suite);
        let a = self.accounts.get_mut(&p).ok_or(KeyError::UnknownAccount)?;
        if actor != Actor::Recovery {
            return Err(KeyError::NotAuthorized);
        }
        if a.recovery.is_none() {
            return Err(KeyError::NoRecovery);
        }
        if a.pq_bound && !new_pq {
            return Err(KeyError::PqDowngrade);
        }
        a.key = new;
        a.frozen = false;
        a.revoked = false;
        a.pq_bound = a.pq_bound || new_pq;
        Ok(())
    }

    pub fn initiate(
        &mut self,
        actor: Actor,
        p: u32,
        new: KeyRecord,
        now: u64,
    ) -> Result<(), KeyError> {
        let a = self.accounts.get(&p).ok_or(KeyError::UnknownAccount)?;
        if actor != Actor::Recovery {
            return Err(KeyError::NotAuthorized);
        }
        if a.recovery.is_none() {
            return Err(KeyError::NoRecovery);
        }
        if self.pending.contains_key(&p) {
            return Err(KeyError::AlreadyPending);
        }
        self.pending.insert(p, (new, now));
        Ok(())
    }

    pub fn cancel(&mut self, actor: Actor, p: u32) -> Result<(), KeyError> {
        if !self.accounts.contains_key(&p) {
            return Err(KeyError::UnknownAccount);
        }
        if actor != Actor::Current {
            return Err(KeyError::NotAuthorized);
        }
        self.pending
            .remove(&p)
            .map(|_| ())
            .ok_or(KeyError::NoPending)
    }

    pub fn finalize(&mut self, actor: Actor, p: u32, now: u64) -> Result<(), KeyError> {
        if !self.accounts.contains_key(&p) {
            return Err(KeyError::UnknownAccount);
        }
        let (new, start) = *self.pending.get(&p).ok_or(KeyError::NoPending)?;
        if actor != Actor::Recovery {
            return Err(KeyError::NotAuthorized);
        }
        if now < start.saturating_add(self.delay) {
            return Err(KeyError::TooEarly);
        }
        self.recover(Actor::Recovery, p, new).map_err(|e| match e {
            KeyError::NoRecovery => KeyError::Rejected("noRecovery"),
            KeyError::PqDowngrade => KeyError::Rejected("pqDowngrade"),
            _ => KeyError::Rejected("other"),
        })?;
        self.pending.remove(&p);
        Ok(())
    }
}

/// `true` if no two registered records share a public key (Lean: `ThresholdAuth.KeysDistinct`).
/// `threshold_accepts` counts indices, so a policy has to satisfy this for the `k` approvals to come
/// from `k` different keys.
pub fn keys_distinct(keys: &[KeyRecord]) -> bool {
    keys.iter()
        .enumerate()
        .all(|(i, a)| keys.iter().skip(i + 1).all(|b| a.key != b.key))
}

/// k-of-n acceptance over a plain list of `(index, signature)` pairs. Each registered index counts
/// at most once; `permits` says whether a suite may authorize; `verify` is the abstract verifier.
pub fn threshold_accepts(
    keys: &[KeyRecord],
    k: usize,
    permits: impl Fn(u16) -> bool,
    verify: impl Fn(&KeyRecord, u64) -> bool,
    sigs: &[(usize, u64)],
) -> bool {
    if k == 0 {
        return false;
    }
    let count = keys
        .iter()
        .enumerate()
        .filter(|(i, r)| permits(r.suite) && sigs.iter().any(|(j, s)| j == i && verify(r, *s)))
        .count();
    k <= count
}

#[cfg(test)]
mod threshold_tests {
    use super::*;

    #[test]
    fn one_key_registered_twice_counts_twice_unless_the_policy_is_checked() {
        let keys = [
            KeyRecord { suite: 2, key: 10 },
            KeyRecord { suite: 2, key: 10 },
            KeyRecord { suite: 2, key: 12 },
        ];
        // the same signature of key 10 labelled with both indices reaches 2-of-3
        let sigs = [(0usize, 7u64), (1, 7)];
        assert!(threshold_accepts(&keys, 2, |_| true, |_, s| s == 7, &sigs));
        // which is why a policy must pass `keys_distinct`
        assert!(!keys_distinct(&keys));
        assert!(keys_distinct(&[keys[0], keys[2]]));
        assert!(keys_distinct(&[]));
    }
}
