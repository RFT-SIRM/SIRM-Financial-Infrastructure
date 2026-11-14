//! Rust port of `SIRM.EscrowDisputes`: first-stage dispute intake and per-ID freeze on
//! top of the time-locked pooled-vault escrow (`timelock`).
//!
//! `raise` records one permanent filing (principal, claimant, filing time) for an
//! existing pending record strictly before its deadline, with no earlier filing, by the
//! depositor or the beneficiary. A disputed ID rejects release, cancel and expire (also
//! after the deadline); other IDs and the clock are unaffected. This stage is
//! safety-only: it never resolves a dispute, so a frozen record stays pending and its
//! units stay in the vault. The dispute authorization policy is outside this module, as
//! in Lean where it is a separate witness.

use crate::escrow::Phase;
use crate::timelock::{TimeLockError, TimeLockedEscrow};
use std::collections::BTreeMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Filing {
    pub principal: u32,
    pub claimant: u32,
    pub filed_at: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DisputeError {
    /// The ID has an active filing; release, cancel, expire and open are rejected.
    Disputed,
    AlreadyFiled,
    ClaimantNotParty,
    TimeLock(TimeLockError),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DisputedEscrow {
    pub escrow: TimeLockedEscrow,
    filings: BTreeMap<usize, Filing>,
}

impl DisputedEscrow {
    pub fn new(escrow: TimeLockedEscrow) -> Self {
        DisputedEscrow {
            escrow,
            filings: BTreeMap::new(),
        }
    }

    pub fn filing(&self, id: usize) -> Option<Filing> {
        self.filings.get(&id).copied()
    }

    /// Timed-escrow invariant, and every filing belongs to a stored record.
    pub fn invariant(&self, assets: u32) -> bool {
        self.escrow.invariant(assets)
            && self
                .filings
                .keys()
                .all(|&id| self.escrow.record(id).is_some())
    }

    fn guard(&self, id: usize) -> Result<(), DisputeError> {
        if self.filings.contains_key(&id) {
            Err(DisputeError::Disputed)
        } else {
            Ok(())
        }
    }

    pub fn open(
        &mut self,
        id: usize,
        depositor: u32,
        beneficiary: u32,
        asset: u32,
        amount: u128,
    ) -> Result<(), DisputeError> {
        self.guard(id)?;
        self.escrow
            .open(id, depositor, beneficiary, asset, amount)
            .map_err(DisputeError::TimeLock)
    }

    pub fn release(&mut self, id: usize) -> Result<(), DisputeError> {
        self.guard(id)?;
        self.escrow.release(id).map_err(DisputeError::TimeLock)
    }

    pub fn cancel(&mut self, id: usize) -> Result<(), DisputeError> {
        self.guard(id)?;
        self.escrow.cancel(id).map_err(DisputeError::TimeLock)
    }

    pub fn expire(&mut self, id: usize) -> Result<(), DisputeError> {
        self.guard(id)?;
        self.escrow.expire(id).map_err(DisputeError::TimeLock)
    }

    pub fn advance(&mut self, next: u64) -> Result<(), DisputeError> {
        self.escrow.advance(next).map_err(DisputeError::TimeLock)
    }

    pub fn raise(&mut self, id: usize, principal: u32, claimant: u32) -> Result<(), DisputeError> {
        let record = self
            .escrow
            .record(id)
            .ok_or(DisputeError::TimeLock(TimeLockError::UnknownId))?;
        if record.phase != Phase::Pending {
            return Err(DisputeError::TimeLock(TimeLockError::NotPending));
        }
        // A stored record always has an in-range ID, hence a deadline.
        let deadline = self
            .escrow
            .deadline(id)
            .expect("stored record has a deadline");
        if self.escrow.now() >= deadline {
            return Err(DisputeError::TimeLock(TimeLockError::DeadlinePassed));
        }
        if self.filings.contains_key(&id) {
            return Err(DisputeError::AlreadyFiled);
        }
        if claimant != record.depositor && claimant != record.beneficiary {
            return Err(DisputeError::ClaimantNotParty);
        }
        self.filings.insert(
            id,
            Filing {
                principal,
                claimant,
                filed_at: self.escrow.now(),
            },
        );
        Ok(())
    }
}
