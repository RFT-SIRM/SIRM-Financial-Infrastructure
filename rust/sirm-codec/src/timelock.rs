//! Rust port of `SIRM.EscrowTimeLocks` (with the multi-record registry and the pooled
//! vault of `EscrowRegistry` / `EscrowFinancialIntegration`) at the holdings level.
//!
//! Many escrow IDs share one vault account. Every ID has a fixed deadline
//! (`expires_at[id]`); time is a discrete clock that only moves strictly forward.
//! `open`: fresh ID, `now < deadline`, vault is neither party, amount > 0, funded.
//! `release`/`cancel`: record pending and `now < deadline`.
//! `expire`: record pending and `deadline <= now`; refunds the depositor and marks the
//! record `Expired` (distinct from voluntary `Cancelled`).
//! Terminal records stay stored, so an ID is never reusable. Authorization policies are
//! outside this module, as in Lean where they are separate witnesses. IDs outside the
//! schedule are rejected (`UnknownId`); Lean's ID type is finite, so this is the
//! runtime counterpart.
//!
//! Every operation validates before its first write; the single holdings transfer is
//! atomic and the registry/clock change only after it succeeds.

use crate::escrow::{Phase, Record};
use crate::ledger::{Holdings, LedgerError};
use std::collections::BTreeMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TimeLockError {
    /// ID outside the deadline schedule, or no record for release/cancel/expire.
    UnknownId,
    IdInUse,
    NotPending,
    DeadlinePassed,
    DeadlineNotReached,
    VaultIsParty,
    ZeroAmount,
    TimeNotForward,
    Ledger(LedgerError),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TimeLockedEscrow {
    pub holdings: Holdings,
    vault: u32,
    expires_at: Vec<u64>,
    now: u64,
    records: BTreeMap<usize, Record>,
}

impl TimeLockedEscrow {
    pub fn new(holdings: Holdings, vault: u32, expires_at: Vec<u64>, now: u64) -> Self {
        TimeLockedEscrow {
            holdings,
            vault,
            expires_at,
            now,
            records: BTreeMap::new(),
        }
    }

    pub fn now(&self) -> u64 {
        self.now
    }

    pub fn record(&self, id: usize) -> Option<Record> {
        self.records.get(&id).copied()
    }

    /// Sum of pending amounts of one asset; `None` on overflow.
    pub fn pooled_reserve(&self, asset: u32) -> Option<u128> {
        self.records
            .values()
            .filter(|r| r.phase == Phase::Pending && r.asset == asset)
            .try_fold(0u128, |acc, r| acc.checked_add(r.amount))
    }

    /// Reconciled holdings; every record non-ready with positive amount; the vault
    /// holds exactly the pooled pending reserve of every asset.
    pub fn invariant(&self, assets: u32) -> bool {
        self.holdings.invariant()
            && self
                .records
                .values()
                .all(|r| r.phase != Phase::Ready && r.amount > 0)
            && (0..assets)
                .all(|s| self.pooled_reserve(s) == Some(self.holdings.balance(self.vault, s)))
    }

    pub fn advance(&mut self, next: u64) -> Result<(), TimeLockError> {
        if next <= self.now {
            return Err(TimeLockError::TimeNotForward);
        }
        self.now = next;
        Ok(())
    }

    pub fn open(
        &mut self,
        id: usize,
        depositor: u32,
        beneficiary: u32,
        asset: u32,
        amount: u128,
    ) -> Result<(), TimeLockError> {
        let deadline = *self.expires_at.get(id).ok_or(TimeLockError::UnknownId)?;
        if self.records.contains_key(&id) {
            return Err(TimeLockError::IdInUse);
        }
        if self.now >= deadline {
            return Err(TimeLockError::DeadlinePassed);
        }
        if self.vault == depositor || self.vault == beneficiary {
            return Err(TimeLockError::VaultIsParty);
        }
        if amount == 0 {
            return Err(TimeLockError::ZeroAmount);
        }
        self.holdings
            .clone()
            .transfer(beneficiary, beneficiary, asset, 0)
            .map_err(TimeLockError::Ledger)?;
        self.holdings
            .transfer(depositor, self.vault, asset, amount)
            .map_err(TimeLockError::Ledger)?;
        self.records.insert(
            id,
            Record {
                depositor,
                beneficiary,
                asset,
                amount,
                phase: Phase::Pending,
            },
        );
        Ok(())
    }

    fn settle(
        &mut self,
        id: usize,
        to_beneficiary: bool,
        phase: Phase,
    ) -> Result<(), TimeLockError> {
        let deadline = *self.expires_at.get(id).ok_or(TimeLockError::UnknownId)?;
        let r = *self.records.get(&id).ok_or(TimeLockError::UnknownId)?;
        if r.phase != Phase::Pending {
            return Err(TimeLockError::NotPending);
        }
        if phase == Phase::Expired {
            if self.now < deadline {
                return Err(TimeLockError::DeadlineNotReached);
            }
        } else if self.now >= deadline {
            return Err(TimeLockError::DeadlinePassed);
        }
        let to = if to_beneficiary {
            r.beneficiary
        } else {
            r.depositor
        };
        self.holdings
            .transfer(self.vault, to, r.asset, r.amount)
            .map_err(TimeLockError::Ledger)?;
        self.records.insert(id, Record { phase, ..r });
        Ok(())
    }

    pub fn release(&mut self, id: usize) -> Result<(), TimeLockError> {
        self.settle(id, true, Phase::Released)
    }

    pub fn cancel(&mut self, id: usize) -> Result<(), TimeLockError> {
        self.settle(id, false, Phase::Cancelled)
    }

    pub fn expire(&mut self, id: usize) -> Result<(), TimeLockError> {
        self.settle(id, false, Phase::Expired)
    }
}
