//! Rust port of `SIRM.EscrowAccounting` holdings and record semantics.
//!
//! One dedicated vault account and one escrow record. `open` moves the amount from
//! the depositor to the vault (only from `Ready`, vault distinct from depositor and
//! beneficiary, amount positive); `release` moves exactly that amount to the
//! recorded beneficiary, `cancel` back to the depositor (both only from `Pending`).
//! A terminal record cannot reopen. Transfer/escrow *policies* are outside this
//! module, as in Lean where they are separate witnesses. The `Expired` phase exists
//! in Lean for `EscrowTimeLocks` and is not reachable through these three operations.
//!
//! Each operation validates before its first write; the single holdings transfer is
//! atomic and the record changes only after it succeeds.

use crate::ledger::{Holdings, LedgerError};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Phase {
    Ready,
    Pending,
    Released,
    Cancelled,
    Expired,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Record {
    pub depositor: u32,
    pub beneficiary: u32,
    pub asset: u32,
    pub amount: u128,
    pub phase: Phase,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EscrowError {
    NotReady,
    NotPending,
    VaultIsParty,
    ZeroAmount,
    Ledger(LedgerError),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Escrow {
    pub holdings: Holdings,
    vault: u32,
    record: Record,
}

impl Escrow {
    pub fn new(holdings: Holdings, vault: u32) -> Escrow {
        Escrow {
            holdings,
            vault,
            record: Record {
                depositor: 0,
                beneficiary: 0,
                asset: 0,
                amount: 0,
                phase: Phase::Ready,
            },
        }
    }

    pub fn vault(&self) -> u32 {
        self.vault
    }

    pub fn record(&self) -> Record {
        self.record
    }

    /// `EscrowFinancialInvariant` (holdings part): reconciled holdings, vault holds
    /// exactly the amount of the escrow asset while pending and nothing otherwise,
    /// and a pending escrow has a distinct vault and positive amount.
    pub fn invariant(&self, assets: u32) -> bool {
        let r = &self.record;
        let pending = r.phase == Phase::Pending;
        self.holdings.invariant()
            && (0..assets).all(|s| {
                let want = if pending && s == r.asset { r.amount } else { 0 };
                self.holdings.balance(self.vault, s) == want
            })
            && (!pending
                || (self.vault != r.depositor && self.vault != r.beneficiary && r.amount > 0))
    }

    pub fn open(
        &mut self,
        depositor: u32,
        beneficiary: u32,
        asset: u32,
        amount: u128,
    ) -> Result<(), EscrowError> {
        if self.record.phase != Phase::Ready {
            return Err(EscrowError::NotReady);
        }
        if self.vault == depositor || self.vault == beneficiary {
            return Err(EscrowError::VaultIsParty);
        }
        if amount == 0 {
            return Err(EscrowError::ZeroAmount);
        }
        // Range-check the beneficiary (the deposit transfer checks depositor, vault, asset).
        self.holdings
            .clone()
            .transfer(beneficiary, beneficiary, asset, 0)
            .map_err(EscrowError::Ledger)?;
        self.holdings
            .transfer(depositor, self.vault, asset, amount)
            .map_err(EscrowError::Ledger)?;
        self.record = Record {
            depositor,
            beneficiary,
            asset,
            amount,
            phase: Phase::Pending,
        };
        Ok(())
    }

    fn settle(&mut self, to: u32, phase: Phase) -> Result<(), EscrowError> {
        if self.record.phase != Phase::Pending {
            return Err(EscrowError::NotPending);
        }
        let r = self.record;
        self.holdings
            .transfer(self.vault, to, r.asset, r.amount)
            .map_err(EscrowError::Ledger)?;
        self.record.phase = phase;
        Ok(())
    }

    pub fn release(&mut self) -> Result<(), EscrowError> {
        self.settle(self.record.beneficiary, Phase::Released)
    }

    pub fn cancel(&mut self) -> Result<(), EscrowError> {
        self.settle(self.record.depositor, Phase::Cancelled)
    }
}
