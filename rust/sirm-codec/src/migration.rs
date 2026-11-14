//! Rust port of `SIRM.AssetMigration`, `SIRM.AuthorizedAssetMigration` and
//! `SIRM.ReplayProtectedAssetMigration` at the holdings level.
//!
//! One migration stream has one exact rate (`numerator` target units per
//! `denominator` source units), one source holder, one recipient and a pair of
//! distinct assets. A migration burns `amount` source units from the source holder,
//! issues the released target units to the recipient, and advances the exact dust
//! accumulator, all as one atomic step:
//!
//! ```text
//! acc = dust + amount * numerator;  released = acc / denominator;  dust' = acc % denominator
//! total_source += amount;           total_target += released
//! total_source * numerator == total_target * denominator + dust,   dust < denominator
//! ```
//!
//! The remainder is carried, never rounded away. A request must carry the principal's
//! exact next nonce (stale and future nonces are both rejected, as in Lean). Account
//! control, authority grants, asset/account registries and the network-distinctness
//! proofs are outside this module, as in Lean where they are separate witnesses.
//! Lean works over unbounded naturals; here every product and sum is checked in `u128`
//! and an overflowing step is rejected without writes (explicit extension).

use crate::ledger::{Holdings, LedgerError};
use std::collections::BTreeMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MigrationError {
    NonceMismatch,
    ZeroAmount,
    Insufficient,
    Overflow,
    Ledger(LedgerError),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Migration {
    pub holdings: Holdings,
    source_holder: u32,
    recipient: u32,
    source_asset: u32,
    dest_asset: u32,
    numerator: u128,
    denominator: u128,
    total_source: u128,
    total_target: u128,
    dust: u128,
    next_nonce: BTreeMap<u32, u64>,
}

impl Migration {
    /// `None` if the rate is not positive or the assets are not distinct.
    pub fn new(
        holdings: Holdings,
        source_holder: u32,
        recipient: u32,
        source_asset: u32,
        dest_asset: u32,
        numerator: u128,
        denominator: u128,
    ) -> Option<Migration> {
        if numerator == 0 || denominator == 0 || source_asset == dest_asset {
            return None;
        }
        Some(Migration {
            holdings,
            source_holder,
            recipient,
            source_asset,
            dest_asset,
            numerator,
            denominator,
            total_source: 0,
            total_target: 0,
            dust: 0,
            next_nonce: BTreeMap::new(),
        })
    }

    pub fn total_source(&self) -> u128 {
        self.total_source
    }

    pub fn total_target(&self) -> u128 {
        self.total_target
    }

    pub fn dust(&self) -> u128 {
        self.dust
    }

    pub fn nonce(&self, principal: u32) -> u64 {
        self.next_nonce.get(&principal).copied().unwrap_or(0)
    }

    /// Exact scaled-value equation of the dust subledger, evaluated without overflow
    /// on the 256-bit-free side: `src*num` and `tgt*den + dust` are compared via
    /// checked arithmetic (a state that arose from `migrate` never overflows here).
    pub fn dust_invariant(&self) -> bool {
        let lhs = self.total_source.checked_mul(self.numerator);
        let rhs = self
            .total_target
            .checked_mul(self.denominator)
            .and_then(|v| v.checked_add(self.dust));
        self.dust < self.denominator && lhs.is_some() && lhs == rhs
    }

    /// Target units a migration of `amount` would release now (carried dust included).
    pub fn released(&self, amount: u128) -> Result<u128, MigrationError> {
        let acc = amount
            .checked_mul(self.numerator)
            .and_then(|p| p.checked_add(self.dust))
            .ok_or(MigrationError::Overflow)?;
        Ok(acc / self.denominator)
    }

    pub fn migrate(
        &mut self,
        principal: u32,
        nonce: u64,
        amount: u128,
    ) -> Result<(), MigrationError> {
        let expected = self.nonce(principal);
        if nonce != expected {
            return Err(MigrationError::NonceMismatch);
        }
        if amount == 0 {
            return Err(MigrationError::ZeroAmount);
        }
        if amount > self.holdings.balance(self.source_holder, self.source_asset) {
            return Err(MigrationError::Insufficient);
        }
        let acc = amount
            .checked_mul(self.numerator)
            .and_then(|p| p.checked_add(self.dust))
            .ok_or(MigrationError::Overflow)?;
        let released = acc / self.denominator;
        let new_dust = acc % self.denominator;
        let new_source = self
            .total_source
            .checked_add(amount)
            .ok_or(MigrationError::Overflow)?;
        let new_target = self
            .total_target
            .checked_add(released)
            .ok_or(MigrationError::Overflow)?;
        let next = expected.checked_add(1).ok_or(MigrationError::Overflow)?;
        // Both legs on a copy: burn then issue, committed together or not at all.
        let mut tmp = self.holdings.clone();
        tmp.burn(self.source_holder, self.source_asset, amount)
            .map_err(MigrationError::Ledger)?;
        tmp.issue(self.recipient, self.dest_asset, released)
            .map_err(|e| match e {
                LedgerError::Overflow => MigrationError::Overflow,
                other => MigrationError::Ledger(other),
            })?;
        self.holdings = tmp;
        self.total_source = new_source;
        self.total_target = new_target;
        self.dust = new_dust;
        self.next_nonce.insert(principal, next);
        Ok(())
    }
}
