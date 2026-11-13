//! Rust port of the static authorization layer (`SIRM.Authorization`,
//! `SIRM.AuthorityRegistry`, `SIRM.AccountControl`).
//!
//! An operation is authorized iff the acting principal controls the
//! source/issuer/holder account AND a grant with the exact
//! (principal, scope, asset) key exists whose single-operation limit is at least the
//! amount. Authorization is checked before any ledger precondition; a failed check
//! changes nothing. This is a static snapshot: no revocation, expiry, signatures or
//! key custody, exactly as in the Lean modules.

use crate::ledger::{Holdings, LedgerError};
use std::collections::{BTreeMap, BTreeSet};

/// The exact account operation a grant covers. A transfer is directional.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Scope {
    Transfer { source: u32, destination: u32 },
    Issue { issuer: u32, recipient: u32 },
    Burn { holder: u32 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Grant {
    pub principal: u32,
    pub scope: Scope,
    pub asset: u32,
    pub max_amount: u128,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegistryError {
    /// Two grants share (principal, scope, asset) but differ in limit (Lean `unique_scope`).
    ConflictingGrant,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AuthError {
    Unauthorized,
    Ledger(LedgerError),
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Policy {
    grants: BTreeMap<(u32, Scope, u32), u128>,
    control: BTreeSet<(u32, u32)>,
}

impl Policy {
    /// Identical duplicate grants are accepted; conflicting limits are rejected.
    pub fn new(grants: &[Grant], control: &[(u32, u32)]) -> Result<Policy, RegistryError> {
        let mut map = BTreeMap::new();
        for g in grants {
            let key = (g.principal, g.scope, g.asset);
            match map.get(&key) {
                Some(&existing) if existing != g.max_amount => {
                    return Err(RegistryError::ConflictingGrant)
                }
                _ => {
                    map.insert(key, g.max_amount);
                }
            }
        }
        Ok(Policy {
            grants: map,
            control: control.iter().copied().collect(),
        })
    }

    pub fn controls(&self, principal: u32, account: u32) -> bool {
        self.control.contains(&(principal, account))
    }

    pub fn allows(&self, principal: u32, scope: Scope, asset: u32, amount: u128) -> bool {
        self.grants
            .get(&(principal, scope, asset))
            .is_some_and(|&max| amount <= max)
    }

    pub fn may_transfer(
        &self,
        principal: u32,
        source: u32,
        destination: u32,
        asset: u32,
        amount: u128,
    ) -> bool {
        self.controls(principal, source)
            && self.allows(
                principal,
                Scope::Transfer {
                    source,
                    destination,
                },
                asset,
                amount,
            )
    }

    /// Control of the issuer is required; the recipient need not be controlled.
    pub fn may_issue(
        &self,
        principal: u32,
        issuer: u32,
        recipient: u32,
        asset: u32,
        amount: u128,
    ) -> bool {
        self.controls(principal, issuer)
            && self.allows(principal, Scope::Issue { issuer, recipient }, asset, amount)
    }

    pub fn may_burn(&self, principal: u32, holder: u32, asset: u32, amount: u128) -> bool {
        self.controls(principal, holder)
            && self.allows(principal, Scope::Burn { holder }, asset, amount)
    }

    pub fn transfer(
        &self,
        ledger: &mut Holdings,
        principal: u32,
        source: u32,
        destination: u32,
        asset: u32,
        amount: u128,
    ) -> Result<(), AuthError> {
        if !self.may_transfer(principal, source, destination, asset, amount) {
            return Err(AuthError::Unauthorized);
        }
        ledger
            .transfer(source, destination, asset, amount)
            .map_err(AuthError::Ledger)
    }

    /// Mints to `recipient`; like Lean, it does not debit the issuer account.
    pub fn issue(
        &self,
        ledger: &mut Holdings,
        principal: u32,
        issuer: u32,
        recipient: u32,
        asset: u32,
        amount: u128,
    ) -> Result<(), AuthError> {
        if !self.may_issue(principal, issuer, recipient, asset, amount) {
            return Err(AuthError::Unauthorized);
        }
        ledger
            .issue(recipient, asset, amount)
            .map_err(AuthError::Ledger)
    }

    pub fn burn(
        &self,
        ledger: &mut Holdings,
        principal: u32,
        holder: u32,
        asset: u32,
        amount: u128,
    ) -> Result<(), AuthError> {
        if !self.may_burn(principal, holder, asset, amount) {
            return Err(AuthError::Unauthorized);
        }
        ledger
            .burn(holder, asset, amount)
            .map_err(AuthError::Ledger)
    }
}
