//! Rust port of `SIRM.TypedRegistry` and the issuance gate of
//! `SIRM.RegistryAwareFinancialMachine`.
//!
//! Account and asset metadata is total over finite ID domains (`0..accounts`,
//! `0..assets`). Every asset names an issuer account that must exist and must be on the
//! asset's network. Account classes are descriptive, not grants. An asset is
//! *issuance-enabled* iff the asset is active AND its issuer account is active.
//!
//! The registry-aware policy composes the base `auth::Policy` with that gate: issuance
//! needs both the base authorization and issuance eligibility; transfer and burn keep
//! exactly the base predicates (a frozen account or a non-active asset does not restrict
//! them in this layer, as in Lean). A denied operation changes nothing; the gate denial
//! is reported as `AuthError::Unauthorized` like any failed authorization predicate.
//! The migration route checks (`endpointsEnabled`) and the network-distinctness proofs of
//! `AssetMigration` are not part of this module.

use crate::auth::{AuthError, Policy};
use crate::ledger::Holdings;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Network(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AccountClass {
    Holder,
    Treasury,
    ValidatorPool,
    EcosystemPool,
    CommunityPool,
    UnallocatedPool,
    Control,
    Custody,
    Reserve,
    CustomerLiability,
    Equity,
    Income,
    Expense,
    Fee,
    Escrow,
    Clearing,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AccountStatus {
    Active,
    Frozen,
    Closed,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssetStatus {
    Draft,
    Active,
    Frozen,
    Retired,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AccountMeta {
    pub class: AccountClass,
    pub status: AccountStatus,
    pub network: Network,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssetMeta {
    pub symbol: String,
    pub decimals: u32,
    pub issuer: u32,
    pub status: AssetStatus,
    pub network: Network,
}

impl AssetMeta {
    /// `10^decimals` base units per whole unit; `None` if it exceeds `u128`
    /// (Lean's `Nat` is unbounded; the width limit is an explicit extension).
    pub fn base_units_per_whole(&self) -> Option<u128> {
        10u128.checked_pow(self.decimals)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypedRegistryError {
    /// The issuer of this asset is not an account of the registry.
    IssuerOutOfRange(usize),
    /// Lean's `issuer_network_matches`: asset and issuer must share a network.
    IssuerNetworkMismatch(usize),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Registry {
    accounts: Vec<AccountMeta>,
    assets: Vec<AssetMeta>,
}

impl Registry {
    pub fn new(
        accounts: Vec<AccountMeta>,
        assets: Vec<AssetMeta>,
    ) -> Result<Registry, TypedRegistryError> {
        for (i, a) in assets.iter().enumerate() {
            let issuer = accounts
                .get(a.issuer as usize)
                .ok_or(TypedRegistryError::IssuerOutOfRange(i))?;
            if issuer.network != a.network {
                return Err(TypedRegistryError::IssuerNetworkMismatch(i));
            }
        }
        Ok(Registry { accounts, assets })
    }

    pub fn account(&self, id: u32) -> Option<&AccountMeta> {
        self.accounts.get(id as usize)
    }

    pub fn asset(&self, id: u32) -> Option<&AssetMeta> {
        self.assets.get(id as usize)
    }

    /// Unknown accounts are not active.
    pub fn account_active(&self, id: u32) -> bool {
        self.account(id)
            .is_some_and(|a| a.status == AccountStatus::Active)
    }

    /// Unknown assets are not active.
    pub fn asset_active(&self, id: u32) -> bool {
        self.asset(id)
            .is_some_and(|a| a.status == AssetStatus::Active)
    }

    /// Active asset and active issuer account (additional to authorization and control).
    pub fn issuance_enabled(&self, asset: u32) -> bool {
        self.asset_active(asset)
            && self
                .asset(asset)
                .is_some_and(|a| self.account_active(a.issuer))
    }
}

/// `withAssetRegistryIssuanceGate policy registry`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GatedPolicy {
    policy: Policy,
    registry: Registry,
}

impl GatedPolicy {
    pub fn new(policy: Policy, registry: Registry) -> GatedPolicy {
        GatedPolicy { policy, registry }
    }

    pub fn registry(&self) -> &Registry {
        &self.registry
    }

    pub fn may_transfer(&self, p: u32, source: u32, dest: u32, asset: u32, amount: u128) -> bool {
        self.policy.may_transfer(p, source, dest, asset, amount)
    }

    pub fn may_issue(&self, p: u32, issuer: u32, recipient: u32, asset: u32, amount: u128) -> bool {
        self.policy.may_issue(p, issuer, recipient, asset, amount)
            && self.registry.issuance_enabled(asset)
    }

    pub fn may_burn(&self, p: u32, holder: u32, asset: u32, amount: u128) -> bool {
        self.policy.may_burn(p, holder, asset, amount)
    }

    pub fn transfer(
        &self,
        ledger: &mut Holdings,
        p: u32,
        source: u32,
        dest: u32,
        asset: u32,
        amount: u128,
    ) -> Result<(), AuthError> {
        self.policy.transfer(ledger, p, source, dest, asset, amount)
    }

    pub fn issue(
        &self,
        ledger: &mut Holdings,
        p: u32,
        issuer: u32,
        recipient: u32,
        asset: u32,
        amount: u128,
    ) -> Result<(), AuthError> {
        if !self.may_issue(p, issuer, recipient, asset, amount) {
            return Err(AuthError::Unauthorized);
        }
        self.policy
            .issue(ledger, p, issuer, recipient, asset, amount)
    }

    pub fn burn(
        &self,
        ledger: &mut Holdings,
        p: u32,
        holder: u32,
        asset: u32,
        amount: u128,
    ) -> Result<(), AuthError> {
        self.policy.burn(ledger, p, holder, asset, amount)
    }
}
