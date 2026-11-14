//! Rust port of the supply and holdings core (`SIRM.FinancialCore`, `SIRM.Holdings`).
//!
//! Semantics follow the Lean definitions: a transfer is allowed if it is a
//! self-transfer (a no-op, even if unfunded) or fully funded; a burn requires the
//! holder to own the amount; issuance always succeeds in Lean. Lean uses unbounded
//! naturals; here all amounts are `u128` and every addition is checked. An
//! overflowing issuance or transfer credit is rejected with `Overflow` and leaves
//! the state unchanged (an explicit extension; Lean has no such case).
//!
//! Every operation validates everything before its first write, so a rejected
//! operation never changes state.

use std::collections::BTreeMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct SupplyState {
    pub minted: u128,
    pub burned: u128,
    pub outstanding: u128,
}

impl SupplyState {
    /// `minted = burned + outstanding`, evaluated without overflow.
    pub fn invariant(&self) -> bool {
        self.burned.checked_add(self.outstanding) == Some(self.minted)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LedgerError {
    UnknownAccount(u32),
    UnknownAsset(u32),
    Insufficient,
    Overflow,
    /// Fee larger than the gross amount (`FeeTransferAllowed` fails; see `fees`).
    FeeExceedsGross,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Holdings {
    accounts: u32,
    assets: u32,
    balance: BTreeMap<(u32, u32), u128>,
    supply: BTreeMap<u32, SupplyState>,
}

impl Holdings {
    pub fn new(accounts: u32, assets: u32) -> Holdings {
        Holdings {
            accounts,
            assets,
            balance: BTreeMap::new(),
            supply: BTreeMap::new(),
        }
    }

    pub fn balance(&self, account: u32, asset: u32) -> u128 {
        self.balance.get(&(account, asset)).copied().unwrap_or(0)
    }

    pub fn supply(&self, asset: u32) -> SupplyState {
        self.supply.get(&asset).copied().unwrap_or_default()
    }

    fn check(&self, account: u32, asset: u32) -> Result<(), LedgerError> {
        if account >= self.accounts {
            return Err(LedgerError::UnknownAccount(account));
        }
        if asset >= self.assets {
            return Err(LedgerError::UnknownAsset(asset));
        }
        Ok(())
    }

    /// Total owner-held units of one asset; `None` on overflow.
    pub fn total_holdings(&self, asset: u32) -> Option<u128> {
        (0..self.accounts).try_fold(0u128, |acc, a| acc.checked_add(self.balance(a, asset)))
    }

    /// Reconciliation: for every asset, supply book balances and total holdings equal
    /// outstanding units.
    pub fn invariant(&self) -> bool {
        (0..self.assets).all(|s| {
            self.supply(s).invariant() && self.total_holdings(s) == Some(self.supply(s).outstanding)
        })
    }

    pub fn transfer(
        &mut self,
        src: u32,
        dst: u32,
        asset: u32,
        amount: u128,
    ) -> Result<(), LedgerError> {
        self.check(src, asset)?;
        self.check(dst, asset)?;
        if src == dst {
            return Ok(());
        }
        let src_bal = self.balance(src, asset);
        let new_src = src_bal
            .checked_sub(amount)
            .ok_or(LedgerError::Insufficient)?;
        let new_dst = self
            .balance(dst, asset)
            .checked_add(amount)
            .ok_or(LedgerError::Overflow)?;
        self.balance.insert((src, asset), new_src);
        self.balance.insert((dst, asset), new_dst);
        Ok(())
    }

    pub fn issue(&mut self, recipient: u32, asset: u32, amount: u128) -> Result<(), LedgerError> {
        self.check(recipient, asset)?;
        let mut s = self.supply(asset);
        let new_bal = self
            .balance(recipient, asset)
            .checked_add(amount)
            .ok_or(LedgerError::Overflow)?;
        s.minted = s.minted.checked_add(amount).ok_or(LedgerError::Overflow)?;
        s.outstanding = s
            .outstanding
            .checked_add(amount)
            .ok_or(LedgerError::Overflow)?;
        self.balance.insert((recipient, asset), new_bal);
        self.supply.insert(asset, s);
        Ok(())
    }

    pub fn burn(&mut self, holder: u32, asset: u32, amount: u128) -> Result<(), LedgerError> {
        self.check(holder, asset)?;
        let new_bal = self
            .balance(holder, asset)
            .checked_sub(amount)
            .ok_or(LedgerError::Insufficient)?;
        let mut s = self.supply(asset);
        s.burned = s.burned.checked_add(amount).ok_or(LedgerError::Overflow)?;
        s.outstanding = s
            .outstanding
            .checked_sub(amount)
            .ok_or(LedgerError::Insufficient)?;
        self.balance.insert((holder, asset), new_bal);
        self.supply.insert(asset, s);
        Ok(())
    }
}

pub const PPM_SCALE: u128 = 1_000_000;
pub const FOUNDER_RATE_PPM: u128 = 13_090;

/// `genesis * 13090 / 1_000_000`, rounded down; `Overflow` if the product exceeds `u128`.
pub fn founder_allocation(genesis_supply: u128) -> Result<u128, LedgerError> {
    genesis_supply
        .checked_mul(FOUNDER_RATE_PPM)
        .map(|p| p / PPM_SCALE)
        .ok_or(LedgerError::Overflow)
}

/// `genesis - founder_allocation(genesis)`; never underflows because the rate is below 100%.
pub fn remaining_genesis_pool(genesis_supply: u128) -> Result<u128, LedgerError> {
    Ok(genesis_supply - founder_allocation(genesis_supply)?)
}
