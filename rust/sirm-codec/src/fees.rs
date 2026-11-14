//! Rust port of `SIRM.FeeAccounting` holdings semantics.
//!
//! A fee transfer debits the payer the gross amount, credits the beneficiary
//! `gross - fee` and the collector `fee`. Lean's `FeeTransferAllowed` is
//! `fee <= gross` and `gross <= balance(payer)`; the gross funding condition is
//! mandatory even when roles coincide (self legs are no-ops but the check stays).
//! `feeTransferHoldings` applies the net leg then the fee leg to one final state.
//!
//! Here the whole operation is atomic: both legs run on a copy and are committed
//! only if both succeed. `u128` credit overflow is an explicit extension (Lean is
//! unbounded) and is rejected without writes. Authorization (transfer policy and
//! fee policy) is outside this module, as in Lean where policies are separate.

use crate::ledger::{Holdings, LedgerError};

/// `gross - fee`, defined when `fee <= gross`.
pub fn net_amount(gross: u128, fee: u128) -> Result<u128, LedgerError> {
    gross.checked_sub(fee).ok_or(LedgerError::FeeExceedsGross)
}

pub fn fee_transfer(
    h: &mut Holdings,
    payer: u32,
    beneficiary: u32,
    collector: u32,
    asset: u32,
    gross: u128,
    fee: u128,
) -> Result<(), LedgerError> {
    // Range validation of every role first (same errors as the plain transfer).
    h.clone().transfer(payer, beneficiary, asset, 0)?;
    h.clone().transfer(payer, collector, asset, 0)?;
    let net = net_amount(gross, fee)?;
    if gross > h.balance(payer, asset) {
        return Err(LedgerError::Insufficient);
    }
    let mut tmp = h.clone();
    tmp.transfer(payer, beneficiary, asset, net)?;
    tmp.transfer(payer, collector, asset, fee)?;
    *h = tmp;
    Ok(())
}
