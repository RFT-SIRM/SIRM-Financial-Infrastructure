# Accounting Model

## Two separate accounting projections

The protocol distinguishes:

1. **Holder holdings:** nonnegative balances owned by holders or controlled pools. For each asset, every outstanding unit must appear exactly once in this account universe.
2. **General ledger:** signed double-entry postings for assets, liabilities, equity, income, expense, fees, clearing and control accounts. Every journal entry balances independently per asset.

These projections answer different questions and must not be added together. The holder view reconciles token units to the supply book. The general ledger records financial claims and obligations. A customer liability is not another copy of the customer's token holding.

## Holder-balance reconciliation

For each asset:

- every holder balance is nonnegative;
- the sum of all holder balances equals the supply book's outstanding amount;
- the supply book satisfies `minted = burned + outstanding`.

The account universe must include every place where units can reside, including treasury, escrow, unallocated genesis, validator and protocol-controlled accounts when they hold the asset. Every unit is counted once. General-ledger liability accounts and duplicated control accounts are not included in this holder sum.

A funded transfer debits one holder and credits another without changing supply. A self-transfer is a no-op in the balance model. Issuance increases one holder balance and outstanding supply by the same amount. Burning is bounded by the holder's own balance; the reconciliation theorem then implies that the amount cannot exceed total outstanding supply.

The current Lean model uses signed integers for holder balances so that debit/credit arithmetic is explicit. Its invariant requires every holder balance to be nonnegative. Amounts are natural-number base units; no floating point is used.

## Journal entries

For each asset independently, a journal entry contains signed postings whose sum across the finite account universe is zero. Applying a balanced journal preserves the aggregate signed balance for that asset. The current Lean theorem is stated at this generic level.

A production ledger must add account identifiers, account class, legal owner, authorization policy, normal-balance convention, status, journal sequence, and immutable event references. Those definitions are not all implemented yet.

## Account classes

The target chart of accounts must distinguish at least:

- asset and custody accounts;
- customer and institutional liabilities;
- equity and capital accounts;
- income, expense, and fee accounts;
- treasury and reserve accounts;
- escrow, clearing, and pending-settlement accounts;
- issuance, burn, and other control accounts.

## Per-asset balance

Each journal is balanced per asset. USD, EUR, RFT, and other assets must never be added together as if they shared a unit. FX requires two-sided postings with explicit rate source, quote direction, timestamp, precision, and residual policy.

## Reserves and liabilities

Reserve assets and customer liabilities are separate. Arithmetic reconciliation is not external evidence that assets exist, are unencumbered, or are redeemable. Any reserve claim needs independent evidence with provenance, scope, timestamp, freshness, and exception handling.
