# Accounting Model

The target system uses multi-asset double-entry accounting. Every journal entry has signed postings whose sum is zero for each asset. The first Lean accounting theorem proves aggregate signed-balance conservation for a balanced entry.

Account classes include assets, liabilities, equity, income, expenses, escrow/clearing, fees, treasury, issuance and burn controls. Balances of different assets are never added without an explicit conversion and valuation source.

A customer balance is a ledger claim. Whether it is a deposit, e-money, custody claim or token entitlement depends on contract and jurisdiction, not the data structure.

Reserve assets and customer liabilities are recorded separately. Arithmetic reconciliation cannot prove that external cash or securities actually exist; that requires independent attestations with source, scope, timestamp, freshness and audit status.

FX is an explicit two-sided journal transaction with rate source, quote direction, timestamp, precision and fee. No implicit exchange rate is permitted.

Every ledger state must reconcile account balances, journal postings, aggregate supply, escrow/pending pools, reserve records and liabilities. Any global-field shortcut must be proved equivalent to account-level postings.
