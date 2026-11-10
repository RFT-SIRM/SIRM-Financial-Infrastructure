# SIRM Protocol: Initial Normative Specification

## Purpose

SIRM Protocol defines financial state and allowed transitions independently of any particular execution network. RFT Network is the planned sovereign execution and settlement environment. The initial release is a formal specification and not a production protocol.

## Determinism

- All consensus-critical amounts use integer base units.
- No floating-point operation is permitted in state transitions.
- Every division names its rounding mode and residual destination.
- Overflow, underflow, invalid casts and invalid state transitions reject atomically.
- Transaction encoding, event encoding and state commitments must be canonical.

## Accounting

- Every journal is balanced per asset.
- Asset identifiers are never implicitly interchangeable.
- The holder-balance view is nonnegative and reconciles per-asset outstanding supply exactly.
- The signed general ledger is a separate projection for assets, liabilities, equity, income, expense and control accounts; it is not added to holder balances.
- Transfers do not change aggregate supply and require sufficient funds, except self-transfers, which are balance no-ops.
- Issuance increases the recipient holder balance and outstanding supply by the same amount.
- Burn decreases a holder balance and outstanding supply by the same amount, and cannot burn more than that holder holds.
- Escrow, pending, fee, clearing and unallocated pools must be represented explicitly in the holder universe when they contain units.
- Customer liabilities and reserve assets are distinct.
- Redemption extinguishes a named liability only after all stated preconditions and settlement rules are satisfied.

## Authorization

Each state-changing operation specifies signer requirements, roles, thresholds, limits, pause conditions, expiry, nonce/replay protection and recovery behavior. No single operational key should be able to mint without limit, rewrite accounting history, seize customer balances or change consensus rules unilaterally.

## State transition contract

For every operation, the complete protocol definition must include: input schema; read/write set; authorization; preconditions; arithmetic; journal postings; state changes; emitted events; atomicity; failure codes; and invariant-preservation obligations. In the current Lean holder model, arithmetic preconditions are explicit proof arguments to guarded transitions. This establishes admissibility at the specification level; it is not yet a runtime transaction decoder, signature check, or failure-code implementation.

## Genesis

Genesis fixes the chain identifier, protocol version, asset registry, total supply, allocation table, founder allocation, treasury and validator policy, initial governance, validator bootstrap and genesis state commitment. The only selected tokenomic rate at this stage is the founder's one-time 1.309% share (13,090 ppm). All other allocations remain unallocated until specified. Every issued genesis unit must be assigned exactly once in the holder-balance view.

## Upgrades

Each upgrade must define the prior and new protocol versions, authorization threshold, notice period/timelock, migration function, state-equivalence obligations, compatibility window, abort procedure and recovery plan. An upgrade may not silently rewrite finalized journal history.

## Privacy

Public code and verifiable state transitions are required. Personal identity and confidential customer data must not be exposed by default. Transaction privacy, selective disclosure and institutional compliance proofs remain an explicit design workstream before production.
