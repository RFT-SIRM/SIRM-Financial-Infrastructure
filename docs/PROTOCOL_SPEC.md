# SIRM Protocol — Initial Specification

SIRM Protocol defines financial state transitions. RFT Network is its planned native execution and settlement network.

## Determinism
Assets have distinct identifiers and integer base units. Consensus-critical arithmetic uses no floating point. Every division has an explicit rounding rule and remainder destination. Overflow rejects; it never wraps.

## State target
The complete state is expected to include account ownership, typed balances, journal sequence, per-asset issued/burned/outstanding supply, escrow and pending pools, reserve and liability accounts, governance, protocol version and state commitment. Not all structures are implemented yet.

## Transition contract
Every operation defines read/write fields, signer authorization, preconditions, arithmetic, journal postings, events, atomicity and invariant obligations. Failed operations cannot partially mutate committed state.

## Accounting rules
1. Balanced postings sum to zero per asset.
2. Transfers conserve aggregate units.
3. Issuance and burn update journal and supply counters together.
4. Redemption extinguishes a defined liability only after its preconditions.
5. A token is not presumed reserve-backed.
6. Pending distributions and rounding remainder are explicit.
7. External valuations and reserve attestations carry provenance and timestamps.

## Genesis
Genesis defines supply, allocation pools, asset registry, governance and validator bootstrap. Founder allocation is 1.309% = 13,090 ppm. Total supply and other pools remain open.

## Upgrades
Each upgrade specifies migration, compatibility, authorization, timelock, rollback/recovery and proof obligations.
