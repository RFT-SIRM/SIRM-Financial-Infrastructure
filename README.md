# SIRM Financial Infrastructure

**SIRM** is an open, formally specified financial-infrastructure project. **SIRM Protocol** is the normative financial model. **RFT Network** is the planned sovereign execution and settlement network; **RFT** is its planned native asset. This repository is the protocol and assurance foundation—not a live bank, deployed blockchain or customer financial service.

## Design principle

The protocol is specified in Lean 4 first. Implementations must be deterministic, independently testable and demonstrably conform to the specification. A green Lean build proves only the definitions and theorems actually compiled; it does not prove an unverified Rust binary, validator implementation, custodian, legal claim or external reserve.

## Current mathematical foundation

- `SIRM/FinancialCore.lean` defines the supply equation, issuance and burn transitions, and exact founder genesis allocation.
- `SIRM/Accounting.lean` defines signed double-entry postings and per-asset conservation for balanced general-ledger journal entries.
- `SIRM/Holdings.lean` links nonnegative per-account, per-asset holdings to outstanding supply and proves preservation under funded transfers, holder issuance and holder burns. Guarded transfer and burn commands return no next state when their arithmetic preconditions fail.
- `SIRM/StateMachine.lean` derives reachable-state safety from initial-state and transition-preservation obligations.
- `SIRMTests.lean` contains concrete theorem-level regression scenarios; `lake test` is configured to build this dedicated test library.
- `docs/` defines the financial model, network requirements, governance, security assumptions, migration boundaries and staged release gates.

## Accounting boundary

The holder-balance view and signed general ledger are separate projections. The holder view counts each outstanding unit once, including protocol-controlled pools. The general ledger accounts for assets, liabilities, equity, revenue, expenses and control postings. They must be linked by explicit posting rules, never simply added together.

## Genesis founder allocation

The selected one-time founder allocation is **1.309%**, replacing the legacy Rift prototype's 3.14% parameter:

\[
\text{founder}(G)=\left\lfloor\frac{13{,}090\,G}{1{,}000{,}000}\right\rfloor.
\]

The rate is represented exactly as 13,090 parts per million. The remaining genesis pool is explicit and unallocated until separate treasury, validator, ecosystem and community policies are specified. Total supply, decimals, founder address, vesting, custody and other pool sizes are not yet selected.

The nearby Phi-Genesis spectral value `1.309128920280813…` is a distinct research quantity. It does not prove that 1.309% is economically optimal; 1.309% is the explicit tokenomics policy input.

## Target architecture

1. **Formal protocol:** typed assets and accounts, supply rules, holder reconciliation, double-entry accounting, authorization, fees, redemption, governance and state-transition invariants.
2. **Execution implementation:** a deterministic Rust reference implementation whose behavior is tested and refined against the specification.
3. **RFT Network:** independent node software, transaction format, consensus, state commitments, storage, peer-to-peer networking and upgrade/recovery mechanisms.
4. **Institutional applications:** treasury, settlement, custody integrations, reserve attestations, credit and external financial interfaces. These are separate modules, not assumptions built into the core.

## Public verification and privacy

Protocol source, formal statements, build results, releases and state-transition rules are intended to be publicly auditable. Public verifiability does not require publishing personal identity or confidential customer data. A privacy-preserving transaction and disclosure model is a pre-production requirement, not yet implemented.

## Honest status

This is a foundational formal specification. No production network, consensus protocol, native token deployment, bank, reserve backing, redemption guarantee or regulatory approval is claimed. See [formalization status](docs/FORMALIZATION_STATUS.md) and [release gates](docs/RELEASE_GATES.md).
