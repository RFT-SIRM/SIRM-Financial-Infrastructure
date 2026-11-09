# Roadmap

## Phase 0 — Formal foundation

- [x] Establish the repository charter and assurance boundaries.
- [x] Pin Lean 4 and Mathlib versions.
- [x] Introduce an initial aggregate supply model and preservation theorems.
- [ ] Build the Lean project in CI and verify all declarations with the pinned toolchain.
- [ ] Add reproducible proof and dependency instructions.

## Phase 1 — Accounting kernel

- [ ] Typed assets and accounts.
- [ ] Double-entry journal and balanced postings.
- [ ] Account-level transfer and conservation theorems.
- [ ] Issuance, redemption, fee, and dust semantics.
- [ ] Reachability theorem for accounting safety.

## Phase 2 — Protocol and governance

- [ ] Authorization and role model.
- [ ] Threshold approvals and timelocks.
- [ ] Governance-controlled parameter changes.
- [ ] Emergency pause and recovery model.
- [ ] Upgrade and migration safety.

## Phase 3 — Executable reference implementation

- [ ] Rust reference state machine.
- [ ] Canonical serialization and deterministic arithmetic.
- [ ] Differential/property testing against Lean-generated examples.
- [ ] Conformance vectors and independent audit.

## Phase 4 — Ledger and network research

- [ ] Specify transaction ordering and finality requirements.
- [ ] Evaluate replicated state machine and consensus designs.
- [ ] Specify validator membership, incentives, slashing, and recovery.
- [ ] Prototype P2P transport and data availability.
- [ ] Do not launch a token or public network before threat modelling and independent review.

## Phase 5 — Institutional integrations

- [ ] Reserve and liability accounting.
- [ ] Custody and external attestation interfaces.
- [ ] Settlement and reporting.
- [ ] Jurisdiction-specific legal and compliance analysis.
- [ ] Independent operational and security audits.
