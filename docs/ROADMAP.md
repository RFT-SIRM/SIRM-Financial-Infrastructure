# Roadmap and Completion Gates

## Phase 0 — formal foundation
- [x] Establish SIRM/RFT naming and boundaries.
- [x] Pin Lean and Mathlib.
- [x] Add supply accounting and 1.309% founder allocation.
- [x] Add first balanced-journal theorem.
- [x] Configure explicit Lean library target.
- [x] Verify the expanded holdings core in Lean CI.
- [x] Configure a theorem-level regression library as the `lake test` driver.
- [ ] Add runtime/property tests and a dedicated linter driver.

## Phase 1 — accounting kernel
- [x] finite typed account/asset identifier domains, account classes, lifecycle metadata, asset decimal precision and issuer/network coherence;
- [x] compose typed asset/issuer lifecycle eligibility with the authorized financial machine's issuance gate;
- [x] exact decimal-to-base-unit conversion with rejection of nonrepresentable precision and a separately parameterized range bound;
- [x] exact rational cross-network base-unit conversion with a conserved, rate- and partition-scoped residual accumulator;
- [x] one-step authorized cross-network migration: exact source burn, target issuance, paired balanced journals, and route/source/recipient-scoped dust carry-forward;
- [ ] replay/idempotency, external bridge settlement/finality, asset-collision policy, and production migration execution;
- balanced journals, account ownership and authorization;
- transfer, fees, escrow, settlement and reversals;
- pending pools, dust and rounding;
- issuance, burn, redemption, liability accounting and supply caps;
- reachable-state safety theorem;
- concrete theorem-level regression suite wired into `lake test`.

## Phase 2 — protocol
- reconcile global field with individual accounts;
- prove distribution equivalent to account-level postings;
- rework negative-entropy semantics and debt safety;
- formalize edge costs, fees, governance and upgrades.

## Phase 3 — reference implementation
- Rust state machine, checked arithmetic and canonical serialization;
- differential/property/fuzz tests, conformance vectors and audit;
- replay and migration tests.

## Phase 4 — RFT Network
- deterministic transaction format, state engine and local ledger;
- block format, state commitment, RPC and single-node devnet;
- validator admission, threat model, consensus and finality;
- multi-node adversarial testnet and recovery.

## Phase 5 — institutional infrastructure
- treasury, reserves, custody attestations, settlement and reporting;
- legal and compliance review per jurisdiction;
- independent security and operational audits.

## Phase 6 — production
No public token sale, customer deposits, real-money settlement or mainnet launch before relevant legal, custody, reserve, security and operational gates are independently satisfied.
