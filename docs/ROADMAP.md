# Roadmap and Completion Gates

**Verified baseline:** `main` is at `85f69841b13d9ff62604685e158449904f15c3eb` (PR #31). PRs #26–#31 each passed all 18 GitHub Actions jobs on the PR head before squash merge: one Lean build/theorem-test job and 17 static audits. Earlier escrow milestones (PR #23 time locks, PR #24 dispute freeze) are recorded below.

**Status rule:** [x] means the stated scope exists in the Lean model and passed the recorded CI gate. It does not mean a production implementation or external service exists.

## Phase 0 — formal development foundation
- [x] Establish SIRM/RFT naming and repository boundaries.
- [x] Pin Lean and Mathlib; configure the SIRM library and theorem-level test driver.
- [x] Configure PR CI: one Lean job and 17 static audits.
- [ ] Add a dedicated Lean linter driver.
- [ ] Add runtime/property tests when an executable reference implementation exists.

## Phase 1 — financial accounting kernel

### Formalized and CI-checked
- [x] Per-asset supply state, holder balances and holder/supply reconciliation.
- [x] Balanced per-asset journals, aggregate signed-ledger conservation and mapped subledger agreement under stated assumptions.
- [x] Guarded transfer, issuance and burn transitions in an abstract combined financial state.
- [x] Separate finite authority grants and principal/account-control relations.
- [x] Typed finite account/asset registries, lifecycle metadata and issuer/network coherence.
- [x] Exact decimal-to-integer base-unit conversion without floating point or nonzero precision truncation.
- [x] Exact rational cross-network conversion with rate- and partition-indexed residual carry-forward.
- [x] One abstract authorized migration pairing source burn, destination issuance, two balanced journals and residual update.
- [x] Migration-scoped per-principal sequential nonce: reject mismatches, advance the accepted nonce with migration state, and preserve other principals' nonces.
- [x] Reachable-state invariant theorems and theorem regressions wired into `lake test`.
- [x] Abstract typed transaction envelope: exact request-ID receipt replay, conflict rejection, nonce mismatch rejection, receipt consistency, and financial-invariant preservation in reachable states.
- [x] Abstract authorization-denial cache: cache only at the exact current nonce, do not consume nonce or change financial state, enforce one request-ID namespace across success/denial receipts, and replay the cached denial after a later nonce advance.
- [x] Abstract insufficient-funds denial cache for authorized non-self transfers and burns: cache only at the exact current nonce and an unused request ID, do not change balances/GL/nonce, and return the original insufficient-funds response on exact retry. Self-transfers and unauthorized requests are not classified as insufficient-funds failures; issuance has no debit-funding precondition.

- [x] Exact-base-unit fee transfer with separate transfer/fee authorization, a balanced combined journal, and holder/GL/supply conservation (tariff and non-holder revenue policy remain open).
- [x] One-record escrow open, release and cancellation with separate authorization, exact vault backing, and holder/GL/supply conservation.
- [x] Multiple concurrent escrow IDs, aggregate per-asset pending liabilities, and exact reconciliation to the designated vault-holder balance and mapped GL subledger.
- [x] Abstract escrow expiry/time locks: fixed per-ID deadlines, monotone discrete time, pre-deadline release/cancel guards, and a separately authorized post-deadline refund recorded as `expired`, preserving vault/GL/pool backing. Wall-clock binding and scheduler liveness remain open.

### Merged in PR #24
- [x] First-stage escrow dispute intake/freeze (PR #24; all 18 checks passed on the merged commit). An authorized claimant can flag a pending escrow before its deadline; release, voluntary cancellation, and timeout expiry are then blocked for that ID while funds remain in the pooled vault. Adjudication, evidence verification, appeals, and outcome-specific settlement remain open.

### Still open
- [ ] Dispute adjudication, evidence validation/provenance, outcome-specific beneficiary/refund settlement, appeals, and reversal policy.
- [ ] External settlement evidence and finality, including the policy for reconciling external delivery with the internal escrow state.
- [ ] Pending-pool and residual accounting beyond the migration-specific dust subledger.
- [ ] Redemption obligations, liability accounts, reserve assumptions and supply caps.
- [ ] Complete posting policy for custody, customer-liability and control accounts.
- [ ] Production transaction execution: canonical bytes/hashing, signatures/thresholds, expiry, persisted nonce/receipt storage for remaining failure classes, deterministic event/error schemas, rollback and crash recovery. The abstract Lean model covers successful receipts plus cached authorization and insufficient-funds denials, but not expiry/signature/other failure classes or a persisted runtime implementation.
- [ ] Asset-collision, route-change and migration-failure policies.

## Phase 2 — protocol-level semantics
- [ ] Reconcile global field with individual account states.
- [ ] Prove distribution equivalence to account-level postings where required.
- [ ] Formalize negative-entropy semantics and debt safety.
- [ ] Define edge costs, network fees, governance and upgrade transitions.
- [ ] Verify that new operations compose without weakening existing invariants.

## Phase 3 — deterministic Rust reference implementation
- [ ] Implement the stabilized state-transition model separately in Rust. Partial: holdings-level ports with differential tests exist (`rust/sirm-codec`: envelope policy, ledger core, authorization/account control, integrated processor, fees, escrow, time-locks, dispute freeze, asset migration, typed registry with the issuance gate); the network-distinctness proofs of migration, the Lean proof-carrying machine structure and everything above the holdings level are not ported.
- [ ] Define canonical transaction and state serialization. Partial: request encoding v0 is a proposal with a Python reference, Lean round-trip/injectivity theorems for a bounded request record, and a Rust codec; adoption, expiry and state commitments are open. A signed request layer v0 (chain id and Ed25519, `engineering/canonical_encoding/SPEC_signed_request_v0.md`) is a proposal with a Python reference and Rust implementation; key management and thresholds are open. State commitment v0 (`engineering/canonical_encoding/SPEC_state_commitment_v0.md`) is a sparse Merkle tree proposal over balances, supply and nonces with a Python reference and Rust implementation; other modules are not committed. Receipt encoding v0 is a separate proposal (`engineering/canonical_encoding/SPEC_receipt_v0.md`) with a Python reference and Rust codec, not adopted and without Lean theorems.
- [x] Rust reference codec for request encoding v0 with conformance tests against the shared Python vectors (`rust/sirm-codec`; proposal level; checked by the `Rust` CI job).
- [ ] Use checked integer arithmetic and deterministic failure behavior. Partial: the ported modules use checked `u128` and validate before writing; the bounded-width extension of Lean's unbounded `Nat` is documented per module and not proved.
- [ ] Add differential tests against Lean examples, plus property, fuzz, replay and migration tests. Partial: seeded differential traces against independent Python references run in CI for every ported module; Lean-example extraction, fuzzing and crash/replay campaigns are open.
- [ ] Document Lean-to-Rust refinement/conformance and obtain independent review.

## Phase 4 — RFT Network
- [ ] Specify deterministic execution, block format and state commitments.
- [ ] Build a single-node local development network before selecting multi-node consensus.
- [ ] Specify authenticated transport, peer discovery, node identity, validator admission and recovery.
- [ ] Analyze consensus safety/liveness, finality, censorship, equivocation and data availability.
- [ ] Run an adversarial multi-node testnet and exercise upgrades and recovery.

No consensus algorithm or production network is claimed as selected or deployed by the current financial foundation.

## Phase 5 — institutional infrastructure
- [ ] Specify treasury, custody, reserve evidence, settlement and reporting interfaces.
- [ ] Establish legal responsibilities and jurisdiction-specific compliance where applicable.
- [ ] Obtain independent custody, reserve, security, privacy and operational attestations.
- [ ] Keep external legal and asset claims separate from properties proved by Lean.

## Phase 6 — production release
No public token sale, customer deposits, real-money settlement or mainnet launch before the relevant legal, custody, reserve, security, implementation and operational gates are independently satisfied.

## Recommended execution order
1. Complete open accounting semantics: formalize dispute adjudication, evidence validation/provenance, outcome-specific beneficiary/refund settlement, appeals and reversal policy; then address redemption obligations, reserve assumptions, liability accounts and complete custody/customer-liability postings. Dispute intake/freeze, concurrent escrow IDs, pooled vault/GL reconciliation and discrete expiry guards are formalized. Wall-clock binding and timeout scheduler liveness remain open. Fee tariff policy and non-holder revenue classification remain open.
2. Complete the transaction envelope's remaining semantics (canonical encoding and hashing, signature/threshold rules, expiry, cached responses for other deterministic failures, and deterministic failure schemas), then refine it to a persisted runtime processor.
3. Implement and test Rust against the stabilized Lean model.
4. Build a single-node development network; only then design and test consensus.
5. Proceed to institutional pilots and production gates only after independent reviews.

A network cannot repair an incomplete accounting model, and consensus cannot establish the correctness of an underspecified financial transition.


Escrow formalization is layered: `EscrowAccounting` proves the single-record authorized lifecycle; `EscrowRegistry` adds concurrent, permanently allocated IDs; `EscrowPooledReserve` derives aggregate pending obligations by asset; `EscrowFinancialIntegration` proves those obligations equal the designated vault-holder balance and mapped GL subledger; `EscrowTimeLocks` adds discrete per-ID deadlines and timeout refunds; and `EscrowDisputes` adds a first-stage authorized dispute freeze. Dispute adjudication, evidence verification, appeals, outcome-specific settlement, external settlement finality, reversals and production persistence/idempotency remain open.
- [ ] Integrated state machine: proposal only (`docs/INTEGRATED_STATE_MACHINE_PROPOSAL.md`): one shared ledger and one request pipeline for transfer, issue, burn, escrow, time and migration, in steps I1 to I5. Steps I1 and I2 exist: an independent Python reference with seeded traces (`scripts/integrated_machine_reference.py`, `engineering/ledger_core/results/integrated_trace_v0.json`) and a Rust port (`rust/sirm-codec/src/integrated.rs`) checked outcome by outcome; the old processor is reproduced byte for byte. Step I3 (request encoding v1 for all ten operations, `engineering/canonical_encoding/SPEC_request_v1.md`) also exists, and so does the single state commitment v5 for the integrated machine (`engineering/canonical_encoding/SPEC_state_commitment_v5.md`, step I4); signed request v2 that carries request v1 (`engineering/canonical_encoding/SPEC_signed_request_v2.md`; Rust verifies Ed25519 only, post-quantum wires are refused for lack of a verifier) and the Lean model of the request pipeline (`SIRM/IntegratedPipeline.lean`, generic, step I5 partial) exist; the concrete Lean ledger slice (`SIRM/IntegratedLedger.lean`: conservation, vault backing, the migration equation, frozen disputed escrows and monotone time for all ten operations, natural-number amounts) exists; authorization in that Lean model is proved (deny by default, no debit without control, time, filing and mint only by grant; PR #75), the `u128` ceiling is added to it in `SIRM/BoundedAmounts.lean` (PR #77, with a differential test against the Rust machine in PR #78), and the escrow and migration ports in Rust still keep their own ledgers.
- [ ] Post-quantum security architecture: a proposal exists (`docs/POST_QUANTUM_SECURITY_ARCHITECTURE.md`, `docs/PQ_DECISIONS_PROPOSED.md`), not adopted and not reviewed; no implementation. Phases P1 to P5 and their gates are listed there. P1 has started (Lean abstract models `SIRM/SignatureSuite.lean` and, for P2 key transitions, `SIRM/KeyRegistry.lean`, `SIRM/ThresholdAuth.lean` and `SIRM/RecoveryDelay.lean` and the generic `SIRM/AuthenticatedStep.lean` also exist; state commitment v1 adds the key and suite registries and a protocol header in Python and Rust, still a partial root; a Rust port of the key lifecycle, recovery delay and threshold models, checked differentially against Python, exists in `rust/sirm-codec/src/keys.rs`): signed request v1 (suite registry, ML-DSA-65, hybrid) is a Python-only proposal (`engineering/canonical_encoding/SPEC_signed_request_v1.md`). P3 evaluation recorded in `docs/PQ_RUST_LIBRARY_EVALUATION.md` (RustCrypto `ml-dsa` 0.1.2 and `aws-lc-rs` 1.19.0 both verify the frozen ML-DSA-65 vectors; verification only, no library chosen, no dependency added).
