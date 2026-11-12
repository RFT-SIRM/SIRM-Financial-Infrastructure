# Roadmap and Completion Gates

**Verified baseline:** PR #11 is merged into `main` at `8588b61401b6eae02510fc5f9772acf47e0dd3e5`. Its exact head passed 18/18 GitHub Actions checks: one Lean build/theorem-test job and 17 static audits.

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

### Still open
- [x] Exact-base-unit fee transfer with separate transfer/fee authorization, a balanced combined journal, and holder/GL/supply conservation (tariff and non-holder revenue policy remain open).
- [x] One-record escrow open, release and cancellation with separate authorization, exact vault backing, and holder/GL/supply conservation.
- [ ] Multiple concurrent escrow IDs, settlement finality, expiry, dispute handling and reversal policy.
- [ ] Pending-pool and residual accounting beyond the migration-specific dust subledger.
- [ ] Redemption obligations, liability accounts, reserve assumptions and supply caps.
- [ ] Complete posting policy for custody, customer-liability and control accounts.
- [ ] Production-wide transaction envelope: canonical representation, signatures/thresholds, expiry, operation-wide nonce, idempotent replay responses, deterministic errors and rollback.
- [ ] Asset-collision, route-change and migration-failure policies.

## Phase 2 — protocol-level semantics
- [ ] Reconcile global field with individual account states.
- [ ] Prove distribution equivalence to account-level postings where required.
- [ ] Formalize negative-entropy semantics and debt safety.
- [ ] Define edge costs, network fees, governance and upgrade transitions.
- [ ] Verify that new operations compose without weakening existing invariants.

## Phase 3 — deterministic Rust reference implementation
- [ ] Implement the stabilized state-transition model separately in Rust.
- [ ] Define canonical transaction and state serialization.
- [ ] Use checked integer arithmetic and deterministic failure behavior.
- [ ] Add differential tests against Lean examples, plus property, fuzz, replay and migration tests.
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
1. Complete open accounting semantics: extend the verified one-record escrow lifecycle to concurrent escrow IDs, then formalize settlement finality, expiry, dispute/reversal policy, redemption obligations, liabilities and complete custody/customer-liability postings. Fee tariff policy and non-holder revenue classification remain open.
2. Specify the complete transaction envelope, including global replay/idempotency and deterministic failure behavior.
3. Implement and test Rust against the stabilized Lean model.
4. Build a single-node development network; only then design and test consensus.
5. Proceed to institutional pilots and production gates only after independent reviews.

A network cannot repair an incomplete accounting model, and consensus cannot establish the correctness of an underspecified financial transition.


The first escrow lifecycle is specified as a single-use record: a funded deposit moves to a dedicated vault holder, followed by either release to the recorded beneficiary or cancellation back to the depositor. The vault is exactly backed while pending, and the record cannot reopen after a terminal transition. This does not model concurrent escrow IDs, external settlement finality, dispute resolution, expiry, or production idempotency.
