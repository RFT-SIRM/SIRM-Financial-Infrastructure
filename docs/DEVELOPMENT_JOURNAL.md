# Development Journal — 2026-11-10

## Work block: registry-aware issuance in the combined financial machine

### Verified starting point

- Repository: `RFT-SIRM/SIRM-Financial-Infrastructure`.
- Working branch: `foundation/registry-aware-issuance-machine-2026-11-10`.
- Exact starting commit: `78c86700d77ccacde6d026ffc4ff5c5f056a0681`.
- The local branch was created from the fetched `FETCH_HEAD` at that exact SHA; the worktree was clean before this patch.
- The same branch/ref was verified on GitHub at the same base SHA.

### Objective and adopted scope

Integrate the typed `AssetRegistry.issuanceEnabled` predicate into the already-proved authorized financial machine without replacing the authority-grant, account-control, holder, journal, or conservation layers.

The effective issue predicate is:

```lean
existingPolicy.mayIssue state principal issuer recipient asset amount ∧
  registry.issuanceEnabled asset
```

`registry.issuanceEnabled asset` means that the asset is active and its issuer account is active. The original policy therefore continues to require the principal's account control and the exact authority grant (including issuer, recipient, asset, and amount limit).

Transfers and burns intentionally retain their existing policy predicates in this work block. No issuer debit is introduced: issuance continues to credit the recipient and use the explicitly unmapped GL counterpart account.

### Expected source changes

- Add `SIRM/RegistryAwareFinancialMachine.lean`.
- Import that module from `SIRM.lean`.
- Add theorem-level tests in `SIRMTests.lean` for allowed active-asset issuance, denial for draft assets, denial for frozen issuers, unchanged transfer/burn gates, and a reachable typed issuance trace preserving the full financial invariant.
- Update README, formalization status, mathematical scope, roadmap, testing notes, and decisions.

### Verification sequence

Run from the repository root, on the branch above:

```bash
lake build SIRM.RegistryAwareFinancialMachine
lake build SIRM
lake test
python3 scripts/ci_audit.py all
git diff --check
```

Expected static audit count: 17. Inspect the complete `git diff`, not just the summary. Record the exact output and commit SHA in the journal before pushing. Do not state that a test passed unless its command completed successfully for the exact source tree.

### Commit and PR discipline

1. Do not commit until the target module, full `SIRM` build, theorem-level test library, all 17 static audits, and `git diff --check` pass.
2. Make one coherent commit on this branch only.
3. Push this branch once and verify the remote branch SHA equals the local commit SHA.
4. Open one PR against `main`; verify its exact head SHA and all 18 checks (one Lean job plus 17 static audits).
5. Merge only after all required checks are green. Do not start another CI run while the current run is active.

### Remaining formalization after this block

The next narrowly scoped accounting task is exact asset-denominated base-unit handling: define conversion between whole units and integer base units using `10 ^ decimals`, prove exactness for integral values and explicit rejection/handling of fractional precision, then bound runtime overflow/range separately. Do not select production RFT decimals here. Avoid floating-point arithmetic in the normative model.

Open topics not claimed as solved: asset migration and cross-network conversion, legal identity/title, cryptographic signatures, lifecycle transition policy, production transaction envelopes, Rust refinement, reserve evidence, consensus, and runtime testing.

## Work block: exact asset-denominated base units

### Verified starting point

- Repository: `RFT-SIRM/SIRM-Financial-Infrastructure`.
- Working branch: `foundation/exact-asset-base-units-2026-11-10`.
- Exact starting commit after the preceding squash merge: `626d38dce1a5ed0d18e8b1802c19576cefd7f9d5`.
- The branch was created from that SHA and verified identical to it on GitHub before patching.

### Objective and adopted arithmetic

Represent a nonnegative decimal input as `(coefficient, decimalPlaces)`, meaning `coefficient / 10^decimalPlaces` whole asset units. For an asset with `d` metadata decimals:

- if `decimalPlaces ≤ d`, multiply the coefficient by `10^(d - decimalPlaces)`;
- if `decimalPlaces > d`, divide by `10^(decimalPlaces - d)` only when the remainder is zero;
- otherwise return `none`. There is no truncation, rounding, floating point, or implicit precision loss.

Whole-unit conversion uses `10^d`. A separate bounded conversion takes an explicit inclusive maximum and returns `Fin (max + 1)`. This is a proof-level range guard only: `Nat` remains unbounded, and no concrete Rust/C integer width or runtime overflow policy is selected.

### Expected source changes

- Add `SIRM/AssetUnits.lean` and import it from `SIRM.lean` after `SIRM.TypedRegistry`.
- Add theorem-level regressions for whole units, exact input precision, extra trailing zeros, rejected nonzero excess precision, and in-range/out-of-range bounded conversion.
- Update README, formalization status, mathematical scope, roadmap, testing notes, decisions, and this journal.

### Verification sequence

```bash
lake build SIRM.AssetUnits
lake build SIRM
lake test
python3 scripts/ci_audit.py all
git diff --check
```

Do not commit until the target module, full `SIRM` build, theorem-level test driver, all 17 static audits, and diff checks pass. Then create one commit on this branch, push once, verify the remote SHA, open one PR against `main`, and merge only after all 18 CI jobs are green.

### Explicitly deferred

- Selecting production decimal precision for RFT or any other asset.
- Selecting a concrete 32-bit/64-bit or platform-specific runtime integer bound.
- Rust checked-arithmetic implementation and Lean-to-Rust refinement proof.
- Fees, FX, migration, residual rounding, and signed-value parsing.


## Work block: exact cross-network migration arithmetic and residual accounting

### Verified starting point

- Repository: `RFT-SIRM/SIRM-Financial-Infrastructure`.
- Working branch: `foundation/exact-asset-migration-dust-2026-11-10`.
- Exact starting commit after the preceding squash merge: `7655d68e104b1d0def05135b72b3070897c546a4`.
- The remote branch was created from that exact `main` SHA after confirming `main` matched it.

### Objective and adopted arithmetic

A route supplies a positive rate `numerator / denominator`, interpreted as target base units per source base unit. For source amount `s`, conversion proves:

```text
s * numerator = targetBaseUnits * denominator + dustNumerator
0 <= dustNumerator < denominator
```

No floating point, implicit rounding, or silent residual loss is permitted. A cumulative accumulator adds new scaled source value to the previously carried residual, emits only completed target base units, and retains the new residual. The accumulator is indexed by the exact rate and an explicit accounting partition; different rates or partitions cannot share a state by definitional equality. A shared partition, where deliberately chosen, remains an explicit policy decision.

A route connects distinct registered asset IDs on distinct network IDs. Route eligibility requires both endpoint assets and both issuer accounts to be active. This is deliberately only route metadata and exact arithmetic: source redemption/burn, destination issuance, authority, custody, replay/idempotency, bridge finality, rollback, and asset-collision policy remain unformalized.

No production exchange rate, asset decimals, dust pooling rule, or economic valuation is selected.

### Expected source changes

- Add `SIRM/AssetMigration.lean` and import it from `SIRM.lean`.
- Add generic quotient/remainder and cumulative dust-conservation definitions/theorems.
- Add a route structure tied to the typed registry with distinct-asset and cross-network proofs plus active endpoint/issuer eligibility.
- Add synthetic-rate regression tests and update the architecture decision, roadmap, mathematical scope, formalization status, README, testing notes, and journal.

### Verification sequence

```bash
lake build SIRM.AssetMigration
lake build SIRM
lake test
python3 scripts/ci_audit.py all
git diff --check
```

Do not commit until the target module, full `SIRM` build, theorem-level test driver, all 17 static audits, and diff checks pass. Inspect the full staged Lean diff before one commit, one push, and one PR against `main`.

### Explicitly deferred

- Production exchange rates, FX/market pricing, and denomination policy.
- Pooling residuals across beneficiaries or different routes/rates.
- Source token burn/redemption and destination mint/issuance transactions.
- Authorization, custody proofs, bridge finality, replay/idempotency, rollback, asset collision and insolvency policy.
- Rust implementation and Lean-to-Rust refinement.


## Work block: authorized atomic cross-network migration

### Verified starting point

- Repository: `RFT-SIRM/SIRM-Financial-Infrastructure`.
- Working branch: `foundation/atomic-authorized-asset-migration-2026-11-10`.
- Exact starting commit after PR #9 squash merge: `0d88ee628323afc4c5cc454114e82a082a34e6a9`.
- The local branch was fetched and checked out from that exact remote SHA; the worktree was clean before patching.

### Reviewed design

- A migration partition is fixed to one route, one source holder, and one destination recipient. Proof fields bind the source holder and recipient to the respective registered networks.
- The same principal must satisfy the existing controlled policy for both operations: control of the source holder plus an exact `.burn sourceHolder` grant, and control of the destination asset issuer plus an exact `.issue destinationIssuer recipient` grant for the computed target amount.
- Both endpoint assets and issuers must be active through `route.endpointsEnabled`; the source holder and recipient accounts must also be active.
- The single transition burns source base units, issues only the newly released target base units, posts the two asset-specific balanced journals, and advances the exact residual claim accumulator. There is no admitted intermediate state with only one side applied.
- The residual subledger is scoped by route/source-holder/recipient. It is an exact fractional claim record, not a fractional integer-GL posting or proof of legal/economic backing.

### Invariant and explicit limits

The verified machine preserves holder/supply reconciliation, mapped holder/GL agreement, aggregate signed GL totals per asset, and the scaled source/target/residual equation. The transition remains an abstract model: replay/idempotency, nonce/expiry, bridge settlement/finality, custody, rollback, asset-collision handling, production residual-liability posting, valuation, and external backing remain open.

### Verification sequence

```bash
lake build SIRM.AuthorizedAssetMigration
lake build SIRM
lake test
python3 scripts/ci_audit.py all
git diff --check
```

Do not commit until the target module, full `SIRM` build, theorem-level test driver, all 17 static audits, and diff checks pass. Inspect the complete staged diff before one commit, one push, and one PR against `main`.


## Work block: per-principal nonce guard for authorized migration replay

### Verified starting point

- Repository: `RFT-SIRM/SIRM-Financial-Infrastructure`.
- Working branch: `foundation/transaction-replay-guard-2026-11-10`.
- Exact `main` base: `f6740483006d45bfc82b04fd441f49aac1865e52`.
- The branch also contains the session handoff guide introduced from that exact base; before this source patch its head was `69b65f0aa92b14aad376a50ef04cb23b8915340e`.

### Objective and selected model

- Preserve `SIRM.AuthorizedAssetMigration` unchanged and compose it through a separate replay-protected state machine.
- Extend the state with `nextNonce : Principal → Nat`; every principal starts at zero and has an independent sequence.
- A request carries an explicit nonce and is admitted only when it equals the current expected nonce for the same principal.
- The accepted transition computes the existing authorized atomic migration and increments that principal's expected nonce by one in the same returned state. All other principals' nonce values remain unchanged.
- Prove exact advancement, non-interference for other principals, rejection of any mismatching nonce, and reachable preservation of the existing financial/residual invariant.

### Explicit limits

This is a migration-specific abstract nonce gate. It is not a global nonce across all protocol operations, transaction hash/idempotent response cache, signature validation, expiry, canonical bytes, persistent storage, concurrent execution protocol, or production runtime commit guarantee. Lean `Nat` is unbounded; no production nonce width is selected.

### Verification gate

```bash
lake build SIRM.ReplayProtectedAssetMigration
lake build SIRM
lake test
python3 scripts/ci_audit.py all
git diff --check
```

Do not commit until the new module, umbrella library, theorem regression suite, all 17 static audits, and complete diff review pass. Then use one commit, one non-force push, one PR, and merge only after all 18 checks pass for the exact PR head. Exact commit/PR/merge SHAs and CI results are to be added to the next verified handoff entry.


## Public roadmap, project narrative and visual README overview

- Verified starting `main`: `8588b61401b6eae02510fc5f9772acf47e0dd3e5`, after PR #11 squash merge.
- PR #11 feature head: `4e95e912898e310d927afcae0de507181eb7dd65`; all 18 CI checks succeeded (one Lean job and 17 static audits).
- This documentation block adds an English author statement and a repository-local SVG overview of the eight formalized financial layers.
- Roadmap and scope text distinguish completed Lean properties from open accounting semantics, global transaction idempotency, Rust refinement, RFT Network, institutional and production gates.
- No Lean definitions or theorem statements are changed. No production deployment, custody, reserves, legal status or Rust implementation is claimed.
- Verify exact PR head and all 18 checks before merge.


## Historical handoff: initial single-use escrow accounting preparation (superseded)

The earlier preparation note below described only the first single-record escrow primitive and predates the subsequently merged registry, pooled-reserve, financial-integration and time-lock layers. It is retained as historical context only; it is not the current escrow status. The verified progression is recorded in the current dispute-intake work block below and in PRs #16, #17 and #23.

- Initial preparation base: `ba5ed00248b21921ac50b2c1e925a5fbd54bb0c7`.
- Initial branch label: `foundation/escrow-accounting-2026-11-12`.
- The original single-record assumptions remain the scope of `SIRM.EscrowAccounting` only; they must not be applied to the later composed escrow model.

## Work block: first-stage escrow dispute intake/freeze (merged in PR #24)

### Verified baseline and preceding escrow layers

- Repository: `RFT-SIRM/SIRM-Financial-Infrastructure`.
- Exact starting `main` SHA: `998bec99364832c0273d8680993f453b44c3dbb9`.
- The escrow foundation was merged in sequence: PR #16 (`5755c728b551a2838f505c6a9f9eaf6c1d19b03c`) added concurrent IDs and pooled reserve; PR #17 (`ed928ecdc34e2740ea87a55925fad8ab8386ddb2`) connected the reserve to `FinancialState` and the mapped GL; PR #23 (`998bec99364832c0273d8680993f453b44c3dbb9`) added discrete deadlines and permissioned expiry. PR #23 passed all 18 CI jobs for its exact head.
- Feature branch: `feat/escrow-dispute-freeze-2026-11-12`, based on the exact `main` SHA above. Feature commit `bb9ea4721e25bbfc9784c0643505abfb7876483c` contains exactly the 13 task files; its parent is the stated `main` SHA. The branch was pushed without force, and the remote branch SHA was verified equal to this commit. It was merged as PR #24 (`5bb3fd4f4d58436debce6abfab4c87df132632c8`); all 18 checks passed on the post-merge commit.

### Objective and selected semantics

Add stage-1 dispute intake as a safety freeze layered over `EscrowTimeLocks`:

- A separate dispute policy witness authorizes the principal/claimant/request context; the claimant must be the recorded depositor or beneficiary.
- Filing is permitted only for an existing pending ID, before its deadline, and only if that ID has no earlier filing.
- The filing stores principal, claimant and discrete filing time. It does not transfer funds or change the timed financial state.
- A filed ID cannot be released, voluntarily cancelled, or expired, including after its deadline. The discrete clock can still advance; other escrow IDs remain independently operable.
- Reachable states retain the established timed holder/supply, vault-balance, pending-pool and mapped-GL invariant.

### Explicit non-goals

No evidence authenticity/provenance validation, adjudication, winner selection, beneficiary/refund settlement, appeals, reversal, external delivery or settlement finality, wall-clock oracle, automatic scheduler liveness, persistence, production transaction idempotency, or Lean-to-Rust refinement is claimed. The stage-1 filing is a permanent freeze marker; a later layer must define its only authorized resolution semantics.

### Changed source and documentation paths in the current local patch

- `SIRM/EscrowDisputes.lean` (new) and `SIRM.lean`.
- `SIRMTests.lean` (integrated regression scenarios).
- `scripts/ci_audit.py` (dispute declarations and regression assertions in the existing 17-check audit set).
- `README.md`, `docs/FORMALIZATION_STATUS.md`, `docs/MATHEMATICAL_SCOPE.md`, `docs/ROADMAP.md`, `docs/TESTING.md`, and `docs/SECURITY_MODEL.md`.

The handoff/documentation reconciliation also updates `docs/DECISIONS.md`, this journal, and `docs/SESSION_WORKFLOW.md` in the same reviewed change set.

### Local verification reported for the source patch

The exact existing worktree completed the following commands successfully:

```bash
lake build SIRM.EscrowDisputes
lake build SIRMTests
lake build SIRM
lake test
python3 scripts/ci_audit.py all
git diff --check
```

- `SIRMTests` built successfully (8734 jobs).
- The static audit reported `STATIC_AUDITS_PASSED=17`.
- The command block reached `ALL_REQUIRED_LOCAL_CHECKS_PASSED`; `git diff --check` was clean.
- Remaining messages were Lean linter warnings only; no Lean errors were reported.

### Debugging facts to retain

- The first failing test output contained parser errors in two nested `some { ... }` record literals. Fixing those record layouts exposed the next, independent goal: the claimant-policy disjunction. The actual proof repair unfolds `integratedPendingEscrowRecord` alongside `integratedEscrowDisputeDemoPolicy` in the `simp` call. Do not revive the earlier guessed comma/record-field repair scripts.
- No theorem statement was weakened and no `sorry`/`admit` was introduced; `no-proof-holes` passed.

### Outcome

PR #24 was merged into `main` at `5bb3fd4f4d58436debce6abfab4c87df132632c8` with all 18 checks green (one Lean build/theorem-test job and 17 static audits). Open follow-ups are unchanged: dispute adjudication, evidence validation/provenance, outcome-specific settlement, appeals, and wall-clock/scheduler binding.

## Work block: canonical request encoding v0 and Rust reference codec (merged, PRs #25–#31)

- Starting point: `main` at `5bb3fd4f4d58436debce6abfab4c87df132632c8` (PR #24). End point: `85f69841b13d9ff62604685e158449904f15c3eb` (PR #31).
- Docs/lint: PR #25 synchronized roadmap, workflow and journal with PR #24 and replaced an obsolete branch/base audit assertion with a merged-baseline assertion. PR #26 prefixed six unused binders with an underscore (no logic change).
- Encoding: PR #27 added `scripts/canonical_encoding_reference.py`, `engineering/canonical_encoding/SPEC_v0.md` and vectors; the checks cover 5 boundary vectors, 2268 exhaustive small-domain requests, malformed-input rejection, out-of-range rejection and byte-identical reruns.
- Lean: PR #28 added `SIRM.CanonicalEncoding` (value recovery, length, digit bound, injectivity on `[0, 256^n)`); PR #29 added `SIRM.CanonicalRequestEncoding` (`decode_encode`, `encodeRequest_injective` for in-range requests). The first build attempts failed on a nonexistent Mathlib import (`Mathlib.Data.Nat.Defs`, replaced by `import Mathlib`), on a `v % 1` base case (closed with `Nat.mod_one`), and on a final field that lacked a trailing list (added `takeNum_beDigits`). No theorem was weakened and no `sorry`/`admit` was introduced.
- Rust: PR #31 added `rust/sirm-codec` with three conformance tests (vectors and SHA-256 against the Python reference, malformed-input rejection, 2268-case round trip and injectivity). Not part of CI.
- Open (the first item was closed by PR #44, see the Rust ports block): inverse direction on arbitrary digit lists; response/receipt encoding; chain id, signatures, expiry and state commitments; running the Rust tests in CI (this requires changing the one-workflow, 17-audit CI topology assertion deliberately).

## Work block: Rust ports and CI (merged, PRs #33–#42)

- Starting point: `main` after PR #31. Each port follows one pattern: read the Lean module, write an independent Python reference with seeded traces and committed JSON, write the Rust port, compare outcomes and final state operation by operation, and check that every rejected operation leaves the state unchanged.
- PR #33 envelope idempotency policy; PR #34 supply and holdings ledger core; PR #35 static authorization and account control; PR #36 integrated processor (replay vs conflict, stale/future nonce, cached denials, atomic commit; 4000-request trace); PR #37 the `Rust` CI job (fmt, clippy, tests) and a topology-audit assertion that requires those commands, with the static matrix unchanged at 17 and a single workflow file; PR #38 fee accounting (4000 operations); PR #39 single-use escrow (1500 episodes); PR #40 pooled time-locked escrow (1500 episodes); PR #41 first-stage dispute freeze (1500 episodes, 292 filings, 439 freeze rejections); PR #42 asset migration (1505 episodes including five hand-built `u128` boundary episodes).
- CI per pull request is now 19 checks: one Lean job, one Rust job and 17 static audits.
- Findings from the differential runs: a fee-transfer test assumed credit overflow was reachable, but holdings never exceed minted supply, so the checked arithmetic there is defence in depth; the dispute port and reference disagreed on the order of two rejection reasons (frozen vs ID in use), both conditions being mandatory in Lean, and the reference was aligned to the Rust order. No Lean theorem was changed.
- Rust-side extensions over Lean (documented in each module): checked `u128` instead of unbounded `Nat`; IDs outside the deadline schedule rejected as unknown; policies, registries and network-distinctness proofs live outside the ports.
- Open: the typed registry and the registry-aware issuance gate were ported afterwards (see the next block); the network-distinctness proofs of migration are not ported; the concrete principal/holder/asset numbering for `CanonicalRequestLink` and its range bounds are not constructed; Lean-to-Rust refinement is not claimed; no production runtime, persistence or network claim follows from these tests.
- PR #43 synchronized README, ROADMAP, TESTING, FORMALIZATION_STATUS and this journal with the Rust ports. PR #44 added `SIRM.CanonicalRequestLink` (`toFtxOp_injective`, `toFtx_injective`, `encodeRequest_toFtx_injective`): the first draft required range validity for every possible request, which is unsatisfiable for unbounded nonces and amounts, so the final theorem requires it only for the two compared requests. Built by the user (`lake build SIRM.CanonicalRequestLink` first try, full `lake build`, `lake test`, 17 static audits) and merged with 19 green checks. A new git worktree has no Mathlib build products: run `lake exe cache get` after `git worktree add`, otherwise `lake build` recompiles Mathlib for hours.

## Work block: typed registry and issuance gate in Rust

- `rust/sirm-codec/src/registry.rs` ports `SIRM.TypedRegistry` (total account/asset metadata, issuer on the asset's network, `issuance_enabled` = active asset and active issuer account, `10^decimals` with checked `u128`) and the issuance gate of `SIRM.RegistryAwareFinancialMachine` (`GatedPolicy`: issue needs the base policy and eligibility; transfer and burn keep exactly the base predicates, so frozen accounts and non-active assets do not restrict them in this layer). `AuthorityRegistry` and `AccountControl` were already ported in `auth.rs` (PR #35).
- Check: `scripts/registry_gate_reference_trace.py` (independent Python reference) produces 24 random typed registries with 500 operations each (3937 accepted, 4520 base-policy denials, 1957 gate-only denials, 1586 insufficient-funds); the Rust test replays them and compares outcomes, final balances and the enabled flag of every asset.
- Not ported: the Lean proof-carrying `VerifiedStateMachine` structure and migration route checks that need the network-distinctness proofs.

## Work block: property and fuzz tests of the integrated processor

- `rust/sirm-codec/tests/machine_property.rs`: 200 seeded runs of 400 requests each (80,000 total; 3,555 accepted, 46,053 cached denials, 8,985 replays, 6,100 same-ID conflicts, 5,469 stale and 9,676 future nonces, 162 invalid) against random grant/control policies. After every request: holdings invariant and per-asset conservation; an accepted request advances only the acting principal's nonce by one and adds one cache entry; a cached denial changes neither ledger nor nonces; replay, conflict, stale, future and invalid requests leave the whole processor equal to its previous state; a replay returns exactly the first stored response; accepted nonces are consecutive per principal; replaying the whole log into a fresh processor reproduces the processor exactly. No property failed. The first coverage threshold for `invalid` was set too high and was lowered, since range failures are rare by construction.
- Limits: fixed-seed pseudo-random generation without external crates, not coverage-guided fuzzing; the oracle is the set of properties, not the Lean model (that comparison is the differential trace test).

## Work block: receipt encoding v0 (protocol item 1, proposal)

- Added `engineering/canonical_encoding/SPEC_receipt_v0.md`, `scripts/canonical_receipt_reference.py`, `results/receipt_vectors_v0.json` and `rust/sirm-codec/src/receipt.rs` with `tests/receipt_conformance.rs`. Decisions (each recorded in the specification): the receipt embeds the full canonical request encoding; only responses that Lean stores are encoded (success, authorization denial, insufficient-funds denial); no state hash, signature or chain id in v0 (they are the next two protocol items and would be new versions with their own domain tags); the decoder rejects every receipt that violates the Lean construction (accepted nonce = request nonce, next = accepted + 1, expected nonce = request nonce for denials, reason matches the operation family).
- Evidence: 11 vectors, 4374 receipts exhaustively on a small domain (distinct, exact round trip, exact lengths), 12 malformed-input rejections, 7 encoder rejections, and in Rust a link to the integrated processor (every stored response encodes and decodes back; an exact retry is byte-identical). Not claimed: any Lean theorem, adoption, authentication.
- Open: protocol item 2 (signatures, chain id) and item 3 (state commitments).

## Work block: signed request layer v0 (protocol item 2, proposal)

- Added `engineering/canonical_encoding/SPEC_signed_request_v0.md`, `scripts/signed_request_reference.py`, `results/signed_request_vectors_v0.json`, `rust/sirm-codec/src/signed.rs` and `tests/signed_conformance.rs`. Design: chain id u64 inside the signed bytes, separate signing/wire domains, Ed25519 over the signing message, key looked up by principal, strict verification, rejected messages never reach the processor.
- New dependency: `ed25519-dalek` 2 (default features off, `std`); `Cargo.lock` grew accordingly and deserves review.
- Evidence: RFC 8032 vector 1, 8 vectors with byte-identical signatures from OpenSSL and ed25519-dalek, every single-byte mutation rejected, 9 structured negatives, node pipeline test. Not claimed: Lean theorem, adoption, key management.
- Closed by the next block: protocol item 3.

## Work block: state commitment v0 (protocol item 3, proposal)

- Added `engineering/canonical_encoding/SPEC_state_commitment_v0.md`, `scripts/state_commitment_reference.py`, `results/state_commitment_vectors_v0.json`, `rust/sirm-codec/src/commit.rs` and `tests/commit_conformance.rs`. Decision: depth-64 sparse Merkle tree (SHA-256) over balances, supply and nonces, combined with the dimensions into a state root; inclusion and absence proofs. The response cache and the policy, fee, escrow, dispute, migration and registry state are not committed.
- Evidence: two independent Python algorithms agree, proofs verify and tampering fails, Rust matches the vectors and the root of the replayed 4000-request processor trace; accepted requests move the root, rejections and replays do not. Not claimed: Lean theorem, adoption, whole-system coverage.
- Open: adoption of the three v0 proposals as a protocol, key management, expiry, commitments for the remaining modules, Lean statements for the receipt, signature and commitment layers.

## Work block: Rust port of the key lifecycle models (phase P2/P3)

- Added `rust/sirm-codec/src/keys.rs`, `tests/keys_trace.rs`, `scripts/key_registry_reference.py` and `engineering/ledger_core/results/key_registry_trace_v0.json`. The Rust registry ports `SIRM/KeyRegistry.lean`, `SIRM/RecoveryDelay.lean` and `SIRM/ThresholdAuth.lean` (register, rotate, freeze, revoke, recover, initiate, cancel, finalize, k-of-n acceptance over a plain signature list). One explicit difference from the Lean per-account `DelayState`: the registry holds all accounts, so initiate, cancel and finalize on a missing account fail with `unknownAccount` first.
- Evidence: an independent Python reference with three seeded traces (3,600 operations) and 1,500 threshold cases; Rust matches every per-operation outcome and the final state, rejected operations leave state unchanged, and the legacy-key invariant holds after every step. A deliberate mutation (removing the downgrade check) is caught by the test. All 12 outcome classes occur.
- This is differential evidence, not a refinement proof. The actor is the outcome of an earlier signature check, the clock is a caller-supplied value, and no signature scheme is involved.

## Work block: state commitment v1 (phase P4 start, proposal)

- Added `engineering/canonical_encoding/SPEC_state_commitment_v1.md`, `scripts/state_commitment_v1_reference.py`, `results/state_commitment_v1_vectors.json`, `rust/sirm-codec/src/commit_v1.rs`, `tests/commit_v1_conformance.rs` and a shared replay helper `tests/support/machine_replay.rs`. v1 keeps the three v0 roots and adds a key registry tree, a suite registry tree and a protocol header (chain id, version, hash suite). v0 is untouched.
- Evidence: Python and Rust agree on value encodings, registry roots and the full root over the replayed 4000-request processor trace; 18 single-field changes each move the root.
- Still partial, and documented as such: receipts and the cache, account and asset registries, grants, fees, governance, escrow, time-lock, dispute, migration and threshold policies are not covered. No Lean statements.

## Work block: Lean authenticated step (phase P3 groundwork)

- Added `SIRM/AuthenticatedStep.lean`: a generic wrapper `authStep` that authenticates a request with `SIRM.SignatureSuite` and only then runs an arbitrary state machine. Proved: a request whose authorization is not accepted leaves the state unchanged (no nonce, no cache entry); a processed request was accepted under its principal's registered suite; frozen or revoked accounts never reach the machine; any invariant the machine preserves is preserved by the wrapper. Three concrete examples with a toy counter.
- The wrapper is deliberately generic, so it has not yet been instantiated with the real integrated processor (`SIRM.ReplayProtectedFinancialMachine`), which needs Mathlib and is built only in CI. Assumed, not proved: the signed message determines the request, and signature unforgeability.
- Checked with Lean 4.33.1 in the sandbox (core Lean); standard axioms only.

## Work block: Lean threshold authorization and delayed recovery (phase P2)

- Added `SIRM/ThresholdAuth.lean` and `SIRM/RecoveryDelay.lean`. Threshold: a plain list of `(index, signature)` pairs, no aggregation assumed; accepted only when at least `k` distinct registered indices have a verified signature of a permitted suite; `k = 0` never accepts; duplicates never count twice; a lower threshold is easier. Delayed recovery: a recovery is announced by the recovery actor, can be cancelled only by the current key, finalizes only after the delay, and the key change is exactly the `recover` transition of `SIRM.KeyRegistry`, so the legacy-key rule (`finalize_preserves_pqSound`) carries over.
- Checked with Lean 4.33.1 in the sandbox (core Lean, no Mathlib); theorems depend only on the standard Lean axioms (`propext`, `Quot.sound`, and `Classical.choice` for two threshold theorems), no custom axioms and no `sorry`. Nine concrete examples. The full `lake build` runs in CI.
- Not modelled: the clock (monotonicity of `now` is an assumption of the protocol), several pending recoveries, threshold policy changes, linking to the processor and to the committed state.

## Work block: Lean key registry transitions (phase P2)

- Added `SIRM/KeyRegistry.lean` (imports `SIRM.SignatureSuite` only). A state machine for register, rotate, freeze, revoke and recover with an `Actor` (current key or recovery key) that is the outcome of an earlier signature check. Proved: only the target principal's entry changes; the legacy-key rule (no successful transition replaces the post-quantum key of a bound account by a non-post-quantum key, as the invariant `PqSound`); a frozen account cannot rotate; recovery and revocation need the recovery actor and a registered recovery credential; frozen or revoked accounts are not authorized by the signature check of `SIRM.SignatureSuite`; key transitions never change the financial state (frame property for any invariant) and a rejected command changes nothing. Four concrete examples.
- Checked with Lean 4.33.1 in the sandbox (core Lean, no Mathlib); theorems depend only on `propext` and `Quot.sound`. The full `lake build` runs in CI.
- Not modelled: who may register, expiry, thresholds, challenge delays, hash commitment to a successor key, linking to the processor and to the committed state.

## Work block: Lean signature-suite model (phase P1)

- Added `SIRM/SignatureSuite.lean` (imports nothing but core Lean). An abstract model of the v1 authorization step: suite identifiers, key records that carry the suite, a node policy, a total `authorize` function with explicit rejection reasons, and a hybrid verifier as a conjunction. Proved: acceptance characterization, an accepted authorization uses the registered suite (no downgrade or substitution), only policy-permitted suites authorize, proposed and disabled suites never authorize, deprecated suites need an opt-in, acceptance implies the abstract verifier accepted, unregistered principals are rejected, a hybrid needs both components. Four concrete regression examples.
- Checked with Lean 4.33.1 (core only, no Mathlib import) in the sandbox; theorems depend only on `propext` and `Quot.sound`. The full `lake build` runs in CI. Not proved and not assumed as axioms: unforgeability of any real scheme.
- Not covered yet: key registry transitions, threshold authorization, atomic migration of keys, linkage to the processor's principal.

## Work block: signed request layer v1 (phase P1, proposal)

- Added `engineering/canonical_encoding/SPEC_signed_request_v1.md`, `scripts/signed_request_v1_reference.py` and `results/signed_request_v1_vectors.json`. Suite registry, suite id and key id inside the signed bytes, ML-DSA-65 and a hybrid Ed25519+ML-DSA-65 suite, downgrade and substitution rejected because the suite comes from the registered key. v0 is untouched.
- Evidence: 10 valid and 18 negative vectors, 13,792 single-byte mutations rejected. ML-DSA signatures from OpenSSL are randomized, so the vector file is frozen and checked rather than regenerated. Not claimed: Rust or Lean agreement, second ML-DSA implementation, adoption.
- Open: Lean abstract verification model, Rust port after the library choice, key registry transitions.

## Work block: post-quantum security architecture (proposal)

- Added `docs/POST_QUANTUM_SECURITY_ARCHITECTURE.md` and `docs/PQ_DECISIONS_PROPOSED.md`. Documents only: no Lean or Rust change, nothing adopted. Standards were checked against csrc.nist.gov on 2026-11-15 (FIPS 203/204/205 final, SP 800-227 final, IR 8547 final in October 2026, CSWP 39 final; FIPS 206 status not verified).
- Findings recorded: the v0 signed request and state commitment are proposals, Ed25519 is quantum-vulnerable, the v0 state root is partial, and no audited Rust post-quantum implementation was known in a 2025 survey (to re-verify).
- Open: independent review of the proposal, then the phased plan P1 to P5 in the architecture document.

- Added `docs/PQ_RUST_LIBRARY_EVALUATION.md` and PQ-13. A throwaway crate (not committed) checked that RustCrypto `ml-dsa` 0.1.2 and `aws-lc-rs` 1.19.0 accept the 8 frozen ML-DSA-65 signatures of the v1 vectors and reject 473 single-byte mutations. Verification only, one platform, not an audit; no dependency added, no library chosen.

- Extended `docs/PQ_RUST_LIBRARY_EVALUATION.md` with a duplicate-hint (CVE-2026-24850 class) check: `ml-dsa` 0.1.2 and `aws-lc-rs` 1.19.0 reject 4 of 4 constructed signatures, the known-vulnerable `ml-dsa` 0.1.0-rc.3 accepts all 4. One malformed-encoding construction, not a full negative suite. Documents only.

- Added `docs/LICENSE_SPLIT_PROPOSAL.md` and `docs/TRADEMARK_AND_NAMING_POLICY.md`: proposals only. `LICENSE` unchanged (Apache-2.0); a future production implementation would be a separate repository under BUSL-1.1 with the parameters and gates stated there; no legal review yet.

- Added `engineering/canonical_encoding/SPEC_state_commitment_v2.md`, `scripts/state_commitment_v2_reference.py`, `results/state_commitment_v2_vectors.json`, `rust/sirm-codec/src/commit_v2.rs` and `tests/commit_v2_conformance.rs`. v2 keeps v1 and adds the request-id cache, the authorization policy (grants, control) and the account/asset registry as ordered list hashes (no inclusion proofs for them). Added read accessors `Processor::policy/cache_entries`, `Policy::grants/control_pairs`, `Registry::accounts/assets`. Still partial: escrow, time-lock, dispute, migration, fees and governance state are not covered. Differential evidence only; not adopted.

- Added `engineering/canonical_encoding/SPEC_state_commitment_v3.md`, `scripts/state_commitment_v3_reference.py`, `results/state_commitment_v3_vectors.json`, `rust/sirm-codec/src/commit_v3.rs` and `tests/commit_v3_conformance.rs`. v3 keeps v2 and adds the escrow / time-lock / dispute component (deadline schedule, records, filings, clock, vault, and the escrow machine's own balance and supply roots). Added `TimeLockedEscrow::vault/ids`. 1500 per-episode commitments are byte-identical between Python and Rust. Still partial: migration, fees, governance, thresholds. Differential evidence only; not adopted.

- Added `engineering/canonical_encoding/SPEC_state_commitment_v4.md`, `scripts/state_commitment_v4_reference.py`, `results/state_commitment_v4_vectors.json`, `rust/sirm-codec/src/commit_v4.rs` and `tests/commit_v4_conformance.rs`. v4 keeps v3 and adds the asset-migration component (rate, holder, recipient, totals, dust, nonces, own balance/supply roots). Added read accessors on `Migration`. 1505 per-episode commitments are byte-identical between Python and Rust. Found that fees have no persistent state and that no governance module exists, so those are recorded as nothing to commit rather than as a gap. Differential evidence only; not adopted.

- Added `docs/INTEGRATED_STATE_MACHINE_PROPOSAL.md` (proposal only): one shared ledger and one request pipeline, deny-by-default grants for the new operations, invariants, and steps I1 to I5. No code or encoding changed.

- Added `scripts/integrated_machine_reference.py` and `engineering/ledger_core/results/integrated_trace_v0.json` (step I1 of the integrated state machine proposal). One shared ledger and one request pipeline for ten operations; deny-by-default grants for the new ones; reserved vault account. Reproduces the old processor trace exactly; invariants checked at every step; 402 episodes. Python only; the next step (I2) is the Rust port with a differential test.

- Added `rust/sirm-codec/src/integrated.rs` and `tests/integrated_trace.rs` (step I2): Rust port of the integrated state machine, byte-identical outcomes and final states on 402 reference episodes and on the old processor trace. The comparison found two reference defects, fixed in `scripts/integrated_machine_reference.py` (an ambiguous denial code, and replays with an extra argument), and the trace was regenerated; migration rates are now written as strings because they can exceed 2^53.
- Added request encoding v1 (step I3): `scripts/request_v1_reference.py`, `engineering/canonical_encoding/SPEC_request_v1.md`, `results/request_v1_vectors.json`, `rust/sirm-codec/src/request_v1.rs`, `tests/request_v1_conformance.rs`. Request ids in the Rust integrated machine are now 32 bytes; shared test helpers moved to `tests/support/integrated_load.rs`. Signed requests still carry v0 only.
- Added state commitment v5 (step I4) for the integrated machine: `scripts/state_commitment_v5_reference.py`, `SPEC_state_commitment_v5.md`, `results/state_commitment_v5_vectors.json`, `rust/sirm-codec/src/commit_v5.rs`, `tests/commit_v5_conformance.rs`; read-only accessors on `integrated::Machine`.
- Added `SIRM/IntegratedPipeline.lean` (step I5, partial): generic Lean model of the integrated request pipeline with 16 theorems; no Mathlib, compiled locally with Lean 4.33.1 before the commit. Added to `SIRM.lean`.
- Added signed request v2 (carries request encoding v1): `scripts/signed_request_v2_reference.py`, `SPEC_signed_request_v2.md`, frozen `results/signed_request_v2_vectors.json`, `rust/sirm-codec/src/signed_v2.rs` and `tests/signed_v2_conformance.rs`. Rust verifies Ed25519 only; ML-DSA and hybrid are refused (`VerifierUnavailable`) until a verifier library is chosen.
- Added `SIRM/IntegratedLedger.lean` (step I5, concrete slice): shared-ledger core with transfer, issue, burn, escrow open, release, cancel, expire; conservation and vault-backing invariants proved over the pipeline (25 theorems, no Mathlib, compiled locally with Lean 4.33.1 before the commit). Added to `SIRM.lean`.
- Extended `SIRM/IntegratedLedger.lean` with the asset migration: `migrateEff` (burn, issue, carried remainder), the migration equation in the invariant, `inv_migrate` built on the proved burn and issue (28 theorems, no Mathlib, only `propext` and `Quot.sound`, compiled locally with Lean 4.33.1).
- Extended `SIRM/IntegratedLedger.lean` with the clock, deadlines and dispute filings (`dispute`, `advance`): invariant `filesOk` (a filing belongs to a pending record, claimant is a party), `pipeline_now_monotone`, `pipeline_files_stable` (38 theorems, no Mathlib, only `propext` and `Quot.sound`, compiled locally with Lean 4.33.1). All ten operations of the integrated machine are now in the Lean model.
- Authorization in Lean (`SIRM/IntegratedLedger.lean`): `Op.issue` now names an issuer; `Policy` and `authorizedOp` mirror the Rust `authorized`; theorems `empty_policy_changes_nothing`, `no_debit_without_control`, `time_only_by_clock`, `filing_only_by_grant`, `mint_only_by_grant` via `pipeline_rel_p` (52 theorems, only `propext` and `Quot.sound`, no Mathlib). The policy is a model, not connected to the Rust code.
- Added `SIRM/BoundedAmounts.lean` (step I5, bounded amounts): the `u128` ceiling as a parameter and one extra validation step (`boundVal`, `fitsB`, `overflowDenial`); proved that invariants plus bounds on supply counters, migration totals and remainder hold in every reachable state, that balances and burned totals are bounded through conservation, and that a request that does not fit leaves the core unchanged (13 theorems, no Mathlib, only `propext` and `Quot.sound`, compiled locally with Lean 4.33.1). Proposal level; no refinement proof for the Rust code.
- Added `rust/sirm-codec/tests/integrated_ceiling.rs`: differential check of the `u128` ceiling against the Lean predicate `fitsB` on 400 seeded runs; fixed `Machine::invariant()` to evaluate the migration equation in exact 256-bit arithmetic (it returned false on valid states with products above `u128`; test-only). Differential evidence, not a refinement proof.
- Added `SIRM/DisputeResolution.lean`: a minimal arbiter resolution of a frozen dispute as a separate Lean layer (13 theorems, no Mathlib, only `propext` and `Quot.sound`, compiled locally with Lean 4.33.1): invariants and bounds preserved, payout exactly the escrowed amount, no resolution without the grant, without a filing, or twice. Not wired into the pipeline, wire formats or the Rust and Python machines; arbiter identity, evidence, deadlines and appeals remain open. Proposal level.
- Added `docs/STATUS_AT_A_GLANCE.md`, a one-page reader's guide (what is proved, what is only tested, what is open, how to check), linked from the README; README sentence on `Nat` versus `u128` updated for `SIRM.BoundedAmounts` and `integrated_ceiling.rs`.
- Added `docs/REVIEWER_GUIDE.md`: scope, reading order, the questions most wanted answered and what each kind of evidence means, for an independent reviewer; states plainly that no independent review exists and that most of the repository was written with AI assistance. Linked from `docs/STATUS_AT_A_GLANCE.md`.
- Added the arbiter operation `resolve` to the Rust integrated machine and the Python reference with its own 300-episode trace and a Rust differential test (`integrated_resolve_trace.rs`); the base trace stays byte-identical; no wire encoding yet (`UnsupportedOperation`, `state_root_v5` is `None` after a cached resolve); not yet in the Lean pipeline. Proposal level.
- Wired `resolve` into the Lean pipeline as the eleventh operation (`Op.resolve`, `Kind.resolve`, `pre`, `applyOp` = filing consumed then `settle`, `authorizedOp` with `pol.ids p .resolve id`). All earlier theorems re-proved (`inv_applyOp`, clock monotonicity, `bal_ge_step`, `time_only_by_clock`, `filing_only_by_grant`, `mint_only_by_grant`, `bounded_applyOp`); `files_stable_applyOp` and `pipeline_files_stable` now exclude a resolve of the same escrow; new `filing_removed_only_by_resolve_grant`; a demo scenario (dispute then resolve) was added. `SIRM.DisputeResolution` now reuses `resolveEff` and `inv_resolveEff` from the ledger (11 theorems). `IntegratedLedger` has 56 theorems (62 after the later self-transfer fix); only `propext` and `Quot.sound`; compiled locally with Lean 4.33.1. Still open: wire encoding of `resolve`, commitment, arbiter identity and process. Proposal level.
- Added request encoding v2 (`SPEC_request_v2.md`, `scripts/request_v2_reference.py`, `rust/sirm-codec/src/request_v2.rs`, `tests/request_v2_conformance.rs`, `results/request_v2_vectors.json`): v1 plus `resolve` as tag 10 (escrow id u32, one flag byte, 0 or 1 only; 62 bytes); tags 0 to 9 differ from v1 only in the domain `SIRM/FTX/v2\0`; v1 and its frozen vectors are untouched. The Python reference checks 19 vectors, 5463 round trips, 1374 single-byte mutations, 254 non-canonical flags and both traces; the Rust codec reproduces the vector bytes and both aggregate digests and replays both traces through bytes -> decode -> machine. Still open: signed request carrying v2, state commitment covering resolve. Differential evidence, proposal level.
- Added signed request layer v3 (`SPEC_signed_request_v3.md`, `scripts/signed_request_v3_reference.py`, `rust/sirm-codec/src/signed_v3.rs`, `tests/signed_v3_conformance.rs`, frozen `results/signed_request_v3_vectors.json`): the v2 suite registry carrying request encoding v2 with domains `SIRM/SIG/v3\0` and `SIRM/SRQ/v3\0`. Python: 26 valid vectors, 32 negative cases (including a correctly signed resolve with a non-canonical flag), 14,358 single-byte mutations rejected; Rust: Ed25519 signatures reproduced byte for byte, all negative cases, mutations, and an end-to-end node in which a signed resolve settles a dispute and a repeated or ungranted resolve is denied. No post-quantum verifier in Rust (unchanged). Still open: state commitment covering resolve. Differential evidence, proposal level.
- Added state commitment v6 (`SPEC_state_commitment_v6.md`, `scripts/state_commitment_v6_reference.py`, `rust/sirm-codec/src/commit_v6.rs`, `tests/commit_v6_conformance.rs`, `results/state_commitment_v6_vectors.json`): v5 with new domains, cache entries in request encoding v2 (so a cached resolve request is committed) and cause code 15 in use; v5 and its vectors are untouched. Python regenerates the 402 base episodes and the 300 resolve-trace episodes from their seeds, checks them against the committed traces and commits their final states; Rust replays both families and all 702 roots, both aggregate digests and the components of both examples agree. Every accepted or denied resolve request changes the root; a denied one changes only the cache. With request v2, signed request v3 and commitment v6, the arbiter operation now has a wire format, a signature layer and a state commitment, all proposal level and differential evidence only. Still open: arbiter identity and process, a Lean counterpart of the wire layers, an independent review.
- Added `SIRM/RequestEncodingV2.lean` (17 theorems, only `propext` and `Quot.sound`, no Mathlib, compiled locally with Lean 4.33.1): one table from operation tag to field widths for the eleven operations of request encoding v2, with `decode_encode`, `encode_injective`, `encode_decode` (every accepted byte string is the canonical encoding of the request returned, which is valid, including the `resolve` side byte 0 or 1) and `decode_unknown_tag`; imported by `SIRM.lean`. The table is hand-written, so its agreement with the Rust and Python codecs remains differential evidence. Still open: Lean counterparts of the signature layer and the state commitment, arbiter identity and process, an independent review.
- Added `replay/ReplayTraces.lean`, an executable Lean replay of both committed Python traces (402 + 300 episodes, 52,953 requests) through the Lean pipeline (`process`, `policyAuth`, `pre`): per request the outcome class (replay, conflict, stale, future, accepted, denied), the authorization-denial reason and the final core state agree; a sound boolean `preB` implies `pre` (`preB_sound`). It runs in CI after the Lean build. The first run found a real gap between the model and the code: the Rust and Python machines accept a transfer from an account to itself as a no-op for any amount, while the Lean `pre` required the balance to cover it (247 accepted self-transfers failed). The Lean model was changed (`applyOp` leaves the core unchanged when `src = dst`; `pre` allows `src = dst`; six small `transfer_*` lemmas; all dependent proofs redone, no new axioms); the code was not changed and was already conservation-safe. After the fix the replay reports 0 mismatches. This is differential evidence over fixed traces, not a refinement proof.
- Status wording: the label "(proposal, not adopted)" in titles of specifications, reference scripts, Rust modules and Lean headers was replaced by "(checked by SIRM)": everything is checked by the project's own Lean proofs, Rust conformance tests, Python references and trace replay. The limits stay stated where they apply (no independent cryptographic review, differential evidence is not a refinement proof). Post-quantum decision documents keep their own status.
- Added `SIRM/SignedEnvelopeV3.lean` (11 theorems, only `propext` and `Quot.sound`, no Mathlib, compiled locally with Lean 4.33.1): the byte layout of the signed request wire v3 on top of `SIRM.RequestEncodingV2` (domain, chain u64, suite u16, request, suite-sized signature). Proved: decode inverts encode on valid envelopes, injectivity, every accepted wire is canonical and valid, other domains (the v2 wire domain and the signing-message domain) are rejected, and the signing message determines chain, suite, key id and the whole request. Not modelled: the signature check, the key registry, the verification order, the state commitment. The suite table is hand-written; agreement with Rust and Python stays differential evidence.
- Added `SIRM/StateCommitmentV6.lean` (10 theorems, only `propext` and `Quot.sound`, no Mathlib, compiled locally with Lean 4.33.1): what the v6 state root binds, with the hash abstract and collision freedom a hypothesis. Proved: the hashed payload determines domain and every component, so equal roots have equal components; v5 and v6 roots never coincide; a cache entry fixes the request (the escrow id and side of a cached `resolve`) and the stored outcome. Not modelled: the sparse trees and the config, cache and escrow digests as functions of a machine state, sorting, SHA-256. Agreement with Rust and Python stays differential evidence.
- Added `SIRM/CacheDigestV6.lean` (7 theorems, only `propext` and `Quot.sound`, no Mathlib, compiled locally with Lean 4.33.1): the cache digest of commitment v6 is unambiguous. A cache entry carries its own length (operation tag at byte 44 fixes the request width, outcome is 11 bytes), so concatenated entries determine the entry list, and under a collision-free hash the digest determines the cached requests and outcomes. Not modelled: sorting by request id, building the list from a machine state, SHA-256. Agreement with Rust and Python stays differential evidence.
- Added `SIRM/EscrowConfigDigestV6.lean` (26 theorems, only `propext` and `Quot.sound`, no Mathlib, compiled locally with Lean 4.33.1): the escrow digest and the config digest of commitment v6 determine what they cover. Generic lemmas for a u32 count followed by fixed-width entries and for flag-byte optional parts; `escrowDigest_binds` (deadlines, records, filings) and `configDigest_binds` (shape, vault, deadlines, migration rate, controls, limits, ids with the arbiter grants as tag 10, clock), both under a collision-free hash as a hypothesis. Together with `StateCommitmentV6` and `CacheDigestV6` the v6 root is bound, in the abstract, to the cache, escrow, config, shape, clock and migration totals. Not modelled: the sparse balance, supply and nonce trees, building the lists from a machine state, sorting, SHA-256.
- Added `SIRM/SparseTreeV0.lean` (10 theorems, only `propext` and `Quot.sound`, no Mathlib, compiled locally with Lean 4.33.1): the sparse Merkle tree of commitment v0 by recursion on the level, hash abstract with 32-byte outputs and collision freedom as a hypothesis. `root_binds_64`: entries with distinct keys below 2^64 and values shorter than 2^16 are determined, as a set, by the depth-64 root; `root_empty`: the empty list gives the empty-subtree hash. Together with the digest files, the v6 root is bound in the abstract to everything it covers except what keys and values mean for balances, supplies and nonces and how the lists are built from a machine state. Not modelled: inclusion proofs, the incremental Rust algorithm, SHA-256.
- Added `SIRM/LedgerRootsV0.lean` (12 theorems, only `propext` and `Quot.sound`, no Mathlib, compiled locally with Lean 4.33.1): the balance, supply and nonce roots determine the ledger they commit to. Entries are built from a function on a key list with the zero value skipped, as in the specification; `balances_determined`, `supplies_determined`, `nonces_determined` under a collision-free hash with 32-byte outputs and the value ranges of the ledger invariants. The list of keys uses an own `upto` instead of `List.range` because the library lemmas pull in classical choice. Together with the digest files and `SparseTreeV0`, the v6 root is bound in the abstract to the balances, supplies, nonces, config, cache, escrow table, clock and migration totals. Not modelled: that the Rust code enumerates exactly these keys, SHA-256, inclusion proofs.
- Added `SIRM/StateRootV6.lean` (3 theorems, only `propext` and `Quot.sound`, no Mathlib, compiled locally with Lean 4.33.1): the whole chain of the v6 commitment in one statement. `rootOf` builds the root of a snapshot from the sparse trees, the config, cache and escrow digests and the state payload as the specification says; `state_root_binds`: under a collision-free hash with 32-byte byte outputs (assumptions) and the value ranges of the ledger invariants, equal roots mean equal shape, clock, migration totals, balances, supplies, nonces, config (arbiter grants included), cache (cached `resolve` requests and outcomes included) and escrow table. Not modelled: that the code builds the lists from a machine state in this order, SHA-256, inclusion proofs. The hash assumptions are not proved; the agreement with Rust and Python stays differential evidence.
- Review of `main` at 084c1da by another AI system (commissioned by the author), checked against the sources. Confirmed and fixed: (1) `Machine::new` accepted a vault, a migration holder, recipient or asset outside the ledger; reproduced on `main`: a migration to a recipient outside the ledger passed the domain check and panicked in `apply` after the source units were burned (balance 10 -> 5, then a panic), and `Open` with a vault outside the ledger panicked in `apply`. The constructor now refuses such configurations; regression tests in `tests/integrated_config_validation.rs`. The Lean theorems already assumed `vault < accounts`; the code did not enforce it. (2) The Rust nonce counter did `expected + 1` on a `u64`, which wraps in release builds and panics in debug builds at `u64::MAX`; the counter now stops at the ceiling (the request with that nonce is answered stale and not cached; unit test), and `IntegratedPipeline.processCapped` with `processCapped_nonces_le` models this (the older `ReplayProtectedFinancialMachine` already stated that its nonces are unbounded). (3) `ThresholdAuth.accepts_implies_k_distinct` promised verified signatures but its conclusion did not say so; the conclusion now includes, for each counted index, the registered key, the permitted suite, the signature in the list and the successful verification. The counting is by index (the Python and Rust mirrors do the same, and the seeded traces contain duplicate keys), so one key registered twice counts twice: `duplicate_key_counts_twice` shows it, `KeysDistinct` and `accepts_implies_k_distinct_signers` state what holds on a policy with pairwise different keys, and Rust has `keys::keys_distinct`. The acceptance function itself is unchanged, so the frozen traces are unchanged. (4) The static audit `no-proof-holes` only matched lines that start with `sorry` and skipped `replay/`; it now finds whole-word `sorry` and `admit` anywhere in code (comments ignored) and covers `replay/`. (5) The Rust CI job now installs `cryptography`, runs all Python reference scripts and fails if any committed result under `engineering/` changes; run locally, all 29 scripts finish in about 35 seconds and reproduce the results unchanged. (6) The title of the integrated state machine document still said that nothing was implemented; corrected. Not changed: Lean lint is off in CI (no linter is configured), the Rust code is still not proved to refine the Lean model, there is still no independent cryptographic review. In the same review: balances, supplies and nonces roots, the signed envelope and the commitment chain were read as correct in the abstract and the remaining limits were already stated in the documents.
- Added `SIRM/SignedPipelineV3.lean` (6 theorems, only `propext` and `Quot.sound`, no Mathlib, compiled locally with Lean 4.33.1): wire bytes to the integrated pipeline in one statement. `wireStep` = decode, chain check, signing message from the registered key, `authStep`, then the machine; proved that processed wires are authenticated and canonical, that the signature binds chain, suite, key id and the request, that rejected wires leave the state untouched and that no nonce exceeds `2^64 - 1`. The verifier stays abstract. Also brought `scripts/integrated_machine_reference.py` to the fixed behaviour (config validation in the constructor, nonce ceiling answering `S` without caching, self-test); committed traces are unchanged.
- Threshold keys: `scripts/key_registry_reference.py` got `keys_distinct` (mirror of `keys::keys_distinct` and of `KeysDistinct` in `ThresholdAuth.lean`) and writes `keys_distinct` into each of the 1,500 threshold cases of `key_registry_trace_v0.json`; `rust/sirm-codec/tests/keys_trace.rs` checks that Rust agrees on every case. Decisions of `threshold_accepts` are unchanged. Differential evidence only.
- Refinement setup (not a proof): `rust/sirm-keys-core` (loop-only core of `keys_distinct` and `threshold_accepts`, unit tests) and `refinement/` (README with the targets against `ThresholdAuth.lean`, `run_extraction.sh` for Charon and Aeneas). The Aeneas Lean backend needs Lean 4.36 and Mathlib, so the proof will live in a separate Lake package; the sandbox cannot build Aeneas (OCaml, Nix and Rust hosts are blocked), so the extraction has not been run and nothing is claimed. The Rust code is still tied to Lean by differential tests only.
- Refinement setup, first run on the Mac: Aeneas and Charon built and ran on `rust/sirm-keys-core`; `count_valid` and `accepts` were extracted, `keys_distinct` was rejected ("returns inside of nested loops are not supported yet"). `keys_distinct` now uses a flag instead of an early `return`; same behaviour, same tests. The refinement proof is still not started.
- Refinement package `refinement/lean` (Lean 4.36, Aeneas dependency): committed the Aeneas translation of `sirm-keys-core` and a first draft of the proofs `count_valid_spec`, `accepts_spec` and `keys_distinct_spec`. Not compiled yet (the sandbox cannot build Aeneas and Mathlib); nothing is claimed until `lake build` passes on the Mac.
- Refinement package: the Aeneas dependency is pinned to a commit (the repository has no `master` branch, so the unpinned require failed).
- Refinement proofs, first `lake build` on the Mac: the translation and most of the draft compile; fixed the first loop spec (refine instead of apply), one surplus tactic and three no-progress simplifications. Still not a finished proof until the build is clean.
- Refinement proofs, second build: one error left in the first loop spec (type of the result variable not inferred); annotated the loop-state and result types in the three loop specs.
- Refinement proofs, third build: rewrote the case split of the count loop body (explicit facts for the overflow bound and the invariant); remaining proofs (accepts, keys_distinct) not yet reached by the checker.
- First refinement proofs complete: `lake build` in `refinement/lean` succeeds (3,617 jobs) and `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound` for `count_valid_spec`, `accepts_spec` and `keys_distinct_spec`. Scope: the loop-only core `rust/sirm-keys-core` as translated by Aeneas; the translation is trusted, the specifications mirror `ThresholdAuth.lean` by shape, and `sirm_codec::keys` does not call the core yet. The package is not in CI; the result was obtained on the Mac, not in the sandbox.
- `sirm_codec::keys::keys_distinct` and `threshold_accepts` now call `sirm-keys-core` (path dependency, `Cargo.lock` updated): the proved core decides distinctness and the `0 < k && k <= count` rule, so the proved code is the code that runs for these two decisions. The 1,500 threshold cases and the other 31 Rust test files still pass (cargo test, clippy with `-D warnings`). The construction of the valid-index list stays differential evidence.
- Nonce decision moved into the loop-free core `sirm-keys-core` (`nonce_class`: stale, future, or stale at the `u64::MAX` ceiling, in the order of `IntegratedPipeline.processCapped`; `next_nonce`) and `integrated::Machine::process` calls it. Behaviour unchanged (clippy with `-D warnings` and all Rust tests pass, including the ceiling tests). No Lean proof of this core yet: it must be extracted with Aeneas and proved against `processCapped` before any claim is made.
- Draft proofs for the nonce core in `refinement/lean`: `nonce_class_spec` (stale / future / ceiling-stale / proceed, in the order of `processCapped` with `N = 2^64 - 1`) and `next_nonce_spec` (below the ceiling the successor is the counter plus one, no overflow); the regenerated Aeneas translation now includes `nonce_class` and `next_nonce`. Not built yet: nothing is claimed until `lake build` passes on the Mac.
- `nonce_class_spec` and `next_nonce_spec` are built: `lake build` in `refinement/lean` succeeds (3,617 jobs), no `sorry`, axioms `propext`, `Classical.choice`, `Quot.sound` for them and for `keys_distinct_spec`. `integrated::Machine::process` calls the proved core for the nonce decision. Limits: the translation is trusted, the specification is tied to `processCapped` by shape and not by a theorem, and everything else in `process` is differential evidence. Result obtained on the Mac.
- Migration arithmetic moved into the loop-free core `sirm-keys-core` (`migrate_acc`: `amount * num + dust` or `None` on `u128` overflow, the `checked_mul`/`checked_add` pair written with comparisons; `migrate_split`: `(acc / den, acc % den)`), called by the validation and by the apply step of `integrated::Machine`. Behaviour unchanged: unit test against the `checked_*` operations on boundary values, clippy with `-D warnings` and all Rust tests pass. No Lean proof of this part yet: it has to be extracted with Aeneas and proved first. The request-cache lookup was not moved: it is a comparison and a lookup with nothing to prove without modelling `Request`.
- Draft proofs for the migration arithmetic in `refinement/lean`: `migrate_acc_spec` (the result is `amount * num + dust`, and `none` exactly when that sum exceeds `u128::MAX`) and `migrate_split_spec` (division with remainder, `acc = released * den + rest`, `rest < den`); the regenerated translation includes `migrate_acc` and `migrate_split`. Not built yet: nothing is claimed until `lake build` passes on the Mac.
- Migration proofs, first build: five errors fixed (two trivial goals closed by `simp`, the `u128` maximum made explicit for `omega` in the two `add_spec` side conditions, the zero-multiplier case taken from the simplified hypothesis). Not a finished proof until `lake build` passes.
- License changed to BUSL-1.1 on the owner's decision (see `docs/DECISIONS.md`): root `LICENSE` is the standard text of the Business Source License 1.1 (copied unchanged from the SPDX list) with the parameters filled in; the old Apache text is kept in `LICENSES/Apache-2.0.txt`; the two crates declare `BUSL-1.1`; README and CONTRIBUTING updated (outside pull requests are not accepted until contributor terms exist). Also: the `U128.max` equality in the migration proof now uses the library lemma `U128.max_eq` (the previous `decide` could not reduce it). Not a legal opinion; a lawyer has not reviewed the parameters.
- Migration proofs finished: `lake build` in `refinement/lean` succeeds (3,617 jobs), no `sorry`; `#print axioms` for `migrate_acc_spec` and `migrate_split_spec` gives `propext`, `Classical.choice`, `Quot.sound`. Limits as before: the translation is trusted, the specifications are tied to the Lean model by shape and not by a theorem, and the rest of the Rust code is covered by differential tests only.
- `IntegratedPipeline.processCapped_stale_iff` and `processCapped_future_iff`: on a cache miss the capped pipeline answers stale exactly when the nonce is behind the counter or equals a counter at the ceiling, and future exactly when the nonce is ahead; these are the conditions of `nonce_class_spec` of the Rust core. Compiles with Lean 4.33.1, no Mathlib.
- `add_ok` (the `checked_add` decision on `u128`) moved into `sirm-keys-core`; the validation of `issue` and `migrate` in `integrated::Machine` calls it in six places. `add_ok_spec` is proved; `lake build` in `refinement/lean` succeeds (3,617 jobs), no `sorry`.
- `ThresholdAuth.thresholdAccepts_iff_flags`: the Lean threshold decision equals `0 < k ∧ k ≤` the number of true entries of `validFlags`, the input and the condition of the Rust core `accepts` and its `accepts_spec`. Compiles with Lean 4.33.1, no Mathlib.
- `sub_ok` added to `sirm-keys-core` and proved (`sub_ok_spec`); `lake build` in `refinement/lean` succeeds (3,617 jobs), no `sorry`. `ledger.rs` (`transfer`, `issue`, `burn`) and `fees.rs` (`net_amount`) now use `add_ok` and `sub_ok` instead of `checked_add` and `checked_sub`; all Rust tests unchanged and green.
- `succ_ok` (the `checked_add(1)` decision on a `u64` nonce: `None` at `u64::MAX`, otherwise `x + 1`) added to `sirm-keys-core` and proved (`succ_ok_spec`); `lake build` in `refinement/lean` succeeds (3,617 jobs), no `sorry`, axioms `propext`, `Classical.choice`, `Quot.sound`. The nonce successor and the remaining `u128` sums in migration, receipts, escrow and the ledger (`envelope.rs`, `ledger.rs`, `machine.rs`, `migration.rs`, `receipt.rs`, `timelock.rs`) go through the core. Limits as before: the translation is trusted and the rest of the Rust code is covered by differential tests only.
- CI per pull request is now 20 checks: the Lean job, the Rust job, the 17 static audits and `Refinement / build and proofs`, which builds `refinement/lean` (Mathlib cache) and runs `refinement/check_proofs.sh` (no proof placeholder in `KeysCoreProofs.lean`; the ten refinement theorems depend on `propext`, `Classical.choice` and `Quot.sound` only). It passed on its first run on GitHub (about 6 minutes). The Rust job also runs the unit tests of `sirm-keys-core`. The Refinement job and the Rust job are now required status checks of `main`; before this change the Rust job was not required, so a failing Rust job would not have blocked a merge.
