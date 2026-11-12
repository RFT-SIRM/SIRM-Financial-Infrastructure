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

## Work block: first-stage escrow dispute intake/freeze (local checks passed; commit/PR pending)

### Verified baseline and preceding escrow layers

- Repository: `RFT-SIRM/SIRM-Financial-Infrastructure`.
- Exact starting `main` SHA: `998bec99364832c0273d8680993f453b44c3dbb9`.
- The escrow foundation was merged in sequence: PR #16 (`5755c728b551a2838f505c6a9f9eaf6c1d19b03c`) added concurrent IDs and pooled reserve; PR #17 (`ed928ecdc34e2740ea87a55925fad8ab8386ddb2`) connected the reserve to `FinancialState` and the mapped GL; PR #23 (`998bec99364832c0273d8680993f453b44c3dbb9`) added discrete deadlines and permissioned expiry. PR #23 passed all 18 CI jobs for its exact head.
- Existing local branch: `feat/escrow-dispute-freeze-2026-11-12`, based on the exact `main` SHA above. The branch and worktree are local only at this point; no feature commit, remote feature branch, PR, or merge has been created.

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

### Next gate

Review the complete final diff after documentation reconciliation, run the mandatory commands again, and only then create one commit on this existing branch and one non-force push. Verify the remote SHA, open one PR, and require all 18 checks to pass for its exact head before merge. Do not create another branch or touch `main` directly.
