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
