# Testing and Verification

## Pinned Lean build

The CI workflow pins Lean 4.33.1 and Mathlib v4.33.1 and explicitly runs:

- `lake build` for the normative `SIRM` target;
- `lake test` for the `SIRMTests` theorem-level regression library.

## What the theorem-level regression suite checks

`SIRMTests.lean` instantiates the formal model with three accounts and two assets. It checks:

- initial per-asset holdings/supply reconciliation;
- a funded transfer and its exact resulting balances;
- proof that an over-funded transfer request does not satisfy the transition precondition;
- successful proof-carrying transfer and preservation of reconciliation;
- successful proof-carrying holder burn and proof that an excessive burn does not satisfy its precondition;
- self-transfer behavior;
- non-interference with another asset;
- issuance and corresponding outstanding-supply increase;
- a holder-bounded burn and corresponding supply decrease;
- exact founder-allocation arithmetic;
- a concrete use of the balanced journal conservation theorem;
- a separate four-account general ledger (including an unmapped control account), with holder/subledger agreement preserved by a matching transfer journal;
- an authorized transfer → issuance → burn trace, with a reachability proof and final holdings/supply reconciliation theorem;
- holder issuance and burn journal tests using the unmapped demo control account, checking per-asset journal balance, aggregate signed-ledger conservation, mapped subledger agreement, and the exact control-account postings;
- an integrated financial-machine trace executing transfer → issuance → burn, proving reachability, holder/supply reconciliation, mapped subledger agreement, aggregate signed-ledger conservation relative to the opening ledger, and exact Alice, treasury and control balances.

Because the test driver is a Lean library, `lake test` succeeds only if these statements and proof terms compile. The tests are theorem-level regression checks, not a runtime node test or a randomized fuzz campaign. The demo authorization policy is illustrative only; it does not select a production ownership, key, role, threshold, or governance scheme.

The account-control and issuer-scope regression cases additionally verify:

- authority issue scopes bind the exact issuer and recipient, asset, and amount limit;
- account control is a separate finite relation and is not inferred from an authority grant;
- a grant without account control is rejected, and account control without the exact operation grant is rejected;
- Treasury may issue to Alice under a Treasury-to-Alice grant while Treasury controls only the issuer account;
- the registry-backed financial trace uses the combined control-plus-grant policy for transfer, issue, and burn;
- issuance credits the recipient and increases outstanding supply; it does not debit the issuer account.

## Lint and runtime tests

Linting is explicitly disabled in CI until a linter driver is added. Runtime/property/fuzz tests for an executable reference implementation are not yet present. These are separate requirements and must not be described as passed.

## Reproducibility

A green run must be tied to the exact commit SHA and pinned toolchain. An absent test driver, skipped test command, or empty build is not accepted as a passing test result.

### Account-control theorem traceability

The following theorem-level regressions are compiled by `lake test`:

- `registryGrantWithoutAccountControlIsDenied` rejects an authority grant when the principal does not control the relevant account.
- `registryAccountControlWithoutGrantIsDenied` rejects account control when the exact operation grant is absent.
- `controlledTreasuryMayIssueToUncontrolledAlice` permits the explicitly granted Treasury-to-Alice issuance without requiring Treasury to control Alice's recipient account.

## Typed registry regression cases

The `SIRMTests.lean` suite additionally compiles the following cases:

- account and asset identifiers are distinct finite types and instantiate the existing holdings model;
- account classification is retrievable from the typed account registry;
- asset decimal metadata determines a positive base-unit scale (the two-decimal test fixture is non-normative);
- each asset's issuer account is proven to share its declared network;
- issuance eligibility holds for an active asset with an active issuer;
- issuance eligibility fails when the issuer account is frozen;
- issuance eligibility fails when the asset is not active (the draft-status case).

These tests do not select production RFT decimals, a production network identifier, or cross-network migration semantics.

## Registry-aware financial-machine regressions

The registry-aware tests compile the following cases:

- the active typed asset and active issuer pass the new issuance gate only after the existing principal/account-control and exact issue-grant policy passes;
- a draft asset is denied even when the underlying authority and control policy allows the issue;
- a frozen issuer is denied even when the underlying authority and control policy allows the issue;
- transfer and burn authorization predicates are definitionally unchanged by the adapter;
- one admitted typed issuance is a reachable transition of the new combined financial machine, and the resulting state retains holder/supply reconciliation, mapped subledger agreement, and aggregate signed-ledger conservation.

The gate is intentionally issuance-specific in this block. It does not yet formalize lifecycle transitions or impose asset/issuer activity checks on transfer or burn.

## Exact asset-denominated base-unit regressions

The `SIRMTests.lean` suite compiles these exact-conversion cases:

- whole-unit amounts convert by multiplying by the metadata scale `10 ^ decimals`;
- an input using exactly the asset's decimal precision maps its coefficient directly to base units;
- input with additional trailing zero digits is divided exactly and accepted;
- input with nonzero excess precision is rejected rather than truncated or rounded;
- a caller-supplied inclusive maximum is enforced by returning `Fin (maxBaseUnits + 1)` or `none` when out of range.

The range proof is parameterized by a natural-number maximum. It does not select a machine integer width or claim runtime overflow safety for a Rust implementation. Production decimals remain unselected.


## Exact cross-network migration arithmetic regressions

The `SIRMTests.lean` suite compiles synthetic-rate examples and generic theorems:

- a positive rational rate decomposes source-scaled units into target units times the denominator plus a strictly smaller residual numerator;
- a residual that cannot yet form one target base unit is retained;
- later source input consumes the carried residual and releases the exact accumulated target amount;
- the cumulative scaled-value equation remains invariant after every accrual;
- accumulator types are scoped to a rate and a partition, so different owners or rate configurations cannot silently share dust state;
- a route connects distinct assets on distinct registered networks, and route eligibility requires both assets and both issuer accounts to be active.

The rate values in regressions are synthetic. These proofs do not implement migration authorization, burning, minting, bridge settlement, replay protection, or production custody.


## Authorized atomic cross-network migration regressions

The `SIRMTests.lean` suite compiles a two-step synthetic migration through the verified migration machine:

- the source holder and destination recipient are pinned to the route's respective networks;
- the same principal must control the source holder and destination issuer and possess the exact burn and issue grants;
- the first source unit is burned while its fractional target residual is retained and no whole target unit is issued;
- the second source unit consumes the carried residual and issues exactly one target base unit;
- both holder balances and their corresponding source/destination GL subledgers change in the same state transition;
- the reachable-state theorem preserves holder reconciliation, mapped subledger agreement, aggregate GL balance per asset, and exact residual conservation.

The example uses a synthetic 2/3 base-unit rate. The residual is an auxiliary exact claim subledger, not a fractional posting to the integer GL. Replay/idempotency and external bridge execution remain out of scope.
