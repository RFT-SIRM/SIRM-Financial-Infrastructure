# Mathematical Scope and Assurance Boundaries

This document describes what the current Lean declarations establish, the assumptions they use, and what they do not establish. A module's presence in source is not by itself a claim that a theorem was successfully checked at an arbitrary commit; the pinned CI run must be tied to the exact revision.

## 1. Current Lean development

### Supply and financial state

- `SIRM.FinancialCore`: supply-state definition, initial state, mint and burn transitions with invariant-preservation statements, exact 1.309% founder-rate arithmetic, founder allocation, and the unallocated remainder.
- `SIRM.Holdings`: nonnegative integer holder balances indexed by account and asset; exact per-asset reconciliation with outstanding supply; funded transfers; issuance to a holder; and holder-bounded burns.
- The holdings reconciliation theorem assumes a complete account universe in which each outstanding unit is assigned exactly once. It does not independently establish that the universe corresponds to legal ownership or real-world custody.

### General ledger and holder bridge

- `SIRM.Accounting`: a finite-account, per-asset signed general ledger; journal entries carrying a per-asset balance proof; aggregate signed-balance preservation for balanced entries; and a balanced transfer-journal constructor.
- `SIRM.HolderAccountingBridge`: matching balanced journals for holder transfers, issuance, and burns; pointwise subledger-agreement preservation under an unmapped counterpart-account assumption.
- Holder balances and the signed general ledger are separate projections. The bridge relates them; it does not treat them as additive copies of the same quantity.

### Authorization and reachable-state results

- `SIRM.Authorization`: abstract, state-dependent authorization predicates and guarded transfer, issue, and burn operations. The predicates are policy inputs, not a selected production identity or cryptographic scheme.
- `SIRM.StateMachine`: a generic theorem deriving an invariant for reachable states from an invariant initial state and transition-preservation obligation.
- `SIRM.AuthorizedStateMachine`: an authorization-gated holder transition relation and reachable-state preservation of the holdings invariant.

### Typed finite account and asset registries

- `SIRM.TypedRegistry` defines distinct finite account and asset identifier types, so an account identifier cannot be supplied where an asset identifier is required.
- The account registry is total over its finite account universe and records account class, lifecycle status, and network.
- The asset registry is total over its finite asset universe and records symbol, decimal precision, issuer, lifecycle status, and network.
- A registry proof enforces that each asset's issuer account belongs to the same declared network. Registry-level issuance eligibility requires both the asset and issuer account to be active.
- These metadata predicates do not prove identity, ownership, key custody, or authority. The existing authority-grant and account-control gates remain independent. Cross-network migration is composed by a separate transition module; the registry itself does not execute a migration.

### Exact asset-denominated base units

- `SIRM.AssetUnits` represents a nonnegative decimal input as a natural-number coefficient plus an explicit decimal-place count. For an asset with `d` decimals, input precision `p ≤ d` is scaled by `10^(d-p)`; when `p > d`, conversion succeeds only if the coefficient is divisible by `10^(p-d)`. Nonzero excess digits are rejected rather than rounded.
- Whole-unit conversion uses the registry metadata scale `10^d`. The `Fin (maxBaseUnits + 1)` adapter separately enforces an explicit inclusive range bound. Lean's `Nat` is mathematically unbounded; this generic bound does not select or prove a concrete Rust/C machine integer width, and runtime overflow behavior remains a downstream refinement obligation.
- No production asset decimal precision, target integer width, floating-point representation, or rounding policy is selected by these definitions.

### Exact cross-network migration arithmetic

- `SIRM.AssetMigration` represents a positive rational rate as `numerator / denominator`, interpreted as target base units per source base unit. Both values are explicit parameters; no production rate or market price is selected.
- For source amount `s`, the proof-carrying conversion establishes `s * numerator = targetBaseUnits * denominator + dustNumerator`, with `dustNumerator < denominator`. The remainder is an exact fraction of one target base unit, not a rounded-away value.
- `AssetMigrationDustState` carries that numerator into subsequent conversions. Its type is indexed by the exact rate and an accounting partition, preventing accidental combination of dust from different rates or different partitions. A caller choosing one shared partition is making an explicit pooling-policy choice outside the theorem.
- A route requires distinct asset identifiers and distinct registered network identifiers. `endpointsEnabled` additionally requires both assets and both issuer accounts to be active.
- The base `SIRM.AssetMigration` module supplies exact arithmetic and route eligibility; `SIRM.AuthorizedAssetMigration` composes it into an abstract controlled burn/issue transition. Neither module establishes external custody, bridge finality, replay/idempotency, rollback, asset-collision policy, or legal/economic backing.

### Authorized atomic cross-network migration

- `AuthorizedAssetMigrationPartition` fixes one registered route, one source holder, and one destination recipient. It carries proofs that the source holder belongs to the source asset's network and the recipient belongs to the destination asset's network. Residuals therefore cannot be silently shared across different routes or account pairs.
- A step requires one principal to satisfy the source-holder control relation and exact burn grant, plus control of the destination asset issuer and an exact issue grant for the target amount actually released by the carried residual. Both endpoint assets and their issuers, and both endpoint accounts, must be active.
- The transition burns source base units, issues the quotient output in destination base units, posts a source burn journal and a destination issuance journal, and advances the residual state in one state value. There is no intermediate state exposing only one side of the operation.
- The state machine preserves holder/supply reconciliation, mapped holder/GL agreement, aggregate signed GL totals per asset, and the route/source-holder/recipient residual equation. The residual accumulator is a separate exact claim subledger; fractional dust is not posted as an integer-valued GL liability account by this model.
- This remains an abstract formal transition. It does not provide a transaction nonce, replay/idempotency protection, external bridge settlement/finality, custody, rollback, asset-collision handling, a production valuation policy, or legal/economic backing for the residual claim.

### Registry-aware issuance eligibility

- `SIRM.RegistryAwareFinancialMachine` composes the existing authority-grant and account-control policy with `AssetRegistry.issuanceEnabled`. A new issue is admitted only when the original policy authorizes the principal, issuer, recipient, asset, and amount, and the asset plus its issuer account are active.
- Transfer and burn authorization predicates are passed through unchanged. This block does not introduce transfer/burn freeze gates, account lifecycle transitions, or production policy administration.
- The registry-aware machine reuses the paired holder/GL transition and the existing reachable-state theorem for holder reconciliation, subledger agreement, and aggregate signed-ledger conservation.

### Combined authorized financial machine

- `SIRM.AuthorizedFinancialMachine`: one abstract financial state containing both holder balances and the signed general ledger.
- Its authorized transfer, issuance, and burn steps update the holder projection and the corresponding journal projection together in a single Lean state transition.
- The machine invariant preserves holder/supply reconciliation, mapped holder-subledger agreement, and aggregate signed general-ledger balance relative to the opening ledger.
- `SIRMTests.lean` contains a concrete integrated transfer → issuance → burn theorem-level regression trace, including reachability and the stated financial invariants.

## 2. Important distinction: abstract paired transition vs production transaction

The combined machine **does** formalize a paired state transition: a holder operation and its corresponding general-ledger posting are represented together in one transition of the abstract Lean state. It would therefore be inaccurate to say that no unified holder/ledger transition is formalized.

That result does **not** yet provide a production transaction processor. The current declarations do not specify or implement a complete transaction object, canonical byte encoding, cryptographic signature verification, concrete signer thresholds, nonce and expiry handling, replay protection, event encoding, production failure codes, rollback behavior, or runtime storage/commit atomicity. Nor is a Rust implementation yet proved to refine the Lean transition.

## 3. Not established by the current declarations

- Completeness or legal correctness of the account universe; it is an explicit assumption of holdings reconciliation.
- A concrete principal-to-account legal-ownership map, production identity verification, cryptographic signatures, private-key custody, lifecycle transition policy, production role semantics, signer thresholds, or permission-policy administration. Typed account metadata is descriptive and does not by itself establish these properties.
- A complete genesis assignment to actual founder, treasury, validator, ecosystem, community, and other accounts.
- A production posting policy for custody, customer-liability, control, and other non-holder GL accounts.
- Freeze, escrow, fees, settlement, reversals, credit lines, account restrictions, and multi-asset FX/valuation rules.
- Reserve backing, solvency, par redemption, external asset existence, or independent reserve attestations.
- A global-field distribution law or an equivalence to legacy Rift behavior.
- Rust/Lean refinement, consensus safety/finality, censorship resistance, data availability, privacy guarantees, legal enforceability, licensing conclusions, or regulatory compliance.

## 4. Assurance rule

A theorem applies only to its formal statement and assumptions. A successful pinned `lake build SIRM` and `lake test` establish that the relevant source and theorem-level regression library compile under the configured toolchain; they do not prove that an unimplemented runtime, network, institution, or external asset behaves as modeled.

Implementation claims require a documented refinement/conformance argument plus appropriate differential tests, property/fuzz testing, independent security review, and operational evidence. Network, institutional, legal, reserve, and regulatory claims require their own separate evidence.
