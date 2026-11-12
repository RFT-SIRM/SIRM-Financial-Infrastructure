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
- This remains an abstract formal transition. `AuthorizedAssetMigration` alone does not provide replay protection, external bridge settlement/finality, custody, rollback, asset-collision handling, production valuation, or legal/economic backing. The separate `ReplayProtectedAssetMigration` wrapper adds only a migration-scoped per-principal sequential nonce; it does not add global transaction idempotency or runtime persistence.

### Per-principal nonce and replay protection for migration

- `SIRM.ReplayProtectedAssetMigration` augments the authorized migration state with `nextNonce : Principal → Nat`. The initial expected nonce is zero for every principal.
- A migration request is admitted only when its supplied nonce equals `nextNonce principal`. The accepted transition applies the existing authorized burn/issue/dust update and advances that principal's expected nonce to `nonce + 1` in the same returned state.
- The transition lemmas prove that the selected principal advances by exactly one, other principals are unchanged, and a nonce unequal to the expected value cannot satisfy the step relation. The replay-protected reachable-state theorem retains the complete holder/GL/residual migration invariant.
- This is a sequential nonce gate for this abstract migration machine only. It does not define a global protocol nonce across transfers and other operations, a transaction hash or idempotent response cache, canonical transaction encoding, signatures, expiry, persistent storage, concurrent execution, or runtime atomic commit semantics. `Nat` is unbounded in Lean; production nonce width and overflow behavior are not selected.

### Registry-aware issuance eligibility

- `SIRM.RegistryAwareFinancialMachine` composes the existing authority-grant and account-control policy with `AssetRegistry.issuanceEnabled`. A new issue is admitted only when the original policy authorizes the principal, issuer, recipient, asset, and amount, and the asset plus its issuer account are active.
- Transfer and burn authorization predicates are passed through unchanged. This block does not introduce transfer/burn freeze gates, account lifecycle transitions, or production policy administration.
- The registry-aware machine reuses the paired holder/GL transition and the existing reachable-state theorem for holder reconciliation, subledger agreement, and aggregate signed-ledger conservation.

### Combined authorized financial machine

- `SIRM.AuthorizedFinancialMachine`: one abstract financial state containing both holder balances and the signed general ledger.
- Its authorized transfer, issuance, and burn steps update the holder projection and the corresponding journal projection together in a single Lean state transition.
- The machine invariant preserves holder/supply reconciliation, mapped holder-subledger agreement, and aggregate signed general-ledger balance relative to the opening ledger.
- `SIRMTests.lean` contains a concrete integrated transfer → issuance → burn theorem-level regression trace, including reachability and the stated financial invariants.

### Authorized one-record escrow lifecycle

- `SIRM.EscrowAccounting` models a dedicated escrow holder account as part of the holder universe. Opening moves existing units from a depositor into that vault; release transfers the recorded amount to the fixed beneficiary; cancellation returns it to the depositor. These are ordinary holder transfers, not issuance or burn.
- Opening, release and cancellation each require an ordinary transfer-policy witness and an independent escrow-policy witness. Opening is admitted only from `ready`; release/cancel are admitted only from `pending`. A terminal record cannot be reopened, preventing reuse of the same escrow record after completion.
- The escrow invariant requires the vault to hold exactly the recorded amount of the escrow asset while pending, and zero units of every asset in all other phases. It composes with holder/supply reconciliation, mapped holder/GL agreement, and aggregate signed GL conservation. The state machine therefore preserves these facts for every reachable state.
- `EscrowAccounting` is the single-record primitive only. The composed escrow model is layered: `EscrowRegistry` adds concurrent, permanently allocated IDs; `EscrowPooledReserve` derives aggregate pending obligations by asset; `EscrowFinancialIntegration` identifies those obligations with the designated vault-holder balance and mapped GL subledger; `EscrowTimeLocks` adds discrete per-ID deadlines and separately authorized expiry refunds; and `EscrowDisputes` adds a separate policy-gated first-stage dispute intake/freeze marker that freezes release, voluntary cancellation, and timeout expiry for the selected ID. The dispute marker does not move funds, the clock may still advance, and unrelated IDs remain independent. The marker is permanent in this stage. Wall-clock binding, scheduler liveness, adjudication, evidence validation/provenance, appeals, outcome-specific settlement, external finality, reversals, and production idempotency remain outside the model. Rights and authority remain policy inputs, not legal or cryptographic proofs.

## 2. Important distinction: abstract paired transition vs production transaction

The combined machine **does** formalize a paired state transition: a holder operation and its corresponding general-ledger posting are represented together in one transition of the abstract Lean state. It would therefore be inaccurate to say that no unified holder/ledger transition is formalized.

That result does **not** yet provide a production transaction processor. The migration wrapper proves only an abstract per-principal sequential nonce gate for migration. The current declarations do not specify or implement a complete transaction object, canonical byte encoding, cryptographic signature verification, signer thresholds, expiry, operation-wide nonce handling, idempotent replay responses, event encoding, production failure codes, rollback, or runtime storage/commit atomicity. Nor is Rust proved to refine the Lean transition.

## 3. Not established by the current declarations

- Completeness or legal correctness of the account universe; it is an explicit assumption of holdings reconciliation.
- A concrete principal-to-account legal-ownership map, production identity verification, cryptographic signatures, private-key custody, lifecycle transition policy, production role semantics, signer thresholds, or permission-policy administration. Typed account metadata is descriptive and does not by itself establish these properties.
- A complete genesis assignment to actual founder, treasury, validator, ecosystem, community, and other accounts.
- A production posting policy for custody, customer-liability, control, and other non-holder GL accounts.
- Wall-clock binding and automatic timeout-scheduler liveness; dispute adjudication, evidence validation/provenance, appeals, outcome-specific beneficiary/refund settlement, external settlement finality/evidence, and reversal policy. Concurrent IDs, pooled vault/GL reconciliation, discrete expiry guards/refunds, and first-stage dispute intake/freeze are formalized. Credit lines, account restrictions, and multi-asset FX/valuation rules also remain open.
- Reserve backing, solvency, par redemption, external asset existence, or independent reserve attestations.
- A global-field distribution law or an equivalence to legacy Rift behavior.
- Rust/Lean refinement, consensus safety/finality, censorship resistance, data availability, privacy guarantees, legal enforceability, licensing conclusions, or regulatory compliance.

## 4. Assurance rule

A theorem applies only to its formal statement and assumptions. A successful pinned `lake build SIRM` and `lake test` establish that the relevant source and theorem-level regression library compile under the configured toolchain; they do not prove that an unimplemented runtime, network, institution, or external asset behaves as modeled.

Implementation claims require a documented refinement/conformance argument plus appropriate differential tests, property/fuzz testing, independent security review, and operational evidence. Network, institutional, legal, reserve, and regulatory claims require their own separate evidence.


## Fee accounting boundary

The initial fee model treats a fee as an internal transfer of already-issued base units: gross is split exactly into net beneficiary credit plus fee-collector credit. The collector is an explicit holder, and fee authorization is independent of ordinary transfer authorization. No units are minted or burned by the fee transition. The model does not yet classify a non-holder revenue account, define a tariff schedule, rounding/minimum/maximum rules, tax treatment, refunds, fee changes, or production revenue recognition.


## Escrow accounting boundary

Escrowed units remain holder-owned units in the formal supply partition, held temporarily in a dedicated vault account. This model does not represent them as both depositor assets and a separate liability balance; the vault is the single holder coordinate for those units. The concurrent registry's pending aggregate is reconciled to that vault coordinate and its mapped GL subledger. Expiry returns the selected record to its depositor under a distinct permissioned transition. Dispute intake only records a per-ID freeze marker: it does not move the escrowed funds or decide entitlement. These abstract results prove accounting movement, phase-dependent backing, and the specified safety guards, not legal beneficial ownership, custody, external delivery, evidence authenticity, or settlement finality.
