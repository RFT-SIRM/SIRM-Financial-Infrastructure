# Formalization Status

This file separates Lean declarations present in source from protocol properties still awaiting formalization. A declaration is not described as kernel-checked until the pinned `lake build SIRM` succeeds for the relevant commit.

## Present in the repository

- Supply-state definition and initial-state invariant.
- Mint transition and invariant-preservation theorem.
- Burn transition with an explicit sufficient-outstanding precondition and invariant-preservation theorem.
- Exact 1.309% founder-rate representation as 13,090 ppm.
- Founder allocation floor formula, allocation upper-bound theorem, and founder-plus-remainder equality.
- Genesis allocation record with all non-founder pools explicitly unallocated.
- Generic finite-account, per-asset signed general-ledger model.
- Per-asset balance-conservation theorem for any journal entry carrying its balance proof.
- A balanced transfer-journal constructor for the signed general-ledger view.
- An injective holder-to-subledger mapping and a pointwise agreement relation for the designated ledger accounts.
- A theorem that a holder transfer and its matching per-asset journal preserve the subledger agreement and aggregate signed-ledger balance.
- Balanced holder-issuance and holder-burn journals using an explicitly unmapped counterpart account; their mapped subledger effects preserve pointwise holder/GL agreement, and each journal preserves aggregate signed-ledger balance.
- Per-asset holder holdings indexed by account and asset.
- A reconciliation invariant requiring nonnegative holder balances whose total equals outstanding supply.
- A theorem bounding each nonnegative holder balance by total holdings.
- A funded holder-transfer transition preserving balances, nonnegativity and supply reconciliation; self-transfer is a no-op.
- An issuance-to-holder transition that increases the holder balance and outstanding supply equally.
- A burn-from-holder transition bounded by that holder's balance, with a proof that this bound also protects aggregate outstanding supply.
- Proof-carrying transfer and holder-burn transitions: numeric preconditions are explicit proof arguments, so invalid requests have no admissible transition term; every resulting state preserves the holdings invariant.
- Generic reachable-state invariant theorem, instantiated by an authorization-gated holder state machine and a combined authorized financial machine. The combined machine updates holder balances and corresponding GL journals together; a stronger reachable-state theorem also preserves aggregate signed GL balance for every asset relative to the opening ledger.
- A dedicated `SIRMTests` Lake test-driver library covering a reconciled two-asset example, funded transfer, overspending rejection, self-transfer, issuance, holder burn, founder allocation arithmetic and journal conservation.
- `SIRM.TypedRegistry` defines distinct finite `AccountId` and `AssetId` types, total metadata registries, account classes and lifecycle statuses, asset decimal precision and issuer metadata, and a proof that each asset's issuer account shares its network. Registry-level issuance eligibility requires both an active asset and an active issuer.
- `SIRM.RegistryAwareFinancialMachine` wraps the existing authority/control policy with the typed registry's issuance gate. An issue step requires the existing policy plus an active asset and active issuer; transfer and burn policy predicates are unchanged. The wrapper reuses the combined holder/GL machine and its reachable-state conservation theorem.
- `SIRM.AssetUnits` defines explicit decimal-coefficient inputs, exact conversion to integer asset base units, rejection of nonrepresentable excess precision, and a range-bounded conversion returning `Fin (max + 1)` under a caller-supplied limit. No floating-point conversion or implicit rounding is introduced.
- `SIRM.AssetMigration` defines positive rational rates in target-base-units per source-base-unit, a proof-carrying quotient/remainder conversion, a cumulative dust state preserving the scaled-value equation, and cross-network route metadata. Dust state is indexed by the exact rate and an explicit accounting partition.
- `SIRM.AuthorizedAssetMigration` composes source burn and destination issue authorization with account-control and exact authority-grant checks, active endpoint/account checks, a route/source/recipient-indexed residual claim subledger, and one paired holder/GL state transition. Its verified machine preserves holder reconciliation, mapped subledger agreement, aggregate per-asset GL totals, and the residual scaled-value equation.
- `SIRM.ReplayProtectedAssetMigration` wraps the authorized migration with a migration-scoped expected-next-nonce function indexed by principal. A step requires exact nonce equality and returns the migration update plus a one-step nonce increment in the same state; stale and future nonce mismatches are rejected, and other principals' nonce values are unchanged.
- `SIRM.ReplayProtectedFinancialMachine` generalizes sequential replay protection to the complete authorized financial transition relation: transfer, issuance and burn share one per-principal nonce sequence, with the financial update and nonce increment paired atomically in the abstract state. Stale/future mismatch rejection, selected-principal increment, other-principal frame preservation, and reachable holder/GL conservation are proved.
- `SIRM.FinancialTransactionEnvelope` binds a typed transfer/issue/burn payload and request ID to an accepted response receipt. It proves receipt-first exact retry lookup and state non-interference, rejects rebinding an occupied ID to a different payload, proves a second request from the same principal cannot commit at an already-consumed nonce, rejects stale/future nonce as a new success, proves receipt key/payload/nonce consistency in every reachable state, and preserves the existing holder/GL conservation invariant. This is an abstract state-machine result, not a database linearizability or crash-durability proof.
- `SIRM.FinancialTransactionDenials` composes a denial-receipt cache with the success envelope using one request-ID namespace. It proves that authorization denials are admitted only at the exact current nonce and that authorized non-self transfers or burns with insufficient funds receive a distinct cached business-denial reason. Both denial classes store the exact request/reason/expected nonce, change neither balances nor GL nor nonce, and preserve the disjoint success/denial cache invariant over reachable processor states. Exact retry returns the original response without re-evaluating current authorization or funds. Self-transfers are excluded from insufficient-funds classification; issuance has no debit-funding precondition. The transition relation is parameterized by a fixed policy; policy mutation is not represented as a reachable in-machine transition. Expiry, signature, and other deterministic failure classes remain open.

- A finite static account-control relation, independent of authority grants, represented by principal/account pairs. The combined policy requires control of the source for transfers, the issuer for issuance, and the holder for burns, together with an exact grant. Issue grants bind both issuer and recipient; recipient control is not required by this model.
- A registry-backed authorization adapter and regression theorems for denial when control is absent, denial when the exact grant is absent, and an allowed Treasury-to-Alice issuance where Treasury controls the issuer account but not Alice's recipient account. The holder operation remains mint-to-recipient and does not debit the issuer.

- `SIRM.EscrowAccounting` defines a one-record authorized escrow lifecycle. Opening transfers funded, already-issued units from a depositor to a dedicated vault holder; release transfers the exact amount to the recorded beneficiary; cancellation returns it to the depositor. Separate ordinary-transfer and escrow-specific permissions are required. The verified machine preserves holder/supply reconciliation, mapped holder/GL agreement, aggregate signed GL totals, exact vault backing while pending, and terminal-state replay rejection.
- `SIRM.EscrowRegistry`, `SIRM.EscrowPooledReserve`, and `SIRM.EscrowFinancialIntegration` extend the primitive to concurrent escrow IDs, aggregate pending liabilities per asset, and one designated vault-holder inside `FinancialState`. The integrated machine proves exact equality between pending records, vault-holder balance, and its mapped GL subledger for every reachable state, in addition to the existing financial conservation invariants.
- `SIRM.EscrowTimeLocks` wraps the integrated multi-record escrow machine with a strictly monotone discrete `Nat` clock and an immutable per-ID deadline schedule. Opening, release and voluntary cancellation require the deadline to be in the future; after the deadline a separately authorized refund returns funds to the depositor and marks the record `expired`, not `cancelled`. The timed machine preserves the existing reachable holder/supply, vault-balance, pooled-liability and mapped-GL invariants. The clock is abstract: no wall-clock oracle, scheduler liveness, or persisted deadline field is proved.

## Not yet formalized

- Production migration execution: the repository proves a migration-scoped sequential nonce gate, but not a production transaction envelope, operation-wide nonce policy, idempotent response cache, external bridge settlement/finality, custody, rollback/failure execution, asset-collision handling, or production posting/valuation/backing of fractional residual claims. The model proves an authorized source burn paired with destination issuance, exact residual carry-forward and per-principal nonce increment in one abstract transition; it does not execute an external bridge or establish legal/economic backing.
- Proof that a static principal/account control entry corresponds to legal ownership, beneficial entitlement, or actual key possession; production identity enrollment and verification, lifecycle transition rules, key custody, signer thresholds, permission administration, and revocation remain open. Account classes and active/frozen/closed lifecycle labels are represented as descriptive metadata, but their legal meaning and transition policy are not established. The formal control relation is an asserted policy snapshot, not proof of real-world identity or title.
- Cryptographic signature validation, concrete role and threshold policy, freeze/closure rules, and permission-policy administration.
- A canonical finite account universe and concrete genesis assignment covering founder, treasury, validator, ecosystem, community and unallocated pools.
- Production transaction execution remains open: canonical bytes/hash, signer/threshold verification, expiry, fees, deterministic event/error schemas, persisted nonce/receipt storage for remaining failure classes, rollback and crash recovery. `SIRM.ReplayProtectedFinancialMachine`, `SIRM.FinancialTransactionEnvelope`, and `SIRM.FinancialTransactionDenials` specify global nonce, typed success receipts, exact retries, and cached authorization/insufficient-funds denial receipts in Lean, but use unbounded `Nat`, exact typed-value equality, and abstract state transitions; they do not prove a concrete database, runtime serialization, crash durability, or Lean-to-Rust refinement.
- A complete production posting policy for custody, customer-liability, control, and other non-holder general-ledger accounts.
- Wall-clock binding for escrow deadlines, timeout scheduler liveness/automatic invocation, dispute resolution, external settlement finality/evidence, reversals, credit lines and account restrictions. The discrete abstract deadline guards and permissioned expiry refund are formalized; concurrent IDs, pooled obligations and vault/GL reconciliation remain covered by the integrated machine.
- Multi-asset FX, valuation and rounding-residual policies.
- Redemption obligations and their legal/operational preconditions.
- Reserve evidence and external attestations as explicit assumptions with freshness and provenance.
- Governance, validator-set changes, upgrades, rollback and recovery transitions.
- The correspondence between Lean definitions and Rust code.
- Consensus safety, liveness, data availability and privacy proofs.

## Test execution

The pinned workflow explicitly invokes `lake build` and `lake test`. The test driver is a Lean library whose concrete theorem scenarios must compile; it is not a randomized runtime/fuzz harness. Linting is explicitly disabled until a linter driver is configured.

## Assurance rule

No theorem is described as proving more than its exact statement. The holder-supply invariant assumes that the account universe is complete and that each outstanding unit is assigned to exactly one holder/control account. It does not prove legal ownership, private-key custody or external reserves. A later implementation must have a refinement argument; ordinary tests alone do not establish full correspondence.

- The static account-control registry is a general finite many-to-many principal/account relation: a principal may control multiple accounts, and an account may be associated with multiple principals. The relation is a policy input and does not establish real-world ownership or key custody.


- `SIRM.FeeAccounting` defines an authorized fee transfer with explicit payer, beneficiary and fee-collector holder roles. The payer is debited gross base units, the beneficiary receives gross minus fee, and the collector receives the fee. Transfer permission and fee permission are separate witnesses. The combined two-leg journal is balanced and the verified machine preserves holder/supply reconciliation, mapped holder/GL agreement and aggregate signed GL totals. The initial model requires the collector to be in the holder universe; tariff calculation, non-holder revenue classification, production fee policy and runtime execution remain open.


The original single-record escrow primitive remains limited to one record and one dedicated vault holder. Later registry, pooled-reserve and financial-integration layers formalize concurrent IDs and backing; `EscrowTimeLocks` adds discrete deadline gating and an authorized `expired` terminal transition. None of these abstract layers proves a wall-clock source, autonomous scheduler liveness, dispute adjudication, external settlement evidence, persisted idempotent responses or runtime atomicity.
