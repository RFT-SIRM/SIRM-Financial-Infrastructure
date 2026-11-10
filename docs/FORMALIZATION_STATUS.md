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

- A finite static account-control relation, independent of authority grants, represented by principal/account pairs. The combined policy requires control of the source for transfers, the issuer for issuance, and the holder for burns, together with an exact grant. Issue grants bind both issuer and recipient; recipient control is not required by this model.
- A registry-backed authorization adapter and regression theorems for denial when control is absent, denial when the exact grant is absent, and an allowed Treasury-to-Alice issuance where Treasury controls the issuer account but not Alice's recipient account. The holder operation remains mint-to-recipient and does not debit the issuer.

## Not yet formalized

- End-to-end migration execution: source burn/redemption, destination issuance, authority and custody evidence, replay/idempotency, asset-collision policy, bridge finality, and failure/rollback semantics. The current migration module proves arithmetic and route eligibility only; it does not implement a production bridge transaction.
- Proof that a static principal/account control entry corresponds to legal ownership, beneficial entitlement, or actual key possession; production identity enrollment and verification, lifecycle transition rules, key custody, signer thresholds, permission administration, and revocation remain open. Account classes and active/frozen/closed lifecycle labels are represented as descriptive metadata, but their legal meaning and transition policy are not established. The formal control relation is an asserted policy snapshot, not proof of real-world identity or title.
- Cryptographic signature validation, concrete role and threshold policy, freeze/closure rules, and permission-policy administration.
- A canonical finite account universe and concrete genesis assignment covering founder, treasury, validator, ecosystem, community and unallocated pools.
- A unified transaction object with signer rules, nonce, expiry, replay prevention, fees and atomic failure semantics.
- A complete production posting policy for custody, customer-liability, control, and other non-holder general-ledger accounts.
- Freeze, escrow, fees, settlement, reversals, credit lines and account restrictions.
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
