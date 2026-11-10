# Mathematical Scope and Assurance Boundaries

## Lean modules in this branch

- `SIRM.FinancialCore`: the supply-state equation; initial state; mint and burn transitions with invariant-preservation theorems; exact 1.309% founder-rate arithmetic; genesis allocation and unallocated remainder.
- `SIRM.Accounting`: a generic finite-account, per-asset signed general ledger; journal entries carrying a balance proof per asset; aggregate signed-balance preservation for balanced entries; and a balanced transfer-journal constructor.
- `SIRM.Holdings`: nonnegative integer holder balances indexed by account and asset; exact per-asset reconciliation with outstanding supply; funded transfers; issuance to a holder; and holder-bounded burns with preservation theorems.
- `SIRM.StateMachine`: a generic reachable-state theorem deriving safety from initial-state and transition-preservation obligations.
- `SIRM.AuthorizedStateMachine`: an authorization-gated holder transition relation, an invariant initial state, and a theorem that every reachable state preserves holdings/supply reconciliation.
- `SIRM.AuthorizedFinancialMachine`: one combined state containing holder balances and the signed GL; authorized transfer, issuance and burn steps update both projections together. Its stronger machine invariant preserves holder reconciliation, mapped subledger agreement and aggregate signed GL balance relative to the opening ledger.
- `SIRM.HolderAccountingBridge`: matching balanced general-ledger journals for holder transfers, issuance and burn; pointwise subledger-agreement preservation for all three operations under an unmapped counterpart-account assumption.

## Not proved by these declarations

- Completeness or legal correctness of the account universe; it is an explicit assumption of the holdings reconciliation statement.
- A concrete principal-to-account ownership map, cryptographic signatures, key custody, roles, signer thresholds or a production authorization policy; the authorization predicates are abstract policy inputs.
- A complete genesis assignment to real founder, treasury, validator and other accounts.
- A unified posting transaction that atomically updates holder balances and the signed general ledger.
- Reserve backing, solvency, par redemption or external asset existence.
- A particular global-field distribution law or an equivalence to the legacy Rift implementation.
- Rust/Lean refinement, consensus safety/finality, censorship resistance or data availability.
- Privacy guarantees, legal enforceability, licensing or regulatory compliance.

## Assurance rule

A theorem applies only to its formal statement and assumptions. Lean source is described as kernel-checked only after the pinned `lake build SIRM` succeeds. Implementation and network claims require separate refinement proofs, tests, audits and operational evidence.
