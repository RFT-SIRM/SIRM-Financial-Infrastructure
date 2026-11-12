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

## Per-principal migration nonce and replay-protection regressions

The `SIRMTests.lean` suite compiles a replay-protected two-step migration and negative nonce cases:

- the first authorized migration is admitted with the initial nonce zero;
- the same principal's next expected nonce advances to one in the very same state as the first migration;
- a second authorized migration is admitted with nonce one and advances the expected nonce to two;
- replaying the old nonce zero after the first step is rejected;
- submitting a future nonce two before nonce one is consumed is rejected;
- another principal's nonce remains unchanged across both transitions;
- the reachable-state theorem preserves the underlying holder/supply, mapped holder/GL, aggregate signed GL, and residual conservation invariants.

The model uses an unbounded Lean `Nat` and scopes sequences to the migration machine. It does not prove global replay protection for every protocol operation, persistent runtime storage, concurrent transaction ordering, signature verification, or idempotent replay responses.

## Global financial operation nonce regressions

The `SIRM.ReplayProtectedFinancialMachine` test driver exercises one shared per-principal nonce across the three operation families admitted by `AuthorizedFinancialStep`: transfer, issue and burn. It checks initial nonce zero, exact-next acceptance, one-step increment, other-principal isolation, stale replay rejection and future-nonce rejection. The reachable-state theorem retains holder/supply reconciliation, mapped holder/GL agreement and aggregate signed-GL conservation.

A finite Python model checker additionally explores every order-preserving interleaving of three operation families for two principals (720 schedules), including cross-family replay attempts. This is a finite nonce-scheduling check, not a Lean proof or a runtime implementation test. The abstract Lean machine records successful admitted transitions only and uses unbounded `Nat`; persistent nonce storage, signature verification, concurrent runtime atomicity, idempotent responses and failed-request nonce policy remain outside scope.

## Transaction-envelope finite model check

`scripts/model_check_transaction_envelope.py` exhaustively checks a small linearized request processor: three distinct requests racing for one principal nonce, exact retries, request-ID/body conflicts, reordered consecutive nonces with fair retries, two-principal isolation, cached authorization denial, and all-or-none write-set patterns. The request-ID receipt is checked before nonce validation; nonce mismatches are not cached; deterministic authorization rejections are cached but do not consume a nonce; successful financial effect, nonce increment, and success receipt are one abstract transition.

The model is finite Python computation, not a Lean theorem, database isolation test, distributed linearizability proof, crash-durability test, or production signature/canonical-encoding implementation. Exact payload equality is modeled with typed tuples only. Detailed scope and calculated counts are in `engineering/transaction_envelope/MODEL_SCOPE.md`.

## Typed financial transaction-envelope regressions

`SIRM.FinancialTransactionEnvelope` adds a typed request payload whose operation constructor fixes every transfer, issue, or burn parameter. The theorem driver compiles a concrete authorized transfer and checks:

- a successful request requires an unused request ID and the principal's exact next nonce;
- successful execution stores the exact typed request and its accepted response under the request ID;
- the response records the accepted nonce and next nonce, and receipt invariants preserve those bindings at every reachable state;
- an exact retry is checked against the stored request before any nonce check, returns the stored response, and leaves financial state, nonce, GL, and receipt cache unchanged;
- reusing an occupied request ID with a different typed payload cannot form a successful transition;
- a second request from the same principal cannot commit at the nonce consumed by the first operation, even when the request ID and operation payload differ;
- a stale/future nonce with a new request ID cannot form a successful transition;
- the reachable envelope machine preserves holder/supply reconciliation, mapped holder/GL agreement, and aggregate signed-GL conservation.

The Lean envelope formalizes successful-operation receipts and exact retry behavior. The follow-on `SIRM.FinancialTransactionDenials` layer now also caches deterministic authorization denials at the exact current nonce, without consuming that nonce or changing financial state. A denial retry returns the original stored response before nonce validation, even after another request ID has subsequently advanced the principal nonce. A separate regression re-instantiates the transition relation with a replacement policy and uses a new request ID at the still-unconsumed nonce. Policy update itself is not a transition in the machine: each verified machine is built with one fixed policy parameter.

The Lean model does not yet define canonical byte encoding or cryptographic payload hashes, prove production persistence, locking/CAS, database isolation, crash durability, or runtime refinement. It caches authorization and insufficient-funds denials; expiry, signature, and other failure classes still need explicit response semantics. Nonce mismatch is a rejected predicate rather than a state-changing transition; an exact receipt replay remains valid even though its nonce is now stale.

## Cached authorization-denial regressions

`SIRMTests.lean` and the processor machine prove a concrete denial path: an unauthorized transfer at the current nonce stores a denial receipt; balances, GL and nonce remain unchanged; a new request ID can succeed at that same nonce when the transition relation is re-instantiated with an updated policy parameter (policy mutation is not modeled as an in-machine state transition); the original request ID continues to return its stored denial after the successful request advances the nonce. The reachable-state invariant preserves the success/denial cache disjointness, denial request-ID binding, expected nonce and operation-family reason tag.

The transition relation deliberately does not cache stale/future nonce mismatches. Other business failures beyond the explicitly modeled insufficient-funds cases remain outside this denial-cache layer.


## Cached insufficient-funds regressions

The `FinancialTransactionDenials` processor also caches insufficient-funds business denials for an authorized transfer whose source differs from its destination and whose source balance is too small, and for an authorized burn whose holder balance is too small. The regression suite checks that:

- the failure is classified only after authorization succeeds;
- self-transfers are not classified as insufficient-funds failures, because the existing transfer relation explicitly permits them without a debit;
- issuance is outside this failure class because it mints units rather than debiting a holder;
- a failure receipt is admitted only at the exact current nonce and an unused request ID;
- balances, GL, and every principal nonce remain unchanged;
- the exact request ID/payload returns the stored `insufficientFundsRejected` response;
- stale/future nonce requests are not cached; and
- the reachable processor invariant continues to preserve financial conservation, receipt consistency, and success/denial cache disjointness.

This is an abstract Lean state-transition model. It does not yet cache expiry, signature, request-format, policy-version, or other failure classes, and it does not establish persistence or runtime atomicity.

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


## Exact fee-accounting regressions

The fee-accounting module and `SIRMTests.lean` compile theorem-level checks for:

- exact gross = net + fee decomposition in integer base units;
- zero-fee and full-fee boundary cases;
- rejection of a fee greater than gross;
- a generic proof that every admitted fee amount decomposes exactly;
- separate ordinary-transfer and fee-authorization witnesses;
- a funded net leg followed by a funded fee leg, with the fee collector credited explicitly;
- one combined balanced journal for the two legs;
- preservation of holder/supply reconciliation, mapped holder/GL agreement and aggregate signed GL totals through the verified fee machine.

These are abstract Lean transition proofs, not a production tariff, percentage calculation, tax treatment, revenue-recognition policy, runtime transaction processor or Rust implementation. The collector is a holder in this first model.


## Authorized escrow accounting regressions

The escrow regressions compile the authorized single-record deposit/release/cancel lifecycle and the financially integrated two-ID pooled-vault lifecycle. They check exact balances and GL postings, unchanged supply, aggregate pending liabilities, vault/GL/pool equality, reachable-state invariants and terminal-ID non-reuse. Discrete expiry and deadline guards are covered separately by `SIRM.EscrowTimeLocks`; wall-clock binding, automatic scheduler liveness, disputes and external settlement finality remain open.

## Escrow expiry and time-lock regressions

The timed fixture assigns the two pending escrow IDs distinct absolute deadlines (10 and 5) over an abstract `Nat` clock. It opens both records before their deadlines, advances time monotonically to the second deadline, and proves that release and voluntary cancellation are no longer admissible for that ID. Expiry is a separate permissioned refund: it requires the dedicated `mayExpireEscrow` policy witness, returns the selected 25 units to the depositor, and marks that record `expired` rather than `cancelled`. The other 40-unit record remains pending; the reachable-state theorem proves the remaining vault-holder balance, mapped vault GL subledger and pooled pending liability all equal 40. A negative regression shows that the ordinary cancellation permission alone does not authorize expiry.

This is a discrete abstract-time safety specification. It does not bind `Nat` to a wall clock, prove an external scheduler will invoke expiry, persist deadline terms inside the escrow record, or prove runtime atomicity.
