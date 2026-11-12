import SIRM.ReplayProtectedFinancialMachine

/-!
# Typed Financial Transaction Envelope

This layer binds a request identifier and an exact typed financial operation
payload to the existing replay-protected financial machine. It specifies
successful requests and exact retries in one abstract transition relation.

The receipt lookup is logically prior to nonce validation: an exact retry of
an already committed request returns its stored response even though its nonce
is now stale. Reusing an occupied request ID with another payload is a
conflict. A new request can commit only at the principal's exact next nonce.
The successful financial transition, nonce increment, and receipt insertion
are one abstract state update.

This is a Lean state-transition specification. It does not prove database
isolation, compare-and-swap, crash durability, cryptographic request hashing,
signatures, or a concrete runtime implementation. Rejected authorization
responses and their caching policy are not yet included in this layer.
-/

namespace SIRM

/-- The typed business operation carried by a financial request. -/
inductive FinancialOperation (Holder Asset : Type)
  | transfer (source destination : Holder) (asset : Asset) (amount : Nat)
  | issue (issuer recipient : Holder) (asset : Asset) (amount : Nat)
  | burn (holder : Holder) (asset : Asset) (amount : Nat)
  deriving DecidableEq

/-- Exact typed request payload; the request ID is supplied separately. -/
structure FinancialTransactionRequest (Principal Holder Asset : Type) where
  principal : Principal
  nonce : Nat
  operation : FinancialOperation Holder Asset
  deriving DecidableEq

/-- Deterministic response metadata stored for one accepted request. -/
structure FinancialTransactionResponse (RequestId : Type) where
  requestId : RequestId
  acceptedNonce : Nat
  nextNonce : Nat
  deriving DecidableEq

/-- The receipt binds the exact request payload to the response we return. -/
structure FinancialTransactionReceipt
    (RequestId Principal Holder Asset : Type) where
  request : FinancialTransactionRequest Principal Holder Asset
  response : FinancialTransactionResponse RequestId
  deriving DecidableEq

/-- Construct the response associated with a successful request. -/
def acceptedFinancialTransactionResponse
    {RequestId Principal Holder Asset : Type}
    (requestId : RequestId)
    (request : FinancialTransactionRequest Principal Holder Asset) :
    FinancialTransactionResponse RequestId :=
  { requestId := requestId
    acceptedNonce := request.nonce
    nextNonce := request.nonce + 1 }

/-- The immutable receipt produced by a successful request. -/
def acceptedFinancialTransactionReceipt
    {RequestId Principal Holder Asset : Type}
    (requestId : RequestId)
    (request : FinancialTransactionRequest Principal Holder Asset) :
    FinancialTransactionReceipt RequestId Principal Holder Asset :=
  { request := request
    response := acceptedFinancialTransactionResponse requestId request }

/-- The replay-protected financial state and an ID-indexed receipt cache. -/
structure FinancialTransactionEnvelopeState
    (RequestId Principal Holder LedgerAccount Asset : Type) where
  core : ReplayProtectedFinancialState Principal Holder LedgerAccount Asset
  receipts : RequestId →
    Option (FinancialTransactionReceipt RequestId Principal Holder Asset)

/-- Initial envelope state: all principals start at nonce zero; no ID is occupied. -/
def initialFinancialTransactionEnvelopeState
    (RequestId Principal : Type)
    {Holder LedgerAccount Asset : Type}
    (initialFinancial : FinancialState Holder LedgerAccount Asset) :
    FinancialTransactionEnvelopeState RequestId Principal Holder LedgerAccount Asset :=
  { core := initialReplayProtectedFinancialState Principal initialFinancial
    receipts := fun _ => none }

/--
The transition relation for one specifically tagged operation. Unlike the
existential `AuthorizedFinancialStep`, the operation constructor fixes every
business parameter in the request payload.
-/
def FinancialOperationStep
    {Principal Holder LedgerAccount Asset : Type}
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (principal : Principal)
    (operation : FinancialOperation Holder Asset)
    (before after : FinancialState Holder LedgerAccount Asset) : Prop :=
  match operation with
  | .transfer source destination asset amount =>
      ∃ (hAuthorized :
          policy.mayTransfer before.holdings principal
            source destination asset amount),
        ∃ (hAllowed :
          TransferAllowed before.holdings source destination asset amount),
          after =
            { holdings := executeAuthorizedTransfer policy before.holdings
                principal source destination asset amount hAuthorized hAllowed
              ledger := postJournal before.ledger
                (holderTransferJournal mapping source destination asset amount) }
  | .issue issuer recipient asset amount =>
      ∃ (hAuthorized :
          policy.mayIssue before.holdings principal issuer recipient asset amount),
        ∃ (hCounterpart :
          ∀ holder, counterpart ≠ mapping.ledgerAccount holder),
          after =
            { holdings := executeAuthorizedIssue policy before.holdings
                principal issuer recipient asset amount hAuthorized
              ledger := postJournal before.ledger
                (holderIssuanceJournal mapping counterpart recipient asset amount) }
  | .burn holder asset amount =>
      ∃ (hAuthorized :
          policy.mayBurn before.holdings principal holder asset amount),
        ∃ (hEnough : (amount : Int) ≤ before.holdings.balance holder asset),
        ∃ (hCounterpart :
          ∀ mappedHolder, counterpart ≠ mapping.ledgerAccount mappedHolder),
          after =
            { holdings := executeAuthorizedBurn policy before.holdings
                principal holder asset amount hAuthorized hEnough
              ledger := postJournal before.ledger
                (holderBurnJournal mapping counterpart holder asset amount) }

/-- Every tagged operation is one of the existing authorized financial steps. -/
theorem financialOperationStep_toAuthorizedFinancialStep
    {Principal Holder LedgerAccount Asset : Type}
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (principal : Principal)
    (operation : FinancialOperation Holder Asset)
    {before after : FinancialState Holder LedgerAccount Asset}
    (hOperation : FinancialOperationStep policy mapping counterpart
      principal operation before after) :
    AuthorizedFinancialStep policy mapping counterpart before after := by
  cases operation with
  | transfer source destination asset amount =>
      rcases hOperation with ⟨hAuthorized, hAllowed, hAfter⟩
      exact Or.inl ⟨principal, source, destination, asset, amount,
        hAuthorized, hAllowed, hAfter⟩
  | issue issuer recipient asset amount =>
      rcases hOperation with ⟨hAuthorized, hCounterpart, hAfter⟩
      exact Or.inr (Or.inl ⟨principal, issuer, recipient, asset, amount,
        hAuthorized, hCounterpart, hAfter⟩)
  | burn holder asset amount =>
      rcases hOperation with ⟨hAuthorized, hEnough, hCounterpart, hAfter⟩
      exact Or.inr (Or.inr ⟨principal, holder, asset, amount,
        hAuthorized, hEnough, hCounterpart, hAfter⟩)

/-- Apply one accepted request, updating core state and receipt cache together. -/
def applyFinancialTransactionSuccess
    (Principal RequestId : Type)
    [DecidableEq Principal] [DecidableEq RequestId]
    {Holder LedgerAccount Asset : Type}
    (before : FinancialTransactionEnvelopeState
      RequestId Principal Holder LedgerAccount Asset)
    (requestId : RequestId)
    (request : FinancialTransactionRequest Principal Holder Asset)
    (financialAfter : FinancialState Holder LedgerAccount Asset) :
    FinancialTransactionEnvelopeState RequestId Principal Holder LedgerAccount Asset :=
  { core := applyReplayProtectedFinancialStep Principal before.core
      request.principal request.nonce financialAfter
    receipts := fun candidate =>
      if candidate = requestId then
        some (acceptedFinancialTransactionReceipt requestId request)
      else before.receipts candidate }

/-- A new request succeeds only when its ID is unused and its nonce is exact. -/
def FinancialTransactionEnvelopeSuccessStep
    {RequestId Principal Holder LedgerAccount Asset : Type}
    [DecidableEq RequestId] [DecidableEq Principal]
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (requestId : RequestId)
    (request : FinancialTransactionRequest Principal Holder Asset)
    (before after : FinancialTransactionEnvelopeState
      RequestId Principal Holder LedgerAccount Asset) : Prop :=
  before.receipts requestId = none ∧
    request.nonce = before.core.nextNonce request.principal ∧
    ∃ financialAfter,
      FinancialOperationStep policy mapping counterpart request.principal
        request.operation before.core.financial financialAfter ∧
      after = applyFinancialTransactionSuccess Principal RequestId before
        requestId request financialAfter

/--
An exact retry is accepted by receipt lookup before nonce validation and is a
strict no-op on protocol state. The receipt contains the response to return.
-/
def FinancialTransactionEnvelopeReplayStep
    {RequestId Principal Holder LedgerAccount Asset : Type}
    (requestId : RequestId)
    (request : FinancialTransactionRequest Principal Holder Asset)
    (before after : FinancialTransactionEnvelopeState
      RequestId Principal Holder LedgerAccount Asset) : Prop :=
  ∃ receipt,
    before.receipts requestId = some receipt ∧
    receipt.response.requestId = requestId ∧
    receipt.request = request ∧
    after = before

/-- An occupied request ID cannot be rebound to a different typed payload. -/
def FinancialTransactionRequestIdConflict
    {RequestId Principal Holder LedgerAccount Asset : Type}
    (state : FinancialTransactionEnvelopeState
      RequestId Principal Holder LedgerAccount Asset)
    (requestId : RequestId)
    (request : FinancialTransactionRequest Principal Holder Asset) : Prop :=
  ∃ receipt,
    state.receipts requestId = some receipt ∧
    receipt.request ≠ request

/-- Cache lookup returns a response only for an exact request-payload match. -/
def cachedFinancialTransactionResponse
    {RequestId Principal Holder LedgerAccount Asset : Type}
    [DecidableEq RequestId] [DecidableEq Principal]
    [DecidableEq Holder] [DecidableEq Asset]
    (state : FinancialTransactionEnvelopeState
      RequestId Principal Holder LedgerAccount Asset)
    (requestId : RequestId)
    (request : FinancialTransactionRequest Principal Holder Asset) :
    Option (FinancialTransactionResponse RequestId) :=
  match state.receipts requestId with
  | none => none
  | some receipt =>
      if receipt.response.requestId = requestId ∧ receipt.request = request
      then some receipt.response else none

/-- The receipt-first exact retry returns the stored response, unchanged. -/
theorem financialTransactionEnvelopeReplay_returns_cached_response
    {RequestId Principal Holder LedgerAccount Asset : Type}
    [DecidableEq RequestId] [DecidableEq Principal]
    [DecidableEq Holder] [DecidableEq Asset]
    (before after : FinancialTransactionEnvelopeState
      RequestId Principal Holder LedgerAccount Asset)
    (requestId : RequestId)
    (request : FinancialTransactionRequest Principal Holder Asset)
    (hReplay : FinancialTransactionEnvelopeReplayStep
      requestId request before after) :
    ∃ receipt,
      before.receipts requestId = some receipt ∧
      receipt.response.requestId = requestId ∧
      receipt.request = request ∧
      cachedFinancialTransactionResponse before requestId request =
        some receipt.response := by
  rcases hReplay with ⟨receipt, hStored, hResponseId, hSame, _hNoChange⟩
  refine ⟨receipt, hStored, hResponseId, hSame, ?_⟩
  simp [cachedFinancialTransactionResponse, hStored, hResponseId, hSame]

/-- Exact replay cannot change balances, nonce, ledger, or any receipt. -/
theorem financialTransactionEnvelopeReplay_state_unchanged
    {RequestId Principal Holder LedgerAccount Asset : Type}
    (before after : FinancialTransactionEnvelopeState
      RequestId Principal Holder LedgerAccount Asset)
    (requestId : RequestId)
    (request : FinancialTransactionRequest Principal Holder Asset)
    (hReplay : FinancialTransactionEnvelopeReplayStep
      requestId request before after) :
    after = before := by
  rcases hReplay with ⟨_receipt, _hStored, _hResponseId, _hSame, hNoChange⟩
  exact hNoChange

/-- Every accepted new request writes the exact request/response receipt. -/
theorem financialTransactionEnvelopeSuccess_stores_receipt
    {RequestId Principal Holder LedgerAccount Asset : Type}
    [DecidableEq RequestId] [DecidableEq Principal]
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (requestId : RequestId)
    (request : FinancialTransactionRequest Principal Holder Asset)
    {before after : FinancialTransactionEnvelopeState
      RequestId Principal Holder LedgerAccount Asset}
    (hSuccess : FinancialTransactionEnvelopeSuccessStep
      policy mapping counterpart requestId request before after) :
    after.receipts requestId =
      some (acceptedFinancialTransactionReceipt requestId request) := by
  rcases hSuccess with ⟨_hUnused, _hNonce, financialAfter, _hOperation, rfl⟩
  simp [applyFinancialTransactionSuccess]

/-- An accepted request increments exactly its selected principal's nonce. -/
theorem financialTransactionEnvelopeSuccess_advances_nonce
    {RequestId Principal Holder LedgerAccount Asset : Type}
    [DecidableEq RequestId] [DecidableEq Principal]
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (requestId : RequestId)
    (request : FinancialTransactionRequest Principal Holder Asset)
    {before after : FinancialTransactionEnvelopeState
      RequestId Principal Holder LedgerAccount Asset}
    (hSuccess : FinancialTransactionEnvelopeSuccessStep
      policy mapping counterpart requestId request before after) :
    after.core.nextNonce request.principal = request.nonce + 1 := by
  rcases hSuccess with ⟨_hUnused, _hNonce, financialAfter, _hOperation, rfl⟩
  simp [applyFinancialTransactionSuccess, applyReplayProtectedFinancialStep]

/--
After one request commits, a different request by the same principal cannot
also commit at that nonce, regardless of operation family or request ID.
This is the sequential-state form of the same-nonce race winner property.
-/
theorem financialTransactionEnvelopeSuccess_rejects_same_nonce_competitor
    {RequestId Principal Holder LedgerAccount Asset : Type}
    [DecidableEq RequestId] [DecidableEq Principal]
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (firstRequestId secondRequestId : RequestId)
    (firstRequest secondRequest : FinancialTransactionRequest Principal Holder Asset)
    (before after afterSecond : FinancialTransactionEnvelopeState
      RequestId Principal Holder LedgerAccount Asset)
    (hFirst : FinancialTransactionEnvelopeSuccessStep
      policy mapping counterpart firstRequestId firstRequest before after)
    (hSamePrincipal : secondRequest.principal = firstRequest.principal)
    (hSameNonce : secondRequest.nonce = firstRequest.nonce) :
    ¬ FinancialTransactionEnvelopeSuccessStep
      policy mapping counterpart secondRequestId secondRequest after afterSecond := by
  have hNext := financialTransactionEnvelopeSuccess_advances_nonce
    policy mapping counterpart firstRequestId firstRequest hFirst
  have hMismatch : secondRequest.nonce ≠ after.core.nextNonce secondRequest.principal := by
    rw [hSamePrincipal, hNext, hSameNonce]
    exact Nat.ne_of_lt (Nat.lt_succ_self firstRequest.nonce)
  intro hSecond
  exact hMismatch hSecond.2.1

/-- An accepted request leaves every other principal's nonce unchanged. -/
theorem financialTransactionEnvelopeSuccess_other_nonce
    {RequestId Principal Holder LedgerAccount Asset : Type}
    [DecidableEq RequestId] [DecidableEq Principal]
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (requestId : RequestId)
    (request : FinancialTransactionRequest Principal Holder Asset)
    (other : Principal)
    {before after : FinancialTransactionEnvelopeState
      RequestId Principal Holder LedgerAccount Asset}
    (hSuccess : FinancialTransactionEnvelopeSuccessStep
      policy mapping counterpart requestId request before after)
    (hOther : other ≠ request.principal) :
    after.core.nextNonce other = before.core.nextNonce other := by
  rcases hSuccess with ⟨_hUnused, _hNonce, financialAfter, _hOperation, rfl⟩
  simp [applyFinancialTransactionSuccess, applyReplayProtectedFinancialStep, hOther]

/-- An occupied request ID blocks a success with a different request payload. -/
theorem financialTransactionEnvelopeConflict_rejects_success
    {RequestId Principal Holder LedgerAccount Asset : Type}
    [DecidableEq RequestId] [DecidableEq Principal]
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (requestId : RequestId)
    (request : FinancialTransactionRequest Principal Holder Asset)
    (before after : FinancialTransactionEnvelopeState
      RequestId Principal Holder LedgerAccount Asset)
    (hConflict : FinancialTransactionRequestIdConflict before requestId request) :
    ¬ FinancialTransactionEnvelopeSuccessStep
      policy mapping counterpart requestId request before after := by
  intro hSuccess
  rcases hConflict with ⟨receipt, hStored, _hDifferent⟩
  rw [hSuccess.1] at hStored
  cases hStored

/-- A stale/future nonce cannot be admitted as a new successful request. -/
theorem financialTransactionEnvelopeNonceMismatch_rejects_success
    {RequestId Principal Holder LedgerAccount Asset : Type}
    [DecidableEq RequestId] [DecidableEq Principal]
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (requestId : RequestId)
    (request : FinancialTransactionRequest Principal Holder Asset)
    (before after : FinancialTransactionEnvelopeState
      RequestId Principal Holder LedgerAccount Asset)
    (hMismatch : request.nonce ≠ before.core.nextNonce request.principal) :
    ¬ FinancialTransactionEnvelopeSuccessStep
      policy mapping counterpart requestId request before after := by
  intro hSuccess
  exact hMismatch hSuccess.2.1

/-- A successful update preserves all receipts at IDs other than its own. -/
theorem financialTransactionEnvelopeSuccess_other_receipt_unchanged
    {RequestId Principal Holder LedgerAccount Asset : Type}
    [DecidableEq RequestId] [DecidableEq Principal]
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (requestId otherId : RequestId)
    (request : FinancialTransactionRequest Principal Holder Asset)
    {before after : FinancialTransactionEnvelopeState
      RequestId Principal Holder LedgerAccount Asset}
    (hSuccess : FinancialTransactionEnvelopeSuccessStep
      policy mapping counterpart requestId request before after)
    (hOther : otherId ≠ requestId) :
    after.receipts otherId = before.receipts otherId := by
  rcases hSuccess with ⟨_hUnused, _hNonce, financialAfter, _hOperation, rfl⟩
  simp [applyFinancialTransactionSuccess, hOther]

/-- Every stored receipt is keyed by its request ID and records its nonce result. -/
def FinancialTransactionReceiptInvariant
    {RequestId Principal Holder LedgerAccount Asset : Type}
    (state : FinancialTransactionEnvelopeState
      RequestId Principal Holder LedgerAccount Asset) : Prop :=
  ∀ requestId receipt, state.receipts requestId = some receipt →
    receipt.response.requestId = requestId ∧
    receipt.response.acceptedNonce = receipt.request.nonce ∧
    receipt.response.nextNonce = receipt.request.nonce + 1

/-- Inserting one successful receipt preserves the validity of the whole cache. -/
theorem applyFinancialTransactionSuccess_preserves_receipt_invariant
    {RequestId Principal Holder LedgerAccount Asset : Type}
    [DecidableEq RequestId] [DecidableEq Principal]
    (before : FinancialTransactionEnvelopeState
      RequestId Principal Holder LedgerAccount Asset)
    (requestId : RequestId)
    (request : FinancialTransactionRequest Principal Holder Asset)
    (financialAfter : FinancialState Holder LedgerAccount Asset)
    (hBefore : FinancialTransactionReceiptInvariant before) :
    FinancialTransactionReceiptInvariant
      (applyFinancialTransactionSuccess Principal RequestId before
        requestId request financialAfter) := by
  intro queryId receipt hFound
  by_cases hTarget : queryId = requestId
  · subst queryId
    have hNew :
        some (acceptedFinancialTransactionReceipt requestId request) = some receipt := by
      simpa [applyFinancialTransactionSuccess] using hFound
    have hReceipt :
        acceptedFinancialTransactionReceipt requestId request = receipt :=
      Option.some.inj hNew
    subst receipt
    simp [acceptedFinancialTransactionReceipt,
      acceptedFinancialTransactionResponse]
  · have hOld : before.receipts queryId = some receipt := by
      simpa [applyFinancialTransactionSuccess, hTarget] using hFound
    exact hBefore queryId receipt hOld

/-- The envelope invariant includes both financial conservation and receipt consistency. -/
def FinancialTransactionEnvelopeInvariant
    {RequestId Principal Holder LedgerAccount Asset : Type}
    [Fintype Holder] [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (openingLedger : Ledger LedgerAccount Asset)
    (state : FinancialTransactionEnvelopeState
      RequestId Principal Holder LedgerAccount Asset) : Prop :=
  FinancialConservationInvariant mapping openingLedger state.core.financial ∧
    FinancialTransactionReceiptInvariant state

/-- Only successful new requests and exact retries are state-machine transitions. -/
def FinancialTransactionEnvelopeStep
    {RequestId Principal Holder LedgerAccount Asset : Type}
    [DecidableEq RequestId] [DecidableEq Principal]
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (before after : FinancialTransactionEnvelopeState
      RequestId Principal Holder LedgerAccount Asset) : Prop :=
  (∃ requestId request,
    FinancialTransactionEnvelopeSuccessStep policy mapping counterpart
      requestId request before after) ∨
  (∃ requestId request,
    FinancialTransactionEnvelopeReplayStep requestId request before after)

/-- Verified machine for typed successful requests and exact idempotent retries. -/
def financialTransactionEnvelopeMachine
    {RequestId Principal Holder LedgerAccount Asset : Type}
    [DecidableEq RequestId] [DecidableEq Principal]
    [Fintype Holder] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (initialFinancial : FinancialState Holder LedgerAccount Asset)
    (hInitial : FinancialInvariant mapping initialFinancial) :
    VerifiedStateMachine
      (FinancialTransactionEnvelopeState RequestId Principal Holder LedgerAccount Asset) where
  invariant := FinancialTransactionEnvelopeInvariant mapping initialFinancial.ledger
  initial := fun state =>
    state = initialFinancialTransactionEnvelopeState
      RequestId Principal initialFinancial
  step := FinancialTransactionEnvelopeStep policy mapping counterpart
  initial_safe := by
    intro state hState
    subst state
    constructor
    · exact ⟨hInitial, by intro asset; rfl⟩
    · intro requestId receipt hReceipt
      have hImpossible : False := by
        simpa [initialFinancialTransactionEnvelopeState] using hReceipt
      exact hImpossible.elim
  step_safe := by
    intro before after hBefore hStep
    rcases hStep with hSuccess | hReplay
    · rcases hSuccess with ⟨requestId, request, hAccepted⟩
      rcases hAccepted with
        ⟨_hUnused, _hNonce, financialAfter, hOperation, hAfter⟩
      subst after
      constructor
      · exact authorizedFinancialStep_preserves_conservation
          policy mapping counterpart initialFinancial.ledger hBefore.1
          (financialOperationStep_toAuthorizedFinancialStep
            policy mapping counterpart request.principal request.operation hOperation)
      · exact applyFinancialTransactionSuccess_preserves_receipt_invariant
          before requestId request financialAfter hBefore.2
    · rcases hReplay with ⟨requestId, request, hExactReplay⟩
      rcases hExactReplay with ⟨_receipt, _hStored, _hResponseId, _hSame, rfl⟩
      exact hBefore

/-- Every reachable envelope state retains the full holder/GL conservation invariant. -/
theorem financialTransactionEnvelopeInvariant_of_reachable
    {RequestId Principal Holder LedgerAccount Asset : Type}
    [DecidableEq RequestId] [DecidableEq Principal]
    [Fintype Holder] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (initialFinancial : FinancialState Holder LedgerAccount Asset)
    (hInitial : FinancialInvariant mapping initialFinancial)
    {state : FinancialTransactionEnvelopeState
      RequestId Principal Holder LedgerAccount Asset}
    (hReachable : Reachable
      (financialTransactionEnvelopeMachine policy mapping counterpart
        initialFinancial hInitial) state) :
    FinancialTransactionEnvelopeInvariant mapping initialFinancial.ledger state := by
  exact invariant_of_reachable
    (financialTransactionEnvelopeMachine policy mapping counterpart
      initialFinancial hInitial) hReachable

end SIRM
