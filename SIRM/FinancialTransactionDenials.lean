import SIRM.FinancialTransactionEnvelope

/-!
# Cached Authorization Denials for the Financial Transaction Processor

This layer extends the successful-request envelope with a disjoint cache for
deterministic authorization rejections. Receipt lookup remains first: an exact
retry returns the previously stored success or denial, regardless of the
principal's current nonce.

A new authorization denial is recorded only at the exact current nonce and
only for an unused request ID. It leaves the financial state and nonce
unchanged. A later attempt after a policy change may use a new request ID and
the same nonce. Reusing the denied request ID continues to replay the original
denial.

The model covers authorization denials only. It does not yet assign cached
responses to insufficient-funds, expiry, signature, or other failure classes.
-/

namespace SIRM

/-- Stable Lean-level reason codes for authorization denials by operation family. -/
inductive FinancialTransactionDenialReason
  | transferAuthorizationDenied
  | issueAuthorizationDenied
  | burnAuthorizationDenied
  deriving DecidableEq, Repr

/-- A deterministic authorization-denial response; no nonce is consumed. -/
structure FinancialTransactionDenialResponse (RequestId : Type) where
  requestId : RequestId
  expectedNonce : Nat
  reason : FinancialTransactionDenialReason
  deriving DecidableEq

/-- A denial receipt binds the exact rejected request to its stored response. -/
structure FinancialTransactionDenialReceipt
    (RequestId Principal Holder Asset : Type) where
  request : FinancialTransactionRequest Principal Holder Asset
  response : FinancialTransactionDenialResponse RequestId
  deriving DecidableEq

/-- The success and authorization-denial caches share one request-ID namespace. -/
structure FinancialTransactionProcessorState
    (RequestId Principal Holder LedgerAccount Asset : Type) where
  envelope : FinancialTransactionEnvelopeState
    RequestId Principal Holder LedgerAccount Asset
  denials : RequestId →
    Option (FinancialTransactionDenialReceipt RequestId Principal Holder Asset)

/-- Initial processor state: zero nonces and both receipt caches empty. -/
def initialFinancialTransactionProcessorState
    (RequestId Principal : Type)
    {Holder LedgerAccount Asset : Type}
    (initialFinancial : FinancialState Holder LedgerAccount Asset) :
    FinancialTransactionProcessorState
      RequestId Principal Holder LedgerAccount Asset :=
  { envelope := initialFinancialTransactionEnvelopeState
      RequestId Principal initialFinancial
    denials := fun _ => none }

/-- The response recorded for one deterministic authorization denial. -/
def financialTransactionAuthorizationDenialReceipt
    {RequestId Principal Holder Asset : Type}
    (requestId : RequestId)
    (request : FinancialTransactionRequest Principal Holder Asset)
    (reason : FinancialTransactionDenialReason) :
    FinancialTransactionDenialReceipt RequestId Principal Holder Asset :=
  { request := request
    response :=
      { requestId := requestId
        expectedNonce := request.nonce
        reason := reason } }

/-- Insert a denial receipt without changing the successful envelope state. -/
def applyFinancialTransactionAuthorizationDenial
    [DecidableEq RequestId]
    {RequestId Principal Holder LedgerAccount Asset : Type}
    (before : FinancialTransactionProcessorState
      RequestId Principal Holder LedgerAccount Asset)
    (requestId : RequestId)
    (request : FinancialTransactionRequest Principal Holder Asset)
    (reason : FinancialTransactionDenialReason) :
    FinancialTransactionProcessorState
      RequestId Principal Holder LedgerAccount Asset :=
  { before with
    denials := fun candidate =>
      if candidate = requestId then
        some (financialTransactionAuthorizationDenialReceipt
          requestId request reason)
      else before.denials candidate }

/-- The denial reason must match the operation family carried by the request. -/
def FinancialTransactionDenialReasonMatchesRequest
    {Principal Holder Asset : Type}
    (request : FinancialTransactionRequest Principal Holder Asset)
    (reason : FinancialTransactionDenialReason) : Prop :=
  match request.operation with
  | .transfer _ _ _ _ => reason = .transferAuthorizationDenied
  | .issue _ _ _ _ => reason = .issueAuthorizationDenied
  | .burn _ _ _ => reason = .burnAuthorizationDenied

/-- Evidence that the current authorization policy rejects this exact request. -/
def FinancialTransactionAuthorizationDenial
    {Principal Holder LedgerAccount Asset : Type}
    (policy : AuthorizationPolicy Principal Holder Asset)
    (request : FinancialTransactionRequest Principal Holder Asset)
    (financial : FinancialState Holder LedgerAccount Asset)
    (reason : FinancialTransactionDenialReason) : Prop :=
  match request.operation with
  | .transfer source destination asset amount =>
      reason = .transferAuthorizationDenied ∧
        ¬ policy.mayTransfer financial.holdings request.principal
          source destination asset amount
  | .issue issuer recipient asset amount =>
      reason = .issueAuthorizationDenied ∧
        ¬ policy.mayIssue financial.holdings request.principal
          issuer recipient asset amount
  | .burn holder asset amount =>
      reason = .burnAuthorizationDenied ∧
        ¬ policy.mayBurn financial.holdings request.principal
          holder asset amount

/-- A denial is cacheable only for an unused ID and the exact current nonce. -/
def FinancialTransactionAuthorizationDenialStep
    [DecidableEq RequestId]
    {RequestId Principal Holder LedgerAccount Asset : Type}
    (policy : AuthorizationPolicy Principal Holder Asset)
    (requestId : RequestId)
    (request : FinancialTransactionRequest Principal Holder Asset)
    (reason : FinancialTransactionDenialReason)
    (before after : FinancialTransactionProcessorState
      RequestId Principal Holder LedgerAccount Asset) : Prop :=
  before.envelope.receipts requestId = none ∧
    before.denials requestId = none ∧
    request.nonce = before.envelope.core.nextNonce request.principal ∧
    FinancialTransactionAuthorizationDenial policy request
      before.envelope.core.financial reason ∧
    after = applyFinancialTransactionAuthorizationDenial
      before requestId request reason

/-- A successful request may not reuse an ID occupied by a cached denial. -/
def FinancialTransactionProcessorSuccessStep
    {RequestId Principal Holder LedgerAccount Asset : Type}
    [DecidableEq RequestId] [DecidableEq Principal]
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (requestId : RequestId)
    (request : FinancialTransactionRequest Principal Holder Asset)
    (before after : FinancialTransactionProcessorState
      RequestId Principal Holder LedgerAccount Asset) : Prop :=
  before.denials requestId = none ∧
    FinancialTransactionEnvelopeSuccessStep policy mapping counterpart
      requestId request before.envelope after.envelope ∧
    after.denials = before.denials

/-- An exact retry replays either the accepted response or the cached denial. -/
def FinancialTransactionProcessorReplayStep
    {RequestId Principal Holder LedgerAccount Asset : Type}
    (requestId : RequestId)
    (request : FinancialTransactionRequest Principal Holder Asset)
    (before after : FinancialTransactionProcessorState
      RequestId Principal Holder LedgerAccount Asset) : Prop :=
  (∃ receipt,
    before.envelope.receipts requestId = some receipt ∧
    receipt.response.requestId = requestId ∧
    receipt.request = request ∧
    after = before) ∨
  (∃ receipt,
    before.denials requestId = some receipt ∧
    receipt.response.requestId = requestId ∧
    receipt.request = request ∧
    after = before)

/-- All admitted processor transitions: success, cached denial, or exact replay. -/
def FinancialTransactionProcessorStep
    {RequestId Principal Holder LedgerAccount Asset : Type}
    [DecidableEq RequestId] [DecidableEq Principal]
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (before after : FinancialTransactionProcessorState
      RequestId Principal Holder LedgerAccount Asset) : Prop :=
  (∃ requestId request,
    FinancialTransactionProcessorSuccessStep policy mapping counterpart
      requestId request before after) ∨
  (∃ requestId request reason,
    FinancialTransactionAuthorizationDenialStep policy
      requestId request reason before after) ∨
  (∃ requestId request,
    FinancialTransactionProcessorReplayStep requestId request before after)

/-- Every denial receipt is keyed by its request ID and preserves the expected nonce. -/
def FinancialTransactionDenialReceiptInvariant
    {RequestId Principal Holder LedgerAccount Asset : Type}
    (state : FinancialTransactionProcessorState
      RequestId Principal Holder LedgerAccount Asset) : Prop :=
  ∀ requestId receipt, state.denials requestId = some receipt →
    receipt.response.requestId = requestId ∧
    receipt.response.expectedNonce = receipt.request.nonce ∧
    FinancialTransactionDenialReasonMatchesRequest
      receipt.request receipt.response.reason

/-- A request ID cannot simultaneously identify a success and a denial receipt. -/
def FinancialTransactionProcessorCacheDisjoint
    {RequestId Principal Holder LedgerAccount Asset : Type}
    (state : FinancialTransactionProcessorState
      RequestId Principal Holder LedgerAccount Asset) : Prop :=
  ∀ requestId,
    (∃ receipt, state.envelope.receipts requestId = some receipt) →
      state.denials requestId = none

/-- Full processor invariant: financial conservation, valid receipts, and disjoint caches. -/
def FinancialTransactionProcessorInvariant
    {RequestId Principal Holder LedgerAccount Asset : Type}
    [Fintype Holder] [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (openingLedger : Ledger LedgerAccount Asset)
    (state : FinancialTransactionProcessorState
      RequestId Principal Holder LedgerAccount Asset) : Prop :=
  FinancialTransactionEnvelopeInvariant mapping openingLedger state.envelope ∧
    FinancialTransactionDenialReceiptInvariant state ∧
    FinancialTransactionProcessorCacheDisjoint state

/-- A success step preserves the pre-existing envelope invariant. -/
theorem financialTransactionEnvelopeSuccess_preserves_invariant
    {RequestId Principal Holder LedgerAccount Asset : Type}
    [DecidableEq RequestId] [DecidableEq Principal]
    [Fintype Holder] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (openingLedger : Ledger LedgerAccount Asset)
    (before after : FinancialTransactionEnvelopeState
      RequestId Principal Holder LedgerAccount Asset)
    (requestId : RequestId)
    (request : FinancialTransactionRequest Principal Holder Asset)
    (hBefore : FinancialTransactionEnvelopeInvariant mapping openingLedger before)
    (hSuccess : FinancialTransactionEnvelopeSuccessStep
      policy mapping counterpart requestId request before after) :
    FinancialTransactionEnvelopeInvariant mapping openingLedger after := by
  rcases hSuccess with ⟨_hUnused, _hNonce, financialAfter, hOperation, hAfter⟩
  subst after
  constructor
  · exact authorizedFinancialStep_preserves_conservation
      policy mapping counterpart openingLedger hBefore.1.1
      (financialOperationStep_toAuthorizedFinancialStep
        policy mapping counterpart request.principal request.operation hOperation)
  · exact applyFinancialTransactionSuccess_preserves_receipt_invariant
      before requestId request financialAfter hBefore.2

/-- Inserting a denial preserves the key/nonce/reason receipt invariant. -/
theorem applyFinancialTransactionAuthorizationDenial_preserves_receipt_invariant
    {RequestId Principal Holder LedgerAccount Asset : Type}
    [DecidableEq RequestId]
    (before : FinancialTransactionProcessorState
      RequestId Principal Holder LedgerAccount Asset)
    (requestId : RequestId)
    (request : FinancialTransactionRequest Principal Holder Asset)
    (reason : FinancialTransactionDenialReason)
    (hBefore : FinancialTransactionDenialReceiptInvariant before)
    (hReason : FinancialTransactionDenialReasonMatchesRequest request reason) :
    FinancialTransactionDenialReceiptInvariant
      (applyFinancialTransactionAuthorizationDenial before requestId request reason) := by
  intro queryId receipt hFound
  by_cases hTarget : queryId = requestId
  · subst queryId
    have hEq : financialTransactionAuthorizationDenialReceipt
        requestId request reason = receipt := by
      apply Option.some.inj
      simpa [applyFinancialTransactionAuthorizationDenial] using hFound
    subst receipt
    exact ⟨rfl, rfl, hReason⟩
  · have hOld : before.denials queryId = some receipt := by
      simpa [applyFinancialTransactionAuthorizationDenial, hTarget] using hFound
    exact hBefore queryId receipt hOld

/-- A successful processor transition preserves all processor invariants. -/
theorem financialTransactionProcessorSuccess_preserves_invariant
    {RequestId Principal Holder LedgerAccount Asset : Type}
    [DecidableEq RequestId] [DecidableEq Principal]
    [Fintype Holder] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (openingLedger : Ledger LedgerAccount Asset)
    (before after : FinancialTransactionProcessorState
      RequestId Principal Holder LedgerAccount Asset)
    (requestId : RequestId)
    (request : FinancialTransactionRequest Principal Holder Asset)
    (hBefore : FinancialTransactionProcessorInvariant mapping openingLedger before)
    (hSuccess : FinancialTransactionProcessorSuccessStep
      policy mapping counterpart requestId request before after) :
    FinancialTransactionProcessorInvariant mapping openingLedger after := by
  rcases hSuccess with ⟨hNoDenial, hEnvelopeSuccess, hDenials⟩
  constructor
  · exact financialTransactionEnvelopeSuccess_preserves_invariant
      policy mapping counterpart openingLedger before.envelope after.envelope
      requestId request hBefore.1 hEnvelopeSuccess
  · constructor
    · simpa [hDenials] using hBefore.2.1
    · intro queryId hSuccessReceipt
      rcases hSuccessReceipt with ⟨receipt, hStored⟩
      by_cases hTarget : queryId = requestId
      · subst queryId
        simpa [hDenials] using hNoDenial
      · rcases hEnvelopeSuccess with
          ⟨_hUnused, _hNonce, financialAfter, _hOperation, hAfter⟩
        have hOld : before.envelope.receipts queryId = some receipt := by
          rw [hAfter] at hStored
          simpa [applyFinancialTransactionSuccess, hTarget] using hStored
        have hNoOldDenial := hBefore.2.2 queryId ⟨receipt, hOld⟩
        simpa [hDenials] using hNoOldDenial

/-- A cached authorization denial preserves the successful core state and nonce. -/
theorem financialTransactionAuthorizationDenial_core_unchanged
    {RequestId Principal Holder LedgerAccount Asset : Type}
    [DecidableEq RequestId]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (before after : FinancialTransactionProcessorState
      RequestId Principal Holder LedgerAccount Asset)
    (requestId : RequestId)
    (request : FinancialTransactionRequest Principal Holder Asset)
    (reason : FinancialTransactionDenialReason)
    (hDenial : FinancialTransactionAuthorizationDenialStep
      policy requestId request reason before after) :
    after.envelope.core = before.envelope.core := by
  rcases hDenial with ⟨_hSuccessUnused, _hDenialUnused, _hNonce, _hReason, rfl⟩
  rfl

/-- A denial transition cannot be cached at a stale or future nonce. -/
theorem financialTransactionAuthorizationDenial_rejects_nonce_mismatch
    {RequestId Principal Holder LedgerAccount Asset : Type}
    [DecidableEq RequestId]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (requestId : RequestId)
    (request : FinancialTransactionRequest Principal Holder Asset)
    (reason : FinancialTransactionDenialReason)
    (before after : FinancialTransactionProcessorState
      RequestId Principal Holder LedgerAccount Asset)
    (hMismatch : request.nonce ≠ before.envelope.core.nextNonce request.principal) :
    ¬ FinancialTransactionAuthorizationDenialStep
      policy requestId request reason before after := by
  intro hDenial
  exact hMismatch hDenial.2.2.1

/-- A denial receipt is inserted exactly as supplied by the rejected request. -/
theorem financialTransactionAuthorizationDenial_stores_receipt
    {RequestId Principal Holder LedgerAccount Asset : Type}
    [DecidableEq RequestId]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (requestId : RequestId)
    (request : FinancialTransactionRequest Principal Holder Asset)
    (reason : FinancialTransactionDenialReason)
    {before after : FinancialTransactionProcessorState
      RequestId Principal Holder LedgerAccount Asset}
    (hDenial : FinancialTransactionAuthorizationDenialStep
      policy requestId request reason before after) :
    after.denials requestId =
      some (financialTransactionAuthorizationDenialReceipt requestId request reason) := by
  rcases hDenial with ⟨_hSuccessUnused, _hDenialUnused, _hNonce, _hReason, rfl⟩
  simp [applyFinancialTransactionAuthorizationDenial]

/-- Response type returned by an exact request-ID lookup. -/
inductive FinancialTransactionProcessorResponse (RequestId : Type)
  | accepted (response : FinancialTransactionResponse RequestId)
  | authorizationRejected (response : FinancialTransactionDenialResponse RequestId)
  deriving DecidableEq

/-- Lookup returns a cached success or denial only for the exact stored request. -/
def cachedFinancialTransactionProcessorResponse
    {RequestId Principal Holder LedgerAccount Asset : Type}
    [DecidableEq RequestId] [DecidableEq Principal]
    [DecidableEq Holder] [DecidableEq Asset]
    (state : FinancialTransactionProcessorState
      RequestId Principal Holder LedgerAccount Asset)
    (requestId : RequestId)
    (request : FinancialTransactionRequest Principal Holder Asset) :
    Option (FinancialTransactionProcessorResponse RequestId) :=
  match state.envelope.receipts requestId with
  | some receipt =>
      if receipt.response.requestId = requestId ∧ receipt.request = request
      then some (.accepted receipt.response) else none
  | none =>
      match state.denials requestId with
      | none => none
      | some receipt =>
          if receipt.response.requestId = requestId ∧ receipt.request = request
          then some (.authorizationRejected receipt.response) else none

/-- Inserting a denial preserves the processor invariant, including cache disjointness. -/
theorem financialTransactionProcessorDenial_preserves_invariant
    {RequestId Principal Holder LedgerAccount Asset : Type}
    [DecidableEq RequestId]
    [Fintype Holder] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (openingLedger : Ledger LedgerAccount Asset)
    (before after : FinancialTransactionProcessorState
      RequestId Principal Holder LedgerAccount Asset)
    (requestId : RequestId)
    (request : FinancialTransactionRequest Principal Holder Asset)
    (reason : FinancialTransactionDenialReason)
    (hBefore : FinancialTransactionProcessorInvariant mapping openingLedger before)
    (hDenial : FinancialTransactionAuthorizationDenialStep
      policy requestId request reason before after) :
    FinancialTransactionProcessorInvariant mapping openingLedger after := by
  rcases hDenial with ⟨hNoSuccess, _hNoDenial, _hNonce, hReason, rfl⟩
  have hReasonMatches : FinancialTransactionDenialReasonMatchesRequest request reason := by
    cases hOp : request.operation with
    | transfer source destination asset amount =>
        have hAuthorization := hReason
        simp [FinancialTransactionAuthorizationDenial, hOp] at hAuthorization
        simpa [FinancialTransactionDenialReasonMatchesRequest, hOp] using hAuthorization.1
    | issue issuer recipient asset amount =>
        have hAuthorization := hReason
        simp [FinancialTransactionAuthorizationDenial, hOp] at hAuthorization
        simpa [FinancialTransactionDenialReasonMatchesRequest, hOp] using hAuthorization.1
    | burn holder asset amount =>
        have hAuthorization := hReason
        simp [FinancialTransactionAuthorizationDenial, hOp] at hAuthorization
        simpa [FinancialTransactionDenialReasonMatchesRequest, hOp] using hAuthorization.1
  constructor
  · exact hBefore.1
  · constructor
    · exact applyFinancialTransactionAuthorizationDenial_preserves_receipt_invariant
        before requestId request reason hBefore.2.1 hReasonMatches
    · intro queryId hSuccessReceipt
      by_cases hTarget : queryId = requestId
      · subst queryId
        rcases hSuccessReceipt with ⟨receipt, hReceipt⟩
        have hOld : before.envelope.receipts requestId = some receipt := by
          simpa [applyFinancialTransactionAuthorizationDenial] using hReceipt
        rw [hNoSuccess] at hOld
        cases hOld
      · rcases hSuccessReceipt with ⟨receipt, hReceipt⟩
        have hOld : before.envelope.receipts queryId = some receipt := by
          simpa [applyFinancialTransactionAuthorizationDenial, hTarget] using hReceipt
        have hNoOldDenial := hBefore.2.2 queryId ⟨receipt, hOld⟩
        simpa [applyFinancialTransactionAuthorizationDenial, hTarget] using hNoOldDenial

/-- Initial processor state satisfies financial, receipt, and cache-disjointness invariants. -/
theorem initialFinancialTransactionProcessorState_invariant
    {RequestId Principal Holder LedgerAccount Asset : Type}
    [Fintype Holder] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (initialFinancial : FinancialState Holder LedgerAccount Asset)
    (hInitial : FinancialInvariant mapping initialFinancial) :
    FinancialTransactionProcessorInvariant mapping initialFinancial.ledger
      (initialFinancialTransactionProcessorState
        RequestId Principal initialFinancial) := by
  constructor
  · constructor
    · exact ⟨hInitial, by intro asset; rfl⟩
    · intro requestId receipt hReceipt
      simp [initialFinancialTransactionProcessorState,
        initialFinancialTransactionEnvelopeState] at hReceipt
  · constructor
    · intro requestId receipt hReceipt
      simp [initialFinancialTransactionProcessorState] at hReceipt
    · intro requestId hSuccess
      rcases hSuccess with ⟨receipt, hReceipt⟩
      simp [initialFinancialTransactionProcessorState,
        initialFinancialTransactionEnvelopeState] at hReceipt

/-- A cached denial is returned only for the exact stored request. -/
theorem financialTransactionDenialReplay_returns_cached_response
    {RequestId Principal Holder LedgerAccount Asset : Type}
    [DecidableEq RequestId] [DecidableEq Principal]
    [DecidableEq Holder] [DecidableEq Asset]
    (state : FinancialTransactionProcessorState
      RequestId Principal Holder LedgerAccount Asset)
    (requestId : RequestId)
    (request : FinancialTransactionRequest Principal Holder Asset)
    (receipt : FinancialTransactionDenialReceipt RequestId Principal Holder Asset)
    (hStored : state.denials requestId = some receipt)
    (hResponseId : receipt.response.requestId = requestId)
    (hSame : receipt.request = request)
    (hNoSuccess : state.envelope.receipts requestId = none) :
    cachedFinancialTransactionProcessorResponse state requestId request =
      some (.authorizationRejected receipt.response) := by
  simp [cachedFinancialTransactionProcessorResponse, hNoSuccess,
    hStored, hResponseId, hSame]

/-- A verified processor machine admits successes, cached authorization denials, and exact replays. -/
def financialTransactionProcessorMachine
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
      (FinancialTransactionProcessorState
        RequestId Principal Holder LedgerAccount Asset) where
  invariant := FinancialTransactionProcessorInvariant mapping initialFinancial.ledger
  initial := fun state =>
    state = initialFinancialTransactionProcessorState
      RequestId Principal initialFinancial
  step := FinancialTransactionProcessorStep policy mapping counterpart
  initial_safe := by
    intro state hState
    subst state
    exact initialFinancialTransactionProcessorState_invariant
      mapping initialFinancial hInitial
  step_safe := by
    intro before after hBefore hStep
    rcases hStep with hSuccess | hRest
    · rcases hSuccess with ⟨requestId, request, hAccepted⟩
      exact financialTransactionProcessorSuccess_preserves_invariant
        policy mapping counterpart initialFinancial.ledger
        before after requestId request hBefore hAccepted
    · rcases hRest with hDenial | hReplay
      · rcases hDenial with ⟨requestId, request, reason, hRejected⟩
        exact financialTransactionProcessorDenial_preserves_invariant
          policy mapping initialFinancial.ledger before after requestId request reason
          hBefore hRejected
      · rcases hReplay with ⟨requestId, request, hExactReplay⟩
        rcases hExactReplay with hSuccessReplay | hDenialReplay
        · rcases hSuccessReplay with
            ⟨_receipt, _hStored, _hResponseId, _hSame, hUnchanged⟩
          rw [hUnchanged]
          exact hBefore
        · rcases hDenialReplay with
            ⟨_receipt, _hStored, _hResponseId, _hSame, hUnchanged⟩
          rw [hUnchanged]
          exact hBefore

/-- Every reachable processor state retains the financial and receipt invariants. -/
theorem financialTransactionProcessorInvariant_of_reachable
    {RequestId Principal Holder LedgerAccount Asset : Type}
    [DecidableEq RequestId] [DecidableEq Principal]
    [Fintype Holder] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (initialFinancial : FinancialState Holder LedgerAccount Asset)
    (hInitial : FinancialInvariant mapping initialFinancial)
    {state : FinancialTransactionProcessorState
      RequestId Principal Holder LedgerAccount Asset}
    (hReachable : Reachable
      (financialTransactionProcessorMachine policy mapping counterpart
        initialFinancial hInitial) state) :
    FinancialTransactionProcessorInvariant mapping initialFinancial.ledger state := by
  exact invariant_of_reachable
    (financialTransactionProcessorMachine policy mapping counterpart
      initialFinancial hInitial) hReachable

end SIRM
