import SIRM.AuthorizedFinancialMachine

/-!
# Replay-Protected Authorized Financial Machine

This layer generalizes the migration-only nonce guard to the complete
`AuthorizedFinancialStep` relation: transfer, issuance, and burn all consume
one shared sequential nonce for the acting principal. The selected financial
transition and the nonce increment are returned in one state update.

The model uses unbounded `Nat` nonces and records only admitted successful
transitions. Persistent storage, signatures, failed-request nonce policy,
response idempotency, concurrent transaction ordering, and a production
transaction envelope remain outside this abstract machine.
-/

namespace SIRM

/-- Financial balances/GL paired with one independent next nonce per principal. -/
structure ReplayProtectedFinancialState
    (Principal Holder LedgerAccount Asset : Type) where
  financial : FinancialState Holder LedgerAccount Asset
  nextNonce : Principal → Nat

/-- Initial replay-protected state: every principal starts at nonce zero. -/
def initialReplayProtectedFinancialState
    (Principal : Type)
    {Holder LedgerAccount Asset : Type}
    (initialFinancial : FinancialState Holder LedgerAccount Asset) :
    ReplayProtectedFinancialState Principal Holder LedgerAccount Asset :=
  { financial := initialFinancial
    nextNonce := fun _ => 0 }

@[simp] theorem initialReplayProtectedFinancialState_nonce_zero
    (Principal : Type)
    {Holder LedgerAccount Asset : Type}
    (initialFinancial : FinancialState Holder LedgerAccount Asset)
    (principal : Principal) :
    (initialReplayProtectedFinancialState Principal initialFinancial).nextNonce principal = 0 :=
  rfl

/-- Paired update: commit one financial result and increment only its principal. -/
def applyReplayProtectedFinancialStep
    (Principal : Type) [DecidableEq Principal]
    {Holder LedgerAccount Asset : Type}
    (before : ReplayProtectedFinancialState Principal Holder LedgerAccount Asset)
    (principal : Principal) (nonce : Nat)
    (financialAfter : FinancialState Holder LedgerAccount Asset) :
    ReplayProtectedFinancialState Principal Holder LedgerAccount Asset :=
  { financial := financialAfter
    nextNonce := fun candidate =>
      if candidate = principal then nonce + 1 else before.nextNonce candidate }

/--
An operation is admitted only at the principal's exact next nonce and only
when the underlying transfer/issue/burn financial transition is authorized.
-/
def ReplayProtectedFinancialStep
    {Principal Holder LedgerAccount Asset : Type}
    [DecidableEq Principal]
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (principal : Principal) (nonce : Nat)
    (before after : ReplayProtectedFinancialState Principal Holder LedgerAccount Asset) : Prop :=
  nonce = before.nextNonce principal ∧
    ∃ financialAfter,
      AuthorizedFinancialStep policy mapping counterpart before.financial financialAfter ∧
      after = applyReplayProtectedFinancialStep Principal before principal nonce financialAfter

/-- A stale or future nonce cannot form an admitted financial step. -/
theorem replayProtectedFinancialStep_reject_nonce_mismatch
    {Principal Holder LedgerAccount Asset : Type}
    [DecidableEq Principal]
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (principal : Principal) (nonce : Nat)
    (before after : ReplayProtectedFinancialState Principal Holder LedgerAccount Asset)
    (hMismatch : nonce ≠ before.nextNonce principal) :
    ¬ ReplayProtectedFinancialStep policy mapping counterpart principal nonce before after := by
  intro hStep
  exact hMismatch hStep.1

/-- Every accepted operation increments the selected principal exactly once. -/
theorem replayProtectedFinancialStep_next_nonce
    {Principal Holder LedgerAccount Asset : Type}
    [DecidableEq Principal]
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (principal : Principal) (nonce : Nat)
    {before after : ReplayProtectedFinancialState Principal Holder LedgerAccount Asset}
    (hStep : ReplayProtectedFinancialStep policy mapping counterpart
      principal nonce before after) :
    after.nextNonce principal = nonce + 1 := by
  rcases hStep with ⟨_hExpected, financialAfter, _hFinancial, rfl⟩
  simp [applyReplayProtectedFinancialStep]

/-- An accepted operation leaves every other principal's nonce unchanged. -/
theorem replayProtectedFinancialStep_other_nonce
    {Principal Holder LedgerAccount Asset : Type}
    [DecidableEq Principal]
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (principal other : Principal) (nonce : Nat)
    {before after : ReplayProtectedFinancialState Principal Holder LedgerAccount Asset}
    (hStep : ReplayProtectedFinancialStep policy mapping counterpart
      principal nonce before after)
    (hOther : other ≠ principal) :
    after.nextNonce other = before.nextNonce other := by
  rcases hStep with ⟨_hExpected, financialAfter, _hFinancial, rfl⟩
  simp [applyReplayProtectedFinancialStep, hOther]

/-- The financial projection of an accepted replay-protected step is an ordinary authorized step. -/
theorem replayProtectedFinancialStep_financial_projection
    {Principal Holder LedgerAccount Asset : Type}
    [DecidableEq Principal]
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (principal : Principal) (nonce : Nat)
    {before after : ReplayProtectedFinancialState Principal Holder LedgerAccount Asset}
    (hStep : ReplayProtectedFinancialStep policy mapping counterpart
      principal nonce before after) :
    ∃ financialAfter,
      AuthorizedFinancialStep policy mapping counterpart before.financial financialAfter ∧
      after.financial = financialAfter := by
  rcases hStep with ⟨_hExpected, financialAfter, hFinancial, hAfter⟩
  refine ⟨financialAfter, hFinancial, ?_⟩
  rw [hAfter]
  rfl

/-- The replay-protected invariant is the complete existing holder/GL conservation invariant. -/
def ReplayProtectedFinancialInvariant
    {Principal Holder LedgerAccount Asset : Type}
    [Fintype Holder] [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (openingLedger : Ledger LedgerAccount Asset)
    (state : ReplayProtectedFinancialState Principal Holder LedgerAccount Asset) : Prop :=
  FinancialConservationInvariant mapping openingLedger state.financial

/--
Verified machine for all authorized financial operations under one shared
per-principal nonce sequence.
-/
def replayProtectedFinancialMachine
    {Principal Holder LedgerAccount Asset : Type}
    [DecidableEq Principal]
    [Fintype Holder] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (initialFinancial : FinancialState Holder LedgerAccount Asset)
    (hInitial : FinancialInvariant mapping initialFinancial) :
    VerifiedStateMachine (ReplayProtectedFinancialState Principal Holder LedgerAccount Asset) where
  invariant := ReplayProtectedFinancialInvariant mapping initialFinancial.ledger
  initial := fun state =>
    state = initialReplayProtectedFinancialState Principal initialFinancial
  step := fun before after =>
    ∃ principal nonce,
      ReplayProtectedFinancialStep policy mapping counterpart principal nonce before after
  initial_safe := by
    intro state hState
    subst state
    exact ⟨hInitial, by intro asset; rfl⟩
  step_safe := by
    intro before after hBefore hStep
    rcases hStep with ⟨principal, nonce, hReplay⟩
    rcases hReplay with ⟨_hNonce, financialAfter, hFinancial, hAfter⟩
    subst after
    exact authorizedFinancialStep_preserves_conservation
      policy mapping counterpart initialFinancial.ledger hBefore hFinancial

/-- Every reachable state retains holder/supply, mapped-subledger, and signed-GL conservation. -/
theorem replayProtectedFinancialInvariant_of_reachable
    {Principal Holder LedgerAccount Asset : Type}
    [DecidableEq Principal]
    [Fintype Holder] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (initialFinancial : FinancialState Holder LedgerAccount Asset)
    (hInitial : FinancialInvariant mapping initialFinancial)
    {state : ReplayProtectedFinancialState Principal Holder LedgerAccount Asset}
    (hReachable : Reachable
      (replayProtectedFinancialMachine policy mapping counterpart
        initialFinancial hInitial) state) :
    ReplayProtectedFinancialInvariant mapping initialFinancial.ledger state := by
  exact invariant_of_reachable
    (replayProtectedFinancialMachine policy mapping counterpart
      initialFinancial hInitial) hReachable

end SIRM
