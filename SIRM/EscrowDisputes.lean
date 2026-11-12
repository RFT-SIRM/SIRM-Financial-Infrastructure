import SIRM.EscrowTimeLocks

/-!
# Escrow Dispute Intake and Per-ID Freeze

This first dispute layer adds an authorized, one-way dispute-intake marker to
an already time-locked, financially integrated escrow registry. A dispute may
be raised only for a pending record and strictly before its fixed deadline.
Once raised, that escrow ID is frozen: ordinary release, voluntary
cancellation, and timeout expiry are no longer admissible for that ID. The
underlying discrete clock may continue to advance, and unrelated escrow IDs
remain independently operable.

This is deliberately a safety-only stage. It does not adjudicate the merits,
validate external evidence, choose a beneficiary/refund outcome, provide an
appeal or reversal process, or establish external settlement finality. The
marker is permanent in this layer; a later adjudication module must define the
only authorized way to resolve it.
-/

namespace SIRM

/-- Immutable filing metadata retained for the lifetime of the escrow ID. -/
structure EscrowDisputeFiling (Principal Holder : Type) where
  principal : Principal
  claimant : Holder
  filedAt : Nat

/-- A dispute-aware wrapper around the existing time-locked escrow state. -/
structure EscrowDisputeFinancialRegistryState
    (Principal EscrowId Holder LedgerAccount Asset : Type) where
  timed : EscrowTimeLockedFinancialRegistryState EscrowId Holder LedgerAccount Asset
  disputes : EscrowId → Option (EscrowDisputeFiling Principal Holder)

/-- The dispute-intake authority is independent of transfer and escrow permissions. -/
structure EscrowDisputeAuthorizationPolicy
    (Principal EscrowId Holder Asset : Type) where
  mayRaiseDispute :
    HoldingsState Holder Asset → Principal → EscrowId → Holder → Nat →
      Holder → Holder → Holder → Asset → Nat → Prop

/-- The financial invariant remains exactly the established timed escrow invariant. -/
def EscrowDisputeFinancialRegistryInvariant
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [Fintype EscrowId] [Fintype Holder] [Fintype LedgerAccount]
    [DecidableEq LedgerAccount] [DecidableEq Asset]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (openingLedger : Ledger LedgerAccount Asset)
    (vaultHolder : Holder)
    (state : EscrowDisputeFinancialRegistryState
      Principal EscrowId Holder LedgerAccount Asset) : Prop :=
  EscrowTimeLockedFinancialRegistryInvariant mapping openingLedger vaultHolder state.timed

/-- Start with no dispute markers around an existing timed escrow state. -/
def emptyEscrowDisputeFinancialRegistryState
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    (timed : EscrowTimeLockedFinancialRegistryState
      EscrowId Holder LedgerAccount Asset) :
    EscrowDisputeFinancialRegistryState Principal EscrowId Holder LedgerAccount Asset :=
  { timed := timed
    disputes := fun _ => none }

/-- Open a fresh escrow ID only if that ID has no dispute filing. -/
def EscrowDisputeTimeLockedOpenStep
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (vaultHolder : Holder)
    (expiresAt : EscrowId → Nat)
    (id : EscrowId)
    (before after : EscrowDisputeFinancialRegistryState
      Principal EscrowId Holder LedgerAccount Asset) : Prop :=
  ∃ timedAfter,
    before.disputes id = none ∧
    EscrowTimeLockedOpenStep policy escrowPolicy mapping vaultHolder expiresAt id
      before.timed timedAfter ∧
    after = { timed := timedAfter, disputes := before.disputes }

/-- Release is admitted only while the selected ID has no active dispute. -/
def EscrowDisputeTimeLockedReleaseStep
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (vaultHolder : Holder)
    (expiresAt : EscrowId → Nat)
    (id : EscrowId)
    (before after : EscrowDisputeFinancialRegistryState
      Principal EscrowId Holder LedgerAccount Asset) : Prop :=
  ∃ timedAfter,
    before.disputes id = none ∧
    EscrowTimeLockedReleaseStep policy escrowPolicy mapping vaultHolder expiresAt id
      before.timed timedAfter ∧
    after = { timed := timedAfter, disputes := before.disputes }

/-- Voluntary cancellation is blocked for a disputed ID. -/
def EscrowDisputeTimeLockedCancelStep
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (vaultHolder : Holder)
    (expiresAt : EscrowId → Nat)
    (id : EscrowId)
    (before after : EscrowDisputeFinancialRegistryState
      Principal EscrowId Holder LedgerAccount Asset) : Prop :=
  ∃ timedAfter,
    before.disputes id = none ∧
    EscrowTimeLockedCancelStep policy escrowPolicy mapping vaultHolder expiresAt id
      before.timed timedAfter ∧
    after = { timed := timedAfter, disputes := before.disputes }

/-- Timeout expiry is blocked for a disputed ID, even after its deadline. -/
def EscrowDisputeTimeLockedExpireStep
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (vaultHolder : Holder)
    (expiresAt : EscrowId → Nat)
    (id : EscrowId)
    (before after : EscrowDisputeFinancialRegistryState
      Principal EscrowId Holder LedgerAccount Asset) : Prop :=
  ∃ timedAfter,
    before.disputes id = none ∧
    EscrowTimeLockedExpireStep policy escrowPolicy mapping vaultHolder expiresAt id
      before.timed timedAfter ∧
    after = { timed := timedAfter, disputes := before.disputes }

/-- The discrete clock can advance without modifying dispute filings. -/
def EscrowDisputeTimeAdvanceStep
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    (before after : EscrowDisputeFinancialRegistryState
      Principal EscrowId Holder LedgerAccount Asset) : Prop :=
  ∃ timedAfter,
    EscrowTimeAdvanceStep before.timed timedAfter ∧
    after = { timed := timedAfter, disputes := before.disputes }

/-- Record one authorized dispute filing against a pending, not-yet-expired ID. -/
def EscrowDisputeRaiseStep
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    (disputePolicy : EscrowDisputeAuthorizationPolicy Principal EscrowId Holder Asset)
    (vaultHolder : Holder)
    (expiresAt : EscrowId → Nat)
    (id : EscrowId)
    (before after : EscrowDisputeFinancialRegistryState
      Principal EscrowId Holder LedgerAccount Asset) : Prop :=
  ∃ (record : EscrowRecord Holder Asset) (principal : Principal) (claimant : Holder),
    before.timed.escrow.registry.records id = some record ∧
    record.phase = EscrowPhase.pending ∧
    before.timed.currentTime < expiresAt id ∧
    before.disputes id = none ∧
    (claimant = record.depositor ∨ claimant = record.beneficiary) ∧
    disputePolicy.mayRaiseDispute before.timed.escrow.financial.holdings
      principal id claimant before.timed.currentTime record.depositor
      record.beneficiary vaultHolder record.asset record.amount ∧
    after = {
      timed := before.timed
      disputes := fun query =>
        if query = id then
          some {
            principal := principal
            claimant := claimant
            filedAt := before.timed.currentTime
          }
        else before.disputes query
    }

/-- All timed escrow operations pass through the per-ID dispute freeze. -/
def EscrowDisputeFinancialRegistryStep
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (disputePolicy : EscrowDisputeAuthorizationPolicy Principal EscrowId Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (vaultHolder : Holder)
    (expiresAt : EscrowId → Nat)
    (before after : EscrowDisputeFinancialRegistryState
      Principal EscrowId Holder LedgerAccount Asset) : Prop :=
  (∃ id, EscrowDisputeTimeLockedOpenStep policy escrowPolicy mapping vaultHolder
    expiresAt id before after) ∨
  (∃ id, EscrowDisputeTimeLockedReleaseStep policy escrowPolicy mapping vaultHolder
    expiresAt id before after) ∨
  (∃ id, EscrowDisputeTimeLockedCancelStep policy escrowPolicy mapping vaultHolder
    expiresAt id before after) ∨
  (∃ id, EscrowDisputeTimeLockedExpireStep policy escrowPolicy mapping vaultHolder
    expiresAt id before after) ∨
  EscrowDisputeTimeAdvanceStep before after ∨
  (∃ id, EscrowDisputeRaiseStep disputePolicy vaultHolder expiresAt id before after)

/-- An active filing makes release of that same escrow ID impossible. -/
theorem escrowDisputeTimeLockedReleaseStep_rejects_disputed
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (vaultHolder : Holder) (expiresAt : EscrowId → Nat) (id : EscrowId)
    (before after : EscrowDisputeFinancialRegistryState
      Principal EscrowId Holder LedgerAccount Asset)
    (hDisputed : before.disputes id ≠ none) :
    ¬ EscrowDisputeTimeLockedReleaseStep policy escrowPolicy mapping vaultHolder
      expiresAt id before after := by
  intro hStep
  rcases hStep with ⟨_timedAfter, hNoDispute, _hTimed, _hAfter⟩
  exact hDisputed hNoDispute

/-- An active filing makes voluntary cancellation of that ID impossible. -/
theorem escrowDisputeTimeLockedCancelStep_rejects_disputed
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (vaultHolder : Holder) (expiresAt : EscrowId → Nat) (id : EscrowId)
    (before after : EscrowDisputeFinancialRegistryState
      Principal EscrowId Holder LedgerAccount Asset)
    (hDisputed : before.disputes id ≠ none) :
    ¬ EscrowDisputeTimeLockedCancelStep policy escrowPolicy mapping vaultHolder
      expiresAt id before after := by
  intro hStep
  rcases hStep with ⟨_timedAfter, hNoDispute, _hTimed, _hAfter⟩
  exact hDisputed hNoDispute

/-- An active filing blocks timeout expiry, including at or after the deadline. -/
theorem escrowDisputeTimeLockedExpireStep_rejects_disputed
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (vaultHolder : Holder) (expiresAt : EscrowId → Nat) (id : EscrowId)
    (before after : EscrowDisputeFinancialRegistryState
      Principal EscrowId Holder LedgerAccount Asset)
    (hDisputed : before.disputes id ≠ none) :
    ¬ EscrowDisputeTimeLockedExpireStep policy escrowPolicy mapping vaultHolder
      expiresAt id before after := by
  intro hStep
  rcases hStep with ⟨_timedAfter, hNoDispute, _hTimed, _hAfter⟩
  exact hDisputed hNoDispute

/-- An escrow ID accepts at most one dispute filing in this first-stage model. -/
theorem escrowDisputeRaiseStep_rejects_existing_filing
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    (disputePolicy : EscrowDisputeAuthorizationPolicy Principal EscrowId Holder Asset)
    (vaultHolder : Holder) (expiresAt : EscrowId → Nat) (id : EscrowId)
    (before after : EscrowDisputeFinancialRegistryState
      Principal EscrowId Holder LedgerAccount Asset)
    (hDisputed : before.disputes id ≠ none) :
    ¬ EscrowDisputeRaiseStep disputePolicy vaultHolder expiresAt id before after := by
  intro hStep
  rcases hStep with
    ⟨_record, _principal, _claimant, _hRecord, _hPending, _hBeforeDeadline,
      hNoDispute, _hParty, _hAuthorized, _hAfter⟩
  exact hDisputed hNoDispute

/-- A filed marker cannot be erased or replaced by any later admitted step. -/
theorem escrowDisputeFinancialRegistryStep_preserves_existing_filing
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (disputePolicy : EscrowDisputeAuthorizationPolicy Principal EscrowId Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (vaultHolder : Holder) (expiresAt : EscrowId → Nat)
    {before after : EscrowDisputeFinancialRegistryState
      Principal EscrowId Holder LedgerAccount Asset}
    (hStep : EscrowDisputeFinancialRegistryStep policy escrowPolicy disputePolicy
      mapping vaultHolder expiresAt before after)
    (id : EscrowId) (hDisputed : before.disputes id ≠ none) :
    after.disputes id = before.disputes id := by
  rcases hStep with hOpen | hRest
  · rcases hOpen with ⟨openedId, hOpen⟩
    rcases hOpen with ⟨_timedAfter, _hNoDispute, _hTimed, hAfter⟩
    cases hAfter
    rfl
  · rcases hRest with hRelease | hRest
    · rcases hRelease with ⟨releasedId, hRelease⟩
      rcases hRelease with ⟨_timedAfter, _hNoDispute, _hTimed, hAfter⟩
      cases hAfter
      rfl
    · rcases hRest with hCancel | hRest
      · rcases hCancel with ⟨cancelledId, hCancel⟩
        rcases hCancel with ⟨_timedAfter, _hNoDispute, _hTimed, hAfter⟩
        cases hAfter
        rfl
      · rcases hRest with hExpire | hRest
        · rcases hExpire with ⟨expiredId, hExpire⟩
          rcases hExpire with ⟨_timedAfter, _hNoDispute, _hTimed, hAfter⟩
          cases hAfter
          rfl
        · rcases hRest with hAdvance | hRaise
          · rcases hAdvance with ⟨_timedAfter, _hTimed, hAfter⟩
            cases hAfter
            rfl
          · rcases hRaise with ⟨filedId, hRaise⟩
            rcases hRaise with
              ⟨_record, principal, claimant, _hRecord, _hPending,
                _hBeforeDeadline, hNoDispute, _hParty, _hAuthorized, hAfter⟩
            cases hAfter
            by_cases hSame : id = filedId
            · subst filedId
              exact False.elim (hDisputed hNoDispute)
            · simp [hSame]

/-- A dispute cannot be filed once the selected ID's deadline has elapsed. -/
theorem escrowDisputeRaiseStep_rejects_elapsed_deadline
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    (disputePolicy : EscrowDisputeAuthorizationPolicy Principal EscrowId Holder Asset)
    (vaultHolder : Holder) (expiresAt : EscrowId → Nat) (id : EscrowId)
    (before after : EscrowDisputeFinancialRegistryState
      Principal EscrowId Holder LedgerAccount Asset)
    (hElapsed : expiresAt id ≤ before.timed.currentTime) :
    ¬ EscrowDisputeRaiseStep disputePolicy vaultHolder expiresAt id before after := by
  intro hStep
  rcases hStep with
    ⟨_record, _principal, _claimant, _hRecord, _hPending, hBeforeDeadline,
      _hNoDispute, _hParty, _hAuthorized, _hAfter⟩
  exact (not_lt_of_ge hElapsed) hBeforeDeadline

/-- The dispute wrapper preserves the full timed financial invariant. -/
theorem escrowDisputeFinancialRegistryStep_preserves_invariant
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype EscrowId] [Fintype Holder] [Fintype LedgerAccount]
    [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (disputePolicy : EscrowDisputeAuthorizationPolicy Principal EscrowId Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (openingLedger : Ledger LedgerAccount Asset)
    (vaultHolder : Holder) (expiresAt : EscrowId → Nat)
    {before after : EscrowDisputeFinancialRegistryState
      Principal EscrowId Holder LedgerAccount Asset}
    (hBefore : EscrowDisputeFinancialRegistryInvariant mapping openingLedger
      vaultHolder before)
    (hStep : EscrowDisputeFinancialRegistryStep policy escrowPolicy disputePolicy
      mapping vaultHolder expiresAt before after) :
    EscrowDisputeFinancialRegistryInvariant mapping openingLedger vaultHolder after := by
  change EscrowTimeLockedFinancialRegistryInvariant mapping openingLedger
    vaultHolder before.timed at hBefore
  change EscrowTimeLockedFinancialRegistryInvariant mapping openingLedger
    vaultHolder after.timed
  rcases hStep with hOpen | hRest
  · rcases hOpen with ⟨id, hOpen⟩
    rcases hOpen with ⟨timedAfter, _hNoDispute, hTimed, hAfter⟩
    cases hAfter
    exact escrowTimeLockedFinancialRegistryStep_preserves_invariant
      policy escrowPolicy mapping openingLedger vaultHolder expiresAt hBefore
      (Or.inl ⟨id, hTimed⟩)
  · rcases hRest with hRelease | hRest
    · rcases hRelease with ⟨id, hRelease⟩
      rcases hRelease with ⟨timedAfter, _hNoDispute, hTimed, hAfter⟩
      cases hAfter
      exact escrowTimeLockedFinancialRegistryStep_preserves_invariant
        policy escrowPolicy mapping openingLedger vaultHolder expiresAt hBefore
        (Or.inr (Or.inl ⟨id, hTimed⟩))
    · rcases hRest with hCancel | hRest
      · rcases hCancel with ⟨id, hCancel⟩
        rcases hCancel with ⟨timedAfter, _hNoDispute, hTimed, hAfter⟩
        cases hAfter
        exact escrowTimeLockedFinancialRegistryStep_preserves_invariant
          policy escrowPolicy mapping openingLedger vaultHolder expiresAt hBefore
          (Or.inr (Or.inr (Or.inl ⟨id, hTimed⟩)))
      · rcases hRest with hExpire | hRest
        · rcases hExpire with ⟨id, hExpire⟩
          rcases hExpire with ⟨timedAfter, _hNoDispute, hTimed, hAfter⟩
          cases hAfter
          exact escrowTimeLockedFinancialRegistryStep_preserves_invariant
            policy escrowPolicy mapping openingLedger vaultHolder expiresAt hBefore
            (Or.inr (Or.inr (Or.inr (Or.inl ⟨id, hTimed⟩))))
        · rcases hRest with hAdvance | hRaise
          · rcases hAdvance with ⟨timedAfter, hTimed, hAfter⟩
            cases hAfter
            exact escrowTimeLockedFinancialRegistryStep_preserves_invariant
              policy escrowPolicy mapping openingLedger vaultHolder expiresAt hBefore
              (Or.inr (Or.inr (Or.inr (Or.inr hTimed))))
          · rcases hRaise with ⟨id, hRaise⟩
            rcases hRaise with
              ⟨_record, _principal, _claimant, _hRecord, _hPending,
                _hBeforeDeadline, _hNoDispute, _hParty, _hAuthorized, hAfter⟩
            cases hAfter
            exact hBefore

/-- A dispute filing does not advance or rewind the abstract clock. -/
theorem escrowDisputeFinancialRegistryStep_time_monotone
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (disputePolicy : EscrowDisputeAuthorizationPolicy Principal EscrowId Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (vaultHolder : Holder) (expiresAt : EscrowId → Nat)
    {before after : EscrowDisputeFinancialRegistryState
      Principal EscrowId Holder LedgerAccount Asset}
    (hStep : EscrowDisputeFinancialRegistryStep policy escrowPolicy disputePolicy
      mapping vaultHolder expiresAt before after) :
    before.timed.currentTime ≤ after.timed.currentTime := by
  rcases hStep with hOpen | hRest
  · rcases hOpen with ⟨id, hOpen⟩
    rcases hOpen with ⟨timedAfter, _hNoDispute, hTimed, hAfter⟩
    cases hAfter
    exact escrowTimeLockedFinancialRegistryStep_time_monotone
      policy escrowPolicy mapping vaultHolder expiresAt (Or.inl ⟨id, hTimed⟩)
  · rcases hRest with hRelease | hRest
    · rcases hRelease with ⟨id, hRelease⟩
      rcases hRelease with ⟨timedAfter, _hNoDispute, hTimed, hAfter⟩
      cases hAfter
      exact escrowTimeLockedFinancialRegistryStep_time_monotone
        policy escrowPolicy mapping vaultHolder expiresAt (Or.inr (Or.inl ⟨id, hTimed⟩))
    · rcases hRest with hCancel | hRest
      · rcases hCancel with ⟨id, hCancel⟩
        rcases hCancel with ⟨timedAfter, _hNoDispute, hTimed, hAfter⟩
        cases hAfter
        exact escrowTimeLockedFinancialRegistryStep_time_monotone
          policy escrowPolicy mapping vaultHolder expiresAt (Or.inr (Or.inr (Or.inl ⟨id, hTimed⟩)))
      · rcases hRest with hExpire | hRest
        · rcases hExpire with ⟨id, hExpire⟩
          rcases hExpire with ⟨timedAfter, _hNoDispute, hTimed, hAfter⟩
          cases hAfter
          exact escrowTimeLockedFinancialRegistryStep_time_monotone
            policy escrowPolicy mapping vaultHolder expiresAt (Or.inr (Or.inr (Or.inr (Or.inl ⟨id, hTimed⟩))))
        · rcases hRest with hAdvance | hRaise
          · rcases hAdvance with ⟨timedAfter, hTimed, hAfter⟩
            cases hAfter
            exact escrowTimeLockedFinancialRegistryStep_time_monotone
              policy escrowPolicy mapping vaultHolder expiresAt
              (Or.inr (Or.inr (Or.inr (Or.inr hTimed))))
          · rcases hRaise with ⟨id, hRaise⟩
            rcases hRaise with
              ⟨_record, _principal, _claimant, _hRecord, _hPending,
                _hBeforeDeadline, _hNoDispute, _hParty, _hAuthorized, hAfter⟩
            cases hAfter
            exact le_rfl

/-- Verified dispute-aware machine; disputed IDs cannot be released/refunded. -/
def escrowDisputeFinancialRegistryMachine
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype EscrowId] [Fintype Holder] [Fintype LedgerAccount]
    [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (disputePolicy : EscrowDisputeAuthorizationPolicy Principal EscrowId Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (openingLedger : Ledger LedgerAccount Asset)
    (vaultHolder : Holder) (expiresAt : EscrowId → Nat)
    (initialState : EscrowDisputeFinancialRegistryState
      Principal EscrowId Holder LedgerAccount Asset)
    (hInitial : EscrowDisputeFinancialRegistryInvariant mapping openingLedger
      vaultHolder initialState)
    (hInitialNoDisputes : ∀ id, initialState.disputes id = none) :
    VerifiedStateMachine
      (EscrowDisputeFinancialRegistryState Principal EscrowId Holder LedgerAccount Asset) where
  invariant := EscrowDisputeFinancialRegistryInvariant mapping openingLedger vaultHolder
  initial := fun state => state = initialState ∧ ∀ id, state.disputes id = none
  step := EscrowDisputeFinancialRegistryStep policy escrowPolicy disputePolicy
    mapping vaultHolder expiresAt
  initial_safe := by
    intro state hState
    rcases hState with ⟨rfl, _hNoDisputes⟩
    exact hInitial
  step_safe := by
    intro before after hBefore hStep
    exact escrowDisputeFinancialRegistryStep_preserves_invariant
      policy escrowPolicy disputePolicy mapping openingLedger vaultHolder expiresAt
      hBefore hStep

/-- Every reachable dispute-aware state preserves the timed vault/pool/GL invariant. -/
theorem escrowDisputeFinancialRegistryInvariant_of_reachable
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype EscrowId] [Fintype Holder] [Fintype LedgerAccount]
    [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (disputePolicy : EscrowDisputeAuthorizationPolicy Principal EscrowId Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (openingLedger : Ledger LedgerAccount Asset)
    (vaultHolder : Holder) (expiresAt : EscrowId → Nat)
    (initialState : EscrowDisputeFinancialRegistryState
      Principal EscrowId Holder LedgerAccount Asset)
    (hInitial : EscrowDisputeFinancialRegistryInvariant mapping openingLedger
      vaultHolder initialState)
    (hInitialNoDisputes : ∀ id, initialState.disputes id = none)
    {state : EscrowDisputeFinancialRegistryState
      Principal EscrowId Holder LedgerAccount Asset}
    (hReachable : Reachable
      (escrowDisputeFinancialRegistryMachine policy escrowPolicy disputePolicy
        mapping openingLedger vaultHolder expiresAt initialState hInitial
        hInitialNoDisputes) state) :
    EscrowDisputeFinancialRegistryInvariant mapping openingLedger vaultHolder state :=
  invariant_of_reachable
    (escrowDisputeFinancialRegistryMachine policy escrowPolicy disputePolicy
      mapping openingLedger vaultHolder expiresAt initialState hInitial
      hInitialNoDisputes) hReachable

end SIRM
