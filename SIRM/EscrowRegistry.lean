import SIRM.EscrowAccounting

/-!
# Multi-record Escrow Registry

This module adds the registry/lifecycle layer on top of the single-record
financial escrow primitive. A registry is indexed by escrow IDs, so two
records can coexist without overwriting one another. Opening requires an
unused ID; release and cancellation require that the selected record is
pending. Terminal records remain stored, making an ID permanently non-reusable.

The module proves a registry invariant, preservation under every registry
transition, frame properties for non-target IDs, and reachability safety.
The registry relation is not itself an externally callable settlement API:
existing authorization and balance movement remain in EscrowAccounting.

Scope boundary: this module does not yet connect several records to one pooled
vault balance. It proves independent registry semantics only. Aggregate
financial backing for concurrent records is a separate subsequent layer.
-/

namespace SIRM

/-- Registry of escrow records, keyed by a caller-defined unique identifier. -/
structure EscrowRegistry (EscrowId Holder Asset : Type) where
  records : EscrowId → Option (EscrowRecord Holder Asset)

/-- Empty registry: no escrow identifier has ever been allocated. -/
def emptyEscrowRegistry {EscrowId Holder Asset : Type} :
    EscrowRegistry EscrowId Holder Asset :=
  ⟨fun _ => none⟩

/-- Insert a new pending record at an unused identifier. -/
def escrowRegistryInsert
    {EscrowId Holder Asset : Type} [DecidableEq EscrowId]
    (before : EscrowRegistry EscrowId Holder Asset)
    (id : EscrowId) (record : EscrowRecord Holder Asset) :
    EscrowRegistry EscrowId Holder Asset :=
  ⟨fun query => if query = id then some record else before.records query⟩

/-- Mark exactly one pending record as released; all its terms stay immutable. -/
def escrowRegistryRelease
    {EscrowId Holder Asset : Type} [DecidableEq EscrowId]
    (before : EscrowRegistry EscrowId Holder Asset)
    (id : EscrowId) (record : EscrowRecord Holder Asset) :
    EscrowRegistry EscrowId Holder Asset :=
  ⟨fun query =>
    if query = id then some { record with phase := EscrowPhase.released }
    else before.records query⟩

/-- Mark exactly one pending record as cancelled; all its terms stay immutable. -/
def escrowRegistryCancel
    {EscrowId Holder Asset : Type} [DecidableEq EscrowId]
    (before : EscrowRegistry EscrowId Holder Asset)
    (id : EscrowId) (record : EscrowRecord Holder Asset) :
    EscrowRegistry EscrowId Holder Asset :=
  ⟨fun query =>
    if query = id then some { record with phase := EscrowPhase.cancelled }
    else before.records query⟩

/-- Every registered record is non-ready and has a strictly positive amount. -/
def EscrowRegistryInvariant
    {EscrowId Holder Asset : Type}
    (registry : EscrowRegistry EscrowId Holder Asset) : Prop :=
  ∀ id record, registry.records id = some record →
    record.phase ≠ EscrowPhase.ready ∧ 0 < record.amount

/-- Open a fresh ID with a positive pending record. -/
def EscrowRegistryOpenStep
    {EscrowId Holder Asset : Type} [DecidableEq EscrowId]
    (before after : EscrowRegistry EscrowId Holder Asset) : Prop :=
  ∃ id record,
    before.records id = none ∧
    record.phase = EscrowPhase.pending ∧
    0 < record.amount ∧
    after = escrowRegistryInsert before id record

/-- Release is permitted only for an existing pending record. -/
def EscrowRegistryReleaseStep
    {EscrowId Holder Asset : Type} [DecidableEq EscrowId]
    (before after : EscrowRegistry EscrowId Holder Asset) : Prop :=
  ∃ id record,
    before.records id = some record ∧
    record.phase = EscrowPhase.pending ∧
    after = escrowRegistryRelease before id record

/-- Cancellation is permitted only for an existing pending record. -/
def EscrowRegistryCancelStep
    {EscrowId Holder Asset : Type} [DecidableEq EscrowId]
    (before after : EscrowRegistry EscrowId Holder Asset) : Prop :=
  ∃ id record,
    before.records id = some record ∧
    record.phase = EscrowPhase.pending ∧
    after = escrowRegistryCancel before id record

/-- The complete multi-record registry transition relation. -/
def EscrowRegistryStep
    {EscrowId Holder Asset : Type} [DecidableEq EscrowId]
    (before after : EscrowRegistry EscrowId Holder Asset) : Prop :=
  EscrowRegistryOpenStep before after ∨
    EscrowRegistryReleaseStep before after ∨
    EscrowRegistryCancelStep before after

@[simp] theorem escrowRegistryInsert_at
    {EscrowId Holder Asset : Type} [DecidableEq EscrowId]
    (before : EscrowRegistry EscrowId Holder Asset)
    (id : EscrowId) (record : EscrowRecord Holder Asset) :
    (escrowRegistryInsert before id record).records id = some record := by
  simp [escrowRegistryInsert]

theorem escrowRegistryInsert_other
    {EscrowId Holder Asset : Type} [DecidableEq EscrowId]
    (before : EscrowRegistry EscrowId Holder Asset)
    (id other : EscrowId) (record : EscrowRecord Holder Asset)
    (hDifferent : other ≠ id) :
    (escrowRegistryInsert before id record).records other = before.records other := by
  simp [escrowRegistryInsert, hDifferent]

@[simp] theorem escrowRegistryRelease_at
    {EscrowId Holder Asset : Type} [DecidableEq EscrowId]
    (before : EscrowRegistry EscrowId Holder Asset)
    (id : EscrowId) (record : EscrowRecord Holder Asset) :
    (escrowRegistryRelease before id record).records id =
      some { record with phase := EscrowPhase.released } := by
  simp [escrowRegistryRelease]

theorem escrowRegistryRelease_other
    {EscrowId Holder Asset : Type} [DecidableEq EscrowId]
    (before : EscrowRegistry EscrowId Holder Asset)
    (id other : EscrowId) (record : EscrowRecord Holder Asset)
    (hDifferent : other ≠ id) :
    (escrowRegistryRelease before id record).records other =
      before.records other := by
  simp [escrowRegistryRelease, hDifferent]

@[simp] theorem escrowRegistryCancel_at
    {EscrowId Holder Asset : Type} [DecidableEq EscrowId]
    (before : EscrowRegistry EscrowId Holder Asset)
    (id : EscrowId) (record : EscrowRecord Holder Asset) :
    (escrowRegistryCancel before id record).records id =
      some { record with phase := EscrowPhase.cancelled } := by
  simp [escrowRegistryCancel]

theorem escrowRegistryCancel_other
    {EscrowId Holder Asset : Type} [DecidableEq EscrowId]
    (before : EscrowRegistry EscrowId Holder Asset)
    (id other : EscrowId) (record : EscrowRecord Holder Asset)
    (hDifferent : other ≠ id) :
    (escrowRegistryCancel before id record).records other =
      before.records other := by
  simp [escrowRegistryCancel, hDifferent]

/-- Inserting one valid pending record preserves validity of all registry entries. -/
theorem escrowRegistryInsert_preserves_invariant
    {EscrowId Holder Asset : Type} [DecidableEq EscrowId]
    (before : EscrowRegistry EscrowId Holder Asset)
    (id : EscrowId) (record : EscrowRecord Holder Asset)
    (hBefore : EscrowRegistryInvariant before)
    (_hFresh : before.records id = none)
    (hPending : record.phase = EscrowPhase.pending)
    (hPositive : 0 < record.amount) :
    EscrowRegistryInvariant (escrowRegistryInsert before id record) := by
  intro query found hFound
  by_cases hQuery : query = id
  · subst query
    have hSome : some record = some found := by
      simpa [escrowRegistryInsert] using hFound
    have hRecord : record = found := Option.some.inj hSome
    subst found
    exact ⟨by simp [hPending], hPositive⟩
  · have hOld : before.records query = some found := by
      simpa [escrowRegistryInsert, hQuery] using hFound
    exact hBefore query found hOld

/-- Releasing a record preserves validity and leaves every other ID unchanged. -/
theorem escrowRegistryRelease_preserves_invariant
    {EscrowId Holder Asset : Type} [DecidableEq EscrowId]
    (before : EscrowRegistry EscrowId Holder Asset)
    (id : EscrowId) (record : EscrowRecord Holder Asset)
    (hBefore : EscrowRegistryInvariant before)
    (hRecord : before.records id = some record)
    (_hPending : record.phase = EscrowPhase.pending) :
    EscrowRegistryInvariant (escrowRegistryRelease before id record) := by
  intro query found hFound
  by_cases hQuery : query = id
  · subst query
    have hSome :
        some { record with phase := EscrowPhase.released } = some found := by
      simpa [escrowRegistryRelease] using hFound
    have hRecord' : { record with phase := EscrowPhase.released } = found :=
      Option.some.inj hSome
    subst found
    exact ⟨by simp, (hBefore id record hRecord).2⟩
  · have hOld : before.records query = some found := by
      simpa [escrowRegistryRelease, hQuery] using hFound
    exact hBefore query found hOld

/-- Cancelling a record preserves validity and leaves every other ID unchanged. -/
theorem escrowRegistryCancel_preserves_invariant
    {EscrowId Holder Asset : Type} [DecidableEq EscrowId]
    (before : EscrowRegistry EscrowId Holder Asset)
    (id : EscrowId) (record : EscrowRecord Holder Asset)
    (hBefore : EscrowRegistryInvariant before)
    (hRecord : before.records id = some record)
    (_hPending : record.phase = EscrowPhase.pending) :
    EscrowRegistryInvariant (escrowRegistryCancel before id record) := by
  intro query found hFound
  by_cases hQuery : query = id
  · subst query
    have hSome :
        some { record with phase := EscrowPhase.cancelled } = some found := by
      simpa [escrowRegistryCancel] using hFound
    have hRecord' : { record with phase := EscrowPhase.cancelled } = found :=
      Option.some.inj hSome
    subst found
    exact ⟨by simp, (hBefore id record hRecord).2⟩
  · have hOld : before.records query = some found := by
      simpa [escrowRegistryCancel, hQuery] using hFound
    exact hBefore query found hOld

/-- Every registry transition preserves the registry invariant. -/
theorem escrowRegistryStep_preserves_invariant
    {EscrowId Holder Asset : Type} [DecidableEq EscrowId]
    {before after : EscrowRegistry EscrowId Holder Asset}
    (hBefore : EscrowRegistryInvariant before)
    (hStep : EscrowRegistryStep before after) :
    EscrowRegistryInvariant after := by
  rcases hStep with hOpen | hRest
  · rcases hOpen with ⟨id, record, hFresh, hPending, hPositive, hEq⟩
    subst after
    exact escrowRegistryInsert_preserves_invariant
      before id record hBefore hFresh hPending hPositive
  · rcases hRest with hRelease | hCancel
    · rcases hRelease with ⟨id, record, hRecord, hPending, hEq⟩
      subst after
      exact escrowRegistryRelease_preserves_invariant
        before id record hBefore hRecord hPending
    · rcases hCancel with ⟨id, record, hRecord, hPending, hEq⟩
      subst after
      exact escrowRegistryCancel_preserves_invariant
        before id record hBefore hRecord hPending

/-- A registered identifier is occupied and cannot be used as a fresh ID again. -/
theorem escrowRegistry_registered_id_not_free
    {EscrowId Holder Asset : Type}
    (registry : EscrowRegistry EscrowId Holder Asset)
    (id : EscrowId) (record : EscrowRecord Holder Asset)
    (hRegistered : registry.records id = some record) :
    registry.records id ≠ none := by
  simp [hRegistered]

/-- The registry state machine admits only valid open/release/cancel transitions. -/
def escrowRegistryMachine
    {EscrowId Holder Asset : Type} [DecidableEq EscrowId]
    (initialState : EscrowRegistry EscrowId Holder Asset)
    (hInitial : EscrowRegistryInvariant initialState) :
    VerifiedStateMachine (EscrowRegistry EscrowId Holder Asset) where
  invariant := EscrowRegistryInvariant
  initial := fun state => state = initialState
  step := EscrowRegistryStep
  initial_safe := by
    intro state hState
    subst state
    exact hInitial
  step_safe := by
    intro before after hBefore hStep
    exact escrowRegistryStep_preserves_invariant hBefore hStep

/-- Every reachable multi-record registry state satisfies the registry invariant. -/
theorem escrowRegistryInvariant_of_reachable
    {EscrowId Holder Asset : Type} [DecidableEq EscrowId]
    (initialState : EscrowRegistry EscrowId Holder Asset)
    (hInitial : EscrowRegistryInvariant initialState)
    {state : EscrowRegistry EscrowId Holder Asset}
    (hReachable :
      Reachable (escrowRegistryMachine initialState hInitial) state) :
    EscrowRegistryInvariant state :=
  invariant_of_reachable (escrowRegistryMachine initialState hInitial) hReachable

end SIRM
