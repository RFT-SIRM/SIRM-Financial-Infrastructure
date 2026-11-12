import SIRM.EscrowRegistry

/-!
# Pooled Escrow Reserve Accounting

This layer derives the aggregate outstanding liability of all pending escrow
records, separately for each asset, and models a pooled reserve balance that
must match that aggregate exactly. Opening increases both the pending
obligation and pooled reserve by the same amount. Release and cancellation
reduce both by the selected record's amount. The transition machine preserves
this equality for every reachable state.

Important boundary: this is the aggregate escrow reserve subledger. It does
not yet identify this abstract reserve balance with the concrete
`FinancialState` holder balance or its general-ledger account. That final
reconciliation is intentionally a separate integration layer.
-/

open scoped BigOperators

namespace SIRM

/-- Amount contributed by one registry entry to one asset's pending liability. -/
def pooledEscrowContribution
    {EscrowId Holder Asset : Type} [DecidableEq Asset]
    (registry : EscrowRegistry EscrowId Holder Asset)
    (id : EscrowId) (asset : Asset) : Int :=
  match registry.records id with
  | none => 0
  | some record =>
      if record.phase = EscrowPhase.pending ∧ record.asset = asset
      then (record.amount : Int) else 0

/-- Total outstanding pending escrow liability, aggregated by asset over all IDs. -/
def pooledEscrowReserve
    {EscrowId Holder Asset : Type} [Fintype EscrowId] [DecidableEq Asset]
    (registry : EscrowRegistry EscrowId Holder Asset)
    (asset : Asset) : Int :=
  ∑ id : EscrowId, pooledEscrowContribution registry id asset

/-- Aggregate pending liabilities are nonnegative. -/
theorem pooledEscrowReserve_nonnegative
    {EscrowId Holder Asset : Type} [Fintype EscrowId] [DecidableEq Asset]
    (registry : EscrowRegistry EscrowId Holder Asset) (asset : Asset) :
    0 ≤ pooledEscrowReserve registry asset := by
  classical
  unfold pooledEscrowReserve
  apply Finset.sum_nonneg
  intro id _
  cases hRecord : registry.records id with
  | none => simp [pooledEscrowContribution, hRecord]
  | some record =>
      by_cases hPending : record.phase = EscrowPhase.pending ∧ record.asset = asset
      · simp [pooledEscrowContribution, hRecord, hPending]
      · simp [pooledEscrowContribution, hRecord, hPending]

/-- Inserting a fresh pending record adds exactly its amount to that asset's pool. -/
theorem pooledEscrowReserve_insert
    {EscrowId Holder Asset : Type} [Fintype EscrowId] [DecidableEq EscrowId] [DecidableEq Asset]
    (registry : EscrowRegistry EscrowId Holder Asset)
    (id : EscrowId) (record : EscrowRecord Holder Asset) (asset : Asset)
    (hFresh : registry.records id = none)
    (hPending : record.phase = EscrowPhase.pending) :
    pooledEscrowReserve (escrowRegistryInsert registry id record) asset =
      pooledEscrowReserve registry asset +
        (if record.asset = asset then (record.amount : Int) else 0) := by
  classical
  unfold pooledEscrowReserve
  calc
    (∑ query : EscrowId,
        pooledEscrowContribution (escrowRegistryInsert registry id record) query asset) =
      ∑ query : EscrowId,
        (pooledEscrowContribution registry query asset +
          (if query = id then
            (if record.asset = asset then (record.amount : Int) else 0)
           else 0)) := by
        apply Finset.sum_congr rfl
        intro query _
        by_cases hQuery : query = id
        · subst query
          simp [pooledEscrowContribution, escrowRegistryInsert, hFresh, hPending]
        · simp [pooledEscrowContribution, escrowRegistryInsert, hQuery]
    _ = (∑ query : EscrowId, pooledEscrowContribution registry query asset) +
        (if record.asset = asset then (record.amount : Int) else 0) := by
          rw [Finset.sum_add_distrib]
          simp

/-- Releasing a pending record removes exactly its amount from that asset's pool. -/
theorem pooledEscrowReserve_release
    {EscrowId Holder Asset : Type} [Fintype EscrowId] [DecidableEq EscrowId] [DecidableEq Asset]
    (registry : EscrowRegistry EscrowId Holder Asset)
    (id : EscrowId) (record : EscrowRecord Holder Asset) (asset : Asset)
    (hRecord : registry.records id = some record)
    (hPending : record.phase = EscrowPhase.pending) :
    pooledEscrowReserve (escrowRegistryRelease registry id record) asset =
      pooledEscrowReserve registry asset -
        (if record.asset = asset then (record.amount : Int) else 0) := by
  classical
  unfold pooledEscrowReserve
  calc
    (∑ query : EscrowId,
        pooledEscrowContribution (escrowRegistryRelease registry id record) query asset) =
      ∑ query : EscrowId,
        (pooledEscrowContribution registry query asset -
          (if query = id then
            (if record.asset = asset then (record.amount : Int) else 0)
           else 0)) := by
        apply Finset.sum_congr rfl
        intro query _
        by_cases hQuery : query = id
        · subst query
          simp [pooledEscrowContribution, escrowRegistryRelease, hRecord, hPending]
        · simp [pooledEscrowContribution, escrowRegistryRelease, hQuery]
    _ = (∑ query : EscrowId, pooledEscrowContribution registry query asset) -
        (if record.asset = asset then (record.amount : Int) else 0) := by
          rw [Finset.sum_sub_distrib]
          simp

/-- Cancellation removes exactly the returned pending amount from the pool. -/
theorem pooledEscrowReserve_cancel
    {EscrowId Holder Asset : Type} [Fintype EscrowId] [DecidableEq EscrowId] [DecidableEq Asset]
    (registry : EscrowRegistry EscrowId Holder Asset)
    (id : EscrowId) (record : EscrowRecord Holder Asset) (asset : Asset)
    (hRecord : registry.records id = some record)
    (hPending : record.phase = EscrowPhase.pending) :
    pooledEscrowReserve (escrowRegistryCancel registry id record) asset =
      pooledEscrowReserve registry asset -
        (if record.asset = asset then (record.amount : Int) else 0) := by
  classical
  unfold pooledEscrowReserve
  calc
    (∑ query : EscrowId,
        pooledEscrowContribution (escrowRegistryCancel registry id record) query asset) =
      ∑ query : EscrowId,
        (pooledEscrowContribution registry query asset -
          (if query = id then
            (if record.asset = asset then (record.amount : Int) else 0)
           else 0)) := by
        apply Finset.sum_congr rfl
        intro query _
        by_cases hQuery : query = id
        · subst query
          simp [pooledEscrowContribution, escrowRegistryCancel, hRecord, hPending]
        · simp [pooledEscrowContribution, escrowRegistryCancel, hQuery]
    _ = (∑ query : EscrowId, pooledEscrowContribution registry query asset) -
        (if record.asset = asset then (record.amount : Int) else 0) := by
          rw [Finset.sum_sub_distrib]
          simp

/-- A pooled reserve state stores the registry and the per-asset reserve balance. -/
structure PooledEscrowVaultState (EscrowId Holder Asset : Type) where
  registry : EscrowRegistry EscrowId Holder Asset
  vaultBalance : Asset → Int

/-- Exact aggregate backing: each asset's vault balance equals its pending liability. -/
def PooledEscrowVaultInvariant
    {EscrowId Holder Asset : Type} [Fintype EscrowId] [DecidableEq Asset]
    (state : PooledEscrowVaultState EscrowId Holder Asset) : Prop :=
  EscrowRegistryInvariant state.registry ∧
    ∀ asset, state.vaultBalance asset = pooledEscrowReserve state.registry asset

/-- Exact backing also rules out a negative pooled reserve for every asset. -/
theorem pooledEscrowVaultBalance_nonnegative
    {EscrowId Holder Asset : Type} [Fintype EscrowId] [DecidableEq Asset]
    (state : PooledEscrowVaultState EscrowId Holder Asset)
    (hInvariant : PooledEscrowVaultInvariant state) (asset : Asset) :
    0 ≤ state.vaultBalance asset := by
  rw [hInvariant.2 asset]
  exact pooledEscrowReserve_nonnegative state.registry asset

/-- Open one fresh ID and reserve its amount in the pooled vault. -/
def pooledEscrowVaultOpen
    {EscrowId Holder Asset : Type} [DecidableEq EscrowId] [DecidableEq Asset]
    (before : PooledEscrowVaultState EscrowId Holder Asset)
    (id : EscrowId) (record : EscrowRecord Holder Asset) :
    PooledEscrowVaultState EscrowId Holder Asset :=
  { registry := escrowRegistryInsert before.registry id record
    vaultBalance := fun asset => before.vaultBalance asset +
      (if record.asset = asset then (record.amount : Int) else 0) }

/-- Release one pending ID and remove its amount from the pooled vault. -/
def pooledEscrowVaultRelease
    {EscrowId Holder Asset : Type} [DecidableEq EscrowId] [DecidableEq Asset]
    (before : PooledEscrowVaultState EscrowId Holder Asset)
    (id : EscrowId) (record : EscrowRecord Holder Asset) :
    PooledEscrowVaultState EscrowId Holder Asset :=
  { registry := escrowRegistryRelease before.registry id record
    vaultBalance := fun asset => before.vaultBalance asset -
      (if record.asset = asset then (record.amount : Int) else 0) }

/-- Cancel one pending ID and remove its returned amount from the pooled vault. -/
def pooledEscrowVaultCancel
    {EscrowId Holder Asset : Type} [DecidableEq EscrowId] [DecidableEq Asset]
    (before : PooledEscrowVaultState EscrowId Holder Asset)
    (id : EscrowId) (record : EscrowRecord Holder Asset) :
    PooledEscrowVaultState EscrowId Holder Asset :=
  { registry := escrowRegistryCancel before.registry id record
    vaultBalance := fun asset => before.vaultBalance asset -
      (if record.asset = asset then (record.amount : Int) else 0) }

/-- Open requires a never-used identifier, a pending record, and a positive amount. -/
def PooledEscrowVaultOpenStep
    {EscrowId Holder Asset : Type} [DecidableEq EscrowId] [DecidableEq Asset]
    (before after : PooledEscrowVaultState EscrowId Holder Asset) : Prop :=
  ∃ id record,
    before.registry.records id = none ∧
    record.phase = EscrowPhase.pending ∧
    0 < record.amount ∧
    after = pooledEscrowVaultOpen before id record

/-- Release requires an existing pending ID. -/
def PooledEscrowVaultReleaseStep
    {EscrowId Holder Asset : Type} [DecidableEq EscrowId] [DecidableEq Asset]
    (before after : PooledEscrowVaultState EscrowId Holder Asset) : Prop :=
  ∃ id record,
    before.registry.records id = some record ∧
    record.phase = EscrowPhase.pending ∧
    after = pooledEscrowVaultRelease before id record

/-- Cancellation requires an existing pending ID. -/
def PooledEscrowVaultCancelStep
    {EscrowId Holder Asset : Type} [DecidableEq EscrowId] [DecidableEq Asset]
    (before after : PooledEscrowVaultState EscrowId Holder Asset) : Prop :=
  ∃ id record,
    before.registry.records id = some record ∧
    record.phase = EscrowPhase.pending ∧
    after = pooledEscrowVaultCancel before id record

/-- Complete pooled reserve transition relation. -/
def PooledEscrowVaultStep
    {EscrowId Holder Asset : Type} [DecidableEq EscrowId] [DecidableEq Asset]
    (before after : PooledEscrowVaultState EscrowId Holder Asset) : Prop :=
  PooledEscrowVaultOpenStep before after ∨
    PooledEscrowVaultReleaseStep before after ∨
    PooledEscrowVaultCancelStep before after

/-- Opening preserves exact pooled backing and registry validity. -/
theorem pooledEscrowVaultOpen_preserves_invariant
    {EscrowId Holder Asset : Type} [Fintype EscrowId] [DecidableEq EscrowId] [DecidableEq Asset]
    {before after : PooledEscrowVaultState EscrowId Holder Asset}
    (hBefore : PooledEscrowVaultInvariant before)
    (hStep : PooledEscrowVaultOpenStep before after) :
    PooledEscrowVaultInvariant after := by
  rcases hStep with ⟨id, record, hFresh, hPending, hPositive, hAfter⟩
  subst after
  refine ⟨escrowRegistryInsert_preserves_invariant before.registry id record
    hBefore.1 hFresh hPending hPositive, ?_⟩
  intro asset
  change before.vaultBalance asset +
    (if record.asset = asset then (record.amount : Int) else 0) =
    pooledEscrowReserve (escrowRegistryInsert before.registry id record) asset
  rw [hBefore.2 asset]
  exact (pooledEscrowReserve_insert before.registry id record asset hFresh hPending).symm

/-- Releasing preserves exact pooled backing and the validity of every registry entry. -/
theorem pooledEscrowVaultRelease_preserves_invariant
    {EscrowId Holder Asset : Type} [Fintype EscrowId] [DecidableEq EscrowId] [DecidableEq Asset]
    {before after : PooledEscrowVaultState EscrowId Holder Asset}
    (hBefore : PooledEscrowVaultInvariant before)
    (hStep : PooledEscrowVaultReleaseStep before after) :
    PooledEscrowVaultInvariant after := by
  rcases hStep with ⟨id, record, hRecord, hPending, hAfter⟩
  subst after
  refine ⟨escrowRegistryRelease_preserves_invariant before.registry id record
    hBefore.1 hRecord hPending, ?_⟩
  intro asset
  change before.vaultBalance asset -
    (if record.asset = asset then (record.amount : Int) else 0) =
    pooledEscrowReserve (escrowRegistryRelease before.registry id record) asset
  rw [hBefore.2 asset]
  exact (pooledEscrowReserve_release before.registry id record asset hRecord hPending).symm

/-- Cancellation preserves exact pooled backing and registry validity. -/
theorem pooledEscrowVaultCancel_preserves_invariant
    {EscrowId Holder Asset : Type} [Fintype EscrowId] [DecidableEq EscrowId] [DecidableEq Asset]
    {before after : PooledEscrowVaultState EscrowId Holder Asset}
    (hBefore : PooledEscrowVaultInvariant before)
    (hStep : PooledEscrowVaultCancelStep before after) :
    PooledEscrowVaultInvariant after := by
  rcases hStep with ⟨id, record, hRecord, hPending, hAfter⟩
  subst after
  refine ⟨escrowRegistryCancel_preserves_invariant before.registry id record
    hBefore.1 hRecord hPending, ?_⟩
  intro asset
  change before.vaultBalance asset -
    (if record.asset = asset then (record.amount : Int) else 0) =
    pooledEscrowReserve (escrowRegistryCancel before.registry id record) asset
  rw [hBefore.2 asset]
  exact (pooledEscrowReserve_cancel before.registry id record asset hRecord hPending).symm

/-- Every pooled escrow operation preserves the exact aggregate backing invariant. -/
theorem pooledEscrowVaultStep_preserves_invariant
    {EscrowId Holder Asset : Type} [Fintype EscrowId] [DecidableEq EscrowId] [DecidableEq Asset]
    {before after : PooledEscrowVaultState EscrowId Holder Asset}
    (hBefore : PooledEscrowVaultInvariant before)
    (hStep : PooledEscrowVaultStep before after) :
    PooledEscrowVaultInvariant after := by
  rcases hStep with hOpen | hRest
  · exact pooledEscrowVaultOpen_preserves_invariant hBefore hOpen
  · rcases hRest with hRelease | hCancel
    · exact pooledEscrowVaultRelease_preserves_invariant hBefore hRelease
    · exact pooledEscrowVaultCancel_preserves_invariant hBefore hCancel

/-- Verified machine for pooled reserve operations. -/
def pooledEscrowVaultMachine
    {EscrowId Holder Asset : Type} [Fintype EscrowId] [DecidableEq EscrowId] [DecidableEq Asset]
    (initialState : PooledEscrowVaultState EscrowId Holder Asset)
    (hInitial : PooledEscrowVaultInvariant initialState) :
    VerifiedStateMachine (PooledEscrowVaultState EscrowId Holder Asset) where
  invariant := PooledEscrowVaultInvariant
  initial := fun state => state = initialState
  step := PooledEscrowVaultStep
  initial_safe := by
    intro state hState
    subst state
    exact hInitial
  step_safe := by
    intro before after hBefore hStep
    exact pooledEscrowVaultStep_preserves_invariant hBefore hStep

/-- Every state reachable from a correctly backed pooled reserve remains exactly backed. -/
theorem pooledEscrowVaultInvariant_of_reachable
    {EscrowId Holder Asset : Type} [Fintype EscrowId] [DecidableEq EscrowId] [DecidableEq Asset]
    (initialState : PooledEscrowVaultState EscrowId Holder Asset)
    (hInitial : PooledEscrowVaultInvariant initialState)
    {state : PooledEscrowVaultState EscrowId Holder Asset}
    (hReachable : Reachable (pooledEscrowVaultMachine initialState hInitial) state) :
    PooledEscrowVaultInvariant state :=
  invariant_of_reachable (pooledEscrowVaultMachine initialState hInitial) hReachable

end SIRM
