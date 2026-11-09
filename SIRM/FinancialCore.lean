import Mathlib

/-!
# SIRM Financial Core — initial formal model

This module is deliberately small. It specifies aggregate token accounting,
not a production bank, a complete ledger, or a consensus protocol.

All quantities are natural-number accounting units. More expressive asset
types, participant accounts, fractional units, fees, and external attestations
will be introduced only with explicit semantics.
-/

namespace SIRM

/-- Aggregate supply accounting. -/
structure SupplyState where
  minted : Nat
  burned : Nat
  outstanding : Nat
  deriving DecidableEq, Repr

/-- The outstanding supply equals cumulative issuance less cumulative burns. -/
def SupplyInvariant (s : SupplyState) : Prop :=
  s.minted = s.burned + s.outstanding

/-- Initial state has no issuance, burns, or outstanding units. -/
def initialSupply : SupplyState :=
  ⟨0, 0, 0⟩

theorem initialSupply_invariant : SupplyInvariant initialSupply := by
  rfl

/-- Minting increases cumulative issuance and outstanding supply equally. -/
def mint (s : SupplyState) (amount : Nat) : SupplyState :=
  ⟨s.minted + amount, s.burned, s.outstanding + amount⟩

/-- Burning reduces outstanding supply and records cumulative destruction. -/
def burn (s : SupplyState) (amount : Nat) : SupplyState :=
  ⟨s.minted, s.burned + amount, s.outstanding - amount⟩

/-- A transfer changes ownership, not aggregate supply. -/
def transfer (s : SupplyState) (_amount : Nat) : SupplyState :=
  s

theorem mint_preserves_invariant
    (s : SupplyState) (h : SupplyInvariant s) (amount : Nat) :
    SupplyInvariant (mint s amount) := by
  unfold SupplyInvariant mint at *
  omega

theorem burn_preserves_invariant
    (s : SupplyState) (h : SupplyInvariant s) (amount : Nat)
    (hAmount : amount ≤ s.outstanding) :
    SupplyInvariant (burn s amount) := by
  unfold SupplyInvariant burn at *
  omega

theorem transfer_preserves_invariant
    (s : SupplyState) (h : SupplyInvariant s) (amount : Nat) :
    SupplyInvariant (transfer s amount) := by
  simpa [transfer] using h

/-- A token allocation is an exact split of a fixed total. -/
structure Allocation where
  total : Nat
  founder : Nat
  treasury : Nat
  ecosystem : Nat
  deriving DecidableEq, Repr

/-- Every unit is assigned exactly once; no units are created by allocation. -/
def AllocationInvariant (a : Allocation) : Prop :=
  a.total = a.founder + a.treasury + a.ecosystem

theorem allocation_invariant_of_parts
    (a : Allocation)
    (h : a.total = a.founder + a.treasury + a.ecosystem) :
    AllocationInvariant a := h

/--
A founder share is represented as basis points, with 10,000 basis points
equal to 100%. No default founder rate is selected by this formal core.
-/
def ValidBasisPoints (bps : Nat) : Prop := bps ≤ 10000

/-- Exact floor allocation in integer accounting units. -/
def shareOf (total bps : Nat) : Nat :=
  total * bps / 10000

theorem shareOf_le_total (total bps : Nat) (h : ValidBasisPoints bps) :
    shareOf total bps ≤ total := by
  unfold shareOf ValidBasisPoints at *
  omega

/-- The unallocated remainder is explicit and never silently discarded. -/
def remainderAfterShare (total bps : Nat) : Nat :=
  total - shareOf total bps

theorem share_plus_remainder (total bps : Nat) (h : ValidBasisPoints bps) :
    shareOf total bps + remainderAfterShare total bps = total := by
  unfold remainderAfterShare
  have hs := shareOf_le_total total bps h
  omega

end SIRM
