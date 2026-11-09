import Mathlib

/-!
# SIRM Financial Core

The normative first layer of the SIRM financial specification.
All amounts are integer base units. This module deliberately separates
supply accounting from signed double-entry bookkeeping (see `SIRM.Accounting`).
-/

namespace SIRM

/-- Cumulative issuance, cumulative destruction, and currently outstanding units. -/
structure SupplyState where
  minted : Nat
  burned : Nat
  outstanding : Nat
  deriving DecidableEq, Repr

/-- The supply book reconciles exactly: issued = burned + outstanding. -/
def SupplyInvariant (s : SupplyState) : Prop :=
  s.minted = s.burned + s.outstanding

/-- Empty supply is a valid initial state. -/
def initialSupply : SupplyState := ⟨0, 0, 0⟩

theorem initialSupply_invariant : SupplyInvariant initialSupply := by
  rfl

/-- Minting increases cumulative issuance and outstanding units equally. -/
def mint (s : SupplyState) (amount : Nat) : SupplyState :=
  ⟨s.minted + amount, s.burned, s.outstanding + amount⟩

theorem mint_preserves_invariant (s : SupplyState)
    (h : SupplyInvariant s) (amount : Nat) :
    SupplyInvariant (mint s amount) := by
  change s.minted + amount = s.burned + (s.outstanding + amount)
  change s.minted = s.burned + s.outstanding at h
  omega

/-- Burning is defined only for units that are currently outstanding. -/
def burn (s : SupplyState) (amount : Nat) : SupplyState :=
  ⟨s.minted, s.burned + amount, s.outstanding - amount⟩

theorem burn_preserves_invariant (s : SupplyState)
    (h : SupplyInvariant s) (amount : Nat)
    (hAmount : amount ≤ s.outstanding) :
    SupplyInvariant (burn s amount) := by
  change s.minted = (s.burned + amount) + (s.outstanding - amount)
  change s.minted = s.burned + s.outstanding at h
  omega

/-- One million parts per million represent 100 percent. -/
def ppmScale : Nat := 1_000_000

/-- One-time founder genesis allocation: 1.309%, replacing the legacy 3.14%. -/
def founderRatePpm : Nat := 13_090

theorem founderRate_valid : founderRatePpm ≤ ppmScale := by
  norm_num [founderRatePpm, ppmScale]

/-- Exact integer identity for the selected 1.309% rate. -/
theorem founderRate_exact :
    founderRatePpm * 100_000 = ppmScale * 1_309 := by
  norm_num [founderRatePpm, ppmScale]

/-- Founder units are rounded down in the smallest token accounting unit. -/
def founderAllocation (genesisSupply : Nat) : Nat :=
  genesisSupply * founderRatePpm / ppmScale

/-- The founder allocation cannot exceed the genesis supply. -/
theorem founderAllocation_le_genesisSupply (genesisSupply : Nat) :
    founderAllocation genesisSupply ≤ genesisSupply := by
  have hRate : founderRatePpm ≤ ppmScale := founderRate_valid
  unfold founderAllocation
  calc
    genesisSupply * founderRatePpm / ppmScale ≤
        genesisSupply * ppmScale / ppmScale :=
      Nat.div_le_div_right (Nat.mul_le_mul_left genesisSupply hRate)
    _ = genesisSupply := by
      simp [ppmScale]

/-- Everything not assigned to the founder remains explicit, not implicitly issued. -/
def remainingGenesisPool (genesisSupply : Nat) : Nat :=
  genesisSupply - founderAllocation genesisSupply

theorem founderAllocation_plus_remaining (genesisSupply : Nat) :
    founderAllocation genesisSupply + remainingGenesisPool genesisSupply =
      genesisSupply := by
  unfold remainingGenesisPool
  rw [Nat.add_comm]
  exact Nat.sub_add_cancel (founderAllocation_le_genesisSupply genesisSupply)

/-- Genesis allocation categories. Unspecified pools remain explicitly unallocated. -/
structure GenesisAllocation where
  total : Nat
  founder : Nat
  treasury : Nat
  validatorPool : Nat
  ecosystemPool : Nat
  unallocated : Nat
  deriving DecidableEq, Repr

/-- Each genesis unit is assigned exactly once. -/
def GenesisAllocationInvariant (a : GenesisAllocation) : Prop :=
  a.total = a.founder + a.treasury + a.validatorPool + a.ecosystemPool + a.unallocated

/-- Initial policy assigns 1.309% to the founder and leaves all other units unallocated. -/
def initialGenesisAllocation (total : Nat) : GenesisAllocation :=
  { total := total
    founder := founderAllocation total
    treasury := 0
    validatorPool := 0
    ecosystemPool := 0
    unallocated := remainingGenesisPool total }

theorem initialGenesisAllocation_balanced (total : Nat) :
    GenesisAllocationInvariant (initialGenesisAllocation total) := by
  change total = founderAllocation total + 0 + 0 + 0 + remainingGenesisPool total
  simp only [Nat.add_zero]
  exact (founderAllocation_plus_remaining total).symm

end SIRM
