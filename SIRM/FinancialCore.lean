import Mathlib

/-! # SIRM Financial Core -/

namespace SIRM

structure SupplyState where
  minted : Nat
  burned : Nat
  outstanding : Nat
  deriving DecidableEq, Repr

def SupplyInvariant (s : SupplyState) : Prop :=
  s.minted = s.burned + s.outstanding

def initialSupply : SupplyState := ⟨0, 0, 0⟩

theorem initialSupply_invariant : SupplyInvariant initialSupply := by
  rfl

def mint (s : SupplyState) (amount : Nat) : SupplyState :=
  ⟨s.minted + amount, s.burned, s.outstanding + amount⟩

def burn (s : SupplyState) (amount : Nat) : SupplyState :=
  ⟨s.minted, s.burned + amount, s.outstanding - amount⟩

def transfer (s : SupplyState) (_amount : Nat) : SupplyState := s

theorem mint_preserves_invariant (s : SupplyState)
    (h : SupplyInvariant s) (amount : Nat) :
    SupplyInvariant (mint s amount) := by
  unfold SupplyInvariant mint at *
  omega

theorem burn_preserves_invariant (s : SupplyState)
    (h : SupplyInvariant s) (amount : Nat)
    (hAmount : amount ≤ s.outstanding) :
    SupplyInvariant (burn s amount) := by
  unfold SupplyInvariant burn at *
  omega

theorem transfer_preserves_invariant (s : SupplyState)
    (h : SupplyInvariant s) (amount : Nat) :
    SupplyInvariant (transfer s amount) := by
  simpa [transfer] using h

/-- One million parts per million equal 100%. -/
def ppmScale : Nat := 1_000_000

/-- Creator allocation at genesis: exactly 1.309%, replacing 3.14%. -/
def founderRatePpm : Nat := 13_090

theorem founderRate_valid : founderRatePpm ≤ ppmScale := by
  norm_num [founderRatePpm, ppmScale]

theorem founderRate_exact :
    founderRatePpm * 100_000 = ppmScale * 1_309 := by
  norm_num [founderRatePpm, ppmScale]

/-- Integer floor allocation in the smallest token accounting unit. -/
def founderAllocation (genesisSupply : Nat) : Nat :=
  genesisSupply * founderRatePpm / ppmScale

def remainingGenesisPool (genesisSupply : Nat) : Nat :=
  genesisSupply - founderAllocation genesisSupply

theorem founderAllocation_le_genesisSupply (genesisSupply : Nat) :
    founderAllocation genesisSupply ≤ genesisSupply := by
  unfold founderAllocation founderRatePpm ppmScale
  omega

theorem founderAllocation_plus_remaining (genesisSupply : Nat) :
    founderAllocation genesisSupply + remainingGenesisPool genesisSupply =
      genesisSupply := by
  unfold remainingGenesisPool
  omega

end SIRM
