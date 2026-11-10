import SIRM.AssetUnits

/-!
# Exact Cross-Network Asset Migration Arithmetic

A rate is stated in target base units per source base unit. Applying it uses
integer quotient/remainder arithmetic only. The remainder is retained as a
fraction of one target base unit; it is never silently rounded away.

A dust accumulator is indexed by both the exact rate and an accounting
partition (for example, one beneficiary or one explicitly governed pool).
This prevents accidental mixing of residuals from different rates or
partitions. Choosing a shared partition is an explicit policy decision.

This module formalizes arithmetic and route eligibility, not a complete
production migration transaction, authorization, burn/mint posting, replay
protection, or external bridge security.
-/

namespace SIRM

/-- Positive rational conversion rate: target base units per source base unit. -/
structure AssetMigrationRate where
  numerator : Nat
  denominator : Nat
  numerator_pos : 0 < numerator
  denominator_pos : 0 < denominator

/-- Exact quotient/remainder decomposition for one source amount. -/
structure AssetMigrationConversion
    (rate : AssetMigrationRate)
    (sourceBaseUnits : Nat) where
  targetBaseUnits : Nat
  dustNumerator : Nat
  scaled_conservation :
    sourceBaseUnits * rate.numerator =
      targetBaseUnits * rate.denominator + dustNumerator
  dust_lt_denominator : dustNumerator < rate.denominator

namespace AssetMigrationRate

/--
Apply the rate to a source amount. The target amount is the quotient and the
remainder is kept in numerator units over `rate.denominator`.
-/
def convert
    (rate : AssetMigrationRate)
    (sourceBaseUnits : Nat) :
    AssetMigrationConversion rate sourceBaseUnits := by
  refine
    { targetBaseUnits :=
        (sourceBaseUnits * rate.numerator) / rate.denominator
      dustNumerator :=
        (sourceBaseUnits * rate.numerator) % rate.denominator
      scaled_conservation := ?_
      dust_lt_denominator :=
        Nat.mod_lt _ rate.denominator_pos }
  calc
    sourceBaseUnits * rate.numerator =
        (sourceBaseUnits * rate.numerator) % rate.denominator +
          rate.denominator *
            ((sourceBaseUnits * rate.numerator) / rate.denominator) :=
      (Nat.mod_add_div _ _).symm
    _ =
        ((sourceBaseUnits * rate.numerator) / rate.denominator) *
          rate.denominator +
          (sourceBaseUnits * rate.numerator) % rate.denominator := by
      ac_rfl

end AssetMigrationRate

/--
Cumulative migration arithmetic for one rate and one accounting partition.
The fraction `dustNumerator / rate.denominator` is the exact fractional
target-base-unit remainder carried forward. The partition index prevents accidental reuse of
one beneficiary's dust in another beneficiary's accumulator.
-/
structure AssetMigrationDustState
    (rate : AssetMigrationRate)
    (Partition : Type)
    (partition : Partition) where
  totalSourceBaseUnits : Nat
  totalTargetBaseUnits : Nat
  dustNumerator : Nat
  dust_lt_denominator : dustNumerator < rate.denominator
  scaled_conservation :
    totalSourceBaseUnits * rate.numerator =
      totalTargetBaseUnits * rate.denominator + dustNumerator

namespace AssetMigrationDustState

/-- Empty accumulator with no source, target, or residual value. -/
def empty
    (rate : AssetMigrationRate)
    {Partition : Type}
    (partition : Partition) :
    AssetMigrationDustState rate Partition partition :=
  { totalSourceBaseUnits := 0
    totalTargetBaseUnits := 0
    dustNumerator := 0
    dust_lt_denominator := rate.denominator_pos
    scaled_conservation := by simp }

/--
Add source base units, release any newly completed target base units, and
carry the exact residual numerator into the next operation.
-/
def addSource
    {rate : AssetMigrationRate}
    {Partition : Type}
    {partition : Partition}
    (state : AssetMigrationDustState rate Partition partition)
    (sourceBaseUnits : Nat) :
    AssetMigrationDustState rate Partition partition := by
  have hSplit :
      state.dustNumerator + sourceBaseUnits * rate.numerator =
        (state.dustNumerator + sourceBaseUnits * rate.numerator) /
            rate.denominator * rate.denominator +
          (state.dustNumerator + sourceBaseUnits * rate.numerator) %
            rate.denominator := by
    calc
      _ =
          (state.dustNumerator + sourceBaseUnits * rate.numerator) %
              rate.denominator +
            rate.denominator *
              ((state.dustNumerator + sourceBaseUnits * rate.numerator) /
                rate.denominator) :=
        (Nat.mod_add_div _ _).symm
      _ = _ := by ac_rfl
  refine
    { totalSourceBaseUnits := state.totalSourceBaseUnits + sourceBaseUnits
      totalTargetBaseUnits :=
        state.totalTargetBaseUnits +
          (state.dustNumerator + sourceBaseUnits * rate.numerator) /
            rate.denominator
      dustNumerator :=
        (state.dustNumerator + sourceBaseUnits * rate.numerator) %
          rate.denominator
      dust_lt_denominator := Nat.mod_lt _ rate.denominator_pos
      scaled_conservation := ?_ }
  calc
    (state.totalSourceBaseUnits + sourceBaseUnits) * rate.numerator =
        state.totalSourceBaseUnits * rate.numerator +
          sourceBaseUnits * rate.numerator := by ring
    _ = state.totalTargetBaseUnits * rate.denominator +
          (state.dustNumerator + sourceBaseUnits * rate.numerator) := by
      rw [state.scaled_conservation]
      ring
    _ = state.totalTargetBaseUnits * rate.denominator +
          ((state.dustNumerator + sourceBaseUnits * rate.numerator) /
              rate.denominator * rate.denominator +
            (state.dustNumerator + sourceBaseUnits * rate.numerator) %
              rate.denominator) := by
      exact congrArg
        (fun residual : Nat =>
          state.totalTargetBaseUnits * rate.denominator + residual)
        hSplit
    _ =
        (state.totalTargetBaseUnits +
            (state.dustNumerator + sourceBaseUnits * rate.numerator) /
              rate.denominator) * rate.denominator +
          (state.dustNumerator + sourceBaseUnits * rate.numerator) %
            rate.denominator := by ring

end AssetMigrationDustState

/--
A proposed route connects two distinct registered assets on different
networks. Its rate is explicit and denominated in target/source base units.
-/
structure AssetMigrationRoute
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    (registry : AssetRegistry accountCount assetCount accounts) where
  sourceAsset : AssetId assetCount
  destinationAsset : AssetId assetCount
  rate : AssetMigrationRate
  assets_distinct : sourceAsset ≠ destinationAsset
  networks_distinct :
    (registry.metadata sourceAsset).network ≠
      (registry.metadata destinationAsset).network

namespace AssetMigrationRoute

/-- Both ends of a route must be active and have active issuers. -/
def endpointsEnabled
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    {registry : AssetRegistry accountCount assetCount accounts}
    (route : AssetMigrationRoute registry) : Prop :=
  registry.issuanceEnabled route.sourceAsset ∧
    registry.issuanceEnabled route.destinationAsset

theorem endpointsEnabled_source_active
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    {registry : AssetRegistry accountCount assetCount accounts}
    (route : AssetMigrationRoute registry)
    (h : route.endpointsEnabled) :
    registry.isActive route.sourceAsset :=
  h.1.1

theorem endpointsEnabled_source_issuer_active
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    {registry : AssetRegistry accountCount assetCount accounts}
    (route : AssetMigrationRoute registry)
    (h : route.endpointsEnabled) :
    AccountRegistry.isActive accounts
      (registry.metadata route.sourceAsset).issuer :=
  h.1.2

theorem endpointsEnabled_destination_active
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    {registry : AssetRegistry accountCount assetCount accounts}
    (route : AssetMigrationRoute registry)
    (h : route.endpointsEnabled) :
    registry.isActive route.destinationAsset :=
  h.2.1

theorem endpointsEnabled_destination_issuer_active
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    {registry : AssetRegistry accountCount assetCount accounts}
    (route : AssetMigrationRoute registry)
    (h : route.endpointsEnabled) :
    AccountRegistry.isActive accounts
      (registry.metadata route.destinationAsset).issuer :=
  h.2.2

end AssetMigrationRoute
end SIRM
