import SIRM.TypedRegistry

/-!
# Exact Asset-Denominated Base Units

Decimal inputs are represented by a natural-number coefficient and an explicit
number of decimal places. No floating-point values or implicit rounding are
used. Conversion either produces an exact integer base-unit amount or rejects
an input whose precision cannot be represented by the asset.

A separate bounded conversion takes an explicit caller-supplied maximum and
returns a `Fin` value. The bound is not a selected machine word size.
-/

namespace SIRM

/-- A nonnegative decimal amount: `coefficient / 10 ^ decimalPlaces` whole units. -/
structure DecimalAmount where
  coefficient : Nat
  decimalPlaces : Nat
  deriving DecidableEq, Repr

namespace AssetMetadata

/-- Convert an integer number of whole units into the asset's base units. -/
def wholeUnitsToBaseUnits
    {accountCount : Nat}
    (asset : AssetMetadata accountCount)
    (wholeUnits : Nat) : Nat :=
  wholeUnits * asset.baseUnitsPerWhole

/--
Convert a decimal amount into integer base units without rounding.

If the input precision is no greater than the asset precision, the
coefficient is scaled up. If the input has more decimal places, conversion is
accepted only when all excess decimal places are zero (the coefficient is
divisible by the corresponding power of ten). Otherwise the result is `none`.
-/
def toBaseUnits?
    {accountCount : Nat}
    (asset : AssetMetadata accountCount)
    (amount : DecimalAmount) : Option Nat :=
  if amount.decimalPlaces ≤ asset.decimals then
    some (amount.coefficient * 10 ^ (asset.decimals - amount.decimalPlaces))
  else if amount.coefficient % (10 ^ (amount.decimalPlaces - asset.decimals)) = 0 then
    some (amount.coefficient / (10 ^ (amount.decimalPlaces - asset.decimals)))
  else
    none

/-- Whole-unit conversion is exact and uses the metadata-defined scale. -/
@[simp]
theorem toBaseUnits?_wholeUnits
    {accountCount : Nat}
    (asset : AssetMetadata accountCount)
    (wholeUnits : Nat) :
    asset.toBaseUnits? ⟨wholeUnits, 0⟩ =
      some (asset.wholeUnitsToBaseUnits wholeUnits) := by
  simp [toBaseUnits?, wholeUnitsToBaseUnits, baseUnitsPerWhole]

/-- At the asset's declared precision, conversion is the identity on coefficients. -/
@[simp]
theorem toBaseUnits?_at_asset_precision
    {accountCount : Nat}
    (asset : AssetMetadata accountCount)
    (coefficient : Nat) :
    asset.toBaseUnits? ⟨coefficient, asset.decimals⟩ = some coefficient := by
  simp [toBaseUnits?]

/-- Scaling an input with fewer decimal places preserves its exact value. -/
theorem toBaseUnits?_precision_fits_exact
    {accountCount : Nat}
    (asset : AssetMetadata accountCount)
    (amount : DecimalAmount)
    (hPrecision : amount.decimalPlaces ≤ asset.decimals) :
    (amount.coefficient *
        10 ^ (asset.decimals - amount.decimalPlaces)) *
        10 ^ amount.decimalPlaces =
      amount.coefficient * asset.baseUnitsPerWhole := by
  change
    (amount.coefficient *
      10 ^ (asset.decimals - amount.decimalPlaces)) *
      10 ^ amount.decimalPlaces =
    amount.coefficient * 10 ^ asset.decimals
  have hExponent :
      (asset.decimals - amount.decimalPlaces) + amount.decimalPlaces =
        asset.decimals :=
    Nat.sub_add_cancel hPrecision
  have hScale :
      10 ^ (asset.decimals - amount.decimalPlaces) *
        10 ^ amount.decimalPlaces = 10 ^ asset.decimals := by
    calc
      10 ^ (asset.decimals - amount.decimalPlaces) *
          10 ^ amount.decimalPlaces =
        10 ^ ((asset.decimals - amount.decimalPlaces) +
          amount.decimalPlaces) := by rw [pow_add]
      _ = 10 ^ asset.decimals := by rw [hExponent]
  calc
    (amount.coefficient *
        10 ^ (asset.decimals - amount.decimalPlaces)) *
        10 ^ amount.decimalPlaces =
      amount.coefficient *
        (10 ^ (asset.decimals - amount.decimalPlaces) *
          10 ^ amount.decimalPlaces) := by rw [Nat.mul_assoc]
    _ = amount.coefficient * 10 ^ asset.decimals := by rw [hScale]

/-- More input decimal places are accepted exactly when excess digits vanish. -/
theorem toBaseUnits?_precision_exceeds_exact
    {accountCount : Nat}
    (asset : AssetMetadata accountCount)
    (amount : DecimalAmount)
    (hPrecision : asset.decimals < amount.decimalPlaces)
    (hRemainder :
      amount.coefficient %
        (10 ^ (amount.decimalPlaces - asset.decimals)) = 0) :
    asset.toBaseUnits? amount =
      some (amount.coefficient /
        (10 ^ (amount.decimalPlaces - asset.decimals))) := by
  have hNotLe : ¬ amount.decimalPlaces ≤ asset.decimals :=
    not_le.mpr hPrecision
  simp [toBaseUnits?, hNotLe, hRemainder]

/-- Rejected excess precision is precisely a nonzero discarded remainder. -/
theorem toBaseUnits?_precision_exceeds_rejected
    {accountCount : Nat}
    (asset : AssetMetadata accountCount)
    (amount : DecimalAmount)
    (hPrecision : asset.decimals < amount.decimalPlaces)
    (hRemainder :
      amount.coefficient %
        (10 ^ (amount.decimalPlaces - asset.decimals)) ≠ 0) :
    asset.toBaseUnits? amount = none := by
  have hNotLe : ¬ amount.decimalPlaces ≤ asset.decimals :=
    not_le.mpr hPrecision
  simp [toBaseUnits?, hNotLe, hRemainder]

/-- Exact division identity for an accepted input with excess decimal places. -/
theorem toBaseUnits?_excess_precision_division_exact
    {accountCount : Nat}
    (asset : AssetMetadata accountCount)
    (amount : DecimalAmount)
    (hRemainder :
      amount.coefficient %
        (10 ^ (amount.decimalPlaces - asset.decimals)) = 0) :
    amount.coefficient =
      10 ^ (amount.decimalPlaces - asset.decimals) *
        (amount.coefficient /
          (10 ^ (amount.decimalPlaces - asset.decimals))) := by
  have hDecomposition :=
    Nat.mod_add_div amount.coefficient
      (10 ^ (amount.decimalPlaces - asset.decimals))
  have hQuotient :
      10 ^ (amount.decimalPlaces - asset.decimals) *
        (amount.coefficient /
          (10 ^ (amount.decimalPlaces - asset.decimals))) =
        amount.coefficient := by
    simpa [hRemainder] using hDecomposition
  exact hQuotient.symm

/--
Convert exactly and additionally require the result to fit in an explicit
inclusive range `0 .. maxBaseUnits`. Returning `Fin (maxBaseUnits + 1)` makes
the bound part of the result's type.
-/
def toBaseUnitsWithin?
    {accountCount : Nat}
    (asset : AssetMetadata accountCount)
    (amount : DecimalAmount)
    (maxBaseUnits : Nat) : Option (Fin (Nat.succ maxBaseUnits)) :=
  match asset.toBaseUnits? amount with
  | none => none
  | some units =>
      if h : units ≤ maxBaseUnits then
        some ⟨units, Nat.lt_succ_of_le h⟩
      else
        none

/-- Any bounded conversion result is no greater than the supplied maximum. -/
theorem toBaseUnitsWithin?_value_le
    {accountCount : Nat}
    (asset : AssetMetadata accountCount)
    (amount : DecimalAmount)
    (maxBaseUnits : Nat)
    (units : Fin (Nat.succ maxBaseUnits)) :
    units.val ≤ maxBaseUnits :=
  Nat.le_of_lt_succ units.isLt

/-- A valid exact conversion is retained when it is within the supplied bound. -/
theorem toBaseUnitsWithin?_of_exact_conversion
    {accountCount : Nat}
    (asset : AssetMetadata accountCount)
    (amount : DecimalAmount)
    (maxBaseUnits units : Nat)
    (hConversion : asset.toBaseUnits? amount = some units)
    (hBound : units ≤ maxBaseUnits) :
    asset.toBaseUnitsWithin? amount maxBaseUnits =
      some ⟨units, Nat.lt_succ_of_le hBound⟩ := by
  simp [toBaseUnitsWithin?, hConversion, hBound]

/-- Exact amounts exceeding the caller-supplied bound are rejected. -/
theorem toBaseUnitsWithin?_rejects_over_limit
    {accountCount : Nat}
    (asset : AssetMetadata accountCount)
    (amount : DecimalAmount)
    (maxBaseUnits units : Nat)
    (hConversion : asset.toBaseUnits? amount = some units)
    (hTooLarge : maxBaseUnits < units) :
    asset.toBaseUnitsWithin? amount maxBaseUnits = none := by
  have hNotBound : ¬ units ≤ maxBaseUnits := not_le.mpr hTooLarge
  simp [toBaseUnitsWithin?, hConversion, hNotBound]

end AssetMetadata
end SIRM
