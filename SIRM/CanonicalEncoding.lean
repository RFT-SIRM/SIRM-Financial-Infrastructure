import Mathlib

/-!
# Fixed-Width Big-Endian Natural-Number Codec

Arithmetic core of the proposed canonical request encoding
(`engineering/canonical_encoding/SPEC_v0.md`). A natural number is written as
exactly `n` base-256 digits, most significant first. Digits are `Nat` values;
the byte-range bound `< 256` is proved separately.

Proved here: value recovery for in-range numbers, the exact length, the digit
bound, and injectivity on `[0, 256^n)`. Not proved here: composition of
several fields into a full request encoding, the inverse direction on arbitrary
digit lists, and any refinement to a Rust implementation.
-/

namespace SIRM

/-- `n` base-256 digits of `v`, most significant first (high digits truncated). -/
def beDigits : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, v => beDigits n (v / 256) ++ [v % 256]

/-- Read a most-significant-first base-256 digit list. -/
def beValue (l : List Nat) : Nat :=
  l.foldl (fun acc d => acc * 256 + d) 0

theorem beValue_append_singleton (l : List Nat) (d : Nat) :
    beValue (l ++ [d]) = beValue l * 256 + d := by
  simp [beValue, List.foldl_append]

theorem beDigits_length (n v : Nat) : (beDigits n v).length = n := by
  induction n generalizing v with
  | zero => simp [beDigits]
  | succ n ih => simp [beDigits, ih]

theorem beDigits_lt (n v : Nat) : ∀ d ∈ beDigits n v, d < 256 := by
  induction n generalizing v with
  | zero => simp [beDigits]
  | succ n ih =>
    intro d hd
    simp only [beDigits, List.mem_append, List.mem_singleton] at hd
    rcases hd with hd | hd
    · exact ih (v / 256) d hd
    · subst hd
      exact Nat.mod_lt _ (by decide)

/-- Reading the digits of `v` yields `v` reduced modulo `256 ^ n`. -/
theorem beValue_beDigits (n v : Nat) :
    beValue (beDigits n v) = v % 256 ^ n := by
  induction n generalizing v with
  | zero => simp [beDigits, beValue, Nat.mod_one]
  | succ n ih =>
    rw [beDigits, beValue_append_singleton, ih]
    have hpow : 256 ^ (n + 1) = 256 * 256 ^ n := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow, Nat.mod_mul]
    omega

/-- In-range values are recovered exactly. -/
theorem beValue_beDigits_of_lt {n v : Nat} (h : v < 256 ^ n) :
    beValue (beDigits n v) = v := by
  rw [beValue_beDigits]
  exact Nat.mod_eq_of_lt h

/-- Distinct in-range values have distinct fixed-width encodings. -/
theorem beDigits_injective_of_lt {n v w : Nat}
    (hv : v < 256 ^ n) (hw : w < 256 ^ n)
    (h : beDigits n v = beDigits n w) : v = w := by
  have := congrArg beValue h
  rwa [beValue_beDigits_of_lt hv, beValue_beDigits_of_lt hw] at this

example : beDigits 4 258 = [0, 0, 1, 2] := by decide
example : beValue [0, 0, 1, 2] = 258 := by decide

end SIRM
