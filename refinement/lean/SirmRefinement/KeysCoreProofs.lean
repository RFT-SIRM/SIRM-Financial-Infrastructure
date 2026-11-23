import Aeneas
import SirmRefinement.SirmKeysCore

/-!
# Refinement of `sirm-keys-core` (Rust) against the model of `SIRM/ThresholdAuth.lean`

`SirmKeysCore.lean` is the Aeneas translation of `rust/sirm-keys-core/src/lib.rs` (do not edit it; regenerate
with `refinement/run_extraction.sh`). Here the translated functions are proved to do what the Lean model says:

* `count_valid_spec`: the result is the number of `true` entries (no overflow);
* `accepts_spec`: the decision is `0 < k ∧ k ≤ number of true entries` (`thresholdAccepts`);
* `keys_distinct_spec`: the result is `true` exactly when no two indices carry the same key value
  (`KeysDistinct`).

Status: first draft, to be completed by iterating with `lake build` (it has not been compiled yet).
-/

open Aeneas Aeneas.Std Result ControlFlow
open sirm_keys_core

namespace sirm_keys_core

/-- Number of `true` entries. -/
def total (l : List Bool) : Nat := (l.filter id).length

/-- The key value at an index, if there is one. -/
def kk (keys : Slice Key) (n : Nat) : Option Std.U64 := (keys.val[n]?).map (·.key)

/-- Dropping one more element removes its contribution. -/
theorem total_drop (l : List Bool) (i : Nat) (h : i < l.length) :
    ((l.drop i).filter id).length = (if l[i] = true then 1 else 0) + ((l.drop (i + 1)).filter id).length := by
  rw [List.drop_eq_getElem_cons h]
  cases hb : l[i] <;> simp [List.filter_cons, hb] <;> omega

theorem count_valid_loop_spec (valid : Slice Bool) (n i : Usize) (hi : i.val ≤ valid.length)
    (hn : n.val + ((valid.val.drop i.val).filter id).length = total valid.val) :
    count_valid_loop valid n i ⦃ r => r.val = total valid.val ⦄ := by
  unfold count_valid_loop
  refine loop.spec_decr_nat (fun p => valid.length - p.2.val)
    (fun p => p.2.val ≤ valid.length ∧ p.1.val + ((valid.val.drop p.2.val).filter id).length = total valid.val)
    (fun r => r.val = total valid.val) _ (n, i) ?_ ⟨hi, hn⟩
  rintro ⟨n, i⟩ ⟨hi, hn⟩
  dsimp only at hi hn ⊢
  unfold count_valid_loop.body
  by_cases hlt : i < Slice.len valid
  · have hl : i.val < valid.length := by scalar_tac
    simp only [hlt, if_true]
    apply WP.spec_bind (Slice.index_usize_spec valid i hl)
    intro b hb
    have hd := total_drop valid.val i.val hl
    cases hbb : b
    · simp only [hbb, Bool.false_eq_true, if_false, WP.spec_ok] at *
      apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
      intro i2 hi2
      simp only [WP.spec_ok]
      subst hbb
      refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
      simp_all
      scalar_tac
    · simp only [hbb, if_true] at *
      apply WP.spec_bind (Usize.add_spec (x := n) (y := 1#usize) (by scalar_tac))
      intro n1 hn1
      apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
      intro i2 hi2
      simp only [WP.spec_ok]
      refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
      simp_all
      scalar_tac
  · have : i.val = valid.length := by scalar_tac
    simp only [hlt, if_false, WP.spec_ok]
    have hd : (valid.val.drop i.val) = [] := by simp [this, Slice.length]
    rw [hd] at hn
    simpa using hn

theorem count_valid_spec (valid : Slice Bool) :
    count_valid valid ⦃ r => r.val = total valid.val ⦄ := by
  unfold count_valid
  apply count_valid_loop_spec
  · simp
  · simp [total]

/-- `accepts` is the decision of `thresholdAccepts`: `0 < k ∧ k ≤` number of verified indices. -/
theorem accepts_spec (valid : Slice Bool) (k : Usize) :
    accepts valid k ⦃ r => r = true ↔ (0 < k.val ∧ k.val ≤ total valid.val) ⦄ := by
  unfold accepts
  by_cases hk : k > 0#usize
  · have hk' : 0 < k.val := by scalar_tac
    simp only [hk, if_true]
    apply WP.spec_bind (count_valid_spec valid)
    intro c hc
    simp only [WP.spec_ok]
    simp [hc, hk']
  · have hk' : ¬ 0 < k.val := by scalar_tac
    simp only [hk, if_false, WP.spec_ok]
    simp [hk']

/-- No two indices carry the same key value. -/
def Distinct (keys : Slice Key) : Prop :=
  ∀ a b, a < b → b < keys.length → kk keys a ≠ kk keys b

theorem kk_eq (keys : Slice Key) (n : Nat) (h : n < keys.length) :
    kk keys n = some (keys.val[n]'h).key := by
  simp [kk, List.getElem?_eq_getElem h]

theorem kk_iff (keys : Slice Key) (a b : Nat) (ha : a < keys.length) (hb : b < keys.length)
    (k k1 : Key) (hk : k = keys.val[a]'ha) (hk1 : k1 = keys.val[b]'hb) :
    kk keys a = kk keys b ↔ k.key = k1.key := by
  rw [kk_eq keys a ha, kk_eq keys b hb, hk, hk1]
  simp

theorem keys_distinct_inner_spec (keys : Slice Key) (i : Usize) (d0 : Bool)
    (hi : i.val < keys.length) (d : Bool) (j : Usize)
    (hj : i.val < j.val ∧ j.val ≤ keys.length)
    (hd : d = true ↔ d0 = true ∧ ∀ j', i.val < j' → j' < j.val → kk keys i.val ≠ kk keys j') :
    keys_distinct_loop0_loop0 keys d i j ⦃ r => (r = true ↔ d0 = true ∧
      ∀ j', i.val < j' → j' < keys.length → kk keys i.val ≠ kk keys j') ⦄ := by
  unfold keys_distinct_loop0_loop0
  refine loop.spec_decr_nat (fun p => keys.length - p.2.val)
    (fun p => (i.val < p.2.val ∧ p.2.val ≤ keys.length) ∧
      (p.1 = true ↔ d0 = true ∧ ∀ j', i.val < j' → j' < p.2.val → kk keys i.val ≠ kk keys j'))
    (fun r => (r = true ↔ d0 = true ∧
      ∀ j', i.val < j' → j' < keys.length → kk keys i.val ≠ kk keys j')) _ (d, j) ?_ ⟨hj, hd⟩
  rintro ⟨d, j⟩ ⟨hj, hd⟩
  dsimp only at hj hd ⊢
  unfold keys_distinct_loop0_loop0.body
  by_cases hlt : j < Slice.len keys
  · have hl : j.val < keys.length := by scalar_tac
    simp only [hlt, if_true]
    apply WP.spec_bind (Slice.index_usize_spec keys i hi)
    intro k hk
    apply WP.spec_bind (Slice.index_usize_spec keys j hl)
    intro k1 hk1
    have hiff := kk_iff keys i.val j.val hi hl k k1 hk hk1
    by_cases heq : k.key = k1.key
    · apply WP.spec_bind (Pₘ := fun x => x = false) (by simp only [if_pos heq, WP.spec_ok])
      intro d1 hd1
      apply WP.spec_bind (Usize.add_spec (x := j) (y := 1#usize) (by scalar_tac))
      intro j1 hj1
      have hj1' : j1.val = j.val + 1 := by scalar_tac
      simp only [WP.spec_ok]
      try dsimp only
      refine ⟨⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
      subst hd1
      constructor
      · intro h; simp at h
      · rintro ⟨_, h⟩
        exact absurd (hiff.mpr heq) (h j.val hj.1 (by omega))
    · apply WP.spec_bind (Pₘ := fun x => x = d) (by simp only [if_neg heq, WP.spec_ok])
      intro d1 hd1
      apply WP.spec_bind (Usize.add_spec (x := j) (y := 1#usize) (by scalar_tac))
      intro j1 hj1
      have hj1' : j1.val = j.val + 1 := by scalar_tac
      simp only [WP.spec_ok]
      try dsimp only
      refine ⟨⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
      subst hd1
      constructor
      · intro h
        obtain ⟨h0, h2⟩ := hd.mp h
        refine ⟨h0, fun j' h1 h3 => ?_⟩
        by_cases hjj : j' = j.val
        · subst hjj
          exact fun e => heq (hiff.mp e)
        · exact h2 j' h1 (by omega)
      · rintro ⟨h0, h2⟩
        exact hd.mpr ⟨h0, fun j' h1 h3 => h2 j' h1 (by omega)⟩
  · have hjl : j.val = keys.length := by scalar_tac
    simp only [hlt, if_false, WP.spec_ok]
    rw [hjl] at hd
    exact hd

theorem keys_distinct_outer_spec (keys : Slice Key) (d : Bool) (i : Usize) (hi : i.val ≤ keys.length)
    (hd : d = true ↔ ∀ a b, a < b → b < keys.length → a < i.val → kk keys a ≠ kk keys b) :
    keys_distinct_loop0 keys d i ⦃ r => (r = true ↔ Distinct keys) ⦄ := by
  unfold keys_distinct_loop0
  refine loop.spec_decr_nat (fun p => keys.length - p.2.val)
    (fun p => p.2.val ≤ keys.length ∧
      (p.1 = true ↔ ∀ a b, a < b → b < keys.length → a < p.2.val → kk keys a ≠ kk keys b))
    (fun r => (r = true ↔ Distinct keys)) _ (d, i) ?_ ⟨hi, hd⟩
  rintro ⟨d, i⟩ ⟨hi, hd⟩
  dsimp only at hi hd ⊢
  unfold keys_distinct_loop0.body
  by_cases hlt : i < Slice.len keys
  · have hl : i.val < keys.length := by scalar_tac
    simp only [hlt, if_true]
    apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    intro j hj
    have hj' : j.val = i.val + 1 := by scalar_tac
    apply WP.spec_bind (keys_distinct_inner_spec keys i d hl d j ⟨by omega, by omega⟩ ?_)
    · intro d1 hd1
      apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
      intro i2 hi2
      have hi2' : i2.val = i.val + 1 := by scalar_tac
      simp only [WP.spec_ok]
      try dsimp only
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      constructor
      · intro h
        obtain ⟨h0, h2⟩ := hd1.mp h
        have h3 := hd.mp h0
        intro a b hab hb ha
        by_cases haa : a = i.val
        · subst haa
          exact h2 b hab hb
        · exact h3 a b hab hb (by omega)
      · intro H
        exact hd1.mpr ⟨hd.mpr (fun a b hab hb ha => H a b hab hb (by omega)),
          fun j' h1 h2 => H i.val j' h1 h2 (by omega)⟩
    · constructor
      · intro h
        exact ⟨h, fun j' h1 h2 => by omega⟩
      · exact fun h => h.1
  · have hil : i.val = keys.length := by scalar_tac
    simp only [hlt, if_false, WP.spec_ok]
    constructor
    · intro h a b hab hb
      exact hd.mp h a b hab hb (by omega)
    · intro H
      exact hd.mpr (fun a b hab hb ha => H a b hab hb)

/-- `keys_distinct` returns `true` exactly when no two indices carry the same key value (`KeysDistinct`). -/
theorem keys_distinct_spec (keys : Slice Key) :
    keys_distinct keys ⦃ r => (r = true ↔ Distinct keys) ⦄ := by
  unfold keys_distinct
  apply keys_distinct_outer_spec
  · simp
  · simp

end sirm_keys_core
