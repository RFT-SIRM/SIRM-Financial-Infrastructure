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
  refine loop.spec_decr_nat (fun p : Usize × Usize => valid.length - p.2.val)
    (fun p : Usize × Usize => p.2.val ≤ valid.length ∧ p.1.val + ((valid.val.drop p.2.val).filter id).length = total valid.val)
    (fun r : Usize => r.val = total valid.val) _ (n, i) ?_ ⟨hi, hn⟩
  rintro ⟨n, i⟩ ⟨hi, hn⟩
  dsimp only at hi hn ⊢
  unfold count_valid_loop.body
  by_cases hlt : i < Slice.len valid
  · have hl : i.val < valid.length := by scalar_tac
    simp only [hlt, if_true]
    apply WP.spec_bind (Slice.index_usize_spec valid i hl)
    intro b hb
    have hd := total_drop valid.val i.val hl
    by_cases hbb : b = true
    · rw [if_pos hbb]
      have hv : valid.val[i.val]'hl = true := by rw [← hb]; exact hbb
      rw [if_pos hv] at hd
      have htot : total valid.val ≤ valid.length := by
        unfold total; exact List.length_filter_le _ _
      have hmax : valid.length ≤ Usize.max := Slice.length_ineq valid
      apply WP.spec_bind (Usize.add_spec (x := n) (y := 1#usize) (by scalar_tac))
      intro n1 hn1
      apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
      intro i2 hi2
      simp only [WP.spec_ok]
      have h1 : n1.val = n.val + 1 := by scalar_tac
      have h2 : i2.val = i.val + 1 := by scalar_tac
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      rw [h1, h2]; omega
    · rw [if_neg hbb]
      apply WP.spec_bind (Pₘ := fun x => x = n) (by simp [WP.spec_ok])
      intro n1 hn1
      apply WP.spec_bind (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
      intro i2 hi2
      simp only [WP.spec_ok]
      subst hn1
      have hbf : b = false := by simpa using hbb
      have hv : valid.val[i.val]'hl = false := by rw [← hb]; exact hbf
      rw [hv] at hd
      simp at hd
      have h2 : i2.val = i.val + 1 := by scalar_tac
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      rw [h2]; omega
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
  refine loop.spec_decr_nat (fun p : Bool × Usize => keys.length - p.2.val)
    (fun p : Bool × Usize => (i.val < p.2.val ∧ p.2.val ≤ keys.length) ∧
      (p.1 = true ↔ d0 = true ∧ ∀ j', i.val < j' → j' < p.2.val → kk keys i.val ≠ kk keys j'))
    (fun r : Bool => (r = true ↔ d0 = true ∧
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
  refine loop.spec_decr_nat (fun p : Bool × Usize => keys.length - p.2.val)
    (fun p : Bool × Usize => p.2.val ≤ keys.length ∧
      (p.1 = true ↔ ∀ a b, a < b → b < keys.length → a < p.2.val → kk keys a ≠ kk keys b))
    (fun r : Bool => (r = true ↔ Distinct keys)) _ (d, i) ?_ ⟨hi, hd⟩
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

/-! ### The nonce decision (`IntegratedPipeline.processCapped` with `N = 2^64 - 1`) -/

theorem u64_max_val : (core.num.U64.MAX).val = 18446744073709551615 := by
  first | rfl | decide

/-- `nonce_class` is the order of the checks of `processCapped` after the request-id lookup: a nonce behind the
counter is stale, one ahead is future, and a request carrying exactly the counter is stale when the counter is at
`2^64 - 1` (it cannot advance) and proceeds otherwise. -/
theorem nonce_class_spec (request expected : Std.U64) :
    nonce_class request expected ⦃ c =>
      (c = NonceClass.Stale ↔ (request.val < expected.val ∨
        (request.val = expected.val ∧ expected.val = 18446744073709551615))) ∧
      (c = NonceClass.Future ↔ expected.val < request.val) ∧
      (c = NonceClass.Proceed ↔ (request.val = expected.val ∧ expected.val < 18446744073709551615)) ⦄ := by
  have hM := u64_max_val
  have hb : expected.val ≤ 18446744073709551615 := by scalar_tac
  unfold nonce_class
  by_cases h1 : request < expected
  · have h1' : request.val < expected.val := (UScalar.lt_equiv _ _).mp h1
    rw [if_pos h1]
    simp only [WP.spec_ok]
    refine ⟨?_, ?_, ?_⟩ <;> (try simp) <;> (try omega)
  · have h1' : ¬ request.val < expected.val := fun h => h1 ((UScalar.lt_equiv _ _).mpr h)
    by_cases h2 : request > expected
    · have h2' : expected.val < request.val := (UScalar.lt_equiv _ _).mp h2
      rw [if_neg h1, if_pos h2]
      simp only [WP.spec_ok]
      refine ⟨?_, ?_, ?_⟩ <;> (try simp) <;> (try omega)
    · have h2' : ¬ expected.val < request.val := fun h => h2 ((UScalar.lt_equiv _ _).mpr h)
      have heq : request.val = expected.val := by omega
      by_cases h3 : expected = core.num.U64.MAX
      · have h3' : expected.val = 18446744073709551615 := by
          have := (UScalar.eq_equiv expected core.num.U64.MAX).mp h3
          omega
        rw [if_neg h1, if_neg h2, if_pos h3]
        simp only [WP.spec_ok]
        refine ⟨?_, ?_, ?_⟩ <;> (try simp) <;> (try omega)
      · have h3' : expected.val ≠ 18446744073709551615 := by
          intro h
          apply h3
          exact (UScalar.eq_equiv expected core.num.U64.MAX).mpr (by omega)
        rw [if_neg h1, if_neg h2, if_neg h3]
        simp only [WP.spec_ok]
        refine ⟨?_, ?_, ?_⟩ <;> (try simp) <;> (try omega)

/-- Below the ceiling the successor fits and is the counter plus one: this is why `Proceed` can bump the counter. -/
theorem next_nonce_spec (expected : Std.U64) (h : expected.val < 18446744073709551615) :
    next_nonce expected ⦃ r => r.val = expected.val + 1 ⦄ := by
  unfold next_nonce
  refine WP.spec_mono (U64.add_spec (x := expected) (y := 1#u64) (by scalar_tac)) ?_
  intro r hr
  simpa using hr


end sirm_keys_core
