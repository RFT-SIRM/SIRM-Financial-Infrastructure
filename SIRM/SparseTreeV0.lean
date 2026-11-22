import SIRM.StateCommitmentV6

/-!
# The sparse Merkle tree of state commitment v0 (checked by SIRM)

The balance, supply and nonce roots of every state commitment version are sparse Merkle trees over u64 keys
(`engineering/canonical_encoding/SPEC_state_commitment_v0.md`):

    empty leaf = H("SIRM/SMT/E/v0\0")
    leaf       = H("SIRM/SMT/L/v0\0" | key u64 | len u16 | value)
    node       = H("SIRM/SMT/N/v0\0" | left | right)        (the key bit at the level splits the entries)

`H` is any function on byte lists whose outputs are 32 bytes long (`HLen`) and which is collision free
(`CollisionFree`, a hypothesis, as in `SIRM.StateCommitmentV6`). The tree is defined by plain recursion on the
level over a list of (key, value) pairs; the root of the empty list at level `l` is the empty-subtree hash
`e[l]` of the specification (`root_empty`).

Proved: for two lists of entries with distinct keys, below `2^64`, with values shorter than `2^16`, equal
roots at level 64 mean the same set of entries (`root_binds_64`). The root therefore determines the whole
map from keys to values, including which keys are absent. Not modelled: inclusion proofs, the incremental
algorithm of the Rust code (it computes the same recursion on sorted entries), what the keys and values
mean for balances, supplies and nonces, SHA-256 itself.
-/

namespace SIRM
namespace SparseTreeV0

open RequestEncodingV2 StateCommitmentV6

/-- "SIRM/SMT/E/v0\0" -/
def emptyDom : List Nat := [83, 73, 82, 77, 47, 83, 77, 84, 47, 69, 47, 118, 48, 0]
/-- "SIRM/SMT/L/v0\0" -/
def leafDom : List Nat := [83, 73, 82, 77, 47, 83, 77, 84, 47, 76, 47, 118, 48, 0]
/-- "SIRM/SMT/N/v0\0" -/
def nodeDom : List Nat := [83, 73, 82, 77, 47, 83, 77, 84, 47, 78, 47, 118, 48, 0]

theorem emptyDom_length : emptyDom.length = 14 := by decide
theorem leafDom_length : leafDom.length = 14 := by decide
theorem nodeDom_length : nodeDom.length = 14 := by decide

/-- The hash has 32-byte outputs. -/
def HLen (H : List Nat → List Nat) : Prop := ∀ x, (H x).length = 32

def leafP (k : Nat) (v : List Nat) : List Nat :=
  leafDom ++ (be 8 k ++ (be 2 v.length ++ v))

/-- The key bit that splits the entries at level `l + 1`. -/
def bitOf (l k : Nat) : Nat := k / 2 ^ l % 2

def root (H : List Nat → List Nat) : Nat → List (Nat × List Nat) → List Nat
  | 0, [] => H emptyDom
  | 0, (k, v) :: _ => H (leafP k v)
  | l + 1, is =>
    H (nodeDom ++ (root H l (is.filter (fun p => decide (bitOf l p.1 = 0))) ++
      root H l (is.filter (fun p => decide (bitOf l p.1 ≠ 0)))))

/-- Empty-subtree hashes: `e[0]` is the empty leaf, `e[l+1] = node(e[l], e[l])`. -/
def emptyLevel (H : List Nat → List Nat) : Nat → List Nat
  | 0 => H emptyDom
  | l + 1 => H (nodeDom ++ (emptyLevel H l ++ emptyLevel H l))

theorem root_empty (H : List Nat → List Nat) : ∀ l, root H l [] = emptyLevel H l
  | 0 => rfl
  | l + 1 => by
      simp only [root, emptyLevel, List.filter_nil]
      rw [root_empty H l]

theorem root_length {H : List Nat → List Nat} (hL : HLen H) :
    ∀ l is, (root H l is).length = 32
  | 0, [] => hL _
  | 0, (k, v) :: _ => hL _
  | l + 1, is => hL _

theorem leafP_inj {k k' : Nat} {v v' : List Nat} (hk : k < 256 ^ 8) (hk' : k' < 256 ^ 8)
    (hv : v.length < 256 ^ 2) (hv' : v'.length < 256 ^ 2) (h : leafP k v = leafP k' v') :
    k = k' ∧ v = v' := by
  unfold leafP at h
  obtain ⟨_, h⟩ := List.append_inj h (by rw [leafDom_length])
  obtain ⟨h1, h⟩ := List.append_inj h (by rw [be_length, be_length])
  obtain ⟨h2, h3⟩ := List.append_inj h (by rw [be_length, be_length])
  exact ⟨be_inj hk hk' h1, h3⟩

theorem empty_ne_leaf (k : Nat) (v : List Nat) : emptyDom ≠ leafP k v := by
  intro h
  have h1 := congrArg List.length h
  unfold leafP at h1
  rw [List.length_append, List.length_append, List.length_append, emptyDom_length, leafDom_length,
    be_length, be_length] at h1
  omega

/-- An entry: key below `2^64`, value shorter than `2^16`. -/
def Good (p : Nat × List Nat) : Prop := p.1 < 256 ^ 8 ∧ p.2.length < 256 ^ 2

theorem prefix_split {l k pre : Nat} (h : k / 2 ^ (l + 1) = pre) :
    k / 2 ^ l = 2 * pre + bitOf l k := by
  unfold bitOf
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul] at h
  omega

theorem root_binds : ∀ (l pre : Nat) (is js : List (Nat × List Nat)),
    (∀ p ∈ is, Good p) → (∀ p ∈ js, Good p) →
    (∀ p ∈ is, p.1 / 2 ^ l = pre) → (∀ p ∈ js, p.1 / 2 ^ l = pre) →
    (is.map Prod.fst).Nodup → (js.map Prod.fst).Nodup → ∀ {H : List Nat → List Nat},
    CollisionFree H → HLen H → root H l is = root H l js → ∀ p, p ∈ is ↔ p ∈ js
  | 0, pre, is, js, gi, gj, pi, pj, ni, nj, H, hH, hL, h => by
      -- at level 0 all keys are equal, so each list has at most one entry
      have single : ∀ (xs : List (Nat × List Nat)), (xs.map Prod.fst).Nodup →
          (∀ p ∈ xs, p.1 / 2 ^ 0 = pre) → xs = [] ∨ ∃ x, xs = [x] := by
        intro xs nd hp
        cases xs with
        | nil => exact Or.inl rfl
        | cons a t =>
          right
          refine ⟨a, ?_⟩
          cases t with
          | nil => rfl
          | cons b t' =>
            exfalso
            have ha := hp a (by simp)
            have hb := hp b (by simp)
            simp only [Nat.pow_zero, Nat.div_one] at ha hb
            simp only [List.map_cons, List.nodup_cons, List.mem_cons, List.mem_map] at nd
            exact nd.1 (Or.inl (by rw [ha, hb]))
      rcases single is ni pi with rfl | ⟨⟨k, v⟩, rfl⟩ <;>
        rcases single js nj pj with rfl | ⟨⟨k', v'⟩, rfl⟩
      · intro p; exact Iff.rfl
      · simp only [root] at h
        exact absurd (hH _ _ h) (empty_ne_leaf k' v')
      · simp only [root] at h
        exact absurd (hH _ _ h).symm (empty_ne_leaf k v)
      · simp only [root] at h
        have e := hH _ _ h
        have g1 := gi (k, v) (by simp)
        have g2 := gj (k', v') (by simp)
        obtain ⟨rfl, rfl⟩ := leafP_inj g1.1 g2.1 g1.2 g2.2 e
        intro p; exact Iff.rfl
  | l + 1, pre, is, js, gi, gj, pi, pj, ni, nj, H, hH, hL, h => by
      simp only [root] at h
      have e := hH _ _ h
      obtain ⟨_, e⟩ := List.append_inj e (by rw [nodeDom_length])
      obtain ⟨eL, eR⟩ := List.append_inj e (by rw [root_length hL, root_length hL])
      have nf : ∀ (xs : List (Nat × List Nat)) (P : Nat × List Nat → Bool),
          (xs.map Prod.fst).Nodup → ((xs.filter P).map Prod.fst).Nodup :=
        fun xs P nd => nd.sublist ((List.filter_sublist).map _)
      have gf : ∀ (xs : List (Nat × List Nat)) (P : Nat × List Nat → Bool),
          (∀ p ∈ xs, Good p) → ∀ p ∈ xs.filter P, Good p :=
        fun xs P g p hp => g p (List.mem_filter.mp hp).1
      have pfL : ∀ (xs : List (Nat × List Nat)), (∀ p ∈ xs, p.1 / 2 ^ (l + 1) = pre) →
          ∀ p ∈ xs.filter (fun p => decide (bitOf l p.1 = 0)), p.1 / 2 ^ l = 2 * pre := by
        intro xs hp p hp'
        rw [List.mem_filter] at hp'
        have := prefix_split (hp p hp'.1)
        have hb := of_decide_eq_true hp'.2
        omega
      have pfR : ∀ (xs : List (Nat × List Nat)), (∀ p ∈ xs, p.1 / 2 ^ (l + 1) = pre) →
          ∀ p ∈ xs.filter (fun p => decide (bitOf l p.1 ≠ 0)), p.1 / 2 ^ l = 2 * pre + 1 := by
        intro xs hp p hp'
        rw [List.mem_filter] at hp'
        have := prefix_split (hp p hp'.1)
        have hb := of_decide_eq_true hp'.2
        have : bitOf l p.1 < 2 := by unfold bitOf; omega
        omega
      have ihL := root_binds l (2 * pre) _ _ (gf is _ gi) (gf js _ gj) (pfL is pi) (pfL js pj)
        (nf is _ ni) (nf js _ nj) hH hL eL
      have ihR := root_binds l (2 * pre + 1) _ _ (gf is _ gi) (gf js _ gj) (pfR is pi) (pfR js pj)
        (nf is _ ni) (nf js _ nj) hH hL eR
      intro p
      by_cases hb : bitOf l p.1 = 0
      · have := ihL p
        simp only [List.mem_filter, hb, decide_true, and_true] at this
        exact this
      · have := ihR p
        simpa [List.mem_filter, hb] using this

/-- The root at level 64 determines the set of entries. -/
theorem root_binds_64 {H : List Nat → List Nat} (hH : CollisionFree H) (hL : HLen H)
    {is js : List (Nat × List Nat)} (gi : ∀ p ∈ is, Good p) (gj : ∀ p ∈ js, Good p)
    (ni : (is.map Prod.fst).Nodup) (nj : (js.map Prod.fst).Nodup)
    (h : root H 64 is = root H 64 js) : ∀ p, p ∈ is ↔ p ∈ js := by
  have key : ∀ (xs : List (Nat × List Nat)), (∀ p ∈ xs, Good p) → ∀ p ∈ xs, p.1 / 2 ^ 64 = 0 := by
    intro xs g p hp
    have := (g p hp).1
    exact Nat.div_eq_of_lt (by simpa [Nat.pow_mul] using this)
  exact root_binds 64 0 is js gi gj (key is gi) (key js gj) ni nj hH hL h

end SparseTreeV0
end SIRM
