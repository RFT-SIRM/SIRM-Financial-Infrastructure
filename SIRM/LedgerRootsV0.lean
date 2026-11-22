import SIRM.SparseTreeV0

/-!
# What the balance, supply and nonce roots cover (checked by SIRM)

`SIRM.SparseTreeV0` shows that a sparse tree root determines its set of entries. Here the entries are built
from a ledger the way `SPEC_state_commitment_v0.md` says:

    balances: key account << 32 | asset,  value u128 (16 bytes); zero balances are not stored
    supply:   key asset,                   value minted | burned | outstanding, 3 x u128; all-zero is not stored
    nonces:   key principal,               value next nonce u64 (8 bytes); zero is not stored

Entries are produced from a function on a finite list of keys (`items`); the zero value is skipped. Proved,
under a collision-free hash with 32-byte outputs (hypotheses, as before) and the value ranges the ledger
invariants give (`SIRM.BoundedAmounts`): two ledgers with the same balance root have the same balance for
every account and asset below the bounds (`balances_determined`), likewise supplies and nonces. The functions
have the shape of `SIRM.IntegratedLedger.Core` (`bal asset account`, `minted`, `burned`).

Not modelled: that the Rust and Python code enumerates exactly these keys (differential evidence), SHA-256,
inclusion proofs.
-/

namespace SIRM
namespace LedgerRootsV0

open RequestEncodingV2 StateCommitmentV6 SparseTreeV0

/-- The keys below `n`, own definition (the library `upto` lemmas pull in classical choice). -/
def upto : Nat → List Nat
  | 0 => []
  | n + 1 => n :: upto n

theorem mem_upto : ∀ {n k : Nat}, k ∈ upto n ↔ k < n
  | 0, k => by simp [upto]
  | n + 1, k => by
      simp only [upto, List.mem_cons]
      rw [mem_upto]
      constructor
      · rintro (h | h)
        · exact h ▸ Nat.lt_succ_self n
        · exact Nat.lt_succ_of_lt h
      · intro h
        exact (Nat.lt_succ_iff_lt_or_eq.mp h).symm

theorem upto_nodup : ∀ n, (upto n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => List.nodup_cons.mpr ⟨fun h => Nat.lt_irrefl n (mem_upto.mp h), upto_nodup n⟩

/-- The entries of a function on the key list `D`: every key whose value is not the zero value `z`. -/
def items {α : Type} [DecidableEq α] (z : α) (enc : α → List Nat) (D : List Nat) (f : Nat → α) :
    List (Nat × List Nat) :=
  D.filterMap (fun k => if f k = z then none else some (k, enc (f k)))

theorem mem_items {α : Type} [DecidableEq α] {z : α} {enc : α → List Nat} {D : List Nat}
    {f : Nat → α} {p : Nat × List Nat} :
    p ∈ items z enc D f ↔ ∃ k ∈ D, f k ≠ z ∧ p = (k, enc (f k)) := by
  unfold items
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨k, hk, h⟩
    by_cases hz : f k = z
    · simp [hz] at h
    · simp only [hz, if_false, Option.some.injEq] at h
      exact ⟨k, hk, hz, h.symm⟩
  · rintro ⟨k, hk, hz, rfl⟩
    exact ⟨k, hk, by simp [hz]⟩

theorem items_keys {α : Type} [DecidableEq α] (z : α) (enc : α → List Nat) (f : Nat → α) :
    ∀ D : List Nat, (items z enc D f).map Prod.fst = D.filter (fun k => decide (f k ≠ z))
  | [] => rfl
  | k :: D => by
      have ih := items_keys z enc f D
      unfold items at ih ⊢
      by_cases hz : f k = z
      · simp [List.filterMap_cons, hz, ih]
      · simp [List.filterMap_cons, hz, ih]

theorem items_nodup {α : Type} [DecidableEq α] (z : α) (enc : α → List Nat) (f : Nat → α)
    {D : List Nat} (hD : D.Nodup) : ((items z enc D f).map Prod.fst).Nodup := by
  rw [items_keys]
  exact hD.filter _

/-- The root over the entries of a function determines the function on the keys: the same root, the same
values, for every key in the list, absent (zero) values included. -/
theorem items_root_binds {H : List Nat → List Nat} (hH : CollisionFree H) (hL : HLen H)
    {α : Type} [DecidableEq α] {z : α} {enc : α → List Nat} {V : α → Prop}
    (hinj : ∀ a b, V a → V b → enc a = enc b → a = b) (hlen : ∀ a, (enc a).length < 256 ^ 2)
    {D : List Nat} (hD : D.Nodup) (hk : ∀ k ∈ D, k < 256 ^ 8) {f g : Nat → α}
    (hf : ∀ k ∈ D, V (f k)) (hg : ∀ k ∈ D, V (g k))
    (h : root H 64 (items z enc D f) = root H 64 (items z enc D g)) : ∀ k ∈ D, f k = g k := by
  have gd : ∀ (u : Nat → α), ∀ p ∈ items z enc D u, Good p := by
    intro u p hp
    obtain ⟨k, hkD, _, rfl⟩ := mem_items.mp hp
    exact ⟨hk k hkD, hlen _⟩
  have set := root_binds_64 hH hL (gd f) (gd g) (items_nodup z enc f hD) (items_nodup z enc g hD) h
  have one : ∀ (u v : Nat → α), (∀ k ∈ D, V (u k)) → (∀ k ∈ D, V (v k)) →
      (∀ p, p ∈ items z enc D u ↔ p ∈ items z enc D v) → ∀ k ∈ D, u k ≠ z → u k = v k := by
    intro u v hu hv hs k hkD hz
    have h1 : (k, enc (u k)) ∈ items z enc D u := mem_items.mpr ⟨k, hkD, hz, rfl⟩
    obtain ⟨k', hk'D, _, he⟩ := mem_items.mp ((hs _).mp h1)
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, he2⟩ := he
    exact hinj _ _ (hu k hkD) (hv k hkD) he2
  intro k hkD
  by_cases hz : f k = z
  · by_cases hz' : g k = z
    · rw [hz, hz']
    · have := one g f hg hf (fun p => (set p).symm) k hkD hz'
      exact absurd (this.trans hz) hz'
  · exact one f g hf hg set k hkD hz

/-! ### Balances: key `account << 32 | asset`, value u128 -/

/-- The keys of an `accounts × assets` ledger: `account * 2^32 + asset` with `asset < assets`. -/
def balKeys (A S : Nat) : List Nat :=
  (upto (A * 4294967296)).filter (fun k => decide (k % 4294967296 < S))

theorem balKeys_nodup (A S : Nat) : (balKeys A S).Nodup :=
  (upto_nodup _).filter _

theorem mem_balKeys {A S k : Nat} : k ∈ balKeys A S ↔ k < A * 4294967296 ∧ k % 4294967296 < S := by
  unfold balKeys
  simp [List.mem_filter, mem_upto]

/-- The balance of key `k` in a ledger `bal asset account`. -/
def balAt (bal : Nat → Nat → Nat) (k : Nat) : Nat := bal (k % 4294967296) (k / 4294967296)

theorem balances_determined {H : List Nat → List Nat} (hH : CollisionFree H) (hL : HLen H)
    {A S : Nat} (hA : A ≤ 4294967296) (hS : S ≤ 4294967296) (bal bal' : Nat → Nat → Nat)
    (hb : ∀ a < A, ∀ s < S, bal s a < 256 ^ 16) (hb' : ∀ a < A, ∀ s < S, bal' s a < 256 ^ 16)
    (h : root H 64 (items 0 (be 16) (balKeys A S) (balAt bal)) =
         root H 64 (items 0 (be 16) (balKeys A S) (balAt bal'))) :
    ∀ a < A, ∀ s < S, bal s a = bal' s a := by
  intro a ha s hs
  have hkey : ∀ k ∈ balKeys A S, k < 256 ^ 8 := by
    intro k hk
    have := (mem_balKeys.mp hk).1
    have h2 : A * 4294967296 ≤ 4294967296 * 4294967296 := Nat.mul_le_mul_right _ hA
    have h3 : (256 : Nat) ^ 8 = 4294967296 * 4294967296 := by decide
    omega
  have hv : ∀ (u : Nat → Nat → Nat), (∀ a < A, ∀ s < S, u s a < 256 ^ 16) →
      ∀ k ∈ balKeys A S, balAt u k < 256 ^ 16 := by
    intro u hu k hk
    obtain ⟨h1, h2⟩ := mem_balKeys.mp hk
    exact hu (k / 4294967296) (by omega) (k % 4294967296) h2
  have := items_root_binds hH hL (V := fun x => x < 256 ^ 16)
    (fun a b ha hb h => be_inj ha hb h) (fun a => by rw [be_length]; decide)
    (balKeys_nodup A S) hkey (hv bal hb) (hv bal' hb') h (a * 4294967296 + s)
    (mem_balKeys.mpr ⟨by omega, by omega⟩)
  unfold balAt at this
  have e1 : (a * 4294967296 + s) % 4294967296 = s := by omega
  have e2 : (a * 4294967296 + s) / 4294967296 = a := by omega
  rwa [e1, e2] at this

/-! ### Nonces: key principal, value u64 -/

theorem nonces_determined {H : List Nat → List Nat} (hH : CollisionFree H) (hL : HLen H)
    {P : Nat} (hP : P ≤ 256 ^ 8) (n n' : Nat → Nat)
    (hn : ∀ p < P, n p < 256 ^ 8) (hn' : ∀ p < P, n' p < 256 ^ 8)
    (h : root H 64 (items 0 (be 8) (upto P) n) = root H 64 (items 0 (be 8) (upto P) n')) :
    ∀ p < P, n p = n' p := by
  intro p hp
  have := items_root_binds hH hL (V := fun x => x < 256 ^ 8)
    (fun a b ha hb h => be_inj ha hb h) (fun a => by rw [be_length]; decide)
    (upto_nodup _) (fun k hk => Nat.lt_of_lt_of_le (mem_upto.mp hk) hP)
    (fun k hk => hn k (mem_upto.mp hk)) (fun k hk => hn' k (mem_upto.mp hk)) h p
    (mem_upto.mpr hp)
  exact this

/-! ### Supplies: key asset, value minted | burned | outstanding -/

/-- The stored supply value of an asset: minted, burned, and outstanding = minted - burned. -/
def encSup (x : Nat × Nat) : List Nat := be 16 x.1 ++ (be 16 x.2 ++ be 16 (x.1 - x.2))

theorem encSup_inj {a b : Nat × Nat} (ha : a.1 < 256 ^ 16 ∧ a.2 < 256 ^ 16)
    (hb : b.1 < 256 ^ 16 ∧ b.2 < 256 ^ 16) (h : encSup a = encSup b) : a = b := by
  unfold encSup at h
  obtain ⟨h1, h⟩ := List.append_inj h (by rw [be_length, be_length])
  obtain ⟨h2, _⟩ := List.append_inj h (by rw [be_length, be_length])
  exact Prod.ext (be_inj ha.1 hb.1 h1) (be_inj ha.2 hb.2 h2)

theorem supplies_determined {H : List Nat → List Nat} (hH : CollisionFree H) (hL : HLen H)
    {S : Nat} (hS : S ≤ 256 ^ 8) (m m' b b' : Nat → Nat)
    (hm : ∀ s < S, m s < 256 ^ 16 ∧ b s < 256 ^ 16)
    (hm' : ∀ s < S, m' s < 256 ^ 16 ∧ b' s < 256 ^ 16)
    (h : root H 64 (items ((0, 0) : Nat × Nat) encSup (upto S) (fun s => (m s, b s))) =
         root H 64 (items ((0, 0) : Nat × Nat) encSup (upto S) (fun s => (m' s, b' s)))) :
    ∀ s < S, m s = m' s ∧ b s = b' s := by
  intro s hs
  have := items_root_binds hH hL (V := fun x : Nat × Nat => x.1 < 256 ^ 16 ∧ x.2 < 256 ^ 16)
    (fun a b ha hb h => encSup_inj ha hb h)
    (fun a => by unfold encSup; simp only [List.length_append, be_length]; decide)
    (upto_nodup _) (fun k hk => Nat.lt_of_lt_of_le (mem_upto.mp hk) hS)
    (fun k hk => hm k (mem_upto.mp hk)) (fun k hk => hm' k (mem_upto.mp hk)) h s
    (mem_upto.mpr hs)
  simp only [Prod.mk.injEq] at this
  exact this

end LedgerRootsV0
end SIRM
