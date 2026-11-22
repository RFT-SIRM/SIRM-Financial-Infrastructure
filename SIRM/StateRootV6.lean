import SIRM.LedgerRootsV0
import SIRM.EscrowConfigDigestV6
import SIRM.CacheDigestV6

/-!
# The v6 state root determines the committed state (checked by SIRM)

The last step of the commitment chain. A `Snapshot` is what the root of
`engineering/canonical_encoding/SPEC_state_commitment_v6.md` covers in the model: the shape (accounts,
assets), the ledger (balances, supplies, nonces), the config, the request cache, the escrow table, the clock
and the migration totals. `rootOf` builds the root exactly as the specification does, from

* the three sparse trees (`SIRM.LedgerRootsV0`, `SIRM.SparseTreeV0`),
* the config, cache and escrow digests (`SIRM.EscrowConfigDigestV6`, `SIRM.CacheDigestV6`),
* the state payload (`SIRM.StateCommitmentV6`).

`state_root_binds`: under a collision-free hash with 32-byte byte outputs (hypotheses `CollisionFree`,
`HLen`, `HDig`, as before) and the value ranges of the ledger invariants, two snapshots with equal roots
have the same shape, clock and migration totals, the same balance for every account and asset, the same
minted and burned amount for every asset, the same nonce for every principal, the same config (including
every arbiter grant), the same list of cached requests with their stored outcomes (including a cached
`resolve`, its escrow id and side), and the same escrow table with deadlines, records and filings.

Not modelled: that the Rust and Python code builds the lists from a machine state in this order (differential
evidence, `commit_v6_conformance.rs`), sorting, inclusion proofs, SHA-256 itself. The hash hypotheses are
assumptions, not facts proved here.
-/

namespace SIRM
namespace StateRootV6

open RequestEncodingV2 StateCommitmentV6 SparseTreeV0 LedgerRootsV0 EscrowConfigDigestV6 CacheDigestV6

/-- Hash outputs are bytes. -/
def HDig (H : List Nat → List Nat) : Prop := ∀ x, ∀ d ∈ H x, d < 256

structure Snapshot where
  accounts : Nat
  assets : Nat
  /-- number of principals considered for the nonce tree (a bound of the model, not committed) -/
  principals : Nat
  bal : Nat → Nat → Nat
  minted : Nat → Nat
  burned : Nat → Nat
  nonce : Nat → Nat
  cfg : Cfg
  cache : List (Req × Out)
  escrow : List Ent
  now : Nat
  ts : Nat
  tt : Nat
  dust : Nat

def Snapshot.V (s : Snapshot) : Prop :=
  s.accounts < 256 ^ 4 ∧ s.assets < 256 ^ 4 ∧ s.principals ≤ 256 ^ 8 ∧
  (∀ a < s.accounts, ∀ x < s.assets, s.bal x a < 256 ^ 16) ∧
  (∀ x < s.assets, s.minted x < 256 ^ 16 ∧ s.burned x < 256 ^ 16) ∧
  (∀ p < s.principals, s.nonce p < 256 ^ 8) ∧
  s.cfg.V ∧ (∀ p ∈ s.cache, PValid p) ∧ s.cache.length < 256 ^ 4 ∧
  (∀ e ∈ s.escrow, e.V) ∧ s.escrow.length < 256 ^ 4 ∧
  s.now < 256 ^ 8 ∧ s.ts < 256 ^ 16 ∧ s.tt < 256 ^ 16 ∧ s.dust < 256 ^ 16

def comps (H : List Nat → List Nat) (s : Snapshot) : Comps where
  accounts := s.accounts
  assets := s.assets
  bal := root H 64 (items 0 (be 16) (balKeys s.accounts s.assets) (balAt s.bal))
  sup := root H 64 (items ((0, 0) : Nat × Nat) encSup (upto s.assets) (fun a => (s.minted a, s.burned a)))
  non := root H 64 (items 0 (be 8) (upto s.principals) s.nonce)
  cfg := H (cfgPayload s.cfg)
  cac := H (cachePayload s.cache)
  esc := H (escPayload s.escrow)
  now := s.now
  ts := s.ts
  tt := s.tt
  dust := s.dust

def rootOf (H : List Nat → List Nat) (s : Snapshot) : List Nat := stateRoot H stcV6 (comps H s)

theorem root_dig {H : List Nat → List Nat} (hD : HDig H) : ∀ l is, ∀ d ∈ root H l is, d < 256
  | 0, [] => hD _
  | 0, (k, v) :: _ => hD _
  | l + 1, is => hD _

theorem comps_valid {H : List Nat → List Nat} (hL : HLen H) (hD : HDig H) {s : Snapshot}
    (hs : s.V) : (comps H s).Valid := by
  obtain ⟨h1, h2, _, _, _, _, _, _, _, _, _, h13, h14, h15, h16⟩ := hs
  refine ⟨h1, h2, ⟨root_length hL _ _, root_dig hD _ _⟩, ⟨root_length hL _ _, root_dig hD _ _⟩,
    ⟨root_length hL _ _, root_dig hD _ _⟩, ⟨hL _, hD _⟩, ⟨hL _, hD _⟩, ⟨hL _, hD _⟩,
    h13, h14, h15, h16⟩

theorem state_root_binds {H : List Nat → List Nat} (hH : CollisionFree H) (hL : HLen H)
    (hD : HDig H) {s t : Snapshot} (hs : s.V) (ht : t.V) (hP : s.principals = t.principals)
    (h : rootOf H s = rootOf H t) :
    s.accounts = t.accounts ∧ s.assets = t.assets ∧ s.now = t.now ∧ s.ts = t.ts ∧ s.tt = t.tt ∧
    s.dust = t.dust ∧
    (∀ a < s.accounts, ∀ x < s.assets, s.bal x a = t.bal x a) ∧
    (∀ x < s.assets, s.minted x = t.minted x ∧ s.burned x = t.burned x) ∧
    (∀ p < s.principals, s.nonce p = t.nonce p) ∧
    s.cfg = t.cfg ∧ s.cache = t.cache ∧ s.escrow = t.escrow := by
  have hc := (root_binds hH stcV6_length stcV6_length (comps_valid hL hD hs) (comps_valid hL hD ht) h).2
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := hs
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15⟩ := ht
  unfold comps at hc
  simp only [Comps.mk.injEq] at hc
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ := hc
  have hA : s.accounts ≤ 4294967296 := by
    have : (256 : Nat) ^ 4 = 4294967296 := by decide
    omega
  have hS : s.assets ≤ 4294967296 := by
    have : (256 : Nat) ^ 4 = 4294967296 := by decide
    omega
  refine ⟨e1, e2, e9, e10, e11, e12, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← e1, ← e2] at e3
    exact balances_determined hH hL hA hS s.bal t.bal a4
      (fun a ha x hx => b4 a (by rw [← e1]; exact ha) x (by rw [← e2]; exact hx)) e3
  · rw [← e2] at e4
    intro x hx
    exact supplies_determined hH hL (Nat.le_of_lt (Nat.lt_of_lt_of_le a2 (by decide))) s.minted
      t.minted s.burned t.burned a5 (fun y hy => b5 y (by rw [← e2]; exact hy)) e4 x hx
  · rw [← hP] at e5
    exact nonces_determined hH hL a3 s.nonce t.nonce a6
      (fun p hp => b6 p (by rw [← hP]; exact hp)) e5
  · exact configDigest_binds hH a7 b7 e6
  · exact cacheDigest_binds hH a8 b8 e7
  · exact escrowDigest_binds hH a10 b10 a11 b11 e8

end StateRootV6
end SIRM
