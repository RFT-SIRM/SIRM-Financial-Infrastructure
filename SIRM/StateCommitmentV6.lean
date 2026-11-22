import SIRM.RequestEncodingV2

/-!
# State commitment v6: what the root binds (checked by SIRM)

The layout of `engineering/canonical_encoding/SPEC_state_commitment_v6.md`, with the hash left abstract:

    state root = H("SIRM/STC/v6\0" | accounts u32 | assets u32 | balance root | supply root | nonce root
                   | config | cache | escrow | now u64 | total source u128 | total target u128 | dust u128)
    cache entry = request encoding v2 (request id included) | stored outcome (11 bytes)

`H` is any function on byte lists. Its collision freedom is a hypothesis of the theorems (`CollisionFree`),
not an axiom and not something proved here: SHA-256 is only assumed to behave that way.

Proved: the hashed payload determines its domain and every component (`payload_injective`), so under a
collision-free `H` two equal roots have equal components (`root_binds`) and a root under the v5 domain
never equals a root under the v6 domain (`v5_v6_roots_differ`); a cache entry determines the request and
the stored outcome (`cacheEntry_injective`), so the committed cache binds a cached `resolve` request, its
escrow id and its side. Not modelled: the sparse trees, the config, cache and escrow digests as functions of
a machine state, the sorting of lists. Those digests are opaque 32-byte values here; their agreement with
Rust and Python is differential evidence (`commit_v6_conformance.rs`).
-/

namespace SIRM
namespace StateCommitmentV6

open RequestEncodingV2

/-- "SIRM/STC/v6\0" -/
def stcV6 : List Nat := [83, 73, 82, 77, 47, 83, 84, 67, 47, 118, 54, 0]
/-- "SIRM/STC/v5\0" -/
def stcV5 : List Nat := [83, 73, 82, 77, 47, 83, 84, 67, 47, 118, 53, 0]

theorem stcV6_length : stcV6.length = 12 := by decide
theorem stcV5_length : stcV5.length = 12 := by decide
theorem stc_v5_ne_v6 : stcV5 ≠ stcV6 := by decide

/-- The hash is collision free (an assumption about the hash, used as a hypothesis). -/
def CollisionFree (H : List Nat → List Nat) : Prop := ∀ a b, H a = H b → a = b

/-- The parts of a state root: three tree roots, config, cache and escrow digests (32 bytes each),
the shape, the clock and the migration totals. -/
structure Comps where
  accounts : Nat
  assets : Nat
  bal : List Nat
  sup : List Nat
  non : List Nat
  cfg : List Nat
  cac : List Nat
  esc : List Nat
  now : Nat
  ts : Nat
  tt : Nat
  dust : Nat
  deriving DecidableEq, Repr

def Dig (x : List Nat) : Prop := x.length = 32 ∧ ∀ d ∈ x, d < 256

def Comps.Valid (c : Comps) : Prop :=
  c.accounts < 256 ^ 4 ∧ c.assets < 256 ^ 4 ∧ Dig c.bal ∧ Dig c.sup ∧ Dig c.non ∧ Dig c.cfg ∧
    Dig c.cac ∧ Dig c.esc ∧ c.now < 256 ^ 8 ∧ c.ts < 256 ^ 16 ∧ c.tt < 256 ^ 16 ∧ c.dust < 256 ^ 16

def payload (dom : List Nat) (c : Comps) : List Nat :=
  dom ++ (be 4 c.accounts ++ (be 4 c.assets ++ (c.bal ++ (c.sup ++ (c.non ++ (c.cfg ++ (c.cac ++
    (c.esc ++ (be 8 c.now ++ (be 16 c.ts ++ (be 16 c.tt ++ be 16 c.dust)))))))))))

def stateRoot (H : List Nat → List Nat) (dom : List Nat) (c : Comps) : List Nat := H (payload dom c)

theorem be_inj {n a b : Nat} (ha : a < 256 ^ n) (hb : b < 256 ^ n) (h : be n a = be n b) : a = b := by
  have := congrArg valBE h
  rwa [valBE_be ha, valBE_be hb] at this

/-- The payload determines its domain and every component. -/
theorem payload_injective {d1 d2 : List Nat} {c1 c2 : Comps} (hd1 : d1.length = 12)
    (hd2 : d2.length = 12) (h1 : c1.Valid) (h2 : c2.Valid)
    (h : payload d1 c1 = payload d2 c2) : d1 = d2 ∧ c1 = c2 := by
  cases c1
  cases c2
  obtain ⟨a1, a2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := h1
  obtain ⟨c1', c2', e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ := h2
  unfold payload at h
  obtain ⟨hd, h⟩ := List.append_inj h (by rw [hd1, hd2])
  obtain ⟨x1, h⟩ := List.append_inj h (by rw [be_length, be_length])
  obtain ⟨x2, h⟩ := List.append_inj h (by rw [be_length, be_length])
  obtain ⟨x3, h⟩ := List.append_inj h (by rw [b3.1, e3.1])
  obtain ⟨x4, h⟩ := List.append_inj h (by rw [b4.1, e4.1])
  obtain ⟨x5, h⟩ := List.append_inj h (by rw [b5.1, e5.1])
  obtain ⟨x6, h⟩ := List.append_inj h (by rw [b6.1, e6.1])
  obtain ⟨x7, h⟩ := List.append_inj h (by rw [b7.1, e7.1])
  obtain ⟨x8, h⟩ := List.append_inj h (by rw [b8.1, e8.1])
  obtain ⟨x9, h⟩ := List.append_inj h (by rw [be_length, be_length])
  obtain ⟨x10, h⟩ := List.append_inj h (by rw [be_length, be_length])
  obtain ⟨x11, x12⟩ := List.append_inj h (by rw [be_length, be_length])
  refine ⟨hd, ?_⟩
  have y1 := be_inj a1 c1' x1
  have y2 := be_inj a2 c2' x2
  have y9 := be_inj b9 e9 x9
  have y10 := be_inj b10 e10 x10
  have y11 := be_inj b11 e11 x11
  have y12 := be_inj b12 e12 x12
  simp only at *
  subst_vars
  rfl

/-- Two equal roots, from a collision-free hash, have equal domains and equal components: the root binds
the shape, the clock, the migration totals and the tree, config, cache and escrow digests. -/
theorem root_binds {H : List Nat → List Nat} (hH : CollisionFree H) {d1 d2 : List Nat}
    {c1 c2 : Comps} (hd1 : d1.length = 12) (hd2 : d2.length = 12) (h1 : c1.Valid) (h2 : c2.Valid)
    (h : stateRoot H d1 c1 = stateRoot H d2 c2) : d1 = d2 ∧ c1 = c2 :=
  payload_injective hd1 hd2 h1 h2 (hH _ _ h)

/-- The same components under the v5 and the v6 domain never give the same root. -/
theorem v5_v6_roots_differ {H : List Nat → List Nat} (hH : CollisionFree H) {c1 c2 : Comps}
    (h1 : c1.Valid) (h2 : c2.Valid) : stateRoot H stcV5 c1 ≠ stateRoot H stcV6 c2 := by
  intro h
  exact stc_v5_ne_v6 (root_binds hH stcV5_length stcV6_length h1 h2 h).1

/-! ### The cache entry -/

/-- Stored outcome: flag (1 accepted, 2 denied), kind tag, cause code (15 is "not disputed"), nonce. -/
structure Out where
  flag : Nat
  kind : Nat
  cause : Nat
  nonce : Nat
  deriving DecidableEq, Repr

def Out.Valid (o : Out) : Prop := o.flag < 256 ∧ o.kind < 256 ∧ o.cause < 256 ∧ o.nonce < 256 ^ 8

def outBytes (o : Out) : List Nat := [o.flag, o.kind, o.cause] ++ be 8 o.nonce

theorem outBytes_length (o : Out) : (outBytes o).length = 11 := by
  unfold outBytes; simp [be_length]

/-- Cache entry: the request in encoding v2, request id included, then the stored outcome. -/
def cacheEntry (r : Req) (o : Out) : List Nat := encode r ++ outBytes o

theorem cacheEntry_injective {r r' : Req} {o o' : Out} (hr : r.Valid) (hr' : r'.Valid)
    (ho : o.Valid) (ho' : o'.Valid) (h : cacheEntry r o = cacheEntry r' o') : r = r' ∧ o = o' := by
  unfold cacheEntry at h
  have hl := congrArg List.length h
  rw [List.length_append, List.length_append, outBytes_length, outBytes_length] at hl
  obtain ⟨he, hb⟩ := List.append_inj h (by omega)
  refine ⟨encode_injective hr hr' he, ?_⟩
  unfold outBytes at hb
  obtain ⟨h3, h8⟩ := List.append_inj hb (by simp)
  have hn := be_inj ho.2.2.2 ho'.2.2.2 h8
  simp only [List.cons.injEq, and_true] at h3
  obtain ⟨hf, hk, hc⟩ := h3
  cases o
  cases o'
  simp only at *
  subst_vars
  rfl

/-- A committed cache entry fixes the cached `resolve` request: its escrow id and its side are part of
what the cache digest covers. -/
theorem cacheEntry_binds_fields {r r' : Req} {o o' : Out} (hr : r.Valid) (hr' : r'.Valid)
    (ho : o.Valid) (ho' : o'.Valid) (h : cacheEntry r o = cacheEntry r' o') :
    r.tag = r'.tag ∧ r.fields = r'.fields := by
  obtain ⟨e, _⟩ := cacheEntry_injective hr hr' ho ho' h
  subst e
  exact ⟨rfl, rfl⟩

end StateCommitmentV6
end SIRM
