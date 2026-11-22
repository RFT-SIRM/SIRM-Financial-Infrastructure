import SIRM.StateCommitmentV6

/-!
# The escrow and config digests of state commitment v6 (checked by SIRM)

    escrow digest = H("SIRM/ESC/v6\0" | n u32 | n id entries of 55 bytes)
      id entry    = deadline u64 | record (flag u8 + 29 bytes, or 30 zero bytes) | filing (flag u8 + 16 bytes, or 17 zero bytes)
    config digest = H("SIRM/CFG/v6\0" | accounts u32 | assets u32 | vault (flag + u32, or 5 zero bytes)
                      | n u32 + n deadlines u64 | migration (flag + 48 bytes, or 49 zero bytes)
                      | controls | limits | ids | clock)      each list: n u32 + n fixed-width entries

Every entry has a fixed width, so a count followed by the entries is unambiguous (`cp_inj`), an optional
part is distinguished by its flag byte (`encOpt_inj`), and under a collision-free hash (a hypothesis,
as in `SIRM.StateCommitmentV6`) the digests determine what they cover: the escrow digest the list of
deadlines, records and filings (`escrowDigest_binds`), the config digest the shape, the vault, the
deadlines, the migration rate and the four policy lists, including the arbiter grants, which are id
entries with tag 10 (`configDigest_binds`).

Not modelled: that the Rust and Python code builds these lists from a machine state, sorting of the
policy lists, SHA-256. Agreement with the code is differential evidence (`commit_v6_conformance.rs`).
-/

namespace SIRM
namespace EscrowConfigDigestV6

open RequestEncodingV2 StateCommitmentV6

/-- "SIRM/ESC/v6\0" -/
def escDomain : List Nat := [83, 73, 82, 77, 47, 69, 83, 67, 47, 118, 54, 0]
/-- "SIRM/CFG/v6\0" -/
def cfgDomain : List Nat := [83, 73, 82, 77, 47, 67, 70, 71, 47, 118, 54, 0]

theorem escDomain_length : escDomain.length = 12 := by decide
theorem cfgDomain_length : cfgDomain.length = 12 := by decide

/-! ### Fixed-width lists with a count -/

theorem flatten_length_fixed {w : Nat} :
    ∀ es : List (List Nat), (∀ e ∈ es, e.length = w) → es.flatten.length = es.length * w
  | [], _ => by simp
  | e :: es, h => by
      simp only [List.flatten_cons, List.length_append, List.length_cons]
      rw [flatten_length_fixed es (fun x hx => h x (by simp [hx])), h e (by simp), Nat.succ_mul,
        Nat.add_comm]

theorem fixed_flatten_inj {w : Nat} (hw : 0 < w) : ∀ es fs : List (List Nat),
    (∀ e ∈ es, e.length = w) → (∀ f ∈ fs, f.length = w) → es.flatten = fs.flatten → es = fs
  | [], [], _, _, _ => rfl
  | [], f :: fs, _, hf, h => by
      have h1 := hf f (by simp)
      simp only [List.flatten_nil, List.flatten_cons] at h
      have h2 := congrArg List.length h
      simp only [List.length_nil, List.length_append] at h2
      omega
  | e :: es, [], he, _, h => by
      have h1 := he e (by simp)
      simp only [List.flatten_nil, List.flatten_cons] at h
      have h2 := congrArg List.length h
      simp only [List.length_nil, List.length_append] at h2
      omega
  | e :: es, f :: fs, he, hf, h => by
      simp only [List.flatten_cons] at h
      have h1 := he e (by simp)
      have h2 := hf f (by simp)
      obtain ⟨a, b⟩ := List.append_inj h (by rw [h1, h2])
      rw [a, fixed_flatten_inj hw es fs (fun x hx => he x (by simp [hx]))
        (fun x hx => hf x (by simp [hx])) b]

/-- A count (u32) followed by the entries. -/
def cp (es : List (List Nat)) : List Nat := be 4 es.length ++ es.flatten

theorem cp_inj {w : Nat} (hw : 0 < w) {es fs : List (List Nat)} {r r' : List Nat}
    (he : ∀ e ∈ es, e.length = w) (hf : ∀ f ∈ fs, f.length = w)
    (hn : es.length < 256 ^ 4) (hm : fs.length < 256 ^ 4) (h : cp es ++ r = cp fs ++ r') :
    es = fs ∧ r = r' := by
  unfold cp at h
  rw [List.append_assoc, List.append_assoc] at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by rw [be_length, be_length])
  have hl := be_inj hn hm h1
  have hfl : es.flatten.length = fs.flatten.length := by
    rw [flatten_length_fixed es he, flatten_length_fixed fs hf, hl]
  obtain ⟨h3, h4⟩ := List.append_inj h2 hfl
  exact ⟨fixed_flatten_inj hw es fs he hf h3, h4⟩

def cpMap {α : Type} (f : α → List Nat) (xs : List α) : List Nat := cp (xs.map f)

theorem map_inj_of {α : Type} (f : α → List Nat) (V : α → Prop)
    (hinj : ∀ a b, V a → V b → f a = f b → a = b) :
    ∀ xs ys : List α, (∀ x ∈ xs, V x) → (∀ y ∈ ys, V y) → xs.map f = ys.map f → xs = ys
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: xs, y :: ys, hx, hy, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      rw [hinj x y (hx x (by simp)) (hy y (by simp)) h.1,
        map_inj_of f V hinj xs ys (fun a ha => hx a (by simp [ha])) (fun a ha => hy a (by simp [ha])) h.2]

theorem cpMap_inj {α : Type} {w : Nat} (hw : 0 < w) (f : α → List Nat) (V : α → Prop)
    (hl : ∀ a, (f a).length = w) (hinj : ∀ a b, V a → V b → f a = f b → a = b)
    {xs ys : List α} {r r' : List Nat} (hx : ∀ x ∈ xs, V x) (hy : ∀ y ∈ ys, V y)
    (hn : xs.length < 256 ^ 4) (hm : ys.length < 256 ^ 4)
    (h : cpMap f xs ++ r = cpMap f ys ++ r') : xs = ys ∧ r = r' := by
  unfold cpMap at h
  have he : ∀ e ∈ xs.map f, e.length = w := by
    intro e he
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp he
    exact hl a
  have hf : ∀ e ∈ ys.map f, e.length = w := by
    intro e he
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp he
    exact hl a
  obtain ⟨h1, h2⟩ := cp_inj hw he hf (by simpa using hn) (by simpa using hm) h
  exact ⟨map_inj_of f V hinj xs ys hx hy h1, h2⟩

/-! ### Optional parts: a flag byte, then the payload or zero fill -/

def encOpt {α : Type} (k : Nat) (g : α → List Nat) : Option α → List Nat
  | none => List.replicate (k + 1) 0
  | some x => 1 :: g x

def OptV {α : Type} (V : α → Prop) : Option α → Prop
  | none => True
  | some x => V x

theorem encOpt_length {α : Type} {k : Nat} {g : α → List Nat} (hg : ∀ x, (g x).length = k) :
    ∀ o : Option α, (encOpt k g o).length = k + 1
  | none => by simp [encOpt]
  | some x => by simp [encOpt, hg x]

theorem encOpt_inj {α : Type} {k : Nat} {g : α → List Nat} {V : α → Prop}
    (hinj : ∀ a b, V a → V b → g a = g b → a = b) :
    ∀ a b : Option α, OptV V a → OptV V b → encOpt k g a = encOpt k g b → a = b
  | none, none, _, _, _ => rfl
  | none, some y, _, _, h => by simp [encOpt, List.replicate_succ] at h
  | some x, none, _, _, h => by simp [encOpt, List.replicate_succ] at h
  | some x, some y, hx, hy, h => by
      simp only [encOpt, List.cons.injEq, true_and] at h
      rw [hinj x y hx hy h]

/-! ### Entries -/

structure Rec where
  dep : Nat
  ben : Nat
  asset : Nat
  amt : Nat
  phase : Nat
  deriving DecidableEq, Repr

def Rec.V (r : Rec) : Prop :=
  r.dep < 256 ^ 4 ∧ r.ben < 256 ^ 4 ∧ r.asset < 256 ^ 4 ∧ r.amt < 256 ^ 16 ∧ r.phase < 256

def encRec (r : Rec) : List Nat :=
  be 4 r.dep ++ (be 4 r.ben ++ (be 4 r.asset ++ (be 16 r.amt ++ [r.phase])))

theorem encRec_length (r : Rec) : (encRec r).length = 29 := by simp [encRec, be_length]

theorem encRec_inj {a b : Rec} (ha : a.V) (hb : b.V) (h : encRec a = encRec b) : a = b := by
  cases a
  cases b
  obtain ⟨a1, a2, a3, a4, a5⟩ := ha
  obtain ⟨b1, b2, b3, b4, b5⟩ := hb
  unfold encRec at h
  obtain ⟨x1, h⟩ := List.append_inj h (by rw [be_length, be_length])
  obtain ⟨x2, h⟩ := List.append_inj h (by rw [be_length, be_length])
  obtain ⟨x3, h⟩ := List.append_inj h (by rw [be_length, be_length])
  obtain ⟨x4, x5⟩ := List.append_inj h (by rw [be_length, be_length])
  simp only [List.cons.injEq, and_true] at x5
  have y1 := be_inj a1 b1 x1
  have y2 := be_inj a2 b2 x2
  have y3 := be_inj a3 b3 x3
  have y4 := be_inj a4 b4 x4
  simp only at *
  subst_vars
  rfl

structure Fil where
  principal : Nat
  claimant : Nat
  at_ : Nat
  deriving DecidableEq, Repr

def Fil.V (f : Fil) : Prop := f.principal < 256 ^ 4 ∧ f.claimant < 256 ^ 4 ∧ f.at_ < 256 ^ 8

def encFil (f : Fil) : List Nat := be 4 f.principal ++ (be 4 f.claimant ++ be 8 f.at_)

theorem encFil_length (f : Fil) : (encFil f).length = 16 := by simp [encFil, be_length]

theorem encFil_inj {a b : Fil} (ha : a.V) (hb : b.V) (h : encFil a = encFil b) : a = b := by
  cases a
  cases b
  obtain ⟨a1, a2, a3⟩ := ha
  obtain ⟨b1, b2, b3⟩ := hb
  unfold encFil at h
  obtain ⟨x1, h⟩ := List.append_inj h (by rw [be_length, be_length])
  obtain ⟨x2, x3⟩ := List.append_inj h (by rw [be_length, be_length])
  have y1 := be_inj a1 b1 x1
  have y2 := be_inj a2 b2 x2
  have y3 := be_inj a3 b3 x3
  simp only at *
  subst_vars
  rfl

/-- One id entry of the escrow table: deadline, record, filing (55 bytes). -/
structure Ent where
  dl : Nat
  rcd : Option Rec
  fl : Option Fil
  deriving DecidableEq, Repr

def Ent.V (e : Ent) : Prop := e.dl < 256 ^ 8 ∧ OptV Rec.V e.rcd ∧ OptV Fil.V e.fl

def encEnt (e : Ent) : List Nat :=
  be 8 e.dl ++ (encOpt 29 encRec e.rcd ++ encOpt 16 encFil e.fl)

theorem encEnt_length (e : Ent) : (encEnt e).length = 55 := by
  simp [encEnt, be_length, encOpt_length encRec_length, encOpt_length encFil_length]

theorem encEnt_inj {a b : Ent} (ha : a.V) (hb : b.V) (h : encEnt a = encEnt b) : a = b := by
  cases a
  cases b
  obtain ⟨a1, a2, a3⟩ := ha
  obtain ⟨b1, b2, b3⟩ := hb
  unfold encEnt at h
  obtain ⟨x1, h⟩ := List.append_inj h (by rw [be_length, be_length])
  obtain ⟨x2, x3⟩ := List.append_inj h
    (by rw [encOpt_length encRec_length, encOpt_length encRec_length])
  have y1 := be_inj a1 b1 x1
  have y2 := encOpt_inj (g := encRec) (V := Rec.V) (fun a b ha hb h => encRec_inj ha hb h) _ _ a2 b2 x2
  have y3 := encOpt_inj (g := encFil) (V := Fil.V) (fun a b ha hb h => encFil_inj ha hb h) _ _ a3 b3 x3
  simp only at *
  subst_vars
  rfl

def escPayload (es : List Ent) : List Nat := escDomain ++ cpMap encEnt es

theorem escrowDigest_binds {H : List Nat → List Nat} (hH : CollisionFree H) {es fs : List Ent}
    (hes : ∀ e ∈ es, e.V) (hfs : ∀ e ∈ fs, e.V) (hn : es.length < 256 ^ 4) (hm : fs.length < 256 ^ 4)
    (h : H (escPayload es) = H (escPayload fs)) : es = fs := by
  have h1 := hH _ _ h
  unfold escPayload at h1
  obtain ⟨_, h2⟩ := List.append_inj h1 (by rw [escDomain_length])
  have h3 : cpMap encEnt es ++ [] = cpMap encEnt fs ++ [] := by simpa using h2
  exact (cpMap_inj (by decide : 0 < 55) encEnt Ent.V encEnt_length
    (fun a b ha hb h => encEnt_inj ha hb h) hes hfs hn hm h3).1

/-! ### The config -/

structure Mig where
  holder : Nat
  recipient : Nat
  src : Nat
  dst : Nat
  num : Nat
  den : Nat
  deriving DecidableEq, Repr

def Mig.V (g : Mig) : Prop :=
  g.holder < 256 ^ 4 ∧ g.recipient < 256 ^ 4 ∧ g.src < 256 ^ 4 ∧ g.dst < 256 ^ 4 ∧
    g.num < 256 ^ 16 ∧ g.den < 256 ^ 16

def encMig (g : Mig) : List Nat :=
  be 4 g.holder ++ (be 4 g.recipient ++ (be 4 g.src ++ (be 4 g.dst ++ (be 16 g.num ++ be 16 g.den))))

theorem encMig_length (g : Mig) : (encMig g).length = 48 := by simp [encMig, be_length]

theorem encMig_inj {a b : Mig} (ha : a.V) (hb : b.V) (h : encMig a = encMig b) : a = b := by
  cases a
  cases b
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb
  unfold encMig at h
  obtain ⟨x1, h⟩ := List.append_inj h (by rw [be_length, be_length])
  obtain ⟨x2, h⟩ := List.append_inj h (by rw [be_length, be_length])
  obtain ⟨x3, h⟩ := List.append_inj h (by rw [be_length, be_length])
  obtain ⟨x4, h⟩ := List.append_inj h (by rw [be_length, be_length])
  obtain ⟨x5, x6⟩ := List.append_inj h (by rw [be_length, be_length])
  have y1 := be_inj a1 b1 x1
  have y2 := be_inj a2 b2 x2
  have y3 := be_inj a3 b3 x3
  have y4 := be_inj a4 b4 x4
  have y5 := be_inj a5 b5 x5
  have y6 := be_inj a6 b6 x6
  simp only at *
  subst_vars
  rfl

/-- A control grant (principal, account). -/
structure Ctl where
  p : Nat
  a : Nat
  deriving DecidableEq, Repr

def Ctl.V (c : Ctl) : Prop := c.p < 256 ^ 4 ∧ c.a < 256 ^ 4
def encCtl (c : Ctl) : List Nat := be 4 c.p ++ be 4 c.a
theorem encCtl_length (c : Ctl) : (encCtl c).length = 8 := by simp [encCtl, be_length]
theorem encCtl_inj {a b : Ctl} (ha : a.V) (hb : b.V) (h : encCtl a = encCtl b) : a = b := by
  cases a
  cases b
  obtain ⟨a1, a2⟩ := ha
  obtain ⟨b1, b2⟩ := hb
  unfold encCtl at h
  obtain ⟨x1, x2⟩ := List.append_inj h (by rw [be_length, be_length])
  have y1 := be_inj a1 b1 x1
  have y2 := be_inj a2 b2 x2
  simp only at *
  subst_vars
  rfl

/-- An id grant (principal, operation tag, escrow id); the arbiter grant has tag 10. -/
structure IdE where
  p : Nat
  tag : Nat
  id : Nat
  deriving DecidableEq, Repr

def IdE.V (c : IdE) : Prop := c.p < 256 ^ 4 ∧ c.tag < 256 ∧ c.id < 256 ^ 4
def encIdE (c : IdE) : List Nat := be 4 c.p ++ (c.tag :: be 4 c.id)
theorem encIdE_length (c : IdE) : (encIdE c).length = 9 := by simp [encIdE, be_length]
theorem encIdE_inj {a b : IdE} (ha : a.V) (hb : b.V) (h : encIdE a = encIdE b) : a = b := by
  cases a
  cases b
  obtain ⟨a1, a2, a3⟩ := ha
  obtain ⟨b1, b2, b3⟩ := hb
  unfold encIdE at h
  obtain ⟨x1, h⟩ := List.append_inj h (by rw [be_length, be_length])
  simp only [List.cons.injEq] at h
  have y1 := be_inj a1 b1 x1
  have y2 := h.1
  have y3 := be_inj a3 b3 h.2
  simp only at *
  subst_vars
  rfl

/-- A spending limit (principal, tag, a, optional b, asset, limit): 34 bytes. -/
structure Lim where
  p : Nat
  tag : Nat
  a : Nat
  b : Option Nat
  asset : Nat
  limit : Nat
  deriving DecidableEq, Repr

def Lim.V (c : Lim) : Prop :=
  c.p < 256 ^ 4 ∧ c.tag < 256 ∧ c.a < 256 ^ 4 ∧ OptV (· < 256 ^ 4) c.b ∧ c.asset < 256 ^ 4 ∧
    c.limit < 256 ^ 16

def encLim (c : Lim) : List Nat :=
  be 4 c.p ++ (c.tag :: (be 4 c.a ++ (encOpt 4 (be 4) c.b ++ (be 4 c.asset ++ be 16 c.limit))))

theorem be4_length (x : Nat) : (be 4 x).length = 4 := be_length 4 x

theorem encLim_length (c : Lim) : (encLim c).length = 34 := by
  simp [encLim, be_length, encOpt_length be4_length]

theorem encLim_inj {a b : Lim} (ha : a.V) (hb : b.V) (h : encLim a = encLim b) : a = b := by
  cases a
  cases b
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb
  unfold encLim at h
  obtain ⟨x1, h⟩ := List.append_inj h (by rw [be_length, be_length])
  simp only [List.cons.injEq] at h
  obtain ⟨x2, h⟩ := h
  obtain ⟨x3, h⟩ := List.append_inj h (by rw [be_length, be_length])
  obtain ⟨x4, h⟩ := List.append_inj h
    (by rw [encOpt_length be4_length, encOpt_length be4_length])
  obtain ⟨x5, x6⟩ := List.append_inj h (by rw [be_length, be_length])
  have y1 := be_inj a1 b1 x1
  have y3 := be_inj a3 b3 x3
  have y4 := encOpt_inj (g := be 4) (V := (· < 256 ^ 4)) (fun a b ha hb h => be_inj ha hb h) _ _ a4 b4 x4
  have y5 := be_inj a5 b5 x5
  have y6 := be_inj a6 b6 x6
  simp only at *
  subst_vars
  rfl

/-- The configuration committed by the config digest. -/
structure Cfg where
  accounts : Nat
  assets : Nat
  vault : Option Nat
  deadlines : List Nat
  mig : Option Mig
  controls : List Ctl
  limits : List Lim
  ids : List IdE
  clock : List Nat
  deriving DecidableEq, Repr

def Cfg.V (c : Cfg) : Prop :=
  c.accounts < 256 ^ 4 ∧ c.assets < 256 ^ 4 ∧ OptV (· < 256 ^ 4) c.vault ∧
  (∀ d ∈ c.deadlines, d < 256 ^ 8) ∧ c.deadlines.length < 256 ^ 4 ∧ OptV Mig.V c.mig ∧
  (∀ x ∈ c.controls, x.V) ∧ c.controls.length < 256 ^ 4 ∧
  (∀ x ∈ c.limits, x.V) ∧ c.limits.length < 256 ^ 4 ∧
  (∀ x ∈ c.ids, x.V) ∧ c.ids.length < 256 ^ 4 ∧
  (∀ x ∈ c.clock, x < 256 ^ 4) ∧ c.clock.length < 256 ^ 4

def cfgPayload (c : Cfg) : List Nat :=
  cfgDomain ++ (be 4 c.accounts ++ (be 4 c.assets ++ (encOpt 4 (be 4) c.vault ++
    (cpMap (be 8) c.deadlines ++ (encOpt 48 encMig c.mig ++ (cpMap encCtl c.controls ++
      (cpMap encLim c.limits ++ (cpMap encIdE c.ids ++ cpMap (be 4) c.clock))))))))

theorem configDigest_binds {H : List Nat → List Nat} (hH : CollisionFree H) {c d : Cfg}
    (hc : c.V) (hd : d.V) (h : H (cfgPayload c) = H (cfgPayload d)) : c = d := by
  have h1 := hH _ _ h
  cases c
  cases d
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14⟩ := hc
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14⟩ := hd
  unfold cfgPayload at h1
  obtain ⟨_, h1⟩ := List.append_inj h1 (by rw [cfgDomain_length])
  obtain ⟨x1, h1⟩ := List.append_inj h1 (by rw [be_length, be_length])
  obtain ⟨x2, h1⟩ := List.append_inj h1 (by rw [be_length, be_length])
  obtain ⟨x3, h1⟩ := List.append_inj h1
    (by rw [encOpt_length be4_length, encOpt_length be4_length])
  obtain ⟨x4, h1⟩ := cpMap_inj (by decide : 0 < 8) (be 8) (· < 256 ^ 8) (be_length 8)
    (fun a b ha hb h => be_inj ha hb h) c4 d4 c5 d5 h1
  obtain ⟨x5, h1⟩ := List.append_inj h1
    (by rw [encOpt_length encMig_length, encOpt_length encMig_length])
  obtain ⟨x6, h1⟩ := cpMap_inj (by decide : 0 < 8) encCtl Ctl.V encCtl_length
    (fun a b ha hb h => encCtl_inj ha hb h) c7 d7 c8 d8 h1
  obtain ⟨x7, h1⟩ := cpMap_inj (by decide : 0 < 34) encLim Lim.V encLim_length
    (fun a b ha hb h => encLim_inj ha hb h) c9 d9 c10 d10 h1
  obtain ⟨x8, h1⟩ := cpMap_inj (by decide : 0 < 9) encIdE IdE.V encIdE_length
    (fun a b ha hb h => encIdE_inj ha hb h) c11 d11 c12 d12 h1
  have x9 := (cpMap_inj (r := []) (r' := []) (by decide : 0 < 4) (be 4) (· < 256 ^ 4) be4_length
    (fun a b ha hb h => be_inj ha hb h) c13 d13 c14 d14 (by simpa using h1)).1
  have y1 := be_inj c1 d1 x1
  have y2 := be_inj c2 d2 x2
  have y3 := encOpt_inj (g := be 4) (V := (· < 256 ^ 4)) (fun a b ha hb h => be_inj ha hb h) _ _ c3 d3 x3
  have y5 := encOpt_inj (g := encMig) (V := Mig.V) (fun a b ha hb h => encMig_inj ha hb h) _ _ c6 d6 x5
  simp only at *
  subst_vars
  rfl

end EscrowConfigDigestV6
end SIRM
