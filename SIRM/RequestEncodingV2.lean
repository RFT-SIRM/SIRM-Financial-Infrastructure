/-!
# Request Encoding v2: round trip and canonical inputs (checked by SIRM)

Lean model of the byte layout of `engineering/canonical_encoding/SPEC_request_v2.md` (request encoding v1
plus the arbiter operation `resolve`), without the constant 12-byte domain prefix:

    request id (32) | principal u32 | nonce u64 | tag u8 | fields (widths by tag)

The eleven operations are one table `widths` (tag to field widths), so one proof covers all of them.
Proved, without Mathlib:

* `decode_encode`: decoding the encoding of a valid request returns that request;
* `encode_injective`: distinct valid requests have distinct encodings;
* `encode_decode`: **every** byte string the decoder accepts is the encoding of the request it returns
  (no second spelling of an accepted request), and that request is valid, which includes the
  restriction that the `resolve` side byte is 0 or 1;
* `decode_unknown_tag`: a tag outside the table is rejected. Trailing and missing bytes need no separate
  theorem: a longer or shorter input is a different list, so `encode_decode` says it is accepted only if
  it is itself the canonical encoding of some valid request.

Not covered, stated so that no reader assumes it: the domain prefix; that the table agrees with the Rust
and Python codecs (that is the differential evidence of `request_v2_conformance.rs`, not a refinement
proof); the signature layer and the state commitment; escrow ids and amounts are plain naturals bounded
only by their field widths.
-/

namespace SIRM
namespace RequestEncodingV2

/-! ### Fixed-width big-endian numbers -/

/-- Little-endian digits, `n` of them (the value modulo `256 ^ n`). -/
def le : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, v => (v % 256) :: le n (v / 256)

/-- Value of a little-endian digit list. -/
def val : List Nat → Nat
  | [] => 0
  | d :: l => d + 256 * val l

/-- Big-endian digits, exactly `n` of them. -/
def be (n v : Nat) : List Nat := (le n v).reverse

/-- Value of a big-endian digit list. -/
def valBE (l : List Nat) : Nat := val l.reverse

theorem le_length (n v : Nat) : (le n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [le, ih]

theorem be_length (n v : Nat) : (be n v).length = n := by
  simp [be, le_length]

theorem val_le (n : Nat) : ∀ v, v < 256 ^ n → val (le n v) = v := by
  induction n with
  | zero => intro v h; simp at h; simp [le, val, h]
  | succ n ih =>
    intro v h
    have h2 : v / 256 < 256 ^ n := by
      rw [Nat.pow_succ] at h
      exact (Nat.div_lt_iff_lt_mul (by omega)).2 h
    simp only [le, val]
    rw [ih _ h2]
    omega

theorem val_lt : ∀ l : List Nat, (∀ d ∈ l, d < 256) → val l < 256 ^ l.length := by
  intro l
  induction l with
  | nil => intro _; simp [val]
  | cons d l ih =>
    intro h
    have hd : d < 256 := h d (by simp)
    have hl := ih (fun x hx => h x (by simp [hx]))
    simp only [val, List.length_cons, Nat.pow_succ]
    omega

theorem le_val : ∀ l : List Nat, (∀ d ∈ l, d < 256) → le l.length (val l) = l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons d l ih =>
    intro h
    have hd : d < 256 := h d (by simp)
    have hl := ih (fun x hx => h x (by simp [hx]))
    simp only [val, List.length_cons, le]
    have e1 : (d + 256 * val l) % 256 = d := by omega
    have e2 : (d + 256 * val l) / 256 = val l := by omega
    rw [e1, e2, hl]

theorem valBE_be {n v : Nat} (h : v < 256 ^ n) : valBE (be n v) = v := by
  simp [valBE, be, val_le n v h]

theorem be_valBE {l : List Nat} (h : ∀ d ∈ l, d < 256) : be l.length (valBE l) = l := by
  have h' : ∀ d ∈ l.reverse, d < 256 := fun d hd => h d (List.mem_reverse.1 hd)
  have := le_val l.reverse h'
  simp only [List.length_reverse] at this
  simp [be, valBE, this]

theorem valBE_lt {l : List Nat} (h : ∀ d ∈ l, d < 256) : valBE l < 256 ^ l.length := by
  have h' : ∀ d ∈ l.reverse, d < 256 := fun d hd => h d (List.mem_reverse.1 hd)
  have := val_lt l.reverse h'
  simpa [valBE] using this

theorem be_digits {n v d : Nat} (h : d ∈ be n v) : d < 256 := by
  have : ∀ n v, ∀ d ∈ le n v, d < 256 := by
    intro n
    induction n with
    | zero => intro v d h; simp [le] at h
    | succ n ih =>
      intro v d h
      simp only [le, List.mem_cons] at h
      rcases h with h | h
      · omega
      · exact ih _ _ h
  exact this n v d (List.mem_reverse.1 h)

/-! ### Reading a field -/

/-- Read `n` digits; reject if fewer than `n` remain. -/
def takeNum (n : Nat) (l : List Nat) : Option (Nat × List Nat) :=
  if n ≤ l.length then some (valBE (l.take n), l.drop n) else none

theorem takeNum_append {n v : Nat} (h : v < 256 ^ n) (rest : List Nat) :
    takeNum n (be n v ++ rest) = some (v, rest) := by
  have hl := be_length n v
  have hle : n ≤ (be n v ++ rest).length := by
    rw [List.length_append, hl]; exact Nat.le_add_right n rest.length
  unfold takeNum
  rw [if_pos hle, List.take_left' hl, List.drop_left' hl, valBE_be h]

theorem takeNum_canonical {n : Nat} {l : List Nat} {v : Nat} {rest : List Nat}
    (hb : ∀ d ∈ l, d < 256) (h : takeNum n l = some (v, rest)) :
    v < 256 ^ n ∧ be n v ++ rest = l := by
  unfold takeNum at h
  split at h
  · rename_i hn
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have htake : ∀ d ∈ l.take n, d < 256 := fun d hd => hb d (List.mem_of_mem_take hd)
    have hlen : (l.take n).length = n := by simp [List.length_take]; omega
    refine ⟨?_, ?_⟩
    · have := valBE_lt htake
      rwa [hlen] at this
    · have := be_valBE htake
      rw [hlen] at this
      rw [this, List.take_append_drop]
  · simp at h

/-! ### The table of operations and the request layout -/

/-- Field widths by operation tag; `none` for an unknown tag.
0 transfer, 1 issue, 2 burn, 3 open, 4 release, 5 cancel, 6 expire, 7 dispute, 8 advance, 9 migrate,
10 resolve (new in v2: escrow id u32, side u8). -/
def widths : Nat → Option (List Nat)
  | 0 => some [4, 4, 4, 16]
  | 1 => some [4, 4, 4, 16]
  | 2 => some [4, 4, 16]
  | 3 => some [4, 4, 4, 4, 16]
  | 4 => some [4]
  | 5 => some [4]
  | 6 => some [4]
  | 7 => some [4, 4]
  | 8 => some [8]
  | 9 => some [16]
  | 10 => some [4, 1]
  | _ => none

/-- Every field fits its width, and the field list has the right length. -/
def Fits : List Nat → List Nat → Prop
  | [], [] => True
  | w :: ws, v :: vs => v < 256 ^ w ∧ Fits ws vs
  | _, _ => False

def encFields : List Nat → List Nat → List Nat
  | w :: ws, v :: vs => be w v ++ encFields ws vs
  | _, _ => []

def decFields : List Nat → List Nat → Option (List Nat × List Nat)
  | [], l => some ([], l)
  | w :: ws, l =>
    match takeNum w l with
    | none => none
    | some (v, l1) =>
      match decFields ws l1 with
      | none => none
      | some (vs, l2) => some (v :: vs, l2)

/-- A request: opaque 32-byte id, principal, nonce, operation tag and its fields in order. -/
structure Req where
  rid : Nat
  principal : Nat
  nonce : Nat
  tag : Nat
  fields : List Nat
  deriving DecidableEq, Repr

/-- The `resolve` side byte is 0 (depositor) or 1 (beneficiary). -/
def sideOk (tag : Nat) (fields : List Nat) : Prop :=
  tag = 10 → ∀ f, fields[1]? = some f → f ≤ 1

instance (tag : Nat) (fields : List Nat) : Decidable (sideOk tag fields) := by
  unfold sideOk; infer_instance

def Req.Valid (r : Req) : Prop :=
  r.rid < 256 ^ 32 ∧ r.principal < 256 ^ 4 ∧ r.nonce < 256 ^ 8 ∧ r.tag < 256 ∧
  ∃ ws, widths r.tag = some ws ∧ Fits ws r.fields ∧ sideOk r.tag r.fields

def encode (r : Req) : List Nat :=
  be 32 r.rid ++ be 4 r.principal ++ be 8 r.nonce ++ [r.tag] ++
    match widths r.tag with
    | some ws => encFields ws r.fields
    | none => []

def decode (l : List Nat) : Option Req :=
  match takeNum 32 l with
  | none => none
  | some (rid, l1) =>
    match takeNum 4 l1 with
    | none => none
    | some (p, l2) =>
      match takeNum 8 l2 with
      | none => none
      | some (n, l3) =>
        match l3 with
        | [] => none
        | tag :: l4 =>
          match widths tag with
          | none => none
          | some ws =>
            match decFields ws l4 with
            | none => none
            | some (fs, rest) =>
              if rest = [] ∧ sideOk tag fs then some ⟨rid, p, n, tag, fs⟩ else none

theorem decFields_append {ws vs : List Nat} (h : Fits ws vs) (rest : List Nat) :
    decFields ws (encFields ws vs ++ rest) = some (vs, rest) := by
  induction ws generalizing vs with
  | nil => cases vs with
    | nil => simp [decFields, encFields]
    | cons _ _ => exact h.elim
  | cons w ws ih => cases vs with
    | nil => exact h.elim
    | cons v vs =>
      obtain ⟨hv, hf⟩ := h
      simp only [encFields, List.append_assoc, decFields]
      rw [takeNum_append hv]
      simp only [ih hf]

theorem decFields_canonical {ws : List Nat} {l vs rest : List Nat} (hb : ∀ d ∈ l, d < 256)
    (h : decFields ws l = some (vs, rest)) : Fits ws vs ∧ encFields ws vs ++ rest = l := by
  induction ws generalizing l vs rest with
  | nil =>
    simp only [decFields, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [Fits, encFields]
  | cons w ws ih =>
    simp only [decFields] at h
    cases h1 : takeNum w l with
    | none => simp [h1] at h
    | some p1 =>
      obtain ⟨v, l1⟩ := p1
      rw [h1] at h
      simp only at h
      cases h2 : decFields ws l1 with
      | none => simp [h2] at h
      | some p2 =>
        obtain ⟨vs', l2⟩ := p2
        rw [h2] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hv, hl1⟩ := takeNum_canonical hb h1
        have hb1 : ∀ d ∈ l1, d < 256 := by
          intro d hd
          apply hb
          rw [← hl1]
          exact List.mem_append_right _ hd
        obtain ⟨hf, he⟩ := ih hb1 h2
        refine ⟨⟨hv, hf⟩, ?_⟩
        simp only [encFields, List.append_assoc]
        rw [he, hl1]

theorem decode_encode (r : Req) (hv : r.Valid) : decode (encode r) = some r := by
  obtain ⟨rid, p, n, tag, fs⟩ := r
  obtain ⟨h1, h2, h3, ht, ws, hw, hf, hs⟩ := hv
  simp only at h1 h2 h3 ht hw hf hs
  have e : encode ⟨rid, p, n, tag, fs⟩ =
      be 32 rid ++ (be 4 p ++ (be 8 n ++ (tag :: (encFields ws fs ++ [])))) := by
    simp [encode, hw]
  rw [e]
  unfold decode
  rw [takeNum_append h1]
  simp only
  rw [takeNum_append h2]
  simp only
  rw [takeNum_append h3]
  have hd := decFields_append hf []
  simp only [List.append_nil] at hd
  simp [hw, hd, hs]

/-- Distinct valid requests have distinct encodings. -/
theorem encode_injective {r s : Req} (hr : r.Valid) (hs : s.Valid)
    (h : encode r = encode s) : r = s := by
  have := congrArg decode h
  rw [decode_encode r hr, decode_encode s hs] at this
  exact Option.some.inj this

/-- Everything the decoder accepts is canonical: it is the encoding of the request it returns, and that
request is valid. There is no other byte string for an accepted request. -/
theorem encode_decode {l : List Nat} {r : Req} (hb : ∀ d ∈ l, d < 256)
    (h : decode l = some r) : encode r = l ∧ r.Valid := by
  unfold decode at h
  cases h1 : takeNum 32 l with
  | none => simp [h1] at h
  | some p1 =>
    obtain ⟨rid, l1⟩ := p1
    rw [h1] at h
    simp only at h
    obtain ⟨hr, e1⟩ := takeNum_canonical hb h1
    have hb1 : ∀ d ∈ l1, d < 256 := fun d hd => hb d (by rw [← e1]; exact List.mem_append_right _ hd)
    cases h2 : takeNum 4 l1 with
    | none => simp [h2] at h
    | some p2 =>
      obtain ⟨p, l2⟩ := p2
      rw [h2] at h
      simp only at h
      obtain ⟨hp, e2⟩ := takeNum_canonical hb1 h2
      have hb2 : ∀ d ∈ l2, d < 256 := fun d hd => hb1 d (by rw [← e2]; exact List.mem_append_right _ hd)
      cases h3 : takeNum 8 l2 with
      | none => simp [h3] at h
      | some p3 =>
        obtain ⟨n, l3⟩ := p3
        rw [h3] at h
        simp only at h
        obtain ⟨hn, e3⟩ := takeNum_canonical hb2 h3
        have hb3 : ∀ d ∈ l3, d < 256 := fun d hd => hb2 d (by rw [← e3]; exact List.mem_append_right _ hd)
        cases l3 with
        | nil => simp at h
        | cons tag l4 =>
          have htag : tag < 256 := hb3 tag (by simp)
          have hb4 : ∀ d ∈ l4, d < 256 := fun d hd => hb3 d (by simp [hd])
          simp only at h
          cases hw : widths tag with
          | none => simp [hw] at h
          | some ws =>
            rw [hw] at h
            simp only at h
            cases h4 : decFields ws l4 with
            | none => simp [h4] at h
            | some p4 =>
              obtain ⟨fs, rest⟩ := p4
              rw [h4] at h
              simp only at h
              split at h
              · rename_i hc
                simp only [Option.some.injEq] at h
                subst h
                obtain ⟨hf, e4⟩ := decFields_canonical hb4 h4
                obtain ⟨hrest, hside⟩ := hc
                subst hrest
                refine ⟨?_, hr, hp, hn, htag, ws, hw, hf, hside⟩
                simp only [encode, hw, List.append_nil] at e4 ⊢
                rw [List.append_assoc (be 32 rid ++ be 4 p ++ be 8 n), List.singleton_append, e4]
                rw [← e1, ← e2, ← e3]
                simp
              · simp at h

/-- A tag outside the table is rejected. -/
theorem decode_unknown_tag (rid p n : Nat) (hr : rid < 256 ^ 32) (hp : p < 256 ^ 4) (hn : n < 256 ^ 8)
    (tag : Nat) (hw : widths tag = none) (rest : List Nat) :
    decode (be 32 rid ++ be 4 p ++ be 8 n ++ tag :: rest) = none := by
  have e : be 32 rid ++ be 4 p ++ be 8 n ++ tag :: rest =
      be 32 rid ++ (be 4 p ++ (be 8 n ++ (tag :: rest))) := by simp
  rw [e]
  unfold decode
  rw [takeNum_append hr]
  simp only
  rw [takeNum_append hp]
  simp only
  rw [takeNum_append hn]
  simp [hw]

/-! ### Concrete checks of the table -/

example : widths 10 = some [4, 1] := rfl
example : widths 11 = none := rfl

/-- The wire vector `resolve_beneficiary` of `request_v2_vectors.json` (request id `00 01 .. 1f`,
principal 4, nonce 10, escrow 2, side 1) without the domain prefix. -/
example : encode ⟨valBE (List.range 32), 4, 10, 10, [2, 1]⟩ =
    List.range 32 ++ [0, 0, 0, 4] ++ [0, 0, 0, 0, 0, 0, 0, 10] ++ [10] ++ [0, 0, 0, 2] ++ [1] := by
  decide +kernel

end RequestEncodingV2
end SIRM
