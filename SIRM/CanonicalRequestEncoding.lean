import Mathlib
import SIRM.CanonicalEncoding

/-!
# Canonical Request Encoding: Round Trip

Composes the fixed-width codec of `SIRM.CanonicalEncoding` into the request
layout of `engineering/canonical_encoding/SPEC_v0.md` (without the constant
domain-tag prefix) and proves that decoding an encoded in-range request returns
that request, and that distinct in-range requests have distinct encodings.

The request here is a concrete bounded record (`Nat` fields with explicit range
predicates), not the polymorphic `FinancialTransactionRequest` of the envelope
layer. Linking the two (account/asset indices, the Lean `Nat` versus bounded
fields) and the inverse direction on arbitrary digit lists are not proved here.
-/

namespace SIRM

/-- Operation payloads of the proposed v0 layout. -/
inductive FtxOp
  | transfer (source destination asset amount : Nat)
  | issue (issuer recipient asset amount : Nat)
  | burn (holder asset amount : Nat)
  deriving DecidableEq, Repr

/-- Concrete request record: opaque ID, principal, nonce, operation. -/
structure FtxRequest where
  requestId : Nat
  principal : Nat
  nonce : Nat
  op : FtxOp
  deriving DecidableEq, Repr

/-- Range predicate: every field fits its fixed width (32/4/8 digits; 4 per index; 16 per amount). -/
def FtxRequest.Valid (r : FtxRequest) : Prop :=
  r.requestId < 256 ^ 32 ∧ r.principal < 256 ^ 4 ∧ r.nonce < 256 ^ 8 ∧
  match r.op with
  | .transfer a b c m => a < 256 ^ 4 ∧ b < 256 ^ 4 ∧ c < 256 ^ 4 ∧ m < 256 ^ 16
  | .issue a b c m => a < 256 ^ 4 ∧ b < 256 ^ 4 ∧ c < 256 ^ 4 ∧ m < 256 ^ 16
  | .burn h a m => h < 256 ^ 4 ∧ a < 256 ^ 4 ∧ m < 256 ^ 16

def encodeRequest (r : FtxRequest) : List Nat :=
  beDigits 32 r.requestId ++ beDigits 4 r.principal ++ beDigits 8 r.nonce ++
  match r.op with
  | .transfer a b c m =>
      0 :: (beDigits 4 a ++ beDigits 4 b ++ beDigits 4 c ++ beDigits 16 m)
  | .issue a b c m =>
      1 :: (beDigits 4 a ++ beDigits 4 b ++ beDigits 4 c ++ beDigits 16 m)
  | .burn h a m =>
      2 :: (beDigits 4 h ++ beDigits 4 a ++ beDigits 16 m)

/-- Read `n` digits; reject if fewer than `n` remain. -/
def takeNum (n : Nat) (l : List Nat) : Option (Nat × List Nat) :=
  if n ≤ l.length then some (beValue (l.take n), l.drop n) else none

theorem takeNum_append {n v : Nat} (h : v < 256 ^ n) (rest : List Nat) :
    takeNum n (beDigits n v ++ rest) = some (v, rest) := by
  have hl := beDigits_length n v
  have hle : n ≤ (beDigits n v ++ rest).length := by
    rw [List.length_append, hl]
    exact Nat.le_add_right n rest.length
  unfold takeNum
  rw [if_pos hle, List.take_left' hl, List.drop_left' hl, beValue_beDigits_of_lt h]

theorem takeNum_beDigits {n v : Nat} (h : v < 256 ^ n) :
    takeNum n (beDigits n v) = some (v, []) := by
  simpa using takeNum_append h []

def decodeRequest (l : List Nat) : Option FtxRequest := do
  let (rid, l) ← takeNum 32 l
  let (p, l) ← takeNum 4 l
  let (n, l) ← takeNum 8 l
  match l with
  | [] => none
  | tag :: l =>
    if tag = 0 then
      let (a, l) ← takeNum 4 l
      let (b, l) ← takeNum 4 l
      let (c, l) ← takeNum 4 l
      let (m, l) ← takeNum 16 l
      if l = [] then some ⟨rid, p, n, .transfer a b c m⟩ else none
    else if tag = 1 then
      let (a, l) ← takeNum 4 l
      let (b, l) ← takeNum 4 l
      let (c, l) ← takeNum 4 l
      let (m, l) ← takeNum 16 l
      if l = [] then some ⟨rid, p, n, .issue a b c m⟩ else none
    else if tag = 2 then
      let (h, l) ← takeNum 4 l
      let (a, l) ← takeNum 4 l
      let (m, l) ← takeNum 16 l
      if l = [] then some ⟨rid, p, n, .burn h a m⟩ else none
    else none

theorem decode_encode (r : FtxRequest) (hv : r.Valid) :
    decodeRequest (encodeRequest r) = some r := by
  obtain ⟨rid, p, n, op⟩ := r
  cases op with
  | transfer a b c m =>
    simp only [FtxRequest.Valid] at hv
    obtain ⟨h1, h2, h3, ha, hb, hc, hm⟩ := hv
    simp [encodeRequest, decodeRequest, takeNum_append h1, takeNum_append h2,
      takeNum_append h3, takeNum_append ha, takeNum_append hb,
      takeNum_append hc, takeNum_beDigits hm]
  | issue a b c m =>
    simp only [FtxRequest.Valid] at hv
    obtain ⟨h1, h2, h3, ha, hb, hc, hm⟩ := hv
    simp [encodeRequest, decodeRequest, takeNum_append h1, takeNum_append h2,
      takeNum_append h3, takeNum_append ha, takeNum_append hb,
      takeNum_append hc, takeNum_beDigits hm]
  | burn h a m =>
    simp only [FtxRequest.Valid] at hv
    obtain ⟨h1, h2, h3, hh, ha, hm⟩ := hv
    simp [encodeRequest, decodeRequest, takeNum_append h1, takeNum_append h2,
      takeNum_append h3, takeNum_append hh, takeNum_append ha,
      takeNum_beDigits hm]

/-- Distinct in-range requests have distinct canonical encodings. -/
theorem encodeRequest_injective {r s : FtxRequest}
    (hr : r.Valid) (hs : s.Valid) (h : encodeRequest r = encodeRequest s) :
    r = s := by
  have := congrArg decodeRequest h
  rw [decode_encode r hr, decode_encode s hs] at this
  exact Option.some.inj this

end SIRM
