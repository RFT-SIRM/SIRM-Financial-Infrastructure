import SIRM.RequestEncodingV2

/-!
# Signed request envelope v3 (checked by SIRM)

The byte layout of the signed request wire format of `engineering/canonical_encoding/SPEC_signed_request_v3.md`:

    wire:            "SIRM/SRQ/v3\0" (12) | chain_id u64 | suite u16 | request encoding v2 | signature
    signing message: "SIRM/SIG/v3\0" (12) | chain_id u64 | suite u16 | key id (32) | request encoding v2

Bytes are natural numbers below 256. The request part is `SIRM.RequestEncodingV2`; the signature length
comes from the suite, so the request is the middle of the wire and nothing is guessed.

Proved: the decoder inverts the encoder on valid envelopes, distinct valid envelopes have distinct wires,
every wire the decoder accepts is the canonical encoding of the envelope it returns (which is valid), a
wire with any other domain (the v2 wire domain, or the signing-message domain) is rejected, and the
signing message determines chain, suite, key id and the whole request, so a signature over it cannot be
moved to another request.

Not modelled: the signature itself (verification is in Rust for Ed25519 and in the Python reference for
ML-DSA and the hybrid), the key registry, the verification order after decoding. The suite table is
hand-written, so its agreement with the Rust and Python codecs is differential evidence.
-/

namespace SIRM
namespace SignedEnvelopeV3

open RequestEncodingV2

/-- "SIRM/SRQ/v3\0" -/
def wireDomain : List Nat := [83, 73, 82, 77, 47, 83, 82, 81, 47, 118, 51, 0]
/-- "SIRM/SIG/v3\0" -/
def sigDomain : List Nat := [83, 73, 82, 77, 47, 83, 73, 71, 47, 118, 51, 0]
/-- "SIRM/SRQ/v2\0", the previous wire domain. -/
def v2WireDomain : List Nat := [83, 73, 82, 77, 47, 83, 82, 81, 47, 118, 50, 0]

theorem wireDomain_length : wireDomain.length = 12 := by decide
theorem sigDomain_length : sigDomain.length = 12 := by decide
theorem wire_ne_sig : sigDomain ≠ wireDomain := by decide
theorem wire_ne_v2 : v2WireDomain ≠ wireDomain := by decide

/-- Signature length of a known suite: Ed25519 (1), ML-DSA-65 (2), hybrid (257), SLH-DSA-128s (3). -/
def sigLen : Nat → Option Nat
  | 1 => some 64
  | 2 => some 3309
  | 257 => some 3373
  | 3 => some 7856
  | _ => none

structure Env where
  chain : Nat
  suite : Nat
  req : Req
  sig : List Nat
  deriving DecidableEq, Repr

def Env.Valid (e : Env) : Prop :=
  e.chain < 256 ^ 8 ∧ e.suite < 256 ^ 2 ∧ e.req.Valid ∧ sigLen e.suite = some e.sig.length ∧
    ∀ d ∈ e.sig, d < 256

def encodeEnv (e : Env) : List Nat :=
  wireDomain ++ (be 8 e.chain ++ (be 2 e.suite ++ (encode e.req ++ e.sig)))

def decodeEnv (l : List Nat) : Option Env :=
  if l.take 12 = wireDomain then
    match takeNum 8 (l.drop 12) with
    | none => none
    | some (ch, l1) =>
      match takeNum 2 l1 with
      | none => none
      | some (su, l2) =>
        match sigLen su with
        | none => none
        | some k =>
          if k ≤ l2.length then
            match decode (l2.take (l2.length - k)) with
            | none => none
            | some r => some ⟨ch, su, r, l2.drop (l2.length - k)⟩
          else none
  else none

/-- The message that is signed: it carries the key id and no signature. -/
def sigMsg (chain suite : Nat) (kid : List Nat) (r : Req) : List Nat :=
  sigDomain ++ (be 8 chain ++ (be 2 suite ++ (kid ++ encode r)))

theorem decodeEnv_encodeEnv (e : Env) (hv : e.Valid) : decodeEnv (encodeEnv e) = some e := by
  obtain ⟨hc, hs, hr, hk, hb⟩ := hv
  have hdom : (encodeEnv e).take 12 = wireDomain := by
    unfold encodeEnv
    exact List.take_left' wireDomain_length
  have hdrop : (encodeEnv e).drop 12 = be 8 e.chain ++ (be 2 e.suite ++ (encode e.req ++ e.sig)) := by
    unfold encodeEnv
    exact List.drop_left' wireDomain_length
  unfold decodeEnv
  rw [if_pos hdom, hdrop, takeNum_append hc]
  simp only
  rw [takeNum_append hs]
  simp only [hk]
  have hlen : (encode e.req ++ e.sig).length - e.sig.length = (encode e.req).length := by
    simp
  have hle : e.sig.length ≤ (encode e.req ++ e.sig).length := by simp
  rw [if_pos hle, hlen, List.take_left' rfl, decode_encode e.req hr]
  simp only
  rw [List.drop_left' rfl]

/-- Everything the decoder accepts is canonical and valid. -/
theorem encodeEnv_decodeEnv {l : List Nat} {e : Env} (hb : ∀ d ∈ l, d < 256)
    (h : decodeEnv l = some e) : encodeEnv e = l ∧ e.Valid := by
  unfold decodeEnv at h
  by_cases hd : l.take 12 = wireDomain
  · rw [if_pos hd] at h
    have hb1 : ∀ d ∈ l.drop 12, d < 256 := fun d hm => hb d (List.mem_of_mem_drop hm)
    cases h1 : takeNum 8 (l.drop 12) with
    | none => simp [h1] at h
    | some p1 =>
      obtain ⟨ch, l1⟩ := p1
      rw [h1] at h
      simp only at h
      obtain ⟨hc, e1⟩ := takeNum_canonical hb1 h1
      have hb2 : ∀ d ∈ l1, d < 256 := by
        intro d hm; apply hb1; rw [← e1]; exact List.mem_append_right _ hm
      cases h2 : takeNum 2 l1 with
      | none => simp [h2] at h
      | some p2 =>
        obtain ⟨su, l2⟩ := p2
        rw [h2] at h
        simp only at h
        obtain ⟨hs, e2⟩ := takeNum_canonical hb2 h2
        have hb3 : ∀ d ∈ l2, d < 256 := by
          intro d hm; apply hb2; rw [← e2]; exact List.mem_append_right _ hm
        cases h3 : sigLen su with
        | none => simp [h3] at h
        | some k =>
          rw [h3] at h
          simp only at h
          by_cases hk : k ≤ l2.length
          · rw [if_pos hk] at h
            cases h4 : decode (l2.take (l2.length - k)) with
            | none => simp [h4] at h
            | some r =>
              rw [h4] at h
              simp only [Option.some.injEq] at h
              subst h
              have hbt : ∀ d ∈ l2.take (l2.length - k), d < 256 :=
                fun d hm => hb3 d (List.mem_of_mem_take hm)
              obtain ⟨er, hrv⟩ := encode_decode hbt h4
              have hbd : ∀ d ∈ l2.drop (l2.length - k), d < 256 :=
                fun d hm => hb3 d (List.mem_of_mem_drop hm)
              have hsl : (l2.drop (l2.length - k)).length = k := by
                rw [List.length_drop]; omega
              refine ⟨?_, hc, hs, hrv, ?_, hbd⟩
              · show wireDomain ++ (be 8 ch ++ (be 2 su ++ (encode r ++ l2.drop (l2.length - k)))) = l
                rw [er, List.take_append_drop, e2, e1, ← hd, List.take_append_drop]
              · show sigLen su = some (l2.drop (l2.length - k)).length
                rw [hsl, h3]
          · rw [if_neg hk] at h
            simp at h
  · rw [if_neg hd] at h
    simp at h

theorem encodeEnv_injective {e f : Env} (he : e.Valid) (hf : f.Valid)
    (h : encodeEnv e = encodeEnv f) : e = f := by
  have := congrArg decodeEnv h
  rw [decodeEnv_encodeEnv e he, decodeEnv_encodeEnv f hf] at this
  exact Option.some.inj this

/-- A wire with any other domain is rejected. -/
theorem decodeEnv_bad_domain {l : List Nat} (h : l.take 12 ≠ wireDomain) : decodeEnv l = none := by
  unfold decodeEnv
  rw [if_neg h]

/-- A v2 wire is rejected by the v3 decoder. -/
theorem v2_wire_rejected {l : List Nat} (h : l.take 12 = v2WireDomain) : decodeEnv l = none := by
  apply decodeEnv_bad_domain
  rw [h]; exact wire_ne_v2

/-- The signing message is never a wire: the two domains differ, so a signature cannot be replayed as
a wire, nor a wire taken for a message to be signed. -/
theorem sigMsg_not_a_wire (chain suite : Nat) (kid : List Nat) (r : Req) :
    decodeEnv (sigMsg chain suite kid r) = none := by
  apply decodeEnv_bad_domain
  unfold sigMsg
  rw [List.take_left' sigDomain_length]
  exact wire_ne_sig

/-- The signing message fixes chain, suite, key id and the whole request: two valid signing messages of
the same shape are equal only if all four are. -/
theorem sigMsg_injective {c1 c2 s1 s2 : Nat} {k1 k2 : List Nat} {r1 r2 : Req}
    (hc1 : c1 < 256 ^ 8) (hc2 : c2 < 256 ^ 8) (hs1 : s1 < 256 ^ 2) (hs2 : s2 < 256 ^ 2)
    (hk1 : k1.length = 32) (hk2 : k2.length = 32) (hr1 : r1.Valid) (hr2 : r2.Valid)
    (h : sigMsg c1 s1 k1 r1 = sigMsg c2 s2 k2 r2) :
    c1 = c2 ∧ s1 = s2 ∧ k1 = k2 ∧ r1 = r2 := by
  unfold sigMsg at h
  have h1 := List.append_cancel_left h
  have t1 := congrArg (takeNum 8) h1
  rw [takeNum_append hc1, takeNum_append hc2] at t1
  simp only [Option.some.injEq, Prod.mk.injEq] at t1
  obtain ⟨rfl, h2⟩ := t1
  have t2 := congrArg (takeNum 2) h2
  rw [takeNum_append hs1, takeNum_append hs2] at t2
  simp only [Option.some.injEq, Prod.mk.injEq] at t2
  obtain ⟨rfl, h3⟩ := t2
  obtain ⟨hk, he⟩ := List.append_inj h3 (by rw [hk1, hk2])
  exact ⟨rfl, rfl, hk, encode_injective hr1 hr2 he⟩

end SignedEnvelopeV3
end SIRM
