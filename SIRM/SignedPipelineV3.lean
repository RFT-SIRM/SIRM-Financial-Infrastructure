import SIRM.AuthenticatedStep
import SIRM.SignedEnvelopeV3
import SIRM.IntegratedPipeline

/-!
# From wire bytes to the integrated pipeline (checked by SIRM)

This file joins three layers that were proved separately: the byte layout of the signed request
(`SIRM.SignedEnvelopeV3`), the authentication wrapper (`SIRM.AuthenticatedStep`, with the abstract
signature model of `SIRM.SignatureSuite`) and the integrated request pipeline
(`SIRM.IntegratedPipeline`, with the nonce ceiling `processCapped`).

`wireStep` takes the bytes that arrive and does what `SPEC_signed_request_v3.md` describes:

1. decode the envelope (anything that is not a canonical v3 wire is `malformed`);
2. refuse another chain (`wrongChain`);
3. look the principal up, build the signing message from the registered key (domain, chain, suite, key id,
   request encoding) and run the authentication (`authStep`);
4. only then run the machine on the request.

Proved: a wire that is malformed, for another chain, or not authenticated leaves the whole state
untouched, so it consumes no nonce and writes no cache entry (`wirePipeline_rejected_untouched`); a wire that
reached the machine decoded to a canonical valid envelope for this chain, its principal is registered under
the claimed suite, the suite is permitted and the verifier accepted the signature over the signing message
(`wire_processed`); that message determines chain, suite, key id and the whole request, so the signature
cannot be moved to another request (`processed_signature_binds_request`); and every invariant of the
machine, in particular that no stored nonce exceeds `2^64 - 1`, holds after any byte string
(`wirePipeline_nonces_le`).

Assumed, not proved: the verifier (`SignatureModel`) is an abstract function, no claim is made about
unforgeability; the key id function `kidOf` returns 32 bytes; the Rust and Python code follow the same
order of checks (differential evidence, `signed_v3_conformance.rs`); the PQ suites have no Rust verifier.
-/

namespace SIRM
namespace SignedPipelineV3

open SignedEnvelopeV3 RequestEncodingV2

variable {State Outcome PublicKey : Type}

/-- Result of a wire step: decoding, the chain check, then the authenticated machine step. -/
inductive WireOutcome (Outcome : Type) where
  | malformed
  | wrongChain
  | auth (o : AuthOutcome Outcome)

/-- The signing message of an envelope, built from the registered key of its principal (empty when the
principal is unknown: the authentication refuses it before the message is looked at). -/
def messageOf (kidOf : KeyRecord PublicKey → List Nat) (registry : Nat → Option (KeyRecord PublicKey))
    (e : Env) : List Nat :=
  match registry e.req.principal with
  | some r => sigMsg e.chain e.suite (kidOf r) e.req
  | none => []

def wireStep (chainId : Nat) (kidOf : KeyRecord PublicKey → List Nat)
    (M : SignatureModel PublicKey (List Nat) (List Nat)) (P : SuitePolicy)
    (registry : Nat → Option (KeyRecord PublicKey)) (step : State → Req → State × Outcome)
    (s : State) (l : List Nat) : State × WireOutcome Outcome :=
  match decodeEnv l with
  | none => (s, .malformed)
  | some e =>
    if e.chain = chainId then
      let r := authStep M P registry (fun q : Req => q.principal) step s
        ⟨e.req, e.suite, messageOf kidOf registry e, e.sig⟩
      (r.1, .auth r.2)
    else (s, .wrongChain)

/-- Anything that did not reach the machine leaves the state as it was. -/
theorem wire_unprocessed_state (chainId : Nat) (kidOf : KeyRecord PublicKey → List Nat)
    (M : SignatureModel PublicKey (List Nat) (List Nat)) (P : SuitePolicy)
    (registry : Nat → Option (KeyRecord PublicKey)) (step : State → Req → State × Outcome)
    (s : State) (l : List Nat)
    (h : ∀ o, (wireStep chainId kidOf M P registry step s l).2 ≠ .auth (.processed o)) :
    (wireStep chainId kidOf M P registry step s l).1 = s := by
  unfold wireStep at h ⊢
  cases hd : decodeEnv l with
  | none => rfl
  | some e =>
    rw [hd] at h
    simp only at h ⊢
    by_cases hc : e.chain = chainId
    · rw [if_pos hc] at h ⊢
      simp only at h ⊢
      apply authStep_rejected_state
      intro hacc
      apply h ((step s e.req).2)
      simp only [authStep, hacc]
    · rw [if_neg hc]

/-- A wire that reached the machine was authenticated: it decoded, it is for this chain, its principal is
registered under the claimed suite, the suite is permitted and the verifier accepted the signature over the
signing message built from the registered key. -/
theorem wire_processed (chainId : Nat) (kidOf : KeyRecord PublicKey → List Nat)
    (M : SignatureModel PublicKey (List Nat) (List Nat)) (P : SuitePolicy)
    (registry : Nat → Option (KeyRecord PublicKey)) (step : State → Req → State × Outcome)
    (s : State) (l : List Nat) (o : Outcome)
    (h : (wireStep chainId kidOf M P registry step s l).2 = .auth (.processed o)) :
    ∃ e, decodeEnv l = some e ∧ e.chain = chainId ∧
      ∃ r, registry e.req.principal = some r ∧ r.suite = e.suite ∧ P.permits e.suite = true ∧
        M.verify e.suite r.key (sigMsg e.chain e.suite (kidOf r) e.req) e.sig = true := by
  unfold wireStep at h
  cases hd : decodeEnv l with
  | none => rw [hd] at h; simp at h
  | some e =>
    rw [hd] at h
    simp only at h
    by_cases hc : e.chain = chainId
    · rw [if_pos hc] at h
      simp only [WireOutcome.auth.injEq] at h
      obtain ⟨r, hr, hs, hp, hv⟩ := authStep_processed_authorized M P registry
        (fun q : Req => q.principal) step s ⟨e.req, e.suite, messageOf kidOf registry e, e.sig⟩ o h
      refine ⟨e, rfl, hc, r, hr, hs, hp, ?_⟩
      simp only [messageOf, hr] at hv
      exact hv
    · rw [if_neg hc] at h; simp at h

/-- The envelope that reached the machine is canonical and valid when the bytes are bytes. -/
theorem wire_processed_canonical (chainId : Nat) (kidOf : KeyRecord PublicKey → List Nat)
    (M : SignatureModel PublicKey (List Nat) (List Nat)) (P : SuitePolicy)
    (registry : Nat → Option (KeyRecord PublicKey)) (step : State → Req → State × Outcome)
    (s : State) (l : List Nat) (o : Outcome) (hb : ∀ d ∈ l, d < 256)
    (h : (wireStep chainId kidOf M P registry step s l).2 = .auth (.processed o)) :
    ∃ e, decodeEnv l = some e ∧ encodeEnv e = l ∧ e.Valid ∧ e.chain = chainId := by
  obtain ⟨e, hd, hc, _⟩ := wire_processed chainId kidOf M P registry step s l o h
  obtain ⟨he, hv⟩ := encodeEnv_decodeEnv hb hd
  exact ⟨e, hd, he, hv, hc⟩

/-- The signature is bound to the request: whatever other chain, suite, 32-byte key id and valid request
produce the same signing message are the ones of the envelope that reached the machine. -/
theorem processed_signature_binds_request {c2 s2 : Nat} {k2 : List Nat} {r2 : Req}
    {e : Env} (hv : e.Valid) (hk : k2.length = 32) (kid : List Nat) (hkid : kid.length = 32)
    (hc2 : c2 < 256 ^ 8) (hs2 : s2 < 256 ^ 2) (hr2 : r2.Valid)
    (h : sigMsg e.chain e.suite kid e.req = sigMsg c2 s2 k2 r2) :
    e.chain = c2 ∧ e.suite = s2 ∧ kid = k2 ∧ e.req = r2 :=
  sigMsg_injective hv.1 hc2 hv.2.1 hs2 hkid hk hv.2.2.1 hr2 h

end SignedPipelineV3

/-! ### The integrated pipeline behind the wire -/

namespace SignedPipelineV3

open SignedEnvelopeV3 RequestEncodingV2 IntegratedPipeline

variable {Core Denial PublicKey : Type}

/-- The integrated pipeline, with the nonce ceiling, behind the wire. -/
def wirePipeline (R : Rules Nat Req Core Denial) (N chainId : Nat)
    (kidOf : KeyRecord PublicKey → List Nat)
    (M : SignatureModel PublicKey (List Nat) (List Nat)) (P : SuitePolicy)
    (registry : Nat → Option (KeyRecord PublicKey))
    (s : State Nat Nat Req Core Denial) (l : List Nat) :
    State Nat Nat Req Core Denial × WireOutcome (Outcome Denial) :=
  wireStep chainId kidOf M P registry (fun s q => processCapped R s q.rid q N) s l

/-- Bytes that are malformed, for another chain or not authenticated leave core, nonces and cache
untouched: no nonce is consumed, no receipt is written. -/
theorem wirePipeline_rejected_untouched (R : Rules Nat Req Core Denial) (N chainId : Nat)
    (kidOf : KeyRecord PublicKey → List Nat)
    (M : SignatureModel PublicKey (List Nat) (List Nat)) (P : SuitePolicy)
    (registry : Nat → Option (KeyRecord PublicKey)) (s : State Nat Nat Req Core Denial)
    (l : List Nat) (h : ∀ o, (wirePipeline R N chainId kidOf M P registry s l).2 ≠ .auth (.processed o)) :
    (wirePipeline R N chainId kidOf M P registry s l).1 = s :=
  wire_unprocessed_state chainId kidOf M P registry _ s l h

/-- After any byte string no stored nonce exceeds `N` (for the wire, `N = 2^64 - 1`, so every stored nonce
fits the eight bytes of the request encoding), provided none did before. -/
theorem wirePipeline_nonces_le (R : Rules Nat Req Core Denial) (N chainId : Nat)
    (kidOf : KeyRecord PublicKey → List Nat)
    (M : SignatureModel PublicKey (List Nat) (List Nat)) (P : SuitePolicy)
    (registry : Nat → Option (KeyRecord PublicKey)) (s : State Nat Nat Req Core Denial)
    (l : List Nat) (h : ∀ q, s.nonces q ≤ N) :
    ∀ q, (wirePipeline R N chainId kidOf M P registry s l).1.nonces q ≤ N := by
  unfold wirePipeline wireStep
  cases hd : decodeEnv l with
  | none => simpa using h
  | some e =>
    simp only
    by_cases hc : e.chain = chainId
    · rw [if_pos hc]
      simp only
      exact authStep_preserves (fun t : State Nat Nat Req Core Denial => ∀ q, t.nonces q ≤ N) M P
        registry (fun q : Req => q.principal) (fun t q => processCapped R t q.rid q N)
        (fun t q ht => processCapped_nonces_le R t q.rid q N ht) s
        ⟨e.req, e.suite, messageOf kidOf registry e, e.sig⟩ h
    · rw [if_neg hc]; exact h

end SignedPipelineV3
end SIRM
