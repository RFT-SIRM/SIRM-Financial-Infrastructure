import SIRM.KeyRegistry

/-!
# Authenticated Step: Linking Authorization to Any State Machine

Wraps an arbitrary state machine `step : State → Request → State × Outcome` (for example the
integrated financial processor) with the signature-suite authorization of
`SIRM.SignatureSuite`. The wrapper is generic on purpose: nothing here depends on the
accounting rules, so every property of the machine carries over unchanged.

What is proved: a request whose authorization is not accepted never reaches the machine and
leaves the state untouched (so it consumes no nonce and no cache entry); a processed request
was accepted under the registered suite of its principal; frozen or revoked accounts are never
processed; and any invariant that the machine preserves is preserved by the wrapper.

Assumed, not proved: that the signed message determines the request (injectivity of the
signing message, proved separately for the canonical encoding), and that the signature scheme
is unforgeable.
-/

namespace SIRM

section Authenticated

variable {State Request Outcome Principal PublicKey Message Signature : Type}

/-- A request together with the authorization data that arrived with it. -/
structure AuthRequest (Request Message Signature : Type) where
  request : Request
  claimedSuite : SuiteId
  message : Message
  signature : Signature

/-- Result of an authenticated step. -/
inductive AuthOutcome (Outcome : Type) where
  | processed (o : Outcome)
  | rejected (r : AuthResult)

/-- Authenticate, then (and only then) run the machine. -/
def authStep (M : SignatureModel PublicKey Message Signature) (P : SuitePolicy)
    (registry : Principal → Option (KeyRecord PublicKey)) (principalOf : Request → Principal)
    (step : State → Request → State × Outcome) (s : State)
    (a : AuthRequest Request Message Signature) : State × AuthOutcome Outcome :=
  match authorize M P registry (principalOf a.request) a.claimedSuite a.message a.signature with
  | .accepted => ((step s a.request).1, .processed (step s a.request).2)
  | r => (s, .rejected r)

/-- A request whose authorization is not accepted leaves the state unchanged. -/
theorem authStep_rejected_state (M : SignatureModel PublicKey Message Signature)
    (P : SuitePolicy) (registry : Principal → Option (KeyRecord PublicKey))
    (principalOf : Request → Principal) (step : State → Request → State × Outcome)
    (s : State) (a : AuthRequest Request Message Signature)
    (h : authorize M P registry (principalOf a.request) a.claimedSuite a.message
      a.signature ≠ .accepted) :
    (authStep M P registry principalOf step s a).1 = s := by
  unfold authStep
  cases hr : authorize M P registry (principalOf a.request) a.claimedSuite a.message a.signature
  all_goals first | exact absurd hr h | rfl

/-- A processed request was authorized: its principal is registered under the claimed suite,
the suite is permitted, and the abstract verifier accepted. -/
theorem authStep_processed_authorized (M : SignatureModel PublicKey Message Signature)
    (P : SuitePolicy) (registry : Principal → Option (KeyRecord PublicKey))
    (principalOf : Request → Principal) (step : State → Request → State × Outcome)
    (s : State) (a : AuthRequest Request Message Signature) (o : Outcome)
    (h : (authStep M P registry principalOf step s a).2 = .processed o) :
    ∃ r, registry (principalOf a.request) = some r ∧ r.suite = a.claimedSuite ∧
      P.permits a.claimedSuite = true ∧
      M.verify a.claimedSuite r.key a.message a.signature = true := by
  unfold authStep at h
  cases hr : authorize M P registry (principalOf a.request) a.claimedSuite a.message a.signature
  all_goals first
    | (rw [hr] at h; cases h; done)
    | (rw [hr] at h; simp at h; done)
    | skip
  exact (authorize_accepted_iff M P registry _ _ _ _).1 hr

/-- The wrapper preserves every invariant the machine preserves. -/
theorem authStep_preserves (Inv : State → Prop) (M : SignatureModel PublicKey Message Signature)
    (P : SuitePolicy) (registry : Principal → Option (KeyRecord PublicKey))
    (principalOf : Request → Principal) (step : State → Request → State × Outcome)
    (hstep : ∀ s r, Inv s → Inv (step s r).1) (s : State)
    (a : AuthRequest Request Message Signature) (h : Inv s) :
    Inv (authStep M P registry principalOf step s a).1 := by
  unfold authStep
  cases authorize M P registry (principalOf a.request) a.claimedSuite a.message a.signature
  all_goals first | exact hstep _ _ h | exact h

/-- A frozen or revoked account never reaches the machine. -/
theorem authStep_frozen_not_processed (M : SignatureModel PublicKey Message Signature)
    (P : SuitePolicy) [DecidableEq Principal] (reg : KeyRegistry Principal PublicKey)
    (principalOf : Request → Principal) (step : State → Request → State × Outcome)
    (s : State) (a : AuthRequest Request Message Signature) (acct : Account PublicKey)
    (hp : reg (principalOf a.request) = some acct) (hf : acct.frozen = true ∨ acct.revoked = true) :
    (authStep M P reg.view principalOf step s a).1 = s := by
  apply authStep_rejected_state
  rw [frozen_or_revoked_not_authorized M P reg _ _ _ _ acct hp hf]
  intro h; cases h

end Authenticated

/-! ### Concrete regression examples (toy counter machine; reuses the toy model of
`SIRM.SignatureSuite`) -/

section Demo

/-- A counter that increments on every processed request and reports the old value. -/
def demoCounter : Nat → Nat → Nat × Nat := fun s _ => (s + 1, s)

-- principal 0 is registered under suite 2: processed, counter moves 10 → 11
example : ((authStep demoModel demoPolicy demoRegistry (fun r : Nat => r) demoCounter 10
    ⟨0, 2, 0, 0⟩).1) = 11 := by decide
-- unknown principal 5: rejected, counter stays 10
example : ((authStep demoModel demoPolicy demoRegistry (fun r : Nat => r) demoCounter 10
    ⟨5, 2, 0, 0⟩).1) = 10 := by decide
-- registered principal claiming the deprecated suite 1: rejected, counter stays 10
example : ((authStep demoModel demoPolicy demoRegistry (fun r : Nat => r) demoCounter 10
    ⟨0, 1, 0, 0⟩).1) = 10 := by decide

end Demo

end SIRM
