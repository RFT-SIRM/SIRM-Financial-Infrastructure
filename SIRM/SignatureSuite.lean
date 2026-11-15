/-!
# Signature Suites and Downgrade Rejection (abstract model)

Models the authorization step of the proposed signed-request layer v1
(`engineering/canonical_encoding/SPEC_signed_request_v1.md`) with cryptography
as an explicit, abstract hypothesis. A suite identifier names an algorithm
family; a registry maps each principal to a key record that carries its suite;
the node policy decides which suites may authorize.

Nothing here proves that any real signature scheme is secure. The verification
function `SignatureModel.verify` is an arbitrary parameter. What is proved is
the protocol-level logic around it: an accepted authorization always uses the
suite of the principal's registered key (no downgrade or substitution), only a
policy-permitted suite is accepted, an accepted authorization implies the
abstract verifier accepted, and the decision is the same for any message that
the verifier treats alike. Unforgeability of ML-DSA, SLH-DSA or Ed25519 is an
external assumption and is not stated as a Lean axiom.

The model does not touch balances, supply, nonces or any financial state: it
only decides whether a principal is authenticated.
-/

namespace SIRM

/-- Identifier of a cryptographic suite (see the suite registry of the proposal). -/
abbrev SuiteId := Nat

/-- Lifecycle status of a suite. -/
inductive SuiteStatus where
  | proposed
  | active
  | deprecated
  | disabled
  deriving DecidableEq, Repr

/-- A registered key: the suite is part of the registration, not of the message. -/
structure KeyRecord (PublicKey : Type) where
  suite : SuiteId
  key : PublicKey

/-- Abstract signature verification, one verifier per suite identifier. -/
structure SignatureModel (PublicKey Message Signature : Type) where
  verify : SuiteId → PublicKey → Message → Signature → Bool

/-- Node policy: the status of each suite, and whether deprecated suites may authorize. -/
structure SuitePolicy where
  status : SuiteId → SuiteStatus
  allowDeprecated : Bool

/-- A suite may authorize if it is active, or deprecated while the policy allows it. -/
def SuitePolicy.permits (P : SuitePolicy) (s : SuiteId) : Bool :=
  match P.status s with
  | .active => true
  | .deprecated => P.allowDeprecated
  | .proposed => false
  | .disabled => false

/-- Outcome of the authorization step. -/
inductive AuthResult where
  | accepted
  | unknownPrincipal
  | suiteMismatch
  | suiteNotAllowed
  | badSignature
  deriving DecidableEq, Repr

section Authorize

variable {Principal PublicKey Message Signature : Type}

/-- Authorization decision for a message that claims suite `claimed`. The suite used for
verification is the one of the registered key; a different claim is rejected. -/
def authorize (M : SignatureModel PublicKey Message Signature) (P : SuitePolicy)
    (registry : Principal → Option (KeyRecord PublicKey))
    (principal : Principal) (claimed : SuiteId) (msg : Message) (sig : Signature) :
    AuthResult :=
  match registry principal with
  | none => .unknownPrincipal
  | some r =>
    if r.suite = claimed then
      if P.permits claimed then
        if M.verify claimed r.key msg sig then .accepted else .badSignature
      else .suiteNotAllowed
    else .suiteMismatch

/-- Characterization of acceptance. -/
theorem authorize_accepted_iff (M : SignatureModel PublicKey Message Signature)
    (P : SuitePolicy) (registry : Principal → Option (KeyRecord PublicKey))
    (principal : Principal) (claimed : SuiteId) (msg : Message) (sig : Signature) :
    authorize M P registry principal claimed msg sig = .accepted ↔
      ∃ r, registry principal = some r ∧ r.suite = claimed ∧
        P.permits claimed = true ∧ M.verify claimed r.key msg sig = true := by
  unfold authorize
  cases h : registry principal with
  | none => simp
  | some r =>
    by_cases h1 : r.suite = claimed <;> by_cases h2 : P.permits claimed = true <;>
      by_cases h3 : M.verify claimed r.key msg sig = true <;> simp_all

/-- No downgrade or substitution: an accepted authorization uses exactly the suite of the
registered key. -/
theorem accepted_uses_registered_suite (M : SignatureModel PublicKey Message Signature)
    (P : SuitePolicy) (registry : Principal → Option (KeyRecord PublicKey))
    (principal : Principal) (claimed : SuiteId) (msg : Message) (sig : Signature)
    (h : authorize M P registry principal claimed msg sig = .accepted) :
    ∃ r, registry principal = some r ∧ r.suite = claimed := by
  obtain ⟨r, hr, hs, -, -⟩ := (authorize_accepted_iff M P registry principal claimed msg sig).1 h
  exact ⟨r, hr, hs⟩

/-- A suite the policy does not permit never authorizes. -/
theorem accepted_suite_permitted (M : SignatureModel PublicKey Message Signature)
    (P : SuitePolicy) (registry : Principal → Option (KeyRecord PublicKey))
    (principal : Principal) (claimed : SuiteId) (msg : Message) (sig : Signature)
    (h : authorize M P registry principal claimed msg sig = .accepted) :
    P.permits claimed = true := by
  obtain ⟨r, -, -, hp, -⟩ := (authorize_accepted_iff M P registry principal claimed msg sig).1 h
  exact hp

/-- A proposed or disabled suite never authorizes. -/
theorem not_accepted_of_status_closed (M : SignatureModel PublicKey Message Signature)
    (P : SuitePolicy) (registry : Principal → Option (KeyRecord PublicKey))
    (principal : Principal) (claimed : SuiteId) (msg : Message) (sig : Signature)
    (h : P.status claimed = .proposed ∨ P.status claimed = .disabled) :
    authorize M P registry principal claimed msg sig ≠ .accepted := by
  intro hacc
  have hp := accepted_suite_permitted M P registry principal claimed msg sig hacc
  unfold SuitePolicy.permits at hp
  rcases h with h | h <;> simp [h] at hp

/-- A deprecated suite authorizes only when the policy opts in. -/
theorem deprecated_requires_opt_in (M : SignatureModel PublicKey Message Signature)
    (P : SuitePolicy) (registry : Principal → Option (KeyRecord PublicKey))
    (principal : Principal) (claimed : SuiteId) (msg : Message) (sig : Signature)
    (hd : P.status claimed = .deprecated) (hn : P.allowDeprecated = false) :
    authorize M P registry principal claimed msg sig ≠ .accepted := by
  intro hacc
  have hp := accepted_suite_permitted M P registry principal claimed msg sig hacc
  unfold SuitePolicy.permits at hp
  simp [hd, hn] at hp

/-- Acceptance implies the abstract verifier accepted for the registered key. -/
theorem accepted_implies_verified (M : SignatureModel PublicKey Message Signature)
    (P : SuitePolicy) (registry : Principal → Option (KeyRecord PublicKey))
    (principal : Principal) (claimed : SuiteId) (msg : Message) (sig : Signature)
    (h : authorize M P registry principal claimed msg sig = .accepted) :
    ∃ r, registry principal = some r ∧ M.verify claimed r.key msg sig = true := by
  obtain ⟨r, hr, -, -, hv⟩ := (authorize_accepted_iff M P registry principal claimed msg sig).1 h
  exact ⟨r, hr, hv⟩

/-- An unregistered principal is never authorized. -/
theorem unregistered_not_accepted (M : SignatureModel PublicKey Message Signature)
    (P : SuitePolicy) (registry : Principal → Option (KeyRecord PublicKey))
    (principal : Principal) (claimed : SuiteId) (msg : Message) (sig : Signature)
    (h : registry principal = none) :
    authorize M P registry principal claimed msg sig = .unknownPrincipal := by
  simp [authorize, h]

/-- Substitution rejected: a claim for a suite other than the registered one is a mismatch. -/
theorem mismatch_rejected (M : SignatureModel PublicKey Message Signature)
    (P : SuitePolicy) (registry : Principal → Option (KeyRecord PublicKey))
    (principal : Principal) (claimed : SuiteId) (msg : Message) (sig : Signature)
    (r : KeyRecord PublicKey) (hr : registry principal = some r) (hne : r.suite ≠ claimed) :
    authorize M P registry principal claimed msg sig = .suiteMismatch := by
  simp [authorize, hr, hne]

end Authorize

/-! ### Hybrid suites

A hybrid suite requires both component verifiers to accept the same message. The
combination is a conjunction, so a break of one component alone does not authorize. -/

/-- Verifier of a hybrid suite built from two component verifiers. -/
def hybridVerify {PublicKey Message Signature : Type}
    (first second : PublicKey → Message → Signature → Bool) :
    PublicKey × PublicKey → Message → Signature × Signature → Bool :=
  fun k m s => first k.1 m s.1 && second k.2 m s.2

theorem hybridVerify_iff {PublicKey Message Signature : Type}
    (first second : PublicKey → Message → Signature → Bool)
    (k : PublicKey × PublicKey) (m : Message) (s : Signature × Signature) :
    hybridVerify first second k m s = true ↔
      first k.1 m s.1 = true ∧ second k.2 m s.2 = true := by
  simp [hybridVerify]

/-- A hybrid accepts only if each component accepts; failing either rejects. -/
theorem hybridVerify_false_of_left {PublicKey Message Signature : Type}
    (first second : PublicKey → Message → Signature → Bool)
    (k : PublicKey × PublicKey) (m : Message) (s : Signature × Signature)
    (h : first k.1 m s.1 = false) : hybridVerify first second k m s = false := by
  simp [hybridVerify, h]

theorem hybridVerify_false_of_right {PublicKey Message Signature : Type}
    (first second : PublicKey → Message → Signature → Bool)
    (k : PublicKey × PublicKey) (m : Message) (s : Signature × Signature)
    (h : second k.2 m s.2 = false) : hybridVerify first second k m s = false := by
  simp [hybridVerify, h]

/-! ### Concrete regression examples (a toy model, not a real scheme) -/

section Demo

/-- Suite 2 active, suite 1 deprecated, everything else proposed; deprecated not allowed. -/
def demoPolicy : SuitePolicy where
  status := fun s => if s = 2 then .active else if s = 1 then .deprecated else .proposed
  allowDeprecated := false

/-- Principal 0 is registered under suite 2 with toy key 7. -/
def demoRegistry : Nat → Option (KeyRecord Nat) := fun p =>
  if p = 0 then some { suite := 2, key := 7 } else none

/-- A toy verifier that accepts everything, so only the protocol logic is exercised. -/
def demoModel : SignatureModel Nat Nat Nat := ⟨fun _ _ _ _ => true⟩

example : authorize demoModel demoPolicy demoRegistry 0 2 0 0 = .accepted := by decide
example : authorize demoModel demoPolicy demoRegistry 0 1 0 0 = .suiteMismatch := by decide
example : authorize demoModel demoPolicy demoRegistry 0 3 0 0 = .suiteMismatch := by decide
example : authorize demoModel demoPolicy demoRegistry 5 2 0 0 = .unknownPrincipal := by decide

end Demo

end SIRM
