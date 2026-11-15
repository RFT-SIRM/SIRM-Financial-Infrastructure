import SIRM.SignatureSuite

/-!
# Key Registry Transitions (abstract model)

Models the proposed key lifecycle of `docs/POST_QUANTUM_SECURITY_ARCHITECTURE.md`:
registration, rotation, freezing, revocation and recovery of the key that authorizes a
principal, as a state machine that is kept apart from the financial state.

Cryptography stays abstract: `isPQ` says which suite identifiers are post-quantum, and the
actor of a command (`currentKey` or `recoveryKey`) is the outcome of an earlier signature
check, not something decided here. What is proved:

* a rejected command changes nothing;
* only the targeted principal's entry can change;
* once an account is bound to a post-quantum key, no transition replaces it by a
  non-post-quantum key (the legacy-key rule);
* a frozen account cannot rotate, a recovery needs the recovery actor and a registered
  recovery credential;
* a frozen or revoked account is invisible to the signature check, so it cannot authorize;
* key transitions never change the financial state, so any invariant of the financial
  state is preserved (frame property).

Not modelled: who may register an account, expiry, thresholds, challenge delays, and the
hash commitment to a successor key.
-/

namespace SIRM

/-- Who authenticated the command, decided by an earlier signature check. -/
inductive Actor where
  | currentKey
  | recoveryKey
  deriving DecidableEq, Repr

inductive KeyError where
  | unknownAccount
  | alreadyRegistered
  | frozen
  | revoked
  | notAuthorized
  | noRecovery
  | pqDowngrade
  deriving DecidableEq, Repr

/-- One principal's key state. -/
structure Account (PublicKey : Type) where
  key : KeyRecord PublicKey
  recovery : Option (KeyRecord PublicKey)
  frozen : Bool
  revoked : Bool
  /-- A post-quantum key has been bound to this account. -/
  pqBound : Bool

inductive KeyCmd (Principal PublicKey : Type) where
  | register (p : Principal) (key : KeyRecord PublicKey) (recovery : Option (KeyRecord PublicKey))
  | rotate (p : Principal) (new : KeyRecord PublicKey)
  | freeze (p : Principal)
  | revoke (p : Principal)
  | recover (p : Principal) (new : KeyRecord PublicKey)

/-- The key registry: a partial map from principals to accounts. -/
abbrev KeyRegistry (Principal PublicKey : Type) := Principal → Option (Account PublicKey)

section Transitions

variable {Principal PublicKey : Type} [DecidableEq Principal]

/-- Point update of the registry. -/
def KeyRegistry.set (reg : KeyRegistry Principal PublicKey) (p : Principal)
    (a : Account PublicKey) : KeyRegistry Principal PublicKey :=
  fun q => if q = p then some a else reg q

/-- Apply one command; `isPQ` classifies post-quantum suites. -/
def keyApply (isPQ : SuiteId → Bool) (reg : KeyRegistry Principal PublicKey)
    (actor : Actor) : KeyCmd Principal PublicKey → Except KeyError (KeyRegistry Principal PublicKey)
  | .register p key recovery =>
    match reg p with
    | some _ => .error .alreadyRegistered
    | none =>
      .ok (reg.set p { key := key, recovery := recovery, frozen := false, revoked := false,
                       pqBound := isPQ key.suite })
  | .rotate p new =>
    match reg p with
    | none => .error .unknownAccount
    | some a =>
      if actor ≠ .currentKey then .error .notAuthorized
      else if a.revoked then .error .revoked
      else if a.frozen then .error .frozen
      else if a.pqBound ∧ isPQ new.suite = false then .error .pqDowngrade
      else .ok (reg.set p { a with key := new, pqBound := a.pqBound || isPQ new.suite })
  | .freeze p =>
    match reg p with
    | none => .error .unknownAccount
    | some a => .ok (reg.set p { a with frozen := true })
  | .revoke p =>
    match reg p with
    | none => .error .unknownAccount
    | some a =>
      if actor ≠ .recoveryKey then .error .notAuthorized
      else if a.recovery = none then .error .noRecovery
      else .ok (reg.set p { a with frozen := true, revoked := true })
  | .recover p new =>
    match reg p with
    | none => .error .unknownAccount
    | some a =>
      if actor ≠ .recoveryKey then .error .notAuthorized
      else if a.recovery = none then .error .noRecovery
      else if a.pqBound ∧ isPQ new.suite = false then .error .pqDowngrade
      else .ok (reg.set p { a with key := new, frozen := false, revoked := false,
                                   pqBound := a.pqBound || isPQ new.suite })

/-- The command's target principal. -/
def KeyCmd.target : KeyCmd Principal PublicKey → Principal
  | .register p _ _ => p
  | .rotate p _ => p
  | .freeze p => p
  | .revoke p => p
  | .recover p _ => p

/-- Only the target principal's entry can change. -/
theorem keyApply_other_unchanged (isPQ : SuiteId → Bool) (reg : KeyRegistry Principal PublicKey)
    (actor : Actor) (c : KeyCmd Principal PublicKey) (reg' : KeyRegistry Principal PublicKey)
    (h : keyApply isPQ reg actor c = .ok reg') (q : Principal) (hq : q ≠ c.target) :
    reg' q = reg q := by
  cases c with
  | register p key recovery =>
    simp only [keyApply] at h
    cases hp : reg p <;> rw [hp] at h <;> try contradiction
    cases h
    simp [KeyRegistry.set, KeyCmd.target] at hq ⊢; simp [hq]
  | rotate p new =>
    simp only [keyApply] at h
    cases hp : reg p <;> rw [hp] at h <;> try contradiction
    repeat' (split at h <;> try contradiction)
    cases h
    simp [KeyRegistry.set, KeyCmd.target] at hq ⊢; simp [hq]
  | freeze p =>
    simp only [keyApply] at h
    cases hp : reg p <;> rw [hp] at h <;> try contradiction
    cases h
    simp [KeyRegistry.set, KeyCmd.target] at hq ⊢; simp [hq]
  | revoke p =>
    simp only [keyApply] at h
    cases hp : reg p <;> rw [hp] at h <;> try contradiction
    repeat' (split at h <;> try contradiction)
    cases h
    simp [KeyRegistry.set, KeyCmd.target] at hq ⊢; simp [hq]
  | recover p new =>
    simp only [keyApply] at h
    cases hp : reg p <;> rw [hp] at h <;> try contradiction
    repeat' (split at h <;> try contradiction)
    cases h
    simp [KeyRegistry.set, KeyCmd.target] at hq ⊢; simp [hq]


/-- Registry invariant: an account bound to a post-quantum key holds a post-quantum key. -/
def PqSound (isPQ : SuiteId → Bool) (reg : KeyRegistry Principal PublicKey) : Prop :=
  ∀ p a, reg p = some a → a.pqBound = true → isPQ a.key.suite = true

/-- The legacy-key rule: no successful transition breaks `PqSound`. In particular no
command replaces a post-quantum key of a bound account by a non-post-quantum key. -/
theorem keyApply_preserves_pqSound (isPQ : SuiteId → Bool)
    (reg : KeyRegistry Principal PublicKey) (actor : Actor) (c : KeyCmd Principal PublicKey)
    (reg' : KeyRegistry Principal PublicKey) (hinv : PqSound isPQ reg)
    (h : keyApply isPQ reg actor c = .ok reg') : PqSound isPQ reg' := by
  intro q a hq hb
  by_cases hqt : q = c.target
  · subst hqt
    cases c with
    | register p key recovery =>
      simp only [keyApply] at h
      cases hp : reg p <;> rw [hp] at h <;> try contradiction
      cases h
      simp [KeyRegistry.set, KeyCmd.target] at hq
      subst hq
      simpa using hb
    | rotate p new =>
      simp only [keyApply] at h
      rcases hp : reg p with _ | a0
      · rw [hp] at h; contradiction
      rw [hp] at h
      dsimp only at h
      repeat' (split at h <;> try contradiction)
      rename_i hnot
      cases h
      simp [KeyRegistry.set, KeyCmd.target] at hq
      subst hq
      simp at hb ⊢
      rcases hb with hb | hb
      · have := hinv _ a0 hp hb
        by_cases hn : isPQ new.suite = true
        · exact hn
        · exact absurd ⟨hb, by simpa using hn⟩ hnot
      · exact hb
    | freeze p =>
      simp only [keyApply] at h
      rcases hp : reg p with _ | a0
      · rw [hp] at h; contradiction
      rw [hp] at h
      dsimp only at h
      cases h
      simp [KeyRegistry.set, KeyCmd.target] at hq
      subst hq
      exact hinv _ a0 hp (by simpa using hb)
    | revoke p =>
      simp only [keyApply] at h
      rcases hp : reg p with _ | a0
      · rw [hp] at h; contradiction
      rw [hp] at h
      dsimp only at h
      repeat' (split at h <;> try contradiction)
      cases h
      simp [KeyRegistry.set, KeyCmd.target] at hq
      subst hq
      exact hinv _ a0 hp (by simpa using hb)
    | recover p new =>
      simp only [keyApply] at h
      rcases hp : reg p with _ | a0
      · rw [hp] at h; contradiction
      rw [hp] at h
      dsimp only at h
      repeat' (split at h <;> try contradiction)
      rename_i hnot
      cases h
      simp [KeyRegistry.set, KeyCmd.target] at hq
      subst hq
      simp at hb ⊢
      rcases hb with hb | hb
      · have := hinv _ a0 hp hb
        by_cases hn : isPQ new.suite = true
        · exact hn
        · exact absurd ⟨hb, by simpa using hn⟩ hnot
      · exact hb
  · rw [keyApply_other_unchanged isPQ reg actor c reg' h q hqt] at hq
    exact hinv q a hq hb


/-- A frozen account cannot rotate its key: rotation is refused until a recovery. -/
theorem rotate_frozen_rejected (isPQ : SuiteId → Bool) (reg : KeyRegistry Principal PublicKey)
    (p : Principal) (new : KeyRecord PublicKey) (a : Account PublicKey)
    (hp : reg p = some a) (hf : a.frozen = true) :
    ∃ e, keyApply isPQ reg .currentKey (.rotate p new) = .error e := by
  simp only [keyApply, hp]
  by_cases hr : a.revoked = true
  · exact ⟨.revoked, by simp [hr]⟩
  · exact ⟨.frozen, by simp [hr, hf]⟩

/-- Recovery needs the recovery actor: the current key alone cannot recover. -/
theorem recover_needs_recovery_actor (isPQ : SuiteId → Bool)
    (reg : KeyRegistry Principal PublicKey) (p : Principal) (new : KeyRecord PublicKey)
    (a : Account PublicKey) (hp : reg p = some a) :
    keyApply isPQ reg .currentKey (.recover p new) = .error .notAuthorized := by
  simp [keyApply, hp]

/-- Revocation needs the recovery actor too. -/
theorem revoke_needs_recovery_actor (isPQ : SuiteId → Bool)
    (reg : KeyRegistry Principal PublicKey) (p : Principal)
    (a : Account PublicKey) (hp : reg p = some a) :
    keyApply isPQ reg .currentKey (.revoke p) = .error .notAuthorized := by
  simp [keyApply, hp]

/-- Without a registered recovery credential, recovery is impossible even for the
recovery actor. -/
theorem recover_without_credential_rejected (isPQ : SuiteId → Bool)
    (reg : KeyRegistry Principal PublicKey) (p : Principal) (new : KeyRecord PublicKey)
    (a : Account PublicKey) (hp : reg p = some a) (hn : a.recovery = none) :
    keyApply isPQ reg .recoveryKey (.recover p new) = .error .noRecovery := by
  simp [keyApply, hp, hn]

/-- The registry as seen by the signature check: frozen and revoked accounts have no key. -/
def KeyRegistry.view (reg : KeyRegistry Principal PublicKey) :
    Principal → Option (KeyRecord PublicKey) := fun p =>
  match reg p with
  | none => none
  | some a => if a.frozen = true ∨ a.revoked = true then none else some a.key

omit [DecidableEq Principal] in
/-- A frozen or revoked account cannot be authorized by the signature check. -/
theorem frozen_or_revoked_not_authorized {Message Signature : Type}
    (M : SignatureModel PublicKey Message Signature) (P : SuitePolicy)
    (reg : KeyRegistry Principal PublicKey) (p : Principal) (claimed : SuiteId)
    (msg : Message) (sig : Signature) (a : Account PublicKey) (hp : reg p = some a)
    (h : a.frozen = true ∨ a.revoked = true) :
    authorize M P reg.view p claimed msg sig = .unknownPrincipal := by
  have : reg.view p = none := by simp [KeyRegistry.view, hp, h]
  simp [authorize, this]

/-- Sketch of a whole system: a financial state of any type next to the key registry. -/
structure KeySystem (Fin Principal PublicKey : Type) where
  fin : Fin
  keys : KeyRegistry Principal PublicKey

/-- One key transition on the whole system; a rejected command changes nothing. -/
def KeySystem.step {Fin : Type} (isPQ : SuiteId → Bool)
    (s : KeySystem Fin Principal PublicKey) (actor : Actor) (c : KeyCmd Principal PublicKey) :
    KeySystem Fin Principal PublicKey :=
  match keyApply isPQ s.keys actor c with
  | .ok keys' => { s with keys := keys' }
  | .error _ => s

/-- Frame property: key transitions never change the financial state. -/
theorem KeySystem.step_fin {Fin : Type} (isPQ : SuiteId → Bool)
    (s : KeySystem Fin Principal PublicKey) (actor : Actor) (c : KeyCmd Principal PublicKey) :
    (s.step isPQ actor c).fin = s.fin := by
  unfold KeySystem.step
  cases keyApply isPQ s.keys actor c <;> rfl

/-- Hence every invariant of the financial state (supply conservation, nonces, ...) is
preserved by key transitions. -/
theorem KeySystem.step_preserves {Fin : Type} (Inv : Fin → Prop) (isPQ : SuiteId → Bool)
    (s : KeySystem Fin Principal PublicKey) (actor : Actor) (c : KeyCmd Principal PublicKey)
    (h : Inv s.fin) : Inv (s.step isPQ actor c).fin := by
  rw [KeySystem.step_fin]; exact h

/-- A rejected command changes nothing. -/
theorem KeySystem.step_rejected {Fin : Type} (isPQ : SuiteId → Bool)
    (s : KeySystem Fin Principal PublicKey) (actor : Actor) (c : KeyCmd Principal PublicKey)
    (e : KeyError) (h : keyApply isPQ s.keys actor c = .error e) : s.step isPQ actor c = s := by
  simp [KeySystem.step, h]

end Transitions

/-! ### Concrete regression examples -/

section Demo

/-- Suites 2 and 0x0101 are post-quantum-bearing, suite 1 (Ed25519) is classical. -/
def demoIsPQ : SuiteId → Bool := fun s => s = 2 || s = 0x0101

def demoReg0 : KeyRegistry Nat Nat :=
  fun p => if p = 0 then some { key := { suite := 2, key := 7 }, recovery := some { suite := 3, key := 9 },
                                frozen := false, revoked := false, pqBound := true } else none

/-- A bound account cannot be downgraded to Ed25519 by rotation. -/
example : keyApply demoIsPQ demoReg0 .currentKey (.rotate 0 { suite := 1, key := 5 }) =
    .error .pqDowngrade := by rfl

/-- Nor by recovery. -/
example : keyApply demoIsPQ demoReg0 .recoveryKey (.recover 0 { suite := 1, key := 5 }) =
    .error .pqDowngrade := by rfl

/-- Rotation to another post-quantum key succeeds. -/
example : (keyApply demoIsPQ demoReg0 .currentKey (.rotate 0 { suite := 2, key := 8 })).isOk = true := by
  decide

/-- Unknown principals cannot be rotated. -/
example : keyApply demoIsPQ demoReg0 .currentKey (.rotate 4 { suite := 2, key := 8 }) =
    .error .unknownAccount := by rfl

end Demo

end SIRM
