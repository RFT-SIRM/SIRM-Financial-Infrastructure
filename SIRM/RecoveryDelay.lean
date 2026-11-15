import SIRM.KeyRegistry

/-!
# Delayed, Cancellable Recovery (abstract model)

A recovery of one account's key is announced, waits a fixed delay, and only then takes effect.
During the wait the current key can cancel it. The actual key change is exactly the `recover`
transition of `SIRM.KeyRegistry`, so the legacy-key rule carries over.

Time is a natural number supplied by the caller; its monotonicity is an assumption of the
surrounding protocol, not proved here. The model describes the protocol rule, not who
supplies the clock.
-/

namespace SIRM

section Delay

variable {PublicKey : Type}

/-- A recovery that has been announced at time `start` for the new key `new`. -/
structure PendingRecovery (PublicKey : Type) where
  new : KeyRecord PublicKey
  start : Nat

/-- One account with at most one pending recovery. -/
structure DelayState (PublicKey : Type) where
  account : Account PublicKey
  pending : Option (PendingRecovery PublicKey)

inductive DelayCmd (PublicKey : Type) where
  | initiate (new : KeyRecord PublicKey)
  | cancel
  | finalize

inductive DelayError where
  | notAuthorized
  | noRecovery
  | alreadyPending
  | noPending
  | tooEarly
  | rejected (e : KeyError)

/-- Transition at time `now` with a recovery delay of `delay`. -/
def delayStep (isPQ : SuiteId → Bool) (delay now : Nat) (actor : Actor)
    (s : DelayState PublicKey) : DelayCmd PublicKey → Except DelayError (DelayState PublicKey)
  | .initiate new =>
    if actor ≠ .recoveryKey then .error .notAuthorized
    else if s.account.recovery = none then .error .noRecovery
    else if s.pending ≠ none then .error .alreadyPending
    else .ok { s with pending := some ⟨new, now⟩ }
  | .cancel =>
    if actor ≠ .currentKey then .error .notAuthorized
    else if s.pending = none then .error .noPending
    else .ok { s with pending := none }
  | .finalize =>
    match s.pending with
    | none => .error .noPending
    | some pr =>
      if actor ≠ .recoveryKey then .error .notAuthorized
      else if now < pr.start + delay then .error .tooEarly
      else
        match keyApply isPQ (fun _ : Unit => some s.account) .recoveryKey (.recover () pr.new) with
        | .error e => .error (.rejected e)
        | .ok reg' =>
          match reg' () with
          | none => .error (.rejected .unknownAccount)
          | some a => .ok { account := a, pending := none }

/-- Announcing and cancelling never change the account: the key stays as it was. -/
theorem initiate_keeps_account (isPQ : SuiteId → Bool) (delay now : Nat) (actor : Actor)
    (s s' : DelayState PublicKey) (new : KeyRecord PublicKey)
    (h : delayStep isPQ delay now actor s (.initiate new) = .ok s') :
    s'.account = s.account := by
  simp only [delayStep] at h
  repeat' (split at h <;> try contradiction)
  cases h; rfl

theorem cancel_keeps_account (isPQ : SuiteId → Bool) (delay now : Nat) (actor : Actor)
    (s s' : DelayState PublicKey)
    (h : delayStep isPQ delay now actor s .cancel = .ok s') : s'.account = s.account := by
  simp only [delayStep] at h
  repeat' (split at h <;> try contradiction)
  cases h; rfl

/-- Only the recovery actor can announce a recovery. -/
theorem initiate_needs_recovery_actor (isPQ : SuiteId → Bool) (delay now : Nat)
    (s : DelayState PublicKey) (new : KeyRecord PublicKey) :
    delayStep isPQ delay now .currentKey s (.initiate new) = .error .notAuthorized := by
  simp [delayStep]

/-- Only the current key can cancel: a thief with the recovery credential alone cannot. -/
theorem cancel_needs_current_key (isPQ : SuiteId → Bool) (delay now : Nat)
    (s : DelayState PublicKey) :
    delayStep isPQ delay now .recoveryKey s .cancel = .error .notAuthorized := by
  simp [delayStep]

/-- Cancelling clears the pending recovery. -/
theorem cancel_clears_pending (isPQ : SuiteId → Bool) (delay now : Nat)
    (s s' : DelayState PublicKey)
    (h : delayStep isPQ delay now .currentKey s .cancel = .ok s') : s'.pending = none := by
  simp only [delayStep] at h
  repeat' (split at h <;> try contradiction)
  cases h; rfl

/-- A second announcement cannot overwrite a pending one. -/
theorem initiate_twice_rejected (isPQ : SuiteId → Bool) (delay now : Nat)
    (s : DelayState PublicKey) (new : KeyRecord PublicKey) (pr : PendingRecovery PublicKey)
    (hp : s.pending = some pr) (hr : s.account.recovery ≠ none) :
    delayStep isPQ delay now .recoveryKey s (.initiate new) = .error .alreadyPending := by
  simp [delayStep, hp, hr]

/-- Nothing finalizes before the delay has elapsed. -/
theorem finalize_before_delay_rejected (isPQ : SuiteId → Bool) (delay now : Nat)
    (s : DelayState PublicKey) (pr : PendingRecovery PublicKey)
    (hp : s.pending = some pr) (ht : now < pr.start + delay) :
    delayStep isPQ delay now .recoveryKey s .finalize = .error .tooEarly := by
  simp [delayStep, hp, ht]

/-- Nothing finalizes without an announcement. -/
theorem finalize_without_pending_rejected (isPQ : SuiteId → Bool) (delay now : Nat)
    (actor : Actor) (s : DelayState PublicKey) (hp : s.pending = none) :
    delayStep isPQ delay now actor s .finalize = .error .noPending := by
  simp [delayStep, hp]

/-- A successful finalization consumed the pending recovery and the delay had elapsed. -/
theorem finalize_ok_after_delay (isPQ : SuiteId → Bool) (delay now : Nat) (actor : Actor)
    (s s' : DelayState PublicKey) (h : delayStep isPQ delay now actor s .finalize = .ok s') :
    s'.pending = none ∧ ∃ pr, s.pending = some pr ∧ pr.start + delay ≤ now ∧
      actor = .recoveryKey := by
  simp only [delayStep] at h
  cases hp : s.pending with
  | none => simp [hp] at h
  | some pr =>
    rw [hp] at h
    dsimp only at h
    repeat' (split at h <;> try contradiction)
    cases h
    refine ⟨rfl, pr, rfl, ?_, ?_⟩
    · omega
    · simpa using ‹¬actor ≠ Actor.recoveryKey›

/-- The legacy-key rule carries over: a finalized recovery never leaves a bound account with a
non-post-quantum key. -/
theorem finalize_preserves_pqSound (isPQ : SuiteId → Bool) (delay now : Nat) (actor : Actor)
    (s s' : DelayState PublicKey)
    (hs : s.account.pqBound = true → isPQ s.account.key.suite = true)
    (h : delayStep isPQ delay now actor s .finalize = .ok s') :
    s'.account.pqBound = true → isPQ s'.account.key.suite = true := by
  simp only [delayStep] at h
  cases hp : s.pending with
  | none => simp [hp] at h
  | some pr =>
    rw [hp] at h
    dsimp only at h
    repeat' (split at h <;> try contradiction)
    cases h
    rename_i _ reg' hk _ a hr
    have hinv : PqSound isPQ (fun _ : Unit => some s.account) := by
      intro p a' hq hb
      simp at hq
      subst hq
      exact hs hb
    exact keyApply_preserves_pqSound isPQ _ .recoveryKey _ reg' hinv hk () a hr

end Delay

/-! ### Concrete regression examples -/

section Demo

def demoIsPQD : SuiteId → Bool := fun s => s = 2

def demoAcct : Account Nat :=
  { key := { suite := 2, key := 7 }, recovery := some { suite := 3, key := 9 },
    frozen := false, revoked := false, pqBound := true }

def demoDelayState : DelayState Nat :=
  { account := demoAcct, pending := some ⟨{ suite := 2, key := 8 }, 100⟩ }

-- delay 50: at time 149 the recovery is still too early, at 150 it takes effect
example : (match delayStep demoIsPQD 50 149 .recoveryKey demoDelayState .finalize with
    | .error .tooEarly => true | _ => false) = true := by decide
example : (match delayStep demoIsPQD 50 150 .recoveryKey demoDelayState .finalize with
    | .ok s => s.account.key.key == 8 && s.pending.isNone | _ => false) = true := by decide
-- the current key cancels, the recovery credential alone cannot
example : (match delayStep demoIsPQD 50 120 .currentKey demoDelayState .cancel with
    | .ok s => s.pending.isNone && s.account.key.key == 7 | _ => false) = true := by decide
example : (match delayStep demoIsPQD 50 120 .recoveryKey demoDelayState .cancel with
    | .error .notAuthorized => true | _ => false) = true := by decide
-- a classical successor key is refused even after the delay
example : (match delayStep demoIsPQD 50 200 .recoveryKey
      { demoDelayState with pending := some ⟨{ suite := 1, key := 5 }, 100⟩ } .finalize with
    | .error (.rejected .pqDowngrade) => true | _ => false) = true := by decide

end Demo

end SIRM
