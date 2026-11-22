/-!
# Integrated Request Pipeline (checked by SIRM)

A generic model of the request pipeline of the integrated state machine
(`docs/INTEGRATED_STATE_MACHINE_PROPOSAL.md`, rust `integrated::Machine`, Python `IM.process`):

1. request-id lookup: a cached identical request is answered from the cache (replay), a cached
   different request under the same id is a conflict; neither changes the state;
2. nonce check: stale and future nonces are rejected and are not cached;
3. authorization (deny by default): a denial is cached, consumes no nonce, changes nothing else;
4. domain validation: a denial is cached, consumes no nonce, changes nothing else;
5. apply: the core state changes, the principal's nonce becomes `n + 1`, the receipt is cached.

The model is generic on purpose. It does not mention balances, escrow or migration: `Core` is any
state, `authorized`, `validate` and `apply` are arbitrary functions. Everything proved here
therefore holds for the ledger, escrow and migration operations alike, and any invariant on
`Core` that every accepted `apply` preserves is an invariant of the whole machine
(`process_preserves`). It does not prove that the Rust or Python machines implement this model
(that evidence is differential testing), and it does not prove any ledger invariant: those need
the concrete `apply` and stay open. No Mathlib is used.
-/

namespace SIRM
namespace IntegratedPipeline

/-- What a request left in the response cache. -/
inductive Stored (Denial : Type) where
  | accepted (nonce : Nat)
  | denied (denial : Denial) (expectedNonce : Nat)
  deriving DecidableEq

/-- The answer to one request. `fresh` means the request was processed now and cached. -/
inductive Outcome (Denial : Type) where
  | replay (stored : Stored Denial)
  | conflict
  | stale
  | future
  | fresh (stored : Stored Denial)

/-- The rules of a machine: who sends, the nonce, authorization, validation and effect. -/
structure Rules (Principal Req Core Denial : Type) where
  principal : Req → Principal
  nonce : Req → Nat
  authorized : Core → Req → Bool
  authDenial : Req → Denial
  validate : Core → Req → Option Denial
  apply : Core → Req → Core

structure State (Id Principal Req Core Denial : Type) where
  core : Core
  nonces : Principal → Nat
  cache : Id → Option (Req × Stored Denial)

variable {Id Principal Req Core Denial : Type}
  [DecidableEq Id] [DecidableEq Principal] [DecidableEq Req]

def record (cache : Id → Option (Req × Stored Denial)) (id : Id) (r : Req)
    (st : Stored Denial) : Id → Option (Req × Stored Denial) :=
  fun i => if i = id then some (r, st) else cache i

def bump (nonces : Principal → Nat) (p : Principal) (n : Nat) : Principal → Nat :=
  fun q => if q = p then n + 1 else nonces q

/-- The pipeline. -/
def process (R : Rules Principal Req Core Denial)
    (s : State Id Principal Req Core Denial) (id : Id) (r : Req) :
    State Id Principal Req Core Denial × Outcome Denial :=
  match s.cache id with
  | some (prior, stored) =>
      if prior = r then (s, .replay stored) else (s, .conflict)
  | none =>
      let n := s.nonces (R.principal r)
      if R.nonce r < n then (s, .stale)
      else if n < R.nonce r then (s, .future)
      else
        let verdict : Option Denial :=
          if R.authorized s.core r then R.validate s.core r else some (R.authDenial r)
        match verdict with
        | some d =>
            let st := Stored.denied d n
            ({ s with cache := record s.cache id r st }, .fresh st)
        | none =>
            let st := Stored.accepted (R.nonce r)
            ({ core := R.apply s.core r
               nonces := bump s.nonces (R.principal r) n
               cache := record s.cache id r st }, .fresh st)

variable (R : Rules Principal Req Core Denial)
  (s : State Id Principal Req Core Denial) (id : Id) (r : Req)

/-- A cached identical request is answered from the cache and changes nothing. -/
theorem replay_unchanged {prior : Req} {st : Stored Denial}
    (h : s.cache id = some (prior, st)) (hp : prior = r) :
    process R s id r = (s, .replay st) := by
  simp [process, h, hp]

/-- A cached different request under the same id is a conflict and changes nothing. -/
theorem conflict_unchanged {prior : Req} {st : Stored Denial}
    (h : s.cache id = some (prior, st)) (hp : prior ≠ r) :
    process R s id r = (s, .conflict) := by
  simp [process, h, hp]

/-- A stale nonce is rejected, changes nothing and is not cached. -/
theorem stale_unchanged (h : s.cache id = none)
    (hn : R.nonce r < s.nonces (R.principal r)) :
    process R s id r = (s, .stale) := by
  simp [process, h, hn]

/-- A future nonce is rejected, changes nothing and is not cached. -/
theorem future_unchanged (h : s.cache id = none)
    (hn : s.nonces (R.principal r) < R.nonce r) :
    process R s id r = (s, .future) := by
  have hs : ¬ R.nonce r < s.nonces (R.principal r) := Nat.not_lt.mpr (Nat.le_of_lt hn)
  simp [process, h, hs, hn]

/-- An unauthorized request is denied with the authorization denial, whatever validation would
say; the core state and all nonces are unchanged and the denial is cached. -/
theorem unauthorized_denied (h : s.cache id = none)
    (hn : R.nonce r = s.nonces (R.principal r))
    (ha : R.authorized s.core r = false) :
    process R s id r =
      ({ s with cache := (record s.cache id r
          (Stored.denied (R.authDenial r) (s.nonces (R.principal r)))) },
       .fresh (Stored.denied (R.authDenial r) (s.nonces (R.principal r)))) := by
  have h1 : ¬ R.nonce r < s.nonces (R.principal r) := by omega
  have h2 : ¬ s.nonces (R.principal r) < R.nonce r := by omega
  simp [process, h, h1, h2, ha]

/-- An authorized request that fails validation is denied: core and nonces unchanged. -/
theorem invalid_denied (h : s.cache id = none)
    (hn : R.nonce r = s.nonces (R.principal r))
    (ha : R.authorized s.core r = true) {d : Denial}
    (hv : R.validate s.core r = some d) :
    process R s id r =
      ({ s with cache := record s.cache id r (Stored.denied d (s.nonces (R.principal r))) },
       .fresh (Stored.denied d (s.nonces (R.principal r)))) := by
  have h1 : ¬ R.nonce r < s.nonces (R.principal r) := by omega
  have h2 : ¬ s.nonces (R.principal r) < R.nonce r := by omega
  simp [process, h, h1, h2, ha, hv]

/-- An authorized, valid request with the expected nonce is applied, the principal's nonce
advances by exactly one, and the receipt is cached. -/
theorem accepted_applied (h : s.cache id = none)
    (hn : R.nonce r = s.nonces (R.principal r))
    (ha : R.authorized s.core r = true) (hv : R.validate s.core r = none) :
    process R s id r =
      ({ core := R.apply s.core r
         nonces := bump s.nonces (R.principal r) (s.nonces (R.principal r))
         cache := record s.cache id r (Stored.accepted (R.nonce r)) },
       .fresh (Stored.accepted (R.nonce r))) := by
  have h1 : ¬ R.nonce r < s.nonces (R.principal r) := by omega
  have h2 : ¬ s.nonces (R.principal r) < R.nonce r := by omega
  simp [process, h, h1, h2, ha, hv]

/-- A request that is not freshly processed leaves the whole state unchanged. -/
theorem not_fresh_state_unchanged
    (hf : ∀ st, (process R s id r).2 ≠ Outcome.fresh st) :
    (process R s id r).1 = s := by
  rcases hc : s.cache id with _ | ⟨prior, st⟩
  · by_cases h1 : R.nonce r < s.nonces (R.principal r)
    · rw [stale_unchanged R s id r hc h1]
    · by_cases h2 : s.nonces (R.principal r) < R.nonce r
      · rw [future_unchanged R s id r hc h2]
      · have hn : R.nonce r = s.nonces (R.principal r) := by omega
        exfalso
        by_cases ha : R.authorized s.core r = true
        · rcases hv : R.validate s.core r with _ | d
          · exact hf _ (by rw [accepted_applied R s id r hc hn ha hv])
          · exact hf _ (by rw [invalid_denied R s id r hc hn ha hv])
        · have ha' : R.authorized s.core r = false := by simpa using ha
          exact hf _ (by rw [unauthorized_denied R s id r hc hn ha'])
  · by_cases hp : prior = r
    · rw [replay_unchanged R s id r hc hp]
    · rw [conflict_unchanged R s id r hc hp]

/-- The three shapes of the new state: unchanged, a cached denial, or an applied request. -/
theorem process_cases :
    (process R s id r).1 = s ∨
    (s.cache id = none ∧ ∃ d : Denial, (process R s id r).1 =
      { s with cache := record s.cache id r (Stored.denied d (s.nonces (R.principal r))) }) ∨
    (s.cache id = none ∧ R.authorized s.core r = true ∧ R.validate s.core r = none ∧
      (process R s id r).1 =
        { core := R.apply s.core r
          nonces := bump s.nonces (R.principal r) (s.nonces (R.principal r))
          cache := record s.cache id r (Stored.accepted (R.nonce r)) } ∧
      (process R s id r).2 = .fresh (Stored.accepted (R.nonce r))) := by
  rcases hc : s.cache id with _ | ⟨prior, st⟩
  · by_cases h1 : R.nonce r < s.nonces (R.principal r)
    · left; rw [stale_unchanged R s id r hc h1]
    · by_cases h2 : s.nonces (R.principal r) < R.nonce r
      · left; rw [future_unchanged R s id r hc h2]
      · have hn : R.nonce r = s.nonces (R.principal r) := by omega
        right
        by_cases ha : R.authorized s.core r = true
        · rcases hv : R.validate s.core r with _ | d
          · right
            exact ⟨rfl, ha, rfl, by rw [accepted_applied R s id r hc hn ha hv],
              by rw [accepted_applied R s id r hc hn ha hv]⟩
          · left
            exact ⟨rfl, d, by rw [invalid_denied R s id r hc hn ha hv]⟩
        · have ha' : R.authorized s.core r = false := by simpa using ha
          left
          exact ⟨rfl, R.authDenial r, by rw [unauthorized_denied R s id r hc hn ha']⟩
  · left
    by_cases hp : prior = r
    · rw [replay_unchanged R s id r hc hp]
    · rw [conflict_unchanged R s id r hc hp]

/-- Receipts are never overwritten or removed: whatever the cache held for any id is still there. -/
theorem cache_stable {i : Id} {e : Req × Stored Denial} (h : s.cache i = some e) :
    (process R s id r).1.cache i = some e := by
  rcases process_cases R s id r with hc | ⟨hn, d, hc⟩ | ⟨hn, _, _, hc, _⟩
  · rw [hc]; exact h
  · rw [hc]
    have : i ≠ id := fun hi => by rw [hi, hn] at h; cases h
    simp [record, this, h]
  · rw [hc]
    have : i ≠ id := fun hi => by rw [hi, hn] at h; cases h
    simp [record, this, h]

/-- Nonces never decrease. -/
theorem nonce_monotone (q : Principal) :
    s.nonces q ≤ (process R s id r).1.nonces q := by
  rcases process_cases R s id r with hc | ⟨_, d, hc⟩ | ⟨_, _, _, hc, _⟩
  · rw [hc]; exact Nat.le_refl _
  · rw [hc]; exact Nat.le_refl _
  · rw [hc]
    by_cases hq : q = R.principal r
    · subst hq; simp [bump]
    · simp [bump, hq]

/-- Only the sender's nonce can change. -/
theorem other_nonce_unchanged {q : Principal} (hq : q ≠ R.principal r) :
    (process R s id r).1.nonces q = s.nonces q := by
  rcases process_cases R s id r with hc | ⟨_, d, hc⟩ | ⟨_, _, _, hc, _⟩
  · rw [hc]
  · rw [hc]
  · rw [hc]; simp [bump, hq]

/-- A nonce ceiling `N`. The wire format fixes nonces to 8 bytes, so `N = 2^64 - 1`. A counter that has
reached `N` cannot advance (its successor would not fit); a request carrying exactly that nonce is
answered as `stale`, like a nonce that can no longer be used, and is not cached. Every other request
goes through `process` unchanged. -/
def processCapped (N : Nat) : State Id Principal Req Core Denial × Outcome Denial :=
  if s.cache id = none ∧ s.nonces (R.principal r) = N ∧ R.nonce r = N then (s, .stale)
  else process R s id r

/-- Away from the ceiling the capped pipeline is the pipeline. -/
theorem processCapped_eq (N : Nat)
    (h : ¬ (s.cache id = none ∧ s.nonces (R.principal r) = N ∧ R.nonce r = N)) :
    processCapped R s id r N = process R s id r := by
  unfold processCapped
  rw [if_neg h]

/-- Under the ceiling no nonce ever exceeds `N`: the counter of the sender is bumped only from a value
below `N`. With `N = 2^64 - 1` every stored nonce fits the eight bytes of the wire format, so the
bounds of `RequestEncodingV2` and `LedgerRootsV0` hold along every run. -/
theorem processCapped_nonces_le (N : Nat) (hN : ∀ q, s.nonces q ≤ N) :
    ∀ q, (processCapped R s id r N).1.nonces q ≤ N := by
  intro q
  unfold processCapped
  by_cases hc : s.cache id = none ∧ s.nonces (R.principal r) = N ∧ R.nonce r = N
  · rw [if_pos hc]; exact hN q
  · rw [if_neg hc]
    rcases process_cases R s id r with h | ⟨_, d, h⟩ | ⟨hcache, _, _, h, h2⟩
    · rw [h]; exact hN q
    · rw [h]; exact hN q
    · have hn : R.nonce r = s.nonces (R.principal r) := by
        rcases Nat.lt_trichotomy (R.nonce r) (s.nonces (R.principal r)) with hl | he | hl
        · rw [stale_unchanged R s id r hcache hl] at h2; cases h2
        · exact he
        · rw [future_unchanged R s id r hcache hl] at h2; cases h2
      have hlt : s.nonces (R.principal r) < N := by
        have hle := hN (R.principal r)
        rcases Nat.lt_or_ge (s.nonces (R.principal r)) N with h3 | h3
        · exact h3
        · exact absurd ⟨hcache, Nat.le_antisymm hle h3, by rw [hn]; exact Nat.le_antisymm hle h3⟩ hc
      rw [h]
      by_cases hq : q = R.principal r
      · subst hq; simp only [bump, if_true]; omega
      · simp only [bump, hq, if_false]; exact hN q

/-- An invariant of the core state that every accepted `apply` preserves is an invariant of the
whole pipeline: denials, replays, conflicts and rejected nonces do not touch the core. -/
theorem process_preserves (Inv : Core → Prop)
    (hApply : ∀ c q, R.authorized c q = true → R.validate c q = none →
      Inv c → Inv (R.apply c q))
    (h : Inv s.core) : Inv (process R s id r).1.core := by
  rcases process_cases R s id r with hc | ⟨_, d, hc⟩ | ⟨_, ha, hv, hc, _⟩
  · rw [hc]; exact h
  · rw [hc]; exact h
  · rw [hc]; exact hApply _ _ ha hv h

/-- A denial changes neither the core state nor any nonce (so it consumes no nonce). -/
theorem denial_keeps_core_and_nonces {d : Denial} {s' : State Id Principal Req Core Denial}
    (h : process R s id r = (s', .fresh (Stored.denied d (s.nonces (R.principal r))))) :
    s'.core = s.core ∧ s'.nonces = s.nonces := by
  rcases process_cases R s id r with hc | ⟨_, d', hc⟩ | ⟨_, _, _, hc, hout⟩
  · have := congrArg Prod.fst h; rw [hc] at this; subst this; exact ⟨rfl, rfl⟩
  · have := congrArg Prod.fst h; rw [hc] at this; subst this; exact ⟨rfl, rfl⟩
  · exfalso
    have h2 := congrArg Prod.snd h
    rw [hout] at h2
    cases h2

/-- Replaying a freshly processed request returns the same receipt and changes nothing. -/
theorem replay_after_fresh {s' : State Id Principal Req Core Denial} {st : Stored Denial}
    (h : process R s id r = (s', .fresh st)) :
    process R s' id r = (s', .replay st) := by
  rcases hc : s.cache id with _ | ⟨prior, st0⟩
  · by_cases h1 : R.nonce r < s.nonces (R.principal r)
    · rw [stale_unchanged R s id r hc h1] at h; simp at h
    · by_cases h2 : s.nonces (R.principal r) < R.nonce r
      · rw [future_unchanged R s id r hc h2] at h; simp at h
      · have hn : R.nonce r = s.nonces (R.principal r) := by omega
        by_cases ha : R.authorized s.core r = true
        · rcases hv : R.validate s.core r with _ | d
          · rw [accepted_applied R s id r hc hn ha hv] at h
            simp at h
            obtain ⟨hs, hst⟩ := h
            subst hs hst
            exact replay_unchanged R _ id r (by simp [record]) rfl
          · rw [invalid_denied R s id r hc hn ha hv] at h
            simp at h
            obtain ⟨hs, hst⟩ := h
            subst hs hst
            exact replay_unchanged R _ id r (by simp [record]) rfl
        · have ha' : R.authorized s.core r = false := by simpa using ha
          rw [unauthorized_denied R s id r hc hn ha'] at h
          simp at h
          obtain ⟨hs, hst⟩ := h
          subst hs hst
          exact replay_unchanged R _ id r (by simp [record]) rfl
  · by_cases hp : prior = r
    · rw [replay_unchanged R s id r hc hp] at h; simp at h
    · rw [conflict_unchanged R s id r hc hp] at h; simp at h

/-- After a request was accepted, the same request under a different id is stale: its nonce is
spent, so an accepted request cannot be applied a second time by renaming it. -/
theorem accepted_then_other_id_stale {s' : State Id Principal Req Core Denial} {id2 : Id}
    (h : process R s id r = (s', .fresh (Stored.accepted (R.nonce r))))
    (h2 : s'.cache id2 = none) :
    process R s' id2 r = (s', .stale) := by
  have hn : R.nonce r < s'.nonces (R.principal r) := by
    rcases hc : s.cache id with _ | ⟨prior, st0⟩
    · by_cases h1 : R.nonce r < s.nonces (R.principal r)
      · rw [stale_unchanged R s id r hc h1] at h; simp at h
      · by_cases h3 : s.nonces (R.principal r) < R.nonce r
        · rw [future_unchanged R s id r hc h3] at h; simp at h
        · have hn : R.nonce r = s.nonces (R.principal r) := by omega
          by_cases ha : R.authorized s.core r = true
          · rcases hv : R.validate s.core r with _ | d
            · rw [accepted_applied R s id r hc hn ha hv] at h
              simp at h
              subst h
              simp [bump]
              omega
            · rw [invalid_denied R s id r hc hn ha hv] at h; simp at h
          · have ha' : R.authorized s.core r = false := by simpa using ha
            rw [unauthorized_denied R s id r hc hn ha'] at h; simp at h
    · by_cases hp : prior = r
      · rw [replay_unchanged R s id r hc hp] at h; simp at h
      · rw [conflict_unchanged R s id r hc hp] at h; simp at h
  exact stale_unchanged R s' id2 r h2 hn

/-! ### Concrete scenarios (a counter machine; principals below 2 are authorized) -/

section Demo

def demoRules : Rules Nat (Nat × Nat) Nat Nat where
  principal := fun r => r.1
  nonce := fun r => r.2
  authorized := fun _ r => r.1 < 2
  authDenial := fun _ => 1
  validate := fun c _ => if c < 2 then none else some 2
  apply := fun c _ => c + 1

def demo0 : State Nat Nat (Nat × Nat) Nat Nat :=
  { core := 0, nonces := fun _ => 0, cache := fun _ => none }

example : (process demoRules demo0 7 (0, 0)).2 = .fresh (.accepted 0) := by
  simp [process, demoRules, demo0]

example : (process demoRules demo0 7 (3, 0)).2 = .fresh (.denied 1 0) := by
  simp [process, demoRules, demo0]

example : (process demoRules demo0 7 (0, 1)).2 = .future := by
  simp [process, demoRules, demo0]

example : (process demoRules (process demoRules demo0 7 (0, 0)).1 7 (0, 0)).2 =
    .replay (.accepted 0) := by
  simp [process, demoRules, demo0, record]

example : (process demoRules (process demoRules demo0 7 (0, 0)).1 8 (0, 0)).2 = .stale := by
  simp [process, demoRules, demo0, record, bump]

example : (process demoRules (process demoRules demo0 7 (0, 0)).1 7 (0, 1)).2 = .conflict := by
  simp [process, demoRules, demo0, record]

end Demo

end IntegratedPipeline
end SIRM
