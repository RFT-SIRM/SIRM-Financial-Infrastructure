import SIRM.IntegratedLedger

/-!
# Bounded Amounts for the Integrated Ledger (checked by SIRM)

`SIRM.IntegratedLedger` models amounts as natural numbers. The Rust and Python machines use a fixed
width (`u128`) and deny a request whose arithmetic would exceed it. This file adds that ceiling to the
Lean model as a parameter `lim` (for `u128`, `lim = 2^128 - 1`, see `u128Max`).

The ceiling is added as one more validation step, `boundVal`: a request whose effect would push a
supply counter, a migration total or the migration amount past `lim` is denied with the code
`overflowDenial` and changes nothing. Proved, for any authorization function and any validation that
implies the ledger preconditions:

* the wrapped validation still implies the ledger preconditions, so every earlier theorem applies;
* in every reachable state the ledger invariants hold and every supply counter (`minted`), the migration
  totals (`tsrc`, `ttgt`) and the carried remainder (`dust`) are at most `lim`;
* in every reachable state, every burned total and every account balance is at most `lim` as well. This
  is a consequence of conservation (`minted = burned + sum of balances`), so no separate balance check
  is needed for the bound itself;
* a request that does not fit leaves the core state unchanged.

Not covered, stated so that no reader assumes it: the clock, escrow ids and other indices are still
unbounded naturals; the order in which denial reasons are reported is not modelled; nothing here proves
that the Rust or Python code checks exactly the conditions in `fitsB` (that is differential evidence,
not a refinement proof). No Mathlib is used.
-/

namespace SIRM
namespace BoundedAmounts

open IntegratedPipeline IntegratedLedger

/-- The ceiling of `u128`. -/
def u128Max : Nat := 2 ^ 128 - 1

/-- The checked-arithmetic conditions of a request against the ceiling `lim`. Only operations that
increase a supply counter or a migration total have a condition; the others move existing amounts. -/
def fitsB (cfg : Cfg) (lim : Nat) (c : Core) : Op → Bool
  | .issue _ _ s amt => decide (c.minted s + amt ≤ lim)
  | .migrate amt =>
      match cfg.mig with
      | some m =>
          decide (amt * m.num + c.dust ≤ lim) && decide (c.tsrc + amt ≤ lim) &&
          decide (c.ttgt + (amt * m.num + c.dust) / m.den ≤ lim) &&
          decide (c.minted m.dst + (amt * m.num + c.dust) / m.den ≤ lim)
      | none => true
  | _ => true

/-- The denial code of a request that does not fit. -/
def overflowDenial : Nat := 1000

/-- The validation with the ceiling added in front of any other validation. -/
def boundVal (cfg : Cfg) (lim : Nat) (validate : Core → Req → Option Nat) : Core → Req → Option Nat :=
  fun c r => if fitsB cfg lim c r.op = true then validate c r else some overflowDenial

theorem boundVal_pre (cfg : Cfg) (lim : Nat) (validate : Core → Req → Option Nat)
    (hval : ∀ c r, validate c r = none → pre cfg c r.op) :
    ∀ c r, boundVal cfg lim validate c r = none → pre cfg c r.op := by
  intro c r h
  unfold boundVal at h
  split at h
  · exact hval c r h
  · simp at h

theorem boundVal_fits (cfg : Cfg) (lim : Nat) (validate : Core → Req → Option Nat) (c : Core)
    (r : Req) (h : boundVal cfg lim validate c r = none) : fitsB cfg lim c r.op = true := by
  unfold boundVal at h
  split at h
  · assumption
  · simp at h

/-- The counters that the ceiling bounds directly. -/
structure Bounded (lim : Nat) (c : Core) : Prop where
  minted : ∀ s, c.minted s ≤ lim
  tsrc : c.tsrc ≤ lim
  ttgt : c.ttgt ≤ lim
  dust : c.dust ≤ lim

theorem bounded_empty (lim : Nat) : Bounded lim Core.empty :=
  ⟨fun _ => Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

theorem bounded_settle (cfg : Cfg) (lim : Nat) {c : Core} (b : Bounded lim c) (id : Nat)
    (toBen : Bool) (ph : Phase) : Bounded lim (settle cfg c id toBen ph) := by
  unfold settle
  split
  · exact ⟨b.minted, b.tsrc, b.ttgt, b.dust⟩
  · exact b

theorem bounded_issue (lim : Nat) {c : Core} (b : Bounded lim c) (r s amt : Nat)
    (h : c.minted s + amt ≤ lim) : Bounded lim (issueEff c r s amt) := by
  refine ⟨?_, b.tsrc, b.ttgt, b.dust⟩
  intro t
  show (if t = s then c.minted t + amt else c.minted t) ≤ lim
  by_cases hts : t = s
  · subst hts; simpa using h
  · simpa [hts] using b.minted t

theorem bounded_applyOp (cfg : Cfg) (lim : Nat) {c : Core} (b : Bounded lim c) (op : Op)
    (h : fitsB cfg lim c op = true) : Bounded lim (applyOp cfg c op) := by
  cases op with
  | transfer src dst s amt =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro t
        rw [show (applyOp cfg c (.transfer src dst s amt)).minted t = c.minted t from
          congrFun (transfer_minted cfg c src dst s amt) t]
        exact b.minted t
      · rw [transfer_tsrc]; exact b.tsrc
      · rw [transfer_ttgt]; exact b.ttgt
      · rw [transfer_dust]; exact b.dust
  | issue iss r s amt =>
      exact bounded_issue lim b r s amt (by simpa [fitsB] using h)
  | burn x s amt => exact ⟨b.minted, b.tsrc, b.ttgt, b.dust⟩
  | «open» id dep ben s amt => exact ⟨b.minted, b.tsrc, b.ttgt, b.dust⟩
  | release id => exact bounded_settle cfg lim b id true Phase.released
  | cancel id => exact bounded_settle cfg lim b id false Phase.cancelled
  | expire id => exact bounded_settle cfg lim b id false Phase.expired
  | dispute id cl => exact ⟨b.minted, b.tsrc, b.ttgt, b.dust⟩
  | advance t => exact ⟨b.minted, b.tsrc, b.ttgt, b.dust⟩
  | resolve id toBen =>
      have hb : Bounded lim (clearFile c id) := ⟨b.minted, b.tsrc, b.ttgt, b.dust⟩
      exact bounded_settle cfg lim hb id toBen _
  | migrate amt =>
      unfold applyOp
      cases hm : cfg.mig with
      | none => exact b
      | some m =>
          simp only [hm, fitsB, Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
          have hb : Bounded lim (burnEff c m.holder m.src amt) :=
            ⟨b.minted, b.tsrc, b.ttgt, b.dust⟩
          have hi : Bounded lim (issueEff (burnEff c m.holder m.src amt) m.recipient m.dst
              ((amt * m.num + c.dust) / m.den)) :=
            bounded_issue lim hb m.recipient m.dst _ h4
          refine ⟨hi.minted, ?_, ?_, ?_⟩
          · exact h2
          · exact h3
          · exact Nat.le_trans (Nat.mod_le _ _) h1

/-! ### The pipeline with the ceiling -/

/-- Invariants and bounds together. -/
def Safe (cfg : Cfg) (lim : Nat) (c : Core) : Prop := Inv cfg c ∧ Bounded lim c

theorem bounded_pipeline_safe (cfg : Cfg) (lim : Nat) (hv : cfg.vault < cfg.accounts)
    (auth : Core → Req → Bool) (validate : Core → Req → Option Nat)
    (hval : ∀ c r, validate c r = none → pre cfg c r.op)
    (s : State Nat Nat Req Core Nat) (id : Nat) (r : Req) (h : Safe cfg lim s.core) :
    Safe cfg lim (process (rules cfg auth (boundVal cfg lim validate)) s id r).1.core :=
  process_preserves (rules cfg auth (boundVal cfg lim validate)) s id r (Safe cfg lim)
    (fun c q _ hq hs =>
      ⟨inv_applyOp hv hs.1 q.op (boundVal_pre cfg lim validate hval c q hq),
        bounded_applyOp cfg lim hs.2 q.op (boundVal_fits cfg lim validate c q hq)⟩) h

/-- A request that does not fit leaves the core state unchanged. -/
theorem unfit_keeps_core (cfg : Cfg) (lim : Nat) (auth : Core → Req → Bool)
    (validate : Core → Req → Option Nat) (s : State Nat Nat Req Core Nat) (id : Nat) (r : Req)
    (h : fitsB cfg lim s.core r.op = false) :
    (process (rules cfg auth (boundVal cfg lim validate)) s id r).1.core = s.core := by
  rcases process_cases (rules cfg auth (boundVal cfg lim validate)) s id r with hc | ⟨_, d, hc⟩ | ⟨_, _, hv, _, _⟩
  · rw [hc]
  · rw [hc]
  · have := boundVal_fits cfg lim validate s.core r hv
    rw [h] at this
    exact absurd this (by simp)

/-- The machine with the ceiling: initial states have the empty core. -/
def machineB (cfg : Cfg) (lim : Nat) (hv : cfg.vault < cfg.accounts)
    (auth : Core → Req → Bool) (validate : Core → Req → Option Nat)
    (hval : ∀ c r, validate c r = none → pre cfg c r.op) :
    VerifiedStateMachine (State Nat Nat Req Core Nat) where
  invariant := fun s => Safe cfg lim s.core
  initial := fun s => s.core = Core.empty
  step := fun s s' =>
    ∃ (id : Nat) (r : Req), s' = (process (rules cfg auth (boundVal cfg lim validate)) s id r).1
  initial_safe := by
    intro s h
    rw [h]
    exact ⟨inv_empty cfg, bounded_empty lim⟩
  step_safe := by
    intro s s' hs ⟨id, r, e⟩
    rw [e]
    exact bounded_pipeline_safe cfg lim hv auth validate hval s id r hs

theorem reachable_safe_bounded (cfg : Cfg) (lim : Nat) (hv : cfg.vault < cfg.accounts)
    (auth : Core → Req → Bool) (validate : Core → Req → Option Nat)
    (hval : ∀ c r, validate c r = none → pre cfg c r.op)
    {s : State Nat Nat Req Core Nat} (h : Reachable (machineB cfg lim hv auth validate hval) s) :
    Safe cfg lim s.core :=
  invariant_of_reachable (machineB cfg lim hv auth validate hval) h

/-! ### Balances and burned totals are bounded by conservation -/

theorem le_total (f : Nat → Nat) (a n : Nat) (h : a < n) : f a ≤ total f n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hlt : a < n
    · have := ih hlt
      simp only [total]
      omega
    · have han : a = n := by omega
      subst han
      simp only [total]
      omega

theorem safe_balance_le (cfg : Cfg) (lim : Nat) {c : Core} (h : Safe cfg lim c) (s a : Nat)
    (ha : a < cfg.accounts) : c.bal s a ≤ lim := by
  have h1 := h.1.conserve s
  have h2 := le_total (c.bal s) a cfg.accounts ha
  have h3 := h.2.minted s
  omega

theorem safe_burned_le (cfg : Cfg) (lim : Nat) {c : Core} (h : Safe cfg lim c) (s : Nat) :
    c.burned s ≤ lim := by
  have h1 := h.1.conserve s
  have h3 := h.2.minted s
  omega

/-- In every reachable state of the `u128` machine, every counter, every burned total and every
account balance fits in `u128`. -/
theorem reachable_u128 (cfg : Cfg) (hv : cfg.vault < cfg.accounts)
    (auth : Core → Req → Bool) (validate : Core → Req → Option Nat)
    (hval : ∀ c r, validate c r = none → pre cfg c r.op)
    {s : State Nat Nat Req Core Nat}
    (h : Reachable (machineB cfg u128Max hv auth validate hval) s) :
    (∀ t, s.core.minted t ≤ u128Max) ∧ (∀ t, s.core.burned t ≤ u128Max) ∧
    (∀ t a, a < cfg.accounts → s.core.bal t a ≤ u128Max) ∧ s.core.tsrc ≤ u128Max ∧
    s.core.ttgt ≤ u128Max ∧ s.core.dust ≤ u128Max := by
  have hs := reachable_safe_bounded cfg u128Max hv auth validate hval h
  exact ⟨hs.2.minted, safe_burned_le cfg u128Max hs, fun t a ha => safe_balance_le cfg u128Max hs t a ha,
    hs.2.tsrc, hs.2.ttgt, hs.2.dust⟩

end BoundedAmounts
end SIRM
