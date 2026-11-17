import SIRM.IntegratedPipeline
import SIRM.StateMachine

/-!
# Integrated Ledger Invariants (proposal, not adopted)

A concrete core state for the integrated state machine (`docs/INTEGRATED_STATE_MACHINE_PROPOSAL.md`)
with the ledger operations transfer, issue, burn and the escrow operations open, release, cancel and
expire over one shared ledger, instantiated into the generic pipeline of `SIRM.IntegratedPipeline`.

Proved, for any authorization function and any validation that implies the ledger preconditions
(`pre`), by induction over the pipeline:

* **Conservation:** for every asset, `minted = burned + sum of all balances`.
* **Vault backing:** for every asset, the vault balance equals the sum of the amounts of the pending
  escrows of that asset.
* The accounts of every escrow record are real accounts and are not the vault, so settlement never
  credits outside the ledger or the vault.

What this does **not** cover, stated so that no reader assumes it:

* Amounts are natural numbers: the `u128` overflow checks of the Rust and Python machines are not
  modelled (they only add denials, so they cannot break these invariants, but that is an argument, not
  a theorem here).
* Time, deadlines, disputes (filings), the clock and the asset migration are not modelled; they are
  further validation conditions or have their own state. The real validation is stricter than `pre`.
* Nothing connects this model to the Rust or Python machines except the shape of the operations; that
  evidence is differential testing. No Mathlib is used.
-/

namespace SIRM
namespace IntegratedLedger

open IntegratedPipeline

/-! ### Finite sums without Mathlib -/

/-- `total f n = f 0 + ... + f (n - 1)`. -/
def total (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => total f n + f n

def setAt (f : Nat → Nat) (a v : Nat) : Nat → Nat := fun i => if i = a then v else f i

theorem total_setAt_outside (f : Nat → Nat) (a v n : Nat) (h : n ≤ a) :
    total (setAt f a v) n = total f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hne : n ≠ a := by omega
    simp only [total]
    rw [ih (by omega)]
    simp [setAt, hne]

theorem total_setAt (f : Nat → Nat) (a v n : Nat) (h : a < n) :
    total (setAt f a v) n + f a = total f n + v := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hlt : a < n
    · have h1 := ih hlt
      have h2 : setAt f a v n = f n := by simp [setAt]; omega
      simp only [total]
      omega
    · have han : a = n := by omega
      subst han
      simp only [total]
      rw [total_setAt_outside f a v a (Nat.le_refl a)]
      simp [setAt]
      omega

theorem total_zero (n : Nat) : total (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [total, ih]

/-! ### The core state -/

inductive Phase where
  | pending
  | released
  | cancelled
  | expired
  deriving DecidableEq

structure Rec where
  dep : Nat
  ben : Nat
  asset : Nat
  amount : Nat
  phase : Phase
  deriving DecidableEq

/-- `bal s a` is the balance of account `a` in asset `s`. -/
structure Core where
  bal : Nat → Nat → Nat
  minted : Nat → Nat
  burned : Nat → Nat
  recs : Nat → Option Rec

structure Cfg where
  accounts : Nat
  ids : Nat
  vault : Nat

def upd (bal : Nat → Nat → Nat) (s a v : Nat) : Nat → Nat → Nat :=
  fun s' => if s' = s then setAt (bal s) a v else bal s'

def setRec (recs : Nat → Option Rec) (id : Nat) (o : Option Rec) : Nat → Option Rec :=
  fun i => if i = id then o else recs i

/-- Move `amt` of asset `s` from `src` to `dst` (debit then credit). -/
def move (bal : Nat → Nat → Nat) (s src dst amt : Nat) : Nat → Nat → Nat :=
  let b1 := upd bal s src (bal s src - amt)
  upd b1 s dst (b1 s dst + amt)

def contrib (o : Option Rec) (s : Nat) : Nat :=
  match o with
  | some r => if r.phase = Phase.pending ∧ r.asset = s then r.amount else 0
  | none => 0

/-- Sum of the pending escrow amounts of asset `s` over the ids below `ids`. -/
def pendingSum (recs : Nat → Option Rec) (s ids : Nat) : Nat :=
  total (fun i => contrib (recs i) s) ids

inductive Op where
  | transfer (src dst asset amount : Nat)
  | issue (recipient asset amount : Nat)
  | burn (holder asset amount : Nat)
  | open (id dep ben asset amount : Nat)
  | release (id : Nat)
  | cancel (id : Nat)
  | expire (id : Nat)
  deriving DecidableEq

structure Req where
  principal : Nat
  nonce : Nat
  op : Op
  deriving DecidableEq

/-- Settle a pending escrow: the vault pays the beneficiary (`toBen`) or the depositor, and the record
takes its final phase. -/
def settle (cfg : Cfg) (c : Core) (id : Nat) (toBen : Bool) (ph : Phase) : Core :=
  match c.recs id with
  | some r =>
      { c with bal := move c.bal r.asset cfg.vault (if toBen then r.ben else r.dep) r.amount
               recs := setRec c.recs id (some { r with phase := ph }) }
  | none => c

/-- The effect of a request on the core state (meaningful when `pre` holds). -/
def applyOp (cfg : Cfg) (c : Core) : Op → Core
  | .transfer src dst s amt => { c with bal := move c.bal s src dst amt }
  | .issue r s amt =>
      { c with bal := upd c.bal s r (c.bal s r + amt), minted := fun t => if t = s then c.minted t + amt else c.minted t }
  | .burn h s amt =>
      { c with bal := upd c.bal s h (c.bal s h - amt), burned := fun t => if t = s then c.burned t + amt else c.burned t }
  | .open id dep ben s amt =>
      { c with bal := move c.bal s dep cfg.vault amt
               recs := setRec c.recs id (some ⟨dep, ben, s, amt, Phase.pending⟩) }
  | .release id => settle cfg c id true Phase.released
  | .cancel id => settle cfg c id false Phase.cancelled
  | .expire id => settle cfg c id false Phase.expired

/-- Ledger preconditions of each operation. The real validation is stricter (time, filings, zero
amounts, overflow, unknown accounts); the proofs only need these. -/
def pre (cfg : Cfg) (c : Core) : Op → Prop
  | .transfer src dst s amt =>
      src < cfg.accounts ∧ dst < cfg.accounts ∧ src ≠ cfg.vault ∧ dst ≠ cfg.vault ∧ amt ≤ c.bal s src
  | .issue r _ _ => r < cfg.accounts ∧ r ≠ cfg.vault
  | .burn h s amt => h < cfg.accounts ∧ h ≠ cfg.vault ∧ amt ≤ c.bal s h
  | .open id dep ben s amt =>
      id < cfg.ids ∧ c.recs id = none ∧ dep < cfg.accounts ∧ ben < cfg.accounts ∧
      dep ≠ cfg.vault ∧ ben ≠ cfg.vault ∧ amt ≤ c.bal s dep
  | .release id => id < cfg.ids ∧ ∃ r, c.recs id = some r ∧ r.phase = Phase.pending
  | .cancel id => id < cfg.ids ∧ ∃ r, c.recs id = some r ∧ r.phase = Phase.pending
  | .expire id => id < cfg.ids ∧ ∃ r, c.recs id = some r ∧ r.phase = Phase.pending

/-- The invariants. -/
structure Inv (cfg : Cfg) (c : Core) : Prop where
  conserve : ∀ s, c.minted s = c.burned s + total (c.bal s) cfg.accounts
  backing : ∀ s, c.bal s cfg.vault = pendingSum c.recs s cfg.ids
  recsOk : ∀ i r, c.recs i = some r →
    r.dep < cfg.accounts ∧ r.ben < cfg.accounts ∧ r.dep ≠ cfg.vault ∧ r.ben ≠ cfg.vault

def Core.empty : Core :=
  { bal := fun _ _ => 0, minted := fun _ => 0, burned := fun _ => 0, recs := fun _ => none }

theorem inv_empty (cfg : Cfg) : Inv cfg Core.empty where
  conserve := by intro s; simp [Core.empty, total_zero]
  backing := by
    intro s
    show 0 = pendingSum (fun _ => none) s cfg.ids
    exact (total_zero cfg.ids).symm
  recsOk := by intro i r h; simp [Core.empty] at h

/-! ### Lemmas about `upd`, `move` and the pending sum -/

theorem upd_same (bal : Nat → Nat → Nat) (s a v : Nat) : upd bal s a v s = setAt (bal s) a v := by
  simp [upd]

theorem upd_other (bal : Nat → Nat → Nat) {s s' : Nat} (a v : Nat) (h : s' ≠ s) :
    upd bal s a v s' = bal s' := by
  simp [upd, h]

theorem move_eq (bal : Nat → Nat → Nat) (s src dst amt : Nat) :
    move bal s src dst amt s =
      setAt (setAt (bal s) src (bal s src - amt)) dst (setAt (bal s) src (bal s src - amt) dst + amt) := by
  simp [move, upd]

theorem move_other (bal : Nat → Nat → Nat) {s s' : Nat} (src dst amt : Nat) (h : s' ≠ s) :
    move bal s src dst amt s' = bal s' := by
  simp [move, upd, h]

theorem move_total (bal : Nat → Nat → Nat) (s src dst amt n : Nat)
    (hs : src < n) (hd : dst < n) (ha : amt ≤ bal s src) :
    total (move bal s src dst amt s) n = total (bal s) n := by
  have h1 := total_setAt (bal s) src (bal s src - amt) n hs
  have h2 := total_setAt (setAt (bal s) src (bal s src - amt)) dst
    (setAt (bal s) src (bal s src - amt) dst + amt) n hd
  rw [move_eq]
  omega

theorem move_src (bal : Nat → Nat → Nat) (s src dst amt : Nat) (h : src ≠ dst) :
    move bal s src dst amt s src = bal s src - amt := by
  rw [move_eq]; simp [setAt, h]

theorem move_dst (bal : Nat → Nat → Nat) (s src dst amt : Nat) (h : dst ≠ src) :
    move bal s src dst amt s dst = bal s dst + amt := by
  rw [move_eq]; simp [setAt, h]

theorem move_elsewhere (bal : Nat → Nat → Nat) (s src dst amt x : Nat) (hs : x ≠ src) (hd : x ≠ dst) :
    move bal s src dst amt s x = bal s x := by
  rw [move_eq]; simp [setAt, hs, hd]

theorem pendingSum_set (recs : Nat → Option Rec) (id : Nat) (o : Option Rec) (s ids : Nat)
    (h : id < ids) :
    pendingSum (setRec recs id o) s ids + contrib (recs id) s = pendingSum recs s ids + contrib o s := by
  unfold pendingSum
  have e : (fun i => contrib (setRec recs id o i) s) = setAt (fun i => contrib (recs i) s) id (contrib o s) := by
    funext i
    by_cases hi : i = id <;> simp [setRec, setAt, hi]
  rw [e]
  exact total_setAt (fun i => contrib (recs i) s) id (contrib o s) ids h

theorem contrib_le_pendingSum (recs : Nat → Option Rec) (id s ids : Nat) (h : id < ids) :
    contrib (recs id) s ≤ pendingSum recs s ids := by
  have := pendingSum_set recs id none s ids h
  have h0 : contrib none s = 0 := rfl
  rw [h0] at this
  omega

/-! ### Every operation preserves the invariants -/

variable {cfg : Cfg} {c : Core}

theorem inv_transfer (_hv : cfg.vault < cfg.accounts) (inv : Inv cfg c) {src dst s amt : Nat}
    (h : pre cfg c (.transfer src dst s amt)) : Inv cfg (applyOp cfg c (.transfer src dst s amt)) := by
  obtain ⟨hs, hd, hsv, hdv, ha⟩ := h
  refine ⟨?_, ?_, inv.recsOk⟩
  · intro t
    show c.minted t = c.burned t + total (move c.bal s src dst amt t) cfg.accounts
    by_cases ht : t = s
    · subst ht
      rw [move_total c.bal t src dst amt cfg.accounts hs hd ha]
      exact inv.conserve t
    · rw [move_other c.bal src dst amt ht]
      exact inv.conserve t
  · intro t
    show move c.bal s src dst amt t cfg.vault = pendingSum c.recs t cfg.ids
    by_cases ht : t = s
    · subst ht
      rw [move_elsewhere c.bal t src dst amt cfg.vault (Ne.symm hsv) (Ne.symm hdv)]
      exact inv.backing t
    · rw [move_other c.bal src dst amt ht]
      exact inv.backing t

theorem inv_issue (_hv : cfg.vault < cfg.accounts) (inv : Inv cfg c) {r s amt : Nat}
    (h : pre cfg c (.issue r s amt)) : Inv cfg (applyOp cfg c (.issue r s amt)) := by
  obtain ⟨hr, hrv⟩ := h
  refine ⟨?_, ?_, inv.recsOk⟩
  · intro t
    show (if t = s then c.minted t + amt else c.minted t) =
      c.burned t + total (upd c.bal s r (c.bal s r + amt) t) cfg.accounts
    by_cases ht : t = s
    · subst ht
      have h1 := total_setAt (c.bal t) r (c.bal t r + amt) cfg.accounts hr
      have h2 := inv.conserve t
      rw [upd_same]
      simp only [if_true]
      omega
    · rw [upd_other c.bal _ _ ht]
      simp only [ht, if_false]
      exact inv.conserve t
  · intro t
    show upd c.bal s r (c.bal s r + amt) t cfg.vault = pendingSum c.recs t cfg.ids
    by_cases ht : t = s
    · subst ht
      rw [upd_same]
      simp [setAt, Ne.symm hrv]
      exact inv.backing t
    · rw [upd_other c.bal _ _ ht]
      exact inv.backing t

theorem inv_burn (_hv : cfg.vault < cfg.accounts) (inv : Inv cfg c) {h s amt : Nat}
    (hp : pre cfg c (.burn h s amt)) : Inv cfg (applyOp cfg c (.burn h s amt)) := by
  obtain ⟨hh, hhv, ha⟩ := hp
  refine ⟨?_, ?_, inv.recsOk⟩
  · intro t
    show c.minted t = (if t = s then c.burned t + amt else c.burned t) +
      total (upd c.bal s h (c.bal s h - amt) t) cfg.accounts
    by_cases ht : t = s
    · subst ht
      have h1 := total_setAt (c.bal t) h (c.bal t h - amt) cfg.accounts hh
      have h2 := inv.conserve t
      rw [upd_same]
      simp only [if_true]
      omega
    · rw [upd_other c.bal _ _ ht]
      simp only [ht, if_false]
      exact inv.conserve t
  · intro t
    show upd c.bal s h (c.bal s h - amt) t cfg.vault = pendingSum c.recs t cfg.ids
    by_cases ht : t = s
    · subst ht
      rw [upd_same]
      simp [setAt, Ne.symm hhv]
      exact inv.backing t
    · rw [upd_other c.bal _ _ ht]
      exact inv.backing t

theorem inv_open (hv : cfg.vault < cfg.accounts) (inv : Inv cfg c) {id dep ben s amt : Nat}
    (h : pre cfg c (.open id dep ben s amt)) :
    Inv cfg (applyOp cfg c (.open id dep ben s amt)) := by
  obtain ⟨hid, hnone, hdep, hben, hdepv, hbenv, ha⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro t
    show c.minted t = c.burned t + total (move c.bal s dep cfg.vault amt t) cfg.accounts
    by_cases ht : t = s
    · subst ht
      rw [move_total c.bal t dep cfg.vault amt cfg.accounts hdep hv ha]
      exact inv.conserve t
    · rw [move_other c.bal dep cfg.vault amt ht]
      exact inv.conserve t
  · intro t
    show move c.bal s dep cfg.vault amt t cfg.vault =
      pendingSum (setRec c.recs id (some ⟨dep, ben, s, amt, Phase.pending⟩)) t cfg.ids
    have hset := pendingSum_set c.recs id (some ⟨dep, ben, s, amt, Phase.pending⟩) t cfg.ids hid
    rw [hnone] at hset
    have h0 : contrib none t = 0 := rfl
    rw [h0] at hset
    have hb := inv.backing t
    by_cases ht : t = s
    · subst ht
      rw [move_dst c.bal t dep cfg.vault amt (Ne.symm hdepv)]
      have : contrib (some ⟨dep, ben, t, amt, Phase.pending⟩) t = amt := by simp [contrib]
      rw [this] at hset
      omega
    · rw [move_other c.bal dep cfg.vault amt ht]
      have : contrib (some ⟨dep, ben, s, amt, Phase.pending⟩) t = 0 := by simp [contrib, Ne.symm ht]
      rw [this] at hset
      omega
  · intro i r hr
    show r.dep < cfg.accounts ∧ r.ben < cfg.accounts ∧ r.dep ≠ cfg.vault ∧ r.ben ≠ cfg.vault
    have hr' : setRec c.recs id (some ⟨dep, ben, s, amt, Phase.pending⟩) i = some r := hr
    by_cases hi : i = id
    · simp [setRec, hi] at hr'
      subst hr'
      exact ⟨hdep, hben, hdepv, hbenv⟩
    · simp [setRec, hi] at hr'
      exact inv.recsOk i r hr'

theorem inv_settle (hv : cfg.vault < cfg.accounts) (inv : Inv cfg c) {id : Nat} {toBen : Bool}
    {ph : Phase} (hph : ph ≠ Phase.pending) {r : Rec} (hid : id < cfg.ids)
    (hr : c.recs id = some r) (hp : r.phase = Phase.pending) :
    Inv cfg (settle cfg c id toBen ph) := by
  have e : settle cfg c id toBen ph =
      { c with bal := move c.bal r.asset cfg.vault (if toBen then r.ben else r.dep) r.amount
               recs := setRec c.recs id (some { r with phase := ph }) } := by
    simp [settle, hr]
  rw [e]
  obtain ⟨hdep, hben, hdepv, hbenv⟩ := inv.recsOk id r hr
  have hto : (if toBen then r.ben else r.dep) < cfg.accounts ∧ (if toBen then r.ben else r.dep) ≠ cfg.vault := by
    cases toBen <;> simp [hdep, hben, hdepv, hbenv]
  obtain ⟨hto1, hto2⟩ := hto
  have hcontrib : contrib (c.recs id) r.asset = r.amount := by simp [contrib, hr, hp]
  have hle : r.amount ≤ c.bal r.asset cfg.vault := by
    rw [inv.backing r.asset]
    have := contrib_le_pendingSum c.recs id r.asset cfg.ids hid
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro t
    show c.minted t = c.burned t + total (move c.bal r.asset cfg.vault (if toBen then r.ben else r.dep) r.amount t) cfg.accounts
    by_cases ht : t = r.asset
    · subst ht
      rw [move_total c.bal r.asset cfg.vault _ r.amount cfg.accounts hv hto1 hle]
      exact inv.conserve r.asset
    · rw [move_other c.bal _ _ _ ht]
      exact inv.conserve t
  · intro t
    show move c.bal r.asset cfg.vault (if toBen then r.ben else r.dep) r.amount t cfg.vault =
      pendingSum (setRec c.recs id (some { r with phase := ph })) t cfg.ids
    have hset := pendingSum_set c.recs id (some { r with phase := ph }) t cfg.ids hid
    have hb := inv.backing t
    rw [hr] at hset
    have hnew : contrib (some { r with phase := ph }) t = 0 := by simp [contrib, hph]
    rw [hnew] at hset
    by_cases ht : t = r.asset
    · subst ht
      rw [move_src c.bal r.asset cfg.vault _ r.amount (Ne.symm hto2)]
      have : contrib (some r) r.asset = r.amount := by simpa [hr] using hcontrib
      rw [this] at hset
      omega
    · rw [move_other c.bal _ _ _ ht]
      have : contrib (some r) t = 0 := by simp [contrib, Ne.symm ht]
      rw [this] at hset
      omega
  · intro i r' hr'
    show r'.dep < cfg.accounts ∧ r'.ben < cfg.accounts ∧ r'.dep ≠ cfg.vault ∧ r'.ben ≠ cfg.vault
    have hr'' : setRec c.recs id (some { r with phase := ph }) i = some r' := hr'
    by_cases hi : i = id
    · simp [setRec, hi] at hr''
      subst hr''
      exact ⟨hdep, hben, hdepv, hbenv⟩
    · simp [setRec, hi] at hr''
      exact inv.recsOk i r' hr''

/-- Every operation whose ledger preconditions hold preserves the invariants. -/
theorem inv_applyOp (hv : cfg.vault < cfg.accounts) (inv : Inv cfg c) (op : Op) (h : pre cfg c op) :
    Inv cfg (applyOp cfg c op) := by
  cases op with
  | transfer src dst s amt => exact inv_transfer hv inv h
  | issue r s amt => exact inv_issue hv inv h
  | burn x s amt => exact inv_burn hv inv h
  | «open» id dep ben s amt => exact inv_open hv inv h
  | release id =>
      obtain ⟨hid, r, hr, hp⟩ := h
      exact inv_settle hv inv (by decide) hid hr hp
  | cancel id =>
      obtain ⟨hid, r, hr, hp⟩ := h
      exact inv_settle hv inv (by decide) hid hr hp
  | expire id =>
      obtain ⟨hid, r, hr, hp⟩ := h
      exact inv_settle hv inv (by decide) hid hr hp

/-! ### The pipeline over this core -/

/-- The rules of the integrated machine on this core: any authorization function, any validation
(denials are numbered), and the effect `applyOp`. -/
def rules (cfg : Cfg) (auth : Core → Req → Bool) (validate : Core → Req → Option Nat) :
    Rules Nat Req Core Nat where
  principal := Req.principal
  nonce := Req.nonce
  authorized := auth
  authDenial := fun _ => 0
  validate := validate
  apply := fun c r => applyOp cfg c r.op

/-- One pipeline step keeps the invariants, whatever the authorization is and whatever the request is,
provided that accepted requests satisfy the ledger preconditions. -/
theorem pipeline_invariant (cfg : Cfg) (hv : cfg.vault < cfg.accounts)
    (auth : Core → Req → Bool) (validate : Core → Req → Option Nat)
    (hval : ∀ c r, validate c r = none → pre cfg c r.op)
    (s : State Nat Nat Req Core Nat) (id : Nat) (r : Req) (h : Inv cfg s.core) :
    Inv cfg (process (rules cfg auth validate) s id r).1.core :=
  process_preserves (rules cfg auth validate) s id r (Inv cfg)
    (fun c q _ hq hi => inv_applyOp hv hi q.op (hval c q hq)) h

/-- The machine: initial states have the empty core; a step is the processing of one request. -/
def machine (cfg : Cfg) (hv : cfg.vault < cfg.accounts)
    (auth : Core → Req → Bool) (validate : Core → Req → Option Nat)
    (hval : ∀ c r, validate c r = none → pre cfg c r.op) :
    VerifiedStateMachine (State Nat Nat Req Core Nat) where
  invariant := fun s => Inv cfg s.core
  initial := fun s => s.core = Core.empty
  step := fun s s' => ∃ (id : Nat) (r : Req), s' = (process (rules cfg auth validate) s id r).1
  initial_safe := by
    intro s h
    rw [h]
    exact inv_empty cfg
  step_safe := by
    intro s s' hs ⟨id, r, e⟩
    rw [e]
    exact pipeline_invariant cfg hv auth validate hval s id r hs

/-- In every reachable state, for every asset, `minted = burned + sum of balances`, the vault holds
exactly the pending escrows, and no escrow names the vault or a non-account. -/
theorem reachable_safe (cfg : Cfg) (hv : cfg.vault < cfg.accounts)
    (auth : Core → Req → Bool) (validate : Core → Req → Option Nat)
    (hval : ∀ c r, validate c r = none → pre cfg c r.op)
    {s : State Nat Nat Req Core Nat} (h : Reachable (machine cfg hv auth validate hval) s) :
    Inv cfg s.core :=
  invariant_of_reachable (machine cfg hv auth validate hval) h

/-! ### A concrete scenario (the invariants are not vacuous) -/

section Demo

def cfg3 : Cfg := { accounts := 3, ids := 2, vault := 2 }

def c1 : Core := applyOp cfg3 Core.empty (.issue 0 0 100)
def c2 : Core := applyOp cfg3 c1 (.open 0 0 1 0 40)
def c3 : Core := applyOp cfg3 c2 (.release 0)

theorem pre_issue : pre cfg3 Core.empty (.issue 0 0 100) := by
  simp [pre, cfg3]

theorem pre_open : pre cfg3 c1 (.open 0 0 1 0 40) := by
  simp [pre, cfg3, c1, applyOp, upd, setAt, Core.empty]

theorem pre_release : pre cfg3 c2 (.release 0) := by
  refine ⟨by decide, ⟨0, 1, 0, 40, Phase.pending⟩, ?_, rfl⟩
  decide

example : c2.bal 0 0 = 60 ∧ c2.bal 0 1 = 0 ∧ c2.bal 0 2 = 40 := by decide
example : c3.bal 0 0 = 60 ∧ c3.bal 0 1 = 40 ∧ c3.bal 0 2 = 0 := by decide
example : c3.minted 0 = 100 ∧ c3.burned 0 = 0 := by decide
-- the invariants hold along the scenario, by the theorems above
example : Inv cfg3 c3 :=
  inv_applyOp (by decide)
    (inv_applyOp (by decide) (inv_applyOp (by decide) (inv_empty cfg3) _ pre_issue) _ pre_open)
    _ pre_release

end Demo

end IntegratedLedger
end SIRM
