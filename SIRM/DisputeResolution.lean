import SIRM.BoundedAmounts

/-!
# Dispute Resolution by an Arbiter (proposal, not adopted)

A disputed escrow (see `SIRM.IntegratedLedger`) is frozen: release, cancel and expire need an empty
filing slot, so a filing is never removed and its funds stay in the vault. This file adds the
smallest exit from that state, as a separate layer on top of the integrated model:

* `resolve` pays the vault amount of one disputed escrow to the beneficiary or to the depositor,
  consumes the filing and records the final phase (`released` for the beneficiary, `cancelled` for
  the depositor; separate phases for resolved disputes are left out on purpose, so the integrated
  model, its wire formats and the Rust and Python machines stay unchanged);
* `resolveStep` guards it: it acts only when an explicitly granted arbiter permission `arb p id`
  holds, the escrow is pending, and a filing exists for it. Otherwise the core is returned unchanged.

Proved, for any arbiter permission:

* the ledger invariants (conservation, vault backing, the migration equation, filings belong to
  pending escrows) are preserved, so a resolution cannot create or destroy value;
* the supply counters, the burned totals, the migration totals, the remainder and the clock are
  unchanged, and the bounds of `SIRM.BoundedAmounts` are preserved;
* the payout is exactly `move` of the escrowed amount out of the vault to the chosen party;
* an arbiter cannot act without the grant, cannot touch an escrow that has no filing, and cannot
  resolve an escrow twice (the first resolution leaves it non-pending).

Not covered, stated so that no reader assumes it: who the arbiter is and how a grant is obtained;
what counts as evidence; deadlines for the arbiter; appeals and reversal; the wire format, the
signed-request layer, the Rust and Python machines and the state commitment do not know about
`resolve`. Nothing here claims that a resolution is fair, only that it is accounted for. No Mathlib.
-/

namespace SIRM
namespace DisputeResolution

open IntegratedPipeline IntegratedLedger BoundedAmounts

/-- The guarded step: acts only with the arbiter permission, on a pending escrow with a filing. -/
def resolveStep (cfg : Cfg) (arb : Nat → Nat → Bool) (c : Core) (p id : Nat) (toBen : Bool) : Core :=
  match c.recs id, c.files id with
  | some r, some _ =>
      if arb p id = true ∧ id < cfg.ids ∧ r.phase = Phase.pending then resolveEff cfg c id toBen else c
  | _, _ => c

theorem resolveStep_inv {cfg : Cfg} {c : Core} (hv : cfg.vault < cfg.accounts) (inv : Inv cfg c)
    (arb : Nat → Nat → Bool) (p id : Nat) (toBen : Bool) :
    Inv cfg (resolveStep cfg arb c p id toBen) := by
  unfold resolveStep
  split
  · rename_i r f hr hf
    split
    · rename_i h
      exact inv_resolveEff hv inv h.2.1 hr h.2.2 toBen
    · exact inv
  · exact inv

/-! ### The guard -/

theorem resolveStep_unauthorized (cfg : Cfg) (arb : Nat → Nat → Bool) (c : Core) (p id : Nat)
    (toBen : Bool) (h : arb p id = false) : resolveStep cfg arb c p id toBen = c := by
  unfold resolveStep
  split
  · split
    · rename_i hh; rw [h] at hh; simp at hh
    · rfl
  · rfl

theorem resolveStep_undisputed (cfg : Cfg) (arb : Nat → Nat → Bool) (c : Core) (p id : Nat)
    (toBen : Bool) (h : c.files id = none) : resolveStep cfg arb c p id toBen = c := by
  unfold resolveStep
  split
  · rename_i r f hr hf; rw [h] at hf; cases hf
  · rfl

theorem resolveStep_not_pending (cfg : Cfg) (arb : Nat → Nat → Bool) (c : Core) (p id : Nat)
    (toBen : Bool) {r : Rec} (hr : c.recs id = some r) (h : r.phase ≠ Phase.pending) :
    resolveStep cfg arb c p id toBen = c := by
  unfold resolveStep
  split
  · rename_i r' f hr' hf
    rw [hr] at hr'
    cases hr'
    split
    · rename_i hh; exact absurd hh.2.2 h
    · rfl
  · rfl

/-! ### What a resolution does -/

theorem resolve_balance {cfg : Cfg} {c : Core} {id : Nat} {r : Rec} (hr : c.recs id = some r)
    (toBen : Bool) :
    (resolveEff cfg c id toBen).bal =
      move c.bal r.asset cfg.vault (if toBen then r.ben else r.dep) r.amount :=
  settle_bal (c := clearFile c id) (id := id) (r := r) hr

theorem resolve_recs {cfg : Cfg} {c : Core} {id : Nat} {r : Rec} (hr : c.recs id = some r)
    (toBen : Bool) :
    (resolveEff cfg c id toBen).recs id =
      some { r with phase := if toBen then Phase.released else Phase.cancelled } := by
  have hr' : (clearFile c id).recs id = some r := hr
  simp [resolveEff, settle, hr', setRec]

theorem resolve_files (cfg : Cfg) (c : Core) (id : Nat) (toBen : Bool) :
    (resolveEff cfg c id toBen).files id = none := by
  unfold resolveEff settle
  split <;> simp [clearFile, setFile]

theorem resolve_supply (cfg : Cfg) (c : Core) (id : Nat) (toBen : Bool) :
    (resolveEff cfg c id toBen).minted = c.minted ∧ (resolveEff cfg c id toBen).burned = c.burned ∧
    (resolveEff cfg c id toBen).tsrc = c.tsrc ∧ (resolveEff cfg c id toBen).ttgt = c.ttgt ∧
    (resolveEff cfg c id toBen).dust = c.dust := by
  unfold resolveEff settle
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem resolve_now (cfg : Cfg) (c : Core) (id : Nat) (toBen : Bool) :
    (resolveEff cfg c id toBen).now = c.now := by
  unfold resolveEff settle
  split <;> rfl

theorem resolve_bounded {cfg : Cfg} {lim : Nat} {c : Core} (b : Bounded lim c) (id : Nat)
    (toBen : Bool) : Bounded lim (resolveEff cfg c id toBen) := by
  have hb : Bounded lim (clearFile c id) := ⟨b.minted, b.tsrc, b.ttgt, b.dust⟩
  exact bounded_settle cfg lim hb id toBen _

/-- A resolved escrow cannot be resolved again, and the arbiter's grant does not help. -/
theorem resolve_once {cfg : Cfg} {c : Core} {id : Nat} {r : Rec} (hr : c.recs id = some r)
    (arb : Nat → Nat → Bool) (p : Nat) (toBen toBen' : Bool) :
    resolveStep cfg arb (resolveEff cfg c id toBen) p id toBen' = resolveEff cfg c id toBen := by
  apply resolveStep_not_pending cfg arb _ p id toBen' (r := { r with phase := if toBen then Phase.released else Phase.cancelled })
  · exact resolve_recs hr toBen
  · cases toBen <;> simp

end DisputeResolution
end SIRM
