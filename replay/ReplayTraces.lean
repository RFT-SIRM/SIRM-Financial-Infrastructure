import Lean.Data.Json
import SIRM.IntegratedLedger

/-!
# Replaying the reference traces in the Lean model (differential evidence, not a refinement proof)

`lean --run replay/ReplayTraces.lean <trace.json>...` replays every episode of the committed integrated
traces (`integrated_trace_v0.json`, `integrated_resolve_trace_v0.json`) through the Lean model itself:
the generic pipeline `SIRM.IntegratedPipeline.process` with the rules of `SIRM.IntegratedLedger`
(`policyAuth`, `applyOp`), the policy and configuration of the episode, and the outcome tokens of the
independent Python reference as the oracle for validation. For every request it checks

1. the class of the answer: replay (`R`), conflict (`C`), stale (`S`), future (`F`), accepted (`A`) or
   denied (`N`) against the Lean pipeline's own outcome;
2. authorization: a request that reached authorization is authorized in Lean exactly when the reference
   did not deny it as unauthorized;
3. the ledger preconditions: every request the reference accepted satisfies the Lean predicate `pre`
   (through `preB`, proved sound below), which is the hypothesis `hval` of every Lean theorem;

and, at the end of an episode, the Lean state against the reference's final state: balances, minted and
burned totals, escrow records, dispute filings, migration totals, the clock and the nonces.

What this is not: the Lean model does not validate (the Lean `pre` is deliberately weaker than the
reference validation), so which request is accepted is taken from the reference; this checks that the
model's authorization, nonce and cache rules, preconditions and effects agree with the code on these
traces, not that the code refines the model.
-/

open SIRM SIRM.IntegratedPipeline SIRM.IntegratedLedger

/-! ### A boolean version of `pre`, proved sound -/

def isPending (o : Option Rec) : Bool :=
  match o with
  | some r => decide (r.phase = Phase.pending)
  | none => false

def party (o : Option Rec) (cl : Nat) : Bool :=
  match o with
  | some r => decide (r.phase = Phase.pending) && (decide (cl = r.dep) || decide (cl = r.ben))
  | none => false

def preB (cfg : Cfg) (c : Core) : Op → Bool
  | .transfer src dst s amt =>
      decide (src < cfg.accounts) && decide (dst < cfg.accounts) && decide (src ≠ cfg.vault) &&
        decide (dst ≠ cfg.vault) && (decide (src = dst) || decide (amt ≤ c.bal s src))
  | .issue _ r _ _ => decide (r < cfg.accounts) && decide (r ≠ cfg.vault)
  | .burn h s amt => decide (h < cfg.accounts) && decide (h ≠ cfg.vault) && decide (amt ≤ c.bal s h)
  | .open id dep ben s amt =>
      decide (id < cfg.ids) && (c.recs id).isNone && decide (dep < cfg.accounts) &&
        decide (ben < cfg.accounts) && decide (dep ≠ cfg.vault) && decide (ben ≠ cfg.vault) &&
        decide (amt ≤ c.bal s dep) && decide (c.now < cfg.deadline id)
  | .release id =>
      decide (id < cfg.ids) && (c.files id).isNone && decide (c.now < cfg.deadline id) &&
        isPending (c.recs id)
  | .cancel id =>
      decide (id < cfg.ids) && (c.files id).isNone && decide (c.now < cfg.deadline id) &&
        isPending (c.recs id)
  | .expire id =>
      decide (id < cfg.ids) && (c.files id).isNone && decide (cfg.deadline id ≤ c.now) &&
        isPending (c.recs id)
  | .migrate amt =>
      match cfg.mig with
      | some m =>
          decide (0 < m.den) && decide (m.holder < cfg.accounts) && decide (m.recipient < cfg.accounts) &&
            decide (m.holder ≠ cfg.vault) && decide (m.recipient ≠ cfg.vault) &&
            decide (amt ≤ c.bal m.src m.holder)
      | none => false
  | .dispute id cl =>
      decide (id < cfg.ids) && (c.files id).isNone && decide (c.now < cfg.deadline id) &&
        party (c.recs id) cl
  | .advance t => decide (c.now < t)
  | .resolve id _ => decide (id < cfg.ids) && (c.files id).isSome && isPending (c.recs id)

theorem preB_sound (cfg : Cfg) (c : Core) (op : Op) (h : preB cfg c op = true) : pre cfg c op := by
  cases op with
  | transfer src dst s amt =>
      simp only [preB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
      exact ⟨h1, h2, h3, h4, h5⟩
  | issue i r s amt =>
      simp only [preB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, h.2⟩
  | burn x s amt =>
      simp only [preB, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      exact ⟨h1, h2, h3⟩
  | «open» id dep ben s amt =>
      simp only [preB, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
      exact ⟨h1, Option.isNone_iff_eq_none.1 h2, h3, h4, h5, h6, h7, h8⟩
  | release id =>
      simp only [preB, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
      refine ⟨h1, Option.isNone_iff_eq_none.1 h2, h3, ?_⟩
      unfold isPending at h4
      cases hr : c.recs id with
      | none => simp [hr] at h4
      | some r => rw [hr] at h4; exact ⟨r, rfl, by simpa using h4⟩
  | cancel id =>
      simp only [preB, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
      refine ⟨h1, Option.isNone_iff_eq_none.1 h2, h3, ?_⟩
      unfold isPending at h4
      cases hr : c.recs id with
      | none => simp [hr] at h4
      | some r => rw [hr] at h4; exact ⟨r, rfl, by simpa using h4⟩
  | expire id =>
      simp only [preB, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
      refine ⟨h1, Option.isNone_iff_eq_none.1 h2, h3, ?_⟩
      unfold isPending at h4
      cases hr : c.recs id with
      | none => simp [hr] at h4
      | some r => rw [hr] at h4; exact ⟨r, rfl, by simpa using h4⟩
  | migrate amt =>
      unfold preB at h
      cases hm : cfg.mig with
      | none => rw [hm] at h; simp at h
      | some m =>
          rw [hm] at h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
          exact ⟨m, hm, h1, h2, h3, h4, h5, h6⟩
  | dispute id cl =>
      simp only [preB, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
      refine ⟨h1, Option.isNone_iff_eq_none.1 h2, h3, ?_⟩
      unfold party at h4
      cases hr : c.recs id with
      | none => simp [hr] at h4
      | some r =>
          rw [hr] at h4
          simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h4
          exact ⟨r, rfl, h4.1, h4.2⟩
  | advance t => show c.now < t; simpa [preB] using h
  | resolve id toBen =>
      simp only [preB, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      refine ⟨h1, ?_, ?_⟩
      · cases hf : c.files id with
        | none => simp [hf] at h2
        | some f => exact ⟨f, rfl⟩
      · unfold isPending at h3
        cases hr : c.recs id with
        | none => simp [hr] at h3
        | some r => rw [hr] at h3; exact ⟨r, rfl, by simpa using h3⟩

/-! ### Reading a trace -/

deriving instance Inhabited for Kind, Op, Phase

def nat (j : Lean.Json) : Nat :=
  match j with
  | .str s => s.toNat!
  | j => match j.getNat? with
    | .ok n => n
    | .error e => panic! e

def arr (j : Lean.Json) : Array Lean.Json :=
  match j.getArr? with
  | .ok a => a
  | .error e => panic! e

def fld (j : Lean.Json) (k : String) : Lean.Json :=
  match j.getObjVal? k with
  | .ok v => v
  | .error e => panic! e

def str (j : Lean.Json) : String :=
  match j.getStr? with
  | .ok s => s
  | .error e => panic! e

def kindOf : String → Kind
  | "transfer" => .transfer
  | "issue" => .issue
  | "burn" => .burn
  | "open" => .open
  | "release" => .release
  | "cancel" => .cancel
  | "expire" => .expire
  | "migrate" => .migrate
  | "dispute" => .dispute
  | "resolve" => .resolve
  | s => panic! s!"kind {s}"

def opOf (row : Array Lean.Json) : Op :=
  let n := fun k => nat row[k]!
  match str row[3]! with
  | "transfer" => .transfer (n 4) (n 5) (n 6) (n 7)
  | "issue" => .issue (n 4) (n 5) (n 6) (n 7)
  | "burn" => .burn (n 4) (n 6) (n 7)
  | "open" => .open (n 4) (n 5) (n 6) (n 7) (n 8)
  | "release" => .release (n 4)
  | "cancel" => .cancel (n 4)
  | "expire" => .expire (n 4)
  | "dispute" => .dispute (n 4) (n 5)
  | "advance" => .advance (n 4)
  | "migrate" => .migrate (n 4)
  | "resolve" => .resolve (n 4) (n 5 != 0)
  | s => panic! s!"op {s}"

def phaseOf : String → Phase
  | "pending" => .pending
  | "released" => .released
  | "cancelled" => .cancelled
  | "expired" => .expired
  | s => panic! s!"phase {s}"

def policyOf (p : Lean.Json) : Policy :=
  let ctl := (arr (fld p "control")).toList.map fun c => (nat (arr c)[0]!, nat (arr c)[1]!)
  let lims := (arr (fld p "limits")).toList.map fun g =>
    let g := arr g
    ((nat g[0]!, kindOf (str g[1]!), nat g[2]!, (if g[3]! == .null then none else some (nat g[3]!)), nat g[4]!),
      nat g[5]!)
  let ids := (arr (fld p "ids")).toList.map fun i => (nat (arr i)[0]!, kindOf (str (arr i)[1]!), nat (arr i)[2]!)
  let clk := (arr (fld p "clock")).toList.map nat
  { controls := fun p a => ctl.any fun (x, y) => x == p && y == a
    limit := fun p k a b s =>
      match lims.find? fun (key, _) => key.1 == p && decide (key.2.1 = k) && key.2.2.1 == a &&
          key.2.2.2.1 == b && key.2.2.2.2 == s with
      | some (_, v) => some v
      | none => none
    ids := fun p k i => ids.any fun (x, kk, y) => x == p && decide (kk = k) && y == i
    clock := fun p => clk.any (· == p) }

def cfgOf (accounts ids : Nat) (ep : Lean.Json) : Cfg :=
  let dl := (arr (fld ep "deadlines")).toList.map nat
  let mg := fld ep "migration"
  { accounts := accounts, ids := ids, vault := nat (fld ep "vault"),
    mig := if mg == .null then none else
      some ⟨nat (fld mg "holder"), nat (fld mg "recipient"), nat (fld mg "src"), nat (fld mg "dst"),
        nat (fld mg "num"), nat (fld mg "den")⟩,
    deadline := fun i => dl.getD i 0 }

/-- Auth denials of the reference: `<op>:auth` or the short codes `ta`, `ia`, `ba`. -/
def isAuthDenial (tok : String) : Bool :=
  let code := (tok.drop 1).takeWhile (· != '@')
  code.endsWith ":auth" || code == "ta" || code == "ia" || code == "ba"

structure Counts where
  requests : Nat := 0
  accepted : Nat := 0
  resolves : Nat := 0
  mismatches : Nat := 0
  deriving Repr

abbrev St := State Nat Nat Req Core Nat

def classOk (tok : String) : Outcome Nat → Bool
  | .replay _ => tok.startsWith "R"
  | .conflict => tok.startsWith "C"
  | .stale => tok.startsWith "S"
  | .future => tok.startsWith "F"
  | .fresh (.accepted _) => tok.startsWith "A"
  | .fresh (.denied _ _) => tok.startsWith "N"

def replayEpisode (accounts assets ids : Nat) (ep : Lean.Json) (cnt : Counts) : IO Counts := do
  let cfg := cfgOf accounts ids ep
  let pol := policyOf (fld ep "policy")
  let mut s : St := { core := { Core.empty with now := nat (fld ep "start_now") },
                      nonces := fun _ => 0, cache := fun _ => none }
  let mut cnt := cnt
  let reqs := arr (fld ep "requests")
  let toks := arr (fld ep "tokens")
  for i in [0:reqs.size] do
    let row := arr reqs[i]!
    let tok := str toks[i]!
    let req : Req := ⟨nat row[1]!, nat row[2]!, opOf row⟩
    let accepted := tok.startsWith "A"
    let rules := rules cfg (policyAuth cfg pol) (fun _ _ => if accepted then none else some 1)
    let (s', out) := process rules s (nat row[0]!) req
    cnt := { cnt with requests := cnt.requests + 1 }
    let mut bad := false
    if !classOk tok out then
      bad := true
      IO.eprintln s!"class mismatch: request {i} token {tok}"
    -- only requests that reached authorization carry an authorization verdict
    match out with
    | .fresh (.denied _ _) =>
        if authorizedOp cfg pol req.principal req.op == isAuthDenial tok then
          bad := true
          IO.eprintln s!"authorization mismatch: request {i} token {tok}"
    | .fresh (.accepted _) =>
        cnt := { cnt with accepted := cnt.accepted + 1 }
        if let .resolve .. := req.op then cnt := { cnt with resolves := cnt.resolves + 1 }
        if !authorizedOp cfg pol req.principal req.op then
          bad := true
          IO.eprintln s!"accepted but not authorized in Lean: request {i} token {tok}"
        if !preB cfg s.core req.op then
          bad := true
          IO.eprintln s!"accepted but Lean `pre` fails: request {i} token {tok} op {str row[3]!} args {(row.toList.drop 4).map (·.compress)}"
    | _ => pure ()
    if bad then cnt := { cnt with mismatches := cnt.mismatches + 1 }
    s := s'
  -- final state
  let fin := fld ep "final"
  let c := s.core
  let mut bad := 0
  let chk (name : String) (ok : Bool) : IO Nat := do
    if ok then return 0
    IO.eprintln s!"final state mismatch: {name}"
    return 1
  let bals := arr (fld fin "balances")
  for a in [0:accounts] do
    for t in [0:assets] do
      bad := bad + (← chk s!"balance {a} {t}" (c.bal t a == nat (arr bals[a]!)[t]!))
  let sup := arr (fld fin "supply")
  for t in [0:assets] do
    bad := bad + (← chk s!"minted {t}" (c.minted t == nat (arr sup[t]!)[0]!))
    bad := bad + (← chk s!"burned {t}" (c.burned t == nat (arr sup[t]!)[1]!))
  let recs := arr (fld fin "records")
  for i in [0:ids] do
    match recs[i]! with
    | .null => bad := bad + (← chk s!"record {i} absent" (c.recs i).isNone)
    | j =>
        let r := arr j
        bad := bad + (← chk s!"record {i}" (match c.recs i with
          | some x => x.dep == nat r[0]! && x.ben == nat r[1]! && x.asset == nat r[2]! &&
              x.amount == nat r[3]! && decide (x.phase = phaseOf (str r[4]!))
          | none => false))
  let files := arr (fld fin "filings")
  for i in [0:ids] do
    match files[i]! with
    | .null => bad := bad + (← chk s!"filing {i} absent" (c.files i).isNone)
    | j =>
        let f := arr j
        bad := bad + (← chk s!"filing {i}" (match c.files i with
          | some x => x.claimant == nat f[1]! && x.filedAt == nat f[2]!
          | none => false))
  let mig := fld fin "migration"
  bad := bad + (← chk "total_source" (c.tsrc == nat (fld mig "total_source")))
  bad := bad + (← chk "total_target" (c.ttgt == nat (fld mig "total_target")))
  bad := bad + (← chk "dust" (c.dust == nat (fld mig "dust")))
  bad := bad + (← chk "now" (c.now == nat (fld fin "now")))
  let nonces := arr (fld fin "nonces")
  for p in [0:nonces.size] do
    bad := bad + (← chk s!"nonce {p}" (s.nonces p == nat nonces[p]!))
  return { cnt with mismatches := cnt.mismatches + bad }

def main (args : List String) : IO UInt32 := do
  let mut total : Counts := {}
  for path in args do
    let txt ← IO.FS.readFile path
    let j ← match Lean.Json.parse txt with
      | .ok j => pure j
      | .error e => throw (IO.userError s!"{path}: {e}")
    let accounts := nat (fld j "accounts")
    let assets := nat (fld j "assets")
    let ids := nat (fld j "ids")
    let eps := arr (fld j "episodes")
    let mut cnt : Counts := {}
    for ep in eps do
      cnt ← replayEpisode accounts assets ids ep cnt
    IO.println s!"{path}: episodes {eps.size}, requests {cnt.requests}, accepted {cnt.accepted}, accepted resolves {cnt.resolves}, mismatches {cnt.mismatches}"
    total := { requests := total.requests + cnt.requests, accepted := total.accepted + cnt.accepted,
               resolves := total.resolves + cnt.resolves, mismatches := total.mismatches + cnt.mismatches }
  IO.println s!"LEAN_REPLAY requests={total.requests} mismatches={total.mismatches}"
  return if total.mismatches == 0 && total.requests > 0 then 0 else 1
