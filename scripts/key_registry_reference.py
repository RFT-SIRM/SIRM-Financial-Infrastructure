#!/usr/bin/env python3
"""Independent Python reference for the key lifecycle models (PROPOSAL).

Mirrors SIRM/KeyRegistry.lean, SIRM/RecoveryDelay.lean and SIRM/ThresholdAuth.lean with seeded
traces. Output: engineering/ledger_core/results/key_registry_trace_v0.json

The registry-level delayed recovery differs from the per-account Lean DelayState in one explicit
way: initiate/cancel/finalize on a principal with no account fail with unknownAccount first.
"""
import json, os, random

PQ = {2, 0x0101}
DELAY = 50
STATUS_PERMITS = {"active": True, "deprecated": None, "proposed": False, "disabled": False}


def is_pq(suite):
    return suite in PQ


class Err(Exception):
    def __init__(self, code):
        super().__init__(code); self.code = code


class Registry:
    def __init__(self):
        self.acct = {}      # principal -> dict
        self.pending = {}   # principal -> (new_suite, new_key, start)

    def snapshot(self):
        return (json.dumps(self.acct, sort_keys=True), json.dumps(self.pending, sort_keys=True))

    # --- KeyRegistry.lean primitives (keyApply) ---
    def register(self, actor, p, suite, key, rec):
        if p in self.acct:
            raise Err("alreadyRegistered")
        self.acct[p] = dict(suite=suite, key=key, rec=rec, frozen=False, revoked=False, pq=is_pq(suite))

    def rotate(self, actor, p, suite, key):
        a = self.acct.get(p)
        if a is None: raise Err("unknownAccount")
        if actor != "cur": raise Err("notAuthorized")
        if a["revoked"]: raise Err("revoked")
        if a["frozen"]: raise Err("frozen")
        if a["pq"] and not is_pq(suite): raise Err("pqDowngrade")
        a.update(suite=suite, key=key, pq=a["pq"] or is_pq(suite))

    def freeze(self, actor, p):
        a = self.acct.get(p)
        if a is None: raise Err("unknownAccount")
        a["frozen"] = True

    def revoke(self, actor, p):
        a = self.acct.get(p)
        if a is None: raise Err("unknownAccount")
        if actor != "rec": raise Err("notAuthorized")
        if a["rec"] is None: raise Err("noRecovery")
        a.update(frozen=True, revoked=True)

    def recover(self, actor, p, suite, key):
        a = self.acct.get(p)
        if a is None: raise Err("unknownAccount")
        if actor != "rec": raise Err("notAuthorized")
        if a["rec"] is None: raise Err("noRecovery")
        if a["pq"] and not is_pq(suite): raise Err("pqDowngrade")
        a.update(suite=suite, key=key, frozen=False, revoked=False, pq=a["pq"] or is_pq(suite))

    # --- RecoveryDelay.lean ---
    def initiate(self, actor, p, suite, key, now):
        a = self.acct.get(p)
        if a is None: raise Err("unknownAccount")
        if actor != "rec": raise Err("notAuthorized")
        if a["rec"] is None: raise Err("noRecovery")
        if p in self.pending: raise Err("alreadyPending")
        self.pending[p] = [suite, key, now]

    def cancel(self, actor, p):
        if p not in self.acct: raise Err("unknownAccount")
        if actor != "cur": raise Err("notAuthorized")
        if p not in self.pending: raise Err("noPending")
        del self.pending[p]

    def finalize(self, actor, p, now):
        if p not in self.acct: raise Err("unknownAccount")
        if p not in self.pending: raise Err("noPending")
        if actor != "rec": raise Err("notAuthorized")
        suite, key, start = self.pending[p]
        if now < start + DELAY: raise Err("tooEarly")
        try:
            self.recover("rec", p, suite, key)
        except Err as e:
            raise Err("rejected:" + e.code)
        del self.pending[p]

    def pq_sound(self):
        return all((not a["pq"]) or is_pq(a["suite"]) for a in self.acct.values())


def run_trace(seed, n):
    rnd = random.Random(seed)
    reg = Registry()
    ops, outs = [], []
    now = 0
    suites = [1, 2, 0x0101, 3]
    for _ in range(n):
        now += rnd.choice([0, 0, 1, 7, 30])
        p = rnd.randrange(6)
        actor = rnd.choice(["cur", "cur", "rec"])
        suite, key = rnd.choice(suites), rnd.randrange(5)
        kind = rnd.choice(["register", "rotate", "rotate", "freeze", "revoke", "recover",
                           "initiate", "initiate", "cancel", "finalize", "finalize"])
        if kind == "register":
            rec = None if rnd.random() < 0.3 else [rnd.choice([3, 4]), rnd.randrange(5)]
            op = dict(op="register", actor=actor, p=p, suite=suite, key=key, rec=rec, now=now)
            call = lambda: reg.register(actor, p, suite, key, rec)
        elif kind == "rotate":
            op = dict(op="rotate", actor=actor, p=p, suite=suite, key=key, now=now)
            call = lambda: reg.rotate(actor, p, suite, key)
        elif kind == "freeze":
            op = dict(op="freeze", actor=actor, p=p, now=now)
            call = lambda: reg.freeze(actor, p)
        elif kind == "revoke":
            op = dict(op="revoke", actor=actor, p=p, now=now)
            call = lambda: reg.revoke(actor, p)
        elif kind == "recover":
            op = dict(op="recover", actor=actor, p=p, suite=suite, key=key, now=now)
            call = lambda: reg.recover(actor, p, suite, key)
        elif kind == "initiate":
            op = dict(op="initiate", actor=actor, p=p, suite=suite, key=key, now=now)
            call = lambda: reg.initiate(actor, p, suite, key, now)
        elif kind == "cancel":
            op = dict(op="cancel", actor=actor, p=p, now=now)
            call = lambda: reg.cancel(actor, p)
        else:
            op = dict(op="finalize", actor=actor, p=p, now=now)
            call = lambda: reg.finalize(actor, p, now)
        before = reg.snapshot()
        try:
            call(); out = "ok"
        except Err as e:
            out = e.code
            assert reg.snapshot() == before, "rejected op changed state: " + str(op)
        assert reg.pq_sound(), "legacy-key rule broken"
        ops.append(op); outs.append(out)
    state = {"accounts": {str(p): dict(a) for p, a in sorted(reg.acct.items())},
             "pending": {str(p): v for p, v in sorted(reg.pending.items())}}
    return {"seed": seed, "ops": ops, "outcomes": outs, "final": state}


# --- ThresholdAuth.lean ---
def toy_verify(suite, key, msg, sig):
    return sig == (key * 7 + msg + suite) % 101


def permits(status, allow_deprecated):
    p = STATUS_PERMITS[status]
    return allow_deprecated if p is None else p


def threshold_accepts(keys, k, statuses, allow_dep, msg, sigs):
    if not (0 < k): return False
    count = 0
    for i, (suite, key) in enumerate(keys):
        if not permits(statuses[suite], allow_dep): continue
        if any(j == i and toy_verify(suite, key, msg, s) for j, s in sigs):
            count += 1
    return k <= count


def threshold_cases(seed, n):
    rnd = random.Random(seed)
    statuses = {1: "deprecated", 2: "active", 0x0101: "active", 3: "proposed", 4: "disabled"}
    cases = []
    for _ in range(n):
        keys = [[rnd.choice(list(statuses)), rnd.randrange(5)] for _ in range(rnd.randrange(0, 6))]
        k = rnd.randrange(0, 5)
        msg = rnd.randrange(50)
        allow = rnd.random() < 0.5
        sigs = []
        for _ in range(rnd.randrange(0, 8)):
            j = rnd.randrange(0, 7)
            if j < len(keys) and rnd.random() < 0.7:
                suite, key = keys[j]
                s = (key * 7 + msg + suite) % 101
            else:
                s = rnd.randrange(101)
            sigs.append([j, s])
        exp = threshold_accepts(keys, k, statuses, allow, msg, sigs)
        # duplicating the signature list never changes the decision
        assert threshold_accepts(keys, k, statuses, allow, msg, sigs + sigs) == exp
        # a lower positive threshold is never harder
        if exp and k > 1:
            assert threshold_accepts(keys, k - 1, statuses, allow, msg, sigs)
        cases.append(dict(keys=keys, k=k, msg=msg, allow_deprecated=allow, sigs=sigs, accepts=exp))
    return {"statuses": {str(s): v for s, v in statuses.items()}, "cases": cases}


def main():
    base = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    traces = [run_trace(s, 1200) for s in (11, 22, 33)]
    # coverage: every outcome class occurs
    seen = {o for t in traces for o in t["outcomes"]}
    need = {"ok", "alreadyRegistered", "unknownAccount", "notAuthorized", "revoked", "frozen", "pqDowngrade",
            "noRecovery", "alreadyPending", "noPending", "tooEarly", "rejected:pqDowngrade"}
    missing = need - seen
    assert not missing, missing
    th = threshold_cases(77, 1500)
    assert any(c["accepts"] for c in th["cases"]) and any(not c["accepts"] for c in th["cases"])
    out = {"format": "SIRM key registry reference traces v0", "delay": DELAY, "pq_suites": sorted(PQ),
           "traces": traces, "threshold": th}
    path = os.path.join(base, "engineering/ledger_core/results/key_registry_trace_v0.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=1, sort_keys=True); f.write("\n")
    print("OUTCOMES_SEEN=%d" % len(seen))
    print("TRACE_OPS=%d" % sum(len(t["ops"]) for t in traces))
    print("THRESHOLD_CASES=%d ACCEPTED=%d" % (len(th["cases"]), sum(c["accepts"] for c in th["cases"])))
    print("RESULT_JSON=engineering/ledger_core/results/key_registry_trace_v0.json")


if __name__ == "__main__":
    main()
