#!/usr/bin/env python3
"""Independent Python reference for SIRM.EscrowDisputes (first-stage dispute intake and
per-ID freeze on top of the time-locked pooled-vault escrow).

Rules mirrored from Lean: a dispute may be raised only for an existing pending record
strictly before its deadline, with no earlier filing, by the depositor or beneficiary;
it records (principal, claimant, filed_at = now) permanently. A disputed ID rejects
release, cancel and expire (even after the deadline). Other IDs and the clock are
unaffected. Time-lock rules as in timelock_reference_trace.py.
Outcome codes: o ok, k id used, w unknown id / no record, n not pending, d deadline
passed, e deadline not reached, v vault is party, z zero amount, u unknown account/asset,
i insufficient funds, t time not forward, x disputed (frozen), a already filed,
c claimant is neither depositor nor beneficiary.
"""
import json, random, sys
from pathlib import Path

ACCOUNTS, ASSETS, IDS = 4, 2, 3

class Esc:
    def __init__(self, vault, deadlines, now):
        self.vault, self.dl, self.now = vault, deadlines, now
        self.bal = {(a, s): 0 for a in range(ACCOUNTS) for s in range(ASSETS)}
        self.recs, self.files = {}, {}

    def open(self, i, dep, ben, s, amt):
        if i in self.files: return "x"
        if i >= IDS: return "w"
        if i in self.recs: return "k"
        if self.now >= self.dl[i]: return "d"
        if self.vault in (dep, ben): return "v"
        if amt == 0: return "z"
        if dep >= ACCOUNTS or ben >= ACCOUNTS or s >= ASSETS: return "u"
        if amt > self.bal[(dep, s)]: return "i"
        self.bal[(dep, s)] -= amt; self.bal[(self.vault, s)] += amt
        self.recs[i] = [dep, ben, s, amt, "pending"]
        return "o"

    def settle(self, k, i):
        if i in self.files: return "x"
        if i >= IDS or i not in self.recs: return "w"
        r = self.recs[i]
        if r[4] != "pending": return "n"
        if k == "expire" and self.now < self.dl[i]: return "e"
        if k != "expire" and self.now >= self.dl[i]: return "d"
        dep, ben, s, amt, _ = r
        to = ben if k == "release" else dep
        self.bal[(self.vault, s)] -= amt; self.bal[(to, s)] += amt
        r[4] = {"release": "released", "cancel": "cancelled", "expire": "expired"}[k]
        return "o"

    def advance(self, t):
        if t <= self.now: return "t"
        self.now = t
        return "o"

    def dispute(self, i, principal, claimant):
        if i >= IDS or i not in self.recs: return "w"
        r = self.recs[i]
        if r[4] != "pending": return "n"
        if self.now >= self.dl[i]: return "d"
        if i in self.files: return "a"
        if claimant not in (r[0], r[1]): return "c"
        self.files[i] = [principal, claimant, self.now]
        return "o"

    def check(self):
        for s in range(ASSETS):
            assert self.bal[(self.vault, s)] == sum(r[3] for r in self.recs.values() if r[4] == "pending" and r[2] == s)
        assert all(v >= 0 for v in self.bal.values())
        for i, f in self.files.items():  # filings are permanent and tied to existing records
            assert i in self.recs

def episode(rnd):
    vault = rnd.randrange(ACCOUNTS)
    others = [a for a in range(ACCOUNTS) if a != vault]
    e = Esc(vault, [rnd.randrange(4, 14) for _ in range(IDS)], rnd.randrange(0, 3))
    start = e.now
    ops, out = [], []
    for step in range(rnd.randrange(16, 28)):
        k = "issue" if step < 3 else rnd.choice(["open", "open", "release", "cancel", "expire", "advance", "advance", "dispute", "dispute"])
        if k == "issue":
            a, s, amt = rnd.choice(others), rnd.randrange(ASSETS), rnd.randrange(50, 300)
            ops.append(["issue", a, s, str(amt)]); e.bal[(a, s)] += amt; out.append("o")
        elif k == "open":
            def pick():
                r = rnd.random()
                if r < 0.85: return rnd.choice(others)
                return rnd.randrange(ACCOUNTS) if r < 0.95 else ACCOUNTS + 1
            i = rnd.randrange(IDS + 1) if rnd.random() < 0.05 else rnd.randrange(IDS)
            dep, ben = pick(), pick()
            s = ASSETS + 1 if rnd.random() < 0.04 else rnd.randrange(ASSETS)
            amt = rnd.choice([0, 1, rnd.randrange(1, 100), rnd.randrange(1, 300)])
            ops.append(["open", i, dep, ben, s, str(amt)]); out.append(e.open(i, dep, ben, s, amt))
        elif k == "advance":
            t = e.now + rnd.choice([1, 1, 2, 3]) if rnd.random() < 0.92 else e.now - rnd.randrange(0, 2)
            ops.append(["advance", t]); out.append(e.advance(t))
        elif k == "dispute":
            i = rnd.randrange(IDS + 1) if rnd.random() < 0.05 else rnd.randrange(IDS)
            r = e.recs.get(i)
            claimant = rnd.choice([r[0], r[1]]) if r and rnd.random() < 0.85 else rnd.randrange(ACCOUNTS)
            p = rnd.randrange(3)
            ops.append(["dispute", i, p, claimant]); out.append(e.dispute(i, p, claimant))
        else:
            i = rnd.randrange(IDS + 1) if rnd.random() < 0.05 else rnd.randrange(IDS)
            ops.append([k, i]); out.append(e.settle(k, i))
        e.check()
    return {"vault": vault, "deadlines": e.dl, "start": start, "ops": ops, "outcomes": "".join(out),
            "now": e.now, "phases": [e.recs[i][4] if i in e.recs else "none" for i in range(IDS)],
            "filings": [e.files.get(i) for i in range(IDS)],
            "final": [[str(e.bal[(a, s)]) for s in range(ASSETS)] for a in range(ACCOUNTS)]}

def main():
    rnd = random.Random(20261114)
    eps = [episode(rnd) for _ in range(1500)]
    path = Path(sys.argv[1] if len(sys.argv) > 1 else "engineering/ledger_core/results/dispute_trace_v0.json")
    doc = {"format": "SIRM escrow dispute freeze reference trace v0", "accounts": ACCOUNTS, "assets": ASSETS,
           "ids": IDS, "episodes": eps}
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(doc, sort_keys=True, separators=(",", ":")) + "\n")
    allo = "".join(x["outcomes"] for x in eps)
    print("EPISODES=%d " % len(eps) + " ".join(f"{c}={allo.count(c)}" for c in "okwndevzuitxac"))
    print("FILED=%d FROZEN_PENDING=%d" % (sum(f is not None for x in eps for f in x["filings"]),
          sum(1 for x in eps for p, f in zip(x["phases"], x["filings"]) if f is not None and p == "pending")))
    print("RESULT_JSON=" + str(path))

if __name__ == "__main__":
    main()
