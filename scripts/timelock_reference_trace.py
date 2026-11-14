#!/usr/bin/env python3
"""Independent Python reference for SIRM.EscrowTimeLocks (multi-record escrow registry
with a pooled vault, per-ID deadlines and a monotone discrete clock).

Seeded episodes of issue/open/release/cancel/expire/advance. Rules mirrored from Lean:
open: fresh ID, now < deadline, vault is neither party, amount > 0, funded;
release/cancel: pending and now < deadline; expire: pending and deadline <= now,
refund to depositor, phase `expired`; advance: strictly forward.
Outcome codes: o ok, k id already used, w unknown escrow id (outside the schedule, or no record for
release/cancel/expire), n not pending,
d deadline passed, e deadline not yet reached, v vault is a party, z zero amount,
u unknown account/asset, i insufficient funds, t time not strictly forward.
"""
import json, random, sys
from pathlib import Path

ACCOUNTS, ASSETS, IDS = 4, 2, 3

def episode(rnd):
    vault = rnd.randrange(ACCOUNTS)
    others = [a for a in range(ACCOUNTS) if a != vault]
    deadlines = [rnd.randrange(3, 12) for _ in range(IDS)]
    now = rnd.randrange(0, 3)
    start = now
    bal = {(a, s): 0 for a in range(ACCOUNTS) for s in range(ASSETS)}
    recs = {}  # id -> [dep, ben, asset, amt, phase]
    ops, out = [], []
    for step in range(rnd.randrange(14, 26)):
        k = "issue" if step < 3 else rnd.choice(["open", "open", "release", "cancel", "expire", "advance", "advance"])
        if k == "issue":
            a, s, amt = rnd.choice(others), rnd.randrange(ASSETS), rnd.randrange(50, 300)
            ops.append(["issue", a, s, str(amt)]); bal[(a, s)] += amt; out.append("o")
        elif k == "open":
            def pick():
                r = rnd.random()
                if r < 0.85: return rnd.choice(others)
                return rnd.randrange(ACCOUNTS) if r < 0.95 else ACCOUNTS + 1
            i = rnd.choice([0, 1, 2, 2, IDS + 1]) if rnd.random() < 0.1 else rnd.randrange(IDS)
            dep, ben = pick(), pick()
            s = ASSETS + 1 if rnd.random() < 0.04 else rnd.randrange(ASSETS)
            amt = rnd.choice([0, 1, rnd.randrange(1, 100), rnd.randrange(1, 300)])
            ops.append(["open", i, dep, ben, s, str(amt)])
            if i >= IDS: out.append("w")
            elif i in recs: out.append("k")
            elif now >= deadlines[i]: out.append("d")
            elif vault in (dep, ben): out.append("v")
            elif amt == 0: out.append("z")
            elif dep >= ACCOUNTS or ben >= ACCOUNTS or s >= ASSETS: out.append("u")
            elif amt > bal[(dep, s)]: out.append("i")
            else:
                bal[(dep, s)] -= amt; bal[(vault, s)] += amt
                recs[i] = [dep, ben, s, amt, "pending"]; out.append("o")
        elif k == "advance":
            t = now + rnd.choice([1, 1, 2, 3, 5]) if rnd.random() < 0.9 else now - rnd.randrange(0, 2)
            ops.append(["advance", t])
            if t <= now: out.append("t")
            else: now = t; out.append("o")
        else:
            i = rnd.randrange(IDS + 1) if rnd.random() < 0.05 else rnd.randrange(IDS)
            ops.append([k, i])
            if i >= IDS: out.append("w")
            elif i not in recs or recs[i][4] != "pending": out.append("n" if i in recs else "w")
            elif k == "expire" and now < deadlines[i]: out.append("e")
            elif k != "expire" and now >= deadlines[i]: out.append("d")
            else:
                dep, ben, s, amt, _ = recs[i]
                to = ben if k == "release" else dep
                bal[(vault, s)] -= amt; bal[(to, s)] += amt
                recs[i][4] = {"release": "released", "cancel": "cancelled", "expire": "expired"}[k]
                out.append("o")
        # pooled-reserve invariant: vault holds exactly the sum of pending amounts per asset
        for s_ in range(ASSETS):
            assert bal[(vault, s_)] == sum(r[3] for r in recs.values() if r[4] == "pending" and r[2] == s_)
        assert all(v >= 0 for v in bal.values())
    return {"vault": vault, "deadlines": deadlines, "start": start, "ops": ops,
            "outcomes": "".join(out), "now": now,
            "phases": [recs[i][4] if i in recs else "none" for i in range(IDS)],
            "final": [[str(bal[(a, s)]) for s in range(ASSETS)] for a in range(ACCOUNTS)]}

def main():
    rnd = random.Random(20261114)
    eps = [episode(rnd) for _ in range(1500)]
    path = Path(sys.argv[1] if len(sys.argv) > 1 else "engineering/ledger_core/results/timelock_trace_v0.json")
    doc = {"format": "SIRM escrow time-lock reference trace v0", "accounts": ACCOUNTS, "assets": ASSETS,
           "ids": IDS, "episodes": eps}
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(doc, sort_keys=True, separators=(",", ":")) + "\n")
    allo = "".join(e["outcomes"] for e in eps)
    print("EPISODES=%d " % len(eps) + " ".join(f"{c}={allo.count(c)}" for c in "okwndevzuit"))
    ph = {}
    for e in eps:
        for p in e["phases"]: ph[p] = ph.get(p, 0) + 1
    print("PHASES=" + str(dict(sorted(ph.items()))))
    print("RESULT_JSON=" + str(path))

if __name__ == "__main__":
    main()
