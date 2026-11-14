#!/usr/bin/env python3
"""Independent Python reference for SIRM.EscrowAccounting holdings/record semantics.

Many short seeded episodes (a terminal record never reopens, so one long trace is
not possible): each episode has a random vault account and a random mix of
issue/open/release/cancel. Outcome codes: o ok, n not ready, p not pending,
v vault is a party, z zero amount, u unknown account/asset, i insufficient funds.
Python integers are unbounded, as Lean Nat/Int.
"""
import json, random, sys
from pathlib import Path

ACCOUNTS, ASSETS = 4, 2

def episode(rnd):
    vault = rnd.randrange(ACCOUNTS)
    bal = {(a, s): 0 for a in range(ACCOUNTS) for s in range(ASSETS)}
    rec = None  # (dep, ben, asset, amount, phase)
    phase = "ready"
    ops, out = [], []
    for _ in range(rnd.randrange(7, 14)):
        k = "issue" if _ < 3 else rnd.choice(["open", "open", "release", "cancel"])
        if k == "issue":
            a, s, amt = rnd.choice([x for x in range(ACCOUNTS) if x != vault]), rnd.randrange(ASSETS), rnd.choice([0, 5, rnd.randrange(50, 300)])
            ops.append(["issue", a, s, str(amt)]); bal[(a, s)] += amt; out.append("o")
        elif k == "open":
            def pick():
                r = rnd.random()
                if r < 0.85: return rnd.choice([x for x in range(ACCOUNTS) if x != vault])
                return rnd.randrange(ACCOUNTS) if r < 0.95 else ACCOUNTS + 1
            dep, ben = pick(), pick()
            s = rnd.choice([0, 0, 1, ASSETS + 1]) if rnd.random() < 0.1 else rnd.randrange(ASSETS)
            amt = rnd.choice([0, 1, rnd.randrange(1, 100), rnd.randrange(1, 300)])
            ops.append(["open", dep, ben, s, str(amt)])
            if phase != "ready": out.append("n")
            elif vault in (dep, ben): out.append("v")
            elif amt == 0: out.append("z")
            elif ben >= ACCOUNTS or dep >= ACCOUNTS or s >= ASSETS: out.append("u")
            elif amt > bal[(dep, s)]: out.append("i")
            else:
                bal[(dep, s)] -= amt; bal[(vault, s)] += amt
                rec = (dep, ben, s, amt); phase = "pending"; out.append("o")
        else:
            ops.append([k])
            if phase != "pending": out.append("p")
            else:
                dep, ben, s, amt = rec
                to = ben if k == "release" else dep
                bal[(vault, s)] -= amt; bal[(to, s)] += amt
                phase = "released" if k == "release" else "cancelled"; out.append("o")
        # EscrowFinancialInvariant: vault holds exactly the amount of the escrow asset
        # while pending and nothing otherwise (the escrow machine never issues to the vault).
        for s_ in range(ASSETS):
            want = rec[3] if phase == "pending" and s_ == rec[2] else 0
            assert bal[(vault, s_)] == want
        assert all(v >= 0 for v in bal.values())
    return {"vault": vault, "ops": ops, "outcomes": "".join(out), "phase": phase,
            "final": [[str(bal[(a, s)]) for s in range(ASSETS)] for a in range(ACCOUNTS)]}

def main():
    rnd = random.Random(20261114)
    eps = [episode(rnd) for _ in range(1500)]
    path = Path(sys.argv[1] if len(sys.argv) > 1 else "engineering/ledger_core/results/escrow_trace_v0.json")
    doc = {"format": "SIRM escrow accounting reference trace v0", "accounts": ACCOUNTS, "assets": ASSETS, "episodes": eps}
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(doc, sort_keys=True, separators=(",", ":")) + "\n")
    allo = "".join(e["outcomes"] for e in eps)
    print("EPISODES=%d " % len(eps) + " ".join(f"{c}={allo.count(c)}" for c in "onpvzui"))
    print("PHASES=" + str({p: sum(e["phase"] == p for e in eps) for p in ("ready", "pending", "released", "cancelled")}))
    print("RESULT_JSON=" + str(path))

if __name__ == "__main__":
    main()
