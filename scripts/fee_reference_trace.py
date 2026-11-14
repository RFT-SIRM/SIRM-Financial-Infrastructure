#!/usr/bin/env python3
"""Independent Python reference for SIRM.FeeAccounting holdings semantics.

Seeded trace of issue/fee operations (roles may coincide, fee may exceed gross,
payer may be unfunded) with expected outcomes and checkpoints, for differential
testing of `rust/sirm-codec/src/fees.rs`. Python integers are unbounded, as Lean Nat/Int.
Outcome codes: o accepted, e fee exceeds gross, i insufficient funds.
"""
import json, random, sys
from pathlib import Path

ACCOUNTS, ASSETS = 4, 2

def run(seed=20261114, n=4000):
    rnd = random.Random(seed)
    bal = {(a, s): 0 for a in range(ACCOUNTS) for s in range(ASSETS)}
    ops, outcomes, cps = [], [], []
    for i in range(n):
        asset = rnd.randrange(ASSETS)
        if rnd.random() < 0.12:
            a, amt = rnd.randrange(ACCOUNTS), rnd.choice([0, 1, rnd.randrange(1, 500), rnd.randrange(1, 5000)])
            ops.append(["issue", a, asset, str(amt)]); bal[(a, asset)] += amt; outcomes.append("o")
        else:
            p, b, c = (rnd.randrange(ACCOUNTS) for _ in range(3))
            gross = rnd.choice([0, 1, rnd.randrange(1, 100), rnd.randrange(1, 3000)])
            fee = rnd.choice([0, 1, rnd.randrange(0, gross + 1), rnd.randrange(0, gross + 1), gross, gross + 1, rnd.randrange(0, 4000)])
            ops.append(["fee", p, b, c, asset, str(gross), str(fee)])
            before = dict(bal)
            if fee > gross:
                outcomes.append("e")
            elif gross > bal[(p, asset)]:
                outcomes.append("i")
            else:
                net = gross - fee
                if p != b: bal[(p, asset)] -= net; bal[(b, asset)] += net
                if p != c: bal[(p, asset)] -= fee; bal[(c, asset)] += fee
                outcomes.append("o")
                assert net + fee == gross
            if outcomes[-1] != "o":
                assert bal == before
            # conservation: per-asset total unchanged by a fee transfer
            for s in range(ASSETS):
                assert sum(bal[(a, s)] for a in range(ACCOUNTS)) == sum(before[(a, s)] for a in range(ACCOUNTS)) or ops[-1][0] == "issue"
        assert all(v >= 0 for v in bal.values())
        if (i + 1) % 250 == 0:
            cps.append({"after": i + 1, "balances": [[str(bal[(a, s)]) for s in range(ASSETS)] for a in range(ACCOUNTS)]})
    return {"seed": seed, "accounts": ACCOUNTS, "assets": ASSETS, "ops": ops,
            "outcomes": "".join(outcomes), "checkpoints": cps,
            "final": [[str(bal[(a, s)]) for s in range(ASSETS)] for a in range(ACCOUNTS)]}

def main():
    out = Path(sys.argv[1] if len(sys.argv) > 1 else "engineering/ledger_core/results/fee_trace_v0.json")
    doc = {"format": "SIRM fee accounting reference trace v0", "trace": run()}
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(doc, sort_keys=True, separators=(",", ":")) + "\n")
    o = doc["trace"]["outcomes"]
    print(f"OPS={len(o)} OK={o.count('o')} FEE_EXCEEDS={o.count('e')} INSUFFICIENT={o.count('i')}")
    print("RESULT_JSON=" + str(out))

if __name__ == "__main__":
    main()
