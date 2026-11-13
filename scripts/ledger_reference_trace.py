#!/usr/bin/env python3
"""Independent Python reference for SIRM.FinancialCore / SIRM.Holdings semantics.

Generates a seeded operation trace with expected outcomes and state checkpoints,
plus founder-allocation vectors, for differential testing of the Rust ledger
(`rust/sirm-codec/src/ledger.rs`). Python integers are unbounded, as Lean `Nat`/`Int`.
"""
import json, random, sys
from pathlib import Path

PPM_SCALE, FOUNDER_PPM = 1_000_000, 13_090
U128_MAX = 2**128 - 1
ACCOUNTS, ASSETS = 4, 2

def founder_allocation(total):
    return total * FOUNDER_PPM // PPM_SCALE

class Ledger:
    def __init__(self):
        self.bal = {(a, s): 0 for a in range(ACCOUNTS) for s in range(ASSETS)}
        self.sup = {s: [0, 0, 0] for s in range(ASSETS)}  # minted, burned, outstanding
    def transfer(self, src, dst, asset, amt):
        if src != dst and amt > self.bal[(src, asset)]:
            return "insufficient"
        if src != dst:
            self.bal[(src, asset)] -= amt
            self.bal[(dst, asset)] += amt
        return "ok"
    def issue(self, rcp, asset, amt):
        self.bal[(rcp, asset)] += amt
        m = self.sup[asset]; m[0] += amt; m[2] += amt
        return "ok"
    def burn(self, holder, asset, amt):
        if amt > self.bal[(holder, asset)]:
            return "insufficient"
        self.bal[(holder, asset)] -= amt
        m = self.sup[asset]; m[1] += amt; m[2] -= amt
        return "ok"
    def invariant(self):
        for s in range(ASSETS):
            mi, bu, out = self.sup[s]
            if mi != bu + out or sum(self.bal[(a, s)] for a in range(ACCOUNTS)) != out:
                return False
        return all(v >= 0 for v in self.bal.values())
    def state(self):
        return {"balances": [[str(self.bal[(a, s)]) for s in range(ASSETS)] for a in range(ACCOUNTS)],
                "supply": [[str(x) for x in self.sup[s]] for s in range(ASSETS)]}

def trace(seed=20261113, n=3000):
    rnd = random.Random(seed)
    led, ops, outcomes, checkpoints = Ledger(), [], [], []
    for i in range(n):
        kind = rnd.choice(["transfer", "transfer", "issue", "burn"])
        asset = rnd.randrange(ASSETS)
        amt = rnd.choice([0, 1, rnd.randrange(1, 50), rnd.randrange(1, 5000)])
        if kind == "transfer":
            a, b = rnd.randrange(ACCOUNTS), rnd.randrange(ACCOUNTS)
            ops.append(["transfer", a, b, asset, str(amt)]); r = led.transfer(a, b, asset, amt)
        elif kind == "issue":
            a = rnd.randrange(ACCOUNTS)
            ops.append(["issue", a, asset, str(amt)]); r = led.issue(a, asset, amt)
        else:
            a = rnd.randrange(ACCOUNTS)
            ops.append(["burn", a, asset, str(amt)]); r = led.burn(a, asset, amt)
        assert led.invariant()
        outcomes.append("o" if r == "ok" else "r")
        if (i + 1) % 250 == 0:
            checkpoints.append({"after": i + 1, **led.state()})
    return {"seed": seed, "accounts": ACCOUNTS, "assets": ASSETS, "ops": ops,
            "outcomes": "".join(outcomes), "checkpoints": checkpoints, "final": led.state()}

def founder_vectors():
    cap = U128_MAX // FOUNDER_PPM
    totals = [0, 1, 76, 99, 100, 7_647, 7_648, 10**6, 10**9, 10**18, 10**24,
              cap - 1, cap, cap + 1, U128_MAX]
    out = []
    for t in totals:
        fits = t * FOUNDER_PPM <= U128_MAX
        f = founder_allocation(t)
        out.append({"total": str(t), "fits_u128": fits, "founder": str(f), "remaining": str(t - f)})
        assert f <= t
    return out

def main():
    out = Path(sys.argv[1] if len(sys.argv) > 1 else "engineering/ledger_core/results/ledger_trace_v0.json")
    doc = {"format": "SIRM ledger core reference trace v0", "trace": trace(), "founder": founder_vectors()}
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(doc, sort_keys=True, separators=(",", ":")) + "\n")
    t = doc["trace"]
    print(f"OPS={len(t['ops'])} ACCEPTED={t['outcomes'].count('o')} REJECTED={t['outcomes'].count('r')} CHECKPOINTS={len(t['checkpoints'])}")
    print(f"FOUNDER_VECTORS={len(doc['founder'])}")
    print("RESULT_JSON=" + str(out))

if __name__ == "__main__":
    main()
