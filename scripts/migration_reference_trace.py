#!/usr/bin/env python3
"""Independent Python reference for SIRM.AssetMigration / AuthorizedAssetMigration /
ReplayProtectedAssetMigration (holdings level).

One migration stream = one rate (numerator/denominator target-per-source base units),
one source holder, one recipient, a source and a destination asset. A migration burns
`amount` source units from the source holder, issues `released` target units to the
recipient, and advances the exact dust accumulator:
    acc = dust + amount*num;  released = acc // den;  dust' = acc % den
    total_source += amount;  total_target += released
    invariant: total_source*num == total_target*den + dust,  dust < den.
A request carries (principal, nonce, amount); the nonce must equal that principal's next
nonce. Python integers are unbounded (as Lean Nat); the Rust u128 port rejects any step in
which a quantity would exceed u128 (code v), an explicit extension; the random episodes
use small values, hand-built episodes exercise the boundary.
Outcome codes: o ok, m nonce mismatch, z zero amount, i insufficient source funds,
v u128 overflow (rejected without writes).
"""
import json, random, sys
from pathlib import Path

ACCOUNTS, ASSETS, PRINCIPALS = 4, 2, 3
MAX = 2**128 - 1

class Mig:
    def __init__(self, num, den, holder, recipient):
        self.num, self.den, self.holder, self.rcp = num, den, holder, recipient
        self.bal = {(a, s): 0 for a in range(ACCOUNTS) for s in range(ASSETS)}
        self.minted, self.burned = [0, 0], [0, 0]
        self.tsrc = self.ttgt = self.dust = 0
        self.nonce = [0] * PRINCIPALS

    def issue(self, a, s, amt):
        if any(x > MAX for x in (self.bal[(a, s)] + amt, self.minted[s] + amt)):
            return "v"
        self.bal[(a, s)] += amt; self.minted[s] += amt
        return "o"

    def migrate(self, p, nonce, amt):
        if nonce != self.nonce[p]: return "m"
        if amt == 0: return "z"
        if amt > self.bal[(self.holder, 0)]: return "i"
        prod = amt * self.num
        acc = self.dust + prod
        rel = acc // self.den
        new_src, new_tgt = self.tsrc + amt, self.ttgt + rel
        if any(x > MAX for x in (prod, acc, new_src, new_tgt, self.bal[(self.rcp, 1)] + rel, self.minted[1] + rel)):
            return "v"
        self.bal[(self.holder, 0)] -= amt; self.burned[0] += amt
        self.bal[(self.rcp, 1)] += rel; self.minted[1] += rel
        self.tsrc, self.ttgt, self.dust = new_src, new_tgt, acc % self.den
        self.nonce[p] += 1
        return "o"

    def check(self):
        assert self.tsrc * self.num == self.ttgt * self.den + self.dust and self.dust < self.den
        assert self.tsrc == self.burned[0] and all(v >= 0 for v in self.bal.values())
        for s in range(ASSETS):
            assert self.minted[s] == self.burned[s] + sum(self.bal[(a, s)] for a in range(ACCOUNTS))

def run(num, den, holder, recipient, ops):
    m, out = Mig(num, den, holder, recipient), []
    for op in ops:
        a = [int(x) for x in op[1:]]
        out.append(m.issue(a[0], a[1], a[2]) if op[0] == "issue" else m.migrate(*a))
        m.check()
    return {"num": str(num), "den": str(den), "holder": holder, "recipient": recipient,
            "ops": [[op[0]] + [str(x) for x in op[1:]] for op in ops], "outcomes": "".join(out),
            "final": {"balances": [[str(m.bal[(a, s)]) for s in range(ASSETS)] for a in range(ACCOUNTS)],
                      "total_source": str(m.tsrc), "total_target": str(m.ttgt), "dust": str(m.dust),
                      "minted": [str(x) for x in m.minted], "burned": [str(x) for x in m.burned],
                      "nonces": m.nonce}}

def random_episode(rnd):
    num = rnd.choice([1, 1, 2, 3, 7, 100, 997])
    den = rnd.choice([1, 2, 3, 10, 1000, 7919])
    holder, recipient = rnd.randrange(ACCOUNTS), rnd.randrange(ACCOUNTS)
    nonces, ops = [0] * PRINCIPALS, []
    for step in range(rnd.randrange(10, 30)):
        if step < 2 or rnd.random() < 0.15:
            ops.append(["issue", holder, 0, rnd.randrange(0, 5000)])
        else:
            p = rnd.randrange(PRINCIPALS)
            n = nonces[p] if rnd.random() < 0.88 else rnd.randrange(0, 6)
            amt = rnd.choice([0, 1, rnd.randrange(1, 50), rnd.randrange(1, 3000)])
            ops.append(["migrate", p, n, amt])
            if n == nonces[p] and amt > 0:
                nonces[p] += 1  # may be wrong if the migration was rejected; harmless, the oracle decides
    return run(num, den, holder, recipient, ops)

def special_episodes():
    S = []
    # source-side product overflow
    S.append(run(3, 2, 0, 1, [["issue", 0, 0, MAX], ["migrate", 0, 0, MAX], ["migrate", 0, 0, 1000]]))
    # destination minted overflow at the boundary: rate 1/1, recipient supply near MAX
    S.append(run(1, 1, 0, 1, [["issue", 2, 1, MAX - 5], ["issue", 0, 0, 10], ["migrate", 0, 0, 10],
                              ["migrate", 0, 0, 5], ["migrate", 1, 0, 1], ["issue", 0, 0, 3],
                              ["migrate", 0, 1, 3], ["migrate", 0, 1, 1]]))
    # max value, identity rate: exact round trip of the full supply
    S.append(run(1, 1, 0, 1, [["issue", 0, 0, MAX], ["migrate", 0, 0, MAX]]))
    # dust accumulation: 1 source unit at 1/3 releases one target unit every third migration
    S.append(run(1, 3, 0, 1, [["issue", 0, 0, 100]] + [["migrate", 0, i, 1] for i in range(9)]))
    # huge denominator keeps everything as dust
    S.append(run(1, MAX, 0, 1, [["issue", 0, 0, 1000], ["migrate", 0, 0, 1000], ["migrate", 0, 1, 1000]]))
    return S

def main():
    rnd = random.Random(20261114)
    eps = special_episodes() + [random_episode(rnd) for _ in range(1500)]
    path = Path(sys.argv[1] if len(sys.argv) > 1 else "engineering/ledger_core/results/migration_trace_v0.json")
    doc = {"format": "SIRM asset migration reference trace v0", "accounts": ACCOUNTS, "assets": ASSETS,
           "principals": PRINCIPALS, "episodes": eps}
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(doc, sort_keys=True, separators=(",", ":")) + "\n")
    allo = "".join(e["outcomes"] for e in eps)
    print("EPISODES=%d " % len(eps) + " ".join(f"{c}={allo.count(c)}" for c in "omziv"))
    print("WITH_DUST=%d" % sum(e["final"]["dust"] != "0" for e in eps))
    print("RESULT_JSON=" + str(path))

if __name__ == "__main__":
    main()
