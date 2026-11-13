#!/usr/bin/env python3
"""Independent Python reference for SIRM.Authorization / AuthorityRegistry / AccountControl.

Semantics (from the Lean definitions): an operation is authorized iff the acting
principal controls the source/issuer/holder account AND a grant with the exact
(principal, scope, asset) key exists whose single-operation limit is >= the amount.
Authorization is checked first; a failed authorization changes nothing. Transfers
additionally need funds unless source = destination; burns need funds.
Output feeds the Rust differential test (`rust/sirm-codec/tests/auth_trace.rs`).
"""
import json, random, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from ledger_reference_trace import Ledger, ACCOUNTS, ASSETS  # same Lean Holdings semantics

PRINCIPALS = 3
LIMITS = [0, 10, 100, 1000, 5000]

def make_registry(rnd):
    grants, seen = [], {}
    for p in range(PRINCIPALS):
        for asset in range(ASSETS):
            for a in range(ACCOUNTS):
                for kind, targets in (("transfer", range(ACCOUNTS)), ("issue", range(ACCOUNTS)), ("burn", [None])):
                    for b in targets:
                        if rnd.random() < 0.35:
                            key = (p, kind, a, b, asset)
                            seen[key] = rnd.choice(LIMITS)
    grants = [[p, kind, a, b, asset, str(m)] for (p, kind, a, b, asset), m in seen.items()]
    grants.append(list(grants[0]))  # an identical duplicate is allowed by the Lean uniqueness condition
    control = [[p, a] for p in range(PRINCIPALS) for a in range(ACCOUNTS) if rnd.random() < 0.6]
    return grants, control, seen

def trace(seed=20261114, n=3000):
    rnd = random.Random(seed)
    grants, control, table = make_registry(rnd)
    controls = {tuple(c) for c in control}
    led, ops, outcomes = Ledger(), [], []
    # Seed some balances through authorized-free setup is not possible; so issue ops come from the trace itself.
    usable = [k for k in table if (k[0], k[2]) in controls]  # control satisfied: grant can matter
    for _ in range(n):
        if usable and rnd.random() < 0.75:
            p, kind, a, b, asset = rnd.choice(usable)
            lim = table[(p, kind, a, b, asset)]
            amt = rnd.choice([0, 1, rnd.randrange(0, lim + 1), rnd.randrange(0, lim + 1), lim, lim + 1])
        else:
            p = rnd.randrange(PRINCIPALS)
            kind = rnd.choice(["transfer", "transfer", "issue", "burn"])
            asset = rnd.randrange(ASSETS)
            amt = rnd.choice([0, 1, rnd.randrange(1, 50), rnd.randrange(1, 800), rnd.randrange(1, 6000)])
            a = rnd.randrange(ACCOUNTS)
            b = rnd.randrange(ACCOUNTS) if kind != "burn" else None
        ok_auth = (p, a) in controls and (p, kind, a, b, asset) in table and amt <= table[(p, kind, a, b, asset)]
        ops.append([p, kind, a, b, asset, str(amt)])
        if not ok_auth:
            outcomes.append("u"); continue
        if kind == "transfer":
            r = led.transfer(a, b, asset, amt)
        elif kind == "issue":
            r = led.issue(b, asset, amt)
        else:
            r = led.burn(a, asset, amt)
        assert led.invariant()
        outcomes.append("o" if r == "ok" else "i")
    return {"seed": seed, "principals": PRINCIPALS, "accounts": ACCOUNTS, "assets": ASSETS,
            "grants": grants, "control": control, "ops": ops, "outcomes": "".join(outcomes),
            "final": led.state()}

def main():
    out = Path(sys.argv[1] if len(sys.argv) > 1 else "engineering/ledger_core/results/auth_trace_v0.json")
    t = trace()
    out.write_text(json.dumps({"format": "SIRM authorization reference trace v0", "trace": t}, sort_keys=True, separators=(",", ":")) + "\n")
    o = t["outcomes"]
    print(f"OPS={len(t['ops'])} OK={o.count('o')} UNAUTHORIZED={o.count('u')} INSUFFICIENT={o.count('i')} GRANTS={len(t['grants'])}")
    print("RESULT_JSON=" + str(out))

if __name__ == "__main__":
    main()
