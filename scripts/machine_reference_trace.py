#!/usr/bin/env python3
"""Independent Python reference for the integrated transaction processor.

Composes the Lean semantics of SIRM.FinancialTransactionEnvelope and
SIRM.FinancialTransactionDenials over holdings + static authorization:
 1. receipt/denial lookup first (shared request-ID namespace): same request -> replay,
    different request -> conflict;
 2. nonce must equal the principal's next nonce (stale/future are not cached);
 3. authorization failure -> cached denial (no nonce consumed, no financial effect);
 4. authorized but unfunded non-self transfer or burn -> cached funds denial;
 5. otherwise the operation, nonce increment and receipt commit together.
The general ledger of the Lean machine is not modelled here (holdings only).
Output feeds `rust/sirm-codec/tests/machine_trace.rs`.
"""
import json, random, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from ledger_reference_trace import Ledger, ACCOUNTS, ASSETS
from auth_reference_trace import PRINCIPALS, make_registry

REASON = {("transfer", "auth"): "ta", ("issue", "auth"): "ia", ("burn", "auth"): "ba",
          ("transfer", "funds"): "tf", ("burn", "funds"): "bf"}

def trace(seed=20261115, n=4000):
    rnd = random.Random(seed)
    grants, control, table = make_registry(rnd)
    controls = {tuple(c) for c in control}
    led = Ledger()
    nxt = {p: 0 for p in range(PRINCIPALS)}
    cache = {}                      # id -> (request tuple, stored token)
    issued = []                     # previously used (id, request) for replays/conflicts
    reqs, tokens = [], []
    usable = [k for k in table if (k[0], k[2]) in controls]
    next_id = 1
    for _ in range(n):
        roll = rnd.random()
        if issued and roll < 0.18:                        # exact replay of an earlier request
            rid, req = rnd.choice(issued)
        elif issued and roll < 0.26:                      # same id, different payload
            rid, req = rnd.choice(issued)
            req = (req[0], req[1], req[2], req[3], req[4], req[5], req[6] + 1)
        else:
            if usable and rnd.random() < 0.8:
                p, kind, a, b, asset = rnd.choice(usable)
                lim = table[(p, kind, a, b, asset)]
                amt = rnd.choice([0, 1, rnd.randrange(0, lim + 1), rnd.randrange(0, lim + 1), lim, lim + 1])
            else:
                p = rnd.randrange(PRINCIPALS); kind = rnd.choice(["transfer", "transfer", "issue", "burn"])
                asset = rnd.randrange(ASSETS); amt = rnd.choice([0, 1, rnd.randrange(1, 800)])
                a = rnd.randrange(ACCOUNTS); b = rnd.randrange(ACCOUNTS) if kind != "burn" else None
            r2 = rnd.random()
            nonce = nxt[p] if r2 < 0.75 else (max(0, nxt[p] - 1 - rnd.randrange(2)) if r2 < 0.87 else nxt[p] + 1 + rnd.randrange(3))
            rid = next_id; next_id += 1
            req = (p, nonce, kind, a, b, asset, amt)
        reqs.append([rid, req[0], req[1], req[2], req[3], req[4], req[5], str(req[6])])
        p, nonce, kind, a, b, asset, amt = req
        if rid in cache:
            prior_req, stored = cache[rid]
            tokens.append("R" + stored if prior_req == req else "C")
            continue
        if nonce < nxt[p]:
            tokens.append("S"); continue
        if nonce > nxt[p]:
            tokens.append("F"); continue
        authorized = (p, a) in controls and (p, kind, a, b, asset) in table and amt <= table[(p, kind, a, b, asset)]
        if not authorized:
            stored = f"N{REASON[(kind, 'auth')]}@{nxt[p]}"
            cache[rid] = (req, stored); issued.append((rid, req)); tokens.append(stored[0:0] + stored); continue
        funds_lacking = (kind == "transfer" and a != b and amt > led.bal[(a, asset)]) or \
                        (kind == "burn" and amt > led.bal[(a, asset)])
        if funds_lacking:
            stored = f"N{REASON[(kind, 'funds')]}@{nxt[p]}"
            cache[rid] = (req, stored); issued.append((rid, req)); tokens.append(stored); continue
        r = led.transfer(a, b, asset, amt) if kind == "transfer" else led.issue(b, asset, amt) if kind == "issue" else led.burn(a, asset, amt)
        assert r == "ok" and led.invariant()
        stored = f"A{nonce}>{nonce + 1}"
        nxt[p] = nonce + 1
        cache[rid] = (req, stored); issued.append((rid, req)); tokens.append(stored)
    return {"seed": seed, "principals": PRINCIPALS, "accounts": ACCOUNTS, "assets": ASSETS,
            "grants": grants, "control": control, "requests": reqs, "tokens": tokens,
            "final": led.state(), "final_nonces": [nxt[p] for p in range(PRINCIPALS)], "receipts": len(cache)}

def main():
    out = Path(sys.argv[1] if len(sys.argv) > 1 else "engineering/ledger_core/results/machine_trace_v0.json")
    t = trace()
    out.write_text(json.dumps({"format": "SIRM integrated processor reference trace v0", "trace": t}, sort_keys=True, separators=(",", ":")) + "\n")
    from collections import Counter
    c = Counter(tok[:1] if tok[0] != "N" else "N" for tok in t["tokens"])
    c2 = Counter(tok[1:3] for tok in t["tokens"] if tok[0] == "N")
    print("REQUESTS=%d %s DENIALS=%s RECEIPTS=%d" % (len(t["requests"]), dict(sorted(c.items())), dict(sorted(c2.items())), t["receipts"]))
    print("RESULT_JSON=" + str(out))

if __name__ == "__main__":
    main()
