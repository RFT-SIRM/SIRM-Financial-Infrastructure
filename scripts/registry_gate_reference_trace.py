#!/usr/bin/env python3
"""Independent Python reference for SIRM.TypedRegistry and the issuance gate of
SIRM.RegistryAwareFinancialMachine.

Semantics (from the Lean definitions): account/asset metadata is total over finite ID
domains; an asset's issuer is an account and must be on the asset's network; an asset
is issuance-enabled iff the asset is active AND its issuer account is active. The
registry-aware policy equals the base authorization policy for transfer and burn
(unchanged, so frozen/closed accounts and non-active assets do NOT restrict them here),
and for issue it additionally requires issuance-enabled. A denied operation changes
nothing. Base authorization = control of the source/issuer/holder AND an exact grant
whose limit covers the amount (as in auth_reference_trace.py).
Outcome codes: o ok, u denied by the base policy, g denied only by the registry gate,
i insufficient funds. `base_units` vectors check 10**decimals (null if above u128 max).
"""
import json, random, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from ledger_reference_trace import Ledger, ACCOUNTS, ASSETS
from auth_reference_trace import make_registry, PRINCIPALS

CLASSES = ["holder", "treasury", "validatorPool", "ecosystemPool", "communityPool", "unallocatedPool",
           "control", "custody", "reserve", "customerLiability", "equity", "income", "expense", "fee",
           "escrow", "clearing"]
ACC_STATUS = ["active", "frozen", "closed"]
ASSET_STATUS = ["draft", "active", "frozen", "retired"]
MAX = 2**128 - 1

def typed_registry(rnd):
    accounts = [[rnd.choice(CLASSES), rnd.choices(ACC_STATUS, [6, 2, 2])[0], rnd.randrange(3)] for _ in range(ACCOUNTS)]
    assets = []
    for s in range(ASSETS):
        issuer = rnd.randrange(ACCOUNTS)
        assets.append(["T%d" % s, rnd.choice([0, 2, 6, 18]), issuer,
                       rnd.choices(ASSET_STATUS, [1, 6, 2, 1])[0], accounts[issuer][2]])
    return accounts, assets

def enabled(accounts, assets, s):
    return assets[s][3] == "active" and accounts[assets[s][2]][1] == "active"

def episode(seed, n=500):
    rnd = random.Random(seed)
    accounts, assets = typed_registry(rnd)
    grants, control, table = make_registry(rnd)
    controls = {tuple(c) for c in control}
    usable = [k for k in table if (k[0], k[2]) in controls]
    led, ops, out = Ledger(), [], []
    for _ in range(n):
        if usable and rnd.random() < 0.8:
            p, kind, a, b, asset = rnd.choice(usable)
            lim = table[(p, kind, a, b, asset)]
            amt = rnd.choice([0, 1, rnd.randrange(0, lim + 1), lim, lim + 1])
        else:
            p, kind, asset = rnd.randrange(PRINCIPALS), rnd.choice(["transfer", "issue", "issue", "burn"]), rnd.randrange(ASSETS)
            amt, a = rnd.randrange(0, 800), rnd.randrange(ACCOUNTS)
            b = rnd.randrange(ACCOUNTS) if kind != "burn" else None
        ops.append([p, kind, a, b, asset, str(amt)])
        base = (p, a) in controls and (p, kind, a, b, asset) in table and amt <= table[(p, kind, a, b, asset)]
        if not base:
            out.append("u"); continue
        if kind == "issue" and not enabled(accounts, assets, asset):
            out.append("g"); continue
        r = led.transfer(a, b, asset, amt) if kind == "transfer" else led.issue(b, asset, amt) if kind == "issue" else led.burn(a, asset, amt)
        assert led.invariant()
        out.append("o" if r == "ok" else "i")
    return {"seed": seed, "accounts": accounts, "assets": assets, "grants": grants, "control": control,
            "enabled": [enabled(accounts, assets, s) for s in range(ASSETS)],
            "ops": ops, "outcomes": "".join(out), "final": led.state()}

def main():
    eps = [episode(1000 + i) for i in range(24)]
    base_units = {str(d): (str(10**d) if 10**d <= MAX else None) for d in (0, 1, 6, 8, 18, 38, 39, 77)}
    path = Path(sys.argv[1] if len(sys.argv) > 1 else "engineering/ledger_core/results/registry_gate_trace_v0.json")
    doc = {"format": "SIRM typed registry and issuance gate reference trace v0", "accounts": ACCOUNTS,
           "assets": ASSETS, "principals": PRINCIPALS, "base_units": base_units, "episodes": eps}
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(doc, sort_keys=True, separators=(",", ":")) + "\n")
    allo = "".join(e["outcomes"] for e in eps)
    print("EPISODES=%d OPS=%d " % (len(eps), len(allo)) + " ".join(f"{c}={allo.count(c)}" for c in "ougi"))
    print("ENABLED_ASSETS=%d DISABLED_ASSETS=%d" % (sum(x for e in eps for x in e["enabled"]), sum(not x for e in eps for x in e["enabled"])))
    print("RESULT_JSON=" + str(path))

if __name__ == "__main__":
    main()
