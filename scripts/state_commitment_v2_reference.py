#!/usr/bin/env python3
"""Independent reference for state commitment v2 (PROPOSAL, not adopted).

Extends v1 with the request-id cache (receipts and denials), the authorization policy (grants and
account control) and the account/asset registry. See
engineering/canonical_encoding/SPEC_state_commitment_v2.md.
Output: engineering/canonical_encoding/results/state_commitment_v2_vectors.json
"""
import hashlib, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import state_commitment_reference as v0
import state_commitment_v1_reference as v1

H = lambda b: hashlib.sha256(b).digest()
D_STATE = b"SIRM/STC/v2\x00"
D_CACHE = b"SIRM/CAC/v2\x00"
D_POL = b"SIRM/POL/v2\x00"
D_REG = b"SIRM/REG/v2\x00"
OP = {"transfer": 0, "issue": 1, "burn": 2}
REASON = {"ta": 0, "ia": 1, "ba": 2, "tf": 3, "bf": 4}
CLASS = {n: i for i, n in enumerate(
    "holder treasury validatorPool ecosystemPool communityPool unallocatedPool control custody reserve "
    "customerLiability equity income expense fee escrow clearing".split())}
ACCT_STATUS = {"active": 0, "frozen": 1, "closed": 2}
ASSET_STATUS = {"draft": 0, "active": 1, "frozen": 2, "retired": 3}
u32 = lambda x: x.to_bytes(4, "big")
u64 = lambda x: x.to_bytes(8, "big")
u128 = lambda x: x.to_bytes(16, "big")


def request_id(n):
    return bytes(24) + u64(n)


def cache_entry(rid, req, stored):
    """rid 32 | principal u32 | nonce u64 | op u8 | a u32 | b u32 | asset u32 | amount u128 | stored 17."""
    p, nonce, kind, a, b, asset, amt = req
    st = bytes([0]) + u64(stored[0]) + u64(stored[1]) if stored[2] == "A" else bytes([1]) + u64(stored[0]) + u64(stored[1])
    return rid + u32(p) + u64(nonce) + bytes([OP[kind]]) + u32(a) + u32(b or 0) + u32(asset) + u128(amt) + st


def parse_token(tok):
    """'A5>6' -> (accepted nonce, next nonce, 'A'); 'Nta@2' -> (expected nonce, reason code, 'N')."""
    if tok[0] == "A":
        n, nxt = tok[1:].split(">")
        return int(n), int(nxt), "A"
    reason, exp = tok[1:].split("@")
    return int(exp), REASON[reason], "N"


def cache_from_trace(t):
    """First occurrence of each request id that was accepted or denied (not replay/conflict/stale/future)."""
    cache = {}
    for row, tok in zip(t["requests"], t["tokens"]):
        rid = request_id(row[0])
        if tok[0] in "AN" and rid not in cache:
            req = (row[1], row[2], row[3], row[4], row[5], row[6], int(row[7]))
            cache[rid] = cache_entry(rid, req, parse_token(tok))
    return cache


def cache_commit(entries):
    es = [entries[k] for k in sorted(entries)]
    return H(D_CACHE + u64(len(es)) + b"".join(es))


def grant_entry(g):
    p, kind, a, b, asset, mx = g
    return u32(p) + bytes([OP[kind]]) + u32(a) + u32(b or 0) + u32(asset) + u128(int(mx))


def policy_commit(grants, control):
    gs = sorted({grant_entry(g) for g in grants})
    cs = sorted({u32(p) + u32(a) for p, a in control})
    return H(D_POL + u64(len(gs)) + b"".join(gs) + u64(len(cs)) + b"".join(cs))


def account_meta(a):
    return bytes([CLASS[a[0]], ACCT_STATUS[a[1]]]) + u32(a[2])


def asset_meta(a):
    sym = a[0].encode()
    return u32(len(sym)) + sym + u32(a[1]) + u32(a[2]) + bytes([ASSET_STATUS[a[3]]]) + u32(a[4])


def registry_commit(accounts, assets):
    return H(D_REG + u32(len(accounts)) + b"".join(account_meta(a) for a in accounts)
             + u32(len(assets)) + b"".join(asset_meta(a) for a in assets))


def state_root(v1_root_parts, cache_c, policy_c, registry_c):
    """v1_root_parts = (accounts, assets, bal root, sup root, nonce root, key root, header hash)."""
    accounts, assets, bal, sup, non, key, hdr = v1_root_parts
    return H(D_STATE + u32(accounts) + u32(assets) + bal + sup + non + key + hdr + cache_c + policy_c + registry_c)


def v1_parts(accounts, assets, balances, supply, nonces, suites, keys, chain_id, version, hash_suite):
    bal, sup, non = v0.state_trees(accounts, assets, balances, supply, nonces)
    suite_root = v0.root({s: v1.suite_value(e) for s, e in suites.items()})
    key_root = v0.root({p: v1.key_value(a) for p, a in keys.items()})
    return (accounts, assets, v0.root(bal), v0.root(sup), v0.root(non), key_root,
            v1.header_hash(chain_id, version, hash_suite, suite_root))


def main():
    base = os.path.dirname(HERE)
    t = json.load(open(os.path.join(base, "engineering/ledger_core/results/machine_trace_v0.json")))["trace"]
    reg = json.load(open(os.path.join(base, "engineering/ledger_core/results/registry_gate_trace_v0.json")))
    fb = [[int(x) for x in row] for row in t["final"]["balances"]]
    fs = [[int(x) for x in row] for row in t["final"]["supply"]]
    fn = [int(x) for x in t["final_nonces"]]
    accounts, assets = t["accounts"], t["assets"]
    suites, keys = v1.sample()
    args = dict(chain_id=7, version=1, hash_suite=1)
    parts = v1_parts(accounts, assets, fb, fs, fn, suites, keys, **args)

    cache = cache_from_trace(t)
    assert len(cache) == t["receipts"], (len(cache), t["receipts"])
    ep0 = reg["episodes"][0]
    assert len(ep0["accounts"]) == accounts and len(ep0["assets"]) == assets
    cc = cache_commit(cache)
    pc = policy_commit(t["grants"], t["control"])
    rc = registry_commit(ep0["accounts"], ep0["assets"])
    root = state_root(parts, cc, pc, rc)

    # every change of one component changes the root
    variants = {}
    k0 = sorted(cache)[0]
    variants["cache_entry_changed"] = state_root(parts, cache_commit({**cache, k0: cache[k0][:-1] + bytes([cache[k0][-1] ^ 1])}), pc, rc)
    variants["cache_entry_removed"] = state_root(parts, cache_commit({k: v for k, v in cache.items() if k != k0}), pc, rc)
    variants["cache_entry_added"] = state_root(parts, cache_commit({**cache, request_id(10**9): cache[k0]}), pc, rc)
    g = [list(x) for x in t["grants"]]
    g2 = [list(x) for x in g]; g2[0][5] = str(int(g2[0][5]) + 1)
    variants["grant_limit"] = state_root(parts, cc, policy_commit(g2, t["control"]), rc)
    uniq_g = [list(x) for x in sorted({tuple(x) for x in t["grants"]}, key=str)]
    variants["grant_removed"] = state_root(parts, cc, policy_commit(uniq_g[1:], t["control"]), rc)
    uniq_c = sorted({tuple(x) for x in t["control"]})
    variants["control_removed"] = state_root(parts, cc, policy_commit(g, uniq_c[1:]), rc)
    absent = next([p, a] for p in range(t["principals"] + 1) for a in range(accounts) if (p, a) not in set(uniq_c))
    variants["control_added"] = state_root(parts, cc, policy_commit(g, uniq_c + [tuple(absent)]), rc)
    a2 = [list(a) for a in ep0["accounts"]]; a2[0][1] = "closed"
    variants["account_status"] = state_root(parts, cc, pc, registry_commit(a2, ep0["assets"]))
    a3 = [list(a) for a in ep0["accounts"]]; a3[1][2] += 1
    variants["account_network"] = state_root(parts, cc, pc, registry_commit(a3, ep0["assets"]))
    s2 = [list(a) for a in ep0["assets"]]; s2[0][0] = "T0X"
    variants["asset_symbol"] = state_root(parts, cc, pc, registry_commit(ep0["accounts"], s2))
    s3 = [list(a) for a in ep0["assets"]]; s3[1][3] = "active"
    variants["asset_status"] = state_root(parts, cc, pc, registry_commit(ep0["accounts"], s3))
    variants["registry_order"] = state_root(parts, cc, pc, registry_commit(ep0["accounts"][::-1], ep0["assets"]))
    assert len({root, *variants.values()}) == 1 + len(variants), "a change left the root unchanged"
    # order and duplicate independence of the policy lists; cache dict order independence
    assert policy_commit(g[::-1] + g[:3], t["control"][::-1] + t["control"][:2]) == pc
    assert cache_commit(dict(reversed(list(cache.items())))) == cc
    # v2 differs from v1 on the same ledger data
    assert root != v1.state_root(accounts, assets, fb, fs, fn, suites, keys, **args)[0]
    # empty components still bind their domains
    assert len({cache_commit({}), policy_commit([], []), registry_commit([], [])}) == 3

    episodes = []
    for e in reg["episodes"]:
        episodes.append({"policy": policy_commit(e["grants"], e["control"]).hex(),
                         "registry": registry_commit(e["accounts"], e["assets"]).hex()})
    print("VARIANTS_DISTINCT=%d EPISODES=%d CACHE=%d" % (len(variants), len(episodes), len(cache)))
    ex = sorted(cache)[:3]
    out = {"format": "SIRM state commitment reference vectors v2",
           "args": args, "cache_entries": len(cache), "cache_commit": cc.hex(), "policy_commit": pc.hex(),
           "registry_commit": rc.hex(), "state_root": root.hex(),
           "cache_entry_examples_hex": [cache[k].hex() for k in ex],
           "grant_entry_example_hex": grant_entry(t["grants"][0]).hex(),
           "account_meta_example_hex": account_meta(ep0["accounts"][0]).hex(),
           "asset_meta_example_hex": asset_meta(ep0["assets"][0]).hex(),
           "episodes": episodes,
           "variants": {n: v.hex() for n, v in variants.items()},
           "empty": {"cache": cache_commit({}).hex(), "policy": policy_commit([], []).hex(),
                     "registry": registry_commit([], []).hex()}}
    path = os.path.join(base, "engineering/canonical_encoding/results/state_commitment_v2_vectors.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=1, sort_keys=True); f.write("\n")
    print("RESULT_JSON=engineering/canonical_encoding/results/state_commitment_v2_vectors.json")


if __name__ == "__main__":
    main()
