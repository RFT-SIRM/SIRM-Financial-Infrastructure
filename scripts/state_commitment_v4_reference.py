#!/usr/bin/env python3
"""Independent reference for state commitment v4 (PROPOSAL, not adopted).

Extends v3 with the asset-migration component. See
engineering/canonical_encoding/SPEC_state_commitment_v4.md.
Output: engineering/canonical_encoding/results/state_commitment_v4_vectors.json

The migration component is committed from the final state recorded by the independent Python
migration reference trace (engineering/ledger_core/results/migration_trace_v0.json), not from Rust.
"""
import copy, hashlib, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import state_commitment_reference as v0
import state_commitment_v1_reference as v1
import state_commitment_v2_reference as v2
import state_commitment_v3_reference as v3

H = lambda b: hashlib.sha256(b).digest()
D_STATE = b"SIRM/STC/v4\x00"
D_MIG = b"SIRM/MIG/v4\x00"
u32, u64, u128 = v2.u32, v2.u64, v2.u128
SRC, DST = 0, 1  # the migration stream moves asset 0 into asset 1


def migration_commit(accounts, assets, ep):
    f = ep["final"]
    bal = [[int(x) for x in row] for row in f["balances"]]
    supply = [(int(m), int(b), int(m) - int(b)) for m, b in zip(f["minted"], f["burned"])]
    b, s, _ = v0.state_trees(accounts, assets, bal, supply, [])
    nonces = b"".join(u32(p) + u64(n) for p, n in enumerate(f["nonces"]) if n)
    count = sum(1 for n in f["nonces"] if n)
    return H(D_MIG + u32(accounts) + u32(assets) + v0.root(b) + v0.root(s)
             + u32(ep["holder"]) + u32(ep["recipient"]) + u32(SRC) + u32(DST)
             + u128(int(ep["num"])) + u128(int(ep["den"]))
             + u128(int(f["total_source"])) + u128(int(f["total_target"])) + u128(int(f["dust"]))
             + u32(count) + nonces)


def state_root(parts, cache_c, policy_c, registry_c, escrow_c, mig_c):
    accounts, assets, bal, sup, non, key, hdr = parts
    return H(D_STATE + u32(accounts) + u32(assets) + bal + sup + non + key + hdr
             + cache_c + policy_c + registry_c + escrow_c + mig_c)


def main():
    base = os.path.dirname(HERE)
    d = json.load(open(os.path.join(base, "engineering/ledger_core/results/migration_trace_v0.json")))
    accounts, assets = d["accounts"], d["assets"]
    eps = d["episodes"]
    commits = [migration_commit(accounts, assets, e) for e in eps]

    # rich example: dust carried, several principals with nonces
    ex = next(i for i, e in enumerate(eps) if int(e["final"]["dust"]) and sum(1 for n in e["final"]["nonces"] if n) >= 2)
    e = eps[ex]
    mc = commits[ex]

    # full root over the v3 sample plus this episode
    t = json.load(open(os.path.join(base, "engineering/ledger_core/results/machine_trace_v0.json")))["trace"]
    reg = json.load(open(os.path.join(base, "engineering/ledger_core/results/registry_gate_trace_v0.json")))
    fb = [[int(x) for x in row] for row in t["final"]["balances"]]
    fs = [[int(x) for x in row] for row in t["final"]["supply"]]
    fn = [int(x) for x in t["final_nonces"]]
    suites, keys = v1.sample()
    args = dict(chain_id=7, version=1, hash_suite=1)
    parts = v2.v1_parts(t["accounts"], t["assets"], fb, fs, fn, suites, keys, **args)
    cc = v2.cache_commit(v2.cache_from_trace(t))
    pc = v2.policy_commit(t["grants"], t["control"])
    ep0 = reg["episodes"][0]
    rc = v2.registry_commit(ep0["accounts"], ep0["assets"])
    v3ex = json.load(open(os.path.join(base, "engineering/canonical_encoding/results/state_commitment_v3_vectors.json")))["example_episode"]
    _, made = v3.regenerate()
    ec = v3.escrow_commit(made[v3ex])
    root = state_root(parts, cc, pc, rc, ec, mc)

    def var(f):
        e2 = copy.deepcopy(e)
        f(e2)
        return migration_commit(accounts, assets, e2)

    def bump(key, val=1):
        return lambda x: x["final"].__setitem__(key, str(int(x["final"][key]) + val))

    nz = next(p for p, n in enumerate(e["final"]["nonces"]) if n)
    variants = {
        "holder": var(lambda x: x.__setitem__("holder", (x["holder"] + 1) % accounts)),
        "recipient": var(lambda x: x.__setitem__("recipient", (x["recipient"] + 1) % accounts)),
        "numerator": var(lambda x: x.__setitem__("num", str(int(x["num"]) + 1))),
        "denominator": var(lambda x: x.__setitem__("den", str(int(x["den"]) + 1))),
        "total_source": var(bump("total_source")),
        "total_target": var(bump("total_target")),
        "dust": var(bump("dust")),
        "nonce_changed": var(lambda x: x["final"]["nonces"].__setitem__(nz, x["final"]["nonces"][nz] + 1)),
        "nonce_cleared": var(lambda x: x["final"]["nonces"].__setitem__(nz, 0)),
        "balance": var(lambda x: x["final"]["balances"][0].__setitem__(0, str(int(x["final"]["balances"][0][0]) + 1))),
        "minted": var(lambda x: x["final"]["minted"].__setitem__(1, str(int(x["final"]["minted"][1]) + 1))),
        "burned": var(lambda x: x["final"]["burned"].__setitem__(0, str(int(x["final"]["burned"][0]) + 1))),
    }
    assert len({mc, *variants.values()}) == 1 + len(variants), "a change left the commitment unchanged"
    assert root != v3.state_root(parts, cc, pc, rc, ec)
    print("EPISODES=%d DISTINCT_COMMITS=%d VARIANTS=%d EXAMPLE=%d" % (len(commits), len(set(commits)), len(variants), ex))

    out = {"format": "SIRM state commitment reference vectors v4", "args": args,
           "example_episode": ex, "v3_example_episode": v3ex,
           "state_root": root.hex(), "migration_commit": mc.hex(),
           "variants": {k: v.hex() for k, v in variants.items()},
           "episode_commits": [c.hex() for c in commits]}
    path = os.path.join(base, "engineering/canonical_encoding/results/state_commitment_v4_vectors.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=1, sort_keys=True); f.write("\n")
    print("RESULT_JSON=engineering/canonical_encoding/results/state_commitment_v4_vectors.json")


if __name__ == "__main__":
    main()
