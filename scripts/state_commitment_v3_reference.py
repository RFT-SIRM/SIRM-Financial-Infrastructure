#!/usr/bin/env python3
"""Independent reference for state commitment v3 (PROPOSAL, not adopted).

Extends v2 with the escrow / time-lock / dispute component. See
engineering/canonical_encoding/SPEC_state_commitment_v3.md.
Output: engineering/canonical_encoding/results/state_commitment_v3_vectors.json

The escrow component is taken from the final model state of the 1500 episodes of the independent
Python dispute reference (scripts/dispute_reference_trace.py), regenerated here from its seed and
checked against the committed trace.
"""
import hashlib, json, os, random, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import state_commitment_reference as v0
import state_commitment_v1_reference as v1
import state_commitment_v2_reference as v2
import dispute_reference_trace as dr

H = lambda b: hashlib.sha256(b).digest()
D_STATE = b"SIRM/STC/v3\x00"
D_ESC = b"SIRM/ESC/v3\x00"
PHASE = {"pending": 1, "released": 2, "cancelled": 3, "expired": 4}
u32 = v2.u32
u64 = v2.u64
u128 = v2.u128


def regenerate():
    """Re-run the Python dispute reference and capture each episode's final model object."""
    made = []

    class Cap(dr.Esc):
        def __init__(self, *a):
            super().__init__(*a)
            made.append(self)

    orig = dr.Esc
    dr.Esc = Cap
    try:
        rnd = random.Random(20261114)
        eps = [dr.episode(rnd) for _ in range(1500)]
    finally:
        dr.Esc = orig
    assert len(made) == len(eps)
    return eps, made


def id_entry(deadline, rec, filing):
    """deadline u64 | rec flag | dep u32 | ben u32 | asset u32 | amount u128 | phase u8
    | filing flag | principal u32 | claimant u32 | filed_at u64   (55 bytes)."""
    r = (b"\x01" + u32(rec[0]) + u32(rec[1]) + u32(rec[2]) + u128(rec[3]) + bytes([PHASE[rec[4]]])) if rec else bytes(30)
    f = (b"\x01" + u32(filing[0]) + u32(filing[1]) + u64(filing[2])) if filing else bytes(17)
    return u64(deadline) + r + f


def escrow_commit(e):
    accounts, assets = dr.ACCOUNTS, dr.ASSETS
    bal = [[e.bal[(a, s)] for s in range(assets)] for a in range(accounts)]
    # the escrow model only issues (no burns): minted = outstanding = sum of issues; derive from balances
    minted = [sum(e.bal[(a, s)] for a in range(accounts)) for s in range(assets)]
    supply = [(m, 0, m) for m in minted]
    b, s_, _ = v0.state_trees(accounts, assets, bal, supply, [])
    table = b"".join(id_entry(e.dl[i], e.recs.get(i), e.files.get(i)) for i in range(dr.IDS))
    return H(D_ESC + u32(accounts) + u32(assets) + v0.root(b) + v0.root(s_) + u32(e.vault)
             + u64(e.now) + u32(dr.IDS) + table)


def state_root(v1_parts, cache_c, policy_c, registry_c, escrow_c):
    accounts, assets, bal, sup, non, key, hdr = v1_parts
    return H(D_STATE + u32(accounts) + u32(assets) + bal + sup + non + key + hdr
             + cache_c + policy_c + registry_c + escrow_c)


def main():
    base = os.path.dirname(HERE)
    eps, made = regenerate()
    committed = json.load(open(os.path.join(base, "engineering/ledger_core/results/dispute_trace_v0.json")))
    assert [json.loads(json.dumps(x)) for x in eps] == committed["episodes"], "regenerated episodes differ from the committed trace"

    commits = [escrow_commit(e) for e in made]
    # supply cross-check: the derived supply equals issued units (escrow only issues)
    for ep, e in zip(eps, made):
        issued = [0] * dr.ASSETS
        for op, out in zip(ep["ops"], ep["outcomes"]):
            if op[0] == "issue" and out == "o":
                issued[op[2]] += int(op[3])
        assert issued == [sum(e.bal[(a, s)] for a in range(dr.ACCOUNTS)) for s in range(dr.ASSETS)]

    # pick the first episode that has a filing and a settled record (rich example)
    ex = next(i for i, e in enumerate(made) if e.files and any(r[4] in ("released", "cancelled", "expired") for r in e.recs.values()))
    e = made[ex]

    # full v3 root over the v2 sample plus that episode
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
    ec = commits[ex]
    root = state_root(parts, cc, pc, rc, ec)

    # single-field variants of the example episode
    def var(f):
        import copy
        e2 = copy.deepcopy(e)
        f(e2)
        return escrow_commit(e2)

    some_id = next(iter(e.files))
    rec_id = next(iter(e.recs))
    variants = {
        "vault": var(lambda x: setattr(x, "vault", (x.vault + 1) % dr.ACCOUNTS)),
        "now": var(lambda x: setattr(x, "now", x.now + 1)),
        "deadline": var(lambda x: x.dl.__setitem__(0, x.dl[0] + 1)),
        "balance": var(lambda x: x.bal.__setitem__((0, 0), x.bal[(0, 0)] + 1)),
        "record_amount": var(lambda x: x.recs[rec_id].__setitem__(3, x.recs[rec_id][3] + 1)),
        "record_phase": var(lambda x: x.recs[rec_id].__setitem__(4, "pending" if x.recs[rec_id][4] != "pending" else "released")),
        "record_beneficiary": var(lambda x: x.recs[rec_id].__setitem__(1, (x.recs[rec_id][1] + 1) % dr.ACCOUNTS)),
        "filing_removed": var(lambda x: x.files.pop(some_id)),
        "filing_claimant": var(lambda x: x.files[some_id].__setitem__(1, (x.files[some_id][1] + 1) % dr.ACCOUNTS)),
        "filing_time": var(lambda x: x.files[some_id].__setitem__(2, x.files[some_id][2] + 1)),
        "record_removed": var(lambda x: (x.files.pop(rec_id, None), x.recs.pop(rec_id))),
    }
    assert len({ec, *variants.values()}) == 1 + len(variants), "a change left the commitment unchanged"
    assert root != v2.state_root(parts, cc, pc, rc)
    print("EPISODES=%d DISTINCT_COMMITS=%d VARIANTS=%d EXAMPLE=%d" % (len(commits), len(set(commits)), len(variants), ex))

    out = {"format": "SIRM state commitment reference vectors v3",
           "args": args, "example_episode": ex, "state_root": root.hex(), "escrow_commit": ec.hex(),
           "id_entry_example_hex": [id_entry(e.dl[i], e.recs.get(i), e.files.get(i)).hex() for i in range(dr.IDS)],
           "variants": {k: v.hex() for k, v in variants.items()},
           "episode_commits": [c.hex() for c in commits]}
    path = os.path.join(base, "engineering/canonical_encoding/results/state_commitment_v3_vectors.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=1, sort_keys=True); f.write("\n")
    print("RESULT_JSON=engineering/canonical_encoding/results/state_commitment_v3_vectors.json")


if __name__ == "__main__":
    main()
