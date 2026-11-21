#!/usr/bin/env python3
"""Independent reference for state commitment v6 (PROPOSAL, not adopted): state commitment v5 for the
integrated state machine with the arbiter operation `resolve`. Spec: engineering/canonical_encoding/SPEC_state_commitment_v6.md.
Vectors: engineering/canonical_encoding/results/state_commitment_v6_vectors.json

Differences to v5: new domains, cache entries are request encoding v2 (so a cached resolve request has
a commitment), and cause code 15 (not disputed) exists. The state is taken from the final model state of
the 402 episodes of the independent Python integrated reference and of the 300 episodes of its resolve
trace (scripts/integrated_resolve_reference_trace.py), each regenerated here from its seed and checked
against the committed trace.
"""
import copy, hashlib, json, os, random, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import state_commitment_reference as v0
import state_commitment_v2_reference as v2
import state_commitment_v3_reference as v3
import integrated_machine_reference as im
import request_v2_reference as rq
import request_v1_reference as rq1

H = lambda b: hashlib.sha256(b).digest()
D_STATE, D_CFG, D_CAC, D_ESC = b"SIRM/STC/v6\x00", b"SIRM/CFG/v6\x00", b"SIRM/CAC/v6\x00", b"SIRM/ESC/v6\x00"
u32, u64, u128 = v2.u32, v2.u64, v2.u128
TAG = rq.TAGS
CAUSE = {"auth": 0, "r": 1, "v": 2, "x": 3, "w": 4, "k": 5, "n": 6, "d": 7, "e": 8, "z": 9,
         "u": 10, "i": 11, "t": 12, "a": 13, "c": 14, "o": 15}
OLD = {"ta": ("transfer", "auth"), "ia": ("issue", "auth"), "ba": ("burn", "auth"),
       "tf": ("transfer", "i"), "bf": ("burn", "i")}


def regenerate(arbiter):
    """Re-run the integrated reference (base trace, or the resolve trace) and keep every episode's final IM instance."""
    made = []

    class Cap(im.IM):
        def __init__(self, *a, **k):
            super().__init__(*a, **k)
            made.append(self)

    orig = im.IM
    im.IM = Cap
    try:
        if arbiter:
            rnd = random.Random(20261121)
            eps = [im.episode(rnd, rnd.randrange(60, 110), arbiter=True) for _ in range(300)]
        else:
            rnd = random.Random(20261116)
            eps = im.boundary() + [im.episode(rnd, rnd.randrange(50, 90)) for _ in range(400)]
    finally:
        im.IM = orig
    assert len(made) == len(eps)
    return eps, made


def stored_bytes(tok):
    """11 bytes: flag u8 (1 accepted, 2 denied) | kind u8 | cause u8 | nonce u64 (accepted nonce or expected nonce)."""
    if tok[0] == "A":
        return bytes([1, 0, 0]) + u64(int(tok[1:].split(">")[0]))
    code, nonce = tok[1:].split("@")
    op, c = OLD[code] if code in OLD else code.split(":")
    return bytes([2, TAG[op], CAUSE[c]]) + u64(int(nonce))


def cache_commit(m):
    entries = []
    for rid, ((p, nonce, op, args), tok) in m.cache.items():
        row = [rid, p, nonce, op] + list(args)
        req = rq.encode(rq1.trace_request(row))
        entries.append((req[12:44], req + stored_bytes(tok)))
    entries.sort()
    return H(D_CAC + u32(len(entries)) + b"".join(e for _, e in entries))


def policy_bytes(m):
    ctl = sorted(u32(p) + u32(a) for p, a in m.controls)
    lim = sorted(u32(k[0]) + bytes([TAG[k[1]]]) + u32(k[2]) + (b"\x00" + bytes(4) if k[3] is None else b"\x01" + u32(k[3]))
                 + u32(k[4]) + u128(v) for k, v in m.lim.items())
    ids = sorted(u32(p) + bytes([TAG[op]]) + u32(i) for p, op, i in m.idg)
    clk = sorted(u32(p) for p in m.clock)
    out = b""
    for part in (ctl, lim, ids, clk):
        out += u32(len(part)) + b"".join(part)
    return out


def config_commit(m):
    vault = (b"\x01" + u32(m.vault)) if m.vault is not None else bytes(5)
    dl = u32(len(m.dl)) + b"".join(u64(d) for d in m.dl)
    g = m.mig
    mig = (b"\x01" + u32(g["holder"]) + u32(g["recipient"]) + u32(g["src"]) + u32(g["dst"])
           + u128(g["num"]) + u128(g["den"])) if g else bytes(49)
    return H(D_CFG + u32(m.A) + u32(m.S) + vault + dl + mig + policy_bytes(m))


def escrow_commit(m):
    table = b"".join(v3.id_entry(m.dl[i], m.recs.get(i), m.files.get(i)) for i in range(len(m.dl)))
    return H(D_ESC + u32(len(m.dl)) + table)


def parts(m):
    bal = [[m.bal[(a, s)] for s in range(m.S)] for a in range(m.A)]
    sup = [tuple(m.sup[s]) for s in range(m.S)]
    nonces = [m.nxt.get(p, 0) for p in range(max(m.nxt, default=-1) + 1)]
    b, s_, n = v0.state_trees(m.A, m.S, bal, sup, nonces)
    return v0.root(b), v0.root(s_), v0.root(n)


def state_root(m):
    br, sr, nr = parts(m)
    mig = (u128(m.tsrc) + u128(m.ttgt) + u128(m.dust)) if m.mig else bytes(48)
    return H(D_STATE + u32(m.A) + u32(m.S) + br + sr + nr + config_commit(m) + cache_commit(m)
             + escrow_commit(m) + u64(m.now) + mig)


def variants_of(m):
    def var(f):
        m2 = copy.deepcopy(m)
        f(m2)
        return state_root(m2).hex()

    fid = next(iter(m.files)) if m.files else None
    rid = next(iter(m.cache))
    key = next(iter(m.lim))
    v = {
        "balance": var(lambda x: x.bal.__setitem__((0, 0), x.bal[(0, 0)] + 1)),
        "minted": var(lambda x: x.sup[0].__setitem__(0, x.sup[0][0] + 1)),
        "nonce": var(lambda x: x.nxt.__setitem__(0, x.nxt.get(0, 0) + 1)),
        "now": var(lambda x: setattr(x, "now", x.now + 1)),
        "dust": var(lambda x: setattr(x, "dust", x.dust + 1)),
        "total_source": var(lambda x: setattr(x, "tsrc", x.tsrc + 1)),
        "total_target": var(lambda x: setattr(x, "ttgt", x.ttgt + 1)),
        "limit": var(lambda x: x.lim.__setitem__(key, x.lim[key] + 1)),
        "control": var(lambda x: x.controls.add((2, 3)) if (2, 3) not in x.controls else x.controls.discard((2, 3))),
        "clock": var(lambda x: x.clock.symmetric_difference_update({2})),
        "vault": var(lambda x: setattr(x, "vault", (x.vault + 1) % x.A)),
        "deadline": var(lambda x: x.dl.__setitem__(0, x.dl[0] + 1)),
        "migration_rate": var(lambda x: x.mig.__setitem__("num", x.mig["num"] + 1)),
        "cache_outcome": var(lambda x: x.cache.__setitem__(rid, (x.cache[rid][0], "N" + "ta@0" if x.cache[rid][1] != "Nta@0" else "Nia@0"))),
        "cache_entry_removed": var(lambda x: x.cache.pop(rid)),
    }
    if fid is not None:
        v["filing"] = var(lambda x: x.files[fid].__setitem__(2, x.files[fid][2] + 1))
        v["record_phase"] = var(lambda x: x.recs[fid].__setitem__(4, "expired" if x.recs[fid][4] != "expired" else "released"))
    return v


def cached_resolves(m):
    return [rid for rid, ((p, nonce, op, args), tok) in m.cache.items() if op == "resolve"]


def main():
    base = os.path.dirname(HERE)
    res = os.path.join(base, "engineering/ledger_core/results")
    doc = {"format": "SIRM state commitment v6 vectors (proposal)"}
    for name, arbiter, trace in (("base", False, "integrated_trace_v0.json"), ("resolve", True, "integrated_resolve_trace_v0.json")):
        eps, made = regenerate(arbiter)
        committed = json.load(open(os.path.join(res, trace)))
        assert [json.loads(json.dumps(x, sort_keys=True)) for x in eps] == committed["episodes"], "regenerated episodes differ from " + trace
        roots = [state_root(m) for m in made]
        assert len(set(roots)) == len(roots), "state roots must be distinct across episodes"
        if arbiter:
            # an episode with a filing, a resolved escrow (cached accepted resolve), dust and several principals
            def rich(m, need_files):
                return (bool(m.files) or not need_files) and m.dust and len(m.nxt) >= 2 and \
                    any(m.cache[rid][1][0] == "A" for rid in cached_resolves(m))
            ex = next((i for i, m in enumerate(made) if rich(m, True)), None)
            if ex is None:
                ex = next(i for i, m in enumerate(made) if rich(m, False))
        else:
            ex = next(i for i, m in enumerate(made) if m.files and m.dust and
                      any(r[4] in ("released", "cancelled", "expired") for r in m.recs.values()) and len(m.nxt) >= 2)
        m = made[ex]
        variants = variants_of(m)
        if arbiter:
            rr = cached_resolves(m)[0]

            def flip(x):
                (p, nonce, op, args), tok = x.cache[rr]
                x.cache[rr] = ((p, nonce, op, (args[0], str(1 - int(args[1])))), tok)

            def swap_id(x):
                (p, nonce, op, args), tok = x.cache[rr]
                x.cache[rr] = ((p, nonce, op, (str((int(args[0]) + 1) % len(x.dl)), args[1])), tok)

            m2 = copy.deepcopy(m); flip(m2); variants["cached_resolve_side"] = state_root(m2).hex()
            m3 = copy.deepcopy(m); swap_id(m3); variants["cached_resolve_id"] = state_root(m3).hex()
        assert len(set(variants.values())) == len(variants) and state_root(m).hex() not in variants.values(), name
        doc[name] = {"episodes": len(made), "roots": [r.hex() for r in roots],
                     "roots_aggregate_sha256": H(b"".join(roots)).hex(), "example_episode": ex,
                     "example": {"root": roots[ex].hex(), "config": config_commit(m).hex(), "cache": cache_commit(m).hex(),
                                 "escrow": escrow_commit(m).hex(), "balance_root": parts(m)[0].hex(),
                                 "supply_root": parts(m)[1].hex(), "nonce_root": parts(m)[2].hex()},
                     "variants": variants}
        print("%s: EPISODES=%d DISTINCT_ROOTS=%d VARIANTS=%d EXAMPLE=%d AGG=%s" % (
            name, len(made), len(set(roots)), len(variants), ex, doc[name]["roots_aggregate_sha256"]))
    out = os.path.join(base, "engineering/canonical_encoding/results/state_commitment_v6_vectors.json")
    open(out, "w").write(json.dumps(doc, indent=1, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
