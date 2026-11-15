#!/usr/bin/env python3
"""Independent reference for state commitment v1 (PROPOSAL, not adopted).

Extends the v0 root (balances, supply, nonces) with the key registry, the suite registry and a
protocol header. See engineering/canonical_encoding/SPEC_state_commitment_v1.md.
Output: engineering/canonical_encoding/results/state_commitment_v1_vectors.json
"""
import hashlib, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import state_commitment_reference as v0

D_STATE = b"SIRM/STC/v1\x00"
D_HDR = b"SIRM/HDR/v1\x00"
H = lambda b: hashlib.sha256(b).digest()
STATUS = {"proposed": 0, "active": 1, "deprecated": 2, "disabled": 3}
KIND = {"sign": 0, "kem": 1, "hash": 2, "aead": 3}
NONE = 2**64 - 1  # "no height" marker


def suite_value(e):
    return (bytes([KIND[e["kind"]], STATUS[e["status"]]]) + e["pk_len"].to_bytes(4, "big") + e["sig_len"].to_bytes(4, "big")
            + e["activation"].to_bytes(8, "big") + e["deprecation"].to_bytes(8, "big") + e["disable"].to_bytes(8, "big"))


def key_value(a):
    flags = (1 if a["frozen"] else 0) | (2 if a["revoked"] else 0) | (4 if a["pq_bound"] else 0)
    rec = a.get("recovery")
    pend = a.get("pending")
    return (a["suite"].to_bytes(2, "big") + a["key_id"] + bytes([flags])
            + (b"\x01" + rec if rec else b"\x00" + bytes(32))
            + (b"\x01" + pend[0] + pend[1].to_bytes(8, "big") if pend else b"\x00" + bytes(32) + bytes(8)))


def header_hash(chain_id, version, hash_suite, suite_root):
    return H(D_HDR + chain_id.to_bytes(8, "big") + version.to_bytes(2, "big") + hash_suite.to_bytes(2, "big") + suite_root)


def state_root(accounts, assets, balances, supply, nonces, suites, keys, chain_id, version, hash_suite):
    bal, sup, non = v0.state_trees(accounts, assets, balances, supply, nonces)
    suite_root = v0.root({s: suite_value(e) for s, e in suites.items()})
    key_root = v0.root({p: key_value(a) for p, a in keys.items()})
    return H(D_STATE + accounts.to_bytes(4, "big") + assets.to_bytes(4, "big") + v0.root(bal) + v0.root(sup) + v0.root(non)
             + key_root + header_hash(chain_id, version, hash_suite, suite_root)), suite_root, key_root


def sample():
    suites = {
        1: dict(kind="sign", status="deprecated", pk_len=32, sig_len=64, activation=0, deprecation=100, disable=NONE),
        2: dict(kind="sign", status="active", pk_len=1952, sig_len=3309, activation=0, deprecation=NONE, disable=NONE),
        0x0101: dict(kind="sign", status="active", pk_len=1984, sig_len=3373, activation=0, deprecation=NONE, disable=NONE),
        3: dict(kind="sign", status="proposed", pk_len=32, sig_len=7856, activation=NONE, deprecation=NONE, disable=NONE),
    }
    kid = lambda i: H(b"key" + bytes([i]))
    keys = {
        0: dict(suite=2, key_id=kid(0), frozen=False, revoked=False, pq_bound=True, recovery=kid(10), pending=None),
        1: dict(suite=0x0101, key_id=kid(1), frozen=False, revoked=False, pq_bound=True, recovery=kid(11), pending=(kid(12), 500)),
        2: dict(suite=1, key_id=kid(2), frozen=True, revoked=False, pq_bound=False, recovery=None, pending=None),
    }
    return suites, keys


def main():
    base = os.path.dirname(HERE)
    t = json.load(open(os.path.join(base, "engineering/ledger_core/results/machine_trace_v0.json")))["trace"]
    fb = [[int(x) for x in row] for row in t["final"]["balances"]]
    fs = [[int(x) for x in row] for row in t["final"]["supply"]]
    fn = [int(x) for x in t["final_nonces"]]
    accounts, assets = t["accounts"], t["assets"]
    suites, keys = sample()
    args = dict(chain_id=7, version=1, hash_suite=1)
    root, suite_root, key_root = state_root(accounts, assets, fb, fs, fn, suites, keys, **args)

    def variant(**kw):
        s2 = json.loads(json.dumps({str(k): v for k, v in suites.items()}, default=list))
        s = {k: dict(v) for k, v in suites.items()}
        k2 = {p: dict(a) for p, a in keys.items()}
        a2 = dict(args)
        for name, f in kw.items():
            f(s, k2, a2)
        return state_root(accounts, assets, fb, fs, fn, s, k2, **a2)[0]

    changes = {
        "chain_id": lambda s, k, a: a.update(chain_id=8),
        "version": lambda s, k, a: a.update(version=2),
        "hash_suite": lambda s, k, a: a.update(hash_suite=2),
        "suite_status": lambda s, k, a: s[1].update(status="disabled"),
        "suite_pk_len": lambda s, k, a: s[2].update(pk_len=1953),
        "suite_deprecation": lambda s, k, a: s[1].update(deprecation=101),
        "suite_added": lambda s, k, a: s.update({9: dict(kind="kem", status="active", pk_len=1184, sig_len=1088, activation=0, deprecation=NONE, disable=NONE)}),
        "key_suite": lambda s, k, a: k[0].update(suite=0x0101),
        "key_id": lambda s, k, a: k[0].update(key_id=H(b"other")),
        "key_frozen": lambda s, k, a: k[0].update(frozen=True),
        "key_revoked": lambda s, k, a: k[0].update(revoked=True),
        "key_pq_bound": lambda s, k, a: k[2].update(pq_bound=True),
        "key_recovery_removed": lambda s, k, a: k[0].update(recovery=None),
        "key_recovery_changed": lambda s, k, a: k[0].update(recovery=H(b"r2")),
        "key_pending_removed": lambda s, k, a: k[1].update(pending=None),
        "key_pending_start": lambda s, k, a: k[1].update(pending=(k[1]["pending"][0], 501)),
        "key_pending_added": lambda s, k, a: k[0].update(pending=(H(b"p"), 1)),
        "key_account_removed": lambda s, k, a: k.pop(2),
    }
    variants = {n: variant(c=f) for n, f in changes.items()}
    assert len({root, *variants.values()}) == 1 + len(variants), "a change left the root unchanged"
    # order independence of registry dicts
    s_rev = dict(reversed(list(suites.items()))); k_rev = dict(reversed(list(keys.items())))
    assert state_root(accounts, assets, fb, fs, fn, s_rev, k_rev, **args)[0] == root
    # v1 differs from v0 on the same ledger data (the registries and header are bound)
    assert root != v0.state_root(accounts, assets, fb, fs, fn)
    # empty registries still bind chain id and version
    e1 = state_root(accounts, assets, fb, fs, fn, {}, {}, 1, 1, 1)[0]
    e2 = state_root(accounts, assets, fb, fs, fn, {}, {}, 2, 1, 1)[0]
    assert e1 != e2
    print("VARIANTS_DISTINCT=%d" % len(variants))
    out = {"format": "SIRM state commitment reference vectors v1",
           "args": args, "machine_accounts": accounts, "machine_assets": assets,
           "suite_root": suite_root.hex(), "key_root": key_root.hex(), "state_root": root.hex(),
           "suites": {str(s): {k: (str(v) if isinstance(v, int) and v > 2**53 else v) for k, v in e.items()} for s, e in suites.items()},
           "keys": {str(p): {"suite": a["suite"], "key_id": a["key_id"].hex(), "frozen": a["frozen"], "revoked": a["revoked"], "pq_bound": a["pq_bound"],
                             "recovery": a["recovery"].hex() if a["recovery"] else None,
                             "pending": [a["pending"][0].hex(), a["pending"][1]] if a["pending"] else None} for p, a in keys.items()},
           "suite_value_hex": {str(s): suite_value(e).hex() for s, e in suites.items()},
           "key_value_hex": {str(p): key_value(a).hex() for p, a in keys.items()},
           "variants": {n: v.hex() for n, v in variants.items()},
           "empty_registries": {"chain1": e1.hex(), "chain2": e2.hex()}}
    path = os.path.join(base, "engineering/canonical_encoding/results/state_commitment_v1_vectors.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=1, sort_keys=True); f.write("\n")
    print("RESULT_JSON=engineering/canonical_encoding/results/state_commitment_v1_vectors.json")


if __name__ == "__main__":
    main()
