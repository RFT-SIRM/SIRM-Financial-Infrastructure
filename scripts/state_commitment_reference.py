#!/usr/bin/env python3
"""Independent reference for state commitment v0 (checked by SIRM).

Sparse Merkle tree (SMT), depth 64, SHA-256, over u64 keys with byte-string values; absent
and empty are the same.  A state commitment hashes three SMTs (balances, supply, nonces) with
the dimensions.  Output: engineering/canonical_encoding/results/state_commitment_vectors_v0.json
"""
import hashlib, json, os, random, sys

D_EMPTY = b"SIRM/SMT/E/v0\0"
D_LEAF = b"SIRM/SMT/L/v0\0"
D_NODE = b"SIRM/SMT/N/v0\0"
D_STATE = b"SIRM/STC/v0\0"
DEPTH = 64
H = lambda b: hashlib.sha256(b).digest()

EMPTY = [H(D_EMPTY)]
for _ in range(DEPTH):
    EMPTY.append(H(D_NODE + EMPTY[-1] + EMPTY[-1]))


def leaf(key, value):
    assert 0 < len(value) < 65536
    return H(D_LEAF + key.to_bytes(8, "big") + len(value).to_bytes(2, "big") + value)


def root(entries):
    """entries: dict key -> value (nonempty bytes). Recursive over sorted keys."""
    items = sorted(entries.items())

    def go(lo, hi, level):  # items[lo:hi] share the top (DEPTH-level) key bits
        if lo == hi:
            return EMPTY[level]
        if level == 0:
            assert hi - lo == 1
            return leaf(*items[lo])
        bit = level - 1
        mid = lo
        while mid < hi and not (items[mid][0] >> bit) & 1:
            mid += 1
        return H(D_NODE + go(lo, mid, level - 1) + go(mid, hi, level - 1))

    return go(0, len(items), DEPTH)


def root_naive(entries):
    """Second algorithm: build every node bottom-up in a dict, level by level."""
    level = {k: leaf(k, v) for k, v in entries.items()}
    for lv in range(DEPTH):
        nxt = {}
        for k in {k >> 1 for k in level}:
            l = level.get(2 * k, EMPTY[lv])
            r = level.get(2 * k + 1, EMPTY[lv])
            nxt[k] = H(D_NODE + l + r)
        level = nxt
    return level.get(0, EMPTY[DEPTH])


def prove(entries, key):
    """Siblings from the leaf level upward (64 hashes) and the value (None if absent)."""
    nodes = [{k: leaf(k, v) for k, v in entries.items()}]
    for lv in range(DEPTH):
        nxt = {}
        for k in {k >> 1 for k in nodes[-1]}:
            nxt[k] = H(D_NODE + nodes[-1].get(2 * k, EMPTY[lv]) + nodes[-1].get(2 * k + 1, EMPTY[lv]))
        nodes.append(nxt)
    sibs = [nodes[lv].get((key >> lv) ^ 1, EMPTY[lv]) for lv in range(DEPTH)]
    return sibs, entries.get(key)


def verify(rt, key, value, sibs):
    if len(sibs) != DEPTH:
        return False
    h = EMPTY[0] if value is None else leaf(key, value)
    for lv in range(DEPTH):
        h = H(D_NODE + sibs[lv] + h) if (key >> lv) & 1 else H(D_NODE + h + sibs[lv])
    return h == rt


def u128(x):
    assert 0 <= x < 2**128
    return x.to_bytes(16, "big")


def state_trees(accounts, assets, balances, supply, nonces):
    bal = {}
    for a, row in enumerate(balances):
        for s, v in enumerate(row):
            if v:
                bal[(a << 32) | s] = u128(v)
    sup = {s: u128(m) + u128(b) + u128(o) for s, (m, b, o) in enumerate(supply) if m or b or o}
    non = {p: n.to_bytes(8, "big") for p, n in enumerate(nonces) if n}
    return bal, sup, non


def state_root(accounts, assets, balances, supply, nonces):
    bal, sup, non = state_trees(accounts, assets, balances, supply, nonces)
    return H(D_STATE + accounts.to_bytes(4, "big") + assets.to_bytes(4, "big")
             + root(bal) + root(sup) + root(non))


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    base = os.path.dirname(here)
    rnd = random.Random(20261115)
    # 1. two algorithms agree; order independence; absent == not stored
    for n in [0, 1, 2, 3, 7, 40]:
        for _ in range(25):
            keys = rnd.sample([rnd.getrandbits(64) for _ in range(60)] + [0, 1, 2**64 - 1, 2**63], n) if n else []
            e = {k: rnd.getrandbits(128).to_bytes(16, "big") for k in keys}
            assert root(e) == root_naive(e)
            shuffled = dict(rnd.sample(list(e.items()), len(e)))
            assert root(shuffled) == root(e)
    assert root({}) == EMPTY[DEPTH]
    print("ALGORITHMS_AGREE=1")
    # 2. proofs: inclusion, non-inclusion, tamper
    tree = {k: rnd.getrandbits(128).to_bytes(16, "big") for k in [0, 1, 5, 2**63, 2**64 - 1, 12345678901234]}
    rt = root(tree)
    checked = 0
    for k in list(tree) + [2, 3, 2**62, 2**64 - 2]:
        sibs, val = prove(tree, k)
        assert verify(rt, k, val, sibs)
        assert not verify(rt, k, b"\x01" * 16 if val is None else val[:-1] + bytes([val[-1] ^ 1]), sibs)
        for i in range(0, DEPTH, 9):
            bad = list(sibs); bad[i] = bytes([bad[i][0] ^ 1]) + bad[i][1:]
            assert not verify(rt, k, val, bad)
        if val is not None:
            assert not verify(rt, k ^ (1 << 40), val, sibs)
        checked += 1
    print("PROOFS_CHECKED=%d" % checked)
    # 3. state commitment sensitivity (every component changes the root)
    accounts, assets = 3, 2
    bal = [[5, 0], [0, 7], [1, 2]]
    sup = [[6, 0, 6], [9, 0, 9]]
    non = [1, 0, 4]
    base_root = state_root(accounts, assets, bal, sup, non)
    variants = {
        "balance": state_root(accounts, assets, [[5, 0], [0, 8], [1, 2]], sup, non),
        "supply": state_root(accounts, assets, bal, [[6, 0, 6], [9, 1, 8]], non),
        "nonce": state_root(accounts, assets, bal, sup, [1, 1, 4]),
        "accounts": state_root(4, assets, bal + [[0, 0]], sup, non),
        "swap_accounts": state_root(accounts, assets, [bal[1], bal[0], bal[2]], sup, non),
        "swap_assets": state_root(accounts, assets, [[0, 5], [7, 0], [2, 1]], sup, non),
    }
    assert len({base_root, *variants.values()}) == 1 + len(variants)
    print("SENSITIVITY=%d" % len(variants))
    # 4. vectors
    vec_trees = []
    for name, e in [("empty", {}), ("one", {1: b"\x01"}), ("three", {0: b"a", 2**63: b"b", 2**64 - 1: b"c"}), ("random8", {k: rnd.getrandbits(128).to_bytes(16, "big") for k in [rnd.getrandbits(64) for _ in range(8)]})]:
        rt_e = root(e)
        probe = sorted(e)[0] if e else 7
        sibs, val = prove(e, probe)
        absent = 2**64 - 2 if (2**64 - 2) not in e else 3
        sibs2, val2 = prove(e, absent)
        vec_trees.append({"name": name, "entries": [[str(k), v.hex()] for k, v in sorted(e.items())],
                          "root": rt_e.hex(),
                          "proof_key": str(probe), "proof_value": None if val is None else val.hex(), "proof_siblings": [s.hex() for s in sibs],
                          "absent_key": str(absent), "absent_siblings": [s.hex() for s in sibs2]})
    t = json.load(open(os.path.join(base, "engineering/ledger_core/results/machine_trace_v0.json")))["trace"]
    fb = [[int(x) for x in row] for row in t["final"]["balances"]]
    fs = [[int(x) for x in row] for row in t["final"]["supply"]]
    fn = [int(x) for x in t["final_nonces"]]
    sroot = state_root(t["accounts"], t["assets"], fb, fs, fn)
    out = {"format": "SIRM state commitment reference vectors v0",
           "empty_levels": [EMPTY[i].hex() for i in (0, 1, 2, 64)],
           "trees": vec_trees,
           "machine_final_state_root": sroot.hex(),
           "sensitivity_base": {"accounts": accounts, "assets": assets, "balances": bal, "supply": sup, "nonces": non, "root": base_root.hex(),
                                "variants": {k: v.hex() for k, v in variants.items()}}}
    path = os.path.join(base, "engineering/canonical_encoding/results/state_commitment_vectors_v0.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=1, sort_keys=True)
        f.write("\n")
    print("RESULT_JSON=engineering/canonical_encoding/results/state_commitment_vectors_v0.json")


if __name__ == "__main__":
    main()
