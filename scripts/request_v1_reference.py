#!/usr/bin/env python3
"""Canonical request encoding v1 (PROPOSAL, not adopted): the ten operations of the integrated
state machine. Independent of the Rust codec. Spec: engineering/canonical_encoding/SPEC_request_v1.md.
Vectors: engineering/canonical_encoding/results/request_v1_vectors.json.

Layout (big-endian, fixed width per operation tag, no optional fields):
  domain "SIRM/FTX/v1\\0" (12) | request id (32) | principal u32 | nonce u64 | tag u8 | fields
  0 transfer: source u32, destination u32, asset u32, amount u128
  1 issue:    issuer u32, recipient u32, asset u32, amount u128
  2 burn:     holder u32, asset u32, amount u128
  3 open:     id u32, depositor u32, beneficiary u32, asset u32, amount u128
  4 release:  id u32      5 cancel: id u32      6 expire: id u32
  7 dispute:  id u32, claimant u32
  8 advance:  time u64
  9 migrate:  amount u128
"""
import hashlib, itertools, json, os, sys
from pathlib import Path

DOMAIN = b"SIRM/FTX/v1\x00"
U32, U64, U128 = 2**32, 2**64, 2**128
TAGS = {"transfer": 0, "issue": 1, "burn": 2, "open": 3, "release": 4, "cancel": 5, "expire": 6,
        "dispute": 7, "advance": 8, "migrate": 9}
INV = {v: k for k, v in TAGS.items()}
# field widths in bytes, in order
SHAPE = {"transfer": (4, 4, 4, 16), "issue": (4, 4, 4, 16), "burn": (4, 4, 16),
         "open": (4, 4, 4, 4, 16), "release": (4,), "cancel": (4,), "expire": (4,),
         "dispute": (4, 4), "advance": (8,), "migrate": (16,)}
PREFIX = len(DOMAIN) + 32 + 4 + 8 + 1


class EncodingError(ValueError):
    pass


def _u(v, width, name):
    if not isinstance(v, int) or isinstance(v, bool) or not 0 <= v < 256 ** width:
        raise EncodingError(f"{name} out of range: {v!r}")
    return v.to_bytes(width, "big")


def encode(req):
    """req = {request_id: bytes(32), principal, nonce, op: (kind, fields...)}"""
    rid = req["request_id"]
    if not isinstance(rid, bytes) or len(rid) != 32:
        raise EncodingError("request_id must be 32 bytes")
    kind, *f = req["op"]
    if kind not in TAGS or len(f) != len(SHAPE[kind]):
        raise EncodingError("bad operation")
    out = DOMAIN + rid + _u(req["principal"], 4, "principal") + _u(req["nonce"], 8, "nonce") + bytes([TAGS[kind]])
    for v, w in zip(f, SHAPE[kind]):
        out += _u(v, w, kind)
    return out


def decode(b):
    if not b.startswith(DOMAIN):
        raise EncodingError("bad domain tag")
    if len(b) < PREFIX:
        raise EncodingError("truncated")
    rid = b[12:44]
    principal = int.from_bytes(b[44:48], "big")
    nonce = int.from_bytes(b[48:56], "big")
    tag = b[56]
    if tag not in INV:
        raise EncodingError("unknown operation tag")
    kind = INV[tag]
    need = PREFIX + sum(SHAPE[kind])
    if len(b) < need:
        raise EncodingError("truncated")
    if len(b) > need:
        raise EncodingError("trailing bytes")
    p, f = PREFIX, []
    for w in SHAPE[kind]:
        f.append(int.from_bytes(b[p:p + w], "big")); p += w
    return {"request_id": rid, "principal": principal, "nonce": nonce, "op": (kind, *f)}


def rid_of(n):
    """Request ids of the reference traces (small integers) as 32-byte ids."""
    return bytes(24) + n.to_bytes(8, "big")


def trace_request(row):
    """A row of integrated_trace_v0.json -> request dict."""
    rid, p, nonce, op, *a = row
    a = [None if x is None else int(x) for x in a]
    if op == "burn":
        a = [a[0], a[2], a[3]]          # the reference carries a placeholder for the second account
    return {"request_id": rid_of(rid), "principal": p, "nonce": nonce, "op": (op, *a)}


def vectors():
    rid = bytes(range(32))
    mx = {"u32": U32 - 1, "u64": U64 - 1, "u128": U128 - 1}
    vs = [
        ("transfer_min", bytes(32), 0, 0, ("transfer", 0, 0, 0, 0)),
        ("transfer_basic", rid, 1, 7, ("transfer", 1, 2, 3, 1000)),
        ("issue_basic", rid, 2, 0, ("issue", 2, 5, 0, 10**18)),
        ("burn_basic", rid, 3, 41, ("burn", 3, 1, 25)),
        ("open_basic", rid, 0, 3, ("open", 2, 0, 1, 0, 500)),
        ("release_basic", rid, 1, 4, ("release", 2)),
        ("cancel_basic", rid, 1, 5, ("cancel", 0)),
        ("expire_basic", rid, 2, 6, ("expire", 1)),
        ("dispute_basic", rid, 2, 7, ("dispute", 1, 3)),
        ("advance_basic", rid, 0, 8, ("advance", 1_800_000_000)),
        ("migrate_basic", rid, 1, 9, ("migrate", 123456789)),
        ("max_transfer", b"\xff" * 32, mx["u32"], mx["u64"], ("transfer", *[mx["u32"]] * 3, mx["u128"])),
        ("max_open", b"\xff" * 32, mx["u32"], mx["u64"], ("open", *[mx["u32"]] * 4, mx["u128"])),
        ("max_advance", b"\xff" * 32, mx["u32"], mx["u64"], ("advance", mx["u64"])),
        ("max_migrate", b"\xff" * 32, mx["u32"], mx["u64"], ("migrate", mx["u128"])),
        ("max_dispute", b"\xff" * 32, mx["u32"], mx["u64"], ("dispute", mx["u32"], mx["u32"])),
    ]
    return [{"name": n, "request_id": r, "principal": p, "nonce": nc, "op": op} for n, r, p, nc, op in vs]


def selfcheck(root):
    res = {}
    for v in vectors():
        r = {k: v[k] for k in ("request_id", "principal", "nonce", "op")}
        assert decode(encode(r)) == r, v["name"]
    res["vectors_roundtrip"] = len(vectors())

    # exhaustive small domain over all ten operations: injective, round trip, re-encode identical
    seen, small = {}, [0, 1, 2]
    amounts = [0, 1, 255, 256]
    for pr, nc in itertools.product(small, small):
        for kind, shape in SHAPE.items():
            doms = [small if w == 4 else (amounts if w == 16 else [0, 1, 2**40]) for w in shape]
            for f in itertools.product(*doms):
                r = {"request_id": bytes([pr]) * 32, "principal": pr, "nonce": nc, "op": (kind, *f)}
                e = encode(r)
                assert e not in seen, "collision"
                seen[e] = r
                assert decode(e) == r and encode(decode(e)) == e
    res["injectivity_roundtrip_cases"] = len(seen)

    good = encode(vectors()[1])
    bad = {"truncated": good[:-1], "trailing": good + b"\x00", "bad_domain": b"X" + good[1:],
           "v0_domain": b"SIRM/FTX/v0\x00" + good[12:], "empty": b"", "domain_only": DOMAIN}
    for name, blob in bad.items():
        try:
            decode(blob); raise SystemExit(f"accepted malformed: {name}")
        except EncodingError:
            pass
    res["malformed_rejected"] = len(bad)
    unknown = 0
    for t in range(256):
        blob = good[:56] + bytes([t]) + good[57:]
        if t in INV:
            continue
        try:
            decode(blob); raise SystemExit(f"accepted unknown tag {t}")
        except EncodingError:
            unknown += 1
    res["unknown_tags_rejected"] = unknown
    # a tag change to another valid tag must not decode unless the length matches exactly
    changed = 0
    for v in vectors():
        e = encode({k: v[k] for k in ("request_id", "principal", "nonce", "op")})
        for t in INV:
            if t == e[56]:
                continue
            m = e[:56] + bytes([t]) + e[57:]
            try:
                d = decode(m)
            except EncodingError:
                changed += 1
                continue
            assert encode(d) == m and d["op"][0] != v["op"][0]
    res["tag_changes_checked"] = changed
    # every single-byte mutation of every vector: rejected, or decodes to a different request
    # whose canonical encoding is exactly the mutated bytes
    muts = 0
    for v in vectors():
        e = encode({k: v[k] for k in ("request_id", "principal", "nonce", "op")})
        for i in range(len(e)):
            m = e[:i] + bytes([e[i] ^ 0x01]) + e[i + 1:]
            try:
                d = decode(m)
            except EncodingError:
                muts += 1
                continue
            assert encode(d) == m, "non-canonical input accepted"
            muts += 1
    res["single_byte_mutations_checked"] = muts
    for r in [{"request_id": bytes(32), "principal": U32, "nonce": 0, "op": ("release", 0)},
              {"request_id": bytes(32), "principal": 0, "nonce": U64, "op": ("release", 0)},
              {"request_id": bytes(32), "principal": 0, "nonce": 0, "op": ("advance", U64)},
              {"request_id": bytes(32), "principal": 0, "nonce": 0, "op": ("migrate", U128)},
              {"request_id": bytes(32), "principal": 0, "nonce": 0, "op": ("open", 0, 0, 0, 0, -1)},
              {"request_id": bytes(32), "principal": 0, "nonce": 0, "op": ("release",)},
              {"request_id": bytes(32), "principal": 0, "nonce": 0, "op": ("burn", 0, 0, 0, 0)},
              {"request_id": bytes(31), "principal": 0, "nonce": 0, "op": ("release", 0)}]:
        try:
            encode(r); raise SystemExit(f"accepted invalid request: {r}")
        except EncodingError:
            pass
    res["invalid_requests_rejected"] = 8

    # the whole integrated reference trace encodes, round-trips and has a stable aggregate digest
    d = json.load(open(root / "engineering/ledger_core/results/integrated_trace_v0.json"))
    agg, n = hashlib.sha256(), 0
    for ep in d["episodes"]:
        for row in ep["requests"]:
            r = trace_request(row)
            e = encode(r)
            assert decode(e) == r
            agg.update(hashlib.sha256(e).digest())
            n += 1
    res["trace_requests"] = n
    res["trace_aggregate_sha256"] = agg.hexdigest()
    return res


def main():
    root = Path(__file__).resolve().parent.parent
    res = selfcheck(root)
    out = Path(sys.argv[1] if len(sys.argv) > 1 else root / "engineering/canonical_encoding/results/request_v1_vectors.json")
    doc = {"format": "SIRM canonical request encoding vectors v1", "domain": DOMAIN.decode().replace("\x00", "\\0"),
           "checks": res,
           "vectors": [{"name": v["name"], "request_id": v["request_id"].hex(), "principal": v["principal"],
                        "nonce": str(v["nonce"]), "op": [v["op"][0], *[str(x) for x in v["op"][1:]]],
                        "hex": encode({k: v[k] for k in ("request_id", "principal", "nonce", "op")}).hex()}
                       for v in vectors()]}
    out.write_text(json.dumps(doc, indent=1, sort_keys=True) + "\n")
    print(json.dumps(res, indent=1))
    print("RESULT_JSON=" + str(out))


if __name__ == "__main__":
    main()
