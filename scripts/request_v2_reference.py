#!/usr/bin/env python3
"""Canonical request encoding v2 (PROPOSAL, not adopted): request encoding v1 plus the arbiter
operation `resolve`. Independent of the Rust codec. Spec: engineering/canonical_encoding/SPEC_request_v2.md.
Vectors: engineering/canonical_encoding/results/request_v2_vectors.json.

Layout (big-endian, fixed width per operation tag, no optional fields):
  domain "SIRM/FTX/v2\\0" (12) | request id (32) | principal u32 | nonce u64 | tag u8 | fields
  tags 0-9 and their fields are exactly those of request encoding v1 (only the domain differs)
  10 resolve: id u32, to_beneficiary u8 (0 = depositor, 1 = beneficiary; any other value is rejected)
Request encoding v1 and its frozen vectors are unchanged.
"""
import hashlib, itertools, json, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import request_v1_reference as v1  # tables and trace helpers of v1 (the v2 codec below is its own)

DOMAIN = b"SIRM/FTX/v2\x00"
U32, U64, U128 = v1.U32, v1.U64, v1.U128
TAGS = dict(v1.TAGS, resolve=10)
INV = {v: k for k, v in TAGS.items()}
SHAPE = dict(v1.SHAPE, resolve=(4, 1))
PREFIX = len(DOMAIN) + 32 + 4 + 8 + 1


class EncodingError(ValueError):
    pass


def _u(v, width, name):
    if not isinstance(v, int) or isinstance(v, bool) or not 0 <= v < 256 ** width:
        raise EncodingError(f"{name} out of range: {v!r}")
    return v.to_bytes(width, "big")


def encode(req):
    rid = req["request_id"]
    if not isinstance(rid, bytes) or len(rid) != 32:
        raise EncodingError("request_id must be 32 bytes")
    kind, *f = req["op"]
    if kind not in TAGS or len(f) != len(SHAPE[kind]):
        raise EncodingError("bad operation")
    if kind == "resolve" and f[1] not in (0, 1):
        raise EncodingError("to_beneficiary must be 0 or 1")
    out = DOMAIN + rid + _u(req["principal"], 4, "principal") + _u(req["nonce"], 8, "nonce") + bytes([TAGS[kind]])
    for v, w in zip(f, SHAPE[kind]):
        out += _u(v, w, kind)
    return out


def decode(b):
    if not b.startswith(DOMAIN):
        raise EncodingError("bad domain tag")
    if len(b) < PREFIX:
        raise EncodingError("truncated")
    rid, principal, nonce, tag = b[12:44], int.from_bytes(b[44:48], "big"), int.from_bytes(b[48:56], "big"), b[56]
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
    if kind == "resolve" and f[1] not in (0, 1):
        raise EncodingError("non-canonical to_beneficiary")
    return {"request_id": rid, "principal": principal, "nonce": nonce, "op": (kind, *f)}


def vectors():
    rid = bytes(range(32))
    mx32, mx64 = U32 - 1, U64 - 1
    old = [(n, r, p, nc, op) for n, r, p, nc, op in
           [(v["name"], v["request_id"], v["principal"], v["nonce"], v["op"]) for v in v1.vectors()]]
    new = [
        ("resolve_beneficiary", rid, 4, 10, ("resolve", 2, 1)),
        ("resolve_depositor", rid, 4, 11, ("resolve", 0, 0)),
        ("max_resolve", b"\xff" * 32, mx32, mx64, ("resolve", mx32, 1)),
    ]
    return [{"name": n, "request_id": r, "principal": p, "nonce": nc, "op": op} for n, r, p, nc, op in old + new]


def _req(v):
    return {k: v[k] for k in ("request_id", "principal", "nonce", "op")}


def aggregate(path):
    d = json.load(open(path))
    agg, n, kinds = hashlib.sha256(), 0, {}
    for ep in d["episodes"]:
        for row in ep["requests"]:
            r = v1.trace_request(row)
            e = encode(r)
            assert decode(e) == r
            agg.update(hashlib.sha256(e).digest())
            n += 1
            kinds[r["op"][0]] = kinds.get(r["op"][0], 0) + 1
    return n, agg.hexdigest(), kinds


def selfcheck(root):
    res = {}
    for v in vectors():
        assert decode(encode(_req(v))) == _req(v), v["name"]
    res["vectors_roundtrip"] = len(vectors())

    seen, small, amounts = {}, [0, 1, 2], [0, 1, 255, 256]
    for pr, nc in itertools.product(small, small):
        for kind, shape in SHAPE.items():
            if kind == "resolve":
                doms = [small, [0, 1]]
            else:
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
           "v0_domain": b"SIRM/FTX/v0\x00" + good[12:], "v1_domain": v1.DOMAIN + good[12:],
           "empty": b"", "domain_only": DOMAIN}
    for name, blob in bad.items():
        try:
            decode(blob); raise SystemExit(f"accepted malformed: {name}")
        except EncodingError:
            pass
    res["malformed_rejected"] = len(bad)
    # cross-version: a v1 encoding is not a v2 encoding and the other way round
    for v in vectors():
        if v["op"][0] == "resolve":
            try:
                v1.decode(v1.DOMAIN + encode(_req(v))[12:]); raise SystemExit("v1 accepted resolve")
            except v1.EncodingError:
                pass
        else:
            assert v1.decode(v1.encode(_req(v))) == _req(v)
            assert encode(_req(v))[12:] == v1.encode(_req(v))[12:], "v2 differs from v1 beyond the domain"
    res["v1_v2_agree_except_domain_and_resolve"] = True

    unknown = 0
    for t in range(256):
        if t in INV:
            continue
        try:
            decode(good[:56] + bytes([t]) + good[57:]); raise SystemExit(f"accepted unknown tag {t}")
        except EncodingError:
            unknown += 1
    res["unknown_tags_rejected"] = unknown

    rv = encode({"request_id": bytes(32), "principal": 0, "nonce": 0, "op": ("resolve", 1, 1)})
    flags = 0
    for fl in range(2, 256):
        try:
            decode(rv[:-1] + bytes([fl])); raise SystemExit(f"accepted flag {fl}")
        except EncodingError:
            flags += 1
    res["resolve_flag_values_rejected"] = flags

    changed = 0
    for v in vectors():
        e = encode(_req(v))
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

    muts = 0
    for v in vectors():
        e = encode(_req(v))
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

    base = {"request_id": bytes(32), "principal": 0, "nonce": 0}
    invalid = [dict(base, principal=U32, op=("release", 0)), dict(base, nonce=U64, op=("release", 0)),
               dict(base, op=("advance", U64)), dict(base, op=("migrate", U128)),
               dict(base, op=("open", 0, 0, 0, 0, -1)), dict(base, op=("release",)),
               dict(base, op=("burn", 0, 0, 0, 0)), dict(base, request_id=bytes(31), op=("release", 0)),
               dict(base, op=("resolve", 0, 2)), dict(base, op=("resolve", 0, -1)),
               dict(base, op=("resolve", U32, 0)), dict(base, op=("resolve", 0))]
    for r in invalid:
        try:
            encode(r); raise SystemExit(f"accepted invalid request: {r}")
        except EncodingError:
            pass
    res["invalid_requests_rejected"] = len(invalid)

    n, h, _ = aggregate(root / "engineering/ledger_core/results/integrated_trace_v0.json")
    res["trace_requests"], res["trace_aggregate_sha256"] = n, h
    n, h, kinds = aggregate(root / "engineering/ledger_core/results/integrated_resolve_trace_v0.json")
    assert kinds.get("resolve", 0) >= 100
    res["resolve_trace_requests"], res["resolve_trace_resolve_requests"] = n, kinds["resolve"]
    res["resolve_trace_aggregate_sha256"] = h
    return res


def main():
    root = HERE.parent
    res = selfcheck(root)
    out = Path(sys.argv[1] if len(sys.argv) > 1 else root / "engineering/canonical_encoding/results/request_v2_vectors.json")
    doc = {"format": "SIRM canonical request encoding vectors v2", "domain": DOMAIN.decode().replace("\x00", "\\0"),
           "checks": res,
           "vectors": [{"name": v["name"], "request_id": v["request_id"].hex(), "principal": v["principal"],
                        "nonce": str(v["nonce"]), "op": [v["op"][0], *[str(x) for x in v["op"][1:]]],
                        "hex": encode(_req(v)).hex()} for v in vectors()]}
    out.write_text(json.dumps(doc, indent=1, sort_keys=True) + "\n")
    print(json.dumps(res, indent=1))
    print("RESULT_JSON=" + str(out))


if __name__ == "__main__":
    main()
