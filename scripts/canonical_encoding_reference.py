#!/usr/bin/env python3
"""Reference canonical byte encoding for FinancialTransactionRequest (v0 PROPOSAL).

Executable specification + test vectors for a future Rust implementation.
It mirrors SIRM/FinancialTransactionEnvelope.lean (principal, nonce, operation)
plus an opaque 32-byte request ID. It is NOT proved against the Lean model:
Lean uses unbounded Nat, this encoding is bounded (u64 nonce, u128 amount) and
rejects out-of-range values explicitly. Signatures, expiry and chain id are out of scope.
"""
import hashlib, itertools, json, sys
from pathlib import Path

DOMAIN = b"SIRM/FTX/v0\x00"          # 12 bytes, fixed
OPS = {"transfer": 0, "issue": 1, "burn": 2}
OPS_INV = {v: k for k, v in OPS.items()}
U32, U64, U128 = 2**32, 2**64, 2**128

class EncodingError(ValueError):
    pass

def _u(v, bound, n, name):
    if not isinstance(v, int) or isinstance(v, bool) or not 0 <= v < bound:
        raise EncodingError(f"{name} out of range: {v!r}")
    return v.to_bytes(n, "big")

def encode(req):
    """req = {request_id: bytes(32), principal, nonce, op: (kind, fields...)}"""
    rid = req["request_id"]
    if not isinstance(rid, bytes) or len(rid) != 32:
        raise EncodingError("request_id must be 32 bytes")
    kind, *f = req["op"]
    if kind not in OPS:
        raise EncodingError("unknown operation")
    out = DOMAIN + rid + _u(req["principal"], U32, 4, "principal") + _u(req["nonce"], U64, 8, "nonce")
    out += bytes([OPS[kind]])
    if kind == "transfer":
        src, dst, asset, amt = f
        out += _u(src, U32, 4, "source") + _u(dst, U32, 4, "destination") + _u(asset, U32, 4, "asset") + _u(amt, U128, 16, "amount")
    elif kind == "issue":
        iss, rcp, asset, amt = f
        out += _u(iss, U32, 4, "issuer") + _u(rcp, U32, 4, "recipient") + _u(asset, U32, 4, "asset") + _u(amt, U128, 16, "amount")
    else:
        h, asset, amt = f
        out += _u(h, U32, 4, "holder") + _u(asset, U32, 4, "asset") + _u(amt, U128, 16, "amount")
    return out

def decode(b):
    if not b.startswith(DOMAIN):
        raise EncodingError("bad domain tag")
    p = len(DOMAIN)
    def take(n):
        nonlocal p
        if p + n > len(b):
            raise EncodingError("truncated")
        v = b[p:p + n]; p += n; return v
    rid = take(32)
    principal = int.from_bytes(take(4), "big"); nonce = int.from_bytes(take(8), "big")
    tag = take(1)[0]
    if tag not in OPS_INV:
        raise EncodingError("unknown operation tag")
    kind = OPS_INV[tag]
    n32 = {"transfer": 3, "issue": 3, "burn": 2}[kind]
    ids = [int.from_bytes(take(4), "big") for _ in range(n32)]
    amt = int.from_bytes(take(16), "big")
    if p != len(b):
        raise EncodingError("trailing bytes")
    op = (kind, *ids, amt)
    return {"request_id": rid, "principal": principal, "nonce": nonce, "op": op}

def digest(b):
    return hashlib.sha256(b).hexdigest()

def vectors():
    rid = bytes(range(32))
    base = [
        {"name": "transfer_min", "request_id": bytes(32), "principal": 0, "nonce": 0, "op": ("transfer", 0, 0, 0, 0)},
        {"name": "transfer_basic", "request_id": rid, "principal": 1, "nonce": 7, "op": ("transfer", 1, 2, 3, 1000)},
        {"name": "issue_basic", "request_id": rid, "principal": 2, "nonce": 0, "op": ("issue", 2, 5, 0, 10**18)},
        {"name": "burn_basic", "request_id": rid, "principal": 3, "nonce": 41, "op": ("burn", 3, 1, 25)},
        {"name": "max_values", "request_id": b"\xff" * 32, "principal": U32 - 1, "nonce": U64 - 1, "op": ("transfer", U32 - 1, U32 - 1, U32 - 1, U128 - 1)},
    ]
    return base

def selfcheck():
    res = {}
    # 1. round trip on boundary vectors
    for v in vectors():
        r = {k: v[k] for k in ("request_id", "principal", "nonce", "op")}
        assert decode(encode(r)) == r, v["name"]
    res["vectors_roundtrip"] = len(vectors())
    # 2. exhaustive small-domain injectivity + roundtrip
    seen = {}
    small = [0, 1, 2]
    reqs = []
    for pr, nc in itertools.product(small, small):
        for a, b2, c, amt in itertools.product(small, small, small, [0, 1, 255, 256]):
            reqs.append({"request_id": bytes([pr]) * 32, "principal": pr, "nonce": nc, "op": ("transfer", a, b2, c, amt)})
            reqs.append({"request_id": bytes([pr]) * 32, "principal": pr, "nonce": nc, "op": ("issue", a, b2, c, amt)})
        for a, c, amt in itertools.product(small, small, [0, 1, 255, 256]):
            reqs.append({"request_id": bytes([pr]) * 32, "principal": pr, "nonce": nc, "op": ("burn", a, c, amt)})
    for r in reqs:
        e = encode(r)
        assert e not in seen, "collision"
        seen[e] = r
        assert decode(e) == r
    res["injectivity_roundtrip_cases"] = len(reqs)
    # 3. rejection of non-canonical / malformed input
    good = encode(vectors()[1] | {})
    bad = {"truncated": good[:-1], "trailing": good + b"\x00", "bad_domain": b"X" + good[1:],
           "bad_tag": good[:len(DOMAIN) + 32 + 12] + b"\x09" + good[len(DOMAIN) + 32 + 13:]}
    for name, blob in bad.items():
        try:
            decode(blob); raise SystemExit(f"accepted malformed: {name}")
        except EncodingError:
            pass
    res["malformed_rejected"] = len(bad)
    for r, why in [({"request_id": bytes(32), "principal": U32, "nonce": 0, "op": ("burn", 0, 0, 0)}, "principal"),
                   ({"request_id": bytes(32), "principal": 0, "nonce": U64, "op": ("burn", 0, 0, 0)}, "nonce"),
                   ({"request_id": bytes(32), "principal": 0, "nonce": 0, "op": ("burn", 0, 0, U128)}, "amount"),
                   ({"request_id": bytes(32), "principal": 0, "nonce": -1, "op": ("burn", 0, 0, 0)}, "negative")]:
        try:
            encode(r); raise SystemExit(f"accepted out-of-range: {why}")
        except EncodingError:
            pass
    res["out_of_range_rejected"] = 4
    return res

def main():
    out = Path(sys.argv[1] if len(sys.argv) > 1 else "engineering/canonical_encoding/results/vectors_v0.json")
    res = selfcheck()
    vs = []
    for v in vectors():
        r = {k: v[k] for k in ("request_id", "principal", "nonce", "op")}
        e = encode(r)
        vs.append({"name": v["name"], "request_id": r["request_id"].hex(), "principal": r["principal"],
                   "nonce": r["nonce"], "op": [r["op"][0], *[str(x) for x in r["op"][1:]]],
                   "bytes_hex": e.hex(), "length": len(e), "sha256": digest(e)})
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({"format": "SIRM/FTX/v0 (proposal)", "checks": res, "vectors": vs}, indent=2, sort_keys=True) + "\n")
    for k, v in res.items():
        print(f"{k.upper()}={v}")
    print("RESULT_JSON=" + str(out))

if __name__ == "__main__":
    main()
