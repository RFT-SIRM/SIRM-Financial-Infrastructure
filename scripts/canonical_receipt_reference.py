#!/usr/bin/env python3
"""Reference canonical byte encoding for transaction receipts (v0 PROPOSAL).

Executable specification + vectors for SIRM.FinancialTransactionEnvelope
(`FinancialTransactionReceipt`, success) and SIRM.FinancialTransactionDenials
(`FinancialTransactionDenialReceipt`, authorization / insufficient-funds denial).
A receipt binds the exact request payload (its canonical v0 encoding, which carries the
request ID) to the stored response. Not proved against Lean: Lean uses unbounded Nat.

Layout (big-endian, fixed width per variant):
  domain 12 = b"SIRM/RCT/v0\\0" | status 1 (0 accepted, 1 denied) | request encoding (85 or 81)
  accepted: accepted_nonce u64 | next_nonce u64
  denied:   expected_nonce u64 | reason u8
Reason codes follow the Lean enum order: 0 transferAuthorizationDenied, 1 issueAuthorizationDenied,
2 burnAuthorizationDenied, 3 transferInsufficientFunds, 4 burnInsufficientFunds.
The response request ID of Lean is the request ID inside the embedded request encoding.
Decoder-enforced consistency (all from the Lean construction/invariants): accepted_nonce equals
the request nonce and next_nonce = accepted_nonce + 1; a denial's expected_nonce equals the request
nonce (denials are only cached at the exact current nonce) and its reason matches the operation family.
"""
import hashlib, itertools, json, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import canonical_encoding_reference as rq

DOMAIN = b"SIRM/RCT/v0\x00"
REASONS = ["transferAuthorizationDenied", "issueAuthorizationDenied", "burnAuthorizationDenied",
           "transferInsufficientFunds", "burnInsufficientFunds"]
ALLOWED = {"transfer": {0, 3}, "issue": {1}, "burn": {2, 4}}
REQ_LEN = {0: 85, 1: 85, 2: 81}
U64 = 2**64

class ReceiptError(ValueError):
    pass

def _check_response(req, resp):
    kind = req["op"][0]
    if resp[0] == "accepted":
        _, acc, nxt = resp
        if acc != req["nonce"]:
            raise ReceiptError("accepted nonce differs from request nonce")
        if nxt != acc + 1:
            raise ReceiptError("next nonce must be accepted nonce + 1")
    elif resp[0] == "denied":
        _, exp, reason = resp
        if exp != req["nonce"]:
            raise ReceiptError("expected nonce differs from request nonce")
        if reason not in REASONS or REASONS.index(reason) not in ALLOWED[kind]:
            raise ReceiptError("reason does not match the operation family")
    else:
        raise ReceiptError("unknown response kind")

def encode(req, resp):
    _check_response(req, resp)
    try:
        body = rq.encode(req)
    except rq.EncodingError as e:
        raise ReceiptError(str(e))
    if resp[0] == "accepted":
        if resp[2] >= U64:
            raise ReceiptError("next nonce out of range")
        return DOMAIN + b"\x00" + body + resp[1].to_bytes(8, "big") + resp[2].to_bytes(8, "big")
    return DOMAIN + b"\x01" + body + resp[1].to_bytes(8, "big") + bytes([REASONS.index(resp[2])])

def decode(b):
    if not b.startswith(DOMAIN):
        raise ReceiptError("bad domain tag")
    p = len(DOMAIN)
    if len(b) < p + 1 + 69 + 1:
        raise ReceiptError("truncated")
    status = b[p]
    if status not in (0, 1):
        raise ReceiptError("unknown status")
    start = p + 1
    tag = b[start + 12 + 32 + 4 + 8]
    if tag not in REQ_LEN:
        raise ReceiptError("unknown operation tag")
    end = start + REQ_LEN[tag]
    tail = 16 if status == 0 else 9
    if len(b) < end + tail:
        raise ReceiptError("truncated")
    if len(b) > end + tail:
        raise ReceiptError("trailing bytes")
    try:
        req = rq.decode(b[start:end])
    except rq.EncodingError as e:
        raise ReceiptError(str(e))
    if status == 0:
        resp = ("accepted", int.from_bytes(b[end:end + 8], "big"), int.from_bytes(b[end + 8:end + 16], "big"))
    else:
        code = b[end + 8]
        if code >= len(REASONS):
            raise ReceiptError("unknown reason code")
        resp = ("denied", int.from_bytes(b[end:end + 8], "big"), REASONS[code])
    _check_response(req, resp)
    return req, resp

def digest(b):
    return hashlib.sha256(b).hexdigest()

def vectors():
    rid = bytes(range(32))
    reqs = {
        "transfer": {"request_id": rid, "principal": 1, "nonce": 7, "op": ("transfer", 1, 2, 3, 1000)},
        "issue": {"request_id": rid, "principal": 2, "nonce": 0, "op": ("issue", 2, 5, 0, 10**18)},
        "burn": {"request_id": rid, "principal": 3, "nonce": 41, "op": ("burn", 3, 1, 25)},
        "max": {"request_id": b"\xff" * 32, "principal": 2**32 - 1, "nonce": 2**64 - 2,
                "op": ("transfer", 2**32 - 1, 2**32 - 1, 2**32 - 1, 2**128 - 1)},
    }
    out = []
    for name, r in reqs.items():
        out.append((f"accepted_{name}", r, ("accepted", r["nonce"], r["nonce"] + 1)))
        for code in sorted(ALLOWED[r["op"][0]]):
            out.append((f"denied_{name}_{REASONS[code]}", r, ("denied", r["nonce"], REASONS[code])))
    return out

def selfcheck():
    res = {}
    vs = vectors()
    for name, r, resp in vs:
        assert decode(encode(r, resp)) == (r, resp), name
    res["vectors_roundtrip"] = len(vs)
    # exhaustive small domain: distinct bytes, exact round trip, exact lengths
    small, seen, n = [0, 1, 2], {}, 0
    for pr, nc in itertools.product(small, small):
        reqs = []
        for a, b2, c, amt in itertools.product(small, small, small, [0, 1, 256]):
            reqs.append({"request_id": bytes([pr]) * 32, "principal": pr, "nonce": nc, "op": ("transfer", a, b2, c, amt)})
            reqs.append({"request_id": bytes([pr]) * 32, "principal": pr, "nonce": nc, "op": ("issue", a, b2, c, amt)})
        for a, c, amt in itertools.product(small, small, [0, 1, 256]):
            reqs.append({"request_id": bytes([pr]) * 32, "principal": pr, "nonce": nc, "op": ("burn", a, c, amt)})
        for r in reqs:
            resps = [("accepted", nc, nc + 1)] + [("denied", nc, REASONS[k]) for k in sorted(ALLOWED[r["op"][0]])]
            for resp in resps:
                e = encode(r, resp)
                assert e not in seen, "collision"
                seen[e] = (r, resp)
                assert decode(e) == (r, resp)
                assert len(e) == 13 + (81 if r["op"][0] == "burn" else 85) + (16 if resp[0] == "accepted" else 9)
                assert not e.startswith(rq.DOMAIN)
                n += 1
    res["injectivity_roundtrip_cases"] = n
    # rejection of malformed / inconsistent receipts
    r, resp = vs[0][1], vs[0][2]
    good = encode(r, resp)
    dn = encode(r, ("denied", r["nonce"], "transferAuthorizationDenied"))
    L = len(DOMAIN) + 1
    bad = {
        "truncated": good[:-1], "trailing": good + b"\x00", "bad_domain": b"X" + good[1:],
        "bad_status": good[:len(DOMAIN)] + b"\x02" + good[len(DOMAIN) + 1:],
        "bad_op_tag": good[:L + 56] + b"\x09" + good[L + 57:],
        "embedded_bad_request_domain": good[:L] + b"X" + good[L + 1:],
        "accepted_nonce_differs": good[:-16] + (r["nonce"] + 1).to_bytes(8, "big") + (r["nonce"] + 2).to_bytes(8, "big"),
        "next_not_plus_one": good[:-8] + (r["nonce"] + 5).to_bytes(8, "big"),
        "denied_expected_differs": dn[:-9] + (r["nonce"] + 1).to_bytes(8, "big") + dn[-1:],
        "denied_unknown_reason": dn[:-1] + b"\x05",
        "denied_reason_wrong_family": dn[:-1] + b"\x01",
        "request_bytes_as_receipt": rq.encode(r),
    }
    for name, blob in bad.items():
        try:
            decode(blob); raise SystemExit(f"accepted malformed: {name}")
        except ReceiptError:
            pass
    res["malformed_rejected"] = len(bad)
    # encoder rejections
    enc_bad = [
        (r, ("accepted", r["nonce"] + 1, r["nonce"] + 2)),
        (r, ("accepted", r["nonce"], r["nonce"])),
        (vs[-1][1] | {"nonce": 2**64 - 1}, ("accepted", 2**64 - 1, 2**64)),
        (r, ("denied", r["nonce"] + 1, "transferAuthorizationDenied")),
        (r, ("denied", r["nonce"], "issueAuthorizationDenied")),
        (r, ("denied", r["nonce"], "nonsense")),
        (r, ("pending", 0, 0)),
    ]
    for req, resp in enc_bad:
        try:
            encode(req, resp); raise SystemExit(f"accepted inconsistent receipt: {resp}")
        except ReceiptError:
            pass
    res["encoder_rejections"] = len(enc_bad)
    return res

def main():
    out = Path(sys.argv[1] if len(sys.argv) > 1 else "engineering/canonical_encoding/results/receipt_vectors_v0.json")
    res = selfcheck()
    vs = []
    for name, r, resp in vectors():
        e = encode(r, resp)
        vs.append({"name": name, "request_id": r["request_id"].hex(), "principal": r["principal"], "nonce": r["nonce"],
                   "op": [r["op"][0], *[str(x) for x in r["op"][1:]]],
                   "response": [resp[0], str(resp[1]), str(resp[2]) if resp[0] == "accepted" else resp[2]],
                   "bytes_hex": e.hex(), "length": len(e), "sha256": digest(e)})
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({"format": "SIRM/RCT/v0 (proposal)", "checks": res, "vectors": vs}, indent=2, sort_keys=True) + "\n")
    for k, v in res.items():
        print(f"{k.upper()}={v}")
    print("RESULT_JSON=" + str(out))

if __name__ == "__main__":
    main()
