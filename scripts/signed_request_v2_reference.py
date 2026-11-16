#!/usr/bin/env python3
"""Reference signed-request layer v2 (PROPOSAL): the v1 suite registry carrying request encoding v1.

See engineering/canonical_encoding/SPEC_signed_request_v2.md. Differences to v1: the signed request
bytes are the request encoding v1 of scripts/request_v1_reference.py (ten operations, 32-byte request
id), and the domains are "SIRM/SIG/v2\\0" and "SIRM/SRQ/v2\\0". Suites, key ids and the rules are those of
SPEC_signed_request_v1.md. Crypto comes from the Python `cryptography` package (OpenSSL).

Modes:  python3 -I scripts/signed_request_v2_reference.py            verify the frozen vectors and run all checks
        python3 -I scripts/signed_request_v2_reference.py --generate   rewrite the vectors (ML-DSA signing is
        hedged/randomized in OpenSSL; Ed25519 signatures, keys, requests and expected results are deterministic)
"""
import hashlib, json, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import request_v1_reference as rq
import signed_request_v1_reference as v1
from signed_request_v1_reference import ED, ML, HYB, SLH, REGISTRY, Keys, key_id, seed, _verify_one

SIG_DOMAIN = b"SIRM/SIG/v2\x00"
WIRE_DOMAIN = b"SIRM/SRQ/v2\x00"
TAG_AT = 22 + 12 + 32 + 4 + 8          # offset of the operation tag in the wire
REQ_LEN = {rq.TAGS[k]: rq.PREFIX + sum(w) for k, w in rq.SHAPE.items()}
OUT = HERE.parent / "engineering/canonical_encoding/results/signed_request_v2_vectors.json"
VerifyError = v1.VerifyError


def signing_message(chain, suite, kid, request_bytes):
    return SIG_DOMAIN + chain.to_bytes(8, "big") + suite.to_bytes(2, "big") + kid + request_bytes


def encode_wire(chain, suite, request_bytes, signature):
    return WIRE_DOMAIN + chain.to_bytes(8, "big") + suite.to_bytes(2, "big") + request_bytes + signature


def make_wire(keys, chain, suite, request, sign_suite=None, kid=None, sign_chain=None):
    rb = rq.encode(request)
    kid = kid or key_id(suite, keys.pk(suite))
    sig = keys.sign(sign_suite or suite, signing_message(sign_chain if sign_chain is not None else chain, suite, kid, rb))
    return encode_wire(chain, suite, rb, sig)


def verify(wire, node_chain, registry, allow_deprecated=False):
    """registry: principal -> (suite, pk). Returns the decoded request or raises VerifyError(kind)."""
    if wire[:12] != WIRE_DOMAIN:
        raise VerifyError("bad_domain")
    if len(wire) < 22:
        raise VerifyError("truncated")
    suite = int.from_bytes(wire[20:22], "big")
    if suite not in REGISTRY:
        raise VerifyError("unknown_suite")
    if len(wire) <= TAG_AT:
        raise VerifyError("truncated")
    if wire[TAG_AT] not in REQ_LEN:
        raise VerifyError("unknown_operation")
    end = 22 + REQ_LEN[wire[TAG_AT]]
    sig_len = REGISTRY[suite][3]
    if len(wire) < end + sig_len:
        raise VerifyError("truncated")
    if len(wire) > end + sig_len:
        raise VerifyError("trailing_bytes")
    try:
        request = rq.decode(wire[22:end])
    except rq.EncodingError:
        raise VerifyError("bad_request")
    if int.from_bytes(wire[12:20], "big") != node_chain:
        raise VerifyError("wrong_chain")
    entry = registry.get(request["principal"])
    if entry is None:
        raise VerifyError("unknown_principal")
    reg_suite, pk = entry
    if suite != reg_suite:
        raise VerifyError("suite_mismatch")
    status = REGISTRY[suite][4]
    if status != "active" and not (status == "deprecated" and allow_deprecated):
        raise VerifyError("suite_not_allowed")
    msg = signing_message(node_chain, suite, key_id(suite, pk), wire[22:end])
    sig = wire[end:]
    if suite == HYB:
        ok = _verify_one(ED, pk[:32], msg, sig[:64]) and _verify_one(ML, pk[32:], msg, sig[64:])
    else:
        ok = _verify_one(suite, pk, msg, sig)
    if not ok:
        raise VerifyError("bad_signature")
    return request


PRINCIPAL_SUITE = {0: ML, 1: HYB, 2: ED}
CHAINS = [1, 2**64 - 1]


def requests():
    """One request per operation, principal and suite assigned round-robin; ids differ per request."""
    ops = [("transfer", 1, 2, 3, 1000), ("issue", 0, 5, 0, 10**18), ("burn", 3, 1, 25),
           ("open", 2, 0, 1, 0, 500), ("release", 2), ("cancel", 0), ("expire", 1),
           ("dispute", 1, 3), ("advance", 1_800_000_000), ("migrate", 10**30)]
    out = []
    for i, op in enumerate(ops):
        out.append(("%s_p%d" % (op[0], i % 3), {"request_id": hashlib.sha256(b"req %d" % i).digest(),
                                                  "principal": i % 3, "nonce": i * 7, "op": op}))
    out.append(("max_p1", {"request_id": b"\xff" * 32, "principal": 1, "nonce": 2**64 - 1,
                           "op": ("open", 2**32 - 1, 2**32 - 1, 2**32 - 1, 2**32 - 1, 2**128 - 1)}))
    return out


def build():
    keys = {p: Keys("principal %d" % p) for p in PRINCIPAL_SUITE}
    registry = {p: (s, keys[p].pk(s)) for p, s in PRINCIPAL_SUITE.items()}
    registry[3] = (SLH, bytes(32))
    valid = []
    for name, r in requests():
        p = r["principal"]
        for chain in CHAINS:
            valid.append({"name": name, "chain": chain, "request": r, "suite": PRINCIPAL_SUITE[p],
                          "wire": make_wire(keys[p], chain, PRINCIPAL_SUITE[p], r)})
    k0, k1, k2 = keys[0], keys[1], keys[2]
    r0 = {"request_id": bytes(range(32)), "principal": 0, "nonce": 1, "op": ("migrate", 5)}
    r1 = {"request_id": bytes(range(32)), "principal": 1, "nonce": 2, "op": ("dispute", 1, 3)}
    r2 = {"request_id": bytes(range(32)), "principal": 2, "nonce": 3, "op": ("open", 2, 0, 1, 0, 5)}
    ch = 1
    neg = []

    def add(name, wire, kind, **kw):
        neg.append({"name": name, "wire": wire, "expect": kind, **kw})

    good_ml = make_wire(k0, ch, ML, r0)
    good_h = make_wire(k1, ch, HYB, r1)
    good_ed = make_wire(k2, ch, ED, r2)
    add("wrong_chain", good_ml, "wrong_chain", node_chain=2)
    add("truncated", good_ml[:-1], "truncated")
    add("trailing", good_ml + b"\0", "trailing_bytes")
    add("v1_domain", b"SIRM/SRQ/v1\x00" + good_ml[12:], "bad_domain")
    add("unknown_suite", good_ml[:20] + b"\x7f\xff" + good_ml[22:], "unknown_suite")
    unk_op = bytearray(good_ml); unk_op[TAG_AT] = 10
    add("unknown_operation_tag", bytes(unk_op), "unknown_operation")
    old_req = bytearray(good_ml); old_req[22:34] = b"SIRM/FTX/v0\x00"
    add("request_v0_domain_inside", bytes(old_req), "bad_request")
    p3 = dict(r0); p3["principal"] = 3
    add("proposed_suite_refused", encode_wire(ch, SLH, rq.encode(p3), bytes(REGISTRY[SLH][3])), "suite_not_allowed")
    add("downgrade_hybrid_to_ed25519", make_wire(k1, ch, ED, r1), "suite_mismatch")
    add("downgrade_hybrid_to_mldsa", make_wire(k1, ch, ML, r1), "suite_mismatch")
    add("substitute_ed25519_for_mldsa", make_wire(k0, ch, ED, r0), "suite_mismatch")
    gh = bytearray(good_h); gh[-1] ^= 1
    add("hybrid_bad_mldsa_half", bytes(gh), "bad_signature")
    gh = bytearray(good_h); gh[len(good_h) - 3309 - 1] ^= 1
    add("hybrid_bad_ed25519_half", bytes(gh), "bad_signature")
    rb = rq.encode(r1)
    kid = key_id(HYB, k1.pk(HYB))
    m = signing_message(ch, ML, kid, rb)
    add("hybrid_signed_under_other_suite_id", encode_wire(ch, HYB, rb, k1.ed.sign(m) + k1.ml.sign(m)), "bad_signature")
    add("signature_for_other_chain", make_wire(k0, ch, ML, r0, sign_chain=2), "bad_signature")
    add("signature_over_bare_request", encode_wire(ch, ML, rq.encode(r0), k0.ml.sign(rq.encode(r0))), "bad_signature")
    add("signature_over_v1_message_domain", encode_wire(ch, ML, rq.encode(r0), k0.ml.sign(
        v1.signing_message(ch, ML, key_id(ML, k0.pk(ML)), rq.encode(r0)))), "bad_signature")
    add("signed_by_other_key", make_wire(Keys("someone else"), ch, ML, r0, kid=key_id(ML, k0.pk(ML))), "bad_signature")
    add("wrong_key_id_in_message", make_wire(k0, ch, ML, r0, kid=bytes(32)), "bad_signature")
    unknown = dict(r0); unknown["principal"] = 9
    add("unknown_principal", make_wire(k0, ch, ML, unknown), "unknown_principal")
    add("deprecated_suite_refused_by_default", good_ed, "suite_not_allowed")
    # legacy Ed25519 account, deprecated suite allowed by policy: deterministic signatures, checked in Rust too
    ed = lambda w: bytes(w)
    b = bytearray(good_ed); b[-1] ^= 1
    add("ed25519_bad_signature", ed(b), "bad_signature", allow_deprecated=True)
    b = bytearray(good_ed); b[40] ^= 1
    add("ed25519_request_changed_after_signing", ed(b), "bad_signature", allow_deprecated=True)
    add("ed25519_signature_for_other_chain", make_wire(k2, ch, ED, r2, sign_chain=2), "bad_signature", allow_deprecated=True)
    add("ed25519_wrong_key_id_in_message", make_wire(k2, ch, ED, r2, kid=bytes(32)), "bad_signature", allow_deprecated=True)
    add("ed25519_signature_over_bare_request", encode_wire(ch, ED, rq.encode(r2), k2.ed.sign(rq.encode(r2))), "bad_signature", allow_deprecated=True)
    return keys, registry, valid, neg


def hx(b):
    return b.hex()


def run_checks(valid, neg, registry):
    for v in valid:
        got = verify(v["wire"], v["chain"], registry, allow_deprecated=v["suite"] == ED)
        assert got == v["request"], v["name"]
    legacy = [v for v in valid if v["suite"] == ED]
    assert legacy and all(_refused(v, registry) for v in legacy)
    for n in neg:
        try:
            verify(n["wire"], n.get("node_chain", 1), registry, allow_deprecated=n.get("allow_deprecated", False))
            raise AssertionError("accepted: " + n["name"])
        except VerifyError as e:
            assert e.kind == n["expect"], (n["name"], e.kind, n["expect"])
    tried = 0
    pick = [next(v for v in valid if v["suite"] == s and v["chain"] == 1 and v["request"]["op"][0] == op)
            for s, op in ((ML, "migrate"), (HYB, "dispute"), (ED, "burn"))]
    for v in pick:
        w = v["wire"]
        for pos in range(len(w)):
            for mask in (0x01, 0x80):
                m = bytearray(w); m[pos] ^= mask
                try:
                    verify(bytes(m), 1, registry, allow_deprecated=True)
                    raise AssertionError("mutation accepted at %d" % pos)
                except VerifyError:
                    pass
                tried += 1
    return len(valid), len(neg), tried


def _refused(v, registry):
    try:
        verify(v["wire"], v["chain"], registry)
        return False
    except VerifyError as e:
        return e.kind == "suite_not_allowed"


def encode_json(keys, registry, valid, neg):
    j = {"format": "SIRM signed request v2 reference vectors (PROPOSAL)",
         "note": "ML-DSA signatures are hedged-random in OpenSSL; this file is frozen. Ed25519 signatures, keys and expected results are deterministic.",
         "registry": {("%04x" % k): {"name": v[0], "kind": v[1], "pk_len": v[2], "sig_len": v[3], "status": v[4]} for k, v in sorted(REGISTRY.items())},
         "principals": {str(p): {"suite": "%04x" % s, "key_id": hx(key_id(s, keys[p].pk(s))), "public_hex": hx(keys[p].pk(s)), "seed_hex": hx(seed("principal %d" % p))} for p, s in sorted(PRINCIPAL_SUITE.items())},
         "valid": [{"name": v["name"], "chain_id": str(v["chain"]), "suite": "%04x" % v["suite"], "length": len(v["wire"]),
                    "request_hex": hx(rq.encode(v["request"])), "wire_hex": hx(v["wire"]),
                    "sha256": hashlib.sha256(v["wire"]).hexdigest()} for v in valid],
         "negative": [{"name": n["name"], "wire_hex": hx(n["wire"]), "node_chain": str(n.get("node_chain", 1)),
                       "allow_deprecated": bool(n.get("allow_deprecated", False)), "expect": n["expect"]} for n in neg]}
    return json.dumps(j, indent=1, sort_keys=True) + "\n"


def main():
    keys, registry, valid, neg = build()
    if "--generate" in sys.argv or not OUT.exists():
        n_valid, n_neg, tried = run_checks(valid, neg, registry)
        OUT.write_text(encode_json(keys, registry, valid, neg))
        print("GENERATED=1")
    else:
        d = json.loads(OUT.read_text())
        for p, info in d["principals"].items():
            assert info["public_hex"] == hx(registry[int(p)][1]) and info["key_id"] == hx(key_id(registry[int(p)][0], registry[int(p)][1]))
        stored = [{"name": v["name"], "chain": int(v["chain_id"]), "suite": int(v["suite"], 16), "wire": bytes.fromhex(v["wire_hex"]),
                   "request": rq.decode(bytes.fromhex(v["request_hex"]))} for v in d["valid"]]
        stored_neg = [{"name": n["name"], "wire": bytes.fromhex(n["wire_hex"]), "expect": n["expect"], "node_chain": int(n["node_chain"]),
                       "allow_deprecated": n["allow_deprecated"]} for n in d["negative"]]
        n_valid, n_neg, tried = run_checks(stored, stored_neg, registry)
        run_checks(valid, neg, registry)
        # Ed25519 signatures are deterministic: the freshly built legacy vectors equal the stored ones
        fresh = {(v["name"], v["chain"]): v["wire"] for v in valid if v["suite"] == ED}
        assert all(fresh[(v["name"], v["chain"])] == v["wire"] for v in stored if v["suite"] == ED)
        print("FROZEN_VECTORS_VERIFIED=1")
    print("VALID_VECTORS=%d" % n_valid)
    print("NEGATIVE_CASES=%d" % n_neg)
    print("SINGLE_BYTE_MUTATIONS_REJECTED=%d" % tried)


if __name__ == "__main__":
    main()
