#!/usr/bin/env python3
"""Reference signed-request layer v1 (PROPOSAL): suite registry, ML-DSA-65, hybrid, downgrade rejection.

See engineering/canonical_encoding/SPEC_signed_request_v1.md. Crypto comes from the Python
`cryptography` package (OpenSSL): ML-DSA-65 (FIPS 204) and Ed25519 (RFC 8032).

Modes:  python3 -I scripts/signed_request_v1_reference.py          verify the frozen vectors and run all checks
        python3 -I scripts/signed_request_v1_reference.py --generate   rewrite the vectors (ML-DSA signing is
        hedged/randomized in OpenSSL, so regenerated signatures differ; keys, requests and expected results do not)
"""
import hashlib, json, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import canonical_encoding_reference as rq
from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives import serialization as S
from cryptography.hazmat.primitives.asymmetric import mldsa
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey, Ed25519PublicKey

SIG_DOMAIN = b"SIRM/SIG/v1\x00"
WIRE_DOMAIN = b"SIRM/SRQ/v1\x00"
REQ_LEN = {0: 85, 1: 85, 2: 81}
ED, ML, HYB, SLH = 0x0001, 0x0002, 0x0101, 0x0003
# suite id -> (name, kind, public key length, signature length, status)
REGISTRY = {
    ED: ("Ed25519", "sign", 32, 64, "deprecated"),
    ML: ("ML-DSA-65", "sign", 1952, 3309, "active"),
    HYB: ("Ed25519+ML-DSA-65", "sign", 32 + 1952, 64 + 3309, "active"),
    SLH: ("SLH-DSA-SHA2-128s", "sign", 32, 7856, "proposed"),
}
OUT = HERE.parent / "engineering/canonical_encoding/results/signed_request_v1_vectors.json"


class VerifyError(ValueError):
    def __init__(self, kind):
        super().__init__(kind); self.kind = kind


def key_id(suite, pk):
    return hashlib.sha256(b"SIRM/KID/v1\x00" + suite.to_bytes(2, "big") + pk).digest()


def signing_message(chain, suite, kid, request_bytes):
    return SIG_DOMAIN + chain.to_bytes(8, "big") + suite.to_bytes(2, "big") + kid + request_bytes


def seed(label):
    return hashlib.sha256(b"SIRM test key v1 " + label.encode()).digest()


class Keys:
    """Test key material (vectors only)."""
    def __init__(self, label):
        s = seed(label)
        self.ed = Ed25519PrivateKey.from_private_bytes(s)
        self.ml = mldsa.MLDSA65PrivateKey.from_seed_bytes(s)
        raw = S.Encoding.Raw
        self.ed_pk = self.ed.public_key().public_bytes(raw, S.PublicFormat.Raw)
        self.ml_pk = self.ml.public_key().public_bytes(raw, S.PublicFormat.Raw)

    def pk(self, suite):
        return {ED: self.ed_pk, ML: self.ml_pk, HYB: self.ed_pk + self.ml_pk}[suite]

    def sign(self, suite, msg):
        return {ED: lambda: self.ed.sign(msg), ML: lambda: self.ml.sign(msg),
                HYB: lambda: self.ed.sign(msg) + self.ml.sign(msg)}[suite]()


def encode_wire(chain, suite, request_bytes, signature):
    return WIRE_DOMAIN + chain.to_bytes(8, "big") + suite.to_bytes(2, "big") + request_bytes + signature


def make_wire(keys, chain, suite, request, sign_suite=None, kid=None, sign_chain=None):
    rb = rq.encode(request)
    kid = kid or key_id(suite, keys.pk(suite))
    sig = keys.sign(sign_suite or suite, signing_message(sign_chain if sign_chain is not None else chain, suite, kid, rb))
    return encode_wire(chain, suite, rb, sig)


def _verify_one(suite, pk, msg, sig):
    try:
        if suite == ED:
            Ed25519PublicKey.from_public_bytes(pk).verify(sig, msg)
        elif suite == ML:
            mldsa.MLDSA65PublicKey.from_public_bytes(pk).verify(sig, msg)
        else:
            return False
        return True
    except (InvalidSignature, ValueError):
        return False


def verify(wire, node_chain, registry, allow_deprecated=False):
    """registry: principal -> (suite, pk). Returns the decoded request or raises VerifyError(kind)."""
    if wire[:12] != WIRE_DOMAIN:
        raise VerifyError("bad_domain")
    if len(wire) < 22:
        raise VerifyError("truncated")
    suite = int.from_bytes(wire[20:22], "big")
    if suite not in REGISTRY:
        raise VerifyError("unknown_suite")
    tag_at = 22 + 12 + 32 + 4 + 8
    if len(wire) <= tag_at:
        raise VerifyError("truncated")
    if wire[tag_at] not in REQ_LEN:
        raise VerifyError("unknown_operation")
    end = 22 + REQ_LEN[wire[tag_at]]
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
        raise VerifyError("suite_mismatch")  # the suite comes from the registered key, not the message
    status = REGISTRY[suite][4]
    if status != "active" and not (status == "deprecated" and allow_deprecated):
        raise VerifyError("suite_not_allowed")
    msg = signing_message(node_chain, suite, key_id(suite, pk), wire[22:end])
    sig = wire[end:]
    if suite == HYB:  # both halves must verify
        ok = _verify_one(ED, pk[:32], msg, sig[:64]) and _verify_one(ML, pk[32:], msg, sig[64:])
    else:
        ok = _verify_one(suite, pk, msg, sig)
    if not ok:
        raise VerifyError("bad_signature")
    return request


def requests():
    rid = bytes(range(32))
    return [
        ("transfer_p1", {"request_id": rid, "principal": 1, "nonce": 7, "op": ("transfer", 1, 2, 3, 1000)}),
        ("issue_p0", {"request_id": rid, "principal": 0, "nonce": 0, "op": ("issue", 0, 5, 0, 10**18)}),
        ("burn_p0", {"request_id": b"\xaa" * 32, "principal": 0, "nonce": 41, "op": ("burn", 0, 1, 25)}),
        ("max_p1", {"request_id": b"\xff" * 32, "principal": 1, "nonce": 2**64 - 1,
                    "op": ("transfer", 2**32 - 1, 2**32 - 1, 2**32 - 1, 2**128 - 1)}),
        ("transfer_p2_legacy", {"request_id": rid, "principal": 2, "nonce": 3, "op": ("transfer", 2, 1, 0, 5)}),
    ]


PRINCIPAL_SUITE = {0: ML, 1: HYB, 2: ED}  # test accounts: PQ only, hybrid, legacy Ed25519 only
CHAINS = [1, 2**64 - 1]


def build():
    keys = {p: Keys("principal %d" % p) for p in PRINCIPAL_SUITE}
    registry = {p: (s, keys[p].pk(s)) for p, s in PRINCIPAL_SUITE.items()}
    registry[3] = (SLH, bytes(32))  # registered under a suite that is only proposed
    valid = []
    for name, r in requests():
        p = r["principal"]
        for chain in CHAINS:
            valid.append({"name": name, "chain": chain, "request": r, "suite": PRINCIPAL_SUITE[p],
                          "wire": make_wire(keys[p], chain, PRINCIPAL_SUITE[p], r)})
    r1 = requests()[0][1]       # principal 1 (hybrid)
    r0 = requests()[1][1]       # principal 0 (ML-DSA only)
    r2 = requests()[4][1]       # principal 2 (legacy Ed25519 only)
    k0, k1, k2 = keys[0], keys[1], keys[2]
    ch = 1
    neg = []

    def add(name, wire, kind, **kw):
        neg.append({"name": name, "wire": wire, "expect": kind, **kw})

    good_ml = make_wire(k0, ch, ML, r0)
    good_h = make_wire(k1, ch, HYB, r1)
    add("wrong_chain", good_ml, "wrong_chain", node_chain=2)
    add("truncated", good_ml[:-1], "truncated")
    add("trailing", good_ml + b"\0", "trailing_bytes")
    add("v0_domain", b"SIRM/SRQ/v0\x00" + good_ml[12:], "bad_domain")
    add("unknown_suite", good_ml[:20] + b"\x7f\xff" + good_ml[22:], "unknown_suite")
    # a principal registered under a suite that is only "proposed": refused even with a well-formed wire
    p3 = dict(r0); p3["principal"] = 3
    add("proposed_suite_refused", encode_wire(ch, SLH, rq.encode(p3), bytes(REGISTRY[SLH][3])), "suite_not_allowed")
    # downgrade: hybrid account, attacker presents an Ed25519-only wire signed with the Ed25519 half
    down = make_wire(k1, ch, ED, r1)
    add("downgrade_hybrid_to_ed25519", down, "suite_mismatch")
    # downgrade: hybrid account, attacker presents an ML-DSA-only wire
    add("downgrade_hybrid_to_mldsa", make_wire(k1, ch, ML, r1), "suite_mismatch")
    # substitution: PQ-only account presented with an Ed25519 wire
    add("substitute_ed25519_for_mldsa", make_wire(k0, ch, ED, r0), "suite_mismatch")
    # stripping one half of a hybrid: garbage in the ML-DSA half, then garbage in the Ed25519 half
    gh = bytearray(good_h); gh[-1] ^= 1
    add("hybrid_bad_mldsa_half", bytes(gh), "bad_signature")
    gh = bytearray(good_h); gh[len(good_h) - 3309 - 1] ^= 1
    add("hybrid_bad_ed25519_half", bytes(gh), "bad_signature")
    # a hybrid whose ML-DSA half is signed for the plain ML-DSA suite message (cross-suite signature reuse)
    rb = rq.encode(r1)
    kid = key_id(HYB, k1.pk(HYB))
    cross = encode_wire(ch, HYB, rb, k1.ed.sign(signing_message(ch, ML, kid, rb)) + k1.ml.sign(signing_message(ch, ML, kid, rb)))
    add("hybrid_signed_under_other_suite_id", cross, "bad_signature")
    # signature made for another chain
    add("signature_for_other_chain", make_wire(k0, ch, ML, r0, sign_chain=2), "bad_signature")
    # signature over the bare request encoding (domain confusion)
    add("signature_over_bare_request", encode_wire(ch, ML, rq.encode(r0), k0.ml.sign(rq.encode(r0))), "bad_signature")
    # signed by another principal's key
    add("signed_by_other_key", make_wire(Keys("someone else"), ch, ML, r0, kid=key_id(ML, k0.pk(ML))), "bad_signature")
    # signature bound to a different key id
    add("wrong_key_id_in_message", make_wire(k0, ch, ML, r0, kid=bytes(32)), "bad_signature")
    # unknown principal
    unknown = dict(r0); unknown["principal"] = 9
    add("unknown_principal", make_wire(k0, ch, ML, unknown), "unknown_principal")
    # deprecated suite: legacy Ed25519 account is refused by default, accepted only when policy allows
    legacy = make_wire(k2, ch, ED, r2)
    add("deprecated_suite_refused_by_default", legacy, "suite_not_allowed")
    return keys, registry, valid, neg, legacy


def hx(b):
    return b.hex()


def run_checks(valid, neg, registry):
    for v in valid:
        got = verify(v["wire"], v["chain"], registry, allow_deprecated=v["suite"] == ED)
        assert got == v["request"], v["name"]
    # the deprecated suite verifies only when the policy opts in
    legacy = [v for v in valid if v["suite"] == ED]
    assert legacy and all(_refused(v, registry) for v in legacy)
    for n in neg:
        try:
            verify(bytes.fromhex(n["wire"]) if isinstance(n["wire"], str) else n["wire"], n.get("node_chain", 1), registry)
            raise AssertionError("accepted: " + n["name"])
        except VerifyError as e:
            assert e.kind == n["expect"], (n["name"], e.kind, n["expect"])
    # every single-byte mutation of one ML-DSA vector and one hybrid vector is rejected
    tried = 0
    for v in [v for v in valid if v["suite"] in (ML, HYB) and v["chain"] == 1][:2]:
        w = v["wire"]
        for pos in range(len(w)):
            for mask in (0x01, 0x80):
                m = bytearray(w); m[pos] ^= mask
                try:
                    verify(bytes(m), 1, registry)
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
    j = {"format": "SIRM signed request v1 reference vectors (PROPOSAL)",
         "note": "ML-DSA signatures are hedged-random in OpenSSL; this file is frozen. Keys and expected results are deterministic.",
         "registry": {("%04x" % k): {"name": v[0], "kind": v[1], "pk_len": v[2], "sig_len": v[3], "status": v[4]} for k, v in sorted(REGISTRY.items())},
         "principals": {str(p): {"suite": "%04x" % s, "key_id": hx(key_id(s, keys[p].pk(s))), "public_hex": hx(keys[p].pk(s)), "seed_hex": hx(seed("principal %d" % p))} for p, s in sorted(PRINCIPAL_SUITE.items())},
         "valid": [{"name": v["name"], "chain_id": str(v["chain"]), "suite": "%04x" % v["suite"], "length": len(v["wire"]),
                    "request_hex": hx(rq.encode(v["request"])), "wire_hex": hx(v["wire"]),
                    "sha256": hashlib.sha256(v["wire"]).hexdigest()} for v in valid],
         "negative": [{"name": n["name"], "wire_hex": hx(n["wire"]), "node_chain": str(n.get("node_chain", 1)), "expect": n["expect"]} for n in neg]}
    return json.dumps(j, indent=1, sort_keys=True) + "\n"


def main():
    keys, registry, valid, neg, _ = build()
    if "--generate" in sys.argv or not OUT.exists():
        n_valid, n_neg, tried = run_checks(valid, neg, registry)
        OUT.write_text(encode_json(keys, registry, valid, neg))
        print("GENERATED=1")
    else:
        d = json.loads(OUT.read_text())
        # frozen vectors: keys and requests re-derive exactly; every stored wire verifies as recorded
        for p, info in d["principals"].items():
            assert info["public_hex"] == hx(registry[int(p)][1]) and info["key_id"] == hx(key_id(registry[int(p)][0], registry[int(p)][1]))
        stored = [{"name": v["name"], "chain": int(v["chain_id"]), "suite": int(v["suite"], 16), "wire": bytes.fromhex(v["wire_hex"]),
                   "request": rq.decode(bytes.fromhex(v["request_hex"]))} for v in d["valid"]]
        stored_neg = [{"name": n["name"], "wire": bytes.fromhex(n["wire_hex"]), "expect": n["expect"], "node_chain": int(n["node_chain"])} for n in d["negative"]]
        n_valid, n_neg, tried = run_checks(stored, stored_neg, registry)
        # the freshly built negative cases (new random signatures) give the same verdicts
        run_checks(valid, neg, registry)
        print("FROZEN_VECTORS_VERIFIED=1")
    print("VALID_VECTORS=%d" % n_valid)
    print("NEGATIVE_CASES=%d" % n_neg)
    print("SINGLE_BYTE_MUTATIONS_REJECTED=%d" % tried)
    print("ML_DSA_65_PK=%d SIG=%d  HYBRID_WIRE=%d  ML_WIRE=%d" % (REGISTRY[ML][2], REGISTRY[ML][3],
          len(next(v for v in valid if v["suite"] == HYB)["wire"]), len(next(v for v in valid if v["suite"] == ML)["wire"])))


if __name__ == "__main__":
    main()
