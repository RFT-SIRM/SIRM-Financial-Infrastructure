#!/usr/bin/env python3
"""Reference signed-request layer (v0 PROPOSAL): chain id binding + Ed25519 signature.

Executable specification + vectors for rust/sirm-codec/src/signed.rs. Independent of the Rust
crate: Ed25519 comes from OpenSSL through the Python `cryptography` package (RFC 8032, pure
Ed25519), the Rust side uses ed25519-dalek.

Signing message (what is signed):   b"SIRM/SIG/v0\\0" (12) | chain_id u64 | request encoding (85|81)
Wire format (what is transmitted):  b"SIRM/SRQ/v0\\0" (12) | chain_id u64 | request encoding | signature (64)
The public key is NOT in the message: the verifier looks it up by `principal` in its key registry,
so a signature cannot be paired with an attacker-chosen key. Verification order:
decode wire -> chain id equals the node's -> key exists for principal -> strict signature check.
A failure at any step produces no receipt, no cache entry and no nonce change (the request never
reaches the processor). Test keys below are derived from public labels and are for vectors only.
"""
import hashlib, json, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import canonical_encoding_reference as rq
from cryptography.exceptions import InvalidSignature
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey, Ed25519PublicKey

SIG_DOMAIN = b"SIRM/SIG/v0\x00"
WIRE_DOMAIN = b"SIRM/SRQ/v0\x00"
L = 2**252 + 27742317777372353535851937790883648493  # Ed25519 group order
U64 = 2**64
REQ_LEN = {0: 85, 1: 85, 2: 81}

class SignedError(ValueError):
    def __init__(self, kind):
        super().__init__(kind); self.kind = kind

def test_seed(i):
    return hashlib.sha256(b"SIRM test key v0 #" + str(i).encode()).digest()

def keypair(i):
    sk = Ed25519PrivateKey.from_private_bytes(test_seed(i))
    pk = sk.public_key().public_bytes(serialization.Encoding.Raw, serialization.PublicFormat.Raw)
    return sk, pk

def signing_message(chain_id, req):
    if not 0 <= chain_id < U64:
        raise SignedError("chain_id_range")
    return SIG_DOMAIN + chain_id.to_bytes(8, "big") + rq.encode(req)

def sign(sk, chain_id, req):
    return sk.sign(signing_message(chain_id, req))

def wire(chain_id, req, sig):
    return WIRE_DOMAIN + chain_id.to_bytes(8, "big") + rq.encode(req) + sig

def verify(b, expected_chain, keys):
    """keys: principal -> 32-byte public key. Returns the request or raises SignedError(kind)."""
    if not b.startswith(WIRE_DOMAIN):
        raise SignedError("bad_domain")
    p = len(WIRE_DOMAIN)
    tag_at = p + 8 + 12 + 32 + 4 + 8
    if len(b) <= tag_at:
        raise SignedError("truncated")
    if b[tag_at] not in REQ_LEN:
        raise SignedError("unknown_operation")
    end = p + 8 + REQ_LEN[b[tag_at]]
    if len(b) < end + 64:
        raise SignedError("truncated")
    if len(b) > end + 64:
        raise SignedError("trailing_bytes")
    chain = int.from_bytes(b[p:p + 8], "big")
    try:
        req = rq.decode(b[p + 8:end])
    except rq.EncodingError:
        raise SignedError("bad_request")
    if chain != expected_chain:
        raise SignedError("wrong_chain")
    if req["principal"] not in keys:
        raise SignedError("unknown_principal")
    sig = b[end:]
    # strict check: reject non-canonical S (>= L) explicitly, as OpenSSL and dalek strict both do
    if int.from_bytes(sig[32:], "little") >= L:
        raise SignedError("bad_signature")
    try:
        Ed25519PublicKey.from_public_bytes(keys[req["principal"]]).verify(sig, signing_message(chain, req))
    except InvalidSignature:
        raise SignedError("bad_signature")
    return req

def requests():
    rid = bytes(range(32))
    return [
        ("transfer", {"request_id": rid, "principal": 1, "nonce": 7, "op": ("transfer", 1, 2, 3, 1000)}),
        ("issue", {"request_id": rid, "principal": 2, "nonce": 0, "op": ("issue", 2, 5, 0, 10**18)}),
        ("burn", {"request_id": b"\xaa" * 32, "principal": 0, "nonce": 41, "op": ("burn", 0, 1, 25)}),
        ("max", {"request_id": b"\xff" * 32, "principal": 2, "nonce": 2**64 - 1,
                 "op": ("transfer", 2**32 - 1, 2**32 - 1, 2**32 - 1, 2**128 - 1)}),
    ]

def selfcheck():
    res = {}
    keys = {i: keypair(i)[1] for i in range(3)}
    sks = {i: keypair(i)[0] for i in range(3)}
    # primitive sanity: RFC 8032 test vector 1 (empty message)
    sk = Ed25519PrivateKey.from_private_bytes(bytes.fromhex("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"))
    assert sk.public_key().public_bytes(serialization.Encoding.Raw, serialization.PublicFormat.Raw).hex() == \
        "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"
    assert sk.sign(b"").hex() == ("e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155"
                                  "5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b")
    res["rfc8032_vector"] = 1
    chains = [1, 2**64 - 1]
    n = 0
    for _, r in requests():
        for chain in chains:
            sig = sign(sks[r["principal"]], chain, r)
            w = wire(chain, r, sig)
            assert verify(w, chain, keys) == r
            assert len(w) == 12 + 8 + (81 if r["op"][0] == "burn" else 85) + 64
            n += 1
            # every single-byte mutation of the wire must be rejected (xor 0x01 and xor 0x80)
            for pos in range(len(w)):
                for mask in (0x01, 0x80):
                    m = bytearray(w); m[pos] ^= mask
                    try:
                        verify(bytes(m), chain, keys); raise SystemExit(f"mutation accepted at {pos}")
                    except SignedError:
                        pass
    res["valid_roundtrip"] = n
    res["single_byte_mutations_rejected"] = "all"
    # structured negatives
    name, r = requests()[0]
    sig = sign(sks[r["principal"]], 1, r)
    good = wire(1, r, sig)
    neg = {
        "wrong_chain": (good, 2),
        "truncated": (good[:-1], 1),
        "trailing_bytes": (good + b"\x00", 1),
        "bad_domain": (b"X" + good[1:], 1),
    }
    for k, (blob, chain) in neg.items():
        try:
            verify(blob, chain, keys); raise SystemExit(f"accepted {k}")
        except SignedError as e:
            assert e.kind == {"wrong_chain": "wrong_chain", "truncated": "truncated", "trailing_bytes": "trailing_bytes",
                              "bad_domain": "bad_domain"}[k], (k, e.kind)
    # wrong key for the principal, key missing, malleated S, signature over the wire bytes (domain confusion)
    for k, blob, ks, chain, want in [
        ("signed_by_other_key", wire(1, r, sign(sks[0], 1, r)), keys, 1, "bad_signature"),
        ("unknown_principal", good, {0: keys[0]}, 1, "unknown_principal"),
        ("malleated_s", good[:-32] + ((int.from_bytes(sig[32:], "little") + L) % 2**256).to_bytes(32, "little"), keys, 1, "bad_signature"),
        ("signed_request_encoding_only", wire(1, r, sks[1].sign(rq.encode(r))), keys, 1, "bad_signature"),
        ("signed_other_chain", wire(1, r, sign(sks[1], 2, r)), keys, 1, "bad_signature"),
    ]:
        try:
            verify(blob, chain, ks); raise SystemExit(f"accepted {k}")
        except SignedError as e:
            assert e.kind == want, (k, e.kind)
    res["structured_negatives"] = len(neg) + 5
    return res

def main():
    out = Path(sys.argv[1] if len(sys.argv) > 1 else "engineering/canonical_encoding/results/signed_request_vectors_v0.json")
    res = selfcheck()
    keys = {i: keypair(i) for i in range(3)}
    vs = []
    for name, r in requests():
        for chain in (1, 2**64 - 1):
            sig = sign(keys[r["principal"]][0], chain, r)
            w = wire(chain, r, sig)
            vs.append({"name": f"{name}_chain_{chain}", "chain_id": str(chain), "request_id": r["request_id"].hex(),
                       "principal": r["principal"], "nonce": str(r["nonce"]),
                       "op": [r["op"][0], *[str(x) for x in r["op"][1:]]],
                       "signing_message_hex": signing_message(chain, r).hex(), "signature_hex": sig.hex(),
                       "wire_hex": w.hex(), "length": len(w), "sha256": hashlib.sha256(w).hexdigest()})
    doc = {"format": "SIRM/SRQ/v0 (proposal)", "checks": res,
           "test_keys": [{"principal": i, "seed_hex": test_seed(i).hex(), "public_hex": keys[i][1].hex()} for i in range(3)],
           "vectors": vs}
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(doc, indent=2, sort_keys=True) + "\n")
    for k, v in res.items():
        print(f"{k.upper()}={v}")
    print("RESULT_JSON=" + str(out))

if __name__ == "__main__":
    main()
