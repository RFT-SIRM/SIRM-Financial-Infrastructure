# Signed request layer v0 (proposal, not adopted)

Status: proposal. Executable reference: `scripts/signed_request_reference.py`. Vectors:
`engineering/canonical_encoding/results/signed_request_vectors_v0.json`. Rust:
`rust/sirm-codec/src/signed.rs`, tests `rust/sirm-codec/tests/signed_conformance.rs`.
No Lean statements exist for this layer.

## Layout

    signing message: "SIRM/SIG/v0\0" (12) | chain_id u64 BE | request encoding (85 | 81)
    wire format:     "SIRM/SRQ/v0\0" (12) | chain_id u64 BE | request encoding | signature (64)

The request encoding is the v0 encoding from `SPEC_v0.md`. Wire length is 169 (transfer, issue)
or 165 (burn). Signature scheme: Ed25519 (RFC 8032), signing the signing message directly.

## Decisions

- Chain binding: the chain id is part of the signed bytes and of the wire bytes. A signature
  made for one chain does not verify on another.
- Domain separation: the signing domain differs from the wire domain and from the request
  domain, so a signature over the bare request encoding, or over any other layer, is rejected.
- The public key is not transmitted. The node looks it up by `principal` in a key registry.
  Key custody, rotation, revocation, thresholds and expiry are not modelled.
- Strict verification: non-canonical `S` (malleated signatures) and small-order keys are rejected.
  Registry keys must decode to a curve point.

## Verification order

1. wire decode: `bad_domain`, `truncated`, `unknown_operation`, `trailing_bytes`, `bad_request`
2. chain id equals the node's: `wrong_chain`
3. a key exists for the principal: `unknown_principal`
4. strict signature check: `bad_signature`

Any failure stops before the processor: no receipt, no cache entry, no nonce change. Replay
protection stays with the processor (request ID and nonce); a signed exact retry is a replay.

## Evidence and limits

Evidence: RFC 8032 vector 1; 8 valid vectors (4 requests, chains 1 and 2^64-1) whose
signatures from OpenSSL (Python) and ed25519-dalek (Rust) are byte-identical; every
single-byte mutation of every vector rejected; structured negatives; a node pipeline test in
which rejected wire messages leave the processor unchanged. Not claimed: adoption, security
proof, key management, any link to Lean authorization beyond the processor interface.
