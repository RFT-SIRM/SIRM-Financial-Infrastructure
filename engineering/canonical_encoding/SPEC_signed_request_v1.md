# Signed request layer v1 (proposal, not adopted)

Status: proposal (phase P1 of `docs/POST_QUANTUM_SECURITY_ARCHITECTURE.md`). It does not replace
or modify `SPEC_signed_request_v0.md`, which stays as a historical proposal. Reference:
`scripts/signed_request_v1_reference.py`. Vectors:
`engineering/canonical_encoding/results/signed_request_v1_vectors.json`. No Rust or Lean
counterpart yet.

## Layout

    key id:          SHA-256("SIRM/KID/v1\0" | suite u16 | public key)
    signing message: "SIRM/SIG/v1\0" (12) | chain_id u64 | suite u16 | key id (32) | request encoding
    wire format:     "SIRM/SRQ/v1\0" (12) | chain_id u64 | suite u16 | request encoding | signature

The request encoding is the v0 request encoding (85 or 81 bytes). The signature length is fixed by
the suite, so the wire length is determined once the suite id and the operation tag are read.

## Suite registry (proposal values)

| id | suite | public key | signature | status |
|---|---|---|---|---|
| 0x0001 | Ed25519 | 32 | 64 | deprecated (refused unless policy allows) |
| 0x0002 | ML-DSA-65 (FIPS 204) | 1,952 | 3,309 | active |
| 0x0101 | Ed25519 + ML-DSA-65 (hybrid) | 1,984 | 3,373 | active |
| 0x0003 | SLH-DSA-SHA2-128s (FIPS 205) | 32 | 7,856 | proposed (not implemented, refused) |

Status values: proposed, active, deprecated, disabled. Only `active` suites authorize; a
`deprecated` suite authorizes only when the node policy opts in.

## Rules

1. The suite is taken from the **registered key** of the principal, never from the message. A wire
   whose suite differs from the registered one is rejected (`suite_mismatch`). This is the
   downgrade and substitution defence: an attacker cannot present an Ed25519-only wire for an
   account registered as hybrid or ML-DSA.
2. The suite id and the key id are inside the signed bytes, so a signature made under one suite or
   key cannot be reused under another.
3. Hybrid: both halves (Ed25519 then ML-DSA-65) sign the same signing message, which contains the
   hybrid suite id. Both must verify. Either half alone, or a half made for another suite id, is
   rejected.
4. Verification order: wire domain, suite known, wire length, operation tag, request decode,
   chain equals the node's, principal has a registered key, suite matches, suite allowed,
   signature (strict, both halves for hybrid). Failure never reaches the processor.
5. A (domain tag, suite id) pair has one meaning forever; a v0 wire is rejected as `bad_domain`.

Reason codes: `bad_domain`, `truncated`, `unknown_suite`, `unknown_operation`, `trailing_bytes`,
`bad_request`, `wrong_chain`, `unknown_principal`, `suite_mismatch`, `suite_not_allowed`,
`bad_signature`.

## Sizes (computed from the vectors)

Wire length for transfer and issue: ML-DSA-65 3,416 bytes; hybrid 3,480 bytes; Ed25519 alone would
be 12+8+2+85+64 = 171 bytes. A burn is 4 bytes shorter. About 20 times the Ed25519 size.

## Evidence and limits

- 10 valid vectors (5 requests, chains 1 and 2^64-1, three account kinds: ML-DSA only, hybrid,
  legacy Ed25519) and 18 negative cases, each with an expected reason code.
- Every single-byte mutation (two masks) of one ML-DSA vector and one hybrid vector is rejected
  (13,792 mutations).
- ML-DSA-65 and Ed25519 come from the Python `cryptography` package (OpenSSL). OpenSSL signs
  ML-DSA in a hedged, randomized mode, so the vector file is **frozen**: the script verifies it by
  default and rewrites it only with `--generate`. Keys, requests and expected reasons are
  deterministic. This is one implementation; no second independent ML-DSA implementation has
  been compared yet.
- Not claimed: adoption, security proof, constant-time behavior, Rust or Lean agreement,
  threshold policies, key registry transitions (rotation, revocation, recovery), expiry.
