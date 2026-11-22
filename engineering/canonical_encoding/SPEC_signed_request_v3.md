# Signed request layer v3 (checked by SIRM)

Status: proposal. It does not replace or modify v0, v1 or v2. Reference:
`scripts/signed_request_v3_reference.py`. Vectors:
`engineering/canonical_encoding/results/signed_request_v3_vectors.json`. Rust:
`rust/sirm-codec/src/signed_v3.rs`, test `rust/sirm-codec/tests/signed_v3_conformance.rs`. No Lean
counterpart.

## What changes against v2

The signed request bytes are the **request encoding v2** (`SPEC_request_v2.md`): eleven operations,
including the arbiter operation `resolve` (tag 10), and a 32-byte request id, 61 to 89 bytes. Everything
else is v2: suite registry and statuses, key id, rules, downgrade defence, verification order and reason
codes. Only the domains change (a domain tag has one meaning forever):

    key id:          SHA-256("SIRM/KID/v1\0" | suite u16 | public key)          (unchanged)
    signing message: "SIRM/SIG/v3\0" (12) | chain_id u64 | suite u16 | key id (32) | request encoding v2
    wire format:     "SIRM/SRQ/v3\0" (12) | chain_id u64 | suite u16 | request encoding v2 | signature

The operation tag is at wire offset 78; the request length follows from the tag (61, 65, 73, 81, 85 or
89 bytes, and 62 for `resolve`), the signature length from the suite. A v1 or v2 wire is rejected as
`bad_domain`; a request with a v0 or v1 domain inside a v3 wire is rejected as `bad_request`; a
`resolve` whose flag byte is neither 0 nor 1 is rejected as `bad_request` even when correctly signed. A
signature made over the v1 or v2 signing message does not verify under v3.

The request id is inside the signed bytes, so the replay and conflict key of the machine cannot be
changed without breaking the signature.

## Evidence

- Python: 26 valid vectors (13 requests covering all eleven operations plus a maximum-value one, chains
  1 and 2^64-1, accounts of three kinds: ML-DSA-65 only, hybrid, legacy Ed25519), 32 negative cases with
  an expected reason each (including a correctly signed `resolve` with a non-canonical flag, a truncated
  `resolve` body, and signatures over the v1 and v2 message domains), and 14,358 single-byte mutations
  of one ML-DSA, one hybrid and two Ed25519 wires, all rejected. ML-DSA signatures are hedged-random in
  OpenSSL, so the file is frozen (`--generate` rewrites it); Ed25519 signatures are deterministic and
  re-derived on every run.
- Rust: the Ed25519 vectors are signed again with `ed25519-dalek` from the recorded seed and equal the
  OpenSSL bytes; they verify with `verify_strict`, are refused by default (deprecated suite) and accepted
  when policy allows. All 32 negative cases give the expected reason. No single-byte mutation of any
  Ed25519 vector or of one ML-DSA vector is accepted. End to end through `integrated::Machine`: a signed
  issue, escrow open, dispute and `resolve` settle the escrow to the beneficiary and the invariant
  holds; the same wire is answered from the cache; a second `resolve` of the same escrow is denied
  (`resolve:n`); a `resolve` without the arbiter grant is denied (`resolve:auth`); a tampered wire never
  reaches the machine; another chain is refused.

## Limits

- **No post-quantum verifier in Rust.** ML-DSA-65 and hybrid wires pass every structural check and are
  then refused with `VerifierUnavailable`; they are never accepted. Whether the PQ signatures verify is
  established only by the Python reference (OpenSSL). The Rust library choice stays open
  (`docs/PQ_RUST_LIBRARY_EVALUATION.md`).
- The negative cases that expect `bad_signature` for ML-DSA or hybrid wires are checked in Rust only as
  `VerifierUnavailable`; only the Ed25519 ones are checked as `bad_signature`.
- The state commitment (`SPEC_state_commitment_v5.md`) does not cover a machine whose cache holds a
  `resolve` request.
- Not claimed: adoption, security proof, constant-time behaviour, a second independent ML-DSA
  implementation, threshold policies, key registry transitions, expiry. Differential evidence only.
