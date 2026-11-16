# Signed request layer v2 (proposal, not adopted)

Status: proposal (phase P1 of `docs/POST_QUANTUM_SECURITY_ARCHITECTURE.md`, step after I3 of
`docs/INTEGRATED_STATE_MACHINE_PROPOSAL.md`). It does not replace or modify v0 or v1. Reference:
`scripts/signed_request_v2_reference.py`. Vectors:
`engineering/canonical_encoding/results/signed_request_v2_vectors.json`. Rust:
`rust/sirm-codec/src/signed_v2.rs`, test `rust/sirm-codec/tests/signed_v2_conformance.rs`. No Lean
counterpart.

## What changes against v1

The signed request bytes are the **request encoding v1** (`SPEC_request_v1.md`): ten operations and a
32-byte request id, 61 to 89 bytes. Everything else is v1: suite registry and statuses, key id, rules,
downgrade defence, verification order and reason codes. Only the domains change (a domain tag has one
meaning forever):

    key id:          SHA-256("SIRM/KID/v1\0" | suite u16 | public key)          (unchanged)
    signing message: "SIRM/SIG/v2\0" (12) | chain_id u64 | suite u16 | key id (32) | request encoding v1
    wire format:     "SIRM/SRQ/v2\0" (12) | chain_id u64 | suite u16 | request encoding v1 | signature

The operation tag is at wire offset 56 + 22 = 78; the request length follows from the tag (61, 65, 73,
81, 85 or 89 bytes), the signature length from the suite. A v1 wire is rejected as `bad_domain`; a
request with a v0 domain inside a v2 wire is rejected as `bad_request`. A signature made over the v1
signing message does not verify under v2.

The request id is inside the signed bytes, so the replay and conflict key of the machine cannot be
changed without breaking the signature.

## Evidence

- Python: 22 valid vectors (11 requests covering all ten operations plus a maximum-value one, chains 1
  and 2^64-1, accounts of three kinds: ML-DSA-65 only, hybrid, legacy Ed25519), 26 negative cases with
  an expected reason each, and 14,062 single-byte mutations of one ML-DSA, one hybrid and one Ed25519
  wire, all rejected. ML-DSA signatures are hedged-random in OpenSSL, so the file is frozen
  (`--generate` rewrites it); Ed25519 signatures are deterministic and re-derived on every run.
- Rust: the Ed25519 vectors are signed again with `ed25519-dalek` from the recorded seed and equal the
  OpenSSL bytes; they verify with `verify_strict`, are refused by default (deprecated suite) and accepted
  when policy allows. All 26 negative cases give the expected reason. No single-byte mutation of any
  Ed25519 vector or of one ML-DSA vector is accepted. An end-to-end node accepts a verified request into
  `integrated::Machine`, answers the same wire from the cache, leaves the machine untouched (no receipt,
  no state change) for a tampered wire, caches a denial for an authenticated request outside its grant,
  and refuses another chain.

## Limits

- **No post-quantum verifier in Rust.** ML-DSA-65 and hybrid wires pass every structural check and are
  then refused with `VerifierUnavailable`; they are never accepted. Whether the PQ signatures verify is
  established only by the Python reference (OpenSSL). The Rust library choice stays open
  (`docs/PQ_RUST_LIBRARY_EVALUATION.md`).
- The negative cases that expect `bad_signature` for ML-DSA or hybrid wires are checked in Rust only as
  `VerifierUnavailable`; only the Ed25519 ones are checked as `bad_signature`.
- Not claimed: adoption, security proof, constant-time behaviour, a second independent ML-DSA
  implementation, threshold policies, key registry transitions, expiry. Differential evidence only.
