# Rust ML-DSA library evaluation (P3) — proposal, nothing adopted

Date of research: 2026-11-15. Status: **evaluation only**. No dependency has been added to the
repository, and no library is chosen. This document records what was checked and what was not.

## What was checked

A throwaway crate outside the repository (not committed) verified the frozen vectors in
`engineering/canonical_encoding/results/signed_request_v1_vectors.json`
(see `SPEC_signed_request_v1.md`). The signing message was rebuilt byte by byte
(`SIRM/SIG/v1\0 | chain | suite | key id | request`), pure ML-DSA-65, empty context.

| Check | RustCrypto `ml-dsa` 0.1.2 | `aws-lc-rs` 1.19.0 |
|---|---|---|
| 8 vectors with an ML-DSA-65 signature (4 ML-DSA, 4 hybrid, ML half) | 8 / 8 accepted | 8 / 8 accepted |
| 473 single-byte flips of one signature | 0 accepted | 0 accepted |

### Non-canonical signature check (CVE-2026-24850 class)

From each of the 4 ML-DSA-65 vectors a signature was built that differs only by one duplicated
hint index (counts adjusted so the encoding is otherwise well formed). Result:

| Library | Duplicate-hint signatures rejected |
|---|---|
| RustCrypto `ml-dsa` 0.1.2 | 4 / 4 |
| `aws-lc-rs` 1.19.0 | 4 / 4 |
| RustCrypto `ml-dsa` 0.1.0-rc.3 (known vulnerable, built without default features) | 0 / 4 (all accepted) |

The last row shows the test can detect the defect: the vulnerable version accepts what the
fixed one rejects. This is one construction of one malformed-encoding class, not a full
negative suite. On the Rust side already in the repository, Ed25519 uses `verify_strict`
and a test rejects `S + L` (see `rust/sirm-codec/tests/signed_conformance.rs`).

The vectors were produced by a third implementation (OpenSSL through Python `cryptography`),
so three independent implementations agree on these vectors. The Ed25519 half of the hybrid
vectors is already covered by the existing Rust conformance tests.

## What this does not show

- It is not a security audit. It does not show constant-time behaviour, side-channel
  resistance, or correctness on inputs outside the vectors.
- The vectors come from randomized signing; they test verification only. Rust-side signing
  was not evaluated.
- Only one platform (this Linux container) was used. A published cross-platform defect in
  another library (libcrux, reported by an interested party) is the reason to require CI on
  several platforms before adoption.
- Reported status of libraries comes from crate metadata and public advisories; it was not
  independently re-audited here.

## Facts gathered (from crates.io metadata and public advisories)

- `ml-dsa` (RustCrypto) 0.1.2. Versions up to 0.1.0-rc.3 were affected by
  GHSA-5x2r-hc65-25f9 / CVE-2026-24850: repeated hint indices were accepted, making
  signatures malleable. Fixed in 0.1.0-rc.4. Reported as not independently audited.
- `aws-lc-rs` 1.19.0. ML-DSA stable since 1.18.0; available under its FIPS build.
  SLH-DSA support was not confirmed.
- `slh-dsa` (RustCrypto) is still release-candidate (0.2.0-rc.5). `ml-kem` 0.3.4.
- Other candidates seen but not tested: `libcrux-ml-dsa`, `fips204`, `pqcrypto-mldsa`.

## Options

1. **`aws-lc-rs` as primary.** Maintained C core with FIPS-validated lineage; costs a C/CMake
   build dependency. Fits the "one boundary" rule (PQ-1).
2. **RustCrypto `ml-dsa` as primary.** Pure Rust; younger, had a malleability bug in its
   release-candidate phase, no audit reported.
3. **Two implementations, differential check in CI** (recommended as the direction):
   one primary, the other used only in tests against the frozen vectors and fresh random
   signatures. Disagreement fails CI.

## Conditions before any adoption (gates, proposed)

- Pin exact versions with `--locked`; review the advisory list at adoption time.
- Re-run the vector check on at least Linux, macOS and one non-x86 target in CI.
- Reject non-canonical signature encodings and test it (the CVE class above).
- Independent review of the architecture first (PQ-12). That review is still unstaffed.

## Related rule

PQ-13 (see `PQ_DECISIONS_PROPOSED.md`): signature bytes are never used as identifiers or
deduplication keys. Malleability bugs of the kind above make the same logical signature
appear as different bytes.
