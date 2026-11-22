# State commitment v1 (checked by SIRM)

Status: proposal (phase P4 start of `docs/POST_QUANTUM_SECURITY_ARCHITECTURE.md`). It does not
replace `SPEC_state_commitment_v0.md`. Reference: `scripts/state_commitment_v1_reference.py`.
Vectors: `engineering/canonical_encoding/results/state_commitment_v1_vectors.json`. Rust:
`rust/sirm-codec/src/commit_v1.rs`, tests `rust/sirm-codec/tests/commit_v1_conformance.rs`. No Lean
statements exist for this layer.

## What v1 adds to v0

v0 commits balances, supply and nonces. v1 keeps those three sparse-Merkle roots and adds:

- a **key registry** tree (principal to key account),
- a **suite registry** tree (suite id to suite entry),
- a **protocol header** (chain id, protocol version, hash suite id, suite registry root).

## Layout

    suite value = kind u8 | status u8 | pk_len u32 | sig_len u32 | activation u64
                  | deprecation u64 | disable u64                       (34 bytes; no height = 2^64-1)
    key value   = suite u16 | key id 32 | flags u8 (1 frozen, 2 revoked, 4 pq bound)
                  | recovery flag u8 | recovery key id 32 | pending flag u8
                  | pending key id 32 | pending start u64               (109 bytes)
    header hash = SHA256("SIRM/HDR/v1\0" | chain id u64 | version u16 | hash suite u16 | suite root)
    state root  = SHA256("SIRM/STC/v1\0" | accounts u32 | assets u32 | balance root | supply root
                         | nonce root | key root | header hash)

Codes: kind sign 0, kem 1, hash 2, aead 3; status proposed 0, active 1, deprecated 2, disabled 3.
An absent optional field is a flag byte 0 followed by zero fill, never omitted. The registry trees
are the v0 sparse Merkle tree (depth 64, SHA-256, keys u64). The key registry stores the key id
(a hash of suite and public key, see `SPEC_signed_request_v1.md`), not the public key itself.

## Coverage classification (v1)

| State element | Covered by v1 | Note |
|---|---|---|
| Balances, supply, nonces | yes | as v0 |
| Key registry (suite, key id, frozen, revoked, pq bound, recovery, pending recovery) | yes | thresholds not yet |
| Suite registry and statuses | yes | |
| Chain id, protocol version, hash suite | yes | |
| Receipts and the request-id cache | **no** | needed for idempotency |
| Account and asset registries | **no** | |
| Authorization grants, account control | **no** | |
| Fee parameters, governance state, timelocks | **no** | |
| Escrow, time-lock, dispute, migration, residuals | **no** | |
| Threshold policies | **no** | |

**v1 is a wider but still partial root. It is not a commitment to the complete protocol state**
and must not be described as one.

## Evidence and limits

- Python and Rust agree byte for byte on the value encodings, the suite root, the key root and the
  full root, which includes the root of the replayed integrated processor (4000 requests).
- 18 single-field changes (header, suite entries, key accounts, additions and removals) each give
  a distinct root in both implementations; registry insertion order does not matter.
- Not claimed: Lean statements, collision-resistance proof, adoption, incremental-update cost,
  coverage of the rows marked "no". The Rust types here are commitment inputs only; there is no
  Rust key-registry state machine yet, so the Rust test feeds registries from the vectors.
