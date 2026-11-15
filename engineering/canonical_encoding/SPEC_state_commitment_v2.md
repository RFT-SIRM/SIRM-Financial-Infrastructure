# State commitment v2 (proposal, not adopted)

Status: proposal (phase P4 of `docs/POST_QUANTUM_SECURITY_ARCHITECTURE.md`). It does not replace
v0 or v1. Reference: `scripts/state_commitment_v2_reference.py`. Vectors:
`engineering/canonical_encoding/results/state_commitment_v2_vectors.json`. Rust:
`rust/sirm-codec/src/commit_v2.rs`, tests `rust/sirm-codec/tests/commit_v2_conformance.rs`.
No Lean statements exist for this layer.

## What v2 adds to v1

v1 commits balances, supply, nonces, key registry, suite registry and a protocol header. v2 keeps
all of that and adds three components:

- the **request-id cache** (accepted receipts and cached denials),
- the **authorization policy** (grants and account control),
- the **account and asset registry**.

## Layout

    cache entry   = request id 32 | principal u32 | nonce u64 | op u8 | a u32 | b u32 | asset u32
                    | amount u128 | stored tag u8 | u64 | u64                          (90 bytes)
                    op: 0 transfer (source, destination), 1 issue (issuer, recipient), 2 burn (holder, 0)
                    stored: tag 0 accepted (accepted nonce, next nonce);
                            tag 1 denied (expected nonce, reason code)
                    reason: 0 transfer auth, 1 issue auth, 2 burn auth, 3 transfer funds, 4 burn funds
    cache commit  = SHA256("SIRM/CAC/v2\0" | count u64 | entries ascending by request id)
    grant entry   = principal u32 | scope u8 | a u32 | b u32 | asset u32 | limit u128   (33 bytes)
    policy commit = SHA256("SIRM/POL/v2\0" | n u64 | grant entries | m u64 | control entries)
                    grant entries and control entries (principal u32 | account u32) sorted bytewise,
                    duplicates removed
    account meta  = class u8 | status u8 | network u32
    asset meta    = symbol length u32 | symbol UTF-8 | decimals u32 | issuer u32 | status u8 | network u32
    registry commit = SHA256("SIRM/REG/v2\0" | n u32 | account metas in index order
                             | m u32 | asset metas in index order)
    state root v2 = SHA256("SIRM/STC/v2\0" | accounts u32 | assets u32 | balance root | supply root
                           | nonce root | key root | header hash | cache | policy | registry)

Codes: account class in declaration order (holder 0 ... clearing 15, as in `SIRM.AccountRegistry`
and the Rust enum); account status active 0, frozen 1, closed 2; asset status draft 0, active 1,
frozen 2, retired 3.

## Design notes

- These three components are **ordered list hashes**, not sparse trees. Request ids are 32 bytes,
  wider than the tree key, and truncating them would allow two ids to share a slot. The cost is that
  there are no inclusion or non-inclusion proofs for these components; a later version may move
  them into trees with full-width keys.
- Entries are fixed width or length prefixed, and every list is count prefixed, so concatenation
  is unambiguous.
- Only requests that reached the cache are committed: accepted and denied ones. Replays, id
  conflicts, stale and future nonces, and invalid ledger requests are not stored by the processor,
  so they are not in the root.

## Checks

Python and Rust agree on the entry encodings, the three component commitments, the full root over
the replayed 4000-request processor trace (2270 cache entries), and the policy and registry
commitments of all 24 registry episodes. Twelve single-component changes each give a distinct
root; list order and duplicate grants do not change it.

## Still not covered

Fee parameters, governance state, escrow, time-lock, dispute, migration and residual state,
threshold policies. This is not a commitment to the complete protocol state, and a matching root
is differential evidence only, not a refinement proof.
