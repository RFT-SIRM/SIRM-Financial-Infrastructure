# State commitment v0 (checked by SIRM)

Status: proposal. Reference: `scripts/state_commitment_reference.py`. Vectors:
`engineering/canonical_encoding/results/state_commitment_vectors_v0.json`. Rust:
`rust/sirm-codec/src/commit.rs`, tests `rust/sirm-codec/tests/commit_conformance.rs`.
No Lean statements exist for this layer.

## Decision: tree, not a flat hash

A depth-64 sparse Merkle tree (SMT) over u64 keys, SHA-256. A flat hash of the whole state
would give a root but no way to prove one balance without the entire state; the tree gives
inclusion and non-inclusion proofs of 64 sibling hashes.

    empty leaf = SHA256("SIRM/SMT/E/v0\0")
    leaf       = SHA256("SIRM/SMT/L/v0\0" | key u64 | len u16 | value)
    node       = SHA256("SIRM/SMT/N/v0\0" | left | right)     (bit 63 of the key at the top)
    empty subtree hashes: e[0] = empty leaf, e[i+1] = node(e[i], e[i])

Absent and empty are identical: zero balances, all-zero supply and zero nonces are not stored.

## State root

    state root = SHA256("SIRM/STC/v0\0" | accounts u32 | assets u32
                        | balance root | supply root | nonce root)

- balances: key `account << 32 | asset`, value u128 BE (16 bytes)
- supply: key `asset`, value `minted | burned | outstanding`, 3 x u128 BE (48 bytes)
- nonces: key `principal`, value next nonce u64 BE (8 bytes)

Not committed: the response cache (request ids and stored receipts), the policy, fees,
escrow, disputes, migration and registry state. These need their own commitments before any
whole-system root is claimed.

## Proofs

A proof is the 64 siblings from the leaf level upward. Verification recomputes the root from
the leaf (or the empty leaf for absence) and compares.

## Evidence and limits

Two independent algorithms in Python agree on 150 random trees; order independence; proofs of
inclusion and absence with tampering rejected; six single-component changes give distinct state
roots. In Rust, vectors match byte for byte, and the root of the replayed integrated processor
(4000 requests) equals the root the Python reference computes from the trace's final state;
every accepted request moves the root and every rejection or replay leaves it unchanged.
Not claimed: Lean theorem, collision-resistance proof, adoption, incremental update
efficiency, or that the committed parts are the whole state.
