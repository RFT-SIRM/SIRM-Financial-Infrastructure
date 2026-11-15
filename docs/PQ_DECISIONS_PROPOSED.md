# Proposed Post-Quantum Decisions (DRAFT, not adopted)

These are proposals for review. They are **not** part of `docs/DECISIONS.md`. Adoption means
moving an item there together with the matching Lean, specification and tests. See
`docs/POST_QUANTUM_SECURITY_ARCHITECTURE.md` for the reasoning.

| # | Proposed decision | Status | Open question |
|---|---|---|---|
| PQ-1 | Cryptography sits behind one boundary; financial transitions see only an authenticated principal. | Proposed | none |
| PQ-2 | Default transaction signature: ML-DSA-65 (FIPS 204). | Proposed | ML-DSA-87 for treasury and governance roles? |
| PQ-3 | Long-lived trust roles (governance, recovery, checkpoints, releases) additionally use SLH-DSA-128s (FIPS 205) for algorithm diversity. | Proposed | which roles exactly |
| PQ-4 | A versioned suite registry in committed state; suite id inside every signed byte string; (domain tag, version, suite id) never reinterpreted; verifier takes the suite from the registered key. | Proposed | none |
| PQ-5 | Transport and backups: ML-KEM-768 combined with X25519; AES-256-class symmetric keys. | Proposed | exact hybrid construction after reading SP 800-227 |
| PQ-6 | SHA-256 remains the commitment hash, with a hash suite id and a dual-root transition for any change. | Proposed | none |
| PQ-7 | Threshold authorization is an explicit k-of-n list of independent signatures; no aggregation is assumed. | Proposed | none |
| PQ-8 | Genesis is PQ-first; Ed25519 is never the sole authorization path; hybrid is a bounded transition tool. | Proposed | hybrid mandatory for all accounts or only roles |
| PQ-9 | Once a PQ key is registered, classical keys cannot register, rotate or revoke keys for that principal. | Proposed | none |
| PQ-10 | Successor-key hash commitments for any legacy identity that needs migration (Rift imports). | Proposed | none |
| PQ-11 | The state commitment must cover all consensus-critical state before being called a commitment to the protocol state; v0 is partial and says so. | Proposed | none |
| PQ-12 | No implementation phase starts before independent cryptographic review of the architecture. | Proposed | who reviews |
| PQ-13 | Signature bytes are never used as identifiers or deduplication keys; identity comes from the signed message (request hash, nonce), not from the signature. | Proposed | none |

Not decided: library choice (see `PQ_RUST_LIBRARY_EVALUATION.md`), consensus and validator signing, HSM support, concrete threshold
policies, expiry fields, privacy and confidential-transaction cryptography.
