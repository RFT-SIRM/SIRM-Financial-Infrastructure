# RFT Network: Requirements Before Implementation

RFT Network is intended to be a sovereign, independently operated network. It is not implemented by this repository yet. Solana was the execution host of the earlier Rift Network prototype; the new target is an independent network with its own node software and settlement rules.

## Required components

1. **Canonical transaction format:** chain identifier, protocol version, sender/authority, nonce, operation, asset identifiers, integer amounts, expiry, and signature envelope.
2. **Deterministic execution:** one state-transition definition shared by validators; explicit arithmetic and failure behavior; atomic application.
3. **Consensus:** separately specified safety and liveness properties, validator admission/removal, Byzantine assumptions, finality, and fork handling. The algorithm is not selected in this stage.
4. **State commitments:** canonical serialization, commitment/hash function, block headers, transaction inclusion proofs, and independently reproducible state roots.
5. **Data availability:** retention, archival nodes, pruning, snapshots, state sync, and recovery after long offline periods.
6. **Peer-to-peer network:** authenticated transport, peer discovery, rate limiting, DoS resistance, and network partition recovery.
7. **Governance and upgrades:** versioning, validator-set transitions, timelocked upgrades, reproducible binaries, and migration equivalence.
8. **Privacy and compliance interfaces:** privacy-by-design for user data, selective disclosure, and institution-specific attestations without changing core accounting semantics.

## Execution model

A reference Rust implementation is planned only after the Lean transition model is sufficiently complete. The implementation must pass differential tests and have a documented refinement/conformance argument. A matching test output is evidence, not a proof of full correspondence.

## Public verifiability

The source, protocol version, validators' signed attestations, block/state commitments, and inclusion proofs should be independently inspectable. A user or institution must be able to verify that a finalized state root follows from the published protocol and accepted transactions, subject to the stated consensus and data-availability assumptions.

## Explicit non-claims

No TPS target, validator count, consensus safety bound, finality time, censorship-resistance guarantee, or production-readiness claim is made until a concrete protocol is selected, formally specified, implemented, benchmarked, and audited.