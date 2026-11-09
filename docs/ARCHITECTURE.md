# Architecture

## Naming
- **SIRM Financial Infrastructure:** whole project and institutional architecture.
- **SIRM Protocol:** normative formal rules.
- **RFT Network:** planned independent native network and distributed ledger.
- **RFT:** planned native network asset; symbol clearance remains outstanding.

## Layers
1. Lean formal model: state, transition preconditions, accounting identities, authorization and proofs.
2. Rust reference execution: deterministic state machine, checked arithmetic, canonical serialization.
3. Ledger: ordered journal, durable state, replay, snapshots and state commitments.
4. RFT Network: mempool, validators, networking, consensus, finality, state sync and RPC.
5. Institutional services: treasury, reserves, settlement, risk, governance and external integrations.
6. Clients: wallet, explorer, APIs and institutional adapters.

The old Solana/Anchor deployment was a practical host before a native chain existed. RFT Network is not a Solana rename. Solana may remain an optional external adapter.

A valid state transition does not prove consensus safety. Consensus finality does not prove economic correctness. Lean model proofs do not establish that an unverified binary conforms. Each layer has separate assurance gates.

The old Rift repositories are migration references. Their semantics must be re-derived and reconciled at account level before migration.
