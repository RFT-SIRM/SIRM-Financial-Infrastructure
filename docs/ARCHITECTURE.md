# Architecture

## Normative boundary

`SIRM Financial Infrastructure` is the umbrella project. `SIRM Protocol` is the normative financial state-transition specification. `RFT Network` is the planned independent execution and settlement network. `RFT` is the proposed native network asset. The names do not imply that a production network or token is deployed.

The dependency direction is:

    Institutional applications and external adapters
                       |
                  RFT Network
          (nodes, consensus, storage, P2P)
                       |
          Deterministic execution layer
           (reference Rust implementation)
                       |
                 SIRM Protocol
            (Lean 4 normative specification)

The Lean model is authoritative for protocol semantics. The Rust implementation is not authoritative merely because it passes tests; it must be shown to refine the specified transitions. Network consensus must execute the same state-transition function and reject invalid state updates.

## Core boundaries

### Formal protocol

- typed asset identifiers and integer base units;
- account identifiers and explicit account classes;
- per-asset supply state;
- balanced double-entry postings per asset;
- issuance, burn, transfer, fee, escrow, settlement, and redemption semantics;
- authorization and governance predicates;
- transition-preservation and reachable-state safety theorems.

### Execution

- canonical transaction encoding;
- deterministic arithmetic and explicit rounding;
- checked overflow/underflow;
- atomic state transitions;
- deterministic event and state-commitment formats;
- reference implementation and differential/property tests against the Lean model.

### Network

- node identity and key management;
- peer discovery and authenticated transport;
- consensus safety and liveness assumptions;
- block proposal, validation, finality, and fork-choice rules;
- data availability, snapshots, state sync, and recovery;
- protocol-version negotiation and governed upgrades.

No consensus algorithm is selected in this foundational stage. No network-security guarantee is claimed before the protocol and implementation are specified, reviewed, tested, and independently audited.

### Institutional applications

Institutional services are adapters around the protocol. They may introduce legal entities, custody, banking partners, fiat rails, identity checks, compliance controls, or reserve evidence. They must not silently alter core accounting semantics or turn an external claim into a protocol-proven fact.

## Separation of guarantees

1. A Lean theorem proves a property of a mathematical definition under its stated assumptions.
2. A refinement proof or verified compiler path connects an implementation to that definition.
3. Tests and independent audits examine implementation and operational risks not covered by the proof.
4. Consensus and network analysis addresses Byzantine behavior, network partitions, data availability, and liveness.
5. Legal and reserve attestations concern real-world institutions and assets; they are not derivable from source code alone.