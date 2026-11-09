# RFT Network — Native Network Design

RFT Network is the planned independent network for deterministic execution and settlement of SIRM Protocol. It is not Solana with a renamed program and not the old Rift code with strings changed.

## Required components
- canonical transaction format, signatures, nonce/replay rules, authorization and fees;
- deterministic execution engine, checked arithmetic and atomic failure;
- ordered durable ledger, block format, replay, snapshots and state commitment;
- mempool, admission checks, resource limits and anti-spam;
- validator identity, admission, rotation and monitoring;
- consensus, safety, liveness, finality and validator fault model;
- peer discovery, authenticated transport, gossip and state synchronization;
- RPC, wallet protocol, indexer, explorer and institutional APIs.

## Stages
R0: single-node deterministic ledger and replay, no distributed consensus claim.
R1: multi-node devnet, validator identities and state sync, valueless test assets.
R2: adversarial testnet covering partitions, equivocation, restart, divergence, recovery and upgrades.
R3: institutional pilot after independent audit and legal review.
R4: public network only after formal, implementation, consensus, security and operational gates.

No consensus algorithm is selected until validator count, Byzantine assumptions, network synchrony, finality, recovery, data availability, censorship and incentive requirements are documented. No throughput claim is made without end-to-end measurements.
