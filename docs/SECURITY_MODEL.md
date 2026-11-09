# Security Model

Threat classes: arithmetic overflow/underflow/rounding; account/aggregate divergence; unauthorized issuance or parameter changes; replay and signature confusion; validator equivocation, censorship and collusion; partitions, data withholding and denial of service; storage corruption and unsafe migration; compromised keys; bridge/oracle/indexer compromise; reserve misreporting and custody failure.

Controls: canonical serialization, domain-separated signatures, checked arithmetic, atomic transitions, pre-mutation authorization, journal reconciliation, threshold key custody, rotation/recovery, validator monitoring, fuzzing, property tests, adversarial integration tests, reproducible builds, monitoring, backups and incident playbooks.

Lean proves protocol properties. Rust needs conformance and correspondence evidence. Consensus requires its own safety/liveness analysis. Operational assurance requires independent penetration tests, key ceremony review, custody controls, restore drills and vulnerability disclosure.

No absolute-security or guaranteed-solvency claims are permitted.
