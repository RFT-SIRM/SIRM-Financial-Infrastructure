# Consensus and Validator Requirements

Consensus is distinct from valid transaction execution and ledger storage. Lean specifies valid transitions; the ledger records ordered history; consensus selects the history and establishes finality.

Before selecting an algorithm, specify network synchrony, validator count, Byzantine threshold, admission/exit, key rotation, ordering and censorship expectations, finality, data availability, state sync, crash recovery, incentives, slashing and upgrade safety.

Candidate families include BFT state-machine replication for bounded/permissioned validator sets and stake-weighted designs for more open sets. No family is selected here.

Tests must cover equivocation, partitions, delayed messages, validator churn, restart, snapshot divergence, censorship, malformed blocks and upgrades. Testnets use valueless assets until independent review.
