# Architecture Decisions

## ADR-001 — Naming
SIRM Financial Infrastructure is the whole platform; SIRM Protocol is the formal model; RFT Network is the planned independent network; RFT is its planned native asset. Ticker/trademark clearance remains outstanding.

## ADR-002 — Lean
Lean 4 is the normative mathematical specification. Implementations must conform.

## ADR-003 — Native network
RFT Network is independent. Solana is an optional external adapter, not the base protocol.

## ADR-004 — Founder allocation
The historical 3.14% is replaced with a one-time 1.309% genesis allocation, represented as 13,090 ppm. This is an explicit project policy; Lean proves arithmetic, not economic optimality.

## ADR-005 — Open token parameters
Total supply, decimals, inflation, validator rewards and distribution of the remaining 98.691% are not invented.

## ADR-006 — Consensus
No algorithm is selected before a threat model and validator requirements.

## ADR-007 — Old Rift code
The prototypes are design inputs, not normative behavior. Account-level semantics, dust and global-field effects must be re-derived.
