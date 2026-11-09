# SIRM Financial Infrastructure

SIRM is the formal and institutional framework. **RFT Network** is the planned independent native network; **RFT** is its planned native asset. Lean 4 is the normative specification language. Rust is the intended implementation language.

## Design rule
Specify the financial rules mathematically, prove their invariants, implement deterministic state transitions, and establish implementation correspondence before real-value deployment.

## Founder allocation
The requested founder allocation is **1.309% of genesis supply**, replacing the old 3.14% Rift prototype parameter. Exact representation: 13,090 / 1,000,000 = 1.309%, stored as integer ppm. The allocation is one-time at genesis; it does not grant future inflation, fee, reserve, treasury, or administrative rights. Total supply, decimals, vesting, custody, and the other allocation pools remain open decisions.

## Project boundary
This repository is not yet a bank, licensed institution, production blockchain, live token, or customer financial service. Lean theorems establish properties of the model, not of an unverified Rust binary, validator network, custodian, or real-world reserve.

## Modules
- `SIRM/FinancialCore.lean`: supply accounting and exact founder allocation.
- `SIRM/Accounting.lean`: balanced journal postings.
- `docs/`: protocol, tokenomics, accounting, network, migration, governance, security and release specifications.

Old Rift repositories are migration references, not normative protocol definitions. Solana was the original host because no native network existed; RFT Network is designed as a separate network, not a renamed Solana program.

**Status:** foundational formal specification. No production readiness is claimed.
