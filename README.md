# SIRM Financial Infrastructure

**A formally specified financial protocol and infrastructure, grounded in the RFT research programme.**

SIRM Financial Infrastructure is the foundational engineering project for building reliable financial systems from explicit mathematical rules. Its first deliverable is a Lean 4 specification of the financial state and the transitions that are allowed to change it. Executable implementations, a native ledger, networking, consensus, institutional governance, and token interfaces will be developed against that specification.

The long-term objective is a network-independent financial infrastructure suitable for institutional settlement and accounting. The repository does **not** claim to be a bank, a production blockchain, or a live financial service.

## Design principle

> Specify the rules mathematically. Prove the model's properties. Implement the model. Verify that implementations conform. Only then expose institutional and network interfaces.

Lean is the normative language for the mathematical specification. Rust is the intended language for the high-performance reference implementation and node software. A blockchain is an execution and settlement environment; it is not the source of the economic rules.

## Initial scope

The first foundation release focuses on:

- a canonical financial state model;
- explicit accounting and supply invariants;
- state-transition definitions and machine-checked preservation proofs;
- exact, parameterized token-allocation mathematics, without silently choosing a founder allocation;
- an architecture that can later support a native ledger, governance, settlement, reserves, risk controls, networking, and consensus.

## What this project is not yet

At this stage there is no native blockchain, consensus algorithm, peer-to-peer network, validator implementation, production ledger, bank, legal entity, deposit product, or issued token. These are future engineering and institutional workstreams, not implied by the repository name.

The previous Rift projects are treated as research prototypes and sources of design questions. Their Rust and Solana implementations are not automatically normative. Any future adapter or migration must conform to the SIRM formal specification.

## Mathematical provenance and token allocation

The project will keep a traceable register of constants, units, definitions, assumptions, and proofs. No numerical value is promoted into financial policy merely because it appears in an RFT model.

In particular, the spectral value near **1.30912892028081…** reported by the Phi-Genesis research is a numerically observed eigenvalue candidate in a specific spectral problem. The current Phi-Genesis status describes the exact limiting value and a closed form as open. It is not an established 1.309% financial allocation rule. The founder-allocation rate therefore remains an explicit, unselected policy parameter until its economic meaning, unit, rounding rule, and governance approval are specified.

The historical 3.14% founder allocation from the Rift token prototype is not carried forward as a default.

## Verification levels

The project distinguishes four different claims:

1. **Model theorem:** Lean proves a property of the mathematical specification.
2. **Implementation correspondence:** an executable implementation is shown to implement that specification.
3. **Runtime assurance:** tests, fuzzing, audits, operational controls, and deployment evidence support the running system.
4. **Institutional assurance:** legal, custodial, reserve, governance, and regulatory requirements are met by the relevant real-world entities.

A result at one level does not imply the next.

## Repository layout

The initial formal core and its documentation are being introduced incrementally:

- `SIRM/` — Lean 4 specification;
- `docs/` — architecture, protocol decisions, mathematical scope, constants, and roadmap;
- `.github/workflows/` — reproducible Lean build checks.

## Development status

<badge-placeholder>

The repository is in its foundational specification phase. Early proofs concern the aggregate accounting model only; they do not yet prove correctness of participant-level account storage, token issuance, a ledger implementation, or a network.

See [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md), [docs/MATHEMATICAL_SCOPE.md](docs/MATHEMATICAL_SCOPE.md), [docs/CONSTANTS_REGISTER.md](docs/CONSTANTS_REGISTER.md), and [docs/ROADMAP.md](docs/ROADMAP.md) as they are added.

## Toolchain

The Lean project is pinned to Lean 4.33.1 and Mathlib v4.33.1, matching the current formalization toolchain used in the RFT research repositories.

## Licensing

No repository-specific license has been selected in this initial foundation. Public visibility on GitHub does not itself grant permission to use, deploy, modify, or redistribute the work. A clear licensing and contribution policy must be adopted before external development or operational deployment.
