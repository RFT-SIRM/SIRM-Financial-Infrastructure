# Migration from Rift Prototypes

The two Rift repositories are historical research and prototype inputs, not normative protocol definitions. New SIRM definitions take precedence. No legacy parameter or invariant is adopted merely because it appears in old code or documentation.

## Rift-Network (Solana / Anchor)

Useful input: a real Anchor program structure with a Core program, token program, tests, and a model using participant balances plus a `global_field`. It demonstrates one execution host that was useful while no independent network existed.

Items not to copy without redesign:

- `FOUNDER_SHARE_BPS = 314` is superseded by the requested 1.309% genesis policy, represented as 13,090 ppm.
- The token program keeps a copied CoreState layout; this manual duplication can drift from the owning program's layout.
- The issue path does not store and enforce one canonical SPL mint address in token state. The new protocol must bind each asset identifier to its canonical mint/asset definition and reject substitution.
- The old token interface has no complete burn/redemption lifecycle tied to the supply book and customer liabilities.
- Planner and historical memory are described as future components, not completed modules.
- The Solana gate model is not accepted as the target governance architecture for a sovereign network.

## Rift-L1-Blockchain

Useful input: deterministic Rust simulation, checked arithmetic, operation-sequence fuzzing, and edge-case exploration.

Boundary: its main implementation lives predominantly in a simulation binary; several `src/core` modules are placeholders. Stress-test counts are evidence about the tested harness and input distribution, not a proof of the complete protocol or a live network.

## Legacy global-field model: not adopted yet

The legacy identity is written as `total_supply = total_base_sum + global_field * participants`. Its intended interpretation must be reconciled with actual account balances.

In the inspected Anchor code, registration initializes a user's `base_balance` to zero but subtracts `global_field` from `total_base_sum`. Unregistration adjusts the aggregate by `-base_balance + global_field` while supply counters change by the base balance. Negative-entropy updates also alter the aggregate without writing corresponding participant account balances. These updates preserve the stated aggregate equation under their own conventions, but the stored aggregate cannot simultaneously be assumed to be the literal sum of the persisted user `base_balance` fields without an additional offset/refinement definition.

Before this model can be adopted, specify the exact meaning of `base_balance`, `effective_balance`, `total_base_sum`, `global_field`, participant creation/removal, negative-entropy compensation, and dust. Then prove that the optimized aggregate state refines a direct account-level model for every transition, including boundary and failure cases.

## Parameter conflicts

The prototypes contain different edge-cost limits and operational assumptions. No edge-cost unit, negative-entropy constant, debt-limit rule, or global-field schedule is canonical until units, economic meaning, account-level semantics, rounding, and safety invariants are specified and proved.

## Migration rule

Do not deploy a renamed or mechanically ported version of either old project. Reimplement only behavior that has a written SIRM specification, a Lean model, tests, and an explicit refinement/conformance argument.