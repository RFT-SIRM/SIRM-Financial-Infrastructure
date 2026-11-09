# Mathematical scope and assurance boundaries

## What the first Lean module proves

The initial module defines aggregate supply accounting over natural-number units and proves:

- the empty state satisfies the supply invariant;
- minting preserves the invariant;
- burning preserves the invariant when the burned amount does not exceed outstanding supply;
- transfers preserve aggregate supply;
- an allocation can be represented as an exact split;
- a basis-point share and its explicit remainder sum to the original total.

## What it does not prove

It does not yet prove participant-level conservation, authorization, solvency, reserve adequacy, correctness of an executable implementation, consensus safety, censorship resistance, legal enforceability, custody of real-world assets, or regulatory compliance.

The current aggregate model is intentionally not a substitute for a complete double-entry accounting model. In particular, it does not assert that a token supply is backed by reserves or redeemable at par.

## Next formal milestones

1. Define typed assets and account identifiers.
2. Define balanced journal entries and prove debit/credit conservation.
3. Define transfers with authorization and account-level balance preservation.
4. Define issuance and redemption against explicit liability accounts.
5. Define fee, rounding, dust, and overflow semantics.
6. Define governance authorization and bounded parameter changes.
7. Define reserve attestations as external assumptions with provenance and freshness.
8. Define a transition-system safety theorem for all reachable states.
