# Tokenomics: Initial Genesis Policy Record

This document records the one selected numerical tokenomics input in the current SIRM financial model. It does not define a complete token, issuance schedule, reserve, or production economic design.

## Selected one-time founder allocation

> **SELECTED GENESIS POLICY**
>
> **Founder rate: 1.309% · 13,090 ppm**
>
> The rate applies once to total genesis supply. It replaces the legacy Rift prototype value of 3.14% (31,400 ppm).

Let `G` denote total genesis supply, measured in the smallest integer accounting unit.

```text
A(G) = floor((13,090 × G) / 1,000,000)
U(G) = G − A(G)
```

- `A(G)` is the founder allocation.
- `U(G)` is the remainder left unallocated.
- Division is rounded down to a whole base unit, exactly as in the Lean `Nat` definition.
- The identity `A(G) + U(G) = G` holds by construction; the Lean model also proves `A(G) ≤ G`.

The corresponding Lean definitions are `ppmScale`, `founderRatePpm`, `founderAllocation`, and `remainingGenesisPool` in `SIRM/FinancialCore.lean`. The associated statements include `founderRate_valid`, `founderRate_exact`, `founderAllocation_le_genesisSupply`, and `founderAllocation_plus_remaining`.

### Integer example

For `G = 1,000,000,000,000` base units:

- founder allocation: `13,090,000,000`;
- unallocated remainder: `986,910,000,000`.

This example illustrates the formula only. It does not select the actual genesis supply or token decimals.

## What this policy does—and does not—decide

This is a one-time genesis allocation. It does not grant automatic rights to future issuance, transaction fees, reserves, treasury assets, customer deposits, governance control, validator rewards, or protocol administration.

The remaining amount is an explicitly unallocated pool. It is not silently transferred to the treasury, community, validators, or another recipient. For every actual genesis allocation, the account universe and assignment of every unit must be specified separately.

The following remain unresolved:

- total genesis supply and token decimals;
- founder receiving address, account assignment, and custody arrangements;
- vesting, lock-up, transferability, and lost-key recovery;
- treasury, validator, ecosystem, community, and reserve allocations;
- fee schedule, burn policy, future issuance, and any supply cap;
- legal or economic rights, if any, associated with the proposed RFT asset.

The 1.309% selection is a policy input recorded in the current model, not a theorem that the rate is economically optimal.

## Separation from Phi-Genesis

Phi-Genesis studies a separate spectral quantity numerically near `1.309128920280813…`. That spectral value and the 1.309% founder-rate policy are different mathematical objects. The spectral computation does not define this allocation rate and does not establish tokenomics optimality.

See the [Constants Register](CONSTANTS_REGISTER.md), [Formalization Status](FORMALIZATION_STATUS.md), and [Architecture Decision Record](DECISIONS.md).
