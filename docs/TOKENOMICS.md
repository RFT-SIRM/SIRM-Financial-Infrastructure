# RFT Tokenomics: Initial Policy Record

## Selected founder genesis allocation

The founder allocation is **1.309% of the total genesis supply**, replacing the legacy Rift prototype's 3.14% value.

Exact representation:

- 1.309% = 0.01309;
- 0.01309 = 13,090 / 1,000,000;
- integer rate = 13,090 ppm;
- founder units for genesis supply `G` = `floor(G * 13_090 / 1_000_000)`;
- unallocated remainder = `G - founder`.

The floor is taken in the smallest integer accounting unit. The result cannot exceed `G`, and founder allocation plus remainder equals `G`; these properties are included in the Lean model.

Example only: for `G = 1,000,000,000,000` base units, founder allocation is `13,090,000,000` base units. This example does not select the actual genesis supply or token decimals.

## Scope

This is a one-time genesis allocation. It does not grant automatic rights to future issuance, transaction fees, reserves, treasury assets, customer deposits, governance control, validator rewards, or protocol administration.

## Explicitly unresolved

- total genesis supply and token decimals;
- founder receiving address and custody arrangements;
- vesting, lock-up, transferability, and lost-key recovery;
- treasury, validator, ecosystem, community, and reserve allocations;
- fee schedule, burn policy, future issuance, and any supply cap;
- whether RFT is only a network utility asset or has any other defined legal/economic rights.

The remaining 98.691% is an explicit unallocated pool in the initial model. It is not silently transferred to the treasury or community.

## Spectral-value separation

Phi-Genesis contains a distinct numerical spectral quantity near `1.309128920280813…`. Its exact limit and closed form are not established in the cited research note. It is not the same object as the 1.309% policy rate and does not establish economic optimality.