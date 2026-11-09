# RFT Tokenomics — Initial Policy

## Founder allocation
The old Rift prototype's 3.14% founder parameter is superseded by a one-time **1.309% genesis allocation**.

Exact representation:
- 1.309% = 0.01309 = 13,090 / 1,000,000;
- integer representation: 13,090 ppm;
- for genesis supply G: founder = floor(G × 13,090 / 1,000,000);
- remaining pool = G − founder.

The Lean core proves the allocation is bounded by G and that founder plus remainder equals G. The rounding convention is floor in the smallest integer accounting unit.

This is a one-time genesis allocation. It grants no ongoing share of future issuance, fees, reserves, treasury assets, customer deposits, equity, or protocol administration. Creator address, custody, vesting, transferability, total supply, decimals, and all other pools require explicit decisions before genesis.

The remaining 98.691% is not silently assigned. It remains an explicit unallocated pool until validator, treasury, community and ecosystem allocations are designed and approved.

The nearby Phi-Genesis spectral value is a separate mathematical research quantity. This tokenomics policy uses 1.309% as the requested policy input; it does not claim the spectral result proves economic optimality.
