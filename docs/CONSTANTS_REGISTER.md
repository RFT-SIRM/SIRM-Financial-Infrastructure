# Constants and parameter register

Every numerical parameter used by the protocol must have a definition, unit, provenance, status, and owner. Numerical coincidence is not economic justification.

| Symbol / value | Meaning | Status | Permitted use |
|---|---|---|---|
| 10,000 basis points | 100% in the allocation representation | Definition | Exact integer share arithmetic |
| 3.14% | Historical founder-allocation value in the Rift prototype | Superseded / not adopted | Historical comparison only |
| 1.30912892028081… | Numerically reported spectral value in the Phi-Genesis theta = 2π spectral study | Research result; exact limit and closed form remain open in the cited project status | Research provenance only; not a financial rate |
| Founder share | Founder allocation parameter | Unselected | Must be approved as explicit policy before token genesis |

## Why 1.309 is not silently used as 1.309%

The value near 1.30912892028081… is a spectral quantity in a particular mathematical model. A spectral eigenvalue does not automatically define a percentage, monetary unit, issuance schedule, or founder allocation.

To connect it to token economics, a separate derivation would need to define a dimensionless mapping, justify its economic interpretation, prove required bounds and rounding behavior, and receive explicit governance approval. Until then the Lean core accepts a parameter in basis points but selects no default.

## Precision and rounding

The first core uses integer basis points and floor division. The remainder is explicit. Future work must define whether fractional token units exist, whether dust accumulates in a designated account, and how any rounding remainder is assigned. No implicit floating-point arithmetic is permitted in consensus-critical accounting.
