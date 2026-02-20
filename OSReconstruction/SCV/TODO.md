# SCV Module TODO

## Sorry Status

### Analyticity.lean — 0 sorrys ✓
### IteratedCauchyIntegral.lean — 0 sorrys ✓
### Polydisc.lean — 0 sorrys ✓
### Osgood.lean — 0 sorrys ✓
### TubeDomainExtension.lean — 0 sorrys ✓

All theorems fully proved. `edge_of_the_wedge_theorem` verified axiom-free.

## Proof Strategy (completed 2026-02-19)

The original approach via `rudin_mean_value_pos/neg` required Painlevé/Morera
(not in Mathlib). These were replaced by a **1D line argument**:

For ζ with all Im(ζ_j) > 0 in ball(0, δ/2):
1. Define L(z)_j = Re(ζ_j) + z * Im(ζ_j)
2. L(I) = ζ, L maps UHP → positive octant, LHP → negative octant
3. Apply `edge_of_the_wedge_1d` along L to get F_1d on ball(0, 2)
4. `rudin_mean_value_real` → F₀(L(t)) = bv_line(t) for real t near 0
5. Limit uniqueness → F_1d(t) = bv_line(t) for real t ∈ (-2, 2)
6. Identity theorem on V = L⁻¹(ball) ∩ U_L → F₀ ∘ L = F_1d
7. At z = I: F₀(ζ) = F_1d(I) = f_plus(Phi(ζ))

Symmetric argument for neg_agree (ζ with all Im < 0).

Dead code (`rudin_mean_value_pos/neg`) moved to `deprecated/`.

## Dependency Chain

```
cauchyIntegralPolydisc infrastructure ✓
        │
        ▼
differentiableOn_analyticAt (Analyticity.lean) ✓
        │
        ▼
rudin_mean_value_real (TubeDomainExtension.lean) ✓
        │
        ▼
rudin_orthant_extension (TubeDomainExtension.lean) ✓
        │
        ▼
edge_of_the_wedge_theorem (TubeDomainExtension.lean) ✓
```
