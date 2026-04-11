# Vladimirov-Tillmann Proof Branch Status

Branch: `vladimirov-tillmann-phase1-2` on `myfork` (mrdouglasny/OSreconstruction)
Updated: 2026-04-06

## Overview

10 new files, ~3800 lines. Goal: eliminate the `vladimirov_tillmann` axiom and prove
the VT converse (polynomial growth → tempered boundary values) needed for OS reconstruction.

## File Status

| File | Lines | Axioms | Sorrys | Status |
|------|-------|--------|--------|--------|
| `SCV/DualCone.lean` | 217 | 0 | 0 | **COMPLETE** |
| `SCV/ConeCutoffSchwartz.lean` | 864 | 0 | 0 | **COMPLETE** |
| `SCV/VladimirovProof.lean` | 79 | 0 | 0 | **COMPLETE** |
| `GeneralResults/DiffUnderIntegralSchwartz.lean` | 182 | 0 | 0 | **COMPLETE** |
| `GeneralResults/DistributionalLimit.lean` | 130 | 0 | 0 | **COMPLETE** |
| `SCV/FourierSupportCone.lean` | 184 | 1 | 0 | 1 axiom |
| `SCV/PaleyWienerSchwartz.lean` | 770 | 4 | 0 | 4 axioms |
| `SCV/TubeBoundaryValueExistence.lean` | 1227 | 1 | 0 | 1 axiom |
| `GeneralResults/SchwartzCutoffExp.lean` | 80 | 1 | 0 | 1 axiom |
| `GeneralResults/SmoothCutoff.lean` | 79 | 1 | 0 | 1 axiom |

**5 complete files** (0 axioms, 0 sorrys). **8 axioms** remain across 5 files.

## Remaining Axioms (8)

All reviewed by Gemini Deep Think and confirmed TRUE.

### Tier 1: General infrastructure (2)

**`exists_smooth_cutoff_of_closed`** (SmoothCutoff.lean)
- Smooth cutoff χ = 1 near closed set, χ = 0 far away, bounded derivatives
- Construction: convolution 1_A * φ with mollifier φ
- Difficulty: Medium. HilleYosida has a 1D mollifier; need multivariate version.

**`schwartz_seminorm_cutoff_exp_bound`** (SchwartzCutoffExp.lean)
- ‖ξ‖^k · ‖D^n[χ · exp(L)](ξ)‖ ≤ B · (1 + ‖L‖)^n
- Leibniz rule + polynomial × exponential decay estimate
- Difficulty: Medium. Pure calculus, well-understood blueprint.

### Tier 2: Schwartz seminorm estimates for ψ_z family (3)

**`psiZRSchwartz_seminorm_vladimirovBound`** (PaleyWienerSchwartz.lean)
- Vladimirov growth bound on dynamically-scaled ψ_{z,R(z)} seminorms
- ‖ψ_{z,R}‖_{k,n} ≤ B(1+‖z‖)^N (1+dist(Im z, ∂C)⁻¹)^M
- Depends on: `schwartz_seminorm_cutoff_exp_bound`
- Difficulty: Hard. Chain rule with scaling + boundary distance singularity.

**`multiDimPsiZ_seminorm_difference_bound`** (PaleyWienerSchwartz.lean)
- Lipschitz: ‖ψ_z - ψ_{z₀}‖_{k,n} ≤ D · ‖z - z₀‖ for ‖z-z₀‖ < δ
- Difficulty: Medium. Lipschitz of exp(iz·ξ) on compact tube cross-sections.

**`multiDimPsiZ_differenceQuotient_seminorm_bound`** (PaleyWienerSchwartz.lean)
- Convergence of difference quotients: ‖(ψ_{z+he_j} - ψ_z)/h - ψ'_j‖_{k,n} ≤ D|h|
- Taylor remainder |exp(ihξ_j) - 1 - ihξ_j| ≤ h²ξ_j²/2 + cutoff decay
- Difficulty: Medium.

### Tier 3: Boundary value convergence (2)

**`fourierLaplaceExtMultiDim_boundaryValue`** (PaleyWienerSchwartz.lean)
- BV of F(z) = T(ψ_z): ∫ F(x+iεη) f(x) dx → T(FT⁻¹(f)) as ε→0+
- Known issue: original RHS was T(f), should be T(FT⁻¹(f))
- Depends on: seminorm estimates (Tier 2)
- Difficulty: Hard. Equicontinuity + distributional limit.

**`tube_boundaryValue_of_vladimirov_growth`** (TubeBoundaryValueExistence.lean)
- THE main VT converse for M>0: Vladimirov growth → tempered BV exist
- Cauchy repeated integration k = M+2 times to regularize singularity
- Depends on: M=0 case (proved), CR identity (proved), all Tier 1-2
- Difficulty: Hard. The hardest remaining axiom.

### Tier 4: Fourier support (1)

**`fourierSupportInDualCone_of_tube_boundaryValue`** (FourierSupportCone.lean)
- Tube-holomorphic F with BV W ⟹ W has Fourier support in dual cone C*
- Depends on: full PW-Schwartz bridge (Tiers 1-3)
- Difficulty: Medium once Tier 3 is done.

## What's fully proved (no sorrys in chain)

- Dual cone: all properties, Hahn-Banach separation
- Concrete ψ_{z,R}: construction, decay, support, R-independence, iteratedFDeriv decay
- Fourier-Laplace extension: holomorphicity (via Osgood), Vladimirov growth bound
- Distributional limit: equicontinuous families → convergent
- Diff under integral: hasDerivAt for Schwartz-paired integrals
- Tube slice temperedness: each ε-slice defines a tempered distribution
- R-independence under Fourier support hypothesis
- M=0 boundary value (tube_boundaryValueData_of_polyGrowth') — OS critical
- CR + IBP keystone (hasDerivAt_tubeSlice_ray) — 493 lines
- DCT parameter continuity (continuous_tubeSlice_ray_deriv)

## Dependency DAG

```
Tier 1 (general):
  exists_smooth_cutoff_of_closed ──→ fixedConeCutoff_exists (PROVED)
  schwartz_seminorm_cutoff_exp_bound ──→ psiZRSchwartz_seminorm_vladimirovBound

Tier 2 (seminorm estimates):
  psiZRSchwartz_seminorm_vladimirovBound ──→ fourierLaplaceExtMultiDim_vladimirov_growth (PROVED)
  multiDimPsiZ_seminorm_difference_bound ──→ fourierLaplaceExtMultiDim_boundaryValue
  multiDimPsiZ_differenceQuotient_seminorm_bound ──→ fourierLaplaceExtMultiDim_boundaryValue

Tier 3 (boundary values):
  fourierLaplaceExtMultiDim_boundaryValue ──→ tube_boundaryValue_of_vladimirov_growth
  tube_boundaryValue_of_vladimirov_growth ──→ vladimirov_tillmann (TARGET)

Tier 4 (Fourier support):
  fourierSupportInDualCone_of_tube_boundaryValue ──→ vladimirov_tillmann (TARGET)
```

## Suggested Execution Order

1. `exists_smooth_cutoff_of_closed` — convolution mollifier (Tier 1)
2. `schwartz_seminorm_cutoff_exp_bound` — Leibniz + exp decay (Tier 1)
3. `psiZRSchwartz_seminorm_vladimirovBound` — dynamic scaling bound (Tier 2)
4. `multiDimPsiZ_seminorm_difference_bound` — Lipschitz (Tier 2)
5. `multiDimPsiZ_differenceQuotient_seminorm_bound` — Taylor remainder (Tier 2)
6. `fourierLaplaceExtMultiDim_boundaryValue` — BV convergence (Tier 3, fix RHS bug first)
7. `tube_boundaryValue_of_vladimirov_growth` — M>0 repeated Cauchy (Tier 3)
8. `fourierSupportInDualCone_of_tube_boundaryValue` — PW bridge (Tier 4)

## References

- Vladimirov, "Methods of the Theory of Generalized Functions" (2002), §25
- Hörmander, "The Analysis of Linear PDOs I" (1990), §7.4
- Streater & Wightman, "PCT, Spin and Statistics, and All That", Ch. 2
- `docs/vladimirov_tillmann_proof_plan.md` — 4-phase proof plan
- `docs/vladimirov_axiom_blueprints.md` — detailed proof sketches per axiom
- `docs/vladimirov_tillmann_gemini_reviews.md` — 4 Gemini reviews
