# Blueprints for Remaining 9 Axioms (Gemini Review 2026-04-01)

## Two Buggy Axioms

### 1. `cr_integration_identity` is a TAUTOLOGY
The `∃ correction` makes it trivially true (correction = LHS - RHS).
Fix: replace with the exact 1D FTC integral remainder.

### 2. `fourierLaplaceExtMultiDim_boundaryValue` has WRONG RHS
Claims limit is `T f` but should be `T (Fourier.inv f)`.
F(z) = T(ψ_z) acts on momentum ξ. Integrating F(x)f(x) over x
passes inverse Fourier transform onto f.

## Proof Blueprints

### multiDimPsiZDynamic_seminorm_bound
- Leibniz rule (iteratedFDeriv_mul) splits into cutoff + exponential
- Cutoff: chain rule gives R^{-k} = (1+‖y‖)^k factor
- Exponential: |D^j exp(iz·ξ)| ≤ ‖z‖^j exp(-y·ξ)
- Cap: on support, -y·ξ ≤ ‖y‖R = ‖y‖/(1+‖y‖) ≤ 1, so exp ≤ e

### multiDimPsiZ_differenceQuotient_converges + _seminorm_continuous
- Pointwise scalarization: fix ξ, define scalar g(t) = ξ^α ∂^β [∂_{z_j} ψ_{z+te_j}(ξ)]
- intervalIntegral_deriv_eq_sub for the FTC
- norm_integral_le_integral_norm + uniform bound over ξ

### cr_integration_identity (after fix)
- g(τ) = ∫ F(x+iτη) φ(x) dx
- hasDerivAt_integral_of_dominated_loc_of_deriv_le to push d/dt inside
- CR: ∂_τ F = i(η·∇_x F)
- Integration by parts: integral_deriv_mul_eq_sub
- intervalIntegral_deriv_eq_sub on g(τ)

### tube_boundaryValueData_of_polyGrowth' (M=0)
- JUST DCT! No repeated integration needed
- tendsto_integral_filter_of_dominated_convergence
- Dominator: C(1+‖x‖+‖η‖)^N |φ(x)| ∈ L¹ (independent of ε)
- Limit defines W ∈ S'

### tube_boundaryValue_of_vladimirov_growth (M>0)
- Cauchy repeated integration, k = M+2
- H(x) = i^k/(k-1)! ∫₀^{t₀} (t₀-τ)^{k-1} F(x+iτη) dτ
- Singularity τ^{-M} * τ^{M+1} = τ¹ → integrable
- H continuous with polynomial growth → polyGrowth_temperedDistribution
- W = iteratedDistribDirectionalDeriv H η k + smooth correction
- BV by cr_integration_identity applied k times + DCT on remainder

## Execution Order
1. Fix buggy axioms (cr_integration_identity, boundaryValue)
2. tube_boundaryValueData_of_polyGrowth' (M=0 DCT — unlocks OS reconstruction)
3. cr_integration_identity (real-variable FTC)
4. multiDimPsiZDynamic_seminorm_bound (Leibniz + cap)
5. seminorm_continuous + differenceQuotient (pointwise scalarization)
6. tube_boundaryValue_of_vladimirov_growth (M>0 full converse)
