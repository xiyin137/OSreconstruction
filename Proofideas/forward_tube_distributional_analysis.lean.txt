/-
# Forward Tube Distributional Theorems: Correctness and Proof Analysis

Date: 2026-03-08
Author: Claude Code

## Statement Correctness

### distributional_uniqueness_forwardTube (line 560) — CORRECTLY STATED
Conclusion: ∀ z ∈ ForwardTube d n, F₁ z = F₂ z
This only evaluates F₁, F₂ on the tube INTERIOR (where they're holomorphic).
No dependence on boundary behavior of the total function.

### continuous_boundary_forwardTube (line 536) — STATEMENT ISSUE
Conclusion: ContinuousWithinAt F (ForwardTube d n) (realEmbed x)
This requires F(realEmbed x) = lim_{z→realEmbed(x)} F(z).
But realEmbed x ∉ ForwardTube, so F(realEmbed x) is determined by the total
function, not by holomorphicity on the tube. The hypotheses (DifferentiableOn +
distributional BV) don't constrain F at boundary points.

Counterexample: Take F₀ holomorphic on forward tube with BV → T.
Define F(z) = F₀(z) for z ∈ ForwardTube, F(z) = F₀(z) + 1 elsewhere.
Then F is DifferentiableOn ForwardTube with same BV, but ContinuousWithinAt fails
because F(realEmbed x) = F₀(realEmbed x) + 1 ≠ lim F(z) = lim F₀(z) = F₀(realEmbed x).

### boundary_value_recovery_forwardTube (line 585) — STATEMENT ISSUE
Conclusion: T f = ∫ F(realEmbed x) * f x
Same issue: evaluates F at boundary points.

### boundary_function_continuous_forwardTube (line 612) — STATEMENT ISSUE
Conclusion: Continuous (fun x => F(realEmbed x))
Same issue: evaluates F at boundary points.

## Why This Matters for the Wightman Reconstruction

In BHWExtension.lean, these are applied to (Wfn.spectrum_condition n).choose,
which is a total function from the existential in WightmanFunctions.spectrum_condition.
The spectrum_condition only guarantees:
  ∃ W_analytic, DifferentiableOn ℂ W_analytic (ForwardTube d n) ∧ [distributional BV]

The .choose extracts SOME such function. Its boundary values are unconstrained.
The theorems would be correct if:
  (a) spectrum_condition were strengthened to include boundary regularity, OR
  (b) the theorems were reformulated to avoid evaluating F at boundary points.

## Proposed Fix Options

### Option A: Reformulate the 3 problematic theorems
Replace conclusions with existential forms:
- continuous_boundary_forwardTube:
    ∃ L, Filter.Tendsto F (nhdsWithin (realEmbed x) (ForwardTube d n)) (nhds L)
- boundary_value_recovery:
    T f = ∫ ... (using the limit function, not F directly)
- boundary_function_continuous:
    ∃ G : NPointDomain d n → ℂ, Continuous G ∧
      ∀ x, G x = lim_{z→realEmbed(x)} F(z) within ForwardTube

### Option B: Strengthen spectrum_condition
Add to WightmanFunctions.spectrum_condition:
  the W_analytic also satisfies ContinuousWithinAt at boundary points.
This is a theorem in physics (follows from FL representation) but can be stated as
part of the axiom to make downstream arguments clean.

### Option C: Add HasFourierLaplaceReprRegular to spectrum_condition
Add to WightmanFunctions.spectrum_condition:
  the flattened W_analytic has HasFourierLaplaceReprRegular.
This is the strongest form and directly enables all downstream proofs.

## Proof Strategy for distributional_uniqueness_forwardTube

This is correctly stated and IS the highest-value target.

The standard proof (Vladimirov §25, Thm 25.3) requires:
1. G = F₁ - F₂ holomorphic on T_C with distributional BV → 0
2. Vladimirov-Tillmann: G has polynomial growth on compact subcones of C
3. G has Fourier-Laplace representation G = FL(μ) with μ supported in C*
4. BV(G) = μ̂ = 0, so μ = 0, so G = 0

Steps 2-3 are the deep infrastructure (currently missing).

Alternative proof (via existing infrastructure):
1. Construct HasFourierLaplaceReprRegular for flattened G with dist = 0
2. Apply distributional_uniqueness_forwardTube_of_flatRegular (PROVED)
This reduces to building the Regular package, which requires same infrastructure.

### Infrastructure needed: Vladimirov-Tillmann theorem
Statement: If G is holomorphic on T_C and has distributional boundary values,
then for each compact K ⊆ C, there exist C_bd, N such that
  |G(x+iy)| ≤ C_bd * (1+|x|)^N for y ∈ K.

The standard proof (Vladimirov §25.1) uses:
- Cauchy integral formula on polydiscs
- Uniform boundedness principle (Banach-Steinhaus) for Schwartz functionals
- The distributional BV gives a family of tempered distributions {T_ε}_{ε>0}
  that converge pointwise; Banach-Steinhaus gives uniform seminorm bounds
- These bounds translate to polynomial growth of G via Cauchy estimates

This is the ROOT BLOCKER for all 4 sorrys.

## Downstream Dependencies

distributional_uniqueness_forwardTube
  → BHWExtension.W_analytic_lorentz_on_tube
  → BHWTranslation (line 273)

continuous_boundary_forwardTube
  → BHWExtension.W_analytic_continuous_boundary

boundary_value_recovery_forwardTube
  → BHWExtension.W_analytic_swap_boundary_pairing_eq

boundary_function_continuous_forwardTube
  → BHWExtension.analytic_boundary_local_commutativity
-/
