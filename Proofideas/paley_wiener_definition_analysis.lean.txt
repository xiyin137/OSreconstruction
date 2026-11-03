/-
# Proof Ideas: PaleyWiener.lean Definition Issues and Sorry Analysis

## Date: 2026-03-07 (updated — Step A analysis added)

## Status: CRITICAL DEFINITION BUGS IDENTIFIED AND PARTIALLY FIXED

---

## 1. HasOneSidedFourierSupport — FIXED

### The Bug
The original definition:
```lean
def HasOneSidedFourierSupport (T : SchwartzMap ℝ ℂ → ℂ) : Prop :=
  ∀ (φ : SchwartzMap ℝ ℂ), (∀ x ∈ support φ, x < 0) → T φ = 0
```
This defines: "T annihilates test functions supported on (-∞,0)."
This is the condition that the DISTRIBUTIONAL SUPPORT of T lies in [0,∞), NOT the Fourier support.

Counter-example (Gemini, 2026-03-05): δ₁ (Dirac delta at x=1) satisfies the current definition
(support = {1} ⊂ [0,∞)) but its Fourier transform is e^{-iξ}, which does NOT have support in [0,∞).

### The Fix (applied 2026-03-05)
The correct definition:
```lean
def HasOneSidedFourierSupport (T : SchwartzMap ℝ ℂ → ℂ) : Prop :=
  ∀ (φ : SchwartzMap ℝ ℂ), (∀ x ∈ support φ, x < 0) →
    T (SchwartzMap.fourierTransformCLM ℂ φ) = 0
```
This says: T(F[φ]) = 0 for supp(φ) ⊂ (-∞,0). By Fourier duality, T(F[φ]) = T̂(φ).
So this correctly says: T̂ annihilates test functions supported on (-∞,0), i.e., supp(T̂) ⊆ [0,∞).

Required import: `Mathlib.Analysis.Distribution.SchwartzSpace.Fourier`

---

## 2. HasFourierSupportIn — NOT YET FIXED (TYPE ISSUE)

### The Bug
The definition:
```lean
def HasFourierSupportIn {m : ℕ} (T : SchwartzMap (Fin m → ℝ) ℂ → ℂ)
    (S : Set (Fin m → ℝ)) : Prop :=
  ∀ (φ : SchwartzMap (Fin m → ℝ) ℂ), (∀ x ∈ support φ, x ∉ S) → T φ = 0
```
Same issue: this captures distributional support, not Fourier support.

### The Type Problem
`SchwartzMap.fourierTransformCLM` requires `InnerProductSpace ℝ V` where the norm matches
the inner product. But `Fin m → ℝ` in Mathlib uses the **sup norm** (Pi.normedAddCommGroup),
which does NOT match the ℓ²-inner product (Pi.innerProductSpace). Hence type error.

### Correct Fix (not yet applied)
Replace `Fin m → ℝ` with `EuclideanSpace ℝ (Fin m)` throughout:
- `HasFourierSupportIn` definition
- `dualCone` definition
- `paley_wiener_cone`, `paley_wiener_converse` signatures
- All other multi-dimensional PW lemmas

This requires refactoring the entire multi-d PW framework. Left as TODO.

---

## 3. paley_wiener_one_step and paley_wiener_one_step_simple — INCORRECT HYPOTHESES

### The Problem
The `h_spectral` condition in both theorems uses DISTRIBUTIONAL support:
```lean
h_spectral : ∀ φ, (∀ x ∈ support φ, x < 0) → ∫ t, F(t) * φ(t) = 0
```
This says: the boundary value function has distributional support in [0,∞), i.e., f = 0 a.e. on (-∞,0).

### Physical Application Mismatch
The OS spectral condition gives: the Schwinger function's Fourier transform is supported in [0,∞)
(from positivity of the Hamiltonian). This is FOURIER SUPPORT, not distributional support.

These are different conditions:
- Distributional support in [0,∞): f(x) = 0 for x < 0
- Fourier support in [0,∞): f̂(ξ) = 0 for ξ < 0 ↔ f is a BV from above (holomorphic in UHP)

The Paley-Wiener theorem for the OS reconstruction should use the FOURIER support condition.

### The Conclusion Problem in paley_wiener_one_step_simple
The conclusion `∀ x : ℝ, F_ext ↑x = f x` (pointwise equality on ℝ) is INCORRECT for
polynomial-growth functions. For f ∈ L¹ ∩ L²([0,∞)), the Laplace transform F(z) = ∫₀^∞ f(t)e^{izt}dt
has F(x) = (Fourier transform of f)(x) which need not equal f(x). The boundary value of F on ℝ
is the Fourier transform f̂, NOT f itself.

### Correct Conclusion
The conclusion should be that F_ext has distributional boundary value equal to f:
```lean
∀ φ : SchwartzMap ℝ ℂ,
  Tendsto (fun η => ∫ x, F_ext (x + η*I) * φ x) (nhdsWithin 0 (Ioi 0)) (nhds (∫ x, f x * φ x))
```

---

## 4. Sorry Status in PaleyWiener.lean

All 5 sorrys remain blocked by FL theory not in Mathlib:

| Sorry | Status | Blocker |
|-------|--------|---------|
| `paley_wiener_half_line` | SORRY | Needs FL distribution theory |
| `paley_wiener_cone` | SORRY | Needs multi-d FL theory |
| `paley_wiener_converse` | SORRY | Needs FL inversion |
| `paley_wiener_one_step` | SORRY | Needs PW half-line + Osgood |
| `paley_wiener_one_step_simple` | SORRY + WRONG STATEMENT | See above |

`paley_wiener_unique` is PROVED (uses distributional_uniqueness_tube).

---

## 5. Proof Strategy for paley_wiener_half_line (with corrected definition)

With the correct Fourier support definition, the proof strategy is:

**Approach: Smooth Cutoff (Fourier-Laplace)**

Define: F(z) = T(F^{-1}[χ(ξ) e^{izξ}]) where χ is a smooth cutoff (= 1 for ξ ≥ 0, = 0 for ξ ≤ -1).

For Im(z) > 0: χ(ξ)e^{izξ} = χ(ξ) e^{iRe(z)ξ} e^{-Im(z)ξ}
- For ξ ≥ 0: decays as e^{-Im(z)ξ} ✓
- For ξ ≤ -1: χ(ξ) = 0 ✓
- For -1 ≤ ξ ≤ 0: bounded ✓
So ξ ↦ χ(ξ)e^{izξ} is in L¹(ℝ), and its inverse FT F^{-1}[χe^{iz·}] ∈ 𝓢(ℝ,ℂ) (by smooth cutoff).

Holomorphicity: differentiate under T.
BV condition: as η → 0+, F^{-1}[χe^{iz·}] → F^{-1}[χe^{ix·}]. For the HasOneSidedFourierSupport
condition (supp(T̂) ⊆ [0,∞)): T(F^{-1}[φ]) = T̂(φ)/normalization, so T(F^{-1}[χe^{ix·}])
= T̂(χ e^{ix·})(ξ) which recovers T̂ at real frequencies ξ ≥ 0 → the BV is T(f) for Schwartz f.

Key obstacle in Lean formalization:
- Showing F^{-1}[χ(ξ)e^{izξ}] ∈ 𝓢(ℝ,ℂ) as a function of z (holomorphic map into Schwartz)
- Differentiating T under the Schwartz topology
- Identifying the BV via the HasOneSidedFourierSupport condition

---

## 6. isConnected_permutedExtendedTube_inter_translate Analysis

Gemini consultation (2026-03-05) suggests D = PET ∩ (PET-c) might be DISCONNECTED for general c.
The "starburst" structure of PET could fracture under translation.

**Recommendation (Gemini Path B)**: Instead of proving D is connected, prove bhw_translation_invariant
using only the connected component of D containing FT ∩ (FT-c):
1. D' = connected component of D containing FT ∩ (FT-c)
2. G = F_ext on FT ∩ (FT-c) ⊆ D'
3. Identity theorem on D': G = F_ext on all of D'
4. For z ∉ D', the translation invariance might not hold (if D is disconnected)

This weakens `bhw_translation_invariant` but might be mathematically correct.

**Alternative**: Reformulate everything in difference variables (Gemini Path A) — requires
major refactoring but matches the physics literature (Streater-Wightman pg. 65).

Numerical evidence: 9 test cases for d=1, n=2 all returned 1 connected component (D connected).
Confidence: medium-high for small n,d but uncertain for large n.

---

## 7. LaplaceSchwartz.lean Sorrys

All 5 sorrys require FL theory (Vladimirov §25-26), not in Mathlib:
1. `fourierLaplace_continuousWithinAt` — requires pointwise (not distributional) BV extension
   (stronger than HasFourierLaplaceRepr provides without regularity assumptions on dist)
2. `fourierLaplace_uniform_bound_near_boundary` — requires growth bounds from FL repr
3. `fourierLaplace_polynomial_growth` — Vladimirov Theorem 25.5
4. `polynomial_growth_of_continuous_bv` — requires FL repr → regularity
5. `fourierLaplace_boundary_continuous` — requires regularity of boundary function

All blocked until FL theory is formalized in Mathlib or built from scratch.

---

## 8. SchwingerAxioms.lean Sorrys

All 5 sorrys require FL/PW theory or deep distribution theory:
1. `polynomial_growth_forwardTube_full` — Vladimirov, requires FL repr
2. `polynomial_growth_on_PET` — depends on (1)
3. `schwinger_os_term_eq_wightman_term` — distributional BV identity; requires PW
4. `bhw_pointwise_cluster_forwardTube` — analytic continuation of cluster property
5. `W_analytic_cluster_integral` — depends on (4), DCT application

---

## 9. OSToWightman.lean Axiom Transfer Sorrys

All 12 sorrys require FL/PW theory:
- `inductive_analytic_continuation` — the central sorry; needs PW one-step extension
- `schwinger_holomorphic_on_base_region` — Schwinger kernel ↔ distribution
- `extend_to_forward_tube_via_bochner` — Bochner tube theorem (itself sorry)
- `full_analytic_continuation` (2 holes) — combination
- `forward_tube_bv_tempered` — Vladimirov distributional BV theorem
- Axiom transfers (5 sorrys) — all depend on FL+BV infrastructure
- `bvt_cluster` — cluster property transfer

Note on `bv_hermiticity_transfer` (line 625): This sorry may be missing an OS Hermiticity/
reality axiom in its hypothesis list. The OS axioms should include:
S_n(g) = conj(S_n(f)) when g(x) = conj(f(rev x))
Check OsterwalderSchraderAxioms in SchwingerAxioms.lean.

---

## 10. Root Blocker Summary

**All project sorrys ultimately blocked by ONE root blocker:**

> Fourier-Laplace theory for tube domains (Vladimirov §25-26) is NOT in Mathlib.

Required theory:
1. The Fourier-Laplace transform T(ξ ↦ e^{iz·ξ}) for tempered distributions T
2. Holomorphicity on the tube domain T(C) when supp(T̂) ⊆ dualCone(C)
3. Polynomial growth bounds (Theorem 25.5 in Vladimirov)
4. Distributional boundary value recovery

Until this is in Mathlib or built from scratch, the project will remain heavily sorry-laden.

-/

/-!
## 11. Step A Analysis: The Distributional BV Exchange (2026-03-07)

This section documents the mathematical analysis of the key blocker for
`paley_wiener_half_line`: the "distributional Fubini" needed to exchange T
(a CLM on Schwartz space) with the x-integral.

### 11.1 The Problem Setup

The goal is to prove:
  ∫ x : ℝ, F(↑x + ↑η * I) * φ(x) → T(φ)  as η → 0+

where F(x+iη) = T(FT[schwartzPsiZ(x+iη)]).

The proof chain (Steps A-D) is:
- Step A: ∫ x, F(x+iη) * φ(x) = T̂(G_η)  [BLOCKER, see below]
  where T̂ = T ∘ FT : SchwartzMap ℝ ℂ →L[ℂ] ℂ
  and G_η(ξ) = ∫ x, ψ_{x+iη}(ξ) * φ(x) = χ(ξ)*exp(-ηξ)*FT⁻¹[φ](ξ/(2π))
             = Φ_η(ξ)   [from psiZ_pairing_formula, PROVED]
  Note: T̂(G_η) = T(FT[G_η]) = T(FT[Φ_η])
- Step B: T(FT[(exp(-η·)-1)·χ·ψ]) → 0  [PROVED: tendsto_fourier_expDampingCutoff_zero]
- Step C: T(FT[χ·ψ]) = T(FT[ψ])  [PROVED: fourier_pairing_cutoffSchwartz_eq]
- Step D: T(FT[ψ]) = T(φ) where ψ = FT⁻¹[φ]  [Fourier inversion, need: FT∘FT⁻¹ = id]

Chain from T̂(G_η) = T(FT[Φ_η]) to T(φ):
  T(FT[Φ_η]) = T(FT[χ·exp(-η·)·ψ])
             = T(FT[χ·ψ]) + T(FT[(exp(-η·)-1)·χ·ψ])
             → T(FT[χ·ψ]) + 0   [Step B]
             = T(FT[ψ])          [Step C]
             = T(φ)              [Step D: FT[FT⁻¹[φ]] = φ]

### 11.2 Why Step A Is Hard

Step A requires: T̂(G_η) = ∫ x, T̂(ψ_{x+iη}) * φ(x)
i.e., T̂(∫ x, ψ_{x+iη} * φ(x)) = ∫ x, T̂(ψ_{x+iη}) * φ(x)
where the integral ∫ x, ψ_{x+iη} * φ(x) lives in SchwartzMap ℝ ℂ.

The obstruction: SchwartzMap is a FRÉCHET space, not Banach.
Mathlib's `ContinuousLinearMap.integral_comp_comm` requires Banach spaces:
  `T (∫ x, f x ∂μ) = ∫ x, T (f x) ∂μ`
requires `E →L[𝕜] F` with both E, F NormedAddCommGroup + CompleteSpace.

SchwartzMap does NOT satisfy NormedAddCommGroup (it's not normable).
So `integral_comp_comm` CANNOT be applied directly to SchwartzMap-valued integrals.

### 11.3 Standard Mathematical Approaches

**Approach 1: Structure theorem for distributions (Vladimirov)**
T = Σ D^α μ_α (finite derivatives of polynomially bounded measures).
Then exchange via Fubini for measures.
In Lean: requires full structure theorem — NOT in Mathlib, ~500 lines to develop.

**Approach 2: Riemann sum + Fréchet continuity**
T(G_η) = lim_{N→∞} T(Σ_j ψ_{j/N+iη} φ(j/N)/N) [Riemann sums → G_η in Fréchet topology]
       = lim_{N→∞} Σ_j T(ψ_{j/N+iη}) φ(j/N)/N   [T linear, finite sums]
       = ∫ x, T(ψ_{x+iη}) φ(x)                   [Riemann sum → scalar integral]
Requires: Riemann sums converge to G_η in Schwartz topology (all seminorms).
In Lean: ~200 lines, uses schwartzPsiZ_seminorm_horizontal_bound.

**Approach 3: Hahn-Banach factorization + Bochner in Banach space (recommended by Gemini)**
From schwartz_functional_bound: |T̂(f)| ≤ C * Σ_{p∈s} seminorm(p)(f)
Define Banach space E = (s : Finset (ℕ×ℕ)) → BoundedContinuousFunction ℝ ℂ
Define ι : SchwartzMap → E by ι(f)(p)(ξ) = ξ^{p.1} * ∂^{p.2} f(ξ)
By Hahn-Banach: ∃ L : E →L[ℂ] ℂ, T̂ = L ∘ ι
Then: ∫ T̂(ψ_x φ(x)) = ∫ L(ι(ψ_x) φ(x)) = L(∫ ι(ψ_x) φ(x))  [Banach integral_comp_comm for L!]
And: ∫ ι(ψ_x) φ(x) = ι(G_η)  [by differentiating under the integral sign, scalar]
So: L(ι(G_η)) = T̂(G_η).
In Lean: ~100-120 lines, uses exists_extension_norm_eq + integral_comp_comm + hasDerivAt_integral.

### 11.4 Recommended Lean Proof Path for Step A

The cleanest Lean formalization uses Approach 3 (Hahn-Banach + Bochner):

Phase 1: Define the Banach embedding space (~30 lines)
  - Define schwartzBanachEmbedding s := (p : s) → (ℝ →ᵇ ℂ)  (product of Banach spaces)
  - Define the CLM schwartzEmbed : SchwartzMap ℝ ℂ →L[ℂ] schwartzBanachEmbedding s
    by schwartzEmbed(f)(p)(ξ) = ξ^{p.1} * iteratedDeriv p.2 f ξ
    (bounded by SchwartzMap decay, continuous from contDiff)

Phase 2: Hahn-Banach extension (~30 lines)
  - T̂ bounded by the norm of schwartzEmbed(f): |T̂(f)| ≤ C * ‖schwartzEmbed(f)‖_E
  - Apply exists_extension_norm_eq to extend T̂ from range(schwartzEmbed) to E
  - Obtain L : E →L[ℂ] ℂ with T̂ = L ∘ schwartzEmbed

Phase 3: Differentiation under the integral sign (~50 lines)
  - For each p=(k,n) and each ξ₀, show HasDerivAt for the map
    ξ ↦ ∫ x, ξ^k * iteratedDeriv n (schwartzPsiZ(x+iη)) ξ * φ(x)
  - Use hasDerivAt_integral_of_dominated_loc_of_deriv_le
  - Bound: ‖∂_ξ(ξ^k * ∂^n ψ_{x+iη}(ξ))‖ ≤ C_{k,n}(η) * (1+|x|)^{n+1}
    and ∫ (1+|x|)^{n+1} |φ(x)| < ∞ since φ is Schwartz
  - Iterate to get: schwartzEmbed(G_η) = ∫ x, schwartzEmbed(ψ_{x+iη}) * φ(x)  in E

Phase 4: Combine (~10 lines)
  - ∫ T̂(ψ_{x+iη}) φ(x) = ∫ L(schwartzEmbed(ψ_{x+iη})) φ(x)
                         = L(∫ schwartzEmbed(ψ_{x+iη}) φ(x))  [integral_comp_comm for L on Banach E]
                         = L(schwartzEmbed(G_η))               [Phase 3 result]
                         = T̂(G_η) = T(FT[G_η]) = T(FT[Φ_η])

### 11.5 Key Mathlib Lemmas Needed

1. `schwartz_functional_bound` — T bounded by finitely many seminorms [PROVED]
2. `SchwartzMap.toBoundedContinuousFunctionCLM` — embedding to BCF [IN MATHLIB]
3. `exists_extension_norm_eq` — Hahn-Banach for bounded linear functionals [IN MATHLIB]
4. `hasDerivAt_integral_of_dominated_loc_of_deriv_le` — diff under integral [IN MATHLIB]
5. `ContinuousLinearMap.integral_comp_comm` — exchange CLM with Bochner integral [IN MATHLIB]
6. `FourierPair.fourierInv_fourier_eq` — Fourier inversion on SchwartzMap [IN MATHLIB]
7. `FourierInvPair.fourier_fourierInv_eq` — inverse Fourier inversion [IN MATHLIB]

### 11.6 Approach 2 (Riemann Sums) Details

If Hahn-Banach is too complex, Approach 2 can work:

For Step A via Riemann sums, need a key lemma:
  schwartz_valued_riemann_sum_convergence:
    f : ℝ → SchwartzMap ℝ ℂ  (continuous, polynomial seminorm bounds)
    φ : SchwartzMap ℝ ℂ       (Schwartz test function)
    G : SchwartzMap ℝ ℂ       (G(ξ) = ∫ x, f(x)(ξ) * φ(x), defined pointwise)
    CONCLUSION: seminorm(k,n)(Σ_j f(x_j)φ(x_j)/N - G) → 0 for all k, n

The bound needed: seminorm(k,n)(Σ_j f(x_j)φ(x_j)/N - G)
= sup_ξ |ξ^k ∂^n_ξ (Σ_j f(x_j)(ξ)φ(x_j)/N - G(ξ))|
≤ sup_ξ ∫ |ξ^k ∂^n_ξ f(x)(ξ)| |Riemann_error(x)| dx
→ 0 by Fubini + dominated convergence.

This requires:
- SchwartzMap.iteratedDeriv is continuous in the ξ argument
- Uniform bounds on Schwartz seminorms of the family ψ_{x+iη} (already available)
- Standard Riemann sum convergence theorem
- Dominated convergence in sup_ξ (requires exchange of sup and limit — tricky!)

The sup_ξ exchange with the limit is the hardest part of Approach 2.
It requires uniform convergence of the Riemann sum error in ξ, which follows
from the fact that all functions are Schwartz (decay rapidly).
But formalizing this uniformity rigorously is about 100 lines.

### 11.7 Recommendation

For the Lean formalization, **Approach 3 (Hahn-Banach + Bochner)** is recommended.
It avoids all topological convergence issues in Schwartz space and reduces to:
- A single Hahn-Banach application (well-supported in Mathlib)
- Bochner integral exchange (well-supported in Mathlib)
- Scalar differentiation under the integral sign (well-supported in Mathlib)

Total estimated Lean code: ~120-150 lines for the new infrastructure, plus the
Step A proof itself (~30 lines using the infrastructure).

The infrastructure should be in a NEW file:
  OSReconstruction/SCV/SchwartzBochner.lean

-/

section PaleyWienerAnalysis
end PaleyWienerAnalysis
