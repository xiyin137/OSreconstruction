/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.TubeDomainExtension
import OSReconstruction.SCV.IdentityTheorem
import Mathlib.Analysis.Distribution.SchwartzSpace

/-!
# Distribution Theory Axioms for Tube Domains

This file provides two axioms from the theory of distributions and holomorphic
functions on tube domains. These are deep results from several complex variables
that connect distributional boundary values to pointwise properties of holomorphic
functions.

## Axioms

* `continuous_boundary_tube` — holomorphic functions on tube domains with tempered
  distributional boundary values extend continuously to the real boundary.

* `polynomial_growth_tube` — holomorphic functions on tube domains with tempered
  distributional boundary values satisfy polynomial growth estimates.

## Mathematical Background

A tube domain T(C) = ℝᵐ + iC (where C ⊂ ℝᵐ is an open convex cone) carries a
natural notion of "distributional boundary value": a holomorphic function F on T(C)
has distributional boundary values if for each Schwartz function f and approach
direction η ∈ C, the integrals

    ∫ F(x + iεη) f(x) dx

converge as ε → 0⁺ to a tempered distribution.

**Theorem (Vladimirov):** If F is holomorphic on T(C) and has tempered distributional
boundary values, then:
1. F extends continuously to the closure of T(C) at every real point
   (`continuous_boundary_tube`)
2. F satisfies polynomial growth estimates on approach regions
   (`polynomial_growth_tube`)

These results are proved in:
- Vladimirov, V.S. "Methods of the Theory of Generalized Functions" (2002), §25-26
- Epstein, H. "Generalization of the Edge-of-the-Wedge Theorem" (1960)
- Streater & Wightman, "PCT, Spin and Statistics", Theorem 2-6 and 2-9

## Why Axioms?

The proofs of these results require:
- The Paley-Wiener-Schwartz theorem (characterizing Fourier transforms of
  compactly supported distributions)
- The theory of Laplace transforms of tempered distributions
- Estimates on holomorphic functions via their Fourier-Laplace representation

None of these are currently available in Mathlib.

## Application

These axioms are used in `WickRotation.lean` to:
1. Prove that the BHW hypotheses (Lorentz invariance, boundary continuity,
   local commutativity of W_analytic) follow from the Wightman axioms
2. Establish temperedness (E0) of the constructed Schwinger functions
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set

namespace SCV

/-! ### Axiom 1: Continuous Boundary Values -/

/-- **Continuous boundary values for tube-domain holomorphic functions.**

    If F is holomorphic on a tube domain T(C) and has distributional boundary
    values (the smeared integrals ∫ F(x+iεη)f(x)dx converge as ε→0⁺), then
    F extends continuously to the real boundary: for each real point x,
    `ContinuousWithinAt F (TubeDomain C) (realEmbed x)`.

    This is a fundamental result connecting the distributional and pointwise
    theories of boundary values of holomorphic functions on tube domains.

    The proof (not formalized here) proceeds by:
    1. The Fourier-Laplace representation: F(z) = ∫ e^{iz·ξ} dμ(ξ) where μ is
       a tempered distribution supported in the dual cone C*
    2. The Laplace integral converges absolutely for Im(z) ∈ C and extends
       continuously to Im(z) → 0 by dominated convergence
    3. The boundary value of this representation is the distributional boundary
       value of F

    Ref: Vladimirov, "Methods of the Theory of Generalized Functions" §26.2;
    Epstein, J. Math. Phys. 1 (1960) 524-531;
    Streater-Wightman, Theorem 2-9 -/
axiom continuous_boundary_tube {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (TubeDomain C))
    (h_bv : ∃ (T : SchwartzMap (Fin m → ℝ) ℂ → ℂ),
      ∀ (f : SchwartzMap (Fin m → ℝ) ℂ) (η : Fin m → ℝ), η ∈ C →
        Filter.Tendsto (fun ε : ℝ =>
          ∫ x : Fin m → ℝ, F (fun i => ↑(x i) + ↑ε * ↑(η i) * I) * f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (T f)))
    (x : Fin m → ℝ) :
    ContinuousWithinAt F (TubeDomain C) (realEmbed x)

/-- **Distributional uniqueness for tube-domain holomorphic functions.**

    If two holomorphic functions on a tube domain T(C) have the same distributional
    boundary values, they are equal on T(C).

    This is a corollary of `continuous_boundary_tube` + the identity theorem:
    both functions extend continuously to the real boundary where they agree
    (as distributions, hence pointwise by continuity). They therefore agree on
    an open subset of T(C) (a neighborhood of any real boundary point), and by
    the identity theorem (`identity_theorem_tubeDomain`), they agree everywhere.

    Ref: Vladimirov §26.3; Streater-Wightman, Corollary to Theorem 2-9 -/
axiom distributional_uniqueness_tube {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    {F₁ F₂ : (Fin m → ℂ) → ℂ}
    (hF₁ : DifferentiableOn ℂ F₁ (TubeDomain C))
    (hF₂ : DifferentiableOn ℂ F₂ (TubeDomain C))
    -- Same distributional boundary values: for all Schwartz test functions f
    -- and approach directions η ∈ C, the boundary integrals of (F₁-F₂)*f → 0.
    (h_agree : ∀ (f : SchwartzMap (Fin m → ℝ) ℂ) (η : Fin m → ℝ), η ∈ C →
      Filter.Tendsto (fun ε : ℝ =>
        ∫ x : Fin m → ℝ,
          (F₁ (fun i => ↑(x i) + ↑ε * ↑(η i) * I) -
           F₂ (fun i => ↑(x i) + ↑ε * ↑(η i) * I)) * f x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0)) :
    ∀ z ∈ TubeDomain C, F₁ z = F₂ z

/-! ### Axiom 2: Polynomial Growth Estimates -/

/-- **Polynomial growth of holomorphic functions on tube domains.**

    If F is holomorphic on a tube domain T(C) with tempered distributional boundary
    values, then F satisfies polynomial growth estimates: for any compact subset
    K ⊂ C of approach directions, there exist C > 0 and N ∈ ℕ such that

        |F(x + iy)| ≤ C · (1 + ‖x‖)^N

    for all x ∈ ℝᵐ and y ∈ K.

    This is the key estimate needed to show that Wick-rotated Wightman functions
    define tempered distributions (OS axiom E0). The polynomial growth follows
    from the Fourier-Laplace representation: the Laplace transform of a tempered
    distribution has at most polynomial growth in the real directions.

    Ref: Streater-Wightman, Theorem 2-6;
    Jost, "The General Theory of Quantized Fields" §III.1;
    Vladimirov §25.3 -/
axiom polynomial_growth_tube {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (TubeDomain C))
    (h_bv : ∀ (η : Fin m → ℝ), η ∈ C →
      ∃ (T : (Fin m → ℝ) → ℂ), ContinuousOn T Set.univ ∧
        ∀ (f : (Fin m → ℝ) → ℂ), MeasureTheory.Integrable f →
          Filter.Tendsto (fun ε : ℝ =>
            ∫ x : Fin m → ℝ, F (fun i => ↑(x i) + ↑ε * ↑(η i) * I) * f x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (∫ x, T x * f x)))
    (K : Set (Fin m → ℝ)) (hK : IsCompact K) (hK_sub : K ⊆ C) :
    ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
      ∀ (x : Fin m → ℝ) (y : Fin m → ℝ), y ∈ K →
        ‖F (fun i => ↑(x i) + ↑(y i) * I)‖ ≤ C_bd * (1 + ‖x‖) ^ N

end SCV

end
