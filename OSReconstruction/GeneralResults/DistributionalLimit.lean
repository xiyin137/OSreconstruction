/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Distributional Limits of Equicontinuous Families

An equicontinuous family of tempered distributions `{T_ε}_{ε > 0}` that is
pointwise Cauchy (i.e., `T_ε(φ)` is Cauchy for each Schwartz φ) has a
distributional limit that is again a tempered distribution.

This is a consequence of the Banach-Steinhaus theorem / uniform boundedness
principle applied to the Schwartz dual.

## Main result

`distributional_limit_of_equicontinuous`: Given an equicontinuous family
of tempered distributions with the pointwise Cauchy property, the limit
exists as a continuous linear functional on Schwartz space.

## Applications

- `tube_boundaryValueData_of_polyGrowth'` (M=0 boundary value existence)
- `tube_boundaryValue_of_vladimirov_growth` (M>0 general converse)
- General distributional convergence arguments

## Mathematical background

In the strong dual topology on S'(ℝ^m), an equicontinuous and pointwise
convergent net converges to a CLM by:
1. Equicontinuity: ∃ finset s, C, ∀ ε, |T_ε(φ)| ≤ C · (s.sup seminorms)(φ)
2. Pointwise convergence: T_ε(φ) → W(φ) in ℂ for each φ
3. W is linear: from linearity of each T_ε + convergence
4. W is continuous: from the equicontinuity bound (preserved under limits)

## References

- Reed-Simon I, Theorem IV.21 (Banach-Steinhaus)
- Hörmander, "The Analysis of Linear PDOs I", §2.1
-/

open scoped Classical ComplexConjugate BigOperators NNReal
open MeasureTheory Filter
noncomputable section

variable {m : ℕ}

/-- **Distributional limit from equicontinuity + pointwise Cauchy.**

    If a family of tempered distributions `T : ℝ → S' → ℂ` satisfies:
    1. Equicontinuity: uniformly bounded by a finset sup of Schwartz seminorms
    2. Pointwise Cauchy: for each test function φ, the net T(ε)(φ) is Cauchy as ε → 0+

    then there exists a tempered distribution W with T(ε)(φ) → W(φ) as ε → 0+.

    **Proof sketch**:
    - Pointwise Cauchy + completeness of ℂ → pointwise limit W(φ) exists
    - Linearity: W(aφ + bψ) = lim T(ε)(aφ + bψ) = a·W(φ) + b·W(ψ)
    - Continuity: |W(φ)| = lim |T(ε)(φ)| ≤ C · (s.sup seminorms)(φ) (equicontinuity)
    - Package as CLM via `SchwartzMap.mkCLMtoNormedSpace` -/
axiom distributional_limit_of_equicontinuous
    (T : ℝ → SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    -- Equicontinuity: uniform seminorm bound
    (s : Finset (ℕ × ℕ)) (C_eq : ℝ) (hC_eq : 0 < C_eq)
    (hT_equicont : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        ‖T ε φ‖ ≤ C_eq * (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) φ)
    -- Pointwise Cauchy
    (hT_cauchy : ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
      ∀ δ > 0, ∃ ε₀ > 0, ∀ ε₁ ε₂ : ℝ,
        0 < ε₁ → ε₁ < ε₀ → 0 < ε₂ → ε₂ < ε₀ →
        ‖T ε₁ φ - T ε₂ φ‖ < δ) :
    ∃ (W : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ),
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        Tendsto (fun ε => T ε φ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (W φ))

end
