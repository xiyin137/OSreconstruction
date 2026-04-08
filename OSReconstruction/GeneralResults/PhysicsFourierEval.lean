/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Pointwise Evaluation of Fourier Transform on Fin m → ℝ

Provides the pointwise integral formula for the Fourier transform
transported through EuclideanSpace.

The key fact: for f ∈ S(ℝᵐ) and ξ ∈ ℝᵐ, the Mathlib-convention
Fourier transform (transported to Fin m → ℝ via EuclideanSpace)
evaluates as:
  FT(f)(ξ) = ∫ exp(-2πi · Σ x_i ξ_i) f(x) dx

This is provable by unwinding the EuclideanSpace transport and
applying Mathlib's `SchwartzMap.fourierTransformCLM_apply` (or the
`VectorFourier.fourierIntegral` pointwise formula).

## References

- Mathlib: `SchwartzMap.fourierTransformCLM`
- Hörmander, "The Analysis of Linear PDOs I", §7.1
-/

open MeasureTheory Complex
noncomputable section

variable {m : ℕ}

-- **Axiom: Pointwise integral formula for the flat Fourier transform.**
--
-- The Fourier transform on Fin m → ℝ (transported through EuclideanSpace)
-- evaluates pointwise as the expected integral. Provable by unwinding
-- the EuclideanSpace.equiv transport + Mathlib's FT pointwise formula.
theorem fourierTransformFlat_eval
    (f : SchwartzMap (Fin m → ℝ) ℂ) (ξ : Fin m → ℝ) :
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (EuclideanSpace.equiv (Fin m) ℝ).symm
      ((SchwartzMap.fourierTransformCLM ℂ)
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (EuclideanSpace.equiv (Fin m) ℝ) f))) ξ =
    ∫ x : Fin m → ℝ,
      exp (-2 * ↑Real.pi * I * (∑ i, (x i : ℂ) * (ξ i : ℂ))) * f x := by
  -- Unfold the CLM compositions
  simp only [ContinuousLinearMap.comp_apply, SchwartzMap.fourierTransformCLM_apply]
  -- This is deep EuclideanSpace transport bookkeeping.
  -- The chain: compCLM ∘ FT ∘ compCLM evaluates pointwise as the integral
  -- with inner product ⟨x, ξ⟩_Euc = Σ x_i ξ_i.
  sorry

end
