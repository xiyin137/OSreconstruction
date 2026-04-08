/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

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
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (Fin m) ℝ
  simp only [SchwartzMap.fourierTransformCLM_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  simp only [Real.fourierChar_apply, Circle.smul_def, mul_neg, neg_mul, smul_eq_mul]
  have hcomp := ((PiLp.volume_preserving_toLp (ι := Fin m)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin m → ℝ)).measurableEmbedding
      (fun x : EuclideanSpace ℝ (Fin m) =>
        cexp (↑(-2 * Real.pi * inner ℝ x ((EuclideanSpace.equiv (Fin m) ℝ).symm ξ)) * I) *
          ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (EuclideanSpace.equiv (Fin m) ℝ)) f) x)).symm
  calc
    ∫ v : EuclideanSpace ℝ (Fin m),
        cexp (↑(-(2 * Real.pi * inner ℝ v ((EuclideanSpace.equiv (Fin m) ℝ).symm ξ))) * I) *
          ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (EuclideanSpace.equiv (Fin m) ℝ)) f) v
      = ∫ y : WithLp 2 (Fin m → ℝ),
          cexp (↑(-(2 * Real.pi * inner ℝ y ((EuclideanSpace.equiv (Fin m) ℝ).symm ξ))) * I) * f y.ofLp := by
            simp [PiLp.coe_continuousLinearEquiv]
    _ = ∫ x : Fin m → ℝ,
          cexp (↑(-(2 * Real.pi * inner ℝ (WithLp.toLp 2 x) ((EuclideanSpace.equiv (Fin m) ℝ).symm ξ))) * I) *
            f ((EuclideanSpace.equiv (Fin m) ℝ) (WithLp.toLp 2 x)) := by
            simpa [EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using hcomp
    _ = ∫ x : Fin m → ℝ, cexp (-(2 * ↑Real.pi * I * (∑ i, (x i : ℂ) * (ξ i : ℂ)))) * f x := by
          apply integral_congr_ae
          filter_upwards with x
          have hx : ((EuclideanSpace.equiv (Fin m) ℝ) (WithLp.toLp 2 x)) = x := by
            ext i
            simp [EuclideanSpace.equiv]
          rw [hx]
          have hinner : inner ℝ (WithLp.toLp 2 x) ((EuclideanSpace.equiv (Fin m) ℝ).symm ξ) =
              ∑ i, x i * ξ i := by
            rw [PiLp.inner_apply]
            change ∑ i, ξ i * x i = ∑ i, x i * ξ i
            simp_rw [mul_comm]
          rw [hinner]
          congr 1
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

end
