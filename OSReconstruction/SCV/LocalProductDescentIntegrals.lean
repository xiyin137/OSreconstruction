/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.LocalProductDescent

/-!
# Integral identities for local product-kernel descent

This file contains the sign-sensitive mixed-fiber change-of-variables and
partial-evaluation identities used by the local product-test descent theorem.
The substrate constructions live in `LocalProductDescent.lean`; this companion
keeps the next layer small.
-/

noncomputable section

open Complex MeasureTheory

namespace SCV

/-- The left local descent parameter test integrates to the sheared
`realConvolutionTest φ ψ ⊗ η`. -/
theorem mixedRealFiberIntegralCLM_localDescentParamTestLeft {m : ℕ}
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ η : SchwartzMap (Fin m → ℝ) ℂ) :
    mixedRealFiberIntegralCLM (localDescentParamTestLeft φ ψ η) =
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (realConvolutionShearCLE m).symm)
        (schwartzTensorProduct₂ (realConvolutionTest φ ψ) η) := by
  ext p
  rcases p with ⟨z, t⟩
  rw [mixedRealFiberIntegralCLM_apply]
  change (∫ a : Fin m → ℝ, localDescentParamTestLeft φ ψ η ((z, t), a)) =
    schwartzTensorProduct₂ (realConvolutionTest φ ψ) η
      ((realConvolutionShearCLE m).symm (z, t))
  rw [realConvolutionShearCLE_symm_apply]
  rw [schwartzTensorProduct₂_apply]
  rw [realConvolutionTest_apply]
  have htrans :
      (∫ a : Fin m → ℝ, φ (z - realEmbed a) * ψ (t + a)) =
        ∫ b : Fin m → ℝ, φ (z + realEmbed t - realEmbed b) * ψ b := by
    rw [← integral_add_right_eq_self
      (μ := (volume : Measure (Fin m → ℝ)))
      (f := fun b : Fin m → ℝ => φ (z + realEmbed t - realEmbed b) * ψ b) t]
    apply integral_congr_ae
    filter_upwards with a
    have hz : z + realEmbed t - realEmbed (a + t) = z - realEmbed a := by
      ext i
      simp [realEmbed, sub_eq_add_neg, add_assoc, add_comm]
    have htadd : t + a = a + t := by
      ext i
      simp [add_comm]
    rw [htadd]
    rw [hz]
  calc
    ∫ a : Fin m → ℝ, localDescentParamTestLeft φ ψ η ((z, t), a)
        = ∫ a : Fin m → ℝ, φ (z - realEmbed a) * η t * ψ (t + a) := by
            apply integral_congr_ae
            filter_upwards with a
            simp
    _ = ∫ a : Fin m → ℝ, η t * (φ (z - realEmbed a) * ψ (t + a)) := by
            apply integral_congr_ae
            filter_upwards with a
            ring
    _ = η t * ∫ a : Fin m → ℝ, φ (z - realEmbed a) * ψ (t + a) := by
            exact integral_const_mul (μ := (volume : Measure (Fin m → ℝ)))
              (η t) (fun a : Fin m → ℝ => φ (z - realEmbed a) * ψ (t + a))
    _ = η t * ∫ b : Fin m → ℝ, φ (z + realEmbed t - realEmbed b) * ψ b := by
            rw [htrans]
    _ = (∫ b : Fin m → ℝ, φ (z + realEmbed t - realEmbed b) * ψ b) * η t := by
            ring

/-- The right local descent parameter test integrates back to `φ ⊗ ψ` when
the parameter cutoff is normalized. -/
theorem mixedRealFiberIntegralCLM_localDescentParamTestRight {m : ℕ}
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη_norm : ∫ a : Fin m → ℝ, η a = 1) :
    mixedRealFiberIntegralCLM (localDescentParamTestRight φ ψ η) =
      schwartzTensorProduct₂ φ ψ := by
  ext p
  rcases p with ⟨z, t⟩
  rw [mixedRealFiberIntegralCLM_apply]
  rw [schwartzTensorProduct₂_apply]
  have htranslate :
      (∫ a : Fin m → ℝ, η (t - a)) = ∫ a : Fin m → ℝ, η a := by
    calc
      (∫ a : Fin m → ℝ, η (t - a))
          = ∫ a : Fin m → ℝ, η (t + a) := by
              rw [← integral_neg_eq_self
                (μ := (volume : Measure (Fin m → ℝ)))
                (f := fun a : Fin m → ℝ => η (t + a))]
              apply integral_congr_ae
              filter_upwards with a
              simp [sub_eq_add_neg]
      _ = ∫ a : Fin m → ℝ, η (a + t) := by
              apply integral_congr_ae
              filter_upwards with a
              simp [add_comm]
      _ = ∫ a : Fin m → ℝ, η a := by
              exact integral_add_right_eq_self
                (μ := (volume : Measure (Fin m → ℝ)))
                (f := fun a : Fin m → ℝ => η a) t
  calc
    ∫ a : Fin m → ℝ, localDescentParamTestRight φ ψ η ((z, t), a)
        = ∫ a : Fin m → ℝ, (φ z * ψ t) * η (t - a) := by
            apply integral_congr_ae
            filter_upwards with a
            rw [localDescentParamTestRight_apply]
            ring
    _ = (φ z * ψ t) * ∫ a : Fin m → ℝ, η (t - a) := by
            exact integral_const_mul (μ := (volume : Measure (Fin m → ℝ)))
              (φ z * ψ t) (fun a : Fin m → ℝ => η (t - a))
    _ = φ z * ψ t := by
            rw [htranslate, hη_norm]
            ring

/-- Fixed-last-variable evaluation of the left local descent test. -/
theorem schwartzPartialEval₂CLM_localDescentParamTestLeft {m : ℕ}
    (a : Fin m → ℝ)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ η : SchwartzMap (Fin m → ℝ) ℂ) :
    schwartzPartialEval₂CLM a (localDescentParamTestLeft φ ψ η) =
      schwartzTensorProduct₂
        (complexTranslateSchwartz (-a) φ)
        (SchwartzMap.smulLeftCLM ℂ (η : (Fin m → ℝ) → ℂ)
          (translateSchwartz a ψ)) := by
  ext p
  rcases p with ⟨z, t⟩
  have hreal : realEmbed (-a) = -realEmbed a := by
    ext i
    simp [realEmbed]
  rw [schwartzPartialEval₂CLM_apply]
  rw [localDescentParamTestLeft_apply]
  rw [schwartzTensorProduct₂_apply]
  rw [complexTranslateSchwartz_apply]
  rw [SchwartzMap.smulLeftCLM_apply_apply η.hasTemperateGrowth]
  simp [translateSchwartz_apply, hreal, sub_eq_add_neg, add_comm, mul_assoc]

/-- Translating the left parameter kernel by `-a` exposes the original
`ψ`-support factor. -/
theorem translateSchwartz_neg_smulLeft_eta_translate {m : ℕ}
    (a : Fin m → ℝ)
    (ψ η : SchwartzMap (Fin m → ℝ) ℂ) :
    translateSchwartz (-a)
      (SchwartzMap.smulLeftCLM ℂ (η : (Fin m → ℝ) → ℂ)
        (translateSchwartz a ψ)) =
      SchwartzMap.smulLeftCLM ℂ
        ((translateSchwartz (-a) η : SchwartzMap (Fin m → ℝ) ℂ) :
          (Fin m → ℝ) → ℂ)
        ψ := by
  ext x
  rw [translateSchwartz_apply]
  rw [SchwartzMap.smulLeftCLM_apply_apply η.hasTemperateGrowth]
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (translateSchwartz (-a) η).hasTemperateGrowth]
  simp [translateSchwartz_apply, add_assoc]

/-- Fixed-last-variable evaluation of the right local descent test. -/
theorem schwartzPartialEval₂CLM_localDescentParamTestRight {m : ℕ}
    (a : Fin m → ℝ)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ η : SchwartzMap (Fin m → ℝ) ℂ) :
    schwartzPartialEval₂CLM a (localDescentParamTestRight φ ψ η) =
      schwartzTensorProduct₂ φ
        (translateSchwartz (-a)
          (SchwartzMap.smulLeftCLM ℂ (η : (Fin m → ℝ) → ℂ)
            (translateSchwartz a ψ))) := by
  ext p
  rcases p with ⟨z, t⟩
  rw [schwartzPartialEval₂CLM_apply]
  rw [localDescentParamTestRight_apply]
  rw [schwartzTensorProduct₂_apply]
  rw [translateSchwartz_apply]
  rw [SchwartzMap.smulLeftCLM_apply_apply η.hasTemperateGrowth]
  simp [translateSchwartz_apply, sub_eq_add_neg, add_assoc, mul_assoc]

end SCV
