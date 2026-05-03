/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.VaryingKernelContinuity

/-!
# Support Transport for the Local Descent Package

This file contains the first small support lemmas for the local product-kernel
descent route.  They are separated from the larger varying-kernel continuity
file so the next covariance/pairing steps can grow in a small frontier module.
-/

noncomputable section

open Complex MeasureTheory

namespace SCV

variable {m : ℕ}

/-- Topological support transport for inverse complex-chart translation.

If the translated test `complexTranslateSchwartz a φ` is supported in a local
window, then every support point of `φ` shifts back into that same window.  This
is the exact support input used by the support-localized change-of-variables
step in local product-kernel covariance. -/
theorem tsupport_subset_preimage_tsupport_complexTranslateSchwartz
    (a : Fin m → ℝ)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
    tsupport (φ : ComplexChartSpace m → ℂ) ⊆
      (fun z : ComplexChartSpace m => z - realEmbed a) ⁻¹'
        tsupport
          (complexTranslateSchwartz a φ : ComplexChartSpace m → ℂ) := by
  intro z hz
  have hsub :
      tsupport
          ((complexTranslateSchwartz a φ : ComplexChartSpace m → ℂ) ∘
            fun z : ComplexChartSpace m => z - realEmbed a) ⊆
        (fun z : ComplexChartSpace m => z - realEmbed a) ⁻¹'
          tsupport
            (complexTranslateSchwartz a φ : ComplexChartSpace m → ℂ) := by
    exact tsupport_comp_subset_preimage
      (complexTranslateSchwartz a φ : ComplexChartSpace m → ℂ)
      (continuous_id.sub continuous_const)
  apply hsub
  have hfun :
      ((complexTranslateSchwartz a φ : ComplexChartSpace m → ℂ) ∘
          fun z : ComplexChartSpace m => z - realEmbed a) =
        (φ : ComplexChartSpace m → ℂ) := by
    funext z
    simp [complexTranslateSchwartz_apply, sub_eq_add_neg, add_assoc]
  simpa [hfun] using hz

/-- Support-localized change of variables for a translated complex-chart test.

The hypotheses are the local-continuity/support data supplied by the local
covariance proof.  The equality itself is the additive Haar translation
`y = z - realEmbed a`, with the sign convention fixed by
`complexTranslateSchwartz_apply`. -/
theorem integral_mul_complexTranslateSchwartz_eq_shift_of_support
    (G : ComplexChartSpace m → ℂ)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (a : Fin m → ℝ)
    (U : Set (ComplexChartSpace m))
    (_hG_cont : ContinuousOn G U)
    (_hφ_compact : HasCompactSupport (φ : ComplexChartSpace m → ℂ))
    (_hφ_shift :
      SupportsInOpen
        (complexTranslateSchwartz a φ : ComplexChartSpace m → ℂ) U)
    (_hshift_support :
      ∀ z ∈ tsupport (φ : ComplexChartSpace m → ℂ),
        z - realEmbed a ∈ U) :
    (∫ y : ComplexChartSpace m,
       G y * complexTranslateSchwartz a φ y) =
      ∫ z : ComplexChartSpace m, G (z - realEmbed a) * φ z := by
  rw [← MeasureTheory.integral_add_right_eq_self
    (μ := (volume : Measure (ComplexChartSpace m)))
    (f := fun y : ComplexChartSpace m =>
      G y * complexTranslateSchwartz a φ y)
    (-realEmbed a)]
  apply integral_congr_ae
  filter_upwards with z
  have harg : z + -realEmbed a + realEmbed a = z := by
    simp [add_assoc]
  simp [complexTranslateSchwartz_apply, sub_eq_add_neg, harg]

end SCV
