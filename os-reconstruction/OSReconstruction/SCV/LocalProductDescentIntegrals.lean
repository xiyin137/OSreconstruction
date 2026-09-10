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

/-- Local product-kernel covariance is enough to identify a sheared product
test with the normalized fiber quotient, provided all translated product tests
stay inside the declared local support window. -/
theorem shearedProductKernelFunctional_localQuotient_of_productCovariant {m : ℕ}
    {r rη : ℝ}
    (K : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ)
    (Udesc Ucov : Set (ComplexChartSpace m))
    (hr_nonneg : 0 ≤ r) (hrη_nonneg : 0 ≤ rη)
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη_norm : ∫ t : Fin m → ℝ, η t = 1)
    (hη_support : KernelSupportWithin η rη)
    (hmargin :
      ∀ z ∈ Udesc, ∀ t : Fin m → ℝ, ‖t‖ ≤ r + rη →
        z + realEmbed t ∈ Ucov)
    (hcov : ProductKernelRealTranslationCovariantLocal K Ucov (r + rη))
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (hφ : SupportsInOpen (φ : ComplexChartSpace m → ℂ) Udesc)
    (hψ : KernelSupportWithin ψ r) :
    K (schwartzTensorProduct₂ φ ψ) =
      complexRealFiberTranslationDescentCLM
        (shearedProductKernelFunctional K) η
        (realConvolutionTest φ ψ) := by
  let A := localDescentParamTestLeft φ ψ η
  let B := localDescentParamTestRight φ ψ η
  have hpoint : ∀ a : Fin m → ℝ,
      K (schwartzPartialEval₂CLM a A) =
        K (schwartzPartialEval₂CLM a B) := by
    intro a
    let κ : SchwartzMap (Fin m → ℝ) ℂ :=
      SchwartzMap.smulLeftCLM ℂ (η : (Fin m → ℝ) → ℂ) (translateSchwartz a ψ)
    have hAeval : schwartzPartialEval₂CLM a A =
        schwartzTensorProduct₂ (complexTranslateSchwartz (-a) φ) κ := by
      simpa [A, κ] using
        schwartzPartialEval₂CLM_localDescentParamTestLeft a φ ψ η
    have hBeval : schwartzPartialEval₂CLM a B =
        schwartzTensorProduct₂ φ (translateSchwartz (-a) κ) := by
      simpa [B, κ] using
        schwartzPartialEval₂CLM_localDescentParamTestRight a φ ψ η
    rw [hAeval, hBeval]
    by_cases hκ_zero : κ = 0
    · have hleft :
          schwartzTensorProduct₂ (complexTranslateSchwartz (-a) φ) κ = 0 := by
        ext p
        rcases p with ⟨z, t⟩
        simp [hκ_zero]
      have hright :
          schwartzTensorProduct₂ φ (translateSchwartz (-a) κ) = 0 := by
        ext p
        rcases p with ⟨z, t⟩
        simp [hκ_zero]
      simp [hleft, hright]
    · have hκ_ne : κ ≠ 0 := hκ_zero
      have hbound : ‖a‖ ≤ r + rη := by
        obtain ⟨t, ht_ne⟩ : ∃ t : Fin m → ℝ, κ t ≠ 0 := by
          by_contra hnone
          apply hκ_ne
          ext t
          have ht_not : ¬ κ t ≠ 0 := by
            intro ht
            exact hnone ⟨t, ht⟩
          exact not_not.mp ht_not
        have ht_support : t ∈ Function.support (κ : (Fin m → ℝ) → ℂ) := ht_ne
        have ht_tsupport : t ∈ tsupport (κ : (Fin m → ℝ) → ℂ) :=
          (subset_tsupport (κ : (Fin m → ℝ) → ℂ)) ht_support
        have hpair := SchwartzMap.tsupport_smulLeftCLM_subset
          (𝕜 := ℂ) (F := ℂ) (g := (η : (Fin m → ℝ) → ℂ))
          (f := translateSchwartz a ψ) ht_tsupport
        have ht_translate :
            t ∈ tsupport
              ((translateSchwartz a ψ : SchwartzMap (Fin m → ℝ) ℂ) :
                (Fin m → ℝ) → ℂ) := hpair.1
        have ht_eta : t ∈ tsupport (η : (Fin m → ℝ) → ℂ) := hpair.2
        have hsub :
            tsupport ((ψ : (Fin m → ℝ) → ℂ) ∘ fun x : Fin m → ℝ => x + a) ⊆
              (fun x : Fin m → ℝ => x + a) ⁻¹'
                tsupport (ψ : (Fin m → ℝ) → ℂ) := by
          exact tsupport_comp_subset_preimage (ψ : (Fin m → ℝ) → ℂ)
            (continuous_id.add continuous_const)
        have ht_translate' :
            t ∈ tsupport
              ((ψ : (Fin m → ℝ) → ℂ) ∘ fun x : Fin m → ℝ => x + a) := by
          simpa [translateSchwartz_apply] using ht_translate
        have hta_ψ : t + a ∈ tsupport (ψ : (Fin m → ℝ) → ℂ) :=
          hsub ht_translate'
        have htη_ball := hη_support ht_eta
        have htaψ_ball := hψ hta_ψ
        rw [Metric.mem_closedBall, dist_zero_right] at htη_ball htaψ_ball
        have haeq : ‖a‖ = ‖(t + a) - t‖ := by
          congr 1
          ext i
          simp
        calc
          ‖a‖ = ‖(t + a) - t‖ := haeq
          _ ≤ ‖t + a‖ + ‖t‖ := norm_sub_le _ _
          _ ≤ r + rη := by linarith
      have hφ_cov : SupportsInOpen (φ : ComplexChartSpace m → ℂ) Ucov := by
        constructor
        · exact hφ.1
        · intro z hz
          have hz_cov :=
            hmargin z (hφ.2 hz) 0 (by simpa using add_nonneg hr_nonneg hrη_nonneg)
          have hz_eq : z + realEmbed (0 : Fin m → ℝ) = z := by
            ext i
            simp [realEmbed]
          exact hz_eq ▸ hz_cov
      have hφ_shift :
          SupportsInOpen
            (complexTranslateSchwartz (-a) φ : ComplexChartSpace m → ℂ) Ucov := by
        apply SupportsInOpen.complexTranslateSchwartz_of_image_subset
          φ Udesc Ucov (-a) hφ
        intro y hy
        have hycov := hmargin (y + realEmbed (-a)) hy a hbound
        have hcancel : y + realEmbed (-a) + realEmbed a = y := by
          ext i
          simp [realEmbed, add_assoc]
        exact hcancel ▸ hycov
      have hκ_support : KernelSupportWithin κ (r + rη) := by
        have hκ_rη : KernelSupportWithin κ rη := by
          exact KernelSupportWithin.smulLeftCLM_of_leftSupport hη_support
            (translateSchwartz a ψ)
        exact KernelSupportWithin.mono hκ_rη (by linarith)
      have hκ_shift : KernelSupportWithin (translateSchwartz (-a) κ) (r + rη) := by
        have hrew : translateSchwartz (-a) κ =
            SchwartzMap.smulLeftCLM ℂ
              ((translateSchwartz (-a) η : SchwartzMap (Fin m → ℝ) ℂ) :
                (Fin m → ℝ) → ℂ) ψ := by
          simpa [κ] using translateSchwartz_neg_smulLeft_eta_translate a ψ η
        have hκ_r :
            KernelSupportWithin
              (SchwartzMap.smulLeftCLM ℂ
                ((translateSchwartz (-a) η : SchwartzMap (Fin m → ℝ) ℂ) :
                  (Fin m → ℝ) → ℂ) ψ) r := by
          exact KernelSupportWithin.smulLeftCLM
            ((translateSchwartz (-a) η : SchwartzMap (Fin m → ℝ) ℂ) :
              (Fin m → ℝ) → ℂ) hψ
        simpa [hrew] using KernelSupportWithin.mono hκ_r (by linarith)
      exact hcov (-a) φ κ hφ_cov hφ_shift hκ_support hκ_shift
  have hint :
      (∫ a : Fin m → ℝ, K (schwartzPartialEval₂CLM a A)) =
        ∫ a : Fin m → ℝ, K (schwartzPartialEval₂CLM a B) := by
    apply integral_congr_ae
    filter_upwards with a
    exact hpoint a
  calc
    K (schwartzTensorProduct₂ φ ψ)
        = K (mixedRealFiberIntegralCLM B) := by
            rw [mixedRealFiberIntegralCLM_localDescentParamTestRight φ ψ η hη_norm]
    _ = ∫ a : Fin m → ℝ, K (schwartzPartialEval₂CLM a B) := by
            exact continuousLinearMap_apply_mixedRealFiberIntegralCLM_eq_integral K B
    _ = ∫ a : Fin m → ℝ, K (schwartzPartialEval₂CLM a A) := by
            rw [hint]
    _ = K (mixedRealFiberIntegralCLM A) := by
            exact (continuousLinearMap_apply_mixedRealFiberIntegralCLM_eq_integral K A).symm
    _ = K ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (realConvolutionShearCLE m).symm)
              (schwartzTensorProduct₂ (realConvolutionTest φ ψ) η)) := by
            rw [mixedRealFiberIntegralCLM_localDescentParamTestLeft]
    _ = complexRealFiberTranslationDescentCLM
          (shearedProductKernelFunctional K) η
          (realConvolutionTest φ ψ) := by
            simp [complexRealFiberTranslationDescentCLM, shearedProductKernelFunctional,
              schwartzTensorProduct₂CLMRight_eq, ContinuousLinearMap.comp_apply]

/-- Local product-test descent for translation-covariant product kernels.  This
is deliberately only a product-test statement under the declared support
window, not a quotient theorem for arbitrary mixed Schwartz tests. -/
theorem translationCovariantProductKernel_descends_local {m : ℕ}
    (K : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ)
    (Udesc Ucov : Set (ComplexChartSpace m)) (r rη : ℝ)
    (hr_nonneg : 0 ≤ r) (hrη_nonneg : 0 ≤ rη)
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη_norm : ∫ t : Fin m → ℝ, η t = 1)
    (hη_support : KernelSupportWithin η rη)
    (hmargin :
      ∀ z ∈ Udesc, ∀ t : Fin m → ℝ, ‖t‖ ≤ r + rη →
        z + realEmbed t ∈ Ucov)
    (hcov : ProductKernelRealTranslationCovariantLocal K Ucov (r + rη)) :
    ∃ Hdist : SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ] ℂ,
      ∀ (φ : SchwartzMap (ComplexChartSpace m) ℂ)
        (ψ : SchwartzMap (Fin m → ℝ) ℂ),
        SupportsInOpen (φ : ComplexChartSpace m → ℂ) Udesc →
        KernelSupportWithin ψ r →
          K (schwartzTensorProduct₂ φ ψ) =
            Hdist (realConvolutionTest φ ψ) := by
  refine ⟨complexRealFiberTranslationDescentCLM
    (shearedProductKernelFunctional K) η, ?_⟩
  intro φ ψ hφ hψ
  exact shearedProductKernelFunctional_localQuotient_of_productCovariant
    K Udesc Ucov hr_nonneg hrη_nonneg η hη_norm hη_support hmargin hcov
    φ ψ hφ hψ

end SCV
