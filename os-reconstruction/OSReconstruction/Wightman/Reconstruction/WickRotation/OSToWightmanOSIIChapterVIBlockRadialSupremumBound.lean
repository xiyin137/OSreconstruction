/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPartialConvolutionSupport
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialLocalMeanValue
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIPartialConvolutionIntegrability











noncomputable section

open Complex MeasureTheory Metric Set
open scoped Classical

namespace OSReconstruction

theorem osiiStep4PartialConvolutionTransform_support_subset_closedImaginaryBox
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (F : (Fin (k * q) → ℂ) → ℂ)
    (c : Fin (k * q) → ℂ) :
    Function.support
        (fun p : (Fin (k * q) → ℝ) × (Fin (k * q) → ℝ) =>
          osiiStep4PartialConvolutionTransform
            (osiiStep4FullBlockRadialG q k rho) F c p.1 p.2) ⊆
      osiiStep4PartialConvolutionClosedImaginaryBox q k rho := by
  intro p hp
  constructor
  · rw [Metric.mem_closedBall, dist_zero_right,
      pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ rho / 4)]
    intro a
    obtain ⟨⟨i, mu⟩, rfl⟩ := finProdFinEquiv.surjective a
    simpa only [Real.norm_eq_abs] using
      (osiiStep4PartialConvolutionTransform_support_imaginary_coord_lt
        q k hrho F c hp i mu).le
  · rw [Metric.mem_closedBall, dist_zero_right,
      pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ rho / 8)]
    intro a
    obtain ⟨⟨i, mu⟩, rfl⟩ := finProdFinEquiv.surjective a
    have hsupp := osiiStep4PartialConvolutionTransform_support_subset
      q k hrho F c hp i mu
    simpa only [Real.norm_eq_abs] using hsupp.1.le

theorem osiiStep4PartialConvolutionTransform_eq_zero_of_not_mem_first_closedBall
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (F : (Fin (k * q) → ℂ) → ℂ)
    (c : Fin (k * q) → ℂ)
    (y y' : Fin (k * q) → ℝ)
    (hy : y ∉ Metric.closedBall 0 (rho / 4)) :
    osiiStep4PartialConvolutionTransform
        (osiiStep4FullBlockRadialG q k rho) F c y y' = 0 := by
  exact eq_zero_of_support_subset_prod_left
    (fun p => osiiStep4PartialConvolutionTransform
      (osiiStep4FullBlockRadialG q k rho) F c p.1 p.2)
    (Metric.closedBall 0 (rho / 4))
    (Metric.closedBall 0 (rho / 8))
    (osiiStep4PartialConvolutionTransform_support_subset_closedImaginaryBox
      q k hrho F c) y y' hy

theorem osiiStep4PartialConvolutionClosedImaginaryBox_volumeReal
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    (volume : Measure
      ((Fin (k * q) → ℝ) × (Fin (k * q) → ℝ))).real
        (osiiStep4PartialConvolutionClosedImaginaryBox q k rho) =
      (rho / 2) ^ (k * q) * (rho / 4) ^ (k * q) := by
  rw [measureReal_def]
  change ENNReal.toReal
      (((volume : Measure (Fin (k * q) → ℝ)).prod
        (volume : Measure (Fin (k * q) → ℝ)))
          (Metric.closedBall 0 (rho / 4) ×ˢ
            Metric.closedBall 0 (rho / 8))) = _
  rw [Measure.prod_prod, Real.volume_pi_closedBall,
    Real.volume_pi_closedBall]
  · rw [ENNReal.toReal_mul]
    rw [ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity)]
    simp only [Fintype.card_fin]
    ring
  · positivity
  · positivity

/-- The measure-theoretic `(6.6) -> (6.7)` step, separated from the analytic
proof of the supplied partial-convolution mean-value identity. -/
theorem
    osiiStep4FullBlockRadialG_norm_le_supportVolume_mul_sup_of_meanValue
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (F : (Fin (k * q) → ℂ) → ℂ) (c : Fin (k * q) → ℂ)
    (hF_cont : Continuous F)
    (hmean :
      F c =
        ∫ y' : Fin (k * q) → ℝ, ∫ y : Fin (k * q) → ℝ,
          osiiStep4PartialConvolutionTransform
            (osiiStep4FullBlockRadialG q k rho) F c y y')
    (B : ℝ)
    (hbound :
      ∀ p ∈ osiiStep4PartialConvolutionClosedImaginaryBox q k rho,
        ‖osiiStep4PartialConvolutionTransform
          (osiiStep4FullBlockRadialG q k rho) F c p.1 p.2‖ ≤ B) :
    ‖F c‖ ≤
      B * ((rho / 2) ^ (k * q) * (rho / 4) ^ (k * q)) := by
  let T : ((Fin (k * q) → ℝ) × (Fin (k * q) → ℝ)) → ℂ := fun p =>
    osiiStep4PartialConvolutionTransform
      (osiiStep4FullBlockRadialG q k rho) F c p.1 p.2
  have hweighted :=
    osiiStep4FullBlockRadialG_partialKernel_weighted_integrable
      q k hrho F c hF_cont
  have hTswap := osiiStep4PartialConvolutionTransform_integrable
    (osiiStep4FullBlockRadialG q k rho) F c hweighted
  have hTint : Integrable T
      ((volume : Measure (Fin (k * q) → ℝ)).prod
        (volume : Measure (Fin (k * q) → ℝ))) := by
    simpa [T, Function.comp_def] using hTswap.swap
  have hrecover : F c =
      ∫ p : (Fin (k * q) → ℝ) × (Fin (k * q) → ℝ), T p := by
    exact hmean.trans (integral_prod_symm T hTint).symm
  let K := osiiStep4PartialConvolutionClosedImaginaryBox q k rho
  have hsupport : Function.support T ⊆ K := by
    simpa [T, K] using
      osiiStep4PartialConvolutionTransform_support_subset_closedImaginaryBox
        q k hrho F c
  have hzero : ∀ p, p ∉ K → T p = 0 := by
    intro p hp
    by_contra hne
    exact hp (hsupport (Function.mem_support.mpr hne))
  have hset :
      (∫ p in K, T p
        ∂((volume : Measure (Fin (k * q) → ℝ)).prod
          (volume : Measure (Fin (k * q) → ℝ)))) =
        ∫ p, T p :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  calc
    ‖F c‖ = ‖∫ p, T p‖ := congrArg norm hrecover
    _ = ‖∫ p in K, T p‖ := congrArg norm hset.symm
    _ ≤ B *
        ((volume : Measure
          ((Fin (k * q) → ℝ) × (Fin (k * q) → ℝ))).real K) := by
      apply norm_setIntegral_le_of_norm_le_const_ae'
        (osiiStep4PartialConvolutionClosedImaginaryBox_isCompact
          q k rho).measure_lt_top
      filter_upwards with p
      intro hp
      exact hbound p hp
    _ = B * ((rho / 2) ^ (k * q) * (rho / 4) ^ (k * q)) := by
      rw [osiiStep4PartialConvolutionClosedImaginaryBox_volumeReal q k hrho]

/-- Local OS-II `(6.7)`: holomorphy is needed only on the translated
three-radius support.  The Tietze extension used for local `(6.6)` also
supplies the measurability and integrability required by the support-volume
estimate. -/
theorem
    osiiStep4FullBlockRadialG_norm_le_supportVolume_mul_sup_local
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (F : (Fin (k * q) → ℂ) → ℂ) (c : Fin (k * q) → ℂ)
    (U : Set (Fin (k * q) → ℂ))
    (hF : DifferentiableOn ℂ F U)
    (hsupport : ∀ z ∈ osiiStep4FullBlockRadialClosedSupport q k (3 * rho),
      c + z ∈ U)
    (B : ℝ)
    (hbound :
      ∀ p ∈ osiiStep4PartialConvolutionClosedImaginaryBox q k rho,
        ‖osiiStep4PartialConvolutionTransform
          (osiiStep4FullBlockRadialG q k rho) F c p.1 p.2‖ ≤ B) :
    ‖F c‖ ≤
      B * ((rho / 2) ^ (k * q) * (rho / 4) ^ (k * q)) := by
  obtain ⟨G, hG_cont, hGc, hmean, htransform⟩ :=
    exists_osiiStep4FullBlockRadialG_local_continuous_extension
      q k hrho F c U hF hsupport
  rw [← hGc]
  apply
    osiiStep4FullBlockRadialG_norm_le_supportVolume_mul_sup_of_meanValue
      q k hrho G c hG_cont hmean B
  intro p hp
  rw [htransform]
  exact hbound p hp

end OSReconstruction
