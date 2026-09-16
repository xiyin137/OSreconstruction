import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVMovingSliceChart
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVBlockGlobalTimeMeasure
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReducedTimeSpatialTensor

/-!
# OS-II Chapter V moving slices of reduced time/spatial tensors

Fiber reduction of a full ordered time/spatial tensor separates its common
basepoint into a one-dimensional time head integral and a spatial head-block
marginal. This file records the corresponding moving-slice scalar formula.

The result is deliberately source-independent. A later coordinate theorem can
insert the concrete reflected left/right approximate identities and combine
the reduced-time integral with the time head integral by Fubini.
-/

noncomputable section

open Complex MeasureTheory Topology Filter
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d]

/-- The part of a moving-slice integrand which remains after the full-time
Schwartz test has been separated off. -/
def osiiStageFixedSpatialCutoffIntegrand
    (A : OSIITimeContinuationStage d k)
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (z : OSIITimeGapSpace k)
    (τ : Fin k → ℝ) : ℂ :=
  ρ τ *
    A.distribution
      (z + osiiPositiveRealTimeEmbed τ) χ

/-- At a point of the moving-slice carrier, the fixed-spatial cutoff
integrand is continuous in all real reduced-time variables. -/
theorem continuous_osiiStageFixedSpatialCutoffIntegrand
    (A : OSIITimeContinuationStage d k)
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    {z : OSIITimeGapSpace k}
    (hz : z ∈ osiiStageMovingSliceCarrier A ρ) :
    Continuous
      (osiiStageFixedSpatialCutoffIntegrand A ρ χ z) := by
  rw [continuous_iff_continuousAt]
  intro τ
  by_cases hτ : τ ∈ tsupport (ρ : (Fin k → ℝ) → ℂ)
  · have hshift :
        z + osiiPositiveRealTimeEmbed τ ∈ A.carrier :=
      hz hτ
    have heval :
        ContinuousAt
          (fun p :
            OSIITimeGapSpace k ×
              SchwartzMap (Section43SpatialSpace d k) ℂ =>
            A.distribution p.1 p.2)
          (z + osiiPositiveRealTimeEmbed τ, χ) := by
      have hmem :
          (z + osiiPositiveRealTimeEmbed τ, χ) ∈
            A.carrier ×ˢ Set.univ :=
        ⟨hshift, Set.mem_univ χ⟩
      exact
        ((continuousOn_osiiWeaklyHolomorphicEvaluation A)
          _ hmem).continuousAt
          ((A.carrier_open.prod isOpen_univ).mem_nhds hmem)
    have hinner :
        ContinuousAt
          (fun σ : Fin k → ℝ =>
            (z + osiiPositiveRealTimeEmbed σ, χ))
          τ := by
      exact
        ((continuous_const.add
          continuous_osiiPositiveRealTimeEmbed).prodMk
            continuous_const).continuousAt
    have hpair :
        ContinuousAt
          (fun σ : Fin k → ℝ =>
            A.distribution
              (z + osiiPositiveRealTimeEmbed σ) χ)
          τ := by
      exact
        ContinuousAt.comp'
          (f := fun σ : Fin k → ℝ =>
            (z + osiiPositiveRealTimeEmbed σ, χ))
          (g := fun p :
            OSIITimeGapSpace k ×
              SchwartzMap (Section43SpatialSpace d k) ℂ =>
            A.distribution p.1 p.2)
          heval hinner
    exact ρ.continuous.continuousAt.mul hpair
  · have hnot :
        {σ : Fin k → ℝ |
          σ ∉ tsupport (ρ : (Fin k → ℝ) → ℂ)} ∈ 𝓝 τ :=
      (isClosed_tsupport (ρ : (Fin k → ℝ) → ℂ)
        ).isOpen_compl.mem_nhds hτ
    have hzero :
        osiiStageFixedSpatialCutoffIntegrand A ρ χ z
          =ᶠ[𝓝 τ] fun _ => 0 := by
      filter_upwards [hnot] with σ hσ
      have hρσ : ρ σ = 0 :=
        image_eq_zero_of_notMem_tsupport hσ
      simp [osiiStageFixedSpatialCutoffIntegrand, hρσ]
    exact (continuousAt_congr hzero).2 continuousAt_const

/-- The moving-slice scalar of a fiber-reduced ordered time/spatial tensor has
one fixed spatial marginal. All remaining integration is in the reduced time
variables, with the full time test replaced by its head-coordinate integral. -/
theorem osiiStageMovingSliceScalar_diffVarReduction_orderedPullback_timeSpatialTensor
    (A : OSIITimeContinuationStage d k)
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (φ : SchwartzMap (Fin (k + 1) → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (z : OSIITimeGapSpace k) :
    osiiStageMovingSliceScalar A ρ
        (diffVarReduction d k
          (section43OrderedPullbackTimeSpatialTensorCLM
            d (k + 1) χ φ))
        z =
      ∫ τ : Fin k → ℝ,
        ρ τ *
          (SCV.sliceIntegral φ τ *
            A.distribution
              (z + osiiPositiveRealTimeEmbed τ)
              (section43SpatialHeadMarginal χ)) := by
  rw [diffVarReduction_orderedPullback_timeSpatialTensor]
  simp only [osiiStageMovingSliceScalar,
    osiiShiftedMovingSpatialSliceIntegral,
    osiiMovingSpatialSliceIntegral,
    osiiShiftedStageDistribution,
    osiiFullSourceSpatialSlice_timeSpatialTensor,
    map_smul, smul_eq_mul]

/-- Expanded form of the preceding identity, exposing the missing full-time
head coordinate. This is the form used by the concrete two-block Fubini
change of variables. -/
theorem osiiStageMovingSliceScalar_diffVarReduction_orderedPullback_timeSpatialTensor_eq_iteratedIntegral
    (A : OSIITimeContinuationStage d k)
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (φ : SchwartzMap (Fin (k + 1) → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (z : OSIITimeGapSpace k) :
    osiiStageMovingSliceScalar A ρ
        (diffVarReduction d k
          (section43OrderedPullbackTimeSpatialTensorCLM
            d (k + 1) χ φ))
        z =
      ∫ τ : Fin k → ℝ,
        ρ τ *
          ((∫ a₀ : ℝ, φ (Fin.cons a₀ τ)) *
            A.distribution
              (z + osiiPositiveRealTimeEmbed τ)
              (section43SpatialHeadMarginal χ)) := by
  rw [
    osiiStageMovingSliceScalar_diffVarReduction_orderedPullback_timeSpatialTensor]
  rfl

/-- Combining the reduced-time moving integral with the missing full-time
head coordinate gives one integral over the complete global time tuple. -/
theorem
    osiiStageMovingSliceScalar_diffVarReduction_orderedPullback_timeSpatialTensor_eq_globalIntegral
    (A : OSIITimeContinuationStage d k)
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (φ : SchwartzMap (Fin (k + 1) → ℝ) ℂ)
    (hφ_compact :
      HasCompactSupport
        (φ : (Fin (k + 1) → ℝ) → ℂ))
    (χ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (z : OSIITimeGapSpace k)
    (hz : z ∈ osiiStageMovingSliceCarrier A ρ) :
    osiiStageMovingSliceScalar A ρ
        (diffVarReduction d k
          (section43OrderedPullbackTimeSpatialTensorCLM
            d (k + 1) χ φ))
        z =
      ∫ y : Fin (k + 1) → ℝ,
        φ y *
          osiiStageFixedSpatialCutoffIntegrand A ρ
            (section43SpatialHeadMarginal χ) z (Fin.tail y) := by
  let H : (Fin k → ℝ) → ℂ :=
    osiiStageFixedSpatialCutoffIntegrand A ρ
      (section43SpatialHeadMarginal χ) z
  let G : (Fin (k + 1) → ℝ) → ℂ :=
    fun y => φ y * H (Fin.tail y)
  have hH_cont : Continuous H := by
    exact
      continuous_osiiStageFixedSpatialCutoffIntegrand
        A ρ (section43SpatialHeadMarginal χ) hz
  have hG_cont : Continuous G := by
    exact φ.continuous.mul (hH_cont.comp (tailCLM k).continuous)
  have hG_compact : HasCompactSupport G := by
    exact hφ_compact.mul_right
  have hG_int : Integrable G :=
    hG_cont.integrable_of_hasCompactSupport hG_compact
  let e :=
    MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (k + 1) => ℝ) 0
  have hmp : MeasurePreserving e := by
    simpa [e] using
      (volume_preserving_piFinSuccAbove
        (fun _ : Fin (k + 1) => ℝ) 0)
  have hpair_int :
      @Integrable ℂ _ _ (ℝ × (Fin k → ℝ)) Prod.instMeasurableSpace
        (fun p : ℝ × (Fin k → ℝ) =>
          φ (Fin.cons p.1 p.2) * H p.2)
        ((volume : Measure ℝ).prod
          (volume : Measure (Fin k → ℝ))) := by
    simpa [G, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Function.comp_def, Fin.consEquiv,
      Measure.volume_eq_prod] using
      hmp.symm.integrable_comp_of_integrable hG_int
  rw [
    osiiStageMovingSliceScalar_diffVarReduction_orderedPullback_timeSpatialTensor_eq_iteratedIntegral]
  calc
    (∫ τ : Fin k → ℝ,
        ρ τ *
          ((∫ a₀ : ℝ, φ (Fin.cons a₀ τ)) *
            A.distribution
              (z + osiiPositiveRealTimeEmbed τ)
              (section43SpatialHeadMarginal χ))) =
      ∫ τ : Fin k → ℝ,
        ∫ a₀ : ℝ,
          φ (Fin.cons a₀ τ) * H τ := by
            apply integral_congr_ae
            filter_upwards with τ
            rw [show
              ρ τ *
                  ((∫ a₀ : ℝ, φ (Fin.cons a₀ τ)) *
                    A.distribution
                      (z + osiiPositiveRealTimeEmbed τ)
                      (section43SpatialHeadMarginal χ)) =
                (∫ a₀ : ℝ, φ (Fin.cons a₀ τ)) * H τ by
                  simp [H, osiiStageFixedSpatialCutoffIntegrand]
                  ring]
            exact
              (integral_mul_const
                (H τ)
                (fun a₀ : ℝ => φ (Fin.cons a₀ τ))).symm
    _ =
      @integral (ℝ × (Fin k → ℝ)) ℂ _ _ Prod.instMeasurableSpace
        ((volume : Measure ℝ).prod
          (volume : Measure (Fin k → ℝ)))
        (fun p => φ (Fin.cons p.1 p.2) * H p.2) := by
              simpa using
                (integral_prod_symm
                  (fun p : ℝ × (Fin k → ℝ) =>
                    φ (Fin.cons p.1 p.2) * H p.2)
                  hpair_int).symm
    _ = ∫ y : Fin (k + 1) → ℝ, G y := by
      simpa [G] using
        integral_finCons_eq k G
    _ = _ := rfl

end OSIIChapterV
end OSReconstruction
