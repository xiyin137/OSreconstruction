/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIITimeSpatialCurrying













noncomputable section

open Complex Topology Filter MeasureTheory
open scoped Classical

namespace OSReconstruction

variable {d k : ℕ} [NeZero d]

/-- A continuation stage shifted by a complex time parameter and then
restricted along the real time-gap directions. -/
def osiiShiftedStageDistribution
    (A : OSIITimeContinuationStage d k)
    (z : OSIITimeGapSpace k)
    (τ : Fin k → ℝ) :
    OSIISpatialDistribution d k :=
  A.distribution (z + osiiPositiveRealTimeEmbed τ)

/-- The natural parameter carrier for a cutoff convolution: every real shift
in the cutoff support must remain inside the continuation stage. -/
def osiiShiftedConvolutionCarrier
    (A : OSIITimeContinuationStage d k)
    (ρ : SchwartzMap (Fin k → ℝ) ℂ) :
    Set (OSIITimeGapSpace k) :=
  {z | Set.MapsTo
    (fun τ => z + osiiPositiveRealTimeEmbed τ)
    (tsupport (ρ : (Fin k → ℝ) → ℂ))
    A.carrier}

/-- Scalar convolution of a shifted continuation stage against the moving
spatial slices of a full difference-coordinate Schwartz source. -/
def osiiShiftedMovingSpatialSliceIntegral
    (A : OSIITimeContinuationStage d k)
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (F : SchwartzNPoint d k)
    (z : OSIITimeGapSpace k) : ℂ :=
  osiiMovingSpatialSliceIntegral ρ (osiiShiftedStageDistribution A z) F

omit [NeZero d] in
theorem continuous_osiiPositiveRealTimeEmbed :
    Continuous
      (osiiPositiveRealTimeEmbed :
        (Fin k → ℝ) → OSIITimeGapSpace k) := by
  apply continuous_pi
  intro i
  exact Complex.continuous_ofReal.comp (continuous_apply i)

omit [NeZero d] in
theorem continuous_shift_osiiPositiveRealTimeEmbed
    (z : OSIITimeGapSpace k) :
    Continuous (fun τ : Fin k → ℝ =>
      z + osiiPositiveRealTimeEmbed τ) :=
  continuous_const.add continuous_osiiPositiveRealTimeEmbed

omit [NeZero d] in
/-- The shifted stage pairings are continuous along the real cutoff orbit. -/
theorem continuousOn_osiiShiftedStageDistribution_pairing
    (A : OSIITimeContinuationStage d k)
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (z : osiiShiftedConvolutionCarrier A ρ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    ContinuousOn
      (fun τ => osiiShiftedStageDistribution A z.1 τ χ)
      (tsupport (ρ : (Fin k → ℝ) → ℂ)) := by
  exact
    (A.weaklyHolomorphic χ).continuousOn.comp
      (continuous_shift_osiiPositiveRealTimeEmbed z.1).continuousOn
      z.2

omit [NeZero d] in
/-- The compact real orbit of an admissible shifted parameter. -/
def osiiShiftedConvolutionOrbit
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (z : OSIITimeGapSpace k) :
    Set (OSIITimeGapSpace k) :=
  (fun τ => z + osiiPositiveRealTimeEmbed τ) ''
    tsupport (ρ : (Fin k → ℝ) → ℂ)

omit [NeZero d] in
theorem isCompact_osiiShiftedConvolutionOrbit
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (hρ_compact : HasCompactSupport (ρ : (Fin k → ℝ) → ℂ))
    (z : OSIITimeGapSpace k) :
    IsCompact (osiiShiftedConvolutionOrbit ρ z) := by
  have hsupport :
      IsCompact (tsupport (ρ : (Fin k → ℝ) → ℂ)) := by
    simpa [HasCompactSupport] using hρ_compact
  exact hsupport.image
    (continuous_shift_osiiPositiveRealTimeEmbed z)

omit [NeZero d] in
theorem osiiShiftedConvolutionOrbit_subset_carrier
    (A : OSIITimeContinuationStage d k)
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (z : osiiShiftedConvolutionCarrier A ρ) :
    osiiShiftedConvolutionOrbit ρ z.1 ⊆ A.carrier := by
  rintro ζ ⟨τ, hτ, rfl⟩
  exact z.2 hτ

omit [NeZero d] in
/-- The shifted moving-slice scalar is integrable throughout its natural
compact-cutoff carrier. -/
theorem integrable_osiiShiftedMovingSpatialSlicePairing
    (A : OSIITimeContinuationStage d k)
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (hρ_compact : HasCompactSupport (ρ : (Fin k → ℝ) → ℂ))
    (F : SchwartzNPoint d k)
    (z : osiiShiftedConvolutionCarrier A ρ) :
    Integrable (fun τ : Fin k → ℝ =>
      ρ τ *
        osiiShiftedStageDistribution A z.1 τ
          (osiiFullSourceSpatialSlice F τ)) := by
  let U := tsupport (ρ : (Fin k → ℝ) → ℂ)
  let K := osiiShiftedConvolutionOrbit ρ z.1
  obtain ⟨s, C, hC, hbound⟩ :=
    exists_uniform_schwartz_bound_osiiStage_on_compact
      A K
        (isCompact_osiiShiftedConvolutionOrbit ρ hρ_compact z.1)
        (osiiShiftedConvolutionOrbit_subset_carrier A ρ z)
  have hbounded :
      OSIITimeSpatialPointwiseBoundedOn
        (osiiShiftedStageDistribution A z.1) U := by
    intro χ
    refine ⟨C * s.sup
      (schwartzSeminormFamily ℂ
        (Section43SpatialSpace d k) ℂ) χ, ?_⟩
    intro τ hτ
    exact hbound
      (z.1 + osiiPositiveRealTimeEmbed τ)
      ⟨τ, hτ, rfl⟩ χ
  exact
    integrable_osiiMovingSpatialSlicePairing
      ρ (osiiShiftedStageDistribution A z.1) U
      hρ_compact (fun _ h => h)
      (continuousOn_osiiShiftedStageDistribution_pairing A ρ z)
      hbounded F

omit [NeZero d] in
@[simp] theorem osiiShiftedMovingSpatialSliceIntegral_zero
    (A : OSIITimeContinuationStage d k)
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (F : SchwartzNPoint d k) :
    osiiShiftedMovingSpatialSliceIntegral A ρ F 0 =
      osiiMovingSpatialSliceIntegral ρ
        (fun τ => A.distribution (osiiPositiveRealTimeEmbed τ)) F := by
  apply integral_congr_ae
  filter_upwards [] with τ
  simp [osiiShiftedStageDistribution]

end OSReconstruction
