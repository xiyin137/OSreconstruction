import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVMovingSliceChart
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIConfigurationTranslation

/-!
# OS-II Chapter V Moving-Slice Real Edge

This file separates the real change-of-variables argument from the analytic
construction of the moving-slice chart. A real shift of the continuation
parameter is moved onto the compact time cutoff and the full
difference-coordinate source with the opposite sign. The zero-shift
representation theorem then gives the corresponding Euclidean real edge.
-/

noncomputable section

open Complex Topology Filter MeasureTheory
open scoped Classical

namespace OSReconstruction

variable {d k : ℕ} [NeZero d]

/-- A pure translation in the time coordinates of the Section 4.3
time/spatial splitting. -/
def osiiDifferenceTimeTranslation
    (s : Fin k → ℝ) :
    NPointDomain d k :=
  (nPointTimeSpatialCLE (d := d) k).symm (s, 0)

omit [NeZero d] in
@[simp] theorem nPointTimeSpatialCLE_osiiDifferenceTimeTranslation
    (s : Fin k → ℝ) :
    nPointTimeSpatialCLE (d := d) k
        (osiiDifferenceTimeTranslation (d := d) s) =
      (s, 0) := by
  exact (nPointTimeSpatialCLE (d := d) k).apply_symm_apply (s, 0)

@[simp] theorem osiiPositiveRealTimeEmbed_add
    (s τ : Fin k → ℝ) :
    osiiPositiveRealTimeEmbed (s + τ) =
      osiiPositiveRealTimeEmbed s + osiiPositiveRealTimeEmbed τ := by
  funext i
  simp [osiiPositiveRealTimeEmbed]

namespace OSIIChapterV

theorem section43QTime_add_osiiDifferenceTimeTranslation
    (s : Fin k → ℝ)
    (x : NPointDomain d k) :
    section43QTime (d := d) (n := k)
        (x + osiiDifferenceTimeTranslation (d := d) s) =
      section43QTime (d := d) (n := k) x + s := by
  change
    (nPointTimeSpatialCLE (d := d) k
      (x + osiiDifferenceTimeTranslation (d := d) s)).1 =
      (nPointTimeSpatialCLE (d := d) k x).1 + s
  rw [map_add, nPointTimeSpatialCLE_osiiDifferenceTimeTranslation]
  rfl

end OSIIChapterV

/-- Translating a full difference-coordinate source purely in time translates
its moving spatial slice by the same time vector. -/
theorem osiiFullSourceSpatialSlice_translate_differenceTime
    (F : SchwartzNPoint d k)
    (s τ : Fin k → ℝ) :
    osiiFullSourceSpatialSlice
        (translateSchwartzConfiguration
          (osiiDifferenceTimeTranslation (d := d) s) F) τ =
      osiiFullSourceSpatialSlice F (τ + s) := by
  ext η
  simp only [osiiFullSourceSpatialSlice_apply,
    translateSchwartzConfiguration_apply]
  congr 1
  apply (nPointTimeSpatialCLE (d := d) k).injective
  simp [map_add]

/-- A real shift of the moving-slice scalar is the zero-shift scalar with the
time cutoff and full difference-coordinate source translated by the opposite
time vector. -/
theorem osiiStageMovingSliceScalar_positiveRealTimeEmbed_eq_zero_translated
    (A : OSIITimeContinuationStage d k)
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (F : SchwartzNPoint d k)
    (s : Fin k → ℝ) :
    osiiStageMovingSliceScalar A ρ F
        (osiiPositiveRealTimeEmbed s) =
      osiiStageMovingSliceScalar A
        (SCV.translateSchwartz (-s) ρ)
        (translateSchwartzConfiguration
          (osiiDifferenceTimeTranslation (d := d) (-s)) F)
        0 := by
  let H : (Fin k → ℝ) → ℂ := fun σ =>
    ρ (σ - s) *
      A.distribution (osiiPositiveRealTimeEmbed σ)
        (osiiFullSourceSpatialSlice F (σ - s))
  have hshift :
      (fun τ : Fin k → ℝ =>
        ρ τ *
          A.distribution
            (osiiPositiveRealTimeEmbed s +
              osiiPositiveRealTimeEmbed τ)
            (osiiFullSourceSpatialSlice F τ)) =
        fun τ => H (τ + s) := by
    funext τ
    simp only [H]
    have hsub : τ + s - s = τ := by
      abel
    have hadd :
        osiiPositiveRealTimeEmbed (τ + s) =
          osiiPositiveRealTimeEmbed s +
            osiiPositiveRealTimeEmbed τ := by
      rw [osiiPositiveRealTimeEmbed_add]
      exact add_comm _ _
    rw [hsub, hadd]
  have hzero :
      (fun σ : Fin k → ℝ =>
        (SCV.translateSchwartz (-s) ρ) σ *
          A.distribution (osiiPositiveRealTimeEmbed σ)
            (osiiFullSourceSpatialSlice
              (translateSchwartzConfiguration
                (osiiDifferenceTimeTranslation (d := d) (-s)) F)
              σ)) =
        H := by
    funext σ
    simp only [SCV.translateSchwartz_apply,
      osiiFullSourceSpatialSlice_translate_differenceTime, H]
    congr 2
  simp only [osiiStageMovingSliceScalar,
    osiiShiftedMovingSpatialSliceIntegral,
    osiiMovingSpatialSliceIntegral,
    osiiShiftedStageDistribution]
  rw [hshift, MeasureTheory.integral_add_right_eq_self H s]
  calc
    (∫ σ : Fin k → ℝ, H σ) =
        ∫ σ : Fin k → ℝ,
          (SCV.translateSchwartz (-s) ρ) σ *
            A.distribution (osiiPositiveRealTimeEmbed σ)
              (osiiFullSourceSpatialSlice
                (translateSchwartzConfiguration
                  (osiiDifferenceTimeTranslation (d := d) (-s)) F)
                σ) := by
          exact congrArg (fun G : (Fin k → ℝ) → ℂ => ∫ σ, G σ) hzero.symm
    _ = _ := by simp

/-- Before any spacetime distribution is introduced, a positive-real shift of
the moving-slice chart is exactly the translated convolution of the stage's
own positive-real-time spatial orbit. -/
theorem
    osiiStageMovingSliceScalar_positiveRealTimeEmbed_eq_movingSpatialSliceIntegral
    (A : OSIITimeContinuationStage d k)
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (F : SchwartzNPoint d k)
    (s : Fin k → ℝ) :
    osiiStageMovingSliceScalar A ρ F
        (osiiPositiveRealTimeEmbed s) =
      osiiMovingSpatialSliceIntegral
        (SCV.translateSchwartz (-s) ρ)
        (fun τ => A.distribution (osiiPositiveRealTimeEmbed τ))
        (translateSchwartzConfiguration
          (osiiDifferenceTimeTranslation (d := d) (-s)) F) := by
  rw [osiiStageMovingSliceScalar_positiveRealTimeEmbed_eq_zero_translated]
  exact
    osiiStageMovingSliceScalar_zero
      A (SCV.translateSchwartz (-s) ρ)
        (translateSchwartzConfiguration
          (osiiDifferenceTimeTranslation (d := d) (-s)) F)

/-- Compact support is preserved by translating a finite-time Schwartz
cutoff. -/
theorem hasCompactSupport_translateSchwartz
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (hρ_compact : HasCompactSupport (ρ : (Fin k → ℝ) → ℂ))
    (s : Fin k → ℝ) :
    HasCompactSupport
      ((SCV.translateSchwartz s ρ :
        SchwartzMap (Fin k → ℝ) ℂ) : (Fin k → ℝ) → ℂ) := by
  change HasCompactSupport (fun τ : Fin k → ℝ => ρ (τ + s))
  simpa [Function.comp_def] using
    hρ_compact.comp_homeomorph (Homeomorph.addRight s)

/-- On every real shift for which the translated cutoff remains in the
represented time region, the moving-slice chart is the Euclidean
ordered-pullback functional of the oppositely translated cutoff and source. -/
theorem osiiStageMovingSliceScalar_positiveRealTimeEmbed_eq_orderedPullbackFullCutoff
    (A : OSIITimeContinuationStage d k)
    (W : SchwartzNPoint d k →L[ℂ] ℂ)
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (U : Set (Fin k → ℝ))
    (hρ_compact : HasCompactSupport (ρ : (Fin k → ℝ) → ℂ))
    (hscalar :
      ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
        ContinuousOn
          (fun τ => A.distribution
            (osiiPositiveRealTimeEmbed τ) χ) U)
    (hbounded :
      OSIITimeSpatialPointwiseBoundedOn
        (fun τ => A.distribution (osiiPositiveRealTimeEmbed τ)) U)
    (hrep :
      OSIITimeSpatialRepresentsDistributionOn W
        (fun τ => A.distribution (osiiPositiveRealTimeEmbed τ)) U)
    (F : SchwartzNPoint d k)
    (s : Fin k → ℝ)
    (hρ_shift_support :
      tsupport
          ((SCV.translateSchwartz (-s) ρ :
            SchwartzMap (Fin k → ℝ) ℂ) : (Fin k → ℝ) → ℂ) ⊆ U) :
    osiiStageMovingSliceScalar A ρ F
        (osiiPositiveRealTimeEmbed s) =
      W (section43OrderedPullbackFullCutoffCLM d k
        (SCV.translateSchwartz (-s) ρ)
        (translateSchwartzConfiguration
          (osiiDifferenceTimeTranslation (d := d) (-s)) F)) := by
  rw [osiiStageMovingSliceScalar_positiveRealTimeEmbed_eq_zero_translated]
  exact
    osiiStageMovingSliceScalar_zero_eq_orderedPullbackFullCutoff
      A W (SCV.translateSchwartz (-s) ρ) U
      (hasCompactSupport_translateSchwartz ρ hρ_compact (-s))
      hρ_shift_support hscalar hbounded hrep
      (translateSchwartzConfiguration
        (osiiDifferenceTimeTranslation (d := d) (-s)) F)

end OSReconstruction
