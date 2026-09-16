import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVCanonicalReducedSchwinger
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReflectedMovingSliceBridge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageRealEdge

/-!
# The zero-gap Chapter V continuation stage

At reduced arity zero there is no analytic continuation problem.  The time
space and the spatial difference space are both zero-dimensional, so every
time Schwartz test is a scalar multiple of the unit test.  Consequently every
zero-gap tempered distribution has a canonical constant holomorphic stage and
an exact positive-real edge.

This supplies the arity-zero member of the simultaneous Chapter V base level.
The genuine initial-stage continuation problem starts at positive reduced
arity.
-/

noncomputable section

open Complex MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d : ℕ} [NeZero d]

/-- The unit Schwartz function on the zero-dimensional time space. -/
noncomputable def zeroGapUnitTimeSchwartz :
    SchwartzMap (Fin 0 → ℝ) ℂ := by
  let f : (Fin 0 → ℝ) → ℂ := fun _ => 1
  have hf_smooth : ContDiff ℝ (⊤ : ENat) f := by
    simpa [f] using
      (contDiff_const :
        ContDiff ℝ (⊤ : ENat) (fun _ : Fin 0 → ℝ => (1 : ℂ)))
  have hf_compact : HasCompactSupport f := by
    simpa [HasCompactSupport, tsupport, Function.support, f] using
      (show IsCompact (Set.univ : Set (Fin 0 → ℝ)) from isCompact_univ)
  exact hf_compact.toSchwartzMap hf_smooth

@[simp] theorem zeroGapUnitTimeSchwartz_apply
    (τ : Fin 0 → ℝ) :
    zeroGapUnitTimeSchwartz τ = 1 := by
  change (1 : ℂ) = 1
  rfl

theorem zeroGapUnitTimeSchwartz_compact :
    HasCompactSupport
      (zeroGapUnitTimeSchwartz : (Fin 0 → ℝ) → ℂ) := by
  change IsCompact (tsupport (fun _ : Fin 0 → ℝ => (1 : ℂ)))
  simpa [tsupport, Function.support] using
    (show IsCompact (Set.univ : Set (Fin 0 → ℝ)) from isCompact_univ)

theorem zeroGapUnitTimeSchwartz_support :
    tsupport
        (zeroGapUnitTimeSchwartz : (Fin 0 → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion 0 := by
  intro τ _hτ
  simp [section43TimeStrictPositiveRegion]

/-- Every zero-dimensional time Schwartz test is its unique value times the
unit test. -/
theorem zeroGapTimeSchwartz_eq_smul_unit
    (φ : SchwartzMap (Fin 0 → ℝ) ℂ) :
    φ = φ default • zeroGapUnitTimeSchwartz := by
  ext τ
  rw [show τ = default from Subsingleton.elim _ _]
  simp

/-- Evaluate a zero-gap spacetime distribution on the unit time test, leaving
the zero-dimensional spatial Schwartz variable. -/
noncomputable def zeroGapSpatialDistribution
    (W : SchwartzNPoint d 0 →L[ℂ] ℂ) :
    OSIISpatialDistribution d 0 :=
  W.comp
    (section43OrderedPullbackTimeSpatialTensorSpatialCLM
      d 0 zeroGapUnitTimeSchwartz)

/-- The constant weakly holomorphic stage attached to a zero-gap
distribution. -/
noncomputable def zeroGapTimeContinuationStage
    (W : SchwartzNPoint d 0 →L[ℂ] ℂ) :
    OSIITimeContinuationStage d 0 where
  carrier := Set.univ
  carrier_open := isOpen_univ
  distribution := fun _ => zeroGapSpatialDistribution W
  weaklyHolomorphic := by
    intro χ
    exact differentiableOn_const _

/-- The constant zero-gap orbit represents the original distribution on the
entire zero-dimensional time space. -/
theorem zeroGapTimeSpatialRepresentsDistributionOn
    (W : SchwartzNPoint d 0 →L[ℂ] ℂ) :
    OSIITimeSpatialRepresentsDistributionOn W
      (fun _ => zeroGapSpatialDistribution W) Set.univ := by
  intro χ φ _hφ
  rw [zeroGapTimeSchwartz_eq_smul_unit φ]
  simp only [map_smul, smul_eq_mul]
  rw [MeasureTheory.Measure.volume_pi_eq_dirac
    (ι := Fin 0) (α := fun _ => ℝ) (x := default)]
  simp only [MeasureTheory.integral_dirac]
  change
    φ default * zeroGapSpatialDistribution W χ =
      zeroGapSpatialDistribution W χ *
        (φ default * zeroGapUnitTimeSchwartz default)
  rw [zeroGapUnitTimeSchwartz_apply]
  simp [mul_comm]

/-- Every zero-gap distribution carries a canonical positive-real edge on
the full zero-dimensional real time space. -/
noncomputable def zeroGapPositiveRealEdgeData
    (W : SchwartzNPoint d 0 →L[ℂ] ℂ) :
    (zeroGapTimeContinuationStage W).PositiveRealEdgeData W Set.univ where
  orbit := fun _ => zeroGapSpatialDistribution W
  stageEdge := by
    intro τ _hτ
    exact ⟨Set.mem_univ _, rfl⟩
  represents := zeroGapTimeSpatialRepresentsDistributionOn W
  pointwiseBounded := by
    intro χ
    exact ⟨‖zeroGapSpatialDistribution W χ‖, fun _τ _hτ => le_rfl⟩

/-- The canonical reduced zero-gap Schwinger distribution in ordered
coordinates. -/
noncomputable def canonicalZeroGapReducedDistribution
    (OS : OsterwalderSchraderAxioms d) :
    SchwartzNPoint d 0 →L[ℂ] ℂ :=
  orderedTransportDistribution
    (canonicalReducedTimeCutoffSchwingerCLM
      OS zeroGapUnitTimeSchwartz zeroGapUnitTimeSchwartz_support)

/-- The canonical arity-zero member of the simultaneous Chapter V stage
level. -/
noncomputable def canonicalZeroGapTimeContinuationStage
    (OS : OsterwalderSchraderAxioms d) :
    OSIITimeContinuationStage d 0 :=
  zeroGapTimeContinuationStage
    (canonicalZeroGapReducedDistribution OS)

/-- The canonical zero-gap stage has the canonical reduced Schwinger edge on
the full real time space. -/
noncomputable def canonicalZeroGapPositiveRealEdgeData
    (OS : OsterwalderSchraderAxioms d) :
    (canonicalZeroGapTimeContinuationStage OS).PositiveRealEdgeData
      (canonicalZeroGapReducedDistribution OS) Set.univ :=
  zeroGapPositiveRealEdgeData
    (canonicalZeroGapReducedDistribution OS)

end OSIIChapterV
end OSReconstruction
