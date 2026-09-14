/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSimultaneousAtlasSuccessor
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratedLogarithmicDomains
















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d : ℕ} [NeZero d]

/-- The physical carrier of the depth-zero generated scalar base lies in
every positive-width narrow time carrier. -/
theorem osiiTimeArgumentCarrier_generated_zero_subset_narrow
    {k : ℕ}
    (η : ℝ) (hη : 0 < η) :
    osiiTimeArgumentCarrier (osiiGeneratedLogarithmicBase k 0) ⊆
      osiiNarrowTimeCarrier (k := k) η := by
  intro ζ hζ i
  have hargVector :
      osiiTimeArgumentVector ζ = (0 : Fin k → ℝ) := by
    rw [osiiGeneratedLogarithmicBase_zero] at hζ
    exact Set.mem_singleton_iff.mp hζ.2
  have harg : Complex.arg (ζ i) = 0 := by
    exact congrFun hargVector i
  have him : (ζ i).im = 0 :=
    (Complex.arg_eq_zero_iff.mp harg).2
  constructor
  · exact hζ.1 i
  · rw [him]
    simp only [abs_zero]
    exact mul_pos hη (hζ.1 i)

/-- The proved initial simultaneous level, retaining the exact aperture and
narrow-carrier identity at every positive arity. -/
structure InitialGeneratedLogarithmicStageLevelData
    (OS : OsterwalderSchraderAxioms d) where
  level : SimultaneousTimeContinuationStageLevel d
  aperture : ℕ → ℝ
  aperture_pos : ∀ k, 0 < aperture k
  zeroStage :
    level.stage 0 = canonicalZeroGapTimeContinuationStage OS
  positiveCarrier :
    ∀ k,
      (level.stage (k + 1)).carrier =
        osiiNarrowTimeCarrier (k := k + 1) (aperture k)
  canonicalEdges : level.HasCanonicalReducedCompactEdges OS
  convexCarriers : level.HasConvexCarriers

namespace InitialGeneratedLogarithmicStageLevelData

/-- The original OS axioms supply the entire simultaneous initial level,
including every narrow carrier and canonical compact real edge. -/
theorem exists_initial_ofOS
    (OS : OsterwalderSchraderAxioms d) :
    Nonempty (InitialGeneratedLogarithmicStageLevelData OS) := by
  let I : (k : ℕ) → Section43ProductTimeApproximateIdentity (k + 1) :=
    fun k =>
      Classical.choice
        (Section43ProductTimeApproximateIdentity.nonempty (k + 1))
  choose η hη_pos hη_sum using
    fun k : ℕ => exists_initialStage_aperture (d := d) k
  have hstage :
      ∀ k : ℕ,
        ∃ stage : OSIITimeContinuationStage d (k + 1),
          stage.carrier =
              osiiNarrowTimeCarrier (k := k + 1) (η k) ∧
            HasCanonicalReducedCompactStageEdges OS stage := by
    intro k
    exact
      exists_initialStage_hasCanonicalReducedCompactStageEdges_with_carrier_ofOS
        OS (I k) (η k) (hη_pos k) (hη_sum k)
  choose positiveStage hpositiveStage using hstage
  let L : SimultaneousTimeContinuationStageLevel d :=
    SimultaneousTimeContinuationStageLevel.ofPositiveArityStages
      OS positiveStage
  refine ⟨⟨L, η, hη_pos, rfl, ?_, ?_, ?_⟩⟩
  · intro k
    exact (hpositiveStage k).1
  · exact
      SimultaneousTimeContinuationStageLevel.ofPositiveArityStages_hasCanonicalReducedCompactEdges
        OS positiveStage (fun k => (hpositiveStage k).2)
  · apply
      SimultaneousTimeContinuationStageLevel.ofPositiveArityStages_hasConvexCarriers
        OS positiveStage
    intro k
    rw [(hpositiveStage k).1]
    exact convex_osiiNarrowTimeCarrier (η k)

/-- The depth-zero generated scalar argument carrier is contained in every
stage of the retained initial simultaneous level. -/
theorem generatedArgumentCarrier_subset_stage_zero
    (D : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (k : ℕ) :
    osiiTimeArgumentCarrier (osiiGeneratedLogarithmicBase k 0) ⊆
      (D.level.stage k).carrier := by
  cases k with
  | zero =>
      rw [D.zeroStage]
      simp [canonicalZeroGapTimeContinuationStage,
        zeroGapTimeContinuationStage]
  | succ k =>
      rw [D.positiveCarrier k]
      exact
        osiiTimeArgumentCarrier_generated_zero_subset_narrow
          (D.aperture k) (D.aperture_pos k)

/-- Promote the retained simultaneous level to the atlas invariant used by
the Chapter V successor construction. -/
noncomputable def toAtlasLevel
    (D : InitialGeneratedLogarithmicStageLevelData (d := d) OS) :
    CanonicalGeneratorConvexAtlasStageLevelData OS :=
  CanonicalGeneratorConvexAtlasStageLevelData.ofConvexSimultaneousStageLevel
    D.level D.canonicalEdges D.convexCarriers

@[simp]
theorem toAtlasLevel_stage
    (D : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (k : ℕ) :
    (D.toAtlasLevel.stageData k).stage = D.level.stage k :=
  rfl

/-- The initial simultaneous atlas is constructed around the same unit hub in
every positive arity.  Naming it here preserves the cross-arity lower bound
that would otherwise be lost by reselecting an arbitrary point in each real
patch. -/
def unitPointedHub (k : Nat) : Fin (k + 1) -> Real :=
  fun _ => 1

/-- The unit hub used to build the initial canonical edge remains in the
resulting real patch. -/
theorem unitPointedHub_mem_toAtlasLevel_realRegion
    (D : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (k : Nat) :
    unitPointedHub k ∈ (D.toAtlasLevel.stageData (k + 1)).realRegion := by
  let anchor : Fin (k + 1) -> Real := fun _ => 1
  have hanchor : anchor ∈ section43TimeStrictPositiveRegion (k + 1) := by
    intro i
    norm_num [anchor]
  have hcarrier : {anchor} ⊆ section43TimeStrictPositiveRegion (k + 1) := by
    intro tau htau
    simpa only [Set.mem_singleton_iff] using htau ▸ hanchor
  let edge := Classical.choice
    (D.canonicalEdges (k + 1) {anchor} isCompact_singleton hcarrier)
  change anchor ∈ edge.realRegion
  exact edge.compactCarrier_subset (Set.mem_singleton anchor)

/-- The promoted initial atlas level realizes the canonical generated
logarithmic base at depth zero. -/
theorem generatedArgumentCarrier_subset_atlas_stage_zero
    (D : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (k : ℕ) :
    osiiTimeArgumentCarrier (osiiGeneratedLogarithmicBase k 0) ⊆
      (D.toAtlasLevel.stageData k).stage.carrier := by
  simpa using D.generatedArgumentCarrier_subset_stage_zero k

end InitialGeneratedLogarithmicStageLevelData

end OSIIChapterV
end OSReconstruction
