/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVLogarithmicTargetPhysicalPointedSuccessor
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedOpenBase
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedScalarAmbient














noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- The complete next-rank logarithmic target, with all hypotheses needed for
exact physical principal-log transport. -/
noncomputable def rankSuccessorScalarLogarithmicTargetData
    {d : Nat} [NeZero d]
    {current : SimultaneousTimeContinuationStageLevel d}
    {OS : OsterwalderSchraderAxioms d}
    {depth rank k : Nat}
    (D :
      StrictGeneratedScalarRankSuccessorSeedStageLevelData
        current OS depth rank) :
    LogarithmicTargetAmbientData
      (D.next.stage k)
      (osiiStrictGeneratedLogarithmicBaseAtRank
        k (depth + 1) (rank + 1)) where
  stage :=
    rankSuccessorScalarLogarithmicTargetAmbientStage D
  base_open :=
    isOpen_rankSuccessorScalarBase rank k depth
  zero_mem_base :=
    OSIIStrictGeneratedLogarithmicArgumentAtRank.scalar_zero_mem
      (rank + 1) k (depth + 1)
  base_solid :=
    strictGeneratedScalarBaseAtRank_isCoordinatewiseSolid
      k (depth + 1) (rank + 1)
  tube_subset_stage :=
    rankSuccessorScalarLogarithmicTube_subset_ambientStage D
  exists_open_seed :=
    exists_open_seed_rankSuccessorScalarAmbientStage_eq_predecessor D

/-- Pointed predecessor data for the ranked physical target. Canonical compact
edges supply the required positive-real hub membership. -/
noncomputable def rankSuccessorScalarPhysicalPointedData
    {d : Nat} [NeZero d]
    {current : SimultaneousTimeContinuationStageLevel d}
    {OS : OsterwalderSchraderAxioms d}
    {depth rank k : Nat}
    (D :
      StrictGeneratedScalarRankSuccessorSeedStageLevelData
        current OS depth rank)
    (chart : Type)
    (hub : Fin k -> Real)
    (hub_positive :
      hub ∈ section43TimeStrictPositiveRegion k)
    (pointedAtlas :
      GeneratorStagePointedConvexAtlas
        (D.next.stage k)
        (osiiPositiveRealTimeEmbed hub)
        chart) :
    LogarithmicTargetAmbientData.PhysicalPointedPredecessorData
      (rankSuccessorScalarLogarithmicTargetData
        (k := k) D) where
  chart := chart
  hub := hub
  hub_positive := hub_positive
  hub_mem_predecessor :=
    (D.canonicalEdges k).positiveReal_mem_carrier
      hub hub_positive
  pointedAtlas := pointedAtlas

end OSIIChapterV
end OSReconstruction
