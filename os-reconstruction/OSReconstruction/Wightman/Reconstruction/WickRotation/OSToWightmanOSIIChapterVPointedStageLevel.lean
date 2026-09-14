/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSimultaneousAtlasSuccessor
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageExtensionConvexCoreAtlas














noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d : ℕ} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

/-- A simultaneous continuation level with canonical compact edges and one
fixed-hub pointed convex atlas at every positive arity. -/
structure CanonicalGeneratorPointedConvexAtlasStageLevelData
    (OS : OsterwalderSchraderAxioms d) where
  stageLevel : SimultaneousTimeContinuationStageLevel d
  canonicalEdges :
    stageLevel.HasCanonicalReducedCompactEdges OS
  chart : ℕ → Type
  hub : ∀ k, Fin (k + 1) → ℝ
  hub_positive :
    ∀ k, hub k ∈ section43TimeStrictPositiveRegion (k + 1)
  pointedAtlas :
    ∀ k,
      GeneratorStagePointedConvexAtlas
        (stageLevel.stage (k + 1))
        (osiiPositiveRealTimeEmbed (hub k))
        (chart k)

namespace CanonicalGeneratorPointedConvexAtlasStageLevelData

noncomputable instance :
    CanonicalGeneratorStageLevelProvider OS
      (CanonicalGeneratorPointedConvexAtlasStageLevelData OS) where
  stageLevel := fun S => S.stageLevel
  canonicalEdges := fun S => S.canonicalEdges

end CanonicalGeneratorPointedConvexAtlasStageLevelData

namespace CanonicalGeneratorConvexAtlasStageLevelData

/-- Point a simultaneous convex-atlas level at a prescribed positive-real hub
in each arity.  The hub membership proof is retained instead of replacing the
chosen centers by unrelated noncomputable points. -/
noncomputable def toPointedStageLevelAt
    (S : CanonicalGeneratorConvexAtlasStageLevelData OS)
    (hub : forall k, Fin (k + 1) -> Real)
    (hub_mem : forall k, hub k ∈ (S.stageData (k + 1)).realRegion) :
    CanonicalGeneratorPointedConvexAtlasStageLevelData OS where
  stageLevel := S.toSimultaneousTimeContinuationStageLevel
  canonicalEdges := S.hasCanonicalReducedCompactEdges
  chart := fun k => (S.stageData (k + 1)).chart
  hub := hub
  hub_positive := fun k =>
    (S.stageData (k + 1)).realRegion_subset_strictPositive (hub_mem k)
  pointedAtlas := fun k =>
    (S.stageData (k + 1)).atlas.toPointedAtReal (hub k) (hub_mem k)

end CanonicalGeneratorConvexAtlasStageLevelData

end OSIIChapterV
end OSReconstruction
