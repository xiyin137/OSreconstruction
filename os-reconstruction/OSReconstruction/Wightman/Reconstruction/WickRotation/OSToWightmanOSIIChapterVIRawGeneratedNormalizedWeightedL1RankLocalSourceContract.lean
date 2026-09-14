/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRawGeneratedNormalizedWeightedL1SourcePoint
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621SourceIntegralSegment
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedApproximationRecovery
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedDensityDistributionBound
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedGeometry
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621Recovery
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIUniformEquation621Seed
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINormalizedEnvelopeBoundedRankInduction
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINormalizedEnvelopeWeightedSourceEnvelope
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageWideReflectedGramRootedBounds
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedReflectedGram
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedSourceIntegral
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation629Majorant
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedBoundedScalarPhysicalCharts











noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

open Section43ProductTimeApproximateIdentity
open Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData

namespace RawStrictGeneratedVI2RankLocalNormalizedWeightedL1DepthBoundData

/-- Equation-(6.21)'s left center is the rooted left block of the centered
parent point. -/
theorem equation621RootedLeftCenter_eq_rootedLeftBlockTarget_centered
    {k : Nat}
    (i : GeneratorIndex k)
    (anchor : Fin k -> Real)
    (w : OSIITimeGapSpace k) :
    equation621RootedLeftCenter i anchor w =
      rootedLeftBlockTarget i
        (w - osiiPositiveRealTimeEmbed anchor) := by
  ext a
  rw [equation621RootedLeftCenter_apply]
  change star (w (i.leftGlobalIndex a) - anchor (i.leftGlobalIndex a)) =
    star
      ((i.splitCoordinatesCLM
        (generatorChronologicalParameterComplexCLE i
          (w - osiiPositiveRealTimeEmbed anchor))).2.1 a)
  rw [generatorChronological_split_left]
  simp [osiiPositiveRealTimeEmbed]

/-- Equation-(6.21)'s right center is the rooted right block of the centered
parent point. -/
theorem equation621RootedRightCenter_eq_rootedRightBlockTarget_centered
    {k : Nat}
    (i : GeneratorIndex k)
    (anchor : Fin k -> Real)
    (w : OSIITimeGapSpace k) :
    equation621RootedRightCenter i anchor w =
      rootedRightBlockTarget i
        (w - osiiPositiveRealTimeEmbed anchor) := by
  ext b
  rw [equation621RootedRightCenter_apply]
  change w (i.rightGlobalIndex b) - anchor (i.rightGlobalIndex b) =
    (i.splitCoordinatesCLM
      (generatorChronologicalParameterComplexCLE i
        (w - osiiPositiveRealTimeEmbed anchor))).2.2 b
  rw [generatorChronological_split_right]
  simp [osiiPositiveRealTimeEmbed]

end RawStrictGeneratedVI2RankLocalNormalizedWeightedL1DepthBoundData

end OSIIChapterV
end OSReconstruction
