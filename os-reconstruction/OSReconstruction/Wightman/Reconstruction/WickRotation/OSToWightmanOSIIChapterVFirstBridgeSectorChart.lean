/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorStageExtensionAtlas
import Init
import OSReconstruction.SCV.DistributionalRepresentationUniqueness
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorRadialStageExtension
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorStageAffineTranslation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorRadialDomain
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVLogarithmicGeneratorDomains
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRootedAnchoredGeneratedBranch
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVAnchoredOrderedTransport
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRootedStageSuccessor













noncomputable section

open Complex Set Topology
open scoped Classical Topology

namespace OSReconstruction
namespace OSIIChapterV

/-- Keep only the first-bridge generator chart on a prescribed domain. -/
def firstBridgeOnlyDomain
    (q : ℕ)
    (domain : Set (OSIITimeGapSpace (q + 1)))
    (i : GeneratorIndex (q + 1)) :
    Set (OSIITimeGapSpace (q + 1)) :=
  if i = firstBridgeGeneratorIndex q then domain else ∅

@[simp]
theorem firstBridgeOnlyDomain_first
    (q : ℕ)
    (domain : Set (OSIITimeGapSpace (q + 1))) :
    firstBridgeOnlyDomain q domain (firstBridgeGeneratorIndex q) =
      domain := by
  simp [firstBridgeOnlyDomain]

theorem firstBridgeOnlyDomain_eq_empty
    (q : ℕ)
    (domain : Set (OSIITimeGapSpace (q + 1)))
    (i : GeneratorIndex (q + 1))
    (hi : i ≠ firstBridgeGeneratorIndex q) :
    firstBridgeOnlyDomain q domain i = ∅ := by
  simp [firstBridgeOnlyDomain, hi]

namespace FirstBridgeSectorExtensionChartData

variable {d q : ℕ}
  {stage : OSIITimeContinuationStage d (q + 1)}
  {aperture hub : Fin (q + 1) → ℝ}

end FirstBridgeSectorExtensionChartData

namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d q N : ℕ} [NeZero d]
variable
  {J : Section43ProductTimeApproximateIdentity (q + 1)}
  {anchor : Fin (q + 1) → ℝ}
  {OS : OsterwalderSchraderAxioms d}
  {L : SimultaneousTimeContinuationStageLevel d}
  {canonicalEdges : L.HasCanonicalReducedCompactEdges OS}
  {A : AnchoredPacketTimeShellFamilyData (d := d) J anchor}
  {R : TripleConvolutionRootData J}
  {H : RootedA0BlockHolomorphicTranslationData OS A R}
  {lgc : OSLinearGrowthCondition d OS}
  {D :
    StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
      A OS (L.stage (q + 1))}

namespace StageMatchedRootedAnchoredRadialGeneratorData

end StageMatchedRootedAnchoredRadialGeneratorData

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
