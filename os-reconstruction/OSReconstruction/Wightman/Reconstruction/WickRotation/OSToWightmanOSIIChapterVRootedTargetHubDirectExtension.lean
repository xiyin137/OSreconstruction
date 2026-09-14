/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRootedTargetHubReflectedGramReplacement
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageWideReflectedGramSelectedRadialExtension












noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {OS : OsterwalderSchraderAxioms d}
  {C : Type*}
  [CanonicalGeneratorStageLevelProvider OS C]
  {S : C}
  {depth : ℕ}
  {P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth}
  {lgc : OSLinearGrowthCondition d OS}
  {anchor : Fin k → ℝ}

namespace AnchorLocalRootedReflectedGramRadialProducerPackage

/-- Retain every analytic choice of an anchor-local producer while replacing
only its stage-wide reflected-Gram atlas package. -/
noncomputable def withStageWideReflectedGram
    (Q :
      AnchorLocalRootedReflectedGramRadialProducerPackage
        S depth P lgc anchor)
    (P' : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth) :
    AnchorLocalRootedReflectedGramRadialProducerPackage
      S depth P' lgc anchor where
  approximateIdentity := Q.approximateIdentity
  packet := Q.packet
  roots := Q.roots
  current := Q.current
  holomorphic := Q.holomorphic

end AnchorLocalRootedReflectedGramRadialProducerPackage

namespace AnchorLocalRootedReflectedGramRadialProducerPackageOfOS

/-- Replace only the reflected-Gram atlas of an original-OS rooted
producer, retaining all of its analytic and source-matching data. -/
noncomputable def withStageWideReflectedGram
    (Q :
      AnchorLocalRootedReflectedGramRadialProducerPackageOfOS
        S depth P anchor)
    (P' : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth) :
    AnchorLocalRootedReflectedGramRadialProducerPackageOfOS
      S depth P' anchor where
  approximateIdentity := Q.approximateIdentity
  packet := Q.packet
  roots := Q.roots
  current := Q.current
  holomorphic := Q.holomorphic

end AnchorLocalRootedReflectedGramRadialProducerPackageOfOS

namespace RootedTargetHubDirectExtensionData

variable
  {i : GeneratorIndex k}
  {hub : Fin k → ℝ}
  {z : OSIITimeGapSpace k}

end RootedTargetHubDirectExtensionData

namespace RootedTargetHubDirectExtensionDataOfOS

variable
  {i : GeneratorIndex k}
  {hub : Fin k → ℝ}
  {z : OSIITimeGapSpace k}

end RootedTargetHubDirectExtensionDataOfOS

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity

end OSIIChapterV
end OSReconstruction
