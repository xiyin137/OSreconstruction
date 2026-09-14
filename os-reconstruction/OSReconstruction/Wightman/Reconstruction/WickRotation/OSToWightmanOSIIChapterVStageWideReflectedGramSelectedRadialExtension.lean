/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageExtensionConvexCoreAtlas
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageWideReflectedGramRadialStageExtension





















noncomputable section

open Complex Filter Set Topology
open scoped Classical Topology

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {OS : OsterwalderSchraderAxioms d}
  {StageLevel : Type*}
  [CanonicalGeneratorStageLevelProvider OS StageLevel]
  {S : StageLevel}
  {depth : ℕ}
  {P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth}
  {lgc : OSLinearGrowthCondition d OS}
  {anchor : Fin k → ℝ}

/-- One open positive-real predecessor patch through a prescribed anchor,
contained in every chart of a convex cover of the full predecessor stage. -/
structure AnchoredGeneratorStageConvexAtlasData
    (stage : OSIITimeContinuationStage d k)
    (anchor : Fin k → ℝ) where
  chart : Type
  realRegion : Set (Fin k → ℝ)
  realRegion_open : IsOpen realRegion
  anchor_mem : anchor ∈ realRegion
  atlas : GeneratorStageConvexAtlas stage realRegion chart

namespace AnchoredGeneratorStageConvexAtlasData

end AnchoredGeneratorStageConvexAtlasData

namespace GeneratorStageExtensionData

variable {stage : OSIITimeContinuationStage d k}

end GeneratorStageExtensionData

namespace GeneratorStageEnvelopeExtension

variable
  {stage : OSIITimeContinuationStage d k}
  {C : GeneratorStageExtensionData stage}
  {carrier : Set (OSIITimeGapSpace k)}

end GeneratorStageEnvelopeExtension

namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

/-- The complete anchor-local rooted analytic producer under the original OS
axioms alone. None of its data require a global arity-growth condition. -/
structure AnchorLocalRootedReflectedGramRadialProducerPackageOfOS
    (S : StageLevel)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (anchor : Fin k → ℝ) where
  approximateIdentity :
    Section43ProductTimeApproximateIdentity k
  packet :
    AnchoredPacketTimeShellFamilyData
      (d := d) approximateIdentity anchor
  roots :
    TripleConvolutionRootData approximateIdentity
  current :
    StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
      packet OS (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k)
  holomorphic :
    RootedA0BlockHolomorphicTranslationData OS packet roots

/-- The rooted reflected-Gram analytic producer at one anchor. Its
approximate identity is local to this package, and no predecessor atlas has
yet been chosen. -/
structure AnchorLocalRootedReflectedGramRadialProducerPackage
    (S : StageLevel)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (lgc : OSLinearGrowthCondition d OS)
    (anchor : Fin k → ℝ) where
  approximateIdentity :
    Section43ProductTimeApproximateIdentity k
  packet :
    AnchoredPacketTimeShellFamilyData
      (d := d) approximateIdentity anchor
  roots :
    TripleConvolutionRootData approximateIdentity
  current :
    StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
      packet OS (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k)
  holomorphic :
    RootedA0BlockHolomorphicTranslationData OS packet roots

namespace AnchorLocalRootedReflectedGramRadialProducerPackageOfOS

/-- Preserve the old phantom growth-indexed producer interface without
using that hypothesis in the actual anchor-local construction. -/
def toLegacy
    (Q :
      AnchorLocalRootedReflectedGramRadialProducerPackageOfOS
        S depth P anchor)
    (lgc : OSLinearGrowthCondition d OS) :
    AnchorLocalRootedReflectedGramRadialProducerPackage
      S depth P lgc anchor where
  approximateIdentity := Q.approximateIdentity
  packet := Q.packet
  roots := Q.roots
  current := Q.current
  holomorphic := Q.holomorphic

/-- The exact radial domains of the original-OS anchor-local producer. -/
noncomputable def radialData
    (Q :
      AnchorLocalRootedReflectedGramRadialProducerPackageOfOS
        S depth P anchor) :
    GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k :=
  rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
    S depth P Q.packet Q.roots
    Q.holomorphic.toContinuousTranslationData

/-- Match the actual represented source edge to any predecessor atlas patch
containing the selected positive anchor. -/
noncomputable def matched
    (Q :
      AnchorLocalRootedReflectedGramRadialProducerPackageOfOS
        S depth P anchor)
    (A :
      AnchoredGeneratorStageConvexAtlasData
        (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k) anchor) :
    StageMatchedRootedReflectedGramRadialGeneratorDataOfOS
      S depth P Q.current Q.holomorphic :=
  Classical.choose
    (exists_stageMatchedRootedReflectedGramRadialGeneratorDataOfOS_of_anchor_mem_open
      S depth P Q.current Q.holomorphic
      A.realRegion A.realRegion_open A.anchor_mem)

theorem matched_edge_subset_atlas
    (Q :
      AnchorLocalRootedReflectedGramRadialProducerPackageOfOS
        S depth P anchor)
    (A :
      AnchoredGeneratorStageConvexAtlasData
        (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k) anchor) :
    ∀ u ∈ (Q.matched A).edge.realRegion,
      u + anchor ∈ A.realRegion :=
  Classical.choose_spec
    (exists_stageMatchedRootedReflectedGramRadialGeneratorDataOfOS_of_anchor_mem_open
      S depth P Q.current Q.holomorphic
      A.realRegion A.realRegion_open A.anchor_mem)

/-- The original-OS centered radial extension preserves the predecessor's
actual represented source distribution on their complete overlap. -/
noncomputable def centeredExtension
    (Q :
      AnchorLocalRootedReflectedGramRadialProducerPackageOfOS
        S depth P anchor)
    (A :
      AnchoredGeneratorStageConvexAtlasData
        (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k) anchor) :
    GeneratorStageExtensionData
      ((CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k).recenter anchor) :=
  (Q.matched A).toStageExtensionDataOfConvexAtlas
    A.atlas (Q.matched_edge_subset_atlas A)

@[simp]
theorem centeredExtension_domain
    (Q :
      AnchorLocalRootedReflectedGramRadialProducerPackageOfOS
        S depth P anchor)
    (A :
      AnchoredGeneratorStageConvexAtlasData
        (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k) anchor)
    (i : GeneratorIndex k) :
    (Q.centeredExtension A).domain i =
      Q.radialData.radialChronologicalDomain i :=
  rfl

end AnchorLocalRootedReflectedGramRadialProducerPackageOfOS

namespace AnchorLocalRootedReflectedGramRadialProducerPackage

/-- The radial domain data of the locally selected rooted producer. -/
noncomputable def radialData
    (Q :
      AnchorLocalRootedReflectedGramRadialProducerPackage
        S depth P lgc anchor) :
    GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k :=
  rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
    S depth P Q.packet Q.roots
    Q.holomorphic.toContinuousTranslationData

/-- Select a matched reflected-Gram edge whose absolute translate remains in
the chosen anchor-local predecessor patch. -/
noncomputable def matched
    (Q :
      AnchorLocalRootedReflectedGramRadialProducerPackage
        S depth P lgc anchor)
    (A :
      AnchoredGeneratorStageConvexAtlasData
        (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k) anchor) :
    StageMatchedRootedReflectedGramRadialGeneratorData
      S depth P Q.current Q.holomorphic lgc :=
  Classical.choose
    (exists_stageMatchedRootedReflectedGramRadialGeneratorData_of_anchor_mem_open
      S depth P Q.current Q.holomorphic lgc
      A.realRegion A.realRegion_open A.anchor_mem)

theorem matched_edge_subset_atlas
    (Q :
      AnchorLocalRootedReflectedGramRadialProducerPackage
        S depth P lgc anchor)
    (A :
      AnchoredGeneratorStageConvexAtlasData
        (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k) anchor) :
    ∀ u ∈ (Q.matched A).edge.realRegion,
      u + anchor ∈ A.realRegion :=
  Classical.choose_spec
    (exists_stageMatchedRootedReflectedGramRadialGeneratorData_of_anchor_mem_open
      S depth P Q.current Q.holomorphic lgc
      A.realRegion A.realRegion_open A.anchor_mem)

/-- The centered extension obtained after supplying the mobile predecessor
atlas patch at this anchor. -/
noncomputable def centeredExtension
    (Q :
      AnchorLocalRootedReflectedGramRadialProducerPackage
        S depth P lgc anchor)
    (A :
      AnchoredGeneratorStageConvexAtlasData
        (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k) anchor) :
    GeneratorStageExtensionData
      ((CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k).recenter anchor) :=
  (Q.matched A).toStageExtensionDataOfConvexAtlas
    A.atlas (Q.matched_edge_subset_atlas A)

@[simp]
theorem centeredExtension_domain
    (Q :
      AnchorLocalRootedReflectedGramRadialProducerPackage
        S depth P lgc anchor)
    (A :
      AnchoredGeneratorStageConvexAtlasData
        (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k) anchor)
    (i : GeneratorIndex k) :
    (Q.centeredExtension A).domain i =
      Q.radialData.radialChronologicalDomain i :=
  rfl

end AnchorLocalRootedReflectedGramRadialProducerPackage

/-- Select the complete source-compatible anchor-local reflected-Gram
producer using only the original OS axioms. -/
noncomputable def selectedAnchorLocalRootedReflectedGramRadialProducerOfOS
    (S : StageLevel)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (anchor : Fin k → ℝ)
    (hanchor : anchor ∈ section43TimeStrictPositiveRegion k) :
    AnchorLocalRootedReflectedGramRadialProducerPackageOfOS
      S depth P anchor := by
  let Q :=
    selectedRootedAnchoredPacketTimeShellFamilyData
      (d := d) anchor hanchor
  let L :=
    CanonicalGeneratorStageLevelProvider.toSimultaneousTimeContinuationStageLevel
      (OS := OS) S
  let canonicalEdges :=
    CanonicalGeneratorStageLevelProvider.hasCanonicalReducedCompactEdges
      (OS := OS) S
  let H :=
    Q.packet.rootedA0BlockHolomorphicTranslationData
      L OS canonicalEdges Q.roots
  let D :=
    Classical.choice
      (nonempty_stageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
        (A := Q.packet) (canonicalEdges k))
  exact
    { approximateIdentity := Q.approximateIdentity
      packet := Q.packet
      roots := Q.roots
      current := D
      holomorphic := H }

/-- Select the complete rooted reflected-Gram analytic producer from any
strict-positive anchor. No cross-anchor approximate identity and no fixed
predecessor real patch are required. -/
noncomputable def selectedAnchorLocalRootedReflectedGramRadialProducer
    (S : StageLevel)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (lgc : OSLinearGrowthCondition d OS)
    (anchor : Fin k → ℝ)
    (hanchor : anchor ∈ section43TimeStrictPositiveRegion k) :
    AnchorLocalRootedReflectedGramRadialProducerPackage
      S depth P lgc anchor :=
  (selectedAnchorLocalRootedReflectedGramRadialProducerOfOS
    S depth P anchor hanchor).toLegacy lgc

namespace SelectedRootedReflectedGramVanishingAnchorRadialWitnessData

end SelectedRootedReflectedGramVanishingAnchorRadialWitnessData

namespace SelectedRootedReflectedGramVanishingAnchorRadialChartData

end SelectedRootedReflectedGramVanishingAnchorRadialChartData

namespace SelectedRootedReflectedGramGeneratorFiberCoreData

variable
  {generator : GeneratorIndex k}
  {left : Fin generator.n → ℝ}
  {θ : ℝ}
  {right : Fin generator.m → ℝ}

end SelectedRootedReflectedGramGeneratorFiberCoreData

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
