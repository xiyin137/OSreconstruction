/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedRootedSuccessor












noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d k : Nat} [NeZero d] [NeZero k]
variable
  {OS : OsterwalderSchraderAxioms d}
  {C : Type*}
  [CanonicalGeneratorStageLevelProvider OS C]
  {ι : Type*}

set_option maxHeartbeats 1000000 in
/-- Every strict-rank physical generator target has an actual pointed
source-matched extension under the original OS axioms alone. -/
theorem nonempty_rootedTargetHubPointedDirectExtensionDataOfOS_atRank
    (S : C)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (i : GeneratorIndex k)
    (hub : Fin k -> Real)
    (hhub : hub ∈ section43TimeStrictPositiveRegion k)
    (atlas :
      GeneratorStagePointedConvexAtlas
        (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S k)
        (osiiPositiveRealTimeEmbed hub) ι)
    (z : OSIITimeGapSpace k)
    (left : Fin i.n -> Real)
    (hleft :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed i.n depth left)
    (right : Fin i.m -> Real)
    (hright :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed i.m depth right)
    (theta : Real)
    (hz :
      z ∈ osiiTimeArgumentCarrier
        ({osiiArgumentGeneratorPoint i left theta right} :
          Set (Fin k -> Real))) :
    Nonempty
      (RootedTargetHubPointedDirectExtensionDataOfOS
        S depth P.toAtlasFamily i hub z atlas) := by
  let C0 := targetHubHalfAnchorData hub hhub z hz.1
  let Q :=
    selectedAnchorLocalRootedReflectedGramRadialProducerOfOS
      S depth P.toAtlasFamily C0.anchor C0.anchor_positive
  obtain ⟨D⟩ :=
    nonempty_rootedTargetHubAdaptedReflectedGramData_atRank
      S depth rank P Q.packet Q.roots
      Q.holomorphic.toContinuousTranslationData
      i hub C0.anchor_le_hub z
      left hleft right hright theta hz
  exact
    nonempty_rootedTargetHubPointedDirectExtensionDataOfOS_of_rootedData
      S depth P.toAtlasFamily i hub atlas z C0 Q D

/-- Select the original-OS pointed rooted extension assigned to one strict
rank generator chart. -/
noncomputable def selectedRootedTargetHubPointedDirectExtensionAtRankOfOS
    (S : C)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (hub : Fin k -> Real)
    (hhub : hub ∈ section43TimeStrictPositiveRegion k)
    (atlas :
      GeneratorStagePointedConvexAtlas
        (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S k)
        (osiiPositiveRealTimeEmbed hub) ι)
    (a : RootedStrictGeneratedTargetHubChartAtRank k depth rank) :
    RootedTargetHubPointedDirectExtensionDataOfOS
      S depth P.toAtlasFamily a.generator hub a.target atlas :=
  Classical.choice
    (nonempty_rootedTargetHubPointedDirectExtensionDataOfOS_atRank
      S depth rank P a.generator hub hhub atlas a.target
      a.left a.left_rank a.right a.right_rank
      a.theta a.target_mem)

/-- The complete original-OS common-hub convex-core atlas of strict-rank
physical generator targets. -/
noncomputable def
    rootedStrictGeneratedTargetHubPointedConvexCoreAtlasDataAtRankOfOS
    (S : C)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (hub : Fin k -> Real)
    (hhub : hub ∈ section43TimeStrictPositiveRegion k)
    (atlas :
      GeneratorStagePointedConvexAtlas
        (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S k)
        (osiiPositiveRealTimeEmbed hub) ι) :
    GeneratorStageExtensionConvexCoreAtlasData
      (CanonicalGeneratorStageLevelProvider.stage
        (OS := OS) S k) where
  chart := RootedStrictGeneratedTargetHubChartAtRank k depth rank
  chartGenerator := fun a => a.generator
  carrier := fun a =>
    (selectedRootedTargetHubPointedDirectExtensionAtRankOfOS
      S depth rank P hub hhub atlas a).carrier
  carrier_open := fun a =>
    (selectedRootedTargetHubPointedDirectExtensionAtRankOfOS
      S depth rank P hub hhub atlas a).carrier_open
  carrier_convex := fun a =>
    (selectedRootedTargetHubPointedDirectExtensionAtRankOfOS
      S depth rank P hub hhub atlas a).carrier_convex
  extension := fun a =>
    (selectedRootedTargetHubPointedDirectExtensionAtRankOfOS
      S depth rank P hub hhub atlas a).extension
  carrier_subset_extensionDomain := fun a =>
    (selectedRootedTargetHubPointedDirectExtensionAtRankOfOS
      S depth rank P hub hhub atlas a
      ).carrier_subset_extensionDomain
  commonPoint := osiiPositiveRealTimeEmbed hub
  commonPoint_mem_predecessor :=
    (CanonicalGeneratorStageLevelProvider.hasCanonicalReducedCompactEdges
      (OS := OS) S k).positiveReal_mem_carrier hub hhub
  commonPoint_mem_carrier := fun a =>
    (selectedRootedTargetHubPointedDirectExtensionAtRankOfOS
      S depth rank P hub hhub atlas a).hub_mem_carrier

namespace RootedStrictGeneratedTargetHubPointedConvexCoreAtlasAtRank

/-- Original-OS target-core selection covers every strict-rank generator
fiber. -/
theorem argumentGeneratorCarrier_subset_iUnion_carrierOfOS
    (S : C)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (hub : Fin k -> Real)
    (hhub : hub ∈ section43TimeStrictPositiveRegion k)
    (atlas :
      GeneratorStagePointedConvexAtlas
        (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S k)
        (osiiPositiveRealTimeEmbed hub) ι)
    (i : GeneratorIndex k)
    (left : Fin i.n -> Real)
    (hleft :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed i.n depth left)
    (theta : Real)
    (htheta : |theta| < Real.pi / 2)
    (right : Fin i.m -> Real)
    (hright :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed i.m depth right) :
    osiiTimeArgumentCarrier
        ({osiiArgumentGeneratorPoint i left theta right} :
          Set (Fin k -> Real)) ⊆
      ⋃ a : RootedStrictGeneratedTargetHubChartAtRank k depth rank,
        (rootedStrictGeneratedTargetHubPointedConvexCoreAtlasDataAtRankOfOS
          S depth rank P hub hhub atlas).carrier a := by
  intro z hz
  let a : RootedStrictGeneratedTargetHubChartAtRank k depth rank :=
    { generator := i
      left := left
      left_rank := hleft
      theta := theta
      angle_bound := htheta
      right := right
      right_rank := hright
      target := z
      target_mem := hz }
  exact
    Set.mem_iUnion_of_mem a
      (selectedRootedTargetHubPointedDirectExtensionAtRankOfOS
        S depth rank P hub hhub atlas a).target_mem_carrier

/-- One source-compatible original-OS pointed successor contains every
strict-rank physical generator fiber. -/
theorem argumentGeneratorCarrier_subset_successorCarrierOfOS
    (S : C)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank)
    (hub : Fin k -> Real)
    (hhub : hub ∈ section43TimeStrictPositiveRegion k)
    (atlas :
      GeneratorStagePointedConvexAtlas
        (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S k)
        (osiiPositiveRealTimeEmbed hub) ι)
    (i : GeneratorIndex k)
    (left : Fin i.n -> Real)
    (hleft :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed i.n depth left)
    (theta : Real)
    (htheta : |theta| < Real.pi / 2)
    (right : Fin i.m -> Real)
    (hright :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed i.m depth right) :
    osiiTimeArgumentCarrier
        ({osiiArgumentGeneratorPoint i left theta right} :
          Set (Fin k -> Real)) ⊆
      (rootedStrictGeneratedTargetHubPointedConvexCoreAtlasDataAtRankOfOS
        S depth rank P hub hhub atlas).successorStage.carrier :=
  (rootedStrictGeneratedTargetHubPointedConvexCoreAtlasDataAtRankOfOS
      S depth rank P hub hhub atlas
    ).argumentGeneratorCarrier_subset_successorCarrier
      i left theta right
      (argumentGeneratorCarrier_subset_iUnion_carrierOfOS
        S depth rank P hub hhub atlas
        i left hleft theta htheta right hright)

end RootedStrictGeneratedTargetHubPointedConvexCoreAtlasAtRank

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity

namespace CanonicalGeneratorPointedConvexAtlasStageLevelData

open Section43ProductTimeApproximateIdentity
open Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData

variable {d : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

/-- The original-OS strict-rank rooted convex-core atlas at one positive
arity. -/
noncomputable def rootedInsertionRankConvexCoreAtlasOfOS
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) D depth rank)
    (q : Nat) :
    GeneratorStageExtensionConvexCoreAtlasData
      (D.stageLevel.stage (q + 1)) :=
  rootedStrictGeneratedTargetHubPointedConvexCoreAtlasDataAtRankOfOS
    D depth rank P
    (D.hub q) (D.hub_positive q) (D.pointedAtlas q)

/-- Simultaneous strict-rank original-OS generator insertion, retaining the
complete zero-gap predecessor. -/
noncomputable def rootedInsertionRankStageLevelOfOS
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) D depth rank) :
    SimultaneousTimeContinuationStageLevel d where
  stage
    | 0 => D.stageLevel.stage 0
    | q + 1 => (D.rootedInsertionRankConvexCoreAtlasOfOS
        depth rank P q).successorStage

@[simp]
theorem rootedInsertionRankStageLevelOfOS_stage_zero
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) D depth rank) :
    (D.rootedInsertionRankStageLevelOfOS depth rank P).stage 0 =
      D.stageLevel.stage 0 :=
  rfl

@[simp]
theorem rootedInsertionRankStageLevelOfOS_stage_succ
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) D depth rank)
    (q : Nat) :
    (D.rootedInsertionRankStageLevelOfOS depth rank P).stage (q + 1) =
      (D.rootedInsertionRankConvexCoreAtlasOfOS
        depth rank P q).successorStage :=
  rfl

/-- Original-OS ranked generator insertion retains every predecessor
carrier. -/
theorem oldCarrier_subset_rootedInsertionRankStageLevelOfOS
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) D depth rank)
    (k : Nat) :
    (D.stageLevel.stage k).carrier ⊆
      ((D.rootedInsertionRankStageLevelOfOS
        depth rank P).stage k).carrier := by
  cases k with
  | zero =>
      exact Set.Subset.rfl
  | succ q =>
      exact
        (D.rootedInsertionRankConvexCoreAtlasOfOS
          depth rank P q).oldCarrier_subset_successorCarrier

/-- Original-OS ranked generator insertion preserves the full predecessor
distribution on its complete carrier. -/
theorem rootedInsertionRankStageLevelOfOS_extends
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) D depth rank)
    (k : Nat) :
    Set.EqOn
      ((D.rootedInsertionRankStageLevelOfOS
        depth rank P).stage k).distribution
      (D.stageLevel.stage k).distribution
      (D.stageLevel.stage k).carrier := by
  cases k with
  | zero =>
      exact Set.eqOn_refl _ _
  | succ q =>
      exact
        (D.rootedInsertionRankConvexCoreAtlasOfOS
          depth rank P q).successorStage_extends_predecessor

/-- Canonical compact positive-real edges survive original-OS ranked
generator insertion. -/
theorem rootedInsertionRankStageLevelOfOS_hasCanonicalEdges
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) D depth rank) :
    (D.rootedInsertionRankStageLevelOfOS
      depth rank P).HasCanonicalReducedCompactEdges OS := by
  intro k
  cases k with
  | zero =>
      exact D.canonicalEdges 0
  | succ q =>
      exact
        (D.rootedInsertionRankConvexCoreAtlasOfOS
          depth rank P q).stageExtensionData
          |>.preservesCanonicalReducedCompactStageEdges
            OS (D.canonicalEdges (q + 1))

/-- The original-OS strict-rank generator successor retains the same
positive-real hubs and pointed convex-atlas invariant. -/
noncomputable def rootedInsertionRankNextOfOS
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) D depth rank) :
    CanonicalGeneratorPointedConvexAtlasStageLevelData OS where
  stageLevel :=
    D.rootedInsertionRankStageLevelOfOS depth rank P
  canonicalEdges :=
    D.rootedInsertionRankStageLevelOfOS_hasCanonicalEdges
      depth rank P
  chart := fun q =>
    Sum
      (D.chart q)
      (RootedStrictGeneratedTargetHubChartAtRank
        (q + 1) depth rank)
  hub := D.hub
  hub_positive := D.hub_positive
  pointedAtlas := fun q =>
    (D.rootedInsertionRankConvexCoreAtlasOfOS
      depth rank P q).successorPointedConvexAtlas
      (D.pointedAtlas q)

/-- The original-OS ranked pointed successor contains every strict-rank
generated physical argument fiber. -/
theorem argumentGeneratorCarrier_subset_rootedInsertionRankNextOfOS
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth rank : Nat)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) D depth rank)
    (q : Nat)
    (i : GeneratorIndex (q + 1))
    (left : Fin i.n -> Real)
    (hleft :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed i.n depth left)
    (theta : Real)
    (htheta : |theta| < Real.pi / 2)
    (right : Fin i.m -> Real)
    (hright :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .mixed i.m depth right) :
    osiiTimeArgumentCarrier
        ({osiiArgumentGeneratorPoint i left theta right} :
          Set (Fin (q + 1) -> Real)) ⊆
      ((D.rootedInsertionRankNextOfOS
        depth rank P).stageLevel.stage (q + 1)).carrier := by
  exact
    RootedStrictGeneratedTargetHubPointedConvexCoreAtlasAtRank.argumentGeneratorCarrier_subset_successorCarrierOfOS
      D depth rank P
      (D.hub q) (D.hub_positive q) (D.pointedAtlas q)
      i left hleft theta htheta right hright

end CanonicalGeneratorPointedConvexAtlasStageLevelData

end OSIIChapterV
end OSReconstruction
