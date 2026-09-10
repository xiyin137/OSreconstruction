/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRootedStageAtlasSuccessor
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVAngleExhaustion













noncomputable section

open Complex Set Topology
open scoped Classical Topology

namespace OSReconstruction
namespace OSIIChapterV

variable {d : ℕ} [NeZero d]

/-- A coherent Chapter V induction level carrying the fixed-coordinate convex
atlas invariant at every reduced time-gap arity. -/
structure CanonicalGeneratorConvexAtlasStageLevelData
    (OS : OsterwalderSchraderAxioms d) where
  stageData :
    (k : ℕ) → CanonicalGeneratorConvexAtlasStageData OS k

/-- Minimal stage-level interface used by the reflected-Gram analytic
construction.  Atlas geometry is deliberately absent: the construction only
needs the simultaneous stages and their canonical compact real edges. -/
class CanonicalGeneratorStageLevelProvider
    (OS : OsterwalderSchraderAxioms d)
    (C : Type*) where
  stageLevel :
    C → SimultaneousTimeContinuationStageLevel d
  canonicalEdges :
    ∀ S : C, (stageLevel S).HasCanonicalReducedCompactEdges OS

namespace CanonicalGeneratorStageLevelProvider

variable {OS : OsterwalderSchraderAxioms d}
variable {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]

/-- The simultaneous continuation level exposed by a stage-level provider. -/
def toSimultaneousTimeContinuationStageLevel
    (S : C) :
    SimultaneousTimeContinuationStageLevel d :=
  CanonicalGeneratorStageLevelProvider.stageLevel
    (OS := OS) S

/-- The stage at one arity exposed by a stage-level provider. -/
def stage
    (S : C)
    (k : ℕ) :
    OSIITimeContinuationStage d k :=
  (toSimultaneousTimeContinuationStageLevel
    (OS := OS) S).stage k

/-- Canonical compact edges exposed by a stage-level provider. -/
theorem hasCanonicalReducedCompactEdges
    (S : C) :
    (toSimultaneousTimeContinuationStageLevel
      (OS := OS) S
      ).HasCanonicalReducedCompactEdges OS :=
  CanonicalGeneratorStageLevelProvider.canonicalEdges
    (OS := OS) S

end CanonicalGeneratorStageLevelProvider

namespace CanonicalGeneratorConvexAtlasStageLevelData

variable {OS : OsterwalderSchraderAxioms d}

/-- Forget the atlas bookkeeping and expose the simultaneous continuation
level consumed by the rooted block-field construction. -/
def toSimultaneousTimeContinuationStageLevel
    (S : CanonicalGeneratorConvexAtlasStageLevelData OS) :
    SimultaneousTimeContinuationStageLevel d where
  stage k := (S.stageData k).stage

/-- The atlas level retains the canonical compact-edge invariant required to
construct all rooted block fields at the next induction level. -/
theorem hasCanonicalReducedCompactEdges
    (S : CanonicalGeneratorConvexAtlasStageLevelData OS) :
    S.toSimultaneousTimeContinuationStageLevel.HasCanonicalReducedCompactEdges
      OS :=
  fun k => (S.stageData k).canonicalEdges

/-- A simultaneous stage with convex carriers and canonical compact edges
induces the fixed-coordinate atlas invariant at every arity.  The constant
strict-positive anchor is used only to choose a common local real patch. -/
noncomputable def ofConvexSimultaneousStageLevel
    (L : SimultaneousTimeContinuationStageLevel d)
    (Hcanonical : L.HasCanonicalReducedCompactEdges OS)
    (Hconvex : L.HasConvexCarriers) :
    CanonicalGeneratorConvexAtlasStageLevelData OS where
  stageData k := by
    let anchor : Fin k → ℝ := fun _ => 1
    have hanchor :
        anchor ∈ section43TimeStrictPositiveRegion k := by
      intro i
      norm_num [anchor]
    have hcarrier :
        {anchor} ⊆ section43TimeStrictPositiveRegion k := by
      intro τ hτ
      simpa only [Set.mem_singleton_iff] using hτ ▸ hanchor
    let D :=
      Classical.choice
        (Hcanonical k {anchor} isCompact_singleton hcarrier)
    exact
      CanonicalGeneratorConvexAtlasStageData.ofConvexCompactEdge
        (Hcanonical k) D (Set.singleton_nonempty anchor) (Hconvex k)

end CanonicalGeneratorConvexAtlasStageLevelData

namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {OS : OsterwalderSchraderAxioms d}

/-- The rooted holomorphic block data at arity `k` obtained from the current
simultaneous atlas level. -/
noncomputable def selectedStageLevelSuccessorHolomorphicData
    (S : CanonicalGeneratorConvexAtlasStageLevelData OS)
    (k : ℕ) [NeZero k] :
    RootedA0BlockHolomorphicTranslationData
      OS (selectedSuccessorPacket (S.stageData k)).packet
        (selectedSuccessorPacket (S.stageData k)).roots :=
  (selectedSuccessorPacket (S.stageData k)).packet
    |>.rootedA0BlockHolomorphicTranslationData
      S.toSimultaneousTimeContinuationStageLevel OS
        S.hasCanonicalReducedCompactEdges
          (selectedSuccessorPacket (S.stageData k)).roots

/-- Choose the genuine original-OS rooted successor using the entire current
simultaneous predecessor level for its reflected block fields. -/
noncomputable def selectedStageLevelSuccessorDataOfOS
    (S : CanonicalGeneratorConvexAtlasStageLevelData OS)
    (k : ℕ) [NeZero k] :
    RootedGeneratorConvexAtlasSuccessorDataOfOS
      (S.stageData k)
      (selectedSuccessorPacket (S.stageData k)).packet
      (selectedStageLevelSuccessorHolomorphicData S k) :=
  Classical.choice
    (nonempty_rootedGeneratorConvexAtlasSuccessorDataOfOS
      (S.stageData k)
      (selectedSuccessorPacket (S.stageData k)).packet
      (selectedStageLevelSuccessorHolomorphicData S k)
      (selectedSuccessorAnchor_mem (S.stageData k)))

/-- Apply the original-OS rooted successor simultaneously at every positive
arity, retaining the canonical zero-gap predecessor unchanged. -/
noncomputable def advanceStageLevelOfOS
    (S : CanonicalGeneratorConvexAtlasStageLevelData OS) :
    CanonicalGeneratorConvexAtlasStageLevelData OS where
  stageData
    | 0 => S.stageData 0
    | k + 1 => (selectedStageLevelSuccessorDataOfOS S (k + 1)).next

@[simp] theorem advanceStageLevelOfOS_stageData_zero
    (S : CanonicalGeneratorConvexAtlasStageLevelData OS) :
    (advanceStageLevelOfOS S).stageData 0 = S.stageData 0 :=
  rfl

@[simp] theorem advanceStageLevelOfOS_stageData_succ
    (S : CanonicalGeneratorConvexAtlasStageLevelData OS)
    (k : ℕ) :
    (advanceStageLevelOfOS S).stageData (k + 1) =
      (selectedStageLevelSuccessorDataOfOS S (k + 1)).next :=
  rfl

/-- Select one verified rooted successor at positive arity from the current
simultaneous level.  Unlike `selectedSuccessorData`, this uses the current
level's reconstructed block fields rather than the initial specialization. -/
noncomputable def selectedStageLevelSuccessorData
    (S : CanonicalGeneratorConvexAtlasStageLevelData OS)
    (k : ℕ) [NeZero k]
    (lgc : OSLinearGrowthCondition d OS) :
    RootedGeneratorConvexAtlasSuccessorData
      (S.stageData k)
      (selectedSuccessorPacket (S.stageData k)).packet
      (selectedStageLevelSuccessorHolomorphicData S k)
      lgc :=
  Classical.choice
    (nonempty_rootedGeneratorConvexAtlasSuccessorData
      (S.stageData k)
      (selectedSuccessorPacket (S.stageData k)).packet
      (selectedStageLevelSuccessorHolomorphicData S k)
      lgc
      (selectedSuccessorAnchor_mem (S.stageData k)))

/-- Apply the rooted generator successor simultaneously at every positive
arity.  The canonical zero-gap stage is retained unchanged. -/
noncomputable def advanceStageLevel
    (S : CanonicalGeneratorConvexAtlasStageLevelData OS)
    (lgc : OSLinearGrowthCondition d OS) :
    CanonicalGeneratorConvexAtlasStageLevelData OS where
  stageData
    | 0 => S.stageData 0
    | k + 1 => (selectedStageLevelSuccessorData S (k + 1) lgc).next

@[simp] theorem advanceStageLevel_stageData_zero
    (S : CanonicalGeneratorConvexAtlasStageLevelData OS)
    (lgc : OSLinearGrowthCondition d OS) :
    (advanceStageLevel S lgc).stageData 0 = S.stageData 0 :=
  rfl

@[simp] theorem advanceStageLevel_stageData_succ
    (S : CanonicalGeneratorConvexAtlasStageLevelData OS)
    (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) :
    (advanceStageLevel S lgc).stageData (k + 1) =
      (selectedStageLevelSuccessorData S (k + 1) lgc).next :=
  rfl

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
