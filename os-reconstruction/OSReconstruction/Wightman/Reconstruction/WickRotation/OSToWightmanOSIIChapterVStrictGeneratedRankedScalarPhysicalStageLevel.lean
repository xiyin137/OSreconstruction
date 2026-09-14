/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVPointedStageLevel
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedScalarPhysicalSuccessor
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictScalarSeedCoefficientPhysicalSuccessor
















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d : Nat} [NeZero d]

/-- A ranked scalar-seed successor together with pointed convex-atlas
provenance at every positive arity. -/
structure StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData
    (current : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (depth rank : Nat) where
  seed :
    StrictGeneratedScalarRankSuccessorSeedStageLevelData
      current OS depth rank
  chart : Nat -> Type
  hub : forall q, Fin (q + 1) -> Real
  hub_positive :
    forall q,
      hub q ∈ section43TimeStrictPositiveRegion (q + 1)
  pointedAtlas :
    forall q,
      GeneratorStagePointedConvexAtlas
        (seed.next.stage (q + 1))
        (osiiPositiveRealTimeEmbed (hub q))
        (chart q)

/-- The exact simultaneous conclusion of scalar rank convexification. -/
structure StrictGeneratedScalarRankStageLevelSuccessorData
    (current : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (depth rank : Nat) where
  next : SimultaneousTimeContinuationStageLevel d
  carrier_subset :
    forall k,
      (current.stage k).carrier ⊆
        (next.stage k).carrier
  extendsOld :
    forall k,
      Set.EqOn
        (next.stage k).distribution
        (current.stage k).distribution
        (current.stage k).carrier
  canonicalEdges :
    next.HasCanonicalReducedCompactEdges OS
  scalarRankSuccessorCarrier_subset :
    forall k,
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            k (depth + 1) (rank + 1)) ⊆
        (next.stage k).carrier

namespace StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData

variable
  {current : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {depth rank : Nat}

/-- Fixed positive-arity input for ranked physical target gluing. -/
noncomputable def physicalPointedData
    (D :
      StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData
        current OS depth rank)
    (q : Nat) :
    LogarithmicTargetAmbientData.PhysicalPointedPredecessorData
      (rankSuccessorScalarLogarithmicTargetData
        (k := q + 1) D.seed) :=
  rankSuccessorScalarPhysicalPointedData
    D.seed (D.chart q) (D.hub q)
    (D.hub_positive q) (D.pointedAtlas q)

/-- Apply ranked physical convexification at every positive arity and retain
the seed predecessor at arity zero. -/
noncomputable def physicalSuccessorStage
    (D :
      StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData
        current OS depth rank)
    (k : Nat) :
    OSIITimeContinuationStage d k :=
  match k with
  | 0 => D.seed.next.stage 0
  | q + 1 => (D.physicalPointedData q).physicalSuccessorStage

@[simp] theorem physicalSuccessorStage_zero
    (D :
      StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData
        current OS depth rank) :
    D.physicalSuccessorStage 0 = D.seed.next.stage 0 :=
  rfl

@[simp] theorem physicalSuccessorStage_succ
    (D :
      StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData
        current OS depth rank)
    (q : Nat) :
    D.physicalSuccessorStage (q + 1) =
      (D.physicalPointedData q).physicalSuccessorStage :=
  rfl

/-- The simultaneous ranked physical successor. -/
noncomputable def physicalSuccessorStageLevel
    (D :
      StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData
        current OS depth rank) :
    SimultaneousTimeContinuationStageLevel d where
  stage := D.physicalSuccessorStage

/-- Every ranked seed-stage carrier is retained. -/
theorem seedStageCarrier_subset_physicalSuccessorStage
    (D :
      StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData
        current OS depth rank)
    (k : Nat) :
    (D.seed.next.stage k).carrier ⊆
      (D.physicalSuccessorStage k).carrier := by
  cases k with
  | zero =>
      exact Set.Subset.rfl
  | succ q =>
      exact
        (D.physicalPointedData q
          ).predecessorCarrier_subset_physicalSuccessorStage

/-- The physical successor agrees with the ranked seed stage on its complete
carrier. -/
theorem physicalSuccessorStage_extends_seedStage
    (D :
      StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData
        current OS depth rank)
    (k : Nat) :
    Set.EqOn
      (D.physicalSuccessorStage k).distribution
      (D.seed.next.stage k).distribution
      (D.seed.next.stage k).carrier := by
  cases k with
  | zero =>
      exact Set.eqOn_refl _ _
  | succ q =>
      exact
        (D.physicalPointedData q
          ).physicalSuccessorStage_extends_predecessor

/-- Canonical compact positive-real edges survive ranked physical
convexification. -/
theorem physicalSuccessorStageLevel_hasCanonicalReducedCompactEdges
    (D :
      StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData
        current OS depth rank) :
    D.physicalSuccessorStageLevel.HasCanonicalReducedCompactEdges OS := by
  intro k
  exact
    hasCanonicalReducedCompactStageEdges_of_eqOn_extension
      (D.seed.canonicalEdges k)
      (D.seedStageCarrier_subset_physicalSuccessorStage k)
      (D.physicalSuccessorStage_extends_seedStage k)

/-- Every positive-arity ranked physical successor remains star-convex about
its selected hub. -/
theorem physicalSuccessorStage_starConvex
    (D :
      StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData
        current OS depth rank)
    (q : Nat) :
    StarConvex Real
      (osiiPositiveRealTimeEmbed (D.hub q))
      (D.physicalSuccessorStage (q + 1)).carrier :=
  (D.physicalPointedData q).physicalSuccessorStage_starConvex

/-- Ranked physical convexification preserves the simultaneous pointed
convex-atlas invariant. -/
noncomputable def physicalSuccessorPointedStageLevel
    (D :
      StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData
        current OS depth rank) :
    CanonicalGeneratorPointedConvexAtlasStageLevelData OS where
  stageLevel := D.physicalSuccessorStageLevel
  canonicalEdges :=
    D.physicalSuccessorStageLevel_hasCanonicalReducedCompactEdges
  chart := fun q =>
    {z // z ∈ (D.physicalSuccessorStage (q + 1)).carrier}
  hub := D.hub
  hub_positive := D.hub_positive
  pointedAtlas := fun q =>
    GeneratorStagePointedConvexAtlas.ofOpenStarConvex
      (D.physicalSuccessorStage_starConvex q)

/-- The complete rank-`rank + 1` scalar physical carrier at target depth
`depth + 1` lies in the simultaneous successor at every arity. -/
theorem scalarRankSuccessorCarrier_subset_physicalSuccessorStage
    (D :
      StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData
        current OS depth rank)
    (k : Nat) :
    osiiTimeArgumentCarrier
        (osiiStrictGeneratedLogarithmicBaseAtRank
          k (depth + 1) (rank + 1)) ⊆
      (D.physicalSuccessorStage k).carrier := by
  cases k with
  | zero =>
      intro z hz
      change z ∈ (D.seed.next.stage 0).carrier
      have hpositive :
          (0 : Fin 0 -> Real) ∈
            section43TimeStrictPositiveRegion 0 := by
        intro i
        exact Fin.elim0 i
      have hzero :
          osiiPositiveRealTimeEmbed (0 : Fin 0 -> Real) ∈
            (D.seed.next.stage 0).carrier :=
        (D.seed.canonicalEdges 0).positiveReal_mem_carrier
          (0 : Fin 0 -> Real) hpositive
      have hz_eq :
          z =
            osiiPositiveRealTimeEmbed
              (0 : Fin 0 -> Real) :=
        Subsingleton.elim _ _
      rwa [hz_eq]
  | succ q =>
      exact
        (D.physicalPointedData q
          ).targetArgumentCarrier_subset_physicalSuccessorStage

/-- Package ranked seed realization followed by automatic physical scalar
convexification as one honest successor of the original stage level. -/
noncomputable def toStrictGeneratedScalarRankStageLevelSuccessorData
    (D :
      StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData
        current OS depth rank) :
    StrictGeneratedScalarRankStageLevelSuccessorData
      current OS depth rank where
  next := D.physicalSuccessorStageLevel
  carrier_subset := by
    intro k
    exact
      (D.seed.carrier_subset k).trans
        (D.seedStageCarrier_subset_physicalSuccessorStage k)
  extendsOld := by
    intro k z hz
    exact
      (D.physicalSuccessorStage_extends_seedStage k
        (D.seed.carrier_subset k hz)).trans
          (D.seed.extendsOld k hz)
  canonicalEdges :=
    D.physicalSuccessorStageLevel_hasCanonicalReducedCompactEdges
  scalarRankSuccessorCarrier_subset :=
    D.scalarRankSuccessorCarrier_subset_physicalSuccessorStage

end StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData

namespace CanonicalGeneratorPointedConvexAtlasStageLevelData

variable
  {OS : OsterwalderSchraderAxioms d}
  (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
  (depth rank : Nat)
  (P :
    StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) D depth rank)
  (Q :
    StageWideStrictGeneratedTargetDepthScalarRankData
      (OS := OS) D depth rank)
  (lgc : OSLinearGrowthCondition d OS)

/-- The concrete ranked generator/tail seed stage with its retained pointed
atlas, ready for automatic physical scalar convexification. -/
noncomputable def scalarRankSuccessorSeedPointedData :
    StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData
      D.stageLevel
      OS depth rank where
  seed :=
    D.toStrictGeneratedScalarRankSuccessorSeedStageLevelData
      depth rank P Q lgc
  chart :=
    (D.scalarRankSuccessorSeedPointedNext
      depth rank P Q lgc).chart
  hub :=
    (D.scalarRankSuccessorSeedPointedNext
      depth rank P Q lgc).hub
  hub_positive :=
    (D.scalarRankSuccessorSeedPointedNext
      depth rank P Q lgc).hub_positive
  pointedAtlas := by
    intro q
    exact
      (D.scalarRankSuccessorSeedPointedNext
        depth rank P Q lgc).pointedAtlas q

/-- The concrete rank successor with the pointed convex-atlas invariant
retained for subsequent target-and-hub continuation. -/
noncomputable def scalarRankSuccessorPhysicalPointedNext :
    CanonicalGeneratorPointedConvexAtlasStageLevelData OS :=
  (D.scalarRankSuccessorSeedPointedData
    depth rank P Q lgc).physicalSuccessorPointedStageLevel

/-- Complete concrete scalar rank closure from the original simultaneous
stage. -/
noncomputable def toStrictGeneratedScalarRankStageLevelSuccessorData :
    StrictGeneratedScalarRankStageLevelSuccessorData
      D.stageLevel
      OS depth rank :=
  (D.scalarRankSuccessorSeedPointedData
    depth rank P Q lgc
    ).toStrictGeneratedScalarRankStageLevelSuccessorData

/-- The complete original-OS generator and mixed-tail seed stage with its
retained pointed atlas, ready for physical scalar convexification. -/
noncomputable def scalarRankSuccessorSeedPointedDataOfOS :
    StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData
      D.stageLevel
      OS depth rank where
  seed :=
    D.toStrictGeneratedScalarRankSuccessorSeedStageLevelDataOfOS
      depth rank P Q
  chart :=
    (D.scalarRankSuccessorSeedPointedNextOfOS
      depth rank P Q).chart
  hub :=
    (D.scalarRankSuccessorSeedPointedNextOfOS
      depth rank P Q).hub
  hub_positive :=
    (D.scalarRankSuccessorSeedPointedNextOfOS
      depth rank P Q).hub_positive
  pointedAtlas := by
    intro q
    exact
      (D.scalarRankSuccessorSeedPointedNextOfOS
        depth rank P Q).pointedAtlas q

/-- The original-OS strict-rank scalar successor, retaining the pointed
convex-atlas invariant needed for subsequent ranks and depths. -/
noncomputable def scalarRankSuccessorPhysicalPointedNextOfOS :
    CanonicalGeneratorPointedConvexAtlasStageLevelData OS :=
  (D.scalarRankSuccessorSeedPointedDataOfOS
    depth rank P Q).physicalSuccessorPointedStageLevel

/-- Complete source-compatible strict-rank physical scalar closure at any
depth and rank under the original OS axioms alone. -/
noncomputable def toStrictGeneratedScalarRankStageLevelSuccessorDataOfOS :
    StrictGeneratedScalarRankStageLevelSuccessorData
      D.stageLevel
      OS depth rank :=
  (D.scalarRankSuccessorSeedPointedDataOfOS
    depth rank P Q
    ).toStrictGeneratedScalarRankStageLevelSuccessorData

end CanonicalGeneratorPointedConvexAtlasStageLevelData

end OSIIChapterV
end OSReconstruction
