/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedScalarPhysicalStageLevel
















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

/-- The nested-induction invariant at one target analytic rank. -/
structure StrictGeneratedScalarRankPointedInductionData
    (OS : OsterwalderSchraderAxioms d)
    (depth rank : Nat) where
  pointed : CanonicalGeneratorPointedConvexAtlasStageLevelData OS
  sourceStrictGeneratedCarrier_subset :
    forall arity,
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
        (pointed.stageLevel.stage arity).carrier
  targetRankCarrier_subset :
    forall arity,
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            arity (depth + 1) rank) ⊆
        (pointed.stageLevel.stage arity).carrier

namespace StrictGeneratedScalarRankPointedInductionData

variable {depth rank : Nat}

/-- The outer source-depth realization supplies every finite-rank scalar
input needed by reflected-Gram reconstruction. -/
noncomputable def sourceReflectedGramRankData
    (D : StrictGeneratedScalarRankPointedInductionData OS depth rank) :
    StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) D.pointed depth rank :=
  StageWideStrictGeneratedMixedReflectedGramRankData.ofStrictGeneratedAtRank
    D.pointed depth rank
    (fun arity _z hz =>
      D.sourceStrictGeneratedCarrier_subset arity
        ⟨hz.1, hz.2.toStrictGenerated⟩)

/-- The inner induction hypothesis in the exact input form consumed by the
ranked scalar successor. -/
def targetDepthScalarRankData
    (D : StrictGeneratedScalarRankPointedInductionData OS depth rank) :
    StageWideStrictGeneratedTargetDepthScalarRankData
      (OS := OS) D.pointed depth rank where
  scalarStrictGeneratedAtTargetDepth :=
    D.targetRankCarrier_subset

/-- One complete pointed analytic-rank step. -/
noncomputable def next
    (D : StrictGeneratedScalarRankPointedInductionData OS depth rank)
    (lgc : OSLinearGrowthCondition d OS) :
    StrictGeneratedScalarRankPointedInductionData
      OS depth (rank + 1) := by
  let P := D.sourceReflectedGramRankData
  let Q := D.targetDepthScalarRankData
  let nextPointed :=
    D.pointed.scalarRankSuccessorPhysicalPointedNext
      depth rank P Q lgc
  let successor :=
    D.pointed.toStrictGeneratedScalarRankStageLevelSuccessorData
      depth rank P Q lgc
  exact
    {
      pointed := nextPointed
      sourceStrictGeneratedCarrier_subset := by
        intro arity
        exact
          (D.sourceStrictGeneratedCarrier_subset arity).trans
            (by
              simpa [nextPointed, successor,
                CanonicalGeneratorPointedConvexAtlasStageLevelData.scalarRankSuccessorPhysicalPointedNext,
                CanonicalGeneratorPointedConvexAtlasStageLevelData.toStrictGeneratedScalarRankStageLevelSuccessorData,
                StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData.physicalSuccessorPointedStageLevel,
                StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData.toStrictGeneratedScalarRankStageLevelSuccessorData] using
                successor.carrier_subset arity)
      targetRankCarrier_subset := by
        intro arity
        simpa [nextPointed, successor,
          CanonicalGeneratorPointedConvexAtlasStageLevelData.scalarRankSuccessorPhysicalPointedNext,
          CanonicalGeneratorPointedConvexAtlasStageLevelData.toStrictGeneratedScalarRankStageLevelSuccessorData,
          StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData.physicalSuccessorPointedStageLevel,
          StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData.toStrictGeneratedScalarRankStageLevelSuccessorData] using
          successor.scalarRankSuccessorCarrier_subset arity
    }

/-- A rank step retains every predecessor carrier. -/
theorem carrier_subset_next
    (D : StrictGeneratedScalarRankPointedInductionData OS depth rank)
    (lgc : OSLinearGrowthCondition d OS)
    (arity : Nat) :
    (D.pointed.stageLevel.stage arity).carrier ⊆
      ((D.next lgc).pointed.stageLevel.stage arity).carrier := by
  let P := D.sourceReflectedGramRankData
  let Q := D.targetDepthScalarRankData
  simpa [next, P, Q,
    CanonicalGeneratorPointedConvexAtlasStageLevelData.scalarRankSuccessorPhysicalPointedNext,
    CanonicalGeneratorPointedConvexAtlasStageLevelData.toStrictGeneratedScalarRankStageLevelSuccessorData,
    StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData.physicalSuccessorPointedStageLevel,
    StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData.toStrictGeneratedScalarRankStageLevelSuccessorData] using
    (D.pointed.toStrictGeneratedScalarRankStageLevelSuccessorData
      depth rank P Q lgc).carrier_subset arity

/-- A rank step agrees with its predecessor on the complete predecessor
carrier. -/
theorem next_extends
    (D : StrictGeneratedScalarRankPointedInductionData OS depth rank)
    (lgc : OSLinearGrowthCondition d OS)
    (arity : Nat) :
    Set.EqOn
      ((D.next lgc).pointed.stageLevel.stage arity).distribution
      (D.pointed.stageLevel.stage arity).distribution
      (D.pointed.stageLevel.stage arity).carrier := by
  let P := D.sourceReflectedGramRankData
  let Q := D.targetDepthScalarRankData
  simpa [next, P, Q,
    CanonicalGeneratorPointedConvexAtlasStageLevelData.scalarRankSuccessorPhysicalPointedNext,
    CanonicalGeneratorPointedConvexAtlasStageLevelData.toStrictGeneratedScalarRankStageLevelSuccessorData,
    StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData.physicalSuccessorPointedStageLevel,
    StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData.toStrictGeneratedScalarRankStageLevelSuccessorData] using
    (D.pointed.toStrictGeneratedScalarRankStageLevelSuccessorData
      depth rank P Q lgc).extendsOld arity

/-- The next scalar rank stage agrees with the complete rooted
generator-insertion stage on that stage's carrier. -/
theorem next_extends_rootedInsertion
    (D : StrictGeneratedScalarRankPointedInductionData OS depth rank)
    (lgc : OSLinearGrowthCondition d OS)
    (arity : Nat) :
    Set.EqOn
      ((D.next lgc).pointed.stageLevel.stage arity).distribution
      ((D.pointed.rootedInsertionRankStageLevel
        depth rank D.sourceReflectedGramRankData lgc).stage arity).distribution
      ((D.pointed.rootedInsertionRankStageLevel
        depth rank D.sourceReflectedGramRankData lgc).stage arity).carrier := by
  let S := D.pointed
  let P := D.sourceReflectedGramRankData
  let Q := D.targetDepthScalarRankData
  let I := S.rootedInsertionRankNext depth rank P lgc
  let V := S.rootedInsertionTargetDepthReflectedScalarRankInput
    depth rank P Q lgc
  let A := S.scalarRankSuccessorSeedPointedData depth rank P Q lgc
  intro z hz
  have hseed : z ∈ (A.seed.next.stage arity).carrier := by
    exact I.oldCarrier_subset_vacuumTailProjectionRankStageLevel V arity hz
  have hphysical :
      (A.physicalSuccessorStage arity).distribution z =
        (I.stageLevel.stage arity).distribution z :=
    (A.physicalSuccessorStage_extends_seedStage arity hseed).trans
      (I.vacuumTailProjectionRankStageLevel_extends V arity hz)
  simpa [S, P, Q, I, V, A, next,
    CanonicalGeneratorPointedConvexAtlasStageLevelData.scalarRankSuccessorPhysicalPointedNext,
    StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData.physicalSuccessorPointedStageLevel,
    StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData.physicalSuccessorStageLevel,
    CanonicalGeneratorPointedConvexAtlasStageLevelData.rootedInsertionRankNext,
    CanonicalGeneratorPointedConvexAtlasStageLevelData.rootedInsertionRankStageLevel]
    using hphysical

/-- The ranked successor preserves the chosen hubs exactly. -/
@[simp] theorem next_hub
    (D : StrictGeneratedScalarRankPointedInductionData OS depth rank)
    (lgc : OSLinearGrowthCondition d OS) :
    (D.next lgc).pointed.hub = D.pointed.hub := by
  rfl

/-- One complete source-compatible physical rank step under the original
OS axioms, including its genuine same-depth vacuum-tail seeds. -/
noncomputable def nextOfOS
    (D : StrictGeneratedScalarRankPointedInductionData OS depth rank) :
    StrictGeneratedScalarRankPointedInductionData
      OS depth (rank + 1) := by
  let P := D.sourceReflectedGramRankData
  let Q := D.targetDepthScalarRankData
  let nextPointed :=
    D.pointed.scalarRankSuccessorPhysicalPointedNextOfOS
      depth rank P Q
  let successor :=
    D.pointed.toStrictGeneratedScalarRankStageLevelSuccessorDataOfOS
      depth rank P Q
  exact
    {
      pointed := nextPointed
      sourceStrictGeneratedCarrier_subset := by
        intro arity
        exact
          (D.sourceStrictGeneratedCarrier_subset arity).trans
            (by
              simpa [nextPointed, successor,
                CanonicalGeneratorPointedConvexAtlasStageLevelData.scalarRankSuccessorPhysicalPointedNextOfOS,
                CanonicalGeneratorPointedConvexAtlasStageLevelData.toStrictGeneratedScalarRankStageLevelSuccessorDataOfOS,
                StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData.physicalSuccessorPointedStageLevel,
                StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData.toStrictGeneratedScalarRankStageLevelSuccessorData] using
                successor.carrier_subset arity)
      targetRankCarrier_subset := by
        intro arity
        simpa [nextPointed, successor,
          CanonicalGeneratorPointedConvexAtlasStageLevelData.scalarRankSuccessorPhysicalPointedNextOfOS,
          CanonicalGeneratorPointedConvexAtlasStageLevelData.toStrictGeneratedScalarRankStageLevelSuccessorDataOfOS,
          StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData.physicalSuccessorPointedStageLevel,
          StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData.toStrictGeneratedScalarRankStageLevelSuccessorData] using
          successor.scalarRankSuccessorCarrier_subset arity
    }

/-- The original-OS rank step retains its complete predecessor carrier. -/
theorem carrier_subset_nextOfOS
    (D : StrictGeneratedScalarRankPointedInductionData OS depth rank)
    (arity : Nat) :
    (D.pointed.stageLevel.stage arity).carrier ⊆
      (D.nextOfOS.pointed.stageLevel.stage arity).carrier := by
  let P := D.sourceReflectedGramRankData
  let Q := D.targetDepthScalarRankData
  simpa [nextOfOS, P, Q,
    CanonicalGeneratorPointedConvexAtlasStageLevelData.scalarRankSuccessorPhysicalPointedNextOfOS,
    CanonicalGeneratorPointedConvexAtlasStageLevelData.toStrictGeneratedScalarRankStageLevelSuccessorDataOfOS,
    StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData.physicalSuccessorPointedStageLevel,
    StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData.toStrictGeneratedScalarRankStageLevelSuccessorData] using
    (D.pointed.toStrictGeneratedScalarRankStageLevelSuccessorDataOfOS
      depth rank P Q).carrier_subset arity

/-- The original-OS rank step agrees on the whole predecessor carrier. -/
theorem nextOfOS_extends
    (D : StrictGeneratedScalarRankPointedInductionData OS depth rank)
    (arity : Nat) :
    Set.EqOn
      (D.nextOfOS.pointed.stageLevel.stage arity).distribution
      (D.pointed.stageLevel.stage arity).distribution
      (D.pointed.stageLevel.stage arity).carrier := by
  let P := D.sourceReflectedGramRankData
  let Q := D.targetDepthScalarRankData
  simpa [nextOfOS, P, Q,
    CanonicalGeneratorPointedConvexAtlasStageLevelData.scalarRankSuccessorPhysicalPointedNextOfOS,
    CanonicalGeneratorPointedConvexAtlasStageLevelData.toStrictGeneratedScalarRankStageLevelSuccessorDataOfOS,
    StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData.physicalSuccessorPointedStageLevel,
    StrictGeneratedScalarRankSuccessorSeedPointedStageLevelData.toStrictGeneratedScalarRankStageLevelSuccessorData] using
    (D.pointed.toStrictGeneratedScalarRankStageLevelSuccessorDataOfOS
      depth rank P Q).extendsOld arity

/-- The qualitative original-OS rank step preserves its pointed hub. -/
@[simp] theorem nextOfOS_hub
    (D : StrictGeneratedScalarRankPointedInductionData OS depth rank) :
    D.nextOfOS.pointed.hub = D.pointed.hub :=
  rfl

end StrictGeneratedScalarRankPointedInductionData

namespace CanonicalGeneratorPointedConvexAtlasStageLevelData

/-- Canonical compact real edges initialize target-depth scalar rank zero:
that rank is exactly the zero argument, hence its physical carrier is the
strict-positive real orthant. -/
theorem scalarRankZeroCarrier_subset
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth arity : Nat) :
    osiiTimeArgumentCarrier
        (osiiStrictGeneratedLogarithmicBaseAtRank
          arity (depth + 1) 0) ⊆
      (D.stageLevel.stage arity).carrier := by
  intro z hz
  have harg :
      osiiTimeArgumentVector z = (0 : Fin arity -> Real) :=
    OSIIStrictGeneratedLogarithmicArgumentAtRank.scalar_eq_zero_of_rank_zero
      hz.2
  have hreal : forall i, 0 < (z i).re := hz.1
  have him : forall i, (z i).im = 0 := by
    intro i
    exact
      (Complex.arg_eq_zero_iff.mp
        (congrFun harg i)).2
  let tau : Fin arity -> Real := fun i => (z i).re
  have htau :
      tau ∈ section43TimeStrictPositiveRegion arity :=
    hreal
  have hz_real :
      z = osiiPositiveRealTimeEmbed tau := by
    funext i
    apply Complex.ext
    · rfl
    · simpa [tau, osiiPositiveRealTimeEmbed] using him i
  rw [hz_real]
  exact
    (D.canonicalEdges arity).positiveReal_mem_carrier tau htau

/-- Start the inner target-rank induction from any pointed source stage that
realizes the complete strict generated scalar carrier at the source depth. -/
noncomputable def scalarRankInductionZero
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier) :
    StrictGeneratedScalarRankPointedInductionData OS depth 0 where
  pointed := D
  sourceStrictGeneratedCarrier_subset :=
    sourceStrictGeneratedCarrier_subset
  targetRankCarrier_subset :=
    D.scalarRankZeroCarrier_subset depth

/-- The complete recursively constructed pointed stage at one finite target
rank. -/
noncomputable def scalarRankInduction
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (lgc : OSLinearGrowthCondition d OS) :
    (rank : Nat) ->
      StrictGeneratedScalarRankPointedInductionData OS depth rank
  | 0 =>
      D.scalarRankInductionZero
        depth sourceStrictGeneratedCarrier_subset
  | rank + 1 =>
      (D.scalarRankInduction
        depth sourceStrictGeneratedCarrier_subset lgc rank).next lgc

@[simp] theorem scalarRankInduction_zero
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (lgc : OSLinearGrowthCondition d OS) :
    D.scalarRankInduction
        depth sourceStrictGeneratedCarrier_subset lgc 0 =
      D.scalarRankInductionZero
        depth sourceStrictGeneratedCarrier_subset :=
  rfl

@[simp] theorem scalarRankInduction_succ
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (lgc : OSLinearGrowthCondition d OS)
    (rank : Nat) :
    D.scalarRankInduction
        depth sourceStrictGeneratedCarrier_subset lgc (rank + 1) =
      (D.scalarRankInduction
        depth sourceStrictGeneratedCarrier_subset lgc rank).next lgc :=
  rfl

theorem scalarRankInduction_carrier_subset_succ
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (lgc : OSLinearGrowthCondition d OS)
    (rank arity : Nat) :
    ((D.scalarRankInduction
      depth sourceStrictGeneratedCarrier_subset lgc rank
      ).pointed.stageLevel.stage arity).carrier ⊆
      ((D.scalarRankInduction
        depth sourceStrictGeneratedCarrier_subset lgc (rank + 1)
        ).pointed.stageLevel.stage arity).carrier := by
  rw [D.scalarRankInduction_succ
    depth sourceStrictGeneratedCarrier_subset lgc rank]
  exact
    (D.scalarRankInduction
      depth sourceStrictGeneratedCarrier_subset lgc rank
      ).carrier_subset_next lgc arity

theorem scalarRankInduction_extends_succ
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (lgc : OSLinearGrowthCondition d OS)
    (rank arity : Nat) :
    Set.EqOn
      ((D.scalarRankInduction
        depth sourceStrictGeneratedCarrier_subset lgc (rank + 1)
        ).pointed.stageLevel.stage arity).distribution
      ((D.scalarRankInduction
        depth sourceStrictGeneratedCarrier_subset lgc rank
        ).pointed.stageLevel.stage arity).distribution
      ((D.scalarRankInduction
        depth sourceStrictGeneratedCarrier_subset lgc rank
        ).pointed.stageLevel.stage arity).carrier := by
  rw [D.scalarRankInduction_succ
    depth sourceStrictGeneratedCarrier_subset lgc rank]
  exact
    (D.scalarRankInduction
      depth sourceStrictGeneratedCarrier_subset lgc rank
      ).next_extends lgc arity

theorem scalarRankInduction_carrier_mono
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (lgc : OSLinearGrowthCondition d OS)
    (arity : Nat) :
    Monotone fun rank =>
      ((D.scalarRankInduction
        depth sourceStrictGeneratedCarrier_subset lgc rank
        ).pointed.stageLevel.stage arity).carrier := by
  intro rank rank' hrank
  induction rank', hrank using Nat.le_induction with
  | base =>
      exact Set.Subset.rfl
  | succ rank' hrank ih =>
      exact
        ih.trans
          (D.scalarRankInduction_carrier_subset_succ
            depth sourceStrictGeneratedCarrier_subset
            lgc rank' arity)

theorem scalarRankInduction_distribution_eq_of_le
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (lgc : OSLinearGrowthCondition d OS)
    {rank rank' arity : Nat}
    (hrank : rank <= rank')
    {z : OSIITimeGapSpace arity}
    (hz :
      z ∈ ((D.scalarRankInduction
        depth sourceStrictGeneratedCarrier_subset lgc rank
        ).pointed.stageLevel.stage arity).carrier) :
    ((D.scalarRankInduction
      depth sourceStrictGeneratedCarrier_subset lgc rank'
      ).pointed.stageLevel.stage arity).distribution z =
      ((D.scalarRankInduction
        depth sourceStrictGeneratedCarrier_subset lgc rank
        ).pointed.stageLevel.stage arity).distribution z := by
  induction rank', hrank using Nat.le_induction with
  | base =>
      rfl
  | succ rank' hrank ih =>
      calc
        ((D.scalarRankInduction
          depth sourceStrictGeneratedCarrier_subset lgc (rank' + 1)
          ).pointed.stageLevel.stage arity).distribution z =
            ((D.scalarRankInduction
              depth sourceStrictGeneratedCarrier_subset lgc rank'
              ).pointed.stageLevel.stage arity).distribution z :=
          D.scalarRankInduction_extends_succ
            depth sourceStrictGeneratedCarrier_subset lgc rank' arity
            (D.scalarRankInduction_carrier_mono
              depth sourceStrictGeneratedCarrier_subset lgc arity
              hrank hz)
        _ =
            ((D.scalarRankInduction
              depth sourceStrictGeneratedCarrier_subset lgc rank
              ).pointed.stageLevel.stage arity).distribution z :=
          ih

theorem scalarRankInduction_pairwise_compatible
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (lgc : OSLinearGrowthCondition d OS)
    (arity rank rank' : Nat) :
    Set.EqOn
      ((D.scalarRankInduction
        depth sourceStrictGeneratedCarrier_subset lgc rank
        ).pointed.stageLevel.stage arity).distribution
      ((D.scalarRankInduction
        depth sourceStrictGeneratedCarrier_subset lgc rank'
        ).pointed.stageLevel.stage arity).distribution
      (((D.scalarRankInduction
          depth sourceStrictGeneratedCarrier_subset lgc rank
          ).pointed.stageLevel.stage arity).carrier ∩
        ((D.scalarRankInduction
          depth sourceStrictGeneratedCarrier_subset lgc rank'
          ).pointed.stageLevel.stage arity).carrier) := by
  intro z hz
  rcases le_total rank rank' with hrank | hrank
  · exact
      (D.scalarRankInduction_distribution_eq_of_le
        depth sourceStrictGeneratedCarrier_subset lgc
        hrank hz.1).symm
  · exact
      D.scalarRankInduction_distribution_eq_of_le
        depth sourceStrictGeneratedCarrier_subset lgc
        hrank hz.2

@[simp] theorem scalarRankInduction_hub
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (lgc : OSLinearGrowthCondition d OS)
    (rank : Nat) :
    (D.scalarRankInduction
      depth sourceStrictGeneratedCarrier_subset lgc rank
      ).pointed.hub = D.hub := by
  induction rank with
  | zero =>
      rfl
  | succ rank ih =>
      rw [D.scalarRankInduction_succ
        depth sourceStrictGeneratedCarrier_subset lgc rank,
        StrictGeneratedScalarRankPointedInductionData.next_hub,
        ih]

/-- Glue all target analytic ranks at one arity. -/
noncomputable def scalarRankUnionStage
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (lgc : OSLinearGrowthCondition d OS)
    (arity : Nat) :
    OSIITimeContinuationStage d arity where
  carrier :=
    ⋃ rank,
      ((D.scalarRankInduction
        depth sourceStrictGeneratedCarrier_subset lgc rank
        ).pointed.stageLevel.stage arity).carrier
  carrier_open :=
    isOpen_iUnion fun rank =>
      ((D.scalarRankInduction
        depth sourceStrictGeneratedCarrier_subset lgc rank
        ).pointed.stageLevel.stage arity).carrier_open
  distribution :=
    SCV.glued_iUnion
      (fun rank =>
        ((D.scalarRankInduction
          depth sourceStrictGeneratedCarrier_subset lgc rank
          ).pointed.stageLevel.stage arity).carrier)
      (fun rank =>
        ((D.scalarRankInduction
          depth sourceStrictGeneratedCarrier_subset lgc rank
          ).pointed.stageLevel.stage arity).distribution)
  weaklyHolomorphic := by
    intro chi
    let scalarDistribution :
        Nat -> OSIITimeGapSpace arity -> Complex :=
      fun rank z =>
        ((D.scalarRankInduction
          depth sourceStrictGeneratedCarrier_subset lgc rank
          ).pointed.stageLevel.stage arity).distribution z chi
    have hEq :
        forall rank rank',
          Set.EqOn
            (scalarDistribution rank)
            (scalarDistribution rank')
            (((D.scalarRankInduction
                depth sourceStrictGeneratedCarrier_subset lgc rank
                ).pointed.stageLevel.stage arity).carrier ∩
              ((D.scalarRankInduction
                depth sourceStrictGeneratedCarrier_subset lgc rank'
                ).pointed.stageLevel.stage arity).carrier) := by
      intro rank rank' z hz
      exact congrArg
        (fun T : OSIISpatialDistribution d arity => T chi)
        (D.scalarRankInduction_pairwise_compatible
          depth sourceStrictGeneratedCarrier_subset
          lgc arity rank rank' hz)
    have hglue :
        (fun z =>
          (SCV.glued_iUnion
            (fun rank =>
              ((D.scalarRankInduction
                depth sourceStrictGeneratedCarrier_subset lgc rank
                ).pointed.stageLevel.stage arity).carrier)
            (fun rank =>
              ((D.scalarRankInduction
                depth sourceStrictGeneratedCarrier_subset lgc rank
                ).pointed.stageLevel.stage arity).distribution)
            z) chi) =
          SCV.glued_iUnion
            (fun rank =>
              ((D.scalarRankInduction
                depth sourceStrictGeneratedCarrier_subset lgc rank
                ).pointed.stageLevel.stage arity).carrier)
            scalarDistribution := by
      funext z
      classical
      simp only [SCV.glued_iUnion, scalarDistribution]
      split_ifs <;> rfl
    rw [hglue]
    exact
      SCV.differentiableOn_glued_iUnion
        Set.Subset.rfl
        (fun rank =>
          ((D.scalarRankInduction
            depth sourceStrictGeneratedCarrier_subset lgc rank
            ).pointed.stageLevel.stage arity).carrier_open)
        (fun rank =>
          ((D.scalarRankInduction
            depth sourceStrictGeneratedCarrier_subset lgc rank
            ).pointed.stageLevel.stage arity).weaklyHolomorphic chi)
        hEq

theorem scalarRankStageCarrier_subset_union
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (lgc : OSLinearGrowthCondition d OS)
    (rank arity : Nat) :
    ((D.scalarRankInduction
      depth sourceStrictGeneratedCarrier_subset lgc rank
      ).pointed.stageLevel.stage arity).carrier ⊆
      (D.scalarRankUnionStage
        depth sourceStrictGeneratedCarrier_subset lgc arity).carrier := by
  intro z hz
  exact Set.mem_iUnion_of_mem rank hz

theorem scalarRankUnionStage_extends_rank
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (lgc : OSLinearGrowthCondition d OS)
    (rank arity : Nat) :
    Set.EqOn
      (D.scalarRankUnionStage
        depth sourceStrictGeneratedCarrier_subset lgc arity).distribution
      ((D.scalarRankInduction
        depth sourceStrictGeneratedCarrier_subset lgc rank
        ).pointed.stageLevel.stage arity).distribution
      ((D.scalarRankInduction
        depth sourceStrictGeneratedCarrier_subset lgc rank
        ).pointed.stageLevel.stage arity).carrier := by
  exact
    SCV.glued_iUnion_eqOn
      (D.scalarRankInduction_pairwise_compatible
        depth sourceStrictGeneratedCarrier_subset lgc arity)
      rank

/-- The rank union realizes the complete strict generated scalar carrier at
target depth. -/
theorem strictGeneratedTargetCarrier_subset_scalarRankUnionStage
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (lgc : OSLinearGrowthCondition d OS)
    (arity : Nat) :
    osiiTimeArgumentCarrier
        (osiiStrictGeneratedLogarithmicBase arity (depth + 1)) ⊆
      (D.scalarRankUnionStage
        depth sourceStrictGeneratedCarrier_subset lgc arity).carrier := by
  intro z hz
  obtain ⟨rank, hrank⟩ :=
    mem_strictGeneratedScalarBase_iff_exists_rank.mp hz.2
  exact
    D.scalarRankStageCarrier_subset_union
      depth sourceStrictGeneratedCarrier_subset lgc rank arity
      ((D.scalarRankInduction
        depth sourceStrictGeneratedCarrier_subset lgc rank
        ).targetRankCarrier_subset arity ⟨hz.1, hrank⟩)

/-- Simultaneous union over all finite target ranks. -/
noncomputable def scalarRankUnionStageLevel
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (lgc : OSLinearGrowthCondition d OS) :
    SimultaneousTimeContinuationStageLevel d where
  stage :=
    D.scalarRankUnionStage
      depth sourceStrictGeneratedCarrier_subset lgc

/-- The all-rank union retains every original source stage and agrees with it
on its complete carrier. -/
theorem scalarRankUnionStageLevel_extends
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (lgc : OSLinearGrowthCondition d OS)
    (arity : Nat) :
    Set.EqOn
      ((D.scalarRankUnionStageLevel
        depth sourceStrictGeneratedCarrier_subset lgc
        ).stage arity).distribution
      (D.stageLevel.stage arity).distribution
      (D.stageLevel.stage arity).carrier := by
  simpa [scalarRankUnionStageLevel, scalarRankInductionZero] using
    D.scalarRankUnionStage_extends_rank
      depth sourceStrictGeneratedCarrier_subset lgc 0 arity

theorem oldCarrier_subset_scalarRankUnionStageLevel
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (lgc : OSLinearGrowthCondition d OS)
    (arity : Nat) :
    (D.stageLevel.stage arity).carrier ⊆
      ((D.scalarRankUnionStageLevel
        depth sourceStrictGeneratedCarrier_subset lgc
        ).stage arity).carrier := by
  simpa [scalarRankUnionStageLevel, scalarRankInductionZero] using
    D.scalarRankStageCarrier_subset_union
      depth sourceStrictGeneratedCarrier_subset lgc 0 arity

/-- Canonical compact positive-real edges pass to the all-rank union through
its exact extension of the rank-zero stage. -/
theorem scalarRankUnionStageLevel_hasCanonicalEdges
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (lgc : OSLinearGrowthCondition d OS) :
    (D.scalarRankUnionStageLevel
      depth sourceStrictGeneratedCarrier_subset lgc
      ).HasCanonicalReducedCompactEdges OS := by
  intro arity
  exact
    hasCanonicalReducedCompactStageEdges_of_eqOn_extension
      (D.canonicalEdges arity)
      (D.oldCarrier_subset_scalarRankUnionStageLevel
        depth sourceStrictGeneratedCarrier_subset lgc arity)
      (D.scalarRankUnionStageLevel_extends
        depth sourceStrictGeneratedCarrier_subset lgc arity)

/-- Every finite rank is star-convex about the original source hub. -/
theorem scalarRankInduction_stage_starConvex
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (lgc : OSLinearGrowthCondition d OS)
    (rank q : Nat) :
    StarConvex Real
      (osiiPositiveRealTimeEmbed (D.hub q))
      ((D.scalarRankInduction
        depth sourceStrictGeneratedCarrier_subset lgc rank
        ).pointed.stageLevel.stage (q + 1)).carrier := by
  simpa [D.scalarRankInduction_hub
    depth sourceStrictGeneratedCarrier_subset lgc rank] using
    ((D.scalarRankInduction
      depth sourceStrictGeneratedCarrier_subset lgc rank
      ).pointed.pointedAtlas q).carrier_starConvex

/-- The all-rank carrier is star-convex about the fixed source hub. -/
theorem scalarRankUnionStage_starConvex
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (lgc : OSLinearGrowthCondition d OS)
    (q : Nat) :
    StarConvex Real
      (osiiPositiveRealTimeEmbed (D.hub q))
      ((D.scalarRankUnionStageLevel
        depth sourceStrictGeneratedCarrier_subset lgc
        ).stage (q + 1)).carrier := by
  apply starConvex_iUnion
  intro rank
  exact
    D.scalarRankInduction_stage_starConvex
      depth sourceStrictGeneratedCarrier_subset lgc rank q

/-- The complete target-depth rank union, retaining the fixed pointed
invariant needed for the next outer depth. -/
noncomputable def scalarRankUnionPointedNext
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (lgc : OSLinearGrowthCondition d OS) :
    CanonicalGeneratorPointedConvexAtlasStageLevelData OS where
  stageLevel :=
    D.scalarRankUnionStageLevel
      depth sourceStrictGeneratedCarrier_subset lgc
  canonicalEdges :=
    D.scalarRankUnionStageLevel_hasCanonicalEdges
      depth sourceStrictGeneratedCarrier_subset lgc
  chart := fun q =>
    {z //
      z ∈ ((D.scalarRankUnionStageLevel
        depth sourceStrictGeneratedCarrier_subset lgc
        ).stage (q + 1)).carrier}
  hub := D.hub
  hub_positive := D.hub_positive
  pointedAtlas := fun q =>
    GeneratorStagePointedConvexAtlas.ofOpenStarConvex
      (D.scalarRankUnionStage_starConvex
        depth sourceStrictGeneratedCarrier_subset lgc q)

theorem strictGeneratedTargetCarrier_subset_scalarRankUnionPointedNext
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (lgc : OSLinearGrowthCondition d OS)
    (arity : Nat) :
    osiiTimeArgumentCarrier
        (osiiStrictGeneratedLogarithmicBase arity (depth + 1)) ⊆
      ((D.scalarRankUnionPointedNext
        depth sourceStrictGeneratedCarrier_subset lgc
        ).stageLevel.stage arity).carrier :=
  D.strictGeneratedTargetCarrier_subset_scalarRankUnionStage
    depth sourceStrictGeneratedCarrier_subset lgc arity

/-- The finite analytic-rank induction needs no growth information once its
generator and vacuum-tail successors use their genuine source edges. -/
noncomputable def scalarRankInductionOfOS
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier) :
    (rank : Nat) ->
      StrictGeneratedScalarRankPointedInductionData OS depth rank
  | 0 =>
      D.scalarRankInductionZero
        depth sourceStrictGeneratedCarrier_subset
  | rank + 1 =>
      (D.scalarRankInductionOfOS
        depth sourceStrictGeneratedCarrier_subset rank).nextOfOS

@[simp] theorem scalarRankInductionOfOS_zero
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier) :
    D.scalarRankInductionOfOS
        depth sourceStrictGeneratedCarrier_subset 0 =
      D.scalarRankInductionZero
        depth sourceStrictGeneratedCarrier_subset :=
  rfl

@[simp] theorem scalarRankInductionOfOS_succ
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (rank : Nat) :
    D.scalarRankInductionOfOS
        depth sourceStrictGeneratedCarrier_subset (rank + 1) =
      (D.scalarRankInductionOfOS
        depth sourceStrictGeneratedCarrier_subset rank).nextOfOS :=
  rfl

theorem scalarRankInductionOfOS_carrier_subset_succ
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (rank arity : Nat) :
    ((D.scalarRankInductionOfOS
      depth sourceStrictGeneratedCarrier_subset rank
      ).pointed.stageLevel.stage arity).carrier ⊆
      ((D.scalarRankInductionOfOS
        depth sourceStrictGeneratedCarrier_subset (rank + 1)
        ).pointed.stageLevel.stage arity).carrier :=
  (D.scalarRankInductionOfOS
    depth sourceStrictGeneratedCarrier_subset rank
    ).carrier_subset_nextOfOS arity

theorem scalarRankInductionOfOS_extends_succ
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (rank arity : Nat) :
    Set.EqOn
      ((D.scalarRankInductionOfOS
        depth sourceStrictGeneratedCarrier_subset (rank + 1)
        ).pointed.stageLevel.stage arity).distribution
      ((D.scalarRankInductionOfOS
        depth sourceStrictGeneratedCarrier_subset rank
        ).pointed.stageLevel.stage arity).distribution
      ((D.scalarRankInductionOfOS
        depth sourceStrictGeneratedCarrier_subset rank
        ).pointed.stageLevel.stage arity).carrier :=
  (D.scalarRankInductionOfOS
    depth sourceStrictGeneratedCarrier_subset rank
    ).nextOfOS_extends arity

theorem scalarRankInductionOfOS_carrier_mono
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (arity : Nat) :
    Monotone fun rank =>
      ((D.scalarRankInductionOfOS
        depth sourceStrictGeneratedCarrier_subset rank
        ).pointed.stageLevel.stage arity).carrier := by
  intro rank rank' hrank
  induction rank', hrank using Nat.le_induction with
  | base =>
      exact Set.Subset.rfl
  | succ rank' _ ih =>
      exact
        ih.trans
          (D.scalarRankInductionOfOS_carrier_subset_succ
            depth sourceStrictGeneratedCarrier_subset rank' arity)

theorem scalarRankInductionOfOS_distribution_eq_of_le
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    {rank rank' arity : Nat}
    (hrank : rank <= rank')
    {z : OSIITimeGapSpace arity}
    (hz :
      z ∈ ((D.scalarRankInductionOfOS
        depth sourceStrictGeneratedCarrier_subset rank
        ).pointed.stageLevel.stage arity).carrier) :
    ((D.scalarRankInductionOfOS
      depth sourceStrictGeneratedCarrier_subset rank'
      ).pointed.stageLevel.stage arity).distribution z =
      ((D.scalarRankInductionOfOS
        depth sourceStrictGeneratedCarrier_subset rank
        ).pointed.stageLevel.stage arity).distribution z := by
  induction rank', hrank using Nat.le_induction with
  | base =>
      rfl
  | succ rank' hrank ih =>
      exact
        (D.scalarRankInductionOfOS_extends_succ
          depth sourceStrictGeneratedCarrier_subset rank' arity
          (D.scalarRankInductionOfOS_carrier_mono
            depth sourceStrictGeneratedCarrier_subset arity
            hrank hz)).trans ih

theorem scalarRankInductionOfOS_pairwise_compatible
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (arity rank rank' : Nat) :
    Set.EqOn
      ((D.scalarRankInductionOfOS
        depth sourceStrictGeneratedCarrier_subset rank
        ).pointed.stageLevel.stage arity).distribution
      ((D.scalarRankInductionOfOS
        depth sourceStrictGeneratedCarrier_subset rank'
        ).pointed.stageLevel.stage arity).distribution
      (((D.scalarRankInductionOfOS
          depth sourceStrictGeneratedCarrier_subset rank
          ).pointed.stageLevel.stage arity).carrier ∩
        ((D.scalarRankInductionOfOS
          depth sourceStrictGeneratedCarrier_subset rank'
          ).pointed.stageLevel.stage arity).carrier) := by
  intro z hz
  rcases le_total rank rank' with hrank | hrank
  · exact
      (D.scalarRankInductionOfOS_distribution_eq_of_le
        depth sourceStrictGeneratedCarrier_subset
        hrank hz.1).symm
  · exact
      D.scalarRankInductionOfOS_distribution_eq_of_le
        depth sourceStrictGeneratedCarrier_subset
        hrank hz.2

@[simp] theorem scalarRankInductionOfOS_hub
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (rank : Nat) :
    (D.scalarRankInductionOfOS
      depth sourceStrictGeneratedCarrier_subset rank
      ).pointed.hub = D.hub := by
  induction rank with
  | zero =>
      rfl
  | succ rank ih =>
      rw [D.scalarRankInductionOfOS_succ
        depth sourceStrictGeneratedCarrier_subset rank,
        StrictGeneratedScalarRankPointedInductionData.nextOfOS_hub,
        ih]

/-- Reuse the existing arbitrary-family local-stage gluing API for the
entire compatible original-OS analytic-rank chain. -/
noncomputable def scalarRankLocalTimeStageFamilyOfOS
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (arity : Nat) :
    OSIILocalTimeStageFamily d arity Nat where
  domain := fun rank =>
    ((D.scalarRankInductionOfOS
      depth sourceStrictGeneratedCarrier_subset rank
      ).pointed.stageLevel.stage arity).carrier
  domain_open := fun rank =>
    ((D.scalarRankInductionOfOS
      depth sourceStrictGeneratedCarrier_subset rank
      ).pointed.stageLevel.stage arity).carrier_open
  distribution := fun rank =>
    ((D.scalarRankInductionOfOS
      depth sourceStrictGeneratedCarrier_subset rank
      ).pointed.stageLevel.stage arity).distribution
  weaklyHolomorphic := fun rank =>
    ((D.scalarRankInductionOfOS
      depth sourceStrictGeneratedCarrier_subset rank
      ).pointed.stageLevel.stage arity).weaklyHolomorphic
  compatible :=
    D.scalarRankInductionOfOS_pairwise_compatible
      depth sourceStrictGeneratedCarrier_subset arity

/-- Glue every finite analytic rank without an additional OS hypothesis. -/
noncomputable def scalarRankUnionStageOfOS
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (arity : Nat) :
    OSIITimeContinuationStage d arity :=
  (D.scalarRankLocalTimeStageFamilyOfOS
    depth sourceStrictGeneratedCarrier_subset arity
    ).toTimeContinuationStage

theorem scalarRankStageCarrier_subset_unionOfOS
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (rank arity : Nat) :
    ((D.scalarRankInductionOfOS
      depth sourceStrictGeneratedCarrier_subset rank
      ).pointed.stageLevel.stage arity).carrier ⊆
      (D.scalarRankUnionStageOfOS
        depth sourceStrictGeneratedCarrier_subset arity).carrier := by
  intro z hz
  exact Set.mem_iUnion_of_mem rank hz

theorem scalarRankUnionStageOfOS_extends_rank
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (rank arity : Nat) :
    Set.EqOn
      (D.scalarRankUnionStageOfOS
        depth sourceStrictGeneratedCarrier_subset arity).distribution
      ((D.scalarRankInductionOfOS
        depth sourceStrictGeneratedCarrier_subset rank
        ).pointed.stageLevel.stage arity).distribution
      ((D.scalarRankInductionOfOS
        depth sourceStrictGeneratedCarrier_subset rank
        ).pointed.stageLevel.stage arity).carrier :=
  (D.scalarRankLocalTimeStageFamilyOfOS
    depth sourceStrictGeneratedCarrier_subset arity
    ).gluedDistribution_eqOn_domain rank

/-- Every strict target-depth derivation has finite analytic rank. -/
theorem strictGeneratedTargetCarrier_subset_scalarRankUnionStageOfOS
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (arity : Nat) :
    osiiTimeArgumentCarrier
        (osiiStrictGeneratedLogarithmicBase arity (depth + 1)) ⊆
      (D.scalarRankUnionStageOfOS
        depth sourceStrictGeneratedCarrier_subset arity).carrier := by
  intro z hz
  obtain ⟨rank, hrank⟩ :=
    mem_strictGeneratedScalarBase_iff_exists_rank.mp hz.2
  exact
    D.scalarRankStageCarrier_subset_unionOfOS
      depth sourceStrictGeneratedCarrier_subset rank arity
      ((D.scalarRankInductionOfOS
        depth sourceStrictGeneratedCarrier_subset rank
        ).targetRankCarrier_subset arity ⟨hz.1, hrank⟩)

/-- Simultaneous original-OS all-rank union at every arity. -/
noncomputable def scalarRankUnionStageLevelOfOS
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier) :
    SimultaneousTimeContinuationStageLevel d where
  stage :=
    D.scalarRankUnionStageOfOS
      depth sourceStrictGeneratedCarrier_subset

theorem scalarRankUnionStageLevelOfOS_extends
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (arity : Nat) :
    Set.EqOn
      ((D.scalarRankUnionStageLevelOfOS
        depth sourceStrictGeneratedCarrier_subset
        ).stage arity).distribution
      (D.stageLevel.stage arity).distribution
      (D.stageLevel.stage arity).carrier :=
  D.scalarRankUnionStageOfOS_extends_rank
    depth sourceStrictGeneratedCarrier_subset 0 arity

theorem oldCarrier_subset_scalarRankUnionStageLevelOfOS
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (arity : Nat) :
    (D.stageLevel.stage arity).carrier ⊆
      ((D.scalarRankUnionStageLevelOfOS
        depth sourceStrictGeneratedCarrier_subset
        ).stage arity).carrier :=
  D.scalarRankStageCarrier_subset_unionOfOS
    depth sourceStrictGeneratedCarrier_subset 0 arity

theorem scalarRankUnionStageLevelOfOS_hasCanonicalEdges
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier) :
    (D.scalarRankUnionStageLevelOfOS
      depth sourceStrictGeneratedCarrier_subset
      ).HasCanonicalReducedCompactEdges OS := by
  intro arity
  exact
    hasCanonicalReducedCompactStageEdges_of_eqOn_extension
      (D.canonicalEdges arity)
      (D.oldCarrier_subset_scalarRankUnionStageLevelOfOS
        depth sourceStrictGeneratedCarrier_subset arity)
      (D.scalarRankUnionStageLevelOfOS_extends
        depth sourceStrictGeneratedCarrier_subset arity)

theorem scalarRankUnionStageOfOS_starConvex
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (q : Nat) :
    StarConvex Real
      (osiiPositiveRealTimeEmbed (D.hub q))
      ((D.scalarRankUnionStageLevelOfOS
        depth sourceStrictGeneratedCarrier_subset
        ).stage (q + 1)).carrier := by
  apply starConvex_iUnion
  intro rank
  simpa [scalarRankUnionStageLevelOfOS, scalarRankUnionStageOfOS,
    scalarRankLocalTimeStageFamilyOfOS,
    D.scalarRankInductionOfOS_hub
    depth sourceStrictGeneratedCarrier_subset rank] using
    ((D.scalarRankInductionOfOS
      depth sourceStrictGeneratedCarrier_subset rank
      ).pointed.pointedAtlas q).carrier_starConvex

/-- The complete all-rank qualitative depth successor under the original
OS axioms, with its fixed pointed atlas retained. -/
noncomputable def scalarRankUnionPointedNextOfOS
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier) :
    CanonicalGeneratorPointedConvexAtlasStageLevelData OS where
  stageLevel :=
    D.scalarRankUnionStageLevelOfOS
      depth sourceStrictGeneratedCarrier_subset
  canonicalEdges :=
    D.scalarRankUnionStageLevelOfOS_hasCanonicalEdges
      depth sourceStrictGeneratedCarrier_subset
  chart := fun q =>
    {z //
      z ∈ ((D.scalarRankUnionStageLevelOfOS
        depth sourceStrictGeneratedCarrier_subset
        ).stage (q + 1)).carrier}
  hub := D.hub
  hub_positive := D.hub_positive
  pointedAtlas := fun q =>
    GeneratorStagePointedConvexAtlas.ofOpenStarConvex
      (D.scalarRankUnionStageOfOS_starConvex
        depth sourceStrictGeneratedCarrier_subset q)

theorem strictGeneratedTargetCarrier_subset_scalarRankUnionPointedNextOfOS
    (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
    (depth : Nat)
    (sourceStrictGeneratedCarrier_subset :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
          (D.stageLevel.stage arity).carrier)
    (arity : Nat) :
    osiiTimeArgumentCarrier
        (osiiStrictGeneratedLogarithmicBase arity (depth + 1)) ⊆
      ((D.scalarRankUnionPointedNextOfOS
        depth sourceStrictGeneratedCarrier_subset
        ).stageLevel.stage arity).carrier :=
  D.strictGeneratedTargetCarrier_subset_scalarRankUnionStageOfOS
    depth sourceStrictGeneratedCarrier_subset arity

end CanonicalGeneratorPointedConvexAtlasStageLevelData

end OSIIChapterV
end OSReconstruction
