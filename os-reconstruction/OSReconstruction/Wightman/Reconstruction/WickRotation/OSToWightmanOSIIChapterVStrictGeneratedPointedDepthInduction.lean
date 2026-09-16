/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialGeneratedLogarithmicRealization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedPointedInduction
















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

namespace InitialGeneratedLogarithmicStageLevelData

/-- Initial pointed stage retaining the canonical unit hub at every arity. -/
noncomputable def toUnitPointedStageLevel
    (D : InitialGeneratedLogarithmicStageLevelData (d := d) OS) :
    CanonicalGeneratorPointedConvexAtlasStageLevelData OS :=
  D.toAtlasLevel.toPointedStageLevelAt unitPointedHub
    D.unitPointedHub_mem_toAtlasLevel_realRegion

@[simp] theorem toUnitPointedStageLevel_hub
    (D : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (k : Nat) :
    D.toUnitPointedStageLevel.hub k = unitPointedHub k :=
  rfl

end InitialGeneratedLogarithmicStageLevelData

/-- The outer depth-induction invariant. -/
structure StrictGeneratedScalarDepthPointedData
    (OS : OsterwalderSchraderAxioms d)
    (depth : Nat) where
  pointed : CanonicalGeneratorPointedConvexAtlasStageLevelData OS
  strictGeneratedCarrier_subset :
    forall arity,
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBase arity depth) ⊆
        (pointed.stageLevel.stage arity).carrier

namespace StrictGeneratedScalarDepthPointedData

variable {depth : Nat}

/-- The all-rank target union is one complete outer depth successor. -/
noncomputable def next
    (D : StrictGeneratedScalarDepthPointedData OS depth)
    (lgc : OSLinearGrowthCondition d OS) :
    StrictGeneratedScalarDepthPointedData OS (depth + 1) where
  pointed :=
    D.pointed.scalarRankUnionPointedNext
      depth D.strictGeneratedCarrier_subset lgc
  strictGeneratedCarrier_subset :=
    D.pointed.strictGeneratedTargetCarrier_subset_scalarRankUnionPointedNext
      depth D.strictGeneratedCarrier_subset lgc

/-- Every outer depth step retains its complete predecessor carrier. -/
theorem carrier_subset_next
    (D : StrictGeneratedScalarDepthPointedData OS depth)
    (lgc : OSLinearGrowthCondition d OS)
    (arity : Nat) :
    (D.pointed.stageLevel.stage arity).carrier ⊆
      ((D.next lgc).pointed.stageLevel.stage arity).carrier :=
  D.pointed.oldCarrier_subset_scalarRankUnionStageLevel
    depth D.strictGeneratedCarrier_subset lgc arity

/-- Every outer depth step agrees with its predecessor on the complete old
carrier. -/
theorem next_extends
    (D : StrictGeneratedScalarDepthPointedData OS depth)
    (lgc : OSLinearGrowthCondition d OS)
    (arity : Nat) :
    Set.EqOn
      ((D.next lgc).pointed.stageLevel.stage arity).distribution
      (D.pointed.stageLevel.stage arity).distribution
      (D.pointed.stageLevel.stage arity).carrier :=
  D.pointed.scalarRankUnionStageLevel_extends
    depth D.strictGeneratedCarrier_subset lgc arity

/-- The complete outer-depth successor agrees with every finite inner-rank
stage on that rank stage's carrier. -/
theorem next_extends_rankInduction
    (D : StrictGeneratedScalarDepthPointedData OS depth)
    (lgc : OSLinearGrowthCondition d OS)
    (rank arity : Nat) :
    Set.EqOn
      ((D.next lgc).pointed.stageLevel.stage arity).distribution
      ((D.pointed.scalarRankInduction
        depth D.strictGeneratedCarrier_subset lgc rank
        ).pointed.stageLevel.stage arity).distribution
      ((D.pointed.scalarRankInduction
        depth D.strictGeneratedCarrier_subset lgc rank
        ).pointed.stageLevel.stage arity).carrier := by
  simpa [next,
    CanonicalGeneratorPointedConvexAtlasStageLevelData.scalarRankUnionPointedNext,
    CanonicalGeneratorPointedConvexAtlasStageLevelData.scalarRankUnionStageLevel]
    using
      D.pointed.scalarRankUnionStage_extends_rank
        depth D.strictGeneratedCarrier_subset lgc rank arity

/-- The outer depth successor retains the fixed positive-real hubs. -/
@[simp] theorem next_hub
    (D : StrictGeneratedScalarDepthPointedData OS depth)
    (lgc : OSLinearGrowthCondition d OS) :
    (D.next lgc).pointed.hub = D.pointed.hub :=
  rfl

/-- The complete all-rank outer-depth successor under the original OS
axioms, retaining both generator and same-depth vacuum-tail branches. -/
noncomputable def nextOfOS
    (D : StrictGeneratedScalarDepthPointedData OS depth) :
    StrictGeneratedScalarDepthPointedData OS (depth + 1) where
  pointed :=
    D.pointed.scalarRankUnionPointedNextOfOS
      depth D.strictGeneratedCarrier_subset
  strictGeneratedCarrier_subset :=
    D.pointed.strictGeneratedTargetCarrier_subset_scalarRankUnionPointedNextOfOS
      depth D.strictGeneratedCarrier_subset

@[simp] theorem nextOfOS_hub
    (D : StrictGeneratedScalarDepthPointedData OS depth) :
    D.nextOfOS.pointed.hub = D.pointed.hub :=
  rfl

end StrictGeneratedScalarDepthPointedData

namespace InitialGeneratedLogarithmicStageLevelData

/-- The proved initial narrow stage realizes the complete strict generated
scalar base at depth zero and supplies the outer pointed base case. -/
noncomputable def toStrictGeneratedScalarDepthZeroPointedData
    (D : InitialGeneratedLogarithmicStageLevelData (d := d) OS) :
    StrictGeneratedScalarDepthPointedData OS 0 where
  pointed := D.toUnitPointedStageLevel
  strictGeneratedCarrier_subset := by
    intro arity z hz
    exact
      D.generatedArgumentCarrier_subset_atlas_stage_zero arity
        ⟨hz.1,
          strictGeneratedScalarBase_subset_generated arity 0 hz.2⟩

end InitialGeneratedLogarithmicStageLevelData

namespace StrictGeneratedScalarDepthPointedData

/-- Iterate the complete outer depth successor from any valid depth-zero
pointed stage. -/
noncomputable def depthInduction
    (D0 : StrictGeneratedScalarDepthPointedData OS 0)
    (lgc : OSLinearGrowthCondition d OS) :
    (depth : Nat) -> StrictGeneratedScalarDepthPointedData OS depth
  | 0 => D0
  | depth + 1 => (D0.depthInduction lgc depth).next lgc

@[simp] theorem depthInduction_zero
    (D0 : StrictGeneratedScalarDepthPointedData OS 0)
    (lgc : OSLinearGrowthCondition d OS) :
    D0.depthInduction lgc 0 = D0 :=
  rfl

@[simp] theorem depthInduction_succ
    (D0 : StrictGeneratedScalarDepthPointedData OS 0)
    (lgc : OSLinearGrowthCondition d OS)
    (depth : Nat) :
    D0.depthInduction lgc (depth + 1) =
      (D0.depthInduction lgc depth).next lgc :=
  rfl

theorem depthInduction_carrier_subset_succ
    (D0 : StrictGeneratedScalarDepthPointedData OS 0)
    (lgc : OSLinearGrowthCondition d OS)
    (depth arity : Nat) :
    ((D0.depthInduction lgc depth
      ).pointed.stageLevel.stage arity).carrier ⊆
      ((D0.depthInduction lgc (depth + 1)
        ).pointed.stageLevel.stage arity).carrier := by
  rw [D0.depthInduction_succ lgc depth]
  exact
    (D0.depthInduction lgc depth).carrier_subset_next lgc arity

theorem depthInduction_extends_succ
    (D0 : StrictGeneratedScalarDepthPointedData OS 0)
    (lgc : OSLinearGrowthCondition d OS)
    (depth arity : Nat) :
    Set.EqOn
      ((D0.depthInduction lgc (depth + 1)
        ).pointed.stageLevel.stage arity).distribution
      ((D0.depthInduction lgc depth
        ).pointed.stageLevel.stage arity).distribution
      ((D0.depthInduction lgc depth
        ).pointed.stageLevel.stage arity).carrier := by
  rw [D0.depthInduction_succ lgc depth]
  exact
    (D0.depthInduction lgc depth).next_extends lgc arity

theorem depthInduction_carrier_mono
    (D0 : StrictGeneratedScalarDepthPointedData OS 0)
    (lgc : OSLinearGrowthCondition d OS)
    (arity : Nat) :
    Monotone fun depth =>
      ((D0.depthInduction lgc depth
        ).pointed.stageLevel.stage arity).carrier := by
  intro depth depth' hdepth
  induction depth', hdepth using Nat.le_induction with
  | base =>
      exact Set.Subset.rfl
  | succ depth' hdepth ih =>
      exact
        ih.trans
          (D0.depthInduction_carrier_subset_succ
            lgc depth' arity)

/-- Later outer-depth stages agree with every earlier depth stage on the
earlier stage's complete carrier. -/
theorem depthInduction_distribution_eq_of_le
    (D0 : StrictGeneratedScalarDepthPointedData OS 0)
    (lgc : OSLinearGrowthCondition d OS)
    {depth depth' arity : Nat}
    (hdepth : depth <= depth')
    {z : OSIITimeGapSpace arity}
    (hz :
      z ∈ ((D0.depthInduction lgc depth
        ).pointed.stageLevel.stage arity).carrier) :
    ((D0.depthInduction lgc depth'
      ).pointed.stageLevel.stage arity).distribution z =
      ((D0.depthInduction lgc depth
        ).pointed.stageLevel.stage arity).distribution z := by
  induction depth', hdepth using Nat.le_induction with
  | base =>
      rfl
  | succ depth' hdepth ih =>
      calc
        ((D0.depthInduction lgc (depth' + 1)
          ).pointed.stageLevel.stage arity).distribution z =
            ((D0.depthInduction lgc depth'
              ).pointed.stageLevel.stage arity).distribution z :=
          D0.depthInduction_extends_succ lgc depth' arity
            (D0.depthInduction_carrier_mono lgc arity hdepth hz)
        _ =
            ((D0.depthInduction lgc depth
              ).pointed.stageLevel.stage arity).distribution z :=
          ih

/-- Every finite outer-depth stage retains the complete depth-zero
distribution on the original depth-zero carrier. -/
theorem depthInduction_distribution_eq_zero
    (D0 : StrictGeneratedScalarDepthPointedData OS 0)
    (lgc : OSLinearGrowthCondition d OS)
    (depth arity : Nat)
    {z : OSIITimeGapSpace arity}
    (hz : z ∈ (D0.pointed.stageLevel.stage arity).carrier) :
    ((D0.depthInduction lgc depth
      ).pointed.stageLevel.stage arity).distribution z =
      (D0.pointed.stageLevel.stage arity).distribution z := by
  simpa using
    D0.depthInduction_distribution_eq_of_le lgc
      (depth := 0) (depth' := depth) (arity := arity)
      (Nat.zero_le depth) hz

@[simp] theorem depthInduction_hub
    (D0 : StrictGeneratedScalarDepthPointedData OS 0)
    (lgc : OSLinearGrowthCondition d OS)
    (depth : Nat) :
    (D0.depthInduction lgc depth).pointed.hub =
      D0.pointed.hub := by
  induction depth with
  | zero =>
      rfl
  | succ depth ih =>
      rw [D0.depthInduction_succ lgc depth,
        StrictGeneratedScalarDepthPointedData.next_hub,
        ih]

/-- The exact recursive-angle sector at depth `depth` lies in the
corresponding constructed stage. -/
theorem recursiveAngleSector_subset_depthInductionStage
    (D0 : StrictGeneratedScalarDepthPointedData OS 0)
    (lgc : OSLinearGrowthCondition d OS)
    (arity depth : Nat) :
    osiiTimeArgumentSector
        (fun i : Fin arity => recursiveAngle (i.val + 1) depth) ⊆
      ((D0.depthInduction lgc depth
        ).pointed.stageLevel.stage arity).carrier := by
  change
    osiiTimeArgumentSector (osiiRecursiveAngleAperture arity depth) ⊆
      ((D0.depthInduction lgc depth
        ).pointed.stageLevel.stage arity).carrier
  exact
    (strict_recursiveAngle_sector_subset_argumentCarrier arity depth).trans
      ((D0.depthInduction lgc depth
        ).strictGeneratedCarrier_subset arity)

/-- At one arity, the constructed depth sequence is the full exhausting
OS-II continuation ladder. -/
noncomputable def toTimeContinuationLadder
    (D0 : StrictGeneratedScalarDepthPointedData OS 0)
    (lgc : OSLinearGrowthCondition d OS)
    (arity : Nat) :
    OSIITimeContinuationLadder d arity :=
  timeContinuationLadderOfAngleSectorCover
    (fun depth =>
      (D0.depthInduction lgc depth
        ).pointed.stageLevel.stage arity)
    (D0.depthInduction_carrier_mono lgc arity)
    (fun depth =>
      D0.depthInduction_extends_succ lgc depth arity)
    (stageAngleSectorCoverOfRecursiveAngles
      (fun depth =>
        (D0.depthInduction lgc depth
          ).pointed.stageLevel.stage arity)
      (D0.recursiveAngleSector_subset_depthInductionStage
        lgc arity))

/-- The resulting continuation stage on the complete product right
half-plane. -/
noncomputable def toFullTimeContinuationStage
    (D0 : StrictGeneratedScalarDepthPointedData OS 0)
    (lgc : OSLinearGrowthCondition d OS)
    (arity : Nat) :
    OSIITimeContinuationStage d arity :=
  (D0.toTimeContinuationLadder lgc arity).toFullTimeContinuationStage

/-- The full continuation agrees with every finite constructed depth stage
on that stage's complete carrier. -/
theorem toFullTimeContinuationStage_extends_depth
    (D0 : StrictGeneratedScalarDepthPointedData OS 0)
    (lgc : OSLinearGrowthCondition d OS)
    (arity depth : Nat) :
    Set.EqOn
      (D0.toFullTimeContinuationStage lgc arity).distribution
      ((D0.depthInduction lgc depth
        ).pointed.stageLevel.stage arity).distribution
      ((D0.depthInduction lgc depth
        ).pointed.stageLevel.stage arity).carrier :=
  (D0.toTimeContinuationLadder lgc arity
    ).toFullTimeContinuationStage_extends_stage depth

/-- Every canonical compact positive-real edge retained by the depth-zero
stage survives in the exhausted full continuation.

The finite stages need not lie entirely in the product right half-plane, so
this is deliberately not phrased as a global stage extension.  Instead, each
canonical edge is transported on its own strict-positive real region. -/
theorem
    toFullTimeContinuationStage_hasCanonicalReducedCompactStageEdges
    (D0 : StrictGeneratedScalarDepthPointedData OS 0)
    (lgc : OSLinearGrowthCondition d OS)
    (arity : Nat) :
    HasCanonicalReducedCompactStageEdges OS
      (D0.toFullTimeContinuationStage lgc arity) := by
  intro compactCarrier hcompact hpositive
  obtain ⟨E⟩ :=
    D0.pointed.canonicalEdges arity
      compactCarrier hcompact hpositive
  refine ⟨{
    cutoff := E.cutoff
    cutoff_support := E.cutoff_support
    cutoff_compact := E.cutoff_compact
    realRegion := E.realRegion
    realRegion_open := E.realRegion_open
    compactCarrier_subset := E.compactCarrier_subset
    cutoff_one_on := E.cutoff_one_on
    edge := ?_ }⟩
  exact
    (D0.toTimeContinuationLadder lgc arity
      ).toFullTimeContinuationStagePositiveRealEdgeData
        0 E.realRegion_subset_strictPositive E.edge

/-- Iterate every outer depth using only the genuine original-OS qualitative
rank successor. -/
noncomputable def depthInductionOfOS
    (D0 : StrictGeneratedScalarDepthPointedData OS 0) :
    (depth : Nat) -> StrictGeneratedScalarDepthPointedData OS depth
  | 0 => D0
  | depth + 1 => (D0.depthInductionOfOS depth).nextOfOS

@[simp] theorem depthInductionOfOS_zero
    (D0 : StrictGeneratedScalarDepthPointedData OS 0) :
    D0.depthInductionOfOS 0 = D0 :=
  rfl

@[simp] theorem depthInductionOfOS_succ
    (D0 : StrictGeneratedScalarDepthPointedData OS 0)
    (depth : Nat) :
    D0.depthInductionOfOS (depth + 1) =
      (D0.depthInductionOfOS depth).nextOfOS :=
  rfl

end StrictGeneratedScalarDepthPointedData

namespace InitialGeneratedLogarithmicStageLevelData

/-- The proved initial stage and the nested rank/depth construction produce
an exhausting continuation ladder at every arity. -/
noncomputable def toStrictGeneratedTimeContinuationLadder
    (D : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS)
    (arity : Nat) :
    OSIITimeContinuationLadder d arity :=
  D.toStrictGeneratedScalarDepthZeroPointedData
    |>.toTimeContinuationLadder lgc arity

/-- The corresponding continuation stage on the complete product right
half-plane. -/
noncomputable def toStrictGeneratedFullTimeContinuationStage
    (D : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS)
    (arity : Nat) :
    OSIITimeContinuationStage d arity :=
  (D.toStrictGeneratedTimeContinuationLadder
    lgc arity).toFullTimeContinuationStage

/-- The strict-generated full continuation retains every represented
canonical compact Schwinger edge from the proved initial stage. -/
theorem
    toStrictGeneratedFullTimeContinuationStage_hasCanonicalReducedCompactStageEdges
    (D : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS)
    (arity : Nat) :
    HasCanonicalReducedCompactStageEdges OS
      (D.toStrictGeneratedFullTimeContinuationStage lgc arity) :=
  D.toStrictGeneratedScalarDepthZeroPointedData
    |>.toFullTimeContinuationStage_hasCanonicalReducedCompactStageEdges
      lgc arity

end InitialGeneratedLogarithmicStageLevelData

end OSIIChapterV
end OSReconstruction
