import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedOriginalOSSuccessor
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedScalarSeeds

/-!
# Simultaneous stage realization of one ranked scalar successor seed base

The rank step at source depth `depth` has two analytic substeps:

* rooted generator insertion realizes rank-`rank` mixed generator outputs at
  target depth `depth + 1`;
* vacuum-tail projection, now at target depth `depth + 1`, realizes the
  remaining rank-`rank` mixed-tail outputs.

The old rank-`rank` scalar target-depth stratum is retained throughout.  This
file packages the composite stage and proves that it contains the complete
rank-successor seed base isolated in
`OSToWightmanOSIIChapterVStrictGeneratedRankedScalarSeeds`.
-/

noncomputable section

open Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

/-- The exact additional induction invariant needed to pass from source
depth `depth` to scalar target depth `depth + 1`: the current stage already
realizes rank `rank` scalar points at the target depth. -/
structure StageWideStrictGeneratedTargetDepthScalarRankData
    {C : Type*}
    [CanonicalGeneratorStageLevelProvider OS C]
    (S : C)
    (depth rank : Nat) where
  scalarStrictGeneratedAtTargetDepth :
    forall arity,
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            arity (depth + 1) rank) ⊆
        (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S arity).carrier

/-- A simultaneous successor which retains its predecessor and realizes the
complete scalar rank-successor seed base at depth `depth + 1`. -/
structure StrictGeneratedScalarRankSuccessorSeedStageLevelData
    (current : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (depth rank : Nat) where
  next : SimultaneousTimeContinuationStageLevel d
  carrier_subset :
    forall k, (current.stage k).carrier ⊆ (next.stage k).carrier
  extendsOld :
    forall k,
      Set.EqOn
        (next.stage k).distribution
        (current.stage k).distribution
        (current.stage k).carrier
  canonicalEdges :
    next.HasCanonicalReducedCompactEdges OS
  scalarRankSuccessorSeedMem :
    forall (k : Nat) (x : Fin k -> Real),
      OSIIStrictGeneratedScalarRankSuccessorSeed
          rank k (depth + 1) x ->
      osiiTimeArgumentCarrier
          ({x} : Set (Fin k -> Real)) ⊆
        (next.stage k).carrier

namespace StrictGeneratedScalarRankSuccessorSeedStageLevelData

variable
  {current : SimultaneousTimeContinuationStageLevel d}
  {depth rank : Nat}

/-- The complete rank-successor seed carrier lies in the composed stage. -/
theorem scalarRankSuccessorSeedCarrier_subset
    (D :
      StrictGeneratedScalarRankSuccessorSeedStageLevelData
        current OS depth rank)
    (k : Nat) :
    osiiTimeArgumentCarrier
        (osiiStrictGeneratedScalarRankSuccessorSeedBase
          k (depth + 1) rank) ⊆
      (D.next.stage k).carrier := by
  intro z hz
  apply
    D.scalarRankSuccessorSeedMem
      k (osiiTimeArgumentVector z) hz.2
  exact ⟨hz.1, rfl⟩

end StrictGeneratedScalarRankSuccessorSeedStageLevelData

namespace CanonicalGeneratorPointedConvexAtlasStageLevelData

variable
  (D : CanonicalGeneratorPointedConvexAtlasStageLevelData OS)
  (depth rank : Nat)
  (P :
    StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) D depth rank)
  (Q :
    StageWideStrictGeneratedTargetDepthScalarRankData
      (OS := OS) D depth rank)
  (lgc : OSLinearGrowthCondition d OS)

/-- Rank-`rank` target-depth scalar realization survives rooted generator
insertion and supplies the reflected inputs for same-depth vacuum-tail
projection. -/
noncomputable def rootedInsertionTargetDepthReflectedScalarRankInput :
    StageWideStrictGeneratedReflectedScalarRankInputData
      (D.rootedInsertionRankNext
        depth rank P lgc).stageLevel
      (depth + 1) rank :=
  StageWideStrictGeneratedReflectedScalarRankInputData.ofScalarAtRank
    (D.rootedInsertionRankNext
      depth rank P lgc).stageLevel
    (depth + 1) rank
    (fun arity =>
      (Q.scalarStrictGeneratedAtTargetDepth arity).trans
        (D.oldCarrier_subset_rootedInsertionRankStageLevel
          depth rank P lgc arity))

/-- The pointed final stage obtained by generator insertion at source depth
`depth` followed by tail projection at target depth `depth + 1`. -/
noncomputable def scalarRankSuccessorSeedPointedNext :
    CanonicalGeneratorPointedConvexAtlasStageLevelData OS :=
  let I :=
    D.rootedInsertionRankNext depth rank P lgc
  I.vacuumTailProjectionRankNext
    (D.rootedInsertionTargetDepthReflectedScalarRankInput
      depth rank P Q lgc)

/-- The composed pointed successor contains every old rank scalar point and
every new generator/tail seed at the target depth. -/
noncomputable def toStrictGeneratedScalarRankSuccessorSeedStageLevelData :
    StrictGeneratedScalarRankSuccessorSeedStageLevelData
      D.stageLevel
      OS depth rank where
  next :=
    (D.scalarRankSuccessorSeedPointedNext
      depth rank P Q lgc).stageLevel
  carrier_subset := by
    intro k
    exact
      (D.oldCarrier_subset_rootedInsertionRankStageLevel
        depth rank P lgc k).trans
        ((D.rootedInsertionRankNext depth rank P lgc
          ).oldCarrier_subset_vacuumTailProjectionRankStageLevel
            (D.rootedInsertionTargetDepthReflectedScalarRankInput
              depth rank P Q lgc)
            k)
  extendsOld := by
    intro k z hz
    let I :=
      D.rootedInsertionRankNext depth rank P lgc
    let R :=
      D.rootedInsertionTargetDepthReflectedScalarRankInput
        depth rank P Q lgc
    exact
      (I.vacuumTailProjectionRankStageLevel_extends R k
        (D.oldCarrier_subset_rootedInsertionRankStageLevel
          depth rank P lgc k hz)).trans
        (D.rootedInsertionRankStageLevel_extends
          depth rank P lgc k hz)
  canonicalEdges :=
    (D.scalarRankSuccessorSeedPointedNext
      depth rank P Q lgc).canonicalEdges
  scalarRankSuccessorSeedMem := by
    intro k x hx
    let I :=
      D.rootedInsertionRankNext depth rank P lgc
    let R :=
      D.rootedInsertionTargetDepthReflectedScalarRankInput
        depth rank P Q lgc
    cases hx with
    | old hx =>
        have hseed :
            osiiTimeArgumentCarrier
                ({x} : Set (Fin k -> Real)) ⊆
              osiiTimeArgumentCarrier
                (osiiStrictGeneratedLogarithmicBaseAtRank
                  k (depth + 1) rank) := by
          intro z hz
          refine ⟨hz.1, ?_⟩
          have harg :
              osiiTimeArgumentVector z = x :=
            Set.mem_singleton_iff.mp hz.2
          rw [harg]
          exact hx
        exact
          hseed.trans
            ((Q.scalarStrictGeneratedAtTargetDepth k).trans
              ((D.oldCarrier_subset_rootedInsertionRankStageLevel
                depth rank P lgc k).trans
                (I.oldCarrier_subset_vacuumTailProjectionRankStageLevel
                  R k)))
    | generatorMemSucc i sourceDepth left theta right
        hleft hright htheta =>
        cases k with
        | zero =>
            have hn := i.hn
            have hm := i.hm
            have hnm := i.hnm
            omega
        | succ q =>
            exact
              (D.argumentGeneratorCarrier_subset_rootedInsertionRankNext
                depth rank P lgc q i left hleft theta htheta
                right hright).trans
                (I.oldCarrier_subset_vacuumTailProjectionRankStageLevel
                  R (q + 1))
    | mixedTailMemScalar targetDepth x hx =>
        exact
          I.mixedTailMemScalar_vacuumTailProjectionRankNext
            R k x hx

/-- Under the original OS axioms, the retained target-depth scalar stratum
survives pointed generator insertion and supplies every reflected input
needed by same-depth vacuum-tail projection. -/
noncomputable def rootedInsertionTargetDepthReflectedScalarRankInputOfOS :
    StageWideStrictGeneratedReflectedScalarRankInputData
      (D.rootedInsertionRankNextOfOS
        depth rank P).stageLevel
      (depth + 1) rank :=
  StageWideStrictGeneratedReflectedScalarRankInputData.ofScalarAtRank
    (D.rootedInsertionRankNextOfOS
      depth rank P).stageLevel
    (depth + 1) rank
    (fun arity =>
      (Q.scalarStrictGeneratedAtTargetDepth arity).trans
        (D.oldCarrier_subset_rootedInsertionRankStageLevelOfOS
          depth rank P arity))

/-- The complete original-OS pointed seed stage: strict-rank generator
insertion followed by the genuine same-depth mixed-tail projection. -/
noncomputable def scalarRankSuccessorSeedPointedNextOfOS :
    CanonicalGeneratorPointedConvexAtlasStageLevelData OS :=
  let I :=
    D.rootedInsertionRankNextOfOS depth rank P
  I.vacuumTailProjectionRankNext
    (D.rootedInsertionTargetDepthReflectedScalarRankInputOfOS
      depth rank P Q)

/-- Every old scalar, strict generator, and same-depth mixed-tail seed is
realized by one source-compatible original-OS pointed successor. -/
noncomputable def toStrictGeneratedScalarRankSuccessorSeedStageLevelDataOfOS :
    StrictGeneratedScalarRankSuccessorSeedStageLevelData
      D.stageLevel
      OS depth rank where
  next :=
    (D.scalarRankSuccessorSeedPointedNextOfOS
      depth rank P Q).stageLevel
  carrier_subset := by
    intro k
    exact
      (D.oldCarrier_subset_rootedInsertionRankStageLevelOfOS
        depth rank P k).trans
        ((D.rootedInsertionRankNextOfOS depth rank P
          ).oldCarrier_subset_vacuumTailProjectionRankStageLevel
            (D.rootedInsertionTargetDepthReflectedScalarRankInputOfOS
              depth rank P Q)
            k)
  extendsOld := by
    intro k z hz
    let I :=
      D.rootedInsertionRankNextOfOS depth rank P
    let R :=
      D.rootedInsertionTargetDepthReflectedScalarRankInputOfOS
        depth rank P Q
    exact
      (I.vacuumTailProjectionRankStageLevel_extends R k
        (D.oldCarrier_subset_rootedInsertionRankStageLevelOfOS
          depth rank P k hz)).trans
        (D.rootedInsertionRankStageLevelOfOS_extends
          depth rank P k hz)
  canonicalEdges :=
    (D.scalarRankSuccessorSeedPointedNextOfOS
      depth rank P Q).canonicalEdges
  scalarRankSuccessorSeedMem := by
    intro k x hx
    let I :=
      D.rootedInsertionRankNextOfOS depth rank P
    let R :=
      D.rootedInsertionTargetDepthReflectedScalarRankInputOfOS
        depth rank P Q
    cases hx with
    | old hx =>
        have hseed :
            osiiTimeArgumentCarrier
                ({x} : Set (Fin k -> Real)) ⊆
              osiiTimeArgumentCarrier
                (osiiStrictGeneratedLogarithmicBaseAtRank
                  k (depth + 1) rank) := by
          intro z hz
          refine ⟨hz.1, ?_⟩
          have harg :
              osiiTimeArgumentVector z = x :=
            Set.mem_singleton_iff.mp hz.2
          rw [harg]
          exact hx
        exact
          hseed.trans
            ((Q.scalarStrictGeneratedAtTargetDepth k).trans
              ((D.oldCarrier_subset_rootedInsertionRankStageLevelOfOS
                depth rank P k).trans
                (I.oldCarrier_subset_vacuumTailProjectionRankStageLevel
                  R k)))
    | generatorMemSucc i sourceDepth left theta right
        hleft hright htheta =>
        cases k with
        | zero =>
            have hn := i.hn
            have hm := i.hm
            have hnm := i.hnm
            omega
        | succ q =>
            exact
              (D.argumentGeneratorCarrier_subset_rootedInsertionRankNextOfOS
                depth rank P q i left hleft theta htheta
                right hright).trans
                (I.oldCarrier_subset_vacuumTailProjectionRankStageLevel
                  R (q + 1))
    | mixedTailMemScalar targetDepth x hx =>
        exact
          I.mixedTailMemScalar_vacuumTailProjectionRankNext
            R k x hx

end CanonicalGeneratorPointedConvexAtlasStageLevelData

end OSIIChapterV
end OSReconstruction
