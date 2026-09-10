/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINormalizedEnvelopeWeightedSourceEnvelope
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVOneParticleTranslatedMixedDeltaProducer
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedRootedSuccessor
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation629Majorant
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedGeometry
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedBoundedScalarPhysicalCharts
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedPointedInduction
import OSReconstruction.SCV.BochnerTubeTheorem
import OSReconstruction.SCV.SchwartzFiniteSeminormBound
















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

open Section43ProductTimeApproximateIdentity
open Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData

/-- The physical-strip intersection does not shrink a ranked
strict-generated scalar base. -/
private theorem rankPhysicalLogarithmicBase_eq
    (m depth rank : Nat) :
    osiiPhysicalLogarithmicBase
        (osiiStrictGeneratedLogarithmicBaseAtRank m depth rank) =
      osiiStrictGeneratedLogarithmicBaseAtRank m depth rank := by
  apply Set.Subset.antisymm inter_subset_left
  intro x hx
  exact ⟨hx, hx.toStrictGenerated.coordinate_abs_lt_pi_div_two⟩

/-- Ranked logarithmic tubes are real-convex. -/
private theorem rankLogarithmicTube_convex
    (m depth rank : Nat) :
    Convex Real
      (osiiLogarithmicTube
        (osiiStrictGeneratedLogarithmicBaseAtRank m depth rank)) := by
  rw [osiiLogarithmicTube, rankPhysicalLogarithmicBase_eq]
  exact SCV.tubeDomain_convex
    (convex_osiiStrictGeneratedLogarithmicBaseAtRank m depth rank)

/-- Zero belongs to every ranked logarithmic tube. -/
private theorem zero_mem_rankLogarithmicTube
    (m depth rank : Nat) :
    (0 : Fin m -> Complex) ∈
      osiiLogarithmicTube
        (osiiStrictGeneratedLogarithmicBaseAtRank m depth rank) := by
  rw [osiiLogarithmicTube, rankPhysicalLogarithmicBase_eq]
  change (0 : Fin m -> Real) ∈
    osiiStrictGeneratedLogarithmicBaseAtRank m depth rank
  exact OSIIStrictGeneratedLogarithmicArgumentAtRank.scalar_zero_mem
    rank m depth

/-- A positive-depth positive-rank logarithmic tube is open. -/
private theorem rankSuccessorLogarithmicTube_open
    (m depth rank : Nat) :
    IsOpen
      (osiiLogarithmicTube
        (osiiStrictGeneratedLogarithmicBaseAtRank
          m (depth + 1) (rank + 1))) :=
  isOpen_osiiLogarithmicTube
    (isOpen_rankSuccessorScalarBase rank m depth)

/-- The fixed positive VI.2 shift preserves every coordinatewise-solid
principal-argument carrier.  Adding positive real time keeps each coordinate
in the right half-plane and can only decrease its absolute argument. -/
theorem osiiVI2Shift_mem_timeArgumentCarrier_of_coordinatewiseSolid
    {k : Nat}
    {base : Set (Fin k -> Real)}
    (hsolid : SCV.IsCoordinatewiseSolid base)
    {epsilon : Real}
    (hepsilon : 0 <= epsilon)
    {zeta : OSIITimeGapSpace k}
    (hzeta : zeta ∈ osiiTimeArgumentCarrier base) :
    osiiVI2Shift k epsilon zeta ∈ osiiTimeArgumentCarrier base := by
  refine ⟨?_, hsolid hzeta.2 _ ?_⟩
  · intro i
    change 0 < (zeta i + epsilon).re
    simpa using add_pos_of_pos_of_nonneg (hzeta.1 i) hepsilon
  · intro i
    simpa [osiiTimeArgumentVector] using
      (abs_arg_add_ofReal_le (hzeta.1 i) hepsilon)

namespace BoundedGlobalRankSuccessorFlatChartData

variable {m : Nat} {B : Real}
variable {A : BoundedScalarContinuationData m B}
variable {rank depth : Nat}

/-- The two pieces retained by the physically matched scalar successor: the
complete old carrier and the exact next-rank logarithmic tube. -/
def rankTubeSuccessorDomain
    (_D : BoundedGlobalRankSuccessorFlatChartData A rank depth)
    (b : Bool) : Set (Fin m -> Complex) :=
  if b then A.carrier else
    osiiLogarithmicTube
      (osiiStrictGeneratedLogarithmicBaseAtRank
        m (depth + 1) (rank + 1))

/-- The exact next-rank logarithmic tube is contained in the unrestricted
global scalar successor. -/
theorem rankTube_subset_rankSuccessor
    (D : BoundedGlobalRankSuccessorFlatChartData A rank depth) :
    osiiLogarithmicTube
        (osiiStrictGeneratedLogarithmicBaseAtRank
          m (depth + 1) (rank + 1)) ⊆
      D.rankSuccessor.carrier := by
  intro z hz
  apply D.logarithmicRankTarget_mem_rankSuccessor z
  change
    (fun j => (z j).im) ∈
      osiiPhysicalLogarithmicBase
        (osiiStrictGeneratedLogarithmicBaseAtRank
          m (depth + 1) (rank + 1)) at hz
  exact hz.1

theorem rankTubeSuccessorDomain_subset_rankSuccessor
    (D : BoundedGlobalRankSuccessorFlatChartData A rank depth)
    (b : Bool) :
    D.rankTubeSuccessorDomain b ⊆ D.rankSuccessor.carrier := by
  cases b with
  | false =>
      simpa [rankTubeSuccessorDomain] using
        D.rankTube_subset_rankSuccessor
  | true =>
      simpa [rankTubeSuccessorDomain] using
        D.predecessor_subset_rankSuccessor

/-- Restrict the completed scalar successor to precisely the part represented
by the old physical stage and the exact next-rank physical target. -/
noncomputable def rankTubeSuccessor
    (D : BoundedGlobalRankSuccessorFlatChartData A rank depth) :
    BoundedScalarContinuationData m B where
  carrier := ⋃ b : Bool, D.rankTubeSuccessorDomain b
  carrier_open := by
    apply isOpen_iUnion
    intro b
    cases b with
    | false =>
        simpa [rankTubeSuccessorDomain] using
          rankSuccessorLogarithmicTube_open m depth rank
    | true =>
        simpa [rankTubeSuccessorDomain] using A.carrier_open
  carrier_starConvex := by
    apply starConvex_iUnion
    intro b
    cases b with
    | false =>
        have hzero :
            (0 : Fin m -> Complex) ∈
              osiiLogarithmicTube
                (osiiStrictGeneratedLogarithmicBaseAtRank
                  m (depth + 1) (rank + 1)) := by
          exact zero_mem_rankLogarithmicTube
            m (depth + 1) (rank + 1)
        simpa [rankTubeSuccessorDomain] using
          (rankLogarithmicTube_convex
            m (depth + 1) (rank + 1)).starConvex hzero
    | true =>
        simpa [rankTubeSuccessorDomain] using A.carrier_starConvex
  zero_mem :=
    Set.mem_iUnion_of_mem true
      (by simpa [rankTubeSuccessorDomain] using A.zero_mem)
  toFun := D.rankSuccessor.toFun
  differentiableOn :=
    D.rankSuccessor.differentiableOn.mono (by
      intro z hz
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hz
      exact D.rankTubeSuccessorDomain_subset_rankSuccessor b hb)
  norm_le := by
    intro z hz
    apply D.rankSuccessor.norm_le z
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hz
    exact D.rankTubeSuccessorDomain_subset_rankSuccessor b hb

theorem rankTube_subset_rankTubeSuccessor
    (D : BoundedGlobalRankSuccessorFlatChartData A rank depth) :
    osiiLogarithmicTube
        (osiiStrictGeneratedLogarithmicBaseAtRank
          m (depth + 1) (rank + 1)) ⊆
      D.rankTubeSuccessor.carrier := by
  intro z hz
  exact Set.mem_iUnion_of_mem false
    (by simpa [rankTubeSuccessorDomain] using hz)

theorem rankTubeSuccessor_eq_predecessor
    (D : BoundedGlobalRankSuccessorFlatChartData A rank depth) :
    Set.EqOn D.rankTubeSuccessor.toFun A.toFun A.carrier :=
  D.rankSuccessor_eq_predecessor

/-- Every arbitrary-real-center point over the next-rank imaginary stratum
remains in the physically matched scalar successor. -/
theorem logarithmicRankTarget_mem_rankTubeSuccessor
    (D : BoundedGlobalRankSuccessorFlatChartData A rank depth)
    (z : Fin m -> Complex)
    (hz :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        (rank + 1) .scalar m (depth + 1) (fun j => (z j).im)) :
    z ∈ D.rankTubeSuccessor.carrier := by
  apply D.rankTube_subset_rankTubeSuccessor
  change
    (fun j => (z j).im) ∈
      osiiPhysicalLogarithmicBase
        (osiiStrictGeneratedLogarithmicBaseAtRank
          m (depth + 1) (rank + 1))
  exact ⟨hz, hz.toStrictGenerated.coordinate_abs_lt_pi_div_two⟩

end BoundedGlobalRankSuccessorFlatChartData

namespace VI2NormalizedEnvelopeRealSliceCoverageData

variable {d : Nat} [NeZero d]
variable {S : SimultaneousTimeContinuationStageLevel d}
variable {t : Nat} {epsilon : Real}
variable {bound : forall k,
  SchwartzMap (Section43SpatialSpace d k) Complex -> Real}
variable {D : VI2NormalizedEnvelopeFamilyData S t epsilon bound}

end VI2NormalizedEnvelopeRealSliceCoverageData

/-- A bounded scalar continuation at one analytic rank, together with its
realization by the matching qualitative physical rank stage.  The final field
is the recursive coverage invariant deliberately absent from the older
scalar-only rank ladder. -/
structure BoundedScalarRankPhysicalInductionData
    {d m depth rank : Nat} [NeZero d]
    {OS : OsterwalderSchraderAxioms d}
    (Q : StrictGeneratedScalarRankPointedInductionData OS depth rank)
    (chi : SchwartzMap (Section43SpatialSpace d m) Complex)
    (B : Real) where
  continuation : BoundedScalarContinuationData m B
  restriction : BoundedScalarLogarithmicRestrictionData
    continuation (Q.pointed.stageLevel.stage m) chi
  logarithmicRankTarget_mem : forall z,
    OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .scalar m (depth + 1) (fun j => (z j).im) ->
      z ∈ continuation.carrier

namespace BoundedScalarRankPhysicalInductionData

variable {d m depth rank : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}
variable {Q : StrictGeneratedScalarRankPointedInductionData OS depth rank}
variable {chi : SchwartzMap (Section43SpatialSpace d m) Complex}
variable {B : Real}

/-- The old-seed coefficient chart at every rank is supplied by the retained
rank-tube coverage, including rank zero once its real slice is initialized. -/
theorem nonempty_oldCoefficientTarget
    (P : BoundedScalarRankPhysicalInductionData Q chi B)
    {physical : OSIITimeContinuationStage d m}
    (R : BoundedScalarLogarithmicRestrictionData
      P.continuation physical chi)
    {n : Nat} {rho : Real}
    (seed : Fin n -> Fin m -> Real)
    (r : Fin n -> Complex)
    (active : Fin n)
    (hactive : |(r active).im| <= rho ∧
      forall j, j ≠ active -> (r j).im = 0)
    (hrho_lt_one : rho < 1)
    (hold :
      OSIIStrictGeneratedLogarithmicArgumentAtRank
        rank .scalar m (depth + 1) (seed active)) :
    Nonempty
      (BoundedZeroPointedAmbientChartData R
        (osiiStrictScalarSeedCoefficientMap seed r)) :=
  BoundedZeroPointedAmbientChartData.nonempty_ofPredecessorTarget R _
    (P.logarithmicRankTarget_mem _
      (osiiStrictScalarSeedCoefficientMap_im_oldAtRank
        seed r active hactive hrho_lt_one hold))

/-- The old carrier and exact next-rank tube both lie in the logarithmic
pullback of the matching qualitative physical successor. -/
theorem rankTubeSuccessor_carrier_subset_nextPullback
    (P : BoundedScalarRankPhysicalInductionData Q chi B)
    (lgc : OSLinearGrowthCondition d OS)
    (G : BoundedGlobalRankSuccessorFlatChartData
      P.continuation rank depth) :
    G.rankTubeSuccessor.carrier ⊆
      (logarithmicPullbackStage
        ((Q.next lgc).pointed.stageLevel.stage m)).carrier := by
  intro z hz
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hz
  cases b with
  | false =>
      apply osiiLogarithmicTube_subset_pullbackStage
        ((Q.next lgc).targetRankCarrier_subset m)
      simpa [BoundedGlobalRankSuccessorFlatChartData.rankTubeSuccessorDomain]
        using hb
  | true =>
      have hold :
          osiiLogExp z ∈ (Q.pointed.stageLevel.stage m).carrier :=
        P.restriction.carrier_subset_pullback
          (by simpa [BoundedGlobalRankSuccessorFlatChartData.rankTubeSuccessorDomain]
            using hb)
      exact Q.carrier_subset_next lgc m hold

/-- Advance the scalar bound and the physical rank stage together.  This is
the compatibility theorem missing from the scalar-only rank ladder. -/
noncomputable def next
    (P : BoundedScalarRankPhysicalInductionData Q chi B)
    (lgc : OSLinearGrowthCondition d OS)
    (G : BoundedGlobalRankSuccessorFlatChartData
      P.continuation rank depth) :
    BoundedScalarRankPhysicalInductionData (Q.next lgc) chi B where
  continuation := G.rankTubeSuccessor
  restriction :=
    BoundedScalarLogarithmicRestrictionData.ofRetainedExtensions
      P.restriction G.rankTubeSuccessor_eq_predecessor
        (Q.next_extends lgc m)
        (P.rankTubeSuccessor_carrier_subset_nextPullback lgc G)
  logarithmicRankTarget_mem := by
    intro z hz
    exact G.logarithmicRankTarget_mem_rankTubeSuccessor z hz

end BoundedScalarRankPhysicalInductionData

namespace StrictGeneratedScalarRankPointedInductionData

variable {d depth : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

/-- The canonical qualitative physical rank iteration beginning with a
rank-zero induction stage. -/
noncomputable def rankIteration
    (Q0 : StrictGeneratedScalarRankPointedInductionData OS depth 0)
    (lgc : OSLinearGrowthCondition d OS) :
    (rank : Nat) ->
      StrictGeneratedScalarRankPointedInductionData OS depth rank
  | 0 => Q0
  | rank + 1 => (rankIteration Q0 lgc rank).next lgc

@[simp] theorem rankIteration_zero
    (Q0 : StrictGeneratedScalarRankPointedInductionData OS depth 0)
    (lgc : OSLinearGrowthCondition d OS) :
    Q0.rankIteration lgc 0 = Q0 :=
  rfl

@[simp] theorem rankIteration_succ
    (Q0 : StrictGeneratedScalarRankPointedInductionData OS depth 0)
    (lgc : OSLinearGrowthCondition d OS)
    (rank : Nat) :
    Q0.rankIteration lgc (rank + 1) =
      (Q0.rankIteration lgc rank).next lgc :=
  rfl

end StrictGeneratedScalarRankPointedInductionData

/-- The exact same-bound rooted and vacuum-tail atlas input at one bounded
scalar/physical rank.  Restrictions are not stored independently: the
qualitative physical extension order and the current bounded restriction
determine them by rebasing. -/
structure BoundedRankRootedTailAtlasData
    {d q depth rank : Nat} [NeZero d]
    {OS : OsterwalderSchraderAxioms d}
    {Q : StrictGeneratedScalarRankPointedInductionData OS depth rank}
    {chi : SchwartzMap (Section43SpatialSpace d (q + 1)) Complex}
    {B : Real}
    (P : BoundedScalarRankPhysicalInductionData Q chi B)
    (lgc : OSLinearGrowthCondition d OS) where
  rootBound : BoundedGeneratorStageExtensionConvexCoreAtlasData
    (B := B)
    (Q.pointed.rootedInsertionRankConvexCoreAtlas
      depth rank Q.sourceReflectedGramRankData lgc q) chi
  tailBound : BoundedGeneratorStageExtensionConvexCoreAtlasData
    (B := B)
    ((Q.pointed.rootedInsertionRankNext
        depth rank Q.sourceReflectedGramRankData lgc
      ).vacuumTailProjectionRankConvexCoreAtlas
        (Q.pointed.rootedInsertionTargetDepthReflectedScalarRankInput
          depth rank Q.sourceReflectedGramRankData
            Q.targetDepthScalarRankData lgc) q) chi

namespace BoundedRankRootedTailAtlasData

variable {d q depth rank : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}
variable {Q : StrictGeneratedScalarRankPointedInductionData OS depth rank}
variable {chi : SchwartzMap (Section43SpatialSpace d (q + 1)) Complex}
variable {B : Real}
variable {P : BoundedScalarRankPhysicalInductionData Q chi B}
variable {lgc : OSLinearGrowthCondition d OS}

/-- Rebase the current bounded restriction through the rooted insertion
atlas. -/
def rootRestriction
    (_H : BoundedRankRootedTailAtlasData P lgc) :
    BoundedScalarLogarithmicRestrictionData
      P.continuation
      (Q.pointed.rootedInsertionRankConvexCoreAtlas
        depth rank Q.sourceReflectedGramRankData lgc q).successorStage chi :=
  P.restriction.rebaseConvexCoreAtlas
    (Q.pointed.rootedInsertionRankConvexCoreAtlas
      depth rank Q.sourceReflectedGramRankData lgc q)

/-- Rebase once more through vacuum-tail projection.  This is the bounded
restriction on the complete physical seed stage. -/
def tailRestriction
    (H : BoundedRankRootedTailAtlasData P lgc) :
    BoundedScalarLogarithmicRestrictionData
      P.continuation
      ((Q.pointed.rootedInsertionRankNext
          depth rank Q.sourceReflectedGramRankData lgc
        ).vacuumTailProjectionRankConvexCoreAtlas
          (Q.pointed.rootedInsertionTargetDepthReflectedScalarRankInput
            depth rank Q.sourceReflectedGramRankData
              Q.targetDepthScalarRankData lgc) q).successorStage chi :=
  H.rootRestriction.rebaseConvexCoreAtlas
    ((Q.pointed.rootedInsertionRankNext
        depth rank Q.sourceReflectedGramRankData lgc
      ).vacuumTailProjectionRankConvexCoreAtlas
        (Q.pointed.rootedInsertionTargetDepthReflectedScalarRankInput
          depth rank Q.sourceReflectedGramRankData
            Q.targetDepthScalarRankData lgc) q)

/-- The bounded rank invariant supplies the old branch, while the two atlas
bounds supply the rooted generator and vacuum-tail branches in their actual
physical order.  This works uniformly at rank zero and positive rank. -/
noncomputable def toPhysicalChartProducer
    (H : BoundedRankRootedTailAtlasData P lgc)
    {coefficientBudget rho : Real}
    (compactification :
      SCV.StripCompactificationParameters coefficientBudget rho)
    (hrho_lt_one : rho < 1)
    {n : Nat}
    (seed : Fin n -> Fin (q + 1) -> Real)
    (seed_rank : forall a,
      OSIIStrictGeneratedScalarRankSuccessorSeed
        rank (q + 1) (depth + 1) (seed a)) :
    BoundedRankSuccessorSeedPhysicalChartProducerData
      H.tailRestriction compactification rank (depth + 1) seed := by
  let D := Q.pointed
  let rankData := Q.sourceReflectedGramRankData
  let targetRankData := Q.targetDepthScalarRankData
  let I := D.rootedInsertionRankNext depth rank rankData lgc
  let reflected :=
    D.rootedInsertionTargetDepthReflectedScalarRankInput
      depth rank rankData targetRankData lgc
  let tailAtlas := I.vacuumTailProjectionRankConvexCoreAtlas reflected q
  exact BoundedRankSuccessorSeedPhysicalChartProducerData.ofSequentialBranches
    tailAtlas H.rootRestriction seed_rank
    (fun active r _hr hactive hold =>
      P.nonempty_oldCoefficientTarget H.tailRestriction
        seed r active hactive hrho_lt_one hold)
    (fun active r _hr hactive hgenerator =>
      nonempty_boundedRootedRankZeroPointedChart
        rankData lgc (D.hub q) (D.hub_positive q) (D.pointedAtlas q)
        H.rootBound H.rootRestriction seed r active hactive
        hrho_lt_one hgenerator)
    (fun active r _hr hactive htail =>
      nonempty_boundedVacuumTailRankZeroPointedChart
        I.stageLevel I.canonicalEdges (depth + 1) rank
        (reflected.reflectedScalarStrictGeneratedAtRank q)
        (I.hub q) (I.hub_positive q) (I.pointedAtlas q)
        H.tailBound H.tailRestriction seed r active hactive
        hrho_lt_one htail)

/-- Convert the concrete rooted/tail atlas bounds into the complete global
flat-chart datum consumed by the scalar successor. -/
noncomputable def toGlobalRankSuccessor
    (H : BoundedRankRootedTailAtlasData P lgc)
    (hB : 0 < B) :
    BoundedGlobalRankSuccessorFlatChartData
      P.continuation rank depth :=
  BoundedGlobalRankSuccessorFlatChartData.ofPhysicalConstructorwise
    (R := H.tailRestriction) hB fun _n seed hseed
      {_S _rho} compactification _hrho_pos hrho_lt_one =>
        ⟨H.toPhysicalChartProducer
          compactification hrho_lt_one seed hseed⟩

/-- One concrete same-bound rooted/tail atlas advances the complete recursive
bounded scalar/physical rank invariant. -/
noncomputable def toNext
    (H : BoundedRankRootedTailAtlasData P lgc)
    (hB : 0 < B) :
    BoundedScalarRankPhysicalInductionData (Q.next lgc) chi B :=
  P.next lgc (H.toGlobalRankSuccessor hB)

end BoundedRankRootedTailAtlasData

namespace BoundedScalarRankPhysicalInductionData

variable {d q depth : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}
variable {Q0 : StrictGeneratedScalarRankPointedInductionData OS depth 0}
variable {chi : SchwartzMap (Section43SpatialSpace d (q + 1)) Complex}
variable {B : Real}

/-- Iterate the physically matched bounded rank successor.  The callback is
exactly the remaining analytic input: same-bound rooted and vacuum-tail atlas
estimates at the current rank. -/
noncomputable def rankIteration
    (P0 : BoundedScalarRankPhysicalInductionData Q0 chi B)
    (lgc : OSLinearGrowthCondition d OS)
    (hB : 0 < B)
    (produce : forall
      (rank : Nat)
      (P : BoundedScalarRankPhysicalInductionData
        (Q0.rankIteration lgc rank) chi B),
      Nonempty (BoundedRankRootedTailAtlasData P lgc)) :
    (rank : Nat) ->
      BoundedScalarRankPhysicalInductionData
        (Q0.rankIteration lgc rank) chi B
  | 0 => P0
  | rank + 1 =>
      (Classical.choice
        (produce rank (rankIteration P0 lgc hB produce rank))).toNext hB

@[simp] theorem rankIteration_zero
    (P0 : BoundedScalarRankPhysicalInductionData Q0 chi B)
    (lgc : OSLinearGrowthCondition d OS)
    (hB : 0 < B)
    (produce : forall
      (rank : Nat)
      (P : BoundedScalarRankPhysicalInductionData
        (Q0.rankIteration lgc rank) chi B),
      Nonempty (BoundedRankRootedTailAtlasData P lgc)) :
    rankIteration P0 lgc hB produce 0 = P0 :=
  rfl

@[simp] theorem rankIteration_succ
    (P0 : BoundedScalarRankPhysicalInductionData Q0 chi B)
    (lgc : OSLinearGrowthCondition d OS)
    (hB : 0 < B)
    (produce : forall
      (rank : Nat)
      (P : BoundedScalarRankPhysicalInductionData
        (Q0.rankIteration lgc rank) chi B),
      Nonempty (BoundedRankRootedTailAtlasData P lgc))
    (rank : Nat) :
    rankIteration P0 lgc hB produce (rank + 1) =
      (Classical.choice
        (produce rank (rankIteration P0 lgc hB produce rank))).toNext hB :=
  rfl

end BoundedScalarRankPhysicalInductionData

end OSIIChapterV
end OSReconstruction
