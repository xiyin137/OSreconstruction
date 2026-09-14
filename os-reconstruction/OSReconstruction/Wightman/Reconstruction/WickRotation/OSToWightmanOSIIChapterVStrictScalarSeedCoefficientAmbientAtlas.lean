/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictScalarSeedCoefficientAmbientChart
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorGluing
import OSReconstruction.SCV.ConnectedNeighborhood

















noncomputable section

open Complex Set Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- One zero-pointed ambient chart reaching a selected logarithmic target and
agreeing near zero with an arbitrary predecessor stage. -/
structure ZeroPointedAmbientChartData
    {d k : Nat} [NeZero d]
    (A : OSIITimeContinuationStage d k)
    (z0 : Fin k -> Complex) where
  stage : OSIITimeContinuationStage d k
  carrier_convex : Convex Real stage.carrier
  zero_mem : (0 : Fin k -> Complex) ∈ stage.carrier
  target_mem : z0 ∈ stage.carrier
  seedDomain : Set (Fin k -> Complex)
  seed_open : IsOpen seedDomain
  zero_mem_seed : (0 : Fin k -> Complex) ∈ seedDomain
  seed_subset_overlap :
    seedDomain ⊆
      stage.carrier ∩
        (logarithmicPullbackStage
          A).carrier
  seed_agreesPredecessor :
    Set.EqOn
      stage.distribution
      (logarithmicPullbackStage A).distribution
      seedDomain

namespace ZeroPointedAmbientChartData

variable
  {d : Nat} [NeZero d]
  {k : Nat}
  {P : OSIITimeContinuationStage d k}
  {z1 z2 : Fin k -> Complex}

/-- Two zero-pointed convex target charts agree on their complete overlap. -/
theorem compatible
    (A : ZeroPointedAmbientChartData P z1)
    (B : ZeroPointedAmbientChartData P z2) :
    Set.EqOn
      A.stage.distribution B.stage.distribution
      (A.stage.carrier ∩ B.stage.carrier) := by
  let U : Set (Fin k -> Complex) :=
    A.stage.carrier ∩ B.stage.carrier
  have hU_open : IsOpen U :=
    A.stage.carrier_open.inter B.stage.carrier_open
  have hU_connected : IsConnected U := by
    apply (A.carrier_convex.inter B.carrier_convex).isConnected
    exact ⟨0, A.zero_mem, B.zero_mem⟩
  let V : Set (Fin k -> Complex) :=
    A.seedDomain ∩ B.seedDomain
  have hV_open : IsOpen V :=
    A.seed_open.inter B.seed_open
  have hV_nonempty : V.Nonempty :=
    ⟨0, A.zero_mem_seed, B.zero_mem_seed⟩
  have hVU : V ⊆ U := by
    intro z hz
    exact
      ⟨(A.seed_subset_overlap hz.1).1,
        (B.seed_subset_overlap hz.2).1⟩
  apply
    weaklyHolomorphic_eqOn_of_eqOn_open
      hU_open hU_connected hV_open hV_nonempty hVU
  · intro chi
    exact (A.stage.weaklyHolomorphic chi).mono Set.inter_subset_left
  · intro chi
    exact (B.stage.weaklyHolomorphic chi).mono Set.inter_subset_right
  · intro z hz
    exact
      (A.seed_agreesPredecessor hz.1).trans
        (B.seed_agreesPredecessor hz.2).symm

end ZeroPointedAmbientChartData

namespace StrictScalarTargetAmbientChartData

variable
  {d : Nat} [NeZero d]
  {current : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {depth k : Nat}
  {D :
    GeneratedScalarSeedStageLevelSuccessorData
      current OS depth}
  {z1 z2 : Fin k -> Complex}

end StrictScalarTargetAmbientChartData

/-- A family of zero-pointed ambient charts over one predecessor stage,
including one distinguished chart which supplies the common predecessor
germ. -/
structure ZeroPointedAmbientAtlasData
    {d k : Nat} [NeZero d]
    (A : OSIITimeContinuationStage d k) where
  Index : Type
  target : Index -> Fin k -> Complex
  distinguished : Index
  chart :
    forall a,
      ZeroPointedAmbientChartData A (target a)

namespace ZeroPointedAmbientAtlasData

variable
  {d k : Nat} [NeZero d]
  {A : OSIITimeContinuationStage d k}

/-- Union of all chart carriers in a zero-pointed ambient atlas. -/
def carrier
    (F : ZeroPointedAmbientAtlasData A) :
    Set (Fin k -> Complex) :=
  ⋃ a : F.Index, (F.chart a).stage.carrier

theorem carrier_open
    (F : ZeroPointedAmbientAtlasData A) :
    IsOpen F.carrier := by
  apply isOpen_iUnion
  intro a
  exact (F.chart a).stage.carrier_open

/-- Distribution obtained by gluing all compatible zero-pointed charts. -/
noncomputable def distribution
    (F : ZeroPointedAmbientAtlasData A) :
    (Fin k -> Complex) -> OSIISpatialDistribution d k :=
  SCV.glued_iUnion
    (fun a : F.Index => (F.chart a).stage.carrier)
    (fun a => (F.chart a).stage.distribution)

theorem distribution_eqOn_chart
    (F : ZeroPointedAmbientAtlasData A)
    (a : F.Index) :
    Set.EqOn
      F.distribution
      (F.chart a).stage.distribution
      (F.chart a).stage.carrier := by
  apply SCV.glued_iUnion_eqOn
  intro b c
  exact
    ZeroPointedAmbientChartData.compatible
      (F.chart b) (F.chart c)

theorem distribution_apply
    (F : ZeroPointedAmbientAtlasData A)
    (chi : SchwartzMap
      (Section43SpatialSpace d k) Complex) :
    (fun z => F.distribution z chi) =
      SCV.glued_iUnion
        (fun a : F.Index => (F.chart a).stage.carrier)
        (fun a z => (F.chart a).stage.distribution z chi) := by
  funext z
  classical
  simp only [distribution, SCV.glued_iUnion]
  split_ifs <;> rfl

theorem distribution_weaklyHolomorphic
    (F : ZeroPointedAmbientAtlasData A) :
    OSIIWeaklyHolomorphicOn F.distribution F.carrier := by
  intro chi
  rw [F.distribution_apply chi]
  apply SCV.differentiableOn_glued_iUnion
  · intro z hz
    exact hz
  · intro a
    exact (F.chart a).stage.carrier_open
  · intro a
    exact (F.chart a).stage.weaklyHolomorphic chi
  · intro a b z hz
    exact
      congrArg
        (fun T : OSIISpatialDistribution d k => T chi)
        (ZeroPointedAmbientChartData.compatible
          (F.chart a) (F.chart b) hz)

/-- The glued continuation stage of a zero-pointed ambient atlas. -/
noncomputable def stage
    (F : ZeroPointedAmbientAtlasData A) :
    OSIITimeContinuationStage d k where
  carrier := F.carrier
  carrier_open := F.carrier_open
  distribution := F.distribution
  weaklyHolomorphic := F.distribution_weaklyHolomorphic

theorem target_mem_stage
    (F : ZeroPointedAmbientAtlasData A)
    (a : F.Index) :
    F.target a ∈ F.stage.carrier :=
  Set.mem_iUnion_of_mem a (F.chart a).target_mem

/-- The distinguished chart supplies a nonempty open germ on which the glued
stage agrees with the predecessor logarithmic pullback. -/
theorem exists_open_seed_stage_eq_predecessor
    (F : ZeroPointedAmbientAtlasData A) :
    ∃ U : Set (Fin k -> Complex),
      IsOpen U ∧ (0 : Fin k -> Complex) ∈ U ∧
      U ⊆
        F.stage.carrier ∩
          (logarithmicPullbackStage A).carrier ∧
      Set.EqOn
        F.stage.distribution
        (logarithmicPullbackStage A).distribution
        U := by
  let C := F.chart F.distinguished
  refine
    ⟨C.seedDomain, C.seed_open, C.zero_mem_seed, ?_, ?_⟩
  · intro z hz
    refine ⟨?_, (C.seed_subset_overlap hz).2⟩
    exact
      Set.mem_iUnion_of_mem F.distinguished
        (C.seed_subset_overlap hz).1
  · intro z hz
    exact
      (F.distribution_eqOn_chart F.distinguished
        (C.seed_subset_overlap hz).1).trans
        (C.seed_agreesPredecessor hz)

end ZeroPointedAmbientAtlasData

namespace StrictGeneratedScalarTargetIndex

end StrictGeneratedScalarTargetIndex

end OSIIChapterV
end OSReconstruction
