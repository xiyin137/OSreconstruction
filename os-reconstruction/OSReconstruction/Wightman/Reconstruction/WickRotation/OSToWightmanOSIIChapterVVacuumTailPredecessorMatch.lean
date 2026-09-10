/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRootedStageSuccessor
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageRealEdgeUniqueness
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVVacuumTailAbsoluteStage










noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData
namespace PositiveHeadUniversalAnchoredAtlasData

variable {d q : ℕ} [NeZero d]
variable
  {I : Section43ProductTimeApproximateIdentity (q + 1)}
  {anchor : Fin (q + 1) → ℝ}
  {L : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
  {stage : OSIITimeContinuationStage d (q + 1)}

/-- The common absolute real germ of the predecessor and vacuum-tail stages. -/
def vacuumTailPredecessorRealRegion
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (M : StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
      A OS stage) :
    Set (Fin (q + 1) → ℝ) :=
  M.realRegion ∩ D.vacuumTailAbsoluteRealRegion M.currentData

theorem vacuumTailPredecessorRealRegion_open
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (M : StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
      A OS stage) :
    IsOpen (D.vacuumTailPredecessorRealRegion M) :=
  M.realRegion_open.inter
    (D.vacuumTailAbsoluteRealRegion_open M.currentData)

@[simp]
theorem anchor_mem_vacuumTailPredecessorRealRegion
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (M : StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
      A OS stage) :
    anchor ∈ D.vacuumTailPredecessorRealRegion M :=
  ⟨M.anchor_mem,
    D.anchor_mem_vacuumTailAbsoluteRealRegion M.currentData⟩

/-- The absolute vacuum-tail orbit and predecessor orbit agree on their
entire common open real germ. -/
theorem vacuumTailAbsoluteOrbit_eq_predecessorOrbit
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (M : StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
      A OS stage) :
    Set.EqOn
      D.vacuumTailAbsoluteOrbit
      M.edge.orbit
      (D.vacuumTailPredecessorRealRegion M) := by
  intro τ hτ
  exact
    OSIITimeContinuationStage.orbit_eqOn_inter_of_sameDistribution
      (D.vacuumTailAbsoluteStage_hasPositiveRealEdge M.currentData)
      M.edge.stageEdge
      (D.vacuumTailAbsoluteRealRegion_open M.currentData)
      M.realRegion_open
      (D.vacuumTailAbsoluteOrbit_represents M.currentData)
      M.edge.represents
      ⟨hτ.2, hτ.1⟩

/-- The vacuum-tail stage, restricted to the common predecessor germ, carries
the complete represented positive-real-edge package.  Pointwise boundedness
is inherited from the predecessor orbit after uniqueness. -/
noncomputable def vacuumTailAbsoluteEdgeOnPredecessor
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (M : StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
      A OS stage) :
    D.vacuumTailAbsoluteStage.PositiveRealEdgeData
      (orderedTransportDistribution M.currentData.current)
      (D.vacuumTailPredecessorRealRegion M) where
  orbit := D.vacuumTailAbsoluteOrbit
  stageEdge := fun τ hτ =>
    D.vacuumTailAbsoluteStage_hasPositiveRealEdge
      M.currentData τ hτ.2
  represents := by
    intro χ
    exact
      SCV.representsDistributionOn_congr_on_subset
        ((orderedTransportDistribution M.currentData.current).comp
          (section43OrderedPullbackTimeSpatialTensorCLM
            d (q + 1) χ))
        (D.vacuumTailAbsoluteOrbit_represents M.currentData χ)
        (fun _ _ => rfl)
        Set.inter_subset_right
  pointwiseBounded := by
    intro χ
    obtain ⟨C, hC⟩ := M.edge.pointwiseBounded χ
    exact ⟨C, fun τ hτ => by
      rw [D.vacuumTailAbsoluteOrbit_eq_predecessorOrbit M hτ]
      exact hC τ hτ.1⟩

/-- The predecessor edge can be renamed to the absolute vacuum-tail orbit on
the common germ.  The two stages now have definitionally the same named real
edge, ready for a connected-overlap or convex-atlas gluing step. -/
noncomputable def predecessorEdgeMatchedToVacuumTail
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (M : StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
      A OS stage) :
    stage.PositiveRealEdgeData
      (orderedTransportDistribution M.currentData.current)
      (D.vacuumTailPredecessorRealRegion M) where
  orbit := D.vacuumTailAbsoluteOrbit
  stageEdge := by
    intro τ hτ
    have hold := M.edge.stageEdge τ hτ.1
    exact
      ⟨hold.1,
        hold.2.trans
          (D.vacuumTailAbsoluteOrbit_eq_predecessorOrbit M hτ).symm⟩
  represents :=
    (D.vacuumTailAbsoluteEdgeOnPredecessor M).represents
  pointwiseBounded :=
    (D.vacuumTailAbsoluteEdgeOnPredecessor M).pointwiseBounded

end PositiveHeadUniversalAnchoredAtlasData
end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
