/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRootedStageSuccessor
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketRootedRepresentedStage
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorStageAffineTranslation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageRealEdgeUniqueness



















noncomputable section

open Complex Filter Set Topology
open scoped Classical Topology

namespace OSReconstruction

namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}
  {OS : OsterwalderSchraderAxioms d}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
  {R : TripleConvolutionRootData I}
  {stage : OSIITimeContinuationStage d k}

/-- The original-OS rooted represented generator and recentered predecessor
stage on one common real edge, retaining their exact reduced current. -/
structure StageMatchedRootedRepresentedGeneratorDataOfOS
    (D : StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
      A OS stage)
    (H : RootedA0BlockHolomorphicTranslationData OS A R) where
  edge :
    (rootedGeneratorDiagonalApproximationFamilyOfOS H
      ).CommonPositiveRealEdgeData
  edge_subset_currentRegion :
    edge.realRegion ⊆ D.currentData.realRegion
  edge_subset_recenteredRegion :
    edge.realRegion ⊆ D.recenteredRealRegion
  rootedEdge :
    ((rootedGeneratorDiagonalApproximationFamilyOfOS H
        ).toGeneratorFamilyOfConvex edge
          (by
            simpa [rootedGeneratorDiagonalApproximationFamilyOfOS] using
              rootedGeneratorTwoScaleApproximationFamilyOfOS_domain_convex H)
      ).toTimeContinuationStage.PositiveRealEdgeData
        (anchoredOrderedTransportDistribution
          D.currentData.current anchor)
        edge.realRegion
  predecessorEdge :
    (stage.recenter anchor).PositiveRealEdgeData
      (anchoredOrderedTransportDistribution
        D.currentData.current anchor)
      edge.realRegion
  predecessor_orbit :
    predecessorEdge.orbit = edge.orbit

/-- Legacy presentation of predecessor matching for existing consumers. -/
structure StageMatchedRootedRepresentedGeneratorData
    (D : StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
      A OS stage)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS) where
  edge :
    (rootedGeneratorDiagonalApproximationFamily H lgc
      ).CommonPositiveRealEdgeData
  edge_subset_currentRegion :
    edge.realRegion ⊆ D.currentData.realRegion
  edge_subset_recenteredRegion :
    edge.realRegion ⊆ D.recenteredRealRegion
  rootedEdge :
    ((rootedGeneratorDiagonalApproximationFamily H lgc
        ).toGeneratorFamilyOfConvex edge
          (by
            simpa [rootedGeneratorDiagonalApproximationFamily,
              rootedGeneratorDiagonalApproximationFamilyOfOS,
              rootedGeneratorTwoScaleApproximationFamily,
              GeneratorSpatialTwoScaleApproximationFamily.diagonal] using
              rootedGeneratorTwoScaleApproximationFamily_domain_convex
                H lgc)
      ).toTimeContinuationStage.PositiveRealEdgeData
        (anchoredOrderedTransportDistribution
          D.currentData.current anchor)
        edge.realRegion
  predecessorEdge :
    (stage.recenter anchor).PositiveRealEdgeData
      (anchoredOrderedTransportDistribution
        D.currentData.current anchor)
      edge.realRegion
  predecessor_orbit :
    predecessorEdge.orbit = edge.orbit

namespace StageMatchedRootedRepresentedGeneratorData

variable
  {D : StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
    A OS stage}
  {H : RootedA0BlockHolomorphicTranslationData OS A R}
  {lgc : OSLinearGrowthCondition d OS}

/-- The rooted generator family translated from increment coordinates back to
the absolute coordinates of the predecessor stage. -/
noncomputable def absoluteApproximationFamily
    (_P : StageMatchedRootedRepresentedGeneratorData D H lgc) :
    GeneratorSpatialApproximationFamily d k :=
  (rootedGeneratorDiagonalApproximationFamily H lgc).uncenter anchor

/-- The matched rooted real edge translated back to absolute time
coordinates. -/
noncomputable def absoluteEdge
    (P : StageMatchedRootedRepresentedGeneratorData D H lgc) :
    P.absoluteApproximationFamily.CommonPositiveRealEdgeData :=
  P.edge.uncenter anchor

/-- Translating the centered matched edge back to absolute coordinates gives a
real edge of the original predecessor stage. -/
theorem predecessor_hasAbsoluteEdge
    (P : StageMatchedRootedRepresentedGeneratorData D H lgc) :
    stage.HasPositiveRealEdge
      P.absoluteEdge.orbit P.absoluteEdge.realRegion := by
  intro τ hτ
  have hold :=
    P.predecessorEdge.stageEdge (τ + -anchor) hτ
  rw [P.predecessor_orbit] at hold
  have hpoint :
      osiiPositiveRealTimeEmbed (τ + -anchor) +
          osiiPositiveRealTimeEmbed anchor =
        osiiPositiveRealTimeEmbed τ := by
    rw [← osiiPositiveRealTimeEmbed_add]
    congr 1
    ext i
    simp
  constructor
  · simpa only [OSIITimeContinuationStage.recenter_carrier,
      Set.mem_setOf_eq, hpoint] using hold.1
  · change
      stage.distribution (osiiPositiveRealTimeEmbed τ) =
        P.edge.orbit (τ + -anchor)
    simpa only [OSIITimeContinuationStage.recenter_distribution,
      hpoint] using hold.2

/-- A centered edge confined to the recentering of `U` translates to an
absolute edge contained in `U`. -/
theorem absoluteEdge_subset
    (P : StageMatchedRootedRepresentedGeneratorData D H lgc)
    {U : Set (Fin k → ℝ)}
    (hU :
      ∀ u ∈ P.edge.realRegion, u + anchor ∈ U) :
    P.absoluteEdge.realRegion ⊆ U := by
  intro τ hτ
  have h := hU (τ + -anchor) hτ
  simpa [add_assoc] using h

/-- Form the genuine fixed-coordinate successor by translating the rooted
generator charts back from increment coordinates before gluing. -/
noncomputable def toAbsoluteStageExtensionDataOfConvexAtlas
    (P : StageMatchedRootedRepresentedGeneratorData D H lgc)
    {U : Set (Fin k → ℝ)}
    {ι : Type*}
    (atlas : GeneratorStageConvexAtlas stage U ι)
    (edge_subset_atlas :
      ∀ u ∈ P.edge.realRegion, u + anchor ∈ U) :
    GeneratorStageExtensionData stage :=
  P.absoluteApproximationFamily.toStageExtensionDataOfConvexAtlas
    P.absoluteEdge
    stage
    P.predecessor_hasAbsoluteEdge
    (atlas.restrictRealRegion
      (P.absoluteEdge_subset edge_subset_atlas))
    ((rootedGeneratorDiagonalApproximationFamily H lgc
      ).uncenter_domain_convex anchor
        (by
          simpa [rootedGeneratorDiagonalApproximationFamily,
            rootedGeneratorDiagonalApproximationFamilyOfOS,
            rootedGeneratorTwoScaleApproximationFamily,
            GeneratorSpatialTwoScaleApproximationFamily.diagonal] using
            rootedGeneratorTwoScaleApproximationFamily_domain_convex H lgc))

/-- The fixed-coordinate predecessor charts and translated rooted generator
domains form the atlas for the genuine successor stage. -/
noncomputable def toAbsoluteSuccessorConvexAtlas
    (P : StageMatchedRootedRepresentedGeneratorData D H lgc)
    {U : Set (Fin k → ℝ)}
    {ι : Type*}
    (atlas : GeneratorStageConvexAtlas stage U ι)
    (edge_subset_atlas :
      ∀ u ∈ P.edge.realRegion, u + anchor ∈ U) :
    GeneratorStageConvexAtlas
      (P.toAbsoluteStageExtensionDataOfConvexAtlas
        atlas edge_subset_atlas).toTimeContinuationStage
      P.absoluteEdge.realRegion
      (Sum ι (GeneratorIndex k)) := by
  let C :=
    P.toAbsoluteStageExtensionDataOfConvexAtlas
      atlas edge_subset_atlas
  exact
    C.toConvexAtlas
      (atlas.restrictRealRegion
        (P.absoluteEdge_subset edge_subset_atlas))
      (by
        change
          ∀ i, Convex ℝ
            (((rootedGeneratorDiagonalApproximationFamily H lgc
              ).uncenter anchor).domain i)
        exact
          (rootedGeneratorDiagonalApproximationFamily H lgc
            ).uncenter_domain_convex anchor
              (by
                simpa [rootedGeneratorDiagonalApproximationFamily,
                  rootedGeneratorDiagonalApproximationFamilyOfOS,
                  rootedGeneratorTwoScaleApproximationFamily,
                  GeneratorSpatialTwoScaleApproximationFamily.diagonal] using
                  rootedGeneratorTwoScaleApproximationFamily_domain_convex
                    H lgc))
      (by
        intro i τ hτ
        change
          osiiPositiveRealTimeEmbed τ ∈
            ((rootedGeneratorDiagonalApproximationFamily H lgc
              ).uncenter anchor).domain i
        exact
          (P.absoluteEdge.scalarLimit_realEdge i τ hτ).1)

end StageMatchedRootedRepresentedGeneratorData

namespace StageMatchedRootedRepresentedGeneratorDataOfOS

variable
  {D : StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
    A OS stage}
  {H : RootedA0BlockHolomorphicTranslationData OS A R}

/-- Translate the genuine original-OS rooted generator back to absolute
predecessor coordinates. -/
noncomputable def absoluteApproximationFamily
    (_P : StageMatchedRootedRepresentedGeneratorDataOfOS D H) :
    GeneratorSpatialApproximationFamily d k :=
  (rootedGeneratorDiagonalApproximationFamilyOfOS H).uncenter anchor

/-- Translate the original-OS matched edge back to absolute coordinates. -/
noncomputable def absoluteEdge
    (P : StageMatchedRootedRepresentedGeneratorDataOfOS D H) :
    P.absoluteApproximationFamily.CommonPositiveRealEdgeData :=
  P.edge.uncenter anchor

/-- The original-OS matched edge remains a real edge of the predecessor
after undoing chronological recentering. -/
theorem predecessor_hasAbsoluteEdge
    (P : StageMatchedRootedRepresentedGeneratorDataOfOS D H) :
    stage.HasPositiveRealEdge
      P.absoluteEdge.orbit P.absoluteEdge.realRegion := by
  intro τ hτ
  have hold :=
    P.predecessorEdge.stageEdge (τ + -anchor) hτ
  rw [P.predecessor_orbit] at hold
  have hpoint :
      osiiPositiveRealTimeEmbed (τ + -anchor) +
          osiiPositiveRealTimeEmbed anchor =
        osiiPositiveRealTimeEmbed τ := by
    rw [← osiiPositiveRealTimeEmbed_add]
    congr 1
    ext i
    simp
  constructor
  · simpa only [OSIITimeContinuationStage.recenter_carrier,
      Set.mem_setOf_eq, hpoint] using hold.1
  · change
      stage.distribution (osiiPositiveRealTimeEmbed τ) =
        P.edge.orbit (τ + -anchor)
    simpa only [OSIITimeContinuationStage.recenter_distribution,
      hpoint] using hold.2

/-- An original-OS centered edge confined to an atlas germ stays in that
germ after conversion to absolute coordinates. -/
theorem absoluteEdge_subset
    (P : StageMatchedRootedRepresentedGeneratorDataOfOS D H)
    {U : Set (Fin k → ℝ)}
    (hU :
      ∀ u ∈ P.edge.realRegion, u + anchor ∈ U) :
    P.absoluteEdge.realRegion ⊆ U := by
  intro τ hτ
  have h := hU (τ + -anchor) hτ
  simpa [add_assoc] using h

/-- Glue the original-OS rooted generator to a fixed-coordinate predecessor
using its retained convex atlas. -/
noncomputable def toAbsoluteStageExtensionDataOfConvexAtlas
    (P : StageMatchedRootedRepresentedGeneratorDataOfOS D H)
    {U : Set (Fin k → ℝ)}
    {ι : Type*}
    (atlas : GeneratorStageConvexAtlas stage U ι)
    (edge_subset_atlas :
      ∀ u ∈ P.edge.realRegion, u + anchor ∈ U) :
    GeneratorStageExtensionData stage :=
  P.absoluteApproximationFamily.toStageExtensionDataOfConvexAtlas
    P.absoluteEdge
    stage
    P.predecessor_hasAbsoluteEdge
    (atlas.restrictRealRegion
      (P.absoluteEdge_subset edge_subset_atlas))
    ((rootedGeneratorDiagonalApproximationFamilyOfOS H
      ).uncenter_domain_convex anchor
        (by
          simpa [rootedGeneratorDiagonalApproximationFamilyOfOS] using
            rootedGeneratorTwoScaleApproximationFamilyOfOS_domain_convex H))

/-- The predecessor charts and original-OS rooted charts form a retained
convex atlas for their genuine fixed-coordinate successor. -/
noncomputable def toAbsoluteSuccessorConvexAtlas
    (P : StageMatchedRootedRepresentedGeneratorDataOfOS D H)
    {U : Set (Fin k → ℝ)}
    {ι : Type*}
    (atlas : GeneratorStageConvexAtlas stage U ι)
    (edge_subset_atlas :
      ∀ u ∈ P.edge.realRegion, u + anchor ∈ U) :
    GeneratorStageConvexAtlas
      (P.toAbsoluteStageExtensionDataOfConvexAtlas
        atlas edge_subset_atlas).toTimeContinuationStage
      P.absoluteEdge.realRegion
      (Sum ι (GeneratorIndex k)) := by
  let C :=
    P.toAbsoluteStageExtensionDataOfConvexAtlas
      atlas edge_subset_atlas
  exact
    C.toConvexAtlas
      (atlas.restrictRealRegion
        (P.absoluteEdge_subset edge_subset_atlas))
      (by
        change
          ∀ i, Convex ℝ
            (((rootedGeneratorDiagonalApproximationFamilyOfOS H
              ).uncenter anchor).domain i)
        exact
          (rootedGeneratorDiagonalApproximationFamilyOfOS H
            ).uncenter_domain_convex anchor
              (by
                simpa [rootedGeneratorDiagonalApproximationFamilyOfOS] using
                  rootedGeneratorTwoScaleApproximationFamilyOfOS_domain_convex H))
      (by
        intro i τ hτ
        change
          osiiPositiveRealTimeEmbed τ ∈
            ((rootedGeneratorDiagonalApproximationFamilyOfOS H
              ).uncenter anchor).domain i
        exact
          (P.absoluteEdge.scalarLimit_realEdge i τ hτ).1)

end StageMatchedRootedRepresentedGeneratorDataOfOS

/-- Construct a matched rooted generator inside any prescribed neighborhood
which is already contained in both the packet recovery germ and the
recentered predecessor edge, using only the original OS axioms. -/
theorem exists_stageMatchedRootedRepresentedGeneratorDataOfOS_on
    (D : StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
      A OS stage)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (Q : Set (Fin k → ℝ))
    (hQ : Q ∈ 𝓝 0)
    (hQ_current : Q ⊆ D.currentData.realRegion)
    (hQ_recentered : Q ⊆ D.recenteredRealRegion) :
    ∃ P : StageMatchedRootedRepresentedGeneratorDataOfOS D H,
      P.edge.realRegion ⊆ Q := by
  obtain ⟨E, P, hEQ, hP_orbit⟩ :=
    exists_rootedRepresentedGeneratorStageOfOS_of_currentData_on
      H D.currentData Q hQ
  have hE_current :
      E.realRegion ⊆ D.currentData.realRegion :=
    hEQ.trans hQ_current
  have hE_recentered :
      E.realRegion ⊆ D.recenteredRealRegion :=
    hEQ.trans hQ_recentered
  let oldEdge :=
    D.recenteredEdge.restrictRegion E.realRegion hE_recentered
  have horbit :
      Set.EqOn E.orbit oldEdge.orbit E.realRegion := by
    intro τ hτ
    have h :=
      OSIITimeContinuationStage.PositiveRealEdgeData.orbit_eqOn_inter_of_sameDistribution
        P oldEdge E.realRegion_open E.realRegion_open ⟨hτ, hτ⟩
    simpa [hP_orbit] using h
  let predecessorEdge :
      (stage.recenter anchor).PositiveRealEdgeData
        (anchoredOrderedTransportDistribution
          D.currentData.current anchor)
        E.realRegion :=
    { orbit := E.orbit
      stageEdge := by
        intro τ hτ
        have hold := oldEdge.stageEdge τ hτ
        exact ⟨hold.1, hold.2.trans (horbit hτ).symm⟩
      represents := by
        simpa [hP_orbit] using P.represents
      pointwiseBounded := by
        simpa [hP_orbit] using P.pointwiseBounded }
  exact
    ⟨{
      edge := E
      edge_subset_currentRegion := hE_current
      edge_subset_recenteredRegion := hE_recentered
      rootedEdge := P
      predecessorEdge := predecessorEdge
      predecessor_orbit := rfl },
      hEQ⟩

/-- Compatibility wrapper for original-OS predecessor/rooted matching. -/
theorem exists_stageMatchedRootedRepresentedGeneratorData_on
    (D : StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
      A OS stage)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (_lgc : OSLinearGrowthCondition d OS)
    (Q : Set (Fin k → ℝ))
    (hQ : Q ∈ 𝓝 0)
    (hQ_current : Q ⊆ D.currentData.realRegion)
    (hQ_recentered : Q ⊆ D.recenteredRealRegion) :
    ∃ P : StageMatchedRootedRepresentedGeneratorData D H _lgc,
      P.edge.realRegion ⊆ Q := by
  obtain ⟨P, hP⟩ :=
    exists_stageMatchedRootedRepresentedGeneratorDataOfOS_on
      D H Q hQ hQ_current hQ_recentered
  exact
    ⟨{
      edge := P.edge
      edge_subset_currentRegion := P.edge_subset_currentRegion
      edge_subset_recenteredRegion := P.edge_subset_recenteredRegion
      rootedEdge := P.rootedEdge
      predecessorEdge := P.predecessorEdge
      predecessor_orbit := P.predecessor_orbit },
      hP⟩

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
