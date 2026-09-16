/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.SCV.DistributionalRepresentationUniqueness
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageWideReflectedGramCommonRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorRadialStageExtension
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorStageAffineTranslation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRootedStageSuccessor













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
variable {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]

/-- The genuine original-OS reflected-Gram radial edge and recentered
predecessor edge on one common source-realization region. -/
structure StageMatchedRootedReflectedGramRadialGeneratorDataOfOS
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (D :
      StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
        A OS (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S k))
    (H : RootedA0BlockHolomorphicTranslationData OS A R) where
  edge :
    (rootedReflectedGramRadialGeneratorTwoScaleApproximationFamilyOfOS
      S depth P A R H).CommonPositiveRealEdgeData
  edge_subset_currentRegion :
    edge.realRegion ⊆ D.currentData.realRegion
  edge_subset_recenteredRegion :
    edge.realRegion ⊆ D.recenteredRealRegion
  edge_radial :
    IsPositiveRadial edge.realRegion
  edge_subset_strictPositive :
    edge.realRegion ⊆ section43TimeStrictPositiveRegion k
  represents :
    OSIITimeSpatialRepresentsDistributionOn
      (anchoredOrderedTransportDistribution
        D.currentData.current anchor)
      edge.orbit edge.realRegion
  predecessorEdge :
    ((CanonicalGeneratorStageLevelProvider.stage
      (OS := OS) S k).recenter anchor).PositiveRealEdgeData
      (anchoredOrderedTransportDistribution
        D.currentData.current anchor)
      edge.realRegion
  predecessor_orbit :
    predecessorEdge.orbit = edge.orbit

namespace StageMatchedRootedReflectedGramRadialGeneratorDataOfOS

variable
  {S : C}
  {depth : ℕ}
  {P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth}
  {D :
    StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
      A OS (CanonicalGeneratorStageLevelProvider.stage
        (OS := OS) S k)}
  {H : RootedA0BlockHolomorphicTranslationData OS A R}

/-- Glue every original-OS radial generator branch to the actual
predecessor using their common represented source distribution. -/
noncomputable def toStageExtensionDataOfConvexAtlas
    (X :
      StageMatchedRootedReflectedGramRadialGeneratorDataOfOS
        S depth P D H)
    {U : Set (Fin k → ℝ)}
    {ι : Type*}
    (atlas :
      GeneratorStageConvexAtlas
        (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S k) U ι)
    (edge_subset_atlas :
      ∀ u ∈ X.edge.realRegion, u + anchor ∈ U) :
    GeneratorStageExtensionData
      ((CanonicalGeneratorStageLevelProvider.stage
        (OS := OS) S k).recenter anchor) := by
  let T :=
    rootedReflectedGramRadialGeneratorTwoScaleApproximationFamilyOfOS
      S depth P A R H
  let F :=
    rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
      S depth P A R H.toContinuousTranslationData
  let recenteredAtlas :=
    (atlas.recenter anchor).restrictRealRegion
      (by
        intro u hu
        exact edge_subset_atlas u hu)
  exact
    T.diagonal.toStageExtensionDataOfRadialConvexAtlas
      X.edge.toDiagonal F
      (by
        intro i
        rfl)
      ((CanonicalGeneratorStageLevelProvider.stage
        (OS := OS) S k).recenter anchor)
      (by
        change
          ((CanonicalGeneratorStageLevelProvider.stage
            (OS := OS) S k).recenter anchor).HasPositiveRealEdge
              X.edge.orbit X.edge.realRegion
        rw [← X.predecessor_orbit]
        exact X.predecessorEdge.stageEdge)
      recenteredAtlas X.edge_radial

@[simp]
theorem toStageExtensionDataOfConvexAtlas_domain
    (X :
      StageMatchedRootedReflectedGramRadialGeneratorDataOfOS
        S depth P D H)
    {U : Set (Fin k → ℝ)}
    {ι : Type*}
    (atlas :
      GeneratorStageConvexAtlas
        (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S k) U ι)
    (edge_subset_atlas :
      ∀ u ∈ X.edge.realRegion, u + anchor ∈ U)
    (i : GeneratorIndex k) :
    (X.toStageExtensionDataOfConvexAtlas
      atlas edge_subset_atlas).domain i =
      (rootedReflectedGramRadialGeneratorTwoScaleApproximationFamilyOfOS
        S depth P A R H).domain i :=
  rfl

end StageMatchedRootedReflectedGramRadialGeneratorDataOfOS

/-- The reflected-Gram radial edge and the recentered predecessor edge,
retained on one common real region and representing the same current. -/
structure StageMatchedRootedReflectedGramRadialGeneratorData
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (D :
      StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
        A OS (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S k))
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS) where
  edge :
    (rootedReflectedGramRadialGeneratorTwoScaleApproximationFamily
      S depth P lgc A R H).CommonPositiveRealEdgeData
  edge_subset_currentRegion :
    edge.realRegion ⊆ D.currentData.realRegion
  edge_subset_recenteredRegion :
    edge.realRegion ⊆ D.recenteredRealRegion
  edge_radial :
    IsPositiveRadial edge.realRegion
  edge_subset_strictPositive :
    edge.realRegion ⊆ section43TimeStrictPositiveRegion k
  represents :
    OSIITimeSpatialRepresentsDistributionOn
      (anchoredOrderedTransportDistribution
        D.currentData.current anchor)
      edge.orbit edge.realRegion
  predecessorEdge :
    ((CanonicalGeneratorStageLevelProvider.stage
      (OS := OS) S k).recenter anchor).PositiveRealEdgeData
      (anchoredOrderedTransportDistribution
        D.currentData.current anchor)
      edge.realRegion
  predecessor_orbit :
    predecessorEdge.orbit = edge.orbit

namespace StageMatchedRootedReflectedGramRadialGeneratorData

variable
  {S : C}
  {depth : ℕ}
  {P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth}
  {D :
    StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
      A OS (CanonicalGeneratorStageLevelProvider.stage
        (OS := OS) S k)}
  {H : RootedA0BlockHolomorphicTranslationData OS A R}
  {lgc : OSLinearGrowthCondition d OS}

/-- The reflected-Gram radial branches form a centered extension of the
predecessor after restricting its convex atlas to the matched real edge. -/
noncomputable def toStageExtensionDataOfConvexAtlas
    (X :
      StageMatchedRootedReflectedGramRadialGeneratorData
        S depth P D H lgc)
    {U : Set (Fin k → ℝ)}
    {ι : Type*}
    (atlas :
      GeneratorStageConvexAtlas
        (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S k) U ι)
    (edge_subset_atlas :
      ∀ u ∈ X.edge.realRegion, u + anchor ∈ U) :
    GeneratorStageExtensionData
      ((CanonicalGeneratorStageLevelProvider.stage
        (OS := OS) S k).recenter anchor) := by
  let T :=
    rootedReflectedGramRadialGeneratorTwoScaleApproximationFamily
      S depth P lgc A R H
  let F :=
    rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
      S depth P A R H.toContinuousTranslationData
  let recenteredAtlas :=
    (atlas.recenter anchor).restrictRealRegion
      (by
        intro u hu
        exact edge_subset_atlas u hu)
  exact
    T.diagonal.toStageExtensionDataOfRadialConvexAtlas
      X.edge.toDiagonal F
      (by
        intro i
        rfl)
      ((CanonicalGeneratorStageLevelProvider.stage
        (OS := OS) S k).recenter anchor)
      (by
        change
          ((CanonicalGeneratorStageLevelProvider.stage
            (OS := OS) S k).recenter anchor).HasPositiveRealEdge
              X.edge.orbit X.edge.realRegion
        rw [← X.predecessor_orbit]
        exact X.predecessorEdge.stageEdge)
      recenteredAtlas X.edge_radial

@[simp]
theorem toStageExtensionDataOfConvexAtlas_domain
    (X :
      StageMatchedRootedReflectedGramRadialGeneratorData
        S depth P D H lgc)
    {U : Set (Fin k → ℝ)}
    {ι : Type*}
    (atlas :
      GeneratorStageConvexAtlas
        (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S k) U ι)
    (edge_subset_atlas :
      ∀ u ∈ X.edge.realRegion, u + anchor ∈ U)
    (i : GeneratorIndex k) :
    (X.toStageExtensionDataOfConvexAtlas
      atlas edge_subset_atlas).domain i =
      (rootedReflectedGramRadialGeneratorTwoScaleApproximationFamily
        S depth P lgc A R H).domain i :=
  rfl

end StageMatchedRootedReflectedGramRadialGeneratorData

/-- Construct the genuine original-OS predecessor-matched reflected-Gram
generator in any neighborhood common to its current and predecessor. -/
theorem exists_stageMatchedRootedReflectedGramRadialGeneratorDataOfOS_on
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (D :
      StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
        A OS (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S k))
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (Q : Set (Fin k → ℝ))
    (hQ : Q ∈ 𝓝 0)
    (hQ_current : Q ⊆ D.currentData.realRegion)
    (hQ_recentered : Q ⊆ D.recenteredRealRegion) :
    ∃ X :
        StageMatchedRootedReflectedGramRadialGeneratorDataOfOS
          S depth P D H,
      X.edge.realRegion ⊆ Q := by
  let T :=
    rootedReflectedGramRadialGeneratorTwoScaleApproximationFamilyOfOS
      S depth P A R H
  obtain
    ⟨E, hEQ, hE_radial, hE_positive, hE_represents⟩ :=
      exists_rootedReflectedGramRadialCommonPositiveRealEdgeDataOfOS_of_currentData_on
        S depth P A R H D.currentData Q hQ
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
    apply ContinuousLinearMap.ext
    intro χ
    have hnew_cont :
        ContinuousOn (fun u => E.orbit u χ) E.realRegion := by
      exact
        GeneratorSpatialApproximationFamily.CommonPositiveRealEdgeData.orbit_continuousOn
          T.diagonal E.toDiagonal χ
    have hold_cont :
        ContinuousOn (fun u => oldEdge.orbit u χ) E.realRegion :=
      ((CanonicalGeneratorStageLevelProvider.stage
        (OS := OS) S k).recenter anchor
        ).continuousOn_positiveRealEdge
          oldEdge.orbit E.realRegion oldEdge.stageEdge χ
    exact
      SCV.eqOn_inter_of_representsDistributionOn
        ((anchoredOrderedTransportDistribution
          D.currentData.current anchor).comp
            (section43OrderedPullbackTimeSpatialTensorCLM d k χ))
        E.realRegion E.realRegion
        (fun u => E.orbit u χ)
        (fun u => oldEdge.orbit u χ)
        E.realRegion_open E.realRegion_open
        hnew_cont hold_cont
        (hE_represents χ) (oldEdge.represents χ)
        ⟨hτ, hτ⟩
  let predecessorEdge :
      ((CanonicalGeneratorStageLevelProvider.stage
        (OS := OS) S k).recenter anchor).PositiveRealEdgeData
        (anchoredOrderedTransportDistribution
          D.currentData.current anchor)
        E.realRegion :=
    { orbit := E.orbit
      stageEdge := by
        intro τ hτ
        have hold := oldEdge.stageEdge τ hτ
        exact ⟨hold.1, hold.2.trans (horbit hτ).symm⟩
      represents := hE_represents
      pointwiseBounded := by
        intro χ
        obtain ⟨C, hC⟩ := oldEdge.pointwiseBounded χ
        exact
          ⟨C, fun τ hτ => by
            rw [horbit hτ]
            exact hC τ hτ⟩ }
  exact
    ⟨{
      edge := E
      edge_subset_currentRegion := hE_current
      edge_subset_recenteredRegion := hE_recentered
      edge_radial := hE_radial
      edge_subset_strictPositive := hE_positive
      represents := hE_represents
      predecessorEdge := predecessorEdge
      predecessor_orbit := rfl },
      hEQ⟩

/-- Select the original-OS predecessor-matched generator so its translated
real edge stays inside any open predecessor patch containing its anchor. -/
theorem
    exists_stageMatchedRootedReflectedGramRadialGeneratorDataOfOS_of_anchor_mem_open
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (D :
      StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
        A OS (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S k))
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (U : Set (Fin k → ℝ))
    (hU_open : IsOpen U)
    (hanchor : anchor ∈ U) :
    ∃ X :
        StageMatchedRootedReflectedGramRadialGeneratorDataOfOS
          S depth P D H,
      ∀ u ∈ X.edge.realRegion,
        u + anchor ∈ U := by
  let atlasRegion : Set (Fin k → ℝ) :=
    {u | u + anchor ∈ U}
  let Q : Set (Fin k → ℝ) :=
    D.currentData.realRegion ∩
      (D.recenteredRealRegion ∩ atlasRegion)
  have hatlas : atlasRegion ∈ 𝓝 0 := by
    exact
      hU_open.preimage
          (continuous_id.add continuous_const)
        |>.mem_nhds (by simpa [atlasRegion] using hanchor)
  have hQ : Q ∈ 𝓝 0 :=
    Filter.inter_mem
      D.currentData.realRegion_mem_nhds
      (Filter.inter_mem
        (D.recenteredRealRegion_open.mem_nhds
          D.zero_mem_recenteredRealRegion)
        hatlas)
  obtain ⟨X, hXQ⟩ :=
    exists_stageMatchedRootedReflectedGramRadialGeneratorDataOfOS_on
      S depth P D H Q hQ
      (Set.inter_subset_left)
      (Set.inter_subset_right.trans Set.inter_subset_left)
  refine ⟨X, ?_⟩
  intro u hu
  exact (hXQ hu).2.2

/-- Construct a predecessor-matched reflected-Gram radial generator inside
any neighborhood contained in both current and recentered predecessor germs. -/
theorem exists_stageMatchedRootedReflectedGramRadialGeneratorData_on
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (D :
      StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
        A OS (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S k))
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (Q : Set (Fin k → ℝ))
    (hQ : Q ∈ 𝓝 0)
    (hQ_current : Q ⊆ D.currentData.realRegion)
    (hQ_recentered : Q ⊆ D.recenteredRealRegion) :
    ∃ X :
        StageMatchedRootedReflectedGramRadialGeneratorData
          S depth P D H lgc,
      X.edge.realRegion ⊆ Q := by
  let T :=
    rootedReflectedGramRadialGeneratorTwoScaleApproximationFamily
      S depth P lgc A R H
  obtain
    ⟨E, hEQ, hE_radial, hE_positive, hE_represents⟩ :=
      exists_rootedReflectedGramRadialCommonPositiveRealEdgeData_of_currentData_on
        S depth P lgc A R H D.currentData Q hQ
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
    apply ContinuousLinearMap.ext
    intro χ
    have hnew_cont :
        ContinuousOn (fun u => E.orbit u χ) E.realRegion := by
      exact
        GeneratorSpatialApproximationFamily.CommonPositiveRealEdgeData.orbit_continuousOn
          T.diagonal E.toDiagonal χ
    have hold_cont :
        ContinuousOn (fun u => oldEdge.orbit u χ) E.realRegion :=
      ((CanonicalGeneratorStageLevelProvider.stage
        (OS := OS) S k).recenter anchor
        ).continuousOn_positiveRealEdge
          oldEdge.orbit E.realRegion oldEdge.stageEdge χ
    exact
      SCV.eqOn_inter_of_representsDistributionOn
        ((anchoredOrderedTransportDistribution
          D.currentData.current anchor).comp
            (section43OrderedPullbackTimeSpatialTensorCLM d k χ))
        E.realRegion E.realRegion
        (fun u => E.orbit u χ)
        (fun u => oldEdge.orbit u χ)
        E.realRegion_open E.realRegion_open
        hnew_cont hold_cont
        (hE_represents χ) (oldEdge.represents χ)
        ⟨hτ, hτ⟩
  let predecessorEdge :
      ((CanonicalGeneratorStageLevelProvider.stage
        (OS := OS) S k).recenter anchor).PositiveRealEdgeData
        (anchoredOrderedTransportDistribution
          D.currentData.current anchor)
        E.realRegion :=
    { orbit := E.orbit
      stageEdge := by
        intro τ hτ
        have hold := oldEdge.stageEdge τ hτ
        exact ⟨hold.1, hold.2.trans (horbit hτ).symm⟩
      represents := hE_represents
      pointwiseBounded := by
        intro χ
        obtain ⟨C, hC⟩ := oldEdge.pointwiseBounded χ
        exact
          ⟨C, fun τ hτ => by
            rw [horbit hτ]
            exact hC τ hτ⟩ }
  exact
    ⟨{
      edge := E
      edge_subset_currentRegion := hE_current
      edge_subset_recenteredRegion := hE_recentered
      edge_radial := hE_radial
      edge_subset_strictPositive := hE_positive
      represents := hE_represents
      predecessorEdge := predecessorEdge
      predecessor_orbit := rfl },
      hEQ⟩

/-- If the packet anchor lies in an open predecessor real patch, the matched
reflected-Gram edge can be selected so that its absolute translate remains in
that patch. -/
theorem
    exists_stageMatchedRootedReflectedGramRadialGeneratorData_of_anchor_mem_open
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (D :
      StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
        A OS (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S k))
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (U : Set (Fin k → ℝ))
    (hU_open : IsOpen U)
    (hanchor : anchor ∈ U) :
    ∃ X :
        StageMatchedRootedReflectedGramRadialGeneratorData
          S depth P D H lgc,
      ∀ u ∈ X.edge.realRegion,
        u + anchor ∈ U := by
  let atlasRegion : Set (Fin k → ℝ) :=
    {u | u + anchor ∈ U}
  let Q : Set (Fin k → ℝ) :=
    D.currentData.realRegion ∩
      (D.recenteredRealRegion ∩ atlasRegion)
  have hatlas : atlasRegion ∈ 𝓝 0 := by
    exact
      hU_open.preimage
          (continuous_id.add continuous_const)
        |>.mem_nhds (by simpa [atlasRegion] using hanchor)
  have hQ : Q ∈ 𝓝 0 :=
    Filter.inter_mem
      D.currentData.realRegion_mem_nhds
      (Filter.inter_mem
        (D.recenteredRealRegion_open.mem_nhds
          D.zero_mem_recenteredRealRegion)
        hatlas)
  obtain ⟨X, hXQ⟩ :=
    exists_stageMatchedRootedReflectedGramRadialGeneratorData_on
      S depth P D H lgc Q hQ
      (Set.inter_subset_left)
      (Set.inter_subset_right.trans Set.inter_subset_left)
  refine ⟨X, ?_⟩
  intro u hu
  exact (hXQ hu).2.2

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
