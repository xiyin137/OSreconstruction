/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorRadialPointedAtlas
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRootedTargetHubDirectExtension















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {OS : OsterwalderSchraderAxioms d}
  {C : Type*}
  [CanonicalGeneratorStageLevelProvider OS C]
  {S : C}
  {depth : ℕ}
  {P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth}
  {lgc : OSLinearGrowthCondition d OS}
  {ι : Type*}

/-- The exact qualitative pointed target-and-hub extension. Its visible
data are only those needed by source-compatible convex-core gluing; no
arity-growth premise or quantitative approximation package is required. -/
structure RootedTargetHubPointedDirectExtensionDataOfOS
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (i : GeneratorIndex k)
    (hub : Fin k → ℝ)
    (z : OSIITimeGapSpace k)
    (_atlas :
      GeneratorStagePointedConvexAtlas
        (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S k)
        (osiiPositiveRealTimeEmbed hub) ι) where
  anchorData : TargetHubHalfAnchorData hub z
  extension :
    GeneratorStageExtensionData
      (CanonicalGeneratorStageLevelProvider.stage
        (OS := OS) S k)
  carrier : Set (OSIITimeGapSpace k)
  carrier_open : IsOpen carrier
  carrier_convex : Convex ℝ carrier
  carrier_subset_extensionDomain :
    carrier ⊆ extension.domain i
  hub_mem_carrier : osiiPositiveRealTimeEmbed hub ∈ carrier
  target_mem_carrier : z ∈ carrier

/-- One target-local rooted extension using only pointed convex-atlas
provenance for the predecessor.  The private analytic choices are compressed
to the absolute convex chart needed by successor gluing. -/
structure RootedTargetHubPointedDirectExtensionData
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (hub : Fin k → ℝ)
    (z : OSIITimeGapSpace k)
    (_atlas :
      GeneratorStagePointedConvexAtlas
        (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S k)
        (osiiPositiveRealTimeEmbed hub) ι) where
  anchorData : TargetHubHalfAnchorData hub z
  extension :
    GeneratorStageExtensionData
      (CanonicalGeneratorStageLevelProvider.stage
        (OS := OS) S k)
  carrier : Set (OSIITimeGapSpace k)
  carrier_open : IsOpen carrier
  carrier_convex : Convex ℝ carrier
  carrier_subset_extensionDomain :
    carrier ⊆ extension.domain i
  hub_mem_carrier : osiiPositiveRealTimeEmbed hub ∈ carrier
  target_mem_carrier : z ∈ carrier
  unsmearedFieldData :
    GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k
  unsmearedSourceProvenance :
    RootedAllSplitSourceProvenanceData
      S depth unsmearedFieldData
  unsmearedSourceProvenance_anchor_eq :
    unsmearedSourceProvenance.anchor = anchorData.anchor
  /-- The compact centered parameter set from which the selected absolute
  carrier was cut.  Retaining it is what makes compact-uniform Hilbert-field
  estimates available after the private convex-core choice is hidden. -/
  compactCenteredParameterSet : Set (OSIITimeGapSpace k)
  compactCenteredParameterSet_compact :
    IsCompact compactCenteredParameterSet
  carrier_centered_mem_compactParameterSet : forall w, w ∈ carrier ->
    w - osiiPositiveRealTimeEmbed anchorData.anchor ∈
      compactCenteredParameterSet
  compactCenteredParameterSet_parameter_mem_unsmearedRadialNativeDomain :
    forall v, v ∈ compactCenteredParameterSet ->
      generatorChronologicalParameterComplexCLE i v ∈
        unsmearedFieldData.radialNativeDomain i
  fieldData : GeneratorOpenHilbertFieldScaleFamilyData OS k
  fieldData_leftDomain_eq_unsmeared :
    fieldData.leftDomain i = unsmearedFieldData.leftDomain i
  fieldData_rightDomain_eq_unsmeared :
    fieldData.rightDomain i = unsmearedFieldData.rightDomain i
  fieldData_leftField_eq_unsmeared : forall scale mode point,
    fieldData.leftField i scale mode point =
      unsmearedFieldData.leftField i scale mode point
  fieldData_rightField_norm_le_unsmeared : forall scale mode point,
    ‖fieldData.rightField i scale mode point‖ <=
      ‖unsmearedFieldData.rightField i scale mode point‖
  approximation :
    Nat -> OSIITimeGapSpace k -> OSIISpatialDistribution d k
  approximation_eq_fieldData : forall scale w,
    approximation scale w =
      fieldData.twoScaleApproximation lgc
        (rootedGeneratorSplitSpatialLiftCLM i)
        i scale scale
        (generatorChronologicalParameterComplexCLE i
          (w - osiiPositiveRealTimeEmbed anchorData.anchor))
  approximation_parameter_mem_unsmeared_radialNativeDomain :
    forall w, w ∈ carrier ->
      generatorChronologicalParameterComplexCLE i
          (w - osiiPositiveRealTimeEmbed anchorData.anchor) ∈
        unsmearedFieldData.radialNativeDomain i
  approximation_parameter_mem_fieldData_domain :
    forall w, w ∈ carrier ->
      generatorChronologicalParameterComplexCLE i
          (w - osiiPositiveRealTimeEmbed anchorData.anchor) ∈
        fieldData.domain i
  approximation_bridge_positive : forall w, w ∈ carrier ->
    0 < ((generatorChronologicalParameterComplexCLE i
      (w - osiiPositiveRealTimeEmbed anchorData.anchor))
        i.bridgeGlobalIndex).re
  approximation_tendsto : forall w, w ∈ carrier -> forall chi,
    Filter.Tendsto (fun scale => approximation scale w chi) Filter.atTop
      (nhds (extension.distribution i w chi))

namespace RootedTargetHubPointedDirectExtensionData

variable
  {i : GeneratorIndex k}
  {hub : Fin k → ℝ}
  {z : OSIITimeGapSpace k}
  {atlas :
    GeneratorStagePointedConvexAtlas
      (CanonicalGeneratorStageLevelProvider.stage
        (OS := OS) S k)
      (osiiPositiveRealTimeEmbed hub) ι}

theorem segment_subset_carrier
    (D :
      RootedTargetHubPointedDirectExtensionData
        S depth P lgc i hub z atlas) :
    segment ℝ (osiiPositiveRealTimeEmbed hub) z ⊆ D.carrier :=
  D.carrier_convex.segment_subset
    D.hub_mem_carrier D.target_mem_carrier

/-- Shrink a rooted target-and-hub chart inside any open domain containing
its distinguished segment.

The analytic extension, reflected-source provenance, and approximation family
are unchanged.  Only the visible convex chart is replaced by a relatively
compact core in \`D.carrier ∩ U\`; its centered compact parameter witness is
then rebuilt from the new closure.  This is the route-facing way to impose a
later chart-local geometric constraint without strengthening the generic
rooted-extension constructor. -/
noncomputable def restrictToOpenSegmentDomain
    (D :
      RootedTargetHubPointedDirectExtensionData
        S depth P lgc i hub z atlas)
    (U : Set (OSIITimeGapSpace k))
    (hU_open : IsOpen U)
    (hsegment :
      segment ℝ (osiiPositiveRealTimeEmbed hub) z ⊆ U) :
    {D' :
        RootedTargetHubPointedDirectExtensionData
          S depth P lgc i hub z atlas //
      D'.carrier ⊆ U} := by
  let V : Set (OSIITimeGapSpace k) := D.carrier ∩ U
  have hV_open : IsOpen V := D.carrier_open.inter hU_open
  have hsegmentV :
      segment ℝ (osiiPositiveRealTimeEmbed hub) z ⊆ V := by
    intro w hw
    exact ⟨D.segment_subset_carrier hw, hsegment hw⟩
  let core :=
    RelativelyCompactConvexCoreData.selectedOfSegmentSubsetOpen
      hV_open hsegmentV
  let centeredCompact : Set (OSIITimeGapSpace k) :=
    (fun w =>
      w - osiiPositiveRealTimeEmbed D.anchorData.anchor) ''
      closure core.carrier
  have hcore_subset_D : core.carrier ⊆ D.carrier := by
    intro w hw
    exact (core.carrier_closure_subset (subset_closure hw)).1
  have hclosure_subset_D : closure core.carrier ⊆ D.carrier := by
    intro w hw
    exact (core.carrier_closure_subset hw).1
  let D' :
      RootedTargetHubPointedDirectExtensionData
        S depth P lgc i hub z atlas :=
    { anchorData := D.anchorData
      extension := D.extension
      carrier := core.carrier
      carrier_open := core.carrier_open
      carrier_convex := core.carrier_convex
      carrier_subset_extensionDomain := by
        intro w hw
        exact D.carrier_subset_extensionDomain (hcore_subset_D hw)
      hub_mem_carrier := core.left_mem
      target_mem_carrier := core.right_mem
      unsmearedFieldData := D.unsmearedFieldData
      unsmearedSourceProvenance := D.unsmearedSourceProvenance
      unsmearedSourceProvenance_anchor_eq :=
        D.unsmearedSourceProvenance_anchor_eq
      compactCenteredParameterSet := centeredCompact
      compactCenteredParameterSet_compact := by
        apply core.carrier_closure_compact.image
        fun_prop
      carrier_centered_mem_compactParameterSet := by
        intro w hw
        exact ⟨w, subset_closure hw, rfl⟩
      compactCenteredParameterSet_parameter_mem_unsmearedRadialNativeDomain := by
        rintro _v ⟨w, hw, rfl⟩
        exact
          D.approximation_parameter_mem_unsmeared_radialNativeDomain
            w (hclosure_subset_D hw)
      fieldData := D.fieldData
      fieldData_leftDomain_eq_unsmeared :=
        D.fieldData_leftDomain_eq_unsmeared
      fieldData_rightDomain_eq_unsmeared :=
        D.fieldData_rightDomain_eq_unsmeared
      fieldData_leftField_eq_unsmeared :=
        D.fieldData_leftField_eq_unsmeared
      fieldData_rightField_norm_le_unsmeared :=
        D.fieldData_rightField_norm_le_unsmeared
      approximation := D.approximation
      approximation_eq_fieldData := D.approximation_eq_fieldData
      approximation_parameter_mem_unsmeared_radialNativeDomain := by
        intro w hw
        exact
          D.approximation_parameter_mem_unsmeared_radialNativeDomain
            w (hcore_subset_D hw)
      approximation_parameter_mem_fieldData_domain := by
        intro w hw
        exact
          D.approximation_parameter_mem_fieldData_domain
            w (hcore_subset_D hw)
      approximation_bridge_positive := by
        intro w hw
        exact D.approximation_bridge_positive w (hcore_subset_D hw)
      approximation_tendsto := by
        intro w hw chi
        exact D.approximation_tendsto w (hcore_subset_D hw) chi }
  refine ⟨D', ?_⟩
  intro w hw
  change w ∈ core.carrier at hw
  exact (core.carrier_closure_subset (subset_closure hw)).2

@[simp]
theorem restrictToOpenSegmentDomain_anchorData
    (D :
      RootedTargetHubPointedDirectExtensionData
        S depth P lgc i hub z atlas)
    (U : Set (OSIITimeGapSpace k))
    (hU_open : IsOpen U)
    (hsegment :
      segment ℝ (osiiPositiveRealTimeEmbed hub) z ⊆ U) :
    (D.restrictToOpenSegmentDomain U hU_open hsegment).1.anchorData =
      D.anchorData := rfl

@[simp]
theorem restrictToOpenSegmentDomain_extension
    (D :
      RootedTargetHubPointedDirectExtensionData
        S depth P lgc i hub z atlas)
    (U : Set (OSIITimeGapSpace k))
    (hU_open : IsOpen U)
    (hsegment :
      segment ℝ (osiiPositiveRealTimeEmbed hub) z ⊆ U) :
    (D.restrictToOpenSegmentDomain U hU_open hsegment).1.extension =
      D.extension := rfl

@[simp]
theorem restrictToOpenSegmentDomain_unsmearedSourceProvenance
    (D :
      RootedTargetHubPointedDirectExtensionData
        S depth P lgc i hub z atlas)
    (U : Set (OSIITimeGapSpace k))
    (hU_open : IsOpen U)
    (hsegment :
      segment ℝ (osiiPositiveRealTimeEmbed hub) z ⊆ U) :
    (D.restrictToOpenSegmentDomain U hU_open hsegment
      ).1.unsmearedSourceProvenance =
      D.unsmearedSourceProvenance := rfl

end RootedTargetHubPointedDirectExtensionData

set_option maxHeartbeats 1000000 in
/-- One original-OS rooted reflected-Gram replacement gives the complete
qualitative pointed hub-to-target extension from its actual represented
predecessor source edge. -/
theorem nonempty_rootedTargetHubPointedDirectExtensionDataOfOS_of_rootedData
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (i : GeneratorIndex k)
    (hub : Fin k → ℝ)
    (atlas :
      GeneratorStagePointedConvexAtlas
        (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S k)
        (osiiPositiveRealTimeEmbed hub) ι)
    (z : OSIITimeGapSpace k)
    (C0 : TargetHubHalfAnchorData hub z)
    (Q :
      AnchorLocalRootedReflectedGramRadialProducerPackageOfOS
        S depth P C0.anchor)
    (D :
      RootedTargetHubAdaptedReflectedGramData
        S depth P Q.packet Q.roots
          Q.holomorphic.toContinuousTranslationData i hub z) :
    Nonempty
      (RootedTargetHubPointedDirectExtensionDataOfOS
        S depth P i hub z atlas) := by
  let Q' := Q.withStageWideReflectedGram D.adapted
  let core :=
    RelativelyCompactConvexCoreData.selectedOfSegmentSubsetOpen
      (Q'.radialData.radialChronologicalDomain_open i)
      (by
        simpa [Q',
          AnchorLocalRootedReflectedGramRadialProducerPackageOfOS.radialData,
          AnchorLocalRootedReflectedGramRadialProducerPackageOfOS.withStageWideReflectedGram]
          using
            D.centeredHub_target_segment_subset_radialChronologicalDomain
              (C0.anchor_lt_hub i.bridgeGlobalIndex)
              (C0.anchor_lt_target i.bridgeGlobalIndex))
  have hanchor_carrier :
      osiiPositiveRealTimeEmbed C0.anchor ∈
        (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S k).carrier :=
    (CanonicalGeneratorStageLevelProvider.hasCanonicalReducedCompactEdges
      (OS := OS) S k).positiveReal_mem_carrier
      C0.anchor C0.anchor_positive
  obtain ⟨seedChart, hseed⟩ :=
    Set.mem_iUnion.mp
      (atlas.carrier_subset_iUnion hanchor_carrier)
  let U : Set (Fin k → ℝ) :=
    osiiPositiveRealTimeEmbed ⁻¹' atlas.domain seedChart
  have hU_open : IsOpen U :=
    (atlas.domain_open seedChart).preimage
      continuous_osiiPositiveRealTimeEmbed
  have hanchor_U : C0.anchor ∈ U := hseed
  obtain ⟨X, hX⟩ :=
    exists_stageMatchedRootedReflectedGramRadialGeneratorDataOfOS_of_anchor_mem_open
      S depth D.adapted Q.current Q.holomorphic
      U hU_open hanchor_U
  let B : GeneratorSpatialApproximationFamily d k :=
    (rootedReflectedGramRadialGeneratorTwoScaleApproximationFamilyOfOS
      S depth D.adapted Q.packet Q.roots Q.holomorphic).diagonal
  let F := Q'.radialData
  have hcore_domain : core.carrier ⊆ B.domain i := by
    intro w hw
    change w ∈ F.radialChronologicalDomain i
    exact core.carrier_closure_subset (subset_closure hw)
  let centeredExtension :
      GeneratorStageExtensionData
        ((CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S k).recenter C0.anchor) :=
    B.toSingleGeneratorStageExtensionDataOfRadialPointedAtlas
      X.edge.toDiagonal F
      (by
        intro j
        rfl)
      ((CanonicalGeneratorStageLevelProvider.stage
        (OS := OS) S k).recenter C0.anchor)
      (by
        change
          ((CanonicalGeneratorStageLevelProvider.stage
            (OS := OS) S k).recenter C0.anchor).HasPositiveRealEdge
              X.edge.orbit X.edge.realRegion
        rw [← X.predecessor_orbit]
        exact X.predecessorEdge.stageEdge)
      (atlas.recenter C0.anchor)
      seedChart
      (by
        change
          (0 : OSIITimeGapSpace k) +
              osiiPositiveRealTimeEmbed C0.anchor ∈
            atlas.domain seedChart
        simpa using hseed)
      (by
        intro u hu
        change
          osiiPositiveRealTimeEmbed u +
              osiiPositiveRealTimeEmbed C0.anchor ∈
            atlas.domain seedChart
        rw [← osiiPositiveRealTimeEmbed_add]
        simpa [U] using hX u hu)
      i core.carrier core.carrier_open core.carrier_convex
      hcore_domain
      core.left_mem
  have hcentered_domain :
      centeredExtension.domain i = core.carrier := by
    change
      singleGeneratorChartDomain i core.carrier i =
        core.carrier
    exact singleGeneratorChartDomain_selected i core.carrier
  let absoluteExtension :
      GeneratorStageExtensionData
        (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S k) :=
    centeredExtension.uncenter
  let absoluteCarrier : Set (OSIITimeGapSpace k) :=
    {w |
      w - osiiPositiveRealTimeEmbed C0.anchor ∈ core.carrier}
  exact
    ⟨{
      anchorData := C0
      extension := absoluteExtension
      carrier := absoluteCarrier
      carrier_open :=
        core.carrier_open.preimage
          (continuous_id.sub continuous_const)
      carrier_convex := by
        change
          Convex ℝ
            {w |
              w + (-osiiPositiveRealTimeEmbed C0.anchor) ∈
                core.carrier}
        exact
          core.carrier_convex.translate_preimage_left
            (-osiiPositiveRealTimeEmbed C0.anchor)
      carrier_subset_extensionDomain := by
        intro w hw
        change w ∈ centeredExtension.uncenter.domain i
        rw [GeneratorStageExtensionData.mem_uncenter_domain_sub,
          hcentered_domain]
        exact hw
      hub_mem_carrier := core.left_mem
      target_mem_carrier := core.right_mem }⟩

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
