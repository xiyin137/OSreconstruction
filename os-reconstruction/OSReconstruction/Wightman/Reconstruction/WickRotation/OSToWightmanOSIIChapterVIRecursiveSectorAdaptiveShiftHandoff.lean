/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINormalizedEnvelopeRankedSafeShift
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRecursiveSectorNormalizedEnvelopeHandoff
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation628Propagation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPhysicalAngularEquation66OSBuiltRealEdgeGrowth
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINormalizedEnvelopeWeightedSourceEnvelope
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVOneParticleTranslatedMixedDeltaProducer
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketRootedAffinePositiveHeadBridge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketRootedCanonicalFields
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketRootedSourceCurrent
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialSimultaneousStageLevel
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialStageCoherence
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialTimeSmearingStageLimit

















noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

open Section43ProductTimeApproximateIdentity
open Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData
open Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData.RootedA0BlockContinuousTranslationData

variable {d : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

namespace StrictGeneratedScalarDepthPointedData

namespace RecursiveAngleFirstBridgeRadialGeneratorChartAtRank

end RecursiveAngleFirstBridgeRadialGeneratorChartAtRank

set_option maxHeartbeats 800000 in
/-- Expose the left margin package through the pointed extension's visible
source provenance without separating its dependent packet fields. -/
theorem
    RootedRankSuccessorTargetHubMarginPointedDirectExtensionData.visibleLeftMarginData
    {d k depth rank : Nat} [NeZero d] [NeZero k]
    {OS : OsterwalderSchraderAxioms d}
    {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
    {S : C}
    {P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank}
    {lgc : OSLinearGrowthCondition d OS}
    {i : GeneratorIndex k}
    {hub : Fin k -> Real}
    {z : OSIITimeGapSpace k}
    {iota : Type*}
    {atlas : GeneratorStagePointedConvexAtlas
      (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k)
      (osiiPositiveRealTimeEmbed hub) iota}
    {epsilon : Real}
    (M : RootedRankSuccessorTargetHubMarginPointedDirectExtensionData
      S depth rank P lgc i hub z atlas epsilon)
    (q m : Nat) (hn : 1 <= q + 2) (hm : 1 <= m)
    (hnm : k = q + 2 + m - 1)
    (hi : i = ⟨q + 2, m, hn, hm, hnm⟩) :
    let E := M.construction.current
    let j : GeneratorIndex k := ⟨q + 2, m, hn, hm, hnm⟩
    let source := rootedLeftNontrivialReflectedGramSpatialSourceData
      S depth E.unsmearedSourceProvenance.atlasFamily
      E.unsmearedSourceProvenance.packet E.unsmearedSourceProvenance.roots
      j (q := q) rfl
    (forall a,
      2 * epsilon <
        E.unsmearedSourceProvenance.packet.rootedLeftBlockAnchor j a) ∧
    (fun a => rootedLeftBlockTarget j z a - 2 * epsilon) ∈
      osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) (depth + 1) (rank + 1)) ∧
    tsupport
        (source.reflectedGram.atlas.sourceStage.germ.η :
          (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex) ⊆
      reflectedTimeAnchorMarginRegion
        (E.unsmearedSourceProvenance.packet.rootedLeftBlockAnchor j)
        epsilon := by
  subst i
  let j : GeneratorIndex k := ⟨q + 2, m, hn, hm, hnm⟩
  let motive : forall
      (I' : Section43ProductTimeApproximateIdentity k)
      (anchor' : Fin k -> Real)
      (A' : AnchoredPacketTimeShellFamilyData (d := d) I' anchor')
      (R' : TripleConvolutionRootData I')
      (_H' : RootedA0BlockContinuousTranslationData OS A' R')
      (P' : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth),
      Prop :=
    fun _I _anchor A R _H P' =>
      let source := rootedLeftNontrivialReflectedGramSpatialSourceData
        S depth P' A R j (q := q) rfl
      (forall a, 2 * epsilon < A.rootedLeftBlockAnchor j a) ∧
      (fun a => rootedLeftBlockTarget j z a - 2 * epsilon) ∈
        osiiMixedTailArgumentCarrier
          (osiiStrictGeneratedMixedLogarithmicBaseAtRank
            ((q + 1) + 1) (depth + 1) (rank + 1)) ∧
      tsupport
          (source.reflectedGram.atlas.sourceStage.germ.η :
            (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex) ⊆
        reflectedTimeAnchorMarginRegion (A.rootedLeftBlockAnchor j) epsilon
  apply M.construction.current_sourceProvenance_rec motive
  have hmargin := M.leftMargin (by simp)
  have hsuccessor := M.leftSuccessorTarget (by simp)
  have hsupport :=
    (M.rooted.leftSuccessor.atGenerator q m hn hm hnm rfl).2.2
  simpa [motive, j, rootedLeftNontrivialReflectedGramSpatialSourceData] using
    And.intro hmargin (And.intro hsuccessor hsupport)

set_option maxHeartbeats 1000000 in
/-- Every point of the centered left hub-to-target segment belongs to the
source atlas's open zero-convex radial domain.  This is the source-domain fact
hidden inside the older moving-slice coverage proof. -/
theorem
    RootedTargetHubPointedDirectExtensionData.rootedLeftTailAnchorSegment_mem_sourceRadialDomain
    {d k depth : Nat} [NeZero d] [NeZero k]
    {OS : OsterwalderSchraderAxioms d}
    {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
    {S : C}
    {P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth}
    {lgc : OSLinearGrowthCondition d OS}
    {i : GeneratorIndex k}
    {hub : Fin k -> Real}
    {z : OSIITimeGapSpace k}
    {iota : Type*}
    {atlas : GeneratorStagePointedConvexAtlas
      (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k)
      (osiiPositiveRealTimeEmbed hub) iota}
    (D : RootedTargetHubPointedDirectExtensionData
      S depth P lgc i hub z atlas)
    (q m : Nat) (hn : 1 <= q + 2) (hm : 1 <= m)
    (hnm : k = q + 2 + m - 1)
    (hi : i = ⟨q + 2, m, hn, hm, hnm⟩) :
    let j : GeneratorIndex k := ⟨q + 2, m, hn, hm, hnm⟩
    let source := rootedLeftNontrivialReflectedGramSpatialSourceData
      S depth D.unsmearedSourceProvenance.atlasFamily
      D.unsmearedSourceProvenance.packet D.unsmearedSourceProvenance.roots
      j (q := q) rfl
    forall point,
      point ∈ segment Real
        (tailAnchorCenteredHubPoint
          (D.unsmearedSourceProvenance.packet.rootedLeftBlockAnchor j)
          (rootedLeftBlockHub j hub))
        (tailAnchorCenteredPoint
          (D.unsmearedSourceProvenance.packet.rootedLeftBlockAnchor j)
          (rootedLeftBlockTarget j z)) ->
      point ∈ openZeroConvexKernel
        source.reflectedGram.atlas.spatialLinearDomain := by
  subst i
  simp only
  let j : GeneratorIndex k := ⟨q + 2, m, hn, hm, hnm⟩
  let source := rootedLeftNontrivialReflectedGramSpatialSourceData
    S depth D.unsmearedSourceProvenance.atlasFamily
    D.unsmearedSourceProvenance.packet D.unsmearedSourceProvenance.roots
    j (q := q) rfl
  intro point hpoint
  obtain ⟨w, hw, hpoint_eq⟩ :=
    exists_globalSegment_of_mem_rootedLeftTailAnchorSegment
      D.unsmearedSourceProvenance.packet j hub z hpoint
  rw [D.unsmearedSourceProvenance_anchor_eq] at hpoint_eq
  rw [← hpoint_eq]
  let u := generatorChronologicalParameterComplexCLE j
    (w - osiiPositiveRealTimeEmbed D.anchorData.anchor)
  have hdomain :=
    D.approximation_parameter_mem_unsmeared_radialNativeDomain
      w (D.segment_subset_carrier hw)
  change j.splitCoordinatesCLM u ∈
      bridgedMixedHilbertPairingDomain
        {z : Complex | 0 < z.re}
        (D.unsmearedFieldData.radialLeftDomain j)
        (D.unsmearedFieldData.radialRightDomain j) at hdomain
  have hleft := hdomain.2.1
  change star (j.leftCoordinatesCLM u) ∈
    D.unsmearedFieldData.radialLeftDomain j at hleft
  change (fun a => star (j.leftCoordinatesCLM u a)) ∈
    D.unsmearedFieldData.radialLeftDomain j at hleft
  have hradial :
      (fun a => -star (u (j.leftGlobalIndex a))) ∈
        D.unsmearedFieldData.radialLeftDomain j := by
    simpa only [GeneratorIndex.leftCoordinatesCLM_apply, map_neg] using hleft
  rw [D.unsmearedSourceProvenance.family_eq] at hradial
  have hblock :
      rootedReflectedGramLeftGeneratorOpenFieldScaleBlockRealEdgeData
          S depth D.unsmearedSourceProvenance.atlasFamily
          D.unsmearedSourceProvenance.packet
          D.unsmearedSourceProvenance.roots
          D.unsmearedSourceProvenance.translation j =
        rootedScaleShiftOpenFieldBlock
          (rootedLeftNontrivialReflectedGramOpenFieldScaleBlockRealEdgeData
            S depth D.unsmearedSourceProvenance.atlasFamily
            D.unsmearedSourceProvenance.packet
            D.unsmearedSourceProvenance.roots j (q := q) rfl)
          (D.unsmearedSourceProvenance.translation.commonTailStart j) := by
    cases q <;> rfl
  have hz : (fun a => -star (u (j.leftGlobalIndex a))) ∈
      openZeroConvexKernel
        source.reflectedGram.atlas.spatialLinearDomain := by
    change (fun a => -star (u (j.leftGlobalIndex a))) ∈
      openZeroConvexKernel
        (rootedReflectedGramLeftGeneratorOpenFieldScaleBlockRealEdgeData
          S depth D.unsmearedSourceProvenance.atlasFamily
          D.unsmearedSourceProvenance.packet
          D.unsmearedSourceProvenance.roots
          D.unsmearedSourceProvenance.translation j).domain at hradial
    rw [hblock] at hradial
    exact hradial
  exact hz

set_option maxHeartbeats 1000000 in
/-- The visible rooted extension already controls the raw left moving-slice
orbit on its centered hub-to-target segment. -/
theorem
    RootedTargetHubPointedDirectExtensionData.rootedLeftTailAnchorSegment_reflectedCauchyCenter_segment_subset_movingSliceCarrier
    {d k depth : Nat} [NeZero d] [NeZero k]
    {OS : OsterwalderSchraderAxioms d}
    {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
    {S : C}
    {P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth}
    {lgc : OSLinearGrowthCondition d OS}
    {i : GeneratorIndex k}
    {hub : Fin k -> Real}
    {z : OSIITimeGapSpace k}
    {iota : Type*}
    {atlas : GeneratorStagePointedConvexAtlas
      (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k)
      (osiiPositiveRealTimeEmbed hub) iota}
    (D : RootedTargetHubPointedDirectExtensionData
      S depth P lgc i hub z atlas)
    (q m : Nat) (hn : 1 <= q + 2) (hm : 1 <= m)
    (hnm : k = q + 2 + m - 1)
    (hi : i = ⟨q + 2, m, hn, hm, hnm⟩) :
    let j : GeneratorIndex k := ⟨q + 2, m, hn, hm, hnm⟩
    let source := rootedLeftNontrivialReflectedGramSpatialSourceData
      S depth D.unsmearedSourceProvenance.atlasFamily
      D.unsmearedSourceProvenance.packet D.unsmearedSourceProvenance.roots
      j (q := q) rfl
    forall point,
      point ∈ segment Real
        (tailAnchorCenteredHubPoint
          (D.unsmearedSourceProvenance.packet.rootedLeftBlockAnchor j)
          (rootedLeftBlockHub j hub))
        (tailAnchorCenteredPoint
          (D.unsmearedSourceProvenance.packet.rootedLeftBlockAnchor j)
          (rootedLeftBlockTarget j z)) ->
      segment Real
          (0 : Fin ((q + 1) + (q + 1)) -> Complex)
          (reflectedCauchyCenter point) ⊆
        reflectedMovingSliceCarrier
          source.reflectedGram.atlas.sourceStage.stage
          source.reflectedGram.atlas.sourceStage.germ.η := by
  subst i
  simp only
  let j : GeneratorIndex k := ⟨q + 2, m, hn, hm, hnm⟩
  let source := rootedLeftNontrivialReflectedGramSpatialSourceData
    S depth D.unsmearedSourceProvenance.atlasFamily
    D.unsmearedSourceProvenance.packet D.unsmearedSourceProvenance.roots
    j (q := q) rfl
  intro point hpoint
  apply
    source.reflectedCauchyCenter_segment_subset_movingSliceCarrier_of_mem_radialDomain
  exact
    RootedTargetHubPointedDirectExtensionData.rootedLeftTailAnchorSegment_mem_sourceRadialDomain
      D q m hn hm hnm rfl point hpoint

set_option maxHeartbeats 1200000 in
/-- The retained left margin directly supplies one normalized local orbit on
the shifted target-hub segment. -/
noncomputable def
    RootedRankSuccessorTargetHubMarginPointedDirectExtensionData.leftLocalOrbitCoverageOnShiftedSegment
    {d k depth rank t : Nat} [NeZero d] [NeZero k]
    {OS : OsterwalderSchraderAxioms d}
    {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
    {S : C}
    {P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank}
    {lgc : OSLinearGrowthCondition d OS}
    {i : GeneratorIndex k}
    {hub : Fin k -> Real}
    {z : OSIITimeGapSpace k}
    {iota : Type*}
    {atlas : GeneratorStagePointedConvexAtlas
      (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k)
      (osiiPositiveRealTimeEmbed hub) iota}
    {epsilon : Real}
    {bound : forall arity,
      SchwartzMap (Section43SpatialSpace d arity) Complex -> Real}
    {Denv : VI2NormalizedEnvelopeFamilyData
      (CanonicalGeneratorStageLevelProvider.toSimultaneousTimeContinuationStageLevel
        (OS := OS) S) t epsilon bound}
    {target : forall arity, Set (Fin arity -> Complex)}
    (M : RootedRankSuccessorTargetHubMarginPointedDirectExtensionData
      S depth rank P lgc i hub z atlas epsilon)
    (Cenv : VI2NormalizedEnvelopeCoverageData Denv target)
    (htube_target : forall arity,
      osiiLogarithmicTube
          (osiiStrictGeneratedLogarithmicBaseAtRank
            arity (depth + 1) (rank + 1)) ⊆
        target arity)
    (hepsilon : 0 < epsilon)
    (q m : Nat) (hn : 1 <= q + 2) (hm : 1 <= m)
    (hnm : k = q + 2 + m - 1)
    (hi : i = ⟨q + 2, m, hn, hm, hnm⟩) :
    let E := M.construction.current
    let j : GeneratorIndex k := ⟨q + 2, m, hn, hm, hnm⟩
    let source := rootedLeftNontrivialReflectedGramSpatialSourceData
      S depth E.unsmearedSourceProvenance.atlasFamily
      E.unsmearedSourceProvenance.packet E.unsmearedSourceProvenance.roots
      j (q := q) rfl
    {O : VI2NormalizedReflectedLocalOrbitCoverageData Denv target
        source.reflectedGram.atlas.sourceStage.stage
        source.reflectedGram.atlas.sourceStage.germ.η //
      forall point,
        point ∈ segment Real
          (tailAnchorCenteredHubPoint
            (fun a =>
              E.unsmearedSourceProvenance.packet.rootedLeftBlockAnchor j a -
                2 * epsilon)
            (fun a => rootedLeftBlockHub j hub a - 2 * epsilon))
          (tailAnchorCenteredPoint
            (fun a =>
              E.unsmearedSourceProvenance.packet.rootedLeftBlockAnchor j a -
                2 * epsilon)
            (fun a => rootedLeftBlockTarget j z a - 2 * epsilon)) ->
        reflectedCauchyCenter point ∈ O.domain} := by
  subst i
  simp only
  let E := M.construction.current
  let j : GeneratorIndex k := ⟨q + 2, m, hn, hm, hnm⟩
  let source := rootedLeftNontrivialReflectedGramSpatialSourceData
    S depth E.unsmearedSourceProvenance.atlasFamily
    E.unsmearedSourceProvenance.packet E.unsmearedSourceProvenance.roots
    j (q := q) rfl
  obtain ⟨hmargin, hzshift, hsupport⟩ :=
    RootedRankSuccessorTargetHubMarginPointedDirectExtensionData.visibleLeftMarginData
      M q m hn hm hnm rfl
  have hanchor :
      (fun a =>
        E.unsmearedSourceProvenance.packet.rootedLeftBlockAnchor j a -
          2 * epsilon) ∈
        section43TimeStrictPositiveRegion ((q + 1) + 1) := by
    simpa [E, j] using
      (sub_two_mul_margin_mem_strictPositive hmargin)
  have hanchor_hub :
      forall a, E.unsmearedSourceProvenance.anchor a <= hub a := by
    intro a
    rw [E.unsmearedSourceProvenance_anchor_eq]
    exact E.anchorData.anchor_le_hub a
  have hhub :
      forall a,
        E.unsmearedSourceProvenance.packet.rootedLeftBlockAnchor j a -
            2 * epsilon <=
          rootedLeftBlockHub j hub a - 2 * epsilon := by
    intro a
    have hle :=
      E.unsmearedSourceProvenance.packet.rootedLeftBlockAnchor_le_hub
        j hub hanchor_hub a
    linarith
  have htranslated_dominates : forall sigma,
      sigma ∈ tsupport
          ((SCV.translateSchwartz
              (fun _ : Fin ((q + 1) + ((q + 1) + 1)) => epsilon)
              source.reflectedGram.atlas.sourceStage.germ.η :
            SchwartzMap
              (Fin ((q + 1) + ((q + 1) + 1)) -> Real) Complex) :
            (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex) ->
        ReflectedTimeDominatesTailAnchor
          (fun a =>
            E.unsmearedSourceProvenance.packet.rootedLeftBlockAnchor j a -
              2 * epsilon)
          sigma := by
    intro sigma hsigma
    rw [tsupport_translateSchwartz_eq_preimage] at hsigma
    change sigma +
        (fun _ : Fin ((q + 1) + ((q + 1) + 1)) => epsilon) ∈
      tsupport
        (source.reflectedGram.atlas.sourceStage.germ.η :
          (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex) at hsigma
    have hdom :=
      reflectedTimeAnchorMarginRegion_sub_const_dominates
        hepsilon hmargin (hsupport hsigma)
    simpa [Pi.add_apply] using hdom
  have hraw : forall point,
      point ∈ segment Real
        (tailAnchorCenteredHubPoint
          (fun a =>
            E.unsmearedSourceProvenance.packet.rootedLeftBlockAnchor j a -
              2 * epsilon)
          (fun a => rootedLeftBlockHub j hub a - 2 * epsilon))
        (tailAnchorCenteredPoint
          (fun a =>
            E.unsmearedSourceProvenance.packet.rootedLeftBlockAnchor j a -
              2 * epsilon)
          (fun a => rootedLeftBlockTarget j z a - 2 * epsilon)) ->
      segment Real
          (0 : Fin ((q + 1) + (q + 1)) -> Complex)
          (reflectedCauchyCenter point) ⊆
        reflectedMovingSliceCarrier
          source.reflectedGram.atlas.sourceStage.stage
          source.reflectedGram.atlas.sourceStage.germ.η := by
    intro point hpoint
    have hhub_center :
        tailAnchorCenteredHubPoint
            (fun a =>
              E.unsmearedSourceProvenance.packet.rootedLeftBlockAnchor j a -
                2 * epsilon)
            (fun a => rootedLeftBlockHub j hub a - 2 * epsilon) =
          tailAnchorCenteredHubPoint
            (E.unsmearedSourceProvenance.packet.rootedLeftBlockAnchor j)
            (rootedLeftBlockHub j hub) := by
      exact
        tailAnchorCenteredHubPoint_sub_const
          (E.unsmearedSourceProvenance.packet.rootedLeftBlockAnchor j)
          (rootedLeftBlockHub j hub) (2 * epsilon)
    have htarget_center :
        tailAnchorCenteredPoint
            (fun a =>
              E.unsmearedSourceProvenance.packet.rootedLeftBlockAnchor j a -
                2 * epsilon)
            (fun a => rootedLeftBlockTarget j z a - 2 * epsilon) =
          tailAnchorCenteredPoint
            (E.unsmearedSourceProvenance.packet.rootedLeftBlockAnchor j)
            (rootedLeftBlockTarget j z) := by
      ext a
      simp [tailAnchorCenteredPoint]
    have hpoint' :
        point ∈ segment Real
          (tailAnchorCenteredHubPoint
            (E.unsmearedSourceProvenance.packet.rootedLeftBlockAnchor j)
            (rootedLeftBlockHub j hub))
          (tailAnchorCenteredPoint
            (E.unsmearedSourceProvenance.packet.rootedLeftBlockAnchor j)
            (rootedLeftBlockTarget j z)) := by
      rw [hhub_center, htarget_center] at hpoint
      exact hpoint
    exact
      RootedTargetHubPointedDirectExtensionData.rootedLeftTailAnchorSegment_reflectedCauchyCenter_segment_subset_movingSliceCarrier
        E q m hn hm hnm rfl point hpoint'
  exact
    VI2NormalizedReflectedLocalOrbitCoverageData.ofRankSuccessorTargetHubSegmentWithCenters
      Cenv source.reflectedGram.atlas.sourceStage.stage
      source.reflectedGram.atlas.sourceStage.germ.η
      source.reflectedGram.atlas.sourceStage.germ.η_compact
      depth rank (htube_target _)
      (fun a =>
        E.unsmearedSourceProvenance.packet.rootedLeftBlockAnchor j a -
          2 * epsilon)
      (fun a => rootedLeftBlockHub j hub a - 2 * epsilon)
      hanchor hhub
      (fun a => rootedLeftBlockTarget j z a - 2 * epsilon)
      hzshift htranslated_dominates hraw

/-- Any two honest rooted extensions for one ranked chart agree at its
target.  The adaptive margin construction may select a different local
extension from the canonical rank-atlas choice, but both branches agree with
the predecessor on the open convex overlap through the common hub. -/
theorem rootedTargetHubPointedDirectExtension_distribution_eq_selectedAtRank_target
    {d k depth rank : Nat} [NeZero d] [NeZero k]
    {OS : OsterwalderSchraderAxioms d}
    {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
    {S : C}
    {P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank}
    {lgc : OSLinearGrowthCondition d OS}
    {hub : Fin k -> Real}
    (hhub : hub ∈ section43TimeStrictPositiveRegion k)
    {iota : Type*}
    {atlas : GeneratorStagePointedConvexAtlas
      (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k)
      (osiiPositiveRealTimeEmbed hub) iota}
    (a : RootedStrictGeneratedTargetHubChartAtRank k depth rank)
    (E : RootedTargetHubPointedDirectExtensionData
      S depth P.toAtlasFamily lgc a.generator hub a.target atlas) :
    E.extension.distribution a.generator a.target =
      (selectedRootedTargetHubPointedDirectExtensionAtRank
        S depth rank P lgc hub hhub atlas a).extension.distribution
        a.generator a.target := by
  let D := selectedRootedTargetHubPointedDirectExtensionAtRank
    S depth rank P lgc hub hhub atlas a
  let A := CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k
  let U : Set (OSIITimeGapSpace k) := E.carrier ∩ D.carrier
  have hU_open : IsOpen U :=
    E.carrier_open.inter D.carrier_open
  have hU_connected : IsConnected U := by
    apply (E.carrier_convex.inter D.carrier_convex).isConnected
    exact
      ⟨osiiPositiveRealTimeEmbed hub,
        E.hub_mem_carrier, D.hub_mem_carrier⟩
  let V : Set (OSIITimeGapSpace k) := U ∩ A.carrier
  have hV_open : IsOpen V :=
    hU_open.inter A.carrier_open
  have hhub_A : osiiPositiveRealTimeEmbed hub ∈ A.carrier :=
    (CanonicalGeneratorStageLevelProvider.hasCanonicalReducedCompactEdges
      (OS := OS) S k).positiveReal_mem_carrier hub hhub
  have hV_nonempty : V.Nonempty := by
    exact
      ⟨osiiPositiveRealTimeEmbed hub,
        ⟨⟨E.hub_mem_carrier, D.hub_mem_carrier⟩, hhub_A⟩⟩
  have hEq :
      Set.EqOn
        (E.extension.distribution a.generator)
        (D.extension.distribution a.generator) U := by
    apply weaklyHolomorphic_eqOn_of_eqOn_open
      hU_open hU_connected hV_open hV_nonempty Set.inter_subset_left
      (fun chi =>
        (E.extension.weaklyHolomorphic a.generator chi).mono
          (Set.inter_subset_left.trans E.carrier_subset_extensionDomain))
      (fun chi =>
        (D.extension.weaklyHolomorphic a.generator chi).mono
          (Set.inter_subset_right.trans D.carrier_subset_extensionDomain))
    intro w hw
    exact
      (E.extension.agreesOnOld a.generator
        ⟨E.carrier_subset_extensionDomain hw.1.1, hw.2⟩).trans
      (D.extension.agreesOnOld a.generator
        ⟨D.carrier_subset_extensionDomain hw.1.2, hw.2⟩).symm
  exact hEq ⟨E.target_mem_carrier, D.target_mem_carrier⟩

namespace TargetIncludedCompactLogTargetReflectedOrbitData

end TargetIncludedCompactLogTargetReflectedOrbitData

namespace RootedGeneratorSelectedCompactSegmentReflectedTargetData

end RootedGeneratorSelectedCompactSegmentReflectedTargetData

namespace RootedGeneratorSelectedCompactSegmentReflectedTargetData

end RootedGeneratorSelectedCompactSegmentReflectedTargetData

namespace RootedGeneratorSelectedCompactOrbitTargetData

end RootedGeneratorSelectedCompactOrbitTargetData

namespace RootedGeneratorSelectedCompactOrbitTargetData

end RootedGeneratorSelectedCompactOrbitTargetData

namespace RootedGeneratorAsymmetricWeightedGramContinuationData

variable
  {d k depth t : Nat} [NeZero d] [NeZero k]
  {OS : OsterwalderSchraderAxioms d}
  {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
  {S : C}
  {P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth}
  {lgc : OSLinearGrowthCondition d OS}
  {i : GeneratorIndex k}
  {hub : Fin k -> Real}
  {z : OSIITimeGapSpace k}
  {iota : Type*}
  {atlas : GeneratorStagePointedConvexAtlas
    (CanonicalGeneratorStageLevelProvider.stage (OS := OS) S k)
    (osiiPositiveRealTimeEmbed hub) iota}
  {D0 : RootedTargetHubPointedDirectExtensionData
    S depth P lgc i hub z atlas}
  {D : RootedTargetHubPointedDirectExtensionData
    S depth P lgc i hub z atlas}
  {epsilon : Real}
  {target : forall arity, Set (Fin arity -> Complex)}
  {H : VI2NormalizedTargetSeminormBoundData
    (CanonicalGeneratorStageLevelProvider.toSimultaneousTimeContinuationStageLevel
      (OS := OS) S) t epsilon target}
  {test : SchwartzMap (Section43SpatialSpace d k) Complex}
  {Bleft Bright : Real}

end RootedGeneratorAsymmetricWeightedGramContinuationData

namespace RecursiveSectorAdaptiveZeroBetaSelectedVI2GramChartPackageData

end RecursiveSectorAdaptiveZeroBetaSelectedVI2GramChartPackageData

/-- Reuse one initial positive hub floor at every outer depth and analytic
rank.  Both inductions retain the hub itself, so only the dependent hub type
changes; the numerical floor is deliberately copied unchanged. -/
noncomputable def fixedPositiveHubFloorDataAtDepthRank
    (D0 : StrictGeneratedScalarDepthPointedData OS 0)
    (lgc : OSLinearGrowthCondition d OS)
    (q depth rank : Nat)
    (H : PositiveHubFloorData (D0.pointed.hub q)) :
    PositiveHubFloorData
      (((D0.depthInduction lgc depth).recursiveSectorRankInduction
        lgc rank).pointed.hub q) where
  floor := H.floor
  floor_pos := H.floor_pos
  floor_le := by
    intro i
    have hhub :
        ((D0.depthInduction lgc depth).recursiveSectorRankInduction
          lgc rank).pointed.hub q =
          D0.pointed.hub q := by
      simp [recursiveSectorRankInduction]
    rw [hhub]
    exact H.floor_le i

@[simp] theorem fixedPositiveHubFloorDataAtDepthRank_floor
    (D0 : StrictGeneratedScalarDepthPointedData OS 0)
    (lgc : OSLinearGrowthCondition d OS)
    (q depth rank : Nat)
    (H : PositiveHubFloorData (D0.pointed.hub q)) :
    (fixedPositiveHubFloorDataAtDepthRank
      D0 lgc q depth rank H).floor = H.floor :=
  rfl

/-- Every retained depth/rank stage agrees with the depth-zero source stage
on the strict positive-real edge.

The outer-depth and inner-rank constructions only extend carriers.  This
keeps endpoint estimates honest: positive-real values do not acquire a
geometry-dependent constant merely because the adaptive route retained a
later depth or rank. -/
theorem recursiveSectorRankInduction_distribution_eq_depthZero_of_positiveReal
    (D0 : StrictGeneratedScalarDepthPointedData OS 0)
    (lgc : OSLinearGrowthCondition d OS)
    (depth rank arity : Nat)
    (tau : Fin arity -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion arity) :
    (((D0.depthInduction lgc depth).recursiveSectorRankInduction
      lgc rank).pointed.stageLevel.stage arity).distribution
        (osiiPositiveRealTimeEmbed tau) =
      (D0.pointed.stageLevel.stage arity).distribution
        (osiiPositiveRealTimeEmbed tau) := by
  let D := D0.depthInduction lgc depth
  have hz0 :
      osiiPositiveRealTimeEmbed tau ∈
        (D0.pointed.stageLevel.stage arity).carrier :=
    (D0.pointed.canonicalEdges arity).positiveReal_mem_carrier tau htau
  have hdepth :
      (D.pointed.stageLevel.stage arity).distribution
          (osiiPositiveRealTimeEmbed tau) =
        (D0.pointed.stageLevel.stage arity).distribution
          (osiiPositiveRealTimeEmbed tau) := by
    simpa [D] using
      D0.depthInduction_distribution_eq_zero lgc depth arity hz0
  have hzD :
      osiiPositiveRealTimeEmbed tau ∈
        (D.pointed.stageLevel.stage arity).carrier :=
    (D.pointed.canonicalEdges arity).positiveReal_mem_carrier tau htau
  have hzRankZero :
      osiiPositiveRealTimeEmbed tau ∈
        ((D.pointed.scalarRankInduction
          depth D.strictGeneratedCarrier_subset lgc 0
          ).pointed.stageLevel.stage arity).carrier := by
    simpa using hzD
  have hrank :
      ((D.recursiveSectorRankInduction lgc rank
        ).pointed.stageLevel.stage arity).distribution
          (osiiPositiveRealTimeEmbed tau) =
        (D.pointed.stageLevel.stage arity).distribution
          (osiiPositiveRealTimeEmbed tau) := by
    simpa [recursiveSectorRankInduction] using
      D.pointed.scalarRankInduction_distribution_eq_of_le
        depth D.strictGeneratedCarrier_subset lgc
        (Nat.zero_le rank) hzRankZero
  exact hrank.trans hdepth

/-- Every retained finite-rank source distribution agrees pointwise with the
complete next outer-depth distribution on the retained carrier.

This is the equality half of the next-depth handoff.  It is the useful
mathematical statement underneath the older constant-bound wrapper: a
boundary-distance majorant can now be evaluated at the same point on both
stages. -/
theorem recursiveSectorRankInduction_distribution_eq_nextDepth
    (D0 : StrictGeneratedScalarDepthPointedData OS 0)
    (lgc : OSLinearGrowthCondition d OS)
    (depth rank arity : Nat)
    {z : OSIITimeGapSpace arity}
    (hz : z ∈
      ((CanonicalGeneratorStageLevelProvider.toSimultaneousTimeContinuationStageLevel
        (OS := OS)
        (((D0.depthInduction lgc depth).recursiveSectorRankInduction
          lgc rank).pointed)).stage arity).carrier) :
    ((CanonicalGeneratorStageLevelProvider.toSimultaneousTimeContinuationStageLevel
        (OS := OS)
        (((D0.depthInduction lgc depth).recursiveSectorRankInduction
          lgc rank).pointed)).stage arity).distribution z =
      ((D0.depthInduction lgc (depth + 1)
        ).pointed.stageLevel.stage arity).distribution z := by
  let D := D0.depthInduction lgc depth
  have hzrank :
      z ∈ ((D.pointed.scalarRankInduction
        depth D.strictGeneratedCarrier_subset lgc rank
        ).pointed.stageLevel.stage arity).carrier := by
    simpa [D, StrictGeneratedScalarDepthPointedData.recursiveSectorRankInduction,
      CanonicalGeneratorStageLevelProvider.toSimultaneousTimeContinuationStageLevel]
      using hz
  have heq :=
    D.next_extends_rankInduction lgc rank arity hzrank
  calc
    ((CanonicalGeneratorStageLevelProvider.toSimultaneousTimeContinuationStageLevel
        (OS := OS)
        (((D0.depthInduction lgc depth).recursiveSectorRankInduction
          lgc rank).pointed)).stage arity).distribution z =
        ((D.pointed.scalarRankInduction
          depth D.strictGeneratedCarrier_subset lgc rank
          ).pointed.stageLevel.stage arity).distribution z := by
      rfl
    _ = ((D.next lgc).pointed.stageLevel.stage arity).distribution z :=
      heq.symm
    _ = ((D0.depthInduction lgc (depth + 1)
        ).pointed.stageLevel.stage arity).distribution z := by
      rfl

namespace RecursiveSectorAdaptiveZeroBetaSelectedVI2GramChartPackageData

/-- The fixed-hub radial route has one canonical boundary-controlled shift
for each retained depth/rank chart.

Keeping this choice explicit prevents later interfaces from quantifying over
arbitrary shift records whose epsilon merely happens to equal the safe
radial value. -/
noncomputable def selectedRadialBoundaryControlledShift
    (D0 : StrictGeneratedScalarDepthPointedData OS 0)
    (lgc : OSLinearGrowthCondition d OS)
    (q t : Nat)
    (H : PositiveHubFloorData (D0.pointed.hub q))
    (depth rank : Nat)
    (R : RecursiveAngleRadialGeneratorChartAtRank
      (q + 1) depth rank)
    (hz : R.chart.target ∈ osiiTimeRightHalfPlane (q + 1)) :
    OSIIVI2BoundaryControlledShiftData
      t (q + 1) R.chart.target := by
  let Hrank :=
    fixedPositiveHubFloorDataAtDepthRank D0 lgc q depth rank H
  let inverseCoefficient : Real :=
    12 * (2 : Real) ^ (depth + 1) * (2 * H.floor⁻¹ + 2)
  exact
    OSIIVI2BoundaryControlledShiftData.ofInverseBoundaryControl
      (by omega) hz
      (rootedRecursiveNormalizationEpsilon depth Hrank R.chart.target)
      inverseCoefficient
      (rootedRecursiveNormalizationEpsilon_pos depth Hrank hz)
      (rootedRecursiveNormalizationEpsilon_le_canonical depth Hrank hz)
      (by
        simpa [inverseCoefficient, Hrank,
          fixedPositiveHubFloorDataAtDepthRank] using
          (rootedRecursiveNormalizationEpsilon_inv_le_boundary
            depth Hrank hz))

@[simp]
theorem selectedRadialBoundaryControlledShift_epsilon
    (D0 : StrictGeneratedScalarDepthPointedData OS 0)
    (lgc : OSLinearGrowthCondition d OS)
    (q t : Nat)
    (H : PositiveHubFloorData (D0.pointed.hub q))
    (depth rank : Nat)
    (R : RecursiveAngleRadialGeneratorChartAtRank
      (q + 1) depth rank)
    (hz : R.chart.target ∈ osiiTimeRightHalfPlane (q + 1)) :
    (selectedRadialBoundaryControlledShift
      D0 lgc q t H depth rank R hz).epsilon =
      rootedRecursiveNormalizationEpsilon depth
        (fixedPositiveHubFloorDataAtDepthRank
          D0 lgc q depth rank H) R.chart.target :=
  rfl

end RecursiveSectorAdaptiveZeroBetaSelectedVI2GramChartPackageData

namespace RecursiveSectorAdaptiveSelectedVI2GramDepthProducerData

variable
  {D0 : StrictGeneratedScalarDepthPointedData OS 0}
  {lgc : OSLinearGrowthCondition d OS}
  {q t : Nat}
  {alpha : SchwartzMap
    (Section43SpatialSpace d (q + 1)) Complex -> Real}
  {beta : Nat}

end RecursiveSectorAdaptiveSelectedVI2GramDepthProducerData

end StrictGeneratedScalarDepthPointedData

namespace InitialGeneratedLogarithmicStageLevelData

end InitialGeneratedLogarithmicStageLevelData

end OSIIChapterV
end OSReconstruction
