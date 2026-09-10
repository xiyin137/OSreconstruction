/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVUniformCompactTimeAnchoredLinearity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSimultaneousStageLevel















noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d q : ℕ} [NeZero d]

/-- The universal anchored package over all positive-time sources carried by
one compact strict-positive difference-time set. -/
structure UniversalCompactCarrierAnchoredAtlasData
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (K : Set (Fin ((q + 1) + 1) → ℝ)) where
  sourceStage :
    UniformCompactTimeMixedStageOrbitSourceData OS
      (fun a :
          UniformCompactTimeSource d ((q + 1) + 1) K =>
        UniformCompactTimeSource.source a)
  sourceStage_eq :
    sourceStage.stage = L.reflectedPairStage (q := q)
  gram :
    UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a :
          UniformCompactTimeSource d ((q + 1) + 1) K =>
        UniformCompactTimeSource.source a)
      sourceStage.stage sourceStage.germ

namespace UniversalCompactCarrierAnchoredAtlasData

end UniversalCompactCarrierAnchoredAtlasData

set_option maxHeartbeats 800000 in
/-- Build the universal anchored package from a previously selected mixed
reflected germ, retaining the selected germ definitionally in the resulting
stage-orbit package. -/
theorem exists_universalCompactCarrierAnchoredAtlasData_of_germ
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (H : L.HasCanonicalReducedCompactEdges OS)
    (K : Set (Fin ((q + 1) + 1) → ℝ))
    (hK_compact : IsCompact K)
    (hK_positive :
      K ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (germ :
      UniformCompactTimeMixedReflectedSourceFamilyData OS
        (fun a :
            UniformCompactTimeSource d ((q + 1) + 1) K =>
          UniformCompactTimeSource.source a)) :
    ∃ D : UniversalCompactCarrierAnchoredAtlasData L OS K,
      D.sourceStage.germ = germ := by
  let f :
      UniformCompactTimeSource d ((q + 1) + 1) K →
        euclideanPositiveTimeSubmodule (d := d) ((q + 1) + 1) :=
    fun a => UniformCompactTimeSource.source a
  have hf :
      HasUniformCompactStrictPositiveDifferenceTimeSupport
        (fun a => (f a).1) := by
    simpa [f] using
      (UniformCompactTimeSource.hasUniformCompactStrictPositiveDifferenceTimeSupport
        (K := K) hK_compact hK_positive)
  obtain ⟨edge⟩ :=
    H ((q + 1) + ((q + 1) + 1))
      (tsupport
        (germ.η :
          (Fin ((q + 1) + ((q + 1) + 1)) → ℝ) → ℂ))
      germ.η_compact germ.η_support
  let S :
      UniformCompactTimeMixedCanonicalCutoffStageData OS f := {
    uniformSupport := hf
    germ := germ
    stageCutoff := edge.cutoff
    stageCutoff_support := edge.cutoff_support
    stage := L.reflectedPairStage
    realRegion := edge.realRegion
    realRegion_open := edge.realRegion_open
    cutoff_support := edge.compactCarrier_subset
    edge := edge.edge
    stageCutoff_one_on := by
      filter_upwards [germ.cutoff_one_on] with u hu
      intro ab x hx
      exact
        edge.reducedTimeCutoffWeight_eq_one_of_auxiliary
          germ.η Set.Subset.rfl x (hu ab x hx) }
  let T := S.toStageOrbitSourceData OS f
  obtain ⟨G⟩ :=
    exists_uniformCompactTimeMixedHilbertGramFamilyData_of_stageOrbitSource
      (q := q) (inferInstance : IsScalarTower ℝ ℂ ℂ)
      (inferInstance :
        IsScalarTower ℝ ℂ
          (Fin ((q + 1) + (q + 1)) → ℂ))
      OS f hf T
  exact ⟨{
    sourceStage := T
    sourceStage_eq := rfl
    gram := G }, rfl⟩

set_option maxHeartbeats 800000 in
/-- Canonical compact reduced edges construct the universal anchored package
for every compact strict-positive source carrier. -/
theorem nonempty_universalCompactCarrierAnchoredAtlasData
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (H : L.HasCanonicalReducedCompactEdges OS)
    (K : Set (Fin ((q + 1) + 1) → ℝ))
    (hK_compact : IsCompact K)
    (hK_positive :
      K ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1)) :
    Nonempty (UniversalCompactCarrierAnchoredAtlasData L OS K) := by
  let f :
      UniformCompactTimeSource d ((q + 1) + 1) K →
        euclideanPositiveTimeSubmodule (d := d) ((q + 1) + 1) :=
    fun a => UniformCompactTimeSource.source a
  have hf :
      HasUniformCompactStrictPositiveDifferenceTimeSupport
        (fun a => (f a).1) := by
    simpa [f] using
      (UniformCompactTimeSource.hasUniformCompactStrictPositiveDifferenceTimeSupport
        (K := K) hK_compact hK_positive)
  obtain ⟨germ⟩ :=
    exists_uniformCompactTimeMixedReflectedSourceFamilyData OS f hf
  obtain ⟨D, _hD_germ⟩ :=
    exists_universalCompactCarrierAnchoredAtlasData_of_germ
      L OS H K hK_compact hK_positive germ
  exact ⟨D⟩

namespace UniversalCompactCarrierAnchoredAtlasData

variable
  {L : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {K : Set (Fin ((q + 1) + 1) → ℝ)}

/-- The open part of the maximal anchored atlas on which both scalar
moving-slice evaluations used for source continuity are available. -/
def spatialLinearDomain
    (D : UniversalCompactCarrierAnchoredAtlasData L OS K) :
    Set (Fin (q + 1) → ℂ) :=
  {z |
    z ∈ D.gram.anchoredAtlasCoveredDomain
        D.sourceStage.stage D.sourceStage.germ ∧
      reflectedAnchorPair (0 : Fin (q + 1) → ℂ) z ∈
        reflectedMovingSliceCarrier
          D.sourceStage.stage D.sourceStage.germ.η ∧
      reflectedCauchyCenter z ∈
        reflectedMovingSliceCarrier
          D.sourceStage.stage D.sourceStage.germ.η}

theorem spatialLinearDomain_open
    (D : UniversalCompactCarrierAnchoredAtlasData L OS K) :
    IsOpen D.spatialLinearDomain := by
  have hanchor :
      Continuous (fun z : Fin (q + 1) → ℂ =>
        reflectedAnchorPair (0 : Fin (q + 1) → ℂ) z) := by
    apply continuous_pi
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa [reflectedAnchorPair] using
        (continuous_const :
          Continuous (fun _ : Fin (q + 1) → ℂ => (0 : ℂ)))
    · convert
        (continuous_apply i :
          Continuous (fun z : Fin (q + 1) → ℂ => z i)) using 1
      funext z
      simpa using
        congrFun
          (reflectedAnchorPair_right
            (0 : Fin (q + 1) → ℂ) z) i
  have hcenter :
      Continuous (reflectedCauchyCenter :
        (Fin (q + 1) → ℂ) →
          Fin ((q + 1) + (q + 1)) → ℂ) := by
    apply continuous_pi
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa [reflectedCauchyCenter] using
        (continuous_star.comp
          (continuous_apply i :
            Continuous (fun z : Fin (q + 1) → ℂ => z i)))
    · convert
        (continuous_apply i :
          Continuous (fun z : Fin (q + 1) → ℂ => z i)) using 1
      funext z
      simpa using reflectedCauchyCenter_right z i
  rw [spatialLinearDomain]
  exact
    (D.gram.anchoredAtlasCoveredDomain_open
        D.sourceStage.stage D.sourceStage.germ).inter
      (((isOpen_reflectedMovingSliceCarrier
            D.sourceStage.stage D.sourceStage.germ.η
            D.sourceStage.germ.η_compact).preimage hanchor).inter
        ((isOpen_reflectedMovingSliceCarrier
            D.sourceStage.stage D.sourceStage.germ.η
            D.sourceStage.germ.η_compact).preimage hcenter))

/-- The initial Gram polydisc lies in the open source-linear part of the
universal anchored atlas. -/
theorem initialGramPolydisc_subset_spatialLinearDomain
    (D : UniversalCompactCarrierAnchoredAtlasData L OS K) :
    SCV.Polydisc
        (0 : Fin (q + 1) → ℂ) (fun _ => D.gram.gramRadius) ⊆
      D.spatialLinearDomain := by
  intro z hz
  let P :=
    D.gram.toInitialSourceIndexedReflectedGramHilbertFieldData
      OS
      (fun a :
          UniformCompactTimeSource d ((q + 1) + 1) K =>
        UniformCompactTimeSource.source a)
      D.sourceStage.stage D.sourceStage.germ
  let A₀ :=
    D.gram.toInitialSourceIndexedAnchoredReflectedGramHilbertFieldData
      D.sourceStage.stage D.sourceStage.germ
  let C :
      SourceIndexedAnchoredReflectedGramChart
        (OSHilbertSpace OS)
        (UniformCompactTimeSource d ((q + 1) + 1) K)
        (q + 1)
        (fun a b => (D.gram.cauchy a b).scalar)
        (0 : Fin (q + 1) → ℂ)
        (fun a => D.gram.hilbert.field a 0) :=
    { gram := P, anchored := A₀ }
  have hzP : z ∈ P.domain := by
    simpa [P] using hz
  refine ⟨?_, ?_, ?_⟩
  · exact Set.mem_iUnion.mpr ⟨C, hzP⟩
  · exact A₀.anchorPair_subset_scalarDomain z hzP
  · let a : UniformCompactTimeSource d ((q + 1) + 1) K := 0
    apply P.kernelDomain_subset_scalarDomain a a
    constructor
    · have hleft :
          star (fun i =>
            reflectedCauchyCenter z (Fin.castAdd (q + 1) i)) = z := by
        funext i
        simp [reflectedCauchyCenter]
      rw [hleft]
      exact hzP
    · have hright :
          (fun i =>
            reflectedCauchyCenter z (Fin.natAdd (q + 1) i)) = z := by
        funext i
        exact reflectedCauchyCenter_right z i
      rw [hright]
      exact hzP

/-- Compose the universal source-linear field with any scale-indexed
continuous linear spatial source family landing in the fixed carrier. -/
noncomputable def spatialFieldCLM
    (D : UniversalCompactCarrierAnchoredAtlasData L OS K)
    (sourceCLM :
      ℕ →
        SchwartzMap
            (Section43SpatialSpace d ((q + 1) + 1)) ℂ →L[ℂ]
          UniformCompactTimeSource d ((q + 1) + 1) K)
    (scale : ℕ)
    (z : Fin (q + 1) → ℂ)
    (hz : z ∈ D.spatialLinearDomain) :
    SchwartzMap
        (Section43SpatialSpace d ((q + 1) + 1)) ℂ →L[ℂ]
      OSHilbertSpace OS :=
  (D.gram.anchoredAtlasFieldContinuousLinearMap
      D.sourceStage.stage D.sourceStage.germ z
      hz.1 hz.2.1 hz.2.2).comp
    (sourceCLM scale)

@[simp]
theorem spatialFieldCLM_apply
    (D : UniversalCompactCarrierAnchoredAtlasData L OS K)
    (sourceCLM :
      ℕ →
        SchwartzMap
            (Section43SpatialSpace d ((q + 1) + 1)) ℂ →L[ℂ]
          UniformCompactTimeSource d ((q + 1) + 1) K)
    (scale : ℕ)
    (z : Fin (q + 1) → ℂ)
    (hz : z ∈ D.spatialLinearDomain)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) ℂ) :
    D.spatialFieldCLM sourceCLM scale z hz χ =
      D.gram.anchoredAtlasField
        D.sourceStage.stage D.sourceStage.germ
        (sourceCLM scale χ) z :=
  rfl

/-- The universal anchored field at a generated mixed point, continuously
linear in the full spatial Schwartz test. -/
noncomputable def generatedSpatialFieldCLM
    (D : UniversalCompactCarrierAnchoredAtlasData L OS K)
    (sourceCLM :
      ℕ →
        SchwartzMap
            (Section43SpatialSpace d ((q + 1) + 1)) ℂ →L[ℂ]
          UniformCompactTimeSource d ((q + 1) + 1) K)
    {depth : ℕ}
    (hgenerated :
      osiiTimeArgumentCarrier
          (osiiGeneratedLogarithmicBase
            ((q + 1) + ((q + 1) + 1)) depth) ⊆
        D.sourceStage.stage.carrier)
    (scale : ℕ)
    (z : Fin (q + 1) → ℂ)
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiGeneratedMixedLogarithmicBase
          ((q + 1) + 1) depth)) :
    SchwartzMap
        (Section43SpatialSpace d ((q + 1) + 1)) ℂ →L[ℂ]
      OSHilbertSpace OS :=
  (D.gram.anchoredAtlasGeneratedFieldContinuousLinearMap
      D.sourceStage.stage D.sourceStage.germ
      hgenerated z hz).comp
    (sourceCLM scale)

@[simp]
theorem generatedSpatialFieldCLM_apply
    (D : UniversalCompactCarrierAnchoredAtlasData L OS K)
    (sourceCLM :
      ℕ →
        SchwartzMap
            (Section43SpatialSpace d ((q + 1) + 1)) ℂ →L[ℂ]
          UniformCompactTimeSource d ((q + 1) + 1) K)
    {depth : ℕ}
    (hgenerated :
      osiiTimeArgumentCarrier
          (osiiGeneratedLogarithmicBase
            ((q + 1) + ((q + 1) + 1)) depth) ⊆
        D.sourceStage.stage.carrier)
    (scale : ℕ)
    (z : Fin (q + 1) → ℂ)
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiGeneratedMixedLogarithmicBase
          ((q + 1) + 1) depth))
    (χ : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) ℂ) :
    D.generatedSpatialFieldCLM sourceCLM
        hgenerated scale z hz χ =
      D.gram.anchoredAtlasField
        D.sourceStage.stage D.sourceStage.germ
        (sourceCLM scale χ) z :=
  rfl

/-- For every fixed source family, spatial test, and scale, the global
anchored field is holomorphic on the complete covered domain. -/
theorem generatedSpatialField_holomorphic
    (D : UniversalCompactCarrierAnchoredAtlasData L OS K)
    (sourceCLM :
      ℕ →
        SchwartzMap
            (Section43SpatialSpace d ((q + 1) + 1)) ℂ →L[ℂ]
          UniformCompactTimeSource d ((q + 1) + 1) K)
    (scale : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) ℂ) :
    DifferentiableOn ℂ
      (fun z =>
        D.gram.anchoredAtlasField
          D.sourceStage.stage D.sourceStage.germ
          (sourceCLM scale χ) z)
      (D.gram.anchoredAtlasCoveredDomain
        D.sourceStage.stage D.sourceStage.germ) :=
  D.gram.anchoredAtlasField_holomorphic
    D.sourceStage.stage D.sourceStage.germ
    (sourceCLM scale χ)

/-- The global field retains the actual positive-time source supplied by the
carrier-valued source map on the common local real edge. -/
theorem generatedSpatialField_realEdge
    (D : UniversalCompactCarrierAnchoredAtlasData L OS K)
    (sourceCLM :
      ℕ →
        SchwartzMap
            (Section43SpatialSpace d ((q + 1) + 1)) ℂ →L[ℂ]
          UniformCompactTimeSource d ((q + 1) + 1) K)
    (scale : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) ℂ) :
    HasPositiveTimeSourceRealEdge OS
      (fun z =>
        D.gram.anchoredAtlasField
          D.sourceStage.stage D.sourceStage.germ
          (sourceCLM scale χ) z)
      (localPositiveTimeParameterTranslate
        (UniformCompactTimeSource.source (sourceCLM scale χ))
        (fun r : Fin (q + 1) =>
          chronologicalTimeSourceDirection (d := d) r))
      (D.gram.anchoredAtlasRealRegion
        D.sourceStage.stage D.sourceStage.germ) :=
  D.gram.anchoredAtlasField_realEdge
    D.sourceStage.stage D.sourceStage.germ
    (sourceCLM scale χ)

end UniversalCompactCarrierAnchoredAtlasData

end OSIIChapterV
end OSReconstruction
