/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVUniformCompactTimeAnchoredLinearity
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVProductBasepointMixedDeltaProducer
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSimultaneousStageLevel
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapDistributionHolomorphy
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSourceIndexedReflectedGram
















noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d q : ℕ} [NeZero d]
variable
  {I : Section43ProductTimeApproximateIdentity (q + 1)}
  {anchor : Fin (q + 1) → ℝ}

/-- A common difference-time carrier for all scales and all spatial Schwartz
tests in the fixed-head source family.  We retain its product presentation so
that coordinatewise lower bounds on the packet carrier remain available to
later moving-slice arguments. -/
noncomputable def positiveHeadSpatialSourceCarrier
    (A :
      AnchoredPacketTimeShellFamilyData
        (d := d) I anchor) :
    Set (Fin ((q + 1) + 1) → ℝ) :=
  (fun p : ℝ × (Fin (q + 1) → ℝ) =>
    (Fin.cons p.1 p.2 : Fin ((q + 1) + 1) → ℝ)) ''
    (tsupport
        (normalizedPositiveTimeBasepointCutoff.f : ℝ → ℂ) ×ˢ
      A.carrierData.carrier)

theorem positiveHeadSpatialSourceCarrier_compact
    (A :
      AnchoredPacketTimeShellFamilyData
        (d := d) I anchor) :
    IsCompact A.positiveHeadSpatialSourceCarrier := by
  have hcons :
      Continuous
        (fun p : ℝ × (Fin (q + 1) → ℝ) =>
          (Fin.cons p.1 p.2 : Fin ((q + 1) + 1) → ℝ)) := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ ?_ i
    · exact continuous_fst
    · intro j
      fun_prop
  exact
    (normalizedPositiveTimeBasepointCutoff.compact.isCompact.prod
      A.carrierData.carrier_compact).image hcons

theorem positiveHeadSpatialSourceCarrier_positive
    (A :
      AnchoredPacketTimeShellFamilyData
        (d := d) I anchor) :
    A.positiveHeadSpatialSourceCarrier ⊆
      section43TimeStrictPositiveRegion ((q + 1) + 1) := by
  rintro τ ⟨p, hp, rfl⟩ i
  refine Fin.cases ?_ ?_ i
  · exact normalizedPositiveTimeBasepointCutoff.positive hp.1
  · intro j
    exact A.carrierData.carrier_positive hp.2 j

/-- A fixed positive lower margin for the normalized head-time cutoff. -/
noncomputable def normalizedPositiveTimeBasepointLower : ℝ :=
  Classical.choose
    (exists_positive_margin_of_isCompact_subset_Ioi
      normalizedPositiveTimeBasepointCutoff.compact.isCompact
      normalizedPositiveTimeBasepointCutoff.positive)

theorem normalizedPositiveTimeBasepointLower_pos :
    0 < normalizedPositiveTimeBasepointLower :=
  (Classical.choose_spec
    (exists_positive_margin_of_isCompact_subset_Ioi
      normalizedPositiveTimeBasepointCutoff.compact.isCompact
      normalizedPositiveTimeBasepointCutoff.positive)).1

theorem normalizedPositiveTimeBasepointLower_le
    {t : ℝ}
    (ht :
      t ∈ tsupport
        (normalizedPositiveTimeBasepointCutoff.f : ℝ → ℂ)) :
    normalizedPositiveTimeBasepointLower ≤ t :=
  (Classical.choose_spec
    (exists_positive_margin_of_isCompact_subset_Ioi
      normalizedPositiveTimeBasepointCutoff.compact.isCompact
      normalizedPositiveTimeBasepointCutoff.positive)).2 ht

/-- The head lower margin prepended to the packet anchor. -/
noncomputable def positiveHeadSpatialSourceLowerAnchor
    (A :
      AnchoredPacketTimeShellFamilyData
        (d := d) I anchor) :
    Fin ((q + 1) + 1) → ℝ :=
  Fin.cons normalizedPositiveTimeBasepointLower anchor

theorem positiveHeadSpatialSourceLowerAnchor_positive
    (A :
      AnchoredPacketTimeShellFamilyData
        (d := d) I anchor) :
    A.positiveHeadSpatialSourceLowerAnchor ∈
      section43TimeStrictPositiveRegion ((q + 1) + 1) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · simpa [positiveHeadSpatialSourceLowerAnchor] using
      normalizedPositiveTimeBasepointLower_pos
  · intro j
    simpa [positiveHeadSpatialSourceLowerAnchor] using
      A.anchor_positive j

theorem positiveHeadSpatialSourceLowerAnchor_le_carrier
    (A :
      AnchoredPacketTimeShellFamilyData
        (d := d) I anchor)
    (htail :
      ∀ τ ∈ A.carrierData.carrier, ∀ i, anchor i ≤ τ i) :
    ∀ τ ∈ A.positiveHeadSpatialSourceCarrier, ∀ i,
      A.positiveHeadSpatialSourceLowerAnchor i ≤ τ i := by
  rintro τ ⟨p, hp, rfl⟩ i
  refine Fin.cases ?_ ?_ i
  · simpa [positiveHeadSpatialSourceLowerAnchor] using
      normalizedPositiveTimeBasepointLower_le hp.1
  · intro j
    simpa [positiveHeadSpatialSourceLowerAnchor] using
      htail p.2 hp.2 j

theorem positiveHeadSpatialSource_mem_carrier
    (A :
      AnchoredPacketTimeShellFamilyData
        (d := d) I anchor)
    (N : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) ℂ) :
    A.positiveHeadSpatialSource N χ ∈
      uniformCompactTimeSourceSubmodule
        d ((q + 1) + 1) A.positiveHeadSpatialSourceCarrier := by
  intro x hx
  have htime :
      section43QTime (d := d) (n := (q + 1) + 1)
          (section43DiffCoordRealCLE d ((q + 1) + 1) x) ∈
        tsupport
          ((A.positiveProductBasepointTimeSource N).f :
            (Fin ((q + 1) + 1) → ℝ) → ℂ) := by
    exact
      osiiA0_orderedPullback_tsupport_subset_timeSet
        (d := d) χ
        (A.positiveProductBasepointTimeSource N).f
        (tsupport
          ((A.positiveProductBasepointTimeSource N).f :
            (Fin ((q + 1) + 1) → ℝ) → ℂ))
        (Subset.refl _)
        (by simpa [positiveHeadSpatialSource] using hx)
  simpa [positiveHeadSpatialSourceCarrier] using
    (section43PrependCompactPositiveTimeSource_tsupport_subset_carrier
      normalizedPositiveTimeBasepointCutoff
      (A.timeTest N)
      (A.timeTest_compact N)
      (A.timeTest_positive N)
      A.carrierData.carrier
      (by
        simpa [timeTest] using
          A.carrierData.translated_support N)
      htime)

/-- At each fixed packet scale, arbitrary spatial Schwartz data maps
continuously and linearly into the universal source space controlled by the
chosen compact carrier. -/
noncomputable def positiveHeadSpatialAnchoredSourceCLM
    (A :
      AnchoredPacketTimeShellFamilyData
        (d := d) I anchor)
    (N : ℕ) :
    SchwartzMap
        (Section43SpatialSpace d ((q + 1) + 1)) ℂ →L[ℂ]
      UniformCompactTimeSource
        d ((q + 1) + 1) A.positiveHeadSpatialSourceCarrier :=
  (section43PositiveTimeSpatialSourceCLM
      d ((q + 1) + 1)
      (A.positiveProductBasepointTimeSource N)).codRestrict
    (uniformCompactTimeSourceSubmodule
      d ((q + 1) + 1) A.positiveHeadSpatialSourceCarrier)
    (A.positiveHeadSpatialSource_mem_carrier N)

@[simp]
theorem positiveHeadSpatialAnchoredSourceCLM_source
    (A :
      AnchoredPacketTimeShellFamilyData
        (d := d) I anchor)
    (N : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) ℂ) :
    UniformCompactTimeSource.source
        (A.positiveHeadSpatialAnchoredSourceCLM N χ) =
      A.positiveHeadSpatialSource N χ :=
  rfl

/-- The universal fixed-carrier anchored package associated with one
fixed-head source family and one simultaneous predecessor level. -/
structure PositiveHeadUniversalAnchoredAtlasData
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (A :
      AnchoredPacketTimeShellFamilyData
        (d := d) I anchor) where
  sourceStage :
    UniformCompactTimeMixedStageOrbitSourceData OS
      (fun a :
          UniformCompactTimeSource
            d ((q + 1) + 1) A.positiveHeadSpatialSourceCarrier =>
        UniformCompactTimeSource.source a)
  sourceStage_eq :
    sourceStage.stage = L.reflectedPairStage (q := q)
  gram :
    UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a :
          UniformCompactTimeSource
            d ((q + 1) + 1) A.positiveHeadSpatialSourceCarrier =>
        UniformCompactTimeSource.source a)
      sourceStage.stage sourceStage.germ

namespace PositiveHeadUniversalAnchoredAtlasData

variable
  {L : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {A :
    AnchoredPacketTimeShellFamilyData
      (d := d) I anchor}

/-- The open part of the maximal anchored atlas on which both scalar
moving-slice evaluations used to prove source continuity are available. -/
def spatialLinearDomain
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A) :
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
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A) :
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
    · rw [show (fun z : Fin (q + 1) → ℂ =>
          reflectedCauchyCenter z (Fin.castAdd (q + 1) i)) =
          (fun z => star (z i)) by
            funext z
            exact reflectedCauchyCenter_left z i]
      fun_prop
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

/-- The initial Gram polydisc already lies in the open source-linear part of
the global anchored atlas. -/
theorem initialGramPolydisc_subset_spatialLinearDomain
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A) :
    SCV.Polydisc
        (0 : Fin (q + 1) → ℂ) (fun _ => D.gram.gramRadius) ⊆
      D.spatialLinearDomain := by
  intro z hz
  let P :=
    D.gram.toInitialSourceIndexedReflectedGramHilbertFieldData
      OS
      (fun a :
          UniformCompactTimeSource
            d ((q + 1) + 1) A.positiveHeadSpatialSourceCarrier =>
        UniformCompactTimeSource.source a)
      D.sourceStage.stage D.sourceStage.germ
  let A₀ :=
    D.gram.toInitialSourceIndexedAnchoredReflectedGramHilbertFieldData
      D.sourceStage.stage D.sourceStage.germ
  let C :
      SourceIndexedAnchoredReflectedGramChart
        (OSHilbertSpace OS)
        (UniformCompactTimeSource
          d ((q + 1) + 1) A.positiveHeadSpatialSourceCarrier)
        (q + 1)
        (fun a b => (D.gram.cauchy a b).scalar)
        (0 : Fin (q + 1) → ℂ)
        (fun a => D.gram.hilbert.field a 0) :=
    { gram := P, anchored := A₀ }
  have hzP : z ∈ P.domain := by
    change z ∈ SCV.Polydisc
      (0 : Fin (q + 1) → ℂ) (fun _ => D.gram.gramRadius)
    exact hz
  refine ⟨?_, ?_, ?_⟩
  · exact Set.mem_iUnion.mpr ⟨C, hzP⟩
  · exact A₀.anchorPair_subset_scalarDomain z hzP
  · let a :
        UniformCompactTimeSource
          d ((q + 1) + 1) A.positiveHeadSpatialSourceCarrier :=
      A.positiveHeadSpatialAnchoredSourceCLM 0 0
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

/-- On the complete open source-linear atlas domain, the global anchored
field is continuous and linear in the full spatial Schwartz test. -/
noncomputable def spatialFieldCLM
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (scale : ℕ)
    (z : Fin (q + 1) → ℂ)
    (hz : z ∈ D.spatialLinearDomain) :
    SchwartzMap
        (Section43SpatialSpace d ((q + 1) + 1)) ℂ →L[ℂ]
      OSHilbertSpace OS :=
  (D.gram.anchoredAtlasFieldContinuousLinearMap
      D.sourceStage.stage D.sourceStage.germ z
      hz.1 hz.2.1 hz.2.2).comp
    (A.positiveHeadSpatialAnchoredSourceCLM scale)

@[simp]
theorem spatialFieldCLM_apply
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (scale : ℕ)
    (z : Fin (q + 1) → ℂ)
    (hz : z ∈ D.spatialLinearDomain)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) ℂ) :
    D.spatialFieldCLM scale z hz χ =
      D.gram.anchoredAtlasField
        D.sourceStage.stage D.sourceStage.germ
        (A.positiveHeadSpatialAnchoredSourceCLM scale χ) z :=
  rfl

/-- The global anchored field evaluated at a generated mixed point, now
continuous and linear in the full spatial Schwartz test. -/
noncomputable def generatedSpatialFieldCLM
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
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
    (A.positiveHeadSpatialAnchoredSourceCLM scale)

@[simp]
theorem generatedSpatialFieldCLM_apply
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
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
    D.generatedSpatialFieldCLM
        hgenerated scale z hz χ =
      D.gram.anchoredAtlasField
        D.sourceStage.stage D.sourceStage.germ
        (A.positiveHeadSpatialAnchoredSourceCLM scale χ) z :=
  rfl

/-- For every fixed spatial test and packet scale, the global anchored field
is holomorphic on the complete anchored-atlas domain. -/
theorem generatedSpatialField_holomorphic
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (scale : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) ℂ) :
    DifferentiableOn ℂ
      (fun z =>
        D.gram.anchoredAtlasField
          D.sourceStage.stage D.sourceStage.germ
          (A.positiveHeadSpatialAnchoredSourceCLM scale χ) z)
      (D.gram.anchoredAtlasCoveredDomain
        D.sourceStage.stage D.sourceStage.germ) :=
  D.gram.anchoredAtlasField_holomorphic
    D.sourceStage.stage D.sourceStage.germ
    (A.positiveHeadSpatialAnchoredSourceCLM scale χ)

/-- The global spatial field retains the honest translated positive-time
source on the common local real edge. -/
theorem generatedSpatialField_realEdge
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (scale : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) ℂ) :
    HasPositiveTimeSourceRealEdge OS
      (fun z =>
        D.gram.anchoredAtlasField
          D.sourceStage.stage D.sourceStage.germ
          (A.positiveHeadSpatialAnchoredSourceCLM scale χ) z)
      (localPositiveTimeParameterTranslate
        (A.positiveHeadSpatialSource scale χ)
        (fun r : Fin (q + 1) =>
          chronologicalTimeSourceDirection (d := d) r))
      (D.gram.anchoredAtlasRealRegion
        D.sourceStage.stage D.sourceStage.germ) := by
  simpa only [positiveHeadSpatialAnchoredSourceCLM_source] using
    D.gram.anchoredAtlasField_realEdge
      D.sourceStage.stage D.sourceStage.germ
      (A.positiveHeadSpatialAnchoredSourceCLM scale χ)

end PositiveHeadUniversalAnchoredAtlasData

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
