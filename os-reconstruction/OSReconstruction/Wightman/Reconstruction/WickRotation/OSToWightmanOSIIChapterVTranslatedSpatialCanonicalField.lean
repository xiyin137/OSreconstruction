import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVOneParticleTranslatedMixedDeltaProducer
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketA0FieldBounds

/-!
# Canonical translated-product spatial Hilbert fields

The translated mixed-delta producer already constructs the common Gram
family needed for every spatial Schwartz profile. This file retains that
family, packages its finite-scale fields as continuous linear maps in the
spatial variable, and exposes the existing continuous-translation interface.

The one-particle endpoint is handled separately by the proved empty-parameter
mixed-delta producer. No sharp-time Hilbert-vector limit is assumed.
-/

noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d q : ℕ} [NeZero d]

/-- A continuous translated A0 field together with the openness and
holomorphy already present in its canonical Hilbert-field construction. -/
structure LocalReflectedA0HolomorphicTranslationFieldData
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (OS : OsterwalderSchraderAxioms d)
    (n m : ℕ)
    (translatedSource :
      ℕ → (Fin m → ℝ) → SchwartzMap E ℂ →
        euclideanPositiveTimeSubmodule (d := d) n)
    extends
      LocalReflectedA0ContinuousTranslationFieldData
        OS n m translatedSource where
  domain_open : IsOpen domain
  domain_convex : Convex ℝ domain
  domain_star : ∀ z ∈ domain, star z ∈ domain
  field_holomorphic :
    ∀ N χ, DifferentiableOn ℂ (fun z => field N z χ) domain

namespace LocalReflectedA0HolomorphicTranslationFieldData

variable
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {OS : OsterwalderSchraderAxioms d}
  {n m : ℕ}
  {translatedSource translatedSource' :
    ℕ → (Fin m → ℝ) → SchwartzMap E ℂ →
      euclideanPositiveTimeSubmodule (d := d) n}

/-- Reindex an exact translated-source identity without discarding the
analytic data carried by the field. -/
noncomputable def congrTranslatedSource
    (D :
      LocalReflectedA0HolomorphicTranslationFieldData
        OS n m translatedSource)
    (hsource :
      ∀ N x χ, translatedSource N x χ = translatedSource' N x χ) :
    LocalReflectedA0HolomorphicTranslationFieldData
      OS n m translatedSource' where
  toLocalReflectedA0ContinuousTranslationFieldData :=
    D.toLocalReflectedA0ContinuousTranslationFieldData.congrTranslatedSource
      hsource
  domain_open := D.domain_open
  domain_convex := D.domain_convex
  domain_star := D.domain_star
  field_holomorphic := D.field_holomorphic

end LocalReflectedA0HolomorphicTranslationFieldData

namespace Section43ProductTimeApproximateIdentity

/-- The retained canonical predecessor and mixed Gram family for one
translated product approximate identity with at least two particles. -/
structure TranslatedSpatialCanonicalFieldData
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (I : Section43ProductTimeApproximateIdentity ((q + 1) + 1))
    (τ : Fin ((q + 1) + 1) → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1)) where
  predecessor :
    TranslatedMixedDeltaOrderedSourcePredecessorData L OS I τ hτ
  gram :
    UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun p :
          ℕ × SchwartzMap
            (Section43SpatialSpace d ((q + 1) + 1)) ℂ =>
        I.translatedPositiveTimeSpatialSource
          τ hτ p.2 (p.1 + predecessor.tailStart))
      predecessor.sourceEdge.stage predecessor.sourceEdge.germ

/-- Canonical reduced compact edges construct the retained translated spatial
field package. -/
theorem nonempty_translatedSpatialCanonicalFieldData
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (H : L.HasCanonicalReducedCompactEdges OS)
    (I : Section43ProductTimeApproximateIdentity ((q + 1) + 1))
    (τ : Fin ((q + 1) + 1) → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1)) :
    Nonempty (TranslatedSpatialCanonicalFieldData L OS I τ hτ) := by
  obtain ⟨D⟩ :=
    L.exists_translatedMixedDeltaCanonicalCutoffPredecessorData
      (I := I) (τ := τ) (hτ := hτ) H
  let E := D.toOrderedSourcePredecessorData
  obtain ⟨G, _Ψ, _hΨ, _hΨhol⟩ :=
    E.exists_mixedGram_and_translatedHolomorphicHilbertField
      (inferInstance : IsScalarTower ℝ ℂ ℂ)
      (inferInstance :
        IsScalarTower ℝ ℂ
          (Fin ((q + 1) + (q + 1)) → ℂ))
      (0 :
        SchwartzMap
          (Section43SpatialSpace d ((q + 1) + 1)) ℂ)
  exact ⟨{
    predecessor := E
    gram := G }⟩

namespace TranslatedSpatialCanonicalFieldData

variable
  {L : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {I : Section43ProductTimeApproximateIdentity ((q + 1) + 1)}
  {τ : Fin ((q + 1) + 1) → ℝ}
  {hτ : τ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1)}

/-- At a fixed scale and complex chronological shift, the retained translated
Hilbert field is continuous linear in the full spatial Schwartz profile. -/
noncomputable def fieldCLM
    (D : TranslatedSpatialCanonicalFieldData L OS I τ hτ)
    (N : ℕ)
    (z : Fin (q + 1) → ℂ) :
    SchwartzMap
        (Section43SpatialSpace d ((q + 1) + 1)) ℂ →L[ℂ]
      OSHilbertSpace OS :=
  if hz :
      z ∈ Metric.ball
        (0 : Fin (q + 1) → ℂ) D.gram.gramRadius then
    SchwartzMap.continuousLinearMapOfTendstoComplex
      (fun p =>
        compactTimeSpatialTaylorPartialSumCLM
          OS
          (I.translatedSource τ hτ
            (N + D.predecessor.tailStart))
          (by omega) p z)
      (fun χ => D.gram.hilbert.field (N, χ) z)
      (by
        rw [tendsto_pi_nhds]
        intro χ
        have hz_norm : ‖z‖ < D.gram.gramRadius := by
          simpa [Metric.mem_ball, dist_zero_right] using hz
        have hzχ :
            z ∈ SCV.Polydisc
              (0 : Fin (q + 1) → ℂ)
              (fun _ => D.gram.hilbert.radius) := by
          intro i
          change dist (z i) 0 < D.gram.hilbert.radius
          rw [dist_zero_right]
          exact (norm_le_pi_norm z i).trans_lt
            (hz_norm.trans D.gram.gramRadius_lt_hilbert)
        simpa [translatedPositiveTimeSpatialSource] using
          (D.gram.hilbert.taylor (N, χ)).tendsto_at hzχ)
  else
    0

@[simp]
theorem fieldCLM_apply
    (D : TranslatedSpatialCanonicalFieldData L OS I τ hτ)
    (N : ℕ)
    (z : Fin (q + 1) → ℂ)
    (hz :
      z ∈ Metric.ball
        (0 : Fin (q + 1) → ℂ) D.gram.gramRadius)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) ℂ) :
    D.fieldCLM N z χ =
      D.gram.hilbert.field (N, χ) z := by
  simp only [fieldCLM, dif_pos hz]
  rfl

/-- The canonical translated-product Gram family supplies the exact
continuous translated A0 field consumed by the rooted generator bridge. -/
noncomputable def toContinuousTranslationFieldData
    (D : TranslatedSpatialCanonicalFieldData L OS I τ hτ) :
    LocalReflectedA0ContinuousTranslationFieldData
      OS ((q + 1) + 1) (q + 1)
      (fun N x χ =>
        localPositiveTimeParameterTranslate
          (I.translatedPositiveTimeSpatialSource
            τ hτ χ (N + D.predecessor.tailStart))
          (fun r : Fin (q + 1) =>
            chronologicalTimeSourceDirection (d := d) r)
          x) where
  domain :=
    Metric.ball
      (0 : Fin (q + 1) → ℂ) D.gram.gramRadius
  zero_mem_domain := by
    simpa [Metric.mem_ball] using D.gram.gramRadius_pos
  field := D.fieldCLM
  field_continuous := by
    intro N χ
    have hsubset :
        Metric.ball
            (0 : Fin (q + 1) → ℂ) D.gram.gramRadius ⊆
          SCV.Polydisc
            (0 : Fin (q + 1) → ℂ)
            (fun _ => D.gram.hilbert.radius) := by
      intro z hz
      have hz_norm : ‖z‖ < D.gram.gramRadius := by
        simpa [Metric.mem_ball, dist_zero_right] using hz
      intro i
      change dist (z i) 0 < D.gram.hilbert.radius
      rw [dist_zero_right]
      exact (norm_le_pi_norm z i).trans_lt
        (hz_norm.trans D.gram.gramRadius_lt_hilbert)
    exact
      ((D.gram.hilbert.holomorphic (N, χ)).mono hsubset
        ).continuousOn.congr fun z hz =>
          D.fieldCLM_apply N z hz χ
  cauchy := by
    intro χ
    let C :=
      (I.toLocallyUniformPairwiseInnerLimitData_translated
        OS τ hτ χ D.predecessor.tailStart
        D.predecessor.sourceEdge.stage
        D.predecessor.sourceEdge.germ D.gram
        ).toLocallyUniformCauchyData
    refine ⟨?_⟩
    intro z hz
    obtain ⟨V, hV, hC⟩ := C.locallyUniform z hz
    refine
      ⟨V ∩
          Metric.ball
            (0 : Fin (q + 1) → ℂ) D.gram.gramRadius,
        Filter.inter_mem hV self_mem_nhdsWithin, ?_⟩
    rw [Metric.uniformCauchySeqOn_iff] at hC ⊢
    intro ε hε
    obtain ⟨N0, hN0⟩ := hC ε hε
    refine ⟨N0, ?_⟩
    intro m hm n hn w hw
    simpa only [
      D.fieldCLM_apply m w hw.2 χ,
      D.fieldCLM_apply n w hw.2 χ] using
        hN0 m hm n hn w hw.1
  zero_eq := by
    intro N χ
    have hzero :
        (0 : Fin (q + 1) → ℂ) ∈
          Metric.ball
            (0 : Fin (q + 1) → ℂ) D.gram.gramRadius := by
      simpa [Metric.mem_ball] using D.gram.gramRadius_pos
    rw [D.fieldCLM_apply N 0 hzero χ]
    have hzero_real :
        (0 : Fin (q + 1) → ℝ) ∈ D.gram.hilbert.realRegion :=
      mem_of_mem_nhds D.gram.hilbert.realRegion_nhds
    simpa using D.gram.hilbert.realEdge (N, χ) 0 hzero_real
  realRegion :=
    D.gram.hilbert.realRegion ∩
      {x : Fin (q + 1) → ℝ |
        ‖fun a => ((x a : ℝ) : ℂ)‖ < D.gram.gramRadius}
  realRegion_nhds := by
    have hopen :
        IsOpen
          {x : Fin (q + 1) → ℝ |
            ‖fun a => ((x a : ℝ) : ℂ)‖ <
              D.gram.gramRadius} := by
      exact isOpen_lt (by fun_prop) continuous_const
    apply Filter.inter_mem D.gram.hilbert.realRegion_nhds
    apply hopen.mem_nhds
    simpa using D.gram.gramRadius_pos
  realRegion_to_domain := by
    intro x hx
    simpa [Metric.mem_ball, dist_zero_right] using hx.2
  realEdge := by
    intro N χ x hx
    have hxball :
        (fun a => ((x a : ℝ) : ℂ)) ∈
          Metric.ball
            (0 : Fin (q + 1) → ℂ) D.gram.gramRadius := by
      simpa [Metric.mem_ball, dist_zero_right] using hx.2
    rw [D.fieldCLM_apply N _ hxball χ]
    exact D.gram.hilbert.realEdge (N, χ) x hx.1

/-- The canonical translated-product field with its already proved
holomorphy retained. -/
noncomputable def toHolomorphicTranslationFieldData
    (D : TranslatedSpatialCanonicalFieldData L OS I τ hτ) :
    LocalReflectedA0HolomorphicTranslationFieldData
      OS ((q + 1) + 1) (q + 1)
      (fun N x χ =>
        localPositiveTimeParameterTranslate
          (I.translatedPositiveTimeSpatialSource
            τ hτ χ (N + D.predecessor.tailStart))
          (fun r : Fin (q + 1) =>
            chronologicalTimeSourceDirection (d := d) r)
          x) where
  toLocalReflectedA0ContinuousTranslationFieldData :=
    D.toContinuousTranslationFieldData
  domain_open := Metric.isOpen_ball
  domain_convex := convex_ball _ _
  domain_star := by
    intro z hz
    change
      z ∈
        Metric.ball
          (0 : Fin (q + 1) → ℂ) D.gram.gramRadius at hz
    change
      star z ∈
        Metric.ball
          (0 : Fin (q + 1) → ℂ) D.gram.gramRadius
    rw [Metric.mem_ball, dist_zero_right,
      pi_norm_lt_iff D.gram.gramRadius_pos] at hz ⊢
    intro i
    change ‖star (z i)‖ < D.gram.gramRadius
    simpa only [norm_star] using hz i
  field_holomorphic := by
    intro N χ
    have hsubset :
        Metric.ball
            (0 : Fin (q + 1) → ℂ) D.gram.gramRadius ⊆
          SCV.Polydisc
            (0 : Fin (q + 1) → ℂ)
            (fun _ => D.gram.hilbert.radius) := by
      intro z hz
      have hz_norm : ‖z‖ < D.gram.gramRadius := by
        simpa [Metric.mem_ball, dist_zero_right] using hz
      intro i
      change dist (z i) 0 < D.gram.hilbert.radius
      rw [dist_zero_right]
      exact (norm_le_pi_norm z i).trans_lt
        (hz_norm.trans D.gram.gramRadius_lt_hilbert)
    exact
      ((D.gram.hilbert.holomorphic (N, χ)).mono hsubset
        ).congr fun z hz =>
          D.fieldCLM_apply N z hz χ

end TranslatedSpatialCanonicalFieldData

end Section43ProductTimeApproximateIdentity

namespace OneParticleTranslatedMixedDeltaPredecessorData

variable
  {L : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {I : Section43ProductTimeApproximateIdentity 1}
  {τ : Fin 1 → ℝ}
  {hτ : τ ∈ section43TimeStrictPositiveRegion 1}

/-- The proved one-particle mixed-delta endpoint, expressed in the same
continuous translated-field interface as the multi-particle producer. -/
noncomputable def toContinuousTranslationFieldData
    (D : OneParticleTranslatedMixedDeltaPredecessorData L OS I τ hτ) :
    LocalReflectedA0ContinuousTranslationFieldData
      OS 1 0
      (fun N x χ =>
        localPositiveTimeParameterTranslate
          (I.translatedPositiveTimeSpatialSource
            τ hτ χ (N + D.tailStart))
          (fun r : Fin 0 =>
            chronologicalTimeSourceDirection (d := d) r)
          x) where
  domain := Set.univ
  zero_mem_domain := Set.mem_univ 0
  field := fun N _ => D.fieldVectorCLM N
  field_continuous := fun _ _ => continuousOn_const
  cauchy := by
    intro χ
    simpa [OneParticleTranslatedMixedDeltaPredecessorData.field,
      OneParticleTranslatedMixedDeltaPredecessorData.fieldVectorCLM_apply]
      using
        (D.toLocallyCompactTensorPairGramRepresentationData χ
          ).toLocallyUniformPairwiseInnerLimitData
          |>.toLocallyUniformCauchyData
  zero_eq := by
    intro N χ
    rw [D.fieldVectorCLM_apply]
    simp
  realRegion := Set.univ
  realRegion_nhds := univ_mem
  realRegion_to_domain := fun _ _ => Set.mem_univ _
  realEdge := by
    intro N χ x hx
    have hx0 : x = 0 := Subsingleton.elim _ _
    subst x
    rw [D.fieldVectorCLM_apply]
    simp

/-- The one-particle translated field with its trivial holomorphy retained. -/
noncomputable def toHolomorphicTranslationFieldData
    (D : OneParticleTranslatedMixedDeltaPredecessorData L OS I τ hτ) :
    LocalReflectedA0HolomorphicTranslationFieldData
      OS 1 0
      (fun N x χ =>
        localPositiveTimeParameterTranslate
          (I.translatedPositiveTimeSpatialSource
            τ hτ χ (N + D.tailStart))
          (fun r : Fin 0 =>
            chronologicalTimeSourceDirection (d := d) r)
          x) where
  toLocalReflectedA0ContinuousTranslationFieldData :=
    D.toContinuousTranslationFieldData
  domain_open := isOpen_univ
  domain_convex := convex_univ
  domain_star := fun _ _ => Set.mem_univ _
  field_holomorphic := by
    intro N χ
    change DifferentiableOn ℂ
      (fun _ : Fin 0 → ℂ => D.fieldVectorCLM N χ) Set.univ
    exact
      (differentiableOn_const
        (c := D.fieldVectorCLM N χ) :
        DifferentiableOn ℂ
          (fun _ : Fin 0 → ℂ => D.fieldVectorCLM N χ)
          Set.univ)

end OneParticleTranslatedMixedDeltaPredecessorData

end OSIIChapterV
end OSReconstruction
