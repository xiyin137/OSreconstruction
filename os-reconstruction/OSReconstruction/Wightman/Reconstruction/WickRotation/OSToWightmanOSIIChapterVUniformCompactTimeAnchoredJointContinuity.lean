import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVUniversalCompactCarrierAnchoredAtlas
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVMovingSliceDistribution

/-!
# Joint continuity of the universal compact-time anchored field

The source-indexed Cauchy construction is defined one source at a time.  This
module recovers the stronger production statement needed by radial
integration: joint continuity in the complex angular point and the universal
fixed-carrier source.
-/

noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d]

omit [NeZero d] in
/-- Reflected moving-slice evaluation is jointly continuous in the doubled
Cauchy parameter and the complete reduced Schwartz source. -/
theorem continuousOn_reflectedMovingSliceScalar_joint
    (stage : OSIITimeContinuationStage d (k + (k + 1)))
    (η : SchwartzMap (Fin (k + (k + 1)) → ℝ) ℂ)
    (hη : HasCompactSupport
      (η : (Fin (k + (k + 1)) → ℝ) → ℂ)) :
    ContinuousOn
      (fun p : (Fin (k + k) → ℂ) ×
          SchwartzNPoint d (k + (k + 1)) =>
        reflectedMovingSliceScalar stage η p.2 p.1)
      (reflectedMovingSliceCarrier stage η ×ˢ Set.univ) := by
  let pullback :
      ((Fin (k + k) → ℂ) × SchwartzNPoint d (k + (k + 1))) →
        OSIITimeGapSpace (k + (k + 1)) ×
          SchwartzNPoint d (k + (k + 1)) :=
    fun p => (-(reflectedReducedTimeDisplacementCLM k p.1), p.2)
  have hpullback : Continuous pullback :=
    (continuous_neg.comp
        ((reflectedReducedTimeDisplacementCLM k).continuous.comp
          continuous_fst)).prodMk continuous_snd
  have hmaps :
      Set.MapsTo pullback
        (reflectedMovingSliceCarrier stage η ×ˢ Set.univ)
        (osiiStageMovingSliceCarrier stage η ×ˢ Set.univ) := by
    intro p hp
    exact ⟨hp.1, Set.mem_univ _⟩
  have hcontinuous :=
    (continuousOn_osiiStageMovingSliceDistribution_joint stage η hη).comp
      hpullback.continuousOn hmaps
  exact hcontinuous.congr fun p hp => by
    change
      reflectedMovingSliceScalar stage η p.2 p.1 =
        osiiStageMovingSliceDistribution stage η hη
          (-(reflectedReducedTimeDisplacementCLM k p.1)) p.2
    rw [osiiStageMovingSliceDistribution_apply_of_mem
      stage η hη _ hp.1]
    rfl

namespace UniversalCompactCarrierAnchoredAtlasData

variable {q : ℕ}
variable {L : SimultaneousTimeContinuationStageLevel d}
variable {OS : OsterwalderSchraderAxioms d}
variable {K : Set (Fin ((q + 1) + 1) → ℝ)}

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- On its open source-linear domain, the universal anchored Hilbert field is
jointly continuous in the complex angular point and the complete fixed-carrier
positive-time source. -/
theorem continuousOn_anchoredAtlasField_joint
    (D : UniversalCompactCarrierAnchoredAtlasData L OS K) :
    ContinuousOn
      (fun p : (Fin (q + 1) → ℂ) ×
          UniformCompactTimeSource d ((q + 1) + 1) K =>
        D.gram.anchoredAtlasField
          D.sourceStage.stage D.sourceStage.germ p.2 p.1)
      (D.spatialLinearDomain ×ˢ Set.univ) := by
  let J :
      UniformCompactTimeSource d ((q + 1) + 1) K →L[ℂ]
        SchwartzNPoint d ((q + 1) + 1) :=
    (euclideanPositiveTimeSubmodule
        (d := d) ((q + 1) + 1)).subtypeL.comp
      (uniformCompactTimeSourceSubmodule
        d ((q + 1) + 1) K).subtypeL
  let R :
      UniformCompactTimeSource d ((q + 1) + 1) K →
        SchwartzNPoint d ((q + 1) + ((q + 1) + 1)) :=
    fun a =>
      diffVarReduction d ((q + 1) + ((q + 1) + 1))
        (mixedReflectedChronologicalSource (J a) (J a))
  have hR : Continuous R := by
    exact
      (diffVarReduction d ((q + 1) + ((q + 1) + 1))).continuous.comp
        ((continuous_mixedReflectedChronologicalSource_diag
          (d := d) (k := q + 1)).comp J.continuous)
  have hcenter :
      Continuous
        (reflectedCauchyCenter :
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
  intro p hp
  let input :
      ((Fin (q + 1) → ℂ) ×
          UniformCompactTimeSource d ((q + 1) + 1) K) →
        (Fin ((q + 1) + (q + 1)) → ℂ) ×
          SchwartzNPoint d ((q + 1) + ((q + 1) + 1)) :=
    fun y =>
      (reflectedCauchyCenter y.1, R (y.2 - p.2))
  have hinput : Continuous input := by
    exact
      (hcenter.comp continuous_fst).prodMk
        (hR.comp (continuous_snd.sub continuous_const))
  have hinput_mem :
      input p ∈
        reflectedMovingSliceCarrier
            D.sourceStage.stage D.sourceStage.germ.η ×ˢ
          Set.univ := by
    refine ⟨?_, Set.mem_univ _⟩
    simpa only [input] using hp.1.2.2
  have hscalar_at :
      ContinuousAt
        (fun u : (Fin ((q + 1) + (q + 1)) → ℂ) ×
            SchwartzNPoint d ((q + 1) + ((q + 1) + 1)) =>
          reflectedMovingSliceScalar
            D.sourceStage.stage D.sourceStage.germ.η u.2 u.1)
        (input p) := by
    exact
      (continuousOn_reflectedMovingSliceScalar_joint
        D.sourceStage.stage D.sourceStage.germ.η
        D.sourceStage.germ.η_compact).continuousAt
          (((isOpen_reflectedMovingSliceCarrier
              D.sourceStage.stage D.sourceStage.germ.η
              D.sourceStage.germ.η_compact).prod isOpen_univ).mem_nhds
            hinput_mem)
  let Q :
      ((Fin (q + 1) → ℂ) ×
          UniformCompactTimeSource d ((q + 1) + 1) K) → ℝ :=
    fun y =>
      (reflectedMovingSliceScalar
        D.sourceStage.stage D.sourceStage.germ.η
        (R (y.2 - p.2)) (reflectedCauchyCenter y.1)).re
  have hQ_at : ContinuousAt Q p := by
    have hcomp := hscalar_at.comp hinput.continuousAt
    exact Complex.continuous_re.continuousAt.comp (by
      simpa only [Q, input, Function.comp_apply] using hcomp)
  have hnorm_sq
      (y : (Fin (q + 1) → ℂ) ×
        UniformCompactTimeSource d ((q + 1) + 1) K)
      (hy : y.1 ∈ D.spatialLinearDomain) :
      ‖D.gram.anchoredAtlasField
          D.sourceStage.stage D.sourceStage.germ
          (y.2 - p.2) y.1‖ ^ 2 = Q y := by
    calc
      ‖D.gram.anchoredAtlasField
          D.sourceStage.stage D.sourceStage.germ
          (y.2 - p.2) y.1‖ ^ 2 =
          ((D.gram.cauchy (y.2 - p.2) (y.2 - p.2)).scalar
            (reflectedCauchyCenter y.1)).re :=
        D.gram.anchoredAtlasField_norm_sq_eq_scalar_re
          D.sourceStage.stage D.sourceStage.germ
          (y.2 - p.2) y.1 hy.1
      _ = Q y := by
        rw [D.gram.cauchy_scalar (y.2 - p.2) (y.2 - p.2)]
        rfl
  have hfield_zero :
      D.gram.anchoredAtlasField
          D.sourceStage.stage D.sourceStage.germ 0 p.1 = 0 := by
    change
      D.gram.anchoredAtlasFieldLinearMap
          D.sourceStage.stage D.sourceStage.germ
          p.1 hp.1.1 hp.1.2.1 0 = 0
    exact map_zero _
  have hQ_zero : Q p = 0 := by
    calc
      Q p =
          ‖D.gram.anchoredAtlasField
            D.sourceStage.stage D.sourceStage.germ
            (p.2 - p.2) p.1‖ ^ 2 :=
        (hnorm_sq p hp.1).symm
      _ = 0 := by
        rw [sub_self, hfield_zero]
        norm_num
  have hQ_tendsto : Tendsto Q (𝓝 p) (𝓝 0) := by
    simpa only [ContinuousAt, hQ_zero] using hQ_at
  have hdomain_ev :
      ∀ᶠ y : (Fin (q + 1) → ℂ) ×
          UniformCompactTimeSource d ((q + 1) + 1) K in 𝓝 p,
        y.1 ∈ D.spatialLinearDomain := by
    exact continuous_fst.continuousAt.eventually
      (D.spatialLinearDomain_open.mem_nhds hp.1)
  have hnorm_sq_tendsto :
      Tendsto
        (fun y : (Fin (q + 1) → ℂ) ×
            UniformCompactTimeSource d ((q + 1) + 1) K =>
          ‖D.gram.anchoredAtlasField
            D.sourceStage.stage D.sourceStage.germ
            (y.2 - p.2) y.1‖ ^ 2)
        (𝓝 p) (𝓝 0) :=
    hQ_tendsto.congr'
      (hdomain_ev.mono fun y hy => (hnorm_sq y hy).symm)
  have hnorm_tendsto :
      Tendsto
        (fun y : (Fin (q + 1) → ℂ) ×
            UniformCompactTimeSource d ((q + 1) + 1) K =>
          ‖D.gram.anchoredAtlasField
            D.sourceStage.stage D.sourceStage.germ
            (y.2 - p.2) y.1‖)
        (𝓝 p) (𝓝 0) := by
    have hsqrt :=
      Real.continuous_sqrt.continuousAt.tendsto.comp hnorm_sq_tendsto
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm,
      Real.sqrt_zero] using hsqrt
  have hincrement_tendsto :
      Tendsto
        (fun y : (Fin (q + 1) → ℂ) ×
            UniformCompactTimeSource d ((q + 1) + 1) K =>
          D.gram.anchoredAtlasField
            D.sourceStage.stage D.sourceStage.germ
            (y.2 - p.2) y.1)
        (𝓝 p) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm_tendsto
  have hfixed_at :
      ContinuousAt
        (fun z => D.gram.anchoredAtlasField
          D.sourceStage.stage D.sourceStage.germ p.2 z)
        p.1 := by
    exact
      (D.gram.anchoredAtlasField_holomorphic
        D.sourceStage.stage D.sourceStage.germ p.2).continuousOn.continuousAt
          ((D.gram.anchoredAtlasCoveredDomain_open
            D.sourceStage.stage D.sourceStage.germ).mem_nhds hp.1.1)
  have hfixed_tendsto :
      Tendsto
        (fun y : (Fin (q + 1) → ℂ) ×
            UniformCompactTimeSource d ((q + 1) + 1) K =>
          D.gram.anchoredAtlasField
            D.sourceStage.stage D.sourceStage.germ p.2 y.1)
        (𝓝 p)
        (𝓝 (D.gram.anchoredAtlasField
          D.sourceStage.stage D.sourceStage.germ p.2 p.1)) :=
    hfixed_at.comp continuous_fst.continuousAt
  have hsum_tendsto := hincrement_tendsto.add hfixed_tendsto
  have hfield_eq :
      ∀ᶠ y : (Fin (q + 1) → ℂ) ×
          UniformCompactTimeSource d ((q + 1) + 1) K in 𝓝 p,
        D.gram.anchoredAtlasField
            D.sourceStage.stage D.sourceStage.germ y.2 y.1 =
          D.gram.anchoredAtlasField
              D.sourceStage.stage D.sourceStage.germ
              (y.2 - p.2) y.1 +
            D.gram.anchoredAtlasField
              D.sourceStage.stage D.sourceStage.germ p.2 y.1 := by
    filter_upwards [hdomain_ev] with y hy
    calc
      D.gram.anchoredAtlasField
          D.sourceStage.stage D.sourceStage.germ y.2 y.1 =
          D.gram.anchoredAtlasField
            D.sourceStage.stage D.sourceStage.germ
            ((y.2 - p.2) + p.2) y.1 := by rw [sub_add_cancel]
      _ =
          D.gram.anchoredAtlasField
              D.sourceStage.stage D.sourceStage.germ
              (y.2 - p.2) y.1 +
            D.gram.anchoredAtlasField
              D.sourceStage.stage D.sourceStage.germ p.2 y.1 :=
        D.gram.anchoredAtlasField_add
          D.sourceStage.stage D.sourceStage.germ
          (y.2 - p.2) p.2 y.1 hy.1 hy.2.1
  have htotal := hsum_tendsto.congr' (hfield_eq.mono fun y hy => hy.symm)
  have htotal_at :
      ContinuousAt
        (fun y : (Fin (q + 1) → ℂ) ×
            UniformCompactTimeSource d ((q + 1) + 1) K =>
          D.gram.anchoredAtlasField
            D.sourceStage.stage D.sourceStage.germ y.2 y.1)
        p := by
    simpa only [ContinuousAt, zero_add] using htotal
  exact htotal_at.continuousWithinAt

end UniversalCompactCarrierAnchoredAtlasData

end OSIIChapterV
end OSReconstruction
