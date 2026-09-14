/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib.Topology.MetricSpace.Thickening
import OSReconstruction.SCV.SeparatelyAnalytic
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIITimeShiftedConvolution















noncomputable section

open Complex Topology Filter MeasureTheory
open scoped BigOperators Classical

namespace OSReconstruction

variable {d k : ℕ}

private theorem continuous_finsetSpatialSchwartzSeminorm
    (s : Finset (ℕ × ℕ)) :
    Continuous
      (fun χ =>
        (s.sup
          (schwartzSeminormFamily ℂ
            (Section43SpatialSpace d k) ℂ)) χ) := by
  let p : Seminorm ℂ
      (SchwartzMap (Section43SpatialSpace d k) ℂ) :=
    s.sup
      (schwartzSeminormFamily ℂ
        (Section43SpatialSpace d k) ℂ)
  refine Seminorm.continuous_of_le ?_
    (show p ≤ ∑ i ∈ s,
        schwartzSeminormFamily ℂ
          (Section43SpatialSpace d k) ℂ i by
      simpa [p] using Seminorm.finset_sup_le_sum
        (schwartzSeminormFamily ℂ
          (Section43SpatialSpace d k) ℂ) s)
  change Continuous
    (fun x =>
      Seminorm.coeFnAddMonoidHom ℂ
        (SchwartzMap (Section43SpatialSpace d k) ℂ)
        (∑ i ∈ s,
          schwartzSeminormFamily ℂ
            (Section43SpatialSpace d k) ℂ i) x)
  simp_rw [map_sum, Finset.sum_apply]
  exact continuous_finset_sum _ fun i _ =>
    (schwartz_withSeminorms ℂ
      (Section43SpatialSpace d k) ℂ).continuous_seminorm i

/-- Weak holomorphy of a spatial-distribution family implies joint
continuity of its evaluation on a moving spatial Schwartz test.

The nontrivial input is Banach-Steinhaus on a compact complex-time
neighborhood. No strong-dual holomorphy is assumed. -/
theorem continuousOn_osiiWeaklyHolomorphicEvaluation
    (A : OSIITimeContinuationStage d k) :
    ContinuousOn
      (fun p :
        OSIITimeGapSpace k ×
          SchwartzMap (Section43SpatialSpace d k) ℂ =>
        A.distribution p.1 p.2)
      (A.carrier ×ˢ Set.univ) := by
  intro p hp
  have hpA : p.1 ∈ A.carrier := hp.1
  obtain ⟨R, hR, hRsub⟩ :=
    Metric.isOpen_iff.mp A.carrier_open p.1 hpA
  let r : ℝ := R / 2
  have hr : 0 < r := by
    dsimp [r]
    linarith
  have hcball_sub :
      Metric.closedBall p.1 r ⊆ A.carrier := by
    intro z hz
    apply hRsub
    have hzR : dist z p.1 < R := by
      calc
        dist z p.1 ≤ r := hz
        _ < R := by
          dsimp [r]
          linarith
    simpa [Metric.mem_ball] using hzR
  obtain ⟨s, C, hC, hbound'⟩ :=
    exists_uniform_schwartz_bound_osiiStage_on_compact
      A (Metric.closedBall p.1 r)
        (isCompact_closedBall p.1 r) hcball_sub
  let q : Seminorm ℂ
      (SchwartzMap (Section43SpatialSpace d k) ℂ) :=
    s.sup
      (schwartzSeminormFamily ℂ
        (Section43SpatialSpace d k) ℂ)
  have hq : Continuous q := by
    change Continuous (fun χ => q χ)
    simpa [q] using
      (continuous_finsetSpatialSchwartzSeminorm
        (d := d) (k := k) s)
  have hscalar :
      ContinuousAt (fun z => A.distribution z p.2) p.1 := by
    exact
      ((A.weaklyHolomorphic p.2 p.1 hpA).differentiableAt
        (A.carrier_open.mem_nhds hpA)).continuousAt
  apply ContinuousAt.continuousWithinAt
  refine Metric.continuousAt_iff'.mpr ?_
  intro ε hε
  obtain ⟨δ₁, hδ₁, hscalarδ⟩ :=
    (Metric.continuousAt_iff.mp hscalar) (ε / 2) (by positivity)
  have hsemi :
      ContinuousAt
        (fun χ => q (χ - p.2))
        p.2 :=
    hq.continuousAt.comp
      (continuous_id.sub continuous_const).continuousAt
  have hsemi_ev :
      ∀ᶠ χ :
        SchwartzMap (Section43SpatialSpace d k) ℂ in 𝓝 p.2,
        q (χ - p.2) < ε / (2 * C) := by
    have h :=
      (Metric.continuousAt_iff'.mp hsemi)
        (ε / (2 * C)) (by positivity)
    simpa [Real.dist_eq,
      abs_of_nonneg (apply_nonneg q _)] using h
  have hyr :
      ∀ᶠ y :
        OSIITimeGapSpace k ×
          SchwartzMap (Section43SpatialSpace d k) ℂ in 𝓝 p,
        dist y.1 p.1 < r := by
    simpa [Metric.mem_ball] using
      continuous_fst.continuousAt.eventually
        (Metric.ball_mem_nhds p.1 hr)
  have hyδ₁_ev :
      ∀ᶠ y :
        OSIITimeGapSpace k ×
          SchwartzMap (Section43SpatialSpace d k) ℂ in 𝓝 p,
        dist y.1 p.1 < δ₁ := by
    simpa [Metric.mem_ball] using
      continuous_fst.continuousAt.eventually
        (Metric.ball_mem_nhds p.1 hδ₁)
  have hysemi_ev :
      ∀ᶠ y :
        OSIITimeGapSpace k ×
          SchwartzMap (Section43SpatialSpace d k) ℂ in 𝓝 p,
        q (y.2 - p.2) < ε / (2 * C) :=
    continuous_snd.continuousAt.eventually hsemi_ev
  filter_upwards [hyr, hyδ₁_ev, hysemi_ev] with y hy₁ hyδ₁ hsemi_lt
  have hy₁c : y.1 ∈ Metric.closedBall p.1 r := by
    simpa [Metric.mem_closedBall] using hy₁.le
  have hscalar_lt :
      dist
        (A.distribution y.1 p.2)
        (A.distribution p.1 p.2) < ε / 2 :=
    hscalarδ hyδ₁
  have hfirst :
      ‖A.distribution y.1 (y.2 - p.2)‖ < ε / 2 := by
    calc
      ‖A.distribution y.1 (y.2 - p.2)‖
          ≤ C * q (y.2 - p.2) := by
            simpa [q] using hbound' y.1 hy₁c (y.2 - p.2)
      _ < C * (ε / (2 * C)) :=
        mul_lt_mul_of_pos_left hsemi_lt hC
      _ = ε / 2 := by field_simp [hC.ne']
  calc
    dist
        (A.distribution y.1 y.2)
        (A.distribution p.1 p.2) =
      ‖A.distribution y.1 y.2 -
        A.distribution p.1 p.2‖ := by
          rw [dist_eq_norm]
    _ =
      ‖A.distribution y.1 (y.2 - p.2) +
        (A.distribution y.1 p.2 -
          A.distribution p.1 p.2)‖ := by
        congr 1
        rw [map_sub]
        abel
    _ ≤
      ‖A.distribution y.1 (y.2 - p.2)‖ +
        ‖A.distribution y.1 p.2 -
          A.distribution p.1 p.2‖ :=
      norm_add_le _ _
    _ < ε / 2 + ε / 2 := by
      exact add_lt_add hfirst
        (by simpa [dist_eq_norm] using hscalar_lt)
    _ = ε := by ring

/-- Complex-time shifts whose entire compact time-cutoff support remains in a
continuation-stage carrier. -/
def osiiStageMovingSliceCarrier
    (A : OSIITimeContinuationStage d k)
    (ρ : SchwartzMap (Fin k → ℝ) ℂ) :
    Set (OSIITimeGapSpace k) :=
  osiiShiftedConvolutionCarrier A ρ

/-- The natural carrier of the compact-cutoff moving-slice chart is open. -/
theorem isOpen_osiiStageMovingSliceCarrier
    (A : OSIITimeContinuationStage d k)
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (hρ_compact : HasCompactSupport (ρ : (Fin k → ℝ) → ℂ)) :
    IsOpen (osiiStageMovingSliceCarrier A ρ) := by
  rw [Metric.isOpen_iff]
  intro z hz
  let K : Set (Fin k → ℝ) :=
    tsupport (ρ : (Fin k → ℝ) → ℂ)
  have hK : IsCompact K := by
    simpa [K, HasCompactSupport] using hρ_compact
  let S : Set (OSIITimeGapSpace k) :=
    (fun τ => z + osiiPositiveRealTimeEmbed τ) '' K
  have hS : IsCompact S := by
    exact hK.image
      (continuous_const.add continuous_osiiPositiveRealTimeEmbed)
  have hSsub : S ⊆ A.carrier := by
    rintro _ ⟨τ, hτ, rfl⟩
    exact hz hτ
  obtain ⟨δ, hδ, hthick⟩ :=
    hS.exists_cthickening_subset_open A.carrier_open hSsub
  refine ⟨δ, hδ, ?_⟩
  intro w hw τ hτ
  apply hthick
  apply Metric.mem_cthickening_of_dist_le
    (w + osiiPositiveRealTimeEmbed τ)
    (z + osiiPositiveRealTimeEmbed τ) δ S
  · exact ⟨τ, hτ, rfl⟩
  · have hw' : dist w z ≤ δ := (Metric.mem_ball.mp hw).le
    simpa [dist_eq_norm] using hw'

/-- The compact-cutoff moving-slice integrand attached to a continuation
stage and a full difference-coordinate Schwartz source. -/
def osiiStageMovingSliceIntegrand
    (A : OSIITimeContinuationStage d k)
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (F : SchwartzNPoint d k)
    (z : OSIITimeGapSpace k)
    (τ : Fin k → ℝ) : ℂ :=
  ρ τ *
    osiiShiftedStageDistribution A z τ
      (osiiFullSourceSpatialSlice F τ)

/-- Scalar complex-time chart obtained by integrating the continuation stage
against the moving spatial slices of a full source. -/
def osiiStageMovingSliceScalar
    (A : OSIITimeContinuationStage d k)
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (F : SchwartzNPoint d k)
    (z : OSIITimeGapSpace k) : ℂ :=
  osiiShiftedMovingSpatialSliceIntegral A ρ F z

/-- The compact-cutoff moving-slice integrand is jointly continuous on its
natural complex-time carrier and the full real time-gap space. -/
theorem continuousOn_osiiStageMovingSliceIntegrand
    (A : OSIITimeContinuationStage d k)
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (F : SchwartzNPoint d k) :
    ContinuousOn
      (Function.uncurry (osiiStageMovingSliceIntegrand A ρ F))
      (osiiStageMovingSliceCarrier A ρ ×ˢ Set.univ) := by
  intro p hp
  by_cases hτ : p.2 ∈ tsupport (ρ : (Fin k → ℝ) → ℂ)
  · have hshift :
        p.1 + osiiPositiveRealTimeEmbed p.2 ∈ A.carrier :=
      hp.1 hτ
    have heval :
        ContinuousAt
          (fun q :
            OSIITimeGapSpace k ×
              SchwartzMap (Section43SpatialSpace d k) ℂ =>
            A.distribution q.1 q.2)
          (p.1 + osiiPositiveRealTimeEmbed p.2,
            osiiFullSourceSpatialSlice F p.2) := by
      have hmem :
          (p.1 + osiiPositiveRealTimeEmbed p.2,
              osiiFullSourceSpatialSlice F p.2) ∈
            A.carrier ×ˢ Set.univ :=
        ⟨hshift, Set.mem_univ _⟩
      exact
        ((continuousOn_osiiWeaklyHolomorphicEvaluation A)
          _ hmem).continuousAt
          ((A.carrier_open.prod isOpen_univ).mem_nhds hmem)
    have hinner :
        ContinuousAt
          (fun q :
            OSIITimeGapSpace k × (Fin k → ℝ) =>
            (q.1 + osiiPositiveRealTimeEmbed q.2,
              osiiFullSourceSpatialSlice F q.2))
          p := by
      apply ContinuousAt.prodMk
      · exact
          (continuous_fst.add
            (continuous_osiiPositiveRealTimeEmbed.comp
              continuous_snd)).continuousAt
      · exact
          (continuous_osiiFullSourceSpatialSlice F).comp
            continuous_snd |>.continuousAt
    have hpair :
        ContinuousAt
          (fun q :
            OSIITimeGapSpace k × (Fin k → ℝ) =>
            A.distribution
              (q.1 + osiiPositiveRealTimeEmbed q.2)
              (osiiFullSourceSpatialSlice F q.2))
          p := by
      exact
        ContinuousAt.comp'
          (f := fun q :
            OSIITimeGapSpace k × (Fin k → ℝ) =>
            (q.1 + osiiPositiveRealTimeEmbed q.2,
              osiiFullSourceSpatialSlice F q.2))
          (g := fun q :
            OSIITimeGapSpace k ×
              SchwartzMap (Section43SpatialSpace d k) ℂ =>
            A.distribution q.1 q.2)
          (x := p)
          heval hinner
    have hρ :
        ContinuousAt
          (fun q : OSIITimeGapSpace k × (Fin k → ℝ) => ρ q.2)
          p :=
      ρ.continuous.continuousAt.comp continuous_snd.continuousAt
    simpa [osiiStageMovingSliceIntegrand] using
      (hρ.mul hpair).continuousWithinAt
  · have hnot :
        {τ : Fin k → ℝ |
          τ ∉ tsupport (ρ : (Fin k → ℝ) → ℂ)} ∈ 𝓝 p.2 :=
      (isClosed_tsupport (ρ : (Fin k → ℝ) → ℂ)).isOpen_compl.mem_nhds hτ
    have hnot_pair :
        ∀ᶠ q : OSIITimeGapSpace k × (Fin k → ℝ) in
          nhdsWithin p
            (osiiStageMovingSliceCarrier A ρ ×ˢ Set.univ),
          q.2 ∉ tsupport (ρ : (Fin k → ℝ) → ℂ) := by
      exact
        (continuous_snd.continuousAt.eventually hnot).filter_mono
          nhdsWithin_le_nhds
    have hzero :
        Function.uncurry (osiiStageMovingSliceIntegrand A ρ F)
          =ᶠ[nhdsWithin p
            (osiiStageMovingSliceCarrier A ρ ×ˢ Set.univ)]
          fun _ => 0 := by
      filter_upwards [hnot_pair] with q hq
      have hρq : ρ q.2 = 0 :=
        image_eq_zero_of_notMem_tsupport hq
      change osiiStageMovingSliceIntegrand A ρ F q.1 q.2 = 0
      simp [osiiStageMovingSliceIntegrand, hρq]
    exact
      continuousWithinAt_const.congr_of_eventuallyEq hzero
        (by
          have hρp : ρ p.2 = 0 :=
            image_eq_zero_of_notMem_tsupport hτ
          change osiiStageMovingSliceIntegrand A ρ F p.1 p.2 = 0
          simp [osiiStageMovingSliceIntegrand, hρp])

/-- Every fixed real-time parameter gives a holomorphic coordinate slice of
the moving-slice integrand on its natural carrier. -/
theorem differentiableAt_osiiStageMovingSliceIntegrand_update
    (A : OSIITimeContinuationStage d k)
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (F : SchwartzNPoint d k)
    {z : OSIITimeGapSpace k}
    (hz : z ∈ osiiStageMovingSliceCarrier A ρ)
    (τ : Fin k → ℝ)
    (i : Fin k) :
    DifferentiableAt ℂ
      (fun w =>
        osiiStageMovingSliceIntegrand A ρ F
          (Function.update z i w) τ)
      (z i) := by
  by_cases hρτ : ρ τ = 0
  · simp [osiiStageMovingSliceIntegrand, hρτ]
  · have hτ :
        τ ∈ tsupport (ρ : (Fin k → ℝ) → ℂ) := by
      apply subset_closure
      exact hρτ
    have hshift :
        z + osiiPositiveRealTimeEmbed τ ∈ A.carrier :=
      hz hτ
    have houter :
        DifferentiableAt ℂ
          (fun ζ =>
            A.distribution ζ (osiiFullSourceSpatialSlice F τ))
          (z + osiiPositiveRealTimeEmbed τ) := by
      exact
        (A.weaklyHolomorphic (osiiFullSourceSpatialSlice F τ)
          (z + osiiPositiveRealTimeEmbed τ) hshift).differentiableAt
          (A.carrier_open.mem_nhds hshift)
    have hinner :
        DifferentiableAt ℂ
          (fun w : ℂ =>
            Function.update z i w +
              osiiPositiveRealTimeEmbed τ)
          (z i) := by
      rw [differentiableAt_pi]
      intro j
      by_cases hji : j = i
      · subst j
        simpa [Function.update] using
          differentiableAt_id.add
            (differentiableAt_const
              (osiiPositiveRealTimeEmbed τ i))
      · simpa [Function.update, hji] using
          (differentiableAt_const
            (z j + osiiPositiveRealTimeEmbed τ j) :
            DifferentiableAt ℂ
              (fun _ : ℂ =>
                z j + osiiPositiveRealTimeEmbed τ j)
              (z i))
    have houter' :
        DifferentiableAt ℂ
          (fun ζ =>
            A.distribution ζ (osiiFullSourceSpatialSlice F τ))
          ((fun w : ℂ =>
            Function.update z i w +
              osiiPositiveRealTimeEmbed τ) (z i)) := by
      simpa using houter
    have hcomp :
        DifferentiableAt ℂ
          (fun w =>
            A.distribution
              (Function.update z i w +
                osiiPositiveRealTimeEmbed τ)
              (osiiFullSourceSpatialSlice F τ))
          (z i) := by
      simpa [Function.comp_def] using
        houter'.comp (z i) hinner
    simpa [osiiStageMovingSliceIntegrand] using
      hcomp.const_mul (ρ τ)

/-- Before differentiability, the compact-cutoff moving-slice scalar chart is
already continuous on its natural carrier. -/
theorem continuousOn_osiiStageMovingSliceScalar
    (A : OSIITimeContinuationStage d k)
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (F : SchwartzNPoint d k)
    (hρ_compact : HasCompactSupport (ρ : (Fin k → ℝ) → ℂ)) :
    ContinuousOn
      (osiiStageMovingSliceScalar A ρ F)
      (osiiStageMovingSliceCarrier A ρ) := by
  let K : Set (Fin k → ℝ) :=
    tsupport (ρ : (Fin k → ℝ) → ℂ)
  have hK : IsCompact K := by
    simpa [K, HasCompactSupport] using hρ_compact
  have hzero :
      ∀ z τ, z ∈ osiiStageMovingSliceCarrier A ρ →
        τ ∉ K →
        osiiStageMovingSliceIntegrand A ρ F z τ = 0 := by
    intro z τ _ hτ
    have hρτ : ρ τ = 0 := by
      exact image_eq_zero_of_notMem_tsupport hτ
    simp [osiiStageMovingSliceIntegrand, hρτ]
  simpa [osiiStageMovingSliceScalar] using
    continuousOn_integral_of_compact_support
      (μ := volume) hK
      (continuousOn_osiiStageMovingSliceIntegrand A ρ F)
      hzero

private theorem dist_osiiCoordinateUpdate_le
    (z : Fin k → ℂ) (i : Fin k) (w : ℂ) :
    dist (Function.update z i w) z ≤ dist w (z i) := by
  refine (dist_pi_le_iff dist_nonneg).2 ?_
  intro j
  by_cases hji : j = i
  · subst j
    simp
  · simp [Function.update_of_ne hji]

private theorem continuous_osiiCoordinateUpdate_prod
    (z : Fin k → ℂ) (i : Fin k) :
    Continuous
      (fun p : ℂ × (Fin k → ℝ) =>
        (Function.update z i p.1, p.2)) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro j
    by_cases hji : j = i
    · subst j
      simpa using continuous_fst
    · simpa [Function.update_of_ne hji] using
        (continuous_const : Continuous
          (fun _ : ℂ × (Fin k → ℝ) => z j))
  · exact continuous_snd

private theorem continuous_osiiStageMovingSliceIntegrand_fixed
    (A : OSIITimeContinuationStage d k)
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (F : SchwartzNPoint d k)
    {z : OSIITimeGapSpace k}
    (hz : z ∈ osiiStageMovingSliceCarrier A ρ) :
    Continuous (fun τ => osiiStageMovingSliceIntegrand A ρ F z τ) := by
  rw [← continuousOn_univ]
  exact
    (continuousOn_osiiStageMovingSliceIntegrand A ρ F).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun τ _ => ⟨hz, Set.mem_univ τ⟩)

set_option maxHeartbeats 1200000 in
/-- Each coordinate slice of the integrated moving-slice scalar is
holomorphic. The proof uses a compact local carrier collar, a Cauchy estimate
uniform on the cutoff support, and differentiation under the integral. -/
theorem differentiableAt_osiiStageMovingSliceScalar_update
    (A : OSIITimeContinuationStage d k)
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (F : SchwartzNPoint d k)
    (hρ_compact : HasCompactSupport (ρ : (Fin k → ℝ) → ℂ))
    {z : OSIITimeGapSpace k}
    (hz : z ∈ osiiStageMovingSliceCarrier A ρ)
    (i : Fin k) :
    DifferentiableAt ℂ
      (fun w => osiiStageMovingSliceScalar A ρ F
        (Function.update z i w))
      (z i) := by
  obtain ⟨R, hR, hRsub⟩ :=
    Metric.isOpen_iff.mp
      (isOpen_osiiStageMovingSliceCarrier A ρ hρ_compact) z hz
  let ε : ℝ := R / 4
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have h2εR : 2 * ε < R := by
    dsimp [ε]
    linarith
  have hupdate_mem :
      ∀ w : ℂ, dist w (z i) ≤ 2 * ε →
        Function.update z i w ∈ osiiStageMovingSliceCarrier A ρ := by
    intro w hw
    apply hRsub
    rw [Metric.mem_ball]
    exact
      (dist_osiiCoordinateUpdate_le z i w).trans_lt
        (hw.trans_lt h2εR)
  have hupdate_mem_ball :
      ∀ w ∈ Metric.ball (z i) (2 * ε),
        Function.update z i w ∈ osiiStageMovingSliceCarrier A ρ := by
    intro w hw
    exact hupdate_mem w (Metric.mem_ball.mp hw).le
  let K : Set (Fin k → ℝ) :=
    tsupport (ρ : (Fin k → ℝ) → ℂ)
  have hK : IsCompact K := by
    simpa [K, HasCompactSupport] using hρ_compact
  let S : Set (ℂ × (Fin k → ℝ)) :=
    Metric.closedBall (z i) (2 * ε) ×ˢ K
  have hS : IsCompact S :=
    (isCompact_closedBall (z i) (2 * ε)).prod hK
  have hmapS :
      Set.MapsTo
        (fun p : ℂ × (Fin k → ℝ) =>
          (Function.update z i p.1, p.2))
        S
        (osiiStageMovingSliceCarrier A ρ ×ˢ Set.univ) := by
    intro p hp
    exact
      ⟨hupdate_mem p.1 (Metric.mem_closedBall.mp hp.1),
        Set.mem_univ p.2⟩
  have hG_cont :
      ContinuousOn
        (fun p : ℂ × (Fin k → ℝ) =>
          osiiStageMovingSliceIntegrand A ρ F
            (Function.update z i p.1) p.2)
        S := by
    exact
      (continuousOn_osiiStageMovingSliceIntegrand A ρ F).comp
        (continuous_osiiCoordinateUpdate_prod z i).continuousOn hmapS
  obtain ⟨M₀, hM₀⟩ :=
    hS.exists_bound_of_continuousOn hG_cont
  let M : ℝ := max M₀ 0
  have hM :
      ∀ w ∈ Metric.closedBall (z i) (2 * ε),
        ∀ τ ∈ K,
          ‖osiiStageMovingSliceIntegrand A ρ F
            (Function.update z i w) τ‖ ≤ M := by
    intro w hw τ hτ
    exact (hM₀ (w, τ) ⟨hw, hτ⟩).trans (le_max_left _ _)
  let G : ℂ → (Fin k → ℝ) → ℂ := fun w τ =>
    osiiStageMovingSliceIntegrand A ρ F
      (Function.update z i w) τ
  let G' : ℂ → (Fin k → ℝ) → ℂ := fun w τ =>
    deriv (fun u => G u τ) w
  have hG_diff :
      ∀ τ, ∀ w ∈ Metric.ball (z i) (2 * ε),
        HasDerivAt (fun u => G u τ) (G' w τ) w := by
    intro τ w hw
    have hmem := hupdate_mem_ball w hw
    have hdiff :=
      differentiableAt_osiiStageMovingSliceIntegrand_update
        A ρ F hmem τ i
    have heq :
        (fun u =>
          osiiStageMovingSliceIntegrand A ρ F
            (Function.update (Function.update z i w) i u) τ) =
        fun u => G u τ := by
      funext u
      simp [G]
    rw [heq] at hdiff
    simpa [G'] using hdiff.hasDerivAt
  have hG'_cont :
      Continuous (G' (z i)) := by
    rw [continuous_iff_continuousAt]
    intro τ
    have hjoint :
        ContinuousOn
          (fun p : ℂ × (Fin k → ℝ) => G p.1 p.2)
          (Metric.closedBall (z i) ε ×ˢ Set.univ) := by
      exact
        (continuousOn_osiiStageMovingSliceIntegrand A ρ F).comp
          (continuous_osiiCoordinateUpdate_prod z i).continuousOn
          (fun p hp =>
            ⟨hupdate_mem p.1
                ((Metric.mem_closedBall.mp hp.1).trans
                  (by linarith : ε ≤ 2 * ε)),
              Set.mem_univ p.2⟩)
    have hdiff :
        ∀ η ∈ Set.univ,
          DifferentiableOn ℂ (fun w => G w η)
            (Metric.closedBall (z i) ε) := by
      intro η _ w hw
      exact
        (hG_diff η w
          (Metric.closedBall_subset_ball
            (by linarith : ε < 2 * ε) hw)).differentiableAt.differentiableWithinAt
    simpa [G'] using
      continuousAt_deriv_of_continuousOn hε isOpen_univ
        (fun p : ℂ × (Fin k → ℝ) => G p.1 p.2)
        hjoint hdiff (Set.mem_univ τ)
  have hG_meas :
      ∀ᶠ w in 𝓝 (z i),
        AEStronglyMeasurable (G w) volume := by
    filter_upwards [Metric.ball_mem_nhds (z i) hε] with w hw
    exact
      (continuous_osiiStageMovingSliceIntegrand_fixed
        A ρ F (hupdate_mem w
          ((Metric.mem_ball.mp hw).le.trans
            (by linarith : ε ≤ 2 * ε)))).aestronglyMeasurable
  have hG_int : Integrable (G (z i)) volume := by
    have hint :=
      integrable_osiiShiftedMovingSpatialSlicePairing
        A ρ hρ_compact F
          (⟨z, hz⟩ : osiiShiftedConvolutionCarrier A ρ)
    simpa [G, osiiStageMovingSliceIntegrand,
      osiiStageMovingSliceCarrier] using hint
  have hG'_meas :
      AEStronglyMeasurable (G' (z i)) volume :=
    hG'_cont.aestronglyMeasurable
  have hderiv_bound :
      ∀ τ, ∀ w ∈ Metric.ball (z i) ε,
        ‖G' w τ‖ ≤
          K.indicator (fun _ => M / ε) τ := by
    intro τ w hw
    by_cases hτ : τ ∈ K
    · rw [Set.indicator_of_mem hτ]
      apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hε
      · constructor
        · intro u hu
          have hu2 : u ∈ Metric.ball (z i) (2 * ε) := by
            rw [Metric.mem_ball]
            calc
              dist u (z i) ≤ dist u w + dist w (z i) :=
                dist_triangle u w (z i)
              _ < ε + ε := add_lt_add
                (Metric.mem_ball.mp hu) (Metric.mem_ball.mp hw)
              _ = 2 * ε := by ring
          exact
            (hG_diff τ u hu2).differentiableAt.differentiableWithinAt
        · rw [closure_ball w hε.ne']
          intro u hu
          have hu2 : u ∈ Metric.ball (z i) (2 * ε) := by
            rw [Metric.mem_ball]
            calc
              dist u (z i) ≤ dist u w + dist w (z i) :=
                dist_triangle u w (z i)
              _ < ε + ε := add_lt_add_of_le_of_lt
                (Metric.mem_closedBall.mp hu) (Metric.mem_ball.mp hw)
              _ = 2 * ε := by ring
          exact (hG_diff τ u hu2).continuousAt.continuousWithinAt
      · intro u hu
        apply hM u
        · rw [Metric.mem_closedBall]
          calc
            dist u (z i) ≤ dist u w + dist w (z i) :=
              dist_triangle u w (z i)
            _ ≤ ε + ε := add_le_add
              (Metric.sphere_subset_closedBall hu)
              (Metric.mem_ball.mp hw).le
            _ = 2 * ε := by ring
        · exact hτ
    · rw [Set.indicator_of_notMem hτ]
      have hρτ : ρ τ = 0 :=
        image_eq_zero_of_notMem_tsupport hτ
      simp [G', G, osiiStageMovingSliceIntegrand, hρτ]
  have hbound_int :
      Integrable (K.indicator (fun _ => M / ε)) volume := by
    exact
      continuousOn_const.integrableOn_compact hK
        |>.integrable_indicator hK.measurableSet
  have h_diff :
      ∀ᵐ τ ∂volume, ∀ w ∈ Metric.ball (z i) ε,
        HasDerivAt (fun u => G u τ) (G' w τ) w :=
    Filter.Eventually.of_forall fun τ w hw =>
      hG_diff τ w
        (Metric.ball_subset_ball
          (by linarith : ε ≤ 2 * ε) hw)
  have hmain :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume)
      (F := G) (F' := G')
      (bound := K.indicator (fun _ => M / ε))
      (Metric.ball_mem_nhds (z i) hε)
      hG_meas hG_int hG'_meas
      (Filter.Eventually.of_forall fun τ w hw =>
        hderiv_bound τ w hw)
      hbound_int h_diff
  simpa [osiiStageMovingSliceScalar,
    osiiShiftedMovingSpatialSliceIntegral,
    osiiMovingSpatialSliceIntegral, G,
    osiiStageMovingSliceIntegrand,
    osiiShiftedStageDistribution] using
      hmain.2.differentiableAt

/-- The compact-cutoff moving-slice scalar chart is jointly holomorphic on its
natural carrier. -/
theorem differentiableOn_osiiStageMovingSliceScalar
    (A : OSIITimeContinuationStage d k)
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (F : SchwartzNPoint d k)
    (hρ_compact : HasCompactSupport (ρ : (Fin k → ℝ) → ℂ)) :
    DifferentiableOn ℂ
      (osiiStageMovingSliceScalar A ρ F)
      (osiiStageMovingSliceCarrier A ρ) := by
  exact
    osgood_lemma
      (isOpen_osiiStageMovingSliceCarrier A ρ hρ_compact)
      (osiiStageMovingSliceScalar A ρ F)
      (continuousOn_osiiStageMovingSliceScalar A ρ F hρ_compact)
      (fun z hz i =>
        differentiableAt_osiiStageMovingSliceScalar_update
          A ρ F hρ_compact hz i)

/-- At zero complex shift, the Chapter V scalar chart is exactly the moving
spatial-slice convolution of the positive-real-time restriction. -/
theorem osiiStageMovingSliceScalar_zero
    (A : OSIITimeContinuationStage d k)
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (F : SchwartzNPoint d k) :
    osiiStageMovingSliceScalar A ρ F 0 =
      osiiMovingSpatialSliceIntegral ρ
        (fun τ => A.distribution (osiiPositiveRealTimeEmbed τ)) F := by
  simp [osiiStageMovingSliceScalar, osiiMovingSpatialSliceIntegral]

/-- If the positive-real-time restriction represents the Euclidean
distribution on the cutoff support, the zero-shift scalar chart recovers the
full ordered-pullback source. -/
theorem osiiStageMovingSliceScalar_zero_eq_orderedPullbackFullCutoff
    [NeZero d]
    (A : OSIITimeContinuationStage d k)
    (W : SchwartzNPoint d k →L[ℂ] ℂ)
    (ρ : SchwartzMap (Fin k → ℝ) ℂ)
    (U : Set (Fin k → ℝ))
    (hρ_compact : HasCompactSupport (ρ : (Fin k → ℝ) → ℂ))
    (hρ_support : tsupport (ρ : (Fin k → ℝ) → ℂ) ⊆ U)
    (hscalar :
      ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
        ContinuousOn
          (fun τ => A.distribution
            (osiiPositiveRealTimeEmbed τ) χ) U)
    (hbounded :
      OSIITimeSpatialPointwiseBoundedOn
        (fun τ => A.distribution (osiiPositiveRealTimeEmbed τ)) U)
    (hrep :
      OSIITimeSpatialRepresentsDistributionOn W
        (fun τ => A.distribution (osiiPositiveRealTimeEmbed τ)) U)
    (F : SchwartzNPoint d k) :
    osiiStageMovingSliceScalar A ρ F 0 =
      W (section43OrderedPullbackFullCutoffCLM d k ρ F) := by
  rw [osiiStageMovingSliceScalar_zero]
  exact
    osiiMovingSpatialSliceIntegral_eq_orderedPullbackFullCutoff
      W ρ
        (fun τ => A.distribution (osiiPositiveRealTimeEmbed τ))
        U hρ_compact hρ_support hscalar hbounded hrep F

end OSReconstruction
