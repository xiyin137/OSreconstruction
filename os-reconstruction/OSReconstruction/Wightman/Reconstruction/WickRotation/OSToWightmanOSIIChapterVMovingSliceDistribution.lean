/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVMovingSliceChart














noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction

variable {d k : Nat}

/-- At every admissible moving-slice parameter, the scalar construction is
one continuous linear functional of the complete Schwartz source. -/
theorem exists_osiiStageMovingSliceScalarCLM
    (A : OSIITimeContinuationStage d k)
    (rho : SchwartzMap (Fin k -> Real) Complex)
    (hrho_compact :
      HasCompactSupport (rho : (Fin k -> Real) -> Complex))
    (z : OSIITimeGapSpace k)
    (hz : z ∈ osiiStageMovingSliceCarrier A rho) :
    ∃ L : SchwartzNPoint d k →L[Complex] Complex,
      ∀ F, L F = osiiStageMovingSliceScalar A rho F z := by
  let U : Set (Fin k -> Real) :=
    tsupport (rho : (Fin k -> Real) -> Complex)
  let orbit : Set (OSIITimeGapSpace k) :=
    osiiShiftedConvolutionOrbit rho z
  obtain ⟨s, C, hC, hbound⟩ :=
    exists_uniform_schwartz_bound_osiiStage_on_compact
      A orbit
      (isCompact_osiiShiftedConvolutionOrbit rho hrho_compact z)
      (osiiShiftedConvolutionOrbit_subset_carrier A rho ⟨z, hz⟩)
  have hbounded :
      OSIITimeSpatialPointwiseBoundedOn
        (osiiShiftedStageDistribution A z) U := by
    intro chi
    refine
      ⟨C * s.sup
          (schwartzSeminormFamily Complex
            (Section43SpatialSpace d k) Complex) chi, ?_⟩
    intro tau htau
    exact hbound
      (z + osiiPositiveRealTimeEmbed tau)
      ⟨tau, htau, rfl⟩ chi
  obtain ⟨L, hL⟩ :=
    exists_osiiMovingSpatialSliceIntegralCLM
      rho (osiiShiftedStageDistribution A z) U
      hrho_compact (fun _ h => h)
      (continuousOn_osiiShiftedStageDistribution_pairing
        A rho ⟨z, hz⟩)
      hbounded
  refine ⟨L, ?_⟩
  intro F
  rw [hL]
  rfl

/-- The compact-cutoff moving-slice chart as a full-Schwartz distribution at
each parameter, totalized by zero outside its honest carrier. -/
noncomputable def osiiStageMovingSliceDistribution
    (A : OSIITimeContinuationStage d k)
    (rho : SchwartzMap (Fin k -> Real) Complex)
    (hrho_compact :
      HasCompactSupport (rho : (Fin k -> Real) -> Complex))
    (z : OSIITimeGapSpace k) :
    SchwartzNPoint d k →L[Complex] Complex :=
  if hz : z ∈ osiiStageMovingSliceCarrier A rho then
    Classical.choose
      (exists_osiiStageMovingSliceScalarCLM
        A rho hrho_compact z hz)
  else
    0

/-- Evaluation of the bundled distribution recovers the original scalar
moving-slice chart throughout its carrier. -/
@[simp] theorem osiiStageMovingSliceDistribution_apply_of_mem
    (A : OSIITimeContinuationStage d k)
    (rho : SchwartzMap (Fin k -> Real) Complex)
    (hrho_compact :
      HasCompactSupport (rho : (Fin k -> Real) -> Complex))
    (z : OSIITimeGapSpace k)
    (hz : z ∈ osiiStageMovingSliceCarrier A rho)
    (F : SchwartzNPoint d k) :
    osiiStageMovingSliceDistribution A rho hrho_compact z F =
      osiiStageMovingSliceScalar A rho F z := by
  rw [osiiStageMovingSliceDistribution, dif_pos hz]
  exact
    (Classical.choose_spec
      (exists_osiiStageMovingSliceScalarCLM
        A rho hrho_compact z hz)) F

/-- The bundled full-Schwartz distribution is weakly holomorphic on the
moving-slice carrier. -/
theorem differentiableOn_osiiStageMovingSliceDistribution_apply
    (A : OSIITimeContinuationStage d k)
    (rho : SchwartzMap (Fin k -> Real) Complex)
    (hrho_compact :
      HasCompactSupport (rho : (Fin k -> Real) -> Complex))
    (F : SchwartzNPoint d k) :
    DifferentiableOn Complex
      (fun z => osiiStageMovingSliceDistribution
        A rho hrho_compact z F)
      (osiiStageMovingSliceCarrier A rho) := by
  exact
    (differentiableOn_osiiStageMovingSliceScalar
      A rho F hrho_compact).congr fun z hz =>
        osiiStageMovingSliceDistribution_apply_of_mem
          A rho hrho_compact z hz F

private theorem continuous_finsetFullSchwartzSeminorm
    (s : Finset (Nat × Nat)) :
    Continuous
      (fun F : SchwartzNPoint d k =>
        (s.sup
          (schwartzSeminormFamily Real
            (NPointDomain d k) Complex)) F) := by
  let p : Seminorm Real (SchwartzNPoint d k) :=
    s.sup
      (schwartzSeminormFamily Real
        (NPointDomain d k) Complex)
  refine Seminorm.continuous_of_le ?_
    (show p ≤ ∑ i ∈ s,
        schwartzSeminormFamily Real
          (NPointDomain d k) Complex i by
      simpa [p] using Seminorm.finset_sup_le_sum
        (schwartzSeminormFamily Real
          (NPointDomain d k) Complex) s)
  change Continuous
    (fun F =>
      Seminorm.coeFnAddMonoidHom Real (SchwartzNPoint d k)
        (∑ i ∈ s,
          schwartzSeminormFamily Real
            (NPointDomain d k) Complex i) F)
  simp_rw [map_sum, Finset.sum_apply]
  exact continuous_finset_sum _ fun i _ =>
    (schwartz_withSeminorms Real
      (NPointDomain d k) Complex).continuous_seminorm i

/-- On every compact subset of the moving-slice carrier, the bundled
distributions obey one common finite full-Schwartz seminorm bound. -/
private theorem
    exists_uniform_bound_osiiStageMovingSliceDistribution_on_compact
    (A : OSIITimeContinuationStage d k)
    (rho : SchwartzMap (Fin k -> Real) Complex)
    (hrho_compact :
      HasCompactSupport (rho : (Fin k -> Real) -> Complex))
    (K : Set (OSIITimeGapSpace k))
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ osiiStageMovingSliceCarrier A rho) :
    ∃ s : Finset (Nat × Nat), ∃ C : Real, 0 < C ∧
      ∀ z ∈ K, ∀ F : SchwartzNPoint d k,
        ‖osiiStageMovingSliceDistribution A rho hrho_compact z F‖ ≤
          C *
            (s.sup
              (schwartzSeminormFamily Real
                (NPointDomain d k) Complex)) F := by
  let D := osiiStageMovingSliceDistribution A rho hrho_compact
  have hbounded :
      ∀ F : SchwartzNPoint d k,
        ∃ C : Real, ∀ z : K, ‖D z.1 F‖ ≤ C := by
    intro F
    obtain ⟨C, hC⟩ :=
      hK_compact.exists_bound_of_continuousOn
        ((differentiableOn_osiiStageMovingSliceDistribution_apply
          A rho hrho_compact F).continuousOn.mono hK_subset)
    exact ⟨C, fun z => hC z.1 z.2⟩
  obtain ⟨s, C, hC, hbound⟩ :=
    SchwartzMap.tempered_uniform_schwartz_bound
      (E := NPointDomain d k) (F := Complex) (G := Complex)
      (T := fun z : K => (D z.1).restrictScalars Real)
      hbounded
  refine ⟨s, (C : Real), ?_, ?_⟩
  · exact_mod_cast (show 0 < C from pos_iff_ne_zero.mpr hC)
  · intro z hz F
    have h := hbound ⟨z, hz⟩ F
    simpa [D, Seminorm.smul_apply] using h

/-- Evaluation of the moving-slice distribution is jointly continuous in
the complex parameter and complete Schwartz source. -/
theorem continuousOn_osiiStageMovingSliceDistribution_joint
    (A : OSIITimeContinuationStage d k)
    (rho : SchwartzMap (Fin k -> Real) Complex)
    (hrho_compact :
      HasCompactSupport (rho : (Fin k -> Real) -> Complex)) :
    ContinuousOn
      (fun p : OSIITimeGapSpace k × SchwartzNPoint d k =>
        osiiStageMovingSliceDistribution
          A rho hrho_compact p.1 p.2)
      (osiiStageMovingSliceCarrier A rho ×ˢ Set.univ) := by
  intro p hp
  have hpA : p.1 ∈ osiiStageMovingSliceCarrier A rho := hp.1
  have hopen := isOpen_osiiStageMovingSliceCarrier A rho hrho_compact
  obtain ⟨R, hR, hRsub⟩ :=
    Metric.isOpen_iff.mp hopen p.1 hpA
  let r : Real := R / 2
  have hr : 0 < r := by
    dsimp [r]
    linarith
  have hcball_sub :
      Metric.closedBall p.1 r ⊆
        osiiStageMovingSliceCarrier A rho := by
    intro z hz
    apply hRsub
    have hzR : dist z p.1 < R := by
      calc
        dist z p.1 ≤ r := hz
        _ < R := by
          dsimp [r]
          linarith
    simpa [Metric.mem_ball] using hzR
  obtain ⟨s, C, hC, hbound⟩ :=
    exists_uniform_bound_osiiStageMovingSliceDistribution_on_compact
      A rho hrho_compact (Metric.closedBall p.1 r)
      (isCompact_closedBall p.1 r) hcball_sub
  let q : Seminorm Real (SchwartzNPoint d k) :=
    s.sup
      (schwartzSeminormFamily Real
        (NPointDomain d k) Complex)
  have hq : Continuous q := by
    change Continuous (fun F => q F)
    simpa [q] using
      (continuous_finsetFullSchwartzSeminorm (d := d) (k := k) s)
  have hscalar :
      ContinuousAt
        (fun z => osiiStageMovingSliceDistribution
          A rho hrho_compact z p.2) p.1 := by
    exact
      ((differentiableOn_osiiStageMovingSliceDistribution_apply
        A rho hrho_compact p.2 p.1 hpA).differentiableAt
          (hopen.mem_nhds hpA)).continuousAt
  apply ContinuousAt.continuousWithinAt
  refine Metric.continuousAt_iff'.mpr ?_
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hscalar_delta⟩ :=
    (Metric.continuousAt_iff.mp hscalar)
      (epsilon / 2) (by positivity)
  have hsemi :
      ContinuousAt (fun F => q (F - p.2)) p.2 :=
    hq.continuousAt.comp
      (continuous_id.sub continuous_const).continuousAt
  have hsemi_ev :
      ∀ᶠ F : SchwartzNPoint d k in nhds p.2,
        q (F - p.2) < epsilon / (2 * C) := by
    have h :=
      (Metric.continuousAt_iff'.mp hsemi)
        (epsilon / (2 * C)) (by positivity)
    simpa [Real.dist_eq,
      abs_of_nonneg (apply_nonneg q _)] using h
  have hyr :
      ∀ᶠ y : OSIITimeGapSpace k × SchwartzNPoint d k in nhds p,
        dist y.1 p.1 < r := by
    simpa [Metric.mem_ball] using
      continuous_fst.continuousAt.eventually
        (Metric.ball_mem_nhds p.1 hr)
  have hydelta_ev :
      ∀ᶠ y : OSIITimeGapSpace k × SchwartzNPoint d k in nhds p,
        dist y.1 p.1 < delta := by
    simpa [Metric.mem_ball] using
      continuous_fst.continuousAt.eventually
        (Metric.ball_mem_nhds p.1 hdelta)
  have hysemi_ev :
      ∀ᶠ y : OSIITimeGapSpace k × SchwartzNPoint d k in nhds p,
        q (y.2 - p.2) < epsilon / (2 * C) :=
    continuous_snd.continuousAt.eventually hsemi_ev
  filter_upwards [hyr, hydelta_ev, hysemi_ev] with
      y hy_r hy_delta hsemi_lt
  have hy_closed : y.1 ∈ Metric.closedBall p.1 r := by
    simpa [Metric.mem_closedBall] using hy_r.le
  have hscalar_lt :
      dist
          (osiiStageMovingSliceDistribution
            A rho hrho_compact y.1 p.2)
          (osiiStageMovingSliceDistribution
            A rho hrho_compact p.1 p.2) <
        epsilon / 2 :=
    hscalar_delta hy_delta
  have hfirst :
      ‖osiiStageMovingSliceDistribution
          A rho hrho_compact y.1 (y.2 - p.2)‖ <
        epsilon / 2 := by
    calc
      ‖osiiStageMovingSliceDistribution
          A rho hrho_compact y.1 (y.2 - p.2)‖
          ≤ C * q (y.2 - p.2) := by
            simpa [q] using
              hbound y.1 hy_closed (y.2 - p.2)
      _ < C * (epsilon / (2 * C)) :=
        mul_lt_mul_of_pos_left hsemi_lt hC
      _ = epsilon / 2 := by field_simp [hC.ne']
  calc
    dist
        (osiiStageMovingSliceDistribution
          A rho hrho_compact y.1 y.2)
        (osiiStageMovingSliceDistribution
          A rho hrho_compact p.1 p.2) =
      ‖osiiStageMovingSliceDistribution
          A rho hrho_compact y.1 y.2 -
        osiiStageMovingSliceDistribution
          A rho hrho_compact p.1 p.2‖ := by
          rw [dist_eq_norm]
    _ =
      ‖osiiStageMovingSliceDistribution
          A rho hrho_compact y.1 (y.2 - p.2) +
        (osiiStageMovingSliceDistribution
            A rho hrho_compact y.1 p.2 -
          osiiStageMovingSliceDistribution
            A rho hrho_compact p.1 p.2)‖ := by
        congr 1
        rw [map_sub]
        abel
    _ ≤
      ‖osiiStageMovingSliceDistribution
          A rho hrho_compact y.1 (y.2 - p.2)‖ +
        ‖osiiStageMovingSliceDistribution
            A rho hrho_compact y.1 p.2 -
          osiiStageMovingSliceDistribution
            A rho hrho_compact p.1 p.2‖ :=
      norm_add_le _ _
    _ < epsilon / 2 + epsilon / 2 := by
      exact add_lt_add hfirst
        (by simpa [dist_eq_norm] using hscalar_lt)
    _ = epsilon := by ring

end OSReconstruction
