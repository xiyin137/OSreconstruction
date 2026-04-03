/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValuesBase
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputCAssembly
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAStripUniqueness

/-!
# OS to Wightman Boundary Value Comparison Support

This file contains the two-point comparison, positivity-support, and low-degree
comparison lemmas extracted from `OSToWightmanBoundaryValuesBase.lean`.
The base file now stops before this growing comparison layer, so new OS-route
comparison material does not continue to accumulate in the giant support file.
-/

open scoped Classical NNReal
open BigOperators Finset

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The one-variable difference kernel seen on the Euclidean two-point
base-time shell after quotienting out the common translated point. -/
def bvt_twoPointImaginaryAxisDifferenceKernel_local
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    SpacetimeDim d → ℂ :=
  fun ξ =>
    bvt_F OS lgc 2 (fun k μ =>
      if _h0 : k = 0 then 0 else wickRotatePoint ξ μ)

/-- On the two-point Euclidean base-time shell, the center variable already
factors out by translation invariance of `bvt_F`. The remaining shell is the
pure imaginary-axis one-variable kernel `ξ ↦ bvt_F(0, wickRotatePoint ξ)`. -/
theorem bvt_twoPointDifferenceLift_baseTime_pairing_eq_imaginaryAxisKernel_local
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ h : SchwartzSpacetime d) (t : ℝ) :
    ∫ y : NPointDomain d 2,
      bvt_F OS lgc 2
        (xiShift 0 0 (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
        (twoPointDifferenceLift χ h) y =
      (∫ u : SpacetimeDim d, χ u) *
        ∫ ξ : SpacetimeDim d,
          bvt_twoPointImaginaryAxisDifferenceKernel_local OS lgc ξ * h ξ := by
  let K : SpacetimeDim d → ℂ := bvt_twoPointImaginaryAxisDifferenceKernel_local OS lgc
  calc
    ∫ y : NPointDomain d 2,
        bvt_F OS lgc 2
          (xiShift 0 0 (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
          (twoPointDifferenceLift χ h) y
      =
        ∫ z : NPointDomain d 2,
          bvt_F OS lgc 2
            (xiShift 0 0
              (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
              ((t : ℂ) * Complex.I)) *
            (χ (z 0) * h (z 1)) := by
          simpa using
            (integral_mul_twoPointDifferenceLift_eq_centerDiff
              (d := d)
              (Ψ := fun y : NPointDomain d 2 =>
                bvt_F OS lgc 2
                  (xiShift 0 0 (fun i => wickRotatePoint (y i))
                    ((t : ℂ) * Complex.I)))
              χ h)
    _ =
        ∫ z : NPointDomain d 2,
          K (z 1) * (χ (z 0) * h (z 1)) := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with z
          have hdecomp :
              xiShift 0 0
                  (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
                  ((t : ℂ) * Complex.I) =
                (fun j =>
                  (fun μ =>
                    if _h0 : j = 0 then 0 else wickRotatePoint (z 1) μ) +
                  (fun μ =>
                    wickRotatePoint (z 0) μ +
                      if μ = 0 then (t : ℂ) * Complex.I else 0)) := by
            funext j
            funext μ
            fin_cases j
            · by_cases hμ : μ = 0
              · subst hμ
                simp [xiShift, twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv,
                  wickRotatePoint]
              · simp [xiShift, twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv,
                  wickRotatePoint, hμ]
            · by_cases hμ : μ = 0
              · subst hμ
                simp [xiShift, twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv,
                  wickRotatePoint, add_comm, add_left_comm, add_assoc]
                ring
              · simp [xiShift, twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv,
                  wickRotatePoint, hμ, add_comm, add_left_comm, add_assoc]
          calc
            bvt_F OS lgc 2
                (xiShift 0 0
                  (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
                  ((t : ℂ) * Complex.I)) *
                (χ (z 0) * h (z 1))
              =
                bvt_F OS lgc 2
                  (fun j =>
                    (fun μ =>
                      if _h0 : j = 0 then 0 else wickRotatePoint (z 1) μ) +
                    (fun μ =>
                      wickRotatePoint (z 0) μ +
                        if μ = 0 then (t : ℂ) * Complex.I else 0)) *
                  (χ (z 0) * h (z 1)) := by
                    rw [hdecomp]
            _ = K (z 1) * (χ (z 0) * h (z 1)) := by
                  have htrans :
                      bvt_F OS lgc 2
                        (fun j =>
                          (fun μ =>
                            if _h0 : j = 0 then 0 else wickRotatePoint (z 1) μ) +
                          (fun μ =>
                            wickRotatePoint (z 0) μ +
                              if μ = 0 then (t : ℂ) * Complex.I else 0)) =
                      bvt_F OS lgc 2
                        (fun j μ =>
                          if _h0 : j = 0 then 0 else wickRotatePoint (z 1) μ) := by
                    simpa using
                      bvt_F_translationInvariant (d := d) OS lgc 2
                        (fun j μ =>
                          if _h0 : j = 0 then 0 else wickRotatePoint (z 1) μ)
                        (fun μ =>
                          wickRotatePoint (z 0) μ +
                            if μ = 0 then (t : ℂ) * Complex.I else 0)
                  rw [htrans]
                  simp [K, bvt_twoPointImaginaryAxisDifferenceKernel_local]
    _ =
        (∫ u : SpacetimeDim d, χ u) * ∫ ξ : SpacetimeDim d, K ξ * h ξ := by
          let eprod : NPointDomain d 2 ≃ᵐ (SpacetimeDim d × SpacetimeDim d) :=
            MeasurableEquiv.finTwoArrow
          have heprod :
              MeasureTheory.MeasurePreserving eprod
                MeasureTheory.volume MeasureTheory.volume := by
            simpa [eprod] using
              (MeasureTheory.volume_preserving_finTwoArrow (SpacetimeDim d))
          calc
            ∫ z : NPointDomain d 2, K (z 1) * (χ (z 0) * h (z 1))
              = ∫ p : SpacetimeDim d × SpacetimeDim d,
                  K p.2 * (χ p.1 * h p.2) := by
                    symm
                    simpa [eprod, MeasurableEquiv.finTwoArrow, mul_assoc] using
                      heprod.symm.integral_comp'
                        (g := fun z : NPointDomain d 2 => K (z 1) * (χ (z 0) * h (z 1)))
            _ = ∫ p : SpacetimeDim d × SpacetimeDim d,
                  χ p.1 * (K p.2 * h p.2) := by
                    refine MeasureTheory.integral_congr_ae ?_
                    filter_upwards with p
                    ring
            _ = (∫ u : SpacetimeDim d, χ u) * ∫ ξ : SpacetimeDim d, K ξ * h ξ := by
                    simpa [mul_assoc] using
                      (MeasureTheory.integral_prod_mul
                        (μ := (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d)))
                        (ν := (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d)))
                        (f := fun u : SpacetimeDim d => χ u)
                        (g := fun ξ : SpacetimeDim d => K ξ * h ξ))

/-- The positive-time Schwinger two-point difference shell already pairs
against the pure imaginary-axis one-variable kernel `ξ ↦ bvt_F(0,
wickRotatePoint ξ)`. This is the exact one-variable form of the Schwinger side
in the remaining two-point comparison problem. -/
theorem bvt_twoPointDifferenceLift_eq_imaginaryAxisKernel_of_positiveSupport_local
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ h : SchwartzSpacetime d)
    (hχ_pos : tsupport (χ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0}) :
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) =
      (∫ u : SpacetimeDim d, χ u) *
        ∫ ξ : SpacetimeDim d,
          bvt_twoPointImaginaryAxisDifferenceKernel_local OS lgc ξ * h ξ := by
  calc
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h))
      =
        ∫ y : NPointDomain d 2,
          bvt_F OS lgc 2
            (xiShift 0 0 (fun i => wickRotatePoint (y i)) ((1 : ℂ) * Complex.I)) *
            (twoPointDifferenceLift χ h) y := by
              symm
              exact bvt_twoPointDifferenceLift_baseTime_eq_constant_of_positiveSupport_local
                (d := d) (OS := OS) (lgc := lgc) χ h hχ_pos hh_pos 1 zero_lt_one
    _ =
      (∫ u : SpacetimeDim d, χ u) *
        ∫ ξ : SpacetimeDim d,
          bvt_twoPointImaginaryAxisDifferenceKernel_local OS lgc ξ * h ξ := by
            exact bvt_twoPointDifferenceLift_baseTime_pairing_eq_imaginaryAxisKernel_local
              (d := d) (OS := OS) (lgc := lgc) χ h 1

private theorem timeShiftVec_zero_local :
    timeShiftVec d (0 : ℝ) = 0 := by
  ext μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [timeShiftVec]
  · simp [timeShiftVec, hμ]

private theorem continuous_wickRotatePoint_local :
    Continuous (wickRotatePoint (d := d)) := by
  apply continuous_pi
  intro μ
  simp only [wickRotatePoint]
  split_ifs
  · exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply 0))
  · exact Complex.continuous_ofReal.comp (continuous_apply μ)

private theorem bvt_twoPointImaginaryAxisDifferenceKernel_eq_shifted_local
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (ξ : SpacetimeDim d) :
    bvt_twoPointImaginaryAxisDifferenceKernel_local OS lgc ξ =
      bvt_F OS lgc 2
        (fun k => wickRotatePoint
          ((![timeShiftVec d 1, ξ + timeShiftVec d 1] : NPointDomain d 2) k)) := by
  let a : Fin (d + 1) → ℂ := wickRotatePoint (timeShiftVec d 1)
  have htrans :=
    bvt_F_translationInvariant (d := d) OS lgc 2
      (fun j μ => if _h0 : j = 0 then 0 else wickRotatePoint ξ μ) a
  have hcfg :
      (fun j =>
        (fun μ => if _h0 : j = 0 then 0 else wickRotatePoint ξ μ) + a) =
        (fun k => wickRotatePoint
          ((![timeShiftVec d 1, ξ + timeShiftVec d 1] : NPointDomain d 2) k)) := by
    funext k
    fin_cases k
    · ext μ
      by_cases hμ : μ = 0
      · subst hμ
        simp [a, timeShiftVec, wickRotatePoint]
      · simp [a, timeShiftVec, wickRotatePoint, hμ]
    · ext μ
      by_cases hμ : μ = 0
      · subst hμ
        simp [a, timeShiftVec, wickRotatePoint]
        ring
      · simp [a, timeShiftVec, wickRotatePoint, hμ]
  have htrans' := htrans
  rw [hcfg] at htrans'
  simpa [bvt_twoPointImaginaryAxisDifferenceKernel_local, a] using htrans'.symm

/-- On compact positive-time test shells, the pure imaginary-axis BV
two-point kernel already induces exactly the same one-variable pairing as the
common zero-anchor K2 witness. This is the compact-support pairing input used
to recover the stronger pointwise positive-time kernel identity by strip
uniqueness. -/
theorem bvt_twoPointImaginaryAxisDifferenceKernel_pairing_eq_commonZeroAnchor_local
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (hχ₀_pos : tsupport (χ₀ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0}) :
    ∃ G : (Fin (2 * (d + 1)) → ℂ) → ℂ,
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2,
          G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x)) ∧
      (∀ u v : Fin (2 * (d + 1)) → ℂ,
        (∀ μ : Fin (d + 1),
          u (finProdFinEquiv (⟨1, by omega⟩, μ)) =
            v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
        G u = G v) ∧
      ∀ h : SchwartzSpacetime d,
        HasCompactSupport (h : SpacetimeDim d → ℂ) →
        tsupport (h : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | 0 < ξ 0} →
        ∫ ξ : SpacetimeDim d,
          OSReconstruction.commonZeroCenterShiftSection_local (d := d) G 0 ξ * h ξ =
            ∫ ξ : SpacetimeDim d,
              bvt_twoPointImaginaryAxisDifferenceKernel_local OS lgc ξ * h ξ := by
  obtain ⟨G, hG_holo, hG_euclid, hG_diff⟩ :=
    OSReconstruction.schwinger_continuation_base_step_timeParametric_of_translationInvariant_acrOne_local
      OS lgc
  refine ⟨G, hG_holo, hG_euclid, hG_diff, ?_⟩
  intro h hh_compact hh_pos
  let hpt : positiveTimeCompactSupportSubmodule d := ⟨h, ⟨hh_pos, hh_compact⟩⟩
  have hcommon_pair :
      ∫ ξ : SpacetimeDim d,
        OSReconstruction.commonDifferenceKernel_real_local (d := d) G ξ * h ξ =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) := by
    calc
      ∫ ξ : SpacetimeDim d,
          OSReconstruction.commonDifferenceKernel_real_local (d := d) G ξ * h ξ
        = (∫ u : SpacetimeDim d, χ₀ u) *
            ∫ ξ : SpacetimeDim d,
              OSReconstruction.commonDifferenceKernel_real_local (d := d) G ξ * h ξ := by
              rw [hχ₀]
              ring
      _ =
          ∫ x : NPointDomain d 2,
            OSReconstruction.commonK2TimeParametricKernel_real_local (d := d) G x *
              twoPointDifferenceLift χ₀ h x := by
                symm
                simpa [OSReconstruction.commonK2TimeParametricKernel_real_local] using
                  (OSReconstruction.integral_twoPointDifferenceKernel_mul_differenceLift_factorizes
                    (d := d)
                    (OSReconstruction.commonDifferenceKernel_real_local (d := d) G)
                    χ₀ h)
      _ =
          OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) := by
            simpa using
              OSReconstruction.commonK2TimeParametricKernel_real_eq_schwinger_on_differenceShell_of_positiveSupport_local
                (d := d) OS χ₀ hχ₀ G hG_euclid hG_diff χ₀ hpt
  have himag_pair :
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) =
        ∫ ξ : SpacetimeDim d,
          bvt_twoPointImaginaryAxisDifferenceKernel_local OS lgc ξ * h ξ := by
    simpa [hχ₀] using
      bvt_twoPointDifferenceLift_eq_imaginaryAxisKernel_of_positiveSupport_local
        (OS := OS) (lgc := lgc) χ₀ h hχ₀_pos hh_pos
  have hzero_eq_common :
      ∫ ξ : SpacetimeDim d,
        OSReconstruction.commonZeroCenterShiftSection_local (d := d) G 0 ξ * h ξ =
      ∫ ξ : SpacetimeDim d,
        OSReconstruction.commonDifferenceKernel_real_local (d := d) G ξ * h ξ := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with ξ
    by_cases hzero : h ξ = 0
    · simp [hzero]
    · have hmem : ξ ∈ tsupport (h : SpacetimeDim d → ℂ) := by
        exact subset_tsupport _ (Function.mem_support.mpr hzero)
      have hξ : 0 < ξ 0 := hh_pos hmem
      have hnotneg : ¬ ξ 0 < 0 := by linarith
      calc
        OSReconstruction.commonZeroCenterShiftSection_local (d := d) G 0 ξ * h ξ
          =
            k2TimeParametricKernel (d := d) G
              (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2) * h ξ := by
                simp [OSReconstruction.commonZeroCenterShiftSection_local,
                  timeShiftVec_zero_local]
        _ =
            OSReconstruction.commonDifferenceKernel_real_local (d := d) G ξ * h ξ := by
              simp [OSReconstruction.commonDifferenceKernel_real_local, hξ, hnotneg]
  calc
    ∫ ξ : SpacetimeDim d,
        OSReconstruction.commonZeroCenterShiftSection_local (d := d) G 0 ξ * h ξ
      =
        ∫ ξ : SpacetimeDim d,
          OSReconstruction.commonDifferenceKernel_real_local (d := d) G ξ * h ξ := hzero_eq_common
    _ =
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) :=
          hcommon_pair
    _ =
        ∫ ξ : SpacetimeDim d,
          bvt_twoPointImaginaryAxisDifferenceKernel_local OS lgc ξ * h ξ := himag_pair

/-- On the open positive-time region, the pure imaginary-axis BV two-point
kernel agrees pointwise with the common zero-anchor K2 difference kernel. This
restores the strongest Schwinger-side common-kernel identification lost during
the file split. -/
theorem bvt_twoPointImaginaryAxisDifferenceKernel_eq_commonZeroAnchor_on_positiveTime_local
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (hχ₀_pos : tsupport (χ₀ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0}) :
    ∃ G : (Fin (2 * (d + 1)) → ℂ) → ℂ,
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2,
          G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x)) ∧
      (∀ u v : Fin (2 * (d + 1)) → ℂ,
        (∀ μ : Fin (d + 1),
          u (finProdFinEquiv (⟨1, by omega⟩, μ)) =
            v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
        G u = G v) ∧
      Set.EqOn
        (bvt_twoPointImaginaryAxisDifferenceKernel_local OS lgc)
        (OSReconstruction.commonDifferenceKernel_real_local (d := d) G)
        {ξ : SpacetimeDim d | 0 < ξ 0} := by
  obtain ⟨G, hG_holo, hG_euclid, hG_diff, hpair_eq⟩ :=
    bvt_twoPointImaginaryAxisDifferenceKernel_pairing_eq_commonZeroAnchor_local
      (OS := OS) (lgc := lgc) χ₀ hχ₀ hχ₀_pos
  let Kshift : SpacetimeDim d → ℂ := fun ξ =>
    bvt_F OS lgc 2
      (fun k => wickRotatePoint
        ((![timeShiftVec d 1, ξ + timeShiftVec d 1] : NPointDomain d 2) k))
  have hKshift_cont :
      ContinuousOn Kshift {ξ : SpacetimeDim d | 0 < ξ 0} := by
    have hcfg_cont :
        Continuous (fun ξ : SpacetimeDim d =>
          (fun k => wickRotatePoint
            ((![timeShiftVec d 1, ξ + timeShiftVec d 1] : NPointDomain d 2) k))) := by
      apply continuous_pi
      intro k
      fin_cases k
      · simpa using
          (continuous_const :
            Continuous (fun _ : SpacetimeDim d => wickRotatePoint (timeShiftVec d 1)))
      · exact (continuous_wickRotatePoint_local (d := d)).comp
          ((continuous_id : Continuous fun ξ : SpacetimeDim d => ξ).add
            (continuous_const : Continuous fun _ : SpacetimeDim d => timeShiftVec d 1))
    refine (bvt_F_holomorphic (d := d) OS lgc 2).continuousOn.comp hcfg_cont.continuousOn ?_
    intro ξ hξ
    have hξ0 : 0 < ξ 0 := by simpa using hξ
    let xs : NPointDomain d 2 := ![timeShiftVec d 1, ξ + timeShiftVec d 1]
    have hxs_ord : ∀ k j : Fin 2, k < j → xs k 0 < xs j 0 := by
      intro k j hkj
      have hk0 : k = 0 := by omega
      have hj1 : j = 1 := by omega
      subst hk0
      subst hj1
      simp [xs, timeShiftVec]
      linarith
    have hxs_pos : ∀ k : Fin 2, 0 < xs k 0 := by
      intro k
      fin_cases k
      · simp [xs, timeShiftVec]
      · simp [xs, timeShiftVec]
        linarith
    exact euclidean_ordered_in_forwardTube (d := d) (n := 2) xs hxs_ord hxs_pos
  have hK_cont :
      ContinuousOn
        (bvt_twoPointImaginaryAxisDifferenceKernel_local OS lgc)
        {ξ : SpacetimeDim d | 0 < ξ 0} := by
    refine hKshift_cont.congr ?_
    intro ξ hξ
    exact bvt_twoPointImaginaryAxisDifferenceKernel_eq_shifted_local
      (OS := OS) (lgc := lgc) ξ
  have hEq0 :
      Set.EqOn
        (OSReconstruction.commonZeroCenterShiftSection_local (d := d) G 0)
        (bvt_twoPointImaginaryAxisDifferenceKernel_local OS lgc)
        {ξ : SpacetimeDim d | 0 < ξ 0} := by
    have hK_cont0 :
        ContinuousOn
          (bvt_twoPointImaginaryAxisDifferenceKernel_local OS lgc)
          {ξ : SpacetimeDim d | -(0 + 0) < ξ 0} := by
      simpa using hK_cont
    have hpair_eq0 :
        ∀ h : SchwartzSpacetime d,
          HasCompactSupport (h : SpacetimeDim d → ℂ) →
          tsupport (h : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | -(0 + 0) < ξ 0} →
          ∫ ξ : SpacetimeDim d,
            OSReconstruction.commonZeroCenterShiftSection_local (d := d) G 0 ξ * h ξ =
            ∫ ξ : SpacetimeDim d,
              bvt_twoPointImaginaryAxisDifferenceKernel_local OS lgc ξ * h ξ := by
      intro h hh_compact hh_strip
      exact hpair_eq h hh_compact (by simpa using hh_strip)
    simpa using
      (OSReconstruction.zeroCenterShift_eq_comparison_of_compactSupport_pairing_eq_local
        (d := d) G hG_holo hG_diff
        (bvt_twoPointImaginaryAxisDifferenceKernel_local OS lgc) 0 hK_cont0 hpair_eq0)
  refine ⟨G, hG_holo, hG_euclid, hG_diff, ?_⟩
  intro ξ hξ
  have hξ0 : 0 < ξ 0 := by simpa using hξ
  have hnotneg : ¬ ξ 0 < 0 := by linarith
  calc
    bvt_twoPointImaginaryAxisDifferenceKernel_local OS lgc ξ
      = OSReconstruction.commonZeroCenterShiftSection_local (d := d) G 0 ξ := by
          exact (hEq0 hξ).symm
    _ =
        k2TimeParametricKernel (d := d) G
          (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2) := by
            simp [OSReconstruction.commonZeroCenterShiftSection_local,
              timeShiftVec_zero_local]
    _ = OSReconstruction.commonDifferenceKernel_real_local (d := d) G ξ := by
          simp [OSReconstruction.commonDifferenceKernel_real_local, hξ0, hnotneg]

def canonicalForwardConeDirection (n : ℕ) : Fin n → Fin (d + 1) → ℝ :=
  fun k μ => if μ = 0 then (↑(k : ℕ) + 1 : ℝ) else 0

theorem canonicalForwardConeDirection_mem (n : ℕ) :
    InForwardCone d n (canonicalForwardConeDirection (d := d) n) := by
  let η₀ : Fin (d + 1) → ℝ := fun μ => if μ = 0 then 1 else 0
  have hη₀ : InOpenForwardCone d η₀ := by
    constructor
    · simp [η₀]
    · simp only [MinkowskiSpace.minkowskiNormSq, MinkowskiSpace.minkowskiInner, η₀]
      have : ∀ i : Fin (d + 1), (MinkowskiSpace.metricSignature d i *
          (if i = 0 then (1 : ℝ) else 0)) * (if i = 0 then 1 else 0) =
          if i = 0 then -1 else 0 := by
        intro i
        split_ifs with h <;> simp [MinkowskiSpace.metricSignature, h]
      simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      norm_num
  rw [inForwardCone_iff_mem_forwardConeAbs]
  intro k
  simp only []
  convert hη₀ using 1
  ext μ
  split_ifs with h
  · simp [canonicalForwardConeDirection, η₀, h]
  · by_cases hμ : μ = 0
    · simp [canonicalForwardConeDirection, η₀, hμ]
      have hk_pos : (k : ℕ) ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
      have : (↑(↑k - 1 : ℕ) : ℝ) = (↑(k : ℕ) : ℝ) - 1 := by
        rw [Nat.cast_sub hk_pos]
        simp
      rw [this]
      ring
    · simp [canonicalForwardConeDirection, η₀, hμ]

/-- The reduced one-variable kernel seen by the canonical two-point BV ray
after quotienting out the common translation direction. -/
def bvt_twoPointCanonicalDifferenceKernel_local
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (ε : ℝ) : SpacetimeDim d → ℂ :=
  fun ξ =>
    bvt_F OS lgc 2 (fun k μ =>
      if h0 : k = 0 then 0
      else if μ = 0 then ↑(ξ μ) + (ε : ℂ) * Complex.I else ↑(ξ μ))

/-- On the canonical two-point boundary ray, the center variable already factors
out by complex translation invariance of `bvt_F`. The resulting fixed-`ε`
pairing is therefore a one-variable difference-kernel pairing scaled by
`∫ χ`. -/
theorem bvt_twoPointDifferenceLift_canonical_pairing_eq_reducedKernel_local
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ h : SchwartzSpacetime d) (ε : ℝ) :
    ∫ x : NPointDomain d 2,
      bvt_F OS lgc 2 (fun k μ =>
        ↑(x k μ) + ε * ↑(canonicalForwardConeDirection (d := d) 2 k μ) * Complex.I) *
        (twoPointDifferenceLift χ h x) =
      (∫ u : SpacetimeDim d, χ u) *
        ∫ ξ : SpacetimeDim d,
          bvt_twoPointCanonicalDifferenceKernel_local OS lgc ε ξ * h ξ := by
  let K : SpacetimeDim d → ℂ := bvt_twoPointCanonicalDifferenceKernel_local OS lgc ε
  calc
    ∫ x : NPointDomain d 2,
        bvt_F OS lgc 2 (fun k μ =>
          ↑(x k μ) + ε * ↑(canonicalForwardConeDirection (d := d) 2 k μ) * Complex.I) *
          (twoPointDifferenceLift χ h x)
      =
        ∫ z : NPointDomain d 2,
          bvt_F OS lgc 2 (fun k μ =>
            ↑(((twoPointCenterDiffCLE d) z) k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) 2 k μ) * Complex.I) *
            (χ (z 0) * h (z 1)) := by
          simpa using
            (integral_mul_twoPointDifferenceLift_eq_centerDiff
              (d := d)
              (Ψ := fun x : NPointDomain d 2 =>
                bvt_F OS lgc 2 (fun k μ =>
                  ↑(x k μ) + ε * ↑(canonicalForwardConeDirection (d := d) 2 k μ) *
                    Complex.I))
              χ h)
    _ =
        ∫ z : NPointDomain d 2,
          K (z 1) * (χ (z 0) * h (z 1)) := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with z
          have hdecomp :
              (fun k μ =>
                ↑(((twoPointCenterDiffCLE d) z) k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) 2 k μ) * Complex.I) =
              (fun j =>
                (fun μ =>
                  if h0 : j = 0 then 0
                  else if μ = 0 then ↑(z 1 μ) + (ε : ℂ) * Complex.I else ↑(z 1 μ)) +
                (fun μ => ↑(z 0 μ) + ε *
                  ↑(canonicalForwardConeDirection (d := d) 2 0 μ) * Complex.I)) := by
            funext k
            funext μ
            fin_cases k
            · simp [twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv,
                canonicalForwardConeDirection]
            · by_cases hμ : μ = 0
              · subst hμ
                simp [twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv,
                  canonicalForwardConeDirection]
                ring
              · simp [twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv,
                  canonicalForwardConeDirection, hμ, add_comm, add_left_comm, add_assoc]
          calc
            bvt_F OS lgc 2 (fun k μ =>
              ↑(((twoPointCenterDiffCLE d) z) k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) 2 k μ) * Complex.I) *
                (χ (z 0) * h (z 1))
              =
                bvt_F OS lgc 2
                  (fun j =>
                    (fun μ =>
                      if h0 : j = 0 then 0
                      else if μ = 0 then ↑(z 1 μ) + (ε : ℂ) * Complex.I else ↑(z 1 μ)) +
                    (fun μ => ↑(z 0 μ) + ε *
                      ↑(canonicalForwardConeDirection (d := d) 2 0 μ) * Complex.I)) *
                  (χ (z 0) * h (z 1)) := by
                    rw [hdecomp]
            _ = K (z 1) * (χ (z 0) * h (z 1)) := by
                  have htrans :
                      bvt_F OS lgc 2
                        (fun j =>
                          (fun μ =>
                            if h0 : j = 0 then 0
                            else if μ = 0 then ↑(z 1 μ) + (ε : ℂ) * Complex.I else ↑(z 1 μ)) +
                          (fun μ => ↑(z 0 μ) + ε *
                            ↑(canonicalForwardConeDirection (d := d) 2 0 μ) * Complex.I)) =
                      bvt_F OS lgc 2
                        (fun j μ =>
                          if h0 : j = 0 then 0
                          else if μ = 0 then ↑(z 1 μ) + (ε : ℂ) * Complex.I else ↑(z 1 μ)) := by
                    simpa using
                      bvt_F_translationInvariant (d := d) OS lgc 2
                        (fun j μ =>
                          if h0 : j = 0 then 0
                          else if μ = 0 then ↑(z 1 μ) + (ε : ℂ) * Complex.I else ↑(z 1 μ))
                        (fun μ => ↑(z 0 μ) + ε *
                          ↑(canonicalForwardConeDirection (d := d) 2 0 μ) * Complex.I)
                  rw [htrans]
                  simp [K, bvt_twoPointCanonicalDifferenceKernel_local]
    _ =
        (∫ u : SpacetimeDim d, χ u) * ∫ ξ : SpacetimeDim d, K ξ * h ξ := by
          let eprod : NPointDomain d 2 ≃ᵐ (SpacetimeDim d × SpacetimeDim d) :=
            MeasurableEquiv.finTwoArrow
          have heprod :
              MeasureTheory.MeasurePreserving eprod
                MeasureTheory.volume MeasureTheory.volume := by
            simpa [eprod] using
              (MeasureTheory.volume_preserving_finTwoArrow (SpacetimeDim d))
          calc
            ∫ z : NPointDomain d 2, K (z 1) * (χ (z 0) * h (z 1))
              = ∫ p : SpacetimeDim d × SpacetimeDim d,
                  K p.2 * (χ p.1 * h p.2) := by
                    symm
                    simpa [eprod, MeasurableEquiv.finTwoArrow, mul_assoc] using
                      heprod.symm.integral_comp'
                        (g := fun z : NPointDomain d 2 => K (z 1) * (χ (z 0) * h (z 1)))
            _ = ∫ p : SpacetimeDim d × SpacetimeDim d,
                  χ p.1 * (K p.2 * h p.2) := by
                    refine MeasureTheory.integral_congr_ae ?_
                    filter_upwards with p
                    ring
            _ = (∫ u : SpacetimeDim d, χ u) * ∫ ξ : SpacetimeDim d, K ξ * h ξ := by
                    simpa [mul_assoc] using
                      (MeasureTheory.integral_prod_mul
                        (μ := (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d)))
                        (ν := (MeasureTheory.volume : MeasureTheory.Measure (SpacetimeDim d)))
                        (f := fun u : SpacetimeDim d => χ u)
                        (g := fun ξ : SpacetimeDim d => K ξ * h ξ))

/-- Fixing a normalized center cutoff `χ₀` turns the canonical two-point BV
pairing into a genuine one-variable boundary-limit problem in the difference
variable. This isolates the remaining normalized-center comparison scalar in
the exact reduced form needed by the current K2 route. -/
theorem bvt_tendsto_twoPointCanonicalDifferenceKernel_of_normalizedCenter_local
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ₀ h : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1) :
    Filter.Tendsto
      (fun ε : ℝ =>
        ∫ ξ : SpacetimeDim d,
          bvt_twoPointCanonicalDifferenceKernel_local OS lgc ε ξ * h ξ)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (bvt_W OS lgc 2 (twoPointDifferenceLift χ₀ h))) := by
  have hBV :=
    bvt_boundary_values (d := d) OS lgc 2 (twoPointDifferenceLift χ₀ h)
      (canonicalForwardConeDirection (d := d) 2)
      (canonicalForwardConeDirection_mem (d := d) 2)
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d 2,
          bvt_F OS lgc 2 (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) 2 k μ) * Complex.I) *
            (twoPointDifferenceLift χ₀ h x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        ∫ ξ : SpacetimeDim d,
          bvt_twoPointCanonicalDifferenceKernel_local OS lgc ε ξ * h ξ) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [bvt_twoPointDifferenceLift_canonical_pairing_eq_reducedKernel_local
      (OS := OS) (lgc := lgc) (χ := χ₀) (h := h) (ε := ε)]
    simp [hχ₀]
  exact Filter.Tendsto.congr' hEq hBV

/-- The remaining normalized compact two-point comparison problem is exactly a
one-variable boundary-limit problem for the canonical BV difference kernel.

If the canonical kernel pairing tends to a common one-variable kernel `G`, and
that same kernel already agrees with the Schwinger-side imaginary-axis kernel
on positive time, then the reconstructed two-point boundary value equals the
Euclidean Schwinger functional on the corresponding difference shell. -/
theorem bvt_twoPointDifferenceLift_eq_schwinger_of_tendsto_canonicalDifferenceKernel_to_common_local
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ₀ h : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (hχ₀_pos : tsupport (χ₀ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hEqOn :
      Set.EqOn
        (bvt_twoPointImaginaryAxisDifferenceKernel_local OS lgc)
        (OSReconstruction.commonDifferenceKernel_real_local (d := d) G)
        {ξ : SpacetimeDim d | 0 < ξ 0})
    (hcanon :
      Filter.Tendsto
        (fun ε : ℝ =>
          ∫ ξ : SpacetimeDim d,
            bvt_twoPointCanonicalDifferenceKernel_local OS lgc ε ξ * h ξ)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (∫ ξ : SpacetimeDim d,
            OSReconstruction.commonDifferenceKernel_real_local (d := d) G ξ * h ξ))) :
    bvt_W OS lgc 2 (twoPointDifferenceLift χ₀ h) =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) := by
  have hBV :
      Filter.Tendsto
        (fun ε : ℝ =>
          ∫ ξ : SpacetimeDim d,
            bvt_twoPointCanonicalDifferenceKernel_local OS lgc ε ξ * h ξ)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (bvt_W OS lgc 2 (twoPointDifferenceLift χ₀ h))) :=
    bvt_tendsto_twoPointCanonicalDifferenceKernel_of_normalizedCenter_local
      (d := d) (OS := OS) (lgc := lgc) χ₀ h hχ₀
  have hW_eq_common :
      bvt_W OS lgc 2 (twoPointDifferenceLift χ₀ h) =
        ∫ ξ : SpacetimeDim d,
          OSReconstruction.commonDifferenceKernel_real_local (d := d) G ξ * h ξ :=
    tendsto_nhds_unique hBV hcanon
  have himag_eq_common :
      ∫ ξ : SpacetimeDim d,
        bvt_twoPointImaginaryAxisDifferenceKernel_local OS lgc ξ * h ξ =
      ∫ ξ : SpacetimeDim d,
        OSReconstruction.commonDifferenceKernel_real_local (d := d) G ξ * h ξ := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with ξ
    by_cases hzero : h ξ = 0
    · simp [hzero]
    · have hmem : ξ ∈ tsupport (h : SpacetimeDim d → ℂ) := by
        exact subset_tsupport _ (Function.mem_support.mpr hzero)
      have hξ : 0 < ξ 0 := hh_pos hmem
      simp [hEqOn hξ]
  have hS_eq_common :
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h)) =
        ∫ ξ : SpacetimeDim d,
          OSReconstruction.commonDifferenceKernel_real_local (d := d) G ξ * h ξ := by
    calc
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ₀ h))
        =
          ∫ ξ : SpacetimeDim d,
            bvt_twoPointImaginaryAxisDifferenceKernel_local OS lgc ξ * h ξ := by
              simpa [hχ₀] using
                bvt_twoPointDifferenceLift_eq_imaginaryAxisKernel_of_positiveSupport_local
                  (OS := OS) (lgc := lgc) χ₀ h hχ₀_pos hh_pos
      _ =
          ∫ ξ : SpacetimeDim d,
            OSReconstruction.commonDifferenceKernel_real_local (d := d) G ξ * h ξ :=
              himag_eq_common
  exact hW_eq_common.trans hS_eq_common.symm

theorem bvt_F_negCanonical (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    ∀ (x : NPointDomain d n) (ε : ℝ), 0 < ε →
      starRingEnd ℂ
        (bvt_F OS lgc n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)) =
      bvt_F OS lgc n (fun k μ =>
        ↑(x k μ) -
          ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) :=
  by
    intro x ε hε
    have hF_negCanonical :
        ∀ (x : NPointDomain d n) (ε : ℝ), 0 < ε →
          starRingEnd ℂ
            ((full_analytic_continuation_with_symmetry_growth OS lgc n).choose
              (fun j μ =>
                ↑(x j μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) n j μ) * Complex.I)) =
          (full_analytic_continuation_with_symmetry_growth OS lgc n).choose
            (fun j μ =>
              ↑(x j μ) -
                ε * ↑(canonicalForwardConeDirection (d := d) n j μ) * Complex.I) := by
      rcases (full_analytic_continuation_with_symmetry_growth OS lgc n).choose_spec with
        ⟨_hhol, hrest⟩
      rcases hrest with ⟨_hF_euclid, hrest⟩
      rcases hrest with ⟨_hF_perm, hrest⟩
      rcases hrest with ⟨_hF_trans, hrest⟩
      exact hrest.1
    change
      starRingEnd ℂ
        ((full_analytic_continuation_with_symmetry_growth OS lgc n).choose
          (fun j μ =>
            ↑(x j μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n j μ) * Complex.I)) =
      (full_analytic_continuation_with_symmetry_growth OS lgc n).choose
        (fun j μ =>
          ↑(x j μ) -
            ε * ↑(canonicalForwardConeDirection (d := d) n j μ) * Complex.I)
    simpa [bvt_F, canonicalForwardConeDirection] using
      hF_negCanonical x ε hε

/-! #### Helper lemmas for property transfer: OS axiom → F_analytic → W_n -/

theorem bv_zero_point_is_evaluation (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (W_0 : SchwartzNPoint d 0 → ℂ)
    (F_0 : (Fin 0 → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d 0) (η : Fin 0 → Fin (d + 1) → ℝ),
      InForwardCone d 0 η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : Fin 0 → Fin (d + 1) → ℝ,
          F_0 (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_0 f)))
    (hEuclid : ∀ (f : ZeroDiagonalSchwartz d 0),
      OS.S 0 f = ∫ x : Fin 0 → Fin (d + 1) → ℝ,
        F_0 (fun k => wickRotatePoint (x k)) * (f.1 x)) :
    ∀ f : SchwartzNPoint d 0, W_0 f = f 0 := by
  intro f
  let η0 : Fin 0 → Fin (d + 1) → ℝ := fun k => Fin.elim0 k
  have hη0 : InForwardCone d 0 η0 := by
    intro k
    exact Fin.elim0 k
  set I0 : ℂ := ∫ x : Fin 0 → Fin (d + 1) → ℝ,
      F_0 (fun k => wickRotatePoint (x k)) * (f x)
  have hconst :
      ∀ ε : ℝ,
        (∫ x : Fin 0 → Fin (d + 1) → ℝ,
          F_0 (fun k μ => ↑(x k μ) + ε * ↑(η0 k μ) * Complex.I) * (f x)) = I0 := by
    intro ε
    unfold I0
    congr 1
    ext x
    have hz : (fun k μ => ↑(x k μ) + ε * ↑(η0 k μ) * Complex.I) =
        (fun k => wickRotatePoint (x k)) := by
      funext k
      exact Fin.elim0 k
    simp [hz]
  have hBV0 : Filter.Tendsto (fun ε : ℝ => I0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (W_0 f)) := by
    simpa [hconst] using hBV f η0 hη0
  have hI0 : Filter.Tendsto (fun ε : ℝ => I0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds I0) :=
    tendsto_const_nhds
  have hW0 : W_0 f = I0 :=
    tendsto_nhds_unique hBV0 hI0
  let f0 : ZeroDiagonalSchwartz d 0 := ⟨f, by
    intro k x hx
    rcases hx with ⟨i, _, _, _⟩
    exact Fin.elim0 i⟩
  calc
    W_0 f = I0 := hW0
    _ = OS.S 0 f0 := by simpa [I0, f0] using (hEuclid f0).symm
    _ = f 0 := lgc.normalized_zero f0

/-- If the left factor is concentrated in degree `0`, the full compact ordered
positive-time comparison against an arbitrary right Borchers vector is already
formal: the `m = 0` term is normalization, and every `m > 0` term is the
singleton/singleton `xiShift` comparison already established above. -/
theorem bvt_wightmanInner_zero_left_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (g : SchwartzNPoint d 0)
    (hg_ord : tsupport ((g : SchwartzNPoint d 0) :
        NPointDomain d 0 → ℂ) ⊆ OrderedPositiveTimeRegion d 0)
    (hg_compact : HasCompactSupport ((g : SchwartzNPoint d 0) :
        NPointDomain d 0 → ℂ))
    (G : PositiveTimeBorchersSequence d)
    (hG_compact :
      ∀ m,
        HasCompactSupport ((((G : BorchersSequence d).funcs m : SchwartzNPoint d m) :
          NPointDomain d m → ℂ)))
    (hWlimit :
      ∀ m (hm : 0 < m),
        Filter.Tendsto
          (fun t : ℝ =>
            ∫ y : NPointDomain d (0 + m),
              bvt_F OS lgc (0 + m)
                  (xiShift ⟨0, Nat.lt_add_of_pos_right hm⟩ 0
                    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                ((g.osConjTensorProduct ((G : BorchersSequence d).funcs m)) y))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (bvt_W OS lgc (0 + m)
              (g.conjTensorProduct ((G : BorchersSequence d).funcs m))))) :
    WightmanInnerProduct d (bvt_W OS lgc)
      (BorchersSequence.single 0 g) (G : BorchersSequence d)
      =
    PositiveTimeBorchersSequence.osInner OS
      (PositiveTimeBorchersSequence.single 0 g hg_ord) G := by
  rw [WightmanInnerProduct_eq_sum_right_singles (d := d) (W := bvt_W OS lgc)
    (bvt_W_linear (d := d) OS lgc) (F := BorchersSequence.single 0 g)
    (G := (G : BorchersSequence d))]
  rw [PositiveTimeBorchersSequence.osInner_eq_sum_right_singles (d := d) OS
    (PositiveTimeBorchersSequence.single 0 g hg_ord) G]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hm0 : m = 0
  · subst hm0
    let x0 : NPointDomain d 0 := 0
    have hconj0 : g.borchersConj = g.osConj := by
      ext x
      have hx : x = x0 := by
        funext i
        exact Fin.elim0 i
      subst hx
      have harg : (fun i => x0 (Fin.rev i)) = timeReflectionN d x0 := by
        ext i μ
        exact Fin.elim0 i
      rw [SchwartzMap.borchersConj_apply, SchwartzNPoint.osConj_apply]
      simpa [harg]
    have hvanish0 :
        VanishesToInfiniteOrderOnCoincidence
          (g.osConjTensorProduct ((G : BorchersSequence d).funcs 0)) := by
      intro k x hx
      rcases hx with ⟨i, _, _, _⟩
      exact Fin.elim0 i
    have hW0_eval :
        bvt_W OS lgc 0 (g.conjTensorProduct ((G : BorchersSequence d).funcs 0))
          =
        (g.conjTensorProduct ((G : BorchersSequence d).funcs 0)) x0 := by
      simpa [x0] using
        bv_zero_point_is_evaluation (d := d) OS lgc
          (bvt_W OS lgc 0) (bvt_F OS lgc 0)
          (bvt_boundary_values OS lgc 0)
          (bvt_euclidean_restriction (d := d) OS lgc 0)
          (g.conjTensorProduct ((G : BorchersSequence d).funcs 0))
    calc
      WightmanInnerProduct d (bvt_W OS lgc)
          (BorchersSequence.single 0 g)
          (BorchersSequence.single 0 ((G : BorchersSequence d).funcs 0))
        =
          bvt_W OS lgc 0
            (g.conjTensorProduct ((G : BorchersSequence d).funcs 0)) := by
              simpa using
                WightmanInnerProduct_single_single (d := d) (W := bvt_W OS lgc)
                  (bvt_W_linear (d := d) OS lgc) 0 0 g ((G : BorchersSequence d).funcs 0)
      _ =
          (g.conjTensorProduct ((G : BorchersSequence d).funcs 0)) x0 := by
            exact hW0_eval
      _ =
          (g.osConjTensorProduct ((G : BorchersSequence d).funcs 0)) x0 := by
            simpa [SchwartzMap.conjTensorProduct, SchwartzNPoint.osConjTensorProduct, hconj0]
      _ =
          (ZeroDiagonalSchwartz.ofClassical
            (g.osConjTensorProduct ((G : BorchersSequence d).funcs 0))).1 x0 := by
              simpa using congrArg
                (fun h : SchwartzNPoint d 0 => h x0)
                (ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
                  (f := g.osConjTensorProduct ((G : BorchersSequence d).funcs 0)) hvanish0).symm
      _ =
          OS.S 0
            (ZeroDiagonalSchwartz.ofClassical
              (g.osConjTensorProduct ((G : BorchersSequence d).funcs 0))) := by
                symm
                simpa [x0] using lgc.normalized_zero
                  (ZeroDiagonalSchwartz.ofClassical
                    (g.osConjTensorProduct ((G : BorchersSequence d).funcs 0)))
      _ =
          OSInnerProduct d OS.S
            (BorchersSequence.single 0 g)
            (BorchersSequence.single 0 ((G : BorchersSequence d).funcs 0)) := by
              symm
              simpa using
                OSInnerProduct_single_single (d := d) OS.S OS.E0_linear
                  0 0 g ((G : BorchersSequence d).funcs 0)
      _ =
          PositiveTimeBorchersSequence.osInner OS
            (PositiveTimeBorchersSequence.single 0 g hg_ord)
            (PositiveTimeBorchersSequence.single 0 ((G : BorchersSequence d).funcs 0)
              (G.ordered_tsupport 0)) := by
              rfl
  · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
    simpa using
      bvt_wightmanInner_single_single_eq_osInner_of_tendsto_singleSplit_xiShift_nhdsWithin_zero
        (d := d) (OS := OS) (lgc := lgc) 0 m hm_pos
        g hg_ord hg_compact
        (((G : BorchersSequence d).funcs m))
        (G.ordered_tsupport m) (hG_compact m)
        (hWlimit m hm_pos)

/-- The new degree-`0`-on-the-left comparison can be flipped to the missing
degree-`0`-on-the-right pointwise comparison once Hermiticity of `bvt_W` is
available. This is the exact shape needed for the remaining `m = 0` positivity
seam. -/
theorem bvt_eq_schwinger_of_tendsto_singleSplit_xiShift_nhdsWithin_zero_zeroRight_of_hermitian
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (hherm :
      ∀ (n : ℕ) (f g : SchwartzNPoint d n),
        (∀ x : NPointDomain d n,
          g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
        bvt_W OS lgc n g = starRingEnd ℂ (bvt_W OS lgc n f))
    (n : ℕ) (hn : 0 < n)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport ((f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport ((f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (g : SchwartzNPoint d 0)
    (hg_ord : tsupport ((g : SchwartzNPoint d 0) :
        NPointDomain d 0 → ℂ) ⊆ OrderedPositiveTimeRegion d 0)
    (hg_compact : HasCompactSupport ((g : SchwartzNPoint d 0) :
        NPointDomain d 0 → ℂ))
    (hWlimit :
      Filter.Tendsto
        (fun t : ℝ =>
          ∫ y : NPointDomain d (0 + n),
            bvt_F OS lgc (0 + n)
                (xiShift ⟨0, Nat.lt_add_of_pos_right hn⟩ 0
                  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              ((g.osConjTensorProduct f) y))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (bvt_W OS lgc (0 + n)
            (g.conjTensorProduct f)))) :
    bvt_W OS lgc n (f.conjTensorProduct g) =
      OS.S n (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
  let Fn : PositiveTimeBorchersSequence d := PositiveTimeBorchersSequence.single n f hf_ord
  have hFn_compact :
      ∀ m,
        HasCompactSupport ((((Fn : BorchersSequence d).funcs m : SchwartzNPoint d m) :
          NPointDomain d m → ℂ)) := by
    intro m
    by_cases hm : m = n
    · subst hm
      simpa [Fn] using hf_compact
    · simpa [Fn, BorchersSequence.single_funcs_ne hm] using
        (HasCompactSupport.zero : HasCompactSupport (0 : NPointDomain d m → ℂ))
  have hFn_limit :
      ∀ m (hm : 0 < m),
        Filter.Tendsto
          (fun t : ℝ =>
            ∫ y : NPointDomain d (0 + m),
              bvt_F OS lgc (0 + m)
                  (xiShift ⟨0, Nat.lt_add_of_pos_right hm⟩ 0
                    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                ((g.osConjTensorProduct ((Fn : BorchersSequence d).funcs m)) y))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (bvt_W OS lgc (0 + m)
              (g.conjTensorProduct ((Fn : BorchersSequence d).funcs m)))) := by
    intro m hm
    by_cases hmn : m = n
    · subst hmn
      simpa [Fn] using hWlimit
    · have hfunc0 : ((Fn : BorchersSequence d).funcs m) = 0 := by
        simpa [Fn] using (BorchersSequence.single_funcs_ne hmn f)
      rw [hfunc0, SchwartzNPoint.osConjTensorProduct_zero_right]
      have htarget :
          bvt_W OS lgc (0 + m) (g.conjTensorProduct (0 : SchwartzNPoint d m)) = 0 := by
        rw [SchwartzMap.conjTensorProduct_zero_right,
          (bvt_W_linear (d := d) OS lgc (0 + m)).map_zero]
      rw [htarget]
      simpa using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (0 : ℂ))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
  have hleft :
      WightmanInnerProduct d (bvt_W OS lgc)
          (BorchersSequence.single 0 g) (Fn : BorchersSequence d)
        =
      PositiveTimeBorchersSequence.osInner OS
        (PositiveTimeBorchersSequence.single 0 g hg_ord) Fn := by
    exact
      bvt_wightmanInner_zero_left_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero
        (d := d) (OS := OS) (lgc := lgc) g hg_ord hg_compact Fn hFn_compact hFn_limit
  have hright :
      WightmanInnerProduct d (bvt_W OS lgc)
          (BorchersSequence.single n f) (BorchersSequence.single 0 g)
        =
      PositiveTimeBorchersSequence.osInner OS Fn
        (PositiveTimeBorchersSequence.single 0 g hg_ord) := by
    calc
      WightmanInnerProduct d (bvt_W OS lgc)
          (BorchersSequence.single n f) (BorchersSequence.single 0 g)
        =
      starRingEnd ℂ
        (WightmanInnerProduct d (bvt_W OS lgc)
          (BorchersSequence.single 0 g) (BorchersSequence.single n f)) := by
            simpa using
              WightmanInnerProduct_hermitian_of (d := d) (W := bvt_W OS lgc)
                hherm (BorchersSequence.single n f) (BorchersSequence.single 0 g)
      _ =
      starRingEnd ℂ
        (PositiveTimeBorchersSequence.osInner OS
          (PositiveTimeBorchersSequence.single 0 g hg_ord) Fn) := by
            simpa [Fn] using congrArg (starRingEnd ℂ) hleft
      _ =
      PositiveTimeBorchersSequence.osInner OS Fn
        (PositiveTimeBorchersSequence.single 0 g hg_ord) := by
            simpa [Fn] using
              (PositiveTimeBorchersSequence.osInner_hermitian OS Fn
                (PositiveTimeBorchersSequence.single 0 g hg_ord)).symm
  calc
    bvt_W OS lgc n (f.conjTensorProduct g)
      =
    WightmanInnerProduct d (bvt_W OS lgc)
      (BorchersSequence.single n f) (BorchersSequence.single 0 g) := by
        symm
        simpa using
          WightmanInnerProduct_single_single (d := d) (W := bvt_W OS lgc)
            (bvt_W_linear (d := d) OS lgc) n 0 f g
    _ =
      PositiveTimeBorchersSequence.osInner OS Fn
        (PositiveTimeBorchersSequence.single 0 g hg_ord) := hright
    _ =
      OSInnerProduct d OS.S (Fn : BorchersSequence d)
        (BorchersSequence.single 0 g) := by
          rfl
    _ = OS.S n (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
          simpa [Fn] using
            OSInnerProduct_single_single (d := d) OS.S OS.E0_linear n 0 f g

/-- For compact ordered positive-time Borchers vectors, the componentwise
single-split `xiShift` shell comparisons imply the full self-pair comparison
once the remaining degree-`0` right component is discharged using Hermiticity.
This packages the exact repair used by the active positivity lane. -/
theorem bvt_wightmanInner_self_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero_of_hermitian
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (hherm :
      ∀ (n : ℕ) (f g : SchwartzNPoint d n),
        (∀ x : NPointDomain d n,
          g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
        bvt_W OS lgc n g = starRingEnd ℂ (bvt_W OS lgc n f))
    (F : PositiveTimeBorchersSequence d)
    (hF_compact :
      ∀ n,
        HasCompactSupport ((((F : BorchersSequence d).funcs n : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)))
    (hWlimit :
      ∀ n m (hm : 0 < m),
        Filter.Tendsto
          (fun t : ℝ =>
            ∫ y : NPointDomain d (n + m),
              bvt_F OS lgc (n + m)
                  (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                ((((F : BorchersSequence d).funcs n).osConjTensorProduct
                  ((F : BorchersSequence d).funcs m)) y))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (bvt_W OS lgc (n + m)
              ((((F : BorchersSequence d).funcs n).conjTensorProduct
                ((F : BorchersSequence d).funcs m)))))) :
    WightmanInnerProduct d (bvt_W OS lgc)
      (F : BorchersSequence d) (F : BorchersSequence d) =
      PositiveTimeBorchersSequence.osInner OS F F := by
  have hzero :
      ∀ n,
        bvt_W OS lgc n
          ((((F : BorchersSequence d).funcs n).conjTensorProduct
            ((F : BorchersSequence d).funcs 0))) =
          OS.S n (ZeroDiagonalSchwartz.ofClassical
            ((((F : BorchersSequence d).funcs n).osConjTensorProduct
              ((F : BorchersSequence d).funcs 0)))) := by
    intro n
    by_cases hn0 : n = 0
    · subst hn0
      let x0 : NPointDomain d 0 := 0
      have hconj0 :
          ((F : BorchersSequence d).funcs 0).borchersConj =
            ((F : BorchersSequence d).funcs 0).osConj := by
        ext x
        have hx : x = x0 := by
          funext i
          exact Fin.elim0 i
        subst hx
        have harg : (fun i => x0 (Fin.rev i)) = timeReflectionN d x0 := by
          ext i μ
          exact Fin.elim0 i
        rw [SchwartzMap.borchersConj_apply, SchwartzNPoint.osConj_apply]
        simpa [harg]
      have hvanish0 :
          VanishesToInfiniteOrderOnCoincidence
            (((F : BorchersSequence d).funcs 0).osConjTensorProduct
              ((F : BorchersSequence d).funcs 0)) := by
        intro k x hx
        rcases hx with ⟨i, _, _, _⟩
        exact Fin.elim0 i
      have hW0_eval :
          bvt_W OS lgc 0
            (((F : BorchersSequence d).funcs 0).conjTensorProduct
              ((F : BorchersSequence d).funcs 0))
            =
          ((((F : BorchersSequence d).funcs 0).conjTensorProduct
            ((F : BorchersSequence d).funcs 0))) x0 := by
        simpa [x0] using
          bv_zero_point_is_evaluation (d := d) OS lgc
            (bvt_W OS lgc 0) (bvt_F OS lgc 0)
            (bvt_boundary_values OS lgc 0)
            (bvt_euclidean_restriction (d := d) OS lgc 0)
            ((((F : BorchersSequence d).funcs 0).conjTensorProduct
              ((F : BorchersSequence d).funcs 0)))
      calc
        bvt_W OS lgc 0
            (((F : BorchersSequence d).funcs 0).conjTensorProduct
              ((F : BorchersSequence d).funcs 0))
          =
            ((((F : BorchersSequence d).funcs 0).conjTensorProduct
              ((F : BorchersSequence d).funcs 0))) x0 := hW0_eval
        _ =
            ((((F : BorchersSequence d).funcs 0).osConjTensorProduct
              ((F : BorchersSequence d).funcs 0))) x0 := by
                simpa [SchwartzMap.conjTensorProduct, SchwartzNPoint.osConjTensorProduct, hconj0]
        _ =
            (ZeroDiagonalSchwartz.ofClassical
              (((F : BorchersSequence d).funcs 0).osConjTensorProduct
                ((F : BorchersSequence d).funcs 0))).1 x0 := by
                  simpa using congrArg
                    (fun h : SchwartzNPoint d 0 => h x0)
                    (ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
                      (f := ((F : BorchersSequence d).funcs 0).osConjTensorProduct
                        ((F : BorchersSequence d).funcs 0)) hvanish0).symm
        _ =
            OS.S 0 (ZeroDiagonalSchwartz.ofClassical
              ((((F : BorchersSequence d).funcs 0).osConjTensorProduct
                ((F : BorchersSequence d).funcs 0)))) := by
                  symm
                  simpa [x0] using lgc.normalized_zero
                    (ZeroDiagonalSchwartz.ofClassical
                      ((((F : BorchersSequence d).funcs 0).osConjTensorProduct
                        ((F : BorchersSequence d).funcs 0))))
    · have hn : 0 < n := Nat.pos_of_ne_zero hn0
      exact
        bvt_eq_schwinger_of_tendsto_singleSplit_xiShift_nhdsWithin_zero_zeroRight_of_hermitian
          (d := d) (OS := OS) (lgc := lgc) hherm
          n hn
          (((F : BorchersSequence d).funcs n))
          (F.ordered_tsupport n) (hF_compact n)
          (((F : BorchersSequence d).funcs 0))
          (F.ordered_tsupport 0) (hF_compact 0)
          (hWlimit 0 n hn)
  exact
    bvt_wightmanInner_eq_osInner_of_componentwise_tendsto_singleSplit_xiShift_nhdsWithin_zero
      (d := d) (OS := OS) (lgc := lgc) F F hF_compact hF_compact hzero hWlimit

private theorem bvt_F_one_eq_zero_local
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (z : Fin 1 → Fin (d + 1) → ℂ) :
    bvt_F OS lgc 1 z = bvt_F OS lgc 1 (fun _ _ => 0) := by
  let a : Fin (d + 1) → ℂ := fun μ => - z 0 μ
  have htrans := bvt_F_translationInvariant (d := d) OS lgc 1 z a
  have hzero : (fun j => z j + a) = (fun _ _ => 0) := by
    funext j μ
    fin_cases j
    simp [a]
  have hzero' : bvt_F OS lgc 1 (fun _ _ => 0) = bvt_F OS lgc 1 z := by
    simpa [hzero] using htrans
  exact hzero'.symm

private theorem bvt_W_one_eq_const_integral_local
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (f : SchwartzNPoint d 1) :
    bvt_W OS lgc 1 f =
      bvt_F OS lgc 1 (fun _ _ => 0) *
        ∫ x : NPointDomain d 1, f x := by
  let c : ℂ := bvt_F OS lgc 1 (fun _ _ => 0)
  have hBV :=
    bvt_boundary_values (d := d) OS lgc 1 f
      (canonicalForwardConeDirection (d := d) 1)
      (canonicalForwardConeDirection_mem (d := d) 1)
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d 1,
          bvt_F OS lgc 1 (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) 1 k μ) * Complex.I) * f x)
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun _ : ℝ => c * ∫ x : NPointDomain d 1, f x) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    calc
      ∫ x : NPointDomain d 1,
          bvt_F OS lgc 1 (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) 1 k μ) * Complex.I) * f x
          =
        ∫ x : NPointDomain d 1, c * f x := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with x
          rw [bvt_F_one_eq_zero_local (d := d) (OS := OS) (lgc := lgc)
            (z := fun k μ =>
              ↑(x k μ) + ε * ↑(canonicalForwardConeDirection (d := d) 1 k μ) * Complex.I)]
      _ = c * ∫ x : NPointDomain d 1, f x := by
          rw [MeasureTheory.integral_const_mul]
  have hconst :
      Filter.Tendsto
        (fun _ : ℝ => c * ∫ x : NPointDomain d 1, f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (c * ∫ x : NPointDomain d 1, f x)) :=
    tendsto_const_nhds
  have hBV' :
      Filter.Tendsto
        (fun _ : ℝ => c * ∫ x : NPointDomain d 1, f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (bvt_W OS lgc 1 f)) :=
    Filter.Tendsto.congr' hEq hBV
  exact tendsto_nhds_unique hBV' hconst

private theorem schwinger_one_eq_const_integral_local
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (f : SchwartzNPoint d 1) :
    OS.S 1 (ZeroDiagonalSchwartz.ofClassical f) =
      bvt_F OS lgc 1 (fun _ _ => 0) *
        ∫ x : NPointDomain d 1, f x := by
  let c : ℂ := bvt_F OS lgc 1 (fun _ _ => 0)
  calc
    OS.S 1 (ZeroDiagonalSchwartz.ofClassical f)
        =
      ∫ x : NPointDomain d 1,
        bvt_F OS lgc 1 (fun k => wickRotatePoint (x k)) *
          (ZeroDiagonalSchwartz.ofClassical f).1 x := by
          simpa using
            bvt_euclidean_restriction (d := d) OS lgc 1
              (ZeroDiagonalSchwartz.ofClassical f)
    _ =
      ∫ x : NPointDomain d 1,
        bvt_F OS lgc 1 (fun k => wickRotatePoint (x k)) * f x := by
          have hvan : VanishesToInfiniteOrderOnCoincidence f :=
            VanishesToInfiniteOrderOnCoincidence.one (d := d) f
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with x
          rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes (f := f) hvan]
    _ = ∫ x : NPointDomain d 1, c * f x := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with x
          rw [bvt_F_one_eq_zero_local (d := d) (OS := OS) (lgc := lgc)
            (z := fun k => wickRotatePoint (x k))]
    _ = c * ∫ x : NPointDomain d 1, f x := by
          rw [MeasureTheory.integral_const_mul]

/-- In one variable, translation invariance forces the reconstructed boundary
value functional to agree with the Euclidean Schwinger functional on all
Schwartz tests. This is the first exact one-factor comparison theorem on the BV
cluster lane. -/
theorem bvt_W_one_eq_schwinger
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (f : SchwartzNPoint d 1) :
    bvt_W OS lgc 1 f =
      OS.S 1 (ZeroDiagonalSchwartz.ofClassical f) := by
  rw [bvt_W_one_eq_const_integral_local (d := d) (OS := OS) (lgc := lgc) f,
    schwinger_one_eq_const_integral_local (d := d) (OS := OS) (lgc := lgc) f]

/-- Spacetime one-point tests therefore agree with their Euclidean Schwinger
values after boundary-value reconstruction, without additional support
hypotheses. -/
theorem bvt_W_onePointToFin1_eq_schwinger
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (g : SchwartzSpacetime d) :
    bvt_W OS lgc 1 (onePointToFin1CLM d g) =
      OS.S 1 (ZeroDiagonalSchwartz.ofClassical (onePointToFin1CLM d g)) := by
  simpa using bvt_W_one_eq_schwinger (d := d) OS lgc (onePointToFin1CLM d g)

private theorem schwinger_onePointToFin1_osConj_eq_star_local
    (OS : OsterwalderSchraderAxioms d) (χ : SchwartzSpacetime d) :
    OS.S 1 (ZeroDiagonalSchwartz.ofClassical
      (SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1))) =
      starRingEnd ℂ
        (OS.S 1 (ZeroDiagonalSchwartz.ofClassical (onePointToFin1CLM d χ))) := by
  let f : ZeroDiagonalSchwartz d 1 :=
    ZeroDiagonalSchwartz.ofClassical (onePointToFin1CLM d χ)
  let g : ZeroDiagonalSchwartz d 1 :=
    ZeroDiagonalSchwartz.ofClassical
      (SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1))
  have hreal :
      starRingEnd ℂ (OS.S 1 f) = OS.S 1 g := by
    refine OS.E0_reality (n := 1) (f := f) (g := g) ?_
    intro x
    rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
      (f := onePointToFin1CLM d χ)
      (VanishesToInfiniteOrderOnCoincidence.one (d := d) _)]
    rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
      (f := SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1))
      (VanishesToInfiniteOrderOnCoincidence.one (d := d) _)]
    simp [SchwartzNPoint.osConj_apply, onePointToFin1CLM_apply, timeReflectionN]
  simpa [f, g] using hreal.symm

/-- The BV reconstruction already identifies the left one-point `osConj` factor
with the conjugate of the ordinary one-point Schwinger value. This is the exact
mixed one-point comparison used later on the translated two-point cluster lane. -/
theorem bvt_W_onePointToFin1_osConj_eq_star_schwinger
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ : SchwartzSpacetime d) :
    bvt_W OS lgc 1
        (SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d χ : SchwartzNPoint d 1))
      =
    starRingEnd ℂ
      (OS.S 1 (ZeroDiagonalSchwartz.ofClassical (onePointToFin1CLM d χ))) := by
  calc
    bvt_W OS lgc 1
        (SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d χ : SchwartzNPoint d 1))
      =
    OS.S 1 (ZeroDiagonalSchwartz.ofClassical
      (SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1))) := by
          simpa using
            bvt_W_one_eq_schwinger (d := d) OS lgc
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d χ : SchwartzNPoint d 1))
    _ =
      starRingEnd ℂ
        (OS.S 1 (ZeroDiagonalSchwartz.ofClassical (onePointToFin1CLM d χ))) := by
          exact schwinger_onePointToFin1_osConj_eq_star_local (d := d) OS χ

/-- On the actual two-point translated-right cluster lane, the right one-point
factor comparison is now automatic. The only remaining mismatch is the left
one-point `osConj` comparison. -/
theorem bvt_F_clusterCanonicalEventually_translate_of_twoPointLeftFactorComparison
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ g : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hχ_compact : HasCompactSupport (χ : SpacetimeDim d → ℂ))
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (hleft :
      bvt_W OS lgc 1
          (SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d χ : SchwartzNPoint d 1))
        =
      OS.S 1 (ZeroDiagonalSchwartz.ofClassical (onePointToFin1CLM d χ))) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, R > 0 ∧
      ∀ a : Fin d → ℝ, (∑ i : Fin d, (a i)^2) > R^2 →
        ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
          ‖(∫ y : NPointDomain d 2,
              bvt_F OS lgc 2
                  (xiShift ⟨1, by omega⟩ 0
                    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                (χ (y 0) * (SCV.translateSchwartz (-Fin.cons 0 a) g) (y 1))) -
            bvt_W OS lgc 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d χ : SchwartzNPoint d 1)) *
              bvt_W OS lgc 1 (onePointToFin1CLM d g)‖ < ε := by
  let χ0 : SchwartzNPoint d 1 :=
    SchwartzNPoint.osConj (d := d) (n := 1)
      (onePointToFin1CLM d χ : SchwartzNPoint d 1)
  let g0 : SchwartzNPoint d 1 := onePointToFin1CLM d g
  have hcluster :=
    bvt_F_clusterCanonicalEventually_translate_of_singleSplitFactorComparison
      (d := d) (OS := OS) (lgc := lgc) 1 1 (by omega)
      χ0 hχ_pos
      (osConj_onePointToFin1_hasCompactSupport_local (d := d) χ hχ_compact)
      g0 hg_pos
      (onePointToFin1_hasCompactSupport_local (d := d) g hg_compact)
      (by simpa [χ0, SchwartzNPoint.osConj_apply, onePointToFin1CLM_apply,
            timeReflectionN, timeReflection_timeReflection] using hleft)
      (bvt_W_onePointToFin1_eq_schwinger (d := d) OS lgc g)
  intro ε hε
  obtain ⟨R, hR, hclusterR⟩ := hcluster ε hε
  refine ⟨R, hR, ?_⟩
  intro a ha_large
  filter_upwards [hclusterR a ha_large] with t ht
  have hIntEq :
      ∫ y : NPointDomain d 2,
          bvt_F OS lgc 2
              (xiShift ⟨1, by omega⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            ((χ0.osConjTensorProduct
              (translateSchwartzNPoint (d := d) (Fin.cons 0 a) g0)) y)
        =
      ∫ y : NPointDomain d 2,
          bvt_F OS lgc 2
              (xiShift ⟨1, by omega⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (χ (y 0) * (SCV.translateSchwartz (-Fin.cons 0 a) g) (y 1)) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with y
    rw [onePoint_osConjTensorProduct_translate_spatial_apply_local
      (d := d) χ g a y]
  rw [← hIntEq]
  simpa [χ0, g0] using ht

/-- On the actual two-point translated-right cluster lane, it is enough that
the ordinary one-point Schwinger value of the left factor is real. The mixed
BV-vs-Schwinger comparison for the `osConj` left factor is already paid by
`bvt_W_onePointToFin1_osConj_eq_star_schwinger`. -/
theorem bvt_F_clusterCanonicalEventually_translate_of_twoPointLeftFactorReality
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ g : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hχ_compact : HasCompactSupport (χ : SpacetimeDim d → ℂ))
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (hχ_real :
      starRingEnd ℂ
        (OS.S 1 (ZeroDiagonalSchwartz.ofClassical (onePointToFin1CLM d χ))) =
          OS.S 1 (ZeroDiagonalSchwartz.ofClassical (onePointToFin1CLM d χ))) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, R > 0 ∧
      ∀ a : Fin d → ℝ, (∑ i : Fin d, (a i)^2) > R^2 →
        ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
          ‖(∫ y : NPointDomain d 2,
              bvt_F OS lgc 2
                  (xiShift ⟨1, by omega⟩ 0
                    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                (χ (y 0) * (SCV.translateSchwartz (-Fin.cons 0 a) g) (y 1))) -
            bvt_W OS lgc 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d χ : SchwartzNPoint d 1)) *
              bvt_W OS lgc 1 (onePointToFin1CLM d g)‖ < ε := by
  have hleft :
      bvt_W OS lgc 1
          (SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d χ : SchwartzNPoint d 1))
        =
      OS.S 1 (ZeroDiagonalSchwartz.ofClassical (onePointToFin1CLM d χ)) := by
    calc
      bvt_W OS lgc 1
          (SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d χ : SchwartzNPoint d 1))
        =
      starRingEnd ℂ
        (OS.S 1 (ZeroDiagonalSchwartz.ofClassical (onePointToFin1CLM d χ))) := by
            exact bvt_W_onePointToFin1_osConj_eq_star_schwinger (d := d) OS lgc χ
      _ = OS.S 1 (ZeroDiagonalSchwartz.ofClassical (onePointToFin1CLM d χ)) := hχ_real
  exact bvt_F_clusterCanonicalEventually_translate_of_twoPointLeftFactorComparison
    (d := d) (OS := OS) (lgc := lgc) χ g hχ_pos hg_pos hχ_compact hg_compact hleft

/-- For a real-valued time-reflection-invariant one-point test, the mixed
`osConj` one-point BV factor already agrees with the ordinary one-point
Schwinger value. This makes the two-point translated cluster lane theorem-based
on the natural self-adjoint one-point shell. -/
theorem bvt_W_onePointToFin1_osConj_eq_schwinger_of_real_reflectionInvariant
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ : SchwartzSpacetime d)
    (hχ_real : ∀ x, (χ x).im = 0)
    (hχ_reflect : ∀ x, χ (timeReflection d x) = χ x) :
    bvt_W OS lgc 1
        (SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d χ : SchwartzNPoint d 1))
      =
    OS.S 1 (ZeroDiagonalSchwartz.ofClassical (onePointToFin1CLM d χ)) := by
  have hosConj_eq :
      SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d χ : SchwartzNPoint d 1)
        =
      (onePointToFin1CLM d χ : SchwartzNPoint d 1) := by
    ext x
    have him : (χ (timeReflection d (x 0))).im = 0 :=
      hχ_real (timeReflection d (x 0))
    have hstar :
        starRingEnd ℂ (χ (timeReflection d (x 0))) =
          χ (timeReflection d (x 0)) := by
      apply Complex.ext <;> simp [him]
    calc
      (SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d χ : SchwartzNPoint d 1)) x
        = starRingEnd ℂ (χ (timeReflection d (x 0))) := by
            simp [SchwartzNPoint.osConj_apply, onePointToFin1CLM_apply, timeReflectionN]
      _ = χ (timeReflection d (x 0)) := hstar
      _ = χ (x 0) := hχ_reflect (x 0)
      _ = (onePointToFin1CLM d χ : SchwartzNPoint d 1) x := by
            simp [onePointToFin1CLM_apply]
  simpa [hosConj_eq] using bvt_W_onePointToFin1_eq_schwinger (d := d) OS lgc χ

/-- On the actual two-point translated-right cluster lane, it is enough that
the left one-point cutoff is self-adjoint in the explicit test-function sense:
real-valued and invariant under Euclidean time reflection. This removes the
remaining abstract scalar reality hypothesis from the natural reflected-real
one-point shell. -/
theorem bvt_F_clusterCanonicalEventually_translate_of_twoPointLeftFactorSelfAdjoint
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (χ g : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hχ_compact : HasCompactSupport (χ : SpacetimeDim d → ℂ))
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (hχ_real : ∀ x, (χ x).im = 0)
    (hχ_reflect : ∀ x, χ (timeReflection d x) = χ x) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, R > 0 ∧
      ∀ a : Fin d → ℝ, (∑ i : Fin d, (a i)^2) > R^2 →
        ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
          ‖(∫ y : NPointDomain d 2,
              bvt_F OS lgc 2
                  (xiShift ⟨1, by omega⟩ 0
                    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                (χ (y 0) * (SCV.translateSchwartz (-Fin.cons 0 a) g) (y 1))) -
            bvt_W OS lgc 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d χ : SchwartzNPoint d 1)) *
              bvt_W OS lgc 1 (onePointToFin1CLM d g)‖ < ε := by
  have hleft :
      bvt_W OS lgc 1
          (SchwartzNPoint.osConj (d := d) (n := 1)
            (onePointToFin1CLM d χ : SchwartzNPoint d 1))
        =
      OS.S 1 (ZeroDiagonalSchwartz.ofClassical (onePointToFin1CLM d χ)) := by
    exact bvt_W_onePointToFin1_osConj_eq_schwinger_of_real_reflectionInvariant
      (d := d) OS lgc χ hχ_real hχ_reflect
  exact bvt_F_clusterCanonicalEventually_translate_of_twoPointLeftFactorComparison
    (d := d) (OS := OS) (lgc := lgc) χ g hχ_pos hg_pos hχ_compact hg_compact hleft

private theorem boundary_ray_translation_invariant_of_F_invariant
    (n : ℕ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_inv : ∀ (a : SpacetimeDim d) (x : NPointDomain d n)
        (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ), 0 < ε →
      F_n (fun k μ => ↑(x k μ - a μ) + ε * ↑(η k μ) * Complex.I) =
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I))
    (a : SpacetimeDim d) (f : SchwartzNPoint d n)
    (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∫ x : NPointDomain d n,
      F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
        f (fun i => x i + a) =
    ∫ x : NPointDomain d n,
      F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f x := by
  let aN : NPointDomain d n := fun _ => a
  let gfun : NPointDomain d n → ℂ := fun x =>
    F_n (fun k μ => ↑(x k μ - a μ) + ε * ↑(η k μ) * Complex.I) * f x
  have hga :
      (fun x : NPointDomain d n => gfun (x + aN)) =
        fun x : NPointDomain d n =>
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f (fun i => x i + a) := by
    ext x
    calc
      gfun (x + aN)
          = F_n (fun k μ => ↑((x + aN) k μ - a μ) + ε * ↑(η k μ) * Complex.I) * f (x + aN) := by
              rfl
      _ = F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f (x + aN) := by
            congr
            ext k μ
            simp [aN, Pi.add_apply, add_sub_cancel_right]
      _ = F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f (fun i => x i + a) := by
            rfl
  rw [← hga, MeasureTheory.integral_add_right_eq_self gfun aN]
  simp only [gfun]
  congr 1
  ext x
  exact congrArg (fun z : ℂ => z * f x) (hF_inv a x η ε hε)

private theorem bv_translation_invariance_transfer_of_F_invariant
    (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_inv : ∀ (a : SpacetimeDim d) (x : NPointDomain d n)
        (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ), 0 < ε →
      F_n (fun k μ => ↑(x k μ - a μ) + ε * ↑(η k μ) * Complex.I) =
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) :
    ∀ (a : SpacetimeDim d) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => x i + a)) →
      W_n f = W_n g := by
  intro a f g hfg
  obtain ⟨η, hη_abs⟩ := forwardConeAbs_nonempty d n
  have hη : InForwardCone d n η :=
    (inForwardCone_iff_mem_forwardConeAbs η).mpr hη_abs
  have hf := hBV f η hη
  have hg := hBV g η hη
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hrewrite :
        (∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)) =
          ∫ x : NPointDomain d n,
            F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
              f (fun i => x i + a) := by
      congr 1
      ext x
      have hxg : g x = f (fun i => x i + a) := by
        simpa using hfg x
      rw [hxg]
    calc
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)) ε
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (fun i => x i + a) := hrewrite
      _ =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) :=
        boundary_ray_translation_invariant_of_F_invariant (d := d) n F_n hF_inv a f η ε hε
  have hg_as_f : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hg_as_f

theorem bv_translation_invariance_transfer (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_inv :
      ∀ (a : SpacetimeDim d) (x : NPointDomain d n)
        (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ), 0 < ε →
        F_n (fun k μ => ↑(x k μ - a μ) + ε * ↑(η k μ) * Complex.I) =
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) :
    ∀ (a : SpacetimeDim d) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => x i + a)) →
      W_n f = W_n g := by
  exact bv_translation_invariance_transfer_of_F_invariant (d := d) n W_n F_n hBV hF_inv

theorem integral_lorentz_eq_self_full {n : ℕ}
    (Λ : FullLorentzGroup d)
    (h : NPointDomain d n → ℂ) :
    ∫ x : NPointDomain d n, h (fun i => Matrix.mulVec Λ.val (x i)) =
    ∫ x : NPointDomain d n, h x := by
  have habs : |Λ.val.det| = 1 := by
    rcases FullLorentzGroup.det_eq_pm_one Λ with hdet | hdet
    · rw [hdet]
      simp
    · rw [hdet]
      simp
  have hdet_ne : Λ.val.det ≠ 0 := by
    intro hzero
    rw [hzero] at habs
    norm_num at habs
  have hΛ_mul_inv : Λ.val * Λ⁻¹.val = 1 := by
    have h1 := FullLorentzGroup.ext_iff.mp (mul_inv_cancel Λ)
    rw [show (Λ * Λ⁻¹).val = Λ.val * Λ⁻¹.val from rfl] at h1
    rw [show (1 : FullLorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
    exact h1
  have hΛinv_mul : Λ⁻¹.val * Λ.val = 1 := by
    have h1 := FullLorentzGroup.ext_iff.mp (inv_mul_cancel Λ)
    rw [show (Λ⁻¹ * Λ).val = Λ⁻¹.val * Λ.val from rfl] at h1
    rw [show (1 : FullLorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
    exact h1
  have hmv : (fun v => Λ.val.mulVec v) = Matrix.toLin' Λ.val := by
    ext v
    simp [Matrix.toLin'_apply]
  have hcont_Λ : Continuous (Matrix.toLin' Λ.val) :=
    LinearMap.continuous_of_finiteDimensional _
  have hcont_Λinv : Continuous (Matrix.toLin' Λ⁻¹.val) :=
    LinearMap.continuous_of_finiteDimensional _
  have hmp_factor : MeasureTheory.MeasurePreserving
      (fun v : Fin (d + 1) → ℝ => Λ.val.mulVec v)
      MeasureTheory.volume MeasureTheory.volume := by
    rw [hmv]
    constructor
    · exact hcont_Λ.measurable
    · rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hdet_ne]
      simp [habs]
  let e : (Fin n → Fin (d + 1) → ℝ) ≃ᵐ (Fin n → Fin (d + 1) → ℝ) :=
    { toEquiv := {
        toFun := fun a i => Λ.val.mulVec (a i)
        invFun := fun a i => Λ⁻¹.val.mulVec (a i)
        left_inv := fun a => by
          ext i j
          simp [Matrix.mulVec_mulVec, hΛinv_mul]
        right_inv := fun a => by
          ext i j
          simp [Matrix.mulVec_mulVec, hΛ_mul_inv] }
      measurable_toFun :=
        measurable_pi_lambda _ fun i => hcont_Λ.measurable.comp (measurable_pi_apply i)
      measurable_invFun :=
        measurable_pi_lambda _ fun i => hcont_Λinv.measurable.comp (measurable_pi_apply i) }
  have hmp : MeasureTheory.MeasurePreserving e MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.volume_preserving_pi (fun (_ : Fin n) => hmp_factor)
  exact hmp.integral_comp' h

private noncomputable def lorentzInvCLEquivFull
    (Λ : LorentzGroup d) :
    (Fin (d + 1) → ℝ) ≃L[ℝ] (Fin (d + 1) → ℝ) := by
  have hΛinv_mul : Λ⁻¹.val * Λ.val = 1 := by
    have h1 := LorentzGroup.ext_iff.mp (inv_mul_cancel Λ)
    rw [show (Λ⁻¹ * Λ).val = Λ⁻¹.val * Λ.val from rfl] at h1
    rw [show (1 : LorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
    exact h1
  have hΛinv_mul_full : Λ⁻¹.val * Λ.toFull.val = 1 := by
    simpa using hΛinv_mul
  have hΛ_mul_inv : Λ.val * Λ⁻¹.val = 1 := by
    have h1 := LorentzGroup.ext_iff.mp (mul_inv_cancel Λ)
    rw [show (Λ * Λ⁻¹).val = Λ.val * Λ⁻¹.val from rfl] at h1
    rw [show (1 : LorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
    exact h1
  exact
    { toLinearEquiv :=
        { toLinearMap := Matrix.toLin' (Λ⁻¹).val
          invFun := Matrix.toLin' Λ.val
          left_inv := fun v => by
            show (Matrix.toLin' Λ.val) ((Matrix.toLin' (Λ⁻¹).val) v) = v
            rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hΛ_mul_inv, Matrix.toLin'_one]
            simp
          right_inv := fun v => by
            show (Matrix.toLin' (Λ⁻¹).val) ((Matrix.toLin' Λ.val) v) = v
            rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hΛinv_mul, Matrix.toLin'_one]
            simp }
      continuous_toFun := LinearMap.continuous_of_finiteDimensional _
      continuous_invFun := LinearMap.continuous_of_finiteDimensional _ }

private noncomputable def lorentzCompSchwartzFull {n : ℕ}
    (Λ : LorentzGroup d) (f : SchwartzNPoint d n) : SchwartzNPoint d n :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (ContinuousLinearEquiv.piCongrRight
      (fun (_ : Fin n) => lorentzInvCLEquivFull (d := d) Λ)) f

private theorem lorentzCompSchwartzFull_apply {n : ℕ}
    (Λ : LorentzGroup d) (f : SchwartzNPoint d n) (x : NPointDomain d n) :
    (lorentzCompSchwartzFull (d := d) Λ f).toFun x =
      f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := by
  simp only [lorentzCompSchwartzFull, SchwartzMap.compCLMOfContinuousLinearEquiv,
    ContinuousLinearEquiv.piCongrRight, lorentzInvCLEquivFull]
  rfl

private theorem boundary_ray_lorentz_invariant_of_F_invariant
    (n : ℕ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_lorentz :
      ∀ (Λ : LorentzGroup d) (x : NPointDomain d n) (ε : ℝ), 0 < ε →
        F_n (fun k μ =>
          ↑((Matrix.mulVec Λ.val (x k)) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) =
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I))
    (Λ : LorentzGroup d)
    (f : SchwartzNPoint d n) (ε : ℝ) (hε : 0 < ε) :
    ∫ x : NPointDomain d n,
      F_n (fun k μ =>
        ↑(x k μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
        f (fun i => Matrix.mulVec Λ⁻¹.val (x i))
      =
    ∫ x : NPointDomain d n,
      F_n (fun k μ =>
        ↑(x k μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * f x := by
  have hΛinv_mul : Λ⁻¹.val * Λ.val = 1 := by
    have h1 := LorentzGroup.ext_iff.mp (inv_mul_cancel Λ)
    rw [show (Λ⁻¹ * Λ).val = Λ⁻¹.val * Λ.val from rfl] at h1
    rw [show (1 : LorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
    exact h1
  have hΛinv_mul_full : Λ⁻¹.val * Λ.toFull.val = 1 := by
    simpa using hΛinv_mul
  have hcov :
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑((Matrix.mulVec Λ.val (x k)) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
          f x
      =
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
          f (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := by
    simpa [Matrix.mulVec_mulVec, hΛinv_mul_full] using
      (integral_lorentz_eq_self_full (d := d) (n := n) Λ
        (fun y : NPointDomain d n =>
          F_n (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (y i))))
  have hrewrite :
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑((Matrix.mulVec Λ.val (x k)) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
          f x
      =
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * f x := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [Filter.Eventually.of_forall fun x => hF_lorentz Λ x ε hε] with x hx
    simp [hx]
  calc
    ∫ x : NPointDomain d n,
      F_n (fun k μ =>
        ↑(x k μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
        f (fun i => Matrix.mulVec Λ⁻¹.val (x i))
        =
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑((Matrix.mulVec Λ.val (x k)) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
          f x := hcov.symm
    _ =
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * f x := hrewrite

theorem bv_lorentz_covariance_transfer (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_lorentz :
      ∀ (Λ : LorentzGroup d) (x : NPointDomain d n) (ε : ℝ), 0 < ε →
        F_n (fun k μ =>
          ↑((Matrix.mulVec Λ.val (x k)) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) =
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)) :
    ∀ (Λ : LorentzGroup d) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
      W_n f = W_n g := by
  intro Λ f g hfg
  let η := canonicalForwardConeDirection (d := d) n
  have hη : InForwardCone d n η := canonicalForwardConeDirection_mem (d := d) n
  have hf := hBV f η hη
  have hg := hBV g η hη
  have hcanonical_pairing :
      ∀ (Λ : LorentzGroup d) (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
        (∀ x, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x) := by
    intro Λ f g ε hε hfg
    have hrewrite :
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
        =
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := by
      congr 1
      ext x
      exact congrArg
        (fun z : ℂ =>
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * z)
        (hfg x)
    calc
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := hrewrite
      _ =
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x) := by
          simpa using
            boundary_ray_lorentz_invariant_of_F_invariant (d := d) n F_n
              hF_lorentz
              Λ f ε hε
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa [η] using hcanonical_pairing Λ f g ε hε hfg
  have hg_as_f : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hg_as_f

theorem bv_lorentz_covariance_transfer_of_fixed_tube_covariance
    (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (Λ : LorentzGroup d)
    (hF_lorentz_fixed :
      ∀ (x : NPointDomain d n) (ε : ℝ), 0 < ε →
        F_n (fun k μ =>
          ↑((Matrix.mulVec Λ.val (x k)) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) =
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)) :
    ∀ (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
      W_n f = W_n g := by
  intro f g hfg
  let η := canonicalForwardConeDirection (d := d) n
  have hη : InForwardCone d n η := canonicalForwardConeDirection_mem (d := d) n
  have hf := hBV f η hη
  have hg := hBV g η hη
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hrewrite :
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
        =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := by
      congr 1
      ext x
      exact congrArg
        (fun z : ℂ =>
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * z)
        (hfg x)
    calc
      ∫ x : NPointDomain d n,
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := hrewrite
      _ =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) := by
          have hΛinv_mul : Λ⁻¹.val * Λ.val = 1 := by
            have h1 := LorentzGroup.ext_iff.mp (inv_mul_cancel Λ)
            rw [show (Λ⁻¹ * Λ).val = Λ⁻¹.val * Λ.val from rfl] at h1
            rw [show (1 : LorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
            exact h1
          have hΛinv_mul_full : Λ⁻¹.val * Λ.toFull.val = 1 := by
            simpa using hΛinv_mul
          have hcov :
              ∫ x : NPointDomain d n,
                F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
                  f (fun i => Matrix.mulVec Λ⁻¹.val (x i))
              =
              ∫ x : NPointDomain d n,
                F_n (fun k μ =>
                  ↑((Matrix.mulVec Λ.val (x k)) μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
                  (f x) := by
            symm
            simpa [η, Matrix.mulVec_mulVec, hΛinv_mul_full] using
              (integral_lorentz_eq_self_full (d := d) (n := n) Λ
                (fun y : NPointDomain d n =>
                  F_n (fun k μ => ↑(y k μ) + ε * ↑(η k μ) * Complex.I) *
                    f (fun i => Matrix.mulVec Λ⁻¹.val (y i))))
          have htube :
              ∫ x : NPointDomain d n,
                F_n (fun k μ =>
                  ↑((Matrix.mulVec Λ.val (x k)) μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
                  (f x)
              =
              ∫ x : NPointDomain d n,
                F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [Filter.Eventually.of_forall fun x => hF_lorentz_fixed x ε hε] with x hx
            simp [η, hx]
          exact hcov.trans htube
  have hg_as_f : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hg_as_f

private theorem bv_lorentz_covariance_transfer_orthochronous
    (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_lorentz :
      ∀ (Λ : LorentzGroup d), LorentzGroup.IsOrthochronous Λ →
        ∀ (x : NPointDomain d n) (ε : ℝ), 0 < ε →
          F_n (fun k μ =>
            ↑((Matrix.mulVec Λ.val (x k)) μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) =
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)) :
    ∀ (Λ : LorentzGroup d), LorentzGroup.IsOrthochronous Λ →
      ∀ (f g : SchwartzNPoint d n),
        (∀ x, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
        W_n f = W_n g := by
  intro Λ hΛ f g hfg
  have hF_fixed :
      ∀ (x : NPointDomain d n) (ε : ℝ), 0 < ε →
        F_n (fun k μ =>
          ↑((Matrix.mulVec Λ.val (x k)) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) =
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) :=
    hF_lorentz Λ hΛ
  let η := canonicalForwardConeDirection (d := d) n
  have hη : InForwardCone d n η := canonicalForwardConeDirection_mem (d := d) n
  have hf := hBV f η hη
  have hg := hBV g η hη
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hrewrite :
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
        =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := by
      congr 1
      ext x
      exact congrArg
        (fun z : ℂ =>
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * z)
        (hfg x)
    calc
      ∫ x : NPointDomain d n,
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := hrewrite
      _ =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) := by
          have hΛinv_mul : Λ⁻¹.val * Λ.val = 1 := by
            have h1 := LorentzGroup.ext_iff.mp (inv_mul_cancel Λ)
            rw [show (Λ⁻¹ * Λ).val = Λ⁻¹.val * Λ.val from rfl] at h1
            rw [show (1 : LorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
            exact h1
          have hΛinv_mul_full : Λ⁻¹.val * Λ.toFull.val = 1 := by
            simpa using hΛinv_mul
          have hcov :
              ∫ x : NPointDomain d n,
                F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
                  f (fun i => Matrix.mulVec Λ⁻¹.val (x i))
              =
              ∫ x : NPointDomain d n,
                F_n (fun k μ =>
                  ↑((Matrix.mulVec Λ.val (x k)) μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
                  (f x) := by
            symm
            simpa [η, Matrix.mulVec_mulVec, hΛinv_mul_full] using
              (integral_lorentz_eq_self_full (d := d) (n := n) Λ
                (fun y : NPointDomain d n =>
                  F_n (fun k μ => ↑(y k μ) + ε * ↑(η k μ) * Complex.I) *
                    f (fun i => Matrix.mulVec Λ⁻¹.val (y i))))
          have htube :
              ∫ x : NPointDomain d n,
                F_n (fun k μ =>
                  ↑((Matrix.mulVec Λ.val (x k)) μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
                  (f x)
              =
              ∫ x : NPointDomain d n,
                F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [Filter.Eventually.of_forall fun x => hF_fixed x ε hε] with x hx
            simp [η, hx]
          exact hcov.trans htube
  have hg_as_f : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hg_as_f

private theorem bv_lorentz_covariance_transfer_restricted_of_tube_covariance
    (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_lorentz :
      ∀ (Λ : LorentzGroup d)
        (x : NPointDomain d n) (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ), 0 < ε →
        F_n (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
          (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) =
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) :
    ∀ (Λ : LorentzGroup d) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
      W_n f = W_n g := by
  intro Λ f g hfg
  let η := canonicalForwardConeDirection (d := d) n
  let Λη : Fin n → Fin (d + 1) → ℝ := fun k μ => ∑ ν, Λ.val μ ν * η k ν
  have hη : InForwardCone d n η := canonicalForwardConeDirection_mem (d := d) n
  have hΛη : InForwardCone d n Λη := by
    intro k
    let diffη : Fin (d + 1) → ℝ := fun μ => η k μ -
      (if h : k.val = 0 then (0 : Fin (d + 1) → ℝ) else η ⟨k.val - 1, by omega⟩) μ
    have hk : InOpenForwardCone d diffη := hη k
    have hΛdiff := restricted_preserves_forward_cone Λ diffη hk
    convert hΛdiff using 1
    ext μ
    simp only [Λη, diffη]
    split_ifs with hk0
    · simp [sub_zero]
    · rw [← Finset.sum_sub_distrib]
      congr 1
      ext ν
      ring
  have hf := hBV f η hη
  have hg := hBV g Λη hΛη
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) * (g x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hrewrite :
        (∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) * (g x)) =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := by
      congr 1
      ext x
      exact congrArg
        (fun z : ℂ =>
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) * z)
        (hfg x)
    have hlin :
        ∀ x : NPointDomain d n,
          (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
            (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) =
          (fun k μ =>
            ↑((fun i => Matrix.mulVec Λ.val (x i)) k μ) +
              ε * ↑(Λη k μ) * Complex.I) := by
      intro x
      funext k μ
      simp only [Λη, Matrix.mulVec]
      push_cast
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1
      · simp only [dotProduct]
        push_cast
        rfl
      · conv_lhs =>
          arg 2
          ext ν
          rw [show (↑(Λ.val μ ν) : ℂ) * (↑ε * ↑(η k ν) * Complex.I) =
              ↑ε * (↑(Λ.val μ ν) * ↑(η k ν)) * Complex.I from by ring]
        rw [← Finset.sum_mul, ← Finset.mul_sum]
    have hcov :
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (x i))
        =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
            (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) * (f x) := by
      symm
      simpa [hlin, Matrix.mulVec_mulVec, lorentz_inv_mul_eq_one (d := d) Λ] using
        (integral_lorentz_eq_self (d := d) (n := n) Λ
          (fun y : NPointDomain d n =>
            F_n (fun k μ => ↑(y k μ) + ε * ↑(Λη k μ) * Complex.I) *
              f (fun i => Matrix.mulVec Λ⁻¹.val (y i))))
    have htube :
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
            (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) * (f x)
        =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [Filter.Eventually.of_forall fun x => hF_lorentz Λ x η ε hε] with x hx
      simp [hx]
    exact hrewrite.trans (hcov.trans htube)
  have hf_as_g : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hf_as_g

theorem bv_lorentz_covariance_transfer_orthochronous_of_tube_covariance
    (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_lorentz :
      ∀ (Λ : LorentzGroup d),
        LorentzGroup.IsOrthochronous Λ →
        ∀ (x : NPointDomain d n) (ε : ℝ), 0 < ε →
          F_n (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
            (↑(x k ν) + ε *
              ↑(canonicalForwardConeDirection (d := d) n k ν) * Complex.I)) =
          F_n (fun k μ => ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)) :
    ∀ (Λ : LorentzGroup d), LorentzGroup.IsOrthochronous Λ →
      ∀ (f g : SchwartzNPoint d n),
        (∀ x, g.toFun x = f.toFun (fun i => Matrix.mulVec Λ⁻¹.val (x i))) →
        W_n f = W_n g := by
  intro Λ hΛ_ortho f g hfg
  let η := canonicalForwardConeDirection (d := d) n
  let Λη : Fin n → Fin (d + 1) → ℝ := fun k μ => ∑ ν, Λ.val μ ν * η k ν
  have hη : InForwardCone d n η := canonicalForwardConeDirection_mem (d := d) n
  have hΛη : InForwardCone d n Λη := by
    intro k
    let diffη : Fin (d + 1) → ℝ := fun μ => η k μ -
      (if h : k.val = 0 then (0 : Fin (d + 1) → ℝ) else η ⟨k.val - 1, by omega⟩) μ
    have hk : InOpenForwardCone d diffη := hη k
    have hΛdiff := orthochronous_preserves_forward_cone (d := d) Λ hΛ_ortho diffη hk
    convert hΛdiff using 1
    ext μ
    simp only [Λη, diffη]
    split_ifs with hk0
    · simp [sub_zero]
    · rw [← Finset.sum_sub_distrib]
      congr 1
      ext ν
      ring
  have hf := hBV f η hη
  have hg := hBV g Λη hΛη
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) * (g x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hrewrite :
        (∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) * (g x)) =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (x i)) := by
      congr 1
      ext x
      exact congrArg
        (fun z : ℂ =>
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) * z)
        (hfg x)
    have hlin :
        ∀ x : NPointDomain d n,
          (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
            (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) =
          (fun k μ =>
            ↑((fun i => Matrix.mulVec Λ.val (x i)) k μ) +
              ε * ↑(Λη k μ) * Complex.I) := by
      intro x
      funext k μ
      simp only [Λη, Matrix.mulVec]
      push_cast
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1
      · simp only [dotProduct]
        push_cast
        rfl
      · conv_lhs =>
          arg 2
          ext ν
          rw [show (↑(Λ.val μ ν) : ℂ) * (↑ε * ↑(η k ν) * Complex.I) =
              ↑ε * (↑(Λ.val μ ν) * ↑(η k ν)) * Complex.I from by ring]
        rw [← Finset.sum_mul, ← Finset.mul_sum]
    have hΛinv_mul : Λ⁻¹.val * Λ.val = 1 := by
      have h1 := LorentzGroup.ext_iff.mp (inv_mul_cancel Λ)
      rw [show (Λ⁻¹ * Λ).val = Λ⁻¹.val * Λ.val from rfl] at h1
      rw [show (1 : LorentzGroup d).val = (1 : Matrix _ _ ℝ) from rfl] at h1
      exact h1
    have hΛinv_mul_full : Λ⁻¹.val * Λ.toFull.val = 1 := by
      simpa using hΛinv_mul
    have hcov :
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(Λη k μ) * Complex.I) *
            f (fun i => Matrix.mulVec Λ⁻¹.val (x i))
        =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
            (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) * (f x) := by
      symm
      simpa [hlin, Matrix.mulVec_mulVec, hΛinv_mul_full] using
        (integral_lorentz_eq_self_full (d := d) (n := n) Λ
          (fun y : NPointDomain d n =>
            F_n (fun k μ => ↑(y k μ) + ε * ↑(Λη k μ) * Complex.I) *
              f (fun i => Matrix.mulVec Λ⁻¹.val (y i))))
    have htube :
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ∑ ν, (Λ.val μ ν : ℂ) *
            (↑(x k ν) + ε * ↑(η k ν) * Complex.I)) * (f x)
        =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [Filter.Eventually.of_forall fun x => hF_lorentz Λ hΛ_ortho x ε hε] with x hx
      rw [hx]
    exact hrewrite.trans (hcov.trans htube)
  have hf_as_g : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hf_as_g

private theorem boundary_ray_permutation_invariant_of_F_invariant
    (n : ℕ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_perm : ∀ (σ : Equiv.Perm (Fin n)) (x : NPointDomain d n)
        (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ), 0 < ε →
      F_n (fun k μ => ↑(x (σ k) μ) + ε * ↑(η k μ) * Complex.I) =
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I))
    (σ : Equiv.Perm (Fin n))
    (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∫ x : NPointDomain d n,
      F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
        f (fun i => x (σ i))
      =
    ∫ x : NPointDomain d n,
      F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f x := by
  calc
    ∫ x : NPointDomain d n,
      F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
        f (fun i => x (σ i))
        =
      ∫ x : NPointDomain d n,
        F_n (fun k μ => ↑(x (σ k) μ) + ε * ↑(η k μ) * Complex.I) *
          f (fun i => x (σ i)) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [Filter.Eventually.of_forall fun x => hF_perm σ x η ε hε] with x hx
            simp [hx]
  _ =
      ∫ x : NPointDomain d n,
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f x := by
          simpa using
            (MeasureTheory.volume_measurePreserving_piCongrLeft
              (fun _ : Fin n => Fin (d + 1) → ℝ) σ).symm.integral_comp'
                (fun x : NPointDomain d n =>
                  F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f x)

private theorem bv_local_commutativity_transfer_of_F_invariant
    (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_perm : ∀ (σ : Equiv.Perm (Fin n)) (x : NPointDomain d n)
        (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ), 0 < ε →
      F_n (fun k μ => ↑(x (σ k) μ) + ε * ↑(η k μ) * Complex.I) =
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) :
    ∀ (σ : Equiv.Perm (Fin n)) (f g : SchwartzNPoint d n),
      (∀ x, g.toFun x = f.toFun (fun k => x (σ k))) →
      W_n f = W_n g := by
  intro σ f g hfg
  obtain ⟨η, hη_abs⟩ := forwardConeAbs_nonempty d n
  have hη : InForwardCone d n η :=
    (inForwardCone_iff_mem_forwardConeAbs η).mpr hη_abs
  have hf := hBV f η hη
  have hg := hBV g η hη
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hrewrite :
        (∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)) =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (fun k => x (σ k)) := by
      congr 1
      ext x
      have hxg : g x = f (fun k => x (σ k)) := by
        simpa using hfg x
      rw [hxg]
    calc
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)) ε
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (fun k => x (σ k)) := hrewrite
      _ =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) :=
        boundary_ray_permutation_invariant_of_F_invariant (d := d) n F_n hF_perm σ f η ε hε
  have hg_as_f : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hg_as_f

theorem bv_local_commutativity_transfer (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_swapCanonical :
      ∀ (i j : Fin n) (x : NPointDomain d n) (ε : ℝ), 0 < ε →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j) →
        F_n (fun k μ =>
          ↑(x (Equiv.swap i j k) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)
          =
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)) :
    ∀ (i j : Fin n) (f g : SchwartzNPoint d n),
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      W_n f = W_n g := by
  intro i j f g hsupp hswap
  let η := canonicalForwardConeDirection (d := d) n
  have hη : InForwardCone d n η := canonicalForwardConeDirection_mem (d := d) n
  have hf := hBV f η hη
  have hg := hBV g η hη
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hrewrite :
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (fun k => x (Equiv.swap i j k)) := by
      congr 1
      ext x
      exact congrArg
        (fun z : ℂ =>
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * z)
        (hswap x)
    have hswap_integral :
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (fun k => x (Equiv.swap i j k))
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x (Equiv.swap i j k) μ) + ε * ↑(η k μ) * Complex.I) * (f x) := by
      let e : NPointDomain d n ≃ᵐ NPointDomain d n :=
        MeasurableEquiv.piCongrLeft (fun _ : Fin n => Fin (d + 1) → ℝ) (Equiv.swap i j)
      have hmp :
          MeasureTheory.MeasurePreserving e MeasureTheory.volume MeasureTheory.volume :=
        MeasureTheory.volume_measurePreserving_piCongrLeft
          (fun _ : Fin n => Fin (d + 1) → ℝ) (Equiv.swap i j)
      let h :
          NPointDomain d n → ℂ := fun x =>
            F_n (fun k μ => ↑(x (Equiv.swap i j k) μ) + ε * ↑(η k μ) * Complex.I) * f x
      have hleft :
          ∫ x : NPointDomain d n,
            F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
              f (fun k => x (Equiv.swap i j k))
            =
          ∫ x : NPointDomain d n, h (e.symm x) := by
        congr 1
        ext x
        have he_symm :
            e.symm x = fun k => x (Equiv.swap i j k) := by
          ext k μ
          change
            ((Equiv.piCongrLeft (fun _ : Fin n => Fin (d + 1) → ℝ)
              (Equiv.swap i j)).symm x k) μ
              =
            x (Equiv.swap i j k) μ
          simp
        rw [he_symm]
        simp [h]
      calc
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (fun k => x (Equiv.swap i j k))
            =
          ∫ x : NPointDomain d n, h (e.symm x) := hleft
        _ = ∫ x : NPointDomain d n, h x := hmp.symm.integral_comp' h
        _ =
          ∫ x : NPointDomain d n,
            F_n (fun k μ => ↑(x (Equiv.swap i j k) μ) + ε * ↑(η k μ) * Complex.I) * (f x) := by
              rfl
    have hcanonical :
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x (Equiv.swap i j k) μ) + ε * ↑(η k μ) * Complex.I) * (f x)
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) := by
      refine MeasureTheory.integral_congr_ae <| Filter.Eventually.of_forall ?_
      intro x
      by_cases hx : f x = 0
      · simp [hx]
      · have hsp : MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j) := hsupp x hx
        have hswapx :
            F_n (fun k μ => ↑(x (Equiv.swap i j k) μ) + ε * ↑(η k μ) * Complex.I)
              =
            F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) := by
          simpa [η] using hF_swapCanonical i j x ε hε hsp
        simpa [hx] using congrArg (fun z : ℂ => z * f x) hswapx
    calc
      ∫ x : NPointDomain d n,
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (fun k => x (Equiv.swap i j k)) := hrewrite
      _ =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x (Equiv.swap i j k) μ) + ε * ↑(η k μ) * Complex.I) * (f x) :=
        hswap_integral
      _ =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) := hcanonical
  have hg_as_f : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hg_as_f

theorem bv_local_commutativity_transfer_of_swap_pairing (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_swapCanonical_pairing :
      ∀ (i j : Fin n) (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
        (∀ x, f.toFun x ≠ 0 →
          MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
        (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
        =
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x)) :
    ∀ (i j : Fin n) (f g : SchwartzNPoint d n),
      (∀ x, f.toFun x ≠ 0 →
        MinkowskiSpace.AreSpacelikeSeparated d (x i) (x j)) →
      (∀ x, g.toFun x = f.toFun (fun k => x (Equiv.swap i j k))) →
      W_n f = W_n g := by
  intro i j f g hsupp hswap
  let η := canonicalForwardConeDirection (d := d) n
  have hη : InForwardCone d n η := canonicalForwardConeDirection_mem (d := d) n
  have hf := hBV f η hη
  have hg := hBV g η hη
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa [η] using hF_swapCanonical_pairing i j f g ε hε hsupp hswap
  have hg_as_f : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hg_as_f

theorem boundary_ray_hermitian_pairing_of_F_negCanonical
    (n : ℕ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_perm : ∀ (σ : Equiv.Perm (Fin n)) (z : Fin n → Fin (d + 1) → ℂ),
      F_n (fun j => z (σ j)) = F_n z)
    (hF_trans : ∀ (z : Fin n → Fin (d + 1) → ℂ) (a : Fin (d + 1) → ℂ),
      F_n (fun j => z j + a) = F_n z)
    (hF_neg :
      ∀ (x : NPointDomain d n) (ε : ℝ), 0 < ε →
        starRingEnd ℂ
          (F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)) =
        F_n (fun k μ =>
          ↑(x k μ) -
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)) :
    ∀ (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
      (∀ x : NPointDomain d n,
        g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
        =
      starRingEnd ℂ
        (∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x)) := by
  let η := canonicalForwardConeDirection (d := d) n
  intro f g ε hε hfg
  let Ψfun : NPointDomain d n → NPointDomain d n := fun x i => x (Fin.rev i)
  let Ψ : NPointDomain d n ≃ᵐ NPointDomain d n :=
    { toEquiv :=
        { toFun := Ψfun
          invFun := Ψfun
          left_inv := by
            intro x
            ext i μ
            simp [Ψfun]
          right_inv := by
            intro x
            ext i μ
            simp [Ψfun] }
      measurable_toFun := (reverseNPoint_measurePreserving (d := d) (n := n)).measurable
      measurable_invFun := (reverseNPoint_measurePreserving (d := d) (n := n)).measurable }
  have hreflect :
      ∀ x : NPointDomain d n,
        starRingEnd ℂ
          (F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I))
          =
        F_n (fun k μ => ↑(x (Fin.rev k) μ) + ε * ↑(η k μ) * Complex.I) := by
    intro x
    let a : Fin (d + 1) → ℂ := fun μ =>
      if μ = 0 then (((n : ℝ) + 1) * ε : ℂ) * Complex.I else 0
    let zrev : Fin n → Fin (d + 1) → ℂ := fun k μ =>
      ↑(x k μ) + ε * ↑(η (Fin.rev k) μ) * Complex.I
    have hshift :
        F_n (fun k μ => ↑(x k μ) - ε * ↑(η k μ) * Complex.I) =
          F_n zrev := by
      have hzrev :
          (fun j => (fun k μ =>
            ↑(x k μ) - ε * ↑(η k μ) * Complex.I) j + a) = zrev := by
        funext k
        funext μ
        by_cases hμ : μ = 0
        · subst hμ
          simp [a, zrev, η, canonicalForwardConeDirection, Fin.val_rev]
          ring_nf
        · simp [a, zrev, η, canonicalForwardConeDirection, hμ]
      calc
        F_n (fun k μ => ↑(x k μ) - ε * ↑(η k μ) * Complex.I)
            =
          F_n (fun j => (fun k μ =>
            ↑(x k μ) - ε * ↑(η k μ) * Complex.I) j + a) := by
              symm
              exact hF_trans _ a
        _ = F_n zrev := by rw [hzrev]
    have hperm :
        F_n zrev =
          F_n (fun k μ => ↑(x (Fin.rev k) μ) + ε * ↑(η k μ) * Complex.I) := by
      simpa [zrev] using (hF_perm Fin.revPerm zrev).symm
    calc
      starRingEnd ℂ
          (F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I))
          =
        F_n (fun k μ => ↑(x k μ) - ε * ↑(η k μ) * Complex.I) := hF_neg x ε hε
      _ = F_n zrev := hshift
      _ = F_n (fun k μ => ↑(x (Fin.rev k) μ) + ε * ↑(η k μ) * Complex.I) := hperm
  let h : NPointDomain d n → ℂ := fun x =>
    F_n (fun k μ => ↑((Ψfun x) k μ) + ε * ↑(η k μ) * Complex.I) * starRingEnd ℂ (f x)
  have hrewrite :
      ∫ x : NPointDomain d n,
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
        =
      ∫ x : NPointDomain d n, h x := by
    calc
      ∫ x : NPointDomain d n,
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
          =
        ∫ x : NPointDomain d n, h (Ψ x) := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [Filter.Eventually.of_forall hfg] with x _hxg
          have hxg : g x = starRingEnd ℂ (f (fun i => x (Fin.rev i))) := by
            simpa using hfg x
          rw [hxg]
          simp [h, Ψ, Ψfun]
      _ = ∫ x : NPointDomain d n, h x := by
        simpa [h, Ψ, Ψfun] using
          ((reverseNPoint_measurePreserving (d := d) (n := n)).integral_comp'
            (f := Ψ) (g := h))
  calc
    ∫ x : NPointDomain d n,
      F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
        =
      ∫ x : NPointDomain d n,
        starRingEnd ℂ
          (F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f x) := by
            rw [hrewrite]
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [Filter.Eventually.of_forall hreflect] with x hx
            have hx' :
                F_n (fun k μ => ↑(Ψfun x k μ) + ε * ↑(η k μ) * Complex.I) =
                  starRingEnd ℂ (F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) := by
              simpa [Ψfun] using hx.symm
            calc
              h x =
                starRingEnd ℂ (F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) *
                  starRingEnd ℂ (f x) := by
                    simp [h, Ψfun, hx']
              _ =
                starRingEnd ℂ
                  ((F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) * f x) := by
                    simp [map_mul, mul_comm]
    _ =
      starRingEnd ℂ
        (∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
            rw [← _root_.integral_conj]

private theorem bv_hermiticity_transfer_of_F_reflect
    (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_reflect : ∀ (x : NPointDomain d n) (η : Fin n → Fin (d + 1) → ℝ) (ε : ℝ),
      0 < ε →
      starRingEnd ℂ (F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I)) =
        F_n (fun k μ => ↑(x (Fin.rev k) μ) + ε * ↑(η k μ) * Complex.I)) :
    ∀ (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n,
        g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
      W_n g = starRingEnd ℂ (W_n f) := by
  intro f g hfg
  obtain ⟨η, hη_abs⟩ := forwardConeAbs_nonempty d n
  have hη : InForwardCone d n η :=
    (inForwardCone_iff_mem_forwardConeAbs η).mpr hη_abs
  have hf := hBV f η hη
  have hg := hBV g η hη
  let Ψfun : NPointDomain d n → NPointDomain d n := fun x i => x (Fin.rev i)
  have hΨ_invol : Function.Involutive Ψfun := by
    intro x
    ext i μ
    simp [Ψfun]
  let Ψ : NPointDomain d n ≃ᵐ NPointDomain d n :=
    { toEquiv :=
        { toFun := Ψfun
          invFun := Ψfun
          left_inv := hΨ_invol
          right_inv := hΨ_invol }
      measurable_toFun := (reverseNPoint_measurePreserving (d := d) (n := n)).measurable
      measurable_invFun := (reverseNPoint_measurePreserving (d := d) (n := n)).measurable }
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        starRingEnd ℂ
          (∫ x : NPointDomain d n,
            F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hrewrite :
        (∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)) =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            starRingEnd ℂ (f (Ψ x)) := by
      congr 1
      ext x
      have hxg : g x = starRingEnd ℂ (f (Ψ x)) := by
        simpa [Ψ, Ψfun] using hfg x
      rw [hxg]
    have hpattern :
        starRingEnd ℂ
          (∫ x : NPointDomain d n,
            F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) =
          ∫ x : NPointDomain d n,
            F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
              starRingEnd ℂ (f (Ψ x)) := by
      simpa [Ψ, Ψfun] using
          (SCV.bv_reality_pattern (μ := MeasureTheory.volume)
          (F := fun x : NPointDomain d n =>
            F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I))
          (f := f) (Ψ := Ψ)
          (by simpa [Ψ, Ψfun] using reverseNPoint_measurePreserving (d := d) (n := n))
          (fun x => by simpa [Ψ] using hΨ_invol x)
          (Filter.Eventually.of_forall <| by
            intro x
            simpa [Ψ, Ψfun] using hF_reflect x η ε hε))
    exact hrewrite.trans hpattern.symm
  have hstar :
      Filter.Tendsto
        (fun ε : ℝ =>
          starRingEnd ℂ
            (∫ x : NPointDomain d n,
              F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (starRingEnd ℂ (W_n f))) :=
    (continuous_star.tendsto (W_n f)).comp hf
  have hg_as_star :
      Filter.Tendsto
        (fun ε : ℝ =>
          starRingEnd ℂ
            (∫ x : NPointDomain d n,
              F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  simpa using (tendsto_nhds_unique hstar hg_as_star).symm

theorem bv_timeReversal_transfer
    (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_timeReflect_pairing :
      ∀ (f : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
            f (timeReflectionN d x)
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x)) :
    ∀ (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n, g.toFun x = f.toFun (timeReflectionN d x)) →
      W_n f = W_n g := by
  let η := canonicalForwardConeDirection (d := d) n
  have hη : InForwardCone d n η := canonicalForwardConeDirection_mem (d := d) n
  intro f g hfg
  have hf := hBV f η hη
  have hg := hBV g η hη
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hrewrite :
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
        =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (timeReflectionN d x) := by
      congr 1
      ext x
      exact congrArg
        (fun z : ℂ =>
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * z)
        (hfg x)
    calc
      ∫ x : NPointDomain d n,
        F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x)
          =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) *
            f (timeReflectionN d x) := hrewrite
      _ =
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x) := by
          simpa [η] using hF_timeReflect_pairing f ε hε
  have hg_as_f : Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  exact tendsto_nhds_unique hf hg_as_f

theorem boundary_ray_timeReversal_pairing_of_F_timeReversalCanonical
    (n : ℕ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_timeReversal :
      ∀ (x : NPointDomain d n) (ε : ℝ), 0 < ε →
        F_n (fun k μ =>
          ↑((Matrix.mulVec (LorentzGroup.timeReversal (d := d)).val (x k)) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) =
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I)) :
    ∀ (f : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
          f (fun i => Matrix.mulVec (LorentzGroup.timeReversal (d := d)).val (x i))
      =
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x) := by
  intro f ε hε
  have hTT_mul :
      (LorentzGroup.timeReversal (d := d)).val *
          (LorentzGroup.timeReversal (d := d)).val
        = 1 := by
    change Matrix.diagonal (fun i : Fin (d + 1) => if i = 0 then (-1 : ℝ) else 1) *
        Matrix.diagonal (fun i : Fin (d + 1) => if i = 0 then (-1 : ℝ) else 1) = 1
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hi0 : i = 0 <;> simp [Matrix.diagonal, hi0]
    · simp [Matrix.diagonal, hij]
  have hcov :
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑((Matrix.mulVec (LorentzGroup.timeReversal (d := d)).val (x k)) μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x)
      =
      ∫ x : NPointDomain d n,
        F_n (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
          f (fun i => Matrix.mulVec (LorentzGroup.timeReversal (d := d)).val (x i)) := by
    simpa [Matrix.mulVec_mulVec, hTT_mul] using
      (integral_lorentz_eq_self_full (d := d) (n := n)
        (LorentzGroup.timeReversal (d := d))
        (fun y : NPointDomain d n =>
          F_n (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
            f (fun i => Matrix.mulVec (LorentzGroup.timeReversal (d := d)).val (y i))))
  calc
    ∫ x : NPointDomain d n,
      F_n (fun k μ =>
        ↑(x k μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) *
        f (fun i => Matrix.mulVec (LorentzGroup.timeReversal (d := d)).val (x i))
      =
    ∫ x : NPointDomain d n,
      F_n (fun k μ =>
        ↑((Matrix.mulVec (LorentzGroup.timeReversal (d := d)).val (x k)) μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x) := by
          exact hcov.symm
    _ =
    ∫ x : NPointDomain d n,
      F_n (fun k μ =>
        ↑(x k μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x) := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards
            [Filter.Eventually.of_forall fun x =>
              hF_timeReversal x ε hε] with x hx
          rw [hx]

theorem bv_hermiticity_transfer (n : ℕ)
    (W_n : SchwartzNPoint d n → ℂ)
    (F_n : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hBV : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n f)))
    (hF_reflect_pairing :
      ∀ (f g : SchwartzNPoint d n) (ε : ℝ), 0 < ε →
        (∀ x : NPointDomain d n,
          g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
        ∫ x : NPointDomain d n,
          F_n (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (g x)
          =
        starRingEnd ℂ
          (∫ x : NPointDomain d n,
            F_n (fun k μ =>
              ↑(x k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) n k μ) * Complex.I) * (f x))) :
    ∀ (f g : SchwartzNPoint d n),
      (∀ x : NPointDomain d n,
        g.toFun x = starRingEnd ℂ (f.toFun (fun i => x (Fin.rev i)))) →
      W_n g = starRingEnd ℂ (W_n f) := by
  let η := canonicalForwardConeDirection (d := d) n
  have hη : InForwardCone d n η := canonicalForwardConeDirection_mem (d := d) n
  intro f g hfg
  have hf := hBV f η hη
  have hg := hBV g η hη
  let Ψfun : NPointDomain d n → NPointDomain d n := fun x i => x (Fin.rev i)
  have hΨ_invol : Function.Involutive Ψfun := by
    intro x
    ext i μ
    simp [Ψfun]
  let Ψ : NPointDomain d n ≃ᵐ NPointDomain d n :=
    { toEquiv :=
        { toFun := Ψfun
          invFun := Ψfun
          left_inv := hΨ_invol
          right_inv := hΨ_invol }
      measurable_toFun := (reverseNPoint_measurePreserving (d := d) (n := n)).measurable
      measurable_invFun := (reverseNPoint_measurePreserving (d := d) (n := n)).measurable }
  have hEq :
      (fun ε : ℝ =>
        ∫ x : NPointDomain d n,
          F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (g x))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        starRingEnd ℂ
          (∫ x : NPointDomain d n,
            F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x))) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa [η] using hF_reflect_pairing f g ε hε hfg
  have hstar :
      Filter.Tendsto
        (fun ε : ℝ =>
          starRingEnd ℂ
            (∫ x : NPointDomain d n,
              F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (starRingEnd ℂ (W_n f))) :=
    (continuous_star.tendsto (W_n f)).comp hf
  have hg_as_star :
      Filter.Tendsto
        (fun ε : ℝ =>
          starRingEnd ℂ
            (∫ x : NPointDomain d n,
              F_n (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * (f x)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (W_n g)) :=
    Filter.Tendsto.congr' hEq hg
  simpa using (tendsto_nhds_unique hstar hg_as_star).symm
