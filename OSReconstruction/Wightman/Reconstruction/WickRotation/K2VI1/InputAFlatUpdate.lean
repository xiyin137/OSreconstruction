import OSReconstruction.Wightman.Reconstruction.TwoPointFixedTimeKernelBridge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightman

open scoped Classical NNReal

noncomputable section

open Complex MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

private theorem twoPointCenterDiff_toDiffFlat_wickRotate_local
    (d : ℕ)
    (z : NPointDomain d 2) :
    BHW.toDiffFlat 2 d (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i)) =
      BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i)) := by
  ext p
  obtain ⟨q, rfl⟩ := finProdFinEquiv.surjective p
  rcases q with ⟨i, μ⟩
  fin_cases i
  ·
    simp [BHW.toDiffFlat, BHW.flattenCfg, BHW.diffCoordEquiv_apply,
      twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv, wickRotatePoint]
  ·
    by_cases hμ : μ = 0
    ·
      subst hμ
      simp [BHW.toDiffFlat, BHW.flattenCfg, BHW.diffCoordEquiv_apply,
        twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv, wickRotatePoint]
      ring_nf
    ·
      simp [BHW.toDiffFlat, BHW.flattenCfg, BHW.diffCoordEquiv_apply,
        twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv, wickRotatePoint, hμ]

/-- For positive-support difference tests, the fixed-time shifted Schwinger
shell may be read directly from a common flat-update slice of any Euclidean
continuation witness `G`. -/
theorem schwinger_twoPointDifferenceLift_timeShift_eq_flatUpdate_of_positiveSupport_local
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (χ h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (t : ℝ) (ht : 0 < t) :
    OS.S 2
        (ZeroDiagonalSchwartz.ofClassical
          (twoPointDifferenceLift χ (SCV.translateSchwartz (- timeShiftVec d t) h))) =
      ∫ z : NPointDomain d 2,
        G (Function.update
            (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i)))
            (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1))))
            (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))
              (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) +
              (t : ℂ) * Complex.I)) *
          (χ (z 0) * h (z 1)) := by
  have hshift0 :
      (0 : SpacetimeDim d) ∉ tsupport
        (((SCV.translateSchwartz (- timeShiftVec d t) h : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ)) := by
    refine zero_not_mem_tsupport_translate_of_notMem (d := d) h (- timeShiftVec d t) ?_
    exact neg_timeShiftVec_not_mem_positive_tsupport (d := d) h hh_pos t ht
  have hvanish :
      VanishesToInfiniteOrderOnCoincidence
        (twoPointDifferenceLift χ (SCV.translateSchwartz (- timeShiftVec d t) h)) :=
    twoPointDifferenceLift_vanishes_of_zero_not_mem_tsupport χ
      (SCV.translateSchwartz (- timeShiftVec d t) h) hshift0
  calc
    OS.S 2
        (ZeroDiagonalSchwartz.ofClassical
          (twoPointDifferenceLift χ (SCV.translateSchwartz (- timeShiftVec d t) h)))
      =
        ∫ x : NPointDomain d 2,
          G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) *
            (twoPointDifferenceLift χ (SCV.translateSchwartz (- timeShiftVec d t) h) x) := by
              rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes
                (f := twoPointDifferenceLift χ (SCV.translateSchwartz (- timeShiftVec d t) h))
                hvanish]
              exact hG_euclid _
    _ =
        ∫ z : NPointDomain d 2,
          G (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))) *
            (χ (z 0) * (SCV.translateSchwartz (- timeShiftVec d t) h) (z 1)) := by
              simpa [twoPointCenterDiff_toDiffFlat_wickRotate_local] using
                (integral_mul_twoPointDifferenceLift_eq_centerDiff
                  (d := d)
                  (Ψ := fun x : NPointDomain d 2 =>
                    G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))))
                  χ (SCV.translateSchwartz (- timeShiftVec d t) h))
    _ =
        ∫ z : NPointDomain d 2,
          G (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))) *
            (((SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) t (onePointToFin1CLM d h))) z) := by
              refine integral_congr_ae ?_
              filter_upwards with z
              rw [onePoint_osConjTensorProduct_timeShift_apply (d := d) χ h t z]
    _ =
        ∫ z : NPointDomain d 2,
          G (BHW.flattenCfg 2 d
              (xiShift ⟨1, by omega⟩ 0
                (fun i => wickRotatePoint (z i)) ((t : ℂ) * Complex.I))) *
            (((SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
                (onePointToFin1CLM d h : SchwartzNPoint d 1)) z) := by
              exact
                (simpleTensor_timeShift_integral_eq_xiShift (d := d) (n := 1) (m := 1)
                  (hm := by omega)
                  (f := SchwartzNPoint.osConj (d := d) (n := 1)
                    (onePointToFin1CLM d χ : SchwartzNPoint d 1))
                  (g := (onePointToFin1CLM d h : SchwartzNPoint d 1))
                  (t := t)
                  (Ψ := fun z => G (BHW.flattenCfg 2 d z)))
    _ =
        ∫ z : NPointDomain d 2,
          G (BHW.flattenCfg 2 d
              (xiShift ⟨1, by omega⟩ 0
                (fun i => wickRotatePoint (z i)) ((t : ℂ) * Complex.I))) *
            (χ (z 0) * h (z 1)) := by
              refine integral_congr_ae ?_
              filter_upwards with z
              rw [onePoint_osConjTensorProduct_apply (d := d) χ h z]
    _ =
        ∫ z : NPointDomain d 2,
          G (Function.update
              (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i)))
              (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1))))
              (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))
                (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) +
                (t : ℂ) * Complex.I)) *
            (χ (z 0) * h (z 1)) := by
              refine integral_congr_ae ?_
              filter_upwards with z
              congr 2
              simpa using
                (twoPoint_flattenCfg_xiShift_secondTime_eq_update
                  (d := d) (z := fun i => wickRotatePoint (z i))
                  (t := (t : ℂ) * Complex.I))

/-- For fixed positive-time difference-variable test `h`, the flat-update slice
already collapses the center slot to multiplication by `∫ χ`. -/
theorem schwinger_twoPoint_flatUpdateWitness_exists_const_local
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (t : ℝ) (ht : 0 < t) :
    ∃ c : ℂ, ∀ χ : SchwartzSpacetime d,
      ∫ z : NPointDomain d 2,
        G (Function.update
            (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i)))
            (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1))))
            (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))
              (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) +
              (t : ℂ) * Complex.I)) *
          (χ (z 0) * h (z 1)) =
        c * ∫ y : SpacetimeDim d, χ y := by
  have hshift0 :
      (0 : SpacetimeDim d) ∉ tsupport
        (((SCV.translateSchwartz (- timeShiftVec d t) h : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ)) := by
    refine zero_not_mem_tsupport_translate_of_notMem (d := d) h (- timeShiftVec d t) ?_
    exact neg_timeShiftVec_not_mem_positive_tsupport (d := d) h hh_pos t ht
  obtain ⟨c, hc⟩ :=
    OsterwalderSchraderAxioms.exists_const_twoPointDifferenceLift_eq_integral
      (d := d) (OS := OS) (h := SCV.translateSchwartz (- timeShiftVec d t) h) hshift0
  refine ⟨c, ?_⟩
  intro χ
  calc
    ∫ z : NPointDomain d 2,
        G (Function.update
            (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i)))
            (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1))))
            (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))
              (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) +
              (t : ℂ) * Complex.I)) *
          (χ (z 0) * h (z 1))
      = OS.S 2
          (ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift χ
              (SCV.translateSchwartz (- timeShiftVec d t) h))) := by
          symm
          exact schwinger_twoPointDifferenceLift_timeShift_eq_flatUpdate_of_positiveSupport_local
            (d := d) OS G hG_euclid χ h hh_pos t ht
    _ = c * ∫ y : SpacetimeDim d, χ y := hc χ

/-- For fixed strip time `t` and fixed positive-support test `h`, the
Euclidean continuation base-step already yields one common flat-update witness
for all center cutoffs. -/
theorem exists_common_fixedTime_flatUpdateWitness_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (t : ℝ) (ht : 0 < t) :
    ∃ G : (Fin (2 * (d + 1)) → ℂ) → ℂ,
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2,
          G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x)) ∧
      (∀ χ : SchwartzSpacetime d,
        OS.S 2
            (ZeroDiagonalSchwartz.ofClassical
              (twoPointDifferenceLift χ
                (SCV.translateSchwartz (- timeShiftVec d t) h))) =
          ∫ z : NPointDomain d 2,
            G (Function.update
                (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i)))
                (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1))))
                (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))
                  (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) +
                  (t : ℂ) * Complex.I)) *
              (χ (z 0) * h (z 1))) := by
  obtain ⟨G, hG_holo, hG_euclid⟩ :=
    schwinger_continuation_base_step (d := d) OS lgc 2
  refine ⟨G, hG_holo, hG_euclid, ?_⟩
  intro χ
  exact schwinger_twoPointDifferenceLift_timeShift_eq_flatUpdate_of_positiveSupport_local
    (d := d) OS G hG_euclid χ h hh_pos t ht

/-- The fixed-time flat-update witness already has the center-value collapse
needed for the Input A strip analysis. -/
theorem exists_common_fixedTime_flatUpdate_centerValue_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (t : ℝ) (ht : 0 < t) :
    ∃ G : (Fin (2 * (d + 1)) → ℂ) → ℂ,
      IsTimeHolomorphicFlatPositiveTimeDiffWitness G ∧
      (∀ (f : ZeroDiagonalSchwartz d 2),
        OS.S 2 f = ∫ x : NPointDomain d 2,
          G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x)) ∧
      ∃ c : ℂ, ∀ χ : SchwartzSpacetime d,
        ∫ z : NPointDomain d 2,
          G (Function.update
              (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i)))
              (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1))))
              (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))
                (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) +
                (t : ℂ) * Complex.I)) *
            (χ (z 0) * h (z 1)) =
          c * ∫ y : SpacetimeDim d, χ y := by
  obtain ⟨G, hG_holo, hG_euclid, hG_pair⟩ :=
    exists_common_fixedTime_flatUpdateWitness_local (d := d) OS lgc h hh_pos t ht
  obtain ⟨c, hc⟩ :=
    schwinger_twoPoint_flatUpdateWitness_exists_const_local
      (d := d) OS G hG_euclid h hh_pos t ht
  exact ⟨G, hG_holo, hG_euclid, c, hc⟩

end OSReconstruction
