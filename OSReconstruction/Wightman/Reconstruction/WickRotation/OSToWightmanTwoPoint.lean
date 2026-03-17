/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.TwoPointDescent
import OSReconstruction.Wightman.Reconstruction.TwoPointKernelFunctional
import OSReconstruction.Wightman.Reconstruction.CenterSpatialTranslationInvariant
import OSReconstruction.Wightman.Reconstruction.HeadBlockTranslationInvariant
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightman

/-!
# OS to Wightman Two-Point Continuation Reductions

This file contains the specialized `k = 2` continuation/reduction ladder for the
`E→R` reconstruction chain:

- admissible-shell vs witness-shell equivalences
- normalized-center reduction and uniqueness
- Laplace / polarized-Laplace sufficient criteria
- semigroup spectral and matrix-element criteria
- product-shell sufficient criteria

The shared continuation infrastructure now lives in
`OSToWightmanBase.lean`; the specialized `k = 2` holomorphic-kernel blocker
surface lives in `OSToWightmanKernel.lean`; and the general continuation core
and wrappers remain in `OSToWightman.lean`.
-/

open scoped Classical NNReal
open BigOperators Finset
open MeasureTheory OSReconstruction

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem tsupport_precomp_subset_proj0
    (χ : SchwartzSpacetime d) :
    tsupport (fun x : NPointDomain d 2 => χ (x 0)) ⊆
      (fun x : NPointDomain d 2 => x 0) ⁻¹' tsupport (χ : SpacetimeDim d → ℂ) := by
  refine closure_minimal ?_ ((isClosed_tsupport _).preimage (continuous_apply 0))
  intro x hx
  exact subset_closure (by simpa [Function.mem_support] using hx)

omit [NeZero d] in
private theorem tsupport_twoPointDifferenceLift_subset_proj0_preimage
    (χ h : SchwartzSpacetime d) :
    tsupport ((twoPointDifferenceLift χ h : SchwartzNPoint d 2) :
        NPointDomain d 2 → ℂ) ⊆
      (fun x : NPointDomain d 2 => x 0) ⁻¹' tsupport (χ : SpacetimeDim d → ℂ) := by
  refine (tsupport_mul_subset_left
    (f := fun x : NPointDomain d 2 => χ (x 0))
    (g := fun x : NPointDomain d 2 => h (x 1 - x 0))).trans ?_
  exact tsupport_precomp_subset_proj0 (d := d) χ

omit [NeZero d] in
private theorem tsupport_twoPointDifferenceLift_subset_orderedPositiveTimeRegion
    (χ h : SchwartzSpacetime d)
    (hχ_pos : tsupport (χ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0}) :
    tsupport ((twoPointDifferenceLift χ h : SchwartzNPoint d 2) :
        NPointDomain d 2 → ℂ) ⊆ OrderedPositiveTimeRegion d 2 := by
  intro x hx
  have hx0 : x 0 ∈ tsupport (χ : SpacetimeDim d → ℂ) := by
    exact (tsupport_twoPointDifferenceLift_subset_proj0_preimage (d := d) χ h hx)
  have hdiff : x 1 - x 0 ∈ tsupport (h : SpacetimeDim d → ℂ) := by
    exact (tsupport_twoPointDifferenceLift_subset_diff_preimage χ h hx)
  have hx0_pos : 0 < (x 0) 0 := hχ_pos hx0
  have hdiff_pos : 0 < (x 1 - x 0) 0 := hh_pos hdiff
  intro i
  fin_cases i
  · refine ⟨hx0_pos, ?_⟩
    intro j hij
    fin_cases j
    · exact (lt_irrefl _ hij).elim
    · simpa [sub_eq_add_neg] using hdiff_pos
  · refine ⟨?_, ?_⟩
    · have hcoord : (x 1 - x 0) 0 = x 1 0 - x 0 0 := by
        simp
      have hx1_eq : x 1 0 = x 0 0 + (x 1 - x 0) 0 := by
        linarith
      have hx1_pos : 0 < x 1 0 := by
        nlinarith [hx1_eq, hx0_pos, hdiff_pos]
      simpa using hx1_pos
    · intro j hij
      fin_cases j
      · exact (Fin.not_lt_zero _ hij).elim
      · exact (lt_irrefl _ hij).elim

omit [NeZero d] in
private theorem timeShiftSchwartzNPoint_twoPointDifferenceLift_eq
    (χ h : SchwartzSpacetime d) (t : ℝ) :
    timeShiftSchwartzNPoint (d := d) t (twoPointDifferenceLift χ h) =
      twoPointDifferenceLift (SCV.translateSchwartz (- timeShiftVec d t) χ) h := by
  ext x
  have hdiff :
      (x 1 - timeShiftVec d t) - (x 0 - timeShiftVec d t) = x 1 - x 0 := by
    ext μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [timeShiftVec]
    · simp [timeShiftVec, hμ]
  rw [timeShiftSchwartzNPoint_apply, twoPointDifferenceLift_apply,
    twoPointDifferenceLift_apply, SCV.translateSchwartz_apply]
  congr 1
  rw [hdiff]

omit [NeZero d] in
private theorem twoPointCenterDiff_toDiffFlat_wickRotate
    (z : NPointDomain d 2) :
    BHW.toDiffFlat 2 d (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i)) =
      BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i)) := by
  ext p
  obtain ⟨q, rfl⟩ := finProdFinEquiv.surjective p
  rcases q with ⟨i, μ⟩
  fin_cases i
  · simp [BHW.toDiffFlat, BHW.flattenCfg, BHW.diffCoordEquiv_apply,
      twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv, wickRotatePoint]
  · by_cases hμ : μ = 0
    · subst hμ
      simp [BHW.toDiffFlat, BHW.flattenCfg, BHW.diffCoordEquiv_apply,
        twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv, wickRotatePoint]
      ring_nf
    · simp [BHW.toDiffFlat, BHW.flattenCfg, BHW.diffCoordEquiv_apply,
        twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv, wickRotatePoint, hμ]

omit [NeZero d] in
private theorem twoPointCenterDiff_xiShift_secondTime_toDiffFlat_eq_update
    (z : NPointDomain d 2) (t : ℂ) :
    BHW.toDiffFlat 2 d
        (xiShift ⟨1, by omega⟩ 0
          (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
          t) =
      Function.update
        (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i)))
        (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1))))
        (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))
          (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) + t) := by
  let zc : Fin 2 → Fin (d + 1) → ℂ :=
    fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i)
  have hfrom :
      BHW.fromDiffFlat 2 d
          (Function.update
            (BHW.toDiffFlat 2 d zc)
            (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1))))
            (BHW.toDiffFlat 2 d zc
              (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) + t)) =
        xiShift ⟨1, by omega⟩ 0 zc t := by
    simpa [zc, sub_eq_add_neg, BHW.fromDiffFlat_toDiffFlat] using
      (fromDiffFlat_update_eq_xiShift_sub
        (k := 2) (d := d)
        (j := ⟨1, by omega⟩) (r := (0 : Fin (d + 1)))
        (u := BHW.toDiffFlat 2 d zc)
        (w := BHW.toDiffFlat 2 d zc
          (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) + t))
  have hflat :
      Function.update
          (BHW.toDiffFlat 2 d zc)
          (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1))))
          (BHW.toDiffFlat 2 d zc
            (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) + t) =
        BHW.toDiffFlat 2 d
          (xiShift ⟨1, by omega⟩ 0 zc t) := by
    simpa [BHW.toDiffFlat_fromDiffFlat] using
      congrArg (BHW.toDiffFlat 2 d) hfrom
  simpa [zc, twoPointCenterDiff_toDiffFlat_wickRotate] using hflat.symm

private theorem schwinger_twoPointDifferenceLift_baseTime_eq_constant_of_positiveSupport
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (χ h : SchwartzSpacetime d)
    (hχ_pos : tsupport (χ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (t : ℝ) (ht : 0 < t) :
    ∫ y : NPointDomain d 2,
      Ψ (xiShift 0 0 (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
        (twoPointDifferenceLift χ h) y =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) := by
  let f0fun : NPointDomain d 0 → ℂ := fun _ => 1
  have hf0_compact : HasCompactSupport f0fun := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := (Set.univ : Set (NPointDomain d 0))) ?_ ?_
    · exact Set.Subsingleton.isCompact Set.subsingleton_univ
    · intro x hx
      simp
  have hf0_smooth : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) f0fun := by
    simpa [f0fun] using
      (contDiff_const :
        ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
          (fun _ : NPointDomain d 0 => (1 : ℂ)))
  let f0 : SchwartzNPoint d 0 := hf0_compact.toSchwartzMap hf0_smooth
  have hf0_apply : ∀ x : NPointDomain d 0, f0 x = 1 := by
    intro x
    rfl
  have hf0_ord :
      tsupport (f0 : NPointDomain d 0 → ℂ) ⊆ OrderedPositiveTimeRegion d 0 := by
    intro x hx
    simp [OrderedPositiveTimeRegion]
  have hg_ord :
      tsupport (((twoPointDifferenceLift χ h : SchwartzNPoint d 2) :
          NPointDomain d 2 → ℂ)) ⊆ OrderedPositiveTimeRegion d 2 :=
    tsupport_twoPointDifferenceLift_subset_orderedPositiveTimeRegion
      (d := d) χ h hχ_pos hh_pos
  have h0 :
      (0 : SpacetimeDim d) ∉ tsupport (h : SpacetimeDim d → ℂ) := by
    intro h0mem
    have hnot : ¬ 0 < ((0 : SpacetimeDim d) 0) := by
      simp
    exact hnot (hh_pos h0mem)
  have hshift :
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (timeShiftSchwartzNPoint (d := d) t (twoPointDifferenceLift χ h))) =
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) := by
    rw [timeShiftSchwartzNPoint_twoPointDifferenceLift_eq (d := d) χ h t]
    exact (OsterwalderSchraderAxioms.schwinger_twoPointDifferenceLift_translation_invariant
      (d := d) (OS := OS) (a := -timeShiftVec d t) (χ := χ) (h := h) h0).symm
  calc
    ∫ y : NPointDomain d 2,
        Ψ (xiShift 0 0 (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
          (twoPointDifferenceLift χ h) y
      = OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (f0.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t (twoPointDifferenceLift χ h)))) := by
          symm
          have hosconj0 : SchwartzNPoint.osConj (d := d) (n := 0) f0 = f0 := by
            ext x
            simp [SchwartzNPoint.osConj_apply, hf0_apply]
          have htensor :
              f0.osConjTensorProduct (twoPointDifferenceLift χ h) =
                twoPointDifferenceLift χ h := by
            ext y
            have hsplit : splitLast 0 2 y = y := by
              ext i
              simp [splitLast]
            calc
              (f0.osConjTensorProduct (twoPointDifferenceLift χ h)) y
                  = ((f0.tensorProduct (twoPointDifferenceLift χ h)) y) := by
                      simp [SchwartzNPoint.osConjTensorProduct, hosconj0]
              _ = f0 (splitFirst 0 2 y) * (twoPointDifferenceLift χ h) (splitLast 0 2 y) := by
                    rw [SchwartzMap.tensorProduct_apply]
              _ = 1 * (twoPointDifferenceLift χ h) y := by
                    simp [hf0_apply, hsplit]
              _ = (twoPointDifferenceLift χ h) y := by simp
          simpa [htensor] using
            (schwinger_simpleTensor_timeShift_eq_xiShift
              (d := d) (OS := OS) (n := 0) (m := 2) (hm := by omega)
              (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
              (f := f0) (hf_ord := hf0_ord)
              (g := twoPointDifferenceLift χ h) (hg_ord := hg_ord)
              (t := t) ht)
    _ = OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (timeShiftSchwartzNPoint (d := d) t (twoPointDifferenceLift χ h))) := by
          have htensor_shift :
              f0.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t
                (twoPointDifferenceLift χ h)) =
                timeShiftSchwartzNPoint (d := d) t (twoPointDifferenceLift χ h) := by
            ext y
            have hosconj0 : SchwartzNPoint.osConj (d := d) (n := 0) f0 = f0 := by
              ext x
              simp [SchwartzNPoint.osConj_apply, hf0_apply]
            have hsplit : splitLast 0 2 y = y := by
              ext i
              simp [splitLast]
            calc
              (f0.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t
                  (twoPointDifferenceLift χ h))) y
                  = ((f0.tensorProduct (timeShiftSchwartzNPoint (d := d) t
                      (twoPointDifferenceLift χ h))) y) := by
                        simp [SchwartzNPoint.osConjTensorProduct, hosconj0]
              _ = f0 (splitFirst 0 2 y) *
                    (timeShiftSchwartzNPoint (d := d) t (twoPointDifferenceLift χ h))
                      (splitLast 0 2 y) := by
                    rw [SchwartzMap.tensorProduct_apply]
              _ = 1 *
                    (timeShiftSchwartzNPoint (d := d) t (twoPointDifferenceLift χ h)) y := by
                    simp [hf0_apply, hsplit]
              _ = (timeShiftSchwartzNPoint (d := d) t (twoPointDifferenceLift χ h)) y := by
                    simp
          simp [htensor_shift]
    _ = OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)) := hshift

/-- On the admissible two-point shell with positive-time center and
positive-time difference support, the base-time `ξ`-shift variable already has
the trivial holomorphic continuation: the constant Schwinger value. So the live
two-point `E -> R` obstruction really is the difference-time variable, not the
center-time one. -/
theorem exists_twoPoint_baseTime_holomorphicValue_constant
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (χ h : SchwartzSpacetime d)
    (hχ_pos : tsupport (χ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    :
    ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
      ∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          ∫ y : NPointDomain d 2,
            Ψ (xiShift 0 0 (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              (twoPointDifferenceLift χ h) y := by
  refine ⟨fun _ => OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h)),
    by
      exact differentiableOn_const
        (s := {z : ℂ | 0 < z.re})
        (c := OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointDifferenceLift χ h))), ?_⟩
  intro t ht
  exact (schwinger_twoPointDifferenceLift_baseTime_eq_constant_of_positiveSupport
    (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
    χ h hχ_pos hh_pos t ht).symm

/-- Real-axis bridge on the actual two-point center/difference shell. Shifting
the difference test by positive Euclidean time is exactly the same as updating
the flattened difference-time coordinate of the flat witness by `+ t I`. This
avoids the bad product-shell shear and stays on the admissible family
`χ(u) h(ξ)`. -/
theorem schwinger_twoPointDifferenceLift_timeShift_eq_flatUpdate
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (χ h : SchwartzSpacetime d)
    (t : ℝ)
    (hshift0 :
      (0 : SpacetimeDim d) ∉ tsupport
        (((SCV.translateSchwartz (- timeShiftVec d t) h : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ))) :
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
  calc
    OS.S 2
        (ZeroDiagonalSchwartz.ofClassical
          (twoPointDifferenceLift χ (SCV.translateSchwartz (- timeShiftVec d t) h)))
      = ∫ z : NPointDomain d 2,
          G (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))) *
            (χ (z 0) * (SCV.translateSchwartz (- timeShiftVec d t) h) (z 1)) := by
          exact schwinger_twoPointDifferenceLift_eq_flatCenterDiffWitnessIntegral_sameCenter
            (d := d) OS G hG_euclid
            (SCV.translateSchwartz (- timeShiftVec d t) h) hshift0 χ
    _ = ∫ z : NPointDomain d 2,
          G (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))) *
            (((SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d χ : SchwartzNPoint d 1)).osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) t (onePointToFin1CLM d h))) z) := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with z
          rw [onePoint_osConjTensorProduct_timeShift_apply (d := d) χ h t z]
    _ = ∫ z : NPointDomain d 2,
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
    _ = ∫ z : NPointDomain d 2,
          G (BHW.flattenCfg 2 d
              (xiShift ⟨1, by omega⟩ 0
                (fun i => wickRotatePoint (z i)) ((t : ℂ) * Complex.I))) *
            (χ (z 0) * h (z 1)) := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with z
          rw [onePoint_osConjTensorProduct_apply (d := d) χ h z]
    _ = ∫ z : NPointDomain d 2,
          G (Function.update
              (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i)))
              (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1))))
              (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))
                (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) +
                (t : ℂ) * Complex.I)) *
            (χ (z 0) * h (z 1)) := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with z
          congr 2
          simpa using
            (twoPoint_flattenCfg_xiShift_secondTime_eq_update
              (d := d) (z := fun i => wickRotatePoint (z i))
              (t := (t : ℂ) * Complex.I))

/-- Real-axis center collapse for the updated two-point flat witness. After the
`+ t I` update in the second time-difference coordinate, the admissible
two-point witness still depends on the center cutoff only through its integral.
This packages the real-axis slice as an honest one-difference-variable scalar
for each fixed `t`. -/
theorem schwinger_twoPoint_flatUpdateWitness_exists_const
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (h : SchwartzSpacetime d)
    (t : ℝ)
    (hshift0 :
      (0 : SpacetimeDim d) ∉ tsupport
        (((SCV.translateSchwartz (- timeShiftVec d t) h : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ))) :
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
            (twoPointDifferenceLift χ (SCV.translateSchwartz (- timeShiftVec d t) h))) := by
          symm
          exact schwinger_twoPointDifferenceLift_timeShift_eq_flatUpdate
            (d := d) OS G hG_euclid χ h t hshift0
    _ = c * ∫ y : SpacetimeDim d, χ y := hc χ

/-- Cleaner positive-time corollary of the two-point real-axis bridge: if the
difference test is supported in positive Euclidean time, then the shifted test
is automatically admissible for every `t > 0`, so no extra `hshift0`
hypothesis is needed. -/
theorem schwinger_twoPointDifferenceLift_timeShift_eq_flatUpdate_of_positiveSupport
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
  exact schwinger_twoPointDifferenceLift_timeShift_eq_flatUpdate
    (d := d) OS G hG_euclid χ h t hshift0

/-- Direct `Ψ`-witness bridge on the actual admissible two-point
center/difference shell. For positive Euclidean time, shifting the difference
test is exactly the same as evaluating the original witness on the
`+ t I` ξ-shifted Euclidean configuration. -/
theorem schwinger_twoPointDifferenceLift_timeShift_eq_xiShift_of_positiveSupport
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (h : ZeroDiagonalSchwartz d 2),
      OS.S 2 h = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (h.1 x))
    (χ h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (t : ℝ) (ht : 0 < t) :
    OS.S 2
      (ZeroDiagonalSchwartz.ofClassical
        (twoPointDifferenceLift χ
          (SCV.translateSchwartz (- timeShiftVec d t) h))) =
      ∫ y : NPointDomain d 2,
        Ψ (xiShift ⟨1, by omega⟩ 0
          (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
          ((t : ℂ) * Complex.I)) *
          (χ (y 0) * h (y 1)) := by
  let G : (Fin (2 * (d + 1)) → ℂ) → ℂ := fun u => Ψ (BHW.fromDiffFlat 2 d u)
  have hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x) := by
    intro f
    simpa [G, Function.comp_apply, BHW.fromDiffFlat_toDiffFlat] using hΨ_euclid f
  calc
    OS.S 2
      (ZeroDiagonalSchwartz.ofClassical
        (twoPointDifferenceLift χ
          (SCV.translateSchwartz (- timeShiftVec d t) h)))
      = ∫ y : NPointDomain d 2,
          G (Function.update
              (BHW.flattenCfg 2 d (fun i => wickRotatePoint (y i)))
              (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1))))
              (BHW.flattenCfg 2 d (fun i => wickRotatePoint (y i))
                (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) +
                (t : ℂ) * Complex.I)) *
            (χ (y 0) * h (y 1)) := by
        exact schwinger_twoPointDifferenceLift_timeShift_eq_flatUpdate_of_positiveSupport
          (d := d) OS G hG_euclid χ h hh_pos t ht
    _ = ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ (y 0) * h (y 1)) := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with y
        have hslice :
            BHW.fromDiffFlat 2 d
                (Function.update
                  (BHW.flattenCfg 2 d (fun i => wickRotatePoint (y i)))
                  (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1))))
                  (BHW.flattenCfg 2 d (fun i => wickRotatePoint (y i))
                    (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) +
                    (t : ℂ) * Complex.I)) =
              xiShift ⟨1, by omega⟩ 0
                (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
                ((t : ℂ) * Complex.I) := by
          have hcfg :
              BHW.fromDiffFlat 2 d
                  (BHW.flattenCfg 2 d (fun i => wickRotatePoint (y i))) =
                fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i) := by
            rw [← twoPointCenterDiff_toDiffFlat_wickRotate (d := d) y]
            simp [BHW.fromDiffFlat_toDiffFlat]
          simpa [twoPointCenterDiff_toDiffFlat_wickRotate (d := d) y, hcfg, sub_eq_add_neg]
            using
              (fromDiffFlat_update_eq_xiShift_sub
                (j := ⟨1, by omega⟩) (r := (0 : Fin (d + 1)))
                (u := BHW.toDiffFlat 2 d
                  (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i)))
                (w := BHW.toDiffFlat 2 d
                    (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
                    (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) +
                  (t : ℂ) * Complex.I))
        exact congrArg (fun z => Ψ z * (χ (y 0) * h (y 1))) hslice

private theorem selfAdjointSpectralLaplaceOffdiag_onePoint_pair_eq_flatUpdate_centerShear
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (χ g : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (t : ℝ) (ht : 0 < t) :
    ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
        (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d χ : SchwartzNPoint d 1))
                hχ_pos⟧)) : OSHilbertSpace OS))
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (onePointToFin1CLM d g : SchwartzNPoint d 1)
                hg_pos⟧)) : OSHilbertSpace OS))
        (t : ℂ) =
      ∫ z : NPointDomain d 2,
        G (Function.update
            (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i)))
            (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1))))
            (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))
              (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) +
              (t : ℂ) * Complex.I)) *
          (χ (z 0) * g (z 0 + z 1)) := by
  let Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ := fun z => G (BHW.toDiffFlat 2 d z)
  have hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x) := by
    intro f
    simpa [Ψ, Function.comp_apply] using hG_euclid f
  calc
    ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
        (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d χ : SchwartzNPoint d 1))
                hχ_pos⟧)) : OSHilbertSpace OS))
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (onePointToFin1CLM d g : SchwartzNPoint d 1)
                hg_pos⟧)) : OSHilbertSpace OS))
        (t : ℂ)
      =
        ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (y i))
            ((t : ℂ) * Complex.I)) *
            (χ (y 0) * g (y 1)) := by
          exact selfAdjointSpectralLaplaceOffdiag_onePoint_pair_eq_xiShift
            (d := d) (OS := OS) (lgc := lgc) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
            χ g hχ_pos hg_pos hg_compact t ht
    _ =
        ∫ z : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
            ((t : ℂ) * Complex.I)) *
            (χ (z 0) * g (z 0 + z 1)) := by
          simpa [twoPointProductLift_apply] using
            (integral_mul_twoPointProductLift_eq_centerShear
              (d := d)
              (Ψ := fun y : NPointDomain d 2 =>
                Ψ (xiShift ⟨1, by omega⟩ 0
                  (fun i => wickRotatePoint (y i))
                  ((t : ℂ) * Complex.I)))
              χ g)
    _ =
        ∫ z : NPointDomain d 2,
          G (Function.update
              (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i)))
              (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1))))
              (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))
                (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) +
                (t : ℂ) * Complex.I)) *
            (χ (z 0) * g (z 0 + z 1)) := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with z
          have hcfg :=
            twoPointCenterDiff_xiShift_secondTime_toDiffFlat_eq_update
              (d := d) (z := z) (t := (t : ℂ) * Complex.I)
          exact congrArg
            (fun u =>
              G u * (χ (z 0) * g (z 0 + z 1))) hcfg

private theorem OSInnerProductTimeShiftHolomorphicValue_onePoint_pair_eq_flatUpdate_centerShear
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (χ g : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (t : ℝ) (ht : 0 < t) :
    OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        ((show PositiveTimeBorchersSequence d from
          PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d χ : SchwartzNPoint d 1))
            hχ_pos))
        ((show PositiveTimeBorchersSequence d from
          PositiveTimeBorchersSequence.single 1
            (onePointToFin1CLM d g : SchwartzNPoint d 1)
            hg_pos))
        (t : ℂ) =
      ∫ z : NPointDomain d 2,
        G (Function.update
            (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i)))
            (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1))))
            (BHW.flattenCfg 2 d (fun i => wickRotatePoint (z i))
              (finProdFinEquiv (⟨1, by omega⟩, (0 : Fin (d + 1)))) +
              (t : ℂ) * Complex.I)) *
          (χ (z 0) * g (z 0 + z 1)) := by
  rw [OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag
    (d := d) (OS := OS) (lgc := lgc)
    ((show PositiveTimeBorchersSequence d from
      PositiveTimeBorchersSequence.single 1
        (SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d χ : SchwartzNPoint d 1))
        hχ_pos))
    ((show PositiveTimeBorchersSequence d from
      PositiveTimeBorchersSequence.single 1
        (onePointToFin1CLM d g : SchwartzNPoint d 1)
        hg_pos))
    (t : ℂ) (by simpa using ht)]
  exact selfAdjointSpectralLaplaceOffdiag_onePoint_pair_eq_flatUpdate_centerShear
    (d := d) (OS := OS) (lgc := lgc) (G := G) (hG_euclid := hG_euclid)
    χ g hχ_pos hg_pos hg_compact t ht

private theorem selfAdjointSpectralLaplaceOffdiag_onePoint_pair_eq_xiShift_centerShear
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (h : ZeroDiagonalSchwartz d 2),
      OS.S 2 h = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (h.1 x))
    (χ g : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (t : ℝ) (ht : 0 < t) :
    ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
        (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d χ : SchwartzNPoint d 1))
                hχ_pos⟧)) : OSHilbertSpace OS))
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (onePointToFin1CLM d g : SchwartzNPoint d 1)
                hg_pos⟧)) : OSHilbertSpace OS))
        (t : ℂ) =
      ∫ z : NPointDomain d 2,
        Ψ (xiShift ⟨1, by omega⟩ 0
          (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
          ((t : ℂ) * Complex.I)) *
          (χ (z 0) * g (z 0 + z 1)) := by
  calc
    ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
        (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d χ : SchwartzNPoint d 1))
                hχ_pos⟧)) : OSHilbertSpace OS))
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (onePointToFin1CLM d g : SchwartzNPoint d 1)
                hg_pos⟧)) : OSHilbertSpace OS))
        (t : ℂ)
      =
        ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (y i))
            ((t : ℂ) * Complex.I)) *
            (χ (y 0) * g (y 1)) := by
          exact selfAdjointSpectralLaplaceOffdiag_onePoint_pair_eq_xiShift
            (d := d) (OS := OS) (lgc := lgc) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
            χ g hχ_pos hg_pos hg_compact t ht
    _ =
        ∫ z : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
            ((t : ℂ) * Complex.I)) *
            (χ (z 0) * g (z 0 + z 1)) := by
          simpa [twoPointProductLift_apply] using
            (integral_mul_twoPointProductLift_eq_centerShear
              (d := d)
              (Ψ := fun y : NPointDomain d 2 =>
                Ψ (xiShift ⟨1, by omega⟩ 0
                  (fun i => wickRotatePoint (y i))
                  ((t : ℂ) * Complex.I)))
              χ g)

private theorem OSInnerProductTimeShiftHolomorphicValue_onePoint_pair_eq_xiShift_centerShear
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (h : ZeroDiagonalSchwartz d 2),
      OS.S 2 h = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (h.1 x))
    (χ g : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (t : ℝ) (ht : 0 < t) :
    OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        ((show PositiveTimeBorchersSequence d from
          PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d χ : SchwartzNPoint d 1))
            hχ_pos))
        ((show PositiveTimeBorchersSequence d from
          PositiveTimeBorchersSequence.single 1
            (onePointToFin1CLM d g : SchwartzNPoint d 1)
            hg_pos))
        (t : ℂ) =
      ∫ z : NPointDomain d 2,
        Ψ (xiShift ⟨1, by omega⟩ 0
          (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
          ((t : ℂ) * Complex.I)) *
          (χ (z 0) * g (z 0 + z 1)) := by
  rw [OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag
    (d := d) (OS := OS) (lgc := lgc)
    ((show PositiveTimeBorchersSequence d from
      PositiveTimeBorchersSequence.single 1
        (SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d χ : SchwartzNPoint d 1))
        hχ_pos))
    ((show PositiveTimeBorchersSequence d from
      PositiveTimeBorchersSequence.single 1
        (onePointToFin1CLM d g : SchwartzNPoint d 1)
        hg_pos))
    (t : ℂ) (by simpa using ht)]
  exact selfAdjointSpectralLaplaceOffdiag_onePoint_pair_eq_xiShift_centerShear
    (d := d) (OS := OS) (lgc := lgc) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
    χ g hχ_pos hg_pos hg_compact t ht

private theorem integral_xiShift_centerShear_translate_spatial
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (h : ZeroDiagonalSchwartz d 2),
      OS.S 2 h = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (h.1 x))
    (a : SpacetimeDim d) (ha0 : a 0 = 0)
    (χ g : SchwartzSpacetime d)
    (hχ_pos : tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_pos : tsupport (((onePointToFin1CLM d g : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (t : ℝ) (ht : 0 < t) :
    ∫ z : NPointDomain d 2,
      Ψ (xiShift ⟨1, by omega⟩ 0
        (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
        ((t : ℂ) * Complex.I)) *
        ((SCV.translateSchwartz a χ) (z 0) *
          (SCV.translateSchwartz a g) (z 0 + z 1)) =
    ∫ z : NPointDomain d 2,
      Ψ (xiShift ⟨1, by omega⟩ 0
        (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
        ((t : ℂ) * Complex.I)) *
        (χ (z 0) * g (z 0 + z 1)) := by
  have ha0_neg : (-a) 0 = 0 := by simpa [ha0]
  have hχ_eq :
      (SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d (SCV.translateSchwartz a χ) : SchwartzNPoint d 1)) =
      translateSchwartzNPoint (d := d) (-a)
        (SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d χ : SchwartzNPoint d 1)) := by
    ext x
    have hreflect :
        timeReflection d (a + x 0) = a + timeReflection d (x 0) := by
      ext μ
      by_cases hμ : μ = 0
      · subst hμ
        simp [timeReflection, ha0]
      · simp [timeReflection, hμ]
    simp [SchwartzNPoint.osConj_apply, onePointToFin1CLM_apply,
      SCV.translateSchwartz_apply, translateSchwartzNPoint_apply,
      timeReflectionN, sub_eq_add_neg, hreflect, add_assoc, add_left_comm,
      add_comm]
  have hg_eq :
      (onePointToFin1CLM d (SCV.translateSchwartz a g) : SchwartzNPoint d 1) =
      translateSchwartzNPoint (d := d) (-a)
        (onePointToFin1CLM d g : SchwartzNPoint d 1) := by
    ext x
    simp [onePointToFin1CLM_apply, SCV.translateSchwartz_apply,
      translateSchwartzNPoint_apply, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm]
  let hχ_pos' :=
    translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
      (d := d) (-a) ha0_neg
      (SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d χ : SchwartzNPoint d 1))
      hχ_pos
  let hg_pos' :=
    translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
      (d := d) (-a) ha0_neg
      (onePointToFin1CLM d g : SchwartzNPoint d 1)
      hg_pos
  have hg_compact' : HasCompactSupport ((SCV.translateSchwartz a g : SchwartzSpacetime d) :
      SpacetimeDim d → ℂ) := by
    change HasCompactSupport (fun x : SpacetimeDim d => g (x + a))
    simpa [Function.comp, SCV.translateSchwartz_apply, add_comm, add_left_comm, add_assoc] using
      hg_compact.comp_homeomorph (Homeomorph.addRight a)
  calc
    ∫ z : NPointDomain d 2,
        Ψ (xiShift ⟨1, by omega⟩ 0
          (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
          ((t : ℂ) * Complex.I)) *
          ((SCV.translateSchwartz a χ) (z 0) *
            (SCV.translateSchwartz a g) (z 0 + z 1))
      = OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          ((show PositiveTimeBorchersSequence d from
            PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d (SCV.translateSchwartz a χ) : SchwartzNPoint d 1))
              (by simpa [hχ_eq] using hχ_pos')))
          ((show PositiveTimeBorchersSequence d from
            PositiveTimeBorchersSequence.single 1
              (onePointToFin1CLM d (SCV.translateSchwartz a g) : SchwartzNPoint d 1)
              (by simpa [hg_eq] using hg_pos')))
          (t : ℂ) := by
            symm
            exact OSInnerProductTimeShiftHolomorphicValue_onePoint_pair_eq_xiShift_centerShear
              (d := d) (OS := OS) (lgc := lgc) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
              (SCV.translateSchwartz a χ) (SCV.translateSchwartz a g)
              (by simpa [hχ_eq] using hχ_pos')
              (by simpa [hg_eq] using hg_pos')
              hg_compact' t ht
    _ = OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          ((show PositiveTimeBorchersSequence d from
            PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d χ : SchwartzNPoint d 1))
              hχ_pos))
          ((show PositiveTimeBorchersSequence d from
            PositiveTimeBorchersSequence.single 1
              (onePointToFin1CLM d g : SchwartzNPoint d 1)
              hg_pos))
          (t : ℂ) := by
            simpa [hχ_eq, hg_eq] using
              (OSInnerProductTimeShiftHolomorphicValue_single_translate_spatial
                (d := d) (OS := OS) (lgc := lgc) (-a) ha0_neg
                (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d χ : SchwartzNPoint d 1))
                hχ_pos
                (onePointToFin1CLM d g : SchwartzNPoint d 1)
                hg_pos
                (hasCompactSupport_onePointToFin1 (d := d) g hg_compact)
                (t : ℂ) (by simpa using ht))
    _ = ∫ z : NPointDomain d 2,
        Ψ (xiShift ⟨1, by omega⟩ 0
          (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
          ((t : ℂ) * Complex.I)) *
          (χ (z 0) * g (z 0 + z 1)) := by
            exact OSInnerProductTimeShiftHolomorphicValue_onePoint_pair_eq_xiShift_centerShear
              (d := d) (OS := OS) (lgc := lgc) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
              χ g hχ_pos hg_pos hg_compact t ht

theorem exists_twoPointDifferenceLift_timeShift_holomorphicValue_iff_xiShiftWitness_of_positiveSupport
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (χ h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0}) :
    (∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
      (∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          OS.S 2
            (ZeroDiagonalSchwartz.ofClassical
              (twoPointDifferenceLift χ
                (SCV.translateSchwartz (- timeShiftVec d t) h))))) ↔
    (∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
      (∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          ∫ y : NPointDomain d 2,
            Ψ (xiShift ⟨1, by omega⟩ 0
              (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
              ((t : ℂ) * Complex.I)) *
              (χ (y 0) * h (y 1)))) := by
  constructor
  · rintro ⟨H, hH_holo, hH_real⟩
    refine ⟨H, hH_holo, ?_⟩
    intro t ht
    rw [hH_real t ht]
    exact schwinger_twoPointDifferenceLift_timeShift_eq_xiShift_of_positiveSupport
      (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
      χ h hh_pos t ht
  · rintro ⟨H, hH_holo, hH_real⟩
    refine ⟨H, hH_holo, ?_⟩
    intro t ht
    rw [hH_real t ht]
    exact (schwinger_twoPointDifferenceLift_timeShift_eq_xiShift_of_positiveSupport
      (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
      χ h hh_pos t ht).symm

/-- Real-axis center collapse directly in the original `Ψ` witness coordinates.
For each fixed positive Euclidean time `t`, the admissible two-point
`ξ`-shifted witness on the center/difference shell depends on the center cutoff
only through `∫ χ`. -/
theorem schwinger_twoPoint_xiShiftWitness_exists_const_of_positiveSupport
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (t : ℝ) (ht : 0 < t) :
    ∃ c : ℂ, ∀ χ : SchwartzSpacetime d,
      ∫ y : NPointDomain d 2,
        Ψ (xiShift ⟨1, by omega⟩ 0
          (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
          ((t : ℂ) * Complex.I)) *
          (χ (y 0) * h (y 1)) =
        c * ∫ u : SpacetimeDim d, χ u := by
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
    ∫ y : NPointDomain d 2,
        Ψ (xiShift ⟨1, by omega⟩ 0
          (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
          ((t : ℂ) * Complex.I)) *
          (χ (y 0) * h (y 1))
      = OS.S 2
          (ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift χ
              (SCV.translateSchwartz (- timeShiftVec d t) h))) := by
          symm
          exact schwinger_twoPointDifferenceLift_timeShift_eq_xiShift_of_positiveSupport
            (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
            χ h hh_pos t ht
    _ = c * ∫ u : SpacetimeDim d, χ u := hc χ

/-- Normalized center-value form of the real-axis two-point `ξ`-shift witness.
Fixing one center cutoff with integral `1` identifies the scalar from
`schwinger_twoPoint_xiShiftWitness_exists_const_of_positiveSupport` explicitly. -/
theorem schwinger_twoPoint_xiShiftWitness_eq_centerValue_of_positiveSupport
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (t : ℝ) (ht : 0 < t)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (χ : SchwartzSpacetime d) :
    ∫ y : NPointDomain d 2,
      Ψ (xiShift ⟨1, by omega⟩ 0
        (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
        ((t : ℂ) * Complex.I)) *
        (χ (y 0) * h (y 1)) =
      (∫ y : NPointDomain d 2,
        Ψ (xiShift ⟨1, by omega⟩ 0
          (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
          ((t : ℂ) * Complex.I)) *
          (χ₀ (y 0) * h (y 1))) *
        ∫ u : SpacetimeDim d, χ u := by
  obtain ⟨c, hc⟩ :=
    schwinger_twoPoint_xiShiftWitness_exists_const_of_positiveSupport
      (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid) h hh_pos t ht
  calc
    ∫ y : NPointDomain d 2,
        Ψ (xiShift ⟨1, by omega⟩ 0
          (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
          ((t : ℂ) * Complex.I)) *
          (χ (y 0) * h (y 1))
      = c * ∫ u : SpacetimeDim d, χ u := hc χ
    _ = (c * ∫ u : SpacetimeDim d, χ₀ u) * ∫ u : SpacetimeDim d, χ u := by
          rw [hχ₀, mul_one]
    _ = (∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (y 0) * h (y 1))) *
          ∫ u : SpacetimeDim d, χ u := by
          rw [hc χ₀]

/-- Zero-mean center cutoffs are annihilated by the real-axis two-point
`ξ`-shift witness. This is the exact real-axis vanishing statement needed for a
future identity-theorem step once the holomorphic shell is built on the
admissible center/difference family. -/
theorem schwinger_twoPoint_xiShiftWitness_eq_zero_of_centerIntegral_zero_of_positiveSupport
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (t : ℝ) (ht : 0 < t)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (χ : SchwartzSpacetime d)
    (hχ : ∫ u : SpacetimeDim d, χ u = 0) :
    ∫ y : NPointDomain d 2,
      Ψ (xiShift ⟨1, by omega⟩ 0
        (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
        ((t : ℂ) * Complex.I)) *
        (χ (y 0) * h (y 1)) = 0 := by
  rw [schwinger_twoPoint_xiShiftWitness_eq_centerValue_of_positiveSupport
    (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
    h hh_pos t ht χ₀ hχ₀ χ, hχ, mul_zero]

/-- Equivalent center cutoffs, i.e. cutoffs with the same integral, give the
same real-axis two-point `ξ`-shift witness value. This is the clean
“depends only on `∫ χ`” form of center collapse in the original `Ψ`
coordinates. -/
theorem schwinger_twoPoint_xiShiftWitness_eq_of_centerIntegral_eq_of_positiveSupport
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (t : ℝ) (ht : 0 < t)
    (χ₀ χ₁ : SchwartzSpacetime d)
    (hint : ∫ u : SpacetimeDim d, χ₀ u = ∫ u : SpacetimeDim d, χ₁ u) :
    (∫ y : NPointDomain d 2,
        Ψ (xiShift ⟨1, by omega⟩ 0
          (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
          ((t : ℂ) * Complex.I)) *
          (χ₀ (y 0) * h (y 1))) =
      ∫ y : NPointDomain d 2,
        Ψ (xiShift ⟨1, by omega⟩ 0
          (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
          ((t : ℂ) * Complex.I)) *
          (χ₁ (y 0) * h (y 1)) := by
  obtain ⟨c, hc⟩ :=
    schwinger_twoPoint_xiShiftWitness_exists_const_of_positiveSupport
      (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid) h hh_pos t ht
  calc
    ∫ y : NPointDomain d 2,
        Ψ (xiShift ⟨1, by omega⟩ 0
          (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
          ((t : ℂ) * Complex.I)) *
          (χ₀ (y 0) * h (y 1))
      = c * ∫ u : SpacetimeDim d, χ₀ u := hc χ₀
    _ = c * ∫ u : SpacetimeDim d, χ₁ u := by rw [hint]
    _ = ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ₁ (y 0) * h (y 1)) := by
          rw [hc χ₁]

/-- Direct normalized-center formula for the positive-time shifted Schwinger
two-point family. Fixing one center cutoff with integral `1` identifies the
entire admissible real-axis family as a single normalized `ξ`-shift witness
value times `∫ χ`. -/
theorem schwinger_twoPointDifferenceLift_timeShift_eq_centerValue_of_positiveSupport
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (t : ℝ) (ht : 0 < t)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (χ : SchwartzSpacetime d) :
    OS.S 2
      (ZeroDiagonalSchwartz.ofClassical
        (twoPointDifferenceLift χ
          (SCV.translateSchwartz (- timeShiftVec d t) h))) =
      (∫ y : NPointDomain d 2,
        Ψ (xiShift ⟨1, by omega⟩ 0
          (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
          ((t : ℂ) * Complex.I)) *
          (χ₀ (y 0) * h (y 1))) *
        ∫ u : SpacetimeDim d, χ u := by
  calc
    OS.S 2
        (ZeroDiagonalSchwartz.ofClassical
          (twoPointDifferenceLift χ
            (SCV.translateSchwartz (- timeShiftVec d t) h)))
      = ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ (y 0) * h (y 1)) := by
          exact schwinger_twoPointDifferenceLift_timeShift_eq_xiShift_of_positiveSupport
            (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
            χ h hh_pos t ht
    _ = (∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
          (χ₀ (y 0) * h (y 1))) *
          ∫ u : SpacetimeDim d, χ u := by
          exact schwinger_twoPoint_xiShiftWitness_eq_centerValue_of_positiveSupport
            (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
            h hh_pos t ht χ₀ hχ₀ χ

/-- The concrete `k = 2` fixed-time `xiShift` kernel appearing in the
two-point continuation formulas. -/
def twoPointXiShiftKernel
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (t : ℝ) : NPointDomain d 2 → ℂ :=
  fun z =>
    Ψ (xiShift ⟨1, by omega⟩ 0
      (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
      ((t : ℂ) * Complex.I))

/-- Blocker-facing CLM form of the real-axis `k = 2` shell identity: the
concrete `xiShift` kernel CLM already agrees with the Schwinger functional on
the admissible positive-time difference shell. This is the production stepping
stone for shell agreement in the `E -> R` route. -/
theorem twoPointXiShiftKernelCLM_eq_schwinger_on_differenceShell_of_positiveSupport
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (t : ℝ) (ht : 0 < t)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (χ : SchwartzSpacetime d)
    (hK_meas : MeasureTheory.AEStronglyMeasurable
      (twoPointXiShiftKernel (d := d) Ψ t) MeasureTheory.volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖twoPointXiShiftKernel (d := d) Ψ t x‖ ≤ C_bd * (1 + ‖x‖) ^ N) :
    OSReconstruction.twoPointFlatKernelCLM (twoPointXiShiftKernel (d := d) Ψ t)
        hK_meas C_bd N hC hK_bound
        (OSReconstruction.reindexSchwartzFin (by ring)
          (OSReconstruction.flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d) (twoPointDifferenceLift χ h)))) =
      OS.S 2
        (ZeroDiagonalSchwartz.ofClassical
          (twoPointDifferenceLift χ
            (SCV.translateSchwartz (- timeShiftVec d t) h))) := by
  calc
    OSReconstruction.twoPointFlatKernelCLM (twoPointXiShiftKernel (d := d) Ψ t)
        hK_meas C_bd N hC hK_bound
        (OSReconstruction.reindexSchwartzFin (by ring)
          (OSReconstruction.flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d) (twoPointDifferenceLift χ h))))
      = ∫ z : NPointDomain d 2,
          twoPointXiShiftKernel (d := d) Ψ t z * (χ (z 0) * h (z 1)) := by
            simpa [twoPointXiShiftKernel] using
              twoPointFlatKernelCLM_apply_reindex_flatten
                (d := d) (K := twoPointXiShiftKernel (d := d) Ψ t)
                hK_meas C_bd N hC hK_bound
                (twoPointCenterDiffSchwartzCLM (d := d) (twoPointDifferenceLift χ h))
    _ = (∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (y 0) * h (y 1))) *
          ∫ u : SpacetimeDim d, χ u := by
          exact schwinger_twoPoint_xiShiftWitness_eq_centerValue_of_positiveSupport
            (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
            h hh_pos t ht χ₀ hχ₀ χ
    _ = OS.S 2
          (ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift χ
              (SCV.translateSchwartz (- timeShiftVec d t) h))) := by
          symm
          exact schwinger_twoPointDifferenceLift_timeShift_eq_centerValue_of_positiveSupport
            (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
            h hh_pos t ht χ₀ hχ₀ χ

/-- Zero-mean center cutoffs are annihilated by the positive-time shifted
two-point Schwinger family. This is the `OS.S 2` form of the real-axis
center-slot collapse. -/
theorem schwinger_twoPointDifferenceLift_timeShift_eq_zero_of_centerIntegral_zero_of_positiveSupport
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (t : ℝ) (ht : 0 < t)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (χ : SchwartzSpacetime d)
    (hχ : ∫ u : SpacetimeDim d, χ u = 0) :
    OS.S 2
      (ZeroDiagonalSchwartz.ofClassical
        (twoPointDifferenceLift χ
          (SCV.translateSchwartz (- timeShiftVec d t) h))) = 0 := by
  rw [schwinger_twoPointDifferenceLift_timeShift_eq_centerValue_of_positiveSupport
    (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
    h hh_pos t ht χ₀ hχ₀ χ, hχ, mul_zero]

/-- Once a holomorphic family is known for one normalized center cutoff `χ₀`,
the real-axis center-collapse formulas promote it to every other center cutoff
by simple scalar multiplication by `∫ χ`. This reduces the `k = 2` admissible
shell holomorphic existence problem to a single normalized center test. -/
theorem exists_twoPointDifferenceLift_timeShift_holomorphicValue_of_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (H₀ : ℂ → ℂ)
    (hH₀_holo : DifferentiableOn ℂ H₀ {z : ℂ | 0 < z.re})
    (hH₀_real : ∀ t : ℝ, 0 < t →
      H₀ (t : ℂ) =
        ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (y 0) * h (y 1)))
    (χ : SchwartzSpacetime d) :
    ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
      ∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          OS.S 2
            (ZeroDiagonalSchwartz.ofClassical
              (twoPointDifferenceLift χ
                (SCV.translateSchwartz (- timeShiftVec d t) h))) := by
  let c : ℂ := ∫ u : SpacetimeDim d, χ u
  refine ⟨fun z => c * H₀ z, ?_, ?_⟩
  · exact hH₀_holo.const_mul c
  · intro t ht
    calc
      c * H₀ (t : ℂ)
        = c * ∫ y : NPointDomain d 2,
            Ψ (xiShift ⟨1, by omega⟩ 0
              (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
              ((t : ℂ) * Complex.I)) *
              (χ₀ (y 0) * h (y 1)) := by
              rw [hH₀_real t ht]
      _ = OS.S 2
            (ZeroDiagonalSchwartz.ofClassical
              (twoPointDifferenceLift χ
                (SCV.translateSchwartz (- timeShiftVec d t) h))) := by
              rw [mul_comm]
              symm
              exact schwinger_twoPointDifferenceLift_timeShift_eq_centerValue_of_positiveSupport
                (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
                h hh_pos t ht χ₀ hχ₀ χ

/-- Uniqueness of the holomorphic continuation for the admissible positive-time
two-point center/difference shell. Once the positive-real values are fixed,
there is at most one holomorphic family on the right half-plane. -/
theorem twoPointDifferenceLift_timeShift_holomorphicValue_eq_of_positiveSupport
    (OS : OsterwalderSchraderAxioms d)
    (h : SchwartzSpacetime d)
    (χ : SchwartzSpacetime d)
    (H₀ H₁ : ℂ → ℂ)
    (hH₀_holo : DifferentiableOn ℂ H₀ {z : ℂ | 0 < z.re})
    (hH₁_holo : DifferentiableOn ℂ H₁ {z : ℂ | 0 < z.re})
    (hH₀_real : ∀ t : ℝ, 0 < t →
      H₀ (t : ℂ) =
        OS.S 2
          (ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift χ
              (SCV.translateSchwartz (- timeShiftVec d t) h))))
    (hH₁_real : ∀ t : ℝ, 0 < t →
      H₁ (t : ℂ) =
        OS.S 2
          (ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift χ
              (SCV.translateSchwartz (- timeShiftVec d t) h)))) :
    Set.EqOn H₀ H₁ {z : ℂ | 0 < z.re} := by
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_conv : Convex ℝ U := convex_halfSpace_re_gt (0 : ℝ)
  have hU_conn : IsConnected U := ⟨⟨1, by simp [U]⟩, hU_conv.isPreconnected⟩
  have h_freq : ∃ᶠ z in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ, H₀ z = H₁ z := by
    rw [Filter.Frequently, Filter.Eventually, mem_nhdsWithin]
    rintro ⟨V, hV_open, h1_mem, hV_sub⟩
    obtain ⟨r, hr_pos, hrV⟩ := Metric.isOpen_iff.mp hV_open 1 h1_mem
    let ε : ℝ := min (r / 2) (1 / 2)
    have hε_pos : 0 < ε := by
      dsimp [ε]
      positivity
    have hε_lt_r : ε < r := by
      have hr2 : r / 2 < r := by linarith
      exact lt_of_le_of_lt (by dsimp [ε]; exact min_le_left _ _) hr2
    have hz_in_V : (((1 + ε : ℝ) : ℂ)) ∈ V := by
      apply hrV
      rw [Metric.mem_ball, Complex.dist_eq]
      have hsub : (((1 + ε : ℝ) : ℂ) - 1) = (ε : ℂ) := by
        norm_num
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hε_pos)]
      exact hε_lt_r
    have hz_ne : (((1 + ε : ℝ) : ℂ)) ≠ 1 := by
      intro hz
      have hsub : (((1 + ε : ℝ) : ℂ) - 1) = (ε : ℂ) := by
        norm_num
      have hε_zero : (ε : ℂ) = 0 := by
        simpa [hsub] using sub_eq_zero.mpr hz
      exact hε_pos.ne' (Complex.ofReal_eq_zero.mp hε_zero)
    have hreal_eq : H₀ ((1 + ε : ℝ) : ℂ) = H₁ ((1 + ε : ℝ) : ℂ) := by
      have hpos : 0 < 1 + ε := by linarith
      rw [hH₀_real (1 + ε) hpos, hH₁_real (1 + ε) hpos]
    exact hV_sub ⟨hz_in_V, hz_ne⟩ hreal_eq
  exact identity_theorem_connected hU_open hU_conn H₀ H₁
    hH₀_holo hH₁_holo (1 : ℂ) (by simp [U]) h_freq

/-- Witness-level promotion of a normalized-center holomorphic family on the
admissible two-point center/difference shell. Once one normalized cutoff `χ₀`
with `∫ χ₀ = 1` is handled holomorphically, every other center cutoff `χ` is
recovered by multiplying by `∫ χ`. This is the exact `ξ`-shift witness form of
the `k = 2` reduction, with no `OS.S 2` left in the conclusion. -/
theorem exists_twoPoint_xiShiftWitness_holomorphicValue_of_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (H₀ : ℂ → ℂ)
    (hH₀_holo : DifferentiableOn ℂ H₀ {z : ℂ | 0 < z.re})
    (hH₀_real : ∀ t : ℝ, 0 < t →
      H₀ (t : ℂ) =
        ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (y 0) * h (y 1)))
    (χ : SchwartzSpacetime d) :
    ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
      ∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          ∫ y : NPointDomain d 2,
            Ψ (xiShift ⟨1, by omega⟩ 0
              (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
              ((t : ℂ) * Complex.I)) *
              (χ (y 0) * h (y 1)) := by
  let c : ℂ := ∫ u : SpacetimeDim d, χ u
  refine ⟨fun z => c * H₀ z, hH₀_holo.const_mul c, ?_⟩
  intro t ht
  calc
    c * H₀ (t : ℂ)
      = c * ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (y 0) * h (y 1)) := by
          rw [hH₀_real t ht]
    _ = (∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (y 0) * h (y 1))) *
          ∫ u : SpacetimeDim d, χ u := by
          rw [mul_comm]
    _ = ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ (y 0) * h (y 1)) := by
          symm
          exact schwinger_twoPoint_xiShiftWitness_eq_centerValue_of_positiveSupport
            (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
            h hh_pos t ht χ₀ hχ₀ χ

/-- Any two holomorphic realizations of the normalized-center admissible
two-point `ξ`-shift witness must agree on the whole right half-plane. So once
existence is proved for one normalized center cutoff, the resulting
holomorphic family is canonical and independent of that choice. -/
theorem twoPoint_xiShiftWitness_holomorphicValue_eq_of_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (χ₀ χ₁ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (hχ₁ : ∫ u : SpacetimeDim d, χ₁ u = 1)
    (H₀ H₁ : ℂ → ℂ)
    (hH₀_holo : DifferentiableOn ℂ H₀ {z : ℂ | 0 < z.re})
    (hH₁_holo : DifferentiableOn ℂ H₁ {z : ℂ | 0 < z.re})
    (hH₀_real : ∀ t : ℝ, 0 < t →
      H₀ (t : ℂ) =
        ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (y 0) * h (y 1)))
    (hH₁_real : ∀ t : ℝ, 0 < t →
      H₁ (t : ℂ) =
        ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ₁ (y 0) * h (y 1))) :
    Set.EqOn H₀ H₁ {z : ℂ | 0 < z.re} := by
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_conv : Convex ℝ U := convex_halfSpace_re_gt (0 : ℝ)
  have hU_conn : IsConnected U := ⟨⟨1, by simp [U]⟩, hU_conv.isPreconnected⟩
  have h_freq : ∃ᶠ z in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ, H₀ z = H₁ z := by
    rw [Filter.Frequently, Filter.Eventually, mem_nhdsWithin]
    rintro ⟨V, hV_open, h1_mem, hV_sub⟩
    obtain ⟨r, hr_pos, hrV⟩ := Metric.isOpen_iff.mp hV_open 1 h1_mem
    let ε : ℝ := min (r / 2) (1 / 2)
    have hε_pos : 0 < ε := by
      dsimp [ε]
      positivity
    have hε_lt_r : ε < r := by
      have hr2 : r / 2 < r := by linarith
      exact lt_of_le_of_lt (by dsimp [ε]; exact min_le_left _ _) hr2
    have hz_in_V : (((1 + ε : ℝ) : ℂ)) ∈ V := by
      apply hrV
      rw [Metric.mem_ball, Complex.dist_eq]
      have hsub : (((1 + ε : ℝ) : ℂ) - 1) = (ε : ℂ) := by
        norm_num
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hε_pos)]
      exact hε_lt_r
    have hz_ne : (((1 + ε : ℝ) : ℂ)) ≠ 1 := by
      intro hz
      have hsub : (((1 + ε : ℝ) : ℂ) - 1) = (ε : ℂ) := by
        norm_num
      have hε_zero : (ε : ℂ) = 0 := by
        simpa [hsub] using sub_eq_zero.mpr hz
      exact hε_pos.ne' (Complex.ofReal_eq_zero.mp hε_zero)
    have hreal_eq : H₀ ((1 + ε : ℝ) : ℂ) = H₁ ((1 + ε : ℝ) : ℂ) := by
      have hpos : 0 < 1 + ε := by linarith
      rw [hH₀_real (1 + ε) hpos, hH₁_real (1 + ε) hpos]
      exact schwinger_twoPoint_xiShiftWitness_eq_of_centerIntegral_eq_of_positiveSupport
        (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
        h hh_pos (1 + ε) hpos χ₀ χ₁ (by simp [hχ₀, hχ₁])
    exact hV_sub ⟨hz_in_V, hz_ne⟩ hreal_eq
  exact identity_theorem_connected hU_open hU_conn H₀ H₁
    hH₀_holo hH₁_holo (1 : ℂ) (by simp [U]) h_freq

omit [NeZero d] in
/-- Uniqueness of the holomorphic continuation on the admissible positive-time
two-point `ξ`-shift witness shell. Once the positive-real witness values are
fixed for one center cutoff `χ`, the holomorphic family on the right half-plane
is unique. -/
theorem twoPoint_xiShiftWitness_holomorphicValue_eq_of_positiveSupport
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (h : SchwartzSpacetime d)
    (χ : SchwartzSpacetime d)
    (H₀ H₁ : ℂ → ℂ)
    (hH₀_holo : DifferentiableOn ℂ H₀ {z : ℂ | 0 < z.re})
    (hH₁_holo : DifferentiableOn ℂ H₁ {z : ℂ | 0 < z.re})
    (hH₀_real : ∀ t : ℝ, 0 < t →
      H₀ (t : ℂ) =
        ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ (y 0) * h (y 1)))
    (hH₁_real : ∀ t : ℝ, 0 < t →
      H₁ (t : ℂ) =
        ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ (y 0) * h (y 1))) :
    Set.EqOn H₀ H₁ {z : ℂ | 0 < z.re} := by
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_conv : Convex ℝ U := convex_halfSpace_re_gt (0 : ℝ)
  have hU_conn : IsConnected U := ⟨⟨1, by simp [U]⟩, hU_conv.isPreconnected⟩
  have h_freq : ∃ᶠ z in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ, H₀ z = H₁ z := by
    rw [Filter.Frequently, Filter.Eventually, mem_nhdsWithin]
    rintro ⟨V, hV_open, h1_mem, hV_sub⟩
    obtain ⟨r, hr_pos, hrV⟩ := Metric.isOpen_iff.mp hV_open 1 h1_mem
    let ε : ℝ := min (r / 2) (1 / 2)
    have hε_pos : 0 < ε := by
      dsimp [ε]
      positivity
    have hε_lt_r : ε < r := by
      have hr2 : r / 2 < r := by linarith
      exact lt_of_le_of_lt (by dsimp [ε]; exact min_le_left _ _) hr2
    have hz_in_V : (((1 + ε : ℝ) : ℂ)) ∈ V := by
      apply hrV
      rw [Metric.mem_ball, Complex.dist_eq]
      have hsub : (((1 + ε : ℝ) : ℂ) - 1) = (ε : ℂ) := by
        norm_num
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hε_pos)]
      exact hε_lt_r
    have hz_ne : (((1 + ε : ℝ) : ℂ)) ≠ 1 := by
      intro hz
      have hsub : (((1 + ε : ℝ) : ℂ) - 1) = (ε : ℂ) := by
        norm_num
      have hε_zero : (ε : ℂ) = 0 := by
        simpa [hsub] using sub_eq_zero.mpr hz
      exact hε_pos.ne' (Complex.ofReal_eq_zero.mp hε_zero)
    have hreal_eq : H₀ ((1 + ε : ℝ) : ℂ) = H₁ ((1 + ε : ℝ) : ℂ) := by
      have hpos : 0 < 1 + ε := by linarith
      rw [hH₀_real (1 + ε) hpos, hH₁_real (1 + ε) hpos]
    exact hV_sub ⟨hz_in_V, hz_ne⟩ hreal_eq
  exact identity_theorem_connected hU_open hU_conn H₀ H₁
    hH₀_holo hH₁_holo (1 : ℂ) (by simp [U]) h_freq

/-- Exact witness-level `k = 2` reduction on the admissible positive-time
    center/difference shell. For a fixed normalized center cutoff `χ₀`,
    constructing one holomorphic `ξ`-shift witness family for `χ₀` is
    equivalent to constructing, for every center cutoff `χ`, the canonical
    holomorphic witness family, unique on the right half-plane. -/
theorem exists_twoPoint_xiShiftWitness_holomorphicValue_iff_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1) :
    (∃ H₀ : ℂ → ℂ,
      DifferentiableOn ℂ H₀ {z : ℂ | 0 < z.re} ∧
      (∀ t : ℝ, 0 < t →
        H₀ (t : ℂ) =
          ∫ y : NPointDomain d 2,
            Ψ (xiShift ⟨1, by omega⟩ 0
              (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
              ((t : ℂ) * Complex.I)) *
              (χ₀ (y 0) * h (y 1)))) ↔
    (∀ χ : SchwartzSpacetime d,
      ∃ H : ℂ → ℂ,
        DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
        (∀ t : ℝ, 0 < t →
          H (t : ℂ) =
            ∫ y : NPointDomain d 2,
              Ψ (xiShift ⟨1, by omega⟩ 0
                (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
                ((t : ℂ) * Complex.I)) *
                (χ (y 0) * h (y 1))) ∧
        ∀ H' : ℂ → ℂ,
          DifferentiableOn ℂ H' {z : ℂ | 0 < z.re} →
          (∀ t : ℝ, 0 < t →
            H' (t : ℂ) =
              ∫ y : NPointDomain d 2,
                Ψ (xiShift ⟨1, by omega⟩ 0
                  (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
                  ((t : ℂ) * Complex.I)) *
                  (χ (y 0) * h (y 1))) →
          Set.EqOn H H' {z : ℂ | 0 < z.re}) := by
  constructor
  · intro hcenter χ
    rcases hcenter with ⟨H₀, hH₀_holo, hH₀_real⟩
    rcases exists_twoPoint_xiShiftWitness_holomorphicValue_of_centerValue
        (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
        h hh_pos χ₀ hχ₀ H₀ hH₀_holo hH₀_real χ with ⟨H, hH_holo, hH_real⟩
    refine ⟨H, hH_holo, hH_real, ?_⟩
    intro H' hH'_holo hH'_real
    have hH_os : ∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          OS.S 2
            (ZeroDiagonalSchwartz.ofClassical
              (twoPointDifferenceLift χ
                (SCV.translateSchwartz (- timeShiftVec d t) h))) := by
      intro t ht
      rw [hH_real t ht]
      exact (schwinger_twoPointDifferenceLift_timeShift_eq_xiShift_of_positiveSupport
        (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
        χ h hh_pos t ht).symm
    have hH'_os : ∀ t : ℝ, 0 < t →
        H' (t : ℂ) =
          OS.S 2
            (ZeroDiagonalSchwartz.ofClassical
              (twoPointDifferenceLift χ
                (SCV.translateSchwartz (- timeShiftVec d t) h))) := by
      intro t ht
      rw [hH'_real t ht]
      exact (schwinger_twoPointDifferenceLift_timeShift_eq_xiShift_of_positiveSupport
        (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
        χ h hh_pos t ht).symm
    exact twoPointDifferenceLift_timeShift_holomorphicValue_eq_of_positiveSupport
      (d := d) (OS := OS) h χ H H' hH_holo hH'_holo hH_os hH'_os
  · intro hall
    rcases hall χ₀ with ⟨H₀, hH₀_holo, hH₀_real, _huniq⟩
    exact ⟨H₀, hH₀_holo, hH₀_real⟩

/-- Canonical holomorphic continuation on the admissible positive-time
two-point center/difference shell. Once one normalized center cutoff `χ₀`
produces a holomorphic family, every center cutoff `χ` gets a holomorphic
continuation, and any two such continuations agree on the right half-plane. -/
theorem exists_twoPointDifferenceLift_timeShift_holomorphicValue_of_centerValue_unique
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (H₀ : ℂ → ℂ)
    (hH₀_holo : DifferentiableOn ℂ H₀ {z : ℂ | 0 < z.re})
    (hH₀_real : ∀ t : ℝ, 0 < t →
      H₀ (t : ℂ) =
        ∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (y 0) * h (y 1)))
    (χ : SchwartzSpacetime d) :
    ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
      (∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          OS.S 2
            (ZeroDiagonalSchwartz.ofClassical
              (twoPointDifferenceLift χ
                (SCV.translateSchwartz (- timeShiftVec d t) h)))) ∧
      ∀ H' : ℂ → ℂ,
        DifferentiableOn ℂ H' {z : ℂ | 0 < z.re} →
        (∀ t : ℝ, 0 < t →
          H' (t : ℂ) =
            OS.S 2
              (ZeroDiagonalSchwartz.ofClassical
                (twoPointDifferenceLift χ
                  (SCV.translateSchwartz (- timeShiftVec d t) h)))) →
        Set.EqOn H H' {z : ℂ | 0 < z.re} := by
  rcases exists_twoPointDifferenceLift_timeShift_holomorphicValue_of_centerValue
      (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
      h hh_pos χ₀ hχ₀ H₀ hH₀_holo hH₀_real χ with ⟨H, hH_holo, hH_real⟩
  refine ⟨H, hH_holo, hH_real, ?_⟩
  intro H' hH'_holo hH'_real
  exact twoPointDifferenceLift_timeShift_holomorphicValue_eq_of_positiveSupport
    (d := d) (OS := OS) h χ H H' hH_holo hH'_holo hH_real hH'_real

/-- Exact `k = 2` reduction theorem on the admissible positive-time shell.
    For a fixed normalized center cutoff `χ₀`, constructing one holomorphic
    family for that single cutoff is equivalent to constructing, for every
    center cutoff `χ`, the canonical holomorphic continuation on the right
    half-plane. This isolates the remaining two-point `E -> R` gap precisely:
    only the normalized-center existence problem is still open. -/
theorem exists_twoPointDifferenceLift_timeShift_holomorphicValue_iff_centerValue
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1) :
    (∃ H₀ : ℂ → ℂ,
      DifferentiableOn ℂ H₀ {z : ℂ | 0 < z.re} ∧
      (∀ t : ℝ, 0 < t →
        H₀ (t : ℂ) =
          ∫ y : NPointDomain d 2,
            Ψ (xiShift ⟨1, by omega⟩ 0
              (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
              ((t : ℂ) * Complex.I)) *
              (χ₀ (y 0) * h (y 1)))) ↔
    (∀ χ : SchwartzSpacetime d,
      ∃ H : ℂ → ℂ,
        DifferentiableOn ℂ H {z : ℂ | 0 < z.re} ∧
        (∀ t : ℝ, 0 < t →
          H (t : ℂ) =
            OS.S 2
              (ZeroDiagonalSchwartz.ofClassical
                (twoPointDifferenceLift χ
                  (SCV.translateSchwartz (- timeShiftVec d t) h)))) ∧
        ∀ H' : ℂ → ℂ,
          DifferentiableOn ℂ H' {z : ℂ | 0 < z.re} →
          (∀ t : ℝ, 0 < t →
            H' (t : ℂ) =
              OS.S 2
                (ZeroDiagonalSchwartz.ofClassical
                  (twoPointDifferenceLift χ
                    (SCV.translateSchwartz (- timeShiftVec d t) h)))) →
          Set.EqOn H H' {z : ℂ | 0 < z.re}) := by
  constructor
  · intro hcenter χ
    rcases hcenter with ⟨H₀, hH₀_holo, hH₀_real⟩
    exact exists_twoPointDifferenceLift_timeShift_holomorphicValue_of_centerValue_unique
      (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
      h hh_pos χ₀ hχ₀ H₀ hH₀_holo hH₀_real χ
  · intro hall
    rcases hall χ₀ with ⟨H₀, hH₀_holo, hH₀_real, _huniq⟩
    refine ⟨H₀, hH₀_holo, ?_⟩
    intro t ht
    rw [hH₀_real t ht]
    exact schwinger_twoPointDifferenceLift_timeShift_eq_xiShift_of_positiveSupport
      (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
      χ₀ h hh_pos t ht
