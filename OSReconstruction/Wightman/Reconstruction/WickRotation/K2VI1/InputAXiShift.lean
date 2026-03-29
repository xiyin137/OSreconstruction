import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAFlatUpdate

noncomputable section

open Complex MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

private theorem twoPointCenterDiff_toDiffFlat_wickRotate_inputA_local
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

/-- The fixed-time flat-update witness may be rewritten in the original
`xiShift` witness coordinates on the center/difference shell. -/
theorem schwinger_twoPointDifferenceLift_timeShift_eq_xiShift_of_positiveSupport_local
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
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
        exact schwinger_twoPointDifferenceLift_timeShift_eq_flatUpdate_of_positiveSupport_local
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
            rw [← twoPointCenterDiff_toDiffFlat_wickRotate_inputA_local (d := d) y]
            simp [BHW.fromDiffFlat_toDiffFlat]
          simpa [twoPointCenterDiff_toDiffFlat_wickRotate_inputA_local (d := d) y, hcfg,
            sub_eq_add_neg]
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

/-- Real-axis center collapse in the original `xiShift` witness coordinates. -/
theorem schwinger_twoPoint_xiShiftWitness_exists_const_of_positiveSupport_local
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
          exact schwinger_twoPointDifferenceLift_timeShift_eq_xiShift_of_positiveSupport_local
            (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
            χ h hh_pos t ht
    _ = c * ∫ u : SpacetimeDim d, χ u := hc χ

/-- Normalized center-value form of the fixed-time `xiShift` witness. -/
theorem schwinger_twoPoint_xiShiftWitness_eq_centerValue_of_positiveSupport_local
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
    schwinger_twoPoint_xiShiftWitness_exists_const_of_positiveSupport_local
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

/-- The concrete fixed-time `xiShift` kernel attached to a witness `Ψ`. -/
def twoPointXiShiftKernel_local
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (t : ℝ) : NPointDomain d 2 → ℂ :=
  fun z =>
    Ψ (xiShift ⟨1, by omega⟩ 0
      (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))
      ((t : ℂ) * Complex.I))

/-- CLM form of the fixed-time `xiShift` witness identity on positive-support
difference shells. This makes the concrete fixed-time kernel available as a
production object for the next Input A descent step. -/
theorem twoPointXiShiftKernelCLM_eq_schwinger_on_differenceShell_of_positiveSupport_local
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
      (twoPointXiShiftKernel_local (d := d) Ψ t) MeasureTheory.volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖twoPointXiShiftKernel_local (d := d) Ψ t x‖ ≤ C_bd * (1 + ‖x‖) ^ N) :
    OSReconstruction.twoPointFlatKernelCLM (twoPointXiShiftKernel_local (d := d) Ψ t)
        hK_meas C_bd N hC hK_bound
        (OSReconstruction.reindexSchwartzFin (by ring)
          (OSReconstruction.flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d) (twoPointDifferenceLift χ h)))) =
      OS.S 2
        (ZeroDiagonalSchwartz.ofClassical
          (twoPointDifferenceLift χ
            (SCV.translateSchwartz (- timeShiftVec d t) h))) := by
  calc
    OSReconstruction.twoPointFlatKernelCLM (twoPointXiShiftKernel_local (d := d) Ψ t)
        hK_meas C_bd N hC hK_bound
        (OSReconstruction.reindexSchwartzFin (by ring)
          (OSReconstruction.flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d) (twoPointDifferenceLift χ h))))
      = ∫ z : NPointDomain d 2,
          twoPointXiShiftKernel_local (d := d) Ψ t z * (χ (z 0) * h (z 1)) := by
            simpa [twoPointXiShiftKernel_local] using
              twoPointFlatKernelCLM_apply_reindex_flatten
                (d := d) (K := twoPointXiShiftKernel_local (d := d) Ψ t)
                hK_meas C_bd N hC hK_bound
                (twoPointCenterDiffSchwartzCLM (d := d) (twoPointDifferenceLift χ h))
    _ = (∫ y : NPointDomain d 2,
          Ψ (xiShift ⟨1, by omega⟩ 0
            (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
            ((t : ℂ) * Complex.I)) *
            (χ₀ (y 0) * h (y 1))) *
          ∫ u : SpacetimeDim d, χ u := by
          exact schwinger_twoPoint_xiShiftWitness_eq_centerValue_of_positiveSupport_local
            (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
            h hh_pos t ht χ₀ hχ₀ χ
    _ = OS.S 2
          (ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift χ
              (SCV.translateSchwartz (- timeShiftVec d t) h))) := by
          symm
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
                      exact schwinger_twoPointDifferenceLift_timeShift_eq_xiShift_of_positiveSupport_local
                        (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
                        χ h hh_pos t ht
            _ = (∫ y : NPointDomain d 2,
                  Ψ (xiShift ⟨1, by omega⟩ 0
                    (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) y) i))
                    ((t : ℂ) * Complex.I)) *
                    (χ₀ (y 0) * h (y 1))) *
                  ∫ u : SpacetimeDim d, χ u := by
                    exact schwinger_twoPoint_xiShiftWitness_eq_centerValue_of_positiveSupport_local
                      (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
                      h hh_pos t ht χ₀ hχ₀ χ

end OSReconstruction
