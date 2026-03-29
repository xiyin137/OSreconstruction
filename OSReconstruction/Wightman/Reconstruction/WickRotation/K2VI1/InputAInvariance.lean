import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAXiShift

noncomputable section

open Complex MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- The concrete fixed-time `xiShift` kernel functional is translation-invariant
on admissible difference shells. This is the direct `E1` payoff behind the
Input A center-slot invariance route. -/
theorem twoPointXiShiftKernelCLM_translation_invariant_on_differenceShell_of_positiveSupport_local
    (OS : OsterwalderSchraderAxioms d)
    (Ψ : (Fin 2 → Fin (d + 1) → ℂ) → ℂ)
    (hΨ_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        Ψ (fun i => wickRotatePoint (x i)) * (f.1 x))
    (h : SchwartzSpacetime d)
    (hh_pos : tsupport (h : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0})
    (t : ℝ) (ht : 0 < t)
    (χ : SchwartzSpacetime d)
    (a : SpacetimeDim d)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (hK_meas : MeasureTheory.AEStronglyMeasurable
      (twoPointXiShiftKernel_local (d := d) Ψ t) MeasureTheory.volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖twoPointXiShiftKernel_local (d := d) Ψ t x‖ ≤ C_bd * (1 + ‖x‖) ^ N) :
    OSReconstruction.twoPointFlatKernelCLM (twoPointXiShiftKernel_local (d := d) Ψ t)
        hK_meas C_bd N hC hK_bound
        (OSReconstruction.reindexSchwartzFin (by ring)
          (OSReconstruction.flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d)
              (twoPointDifferenceLift (SCV.translateSchwartz a χ) h)))) =
      OSReconstruction.twoPointFlatKernelCLM (twoPointXiShiftKernel_local (d := d) Ψ t)
        hK_meas C_bd N hC hK_bound
        (OSReconstruction.reindexSchwartzFin (by ring)
          (OSReconstruction.flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d)
              (twoPointDifferenceLift χ h)))) := by
  have hshift0 :
      (0 : SpacetimeDim d) ∉ tsupport
        (((SCV.translateSchwartz (- timeShiftVec d t) h : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ)) := by
    refine zero_not_mem_tsupport_translate_of_notMem (d := d) h (- timeShiftVec d t) ?_
    exact neg_timeShiftVec_not_mem_positive_tsupport (d := d) h hh_pos t ht
  calc
    OSReconstruction.twoPointFlatKernelCLM (twoPointXiShiftKernel_local (d := d) Ψ t)
        hK_meas C_bd N hC hK_bound
        (OSReconstruction.reindexSchwartzFin (by ring)
          (OSReconstruction.flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d)
              (twoPointDifferenceLift (SCV.translateSchwartz a χ) h))))
      = OS.S 2
          (ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift (SCV.translateSchwartz a χ)
              (SCV.translateSchwartz (- timeShiftVec d t) h))) := by
            exact twoPointXiShiftKernelCLM_eq_schwinger_on_differenceShell_of_positiveSupport_local
              (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
              h hh_pos t ht χ₀ hχ₀ (SCV.translateSchwartz a χ)
              hK_meas C_bd N hC hK_bound
    _ = OS.S 2
          (ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift χ
              (SCV.translateSchwartz (- timeShiftVec d t) h))) := by
            simpa using
              (OsterwalderSchraderAxioms.schwinger_twoPointDifferenceLift_translation_invariant
                (d := d) (OS := OS) (a := a) (χ := χ)
                (h := SCV.translateSchwartz (- timeShiftVec d t) h) hshift0).symm
    _ = OSReconstruction.twoPointFlatKernelCLM (twoPointXiShiftKernel_local (d := d) Ψ t)
          hK_meas C_bd N hC hK_bound
          (OSReconstruction.reindexSchwartzFin (by ring)
            (OSReconstruction.flattenSchwartzNPoint (d := d)
              (twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointDifferenceLift χ h)))) := by
          exact
            (twoPointXiShiftKernelCLM_eq_schwinger_on_differenceShell_of_positiveSupport_local
              (d := d) (OS := OS) (Ψ := Ψ) (hΨ_euclid := hΨ_euclid)
              h hh_pos t ht χ₀ hχ₀ χ hK_meas C_bd N hC hK_bound).symm

end OSReconstruction
