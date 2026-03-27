import OSReconstruction.Wightman.Reconstruction.TwoPointKernelFunctional
import OSReconstruction.Wightman.Reconstruction.DenseCLM

noncomputable section

open Complex MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Fixed-time bridge: once a flattened CLM agrees with a fixed-time kernel on
all two-point difference shells, the same CLM automatically has the expected
product-shell and difference-shell formulas. This is the non-deprecated version
of the root-facing comparison lemma from the older kernel route. -/
theorem map_productLift_and_differenceLift_of_eq_on_twoPointDifferenceShell_fixedTime
    (T : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (t : ℂ)
    (hK_meas : AEStronglyMeasurable
      (twoPointFixedTimeKernel (d := d) G t) volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖twoPointFixedTimeKernel (d := d) G t x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    (hEq : ∀ χ h : SchwartzSpacetime d,
      T (reindexSchwartzFin (by ring)
            (flattenSchwartzNPoint (d := d)
              (twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointDifferenceLift χ h)))) =
        ∫ z : NPointDomain d 2,
          twoPointFixedTimeKernel (d := d) G t z *
            (χ (z 0) * h (z 1)))
    (χ g h : SchwartzSpacetime d) :
    T (reindexSchwartzFin (by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d)
              (twoPointProductLift χ g)))) =
        ∫ z : NPointDomain d 2,
          twoPointFixedTimeKernel (d := d) G t z *
            (χ (z 0) * g (z 0 + z 1)) ∧
      T (reindexSchwartzFin (by ring)
          (flattenSchwartzNPoint (d := d)
            (twoPointCenterDiffSchwartzCLM (d := d)
              (twoPointDifferenceLift χ h)))) =
        ∫ z : NPointDomain d 2,
          twoPointFixedTimeKernel (d := d) G t z *
            (χ (z 0) * h (z 1)) := by
  let TK : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ :=
    twoPointFlatKernelCLM (d := d)
      (twoPointFixedTimeKernel (d := d) G t)
      hK_meas C_bd N hC hK_bound
  have hShell :
      ∀ χ h : SchwartzSpacetime d,
        T (reindexSchwartzFin (by ring)
              (flattenSchwartzNPoint (d := d)
                (twoPointCenterDiffSchwartzCLM (d := d)
                  (twoPointDifferenceLift χ h)))) =
          TK (reindexSchwartzFin (by ring)
              (flattenSchwartzNPoint (d := d)
                (twoPointCenterDiffSchwartzCLM (d := d)
                  (twoPointDifferenceLift χ h)))) := by
    intro χ h
    rw [hEq χ h]
    simpa [TK] using
      (twoPointFixedTimeKernelCLM_apply_differenceLift
        (d := d) G t hK_meas C_bd N hC hK_bound χ h).symm
  have hT_eq : T = TK :=
    flattened_clm_eq_of_eq_on_twoPointDifferenceShell (d := d) T TK hShell
  constructor
  · calc
      T (reindexSchwartzFin (by ring)
            (flattenSchwartzNPoint (d := d)
              (twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointProductLift χ g)))) =
          TK (reindexSchwartzFin (by ring)
            (flattenSchwartzNPoint (d := d)
              (twoPointCenterDiffSchwartzCLM (d := d)
                (twoPointProductLift χ g)))) := by
              simpa [TK] using congrArg
                (fun L : SchwartzMap (Fin ((d + 1) + (d + 1)) → ℝ) ℂ →L[ℂ] ℂ =>
                  L (reindexSchwartzFin (by ring)
                    (flattenSchwartzNPoint (d := d)
                      (twoPointCenterDiffSchwartzCLM (d := d)
                        (twoPointProductLift χ g))))) hT_eq
      _ = ∫ z : NPointDomain d 2,
            twoPointFixedTimeKernel (d := d) G t z *
              (χ (z 0) * g (z 0 + z 1)) := by
            simpa [TK] using
              twoPointFixedTimeKernelCLM_apply_productLift
                (d := d) G t hK_meas C_bd N hC hK_bound χ g
  · exact hEq χ h

end OSReconstruction
