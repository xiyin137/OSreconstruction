import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTransform
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValuesBase

noncomputable section

open scoped Topology FourierTransform
open Set MeasureTheory

namespace OSReconstruction

theorem bvt_W_eq_of_section43FrequencyProjection_eq
    (d : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {N : ℕ}
    (φ ψ : SchwartzNPoint d N)
    (Tflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_supp :
      HasFourierSupportInDualCone
        ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N) Tflat)
    (hTflat_bv :
      ∀ φflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ,
        bvt_W OS lgc N (unflattenSchwartzNPoint (d := d) φflat) =
          Tflat (physicsFourierFlatCLM φflat))
    (hproj :
      section43FrequencyProjection d N φ =
        section43FrequencyProjection d N ψ) :
    bvt_W OS lgc N φ = bvt_W OS lgc N ψ := by
  have hEqDual :=
    physicsFourierFlat_eqOn_dualCone_of_section43FrequencyProjection_eq
      (d := d) (N := N) φ ψ hproj
  have hφ_flat :
      unflattenSchwartzNPoint (d := d)
          (flattenSchwartzNPoint (d := d) φ) = φ := by
    ext x
    simp [unflattenSchwartzNPoint_apply, flattenSchwartzNPoint_apply]
  have hψ_flat :
      unflattenSchwartzNPoint (d := d)
          (flattenSchwartzNPoint (d := d) ψ) = ψ := by
    ext x
    simp [unflattenSchwartzNPoint_apply, flattenSchwartzNPoint_apply]
  calc
    bvt_W OS lgc N φ
        = bvt_W OS lgc N
            (unflattenSchwartzNPoint (d := d)
              (flattenSchwartzNPoint (d := d) φ)) := by
          rw [hφ_flat]
    _ = Tflat (physicsFourierFlatCLM (flattenSchwartzNPoint (d := d) φ)) := by
          simpa using hTflat_bv (flattenSchwartzNPoint (d := d) φ)
    _ = Tflat (physicsFourierFlatCLM (flattenSchwartzNPoint (d := d) ψ)) := by
          exact tflat_pairing_eq_of_eqOn_dualCone
            (S := (flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N)
            Tflat hTflat_supp
            (physicsFourierFlatCLM (flattenSchwartzNPoint (d := d) φ))
            (physicsFourierFlatCLM (flattenSchwartzNPoint (d := d) ψ))
            hEqDual
    _ = bvt_W OS lgc N
            (unflattenSchwartzNPoint (d := d)
              (flattenSchwartzNPoint (d := d) ψ)) := by
          simpa using (hTflat_bv (flattenSchwartzNPoint (d := d) ψ)).symm
    _ = bvt_W OS lgc N ψ := by
          rw [hψ_flat]

end OSReconstruction
