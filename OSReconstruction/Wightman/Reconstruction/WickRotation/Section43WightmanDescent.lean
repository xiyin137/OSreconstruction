import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTransform
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43SpectralSupport
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValues
import OSReconstruction.Wightman.Reconstruction.SchwartzDensity

noncomputable section

open scoped Topology FourierTransform LineDeriv
open Set MeasureTheory

namespace OSReconstruction

theorem unflattenSchwartzNPoint_translate_section43DiagonalTranslationFlat
    (d N : ℕ) [NeZero d]
    (a : Fin (d + 1) → ℝ)
    (φflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ)
    (x : NPointDomain d N) :
    unflattenSchwartzNPoint (d := d)
        (SCV.translateSchwartz (section43DiagonalTranslationFlat d N a) φflat) x =
      (unflattenSchwartzNPoint (d := d) φflat) (fun i => x i + a) := by
  rw [unflattenSchwartzNPoint_apply, SCV.translateSchwartz_apply,
    unflattenSchwartzNPoint_apply]
  congr 1

theorem bvt_W_flat_diagonalTranslate_eq
    (d : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {N : ℕ}
    (a : Fin (d + 1) → ℝ)
    (φflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ) :
    bvt_W OS lgc N
        (unflattenSchwartzNPoint (d := d)
          (SCV.translateSchwartz (section43DiagonalTranslationFlat d N a) φflat)) =
      bvt_W OS lgc N (unflattenSchwartzNPoint (d := d) φflat) := by
  let f : SchwartzNPoint d N := unflattenSchwartzNPoint (d := d) φflat
  let g : SchwartzNPoint d N :=
    unflattenSchwartzNPoint (d := d)
      (SCV.translateSchwartz (section43DiagonalTranslationFlat d N a) φflat)
  have hfg : ∀ x : NPointDomain d N, g.toFun x = f.toFun (fun i => x i + a) := by
    intro x
    exact unflattenSchwartzNPoint_translate_section43DiagonalTranslationFlat
      (d := d) (N := N) a φflat x
  have h := bvt_translation_invariant (d := d) OS lgc N a f g hfg
  simpa [f, g] using h.symm

theorem tflat_totalMomentumPhase_invariant_of_bvt_W_translationInvariant
    (d : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {N : ℕ}
    (Tflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_bv :
      ∀ φflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ,
        bvt_W OS lgc N (unflattenSchwartzNPoint (d := d) φflat) =
          Tflat (physicsFourierFlatCLM φflat)) :
    ∀ (a : Fin (d + 1) → ℝ)
      (K : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ),
      Tflat (section43TotalMomentumPhaseCLM d N a K) = Tflat K := by
  intro a K
  obtain ⟨φflat, hφflat⟩ := physicsFourierFlatCLM_surjective (N * (d + 1)) K
  rw [← hφflat]
  calc
    Tflat (section43TotalMomentumPhaseCLM d N a (physicsFourierFlatCLM φflat))
        = Tflat (physicsFourierFlatCLM
            (SCV.translateSchwartz (section43DiagonalTranslationFlat d N a) φflat)) := by
          rw [← physicsFourierFlatCLM_diagonalTranslate_eq_phaseCLM]
    _ = bvt_W OS lgc N
            (unflattenSchwartzNPoint (d := d)
              (SCV.translateSchwartz (section43DiagonalTranslationFlat d N a) φflat)) := by
          rw [← hTflat_bv]
    _ = bvt_W OS lgc N (unflattenSchwartzNPoint (d := d) φflat) := by
          exact bvt_W_flat_diagonalTranslate_eq (d := d) OS lgc a φflat
    _ = Tflat (physicsFourierFlatCLM φflat) := by
          rw [hTflat_bv]

theorem hasFourierSupportIn_wightmanSpectralRegion_of_bvt_W_translationInvariant
    (d : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {N : ℕ}
    (Tflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hdual :
      HasFourierSupportInDualCone
        ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N) Tflat)
    (hTflat_bv :
      ∀ φflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ,
        bvt_W OS lgc N (unflattenSchwartzNPoint (d := d) φflat) =
          Tflat (physicsFourierFlatCLM φflat)) :
    HasFourierSupportIn (section43WightmanSpectralRegion d N) Tflat := by
  have hphase :=
    tflat_totalMomentumPhase_invariant_of_bvt_W_translationInvariant
      (d := d) OS lgc Tflat hTflat_bv
  have htotal :=
    hasFourierSupportIn_totalMomentumZero_of_phase_invariant d Tflat hphase
  exact hasFourierSupportIn_inter_of_dualCone_and_totalMomentumZero d N hdual htotal

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
