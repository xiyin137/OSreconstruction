/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorSpatialHermite
import OSReconstruction.SCV.DistributionalEOWApproxIdentity















noncomputable section

open Complex
open MeasureTheory
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- A Schwartz cutoff in the absolute spatial basepoint, normalized to have
integral one. This is the spatial analogue of `BHW.NormalizedBasepointCutoff`;
it is stated directly on `Fin d → ℝ`, so it remains available when `d = 1`. -/
structure NormalizedSpatialBasepointCutoff (d : ℕ) where
  toSchwartz : SchwartzMap (Fin d → ℝ) ℂ
  integral_eq_one : ∫ x : Fin d → ℝ, toSchwartz x = 1

instance : Coe (NormalizedSpatialBasepointCutoff d)
    (SchwartzMap (Fin d → ℝ) ℂ) where
  coe ρ := ρ.toSchwartz

/-- A canonical compactly supported normalized spatial basepoint cutoff. -/
noncomputable def normalizedSpatialBasepointCutoff (d : ℕ) :
    NormalizedSpatialBasepointCutoff d := by
  let h :=
    SCV.exists_normalized_schwartz_bump_kernelSupportWithin
      (m := d) 1 (by norm_num)
  exact ⟨Classical.choose h, (Classical.choose_spec h).2.2.1⟩

noncomputable def section43SpatialSchwartzParticleCLE (d k : ℕ) :
    SchwartzMap (Section43SpatialSpace d k) ℂ ≃L[ℂ]
      SchwartzMap (Fin k → Fin d → ℝ) ℂ := by
  let e := section43SpatialParticleCLE d k
  let toFwd :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Fin k → Fin d → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm
  let toInv :
      SchwartzMap (Fin k → Fin d → ℝ) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d k) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
  exact
    { toLinearEquiv :=
        { toFun := toFwd
          map_add' := toFwd.map_add
          map_smul' := toFwd.map_smul
          invFun := toInv
          left_inv := by
            intro f
            ext η
            simp [toFwd, toInv, e,
              SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
          right_inv := by
            intro f
            ext x
            simp [toFwd, toInv, e,
              SchwartzMap.compCLMOfContinuousLinearEquiv_apply] }
      continuous_toFun := toFwd.continuous
      continuous_invFun := toInv.continuous }

@[simp]
theorem section43SpatialSchwartzParticleCLE_symm_apply
    (d k : ℕ)
    (f : SchwartzMap (Fin k → Fin d → ℝ) ℂ)
    (η : Section43SpatialSpace d k) :
    (section43SpatialSchwartzParticleCLE d k).symm f η =
      f (section43SpatialParticleCLE d k η) := by
  rfl

@[simp]
theorem section43SpatialSchwartzParticleCLE_apply
    (d k : ℕ)
    (f : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (x : Fin k → Fin d → ℝ) :
    section43SpatialSchwartzParticleCLE d k f x =
      f ((section43SpatialParticleCLE d k).symm x) := by
  rfl

end OSIIChapterV
end OSReconstruction
