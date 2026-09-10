/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.DistributionalEOWKernel
import OSReconstruction.SCV.HeadBlockDescent










noncomputable section

open Complex MeasureTheory

namespace SCV

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

@[simp]
theorem compCLMOfContinuousLinearEquiv_symm_left_inv
    (e : E ≃L[ℝ] F) (f : SchwartzMap E ℂ) :
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e)
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm) f) = f := by
  ext x
  simp [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

@[simp]
theorem compCLMOfContinuousLinearEquiv_symm_right_inv
    (e : E ≃L[ℝ] F) (f : SchwartzMap F ℂ) :
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm)
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e) f) = f := by
  ext x
  simp [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

end SCV
