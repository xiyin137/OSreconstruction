/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Init
import OSReconstruction.SCV.LocalContinuousEOW
import OSReconstruction.SCV.DistributionalEOWSupport
import Mathlib.Topology.MetricSpace.Thickening











noncomputable section

open Complex Metric Set

namespace SCV

variable {m : ℕ}

/-- Coordinatewise imaginary part is norm-controlled by the complex chart
norm. -/
theorem norm_complexChart_im_le (w : ComplexChartSpace m) :
    ‖(fun j : Fin m => (w j).im)‖ ≤ ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 ?_
  intro j
  rw [Real.norm_eq_abs]
  exact (Complex.abs_im_le_norm (w j)).trans (norm_le_pi_norm w j)

/-- Coordinatewise real part is norm-controlled by the complex chart norm. -/
theorem norm_complexChart_re_le (w : ComplexChartSpace m) :
    ‖(fun j : Fin m => (w j).re)‖ ≤ ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 ?_
  intro j
  rw [Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm (w j)).trans (norm_le_pi_norm w j)

end SCV
