/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib
import Init
import OSReconstruction.SCV.Osgood
import OSReconstruction.SCV.TotallyRealIdentity














noncomputable section

open Complex Topology
open scoped Classical NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

namespace OSReconstruction

/-- In the right half-plane, a bound on the slope `|Im z| / Re z` bounds the
absolute argument by the corresponding arctangent. -/
theorem osiiLemma51_abs_arg_eq_arctan_abs_im_div_re
    {z : ℂ} (hzre : 0 < z.re) :
    |Complex.arg z| = Real.arctan |z.im / z.re| := by
  have harg_abs_lt : |Complex.arg z| < Real.pi / 2 := by
    exact (Complex.abs_arg_lt_pi_div_two_iff).2 (Or.inl hzre)
  have harg_mem : Complex.arg z ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    exact abs_lt.mp harg_abs_lt
  have htan : Real.tan (Complex.arg z) = z.im / z.re := Complex.tan_arg z
  have harg : Real.arctan (z.im / z.re) = Complex.arg z :=
    Real.arctan_eq_of_tan_eq htan harg_mem
  rw [← harg]
  by_cases hq : 0 ≤ z.im / z.re
  · rw [abs_of_nonneg hq, abs_of_nonneg (Real.arctan_nonneg.mpr hq)]
  · have hq_neg : z.im / z.re < 0 := lt_of_not_ge hq
    rw [abs_of_neg hq_neg, abs_of_neg (Real.arctan_lt_zero.mpr hq_neg),
      Real.arctan_neg]

end OSReconstruction
