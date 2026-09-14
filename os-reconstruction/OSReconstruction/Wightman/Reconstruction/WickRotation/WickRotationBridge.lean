/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Topology.Algebra.Module.Basic








noncomputable section

open Complex

namespace OSReconstruction

/-- The Wick rotation cancels on complex scalars: `-I * (I * t) = t`. -/
theorem neg_I_mul_I_mul (t : ℂ) : -I * (I * t) = t := by
  rw [← mul_assoc]
  simp

end OSReconstruction
