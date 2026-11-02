/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Topology.Algebra.Module.Basic

@[expose] public section

noncomputable section

open Complex

namespace OSReconstruction

/-- The Wick rotation cancels on complex scalars: `-I * (I * t) = t`. -/
theorem neg_I_mul_I_mul (t : ℂ) : -I * (I * t) = t := by
  rw [← mul_assoc]
  simp

end OSReconstruction
