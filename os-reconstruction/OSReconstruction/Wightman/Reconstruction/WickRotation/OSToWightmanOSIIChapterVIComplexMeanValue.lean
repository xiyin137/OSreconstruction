/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
module

public import OSReconstruction.SCV.Polydisc
public import Init
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

@[expose] public section

noncomputable section

open Complex Metric Set
open scoped Classical

namespace OSReconstruction

/-- The flattened complex perturbation space in OS II equation (6.6): one
complex spacetime vector for every difference block. -/
abbrev OSIIStep4FullComplexSpace (d k : ℕ) :=
  Fin (k * (d + 1)) → ℂ

end OSReconstruction
