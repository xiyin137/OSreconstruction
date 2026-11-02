/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
module

public import Init
public import OSReconstruction.SCV.LocalDistributionalEOW
public import OSReconstruction.SCV.LocalContinuousEOW
public import OSReconstruction.SCV.DistributionalEOWSupport
public import Mathlib.Topology.MetricSpace.Thickening
public import OSReconstruction.SCV.LocalEOWPairingCLM
public import OSReconstruction.SCV.LocalEOWChartEnvelope
public import OSReconstruction.SCV.DistributionalEOWKernelRecovery
public import OSReconstruction.SCV.LocalProductRecovery
public import OSReconstruction.SCV.DistributionalRepresentationGluing
public import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTimeProductDensity

@[expose] public section

noncomputable section

open Complex Topology MeasureTheory Metric Set Filter
open scoped Classical NNReal BigOperators LineDeriv

namespace OSReconstruction

instance instTimeSchwartzCompatibleSMul {m : ℕ} :
    LinearMap.CompatibleSMul (SchwartzMap (Fin m → ℝ) ℂ) ℂ ℝ ℂ where
  map_smul := by
    intro f r x
    have hx : r • x = (r : ℂ) • x := by
      ext t
      simp
    rw [hx]
    simpa using f.map_smul (r : ℂ) x

end OSReconstruction
