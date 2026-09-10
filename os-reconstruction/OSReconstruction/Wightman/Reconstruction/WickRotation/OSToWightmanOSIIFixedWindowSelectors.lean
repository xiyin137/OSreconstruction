/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.SCV.LocalDistributionalEOW
import OSReconstruction.SCV.LocalContinuousEOW
import OSReconstruction.SCV.DistributionalEOWSupport
import Mathlib.Topology.MetricSpace.Thickening
import OSReconstruction.SCV.LocalEOWPairingCLM
import OSReconstruction.SCV.LocalEOWChartEnvelope
import OSReconstruction.SCV.DistributionalEOWKernelRecovery
import OSReconstruction.SCV.LocalProductRecovery
import OSReconstruction.SCV.DistributionalRepresentationGluing
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTimeProductDensity














noncomputable section

open Complex Topology MeasureTheory Metric Set Filter
open scoped Classical NNReal BigOperators LineDeriv

namespace OSReconstruction

private instance instTimeSchwartzCompatibleSMul {m : ℕ} :
    LinearMap.CompatibleSMul (SchwartzMap (Fin m → ℝ) ℂ) ℂ ℝ ℂ where
  map_smul := by
    intro f r x
    have hx : r • x = (r : ℂ) • x := by
      ext t
      simp
    rw [hx]
    simpa using f.map_smul (r : ℂ) x

end OSReconstruction
