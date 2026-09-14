/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialDistributionOrbit
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapTargetGeometry
import Init
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Pi
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIComplexMeanValue
















noncomputable section

open Complex MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction

/-- The radial Schwartz source based at the blockwise axis-pair anchor. -/
noncomputable def osiiStep4CoherentTargetSource
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) -> Real)
    (z : OSIIStep4FullComplexSpace d k) :
    SchwartzNPoint d (k + 1) :=
  osiiStep4PositiveLiftedCenteredPartialConvolutionKernelFullSource
    d k hrho (osiiStep4MultiGapXiHatCenter d k center)
      (fun a => (z a).re) (fun a => (z a).im)

/-- The complete radial source family at the blockwise anchor is continuous
in the full complex radial parameter. -/
theorem continuous_osiiStep4CoherentTargetSource
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) -> Real) :
    Continuous (osiiStep4CoherentTargetSource d k hrho center) := by
  have hsplit : Continuous
      (fun z : OSIIStep4FullComplexSpace d k =>
        ((fun a => (z a).re), (fun a => (z a).im))) := by
    apply Continuous.prodMk
    · exact continuous_pi fun a =>
        Complex.continuous_re.comp (continuous_apply a)
    · exact continuous_pi fun a =>
        Complex.continuous_im.comp (continuous_apply a)
  have hcontinuous :=
    (continuous_osiiStep4PositiveLiftedCenteredPartialConvolutionKernelFullSource
      d k hrho (osiiStep4MultiGapXiHatCenter d k center)).comp hsplit
  simpa only [osiiStep4CoherentTargetSource] using hcontinuous

end OSReconstruction
