/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVITimePositiveSpectrum















noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction

variable {d k : Nat} [NeZero d]
variable {A : OSIITimeContinuationStage d k}

namespace OSIIFullTimeStageVladimirovGrowthData

/-- The canonical physics-convention time-frequency distribution of one fixed
spatial probe. -/
def timeFrequencyDistribution
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    SchwartzMap (Fin k -> Real) Complex →L[Complex] Complex :=
  (G.timeBoundary chi).comp physicsFourierFlatInvCLM

/-- The canonical time-frequency distribution is supported in the positive
time orthant. The signed compact-test equation and the global large-height
bound prove this directly for the existing native boundary. -/
theorem timeFrequencyDistribution_support
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    HasFourierSupportInDualCone (osiiTimePositiveCone k)
      (G.timeFrequencyDistribution chi) :=
  G.timeBoundary_positiveFourierSupport chi

end OSIIFullTimeStageVladimirovGrowthData

end OSReconstruction
