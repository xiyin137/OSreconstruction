/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.SCV.LocallyUniformDistributionRepresentation
import OSReconstruction.SCV.EuclideanWeylFrechet
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVAnchoredOrderedTransport















noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Restrict a continuation stage to an open subset of its carrier. -/
def restrictTimeContinuationStageCarrier
    {d k : ℕ}
    (A : OSIITimeContinuationStage d k)
    (U : Set (OSIITimeGapSpace k))
    (hU_open : IsOpen U)
    (hU_subset : U ⊆ A.carrier) :
    OSIITimeContinuationStage d k where
  carrier := U
  carrier_open := hU_open
  distribution := A.distribution
  weaklyHolomorphic := fun χ =>
    (A.weaklyHolomorphic χ).mono hU_subset

namespace ExhaustingCarrierNormalFamilyData

variable {d k : ℕ} [NeZero d]

end ExhaustingCarrierNormalFamilyData
end OSIIChapterV
end OSReconstruction
