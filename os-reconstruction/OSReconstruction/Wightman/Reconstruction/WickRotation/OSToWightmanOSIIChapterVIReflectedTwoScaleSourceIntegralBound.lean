/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINormalizedEnvelopeWeightedSourceSpatialGrowth











noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

open Section43ProductTimeApproximateIdentity

variable {d q : Nat} [NeZero d]

/-- The reflected gap tuple formed from two strict-positive block-time tuples
is itself strict-positive. -/
theorem reflectedChronologicalGapMap_mem_strictPositive
    (tauLeft tauRight : Fin ((q + 1) + 1) -> Real)
    (hleft : tauLeft ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hright : tauRight ∈ section43TimeStrictPositiveRegion ((q + 1) + 1)) :
    reflectedChronologicalGapMap (q + 1) (tauLeft, tauRight) ∈
      section43TimeStrictPositiveRegion
        ((q + 1) + ((q + 1) + 1)) := by
  intro i
  simp only [reflectedChronologicalGapMap]
  split_ifs with hbefore hbridge
  · exact hleft _
  · exact add_pos (hleft 0) (hright 0)
  · exact hright _

namespace VI2NormalizedTargetSeminormBoundData

end VI2NormalizedTargetSeminormBoundData

end OSIIChapterV
end OSReconstruction
