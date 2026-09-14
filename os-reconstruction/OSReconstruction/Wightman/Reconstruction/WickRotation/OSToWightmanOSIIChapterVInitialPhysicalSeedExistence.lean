/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairChronologicalTranslation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialReducedPhysicalCovariance
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVChronologicalCompactCover
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductMultiGapPacketContinuity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapPhysicalBlockPatch
import OSReconstruction.SCV.ConnectedNeighborhood
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReducedTestLiftRepresentative
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSourceDerivatives


















noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d] [NeZero k]

/-- Reduced configurations whose every time gap is strictly positive. -/
def initialReducedStrictPositiveGapRegion (d k : ℕ) [NeZero d] :
    Set (NPointDomain d k) :=
  (section43QTimeCLM d k) ⁻¹'
    section43TimeStrictPositiveRegion k

omit [NeZero k] in
/-- The strict positive reduced-gap region is open. -/
theorem isOpen_initialReducedStrictPositiveGapRegion :
    IsOpen (initialReducedStrictPositiveGapRegion d k) := by
  exact
    (isOpen_section43TimeStrictPositiveRegion k).preimage
      (section43QTimeCLM d k).continuous

end OSIIChapterV
end OSReconstruction
