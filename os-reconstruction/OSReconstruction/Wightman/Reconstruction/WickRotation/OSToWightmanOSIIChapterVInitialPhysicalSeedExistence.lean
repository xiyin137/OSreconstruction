/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
module

public import Init
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairChronologicalTranslation
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialReducedPhysicalCovariance
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVChronologicalCompactCover
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductMultiGapPacketContinuity
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapPhysicalBlockPatch
public import OSReconstruction.SCV.ConnectedNeighborhood
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReducedTestLiftRepresentative
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSourceDerivatives

@[expose] public section

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
