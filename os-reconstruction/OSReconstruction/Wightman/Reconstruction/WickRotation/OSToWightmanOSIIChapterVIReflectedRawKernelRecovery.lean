/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
module

public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReflectedMixedTimeSplit
public import Init
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedGeometry
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621Recovery
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIUniformEquation621Seed
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINormalizedEnvelopeBoundedRankInduction
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINormalizedEnvelopeWeightedSourceEnvelope

@[expose] public section

noncomputable section

open Complex Set Topology Filter
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- A cutoff which is one at the retained reduced-time center does not alter
the raw reflected mixed kernel at any pair of absolute packet centers which
realizes that reduced-time point.  This form permits asymmetric allocation of
the reflected bridge gap between the two packets. -/
theorem osiiReflectedMixedMovingKernel_centers_eq_distribution_of_cutoff_eq_one
    {d k : Nat} [NeZero d]
    (A : OSIITimeContinuationStage d (k + (k + 1)))
    (rho : SchwartzMap (Fin (k + (k + 1)) -> Real) Complex)
    (chiLeft chiRight :
      SchwartzMap (Section43SpatialSpace d (k + 1)) Complex)
    (w : Fin (k + k) -> Complex)
    (leftCenter rightCenter : Fin (k + 1) -> Real)
    (tau : Fin (k + (k + 1)) -> Real)
    (htime : osiiMixedBlockGlobalReducedTime k
      (Fin.append leftCenter rightCenter) = tau)
    (hrho : rho tau = 1) :
    osiiReflectedMixedMovingKernel A rho chiLeft chiRight w
        (osiiMixedTimeCenter leftCenter rightCenter) =
      A.distribution
        (-(reflectedReducedTimeDisplacementCLM k w) +
          osiiPositiveRealTimeEmbed tau)
        (osiiMixedSpatialHeadMarginal chiLeft chiRight) := by
  simp [osiiReflectedMixedMovingKernel,
    osiiStageFixedSpatialCutoffIntegrand, osiiMixedTimeCenter,
    htime, hrho]

namespace OSIIStageMovingSlicePlateauData

end OSIIStageMovingSlicePlateauData

namespace CompactLogTargetReflectedOrbitData

end CompactLogTargetReflectedOrbitData

end OSIIChapterV
end OSReconstruction
