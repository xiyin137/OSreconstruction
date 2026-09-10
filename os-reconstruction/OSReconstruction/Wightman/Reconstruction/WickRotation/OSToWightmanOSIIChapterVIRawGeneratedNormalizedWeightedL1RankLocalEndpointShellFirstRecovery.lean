/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRawGeneratedNormalizedWeightedL1RankLocalShellFirstRecovery
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedReflectedEndpointRows
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621EndpointProbeRows
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621SpatialSmoothingVitali
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621GeneratorSpatialSplit
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorBoundPreservation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVSourceIndexedReflectedGram
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedDensityPointRecovery
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIReflectedOrbitSpatialProductFactorization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedDensityDistributionBound
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621ProductTargetAdaptedFactorization











noncomputable section

open Complex Set Filter Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

open Section43ProductTimeApproximateIdentity
open Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData

theorem positiveRealTimeEmbed_mem_rawStrictGenerated
    {k depth : Nat} (tau : Fin k -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion k) :
    osiiPositiveRealTimeEmbed tau ∈ osiiTimeArgumentCarrier
      (osiiRawStrictGeneratedLogarithmicBase k depth) := by
  refine ⟨(osiiPositiveRealTimeEmbed_mem_rightHalfPlane_iff tau).2 htau, ?_⟩
  have harg :
      osiiTimeArgumentVector (osiiPositiveRealTimeEmbed tau) =
        (0 : Fin k -> Real) := by
    funext j
    rw [osiiTimeArgumentVector, osiiPositiveRealTimeEmbed,
      Complex.arg_ofReal_of_nonneg (htau j).le]
    rfl
  rw [harg]
  exact OSIIRawStrictGeneratedLogarithmicArgument.scalarZero k depth

end OSIIChapterV
end OSReconstruction
