/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
module

public import OSReconstruction.SCV.DistributionalRepresentationUniqueness
public import OSReconstruction.SCV.TotallyRealIdentity
public import Init
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedSpatialDensity
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIUniformEquation621Seed
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation629Majorant

@[expose] public section

noncomputable section

open Complex MeasureTheory Set Topology
open scoped BoundedContinuousFunction Classical

namespace OSReconstruction

namespace OSIIEquation621WeightedDensityRealSeedAtlasData

variable {d k p : Nat}
variable {A : OSIITimeContinuationStage d k}

end OSIIEquation621WeightedDensityRealSeedAtlasData

namespace OSIIEquation621WeightedDensityAtlasData

variable {d k p : Nat}
variable {A : OSIITimeContinuationStage d k}

/-- The stage distribution transported to flat spatial coordinates. -/
noncomputable def flatDistribution
    (A : OSIITimeContinuationStage d k)
    (zeta : OSIITimeGapSpace k) :
    SchwartzMap (Fin (k * d) -> Real) Complex →L[Complex] Complex :=
  (A.distribution zeta).comp
    (section43SpatialFlatSchwartzCLE d k).symm.toContinuousLinearMap

end OSIIEquation621WeightedDensityAtlasData
end OSReconstruction
