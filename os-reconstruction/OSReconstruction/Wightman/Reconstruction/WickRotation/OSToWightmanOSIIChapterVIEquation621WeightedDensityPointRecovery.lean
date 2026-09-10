/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.SCV.LaplaceSchwartz
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIDeltaSmearing
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedSpatialDensity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIUniformEquation621Seed
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation629Majorant












noncomputable section

open Complex Filter MeasureTheory
open scoped Classical

namespace OSReconstruction

/-- A normalized nonnegative real Schwartz approximate identity on a finite
flat spatial coordinate space. -/
structure OSIIEquation621SpatialApproxIdentityData (m : Nat) where
  test : Nat -> SchwartzMap (Fin m -> Real) Complex
  radius : Nat -> Real
  nonneg : forall N x, 0 <= (test N x).re
  real : forall N x, (test N x).im = 0
  integral_eq_one : forall N,
    (∫ x : Fin m -> Real, test N x) = 1
  compactSupport : forall N,
    HasCompactSupport (test N : (Fin m -> Real) -> Complex)
  support_subset_ball : forall N,
    Function.support (test N : (Fin m -> Real) -> Complex) ⊆
      Metric.ball 0 (radius N)
  radius_tendsto : Tendsto radius atTop (nhds 0)

namespace OSIIEquation621SpatialApproxIdentityData

/-- Translate the `N`th flat spatial delta probe to the point `x`. -/
def translatedTest
    {m : Nat}
    (Q : OSIIEquation621SpatialApproxIdentityData m)
    (x : Fin m -> Real) (N : Nat) :
    SchwartzMap (Fin m -> Real) Complex :=
  SCV.translateSchwartz (-x) (Q.test N)

/-- The translated flat delta probe transported back to the Section-4.3
spatial Schwartz space. -/
def section43Probe
    {d k : Nat}
    (Q : OSIIEquation621SpatialApproxIdentityData (k * d))
    (x : Fin (k * d) -> Real) (N : Nat) :
    SchwartzMap (Section43SpatialSpace d k) Complex :=
  (section43SpatialFlatSchwartzCLE d k).symm (Q.translatedTest x N)

end OSIIEquation621SpatialApproxIdentityData

namespace OSIIEquation621WeightedDensityContinuationData

end OSIIEquation621WeightedDensityContinuationData

namespace OSIIEquation621SpatialProbeFactorizationData

end OSIIEquation621SpatialProbeFactorizationData
end OSReconstruction
