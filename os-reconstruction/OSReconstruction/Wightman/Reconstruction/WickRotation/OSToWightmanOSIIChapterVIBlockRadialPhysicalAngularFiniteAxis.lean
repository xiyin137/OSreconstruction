/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPhysicalAngularContinuation



















noncomputable section

open Complex MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction

variable {d k : Nat} [NeZero d] [NeZero k]
variable {rho : Real} {hrho : 0 < rho}
variable {center : Fin (k * (d + 1)) -> Real}
variable {hcenter : forall j : Fin k,
  rho <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
variable {OS : OsterwalderSchraderAxioms d}
variable {lgc : OSLinearGrowthCondition d OS}

namespace OSIIStep4SynchronizedMultiGapContinuationData

variable (Z : OSIIStep4SynchronizedMultiGapContinuationData d k hrho
  (osiiStep4MultiGapXiHatCenter d k center)
  (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter))

/-- The physical target with precisely the signed-axis slices in `A` turned
on.  Every unselected slice is kept at the simultaneous real logarithmic
base. -/
def physicalAngularMaskedTargetLog
    (A : Finset (osiiAxisPairIndex d))
    (z : OSIIStep4FullComplexSpace d k) :
    Fin k -> osiiAxisPairIndex d -> Complex :=
  fun i a =>
    let w := osiiStep4MultiGapTargetLog d k Z.uniform.T center
      (fun u => (z u).re) i a
    if a ∈ A then w else (w.re : Complex)

/-- Compact family of physical angular targets with precisely the axes in
`A` turned on. -/
def physicalAngularMaskedTargetSet
    (A : Finset (osiiAxisPairIndex d)) :
    Set (Fin k -> osiiAxisPairIndex d -> Complex) :=
  (Z.physicalAngularMaskedTargetLog (hcenter := hcenter) A) ''
    SCV.closedPolydisc
      (0 : OSIIStep4FullComplexSpace d k) (fun _ => rho / 8)

end OSIIStep4SynchronizedMultiGapContinuationData

/-- Exact carrier obligation at one finite signed-axis mask. -/
structure OSIIStep4PhysicalAngularFinsetCoverageData
    (Z : OSIIStep4SynchronizedMultiGapContinuationData d k hrho
      (osiiStep4MultiGapXiHatCenter d k center)
      (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter))
    (D : OSIIStep4PhysicalAngularContinuationData
      (hcenter := hcenter) Z OS lgc)
    (A : Finset (osiiAxisPairIndex d)) : Prop where
  maskedTargetSet_subset :
    Z.physicalAngularMaskedTargetSet (hcenter := hcenter) A ⊆ D.carrier

namespace OSIIStep4PhysicalAngularFinsetCoverageData

variable {Z : OSIIStep4SynchronizedMultiGapContinuationData d k hrho
  (osiiStep4MultiGapXiHatCenter d k center)
  (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter)}
variable {D : OSIIStep4PhysicalAngularContinuationData
  (hcenter := hcenter) Z OS lgc}
variable {A : Finset (osiiAxisPairIndex d)}

end OSIIStep4PhysicalAngularFinsetCoverageData

namespace OSIIStep4PhysicalAngularRankData

variable {D0 : OSIIChapterV.StrictGeneratedScalarDepthPointedData OS 0}
variable {Z : OSIIStep4SynchronizedMultiGapContinuationData d k hrho
  (osiiStep4MultiGapXiHatCenter d k center)
  (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter)}
variable {D : OSIIStep4PhysicalAngularContinuationData
  (hcenter := hcenter) Z OS lgc}

end OSIIStep4PhysicalAngularRankData

/-- A physical continuation together with coverage of one finite signed-axis
mask. -/
structure OSIIStep4PhysicalAngularFinsetCoveredData
    (Z : OSIIStep4SynchronizedMultiGapContinuationData d k hrho
      (osiiStep4MultiGapXiHatCenter d k center)
      (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter))
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (A : Finset (osiiAxisPairIndex d)) where
  continuationData : OSIIStep4PhysicalAngularContinuationData
    (hcenter := hcenter) Z OS lgc
  coverage : OSIIStep4PhysicalAngularFinsetCoverageData
    Z continuationData A

namespace OSIIStep4PhysicalAngularFinsetSuccessorData

variable {Z : OSIIStep4SynchronizedMultiGapContinuationData d k hrho
  (osiiStep4MultiGapXiHatCenter d k center)
  (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter)}
variable {A : Finset (osiiAxisPairIndex d)}
variable {C : OSIIStep4PhysicalAngularFinsetCoveredData
  (hcenter := hcenter) Z OS lgc A}
variable {a : osiiAxisPairIndex d}

end OSIIStep4PhysicalAngularFinsetSuccessorData

namespace OSIIStep4PhysicalAngularExtensionAtlasData

variable {Z : OSIIStep4SynchronizedMultiGapContinuationData d k hrho
  (osiiStep4MultiGapXiHatCenter d k center)
  (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter)}
variable {A : Finset (osiiAxisPairIndex d)}
variable {C : OSIIStep4PhysicalAngularFinsetCoveredData
  (hcenter := hcenter) Z OS lgc A}
variable {index : Type*}

end OSIIStep4PhysicalAngularExtensionAtlasData

namespace OSIIStep4SynchronizedMultiGapContinuationData

variable (Z : OSIIStep4SynchronizedMultiGapContinuationData d k hrho
  (osiiStep4MultiGapXiHatCenter d k center)
  (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter))

end OSIIStep4SynchronizedMultiGapContinuationData

end OSReconstruction
