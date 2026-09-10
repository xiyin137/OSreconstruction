/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialCoherentTarget
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapSynchronizedCommonSlope
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedPointedDepthInduction
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapBoundedTarget




















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

/-- The exact continuation invariant needed by the physical radial integral.
It retains only the actual centered radial source family, not every unrelated
full Schwartz source. -/
structure OSIIStep4PhysicalAngularContinuationData
    (Z : OSIIStep4SynchronizedMultiGapContinuationData d k hrho
      (osiiStep4MultiGapXiHatCenter d k center)
      (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter))
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) where
  carrier : Set (Fin k -> osiiAxisPairIndex d -> Complex)
  carrier_open : IsOpen carrier
  firstCarrier_subset :
    osiiAxisPairMultiGapLogDomain d k ⊆ carrier
  continuation : OSIIStep4FullComplexSpace d k ->
    (Fin k -> osiiAxisPairIndex d -> Complex) -> Complex
  weaklyHolomorphic : forall z,
    DifferentiableOn Complex (continuation z) carrier
  continuousOn_joint_on_compact : forall
      (L : Set (Fin k -> osiiAxisPairIndex d -> Complex)),
    IsCompact L -> L ⊆ carrier ->
      ContinuousOn
        (fun p : OSIIStep4FullComplexSpace d k ×
            (Fin k -> osiiAxisPairIndex d -> Complex) =>
          continuation p.1 p.2)
        (Set.univ ×ˢ L)
  extendsFirst : forall z,
    Set.EqOn (continuation z)
      (fun w => Z.coherent.pairing OS lgc
        (osiiStep4CoherentTargetSource d k hrho center z) w)
      (osiiAxisPairMultiGapLogDomain d k)

namespace OSIIStep4PhysicalAngularContinuationData

end OSIIStep4PhysicalAngularContinuationData

namespace OSIIBlockRadialFullSchwartzAngularAtlasData

variable {index : Type*}
variable {Z : OSIIStep4SynchronizedMultiGapContinuationData d k hrho
  (osiiStep4MultiGapXiHatCenter d k center)
  (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter)}

end OSIIBlockRadialFullSchwartzAngularAtlasData

namespace OSIIStep4SynchronizedMultiGapContinuationData

end OSIIStep4SynchronizedMultiGapContinuationData

namespace OSIIStep4PhysicalAngularContinuationExtensionData

variable {Z : OSIIStep4SynchronizedMultiGapContinuationData d k hrho
  (osiiStep4MultiGapXiHatCenter d k center)
  (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter)}
variable {D : OSIIStep4PhysicalAngularContinuationData
  (hcenter := hcenter) Z OS lgc}

end OSIIStep4PhysicalAngularContinuationExtensionData

namespace OSIIStep4PhysicalAngularRankData

variable {D0 : OSIIChapterV.StrictGeneratedScalarDepthPointedData OS 0}
variable {Z : OSIIStep4SynchronizedMultiGapContinuationData d k hrho
  (osiiStep4MultiGapXiHatCenter d k center)
  (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter)}
variable {D : OSIIStep4PhysicalAngularContinuationData
  (hcenter := hcenter) Z OS lgc}

end OSIIStep4PhysicalAngularRankData

namespace OSIIStep4PhysicalAngularContinuationData

variable {Z : OSIIStep4SynchronizedMultiGapContinuationData d k hrho
  (osiiStep4MultiGapXiHatCenter d k center)
  (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter)}

end OSIIStep4PhysicalAngularContinuationData

end OSReconstruction
