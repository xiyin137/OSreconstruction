/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapSourcewiseMZ















noncomputable section

open Complex Topology
open scoped Classical BigOperators

namespace OSReconstruction

variable {d k n : ℕ} [NeZero d] [NeZero k]

namespace OSIIAxisPairPhysicalChart

end OSIIAxisPairPhysicalChart

/-- One simultaneous physical block patch whose complete logarithmic image
lies in the genuine global multi-gap `l1` carrier. -/
structure OSIIAxisPairMultiGapPhysicalBlockPatch
    (d k : ℕ) [NeZero d] where
  toPhysicalBlockPatch : OSIIAxisPairPhysicalBlockPatch d k
  logMap_mapsTo_multiGap :
    Set.MapsTo toPhysicalBlockPatch.blockLogMap
      toPhysicalBlockPatch.carrier
      (osiiAxisPairMultiGapLogDomain d k)

namespace OSIIAxisPairMultiGapPhysicalBlockPatch

instance : Coe (OSIIAxisPairMultiGapPhysicalBlockPatch d k)
    (OSIIAxisPairPhysicalBlockPatch d k) :=
  ⟨toPhysicalBlockPatch⟩

end OSIIAxisPairMultiGapPhysicalBlockPatch

end OSReconstruction
