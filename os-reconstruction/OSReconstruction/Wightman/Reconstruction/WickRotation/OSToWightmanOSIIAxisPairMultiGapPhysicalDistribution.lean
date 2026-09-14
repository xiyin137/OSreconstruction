/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapDistributionHolomorphy
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairPhysicalBlockPatch













noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction

variable {d n k : ℕ} [NeZero d]

namespace OSIIAxisPairPhysicalBlockPatch

/-- The part of a physical block chart seen by the global multi-gap logarithmic
domain. -/
def multiGapCarrier (Q : OSIIAxisPairPhysicalBlockPatch d k) :
    Set (Fin (k * (d + 1)) → ℂ) :=
  Q.carrier ∩ Q.blockLogMap ⁻¹' osiiAxisPairMultiGapLogDomain d k

end OSIIAxisPairPhysicalBlockPatch

namespace OSIIAxisPairMultiGapSourcewiseMZFamily
namespace SchwartzDistributionFamily

variable {P : OSIIAxisPairMultiGapSourcewiseMZFamily d n k}

/-- Pull a distribution-valued continuation back to one physical block chart. -/
def physicalDistribution
    (A : P.SchwartzDistributionFamily)
    (Q : OSIIAxisPairPhysicalBlockPatch d k)
    (z : Q.multiGapCarrier) :
    SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
  A.distribution ⟨Q.blockLogMap z.1, z.2.2⟩

end SchwartzDistributionFamily
end OSIIAxisPairMultiGapSourcewiseMZFamily

end OSReconstruction
