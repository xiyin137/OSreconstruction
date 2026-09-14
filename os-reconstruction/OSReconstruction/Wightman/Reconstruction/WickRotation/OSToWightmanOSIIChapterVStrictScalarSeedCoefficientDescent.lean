/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.SCV.TotallyRealIdentity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictScalarSeedCoefficientGerm












noncomputable section

open Complex Filter Set Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

theorem zero_mem_osiiStrictCoefficientGermDomain
    {n : Nat} {S rho : Real}
    (P : SCV.StripCompactificationParameters S rho) :
    (0 : Fin n -> Complex) ∈
      osiiStrictCoefficientGermDomain P := by
  constructor
  · simp [Metric.mem_ball, P.radius_pos]
  · have harctan_zero :
        Complex.arctan 0 = 0 := by
      calc
        Complex.arctan 0 =
            (Real.arctan 0 : Complex) :=
          (Complex.ofReal_arctan 0).symm
        _ = 0 := by simp [Real.arctan_zero]
    have hinverse_zero :
        SCV.stripCompactificationLocalInverse P 0 = 0 := by
      simp [SCV.stripCompactificationLocalInverse,
        harctan_zero]
    have hlift_zero :
        osiiStrictCoefficientLocalInverseLift
            (n := n) P 0 =
          0 := by
      funext a
      simp [osiiStrictCoefficientLocalInverseLift,
        hinverse_zero]
    change
      osiiStrictCoefficientLocalInverseLift P 0 ∈
        osiiAxisPairLogDomain
    rw [hlift_zero]
    simp [osiiAxisPairLogDomain]
    positivity

namespace StrictScalarSeedCoefficientMZBoundData

variable
  {d : Nat} [NeZero d]
  {n k : Nat} [NeZero n]
  {A : OSIITimeContinuationStage d k}
  {S rho : Real}
  {P : SCV.StripCompactificationParameters S rho}
  {seed : Fin n -> Fin k -> Real}

end StrictScalarSeedCoefficientMZBoundData

end OSIIChapterV
end OSReconstruction
