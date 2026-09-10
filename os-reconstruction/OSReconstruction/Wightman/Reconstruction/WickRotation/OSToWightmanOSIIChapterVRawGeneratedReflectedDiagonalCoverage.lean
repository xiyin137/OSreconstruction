/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRawGeneratedLogarithmicDomains
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratedCarrierCoverage
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVTargetAdaptedMovingSliceCoverage
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVTargetHubMovingSliceCoverage













noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- The reflected diagonal of a raw mixed Hilbert argument is a raw scalar
argument at the same depth, after the harmless finite-arity reindexing from
2 * (m + 1) - 1 to m + (m + 1). -/
theorem reflectedMixedDiagonal_rawStrictGenerated
    {m N : Nat}
    {z : Fin m -> Complex}
    (hz :
      reflectedMixedArgument z ∈
        osiiRawStrictGeneratedMixedLogarithmicBase (m + 1) N) :
    OSIIRawStrictGeneratedLogarithmicArgument .scalar
      (m + (m + 1)) N (reflectedMixedDiagonal z) := by
  have hdiag :=
    OSIIRawStrictGeneratedLogarithmicArgument.mixed_diagonal_mem_scalar
      (n := m + 1) (by omega) hz
  have hreindexed :=
    OSIIRawStrictGeneratedLogarithmicArgument.reindex
      (by omega :
        2 * (m + 1) - 1 = m + (m + 1))
      hdiag
  simpa [reflectedMixedDiagonal] using hreindexed

/-- A positive-real reflected Cauchy shift of a raw mixed tail lies in the
raw scalar argument carrier.  This is the exact carrier-level source
self-pair fact needed before applying the raw equation-(6.28') bound. -/
theorem reflectedCauchyShiftedStagePoint_mem_rawStrictGeneratedCarrier
    {m N : Nat}
    {tau : Fin (m + (m + 1)) -> Real}
    {z : Fin m -> Complex}
    (htau :
      tau ∈ section43TimeStrictPositiveRegion (m + (m + 1)))
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiRawStrictGeneratedMixedLogarithmicBase (m + 1) N)) :
    reflectedCauchyShiftedStagePoint tau z ∈
      osiiTimeArgumentCarrier
        (osiiRawStrictGeneratedLogarithmicBase (m + (m + 1)) N) := by
  refine
    ⟨reflectedCauchyShiftedStagePoint_mem_rightHalfPlane htau hz.1,
      ?_⟩
  apply
    OSIIRawStrictGeneratedLogarithmicArgument.scalar_hyperrectangle
      (reflectedMixedDiagonal_rawStrictGenerated
        (by simpa [reflectedMixedArgument] using hz.2))
  exact
    abs_argumentVector_reflectedCauchyShiftedStagePoint_le
      htau hz.1

end OSIIChapterV
end OSReconstruction
