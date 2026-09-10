/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReducedSchwinger
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapFixedAxisAllSplitUniformTargetRankField
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairProductSourceAdapter
















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIStep4MultiGapUniformCommonSlopeData

variable {d k : Nat} [NeZero d] [NeZero k]
variable {rho : Real} {hrho : 0 < rho}
variable {center : Fin (k * (d + 1)) -> Real}
variable {hcenter : forall j : Fin k,
  rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}

/-- Cutoffs which are one on the two physical time carriers of a generator
split and whose larger supports remain compact and strictly positive. -/
structure FixedAxisSplitUniformTargetCutoffHullData
    (D : OSIIStep4MultiGapUniformCommonSlopeData
      d k hrho center hcenter)
    (i : OSIIChapterV.GeneratorIndex k) where
  leftCutoff : SchwartzMap (Fin i.n -> Real) Complex
  left_eq_one : forall x,
    x ∈ D.fixedAxisSplitUniformTargetLeftTimeCarrier i ->
      leftCutoff x = 1
  left_support_positive :
    tsupport (leftCutoff : (Fin i.n -> Real) -> Complex) ⊆
      section43TimeStrictPositiveRegion i.n
  left_compact :
    HasCompactSupport (leftCutoff : (Fin i.n -> Real) -> Complex)
  rightCutoff : SchwartzMap (Fin i.m -> Real) Complex
  right_eq_one : forall x,
    x ∈ D.fixedAxisSplitUniformTargetRightTimeCarrier i ->
      rightCutoff x = 1
  right_support_positive :
    tsupport (rightCutoff : (Fin i.m -> Real) -> Complex) ⊆
      section43TimeStrictPositiveRegion i.m
  right_compact :
    HasCompactSupport (rightCutoff : (Fin i.m -> Real) -> Complex)

namespace FixedAxisSplitUniformTargetCutoffHullData

variable {D : OSIIStep4MultiGapUniformCommonSlopeData
  d k hrho center hcenter}
variable {i : OSIIChapterV.GeneratorIndex k}

/-- The enlarged left carrier is exactly the support of the left cutoff. -/
def leftCarrier
    (H : FixedAxisSplitUniformTargetCutoffHullData D i) :
    Set (Fin i.n -> Real) :=
  tsupport (H.leftCutoff : (Fin i.n -> Real) -> Complex)

/-- The enlarged right carrier is exactly the support of the right cutoff. -/
def rightCarrier
    (H : FixedAxisSplitUniformTargetCutoffHullData D i) :
    Set (Fin i.m -> Real) :=
  tsupport (H.rightCutoff : (Fin i.m -> Real) -> Complex)

theorem leftCarrier_isCompact
    (H : FixedAxisSplitUniformTargetCutoffHullData D i) :
    IsCompact H.leftCarrier := by
  simpa [leftCarrier, HasCompactSupport] using H.left_compact

theorem leftCarrier_subset_strictPositive
    (H : FixedAxisSplitUniformTargetCutoffHullData D i) :
    H.leftCarrier ⊆ section43TimeStrictPositiveRegion i.n := by
  simpa [leftCarrier] using H.left_support_positive

/-- Being one on the physical carrier forces that carrier into the cutoff
support. -/
theorem physicalLeftCarrier_subset_leftCarrier
    (H : FixedAxisSplitUniformTargetCutoffHullData D i) :
    D.fixedAxisSplitUniformTargetLeftTimeCarrier i ⊆ H.leftCarrier := by
  intro x hx
  apply subset_tsupport
  simpa [Function.mem_support, H.left_eq_one x hx]

/-- Being one on the physical carrier forces that carrier into the cutoff
support. -/
theorem physicalRightCarrier_subset_rightCarrier
    (H : FixedAxisSplitUniformTargetCutoffHullData D i) :
    D.fixedAxisSplitUniformTargetRightTimeCarrier i ⊆ H.rightCarrier := by
  intro x hx
  apply subset_tsupport
  simpa [Function.mem_support, H.right_eq_one x hx]

end FixedAxisSplitUniformTargetCutoffHullData

end OSIIStep4MultiGapUniformCommonSlopeData
end OSReconstruction
