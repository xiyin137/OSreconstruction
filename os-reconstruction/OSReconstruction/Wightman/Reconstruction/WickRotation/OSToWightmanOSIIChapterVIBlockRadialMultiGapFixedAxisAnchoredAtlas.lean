/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapFixedAxisSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedReflectedGram
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVUniformCompactTimeAnchoredJointContinuity










noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction

/-- Number of physical gaps in an interior split with `q + 1` gaps before the
bridge and `r + 1` gaps after it. -/
abbrev osiiStep4MultiGapInteriorArity (q r : Nat) : Nat :=
  (q + 1) + 1 + (r + 1)

/-- The physical bridge gap of an interior split. -/
def osiiStep4MultiGapInteriorIndex (q r : Nat) :
    Fin (osiiStep4MultiGapInteriorArity q r) :=
  osiiStep4SelectedBlockIndex (q + 1) (r + 1)

@[simp] theorem osiiStep4MultiGapInteriorIndex_val (q r : Nat) :
    (osiiStep4MultiGapInteriorIndex q r).val = q + 1 :=
  rfl

/-- Transport a finite time carrier along an equality of its arity. -/
def castFiniteTimeCarrier {n m : Nat} (h : n = m)
    (K : Set (Fin n -> Real)) : Set (Fin m -> Real) :=
  cast (congrArg (fun j => Set (Fin j -> Real)) h) K

/-- Transport a universal compact-time source together with its finite time
carrier. -/
def castUniformCompactTimeSource
    {d n m : Nat} [NeZero d]
    (h : n = m) {K : Set (Fin n -> Real)}
    (source : OSIIChapterV.UniformCompactTimeSource d n K) :
    OSIIChapterV.UniformCompactTimeSource d m
      (castFiniteTimeCarrier h K) := by
  subst m
  simpa [castFiniteTimeCarrier] using source

namespace OSIIChapterV
namespace UniversalCompactCarrierAnchoredAtlasData

variable {d q : Nat} [NeZero d]
variable {L : SimultaneousTimeContinuationStageLevel d}
variable {OS : OsterwalderSchraderAxioms d}
variable {K : Set (Fin ((q + 1) + 1) -> Real)}

end UniversalCompactCarrierAnchoredAtlasData
end OSIIChapterV

namespace OSIIStep4MultiGapUniformCommonSlopeData

variable {d q r : Nat} [NeZero d]
variable [NeZero (osiiStep4MultiGapInteriorArity q r)]
variable {rho : Real} {hrho : 0 < rho}
variable
  {center : Fin (osiiStep4MultiGapInteriorArity q r * (d + 1)) -> Real}
variable
  {hcenter : forall j : Fin (osiiStep4MultiGapInteriorArity q r),
    rho / 2 <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}

variable {OS : OsterwalderSchraderAxioms d}
variable {C : Type*}
variable [OSIIChapterV.CanonicalGeneratorStageLevelProvider OS C]

end OSIIStep4MultiGapUniformCommonSlopeData
end OSReconstruction
