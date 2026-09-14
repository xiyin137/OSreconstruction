/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621SourceCoefficientSeminorm
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621EndpointRootedSourceIntegral
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedSourceIntegral
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation629Majorant
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedGeometry
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedBoundedScalarPhysicalCharts
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedDensityDistributionBound
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621Recovery
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIUniformEquation621Seed
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINormalizedEnvelopeBoundedRankInduction
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINormalizedEnvelopeWeightedSourceEnvelope
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageWideReflectedGramRootedBounds
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedReflectedGram
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRecursiveSectorAdaptiveShiftHandoff
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINormalizedEnvelopeWeightedSourceSpatialGrowth
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINormalizedEnvelopeMovingSlice










noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- The source-side form of the complete VI.2 shift: half the shift in the
state's first time, and the full shift in every internal gap. -/
def equation621ShiftedSourceCenter
    {m : Nat} (epsilon : Real) (tau : Fin (m + 1) -> Real) :
    Fin (m + 1) -> Real :=
  Fin.cons (tau 0 + epsilon / 2) (fun j => tau j.succ + epsilon)

@[simp] theorem equation621ShiftedSourceCenter_zero
    {m : Nat} (epsilon : Real) (tau : Fin (m + 1) -> Real) :
    equation621ShiftedSourceCenter epsilon tau 0 = tau 0 + epsilon / 2 := rfl

@[simp] theorem equation621ShiftedSourceCenter_succ
    {m : Nat} (epsilon : Real) (tau : Fin (m + 1) -> Real) (j : Fin m) :
    equation621ShiftedSourceCenter epsilon tau j.succ =
      tau j.succ + epsilon := rfl

theorem equation621ShiftedSourceCenter_positive
    {m : Nat} {epsilon : Real} (hepsilon : 0 <= epsilon)
    {tau : Fin (m + 1) -> Real}
    (htau : tau ∈ section43TimeStrictPositiveRegion (m + 1)) :
    equation621ShiftedSourceCenter epsilon tau ∈
      section43TimeStrictPositiveRegion (m + 1) := by
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact add_pos_of_pos_of_nonneg (htau 0)
      (div_nonneg hepsilon (by norm_num))
  · exact add_pos_of_pos_of_nonneg (htau i.succ) hepsilon

/-- The two half-shifted source heads make one full reflected bridge shift.
Every other reflected coordinate is an internal source gap. -/
theorem reflectedChronologicalGapMap_equation621ShiftedSourceCenter
    {m : Nat} (epsilon : Real) (left right : Fin (m + 1) -> Real) :
    reflectedChronologicalGapMap m
        (equation621ShiftedSourceCenter epsilon left,
          equation621ShiftedSourceCenter epsilon right) =
      reflectedChronologicalGapMap m (left, right) + (fun _ => epsilon) := by
  ext j
  refine Fin.addCases (fun i => ?_) (fun r => ?_) j
  · simp
  · refine Fin.cases ?_ (fun i => ?_) r
    · simp
      ring
    · simp

/-- At arbitrary complex internal parameters, the shifted physical source
pair is exactly the complete VI.2 shift of the original reflected point. -/
theorem reflectedCauchyShiftedStagePoint_equation621ShiftedSourceCenter
    {m : Nat} (epsilon : Real) (left right : Fin (m + 1) -> Real)
    (z : Fin m -> Complex) :
    reflectedCauchyShiftedStagePoint
        (reflectedChronologicalGapMap m
          (equation621ShiftedSourceCenter epsilon left,
            equation621ShiftedSourceCenter epsilon right)) z =
      osiiVI2Shift (m + (m + 1)) epsilon
        (reflectedCauchyShiftedStagePoint
          (reflectedChronologicalGapMap m (left, right)) z) := by
  rw [reflectedChronologicalGapMap_equation621ShiftedSourceCenter]
  ext j
  refine Fin.addCases (fun i => ?_) (fun r => ?_) j
  · simp [osiiVI2Shift]
    ring
  · refine Fin.cases ?_ (fun i => ?_) r
    · simp [osiiVI2Shift]
    · simp [osiiVI2Shift]
      ring

/-- The VI.2 unshift of a reflected point whose center was shifted first
leaves both reflected blocks unchanged and subtracts `epsilon` only at the
central bridge time. -/
def reflectedCauchyBridgeUnshiftTime
    {m : Nat}
    (epsilon : Real)
    (tau : Fin (m + (m + 1)) -> Real) :
    Fin (m + (m + 1)) -> Real :=
  fun j => Fin.addCases
    (fun i => tau (Fin.castAdd (m + 1) i))
    (fun r => Fin.cases
      (tau (Fin.natAdd m (0 : Fin (m + 1))) - epsilon)
      (fun i => tau (Fin.natAdd m i.succ)) r) j

@[simp] theorem reflectedCauchyBridgeUnshiftTime_left
    {m : Nat}
    (epsilon : Real)
    (tau : Fin (m + (m + 1)) -> Real)
    (i : Fin m) :
    reflectedCauchyBridgeUnshiftTime epsilon tau
        (Fin.castAdd (m + 1) i) =
      tau (Fin.castAdd (m + 1) i) := by
  simp [reflectedCauchyBridgeUnshiftTime]

@[simp] theorem reflectedCauchyBridgeUnshiftTime_bridge
    {m : Nat}
    (epsilon : Real)
    (tau : Fin (m + (m + 1)) -> Real) :
    reflectedCauchyBridgeUnshiftTime epsilon tau
        (Fin.natAdd m (0 : Fin (m + 1))) =
      tau (Fin.natAdd m (0 : Fin (m + 1))) - epsilon := by
  simp [reflectedCauchyBridgeUnshiftTime]

@[simp] theorem reflectedCauchyBridgeUnshiftTime_right
    {m : Nat}
    (epsilon : Real)
    (tau : Fin (m + (m + 1)) -> Real)
    (i : Fin m) :
    reflectedCauchyBridgeUnshiftTime epsilon tau
        (Fin.natAdd m i.succ) =
      tau (Fin.natAdd m i.succ) := by
  simp [reflectedCauchyBridgeUnshiftTime]

namespace TargetHubHalfAnchorData

end TargetHubHalfAnchorData

namespace VI2Equation621ReflectedSourcePointCoverageData

end VI2Equation621ReflectedSourcePointCoverageData

namespace StrictGeneratedScalarDepthPointedData

open Section43ProductTimeApproximateIdentity
open Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData

namespace RootedGeneratorSelectedSegmentReflectedPointCoverageData

end RootedGeneratorSelectedSegmentReflectedPointCoverageData

end StrictGeneratedScalarDepthPointedData
end OSIIChapterV
end OSReconstruction
