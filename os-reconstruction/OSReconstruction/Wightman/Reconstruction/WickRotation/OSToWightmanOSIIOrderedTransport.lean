/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSourceCurrent








noncomputable section

open Complex

namespace OSReconstruction
namespace OSIIChapterV

variable {d m : ℕ} [NeZero d]

def orderedTransportDistribution
    (W : SchwartzNPoint d m →L[ℂ] ℂ) :
    SchwartzNPoint d m →L[ℂ] ℂ :=
  W.comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (section43DiffCoordRealCLE d m).symm)

/-- Transport an ordered-coordinate spacetime distribution back to reduced
difference coordinates.  This is the inverse of
`orderedTransportDistribution`. -/
def reducedTransportDistribution
    (W : SchwartzNPoint d m →L[ℂ] ℂ) :
    SchwartzNPoint d m →L[ℂ] ℂ :=
  W.comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (section43DiffCoordRealCLE d m))

omit [NeZero d] in
@[simp]
theorem orderedTransportDistribution_reducedTransportDistribution
    (W : SchwartzNPoint d m →L[ℂ] ℂ) :
    orderedTransportDistribution (reducedTransportDistribution W) = W := by
  ext F
  apply congrArg W
  ext x
  simp [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

@[simp]
theorem orderedTransportDistribution_orderedPullbackTimeSpatialTensor
    (W : SchwartzNPoint d m →L[ℂ] ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d m) ℂ)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) :
    orderedTransportDistribution W
        (section43OrderedPullbackTimeSpatialTensorCLM d m χ φ) =
      W (section43TimeSpatialTensorCLM d m χ φ) := by
  apply congrArg W
  ext x
  simp [section43OrderedPullbackTimeSpatialTensorCLM]

theorem orderedTransportDistribution_cutoff
    (W : SchwartzNPoint d m →L[ℂ] ℂ)
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (F : SchwartzNPoint d m) :
    orderedTransportDistribution W
        (section43OrderedPullbackFullCutoffCLM d m η F) =
      W (SchwartzMap.smulLeftCLM ℂ
        (section43NPointTimeCutoffWeight d m η) F) := by
  apply congrArg W
  ext x
  simp [section43OrderedPullbackFullCutoffCLM]

end OSIIChapterV
end OSReconstruction
