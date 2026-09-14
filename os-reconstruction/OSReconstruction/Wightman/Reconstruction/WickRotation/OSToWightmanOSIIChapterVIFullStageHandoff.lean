/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedPointedDepthInduction
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRealEdgeRegularizedGrowth
















noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d : ℕ} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

namespace InitialGeneratedLogarithmicStageLevelData

variable
  (D : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
  (lgc : OSLinearGrowthCondition d OS)
  (arity : ℕ)

/-- The strict-generated endpoint has exactly the full product
right-half-plane carrier. -/
@[simp] theorem toStrictGeneratedFullTimeContinuationStage_carrier :
    (D.toStrictGeneratedFullTimeContinuationStage lgc arity).carrier =
      osiiTimeRightHalfPlane arity := by
  rfl

/-- A uniform Vladimirov estimate for the constructed finite-stage ladder
gives the exact global Chapter VI growth package for the strict-generated
full stage. -/
def toStrictGeneratedFullTimeStageGrowthData
    (G : OSIITimeContinuationLadderVladimirovGrowthData
      (D.toStrictGeneratedTimeContinuationLadder lgc arity)) :
    OSIIFullTimeStageVladimirovGrowthData
      (D.toStrictGeneratedFullTimeContinuationStage lgc arity) := by
  simpa [toStrictGeneratedFullTimeContinuationStage] using
    G.toFullTimeStageGrowthData

/-- The strict-generated arity-zero stage has Chapter VI growth
automatically; no Step-4 regularization or boundary-distance estimate is
needed. -/
noncomputable def toStrictGeneratedZeroArityFullTimeStageGrowthData
    (D : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) :
    OSIIFullTimeStageVladimirovGrowthData
      (D.toStrictGeneratedFullTimeContinuationStage lgc 0) :=
  D.toStrictGeneratedFullTimeStageGrowthData lgc 0
    (OSIITimeContinuationLadderVladimirovGrowthData.ofZeroArity
      (D.toStrictGeneratedTimeContinuationLadder lgc 0))

end InitialGeneratedLogarithmicStageLevelData

end OSIIChapterV
end OSReconstruction
