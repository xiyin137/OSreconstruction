/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
module

public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVICanonicalSpectrum
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIForwardTubeBoundaryIdentification
public import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIForwardTubeEuclideanIdentification

@[expose] public section

noncomputable section

open Complex Set

namespace OSReconstruction
namespace OSIIChapterV.InitialGeneratedLogarithmicStageLevelData

variable {d : Nat} [NeZero d] {OS : OsterwalderSchraderAxioms d}

/-- The existing pure-time realization interface, now constructed for the
actual physical forward tube at every arity. -/
def toStrictGeneratedForwardTubeTimeSliceRealizationDataOfOSII
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat) :
    OSIIReducedForwardTubeTimeSliceRealizationData
      (A := initial.toStrictGeneratedFullTimeContinuationStage lgc k)
      (initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k) :=
  (initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k
    ).toForwardTubeTimeSliceRealizationData
      (initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k)

end OSIIChapterV.InitialGeneratedLogarithmicStageLevelData
end OSReconstruction
