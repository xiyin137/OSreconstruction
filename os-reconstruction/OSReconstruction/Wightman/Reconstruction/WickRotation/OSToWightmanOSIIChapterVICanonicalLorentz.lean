/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIForwardTubeLorentzCovariance
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVICanonicalTubeIdentification









noncomputable section

open Complex Set

namespace OSReconstruction
namespace OSIIChapterV.InitialGeneratedLogarithmicStageLevelData

variable {d : Nat} [NeZero d] {OS : OsterwalderSchraderAxioms d}

theorem strictGeneratedForwardTube_complexLorentzInvariant
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat)
    (L : ComplexLorentzGroup d) (z : Fin k -> Fin (d + 1) -> Complex)
    (hz : z ∈ TubeDomainSetPi (BHW.ProductForwardConeReal d k))
    (hLz : BHW.complexLorentzAction L z ∈ TubeDomainSetPi (BHW.ProductForwardConeReal d k)) :
    (initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k).kernel
        (BHW.complexLorentzAction L z) =
      (initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k).kernel z :=
  (initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k).complexLorentzInvariant
    (initial.toStrictGeneratedFullTimeContinuationStage_hasCanonicalReducedCompactStageEdges lgc k)
    (initial.toStrictGeneratedForwardTubeTimeSliceRealizationDataOfOSII lgc k) L z hz hLz

theorem strictGeneratedForwardTube_realLorentzInvariant
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat)
    (L : LorentzLieGroup.RestrictedLorentzGroup d)
    (z : Fin k -> Fin (d + 1) -> Complex)
    (hz : z ∈ TubeDomainSetPi (BHW.ProductForwardConeReal d k)) :
    (initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k).kernel
        (BHW.complexLorentzAction (ComplexLorentzGroup.ofReal L) z) =
      (initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k).kernel z :=
  (initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k).realLorentzInvariant
    (initial.toStrictGeneratedFullTimeContinuationStage_hasCanonicalReducedCompactStageEdges lgc k)
    (initial.toStrictGeneratedForwardTubeTimeSliceRealizationDataOfOSII lgc k) L z hz

/-- The existing reduced analytic interface now has an actual original-OS
producer, retaining the same kernel and the same native boundary. -/
def toStrictGeneratedReducedForwardTubeInputOfOSII
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat) :
    BHW.ReducedForwardTubeInput
      (fun m phi => (initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc m).reducedBoundary phi) k where
  toFun := (initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k).kernel
  holomorphic := (initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k).holomorphic
  real_lorentz_invariant := by
    intro L z hz hLz
    exact initial.strictGeneratedForwardTube_complexLorentzInvariant lgc k
      (ComplexLorentzGroup.ofReal (wightmanToLorentzGroup L)) z hz hLz
  boundary_values := by
    intro phi eta heta
    exact (initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k).boundaryValue eta heta phi

@[simp] theorem toStrictGeneratedReducedForwardTubeInputOfOSII_toFun
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat) :
    (initial.toStrictGeneratedReducedForwardTubeInputOfOSII lgc k).toFun =
      (initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k).kernel := rfl

end OSIIChapterV.InitialGeneratedLogarithmicStageLevelData
end OSReconstruction
