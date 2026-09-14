/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVICanonicalBoundaryWard
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBoostConeTransport
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIForwardConeDuality
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIForwardTubeFromSpectrum









noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV.InitialGeneratedLogarithmicStageLevelData

variable {d : Nat} [NeZero d] {OS : OsterwalderSchraderAxioms d}

theorem strictGeneratedFrequency_boost_eq
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat) (a : Fin d) (t : Real)
    (phi : SchwartzMap (Fin (k * (d + 1)) -> Real) Complex) :
    osiiCanonicalFrequencyDistribution
        (initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k).reducedBoundary
        (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (osiiFlatBoostCLE d k a t) phi) =
      osiiCanonicalFrequencyDistribution
        (initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k).reducedBoundary phi :=
  osiiCanonicalFrequencyDistribution_boost_eq a _
    (fun s f => initial.strictGeneratedReducedBoundary_boost_eq lgc a s f) t phi

/-- Actual inverse-transpose Lorentz transport from the original E1 input. -/
theorem strictGeneratedFrequency_lorentzTransport
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat) :
    OSIICanonicalFrequencyLorentzTransport d k
      (osiiCanonicalFrequencyDistribution
        (initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k).reducedBoundary) :=
  osiiCanonicalFrequencyLorentzTransport_of_boosts _
    (fun a t phi => initial.strictGeneratedFrequency_boost_eq lgc k a t phi)

/-- The actual all-arity boundary has temporal support. At zero gap arity
the temporal cylinder is the entire singleton frequency space. -/
theorem strictGeneratedFrequency_temporalVanishing
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat) :
    Distribution.IsVanishingOn
      (osiiCanonicalFrequencyDistribution
        (initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k).reducedBoundary)
      (osiiCanonicalFrequencyTemporalCylinder d k)ᶜ := by
  cases k with
  | zero =>
    intro phi hphi
    have hzero : phi = 0 := by
      ext p
      by_contra hp
      exact hphi (subset_tsupport _ (Function.mem_support.mpr hp))
        ((mem_osiiCanonicalFrequencyTemporalCylinder_iff p).mpr (fun j => Fin.elim0 j))
    rw [hzero, map_zero]
  | succ q =>
    exact (initial.toStrictGeneratedFullTimeStageGrowthDataOfOSII lgc (q + 1)
      ).osiiCanonicalFrequencyDistribution_isVanishingOn_compl_temporalCylinder

/-- Full product forward-cone spectrum on every Schwartz test, from exactly
the corrected OS-II input. No boundary-to-spectrum axiom is used. -/
theorem strictGeneratedFrequency_support
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat) :
    HasFourierSupportInDualCone (osiiReducedForwardFlatCone d k)
      (osiiCanonicalFrequencyDistribution
        (initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k).reducedBoundary) :=
  osiiCanonicalFrequency_support_of_temporalVanishing_of_lorentzTransport _
    (initial.strictGeneratedFrequency_temporalVanishing lgc k)
    (initial.strictGeneratedFrequency_lorentzTransport lgc k)

/-- Populate the existing forward-tube spectral interface with the actual
OS-built boundary and its now-proved full cone support. -/
def toStrictGeneratedForwardTubeBoundarySpectralDataOfOSII
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat) :
    OSIIReducedForwardTubeBoundarySpectralData d k :=
  (initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k
    ).toReducedForwardTubeBoundarySpectralData (initial.strictGeneratedFrequency_support lgc k)

@[simp] theorem toStrictGeneratedForwardTubeBoundarySpectralDataOfOSII_boundary
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat) :
    (initial.toStrictGeneratedForwardTubeBoundarySpectralDataOfOSII lgc k).boundaryDistribution =
      (initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k).reducedBoundary := rfl

/-- A holomorphic physical forward-tube realization of the same original-OS
chronological boundary, with compact-imaginary polynomial growth. Its
Euclidean identification is a separate subsequent obligation. -/
def toStrictGeneratedForwardTubeBoundaryDataOfOSII
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat) :
    OSIIReducedForwardTubeBoundaryData
      (initial.toStrictGeneratedTemperedBoundaryDataOfOSII lgc k).reducedBoundary :=
  let P := initial.toStrictGeneratedForwardTubeBoundarySpectralDataOfOSII lgc k
  P.toSpectralData.toForwardTubeBoundaryData.congrBoundary
    P.toSpectralData_reducedBoundaryDistribution

@[simp] theorem toStrictGeneratedForwardTubeBoundaryDataOfOSII_kernel
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (k : Nat) :
    (initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc k).kernel =
      (initial.toStrictGeneratedForwardTubeBoundarySpectralDataOfOSII lgc k).toSpectralData.kernel := by
  dsimp only [toStrictGeneratedForwardTubeBoundaryDataOfOSII]
  rw [OSIIReducedForwardTubeBoundaryData.congrBoundary_kernel]
  rfl

end OSIIChapterV.InitialGeneratedLogarithmicStageLevelData
end OSReconstruction
