/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621NormalizedAllArityRankSeed
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIITimeSpatialCurrying













noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace StrictGeneratedScalarDepthPointedData

open Section43ProductTimeApproximateIdentity
open Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData

variable {d : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

/-- Adding a nonnegative real amount to every physical time gap preserves a
mixed-tail carrier.  The right-half-plane condition is immediate, while the
principal arguments shrink coordinatewise and hence remain in the same
strict-generated mixed rank stratum. -/
theorem osiiVI2Shift_mem_mixedTailArgumentCarrier
    {m depth rank : Nat}
    {w : OSIITimeGapSpace m}
    (hw : w ∈ osiiMixedTailArgumentCarrier
      (osiiStrictGeneratedMixedLogarithmicBaseAtRank
        (m + 1) depth rank))
    {epsilon : Real} (hepsilon : 0 <= epsilon) :
    osiiVI2Shift m epsilon w ∈
      osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          (m + 1) depth rank) := by
  let shifted := osiiVI2Shift m epsilon w
  have hshiftedRight : shifted ∈ osiiTimeRightHalfPlane m := by
    intro j
    change 0 < (w j + epsilon).re
    simpa using add_pos_of_pos_of_nonneg (hw.1 j) hepsilon
  have hshrink : forall j,
      |osiiTimeArgumentVector shifted j| <=
        |osiiTimeArgumentVector w j| := by
    intro j
    exact abs_arg_add_ofReal_le (hw.1 j) hepsilon
  have htail : IsMixedTailRankSuccessorSeed
      rank m depth (osiiTimeArgumentVector w) :=
    ⟨Fin.cons 0 (osiiTimeArgumentVector w), hw.2, by
      funext j
      simp [Fin.tail]⟩
  obtain ⟨y, hy, hyTail⟩ :=
    htail.coordinatewiseShrink (osiiTimeArgumentVector shifted) hshrink
  have hyEq : y = Fin.cons 0 (osiiTimeArgumentVector shifted) := by
    funext j
    refine Fin.cases ?_ (fun a => ?_) j
    · exact
        OSIIStrictGeneratedLogarithmicArgumentAtRank.mixed_head_eq_zero
          (by omega : 1 <= m + 1) hy
    · have hya := congrFun hyTail a
      simpa [Fin.tail] using hya
  refine ⟨hshiftedRight, ?_⟩
  rw [← hyEq]
  exact hy

namespace Equation621CanonicalVacuumTailSourceSample

end Equation621CanonicalVacuumTailSourceSample

namespace Equation621CanonicalPositiveRankVacuumTailLocalShiftCoverageData

end Equation621CanonicalPositiveRankVacuumTailLocalShiftCoverageData

namespace Equation621NormalizedAllArityRankSeedData

end Equation621NormalizedAllArityRankSeedData

namespace Equation621NormalizedAdaptiveAllArityRankTubeProfileData

end Equation621NormalizedAdaptiveAllArityRankTubeProfileData

namespace Equation621CanonicalPositiveRankVacuumTailAdaptiveProfileInputData

namespace SelectedTargetCoreFamilyData

end SelectedTargetCoreFamilyData
end Equation621CanonicalPositiveRankVacuumTailAdaptiveProfileInputData

namespace Equation621CanonicalPositiveRankVacuumTailLocalShiftCoverageData

end Equation621CanonicalPositiveRankVacuumTailLocalShiftCoverageData

namespace Equation621CanonicalPositiveRankVacuumTailAdaptiveProfileInputData
namespace SelectedTargetCoreFamilyData

end SelectedTargetCoreFamilyData

end Equation621CanonicalPositiveRankVacuumTailAdaptiveProfileInputData

namespace Equation621CanonicalVacuumTailSourceCoreData

end Equation621CanonicalVacuumTailSourceCoreData

namespace Equation621CanonicalVacuumTailSourceRankCoreData

end Equation621CanonicalVacuumTailSourceRankCoreData

namespace Equation621CanonicalVacuumTailRawSourceRankBoundData

end Equation621CanonicalVacuumTailRawSourceRankBoundData

end StrictGeneratedScalarDepthPointedData
end OSIIChapterV
end OSReconstruction
