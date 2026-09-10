/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRawGeneratedNormalizedWeightedL1RankLocalShellFirstRecovery











noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

open Section43ProductTimeApproximateIdentity
open Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData

/-- Complete VI.2 normalization cancels one parent denormalization at the
same physical target. -/
theorem norm_equation621Normalized_le_of_distribution_le_denormalization
    {d k t : Nat} [NeZero d] [NeZero k]
    (A : OSIITimeContinuationStage d k)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    {zeta : OSIITimeGapSpace k}
    (hzeta : zeta ∈ osiiTimeRightHalfPlane k)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (B : Real)
    (hbound :
      ‖A.distribution zeta chi‖ <=
        B * ‖osiiVI2Equation621Denormalization t k epsilon zeta‖) :
    ‖(A.vi2Equation621NormalizedStage t epsilon).distribution
        (osiiVI2Unshift k epsilon zeta) chi‖ <= B := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hcancel := congrArg norm
    (osiiVI2Equation621Denormalization_mul_normalization_unshift
      hk t hepsilon hzeta)
  have hcancelNorm :
      ‖osiiVI2Equation621Normalization t k epsilon
          (osiiVI2Unshift k epsilon zeta)‖ *
        ‖osiiVI2Equation621Denormalization t k epsilon zeta‖ = 1 := by
    simpa [norm_mul, mul_comm] using hcancel
  rw [A.vi2Equation621NormalizedStage_distribution_apply,
    osiiVI2Shift_unshift, norm_mul]
  calc
    ‖osiiVI2Equation621Normalization t k epsilon
        (osiiVI2Unshift k epsilon zeta)‖ *
        ‖A.distribution zeta chi‖ <=
      ‖osiiVI2Equation621Normalization t k epsilon
          (osiiVI2Unshift k epsilon zeta)‖ *
        (B * ‖osiiVI2Equation621Denormalization t k epsilon zeta‖) :=
      mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
    _ = B *
        (‖osiiVI2Equation621Normalization t k epsilon
            (osiiVI2Unshift k epsilon zeta)‖ *
          ‖osiiVI2Equation621Denormalization t k epsilon zeta‖) := by ring
    _ = B := by rw [hcancelNorm, mul_one]

end OSIIChapterV
end OSReconstruction
