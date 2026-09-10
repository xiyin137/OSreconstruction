/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RealEdgeSeed











noncomputable section

open Complex Set
open scoped Classical

namespace OSReconstruction

theorem osiiVI2TimeAverageBase_ne_zero_of_rightHalfPlane
    {k : Nat} (hk : 0 < k)
    {zeta : OSIITimeGapSpace k}
    (hzeta : zeta ∈ osiiTimeRightHalfPlane k) :
    osiiVI2TimeAverageBase k zeta ≠ 0 := by
  apply Complex.ne_zero_of_re_pos
  have hkR : 0 < (k : Real) := by exact_mod_cast hk
  have hsum : 0 < 1 + ∑ i : Fin k, (zeta i).re := by
    have : 0 <= ∑ i : Fin k, (zeta i).re :=
      Finset.sum_nonneg fun i _ => (hzeta i).le
    linarith
  simpa [osiiVI2TimeAverageBase] using div_pos hsum hkR

/-- The complex time average is controlled by the standard polynomial time
weight on the right-half-plane route; the estimate itself needs only
positive arity. -/
theorem norm_osiiVI2TimeAverageBase_le
    {k : Nat} (hk : 0 < k)
    (zeta : OSIITimeGapSpace k) :
    ‖osiiVI2TimeAverageBase k zeta‖ <= 1 + ‖zeta‖ := by
  have hkR : 0 < (k : Real) := by exact_mod_cast hk
  have hsum :
      ‖∑ i : Fin k, zeta i‖ <= (k : Real) * ‖zeta‖ := by
    calc
      ‖∑ i : Fin k, zeta i‖ <= ∑ i : Fin k, ‖zeta i‖ :=
        norm_sum_le _ _
      _ <= ∑ _i : Fin k, ‖zeta‖ := by
        gcongr with i hi
        exact norm_le_pi_norm zeta i
      _ = (k : Real) * ‖zeta‖ := by simp
  have hnum : ‖(1 : Complex) + ∑ i : Fin k, zeta i‖ <=
      (k : Real) * (1 + ‖zeta‖) := by
    calc
      ‖(1 : Complex) + ∑ i : Fin k, zeta i‖ <=
          1 + ‖∑ i : Fin k, zeta i‖ := by
        simpa using norm_add_le (1 : Complex) (∑ i : Fin k, zeta i)
      _ <= 1 + (k : Real) * ‖zeta‖ := by linarith
      _ <= (k : Real) * (1 + ‖zeta‖) := by
        have hk_one : (1 : Real) <= k := by exact_mod_cast hk
        nlinarith [norm_nonneg zeta]
  rw [osiiVI2TimeAverageBase, norm_div, Complex.norm_natCast]
  rw [div_le_iff₀ hkR]
  simpa [mul_comm] using hnum

theorem norm_osiiVI2TimeDenormalization_le
    {k : Nat} (hk : 0 < k)
    (t : Nat) (zeta : OSIITimeGapSpace k) :
    ‖osiiVI2TimeDenormalization t k zeta‖ <=
      (1 + ‖zeta‖) ^ (k * t) := by
  rw [osiiVI2TimeDenormalization, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_osiiVI2TimeAverageBase_le hk zeta) _

/-- The complete reciprocal scalar cancels the complete normalization at any
unshifted point where the printed time-average denominator is nonzero. -/
theorem osiiVI2Equation621Denormalization_mul_normalization_unshift_of_timeAverage_ne_zero
    {k : Nat} (hk : 0 < k)
    (t : Nat) {epsilon : Real} (hepsilon : 0 < epsilon)
    {zeta : OSIITimeGapSpace k}
    (hbase : osiiVI2TimeAverageBase k zeta ≠ 0) :
    osiiVI2Equation621Denormalization t k epsilon zeta *
        osiiVI2Equation621Normalization t k epsilon
          (osiiVI2Unshift k epsilon zeta) = 1 := by
  have htime :
      osiiVI2TimeDenormalization t k zeta *
          osiiVI2TimeNormalization t k epsilon
            (osiiVI2Unshift k epsilon zeta) = 1 := by
    simp only [osiiVI2TimeDenormalization, osiiVI2TimeNormalization,
      osiiVI2Shift_unshift]
    rw [← mul_pow, mul_inv_cancel₀ hbase, one_pow]
  have hepsilonR :=
    osiiVI2Denormalization_mul_normalization hk hepsilon t
  have hepsilonC :
      (osiiVI2Denormalization t k epsilon : Complex) *
          (osiiVI2Normalization t k epsilon : Complex) = 1 := by
    exact_mod_cast hepsilonR
  rw [osiiVI2Equation621Denormalization,
    osiiVI2Equation621Normalization]
  calc
    (osiiVI2TimeDenormalization t k zeta *
          (osiiVI2Denormalization t k epsilon : Complex)) *
        (osiiVI2TimeNormalization t k epsilon
            (osiiVI2Unshift k epsilon zeta) *
          (osiiVI2Normalization t k epsilon : Complex)) =
      (osiiVI2TimeDenormalization t k zeta *
        osiiVI2TimeNormalization t k epsilon
          (osiiVI2Unshift k epsilon zeta)) *
        ((osiiVI2Denormalization t k epsilon : Complex) *
          (osiiVI2Normalization t k epsilon : Complex)) := by ring
    _ = 1 := by rw [htime, hepsilonC, one_mul]

/-- Right-half-plane specialization of exact equation-`(6.21)`
cancellation. -/
theorem osiiVI2Equation621Denormalization_mul_normalization_unshift
    {k : Nat} (hk : 0 < k)
    (t : Nat) {epsilon : Real} (hepsilon : 0 < epsilon)
    {zeta : OSIITimeGapSpace k}
    (hzeta : zeta ∈ osiiTimeRightHalfPlane k) :
    osiiVI2Equation621Denormalization t k epsilon zeta *
        osiiVI2Equation621Normalization t k epsilon
          (osiiVI2Unshift k epsilon zeta) = 1 :=
  osiiVI2Equation621Denormalization_mul_normalization_unshift_of_timeAverage_ne_zero
    hk t hepsilon (osiiVI2TimeAverageBase_ne_zero_of_rightHalfPlane hk hzeta)

/-- Canonical full denormalization has both the expected polynomial-time and
inverse-boundary costs. -/
theorem norm_osiiVI2Equation621Denormalization_canonical_le
    {k : Nat} (hk : 0 < k)
    {zeta : OSIITimeGapSpace k}
    (hzeta : zeta ∈ osiiTimeRightHalfPlane k)
    (t : Nat) :
    ‖osiiVI2Equation621Denormalization t k
        (osiiVI2CanonicalEpsilon k zeta) zeta‖ <=
      3 ^ (k * t) * (1 + ‖zeta‖) ^ (k * t) *
        (1 + (osiiTimeBoundaryDistance k zeta)⁻¹) ^ (k * t) := by
  have htime := norm_osiiVI2TimeDenormalization_le hk t zeta
  have hepsilon := osiiVI2CanonicalDenormalization_le hk hzeta t
  rw [osiiVI2Equation621Denormalization, norm_mul, Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_pos (osiiVI2Denormalization_pos hk
      (osiiVI2CanonicalEpsilon_pos hk hzeta) t)]
  calc
    ‖osiiVI2TimeDenormalization t k zeta‖ *
        osiiVI2Denormalization t k
          (osiiVI2CanonicalEpsilon k zeta) <=
      (1 + ‖zeta‖) ^ (k * t) *
        (3 ^ (k * t) *
          (1 + (osiiTimeBoundaryDistance k zeta)⁻¹) ^ (k * t)) := by
      exact mul_le_mul htime hepsilon
        (osiiVI2Denormalization_pos hk
          (osiiVI2CanonicalEpsilon_pos hk hzeta) t).le
        (pow_nonneg (by positivity) _)
    _ = 3 ^ (k * t) * (1 + ‖zeta‖) ^ (k * t) *
        (1 + (osiiTimeBoundaryDistance k zeta)⁻¹) ^ (k * t) := by ring

namespace OSIITimeContinuationStage

variable {d k : Nat}

/-- Exact recovery of the original continuation family from the complete
equation-`(6.21)` normalized stage at every point where its time-average
denominator is nonzero. -/
theorem vi2Equation621Denormalization_smul_normalized_unshift_of_timeAverage_ne_zero
    (A : OSIITimeContinuationStage d k)
    (hk : 0 < k)
    (t : Nat) {epsilon : Real} (hepsilon : 0 < epsilon)
    {zeta : OSIITimeGapSpace k}
    (hbase : osiiVI2TimeAverageBase k zeta ≠ 0) :
    osiiVI2Equation621Denormalization t k epsilon zeta •
        (A.vi2Equation621NormalizedStage t epsilon).distribution
          (osiiVI2Unshift k epsilon zeta) =
      A.distribution zeta := by
  ext chi
  simp only [vi2Equation621NormalizedStage_distribution_apply,
    osiiVI2Shift_unshift, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [← mul_assoc,
    osiiVI2Equation621Denormalization_mul_normalization_unshift_of_timeAverage_ne_zero
      hk t hepsilon hbase, one_mul]

/-- A bound on the complete normalized family recovers the raw family at
every point where the printed time-average denominator is nonzero. -/
theorem norm_distribution_le_of_equation621Normalized_of_timeAverage_ne_zero
    (A : OSIITimeContinuationStage d k)
    (hk : 0 < k)
    (t : Nat)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    {zeta : OSIITimeGapSpace k}
    (hbase : osiiVI2TimeAverageBase k zeta ≠ 0)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (B : Real)
    (hbound :
      ‖(A.vi2Equation621NormalizedStage t epsilon).distribution
          (osiiVI2Unshift k epsilon zeta) chi‖ <= B) :
    ‖A.distribution zeta chi‖ <=
      ‖osiiVI2Equation621Denormalization t k epsilon zeta‖ * B := by
  have hrecovery := congrArg
    (fun T : OSIISpatialDistribution d k => T chi)
    (A.vi2Equation621Denormalization_smul_normalized_unshift_of_timeAverage_ne_zero
      hk t hepsilon hbase)
  calc
    ‖A.distribution zeta chi‖ =
        ‖osiiVI2Equation621Denormalization t k epsilon zeta •
          (A.vi2Equation621NormalizedStage t epsilon).distribution
            (osiiVI2Unshift k epsilon zeta) chi‖ := by
      simpa using congrArg norm hrecovery.symm
    _ = ‖osiiVI2Equation621Denormalization t k epsilon zeta‖ *
        ‖(A.vi2Equation621NormalizedStage t epsilon).distribution
          (osiiVI2Unshift k epsilon zeta) chi‖ := norm_smul _ _
    _ <= ‖osiiVI2Equation621Denormalization t k epsilon zeta‖ * B :=
      mul_le_mul_of_nonneg_left hbound (norm_nonneg _)

theorem norm_distribution_le_of_equation621Normalized
    (A : OSIITimeContinuationStage d k)
    (hk : 0 < k)
    (t : Nat)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    {zeta : OSIITimeGapSpace k}
    (hzeta : zeta ∈ osiiTimeRightHalfPlane k)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (B : Real)
    (hbound :
      ‖(A.vi2Equation621NormalizedStage t epsilon).distribution
          (osiiVI2Unshift k epsilon zeta) chi‖ <= B) :
    ‖A.distribution zeta chi‖ <=
      ‖osiiVI2Equation621Denormalization t k epsilon zeta‖ * B := by
  exact A.norm_distribution_le_of_equation621Normalized_of_timeAverage_ne_zero
    hk t hepsilon
    (osiiVI2TimeAverageBase_ne_zero_of_rightHalfPlane hk hzeta)
    chi B hbound

/-- Canonical recovery from a bounded complete normalized family. -/
theorem norm_distribution_le_of_equation621Normalized_canonical
    (A : OSIITimeContinuationStage d k)
    (hk : 0 < k)
    (t : Nat)
    {zeta : OSIITimeGapSpace k}
    (hzeta : zeta ∈ osiiTimeRightHalfPlane k)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (B : Real)
    (hbound :
      ‖(A.vi2Equation621NormalizedStage t
          (osiiVI2CanonicalEpsilon k zeta)).distribution
          (osiiVI2Unshift k (osiiVI2CanonicalEpsilon k zeta) zeta) chi‖ <=
        B) :
    ‖A.distribution zeta chi‖ <=
      3 ^ (k * t) * (1 + ‖zeta‖) ^ (k * t) *
        (1 + (osiiTimeBoundaryDistance k zeta)⁻¹) ^ (k * t) * B := by
  have hB : 0 <= B := (norm_nonneg _).trans hbound
  calc
    ‖A.distribution zeta chi‖ <=
        ‖osiiVI2Equation621Denormalization t k
          (osiiVI2CanonicalEpsilon k zeta) zeta‖ * B :=
      A.norm_distribution_le_of_equation621Normalized hk t
        (osiiVI2CanonicalEpsilon_pos hk hzeta) hzeta chi B hbound
    _ <= (3 ^ (k * t) * (1 + ‖zeta‖) ^ (k * t) *
          (1 + (osiiTimeBoundaryDistance k zeta)⁻¹) ^ (k * t)) * B :=
      mul_le_mul_of_nonneg_right
        (norm_osiiVI2Equation621Denormalization_canonical_le hk hzeta t) hB
    _ = 3 ^ (k * t) * (1 + ‖zeta‖) ^ (k * t) *
        (1 + (osiiTimeBoundaryDistance k zeta)⁻¹) ^ (k * t) * B := by ring

/-- Total-arity wrapper: equation `(6.21)` starts at positive arity, while
the vacuum (`k = 0`) is left unchanged. -/
noncomputable def vi2Equation621TotalNormalizedStage
    (A : OSIITimeContinuationStage d k)
    (t : Nat) (epsilon : Real) : OSIITimeContinuationStage d k :=
  if 0 < k then A.vi2Equation621NormalizedStage t epsilon else A

theorem vi2Equation621TotalNormalizedStage_eq_of_pos
    (A : OSIITimeContinuationStage d k)
    (hk : 0 < k) (t : Nat) (epsilon : Real) :
    A.vi2Equation621TotalNormalizedStage t epsilon =
      A.vi2Equation621NormalizedStage t epsilon := by
  simp [vi2Equation621TotalNormalizedStage, hk]

theorem vi2Equation621TotalNormalizedStage_eq_of_not_pos
    (A : OSIITimeContinuationStage d k)
    (hk : ¬ 0 < k) (t : Nat) (epsilon : Real) :
    A.vi2Equation621TotalNormalizedStage t epsilon = A := by
  simp [vi2Equation621TotalNormalizedStage, hk]

/-- A legacy normalized target in the product right half-plane belongs to
the complete normalized carrier.  The only new carrier condition is
nonvanishing of the printed time average, supplied by positivity. -/
theorem mem_vi2Equation621TotalNormalizedStage_of_mem_vi2NormalizedStage_of_rightHalfPlane
    (A : OSIITimeContinuationStage d k)
    (t : Nat)
    {epsilon : Real} (hepsilon : 0 <= epsilon)
    {zeta : OSIITimeGapSpace k}
    (hlegacy : zeta ∈ (A.vi2NormalizedStage t epsilon).carrier)
    (hright : zeta ∈ osiiTimeRightHalfPlane k) :
    zeta ∈ (A.vi2Equation621TotalNormalizedStage t epsilon).carrier := by
  by_cases hk : 0 < k
  · rw [A.vi2Equation621TotalNormalizedStage_eq_of_pos hk]
    refine ⟨hlegacy, ?_⟩
    apply osiiVI2TimeAverageBase_ne_zero_of_rightHalfPlane hk
    intro i
    change 0 < (zeta i).re + epsilon
    exact add_pos_of_pos_of_nonneg (hright i) hepsilon
  · have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    subst k
    rw [A.vi2Equation621TotalNormalizedStage_eq_of_not_pos (by omega)]
    have hshift : osiiVI2Shift 0 epsilon zeta = zeta :=
      Subsingleton.elim _ _
    simpa [vi2NormalizedStage_carrier, hshift] using hlegacy

end OSIITimeContinuationStage
end OSReconstruction
