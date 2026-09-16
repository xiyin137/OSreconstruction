/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib.Analysis.MeanInequalities
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRegularizationRadius











noncomputable section

open Complex Set Topology
open scoped BigOperators Classical

namespace OSReconstruction



/-- Add the same real time gap to every complex time coordinate. -/
def osiiVI2Shift
    (k : Nat) (epsilon : Real) (zeta : OSIITimeGapSpace k) :
    OSIITimeGapSpace k :=
  fun i => zeta i + epsilon

/-- Subtract the same real time gap from every complex time coordinate. -/
def osiiVI2Unshift
    (k : Nat) (epsilon : Real) (zeta : OSIITimeGapSpace k) :
    OSIITimeGapSpace k :=
  fun i => zeta i - epsilon

@[simp] theorem osiiVI2Shift_apply
    (k : Nat) (epsilon : Real) (zeta : OSIITimeGapSpace k) (i : Fin k) :
    osiiVI2Shift k epsilon zeta i = zeta i + epsilon :=
  rfl

@[simp] theorem osiiVI2Unshift_apply
    (k : Nat) (epsilon : Real) (zeta : OSIITimeGapSpace k) (i : Fin k) :
    osiiVI2Unshift k epsilon zeta i = zeta i - epsilon :=
  rfl

@[simp] theorem osiiVI2Shift_unshift
    (k : Nat) (epsilon : Real) (zeta : OSIITimeGapSpace k) :
    osiiVI2Shift k epsilon (osiiVI2Unshift k epsilon zeta) = zeta := by
  ext i
  simp [osiiVI2Shift, osiiVI2Unshift]

@[simp] theorem osiiVI2Unshift_shift
    (k : Nat) (epsilon : Real) (zeta : OSIITimeGapSpace k) :
    osiiVI2Unshift k epsilon (osiiVI2Shift k epsilon zeta) = zeta := by
  ext i
  simp [osiiVI2Shift, osiiVI2Unshift]

/-- A nonnegative VI.2 shift moves a positive-arity right-half-plane point
at least that far from the boundary.

The boundary distance is measured in the real time-gap coordinates with the
sup norm.  Any point outside the positive orthant has one nonpositive
coordinate, while every shifted coordinate is at least `epsilon` above it. -/
theorem osiiTimeBoundaryDistance_shift_ge
    {k : Nat}
    (hk : 0 < k)
    (zeta : OSIITimeGapSpace k)
    (hzeta : zeta ∈ osiiTimeRightHalfPlane k)
    (epsilon : Real)
    (hepsilon : 0 <= epsilon) :
    epsilon <=
      osiiTimeBoundaryDistance k (osiiVI2Shift k epsilon zeta) := by
  change
    epsilon <=
      Metric.infDist
        (fun i => (osiiVI2Shift k epsilon zeta i).re)
        (osiiTimePositiveCone k)ᶜ
  refine (Metric.le_infDist ?_).2 ?_
  · refine ⟨0, ?_⟩
    intro hzero
    have hcoord := hzero (⟨0, hk⟩ : Fin k)
    simp [osiiTimePositiveCone] at hcoord
  · intro y hy
    have hy_not : y ∉ osiiTimePositiveCone k := hy
    simp only [osiiTimePositiveCone, section43TimeStrictPositiveRegion,
      Set.mem_setOf_eq, not_forall, not_lt] at hy_not
    obtain ⟨i, hyi⟩ := hy_not
    calc
      epsilon <= dist ((osiiVI2Shift k epsilon zeta i).re) (y i) := by
        rw [Real.dist_eq]
        have hdiff :
            0 <= (osiiVI2Shift k epsilon zeta i).re - y i := by
          simp only [osiiVI2Shift_apply, Complex.add_re, Complex.ofReal_re]
          linarith [hzeta i]
        rw [abs_of_nonneg hdiff]
        simp only [osiiVI2Shift_apply, Complex.add_re, Complex.ofReal_re]
        linarith [hzeta i]
      _ <= dist
          (fun j => (osiiVI2Shift k epsilon zeta j).re) y :=
        dist_le_pi_dist
          (fun j => (osiiVI2Shift k epsilon zeta j).re) y i

/-- The target-dependent fixed shift used to undo equation `(6.21)`. -/
def osiiVI2CanonicalEpsilon
    (k : Nat) (zeta : OSIITimeGapSpace k) : Real :=
  osiiChapterVIRegularizationRadius k zeta / 2

theorem osiiVI2CanonicalEpsilon_pos
    {k : Nat} (hk : 0 < k)
    {zeta : OSIITimeGapSpace k}
    (hzeta : zeta ∈ osiiTimeRightHalfPlane k) :
    0 < osiiVI2CanonicalEpsilon k zeta := by
  exact div_pos (osiiChapterVIRegularizationRadius_pos hk hzeta) (by norm_num)

/-- Any shift no larger than the canonical one still leaves the unshifted
target in the product right half-plane. -/
theorem osiiVI2Unshift_mem_rightHalfPlane_of_le_canonical
    {k : Nat} (hk : 0 < k)
    {zeta : OSIITimeGapSpace k}
    (hzeta : zeta ∈ osiiTimeRightHalfPlane k)
    {epsilon : Real}
    (hepsilon_le : epsilon <= osiiVI2CanonicalEpsilon k zeta) :
    osiiVI2Unshift k epsilon zeta ∈
      osiiTimeRightHalfPlane k := by
  intro i
  have hrho_pos : 0 < osiiChapterVIRegularizationRadius k zeta :=
    osiiChapterVIRegularizationRadius_pos hk hzeta
  have hrho_le :
      osiiChapterVIRegularizationRadius k zeta <= (zeta i).re :=
    osiiChapterVIRegularizationRadius_le_re hzeta i
  change 0 < (zeta i).re - epsilon
  change epsilon <= osiiChapterVIRegularizationRadius k zeta / 2 at hepsilon_le
  linarith

/-- Subtracting the canonical fixed shift preserves every positive real time
gap. -/
theorem osiiVI2CanonicalUnshift_mem_rightHalfPlane
    {k : Nat} (hk : 0 < k)
    {zeta : OSIITimeGapSpace k}
    (hzeta : zeta ∈ osiiTimeRightHalfPlane k) :
    osiiVI2Unshift k (osiiVI2CanonicalEpsilon k zeta) zeta ∈
      osiiTimeRightHalfPlane k := by
  exact
    osiiVI2Unshift_mem_rightHalfPlane_of_le_canonical
      hk hzeta le_rfl



/-- The time-average base in the first factor of OS II `(6.21)`.

The printed formula uses
`(1 + sum_j zeta_j) / k`; its negative `k * t` power cancels the
large-positive-time factor in `(6.20)`. -/
def osiiVI2TimeAverageBase
    (k : Nat) (zeta : OSIITimeGapSpace k) : Complex :=
  (1 + ∑ i : Fin k, zeta i) / (k : Complex)

/-- Positive-real form of the time-average base after the uniform
equation-`(6.21)` shift. -/
def osiiVI2PositiveRealTimeAverageBase
    (k : Nat) (epsilon : Real) (tau : Fin k -> Real) : Real :=
  (1 + ∑ i : Fin k, (tau i + epsilon)) / (k : Real)

/-- The time-dependent factor multiplying the shifted family in OS II
`(6.21)`. -/
def osiiVI2TimeNormalization
    (t k : Nat) (epsilon : Real) (zeta : OSIITimeGapSpace k) : Complex :=
  (osiiVI2TimeAverageBase k (osiiVI2Shift k epsilon zeta))⁻¹ ^ (k * t)

/-- The reciprocal time-average factor at the unshifted physical target. -/
def osiiVI2TimeDenormalization
    (t k : Nat) (zeta : OSIITimeGapSpace k) : Complex :=
  osiiVI2TimeAverageBase k zeta ^ (k * t)

theorem osiiVI2TimeAverageBase_shift_positiveReal
    (k : Nat) (epsilon : Real) (tau : Fin k -> Real) :
    osiiVI2TimeAverageBase k
        (osiiVI2Shift k epsilon (osiiPositiveRealTimeEmbed tau)) =
      (osiiVI2PositiveRealTimeAverageBase k epsilon tau : Complex) := by
  simp only [osiiVI2TimeAverageBase,
    osiiVI2PositiveRealTimeAverageBase, osiiVI2Shift_apply,
    osiiPositiveRealTimeEmbed, Complex.ofReal_add, Complex.ofReal_one,
    Complex.ofReal_natCast, Complex.ofReal_sum, Complex.ofReal_div]

theorem osiiVI2PositiveRealTimeAverageBase_pos
    {k : Nat} (hk : 0 < k)
    {epsilon : Real} (hepsilon : 0 <= epsilon)
    {tau : Fin k -> Real}
    (htau : tau ∈ section43TimeStrictPositiveRegion k) :
    0 < osiiVI2PositiveRealTimeAverageBase k epsilon tau := by
  have hkR : 0 < (k : Real) := by exact_mod_cast hk
  have hsum_nonneg :
      0 <= ∑ i : Fin k, (tau i + epsilon) := by
    exact Finset.sum_nonneg fun i _ => by linarith [htau i]
  exact div_pos (by linarith) hkR

/-- The shifted positive-real time average controls the full finite sup
norm.  This is the elementary comparison that lets the first `(6.21)` factor
absorb the time-growth degree from `(6.20)`. -/
theorem one_add_shifted_pi_norm_le_mul_osiiVI2PositiveRealTimeAverageBase
    {k : Nat} (hk : 0 < k)
    {epsilon : Real} (hepsilon : 0 <= epsilon)
    {tau : Fin k -> Real}
    (htau : tau ∈ section43TimeStrictPositiveRegion k) :
    1 + ‖tau + fun _ : Fin k => epsilon‖ <=
      (k : Real) * osiiVI2PositiveRealTimeAverageBase k epsilon tau := by
  have hcoord_nonneg : forall i : Fin k,
      0 <= (tau + fun _ : Fin k => epsilon) i := by
    intro i
    change 0 <= tau i + epsilon
    linarith [htau i]
  have hnorm := pi_norm_le_sum_of_nonneg hcoord_nonneg
  have hkR : (k : Real) ≠ 0 := ne_of_gt (by exact_mod_cast hk)
  calc
    1 + ‖tau + fun _ : Fin k => epsilon‖ <=
        1 + ∑ i : Fin k, (tau + fun _ : Fin k => epsilon) i := by
      linarith
    _ = (k : Real) *
        osiiVI2PositiveRealTimeAverageBase k epsilon tau := by
      simp only [osiiVI2PositiveRealTimeAverageBase, Pi.add_apply]
      field_simp

/-- A positive time-average reciprocal of degree `k * t` absorbs any
polynomial time growth whose degree fits in that budget. -/
theorem inv_pow_mul_growth_pow_le_arity_pow
    {k p t : Nat} (hk : 0 < k) (hp : p <= k * t)
    {base growth : Real}
    (hbase : 0 < base)
    (hgrowth : 1 <= growth)
    (hcompare : growth <= (k : Real) * base) :
    base⁻¹ ^ (k * t) * growth ^ p <= (k : Real) ^ (k * t) := by
  have hbase_nonneg : 0 <= base := hbase.le
  have hpow_degree : growth ^ p <= growth ^ (k * t) := by
    exact pow_le_pow_right₀ hgrowth hp
  have hpow_compare :
      growth ^ (k * t) <= ((k : Real) * base) ^ (k * t) :=
    pow_le_pow_left₀ (by positivity) hcompare _
  calc
    base⁻¹ ^ (k * t) * growth ^ p <=
        base⁻¹ ^ (k * t) * growth ^ (k * t) :=
      mul_le_mul_of_nonneg_left hpow_degree
        (pow_nonneg (inv_nonneg.mpr hbase_nonneg) _)
    _ <= base⁻¹ ^ (k * t) * ((k : Real) * base) ^ (k * t) :=
      mul_le_mul_of_nonneg_left hpow_compare
        (pow_nonneg (inv_nonneg.mpr hbase_nonneg) _)
    _ = (k : Real) ^ (k * t) := by
      rw [mul_pow]
      calc
        base⁻¹ ^ (k * t) *
            ((k : Real) ^ (k * t) * base ^ (k * t)) =
            (base⁻¹ * base) ^ (k * t) * (k : Real) ^ (k * t) := by
          rw [mul_pow]
          ring
        _ = (k : Real) ^ (k * t) := by
          rw [inv_mul_cancel₀ hbase.ne', one_pow, one_mul]

theorem osiiVI2TimeNormalization_positiveReal_norm_mul_growth_pow_le
    {k p t : Nat} (hk : 0 < k) (hp : p <= k * t)
    {epsilon : Real} (hepsilon : 0 <= epsilon)
    {tau : Fin k -> Real}
    (htau : tau ∈ section43TimeStrictPositiveRegion k) :
    ‖osiiVI2TimeNormalization t k epsilon
        (osiiPositiveRealTimeEmbed tau)‖ *
        (1 + ‖tau + fun _ : Fin k => epsilon‖) ^ p <=
      (k : Real) ^ (k * t) := by
  let base := osiiVI2PositiveRealTimeAverageBase k epsilon tau
  have hbase : 0 < base :=
    osiiVI2PositiveRealTimeAverageBase_pos hk hepsilon htau
  have hcompare :
      1 + ‖tau + fun _ : Fin k => epsilon‖ <= (k : Real) * base := by
    simpa only [base] using
      one_add_shifted_pi_norm_le_mul_osiiVI2PositiveRealTimeAverageBase
        hk hepsilon htau
  have hgrowth : 1 <= 1 + ‖tau + fun _ : Fin k => epsilon‖ := by
    linarith [norm_nonneg (tau + fun _ : Fin k => epsilon)]
  have halgebra :=
    inv_pow_mul_growth_pow_le_arity_pow hk hp hbase hgrowth hcompare
  simpa only [osiiVI2TimeNormalization,
    osiiVI2TimeAverageBase_shift_positiveReal, Complex.norm_pow, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hbase, base] using
      halgebra

theorem norm_osiiPositiveRealTimeEmbed_eq
    {k : Nat} (sigma : Fin k -> Real) :
    ‖osiiPositiveRealTimeEmbed sigma‖ = ‖sigma‖ := by
  simp [Pi.norm_def, osiiPositiveRealTimeEmbed]

/-- The positive base `k⁻¹ + epsilon⁻¹` in the second factor of OS II
`(6.21)`. -/
def osiiVI2NormalizationBase (k : Nat) (epsilon : Real) : Real :=
  (k : Real)⁻¹ + epsilon⁻¹

/-- The factor multiplying the positively shifted family in `(6.21)`. -/
def osiiVI2Normalization
    (t k : Nat) (epsilon : Real) : Real :=
  (osiiVI2NormalizationBase k epsilon)⁻¹ ^ (k * t)

/-- The reciprocal factor used to recover the original family. -/
def osiiVI2Denormalization
    (t k : Nat) (epsilon : Real) : Real :=
  osiiVI2NormalizationBase k epsilon ^ (k * t)

/-- The complete scalar multiplying the shifted family in the printed
equation `(6.21)`. -/
def osiiVI2Equation621Normalization
    (t k : Nat) (epsilon : Real) (zeta : OSIITimeGapSpace k) : Complex :=
  osiiVI2TimeNormalization t k epsilon zeta *
    (osiiVI2Normalization t k epsilon : Complex)

/-- The complete reciprocal scalar at an unshifted physical target. -/
def osiiVI2Equation621Denormalization
    (t k : Nat) (epsilon : Real) (zeta : OSIITimeGapSpace k) : Complex :=
  osiiVI2TimeDenormalization t k zeta *
    (osiiVI2Denormalization t k epsilon : Complex)

theorem osiiVI2NormalizationBase_pos
    {k : Nat} (hk : 0 < k)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    0 < osiiVI2NormalizationBase k epsilon := by
  unfold osiiVI2NormalizationBase
  exact add_pos (inv_pos.mpr (by exact_mod_cast hk))
    (inv_pos.mpr hepsilon)

theorem osiiVI2Normalization_pos
    {k : Nat} (hk : 0 < k)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (t : Nat) :
    0 < osiiVI2Normalization t k epsilon := by
  exact pow_pos (inv_pos.mpr
    (osiiVI2NormalizationBase_pos hk hepsilon)) _

/-- A raw estimate carrying at most `p` powers of the equation-`(6.21)`
base loses only the residual arity factor after normalization.

The base can be smaller than one for a large shift, so the sharper bound is
`k ^ (k * t - p)`, not `1`.  This is the form needed when a source estimate
records its inverse-shift degree before the final normalized family bound. -/
theorem osiiVI2Normalization_mul_base_pow_le_arity_pow_sub
    {k p t : Nat}
    (hk : 0 < k)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hp : p <= k * t) :
    osiiVI2Normalization t k epsilon *
        osiiVI2NormalizationBase k epsilon ^ p <=
      (k : Real) ^ (k * t - p) := by
  let base := osiiVI2NormalizationBase k epsilon
  have hk_real : 0 < (k : Real) := by exact_mod_cast hk
  have hbase_pos : 0 < base := by
    simpa [base] using osiiVI2NormalizationBase_pos hk hepsilon
  have hbase_lower : (k : Real)⁻¹ <= base := by
    dsimp [base, osiiVI2NormalizationBase]
    exact le_add_of_nonneg_right (inv_nonneg.mpr hepsilon.le)
  have hbase_inv_le : base⁻¹ <= (k : Real) := by
    have h := one_div_le_one_div_of_le (inv_pos.mpr hk_real) hbase_lower
    simpa [one_div] using h
  have hcancel :
      base⁻¹ ^ (k * t) * base ^ p = base⁻¹ ^ (k * t - p) := by
    conv_lhs =>
      rw [← Nat.add_sub_of_le hp, pow_add]
    calc
      (base⁻¹ ^ p * base⁻¹ ^ (k * t - p)) * base ^ p =
          base⁻¹ ^ (k * t - p) * (base⁻¹ ^ p * base ^ p) := by ring
      _ = base⁻¹ ^ (k * t - p) := by
        rw [← mul_pow, inv_mul_cancel₀ hbase_pos.ne', one_pow, mul_one]
  unfold osiiVI2Normalization
  change base⁻¹ ^ (k * t) * base ^ p <=
    (k : Real) ^ (k * t - p)
  rw [hcancel]
  exact pow_le_pow_left₀ (inv_pos.mpr hbase_pos).le hbase_inv_le _

/-- Equation-`(6.21)` absorbs an inverse-shift polynomial of degree at most
`k * t`, uniformly over every positive shift.

The comparison `1 + epsilon⁻¹ <= k * (k⁻¹ + epsilon⁻¹)` converts the usual
translation/source-growth factor into the exact normalization base.  The
preceding residual-factor lemma then removes the shift dependence completely. -/
theorem osiiVI2Normalization_mul_one_add_inv_pow_le_arity_pow
    {k p t : Nat}
    (hk : 0 < k)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hp : p <= k * t) :
    osiiVI2Normalization t k epsilon * (1 + epsilon⁻¹) ^ p <=
      (k : Real) ^ (k * t) := by
  let base := osiiVI2NormalizationBase k epsilon
  have hk_real : 0 < (k : Real) := by exact_mod_cast hk
  have hk_one : (1 : Real) <= k := by exact_mod_cast hk
  have hepsilon_inv_nonneg : 0 <= epsilon⁻¹ := inv_nonneg.mpr hepsilon.le
  have hbase_comparison :
      1 + epsilon⁻¹ <= (k : Real) * base := by
    dsimp [base, osiiVI2NormalizationBase]
    calc
      1 + epsilon⁻¹ <= 1 + (k : Real) * epsilon⁻¹ := by
        apply add_le_add_right
        calc
          epsilon⁻¹ = 1 * epsilon⁻¹ := by ring
          _ <= (k : Real) * epsilon⁻¹ :=
            mul_le_mul_of_nonneg_right hk_one hepsilon_inv_nonneg
      _ = (k : Real) * ((k : Real)⁻¹ + epsilon⁻¹) := by
        rw [mul_add, mul_inv_cancel₀ hk_real.ne']
  have hpow :
      (1 + epsilon⁻¹) ^ p <=
        ((k : Real) * base) ^ p :=
    pow_le_pow_left₀ (by positivity) hbase_comparison p
  have hnormalization_nonneg :
      0 <= osiiVI2Normalization t k epsilon :=
    (osiiVI2Normalization_pos hk hepsilon t).le
  have habsorb :=
    osiiVI2Normalization_mul_base_pow_le_arity_pow_sub
      hk hepsilon hp
  calc
    osiiVI2Normalization t k epsilon * (1 + epsilon⁻¹) ^ p <=
        osiiVI2Normalization t k epsilon *
          ((k : Real) * base) ^ p :=
      mul_le_mul_of_nonneg_left hpow hnormalization_nonneg
    _ = (k : Real) ^ p *
        (osiiVI2Normalization t k epsilon * base ^ p) := by
      rw [mul_pow]
      ring
    _ <= (k : Real) ^ p * (k : Real) ^ (k * t - p) :=
      mul_le_mul_of_nonneg_left habsorb (by positivity)
    _ = (k : Real) ^ (k * t) := by
      rw [← pow_add]
      congr
      omega

/-- On the positive-real edge, the complete printed equation-`(6.21)`
normalization simultaneously absorbs polynomial growth in the shifted time
point and inverse-distance growth at the shifted boundary.

This is the algebraic passage from `(6.20)` to the rank-zero case of `(6.28)`.
The two factors each contribute one harmless fixed-arity power. -/
theorem
    osiiVI2Equation621Normalization_positiveReal_norm_mul_growth_boundary_le
    {k p q t : Nat}
    (hk : 0 < k)
    (hp : p <= k * t)
    (hq : q <= k * t)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    {tau : Fin k -> Real}
    (htau : tau ∈ section43TimeStrictPositiveRegion k) :
    ‖osiiVI2Equation621Normalization t k epsilon
        (osiiPositiveRealTimeEmbed tau)‖ *
        (1 + ‖osiiVI2Shift k epsilon
          (osiiPositiveRealTimeEmbed tau)‖) ^ p *
        (1 + (osiiTimeBoundaryDistance k
          (osiiVI2Shift k epsilon
            (osiiPositiveRealTimeEmbed tau)))⁻¹) ^ q <=
      (k : Real) ^ (2 * (k * t)) := by
  let shiftedTau : Fin k -> Real := tau + fun _ => epsilon
  have hshift :
      osiiVI2Shift k epsilon (osiiPositiveRealTimeEmbed tau) =
        osiiPositiveRealTimeEmbed shiftedTau := by
    ext i
    simp [shiftedTau, osiiVI2Shift, osiiPositiveRealTimeEmbed]
  have htime :
      ‖osiiVI2TimeNormalization t k epsilon
          (osiiPositiveRealTimeEmbed tau)‖ *
          (1 + ‖osiiVI2Shift k epsilon
            (osiiPositiveRealTimeEmbed tau)‖) ^ p <=
        (k : Real) ^ (k * t) := by
    rw [hshift, norm_osiiPositiveRealTimeEmbed_eq]
    exact osiiVI2TimeNormalization_positiveReal_norm_mul_growth_pow_le
      hk hp hepsilon.le htau
  have hzeta :
      osiiPositiveRealTimeEmbed tau ∈ osiiTimeRightHalfPlane k :=
    (osiiPositiveRealTimeEmbed_mem_rightHalfPlane_iff tau).2 htau
  have hdistance :
      epsilon <= osiiTimeBoundaryDistance k
        (osiiVI2Shift k epsilon (osiiPositiveRealTimeEmbed tau)) :=
    osiiTimeBoundaryDistance_shift_ge hk
      (osiiPositiveRealTimeEmbed tau) hzeta epsilon hepsilon.le
  have hdistance_pos :
      0 < osiiTimeBoundaryDistance k
        (osiiVI2Shift k epsilon (osiiPositiveRealTimeEmbed tau)) :=
    hepsilon.trans_le hdistance
  have hinv :
      (osiiTimeBoundaryDistance k
        (osiiVI2Shift k epsilon
          (osiiPositiveRealTimeEmbed tau)))⁻¹ <= epsilon⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le hepsilon hdistance
  have hboundaryPow :
      (1 + (osiiTimeBoundaryDistance k
        (osiiVI2Shift k epsilon
          (osiiPositiveRealTimeEmbed tau)))⁻¹) ^ q <=
        (1 + epsilon⁻¹) ^ q := by
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hepsilonNormalization :
      osiiVI2Normalization t k epsilon *
          (1 + (osiiTimeBoundaryDistance k
            (osiiVI2Shift k epsilon
              (osiiPositiveRealTimeEmbed tau)))⁻¹) ^ q <=
        (k : Real) ^ (k * t) := by
    calc
      osiiVI2Normalization t k epsilon *
          (1 + (osiiTimeBoundaryDistance k
            (osiiVI2Shift k epsilon
              (osiiPositiveRealTimeEmbed tau)))⁻¹) ^ q <=
          osiiVI2Normalization t k epsilon * (1 + epsilon⁻¹) ^ q :=
        mul_le_mul_of_nonneg_left hboundaryPow
          (osiiVI2Normalization_pos hk hepsilon t).le
      _ <= (k : Real) ^ (k * t) :=
        osiiVI2Normalization_mul_one_add_inv_pow_le_arity_pow
          hk hepsilon hq
  have hepsilon_nonneg :
      0 <= osiiVI2Normalization t k epsilon *
          (1 + (osiiTimeBoundaryDistance k
            (osiiVI2Shift k epsilon
              (osiiPositiveRealTimeEmbed tau)))⁻¹) ^ q := by
    exact mul_nonneg (osiiVI2Normalization_pos hk hepsilon t).le
      (pow_nonneg
        (add_nonneg zero_le_one (inv_nonneg.mpr hdistance_pos.le)) _)
  calc
    ‖osiiVI2Equation621Normalization t k epsilon
        (osiiPositiveRealTimeEmbed tau)‖ *
        (1 + ‖osiiVI2Shift k epsilon
          (osiiPositiveRealTimeEmbed tau)‖) ^ p *
        (1 + (osiiTimeBoundaryDistance k
          (osiiVI2Shift k epsilon
            (osiiPositiveRealTimeEmbed tau)))⁻¹) ^ q =
        (‖osiiVI2TimeNormalization t k epsilon
            (osiiPositiveRealTimeEmbed tau)‖ *
          (1 + ‖osiiVI2Shift k epsilon
            (osiiPositiveRealTimeEmbed tau)‖) ^ p) *
        (osiiVI2Normalization t k epsilon *
          (1 + (osiiTimeBoundaryDistance k
            (osiiVI2Shift k epsilon
              (osiiPositiveRealTimeEmbed tau)))⁻¹) ^ q) := by
      rw [osiiVI2Equation621Normalization, norm_mul, Complex.norm_real,
        Real.norm_eq_abs,
        abs_of_pos (osiiVI2Normalization_pos hk hepsilon t)]
      ring
    _ <= (k : Real) ^ (k * t) * (k : Real) ^ (k * t) :=
      mul_le_mul htime hepsilonNormalization hepsilon_nonneg
        (pow_nonneg (Nat.cast_nonneg k) _)
    _ = (k : Real) ^ (2 * (k * t)) := by
      rw [← pow_add]
      congr 1
      omega

theorem osiiVI2Denormalization_pos
    {k : Nat} (hk : 0 < k)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (t : Nat) :
    0 < osiiVI2Denormalization t k epsilon := by
  exact pow_pos (osiiVI2NormalizationBase_pos hk hepsilon) _

theorem osiiVI2Denormalization_mul_normalization
    {k : Nat} (hk : 0 < k)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (t : Nat) :
    osiiVI2Denormalization t k epsilon *
        osiiVI2Normalization t k epsilon = 1 := by
  rw [osiiVI2Denormalization, osiiVI2Normalization, ← mul_pow]
  rw [mul_inv_cancel₀
    (ne_of_gt (osiiVI2NormalizationBase_pos hk hepsilon)), one_pow]



/-- The weighted geometric mean of the two lower-arity normalization bases is
bounded by the target-arity base.  This is the weighted AM--GM content of OS
II `(6.24)`--`(6.25)`: the weights add to one because `a + b = 2 * k`, and
their weighted arithmetic mean is exactly `k⁻¹ + epsilon⁻¹`. -/
theorem osiiVI2NormalizationBase_split_weightedGeometricMean_le
    {a b k : Nat}
    (ha : 0 < a) (hb : 0 < b) (hk : 0 < k)
    (hab : a + b = 2 * k)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    osiiVI2NormalizationBase a epsilon ^
          ((a : Real) / (2 * k : Nat)) *
        osiiVI2NormalizationBase b epsilon ^
          ((b : Real) / (2 * k : Nat)) <=
      osiiVI2NormalizationBase k epsilon := by
  have ha0 : (a : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  have hb0 : (b : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hk0 : (k : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have htwo_k0 : (2 * k : Real) ≠ 0 := by positivity
  have habR : (a : Real) + b = 2 * k := by exact_mod_cast hab
  have hweights :
      (a : Real) / (2 * k : Nat) +
          (b : Real) / (2 * k : Nat) = 1 := by
    field_simp
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith [habR]
  have hmean := Real.geom_mean_le_arith_mean2_weighted
    (show 0 <= (a : Real) / (2 * k : Nat) by positivity)
    (show 0 <= (b : Real) / (2 * k : Nat) by positivity)
    (osiiVI2NormalizationBase_pos ha hepsilon).le
    (osiiVI2NormalizationBase_pos hb hepsilon).le
    hweights
  calc
    osiiVI2NormalizationBase a epsilon ^
          ((a : Real) / (2 * k : Nat)) *
        osiiVI2NormalizationBase b epsilon ^
          ((b : Real) / (2 * k : Nat)) <=
        ((a : Real) / (2 * k : Nat)) *
            osiiVI2NormalizationBase a epsilon +
          ((b : Real) / (2 * k : Nat)) *
            osiiVI2NormalizationBase b epsilon := hmean
    _ = osiiVI2NormalizationBase k epsilon := by
      unfold osiiVI2NormalizationBase
      field_simp
      norm_num only [Nat.cast_mul, Nat.cast_ofNat] at *
      nlinarith [habR]

/-- Integer-power form of the split-base inequality. -/
theorem osiiVI2NormalizationBase_split_pow_le
    {a b k : Nat}
    (ha : 0 < a) (hb : 0 < b) (hk : 0 < k)
    (hab : a + b = 2 * k)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    osiiVI2NormalizationBase a epsilon ^ a *
        osiiVI2NormalizationBase b epsilon ^ b <=
      osiiVI2NormalizationBase k epsilon ^ (2 * k) := by
  let A := osiiVI2NormalizationBase a epsilon
  let B := osiiVI2NormalizationBase b epsilon
  let K := osiiVI2NormalizationBase k epsilon
  let wa : Real := (a : Real) / (2 * k : Nat)
  let wb : Real := (b : Real) / (2 * k : Nat)
  let p : Real := (2 * k : Nat)
  have hA : 0 <= A := (osiiVI2NormalizationBase_pos ha hepsilon).le
  have hB : 0 <= B := (osiiVI2NormalizationBase_pos hb hepsilon).le
  have hweighted : A ^ wa * B ^ wb <= K := by
    simpa [A, B, K, wa, wb] using
      osiiVI2NormalizationBase_split_weightedGeometricMean_le
        ha hb hk hab hepsilon
  have hpow : (A ^ wa * B ^ wb) ^ p <= K ^ p :=
    Real.rpow_le_rpow (by positivity) hweighted (by positivity)
  have hwa : wa * p = a := by
    dsimp [wa, p]
    have hk0 : (k : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
    field_simp
  have hwb : wb * p = b := by
    dsimp [wb, p]
    have hk0 : (k : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
    field_simp
  calc
    osiiVI2NormalizationBase a epsilon ^ a *
        osiiVI2NormalizationBase b epsilon ^ b =
        (A ^ wa * B ^ wb) ^ p := by
      rw [Real.mul_rpow (Real.rpow_nonneg hA wa)
        (Real.rpow_nonneg hB wb)]
      rw [← Real.rpow_mul hA, ← Real.rpow_mul hB, hwa, hwb]
      rw [Real.rpow_natCast, Real.rpow_natCast]
    _ <= K ^ p := hpow
    _ = osiiVI2NormalizationBase k epsilon ^ (2 * k) := by
      rw [show p = ((2 * k : Nat) : Real) by rfl,
        Real.rpow_natCast]

/-- The product of the two lower-arity denormalizations is bounded by the
square of the target-arity denormalization. -/
theorem osiiVI2Denormalization_split_mul_le_sq
    {a b k : Nat}
    (ha : 0 < a) (hb : 0 < b) (hk : 0 < k)
    (hab : a + b = 2 * k)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (t : Nat) :
    osiiVI2Denormalization t a epsilon *
        osiiVI2Denormalization t b epsilon <=
      osiiVI2Denormalization t k epsilon ^ 2 := by
  have hbase := osiiVI2NormalizationBase_split_pow_le
    ha hb hk hab hepsilon
  unfold osiiVI2Denormalization
  calc
    osiiVI2NormalizationBase a epsilon ^ (a * t) *
        osiiVI2NormalizationBase b epsilon ^ (b * t) =
        (osiiVI2NormalizationBase a epsilon ^ a *
          osiiVI2NormalizationBase b epsilon ^ b) ^ t := by
      rw [mul_pow, pow_mul, pow_mul]
    _ <= (osiiVI2NormalizationBase k epsilon ^ (2 * k)) ^ t :=
      pow_le_pow_left₀
        (mul_nonneg
          (pow_nonneg (osiiVI2NormalizationBase_pos ha hepsilon).le _)
          (pow_nonneg (osiiVI2NormalizationBase_pos hb hepsilon).le _))
        hbase t
    _ = (osiiVI2NormalizationBase k epsilon ^ (k * t)) ^ 2 := by
      have hexp : (2 * k) * t = (k * t) * 2 := by ring
      rw [← pow_mul, ← pow_mul]
      rw [hexp]

/-- The canonical shift inverse is controlled by the standard inverse
boundary-distance factor. -/
theorem osiiVI2CanonicalEpsilon_inv_le
    {k : Nat} (hk : 0 < k)
    {zeta : OSIITimeGapSpace k}
    (hzeta : zeta ∈ osiiTimeRightHalfPlane k) :
    (osiiVI2CanonicalEpsilon k zeta)⁻¹ ≤
      2 * (1 + (osiiTimeBoundaryDistance k zeta)⁻¹) := by
  let rho := osiiChapterVIRegularizationRadius k zeta
  have hrho_pos : 0 < rho := by
    simpa [rho] using osiiChapterVIRegularizationRadius_pos hk hzeta
  have hratio := osiiChapterVIRegularizationRadius_ratio_le hk hzeta
  change 16 / rho ≤
    16 * (1 + (osiiTimeBoundaryDistance k zeta)⁻¹) at hratio
  have hscaled := mul_le_mul_of_nonneg_left hratio
    (show 0 ≤ (1 / 8 : Real) by norm_num)
  change (rho / 2)⁻¹ ≤
    2 * (1 + (osiiTimeBoundaryDistance k zeta)⁻¹)
  calc
    (rho / 2)⁻¹ = (1 / 8 : Real) * (16 / rho) := by
      field_simp [ne_of_gt hrho_pos]
      norm_num
    _ ≤ (1 / 8 : Real) *
        (16 * (1 + (osiiTimeBoundaryDistance k zeta)⁻¹)) := hscaled
    _ = 2 * (1 + (osiiTimeBoundaryDistance k zeta)⁻¹) := by ring

/-- Undoing `(6.21)` costs exactly the additional `k * t` power of the
standard boundary-distance factor, up to the explicit constant `3^(k*t)`. -/
theorem osiiVI2CanonicalDenormalization_le
    {k : Nat} (hk : 0 < k)
    {zeta : OSIITimeGapSpace k}
    (hzeta : zeta ∈ osiiTimeRightHalfPlane k)
    (t : Nat) :
    osiiVI2Denormalization t k (osiiVI2CanonicalEpsilon k zeta) ≤
      3 ^ (k * t) *
        (1 + (osiiTimeBoundaryDistance k zeta)⁻¹) ^ (k * t) := by
  let D : Real := 1 + (osiiTimeBoundaryDistance k zeta)⁻¹
  have hdelta_pos : 0 < osiiTimeBoundaryDistance k zeta :=
    osiiTimeBoundaryDistance_pos hk hzeta
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    positivity
  have hD_one : 1 ≤ D := by
    dsimp [D]
    linarith [inv_nonneg.mpr hdelta_pos.le]
  have hk_one : (1 : Real) ≤ k := by exact_mod_cast hk
  have hkinv : (k : Real)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hk_one
  have hepsilon := osiiVI2CanonicalEpsilon_inv_le hk hzeta
  have hbase :
      osiiVI2NormalizationBase k (osiiVI2CanonicalEpsilon k zeta) ≤
        3 * D := by
    unfold osiiVI2NormalizationBase
    dsimp [D] at hepsilon ⊢
    linarith
  have hbase_nonneg :
      0 ≤ osiiVI2NormalizationBase k
        (osiiVI2CanonicalEpsilon k zeta) :=
    (osiiVI2NormalizationBase_pos hk
      (osiiVI2CanonicalEpsilon_pos hk hzeta)).le
  rw [osiiVI2Denormalization, ← mul_pow]
  exact pow_le_pow_left₀ hbase_nonneg hbase (k * t)

/-- A direct inverse-shift bound is enough to preserve the public
boundary-distance degree.

This is the additive counterpart of the canonical-fraction estimate. It is
the form needed when source geometry chooses a shift capped by a fixed
positive hub margin: the cap contributes to the inverse coefficient, while
the target-dependent part remains in the standard boundary weight. -/
theorem osiiVI2Denormalization_le_of_inverse_boundary_control
    {k : Nat} (hk : 0 < k)
    {zeta : OSIITimeGapSpace k}
    (hzeta : zeta ∈ osiiTimeRightHalfPlane k)
    (t : Nat)
    {epsilon inverseCoefficient : Real}
    (hepsilon : 0 < epsilon)
    (hepsilon_inv :
      epsilon⁻¹ <= inverseCoefficient *
        (1 + (osiiTimeBoundaryDistance k zeta)⁻¹)) :
    osiiVI2Denormalization t k epsilon <=
      (1 + inverseCoefficient) ^ (k * t) *
        (1 + (osiiTimeBoundaryDistance k zeta)⁻¹) ^ (k * t) := by
  let D : Real := 1 + (osiiTimeBoundaryDistance k zeta)⁻¹
  have hdelta_pos : 0 < osiiTimeBoundaryDistance k zeta :=
    osiiTimeBoundaryDistance_pos hk hzeta
  have hD_nonneg : 0 <= D := by
    dsimp [D]
    positivity
  have hD_one : 1 <= D := by
    dsimp [D]
    linarith [inv_nonneg.mpr hdelta_pos.le]
  have hk_one : (1 : Real) <= k := by
    exact_mod_cast hk
  have hkinv : (k : Real)⁻¹ <= 1 :=
    inv_le_one_of_one_le₀ hk_one
  have hbase :
      osiiVI2NormalizationBase k epsilon <=
        (1 + inverseCoefficient) * D := by
    unfold osiiVI2NormalizationBase
    calc
      (k : Real)⁻¹ + epsilon⁻¹ <=
          D + inverseCoefficient * D :=
        add_le_add (hkinv.trans hD_one) (by simpa [D] using hepsilon_inv)
      _ = (1 + inverseCoefficient) * D := by ring
  have hbase_nonneg :
      0 <= osiiVI2NormalizationBase k epsilon :=
    (osiiVI2NormalizationBase_pos hk hepsilon).le
  rw [osiiVI2Denormalization, ← mul_pow]
  exact pow_le_pow_left₀ hbase_nonneg hbase (k * t)

namespace OSIIVI2FractionalShiftData

end OSIIVI2FractionalShiftData

/-- A positive target-local VI.2 shift whose denormalization loss is
controlled by an explicit boundary-distance coefficient.

This is the honest interface for source-local shifts on unbounded sectors.
A lower fraction of the canonical radius is one way to produce such a
coefficient, but it is not necessary: a shift capped by a fixed positive hub
margin can still have the same boundary-distance degree with a larger
constant. -/
structure OSIIVI2BoundaryControlledShiftData
    (t k : Nat) (zeta : OSIITimeGapSpace k) where
  recovery : Real
  epsilon : Real
  epsilon_pos : 0 < epsilon
  epsilon_le_canonical :
    epsilon <= osiiVI2CanonicalEpsilon k zeta
  denormalization_le :
    osiiVI2Denormalization t k epsilon <=
      recovery *
        (1 + (osiiTimeBoundaryDistance k zeta)⁻¹) ^ (k * t)

namespace OSIIVI2BoundaryControlledShiftData

/-- Package a positive shift from a direct inverse-boundary estimate. -/
def ofInverseBoundaryControl
    {t k : Nat} (hk : 0 < k)
    {zeta : OSIITimeGapSpace k}
    (hzeta : zeta ∈ osiiTimeRightHalfPlane k)
    (epsilon inverseCoefficient : Real)
    (hepsilon : 0 < epsilon)
    (hepsilon_le :
      epsilon <= osiiVI2CanonicalEpsilon k zeta)
    (hepsilon_inv :
      epsilon⁻¹ <= inverseCoefficient *
        (1 + (osiiTimeBoundaryDistance k zeta)⁻¹)) :
    OSIIVI2BoundaryControlledShiftData t k zeta where
  recovery := (1 + inverseCoefficient) ^ (k * t)
  epsilon := epsilon
  epsilon_pos := hepsilon
  epsilon_le_canonical := hepsilon_le
  denormalization_le :=
    osiiVI2Denormalization_le_of_inverse_boundary_control
      hk hzeta t hepsilon hepsilon_inv

end OSIIVI2BoundaryControlledShiftData

namespace OSIIVI2QuantitativeShiftData

end OSIIVI2QuantitativeShiftData



namespace OSIITimeContinuationStage

variable {d k : Nat}



/-- The translated physical carrier with the pole set of the time-average
reciprocal removed. -/
def vi2Equation621Carrier
    (A : OSIITimeContinuationStage d k)
    (epsilon : Real) : Set (OSIITimeGapSpace k) :=
  {zeta |
    osiiVI2Shift k epsilon zeta ∈ A.carrier ∧
      osiiVI2TimeAverageBase k (osiiVI2Shift k epsilon zeta) ≠ 0}

theorem isOpen_vi2Equation621Carrier
    (A : OSIITimeContinuationStage d k)
    (epsilon : Real) : IsOpen (A.vi2Equation621Carrier epsilon) := by
  have hshift : Continuous (osiiVI2Shift k epsilon) := by
    change Continuous
      (fun zeta : OSIITimeGapSpace k =>
        zeta + fun _ => (epsilon : Complex))
    exact continuous_id.add continuous_const
  have hbase : Continuous
      (fun zeta : OSIITimeGapSpace k =>
        osiiVI2TimeAverageBase k (osiiVI2Shift k epsilon zeta)) := by
    unfold osiiVI2TimeAverageBase osiiVI2Shift
    fun_prop
  change IsOpen ((osiiVI2Shift k epsilon) ⁻¹' A.carrier ∩
    {zeta | osiiVI2TimeAverageBase k (osiiVI2Shift k epsilon zeta) ≠ 0})
  exact (A.carrier_open.preimage hshift).inter
    (isOpen_ne_fun hbase continuous_const)

theorem osiiVI2TimeNormalization_differentiableOn
    (t k : Nat) (epsilon : Real) :
    DifferentiableOn Complex
      (osiiVI2TimeNormalization t k epsilon)
      {zeta |
        osiiVI2TimeAverageBase k (osiiVI2Shift k epsilon zeta) ≠ 0} := by
  intro zeta hzeta
  have hbase : DifferentiableAt Complex
      (fun z : OSIITimeGapSpace k =>
        osiiVI2TimeAverageBase k (osiiVI2Shift k epsilon z)) zeta := by
    unfold osiiVI2TimeAverageBase osiiVI2Shift
    fun_prop
  unfold osiiVI2TimeNormalization
  exact ((hbase.inv hzeta).pow (k * t)).differentiableWithinAt

theorem osiiVI2Equation621Normalization_differentiableOn
    (t k : Nat) (epsilon : Real) :
    DifferentiableOn Complex
      (osiiVI2Equation621Normalization t k epsilon)
      {zeta |
        osiiVI2TimeAverageBase k (osiiVI2Shift k epsilon zeta) ≠ 0} := by
  have htime := osiiVI2TimeNormalization_differentiableOn t k epsilon
  unfold osiiVI2Equation621Normalization
  exact htime.mul_const (osiiVI2Normalization t k epsilon : Complex)

/-- The distribution-valued family in the printed OS II equation `(6.21)`. -/
noncomputable def vi2Equation621NormalizedDistribution
    (A : OSIITimeContinuationStage d k)
    (t : Nat) (epsilon : Real) :
    OSIITimeGapSpace k → OSIISpatialDistribution d k :=
  fun zeta =>
    osiiVI2Equation621Normalization t k epsilon zeta •
      A.distribution (osiiVI2Shift k epsilon zeta)

/-- The source-faithful equation-`(6.21)` family as a continuation stage. -/
noncomputable def vi2Equation621NormalizedStage
    (A : OSIITimeContinuationStage d k)
    (t : Nat) (epsilon : Real) : OSIITimeContinuationStage d k where
  carrier := A.vi2Equation621Carrier epsilon
  carrier_open := A.isOpen_vi2Equation621Carrier epsilon
  distribution := A.vi2Equation621NormalizedDistribution t epsilon
  weaklyHolomorphic := by
    intro chi
    have hshift : Differentiable Complex (osiiVI2Shift k epsilon) := by
      change Differentiable Complex
        (fun zeta : OSIITimeGapSpace k =>
          zeta + fun _ => (epsilon : Complex))
      exact differentiable_id.add_const _
    have hraw : DifferentiableOn Complex
        (fun zeta => A.distribution (osiiVI2Shift k epsilon zeta) chi)
        (A.vi2Equation621Carrier epsilon) :=
      (A.weaklyHolomorphic chi).comp hshift.differentiableOn
        (fun _ hzeta => hzeta.1)
    have hnormalization : DifferentiableOn Complex
        (osiiVI2Equation621Normalization t k epsilon)
        (A.vi2Equation621Carrier epsilon) :=
      (osiiVI2Equation621Normalization_differentiableOn t k epsilon).mono
        (fun _ hzeta => hzeta.2)
    unfold vi2Equation621NormalizedDistribution
    exact hnormalization.mul hraw

@[simp] theorem vi2Equation621NormalizedStage_carrier
    (A : OSIITimeContinuationStage d k)
    (t : Nat) (epsilon : Real) :
    (A.vi2Equation621NormalizedStage t epsilon).carrier =
      A.vi2Equation621Carrier epsilon :=
  rfl

@[simp] theorem vi2Equation621NormalizedStage_distribution_apply
    (A : OSIITimeContinuationStage d k)
    (t : Nat) (epsilon : Real)
    (zeta : OSIITimeGapSpace k)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    (A.vi2Equation621NormalizedStage t epsilon).distribution zeta chi =
      osiiVI2Equation621Normalization t k epsilon zeta *
        A.distribution (osiiVI2Shift k epsilon zeta) chi := by
  rfl



/-- The epsilon-dependent component of `(6.21)`, retained temporarily while
downstream consumers migrate to `vi2Equation621NormalizedStage`. -/
noncomputable def vi2NormalizedDistribution
    (A : OSIITimeContinuationStage d k)
    (t : Nat) (epsilon : Real) :
    OSIITimeGapSpace k → OSIISpatialDistribution d k :=
  fun zeta =>
    (osiiVI2Normalization t k epsilon : Complex) •
      A.distribution (osiiVI2Shift k epsilon zeta)

/-- Legacy epsilon-only stage used by the pre-migration envelope route. -/
noncomputable def vi2NormalizedStage
    (A : OSIITimeContinuationStage d k)
    (t : Nat) (epsilon : Real) :
    OSIITimeContinuationStage d k where
  carrier := {zeta | osiiVI2Shift k epsilon zeta ∈ A.carrier}
  carrier_open :=
    A.carrier_open.preimage (by
      apply continuous_pi
      intro i
      exact (continuous_apply i).add continuous_const)
  distribution := A.vi2NormalizedDistribution t epsilon
  weaklyHolomorphic := by
    intro chi
    have hshift :
        Differentiable Complex (osiiVI2Shift k epsilon) := by
      change Differentiable Complex
        (fun zeta : OSIITimeGapSpace k =>
          zeta + fun _ => (epsilon : Complex))
      exact differentiable_id.add_const _
    have hcomp :=
      (A.weaklyHolomorphic chi).comp
        hshift.differentiableOn
          (fun _ hzeta => hzeta)
    unfold vi2NormalizedDistribution
    exact hcomp.const_mul (osiiVI2Normalization t k epsilon : Complex)

@[simp] theorem vi2NormalizedStage_carrier
    (A : OSIITimeContinuationStage d k)
    (t : Nat) (epsilon : Real) :
    (A.vi2NormalizedStage t epsilon).carrier =
      {zeta | osiiVI2Shift k epsilon zeta ∈ A.carrier} :=
  rfl

end OSIITimeContinuationStage

end OSReconstruction
