import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVITestedTaylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# A quantitative singular Taylor endpoint

Taylor expansion of the first derivative turns an order-`M` wall bound into
an integrable logarithmic bound. Integrating that first derivative gives the
boundary value and the `u * (1 + M * |log u|)` convergence rate.
-/

noncomputable section

open Filter MeasureTheory Set Topology
open scoped BigOperators Interval

namespace OSReconstruction
namespace OSIIChapterVI

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

private theorem factorial_inv_le_one (j : Nat) : (j.factorial : Real)⁻¹ <= 1 :=
  inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos j)

omit [CompleteSpace E] in
private theorem norm_taylorTerm_le
    (v : E) {H u : Real} (hv : ‖v‖ <= H)
    (hu : u ∈ Ioc (0 : Real) 1) (j : Nat) :
    ‖((j.factorial : Real)⁻¹ * (u - 1) ^ j) • v‖ <= H := by
  have hfac : 0 <= (j.factorial : Real)⁻¹ := by positivity
  have huabs : |u - 1| <= 1 := by rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
  have hcoeff : |(j.factorial : Real)⁻¹ * (u - 1) ^ j| <= 1 := by
    rw [abs_mul, abs_of_nonneg hfac, abs_pow]
    exact (mul_le_mul (factorial_inv_le_one j)
      (pow_le_one₀ (abs_nonneg _) huabs) (by positivity) zero_le_one).trans_eq (by ring)
  rw [norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul hcoeff hv (norm_nonneg _) zero_le_one).trans_eq (one_mul H)

/-- Only the first derivative has to be integrated at the singular endpoint.
Its logarithmic bound follows from Taylor expansion at the regular height 1. -/
theorem singularTaylor_firstDerivative_bound
    (J : Nat -> Real -> E) (M : Nat) {H : Real} (hH : 0 <= H)
    (hJ : forall j s, 0 < s -> HasDerivAt (J j) (J (j + 1) s) s)
    (hbound : forall j, j <= M + 1 -> forall s, s ∈ Ioc (0 : Real) 1 ->
      ‖J j s‖ <= H * s ^ (-(M : Real)))
    {u : Real} (hu : u ∈ Ioc (0 : Real) 1) :
    ‖J 1 u‖ <= H * ((M + 1 : Nat) + (M : Real) * |Real.log u|) := by
  cases M with
  | zero => simpa using hbound 1 (by omega) u hu
  | succ m =>
    have hpos : forall s, s ∈ uIcc u 1 -> 0 < s := by
      intro s hs
      have hs' : s ∈ Icc u 1 := by simpa only [uIcc_of_le hu.2] using hs
      exact hu.1.trans_le hs'.1
    have hexpand := osii_testedTaylor_between (fun j => J (j + 1)) m u 1
      (fun j s hs => hJ (j + 1) s (hpos s hs))
    have hpoly :
        ‖∑ j ∈ Finset.range (m + 1),
          ((j.factorial : Real)⁻¹ * (u - 1) ^ j) • J (j + 1) 1‖ <=
          (m + 1 : Nat) * H := by
      refine (norm_sum_le _ _).trans ?_
      calc
        (∑ j ∈ Finset.range (m + 1),
            ‖((j.factorial : Real)⁻¹ * (u - 1) ^ j) • J (j + 1) 1‖) <=
            ∑ _j ∈ Finset.range (m + 1), H := by
          apply Finset.sum_le_sum
          intro j hj
          apply norm_taylorTerm_le _ _ hu j
          simpa using hbound (j + 1) (by have := Finset.mem_range.mp hj; omega)
            1 (by norm_num)
        _ = (m + 1 : Nat) * H := by simp
    have hkernel : forall s, s ∈ Ioc u 1 ->
        ‖(u - s) ^ m • J (m + 1 + 1) s‖ <= H * s⁻¹ := by
      intro s hs
      have hs0 : 0 < s := hu.1.trans hs.1
      have hpow : |u - s| ^ m <= s ^ m := by
        rw [abs_of_nonpos (sub_nonpos.mpr hs.1.le)]
        apply pow_le_pow_left₀ (by linarith [hs.1]) (by linarith [hu.1])
      have hcancel : s ^ m * s ^ (-((m + 1 : Nat) : Real)) = s⁻¹ := by
        rw [Real.rpow_neg hs0.le, Real.rpow_natCast, pow_succ]
        field_simp
      rw [norm_smul, Real.norm_eq_abs, abs_pow]
      calc
        |u - s| ^ m * ‖J (m + 1 + 1) s‖ <=
            s ^ m * (H * s ^ (-((m + 1 : Nat) : Real))) :=
          mul_le_mul hpow (hbound (m + 1 + 1) (by omega) s ⟨hs0, hs.2⟩)
            (norm_nonneg _) (by positivity)
        _ = H * s⁻¹ := by rw [mul_left_comm, hcancel]
    have hinv : IntervalIntegrable (fun s : Real => H * s⁻¹) volume u 1 := by
      apply (continuousOn_const.mul (continuousOn_id.inv₀ ?_)).intervalIntegrable
      intro s hs
      exact ne_of_gt (hpos s hs)
    have hrem :
        ‖∫ s in u..1, (u - s) ^ m • J (m + 1 + 1) s‖ <= H * |Real.log u| := by
      calc
        _ <= ∫ s in u..1, H * s⁻¹ :=
          intervalIntegral.norm_integral_le_of_norm_le hu.2
            (Eventually.of_forall hkernel) hinv
        _ = H * |Real.log u| := by
          rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hu.1 zero_lt_one]
          rw [one_div, Real.log_inv, abs_of_nonpos (Real.log_nonpos hu.1.le hu.2)]
    rw [hexpand]
    calc
      _ <= ‖∑ j ∈ Finset.range (m + 1),
          ((j.factorial : Real)⁻¹ * (u - 1) ^ j) • J (j + 1) 1‖ +
          ‖(m.factorial : Real)⁻¹ •
            ∫ s in u..1, (u - s) ^ m • J (m + 1 + 1) s‖ := norm_sub_le _ _
      _ <= (m + 1 : Nat) * H + H * |Real.log u| := by
        apply add_le_add hpoly
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact (mul_le_mul (factorial_inv_le_one m) hrem (norm_nonneg _) zero_le_one
          ).trans_eq (one_mul _)
      _ <= H * (((m + 1) + 1 : Nat) + ((m + 1 : Nat) : Real) * |Real.log u|) := by
        push_cast
        nlinarith [abs_nonneg (Real.log u), mul_nonneg hH (abs_nonneg (Real.log u)),
          Nat.cast_nonneg (α := Real) m]

private theorem intervalIntegrable_logMajorant (M : Nat) (H a b : Real) :
    IntervalIntegrable
      (fun s : Real => H * ((M + 1 : Nat) + (M : Real) * |Real.log s|)) volume a b := by
  have hc : IntervalIntegrable (fun _ : Real => ((M + 1 : Nat) : Real)) volume a b :=
    intervalIntegrable_const
  have hl : IntervalIntegrable Real.log volume a b := intervalIntegral.intervalIntegrable_log'
  exact (hc.add (hl.abs.const_mul (M : Real))).const_mul H

private theorem integral_logMajorant (M : Nat) {u : Real}
    (hu : u ∈ Ioc (0 : Real) 1) :
    (∫ s in (0 : Real)..u, ((M + 1 : Nat) + (M : Real) * |Real.log s|)) =
      u * ((2 * M + 1 : Nat) + (M : Real) * |Real.log u|) := by
  have hfun : EqOn
      (fun s : Real => ((M + 1 : Nat) + (M : Real) * |Real.log s|))
      (fun s : Real => ((M + 1 : Nat) - (M : Real) * Real.log s))
      (uIcc 0 u) := by
    intro s hs
    have hs' : s ∈ Icc 0 u := by simpa only [uIcc_of_le hu.1.le] using hs
    dsimp only
    rw [abs_of_nonpos (Real.log_nonpos hs'.1 (hs'.2.trans hu.2))]
    ring
  have hl : IntervalIntegrable Real.log volume 0 u := intervalIntegral.intervalIntegrable_log'
  rw [intervalIntegral.integral_congr hfun,
    intervalIntegral.integral_sub intervalIntegrable_const
      (hl.const_mul (M : Real)),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_log_from_zero,
    abs_of_nonpos (Real.log_nonpos hu.1.le hu.2)]
  push_cast
  simp only [sub_zero, smul_eq_mul]
  ring

theorem singularTaylor_firstDerivative_integrable
    (J : Nat -> Real -> E) (M : Nat) {H : Real} (hH : 0 <= H)
    (hJ : forall j s, 0 < s -> HasDerivAt (J j) (J (j + 1) s) s)
    (hbound : forall j, j <= M + 1 -> forall s, s ∈ Ioc (0 : Real) 1 ->
      ‖J j s‖ <= H * s ^ (-(M : Real))) :
    IntervalIntegrable (J 1) volume 0 1 := by
  have hcont : ContinuousOn (J 1) (Ioc (0 : Real) 1) := by
    intro s hs
    exact (hJ 1 s hs.1).continuousAt.continuousWithinAt
  apply (intervalIntegrable_logMajorant M H 0 1).mono_fun'
  · simpa only [uIoc_of_le zero_le_one] using
      hcont.aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    exact singularTaylor_firstDerivative_bound J M hH hJ hbound
      (by simpa only [uIoc_of_le zero_le_one] using hs)

/-- The endpoint recovered from the integrable first derivative. -/
def singularTaylorBoundaryValue (J : Nat -> Real -> E) : E :=
  J 0 1 - ∫ s in (0 : Real)..1, J 1 s

theorem singularTaylorBoundaryValue_sub_eq_integral
    (J : Nat -> Real -> E) (M : Nat) {H : Real} (hH : 0 <= H)
    (hJ : forall j s, 0 < s -> HasDerivAt (J j) (J (j + 1) s) s)
    (hbound : forall j, j <= M + 1 -> forall s, s ∈ Ioc (0 : Real) 1 ->
      ‖J j s‖ <= H * s ^ (-(M : Real)))
    {u : Real} (hu : u ∈ Ioc (0 : Real) 1) :
    J 0 u - singularTaylorBoundaryValue J = ∫ s in (0 : Real)..u, J 1 s := by
  have hpos : forall s, s ∈ uIcc u 1 -> 0 < s := by
    intro s hs
    have hs' : s ∈ Icc u 1 := by simpa only [uIcc_of_le hu.2] using hs
    exact hu.1.trans_le hs'.1
  have hcont : ContinuousOn (J 1) (uIcc u 1) := by
    intro s hs
    exact (hJ 1 s (hpos s hs)).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (J 1) volume u 1 := hcont.intervalIntegrable
  have hint0 := singularTaylor_firstDerivative_integrable J M hH hJ hbound
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hint0.trans hint.symm) hint
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hJ 0 s (hpos s hs)) hint
  unfold singularTaylorBoundaryValue
  rw [← hadd, hftc]
  abel

theorem singularTaylorBoundaryValue_error
    (J : Nat -> Real -> E) (M : Nat) {H : Real} (hH : 0 <= H)
    (hJ : forall j s, 0 < s -> HasDerivAt (J j) (J (j + 1) s) s)
    (hbound : forall j, j <= M + 1 -> forall s, s ∈ Ioc (0 : Real) 1 ->
      ‖J j s‖ <= H * s ^ (-(M : Real)))
    {u : Real} (hu : u ∈ Ioc (0 : Real) 1) :
    ‖J 0 u - singularTaylorBoundaryValue J‖ <=
      H * u * ((2 * M + 1 : Nat) + (M : Real) * |Real.log u|) := by
  rw [singularTaylorBoundaryValue_sub_eq_integral J M hH hJ hbound hu]
  calc
    _ <= ∫ s in (0 : Real)..u,
        H * ((M + 1 : Nat) + (M : Real) * |Real.log s|) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hu.1.le
      · filter_upwards with s hs
        exact singularTaylor_firstDerivative_bound J M hH hJ hbound
          ⟨hs.1, hs.2.trans hu.2⟩
      · exact intervalIntegrable_logMajorant M H 0 u
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_logMajorant M hu]
      ring

theorem norm_singularTaylorBoundaryValue_le
    (J : Nat -> Real -> E) (M : Nat) {H : Real} (hH : 0 <= H)
    (hJ : forall j s, 0 < s -> HasDerivAt (J j) (J (j + 1) s) s)
    (hbound : forall j, j <= M + 1 -> forall s, s ∈ Ioc (0 : Real) 1 ->
      ‖J j s‖ <= H * s ^ (-(M : Real))) :
    ‖singularTaylorBoundaryValue J‖ <= H * (2 * M + 2 : Nat) := by
  have hzero : ‖J 0 1‖ <= H := by simpa using hbound 0 (by omega) 1 (by norm_num)
  have herr := singularTaylorBoundaryValue_error J M hH hJ hbound
    (u := 1) (by norm_num)
  simp only [Real.log_one, abs_zero, mul_zero, add_zero, mul_one] at herr
  calc
    ‖singularTaylorBoundaryValue J‖ <=
        ‖J 0 1‖ + ‖J 0 1 - singularTaylorBoundaryValue J‖ := by
      simpa only [norm_sub_rev] using norm_le_norm_add_norm_sub (J 0 1) (singularTaylorBoundaryValue J)
    _ <= H + H * (2 * M + 1 : Nat) := add_le_add hzero herr
    _ = _ := by push_cast; ring

theorem tendsto_singularTaylorBoundaryValue
    (J : Nat -> Real -> E) (M : Nat) {H : Real} (hH : 0 <= H)
    (hJ : forall j s, 0 < s -> HasDerivAt (J j) (J (j + 1) s) s)
    (hbound : forall j, j <= M + 1 -> forall s, s ∈ Ioc (0 : Real) 1 ->
      ‖J j s‖ <= H * s ^ (-(M : Real))) :
    Tendsto (J 0) (nhdsWithin 0 (Ioi 0)) (nhds (singularTaylorBoundaryValue J)) := by
  let R : Real -> Real := fun u =>
    H * ((2 * M + 1 : Nat) * |u| + (M : Real) * |u * Real.log u|)
  have hR : Continuous R :=
    continuous_const.mul ((continuous_const.mul continuous_abs).add
      (continuous_const.mul Real.continuous_mul_log.abs))
  have hRlim : Tendsto R (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa [R] using (hR.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hRlim
  filter_upwards [Ioc_mem_nhdsGT (show (0 : Real) < 1 by norm_num)] with u hu
  exact (singularTaylorBoundaryValue_error J M hH hJ hbound hu).trans_eq (by
    simp only [R, abs_mul, abs_of_pos hu.1]
    ring)

end OSIIChapterVI
end OSReconstruction
