/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Scalar FTC Identities for Exponential Differences

Pure 1D complex analysis identities for bounding exponential differences
and Taylor remainders. Used by the Paley-Wiener-Schwartz bridge.

## Main results

* `cexp_sub_one_eq_integral` : `exp(w) - 1 = w * ∫₀¹ exp(tw) dt`
* `cexp_sub_one_sub_id_eq_integral` : `exp(w) - 1 - w = w² * ∫₀¹ (1-t) exp(tw) dt`
-/

open Complex MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

private lemma hasDerivAt_ofReal_mul_const (w : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (s : ℂ) * w) w t := by
  have := Complex.ofRealCLM.hasDerivAt (x := t)
  simpa [one_mul] using this.mul_const w

private lemma continuous_cexp_ofReal_mul (w : ℂ) :
    Continuous (fun t : ℝ => cexp ((t : ℂ) * w)) :=
  Complex.continuous_exp.comp (Complex.ofRealCLM.continuous.mul continuous_const)

/-- `exp(w) - 1 = w * ∫ t in 0..1, exp(t * w)` by FTC. -/
theorem cexp_sub_one_eq_integral (w : ℂ) :
    cexp w - 1 = w * ∫ t : ℝ in (0 : ℝ)..(1 : ℝ), cexp ((t : ℂ) * w) := by
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun s : ℝ => cexp ((s : ℂ) * w)) (w * cexp ((t : ℂ) * w)) t := by
    intro t _
    exact (hasDerivAt_ofReal_mul_const w t).cexp.congr_deriv (by ring)
  have hint : IntervalIntegrable (fun t : ℝ => w * cexp ((t : ℂ) * w))
      MeasureTheory.volume (0 : ℝ) (1 : ℝ) :=
    (continuous_const.mul (continuous_cexp_ofReal_mul w)).intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, exp_zero] at hftc
  -- hftc : ∫ w * exp(tw) dt = exp(w) - 1
  -- Need: exp(w) - 1 = w * ∫ exp(tw) dt
  -- Pull w out via smul
  have hsmul : (fun t : ℝ => w * cexp ((t : ℂ) * w)) =
      (fun t : ℝ => w • cexp ((t : ℂ) * w)) := by ext; rfl
  rw [hsmul, intervalIntegral.integral_smul, smul_eq_mul] at hftc
  exact hftc.symm

/-- `exp(w) - 1 - w = w² * ∫ t in 0..1, (1-t) * exp(tw) dt` via explicit antiderivative.

The antiderivative is `F(t) = (w(1-t) + 1) * exp(tw)`, avoiding integration by parts. -/
theorem cexp_sub_one_sub_id_eq_integral (w : ℂ) :
    cexp w - 1 - w = w ^ 2 * ∫ t : ℝ in (0 : ℝ)..(1 : ℝ),
      (1 - (t : ℂ)) * cexp ((t : ℂ) * w) := by
  -- Explicit antiderivative: F(t) = (w(1-t) + 1) * exp(tw)
  -- F'(t) = -w * exp(tw) + (w(1-t) + 1) * w * exp(tw) = w²(1-t) * exp(tw)
  let F : ℝ → ℂ := fun t => (w * (1 - (t : ℂ)) + 1) * cexp ((t : ℂ) * w)
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt F
      (w ^ 2 * (1 - (t : ℂ)) * cexp ((t : ℂ) * w)) t := by
    intro t _
    have hd_1_sub : HasDerivAt (fun s : ℝ => 1 - (s : ℂ)) (-1) t := by
      have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
      convert hasDerivAt_const t (1 : ℂ) |>.sub h1 using 1
      simp
    have hd_poly : HasDerivAt (fun s : ℝ => w * (1 - (s : ℂ)) + 1) (-w) t := by
      simpa using (hd_1_sub.const_mul w).add_const 1
    have hd_exp : HasDerivAt (fun s : ℝ => cexp ((s : ℂ) * w))
        (w * cexp ((t : ℂ) * w)) t :=
      (hasDerivAt_ofReal_mul_const w t).cexp.congr_deriv (by ring)
    have hd_full := hd_poly.mul hd_exp
    exact hd_full.congr_deriv (by ring)
  have hint : IntervalIntegrable
      (fun t : ℝ => w ^ 2 * (1 - (t : ℂ)) * cexp ((t : ℂ) * w))
      MeasureTheory.volume (0 : ℝ) (1 : ℝ) := by
    apply Continuous.intervalIntegrable
    have hc1 : Continuous (fun t : ℝ => w ^ 2 * (1 - (t : ℂ))) :=
      continuous_const.mul (continuous_const.sub Complex.ofRealCLM.continuous)
    exact hc1.mul (continuous_cexp_ofReal_mul w)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  -- hftc : ∫ w²(1-t)exp(tw) dt = F(1) - F(0)
  have hF1 : F 1 = cexp w := by
    simp [F, Complex.ofReal_one, sub_self, mul_zero, zero_add, one_mul]
  have hF0 : F 0 = w + 1 := by
    simp [F, Complex.ofReal_zero, sub_zero, zero_mul, exp_zero, mul_one]
  rw [hF1, hF0] at hftc
  -- hftc : ∫ w²(1-t)exp(tw) dt = exp(w) - (w + 1) = exp(w) - 1 - w
  -- Pull w² out via smul
  have hsmul : (fun t : ℝ => w ^ 2 * (1 - (t : ℂ)) * cexp ((t : ℂ) * w)) =
      (fun t : ℝ => w ^ 2 • ((1 - (t : ℂ)) * cexp ((t : ℂ) * w))) := by
    ext t; simp [smul_eq_mul, mul_assoc]
  rw [hsmul, intervalIntegral.integral_smul, smul_eq_mul] at hftc
  -- hftc : w² * ∫ (1-t)exp(tw) = exp(w) - (w + 1)
  -- Goal : exp(w) - 1 - w = w² * ∫ (1-t)exp(tw)
  linear_combination hftc.symm

/-! ### Norm bounds -/

/-- `‖exp(w) - 1‖ ≤ ‖w‖ * exp(‖w‖)` from the integral representation.
    Proof: |∫₀¹ exp(tw)| ≤ ∫₀¹ |exp(tw)| ≤ ∫₀¹ exp(‖w‖) = exp(‖w‖). -/
theorem norm_cexp_sub_one_le (w : ℂ) :
    ‖cexp w - 1‖ ≤ ‖w‖ * Real.exp ‖w‖ := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp w 1
  have heq : ∑ m ∈ Finset.range 1, w ^ m / (m.factorial : ℂ) = 1 := by
    simp
  rw [heq, pow_one] at h
  exact h

/-- `‖exp(w) - 1 - w‖ ≤ ‖w‖² * exp(‖w‖)` from the integral representation.
    Proof: |∫₀¹ (1-t)exp(tw)| ≤ ∫₀¹ exp(‖w‖) = exp(‖w‖). -/
theorem norm_cexp_sub_one_sub_id_le (w : ℂ) :
    ‖cexp w - 1 - w‖ ≤ ‖w‖ ^ 2 * Real.exp ‖w‖ := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp w 2
  have heq : ∑ m ∈ Finset.range 2, w ^ m / (m.factorial : ℂ) = 1 + w := by
    simp [Finset.sum_range_succ]
  rw [heq] at h
  calc ‖cexp w - 1 - w‖ = ‖cexp w - (1 + w)‖ := by congr 1; ring
    _ ≤ ‖w‖ ^ 2 * Real.exp ‖w‖ := h

end
