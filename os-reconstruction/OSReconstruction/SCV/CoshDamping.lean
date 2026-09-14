import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Cosh damping on logarithmic strips

The OS-II logarithmic coordinates naturally produce exponential growth in the
real directions.  Multiplication by an entire nonvanishing cosh weight converts
that growth into a global bound on every strip `|Im zᵢ| < π / 2`.

The half argument is important: throughout the full strip,
`cos (Im zᵢ / 2) ≥ 1 / 2`, uniformly up to the open boundary.
-/

noncomputable section

open Complex Set
open scoped BigOperators

namespace OSReconstruction.SCV

variable {ι : Type*} [Fintype ι]

/-- The real cosh gauge used to measure exponential logarithmic growth. -/
def logCoshGauge (x : ι → ℝ) : ℝ :=
  ∑ i, Real.cosh (x i / 2)

/-- A real logarithmic coordinate is controlled by its half-cosh. The
constant four is intentionally coarse and keeps the proof elementary. -/
theorem le_four_mul_cosh_half (x : ℝ) :
    x ≤ 4 * Real.cosh (x / 2) := by
  by_cases hx : x ≤ 0
  · exact hx.trans (mul_nonneg (by norm_num) (Real.cosh_pos _).le)
  · have hx0 : 0 ≤ x / 2 := by
      exact div_nonneg (le_of_not_ge hx) (by norm_num)
    have hlin : x / 2 ≤ Real.exp (x / 2) := by
      calc
        x / 2 ≤ x / 2 + 1 := by linarith
        _ ≤ Real.exp (x / 2) := Real.add_one_le_exp _
    have hexp :
        Real.exp (x / 2) ≤ 2 * Real.cosh (x / 2) := by
      rw [Real.cosh_eq]
      nlinarith [Real.exp_pos (-(x / 2))]
    nlinarith

/-- Every coordinate is controlled by four times the full cosh gauge. -/
theorem coord_le_four_mul_logCoshGauge
    (x : ι → ℝ) (i : ι) :
    x i ≤ 4 * logCoshGauge x := by
  calc
    x i ≤ 4 * Real.cosh (x i / 2) :=
      le_four_mul_cosh_half (x i)
    _ ≤ 4 * logCoshGauge x := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.single_le_sum
        (fun j _ => (Real.cosh_pos (x j / 2)).le)
        (Finset.mem_univ i)

/-- All physical coefficients `exp xᵢ` share one exponential envelope given
by the full cosh gauge. -/
theorem exp_coord_le_exp_four_mul_logCoshGauge
    (x : ι → ℝ) (i : ι) :
    Real.exp (x i) ≤ Real.exp (4 * logCoshGauge x) :=
  Real.exp_le_exp.mpr (coord_le_four_mul_logCoshGauge x i)

/-- Entire nonvanishing damping weight for a prescribed nonnegative growth
rate.  The coefficient `2 * (rate + 1)` leaves one full cosh gauge of decay
after absorbing growth of rate `rate`. -/
def logCoshDamping (rate : ℝ) (z : ι → ℂ) : ℂ :=
  Complex.exp
    (-(2 * (rate + 1) : ℂ) * ∑ i, Complex.cosh (z i / 2))

theorem differentiable_logCoshDamping (rate : ℝ) :
    Differentiable ℂ (logCoshDamping (ι := ι) rate) := by
  unfold logCoshDamping
  fun_prop

@[simp]
theorem logCoshDamping_ne_zero (rate : ℝ) (z : ι → ℂ) :
    logCoshDamping rate z ≠ 0 :=
  Complex.exp_ne_zero _

private theorem complex_cosh_re (z : ℂ) :
    (Complex.cosh z).re =
      Real.cosh z.re * Real.cos z.im := by
  rw [Complex.cosh]
  norm_num [Complex.exp_re, Real.cosh_eq]
  ring

theorem logCoshDamping_norm
    (rate : ℝ) (z : ι → ℂ) :
    ‖logCoshDamping rate z‖ =
      Real.exp
        (-2 * (rate + 1) *
          ∑ i, Real.cosh ((z i).re / 2) * Real.cos ((z i).im / 2)) := by
  rw [logCoshDamping, Complex.norm_exp]
  have hsum :
      (∑ i, Complex.cosh (z i / 2)).re =
        ∑ i, Real.cosh ((z i).re / 2) * Real.cos ((z i).im / 2) := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [complex_cosh_re]
    norm_num
  rw [mul_re, hsum]
  norm_num

theorem half_le_cos_half_of_abs_lt_pi_div_two
    {y : ℝ} (hy : |y| < Real.pi / 2) :
    (1 / 2 : ℝ) ≤ Real.cos (y / 2) := by
  have habs : |y / 2| ≤ Real.pi / 3 := by
    have hquarter : |y / 2| < Real.pi / 4 := by
      rw [abs_div]
      norm_num
      nlinarith
    have hpi : Real.pi / 4 ≤ Real.pi / 3 := by
      nlinarith [Real.pi_pos]
    exact hquarter.le.trans hpi
  have hpi3 : Real.pi / 3 ≤ Real.pi := by
    nlinarith [Real.pi_pos]
  have hcos :
      Real.cos (Real.pi / 3) ≤ Real.cos |y / 2| :=
    Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hpi3 habs
  simpa [Real.cos_abs, Real.cos_pi_div_three] using hcos

/-- On the OS-II strip, the damping weight absorbs exponential growth
measured by `logCoshGauge` and leaves one extra gauge of decay. -/
theorem norm_logCoshDamping_le
    (rate : ℝ) (hrate : 0 ≤ rate)
    (z : ι → ℂ)
    (hz : ∀ i, |(z i).im| < Real.pi / 2) :
    ‖logCoshDamping rate z‖ ≤
      Real.exp (-(rate + 1) * logCoshGauge (fun i => (z i).re)) := by
  rw [logCoshDamping_norm]
  apply Real.exp_le_exp.mpr
  have hsum :
      logCoshGauge (fun i => (z i).re) ≤
        2 * ∑ i,
          Real.cosh ((z i).re / 2) * Real.cos ((z i).im / 2) := by
    rw [logCoshGauge, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _hi
    have hcos := half_le_cos_half_of_abs_lt_pi_div_two (hz i)
    have hcosh : 0 ≤ Real.cosh ((z i).re / 2) :=
      (Real.cosh_pos _).le
    nlinarith
  have hrate1 : 0 ≤ rate + 1 := by linarith
  nlinarith

/-- Exponential cosh growth becomes a uniform bound after damping. -/
theorem norm_mul_logCoshDamping_le
    (rate C : ℝ) (hrate : 0 ≤ rate) (hC : 0 ≤ C)
    (F : (ι → ℂ) → ℂ) (z : ι → ℂ)
    (hz : ∀ i, |(z i).im| < Real.pi / 2)
    (hF :
      ‖F z‖ ≤
        C * Real.exp (rate * logCoshGauge (fun i => (z i).re))) :
    ‖logCoshDamping rate z * F z‖ ≤ C := by
  rw [norm_mul]
  calc
    ‖logCoshDamping rate z‖ * ‖F z‖ ≤
        Real.exp (-(rate + 1) *
            logCoshGauge (fun i => (z i).re)) *
          (C * Real.exp
            (rate * logCoshGauge (fun i => (z i).re))) := by
      exact mul_le_mul
        (norm_logCoshDamping_le rate hrate z hz) hF
        (norm_nonneg _) (Real.exp_nonneg _)
    _ = C * Real.exp (-logCoshGauge (fun i => (z i).re)) := by
      calc
        Real.exp (-(rate + 1) *
              logCoshGauge (fun i => (z i).re)) *
            (C * Real.exp
              (rate * logCoshGauge (fun i => (z i).re))) =
          C * (Real.exp (-(rate + 1) *
              logCoshGauge (fun i => (z i).re)) *
            Real.exp
              (rate * logCoshGauge (fun i => (z i).re))) := by ring
        _ = C * Real.exp
            (-(rate + 1) * logCoshGauge (fun i => (z i).re) +
              rate * logCoshGauge (fun i => (z i).re)) := by
          rw [Real.exp_add]
        _ = C * Real.exp (-logCoshGauge (fun i => (z i).re)) := by
          congr 2
          ring
    _ ≤ C := by
      have hgauge :
          0 ≤ logCoshGauge (fun i => (z i).re) := by
        exact Finset.sum_nonneg fun i _ => (Real.cosh_pos _).le
      have hexp : Real.exp (-logCoshGauge (fun i => (z i).re)) ≤ 1 := by
        simpa using Real.exp_le_one_iff.mpr (neg_nonpos.mpr hgauge)
      simpa [mul_one] using mul_le_mul_of_nonneg_left hexp hC

end OSReconstruction.SCV
