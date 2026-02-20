/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Convex.Basic

/-!
# Rudin's Möbius Map for the Edge-of-the-Wedge Theorem

This file defines the Möbius map used in Rudin's proof of the continuous version
of the edge-of-the-wedge theorem (§4 of "Lectures on the Edge-of-the-Wedge Theorem",
CBMS #6, 1971).

## Main definitions

* `rudinC` — the constant c = √2 - 1
* `moebiusRudin w l` — the Möbius map φ(w, λ) = (w + λ/c) / (1 + c·λ·w)
* `moebiusProd w l` — the multi-variable version applying φ to each coordinate

## Main results

* `moebiusRudin_im_pos_iff` — Im(φ(w,l)) > 0 iff Im(l) > 0 when |l| = 1
* `moebiusRudin_zero_right` — φ(w, 0) = w
* `moebiusRudin_norm_le` — |φ(w,l)| ≤ 6 when |w| ≤ 1, |l| ≤ 1
* `moebiusRudin_differentiable_w` — φ is holomorphic in w

## References

* Rudin, W. "Lectures on the edge-of-the-wedge theorem", CBMS #6, AMS 1971, §4.
-/

noncomputable section

open Complex Filter Topology Set MeasureTheory Real

/-! ### The constant c = √2 - 1 -/

/-- Rudin's constant c = √2 - 1. -/
def rudinC : ℝ := Real.sqrt 2 - 1

theorem rudinC_pos : 0 < rudinC := by
  unfold rudinC
  have : Real.sqrt 2 > 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt (by linarith) (by linarith)
  linarith

theorem rudinC_lt_one : rudinC < 1 := by
  unfold rudinC
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by linarith), Real.sqrt_nonneg 2]

theorem rudinC_lt_half : rudinC < 1 / 2 := by
  unfold rudinC
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by linarith), Real.sqrt_nonneg 2,
    sq_nonneg (2 * Real.sqrt 2 - 3)]

theorem rudinC_ne_zero : rudinC ≠ 0 := ne_of_gt rudinC_pos

theorem rudinC_inv : rudinC⁻¹ = Real.sqrt 2 + 1 := by
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by linarith : (0:ℝ) ≤ 2)
  exact (eq_inv_of_mul_eq_one_left (show (Real.sqrt 2 + 1) * rudinC = 1 by
    unfold rudinC; nlinarith)).symm

/-- 1/c - c = 2 for c = √2 - 1. -/
theorem rudinC_inv_sub_self : rudinC⁻¹ - rudinC = 2 := by
  rw [rudinC_inv]; unfold rudinC; ring

/-- 1/c - c·t² > 0 for 0 ≤ t < 1. -/
theorem rudinC_inv_sub_mul_sq_pos {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    0 < rudinC⁻¹ - rudinC * t ^ 2 := by
  have h1 : rudinC * t ^ 2 < rudinC * 1 ^ 2 := by
    apply mul_lt_mul_of_pos_left _ rudinC_pos
    exact pow_lt_pow_left₀ ht1 ht two_ne_zero
  simp at h1
  linarith [rudinC_inv_sub_self]

/-! ### The Möbius map -/

/-- Rudin's Möbius map: φ(w, λ) = (w + λ/c) / (1 + c·λ·w).
    Here c = √2 - 1. This map has the key property that Im(φ(w, e^{iθ}))
    has the same sign as Im(e^{iθ}) when |w| < 1. -/
def moebiusRudin (w l : ℂ) : ℂ :=
  (w + l / (rudinC : ℂ)) / (1 + (rudinC : ℂ) * l * w)

/-- The denominator of the Möbius map. -/
def moebiusDenom (w l : ℂ) : ℂ := 1 + (rudinC : ℂ) * l * w

theorem moebiusDenom_ne_zero {w l : ℂ} (hw : ‖w‖ < 1) (hl : ‖l‖ ≤ 1) :
    moebiusDenom w l ≠ 0 := by
  intro h
  have h1 : ‖(rudinC : ℂ) * l * w‖ < 1 := by
    calc ‖(rudinC : ℂ) * l * w‖
        = ‖(rudinC : ℂ)‖ * ‖l‖ * ‖w‖ := by rw [norm_mul, norm_mul]
      _ = rudinC * ‖l‖ * ‖w‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg rudinC_pos.le]
      _ ≤ rudinC * 1 * ‖w‖ := by
          gcongr; exact rudinC_pos.le
      _ = rudinC * ‖w‖ := by ring_nf
      _ < rudinC * 1 := by gcongr; exact rudinC_pos
      _ < 1 := by rw [mul_one]; exact rudinC_lt_one
  simp only [moebiusDenom] at h
  have h3 : (rudinC : ℂ) * l * w = -1 := by linear_combination h
  have h4 : ‖(rudinC : ℂ) * l * w‖ = 1 := by rw [h3, norm_neg, norm_one]
  linarith

theorem moebiusDenom_ne_zero' {w l : ℂ} (hw : ‖w‖ ≤ 1) (hl : ‖l‖ < 1) :
    moebiusDenom w l ≠ 0 := by
  intro h
  have h1 : ‖(rudinC : ℂ) * l * w‖ < 1 := by
    calc ‖(rudinC : ℂ) * l * w‖
        = rudinC * ‖l‖ * ‖w‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg rudinC_pos.le]
      _ ≤ rudinC * ‖l‖ * 1 := by gcongr; exact mul_nonneg rudinC_pos.le (norm_nonneg _)
      _ = rudinC * ‖l‖ := by ring_nf
      _ < rudinC * 1 := by gcongr; exact rudinC_pos
      _ < 1 := by rw [mul_one]; exact rudinC_lt_one
  simp only [moebiusDenom] at h
  have h3 : (rudinC : ℂ) * l * w = -1 := by linear_combination h
  have : ‖(rudinC : ℂ) * l * w‖ = 1 := by rw [h3, norm_neg, norm_one]
  linarith

/-- When w is real and |w| < 1, moebiusDenom w l ≠ 0 for any l with Im(l) ≠ 0.
    The pole of moebiusRudin (in l) is at l = -1/(c·w) which is REAL when w is real.
    So for Im(l) ≠ 0, the denominator has nonzero imaginary part. -/
theorem moebiusDenom_ne_zero_of_real {w l : ℂ} (hw_im : w.im = 0)
    (hl_im : l.im ≠ 0) :
    moebiusDenom w l ≠ 0 := by
  intro h
  simp only [moebiusDenom] at h
  -- If 1 + c*l*w = 0, then Im(1 + c*l*w) = 0.
  -- But Im(1 + c*l*w) = c * (l.im * w.re + l.re * w.im) · ... let's compute.
  have him : (1 + (rudinC : ℂ) * l * w).im = 0 := by rw [h]; simp
  have him2 : ((rudinC : ℂ) * l * w).im = 0 := by
    have : (1 + (rudinC : ℂ) * l * w).im = 0 := by rw [h]; simp
    simpa [Complex.add_im] using this
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero] at him2
  -- him2 : rudinC * l.re * w.im + rudinC * l.im * w.re = 0
  rw [hw_im, mul_zero, zero_add] at him2
  -- him2 : rudinC * l.im * w.re = 0
  rcases mul_eq_zero.mp him2 with hcl | hre
  · -- rudinC * l.im = 0
    rcases mul_eq_zero.mp hcl with hc | him'
    · linarith [rudinC_pos]
    · exact hl_im him'
  · -- w.re = 0 and w.im = 0, so w = 0, so moebiusDenom = 1 ≠ 0
    have hw_zero : w = 0 := Complex.ext (by simpa using hre) (by simpa using hw_im)
    rw [hw_zero, mul_zero, add_zero] at h
    exact one_ne_zero h

/-- When w is real and |w| < 1, moebiusRudin w is differentiable at l for Im(l) ≠ 0. -/
theorem moebiusRudin_differentiableAt_of_real {w l : ℂ} (hw_im : w.im = 0)
    (hl_im : l.im ≠ 0) :
    DifferentiableAt ℂ (moebiusRudin w) l := by
  have hD : moebiusDenom w l ≠ 0 := moebiusDenom_ne_zero_of_real hw_im hl_im
  apply DifferentiableAt.div
  · exact (differentiableAt_const _).add
      (differentiableAt_id.div (differentiableAt_const _)
        (Complex.ofReal_ne_zero.mpr rudinC_ne_zero))
  · exact (differentiableAt_const 1).add
      (((differentiableAt_const (rudinC : ℂ)).mul differentiableAt_id).mul
        (differentiableAt_const w))
  · exact hD

/-- Denominator is nonzero when the product ‖c·l·w‖ < 1. This is the most general
    version, covering all cases (including real w with l up to |l| < 1/c ≈ 2.41). -/
theorem moebiusDenom_ne_zero_of_norm_prod {w l : ℂ} (h : ‖(rudinC : ℂ) * l * w‖ < 1) :
    moebiusDenom w l ≠ 0 := by
  intro heq
  simp only [moebiusDenom] at heq
  have h3 : (rudinC : ℂ) * l * w = -1 := by linear_combination heq
  linarith [show ‖(rudinC : ℂ) * l * w‖ = 1 from by rw [h3, norm_neg, norm_one]]

/-- moebiusRudin is differentiable at l whenever the denominator is nonzero.
    This gives ContinuousAt as a corollary via DifferentiableAt.continuousAt. -/
theorem moebiusRudin_differentiableAt_general {w l : ℂ} (hD : moebiusDenom w l ≠ 0) :
    DifferentiableAt ℂ (moebiusRudin w) l := by
  apply DifferentiableAt.div
  · exact (differentiableAt_const _).add
      (differentiableAt_id.div (differentiableAt_const _)
        (Complex.ofReal_ne_zero.mpr rudinC_ne_zero))
  · exact (differentiableAt_const 1).add
      (((differentiableAt_const (rudinC : ℂ)).mul differentiableAt_id).mul
        (differentiableAt_const w))
  · exact hD

/-! ### Property (3): φ(w, 0) = w -/

@[simp]
theorem moebiusRudin_zero_right (w : ℂ) : moebiusRudin w 0 = w := by
  simp [moebiusRudin]

/-! ### Imaginary part formula -/

/-- For any complex division: Im(a/b) = (a.im * b.re - a.re * b.im) / normSq b. -/
private theorem complex_div_im_eq (a b : ℂ) :
    (a / b).im = (a.im * b.re - a.re * b.im) / Complex.normSq b := by
  by_cases hb : b = 0
  · simp [hb]
  · rw [div_eq_mul_inv, Complex.inv_def, ← mul_assoc]
    have : a * (starRingEnd ℂ) b * (↑(Complex.normSq b)⁻¹ : ℂ) =
      a * (starRingEnd ℂ) b * (↑(Complex.normSq b))⁻¹ := by rw [Complex.ofReal_inv]
    rw [this, ← div_eq_mul_inv, Complex.div_ofReal_im, Complex.mul_im,
        Complex.conj_re, Complex.conj_im]
    ring

/-- The key imaginary part formula for the Möbius map:
    Im(φ(w,l)) = [Im(w)·(1-|l|²) + Im(l)·(1/c - c·|w|²)] / |1 + clw|²

    When |l| = 1, this simplifies to Im(l)·(1/c - c·|w|²) / |1 + clw|²,
    which has the same sign as Im(l) for |w| < 1. -/
theorem moebiusRudin_im {w l : ℂ} :
    (moebiusRudin w l).im =
      (w.im * (1 - Complex.normSq l) +
       l.im * (rudinC⁻¹ - rudinC * Complex.normSq w)) /
      Complex.normSq (moebiusDenom w l) := by
  simp only [moebiusRudin]
  rw [complex_div_im_eq]
  congr 1
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.div_ofReal_re, Complex.div_ofReal_im,
    Complex.one_re, Complex.one_im, Complex.normSq_apply,
    zero_mul, sub_zero, add_zero]
  field_simp [rudinC_ne_zero]
  ring

/-! ### Property (1): Sign of Im(φ) when |l| = 1 -/

private theorem normSq_lt_one_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    Complex.normSq z < 1 := by
  rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]

private theorem normSq_eq_one_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    Complex.normSq z = 1 := by
  rw [Complex.normSq_eq_norm_sq, hz, one_pow]

private theorem coeff_pos_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) :
    0 < rudinC⁻¹ - rudinC * Complex.normSq w := by
  have : rudinC * Complex.normSq w < rudinC :=
    calc rudinC * Complex.normSq w
        < rudinC * 1 := mul_lt_mul_of_pos_left (normSq_lt_one_of_norm_lt_one hw) rudinC_pos
      _ = rudinC := mul_one _
  linarith [rudinC_inv_sub_self]

/-- When |l| = 1 and |w| < 1: Im(φ(w,l)) > 0 iff Im(l) > 0. -/
theorem moebiusRudin_im_pos_iff {w l : ℂ} (hw : ‖w‖ < 1) (hl : ‖l‖ = 1) :
    0 < (moebiusRudin w l).im ↔ 0 < l.im := by
  rw [moebiusRudin_im]
  simp only [normSq_eq_one_of_norm_eq_one hl, sub_self, mul_zero, zero_add]
  rw [div_pos_iff_of_pos_right (Complex.normSq_pos.mpr (moebiusDenom_ne_zero hw hl.le))]
  exact ⟨fun h => by nlinarith [coeff_pos_of_norm_lt_one hw],
         fun h => mul_pos h (coeff_pos_of_norm_lt_one hw)⟩

/-- When |l| = 1 and |w| < 1: Im(φ(w,l)) < 0 iff Im(l) < 0. -/
theorem moebiusRudin_im_neg_iff {w l : ℂ} (hw : ‖w‖ < 1) (hl : ‖l‖ = 1) :
    (moebiusRudin w l).im < 0 ↔ l.im < 0 := by
  rw [moebiusRudin_im]
  simp only [normSq_eq_one_of_norm_eq_one hl, sub_self, mul_zero, zero_add]
  rw [div_neg_iff]
  have hDsq : 0 < Complex.normSq (moebiusDenom w l) :=
    Complex.normSq_pos.mpr (moebiusDenom_ne_zero hw hl.le)
  have hcoeff := coeff_pos_of_norm_lt_one hw
  constructor
  · rintro (⟨_, hD'⟩ | ⟨hnum, _⟩)
    · linarith
    · nlinarith
  · intro h; exact Or.inr ⟨by nlinarith, hDsq⟩

/-- Half-plane preservation for the disc interior:
    When Im(w) > 0, Im(l) ≥ 0, |w| < 1, |l| ≤ 1, then Im(φ(w,l)) > 0.
    The key point: the numerator Im(w)·(1-|l|²) + Im(l)·coeff has both terms ≥ 0,
    and the first is > 0 when |l| < 1 (since Im(w) > 0 and 1-|l|² > 0). -/
theorem moebiusRudin_im_pos_of_im_pos {w l : ℂ}
    (hw_norm : ‖w‖ < 1) (hl_norm : ‖l‖ ≤ 1)
    (hw_im : 0 < w.im) (hl_im : 0 ≤ l.im) (hl_not_real_circle : ‖l‖ < 1 ∨ 0 < l.im) :
    0 < (moebiusRudin w l).im := by
  rw [moebiusRudin_im]
  have hDsq : 0 < Complex.normSq (moebiusDenom w l) :=
    Complex.normSq_pos.mpr (moebiusDenom_ne_zero hw_norm hl_norm)
  rw [div_pos_iff_of_pos_right hDsq]
  have hcoeff := coeff_pos_of_norm_lt_one hw_norm
  have hnsq : Complex.normSq l ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]; exact pow_le_one₀ (norm_nonneg _) hl_norm
  rcases hl_not_real_circle with hl_lt | hl_pos
  · -- |l| < 1: first term Im(w)·(1-|l|²) > 0
    have h1 : 0 < 1 - Complex.normSq l := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg l]
    have hfirst : 0 < w.im * (1 - Complex.normSq l) := mul_pos hw_im h1
    have hsecond : 0 ≤ l.im * (rudinC⁻¹ - rudinC * Complex.normSq w) :=
      mul_nonneg hl_im hcoeff.le
    linarith
  · -- Im(l) > 0: second term Im(l)·coeff > 0
    have hfirst : 0 ≤ w.im * (1 - Complex.normSq l) :=
      mul_nonneg hw_im.le (sub_nonneg.mpr hnsq)
    have hsecond : 0 < l.im * (rudinC⁻¹ - rudinC * Complex.normSq w) :=
      mul_pos hl_pos hcoeff
    linarith

/-- Half-plane preservation: Im(w) < 0 and (|l| < 1 or Im(l) < 0) and |l| ≤ 1 → Im(φ) < 0. -/
theorem moebiusRudin_im_neg_of_im_neg {w l : ℂ}
    (hw_norm : ‖w‖ < 1) (hl_norm : ‖l‖ ≤ 1)
    (hw_im : w.im < 0) (hl_im : l.im ≤ 0) (hl_not_real_circle : ‖l‖ < 1 ∨ l.im < 0) :
    (moebiusRudin w l).im < 0 := by
  rw [moebiusRudin_im]
  have hDsq : 0 < Complex.normSq (moebiusDenom w l) :=
    Complex.normSq_pos.mpr (moebiusDenom_ne_zero hw_norm hl_norm)
  rw [div_neg_iff]
  have hcoeff := coeff_pos_of_norm_lt_one hw_norm
  have hnsq : Complex.normSq l ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]; exact pow_le_one₀ (norm_nonneg _) hl_norm
  rcases hl_not_real_circle with hl_lt | hl_neg
  · -- |l| < 1: first term Im(w)·(1-|l|²) < 0
    have h1 : 0 < 1 - Complex.normSq l := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg l]
    have hfirst : w.im * (1 - Complex.normSq l) < 0 := mul_neg_of_neg_of_pos hw_im h1
    have hsecond : l.im * (rudinC⁻¹ - rudinC * Complex.normSq w) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hl_im hcoeff.le
    exact Or.inr ⟨by linarith, hDsq⟩
  · -- Im(l) < 0: second term < 0
    have hfirst : w.im * (1 - Complex.normSq l) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hw_im.le (sub_nonneg.mpr hnsq)
    have hsecond : l.im * (rudinC⁻¹ - rudinC * Complex.normSq w) < 0 :=
      mul_neg_of_neg_of_pos hl_neg hcoeff
    exact Or.inr ⟨by linarith, hDsq⟩

/-- When w and l are real, φ(w,l) is real. -/
theorem moebiusRudin_im_zero {w l : ℂ} (hw : w.im = 0) (hl : l.im = 0) :
    (moebiusRudin w l).im = 0 := by
  simp only [moebiusRudin]
  rw [complex_div_im_eq]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
    Complex.div_ofReal_im, Complex.add_re, Complex.mul_re, Complex.div_ofReal_re,
    Complex.one_re, Complex.one_im, hw, hl, zero_mul, mul_zero, sub_zero,
    add_zero, zero_div, Complex.normSq_apply]

/-- When w is real with |w| < 1 and Im(l) > 0, Im(φ(w,l)) > 0.
    No constraint on ‖l‖ needed: the denominator is nonzero for any l with Im(l) ≠ 0
    when w is real (since the pole l = -1/(c·w) is real). -/
theorem moebiusRudin_im_pos_of_real {w l : ℂ} (hw_im : w.im = 0)
    (hw_norm : ‖w‖ < 1) (hl_pos : 0 < l.im) :
    0 < (moebiusRudin w l).im := by
  rw [moebiusRudin_im, hw_im, zero_mul, zero_add]
  exact div_pos (mul_pos hl_pos (coeff_pos_of_norm_lt_one hw_norm))
    (Complex.normSq_pos.mpr (moebiusDenom_ne_zero_of_real hw_im (ne_of_gt hl_pos)))

/-- When w is real with |w| < 1 and Im(l) < 0, Im(φ(w,l)) < 0. -/
theorem moebiusRudin_im_neg_of_real {w l : ℂ} (hw_im : w.im = 0)
    (hw_norm : ‖w‖ < 1) (hl_neg : l.im < 0) :
    (moebiusRudin w l).im < 0 := by
  rw [moebiusRudin_im, hw_im, zero_mul, zero_add]
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hl_neg (coeff_pos_of_norm_lt_one hw_norm))
    (Complex.normSq_pos.mpr (moebiusDenom_ne_zero_of_real hw_im (ne_of_lt hl_neg)))

/-- When |l| = 1 and l is real (i.e., l = ±1), φ(w,l) is real for ALL w.
    This is because the Rudin constant satisfies c · (1/c) = 1, which makes
    the Im(w)·(1 - |l|²) term vanish when |l| = 1. -/
theorem moebiusRudin_im_zero_of_unit_real {w l : ℂ}
    (hl_norm : Complex.normSq l = 1) (hl_im : l.im = 0) :
    (moebiusRudin w l).im = 0 := by
  rw [moebiusRudin_im, hl_norm, hl_im, sub_self, mul_zero, zero_mul, zero_add, zero_div]

/-! ### Property (4): Norm bound -/

/-- |φ(w,l)| ≤ 6 when |w| ≤ 1, |l| ≤ 1.
    The precise bound is (2+√2)/(2-√2) = 3 + 2√2 ≈ 5.83. -/
theorem moebiusRudin_norm_le {w l : ℂ} (hw : ‖w‖ ≤ 1) (hl : ‖l‖ ≤ 1) :
    ‖moebiusRudin w l‖ ≤ 6 := by
  -- numerator bound
  have hnum : ‖w + l / (rudinC : ℂ)‖ ≤ 1 + rudinC⁻¹ := by
    calc ‖w + l / (rudinC : ℂ)‖
        ≤ ‖w‖ + ‖l / (rudinC : ℂ)‖ := norm_add_le _ _
      _ = ‖w‖ + ‖l‖ / rudinC := by
          rw [norm_div, Complex.norm_real, Real.norm_of_nonneg rudinC_pos.le]
      _ ≤ 1 + 1 / rudinC := by
          have h1 : ‖l‖ / rudinC ≤ 1 / rudinC :=
            div_le_div_of_nonneg_right hl rudinC_pos.le
          linarith
      _ = 1 + rudinC⁻¹ := by rw [one_div]
  -- denominator lower bound
  have hclw_bound : ‖(rudinC : ℂ) * l * w‖ ≤ rudinC := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg rudinC_pos.le]
    have h1 : ‖l‖ * ‖w‖ ≤ 1 * 1 :=
      mul_le_mul hl hw (norm_nonneg _) zero_le_one
    have h2 : rudinC * (‖l‖ * ‖w‖) ≤ rudinC * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) rudinC_pos.le
    linarith
  have hdenom_lb : 1 - rudinC ≤ ‖1 + (rudinC : ℂ) * l * w‖ :=
    calc 1 - rudinC
        ≤ 1 - ‖(rudinC : ℂ) * l * w‖ := by linarith
      _ = ‖(1 : ℂ)‖ - ‖(rudinC : ℂ) * l * w‖ := by simp
      _ ≤ ‖(1 : ℂ) + (rudinC : ℂ) * l * w‖ := norm_sub_le_norm_add _ _
  have hdenom_pos : (0 : ℝ) < ‖1 + (rudinC : ℂ) * l * w‖ := by
    linarith [rudinC_lt_one]
  -- combine: ‖N/D‖ = ‖N‖/‖D‖ ≤ (1+1/c)/(1-c) ≤ 6
  simp only [moebiusRudin, norm_div]
  rw [div_le_iff₀ hdenom_pos]
  calc ‖w + l / ↑rudinC‖
      ≤ 1 + rudinC⁻¹ := hnum
    _ ≤ 6 * (1 - rudinC) := by
        -- 1 + (√2+1) ≤ 6*(2-√2), i.e. 2+√2 ≤ 12-6√2, i.e. 7√2 ≤ 10, i.e. 98 ≤ 100
        rw [rudinC_inv]; unfold rudinC
        have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by linarith : (0:ℝ) ≤ 2)
        nlinarith [Real.sqrt_nonneg 2, sq_nonneg (7 * Real.sqrt 2 - 10)]
    _ ≤ 6 * ‖1 + (rudinC : ℂ) * l * w‖ := by linarith

/-! ### Holomorphicity -/

/-- The Möbius map is holomorphic in w for each fixed l with |l| ≤ 1. -/
theorem moebiusRudin_differentiable_w (l : ℂ) (hl : ‖l‖ ≤ 1) :
    DifferentiableOn ℂ (fun w => moebiusRudin w l) (Metric.ball 0 1) := by
  intro w hw
  simp only [Metric.mem_ball, dist_zero_right] at hw
  have hD : moebiusDenom w l ≠ 0 := moebiusDenom_ne_zero hw hl
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.div
  · exact differentiableAt_id.add (differentiableAt_const _)
  · exact (differentiableAt_const 1).add
      ((differentiableAt_const ((rudinC : ℂ) * l)).mul differentiableAt_id)
  · exact hD

/-- The Möbius map is holomorphic in l for each fixed w with |w| < 1. -/
theorem moebiusRudin_differentiable_l (w : ℂ) (hw : ‖w‖ < 1) :
    DifferentiableOn ℂ (moebiusRudin w) (Metric.ball 0 1) := by
  intro l hl
  simp only [Metric.mem_ball, dist_zero_right] at hl
  have hD : moebiusDenom w l ≠ 0 := moebiusDenom_ne_zero' (le_of_lt hw) hl
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.div
  · exact (differentiableAt_const _).add
      (differentiableAt_id.div (differentiableAt_const _)
        (Complex.ofReal_ne_zero.mpr rudinC_ne_zero))
  · exact (differentiableAt_const 1).add
      (((differentiableAt_const (rudinC : ℂ)).mul differentiableAt_id).mul
        (differentiableAt_const w))
  · exact hD

/-- The Möbius map is continuous in (w, l) on ball × closedBall. -/
theorem moebiusRudin_continuousOn :
    ContinuousOn (fun p : ℂ × ℂ => moebiusRudin p.1 p.2)
      (Metric.ball 0 1 ×ˢ Metric.closedBall 0 1) := by
  apply ContinuousOn.div
  · exact continuousOn_fst.add (continuousOn_snd.div continuousOn_const
      (fun _ _ => Complex.ofReal_ne_zero.mpr rudinC_ne_zero))
  · exact continuousOn_const.add ((continuousOn_const.mul continuousOn_snd).mul continuousOn_fst)
  · intro ⟨w, l⟩ hmem
    simp only [mem_prod, Metric.mem_ball, Metric.mem_closedBall, dist_zero_right] at hmem
    exact moebiusDenom_ne_zero hmem.1 hmem.2

/-! ### Multi-variable version -/

/-- Apply the Möbius map componentwise: Φ(w, l) = (φ(w₁,l), ..., φ(wₘ,l)). -/
def moebiusProd {m : ℕ} (w : Fin m → ℂ) (l : ℂ) : Fin m → ℂ :=
  fun j => moebiusRudin (w j) l

@[simp]
theorem moebiusProd_zero_right {m : ℕ} (w : Fin m → ℂ) :
    moebiusProd w 0 = w := by
  ext j; simp [moebiusProd]

/-- When |l| = 1 and Im(l) > 0, all components of moebiusProd have positive Im. -/
theorem moebiusProd_im_pos {m : ℕ} {w : Fin m → ℂ} {l : ℂ}
    (hw : ∀ j, ‖w j‖ < 1) (hl : ‖l‖ = 1) (hl_pos : 0 < l.im) :
    ∀ j, 0 < (moebiusProd w l j).im := by
  intro j
  exact (moebiusRudin_im_pos_iff (hw j) hl).mpr hl_pos

/-- When |l| = 1 and Im(l) < 0, all components have negative Im. -/
theorem moebiusProd_im_neg {m : ℕ} {w : Fin m → ℂ} {l : ℂ}
    (hw : ∀ j, ‖w j‖ < 1) (hl : ‖l‖ = 1) (hl_neg : l.im < 0) :
    ∀ j, (moebiusProd w l j).im < 0 := by
  intro j
  exact (moebiusRudin_im_neg_iff (hw j) hl).mpr hl_neg

/-- Half-plane preservation for moebiusProd: if all Im(wⱼ) > 0, Im(l) ≥ 0,
    |wⱼ| < 1, |l| ≤ 1, and (|l| < 1 or Im(l) > 0), then all Im(mp) > 0. -/
theorem moebiusProd_im_pos_of_im_pos {m : ℕ} {w : Fin m → ℂ} {l : ℂ}
    (hw : ∀ j, ‖w j‖ < 1) (hl : ‖l‖ ≤ 1)
    (hw_im : ∀ j, 0 < (w j).im) (hl_im : 0 ≤ l.im)
    (hl_cond : ‖l‖ < 1 ∨ 0 < l.im) :
    ∀ j, 0 < (moebiusProd w l j).im := by
  intro j
  exact moebiusRudin_im_pos_of_im_pos (hw j) hl (hw_im j) hl_im hl_cond

/-- Half-plane preservation for moebiusProd: negative version. -/
theorem moebiusProd_im_neg_of_im_neg {m : ℕ} {w : Fin m → ℂ} {l : ℂ}
    (hw : ∀ j, ‖w j‖ < 1) (hl : ‖l‖ ≤ 1)
    (hw_im : ∀ j, (w j).im < 0) (hl_im : l.im ≤ 0)
    (hl_cond : ‖l‖ < 1 ∨ l.im < 0) :
    ∀ j, (moebiusProd w l j).im < 0 := by
  intro j
  exact moebiusRudin_im_neg_of_im_neg (hw j) hl (hw_im j) hl_im hl_cond

/-- When l is real (Im = 0) and all w are real: moebiusProd maps to reals. -/
theorem moebiusProd_real {m : ℕ} {w : Fin m → ℂ} {l : ℂ}
    (hw : ∀ j, (w j).im = 0) (hl : l.im = 0) :
    ∀ j, (moebiusProd w l j).im = 0 := by
  intro j; exact moebiusRudin_im_zero (hw j) hl

/-- When |l| = 1 and l is real (l = ±1), moebiusProd maps ANY w to reals. -/
theorem moebiusProd_real_of_unit_real {m : ℕ} {w : Fin m → ℂ} {l : ℂ}
    (hl_norm : Complex.normSq l = 1) (hl_im : l.im = 0) :
    ∀ j, (moebiusProd w l j).im = 0 := by
  intro j; exact moebiusRudin_im_zero_of_unit_real hl_norm hl_im

/-- When all w are real with |w_j| < 1 and Im(l) > 0, all Im(moebiusProd) > 0.
    No bound on ‖l‖ needed. -/
theorem moebiusProd_im_pos_of_real {m : ℕ} {w : Fin m → ℂ} {l : ℂ}
    (hw_im : ∀ j, (w j).im = 0) (hw_norm : ∀ j, ‖w j‖ < 1) (hl_pos : 0 < l.im) :
    ∀ j, 0 < (moebiusProd w l j).im := by
  intro j; exact moebiusRudin_im_pos_of_real (hw_im j) (hw_norm j) hl_pos

/-- When all w are real with |w_j| < 1 and Im(l) < 0, all Im(moebiusProd) < 0. -/
theorem moebiusProd_im_neg_of_real {m : ℕ} {w : Fin m → ℂ} {l : ℂ}
    (hw_im : ∀ j, (w j).im = 0) (hw_norm : ∀ j, ‖w j‖ < 1) (hl_neg : l.im < 0) :
    ∀ j, (moebiusProd w l j).im < 0 := by
  intro j; exact moebiusRudin_im_neg_of_real (hw_im j) (hw_norm j) hl_neg

/-- The norm bound for each component of moebiusProd. -/
theorem moebiusProd_norm_le {m : ℕ} {w : Fin m → ℂ} {l : ℂ}
    (hw : ∀ j, ‖w j‖ ≤ 1) (hl : ‖l‖ ≤ 1) :
    ∀ j, ‖moebiusProd w l j‖ ≤ 6 := by
  intro j; exact moebiusRudin_norm_le (hw j) hl

/-- moebiusProd is holomorphic in l at any point with Im(l) ≠ 0 when all w are real. -/
theorem moebiusProd_differentiableAt_l_of_real {m : ℕ} {w : Fin m → ℂ} {l : ℂ}
    (hw_im : ∀ j, (w j).im = 0) (hl_im : l.im ≠ 0) :
    DifferentiableAt ℂ (moebiusProd w) l := by
  rw [show moebiusProd w = fun l => (fun j => moebiusRudin (w j) l) from rfl]
  exact differentiableAt_pi.mpr fun j => moebiusRudin_differentiableAt_of_real (hw_im j) hl_im

/-- moebiusProd is holomorphic in w. -/
theorem moebiusProd_differentiable_w {m : ℕ} (l : ℂ) (hl : ‖l‖ ≤ 1) :
    DifferentiableOn ℂ (fun w : Fin m → ℂ => moebiusProd w l)
      {w | ∀ j, ‖w j‖ < 1} := by
  intro w hw
  rw [differentiableWithinAt_pi]
  intro j
  show DifferentiableWithinAt ℂ (fun w => moebiusRudin (w j) l) {w | ∀ j, ‖w j‖ < 1} w
  have hdiff_proj : DifferentiableAt ℂ (fun w : Fin m → ℂ => w j) w :=
    (differentiableAt_pi.mp differentiableAt_id) j
  have hmem : w j ∈ Metric.ball (0 : ℂ) 1 := by
    simp [Metric.mem_ball, dist_zero_right]; exact hw j
  have hdiff_moeb : DifferentiableAt ℂ (fun z => moebiusRudin z l) (w j) :=
    (moebiusRudin_differentiable_w l hl).differentiableAt (Metric.isOpen_ball.mem_nhds hmem)
  exact (hdiff_moeb.comp w hdiff_proj).differentiableWithinAt

/-! ### Extended norm bound for ‖w‖ ≤ 1/2, ‖l‖ ≤ 2 -/

/-- The denominator is nonzero for ‖w‖ ≤ 1/2 and ‖l‖ ≤ 2 since ‖c·l·w‖ ≤ c < 1. -/
theorem moebiusDenom_ne_zero_extended {w l : ℂ} (hw : ‖w‖ ≤ 1 / 2) (hl : ‖l‖ ≤ 2) :
    moebiusDenom w l ≠ 0 := by
  have h1 : ‖(rudinC : ℂ) * l * w‖ < 1 := by
    calc ‖(rudinC : ℂ) * l * w‖
        = ‖(rudinC : ℂ)‖ * ‖l‖ * ‖w‖ := by rw [norm_mul, norm_mul]
      _ = rudinC * ‖l‖ * ‖w‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg rudinC_pos.le]
      _ ≤ rudinC * 2 * (1 / 2) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hl rudinC_pos.le) hw
            (norm_nonneg _) (mul_nonneg rudinC_pos.le (by norm_num))
      _ = rudinC := by ring
      _ < 1 := rudinC_lt_one
  intro h
  have h2 : ‖(1 : ℂ) + (rudinC : ℂ) * l * w‖ = 0 := by
    simp only [moebiusDenom] at h; rw [h, norm_zero]
  linarith [calc (0 : ℝ) < 1 - ‖(rudinC : ℂ) * l * w‖ := by linarith
    _ = ‖(1 : ℂ)‖ - ‖(rudinC : ℂ) * l * w‖ := by simp
    _ ≤ ‖(1 : ℂ) + (rudinC : ℂ) * l * w‖ := norm_sub_le_norm_add _ _]

/-- |φ(w,l)| ≤ 10 when |w| ≤ 1/2, |l| ≤ 2.
    The precise bound is (5/2+2√2)/(2-√2) ≈ 9.09. -/
theorem moebiusRudin_norm_le_extended {w l : ℂ} (hw : ‖w‖ ≤ 1 / 2) (hl : ‖l‖ ≤ 2) :
    ‖moebiusRudin w l‖ ≤ 10 := by
  -- numerator bound: ‖w + l/c‖ ≤ 1/2 + 2/c = 1/2 + 2(√2+1) = 5/2 + 2√2
  have hnum : ‖w + l / (rudinC : ℂ)‖ ≤ 1 / 2 + 2 * rudinC⁻¹ := by
    calc ‖w + l / (rudinC : ℂ)‖
        ≤ ‖w‖ + ‖l / (rudinC : ℂ)‖ := norm_add_le _ _
      _ = ‖w‖ + ‖l‖ / rudinC := by
          rw [norm_div, Complex.norm_real, Real.norm_of_nonneg rudinC_pos.le]
      _ ≤ 1 / 2 + 2 / rudinC := by
          gcongr; exact rudinC_pos.le
      _ = 1 / 2 + 2 * rudinC⁻¹ := by rw [div_eq_mul_inv 2 rudinC]
  -- denominator lower bound: ‖1 + clw‖ ≥ 1 - c
  have hclw_bound : ‖(rudinC : ℂ) * l * w‖ ≤ rudinC := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg rudinC_pos.le]
    calc rudinC * ‖l‖ * ‖w‖ ≤ rudinC * 2 * (1 / 2) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hl rudinC_pos.le) hw
            (norm_nonneg _) (mul_nonneg rudinC_pos.le (by norm_num))
      _ = rudinC := by ring
  have hdenom_lb : 1 - rudinC ≤ ‖1 + (rudinC : ℂ) * l * w‖ :=
    calc 1 - rudinC
        ≤ 1 - ‖(rudinC : ℂ) * l * w‖ := by linarith
      _ = ‖(1 : ℂ)‖ - ‖(rudinC : ℂ) * l * w‖ := by simp
      _ ≤ ‖(1 : ℂ) + (rudinC : ℂ) * l * w‖ := norm_sub_le_norm_add _ _
  have hdenom_pos : (0 : ℝ) < ‖1 + (rudinC : ℂ) * l * w‖ := by
    linarith [rudinC_lt_one]
  -- combine: (1/2 + 2(√2+1)) / (1 - (√2-1)) = (5/2 + 2√2) / (2 - √2) ≤ 10
  simp only [moebiusRudin, norm_div]
  rw [div_le_iff₀ hdenom_pos]
  calc ‖w + l / ↑rudinC‖
      ≤ 1 / 2 + 2 * rudinC⁻¹ := hnum
    _ ≤ 10 * (1 - rudinC) := by
        -- Need: 1/2 + 2(√2+1) ≤ 10(2-√2), i.e., 5/2 + 2√2 ≤ 20 - 10√2
        -- i.e., 12√2 ≤ 35/2, i.e., 24√2 ≤ 35, i.e., 1152 ≤ 1225
        rw [rudinC_inv]; unfold rudinC
        have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by linarith : (0:ℝ) ≤ 2)
        nlinarith [Real.sqrt_nonneg 2, sq_nonneg (7 - 5 * Real.sqrt 2)]
    _ ≤ 10 * ‖1 + (rudinC : ℂ) * l * w‖ := by linarith

/-- The extended norm bound for each component of moebiusProd. -/
theorem moebiusProd_norm_le_extended {m : ℕ} {w : Fin m → ℂ} {l : ℂ}
    (hw : ∀ j, ‖w j‖ ≤ 1 / 2) (hl : ‖l‖ ≤ 2) :
    ∀ j, ‖moebiusProd w l j‖ ≤ 10 := by
  intro j; exact moebiusRudin_norm_le_extended (hw j) hl

end
