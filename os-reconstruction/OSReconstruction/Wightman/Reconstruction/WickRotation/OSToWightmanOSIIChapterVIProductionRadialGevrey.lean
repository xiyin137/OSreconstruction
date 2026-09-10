/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib.Analysis.Complex.SqrtDeriv
import OSReconstruction.SCV.Analyticity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIProductionGevrey















noncomputable section

open scoped Classical

namespace OSReconstruction

def osiiProductionComplexRadialSquare
    {m : Nat} (z : Fin m → Complex) : Complex :=
  ∑ i, z i ^ 2

def osiiProductionComplexRadialRoot
    {m : Nat} (z : Fin m → Complex) : Complex :=
  Complex.sqrt (osiiProductionComplexRadialSquare z)

theorem osiiProductionComplexRadialSquare_differentiable
    (m : Nat) :
    Differentiable Complex
      (osiiProductionComplexRadialSquare (m := m)) := by
  unfold osiiProductionComplexRadialSquare
  fun_prop

theorem osiiProductionComplexRadialRoot_differentiableAt
    {m : Nat} {z : Fin m → Complex}
    (hz : 0 < (osiiProductionComplexRadialSquare z).re) :
    DifferentiableAt Complex osiiProductionComplexRadialRoot z := by
  exact
    (Complex.differentiableAt_sqrt
      (show osiiProductionComplexRadialSquare z ∈ Complex.slitPlane from
        Or.inl hz)).comp z
      (osiiProductionComplexRadialSquare_differentiable m z)

theorem osiiProductionComplexRadialSquare_real
    {m : Nat} (x : EuclideanSpace Real (Fin m)) :
    osiiProductionComplexRadialSquare (fun i => (x i : Complex)) =
      ((‖x‖ ^ 2 : Real) : Complex) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [osiiProductionComplexRadialSquare, Real.norm_eq_abs, sq_abs]

theorem osiiProductionComplexRadialRoot_real
    {m : Nat} (x : EuclideanSpace Real (Fin m)) :
    osiiProductionComplexRadialRoot (fun i => (x i : Complex)) =
      (‖x‖ : Complex) := by
  rw [osiiProductionComplexRadialRoot,
    osiiProductionComplexRadialSquare_real]
  rw [Complex.sqrt_of_nonneg (by exact_mod_cast sq_nonneg ‖x‖)]
  congr 1
  simpa only [pow_two, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] using
      Real.sqrt_sq (norm_nonneg x)

theorem osiiProductionComplexRadialSquare_deviation_bound
    {m : Nat} (hm : 0 < m)
    (x : EuclideanSpace Real (Fin m))
    (hx : ‖x‖ ≤ 2)
    {delta : Real} (hdelta : 0 < delta) (hdelta_half : delta ≤ 1 / 2)
    (z : Fin m → Complex)
    (hz : ∀ i, ‖z i - (x i : Complex)‖ ≤
      delta / (32768 * (m : Real))) :
    ‖osiiProductionComplexRadialSquare z -
        ((‖x‖ ^ 2 : Real) : Complex)‖ < delta / 4096 := by
  let a : Real := delta / (32768 * (m : Real))
  have hmreal : (0 : Real) < m := by exact_mod_cast hm
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have ha_one : a ≤ 1 := by
    dsimp [a]
    apply (div_le_iff₀ (by positivity)).2
    have hmone : (1 : Real) ≤ m := by exact_mod_cast hm
    nlinarith
  have hterm (i : Fin m) :
      ‖z i ^ 2 - (x i : Complex) ^ 2‖ ≤ a * 5 := by
    have hxi : ‖(x i : Complex)‖ ≤ ‖x‖ := by
      simpa [Complex.norm_real] using PiLp.norm_apply_le x i
    have hzi : ‖z i‖ ≤ a + ‖x‖ := by
      calc
        ‖z i‖ = ‖(z i - (x i : Complex)) + x i‖ := by
          congr 1
          ring
        _ ≤ ‖z i - (x i : Complex)‖ + ‖(x i : Complex)‖ :=
          norm_add_le _ _
        _ ≤ a + ‖x‖ := add_le_add (by simpa [a] using hz i) hxi
    have hsum : ‖z i + (x i : Complex)‖ ≤ 5 := by
      calc
        ‖z i + (x i : Complex)‖ ≤ ‖z i‖ + ‖(x i : Complex)‖ :=
          norm_add_le _ _
        _ ≤ (a + ‖x‖) + ‖x‖ := add_le_add hzi hxi
        _ ≤ 5 := by nlinarith
    calc
      ‖z i ^ 2 - (x i : Complex) ^ 2‖ =
        ‖z i + (x i : Complex)‖ * ‖z i - (x i : Complex)‖ := by
          rw [sq_sub_sq, norm_mul]
      _ ≤ 5 * a := mul_le_mul hsum (by simpa [a] using hz i)
        (norm_nonneg _) (by norm_num)
      _ = a * 5 := by ring
  calc
    ‖osiiProductionComplexRadialSquare z -
        ((‖x‖ ^ 2 : Real) : Complex)‖ =
      ‖∑ i, (z i ^ 2 - (x i : Complex) ^ 2)‖ := by
        rw [← osiiProductionComplexRadialSquare_real x]
        simp [osiiProductionComplexRadialSquare, ← Finset.sum_sub_distrib]
    _ ≤ ∑ i : Fin m, ‖z i ^ 2 - (x i : Complex) ^ 2‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i : Fin m, a * 5 := Finset.sum_le_sum fun i _ => hterm i
    _ = (m : Real) * (a * 5) := by simp
    _ = delta * 5 / 32768 := by
      dsimp [a]
      field_simp
    _ < delta / 4096 := by nlinarith

theorem osiiProductionComplexSqrt_re_nonneg (z : Complex) :
    0 ≤ (Complex.sqrt z).re := by
  rw [Complex.sqrt, Complex.cpow_inv_two_re]
  exact Real.sqrt_nonneg _

theorem osiiProductionComplexSqrt_sq (z : Complex) :
    (Complex.sqrt z) ^ 2 = z := by
  unfold Complex.sqrt
  exact Complex.cpow_nat_inv_pow z (by decide)

theorem osiiProductionComplexRadialSquare_realPart_pos
    {m : Nat} (hm : 0 < m)
    (x : EuclideanSpace Real (Fin m))
    (hx_lower : 1 ≤ ‖x‖) (hx_upper : ‖x‖ ≤ 2)
    {delta : Real} (hdelta : 0 < delta) (hdelta_half : delta ≤ 1 / 2)
    (z : Fin m → Complex)
    (hz : ∀ i, ‖z i - (x i : Complex)‖ ≤
      delta / (32768 * (m : Real))) :
    0 < (osiiProductionComplexRadialSquare z).re := by
  have hdev := osiiProductionComplexRadialSquare_deviation_bound
    hm x hx_upper hdelta hdelta_half z hz
  have hreal :
      |(osiiProductionComplexRadialSquare z).re - ‖x‖ ^ 2| <
        delta / 4096 := by
    have hnorm := Complex.abs_re_le_norm
      (osiiProductionComplexRadialSquare z -
        ((‖x‖ ^ 2 : Real) : Complex))
    simpa only [Complex.sub_re, pow_two, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using
        hnorm.trans_lt hdev
  have hsq : (1 : Real) ≤ ‖x‖ ^ 2 := by nlinarith
  have hlower := (abs_lt.mp hreal).1
  nlinarith

theorem osiiProductionComplexRadialRoot_deviation_bound
    {m : Nat} (hm : 0 < m)
    (x : EuclideanSpace Real (Fin m))
    (hx_lower : 1 ≤ ‖x‖) (hx_upper : ‖x‖ ≤ 2)
    {delta : Real} (hdelta : 0 < delta) (hdelta_half : delta ≤ 1 / 2)
    (z : Fin m → Complex)
    (hz : ∀ i, ‖z i - (x i : Complex)‖ ≤
      delta / (32768 * (m : Real))) :
    ‖osiiProductionComplexRadialRoot z - (‖x‖ : Complex)‖ <
      delta / 4096 := by
  have hdev := osiiProductionComplexRadialSquare_deviation_bound
    hm x hx_upper hdelta hdelta_half z hz
  have hroot_re : 0 ≤ (osiiProductionComplexRadialRoot z).re :=
    osiiProductionComplexSqrt_re_nonneg
      (osiiProductionComplexRadialSquare z)
  have hden :
      1 ≤ ‖osiiProductionComplexRadialRoot z + (‖x‖ : Complex)‖ := by
    have hreal := Complex.abs_re_le_norm
      (osiiProductionComplexRadialRoot z + (‖x‖ : Complex))
    have hreadd :
        0 ≤ (osiiProductionComplexRadialRoot z + (‖x‖ : Complex)).re := by
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith
    rw [abs_of_nonneg hreadd] at hreal
    simp only [Complex.add_re, Complex.ofReal_re] at hreal
    linarith
  have hfactor :
      (osiiProductionComplexRadialRoot z - (‖x‖ : Complex)) *
          (osiiProductionComplexRadialRoot z + (‖x‖ : Complex)) =
        osiiProductionComplexRadialSquare z -
          ((‖x‖ ^ 2 : Real) : Complex) := by
    calc
      (osiiProductionComplexRadialRoot z - (‖x‖ : Complex)) *
          (osiiProductionComplexRadialRoot z + (‖x‖ : Complex)) =
        osiiProductionComplexRadialRoot z ^ 2 -
          (‖x‖ : Complex) ^ 2 := by ring
      _ = osiiProductionComplexRadialSquare z -
          ((‖x‖ ^ 2 : Real) : Complex) := by
        rw [osiiProductionComplexRadialRoot,
          osiiProductionComplexSqrt_sq]
        norm_cast
  calc
    ‖osiiProductionComplexRadialRoot z - (‖x‖ : Complex)‖ ≤
      ‖osiiProductionComplexRadialRoot z - (‖x‖ : Complex)‖ *
        ‖osiiProductionComplexRadialRoot z + (‖x‖ : Complex)‖ :=
      le_mul_of_one_le_right (norm_nonneg _) hden
    _ = ‖(osiiProductionComplexRadialRoot z - (‖x‖ : Complex)) *
        (osiiProductionComplexRadialRoot z + (‖x‖ : Complex))‖ := by
          rw [norm_mul]
    _ = ‖osiiProductionComplexRadialSquare z -
          ((‖x‖ ^ 2 : Real) : Complex)‖ := by rw [hfactor]
    _ < delta / 4096 := hdev

def osiiProductionRadialAnnulusMargin
    {m : Nat} (x : EuclideanSpace Real (Fin m)) : Real :=
  min (‖x‖ - 1) (2 - ‖x‖)

theorem osiiProductionRadialAnnulusMargin_pos
    {m : Nat} (x : EuclideanSpace Real (Fin m))
    (hx_lower : 1 < ‖x‖) (hx_upper : ‖x‖ < 2) :
    0 < osiiProductionRadialAnnulusMargin x := by
  dsimp [osiiProductionRadialAnnulusMargin]
  exact lt_min (by linarith) (by linarith)

theorem osiiProductionRadialAnnulusMargin_le_half
    {m : Nat} (x : EuclideanSpace Real (Fin m)) :
    osiiProductionRadialAnnulusMargin x ≤ 1 / 2 := by
  dsimp [osiiProductionRadialAnnulusMargin]
  have hleft := min_le_left (‖x‖ - 1) (2 - ‖x‖)
  have hright := min_le_right (‖x‖ - 1) (2 - ‖x‖)
  linarith

theorem osiiProductionComplexRadialTransition_argument_deviation
    {m : Nat} (x : EuclideanSpace Real (Fin m)) (z : Fin m → Complex) :
    ‖(2 - osiiProductionComplexRadialRoot z) -
        ((2 - ‖x‖ : Real) : Complex)‖ =
      ‖osiiProductionComplexRadialRoot z - (‖x‖ : Complex)‖ := by
  have heq :
      (2 - osiiProductionComplexRadialRoot z) -
          ((2 - ‖x‖ : Real) : Complex) =
        -(osiiProductionComplexRadialRoot z - (‖x‖ : Complex)) := by
    push_cast
    ring
  rw [heq, norm_neg]

theorem osiiProductionComplexRadialTransition_denominator_ne_zero
    {m : Nat} (hm : 0 < m)
    (x : EuclideanSpace Real (Fin m))
    (hx_lower : 1 < ‖x‖) (hx_upper : ‖x‖ < 2)
    (z : Fin m → Complex)
    (hz : ∀ i, ‖z i - (x i : Complex)‖ ≤
      osiiProductionRadialAnnulusMargin x / (32768 * (m : Real))) :
    Complex.exp (-(2 - osiiProductionComplexRadialRoot z)⁻¹) +
        Complex.exp
          (-(1 - (2 - osiiProductionComplexRadialRoot z))⁻¹) ≠ 0 := by
  let delta := osiiProductionRadialAnnulusMargin x
  let t : Real := 2 - ‖x‖
  let w : Complex := 2 - osiiProductionComplexRadialRoot z
  have hdelta : 0 < delta :=
    osiiProductionRadialAnnulusMargin_pos x hx_lower hx_upper
  have hdelta_half : delta ≤ 1 / 2 :=
    osiiProductionRadialAnnulusMargin_le_half x
  have ht : 0 < t := by
    dsimp [t]
    linarith
  have ht_one : t < 1 := by
    dsimp [t]
    linarith
  have hdev : ‖w - (t : Complex)‖ < delta / 4096 := by
    rw [show ‖w - (t : Complex)‖ =
      ‖osiiProductionComplexRadialRoot z - (‖x‖ : Complex)‖ by
        exact osiiProductionComplexRadialTransition_argument_deviation x z]
    exact osiiProductionComplexRadialRoot_deviation_bound
      hm x hx_lower.le hx_upper.le hdelta hdelta_half z hz
  by_cases hleft : t ≤ 1 / 8
  · have hmargin : delta ≤ t := by
      exact min_le_right _ _
    have hdisc : ‖w - (t : Complex)‖ ≤ t / 4 := by
      nlinarith
    have hden := osiiProduction_endpoint_transition_denominator_bound
      ht hleft hdisc
    have hpositive : 0 < Real.exp (-2) / 2 := by positivity
    intro hzero
    change Complex.exp (-w⁻¹) + Complex.exp (-(1 - w)⁻¹) = 0 at hzero
    rw [hzero, norm_zero] at hden
    linarith
  by_cases hright : 7 / 8 ≤ t
  · let s : Real := 1 - t
    have hs : 0 < s := by
      dsimp [s]
      linarith
    have hs_small : s ≤ 1 / 8 := by
      dsimp [s]
      linarith
    have hmargin : delta ≤ s := by
      dsimp [delta, s, t, osiiProductionRadialAnnulusMargin]
      linarith [min_le_left (‖x‖ - 1) (2 - ‖x‖)]
    have hreflect : ‖(1 - w) - (s : Complex)‖ = ‖w - (t : Complex)‖ := by
      have heq : (1 - w) - (s : Complex) = -(w - (t : Complex)) := by
        dsimp [s]
        push_cast
        ring
      rw [heq, norm_neg]
    have hdisc : ‖(1 - w) - (s : Complex)‖ ≤ s / 4 := by
      rw [hreflect]
      nlinarith
    have hden := osiiProduction_endpoint_transition_denominator_bound
      hs hs_small hdisc
    have hpositive : 0 < Real.exp (-2) / 2 := by positivity
    intro hzero
    change Complex.exp (-w⁻¹) + Complex.exp (-(1 - w)⁻¹) = 0 at hzero
    have hswap :
        Complex.exp (-(1 - w)⁻¹) + Complex.exp (-(1 - (1 - w))⁻¹) = 0 := by
      simpa [add_comm] using hzero
    rw [hswap, norm_zero] at hden
    linarith
  · have hmiddle_lower : 1 / 8 ≤ t := le_of_lt (lt_of_not_ge hleft)
    have hmiddle_upper : t ≤ 7 / 8 := le_of_lt (lt_of_not_ge hright)
    have hdisc : ‖w - (t : Complex)‖ ≤ 1 / 1024 := by
      nlinarith
    exact osiiProduction_middle_transition_denominator_ne_zero
      hmiddle_lower hmiddle_upper hdisc

def osiiProductionComplexRadialBump
    {m : Nat} (z : Fin m → Complex) : Complex :=
  osiiProductionTransitionComplex
    (2 - osiiProductionComplexRadialRoot z)

theorem osiiProductionComplexRadialBump_differentiableAt
    {m : Nat} (hm : 0 < m)
    (x : EuclideanSpace Real (Fin m))
    (hx_lower : 1 < ‖x‖) (hx_upper : ‖x‖ < 2)
    (z : Fin m → Complex)
    (hz : ∀ i, ‖z i - (x i : Complex)‖ ≤
      osiiProductionRadialAnnulusMargin x / (32768 * (m : Real))) :
    DifferentiableAt Complex osiiProductionComplexRadialBump z := by
  let delta := osiiProductionRadialAnnulusMargin x
  let t : Real := 2 - ‖x‖
  let w : Complex := 2 - osiiProductionComplexRadialRoot z
  have hdelta : 0 < delta :=
    osiiProductionRadialAnnulusMargin_pos x hx_lower hx_upper
  have hdelta_half : delta ≤ 1 / 2 :=
    osiiProductionRadialAnnulusMargin_le_half x
  have ht : 0 < t := by
    dsimp [t]
    linarith
  have ht_one : t < 1 := by
    dsimp [t]
    linarith
  have hmargin_t : delta ≤ t := min_le_right _ _
  have hmargin_one : delta ≤ 1 - t := by
    dsimp [delta, t, osiiProductionRadialAnnulusMargin]
    linarith [min_le_left (‖x‖ - 1) (2 - ‖x‖)]
  have hdev : ‖w - (t : Complex)‖ < delta / 4096 := by
    rw [show ‖w - (t : Complex)‖ =
      ‖osiiProductionComplexRadialRoot z - (‖x‖ : Complex)‖ by
        exact osiiProductionComplexRadialTransition_argument_deviation x z]
    exact osiiProductionComplexRadialRoot_deviation_bound
      hm x hx_lower.le hx_upper.le hdelta hdelta_half z hz
  have hw_ne : w ≠ 0 := by
    intro hzero
    have hfalse := hdev
    rw [hzero] at hfalse
    simp [Complex.norm_real, abs_of_pos ht] at hfalse
    nlinarith
  have hcomplement_ne : 1 - w ≠ 0 := by
    intro hzero
    have hw : w = 1 := (sub_eq_zero.mp hzero).symm
    have hfalse := hdev
    rw [hw] at hfalse
    have hnorm : ‖(1 : Complex) - (t : Complex)‖ = 1 - t := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (sub_pos.mpr ht_one)]
    rw [hnorm] at hfalse
    nlinarith
  have hden := osiiProductionComplexRadialTransition_denominator_ne_zero
    hm x hx_lower hx_upper z hz
  have hroot := osiiProductionComplexRadialRoot_differentiableAt
    (osiiProductionComplexRadialSquare_realPart_pos
      hm x hx_lower.le hx_upper.le hdelta hdelta_half z hz)
  have htransition :
      DifferentiableAt Complex osiiProductionTransitionComplex w := by
    unfold osiiProductionTransitionComplex
    fun_prop (disch := aesop)
  exact htransition.comp z
    ((differentiableAt_const (2 : Complex)).sub hroot)

theorem osiiProductionComplexRadialBump_real
    {m : Nat} (x : EuclideanSpace Real (Fin m))
    (hx_lower : 1 < ‖x‖) (hx_upper : ‖x‖ < 2) :
    osiiProductionComplexRadialBump (fun i => (x i : Complex)) =
      (Real.smoothTransition (2 - ‖x‖) : Complex) := by
  rw [osiiProductionComplexRadialBump,
    osiiProductionComplexRadialRoot_real]
  have harg : (2 : Complex) - (‖x‖ : Complex) =
      ((2 - ‖x‖ : Real) : Complex) := by
    push_cast
    ring
  rw [harg]
  exact osiiProduction_productionTransitionComplex_ofReal
    (by linarith) (by linarith)

theorem osiiProductionTransitionComplex_one_sub
    {z : Complex}
    (hden : Complex.exp (-z⁻¹) + Complex.exp (-(1 - z)⁻¹) ≠ 0) :
    osiiProductionTransitionComplex (1 - z) =
      1 - osiiProductionTransitionComplex z := by
  unfold osiiProductionTransitionComplex
  rw [one_sub_div hden]
  congr 1 <;> ring_nf

def osiiProductionRadialAnnulusBaseline
    {m : Nat} (x : EuclideanSpace Real (Fin m)) : Complex :=
  if 7 / 8 ≤ 2 - ‖x‖ then 1 else 0

theorem osiiProductionComplexRadialBump_decay_bound
    {m : Nat} (hm : 0 < m)
    (x : EuclideanSpace Real (Fin m))
    (hx_lower : 1 < ‖x‖) (hx_upper : ‖x‖ < 2)
    (z : Fin m → Complex)
    (hz : ∀ i, ‖z i - (x i : Complex)‖ ≤
      osiiProductionRadialAnnulusMargin x / (32768 * (m : Real))) :
    ‖osiiProductionComplexRadialBump z -
        osiiProductionRadialAnnulusBaseline x‖ ≤
      Real.exp 6 *
        Real.exp (-(2 / (3 * osiiProductionRadialAnnulusMargin x))) := by
  let delta := osiiProductionRadialAnnulusMargin x
  let t : Real := 2 - ‖x‖
  let w : Complex := 2 - osiiProductionComplexRadialRoot z
  have hdelta : 0 < delta :=
    osiiProductionRadialAnnulusMargin_pos x hx_lower hx_upper
  have hdelta_half : delta ≤ 1 / 2 :=
    osiiProductionRadialAnnulusMargin_le_half x
  have ht : 0 < t := by
    dsimp [t]
    linarith
  have ht_one : t < 1 := by
    dsimp [t]
    linarith
  have hdev : ‖w - (t : Complex)‖ < delta / 4096 := by
    rw [show ‖w - (t : Complex)‖ =
      ‖osiiProductionComplexRadialRoot z - (‖x‖ : Complex)‖ by
        exact osiiProductionComplexRadialTransition_argument_deviation x z]
    exact osiiProductionComplexRadialRoot_deviation_bound
      hm x hx_lower.le hx_upper.le hdelta hdelta_half z hz
  have hcoefficient : 2 * Real.exp 2 ≤ Real.exp 6 := by
    have hexp_four : (2 : Real) ≤ Real.exp 4 := by
      nlinarith [Real.add_one_le_exp (4 : Real)]
    calc
      2 * Real.exp 2 ≤ Real.exp 4 * Real.exp 2 :=
        mul_le_mul_of_nonneg_right hexp_four (Real.exp_pos 2).le
      _ = Real.exp 6 := by
        rw [← Real.exp_add]
        norm_num
  by_cases hleft : t ≤ 1 / 8
  · have hnot_right : ¬ 7 / 8 ≤ t := by linarith
    have hbaseline : osiiProductionRadialAnnulusBaseline x = 0 := by
      simpa [osiiProductionRadialAnnulusBaseline, t] using hnot_right
    have hmargin : delta = t := by
      dsimp [delta, osiiProductionRadialAnnulusMargin, t]
      rw [min_eq_right]
      dsimp [t] at hleft
      linarith
    have hdisc : ‖w - (t : Complex)‖ ≤ t / 4 := by
      rw [hmargin] at hdev
      nlinarith
    have hbound := osiiProduction_endpoint_transition_quotient_bound
      ht hleft hdisc
    change ‖osiiProductionTransitionComplex w -
      osiiProductionRadialAnnulusBaseline x‖ ≤
      Real.exp 6 * Real.exp (-(2 / (3 * delta)))
    rw [hbaseline, sub_zero, hmargin]
    exact hbound.trans
      (mul_le_mul_of_nonneg_right hcoefficient (Real.exp_pos _).le)
  by_cases hright : 7 / 8 ≤ t
  · let s : Real := 1 - t
    have hs : 0 < s := by
      dsimp [s]
      linarith
    have hs_small : s ≤ 1 / 8 := by
      dsimp [s]
      linarith
    have hbaseline : osiiProductionRadialAnnulusBaseline x = 1 := by
      simpa [osiiProductionRadialAnnulusBaseline, t] using hright
    have hmargin : delta = s := by
      have horder : ‖x‖ - 1 ≤ 2 - ‖x‖ := by
        dsimp [t] at hright
        linarith
      dsimp [delta, osiiProductionRadialAnnulusMargin, s, t]
      rw [min_eq_left horder]
      ring
    have hreflect : ‖(1 - w) - (s : Complex)‖ = ‖w - (t : Complex)‖ := by
      have heq : (1 - w) - (s : Complex) = -(w - (t : Complex)) := by
        dsimp [s]
        push_cast
        ring
      rw [heq, norm_neg]
    have hdisc : ‖(1 - w) - (s : Complex)‖ ≤ s / 4 := by
      rw [hreflect]
      rw [hmargin] at hdev
      nlinarith
    have hbound := osiiProduction_endpoint_transition_quotient_bound
      hs hs_small hdisc
    have hden := osiiProductionComplexRadialTransition_denominator_ne_zero
      hm x hx_lower hx_upper z hz
    have hnorm :
        ‖osiiProductionTransitionComplex w - 1‖ =
          ‖osiiProductionTransitionComplex (1 - w)‖ := by
      rw [osiiProductionTransitionComplex_one_sub hden]
      exact norm_sub_rev _ _
    change ‖osiiProductionTransitionComplex w -
      osiiProductionRadialAnnulusBaseline x‖ ≤
      Real.exp 6 * Real.exp (-(2 / (3 * delta)))
    rw [hbaseline, hnorm, hmargin]
    exact hbound.trans
      (mul_le_mul_of_nonneg_right hcoefficient (Real.exp_pos _).le)
  · have hmiddle_lower : 1 / 8 ≤ t := le_of_lt (lt_of_not_ge hleft)
    have hmiddle_upper : t ≤ 7 / 8 := le_of_lt (lt_of_not_ge hright)
    have hbaseline : osiiProductionRadialAnnulusBaseline x = 0 := by
      simpa [osiiProductionRadialAnnulusBaseline, t] using hright
    have hdisc : ‖w - (t : Complex)‖ ≤ 1 / 1024 := by
      nlinarith
    have hbound :=
      (osiiProduction_middle_transition_quotient_bounds
        hmiddle_lower hmiddle_upper hdisc).1
    have hmargin_eighth : (1 / 8 : Real) ≤ delta := by
      dsimp [delta, osiiProductionRadialAnnulusMargin]
      apply le_min
      · dsimp [t] at hmiddle_upper
        linarith
      · dsimp [t] at hmiddle_lower
        linarith
    have hratio : 2 / (3 * delta) ≤ (6 : Real) := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith
    have hexp :
        (1 : Real) ≤ Real.exp 6 * Real.exp (-(2 / (3 * delta))) := by
      rw [← Real.exp_add]
      exact (Real.one_le_exp_iff).2 (by linarith)
    change ‖osiiProductionTransitionComplex w -
      osiiProductionRadialAnnulusBaseline x‖ ≤
      Real.exp 6 * Real.exp (-(2 / (3 * delta)))
    rw [hbaseline, sub_zero]
    exact hbound.trans hexp

theorem osiiProductionComplexRadialBump_cauchyCoeff_bound
    {m : Nat} (hm : 0 < m)
    (x : EuclideanSpace Real (Fin m))
    (hx_lower : 1 < ‖x‖) (hx_upper : ‖x‖ < 2)
    (alpha : Fin m → Nat) :
    ‖SCV.cauchyCoeffPolydisc
        (fun z => osiiProductionComplexRadialBump z -
          osiiProductionRadialAnnulusBaseline x)
        (fun i => (x i : Complex))
        (fun _ => osiiProductionRadialAnnulusMargin x /
          (65536 * (m : Real))) alpha‖ ≤
      Real.exp 6 *
        Real.exp (-(2 / (3 * osiiProductionRadialAnnulusMargin x))) /
        (osiiProductionRadialAnnulusMargin x /
          (65536 * (m : Real))) ^ (∑ i, alpha i) := by
  let delta := osiiProductionRadialAnnulusMargin x
  let R : Real := delta / (65536 * (m : Real))
  let M : Real := Real.exp 6 * Real.exp (-(2 / (3 * delta)))
  have hdelta : 0 < delta :=
    osiiProductionRadialAnnulusMargin_pos x hx_lower hx_upper
  have hmreal : (0 : Real) < m := by exact_mod_cast hm
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hcoeff := SCV.norm_cauchyCoeffPolydisc_le
    (fun z => osiiProductionComplexRadialBump z -
      osiiProductionRadialAnnulusBaseline x)
    (fun i => (x i : Complex)) (fun _ => R)
    (fun _ => hR) M hM
    (by
      intro z hz
      apply osiiProductionComplexRadialBump_decay_bound
        hm x hx_lower hx_upper z
      intro i
      have hi := SCV.mem_distinguishedBoundary_iff.mp hz i
      have hdist : ‖z i - (x i : Complex)‖ = R := by
        simpa [dist_eq_norm] using hi
      rw [hdist]
      dsimp [R]
      apply div_le_div_of_nonneg_left hdelta.le (by positivity)
      nlinarith)
    alpha
  convert hcoeff using 1
  simp [delta, R, M, Finset.prod_pow_eq_pow_sum]

theorem osiiProductionComplexRadialBump_cauchyCoeff_gevrey_bound
    {m : Nat} (hm : 0 < m)
    (x : EuclideanSpace Real (Fin m))
    (hx_lower : 1 < ‖x‖) (hx_upper : ‖x‖ < 2)
    (alpha : Fin m → Nat) :
    ‖SCV.cauchyCoeffPolydisc
        (fun z => osiiProductionComplexRadialBump z -
          osiiProductionRadialAnnulusBaseline x)
        (fun i => (x i : Complex))
        (fun _ => osiiProductionRadialAnnulusMargin x /
          (65536 * (m : Real))) alpha‖ ≤
      Real.exp 6 * (98304 * (m : Real)) ^ (∑ i, alpha i) *
        (((∑ i, alpha i).factorial : Nat) : Real) := by
  let delta := osiiProductionRadialAnnulusMargin x
  let j := ∑ i, alpha i
  have hdelta : 0 < delta :=
    osiiProductionRadialAnnulusMargin_pos x hx_lower hx_upper
  have hmreal : (0 : Real) < m := by exact_mod_cast hm
  have hcoeff := osiiProductionComplexRadialBump_cauchyCoeff_bound
    hm x hx_lower hx_upper alpha
  have hfactorial := osiiProduction_inverse_pow_mul_exp_le_factorial
    hdelta j
  calc
    ‖SCV.cauchyCoeffPolydisc
        (fun z => osiiProductionComplexRadialBump z -
          osiiProductionRadialAnnulusBaseline x)
        (fun i => (x i : Complex))
        (fun _ => delta / (65536 * (m : Real))) alpha‖ ≤
      Real.exp 6 * Real.exp (-(2 / (3 * delta))) /
        (delta / (65536 * (m : Real))) ^ j := hcoeff
    _ = Real.exp 6 * (65536 * (m : Real)) ^ j *
          (delta⁻¹ ^ j * Real.exp (-(2 / (3 * delta)))) := by
      rw [div_pow, div_div_eq_mul_div, div_eq_mul_inv, inv_pow]
      ring
    _ ≤ Real.exp 6 * (65536 * (m : Real)) ^ j *
          ((3 / 2 : Real) ^ j * (j.factorial : Real)) := by
      gcongr
    _ = Real.exp 6 * (98304 * (m : Real)) ^ j *
          (j.factorial : Real) := by
      have hscale :
          (65536 * (m : Real)) ^ j * (3 / 2 : Real) ^ j =
            (98304 * (m : Real)) ^ j := by
        rw [← mul_pow]
        congr 1
        ring
      calc
        Real.exp 6 * (65536 * (m : Real)) ^ j *
            ((3 / 2 : Real) ^ j * (j.factorial : Real)) =
          Real.exp 6 *
            ((65536 * (m : Real)) ^ j * (3 / 2 : Real) ^ j) *
              (j.factorial : Real) := by ring
        _ = Real.exp 6 * (98304 * (m : Real)) ^ j *
              (j.factorial : Real) := by rw [hscale]

def osiiProductionComplexBlockRealCoordinates
    (q : Nat) (z : Fin q → Complex) : EuclideanSpace Real (Fin (q * 2)) :=
  WithLp.toLp 2 fun j =>
    let p := (finProdFinEquiv : Fin q × Fin 2 ≃ Fin (q * 2)).symm j
    if p.2 = 0 then (z p.1).re else (z p.1).im

@[simp]
theorem osiiProductionComplexBlockRealCoordinates_apply_pair
    (q : Nat) (z : Fin q → Complex) (i : Fin q) (j : Fin 2) :
    osiiProductionComplexBlockRealCoordinates q z
        (finProdFinEquiv (i, j)) =
      if j = 0 then (z i).re else (z i).im := by
  change
    (if ((finProdFinEquiv : Fin q × Fin 2 ≃ Fin (q * 2)).symm
        (finProdFinEquiv (i, j))).2 = 0 then
      (z ((finProdFinEquiv : Fin q × Fin 2 ≃ Fin (q * 2)).symm
        (finProdFinEquiv (i, j))).1).re
    else
      (z ((finProdFinEquiv : Fin q × Fin 2 ≃ Fin (q * 2)).symm
        (finProdFinEquiv (i, j))).1).im) =
      if j = 0 then (z i).re else (z i).im
  simp only [Equiv.symm_apply_apply]

theorem osiiProductionComplexBlockRealCoordinates_norm
    (q : Nat) (z : Fin q → Complex) :
    ‖osiiProductionComplexBlockRealCoordinates q z‖ =
      ‖osiiStep4ComplexBlockToEuclideanCLE q z‖ := by
  have hsquare :
      ‖osiiProductionComplexBlockRealCoordinates q z‖ ^ 2 =
        ‖osiiStep4ComplexBlockToEuclideanCLE q z‖ ^ 2 := by
    calc
      ‖osiiProductionComplexBlockRealCoordinates q z‖ ^ 2 =
        ∑ j : Fin (q * 2),
          ‖osiiProductionComplexBlockRealCoordinates q z j‖ ^ 2 :=
        EuclideanSpace.norm_sq_eq _
      _ = ∑ p : Fin q × Fin 2,
          ‖osiiProductionComplexBlockRealCoordinates q z
            (finProdFinEquiv p)‖ ^ 2 :=
        (finProdFinEquiv.sum_comp
          (fun j : Fin (q * 2) =>
            ‖osiiProductionComplexBlockRealCoordinates q z j‖ ^ 2)).symm
      _ = ∑ i : Fin q, ((z i).re ^ 2 + (z i).im ^ 2) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro i _
        simp [Fin.sum_univ_two,
          osiiProductionComplexBlockRealCoordinates_apply_pair,
          Real.norm_eq_abs, sq_abs]
      _ = ∑ i : Fin q, ‖z i‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring
      _ = ‖osiiStep4ComplexBlockToEuclideanCLE q z‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        simp
  nlinarith [norm_nonneg (osiiProductionComplexBlockRealCoordinates q z),
    norm_nonneg (osiiStep4ComplexBlockToEuclideanCLE q z)]

end OSReconstruction
