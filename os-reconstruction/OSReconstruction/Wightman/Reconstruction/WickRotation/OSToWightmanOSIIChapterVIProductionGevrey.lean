/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Data.Nat.Choose.Multinomial
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialRegularizer















noncomputable section

open scoped Classical

namespace OSReconstruction

def osiiProductionTransitionComplex (z : Complex) : Complex :=
  Complex.exp (-z⁻¹) /
    (Complex.exp (-z⁻¹) + Complex.exp (-(1 - z)⁻¹))

theorem osiiProduction_productionTransitionComplex_ofReal
    {x : Real} (hx : 0 < x) (hx_one : x < 1) :
    osiiProductionTransitionComplex (x : Complex) =
      (Real.smoothTransition x : Complex) := by
  rw [Real.smoothTransition]
  simp [osiiProductionTransitionComplex, expNegInvGlue,
    not_le_of_gt hx, not_le_of_gt (sub_pos.mpr hx_one),
    Complex.ofReal_exp]

theorem osiiProduction_pow_mul_exp_neg_le_factorial
    {v : Real} (hv : 0 ≤ v) (n : Nat) :
    v ^ n * Real.exp (-v) ≤ (n.factorial : Real) := by
  have hfactorial : (0 : Real) < n.factorial := by positivity
  have h := Real.pow_div_factorial_le_exp v hv n
  have hmul : v ^ n ≤ (n.factorial : Real) * Real.exp v := by
    simpa [mul_comm] using (div_le_iff₀ hfactorial).mp h
  have hexp : 0 < Real.exp (-v) := Real.exp_pos _
  calc
    v ^ n * Real.exp (-v) ≤
        ((n.factorial : Real) * Real.exp v) * Real.exp (-v) :=
      mul_le_mul_of_nonneg_right hmul hexp.le
    _ = (n.factorial : Real) := by
      rw [mul_assoc, ← Real.exp_add]
      simp

theorem osiiProduction_inverse_pow_mul_exp_le_factorial
    {t : Real} (ht : 0 < t) (n : Nat) :
    t⁻¹ ^ n * Real.exp (-(2 / (3 * t))) ≤
      (3 / 2 : Real) ^ n * (n.factorial : Real) := by
  have hvariable : 0 ≤ (2 / (3 * t) : Real) := by positivity
  have hinverse : t⁻¹ = (3 / 2 : Real) * (2 / (3 * t)) := by
    field_simp
  calc
    t⁻¹ ^ n * Real.exp (-(2 / (3 * t))) =
        (3 / 2 : Real) ^ n *
          ((2 / (3 * t)) ^ n * Real.exp (-(2 / (3 * t)))) := by
      rw [hinverse, mul_pow]
      ring
    _ ≤ (3 / 2 : Real) ^ n * (n.factorial : Real) :=
      mul_le_mul_of_nonneg_left
        (osiiProduction_pow_mul_exp_neg_le_factorial hvariable n) (by positivity)

theorem osiiProduction_endpoint_complex_inverse_real_bound
    {t : Real} (ht : 0 < t)
    {z : Complex} (hz : ‖z - (t : Complex)‖ ≤ t / 4) :
    2 / (3 * t) ≤ (z⁻¹).re := by
  have hreabs : |z.re - t| ≤ t / 4 := by
    calc
      |z.re - t| = |(z - (t : Complex)).re| := by simp
      _ ≤ ‖z - (t : Complex)‖ := Complex.abs_re_le_norm _
      _ ≤ t / 4 := hz
  have hrelower : -(t / 4) ≤ z.re - t := (abs_le.mp hreabs).1
  have hreupper : z.re - t ≤ t / 4 := (abs_le.mp hreabs).2
  have hre : 0 < z.re := by linarith
  have hnonzero : z ≠ 0 := by
    intro heq
    rw [heq] at hre
    simp at hre
  have hnormsq : 0 < Complex.normSq z :=
    Complex.normSq_pos.mpr hnonzero
  have hsquare : (z.re - t) ^ 2 + z.im ^ 2 ≤ (t / 4) ^ 2 := by
    have h := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hz
    rw [Complex.sq_norm] at h
    simpa [Complex.sq_norm, Complex.normSq_apply, pow_two] using h
  rw [Complex.inv_re]
  apply (div_le_div_iff₀ (by positivity : (0 : Real) < 3 * t)
    hnormsq).2
  rw [Complex.normSq_apply]
  have hupper_product : 0 ≤ t * (5 * t / 4 - z.re) := by
    apply mul_nonneg ht.le
    linarith
  nlinarith [hsquare]

theorem osiiProduction_endpoint_complex_complement_norm_bound
    {t : Real} (ht : 0 < t) (htsmall : t ≤ 1 / 8)
    {z : Complex} (hz : ‖z - (t : Complex)‖ ≤ t / 4) :
    (27 / 32 : Real) ≤ ‖1 - z‖ := by
  have hznorm : ‖z‖ ≤ 5 * t / 4 := by
    calc
      ‖z‖ = ‖(z - (t : Complex)) + (t : Complex)‖ := by simp
      _ ≤ ‖z - (t : Complex)‖ + ‖(t : Complex)‖ :=
        norm_add_le _ _
      _ ≤ t / 4 + t := by
        simpa [Real.norm_eq_abs, abs_of_pos ht] using
          add_le_add_right hz t
      _ = 5 * t / 4 := by ring
  have htriangle : (1 : Real) ≤ ‖1 - z‖ + ‖z‖ := by
    calc
      (1 : Real) = ‖(1 - z) + z‖ := by simp
      _ ≤ ‖1 - z‖ + ‖z‖ := norm_add_le _ _
  nlinarith

theorem osiiProduction_endpoint_transition_denominator_bound
    {t : Real} (ht : 0 < t) (htsmall : t ≤ 1 / 8)
    {z : Complex} (hz : ‖z - (t : Complex)‖ ≤ t / 4) :
    Real.exp (-2) / 2 <
      ‖Complex.exp (-z⁻¹) + Complex.exp (-(1 - z)⁻¹)‖ := by
  have hinverse := osiiProduction_endpoint_complex_inverse_real_bound ht hz
  have hcomplement :=
    osiiProduction_endpoint_complex_complement_norm_bound ht htsmall hz
  have hcomplement_pos : 0 < ‖1 - z‖ := by linarith
  have hinverse_complement : ‖(1 - z)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have h := (inv_anti₀ (by norm_num : (0 : Real) < 27 / 32)
      hcomplement)
    norm_num at h ⊢
    linarith
  have hcomplement_real : ((1 - z)⁻¹).re ≤ 2 := by
    calc
      ((1 - z)⁻¹).re ≤ |((1 - z)⁻¹).re| := le_abs_self _
      _ ≤ ‖(1 - z)⁻¹‖ := Complex.abs_re_le_norm _
      _ ≤ 2 := hinverse_complement
  have hlarge : Real.exp (-2) ≤ ‖Complex.exp (-(1 - z)⁻¹)‖ := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using neg_le_neg hcomplement_real
  have hsmall : ‖Complex.exp (-z⁻¹)‖ ≤ Real.exp (-(2 / (3 * t))) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using neg_le_neg hinverse
  have hscale : (16 / 3 : Real) ≤ 2 / (3 * t) := by
    apply (le_div_iff₀ (by positivity : (0 : Real) < 3 * t)).2
    nlinarith
  have hexp_scale :
      Real.exp (-(2 / (3 * t))) ≤ Real.exp (-(16 / 3 : Real)) :=
    Real.exp_le_exp.mpr (neg_le_neg hscale)
  have hexp_growth : (2 : Real) < Real.exp (10 / 3 : Real) := by
    nlinarith [Real.add_one_le_exp (10 / 3 : Real)]
  have hexp_identity :
      Real.exp (-2) =
        Real.exp (-(16 / 3 : Real)) * Real.exp (10 / 3 : Real) := by
    rw [← Real.exp_add]
    congr 1
    norm_num
  have hexp_strict :
      Real.exp (-(16 / 3 : Real)) < Real.exp (-2) / 2 := by
    rw [hexp_identity]
    nlinarith [mul_lt_mul_of_pos_left hexp_growth
      (Real.exp_pos (-(16 / 3 : Real)))]
  have hsmall_strict :
      ‖Complex.exp (-z⁻¹)‖ < Real.exp (-2) / 2 :=
    lt_of_le_of_lt (hsmall.trans hexp_scale) hexp_strict
  have htriangle :
      ‖Complex.exp (-(1 - z)⁻¹)‖ ≤
        ‖Complex.exp (-z⁻¹) + Complex.exp (-(1 - z)⁻¹)‖ +
          ‖Complex.exp (-z⁻¹)‖ := by
    calc
      ‖Complex.exp (-(1 - z)⁻¹)‖ =
          ‖(Complex.exp (-z⁻¹) + Complex.exp (-(1 - z)⁻¹)) -
            Complex.exp (-z⁻¹)‖ := by
        congr 1
        ring
      _ ≤ ‖Complex.exp (-z⁻¹) + Complex.exp (-(1 - z)⁻¹)‖ +
            ‖Complex.exp (-z⁻¹)‖ := norm_sub_le _ _
  linarith

theorem osiiProduction_endpoint_transition_quotient_bound
    {t : Real} (ht : 0 < t) (htsmall : t ≤ 1 / 8)
    {z : Complex} (hz : ‖z - (t : Complex)‖ ≤ t / 4) :
    ‖Complex.exp (-z⁻¹) /
        (Complex.exp (-z⁻¹) + Complex.exp (-(1 - z)⁻¹))‖ ≤
      2 * Real.exp 2 * Real.exp (-(2 / (3 * t))) := by
  have hdenominator :=
    osiiProduction_endpoint_transition_denominator_bound ht htsmall hz
  have hinverse := osiiProduction_endpoint_complex_inverse_real_bound ht hz
  have hnumerator :
      ‖Complex.exp (-z⁻¹)‖ ≤ Real.exp (-(2 / (3 * t))) := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (by simpa using neg_le_neg hinverse)
  rw [norm_div]
  calc
    ‖Complex.exp (-z⁻¹)‖ /
          ‖Complex.exp (-z⁻¹) + Complex.exp (-(1 - z)⁻¹)‖ ≤
        ‖Complex.exp (-z⁻¹)‖ / (Real.exp (-2) / 2) :=
      div_le_div_of_nonneg_left (norm_nonneg _)
        (by positivity) hdenominator.le
    _ ≤ Real.exp (-(2 / (3 * t))) / (Real.exp (-2) / 2) :=
      div_le_div_of_nonneg_right hnumerator (by positivity)
    _ = 2 * Real.exp 2 * Real.exp (-(2 / (3 * t))) := by
      rw [Real.exp_neg]
      field_simp
      rw [← Real.exp_add]
      norm_num

theorem osiiProduction_middle_complex_norm_bounds
    {t : Real} (htlower : 1 / 8 ≤ t) (htupper : t ≤ 7 / 8)
    {z : Complex} (hz : ‖z - (t : Complex)‖ ≤ 1 / 1024) :
    (1 / 16 : Real) ≤ ‖z‖ ∧ (1 / 16 : Real) ≤ ‖1 - z‖ := by
  have hreabs : |z.re - t| ≤ (1 / 1024 : Real) := by
    calc
      |z.re - t| = |(z - (t : Complex)).re| := by simp
      _ ≤ ‖z - (t : Complex)‖ := Complex.abs_re_le_norm _
      _ ≤ 1 / 1024 := hz
  have hrelower : -(1 / 1024 : Real) ≤ z.re - t :=
    (abs_le.mp hreabs).1
  have hreupper : z.re - t ≤ (1 / 1024 : Real) :=
    (abs_le.mp hreabs).2
  constructor
  · calc
      (1 / 16 : Real) ≤ z.re := by linarith
      _ ≤ |z.re| := le_abs_self _
      _ ≤ ‖z‖ := Complex.abs_re_le_norm _
  · calc
      (1 / 16 : Real) ≤ (1 - z).re := by simp; linarith
      _ ≤ |(1 - z).re| := le_abs_self _
      _ ≤ ‖1 - z‖ := Complex.abs_re_le_norm _

theorem osiiProduction_middle_transition_phase_imaginary_bound
    {t : Real} (htlower : 1 / 8 ≤ t) (htupper : t ≤ 7 / 8)
    {z : Complex} (hz : ‖z - (t : Complex)‖ ≤ 1 / 1024) :
    |(-z⁻¹ + (1 - z)⁻¹).im| ≤ (1 / 2 : Real) := by
  obtain ⟨hz_norm, hcomplement_norm⟩ :=
    osiiProduction_middle_complex_norm_bounds htlower htupper hz
  have himaginary : |z.im| ≤ (1 / 1024 : Real) := by
    calc
      |z.im| = |(z - (t : Complex)).im| := by simp
      _ ≤ ‖z - (t : Complex)‖ := Complex.abs_im_le_norm _
      _ ≤ 1 / 1024 := hz
  have hzsq : (1 / 256 : Real) ≤ Complex.normSq z := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  have hcomplementsq :
      (1 / 256 : Real) ≤ Complex.normSq (1 - z) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (1 - z)]
  have hzsq_pos : 0 < Complex.normSq z := by linarith
  have hcomplementsq_pos : 0 < Complex.normSq (1 - z) := by linarith
  have hzinverse : (Complex.normSq z)⁻¹ ≤ (256 : Real) := by
    rw [← one_div]
    apply (div_le_iff₀ hzsq_pos).2
    nlinarith
  have hcomplementinverse :
      (Complex.normSq (1 - z))⁻¹ ≤ (256 : Real) := by
    rw [← one_div]
    apply (div_le_iff₀ hcomplementsq_pos).2
    nlinarith
  have hphase :
      (-z⁻¹ + (1 - z)⁻¹).im =
        z.im *
          ((Complex.normSq z)⁻¹ + (Complex.normSq (1 - z))⁻¹) := by
    simp [Complex.inv_im, div_eq_mul_inv]
    ring
  have hsum_nonneg :
      0 ≤ (Complex.normSq z)⁻¹ + (Complex.normSq (1 - z))⁻¹ := by
    exact add_nonneg (inv_nonneg.mpr hzsq_pos.le)
      (inv_nonneg.mpr hcomplementsq_pos.le)
  rw [hphase, abs_mul, abs_of_nonneg hsum_nonneg]
  calc
    |z.im| *
          ((Complex.normSq z)⁻¹ + (Complex.normSq (1 - z))⁻¹) ≤
        (1 / 1024 : Real) * 512 := by
      gcongr
      linarith
    _ = 1 / 2 := by norm_num

theorem osiiProduction_middle_transition_phase_real_positive
    {t : Real} (htlower : 1 / 8 ≤ t) (htupper : t ≤ 7 / 8)
    {z : Complex} (hz : ‖z - (t : Complex)‖ ≤ 1 / 1024) :
    0 < (Complex.exp (-z⁻¹ + (1 - z)⁻¹)).re := by
  have hphase :=
    osiiProduction_middle_transition_phase_imaginary_bound htlower htupper hz
  have hlower := (abs_le.mp hphase).1
  have hupper := (abs_le.mp hphase).2
  have hcos :
      0 < Real.cos (-z⁻¹ + (1 - z)⁻¹).im := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.one_le_pi_div_two]
  rw [Complex.exp_re]
  exact mul_pos (Real.exp_pos _) hcos

theorem osiiProduction_middle_transition_denominator_ne_zero
    {t : Real} (htlower : 1 / 8 ≤ t) (htupper : t ≤ 7 / 8)
    {z : Complex} (hz : ‖z - (t : Complex)‖ ≤ 1 / 1024) :
    Complex.exp (-z⁻¹) + Complex.exp (-(1 - z)⁻¹) ≠ 0 := by
  let phase : Complex := -z⁻¹ + (1 - z)⁻¹
  have hphase : 0 < (Complex.exp phase).re :=
    osiiProduction_middle_transition_phase_real_positive htlower htupper hz
  have hfactor :
      Complex.exp (-z⁻¹) + Complex.exp (-(1 - z)⁻¹) =
        Complex.exp (-(1 - z)⁻¹) * (1 + Complex.exp phase) := by
    rw [mul_add, mul_one, ← Complex.exp_add]
    have hcancel : -(1 - z)⁻¹ + phase = -z⁻¹ := by
      dsimp [phase]
      ring
    rw [hcancel]
    ring
  have hone : 1 + Complex.exp phase ≠ 0 := by
    intro heq
    have hreal := congrArg Complex.re heq
    simp at hreal
    linarith
  rw [hfactor]
  exact mul_ne_zero (Complex.exp_ne_zero _) hone

theorem osiiProduction_middle_transition_quotient_bounds
    {t : Real} (htlower : 1 / 8 ≤ t) (htupper : t ≤ 7 / 8)
    {z : Complex} (hz : ‖z - (t : Complex)‖ ≤ 1 / 1024) :
    ‖Complex.exp (-z⁻¹) /
        (Complex.exp (-z⁻¹) + Complex.exp (-(1 - z)⁻¹))‖ ≤ 1 ∧
      ‖Complex.exp (-(1 - z)⁻¹) /
        (Complex.exp (-z⁻¹) + Complex.exp (-(1 - z)⁻¹))‖ ≤ 1 := by
  let phase : Complex := -z⁻¹ + (1 - z)⁻¹
  let w : Complex := Complex.exp phase
  let b : Complex := Complex.exp (-(1 - z)⁻¹)
  have hw_real : 0 < w.re :=
    osiiProduction_middle_transition_phase_real_positive htlower htupper hz
  have hb : b ≠ 0 := Complex.exp_ne_zero _
  have hone : 1 + w ≠ 0 := by
    intro heq
    have hreal := congrArg Complex.re heq
    simp at hreal
    linarith
  have hnum : Complex.exp (-z⁻¹) = b * w := by
    dsimp [b, w, phase]
    rw [← Complex.exp_add]
    congr 1
    ring
  have hden :
      Complex.exp (-z⁻¹) + Complex.exp (-(1 - z)⁻¹) =
        b * (1 + w) := by
    rw [hnum]
    dsimp [b]
    ring
  have hw_norm : ‖w‖ ≤ ‖1 + w‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    rw [Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im,
      Complex.one_im, zero_add]
    nlinarith
  have hone_norm : (1 : Real) ≤ ‖1 + w‖ := by
    calc
      (1 : Real) ≤ (1 + w).re := by simp; linarith
      _ ≤ |(1 + w).re| := le_abs_self _
      _ ≤ ‖1 + w‖ := Complex.abs_re_le_norm _
  have hfirst :
      Complex.exp (-z⁻¹) /
          (Complex.exp (-z⁻¹) + Complex.exp (-(1 - z)⁻¹)) =
        w / (1 + w) := by
    rw [hden, hnum]
    field_simp
  have hsecond :
      Complex.exp (-(1 - z)⁻¹) /
          (Complex.exp (-z⁻¹) + Complex.exp (-(1 - z)⁻¹)) =
        1 / (1 + w) := by
    rw [hden]
    change b / (b * (1 + w)) = 1 / (1 + w)
    field_simp
  constructor
  · rw [hfirst, norm_div]
    exact (div_le_iff₀ (norm_pos_iff.mpr hone)).2 (by simpa using hw_norm)
  · rw [hsecond, norm_div, norm_one]
    exact (div_le_iff₀ (norm_pos_iff.mpr hone)).2 (by simpa using hone_norm)

theorem osiiProductionMultinomial_gevrey_sum
    (r n : Nat) :
    ∑ f ∈ Finset.piAntidiag (Finset.univ : Finset (Fin r)) n,
      Nat.multinomial Finset.univ f *
        ∏ i : Fin r, (f i).factorial ^ 2 ≤
      r ^ n * n.factorial ^ 2 := by
  have hmultinomial :
      (∑ f ∈ Finset.piAntidiag (Finset.univ : Finset (Fin r)) n,
        Nat.multinomial Finset.univ f) = r ^ n := by
    simpa using
      (Finset.sum_pow_eq_sum_piAntidiag
        (R := Nat) (Finset.univ : Finset (Fin r))
          (fun _ : Fin r => 1) n).symm
  calc
    (∑ f ∈ Finset.piAntidiag (Finset.univ : Finset (Fin r)) n,
      Nat.multinomial Finset.univ f *
        ∏ i : Fin r, (f i).factorial ^ 2) ≤
      ∑ f ∈ Finset.piAntidiag (Finset.univ : Finset (Fin r)) n,
        Nat.multinomial Finset.univ f * n.factorial ^ 2 := by
      apply Finset.sum_le_sum
      intro f hf
      have hsum : (∑ i : Fin r, f i) = n :=
        (Finset.mem_piAntidiag.mp hf).1
      have hproduct : (∏ i : Fin r, (f i).factorial) ≤ n.factorial := by
        apply Nat.le_of_dvd (Nat.factorial_pos n)
        simpa [hsum] using
          (Nat.prod_factorial_dvd_factorial_sum
            (Finset.univ : Finset (Fin r)) f)
      apply Nat.mul_le_mul_left
      rw [Finset.prod_pow]
      exact Nat.pow_le_pow_left hproduct 2
    _ = (∑ f ∈ Finset.piAntidiag (Finset.univ : Finset (Fin r)) n,
          Nat.multinomial Finset.univ f) * n.factorial ^ 2 := by
      rw [Finset.sum_mul]
    _ = r ^ n * n.factorial ^ 2 := by rw [hmultinomial]

end OSReconstruction
