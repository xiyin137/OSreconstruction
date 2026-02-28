import OSReconstruction.ComplexLieGroups.BHWCore
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

noncomputable section

open Complex Matrix LorentzLieGroup

namespace BHW

private abbrev ForwardTube (d n : ℕ) : Set (Fin n → Fin (d + 1) → ℂ) :=
  BHWCore.ForwardTube d n

private abbrev complexLorentzAction
    {d n : ℕ} (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ) :
    Fin n → Fin (d + 1) → ℂ :=
  BHWCore.complexLorentzAction (d := d) (n := n) Λ z

private theorem complexLorentzAction_mul {d n : ℕ}
    (Λ₁ Λ₂ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ) :
    complexLorentzAction (Λ₁ * Λ₂) z =
      complexLorentzAction Λ₁ (complexLorentzAction Λ₂ z) := by
  simpa [complexLorentzAction] using
    (BHWCore.complexLorentzAction_mul (d := d) (n := n) Λ₁ Λ₂ z)

private theorem complexLorentzAction_one {d n : ℕ}
    (z : Fin n → Fin (d + 1) → ℂ) :
    complexLorentzAction (1 : ComplexLorentzGroup d) z = z := by
  simpa [complexLorentzAction] using
    (BHWCore.complexLorentzAction_one (d := d) (n := n) z)

private def orbitSet {n : ℕ} (w : Fin n → Fin (1 + 1) → ℂ) :
    Set (ComplexLorentzGroup 1) :=
  {Λ | complexLorentzAction Λ w ∈ ForwardTube 1 n}

private abbrev i0 : Fin (1 + 1) := 0
private abbrev i1 : Fin (1 + 1) := 1

private theorem sinusoidal_positivity {A B b : ℝ} (hA : 0 < A)
    (hend : 0 < A * Real.cos b + B * Real.sin b) (hb : |b| < Real.pi)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < A * Real.cos (b * t) + B * Real.sin (b * t) := by
  set C := Real.sqrt (A ^ 2 + B ^ 2) with hC_def
  have hC_pos : 0 < C := Real.sqrt_pos.mpr (by positivity)
  have hC_sq : C ^ 2 = A ^ 2 + B ^ 2 := Real.sq_sqrt (by positivity)
  have hB_le_C : |B| ≤ C := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith [sq_nonneg A])
  have hBC_le : B / C ≤ 1 := by
    rw [div_le_one hC_pos]
    exact (le_abs_self B).trans hB_le_C
  have hBC_ge : -1 ≤ B / C := by
    rw [le_div_iff₀ hC_pos]
    linarith [neg_abs_le B]
  set φ := Real.arccos (B / C) with hφ_def
  have hcos_φ : Real.cos φ = B / C := Real.cos_arccos hBC_ge hBC_le
  have hsin_φ : Real.sin φ = A / C := by
    have h0 := Real.sin_arccos (B / C)
    rw [show (1 : ℝ) - (B / C) ^ 2 = (A / C) ^ 2 by
          field_simp
          nlinarith [hC_sq]] at h0
    rwa [Real.sqrt_sq (div_nonneg (le_of_lt hA) (le_of_lt hC_pos))] at h0
  have hφ_pos : 0 < φ := by
    rcases eq_or_lt_of_le (Real.arccos_nonneg (B / C)) with h | h
    · exfalso
      have := hsin_φ
      rw [show φ = Real.arccos (B / C) from hφ_def, ← h, Real.sin_zero] at this
      linarith [div_pos hA hC_pos]
    · exact hφ_def ▸ h
  have hφ_lt : φ < Real.pi := by
    rcases eq_or_lt_of_le (Real.arccos_le_pi (B / C)) with h | h
    · exfalso
      have := hsin_φ
      rw [show φ = Real.arccos (B / C) from hφ_def, h, Real.sin_pi] at this
      linarith [div_pos hA hC_pos]
    · exact hφ_def ▸ h
  have hf_eq : ∀ s, A * Real.cos (b * s) + B * Real.sin (b * s) = C * Real.sin (b * s + φ) := by
    intro s
    rw [Real.sin_add, hcos_φ, hsin_φ]
    field_simp
    ring
  rw [hf_eq]
  have h_sin_end : 0 < Real.sin (b + φ) := by
    have h1 : 0 < C * Real.sin (b * 1 + φ) := by
      rw [← hf_eq]
      simp [mul_one, hend]
    have h2 : 0 < Real.sin (b * 1 + φ) := by
      by_contra hx
      push_neg at hx
      linarith [mul_nonpos_of_nonneg_of_nonpos (le_of_lt hC_pos) hx]
    rwa [mul_one] at h2
  have ⟨hbφ_pos, hbφ_lt⟩ : 0 < b + φ ∧ b + φ < Real.pi := by
    constructor
    · by_contra h
      push_neg at h
      linarith [Real.sin_nonpos_of_nonpos_of_neg_pi_le h
        (by linarith [abs_lt.mp hb] : -(Real.pi) ≤ b + φ)]
    · by_contra h
      push_neg at h
      have : Real.sin (b + φ) = -Real.sin (b + φ - Real.pi) := by
        conv_lhs =>
          rw [show b + φ = (b + φ - Real.pi) + Real.pi by ring]
        exact Real.sin_add_pi _
      linarith [Real.sin_nonneg_of_nonneg_of_le_pi (by linarith : 0 ≤ b + φ - Real.pi)
        (by linarith [abs_lt.mp hb] : b + φ - Real.pi ≤ Real.pi)]
  have hbt_pos : 0 < b * t + φ := by
    by_cases hb_nn : 0 ≤ b
    · linarith [mul_nonneg hb_nn ht0]
    · push_neg at hb_nn
      nlinarith
  have hbt_lt : b * t + φ < Real.pi := by
    by_cases hb_nn : 0 ≤ b
    · nlinarith
    · linarith [mul_nonpos_of_nonpos_of_nonneg (le_of_lt (not_le.mp hb_nn)) ht0]
  exact mul_pos hC_pos (Real.sin_pos_of_pos_of_lt_pi hbt_pos hbt_lt)

private theorem inOpenForwardCone_one_iff_pm (η : Fin (1 + 1) → ℝ) :
    InOpenForwardCone 1 η ↔
      (η 0 + η 1 > 0 ∧ η 0 - η 1 > 0) := by
  constructor
  · intro hη
    have hq : -(η 0) ^ 2 + (η 1) ^ 2 < 0 := by
      simpa [minkowskiSignature] using hη.2
    have h_sq : (η 1) ^ 2 < (η 0) ^ 2 := by
      nlinarith [hq]
    have h_abs : |η 1| < η 0 := abs_lt_of_sq_lt_sq h_sq (le_of_lt hη.1)
    exact ⟨by linarith [neg_abs_le (η 1)], by linarith [le_abs_self (η 1)]⟩
  · intro hpm
    refine ⟨by linarith [hpm.1, hpm.2], ?_⟩
    have hq : -(η 0) ^ 2 + (η 1) ^ 2 < 0 := by
      nlinarith [hpm.1, hpm.2]
    simpa [minkowskiSignature] using hq

private theorem d1_metric_eq_00 (Λ : ComplexLorentzGroup 1) :
    (-1 : ℂ) * Λ.val i0 i0 * Λ.val i0 i0 + Λ.val i1 i0 * Λ.val i1 i0 = (-1 : ℂ) := by
  simpa [i0, i1, minkowskiSignature] using Λ.metric_preserving i0 i0

private theorem d1_metric_eq_01 (Λ : ComplexLorentzGroup 1) :
    (-1 : ℂ) * Λ.val i0 i0 * Λ.val i0 i1 + Λ.val i1 i0 * Λ.val i1 i1 = 0 := by
  simpa [i0, i1, minkowskiSignature] using Λ.metric_preserving i0 i1

private theorem d1_metric_eq_10 (Λ : ComplexLorentzGroup 1) :
    (-1 : ℂ) * Λ.val i0 i1 * Λ.val i0 i0 + Λ.val i1 i1 * Λ.val i1 i0 = 0 := by
  simpa [i0, i1, minkowskiSignature] using Λ.metric_preserving i1 i0

private theorem d1_metric_eq_11 (Λ : ComplexLorentzGroup 1) :
    (-1 : ℂ) * Λ.val i0 i1 * Λ.val i0 i1 + Λ.val i1 i1 * Λ.val i1 i1 = (1 : ℂ) := by
  simpa [i0, i1, minkowskiSignature] using Λ.metric_preserving i1 i1

private theorem d1_eta_transpose_eta_eq (Λ : ComplexLorentzGroup 1) :
    ComplexLorentzGroup.ηℂ * Λ.val.transpose * ComplexLorentzGroup.ηℂ =
      !![Λ.val i0 i0, -Λ.val i1 i0; -Λ.val i0 i1, Λ.val i1 i1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ComplexLorentzGroup.ηℂ, minkowskiSignature]

private theorem d1_inv_eq_adjugate_fin_two (Λ : ComplexLorentzGroup 1) :
    Λ.val⁻¹ = !![Λ.val i1 i1, -Λ.val i0 i1; -Λ.val i1 i0, Λ.val i0 i0] := by
  rw [Matrix.inv_def]
  have hdet : Λ.val.det = (1 : ℂ) := Λ.proper
  rw [hdet, Ring.inverse_one, one_smul]
  simpa using (Matrix.adjugate_fin_two Λ.val)

private theorem d1_entries_pairing (Λ : ComplexLorentzGroup 1) :
    Λ.val i0 i0 = Λ.val i1 i1 ∧ Λ.val i0 i1 = Λ.val i1 i0 := by
  have h_left_inv : (ComplexLorentzGroup.ηℂ * Λ.val.transpose * ComplexLorentzGroup.ηℂ) * Λ.val =
      (1 : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ) := by
    have hΛ := ComplexLorentzGroup.metric_preserving_matrix Λ
    calc
      ComplexLorentzGroup.ηℂ * Λ.val.transpose * ComplexLorentzGroup.ηℂ * Λ.val
          = ComplexLorentzGroup.ηℂ * (Λ.val.transpose * ComplexLorentzGroup.ηℂ * Λ.val) := by
              simp [Matrix.mul_assoc]
      _ = ComplexLorentzGroup.ηℂ * ComplexLorentzGroup.ηℂ := by rw [hΛ]
      _ = 1 := ComplexLorentzGroup.ηℂ_sq (d := 1)
  have h_right_inv : Λ.val * (ComplexLorentzGroup.ηℂ * Λ.val.transpose * ComplexLorentzGroup.ηℂ) =
      (1 : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ) := by
    exact mul_eq_one_comm.mp h_left_inv
  have h_inv_eta : Λ.val⁻¹ = ComplexLorentzGroup.ηℂ * Λ.val.transpose * ComplexLorentzGroup.ηℂ :=
    Matrix.inv_eq_right_inv h_right_inv
  rw [d1_eta_transpose_eta_eq, d1_inv_eq_adjugate_fin_two] at h_inv_eta
  have h00 : Λ.val i0 i0 = Λ.val i1 i1 := by
    simpa [i0, i1] using (congr_fun (congr_fun h_inv_eta 0) 0).symm
  have h01 : Λ.val i0 i1 = Λ.val i1 i0 := by
    simpa [i0, i1] using congr_fun (congr_fun h_inv_eta 0) 1
  exact ⟨h00, h01⟩

private theorem d1_hyperbola_relation (Λ : ComplexLorentzGroup 1) :
    Λ.val i0 i0 * Λ.val i0 i0 - Λ.val i0 i1 * Λ.val i0 i1 = (1 : ℂ) := by
  rcases d1_entries_pairing Λ with ⟨_hdiag, hoff⟩
  let a : ℂ := Λ.val i0 i0
  let b : ℂ := Λ.val i0 i1
  have h00 := d1_metric_eq_00 Λ
  rw [← hoff] at h00
  have h00' : (-1 : ℂ) * a * a + b * b = (-1 : ℂ) := by simpa [a, b] using h00
  calc
    a * a - b * b = -(((-1 : ℂ) * a * a + b * b)) := by ring
    _ = -(-1 : ℂ) := by rw [h00']
    _ = (1 : ℂ) := by norm_num

private theorem d1_matrix_normal_form (Λ : ComplexLorentzGroup 1) :
    ∃ a b : ℂ, Λ.val = !![a, b; b, a] ∧ a * a - b * b = (1 : ℂ) := by
  refine ⟨Λ.val i0 i0, Λ.val i0 i1, ?_, d1_hyperbola_relation Λ⟩
  rcases d1_entries_pairing Λ with ⟨hdiag, hoff⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [i0, i1, hdiag, hoff]

private theorem d1_exists_rapidity (Λ : ComplexLorentzGroup 1) :
    ∃ θ : ℂ, Λ.val =
      !![Complex.cosh θ, Complex.sinh θ; Complex.sinh θ, Complex.cosh θ] := by
  rcases d1_matrix_normal_form Λ with ⟨a, b, hmat, hrel⟩
  let u : ℂ := a + b
  have hu_ne : u ≠ 0 := by
    intro hu
    have hab : a = -b := by
      exact eq_neg_iff_add_eq_zero.mpr (by simpa [u] using hu)
    rw [hab] at hrel
    norm_num at hrel
  refine ⟨Complex.log u, ?_⟩
  have h_exp : Complex.exp (Complex.log u) = u := Complex.exp_log hu_ne
  have hu_mul : u * (a - b) = (1 : ℂ) := by
    calc
      u * (a - b) = (a + b) * (a - b) := by simp [u]
      _ = a * a - b * b := by ring
      _ = 1 := hrel
  have hu_inv : u⁻¹ = a - b := by
    calc
      u⁻¹ = u⁻¹ * 1 := by simp
      _ = u⁻¹ * (u * (a - b)) := by rw [hu_mul]
      _ = (u⁻¹ * u) * (a - b) := by ring
      _ = a - b := by simp [inv_mul_cancel₀ hu_ne]
  have h_exp_neg : Complex.exp (-Complex.log u) = a - b := by
    calc
      Complex.exp (-Complex.log u) = (Complex.exp (Complex.log u))⁻¹ := Complex.exp_neg (Complex.log u)
      _ = u⁻¹ := by rw [h_exp]
      _ = a - b := hu_inv
  have h_cosh : Complex.cosh (Complex.log u) = a := by
    have hsum : Complex.cosh (Complex.log u) + Complex.sinh (Complex.log u) = a + b := by
      simpa [u] using (Complex.cosh_add_sinh (Complex.log u)).trans h_exp
    have hdiff : Complex.cosh (Complex.log u) - Complex.sinh (Complex.log u) = a - b := by
      simpa using (Complex.cosh_sub_sinh (Complex.log u)).trans h_exp_neg
    apply (mul_right_cancel₀ (two_ne_zero' ℂ))
    calc
      Complex.cosh (Complex.log u) * 2
          = (Complex.cosh (Complex.log u) + Complex.sinh (Complex.log u)) +
              (Complex.cosh (Complex.log u) - Complex.sinh (Complex.log u)) := by ring
      _ = (a + b) + (a - b) := by rw [hsum, hdiff]
      _ = a * 2 := by ring
  have h_sinh : Complex.sinh (Complex.log u) = b := by
    have hsum : Complex.cosh (Complex.log u) + Complex.sinh (Complex.log u) = a + b := by
      simpa [u] using (Complex.cosh_add_sinh (Complex.log u)).trans h_exp
    have hdiff : Complex.cosh (Complex.log u) - Complex.sinh (Complex.log u) = a - b := by
      simpa using (Complex.cosh_sub_sinh (Complex.log u)).trans h_exp_neg
    apply (mul_right_cancel₀ (two_ne_zero' ℂ))
    calc
      Complex.sinh (Complex.log u) * 2
          = (Complex.cosh (Complex.log u) + Complex.sinh (Complex.log u)) -
              (Complex.cosh (Complex.log u) - Complex.sinh (Complex.log u)) := by ring
      _ = (a + b) - (a - b) := by rw [hsum, hdiff]
      _ = b * 2 := by ring
  rw [hmat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h_cosh, h_sinh]

private def rapidityMatrix (θ : ℂ) : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ :=
  !![Complex.cosh θ, Complex.sinh θ; Complex.sinh θ, Complex.cosh θ]

private theorem imag_rapidity_plus_formula (b t : ℝ) (ξ : Fin (1 + 1) → ℂ) :
    (∑ ν, rapidityMatrix (((b * t : ℝ) : ℂ) * Complex.I) 0 ν * ξ ν).im +
      (∑ ν, rapidityMatrix (((b * t : ℝ) : ℂ) * Complex.I) 1 ν * ξ ν).im =
      ((ξ 0).im + (ξ 1).im) * Real.cos (b * t) +
      ((ξ 0).re + (ξ 1).re) * Real.sin (b * t) := by
  have hcos_re : (Complex.cos ((b : ℂ) * (t : ℂ))).re = Real.cos (b * t) := by
    simpa [mul_assoc] using (Complex.cos_ofReal_re (b * t))
  have hcos_im : (Complex.cos ((b : ℂ) * (t : ℂ))).im = 0 := by
    simpa [mul_assoc] using (Complex.cos_ofReal_im (b * t))
  have hsin_re : (Complex.sin ((b : ℂ) * (t : ℂ))).re = Real.sin (b * t) := by
    simpa [mul_assoc] using (Complex.sin_ofReal_re (b * t))
  have hsin_im : (Complex.sin ((b : ℂ) * (t : ℂ))).im = 0 := by
    simpa [mul_assoc] using (Complex.sin_ofReal_im (b * t))
  simp [rapidityMatrix, Complex.cosh_mul_I, Complex.sinh_mul_I, Complex.mul_im,
    hcos_re, hcos_im, hsin_re, hsin_im]
  ring

private theorem imag_rapidity_minus_formula (b t : ℝ) (ξ : Fin (1 + 1) → ℂ) :
    (∑ ν, rapidityMatrix (((b * t : ℝ) : ℂ) * Complex.I) 0 ν * ξ ν).im -
      (∑ ν, rapidityMatrix (((b * t : ℝ) : ℂ) * Complex.I) 1 ν * ξ ν).im =
      ((ξ 0).im - (ξ 1).im) * Real.cos (b * t) +
      ((ξ 1).re - (ξ 0).re) * Real.sin (b * t) := by
  have hcos_re : (Complex.cos ((b : ℂ) * (t : ℂ))).re = Real.cos (b * t) := by
    simpa [mul_assoc] using (Complex.cos_ofReal_re (b * t))
  have hcos_im : (Complex.cos ((b : ℂ) * (t : ℂ))).im = 0 := by
    simpa [mul_assoc] using (Complex.cos_ofReal_im (b * t))
  have hsin_re : (Complex.sin ((b : ℂ) * (t : ℂ))).re = Real.sin (b * t) := by
    simpa [mul_assoc] using (Complex.sin_ofReal_re (b * t))
  have hsin_im : (Complex.sin ((b : ℂ) * (t : ℂ))).im = 0 := by
    simpa [mul_assoc] using (Complex.sin_ofReal_im (b * t))
  simp [rapidityMatrix, Complex.cosh_mul_I, Complex.sinh_mul_I, Complex.mul_im,
    hcos_re, hcos_im, hsin_re, hsin_im]
  ring

private theorem pureImag_rapidity_preserves_cone_segment
    (b : ℝ) (ξ : Fin (1 + 1) → ℂ)
    (h0 : InOpenForwardCone 1 (fun μ => (ξ μ).im))
    (h1 : InOpenForwardCone 1
      (fun μ => (∑ ν, rapidityMatrix ((b : ℂ) * Complex.I) μ ν * ξ ν).im))
    (hb : |b| < Real.pi)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    InOpenForwardCone 1
      (fun μ => (∑ ν, rapidityMatrix (((b * t : ℝ) : ℂ) * Complex.I) μ ν * ξ ν).im) := by
  have h0pm : (ξ 0).im + (ξ 1).im > 0 ∧ (ξ 0).im - (ξ 1).im > 0 := by
    simpa using (inOpenForwardCone_one_iff_pm (fun μ => (ξ μ).im)).1 h0
  have h1pm :
      (∑ ν, rapidityMatrix ((b : ℂ) * Complex.I) 0 ν * ξ ν).im +
          (∑ ν, rapidityMatrix ((b : ℂ) * Complex.I) 1 ν * ξ ν).im > 0 ∧
      (∑ ν, rapidityMatrix ((b : ℂ) * Complex.I) 0 ν * ξ ν).im -
          (∑ ν, rapidityMatrix ((b : ℂ) * Complex.I) 1 ν * ξ ν).im > 0 := by
    simpa using (inOpenForwardCone_one_iff_pm
      (fun μ => (∑ ν, rapidityMatrix ((b : ℂ) * Complex.I) μ ν * ξ ν).im)).1 h1
  have hend_plus :
      0 < ((ξ 0).im + (ξ 1).im) * Real.cos b + ((ξ 0).re + (ξ 1).re) * Real.sin b := by
    calc
      0 < (∑ ν, rapidityMatrix ((b : ℂ) * Complex.I) 0 ν * ξ ν).im +
            (∑ ν, rapidityMatrix ((b : ℂ) * Complex.I) 1 ν * ξ ν).im := h1pm.1
      _ = ((ξ 0).im + (ξ 1).im) * Real.cos b + ((ξ 0).re + (ξ 1).re) * Real.sin b := by
            simpa [mul_one] using imag_rapidity_plus_formula b 1 ξ
  have hend_minus :
      0 < ((ξ 0).im - (ξ 1).im) * Real.cos b + ((ξ 1).re - (ξ 0).re) * Real.sin b := by
    calc
      0 < (∑ ν, rapidityMatrix ((b : ℂ) * Complex.I) 0 ν * ξ ν).im -
            (∑ ν, rapidityMatrix ((b : ℂ) * Complex.I) 1 ν * ξ ν).im := h1pm.2
      _ = ((ξ 0).im - (ξ 1).im) * Real.cos b + ((ξ 1).re - (ξ 0).re) * Real.sin b := by
            simpa [mul_one] using imag_rapidity_minus_formula b 1 ξ
  have hplus_t_rhs :
      0 < ((ξ 0).im + (ξ 1).im) * Real.cos (b * t) + ((ξ 0).re + (ξ 1).re) * Real.sin (b * t) :=
    sinusoidal_positivity h0pm.1 hend_plus hb ht0 ht1
  have hminus_t_rhs :
      0 < ((ξ 0).im - (ξ 1).im) * Real.cos (b * t) + ((ξ 1).re - (ξ 0).re) * Real.sin (b * t) :=
    sinusoidal_positivity h0pm.2 hend_minus hb ht0 ht1
  have hplus_t :
      0 < (∑ ν, rapidityMatrix (((b * t : ℝ) : ℂ) * Complex.I) 0 ν * ξ ν).im +
            (∑ ν, rapidityMatrix (((b * t : ℝ) : ℂ) * Complex.I) 1 ν * ξ ν).im := by
    calc
      0 < ((ξ 0).im + (ξ 1).im) * Real.cos (b * t) + ((ξ 0).re + (ξ 1).re) * Real.sin (b * t) :=
        hplus_t_rhs
      _ = (∑ ν, rapidityMatrix (((b * t : ℝ) : ℂ) * Complex.I) 0 ν * ξ ν).im +
            (∑ ν, rapidityMatrix (((b * t : ℝ) : ℂ) * Complex.I) 1 ν * ξ ν).im := by
              simpa using (imag_rapidity_plus_formula b t ξ).symm
  have hminus_t :
      0 < (∑ ν, rapidityMatrix (((b * t : ℝ) : ℂ) * Complex.I) 0 ν * ξ ν).im -
            (∑ ν, rapidityMatrix (((b * t : ℝ) : ℂ) * Complex.I) 1 ν * ξ ν).im := by
    calc
      0 < ((ξ 0).im - (ξ 1).im) * Real.cos (b * t) + ((ξ 1).re - (ξ 0).re) * Real.sin (b * t) :=
        hminus_t_rhs
      _ = (∑ ν, rapidityMatrix (((b * t : ℝ) : ℂ) * Complex.I) 0 ν * ξ ν).im -
            (∑ ν, rapidityMatrix (((b * t : ℝ) : ℂ) * Complex.I) 1 ν * ξ ν).im := by
              simpa using (imag_rapidity_minus_formula b t ξ).symm
  exact (inOpenForwardCone_one_iff_pm
    (fun μ => (∑ ν, rapidityMatrix (((b * t : ℝ) : ℂ) * Complex.I) μ ν * ξ ν).im)).2
      ⟨hplus_t, hminus_t⟩

private theorem rapidityMatrix_metric (θ : ℂ) :
    ∀ (μ ν : Fin (1 + 1)),
      ∑ α : Fin (1 + 1),
        (minkowskiSignature 1 α : ℂ) * rapidityMatrix θ α μ * rapidityMatrix θ α ν =
      if μ = ν then (minkowskiSignature 1 μ : ℂ) else 0 := by
  intro μ ν
  fin_cases μ <;> fin_cases ν
  · simp [rapidityMatrix, minkowskiSignature]
    have hcs : Complex.cosh θ * Complex.cosh θ - Complex.sinh θ * Complex.sinh θ = (1 : ℂ) := by
      simpa [pow_two] using (Complex.cosh_sq_sub_sinh_sq (x := θ))
    calc
      -(Complex.cosh θ * Complex.cosh θ) + Complex.sinh θ * Complex.sinh θ
          = -(Complex.cosh θ * Complex.cosh θ - Complex.sinh θ * Complex.sinh θ) := by ring
      _ = (-1 : ℂ) := by rw [hcs]
  · (simp [rapidityMatrix, minkowskiSignature]; ring)
  · (simp [rapidityMatrix, minkowskiSignature]; ring)
  · simp [rapidityMatrix, minkowskiSignature]
    have hcs : Complex.cosh θ * Complex.cosh θ - Complex.sinh θ * Complex.sinh θ = (1 : ℂ) := by
      simpa [pow_two] using (Complex.cosh_sq_sub_sinh_sq (x := θ))
    calc
      -(Complex.sinh θ * Complex.sinh θ) + Complex.cosh θ * Complex.cosh θ
          = Complex.cosh θ * Complex.cosh θ - Complex.sinh θ * Complex.sinh θ := by ring
      _ = (1 : ℂ) := hcs

private theorem rapidityMatrix_det (θ : ℂ) :
    (rapidityMatrix θ).det = (1 : ℂ) := by
  have hcs : Complex.cosh θ * Complex.cosh θ - Complex.sinh θ * Complex.sinh θ = (1 : ℂ) := by
    simpa [pow_two] using (Complex.cosh_sq_sub_sinh_sq (x := θ))
  simpa [rapidityMatrix, Matrix.det_fin_two] using hcs

private def rapidityElement (θ : ℂ) : ComplexLorentzGroup 1 where
  val := rapidityMatrix θ
  metric_preserving := rapidityMatrix_metric θ
  proper := rapidityMatrix_det θ

private theorem rapidityMatrix_mul (x y : ℂ) :
    rapidityMatrix (x + y) = rapidityMatrix x * rapidityMatrix y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rapidityMatrix, Complex.cosh_add, Complex.sinh_add] <;> ring

private theorem rapidityElement_mul (x y : ℂ) :
    rapidityElement (x + y) = rapidityElement x * rapidityElement y := by
  apply ComplexLorentzGroup.ext
  simp [rapidityElement, rapidityMatrix_mul]

private theorem d1_real_im_rapidity_decomp (Λ : ComplexLorentzGroup 1) :
    ∃ a b : ℝ,
      Λ.val = rapidityMatrix ((a : ℂ) + (b : ℂ) * Complex.I) ∧
      rapidityMatrix ((a : ℂ) + (b : ℂ) * Complex.I) =
        rapidityMatrix (a : ℂ) * rapidityMatrix ((b : ℂ) * Complex.I) := by
  rcases d1_exists_rapidity Λ with ⟨θ, hθ⟩
  refine ⟨θ.re, θ.im, ?_, ?_⟩
  · simpa [Complex.re_add_im] using hθ
  · simpa using rapidityMatrix_mul (x := (θ.re : ℂ)) (y := (θ.im : ℂ) * Complex.I)

private theorem d1_exists_rapidityElement (Λ : ComplexLorentzGroup 1) :
    ∃ θ : ℂ, Λ = rapidityElement θ := by
  rcases d1_exists_rapidity Λ with ⟨θ, hθ⟩
  refine ⟨θ, ?_⟩
  apply ComplexLorentzGroup.ext
  simpa [rapidityElement] using hθ

private theorem d1_rapidityElement_real_im_decomp (Λ : ComplexLorentzGroup 1) :
    ∃ a b : ℝ, Λ = rapidityElement (a : ℂ) * rapidityElement ((b : ℂ) * Complex.I) := by
  rcases d1_exists_rapidityElement Λ with ⟨θ, rfl⟩
  refine ⟨θ.re, θ.im, ?_⟩
  have hθ : θ = (θ.re : ℂ) + (θ.im : ℂ) * Complex.I := (Complex.re_add_im θ).symm
  rw [hθ]
  simpa using
    (rapidityElement_mul (x := (θ.re : ℂ)) (y := (θ.im : ℂ) * Complex.I))

private theorem rapidityMatrix_add_two_pi_I_int (θ : ℂ) (m : ℤ) :
    rapidityMatrix (θ + (m : ℂ) * (2 * Real.pi) * Complex.I) = rapidityMatrix θ := by
  have hcosh_period :
      Complex.cosh ((m : ℂ) * (2 * Real.pi) * Complex.I) = (1 : ℂ) := by
    calc
      Complex.cosh ((m : ℂ) * (2 * Real.pi) * Complex.I)
          = Complex.cos ((m : ℂ) * (2 * Real.pi)) := by
              simpa [mul_assoc] using
                (Complex.cosh_mul_I ((m : ℂ) * (2 * Real.pi)))
      _ = (1 : ℂ) := Complex.cos_int_mul_two_pi m
  have hsinh_period :
      Complex.sinh ((m : ℂ) * (2 * Real.pi) * Complex.I) = 0 := by
    calc
      Complex.sinh ((m : ℂ) * (2 * Real.pi) * Complex.I)
          = Complex.sin ((m : ℂ) * (2 * Real.pi)) * Complex.I := by
              simpa [mul_assoc] using
                (Complex.sinh_mul_I ((m : ℂ) * (2 * Real.pi)))
      _ = 0 := by
        have hsin :
            Complex.sin ((m : ℂ) * (2 * Real.pi)) = 0 := by
          simpa using (Complex.sin_add_int_mul_two_pi (x := (0 : ℂ)) (n := m))
        simp [hsin]
  ext i j
  fin_cases i <;> fin_cases j
  · calc
      Complex.cosh (θ + (m : ℂ) * (2 * Real.pi) * Complex.I)
          = Complex.cosh θ * Complex.cosh ((m : ℂ) * (2 * Real.pi) * Complex.I) +
              Complex.sinh θ * Complex.sinh ((m : ℂ) * (2 * Real.pi) * Complex.I) := by
                rw [Complex.cosh_add]
      _ = Complex.cosh θ := by simp [hcosh_period, hsinh_period]
  · calc
      Complex.sinh (θ + (m : ℂ) * (2 * Real.pi) * Complex.I)
          = Complex.sinh θ * Complex.cosh ((m : ℂ) * (2 * Real.pi) * Complex.I) +
              Complex.cosh θ * Complex.sinh ((m : ℂ) * (2 * Real.pi) * Complex.I) := by
                rw [Complex.sinh_add]
      _ = Complex.sinh θ := by simp [hcosh_period, hsinh_period]
  · calc
      Complex.sinh (θ + (m : ℂ) * (2 * Real.pi) * Complex.I)
          = Complex.sinh θ * Complex.cosh ((m : ℂ) * (2 * Real.pi) * Complex.I) +
              Complex.cosh θ * Complex.sinh ((m : ℂ) * (2 * Real.pi) * Complex.I) := by
                rw [Complex.sinh_add]
      _ = Complex.sinh θ := by simp [hcosh_period, hsinh_period]
  · calc
      Complex.cosh (θ + (m : ℂ) * (2 * Real.pi) * Complex.I)
          = Complex.cosh θ * Complex.cosh ((m : ℂ) * (2 * Real.pi) * Complex.I) +
              Complex.sinh θ * Complex.sinh ((m : ℂ) * (2 * Real.pi) * Complex.I) := by
                rw [Complex.cosh_add]
      _ = Complex.cosh θ := by simp [hcosh_period, hsinh_period]

private theorem rapidityElement_add_two_pi_I_int (θ : ℂ) (m : ℤ) :
    rapidityElement (θ + (m : ℂ) * (2 * Real.pi) * Complex.I) = rapidityElement θ := by
  apply ComplexLorentzGroup.ext
  exact rapidityMatrix_add_two_pi_I_int θ m

private theorem d1_exists_rapidityElement_principal_im (Λ : ComplexLorentzGroup 1) :
    ∃ a b : ℝ, b ∈ Set.Ioc (-Real.pi) Real.pi ∧
      Λ = rapidityElement ((a : ℂ) + (b : ℂ) * Complex.I) := by
  rcases d1_exists_rapidityElement Λ with ⟨θ, hθΛ⟩
  let a : ℝ := θ.re
  let b : ℝ := toIocMod Real.two_pi_pos (-Real.pi) θ.im
  let k : ℤ := toIocDiv Real.two_pi_pos (-Real.pi) θ.im
  have hb_mem_raw : b ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    simpa [b] using toIocMod_mem_Ioc Real.two_pi_pos (-Real.pi) θ.im
  have hb_mem : b ∈ Set.Ioc (-Real.pi) Real.pi := by
    rcases hb_mem_raw with ⟨hb_lo, hb_hi_raw⟩
    have hb_hi : b ≤ Real.pi := by linarith
    exact ⟨hb_lo, hb_hi⟩
  have hb_eq :
      b + (k : ℝ) * (2 * Real.pi) = θ.im := by
    exact (toIocMod_add_toIocDiv_mul Real.two_pi_pos (-Real.pi) θ.im)
  have hb_eqC : (b : ℂ) + (k : ℂ) * (2 * Real.pi) = (θ.im : ℂ) := by
    exact_mod_cast hb_eq
  have hθ_repr :
      θ = ((a : ℂ) + (b : ℂ) * Complex.I) + (k : ℂ) * (2 * Real.pi) * Complex.I := by
    calc
      θ = (a : ℂ) + (θ.im : ℂ) * Complex.I := by
            unfold a
            exact (Complex.re_add_im θ).symm
      _ = (a : ℂ) + ((b : ℂ) + (k : ℂ) * (2 * Real.pi)) * Complex.I := by rw [hb_eqC.symm]
      _ = ((a : ℂ) + (b : ℂ) * Complex.I) + (k : ℂ) * (2 * Real.pi) * Complex.I := by ring
  refine ⟨a, b, hb_mem, ?_⟩
  rw [hθΛ, hθ_repr]
  simpa using (rapidityElement_add_two_pi_I_int ((a : ℂ) + (b : ℂ) * Complex.I) k)

private theorem rapidityMatrix_pi_I :
    rapidityMatrix ((Real.pi : ℂ) * Complex.I) = !![(-1 : ℂ), 0; 0, (-1 : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rapidityMatrix, Complex.cosh_mul_I, Complex.sinh_mul_I, Complex.cos_pi, Complex.sin_pi]

private theorem complexLorentzAction_rapidity_pi_I
    (z : Fin n → Fin (1 + 1) → ℂ) :
    complexLorentzAction (rapidityElement ((Real.pi : ℂ) * Complex.I)) z =
      fun k μ => -(z k μ) := by
  ext k μ
  fin_cases μ <;>
    simp [complexLorentzAction, BHWCore.complexLorentzAction, rapidityElement, rapidityMatrix_pi_I]

private theorem neg_not_mem_forwardTube_d1 [NeZero n]
    (z : Fin n → Fin (1 + 1) → ℂ) (hz : z ∈ ForwardTube 1 n) :
    (fun k μ => -(z k μ)) ∉ ForwardTube 1 n := by
  intro hneg
  let k0 : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  have hz0 : InOpenForwardCone 1 (fun μ => (z k0 μ).im) := by
    simpa [ForwardTube, k0]
      using (hz k0)
  have hneg0 : InOpenForwardCone 1 (fun μ => (-(z k0 μ)).im) := by
    simpa [ForwardTube, k0]
      using (hneg k0)
  have hneg0' : InOpenForwardCone 1 (fun μ => -(z k0 μ).im) := by
    simpa [Complex.neg_im] using hneg0
  linarith [hz0.1, hneg0'.1]

private def diffVec (z : Fin n → Fin (1 + 1) → ℂ) (k : Fin n) : Fin (1 + 1) → ℂ :=
  fun ν => z k ν - (if h : k.val = 0 then 0 else z ⟨k.val - 1, by omega⟩) ν

private lemma diffVec_action (Λ : ComplexLorentzGroup 1)
    (z : Fin n → Fin (1 + 1) → ℂ) (k : Fin n) :
    diffVec (complexLorentzAction Λ z) k =
      fun μ => ∑ ν, Λ.val μ ν * diffVec z k ν := by
  ext μ
  simp only [diffVec, complexLorentzAction, BHWCore.complexLorentzAction]
  by_cases hk : k.val = 0
  · simp [hk, sub_zero]
  · simp only [hk, ↓reduceDIte, BHWCore.complexLorentzAction]
    rw [← Finset.sum_sub_distrib]
    congr 1
    ext ν
    ring

private theorem pureImag_rapidity_preserves_forwardTube_segment
    (b : ℝ) (w : Fin n → Fin (1 + 1) → ℂ)
    (hw : w ∈ ForwardTube 1 n)
    (h1 : complexLorentzAction (rapidityElement ((b : ℂ) * Complex.I)) w ∈ ForwardTube 1 n)
    (hb : |b| < Real.pi)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    complexLorentzAction (rapidityElement (((b * t : ℝ) : ℂ) * Complex.I)) w ∈ ForwardTube 1 n := by
  intro k
  let ξ : Fin (1 + 1) → ℂ := diffVec w k
  have h0_cone : InOpenForwardCone 1 (fun μ => (ξ μ).im) := by
    simpa [ForwardTube, diffVec, ξ] using hw k
  have h1_cone : InOpenForwardCone 1
      (fun μ => (∑ ν, rapidityMatrix ((b : ℂ) * Complex.I) μ ν * ξ ν).im) := by
    have hk1 : InOpenForwardCone 1
        (fun μ =>
          (diffVec (complexLorentzAction (rapidityElement ((b : ℂ) * Complex.I)) w) k μ).im) := by
      simpa [ForwardTube, diffVec] using h1 k
    rw [diffVec_action] at hk1
    simpa [rapidityElement, ξ] using hk1
  have hseg :
      InOpenForwardCone 1
        (fun μ => (∑ ν, rapidityMatrix (((b * t : ℝ) : ℂ) * Complex.I) μ ν * ξ ν).im) :=
    pureImag_rapidity_preserves_cone_segment b ξ h0_cone h1_cone hb ht0 ht1
  show InOpenForwardCone 1
    (fun μ =>
      (diffVec (complexLorentzAction (rapidityElement (((b * t : ℝ) : ℂ) * Complex.I)) w) k μ).im)
  rw [diffVec_action]
  simpa [rapidityElement, ξ] using hseg

private theorem ofReal_preserves_forwardTube_d1 (R : RestrictedLorentzGroup 1)
    (z : Fin n → Fin (1 + 1) → ℂ) (hz : z ∈ ForwardTube 1 n) :
    complexLorentzAction (ComplexLorentzGroup.ofReal R) z ∈ ForwardTube 1 n := by
  intro k
  show InOpenForwardCone 1
    (fun μ => (diffVec (complexLorentzAction (ComplexLorentzGroup.ofReal R) z) k μ).im)
  rw [diffVec_action]
  have h_im :
      (fun μ =>
        (∑ ν, (ComplexLorentzGroup.ofReal R).val μ ν * diffVec z k ν).im) =
      (fun μ => ∑ ν, R.val.val μ ν * (diffVec z k ν).im) := by
    ext μ
    exact ofReal_im_action R (diffVec z k) μ
  rw [h_im]
  have hk : InOpenForwardCone 1 (fun μ => (diffVec z k μ).im) := by
    simpa [ForwardTube, diffVec] using hz k
  exact real_lorentz_preserves_forwardCone R _ hk

private theorem ofReal_boost_eq_rapidity (a : ℝ) :
    (ComplexLorentzGroup.ofReal (LorentzLieGroup.boostElement 1 (0 : Fin 1) a)).val =
      rapidityMatrix (a : ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j
  · change (↑((LorentzLieGroup.boostElement 1 (0 : Fin 1) a).val.val 0 0) : ℂ) =
      Complex.cosh (a : ℂ)
    simp [LorentzLieGroup.boostElement, LorentzLieGroup.planarBoost, Complex.ofReal_cosh]
  · change (↑((LorentzLieGroup.boostElement 1 (0 : Fin 1) a).val.val 0 1) : ℂ) =
      Complex.sinh (a : ℂ)
    simp [LorentzLieGroup.boostElement, LorentzLieGroup.planarBoost, Complex.ofReal_sinh]
  · change (↑((LorentzLieGroup.boostElement 1 (0 : Fin 1) a).val.val 1 0) : ℂ) =
      Complex.sinh (a : ℂ)
    simp [LorentzLieGroup.boostElement, LorentzLieGroup.planarBoost, Complex.ofReal_sinh]
  · change (↑((LorentzLieGroup.boostElement 1 (0 : Fin 1) a).val.val 1 1) : ℂ) =
      Complex.cosh (a : ℂ)
    simp [LorentzLieGroup.boostElement, LorentzLieGroup.planarBoost, Complex.ofReal_cosh]

private theorem rapidityElement_real_preserves_forwardTube (a : ℝ)
    (z : Fin n → Fin (1 + 1) → ℂ) (hz : z ∈ ForwardTube 1 n) :
    complexLorentzAction (rapidityElement (a : ℂ)) z ∈ ForwardTube 1 n := by
  have hgroup : rapidityElement (a : ℂ) =
      ComplexLorentzGroup.ofReal (LorentzLieGroup.boostElement 1 (0 : Fin 1) a) := by
    apply ComplexLorentzGroup.ext
    simpa [rapidityElement] using (ofReal_boost_eq_rapidity a).symm
  rw [hgroup]
  exact ofReal_preserves_forwardTube_d1 (LorentzLieGroup.boostElement 1 (0 : Fin 1) a) z hz

private theorem rapidityElement_zero : rapidityElement (0 : ℂ) = 1 := by
  apply ComplexLorentzGroup.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rapidityElement, rapidityMatrix]

private theorem rapidityElement_re_add_piI_not_orbit [NeZero n]
    (a : ℝ) (w : Fin n → Fin (1 + 1) → ℂ) (hw : w ∈ ForwardTube 1 n) :
    complexLorentzAction
      (rapidityElement ((a : ℂ) + (Real.pi : ℂ) * Complex.I)) w ∉ ForwardTube 1 n := by
  intro hFT
  have hsplit :
      rapidityElement ((a : ℂ) + (Real.pi : ℂ) * Complex.I) =
        rapidityElement (a : ℂ) * rapidityElement ((Real.pi : ℂ) * Complex.I) := by
    simpa using rapidityElement_mul (x := (a : ℂ)) (y := (Real.pi : ℂ) * Complex.I)
  have haction :
      complexLorentzAction
        (rapidityElement ((a : ℂ) + (Real.pi : ℂ) * Complex.I)) w =
      complexLorentzAction (rapidityElement (a : ℂ)) (fun k μ => -(w k μ)) := by
    calc
      complexLorentzAction
          (rapidityElement ((a : ℂ) + (Real.pi : ℂ) * Complex.I)) w
          = complexLorentzAction
              (rapidityElement (a : ℂ) * rapidityElement ((Real.pi : ℂ) * Complex.I)) w := by
                rw [hsplit]
      _ = complexLorentzAction (rapidityElement (a : ℂ))
            (complexLorentzAction (rapidityElement ((Real.pi : ℂ) * Complex.I)) w) := by
              rw [complexLorentzAction_mul]
      _ = complexLorentzAction (rapidityElement (a : ℂ)) (fun k μ => -(w k μ)) := by
            simp [complexLorentzAction_rapidity_pi_I]
  have hFT' : complexLorentzAction (rapidityElement (a : ℂ))
      (fun k μ => -(w k μ)) ∈ ForwardTube 1 n := by
    simpa [haction] using hFT
  have hnegFT : (fun k μ => -(w k μ)) ∈ ForwardTube 1 n := by
    have hback := rapidityElement_real_preserves_forwardTube (-a)
      (complexLorentzAction (rapidityElement (a : ℂ)) (fun k μ => -(w k μ))) hFT'
    have hmul :
        rapidityElement (((-a : ℝ) : ℂ)) * rapidityElement (a : ℂ) =
          rapidityElement (0 : ℂ) := by
      simpa using
        (rapidityElement_mul (x := (((-a : ℝ) : ℂ))) (y := (a : ℂ))).symm
    rw [← complexLorentzAction_mul, hmul, rapidityElement_zero, complexLorentzAction_one] at hback
    exact hback
  exact neg_not_mem_forwardTube_d1 w hw hnegFT

private theorem d1_exists_rapidityElement_principal_im_strict [NeZero n]
    (Λ : ComplexLorentzGroup 1)
    (w : Fin n → Fin (1 + 1) → ℂ)
    (hw : w ∈ ForwardTube 1 n)
    (hΛw : complexLorentzAction Λ w ∈ ForwardTube 1 n) :
    ∃ a b : ℝ, |b| < Real.pi ∧
      Λ = rapidityElement ((a : ℂ) + (b : ℂ) * Complex.I) := by
  rcases d1_exists_rapidityElement_principal_im Λ with ⟨a, b, hbIoc, hrepr⟩
  have hact : complexLorentzAction (rapidityElement ((a : ℂ) + (b : ℂ) * Complex.I)) w ∈
      ForwardTube 1 n := by
    simpa [hrepr] using hΛw
  have hb_ne_pi : b ≠ Real.pi := by
    intro hbpi
    have hactPi :
        complexLorentzAction (rapidityElement ((a : ℂ) + (Real.pi : ℂ) * Complex.I)) w ∈
          ForwardTube 1 n := by
      simpa [hbpi] using hact
    exact (rapidityElement_re_add_piI_not_orbit (n := n) a w hw) hactPi
  have hb_lt_pi : b < Real.pi := lt_of_le_of_ne hbIoc.2 hb_ne_pi
  have hb_abs_lt : |b| < Real.pi := by
    exact abs_lt.mpr ⟨hbIoc.1, hb_lt_pi⟩
  exact ⟨a, b, hb_abs_lt, hrepr⟩

private theorem continuous_rapidityElement_pureImag (b : ℝ) :
    Continuous (fun t : unitInterval =>
      rapidityElement (((b * (t : ℝ) : ℝ) : ℂ) * Complex.I)) := by
  have hind : Topology.IsInducing
      (ComplexLorentzGroup.val :
        ComplexLorentzGroup 1 → Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ) := ⟨rfl⟩
  rw [hind.continuous_iff]
  have harg_cont : Continuous
      (fun t : unitInterval => (((b * (t : ℝ) : ℝ) : ℂ) * Complex.I)) :=
    (Complex.continuous_ofReal.comp (continuous_const.mul continuous_subtype_val)).mul
      continuous_const
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j
  · simpa [rapidityElement, rapidityMatrix] using Complex.continuous_cosh.comp harg_cont
  · simpa [rapidityElement, rapidityMatrix] using Complex.continuous_sinh.comp harg_cont
  · simpa [rapidityElement, rapidityMatrix] using Complex.continuous_sinh.comp harg_cont
  · simpa [rapidityElement, rapidityMatrix] using Complex.continuous_cosh.comp harg_cont

private theorem continuous_rapidityElement_realImag (a b : ℝ) :
    Continuous (fun t : unitInterval =>
      rapidityElement ((((a * (t : ℝ) : ℝ) : ℂ) + (b : ℂ) * Complex.I))) := by
  have hind : Topology.IsInducing
      (ComplexLorentzGroup.val :
        ComplexLorentzGroup 1 → Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ) := ⟨rfl⟩
  rw [hind.continuous_iff]
  have harg_cont : Continuous
      (fun t : unitInterval => (((a * (t : ℝ) : ℝ) : ℂ) + (b : ℂ) * Complex.I)) :=
    (Complex.continuous_ofReal.comp (continuous_const.mul continuous_subtype_val)).add
      continuous_const
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j
  · simpa [rapidityElement, rapidityMatrix] using Complex.continuous_cosh.comp harg_cont
  · simpa [rapidityElement, rapidityMatrix] using Complex.continuous_sinh.comp harg_cont
  · simpa [rapidityElement, rapidityMatrix] using Complex.continuous_sinh.comp harg_cont
  · simpa [rapidityElement, rapidityMatrix] using Complex.continuous_cosh.comp harg_cont

private theorem joinedIn_orbitSet_one_rapidityImag [NeZero n]
    (w : Fin n → Fin (1 + 1) → ℂ) (hw : w ∈ ForwardTube 1 n)
    (b : ℝ)
    (h1 : complexLorentzAction (rapidityElement ((b : ℂ) * Complex.I)) w ∈ ForwardTube 1 n)
    (hb : |b| < Real.pi) :
    JoinedIn (orbitSet (n := n) w)
      (1 : ComplexLorentzGroup 1) (rapidityElement ((b : ℂ) * Complex.I)) := by
  refine ⟨
    { toFun := fun t => rapidityElement (((b * (t : ℝ) : ℝ) : ℂ) * Complex.I)
      continuous_toFun := continuous_rapidityElement_pureImag b
      source' := by
        simp [rapidityElement_zero, mul_zero]
      target' := by
        simp },
    ?_⟩
  intro t
  exact pureImag_rapidity_preserves_forwardTube_segment b w hw h1 hb t.2.1 t.2.2

private theorem joinedIn_orbitSet_rapidityImag_to_realImag [NeZero n]
    (w : Fin n → Fin (1 + 1) → ℂ) (a b : ℝ)
    (hB : complexLorentzAction (rapidityElement ((b : ℂ) * Complex.I)) w ∈ ForwardTube 1 n) :
    JoinedIn (orbitSet (n := n) w)
      (rapidityElement ((b : ℂ) * Complex.I))
      (rapidityElement ((a : ℂ) + (b : ℂ) * Complex.I)) := by
  refine ⟨
    { toFun := fun t => rapidityElement ((((a * (t : ℝ) : ℝ) : ℂ) + (b : ℂ) * Complex.I))
      continuous_toFun := continuous_rapidityElement_realImag a b
      source' := by
        simp
      target' := by
        simp },
    ?_⟩
  intro t
  have hreal :
      complexLorentzAction
        (rapidityElement (((a * (t : ℝ) : ℝ) : ℂ)))
        (complexLorentzAction (rapidityElement ((b : ℂ) * Complex.I)) w) ∈
      ForwardTube 1 n := by
    exact rapidityElement_real_preserves_forwardTube ((a * (t : ℝ) : ℝ))
      (complexLorentzAction (rapidityElement ((b : ℂ) * Complex.I)) w) hB
  have hdecomp :
      rapidityElement ((((a * (t : ℝ) : ℝ) : ℂ) + (b : ℂ) * Complex.I)) =
        rapidityElement (((a * (t : ℝ) : ℝ) : ℂ)) *
          rapidityElement ((b : ℂ) * Complex.I) := by
    simpa using
      (rapidityElement_mul
        (x := (((a * (t : ℝ) : ℝ) : ℂ))) (y := (b : ℂ) * Complex.I))
  show rapidityElement ((((a * (t : ℝ) : ℝ) : ℂ) + (b : ℂ) * Complex.I)) ∈ orbitSet w
  show complexLorentzAction (rapidityElement ((((a * (t : ℝ) : ℝ) : ℂ) + (b : ℂ) * Complex.I))) w ∈
      ForwardTube 1 n
  rw [hdecomp, complexLorentzAction_mul]
  exact hreal

private theorem rapidityElement_cancel_real (a b : ℝ) :
    rapidityElement (((-a : ℝ) : ℂ)) * rapidityElement ((a : ℂ) + (b : ℂ) * Complex.I) =
      rapidityElement ((b : ℂ) * Complex.I) := by
  calc
    rapidityElement (((-a : ℝ) : ℂ)) * rapidityElement ((a : ℂ) + (b : ℂ) * Complex.I)
        = rapidityElement ((((-a : ℝ) : ℂ)) + ((a : ℂ) + (b : ℂ) * Complex.I)) := by
            symm
            exact rapidityElement_mul (x := (((-a : ℝ) : ℂ)))
              (y := (a : ℂ) + (b : ℂ) * Complex.I)
    _ = rapidityElement ((b : ℂ) * Complex.I) := by
      have hsum :
          ((((-a : ℝ) : ℂ)) + ((a : ℂ) + (b : ℂ) * Complex.I)) = ((b : ℂ) * Complex.I) := by
        simp
      rw [hsum]

private theorem d1_joinedIn_orbitSet_one_to_any [NeZero n]
    (w : Fin n → Fin (1 + 1) → ℂ) (hw : w ∈ ForwardTube 1 n)
    {Λ : ComplexLorentzGroup 1}
    (hΛ : Λ ∈ orbitSet (n := n) w) :
    JoinedIn (orbitSet (n := n) w) (1 : ComplexLorentzGroup 1) Λ := by
  rcases d1_exists_rapidityElement_principal_im_strict (n := n) Λ w hw hΛ with
    ⟨a, b, hb, hrepr⟩
  have hback :
      complexLorentzAction (rapidityElement (((-a : ℝ) : ℂ)))
        (complexLorentzAction Λ w) ∈ ForwardTube 1 n := by
    exact rapidityElement_real_preserves_forwardTube (-a)
      (complexLorentzAction Λ w) hΛ
  have hcancel :
      rapidityElement (((-a : ℝ) : ℂ)) * Λ = rapidityElement ((b : ℂ) * Complex.I) := by
    calc
      rapidityElement (((-a : ℝ) : ℂ)) * Λ
          = rapidityElement (((-a : ℝ) : ℂ)) *
              rapidityElement ((a : ℂ) + (b : ℂ) * Complex.I) := by
              simp [hrepr]
      _ = rapidityElement ((b : ℂ) * Complex.I) :=
        rapidityElement_cancel_real a b
  have hB :
      complexLorentzAction (rapidityElement ((b : ℂ) * Complex.I)) w ∈ ForwardTube 1 n := by
    have hback' :
        complexLorentzAction (rapidityElement (((-a : ℝ) : ℂ)) * Λ) w ∈ ForwardTube 1 n := by
      simpa [complexLorentzAction_mul] using hback
    rw [hcancel] at hback'
    exact hback'
  have hjoin1 :
      JoinedIn (orbitSet (n := n) w)
        (1 : ComplexLorentzGroup 1) (rapidityElement ((b : ℂ) * Complex.I)) := by
    exact joinedIn_orbitSet_one_rapidityImag (n := n) w hw b hB hb
  have hjoin2 :
      JoinedIn (orbitSet (n := n) w)
        (rapidityElement ((b : ℂ) * Complex.I))
        (rapidityElement ((a : ℂ) + (b : ℂ) * Complex.I)) := by
    exact joinedIn_orbitSet_rapidityImag_to_realImag (n := n) w a b hB
  have hjoin2' :
      JoinedIn (orbitSet (n := n) w)
        (rapidityElement ((b : ℂ) * Complex.I)) Λ := by
    simpa [hrepr] using hjoin2
  exact hjoin1.trans hjoin2'

private theorem isPreconnected_of_joinedIn_base
    {X : Type*} [TopologicalSpace X]
    {S : Set X} {x0 : X}
    (hx0 : x0 ∈ S)
    (hjoined : ∀ y ∈ S, JoinedIn S x0 y) :
    IsPreconnected S := by
  let x0S : S := ⟨x0, hx0⟩
  have h_joined_subtype : ∀ y : S, Joined x0S y := by
    intro y
    exact (joinedIn_iff_joined (x_in := hx0) (y_in := y.2)).mp (hjoined y y.2)
  haveI : PathConnectedSpace S := by
    refine PathConnectedSpace.mk ?_ ?_
    · exact ⟨x0S⟩
    · intro x y
      exact (h_joined_subtype x).symm.trans (h_joined_subtype y)
  exact (isPreconnected_iff_preconnectedSpace).2 (inferInstance : PreconnectedSpace S)

private theorem d1_orbitSet_isPreconnected [NeZero n]
    (w : Fin n → Fin (1 + 1) → ℂ) (hw : w ∈ ForwardTube 1 n) :
    IsPreconnected (orbitSet (n := n) w) := by
  have h_one : (1 : ComplexLorentzGroup 1) ∈ orbitSet (n := n) w := by
    simpa [orbitSet, complexLorentzAction_one] using hw
  refine isPreconnected_of_joinedIn_base (S := orbitSet (n := n) w)
    (x0 := (1 : ComplexLorentzGroup 1)) h_one ?_
  intro Λ hΛ
  exact d1_joinedIn_orbitSet_one_to_any (n := n) w hw hΛ

/-- Public wrapper for the `d = 1` rapidity normal form element. -/
def rapidityElementD1 (θ : ℂ) : ComplexLorentzGroup 1 :=
  rapidityElement θ

/-- Multiplicative composition law for `d = 1` rapidity elements. -/
theorem rapidityElementD1_mul (x y : ℂ) :
    rapidityElementD1 (x + y) = rapidityElementD1 x * rapidityElementD1 y := by
  simpa [rapidityElementD1] using rapidityElement_mul x y

/-- Every `d = 1` complex Lorentz element admits principal-imaginary rapidity
coordinates with `b ∈ (-π, π]`. -/
theorem d1_exists_rapidityElement_principal_im_repr
    (Λ : ComplexLorentzGroup 1) :
    ∃ a b : ℝ, b ∈ Set.Ioc (-Real.pi) Real.pi ∧
      Λ = rapidityElementD1 ((a : ℂ) + (b : ℂ) * Complex.I) := by
  rcases d1_exists_rapidityElement_principal_im Λ with ⟨a, b, hb, hrepr⟩
  exact ⟨a, b, hb, by simpa [rapidityElementD1] using hrepr⟩

/-- Real rapidity elements preserve the `d = 1` forward tube. -/
theorem rapidityElementD1_real_preserves_forwardTube
    (a : ℝ) {n : ℕ}
    (z : Fin n → Fin (1 + 1) → ℂ)
    (hz : z ∈ BHWCore.ForwardTube 1 n) :
    BHWCore.complexLorentzAction (d := 1) (n := n) (rapidityElementD1 (a : ℂ)) z
      ∈ BHWCore.ForwardTube 1 n := by
  have hz' : z ∈ ForwardTube 1 n := by
    simpa [ForwardTube] using hz
  have hpres : complexLorentzAction (rapidityElement (a : ℂ)) z ∈ ForwardTube 1 n :=
    rapidityElement_real_preserves_forwardTube a z hz'
  simpa [rapidityElementD1, complexLorentzAction, ForwardTube] using hpres

/-- Public wrapper for the principal-imaginary rapidity decomposition in `d = 1`.

If both `w` and `Λ • w` lie in the forward tube, then `Λ` can be written as
`rapidityElementD1 (a + i b)` with `|b| < π`. -/
theorem d1_exists_rapidityElement_principal_im_strict_of_forwardTube [NeZero n]
    (Λ : ComplexLorentzGroup 1)
    (w : Fin n → Fin (1 + 1) → ℂ)
    (hw : w ∈ BHWCore.ForwardTube 1 n)
    (hΛw : BHWCore.complexLorentzAction (d := 1) (n := n) Λ w ∈ BHWCore.ForwardTube 1 n) :
    ∃ a b : ℝ, |b| < Real.pi ∧
      Λ = rapidityElementD1 ((a : ℂ) + (b : ℂ) * Complex.I) := by
  have hw' : w ∈ ForwardTube 1 n := by
    simpa [ForwardTube] using hw
  have hΛw' : complexLorentzAction Λ w ∈ ForwardTube 1 n := by
    simpa [complexLorentzAction, ForwardTube] using hΛw
  rcases d1_exists_rapidityElement_principal_im_strict (n := n) Λ w hw' hΛw' with
    ⟨a, b, hb, hrepr⟩
  exact ⟨a, b, hb, by simpa [rapidityElementD1] using hrepr⟩

theorem orbitSet_isPreconnected_d1
    (w : Fin n → Fin (1 + 1) → ℂ) (hw : w ∈ BHWCore.ForwardTube 1 n) :
    IsPreconnected {Λ : ComplexLorentzGroup 1 |
      BHWCore.complexLorentzAction (d := 1) (n := n) Λ w ∈ BHWCore.ForwardTube 1 n} := by
  have hw' : w ∈ ForwardTube 1 n := by
    simpa [ForwardTube] using hw
  have hpre : IsPreconnected (orbitSet (n := n) w) := by
    by_cases hn : n = 0
    · subst hn
      have hft0 : ∀ z : Fin 0 → Fin (1 + 1) → ℂ, z ∈ ForwardTube 1 0 := by
        intro z k
        exact (Fin.elim0 k)
      have h_orbit_univ : orbitSet (n := 0) w = Set.univ := by
        ext Λ
        constructor
        · intro _
          trivial
        · intro _
          exact hft0 (complexLorentzAction Λ w)
      haveI : PathConnectedSpace (ComplexLorentzGroup 1) :=
        pathConnectedSpace_iff_univ.mpr ComplexLorentzGroup.isPathConnected
      simpa [h_orbit_univ] using
        (PreconnectedSpace.isPreconnected_univ (α := ComplexLorentzGroup 1))
    · haveI : NeZero n := ⟨hn⟩
      exact d1_orbitSet_isPreconnected (n := n) w hw'
  simpa [orbitSet, ForwardTube, complexLorentzAction, BHWCore.complexLorentzAction] using hpre

end BHW
