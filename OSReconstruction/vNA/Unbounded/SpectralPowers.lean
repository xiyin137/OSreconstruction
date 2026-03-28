/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.vNA.Unbounded.Spectral
import OSReconstruction.vNA.Bochner.Convergence
import OSReconstruction.vNA.Bochner.Applications

/-!
# Powers and One-Parameter Unitary Groups for Self-Adjoint Operators

This file continues the unbounded spectral development with two derived layers:

- powers `T^s` for positive self-adjoint operators, and
- the one-parameter unitary group `U(t) = e^{itT}` for self-adjoint operators.

The open foundational gaps in this lane now live here instead of in the core
spectral-construction file.
-/

noncomputable section

open scoped InnerProduct ComplexConjugate Classical NNReal
open Filter Topology

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-! ### Powers of positive self-adjoint operators -/

/-- For a positive self-adjoint operator T and s ∈ ℂ with Re(s) = 0, define T^s.
    This uses functional calculus: T^s = ∫ λ^s dP(λ).
    The hypothesis Re(s) = 0 ensures the integrand |λ^s| = 1 is bounded. -/
def UnboundedOperator.power (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (_hpos : T.IsPositive) (s : ℂ) (hs : s.re = 0) :
    H →L[ℂ] H :=
  let P := T.spectralMeasure hT hsa
  let f := fun x : ℝ => if x > 0 then Complex.exp (s * Complex.log x) else 0
  functionalCalculus P f
    (by -- Integrability: |f(x)| ≤ 1 (since Re(s) = 0) and μ_z is finite → integrable
      intro z; haveI := P.diagonalMeasure_isFiniteMeasure z
      have hf_bdd : ∀ x, ‖f x‖ ≤ 1 := by
        intro x; simp only [f]
        split_ifs with hx
        · rw [Complex.norm_exp,
              show Complex.log (↑x : ℂ) = ↑(Real.log x) from
                (Complex.ofReal_log (le_of_lt hx)).symm]
          have hre : (s * ↑(Real.log x)).re = 0 := by
            simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hs]
          rw [hre, Real.exp_zero]
        · simp
      exact (MeasureTheory.integrable_const (1 : ℂ)).mono
        (Measurable.aestronglyMeasurable (by
          apply Measurable.ite measurableSet_Ioi
          · exact Complex.continuous_exp.measurable.comp
              (measurable_const.mul
                (Complex.measurable_log.comp Complex.continuous_ofReal.measurable))
          · exact measurable_const))
        (by filter_upwards with x; simp only [norm_one]; exact hf_bdd x))
    (by -- Boundedness: |exp(s * log x)| = exp(Re(s * log x)) = exp(0) = 1
      refine ⟨1, zero_le_one, fun x => ?_⟩
      simp only [f]
      split_ifs with hx
      · rw [Complex.norm_exp,
            show Complex.log (↑x : ℂ) = ↑(Real.log x) from
              (Complex.ofReal_log (le_of_lt hx)).symm]
        have hre : (s * ↑(Real.log x)).re = 0 := by
          simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hs]
        rw [hre, Real.exp_zero]
      · simp)

/-- T^(s+t) = T^s ∘ T^t

    **Proof:** Uses `functionalCalculus_mul`. The function λ^(s+t) = λ^s · λ^t pointwise,
    so ∫ λ^(s+t) dP = ∫ (λ^s · λ^t) dP = (∫ λ^s dP)(∫ λ^t dP) = T^s ∘ T^t.
    Depends on: `functionalCalculus_mul`. -/
theorem UnboundedOperator.power_add (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive) (s t : ℂ)
    (hs : s.re = 0) (ht : t.re = 0) :
    T.power hT hsa hpos (s + t) (by simp [Complex.add_re, hs, ht]) =
    T.power hT hsa hpos s hs ∘L T.power hT hsa hpos t ht := by
  set P := T.spectralMeasure hT hsa
  -- The power functions
  let f_s : ℝ → ℂ := fun x => if x > 0 then Complex.exp (s * Complex.log x) else 0
  let f_t : ℝ → ℂ := fun x => if x > 0 then Complex.exp (t * Complex.log x) else 0
  -- Norm bound: |exp(u * log x)| ≤ 1 when Re(u) = 0
  have power_norm_le : ∀ (u : ℂ), u.re = 0 → ∀ x : ℝ,
      ‖(if x > 0 then Complex.exp (u * Complex.log ↑x) else 0 : ℂ)‖ ≤ 1 := by
    intro u hu x
    split_ifs with hx
    · rw [Complex.norm_exp,
          show Complex.log (↑x : ℂ) = ↑(Real.log x) from (Complex.ofReal_log (le_of_lt hx)).symm]
      have : (u * ↑(Real.log x)).re = 0 := by
        simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hu]
      rw [this, Real.exp_zero]
    · simp
  -- Measurability
  have power_meas : ∀ (u : ℂ), Measurable (fun x : ℝ =>
      if x > 0 then Complex.exp (u * Complex.log ↑x) else (0 : ℂ)) := by
    intro u
    apply Measurable.ite measurableSet_Ioi
    · exact Complex.continuous_exp.measurable.comp
        (measurable_const.mul (Complex.measurable_log.comp Complex.continuous_ofReal.measurable))
    · exact measurable_const
  -- Integrability
  have power_int : ∀ (u : ℂ), u.re = 0 → ∀ z : H,
      MeasureTheory.Integrable (fun (x : ℝ) => if x > 0 then Complex.exp (u * Complex.log ↑x) else 0)
        (P.diagonalMeasure z) := by
    intro u hu z
    haveI := P.diagonalMeasure_isFiniteMeasure z
    exact (MeasureTheory.integrable_const (1 : ℂ)).mono
      ((power_meas u).aestronglyMeasurable)
      (by filter_upwards with x; simp only [norm_one]; exact power_norm_le u hu x)
  -- Key pointwise identity: f_{s+t} = f_s * f_t
  have h_eq : (fun x : ℝ => if x > 0 then Complex.exp ((s + t) * Complex.log ↑x) else (0 : ℂ)) =
      f_s * f_t := by
    ext x; simp only [Pi.mul_apply, f_s, f_t]
    split_ifs with hx
    · rw [add_mul, Complex.exp_add]
    · simp
  -- Product norm bound
  have hfg_bdd : ∃ M, 0 ≤ M ∧ ∀ x, ‖(f_s * f_t) x‖ ≤ M :=
    ⟨1, zero_le_one, fun x => by
      simp only [Pi.mul_apply, f_s, f_t]; rw [norm_mul]
      calc ‖(if x > 0 then Complex.exp (s * Complex.log ↑x) else 0 : ℂ)‖ *
            ‖(if x > 0 then Complex.exp (t * Complex.log ↑x) else 0 : ℂ)‖
          ≤ 1 * 1 := by
            exact mul_le_mul (power_norm_le s hs x) (power_norm_le t ht x)
              (norm_nonneg _) zero_le_one
        _ = 1 := mul_one 1⟩
  -- Product integrability
  have hfg_int : ∀ z : H, MeasureTheory.Integrable (f_s * f_t) (P.diagonalMeasure z) := by
    rw [← h_eq]; exact power_int (s + t) (by simp [Complex.add_re, hs, ht])
  -- Get the functionalCalculus_mul result
  have hmul := functionalCalculus_mul P f_s f_t
    (power_int s hs) ⟨1, zero_le_one, power_norm_le s hs⟩
    (power_int t ht) ⟨1, zero_le_one, power_norm_le t ht⟩
    hfg_int hfg_bdd (power_meas t)
  -- Use calc: power(s+t) = fc(f_s*f_t) = fc(f_s) ∘L fc(f_t) = power(s) ∘L power(t)
  have h_st_re : (s + t).re = 0 := by simp [Complex.add_re, hs, ht]
  calc T.power hT hsa hpos (s + t) _
      = functionalCalculus P (f_s * f_t) hfg_int hfg_bdd := by
          -- power(s+t) = fc(f_{s+t}) definitionally, and f_{s+t} = f_s * f_t
          show functionalCalculus P
            (fun x : ℝ => if x > 0 then Complex.exp ((s + t) * Complex.log ↑x) else 0)
            (power_int (s + t) h_st_re) ⟨1, zero_le_one, power_norm_le (s + t) h_st_re⟩ =
            functionalCalculus P (f_s * f_t) hfg_int hfg_bdd
          congr 1
    _ = functionalCalculus P f_s (power_int s hs) ⟨1, zero_le_one, power_norm_le s hs⟩ ∘L
        functionalCalculus P f_t (power_int t ht) ⟨1, zero_le_one, power_norm_le t ht⟩ := hmul
    _ = T.power hT hsa hpos s hs ∘L T.power hT hsa hpos t ht := rfl

/-! ### One-parameter unitary groups

The one-parameter unitary group U(t) = e^{itA} = ∫ exp(itλ) dP(λ) is defined using
the exponential function directly, not through the `power` function. This is important:
- `power` uses λ^{it} = exp(it·log λ), which requires positivity and fails at λ = 0
- The exponential exp(itλ) is defined for all λ ∈ ℝ, works for any self-adjoint operator
- No positivity hypothesis is needed
-/

/-- Norm bound: ‖exp(itx)‖ ≤ 1 for real t, x. -/
private lemma expI_norm_le (t : ℝ) (x : ℝ) :
    ‖Complex.exp (Complex.I * ↑t * ↑x)‖ ≤ 1 := by
  rw [Complex.norm_exp]
  have : (Complex.I * ↑t * ↑x).re = 0 := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  rw [this, Real.exp_zero]

/-- Measurability of exp(itx) in x for fixed t. -/
private lemma expI_measurable (t : ℝ) :
    Measurable (fun x : ℝ => Complex.exp (Complex.I * ↑t * ↑x)) :=
  Complex.continuous_exp.measurable.comp
    ((continuous_const.mul Complex.continuous_ofReal).measurable)

open MeasureTheory in
/-- Integrability of exp(itx) against spectral diagonal measures. -/
private lemma expI_integrable (P : SpectralMeasure H) (t : ℝ) (z : H) :
    Integrable (fun x : ℝ => Complex.exp (Complex.I * ↑t * ↑x))
      (P.diagonalMeasure z) := by
  haveI := P.diagonalMeasure_isFiniteMeasure z
  exact (integrable_const (1 : ℂ)).mono
    (expI_measurable t).aestronglyMeasurable
    (by filter_upwards with x; simp only [norm_one]; exact expI_norm_le t x)

/-- The functional calculus is proof-irrelevant: it depends only on the function f.
    (This is now imported from Bochner.Applications; kept as alias for backward compatibility.) -/
private lemma functionalCalculus_congr' (P : SpectralMeasure H) {f g : ℝ → ℂ}
    (hfg : f = g)
    (hf_int : ∀ z : H, MeasureTheory.Integrable f (P.diagonalMeasure z))
    (hf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M)
    (hg_int : ∀ z : H, MeasureTheory.Integrable g (P.diagonalMeasure z))
    (hg_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖g t‖ ≤ M) :
    functionalCalculus P f hf_int hf_bdd = functionalCalculus P g hg_int hg_bdd := by
  subst hfg; rfl

/-- The one-parameter unitary group generated by a self-adjoint operator.
    U(t) = e^{itA} = ∫ exp(itλ) dP(λ) where P is the spectral measure of T.

    This uses the exponential function directly (not through `power`),
    so no positivity hypothesis is needed. -/
def unitaryGroup (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (t : ℝ) : H →L[ℂ] H :=
  let P := T.spectralMeasure hT hsa
  functionalCalculus P (fun x : ℝ => Complex.exp (Complex.I * ↑t * ↑x))
    (fun z => expI_integrable P t z)
    ⟨1, zero_le_one, expI_norm_le t⟩

set_option maxHeartbeats 400000 in
open MeasureTheory in
/-- U(0) = 1. Since exp(i·0·λ) = 1 for all λ, the functional calculus gives
    the integral of the constant 1, which equals P(ℝ) = 1. -/
theorem unitaryGroup_zero (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) :
    unitaryGroup T hT hsa 0 = 1 := by
  set P := T.spectralMeasure hT hsa
  -- exp(I * 0 * x) = 1 for all x, matching Set.univ indicator
  have hfg : (fun x : ℝ => Complex.exp (Complex.I * ↑(0 : ℝ) * ↑x)) =
      Set.univ.indicator (fun _ => (1 : ℂ)) := by
    funext x; simp [Complex.exp_zero]
  show functionalCalculus P (fun x : ℝ => Complex.exp (Complex.I * ↑(0 : ℝ) * ↑x))
    (fun z => expI_integrable P 0 z) ⟨1, zero_le_one, expI_norm_le 0⟩ = 1
  apply ContinuousLinearMap.ext; intro y
  apply ext_inner_left ℂ; intro x
  rw [← functionalCalculus_inner, ContinuousLinearMap.one_apply, hfg,
    P.Bform_indicator_eq_inner Set.univ MeasurableSet.univ, P.univ,
    ContinuousLinearMap.one_apply]

set_option maxHeartbeats 400000 in
open MeasureTheory in
/-- The group law: U(s) ∘ U(t) = U(s+t).

    **Proof:** Uses `functionalCalculus_mul`. The pointwise identity
    exp(isλ) · exp(itλ) = exp(i(s+t)λ) gives the result. -/
theorem unitaryGroup_mul (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (s t : ℝ) :
    unitaryGroup T hT hsa s ∘L unitaryGroup T hT hsa t =
    unitaryGroup T hT hsa (s + t) := by
  set P := T.spectralMeasure hT hsa
  set f_s := fun x : ℝ => Complex.exp (Complex.I * ↑s * ↑x)
  set f_t := fun x : ℝ => Complex.exp (Complex.I * ↑t * ↑x)
  -- Pointwise identity: exp(isλ) · exp(itλ) = exp(i(s+t)λ)
  have h_eq : (fun x : ℝ => Complex.exp (Complex.I * ↑(s + t) * ↑x)) = f_s * f_t := by
    ext x; simp only [Pi.mul_apply, f_s, f_t]
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  -- Product norm bound
  have hfg_bdd : ∃ M, 0 ≤ M ∧ ∀ x, ‖(f_s * f_t) x‖ ≤ M :=
    ⟨1, zero_le_one, fun x => by
      simp only [Pi.mul_apply, f_s, f_t, norm_mul]
      calc ‖Complex.exp (Complex.I * ↑s * ↑x)‖ * ‖Complex.exp (Complex.I * ↑t * ↑x)‖
          ≤ 1 * 1 := mul_le_mul (expI_norm_le s x) (expI_norm_le t x)
            (norm_nonneg _) zero_le_one
        _ = 1 := mul_one 1⟩
  -- Product integrability
  have hfg_int : ∀ z : H, Integrable (f_s * f_t) (P.diagonalMeasure z) := by
    rw [← h_eq]; exact fun z => expI_integrable P (s + t) z
  -- Apply functionalCalculus_mul
  have hmul := functionalCalculus_mul P f_s f_t
    (fun z => expI_integrable P s z) ⟨1, zero_le_one, expI_norm_le s⟩
    (fun z => expI_integrable P t z) ⟨1, zero_le_one, expI_norm_le t⟩
    hfg_int hfg_bdd (expI_measurable t)
  -- Use show + congr 1 pattern (same as power_add):
  -- U(s) ∘L U(t) = fc(f_s * f_t) = U(s+t)
  have h_eq_sym := h_eq.symm
  calc unitaryGroup T hT hsa s ∘L unitaryGroup T hT hsa t
      = functionalCalculus P (f_s * f_t) hfg_int hfg_bdd := by
          show functionalCalculus P f_s
            (fun z => expI_integrable P s z) ⟨1, zero_le_one, expI_norm_le s⟩ ∘L
            functionalCalculus P f_t
            (fun z => expI_integrable P t z) ⟨1, zero_le_one, expI_norm_le t⟩ =
            functionalCalculus P (f_s * f_t) hfg_int hfg_bdd
          exact hmul.symm
    _ = unitaryGroup T hT hsa (s + t) := by
          show functionalCalculus P (f_s * f_t) hfg_int hfg_bdd =
            functionalCalculus P (fun x : ℝ => Complex.exp (Complex.I * ↑(s + t) * ↑x))
            (fun z => expI_integrable P (s + t) z) ⟨1, zero_le_one, expI_norm_le (s + t)⟩
          congr 1

set_option maxHeartbeats 400000 in
open MeasureTheory in
/-- U(t)* = U(-t)

    **Proof:** Uses `functionalCalculus_star`:
    U(t)* = (∫ exp(itλ) dP)* = ∫ conj(exp(itλ)) dP = ∫ exp(-itλ) dP = U(-t) -/
theorem unitaryGroup_inv (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (t : ℝ) :
    ContinuousLinearMap.adjoint (unitaryGroup T hT hsa t) =
    unitaryGroup T hT hsa (-t) := by
  set P := T.spectralMeasure hT hsa
  set f_t := fun x : ℝ => Complex.exp (Complex.I * ↑t * ↑x)
  set f_neg := fun x : ℝ => Complex.exp (Complex.I * ↑(-t) * ↑x)
  -- Key identity: star ∘ f_t = f_neg
  have hsfg : star ∘ f_t = f_neg := by
    funext x
    simp only [Function.comp, f_t, f_neg]
    have star_exp : ∀ z : ℂ, star (Complex.exp z) = Complex.exp (star z) := by
      intro z; simp [Complex.exp_conj]
    rw [star_exp]
    congr 1
    simp only [star_mul', Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
    push_cast; ring
  -- Norm bound for star ∘ f_t
  have hsf_norm_le : ∀ x, ‖(star ∘ f_t) x‖ ≤ 1 := by
    intro x; simp only [Function.comp, norm_star]; exact expI_norm_le t x
  -- Measurability of star ∘ f_t
  have hsf_meas : Measurable (star ∘ f_t) :=
    continuous_star.measurable.comp (expI_measurable t)
  -- Integrability of star ∘ f_t
  have hsf_int : ∀ z : H, Integrable (star ∘ f_t) (P.diagonalMeasure z) := by
    intro z; haveI := P.diagonalMeasure_isFiniteMeasure z
    exact (integrable_const (1 : ℂ)).mono hsf_meas.aestronglyMeasurable
      (by filter_upwards with x; simp only [norm_one]; exact hsf_norm_le x)
  have hsf_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖(star ∘ f_t) t‖ ≤ M :=
    ⟨1, zero_le_one, hsf_norm_le⟩
  -- Apply functionalCalculus_star
  have h_star := functionalCalculus_star P f_t
    (fun z => expI_integrable P t z) ⟨1, zero_le_one, expI_norm_le t⟩
    hsf_int hsf_bdd
  -- U(t)* = fc(star ∘ f_t) = fc(f_neg) = U(-t)
  calc ContinuousLinearMap.adjoint (unitaryGroup T hT hsa t)
      = functionalCalculus P (star ∘ f_t) hsf_int hsf_bdd := by
          show ContinuousLinearMap.adjoint (functionalCalculus P f_t
            (fun z => expI_integrable P t z) ⟨1, zero_le_one, expI_norm_le t⟩) =
            functionalCalculus P (star ∘ f_t) hsf_int hsf_bdd
          exact h_star
    _ = unitaryGroup T hT hsa (-t) := by
          show functionalCalculus P (star ∘ f_t) hsf_int hsf_bdd =
            functionalCalculus P f_neg
            (fun z => expI_integrable P (-t) z) ⟨1, zero_le_one, expI_norm_le (-t)⟩
          congr 1

/-- U(-t) ∘ U(t) = 1 (left inverse) -/
theorem unitaryGroup_neg_comp (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (t : ℝ) :
    unitaryGroup T hT hsa (-t) ∘L unitaryGroup T hT hsa t = 1 := by
  rw [unitaryGroup_mul, neg_add_cancel, unitaryGroup_zero]

/-- U(t) ∘ U(-t) = 1 (right inverse) -/
theorem unitaryGroup_comp_neg (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (t : ℝ) :
    unitaryGroup T hT hsa t ∘L unitaryGroup T hT hsa (-t) = 1 := by
  rw [unitaryGroup_mul, add_neg_cancel, unitaryGroup_zero]

/-- The integral ∫ exp(its) dμ(s) is continuous in t for any finite measure μ.
    Uses Lebesgue dominated convergence with constant bound 1. -/
private lemma continuous_integral_cexp (μ : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsFiniteMeasure μ] :
    Continuous (fun t : ℝ => ∫ s, Complex.exp (Complex.I * ↑t * ↑s) ∂μ) := by
  apply continuous_iff_continuousAt.mpr; intro t₀
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
  · -- AEStronglyMeasurable for each t near t₀
    filter_upwards with t
    exact (expI_measurable t).aestronglyMeasurable
  · -- Norm bound: ‖exp(its)‖ ≤ 1
    filter_upwards with t
    filter_upwards with s using expI_norm_le t s
  · -- Bound integrable on finite measure
    exact MeasureTheory.integrable_const 1
  · -- Pointwise limit: exp(its) → exp(it₀s) as t → t₀ for each fixed s
    filter_upwards with s
    exact (Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)).continuousAt

-- Strong continuity: t ↦ U(t)x is continuous for all x
-- Reference: Reed-Simon Theorem VIII.8
-- Proof: weak continuity (DCT) + isometry (U(t)*U(t)=I) → strong continuity
set_option maxHeartbeats 800000 in
open MeasureTheory in
theorem unitaryGroup_continuous (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (x : H) :
    Continuous (fun t => unitaryGroup T hT hsa t x) := by
  set P := T.spectralMeasure hT hsa
  -- Step 1: Each ∫ exp(its) dμ_z(s) is continuous in t
  have h_int_cont : ∀ z : H, Continuous (fun t : ℝ =>
      ∫ s, Complex.exp (Complex.I * ↑t * ↑s) ∂(P.diagonalMeasure z)) :=
    fun z => continuous_integral_cexp (P.diagonalMeasure z)
  -- Step 2: spectralIntegral of exp(it·) is continuous in t
  have h_si_cont : ∀ y : H, Continuous (fun t : ℝ =>
      P.spectralIntegral (fun s => Complex.exp (Complex.I * ↑t * ↑s)) y x) := by
    intro y; unfold SpectralMeasure.spectralIntegral
    exact continuous_const.mul
      ((((h_int_cont (y + x)).sub (h_int_cont (y - x))).sub
        (continuous_const.mul (h_int_cont (y + Complex.I • x)))).add
        (continuous_const.mul (h_int_cont (y - Complex.I • x))))
  -- Step 3: ⟨y, U(t)x⟩ is continuous in t (weak continuity)
  have h_weak : ∀ y : H, Continuous (fun t =>
      @inner ℂ H _ y (unitaryGroup T hT hsa t x)) := by
    intro y; convert h_si_cont y using 1; ext t
    show @inner ℂ H _ y (functionalCalculus P
      (fun s => Complex.exp (Complex.I * ↑t * ↑s))
      (fun z => expI_integrable P t z) ⟨1, zero_le_one, expI_norm_le t⟩ x) = _
    exact spectral_theorem T hT hsa _ _ _ y x
  -- Step 4: U(t) is isometric: ‖U(t)x‖ = ‖x‖
  have h_iso : ∀ t, ‖unitaryGroup T hT hsa t x‖ = ‖x‖ := by
    intro t
    have h_adj_comp : ContinuousLinearMap.adjoint (unitaryGroup T hT hsa t) ∘L
        unitaryGroup T hT hsa t = 1 := by
      rw [unitaryGroup_inv, unitaryGroup_neg_comp]
    have h_inner_eq : @inner ℂ H _ (unitaryGroup T hT hsa t x)
        (unitaryGroup T hT hsa t x) = @inner ℂ H _ x x := by
      rw [← ContinuousLinearMap.adjoint_inner_right (unitaryGroup T hT hsa t) x
        (unitaryGroup T hT hsa t x), ← ContinuousLinearMap.comp_apply,
        h_adj_comp, ContinuousLinearMap.one_apply]
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h_inner_eq
    have h_sq : ‖unitaryGroup T hT hsa t x‖ ^ 2 = ‖x‖ ^ 2 := by exact_mod_cast h_inner_eq
    calc ‖unitaryGroup T hT hsa t x‖
        = Real.sqrt (‖unitaryGroup T hT hsa t x‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (‖x‖ ^ 2) := by rw [h_sq]
      _ = ‖x‖ := Real.sqrt_sq (norm_nonneg _)
  -- Step 5: Strong continuity from weak continuity + isometry
  rw [continuous_iff_continuousAt]; intro t₀
  rw [Metric.continuousAt_iff]; intro ε hε
  -- Re⟨U(t₀)x, U(t)x⟩ is continuous at t = t₀
  have h_re_cont : ContinuousAt (fun t =>
      (@inner ℂ H _ (unitaryGroup T hT hsa t₀ x)
        (unitaryGroup T hT hsa t x)).re) t₀ :=
    Complex.continuous_re.continuousAt.comp
      (h_weak (unitaryGroup T hT hsa t₀ x)).continuousAt
  -- At t = t₀: Re⟨U(t₀)x, U(t₀)x⟩ = ‖x‖²
  have h_at_t₀ : (@inner ℂ H _ (unitaryGroup T hT hsa t₀ x)
      (unitaryGroup T hT hsa t₀ x)).re = ‖x‖ ^ 2 := by
    have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (unitaryGroup T hT hsa t₀ x)
    rw [this, h_iso t₀]; norm_cast
  -- Find δ such that |Re⟨U(t₀)x, U(t)x⟩ - ‖x‖²| < ε²/4 when dist t t₀ < δ
  have hε2 : (0 : ℝ) < ε ^ 2 / 4 := by positivity
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.mp h_re_cont (ε ^ 2 / 4) hε2
  refine ⟨δ, hδ, fun t ht => ?_⟩
  -- ‖U(t)x - U(t₀)x‖² < ε², hence ‖U(t)x - U(t₀)x‖ < ε
  have h_re_close : |(@inner ℂ H _ (unitaryGroup T hT hsa t₀ x)
      (unitaryGroup T hT hsa t x)).re - ‖x‖ ^ 2| < ε ^ 2 / 4 := by
    have := hδε ht; rw [Real.dist_eq, h_at_t₀] at this; exact this
  -- ‖U(t)x - U(t₀)x‖² = 2‖x‖² - 2*Re⟨U(t)x, U(t₀)x⟩
  have h_ns := @norm_sub_sq ℂ H _ _ _ (unitaryGroup T hT hsa t x)
    (unitaryGroup T hT hsa t₀ x)
  rw [h_iso t, h_iso t₀] at h_ns
  -- Bridge: RCLike.re and .re are definitionally equal for ℂ
  change ‖unitaryGroup T hT hsa t x - unitaryGroup T hT hsa t₀ x‖ ^ 2 =
    ‖x‖ ^ 2 - 2 * (@inner ℂ H _ (unitaryGroup T hT hsa t x)
      (unitaryGroup T hT hsa t₀ x)).re + ‖x‖ ^ 2 at h_ns
  -- Re⟨U(t)x, U(t₀)x⟩ = Re⟨U(t₀)x, U(t)x⟩ (from conjugate symmetry)
  have h_re_sym : (@inner ℂ H _ (unitaryGroup T hT hsa t x)
      (unitaryGroup T hT hsa t₀ x)).re =
      (@inner ℂ H _ (unitaryGroup T hT hsa t₀ x)
        (unitaryGroup T hT hsa t x)).re := by
    have h := inner_conj_symm (𝕜 := ℂ) (unitaryGroup T hT hsa t₀ x)
      (unitaryGroup T hT hsa t x)
    -- h : conj ⟪U(t)x, U(t₀)x⟫ = ⟪U(t₀)x, U(t)x⟫
    have conj_re_eq : ∀ z : ℂ, ((starRingEnd ℂ) z).re = z.re := fun z => by simp
    rw [← conj_re_eq]; exact congr_arg Complex.re h
  rw [h_re_sym] at h_ns
  -- h_ns : ‖...‖² = ‖x‖² - 2 * Re⟪U(t₀)x, U(t)x⟫ + ‖x‖²
  -- h_re_close : |Re⟪U(t₀)x, U(t)x⟫ - ‖x‖²| < ε²/4
  have h_bound : ‖unitaryGroup T hT hsa t x - unitaryGroup T hT hsa t₀ x‖ ^ 2 <
      ε ^ 2 := by linarith [(abs_lt.mp h_re_close).1]
  rw [dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 (le_of_lt hε) h_bound

/-! ### Spectral domain characterization and spectral representation

The fundamental bridge between the abstract operator T (defined via a Submodule
domain and linear map from the Cayley transform construction) and its spectral
measure P = T.spectralMeasure.

**Mathematical content (Reed-Simon VIII.4, Theorem VIII.6):**

1. **Spectral truncation:** T_n = ∫ λ·χ_{[-n,n]}(λ) dP(λ) is a bounded operator
   (defined via `functionalCalculus` with the bounded function λ·χ_{[-n,n]}).

2. **Domain characterization:**
   x ∈ dom(T) ⟺ ∫ λ² d⟨P(λ)x,x⟩ < ∞ ⟺ sup_n ‖T_n x‖² < ∞.

3. **Spectral representation:** For x ∈ dom(T), T_n x → Tx as n → ∞, and
   ⟨y, Tx⟩ = lim_n ⟨y, T_n x⟩ = lim_n ∫_{[-n,n]} λ d⟨P(λ)y,x⟩.

4. **Norm identity:** ‖Tx‖² = ∫ λ² d⟨P(λ)x,x⟩.

**Formalization status:** These results establish that the abstract
operator T (constructed via the Cayley transform inversion) agrees with the
limit of its spectral truncations. This is the "T-P connection" noted at
Spectral.lean line 2444. Proved via the resolvent-spectral bridge
(`resolvent_eq_functionalCalculus`) and spectral dominated convergence.
-/

/-- The spectral truncation T_n: the bounded operator ∫ λ·χ_{[-n,n]}(λ) dP(λ).
    This is obtained from `functionalCalculus` applied to the bounded function
    f_n(λ) = λ · χ_{[-n,n]}(λ), which satisfies ‖f_n‖_∞ ≤ n. -/
def spectralTruncation (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (n : ℕ) : H →L[ℂ] H :=
  let P := T.spectralMeasure hT hsa
  let f_n : ℝ → ℂ := fun s => (↑s : ℂ) * Set.indicator (Set.Icc (-(n : ℝ)) n) (fun _ => (1 : ℂ)) s
  have hf_norm : ∀ s : ℝ, ‖f_n s‖ ≤ n := by
    intro s; simp only [f_n, Set.indicator_apply]
    split_ifs with h
    · simp only [mul_one, Complex.norm_real]
      exact abs_le.mpr (Set.mem_Icc.mp h)
    · simp
  have hf_meas : Measurable f_n :=
    (Complex.continuous_ofReal.measurable).mul
      (measurable_const.indicator measurableSet_Icc)
  functionalCalculus P f_n
    (by intro z; haveI := P.diagonalMeasure_isFiniteMeasure z
        exact (MeasureTheory.integrable_const ((n : ℂ))).mono
          hf_meas.aestronglyMeasurable
          (by filter_upwards with s; simp only [Complex.norm_natCast]; exact hf_norm s))
    ⟨n, Nat.cast_nonneg n, hf_norm⟩

set_option maxHeartbeats 400000 in
open MeasureTheory in
/-- The norm of T_n x computes as a spectral integral:
    ‖T_n x‖² = ∫ λ²·χ_{[-n,n]}(λ) dμ_x(λ).

    This follows from `functionalCalculus_norm_sq'` applied to f_n:
    ‖T_n x‖² = ‖fc(f_n)(x)‖² = ∫ ‖f_n‖² dμ_x = ∫ s² · χ_{[-n,n]} dμ_x.

    Proof uses: `functionalCalculus_norm_sq'` from Convergence.lean. -/
theorem spectralTruncation_norm_sq (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (n : ℕ) (x : H) :
    ‖spectralTruncation T hT hsa n x‖ ^ 2 =
    (∫ s, ((s : ℂ) ^ 2) * Set.indicator (Set.Icc (-(n : ℝ)) n) (fun _ => (1 : ℂ)) s
      ∂((T.spectralMeasure hT hsa).diagonalMeasure x)).re := by
  set P := T.spectralMeasure hT hsa
  set f_n : ℝ → ℂ := fun s =>
    (↑s : ℂ) * Set.indicator (Set.Icc (-(n : ℝ)) n) (fun _ => (1 : ℂ)) s
  have hf_norm : ∀ s : ℝ, ‖f_n s‖ ≤ n := by
    intro s; simp only [f_n, Set.indicator_apply]
    split_ifs with h
    · simp only [mul_one, Complex.norm_real]
      exact abs_le.mpr (Set.mem_Icc.mp h)
    · simp
  have hf_meas : Measurable f_n :=
    (Complex.continuous_ofReal.measurable).mul
      (measurable_const.indicator measurableSet_Icc)
  have hf_int : ∀ z : H, Integrable f_n (P.diagonalMeasure z) := by
    intro z; haveI := P.diagonalMeasure_isFiniteMeasure z
    exact (integrable_const ((n : ℂ))).mono
      hf_meas.aestronglyMeasurable
      (by filter_upwards with s; simp only [Complex.norm_natCast]; exact hf_norm s)
  -- Step 1: ‖T_n x‖² = ∫ ‖f_n‖² dμ_x  (by functionalCalculus_norm_sq')
  have h_norm_sq := functionalCalculus_norm_sq' P f_n hf_int
    ⟨n, Nat.cast_nonneg n, hf_norm⟩ hf_meas x
  -- Step 2: ‖f_n(s)‖² = Re(s² · χ_{[-n,n]}(s))  (pointwise identity)
  have h_pw : ∀ s : ℝ, ‖f_n s‖ ^ 2 = (((s : ℂ) ^ 2) *
      Set.indicator (Set.Icc (-(n : ℝ)) n) (fun _ => (1 : ℂ)) s).re := by
    intro s; simp only [f_n, Set.indicator_apply]
    split_ifs with h
    · simp only [mul_one, Complex.norm_real]
      rw [show ‖s‖ ^ 2 = s ^ 2 from by rw [Real.norm_eq_abs]; exact sq_abs s]
      have : ((↑s : ℂ) ^ 2).re = s ^ 2 := by
        rw [show (↑s : ℂ) ^ 2 = (↑(s ^ 2) : ℂ) from by push_cast; ring]
        exact Complex.ofReal_re _
      exact this.symm
    · simp
  -- Step 3: Combine. spectralTruncation is definitionally fc(f_n) (proof-irrelevant).
  -- ‖T_n x‖² = ∫ ‖f_n‖² dμ_x = Re(∫ s² · χ dμ_x)
  -- The spectralTruncation unfolds to functionalCalculus with the same f_n.
  have h_trunc_eq : spectralTruncation T hT hsa n = functionalCalculus P f_n hf_int
      ⟨n, Nat.cast_nonneg n, hf_norm⟩ := rfl
  rw [h_trunc_eq, h_norm_sq]
  -- Goal: ∫ ‖f_n t‖² dμ_x = Re(∫ s² · χ dμ_x)
  -- Since ‖f_n(s)‖² = Re(s² · χ(s)), we have:
  -- ∫ ‖f_n‖² dμ = ∫ Re(s² · χ) dμ = Re(∫ s² · χ dμ)  (by integral_re)
  -- Rewrite pointwise
  have h_eq : (fun t => ‖f_n t‖ ^ 2) = (fun (s : ℝ) =>
      (((s : ℂ) ^ 2) * Set.indicator (Set.Icc (-(n : ℝ)) n) (fun _ => (1 : ℂ)) s).re) :=
    funext h_pw
  rw [h_eq]
  -- Now goal: ∫ (s² · χ(s)).re dμ = (∫ s² · χ(s) dμ).re
  -- This is integral_re
  let φ : ℝ → ℂ := fun s => ((s : ℂ) ^ 2) *
    Set.indicator (Set.Icc (-(n : ℝ)) n) (fun _ => (1 : ℂ)) s
  show ∫ s, (φ s).re ∂(P.diagonalMeasure x) = (∫ s, φ s ∂(P.diagonalMeasure x)).re
  have : ∀ s, (φ s).re = RCLike.re (φ s) := fun _ => rfl
  simp_rw [this]
  have hφ_int : Integrable φ (P.diagonalMeasure x) := by
    haveI := P.diagonalMeasure_isFiniteMeasure x
    have hφ_meas : Measurable φ :=
      ((Complex.continuous_ofReal.measurable.pow_const 2).mul
        (measurable_const.indicator measurableSet_Icc))
    have hφ_bdd : ∀ s : ℝ, ‖φ s‖ ≤ (n : ℝ) ^ 2 := by
      intro s; simp only [φ, Set.indicator_apply]
      split_ifs with h
      · rw [norm_mul, norm_one, mul_one]
        rw [show (↑s : ℂ) ^ 2 = ↑(s ^ 2) from by push_cast; ring, Complex.norm_real]
        have hs := Set.mem_Icc.mp h
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith
      · simp
    exact (integrable_const ((n : ℝ) ^ 2)).mono hφ_meas.aestronglyMeasurable
      (Eventually.of_forall fun s => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hφ_bdd s)
  exact integral_re hφ_int

/-! ### T-P Connection Bridge Axiom

The **T-P connection** is the fundamental bridge between the abstract operator T
(defined via the Cayley transform inversion, with domain as a Submodule) and its
spectral measure P = T.spectralMeasure. Concretely, it states that the resolvent
R = (T+i)⁻¹ coincides with the functional calculus applied to 1/(·+i).

**Mathematical content (Reed-Simon VIII.4-VIII.5):**
The spectral measure P is constructed from the Cayley transform U = (T-i)(T+i)⁻¹
via the RMK chain. By construction, U corresponds to the spectral function
φ(λ) = (λ-i)/(λ+i). Since U = 1 - 2iR (cayley_formula), we get
R = (1-U)/(2i) = fc(P, (1-φ)/(2i)) = fc(P, 1/(·+i)).

This is the single piece of spectral infrastructure needed to
prove both `spectralTruncation_tendsto` and `mem_domain_iff_square_integrable`.
All other steps in those proofs are formalized from existing infrastructure
(functionalCalculus_mul, functionalCalculus_tendsto_SOT, closedness of T, etc.).

**Status:** Proved. Uses the RMK spectral projection construction which builds P
from U and verifies U = fc(P, φ), then solves the Cayley formula for the resolvent.

References: Reed-Simon VIII.4 (spectral theorem), VIII.5 (functional calculus) -/

private lemma resolvent_function_norm (s : ℝ) :
    ‖(1 / ((s : ℂ) + Complex.I))‖ ≤ 1 := by
  have hne : (s : ℂ) + Complex.I ≠ 0 := by
    intro h
    have him : ((s : ℂ) + Complex.I).im = 0 := by rw [h]; simp
    simp [Complex.add_im, Complex.ofReal_im, Complex.I_im] at him
  rw [norm_div, norm_one]
  rw [div_le_one (norm_pos_iff.mpr hne)]
  -- Need: 1 ≤ ‖(s : ℂ) + i‖
  -- ‖(s : ℂ) + i‖² = s² + 1 ≥ 1
  have h1 : ‖(s : ℂ) + Complex.I‖ ^ 2 = s ^ 2 + 1 := by
    have hns : Complex.normSq ((s : ℂ) + Complex.I) = s ^ 2 + 1 := by
      rw [Complex.normSq_apply]
      simp [Complex.add_re, Complex.add_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [← Complex.normSq_eq_norm_sq]; exact hns
  by_contra h
  push_neg at h
  have h2 : ‖(s : ℂ) + Complex.I‖ ^ 2 < 1 ^ 2 :=
    sq_lt_sq' (by linarith [norm_nonneg ((s : ℂ) + Complex.I)]) h
  linarith [sq_nonneg s]

private lemma resolvent_function_measurable :
    Measurable (fun s : ℝ => 1 / ((s : ℂ) + Complex.I)) :=
  measurable_const.div (Complex.continuous_ofReal.measurable.add measurable_const)

private lemma resolvent_function_integrable (P : SpectralMeasure H) (z : H) :
    MeasureTheory.Integrable (fun s : ℝ => 1 / ((s : ℂ) + Complex.I))
      (P.diagonalMeasure z) := by
  haveI := P.diagonalMeasure_isFiniteMeasure z
  exact (MeasureTheory.integrable_const (1 : ℂ)).mono
    resolvent_function_measurable.aestronglyMeasurable
    (by filter_upwards with s; simp only [norm_one]; exact resolvent_function_norm s)

private theorem spectralIntegral_add (P : SpectralMeasure H) (f g : ℝ → ℂ)
    (hf_int : ∀ z : H, MeasureTheory.Integrable f (P.diagonalMeasure z))
    (hg_int : ∀ z : H, MeasureTheory.Integrable g (P.diagonalMeasure z))
    (x y : H) :
    P.spectralIntegral (fun t => f t + g t) x y =
      P.spectralIntegral f x y + P.spectralIntegral g x y := by
  unfold SpectralMeasure.spectralIntegral
  rw [MeasureTheory.integral_add (hf_int _) (hg_int _),
      MeasureTheory.integral_add (hf_int _) (hg_int _),
      MeasureTheory.integral_add (hf_int _) (hg_int _),
      MeasureTheory.integral_add (hf_int _) (hg_int _)]
  ring

private theorem spectralIntegral_smul (P : SpectralMeasure H) (c : ℂ) (f : ℝ → ℂ)
    (_hf_int : ∀ z : H, MeasureTheory.Integrable f (P.diagonalMeasure z))
    (x y : H) :
    P.spectralIntegral (fun t => c * f t) x y = c * P.spectralIntegral f x y := by
  unfold SpectralMeasure.spectralIntegral
  have hmul : ∀ z, ∫ t, c * f t ∂(P.diagonalMeasure z) =
      c * ∫ t, f t ∂(P.diagonalMeasure z) := by
    intro z
    simpa [smul_eq_mul] using
      (MeasureTheory.integral_smul c f (μ := P.diagonalMeasure z))
  rw [hmul, hmul, hmul, hmul]
  ring

private lemma functionalCalculus_const_one_eq_id (P : SpectralMeasure H) :
    functionalCalculus P (fun _ : ℝ => (1 : ℂ))
      (by
        intro z
        haveI := P.diagonalMeasure_isFiniteMeasure z
        simp)
      ⟨1, zero_le_one, by intro s; simp⟩ = 1 := by
  simpa [P.univ] using
    (functionalCalculus_indicator P Set.univ MeasurableSet.univ
      (by
        intro z
        haveI := P.diagonalMeasure_isFiniteMeasure z
        simp)
      ⟨1, zero_le_one, by intro t; simp⟩)

private def cayley_function (s : ℝ) : ℂ :=
  (cayleyToCircle s : ℂ)

private def cayley_re (s : ℝ) : ℂ :=
  ((circleRe (cayleyToCircle s) : ℝ) : ℂ)

private def cayley_im (s : ℝ) : ℂ :=
  ((circleIm (cayleyToCircle s) : ℝ) : ℂ)

private lemma cayley_function_measurable :
    Measurable cayley_function := by
  simpa [cayley_function] using
    (continuous_subtype_val.comp cayleyToCircle_continuous).measurable

private lemma cayley_re_measurable :
    Measurable cayley_re := by
  simpa [cayley_re] using
    (Complex.continuous_ofReal.measurable.comp
      ((ContinuousMap.continuous circleRe).measurable.comp
        cayleyToCircle_continuous.measurable))

private lemma cayley_im_measurable :
    Measurable cayley_im := by
  simpa [cayley_im] using
    (Complex.continuous_ofReal.measurable.comp
      ((ContinuousMap.continuous circleIm).measurable.comp
        cayleyToCircle_continuous.measurable))

private lemma cayley_function_norm (s : ℝ) :
    ‖cayley_function s‖ ≤ 1 := by
  have hs : ‖(cayleyToCircle s : ℂ)‖ = 1 := Circle.norm_coe (cayleyToCircle s)
  simp [cayley_function]

private lemma cayley_re_norm (s : ℝ) :
    ‖cayley_re s‖ ≤ 1 := by
  have hs := circleRe_abs_le_one (cayleyToCircle s)
  simpa [cayley_re, Complex.norm_real, Real.norm_eq_abs] using hs

private lemma cayley_im_norm (s : ℝ) :
    ‖cayley_im s‖ ≤ 1 := by
  have hs := circleIm_abs_le_one (cayleyToCircle s)
  simpa [cayley_im, Complex.norm_real, Real.norm_eq_abs] using hs

private lemma cayley_function_integrable (P : SpectralMeasure H) (z : H) :
    MeasureTheory.Integrable cayley_function (P.diagonalMeasure z) := by
  haveI := P.diagonalMeasure_isFiniteMeasure z
  exact (MeasureTheory.integrable_const (1 : ℂ)).mono
    cayley_function_measurable.aestronglyMeasurable
    (by
      filter_upwards with s
      simp only [norm_one]
      exact cayley_function_norm s)

private lemma cayley_re_integrable (P : SpectralMeasure H) (z : H) :
    MeasureTheory.Integrable cayley_re (P.diagonalMeasure z) := by
  haveI := P.diagonalMeasure_isFiniteMeasure z
  exact (MeasureTheory.integrable_const (1 : ℂ)).mono
    cayley_re_measurable.aestronglyMeasurable
    (by
      filter_upwards with s
      simp only [norm_one]
      exact cayley_re_norm s)

private lemma cayley_im_integrable (P : SpectralMeasure H) (z : H) :
    MeasureTheory.Integrable cayley_im (P.diagonalMeasure z) := by
  haveI := P.diagonalMeasure_isFiniteMeasure z
  exact (MeasureTheory.integrable_const (1 : ℂ)).mono
    cayley_im_measurable.aestronglyMeasurable
    (by
      filter_upwards with s
      simp only [norm_one]
      exact cayley_im_norm s)

private lemma cayley_function_decomp :
    cayley_function = fun s => cayley_re s + Complex.I * cayley_im s := by
  funext s
  simpa [cayley_function, cayley_re, cayley_im] using
    circle_id_eq_re_add_i_im (cayleyToCircle s)

private lemma one_sub_cayley_function (s : ℝ) :
    (1 : ℂ) - cayley_function s =
      (((2 : ℂ) * Complex.I) * (1 / ((s : ℂ) + Complex.I))) := by
  have hne : (s : ℂ) + Complex.I ≠ 0 := by
    intro h
    have him : ((s : ℂ) + Complex.I).im = 0 := by rw [h]; simp
    simp [Complex.add_im, Complex.ofReal_im, Complex.I_im] at him
  simp [cayley_function, cayleyToCircle_coe, cayleyMap]
  field_simp [hne]
  ring

private lemma diagonalMeasure_map_cayley (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (z : H) :
    MeasureTheory.Measure.map cayleyToCircle ((T.spectralMeasure hT hsa).diagonalMeasure z) =
      spectralMeasureDiagonal (T.spectralCayley hT hsa).U
        (cayley_mem_unitary T hT hsa (T.spectralCayley hT hsa)) z := by
  let P := T.spectralMeasure hT hsa
  let C := T.spectralCayley hT hsa
  let U := C.U
  let hU := cayley_mem_unitary T hT hsa C
  apply MeasureTheory.Measure.ext
  intro A hA
  rw [MeasureTheory.Measure.map_apply cayleyToCircle_continuous.measurable hA]
  have hpre_meas : MeasurableSet (cayleyToCircle ⁻¹' A) :=
    cayleyToCircle_continuous.measurable hA
  have hpre_eq_toReal : ((P.diagonalMeasure z) (cayleyToCircle ⁻¹' A)).toReal =
      ((spectralMeasureDiagonal U hU z) (cayleyToCircle '' (cayleyToCircle ⁻¹' A))).toReal := by
    rw [P.diagonalMeasure_apply z _ hpre_meas]
    rw [UnboundedOperator.spectralMeasure_eq_RMK T hT hsa (cayleyToCircle ⁻¹' A) hpre_meas]
    rw [spectralMeasureFromRMK]
    have hinner : @inner ℂ H _ z
        (spectralProjectionOfUnitary U hU (cayleyToCircle '' (cayleyToCircle ⁻¹' A))
          (cayleyToCircle_measurableSet_image (cayleyToCircle ⁻¹' A) hpre_meas) z) =
        spectralMeasurePolarized U hU z z (cayleyToCircle '' (cayleyToCircle ⁻¹' A))
          (cayleyToCircle_measurableSet_image (cayleyToCircle ⁻¹' A) hpre_meas) := by
      unfold spectralProjectionOfUnitary
      rw [← sesquilinearToOperator_inner]
    rw [hinner, spectralMeasurePolarized_diag U hU z _ _]
    simp
  haveI := P.diagonalMeasure_isFiniteMeasure z
  have hlt1 := MeasureTheory.measure_lt_top (P.diagonalMeasure z) (cayleyToCircle ⁻¹' A)
  haveI := spectralMeasureDiagonal_isFiniteMeasure U hU z
  have hlt2 := MeasureTheory.measure_lt_top (spectralMeasureDiagonal U hU z)
    (cayleyToCircle '' (cayleyToCircle ⁻¹' A))
  have hpre_eq : (P.diagonalMeasure z) (cayleyToCircle ⁻¹' A) =
      (spectralMeasureDiagonal U hU z) (cayleyToCircle '' (cayleyToCircle ⁻¹' A)) := by
    exact (ENNReal.toReal_eq_toReal_iff' hlt1.ne hlt2.ne).mp hpre_eq_toReal
  rw [hpre_eq]
  have h_img : cayleyToCircle '' (cayleyToCircle ⁻¹' A) = A ∩ Set.range cayleyToCircle :=
    Set.image_preimage_eq_inter_range
  rw [h_img]
  have hrange : Set.range cayleyToCircle = {w : Circle | w ≠ 1} := cayleyToCircle_range
  rw [hrange]
  have hdecomp : A = (A ∩ {w : Circle | w ≠ 1}) ∪ (A ∩ ({1} : Set Circle)) := by
    ext w
    by_cases hw : w = 1 <;> simp [hw]
  have hdisj : Disjoint (A ∩ {w : Circle | w ≠ 1}) (A ∩ ({1} : Set Circle)) := by
    refine Set.disjoint_left.mpr ?_
    intro w hw1 hw2
    exact hw1.2 hw2.2
  have hA1_meas : MeasurableSet (A ∩ ({1} : Set Circle)) :=
    hA.inter (measurableSet_singleton 1)
  have hP1 : spectralProjectionOfUnitary U hU {1} (measurableSet_singleton 1) = 0 :=
    spectralProjection_singleton_one_eq_zero T hT hsa C
  have hdiag_zero_toReal : ((spectralMeasureDiagonal U hU z) {1}).toReal = 0 := by
    have hnorm := spectralProjection_norm_sq U hU {1} (measurableSet_singleton 1) z
    rw [hP1, ContinuousLinearMap.zero_apply, norm_zero, zero_pow two_ne_zero] at hnorm
    exact hnorm.symm
  have hdiag_zero : (spectralMeasureDiagonal U hU z) {1} = 0 := by
    have hzero_or_top := (ENNReal.toReal_eq_zero_iff _).mp hdiag_zero_toReal
    cases hzero_or_top with
    | inl hzero => exact hzero
    | inr htop =>
        exfalso
        haveI := spectralMeasureDiagonal_isFiniteMeasure U hU z
        exact (MeasureTheory.measure_lt_top (spectralMeasureDiagonal U hU z) {1}).ne htop
  have hμ1 : (spectralMeasureDiagonal U hU z) (A ∩ ({1} : Set Circle)) = 0 := by
    apply MeasureTheory.Measure.mono_null (by intro w hw; exact hw.2)
    exact hdiag_zero
  conv_rhs => rw [hdecomp]
  rw [MeasureTheory.measure_union hdisj hA1_meas, hμ1, add_zero]

private lemma inner_cfcOfCircleReal_re_eq_functionalCalculus
    (T : UnboundedOperator H) (hT : T.IsDenselyDefined) (hsa : T.IsSelfAdjoint hT)
    (x y : H) :
    let P := T.spectralMeasure hT hsa
    let C := T.spectralCayley hT hsa
    let U := C.U
    let hU := cayley_mem_unitary T hT hsa C
    @inner ℂ H _ x (cfcOfCircleReal U hU circleRe y) =
      @inner ℂ H _ x
        (functionalCalculus P cayley_re (cayley_re_integrable P)
          ⟨1, zero_le_one, cayley_re_norm⟩ y) := by
  intro P C U hU
  rw [spectral_theorem T hT hsa cayley_re (cayley_re_integrable P)
    ⟨1, zero_le_one, cayley_re_norm⟩ x y]
  unfold SpectralMeasure.spectralIntegral
  have hsum : ∫ s, cayley_re s ∂(P.diagonalMeasure (x + y)) =
      ∫ w : Circle, ((circleRe w : ℝ) : ℂ) ∂(spectralMeasureDiagonal U hU (x + y)) := by
    rw [← diagonalMeasure_map_cayley T hT hsa (x + y)]
    simpa [cayley_re] using
      (MeasurableEmbedding.integral_map cayleyToCircle_measurableEmbedding
        (fun w : Circle => ((circleRe w : ℝ) : ℂ))
        (μ := P.diagonalMeasure (x + y))).symm
  have hdiff : ∫ s, cayley_re s ∂(P.diagonalMeasure (x - y)) =
      ∫ w : Circle, ((circleRe w : ℝ) : ℂ) ∂(spectralMeasureDiagonal U hU (x - y)) := by
    rw [← diagonalMeasure_map_cayley T hT hsa (x - y)]
    simpa [cayley_re] using
      (MeasurableEmbedding.integral_map cayleyToCircle_measurableEmbedding
        (fun w : Circle => ((circleRe w : ℝ) : ℂ))
        (μ := P.diagonalMeasure (x - y))).symm
  have hisum : ∫ s, cayley_re s ∂(P.diagonalMeasure (x + Complex.I • y)) =
      ∫ w : Circle, ((circleRe w : ℝ) : ℂ) ∂(spectralMeasureDiagonal U hU (x + Complex.I • y)) := by
    rw [← diagonalMeasure_map_cayley T hT hsa (x + Complex.I • y)]
    simpa [cayley_re] using
      (MeasurableEmbedding.integral_map cayleyToCircle_measurableEmbedding
        (fun w : Circle => ((circleRe w : ℝ) : ℂ))
        (μ := P.diagonalMeasure (x + Complex.I • y))).symm
  have hidiff : ∫ s, cayley_re s ∂(P.diagonalMeasure (x - Complex.I • y)) =
      ∫ w : Circle, ((circleRe w : ℝ) : ℂ) ∂(spectralMeasureDiagonal U hU (x - Complex.I • y)) := by
    rw [← diagonalMeasure_map_cayley T hT hsa (x - Complex.I • y)]
    simpa [cayley_re] using
      (MeasurableEmbedding.integral_map cayleyToCircle_measurableEmbedding
        (fun w : Circle => ((circleRe w : ℝ) : ℂ))
        (μ := P.diagonalMeasure (x - Complex.I • y))).symm
  rw [hsum, hdiff, hisum, hidiff]
  have h1 : (∫ w : Circle, ((circleRe w : ℝ) : ℂ) ∂(spectralMeasureDiagonal U hU (x + y))) =
      ((∫ w : Circle, circleRe w ∂(spectralMeasureDiagonal U hU (x + y)) : ℝ) : ℂ) :=
    integral_ofReal
  have h2 : (∫ w : Circle, ((circleRe w : ℝ) : ℂ) ∂(spectralMeasureDiagonal U hU (x - y))) =
      ((∫ w : Circle, circleRe w ∂(spectralMeasureDiagonal U hU (x - y)) : ℝ) : ℂ) :=
    integral_ofReal
  have h3 :
      (∫ w : Circle, ((circleRe w : ℝ) : ℂ) ∂(spectralMeasureDiagonal U hU (x + Complex.I • y))) =
      ((∫ w : Circle, circleRe w ∂(spectralMeasureDiagonal U hU (x + Complex.I • y)) : ℝ) : ℂ) :=
    integral_ofReal
  have h4 :
      (∫ w : Circle, ((circleRe w : ℝ) : ℂ) ∂(spectralMeasureDiagonal U hU (x - Complex.I • y))) =
      ((∫ w : Circle, circleRe w ∂(spectralMeasureDiagonal U hU (x - Complex.I • y)) : ℝ) : ℂ) :=
    integral_ofReal
  rw [h1, h2, h3, h4]
  symm
  simpa [toCc_apply] using
    (spectralMeasurePolarized_integral U hU x y (toCc circleRe))

private lemma inner_cfcOfCircleReal_im_eq_functionalCalculus
    (T : UnboundedOperator H) (hT : T.IsDenselyDefined) (hsa : T.IsSelfAdjoint hT)
    (x y : H) :
    let P := T.spectralMeasure hT hsa
    let C := T.spectralCayley hT hsa
    let U := C.U
    let hU := cayley_mem_unitary T hT hsa C
    @inner ℂ H _ x (cfcOfCircleReal U hU circleIm y) =
      @inner ℂ H _ x
        (functionalCalculus P cayley_im (cayley_im_integrable P)
          ⟨1, zero_le_one, cayley_im_norm⟩ y) := by
  intro P C U hU
  rw [spectral_theorem T hT hsa cayley_im (cayley_im_integrable P)
    ⟨1, zero_le_one, cayley_im_norm⟩ x y]
  unfold SpectralMeasure.spectralIntegral
  have hsum : ∫ s, cayley_im s ∂(P.diagonalMeasure (x + y)) =
      ∫ w : Circle, ((circleIm w : ℝ) : ℂ) ∂(spectralMeasureDiagonal U hU (x + y)) := by
    rw [← diagonalMeasure_map_cayley T hT hsa (x + y)]
    simpa [cayley_im] using
      (MeasurableEmbedding.integral_map cayleyToCircle_measurableEmbedding
        (fun w : Circle => ((circleIm w : ℝ) : ℂ))
        (μ := P.diagonalMeasure (x + y))).symm
  have hdiff : ∫ s, cayley_im s ∂(P.diagonalMeasure (x - y)) =
      ∫ w : Circle, ((circleIm w : ℝ) : ℂ) ∂(spectralMeasureDiagonal U hU (x - y)) := by
    rw [← diagonalMeasure_map_cayley T hT hsa (x - y)]
    simpa [cayley_im] using
      (MeasurableEmbedding.integral_map cayleyToCircle_measurableEmbedding
        (fun w : Circle => ((circleIm w : ℝ) : ℂ))
        (μ := P.diagonalMeasure (x - y))).symm
  have hisum : ∫ s, cayley_im s ∂(P.diagonalMeasure (x + Complex.I • y)) =
      ∫ w : Circle, ((circleIm w : ℝ) : ℂ) ∂(spectralMeasureDiagonal U hU (x + Complex.I • y)) := by
    rw [← diagonalMeasure_map_cayley T hT hsa (x + Complex.I • y)]
    simpa [cayley_im] using
      (MeasurableEmbedding.integral_map cayleyToCircle_measurableEmbedding
        (fun w : Circle => ((circleIm w : ℝ) : ℂ))
        (μ := P.diagonalMeasure (x + Complex.I • y))).symm
  have hidiff : ∫ s, cayley_im s ∂(P.diagonalMeasure (x - Complex.I • y)) =
      ∫ w : Circle, ((circleIm w : ℝ) : ℂ) ∂(spectralMeasureDiagonal U hU (x - Complex.I • y)) := by
    rw [← diagonalMeasure_map_cayley T hT hsa (x - Complex.I • y)]
    simpa [cayley_im] using
      (MeasurableEmbedding.integral_map cayleyToCircle_measurableEmbedding
        (fun w : Circle => ((circleIm w : ℝ) : ℂ))
        (μ := P.diagonalMeasure (x - Complex.I • y))).symm
  rw [hsum, hdiff, hisum, hidiff]
  have h1 : (∫ w : Circle, ((circleIm w : ℝ) : ℂ) ∂(spectralMeasureDiagonal U hU (x + y))) =
      ((∫ w : Circle, circleIm w ∂(spectralMeasureDiagonal U hU (x + y)) : ℝ) : ℂ) :=
    integral_ofReal
  have h2 : (∫ w : Circle, ((circleIm w : ℝ) : ℂ) ∂(spectralMeasureDiagonal U hU (x - y))) =
      ((∫ w : Circle, circleIm w ∂(spectralMeasureDiagonal U hU (x - y)) : ℝ) : ℂ) :=
    integral_ofReal
  have h3 :
      (∫ w : Circle, ((circleIm w : ℝ) : ℂ) ∂(spectralMeasureDiagonal U hU (x + Complex.I • y))) =
      ((∫ w : Circle, circleIm w ∂(spectralMeasureDiagonal U hU (x + Complex.I • y)) : ℝ) : ℂ) :=
    integral_ofReal
  have h4 :
      (∫ w : Circle, ((circleIm w : ℝ) : ℂ) ∂(spectralMeasureDiagonal U hU (x - Complex.I • y))) =
      ((∫ w : Circle, circleIm w ∂(spectralMeasureDiagonal U hU (x - Complex.I • y)) : ℝ) : ℂ) :=
    integral_ofReal
  rw [h1, h2, h3, h4]
  symm
  simpa [toCc_apply] using
    (spectralMeasurePolarized_integral U hU x y (toCc circleIm))

private lemma cayley_eq_functionalCalculus (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) :
    let P := T.spectralMeasure hT hsa
    let C := T.spectralCayley hT hsa
    C.U = functionalCalculus P cayley_function (cayley_function_integrable P)
      ⟨1, zero_le_one, cayley_function_norm⟩ := by
  intro P C
  let U := C.U
  let hU := cayley_mem_unitary T hT hsa C
  ext y
  apply ext_inner_left ℂ
  intro x
  have hUdecomp : C.U = cfcOfCircleReal U hU circleRe + Complex.I • cfcOfCircleReal U hU circleIm := by
    simpa [U] using unitary_eq_cfcOfCircleReal_re_im U hU
  rw [hUdecomp]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, inner_add_right, inner_smul_right]
  rw [inner_cfcOfCircleReal_re_eq_functionalCalculus T hT hsa x y,
      inner_cfcOfCircleReal_im_eq_functionalCalculus T hT hsa x y]
  rw [spectral_theorem T hT hsa cayley_re (cayley_re_integrable P)
      ⟨1, zero_le_one, cayley_re_norm⟩ x y,
    spectral_theorem T hT hsa cayley_im (cayley_im_integrable P)
      ⟨1, zero_le_one, cayley_im_norm⟩ x y,
    spectral_theorem T hT hsa cayley_function (cayley_function_integrable P)
      ⟨1, zero_le_one, cayley_function_norm⟩ x y]
  rw [cayley_function_decomp]
  rw [spectralIntegral_add P cayley_re (fun s => Complex.I * cayley_im s)
      (cayley_re_integrable P)
      (by
        intro z
        exact (cayley_im_integrable P z).const_mul Complex.I) x y]
  rw [spectralIntegral_smul P Complex.I cayley_im (cayley_im_integrable P) x y]

private lemma scaled_resolvent_eq_functionalCalculus
    (T : UnboundedOperator H) (hT : T.IsDenselyDefined) (hsa : T.IsSelfAdjoint hT) :
    let P := T.spectralMeasure hT hsa
    let C := T.spectralCayley hT hsa
    (((2 : ℂ) * Complex.I) • C.resolvent_neg_i.inv) =
      functionalCalculus P (fun s : ℝ => ((2 : ℂ) * Complex.I) * (1 / ((s : ℂ) + Complex.I)))
        (by
          intro z
          exact (resolvent_function_integrable P z).const_mul (((2 : ℂ) * Complex.I)))
        ⟨2, by norm_num, by
        intro s
        have hs := resolvent_function_norm s
        have htwoi : ‖((2 : ℂ) * Complex.I)‖ = 2 := by norm_num
        calc ‖((2 : ℂ) * Complex.I) * (1 / ((s : ℂ) + Complex.I))‖
            = ‖((2 : ℂ) * Complex.I)‖ * ‖(1 / ((s : ℂ) + Complex.I))‖ := norm_mul _ _
          _ ≤ 2 * 1 := by
              rw [htwoi]
              nlinarith
          _ = 2 := by ring⟩ := by
  intro P C
  let U := C.U
  let hU := cayley_mem_unitary T hT hsa C
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [spectral_theorem T hT hsa
    (fun s : ℝ => ((2 : ℂ) * Complex.I) * (1 / ((s : ℂ) + Complex.I)))
    (by
      intro z
      exact (resolvent_function_integrable P z).const_mul (((2 : ℂ) * Complex.I)))
    ⟨2, by norm_num, by
      intro s
      have hs := resolvent_function_norm s
      have htwoi : ‖((2 : ℂ) * Complex.I)‖ = 2 := by norm_num
      calc ‖((2 : ℂ) * Complex.I) * (1 / ((s : ℂ) + Complex.I))‖
          = ‖((2 : ℂ) * Complex.I)‖ * ‖(1 / ((s : ℂ) + Complex.I))‖ := norm_mul _ _
        _ ≤ 2 * 1 := by
            rw [htwoi]
            nlinarith
        _ = 2 := by ring⟩ x y]
  have hRy : (((2 : ℂ) * Complex.I) • C.resolvent_neg_i.inv) y = y - U y := by
    have h := congrFun (congrArg DFunLike.coe C.cayley_formula) y
    apply eq_sub_iff_add_eq.mpr
    have h' : U y + ((((2 : ℂ) * Complex.I) • C.resolvent_neg_i.inv) y) = y :=
      eq_sub_iff_add_eq.mp h
    simpa [ContinuousLinearMap.smul_apply, add_comm, add_left_comm, add_assoc] using h'
  rw [hRy, inner_sub_right]
  have hone :
      @inner ℂ H _ x y =
        P.spectralIntegral (fun _ : ℝ => (1 : ℂ)) x y := by
    rw [← spectral_theorem T hT hsa (fun _ : ℝ => (1 : ℂ))
      (by
        intro z
        haveI := P.diagonalMeasure_isFiniteMeasure z
        simp)
      ⟨1, zero_le_one, by intro s; simp⟩ x y]
    rw [functionalCalculus_const_one_eq_id P, ContinuousLinearMap.one_apply]
  have hUfc :
      @inner ℂ H _ x (U y) =
        P.spectralIntegral cayley_function x y := by
    have hUeq :
        U = functionalCalculus P cayley_function (cayley_function_integrable P)
          ⟨1, zero_le_one, cayley_function_norm⟩ := by
      simpa [U] using cayley_eq_functionalCalculus T hT hsa
    rw [hUeq]
    exact spectral_theorem T hT hsa cayley_function (cayley_function_integrable P)
      ⟨1, zero_le_one, cayley_function_norm⟩ x y
  rw [hone, hUfc]
  have hpoint :
      (fun s : ℝ => (((2 : ℂ) * Complex.I) * (1 / ((s : ℂ) + Complex.I)))) =
      (fun s : ℝ => (1 : ℂ) - cayley_function s) := by
    funext s
    symm
    exact one_sub_cayley_function s
  rw [hpoint]
  have hsub :
      (fun s : ℝ => (1 : ℂ) - cayley_function s) =
      (fun s : ℝ => (1 : ℂ) + (-cayley_function s)) := by
    funext s
    simp [sub_eq_add_neg]
  rw [hsub]
  rw [spectralIntegral_add P (fun _ : ℝ => (1 : ℂ)) (fun s : ℝ => -cayley_function s)
      (by
        intro z
        haveI := P.diagonalMeasure_isFiniteMeasure z
        simp)
      (by
        intro z
        simpa using (cayley_function_integrable P z).const_mul (-1)) x y]
  have hneg :
      (fun s : ℝ => -cayley_function s) = (fun s : ℝ => (-1 : ℂ) * cayley_function s) := by
    funext s
    ring
  rw [hneg]
  rw [spectralIntegral_smul P (-1 : ℂ) cayley_function (cayley_function_integrable P) x y]
  ring

/-- **T-P Connection**: The resolvent (T+i)⁻¹ equals the functional calculus
    of the function λ ↦ 1/(λ+i) with respect to the spectral measure P.

    This is the key bridge between the abstract operator domain and
    spectral integrals. All downstream results (`spectralTruncation_tendsto`,
    `mem_domain_iff_square_integrable`, etc.) are proved from this.

    **Proof:** Transport the diagonal measures of `P` through `cayleyToCircle`,
    identify the pulled-back real and imaginary parts with the Circle CFC for
    the Cayley unitary, reconstruct `C.U = fc(P, φ)`, and then solve the Cayley
    formula `C.U = 1 - 2i • (T + i)⁻¹` for the resolvent. -/
theorem resolvent_eq_functionalCalculus (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) :
    let P := T.spectralMeasure hT hsa
    let C := T.spectralCayley hT hsa
    C.resolvent_neg_i.inv =
      functionalCalculus P (fun s : ℝ => 1 / ((s : ℂ) + Complex.I))
        (resolvent_function_integrable P) ⟨1, zero_le_one, resolvent_function_norm⟩ := by
  intro P C
  ext y
  apply ext_inner_left ℂ
  intro x
  let g : ℝ → ℂ := fun s => 1 / ((s : ℂ) + Complex.I)
  let scaledG : ℝ → ℂ := fun s => ((2 : ℂ) * Complex.I) * g s
  let hscaled_int : ∀ z : H, MeasureTheory.Integrable scaledG (P.diagonalMeasure z) := by
    intro z
    exact (resolvent_function_integrable P z).const_mul (((2 : ℂ) * Complex.I))
  let hscaled_bound :
      ∃ Cbound ≥ 0, ∀ s, ‖scaledG s‖ ≤ Cbound := by
    refine ⟨2, by norm_num, ?_⟩
    intro s
    have hs := resolvent_function_norm s
    have htwoi : ‖((2 : ℂ) * Complex.I)‖ = 2 := by norm_num
    calc
      ‖scaledG s‖ = ‖((2 : ℂ) * Complex.I) * g s‖ := by rfl
      _ = ‖((2 : ℂ) * Complex.I)‖ * ‖g s‖ := norm_mul _ _
      _ ≤ 2 * 1 := by
          rw [htwoi]
          nlinarith
      _ = 2 := by ring
  have hscaled := congrFun (congrArg DFunLike.coe (scaled_resolvent_eq_functionalCalculus T hT hsa)) y
  have hleft :
      @inner ℂ H _ x ((((2 : ℂ) * Complex.I) • C.resolvent_neg_i.inv) y) =
        (((2 : ℂ) * Complex.I) * @inner ℂ H _ x (C.resolvent_neg_i.inv y)) := by
    simp [ContinuousLinearMap.smul_apply]
  have hright :
      @inner ℂ H _ x
        ((functionalCalculus P
          scaledG hscaled_int hscaled_bound) y) =
        (((2 : ℂ) * Complex.I) *
          @inner ℂ H _ x
            ((functionalCalculus P g
              (resolvent_function_integrable P)
              ⟨1, zero_le_one, resolvent_function_norm⟩) y)) := by
    calc
      @inner ℂ H _ x ((functionalCalculus P scaledG hscaled_int hscaled_bound) y)
          = P.spectralIntegral scaledG x y := by
              exact spectral_theorem T hT hsa scaledG hscaled_int hscaled_bound x y
      _ = (((2 : ℂ) * Complex.I) * P.spectralIntegral g x y) := by
            rw [spectralIntegral_smul P (((2 : ℂ) * Complex.I)) g
              (resolvent_function_integrable P) x y]
      _ = (((2 : ℂ) * Complex.I) *
            @inner ℂ H _ x
              ((functionalCalculus P g
                (resolvent_function_integrable P)
                ⟨1, zero_le_one, resolvent_function_norm⟩) y)) := by
            rw [← spectral_theorem T hT hsa g
              (resolvent_function_integrable P) ⟨1, zero_le_one, resolvent_function_norm⟩ x y]
  have htwoi_ne : ((2 : ℂ) * Complex.I) ≠ 0 := by norm_num [Complex.I_ne_zero]
  have hscaled_eq :
      (((2 : ℂ) * Complex.I) * @inner ℂ H _ x (C.resolvent_neg_i.inv y)) =
        (((2 : ℂ) * Complex.I) *
          @inner ℂ H _ x
            ((functionalCalculus P g
              (resolvent_function_integrable P)
              ⟨1, zero_le_one, resolvent_function_norm⟩) y)) := by
    calc
      (((2 : ℂ) * Complex.I) * @inner ℂ H _ x (C.resolvent_neg_i.inv y))
          = @inner ℂ H _ x ((((2 : ℂ) * Complex.I) • C.resolvent_neg_i.inv) y) := hleft.symm
      _ = @inner ℂ H _ x
            ((functionalCalculus P scaledG hscaled_int hscaled_bound) y) := by
            exact congrArg (@inner ℂ H _ x) hscaled
      _ = (((2 : ℂ) * Complex.I) *
            @inner ℂ H _ x
              ((functionalCalculus P g
                (resolvent_function_integrable P)
                ⟨1, zero_le_one, resolvent_function_norm⟩) y)) := hright
  exact mul_left_cancel₀ htwoi_ne hscaled_eq

/-- Helper: `s² / (s² + 1) ≤ 1` for all real `s`. -/
private lemma sq_div_sq_add_one_le_one (s : ℝ) : s ^ 2 / (s ^ 2 + 1) ≤ 1 := by
  rw [div_le_one (by positivity)]
  linarith [sq_nonneg s]

/-- Helper: `‖s² · (1/(s+i))²‖ = s² / (s² + 1) ≤ 1`.
    This is the key pointwise bound for the forward direction. -/
private lemma norm_sq_times_resolvent_sq_le_one (s : ℝ) :
    ‖((s : ℂ) ^ 2) * (1 / ((s : ℂ) + Complex.I)) ^ 2‖ ≤ 1 := by
  have hne : (s : ℂ) + Complex.I ≠ 0 := by
    intro h
    have him : ((s : ℂ) + Complex.I).im = 0 := by rw [h]; simp
    simp [Complex.add_im, Complex.ofReal_im, Complex.I_im] at him
  rw [norm_mul]
  -- ‖(s : ℂ)^2‖ = s^2
  have hs2 : ‖((s : ℂ) ^ 2)‖ = s ^ 2 := by
    rw [show (↑s : ℂ) ^ 2 = ↑(s ^ 2) from by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  -- ‖(1/(s+i))^2‖ = 1/(s^2+1)
  have hg2 : ‖(1 / ((s : ℂ) + Complex.I)) ^ 2‖ = 1 / (s ^ 2 + 1) := by
    rw [norm_pow, norm_div, norm_one, div_pow, one_pow, one_div]
    rw [← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_apply]
    simp [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]
    ring
  rw [hs2, hg2]
  rw [show s ^ 2 * (1 / (s ^ 2 + 1)) = s ^ 2 / (s ^ 2 + 1) from by ring]
  exact sq_div_sq_add_one_le_one s

/-- Helper: the function `s ↦ s² · |1/(s+i)|²` is integrable against any
    diagonal spectral measure (it's bounded by 1 on a finite measure). -/
private lemma sq_resolvent_sq_integrable (P : SpectralMeasure H) (z : H) :
    MeasureTheory.Integrable
      (fun s : ℝ => ((s : ℂ) ^ 2) * (1 / ((s : ℂ) + Complex.I)) ^ 2)
      (P.diagonalMeasure z) := by
  haveI := P.diagonalMeasure_isFiniteMeasure z
  have hf_meas : Measurable
      (fun s : ℝ => ((s : ℂ) ^ 2) * (1 / ((s : ℂ) + Complex.I)) ^ 2) :=
    (Complex.continuous_ofReal.measurable.pow_const 2).mul
      ((measurable_const.div (Complex.continuous_ofReal.measurable.add measurable_const)).pow_const 2)
  exact (MeasureTheory.integrable_const (1 : ℂ)).mono
    hf_meas.aestronglyMeasurable
    (Eventually.of_forall fun s => by
      simp only [norm_one]; exact norm_sq_times_resolvent_sq_le_one s)

/-- Forward direction helper: if `x = fc(g)(y)` where `g(s) = 1/(s+i)`, then
    `∫ s² dμ_x` is finite.

    **Proof:** For any bounded test function `h`, we have (by norm-squared identity):
    `‖fc(h)(fc(g)(y))‖² = ‖fc(h·g)(y)‖² = ∫ |h·g|² dμ_y`.

    Taking `h(s) = s·χ_{[-n,n]}(s)`, we get `|h·g|² = s²χ/(s²+1) ≤ 1`, so
    `‖T_n x‖² = ∫ s²·χ dμ_x ≤ ∫ 1 dμ_y = ‖y‖²`.

    The truncated integrals ∫ s²·χ_{[-n,n]} dμ_x are uniformly bounded by ‖y‖²,
    and increase monotonically to ∫ s² dμ_x. By monotone convergence, the
    full integral is finite.

    Proved via the Bochner-to-lintegral conversion and monotone convergence.
    The key mathematical identity (norm_sq ≤ finite bound) is established above.

    References: Reed-Simon VIII.4, Rudin FA 13.24 -/
private lemma square_integrable_of_resolvent_preimage (T : UnboundedOperator H)
    (hT : T.IsDenselyDefined) (hsa : T.IsSelfAdjoint hT) (x y : H)
    (hxy : x = (T.spectralCayley hT hsa).resolvent_neg_i.inv y) :
    MeasureTheory.Integrable (fun s : ℝ => ((s : ℂ) ^ 2))
      ((T.spectralMeasure hT hsa).diagonalMeasure x) := by
  set P := T.spectralMeasure hT hsa; set C := T.spectralCayley hT hsa; set R := C.resolvent_neg_i
  set μ := P.diagonalMeasure x
  haveI : MeasureTheory.IsFiniteMeasure μ := P.diagonalMeasure_isFiniteMeasure x
  have hf_meas : Measurable (fun s : ℝ => ((s : ℂ) ^ 2)) :=
    Complex.continuous_ofReal.measurable.pow_const 2
  have hR_eq := resolvent_eq_functionalCalculus T hT hsa
  let g : ℝ → ℂ := fun s => 1 / ((s : ℂ) + Complex.I)
  let f_n : ℕ → ℝ → ℂ := fun n s =>
    (↑s : ℂ) * Set.indicator (Set.Icc (-(n : ℝ)) n) (fun _ => (1 : ℂ)) s
  let h_n : ℕ → ℝ → ℂ := fun n s => f_n n s * g s
  have hne : ∀ s : ℝ, (s : ℂ) + Complex.I ≠ 0 := by
    intro s heq; have : ((s : ℂ) + Complex.I).im = 0 := by rw [heq]; simp
    simp [Complex.add_im, Complex.ofReal_im, Complex.I_im] at this
  have h_norm_s_le : ∀ s : ℝ, ‖(s : ℂ)‖ ≤ ‖(s : ℂ) + Complex.I‖ := by
    intro s
    have h1 : ‖(s : ℂ) + Complex.I‖ ^ 2 = s ^ 2 + 1 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im]; ring
    have h2 : ‖(s : ℂ)‖ ^ 2 = s ^ 2 := by rw [Complex.norm_real]; exact sq_abs s
    by_contra hlt; push_neg at hlt
    linarith [sq_lt_sq' (by linarith [norm_nonneg ((s : ℂ) + Complex.I)]) hlt]
  have h_hn_bound : ∀ n (s : ℝ), ‖h_n n s‖ ≤ 1 := by
    intro n s; simp only [h_n, f_n, g]
    by_cases hs : s ∈ Set.Icc (-(n : ℝ)) n
    · rw [Set.indicator_of_mem hs, mul_one,
          show (↑s : ℂ) * (1 / ((↑s : ℂ) + Complex.I)) = (↑s : ℂ) / ((↑s : ℂ) + Complex.I)
            from by ring, norm_div, div_le_one (norm_pos_iff.mpr (hne s))]
      exact h_norm_s_le s
    · simp [hs]
  have h_hn_meas : ∀ n, Measurable (h_n n) := by
    intro n; exact ((Complex.continuous_ofReal.measurable).mul
      (measurable_const.indicator measurableSet_Icc)).mul
      (measurable_const.div (Complex.continuous_ofReal.measurable.add measurable_const))
  have h_hn_int : ∀ n (z : H), MeasureTheory.Integrable (h_n n) (P.diagonalMeasure z) := by
    intro n z; haveI := P.diagonalMeasure_isFiniteMeasure z
    exact (MeasureTheory.integrable_const (1 : ℂ)).mono (h_hn_meas n).aestronglyMeasurable
      (Eventually.of_forall fun s => by simp only [norm_one]; exact h_hn_bound n s)
  have hfn_int : ∀ n (z : H), MeasureTheory.Integrable (f_n n) (P.diagonalMeasure z) := by
    intro n z; haveI := P.diagonalMeasure_isFiniteMeasure z
    exact (MeasureTheory.integrable_const ((n : ℂ))).mono
      ((Complex.continuous_ofReal.measurable).mul
        (measurable_const.indicator measurableSet_Icc)).aestronglyMeasurable
      (by filter_upwards with s; simp only [f_n, Set.indicator_apply, Complex.norm_natCast]
          split_ifs with h
          · simp only [mul_one, Complex.norm_real]; exact abs_le.mpr (Set.mem_Icc.mp h)
          · simp)
  have hfn_bdd : ∀ n, ∃ M, 0 ≤ M ∧ ∀ t, ‖f_n n t‖ ≤ M := by
    intro n; refine ⟨n, Nat.cast_nonneg n, ?_⟩; intro s; simp only [f_n, Set.indicator_apply]
    split_ifs with h
    · simp only [mul_one, Complex.norm_real]; exact abs_le.mpr (Set.mem_Icc.mp h)
    · simp [Nat.cast_nonneg]
  -- Key: ‖T_n x‖ ≤ ‖y‖ via T_n x = fc(h_n n)(y) and operator norm bound
  have h_trunc_bound : ∀ n, ‖spectralTruncation T hT hsa n x‖ ≤ ‖y‖ := by
    intro n
    have hstepA : spectralTruncation T hT hsa n x =
        functionalCalculus P (h_n n) (h_hn_int n) ⟨1, zero_le_one, h_hn_bound n⟩ y := by
      conv_lhs => rw [show x = R.inv y from hxy]
      have hR_apply :
          R.inv y = functionalCalculus P g (resolvent_function_integrable P)
            ⟨1, zero_le_one, resolvent_function_norm⟩ y := by
        simpa [R, g] using congrFun (congrArg DFunLike.coe hR_eq) y
      rw [hR_apply]
      have hfn_meas : Measurable (f_n n) :=
        (Complex.continuous_ofReal.measurable).mul
          (measurable_const.indicator measurableSet_Icc)
      have hfng_eq : f_n n * g = h_n n := by
        ext s
        simp only [Pi.mul_apply, h_n]
      have hmul := functionalCalculus_mul P (f_n n) g (hfn_int n) (hfn_bdd n)
        (resolvent_function_integrable P) ⟨1, zero_le_one, resolvent_function_norm⟩
        (by rw [hfng_eq]; exact h_hn_int n)
        (by rw [hfng_eq]; exact ⟨1, zero_le_one, h_hn_bound n⟩)
        resolvent_function_measurable
      rw [show spectralTruncation T hT hsa n
        = functionalCalculus P (f_n n) (hfn_int n) (hfn_bdd n) from rfl]
      rw [← ContinuousLinearMap.comp_apply, ← hmul]
      exact congrFun (congrArg DFunLike.coe (functionalCalculus_congr' P hfng_eq _ _ _ _)) y
    rw [hstepA]
    calc
      ‖functionalCalculus P (h_n n) (h_hn_int n) ⟨1, zero_le_one, h_hn_bound n⟩ y‖
          ≤ ‖functionalCalculus P (h_n n) (h_hn_int n) ⟨1, zero_le_one, h_hn_bound n⟩‖ * ‖y‖ :=
            ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖y‖ := by
          gcongr
          exact functionalCalculus_opNorm_le P (h_n n) (h_hn_int n)
            ⟨1, zero_le_one, h_hn_bound n⟩ (h_hn_meas n) 1 zero_le_one (h_hn_bound n)
      _ = ‖y‖ := by ring
  -- Step 1: ‖T_n x‖² = Re(∫ s²·χ_{[-n,n]} dμ_x)  (from spectralTruncation_norm_sq)
  have h_norm_sq_eq : ∀ (n : ℕ), ‖spectralTruncation T hT hsa n x‖ ^ 2 =
      (∫ s, ((s : ℂ) ^ 2) * Set.indicator (Set.Icc (-(n : ℝ)) n) (fun _ => (1 : ℂ)) s ∂μ).re :=
    fun n => spectralTruncation_norm_sq T hT hsa n x
  -- Step 2: Re(∫ s²·χ dμ) ≤ ‖y‖²
  have h_int_bound : ∀ (n : ℕ), (∫ s, ((s : ℂ) ^ 2) * Set.indicator (Set.Icc (-(n : ℝ)) n) (fun _ => (1 : ℂ)) s ∂μ).re ≤ ‖y‖ ^ 2 := by
    intro n
    rw [← h_norm_sq_eq]
    exact sq_le_sq' (by linarith [norm_nonneg (spectralTruncation T hT hsa n x), h_trunc_bound n])
      (h_trunc_bound n)
  -- Step 3: Show integrability via integrable_of_tendsto (ℝ → ℝ route)
  let G : ℕ → ℝ → ℝ := fun n s => s ^ 2 * Set.indicator (Set.Icc (-(n : ℝ)) n) (fun _ => (1 : ℝ)) s
  have hGf : ∀ᵐ s ∂μ, Filter.Tendsto (fun n => G n s) Filter.atTop (nhds (s ^ 2)) := by
    filter_upwards with s
    have : ∀ᶠ n in Filter.atTop, G n s = s ^ 2 := by
      obtain ⟨N, hN⟩ := exists_nat_ge |s|
      filter_upwards [Filter.Ici_mem_atTop N] with n hn
      simp only [G]
      have hs_mem : s ∈ Set.Icc (-(n : ℝ)) n := by
        constructor <;> linarith [abs_nonneg s, neg_abs_le s, le_abs_self s,
                                   show (N : ℝ) ≤ (n : ℝ) from Nat.cast_le.mpr hn]
      rw [Set.indicator_of_mem hs_mem]; ring
    exact tendsto_nhds_of_eventually_eq this
  have hG_meas_strong : ∀ n, Measurable (G n) := by
    intro n
    exact (measurable_id.pow_const 2).mul (measurable_const.indicator measurableSet_Icc)
  have hG_meas : ∀ n, MeasureTheory.AEStronglyMeasurable (G n) μ := by
    intro n; exact (hG_meas_strong n).aestronglyMeasurable
  have hG_nonneg : ∀ n, 0 ≤ᵐ[μ] G n := by
    intro n; filter_upwards with s
    simp only [G, Set.indicator_apply]
    split_ifs <;> positivity
  have hG_norm_le : ∀ n (s : ℝ), ‖G n s‖ ≤ (n : ℝ) ^ 2 := by
    intro n s; simp only [G, Set.indicator_apply, Real.norm_eq_abs]
    split_ifs with h
    · rw [abs_of_nonneg (by positivity), mul_one]
      exact sq_le_sq' (by linarith [(Set.mem_Icc.mp h).1]) (by exact (Set.mem_Icc.mp h).2)
    · simp
  have hG_int : ∀ n, MeasureTheory.Integrable (G n) μ := by
    intro n
    exact (MeasureTheory.integrable_const ((n : ℝ) ^ 2)).mono (hG_meas n)
      (Eventually.of_forall fun s => by
        calc ‖G n s‖ ≤ (n : ℝ) ^ 2 := hG_norm_le n s
          _ = ‖((n : ℝ) ^ 2)‖ := by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)])
  -- Connect Re(∫ (s:ℂ)²·χ dμ) to ∫ s²·χ dμ (real Bochner)
  have h_sq_chi_norm : ∀ (n : ℕ) (s : ℝ),
      ‖((s : ℂ) ^ 2) * Set.indicator (Set.Icc (-(n : ℝ)) n) (fun _ => (1 : ℂ)) s‖ ≤ (n : ℝ) ^ 2 := by
    intro n s; simp only [Set.indicator_apply]
    split_ifs with h
    · rw [norm_mul, norm_one, mul_one,
          show (s : ℂ) ^ 2 = ((s ^ 2 : ℝ) : ℂ) from by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact sq_le_sq' (by linarith [(Set.mem_Icc.mp h).1]) (by exact (Set.mem_Icc.mp h).2)
    · simp
  have h_sq_chi_int : ∀ (n : ℕ), MeasureTheory.Integrable
      (fun s : ℝ => ((s : ℂ) ^ 2) * Set.indicator (Set.Icc (-(n : ℝ)) n) (fun _ => (1 : ℂ)) s) μ := by
    intro n
    have hmeas : Measurable (fun s : ℝ => ((s : ℂ) ^ 2) * Set.indicator (Set.Icc (-(n : ℝ)) n) (fun _ => (1 : ℂ)) s) :=
      (Complex.continuous_ofReal.measurable.pow_const 2).mul
        (measurable_const.indicator measurableSet_Icc)
    refine (MeasureTheory.integrable_const ((n : ℝ) ^ 2 : ℂ)).mono
      hmeas.aestronglyMeasurable
      (Eventually.of_forall fun s => ?_)
    calc ‖((s : ℂ) ^ 2) * Set.indicator (Set.Icc (-(n : ℝ)) n) (fun _ => (1 : ℂ)) s‖
        ≤ (n : ℝ) ^ 2 := h_sq_chi_norm n s
      _ = ‖((n : ℝ) ^ 2 : ℂ)‖ := by
          rw [show ((n : ℝ) ^ 2 : ℂ) = ((n ^ 2 : ℝ) : ℂ) from by push_cast; ring,
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h_re_eq_real : ∀ (n : ℕ), (∫ s, ((s : ℂ) ^ 2) * Set.indicator (Set.Icc (-(n : ℝ)) n) (fun _ => (1 : ℂ)) s ∂μ).re = ∫ s, G n s ∂μ := by
    intro n
    -- Re(∫ f dμ) = ∫ Re(f) dμ by integral_re
    -- Re((s:ℂ)² · χ) = s² · χ = G n s
    have h_eq_fns : (fun s : ℝ => RCLike.re (((s : ℂ) ^ 2) * Set.indicator (Set.Icc (-(n : ℝ)) n) (fun _ => (1 : ℂ)) s)) = G n := by
      ext s; simp only [G, Set.indicator_apply]
      split_ifs
      · simp only [mul_one]
        show ((s : ℂ) ^ 2).re = s ^ 2
        rw [show (s : ℂ) ^ 2 = ((s ^ 2 : ℝ) : ℂ) from by push_cast; ring]
        exact Complex.ofReal_re _
      · simp
    -- (∫ f dμ).re = ∫ (Re ∘ f) dμ = ∫ G n dμ  (by integral_re)
    rw [show (∫ s, ((s : ℂ) ^ 2) * Set.indicator (Set.Icc (-(n : ℝ)) n) (fun _ => (1 : ℂ)) s ∂μ).re = RCLike.re (∫ s, ((s : ℂ) ^ 2) * Set.indicator (Set.Icc (-(n : ℝ)) n) (fun _ => (1 : ℂ)) s ∂μ) from rfl,
        ← integral_re (h_sq_chi_int n), h_eq_fns]
  -- ∫ G n dμ ≤ ‖y‖²
  have h_real_bound : ∀ (n : ℕ), ∫ s, G n s ∂μ ≤ ‖y‖ ^ 2 := by
    intro n; rw [← h_re_eq_real]; exact h_int_bound n
  -- Convert Bochner integral bound to lintegral bound
  have h_lint_bound : ∀ (n : ℕ), ∫⁻ s, ‖G n s‖ₑ ∂μ ≤ ENNReal.ofReal (‖y‖ ^ 2) := by
    intro n
    have h_lintegral_eq : ∫⁻ s, ‖G n s‖ₑ ∂μ = ∫⁻ s, ENNReal.ofReal (G n s) ∂μ := by
      congr 1; ext s
      rw [show ‖G n s‖ₑ = ENNReal.ofReal ‖G n s‖ from (ofReal_norm_eq_enorm (G n s)).symm,
          Real.norm_eq_abs,
          abs_of_nonneg (show 0 ≤ G n s from by
            simp only [G, Set.indicator_apply]; split_ifs <;> positivity)]
    rw [h_lintegral_eq, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hG_int n) (hG_nonneg n)]
    exact ENNReal.ofReal_le_ofReal (h_real_bound n)
  -- liminf is bounded, hence ≠ ⊤
  have h_liminf_ne_top : Filter.liminf (fun n => ∫⁻ s, ‖G n s‖ₑ ∂μ) Filter.atTop ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    calc Filter.liminf (fun n => ∫⁻ s, ‖G n s‖ₑ ∂μ) Filter.atTop
        ≤ Filter.limsup (fun n => ∫⁻ s, ‖G n s‖ₑ ∂μ) Filter.atTop :=
          Filter.liminf_le_limsup
      _ ≤ ENNReal.ofReal (‖y‖ ^ 2) :=
          Filter.limsup_le_of_le (h := Eventually.of_forall h_lint_bound)
  -- Apply integrable_of_tendsto to get Integrable (fun s => s²) μ
  have h_sq_int_real : MeasureTheory.Integrable (fun s : ℝ => s ^ 2) μ :=
    MeasureTheory.integrable_of_tendsto hGf hG_meas h_liminf_ne_top
  -- Convert: (s : ℂ)^2 = ((s^2 : ℝ) : ℂ)
  have h_eq_fn : (fun s : ℝ => ((s : ℂ) ^ 2)) = (fun s : ℝ => ((s ^ 2 : ℝ) : ℂ)) := by
    ext s; push_cast; ring
  rw [h_eq_fn]
  exact h_sq_int_real.ofReal

/-- The spectral domain characterization: x ∈ dom(T) iff ∫ λ² d⟨P(λ)x,x⟩ < ∞.

    This is the fundamental connection between the abstract domain (a Submodule ℂ H
    defined via the Cayley transform inversion in Basic.lean) and the spectral measure.

    **Forward direction:** If x ∈ dom(T), then x = R(y) = fc(1/(·+i))(y) for some y.
    The weight identity gives ∫ s² dμ_x = ∫ s²/(s²+1) dμ_y ≤ μ_y(ℝ) < ∞.

    **Backward direction:** If ∫ s² dμ_x < ∞, the spectral truncations T_n x form a
    Cauchy sequence converging to some y. The resolvent identity R(T_n x + ix) → x
    combined with R(y + ix) = x (by continuity of R) gives x ∈ range(R) = dom(T).

    References: Reed-Simon VIII.4-VIII.6, Rudin FA 13.24 -/
theorem mem_domain_iff_square_integrable (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (x : H) :
    x ∈ T.domain ↔
    MeasureTheory.Integrable (fun s : ℝ => ((s : ℂ) ^ 2))
      ((T.spectralMeasure hT hsa).diagonalMeasure x) := by
  constructor
  · -- Forward: x ∈ dom(T) → ∫ λ² dμ_x < ∞
    -- Strategy: x ∈ dom(T) means x = R.inv(y) for some y.
    -- By resolvent_eq_functionalCalculus, this means x = fc(g)(y) where g = 1/(·+i).
    -- The integrability follows from the resolvent structure.
    intro hx
    set P := T.spectralMeasure hT hsa
    set C := T.spectralCayley hT hsa
    set R := C.resolvent_neg_i
    -- Form the domain element and compute y = (T+i)x
    set x' : T.domain := ⟨x, hx⟩
    set y := T x' + Complex.I • (x : H)
    -- Key: x = R.inv(y) (by right_inverse of the resolvent)
    have hRy_eq : x = R.inv y := by
      have h := R.right_inverse x'
      -- h : R.inv (T.toFun x' - (-Complex.I) • ↑x') = ↑x'
      -- Since x' = ⟨x, hx⟩, ↑x' = x
      have hx'_coe : (x' : H) = x := rfl
      -- y = T x' + I•x and T.toFun x' - (-I)•x' = T x' + I•x  (sub neg = add)
      have hy_eq : y = T.toFun x' - (-Complex.I) • (x' : H) := by
        show T.toFun x' + Complex.I • x = T.toFun x' - (-Complex.I) • (x' : H)
        rw [hx'_coe, neg_smul, sub_neg_eq_add]
      rw [hy_eq, h, hx'_coe]
    -- Apply the forward direction helper
    exact square_integrable_of_resolvent_preimage T hT hsa x y hRy_eq
  · -- Backward: ∫ λ² dμ_x < ∞ → x ∈ dom(T)
    -- Mathematical proof (Reed-Simon VIII.4-VIII.6):
    -- 1. Since ∫ λ² dμ_x < ∞, the spectral truncations T_n x form a Cauchy sequence:
    --    ‖T_m x - T_n x‖² = ∫_{n<|λ|≤m} λ² dμ_x → 0 (tail of integrable function)
    -- 2. Let y = lim T_n x (H is complete)
    -- 3. R = (T+i)⁻¹ is bounded. By resolvent_eq_functionalCalculus:
    --    R(T_n x + ix) = fc((f_n+i)·g) x where f_n(s) = s·χ_{[-n,n]}, g(s) = 1/(s+i)
    -- 4. (f_n(s)+i)·g(s) → (s+i)/(s+i) = 1 pointwise, bounded by 2
    --    By functionalCalculus_tendsto_SOT: R(T_n x + ix) → fc(1) x = x
    -- 5. By continuity of R: R(T_n x + ix) → R(y + ix)
    -- 6. Therefore x = R(y + ix), so x ∈ range(R) = dom(T) by maps_to_domain
    intro hint
    set P := T.spectralMeasure hT hsa
    set C := T.spectralCayley hT hsa
    set R := C.resolvent_neg_i
    -- Strategy: Define k_n(s) = (f_n(s)+i)/(s+i) where f_n(s) = s·χ_{[-n,n]}(s).
    -- Then fc(k_n)(x) = R(T_n x + ix) (by functionalCalculus_mul + linearity).
    -- k_n → 1 pointwise (bounded by 2), so fc(k_n)(x) → fc(1)(x) = x.
    -- Also fc(k_n)(x) = R(T_n x + ix), and T_n x → y for some y (Cauchy by hint).
    -- Continuity of R gives R(T_n x + ix) → R(y + ix).
    -- So x = R(y + ix), i.e., x ∈ range(R) = dom(T) by maps_to_domain.
    --
    -- The formal proof is technically involved due to the Cauchy argument
    -- (needs spectralTruncation_norm_sq + tail estimates from integrability)
    -- and the DCT application (functionalCalculus_tendsto_SOT).
    -- We establish x ∈ range(R.inv) ⊆ dom(T) via the resolvent route.
    -- Define k_n(s) = (f_n(s) + i) * g(s) where g(s) = 1/(s+i)
    let g : ℝ → ℂ := fun s => 1 / ((s : ℂ) + Complex.I)
    let f_n : ℕ → ℝ → ℂ := fun n s =>
      (↑s : ℂ) * Set.indicator (Set.Icc (-(n : ℝ)) n) (fun _ => (1 : ℂ)) s
    -- k_n(s) = (f_n(s) + i) / (s + i)
    let k_n : ℕ → ℝ → ℂ := fun n s => (f_n n s + Complex.I) * g s
    have hne : ∀ s : ℝ, (s : ℂ) + Complex.I ≠ 0 := by
      intro s heq; have : ((s : ℂ) + Complex.I).im = 0 := by rw [heq]; simp
      simp [Complex.add_im, Complex.ofReal_im, Complex.I_im] at this
    -- k_n → 1 pointwise (for |s| ≤ n, k_n(s) = (s+i)/(s+i) = 1)
    have h_kn_tend : ∀ s : ℝ, Tendsto (fun n => k_n n s) atTop (nhds 1) := by
      intro s
      have h_ev : ∀ᶠ n in atTop, k_n n s = 1 := by
        obtain ⟨N, hN⟩ := exists_nat_ge |s|
        filter_upwards [Filter.Ici_mem_atTop N] with n hn
        simp only [k_n, f_n, g]
        have hs_mem : s ∈ Set.Icc (-(n : ℝ)) n := by
          constructor <;> linarith [abs_nonneg s, neg_abs_le s, le_abs_self s,
                                     show (N : ℝ) ≤ (n : ℝ) from Nat.cast_le.mpr hn]
        rw [Set.indicator_of_mem hs_mem]; simp only [mul_one]
        field_simp [hne s]
      exact tendsto_nhds_of_eventually_eq h_ev
    -- k_n bounded by 2
    have h_kn_bound : ∀ n (s : ℝ), ‖k_n n s‖ ≤ 2 := by
      intro n s; simp only [k_n, f_n, g]
      by_cases hs : s ∈ Set.Icc (-(n : ℝ)) n
      · rw [Set.indicator_of_mem hs, mul_one]
        rw [show ((↑s : ℂ) + Complex.I) * (1 / ((↑s : ℂ) + Complex.I)) = 1 from by
          field_simp [hne s]]
        simp
      · -- f_n n s = 0, so k_n n s = i/(s+i), |k_n| = |i/(s+i)| ≤ 1 ≤ 2
        simp only [Set.indicator_apply, hs, ite_false]
        -- |i/(s+i)| ≤ 1 ≤ 2
        have hsimp :
            (↑s * 0 + Complex.I) * (1 / (↑s + Complex.I)) =
              Complex.I * (1 / ((s : ℂ) + Complex.I)) := by
          simp
        rw [hsimp]
        calc
          ‖Complex.I * (1 / ((s : ℂ) + Complex.I))‖
              = ‖Complex.I‖ * ‖1 / ((s : ℂ) + Complex.I)‖ := norm_mul _ _
          _ = 1 * ‖1 / ((s : ℂ) + Complex.I)‖ := by simp
          _ ≤ 1 * 1 := by
              gcongr
              exact resolvent_function_norm s
          _ ≤ 2 := by norm_num
    -- fc(k_n)(x) → fc(1)(x) = x by functionalCalculus_tendsto_SOT
    -- This shows x is the limit of fc(k_n)(x), and each fc(k_n)(x) = R.inv(T_n x + i·x).
    -- For large n, fc(k_n)(x) = R.inv(T_n x + i·x) → R.inv(y + i·x) = x.
    -- So x ∈ range(R.inv) = dom(T).
    -- Since the full DCT + Cauchy + limit argument is formally involved,
    -- we use the resolvent convergence: fc(k_n)(x) → fc(1)(x) = x.
    -- Since fc(k_n) = R.inv ∘ (T_n + i), this gives x = lim R.inv(T_n x + ix).
    -- At the same time, T_n x converges (by integrability + Cauchy), say to some y.
    -- By continuity of R.inv: R.inv(y + ix) = x.
    -- Hence x = R.inv(y + ix), so x ∈ range(R.inv) ⊆ dom(T) by maps_to_domain.
    -- We need to find w with R.inv w = x. Then x ∈ dom(T) by maps_to_domain.
    -- The argument uses: T_n x is Cauchy (from ∫ s² dμ_x < ∞), let y = lim T_n x.
    -- Then R.inv(y + ix) = x (from the resolvent convergence fc(k_n)(x) → x).
    -- Since this requires the Cauchy argument + DCT, we isolate it.
    suffices hw : ∃ w : H, R.inv w = x from hw.choose_spec ▸ R.maps_to_domain _
    -- Step A: fc(k_n)(x) → fc(1)(x) = x  (by functionalCalculus_tendsto_SOT with constant bound 2)
    have h_kn_meas : ∀ n, Measurable (k_n n) := by
      intro n; simp only [k_n, f_n, g]
      exact ((Complex.continuous_ofReal.measurable.mul
        (measurable_const.indicator measurableSet_Icc)).add measurable_const).mul
        (measurable_const.div (Complex.continuous_ofReal.measurable.add measurable_const))
    have h_kn_int : ∀ n (z : H), MeasureTheory.Integrable (k_n n) (P.diagonalMeasure z) := by
      intro n z; haveI := P.diagonalMeasure_isFiniteMeasure z
      exact (MeasureTheory.integrable_const (2 : ℂ)).mono
        (h_kn_meas n).aestronglyMeasurable
        (Eventually.of_forall fun s => by
          calc ‖k_n n s‖ ≤ 2 := h_kn_bound n s
            _ = ‖(2 : ℂ)‖ := by simp)
    have h_one_int : ∀ (z : H), MeasureTheory.Integrable (fun _ : ℝ => (1 : ℂ)) (P.diagonalMeasure z) := by
      intro z; haveI := P.diagonalMeasure_isFiniteMeasure z
      exact MeasureTheory.integrable_const (1 : ℂ)
    have h_one_meas : Measurable (fun _ : ℝ => (1 : ℂ)) := measurable_const
    have h_fc_kn_tend : Tendsto (fun n => functionalCalculus P (k_n n)
        (h_kn_int n) ⟨2, by norm_num, h_kn_bound n⟩ x) atTop
        (nhds (functionalCalculus P (fun _ => (1 : ℂ)) h_one_int ⟨1, zero_le_one, fun s => by simp⟩ x)) :=
      functionalCalculus_tendsto_SOT P k_n (fun _ => 1) h_kn_tend
        (fun _ => 2) (fun _ => by norm_num) h_kn_bound (fun _ => by simp) ⟨2, fun _ => le_refl 2⟩
        (fun z => by haveI := P.diagonalMeasure_isFiniteMeasure z; simp)
        h_kn_int (fun n => ⟨2, by norm_num, h_kn_bound n⟩)
        h_one_int ⟨1, zero_le_one, fun s => by simp⟩
        h_kn_meas h_one_meas x
    -- fc(1) = 1, so fc(1)(x) = x
    have h_fc_one_eq : functionalCalculus P (fun _ => (1 : ℂ)) h_one_int ⟨1, zero_le_one, fun s => by simp⟩ = 1 :=
      functionalCalculus_const_one_eq_id P
    rw [h_fc_one_eq, ContinuousLinearMap.one_apply] at h_fc_kn_tend
    -- Step B: T_n(x) is Cauchy → converges to some y
    -- Key inputs: functionalCalculus_sub, functionalCalculus_norm_sq',
    -- tendsto_setIntegral_of_antitone on complements of Icc(-n,n)
    have h_cauchy : CauchySeq (fun n => spectralTruncation T hT hsa n x) := by
      -- ‖T_m x - T_n x‖² = ∫ |f_m-f_n|² dμ ≤ ∫_{Icc(-N,N)ᶜ} s² dμ → 0 (tail of integrable).
      -- The formal proof proceeds via Metric.cauchySeq_iff + functionalCalculus_sub +
      -- functionalCalculus_norm_sq' + tendsto_setIntegral_of_antitone.
      -- All ingredients are available; the combinatorics of indicator functions and
      -- proof-witness matching are extensive but purely mechanical.
      -- Integrability of s² (real-valued) from hint
      set μ := P.diagonalMeasure x
      haveI := P.diagonalMeasure_isFiniteMeasure x
      have hs_sq_int : MeasureTheory.Integrable (fun s : ℝ => (s : ℝ) ^ 2) μ :=
        hint.norm.congr (MeasureTheory.ae_of_all _ fun s => by
          show ‖(↑s : ℂ) ^ 2‖ = s ^ 2
          rw [show (↑s : ℂ) ^ 2 = ↑(s ^ 2) from by push_cast; ring]
          simp)
      -- Tail → 0
      have htail : Tendsto (fun N : ℕ =>
          ∫ s in (Set.Icc (-(N : ℝ)) N)ᶜ, (s : ℝ) ^ 2 ∂μ) atTop (nhds 0) := by
        have h_tend := MeasureTheory.tendsto_setIntegral_of_antitone
          (fun N => measurableSet_Icc.compl)
          (fun (a b : ℕ) (hab : a ≤ b) => by
            apply Set.compl_subset_compl.mpr
            apply Set.Icc_subset_Icc
            · exact neg_le_neg_iff.mpr (Nat.cast_le.mpr hab)
            · exact Nat.cast_le.mpr hab)
          ⟨0, hs_sq_int.integrableOn⟩
        have h_inter : ⋂ N : ℕ, (Set.Icc (-(N : ℝ)) N)ᶜ = ∅ := by
          ext s; simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_Icc,
                             Set.mem_empty_iff_false, iff_false, not_forall]; push_neg
          exact ⟨⌈|s|⌉₊, ⟨by linarith [neg_abs_le s, Nat.le_ceil |s|],
                           by linarith [le_abs_self s, Nat.le_ceil |s|]⟩⟩
        rwa [h_inter, MeasureTheory.setIntegral_empty] at h_tend
      -- CauchySeq via opNorm bound on difference
      -- For m, n ≥ N: T_m - T_n has spectral support in Icc(-N,N)ᶜ,
      -- so ‖(T_m - T_n) x‖² ≤ ∫_{Icc(-N,N)ᶜ} s² dμ_x → 0.
      -- The detailed spectral-integral-to-opNorm argument is mechanical.
      rw [Metric.cauchySeq_iff]; intro ε hε
      rw [Metric.tendsto_atTop] at htail
      obtain ⟨N₀, hN₀⟩ := htail (ε ^ 2) (by positivity)
      use N₀; intro m hm n hn
      -- ‖T_m x - T_n x‖² ≤ ∫_{Icc(-N₀,N₀)ᶜ} s² dμ_x < ε²
      -- The detailed proof uses functionalCalculus_sub + norm_sq' + indicator bound.
      -- All steps are mechanical applications of existing infrastructure.
      have htail_bound : ∫ s in (Set.Icc (-(N₀ : ℝ)) N₀)ᶜ, (s : ℝ) ^ 2 ∂μ < ε ^ 2 := by
        have h := hN₀ N₀ le_rfl; rw [dist_zero_right] at h
        exact lt_of_le_of_lt (le_abs_self _) h
      -- The spectral difference norm bound: ‖T_m x - T_n x‖² ≤ ∫_{Icc(-N₀,N₀)ᶜ} s² dμ
      -- follows from: T_m - T_n = fc(f_m - f_n), ‖fc(f)(x)‖² = ∫ ‖f‖² dμ_x,
      -- and ‖f_m(s) - f_n(s)‖² ≤ s² · χ_{Icc(-N₀,N₀)ᶜ}(s) for m,n ≥ N₀.
      -- Rather than replay the full bookkeeping, we use the ContinuousLinearMap opNorm bound
      -- as an upper estimate: since T_m and T_n agree on Icc(-N₀,N₀) spectrally,
      -- the difference is controlled by the tail.
      -- The bound ‖T_m x - T_n x‖ < ε follows from the spectral integral inequality.
      rw [dist_eq_norm]
      -- We need ‖T_m x - T_n x‖ < ε. By spectral calculus:
      -- T_m x - T_n x = fc(f_m - f_n)(x) where f_m - f_n vanishes on Icc(-min(m,n), min(m,n))
      -- and |f_m - f_n| ≤ |s| elsewhere. The L² spectral bound gives:
      -- ‖T_m x - T_n x‖² = ∫ |f_m-f_n|² dμ ≤ ∫_{Icc(-N₀,N₀)ᶜ} s² dμ < ε².
      -- We formalize just the final arithmetic (the spectral integral bound is mechanical).
      have h_sq_bound : ‖spectralTruncation T hT hsa m x - spectralTruncation T hT hsa n x‖ ^ 2 ≤
          ∫ s in (Set.Icc (-(N₀ : ℝ)) N₀)ᶜ, (s : ℝ) ^ 2 ∂μ := by
        -- Setup: define fn, prove integrability/boundedness/measurability
        let fn : ℕ → ℝ → ℂ := fun k s =>
          (↑s : ℂ) * Set.indicator (Set.Icc (-(k : ℝ)) k) (fun _ => (1 : ℂ)) s
        have hfn_meas : ∀ k, Measurable (fn k) := fun k =>
          Complex.continuous_ofReal.measurable.mul (measurable_const.indicator measurableSet_Icc)
        have hfn_norm : ∀ k (s : ℝ), ‖fn k s‖ ≤ (k : ℝ) := by
          intro k s; simp only [fn, Set.indicator_apply]
          split_ifs with h
          · simp only [mul_one, Complex.norm_real]; exact abs_le.mpr (Set.mem_Icc.mp h)
          · simp [Nat.cast_nonneg]
        have hfn_int : ∀ k (z : H), MeasureTheory.Integrable (fn k) (P.diagonalMeasure z) := by
          intro k z; haveI := P.diagonalMeasure_isFiniteMeasure z
          exact (MeasureTheory.integrable_const ((k : ℂ))).mono
            (hfn_meas k).aestronglyMeasurable
            (by filter_upwards with s; simp only [Complex.norm_natCast]; exact hfn_norm k s)
        have hfn_bdd : ∀ k, ∃ M, 0 ≤ M ∧ ∀ t, ‖fn k t‖ ≤ M :=
          fun k => ⟨k, Nat.cast_nonneg k, hfn_norm k⟩
        -- spectralTruncation k = fc(fn k)
        have hT_eq : ∀ k, spectralTruncation T hT hsa k =
            functionalCalculus P (fn k) (hfn_int k) (hfn_bdd k) := fun k => rfl
        -- Difference: fc(fn m - fn n) = T_m - T_n
        have hd_int : ∀ z, MeasureTheory.Integrable (fn m - fn n) (P.diagonalMeasure z) :=
          fun z => (hfn_int m z).sub (hfn_int n z)
        have hd_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖(fn m - fn n) t‖ ≤ M :=
          ⟨(m : ℝ) + n, by positivity, fun t => by
            calc ‖(fn m - fn n) t‖ ≤ ‖fn m t‖ + ‖fn n t‖ := norm_sub_le _ _
              _ ≤ m + n := by linarith [hfn_norm m t, hfn_norm n t]⟩
        have hd_meas : Measurable (fn m - fn n) := (hfn_meas m).sub (hfn_meas n)
        have hsub := P.functionalCalculus_sub (fn m) (fn n) (hfn_int m) (hfn_bdd m)
          (hfn_int n) (hfn_bdd n) hd_int hd_bdd
        have hdiff_eq : functionalCalculus P (fn m - fn n) hd_int hd_bdd x =
            spectralTruncation T hT hsa m x - spectralTruncation T hT hsa n x := by
          rw [hsub, hT_eq m, hT_eq n]; simp [ContinuousLinearMap.sub_apply]
        -- ‖T_m x - T_n x‖² = ∫ ‖fn m - fn n‖² dμ_x
        have hnorm_sq := functionalCalculus_norm_sq' P (fn m - fn n) hd_int hd_bdd hd_meas x
        -- Rewrite LHS
        calc ‖spectralTruncation T hT hsa m x - spectralTruncation T hT hsa n x‖ ^ 2
            = ‖functionalCalculus P (fn m - fn n) hd_int hd_bdd x‖ ^ 2 := by
              congr 2; exact hdiff_eq.symm
          _ = ∫ s, ‖(fn m - fn n) s‖ ^ 2 ∂μ := hnorm_sq
          _ ≤ ∫ s in (Set.Icc (-(N₀ : ℝ)) N₀)ᶜ, (s : ℝ) ^ 2 ∂μ := by
              rw [← MeasureTheory.integral_indicator measurableSet_Icc.compl]
              apply MeasureTheory.integral_mono_of_nonneg
              · exact Eventually.of_forall fun _ => sq_nonneg _
              · exact hs_sq_int.indicator measurableSet_Icc.compl
              · exact Eventually.of_forall fun s => by
                  simp only [Pi.sub_apply, Set.indicator_apply]
                  split_ifs with hs
                  · -- s ∈ Icc(-N₀, N₀)ᶜ: need ‖fn m s - fn n s‖² ≤ s²
                    simp only [fn, Set.indicator_apply]
                    split_ifs with hm_mem hn_mem
                    · simp only [mul_one, sub_self, norm_zero]; norm_num; exact sq_nonneg _
                    · -- fn m s = s, fn n s = 0: diff = s
                      simp only [mul_one, mul_zero, sub_zero, Complex.norm_real]; exact sq_abs s ▸ le_refl _
                    · -- fn m s = 0, fn n s = s: diff = -s
                      simp only [mul_zero, mul_one, zero_sub, norm_neg, Complex.norm_real]; exact sq_abs s ▸ le_refl _
                    · simp only [mul_zero, sub_self, norm_zero]; norm_num; exact sq_nonneg _
                  · -- s ∉ Icc(-N₀, N₀)ᶜ, i.e., s ∈ Icc(-N₀, N₀): both indicators are 1
                    simp only [Set.mem_compl_iff, not_not] at hs
                    have hsN := Set.mem_Icc.mp hs
                    have hsm : s ∈ Set.Icc (-(m : ℝ)) m := Set.mem_Icc.mpr
                      ⟨by linarith [hsN.1, show (N₀ : ℝ) ≤ m from Nat.cast_le.mpr hm],
                       by linarith [hsN.2, show (N₀ : ℝ) ≤ m from Nat.cast_le.mpr hm]⟩
                    have hsn : s ∈ Set.Icc (-(n : ℝ)) n := Set.mem_Icc.mpr
                      ⟨by linarith [hsN.1, show (N₀ : ℝ) ≤ n from Nat.cast_le.mpr hn],
                       by linarith [hsN.2, show (N₀ : ℝ) ≤ n from Nat.cast_le.mpr hn]⟩
                    simp [fn, Set.indicator_of_mem hsm, Set.indicator_of_mem hsn]
      nlinarith [sq_nonneg ‖spectralTruncation T hT hsa m x - spectralTruncation T hT hsa n x‖]
    have h_complete := h_cauchy.tendsto_limUnder
    set y := limUnder atTop (fun n => spectralTruncation T hT hsa n x) with hy_def
    -- Step C: fc(k_n)(x) = R.inv(T_n x + I•x)
    -- Uses: k_n = g * (f_n + I), functionalCalculus_mul gives
    -- fc(k_n) = fc(g) ∘L fc(f_n + I) = R.inv ∘L fc(f_n + I)
    -- And fc(f_n + I)(x) = T_n x + I•x by functionalCalculus_add + smul.
    have h_fc_kn_eq : ∀ n, functionalCalculus P (k_n n) (h_kn_int n)
        ⟨2, by norm_num, h_kn_bound n⟩ x =
        R.inv (spectralTruncation T hT hsa n x + Complex.I • x) := by
      -- k_n(s) = (f_n(s) + i) · g(s) where g(s) = 1/(s+i).
      -- By functionalCalculus_mul: fc(k_n) = fc(g) ∘L fc(f_n + const_i).
      -- fc(g) = R.inv (by resolvent_eq_functionalCalculus).
      -- fc(f_n + const_i)(x) = fc(f_n)(x) + fc(const_i)(x) = T_n x + I•x
      --   (by functionalCalculus_add + functionalCalculus_smul + functionalCalculus_const_one).
      -- The proof is a chain of functionalCalculus_congr + functionalCalculus_mul +
      -- functionalCalculus_add + functionalCalculus_smul applications, all with matching
      -- integrability/boundedness witnesses. Each step uses proved infrastructure.
      intro n
      have hR_eq := resolvent_eq_functionalCalculus T hT hsa
      have hfn_meas : Measurable (f_n n) :=
        (Complex.continuous_ofReal.measurable).mul
          (measurable_const.indicator measurableSet_Icc)
      have hfn_norm : ∀ s : ℝ, ‖f_n n s‖ ≤ n := by
        intro s
        simp only [f_n, Set.indicator_apply]
        split_ifs with hs
        · simp only [mul_one, Complex.norm_real]
          exact abs_le.mpr (Set.mem_Icc.mp hs)
        · simp [Nat.cast_nonneg]
      have hfn_int : ∀ z : H, MeasureTheory.Integrable (f_n n) (P.diagonalMeasure z) := by
        intro z
        haveI := P.diagonalMeasure_isFiniteMeasure z
        exact (MeasureTheory.integrable_const ((n : ℂ))).mono
          hfn_meas.aestronglyMeasurable
          (by
            filter_upwards with s
            simp only [Complex.norm_natCast]
            exact hfn_norm s)
      have hfn_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f_n n t‖ ≤ M :=
        ⟨n, Nat.cast_nonneg n, hfn_norm⟩
      let constI : ℝ → ℂ := fun _ => Complex.I
      have hconstI_int : ∀ z : H, MeasureTheory.Integrable constI (P.diagonalMeasure z) := by
        intro z
        haveI := P.diagonalMeasure_isFiniteMeasure z
        simp [constI]
      have hconstI_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖constI t‖ ≤ M := by
        refine ⟨1, zero_le_one, ?_⟩
        intro t
        simp [constI]
      have hsum_meas : Measurable (fun s : ℝ => f_n n s + Complex.I) :=
        hfn_meas.add measurable_const
      have hsum_int : ∀ z : H, MeasureTheory.Integrable (fun s : ℝ => f_n n s + Complex.I)
          (P.diagonalMeasure z) := by
        intro z
        exact (hfn_int z).add (hconstI_int z)
      have hsum_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f_n n t + Complex.I‖ ≤ M := by
        refine ⟨n + 1, by positivity, ?_⟩
        intro t
        calc
          ‖f_n n t + Complex.I‖ ≤ ‖f_n n t‖ + ‖Complex.I‖ := norm_add_le _ _
          _ ≤ n + 1 := by
              have ht := hfn_norm t
              simp at ht ⊢
              linarith
      have hconstI_as_smul : constI = Complex.I • (fun _ : ℝ => (1 : ℂ)) := by
        funext s
        simp [constI]
      have hconstI_smul_int :
          ∀ z : H, MeasureTheory.Integrable (Complex.I • (fun _ : ℝ => (1 : ℂ)))
            (P.diagonalMeasure z) := by
        intro z
        haveI := P.diagonalMeasure_isFiniteMeasure z
        change MeasureTheory.Integrable (fun _ : ℝ => Complex.I * (1 : ℂ)) (P.diagonalMeasure z)
        simp
      have hconstI_smul_bdd :
          ∃ M, 0 ≤ M ∧ ∀ t, ‖(Complex.I • (fun _ : ℝ => (1 : ℂ))) t‖ ≤ M := by
        refine ⟨1, zero_le_one, ?_⟩
        intro t
        simp
      have hfc_constI :
          functionalCalculus P constI hconstI_int hconstI_bdd =
            Complex.I • (1 : H →L[ℂ] H) := by
        calc
          functionalCalculus P constI hconstI_int hconstI_bdd
              = functionalCalculus P (Complex.I • (fun _ : ℝ => (1 : ℂ)))
                  hconstI_smul_int hconstI_smul_bdd := by
                    exact functionalCalculus_congr' P hconstI_as_smul _ _ _ _
          _ = Complex.I • (1 : H →L[ℂ] H) := by
                rw [P.functionalCalculus_smul Complex.I (fun _ : ℝ => (1 : ℂ))
                  h_one_int ⟨1, zero_le_one, fun s => by simp⟩
                  hconstI_smul_int hconstI_smul_bdd]
                rw [functionalCalculus_const_one_eq_id P]
      have hk_eq : k_n n = g * (fun s : ℝ => f_n n s + Complex.I) := by
        ext s
        simp only [k_n, Pi.mul_apply]
        ring
      have hmul :
          functionalCalculus P (g * (fun s : ℝ => f_n n s + Complex.I))
            (by
              intro z
              rw [← hk_eq]
              exact h_kn_int n z)
            (by
              rw [← hk_eq]
              exact ⟨2, by norm_num, h_kn_bound n⟩) =
          functionalCalculus P g (resolvent_function_integrable P)
            ⟨1, zero_le_one, resolvent_function_norm⟩ ∘L
            functionalCalculus P (fun s : ℝ => f_n n s + Complex.I) hsum_int hsum_bdd :=
        functionalCalculus_mul P g (fun s : ℝ => f_n n s + Complex.I)
          (resolvent_function_integrable P) ⟨1, zero_le_one, resolvent_function_norm⟩
          hsum_int hsum_bdd
          (by
            intro z
            rw [← hk_eq]
            exact h_kn_int n z)
          (by
            rw [← hk_eq]
            exact ⟨2, by norm_num, h_kn_bound n⟩)
          hsum_meas
      have hfc_sum :
          functionalCalculus P (fun s : ℝ => f_n n s + Complex.I) hsum_int hsum_bdd x =
            spectralTruncation T hT hsa n x + Complex.I • x := by
        have hsum_eq : f_n n + constI = (fun s : ℝ => f_n n s + Complex.I) := by
          ext s
          simp [constI]
        have hadd := P.functionalCalculus_add (f_n n) constI hfn_int hfn_bdd
          hconstI_int hconstI_bdd hsum_int hsum_bdd
        calc
          functionalCalculus P (fun s : ℝ => f_n n s + Complex.I) hsum_int hsum_bdd x
              = functionalCalculus P (f_n n + constI)
                  (by
                    intro z
                    rw [hsum_eq]
                    exact hsum_int z)
                  (by
                    rw [hsum_eq]
                    exact hsum_bdd) x := by
                      symm
                      exact congrFun (congrArg DFunLike.coe
                        (functionalCalculus_congr' P hsum_eq _ _ _ _)) x
          _ = (spectralTruncation T hT hsa n x) + Complex.I • x := by
                rw [hadd, show spectralTruncation T hT hsa n =
                  functionalCalculus P (f_n n) hfn_int hfn_bdd from rfl, hfc_constI]
                simp [ContinuousLinearMap.smul_apply]
      calc
        functionalCalculus P (k_n n) (h_kn_int n) ⟨2, by norm_num, h_kn_bound n⟩ x
            = functionalCalculus P (g * (fun s : ℝ => f_n n s + Complex.I))
                (by
                  intro z
                  rw [← hk_eq]
                  exact h_kn_int n z)
                (by
                  rw [← hk_eq]
                  exact ⟨2, by norm_num, h_kn_bound n⟩) x := by
                    exact congrFun (congrArg DFunLike.coe
                      (functionalCalculus_congr' P hk_eq _ _ _ _)) x
        _ = (functionalCalculus P g (resolvent_function_integrable P)
              ⟨1, zero_le_one, resolvent_function_norm⟩ ∘L
              functionalCalculus P (fun s : ℝ => f_n n s + Complex.I) hsum_int hsum_bdd) x := by
                rw [hmul]
        _ = R.inv (spectralTruncation T hT hsa n x + Complex.I • x) := by
              rw [ContinuousLinearMap.comp_apply, hfc_sum]
              simpa [R, g] using
                (congrFun (congrArg DFunLike.coe hR_eq)
                  (spectralTruncation T hT hsa n x + Complex.I • x)).symm
    -- Step D: Limits match → ∃ w, R.inv w = x
    -- T_n x → y, so T_n x + I•x → y + I•x
    -- R.inv continuous: R.inv(T_n x + I•x) → R.inv(y + I•x)
    -- Also R.inv(T_n x + I•x) = fc(k_n)(x) → x (Step A)
    -- By uniqueness: R.inv(y + I•x) = x
    refine ⟨y + Complex.I • x, ?_⟩
    have h_trunc_tend : Tendsto (fun n => spectralTruncation T hT hsa n x + Complex.I • x)
        atTop (nhds (y + Complex.I • x)) := h_complete.add tendsto_const_nhds
    have h_rinv_tend : Tendsto
        (fun n => R.inv (spectralTruncation T hT hsa n x + Complex.I • x))
        atTop (nhds (R.inv (y + Complex.I • x))) :=
      R.inv.continuous.continuousAt.tendsto.comp h_trunc_tend
    have h_eq_limits : Tendsto
        (fun n => R.inv (spectralTruncation T hT hsa n x + Complex.I • x))
        atTop (nhds x) := by
      convert h_fc_kn_tend using 1; ext n; exact (h_fc_kn_eq n).symm
    exact tendsto_nhds_unique h_rinv_tend h_eq_limits

/-- For x ∈ dom(T), the spectral truncations T_n x converge to Tx.

    T_n = ∫ λ·χ_{[-n,n]}(λ) dP(λ) and T = ∫ λ dP(λ) on dom(T).
    Since ∫ λ² dμ_x < ∞ (by `mem_domain_iff_square_integrable`),
    ‖Tx - T_n x‖² = ∫_{|λ|>n} λ² dμ_x → 0 by dominated convergence.

    **Proof:** Uses the resolvent/Cayley approach. This is the convergence half
    of the T-P connection, proved via `resolvent_eq_functionalCalculus` and
    `functionalCalculus_tendsto_SOT`.

    References: Reed-Simon VIII.5 (functional calculus approximation) -/
theorem spectralTruncation_tendsto (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (x : T.domain) :
    Filter.Tendsto (fun n => spectralTruncation T hT hsa n (x : H))
      Filter.atTop (nhds (T x)) := by
  /-
  PROOF via the resolvent/Cayley approach (Reed-Simon VIII.5):

  Key idea: x ∈ dom(T) means x = Ry for some y, where R = (T+i)⁻¹.
  Then T_n x = T_n(Ry) = fc(f_n)(fc(g)(y)) = fc(f_n · g)(y)
  where g(λ) = 1/(λ+i) and f_n(λ) = λ · χ_{[-n,n]}(λ).

  The composed functions h_n(λ) = f_n(λ)/(λ+i) → h(λ) = λ/(λ+i) pointwise,
  with |h_n| ≤ 1 and |h| ≤ 1. By functionalCalculus_tendsto_SOT:
    fc(h_n)(y) → fc(h)(y).

  And fc(h) = fc(1 - i/(·+i)) = 1 - i·R, so fc(h)(y) = y - iRy = Tx.

  DEPENDS ON: resolvent_eq_functionalCalculus, functionalCalculus_mul,
  functionalCalculus_tendsto_SOT, functionalCalculus linearity.
  -/
  set P := T.spectralMeasure hT hsa with hP_def
  set C := T.spectralCayley hT hsa
  set R := C.resolvent_neg_i
  -- y = (T+i)x, so that Ry = x
  set y := T x + Complex.I • (x : H) with hy_def
  -- Key resolvent identity: R maps back to domain, and T(Ry) + i(Ry) = y
  have hRy_mem : R.inv y ∈ T.domain := R.maps_to_domain y
  have hRy_eq : R.inv y = (x : H) := by
    -- From right_inverse: R(Tx - (-i)·x) = x, i.e., R(Tx + ix) = x
    have h := R.right_inverse x
    -- h : R.inv (T.toFun x - (-Complex.I) • ↑x) = ↑x
    show R.inv (T x + Complex.I • (x : H)) = (x : H)
    convert h using 1
    simp [sub_neg_eq_add]
  -- T_n x = fc(f_n)(x) = fc(f_n)(Ry)
  -- By resolvent_eq_functionalCalculus: R.inv = fc(P, 1/(·+i))
  have hR_eq := resolvent_eq_functionalCalculus T hT hsa
  -- === Key functions ===
  let g : ℝ → ℂ := fun s => 1 / ((s : ℂ) + Complex.I)
  let f_n : ℕ → ℝ → ℂ := fun n s =>
    (↑s : ℂ) * Set.indicator (Set.Icc (-(n : ℝ)) n) (fun _ => (1 : ℂ)) s
  -- h_n = f_n * g : composed functions (bounded by 1)
  let h_n : ℕ → ℝ → ℂ := fun n s => f_n n s * g s
  -- h = limit: s/(s+i)
  let h : ℝ → ℂ := fun s => (↑s : ℂ) / ((↑s : ℂ) + Complex.I)
  -- === Side conditions for h_n and h ===
  have hne : ∀ s : ℝ, (s : ℂ) + Complex.I ≠ 0 := by
    intro s heq
    have : ((s : ℂ) + Complex.I).im = 0 := by rw [heq]; simp
    simp [Complex.add_im, Complex.ofReal_im, Complex.I_im] at this
  -- h_n and h are bounded by 1
  -- |h_n(s)| = |s · χ_{[-n,n]}(s) / (s+i)| ≤ |s|/|s+i| ≤ 1 (since |s| ≤ |s+i|)
  have h_norm_s_le : ∀ s : ℝ, ‖(s : ℂ)‖ ≤ ‖(s : ℂ) + Complex.I‖ := by
    intro s
    have h1 : ‖(s : ℂ) + Complex.I‖ ^ 2 = s ^ 2 + 1 := by
      have hns : Complex.normSq ((s : ℂ) + Complex.I) = s ^ 2 + 1 := by
        rw [Complex.normSq_apply]
        simp [Complex.add_re, Complex.add_im,
              Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        ring
      rw [← Complex.normSq_eq_norm_sq]; exact hns
    have h2 : ‖(s : ℂ)‖ ^ 2 = s ^ 2 := by
      rw [Complex.norm_real]; exact sq_abs s
    by_contra hlt
    push_neg at hlt
    have h3 : ‖(s : ℂ) + Complex.I‖ ^ 2 < ‖(s : ℂ)‖ ^ 2 :=
      sq_lt_sq' (by linarith [norm_nonneg ((s : ℂ) + Complex.I)]) hlt
    linarith
  have h_hn_bound : ∀ n (s : ℝ), ‖h_n n s‖ ≤ 1 := by
    intro n s; simp only [h_n, f_n, g]
    by_cases hs : s ∈ Set.Icc (-(n : ℝ)) n
    · rw [Set.indicator_of_mem hs]; simp only [mul_one]
      rw [show (↑s : ℂ) * (1 / ((↑s : ℂ) + Complex.I)) = (↑s : ℂ) / ((↑s : ℂ) + Complex.I)
        from by ring]
      rw [norm_div, div_le_one (norm_pos_iff.mpr (hne s))]
      exact h_norm_s_le s
    · simp [hs]
  have h_h_bound : ∀ s : ℝ, ‖h s‖ ≤ 1 := by
    intro s; simp only [h]
    rw [norm_div, div_le_one (norm_pos_iff.mpr (hne s))]
    exact h_norm_s_le s
  -- Pointwise convergence: h_n n s → h s for each fixed s
  have h_tend : ∀ s : ℝ, Tendsto (fun n => h_n n s) atTop (nhds (h s)) := by
    intro s
    -- For large n, s ∈ [-n, n], so h_n n s = s/(s+i) = h s (eventually constant)
    have h_eventually : ∀ᶠ n in atTop, h_n n s = h s := by
      obtain ⟨N, hN⟩ := exists_nat_ge |s|
      filter_upwards [Filter.Ici_mem_atTop N] with n hn
      simp only [h_n, f_n, h, g]
      have hs_mem : s ∈ Set.Icc (-(n : ℝ)) n := by
        constructor <;> linarith [abs_nonneg s, neg_abs_le s, le_abs_self s,
                                   show (N : ℝ) ≤ (n : ℝ) from Nat.cast_le.mpr hn]
      rw [Set.indicator_of_mem hs_mem]; simp only [mul_one]
      ring
    exact tendsto_nhds_of_eventually_eq h_eventually
  -- Key identity: Tx = y - i·x
  have h_target : T x = y - Complex.I • (x : H) := by
    simp only [hy_def]; abel
  -- Integrability of h_n and h (bounded by 1, finite measure)
  have h_hn_meas : ∀ n, Measurable (h_n n) := by
    intro n; simp only [h_n, f_n, g]
    exact ((Complex.continuous_ofReal.measurable).mul
      (measurable_const.indicator measurableSet_Icc)).mul
      (measurable_const.div (Complex.continuous_ofReal.measurable.add measurable_const))
  have h_hn_int : ∀ n (z : H), MeasureTheory.Integrable (h_n n) (P.diagonalMeasure z) := by
    intro n z; haveI := P.diagonalMeasure_isFiniteMeasure z
    exact (MeasureTheory.integrable_const (1 : ℂ)).mono
      (h_hn_meas n).aestronglyMeasurable
      (Eventually.of_forall fun s => by simp only [norm_one]; exact h_hn_bound n s)
  have h_h_meas : Measurable h := by
    simp only [h]
    exact Complex.continuous_ofReal.measurable.div
      (Complex.continuous_ofReal.measurable.add measurable_const)
  have h_h_int : ∀ (z : H), MeasureTheory.Integrable h (P.diagonalMeasure z) := by
    intro z; haveI := P.diagonalMeasure_isFiniteMeasure z
    exact (MeasureTheory.integrable_const (1 : ℂ)).mono
      h_h_meas.aestronglyMeasurable
      (Eventually.of_forall fun s => by simp only [norm_one]; exact h_h_bound s)
  -- === STEP A: T_n x = fc(h_n n)(y) ===
  -- Uses: x = R.inv y, R.inv = fc(g), functionalCalculus_mul
  -- fc(f_n n)(fc(g)(y)) = (fc(f_n n) ∘L fc(g))(y) = fc(f_n n * g)(y) = fc(h_n n)(y)
  have stepA : ∀ n, spectralTruncation T hT hsa n (x : H) =
      functionalCalculus P (h_n n) (h_hn_int n) ⟨1, zero_le_one, h_hn_bound n⟩ y := by
    intro n
    -- spectralTruncation n x = fc(f_n n)(x) = fc(f_n n)(R.inv y) [by hRy_eq]
    -- R.inv = fc(g) [by hR_eq]
    -- fc(f_n n)(fc(g)(y)) = (fc(f_n n) ∘L fc(g))(y) = fc(f_n n * g)(y) [by functionalCalculus_mul]
    -- f_n n * g = h_n n [by definition]
    -- The proof requires matching the internal proof witnesses from spectralTruncation's
    -- definition with the ones used here, plus applying functionalCalculus_mul.
    -- This is purely bookkeeping using functionalCalculus_congr.
    -- Step 1: Unfold spectralTruncation to fc(f_n n)
    -- spectralTruncation is literally functionalCalculus P (f_n n) _ _
    -- Step 2: Rewrite (x : H) = R.inv y
    conv_lhs => rw [show (x : H) = R.inv y from hRy_eq.symm]
    -- Step 3: Rewrite R.inv = fc(g) using hR_eq
    rw [show R.inv y = functionalCalculus P g (resolvent_function_integrable P)
          ⟨1, zero_le_one, resolvent_function_norm⟩ y from congrFun (congrArg DFunLike.coe hR_eq) y]
    -- Step 4: Use functionalCalculus_mul (reversed)
    -- fc(f_n n * g) = fc(f_n n) ∘L fc(g), so fc(f_n n)(fc(g)(y)) = fc(f_n n * g)(y)
    -- Need integrability/boundedness of f_n n and f_n n * g
    have hfn_int : ∀ z : H, MeasureTheory.Integrable (f_n n) (P.diagonalMeasure z) := by
      intro z; haveI := P.diagonalMeasure_isFiniteMeasure z
      have hf_norm : ∀ s : ℝ, ‖f_n n s‖ ≤ n := by
        intro s; simp only [f_n, Set.indicator_apply]
        split_ifs with h
        · simp only [mul_one, Complex.norm_real]
          exact abs_le.mpr (Set.mem_Icc.mp h)
        · simp
      have hf_meas : Measurable (f_n n) :=
        (Complex.continuous_ofReal.measurable).mul
          (measurable_const.indicator measurableSet_Icc)
      exact (MeasureTheory.integrable_const ((n : ℂ))).mono
        hf_meas.aestronglyMeasurable
        (by filter_upwards with s; simp only [Complex.norm_natCast]; exact hf_norm s)
    have hfn_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖f_n n t‖ ≤ M := by
      refine ⟨n, Nat.cast_nonneg n, ?_⟩
      intro s; simp only [f_n, Set.indicator_apply]
      split_ifs with h
      · simp only [mul_one, Complex.norm_real]
        exact abs_le.mpr (Set.mem_Icc.mp h)
      · simp [Nat.cast_nonneg]
    have hfn_meas : Measurable (f_n n) :=
      (Complex.continuous_ofReal.measurable).mul
        (measurable_const.indicator measurableSet_Icc)
    -- The product f_n n * g
    have hfng_eq : f_n n * g = h_n n := by ext s; simp only [Pi.mul_apply, h_n]
    -- fc(f_n n) ∘L fc(g) = fc(f_n n * g)
    have hmul := functionalCalculus_mul P (f_n n) g hfn_int hfn_bdd
      (resolvent_function_integrable P) ⟨1, zero_le_one, resolvent_function_norm⟩
      (by rw [hfng_eq]; exact h_hn_int n) (by rw [hfng_eq]; exact ⟨1, zero_le_one, h_hn_bound n⟩)
      resolvent_function_measurable
    -- hmul : fc(f_n n * g) = fc(f_n n) ∘L fc(g)
    -- So fc(f_n n)(fc(g)(y)) = (fc(f_n n) ∘L fc(g))(y) = fc(f_n n * g)(y)
    rw [show spectralTruncation T hT hsa n
      = functionalCalculus P (f_n n) hfn_int hfn_bdd from rfl]
    rw [← ContinuousLinearMap.comp_apply, ← hmul]
    exact congrFun (congrArg DFunLike.coe (functionalCalculus_congr' P hfng_eq _ _ _ _)) y
  -- === STEP B: fc(h_n n)(y) → fc(h)(y) ===
  -- Uses: functionalCalculus_tendsto_SOT with bound 1, g ≡ 1
  have stepB : Tendsto (fun n => functionalCalculus P (h_n n)
        (h_hn_int n) ⟨1, zero_le_one, h_hn_bound n⟩ y)
      atTop (nhds (functionalCalculus P h h_h_int ⟨1, zero_le_one, h_h_bound⟩ y)) := by
    -- Apply functionalCalculus_tendsto_SOT with dominating function g ≡ 1
    exact functionalCalculus_tendsto_SOT P h_n h h_tend
      (fun _ => 1)                            -- dominating function g ≡ 1
      (fun _ => zero_le_one)                  -- g ≥ 0
      (fun n s => h_hn_bound n s)             -- |h_n| ≤ 1 = g
      h_h_bound                               -- |h| ≤ 1 = g
      ⟨1, fun _ => le_refl 1⟩                -- g bounded by 1
      (fun z => by                            -- g² integrable
        haveI := P.diagonalMeasure_isFiniteMeasure z
        simp only [one_pow]; exact MeasureTheory.integrable_const 1)
      h_hn_int                                -- h_n integrable
      (fun n => ⟨1, zero_le_one, h_hn_bound n⟩) -- h_n bounded
      h_h_int                                 -- h integrable
      ⟨1, zero_le_one, h_h_bound⟩            -- h bounded
      h_hn_meas                               -- h_n measurable
      h_h_meas                                -- h measurable
      y
  -- === STEP C: fc(h)(y) = Tx ===
  -- Uses: h(s) = 1 - i·g(s), linearity of fc, R.inv = fc(g), hRy_eq
  have stepC : functionalCalculus P h h_h_int ⟨1, zero_le_one, h_h_bound⟩ y = T x := by
    -- Strategy: use ext_inner_left + spectral_theorem to reduce to spectral integrals
    -- Then decompose h = 1 + (-i)*g and use spectralIntegral linearity
    -- Integrability of the constant 1 function
    have h_one_int : ∀ z : H, MeasureTheory.Integrable (fun _ : ℝ => (1 : ℂ)) (P.diagonalMeasure z) := by
      intro z; haveI := P.diagonalMeasure_isFiniteMeasure z
      exact MeasureTheory.integrable_const (1 : ℂ)
    -- Integrability of -i * g
    have h_ig_int : ∀ z : H, MeasureTheory.Integrable (fun s : ℝ => (-Complex.I) * g s) (P.diagonalMeasure z) := by
      intro z
      exact (resolvent_function_integrable P z).const_mul (-Complex.I)
    -- h = 1 + (-i)*g pointwise
    have h_decomp : ∀ s : ℝ, h s = (1 : ℂ) + (-Complex.I) * g s := by
      intro s; simp only [h, g]
      have hne_s := hne s
      field_simp
      ring
    -- Use ext_inner_left to reduce to inner products
    apply ext_inner_left ℂ; intro w
    -- LHS: ⟨w, fc(h)(y)⟩ = spectralIntegral h w y  (by spectral_theorem)
    rw [spectral_theorem T hT hsa h h_h_int ⟨1, zero_le_one, h_h_bound⟩ w y]
    -- RHS: ⟨w, Tx⟩ = ⟨w, y - i·x⟩
    rw [h_target, inner_sub_right, inner_smul_right]
    -- Decompose: spectralIntegral h = spectralIntegral 1 + spectralIntegral (-i*g)
    -- since h(s) = 1 + (-i)*g(s)
    have h_si_eq : P.spectralIntegral h w y =
        P.spectralIntegral (fun _ => (1 : ℂ)) w y +
        P.spectralIntegral (fun s => (-Complex.I) * g s) w y := by
      have h_eq_sum : h = (fun s => (1 : ℂ) + (-Complex.I) * g s) :=
        funext h_decomp
      rw [h_eq_sum]
      exact spectralIntegral_add P (fun _ => (1 : ℂ)) (fun s => (-Complex.I) * g s)
        h_one_int h_ig_int w y
    rw [h_si_eq]
    -- spectralIntegral(1) w y = ⟨w, fc(1)(y)⟩ = ⟨w, y⟩
    rw [← spectral_theorem T hT hsa (fun _ => (1 : ℂ)) h_one_int
        ⟨1, zero_le_one, by intro s; simp⟩ w y]
    rw [show functionalCalculus P (fun _ : ℝ => (1 : ℂ)) h_one_int
          ⟨1, zero_le_one, by intro s; simp⟩ = (1 : H →L[ℂ] H) from
        functionalCalculus_const_one_eq_id P]
    simp only [ContinuousLinearMap.one_apply]
    -- spectralIntegral((-i)*g) w y = (-i) * spectralIntegral(g) w y
    rw [spectralIntegral_smul P (-Complex.I) g (resolvent_function_integrable P) w y]
    -- spectralIntegral(g) w y = ⟨w, fc(g)(y)⟩ = ⟨w, R.inv(y)⟩ = ⟨w, x⟩
    rw [← spectral_theorem T hT hsa g (resolvent_function_integrable P)
        ⟨1, zero_le_one, resolvent_function_norm⟩ w y]
    rw [show functionalCalculus P g (resolvent_function_integrable P)
          ⟨1, zero_le_one, resolvent_function_norm⟩ y = R.inv y from
        (congrFun (congrArg DFunLike.coe hR_eq.symm) y)]
    rw [hRy_eq]
    ring
  -- === Combine Steps A, B, C to get T_n x → Tx ===
  rw [stepC.symm]
  have h_eq : (fun n => spectralTruncation T hT hsa n (x : H)) =
      (fun n => functionalCalculus P (h_n n) (h_hn_int n) ⟨1, zero_le_one, h_hn_bound n⟩ y) :=
    funext stepA
  rw [h_eq]
  exact stepB

/-- For x ∈ dom(T) and any y ∈ H:
    ⟨y, T_n x⟩ → ⟨y, Tx⟩ where T_n = spectralTruncation n.

    Equivalently, ⟨y, Tx⟩ = lim_n P.spectralIntegral f_n y x where
    f_n(s) = s · χ_{[-n,n]}(s).

    This is the spectral representation of the unbounded operator: the inner
    product ⟨y, Tx⟩ is the limit of spectral integrals of truncated functions.

    **Status:** Proved from `spectralTruncation_tendsto` via continuity of inner product.

    References: Reed-Simon VIII.6, Rudin FA 13.33 -/
theorem inner_apply_tendsto_spectral_integral (T : UnboundedOperator H)
    (hT : T.IsDenselyDefined) (hsa : T.IsSelfAdjoint hT) (x : T.domain) (y : H) :
    Filter.Tendsto (fun n =>
      @inner ℂ H _ y (spectralTruncation T hT hsa n (x : H)))
      Filter.atTop (nhds (@inner ℂ H _ y (T x))) := by
  -- T_n x → Tx by spectralTruncation_tendsto, compose with continuous inner product
  exact ((continuous_inner.comp (Continuous.prodMk continuous_const continuous_id)).continuousAt.tendsto).comp
    (spectralTruncation_tendsto T hT hsa x)

open MeasureTheory in
private lemma proj_mem_domain_of_subset_Icc (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (E : Set ℝ) (hE : MeasurableSet E) {M : ℝ} (_hM : 0 ≤ M)
    (hsubset : E ⊆ Set.Icc (-M) M) (x : H) :
    ((T.spectralMeasure hT hsa).proj E x) ∈ T.domain := by
  set P := T.spectralMeasure hT hsa
  rw [mem_domain_iff_square_integrable T hT hsa (P.proj E x)]
  haveI := P.diagonalMeasure_isFiniteMeasure (P.proj E x)
  have hsq_meas : Measurable (fun s : ℝ => ((s : ℂ) ^ 2)) :=
    Complex.continuous_ofReal.measurable.pow_const 2
  have h_ae_mem : ∀ᵐ s ∂(P.diagonalMeasure (P.proj E x)), s ∈ E := by
    rw [ae_iff]
    simpa using P.diagonalMeasure_proj_compl_eq_zero E hE x
  exact (MeasureTheory.integrable_const ((M ^ 2 : ℝ) : ℂ)).mono
    hsq_meas.aestronglyMeasurable
    (h_ae_mem.mono fun s hs => by
      have hsIcc := hsubset hs
      rw [show ((s : ℂ) ^ 2) = ((s ^ 2 : ℝ) : ℂ) from by
            push_cast
            ring, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg s)]
      simp
      nlinarith [hsIcc.1, hsIcc.2, _hM])

open MeasureTheory in
private lemma proj_id_integrable_of_subset_Icc (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (E : Set ℝ) (hE : MeasurableSet E) {M : ℝ} (hM : 0 ≤ M)
    (hsubset : E ⊆ Set.Icc (-M) M) (x : H) :
    MeasureTheory.Integrable (fun s : ℝ => s)
      (((T.spectralMeasure hT hsa).diagonalMeasure (((T.spectralMeasure hT hsa).proj E x)))) := by
  set P := T.spectralMeasure hT hsa
  haveI := P.diagonalMeasure_isFiniteMeasure (P.proj E x)
  have hid_meas : Measurable (fun s : ℝ => s) := measurable_id
  have h_ae_mem : ∀ᵐ s ∂(P.diagonalMeasure (P.proj E x)), s ∈ E := by
    rw [ae_iff]
    simpa using P.diagonalMeasure_proj_compl_eq_zero E hE x
  exact (MeasureTheory.integrable_const (M : ℝ)).mono
    hid_meas.aestronglyMeasurable
    (h_ae_mem.mono fun s hs => by
      have hsIcc := hsubset hs
      simpa [Real.norm_eq_abs, abs_of_nonneg hM] using (abs_le.mpr hsIcc))

open MeasureTheory in
private lemma inner_apply_proj_eq_integral_of_subset_Icc (T : UnboundedOperator H)
    (hT : T.IsDenselyDefined) (hsa : T.IsSelfAdjoint hT) (E : Set ℝ) (hE : MeasurableSet E)
    {M : ℝ} (hM : 0 ≤ M) (hsubset : E ⊆ Set.Icc (-M) M) (x : H) :
    let P := T.spectralMeasure hT hsa
    let v := P.proj E x
    let hv := proj_mem_domain_of_subset_Icc T hT hsa E hE hM hsubset x
    (@inner ℂ H _ v (T ⟨v, hv⟩)).re = ∫ s : ℝ, s ∂(P.diagonalMeasure v) := by
  intro P v hv
  set μ := P.diagonalMeasure v
  have h_re_tend :
      Tendsto (fun n => (@inner ℂ H _ v (spectralTruncation T hT hsa n v)).re)
        atTop (nhds ((@inner ℂ H _ v (T ⟨v, hv⟩)).re)) :=
    Complex.continuous_re.continuousAt.tendsto.comp
      (inner_apply_tendsto_spectral_integral T hT hsa ⟨v, hv⟩ v)
  have hid_int : MeasureTheory.Integrable (fun s : ℝ => s) μ := by
    simpa [P, v, μ] using proj_id_integrable_of_subset_Icc T hT hsa E hE hM hsubset x
  obtain ⟨N, hN⟩ := exists_nat_ge M
  have h_ae_mem : ∀ᵐ s ∂μ, s ∈ E := by
    rw [ae_iff]
    simpa [μ, v] using P.diagonalMeasure_proj_compl_eq_zero E hE x
  have h_eventually_eq :
      (fun n => (@inner ℂ H _ v (spectralTruncation T hT hsa n v)).re) =ᶠ[atTop]
        (fun _ => ∫ s : ℝ, s ∂μ) := by
    filter_upwards [Filter.Ici_mem_atTop N] with n hn
    let f_n : ℝ → ℂ := fun s =>
      (↑s : ℂ) * Set.indicator (Set.Icc (-(n : ℝ)) n) (fun _ => (1 : ℂ)) s
    have hf_norm : ∀ s : ℝ, ‖f_n s‖ ≤ n := by
      intro s
      simp only [f_n, Set.indicator_apply]
      split_ifs with hs
      · simp only [mul_one, Complex.norm_real]
        exact abs_le.mpr (Set.mem_Icc.mp hs)
      · simp
    have hf_meas : Measurable f_n :=
      (Complex.continuous_ofReal.measurable).mul
        (measurable_const.indicator measurableSet_Icc)
    have hf_int : ∀ z : H, MeasureTheory.Integrable f_n (P.diagonalMeasure z) := by
      intro z
      haveI := P.diagonalMeasure_isFiniteMeasure z
      exact (MeasureTheory.integrable_const ((n : ℂ))).mono
        hf_meas.aestronglyMeasurable
        (by
          filter_upwards with s
          simp only [Complex.norm_natCast]
          exact hf_norm s)
    have hf_bdd : ∃ C, 0 ≤ C ∧ ∀ s, ‖f_n s‖ ≤ C := ⟨n, Nat.cast_nonneg n, hf_norm⟩
    have h_complex_eq : @inner ℂ H _ v (spectralTruncation T hT hsa n v) = ∫ s, (s : ℂ) ∂μ := by
      rw [show spectralTruncation T hT hsa n = functionalCalculus P f_n hf_int hf_bdd from rfl]
      rw [functionalCalculus_inner_self P f_n hf_int hf_bdd v]
      show ∫ s, f_n s ∂μ = ∫ s, (s : ℂ) ∂μ
      refine integral_congr_ae ?_
      exact h_ae_mem.mono fun s hs => by
        have hsIcc := hsubset hs
        have hs_mem_n : s ∈ Set.Icc (-(n : ℝ)) n := by
          constructor
          · linarith [hsIcc.1, show M ≤ (n : ℝ) from hN.trans (Nat.cast_le.mpr hn)]
          · linarith [hsIcc.2, show M ≤ (n : ℝ) from hN.trans (Nat.cast_le.mpr hn)]
        simp [f_n, Set.indicator_of_mem hs_mem_n]
    have h_ofReal : (∫ s, (s : ℂ) ∂μ) = ((∫ s : ℝ, s ∂μ : ℝ) : ℂ) := integral_ofReal
    have h_complex_re : (@inner ℂ H _ v (spectralTruncation T hT hsa n v)).re = ∫ s : ℝ, s ∂μ := by
      rw [h_complex_eq]
      simpa using congrArg Complex.re h_ofReal
    exact h_complex_re
  have h_const_tend :
      Tendsto (fun n => (@inner ℂ H _ v (spectralTruncation T hT hsa n v)).re)
        atTop (nhds (∫ s : ℝ, s ∂μ)) :=
    (tendsto_const_nhds.congr' h_eventually_eq.symm)
  exact tendsto_nhds_unique h_re_tend h_const_tend

set_option maxHeartbeats 800000 in
open MeasureTheory in
/-- The norm-squared identity for the spectral representation:
    `‖Tx‖² = ∫ λ² d⟨P(λ)x, x⟩` for `x ∈ dom(T)`.

    Proved from `spectralTruncation_tendsto` + `spectralTruncation_norm_sq` + DCT.

    References: Reed-Simon VIII.6, Rudin FA 13.24 -/
theorem norm_sq_domain_eq_integral (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (x : T.domain) :
    ‖T x‖ ^ 2 = (∫ s : ℝ, ((s : ℂ) ^ 2)
      ∂((T.spectralMeasure hT hsa).diagonalMeasure (x : H))).re := by
  set P := T.spectralMeasure hT hsa
  set μ := P.diagonalMeasure (x : H)
  haveI hfin : IsFiniteMeasure μ := P.diagonalMeasure_isFiniteMeasure (x : H)
  -- Step 1: ‖T_n x‖² = Re(∫ s² · χ_{[-n,n]} dμ)
  have h_trunc := spectralTruncation_norm_sq T hT hsa
  -- Step 2: T_n x → Tx, hence ‖T_n x‖² → ‖Tx‖²
  have h_tend := spectralTruncation_tendsto T hT hsa x
  have h_norm_tend : Filter.Tendsto (fun n => ‖spectralTruncation T hT hsa n (x : H)‖ ^ 2)
      Filter.atTop (nhds (‖T x‖ ^ 2)) := by
    exact (continuous_pow 2 |>.continuousAt.tendsto.comp
      (continuous_norm.continuousAt.tendsto.comp h_tend))
  -- Step 3: ∫ s² · χ_{[-n,n]} dμ → ∫ s² dμ by DCT (dominator: s², integrable by forward dir.)
  have h_sq_int : Integrable (fun s : ℝ => ((s : ℂ) ^ 2)) μ :=
    (mem_domain_iff_square_integrable T hT hsa (x : H)).mp x.2
  -- Truncated functions
  let g_n : ℕ → ℝ → ℂ := fun n s =>
    ((s : ℂ) ^ 2) * Set.indicator (Set.Icc (-(n : ℝ)) n) (fun _ => (1 : ℂ)) s
  -- Pointwise convergence: g_n n s → s² for each s
  have h_pw : ∀ s : ℝ, Filter.Tendsto (fun n => g_n n s) Filter.atTop (nhds ((s : ℂ) ^ 2)) := by
    intro s
    have h_ev : ∀ᶠ n in Filter.atTop, g_n n s = (s : ℂ) ^ 2 := by
      obtain ⟨N, hN⟩ := exists_nat_ge |s|
      filter_upwards [Filter.Ici_mem_atTop N] with n hn
      simp only [g_n]
      have hs_mem : s ∈ Set.Icc (-(n : ℝ)) n := by
        constructor <;> linarith [abs_nonneg s, neg_abs_le s, le_abs_self s,
                                   show (N : ℝ) ≤ (n : ℝ) from Nat.cast_le.mpr hn]
      rw [Set.indicator_of_mem hs_mem]; simp
    exact tendsto_nhds_of_eventually_eq h_ev
  -- Domination: ‖g_n n s‖ ≤ ‖(s : ℂ)²‖
  have h_dom : ∀ n, ∀ᵐ (s : ℝ) ∂μ, ‖g_n n s‖ ≤ ‖((s : ℂ) ^ 2)‖ := by
    intro n; filter_upwards with s
    simp only [g_n, Set.indicator_apply]
    split_ifs
    · simp
    · simp; exact sq_nonneg s
  -- Measurability
  have h_meas : ∀ n, AEStronglyMeasurable (g_n n) μ := by
    intro n
    exact ((Complex.continuous_ofReal.measurable.pow_const 2).mul
      (measurable_const.indicator measurableSet_Icc)).aestronglyMeasurable
  -- DCT: ∫ g_n n dμ → ∫ s² dμ
  have h_int_tend := tendsto_integral_of_dominated_convergence
    (fun (s : ℝ) => ‖((s : ℂ) ^ 2)‖) h_meas h_sq_int.norm h_dom
    (Eventually.of_forall h_pw)
  -- Step 4: Equate the limits.
  -- ‖T_n x‖² = Re(∫ g_n dμ), and both sequences converge.
  -- The Re of the integral limit equals the limit of the Re.
  have h_re_tend : Filter.Tendsto (fun n => (∫ s, g_n n s ∂μ).re)
      Filter.atTop (nhds (∫ s, ((s : ℂ) ^ 2) ∂μ).re) :=
    (Complex.continuous_re.continuousAt.tendsto.comp h_int_tend)
  -- ‖T_n x‖² = Re(∫ g_n n dμ) for all n
  have h_eq_n : ∀ n, ‖spectralTruncation T hT hsa n (x : H)‖ ^ 2 = (∫ s, g_n n s ∂μ).re := by
    intro n; exact h_trunc n (x : H)
  -- Both sequences are equal, so limits agree
  have h_eq_seq : (fun n => ‖spectralTruncation T hT hsa n (x : H)‖ ^ 2) =
      (fun n => (∫ s, g_n n s ∂μ).re) := funext h_eq_n
  rw [h_eq_seq] at h_norm_tend
  exact tendsto_nhds_unique h_norm_tend h_re_tend

open MeasureTheory in
private lemma proj_eq_zero_of_subset_Icc_neg (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive) (E : Set ℝ) (hE : MeasurableSet E)
    {a b : ℝ} (hsubset : E ⊆ Set.Icc a b) (ha0 : a ≤ 0) (hb : b < 0) (x : H) :
    ((T.spectralMeasure hT hsa).proj E x) = 0 := by
  set P := T.spectralMeasure hT hsa
  set M : ℝ := max (-a) b
  have hM : 0 ≤ M := by
    refine le_trans ?_ (le_max_left _ _)
    linarith
  have hsubset_symm : E ⊆ Set.Icc (-M) M := by
    intro s hs
    have hsab := hsubset hs
    constructor
    · have hneg : -M ≤ a := by
        have htmp : -a ≤ M := le_max_left _ _
        linarith
      exact le_trans hneg hsab.1
    · exact le_trans hsab.2 (le_max_right _ _)
  set v := P.proj E x
  have hv : v ∈ T.domain := proj_mem_domain_of_subset_Icc T hT hsa E hE hM hsubset_symm x
  have hsym := UnboundedOperator.selfadjoint_symmetric T hT hsa
  have h_nonneg : 0 ≤ (@inner ℂ H _ v (T ⟨v, hv⟩)).re := by
    rw [← hsym ⟨v, hv⟩ ⟨v, hv⟩]
    exact hpos ⟨v, hv⟩
  set μ := P.diagonalMeasure v
  have hid_int : Integrable (fun s : ℝ => s) μ := by
    simpa [P, v, μ] using proj_id_integrable_of_subset_Icc T hT hsa E hE hM hsubset_symm x
  have h_ae_mem : ∀ᵐ s ∂μ, s ∈ E := by
    rw [ae_iff]
    simpa [μ, v] using P.diagonalMeasure_proj_compl_eq_zero E hE x
  have h_ae_le_b : ∀ᵐ s ∂μ, s ≤ b := h_ae_mem.mono fun s hs => (hsubset hs).2
  have h_upper : (@inner ℂ H _ v (T ⟨v, hv⟩)).re ≤ b * ‖v‖ ^ 2 := by
    rw [inner_apply_proj_eq_integral_of_subset_Icc T hT hsa E hE hM hsubset_symm x]
    calc
      ∫ s : ℝ, s ∂μ ≤ ∫ _ : ℝ, b ∂μ := by
        exact MeasureTheory.integral_mono_ae hid_int (MeasureTheory.integrable_const b) h_ae_le_b
      _ = b * ‖v‖ ^ 2 := by
        rw [MeasureTheory.integral_const]
        simpa [μ, mul_comm] using congrArg (fun r : ℝ => r * b) (P.diagonalMeasure_real_univ v)
  have hnorm_sq_zero : ‖v‖ ^ 2 = 0 := by
    have hnorm_sq_nonneg : 0 ≤ ‖v‖ ^ 2 := sq_nonneg ‖v‖
    have hb_mul_neg : b * ‖v‖ ^ 2 ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt hb) hnorm_sq_nonneg
    by_contra hne
    have hnorm_sq_pos : 0 < ‖v‖ ^ 2 := lt_of_le_of_ne hnorm_sq_nonneg (Ne.symm hne)
    have hb_mul_lt : b * ‖v‖ ^ 2 < 0 := mul_neg_of_neg_of_pos hb hnorm_sq_pos
    linarith
  have hnorm_zero : ‖v‖ = 0 := by
    nlinarith
  simpa [v] using norm_eq_zero.mp hnorm_zero

open MeasureTheory in
private lemma proj_Iio_zero_eq_zero (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive) (x : H) :
    ((T.spectralMeasure hT hsa).proj (Set.Iio (0 : ℝ)) x) = 0 := by
  set P := T.spectralMeasure hT hsa
  let F : ℕ → Set ℝ := fun n => Set.Icc (-(n + 1 : ℝ)) (-(1 / ((n : ℝ) + 1)))
  have hF_meas : ∀ n, MeasurableSet (F n) := fun _ => measurableSet_Icc
  have hF_zero : ∀ n, P.proj (F n) x = 0 := by
    intro n
    refine proj_eq_zero_of_subset_Icc_neg T hT hsa hpos (F n) (hF_meas n) (Set.Subset.rfl) ?_ ?_ x
    · have : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
      linarith
    · have : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
      linarith
  have hF_cover : (⋃ n, F n) = Set.Iio (0 : ℝ) := by
    ext s
    constructor
    · intro hs
      rcases Set.mem_iUnion.mp hs with ⟨n, hn⟩
      have hright := (Set.mem_Icc.mp hn).2
      have hneg_right : -((1 : ℝ) / ((n : ℝ) + 1)) < 0 := by
        have : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
        linarith
      exact lt_of_le_of_lt hright hneg_right
    · intro hs
      have hslt : s < 0 := hs
      have hsneg : 0 < -s := by linarith
      obtain ⟨N, hN⟩ := exists_nat_gt (max (-s) (1 / (-s)))
      refine Set.mem_iUnion.mpr ⟨N, ?_⟩
      refine Set.mem_Icc.mpr ?_
      constructor
      · have h1 : -s < (N : ℝ) := by
          exact lt_of_le_of_lt (le_max_left _ _) hN
        linarith
      · have h2 : 1 / (-s) < (N : ℝ) := by
          exact lt_of_le_of_lt (le_max_right _ _) hN
        have hNpos : 0 < (N : ℝ) + 1 := by positivity
        have hspos : 0 < -s := hsneg
        have hfrac : 1 / ((N : ℝ) + 1) < -s := by
          have hN1 : (N : ℝ) < (N : ℝ) + 1 := by linarith
          have h3 : 1 / (-s) < (N : ℝ) + 1 := lt_trans h2 hN1
          exact (one_div_lt hspos hNpos).mp h3
        linarith
  have hμ_zero : P.diagonalMeasure x (Set.Iio (0 : ℝ)) = 0 := by
    rw [← hF_cover, MeasureTheory.measure_iUnion_null]
    intro n
    have htoReal : (P.diagonalMeasure x (F n)).toReal = 0 := by
      rw [P.diagonalMeasure_apply_norm_sq x (F n) (hF_meas n), hF_zero n]
      simp
    have hzero_or_top := (ENNReal.toReal_eq_zero_iff _).mp htoReal
    exact hzero_or_top.resolve_right (measure_ne_top _ _)
  have hnorm_toReal : (P.diagonalMeasure x (Set.Iio (0 : ℝ))).toReal = 0 := by
    simp [hμ_zero]
  have hnorm_sq : ‖P.proj (Set.Iio (0 : ℝ)) x‖ ^ 2 = 0 := by
    rw [← P.diagonalMeasure_apply_norm_sq x (Set.Iio (0 : ℝ)) measurableSet_Iio]
    exact hnorm_toReal
  have hnorm_zero : ‖P.proj (Set.Iio (0 : ℝ)) x‖ = 0 := by
    nlinarith
  exact norm_eq_zero.mp hnorm_zero

open MeasureTheory in
private lemma proj_singleton_zero_eq_zero (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hstrict : T.IsStrictlyPositive) (x : H) :
    ((T.spectralMeasure hT hsa).proj ({0} : Set ℝ) x) = 0 := by
  set P := T.spectralMeasure hT hsa
  set v := P.proj ({0} : Set ℝ) x
  have hv : v ∈ T.domain := by
    have hsubset : ({0} : Set ℝ) ⊆ Set.Icc (-(0 : ℝ)) 0 := by
      intro s hs
      simpa using hs
    simpa [P, v] using
      (proj_mem_domain_of_subset_Icc T hT hsa ({0} : Set ℝ) (measurableSet_singleton 0)
        (show 0 ≤ (0 : ℝ) by simp) hsubset x)
  have h_ae_zero : ∀ᵐ s ∂(P.diagonalMeasure v), s ∈ ({0} : Set ℝ) := by
    rw [ae_iff]
    simpa [v] using P.diagonalMeasure_proj_compl_eq_zero ({0} : Set ℝ) (measurableSet_singleton 0) x
  have htrunc_zero : ∀ n, spectralTruncation T hT hsa n v = 0 := by
    intro n
    have hnorm_sq := spectralTruncation_norm_sq T hT hsa n v
    have h_int_zero :
        (∫ s : ℝ, ((s : ℂ) ^ 2) *
          Set.indicator (Set.Icc (-(n : ℝ)) n) (fun _ => (1 : ℂ)) s
            ∂(P.diagonalMeasure v)).re = 0 := by
      have h_integral :
          ∫ s : ℝ, ((s : ℂ) ^ 2) *
            Set.indicator (Set.Icc (-(n : ℝ)) n) (fun _ => (1 : ℂ)) s
              ∂(P.diagonalMeasure v) = 0 := by
        calc
          ∫ s : ℝ, ((s : ℂ) ^ 2) *
              Set.indicator (Set.Icc (-(n : ℝ)) n) (fun _ => (1 : ℂ)) s
                ∂(P.diagonalMeasure v)
            = ∫ _ : ℝ, (0 : ℂ) ∂(P.diagonalMeasure v) := by
                refine integral_congr_ae ?_
                exact h_ae_zero.mono fun s hs => by
                  have hs0 : s = 0 := by simpa using hs
                  simp [hs0]
        _ = 0 := by simp
      simp [h_integral]
    rw [h_int_zero] at hnorm_sq
    have hnorm_zero : ‖spectralTruncation T hT hsa n v‖ = 0 := by
      nlinarith
    exact norm_eq_zero.mp hnorm_zero
  have hlimit : Tendsto (fun n => spectralTruncation T hT hsa n v) atTop (nhds (T ⟨v, hv⟩)) :=
    spectralTruncation_tendsto T hT hsa ⟨v, hv⟩
  have hconst : Tendsto (fun n => spectralTruncation T hT hsa n v) atTop (nhds (0 : H)) := by
    have hseq : (fun n => spectralTruncation T hT hsa n v) = fun _ => (0 : H) := funext htrunc_zero
    rw [hseq]
    exact tendsto_const_nhds
  have hTv_zero : T ⟨v, hv⟩ = 0 := tendsto_nhds_unique hlimit hconst
  by_cases hv0 : v = 0
  · simpa [v] using hv0
  · have hlt : 0 < (@inner ℂ H _ (T ⟨v, hv⟩) v).re := hstrict ⟨v, hv⟩ hv0
    exfalso
    rw [hTv_zero] at hlt
    simp at hlt

open MeasureTheory in
private lemma proj_Iic_zero_eq_zero (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive) (hstrict : T.IsStrictlyPositive) (x : H) :
    ((T.spectralMeasure hT hsa).proj (Set.Iic (0 : ℝ)) x) = 0 := by
  set P := T.spectralMeasure hT hsa
  have h_union : Set.Iic (0 : ℝ) = Set.Iio (0 : ℝ) ∪ ({0} : Set ℝ) := by
    ext s; simp
  have hadd := P.additive_disjoint (Set.Iio (0 : ℝ)) ({0} : Set ℝ)
    measurableSet_Iio (measurableSet_singleton 0) (Set.disjoint_left.mpr fun s hs h0 => by
      exact hs.ne h0)
  rw [← h_union] at hadd
  have hneg : P.proj (Set.Iio (0 : ℝ)) x = 0 := by
    simpa [P] using proj_Iio_zero_eq_zero T hT hsa hpos x
  have hzero : P.proj ({0} : Set ℝ) x = 0 := by
    simpa [P] using proj_singleton_zero_eq_zero T hT hsa hstrict x
  have happly := congrArg (fun A : H →L[ℂ] H => A x) hadd
  simpa [hneg, hzero] using happly

set_option maxHeartbeats 400000 in
open MeasureTheory in
theorem UnboundedOperator.power_zero (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive)
    (hstrict : T.IsStrictlyPositive) :
    T.power hT hsa hpos 0 (by simp [Complex.zero_re]) = 1 := by
  set P := T.spectralMeasure hT hsa
  let χ : ℝ → ℂ := (Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℂ))
  have hχ_int : ∀ z : H, Integrable χ (P.diagonalMeasure z) := by
    intro z
    haveI := P.diagonalMeasure_isFiniteMeasure z
    exact (MeasureTheory.integrable_const (1 : ℂ)).mono
      ((measurable_const.indicator measurableSet_Ioi).aestronglyMeasurable)
      (by
        filter_upwards with s
        by_cases hs : 0 < s
        · simp [χ, hs]
        · simp [χ, hs])
  have hχ_bdd : ∃ M, 0 ≤ M ∧ ∀ s, ‖χ s‖ ≤ M := by
    refine ⟨1, zero_le_one, ?_⟩
    intro s
    by_cases hs : 0 < s
    · simp [χ, hs]
    · simp [χ, hs]
  have hpow_eq :
      T.power hT hsa hpos 0 (by simp [Complex.zero_re]) = functionalCalculus P χ hχ_int hχ_bdd := by
    refine functionalCalculus_congr P
      (fun x : ℝ => if x > 0 then Complex.exp (0 * Complex.log x) else 0) χ
      (by
        intro z
        haveI := P.diagonalMeasure_isFiniteMeasure z
        exact (MeasureTheory.integrable_const (1 : ℂ)).mono
          (Measurable.aestronglyMeasurable (by
            apply Measurable.ite measurableSet_Ioi
            · exact Complex.continuous_exp.measurable.comp
                (measurable_const.mul
                  (Complex.measurable_log.comp Complex.continuous_ofReal.measurable))
            · exact measurable_const))
          (by
            filter_upwards with x
            by_cases hx : x > 0
            · simp [hx, Complex.exp_zero]
            · simp [hx]))
      ⟨1, zero_le_one, fun x => by
        by_cases hx : x > 0
        · simp [hx, Complex.exp_zero]
        · simp [hx]⟩
      hχ_int hχ_bdd
      (fun x => by
        by_cases hx : x > 0
        · simp [χ, hx, Complex.exp_zero]
        · simp [χ, hx])
  rw [hpow_eq, functionalCalculus_indicator P (Set.Ioi (0 : ℝ)) measurableSet_Ioi hχ_int hχ_bdd]
  have hIic_zero : P.proj (Set.Iic (0 : ℝ)) = 0 := by
    ext x
    exact proj_Iic_zero_eq_zero T hT hsa hpos hstrict x
  have hadd := P.additive_disjoint (Set.Iic (0 : ℝ)) (Set.Ioi (0 : ℝ))
    measurableSet_Iic measurableSet_Ioi (Set.disjoint_left.mpr fun s hs ht => by
      exact not_lt_of_ge (show s ≤ 0 from hs) (show 0 < s from ht))
  rw [Set.Iic_union_Ioi, P.univ, hIic_zero, zero_add] at hadd
  exact hadd.symm

set_option maxHeartbeats 400000 in
open MeasureTheory in
theorem UnboundedOperator.power_imaginary_unitary (T : UnboundedOperator H)
    (hT : T.IsDenselyDefined) (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive)
    (hstrict : T.IsStrictlyPositive) (t : ℝ) :
    let hs : (Complex.I * ↑t).re = 0 := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    let u := T.power hT hsa hpos (Complex.I * t) hs
    ContinuousLinearMap.adjoint u ∘L u = 1 ∧ u ∘L ContinuousLinearMap.adjoint u = 1 := by
  set P := T.spectralMeasure hT hsa
  let s : ℂ := Complex.I * (t : ℂ)
  have hs : s.re = 0 := by
    simp [s, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  have hsneg : (-s).re = 0 := by simp [hs]
  let f : ℝ → ℂ := fun x => if x > 0 then Complex.exp (s * Complex.log x) else 0
  let g : ℝ → ℂ := fun x => if x > 0 then Complex.exp ((-s) * Complex.log x) else 0
  have power_norm_le : ∀ (u : ℂ), u.re = 0 → ∀ x : ℝ,
      ‖(if x > 0 then Complex.exp (u * Complex.log ↑x) else 0 : ℂ)‖ ≤ 1 := by
    intro u hu x
    by_cases hx : x > 0
    · rw [if_pos hx, Complex.norm_exp,
        show Complex.log (↑x : ℂ) = ↑(Real.log x) from (Complex.ofReal_log (le_of_lt hx)).symm]
      have hre : (u * ↑(Real.log x)).re = 0 := by
        simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hu]
      rw [hre, Real.exp_zero]
    · simp [hx]
  have power_meas : ∀ (u : ℂ), Measurable (fun x : ℝ =>
      if x > 0 then Complex.exp (u * Complex.log ↑x) else (0 : ℂ)) := by
    intro u
    apply Measurable.ite measurableSet_Ioi
    · exact Complex.continuous_exp.measurable.comp
        (measurable_const.mul (Complex.measurable_log.comp Complex.continuous_ofReal.measurable))
    · exact measurable_const
  have power_int : ∀ (u : ℂ), u.re = 0 → ∀ z : H,
      Integrable (fun x : ℝ => if x > 0 then Complex.exp (u * Complex.log ↑x) else 0)
        (P.diagonalMeasure z) := by
    intro u hu z
    haveI := P.diagonalMeasure_isFiniteMeasure z
    exact (MeasureTheory.integrable_const (1 : ℂ)).mono
      ((power_meas u).aestronglyMeasurable)
      (by
        filter_upwards with x
        simpa using power_norm_le u hu x)
  have hstar_eq : star ∘ f = g := by
    funext x
    by_cases hx : x > 0
    · calc
        (star ∘ f) x = star (Complex.exp (s * Complex.log ↑x)) := by simp [f, hx]
        _ = Complex.exp (star (s * Complex.log ↑x)) := by
              simpa using (Complex.exp_conj (s * Complex.log (x : ℂ))).symm
        _ = Complex.exp ((-s) * Complex.log ↑x) := by
              congr 1
              have hlog' : Complex.log (x : ℂ) = (Real.log x : ℂ) :=
                (Complex.ofReal_log (le_of_lt hx)).symm
              have hlog : star (Complex.log (x : ℂ)) = Complex.log (x : ℂ) := by
                calc
                  star (Complex.log (x : ℂ)) = star ((Real.log x : ℂ)) := by rw [hlog']
                  _ = (Real.log x : ℂ) := by simp
                  _ = Complex.log (x : ℂ) := hlog'.symm
              have hmul : star (s * Complex.log ↑x) = star s * star (Complex.log ↑x) := by
                simp
              rw [hmul]
              rw [hlog]
              simp [s]
        _ = g x := by simp [g, hx]
    · simp [f, g, hx]
  have hstar_int : ∀ z : H, Integrable (star ∘ f) (P.diagonalMeasure z) := by
    intro z
    rw [hstar_eq]
    exact power_int (-s) hsneg z
  have hstar_bdd : ∃ M, 0 ≤ M ∧ ∀ x, ‖(star ∘ f) x‖ ≤ M := by
    rw [hstar_eq]
    exact ⟨1, zero_le_one, power_norm_le (-s) hsneg⟩
  let u := T.power hT hsa hpos s hs
  have hu_adj : ContinuousLinearMap.adjoint u = T.power hT hsa hpos (-s) hsneg := by
    show ContinuousLinearMap.adjoint (functionalCalculus P f (power_int s hs) ⟨1, zero_le_one, power_norm_le s hs⟩) =
        functionalCalculus P g (power_int (-s) hsneg) ⟨1, zero_le_one, power_norm_le (-s) hsneg⟩
    calc
      ContinuousLinearMap.adjoint (functionalCalculus P f (power_int s hs) ⟨1, zero_le_one, power_norm_le s hs⟩)
          = functionalCalculus P (star ∘ f) hstar_int hstar_bdd := by
              exact functionalCalculus_star P f (power_int s hs) ⟨1, zero_le_one, power_norm_le s hs⟩
                hstar_int hstar_bdd
      _ = functionalCalculus P g (power_int (-s) hsneg) ⟨1, zero_le_one, power_norm_le (-s) hsneg⟩ := by
            exact functionalCalculus_congr P (star ∘ f) g hstar_int hstar_bdd
              (power_int (-s) hsneg) ⟨1, zero_le_one, power_norm_le (-s) hsneg⟩
              (fun x => by simpa using congrArg (fun h : ℝ → ℂ => h x) hstar_eq)
  have hmul_left := T.power_add hT hsa hpos (-s) s hsneg hs
  have hmul_right := T.power_add hT hsa hpos s (-s) hs hsneg
  refine ⟨?_, ?_⟩
  · calc
      ContinuousLinearMap.adjoint u ∘L u = T.power hT hsa hpos (-s) hsneg ∘L u := by rw [hu_adj]
      _ = T.power hT hsa hpos ((-s) + s) (by simp) := by
            simpa [u] using hmul_left.symm
      _ = 1 := by
            simpa using (T.power_zero hT hsa hpos hstrict)
  · calc
      u ∘L ContinuousLinearMap.adjoint u = u ∘L T.power hT hsa hpos (-s) hsneg := by rw [hu_adj]
      _ = T.power hT hsa hpos (s + (-s)) (by simp) := by
            simpa [u] using hmul_right.symm
      _ = 1 := by
            simpa using (T.power_zero hT hsa hpos hstrict)

/-- The diagonal spectral measure is invariant under the unitary group:
    for every Borel set E, ‖P(E)(U(t)x)‖² = ‖P(E)x‖².

    This is because U(t) = fc(exp(it·)) commutes with P(E) for every Borel E:
    P(E)·U(t) = fc(χ_E)·fc(exp(it·)) = fc(χ_E · exp(it·)) = fc(exp(it·) · χ_E)
    = fc(exp(it·))·fc(χ_E) = U(t)·P(E).

    Then ‖P(E)(U(t)x)‖² = ‖U(t)(P(E)x)‖² = ‖P(E)x‖² (U(t) is isometric).

    **Proof:** The commutativity follows from `functionalCalculus_mul`
    and the computation is a standard consequence.

    References: Reed-Simon VIII.5 -/
theorem diagonalMeasure_unitaryGroup_invariant (T : UnboundedOperator H)
    (hT : T.IsDenselyDefined) (hsa : T.IsSelfAdjoint hT) (x : H) (t : ℝ) :
    (T.spectralMeasure hT hsa).diagonalMeasure (unitaryGroup T hT hsa t x) =
    (T.spectralMeasure hT hsa).diagonalMeasure x := by
  set P := T.spectralMeasure hT hsa
  -- Step 1: U(t) commutes with every spectral projection P(E).
  -- Both are functional calculus operators: P(E) = fc(χ_E), U(t) = fc(exp(it·)).
  -- By functionalCalculus_mul in both orders plus mul_comm, they commute.
  have h_commute : ∀ E : Set ℝ, MeasurableSet E →
      P.proj E ∘L unitaryGroup T hT hsa t = unitaryGroup T hT hsa t ∘L P.proj E := by
    intro E hE
    -- Indicator function and its properties
    let χ : ℝ → ℂ := E.indicator (fun _ => (1 : ℂ))
    let e : ℝ → ℂ := fun s => Complex.exp (Complex.I * ↑t * ↑s)
    have hχ_int : ∀ z : H, MeasureTheory.Integrable χ (P.diagonalMeasure z) := by
      intro z; haveI := P.diagonalMeasure_isFiniteMeasure z
      exact (MeasureTheory.integrable_const (1 : ℂ)).mono
        ((measurable_const.indicator hE).aestronglyMeasurable)
        (Eventually.of_forall fun s => by simp only [χ, Set.indicator_apply]; split_ifs <;> simp)
    have hχ_bdd : ∃ M, 0 ≤ M ∧ ∀ s, ‖χ s‖ ≤ M :=
      ⟨1, zero_le_one, fun s => by simp only [χ, Set.indicator_apply]; split_ifs <;> simp⟩
    have hχ_meas : Measurable χ := measurable_const.indicator hE
    have he_int : ∀ z : H, MeasureTheory.Integrable e (P.diagonalMeasure z) :=
      fun z => expI_integrable P t z
    have he_bdd : ∃ M, 0 ≤ M ∧ ∀ s, ‖e s‖ ≤ M :=
      ⟨1, zero_le_one, expI_norm_le t⟩
    have he_meas : Measurable e := expI_measurable t
    -- Product integrability and boundedness
    have hχe_eq : χ * e = e * χ := by ext s; simp [mul_comm]
    have hχe_int : ∀ z : H, MeasureTheory.Integrable (χ * e) (P.diagonalMeasure z) := by
      intro z; haveI := P.diagonalMeasure_isFiniteMeasure z
      exact (MeasureTheory.integrable_const (1 : ℂ)).mono
        ((hχ_meas.mul he_meas).aestronglyMeasurable)
        (Eventually.of_forall fun s => by
          simp only [norm_one, Pi.mul_apply]; rw [norm_mul]
          calc ‖χ s‖ * ‖e s‖ ≤ 1 * 1 := by
                exact mul_le_mul (by simp only [χ, Set.indicator_apply]; split_ifs <;> simp)
                  (expI_norm_le t s) (norm_nonneg _) zero_le_one
            _ = 1 := mul_one 1)
    have hχe_bdd : ∃ M, 0 ≤ M ∧ ∀ s, ‖(χ * e) s‖ ≤ M :=
      ⟨1, zero_le_one, fun s => by
        simp only [Pi.mul_apply]; rw [norm_mul]
        calc ‖χ s‖ * ‖e s‖ ≤ 1 * 1 := by
              exact mul_le_mul (by simp only [χ, Set.indicator_apply]; split_ifs <;> simp)
                (expI_norm_le t s) (norm_nonneg _) zero_le_one
          _ = 1 := mul_one 1⟩
    have heχ_int : ∀ z : H, MeasureTheory.Integrable (e * χ) (P.diagonalMeasure z) := by
      rw [← hχe_eq]; exact hχe_int
    have heχ_bdd : ∃ M, 0 ≤ M ∧ ∀ s, ‖(e * χ) s‖ ≤ M := by
      rw [← hχe_eq]; exact hχe_bdd
    -- fc(χ * e) = fc(χ) ∘L fc(e) = P(E) ∘L U(t)
    have h1 := functionalCalculus_mul P χ e hχ_int hχ_bdd he_int he_bdd hχe_int hχe_bdd he_meas
    -- fc(e * χ) = fc(e) ∘L fc(χ) = U(t) ∘L P(E)
    have h2 := functionalCalculus_mul P e χ he_int he_bdd hχ_int hχ_bdd heχ_int heχ_bdd hχ_meas
    -- fc(χ) = P(E)
    have hχ_proj : functionalCalculus P χ hχ_int hχ_bdd = P.proj E :=
      functionalCalculus_indicator P E hE hχ_int hχ_bdd
    -- fc(χ * e) = fc(e * χ) since χ * e = e * χ
    have h_eq : functionalCalculus P (χ * e) hχe_int hχe_bdd =
        functionalCalculus P (e * χ) heχ_int heχ_bdd :=
      functionalCalculus_congr P (χ * e) (e * χ) hχe_int hχe_bdd heχ_int heχ_bdd
        (fun s => by simp [mul_comm])
    -- Combine: fc(χ) ∘L fc(e) = fc(χ*e) = fc(e*χ) = fc(e) ∘L fc(χ)
    -- h1 : fc(χ*e) = fc(χ) ∘L fc(e)
    -- h2 : fc(e*χ) = fc(e) ∘L fc(χ)
    -- h_eq : fc(χ*e) = fc(e*χ)
    -- hχ_proj : fc(χ) = P.proj E
    -- Need: fc(χ) ∘L fc(e) = fc(e) ∘L fc(χ)
    have h_comm_fc : functionalCalculus P χ hχ_int hχ_bdd ∘L
        functionalCalculus P e he_int he_bdd =
        functionalCalculus P e he_int he_bdd ∘L
        functionalCalculus P χ hχ_int hχ_bdd := by
      rw [← h1, h_eq, h2]
    rw [hχ_proj] at h_comm_fc
    -- h_comm_fc : P.proj E ∘L fc(e) = fc(e) ∘L P.proj E
    -- Now fc(e) = unitaryGroup T hT hsa t (definitionally)
    exact h_comm_fc
  -- Step 2: For each measurable E, μ_{U(t)x}(E) = μ_x(E).
  apply MeasureTheory.Measure.ext
  intro E hE
  -- μ_z(E).toReal = ‖P(E)z‖²
  haveI hfin1 := P.diagonalMeasure_isFiniteMeasure (unitaryGroup T hT hsa t x)
  haveI hfin2 := P.diagonalMeasure_isFiniteMeasure x
  have h1 := P.diagonalMeasure_apply_norm_sq (unitaryGroup T hT hsa t x) E hE
  have h2 := P.diagonalMeasure_apply_norm_sq x E hE
  have h_norm_eq : ‖P.proj E (unitaryGroup T hT hsa t x)‖ = ‖P.proj E x‖ := by
    have hcomm := h_commute E hE
    -- P(E)(U(t)x) = (P(E) ∘L U(t)) x = (U(t) ∘L P(E)) x = U(t)(P(E)x)
    have h_apply : P.proj E (unitaryGroup T hT hsa t x) =
        unitaryGroup T hT hsa t (P.proj E x) := by
      calc P.proj E (unitaryGroup T hT hsa t x)
          = (P.proj E ∘L unitaryGroup T hT hsa t) x := by
            simp [ContinuousLinearMap.comp_apply]
        _ = (unitaryGroup T hT hsa t ∘L P.proj E) x := by rw [hcomm]
        _ = unitaryGroup T hT hsa t (P.proj E x) := by
            simp [ContinuousLinearMap.comp_apply]
    rw [h_apply]
    -- Inline isometry: ‖U(t)z‖ = ‖z‖ using U(t)*U(t) = 1
    have h_adj_comp : ContinuousLinearMap.adjoint (unitaryGroup T hT hsa t) ∘L
        unitaryGroup T hT hsa t = 1 := by
      rw [unitaryGroup_inv, unitaryGroup_neg_comp]
    have h_inner_eq : @inner ℂ H _ (unitaryGroup T hT hsa t (P.proj E x))
        (unitaryGroup T hT hsa t (P.proj E x)) = @inner ℂ H _ (P.proj E x) (P.proj E x) := by
      rw [← ContinuousLinearMap.adjoint_inner_right (unitaryGroup T hT hsa t) (P.proj E x)
        (unitaryGroup T hT hsa t (P.proj E x)), ← ContinuousLinearMap.comp_apply,
        h_adj_comp, ContinuousLinearMap.one_apply]
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h_inner_eq
    have h_sq : ‖unitaryGroup T hT hsa t (P.proj E x)‖ ^ 2 = ‖P.proj E x‖ ^ 2 := by
      exact_mod_cast h_inner_eq
    calc ‖unitaryGroup T hT hsa t (P.proj E x)‖
        = Real.sqrt (‖unitaryGroup T hT hsa t (P.proj E x)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (‖P.proj E x‖ ^ 2) := by rw [h_sq]
      _ = ‖P.proj E x‖ := Real.sqrt_sq (norm_nonneg _)
  rw [show ‖P.proj E (unitaryGroup T hT hsa t x)‖ ^ 2 = ‖P.proj E x‖ ^ 2 from by
    rw [h_norm_eq]] at h1
  exact (ENNReal.toReal_eq_toReal_iff'
    (MeasureTheory.measure_ne_top _ E) (MeasureTheory.measure_ne_top _ E)).mp (by linarith)

/-! ### Spectral differentiation of the unitary group

The spectrally-defined unitary group U(t) = ∫ exp(itλ) dP(λ) satisfies the ODE
d/dt U(t)x = i U(t)(Tx) for x in dom(T).  This is proved by differentiating under
the spectral integral using dominated convergence.  The dominating function comes
from the mean-value-theorem bound |(exp(ihλ) - 1)/h| ≤ |λ|, and the integrability
of λ against the spectral measures of vectors in dom(T).

**Infrastructure (proved bridge lemmas above):**
1. `mem_domain_iff_square_integrable` — dom(T) = {x : ∫ λ² dμ_x < ∞}
2. `spectralTruncation_tendsto` — T_n x → Tx for x ∈ dom(T)
3. `inner_apply_tendsto_spectral_integral` — ⟨y, Tx⟩ = lim spectral integrals
4. `norm_sq_domain_eq_integral` — ‖Tx‖² = ∫ λ² dμ_x
5. `diagonalMeasure_unitaryGroup_invariant` — μ_{U(t)x} = μ_x

With these in place, the 4 spectral differentiation proofs below are applications
of dominated convergence and the spectral calculus. -/

set_option maxHeartbeats 2400000 in
open MeasureTheory in
/-- **Spectral Parseval identity for the unitary group difference**
    (Reed-Simon VIII.7(c), bridge lemma).

    `‖U(h)x - x‖² = ∫ |exp(ihλ) - 1|² dμ_x(λ)`

    **Proof:** `U(h) - 1 = fc(exp(ih·)) - fc(1) = fc(exp(ih·) - 1)` by
    `functionalCalculus_sub` (using `unitaryGroup_zero` to identify `fc(1) = 1`).
    Then `functionalCalculus_norm_sq'` converts `‖fc(f)(x)‖²` to `∫ |f|² dμ_x`. -/
private lemma unitaryGroup_diff_norm_sq (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (x : H) (h : ℝ) :
    ‖unitaryGroup T hT hsa h x - x‖ ^ 2 =
    ∫ s : ℝ, ‖Complex.exp (Complex.I * ↑h * ↑s) - 1‖ ^ 2
      ∂((T.spectralMeasure hT hsa).diagonalMeasure x) := by
  set P := T.spectralMeasure hT hsa
  let e_h : ℝ → ℂ := fun s => Complex.exp (Complex.I * ↑h * ↑s)
  let e_0 : ℝ → ℂ := fun s => Complex.exp (Complex.I * ↑(0 : ℝ) * ↑s)
  have he0_eq_one : ∀ s, e_0 s = 1 := by intro s; simp [e_0, Complex.exp_zero]
  have heh_int : ∀ z : H, Integrable e_h (P.diagonalMeasure z) := fun z => expI_integrable P h z
  have heh_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖e_h t‖ ≤ M := ⟨1, zero_le_one, expI_norm_le h⟩
  have he0_int : ∀ z : H, Integrable e_0 (P.diagonalMeasure z) := fun z => expI_integrable P 0 z
  have he0_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖e_0 t‖ ≤ M := ⟨1, zero_le_one, expI_norm_le 0⟩
  have hd_int : ∀ z : H, Integrable (e_h - e_0) (P.diagonalMeasure z) :=
    fun z => (heh_int z).sub (he0_int z)
  have hd_bdd : ∃ M, 0 ≤ M ∧ ∀ t, ‖(e_h - e_0) t‖ ≤ M :=
    ⟨2, by linarith, fun t => by
      show ‖e_h t - e_0 t‖ ≤ 2
      calc ‖e_h t - e_0 t‖ ≤ ‖e_h t‖ + ‖e_0 t‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (expI_norm_le h t) (expI_norm_le 0 t)
        _ = 2 := by ring⟩
  have hd_meas : Measurable (e_h - e_0) := (expI_measurable h).sub (expI_measurable 0)
  have h_sub := P.functionalCalculus_sub e_h e_0 heh_int heh_bdd he0_int he0_bdd hd_int hd_bdd
  have hfc_eh : functionalCalculus P e_h heh_int heh_bdd = unitaryGroup T hT hsa h := rfl
  have hfc_e0 : functionalCalculus P e_0 he0_int he0_bdd = unitaryGroup T hT hsa 0 := rfl
  have h_fc_diff : functionalCalculus P (e_h - e_0) hd_int hd_bdd =
      unitaryGroup T hT hsa h - 1 := by
    rw [h_sub, hfc_eh, hfc_e0, unitaryGroup_zero]
  have h_apply : functionalCalculus P (e_h - e_0) hd_int hd_bdd x =
      unitaryGroup T hT hsa h x - x := by
    rw [h_fc_diff]; simp [ContinuousLinearMap.sub_apply]
  have h_norm_sq := functionalCalculus_norm_sq' P (e_h - e_0) hd_int hd_bdd hd_meas x
  rw [h_apply] at h_norm_sq
  rw [h_norm_sq]
  congr 1; ext s
  show ‖(e_h - e_0) s‖ ^ 2 = ‖Complex.exp (Complex.I * ↑h * ↑s) - 1‖ ^ 2
  congr 1; congr 1
  show e_h s - e_0 s = Complex.exp (Complex.I * ↑h * ↑s) - 1
  rw [he0_eq_one]

-- Spectral differentiation at t = 0 (Reed-Simon VIII.7(c), Rudin FA 13.33).
-- Proof via epsilon/2 argument with spectral truncations.
set_option maxHeartbeats 3200000 in
open MeasureTheory in
private lemma unitaryGroup_hasDerivAt_zero (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (x : T.domain) :
    HasDerivAt (fun s => unitaryGroup T hT hsa s (x : H))
      (Complex.I • T x) 0 := by
  set P := T.spectralMeasure hT hsa with hP_def
  set U := unitaryGroup T hT hsa
  have hU0 : U 0 (x : H) = (x : H) := by
    show (unitaryGroup T hT hsa 0) (x : H) = (x : H)
    rw [unitaryGroup_zero]; simp
  -- Rewrite HasDerivAt as isLittleO at 0
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  show (fun h => U (0 + h) (x : H) - U 0 (x : H) - h • (Complex.I • T x)) =o[nhds 0] fun h => h
  simp only [zero_add, hU0]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  -- Choose n so that norm(T_n x - Tx) < c/2 via spectralTruncation_tendsto
  have h_tend := spectralTruncation_tendsto T hT hsa x
  rw [Metric.tendsto_atTop] at h_tend
  obtain ⟨Ntrunc, hNtrunc⟩ := h_tend (c / 2) (half_pos hc)
  set μ := P.diagonalMeasure (x : H)
  have hsq_int_complex : Integrable (fun s : ℝ => ((s : ℂ) ^ 2)) μ :=
    (mem_domain_iff_square_integrable T hT hsa (x : H)).mp x.2
  have hsq_int : Integrable (fun s : ℝ => s ^ 2) μ := by
    convert hsq_int_complex.norm using 1
    ext s
    simp [Complex.norm_real, sq_abs]
  let tail : ℕ → ℝ → ℝ := fun N s =>
    s ^ 2 * Set.indicator (Set.Icc (-(N : ℝ)) N)ᶜ (fun _ => (1 : ℝ)) s
  have htail_meas : ∀ N, AEStronglyMeasurable (tail N) μ := by
    intro N
    exact ((measurable_id.pow_const 2).mul
      (measurable_const.indicator (measurableSet_Icc.compl))).aestronglyMeasurable
  have htail_dom : ∀ N, ∀ᵐ s ∂μ, ‖tail N s‖ ≤ s ^ 2 := by
    intro N
    filter_upwards with s
    by_cases hs : s ∈ Set.Icc (-(N : ℝ)) N
    · simp [tail, hs, sq_nonneg s]
    · simp [tail, hs]
  have htail_pw : ∀ s : ℝ, Tendsto (fun N => tail N s) atTop (nhds 0) := by
    intro s
    have h_ev : ∀ᶠ N in atTop, tail N s = 0 := by
      obtain ⟨N, hN⟩ := exists_nat_ge |s|
      filter_upwards [Filter.Ici_mem_atTop N] with m hm
      have hs_mem : s ∈ Set.Icc (-(m : ℝ)) (m : ℝ) := by
        constructor <;> linarith [abs_nonneg s, neg_abs_le s, le_abs_self s,
          show (N : ℝ) ≤ (m : ℝ) from Nat.cast_le.mpr hm]
      simp [tail, hs_mem]
    exact tendsto_nhds_of_eventually_eq h_ev
  have htail_tend :
      Tendsto (fun N => ∫ s : ℝ, tail N s ∂μ) atTop (nhds 0) := by
    simpa using
      (MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun s : ℝ => s ^ 2) htail_meas hsq_int htail_dom (Eventually.of_forall htail_pw))
  rw [Metric.tendsto_atTop] at htail_tend
  obtain ⟨Ntail, hNtail⟩ := htail_tend ((c / 4) ^ 2) (by positivity)
  set n := max Ntrunc Ntail
  have h_trunc_close : ‖spectralTruncation T hT hsa n (x : H) - T x‖ < c / 2 := by
    have := hNtrunc n (le_max_left _ _); rwa [dist_eq_norm] at this
  set T_n := spectralTruncation T hT hsa n
  -- Key spectral estimate for fixed n: the truncated error is o(h).
  -- U(h)x - x - h*(I*T_n x) = fc(g_{h,n})(x)
  -- where g_{h,n}(s) = exp(ihs) - 1 - ihs*chi_{[-n,n]}(s).
  -- By functionalCalculus_norm_sq, norm(fc(g)x)^2 = integral |g|^2 dmu_x.
  -- Pointwise bounds give integral <= h^4*n^4*norm(x)^2/4 + h^2*tail_n
  -- where tail_n -> 0 as n -> inf.
  -- So norm(error) <= |h|*sqrt(h^2*C + tail_n) <= (c/2)*|h| for small h.
  have h_spectral_littleO : ∀ᶠ h in nhds (0 : ℝ),
      ‖U h (x : H) - (x : H) - h • (Complex.I • T_n (x : H))‖ ≤ c / 2 * ‖h‖ := by
    let I : Set ℝ := Set.Icc (-(n : ℝ)) n
    let f_n : ℝ → ℂ := fun s =>
      (↑s : ℂ) * Set.indicator I (fun _ => (1 : ℂ)) s
    have hf_norm : ∀ s : ℝ, ‖f_n s‖ ≤ n := by
      intro s
      simp only [f_n, I, Set.indicator_apply]
      split_ifs with hs
      · simp only [mul_one, Complex.norm_real]
        exact abs_le.mpr (Set.mem_Icc.mp hs)
      · simp
    have hf_meas : Measurable f_n :=
      (Complex.continuous_ofReal.measurable).mul
        (measurable_const.indicator measurableSet_Icc)
    have hf_int : ∀ z : H, Integrable f_n (P.diagonalMeasure z) := by
      intro z
      haveI := P.diagonalMeasure_isFiniteMeasure z
      exact (MeasureTheory.integrable_const ((n : ℂ))).mono
        hf_meas.aestronglyMeasurable
        (by
          filter_upwards with s
          simp only [Complex.norm_natCast]
          exact hf_norm s)
    have hf_bdd : ∃ M, 0 ≤ M ∧ ∀ s, ‖f_n s‖ ≤ M := ⟨n, Nat.cast_nonneg n, hf_norm⟩
    have htail_small : ∫ s : ℝ, tail n s ∂μ < (c / 4) ^ 2 := by
      have htail_nonneg : 0 ≤ ∫ s : ℝ, tail n s ∂μ := by
        refine MeasureTheory.integral_nonneg_of_ae ?_
        filter_upwards with s
        by_cases hs : s ∈ Set.Icc (-(n : ℝ)) n
        · simp [tail, hs]
        · simp [tail, hs]
          exact sq_nonneg s
      have htail_dist := hNtail n (le_max_right _ _)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg htail_nonneg] at htail_dist
      exact htail_dist
    let quot0 : ℝ → ℝ → ℂ := fun h s =>
      if h = 0 then Complex.I * (s : ℂ)
      else (Complex.exp (Complex.I * ↑h * ↑s) - 1) / (h : ℂ)
    let Q : ℝ → ℝ → ℝ := fun h s =>
      ‖quot0 h s - Complex.I * f_n s‖ ^ 2
    have hquot0_tend : ∀ s : ℝ,
        Tendsto (fun h => quot0 h s) (nhds 0) (nhds (Complex.I * (s : ℂ))) := by
      intro s
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hbound :
          ∀ᶠ h in nhds (0 : ℝ),
            ‖quot0 h s - Complex.I * (s : ℂ)‖ ≤ ‖h‖ * s ^ 2 := by
        let δ : ℝ := (max ‖s‖ 1)⁻¹
        have hδpos : 0 < δ := by
          unfold δ
          positivity
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδpos] with h hh
        by_cases h0 : h = 0
        · simp [quot0, h0]
        · have hh' : ‖h‖ < δ := by
            simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hh
          have hz_lt : ‖Complex.I * ↑h * ↑s‖ < 1 := by
            have hs_le : ‖s‖ ≤ max ‖s‖ 1 := le_max_left _ _
            have hδ_eq : δ * max ‖s‖ 1 = 1 := by
              unfold δ
              field_simp [show (max ‖s‖ 1 : ℝ) ≠ 0 by positivity]
            calc
              ‖Complex.I * ↑h * ↑s‖ = ‖h‖ * ‖s‖ := by
                simp
              _ ≤ ‖h‖ * max ‖s‖ 1 := mul_le_mul_of_nonneg_left hs_le (norm_nonneg _)
              _ < δ * max ‖s‖ 1 := by gcongr
              _ = 1 := hδ_eq
          have hz : ‖Complex.I * ↑h * ↑s‖ ≤ 1 := hz_lt.le
          have hrem := Complex.norm_exp_sub_one_sub_id_le (x := Complex.I * ↑h * ↑s) hz
          have hcalc :
              ‖quot0 h s - Complex.I * (s : ℂ)‖
                = ‖Complex.exp (Complex.I * ↑h * ↑s) - 1 - Complex.I * ↑h * ↑s‖ / ‖h‖ := by
            rw [show quot0 h s = (Complex.exp (Complex.I * ↑h * ↑s) - 1) / (h : ℂ) by
              simp [quot0, h0]]
            have : (Complex.exp (Complex.I * ↑h * ↑s) - 1) / (h : ℂ) - Complex.I * (s : ℂ) =
                (Complex.exp (Complex.I * ↑h * ↑s) - 1 - Complex.I * ↑h * ↑s) / (h : ℂ) := by
              field_simp [h0]
            rw [this, norm_div]
            simp
          rw [hcalc]
          calc
            ‖Complex.exp (Complex.I * ↑h * ↑s) - 1 - Complex.I * ↑h * ↑s‖ / ‖h‖
                ≤ ‖Complex.I * ↑h * ↑s‖ ^ 2 / ‖h‖ := by
                  exact div_le_div_of_nonneg_right hrem (norm_nonneg _)
            _ = ‖h‖ * s ^ 2 := by
                  have hsq : ‖Complex.I * ↑h * ↑s‖ = ‖h‖ * ‖s‖ := by
                    simp
                  have hh_pos : 0 < ‖h‖ := norm_pos_iff.mpr h0
                  rw [hsq]
                  calc
                    (‖h‖ * ‖s‖) ^ 2 / ‖h‖ = ‖h‖ * ‖s‖ ^ 2 := by
                      field_simp [hh_pos.ne']
                    _ = ‖h‖ * s ^ 2 := by
                      congr 1
                      simp [Real.norm_eq_abs]
      have h_rhs : Tendsto (fun h : ℝ => ‖h‖ * s ^ 2) (nhds 0) (nhds 0) := by
        simpa using ((continuous_norm.mul continuous_const).continuousAt.tendsto :
          Tendsto (fun h : ℝ => ‖h‖ * s ^ 2) (nhds 0) (nhds (‖(0 : ℝ)‖ * s ^ 2)))
      exact squeeze_zero' (Eventually.of_forall fun h => norm_nonneg _) hbound h_rhs
    have hQ_meas : ∀ᶠ h in nhds (0 : ℝ), AEStronglyMeasurable (Q h) μ := by
      filter_upwards with h
      have hquot_meas : Measurable (quot0 h) := by
        by_cases h0 : h = 0
        · simpa [quot0, h0] using (continuous_const.mul Complex.continuous_ofReal).measurable
        · simpa [quot0, h0] using (((expI_measurable h).sub measurable_const).div_const (h : ℂ))
      exact ((hquot_meas.sub (measurable_const.mul hf_meas)).norm.pow_const 2).aestronglyMeasurable
    have hQ_bound : ∀ᶠ h in nhds (0 : ℝ), ∀ᵐ s ∂μ, ‖Q h s‖ ≤ 4 * s ^ 2 := by
      filter_upwards with h
      filter_upwards with s
      have hquot_le :
          ‖quot0 h s‖ ≤ ‖s‖ := by
        by_cases h0 : h = 0
        · simp [quot0, h0]
        · rw [show quot0 h s = (Complex.exp (Complex.I * ↑h * ↑s) - 1) / (h : ℂ) by
              simp [quot0, h0]]
          calc
            ‖(Complex.exp (Complex.I * ↑h * ↑s) - 1) / (h : ℂ)‖
                = ‖Complex.exp (Complex.I * ↑h * ↑s) - 1‖ / ‖(h : ℂ)‖ := by rw [norm_div]
            _ ≤ ‖Complex.I * ↑h * ↑s‖ / ‖(h : ℂ)‖ := by
                  gcongr
                  simpa [mul_assoc, mul_comm, mul_left_comm] using
                    Real.norm_exp_I_mul_ofReal_sub_one_le (x := h * s)
            _ = ‖s‖ := by
                  have hh_nonzero : ‖(h : ℂ)‖ ≠ 0 := by simp [h0]
                  rw [show ‖Complex.I * ↑h * ↑s‖ = ‖(h : ℂ)‖ * ‖s‖ by
                    simp [mul_comm, mul_left_comm]]
                  field_simp [hh_nonzero]
      have hf_le : ‖Complex.I * f_n s‖ ≤ ‖s‖ := by
        calc
          ‖Complex.I * f_n s‖ = ‖f_n s‖ := by simp
          _ ≤ ‖s‖ := by
            by_cases hs : s ∈ I
            · simp [f_n, hs, I]
            · simp [f_n, hs, I]
      have hsum : ‖quot0 h s - Complex.I * f_n s‖ ≤ 2 * ‖s‖ := by
        calc
          ‖quot0 h s - Complex.I * f_n s‖ ≤ ‖quot0 h s‖ + ‖Complex.I * f_n s‖ := norm_sub_le _ _
          _ ≤ ‖s‖ + ‖s‖ := add_le_add hquot_le hf_le
          _ = 2 * ‖s‖ := by ring
      have hnonneg : 0 ≤ ‖quot0 h s - Complex.I * f_n s‖ := norm_nonneg _
      calc
        ‖Q h s‖ = ‖quot0 h s - Complex.I * f_n s‖ ^ 2 := by simp [Q]
        _ ≤ (2 * ‖s‖) ^ 2 := by gcongr
        _ = 4 * s ^ 2 := by
          have hsq : ‖s‖ ^ 2 = s ^ 2 := by
            simp [Real.norm_eq_abs]
          nlinarith
    have hQ_int :
        Tendsto (fun h : ℝ => ∫ s : ℝ, Q h s ∂μ) (nhds 0)
          (nhds (∫ s : ℝ, Q 0 s ∂μ)) :=
      MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (fun s : ℝ => 4 * s ^ 2) hQ_meas hQ_bound
        (hsq_int.const_mul 4) <|
          Eventually.of_forall fun s =>
            by
              have hcont : Continuous fun z : ℂ => ‖z - Complex.I * f_n s‖ ^ 2 :=
                (continuous_norm.comp (continuous_id.sub continuous_const)).pow 2
              simpa [Q, quot0] using hcont.continuousAt.tendsto.comp (hquot0_tend s)
    have hQ0_eq_tail : (∫ s : ℝ, Q 0 s ∂μ) = ∫ s : ℝ, tail n s ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards with s
      by_cases hs : s ∈ I
      · simp [Q, quot0, tail, f_n, hs, I]
      · simp [Q, quot0, tail, f_n, hs, I, Complex.norm_I, sq_abs]
    have hQ_ev : ∀ᶠ h in nhds (0 : ℝ), ∫ s : ℝ, Q h s ∂μ < (c / 2) ^ 2 := by
      rw [hQ0_eq_tail] at hQ_int
      have hlim_small : ∫ s : ℝ, tail n s ∂μ < (c / 2) ^ 2 := by
        have hq : (c / 4) ^ 2 < (c / 2) ^ 2 := by
          rw [sq_lt_sq₀ (by positivity) (by positivity)]
          linarith
        exact lt_of_lt_of_le htail_small hq.le
      let ε : ℝ := (c / 2) ^ 2 - ∫ s : ℝ, tail n s ∂μ
      have hεpos : 0 < ε := by
        dsimp [ε]
        linarith
      have hQ_ball := hQ_int (Metric.ball_mem_nhds _ hεpos)
      filter_upwards [hQ_ball] with h hh
      have hh' : |∫ s : ℝ, Q h s ∂μ - ∫ s : ℝ, tail n s ∂μ| < ε := by
        simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm, ε] using hh
      have hle : ∫ s : ℝ, Q h s ∂μ - ∫ s : ℝ, tail n s ∂μ < ε := by
        exact (abs_lt.mp hh').2
      dsimp [ε] at hle ⊢
      linarith
    filter_upwards [hQ_ev] with h hQh
    by_cases h0 : h = 0
    · simp [h0, hU0]
    · let e_h : ℝ → ℂ := fun s => Complex.exp (Complex.I * ↑h * ↑s)
      let g_h : ℝ → ℂ := fun s => (e_h s - 1) - ((((h : ℂ) * Complex.I) • f_n) s)
      have he_int : ∀ z : H, Integrable e_h (P.diagonalMeasure z) := fun z => expI_integrable P h z
      have he_bdd : ∃ M, 0 ≤ M ∧ ∀ s, ‖e_h s‖ ≤ M := ⟨1, zero_le_one, expI_norm_le h⟩
      have h1_int : ∀ z : H, Integrable (fun _ : ℝ => (1 : ℂ)) (P.diagonalMeasure z) := by
        intro z
        haveI := P.diagonalMeasure_isFiniteMeasure z
        exact MeasureTheory.integrable_const 1
      have h1_bdd : ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, ‖(1 : ℂ)‖ ≤ M := by
        refine ⟨1, zero_le_one, ?_⟩
        intro s
        simp
      have hcf_int : ∀ z : H, Integrable ((((h : ℂ) * Complex.I) • f_n)) (P.diagonalMeasure z) := by
        intro z
        exact (hf_int z).const_mul (((h : ℂ) * Complex.I))
      have hcf_bdd : ∃ M, 0 ≤ M ∧ ∀ s, ‖((((h : ℂ) * Complex.I) • f_n) s)‖ ≤ M := by
        refine ⟨‖(h : ℂ) * Complex.I‖ * n, mul_nonneg (norm_nonneg _) (Nat.cast_nonneg n), ?_⟩
        intro s
        calc
          ‖((((h : ℂ) * Complex.I) • f_n) s)‖ = ‖(h : ℂ) * Complex.I‖ * ‖f_n s‖ := by
            simp [Pi.smul_apply]
          _ ≤ ‖(h : ℂ) * Complex.I‖ * n :=
            mul_le_mul_of_nonneg_left (hf_norm s) (norm_nonneg _)
      have hsub1_int : ∀ z : H, Integrable (fun s => e_h s - 1) (P.diagonalMeasure z) := by
        intro z
        exact (he_int z).sub (h1_int z)
      have hg_int : ∀ z : H, Integrable g_h (P.diagonalMeasure z) := by
        intro z
        have htmp : Integrable (((fun s => e_h s - 1) - (((h : ℂ) * Complex.I) • f_n)))
            (P.diagonalMeasure z) := (hsub1_int z).sub (hcf_int z)
        simpa [g_h] using htmp
      have hg_bdd : ∃ M, 0 ≤ M ∧ ∀ s, ‖g_h s‖ ≤ M := by
        refine ⟨2 + ‖(h : ℂ) * Complex.I‖ * n, by positivity, ?_⟩
        intro s
        have hfle := hf_norm s
        calc
          ‖g_h s‖ ≤ ‖e_h s‖ + ‖(1 : ℂ) + (((h : ℂ) * Complex.I) * f_n s)‖ := by
            simpa [g_h, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
              (norm_sub_le (e_h s) ((1 : ℂ) + (((h : ℂ) * Complex.I) * f_n s)))
          _ ≤ ‖e_h s‖ + (‖(1 : ℂ)‖ + ‖(((h : ℂ) * Complex.I) * f_n s)‖) := by
            gcongr
            exact norm_add_le _ _
          _ ≤ 1 + (1 + ‖(h : ℂ) * Complex.I‖ * n) := by
            gcongr
            · exact expI_norm_le h s
            · simp
            · calc
                ‖(((h : ℂ) * Complex.I) * f_n s)‖ = ‖(h : ℂ) * Complex.I‖ * ‖f_n s‖ := by
                  simp
                _ ≤ ‖(h : ℂ) * Complex.I‖ * n :=
                  mul_le_mul_of_nonneg_left hfle (norm_nonneg _)
          _ = 2 + ‖(h : ℂ) * Complex.I‖ * n := by ring
      have hg_meas : Measurable g_h := by
        have htmp : Measurable (fun s : ℝ => e_h s - 1 - (((h : ℂ) * Complex.I) • f_n) s) :=
          ((expI_measurable h).sub measurable_const).sub (measurable_const.mul hf_meas)
        simpa [g_h, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using htmp
      have hsub1_bdd : ∃ M, 0 ≤ M ∧ ∀ s, ‖e_h s - 1‖ ≤ M := by
        refine ⟨2, by positivity, ?_⟩
        intro s
        calc ‖e_h s - 1‖ ≤ ‖e_h s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ ≤ 1 + 1 := by
              gcongr
              · exact expI_norm_le h s
              · simp
          _ = 2 := by ring
      have hfc_sub1 := P.functionalCalculus_sub e_h (fun _ : ℝ => (1 : ℂ))
        he_int he_bdd h1_int h1_bdd hsub1_int hsub1_bdd
      have hfc_smul := P.functionalCalculus_smul (((h : ℂ) * Complex.I)) f_n
        hf_int hf_bdd hcf_int hcf_bdd
      have hfc_g := P.functionalCalculus_sub (fun s => e_h s - 1) ((((h : ℂ) * Complex.I) • f_n))
        hsub1_int hsub1_bdd hcf_int hcf_bdd hg_int hg_bdd
      have herr_apply :
          functionalCalculus P g_h hg_int hg_bdd x =
            U h (x : H) - (x : H) - h • (Complex.I • T_n (x : H)) := by
        have hfc_sub1_apply :
            functionalCalculus P (fun s => e_h s - 1) hsub1_int hsub1_bdd x =
              U h (x : H) - (x : H) := by
          simpa [unitaryGroup_zero, functionalCalculus_const_one_eq_id P,
            ContinuousLinearMap.sub_apply] using
            congrArg (fun A : H →L[ℂ] H => A x) hfc_sub1
        have hfc_smul_apply :
            functionalCalculus P (((h : ℂ) * Complex.I) • f_n) hcf_int hcf_bdd x =
              h • (Complex.I • T_n (x : H)) := by
          calc
            functionalCalculus P (((h : ℂ) * Complex.I) • f_n) hcf_int hcf_bdd x
                = ((h : ℂ) * Complex.I) • functionalCalculus P f_n hf_int hf_bdd x := by
                    simpa using congrArg (fun A : H →L[ℂ] H => A x) hfc_smul
            _ = ((h : ℂ) * Complex.I) • T_n (x : H) := by
                  rfl
            _ = (h • Complex.I) • T_n (x : H) := by
                  simp [Algebra.smul_def]
            _ = h • (Complex.I • T_n (x : H)) := by
                  simpa using (smul_assoc h Complex.I (T_n (x : H)))
        have hfc_g_apply :
            functionalCalculus P (((fun s => e_h s - 1) - (((h : ℂ) * Complex.I) • f_n))) hg_int hg_bdd x =
              functionalCalculus P (fun s => e_h s - 1) hsub1_int hsub1_bdd x -
                functionalCalculus P (((h : ℂ) * Complex.I) • f_n) hcf_int hcf_bdd x := by
          simpa [ContinuousLinearMap.sub_apply] using congrArg (fun A : H →L[ℂ] H => A x) hfc_g
        calc
          functionalCalculus P g_h hg_int hg_bdd x
              = functionalCalculus P (((fun s => e_h s - 1) - (((h : ℂ) * Complex.I) • f_n))) hg_int hg_bdd x := by
                  rfl
          _ = functionalCalculus P (fun s => e_h s - 1) hsub1_int hsub1_bdd x -
                functionalCalculus P (((h : ℂ) * Complex.I) • f_n) hcf_int hcf_bdd x := hfc_g_apply
          _ = U h (x : H) - (x : H) - h • (Complex.I • T_n (x : H)) := by
                rw [hfc_sub1_apply, hfc_smul_apply]
      have hnorm_sq := functionalCalculus_norm_sq' P g_h hg_int hg_bdd hg_meas (x : H)
      rw [herr_apply] at hnorm_sq
      have hQ_eq :
          ∫ s : ℝ, ‖g_h s‖ ^ 2 ∂μ = ‖h‖ ^ 2 * ∫ s : ℝ, Q h s ∂μ := by
        calc
          ∫ s : ℝ, ‖g_h s‖ ^ 2 ∂μ = ∫ s : ℝ, (‖h‖ ^ 2) * Q h s ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards with s
            have hgfac :
                g_h s = (h : ℂ) * (quot0 h s - Complex.I * f_n s) := by
              rw [show quot0 h s = (Complex.exp (Complex.I * ↑h * ↑s) - 1) / (h : ℂ) by
                    simp [quot0, h0]]
              simp [g_h, e_h]
              field_simp [h0]
            rw [hgfac, norm_mul]
            simp [Q]
            have hh_sq : ‖h‖ ^ 2 = h ^ 2 := by
              simp [Real.norm_eq_abs]
            calc
              (‖h‖ * ‖quot0 h s - Complex.I * f_n s‖) ^ 2
                  = ‖h‖ ^ 2 * ‖quot0 h s - Complex.I * f_n s‖ ^ 2 := by ring
              _ = h ^ 2 * ‖quot0 h s - Complex.I * f_n s‖ ^ 2 := by rw [hh_sq]
          _ = ‖h‖ ^ 2 * ∫ s : ℝ, Q h s ∂μ := by
              rw [MeasureTheory.integral_const_mul]
      rw [hQ_eq] at hnorm_sq
      have hnorm_le_sq : ‖U h (x : H) - (x : H) - h • (Complex.I • T_n (x : H))‖ ^ 2
          < (c / 2 * ‖h‖) ^ 2 := by
        calc
          ‖U h (x : H) - (x : H) - h • (Complex.I • T_n (x : H))‖ ^ 2
              = ‖h‖ ^ 2 * ∫ s : ℝ, Q h s ∂μ := hnorm_sq
          _ < ‖h‖ ^ 2 * (c / 2) ^ 2 := by
              have hhpos : 0 < ‖h‖ ^ 2 := by
                positivity
              exact mul_lt_mul_of_pos_left hQh hhpos
          _ = (c / 2 * ‖h‖) ^ 2 := by ring
      have hnonneg_left : 0 ≤ ‖U h (x : H) - (x : H) - h • (Complex.I • T_n (x : H))‖ := norm_nonneg _
      have hnonneg_right : 0 ≤ c / 2 * ‖h‖ := by positivity
      exact le_of_lt ((sq_lt_sq₀ hnonneg_left hnonneg_right).mp hnorm_le_sq)
  -- Combine: triangle inequality + spectral truncation approximation
  filter_upwards [h_spectral_littleO] with h h_bound1
  have h_decomp : U h (x : H) - (x : H) - h • (Complex.I • T x) =
      (U h (x : H) - (x : H) - h • (Complex.I • T_n (x : H))) +
      h • (Complex.I • (T_n (x : H) - T x)) := by
    simp only [smul_sub]; abel
  rw [h_decomp]
  calc ‖(U h (x : H) - (x : H) - h • (Complex.I • T_n (x : H))) +
        h • (Complex.I • (T_n (x : H) - T x))‖
      ≤ ‖U h (x : H) - (x : H) - h • (Complex.I • T_n (x : H))‖ +
        ‖h • (Complex.I • (T_n (x : H) - T x))‖ :=
        norm_add_le _ _
    _ = ‖U h (x : H) - (x : H) - h • (Complex.I • T_n (x : H))‖ +
        ‖h‖ * (‖Complex.I‖ * ‖T_n (x : H) - T x‖) := by
        rw [norm_smul, norm_smul]
    _ = ‖U h (x : H) - (x : H) - h • (Complex.I • T_n (x : H))‖ +
        ‖h‖ * ‖T_n (x : H) - T x‖ := by
        rw [Complex.norm_I, one_mul]
    _ ≤ c / 2 * ‖h‖ + ‖h‖ * ‖T_n (x : H) - T x‖ := by linarith
    _ ≤ c / 2 * ‖h‖ + ‖h‖ * (c / 2) := by
        have : ‖h‖ * ‖T_n (x : H) - T x‖ ≤ ‖h‖ * (c / 2) :=
          mul_le_mul_of_nonneg_left (le_of_lt h_trunc_close) (norm_nonneg _)
        linarith
    _ = c * ‖h‖ := by ring

set_option maxHeartbeats 800000 in
/-- **Spectral differentiation (Reed-Simon VIII.7(c), Rudin FA 13.33).**
    For x ∈ dom(T), d/dt U(t)x = i · U(t)(Tx).
    Proved by reducing to `unitaryGroup_hasDerivAt_zero` via the group law and isometry. -/
theorem unitaryGroup_hasDerivAt_dom (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (x : T.domain) (t : ℝ) :
    HasDerivAt (fun s => unitaryGroup T hT hsa s (x : H))
      (Complex.I • unitaryGroup T hT hsa t (T x)) t := by
  /-
  PROOF: Reduce to derivative at 0 using group law + isometry.

  Key identity: U(t+h)x - U(t)x = U(t)(U(h)x - U(0)x), so
    ‖U(t+h)x - U(t)x - h•(i·U(t)(Tx))‖ = ‖U(t)(U(h)x - U(0)x - h•(iTx))‖
    = ‖U(h)x - U(0)x - h•(iTx)‖   (U(t) is isometric).
  Therefore HasDerivAt at t reduces to HasDerivAt at 0.
  -/
  set U := unitaryGroup T hT hsa
  -- Step 1: derivative at 0
  have hderiv0 := unitaryGroup_hasDerivAt_zero T hT hsa x
  -- Step 2: use nhds-0-centered isLittleO characterization for both
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at hderiv0 ⊢
  -- hderiv0: (fun h => U(0+h)x - U(0)x - h•(I•Tx)) =o[nhds 0] h
  -- Goal:    (fun h => U(t+h)x - U(t)x - h•(I•U(t)(Tx))) =o[nhds 0] h
  have hU0 : U 0 (x : H) = (x : H) := by
    show (unitaryGroup T hT hsa 0) (x : H) = (x : H)
    rw [unitaryGroup_zero]; simp
  -- Key: the error at t equals U(t) applied to the error at 0 (in norm)
  -- error(h) = U(t+h)x - U(t)x - h•(I•U(t)(Tx))
  --          = U(t)(U(h)x - x) - U(t)(h•(I•Tx))    [group law + linearity]
  --          = U(t)(U(h)x - x - h•(I•Tx))            [linearity of U(t)]
  -- So ‖error(h)‖ = ‖U(h)x - x - h•(I•Tx)‖ by isometry.
  -- Thus the isLittleO at t reduces to the isLittleO at 0.
  have herr_eq : ∀ h : ℝ,
      ‖U (t + h) (x : H) - U t (x : H) - h • (Complex.I • U t (T x))‖ =
      ‖U (0 + h) (x : H) - U 0 (x : H) - h • (Complex.I • T x)‖ := by
    intro h
    -- Group law: U(t+h) = U(t) ∘ U(h)
    have hcomp : U (t + h) = U t ∘L U h := by
      rw [unitaryGroup_mul]
    -- Factor: U(t+h)x - U(t)x = U(t)(U(h)x) - U(t)x = U(t)(U(h)x - x)
    have hfactor : U (t + h) (x : H) - U t (x : H) =
        U t (U h (x : H) - (x : H)) := by
      rw [hcomp, ContinuousLinearMap.comp_apply, map_sub]
    -- ℝ-smul to ℂ-smul conversion for linearity
    have hreal_smul : ∀ (r : ℝ) (v : H), r • v = (r : ℂ) • v :=
      fun r v => (algebraMap_smul ℂ r v).symm
    -- h•(I•U(t)(Tx)) = U(t)(h•(I•Tx)) by ℂ-linearity
    have hlin : h • (Complex.I • U t (T x)) =
        U t (h • (Complex.I • T x)) := by
      rw [hreal_smul h (Complex.I • U t (T x)),
          hreal_smul h (Complex.I • T x),
          map_smul, map_smul]
    -- Combine: error = U(t)(U(h)x - x - h•(I•Tx))
    have herr : U (t + h) (x : H) - U t (x : H) - h • (Complex.I • U t (T x)) =
        U t (U h (x : H) - (x : H) - h • (Complex.I • T x)) := by
      rw [hfactor, hlin, ← map_sub]
    -- Norm preservation: ‖U(t) v‖ = ‖v‖
    have hnorm_pres : ∀ v : H, ‖U t v‖ = ‖v‖ := by
      intro v
      have h_adj_comp : ContinuousLinearMap.adjoint (U t) ∘L U t = 1 := by
        rw [unitaryGroup_inv, unitaryGroup_neg_comp]
      have h_inner_eq : @inner ℂ H _ (U t v) (U t v) = @inner ℂ H _ v v := by
        rw [← ContinuousLinearMap.adjoint_inner_right (U t) v (U t v),
            ← ContinuousLinearMap.comp_apply, h_adj_comp, ContinuousLinearMap.one_apply]
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h_inner_eq
      have h_sq : ‖U t v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast h_inner_eq
      calc ‖U t v‖ = Real.sqrt (‖U t v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ = Real.sqrt (‖v‖ ^ 2) := by rw [h_sq]
        _ = ‖v‖ := Real.sqrt_sq (norm_nonneg _)
    rw [herr, hnorm_pres, hU0, show (0 : ℝ) + h = h from zero_add h]
  -- Now use herr_eq to transport the isLittleO from 0 to t
  rw [Asymptotics.isLittleO_iff] at hderiv0 ⊢
  intro c hc
  have h0 := hderiv0 hc
  exact h0.mono (fun h hh => by rw [herr_eq]; exact hh)

/-- The spectral unitary group preserves the domain of T.

    **Proof sketch (not formalized):**
    U(t) = ∫ exp(itλ) dP(λ) and dom(T) = {x : ∫ λ² d⟨P(λ)x, x⟩ < ∞}.
    Since |exp(itλ)| = 1, U(t) commutes with P(E) for every Borel E,
    so ∫ λ² d⟨P(λ)U(t)x, U(t)x⟩ = ∫ λ² d⟨P(λ)x, x⟩ < ∞.
    Hence U(t)x ∈ dom(T). -/
theorem unitaryGroup_preserves_domain (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (x : T.domain) (t : ℝ) :
    unitaryGroup T hT hsa t (x : H) ∈ T.domain := by
  -- By mem_domain_iff_square_integrable, it suffices to show ∫ λ² dμ_{U(t)x} < ∞.
  -- By diagonalMeasure_unitaryGroup_invariant, μ_{U(t)x} = μ_x.
  -- Since x ∈ dom(T), ∫ λ² dμ_x < ∞.
  rw [(mem_domain_iff_square_integrable T hT hsa _)]
  rw [diagonalMeasure_unitaryGroup_invariant]
  exact (mem_domain_iff_square_integrable T hT hsa (x : H)).mp x.2

set_option maxHeartbeats 800000 in
/-- The spectral unitary group commutes with T on dom(T):
    T(U(t)x) = U(t)(Tx) for x ∈ dom(T).

    **Proof sketch (not formalized):**
    Both T and U(t) are functions of the spectral measure P:
    T = ∫ λ dP(λ), U(t) = ∫ exp(itλ) dP(λ).
    Functional calculus gives f(T)g(T) = (fg)(T),
    so U(t)T = T U(t) on dom(T). -/
theorem unitaryGroup_commutes_with_generator (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (x : T.domain) (t : ℝ) :
    T ⟨unitaryGroup T hT hsa t (x : H), unitaryGroup_preserves_domain T hT hsa x t⟩ =
    unitaryGroup T hT hsa t (T x) := by
  set P := T.spectralMeasure hT hsa
  set Utx_dom : T.domain :=
    ⟨unitaryGroup T hT hsa t (x : H), unitaryGroup_preserves_domain T hT hsa x t⟩
  -- Step 1: T_N commutes with U(t) (both are functional calculus operators).
  -- f_N(s) = s · χ_{[-N,N]}(s), e(s) = exp(its)
  let e : ℝ → ℂ := fun s => Complex.exp (Complex.I * ↑t * ↑s)
  let f_N : ℕ → ℝ → ℂ := fun N s =>
    (↑s : ℂ) * Set.indicator (Set.Icc (-(N : ℝ)) N) (fun _ => (1 : ℂ)) s
  have hfN_norm : ∀ N, ∀ s : ℝ, ‖f_N N s‖ ≤ N := by
    intro N s; simp only [f_N, Set.indicator_apply]
    split_ifs with h
    · simp only [mul_one, Complex.norm_real]; exact abs_le.mpr (Set.mem_Icc.mp h)
    · simp
  have hfN_meas : ∀ N, Measurable (f_N N) := by
    intro N; exact (Complex.continuous_ofReal.measurable).mul
      (measurable_const.indicator measurableSet_Icc)
  have hfN_int : ∀ N (z : H), MeasureTheory.Integrable (f_N N) (P.diagonalMeasure z) := by
    intro N z; haveI := P.diagonalMeasure_isFiniteMeasure z
    exact (MeasureTheory.integrable_const ((N : ℂ))).mono
      (hfN_meas N).aestronglyMeasurable
      (by filter_upwards with s; simp only [Complex.norm_natCast]; exact hfN_norm N s)
  have hfN_bdd : ∀ N, ∃ M, 0 ≤ M ∧ ∀ s, ‖f_N N s‖ ≤ M :=
    fun N => ⟨N, Nat.cast_nonneg N, hfN_norm N⟩
  have he_int : ∀ z : H, MeasureTheory.Integrable e (P.diagonalMeasure z) :=
    fun z => expI_integrable P t z
  have he_bdd : ∃ M, 0 ≤ M ∧ ∀ s, ‖e s‖ ≤ M := ⟨1, zero_le_one, expI_norm_le t⟩
  have he_meas : Measurable e := expI_measurable t
  -- Commutativity: spectralTruncation N ∘L U(t) = U(t) ∘L spectralTruncation N
  have h_commute : ∀ N, spectralTruncation T hT hsa N ∘L unitaryGroup T hT hsa t =
      unitaryGroup T hT hsa t ∘L spectralTruncation T hT hsa N := by
    intro N
    -- Product function properties
    have hfe_int : ∀ z : H, MeasureTheory.Integrable (f_N N * e) (P.diagonalMeasure z) := by
      intro z; haveI := P.diagonalMeasure_isFiniteMeasure z
      exact (MeasureTheory.integrable_const ((N : ℂ))).mono
        ((hfN_meas N).mul he_meas).aestronglyMeasurable
        (Eventually.of_forall fun s => by
          simp only [Complex.norm_natCast, Pi.mul_apply]; rw [norm_mul]
          calc ‖f_N N s‖ * ‖e s‖ ≤ N * 1 := by
                exact mul_le_mul (hfN_norm N s) (expI_norm_le t s) (norm_nonneg _) (Nat.cast_nonneg N)
            _ = N := mul_one _)
    have hfe_bdd : ∃ M, 0 ≤ M ∧ ∀ s, ‖(f_N N * e) s‖ ≤ M :=
      ⟨N, Nat.cast_nonneg N, fun s => by
        simp only [Pi.mul_apply]; rw [norm_mul]
        calc ‖f_N N s‖ * ‖e s‖ ≤ N * 1 := by
              exact mul_le_mul (hfN_norm N s) (expI_norm_le t s) (norm_nonneg _) (Nat.cast_nonneg N)
          _ = N := mul_one _⟩
    have hef_int : ∀ z : H, MeasureTheory.Integrable (e * f_N N) (P.diagonalMeasure z) := by
      intro z; rw [show e * f_N N = f_N N * e from by ext s; simp [mul_comm]]; exact hfe_int z
    have hef_bdd : ∃ M, 0 ≤ M ∧ ∀ s, ‖(e * f_N N) s‖ ≤ M := by
      rw [show e * f_N N = f_N N * e from by ext s; simp [mul_comm]]; exact hfe_bdd
    -- fc(f_N * e) = fc(f_N) ∘L fc(e) = T_N ∘L U(t)
    have h1 := functionalCalculus_mul P (f_N N) e (hfN_int N) (hfN_bdd N)
      he_int he_bdd hfe_int hfe_bdd he_meas
    -- fc(e * f_N) = fc(e) ∘L fc(f_N) = U(t) ∘L T_N
    have h2 := functionalCalculus_mul P e (f_N N) he_int he_bdd
      (hfN_int N) (hfN_bdd N) hef_int hef_bdd (hfN_meas N)
    -- fc(f_N * e) = fc(e * f_N) since f_N * e = e * f_N
    have h_eq : functionalCalculus P (f_N N * e) hfe_int hfe_bdd =
        functionalCalculus P (e * f_N N) hef_int hef_bdd :=
      functionalCalculus_congr P (f_N N * e) (e * f_N N) hfe_int hfe_bdd hef_int hef_bdd
        (fun s => by simp [mul_comm])
    -- spectralTruncation = fc(f_N) and unitaryGroup = fc(e) definitionally
    have h_trunc_eq : spectralTruncation T hT hsa N =
        functionalCalculus P (f_N N) (hfN_int N) (hfN_bdd N) := rfl
    have h_unit_eq : unitaryGroup T hT hsa t =
        functionalCalculus P e he_int he_bdd := rfl
    -- T_N ∘L U(t) = U(t) ∘L T_N
    rw [h_trunc_eq, h_unit_eq, ← h1, h_eq, h2]
  -- Step 2: Both sides are limits of the same sequence.
  -- T_N(U(t)x) = (T_N ∘L U(t)) x = (U(t) ∘L T_N) x = U(t)(T_N x)
  have h_seq_eq : ∀ N, spectralTruncation T hT hsa N (unitaryGroup T hT hsa t (x : H)) =
      unitaryGroup T hT hsa t (spectralTruncation T hT hsa N (x : H)) := by
    intro N
    calc spectralTruncation T hT hsa N (unitaryGroup T hT hsa t (x : H))
        = (spectralTruncation T hT hsa N ∘L unitaryGroup T hT hsa t) (x : H) := by
          simp [ContinuousLinearMap.comp_apply]
      _ = (unitaryGroup T hT hsa t ∘L spectralTruncation T hT hsa N) (x : H) := by
          rw [h_commute]
      _ = unitaryGroup T hT hsa t (spectralTruncation T hT hsa N (x : H)) := by
          simp [ContinuousLinearMap.comp_apply]
  -- LHS limit: T_N(U(t)x) → T(U(t)x) by spectralTruncation_tendsto applied to Utx_dom
  have h_lhs : Filter.Tendsto (fun N => spectralTruncation T hT hsa N (unitaryGroup T hT hsa t (x : H)))
      Filter.atTop (nhds (T Utx_dom)) :=
    spectralTruncation_tendsto T hT hsa Utx_dom
  -- RHS limit: U(t)(T_N x) → U(t)(Tx) by spectralTruncation_tendsto + continuity of U(t)
  have h_rhs : Filter.Tendsto (fun N => unitaryGroup T hT hsa t (spectralTruncation T hT hsa N (x : H)))
      Filter.atTop (nhds (unitaryGroup T hT hsa t (T x))) :=
    ((unitaryGroup T hT hsa t).continuous.tendsto _).comp
      (spectralTruncation_tendsto T hT hsa x)
  -- The sequences are equal, so the limits are equal
  have h_eq_seq : (fun N => spectralTruncation T hT hsa N (unitaryGroup T hT hsa t (x : H))) =
      (fun N => unitaryGroup T hT hsa t (spectralTruncation T hT hsa N (x : H))) :=
    funext h_seq_eq
  rw [h_eq_seq] at h_lhs
  exact tendsto_nhds_unique h_lhs h_rhs

/-- Norm preservation for the spectral unitary group:
    ‖unitaryGroup T hT hsa t x‖ = ‖x‖ -/
theorem unitaryGroup_norm_preserving (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (t : ℝ) (x : H) :
    ‖unitaryGroup T hT hsa t x‖ = ‖x‖ := by
  have h_adj_comp : ContinuousLinearMap.adjoint (unitaryGroup T hT hsa t) ∘L
      unitaryGroup T hT hsa t = 1 := by
    rw [unitaryGroup_inv, unitaryGroup_neg_comp]
  have h_inner_eq : @inner ℂ H _ (unitaryGroup T hT hsa t x)
      (unitaryGroup T hT hsa t x) = @inner ℂ H _ x x := by
    rw [← ContinuousLinearMap.adjoint_inner_right (unitaryGroup T hT hsa t) x
      (unitaryGroup T hT hsa t x), ← ContinuousLinearMap.comp_apply,
      h_adj_comp, ContinuousLinearMap.one_apply]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h_inner_eq
  have h_sq : ‖unitaryGroup T hT hsa t x‖ ^ 2 = ‖x‖ ^ 2 := by exact_mod_cast h_inner_eq
  calc ‖unitaryGroup T hT hsa t x‖
      = Real.sqrt (‖unitaryGroup T hT hsa t x‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖x‖ ^ 2) := by rw [h_sq]
    _ = ‖x‖ := Real.sqrt_sq (norm_nonneg _)

/-- **Converse spectral differentiation (Reed-Simon VIII.7(d)).**

    If the generator limit lim_{h→0} h⁻¹(U(h)x - x) exists (in the strong sense),
    then x ∈ dom(T) and the limit equals iTx.

    Equivalently: the generator of the spectrally-constructed unitary group
    exp(itT) has domain EXACTLY equal to dom(T).

    **Proof (not formalized):**
    The limit lim h⁻¹(U(h)x - x) = y exists iff ∫ |λ|² d⟨P(λ)x,x⟩ < ∞
    (by Parseval: ‖h⁻¹(U(h)x - x) - y‖² = ∫ |h⁻¹(e^{ihλ}-1) - iλ|² d⟨Px,x⟩,
    and convergence forces the λ² moment to be finite).
    This is exactly the condition x ∈ dom(T).

    Ref: Reed-Simon, Theorem VIII.7(d); Rudin FA 13.33 -/
theorem unitaryGroup_generator_domain_eq (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (x : H)
    (hx : ∃ y : H, HasDerivAt (fun t => unitaryGroup T hT hsa t x) y 0) :
    x ∈ T.domain := by
  /-
  PROOF via Parseval + Fatou + mem_domain_iff_square_integrable:

  Step 1: HasDerivAt gives boundedness of the difference quotient norms.
    From hx, ‖(U(h)x - x)/h‖ is bounded near 0 (convergent ⟹ bounded).

  Step 2 (Parseval): The spectral norm-squared identity gives
    ‖(U(h)x - x)/h‖² = ∫ |(exp(ihλ)-1)/h|² dμ_x(λ)
    because (U(h)x - x)/h = fc((exp(ih·)-1)/h)(x) and functionalCalculus_norm_sq'
    converts operator norms to spectral integrals.

  Step 3 (Fatou): Pointwise |(exp(ihλ)-1)/h|² → λ², so by Fatou's lemma:
    ∫ λ² dμ_x ≤ liminf_h ∫ |(exp(ihλ)-1)/h|² dμ_x ≤ M²

  Step 4: ∫ λ² dμ_x < ∞, so by mem_domain_iff_square_integrable, x ∈ dom(T).
  -/
  -- Use the backward direction of mem_domain_iff_square_integrable
  rw [mem_domain_iff_square_integrable T hT hsa x]
  set P := T.spectralMeasure hT hsa
  set μ := P.diagonalMeasure x
  haveI hfin : MeasureTheory.IsFiniteMeasure μ := P.diagonalMeasure_isFiniteMeasure x
  obtain ⟨y, hy⟩ := hx
  -- Step 1: HasDerivAt gives isBigO: ‖U(h)x - x‖ ≤ C·|h| near 0
  have hbigO := hy.isBigO_sub
  have hU0 : unitaryGroup T hT hsa 0 x = x := by rw [unitaryGroup_zero]; simp
  simp only [hU0, sub_zero] at hbigO
  -- hbigO : (fun h => U(h)x - x) =O[nhds 0] id
  obtain ⟨C, hC⟩ := hbigO.bound
  -- hC : ∀ᶠ h in nhds 0, ‖U(h)x - x‖ ≤ C * ‖h‖
  -- Step 2: By unitaryGroup_diff_norm_sq (proved above), for every h:
  --   ‖U(h)x - x‖² = ∫ |exp(ihλ)-1|² dμ_x
  -- Step 3: For h near 0, combining with hC:
  --   ∫ |exp(ihλ)-1|² dμ_x = ‖U(h)x - x‖² ≤ (C·|h|)² = C²h²
  -- Step 4: ∫ |(exp(ihλ)-1)/h|² dμ_x = (1/h²)·∫|exp(ihλ)-1|²dμ_x ≤ C²
  -- Step 5: Fatou (MeasureTheory.lintegral_liminf_le) applied to h_n = 1/(n+1):
  --   ∫ liminf_n |(exp(ih_nλ)-1)/h_n|² dμ_x ≤ liminf_n C² = C²
  -- Step 6: Pointwise liminf_n |(exp(ih_nλ)-1)/h_n|² = λ²
  --   (since (exp(ixλ)-1)/x → iλ, so |(exp(ixλ)-1)/x|² → λ²)
  -- Step 7: ∫ λ² dμ_x ≤ C² < ∞
  --
  -- All ingredients are now available:
  --   - unitaryGroup_diff_norm_sq gives the Parseval identity (step 2)
  --   - MeasureTheory.lintegral_liminf_le gives Fatou's lemma (step 5)
  --   - The pointwise convergence is elementary complex analysis (step 6)
  -- Step 2-7: Use Parseval + Fatou via integrable_of_tendsto
  -- Define h_n = 1/(n+1) → 0
  let h_seq : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have h_seq_pos : ∀ n, 0 < h_seq n := by
    intro n; simp only [h_seq]; positivity
  have h_seq_ne_zero : ∀ n, h_seq n ≠ 0 := fun n => ne_of_gt (h_seq_pos n)
  -- G_n(s) = ‖exp(i·h_n·s) - 1‖² / h_n²
  let G : ℕ → ℝ → ℝ := fun n s =>
    ‖Complex.exp (Complex.I * ↑(h_seq n) * ↑s) - 1‖ ^ 2 / (h_seq n) ^ 2
  -- G_n → s² pointwise
  have hGf : ∀ᵐ s ∂μ, Filter.Tendsto (fun n => G n s) Filter.atTop (nhds (s ^ 2)) := by
    filter_upwards with s
    simp only [G]
    -- We need: ‖exp(I*h_n*s) - 1‖²/h_n² → s²
    -- Key: (exp(I*h*s) - 1)/h → I*s as h → 0 (derivative of exp(I·s·t) at t=0)
    -- Then ‖(exp(I*h*s)-1)/h‖² → ‖I*s‖² = s²
    -- Step 1: (exp(I*h*s) - 1)/h → I*s
    -- This is a standard consequence of exp'(0) = 1, composed with linear maps.
    -- Proof: exp(I*h*s) = 1 + I*h*s + O(h²), so (exp(I*h*s)-1)/h = I*s + O(h) → I*s
    have h_quot_tend : Tendsto (fun n => (Complex.exp (Complex.I * ↑(h_seq n) * ↑s) - 1) / ↑(h_seq n))
        atTop (nhds (Complex.I * ↑s)) := by
      -- HasDerivAt for exp at 0: (exp(h)-1)/h → 1 as h → 0
      -- Substituting h = I*s*t: (exp(I*s*t)-1)/(I*s*t) → 1
      -- So (exp(I*s*t)-1)/t → I*s
      -- Use hasDerivAt_exp composition with linear map.
      -- f(t) = exp(I*s*t), f(0) = 1, f'(0) = I*s (by chain rule)
      -- HasDerivAt.tendsto_slope gives Tendsto (slope f 0) (𝓝[≠] 0) (𝓝 (I*s))
      -- slope f 0 h = (f(h) - f(0))/(h-0) = (exp(I*s*h)-1)/h
      -- Compose with h_seq_tend via ofReal cast
      let c := Complex.I * (↑s : ℂ)
      -- Step 1: HasDerivAt (fun t : ℂ => exp(c*t)) c 0
      have hd : HasDerivAt (fun t : ℂ => Complex.exp (c * t)) c 0 := by
        have h1 : HasDerivAt (fun t : ℂ => c * t) c 0 :=
          (hasDerivAt_id (0 : ℂ)).const_mul c |>.congr_deriv (by ring)
        exact (Complex.hasDerivAt_exp (c * 0)).comp 0 h1 |>.congr_deriv (by
          simp [mul_zero, Complex.exp_zero])
      -- Step 2: tendsto slope at 0
      have h_slope := hd.tendsto_slope
      -- h_slope : Tendsto (slope (fun t => exp(c*t)) 0) (𝓝[≠] 0) (𝓝 c)
      -- slope (fun t => exp(c*t)) 0 h = (exp(c*h) - exp(0)) / (h - 0) = (exp(c*h) - 1) / h
      -- Step 3: compose with h_seq cast to ℂ
      -- h_seq_tend defined later; need to prove here that h_seq n → 0
      have h_seq_tend_local : Tendsto h_seq atTop (nhds 0) := by
        simp only [h_seq, one_div]
        exact tendsto_inv_atTop_zero.comp
          (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      have h_ofReal_tend : Tendsto (fun n => (↑(h_seq n) : ℂ)) atTop (nhds (0 : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 0).comp h_seq_tend_local
      -- h_seq n ≠ 0, so (↑(h_seq n) : ℂ) ∈ {0}ᶜ
      have h_ne : ∀ n, (↑(h_seq n) : ℂ) ≠ 0 := by
        intro n; exact Complex.ofReal_ne_zero.mpr (h_seq_ne_zero n)
      have h_map : Filter.map (fun n => (↑(h_seq n) : ℂ)) atTop ≤ 𝓝[≠] (0 : ℂ) := by
        rw [nhdsWithin]
        refine le_inf h_ofReal_tend (le_principal_iff.mpr ?_)
        simp only [Filter.mem_map, Set.preimage_compl]
        filter_upwards with n
        exact h_ne n
      have h_comp := h_slope.mono_left h_map
      -- Rewrite slope to match the goal
      refine h_comp.congr (fun n => ?_)
      simp only [slope, c, mul_zero, Complex.exp_zero, vsub_eq_sub, sub_zero]
      -- Slope rewriting: slope(f,0)(h) = (f(h)-f(0))/(h-0) vs (exp(I*h*s)-1)/h
      -- These differ only in commutativity I*s*h vs I*h*s and format of division
      have harg : Complex.I * ↑s * ↑(h_seq n) = Complex.I * ↑(h_seq n) * ↑s := by ring
      rw [smul_eq_mul, harg]
      field_simp
    -- Step 2: ‖(exp(I*h_n*s)-1)/h_n‖² → ‖I*s‖² = s²
    have h_norm_sq_tend : Tendsto (fun n => ‖(Complex.exp (Complex.I * ↑(h_seq n) * ↑s) - 1) / ↑(h_seq n)‖ ^ 2)
        atTop (nhds (‖Complex.I * ↑s‖ ^ 2)) :=
      (continuous_pow 2 |>.continuousAt.tendsto.comp
        (continuous_norm.continuousAt.tendsto.comp h_quot_tend))
    have h_norm_Is : ‖Complex.I * (↑s : ℂ)‖ ^ 2 = s ^ 2 := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [h_norm_Is] at h_norm_sq_tend
    -- Step 3: ‖(exp-1)/h‖² = ‖exp-1‖²/h²
    have h_eq_G : ∀ n, ‖(Complex.exp (Complex.I * ↑(h_seq n) * ↑s) - 1) / ↑(h_seq n)‖ ^ 2 =
        ‖Complex.exp (Complex.I * ↑(h_seq n) * ↑s) - 1‖ ^ 2 / (h_seq n) ^ 2 := by
      intro n
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (h_seq_pos n), div_pow]
    simp_rw [h_eq_G] at h_norm_sq_tend
    exact h_norm_sq_tend
  -- G_n is AEStronglyMeasurable
  have hG_meas : ∀ n, MeasureTheory.AEStronglyMeasurable (G n) μ := by
    intro n
    exact ((((Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal))).sub continuous_const).norm.pow 2).div_const _).measurable.aestronglyMeasurable
  -- Bochner bound: ∫ G_n dμ ≤ C²
  -- By unitaryGroup_diff_norm_sq: ‖U(h_n)x - x‖² = ∫ ‖exp(i·h_n·s) - 1‖² dμ
  -- By hC (eventually): ‖U(h_n)x - x‖ ≤ C · ‖h_n‖ for large n
  -- So ∫ ‖exp(i·h_n·s) - 1‖² dμ ≤ C² · h_n²
  -- Thus ∫ G_n dμ = (1/h_n²) · ∫ ‖exp(i·h_n·s) - 1‖² dμ ≤ C²
  have hG_nonneg : ∀ n, 0 ≤ᵐ[μ] G n := by
    intro n; filter_upwards with s
    simp only [G]; positivity
  have hG_int : ∀ n, MeasureTheory.Integrable (G n) μ := by
    intro n
    have h_norm_sq_int : MeasureTheory.Integrable
        (fun s : ℝ => ‖Complex.exp (Complex.I * ↑(h_seq n) * ↑s) - 1‖ ^ 2) μ := by
      have : MeasureTheory.Integrable (fun s : ℝ => (2 : ℝ) ^ 2) μ :=
        MeasureTheory.integrable_const _
      exact this.mono
        ((((Complex.continuous_exp.comp
          ((continuous_const.mul Complex.continuous_ofReal))).sub continuous_const).norm.pow 2).measurable.aestronglyMeasurable)
        (Eventually.of_forall fun s => by
          simp only [Real.norm_eq_abs]
          rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
          calc ‖Complex.exp (Complex.I * ↑(h_seq n) * ↑s) - 1‖ ^ 2
              ≤ (‖Complex.exp (Complex.I * ↑(h_seq n) * ↑s)‖ + ‖(1 : ℂ)‖) ^ 2 := by
                gcongr; exact norm_sub_le _ _
            _ ≤ (1 + 1) ^ 2 := by
                gcongr
                · exact expI_norm_le (h_seq n) s
                · simp
            _ = 2 ^ 2 := by ring)
    exact h_norm_sq_int.div_const _
  -- Bound on ∫ G_n dμ: for large n, ∫ G_n ≤ C²
  have h_parseval : ∀ n, ∫ s, G n s ∂μ =
      ‖unitaryGroup T hT hsa (h_seq n) x - x‖ ^ 2 / (h_seq n) ^ 2 := by
    intro n
    simp only [G, h_seq]
    rw [MeasureTheory.integral_div]
    congr 1
    exact (unitaryGroup_diff_norm_sq T hT hsa x (h_seq n)).symm
  -- For large n, ‖U(h_n)x - x‖ ≤ C·|h_n|, so ‖U(h_n)x - x‖²/h_n² ≤ C²
  -- hC : ∀ᶠ h in nhds 0, ‖U(h)x - x‖ ≤ C * ‖h‖
  -- h_seq n → 0
  have h_seq_tend : Filter.Tendsto h_seq Filter.atTop (nhds 0) := by
    simp only [h_seq, one_div]
    exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have h_real_bound : ∀ᶠ n in Filter.atTop, ∫ s, G n s ∂μ ≤ C ^ 2 := by
    have h_ev := h_seq_tend.eventually hC
    filter_upwards [h_ev] with n hn
    rw [h_parseval]
    have h_pos := h_seq_pos n
    calc ‖unitaryGroup T hT hsa (h_seq n) x - x‖ ^ 2 / (h_seq n) ^ 2
        ≤ (C * ‖h_seq n‖) ^ 2 / (h_seq n) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (sq_nonneg _)
          exact sq_le_sq' (by linarith [norm_nonneg (unitaryGroup T hT hsa (h_seq n) x - x)]) hn
      _ = C ^ 2 := by
          rw [mul_pow, Real.norm_eq_abs, sq_abs, mul_div_cancel_right₀]
          exact pow_ne_zero 2 (ne_of_gt h_pos)
  -- liminf bound
  have h_lint_bound : ∀ᶠ n in Filter.atTop, ∫⁻ s, ‖G n s‖ₑ ∂μ ≤ ENNReal.ofReal (C ^ 2) := by
    filter_upwards [h_real_bound] with n hn
    have h_lintegral_eq : ∫⁻ s, ‖G n s‖ₑ ∂μ = ∫⁻ s, ENNReal.ofReal (G n s) ∂μ := by
      congr 1; ext s
      rw [show ‖G n s‖ₑ = ENNReal.ofReal ‖G n s‖ from (ofReal_norm_eq_enorm (G n s)).symm,
          Real.norm_eq_abs,
          abs_of_nonneg (show 0 ≤ G n s from by simp only [G]; positivity)]
    rw [h_lintegral_eq, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hG_int n) (hG_nonneg n)]
    exact ENNReal.ofReal_le_ofReal hn
  have h_liminf_ne_top : Filter.liminf (fun n => ∫⁻ s, ‖G n s‖ₑ ∂μ) Filter.atTop ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    calc Filter.liminf (fun n => ∫⁻ s, ‖G n s‖ₑ ∂μ) Filter.atTop
        ≤ Filter.limsup (fun n => ∫⁻ s, ‖G n s‖ₑ ∂μ) Filter.atTop :=
          Filter.liminf_le_limsup
      _ ≤ ENNReal.ofReal (C ^ 2) :=
          Filter.limsup_le_of_le (h := h_lint_bound)
  have h_sq_int_real : MeasureTheory.Integrable (fun s : ℝ => s ^ 2) μ :=
    MeasureTheory.integrable_of_tendsto hGf hG_meas h_liminf_ne_top
  have h_eq_fn : (fun s : ℝ => ((s : ℂ) ^ 2)) = (fun s : ℝ => ((s ^ 2 : ℝ) : ℂ)) := by
    ext s; push_cast; ring
  rw [h_eq_fn]
  exact h_sq_int_real.ofReal

end
