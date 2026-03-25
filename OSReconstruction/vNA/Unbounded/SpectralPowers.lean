/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.vNA.Unbounded.Spectral

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

/-- T^0 = 1 for strictly positive T.

    **Note:** This requires strict positivity (T injective), not just positivity.
    For a merely positive T, `power 0` gives `P((0,∞))` (the projection onto ker(T)⊥),
    which equals 1 only when T has trivial kernel. Counterexample: T = 0.
    See Issue #4.

    **Proof:** The function f(λ) = λ^0 = 1 for λ > 0 (and 0 elsewhere).
    For strictly positive T, P({0}) = 0 (since 0 is not an eigenvalue),
    so P((0,∞)) = P([0,∞)) = P(ℝ) = 1, giving ∫ f dP = 1.
    Depends on: spectral support argument (P((-∞, 0]) = 0 for positive T). -/
theorem UnboundedOperator.power_zero (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive)
    (hstrict : T.IsStrictlyPositive) :
    T.power hT hsa hpos 0 (by simp [Complex.zero_re]) = 1 := by
  /-
  PROOF STRUCTURE:

  1. The power function is: f(λ) = if λ > 0 then exp(0 * log λ) else 0
  2. For λ > 0: exp(0 * log λ) = exp(0) = 1
  3. So f(λ) = χ_{(0,∞)}(λ) (indicator of positive reals)

  For a strictly positive operator T:
  - The spectrum is contained in [0, ∞) (by positivity)
  - P({0}) = 0 (by strict positivity / injectivity)
  - Therefore P((0, ∞)) = P([0, ∞)) = P(ℝ) = 1
  - And ∫ χ_{(0,∞)} dP = P((0,∞)) = 1

  FOUNDATIONAL: Requires showing P((-∞, 0]) = 0 for strictly positive T
  and that the functional calculus of the constant 1 on support is the identity.
  -/
  sorry

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

/-- For real t, T^{it} is unitary (requires strict positivity).

    **Note:** Like `power_zero`, this requires strict positivity (T injective).
    For a merely positive T, T^0 = P((0,∞)) ≠ 1, so u* ∘ u = T^0 ≠ 1.
    Counterexample: T = 0 gives T^{it} = 0 for all t, which is not unitary.

    **Proof:** Uses `functionalCalculus_star`. For real t:
    - (T^{it})* = ∫ conj(λ^{it}) dP = ∫ λ^{-it} dP = T^{-it}
    - T^{it} ∘ T^{-it} = T^0 = 1 (by `power_add` and `power_zero`)
    Depends on: `functionalCalculus_star`, `power_add`, `power_zero`. -/
theorem UnboundedOperator.power_imaginary_unitary (T : UnboundedOperator H)
    (hT : T.IsDenselyDefined) (hsa : T.IsSelfAdjoint hT) (hpos : T.IsPositive)
    (hstrict : T.IsStrictlyPositive) (t : ℝ) :
    let hs : (Complex.I * ↑t).re = 0 := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    let u := T.power hT hsa hpos (Complex.I * t) hs
    ContinuousLinearMap.adjoint u ∘L u = 1 ∧ u ∘L ContinuousLinearMap.adjoint u = 1 := by
  /-
  PROOF STRUCTURE:

  Let u = T^{it} where the power function is:
    f_{it}(x) = if x > 0 then exp(it * log x) else 0

  **Step 1: Compute u* using functionalCalculus_star**
  u* = (∫ f_{it} dP)* = ∫ (star ∘ f_{it}) dP
  where (star ∘ f_{it})(x) = conj(f_{it}(x))

  For x > 0:
    conj(exp(it * log x)) = exp(conj(it * log x))
                          = exp(-it * log x)  [since log x ∈ ℝ for x > 0]
                          = exp((-it) * log x)

  So (star ∘ f_{it}) = f_{-it}, hence u* = T^{-it}

  **Step 2: Use power_add and power_zero**
  u* ∘ u = T^{-it} ∘ T^{it} = T^{-it + it} = T^0 = 1
  u ∘ u* = T^{it} ∘ T^{-it} = T^{it + (-it)} = T^0 = 1
  -/
  -- Depends on functionalCalculus_star (proven), power_add (proven), power_zero (sorry'd).
  -- Inherits the bug from power_zero: false for non-injective positive operators.
  -- For T = 0: u = T^{it} = functionalCalculus P (indicator_Ioi) = P(Ioi 0) = 0,
  -- so u* ∘ u = 0 ≠ 1. Fix power definition first (see power_zero comment).
  sorry

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

/-- The functional calculus is proof-irrelevant: it depends only on the function f. -/
private lemma functionalCalculus_congr (P : SpectralMeasure H) {f g : ℝ → ℂ}
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

/-! ### Spectral differentiation of the unitary group

The spectrally-defined unitary group U(t) = ∫ exp(itλ) dP(λ) satisfies the ODE
d/dt U(t)x = i U(t)(Tx) for x in dom(T).  This is proved by differentiating under
the spectral integral using dominated convergence.  The dominating function comes
from the mean-value-theorem bound |(exp(ihλ) - 1)/h| ≤ |λ|, and the integrability
of λ against the spectral measures of vectors in dom(T).

**Gap:** The codebase currently lacks:
1. The spectral representation Tx = ∫ λ dP(λ) x for x ∈ dom(T) (connecting
   the abstract operator defined via the Cayley transform to the spectral integral).
2. Differentiation under the polarized spectral integral.

Once those pieces are in place, the following lemma becomes a straightforward
application of dominated convergence. -/

/-- **Spectral differentiation axiom (Reed-Simon VIII.7(c), Rudin FA 13.33).**

    For a self-adjoint operator T with spectral measure P and x ∈ dom(T),
    the spectrally-defined unitary group U(t) = ∫ exp(itλ) dP(λ) satisfies:

      d/dt U(t)x = i · U(t)(Tx)

    **Proof (not formalized):**
    1. Group law reduces to derivative at 0: (U(h)x - x)/h → iTx.
    2. For each y, ⟨y, (U(h)x - x)/h⟩ = ∫ (exp(ihλ)-1)/h dμ_{y,x}(λ).
    3. Pointwise: (exp(ihλ)-1)/h → iλ.
    4. Domination: |(exp(ihλ)-1)/h| ≤ |λ| (mean value theorem).
    5. For x ∈ dom(T), λ ↦ |λ| is square-integrable against dP_x
       (spectral representation: ‖Tx‖² = ∫ λ² d⟨P(λ)x, x⟩).
    6. DCT: ∫ (exp(ihλ)-1)/h dμ → ∫ iλ dμ = ⟨y, iTx⟩.
    7. Weak convergence + U(h) isometric → strong convergence.

    **Required infrastructure (not yet in codebase):**
    - Spectral representation: Tx = ∫ λ dP(λ)x for x ∈ dom(T)
    - Differentiation under the polarized spectral integral (DCT) -/
axiom unitaryGroup_hasDerivAt_dom (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (x : T.domain) (t : ℝ) :
    HasDerivAt (fun s => unitaryGroup T hT hsa s (x : H))
      (Complex.I • unitaryGroup T hT hsa t (T x)) t

/-- The spectral unitary group preserves the domain of T.

    **Proof sketch (not formalized):**
    U(t) = ∫ exp(itλ) dP(λ) and dom(T) = {x : ∫ λ² d⟨P(λ)x, x⟩ < ∞}.
    Since |exp(itλ)| = 1, U(t) commutes with P(E) for every Borel E,
    so ∫ λ² d⟨P(λ)U(t)x, U(t)x⟩ = ∫ λ² d⟨P(λ)x, x⟩ < ∞.
    Hence U(t)x ∈ dom(T). -/
axiom unitaryGroup_preserves_domain (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (x : T.domain) (t : ℝ) :
    unitaryGroup T hT hsa t (x : H) ∈ T.domain

/-- The spectral unitary group commutes with T on dom(T):
    T(U(t)x) = U(t)(Tx) for x ∈ dom(T).

    **Proof sketch (not formalized):**
    Both T and U(t) are functions of the spectral measure P:
    T = ∫ λ dP(λ), U(t) = ∫ exp(itλ) dP(λ).
    Functional calculus gives f(T)g(T) = (fg)(T),
    so U(t)T = T U(t) on dom(T). -/
axiom unitaryGroup_commutes_with_generator (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (x : T.domain) (t : ℝ) :
    T ⟨unitaryGroup T hT hsa t (x : H), unitaryGroup_preserves_domain T hT hsa x t⟩ =
    unitaryGroup T hT hsa t (T x)

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
axiom unitaryGroup_generator_domain_eq (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (x : H)
    (hx : ∃ y : H, HasDerivAt (fun t => unitaryGroup T hT hsa t x) y 0) :
    x ∈ T.domain

end
