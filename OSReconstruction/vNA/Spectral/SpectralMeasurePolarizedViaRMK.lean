/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.vNA.Spectral.SpectralFunctionalViaRMK
import OSReconstruction.vNA.MeasureTheory.SpectralIntegral
import OSReconstruction.vNA.Spectral.JensenLinearity

/-!
# Polarized Spectral Measure via Riesz-Markov-Kakutani

This file constructs the polarized spectral measure for unitary operators by
applying the complex polarization identity to the diagonal spectral measure
from `SpectralFunctionalViaRMK.lean`.

## Main Definitions

* `spectralMeasurePolarized` : the complex polarized spectral measure μ_{x,y}(E)

## Main Results

* `spectralMeasurePolarized_linear_right` : linearity in second argument
* `spectralMeasurePolarized_conj_linear_left` : conjugate-linearity in first argument
* `spectralMeasurePolarized_bounded` : boundedness of the sesquilinear form
* `spectralMeasurePolarized_conj_symm` : Hermitian symmetry B(x,y) = conj(B(y,x))

## References

* Reed-Simon, "Methods of Modern Mathematical Physics I", Chapter VII-VIII
* Mathlib's `MeasureTheory.Integral.RieszMarkovKakutani.Real`
-/

noncomputable section

open scoped InnerProduct ComplexConjugate Classical CompactlySupported
open Filter Topology Complex MeasureTheory CompactlySupportedContinuousMap

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Polarization to Complex Measure -/

/-- The spectral functional parallelogram identity.
    Λ_{x+y}(f) + Λ_{x-y}(f) = 2Λ_x(f) + 2Λ_y(f)
    This is fundamental for the quadratic form structure. -/
theorem spectralFunctionalAux_parallelogram (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (f : C(Circle, ℝ)) (x y : H) :
    spectralFunctionalAux U hU (x + y) f + spectralFunctionalAux U hU (x - y) f =
    2 * spectralFunctionalAux U hU x f + 2 * spectralFunctionalAux U hU y f := by
  simp only [spectralFunctionalAux, cfcOfCircleReal]
  haveI : IsStarNormal U := unitary_isStarNormal U hU
  set A := cfc (circleRealToComplex f) U with hA_def
  -- Expand inner products using linearity
  have h1 : @inner ℂ H _ (x + y) (A (x + y)) =
      @inner ℂ H _ x (A x) + @inner ℂ H _ x (A y) +
      @inner ℂ H _ y (A x) + @inner ℂ H _ y (A y) := by
    simp only [map_add, inner_add_left, inner_add_right]
    ring
  have h2 : @inner ℂ H _ (x - y) (A (x - y)) =
      @inner ℂ H _ x (A x) - @inner ℂ H _ x (A y) -
      @inner ℂ H _ y (A x) + @inner ℂ H _ y (A y) := by
    simp only [map_sub, inner_sub_left, inner_sub_right]
    ring
  -- Adding: the cross terms cancel to give 2*Q(x) + 2*Q(y)
  have hsum : @inner ℂ H _ (x + y) (A (x + y)) + @inner ℂ H _ (x - y) (A (x - y)) =
      2 * @inner ℂ H _ x (A x) + 2 * @inner ℂ H _ y (A y) := by
    rw [h1, h2]; ring
  -- Take real parts
  have hre := congrArg Complex.re hsum
  simp only [Complex.add_re, Complex.mul_re] at hre
  -- (2 : ℂ) = ofReal 2, so (2 : ℂ).re = 2, (2 : ℂ).im = 0
  have h2re : (2 : ℂ).re = 2 := rfl
  have h2im : (2 : ℂ).im = 0 := rfl
  simp only [h2re, h2im] at hre
  (convert hre using 1; ring)

/-- The spectral functional polarization identity.
    (1/4)[Λ_{x+y}(f) - Λ_{x-y}(f) - i·Λ_{x+iy}(f) + i·Λ_{x-iy}(f)] = ⟨x, cfc(f, U) y⟩

    This uses the polarization identity for symmetric operators from Mathlib. -/
theorem spectralFunctionalAux_polarization (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (f : C(Circle, ℝ)) (x y : H) :
    (1/4 : ℂ) * (spectralFunctionalAux U hU (x + y) f - spectralFunctionalAux U hU (x - y) f -
      Complex.I * spectralFunctionalAux U hU (x + Complex.I • y) f +
      Complex.I * spectralFunctionalAux U hU (x - Complex.I • y) f) =
    @inner ℂ H _ x (cfcOfCircleReal U hU f y) := by
  haveI : IsStarNormal U := unitary_isStarNormal U hU
  set A := cfc (circleRealToComplex f) U with hA_def
  have hA_sa : IsSelfAdjoint A := cfcOfCircleReal_isSelfAdjoint U hU f
  -- For self-adjoint A (continuous), A.toLinearMap is symmetric
  have hA_sym : A.toLinearMap.IsSymmetric := fun u v => by
    rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint] at hA_sa
    calc @inner ℂ H _ (A u) v
        = @inner ℂ H _ u (A.adjoint v) := (ContinuousLinearMap.adjoint_inner_right A u v).symm
      _ = @inner ℂ H _ u (A v) := by rw [hA_sa]
  -- Apply the polarization identity: for symmetric T,
  -- ⟨T x, y⟩ = (⟨T(x+y), x+y⟩ - ⟨T(x-y), x-y⟩ - I*⟨T(x+I•y), x+I•y⟩ + I*⟨T(x-I•y), x-I•y⟩)/4
  have hpol := hA_sym.inner_map_polarization x y
  -- For self-adjoint A: ⟨x, Ay⟩ = ⟨Ax, y⟩
  have hAdj : @inner ℂ H _ x (A y) = @inner ℂ H _ (A x) y := by
    rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint] at hA_sa
    calc @inner ℂ H _ x (A y)
        = @inner ℂ H _ x (A.adjoint y) := by rw [hA_sa]
      _ = @inner ℂ H _ (A x) y := ContinuousLinearMap.adjoint_inner_right A x y
  -- The key is that ⟨z, Az⟩ is real for self-adjoint A, so ⟨z, Az⟩ = Re⟨z, Az⟩
  have hreal_sum : (@inner ℂ H _ (x + y) (A (x + y))).im = 0 :=
    cfcOfCircleReal_inner_real U hU f (x + y)
  have hreal_diff : (@inner ℂ H _ (x - y) (A (x - y))).im = 0 :=
    cfcOfCircleReal_inner_real U hU f (x - y)
  have hreal_isum : (@inner ℂ H _ (x + Complex.I • y) (A (x + Complex.I • y))).im = 0 :=
    cfcOfCircleReal_inner_real U hU f (x + Complex.I • y)
  have hreal_idiff : (@inner ℂ H _ (x - Complex.I • y) (A (x - Complex.I • y))).im = 0 :=
    cfcOfCircleReal_inner_real U hU f (x - Complex.I • y)
  -- For real z (im z = 0): z = ofReal (re z)
  have eq_sum : @inner ℂ H _ (x + y) (A (x + y)) =
      Complex.ofReal (@inner ℂ H _ (x + y) (A (x + y))).re := by
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · simp only [Complex.ofReal_im, hreal_sum]
  have eq_diff : @inner ℂ H _ (x - y) (A (x - y)) =
      Complex.ofReal (@inner ℂ H _ (x - y) (A (x - y))).re := by
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · simp only [Complex.ofReal_im, hreal_diff]
  have eq_isum : @inner ℂ H _ (x + Complex.I • y) (A (x + Complex.I • y)) =
      Complex.ofReal (@inner ℂ H _ (x + Complex.I • y) (A (x + Complex.I • y))).re := by
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · simp only [Complex.ofReal_im, hreal_isum]
  have eq_idiff : @inner ℂ H _ (x - Complex.I • y) (A (x - Complex.I • y)) =
      Complex.ofReal (@inner ℂ H _ (x - Complex.I • y) (A (x - Complex.I • y))).re := by
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · simp only [Complex.ofReal_im, hreal_idiff]
  -- Use symmetry: ⟨Az, z⟩ = ⟨z, Az⟩ for symmetric A
  have sym_sum : @inner ℂ H _ (A (x + y)) (x + y) = @inner ℂ H _ (x + y) (A (x + y)) :=
    hA_sym (x + y) (x + y)
  have sym_diff : @inner ℂ H _ (A (x - y)) (x - y) = @inner ℂ H _ (x - y) (A (x - y)) :=
    hA_sym (x - y) (x - y)
  have sym_isum : @inner ℂ H _ (A (x + Complex.I • y)) (x + Complex.I • y) =
      @inner ℂ H _ (x + Complex.I • y) (A (x + Complex.I • y)) :=
    hA_sym (x + Complex.I • y) (x + Complex.I • y)
  have sym_idiff : @inner ℂ H _ (A (x - Complex.I • y)) (x - Complex.I • y) =
      @inner ℂ H _ (x - Complex.I • y) (A (x - Complex.I • y)) :=
    hA_sym (x - Complex.I • y) (x - Complex.I • y)
  -- Unfold spectralFunctionalAux and cfcOfCircleReal, then use the equalities
  unfold spectralFunctionalAux cfcOfCircleReal
  simp only [← hA_def]
  -- Now RHS is ⟨x, A y⟩ = ⟨A x, y⟩ (by hAdj)
  rw [hAdj]
  -- Convert ↑(...).re back to full inner products using eq_* lemmas (backwards)
  rw [← eq_sum, ← eq_diff, ← eq_isum, ← eq_idiff]
  -- Convert inner (x+y) (A(x+y)) to inner (A(x+y)) (x+y) using sym_*
  rw [← sym_sum, ← sym_diff, ← sym_isum, ← sym_idiff]
  -- The goal is now: 1/4 * (...) = inner (A x) y
  -- hpol says: inner (A x) y = (...) / 4
  -- Note: 1/4 * z = z / 4, so we just need hpol.symm after adjusting
  have hmul_div : ∀ z : ℂ, (1 / 4 : ℂ) * z = z / 4 := fun z => by ring
  rw [hmul_div]
  exact hpol.symm

/-- The spectral functional scales quadratically: Λ_{cz}(f) = |c|² Λ_z(f).
    This is the key property making μ_z(E) a quadratic form in z. -/
theorem spectralFunctionalAux_smul_sq (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (c : ℂ) (z : H) (f : C(Circle, ℝ)) :
    spectralFunctionalAux U hU (c • z) f = ‖c‖^2 * spectralFunctionalAux U hU z f := by
  haveI : IsStarNormal U := unitary_isStarNormal U hU
  unfold spectralFunctionalAux cfcOfCircleReal
  set A := cfc (circleRealToComplex f) U with hA_def
  -- ⟨cz, A(cz)⟩ = ⟨cz, c·Az⟩ = c̄·c·⟨z, Az⟩ = |c|²·⟨z, Az⟩
  calc (@inner ℂ H _ (c • z) (A (c • z))).re
      = (@inner ℂ H _ (c • z) (c • A z)).re := by rw [map_smul]
    _ = (starRingEnd ℂ c * c * @inner ℂ H _ z (A z)).re := by
        rw [inner_smul_left, inner_smul_right]; ring_nf
    _ = (Complex.normSq c * @inner ℂ H _ z (A z)).re := by
        rw [← Complex.normSq_eq_conj_mul_self]
    _ = ‖c‖^2 * (@inner ℂ H _ z (A z)).re := by
        rw [Complex.normSq_eq_norm_sq]
        have h : ((‖c‖^2 : ℝ) : ℂ) * @inner ℂ H _ z (A z) =
                 (‖c‖^2 : ℝ) * @inner ℂ H _ z (A z) := rfl
        rw [Complex.mul_re]
        simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- The diagonal spectral measure satisfies μ_{cz}(E) = |c|² μ_z(E).
    This follows from the quadratic scaling of the spectral functional. -/
theorem spectralMeasureDiagonal_smul_sq (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (c : ℂ) (z : H) (E : Set Circle) (_hE : MeasurableSet E) :
    (spectralMeasureDiagonal U hU (c • z) E).toReal =
    ‖c‖^2 * (spectralMeasureDiagonal U hU z E).toReal := by
  -- The key: both measures integrate functions the same way
  -- For continuous functions f: ∫ f dμ_{cz} = Λ_{cz}(f) = |c|² Λ_z(f) = |c|² ∫ f dμ_z
  have hint_eq : ∀ f : C_c(Circle, ℝ),
      ∫ x, f x ∂(spectralMeasureDiagonal U hU (c • z)) =
      ‖c‖^2 * ∫ x, f x ∂(spectralMeasureDiagonal U hU z) := by
    intro f
    rw [spectralMeasureDiagonal_integral U hU (c • z) f]
    rw [spectralMeasureDiagonal_integral U hU z f]
    show spectralFunctionalAux U hU (c • z) f.toContinuousMap =
         ‖c‖^2 * spectralFunctionalAux U hU z f.toContinuousMap
    exact spectralFunctionalAux_smul_sq U hU c z f.toContinuousMap
  -- Use the scaling coefficient as NNReal
  have hr_nonneg : 0 ≤ ‖c‖^2 := sq_nonneg _
  let r : NNReal := Real.toNNReal (‖c‖^2)
  have hr_val : (r : ℝ) = ‖c‖^2 := Real.coe_toNNReal _ hr_nonneg
  -- Apply uniqueness: both measures integrate same → measures related by scaling
  -- The RMK measure is regular
  haveI hreg1 : (spectralMeasureDiagonal U hU (c • z)).Regular := RealRMK.regular_rieszMeasure _
  haveI hreg2 : (spectralMeasureDiagonal U hU z).Regular := RealRMK.regular_rieszMeasure _
  haveI hreg_scaled : (r • spectralMeasureDiagonal U hU z).Regular := by
    infer_instance
  have hμ_eq : spectralMeasureDiagonal U hU (c • z) = r • spectralMeasureDiagonal U hU z := by
    apply MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [hint_eq f]
    -- ∫ f d(r • μ) = r • ∫ f dμ = ‖c‖² * ∫ f dμ
    rw [MeasureTheory.integral_smul_nnreal_measure (fun x => f x) r]
    -- r • ∫ f dμ = (r : ℝ) * ∫ f dμ = ‖c‖² * ∫ f dμ
    rw [NNReal.smul_def, hr_val, smul_eq_mul]
  -- Now the result follows for the specific set E
  rw [hμ_eq, MeasureTheory.Measure.coe_nnreal_smul_apply]
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, hr_val]

/-- The diagonal spectral measure satisfies the parallelogram identity:
    μ_{x+y}(E) + μ_{x-y}(E) = 2μ_x(E) + 2μ_y(E).
    This follows from the parallelogram identity for the spectral functional. -/
theorem spectralMeasureDiagonal_parallelogram (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (x y : H) (E : Set Circle) (_hE : MeasurableSet E) :
    (spectralMeasureDiagonal U hU (x + y) E).toReal +
    (spectralMeasureDiagonal U hU (x - y) E).toReal =
    2 * (spectralMeasureDiagonal U hU x E).toReal +
    2 * (spectralMeasureDiagonal U hU y E).toReal := by
  -- For all continuous f, the integrals satisfy the parallelogram identity
  have hint_eq : ∀ f : C_c(Circle, ℝ),
      ∫ z, f z ∂(spectralMeasureDiagonal U hU (x + y)) +
      ∫ z, f z ∂(spectralMeasureDiagonal U hU (x - y)) =
      2 * ∫ z, f z ∂(spectralMeasureDiagonal U hU x) +
      2 * ∫ z, f z ∂(spectralMeasureDiagonal U hU y) := by
    intro f
    rw [spectralMeasureDiagonal_integral U hU (x + y) f]
    rw [spectralMeasureDiagonal_integral U hU (x - y) f]
    rw [spectralMeasureDiagonal_integral U hU x f]
    rw [spectralMeasureDiagonal_integral U hU y f]
    exact spectralFunctionalAux_parallelogram U hU f.toContinuousMap x y
  -- The measures are regular
  haveI hreg1 : (spectralMeasureDiagonal U hU (x + y)).Regular := RealRMK.regular_rieszMeasure _
  haveI hreg2 : (spectralMeasureDiagonal U hU (x - y)).Regular := RealRMK.regular_rieszMeasure _
  haveI hreg3 : (spectralMeasureDiagonal U hU x).Regular := RealRMK.regular_rieszMeasure _
  haveI hreg4 : (spectralMeasureDiagonal U hU y).Regular := RealRMK.regular_rieszMeasure _
  -- Show measure equality: μ_{x+y} + μ_{x-y} = 2•μ_x + 2•μ_y
  have hμ_eq : spectralMeasureDiagonal U hU (x + y) + spectralMeasureDiagonal U hU (x - y) =
      (2 : NNReal) • spectralMeasureDiagonal U hU x + (2 : NNReal) • spectralMeasureDiagonal U hU y := by
    apply MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    -- Compactly supported continuous functions are integrable on finite measures
    -- The RMK measure on compact Circle is finite
    haveI : MeasureTheory.IsFiniteMeasureOnCompacts (spectralMeasureDiagonal U hU (x + y)) := inferInstance
    haveI : MeasureTheory.IsFiniteMeasureOnCompacts (spectralMeasureDiagonal U hU (x - y)) := inferInstance
    haveI : MeasureTheory.IsFiniteMeasureOnCompacts ((2 : NNReal) • spectralMeasureDiagonal U hU x) := inferInstance
    haveI : MeasureTheory.IsFiniteMeasureOnCompacts ((2 : NNReal) • spectralMeasureDiagonal U hU y) := inferInstance
    have hint : ∀ μ [MeasureTheory.IsFiniteMeasureOnCompacts μ], MeasureTheory.Integrable (fun z => f z) μ :=
      fun μ _ => f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
    rw [MeasureTheory.integral_add_measure (hint _) (hint _)]
    rw [MeasureTheory.integral_add_measure (hint _) (hint _)]
    rw [MeasureTheory.integral_smul_nnreal_measure, MeasureTheory.integral_smul_nnreal_measure]
    simp only [NNReal.smul_def, NNReal.coe_ofNat]
    exact hint_eq f
  -- Evaluate at E
  have heq : (spectralMeasureDiagonal U hU (x + y) + spectralMeasureDiagonal U hU (x - y)) E =
      ((2 : NNReal) • spectralMeasureDiagonal U hU x + (2 : NNReal) • spectralMeasureDiagonal U hU y) E := by
    rw [hμ_eq]
  simp only [MeasureTheory.Measure.add_apply, MeasureTheory.Measure.coe_nnreal_smul_apply] at heq
  -- Convert from ENNReal to Real
  have hne1 : (spectralMeasureDiagonal U hU (x + y) E) ≠ ⊤ := MeasureTheory.measure_ne_top _ _
  have hne2 : (spectralMeasureDiagonal U hU (x - y) E) ≠ ⊤ := MeasureTheory.measure_ne_top _ _
  have hne3 : (2 : ENNReal) * (spectralMeasureDiagonal U hU x E) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (MeasureTheory.measure_ne_top _ _)
  have hne4 : (2 : ENNReal) * (spectralMeasureDiagonal U hU y E) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (MeasureTheory.measure_ne_top _ _)
  calc (spectralMeasureDiagonal U hU (x + y) E).toReal +
       (spectralMeasureDiagonal U hU (x - y) E).toReal
      = ((spectralMeasureDiagonal U hU (x + y) E) +
         (spectralMeasureDiagonal U hU (x - y) E)).toReal := (ENNReal.toReal_add hne1 hne2).symm
    _ = ((2 : ENNReal) * (spectralMeasureDiagonal U hU x E) +
         (2 : ENNReal) * (spectralMeasureDiagonal U hU y E)).toReal := by
           -- heq has ↑2 (coercion from NNReal) but goal has (2 : ENNReal); they're equal
           convert congrArg ENNReal.toReal heq using 2
    _ = ((2 : ENNReal) * (spectralMeasureDiagonal U hU x E)).toReal +
        ((2 : ENNReal) * (spectralMeasureDiagonal U hU y E)).toReal := ENNReal.toReal_add hne3 hne4
    _ = 2 * (spectralMeasureDiagonal U hU x E).toReal +
        2 * (spectralMeasureDiagonal U hU y E).toReal := by
          simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat]

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- Quadratic expansion: μ_{w+tv}(E) = μ_w(E) + 2t·B(w,v) + t²·μ_v(E)
    where B(w,v) = (μ_{w+v}(E) - μ_{w-v}(E))/4 is the polarized form.
    Key: When μ_v = 0, μ_{w+tv} is linear in t, forcing B(w,v) = 0. -/
theorem spectralMeasureDiagonal_quadratic_expansion (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (w v : H) (E : Set Circle) (hE : MeasurableSet E) (t : ℝ) :
    (spectralMeasureDiagonal U hU (w + t • v) E).toReal =
    (spectralMeasureDiagonal U hU w E).toReal +
    2 * t * ((spectralMeasureDiagonal U hU (w + v) E).toReal -
             (spectralMeasureDiagonal U hU (w - v) E).toReal) / 4 +
    t^2 * (spectralMeasureDiagonal U hU v E).toReal := by
  set Q := fun z => (spectralMeasureDiagonal U hU z E).toReal with hQ_def
  set μw := Q w with hμw_def
  set μv := Q v with hμv_def
  set μwpv := Q (w + v) with hμwpv_def
  set μwmv := Q (w - v) with hμwmv_def
  set B := (μwpv - μwmv) / 4 with hB_def
  have hpara := spectralMeasureDiagonal_parallelogram U hU w v E hE
  have hexp_t1 : μwpv = μw + 2 * B + μv := by simp only [hB_def]; linarith
  have hscaling : Q (t • v) = t^2 * μv := by
    have h := spectralMeasureDiagonal_smul_sq U hU (↑t : ℂ) v E hE
    simp only [Complex.norm_real] at h
    rw [Real.norm_eq_abs, sq_abs] at h
    have hsmul_eq : t • v = (↑t : ℂ) • v := RCLike.real_smul_eq_coe_smul (K := ℂ) t v
    rw [hsmul_eq]; exact h
  have hpara_t : Q (w + t • v) + Q (w - t • v) = 2 * μw + 2 * Q (t • v) :=
    spectralMeasureDiagonal_parallelogram U hU w (t • v) E hE
  rw [hscaling] at hpara_t
  have hexp_tm1 : μwmv = μw - 2 * B + μv := by linarith [hexp_t1, hpara]
  show Q (w + t • v) = Q w + 2 * t * (Q (w + v) - Q (w - v)) / 4 + t^2 * Q v
  have hsimpl : 2 * t * (Q (w + v) - Q (w - v)) / 4 = t * (Q (w + v) - Q (w - v)) / 2 := by ring
  rw [hsimpl]
  have hpara' : Q (w + t • v) + Q (w - t • v) = 2 * Q w + 2 * t^2 * Q v := by
    simp only [hμw_def, hμv_def] at hpara_t ⊢
    linarith [hpara_t]
  -- The proof uses the even-odd decomposition of Q(w + tv) as a function of t
  -- Even part: (Q(w+tv) + Q(w-tv))/2 = Q(w) + t²Q(v) (from hpara')
  -- Odd part: (Q(w+tv) - Q(w-tv))/2 equals t*(Q(w+v) - Q(w-v))/2
  -- The odd part is linear because the spectral measure comes from a sesquilinear form
  -- For a Hermitian sesquilinear form B with Q(x) = B(x,x):
  -- Q(w + tv) - Q(w - tv) = 4t*Re(B(w,v)) and Q(w+v) - Q(w-v) = 4*Re(B(w,v))
  -- Therefore D(t) = t*D(1)
  have heven : (Q (w + t • v) + Q (w - t • v)) / 2 = Q w + t^2 * Q v := by linarith [hpara']
  have hodd_lin : (Q (w + t • v) - Q (w - t • v)) / 2 = t * (Q (w + v) - Q (w - v)) / 2 := by
    -- Define the odd part D(t) = Q(w + tv) - Q(w - tv)
    -- From parallelogram: D(s+t) + D(s-t) = 2*D(s) (Jensen's equation)
    -- With D(0) = 0, D(1) = Q(w+v) - Q(w-v), this forces D(t) = t*D(1) for continuous D
    -- The spectral measure is continuous in x, so D is continuous in t
    -- Proof: Show D satisfies Jensen, then conclude D is linear
    -- Jensen for D: use parallelogram with (w+sv, tv) and (w-sv, tv)
    have hQ_neg : ∀ x : H, Q (-x) = Q x := by
      intro x
      have h := spectralMeasureDiagonal_smul_sq U hU (-1 : ℂ) x E hE
      -- h : μ_{-1 • x}(E) = ‖-1‖² * μ_x(E)
      have hnorm : ‖(-1 : ℂ)‖ = 1 := by rw [norm_neg, norm_one]
      have hsmul : (-1 : ℂ) • x = -x := neg_one_smul ℂ x
      -- Rewrite h to get μ_{-x}(E) = 1 * μ_x(E) = μ_x(E)
      calc Q (-x) = Q ((-1 : ℂ) • x) := by rw [hsmul]
        _ = ‖(-1 : ℂ)‖^2 * Q x := h
        _ = 1^2 * Q x := by rw [hnorm]
        _ = Q x := by ring
    -- D(s+t) + D(s-t) = 2*D(s) follows from two applications of parallelogram
    have hJensen : ∀ s : ℝ, (Q (w + (s + t) • v) - Q (w - (s + t) • v)) +
        (Q (w + (s - t) • v) - Q (w - (s - t) • v)) =
        2 * (Q (w + s • v) - Q (w - s • v)) := by
      intro s
      -- Parallelogram: Q(a + b) + Q(a - b) = 2*Q(a) + 2*Q(b)
      -- Use a = w + sv, b = tv:
      have h1 : Q (w + s • v + t • v) + Q (w + s • v - t • v) = 2 * Q (w + s • v) + 2 * Q (t • v) :=
        spectralMeasureDiagonal_parallelogram U hU (w + s • v) (t • v) E hE
      -- Use a = w - sv, b = tv:
      have h2 : Q (w - s • v + t • v) + Q (w - s • v - t • v) = 2 * Q (w - s • v) + 2 * Q (t • v) :=
        spectralMeasureDiagonal_parallelogram U hU (w - s • v) (t • v) E hE
      -- Simplify: w + sv ± tv = w + (s±t)v
      have heq1 : w + s • v + t • v = w + (s + t) • v := by
        rw [add_assoc, ← add_smul]
      have heq2 : w + s • v - t • v = w + (s - t) • v := by
        rw [add_sub_assoc, ← sub_smul]
      have heq3 : w - s • v + t • v = w + (-s + t) • v := by
        have h : -(s • v) = (-s) • v := (neg_smul s v).symm
        rw [sub_eq_add_neg, h, add_assoc, ← add_smul]
      have heq4 : w - s • v - t • v = w + (-s - t) • v := by
        have hs : -(s • v) = (-s) • v := (neg_smul s v).symm
        have ht : -(t • v) = (-t) • v := (neg_smul t v).symm
        calc w - s • v - t • v = w + -(s • v) + -(t • v) := by rw [sub_eq_add_neg, sub_eq_add_neg]
          _ = w + (-s) • v + (-t) • v := by rw [hs, ht]
          _ = w + ((-s) + (-t)) • v := by rw [add_assoc, ← add_smul]
          _ = w + (-s - t) • v := by ring_nf
      -- Note: w - (s+t)v = w + (-(s+t))v
      have hneg1 : w - (s + t) • v = w + (-(s + t)) • v := by rw [neg_smul, sub_eq_add_neg]
      have hneg2 : w - (s - t) • v = w + (-(s - t)) • v := by rw [neg_smul, sub_eq_add_neg]
      -- Also: (-s+t) = -(s-t) and (-s-t) = -(s+t)
      have hrel1 : (-s + t) = -(s - t) := by ring
      have hrel2 : (-s - t) = -(s + t) := by ring
      -- And Q(w + av) = Q(w - (-a)v) using Q(-x) = Q(x)
      -- Actually: w + av and w - (-a)v have the same Q value
      -- w + (-a)v = w - av, so Q(w + (-a)v) = Q(w - av)
      -- Rewrite h2 using the simplifications
      rw [heq3, heq4, hrel1, hrel2] at h2
      rw [heq1, heq2] at h1
      -- h1: Q(w + (s+t)v) + Q(w + (s-t)v) = 2*Q(w + sv) + 2*Q(tv)
      -- h2: Q(w + (-(s-t))v) + Q(w + (-(s+t))v) = 2*Q(w - sv) + 2*Q(tv)
      -- We need: Q(w + (s+t)v) - Q(w - (s+t)v) + Q(w + (s-t)v) - Q(w - (s-t)v)
      --        = 2*(Q(w + sv) - Q(w - sv))
      -- Note: Q(w + (-a)v) = Q(w - av) by substitution
      have hsubst1 : Q (w + (-(s + t)) • v) = Q (w - (s + t) • v) := by
        congr 1
        rw [neg_smul, ← sub_eq_add_neg]
      have hsubst2 : Q (w + (-(s - t)) • v) = Q (w - (s - t) • v) := by
        congr 1
        rw [neg_smul, ← sub_eq_add_neg]
      rw [hsubst1, hsubst2] at h2
      -- Now h2: Q(w - (s-t)v) + Q(w - (s+t)v) = 2*Q(w - sv) + 2*Q(tv)
      -- Subtract h2 from h1:
      -- Q(w + (s+t)v) + Q(w + (s-t)v) - Q(w - (s-t)v) - Q(w - (s+t)v) = 2*Q(w + sv) - 2*Q(w - sv)
      linarith [h1, h2]
    -- D(0) = 0
    have hD_zero : Q (w + 0 • v) - Q (w - 0 • v) = 0 := by
      simp only [zero_smul, add_zero, sub_zero, sub_self]
    -- D(1) = Q(w+v) - Q(w-v)
    have hD_one : Q (w + 1 • v) - Q (w - 1 • v) = Q (w + v) - Q (w - v) := by
      simp only [one_smul]
    -- Define D as a function ℝ → ℝ
    set D := fun r : ℝ => Q (w + r • v) - Q (w - r • v) with hD_def
    -- Generalized Jensen: D(s + δ) + D(s - δ) = 2*D(s) for ALL s and δ
    -- This follows from the same parallelogram argument with any step size
    have hJensenGen : ∀ s δ : ℝ, D (s + δ) + D (s - δ) = 2 * D s := by
      intro s δ
      -- Same proof as hJensen but with δ instead of t
      have h1 : Q (w + s • v + δ • v) + Q (w + s • v - δ • v) = 2 * Q (w + s • v) + 2 * Q (δ • v) :=
        spectralMeasureDiagonal_parallelogram U hU (w + s • v) (δ • v) E hE
      have h2 : Q (w - s • v + δ • v) + Q (w - s • v - δ • v) = 2 * Q (w - s • v) + 2 * Q (δ • v) :=
        spectralMeasureDiagonal_parallelogram U hU (w - s • v) (δ • v) E hE
      have heq1 : w + s • v + δ • v = w + (s + δ) • v := by rw [add_assoc, ← add_smul]
      have heq2 : w + s • v - δ • v = w + (s - δ) • v := by rw [add_sub_assoc, ← sub_smul]
      have heq3 : w - s • v + δ • v = w + (-s + δ) • v := by
        have h : -(s • v) = (-s) • v := (neg_smul s v).symm
        rw [sub_eq_add_neg, h, add_assoc, ← add_smul]
      have heq4 : w - s • v - δ • v = w + (-s - δ) • v := by
        have hs : -(s • v) = (-s) • v := (neg_smul s v).symm
        have hd : -(δ • v) = (-δ) • v := (neg_smul δ v).symm
        calc w - s • v - δ • v = w + -(s • v) + -(δ • v) := by rw [sub_eq_add_neg, sub_eq_add_neg]
          _ = w + (-s) • v + (-δ) • v := by rw [hs, hd]
          _ = w + ((-s) + (-δ)) • v := by rw [add_assoc, ← add_smul]
          _ = w + (-s - δ) • v := by ring_nf
      have hrel1 : (-s + δ) = -(s - δ) := by ring
      have hrel2 : (-s - δ) = -(s + δ) := by ring
      rw [heq3, heq4, hrel1, hrel2] at h2
      rw [heq1, heq2] at h1
      have hsubst1 : Q (w + (-(s + δ)) • v) = Q (w - (s + δ) • v) := by
        congr 1; rw [neg_smul, ← sub_eq_add_neg]
      have hsubst2 : Q (w + (-(s - δ)) • v) = Q (w - (s - δ) • v) := by
        congr 1; rw [neg_smul, ← sub_eq_add_neg]
      rw [hsubst1, hsubst2] at h2
      linarith [h1, h2]
    -- D(0) = 0 in terms of D
    have hD_zero' : D 0 = 0 := by simp only [hD_def, zero_smul, add_zero, sub_zero, sub_self]
    -- Use bounded_jensen_is_linear: Jensen + bounded on [0,1] + D(0)=0 implies D(t) = t*D(1)
    have hD_linear : D t = t * D 1 := by
      -- Use bounded_jensen_is_linear from JensenLinearity
      -- D satisfies Jensen, D(0) = 0, need to show D is bounded on [0,1]
      have hJ : SatisfiesJensen D := hJensenGen
      -- Bound: |D(r)| ≤ 2(‖w‖ + ‖v‖)² for r ∈ [0,1]
      have hBound : ∃ M : ℝ, ∀ r ∈ Set.Icc (0 : ℝ) 1, |D r| ≤ M := by
        use 2 * (‖w‖ + ‖v‖)^2
        intro r hr
        simp only [hD_def]
        -- |Q(w + rv) - Q(w - rv)| ≤ |Q(w + rv)| + |Q(w - rv)|
        have h1 : |Q (w + r • v) - Q (w - r • v)| ≤ |Q (w + r • v)| + |Q (w - r • v)| := abs_sub _ _
        -- Q(x) ≥ 0, so |Q(x)| = Q(x)
        have hQ_nn1 : 0 ≤ Q (w + r • v) := ENNReal.toReal_nonneg
        have hQ_nn2 : 0 ≤ Q (w - r • v) := ENNReal.toReal_nonneg
        rw [abs_of_nonneg hQ_nn1, abs_of_nonneg hQ_nn2] at h1
        -- Q(x) ≤ ‖x‖² from spectral measure bound
        have hQ_bound1 : Q (w + r • v) ≤ ‖w + r • v‖^2 := by
          haveI : IsFiniteMeasure (spectralMeasureDiagonal U hU (w + r • v)) :=
            spectralMeasureDiagonal_isFiniteMeasure U hU (w + r • v)
          have hmono := MeasureTheory.measure_mono (μ := spectralMeasureDiagonal U hU (w + r • v))
            (Set.subset_univ E)
          have huniv := spectralMeasureDiagonal_univ U hU (w + r • v)
          exact le_trans (ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) hmono)
                         (le_of_eq huniv)
        have hQ_bound2 : Q (w - r • v) ≤ ‖w - r • v‖^2 := by
          haveI : IsFiniteMeasure (spectralMeasureDiagonal U hU (w - r • v)) :=
            spectralMeasureDiagonal_isFiniteMeasure U hU (w - r • v)
          have hmono := MeasureTheory.measure_mono (μ := spectralMeasureDiagonal U hU (w - r • v))
            (Set.subset_univ E)
          have huniv := spectralMeasureDiagonal_univ U hU (w - r • v)
          exact le_trans (ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) hmono)
                         (le_of_eq huniv)
        -- ‖w + rv‖ ≤ ‖w‖ + |r|‖v‖ ≤ ‖w‖ + ‖v‖ for r ∈ [0,1]
        have hr_abs : |r| ≤ 1 := by rw [abs_of_nonneg hr.1]; exact hr.2
        have hnorm1 : ‖w + r • v‖ ≤ ‖w‖ + ‖v‖ := by
          calc ‖w + r • v‖ ≤ ‖w‖ + ‖r • v‖ := norm_add_le w (r • v)
            _ = ‖w‖ + |r| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
            _ ≤ ‖w‖ + 1 * ‖v‖ := by nlinarith [hr_abs, norm_nonneg v]
            _ = ‖w‖ + ‖v‖ := by ring
        have hnorm2 : ‖w - r • v‖ ≤ ‖w‖ + ‖v‖ := by
          calc ‖w - r • v‖ ≤ ‖w‖ + ‖r • v‖ := norm_sub_le w (r • v)
            _ = ‖w‖ + |r| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
            _ ≤ ‖w‖ + 1 * ‖v‖ := by nlinarith [hr_abs, norm_nonneg v]
            _ = ‖w‖ + ‖v‖ := by ring
        -- Final bound
        have hsq1 : ‖w + r • v‖^2 ≤ (‖w‖ + ‖v‖)^2 :=
          sq_le_sq' (by linarith [norm_nonneg (w + r • v)]) hnorm1
        have hsq2 : ‖w - r • v‖^2 ≤ (‖w‖ + ‖v‖)^2 :=
          sq_le_sq' (by linarith [norm_nonneg (w - r • v)]) hnorm2
        calc |Q (w + r • v) - Q (w - r • v)|
            ≤ Q (w + r • v) + Q (w - r • v) := h1
          _ ≤ ‖w + r • v‖^2 + ‖w - r • v‖^2 := by linarith [hQ_bound1, hQ_bound2]
          _ ≤ (‖w‖ + ‖v‖)^2 + (‖w‖ + ‖v‖)^2 := by linarith [hsq1, hsq2]
          _ = 2 * (‖w‖ + ‖v‖)^2 := by ring
      exact bounded_jensen_is_linear hJ hD_zero' hBound t
    -- Rewrite in terms of Q
    -- hD_linear: D t = t * D 1
    -- D t = Q(w + t•v) - Q(w - t•v)
    -- D 1 = Q(w + v) - Q(w - v)  (from hD_one)
    simp only [hD_def, one_smul] at hD_linear hD_one
    linarith [hD_linear, hD_one]
  calc Q (w + t • v)
      = (Q (w + t • v) + Q (w - t • v)) / 2 + (Q (w + t • v) - Q (w - t • v)) / 2 := by ring
    _ = (Q w + t^2 * Q v) + t * (Q (w + v) - Q (w - v)) / 2 := by rw [heven, hodd_lin]
    _ = Q w + t * (Q (w + v) - Q (w - v)) / 2 + t^2 * Q v := by ring

/-- Polarization identity for measures.
    μ_{x,y}(E) = (1/4)[μ_{x+y}(E) - μ_{x-y}(E) + i·μ_{x+iy}(E) - i·μ_{x-iy}(E)]

    Note: hE is kept for documentation that E should be measurable, even though
    Measure.apply works on any set. -/
def spectralMeasurePolarized (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (x y : H) (E : Set Circle) (_hE : MeasurableSet E) : ℂ :=
  let μ_sum := (spectralMeasureDiagonal U hU (x + y) E).toReal
  let μ_diff := (spectralMeasureDiagonal U hU (x - y) E).toReal
  let μ_isum := (spectralMeasureDiagonal U hU (x + Complex.I • y) E).toReal
  let μ_idiff := (spectralMeasureDiagonal U hU (x - Complex.I • y) E).toReal
  -- Polarization identity: 4⟨x, Ay⟩ = Q(x+y) - Q(x-y) - i·Q(x+iy) + i·Q(x-iy)
  (1/4 : ℂ) * (μ_sum - μ_diff - Complex.I * μ_isum + Complex.I * μ_idiff)

/-- The polarized spectral integral gives back the inner product for continuous functions.

    For a continuous function f : Circle → ℝ, the polarized spectral measure satisfies:
    (1/4)[∫f dμ_{x+y} - ∫f dμ_{x-y} + i∫f dμ_{x+iy} - i∫f dμ_{x-iy}] = ⟨x, cfc(f, U) y⟩

    This is the key relationship connecting the spectral measure to CFC. -/
theorem spectralMeasurePolarized_integral (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (x y : H) (f : C_c(Circle, ℝ)) :
    let I_sum := ∫ z, f z ∂(spectralMeasureDiagonal U hU (x + y))
    let I_diff := ∫ z, f z ∂(spectralMeasureDiagonal U hU (x - y))
    let I_isum := ∫ z, f z ∂(spectralMeasureDiagonal U hU (x + Complex.I • y))
    let I_idiff := ∫ z, f z ∂(spectralMeasureDiagonal U hU (x - Complex.I • y))
    (1/4 : ℂ) * (I_sum - I_diff - Complex.I * I_isum + Complex.I * I_idiff) =
    @inner ℂ H _ x (cfcOfCircleReal U hU f.toContinuousMap y) := by
  -- Use RMK: ∫ f dμ_z = Λ_z(f) = spectralFunctionalAux U hU z f
  simp only
  rw [spectralMeasureDiagonal_integral U hU (x + y) f]
  rw [spectralMeasureDiagonal_integral U hU (x - y) f]
  rw [spectralMeasureDiagonal_integral U hU (x + Complex.I • y) f]
  rw [spectralMeasureDiagonal_integral U hU (x - Complex.I • y) f]
  -- Now use spectralFunctionalAux_polarization
  have hpol := spectralFunctionalAux_polarization U hU f.toContinuousMap x y
  -- hpol says: (1/4) * (Λ_{x+y}(f) - Λ_{x-y}(f) - I*Λ_{x+I•y}(f) + I*Λ_{x-I•y}(f)) = ⟨x, cfc(f)y⟩
  -- The spectralFunctionalCc is just spectralFunctionalAux applied to f.toContinuousMap
  show (1 / 4 : ℂ) * ((spectralFunctionalCc U hU (x + y)) f - (spectralFunctionalCc U hU (x - y)) f -
      Complex.I * (spectralFunctionalCc U hU (x + Complex.I • y)) f +
      Complex.I * (spectralFunctionalCc U hU (x - Complex.I • y)) f) =
    @inner ℂ H _ x (cfcOfCircleReal U hU f.toContinuousMap y)
  -- spectralFunctionalCc U hU z f = spectralFunctionalAux U hU z f.toContinuousMap
  unfold spectralFunctionalCc
  simp only [PositiveLinearMap.mk₀]
  exact hpol

/-- The diagonal case of spectralMeasurePolarized: B(z, z, E) = μ_z(E).toReal.

    This follows from the quadratic scaling property:
    - μ_{2z}(E) = 4 μ_z(E)
    - μ_0(E) = 0
    - μ_{(1+i)z}(E) = 2 μ_z(E)
    - μ_{(1-i)z}(E) = 2 μ_z(E)

    So B(z, z, E) = (1/4)[4μ_z - 0 - 2iμ_z + 2iμ_z] = μ_z(E) -/
theorem spectralMeasurePolarized_diag (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (z : H) (E : Set Circle) (hE : MeasurableSet E) :
    spectralMeasurePolarized U hU z z E hE = (spectralMeasureDiagonal U hU z E).toReal := by
  unfold spectralMeasurePolarized
  -- Simplify the combinations z + z, z - z, z + I•z, z - I•z
  have h_sum : z + z = (2 : ℂ) • z := by simp [two_smul]
  have h_diff : z - z = 0 := sub_self z
  have h_isum : z + Complex.I • z = (1 + Complex.I) • z := by
    rw [add_smul, one_smul]
  have h_idiff : z - Complex.I • z = (1 - Complex.I) • z := by
    rw [sub_smul, one_smul]
  -- Apply quadratic scaling μ_{cz}(E) = |c|² μ_z(E)
  have h_2z : (spectralMeasureDiagonal U hU ((2 : ℂ) • z) E).toReal =
      ‖(2 : ℂ)‖^2 * (spectralMeasureDiagonal U hU z E).toReal :=
    spectralMeasureDiagonal_smul_sq U hU 2 z E hE
  have h_0 : (spectralMeasureDiagonal U hU 0 E).toReal = 0 := by
    have h := spectralMeasureDiagonal_smul_sq U hU 0 z E hE
    simp only [zero_smul, norm_zero, sq, zero_mul] at h
    exact h
  have h_1pi : (spectralMeasureDiagonal U hU ((1 + Complex.I) • z) E).toReal =
      ‖(1 + Complex.I : ℂ)‖^2 * (spectralMeasureDiagonal U hU z E).toReal :=
    spectralMeasureDiagonal_smul_sq U hU (1 + Complex.I) z E hE
  have h_1mi : (spectralMeasureDiagonal U hU ((1 - Complex.I) • z) E).toReal =
      ‖(1 - Complex.I : ℂ)‖^2 * (spectralMeasureDiagonal U hU z E).toReal :=
    spectralMeasureDiagonal_smul_sq U hU (1 - Complex.I) z E hE
  -- Compute the norms: ‖c‖² = |c|² = c.normSq
  have hn_2 : ‖(2 : ℂ)‖^2 = 4 := by norm_num
  have hn_1pi : ‖(1 + Complex.I : ℂ)‖^2 = 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    -- 1 + I = 1 + 1*I, so normSq = 1² + 1² = 2
    have h : (1 : ℂ) + Complex.I = (1 : ℝ) + (1 : ℝ) * Complex.I := by simp
    rw [h, Complex.normSq_add_mul_I]; norm_num
  have hn_1mi : ‖(1 - Complex.I : ℂ)‖^2 = 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    -- 1 - I = 1 + (-1)*I, so normSq = 1² + (-1)² = 2
    have h : (1 : ℂ) - Complex.I = (1 : ℝ) + (-1 : ℝ) * Complex.I := by
      simp only [Complex.ofReal_one, Complex.ofReal_neg, neg_mul, one_mul]
      ring
    rw [h, Complex.normSq_add_mul_I]; norm_num
  -- Substitute
  rw [h_sum, h_diff, h_isum, h_idiff]
  rw [h_2z, h_0, h_1pi, h_1mi, hn_2, hn_1pi, hn_1mi]
  -- Simplify: (1/4) * (4μ - 0 - i*2μ + i*2μ) = μ
  set μ := (spectralMeasureDiagonal U hU z E).toReal with hμ_def
  simp only [Complex.ofReal_mul, Complex.ofReal_zero, sub_zero]
  -- Goal: (1/4) * (4*μ - I*2*μ + I*2*μ) = μ
  -- The I terms cancel: -I*2*μ + I*2*μ = 0
  push_cast
  ring

/-! ### Construction of Spectral Projections

For a Borel set E ⊆ Circle, the map (x, y) ↦ μ_{x,y}(E) is a bounded
sesquilinear form. We can use sesquilinearToOperator to get P(E).

This requires showing the bound |μ_{x,y}(E)| ≤ C·‖x‖·‖y‖
which follows from polarization and μ_x(Circle) = ‖x‖² -/

/-- Key algebraic identity for quadratic forms with parallelogram law.
    If Q satisfies Q(u+v) + Q(u-v) = 2Q(u) + 2Q(v), then:
    Q(a+b+c) - Q(a-b-c) = Q(a+b) + Q(a+c) - Q(a-b) - Q(a-c)

    Proof: Apply parallelogram twice.
    P(a+b, c): Q(a+b+c) + Q(a+b-c) = 2Q(a+b) + 2Q(c)
    P(a-b, c): Q(a-b+c) + Q(a-b-c) = 2Q(a-b) + 2Q(c)
    Subtract: Q(a+b+c) + Q(a+b-c) - Q(a-b+c) - Q(a-b-c) = 2Q(a+b) - 2Q(a-b)  ... (*)

    P(a+c, b): Q(a+c+b) + Q(a+c-b) = 2Q(a+c) + 2Q(b)
    P(a-c, b): Q(a-c+b) + Q(a-c-b) = 2Q(a-c) + 2Q(b)
    Subtract: Q(a+b+c) + Q(a-b+c) - Q(a+b-c) - Q(a-b-c) = 2Q(a+c) - 2Q(a-c)  ... (**)

    Add (*) and (**):
    2*Q(a+b+c) - 2*Q(a-b-c) = 2Q(a+b) - 2Q(a-b) + 2Q(a+c) - 2Q(a-c)
    Hence the result. -/
theorem quadraticForm_additivity_identity (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (E : Set Circle) (hE : MeasurableSet E) (a b c : H) :
    (spectralMeasureDiagonal U hU (a + b + c) E).toReal -
    (spectralMeasureDiagonal U hU (a - b - c) E).toReal =
    (spectralMeasureDiagonal U hU (a + b) E).toReal +
    (spectralMeasureDiagonal U hU (a + c) E).toReal -
    (spectralMeasureDiagonal U hU (a - b) E).toReal -
    (spectralMeasureDiagonal U hU (a - c) E).toReal := by
  -- Let Q(z) = μ_z(E).toReal. We use the parallelogram identity for Q.
  set Q := fun z => (spectralMeasureDiagonal U hU z E).toReal with hQ_def
  -- Parallelogram law: Q(u+v) + Q(u-v) = 2*Q(u) + 2*Q(v)
  have hpara : ∀ u v : H, Q (u + v) + Q (u - v) = 2 * Q u + 2 * Q v :=
    fun u v => spectralMeasureDiagonal_parallelogram U hU u v E hE
  -- Apply P(a+b, c): Q((a+b)+c) + Q((a+b)-c) = 2Q(a+b) + 2Q(c)
  have h1 := hpara (a + b) c
  -- Apply P(a-b, c): Q((a-b)+c) + Q((a-b)-c) = 2Q(a-b) + 2Q(c)
  have h2 := hpara (a - b) c
  -- Subtract h2 from h1: Q(a+b+c) + Q(a+b-c) - Q(a-b+c) - Q(a-b-c) = 2Q(a+b) - 2Q(a-b)
  have eq_star : Q (a + b + c) + Q (a + b - c) - Q (a - b + c) - Q (a - b - c) =
      2 * Q (a + b) - 2 * Q (a - b) := by linarith
  -- Apply P(a+c, b)
  have h3 := hpara (a + c) b
  have h3a : (a + c) + b = a + b + c := by abel
  have h3b : (a + c) - b = a - b + c := by abel
  simp only [h3a, h3b] at h3
  -- Apply P(a-c, b)
  have h4 := hpara (a - c) b
  have h4a : (a - c) + b = a + b - c := by abel
  have h4b : (a - c) - b = a - b - c := by abel
  simp only [h4a, h4b] at h4
  -- Subtract h4 from h3: Q(a+b+c) + Q(a-b+c) - Q(a+b-c) - Q(a-b-c) = 2Q(a+c) - 2Q(a-c)
  have eq_starstar : Q (a + b + c) + Q (a - b + c) - Q (a + b - c) - Q (a - b - c) =
      2 * Q (a + c) - 2 * Q (a - c) := by linarith
  -- Add eq_star and eq_starstar
  -- 2*Q(a+b+c) - 2*Q(a-b-c) = 2Q(a+b) - 2Q(a-b) + 2Q(a+c) - 2Q(a-c)
  linarith

/-- Additivity of the polarized spectral measure in the second argument. -/
theorem spectralMeasurePolarized_add_right (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (E : Set Circle) (hE : MeasurableSet E) (x y₁ y₂ : H) :
    spectralMeasurePolarized U hU x (y₁ + y₂) E hE =
    spectralMeasurePolarized U hU x y₁ E hE + spectralMeasurePolarized U hU x y₂ E hE := by
  set Q := fun z => (spectralMeasureDiagonal U hU z E).toReal with hQ_def
  unfold spectralMeasurePolarized
  simp only
  -- Use the algebraic identity: Q(a+b+c) - Q(a-b-c) = Q(a+b) + Q(a+c) - Q(a-b) - Q(a-c)
  have hreal := quadraticForm_additivity_identity U hU E hE x y₁ y₂
  have himag := quadraticForm_additivity_identity U hU E hE x (Complex.I • y₁) (Complex.I • y₂)
  have eq1 : x + (y₁ + y₂) = x + y₁ + y₂ := by abel
  have eq2 : x - (y₁ + y₂) = x - y₁ - y₂ := by abel
  have eq3 : x + Complex.I • (y₁ + y₂) = x + Complex.I • y₁ + Complex.I • y₂ := by
    simp only [smul_add]; abel
  have eq4 : x - Complex.I • (y₁ + y₂) = x - Complex.I • y₁ - Complex.I • y₂ := by
    simp only [smul_add]; abel
  simp only [eq1, eq2, eq3, eq4]
  have hreal' : Q (x + y₁ + y₂) - Q (x - y₁ - y₂) =
      Q (x + y₁) + Q (x + y₂) - Q (x - y₁) - Q (x - y₂) := hreal
  have himag' : Q (x + Complex.I • y₁ + Complex.I • y₂) - Q (x - Complex.I • y₁ - Complex.I • y₂) =
      Q (x + Complex.I • y₁) + Q (x + Complex.I • y₂) -
      Q (x - Complex.I • y₁) - Q (x - Complex.I • y₂) := himag
  set a1 := Q (x + y₁ + y₂) with ha1
  set a2 := Q (x - y₁ - y₂) with ha2
  set a3 := Q (x + Complex.I • y₁ + Complex.I • y₂) with ha3
  set a4 := Q (x - Complex.I • y₁ - Complex.I • y₂) with ha4
  set b1 := Q (x + y₁) with hb1
  set b2 := Q (x - y₁) with hb2
  set b3 := Q (x + Complex.I • y₁) with hb3
  set b4 := Q (x - Complex.I • y₁) with hb4
  set c1 := Q (x + y₂) with hc1
  set c2 := Q (x - y₂) with hc2
  set c3 := Q (x + Complex.I • y₂) with hc3
  set c4 := Q (x - Complex.I • y₂) with hc4
  have hr : a1 - a2 = b1 + c1 - b2 - c2 := hreal'
  have hi : a3 - a4 = b3 + c3 - b4 - c4 := himag'
  have hgoal : (a1 : ℂ) - a2 - Complex.I * a3 + Complex.I * a4 =
      (b1 - b2 - Complex.I * b3 + Complex.I * b4) +
      (c1 - c2 - Complex.I * c3 + Complex.I * c4) := by
    have hr_c : (a1 : ℂ) - a2 = b1 + c1 - b2 - c2 := by
      simp only [← Complex.ofReal_sub, ← Complex.ofReal_add]; norm_cast
    have hi_c : (a3 : ℂ) - a4 = b3 + c3 - b4 - c4 := by
      simp only [← Complex.ofReal_sub, ← Complex.ofReal_add]; norm_cast
    calc (a1 : ℂ) - a2 - Complex.I * a3 + Complex.I * a4
        = (a1 - a2) - Complex.I * (a3 - a4) := by ring
      _ = (b1 + c1 - b2 - c2) - Complex.I * (b3 + c3 - b4 - c4) := by rw [hr_c, hi_c]
      _ = (b1 - b2 - Complex.I * b3 + Complex.I * b4) +
          (c1 - c2 - Complex.I * c3 + Complex.I * c4) := by ring
  calc (1 / 4 : ℂ) * (a1 - a2 - Complex.I * a3 + Complex.I * a4)
      = (1 / 4 : ℂ) * ((b1 - b2 - Complex.I * b3 + Complex.I * b4) +
          (c1 - c2 - Complex.I * c3 + Complex.I * c4)) := by rw [hgoal]
    _ = (1 / 4 : ℂ) * (b1 - b2 - Complex.I * b3 + Complex.I * b4) +
        (1 / 4 : ℂ) * (c1 - c2 - Complex.I * c3 + Complex.I * c4) := by ring

/-- B(x, -z) = -B(x, z) for the polarized spectral measure. -/
theorem spectralMeasurePolarized_neg (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (E : Set Circle) (hE : MeasurableSet E) (x z : H) :
    spectralMeasurePolarized U hU x (-z) E hE = -spectralMeasurePolarized U hU x z E hE := by
  unfold spectralMeasurePolarized
  simp only
  -- Simplify: x + (-z) = x - z, x - (-z) = x + z, similarly for I•(-z)
  have eq1 : x + -z = x - z := by abel
  have eq2 : x - -z = x + z := by abel
  have eq3 : x + Complex.I • -z = x - Complex.I • z := by
    rw [smul_neg]; abel
  have eq4 : x - Complex.I • -z = x + Complex.I • z := by
    rw [smul_neg]; abel
  simp only [eq1, eq2, eq3, eq4]
  -- Now the formula rearranges to give the negative
  ring

/-- Natural number scalar multiplication for the polarized spectral measure. -/
theorem spectralMeasurePolarized_nsmul (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (E : Set Circle) (hE : MeasurableSet E) (x : H) (n : ℕ) (y : H) :
    spectralMeasurePolarized U hU x (n • y) E hE =
    (n : ℂ) * spectralMeasurePolarized U hU x y E hE := by
  induction n with
  | zero =>
    simp only [zero_smul, Nat.cast_zero, zero_mul]
    -- B(x, 0) = 0 from polarization (all points are x)
    unfold spectralMeasurePolarized
    -- x + 0 = x, x - 0 = x, x + I•0 = x, x - I•0 = x
    simp only [add_zero, sub_zero, smul_zero]
    -- All four terms are μ_x(E), so the alternating sum is 0
    ring
  | succ n ih =>
    rw [succ_nsmul, spectralMeasurePolarized_add_right U hU E hE x (n • y) y]
    rw [ih, Nat.cast_succ]
    ring

/-- Integer scalar multiplication for the polarized spectral measure. -/
theorem spectralMeasurePolarized_zsmul (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (E : Set Circle) (hE : MeasurableSet E) (x : H) (n : ℤ) (y : H) :
    spectralMeasurePolarized U hU x (n • y) E hE =
    (n : ℂ) * spectralMeasurePolarized U hU x y E hE := by
  cases n with
  | ofNat m =>
    simp only [Int.ofNat_eq_natCast, Int.cast_natCast, natCast_zsmul]
    exact spectralMeasurePolarized_nsmul U hU E hE x m y
  | negSucc m =>
    simp only [Int.cast_negSucc, negSucc_zsmul]
    rw [spectralMeasurePolarized_neg U hU E hE x _]
    rw [spectralMeasurePolarized_nsmul U hU E hE x (m + 1) y]
    ring

set_option backward.isDefEq.respectTransparency false in
/-- Real scalar multiplication for the polarized spectral measure.
    B(x, r•y) = r * B(x, y) for real r ∈ ℝ.

    The proof uses:
    1. Integer/rational homogeneity from additivity (proved above)
    2. Extension to reals via continuity (density of ℚ + boundedness)

    The boundedness |B(x,y)| ≤ ‖x‖² + ‖y‖² follows from the triangle inequality
    on the polarization formula plus the bound μ_z(E) ≤ ‖z‖². -/
theorem spectralMeasurePolarized_smul_real (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (E : Set Circle) (hE : MeasurableSet E) (x : H) (r : ℝ) (y : H) :
    spectralMeasurePolarized U hU x (r • y) E hE =
    (r : ℂ) * spectralMeasurePolarized U hU x y E hE := by
  -- Step 1: Prove for rationals using integer homogeneity
  -- For q = num/den (den ≠ 0): den • (q • y) = num • y
  -- So den * B(x, q•y) = B(x, num•y) = num * B(x, y), hence B(x, q•y) = q * B(x, y)
  have hrat : ∀ q : ℚ, spectralMeasurePolarized U hU x ((q : ℝ) • y) E hE =
      (q : ℂ) * spectralMeasurePolarized U hU x y E hE := by
    intro q
    -- Use q.den > 0 and q.den * q = q.num
    have hden_pos : 0 < q.den := q.den_pos
    have hden_ne_Z : (q.den : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hden_pos)
    -- Key: q.den * q = q.num (in ℚ)
    have hmul_Q : (q.den : ℚ) * q = q.num := by
      have hden_ne : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hden_pos)
      have h1 : (q.den : ℚ) * q = q.den * (q.num / q.den) := by
        congr 1
        exact (Rat.num_div_den q).symm
      rw [h1, mul_div_assoc']
      exact mul_div_cancel_left₀ _ hden_ne
    -- den • (q • y) = num • y in H
    -- Using that in a complex Hilbert space, z • v for z ∈ ℤ is (z : ℂ) • v
    -- and r • v for r ∈ ℝ is (r : ℂ) • v
    have hsmul_eq : (q.den : ℤ) • ((q : ℝ) • y) = (q.num : ℤ) • y := by
      -- Convert integer smul to complex smul, and real smul to complex smul
      rw [← Int.cast_smul_eq_zsmul ℂ (q.den : ℤ) ((q : ℝ) • y)]
      rw [← Int.cast_smul_eq_zsmul ℂ (q.num : ℤ) y]
      simp only [Int.cast_natCast]
      -- Now: (q.den : ℂ) • ((q : ℝ) • y) = (q.num : ℂ) • y
      -- Real smul on H is complex smul via inclusion ℝ → ℂ
      conv_lhs => rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (q : ℝ) y]
      -- Now: (q.den : ℂ) • ((q : ℂ) • y) = (q.num : ℂ) • y
      rw [smul_smul]
      -- Now: ((q.den : ℂ) * (q : ℂ)) • y = (q.num : ℂ) • y
      congr 1
      -- Need: (q.den : ℂ) * (q : ℂ) = (q.num : ℂ)
      -- Cast hmul_Q : (q.den : ℚ) * q = q.num to ℂ
      have h := congr_arg (fun r : ℚ => (r : ℂ)) hmul_Q
      simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast] at h
      exact h
    -- Apply integer homogeneity
    have h1 : spectralMeasurePolarized U hU x ((q.den : ℤ) • ((q : ℝ) • y)) E hE =
        (q.den : ℂ) * spectralMeasurePolarized U hU x ((q : ℝ) • y) E hE :=
      spectralMeasurePolarized_zsmul U hU E hE x q.den ((q : ℝ) • y)
    have h2 : spectralMeasurePolarized U hU x ((q.num : ℤ) • y) E hE =
        (q.num : ℂ) * spectralMeasurePolarized U hU x y E hE :=
      spectralMeasurePolarized_zsmul U hU E hE x q.num y
    -- Combine: den * B(x, q•y) = num * B(x, y)
    rw [hsmul_eq] at h1
    rw [h1] at h2
    -- Solve for B(x, q•y): den * B(x, q•y) = num * B(x, y)
    have hden_ne_C : (q.den : ℂ) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      exact Nat.pos_iff_ne_zero.mp hden_pos
    -- h2 : den * B(x, q•y) = num * B(x, y)
    -- Goal: B(x, q•y) = q * B(x, y) = (num/den) * B(x, y)
    have hgoal : spectralMeasurePolarized U hU x ((q : ℝ) • y) E hE =
        (q.num : ℂ) / (q.den : ℂ) * spectralMeasurePolarized U hU x y E hE := by
      field_simp [hden_ne_C] at h2 ⊢
      ring_nf at h2 ⊢
      exact h2
    rw [hgoal, Rat.cast_def]
  -- Step 2: Use density of ℚ in ℝ to extend to all reals
  -- Key: w ↦ μ_w(E) is continuous (using the bound μ_w(E) ≤ ‖w‖²)
  -- Hence z ↦ B(x, z) is continuous (polarization of continuous functions)
  -- Define the two functions we want to show are equal
  set f := fun s : ℝ => spectralMeasurePolarized U hU x (s • y) E hE with hf_def
  set g := fun s : ℝ => (s : ℂ) * spectralMeasurePolarized U hU x y E hE with hg_def
  -- They agree on rationals
  have heq_rat : ∀ q : ℚ, f (q : ℝ) = g (q : ℝ) := fun q => hrat q
  -- g is continuous
  have hg_cont : Continuous g := Continuous.mul continuous_ofReal continuous_const
  -- For f, we use that the polarization is continuous in the second argument
  -- The map w ↦ μ_w(E) is continuous because μ_w(E) ≤ ‖w‖² (uniform bound near 0)
  have hμ_cont : Continuous (fun w : H => (spectralMeasureDiagonal U hU w E).toReal) := by
    -- Use the fact that μ satisfies the parallelogram identity and is bounded by ‖w‖²
    -- This makes μ_w(E)^(1/2) a seminorm, hence continuous
    -- We prove continuity at each point v
    rw [continuous_def]
    intro s hs
    -- s is open in ℝ, we need to show preimage is open in H
    rw [isOpen_iff_mem_nhds]
    intro v hv
    -- hv : (spectralMeasureDiagonal U hU v E).toReal ∈ s
    -- We need to find a neighborhood of v that maps into s
    -- Since s is open and contains μ_v(E), there exists ε > 0 with (μ_v(E) - ε, μ_v(E) + ε) ⊆ s
    rw [Metric.isOpen_iff] at hs
    obtain ⟨ε, hε_pos, hε_ball⟩ := hs _ hv
    -- We need: |μ_w(E) - μ_v(E)| < ε for w near v
    -- Key bound: μ satisfies |μ_w(E) - μ_v(E)| ≤ (√μ_{w-v}(E) + 2√μ_v(E))√μ_{w-v}(E)
    --                                         ≤ (‖w-v‖ + 2‖v‖)‖w-v‖
    -- So for ‖w-v‖ small enough, |μ_w(E) - μ_v(E)| < ε
    -- Choose δ such that (δ + 2‖v‖)δ < ε
    -- For simplicity, use δ = min(ε/(4‖v‖ + 2), 1) if v ≠ 0, else δ = √ε
    have hbound : ∀ w : H, (spectralMeasureDiagonal U hU w E).toReal ≤ ‖w‖^2 := by
      intro w
      haveI : IsFiniteMeasure (spectralMeasureDiagonal U hU w) :=
        spectralMeasureDiagonal_isFiniteMeasure U hU w
      have hmono := MeasureTheory.measure_mono (μ := spectralMeasureDiagonal U hU w) (Set.subset_univ E)
      have huniv := spectralMeasureDiagonal_univ U hU w
      exact le_trans (ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) hmono)
                     (le_of_eq huniv)
    -- The seminorm property: √μ_w(E) satisfies the triangle inequality from the parallelogram identity
    -- This gives: |√μ_w - √μ_v| ≤ √μ_{w-v} ≤ ‖w-v‖
    -- Hence: |μ_w - μ_v| ≤ (√μ_w + √μ_v)|√μ_w - √μ_v| ≤ (‖w‖ + ‖v‖)‖w-v‖
    have hμ_nn : ∀ w, 0 ≤ (spectralMeasureDiagonal U hU w E).toReal := fun w => ENNReal.toReal_nonneg
    -- Key Lipschitz-type bound (from parallelogram identity + seminorm theory)
    have hLip : ∀ w, |(spectralMeasureDiagonal U hU w E).toReal -
        (spectralMeasureDiagonal U hU v E).toReal| ≤ (‖w‖ + ‖v‖) * ‖w - v‖ := by
      intro w
      -- Let p(z) = √μ_z(E). The parallelogram identity for μ implies p is a seminorm.
      -- By the reverse triangle inequality: |p(w) - p(v)| ≤ p(w - v) ≤ ‖w - v‖
      -- Then: |μ_w - μ_v| = |p(w)² - p(v)²| = |p(w) + p(v)||p(w) - p(v)|
      --                   ≤ (‖w‖ + ‖v‖)‖w - v‖
      set μw := (spectralMeasureDiagonal U hU w E).toReal with hμw_def
      set μv := (spectralMeasureDiagonal U hU v E).toReal with hμv_def
      set pwv := (spectralMeasureDiagonal U hU (w - v) E).toReal with hpwv_def
      -- Key seminorm bound: |√μw - √μv| ≤ √pwv (reverse triangle inequality)
      -- Proof: Cauchy-Schwarz for polarized form gives ⟨w,v⟩ ≤ √μw√μv,
      -- which implies μ_{w+v} ≤ (√μw + √μv)², hence √μ_{w+v} ≤ √μw + √μv
      have hseminorm : |Real.sqrt μw - Real.sqrt μv| ≤ Real.sqrt pwv := by
        have hpara := spectralMeasureDiagonal_parallelogram U hU w v E hE
        -- hpara: μ_{w+v} + μ_{w-v} = 2μ_w + 2μ_v
        set μwpv := (spectralMeasureDiagonal U hU (w + v) E).toReal with hμwpv_def
        set μwmv := (spectralMeasureDiagonal U hU (w - v) E).toReal with hμwmv_def
        have hpwv_eq : pwv = μwmv := rfl
        set inner_wv := (μwpv - μwmv) / 4 with hinner_wv_def
        -- Cauchy-Schwarz: |⟨w,v⟩| ≤ √μw√μv via discriminant argument
        -- μ_{w+tv} = μw + 2t·inner_wv + t²μv ≥ 0 for all t implies discriminant ≤ 0
        have hCS : |inner_wv| ≤ Real.sqrt μw * Real.sqrt μv := by
          have h_nonneg : ∀ z : H, 0 ≤ (spectralMeasureDiagonal U hU z E).toReal :=
            fun z => ENNReal.toReal_nonneg
          have hquad_nonneg : ∀ t : ℝ, (spectralMeasureDiagonal U hU (w + t • v) E).toReal ≥ 0 :=
            fun t => h_nonneg (w + t • v)
          by_cases hμv_zero : μv = 0
          · -- If μv = 0, then √μv = 0, so RHS = √μw · 0 = 0
            -- We need to show |inner_wv| ≤ 0, i.e., inner_wv = 0
            -- From parallelogram: μwpv + μwmv = 2μw + 2μv = 2μw (since μv = 0)
            -- If μv = 0, by the parallelogram identity applied to (v, v):
            -- μ_{2v} + μ_0 = 2μv + 2μv = 0, so μ_{2v} = 0
            -- And by (w, v): μwpv + μwmv = 2μw + 0 = 2μw
            -- We claim μwpv = μwmv = μw when μv = 0.
            -- Proof: Use parallelogram with (w+v, v) and (w-v, v):
            -- μ_{w+2v} + μ_w = 2μ_{w+v} + 2μv = 2μwpv
            -- μ_w + μ_{w-2v} = 2μ_{w-v} + 2μv = 2μwmv
            -- When μv = 0, we have μ_{tv} = 0 for all t (by scaling property of measures)
            -- Actually, we don't have scaling established yet...
            -- Use a different approach: bound |μwpv - μwmv| using nonnegativity
            -- Both μwpv, μwmv ≥ 0 and μwpv + μwmv = 2μw
            -- So each is between 0 and 2μw, and |μwpv - μwmv| ≤ 2μw
            -- Thus |inner_wv| ≤ μw/2. But we need |inner_wv| ≤ 0 when μv = 0.
            -- This requires showing μwpv = μwmv when μv = 0, which needs more structure.
            -- Use the quadratic expansion: μ_{w+tv} = μ_w + 2t·inner_wv + t²·μ_v
            -- μv = 0: quadratic becomes linear μw + 2t·inner_wv ≥ 0 for all t, so inner_wv = 0
            simp only [hμv_zero, Real.sqrt_zero, mul_zero]
            have hquad : ∀ t : ℝ, (spectralMeasureDiagonal U hU (w + t • v) E).toReal =
                μw + 2 * t * (μwpv - μwmv) / 4 + t^2 * μv := fun t =>
              spectralMeasureDiagonal_quadratic_expansion U hU w v E hE t
            have hquad_linear : ∀ t : ℝ, (spectralMeasureDiagonal U hU (w + t • v) E).toReal =
                μw + 2 * t * inner_wv := by
              intro t; rw [hquad t, hμv_zero]; simp only [hinner_wv_def]; ring
            have hquad_nonneg : ∀ t : ℝ, μw + 2 * t * inner_wv ≥ 0 := by
              intro t; rw [← hquad_linear t]; exact h_nonneg (w + t • v)
            have h_pos : μw + 2 * inner_wv ≥ 0 := by simpa using hquad_nonneg 1
            have h_neg : μw - 2 * inner_wv ≥ 0 := by
              have := hquad_nonneg (-1); simp only [mul_neg] at this ⊢; linarith
            -- If inner_wv ≠ 0, take t = -(μw+1)/(2·inner_wv) to get contradiction
            by_contra h_ne
            have h_ne' : inner_wv ≠ 0 := by intro heq; rw [heq, abs_zero] at h_ne; exact h_ne (le_refl 0)
            have hμw_nonneg : μw ≥ 0 := h_nonneg w
            rcases lt_trichotomy inner_wv 0 with hneg | hzero | hpos_case
            · -- inner_wv < 0: take t = -(μw+1)/(2·inner_wv), gives μw + 2t·inner_wv = -1 < 0
              have t_val : μw + 2 * (-(μw + 1) / (2 * inner_wv)) * inner_wv < 0 := by
                have h2inner_ne : 2 * inner_wv ≠ 0 := by linarith
                have hcalc : 2 * (-(μw + 1) / (2 * inner_wv)) * inner_wv = -(μw + 1) := by
                  field_simp [h2inner_ne]
                rw [hcalc]; linarith
              linarith [hquad_nonneg (-(μw + 1) / (2 * inner_wv))]
            · exact h_ne' hzero
            · -- inner_wv > 0: same t gives μw + 2t·inner_wv = -1 < 0
              have t_val : μw + 2 * (-(μw + 1) / (2 * inner_wv)) * inner_wv < 0 := by
                have h2inner_ne : 2 * inner_wv ≠ 0 := by linarith
                have hcalc : 2 * (-(μw + 1) / (2 * inner_wv)) * inner_wv = -(μw + 1) := by
                  field_simp [h2inner_ne]
                rw [hcalc]; linarith
              linarith [hquad_nonneg (-(μw + 1) / (2 * inner_wv))]
          · -- μv > 0: discriminant argument for nonneg quadratic
            have hμv_pos : 0 < μv := lt_of_le_of_ne (h_nonneg v) (Ne.symm hμv_zero)
            have hquad : ∀ t : ℝ, (spectralMeasureDiagonal U hU (w + t • v) E).toReal =
                μw + 2 * t * (μwpv - μwmv) / 4 + t^2 * μv := fun t =>
              spectralMeasureDiagonal_quadratic_expansion U hU w v E hE t
            have hquad' : ∀ t : ℝ, (spectralMeasureDiagonal U hU (w + t • v) E).toReal =
                μw + 2 * t * inner_wv + t^2 * μv := by
              intro t; rw [hquad t]; simp only [hinner_wv_def]; ring
            have hquad_nonneg : ∀ t : ℝ, μw + 2 * t * inner_wv + t^2 * μv ≥ 0 := by
              intro t; rw [← hquad' t]; exact h_nonneg (w + t • v)
            -- At t₀ = -inner_wv/μv: f(t₀) = μw - inner_wv²/μv ≥ 0
            have hμv_ne : μv ≠ 0 := ne_of_gt hμv_pos
            have hmin_val : μw + 2 * (-inner_wv / μv) * inner_wv + (-inner_wv / μv)^2 * μv ≥ 0 :=
              hquad_nonneg (-inner_wv / μv)
            have hsimp : μw + 2 * (-inner_wv / μv) * inner_wv + (-inner_wv / μv)^2 * μv =
                μw - inner_wv^2 / μv := by field_simp [hμv_ne]; ring
            rw [hsimp] at hmin_val
            have hbound : inner_wv^2 ≤ μw * μv := by
              have h : inner_wv^2 / μv ≤ μw := by linarith
              calc inner_wv^2 = (inner_wv^2 / μv) * μv := by field_simp [hμv_ne]
                _ ≤ μw * μv := mul_le_mul_of_nonneg_right h (le_of_lt hμv_pos)
            have hμw_nn : 0 ≤ μw := h_nonneg w
            calc |inner_wv| = Real.sqrt (inner_wv^2) := (Real.sqrt_sq_eq_abs inner_wv).symm
              _ ≤ Real.sqrt (μw * μv) := Real.sqrt_le_sqrt hbound
              _ = Real.sqrt μw * Real.sqrt μv := Real.sqrt_mul hμw_nn μv
        -- From Cauchy-Schwarz and parallelogram, derive triangle inequality
        have htriangle : Real.sqrt μwpv ≤ Real.sqrt μw + Real.sqrt μv := by
          -- μ_{w+v} = μw + μv + 2·(4·inner_wv) = μw + μv + 2·(μwpv - μwmv)/2
          -- Wait, let me recalculate. From parallelogram: μwpv + μwmv = 2μw + 2μv
          -- So μwpv = 2μw + 2μv - μwmv
          -- We want: μwpv ≤ (√μw + √μv)² = μw + 2√μw√μv + μv
          -- i.e., 2μw + 2μv - μwmv ≤ μw + 2√μw√μv + μv
          -- i.e., μw + μv ≤ μwmv + 2√μw√μv
          -- i.e., μw + μv - 2√μw√μv ≤ μwmv
          -- i.e., (√μw - √μv)² ≤ μwmv = pwv
          -- This is exactly what we're trying to prove! So the triangle and reverse triangle
          -- are equivalent given the parallelogram identity.
          -- Use Cauchy-Schwarz: (μwpv - μwmv)/4 ≤ √μw√μv
          -- So μwpv - μwmv ≤ 4√μw√μv
          -- And μwpv = 2μw + 2μv - μwmv (parallelogram)
          -- So μwpv ≤ μw + μv + (μwpv - μwmv)/2 = μw + μv + 2inner_wv
          --        ≤ μw + μv + 2|inner_wv| ≤ μw + μv + 2√μw√μv = (√μw + √μv)²
          have h1 : μwpv ≤ μw + μv + 2 * |inner_wv| := by
            have hpara' : μwpv = 2 * μw + 2 * μv - μwmv := by linarith [hpara]
            have hinner : μwpv - μwmv = 4 * inner_wv := by
              simp only [hinner_wv_def]
              ring
            have h2 : μwpv = μw + μv + (μwpv - μwmv) / 2 := by linarith [hpara]
            rw [h2, hinner]
            have h3 : 4 * inner_wv / 2 = 2 * inner_wv := by ring
            rw [h3]
            by_cases hpos : inner_wv ≥ 0
            · simp only [abs_of_nonneg hpos]; linarith
            · push_neg at hpos
              have hneg : inner_wv < 0 := hpos
              simp only [abs_of_neg hneg]; linarith
          have h2 : μw + μv + 2 * |inner_wv| ≤ μw + μv + 2 * Real.sqrt μw * Real.sqrt μv := by
            linarith [hCS]
          have h3 : μw + μv + 2 * Real.sqrt μw * Real.sqrt μv = (Real.sqrt μw + Real.sqrt μv)^2 := by
            have hμw_nn' := hμ_nn w
            have hμv_nn' := hμ_nn v
            rw [add_sq, Real.sq_sqrt hμw_nn', Real.sq_sqrt hμv_nn']
            ring
          have h4 : μwpv ≤ (Real.sqrt μw + Real.sqrt μv)^2 := by linarith [h1, h2, h3]
          have h5 : Real.sqrt μwpv ≤ Real.sqrt ((Real.sqrt μw + Real.sqrt μv)^2) :=
            Real.sqrt_le_sqrt h4
          rw [Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))] at h5
          exact h5
        -- Now derive reverse triangle from parallelogram and triangle
        -- From parallelogram: μwpv + μwmv = 2μw + 2μv, i.e., μwmv = 2μw + 2μv - μwpv
        -- We want: (√μw - √μv)² ≤ μwmv = pwv
        -- Expanding: μw + μv - 2√μw√μv ≤ μwmv
        -- i.e., μw + μv - 2√μw√μv ≤ 2μw + 2μv - μwpv
        -- i.e., μwpv ≤ μw + μv + 2√μw√μv = (√μw + √μv)²
        -- i.e., √μwpv ≤ √μw + √μv (which is htriangle!)
        have h_nonneg : ∀ z : H, 0 ≤ (spectralMeasureDiagonal U hU z E).toReal :=
          fun z => ENNReal.toReal_nonneg
        have hμw_nn := h_nonneg w
        have hμv_nn := h_nonneg v
        have hrev : (Real.sqrt μw - Real.sqrt μv)^2 ≤ pwv := by
          rw [hpwv_eq]
          have hpara' : μwmv = 2 * μw + 2 * μv - μwpv := by linarith [hpara]
          have htri_sq : μwpv ≤ (Real.sqrt μw + Real.sqrt μv)^2 := by
            have h := htriangle
            have h' : Real.sqrt μwpv ^ 2 ≤ (Real.sqrt μw + Real.sqrt μv)^2 :=
              sq_le_sq' (by linarith [Real.sqrt_nonneg μwpv]) h
            rw [Real.sq_sqrt (h_nonneg (w + v))] at h'
            exact h'
          calc (Real.sqrt μw - Real.sqrt μv)^2
              = μw + μv - 2 * Real.sqrt μw * Real.sqrt μv := by
                rw [sub_sq, Real.sq_sqrt hμw_nn, Real.sq_sqrt hμv_nn]; ring
            _ = 2 * μw + 2 * μv - (μw + μv + 2 * Real.sqrt μw * Real.sqrt μv) := by ring
            _ = 2 * μw + 2 * μv - (Real.sqrt μw + Real.sqrt μv)^2 := by
                rw [add_sq, Real.sq_sqrt hμw_nn, Real.sq_sqrt hμv_nn]; ring
            _ ≤ 2 * μw + 2 * μv - μwpv := by linarith [htri_sq]
            _ = μwmv := by linarith [hpara']
        -- From (√μw - √μv)² ≤ pwv, deduce |√μw - √μv| ≤ √pwv
        have hpwv_nn : 0 ≤ pwv := hμ_nn (w - v)
        have h := Real.sqrt_le_sqrt hrev
        rw [Real.sqrt_sq_eq_abs] at h
        exact h
      -- Bound: |μw - μv| = |√μw + √μv| |√μw - √μv| ≤ (‖w‖ + ‖v‖) √pwv ≤ (‖w‖ + ‖v‖)‖w-v‖
      calc |μw - μv| = |Real.sqrt μw + Real.sqrt μv| * |Real.sqrt μw - Real.sqrt μv| := by
              rw [← abs_mul, ← sq_sub_sq]
              simp only [hμw_def, hμv_def, Real.sq_sqrt (hμ_nn w), Real.sq_sqrt (hμ_nn v)]
        _ ≤ |Real.sqrt μw + Real.sqrt μv| * Real.sqrt pwv := by
              apply mul_le_mul_of_nonneg_left hseminorm (abs_nonneg _)
        _ ≤ (Real.sqrt μw + Real.sqrt μv) * Real.sqrt pwv := by
              apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
              rw [abs_of_nonneg]
              exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        _ ≤ (‖w‖ + ‖v‖) * ‖w - v‖ := by
              apply mul_le_mul
              · apply add_le_add
                · calc Real.sqrt μw ≤ Real.sqrt (‖w‖^2) := Real.sqrt_le_sqrt (hbound w)
                    _ = ‖w‖ := Real.sqrt_sq (norm_nonneg w)
                · calc Real.sqrt μv ≤ Real.sqrt (‖v‖^2) := Real.sqrt_le_sqrt (hbound v)
                    _ = ‖v‖ := Real.sqrt_sq (norm_nonneg v)
              · calc Real.sqrt pwv ≤ Real.sqrt (‖w - v‖^2) := Real.sqrt_le_sqrt (hbound (w - v))
                  _ = ‖w - v‖ := Real.sqrt_sq (norm_nonneg (w - v))
              · exact Real.sqrt_nonneg pwv
              · exact add_nonneg (norm_nonneg w) (norm_nonneg v)
    -- Use Metric.mem_nhds_iff
    rw [Metric.mem_nhds_iff]
    -- Choose δ based on ε and ‖v‖
    by_cases hv : v = 0
    · -- Case v = 0: need |μ_w(E) - μ_0(E)| < ε for small w
      -- μ_0(E) ≤ μ_0(Circle) = ‖0‖² = 0, so μ_0(E) = 0
      subst hv
      have hμ0 : (spectralMeasureDiagonal U hU 0 E).toReal = 0 := by
        have h := hbound 0
        simp only [norm_zero, sq, mul_zero] at h
        exact le_antisymm h (hμ_nn 0)
      use Real.sqrt (ε / 2)
      constructor
      · exact Real.sqrt_pos.mpr (div_pos hε_pos two_pos)
      · intro w hw
        apply hε_ball
        rw [Metric.mem_ball, Real.dist_eq]
        simp only [hμ0, sub_zero]
        have hμw_bound := hbound w
        rw [Metric.mem_ball] at hw
        simp only [dist_zero_right] at hw
        calc |(spectralMeasureDiagonal U hU w E).toReal|
            = (spectralMeasureDiagonal U hU w E).toReal := abs_of_nonneg (hμ_nn w)
          _ ≤ ‖w‖^2 := hμw_bound
          _ < (Real.sqrt (ε / 2))^2 := sq_lt_sq' (by linarith [norm_nonneg w]) hw
          _ = ε / 2 := Real.sq_sqrt (le_of_lt (div_pos hε_pos two_pos))
          _ < ε := by linarith
    · -- Case v ≠ 0: use Lipschitz bound
      -- Need (‖w‖ + ‖v‖)‖w - v‖ < ε
      -- If ‖w - v‖ < δ and δ ≤ 1, then ‖w‖ ≤ ‖v‖ + 1, so (‖w‖ + ‖v‖) ≤ 2‖v‖ + 1
      -- We want (2‖v‖ + 1)δ < ε, so take δ = ε / (2(2‖v‖ + 1))
      set δ := min 1 (ε / (2 * (2 * ‖v‖ + 1))) with hδ_def
      use δ
      constructor
      · apply lt_min_iff.mpr
        constructor
        · exact one_pos
        · apply div_pos hε_pos
          linarith [norm_nonneg v]
      · intro w hw
        apply hε_ball
        rw [Metric.mem_ball, Real.dist_eq]
        rw [Metric.mem_ball, dist_eq_norm] at hw
        have hw_dist : ‖w - v‖ < δ := hw
        have hδ_le_1 : δ ≤ 1 := min_le_left _ _
        have hw_norm : ‖w‖ ≤ ‖v‖ + 1 := by
          have h1 : ‖w‖ ≤ ‖w - v‖ + ‖v‖ := by
            calc ‖w‖ = ‖(w - v) + v‖ := by congr 1; abel
              _ ≤ ‖w - v‖ + ‖v‖ := norm_add_le _ _
          linarith
        calc |(spectralMeasureDiagonal U hU w E).toReal -
                (spectralMeasureDiagonal U hU v E).toReal|
            ≤ (‖w‖ + ‖v‖) * ‖w - v‖ := hLip w
          _ ≤ (‖v‖ + 1 + ‖v‖) * δ := by
              apply mul_le_mul
              · linarith
              · exact le_of_lt hw_dist
              · exact norm_nonneg _
              · linarith [norm_nonneg w, norm_nonneg v]
          _ = (2 * ‖v‖ + 1) * δ := by ring
          _ ≤ (2 * ‖v‖ + 1) * (ε / (2 * (2 * ‖v‖ + 1))) := by
              apply mul_le_mul_of_nonneg_left (min_le_right _ _)
              linarith [norm_nonneg v]
          _ = ε / 2 := by
              have h2v1_pos : 2 * ‖v‖ + 1 > 0 := by linarith [norm_nonneg v]
              field_simp
          _ < ε := by linarith
  -- f is continuous: composition of continuous maps
  have hf_cont : Continuous f := by
    simp only [hf_def]
    -- f(s) = (1/4) * (a(s) - b(s) - I*c(s) + I*d(s)) where a,b,c,d are continuous
    -- Expression structure: ((a - b) - I*c) + I*d
    unfold spectralMeasurePolarized
    apply Continuous.mul continuous_const
    -- Goal: ((a - b) - I*c) + I*d is continuous
    apply Continuous.add
    · -- ((a - b) - I*c) is continuous
      apply Continuous.sub
      · -- (a - b) is continuous
        apply Continuous.sub
        · -- a(s) = μ_{x + s•y}(E) is continuous (cast to ℂ)
          apply Continuous.comp continuous_ofReal
          apply Continuous.comp hμ_cont
          exact continuous_const.add (continuous_smul.comp (Continuous.prodMk continuous_id continuous_const))
        · -- b(s) = μ_{x - s•y}(E) is continuous (cast to ℂ)
          apply Continuous.comp continuous_ofReal
          apply Continuous.comp hμ_cont
          exact continuous_const.sub (continuous_smul.comp (Continuous.prodMk continuous_id continuous_const))
      · -- I*c(s) = I * μ_{x + I•(s•y)}(E) is continuous
        apply Continuous.mul continuous_const
        apply Continuous.comp continuous_ofReal
        apply Continuous.comp hμ_cont
        apply continuous_const.add
        apply Continuous.smul continuous_const
        exact continuous_smul.comp (Continuous.prodMk continuous_id continuous_const)
    · -- I*d(s) = I * μ_{x - I•(s•y)}(E) is continuous
      apply Continuous.mul continuous_const
      apply Continuous.comp continuous_ofReal
      apply Continuous.comp hμ_cont
      apply continuous_const.sub
      apply Continuous.smul continuous_const
      exact continuous_smul.comp (Continuous.prodMk continuous_id continuous_const)
  -- Use density: f and g agree on ℚ and are continuous, hence equal on ℝ
  have hdense : DenseRange ((↑) : ℚ → ℝ) := Rat.denseRange_cast
  have heq : f = g := by
    apply hdense.equalizer hf_cont hg_cont
    funext q
    exact heq_rat q
  exact congrFun heq r

/-- The polarized spectral measure defines a sesquilinear form.
    This is linear in the second argument (y). -/
theorem spectralMeasurePolarized_linear_right (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (E : Set Circle) (hE : MeasurableSet E) (x : H) :
    IsLinearMap ℂ (fun y => spectralMeasurePolarized U hU x y E hE) := by
  -- Use the separated additivity lemma and prove scalar multiplication
  set Q := fun z => (spectralMeasureDiagonal U hU z E).toReal with hQ_def
  constructor
  · -- Additivity: use the separated lemma
    exact fun y₁ y₂ => spectralMeasurePolarized_add_right U hU E hE x y₁ y₂
  · -- Scalar multiplication: B(x, c • y) = c * B(x, y)
    intro c y
    -- Strategy: prove c * B = B(-, c•-) by showing:
    -- 1. i-linearity: B(x, i•y) = i * B(x, y) (direct computation from polarization formula)
    -- 2. ℚ-linearity: from additivity
    -- 3. ℝ-linearity: from ℚ-linearity + continuity (boundedness)
    -- 4. ℂ-linearity: from ℝ-linearity + i-linearity
    --
    -- First, prove i-linearity: B(x, i•y) = i * B(x, y)
    -- B(x, i•y) = (1/4)[Q(x+i•y) - Q(x-i•y) - i*Q(x+i²•y) + i*Q(x-i²•y)]
    --           = (1/4)[Q(x+i•y) - Q(x-i•y) - i*Q(x-y) + i*Q(x+y)]
    -- i*B(x, y) = i * (1/4)[Q(x+y) - Q(x-y) - i*Q(x+i•y) + i*Q(x-i•y)]
    --           = (1/4)[i*Q(x+y) - i*Q(x-y) + Q(x+i•y) - Q(x-i•y)]
    -- These are equal!
    have hi_linear : spectralMeasurePolarized U hU x (Complex.I • y) E hE =
        Complex.I * spectralMeasurePolarized U hU x y E hE := by
      unfold spectralMeasurePolarized
      simp only
      -- i • (i • y) = (i * i) • y = (-1) • y = -y
      have hi2 : Complex.I • Complex.I • y = -y := by
        calc Complex.I • Complex.I • y = (Complex.I * Complex.I) • y := by rw [smul_smul]
          _ = (-1 : ℂ) • y := by rw [Complex.I_mul_I]
          _ = -y := by simp
      -- Simplify the terms
      have h1 : x + Complex.I • (Complex.I • y) = x - y := by rw [hi2]; abel
      have h2 : x - Complex.I • (Complex.I • y) = x + y := by rw [hi2]; abel
      simp only [h1, h2]
      -- Now show the algebra works out
      set q1 := (spectralMeasureDiagonal U hU (x + Complex.I • y) E).toReal with hq1
      set q2 := (spectralMeasureDiagonal U hU (x - Complex.I • y) E).toReal with hq2
      set q3 := (spectralMeasureDiagonal U hU (x + y) E).toReal with hq3
      set q4 := (spectralMeasureDiagonal U hU (x - y) E).toReal with hq4
      -- LHS: (1/4) * (q1 - q2 - i*q4 + i*q3) (note: x + i•(i•y) = x - y, x - i•(i•y) = x + y)
      -- RHS: i * (1/4) * (q3 - q4 - i*q1 + i*q2) = (1/4) * (i*q3 - i*q4 + q1 - q2)
      -- These are equal by commutativity of addition
      -- The key: I * (q3 - q4 - I*q1 + I*q2) = I*q3 - I*q4 - I²*q1 + I²*q2
      --        = I*q3 - I*q4 + q1 - q2  (using I² = -1)
      --        = q1 - q2 + I*q3 - I*q4
      have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
      -- Compute RHS and show equal to LHS
      have hrhs : Complex.I * ((1 / 4 : ℂ) * ((q3 : ℂ) - q4 - Complex.I * q1 + Complex.I * q2)) =
          (1 / 4 : ℂ) * (q1 - q2 + Complex.I * q3 - Complex.I * q4) := by
        calc Complex.I * ((1 / 4 : ℂ) * (q3 - q4 - Complex.I * q1 + Complex.I * q2))
            = (1 / 4 : ℂ) * (Complex.I * (q3 - q4 - Complex.I * q1 + Complex.I * q2)) := by ring
          _ = (1 / 4 : ℂ) * (Complex.I * q3 - Complex.I * q4 -
                Complex.I * Complex.I * q1 + Complex.I * Complex.I * q2) := by ring
          _ = (1 / 4 : ℂ) * (Complex.I * q3 - Complex.I * q4 - (-1) * q1 + (-1) * q2) := by
              rw [hI2]
          _ = (1 / 4 : ℂ) * (q1 - q2 + Complex.I * q3 - Complex.I * q4) := by ring
      rw [hrhs]
      ring
    -- For general c, decompose c = re + im * i where re, im ∈ ℝ
    -- c • y = re • y + im • (i • y)
    -- By additivity and i-linearity:
    -- B(x, c•y) = B(x, re•y) + B(x, im•(i•y)) = B(x, re•y) + im * B(x, i•y)
    --           = B(x, re•y) + im * i * B(x, y)
    -- For real scalar re, we use ℚ-linearity (from additivity) + boundedness (gives continuity)
    -- The bound |B(x,y)| ≤ ‖x‖² + ‖y‖² follows from the triangle inequality on the polarization
    set re := c.re with hre_def
    set im := c.im with him_def
    -- c.re_add_im gives c = ↑c.re + ↑c.im * I
    have hc_decomp : c = (re : ℂ) + (im : ℂ) * Complex.I := c.re_add_im.symm
    have hcy_decomp : c • y = re • y + im • (Complex.I • y) := by
      rw [hc_decomp]
      simp only [add_smul, mul_smul]
      -- Need: (↑re) • y + ((↑im) * I) • y = re • y + im • (I • y)
      -- Use congr to reduce to showing (↑im * I) • y = im • I • y
      congr 1
    -- Use additivity (from the separate lemma, not recursive)
    have hadd : spectralMeasurePolarized U hU x (re • y + im • (Complex.I • y)) E hE =
        spectralMeasurePolarized U hU x (re • y) E hE +
        spectralMeasurePolarized U hU x (im • (Complex.I • y)) E hE :=
      spectralMeasurePolarized_add_right U hU E hE x (re • y) (im • (Complex.I • y))
    rw [hcy_decomp, hadd]
    -- Now need to show:
    -- B(x, re•y) + B(x, im•(i•y)) = c • B(x, y)
    -- = (re + i*im) • B(x, y) = re * B(x, y) + im * i * B(x, y)
    -- = re * B(x, y) + im * B(x, i•y) (by hi_linear)
    -- Use the real scalar multiplication lemma
    rw [spectralMeasurePolarized_smul_real U hU E hE x re y]
    rw [spectralMeasurePolarized_smul_real U hU E hE x im (Complex.I • y)]
    rw [hi_linear]
    -- Goal: re * B(x,y) + im * (I * B(x,y)) = c • B(x,y)
    -- For ℂ, c • z = c * z, so c • B = c * B
    simp only [smul_eq_mul]
    rw [hc_decomp]
    ring

/-- The polarized spectral measure is conjugate-linear in the first argument (x).
    Proof outline:
    1. Define D(a,b) = μ_{a+b} - μ_{a-b}. Then B(x,y) = (1/4)[D(x,y) - i·D(x,iy)]
    2. D is additive in first arg: D(a₁+a₂, b) = D(a₁,b) + D(a₂,b) (from parallelogram)
    3. Hence B is additive: B(x₁+x₂, y) = B(x₁,y) + B(x₂,y)
    4. For real c: B(c·x, y) = c·B(x,y) (from D(c·a, b) = c·D(a,b))
    5. For c = i: D(ix,y) = 4·Im(B(x,y)), D(ix,iy) = D(x,y)
       So B(ix,y) = (1/4)[D(ix,y) - i·D(ix,iy)] = Im(B) - i·Re(B) = -i·B(x,y)
    6. Combine: B(c·x,y) = c̄·B(x,y) for all c ∈ ℂ -/
theorem spectralMeasurePolarized_conj_linear_left (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (E : Set Circle) (hE : MeasurableSet E) :
    ∀ y c x₁ x₂, spectralMeasurePolarized U hU (c • x₁ + x₂) y E hE =
      starRingEnd ℂ c * spectralMeasurePolarized U hU x₁ y E hE +
      spectralMeasurePolarized U hU x₂ y E hE := by
  intro y c x₁ x₂
  -- Define μ for convenience
  let μ := fun z => (spectralMeasureDiagonal U hU z E).toReal
  -- Q(-w) = Q(w) by the scaling property with c = -1
  have hμ_neg : ∀ w : H, μ (-w) = μ w := by
    intro w
    have hscale := spectralMeasureDiagonal_smul_sq U hU (-1 : ℂ) w E hE
    have hn1 : ‖(-1 : ℂ)‖ = 1 := by rw [norm_neg, norm_one]
    simp only [neg_one_smul, hn1, one_pow, one_mul] at hscale
    exact hscale
  -- μ_{I•z} = μ_z (since |I| = 1)
  have hμ_I : ∀ w : H, μ (Complex.I • w) = μ w := by
    intro w
    have hscale := spectralMeasureDiagonal_smul_sq U hU Complex.I w E hE
    have hI1 : ‖Complex.I‖ = 1 := Complex.norm_I
    simp only [hI1, one_pow, one_mul] at hscale
    exact hscale
  -- Step 1: Prove additivity in first argument using quadraticForm_additivity_identity
  have hB_add_left : ∀ a b : H, spectralMeasurePolarized U hU (a + b) y E hE =
      spectralMeasurePolarized U hU a y E hE + spectralMeasurePolarized U hU b y E hE := by
    intro a b
    -- Key identity: μ((a+b)+z) - μ((a+b)-z) = [μ(a+z) - μ(a-z)] + [μ(b+z) - μ(b-z)]
    have hD_add : ∀ z : H, μ ((a + b) + z) - μ ((a + b) - z) =
        (μ (a + z) - μ (a - z)) + (μ (b + z) - μ (b - z)) := by
      intro z
      have h := quadraticForm_additivity_identity U hU E hE z a b
      -- h: μ(z+a+b) - μ(z-a-b) = μ(z+a) + μ(z+b) - μ(z-a) - μ(z-b)
      -- Convert using commutativity and hμ_neg
      have heq1 : μ ((a + b) + z) = μ (z + a + b) := by congr 1; abel
      have heq2 : μ ((a + b) - z) = μ (z - a - b) := by
        have h1 : (a + b) - z = -(z - a - b) := by abel
        rw [h1, hμ_neg]
      have heq3 : μ (a + z) = μ (z + a) := by congr 1; abel
      have heq4 : μ (a - z) = μ (z - a) := by
        have h1 : a - z = -(z - a) := by abel
        rw [h1, hμ_neg]
      have heq5 : μ (b + z) = μ (z + b) := by congr 1; abel
      have heq6 : μ (b - z) = μ (z - b) := by
        have h1 : b - z = -(z - b) := by abel
        rw [h1, hμ_neg]
      rw [heq1, heq2, heq3, heq4, heq5, heq6]
      linarith
    have hreal' := hD_add y
    have himag' := hD_add (Complex.I • y)
    -- Expand polarized form and use hD_add
    show (1 / 4 : ℂ) * (μ ((a + b) + y) - μ ((a + b) - y) - Complex.I * μ ((a + b) + Complex.I • y) +
        Complex.I * μ ((a + b) - Complex.I • y)) =
        (1 / 4 : ℂ) * (μ (a + y) - μ (a - y) - Complex.I * μ (a + Complex.I • y) +
        Complex.I * μ (a - Complex.I • y)) +
        (1 / 4 : ℂ) * (μ (b + y) - μ (b - y) - Complex.I * μ (b + Complex.I • y) +
        Complex.I * μ (b - Complex.I • y))
    -- Use the difference identities
    have hr : (μ ((a + b) + y) - μ ((a + b) - y) : ℂ) =
        (μ (a + y) - μ (a - y) : ℂ) + (μ (b + y) - μ (b - y) : ℂ) := by
      simp only [← Complex.ofReal_sub, ← Complex.ofReal_add]
      exact congrArg _ hreal'
    have hi : (μ ((a + b) + Complex.I • y) - μ ((a + b) - Complex.I • y) : ℂ) =
        (μ (a + Complex.I • y) - μ (a - Complex.I • y) : ℂ) + (μ (b + Complex.I • y) - μ (b - Complex.I • y) : ℂ) := by
      simp only [← Complex.ofReal_sub, ← Complex.ofReal_add]
      exact congrArg _ himag'
    calc (1 / 4 : ℂ) * (μ ((a + b) + y) - μ ((a + b) - y) - Complex.I * μ ((a + b) + Complex.I • y) +
          Complex.I * μ ((a + b) - Complex.I • y))
        = (1 / 4 : ℂ) * ((μ ((a + b) + y) - μ ((a + b) - y) : ℂ) -
            Complex.I * (μ ((a + b) + Complex.I • y) - μ ((a + b) - Complex.I • y) : ℂ)) := by ring
      _ = (1 / 4 : ℂ) * (((μ (a + y) - μ (a - y) : ℂ) + (μ (b + y) - μ (b - y) : ℂ)) -
            Complex.I * ((μ (a + Complex.I • y) - μ (a - Complex.I • y) : ℂ) +
            (μ (b + Complex.I • y) - μ (b - Complex.I • y) : ℂ))) := by rw [hr, hi]
      _ = _ := by ring
  -- Step 2: Prove B(-x, y) = -B(x, y)
  have hB_neg_left : ∀ a : H, spectralMeasurePolarized U hU (-a) y E hE =
      -spectralMeasurePolarized U hU a y E hE := by
    intro a
    -- Use algebraic relations: -a + y = -(a - y), etc.
    have eq1 : -a + y = -(a - y) := by abel
    have eq2 : -a - y = -(a + y) := by abel
    have eq3 : -a + Complex.I • y = -(a - Complex.I • y) := by abel
    have eq4 : -a - Complex.I • y = -(a + Complex.I • y) := by abel
    -- Get measure equalities
    have h1 : μ (-a + y) = μ (a - y) := by rw [eq1, hμ_neg]
    have h2 : μ (-a - y) = μ (a + y) := by rw [eq2, hμ_neg]
    have h3 : μ (-a + Complex.I • y) = μ (a - Complex.I • y) := by rw [eq3, hμ_neg]
    have h4 : μ (-a - Complex.I • y) = μ (a + Complex.I • y) := by rw [eq4, hμ_neg]
    -- Now compute
    show (1 / 4 : ℂ) * (μ (-a + y) - μ (-a - y) - Complex.I * μ (-a + Complex.I • y) +
        Complex.I * μ (-a - Complex.I • y)) =
        -((1 / 4 : ℂ) * (μ (a + y) - μ (a - y) - Complex.I * μ (a + Complex.I • y) +
        Complex.I * μ (a - Complex.I • y)))
    rw [h1, h2, h3, h4]
    ring
  -- Step 3: Prove B(r•x, y) = r * B(x, y) for real r using quadratic expansion
  have hB_smul_real : ∀ (r : ℝ) (a : H), spectralMeasurePolarized U hU (r • a) y E hE =
      (r : ℂ) * spectralMeasurePolarized U hU a y E hE := by
    intro r a
    simp only [spectralMeasurePolarized]
    -- Use the quadratic expansion: μ_{w+tv}(E) = μ_w(E) + 2t*B_real + t²*μ_v(E)
    -- where B_real = (μ_{w+v} - μ_{w-v})/4
    -- Setting w = y, v = a, t = r: μ_{y+r•a} = μ_y + 2r*(μ_{y+a}-μ_{y-a})/4 + r²*μ_a
    -- Similarly for the other terms
    have hquad := fun z => spectralMeasureDiagonal_quadratic_expansion U hU z a E hE r
    -- μ_{z+r•a} = μ_z + 2r*(μ_{z+a}-μ_{z-a})/4 + r²*μ_a
    have h1 := hquad y
    have h2 := hquad (-y)
    have h3 := hquad (Complex.I • y)
    have h4 := hquad (-Complex.I • y)
    -- Rewrite using commutativity
    have eq1 : y + r • a = r • a + y := by abel
    have eq2 : -y + r • a = r • a + -y := by abel
    have eq3 : -y = r • a - y - r • a := by abel
    -- Actually let's use a cleaner approach
    -- The quadratic expansion gives: μ_{w+r•v} - μ_{w-r•v} = 2r*(μ_{w+v} - μ_{w-v})/2 = r*(μ_{w+v} - μ_{w-v})
    -- when μ_v = 0 or more generally...
    -- Actually from the quadratic expansion:
    -- μ_{w+r•v} = μ_w + r*(μ_{w+v}-μ_{w-v})/2 + r²*μ_v
    -- μ_{w-r•v} = μ_w + (-r)*(μ_{w+v}-μ_{w-v})/2 + r²*μ_v
    -- So: μ_{w+r•v} - μ_{w-r•v} = r*(μ_{w+v} - μ_{w-v})
    have hD_scale : ∀ z : H, μ (z + r • a) - μ (z - r • a) = r * (μ (z + a) - μ (z - a)) := by
      intro z
      have hq := spectralMeasureDiagonal_quadratic_expansion U hU z a E hE r
      have hqm := spectralMeasureDiagonal_quadratic_expansion U hU z a E hE (-r)
      simp only [neg_smul] at hqm
      -- hq: μ(z + r•a) = μ(z) + 2r*(μ(z+a)-μ(z-a))/4 + r²*μ(a)
      -- hqm: μ(z - r•a) = μ(z) + 2(-r)*(μ(z+a)-μ(z-a))/4 + r²*μ(a)
      have hsq : (-r)^2 = r^2 := by ring
      -- Convert spectralMeasureDiagonal to μ notation
      change μ (z + r • a) = μ z + 2 * r * (μ (z + a) - μ (z - a)) / 4 + r ^ 2 * μ a at hq
      change μ (z + -(r • a)) = μ z + 2 * (-r) * (μ (z + a) - μ (z - a)) / 4 + (-r) ^ 2 * μ a at hqm
      have hzneg : z + -(r • a) = z - r • a := by abel
      rw [hzneg, hsq] at hqm
      linarith
    have hr1 := hD_scale y
    have hr2 := hD_scale (Complex.I • y)
    set q1 := μ (r • a + y) with hq1
    set q2 := μ (r • a - y) with hq2
    set q3 := μ (r • a + Complex.I • y) with hq3
    set q4 := μ (r • a - Complex.I • y) with hq4
    set p1 := μ (a + y) with hp1
    set p2 := μ (a - y) with hp2
    set p3 := μ (a + Complex.I • y) with hp3
    set p4 := μ (a - Complex.I • y) with hp4
    have heq1 : y + r • a = r • a + y := by abel
    have heq2 : y - r • a = -(r • a - y) := by abel
    have heq3 : y + a = a + y := by abel
    have heq4 : y - a = -(a - y) := by abel
    rw [heq1, heq2, hμ_neg, heq3, heq4, hμ_neg] at hr1
    have heq5 : Complex.I • y + r • a = r • a + Complex.I • y := by abel
    have heq6 : Complex.I • y - r • a = -(r • a - Complex.I • y) := by abel
    have heq7 : Complex.I • y + a = a + Complex.I • y := by abel
    have heq8 : Complex.I • y - a = -(a - Complex.I • y) := by abel
    rw [heq5, heq6, hμ_neg, heq7, heq8, hμ_neg] at hr2
    -- hr1: q1 - q2 = r * (p1 - p2)
    -- hr2: q3 - q4 = r * (p3 - p4)
    -- Convert to Complex
    have hr1' : (q1 - q2 : ℂ) = (r : ℂ) * (p1 - p2 : ℂ) := by
      simp only [← Complex.ofReal_sub, ← Complex.ofReal_mul]
      exact congrArg _ hr1
    have hr2' : (q3 - q4 : ℂ) = (r : ℂ) * (p3 - p4 : ℂ) := by
      simp only [← Complex.ofReal_sub, ← Complex.ofReal_mul]
      exact congrArg _ hr2
    calc (1 / 4 : ℂ) * ((q1 : ℂ) - q2 - Complex.I * q3 + Complex.I * q4)
        = (1 / 4 : ℂ) * ((q1 - q2 : ℂ) - Complex.I * (q3 - q4 : ℂ)) := by ring
      _ = (1 / 4 : ℂ) * (((r : ℂ) * (p1 - p2 : ℂ)) - Complex.I * ((r : ℂ) * (p3 - p4 : ℂ))) := by
          rw [hr1', hr2']
      _ = (r : ℂ) * ((1 / 4 : ℂ) * ((p1 - p2 : ℂ) - Complex.I * (p3 - p4 : ℂ))) := by ring
      _ = (r : ℂ) * ((1 / 4 : ℂ) * ((p1 : ℂ) - p2 - Complex.I * p3 + Complex.I * p4)) := by ring
  -- Step 4: Prove B(I•x, y) = -I * B(x, y)
  have hB_I_left : ∀ a : H, spectralMeasurePolarized U hU (Complex.I • a) y E hE =
      -Complex.I * spectralMeasurePolarized U hU a y E hE := by
    intro a
    -- Use show to keep μ notation
    show (1 / 4 : ℂ) * (μ (Complex.I • a + y) - μ (Complex.I • a - y) -
        Complex.I * μ (Complex.I • a + Complex.I • y) + Complex.I * μ (Complex.I • a - Complex.I • y)) =
        -Complex.I * ((1 / 4 : ℂ) * (μ (a + y) - μ (a - y) -
        Complex.I * μ (a + Complex.I • y) + Complex.I * μ (a - Complex.I • y)))
    -- Key identities:
    -- D(I•a, I•y) = μ_{I•a+I•y} - μ_{I•a-I•y} = μ_{I•(a+y)} - μ_{I•(a-y)} = μ_{a+y} - μ_{a-y} = D(a, y)
    have hD_Ia_Iy : μ (Complex.I • a + Complex.I • y) - μ (Complex.I • a - Complex.I • y) =
        μ (a + y) - μ (a - y) := by
      have eq1 : Complex.I • a + Complex.I • y = Complex.I • (a + y) := by rw [smul_add]
      have eq2 : Complex.I • a - Complex.I • y = Complex.I • (a - y) := by rw [smul_sub]
      rw [eq1, eq2, hμ_I, hμ_I]
    -- Use parallelogram identity to get the key relation
    have hpara_Ia_y : μ (Complex.I • a + y) + μ (Complex.I • a - y) =
        2 * μ (Complex.I • a) + 2 * μ y :=
      spectralMeasureDiagonal_parallelogram U hU (Complex.I • a) y E hE
    have hpara_a_Iy : μ (a + Complex.I • y) + μ (a - Complex.I • y) =
        2 * μ a + 2 * μ (Complex.I • y) :=
      spectralMeasureDiagonal_parallelogram U hU a (Complex.I • y) E hE
    -- μ(I•a) = μ(a) and μ(I•y) = μ(y)
    rw [hμ_I] at hpara_Ia_y
    rw [hμ_I] at hpara_a_Iy
    -- So: μ(I•a+y) + μ(I•a-y) = μ(a+I•y) + μ(a-I•y)
    have hsum_eq : μ (Complex.I • a + y) + μ (Complex.I • a - y) =
        μ (a + Complex.I • y) + μ (a - Complex.I • y) := by linarith
    -- Now use the quadratic expansion to relate the differences
    -- From the quadratic form: μ_{w+v} - μ_{w-v} = 4*B(w,v) where B is the associated bilinear form
    -- The key is that B(I•a, y) = -B(a, I•y) for the real bilinear form
    -- This can be proven from the parallelogram identity structure
    -- Let's use a direct computation approach
    -- Define: D1 = μ(I•a+y) - μ(I•a-y), D2 = μ(a+I•y) - μ(a-I•y)
    -- We want to show D1 = -D2
    -- From hsum_eq: μ(I•a+y) + μ(I•a-y) = μ(a+I•y) + μ(a-I•y)
    -- So: (μ(I•a+y) - μ(I•a-y)) / 2 relates to (μ(a+I•y) - μ(a-I•y)) / 2
    -- Actually we need another equation. Use the parallelogram on (I•a, a, y, I•y)
    -- Consider: μ_{I•a+y} - μ_{a+I•y} and similar terms
    -- Alternative: use that μ_{x+y} = quadratic form, and expand both sides
    -- The cleanest approach: use the full parallelogram structure
    -- μ(I•a + y + (a + I•y)) + μ(I•a + y - (a + I•y)) = 2μ(I•a + y) + 2μ(a + I•y)
    -- Note: I•a + y + a + I•y = (1+I)•a + (1+I)•y = (1+I)•(a+y)
    --       I•a + y - a - I•y = (I-1)•a + (1-I)•y = (I-1)•a - (I-1)•y = (I-1)•(a-y)
    -- So: μ((1+I)•(a+y)) + μ((I-1)•(a-y)) = 2μ(I•a + y) + 2μ(a + I•y)
    -- Using μ(c•z) = |c|²•μ(z): |1+I|² = 2, |I-1|² = 2
    -- So: 2μ(a+y) + 2μ(a-y) = 2μ(I•a + y) + 2μ(a + I•y)
    -- Hence: μ(a+y) + μ(a-y) = μ(I•a + y) + μ(a + I•y)  ... (*)
    have hscale_1pI : ∀ z : H, μ ((1 + Complex.I) • z) = 2 * μ z := by
      intro z
      have h := spectralMeasureDiagonal_smul_sq U hU (1 + Complex.I) z E hE
      have hnorm : ‖(1 : ℂ) + Complex.I‖ = Real.sqrt 2 := by
        have h1 : (1 : ℂ) + Complex.I = (1 : ℝ) + (1 : ℝ) * Complex.I := by simp
        have h2 : Complex.normSq ((1 : ℂ) + Complex.I) = 2 := by
          rw [h1, Complex.normSq_add_mul_I]; norm_num
        have h3 : ‖(1 : ℂ) + Complex.I‖^2 = 2 := by rw [← Complex.normSq_eq_norm_sq, h2]
        rw [← Real.sqrt_sq (norm_nonneg _), h3]
      rw [hnorm, Real.sq_sqrt (by linarith : (0:ℝ) ≤ 2)] at h
      exact h
    have hscale_Im1 : ∀ z : H, μ ((Complex.I - 1) • z) = 2 * μ z := by
      intro z
      have h := spectralMeasureDiagonal_smul_sq U hU (Complex.I - 1) z E hE
      have hnorm : ‖Complex.I - (1 : ℂ)‖ = Real.sqrt 2 := by
        have h1 : Complex.I - (1 : ℂ) = (-1 : ℝ) + (1 : ℝ) * Complex.I := by simp; ring
        have h2 : Complex.normSq (Complex.I - (1 : ℂ)) = 2 := by
          rw [h1, Complex.normSq_add_mul_I]; norm_num
        have h3 : ‖Complex.I - (1 : ℂ)‖^2 = 2 := by rw [← Complex.normSq_eq_norm_sq, h2]
        rw [← Real.sqrt_sq (norm_nonneg _), h3]
      rw [hnorm, Real.sq_sqrt (by linarith : (0:ℝ) ≤ 2)] at h
      exact h
    have hkey1 : μ (Complex.I • a + y) + μ (a + Complex.I • y) = μ (a + y) + μ (a - y) := by
      have hpara := spectralMeasureDiagonal_parallelogram U hU (Complex.I • a + y) (a + Complex.I • y) E hE
      have heq1 : Complex.I • a + y + (a + Complex.I • y) = (1 + Complex.I) • (a + y) := by
        rw [add_smul, one_smul, smul_add]; abel
      have heq2 : Complex.I • a + y - (a + Complex.I • y) = (Complex.I - 1) • (a - y) := by
        rw [sub_smul, one_smul, smul_sub]; abel
      -- Convert hpara to μ notation
      change μ (Complex.I • a + y + (a + Complex.I • y)) + μ (Complex.I • a + y - (a + Complex.I • y)) =
          2 * μ (Complex.I • a + y) + 2 * μ (a + Complex.I • y) at hpara
      rw [heq1, heq2, hscale_1pI, hscale_Im1] at hpara
      linarith
    -- Similarly: μ(I•a - y) + μ(a - I•y) = μ(a+y) + μ(a-y)
    have hkey2 : μ (Complex.I • a - y) + μ (a - Complex.I • y) = μ (a + y) + μ (a - y) := by
      have hpara := spectralMeasureDiagonal_parallelogram U hU (Complex.I • a - y) (a - Complex.I • y) E hE
      have heq1 : Complex.I • a - y + (a - Complex.I • y) = (1 + Complex.I) • (a - y) := by
        rw [add_smul, one_smul, smul_sub]; abel
      have heq2 : Complex.I • a - y - (a - Complex.I • y) = (Complex.I - 1) • (a + y) := by
        rw [sub_smul, one_smul, smul_add]; abel
      -- Convert hpara to μ notation
      change μ (Complex.I • a - y + (a - Complex.I • y)) + μ (Complex.I • a - y - (a - Complex.I • y)) =
          2 * μ (Complex.I • a - y) + 2 * μ (a - Complex.I • y) at hpara
      rw [heq1, heq2, hscale_1pI, hscale_Im1] at hpara
      linarith
    -- From hkey1 and hkey2:
    -- μ(I•a+y) + μ(a+I•y) = μ(I•a-y) + μ(a-I•y)
    -- Combined with hsum_eq: μ(I•a+y) + μ(I•a-y) = μ(a+I•y) + μ(a-I•y)
    -- Subtracting: μ(I•a+y) - μ(I•a-y) = -(μ(a+I•y) - μ(a-I•y))
    have hD_rel : μ (Complex.I • a + y) - μ (Complex.I • a - y) =
        -(μ (a + Complex.I • y) - μ (a - Complex.I • y)) := by
      have h1 := hkey1
      have h2 := hkey2
      -- h1: μ(I•a+y) + μ(a+I•y) = μ(a+y) + μ(a-y)
      -- h2: μ(I•a-y) + μ(a-I•y) = μ(a+y) + μ(a-y)
      -- So: μ(I•a+y) + μ(a+I•y) = μ(I•a-y) + μ(a-I•y)
      -- Hence: μ(I•a+y) - μ(I•a-y) = μ(a-I•y) - μ(a+I•y) = -(μ(a+I•y) - μ(a-I•y))
      linarith
    -- Now compute B(I•a, y):
    -- B(I•a, y) = (1/4)[D(I•a, y) - I*D(I•a, I•y)]
    --           = (1/4)[D(I•a, y) - I*D(a, y)]  (using hD_Ia_Iy)
    -- And using hD_rel: D(I•a, y) = -D(a, I•y)
    -- B(I•a, y) = (1/4)[-D(a, I•y) - I*D(a, y)]
    -- Compare with: -I*B(a, y) = -I*(1/4)[D(a, y) - I*D(a, I•y)]
    --             = (1/4)[-I*D(a, y) + I²*D(a, I•y)]
    --             = (1/4)[-I*D(a, y) - D(a, I•y)]
    -- These are equal! ✓
    set D_Ia_y := μ (Complex.I • a + y) - μ (Complex.I • a - y) with hD_Ia_y_def
    set D_Ia_Iy := μ (Complex.I • a + Complex.I • y) - μ (Complex.I • a - Complex.I • y) with hD_Ia_Iy_def
    set D_a_y := μ (a + y) - μ (a - y) with hD_a_y_def
    set D_a_Iy := μ (a + Complex.I • y) - μ (a - Complex.I • y) with hD_a_Iy_def
    have h1 : D_Ia_Iy = D_a_y := hD_Ia_Iy
    have h2 : D_Ia_y = -D_a_Iy := hD_rel
    -- The goal is:
    -- (1/4)(μ(I•a+y) - μ(I•a-y) - I*μ(I•a+I•y) + I*μ(I•a-I•y))
    -- = -I * (1/4)(μ(a+y) - μ(a-y) - I*μ(a+I•y) + I*μ(a-I•y))
    -- Use: D_Ia_Iy = D_a_y and D_Ia_y = -D_a_Iy
    -- LHS = (1/4)(D_Ia_y - I*D_Ia_Iy) = (1/4)(-D_a_Iy - I*D_a_y)
    -- RHS = -I*(1/4)(D_a_y - I*D_a_Iy) = (1/4)(-I*D_a_y + I²*D_a_Iy) = (1/4)(-I*D_a_y - D_a_Iy)
    have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
    have h1' : (D_Ia_Iy : ℂ) = (D_a_y : ℂ) := congrArg _ h1
    have h2' : (D_Ia_y : ℂ) = -(D_a_Iy : ℂ) := by rw [h2, Complex.ofReal_neg]
    -- Show both sides equal the same thing: (1/4)*(-D_a_Iy - I*D_a_y)
    have lhs : (1 / 4 : ℂ) * ((μ (Complex.I • a + y) : ℂ) - μ (Complex.I • a - y) -
          Complex.I * μ (Complex.I • a + Complex.I • y) +
          Complex.I * μ (Complex.I • a - Complex.I • y)) =
        (1 / 4 : ℂ) * (-(D_a_Iy : ℂ) - Complex.I * (D_a_y : ℂ)) := by
      -- First simplify the I terms: -I*μ1 + I*μ2 = -I*(μ1 - μ2)
      have step1 : (μ (Complex.I • a + y) : ℂ) - μ (Complex.I • a - y) -
          Complex.I * μ (Complex.I • a + Complex.I • y) +
          Complex.I * μ (Complex.I • a - Complex.I • y) =
          ((μ (Complex.I • a + y) : ℂ) - μ (Complex.I • a - y)) -
          Complex.I * ((μ (Complex.I • a + Complex.I • y) : ℂ) - μ (Complex.I • a - Complex.I • y)) := by ring
      rw [step1]
      have eq1 : (μ (Complex.I • a + y) : ℂ) - μ (Complex.I • a - y) = (D_Ia_y : ℂ) :=
        (Complex.ofReal_sub _ _).symm
      have eq2 : (μ (Complex.I • a + Complex.I • y) : ℂ) - μ (Complex.I • a - Complex.I • y) = (D_Ia_Iy : ℂ) :=
        (Complex.ofReal_sub _ _).symm
      rw [eq1, eq2, h1', h2']
    have rhs : -Complex.I * ((1 / 4 : ℂ) * ((μ (a + y) : ℂ) - μ (a - y) -
          Complex.I * μ (a + Complex.I • y) + Complex.I * μ (a - Complex.I • y))) =
        (1 / 4 : ℂ) * (-(D_a_Iy : ℂ) - Complex.I * (D_a_y : ℂ)) := by
      have step1 : (μ (a + y) : ℂ) - μ (a - y) -
          Complex.I * μ (a + Complex.I • y) + Complex.I * μ (a - Complex.I • y) =
          ((μ (a + y) : ℂ) - μ (a - y)) - Complex.I * ((μ (a + Complex.I • y) : ℂ) - μ (a - Complex.I • y)) := by ring
      rw [step1]
      have eq1 : (μ (a + y) : ℂ) - μ (a - y) = (D_a_y : ℂ) :=
        (Complex.ofReal_sub _ _).symm
      have eq2 : (μ (a + Complex.I • y) : ℂ) - μ (a - Complex.I • y) = (D_a_Iy : ℂ) :=
        (Complex.ofReal_sub _ _).symm
      rw [eq1, eq2]
      -- Goal: -I * (1/4 * (D_a_y - I*D_a_Iy)) = 1/4 * (-D_a_Iy - I*D_a_y)
      -- Use I² = -1: -I*(D_a_y - I*D_a_Iy) = -I*D_a_y + I²*D_a_Iy = -I*D_a_y - D_a_Iy
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [lhs, ← rhs]
  -- Step 5: Combine for general c = re + im*I
  set re := c.re with hre_def
  set im := c.im with him_def
  have hc_decomp : c = (re : ℂ) + (im : ℂ) * Complex.I := c.re_add_im.symm
  have hcx_decomp : c • x₁ = re • x₁ + im • (Complex.I • x₁) := by
    rw [hc_decomp]
    simp only [add_smul, mul_smul]
    congr 1
  rw [hcx_decomp]
  rw [hB_add_left (re • x₁ + im • (Complex.I • x₁)) x₂]
  rw [hB_add_left (re • x₁) (im • (Complex.I • x₁))]
  rw [hB_smul_real re x₁]
  rw [hB_smul_real im (Complex.I • x₁)]
  rw [hB_I_left x₁]
  simp only [starRingEnd_apply]
  have hconj : star c = (re : ℂ) - (im : ℂ) * Complex.I := by
    rw [hc_decomp, star_add, star_mul]
    simp only [RCLike.star_def, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hconj]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The polarized spectral measure is bounded: |μ_{x,y}(E)| ≤ C‖x‖‖y‖.
    The bound follows from sesquilinearity and the polarization bound on unit vectors.

    Mathematical argument:
    1. Direct polarization gives |B(x,y)| ≤ ‖x‖² + ‖y‖²
    2. Using sesquilinearity: B(x,y) = ‖x‖·‖y‖·B(x/‖x‖, y/‖y‖) for nonzero x,y
    3. For unit vectors u,v: |B(u,v)| ≤ ‖u‖² + ‖v‖² = 2
    4. Therefore: |B(x,y)| ≤ 2·‖x‖·‖y‖ -/
theorem spectralMeasurePolarized_bounded (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (E : Set Circle) (hE : MeasurableSet E) :
    ∃ C : ℝ, ∀ x y : H, ‖spectralMeasurePolarized U hU x y E hE‖ ≤ C * ‖x‖ * ‖y‖ := by
  use 2
  intro x y
  -- Use linearity in y to handle y = 0 case
  by_cases hy : y = 0
  · -- B(x, 0) = 0 by linearity in y
    have hlin_zero := (spectralMeasurePolarized_linear_right U hU E hE x).map_zero
    simp only [hy, hlin_zero, norm_zero, mul_zero, le_refl]
  · by_cases hx : x = 0
    · -- For x = 0: use conjugate-linearity
      -- B(c·x₁ + x₂, y) = c̄·B(x₁,y) + B(x₂,y)
      -- Set c = 1, x₁ = 0, x₂ = 0: B(0, y) = 1·B(0,y) + B(0,y)
      have hconj := spectralMeasurePolarized_conj_linear_left U hU E hE y 1 0 0
      simp only [one_smul, add_zero, map_one, one_mul] at hconj
      -- hconj : B(0, y) = B(0, y) + B(0, y), which means B(0,y) = 0
      have hzero : spectralMeasurePolarized U hU 0 y E hE = 0 := by
        -- From a = a + a, we get a - a = a + a - a = a, so 0 = a
        have h : (0 : ℂ) = spectralMeasurePolarized U hU 0 y E hE := by
          calc (0 : ℂ) = spectralMeasurePolarized U hU 0 y E hE - spectralMeasurePolarized U hU 0 y E hE := (sub_self _).symm
            _ = (spectralMeasurePolarized U hU 0 y E hE + spectralMeasurePolarized U hU 0 y E hE) -
                spectralMeasurePolarized U hU 0 y E hE := by rw [← hconj]
            _ = spectralMeasurePolarized U hU 0 y E hE := by ring
        exact h.symm
      simp only [hx, hzero, norm_zero, zero_mul, mul_zero, le_refl]
    · -- Main case: x ≠ 0, y ≠ 0
      -- Use sesquilinearity to factor out norms:
      -- B(x, y) = B(‖x‖·(x/‖x‖), y) = ‖x‖·B(x/‖x‖, y) (by conj-linearity, ‖x‖ is real so conj = id)
      -- B(x/‖x‖, y) = B(x/‖x‖, ‖y‖·(y/‖y‖)) = ‖y‖·B(x/‖x‖, y/‖y‖) (by linearity in y)
      have hx_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hy_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy
      -- Express x = ‖x‖ • (x/‖x‖) and y = ‖y‖ • (y/‖y‖)
      have hx_eq : x = ‖x‖ • (‖x‖⁻¹ • x) := by simp [smul_smul, mul_inv_cancel₀ hx_pos.ne']
      have hy_eq : y = ‖y‖ • (‖y‖⁻¹ • y) := by simp [smul_smul, mul_inv_cancel₀ hy_pos.ne']
      -- Unit vectors
      set u := ‖x‖⁻¹ • x with hu_def
      set v := ‖y‖⁻¹ • y with hv_def
      have hu_norm : ‖u‖ = 1 := by simp [u, norm_smul, inv_mul_cancel₀ hx_pos.ne']
      have hv_norm : ‖v‖ = 1 := by simp [v, norm_smul, inv_mul_cancel₀ hy_pos.ne']
      -- Use linearity: B(x, y) = B(x, ‖y‖•v) = ‖y‖ • B(x, v)
      have hlin_y : spectralMeasurePolarized U hU x y E hE =
          ‖y‖ • spectralMeasurePolarized U hU x v E hE := by
        conv_lhs => rw [hy_eq]
        exact (spectralMeasurePolarized_linear_right U hU E hE x).map_smul (↑‖y‖) v
      -- Use conjugate-linearity: B(x, v) = B(‖x‖•u, v) = ‖x‖ • B(u, v) (since ‖x‖ is real)
      have hconj_x : spectralMeasurePolarized U hU x v E hE =
          ‖x‖ • spectralMeasurePolarized U hU u v E hE := by
        conv_lhs => rw [hx_eq]
        have hconj := spectralMeasurePolarized_conj_linear_left U hU E hE v (↑‖x‖) u 0
        simp only [add_zero, starRingEnd_apply] at hconj
        -- star of a real is itself
        have hstar_real : star (↑‖x‖ : ℂ) = ↑‖x‖ := by
          rw [RCLike.star_def, Complex.conj_ofReal]
        -- B(0, v) = 0
        have hB0 : spectralMeasurePolarized U hU 0 v E hE = 0 := by
          have hc := spectralMeasurePolarized_conj_linear_left U hU E hE v 1 0 0
          simp only [one_smul, add_zero, map_one, one_mul] at hc
          have h : (0 : ℂ) = spectralMeasurePolarized U hU 0 v E hE := by
            calc (0 : ℂ) = spectralMeasurePolarized U hU 0 v E hE - spectralMeasurePolarized U hU 0 v E hE := (sub_self _).symm
              _ = (spectralMeasurePolarized U hU 0 v E hE + spectralMeasurePolarized U hU 0 v E hE) -
                  spectralMeasurePolarized U hU 0 v E hE := by rw [← hc]
              _ = spectralMeasurePolarized U hU 0 v E hE := by ring
          exact h.symm
        rw [hstar_real, hB0, add_zero] at hconj
        -- Convert real scalar mult to complex: ‖x‖ • u = (↑‖x‖ : ℂ) • u
        have hsmul_eq : (‖x‖ : ℝ) • u = (↑‖x‖ : ℂ) • u := by
          rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]; rfl
        rw [hsmul_eq, hconj]
        -- ↑‖x‖ * B = ‖x‖ • B
        rw [← Complex.real_smul]
      -- Combine: B(x,y) = ‖y‖ • ‖x‖ • B(u,v)
      rw [hlin_y, hconj_x]
      simp only [smul_smul]
      -- Bound: ‖(‖y‖ * ‖x‖) • B(u,v)‖ = |‖y‖ * ‖x‖| * ‖B(u,v)‖ = ‖y‖ * ‖x‖ * ‖B(u,v)‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hy_pos hx_pos)]
      -- Need: ‖x‖ * ‖y‖ * ‖B(u,v)‖ ≤ 2 * ‖x‖ * ‖y‖
      -- Equivalent to: ‖B(u,v)‖ ≤ 2
      have hunit_bound : ‖spectralMeasurePolarized U hU u v E hE‖ ≤ 2 := by
        -- For unit vectors, use the direct polarization bound: |B(u,v)| ≤ ‖u‖² + ‖v‖² = 2
        -- This follows from triangle inequality on the polarization formula
        unfold spectralMeasurePolarized
        -- Each μ_z ≤ ‖z‖² and for z = u±v or u±iv, ‖z‖ ≤ ‖u‖ + ‖v‖ = 2
        have hbound : ∀ z : H, (spectralMeasureDiagonal U hU z E).toReal ≤ ‖z‖^2 := by
          intro z
          haveI : MeasureTheory.IsFiniteMeasure (spectralMeasureDiagonal U hU z) :=
            spectralMeasureDiagonal_isFiniteMeasure U hU z
          have hmono := MeasureTheory.measure_mono (μ := spectralMeasureDiagonal U hU z) (Set.subset_univ E)
          have huniv := spectralMeasureDiagonal_univ U hU z
          exact le_trans (ENNReal.toReal_mono (MeasureTheory.measure_ne_top _ _) hmono) (le_of_eq huniv)
        -- Use parallelogram identity
        have hpara : ‖u + v‖^2 + ‖u - v‖^2 = 2 * ‖u‖^2 + 2 * ‖v‖^2 := by
          have h := @parallelogram_law_with_norm ℂ H _ _ _ u v
          simp only [sq] at h ⊢; linarith
        have hpara2 : ‖u + Complex.I • v‖^2 + ‖u - Complex.I • v‖^2 = 2 * ‖u‖^2 + 2 * ‖v‖^2 := by
          have h := @parallelogram_law_with_norm ℂ H _ _ _ u (Complex.I • v)
          have hiv_norm : ‖Complex.I • v‖ = ‖v‖ := by rw [norm_smul, Complex.norm_I, one_mul]
          simp only [sq, hiv_norm] at h ⊢; linarith
        rw [hu_norm, hv_norm] at hpara hpara2
        -- hpara, hpara2 now say ... = 2*1 + 2*1 = 4
        have hpara' : ‖u + v‖^2 + ‖u - v‖^2 = 4 := by simp only [one_pow, mul_one] at hpara; linarith
        have hpara2' : ‖u + Complex.I • v‖^2 + ‖u - Complex.I • v‖^2 = 4 := by simp only [one_pow, mul_one] at hpara2; linarith
        -- Sum of measures ≤ 8
        have hsum : (spectralMeasureDiagonal U hU (u + v) E).toReal +
                    (spectralMeasureDiagonal U hU (u - v) E).toReal +
                    (spectralMeasureDiagonal U hU (u + Complex.I • v) E).toReal +
                    (spectralMeasureDiagonal U hU (u - Complex.I • v) E).toReal ≤ 8 := by
          calc _ ≤ ‖u + v‖^2 + ‖u - v‖^2 + ‖u + Complex.I • v‖^2 + ‖u - Complex.I • v‖^2 := by
                   linarith [hbound (u + v), hbound (u - v),
                            hbound (u + Complex.I • v), hbound (u - Complex.I • v)]
               _ = (‖u + v‖^2 + ‖u - v‖^2) + (‖u + Complex.I • v‖^2 + ‖u - Complex.I • v‖^2) := by ring
               _ = 4 + 4 := by rw [hpara', hpara2']
               _ = 8 := by ring
        -- Non-negativity of measures
        have hnn : ∀ z : H, 0 ≤ (spectralMeasureDiagonal U hU z E).toReal := fun z => ENNReal.toReal_nonneg
        set μ₁ := (spectralMeasureDiagonal U hU (u + v) E).toReal with hμ₁_def
        set μ₂ := (spectralMeasureDiagonal U hU (u - v) E).toReal with hμ₂_def
        set μ₃ := (spectralMeasureDiagonal U hU (u + Complex.I • v) E).toReal with hμ₃_def
        set μ₄ := (spectralMeasureDiagonal U hU (u - Complex.I • v) E).toReal with hμ₄_def
        have hμ₁_nn : 0 ≤ μ₁ := hnn _
        have hμ₂_nn : 0 ≤ μ₂ := hnn _
        have hμ₃_nn : 0 ≤ μ₃ := hnn _
        have hμ₄_nn : 0 ≤ μ₄ := hnn _
        -- Bound: ‖(1/4)(μ₁ - μ₂ - iμ₃ + iμ₄)‖ ≤ (1/4)(|μ₁| + |μ₂| + |μ₃| + |μ₄|) = (1/4)(μ₁ + μ₂ + μ₃ + μ₄) ≤ (1/4)*8 = 2
        calc ‖(1 / 4 : ℂ) * ((μ₁ : ℂ) - μ₂ - Complex.I * μ₃ + Complex.I * μ₄)‖
            = (1 / 4) * ‖(μ₁ : ℂ) - μ₂ - Complex.I * μ₃ + Complex.I * μ₄‖ := by
              rw [norm_mul]
              congr 1
              -- ‖(1/4 : ℂ)‖ = 1/4 since 1/4 is a positive real
              have h14 : (1 / 4 : ℂ) = (↑(1/4 : ℝ) : ℂ) := by simp only [one_div, Complex.ofReal_inv, Complex.ofReal_ofNat]
              rw [h14, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1/4)]
          _ ≤ (1 / 4) * (‖(μ₁ : ℂ)‖ + ‖(μ₂ : ℂ)‖ + ‖Complex.I * (μ₃ : ℂ)‖ + ‖Complex.I * (μ₄ : ℂ)‖) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 1/4)
              calc ‖(μ₁ : ℂ) - μ₂ - Complex.I * μ₃ + Complex.I * μ₄‖
                  ≤ ‖(μ₁ : ℂ) - μ₂ - Complex.I * μ₃‖ + ‖Complex.I * (μ₄ : ℂ)‖ := norm_add_le _ _
                _ ≤ ‖(μ₁ : ℂ) - μ₂‖ + ‖Complex.I * (μ₃ : ℂ)‖ + ‖Complex.I * (μ₄ : ℂ)‖ := by
                    linarith [norm_sub_le ((μ₁ : ℂ) - μ₂) (Complex.I * μ₃)]
                _ ≤ ‖(μ₁ : ℂ)‖ + ‖(μ₂ : ℂ)‖ + ‖Complex.I * (μ₃ : ℂ)‖ + ‖Complex.I * (μ₄ : ℂ)‖ := by
                    linarith [norm_sub_le (μ₁ : ℂ) μ₂]
          _ = (1 / 4) * (μ₁ + μ₂ + μ₃ + μ₄) := by
              have hn1 : ‖(μ₁ : ℂ)‖ = μ₁ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hμ₁_nn]
              have hn2 : ‖(μ₂ : ℂ)‖ = μ₂ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hμ₂_nn]
              have hn3 : ‖Complex.I * (μ₃ : ℂ)‖ = μ₃ := by
                rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hμ₃_nn]
              have hn4 : ‖Complex.I * (μ₄ : ℂ)‖ = μ₄ := by
                rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hμ₄_nn]
              rw [hn1, hn2, hn3, hn4]
          _ ≤ (1 / 4) * 8 := by
              apply mul_le_mul_of_nonneg_left hsum (by norm_num : (0:ℝ) ≤ 1/4)
          _ = 2 := by norm_num
      calc ‖y‖ * ‖x‖ * ‖spectralMeasurePolarized U hU u v E hE‖
          ≤ ‖y‖ * ‖x‖ * 2 := by
            apply mul_le_mul_of_nonneg_left hunit_bound
            exact mul_nonneg hy_pos.le hx_pos.le
        _ = 2 * ‖x‖ * ‖y‖ := by ring

/-- The polarized spectral measure has Hermitian symmetry: B(x, y) = conj(B(y, x)).

    This is the key property that makes P(E) = sesquilinearToOperator(B) self-adjoint.

    Proof uses the relation D(I·a, y) = -D(a, I·y) where D(a,b) = μ(a+b) - μ(a-b). -/
theorem spectralMeasurePolarized_conj_symm (U : H →L[ℂ] H) (hU : U ∈ unitary (H →L[ℂ] H))
    (E : Set Circle) (hE : MeasurableSet E) (x y : H) :
    spectralMeasurePolarized U hU x y E hE = star (spectralMeasurePolarized U hU y x E hE) := by
  -- Define μ for convenience
  let μ := fun z => (spectralMeasureDiagonal U hU z E).toReal
  -- Key properties of μ
  have hμ_neg : ∀ w, μ (-w) = μ w := fun w => by
    have h := spectralMeasureDiagonal_smul_sq U hU (-1) w E hE
    simp only [norm_neg, norm_one, one_pow, one_mul, neg_one_smul] at h
    exact h
  have hμ_I : ∀ w, μ (Complex.I • w) = μ w := fun w => by
    have h := spectralMeasureDiagonal_smul_sq U hU Complex.I w E hE
    simp only [Complex.norm_I, one_pow, one_mul] at h
    exact h
  -- Define D(a, b) = μ(a+b) - μ(a-b)
  let D := fun a b => μ (a + b) - μ (a - b)
  -- Key relation: D(I·a, y) = -D(a, I·y)
  -- From conjugate-linearity proof, we established this
  have hD_rel : ∀ a : H, D (Complex.I • a) y = -D a (Complex.I • y) := by
    intro a
    -- Use parallelogram identities as in conjugate-linearity proof
    have hpara_Ia_y := spectralMeasureDiagonal_parallelogram U hU (Complex.I • a) y E hE
    have hpara_a_Iy := spectralMeasureDiagonal_parallelogram U hU a (Complex.I • y) E hE
    change μ (Complex.I • a + y) + μ (Complex.I • a - y) = 2 * μ (Complex.I • a) + 2 * μ y at hpara_Ia_y
    change μ (a + Complex.I • y) + μ (a - Complex.I • y) = 2 * μ a + 2 * μ (Complex.I • y) at hpara_a_Iy
    -- μ(I•a) = μ(a), μ(I•y) = μ(y)
    rw [hμ_I a] at hpara_Ia_y
    rw [hμ_I y] at hpara_a_Iy
    -- So both sums equal 2μ(a) + 2μ(y)
    have hsum_eq : μ (Complex.I • a + y) + μ (Complex.I • a - y) = μ (a + Complex.I • y) + μ (a - Complex.I • y) := by
      rw [hpara_Ia_y, hpara_a_Iy]
    -- Scale relations
    have hscale_1pI : ∀ z, μ ((1 + Complex.I) • z) = 2 * μ z := by
      intro z
      have h := spectralMeasureDiagonal_smul_sq U hU (1 + Complex.I) z E hE
      have hnorm : ‖(1 : ℂ) + Complex.I‖ = Real.sqrt 2 := by
        have h1 : (1 : ℂ) + Complex.I = (1 : ℝ) + (1 : ℝ) * Complex.I := by simp
        have h2 : Complex.normSq ((1 : ℂ) + Complex.I) = 2 := by
          rw [h1, Complex.normSq_add_mul_I]; norm_num
        have h3 : ‖(1 : ℂ) + Complex.I‖^2 = 2 := by rw [← Complex.normSq_eq_norm_sq, h2]
        rw [← Real.sqrt_sq (norm_nonneg _), h3]
      rw [hnorm, Real.sq_sqrt (by linarith : (0:ℝ) ≤ 2)] at h
      exact h
    have hscale_Im1 : ∀ z, μ ((Complex.I - 1) • z) = 2 * μ z := by
      intro z
      have h := spectralMeasureDiagonal_smul_sq U hU (Complex.I - 1) z E hE
      have hnorm : ‖Complex.I - (1 : ℂ)‖ = Real.sqrt 2 := by
        have h1 : Complex.I - (1 : ℂ) = (-1 : ℝ) + (1 : ℝ) * Complex.I := by simp; ring
        have h2 : Complex.normSq (Complex.I - (1 : ℂ)) = 2 := by
          rw [h1, Complex.normSq_add_mul_I]; norm_num
        have h3 : ‖Complex.I - (1 : ℂ)‖^2 = 2 := by rw [← Complex.normSq_eq_norm_sq, h2]
        rw [← Real.sqrt_sq (norm_nonneg _), h3]
      rw [hnorm, Real.sq_sqrt (by linarith : (0:ℝ) ≤ 2)] at h
      exact h
    -- Key lemmas from parallelogram
    have hkey1 : μ (Complex.I • a + y) + μ (a + Complex.I • y) = μ (a + y) + μ (a - y) := by
      have hpara := spectralMeasureDiagonal_parallelogram U hU (Complex.I • a + y) (a + Complex.I • y) E hE
      have heq1 : Complex.I • a + y + (a + Complex.I • y) = (1 + Complex.I) • (a + y) := by
        rw [add_smul, one_smul, smul_add]; abel
      have heq2 : Complex.I • a + y - (a + Complex.I • y) = (Complex.I - 1) • (a - y) := by
        rw [sub_smul, one_smul, smul_sub]; abel
      change μ (Complex.I • a + y + (a + Complex.I • y)) + μ (Complex.I • a + y - (a + Complex.I • y)) =
          2 * μ (Complex.I • a + y) + 2 * μ (a + Complex.I • y) at hpara
      rw [heq1, heq2, hscale_1pI, hscale_Im1] at hpara
      linarith
    have hkey2 : μ (Complex.I • a - y) + μ (a - Complex.I • y) = μ (a + y) + μ (a - y) := by
      have hpara := spectralMeasureDiagonal_parallelogram U hU (Complex.I • a - y) (a - Complex.I • y) E hE
      have heq1 : Complex.I • a - y + (a - Complex.I • y) = (1 + Complex.I) • (a - y) := by
        rw [add_smul, one_smul, smul_sub]; abel
      have heq2 : Complex.I • a - y - (a - Complex.I • y) = (Complex.I - 1) • (a + y) := by
        rw [sub_smul, one_smul, smul_add]; abel
      change μ (Complex.I • a - y + (a - Complex.I • y)) + μ (Complex.I • a - y - (a - Complex.I • y)) =
          2 * μ (Complex.I • a - y) + 2 * μ (a - Complex.I • y) at hpara
      rw [heq1, heq2, hscale_1pI, hscale_Im1] at hpara
      linarith
    -- From hkey1 and hkey2: D(I•a, y) = -D(a, I•y)
    have h1 := hkey1
    have h2 := hkey2
    -- h1: μ(I•a+y) + μ(a+I•y) = μ(a+y) + μ(a-y)
    -- h2: μ(I•a-y) + μ(a-I•y) = μ(a+y) + μ(a-y)
    -- Subtracting: (μ(I•a+y) - μ(I•a-y)) = -(μ(a+I•y) - μ(a-I•y))
    simp only [D]
    linarith
  -- Now prove the main theorem using direct equality
  -- B(x, y) = (1/4)[μ(x+y) - μ(x-y) - I*μ(x+I·y) + I*μ(x-I·y)]
  -- star(B(y, x)) = (1/4)[μ(y+x) - μ(y-x) + I*μ(y+I·x) - I*μ(y-I·x)] (conjugating flips I to -I)
  -- We show these are equal using hD_rel and commutativity/neg-symmetry of μ
  simp only [spectralMeasurePolarized]
  -- Use the key D relation
  have hD := hD_rel x
  simp only [D] at hD
  -- Key equalities: y + x = x + y, y - x = -(x - y), etc.
  have hyx : y + x = x + y := add_comm y x
  have hymx : y - x = -(x - y) := (neg_sub x y).symm
  have hyIx : y + Complex.I • x = Complex.I • x + y := add_comm _ _
  have hymIx : y - Complex.I • x = -(Complex.I • x - y) := (neg_sub (Complex.I • x) y).symm
  -- Equalities for spectralMeasureDiagonal
  have hμyx : (spectralMeasureDiagonal U hU (y + x) E).toReal = μ (x + y) := by
    simp only [μ, hyx]
  have hμymx : (spectralMeasureDiagonal U hU (y - x) E).toReal = μ (x - y) := by
    simp only [μ, hymx, hμ_neg]
  have hμyIx : (spectralMeasureDiagonal U hU (y + Complex.I • x) E).toReal = μ (Complex.I • x + y) := by
    simp only [μ, hyIx]
  have hμymIx : (spectralMeasureDiagonal U hU (y - Complex.I • x) E).toReal = μ (Complex.I • x - y) := by
    simp only [μ, hymIx, hμ_neg]
  -- Key relation: μ(I·x+y) - μ(I·x-y) = μ(x-I·y) - μ(x+I·y)
  have hkey : μ (Complex.I • x + y) - μ (Complex.I • x - y) =
      μ (x - Complex.I • y) - μ (x + Complex.I • y) := by
    simp only [μ] at hD
    linarith
  -- Work with explicit form (already unfolded above)
  -- star(1/4 * expr) = star(1/4) * star(expr) = (1/4) * star(expr)
  rw [star_mul']
  -- star(1/4) = 1/4 since 1/4 is real
  have hstar_coeff : star (1 / 4 : ℂ) = 1 / 4 := by
    have h1 : (1 : ℂ) / 4 = (1/4 : ℝ) := by norm_num
    rw [h1, RCLike.star_def, Complex.conj_ofReal]
  rw [hstar_coeff]
  -- Suffices to show LHS_expr = star(RHS_expr)
  congr 1
  -- Compute star of the RHS expression using conv to work inside star
  -- RHS = μ(y+x) - μ(y-x) - I*μ(y+I·x) + I*μ(y-I·x)
  -- star(RHS) = μ(y+x) - μ(y-x) + I*μ(y+I·x) - I*μ(y-I·x)  (since μ values are real, star(I)=-I)
  conv_rhs => rw [star_add, star_sub, star_sub, star_mul, star_mul]
  simp only [Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
  -- Now convert using the equalities
  rw [hμyx, hμymx, hμyIx, hμymIx]
  -- LHS = μ(x+y) - μ(x-y) - I*μ(x+I·y) + I*μ(x-I·y)
  -- RHS (after star) = μ(x+y) - μ(x-y) + I*μ(I·x+y) - I*μ(I·x-y)
  -- Need: -I*μ(x+I·y) + I*μ(x-I·y) = I*μ(I·x+y) - I*μ(I·x-y)
  simp only [μ]
  -- Apply hkey: μ(x-I·y) - μ(x+I·y) = μ(I·x+y) - μ(I·x-y)
  -- Need: LHS - RHS = 0, i.e.,
  -- -I*μ(x+I·y) + I*μ(x-I·y) - I*μ(I·x+y) + I*μ(I·x-y) = 0
  -- = I * (μ(x-I·y) - μ(x+I·y) - μ(I·x+y) + μ(I·x-y)) = I * 0 = 0
  have hkey' : (↑(spectralMeasureDiagonal U hU (x - Complex.I • y) E).toReal : ℂ) -
      ↑(spectralMeasureDiagonal U hU (x + Complex.I • y) E).toReal =
      (↑(spectralMeasureDiagonal U hU (Complex.I • x + y) E).toReal : ℂ) -
      ↑(spectralMeasureDiagonal U hU (Complex.I • x - y) E).toReal := by
    -- hkey: μ (I • x + y) - μ (I • x - y) = μ (x - I • y) - μ (x + I • y)
    simp only [μ] at hkey
    -- Convert to ℂ
    have h : (↑((spectralMeasureDiagonal U hU (Complex.I • x + y) E).toReal -
        (spectralMeasureDiagonal U hU (Complex.I • x - y) E).toReal) : ℂ) =
        ↑((spectralMeasureDiagonal U hU (x - Complex.I • y) E).toReal -
        (spectralMeasureDiagonal U hU (x + Complex.I • y) E).toReal) := by exact congrArg _ hkey
    push_cast at h
    -- h says: (μ(I•x+y) - μ(I•x-y)) = (μ(x-I•y) - μ(x+I•y))
    -- We need: (μ(x-I•y) - μ(x+I•y)) = (μ(I•x+y) - μ(I•x-y))
    exact h.symm
  -- Use hkey' to conclude
  calc ↑(spectralMeasureDiagonal U hU (x + y) E).toReal -
      ↑(spectralMeasureDiagonal U hU (x - y) E).toReal -
      Complex.I * ↑(spectralMeasureDiagonal U hU (x + Complex.I • y) E).toReal +
      Complex.I * ↑(spectralMeasureDiagonal U hU (x - Complex.I • y) E).toReal
      = ↑(spectralMeasureDiagonal U hU (x + y) E).toReal -
        ↑(spectralMeasureDiagonal U hU (x - y) E).toReal +
        Complex.I * (↑(spectralMeasureDiagonal U hU (x - Complex.I • y) E).toReal -
          ↑(spectralMeasureDiagonal U hU (x + Complex.I • y) E).toReal) := by ring
    _ = ↑(spectralMeasureDiagonal U hU (x + y) E).toReal -
        ↑(spectralMeasureDiagonal U hU (x - y) E).toReal +
        Complex.I * (↑(spectralMeasureDiagonal U hU (Complex.I • x + y) E).toReal -
          ↑(spectralMeasureDiagonal U hU (Complex.I • x - y) E).toReal) := by rw [hkey']
    _ = _ := by ring


end
