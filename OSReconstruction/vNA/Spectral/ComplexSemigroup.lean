/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.vNA.Spectral.SelfAdjointFunctionalViaRMK

/-!
# Complex Semigroup Extension via Riesz Representation

Given a bounded nonneg self-adjoint operator `A : H →L[ℂ] H` with spectrum in `[0,1]`,
the scalar spectral Laplace `selfAdjointSpectralLaplaceOffdiag A hA x y z` defines a
bounded sesquilinear form for each `z` with `Re(z) > 0`. By the Riesz representation
theorem, this sesquilinear form corresponds to a unique bounded operator `T(z) : H →L[ℂ] H`.

## Main definitions

* `ContinuousLinearMap.spectralSemigroupComplex` : the operator-valued complex semigroup

## Main results

* `spectralSemigroupComplex_inner_eq` : the defining property
* `spectralSemigroupComplex_differentiableOn` : matrix element holomorphicity
* `spectralSemigroupComplex_ofReal_eq_nnrpow` : agrees with CFC.nnrpow at real points
* `spectralSemigroupComplex_strongContinuousOn` : strong operator continuity

## Construction

The operator T(z) is constructed via the Riesz representation theorem:

1. For fixed z with Re(z) > 0 and fixed y, the map
   `x ↦ conj(selfAdjointSpectralLaplaceOffdiag A hA x y z)`
   is a bounded ℂ-linear functional on H (the spectral Laplace is conjugate-linear in x,
   so its conjugate is linear).

2. By the Riesz representation theorem (`InnerProductSpace.toDual`), there exists a unique
   vector `T(z)(y) ∈ H` such that `⟨x, T(z)(y)⟩ = B_z(x,y)` for all x.

3. The map `y ↦ T(z)(y)` is linear and bounded (by the bound on B_z), giving the CLM.
-/

open MeasureTheory Complex Set Filter InnerProductSpace
open scoped Topology

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The operator T(z) via real CFC decomposition

For a self-adjoint operator A with spectrum in [0,1] and z ∈ ℂ with Re(z) > 0,
the "complex power" λ^z = exp(z · log λ) is a well-defined continuous function on (0,1].
We decompose it into real and imaginary parts:
  Re(λ^z) = exp(Re(z) · log λ) · cos(Im(z) · log λ)
  Im(λ^z) = exp(Re(z) · log λ) · sin(Im(z) · log λ)
and define T(z) = cfc(Re part, A) + I · cfc(Im part, A).

When Re(z) > 0, both parts extend continuously to λ = 0 with value 0,
so cfc applies (the function is continuous on the spectrum). -/

/-- Real part of complex power: Re(λ^z) = exp(Re(z) · log λ) · cos(Im(z) · log λ)
for λ > 0, extended to 0 at λ ≤ 0. -/
private def specSemiFRe (z : ℂ) (u : ℝ) : ℝ :=
  if u ≤ 0 then 0 else Real.exp (z.re * Real.log u) * Real.cos (z.im * Real.log u)

/-- Imaginary part of complex power: Im(λ^z) = exp(Re(z) · log λ) · sin(Im(z) · log λ)
for λ > 0, extended to 0 at λ ≤ 0. -/
private def specSemiFIm (z : ℂ) (u : ℝ) : ℝ :=
  if u ≤ 0 then 0 else Real.exp (z.re * Real.log u) * Real.sin (z.im * Real.log u)

/-- The complex semigroup extension: for each `z`, the operator `T(z) : H →L[ℂ] H`
satisfying `⟨x, T(z)(y)⟩ = selfAdjointSpectralLaplaceOffdiag A hA x y z`.

Construction: Decompose the complex power λ^z into real and imaginary parts, apply
the real CFC to each part, and combine:
  T(z) = cfc(Re(λ^z), A) + I · cfc(Im(λ^z), A)

The resulting operator is bounded (from the CFC norm bound) and its matrix elements
are holomorphic (from the holomorphicity of the spectral Laplace). -/
def spectralSemigroupComplex
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hA_nonneg : 0 ≤ A)
    (hspec : spectrum ℝ A ⊆ Set.Icc 0 1)
    (z : ℂ) : H →L[ℂ] H :=
  cfc (specSemiFRe z) A + Complex.I • cfc (specSemiFIm z) A

/-! ### Helper lemmas for the inner product identity -/

/-- The polarization identity for a continuous linear map on a complex Hilbert space:
`⟨x, Ay⟩ = (1/4)(⟨x+y, A(x+y)⟩ - ⟨x-y, A(x-y)⟩ - I⟨x+iy, A(x+iy)⟩ + I⟨x-iy, A(x-iy)⟩)`.
-/
private theorem inner_polarization_clm (T : H →L[ℂ] H) (x y : H) :
    (1 / 4 : ℂ) * (@inner ℂ H _ (x + y) (T (x + y)) - @inner ℂ H _ (x - y) (T (x - y))
      - Complex.I * @inner ℂ H _ (x + Complex.I • y) (T (x + Complex.I • y))
      + Complex.I * @inner ℂ H _ (x - Complex.I • y) (T (x - Complex.I • y))) =
    @inner ℂ H _ x (T y) := by
  have hI_sq : Complex.I ^ 2 = (-1 : ℂ) := Complex.I_sq
  set a := @inner ℂ H _ x (T x)
  set b := @inner ℂ H _ x (T y)
  set c := @inner ℂ H _ y (T x)
  set d := @inner ℂ H _ y (T y)
  have h1 : @inner ℂ H _ (x + y) (T (x + y)) = a + b + c + d := by
    rw [map_add]; simp only [inner_add_left, inner_add_right]; ring
  have h2 : @inner ℂ H _ (x - y) (T (x - y)) = a - b - c + d := by
    rw [map_sub]; simp only [inner_sub_left, inner_sub_right]; ring
  have h3 : @inner ℂ H _ (x + Complex.I • y) (T (x + Complex.I • y)) =
      a + Complex.I * b - Complex.I * c + d := by
    rw [map_add, map_smul]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_I]
    ring_nf; rw [hI_sq]; ring
  have h4 : @inner ℂ H _ (x - Complex.I • y) (T (x - Complex.I • y)) =
      a - Complex.I * b + Complex.I * c + d := by
    rw [map_sub, map_smul]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_I]
    ring_nf; rw [hI_sq]; ring
  rw [h1, h2, h3, h4]; ring_nf; rw [hI_sq]; ring

/-- Full complex inner product for CFC of a real function on a self-adjoint operator:
since `cfc g A` is self-adjoint, `⟨v, cfc(g,A)v⟩` is real and equals `(∫ g dμ_v : ℂ)`. -/
private theorem inner_cfc_eq_ofReal_integral
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (v : H)
    (g : ℝ → ℝ) (hg : ContinuousOn g (spectrum ℝ A)) :
    @inner ℂ H _ v ((cfc g A) v) =
      ((∫ y, g y ∂(selfAdjointSpectralMeasureDiagonal A hA v)) : ℂ) := by
  have hsym : ((cfc g A : H →L[ℂ] H) : H →ₗ[ℂ] H).IsSymmetric :=
    isSelfAdjoint_iff_isSymmetric.mp IsSelfAdjoint.cfc
  have hre := re_inner_cfc_eq_integral_selfAdjointSpectralMeasureDiagonal A hA v g hg
  have hinner_conj : starRingEnd ℂ (@inner ℂ H _ v ((cfc g A) v)) =
      @inner ℂ H _ v ((cfc g A) v) := by
    rw [inner_conj_symm]; exact hsym v v
  rw [(Complex.conj_eq_iff_re.mp hinner_conj).symm, hre]
  exact (_root_.integral_ofReal (f := fun y => g ↑y)
    (μ := selfAdjointSpectralMeasureDiagonal A hA v)).symm

/-- Pointwise identity: `fRe(z,s) + I·fIm(z,s) = exp(z·log s)` for `s > 0`. -/
private theorem specSemiF_combined_eq_exp (z : ℂ) (s : ℝ) (hs : 0 < s) :
    (↑(specSemiFRe z s) : ℂ) + Complex.I * ↑(specSemiFIm z s) =
      Complex.exp (z * ↑(Real.log s)) := by
  simp only [specSemiFRe, specSemiFIm, if_neg (not_le.mpr hs)]
  have : z * ↑(Real.log s) = ↑(z.re * Real.log s) + ↑(z.im * Real.log s) * Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  rw [this, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I]
  push_cast; ring

/-- At `s ≤ 0`, both `fRe` and `fIm` vanish. -/
private theorem specSemiF_combined_eq_zero (z : ℂ) (s : ℝ) (hs : s ≤ 0) :
    (↑(specSemiFRe z s) : ℂ) + Complex.I * ↑(specSemiFIm z s) = 0 := by
  simp only [specSemiFRe, specSemiFIm, if_pos hs, Complex.ofReal_zero, mul_zero, add_zero]

/-- Continuity of `specSemiFRe z` on `[0, ∞)` when `Re(z) > 0`.

On `(0, ∞)`, the function is `exp(Re(z)·log s)·cos(Im(z)·log s)` (smooth).
At `s = 0`, the value is `0` and `|f(s)| ≤ s^{Re(z)} → 0` since `Re(z) > 0`. -/
private theorem specSemiFRe_continuousOn_Ici (z : ℂ) (hz : 0 < z.re) :
    ContinuousOn (specSemiFRe z) (Set.Ici 0) := by
  intro s hs
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hs) with rfl | hs_pos
  · -- At s = 0: value is 0, squeeze by |f(s)| ≤ s^{Re z} → 0
    rw [ContinuousWithinAt]
    simp only [specSemiFRe, if_pos le_rfl]
    apply squeeze_zero_norm'
    · filter_upwards [self_mem_nhdsWithin] with u hu
      simp only [specSemiFRe]
      split_ifs with h
      · simp; exact Real.rpow_nonneg (Set.mem_Ici.mp hu) z.re
      · push_neg at h
        rw [Real.norm_eq_abs, abs_mul]
        calc |Real.exp (z.re * Real.log u)| * |Real.cos (z.im * Real.log u)|
            ≤ |Real.exp (z.re * Real.log u)| * 1 := by
              gcongr; exact Real.abs_cos_le_one _
            _ = Real.exp (z.re * Real.log u) := by
              rw [mul_one, abs_of_pos (Real.exp_pos _)]
            _ = u ^ z.re := by
              rw [Real.rpow_def_of_pos h]; ring_nf
    · have : Tendsto (fun u : ℝ => u ^ z.re) (𝓝[Set.Ici 0] (0 : ℝ)) (𝓝 ((0 : ℝ) ^ z.re)) :=
        (Real.continuous_rpow_const (le_of_lt hz)).continuousAt.continuousWithinAt
      rwa [Real.zero_rpow (ne_of_gt hz)] at this
  · -- At s > 0: reduce to ContinuousAt, then use explicit formula
    rw [continuousWithinAt_iff_continuousAt (Ici_mem_nhds hs_pos)]
    have hne : s ≠ 0 := ne_of_gt hs_pos
    have hcont : ContinuousAt (fun u =>
        Real.exp (z.re * Real.log u) * Real.cos (z.im * Real.log u)) s :=
      ContinuousAt.mul
        (Real.continuous_exp.continuousAt.comp
          (continuousAt_const.mul (Real.continuousAt_log hne)))
        (Real.continuous_cos.continuousAt.comp
          (continuousAt_const.mul (Real.continuousAt_log hne)))
    apply hcont.congr
    filter_upwards [Ioi_mem_nhds hs_pos] with u hu
    simp [specSemiFRe, not_le.mpr (Set.mem_Ioi.mp hu)]

/-- Continuity of `specSemiFIm z` on `[0, ∞)` when `Re(z) > 0`. -/
private theorem specSemiFIm_continuousOn_Ici (z : ℂ) (hz : 0 < z.re) :
    ContinuousOn (specSemiFIm z) (Set.Ici 0) := by
  intro s hs
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hs) with rfl | hs_pos
  · rw [ContinuousWithinAt]
    simp only [specSemiFIm, if_pos le_rfl]
    apply squeeze_zero_norm'
    · filter_upwards [self_mem_nhdsWithin] with u hu
      simp only [specSemiFIm]
      split_ifs with h
      · simp; exact Real.rpow_nonneg (Set.mem_Ici.mp hu) z.re
      · push_neg at h
        rw [Real.norm_eq_abs, abs_mul]
        calc |Real.exp (z.re * Real.log u)| * |Real.sin (z.im * Real.log u)|
            ≤ |Real.exp (z.re * Real.log u)| * 1 := by
              gcongr; exact Real.abs_sin_le_one _
            _ = Real.exp (z.re * Real.log u) := by
              rw [mul_one, abs_of_pos (Real.exp_pos _)]
            _ = u ^ z.re := by
              rw [Real.rpow_def_of_pos h]; ring_nf
    · have : Tendsto (fun u : ℝ => u ^ z.re) (𝓝[Set.Ici 0] (0 : ℝ)) (𝓝 ((0 : ℝ) ^ z.re)) :=
        (Real.continuous_rpow_const (le_of_lt hz)).continuousAt.continuousWithinAt
      rwa [Real.zero_rpow (ne_of_gt hz)] at this
  · rw [continuousWithinAt_iff_continuousAt (Ici_mem_nhds hs_pos)]
    have hne : s ≠ 0 := ne_of_gt hs_pos
    have hcont : ContinuousAt (fun u =>
        Real.exp (z.re * Real.log u) * Real.sin (z.im * Real.log u)) s :=
      ContinuousAt.mul
        (Real.continuous_exp.continuousAt.comp
          (continuousAt_const.mul (Real.continuousAt_log hne)))
        (Real.continuous_sin.continuousAt.comp
          (continuousAt_const.mul (Real.continuousAt_log hne)))
    apply hcont.congr
    filter_upwards [Ioi_mem_nhds hs_pos] with u hu
    simp [specSemiFIm, not_le.mpr (Set.mem_Ioi.mp hu)]

/-- The complex-valued change-of-variables for the Laplace bridge:
`∫ exp(z · log s) d(μ.restrict(Ioi 0)) = ∫ exp(-(z·u)) d(laplaceMeasurePos μ)`. -/
private theorem complex_laplace_change_of_var
    (μ : Measure ℝ) [IsFiniteMeasure μ] (z : ℂ) :
    ∫ s, Complex.exp (z * ↑(Real.log s)) ∂(μ.restrict (Set.Ioi 0)) =
      ∫ u, Complex.exp (-(z * ↑u)) ∂(BochnerLaplaceBridge.laplaceMeasurePos μ) := by
  unfold BochnerLaplaceBridge.laplaceMeasurePos
  have hmeas_neg : Measurable BochnerLaplaceBridge.negLogMap :=
    BochnerLaplaceBridge.negLogMap_measurable
  have hf_meas : AEStronglyMeasurable (fun u => Complex.exp (-(z * ↑u)))
      ((μ.restrict (Set.Ioi 0)).map BochnerLaplaceBridge.negLogMap) :=
    (Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).neg)).aestronglyMeasurable
  rw [MeasureTheory.integral_map hmeas_neg.aemeasurable hf_meas]
  apply integral_congr_ae
  filter_upwards with s
  congr 1
  simp [BochnerLaplaceBridge.negLogMap]

private theorem specSemiFRe_measurable (z : ℂ) : Measurable (specSemiFRe z) := by
  unfold specSemiFRe
  exact Measurable.ite measurableSet_Iic measurable_const
    ((Real.measurable_exp.comp (measurable_const.mul Real.measurable_log)).mul
     (Real.measurable_cos.comp (measurable_const.mul Real.measurable_log)))

private theorem specSemiFIm_measurable (z : ℂ) : Measurable (specSemiFIm z) := by
  unfold specSemiFIm
  exact Measurable.ite measurableSet_Iic measurable_const
    ((Real.measurable_exp.comp (measurable_const.mul Real.measurable_log)).mul
     (Real.measurable_sin.comp (measurable_const.mul Real.measurable_log)))

private theorem combined_integral_eq_laplace
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hspec : spectrum ℝ A ⊆ Set.Icc 0 1)
    (v : H) (z : ℂ) (hz : 0 < z.re) :
    ∫ y, ((specSemiFRe z ↑y : ℝ) : ℂ) + Complex.I * ((specSemiFIm z ↑y : ℝ) : ℂ)
      ∂(selfAdjointSpectralMeasureDiagonal A hA v) =
    selfAdjointSpectralLaplaceDiagonal A hA v z := by
  set μ_spec := selfAdjointSpectralMeasureDiagonal A hA v
  set μ_real := selfAdjointSpectralMeasureDiagonalReal A hA v
  haveI hfin_spec : IsFiniteMeasure μ_spec := by
    show IsFiniteMeasure (selfAdjointSpectralMeasureDiagonal A hA v)
    unfold selfAdjointSpectralMeasureDiagonal; infer_instance
  -- Step 1: Push from spectrum subtype to ℝ
  let h : ℝ → ℂ := fun s => ↑(specSemiFRe z s) + Complex.I * ↑(specSemiFIm z s)
  have hh_meas : AEStronglyMeasurable h μ_real := by
    exact ((Complex.continuous_ofReal.measurable.comp (specSemiFRe_measurable z)).add
      (measurable_const.mul
        (Complex.continuous_ofReal.measurable.comp (specSemiFIm_measurable z)))).aestronglyMeasurable
  have step1 : ∫ y, h ↑y ∂μ_spec = ∫ s, h s ∂μ_real := by
    change ∫ y, h ↑y ∂μ_spec = ∫ s, h s ∂(μ_spec.map ((↑) : spectrum ℝ A → ℝ))
    exact (MeasureTheory.integral_map
      (by fun_prop : Measurable ((↑) : spectrum ℝ A → ℝ)).aemeasurable hh_meas).symm
  rw [show (∫ y, ((↑(specSemiFRe z ↑y) : ℂ) + Complex.I * ↑(specSemiFIm z ↑y)) ∂μ_spec) =
    ∫ y, h ↑y ∂μ_spec from rfl, step1]
  -- Step 2: Replace integrand a.e. with exp(z · log s)
  have hsupp_nonneg : μ_real (Set.Iio 0) = 0 :=
    selfAdjointSpectralMeasureDiagonalReal_Iio_eq_zero_of_spectrum_subset_Icc A hA v hspec
  have hae_nonneg : ∀ᵐ s ∂μ_real, 0 ≤ s := by
    rw [ae_iff]; simpa [Set.compl_setOf, not_le] using hsupp_nonneg
  have step2 : ∫ s, h s ∂μ_real =
      ∫ s, (if 0 < s then Complex.exp (z * ↑(Real.log s)) else 0) ∂μ_real := by
    apply integral_congr_ae
    filter_upwards [hae_nonneg] with s hs
    rcases lt_or_eq_of_le hs with hpos | heq
    · simp only [if_pos hpos]
      exact specSemiF_combined_eq_exp z s hpos
    · simp only [← heq, lt_irrefl, if_false]
      exact specSemiF_combined_eq_zero z 0 le_rfl
  rw [step2]
  -- Step 3: The integral of the if-then-else = integral over Ioi 0
  have step3 : ∫ s, (if 0 < s then Complex.exp (z * ↑(Real.log s)) else 0) ∂μ_real =
      ∫ s, Complex.exp (z * ↑(Real.log s)) ∂(μ_real.restrict (Set.Ioi 0)) := by
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with s
    simp only [Set.indicator, Set.mem_Ioi]
  rw [step3]
  -- Step 4: Change of variables via negLogMap
  rw [complex_laplace_change_of_var]
  -- Step 5: Match with selfAdjointSpectralLaplaceDiagonal
  rfl

/-- Diagonal identity: `⟨v, T(z)v⟩ = selfAdjointSpectralLaplaceDiagonal A hA v z`.

This is the core identity connecting the CFC definition to the spectral Laplace. -/
private theorem spectralSemigroupComplex_inner_diag_eq
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hA_nonneg : 0 ≤ A)
    (hspec : spectrum ℝ A ⊆ Set.Icc 0 1)
    (v : H) (z : ℂ) (hz : 0 < z.re) :
    @inner ℂ H _ v (spectralSemigroupComplex A hA hA_nonneg hspec z v) =
      selfAdjointSpectralLaplaceDiagonal A hA v z := by
  -- Step 1: Expand T(z) = cfc(fRe) + I · cfc(fIm)
  unfold spectralSemigroupComplex
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    inner_add_right, inner_smul_right]
  -- Step 2: Each CFC inner product = ofReal integral via self-adjointness
  have hfRe_cont : ContinuousOn (specSemiFRe z) (spectrum ℝ A) :=
    (specSemiFRe_continuousOn_Ici z hz).mono
      (fun s hs => (hspec hs).1)
  have hfIm_cont : ContinuousOn (specSemiFIm z) (spectrum ℝ A) :=
    (specSemiFIm_continuousOn_Ici z hz).mono
      (fun s hs => (hspec hs).1)
  rw [inner_cfc_eq_ofReal_integral A hA v (specSemiFRe z) hfRe_cont,
    inner_cfc_eq_ofReal_integral A hA v (specSemiFIm z) hfIm_cont]
  -- Step 3: Combine ∫ ↑fRe + I * ∫ ↑fIm = ∫ (↑fRe + I * ↑fIm)
  set μ := selfAdjointSpectralMeasureDiagonal A hA v
  haveI : IsFiniteMeasure μ := by
    show IsFiniteMeasure (selfAdjointSpectralMeasureDiagonal A hA v)
    unfold selfAdjointSpectralMeasureDiagonal; infer_instance
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K _ => measure_lt_top μ K⟩
  have hfRe_int : Integrable (fun y : spectrum ℝ A => (↑(specSemiFRe z ↑y) : ℂ)) μ :=
    (Complex.continuous_ofReal.comp hfRe_cont.restrict).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfIm_int : Integrable (fun y : spectrum ℝ A => Complex.I * (↑(specSemiFIm z ↑y) : ℂ)) μ :=
    (continuous_const.mul (Complex.continuous_ofReal.comp hfIm_cont.restrict)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [show Complex.I * ∫ (y : spectrum ℝ A), (↑(specSemiFIm z ↑y) : ℂ) ∂μ =
    ∫ (y : spectrum ℝ A), Complex.I * (↑(specSemiFIm z ↑y) : ℂ) ∂μ from
    (MeasureTheory.integral_const_mul _ _).symm, ← integral_add hfRe_int hfIm_int]
  -- Now: ∫ (↑fRe + I * ↑fIm) dμ_spec = selfAdjointSpectralLaplaceDiagonal
  exact combined_integral_eq_laplace A hA hspec v z hz

/-- Defining property: `⟨x, T(z)(y)⟩ = spectralLaplaceOffdiag(A, x, y, z)`.

Proved via polarization: both sides are the same polarization of the diagonal form,
and the diagonal identity is proved in `spectralSemigroupComplex_inner_diag_eq`. -/
theorem spectralSemigroupComplex_inner_eq
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hA_nonneg : 0 ≤ A)
    (hspec : spectrum ℝ A ⊆ Set.Icc 0 1)
    (x y : H) (z : ℂ) (hz : 0 < z.re) :
    @inner ℂ H _ x (spectralSemigroupComplex A hA hA_nonneg hspec z y) =
      selfAdjointSpectralLaplaceOffdiag A hA x y z := by
  rw [← inner_polarization_clm (spectralSemigroupComplex A hA hA_nonneg hspec z) x y]
  simp only [selfAdjointSpectralLaplaceOffdiag]
  congr 1
  simp only [spectralSemigroupComplex_inner_diag_eq A hA hA_nonneg hspec _ _ hz]

/-- At positive real points, `spectralSemigroupComplex` agrees with `CFC.nnrpow`. -/
theorem spectralSemigroupComplex_ofReal_eq_nnrpow
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hA_nonneg : 0 ≤ A)
    (hspec : spectrum ℝ A ⊆ Set.Icc 0 1)
    (t : ℝ) (ht : 0 < t) :
    spectralSemigroupComplex A hA hA_nonneg hspec (t : ℂ) =
      CFC.nnrpow A (Real.toNNReal t) := by
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [spectralSemigroupComplex_inner_eq A hA hA_nonneg hspec x y _ (by simp [ht]),
    selfAdjointSpectralLaplaceOffdiag_ofReal_eq_inner_nnrpow A hA hA_nonneg hspec x y t ht]

/-- At positive real points, `spectralSemigroupComplex` satisfies the semigroup law. -/
theorem spectralSemigroupComplex_ofReal_add
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hA_nonneg : 0 ≤ A)
    (hspec : spectrum ℝ A ⊆ Set.Icc 0 1)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    spectralSemigroupComplex A hA hA_nonneg hspec ((s + t : ℝ) : ℂ) =
      (spectralSemigroupComplex A hA hA_nonneg hspec (s : ℂ)).comp
        (spectralSemigroupComplex A hA hA_nonneg hspec (t : ℂ)) := by
  rw [spectralSemigroupComplex_ofReal_eq_nnrpow A hA hA_nonneg hspec (s + t) (add_pos hs ht)]
  rw [spectralSemigroupComplex_ofReal_eq_nnrpow A hA hA_nonneg hspec s hs]
  rw [spectralSemigroupComplex_ofReal_eq_nnrpow A hA hA_nonneg hspec t ht]
  have hs' := Real.toNNReal_pos.mpr hs
  have ht' := Real.toNNReal_pos.mpr ht
  simpa [show (HMul.hMul :
      (H →L[ℂ] H) → _ → _) =
      ContinuousLinearMap.comp from rfl,
    Real.toNNReal_of_nonneg hs.le,
    Real.toNNReal_of_nonneg ht.le,
    Real.toNNReal_of_nonneg (add_nonneg hs.le ht.le)] using
      CFC.nnrpow_add (a := A) hs' ht'

/-- Any bounded operator commuting with `A` also commutes with the complex spectral semigroup
whenever `Re(z) > 0`. -/
theorem Commute.spectralSemigroupComplex
    {A B : H →L[ℂ] H}
    (hBA : Commute B A)
    (hA : IsSelfAdjoint A)
    (hA_nonneg : 0 ≤ A)
    (hspec : spectrum ℝ A ⊆ Set.Icc 0 1)
    (z : ℂ) (hz : 0 < z.re) :
    Commute B (spectralSemigroupComplex A hA hA_nonneg hspec z) := by
  show Commute B (cfc (specSemiFRe z) A + Complex.I • cfc (specSemiFIm z) A)
  exact ((hBA.symm.cfc_real (specSemiFRe z)).symm).add_right
    (((hBA.symm.cfc_real (specSemiFIm z)).symm).smul_right _)

/-! ### Holomorphicity of matrix elements -/

/-- `z ↦ ⟨x, T(z)(y)⟩` is holomorphic on `{z | Re(z) > 0}`. -/
theorem spectralSemigroupComplex_differentiableOn
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hA_nonneg : 0 ≤ A)
    (hspec : spectrum ℝ A ⊆ Set.Icc 0 1)
    (x y : H) :
    DifferentiableOn ℂ
      (fun z => @inner ℂ H _ x (spectralSemigroupComplex A hA hA_nonneg hspec z y))
      {z : ℂ | 0 < z.re} := by
  exact (differentiableOn_selfAdjointSpectralLaplaceOffdiag A hA hspec x y).congr
    fun z hz => spectralSemigroupComplex_inner_eq A hA hA_nonneg hspec x y z hz

/-! ### Continuity in the strong operator topology -/

private theorem continuous_specSemiFRe_uncurry
    (A : H →L[ℂ] H) (hspec : spectrum ℝ A ⊆ Set.Icc 0 1) :
    Continuous (fun p : {z : ℂ // 0 < z.re} × spectrum ℝ A =>
      specSemiFRe p.1.1 p.2.1) := by
  rw [continuous_iff_continuousAt]
  intro p
  rcases eq_or_lt_of_le ((hspec p.2.2).1) with hs0 | hs_pos
  · have hδ : 0 < p.1.1.re / 2 := half_pos p.1.2
    have hs0' : p.2.1 = 0 := by simpa using hs0.symm
    have hRe : ∀ᶠ q in 𝓝 p, p.1.1.re / 2 < q.1.1.re := by
      exact (Complex.continuous_re.comp
          (continuous_subtype_val.comp continuous_fst)).continuousAt.preimage_mem_nhds
        (Ioi_mem_nhds (by nlinarith : p.1.1.re / 2 < p.1.1.re))
    rw [ContinuousAt, show specSemiFRe p.1.1 p.2.1 = 0 by simp [specSemiFRe, hs0]]
    have hbound :
        ∀ᶠ q in 𝓝 p, ‖specSemiFRe q.1.1 q.2.1‖ ≤ q.2.1 ^ (p.1.1.re / 2) := by
      filter_upwards [hRe] with q hq
      rcases eq_or_lt_of_le ((hspec q.2.2).1) with hq0 | hq_pos
      · have hq0' : q.2.1 = 0 := by simpa using hq0.symm
        simp [hq0', specSemiFRe, Real.zero_rpow (by positivity : p.1.1.re / 2 ≠ 0)]
      · have hq_le1 : q.2.1 ≤ 1 := (hspec q.2.2).2
        have hlog_nonpos : Real.log q.2.1 ≤ 0 := Real.log_nonpos hq_pos.le hq_le1
        rw [Real.norm_eq_abs, specSemiFRe, if_neg (not_le.mpr hq_pos)]
        calc
          |Real.exp (q.1.1.re * Real.log q.2.1) * Real.cos (q.1.1.im * Real.log q.2.1)|
              = |Real.exp (q.1.1.re * Real.log q.2.1)| *
                  |Real.cos (q.1.1.im * Real.log q.2.1)| := by
                    rw [abs_mul]
          _ ≤ Real.exp (q.1.1.re * Real.log q.2.1) * 1 := by
                simpa [abs_of_pos (Real.exp_pos _)] using
                  (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
                    (le_of_lt (Real.exp_pos _)))
          _ = Real.exp (q.1.1.re * Real.log q.2.1) := by rw [mul_one]
          _ ≤ Real.exp ((p.1.1.re / 2) * Real.log q.2.1) := by
                exact Real.exp_le_exp.mpr
                  (mul_le_mul_of_nonpos_right (le_of_lt hq) hlog_nonpos)
          _ = q.2.1 ^ (p.1.1.re / 2) := by
                rw [Real.rpow_def_of_pos hq_pos, mul_comm]
    have hpow :
          Tendsto (fun q : {z : ℂ // 0 < z.re} × spectrum ℝ A =>
              q.2.1 ^ (p.1.1.re / 2)) (𝓝 p)
            (𝓝 (p.2.1 ^ (p.1.1.re / 2))) :=
        ((continuous_subtype_val.comp continuous_snd).continuousAt.rpow_const
          (Or.inr (le_of_lt hδ))).tendsto
    have hpow0 :
        Tendsto (fun q : {z : ℂ // 0 < z.re} × spectrum ℝ A =>
            q.2.1 ^ (p.1.1.re / 2)) (𝓝 p) (𝓝 0) := by
      simpa [hs0', Real.zero_rpow (by positivity : p.1.1.re / 2 ≠ 0)] using hpow
    exact squeeze_zero_norm' hbound hpow0
  · have hq_pos : ∀ᶠ q in 𝓝 p, 0 < q.2.1 := by
      exact (continuous_subtype_val.comp continuous_snd).continuousAt.preimage_mem_nhds
        (Ioi_mem_nhds hs_pos)
    have hcont :
        ContinuousAt
          (fun q : {z : ℂ // 0 < z.re} × spectrum ℝ A =>
            Real.exp (q.1.1.re * Real.log q.2.1) *
              Real.cos (q.1.1.im * Real.log q.2.1)) p := by
      have hre :
          ContinuousAt (fun q : {z : ℂ // 0 < z.re} × spectrum ℝ A => q.1.1.re) p :=
        (Complex.continuous_re.comp
          (continuous_subtype_val.comp continuous_fst)).continuousAt
      have him :
          ContinuousAt (fun q : {z : ℂ // 0 < z.re} × spectrum ℝ A => q.1.1.im) p :=
        (Complex.continuous_im.comp
          (continuous_subtype_val.comp continuous_fst)).continuousAt
      have hsnd :
          ContinuousAt (fun q : {z : ℂ // 0 < z.re} × spectrum ℝ A => q.2.1) p :=
        (continuous_subtype_val.comp continuous_snd).continuousAt
      have hsndSubtype :
          ContinuousAt (fun q : {z : ℂ // 0 < z.re} × spectrum ℝ A => q.2) p :=
        continuous_snd.continuousAt
      have hlog' : ContinuousAt (fun s : ℝ => Real.log s) p.2.1 :=
        Real.continuousAt_log hs_pos.ne'
      have hlogSubtype :
          ContinuousAt (fun s : spectrum ℝ A => Real.log s.1) p.2 := by
        simpa using hlog'.comp continuous_subtype_val.continuousAt
      have hlog :
          ContinuousAt (fun q : {z : ℂ // 0 < z.re} × spectrum ℝ A => Real.log q.2.1) p :=
        by simpa using hlogSubtype.comp hsndSubtype
      exact (Real.continuous_exp.continuousAt.comp (hre.mul hlog)).mul
        (Real.continuous_cos.continuousAt.comp (him.mul hlog))
    exact hcont.congr <| by
      filter_upwards [hq_pos] with q hq
      simp [specSemiFRe, not_le.mpr hq]

private theorem continuous_specSemiFIm_uncurry
    (A : H →L[ℂ] H) (hspec : spectrum ℝ A ⊆ Set.Icc 0 1) :
    Continuous (fun p : {z : ℂ // 0 < z.re} × spectrum ℝ A =>
      specSemiFIm p.1.1 p.2.1) := by
  rw [continuous_iff_continuousAt]
  intro p
  rcases eq_or_lt_of_le ((hspec p.2.2).1) with hs0 | hs_pos
  · have hδ : 0 < p.1.1.re / 2 := half_pos p.1.2
    have hs0' : p.2.1 = 0 := by simpa using hs0.symm
    have hRe : ∀ᶠ q in 𝓝 p, p.1.1.re / 2 < q.1.1.re := by
      exact (Complex.continuous_re.comp
          (continuous_subtype_val.comp continuous_fst)).continuousAt.preimage_mem_nhds
        (Ioi_mem_nhds (by nlinarith : p.1.1.re / 2 < p.1.1.re))
    rw [ContinuousAt, show specSemiFIm p.1.1 p.2.1 = 0 by simp [specSemiFIm, hs0]]
    have hbound :
        ∀ᶠ q in 𝓝 p, ‖specSemiFIm q.1.1 q.2.1‖ ≤ q.2.1 ^ (p.1.1.re / 2) := by
      filter_upwards [hRe] with q hq
      rcases eq_or_lt_of_le ((hspec q.2.2).1) with hq0 | hq_pos
      · have hq0' : q.2.1 = 0 := by simpa using hq0.symm
        simp [hq0', specSemiFIm, Real.zero_rpow (by positivity : p.1.1.re / 2 ≠ 0)]
      · have hq_le1 : q.2.1 ≤ 1 := (hspec q.2.2).2
        have hlog_nonpos : Real.log q.2.1 ≤ 0 := Real.log_nonpos hq_pos.le hq_le1
        rw [Real.norm_eq_abs, specSemiFIm, if_neg (not_le.mpr hq_pos)]
        calc
          |Real.exp (q.1.1.re * Real.log q.2.1) * Real.sin (q.1.1.im * Real.log q.2.1)|
              = |Real.exp (q.1.1.re * Real.log q.2.1)| *
                  |Real.sin (q.1.1.im * Real.log q.2.1)| := by
                    rw [abs_mul]
          _ ≤ Real.exp (q.1.1.re * Real.log q.2.1) * 1 := by
                simpa [abs_of_pos (Real.exp_pos _)] using
                  (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _)
                    (le_of_lt (Real.exp_pos _)))
          _ = Real.exp (q.1.1.re * Real.log q.2.1) := by rw [mul_one]
          _ ≤ Real.exp ((p.1.1.re / 2) * Real.log q.2.1) := by
                exact Real.exp_le_exp.mpr
                  (mul_le_mul_of_nonpos_right (le_of_lt hq) hlog_nonpos)
          _ = q.2.1 ^ (p.1.1.re / 2) := by
                rw [Real.rpow_def_of_pos hq_pos, mul_comm]
    have hpow :
          Tendsto (fun q : {z : ℂ // 0 < z.re} × spectrum ℝ A =>
              q.2.1 ^ (p.1.1.re / 2)) (𝓝 p)
            (𝓝 (p.2.1 ^ (p.1.1.re / 2))) :=
        ((continuous_subtype_val.comp continuous_snd).continuousAt.rpow_const
          (Or.inr (le_of_lt hδ))).tendsto
    have hpow0 :
        Tendsto (fun q : {z : ℂ // 0 < z.re} × spectrum ℝ A =>
            q.2.1 ^ (p.1.1.re / 2)) (𝓝 p) (𝓝 0) := by
      simpa [hs0', Real.zero_rpow (by positivity : p.1.1.re / 2 ≠ 0)] using hpow
    exact squeeze_zero_norm' hbound hpow0
  · have hq_pos : ∀ᶠ q in 𝓝 p, 0 < q.2.1 := by
      exact (continuous_subtype_val.comp continuous_snd).continuousAt.preimage_mem_nhds
        (Ioi_mem_nhds hs_pos)
    have hcont :
        ContinuousAt
          (fun q : {z : ℂ // 0 < z.re} × spectrum ℝ A =>
            Real.exp (q.1.1.re * Real.log q.2.1) *
              Real.sin (q.1.1.im * Real.log q.2.1)) p := by
      have hre :
          ContinuousAt (fun q : {z : ℂ // 0 < z.re} × spectrum ℝ A => q.1.1.re) p :=
        (Complex.continuous_re.comp
          (continuous_subtype_val.comp continuous_fst)).continuousAt
      have him :
          ContinuousAt (fun q : {z : ℂ // 0 < z.re} × spectrum ℝ A => q.1.1.im) p :=
        (Complex.continuous_im.comp
          (continuous_subtype_val.comp continuous_fst)).continuousAt
      have hsnd :
          ContinuousAt (fun q : {z : ℂ // 0 < z.re} × spectrum ℝ A => q.2.1) p :=
        (continuous_subtype_val.comp continuous_snd).continuousAt
      have hsndSubtype :
          ContinuousAt (fun q : {z : ℂ // 0 < z.re} × spectrum ℝ A => q.2) p :=
        continuous_snd.continuousAt
      have hlog' : ContinuousAt (fun s : ℝ => Real.log s) p.2.1 :=
        Real.continuousAt_log hs_pos.ne'
      have hlogSubtype :
          ContinuousAt (fun s : spectrum ℝ A => Real.log s.1) p.2 := by
        simpa using hlog'.comp continuous_subtype_val.continuousAt
      have hlog :
          ContinuousAt (fun q : {z : ℂ // 0 < z.re} × spectrum ℝ A => Real.log q.2.1) p :=
        by simpa using hlogSubtype.comp hsndSubtype
      exact (Real.continuous_exp.continuousAt.comp (hre.mul hlog)).mul
        (Real.continuous_sin.continuousAt.comp (him.mul hlog))
    exact hcont.congr <| by
      filter_upwards [hq_pos] with q hq
      simp [specSemiFIm, not_le.mpr hq]

/-- `z ↦ T(z)` is continuous on `{z | Re(z) > 0}` in operator norm. -/
theorem spectralSemigroupComplex_continuousOn
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hA_nonneg : 0 ≤ A)
    (hspec : spectrum ℝ A ⊆ Set.Icc 0 1) :
    ContinuousOn (fun z => spectralSemigroupComplex A hA hA_nonneg hspec z)
      {z : ℂ | 0 < z.re} := by
  haveI : CompactSpace (spectrum ℝ A) :=
    isCompact_iff_compactSpace.mp (ContinuousFunctionalCalculus.isCompact_spectrum A)
  let HP := {z : ℂ // 0 < z.re}
  let fReCM : HP → C(spectrum ℝ A, ℝ) := fun z =>
    ⟨fun s => specSemiFRe z.1 s.1,
      by
        have hcont : ContinuousOn (fun s : ℝ => specSemiFRe z.1 s) (spectrum ℝ A) :=
          (specSemiFRe_continuousOn_Ici z.1 z.2).mono (fun s hs => (hspec hs).1)
        simpa [Set.restrict_def] using (continuousOn_iff_continuous_restrict.mp hcont)⟩
  let fImCM : HP → C(spectrum ℝ A, ℝ) := fun z =>
    ⟨fun s => specSemiFIm z.1 s.1,
      by
        have hcont : ContinuousOn (fun s : ℝ => specSemiFIm z.1 s) (spectrum ℝ A) :=
          (specSemiFIm_continuousOn_Ici z.1 z.2).mono (fun s hs => (hspec hs).1)
        simpa [Set.restrict_def] using (continuousOn_iff_continuous_restrict.mp hcont)⟩
  have hReC : Continuous fReCM := by
    refine ContinuousMap.continuous_of_continuous_uncurry fReCM ?_
    simpa [fReCM, Function.uncurry] using continuous_specSemiFRe_uncurry (A := A) hspec
  have hImC : Continuous fImCM := by
    refine ContinuousMap.continuous_of_continuous_uncurry fImCM ?_
    simpa [fImCM, Function.uncurry] using continuous_specSemiFIm_uncurry (A := A) hspec
  have hfReSection :
      ∀ z : HP, ContinuousOn (fun s : ℝ => specSemiFRe z.1 s) (spectrum ℝ A) := by
    intro z
    exact (specSemiFRe_continuousOn_Ici z.1 z.2).mono (fun s hs => (hspec hs).1)
  have hfImSection :
      ∀ z : HP, ContinuousOn (fun s : ℝ => specSemiFIm z.1 s) (spectrum ℝ A) := by
    intro z
    exact (specSemiFIm_continuousOn_Ici z.1 z.2).mono (fun s hs => (hspec hs).1)
  have hReUniform :
      Continuous (fun z : HP => UniformOnFun.ofFun {spectrum ℝ A}
        (fun s : ℝ => specSemiFRe z.1 s)) :=
    (ContinuousOn.continuous_restrict_iff_continuous_uniformOnFun
      (f := fun z : HP => fun s : ℝ => specSemiFRe z.1 s)
      (s := spectrum ℝ A) hfReSection).mp hReC
  have hImUniform :
      Continuous (fun z : HP => UniformOnFun.ofFun {spectrum ℝ A}
        (fun s : ℝ => specSemiFIm z.1 s)) :=
    (ContinuousOn.continuous_restrict_iff_continuous_uniformOnFun
      (f := fun z : HP => fun s : ℝ => specSemiFIm z.1 s)
      (s := spectrum ℝ A) hfImSection).mp hImC
  have hReOp : Continuous fun z : HP => cfc (fun s => specSemiFRe z.1 s) A := by
    exact Continuous.cfc_fun (f := fun z : HP => fun s : ℝ => specSemiFRe z.1 s) (a := A)
      hReUniform hfReSection
  have hImOp : Continuous fun z : HP => cfc (fun s => specSemiFIm z.1 s) A := by
    exact Continuous.cfc_fun (f := fun z : HP => fun s : ℝ => specSemiFIm z.1 s) (a := A)
      hImUniform hfImSection
  rw [continuousOn_iff_continuous_restrict]
  unfold Set.restrict
  unfold spectralSemigroupComplex
  simpa using hReOp.add (continuous_const.smul hImOp)

/-- `z ↦ T(z)(y)` is continuous on `{z | Re(z) > 0}` for each fixed `y`.

Proof sketch: From the Riesz construction, T(z)(y) depends on z through the spectral
Laplace integrals. The continuity follows from dominated convergence applied to the
Laplace integrals (the integrand exp(-zu) is uniformly bounded for Re(z) ≥ δ > 0). -/
theorem spectralSemigroupComplex_strongContinuousOn
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hA_nonneg : 0 ≤ A)
    (hspec : spectrum ℝ A ⊆ Set.Icc 0 1)
    (y : H) :
    ContinuousOn (fun z => spectralSemigroupComplex A hA hA_nonneg hspec z y)
      {z : ℂ | 0 < z.re} := by
  exact (ContinuousLinearMap.apply ℂ H y).continuous.comp_continuousOn
    (spectralSemigroupComplex_continuousOn A hA hA_nonneg hspec)

/-! ### Operator norm bound -/

/-- `‖T(z)‖ ≤ 2` for `Re(z) > 0`. -/
theorem spectralSemigroupComplex_norm_le
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hA_nonneg : 0 ≤ A)
    (hspec : spectrum ℝ A ⊆ Set.Icc 0 1)
    (z : ℂ) (hz : 0 < z.re) :
    ‖spectralSemigroupComplex A hA hA_nonneg hspec z‖ ≤ 2 := by
  unfold spectralSemigroupComplex
  -- ‖cfc(fRe) + I·cfc(fIm)‖ ≤ ‖cfc(fRe)‖ + ‖I·cfc(fIm)‖
  calc ‖cfc (specSemiFRe z) A + Complex.I • cfc (specSemiFIm z) A‖
      ≤ ‖cfc (specSemiFRe z) A‖ + ‖Complex.I • cfc (specSemiFIm z) A‖ := norm_add_le _ _
    _ ≤ 1 + 1 := by
        gcongr
        · -- ‖cfc(fRe)‖ ≤ 1
          exact norm_cfc_le one_pos.le (fun s hs => by
            simp only [specSemiFRe, Real.norm_eq_abs]
            split_ifs with h
            · simp
            · push_neg at h
              calc |Real.exp (z.re * Real.log s) * Real.cos (z.im * Real.log s)|
                  ≤ |Real.exp (z.re * Real.log s)| * 1 := by
                    rw [abs_mul]; gcongr; exact Real.abs_cos_le_one _
                  _ = Real.exp (z.re * Real.log s) := by
                    rw [mul_one, abs_of_pos (Real.exp_pos _)]
                  _ ≤ Real.exp 0 := by
                    gcongr; exact mul_nonpos_of_nonneg_of_nonpos hz.le
                      (Real.log_nonpos h.le (hspec hs).2)
                  _ = 1 := Real.exp_zero)
        · -- ‖I·cfc(fIm)‖ ≤ 1
          rw [norm_smul, Complex.norm_I, one_mul]
          exact norm_cfc_le one_pos.le (fun s hs => by
            simp only [specSemiFIm, Real.norm_eq_abs]
            split_ifs with h
            · simp
            · push_neg at h
              calc |Real.exp (z.re * Real.log s) * Real.sin (z.im * Real.log s)|
                  ≤ |Real.exp (z.re * Real.log s)| * 1 := by
                    rw [abs_mul]; gcongr; exact Real.abs_sin_le_one _
                  _ = Real.exp (z.re * Real.log s) := by
                    rw [mul_one, abs_of_pos (Real.exp_pos _)]
                  _ ≤ Real.exp 0 := by
                    gcongr; exact mul_nonpos_of_nonneg_of_nonpos hz.le
                      (Real.log_nonpos h.le (hspec hs).2)
                  _ = 1 := Real.exp_zero)
    _ = 2 := by norm_num

/-! ### Joint continuity

The map (z, v) ↦ T(z)(v) is jointly continuous on {Re(z) > 0} × H.
This follows from the contraction bound ‖T(z)‖ ≤ 4 and strong continuity:
  ‖T(z)(v) - T(z₀)(v₀)‖ ≤ ‖T(z)(v - v₀)‖ + ‖(T(z) - T(z₀))(v₀)‖
    ≤ 4‖v - v₀‖ + ‖T(z)(v₀) - T(z₀)(v₀)‖ → 0 -/

theorem spectralSemigroupComplex_jointlyContinuousOn
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hA_nonneg : 0 ≤ A)
    (hspec : spectrum ℝ A ⊆ Set.Icc 0 1) :
    ContinuousOn (fun p : ℂ × H => spectralSemigroupComplex A hA hA_nonneg hspec p.1 p.2)
      ({z : ℂ | 0 < z.re} ×ˢ Set.univ) := by
  exact ((spectralSemigroupComplex_continuousOn A hA hA_nonneg hspec).comp continuousOn_fst
    (fun p hp => hp.1)).clm_apply continuousOn_snd

end ContinuousLinearMap
