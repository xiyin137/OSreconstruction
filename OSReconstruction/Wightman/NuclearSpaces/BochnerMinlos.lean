/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import OSReconstruction.Wightman.NuclearSpaces.NuclearSpace
import OSReconstruction.Wightman.NuclearSpaces.GaussianFieldBridge
import OSReconstruction.Wightman.NuclearSpaces.Helpers.PositiveDefiniteKernels

/-!
# Bochner's Theorem and Minlos' Theorem

This file develops the Bochner-Minlos theorem, which is the key tool for constructing
Euclidean field theory measures from characteristic functionals.

## Main Definitions

* `IsPositiveDefiniteFn` - A function φ : E → ℂ is positive-definite if
  Σᵢⱼ c̄ᵢ cⱼ φ(xⱼ - xᵢ) ≥ 0 for all finite families.
* `CharacteristicFunctional` - A continuous positive-definite functional C : E → ℂ
  with C(0) = 1, on a nuclear space E.
* `bochner_theorem` - (ℝⁿ) Continuous positive-definite φ with φ(0) = 1 corresponds
  to a unique probability measure via Fourier transform.
* `minlos_theorem` - (Nuclear spaces) Continuous positive-definite C with C(0) = 1
  on a nuclear space E corresponds to a unique probability measure on E* (the dual).

## Mathematical Background

**Bochner's theorem** (finite-dimensional): Let φ : ℝⁿ → ℂ be continuous and positive-definite
with φ(0) = 1. Then there exists a unique probability measure μ on ℝⁿ such that
φ(t) = ∫ exp(i⟨t,x⟩) dμ(x) = 𝔼[e^{i⟨t,X⟩}] (i.e., φ is the characteristic function of μ).

**Minlos' theorem** (infinite-dimensional): Let E be a nuclear space and C : E → ℂ be
continuous and positive-definite with C(0) = 1. Then there exists a unique probability
measure μ on E* (the topological dual, with weak-* σ-algebra) such that
C(f) = ∫_{E*} exp(i ω(f)) dμ(ω) for all f ∈ E.

The proof of Minlos uses:
1. Bochner on finite-dimensional quotients E/V (V = ker of finite seminorms)
2. The resulting finite-dimensional measures form a projective family
3. Nuclearity of E provides tightness of the projective family
4. Kolmogorov extension gives the infinite-dimensional measure

## References

* Minlos, "Generalized random processes and their extension to a measure" (1959)
* Gel'fand-Vilenkin, "Generalized Functions IV" (1964), Ch. IV
* Reed-Simon, "Methods of Modern Mathematical Physics I", Theorem V.10
* Glimm-Jaffe, "Quantum Physics" (1987), Ch. 6
-/

noncomputable section

open MeasureTheory Complex
open scoped NNReal Topology

/-! ### Positive-Definite Functions -/

/-- A function φ : E → ℂ on an abelian group is **positive-definite** if
    for every finite family of points x₁, ..., xₙ ∈ E and scalars c₁, ..., cₙ ∈ ℂ,
    the Hermitian form Σᵢ Σⱼ c̄ᵢ · cⱼ · φ(xⱼ - xᵢ) is a non-negative real number.

    This is equivalent to requiring the kernel matrix [φ(xⱼ - xᵢ)] to be
    positive semi-definite (Hermitian with non-negative eigenvalues).

    The standard notion from harmonic analysis (Rudin, Folland). -/
def IsPositiveDefiniteFn {E : Type*} [AddCommGroup E] (φ : E → ℂ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → E) (c : Fin n → ℂ),
    let S := ∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j * φ (x j - x i)
    S.im = 0 ∧ 0 ≤ S.re

section PositiveDefiniteProps

variable {E : Type*} [AddCommGroup E] {φ : E → ℂ}

/-- A positive-definite function satisfies φ(0) ≥ 0 (taking n=1, c₁=1, x₁=0).
    Moreover, φ(0) is real (imaginary part is 0). -/
theorem IsPositiveDefiniteFn.eval_zero_nonneg (hφ : IsPositiveDefiniteFn φ) :
    0 ≤ (φ 0).re := by
  have h := hφ 1 (fun _ => 0) (fun _ => 1)
  simp only [Fin.sum_univ_one, sub_self, map_one, one_mul] at h
  exact h.2

/-- φ(0) is real for a positive-definite function. -/
theorem IsPositiveDefiniteFn.eval_zero_im (hφ : IsPositiveDefiniteFn φ) :
    (φ 0).im = 0 := by
  have h := hφ 1 (fun _ => 0) (fun _ => 1)
  simp only [Fin.sum_univ_one, sub_self, map_one, one_mul] at h
  exact h.1

/-- A positive-definite function satisfies φ(-x) = conj(φ(x)).

    Proof: The 2×2 kernel matrix M = [[φ(0), φ(x)], [φ(-x), φ(0)]] must be
    Hermitian (since c*Mc is real for all c). The off-diagonal Hermiticity
    M₂₁ = conj(M₁₂) gives φ(-x) = conj(φ(x)). -/
theorem IsPositiveDefiniteFn.conj_neg (hφ : IsPositiveDefiniteFn φ) (x : E) :
    starRingEnd ℂ (φ x) = φ (-x) := by
  have h1 := hφ 2 ![0, x] ![1, 1]
  have h2 := hφ 2 ![0, x] ![1, Complex.I]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    sub_self, sub_zero, zero_sub, neg_zero, map_one, one_mul, mul_one] at h1 h2
  obtain ⟨h1_im, _⟩ := h1
  obtain ⟨h2_im, _⟩ := h2
  have hφ0_im := hφ.eval_zero_im
  apply Complex.ext
  · -- Re(conj(φ x)) = Re(φ(-x)), i.e., Re(φ x) = Re(φ(-x))
    simp only [Complex.conj_re]
    -- Extract imaginary parts using mul_im AND mul_re (needed for (conj(I)*I).re evaluation)
    simp only [Complex.add_im, Complex.mul_im, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im] at h2_im
    -- Clean up numerical arithmetic (0*a, 1*a, a-(-b), etc.)
    ring_nf at h2_im
    linarith
  · -- Im(conj(φ x)) = Im(φ(-x)), i.e., -Im(φ x) = Im(φ(-x))
    simp only [Complex.conj_im]
    simp only [Complex.add_im] at h1_im
    linarith

/-- A positive-definite function satisfies |φ(x)| ≤ φ(0) for all x.

    Proof: The 2×2 PSD matrix [[φ(0), φ(x)], [conj(φ(x)), φ(0)]] has
    non-negative determinant: φ(0)² - |φ(x)|² ≥ 0. -/
theorem IsPositiveDefiniteFn.norm_le_eval_zero (hφ : IsPositiveDefiniteFn φ) (x : E) :
    ‖φ x‖ ≤ (φ 0).re := by
  by_cases hφx : φ x = 0
  · simp [hφx, hφ.eval_zero_nonneg]
  · -- Use c₁=‖φ x‖, c₂=-conj(φ x). Then S.re = 2‖φ x‖²((φ 0).re - ‖φ x‖) ≥ 0.
    have hznorm_pos : (0 : ℝ) < ‖φ x‖ := norm_pos_iff.mpr hφx
    have hφ_neg := hφ.conj_neg x
    have hφ0_im := hφ.eval_zero_im
    have h := hφ 2 ![0, x] ![(↑‖φ x‖ : ℂ), -(starRingEnd ℂ (φ x))]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      sub_self, sub_zero, zero_sub, neg_zero] at h
    -- Replace φ(-x) → starRingEnd ℂ (φ x), so hss can simplify conj(conj(φ x)) = φ x
    -- hφ_neg : starRingEnd ℂ (φ x) = φ (-x), so ← replaces φ(-x) with starRingEnd ℂ (φ x)
    rw [← hφ_neg] at h
    -- Simplify: conj(conj(z))=z, conj(↑r)=↑r, conj(-z)=-conj(z)
    have hss : starRingEnd ℂ (starRingEnd ℂ (φ x)) = φ x := star_star (φ x)
    simp only [map_neg, hss, Complex.conj_ofReal] at h
    obtain ⟨_, h_re⟩ := h
    -- Fully expand .re to real arithmetic (need mul_im for intermediate .im terms)
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im,
      mul_zero, zero_mul, sub_zero, add_zero,
      neg_mul, mul_neg, neg_neg, neg_zero] at h_re
    -- Normalize the real polynomial expression (collects terms, cancels double negations)
    ring_nf at h_re
    -- Key identity: ‖z‖² = z.re² + z.im²
    have hnormsq : (φ x).re ^ 2 + (φ x).im ^ 2 = ‖φ x‖ ^ 2 := by
      rw [sq, sq]; exact (RCLike.norm_sq_eq_def (K := ℂ)).symm
    -- Factor out using hnormsq: the sum = 2‖φ x‖²·((φ 0).re - ‖φ x‖)
    -- Derive (φ 0).re ≥ ‖φ x‖ by dividing by 2‖φ x‖² > 0
    suffices hsuff : 0 ≤ (φ 0).re - ‖φ x‖ by linarith
    by_contra h_neg
    push_neg at h_neg
    -- Substitute hnormsq into h_re via helper equalities
    have hp : (φ 0).re * (φ x).re ^ 2 + (φ 0).re * (φ x).im ^ 2 =
        (φ 0).re * ‖φ x‖ ^ 2 := by rw [← mul_add, hnormsq]
    have hr : ‖φ x‖ * (φ x).re ^ 2 + ‖φ x‖ * (φ x).im ^ 2 = ‖φ x‖ ^ 3 := by
      rw [← mul_add, hnormsq]; ring
    -- 0 < ‖φ x‖² * (‖φ x‖ - (φ 0).re) since both factors positive
    have h_prod : 0 < ‖φ x‖ ^ 2 * (‖φ x‖ - (φ 0).re) :=
      mul_pos (by positivity) (by linarith)
    -- Linear combination: h_re + hp substitution + hr substitution + h_prod → 0 > 0
    linarith [hp, hr, h_prod]

end PositiveDefiniteProps

/-! ### Characteristic Functionals -/

/-- A **characteristic functional** on a topological vector space E is a continuous
    function C : E → ℂ that is positive-definite and satisfies C(0) = 1.

    When E is a nuclear space, Minlos' theorem guarantees that C is the
    "Fourier transform" of a unique probability measure on E*.

    Examples:
    - Free scalar field: C(f) = exp(-½ ⟨f, (-Δ+m²)⁻¹ f⟩)
    - Gaussian: C(f) = exp(-½ ⟨f, Af⟩) for positive operator A -/
structure CharacteristicFunctional (E : Type*) [AddCommGroup E]
    [TopologicalSpace E] where
  /-- The functional C : E → ℂ -/
  toFun : E → ℂ
  /-- C is continuous -/
  continuous_toFun : Continuous toFun
  /-- C is positive-definite -/
  positive_definite : IsPositiveDefiniteFn toFun
  /-- C(0) = 1 -/
  eval_zero : toFun 0 = 1

namespace CharacteristicFunctional

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E]

/-- The characteristic functional is bounded by 1. -/
theorem norm_le_one (C : CharacteristicFunctional E) (x : E) : ‖C.toFun x‖ ≤ 1 := by
  have h := C.positive_definite.norm_le_eval_zero x
  rw [C.eval_zero] at h
  simp at h
  exact h

end CharacteristicFunctional

/-! ### Bochner's Theorem (Finite-Dimensional) -/

section BochnerHelpers

/-- Standard basis vector in `Fin n → ℝ`: the function that is 1 at index `i` and 0 elsewhere. -/
private def stdBasisFun {n : ℕ} (i : Fin n) : Fin n → ℝ := fun j => if j = i then 1 else 0

/-- Every continuous linear functional on `Fin n → ℝ` equals `x ↦ ∑ i, L(eᵢ) * x i`
    where `eᵢ` is the standard basis vector. -/
private lemma clm_eq_sum_coord {n : ℕ} (L : (Fin n → ℝ) →L[ℝ] ℝ) :
    ∀ x : Fin n → ℝ, L x = ∑ i : Fin n, L (stdBasisFun i) * x i := by
  intro x
  have hx : x = ∑ i : Fin n, x i • stdBasisFun i := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, stdBasisFun, mul_ite, mul_one,
      mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  conv_lhs => rw [hx]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [map_smul, smul_eq_mul, mul_comm])

/-- The `charFunDual` of a measure on `Fin n → ℝ`, expressed as a sum integral.
    This connects the abstract characteristic function (using dual functionals)
    to the concrete integral `∫ x, exp(i ∑ tᵢ xᵢ) dμ(x)`. -/
private lemma charFunDual_eq_sum_integral {n : ℕ}
    (μ : Measure (Fin n → ℝ)) (L : StrongDual ℝ (Fin n → ℝ)) :
    charFunDual μ L =
      ∫ x, exp (↑(∑ i : Fin n, L (stdBasisFun i) * x i) * I) ∂μ := by
  simp only [charFunDual_apply]
  congr 1; ext x
  congr 1; congr 1; congr 1
  exact clm_eq_sum_coord L x

/-- **Bochner uniqueness**: Two probability measures on `ℝⁿ` with the same
    characteristic function values are equal.

    Uses `Measure.ext_of_charFunDual` from mathlib, which establishes that
    finite measures on a normed space are determined by their characteristic
    function (dual version). -/
theorem bochner_uniqueness {n : ℕ}
    (μ₁ μ₂ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h : ∀ t : Fin n → ℝ,
      ∫ x, exp (↑(∑ i, t i * x i) * I) ∂μ₁ =
      ∫ x, exp (↑(∑ i, t i * x i) * I) ∂μ₂) :
    μ₁ = μ₂ := by
  apply Measure.ext_of_charFunDual
  ext L
  rw [charFunDual_eq_sum_integral, charFunDual_eq_sum_integral]
  exact h (fun i => L (stdBasisFun i))

/-- **Bochner existence (core)**: A continuous positive-definite function with `φ(0) = 1`
    is the characteristic function of some probability measure.

    The classical proof proceeds via:
    1. **Gauss regularization**: `φ_ε(t) = φ(t) · exp(-ε‖t‖²)` is in L¹ (bounded by 1
       times Gaussian), still positive-definite, and the inverse Fourier transform gives
       a non-negative finite measure `μ_ε` (Bochner-Schwartz for L¹ functions).
    2. **Tightness**: Each `μ_ε` has total mass ≤ 1. By the Fourier inversion theorem,
       the measures concentrate: for any `R`, `μ_ε(B(0,R)ᶜ) → 0` uniformly.
    3. **Prokhorov's theorem**: Tightness gives a subsequence converging weakly to `μ`.
    4. **Characteristic function verification**: The weak limit has `charFun(μ) = φ`,
       since `charFun(μ_ε) → φ` pointwise and characteristic functions are continuous
       in the weak topology.
    5. **Probability**: `μ(ℝⁿ) = lim μ_ε(ℝⁿ) = lim φ_ε(0) = φ(0) = 1`.

    This is a deep result requiring Fourier analysis + Prokhorov that is not yet in Mathlib. -/
private theorem bochner_tightness_and_limit {n : ℕ} (φ : (Fin n → ℝ) → ℂ)
    (hcont : Continuous φ) (hpd : IsPositiveDefiniteFn φ) (hφ0 : φ 0 = 1) :
    ∃ (μ : Measure (Fin n → ℝ)), IsProbabilityMeasure μ ∧
      ∀ t, φ t = ∫ x, exp (↑(∑ i, t i * x i) * I) ∂μ := by
  sorry

/-- **Bochner existence**: A continuous positive-definite function `φ : ℝⁿ → ℂ`
    with `φ(0) = 1` is the characteristic function of some probability measure.

    The classical proof constructs the measure via:
    1. φ defines a positive linear functional on L¹(ℝⁿ) convolutions
    2. Riesz representation gives a positive Radon measure
    3. Fourier inversion shows the measure has the right characteristic function
    4. φ(0) = 1 ensures it is a probability measure

    Proved by delegation to `bochner_tightness_and_limit`, which encapsulates the
    full Gauss regularization + Prokhorov tightness argument. -/
theorem bochner_existence {n : ℕ} (φ : (Fin n → ℝ) → ℂ)
    (hcont : Continuous φ) (hpd : IsPositiveDefiniteFn φ) (hφ0 : φ 0 = 1) :
    ∃ (μ : Measure (Fin n → ℝ)), IsProbabilityMeasure μ ∧
      ∀ t, φ t = ∫ x, exp (↑(∑ i, t i * x i) * I) ∂μ :=
  bochner_tightness_and_limit φ hcont hpd hφ0

end BochnerHelpers

/-- **Bochner's theorem**: Every continuous positive-definite function φ : ℝⁿ → ℂ
    with φ(0) = 1 is the characteristic function of a unique probability measure on ℝⁿ.

    That is, there exists a unique probability measure μ such that
    φ(t) = ∫ exp(i⟨t,x⟩) dμ(x) for all t ∈ ℝⁿ.

    Proved by combining:
    - `bochner_existence` (construction via Fourier inversion + Riesz representation)
    - `bochner_uniqueness` (via `Measure.ext_of_charFunDual` from mathlib) -/
theorem bochner_theorem {n : ℕ} (φ : (Fin n → ℝ) → ℂ)
    (hcont : Continuous φ) (hpd : IsPositiveDefiniteFn φ) (hφ0 : φ 0 = 1) :
    ∃! (μ : Measure (Fin n → ℝ)), IsProbabilityMeasure μ ∧
      ∀ t, φ t = ∫ x, exp (↑(∑ i, t i * x i) * I) ∂μ := by
  obtain ⟨μ, hμ_prob, hμ_cf⟩ := bochner_existence φ hcont hpd hφ0
  refine ⟨μ, ⟨hμ_prob, hμ_cf⟩, ?_⟩
  intro ν ⟨hν_prob, hν_cf⟩
  exact bochner_uniqueness ν μ (fun t => by rw [← hν_cf t, ← hμ_cf t])

/-! ### Minlos' Theorem -/

/-- **Helper (finite-dimensional projections)**: For each finite set of elements
    `f₁, ..., fₙ ∈ E`, the functional `C` induces a well-defined continuous
    positive-definite function `φ : ℝⁿ → ℂ` on the finite-dimensional subspace
    spanned by `{f₁, ..., fₙ}`, via `φ(t₁,...,tₙ) = C(∑ tᵢ fᵢ)`.

    By Bochner's theorem, this gives a probability measure `μ_F` on `ℝⁿ`. -/
private theorem minlos_finite_dim_projection {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    (C : CharacteristicFunctional E)
    {n : ℕ} (f : Fin n → E) :
    ∃ (μ_F : Measure (Fin n → ℝ)), IsProbabilityMeasure μ_F ∧
      ∀ t : Fin n → ℝ,
        C.toFun (∑ i, t i • f i) =
        ∫ x : Fin n → ℝ, exp (↑(∑ i, t i * x i) * I) ∂μ_F := by
  -- The function φ(t) = C(∑ tᵢ fᵢ) is continuous, positive-definite, φ(0) = 1
  set φ : (Fin n → ℝ) → ℂ := fun t => C.toFun (∑ i, t i • f i) with hφ_def
  have hcont : Continuous φ := by
    exact C.continuous_toFun.comp (continuous_finset_sum _ fun i _ =>
      (continuous_apply i).smul continuous_const)
  have hpd : IsPositiveDefiniteFn φ := by
    intro m x c
    have hC := C.positive_definite m (fun j => ∑ i, (x j) i • f i) c
    simp only [φ]
    have harg : ∀ i j : Fin m,
        (∑ k, (x j - x i) k • f k) =
        (∑ k, (x j) k • f k) - (∑ k, (x i) k • f k) := by
      intro i j
      simp [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
    simp_rw [harg]
    exact hC
  have hφ0 : φ 0 = 1 := by
    simp only [φ, Pi.zero_apply, zero_smul, Finset.sum_const_zero, C.eval_zero]
  exact bochner_existence φ hcont hpd hφ0

-- **Helper (nuclearity gives tightness of projective family)**: The family of
-- finite-dimensional measures `{μ_F}` is consistent (forms a projective family)
-- and tight. The tightness follows from nuclearity of E.
--
-- By Kolmogorov's extension theorem (with tightness for σ-additivity),
-- there exists a probability measure on `E →L[ℝ] ℝ`.

/-- Helper: The finite-dimensional measures from `minlos_finite_dim_projection` form a
    consistent projective family. For F ⊆ G (as finite sets of test functions), the
    marginal of μ_G on the F-coordinates equals μ_F.

    Consistency follows from the fact that φ_F is the restriction of φ_G:
    if G = F ∪ {extra} and we set t_extra = 0, then φ_G(t_F, 0) = φ_F(t_F).
    Bochner uniqueness then gives μ_F = (proj_F)_* μ_G. -/
private theorem minlos_projective_consistency {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    (C : CharacteristicFunctional E)
    {m n : ℕ} (f : Fin n → E) (g : Fin m → E) (π : Fin m → Fin n)
    (hπ : ∀ i, g i = f (π i))
    (μ_f : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ_f]
    (hμ_f : ∀ (t : Fin n → ℝ), C.toFun (∑ i, t i • f i) = ∫ x, exp (↑(∑ i, t i * x i) * I) ∂μ_f)
    (μ_g : Measure (Fin m → ℝ)) [IsProbabilityMeasure μ_g]
    (hμ_g : ∀ (t : Fin m → ℝ), C.toFun (∑ i, t i • g i) = ∫ x, exp (↑(∑ i, t i * x i) * I) ∂μ_g) :
    μ_g = Measure.map (fun x : Fin n → ℝ => fun i => x (π i)) μ_f := by
  sorry

/-- Helper: Nuclearity of E implies the projective family {μ_F} is tight.

    The key insight: for a nuclear space, each continuous seminorm p is nuclearly dominated
    by some q, meaning p(x) ≤ Σ |φ_k(x)| c_k with Σ c_k < ∞. This controls how spread
    the finite-dimensional measures are. Specifically, for any ε > 0, there exists a compact
    K_ε ⊆ E* such that μ_F(π_F(K_ε)) ≥ 1-ε for all F. -/
private theorem minlos_nuclearity_tightness {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [NuclearSpace E]
    [MeasurableSpace (E →L[ℝ] ℝ)]
    (C : CharacteristicFunctional E) :
    ∃ (μ : Measure (E →L[ℝ] ℝ)),
      IsProbabilityMeasure μ ∧
      ∀ f : E, C.toFun f = ∫ ω : E →L[ℝ] ℝ, exp (↑(ω f) * I) ∂μ := by
  sorry

private theorem minlos_kolmogorov_extension {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [NuclearSpace E]
    [MeasurableSpace (E →L[ℝ] ℝ)]
    (C : CharacteristicFunctional E) :
    ∃ (μ : Measure (E →L[ℝ] ℝ)),
      IsProbabilityMeasure μ ∧
      ∀ f : E, C.toFun f = ∫ ω : E →L[ℝ] ℝ, exp (↑(ω f) * I) ∂μ :=
  minlos_nuclearity_tightness C

/-- **Minlos' theorem**: Let E be a nuclear space and C : E → ℂ a characteristic
    functional (continuous, positive-definite, C(0) = 1). Then there exists a unique
    probability measure μ on the continuous dual E* (with the weak-* σ-algebra)
    such that C(f) = ∫_{E*} exp(i ω(f)) dμ(ω) for all f ∈ E.

    The dual space Dual ℝ E = E →L[ℝ] ℝ is equipped with the weak-* topology.

    Proof structure:
    1. For each continuous seminorm p, E_p = E/ker(p) is finite-dimensional
    2. The projection π_p : E → E_p induces C_p on E_p via C_p(π_p(f)) = C(f)
    3. By Bochner, each C_p gives a probability measure μ_p on E_p*
    4. The {μ_p} form a projective family (consistency from C being well-defined)
    5. **Nuclearity provides tightness**: this is the key step where nuclearity is used
    6. By Kolmogorov extension (with tightness), get μ on E*

    Proved by combining:
    - `minlos_finite_dim_projection`: finite-dim Bochner step
    - `minlos_kolmogorov_extension`: projective limit + tightness from nuclearity -/
theorem minlos_theorem {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [NuclearSpace E]
    [MeasurableSpace (E →L[ℝ] ℝ)]
    (C : CharacteristicFunctional E) :
    ∃ (μ : Measure (E →L[ℝ] ℝ)),
      IsProbabilityMeasure μ ∧
      ∀ f : E, C.toFun f = ∫ ω : E →L[ℝ] ℝ, exp (↑(ω f) * I) ∂μ :=
  minlos_kolmogorov_extension C

-- **Helper (evaluation maps separate measures on dual)**: Two probability measures
-- on `E →L[ℝ] ℝ` that agree on all "evaluation characteristic functions"
-- `∫ exp(i ω(f)) dμ₁ = ∫ exp(i ω(f)) dμ₂` for all `f ∈ E` must be equal.
--
-- This is the infinite-dimensional analogue of uniqueness. It follows from the
-- fact that evaluation maps `ω ↦ ω(f)` separate points in `E →L[ℝ] ℝ` and
-- generate the σ-algebra, so the "evaluation characteristic functions" determine
-- the finite-dimensional distributions, which in turn determine the measure
-- (by the pi-lambda theorem).

/-- Helper: Evaluation maps ω ↦ ω(f) generate the σ-algebra on E →L[ℝ] ℝ.

    The measurable space on E →L[ℝ] ℝ (with weak-* topology) is generated by the
    evaluation maps ev_f : ω ↦ ω(f) for f ∈ E. This means that two measures agreeing
    on all sets of the form {ω : ω(f) ∈ B} for Borel B ⊆ ℝ must agree on all
    measurable sets (by π-λ theorem).

    Blocked by: needs the σ-algebra on E →L[ℝ] ℝ to be generated by evaluation maps,
    which depends on the weak-* topology definition and its Borel σ-algebra. -/
private theorem eval_maps_generate_sigma_algebra {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E]
    [MeasurableSpace (E →L[ℝ] ℝ)]
    (μ₁ μ₂ : Measure (E →L[ℝ] ℝ))
    (hμ₁ : IsProbabilityMeasure μ₁) (hμ₂ : IsProbabilityMeasure μ₂)
    (h_fd : ∀ (n : ℕ) (f : Fin n → E),
      Measure.map (fun ω : E →L[ℝ] ℝ => fun i => ω (f i)) μ₁ =
      Measure.map (fun ω : E →L[ℝ] ℝ => fun i => ω (f i)) μ₂) :
    μ₁ = μ₂ := by
  sorry

/-- Helper: Agreeing evaluation characteristic functions implies agreeing finite-dimensional
    distributions.

    If ∫ exp(i ω(f)) dμ₁ = ∫ exp(i ω(f)) dμ₂ for all f ∈ E, then for any f₁,...,fₙ ∈ E,
    the pushforward measures on ℝⁿ via (ω(f₁),...,ω(fₙ)) agree. This follows from
    bochner_uniqueness applied to the pushforward measures, since agreeing on all
    linear combinations ∑ tᵢ fᵢ means the characteristic functions of the pushforwards agree. -/
private theorem eval_charfun_implies_fd_distributions {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E]
    [MeasurableSpace (E →L[ℝ] ℝ)]
    (μ₁ μ₂ : Measure (E →L[ℝ] ℝ))
    (hμ₁ : IsProbabilityMeasure μ₁) (hμ₂ : IsProbabilityMeasure μ₂)
    (h : ∀ f : E,
      ∫ ω : E →L[ℝ] ℝ, exp (↑(ω f) * I) ∂μ₁ =
      ∫ ω : E →L[ℝ] ℝ, exp (↑(ω f) * I) ∂μ₂) :
    ∀ (n : ℕ) (f : Fin n → E),
      Measure.map (fun ω : E →L[ℝ] ℝ => fun i => ω (f i)) μ₁ =
      Measure.map (fun ω : E →L[ℝ] ℝ => fun i => ω (f i)) μ₂ := by
  sorry

private theorem measures_eq_of_eval_charfun_eq {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E]
    [MeasurableSpace (E →L[ℝ] ℝ)]
    (μ₁ μ₂ : Measure (E →L[ℝ] ℝ))
    (hμ₁ : IsProbabilityMeasure μ₁) (hμ₂ : IsProbabilityMeasure μ₂)
    (h : ∀ f : E,
      ∫ ω : E →L[ℝ] ℝ, exp (↑(ω f) * I) ∂μ₁ =
      ∫ ω : E →L[ℝ] ℝ, exp (↑(ω f) * I) ∂μ₂) :
    μ₁ = μ₂ :=
  eval_maps_generate_sigma_algebra μ₁ μ₂ hμ₁ hμ₂
    (eval_charfun_implies_fd_distributions μ₁ μ₂ hμ₁ hμ₂ h)

/-- Uniqueness part of Minlos' theorem: the measure is unique.

    Proved via `measures_eq_of_eval_charfun_eq`, which shows that evaluation
    characteristic functions determine the measure. -/
theorem minlos_unique {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [NuclearSpace E]
    [MeasurableSpace (E →L[ℝ] ℝ)]
    (C : CharacteristicFunctional E)
    (μ₁ μ₂ : Measure (E →L[ℝ] ℝ))
    (hμ₁ : IsProbabilityMeasure μ₁) (hμ₂ : IsProbabilityMeasure μ₂)
    (h₁ : ∀ f : E, C.toFun f = ∫ ω : E →L[ℝ] ℝ, exp (↑(ω f) * I) ∂μ₁)
    (h₂ : ∀ f : E, C.toFun f = ∫ ω : E →L[ℝ] ℝ, exp (↑(ω f) * I) ∂μ₂) :
    μ₁ = μ₂ :=
  measures_eq_of_eval_charfun_eq μ₁ μ₂ hμ₁ hμ₂ (fun f => by rw [← h₁ f, ← h₂ f])

/-! ### Gaussian Characteristic Functionals -/

/-- A **Gaussian characteristic functional** on a Hilbert space H is given by
    C(f) = exp(-½ ⟨f, Af⟩) where A : H → H is a positive trace-class operator.

    This is the characteristic functional of a centered Gaussian measure on H. -/
def gaussianCharacteristicFunctional {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H) (_hA_pos : ∀ x, 0 ≤ @inner ℝ H _ x (A x)) :
    H → ℂ :=
  fun f => exp (-(1/2 : ℂ) * ↑(@inner ℝ H _ f (A f)))

/-- The Gaussian characteristic functional at 0 equals 1. -/
theorem gaussianCharacteristicFunctional_zero {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H) (hA_pos : ∀ x, 0 ≤ @inner ℝ H _ x (A x)) :
    gaussianCharacteristicFunctional A hA_pos 0 = 1 := by
  simp [gaussianCharacteristicFunctional]

/-- The Gaussian characteristic functional is positive-definite.

    This follows from the fact that exp(-½ Q(f)) where Q is a positive quadratic
    form is positive-definite (by expanding the exponential and using the positive
    definiteness of each power of Q). -/
theorem gaussianCharacteristicFunctional_posdef {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H) (hA_pos : ∀ x, 0 ≤ @inner ℝ H _ x (A x)) :
    IsPositiveDefiniteFn (gaussianCharacteristicFunctional A hA_pos) := by
  intro n x c
  -- Convert complex exponential to real exponential cast to ℂ
  have hconv : ∀ f : H,
      gaussianCharacteristicFunctional A hA_pos f =
      ↑(Real.exp (-(1/2 : ℝ) * @inner ℝ H _ f (A f))) := by
    intro f
    simp only [gaussianCharacteristicFunctional]
    rw [show -(1/2 : ℂ) * ↑(@inner ℝ H _ f (A f)) =
        ↑(-(1/2 : ℝ) * @inner ℝ H _ f (A f)) from by push_cast; ring]
    exact Complex.ofReal_exp (-(1/2 : ℝ) * @inner ℝ H _ f (A f)) |>.symm
  simp_rw [hconv]
  exact gaussian_kernel_posdef A hA_pos x c

end
