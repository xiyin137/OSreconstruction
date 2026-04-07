import OSReconstruction.SCV.LaplaceHolomorphic

/-!
# Positive-Definite Kernels on `(0, ∞)`

This file isolates the semigroup-positive-definite kernel notion relevant to
the OS II Euclidean semigroup argument.

For a scalar kernel `φ : ℝ → ℂ`, positivity on the additive semigroup
`(0, ∞)` means that for every finite family of positive times `τᵢ > 0`, the
matrix `φ(τᵢ + τⱼ)` is positive semidefinite.

The deep missing theorem is the Bernstein-Widder / semigroup Bochner
representation theorem, which would identify such kernels with Laplace
transforms of finite positive measures on `[0, ∞)`.

Important caveat: the semigroup-positive-definite condition by itself is weaker
than a positive-support Laplace representation. The theorem
`exp_mul_isSemigroupPDKernel` below shows that `t ↦ exp (a t)` is
semigroup-positive-definite for every real `a`, so any eventual positive-support
representation theorem must use additional positivity/monotonicity input beyond
the bare Hankel-PSD condition. This file only contains the already proved
algebraic side of that story.
-/

open MeasureTheory Complex Set Filter Finset BigOperators
open scoped Topology

noncomputable section

namespace SCV

/-- Positive-definite kernels on the additive semigroup `(0, ∞)`.

For the additive semigroup with identity involution, the quadratic form must be
an actual nonnegative real number, not merely have nonnegative real part. -/
def IsSemigroupPDKernel (φ : ℝ → ℂ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (c : ι → ℂ) (τ : ι → Set.Ioi (0 : ℝ)),
    let q := ∑ i : ι, ∑ j : ι, starRingEnd ℂ (c i) * c j * φ ((τ i : ℝ) + (τ j : ℝ))
    q.im = 0 ∧ 0 ≤ q.re

/-- Diagonal entries of a semigroup-positive-definite kernel have nonnegative real part. -/
theorem pd_diagonal_nonneg (φ : ℝ → ℂ) (hPD : IsSemigroupPDKernel φ)
    (t : ℝ) (ht : 0 < t) :
    0 ≤ (φ (2 * t)).re := by
  have h := hPD (Fin 1) (fun _ => 1) (fun _ => ⟨t, ht⟩)
  simp only [Fin.sum_univ_one, map_one, one_mul] at h
  convert h.2 using 2
  ring_nf

/-- Diagonal entries of a semigroup-positive-definite kernel are real. -/
theorem pd_diagonal_im_zero (φ : ℝ → ℂ) (hPD : IsSemigroupPDKernel φ)
    (t : ℝ) (ht : 0 < t) :
    (φ (2 * t)).im = 0 := by
  have h := hPD (Fin 1) (fun _ => 1) (fun _ => ⟨t, ht⟩)
  simp only [Fin.sum_univ_one, map_one, one_mul] at h
  convert h.1 using 2
  ring_nf

/-- Off-diagonal Hankel entries of a semigroup-positive-definite kernel are real. -/
theorem pd_pair_im_zero (φ : ℝ → ℂ) (hPD : IsSemigroupPDKernel φ)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    (φ (s + t)).im = 0 := by
  have h := hPD (Fin 2) ![1, (-1 : ℂ)] ![⟨s, hs⟩, ⟨t, ht⟩]
  have hsdiag := pd_diagonal_im_zero φ hPD s hs
  have htdiag := pd_diagonal_im_zero φ hPD t ht
  have him := h.1
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    map_one, one_mul, mul_one, map_neg, neg_mul, mul_neg, neg_neg] at him
  rw [show s + s = 2 * s by ring, show t + t = 2 * t by ring,
    show t + s = s + t by ring] at him
  simp only [Complex.add_im, Complex.neg_im, hsdiag, htdiag, add_zero] at him
  linarith

/-- The `2 × 2` quadratic form inequality for semigroup-positive-definite kernels. -/
theorem pd_quadratic_nonneg (φ : ℝ → ℂ) (hPD : IsSemigroupPDKernel φ)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (r : ℝ) :
    0 ≤ (φ (2 * s)).re - 2 * r * (φ (s + t)).re + r ^ 2 * (φ (2 * t)).re := by
  have h := hPD (Fin 2) ![1, -(r : ℂ)] ![⟨s, hs⟩, ⟨t, ht⟩]
  have htdiag := pd_diagonal_im_zero φ hPD t ht
  have hst := pd_pair_im_zero φ hPD s t hs ht
  have hre := h.2
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    map_one, one_mul, mul_one, map_neg, neg_mul, mul_neg, neg_neg] at hre
  rw [show s + s = 2 * s by ring, show t + t = 2 * t by ring,
    show t + s = s + t by ring] at hre
  simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, htdiag, hst, mul_zero, sub_zero, add_assoc,
    add_left_comm] at hre
  have hre' :
      0 ≤
        -(r * (φ (s + t)).re) +
          ((φ (2 * s)).re + (-(r * (φ (s + t)).re) + r * r * (φ (2 * t)).re)) := by
    simpa using hre
  nlinarith [hre']

/-- Semigroup Cauchy-Schwarz for Hankel kernels on `(0, ∞)`. -/
theorem pd_cauchy_schwarz (φ : ℝ → ℂ) (hPD : IsSemigroupPDKernel φ)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    ((φ (s + t)).re) ^ 2 ≤ (φ (2 * s)).re * (φ (2 * t)).re := by
  have hd := pd_diagonal_nonneg φ hPD t ht
  have hQ := pd_quadratic_nonneg φ hPD s t hs ht
  by_cases hc : (φ (2 * t)).re = 0
  · have hst : (φ (s + t)).re = 0 := by
      by_contra hne
      have hQ' := hQ (((φ (2 * s)).re + 1) / (2 * (φ (s + t)).re))
      simp only [hc, mul_zero, add_zero] at hQ'
      have hcalc :
          2 * (((φ (2 * s)).re + 1) / (2 * (φ (s + t)).re)) * (φ (s + t)).re =
            (φ (2 * s)).re + 1 := by
        field_simp [hne]
      linarith
    simp [hst, hc]
  · have hcpos : 0 < (φ (2 * t)).re := lt_of_le_of_ne hd (Ne.symm hc)
    have hQ' := hQ (((φ (s + t)).re) / ((φ (2 * t)).re))
    have h2t2_pos : (0 : ℝ) < ((φ (2 * t)).re) ^ 2 := by positivity
    suffices h :
        0 ≤ (φ (2 * s)).re * (φ (2 * t)).re - ((φ (s + t)).re) ^ 2 by
      linarith
    have key :
        0 ≤ ((φ (2 * s)).re - 2 * (((φ (s + t)).re) / ((φ (2 * t)).re)) * (φ (s + t)).re +
          (((φ (s + t)).re) / ((φ (2 * t)).re)) ^ 2 * (φ (2 * t)).re) *
            ((φ (2 * t)).re) ^ 2 :=
      mul_nonneg hQ' (le_of_lt h2t2_pos)
    have hcalc :
        ((φ (2 * s)).re - 2 * (((φ (s + t)).re) / ((φ (2 * t)).re)) * (φ (s + t)).re +
            (((φ (s + t)).re) / ((φ (2 * t)).re)) ^ 2 * (φ (2 * t)).re) *
            ((φ (2 * t)).re) ^ 2 =
          ((φ (2 * s)).re * (φ (2 * t)).re - ((φ (s + t)).re) ^ 2) * (φ (2 * t)).re := by
      field_simp [hc]
      ring
    rw [hcalc] at key
    exact nonneg_of_mul_nonneg_left key hcpos

/-- A semigroup-positive-definite kernel is real-valued on `(0, ∞)`. -/
theorem pd_im_zero (φ : ℝ → ℂ) (hPD : IsSemigroupPDKernel φ)
    (t : ℝ) (ht : 0 < t) :
    (φ t).im = 0 := by
  simpa [show t / 2 + t / 2 = t by ring] using
    pd_pair_im_zero φ hPD (t / 2) (t / 2) (half_pos ht) (half_pos ht)

/-- A semigroup-positive-definite kernel has nonnegative values on `(0, ∞)`. -/
theorem pd_re_nonneg (φ : ℝ → ℂ) (hPD : IsSemigroupPDKernel φ)
    (t : ℝ) (ht : 0 < t) :
    0 ≤ (φ t).re := by
  simpa [show 2 * (t / 2) = t by ring] using
    pd_diagonal_nonneg φ hPD (t / 2) (half_pos ht)

/-- A semigroup-positive-definite kernel is represented by its real part on `(0, ∞)`. -/
theorem pd_eq_ofReal_re (φ : ℝ → ℂ) (hPD : IsSemigroupPDKernel φ)
    (t : ℝ) (ht : 0 < t) :
    φ t = ↑((φ t).re) := by
  apply Complex.ext <;> simp [pd_im_zero φ hPD t ht]

/-- Restricting a semigroup-positive-definite kernel to an arithmetic progression
produces a positive Hankel sequence. -/
theorem pd_arithmetic_progression (φ : ℝ → ℂ) (hPD : IsSemigroupPDKernel φ)
    {n : ℕ} (c : Fin n → ℂ) {h : ℝ} (hh : 0 < h) :
    let q := ∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * φ ((((i : ℕ) + (j : ℕ) + 2 : ℕ) : ℝ) * h)
    q.im = 0 ∧ 0 ≤ q.re := by
  let τ : Fin n → Set.Ioi (0 : ℝ) := fun i =>
    ⟨((((i : ℕ) + 1 : ℕ) : ℝ) * h), by
      have hi : (0 : ℝ) < (((i : ℕ) + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_pos (i : ℕ)
      exact mul_pos hi hh⟩
  have hq := hPD (Fin n) c τ
  have hsum : ∀ i j : Fin n,
      ((τ i : ℝ) + (τ j : ℝ)) = ((((i : ℕ) + (j : ℕ) + 2 : ℕ) : ℝ) * h) := by
    intro i j
    dsimp [τ]
    have hcast :
        ((((i : ℕ) + (j : ℕ) + 2 : ℕ) : ℝ)) =
          ((((i : ℕ) + 1 : ℕ) : ℝ) + (((j : ℕ) + 1 : ℕ) : ℝ)) := by
      norm_num [Nat.cast_add, add_assoc, add_left_comm, add_comm]
    rw [hcast]
    ring
  simpa [hsum] using hq

/-- The standard factorization of a rank-one positive semidefinite kernel matrix. -/
theorem pd_sum_eq_norm_sq {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (e : ι → ℂ) :
    (∑ i, ∑ j, starRingEnd ℂ (c i * e i) * (c j * e j)) =
      ↑(‖∑ i, c i * e i‖ ^ 2) := by
  have hrw : (↑(‖∑ i, c i * e i‖ ^ 2) : ℂ) =
      starRingEnd ℂ (∑ i, c i * e i) * (∑ i, c i * e i) := by
    have h1 := @Complex.normSq_eq_conj_mul_self (∑ i, c i * e i)
    have h2 := Complex.normSq_eq_norm_sq (∑ i, c i * e i)
    rw [h2] at h1
    exact_mod_cast h1
  rw [hrw, map_sum, Finset.sum_mul]
  congr 1
  ext i
  rw [Finset.mul_sum]

/-- Exponential kernels `t ↦ exp(a t)` are semigroup-positive-definite. -/
theorem exp_mul_isSemigroupPDKernel (a : ℝ) :
    IsSemigroupPDKernel (fun t => ↑(Real.exp (a * t))) := by
  intro ι _ _ c τ
  have hexp_split : ∀ i j,
      (↑(Real.exp (a * ((τ i : ℝ) + (τ j : ℝ))) ) : ℂ) =
        (↑(Real.exp (a * (τ i : ℝ))) : ℂ) * ↑(Real.exp (a * (τ j : ℝ))) := by
    intro i j
    rw [show a * ((τ i : ℝ) + (τ j : ℝ)) = a * (τ i : ℝ) + a * (τ j : ℝ) by ring,
      Real.exp_add]
    norm_num
  simp_rw [hexp_split]
  have hconj_real : ∀ i, starRingEnd ℂ (↑(Real.exp (a * (τ i : ℝ))) : ℂ) =
      ↑(Real.exp (a * (τ i : ℝ))) := fun i => Complex.conj_ofReal _
  have hterm : ∀ i j,
      starRingEnd ℂ (c i) * c j *
          ((↑(Real.exp (a * (τ i : ℝ))) : ℂ) * ↑(Real.exp (a * (τ j : ℝ)))) =
        starRingEnd ℂ (c i * ↑(Real.exp (a * (τ i : ℝ)))) *
          (c j * ↑(Real.exp (a * (τ j : ℝ)))) := by
    intro i j
    rw [map_mul, hconj_real]
    ring
  simp_rw [hterm]
  rw [pd_sum_eq_norm_sq]
  constructor
  · rw [Complex.ofReal_im]
  · rw [Complex.ofReal_re]
    exact sq_nonneg _

/-- The Laplace-transform kernel integrand is a nonnegative real scalar. -/
theorem laplace_pd_integrand_eq_norm_sq {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (τ : ι → Set.Ioi (0 : ℝ)) (u : ℝ) :
    (∑ i, ∑ j,
      starRingEnd ℂ (c i) * c j * exp (-(↑((τ i : ℝ) + (τ j : ℝ)) : ℂ) * ↑u)) =
      ↑(‖∑ i, c i * (↑(Real.exp (-((τ i : ℝ)) * u)) : ℂ)‖ ^ 2) := by
  have hexp_split : ∀ i j,
      exp (-(↑((τ i : ℝ) + (τ j : ℝ)) : ℂ) * (↑u : ℂ)) =
        exp (-(↑(τ i : ℝ) : ℂ) * ↑u) * exp (-(↑(τ j : ℝ) : ℂ) * ↑u) := by
    intro i j
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hexp_split]
  have hexp_real : ∀ i, exp (-(↑(τ i : ℝ) : ℂ) * (↑u : ℂ)) =
      ↑(Real.exp (-((τ i : ℝ)) * u)) := by
    intro i
    rw [← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_exp]
  simp_rw [hexp_real]
  have hconj_real : ∀ i, starRingEnd ℂ (↑(Real.exp (-((τ i : ℝ)) * u)) : ℂ) =
      ↑(Real.exp (-((τ i : ℝ)) * u)) := fun i => Complex.conj_ofReal _
  have hterm : ∀ i j,
      starRingEnd ℂ (c i) * c j *
          ((↑(Real.exp (-((τ i : ℝ)) * u)) : ℂ) * ↑(Real.exp (-((τ j : ℝ)) * u))) =
        starRingEnd ℂ (c i * ↑(Real.exp (-((τ i : ℝ)) * u))) *
          (c j * ↑(Real.exp (-((τ j : ℝ)) * u))) := by
    intro i j
    rw [map_mul, hconj_real]
    ring
  simp_rw [hterm]
  rw [pd_sum_eq_norm_sq]

/-- Pointwise nonnegativity of the Laplace-transform kernel integrand. -/
theorem laplace_pd_integrand_nonneg {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (τ : ι → Set.Ioi (0 : ℝ)) (u : ℝ) (_hu : 0 ≤ u) :
    0 ≤ (∑ i, ∑ j,
      starRingEnd ℂ (c i) * c j * exp (-(↑((τ i : ℝ) + (τ j : ℝ)) : ℂ) * ↑u)).re := by
  rw [laplace_pd_integrand_eq_norm_sq]
  rw [Complex.ofReal_re]
  exact sq_nonneg _

/-- Pointwise reality of the Laplace-transform kernel integrand. -/
theorem laplace_pd_integrand_im_zero {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (τ : ι → Set.Ioi (0 : ℝ)) (u : ℝ) :
    (∑ i, ∑ j,
      starRingEnd ℂ (c i) * c j * exp (-(↑((τ i : ℝ) + (τ j : ℝ)) : ℂ) * ↑u)).im = 0 := by
  rw [laplace_pd_integrand_eq_norm_sq]
  exact Complex.ofReal_im _

/-- A positive-support Laplace transform is uniformly bounded on `(0, ∞)` by the
total mass of the measure. -/
theorem norm_laplaceTransform_le_measure_univ (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : μ (Iio 0) = 0) (t : ℝ) (ht : 0 < t) :
    ‖∫ u, exp (-(↑t : ℂ) * (↑u : ℂ)) ∂μ‖ ≤ (μ Set.univ).toReal := by
  have hmeas :
      AEStronglyMeasurable (fun u : ℝ => exp (-(↑t : ℂ) * (↑u : ℂ))) μ := by
    have hcont :
        Continuous (fun u : ℝ => exp ((-(↑t : ℂ)) * (↑u : ℂ))) :=
      Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
    have hcont' :
        Continuous (fun u : ℝ => exp (-(↑t : ℂ) * (↑u : ℂ))) := by
      simpa [neg_mul] using hcont
    exact hcont'.aestronglyMeasurable
  have hInt :
      Integrable (fun u : ℝ => exp (-(↑t : ℂ) * (↑u : ℂ))) μ := by
    refine (integrable_const (1 : ℝ)).mono' hmeas ?_
    have hae := SCV.exp_neg_mul_ae_dominated μ hsupp (t : ℂ) (by simpa using ht)
    filter_upwards [hae] with u hu
    exact hu
  calc
    ‖∫ u, exp (-(↑t : ℂ) * (↑u : ℂ)) ∂μ‖ ≤
        ∫ u, ‖exp (-(↑t : ℂ) * (↑u : ℂ))‖ ∂μ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ _u, (1 : ℝ) ∂μ := by
      exact MeasureTheory.integral_mono_ae hInt.norm (integrable_const (1 : ℝ))
        (SCV.exp_neg_mul_ae_dominated μ hsupp (t : ℂ) (by simpa using ht))
    _ = μ.real Set.univ := by
      simp [MeasureTheory.integral_const]
    _ = (μ Set.univ).toReal := by
      rw [MeasureTheory.measureReal_def]

/-- The semigroup-positive-definite kernel `t ↦ exp(a t)` with `a > 0` cannot be
represented as a positive-support Laplace transform. -/
theorem exp_mul_not_laplaceTransform_of_nonnegSupport (a : ℝ) (ha : 0 < a) :
    ¬ ∃ (μ : Measure ℝ) (_ : IsFiniteMeasure μ), μ (Iio 0) = 0 ∧
      ∀ t, 0 < t →
        (↑(Real.exp (a * t)) : ℂ) =
          ∫ u, exp (-(↑t : ℂ) * (↑u : ℂ)) ∂μ := by
  intro h
  rcases h with ⟨μ, hfin, hsupp, hrepr⟩
  letI : IsFiniteMeasure μ := hfin
  let M : ℝ := (μ Set.univ).toReal
  let t : ℝ := (Real.log (M + 1) + 1) / a
  have hMnonneg : 0 ≤ M := by
    exact ENNReal.toReal_nonneg
  have ht : 0 < t := by
    have hM1 : 1 ≤ M + 1 := by linarith
    have hlog : 0 ≤ Real.log (M + 1) := Real.log_nonneg hM1
    have hnum : 0 < Real.log (M + 1) + 1 := by linarith
    exact div_pos hnum ha
  have hbound := norm_laplaceTransform_le_measure_univ μ hsupp t ht
  have hrepr_t := hrepr t ht
  have hnorm :
      Real.exp (a * t) ≤ M := by
    have hrepr_t' : Complex.exp (((a * t : ℝ)) : ℂ) =
        ∫ u, exp (-(↑t : ℂ) * (↑u : ℂ)) ∂μ := by
      simpa using hrepr_t
    calc
      Real.exp (a * t) = ‖Complex.exp ((a * t : ℝ) : ℂ)‖ := by
        rw [Complex.norm_exp]
        simp
      _ = ‖∫ u, exp (-(↑t : ℂ) * (↑u : ℂ)) ∂μ‖ := by rw [hrepr_t']
      _ ≤ M := hbound
  have htcalc : a * t = Real.log (M + 1) + 1 := by
    rw [show t = (Real.log (M + 1) + 1) / a by rfl]
    field_simp [ha.ne']
  have hM1pos : 0 < M + 1 := by linarith
  have hgrow : M < Real.exp (a * t) := by
    calc
      M < M + 1 := by linarith
      _ = Real.exp (Real.log (M + 1)) := by rw [Real.exp_log hM1pos]
      _ < Real.exp (Real.log (M + 1) + 1) := by
        apply Real.exp_lt_exp.mpr
        linarith
      _ = Real.exp (a * t) := by rw [htcalc]
  linarith

/-- Bare semigroup-positive-definiteness does not force a positive-support Laplace
representation. -/
theorem exists_semigroupPDKernel_not_laplaceTransform_of_nonnegSupport :
    ∃ φ : ℝ → ℂ, IsSemigroupPDKernel φ ∧
      ¬ ∃ (μ : Measure ℝ) (_ : IsFiniteMeasure μ), μ (Iio 0) = 0 ∧
        ∀ t, 0 < t → φ t = ∫ u, exp (-(↑t : ℂ) * (↑u : ℂ)) ∂μ := by
  refine ⟨fun t => ↑(Real.exp (1 * t)), exp_mul_isSemigroupPDKernel 1, ?_⟩
  simpa [one_mul] using exp_mul_not_laplaceTransform_of_nonnegSupport 1 zero_lt_one

/-- The Laplace transform of a finite measure supported in `[0, ∞)` is a
semigroup-positive-definite kernel on `(0, ∞)`. -/
theorem laplaceTransform_isSemigroupPDKernel (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : μ (Iio 0) = 0) :
    IsSemigroupPDKernel (fun t => ∫ u, exp (-(↑t : ℂ) * (↑u : ℂ)) ∂μ) := by
  intro ι _ _ c τ
  have hint : ∀ i j, Integrable (fun u : ℝ =>
      starRingEnd ℂ (c i) * c j * exp (-(↑((τ i : ℝ) + (τ j : ℝ)) : ℂ) * (↑u : ℂ))) μ := by
    intro i j
    have hτpos : 0 < ((τ i : ℝ) + (τ j : ℝ)) := add_pos (τ i).2 (τ j).2
    have hbase :
        Integrable (fun u : ℝ => exp (-(↑((τ i : ℝ) + (τ j : ℝ)) : ℂ) * (↑u : ℂ))) μ := by
      have hmeas :
          AEStronglyMeasurable
            (fun u : ℝ => exp (-(↑((τ i : ℝ) + (τ j : ℝ)) : ℂ) * (↑u : ℂ))) μ := by
        have hcont :
            Continuous (fun u : ℝ => exp ((-(↑((τ i : ℝ) + (τ j : ℝ)) : ℂ)) * (↑u : ℂ))) :=
          Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
        have hcont' :
            Continuous (fun u : ℝ => exp (-(↑((τ i : ℝ) + (τ j : ℝ)) : ℂ) * (↑u : ℂ))) := by
          simpa [neg_mul] using hcont
        exact hcont'.aestronglyMeasurable
      refine (integrable_const (1 : ℝ)).mono' hmeas ?_
      have hae : ∀ᵐ (u : ℝ) ∂μ, 0 ≤ u := by
        rw [ae_iff]
        simp only [not_le]
        exact hsupp
      filter_upwards [hae] with u hu
      rw [Complex.norm_exp]
      apply Real.exp_le_one_iff.mpr
      show (-(↑((τ i : ℝ) + (τ j : ℝ)) : ℂ) * (↑u : ℂ)).re ≤ 0
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im]
      nlinarith [le_of_lt hτpos, hu]
    simpa [mul_assoc] using (hbase.const_mul (c j)).const_mul (starRingEnd ℂ (c i))
  have hrepr :
      (∑ i : ι, ∑ j : ι,
        starRingEnd ℂ (c i) * c j * (∫ u, exp (-(↑((τ i : ℝ) + (τ j : ℝ)) : ℂ) * (↑u : ℂ)) ∂μ)) =
      ∫ u : ℝ, ∑ i : ι, ∑ j : ι,
        starRingEnd ℂ (c i) * c j * exp (-(↑((τ i : ℝ) + (τ j : ℝ)) : ℂ) * (↑u : ℂ)) ∂μ := by
    calc
      (∑ i : ι, ∑ j : ι,
          starRingEnd ℂ (c i) * c j *
            (∫ u, exp (-(↑((τ i : ℝ) + (τ j : ℝ)) : ℂ) * (↑u : ℂ)) ∂μ)) =
          ∑ i : ι, ∑ j : ι,
            ∫ u, starRingEnd ℂ (c i) * c j *
              exp (-(↑((τ i : ℝ) + (τ j : ℝ)) : ℂ) * (↑u : ℂ)) ∂μ := by
        congr 1 with i; congr 1 with j; exact (MeasureTheory.integral_const_mul _ _).symm
      _ = ∑ i : ι, ∫ u : ℝ, ∑ j : ι,
            starRingEnd ℂ (c i) * c j *
              exp (-(↑((τ i : ℝ) + (τ j : ℝ)) : ℂ) * (↑u : ℂ)) ∂μ := by
        congr with i
        rw [MeasureTheory.integral_finset_sum]
        intro j hj
        exact hint i j
      _ = ∫ u : ℝ, ∑ i : ι, ∑ j : ι,
            starRingEnd ℂ (c i) * c j *
              exp (-(↑((τ i : ℝ) + (τ j : ℝ)) : ℂ) * (↑u : ℂ)) ∂μ := by
        rw [MeasureTheory.integral_finset_sum]
        intro i hi
        exact integrable_finset_sum _ (fun j _ => hint i j)
  have hnonneg : 0 ≤
      ∫ u : ℝ,
        (∑ i : ι, ∑ j : ι,
          starRingEnd ℂ (c i) * c j * exp (-(↑((τ i : ℝ) + (τ j : ℝ)) : ℂ) * (↑u : ℂ))).re ∂μ := by
    apply MeasureTheory.integral_nonneg_of_ae
    have hae : ∀ᵐ (u : ℝ) ∂μ, 0 ≤ u := by
      rw [ae_iff]
      simp only [not_le]
      exact hsupp
    filter_upwards [hae] with u hu
    exact laplace_pd_integrand_nonneg c τ u hu
  have hintsum :
      Integrable
        (fun u : ℝ =>
          ∑ i : ι, ∑ j : ι,
            starRingEnd ℂ (c i) * c j *
              exp (-(↑((τ i : ℝ) + (τ j : ℝ)) : ℂ) * (↑u : ℂ))) μ := by
    exact integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hint i j))
  have hsumre :
      (∑ i : ι, ∑ j : ι,
        starRingEnd ℂ (c i) * c j *
          (∫ u, exp (-(↑((τ i : ℝ) + (τ j : ℝ)) : ℂ) * (↑u : ℂ)) ∂μ)).re =
      ∫ u : ℝ,
        (∑ i : ι, ∑ j : ι,
          starRingEnd ℂ (c i) * c j *
            exp (-(↑((τ i : ℝ) + (τ j : ℝ)) : ℂ) * (↑u : ℂ))).re ∂μ := by
    calc
      (∑ i : ι, ∑ j : ι,
        starRingEnd ℂ (c i) * c j *
          (∫ u, exp (-(↑((τ i : ℝ) + (τ j : ℝ)) : ℂ) * (↑u : ℂ)) ∂μ)).re
          = (∫ u : ℝ, ∑ i : ι, ∑ j : ι,
              starRingEnd ℂ (c i) * c j *
                exp (-(↑((τ i : ℝ) + (τ j : ℝ)) : ℂ) * (↑u : ℂ)) ∂μ).re := by
          rw [hrepr]
      _ = ∫ u : ℝ,
            (∑ i : ι, ∑ j : ι,
              starRingEnd ℂ (c i) * c j *
                exp (-(↑((τ i : ℝ) + (τ j : ℝ)) : ℂ) * (↑u : ℂ))).re ∂μ := by
          simpa using (integral_re hintsum).symm
  have hsumim :
      (∑ i : ι, ∑ j : ι,
        starRingEnd ℂ (c i) * c j *
          (∫ u, exp (-(↑((τ i : ℝ) + (τ j : ℝ)) : ℂ) * (↑u : ℂ)) ∂μ)).im =
      ∫ u : ℝ,
        (∑ i : ι, ∑ j : ι,
          starRingEnd ℂ (c i) * c j *
            exp (-(↑((τ i : ℝ) + (τ j : ℝ)) : ℂ) * (↑u : ℂ))).im ∂μ := by
    calc
      (∑ i : ι, ∑ j : ι,
        starRingEnd ℂ (c i) * c j *
          (∫ u, exp (-(↑((τ i : ℝ) + (τ j : ℝ)) : ℂ) * (↑u : ℂ)) ∂μ)).im
          = (∫ u : ℝ, ∑ i : ι, ∑ j : ι,
              starRingEnd ℂ (c i) * c j *
                exp (-(↑((τ i : ℝ) + (τ j : ℝ)) : ℂ) * (↑u : ℂ)) ∂μ).im := by
          rw [hrepr]
      _ = ∫ u : ℝ,
            (∑ i : ι, ∑ j : ι,
              starRingEnd ℂ (c i) * c j *
                exp (-(↑((τ i : ℝ) + (τ j : ℝ)) : ℂ) * (↑u : ℂ))).im ∂μ := by
          simpa using (integral_im hintsum).symm
  have hfinal :
      0 ≤
        (∑ i : ι, ∑ j : ι,
          starRingEnd ℂ (c i) * c j *
            (∫ u, exp (-(↑((τ i : ℝ) + (τ j : ℝ)) : ℂ) * (↑u : ℂ)) ∂μ)).re := by
    rw [hsumre]
    exact hnonneg
  have himzero :
      (∑ i : ι, ∑ j : ι,
        starRingEnd ℂ (c i) * c j *
          (∫ u, exp (-(↑((τ i : ℝ) + (τ j : ℝ)) : ℂ) * (↑u : ℂ)) ∂μ)).im = 0 := by
    rw [hsumim]
    apply integral_eq_zero_of_ae
    have hae : ∀ᵐ (u : ℝ) ∂μ, 0 ≤ u := by
      rw [ae_iff]
      simp only [not_le]
      exact hsupp
    filter_upwards [hae] with u hu
    exact laplace_pd_integrand_im_zero c τ u
  exact ⟨himzero, hfinal⟩

end SCV
