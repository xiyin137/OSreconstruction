/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Differentiation of Parameter-Dependent Integrals Against Schwartz Functions

If F(t, x) is a family of functions parametrized by t ∈ ℝ (or ℂ), with
polynomial growth in x and smoothness in t, then

  `g(t) = ∫ F(t, x) * φ(x) dx`

is differentiable and `g'(t₀) = ∫ (∂F/∂t)(t₀, x) * φ(x) dx`.

This is "differentiation under the integral sign" specialized to Schwartz
test functions, where the polynomial growth of F and rapid decay of φ
provide the L¹ domination automatically.

## Main result

`hasDerivAt_schwartz_integral`: If F(t,·) has polynomial growth uniformly
in t (near t₀), and ∂F/∂t exists with polynomial growth, then the
Schwartz pairing g(t) = ∫ F(t,x)φ(x)dx has a derivative at t₀.

## Applications

- `cr_integration_identity` in TubeBoundaryValueExistence.lean
  (with F(t,x) = F_hol(x + itη) and t-derivative = i(η·∇)F)
- General parameter-dependent distribution theory

## References

- Hörmander, "The Analysis of Linear PDOs I", §2.4
- Mathlib: `MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
-/

open scoped Classical ComplexConjugate BigOperators
open MeasureTheory Complex Filter
noncomputable section

variable {m : ℕ}

/-- Polynomial growth × Schwartz is integrable. -/
theorem integrable_polyGrowth_mul_schwartz {m : ℕ}
    (g : (Fin m → ℝ) → ℂ) (hg_meas : AEStronglyMeasurable g volume)
    (C : ℝ) (N : ℕ) (hC : 0 < C)
    (hg_growth : ∀ x : Fin m → ℝ, ‖g x‖ ≤ C * (1 + ‖x‖) ^ N)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) :
    Integrable (fun x => g x * φ x) := by
  -- Dominator: (1+‖x‖)^{-n} * (C * 2^{N+n} * seminorm(φ)), integrable by integrablePower
  let n := (volume : Measure (Fin m → ℝ)).integrablePower
  let s : Finset (ℕ × ℕ) := Finset.Iic (N + n, 0)
  have hdom : Integrable (fun x : Fin m → ℝ => (1 + ‖x‖) ^ (-(n : ℝ))) :=
    MeasureTheory.Measure.integrable_pow_neg_integrablePower (μ := volume)
  have hK : 0 ≤ C * (2 ^ (N + n) * (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) φ) := by
    apply mul_nonneg (le_of_lt hC)
    exact mul_nonneg (pow_nonneg (by norm_num) _) (apply_nonneg _ _)
  refine Integrable.mono' (hdom.mul_const (C * (2 ^ (N + n) *
      (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) φ)))
    (hg_meas.mul φ.continuous.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Complex.norm_mul]
  calc ‖g x‖ * ‖(φ : (Fin m → ℝ) → ℂ) x‖
      ≤ C * (1 + ‖x‖) ^ N * ‖(φ : (Fin m → ℝ) → ℂ) x‖ := by
        exact mul_le_mul_of_nonneg_right (hg_growth x) (norm_nonneg _)
    _ ≤ (1 + ‖x‖) ^ (-(n : ℝ)) *
          (C * (2 ^ (N + n) * (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) φ)) := by
      have hsch :
          (1 + ‖x‖) ^ (N + n) * ‖(φ : (Fin m → ℝ) → ℂ) x‖ ≤
            2 ^ (N + n) * (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) φ := by
        simpa [s, norm_iteratedFDeriv_zero] using
          (SchwartzMap.one_add_le_sup_seminorm_apply
            (𝕜 := ℂ) (m := (N + n, 0)) (k := N + n) (n := 0)
            le_rfl le_rfl φ x)
      rw [Real.rpow_neg (by positivity), ← div_eq_inv_mul, le_div_iff₀' (by positivity),
        Real.rpow_natCast]
      simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hsch (le_of_lt hC)

/-- **Differentiation under the integral sign for Schwartz test functions.**

    If `F : ℝ → (Fin m → ℝ) → ℂ` is a family with:
    - polynomial growth in x, uniformly in t near t₀
    - t-differentiability at each x
    - polynomial growth of ∂F/∂t in x

    then `g(t) = ∫ F(t,x) φ(x) dx` is differentiable and
    `g'(t₀) = ∫ (∂F/∂t)(t₀,x) φ(x) dx`.

    **Proof sketch**: Apply `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
    with the dominator `C * (1+‖x‖)^N * |φ(x)|`, which is integrable
    because polynomial × Schwartz is in L¹.

    See `integrable_polyGrowth_mul_schwartz` for the key integrability fact. -/
theorem hasDerivAt_schwartz_integral
    (F : ℝ → (Fin m → ℝ) → ℂ)
    (t₀ : ℝ) (δ : ℝ) (hδ : 0 < δ)
    -- F(t,·) is measurable for each t
    (hF_meas : ∀ t, AEStronglyMeasurable (F t) volume)
    -- F(t,·) has uniform polynomial growth near t₀
    (C_bd : ℝ) (N : ℕ) (hC_bd : 0 < C_bd)
    (hF_growth : ∀ t, |t - t₀| < δ → ∀ x : Fin m → ℝ,
      ‖F t x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    -- F is differentiable in t on the neighborhood, with polynomial-growth derivative
    (F' : ℝ → (Fin m → ℝ) → ℂ)
    (hF_deriv : ∀ t, |t - t₀| < δ → ∀ x : Fin m → ℝ,
      HasDerivAt (fun s => F s x) (F' t x) t)
    (hF'_meas : AEStronglyMeasurable (F' t₀) volume)
    -- The derivative has polynomial growth UNIFORMLY on the neighborhood
    (C_bd' : ℝ) (N' : ℕ) (hC_bd' : 0 < C_bd')
    (hF'_growth : ∀ t, |t - t₀| < δ → ∀ x : Fin m → ℝ,
      ‖F' t x‖ ≤ C_bd' * (1 + ‖x‖) ^ N')
    -- The test function
    (φ : SchwartzMap (Fin m → ℝ) ℂ) :
    HasDerivAt
      (fun t => ∫ x : Fin m → ℝ, F t x * φ x)
      (∫ x : Fin m → ℝ, F' t₀ x * φ x)
      t₀ := by
  -- Define G(t,x) = F(t,x)*φ(x) and G'(t,x) = F'(t,x)*φ(x)
  let G : ℝ → (Fin m → ℝ) → ℂ := fun t x => F t x * φ x
  let G' : ℝ → (Fin m → ℝ) → ℂ := fun t x => F' t x * φ x
  let bnd : (Fin m → ℝ) → ℝ := fun x => C_bd' * (1 + ‖x‖) ^ N' * ‖(φ : (Fin m → ℝ) → ℂ) x‖
  -- The integral ∫ F(t,x)*φ(x) dx = ∫ G(t,x) dx, so it suffices to differentiate G
  suffices h : HasDerivAt (fun t => ∫ x, G t x) (∫ x, G' t₀ x) t₀ from h
  have hdiff_ae :
      ∀ᵐ a : Fin m → ℝ ∂volume, ∀ t ∈ Metric.ball t₀ δ,
        HasDerivAt (fun s => G s a) (G' t a) t := by
    exact Filter.Eventually.of_forall fun x =>
      fun t ht => (hF_deriv t (Metric.mem_ball.mp ht) x).mul_const (φ x)
  -- Apply Mathlib's theorem
  have hmain :
      Integrable (G' t₀) volume ∧
        HasDerivAt (fun n => ∫ a, G n a ∂volume) (∫ a, G' t₀ a ∂volume) t₀ := by
    exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (s := Metric.ball t₀ δ) (Metric.ball_mem_nhds t₀ hδ)
      (Filter.Eventually.of_forall fun t =>
        (hF_meas t).mul φ.continuous.aestronglyMeasurable)
      (integrable_polyGrowth_mul_schwartz (F t₀) (hF_meas t₀) C_bd N hC_bd
        (hF_growth t₀ (by simp [hδ])) φ)
      (hF'_meas.mul φ.continuous.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x =>
        fun t ht => by
          show ‖G' t x‖ ≤ bnd x
          simp only [G', bnd, norm_mul]
          exact mul_le_mul_of_nonneg_right
            (hF'_growth t (Metric.mem_ball.mp ht) x) (norm_nonneg _))
      (by
        show Integrable (fun x => C_bd' * (1 + ‖x‖) ^ N' * ‖(φ : (Fin m → ℝ) → ℂ) x‖)
        let n := (volume : Measure (Fin m → ℝ)).integrablePower
        let s : Finset (ℕ × ℕ) := Finset.Iic (N' + n, 0)
        have hdom : Integrable (fun x : Fin m → ℝ => (1 + ‖x‖) ^ (-(n : ℝ))) :=
          MeasureTheory.Measure.integrable_pow_neg_integrablePower (μ := volume)
        have hbnd_meas :
            AEStronglyMeasurable (fun x : Fin m → ℝ => C_bd' * (1 + ‖x‖) ^ N' * ‖(φ : (Fin m → ℝ) → ℂ) x‖) volume := by
          exact (by fun_prop : Continuous (fun x : Fin m → ℝ =>
            C_bd' * (1 + ‖x‖) ^ N' * ‖(φ : (Fin m → ℝ) → ℂ) x‖)).aestronglyMeasurable
        refine Integrable.mono' (hdom.mul_const (C_bd' * (2 ^ (N' + n) *
            (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) φ)))
          hbnd_meas
          (Filter.Eventually.of_forall fun x => ?_)
        have hsch :
            (1 + ‖x‖) ^ (N' + n) * ‖(φ : (Fin m → ℝ) → ℂ) x‖ ≤
              2 ^ (N' + n) * (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) φ := by
          simpa [s, norm_iteratedFDeriv_zero] using
            (SchwartzMap.one_add_le_sup_seminorm_apply
              (𝕜 := ℂ) (m := (N' + n, 0)) (k := N' + n) (n := 0)
              le_rfl le_rfl φ x)
        rw [Real.rpow_neg (by positivity), ← div_eq_inv_mul, le_div_iff₀' (by positivity),
          Real.rpow_natCast]
        have hmul := mul_le_mul_of_nonneg_left hsch (le_of_lt hC_bd')
        have hone : 0 ≤ 1 + ‖x‖ := by positivity
        have habsC : |C_bd'| = C_bd' := abs_of_nonneg (le_of_lt hC_bd')
        have habs1 : |1 + ‖x‖| = 1 + ‖x‖ := abs_of_nonneg hone
        simpa [pow_add, mul_assoc, mul_left_comm, mul_comm, habsC, habs1] using hmul)
      hdiff_ae
  exact hmain.2

end
