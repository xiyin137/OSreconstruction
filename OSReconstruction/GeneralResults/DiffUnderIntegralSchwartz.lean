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

/-- **Differentiation under the integral sign for Schwartz test functions.**

    If `F : ℝ → (Fin m → ℝ) → ℂ` is a family with:
    - polynomial growth in x, uniformly in t near t₀
    - t-differentiability at each x
    - polynomial growth of ∂F/∂t in x

    then `g(t) = ∫ F(t,x) φ(x) dx` is differentiable and
    `g'(t₀) = ∫ (∂F/∂t)(t₀,x) φ(x) dx`.

    **Proof sketch**: Apply `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
    with the dominator `C * (1+‖x‖)^N * |φ(x)|`, which is integrable
    because polynomial × Schwartz is in L¹. -/
axiom hasDerivAt_schwartz_integral
    (F : ℝ → (Fin m → ℝ) → ℂ)
    (t₀ : ℝ) (δ : ℝ) (hδ : 0 < δ)
    -- F(t,·) is measurable for each t
    (hF_meas : ∀ t, AEStronglyMeasurable (F t) volume)
    -- F(t,·) has uniform polynomial growth near t₀
    (C_bd : ℝ) (N : ℕ) (hC_bd : 0 < C_bd)
    (hF_growth : ∀ t, |t - t₀| < δ → ∀ x : Fin m → ℝ,
      ‖F t x‖ ≤ C_bd * (1 + ‖x‖) ^ N)
    -- F is differentiable in t at each x
    (F' : (Fin m → ℝ) → ℂ)
    (hF_deriv : ∀ x : Fin m → ℝ, HasDerivAt (fun t => F t x) (F' x) t₀)
    -- The derivative has polynomial growth
    (C_bd' : ℝ) (N' : ℕ) (hC_bd' : 0 < C_bd')
    (hF'_growth : ∀ x : Fin m → ℝ, ‖F' x‖ ≤ C_bd' * (1 + ‖x‖) ^ N')
    -- The test function
    (φ : SchwartzMap (Fin m → ℝ) ℂ) :
    HasDerivAt
      (fun t => ∫ x : Fin m → ℝ, F t x * φ x)
      (∫ x : Fin m → ℝ, F' x * φ x)
      t₀

end
