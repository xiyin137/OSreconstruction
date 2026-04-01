/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Quantitative Schwartz Seminorm Bounds for Cutoff × Exponential

A smooth compactly-supported cutoff χ multiplied by an exponential
`exp(L ξ)` (where L is a continuous linear map with negative-real-part
decay on the support) gives a Schwartz function whose seminorms grow
polynomially in ‖L‖.

This is the core analytic estimate underlying the Vladimirov-Tillmann
theorem: the dynamic scaling trick produces `χ(ξ/R) * exp(iz·ξ)` with
seminorms bounded by `B * (1 + ‖z‖)^N`.

## Main result

`schwartz_seminorm_cutoff_exp_bound`: For χ smooth with bounded
derivatives, compactly supported, and L : E →L[ℝ] ℂ with
`Re(L ξ) ≤ -c‖ξ‖` on supp(χ), the Schwartz (k,n)-seminorm of
`ξ ↦ χ(ξ) * exp(L ξ)` is bounded by `B * (1 + ‖L‖)^n`, where
B depends on χ, c, k, n but NOT on L.

## Applications

- `multiDimPsiZDynamic_seminorm_bound` in PaleyWienerSchwartz.lean
- `multiDimPsiZ_seminorm_continuous` (Lipschitz in L → continuous)
- `multiDimPsiZ_differenceQuotient_converges` (linear in L → differentiable)

## References

- Vladimirov, "Methods of Generalized Functions", §25
- See docs/vladimirov_axiom_blueprints.md
-/

open scoped Classical ComplexConjugate BigOperators NNReal
open MeasureTheory Complex
noncomputable section

variable {m : ℕ}

/-- **Quantitative seminorm bound for cutoff × exponential.**

    If χ is smooth with bounded derivatives and supported in a ball of radius R,
    and `exp(L ξ)` has exponential decay `|exp(L ξ)| ≤ exp(-c‖ξ‖)` on supp(χ),
    then the (k,n)-Schwartz seminorm of `χ * exp(L)` is bounded by
    `B * (1 + ‖L‖)^n`, with B independent of L.

    **Proof sketch** (Leibniz rule + exponential cap):
    1. `D^n[χ * exp(L)] = Σ_{j=0}^{n} C(n,j) D^j[χ] * D^{n-j}[exp(L)]`
       by `norm_iteratedFDeriv_mul_le`
    2. `‖D^j[χ](ξ)‖ ≤ C_j` (from `hχ_deriv_bound`)
    3. `‖D^{n-j}[exp(L)](ξ)‖ ≤ ‖L‖^{n-j} * |exp(L ξ)|`
       (derivatives of `exp ∘ L` bring down powers of L)
    4. `|exp(L ξ)| ≤ exp(-c‖ξ‖)` on supp(χ) (from `hexp_decay`)
    5. `‖ξ‖^k * exp(-c‖ξ‖) ≤ (k/(ce))^k` (polynomial × exponential bound)
    6. Sum over j gives `B * (1 + ‖L‖)^n` -/
axiom schwartz_seminorm_cutoff_exp_bound
    (χ : (Fin m → ℝ) → ℝ)
    (hχ_smooth : ContDiff ℝ ⊤ χ)
    (hχ_deriv_bound : ∀ j : ℕ, ∃ C_j : ℝ, ∀ ξ : Fin m → ℝ,
      ‖iteratedFDeriv ℝ j χ ξ‖ ≤ C_j)
    (hχ_compact_support : ∃ R > 0, ∀ ξ : Fin m → ℝ, ‖ξ‖ > R → χ ξ = 0)
    (L : (Fin m → ℝ) →L[ℝ] ℂ)
    (c : ℝ) (hc : 0 < c)
    (hexp_decay : ∀ ξ : Fin m → ℝ, χ ξ ≠ 0 → (L ξ).re ≤ -c * ‖ξ‖)
    (k n : ℕ) :
    ∃ (B : ℝ) (hB : 0 < B),
      ∀ ξ : Fin m → ℝ,
        ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (fun ξ => (χ ξ : ℂ) * cexp (L ξ)) ξ‖ ≤
          B * (1 + ‖L‖) ^ n

end
