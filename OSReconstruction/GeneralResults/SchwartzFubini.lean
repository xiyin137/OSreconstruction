/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Fubini Exchange for Schwartz-Valued Integrals

A continuous linear functional on Schwartz space commutes with
parameter integrals of Schwartz-valued families.

## Main result

`schwartz_clm_fubini_exchange`: For T : S(ℝᵐ) →L[ℂ] ℂ and a
continuous family g : ℝᵐ → S(ℝᵐ) with polynomial seminorm growth,
there exists a Schwartz function Φ such that
  Φ(ξ) = ∫ g(x)(ξ) f(x) dx  and  T(Φ) = ∫ T(g(x)) f(x) dx.

## Mathematical content

This combines two facts:
1. The Schwartz-valued integral Φ = ∫ g(x) f(x) dx is well-defined
   as a Schwartz function (polynomial growth of seminorms × rapid
   decay of f gives convergent Schwartz-valued integral).
2. T is continuous linear, so T(∫ ...) = ∫ T(...) (CLM exchange).

Both follow from the nuclearity/Fréchet structure of Schwartz space.

## References

- Hörmander, "The Analysis of Linear PDOs I", Ch. 5
- Reed-Simon I, §V.3
- Vladimirov, "Methods of Generalized Functions", §25
-/

open MeasureTheory
noncomputable section

variable {m : ℕ}

-- **Axiom: CLM-integral exchange for Schwartz-valued families.**
--
-- Given:
-- - T : continuous linear functional on Schwartz space
-- - g : continuous Schwartz-valued family with polynomial seminorm growth
-- - f : Schwartz test function
--
-- Conclusion: there exists a Schwartz function Φ (the Schwartz-valued integral)
-- such that Φ(ξ) = ∫ g(x)(ξ) f(x) dx pointwise, and T(Φ) = ∫ T(g(x)) f(x) dx.
--
-- The axiom constructs Φ rather than taking it as input, to avoid redundancy
-- and ensure coherence. The continuity hypothesis on g (in Schwartz topology)
-- ensures the Bochner integral is well-defined.
axiom schwartz_clm_fubini_exchange {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    -- Continuity of the Schwartz-valued family (ensures Bochner integrability)
    (hg_cont : Continuous g)
    -- Uniform seminorm bound (polynomial growth in x)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ (x : Fin m → ℝ),
        SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    ∃ (Φ : SchwartzMap (Fin m → ℝ) ℂ),
      (∀ ξ : Fin m → ℝ, Φ ξ = ∫ x : Fin m → ℝ, g x ξ * f x) ∧
      (T Φ = ∫ x : Fin m → ℝ, T (g x) * f x)

/-- **CLM exchange for ℝ-parametric Schwartz-valued integrals.**

Analogous to `schwartz_clm_fubini_exchange` but for integration over `ℝ` with
Schwartz functions on a (possibly different) domain `E`. Given a continuous
ℂ-linear functional `w` on `SchwartzMap E ℂ` and a continuous family
`G : ℝ → SchwartzMap E ℂ` with polynomial seminorm growth, the pointwise
integral `Θ(ξ) = ∫ φ(t) · G(t)(ξ) dt` defines a Schwartz function, and
`w(Θ) = ∫ w(G(t)) · φ(t) dt`.

Mathematical content: identical to `schwartz_clm_fubini_exchange` — the
Schwartz-valued integral is well-defined by polynomial growth × rapid decay,
and the CLM exchange follows from continuity of `w`. The generalization is
that the integration domain (`ℝ`) may differ from the Schwartz domain (`E`). -/
theorem schwartz_clm_fubini_exchange_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : SchwartzMap E ℂ → ℂ) (hw_cont : Continuous w) (hw_lin : IsLinearMap ℂ w)
    (G : ℝ → SchwartzMap E ℂ) (hG_cont : Continuous G)
    (hG_poly : ∀ (k j : ℕ), ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ t : ℝ,
        SchwartzMap.seminorm ℝ k j (G t) ≤ C * (1 + ‖t‖) ^ N)
    (φ : SchwartzMap ℝ ℂ) :
    ∃ Θ : SchwartzMap E ℂ,
      (∀ ξ : E, Θ ξ = ∫ t : ℝ, (φ : ℝ → ℂ) t * G t ξ) ∧
      w Θ = ∫ t : ℝ, w (G t) * (φ : ℝ → ℂ) t := by
  sorry

end
