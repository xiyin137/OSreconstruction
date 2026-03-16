/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import OSReconstruction.SCV.LaplaceSchwartz
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Vladimirov-Tillmann Theorem

The Vladimirov-Tillmann theorem states that a holomorphic function on a tube
domain T(C) = E + iC over a proper open convex cone C, with tempered
distributional boundary values, has at most polynomial growth on compact
subcones of C, with an explicit inverse-power singularity at the cone boundary.

## Status

This is stated as an axiom. The proof requires:
1. The structure theorem for tempered distributions
2. Fourier support in the dual cone from the boundary value convergence
3. The Fourier-Laplace representation F(z) = ∫_{C*} Ŵ(p) e^{iz·p} dp
4. Growth estimates from the Laplace integral over the dual cone

These are standard results (Vladimirov, "Methods of the Theory of Generalized
Functions", Theorem 14.1 and §25) but require substantial Lean infrastructure
in the SCV library (~800 lines).

## References

* Vladimirov, V.S., "Methods of the Theory of Generalized Functions", Ch. II §14, Ch. V §25
* Streater-Wightman, "PCT, Spin and Statistics, and All That", Chapter 2
-/

open scoped Classical ComplexConjugate
noncomputable section

/-! ### Definitions -/

/-- A set is a (positive) cone if it is closed under scaling by strictly
    positive reals. Uses `•` which is pointwise on Pi types. -/
def IsCone {E : Type*} [SMul ℝ E] (C : Set E) : Prop :=
  ∀ y ∈ C, ∀ t : ℝ, 0 < t → t • y ∈ C

/-- The tube domain T(C) = { z | Im(z) ∈ C } for the nested Pi type
    used by the Wightman forward tube. -/
def TubeDomainSetPi {n d : ℕ} (C : Set (Fin n → Fin (d + 1) → ℝ)) :
    Set (Fin n → Fin (d + 1) → ℂ) :=
  { z | (fun k μ => (z k μ).im) ∈ C }

/-! ### The Vladimirov-Tillmann axiom -/

/-- The Vladimirov-Tillmann theorem for tube domains.

    If F is holomorphic on T(C) = { z | Im(z) ∈ C } where C is a proper open
    convex cone, and has tempered distributional boundary values W, then F has
    polynomial growth on compact subcones and an explicit singularity bound at ∂C.

    **Hypotheses:**
    - C is an open convex cone (closed under positive scaling)
    - C is proper (Cᶜ ≠ ∅, ruling out C = full space)
    - F is holomorphic on T(C)
    - The smeared boundary values converge to a tempered distribution W

    **Conclusions:**
    1. On compact subcones K ⊂ C: ‖F(x+iy)‖ ≤ C_K · (1+‖x‖)^N
    2. Globally: ‖F(z)‖ ≤ C · (1+‖z‖)^N · (1 + dist(Im z, ∂C)⁻¹)^q

    The `(1 + dist⁻¹)` form prevents the bound from collapsing to zero
    deep inside the cone (where dist → ∞) and captures the inverse-power
    singularity near ∂C (where dist → 0). -/
axiom vladimirov_tillmann {n d : ℕ}
    (C : Set (Fin n → Fin (d + 1) → ℝ))
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_proper : Cᶜ.Nonempty)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (TubeDomainSetPi C))
    (W : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ)
    (hF_bv : ∀ (η : Fin n → Fin (d + 1) → ℝ), η ∈ C →
      ∀ (φ : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ),
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : Fin n → Fin (d + 1) → ℝ,
            F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * φ x)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (W φ))) :
    -- Conclusion 1: Polynomial growth on compact subcones
    (∀ (K : Set (Fin n → Fin (d + 1) → ℝ)), IsCompact K → K ⊆ C →
      ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
        ∀ (x y : Fin n → Fin (d + 1) → ℝ), y ∈ K →
          ‖F (fun k μ => ↑(x k μ) + ↑(y k μ) * Complex.I)‖ ≤
            C_bd * (1 + ‖x‖) ^ N) ∧
    -- Conclusion 2: Full Vladimirov bound with boundary distance
    (∃ (C_bd : ℝ) (N q : ℕ), C_bd > 0 ∧
      ∀ (z : Fin n → Fin (d + 1) → ℂ), z ∈ TubeDomainSetPi C →
        ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N *
          (1 + (Metric.infDist (fun k μ => (z k μ).im) Cᶜ)⁻¹) ^ q)
