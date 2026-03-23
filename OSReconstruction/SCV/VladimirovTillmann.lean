/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import OSReconstruction.SCV.LaplaceSchwartz
import OSReconstruction.Wightman.SchwartzTensorProduct
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

open scoped Classical ComplexConjugate BigOperators
open MeasureTheory
noncomputable section

/-! ### Definitions -/

/-- A set is a (positive) cone if it is closed under scaling by strictly
    positive reals. Uses `•` which is pointwise on Pi types. -/
def IsCone {E : Type*} [SMul ℝ E] (C : Set E) : Prop :=
  ∀ y ∈ C, ∀ t : ℝ, 0 < t → t • y ∈ C

/-- A cone is salient (or pointed) if its closure contains no complete line.
    Equivalently: the only element whose negation also lies in the closure is 0.
    This rules out cones like `{ y | y₁ > 0 }` where the `y₂` direction is
    unconstrained.

    For the Vladimirov-Tillmann theorem, salience ensures the dual cone has
    nonempty interior, which is needed for the Fourier-Laplace representation
    to yield global growth bounds. -/
def IsSalientCone {E : Type*} [AddCommGroup E] [TopologicalSpace E] (C : Set E) : Prop :=
  ∀ y, y ∈ closure C → -y ∈ closure C → y = 0

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
    - C is salient (its closure contains no complete line)
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
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (TubeDomainSetPi C))
    (W : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ)
    (hF_bv : ∀ (η : Fin n → Fin (d + 1) → ℝ), η ∈ C →
      ∀ (φ : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ),
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : Fin n → Fin (d + 1) → ℝ,
            F (fun k μ => (x k μ : ℂ) + (ε : ℂ) * (η k μ : ℂ) * Complex.I) * φ x)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (W φ))) :
    -- Conclusion 1: Polynomial growth on compact subsets of C
    (∀ (K : Set (Fin n → Fin (d + 1) → ℝ)), IsCompact K → K ⊆ C →
      ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
        ∀ (x y : Fin n → Fin (d + 1) → ℝ), y ∈ K →
          ‖F (fun k μ => (x k μ : ℂ) + (y k μ : ℂ) * Complex.I)‖ ≤
            C_bd * (1 + ‖x‖) ^ N) ∧
    -- Conclusion 2: Full Vladimirov bound with boundary distance
    (∃ (C_bd : ℝ) (N q : ℕ), C_bd > 0 ∧
      ∀ (z : Fin n → Fin (d + 1) → ℂ), z ∈ TubeDomainSetPi C →
        ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N *
          (1 + (Metric.infDist (fun k μ => (z k μ).im) Cᶜ)⁻¹) ^ q)

/-! ### Cluster property: distributional → tube interior -/

/-- **Distributional cluster property lifts to tube interior.**

    Let C be a proper open convex cone in ℝᵐ and F : T(C) → ℂ a holomorphic
    function on the tube T(C) = { z | Im(z) ∈ C }.  Let F₁, F₂ be holomorphic
    on corresponding lower-dimensional tubes.

    If the distributional boundary values of F satisfy a cluster decomposition
    under purely spatial translation of the second block of arguments — i.e.,
    the smeared (n₁+n₂)-point function factorizes as the product of the
    smeared n₁ and n₂-point functions when the spatial separation grows — then
    the same factorization holds pointwise on the tube interior.

    This is a consequence of the Poisson integral representation for tube
    domains (Vladimirov, Thm 25.1): the interior evaluation F(z) equals the
    distributional BV applied to a Schwartz-class Poisson kernel K_z.  For
    product tube configurations K factors, and a real shift translates the
    second factor.  Riemann-Lebesgue (`tendsto_integral_exp_smul_cocompact`)
    gives decay of the connected spectral component.

    Ref: Vladimirov, "Methods of the Theory of Generalized Functions", §25;
    Reed-Simon II, Thm IX.16; Streater-Wightman, §2.4 + Thm 3-5 -/
axiom distributional_cluster_lifts_to_tube {n₁ n₂ d : ℕ}
    -- Tube domain
    (C : Set (Fin (n₁ + n₂) → Fin (d + 1) → ℝ))
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    -- Joint holomorphic function F with distributional BV W
    (F : (Fin (n₁ + n₂) → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (TubeDomainSetPi C))
    (W : SchwartzMap (Fin (n₁ + n₂) → Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ)
    (hF_bv : ∀ (η : Fin (n₁ + n₂) → Fin (d + 1) → ℝ), η ∈ C →
      ∀ (φ : SchwartzMap (Fin (n₁ + n₂) → Fin (d + 1) → ℝ) ℂ),
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : Fin (n₁ + n₂) → Fin (d + 1) → ℝ,
            F (fun k μ => (x k μ : ℂ) + (ε : ℂ) * (η k μ : ℂ) * Complex.I) * φ x)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (W φ)))
    -- Factor functions F₁, F₂ with BVs W₁, W₂ on sub-tubes
    (C₁ : Set (Fin n₁ → Fin (d + 1) → ℝ))
    (C₂ : Set (Fin n₂ → Fin (d + 1) → ℝ))
    (F₁ : (Fin n₁ → Fin (d + 1) → ℂ) → ℂ)
    (hF₁_holo : DifferentiableOn ℂ F₁ (TubeDomainSetPi C₁))
    (W₁ : SchwartzMap (Fin n₁ → Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ)
    (hF₁_bv : ∀ (η₁ : Fin n₁ → Fin (d + 1) → ℝ), η₁ ∈ C₁ →
      ∀ (φ₁ : SchwartzMap (Fin n₁ → Fin (d + 1) → ℝ) ℂ),
        Filter.Tendsto
          (fun ε : ℝ => ∫ x₁ : Fin n₁ → Fin (d + 1) → ℝ,
            F₁ (fun k μ => (x₁ k μ : ℂ) + (ε : ℂ) * (η₁ k μ : ℂ) * Complex.I) * φ₁ x₁)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (W₁ φ₁)))
    (F₂ : (Fin n₂ → Fin (d + 1) → ℂ) → ℂ)
    (hF₂_holo : DifferentiableOn ℂ F₂ (TubeDomainSetPi C₂))
    (W₂ : SchwartzMap (Fin n₂ → Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ)
    (hF₂_bv : ∀ (η₂ : Fin n₂ → Fin (d + 1) → ℝ), η₂ ∈ C₂ →
      ∀ (φ₂ : SchwartzMap (Fin n₂ → Fin (d + 1) → ℝ) ℂ),
        Filter.Tendsto
          (fun ε : ℝ => ∫ x₂ : Fin n₂ → Fin (d + 1) → ℝ,
            F₂ (fun k μ => (x₂ k μ : ℂ) + (ε : ℂ) * (η₂ k μ : ℂ) * Complex.I) * φ₂ x₂)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (W₂ φ₂)))
    -- **Distributional cluster condition (R4):**
    -- The boundary distribution W cluster-decomposes towards W₁ ⊗ W₂
    -- under purely spatial translation of the n₂-block.
    --
    -- Stated for tensor-product test functions f₁ ⊗ (τ_a f₂), matching
    -- the Wightman cluster axiom R4 exactly.  Density of tensor products
    -- in the joint Schwartz space ensures this is equivalent to the
    -- general-φ version needed for the Poisson integral argument.
    (h_bv_cluster :
      ∀ (f₁ : SchwartzMap (Fin n₁ → Fin (d + 1) → ℝ) ℂ)
        (f₂ : SchwartzMap (Fin n₂ → Fin (d + 1) → ℝ) ℂ)
        (ε : ℝ), ε > 0 →
        ∃ R : ℝ, R > 0 ∧ ∀ (a : Fin (d + 1) → ℝ), a 0 = 0 →
          (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
          ∀ (f₂_a : SchwartzMap (Fin n₂ → Fin (d + 1) → ℝ) ℂ),
            (∀ x, f₂_a x = f₂ (fun k μ => x k μ - a μ)) →
            ‖W (f₁.tensorProduct f₂_a) - W₁ f₁ * W₂ f₂‖ < ε)
    -- Interior points
    (z₁ : Fin n₁ → Fin (d + 1) → ℂ)
    (z₂ : Fin n₂ → Fin (d + 1) → ℂ)
    (hz : Fin.append z₁ z₂ ∈ TubeDomainSetPi C)
    (hz₁ : z₁ ∈ TubeDomainSetPi C₁)
    (hz₂ : z₂ ∈ TubeDomainSetPi C₂)
    (ε : ℝ) (hε : ε > 0) :
    -- Conclusion: pointwise cluster on the tube interior.
    -- Note: the shifted point Fin.append z₁ (z₂ + ↑a) is automatically in T(C)
    -- because a is real, so Im(z₂ + ↑a) = Im(z₂) and the tube condition is unchanged.
    ∃ R : ℝ, R > 0 ∧
      ∀ (a : Fin (d + 1) → ℝ), a 0 = 0 →
        (∑ i : Fin d, (a (Fin.succ i))^2) > R^2 →
        ‖F (Fin.append z₁ (fun k μ => z₂ k μ + (a μ : ℂ))) -
          F₁ z₁ * F₂ z₂‖ < ε
