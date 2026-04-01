/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import OSReconstruction.SCV.VladimirovTillmann
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Tube-Domain Boundary Value Existence from Polynomial Growth

The converse direction of the Vladimirov-Tillmann theorem:
a holomorphic function on a tube domain T(C) with the global Vladimirov
growth bound has tempered distributional boundary values.

This is the **critical SCV theorem** needed for OS reconstruction:
it takes the analytically continued Schwinger functions (which have
polynomial growth from the semigroup contraction) and produces the
Wightman distributions as tempered boundary values.

## Strategy (1D ray integration, avoiding Poincaré lemma)

Fix η ∈ C and approach the boundary along the ray y = tη for t > 0.

1. The Vladimirov bound along the ray: |F(x+itη)| ≤ C(1+|x|)^N · t^{-q}
2. Define the k-th iterated integral using Cauchy's repeated integration formula:
   `G_k(x,t) = (i^k / (k-1)!) ∫_{t₀}^{t} (t-τ)^{k-1} F(x+iτη) dτ`
   This is ONE integral (not k nested integrals), avoiding Fubini boilerplate.
3. For k > q, the t^{-q} singularity is integrable: (t-τ)^{k-1} · τ^{-q} ∈ L¹
4. G_k(x,t) extends continuously to t = 0 as a function H(x)
5. H(x) has polynomial growth (inherited from F)
6. Define the boundary value W as a distributional derivative by duality:
   `⟨W, φ⟩ = (-1)^k ∫ H(x) · ((η·∇_x)^k φ(x)) dx + ⟨correction terms, φ⟩`
   Since φ is Schwartz, (η·∇)^k φ is Schwartz, and the integral converges.

This constructs W ∈ S'(ℝ^m) using only 1D real integrals — no Poincaré lemma,
no Fourier multiplier traps, no Fréchet-valued integration.

## References

- Vladimirov, "Methods of Generalized Functions", §25
- See docs/vladimirov_tillmann_proof_plan.md (Phase 4)
- See docs/vladimirov_tillmann_gemini_reviews.md (ray integration trick)
-/

open scoped Classical ComplexConjugate BigOperators NNReal
open MeasureTheory Complex Filter
noncomputable section

variable {m : ℕ}

/-! ### The directional derivative operator -/

/-- The directional derivative of a Schwartz function along a vector η.
    `(η · ∇) φ (x) = ∑_j η_j · (∂φ/∂x_j)(x)` -/
def directionalDerivSchwartz (η : Fin m → ℝ) :
    SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] SchwartzMap (Fin m → ℝ) ℂ := by
  sorry

/-- The k-th iterated directional derivative. -/
def iteratedDirectionalDerivSchwartz (η : Fin m → ℝ) (k : ℕ) :
    SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] SchwartzMap (Fin m → ℝ) ℂ :=
  (directionalDerivSchwartz η) ^ k

/-! ### The slice functional -/

/-- Integration of F(x+iy) against a test function, for y in the tube. -/
def tubeSlice
    (F : (Fin m → ℂ) → ℂ) (y : Fin m → ℝ)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) : ℂ :=
  ∫ x : Fin m → ℝ, F (fun i => (x i : ℂ) + (y i : ℂ) * I) * φ x

/-! ### Cauchy's repeated integration formula -/

/-- The k-th iterated integral of the slice functional along a ray η ∈ C.
    Using Cauchy's formula for repeated integration:

    `G_k(φ, t) = (1/(k-1)!) ∫_{t₀}^{t} (t-τ)^{k-1} · tubeSlice F (τ•η) φ dτ`

    This is a single 1D integral, avoiding recursive definition + Fubini. -/
def cauchyRepeatedIntegral
    (F : (Fin m → ℂ) → ℂ) (η : Fin m → ℝ) (t₀ : ℝ)
    (k : ℕ) (φ : SchwartzMap (Fin m → ℝ) ℂ) (t : ℝ) : ℂ :=
  (((k - 1).factorial : ℝ)⁻¹ : ℂ) *
    ∫ τ in Set.Icc t₀ t,
      ((t - τ) ^ (k - 1) : ℝ) * tubeSlice F (τ • η) φ

/-! ### The boundary value construction -/

/-- **Main theorem**: A holomorphic function on T(C) with Vladimirov growth
    has tempered distributional boundary values.

    This is the converse of `vladimirov_tillmann` and the critical SCV
    theorem needed for OS reconstruction.

    Equivalent to xiyin's `tube_boundaryValueData_of_polyGrowth` in
    `SCV/TubeBoundaryValues.lean`, but with the full Vladimirov bound
    (including boundary-distance factor). -/
theorem tube_boundaryValue_of_vladimirov_growth
    {C : Set (Fin m → ℝ)}
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_ne : C.Nonempty)
    {F : (Fin m → ℂ) → ℂ}
    (hF_hol : DifferentiableOn ℂ F (SCV.TubeDomain C))
    {C_bd : ℝ} {N M : ℕ} (hC_bd : 0 < C_bd)
    (hF_growth : ∀ (z : Fin m → ℂ), z ∈ SCV.TubeDomain C →
      ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N *
        (1 + (Metric.infDist (fun i => (z i).im) Cᶜ)⁻¹) ^ M) :
    ∃ (W : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ),
      ∀ (φ : SchwartzMap (Fin m → ℝ) ℂ)
        (η : Fin m → ℝ), η ∈ C →
        Tendsto
          (fun ε : ℝ => tubeSlice F (ε • η) φ)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W φ)) := by
  -- Proof outline (1D ray integration):
  -- 1. Fix η ∈ C, t₀ > 0. Along the ray y = tη:
  --    |tubeSlice F (tη) φ| ≤ ∫ |F(x+itη)| |φ(x)| dx
  --    ≤ ∫ C_bd (1+‖x‖+t‖η‖)^N · t^{-M} · |φ(x)| dx
  --    ≤ C' · t^{-M}  (since φ is Schwartz, the x-integral is finite)
  --
  -- 2. Define G_k via cauchyRepeatedIntegral with k = M + 1.
  --    The integrand (t-τ)^{k-1} · tubeSlice has singularity τ^{-M},
  --    and (t-τ)^{k-1} · τ^{-M} is integrable on [t₀, t] since k > M.
  --
  -- 3. G_k(φ, t) extends continuously to t = 0:
  --    As t → 0+, the integral ∫_{t₀}^{0} ... = -∫_{0}^{t₀} (0-τ)^{k-1} · ... dτ
  --    This is a convergent integral (k > M).
  --    Define H(φ) = G_k(φ, 0) = (-1)^{k-1} / (k-1)! ∫_0^{t₀} τ^{k-1} · tubeSlice F (τη) φ dτ
  --
  -- 4. H is a continuous linear functional on Schwartz space:
  --    - Linear: tubeSlice is linear in φ, integral preserves linearity
  --    - Continuous: |H(φ)| ≤ C · ‖φ‖_{s,s} from the growth bound + Schwartz decay
  --
  -- 5. The Cauchy-Riemann equations give:
  --    (η·∇_x)^k G_k(φ, t) = tubeSlice F (tη) φ - (correction from t₀)
  --    Taking t → 0+: (η·∇_x)^k H(φ) = W(φ) - correction
  --    Define W by duality:
  --    ⟨W, φ⟩ = (-1)^k H((η·∇_x)^k φ) + correction(φ)
  --
  -- 6. W ∈ S' and the BV convergence follows from the construction.
  sorry

/-- Simplified version matching xiyin's interface in TubeBoundaryValues.lean:
    just polynomial growth (no boundary-distance factor), Wightman-style types. -/
theorem tube_boundaryValueData_of_polyGrowth'
    {n d : ℕ}
    (C : Set (Fin n → Fin (d + 1) → ℝ))
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_ne : C.Nonempty)
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF_hol : DifferentiableOn ℂ F (TubeDomainSetPi C))
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hF_growth : ∀ z ∈ TubeDomainSetPi C,
      ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N) :
    ∃ (W : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ),
      ∀ (φ : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ)
        (η : Fin n → Fin (d + 1) → ℝ),
        η ∈ C →
        Tendsto
          (fun ε : ℝ => ∫ x : Fin n → Fin (d + 1) → ℝ,
            F (fun k μ => ↑(x k μ) + (ε : ℂ) * ↑(η k μ) * I) * φ x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (W φ)) := by
  -- This follows from tube_boundaryValue_of_vladimirov_growth
  -- by noting that polynomial growth implies the Vladimirov bound
  -- (with M = 0, since no boundary-distance factor is needed).
  sorry

end
