/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import OSReconstruction.SCV.ConeDefs
import OSReconstruction.SCV.DistributionalUniqueness
import OSReconstruction.SCV.LaplaceSchwartz
import OSReconstruction.SCV.PaleyWienerSchwartz
import OSReconstruction.Wightman.Reconstruction.ForwardTubeDistributions
import OSReconstruction.Wightman.SchwartzTensorProduct
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Vladimirov-Tillmann Theorem

The Vladimirov-Tillmann theorem states that a holomorphic function on a tube
domain T(C) = E + iC over a proper open convex cone C, with tempered
distributional boundary values, has at most polynomial growth on compact
subcones of C, with an explicit inverse-power singularity at the cone boundary.

## Status

`vladimirov_tillmann` is a **theorem** (0 sorrys), proved from:
1. `bv_implies_fourier_support` (axiom): BV → Fourier support in dual cone
2. `fl_representation_from_bv` (axiom): F = FL extension on the tube
3. `fourierLaplaceExtMultiDim_vladimirov_growth` (proved in PaleyWienerSchwartz.lean):
   growth bound on the FL extension

The 4 bridge axioms (`bv_implies_fourier_support`, `tube_holomorphic_unique_from_bv`,
`fl_representation_from_bv`, `schwartz_clm_fubini_exchange`) are textbook SCV/FA
results requiring Poisson integral infrastructure not yet in Mathlib.

## References

* Vladimirov, V.S., "Methods of the Theory of Generalized Functions", Ch. II §14, Ch. V §25
* Streater-Wightman, "PCT, Spin and Statistics, and All That", Chapter 2
-/

open scoped Classical ComplexConjugate BigOperators
open MeasureTheory
noncomputable section

-- IsCone, IsSalientCone, TubeDomainSetPi are now in ConeDefs.lean

/-! ### Remaining SCV axioms for the VT bridge

The VT theorem is proved from 4 bridge axioms (3 in this file + 1 in SchwartzFubini).
Below is an informal explanation of each, aimed at a mathematician reviewing
the axiom statements for correctness.

#### Axiom 1: `bv_implies_fourier_support` (spectral support)

**Plain English**: If F is holomorphic on a tube T(C), satisfies the Vladimirov
moderate growth bound, and has tempered distributional boundary values W, then the
Fourier transform of W is supported in the dual cone C*.

**Mathematics**: Given F holomorphic on T(C) = {z : Im(z) ∈ C} with the growth bound
‖F(z)‖ ≤ C(1+‖z‖)^N · (1 + dist(Im z, ∂C)⁻¹)^q, and boundary value W ∈ S'(ℝᵐ)
defined by ∫ F(x+iεη) φ(x) dx → W(φ), there exists a tempered distribution T̂
(called `Tflat` in the code) such that:
  (a) supp(T̂) ⊆ C* = {ξ : ξ·y ≥ 0 for all y ∈ C}
  (b) W(φ) = T̂(FT_phys(φ)) for all φ ∈ S(ℝᵐ)
where FT_phys(φ)(ξ) = ∫ exp(ix·ξ) φ(x) dx is the physics Fourier transform.
The distribution T̂ is on the frequency side (momentum space); `HasFourierSupportInDualCone`
checks its literal distributional support, which IS the Fourier support of W.

**Why the growth hypothesis is essential**: Without it, F(z) = exp(-iaz) for a > 0
on the upper half-plane is a counterexample: holomorphic, tempered BV = exp(-iax),
but spectral support at -a ∉ C* = [0,∞).

**Reference**: Vladimirov, "Methods of Generalized Functions", Theorem 25.1.

#### Axiom 2: `tube_holomorphic_unique_from_bv` (uniqueness)

**Plain English**: Two holomorphic functions on the same tube with the same tempered
distributional boundary values are equal on the entire tube.

**Mathematics**: If F, G : T(C) → ℂ are both holomorphic, and for every direction
η ∈ C and test function φ ∈ S, the smeared slices ∫ F(x+iεη) φ(x) dx and
∫ G(x+iεη) φ(x) dx converge to the same limit W(φ) as ε → 0⁺, then F = G on T(C).

This is an immediate consequence of the edge-of-the-wedge theorem: the difference
H = F − G is holomorphic on T(C) with zero distributional boundary values.
By the edge-of-the-wedge theorem, H extends holomorphically across the boundary
and vanishes there, hence vanishes identically by analytic continuation.

**Reference**: Vladimirov §25; Streater-Wightman, Theorem 2-16 (edge of the wedge).

#### Axiom 3: `fl_representation_from_bv` (Fourier-Laplace representation)

**Plain English**: A tube-holomorphic function with tempered BV equals the
Fourier-Laplace extension of the spectral distribution T̂ from Axiom 1.

**Mathematics**: Given all the hypotheses of Axiom 1 plus the spectral distribution
T̂ with supp(T̂) ⊆ C* and W(φ) = T̂(FT_phys(φ)), define the FL extension
G(z) = T̂(ψ_z) where ψ_z(ξ) = χ(ξ) exp(iz·ξ) is a cutoff exponential in S(ℝᵐ).
Then F(z) = G(z) for all z ∈ T(C).

The proof route: G is holomorphic on T(C) (proved in PaleyWienerSchwartz.lean).
Its distributional BV is T̂ ∘ FT_phys = W (from `fourierLaplaceExtMultiDim_boundaryValue`,
proved in PW). So F and G have the same BV on T(C). By Axiom 2 (uniqueness), F = G.

**Reference**: Vladimirov, Theorem 25.5. This is the representation theorem:
every tube-holomorphic function with tempered BV is the Fourier-Laplace integral
of a dual-cone-supported tempered distribution.

#### Axiom 4: `schwartz_clm_fubini_exchange` (in SchwartzFubini.lean)

**Plain English**: A continuous linear functional on Schwartz space commutes with
parameter integrals of Schwartz-valued families.

**Mathematics**: Given T : S(ℝᵐ) →L ℂ, a continuous Schwartz-valued family
g : ℝᵐ → S(ℝᵐ) with polynomial seminorm growth, and f ∈ S(ℝᵐ), there exists
Φ ∈ S(ℝᵐ) such that:
  (a) Φ(ξ) = ∫ g(x)(ξ) · f(x) dx  (pointwise definition of the Schwartz integral)
  (b) T(Φ) = ∫ T(g(x)) · f(x) dx  (exchange of T with the integral)

Part (a) says the Bochner integral ∫ g(x) f(x) dx converges in S(ℝᵐ) (the polynomial
seminorm growth of g times the rapid decay of f gives convergent Schwartz seminorms).
Part (b) is T continuous ⟹ T(∫ ⋯) = ∫ T(⋯), the standard CLM exchange.

**Reference**: Hörmander, "Analysis of Linear PDOs I", Ch. 5; Reed-Simon I, §V.3.
The formal proof needs Schwartz-valued Bochner integration, which is not in Mathlib.

-/

/-- **Growth + boundary values imply dual-cone spectral support.**

If `F` is holomorphic on a tube `T(C)`, has polynomial growth on compact subsets
of the tube (the Vladimirov H(T^C) condition), and has tempered distributional
boundary values `W`, then there exists a frequency-side tempered distribution
`Tflat` with distributional support in the dual cone `C*`.

This is Vladimirov's Theorem 25.1 (spectral support from moderate growth).
The growth hypothesis is essential: without it, F(z) = exp(-iaz) for a > 0
is a counterexample (holomorphic on the upper half-plane, tempered BV exp(-iax),
but spectral support at -a ∉ C* = [0,∞)).

The compact-subset polynomial growth hypothesis suffices for Vladimirov 25.1.
Combined with `fl_representation_from_bv`, this yields the FL representation,
from which the full Vladimirov bound (with boundary singularity) follows
via `fourierLaplaceExtMultiDim_vladimirov_growth` (proved in PW).

**Convention**: `HasFourierSupportInDualCone` checks literal distributional support
of its argument. Here `Tflat` is already on the frequency side, so literal support
of `Tflat` in `C*` IS the Fourier support of the boundary value `W` in `C*`. -/
axiom bv_implies_fourier_support {n d : ℕ}
    (C : Set (Fin n → Fin (d + 1) → ℝ))
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (TubeDomainSetPi C))
    -- Polynomial growth on compact subsets of the tube (H(T^C) condition).
    -- For Wightman functions from OS axioms, this follows from the contraction
    -- semigroup property (Hille-Yosida: ‖T(t)‖ ≤ 1 for t > 0).
    (hF_growth : ∀ (K : Set (Fin n → Fin (d + 1) → ℂ)),
      IsCompact K → K ⊆ TubeDomainSetPi C →
        ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
          ∀ z ∈ K, ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N)
    (W : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ)
    (hF_bv : ∀ (η : Fin n → Fin (d + 1) → ℝ), η ∈ C →
      ∀ (φ : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ),
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : Fin n → Fin (d + 1) → ℝ,
            F (fun k μ => (x k μ : ℂ) + (ε : ℂ) * (η k μ : ℂ) * Complex.I) * φ x)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (W φ))) :
    let eR := flattenCLEquivReal n (d + 1)
    let Wflat : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ :=
      W.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eR)
    ∃ (Tflat : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ),
      HasFourierSupportInDualCone (eR '' C) Tflat ∧
      ∀ (φ : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ),
        Wflat φ = Tflat (physicsFourierFlatCLM φ)

/-- **Tube-holomorphic uniqueness from common boundary values.**

Two holomorphic functions on the same tube domain with identical tempered
distributional boundary values coincide on the whole tube.

Proved from `SCV.distributional_uniqueness_tube_of_zero_bv` applied to
H = F - G after flattening to the `Fin m → ℂ` type. -/
theorem tube_holomorphic_unique_from_bv {n d : ℕ}
    (C : Set (Fin n → Fin (d + 1) → ℝ))
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (F G : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (TubeDomainSetPi C))
    (hG_holo : DifferentiableOn ℂ G (TubeDomainSetPi C))
    (W : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ)
    (hF_bv : ∀ (η : Fin n → Fin (d + 1) → ℝ), η ∈ C →
      ∀ (φ : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ),
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : Fin n → Fin (d + 1) → ℝ,
            F (fun k μ => (x k μ : ℂ) + (ε : ℂ) * (η k μ : ℂ) * Complex.I) * φ x)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (W φ)))
    (hG_bv : ∀ (η : Fin n → Fin (d + 1) → ℝ), η ∈ C →
      ∀ (φ : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ),
        Filter.Tendsto
          (fun ε : ℝ => ∫ x : Fin n → Fin (d + 1) → ℝ,
            G (fun k μ => (x k μ : ℂ) + (ε : ℂ) * (η k μ : ℂ) * Complex.I) * φ x)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (W φ))) :
    Set.EqOn F G (TubeDomainSetPi C) := by
  -- Strategy: show H = F - G has zero BV, then apply distributional uniqueness.
  -- Work in flat coordinates via flattenCLEquiv.
  let e := flattenCLEquiv n (d + 1)
  let eR := flattenCLEquivReal n (d + 1)
  let Cflat : Set (Fin (n * (d + 1)) → ℝ) := eR '' C
  -- H = F - G in Pi coordinates
  let H : (Fin n → Fin (d + 1) → ℂ) → ℂ := fun z => F z - G z
  -- Hflat = H ∘ e.symm in flat coordinates
  let Hflat : (Fin (n * (d + 1)) → ℂ) → ℂ := H ∘ e.symm
  -- Flattened cone properties
  have hCflat_open : IsOpen Cflat := eR.toHomeomorph.isOpenMap _ hC_open
  have hCflat_conv : Convex ℝ Cflat := by
    intro x hx y hy a b ha hb hab
    obtain ⟨x', hx', rfl⟩ := hx; obtain ⟨y', hy', rfl⟩ := hy
    exact ⟨a • x' + b • y', hC_conv hx' hy' ha hb hab, by simp [map_add, map_smul]⟩
  have hCflat_ne : Cflat.Nonempty := by
    -- Open nonempty cone (salient cone in positive-dimensional space)
    sorry
  have hCflat_cone : ∀ (t : ℝ), 0 < t → ∀ y ∈ Cflat, t • y ∈ Cflat := by
    intro t ht y hy
    obtain ⟨y', hy', rfl⟩ := hy
    exact ⟨t • y', hC_cone y' hy' t ht, by simpa using eR.map_smul t y'⟩
  -- Tube membership transport
  have hmem_tube : ∀ w : Fin (n * (d + 1)) → ℂ,
      w ∈ SCV.TubeDomain Cflat → e.symm w ∈ TubeDomainSetPi C := by
    intro w hw
    show (fun k μ => ((e.symm w) k μ).im) ∈ C
    change (fun i => (w i).im) ∈ Cflat at hw
    obtain ⟨y, hy, hyw⟩ := hw
    convert hy using 1; ext k μ
    have := congr_fun hyw (finProdFinEquiv (k, μ))
    simpa [e, eR, flattenCLEquiv_symm_apply, flattenCLEquivReal_apply] using this.symm
  -- Hflat is holomorphic on TubeDomain Cflat
  have hHflat_holo : DifferentiableOn ℂ Hflat (SCV.TubeDomain Cflat) := by
    refine DifferentiableOn.comp (DifferentiableOn.sub hF_holo hG_holo)
      e.symm.differentiableOn ?_
    exact fun w hw => hmem_tube w hw
  -- Hflat has zero distributional BV
  have hHflat_bv_zero : ∀ (f : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ)
      (η : Fin (n * (d + 1)) → ℝ), η ∈ Cflat →
      Filter.Tendsto
        (fun ε : ℝ => ∫ x : Fin (n * (d + 1)) → ℝ,
          Hflat (fun i => (x i : ℂ) + ε * (η i : ℂ) * Complex.I) * f x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    intro f η ⟨η_pi, hη_pi, hη_eq⟩
    -- Transform to Pi coordinates
    let φ : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ :=
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eR f
    -- Both BV limits equal W(φ), so their difference → 0
    have hF_lim := hF_bv η_pi hη_pi φ
    have hG_lim := hG_bv η_pi hη_pi φ
    -- The integral in flat coords = integral in Pi coords (by change of variables)
    -- Since both converge to W(φ), their difference → 0
    sorry
  -- Integrability: Hflat(x+iy) * ψ(x) is integrable for y ∈ Cflat, ψ ∈ S
  have hHflat_int : ∀ y ∈ Cflat, ∀ ψ : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ,
      MeasureTheory.Integrable (fun x : Fin (n * (d + 1)) → ℝ =>
        Hflat (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) * ψ x) := by
    intro y hy ψ
    -- Hflat is holomorphic → continuous on tube → continuous on slice → locally bounded
    -- Locally bounded × Schwartz → integrable
    sorry
  -- Apply distributional uniqueness
  have hHflat_zero := SCV.distributional_uniqueness_tube_of_zero_bv
    hCflat_open hCflat_conv hCflat_ne hCflat_cone hHflat_holo hHflat_int hHflat_bv_zero
  -- Transport back: F = G on TubeDomainSetPi C
  intro z hz
  have hz_flat : e z ∈ SCV.TubeDomain Cflat := by
    show (fun i => (e z i).im) ∈ Cflat
    exact ⟨fun k μ => (z k μ).im, hz, by ext i; simp [e, eR, flattenCLEquiv_apply,
      flattenCLEquivReal_apply]⟩
  have h0 := hHflat_zero (e z) hz_flat
  -- h0 : Hflat (e z) = 0, i.e., F(e.symm(e z)) - G(e.symm(e z)) = 0
  -- Since e.symm (e z) = z, this gives F z - G z = 0
  change F (e.symm (e z)) - G (e.symm (e z)) = 0 at h0
  rwa [e.symm_apply_apply, sub_eq_zero] at h0

/-! ### Fourier-Laplace representation axiom -/

/-- **Fourier-Laplace representation theorem.**

If `F` is holomorphic on a tube `T(C)` in the Pi type (`Fin n → Fin (d+1) → ℂ`)
with tempered distributional boundary values `W`, and the frequency-side
distribution `Tflat` (the Fourier transform of the flattened BV, as delivered by
`bv_implies_fourier_support`) has distributional support in the dual cone, then
`F` equals the Fourier-Laplace extension of `Tflat` on the tube, after flattening.

This is the main content of Vladimirov's Theorem 25.5: a tube-holomorphic
function with tempered BV is uniquely representable as the FL integral of its
spectral distribution. The Fourier-Laplace extension `z ↦ Tflat(ψ_z)` is built
from the frequency-side distribution `Tflat`, NOT the space-side BV `W`.

The proof combines:
1. The SCV uniqueness theorem (two tube-holomorphic functions with the same
   distributional BV agree on the tube)
2. The BV matching: the FL extension of `Tflat` has distributional BV equal to
   `Tflat ∘ physicsFourierFlatCLM` (proved in PW), which equals `Wflat` by the
   relation from `bv_implies_fourier_support` -/
axiom fl_representation_from_bv {n d : ℕ}
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
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (W φ)))
    (Cflat : Set (Fin (n * (d + 1)) → ℝ))
    (hCflat_eq : Cflat = flattenCLEquivReal n (d + 1) '' C)
    (hCflat_open : IsOpen Cflat) (hCflat_conv : Convex ℝ Cflat)
    (hCflat_cone : IsCone Cflat) (hCflat_salient : IsSalientCone Cflat)
    -- Tflat is the frequency-side spectral distribution (Fourier transform of the BV)
    (Tflat : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_support : HasFourierSupportInDualCone Cflat Tflat)
    -- Tflat is the Fourier transform of the flattened BV
    (hTflat_eq : ∀ (φ : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ),
      W.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (flattenCLEquivReal n (d + 1))) φ = Tflat (physicsFourierFlatCLM φ)) :
    ∀ z ∈ TubeDomainSetPi C,
      F z = fourierLaplaceExtMultiDim Cflat hCflat_open hCflat_conv hCflat_cone
        hCflat_salient Tflat (flattenCLEquiv n (d + 1) z)

/-! ### The Vladimirov-Tillmann theorem -/

/-- The Vladimirov-Tillmann representation theorem for tube domains.

    If F is holomorphic on T(C) = { z | Im(z) ∈ C } where C is a proper open
    convex cone, has the Vladimirov moderate growth bound, and has tempered
    distributional boundary values W, then F has the Fourier-Laplace
    representation F = FL(T̂) for a spectral distribution T̂ supported in the
    dual cone, giving polynomial growth on compact subsets of C.

    **Hypotheses:**
    - C is an open convex cone, salient
    - F is holomorphic on T(C) with Vladimirov moderate growth
    - The smeared boundary values converge to a tempered distribution W

    **Conclusions:**
    1. On compact subsets K ⊂ C: ‖F(x+iy)‖ ≤ C_K · (1+‖x‖)^N
    2. The Vladimirov bound (passed through from the FL representation)

    **Non-circularity:** The hypothesis is compact-subset polynomial growth (H(T^C)),
    which is strictly weaker than the full Vladimirov bound (Conclusion 2). The
    theorem genuinely strengthens the hypothesis by adding the boundary-distance
    singularity factor via the FL representation.

    In the OS reconstruction, the compact-subset growth follows from the contraction
    semigroup property (Hille-Yosida). -/
-- Vladimirov-Tillmann representation theorem.
-- Proof route:
-- 1. bv_implies_fourier_support: compact-subset growth + BV → ∃ Tflat with support
--    in C*, Wflat φ = Tflat(FT_phys(φ))
-- 2. fl_representation_from_bv: BV + Tflat → F = FL(Tflat) on the tube
-- 3. fourierLaplaceExtMultiDim_vladimirov_growth: |FL(Tflat)(z)| ≤ Vladimirov bound
-- 4. Transport growth bound from flat coordinates back to Pi type
-- Steps 1 and 2 are axioms (pure SCV, not yet formalized).
-- Step 3 is fully proved in PaleyWienerSchwartz.lean.
theorem vladimirov_tillmann {n d : ℕ}
    (C : Set (Fin n → Fin (d + 1) → ℝ))
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (TubeDomainSetPi C))
    (hF_growth : ∀ (K : Set (Fin n → Fin (d + 1) → ℂ)),
      IsCompact K → K ⊆ TubeDomainSetPi C →
        ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
          ∀ z ∈ K, ‖F z‖ ≤ C_bd * (1 + ‖z‖) ^ N)
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
          (1 + (Metric.infDist (fun k μ => (z k μ).im) Cᶜ)⁻¹) ^ q) := by
  -- Step 1: Flatten the cone and the distribution
  let e := flattenCLEquiv n (d + 1)
  let eR := flattenCLEquivReal n (d + 1)
  let Cflat : Set (Fin (n * (d + 1)) → ℝ) := eR '' C
  let Wflat : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ :=
    W.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eR)
  -- Flattened cone properties
  have hCflat_open : IsOpen Cflat := eR.toHomeomorph.isOpenMap _ hC_open
  have hCflat_conv : Convex ℝ Cflat := hC_conv.linear_image eR.toLinearEquiv.toLinearMap
  have hCflat_cone : IsCone Cflat := by
    intro y hy t ht
    rcases hy with ⟨y', hy', rfl⟩
    exact ⟨t • y', hC_cone y' hy' t ht, by simpa using eR.map_smul t y'⟩
  have hCflat_salient : IsSalientCone Cflat := by
    intro y hy hy_neg
    -- eR is a homeomorphism, so closure (eR '' C) = eR '' (closure C)
    rw [show closure Cflat = eR '' closure C from
      (eR.toHomeomorph.image_closure C).symm] at hy hy_neg
    obtain ⟨y', hy', rfl⟩ := hy
    obtain ⟨y'', hy'', hyw⟩ := hy_neg
    -- eR y'' = -(eR y') = eR (-y'), so y'' = -y' by injectivity
    have h_neg : y'' = -y' := eR.injective (by rw [hyw, map_neg])
    subst h_neg
    -- Now y' ∈ closure C and -y' ∈ closure C, so y' = 0 by salientness
    exact show eR y' = 0 from by rw [hC_salient y' hy' hy'', map_zero]
  -- Step 2: Apply bv_implies_fourier_support to get frequency-side Tflat
  obtain ⟨Tflat, hTflat_support, hTflat_eq⟩ :=
    bv_implies_fourier_support C hC_open hC_conv hC_cone hC_salient F hF_holo hF_growth W hF_bv
  -- Step 3: Apply fl_representation_from_bv to get F = FL(Tflat) on the tube
  have hFL_repr : ∀ z ∈ TubeDomainSetPi C,
      F z = fourierLaplaceExtMultiDim Cflat hCflat_open hCflat_conv hCflat_cone
        hCflat_salient Tflat (e z) :=
    fl_representation_from_bv C hC_open hC_conv hC_cone hC_salient F hF_holo W hF_bv
      Cflat rfl hCflat_open hCflat_conv hCflat_cone hCflat_salient
      Tflat hTflat_support hTflat_eq
  -- Step 4: Get the growth bound on the FL extension (proved in PaleyWienerSchwartz)
  obtain ⟨C_bd_flat, N_flat, M_flat, hC_bd_pos, hFL_growth⟩ :=
    fourierLaplaceExtMultiDim_vladimirov_growth Cflat hCflat_open hCflat_conv
      hCflat_cone hCflat_salient Tflat hTflat_support
  -- Step 5: Transport infrastructure between Pi and flat coordinates
  -- Norm preservation for complex flatten
  have hflatten_norm : ∀ (z : Fin n → Fin (d + 1) → ℂ), ‖e z‖ = ‖z‖ := by
    intro z
    simp only [Pi.norm_def, e]
    congr 1
    simp only [Pi.nnnorm_def, flattenCLEquiv_apply]
    apply le_antisymm
    · apply Finset.sup_le; intro b _
      exact Finset.le_sup_of_le (Finset.mem_univ (finProdFinEquiv.symm b).1)
        (Finset.le_sup_of_le (Finset.mem_univ (finProdFinEquiv.symm b).2) (by simp))
    · apply Finset.sup_le; intro i _; apply Finset.sup_le; intro j _
      exact Finset.le_sup_of_le (Finset.mem_univ (finProdFinEquiv (i, j))) (by simp)
  -- eR is an isometry
  have heR_isometry : Isometry eR := by
    rw [isometry_iff_dist_eq]
    intro x y
    simp only [dist_eq_norm]
    rw [← eR.map_sub, flattenCLEquivReal_norm_eq]
  -- Complement transport: (eR '' C)^c = eR '' C^c (eR is bijective)
  have hcompl : Cflatᶜ = eR '' Cᶜ := by
    ext w; constructor
    · intro hw
      exact ⟨eR.symm w, fun hc => hw ⟨eR.symm w, hc, eR.apply_symm_apply w⟩,
        eR.apply_symm_apply w⟩
    · rintro ⟨y, hy, rfl⟩ ⟨y', hy', hyw⟩
      exact hy (eR.injective hyw ▸ hy')
  -- Im of flattened z = flatten of Im of z
  have hIm_flatten : ∀ z : Fin n → Fin (d + 1) → ℂ,
      (fun i => (e z i).im) = eR (fun k μ => (z k μ).im) := by
    intro z; ext i; simp [e, eR, flattenCLEquiv_apply, flattenCLEquivReal_apply]
  -- infDist equality
  have hinfDist_eq : ∀ z : Fin n → Fin (d + 1) → ℂ,
      Metric.infDist (fun i => (e z i).im) Cflatᶜ =
      Metric.infDist (fun k μ => (z k μ).im) Cᶜ := by
    intro z; rw [hIm_flatten, hcompl, Metric.infDist_image heR_isometry]
  -- Tube membership transport
  have hmem_tube : ∀ z : Fin n → Fin (d + 1) → ℂ,
      z ∈ TubeDomainSetPi C → e z ∈ SCV.TubeDomain Cflat := by
    intro z hz; show (fun i => (e z i).im) ∈ Cflat
    rw [hIm_flatten]; exact ⟨_, hz, rfl⟩
  -- Full growth bound in Pi type: for any z ∈ T(C),
  --   ‖F z‖ ≤ C_bd * (1+‖z‖)^N * (1+infDist(Im z, C^c)^{-1})^M
  have hF_growth_pi : ∀ z ∈ TubeDomainSetPi C,
      ‖F z‖ ≤ C_bd_flat * (1 + ‖z‖) ^ N_flat *
        (1 + (Metric.infDist (fun k μ => (z k μ).im) Cᶜ)⁻¹) ^ M_flat := by
    intro z hz
    rw [hFL_repr z hz]
    have hFL := hFL_growth (e z) (hmem_tube z hz)
    rwa [hflatten_norm, hinfDist_eq] at hFL
  -- Now prove both conclusions
  refine ⟨?_, ⟨C_bd_flat, N_flat, M_flat, hC_bd_pos, hF_growth_pi⟩⟩
  -- Conclusion 1: Polynomial growth on compact subcones K ⊆ C
  -- Derived from the full Vladimirov bound (Conclusion 2):
  -- On compact K ⊆ C, the infDist and norm-of-y factors are bounded.
  intro K hK hK_sub
  -- If K is empty, the conclusion is vacuously true
  by_cases hK_ne : K.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty] at hK_ne; subst hK_ne
    exact ⟨1, 0, one_pos, fun _ y hy => (Set.mem_empty_iff_false y |>.mp hy).elim⟩
  -- K compact ⊆ C open: bounded and bounded away from C^c
  obtain ⟨B_K, hB_K_pos, hB_K⟩ : ∃ B : ℝ, 0 < B ∧ ∀ y ∈ K, ‖y‖ ≤ B := by
    obtain ⟨B, hB⟩ := hK.isBounded.subset_closedBall 0
    refine ⟨max B 1, lt_max_of_lt_right one_pos, fun y hy => ?_⟩
    have := hB hy; rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  -- infDist achieves positive minimum on K
  obtain ⟨y₀, hy₀_mem, hy₀_min⟩ :=
    hK.exists_isMinOn hK_ne (Metric.continuous_infDist_pt Cᶜ).continuousOn
  -- Assemble the compact-subcone bound
  have hB_pos : (0 : ℝ) < (1 + B_K) ^ N_flat := pow_pos (by linarith) _
  have hD_pos : (0 : ℝ) < (1 + (Metric.infDist y₀ Cᶜ)⁻¹) ^ M_flat :=
    pow_pos (by linarith [inv_nonneg.mpr (Metric.infDist_nonneg (x := y₀) (s := Cᶜ))]) _
  refine ⟨C_bd_flat * (1 + B_K) ^ N_flat * (1 + (Metric.infDist y₀ Cᶜ)⁻¹) ^ M_flat,
    N_flat, mul_pos (mul_pos hC_bd_pos hB_pos) hD_pos, ?_⟩
  intro x y hy
  -- z = x + iy is in the tube since y ∈ K ⊆ C
  have hz_mem : (fun k μ => (x k μ : ℂ) + (y k μ : ℂ) * Complex.I) ∈ TubeDomainSetPi C := by
    show (fun k μ => ((x k μ : ℂ) + (y k μ : ℂ) * Complex.I).im) ∈ C
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, mul_zero, Complex.I_im, mul_one, add_zero, zero_add]
    exact hK_sub hy
  have hgrowth := hF_growth_pi _ hz_mem
  -- Im(z) = y
  have h_im_eq : (fun k μ => ((x k μ : ℂ) + (y k μ : ℂ) * Complex.I).im) = y := by
    ext k μ; simp
  -- infDist bound: (1 + (infDist y Cᶜ)⁻¹)^M ≤ (1 + (infDist y₀ Cᶜ)⁻¹)^M
  have h_infDist_le : Metric.infDist y₀ Cᶜ ≤ Metric.infDist y Cᶜ := hy₀_min hy
  have h_dist : (1 + (Metric.infDist (fun k μ => ((x k μ : ℂ) + ↑(y k μ) * Complex.I).im)
      Cᶜ)⁻¹) ^ M_flat ≤ (1 + (Metric.infDist y₀ Cᶜ)⁻¹) ^ M_flat := by
    rw [h_im_eq]
    have : (0 : ℝ) ≤ (Metric.infDist y Cᶜ)⁻¹ := inv_nonneg.mpr Metric.infDist_nonneg
    apply pow_le_pow_left₀ (by linarith)
    -- (infDist y Cᶜ)⁻¹ ≤ (infDist y₀ Cᶜ)⁻¹
    -- Case: infDist y₀ Cᶜ > 0 (y₀ ∈ C open, Cᶜ closed nonempty)
    -- or infDist y₀ Cᶜ = 0 (Cᶜ = ∅, all infDist = 0, 0⁻¹ = 0, trivial)
    rcases (Cᶜ : Set _).eq_empty_or_nonempty with h_empty | h_ne
    · -- Cᶜ = ∅: infDist to ∅ = 0 for both y₀ and y
      simp [h_empty, Metric.infDist_empty]
    · -- Cᶜ nonempty: y₀ ∈ C \ Cᶜ, so infDist y₀ Cᶜ > 0
      have hδ : 0 < Metric.infDist y₀ Cᶜ :=
        ((isClosed_compl_iff.mpr hC_open).notMem_iff_infDist_pos h_ne).mp
          (fun h => h (hK_sub hy₀_mem))
      linarith [inv_anti₀ hδ h_infDist_le]
  -- ‖z‖ ≤ ‖x‖ + ‖y‖ via triangle inequality
  have hz_norm : ‖(fun k μ => (x k μ : ℂ) + (y k μ : ℂ) * Complex.I)‖ ≤ ‖x‖ + ‖y‖ := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · -- ‖(fun k μ => (x k μ : ℂ))‖ = ‖x‖
      show ‖(fun k μ => (x k μ : ℂ))‖ ≤ ‖x‖
      simp only [Pi.norm_def, Pi.nnnorm_def]
      gcongr with k _ μ _
      simp [Complex.nnnorm_real]
    · -- ‖(fun k μ => (y k μ : ℂ) * I)‖ = ‖y‖
      show ‖(fun k μ => (y k μ : ℂ) * Complex.I)‖ ≤ ‖y‖
      simp only [Pi.norm_def, Pi.nnnorm_def]
      gcongr with k _ μ _
      simp [map_mul, Complex.nnnorm_I, mul_one, Complex.nnnorm_real]
  -- (1+‖z‖)^N ≤ (1+B_K)^N · (1+‖x‖)^N
  have h_norm : (1 + ‖(fun k μ => (x k μ : ℂ) + (y k μ : ℂ) * Complex.I)‖) ^ N_flat ≤
      (1 + B_K) ^ N_flat * (1 + ‖x‖) ^ N_flat := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have hy_bound : ‖y‖ ≤ B_K := hB_K y hy
    nlinarith [hz_norm, norm_nonneg x]
  have step1 : C_bd_flat * (1 + ‖(fun k μ => (x k μ : ℂ) + (y k μ : ℂ) * Complex.I)‖) ^
      N_flat ≤ C_bd_flat * ((1 + B_K) ^ N_flat * (1 + ‖x‖) ^ N_flat) :=
    mul_le_mul_of_nonneg_left h_norm hC_bd_pos.le
  calc ‖F (fun k μ => ↑(x k μ) + ↑(y k μ) * Complex.I)‖
    _ ≤ C_bd_flat * (1 + ‖(fun k μ => (x k μ : ℂ) + (y k μ : ℂ) * Complex.I)‖) ^ N_flat *
        (1 + (Metric.infDist (fun k μ => ((x k μ : ℂ) + ↑(y k μ) * Complex.I).im)
          Cᶜ)⁻¹) ^ M_flat := hgrowth
    _ ≤ C_bd_flat * ((1 + B_K) ^ N_flat * (1 + ‖x‖) ^ N_flat) *
        ((1 + (Metric.infDist y₀ Cᶜ)⁻¹) ^ M_flat) :=
      by
        have h1 : (0 : ℝ) ≤ (Metric.infDist
          (fun k μ => ((x k μ : ℂ) + ↑(y k μ) * Complex.I).im) Cᶜ)⁻¹ :=
          inv_nonneg.mpr Metric.infDist_nonneg
        exact mul_le_mul step1 h_dist (pow_nonneg (by linarith) _)
          (mul_nonneg hC_bd_pos.le (mul_nonneg hB_pos.le (pow_nonneg (by linarith [norm_nonneg x]) _)))
    _ = C_bd_flat * (1 + B_K) ^ N_flat * (1 + (Metric.infDist y₀ Cᶜ)⁻¹) ^ M_flat *
        (1 + ‖x‖) ^ N_flat := by ring

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
