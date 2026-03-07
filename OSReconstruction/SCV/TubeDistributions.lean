/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.TubeDomainExtension
import OSReconstruction.SCV.IdentityTheorem
import OSReconstruction.SCV.LaplaceSchwartz
import OSReconstruction.SCV.BochnerTubeTheorem
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Distribution Theory Axioms for Tube Domains

This file provides the tube-domain boundary-value interface used by the
reconstruction chain. These are deep results from several complex variables
that connect distributional boundary values to pointwise properties of holomorphic
functions.

## Axioms

* boundary-value and uniqueness transport theorems under explicit regular
  Fourier-Laplace input data

## Mathematical Background

A tube domain T(C) = ℝᵐ + iC (where C ⊂ ℝᵐ is an open convex cone) carries a
natural notion of "distributional boundary value": a holomorphic function F on T(C)
has distributional boundary values if for each Schwartz function f and approach
direction η ∈ C, the integrals

    ∫ F(x + iεη) f(x) dx

converge as ε → 0⁺ to a tempered distribution.

**Theorem (Vladimirov):** If F is holomorphic on T(C) and comes from a genuine
Fourier-Laplace representation with the appropriate cone-support input, then it
admits continuous boundary behavior and uniqueness properties on the real edge.
The proved regular variants in this file formalize exactly that stronger route.

These results are proved in:
- Vladimirov, V.S. "Methods of the Theory of Generalized Functions" (2002), §25-26
- Epstein, H. "Generalization of the Edge-of-the-Wedge Theorem" (1960)
- Streater & Wightman, "PCT, Spin and Statistics", Theorem 2-6 and 2-9

## Why Axioms?

The proofs of these results require:
- The Paley-Wiener-Schwartz theorem (characterizing Fourier transforms of
  compactly supported distributions)
- The theory of Laplace transforms of tempered distributions
- Estimates on holomorphic functions via their Fourier-Laplace representation

None of these are currently available in Mathlib.

## Application

These axioms are used in `WickRotation.lean` to:
1. Prove that the BHW hypotheses (Lorentz invariance, boundary continuity,
   local commutativity of W_analytic) follow from the Wightman axioms
2. supply strong boundary-value transport results used downstream
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set

namespace SCV

/-! ### Proved versions under regular FL hypothesis

The weak bare-BV theorem fronts have been removed. The declarations below are
the rigorous transport results currently justified by explicit regular
Fourier-Laplace input data, packaged as `HasFourierLaplaceReprRegular`.
-/

/-- Zero boundary value on tube domains from regular FL input data. -/
theorem boundary_value_zero_of_regular {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    (hcone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C)
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (TubeDomain C))
    (hRegular : HasFourierLaplaceReprRegular C F)
    (h_dist_zero : ∀ (f : SchwartzMap (Fin m → ℝ) ℂ), hRegular.dist f = 0)
    (x : Fin m → ℝ) : F (realEmbed x) = 0 := by
  have hg_cont := hRegular.boundary_continuous
  have hint : ∀ (f : SchwartzMap (Fin m → ℝ) ℂ),
      ∫ y : Fin m → ℝ, F (realEmbed y) * f y = 0 := by
    intro f
    have hrecov := fourierLaplace_boundary_recovery hC hconv hne hcone hF hRegular f
    exact hrecov.symm.trans (h_dist_zero f)
  exact eq_zero_of_schwartz_integral_zero hg_cont hint x

/-- Distributional uniqueness on tube domains from regular FL input data
    for the difference G = F₁ - F₂. -/
theorem distributional_uniqueness_tube_of_regular {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    (hcone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C)
    {F₁ F₂ : (Fin m → ℂ) → ℂ}
    (hF₁ : DifferentiableOn ℂ F₁ (TubeDomain C))
    (hF₂ : DifferentiableOn ℂ F₂ (TubeDomain C))
    (hRegular_G : HasFourierLaplaceReprRegular C (fun z => F₁ z - F₂ z))
    (h_dist_zero : ∀ (f : SchwartzMap (Fin m → ℝ) ℂ), hRegular_G.dist f = 0) :
    ∀ z ∈ TubeDomain C, F₁ z = F₂ z := by
  -- Use `let` (not `set`) so `hRepr_G` and `h_dist_zero` are NOT renamed by the tactic
  let G : (Fin m → ℂ) → ℂ := fun z => F₁ z - F₂ z
  have hG_diff : DifferentiableOn ℂ G (TubeDomain C) := hF₁.sub hF₂
  -- Step 2: G(realEmbed x) = 0 for all x ∈ ℝᵐ
  have hG_boundary : ∀ x : Fin m → ℝ, G (realEmbed x) = 0 :=
    fun x =>
      boundary_value_zero_of_regular hC hconv hne hcone hG_diff
        hRegular_G h_dist_zero x
  -- Step 3: G(realEmbed x) = 0 + ContinuousWithinAt at boundary → G = 0 on T(C)
  -- by 1D edge-of-the-wedge slicing
  have hG_cont : ∀ x : Fin m → ℝ,
      ContinuousWithinAt G (TubeDomain C) (realEmbed x) :=
    fun x => hRegular_G.tube_continuousWithinAt x
  intro z hz
  have hG_zero : G z = 0 := by
    let y₀ : Fin m → ℝ := fun i => (z i).im
    let x₀ : Fin m → ℝ := fun i => (z i).re
    have hy₀ : y₀ ∈ C := hz
    let φ : ℂ → (Fin m → ℂ) := fun w i => ↑(x₀ i) + w * ↑(y₀ i)
    let g : ℂ → ℂ := G ∘ φ
    have hg_real : ∀ t : ℝ, g (t : ℂ) = 0 := by
      intro t
      show G (φ (t : ℂ)) = 0
      have hφ_real : φ (t : ℂ) = realEmbed (fun i => x₀ i + t * y₀ i) := by
        ext i; simp [φ, realEmbed, Complex.ofReal_add, Complex.ofReal_mul]
      rw [hφ_real]; exact hG_boundary _
    have hz_eq : φ I = z := by
      ext i; simp [φ, x₀, y₀, mul_comm I, Complex.re_add_im]
    suffices h : g I = 0 by
      show G z = 0; rw [show G z = g I from by simp [g, hz_eq]]; exact h
    have hφ_UHP : ∀ w : ℂ, w.im > 0 → φ w ∈ TubeDomain C := by
      intro w hw
      show (fun i => (φ w i).im) ∈ C
      have him : (fun i => (φ w i).im) = w.im • y₀ := by
        ext i; simp [φ, x₀, y₀, Complex.add_im, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [him]; exact hcone w.im hw y₀ hy₀
    have hφ_cont : Continuous φ :=
      continuous_pi fun i =>
        (continuous_const.add (continuous_id.mul continuous_const))
    have hg_diff : DifferentiableOn ℂ g EOW.UpperHalfPlane := by
      show DifferentiableOn ℂ (G ∘ φ) EOW.UpperHalfPlane
      exact hG_diff.comp (fun w _ => by
        apply DifferentiableAt.differentiableWithinAt
        exact differentiableAt_pi.mpr fun i =>
          (differentiableAt_const _).add
            (differentiableAt_id.mul (differentiableAt_const _)))
        (fun w hw => hφ_UHP w hw)
    have hφ_real_embed : ∀ t : ℝ, φ (↑t) = realEmbed (fun i => x₀ i + t * y₀ i) := by
      intro t; ext i; simp [φ, x₀, y₀, realEmbed, Complex.ofReal_add, Complex.ofReal_mul]
    have hcont_plus : ∀ x₁ : ℝ, (-3 : ℝ) < x₁ → x₁ < 3 →
        Filter.Tendsto g (nhdsWithin (↑x₁ : ℂ) EOW.UpperHalfPlane) (nhds (g ↑x₁)) := by
      intro x₁ _ _
      show ContinuousWithinAt (G ∘ φ) EOW.UpperHalfPlane ↑x₁
      have h := hG_cont (fun i => x₀ i + x₁ * y₀ i)
      rw [show realEmbed (fun i => x₀ i + x₁ * y₀ i) = φ ↑x₁ from
        (hφ_real_embed x₁).symm] at h
      exact h.comp hφ_cont.continuousAt.continuousWithinAt (fun w hw => hφ_UHP w hw)
    have hbv_cont : ∀ x₁ : ℝ, (-3 : ℝ) < x₁ → x₁ < 3 →
        Filter.Tendsto g (nhdsWithin (↑x₁ : ℂ) {c : ℂ | c.im = 0})
          (nhds (g ↑x₁)) := by
      intro x₁ _ _
      rw [hg_real x₁]
      apply Filter.Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with w (hw : w.im = 0)
      have : w = (w.re : ℂ) := Complex.ext rfl (by simp [hw])
      rw [this]; exact (hg_real w.re).symm
    obtain ⟨U, F, hU_open, hU_conv, _, _, hF_diff, hF_plus, hF_minus, hU_ball⟩ :=
      edge_of_the_wedge_1d (-3) 3 (by norm_num : (-3 : ℝ) < 3)
        g 0
        hg_diff
        (differentiableOn_const 0)
        hcont_plus
        (fun _ _ _ => tendsto_const_nhds)
        (fun x₁ _ _ => by show g ↑x₁ = 0; exact hg_real x₁)
        hbv_cont
    have hI_in_U : I ∈ U :=
      hU_ball (by simp [Metric.mem_ball, Complex.norm_I])
    have h_neg_I_in_U : -I ∈ U :=
      hU_ball (by simp [Metric.mem_ball, norm_neg, Complex.norm_I])
    have hF_zero_on_U : ∀ w ∈ U, F w = 0 := by
      have hU_conn : IsConnected U :=
        ⟨⟨I, hI_in_U⟩, hU_conv.isPreconnected⟩
      have h_neg_I_LHP : (-I).im < 0 := by simp [Complex.neg_im, Complex.I_im]
      have h_freq : ∃ᶠ w in nhdsWithin (-I) {(-I)}ᶜ, F w = (0 : ℂ → ℂ) w := by
        apply Filter.Eventually.frequently
        have hmem : U ∩ EOW.LowerHalfPlane ∈ nhdsWithin (-I) {(-I)}ᶜ :=
          nhdsWithin_le_nhds ((hU_open.inter EOW.lowerHalfPlane_isOpen).mem_nhds
            ⟨h_neg_I_in_U, h_neg_I_LHP⟩)
        filter_upwards [hmem] with w ⟨hwU, hwLHP⟩
        simp [hF_minus w ⟨hwU, hwLHP⟩]
      exact fun w hw => identity_theorem_connected hU_open hU_conn F 0
        hF_diff (differentiableOn_const 0) (-I) h_neg_I_in_U h_freq hw
    have hI_UHP : I.im > 0 := by simp [Complex.I_im]
    rw [← hF_plus I ⟨hI_in_U, hI_UHP⟩]
    exact hF_zero_on_U I hI_in_U
  exact sub_eq_zero.mp hG_zero

/-! ### Axiom 3: Bochner Tube Theorem -/

/-- **Bochner's tube theorem (convex hull extension).**

    If F is holomorphic on a tube domain T(C) = ℝᵐ + iC, then F extends to a
    unique holomorphic function on T(conv C) = ℝᵐ + i(conv C), where conv C
    is the convex hull of C.

    This is a fundamental result in several complex variables: holomorphic functions
    on tube domains automatically extend to the convex hull of the base.

    In the OS reconstruction, this is used only after the relevant cone geometry
    has been identified correctly. The current infrastructure proves Bochner's
    theorem for a fixed tube base `C`; it does not supply the missing OS-specific
    geometry. In particular, the naive "common SO-orbit of the positive orthant,
    then convex hull" route is already too large in `d = 1`, `k = 1`, so some
    different upstream geometric input is required.

    Ref: Bochner, "A theorem on analytic continuation of functions in several
    variables" (1938); Vladimirov §20.2; Hörmander, "An Introduction to Complex
    Analysis in Several Variables", Theorem 2.5.10 -/
theorem bochner_tube_theorem {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hne : C.Nonempty)
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (TubeDomain C)) :
    ∃ (F_ext : (Fin m → ℂ) → ℂ),
      DifferentiableOn ℂ F_ext (TubeDomain (convexHull ℝ C)) ∧
      ∀ z ∈ TubeDomain C, F_ext z = F z :=
  bochner_tube_extension hC hne hF

end SCV

end
