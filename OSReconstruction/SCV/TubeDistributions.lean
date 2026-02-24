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

This file provides two axioms from the theory of distributions and holomorphic
functions on tube domains. These are deep results from several complex variables
that connect distributional boundary values to pointwise properties of holomorphic
functions.

## Axioms

* `continuous_boundary_tube` — holomorphic functions on tube domains with tempered
  distributional boundary values extend continuously to the real boundary.

* `polynomial_growth_tube` — holomorphic functions on tube domains with tempered
  distributional boundary values satisfy polynomial growth estimates.

## Mathematical Background

A tube domain T(C) = ℝᵐ + iC (where C ⊂ ℝᵐ is an open convex cone) carries a
natural notion of "distributional boundary value": a holomorphic function F on T(C)
has distributional boundary values if for each Schwartz function f and approach
direction η ∈ C, the integrals

    ∫ F(x + iεη) f(x) dx

converge as ε → 0⁺ to a tempered distribution.

**Theorem (Vladimirov):** If F is holomorphic on T(C) and has tempered distributional
boundary values, then:
1. F extends continuously to the closure of T(C) at every real point
   (`continuous_boundary_tube`)
2. F satisfies polynomial growth estimates on approach regions
   (`polynomial_growth_tube`)

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
2. Establish temperedness (E0) of the constructed Schwinger functions
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set

namespace SCV

/-! ### Axiom 1: Continuous Boundary Values -/

/-- **Continuous boundary values for tube-domain holomorphic functions.**

    If F is holomorphic on a tube domain T(C) and has distributional boundary
    values (the smeared integrals ∫ F(x+iεη)f(x)dx converge as ε→0⁺), then
    F extends continuously to the real boundary: for each real point x,
    `ContinuousWithinAt F (TubeDomain C) (realEmbed x)`.

    This is a fundamental result connecting the distributional and pointwise
    theories of boundary values of holomorphic functions on tube domains.

    The proof (not formalized here) proceeds by:
    1. The Fourier-Laplace representation: F(z) = ∫ e^{iz·ξ} dμ(ξ) where μ is
       a tempered distribution supported in the dual cone C*
    2. The Laplace integral converges absolutely for Im(z) ∈ C and extends
       continuously to Im(z) → 0 by dominated convergence
    3. The boundary value of this representation is the distributional boundary
       value of F

    Ref: Vladimirov, "Methods of the Theory of Generalized Functions" §26.2;
    Epstein, J. Math. Phys. 1 (1960) 524-531;
    Streater-Wightman, Theorem 2-9 -/
theorem continuous_boundary_tube {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (TubeDomain C))
    (h_bv : ∃ (T : SchwartzMap (Fin m → ℝ) ℂ → ℂ), Continuous T ∧
      ∀ (f : SchwartzMap (Fin m → ℝ) ℂ) (η : Fin m → ℝ), η ∈ C →
        Filter.Tendsto (fun ε : ℝ =>
          ∫ x : Fin m → ℝ, F (fun i => ↑(x i) + ↑ε * ↑(η i) * I) * f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (T f)))
    (x : Fin m → ℝ) :
    ContinuousWithinAt F (TubeDomain C) (realEmbed x) := by
  -- Extract the tempered distribution from the BV hypothesis
  obtain ⟨T, hT_cont, hT⟩ := h_bv
  -- Build the Fourier-Laplace representation
  have hRepr : HasFourierLaplaceRepr C F :=
    exists_fourierLaplaceRepr hC hconv hne hF hT_cont hT
  -- Apply the core Fourier-Laplace continuous boundary result
  exact fourierLaplace_continuousWithinAt hC hconv hne hF hRepr x

/-- **Boundary value recovery for tube-domain holomorphic functions.**

    The continuous extension to the boundary integrates against test functions
    to reproduce the distributional boundary value. This is the second half of
    Vladimirov's theorem (§26.2): not only does the continuous extension exist,
    but the distributional BV T is given by integration against it:
    T(f) = ∫ F(realEmbed x) · f(x) dx.

    Combined with `continuous_boundary_tube`, this says: the distributional BV
    and the pointwise BV (continuous extension) are the same object.

    Ref: Vladimirov §26.2; Streater-Wightman, Theorem 2-9 -/
theorem boundary_value_recovery {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    (hcone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C)
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (TubeDomain C))
    {T : SchwartzMap (Fin m → ℝ) ℂ → ℂ}
    (hT_cont : Continuous T)
    (h_bv : ∀ (f : SchwartzMap (Fin m → ℝ) ℂ) (η : Fin m → ℝ), η ∈ C →
      Filter.Tendsto (fun ε : ℝ =>
        ∫ x : Fin m → ℝ, F (fun i => ↑(x i) + ↑ε * ↑(η i) * I) * f x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (T f)))
    (f : SchwartzMap (Fin m → ℝ) ℂ) :
    T f = ∫ x : Fin m → ℝ, F (realEmbed x) * f x := by
  -- Build the Fourier-Laplace representation from the BV data
  let hRepr : HasFourierLaplaceRepr C F :=
    exists_fourierLaplaceRepr hC hconv hne hF hT_cont h_bv
  -- hRepr.dist = T by construction, so the result follows directly
  exact fourierLaplace_boundary_recovery hC hconv hne hcone hF hRepr f

/-- **Zero distributional boundary value implies zero boundary function.**

    If F is holomorphic on T(C) and has distributional boundary value equal to 0
    (i.e., ∫ F(x+iεη)f(x)dx → 0 as ε → 0⁺ for all Schwartz f and η ∈ C),
    then F(realEmbed x) = 0 for all x ∈ ℝᵐ.

    This combines `continuous_boundary_tube` (the boundary extension exists),
    `boundary_value_recovery` (the extension integrates to give the distributional BV),
    and the fundamental lemma of distribution theory (a continuous function integrating
    to 0 against all Schwartz test functions is identically 0).

    Ref: Vladimirov §26.2-26.3 -/
theorem boundary_value_zero {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    (hcone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C)
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (TubeDomain C))
    (h_bv : ∀ (f : SchwartzMap (Fin m → ℝ) ℂ) (η : Fin m → ℝ), η ∈ C →
      Filter.Tendsto (fun ε : ℝ =>
        ∫ x : Fin m → ℝ, F (fun i => ↑(x i) + ↑ε * ↑(η i) * I) * f x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0))
    (x : Fin m → ℝ) : F (realEmbed x) = 0 := by
  -- Step 1: Package T = 0 as a distributional BV for boundary_value_recovery
  -- h_bv says: for all f η, η ∈ C → tendsto (∫ F(x+iεη)f(x)dx) → 0
  -- This is the same as the zero distribution T = 0 acting as T(f) = 0 for all f.
  -- Step 2: Apply boundary_value_recovery with T = 0 to get
  --   0 = ∫ F(realEmbed x) * f(x) dx for all Schwartz f
  have hint : ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
      ∫ x : Fin m → ℝ, F (realEmbed x) * f x = 0 := by
    intro f
    have h := boundary_value_recovery hC hconv hne hcone hF continuous_const h_bv f
    simp at h
    exact h.symm
  -- Step 3: Build Fourier-Laplace representation to get continuity
  let hRepr : HasFourierLaplaceRepr C F :=
    exists_fourierLaplaceRepr hC hconv hne hF continuous_const h_bv
  have hcont : Continuous (fun x : Fin m → ℝ => F (realEmbed x)) :=
    fourierLaplace_boundary_continuous hC hconv hne hF hRepr
  -- Step 4: Apply fundamental lemma: continuous + integrates to 0 against all Schwartz => 0
  exact eq_zero_of_schwartz_integral_zero hcont hint x

/-- **Distributional uniqueness for tube-domain holomorphic functions.**

    If two holomorphic functions on a tube domain T(C) (where C is an open convex
    cone) have the same distributional boundary values, they are equal on T(C).

    Proof:
    1. G = F₁ - F₂ is holomorphic on T(C) with distributional BV = 0.
    2. `boundary_value_zero` gives G(realEmbed x) = 0 for all x ∈ ℝᵐ.
    3. For any z₀ = x₀ + iy₀ ∈ T(C), restrict G to the complex line w ↦ x₀ + wy₀.
       This gives g holomorphic on {Im w > 0} (since C is a cone) with g(t) = 0 for
       t ∈ ℝ. By edge-of-the-wedge (glue with the zero function on {Im w < 0}) and
       the identity theorem, g ≡ 0. In particular G(z₀) = g(i) = 0.

    Ref: Vladimirov §26.3; Streater-Wightman, Corollary to Theorem 2-9 -/
theorem distributional_uniqueness_tube {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    (hcone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C)
    {F₁ F₂ : (Fin m → ℂ) → ℂ}
    (hF₁ : DifferentiableOn ℂ F₁ (TubeDomain C))
    (hF₂ : DifferentiableOn ℂ F₂ (TubeDomain C))
    -- Same distributional boundary values: for all Schwartz test functions f
    -- and approach directions η ∈ C, the boundary integrals of (F₁-F₂)*f → 0.
    (h_agree : ∀ (f : SchwartzMap (Fin m → ℝ) ℂ) (η : Fin m → ℝ), η ∈ C →
      Filter.Tendsto (fun ε : ℝ =>
        ∫ x : Fin m → ℝ,
          (F₁ (fun i => ↑(x i) + ↑ε * ↑(η i) * I) -
           F₂ (fun i => ↑(x i) + ↑ε * ↑(η i) * I)) * f x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0)) :
    ∀ z ∈ TubeDomain C, F₁ z = F₂ z := by
  -- Step 1: G = F₁ - F₂ is holomorphic on T(C) with distributional BV = 0
  set G := fun z => F₁ z - F₂ z with hG_def
  have hG_diff : DifferentiableOn ℂ G (TubeDomain C) := hF₁.sub hF₂
  -- Package the distributional BV = 0 for continuous_boundary_tube
  have hG_bv : ∃ (T : SchwartzMap (Fin m → ℝ) ℂ → ℂ), Continuous T ∧
      ∀ (f : SchwartzMap (Fin m → ℝ) ℂ) (η : Fin m → ℝ), η ∈ C →
        Filter.Tendsto (fun ε : ℝ =>
          ∫ x : Fin m → ℝ, G (fun i => ↑(x i) + ↑ε * ↑(η i) * I) * f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (T f)) := by
    refine ⟨0, continuous_const, fun f η hη => ?_⟩
    simp only [Pi.zero_apply]
    -- The integrand G(x+iεη) * f(x) = (F₁ - F₂)(x+iεη) * f(x)
    exact h_agree f η hη
  -- Step 2: ContinuousWithinAt G (TubeDomain C) (realEmbed x) for all x
  have hG_cont : ∀ x : Fin m → ℝ,
      ContinuousWithinAt G (TubeDomain C) (realEmbed x) :=
    fun x => continuous_boundary_tube hC hconv hne hG_diff hG_bv x
  -- Step 3: G(realEmbed x) = 0 for all x ∈ ℝᵐ
  -- The continuous boundary value must equal the distributional BV (which is 0).
  -- This follows from: ContinuousWithinAt gives pointwise convergence G(x+iεη) → G(x),
  -- dominated convergence gives ∫ G(x+iεη)f(x)dx → ∫ G(x)f(x)dx = 0 for all Schwartz f,
  -- and a continuous function integrating to 0 against all Schwartz functions is 0.
  have hG_boundary : ∀ x : Fin m → ℝ, G (realEmbed x) = 0 :=
    boundary_value_zero hC hconv hne hcone hG_diff (fun f η hη => h_agree f η hη)
  -- Step 4: G = 0 on T(C) by one-variable slicing + edge-of-the-wedge
  -- For z₀ = x₀ + iy₀ ∈ T(C) with y₀ ∈ C, the restriction g(w) = G(x₀ + wy₀) is
  -- holomorphic on {Im w > 0} (since C contains the ray through y₀ for cones),
  -- zero on ℝ (by hG_boundary), hence zero everywhere by edge_of_the_wedge_1d +
  -- identity_theorem_connected.
  intro z hz
  have hG_zero : G z = 0 := by
    -- Extract real and imaginary parts of z
    let y₀ : Fin m → ℝ := fun i => (z i).im
    let x₀ : Fin m → ℝ := fun i => (z i).re
    have hy₀ : y₀ ∈ C := hz
    -- Define the 1D slice: g(w) = G(x₀ + w · y₀)
    let φ : ℂ → (Fin m → ℂ) := fun w i => ↑(x₀ i) + w * ↑(y₀ i)
    let g : ℂ → ℂ := G ∘ φ
    -- g(t) = 0 for all real t (from hG_boundary)
    have hg_real : ∀ t : ℝ, g (t : ℂ) = 0 := by
      intro t
      show G (φ (t : ℂ)) = 0
      have hφ_real : φ (t : ℂ) = realEmbed (fun i => x₀ i + t * y₀ i) := by
        ext i; simp [φ, realEmbed, Complex.ofReal_add, Complex.ofReal_mul]
      rw [hφ_real]; exact hG_boundary _
    -- z = φ(I) since x₀ i + I * y₀ i = Re(z i) + Im(z i) * I = z i
    have hz_eq : φ I = z := by
      ext i; simp [φ, x₀, y₀, mul_comm I, Complex.re_add_im]
    -- So G(z) = g(I), and it suffices to show g(I) = 0
    suffices h : g I = 0 by
      show G z = 0; rw [show G z = g I from by simp [g, hz_eq]]; exact h
    -- (a) φ maps UHP into TubeDomain C
    -- Im(φ w i) = w.im * y₀ i, so Im(φ w) = w.im • y₀.
    -- Need w.im • y₀ ∈ C when w.im > 0 and y₀ ∈ C.
    -- This is the cone/scaling property of C, which holds for forward light cones.
    have hφ_UHP : ∀ w : ℂ, w.im > 0 → φ w ∈ TubeDomain C := by
      intro w hw
      show (fun i => (φ w i).im) ∈ C
      have him : (fun i => (φ w i).im) = w.im • y₀ := by
        ext i; simp [φ, x₀, y₀, Complex.add_im, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im]
      rw [him]
      exact hcone w.im hw y₀ hy₀
    -- (b) φ is continuous (affine in w)
    have hφ_cont : Continuous φ :=
      continuous_pi fun i =>
        (continuous_const.add (continuous_id.mul continuous_const))
    -- (c) g is holomorphic on UHP (composition of G with differentiable φ)
    have hg_diff : DifferentiableOn ℂ g EOW.UpperHalfPlane := by
      show DifferentiableOn ℂ (G ∘ φ) EOW.UpperHalfPlane
      exact hG_diff.comp (fun w _ => by
        apply DifferentiableAt.differentiableWithinAt
        exact differentiableAt_pi.mpr fun i =>
          (differentiableAt_const _).add
            (differentiableAt_id.mul (differentiableAt_const _)))
        (fun w hw => hφ_UHP w hw)
    -- Helper: φ maps real line to realEmbed
    have hφ_real_embed : ∀ t : ℝ, φ (↑t) = realEmbed (fun i => x₀ i + t * y₀ i) := by
      intro t; ext i; simp [φ, x₀, y₀, realEmbed, Complex.ofReal_add, Complex.ofReal_mul]
    -- (d) Continuous boundary values from above at real points
    have hcont_plus : ∀ x₁ : ℝ, (-3 : ℝ) < x₁ → x₁ < 3 →
        Filter.Tendsto g (nhdsWithin (↑x₁ : ℂ) EOW.UpperHalfPlane) (nhds (g ↑x₁)) := by
      intro x₁ _ _
      show ContinuousWithinAt (G ∘ φ) EOW.UpperHalfPlane ↑x₁
      have h := hG_cont (fun i => x₀ i + x₁ * y₀ i)
      rw [show realEmbed (fun i => x₀ i + x₁ * y₀ i) = φ ↑x₁ from
        (hφ_real_embed x₁).symm] at h
      exact h.comp hφ_cont.continuousAt.continuousWithinAt (fun w hw => hφ_UHP w hw)
    -- (d) Boundary values continuous along real line (g = 0 on reals)
    have hbv_cont : ∀ x₁ : ℝ, (-3 : ℝ) < x₁ → x₁ < 3 →
        Filter.Tendsto g (nhdsWithin (↑x₁ : ℂ) {c : ℂ | c.im = 0})
          (nhds (g ↑x₁)) := by
      intro x₁ _ _
      rw [hg_real x₁]
      apply Filter.Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with w (hw : w.im = 0)
      have : w = (w.re : ℂ) := Complex.ext rfl (by simp [hw])
      rw [this]; exact (hg_real w.re).symm
    -- (e) Apply edge_of_the_wedge_1d with g on UHP and 0 on LHP
    obtain ⟨U, F, hU_open, hU_conv, _, _, hF_diff, hF_plus, hF_minus, hU_ball⟩ :=
      edge_of_the_wedge_1d (-3) 3 (by norm_num : (-3 : ℝ) < 3)
        g 0
        hg_diff
        (differentiableOn_const 0)
        hcont_plus
        (fun _ _ _ => tendsto_const_nhds)
        (fun x₁ _ _ => by show g ↑x₁ = 0; exact hg_real x₁)
        hbv_cont
    -- I ∈ U since |I - 0| = 1 < 3 = radius of ball
    have hI_in_U : I ∈ U :=
      hU_ball (by simp [Metric.mem_ball, Complex.norm_I])
    -- -I ∈ U
    have h_neg_I_in_U : -I ∈ U :=
      hU_ball (by simp [Metric.mem_ball, norm_neg, Complex.norm_I])
    -- (f) F = 0 on U by identity theorem: F = 0 on U ∩ LHP (open, nonempty)
    have hF_zero_on_U : ∀ w ∈ U, F w = 0 := by
      have hU_conn : IsConnected U :=
        ⟨⟨I, hI_in_U⟩, hU_conv.isPreconnected⟩
      -- F = 0 on U ∩ LHP, so F = 0 frequently near -I
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
    -- (g) g(I) = F(I) = 0
    have hI_UHP : I.im > 0 := by simp [Complex.I_im]
    rw [← hF_plus I ⟨hI_in_U, hI_UHP⟩]
    exact hF_zero_on_U I hI_in_U
  exact sub_eq_zero.mp hG_zero

/-! ### Axiom 2: Polynomial Growth Estimates -/

/-- **Polynomial growth of holomorphic functions on tube domains.**

    If F is holomorphic on a tube domain T(C) with tempered distributional boundary
    values, then F satisfies polynomial growth estimates: for any compact subset
    K ⊂ C of approach directions, there exist C > 0 and N ∈ ℕ such that

        |F(x + iy)| ≤ C · (1 + ‖x‖)^N

    for all x ∈ ℝᵐ and y ∈ K.

    This is the key estimate needed to show that Wick-rotated Wightman functions
    define tempered distributions (OS axiom E0). The polynomial growth follows
    from the Fourier-Laplace representation: the Laplace transform of a tempered
    distribution has at most polynomial growth in the real directions.

    Ref: Streater-Wightman, Theorem 2-6;
    Jost, "The General Theory of Quantized Fields" §III.1;
    Vladimirov §25.3 -/
theorem polynomial_growth_tube {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (TubeDomain C))
    (h_bv : ∀ (η : Fin m → ℝ), η ∈ C →
      ∃ (T : (Fin m → ℝ) → ℂ), ContinuousOn T Set.univ ∧
        ∀ (f : (Fin m → ℝ) → ℂ), MeasureTheory.Integrable f →
          Filter.Tendsto (fun ε : ℝ =>
            ∫ x : Fin m → ℝ, F (fun i => ↑(x i) + ↑ε * ↑(η i) * I) * f x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (∫ x, T x * f x)))
    (K : Set (Fin m → ℝ)) (hK : IsCompact K) (hK_sub : K ⊆ C) :
    ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
      ∀ (x : Fin m → ℝ) (y : Fin m → ℝ), y ∈ K →
        ‖F (fun i => ↑(x i) + ↑(y i) * I)‖ ≤ C_bd * (1 + ‖x‖) ^ N := by
  exact polynomial_growth_of_continuous_bv hC hconv hne hF h_bv K hK hK_sub

/-! ### Axiom 3: Bochner Tube Theorem -/

/-- **Bochner's tube theorem (convex hull extension).**

    If F is holomorphic on a tube domain T(C) = ℝᵐ + iC, then F extends to a
    unique holomorphic function on T(conv C) = ℝᵐ + i(conv C), where conv C
    is the convex hull of C.

    This is a fundamental result in several complex variables: holomorphic functions
    on tube domains automatically extend to the convex hull of the base.

    In the OS reconstruction, this is used after the inductive analytic continuation
    (which produces holomorphicity on a tube over the positive orthant) to extend
    to the full forward tube (a tube over V₊, the forward light cone). The key:
    the union of SO(d+1)-rotations of the positive orthant covers V₊, and
    V₊ = conv(⋃_R R · (0,∞)^{d+1}) since V₊ is convex.

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
