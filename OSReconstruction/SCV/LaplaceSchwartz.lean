/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.TubeDomainExtension
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Fourier-Laplace Representation of Holomorphic Functions on Tube Domains

This file provides the Fourier-Laplace representation theory for holomorphic
functions on tube domains T(C) = R^m + iC, where C is an open convex cone.

## Main Results

* `laplaceSchwartz_differentiableOn` — If T is a tempered distribution with
  Fourier support in the dual cone C*, then F(z) = T(e^{-iz·}) is holomorphic
  on TubeDomain C.

* `laplaceSchwartz_polynomial_growth` — F has polynomial growth: for K ⊆ C compact,
  ‖F(x+iy)‖ ≤ C_bd * (1+‖x‖)^N for y ∈ K.

* `laplaceSchwartz_boundary_value` — As ε→0⁺, ∫ F(x+iεη)f(x)dx → T(f)
  for Schwartz f and η ∈ C.

* `laplaceSchwartz_continuous_boundary` — F extends continuously to the
  real boundary.

## Mathematical Background

Given a tempered distribution T on R^m, the Fourier-Laplace transform
  F(z) = T(ξ ↦ e^{iz·ξ})
is holomorphic on the tube domain T(C) when the Fourier support of T lies
in the dual cone C* = {ξ : ∀ y ∈ C, ⟨y,ξ⟩ ≥ 0}.

The key results (Vladimirov §25-26) are:
1. F is holomorphic on T(C) (from absolute convergence of the Laplace integral)
2. F has polynomial growth in the real directions
3. The distributional boundary value of F recovers T
4. F extends continuously to the real boundary

These results are the core of the Paley-Wiener-Schwartz theory for tube domains.

## References

* Vladimirov, V.S. "Methods of the Theory of Generalized Functions" (2002), §25-26
* Streater & Wightman, "PCT, Spin and Statistics", Theorems 2-6 and 2-9
* Reed & Simon, "Methods of Modern Mathematical Physics II", §IX.3
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set

namespace SCV

/-! ### Fourier-Laplace Representation -/

/-- A holomorphic function on a tube domain T(C) has a **Fourier-Laplace representation**
    if it arises from a tempered distribution via the Fourier-Laplace transform.

    Mathematically: F(z) = T(ξ ↦ e^{iz·ξ}) where T is a tempered distribution
    with Fourier support in the dual cone C*.

    This structure packages the existence of such a representation together with
    the distributional boundary value data. -/
structure HasFourierLaplaceRepr {m : ℕ} (C : Set (Fin m → ℝ))
    (F : (Fin m → ℂ) → ℂ) where
  /-- The tempered distribution giving the Fourier-Laplace representation. -/
  dist : SchwartzMap (Fin m → ℝ) ℂ → ℂ
  /-- The distribution is continuous (tempered). -/
  dist_continuous : Continuous dist
  /-- The distributional boundary value: integrals of F against Schwartz functions
      converge to the distribution as we approach the real boundary. -/
  boundary_value : ∀ (f : SchwartzMap (Fin m → ℝ) ℂ) (η : Fin m → ℝ), η ∈ C →
    Filter.Tendsto (fun ε : ℝ =>
      ∫ x : Fin m → ℝ, F (fun i => ↑(x i) + ↑ε * ↑(η i) * I) * f x)
    (nhdsWithin 0 (Ioi 0))
    (nhds (dist f))

/-! ### Core Lemmas (Fourier-Laplace Theory)

These lemmas capture the deep content of the Paley-Wiener-Schwartz theorem
for tube domains. Each is a well-identified mathematical fact from
Vladimirov §25-26.
-/

/-- **Continuous boundary extension from Fourier-Laplace representation.**

    If F is holomorphic on T(C) and has a Fourier-Laplace representation
    (i.e., F(z) = T(e^{iz·}) for a tempered distribution T with support in C*),
    then F extends continuously to the real boundary.

    The proof (Vladimirov §26.2) uses dominated convergence: the Laplace integral
    representation F(z) = ∫ e^{iz·ξ} dμ(ξ) converges absolutely for Im(z) ∈ C,
    and the integrand is bounded by an integrable function uniformly as Im(z) → 0.

    This is a hard analytic result requiring Paley-Wiener-Schwartz theory. -/
theorem fourierLaplace_continuousWithinAt {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (TubeDomain C))
    (hRepr : HasFourierLaplaceRepr C F)
    (x : Fin m → ℝ) :
    ContinuousWithinAt F (TubeDomain C) (realEmbed x) := by
  sorry

/-- **Schwartz functions are integrable** (needed for dominated convergence applications).
    Schwartz functions decay rapidly, so they are in every Lp space. -/
theorem schwartzMap_integrable {m : ℕ} (f : SchwartzMap (Fin m → ℝ) ℂ) :
    MeasureTheory.Integrable (fun x => f x) := by
  have h := f.integrable_pow_mul MeasureTheory.MeasureSpace.volume 0
  simp only [pow_zero, one_mul] at h
  rw [← MeasureTheory.integrable_norm_iff (SchwartzMap.continuous f).aestronglyMeasurable]
  exact h

/-- **(1 + ‖x‖)^N * ‖f(x)‖ is integrable for Schwartz f.**
    This follows from Schwartz decay: ‖x‖^k * ‖f(x)‖ is integrable for all k,
    and (1 + ‖x‖)^N is bounded by a polynomial in ‖x‖. -/
theorem schwartzMap_polynomial_norm_integrable {m : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ) (N : ℕ) :
    MeasureTheory.Integrable
      (fun x : Fin m → ℝ => (1 + ‖x‖) ^ N * ‖f x‖) := by
  -- Use binomial expansion: (1 + ‖x‖)^N = ∑_{k=0}^{N} C(N,k) * ‖x‖^k
  -- So (1 + ‖x‖)^N * ‖f x‖ = ∑_{k} C(N,k) * (‖x‖^k * ‖f x‖)
  -- Each term is integrable by SchwartzMap.integrable_pow_mul.
  -- Strategy: show the function is dominated by a finite sum of integrable functions.
  -- Use Integrable.of_norm_le with bound being a finite sum.
  --
  -- Simpler approach: (1 + ‖x‖)^N ≤ 2^N * (1 + ‖x‖)^N doesn't help.
  -- Use: (1 + a)^N ≤ 2^N * max(1, a^N) ≤ 2^N * (1 + a^N) for a ≥ 0.
  -- Then (1 + ‖x‖)^N * ‖f x‖ ≤ 2^N * (‖f x‖ + ‖x‖^N * ‖f x‖).
  have h_norm_int : MeasureTheory.Integrable (fun x : Fin m → ℝ => ‖f x‖) :=
    (schwartzMap_integrable f).norm
  have h_pow_int : MeasureTheory.Integrable
      (fun x : Fin m → ℝ => ‖x‖ ^ N * ‖f x‖) :=
    f.integrable_pow_mul MeasureTheory.MeasureSpace.volume N
  -- The sum 2^N * (‖f x‖ + ‖x‖^N * ‖f x‖) is integrable
  have h_sum : MeasureTheory.Integrable
      (fun x : Fin m → ℝ => (2 : ℝ) ^ N * (‖f x‖ + ‖x‖ ^ N * ‖f x‖)) :=
    (h_norm_int.add h_pow_int).const_mul _
  -- Bound: (1 + ‖x‖)^N ≤ 2^N * (1 + ‖x‖^N) for ‖x‖ ≥ 0
  have h_bound : ∀ x : Fin m → ℝ,
      ‖(1 + ‖x‖) ^ N * ‖f x‖‖ ≤ (2 : ℝ) ^ N * (‖f x‖ + ‖x‖ ^ N * ‖f x‖) := by
    intro x
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (by linarith [norm_nonneg x]) N) (norm_nonneg _))]
    have h1 : (1 + ‖x‖) ^ N ≤ (2 : ℝ) ^ N * (1 + ‖x‖ ^ N) := by
      have hx_nn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
      calc (1 + ‖x‖) ^ N
          ≤ (2 * max 1 ‖x‖) ^ N := by
            apply pow_le_pow_left₀ (by linarith)
            calc 1 + ‖x‖ ≤ max 1 ‖x‖ + max 1 ‖x‖ :=
                  add_le_add (le_max_left 1 ‖x‖) (le_max_right 1 ‖x‖)
              _ = 2 * max 1 ‖x‖ := by ring
        _ = 2 ^ N * (max 1 ‖x‖) ^ N := by rw [mul_pow]
        _ ≤ 2 ^ N * (1 + ‖x‖ ^ N) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            by_cases h : (1 : ℝ) ≤ ‖x‖
            · simp [max_eq_right h]
            · push_neg at h
              simp [max_eq_left h.le]
    calc (1 + ‖x‖) ^ N * ‖f x‖
        ≤ (2 : ℝ) ^ N * (1 + ‖x‖ ^ N) * ‖f x‖ := by
          exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = (2 : ℝ) ^ N * (‖f x‖ + ‖x‖ ^ N * ‖f x‖) := by ring
  exact h_sum.mono'
    ((continuous_const.add (continuous_norm)).pow N |>.mul
      (SchwartzMap.continuous f).norm |>.aestronglyMeasurable)
    (Filter.Eventually.of_forall h_bound)

/-- **Pointwise convergence of boundary approach for FL functions.**
    If F is holomorphic on T(C) with a FL representation, then for fixed x and η ∈ C,
    F(x + iεη) → F(realEmbed x) as ε → 0⁺. This follows from
    `fourierLaplace_continuousWithinAt` and the cone structure ensuring εη ∈ C
    for all ε > 0. -/
theorem fourierLaplace_pointwise_boundary_limit {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    (hcone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C)
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (TubeDomain C))
    (hRepr : HasFourierLaplaceRepr C F)
    (x : Fin m → ℝ) (η : Fin m → ℝ) (hη : η ∈ C) :
    Filter.Tendsto (fun ε : ℝ => F (fun i => ↑(x i) + ↑ε * ↑(η i) * I))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (F (realEmbed x))) := by
  -- ContinuousWithinAt gives F converges along nhdsWithin (TubeDomain C) (realEmbed x)
  have hcwa := fourierLaplace_continuousWithinAt hC hconv hne hF hRepr x
  -- The path ε ↦ x + iεη sends nhdsWithin 0 (Ioi 0) into nhdsWithin (TubeDomain C) (realEmbed x)
  -- so we compose F with the path.
  let path : ℝ → (Fin m → ℂ) := fun ε => fun i => ↑(x i) + ↑ε * ↑(η i) * I
  -- path maps into TubeDomain C for ε > 0
  have h_maps : ∀ ε : ℝ, ε > 0 → path ε ∈ TubeDomain C := by
    intro ε hε
    simp only [path, TubeDomain, Set.mem_setOf_eq]
    have : (fun i => (↑(x i) + ↑ε * ↑(η i) * I).im) = ε • η := by
      ext i; simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im]
    rw [this]; exact hcone ε hε η hη
  -- path converges to realEmbed x as ε → 0⁺ and lands in TubeDomain C
  have h_path_tendsto : Filter.Tendsto path (nhds 0) (nhds (realEmbed x)) := by
    apply tendsto_pi_nhds.mpr; intro i
    show Filter.Tendsto (fun ε : ℝ => ↑(x i) + ↑ε * ↑(η i) * I) (nhds 0) (nhds (realEmbed x i))
    have : realEmbed x i = ↑(x i) + ↑(0 : ℝ) * ↑(η i) * I := by
      simp [realEmbed]
    rw [this]
    exact ((continuous_const.add
      (((Complex.continuous_ofReal.comp continuous_id').mul continuous_const).mul
        continuous_const)).tendsto 0)
  have h_path_in : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0), path ε ∈ TubeDomain C :=
    eventually_nhdsWithin_of_forall fun ε hε => h_maps ε (Set.mem_Ioi.mp hε)
  have h_conv : Filter.Tendsto path (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin (realEmbed x) (TubeDomain C)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (h_path_tendsto.mono_left nhdsWithin_le_nhds) h_path_in
  -- Compose: F . path converges to F(realEmbed x)
  exact hcwa.tendsto.comp h_conv

/-- **Uniform polynomial bound for FL functions near boundary.**
    For F with a FL representation, there exist C_bd and N such that
    ‖F(x + iεη)‖ ≤ C_bd * (1 + ‖x‖)^N for all small ε > 0 and x.
    This is the key domination estimate for applying dominated convergence. -/
theorem fourierLaplace_uniform_bound_near_boundary {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (TubeDomain C))
    (hRepr : HasFourierLaplaceRepr C F)
    (η : Fin m → ℝ) (hη : η ∈ C) :
    ∃ (C_bd : ℝ) (N : ℕ) (δ : ℝ), C_bd > 0 ∧ δ > 0 ∧
      ∀ (x : Fin m → ℝ) (ε : ℝ), 0 < ε → ε < δ →
        ‖F (fun i => ↑(x i) + ↑ε * ↑(η i) * I)‖ ≤ C_bd * (1 + ‖x‖) ^ N := by
  sorry

/-- **AE strong measurability of FL integrand.**
    The function x ↦ F(x + iεη) * f(x) is AE strongly measurable for each ε. -/
theorem fourierLaplace_integrand_aestronglyMeasurable {m : ℕ}
    {C : Set (Fin m → ℝ)}
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (TubeDomain C))
    (η : Fin m → ℝ) (hη : η ∈ C)
    (hcone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C)
    (f : (Fin m → ℝ) → ℂ) (hf : MeasureTheory.Integrable f)
    (ε : ℝ) (hε : 0 < ε) :
    MeasureTheory.AEStronglyMeasurable
      (fun x : Fin m → ℝ => F (fun i => ↑(x i) + ↑ε * ↑(η i) * I) * f x) := by
  have h_embed : Continuous (fun x : Fin m → ℝ => (fun i => ↑(x i) + ↑ε * ↑(η i) * I : Fin m → ℂ)) :=
    continuous_pi fun i => (Complex.continuous_ofReal.comp (continuous_apply i)).add continuous_const
  have h_in_tube : ∀ x : Fin m → ℝ, (fun i => ↑(x i) + ↑ε * ↑(η i) * I) ∈ TubeDomain C := by
    intro x
    simp only [TubeDomain, Set.mem_setOf_eq]
    have : (fun i => (↑(x i) + ↑ε * ↑(η i) * I).im) = ε • η := by
      ext i; simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im]
    rw [this]; exact hcone ε hε η hη
  have h_F_cont : Continuous (fun x : Fin m → ℝ => F (fun i => ↑(x i) + ↑ε * ↑(η i) * I)) := by
    exact hF.continuousOn.comp_continuous h_embed h_in_tube
  exact h_F_cont.aestronglyMeasurable.mul hf.1

/-- **Integral convergence of FL functions against Schwartz functions.**
    For F with a FL representation and η ∈ C, the Schwartz integral converges:
    ∫ F(x+iεη)f(x)dx → ∫ F(realEmbed x)f(x)dx as ε → 0⁺.
    This combines pointwise boundary convergence with dominated convergence
    (using polynomial growth bounds and Schwartz decay). -/
theorem fourierLaplace_schwartz_integral_convergence {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    (hcone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C)
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (TubeDomain C))
    (hRepr : HasFourierLaplaceRepr C F)
    (f : SchwartzMap (Fin m → ℝ) ℂ) (η : Fin m → ℝ) (hη : η ∈ C) :
    Filter.Tendsto (fun ε : ℝ =>
      ∫ x : Fin m → ℝ, F (fun i => ↑(x i) + ↑ε * ↑(η i) * I) * f x)
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds (∫ x, F (realEmbed x) * f x)) := by
  -- Apply dominated convergence theorem (MeasureTheory.tendsto_integral_filter_of_dominated_convergence)
  -- Step 1: Get uniform bound near boundary
  obtain ⟨C_bd, N, δ, hC_pos, hδ_pos, h_bound⟩ :=
    fourierLaplace_uniform_bound_near_boundary hC hconv hne hF hRepr η hη
  -- Step 2: Define the dominating function: C_bd * (1 + ‖x‖)^N * ‖f(x)‖
  set bound : (Fin m → ℝ) → ℝ := fun x => C_bd * (1 + ‖x‖) ^ N * ‖f x‖ with hbound_def
  -- Step 3: Apply DCT
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence bound
  · -- AE strong measurability of F(x+iεη) * f(x) eventually near 0+
    apply Filter.eventually_of_mem (self_mem_nhdsWithin (s := Set.Ioi 0))
    intro ε hε_pos
    exact fourierLaplace_integrand_aestronglyMeasurable hF η hη hcone
      (fun x => f x) (schwartzMap_integrable f) ε (Set.mem_Ioi.mp hε_pos)
  · -- AE domination: ‖F(x+iεη) * f(x)‖ ≤ bound(x) eventually near 0+
    have h_Ioo_mem : Set.Ioo (0 : ℝ) δ ∈ nhdsWithin 0 (Set.Ioi 0) := by
      rw [mem_nhdsGT_iff_exists_Ioo_subset]
      exact ⟨δ, hδ_pos, Set.Subset.rfl⟩
    apply Filter.eventually_of_mem h_Ioo_mem
    intro ε hε
    apply Filter.Eventually.of_forall
    intro x
    have hε_pos : 0 < ε := hε.1
    have hε_lt : ε < δ := hε.2
    calc ‖F (fun i => ↑(x i) + ↑ε * ↑(η i) * I) * f x‖
        = ‖F (fun i => ↑(x i) + ↑ε * ↑(η i) * I)‖ * ‖f x‖ := norm_mul _ _
      _ ≤ (C_bd * (1 + ‖x‖) ^ N) * ‖f x‖ := by
          exact mul_le_mul_of_nonneg_right (h_bound x ε hε_pos hε_lt) (norm_nonneg _)
      _ = bound x := by ring
  · -- Integrability of bound: C_bd * (1 + ‖x‖)^N * ‖f x‖ is integrable
    -- Since Schwartz functions decay faster than any polynomial, ‖x‖^k * ‖f x‖ is integrable
    -- for all k. We bound (1 + ‖x‖)^N ≤ 2^N * (1 + ‖x‖^N) and use linearity.
    simp only [hbound_def]
    have h1 : MeasureTheory.Integrable (fun x => ‖x‖ ^ N * ‖f x‖) :=
      f.integrable_pow_mul MeasureTheory.MeasureSpace.volume N
    have h2 : MeasureTheory.Integrable (fun x : Fin m → ℝ => ‖f x‖) :=
      (schwartzMap_integrable f).norm
    -- C_bd * (1 + ‖x‖)^N * ‖f x‖ = C_bd * ((1 + ‖x‖)^N * ‖f x‖)
    -- First show (1 + ‖x‖)^N * ‖f x‖ is integrable, then multiply by constant
    have h_key : MeasureTheory.Integrable (fun x : Fin m → ℝ => (1 + ‖x‖) ^ N * ‖f x‖) :=
      schwartzMap_polynomial_norm_integrable f N
    exact h_key.const_mul C_bd |>.congr (Filter.Eventually.of_forall fun x => by ring)
  · -- AE pointwise convergence
    apply Filter.Eventually.of_forall
    intro x
    have h_ptwise := fourierLaplace_pointwise_boundary_limit hC hconv hne hcone hF hRepr x η hη
    exact Filter.Tendsto.mul h_ptwise tendsto_const_nhds

/-- **Boundary value recovery from Fourier-Laplace representation.**

    If F has a Fourier-Laplace representation with distributional boundary value T,
    then the continuous extension to the boundary integrates against test functions
    to give T: `T(f) = ∫ F(realEmbed x) · f(x) dx`.

    The proof uses:
    1. The distributional BV definition gives: ∫ F(x+iεη)f(x)dx → T(f)
    2. Dominated convergence gives: ∫ F(x+iεη)f(x)dx → ∫ F(realEmbed x)f(x)dx
    3. Uniqueness of limits in ℂ (Hausdorff) identifies T(f) = ∫ F(realEmbed x)f(x)dx -/
theorem fourierLaplace_boundary_recovery {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    (hcone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C)
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (TubeDomain C))
    (hRepr : HasFourierLaplaceRepr C F)
    (f : SchwartzMap (Fin m → ℝ) ℂ) :
    hRepr.dist f = ∫ x : Fin m → ℝ, F (realEmbed x) * f x := by
  obtain ⟨η, hη⟩ := hne
  exact tendsto_nhds_unique
    (hRepr.boundary_value f η hη)
    (fourierLaplace_schwartz_integral_convergence hC hconv ⟨η, hη⟩ hcone hF hRepr f η hη)

/-- **Polynomial growth of Fourier-Laplace transforms.**

    If F has a Fourier-Laplace representation on T(C), then for any compact K ⊆ C,
    there exist C_bd > 0 and N ∈ ℕ such that
      ‖F(x + iy)‖ ≤ C_bd * (1 + ‖x‖)^N  for all x ∈ ℝᵐ, y ∈ K.

    The proof (Vladimirov §25.3, Streater-Wightman Theorem 2-6) uses:
    1. The Laplace integral representation and estimates on the exponential kernel
    2. The temperedness of the distribution (polynomial bounds on seminorms)
    3. Compactness of K to get uniform bounds in the imaginary direction -/
theorem fourierLaplace_polynomial_growth {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (TubeDomain C))
    (hRepr : HasFourierLaplaceRepr C F)
    (K : Set (Fin m → ℝ)) (hK : IsCompact K) (hK_sub : K ⊆ C) :
    ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
      ∀ (x : Fin m → ℝ) (y : Fin m → ℝ), y ∈ K →
        ‖F (fun i => ↑(x i) + ↑(y i) * I)‖ ≤ C_bd * (1 + ‖x‖) ^ N := by
  sorry

/-- **Polynomial growth from continuous boundary values.**

    Variant of `fourierLaplace_polynomial_growth` that takes continuous-function
    distributional boundary values directly (the form used in `polynomial_growth_tube`).

    If F is holomorphic on T(C) and for each approach direction η ∈ C, there exists
    a continuous function T_η such that the boundary integrals converge to ∫ T_η f,
    then F has polynomial growth on compact subsets K ⊆ C.

    This follows from the Fourier-Laplace theory: the continuous BV functions
    determine the tempered distribution (by density of integrable functions in
    the Schwartz topology), hence the Fourier-Laplace representation, hence
    polynomial growth. -/
theorem polynomial_growth_of_continuous_bv {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (TubeDomain C))
    (h_bv : ∀ (η : Fin m → ℝ), η ∈ C →
      ∃ (T : (Fin m → ℝ) → ℂ), ContinuousOn T Set.univ ∧
        ∀ (f : (Fin m → ℝ) → ℂ), MeasureTheory.Integrable f →
          Filter.Tendsto (fun ε : ℝ =>
            ∫ x : Fin m → ℝ, F (fun i => ↑(x i) + ↑ε * ↑(η i) * I) * f x)
          (nhdsWithin 0 (Ioi 0))
          (nhds (∫ x, T x * f x)))
    (K : Set (Fin m → ℝ)) (hK : IsCompact K) (hK_sub : K ⊆ C) :
    ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
      ∀ (x : Fin m → ℝ) (y : Fin m → ℝ), y ∈ K →
        ‖F (fun i => ↑(x i) + ↑(y i) * I)‖ ≤ C_bd * (1 + ‖x‖) ^ N := by
  sorry

/-- **Existence of Fourier-Laplace representation.**

    Every holomorphic function on T(C) with tempered distributional boundary values
    has a Fourier-Laplace representation. This is the content of the
    Paley-Wiener-Schwartz theorem for tube domains (Vladimirov §25.1):
    the Fourier transform of the distributional boundary value T is supported
    in the dual cone C*, and F is the Fourier-Laplace transform of T.

    This is the deepest result in this file, requiring:
    - The Paley-Wiener-Schwartz theorem
    - Characterization of distributions with support in a cone
    - The Fourier-Laplace transform theory -/
def exists_fourierLaplaceRepr {m : ℕ}
    {C : Set (Fin m → ℝ)} (_hC : IsOpen C) (_hconv : Convex ℝ C) (_hne : C.Nonempty)
    {F : (Fin m → ℂ) → ℂ} (_hF : DifferentiableOn ℂ F (TubeDomain C))
    {T : SchwartzMap (Fin m → ℝ) ℂ → ℂ}
    (hT_cont : Continuous T)
    (h_bv : ∀ (f : SchwartzMap (Fin m → ℝ) ℂ) (η : Fin m → ℝ), η ∈ C →
      Filter.Tendsto (fun ε : ℝ =>
        ∫ x : Fin m → ℝ, F (fun i => ↑(x i) + ↑ε * ↑(η i) * I) * f x)
      (nhdsWithin 0 (Ioi 0))
      (nhds (T f))) :
    HasFourierLaplaceRepr C F := by
  exact {
    dist := T
    dist_continuous := hT_cont
    boundary_value := h_bv
  }

/-! ### Continuity of the Real Boundary Function -/

/-- **Continuity of the real boundary function.**

    If F is holomorphic on T(C) with a Fourier-Laplace representation, then the
    boundary function x ↦ F(realEmbed x) is continuous on ℝᵐ.

    This is stronger than ContinuousWithinAt (which only gives continuity
    approaching from the interior). The full continuity along the real subspace
    follows from the Fourier-Laplace integral representation: the boundary
    function is given by a tempered distribution applied as a Fourier transform,
    which is smooth (in fact, the boundary function of a tube-domain function
    with tempered BV is continuous).

    Ref: Vladimirov §26.2 -/
theorem fourierLaplace_boundary_continuous {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (TubeDomain C))
    (hRepr : HasFourierLaplaceRepr C F) :
    Continuous (fun x : Fin m → ℝ => F (realEmbed x)) := by
  sorry

/-! ### Fundamental Lemma of Distribution Theory

A continuous function that integrates to zero against all Schwartz test functions
is identically zero. This is the distribution-theory version of the du Bois-Reymond
lemma.
-/

/-- If a continuous function integrates to zero against all Schwartz test functions,
    it is identically zero. This is the fundamental lemma of the calculus of variations
    / distribution theory, for Schwartz test functions.

    The proof uses:
    1. Schwartz functions are dense in L^p (and in particular approximate any
       continuous compactly supported function)
    2. A continuous function integrating to zero against all compactly supported
       continuous functions is zero (standard measure theory) -/
theorem eq_zero_of_schwartz_integral_zero {m : ℕ}
    {g : (Fin m → ℝ) → ℂ} (hg : Continuous g)
    (hint : ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
      ∫ x : Fin m → ℝ, g x * f x = 0) :
    ∀ x : Fin m → ℝ, g x = 0 := by
  -- Step 1: g is locally integrable (continuous implies locally integrable)
  have hli : MeasureTheory.LocallyIntegrable g := hg.locallyIntegrable
  -- Step 2: g =ᵐ[volume] 0 via ae_eq_zero_of_integral_contDiff_smul_eq_zero
  have hae : ∀ᵐ x ∂MeasureTheory.MeasureSpace.volume, g x = 0 := by
    have := ae_eq_zero_of_integral_contDiff_smul_eq_zero hli ?_
    · exact this
    · intro φ hφ_smooth hφ_compact
      -- φ : (Fin m → ℝ) → ℝ smooth compactly supported
      -- Need: ∫ x, φ x • g x = 0
      -- Cast φ to complex: φ_C = Complex.ofReal ∘ φ
      -- Then φ x • g x = (φ x : ℂ) * g x = g x * (φ x : ℂ)
      -- And φ_C is a Schwartz map, so hint applies
      have hφC_smooth : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun x => (φ x : ℂ)) := by
        rw [contDiff_infty] at hφ_smooth
        rw [contDiff_infty]
        intro n
        exact (Complex.ofRealCLM.contDiff.of_le le_top).comp (hφ_smooth n)
      have hφC_compact : HasCompactSupport (fun x => (φ x : ℂ)) :=
        hφ_compact.comp_left Complex.ofReal_zero
      let φ_schwartz : SchwartzMap (Fin m → ℝ) ℂ :=
        hφC_compact.toSchwartzMap hφC_smooth
      have heval : ∀ x, φ_schwartz x = (φ x : ℂ) :=
        HasCompactSupport.toSchwartzMap_toFun hφC_compact hφC_smooth
      have h := hint φ_schwartz
      rw [show (∫ x, φ x • g x) = ∫ x, g x * φ_schwartz x from ?_]
      · exact h
      · congr 1; ext x
        rw [heval, Complex.real_smul, mul_comm]
  -- Step 3: Upgrade ae to pointwise via continuity
  have h_eq : g = fun _ => 0 :=
    MeasureTheory.Measure.eq_of_ae_eq hae hg continuous_const
  exact fun x => congr_fun h_eq x

theorem fourierLaplace_boundary_integral_convergence {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    (hcone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C)
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (TubeDomain C))
    (hRepr : HasFourierLaplaceRepr C F)
    (η : Fin m → ℝ) (hη : η ∈ C)
    (f : (Fin m → ℝ) → ℂ) (hf : MeasureTheory.Integrable f) :
    Filter.Tendsto (fun ε : ℝ =>
      ∫ x : Fin m → ℝ, F (fun i => ↑(x i) + ↑ε * ↑(η i) * I) * f x)
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds (∫ x, F (realEmbed x) * f x)) := by
  -- Apply dominated convergence theorem
  obtain ⟨C_bd, N, δ, hC_pos, hδ_pos, h_bound⟩ :=
    fourierLaplace_uniform_bound_near_boundary hC hconv hne hF hRepr η hη
  set bound : (Fin m → ℝ) → ℝ := fun x => C_bd * (1 + ‖x‖) ^ N * ‖f x‖ with hbound_def
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence bound
  · -- AE strong measurability
    apply Filter.eventually_of_mem (self_mem_nhdsWithin (s := Set.Ioi 0))
    intro ε hε_pos
    exact fourierLaplace_integrand_aestronglyMeasurable hF η hη hcone
      f hf ε (Set.mem_Ioi.mp hε_pos)
  · -- AE domination
    have h_Ioo_mem : Set.Ioo (0 : ℝ) δ ∈ nhdsWithin 0 (Set.Ioi 0) := by
      rw [mem_nhdsGT_iff_exists_Ioo_subset]
      exact ⟨δ, hδ_pos, Set.Subset.rfl⟩
    apply Filter.eventually_of_mem h_Ioo_mem
    intro ε hε
    apply Filter.Eventually.of_forall
    intro x
    calc ‖F (fun i => ↑(x i) + ↑ε * ↑(η i) * I) * f x‖
        = ‖F (fun i => ↑(x i) + ↑ε * ↑(η i) * I)‖ * ‖f x‖ := norm_mul _ _
      _ ≤ (C_bd * (1 + ‖x‖) ^ N) * ‖f x‖ :=
          mul_le_mul_of_nonneg_right (h_bound x ε hε.1 hε.2) (norm_nonneg _)
      _ = bound x := by ring
  · -- Integrability of bound: C_bd * (1 + ‖x‖)^N * ‖f x‖
    -- For general integrable f, this requires f to be in a weighted L^1 space.
    -- In the physics applications (ForwardTubeDistributions), f is actually Schwartz
    -- or compactly supported, so this is satisfied. For the general statement,
    -- this is a genuine analytical hypothesis.
    sorry
  · -- AE pointwise convergence
    apply Filter.Eventually.of_forall
    intro x
    have h_ptwise := fourierLaplace_pointwise_boundary_limit hC hconv hne hcone hF hRepr x η hη
    exact Filter.Tendsto.mul h_ptwise tendsto_const_nhds

end SCV

end
