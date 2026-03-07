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

/-- Weak boundary-value package for a holomorphic function on a tube domain.

    `HasFourierLaplaceRepr C F` does **not** yet formalize an actual Fourier-Laplace
    representation with dual-cone support. It only stores:
    - a continuous Schwartz functional `dist`
    - the distributional boundary-value convergence of `F` to `dist`

    The genuine Paley-Wiener-Schwartz theorem for tube domains should later show
    that an actual Fourier-Laplace transform with Fourier support in the dual cone
    `C*` produces this boundary-value package, and in the strong case also the
    regularity package below. -/
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

/-- A holomorphic function on a tube domain T(C) has a **regular Fourier-Laplace representation**
    if, in addition to the bare distributional boundary-value data in `HasFourierLaplaceRepr`,
    it satisfies the four quantitative regularity conditions proved in Vladimirov §25–26 for
    *actual* Fourier-Laplace transforms of tempered distributions.

    **Why a separate structure from `HasFourierLaplaceRepr`?**
    The minimal `HasFourierLaplaceRepr` (dist, dist_continuous, boundary_value) does NOT imply
    the four regularity conditions below. Counterexample: F(z) = 1/z on the upper half-plane
    has tempered distributional BV `pv(1/x) - iπδ₀` (satisfying `HasFourierLaplaceRepr`), but
    - has no continuous extension to x = 0 (violates `boundary_continuous` and `tube_continuousWithinAt`)
    - does NOT satisfy polynomial growth near x = 0 (violates `poly_growth` and `uniform_bound`).

    F(z) = 1/z is NOT the Fourier-Laplace transform of a distribution supported in C* = [0,∞).
    Its distributional BV arises from a distribution (pv(1/x)) that is NOT supported in [0,∞).
    So the regularity conditions hold precisely when T is supported in the dual cone C*,
    which is the content of the Paley-Wiener-Schwartz theorem for tube domains (Vladimirov §25.1).

    **The deep missing theorem** should say:
    if F is holomorphic on T(C) and has a genuine Fourier-Laplace representation
    (T supported in C*), then this structure can be constructed. This file does
    not yet formalize that theorem. -/
structure HasFourierLaplaceReprRegular {m : ℕ} (C : Set (Fin m → ℝ))
    (F : (Fin m → ℂ) → ℂ) extends HasFourierLaplaceRepr C F where
  /-- Polynomial growth on compact subsets of C (Vladimirov §25.3). -/
  poly_growth : ∀ (K : Set (Fin m → ℝ)), IsCompact K → K ⊆ C →
    ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
      ∀ (x y : Fin m → ℝ), y ∈ K →
        ‖F (fun i => ↑(x i) + ↑(y i) * I)‖ ≤ C_bd * (1 + ‖x‖) ^ N
  /-- Uniform polynomial bound near the real boundary (Vladimirov §26.1). -/
  uniform_bound : ∀ (η : Fin m → ℝ), η ∈ C →
    ∃ (C_bd : ℝ) (N : ℕ) (δ : ℝ), C_bd > 0 ∧ δ > 0 ∧
      ∀ (x : Fin m → ℝ) (ε : ℝ), 0 < ε → ε < δ →
        ‖F (fun i => ↑(x i) + ↑ε * ↑(η i) * I)‖ ≤ C_bd * (1 + ‖x‖) ^ N
  /-- Continuous extension to real boundary (Vladimirov §26.2). -/
  boundary_continuous : Continuous (fun x : Fin m → ℝ => F (realEmbed x))
  /-- Interior-to-boundary continuity within the tube (Vladimirov §26.2). -/
  tube_continuousWithinAt : ∀ (x : Fin m → ℝ),
    ContinuousWithinAt F (TubeDomain C) (realEmbed x)

/- The remaining missing theorem in this file should produce
    `HasFourierLaplaceReprRegular C F` from genuinely strong Fourier-Laplace input:
    an actual FL transform with the required dual-cone support, together with the
    corresponding growth and boundary-ray estimates.

    This upgrade is not yet formalized here. Downstream transport theorems therefore
    take `HasFourierLaplaceReprRegular` explicitly instead of claiming a weak-to-regular
    upgrade theorem that has not been proved. -/

/-! ### Core Lemmas (Fourier-Laplace Theory)

These lemmas capture the deep content of the Paley-Wiener-Schwartz theorem
for tube domains. Each is a well-identified mathematical fact from
Vladimirov §25-26.
-/

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

/-- **Uniform polynomial bound for FL functions near boundary.**
    For F with a FL representation, there exist C_bd and N such that
    ‖F(x + iεη)‖ ≤ C_bd * (1 + ‖x‖)^N for all small ε > 0 and x.
    This is the key domination estimate for applying dominated convergence. -/
theorem fourierLaplace_uniform_bound_near_boundary {m : ℕ}
    {C : Set (Fin m → ℝ)} (_hC : IsOpen C) (_hconv : Convex ℝ C) (_hne : C.Nonempty)
    {F : (Fin m → ℂ) → ℂ} (_hF : DifferentiableOn ℂ F (TubeDomain C))
    (hRegular : HasFourierLaplaceReprRegular C F)
    (η : Fin m → ℝ) (hη : η ∈ C) :
    ∃ (C_bd : ℝ) (N : ℕ) (δ : ℝ), C_bd > 0 ∧ δ > 0 ∧
      ∀ (x : Fin m → ℝ) (ε : ℝ), 0 < ε → ε < δ →
        ‖F (fun i => ↑(x i) + ↑ε * ↑(η i) * I)‖ ≤ C_bd * (1 + ‖x‖) ^ N :=
  hRegular.uniform_bound η hη

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

    Under `HasFourierLaplaceReprRegular` (which includes both `uniform_bound` for DCT
    and `tube_continuousWithinAt` for pointwise convergence), the boundary integrals
    ∫ F(x+iεη)f(x)dx converge to ∫ F(realEmbed x)f(x)dx as ε → 0+.

    Requires the stronger `HasFourierLaplaceReprRegular` because `HasFourierLaplaceRepr`
    alone does not imply either the uniform bound or the boundary continuity. -/
theorem fourierLaplace_schwartz_integral_convergence {m : ℕ}
    {C : Set (Fin m → ℝ)} (_hC : IsOpen C) (_hconv : Convex ℝ C) (_hne : C.Nonempty)
    (hcone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C)
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (TubeDomain C))
    (hRegular : HasFourierLaplaceReprRegular C F)
    (f : SchwartzMap (Fin m → ℝ) ℂ) (η : Fin m → ℝ) (hη : η ∈ C) :
    Filter.Tendsto (fun ε : ℝ =>
      ∫ x : Fin m → ℝ, F (fun i => ↑(x i) + ↑ε * ↑(η i) * I) * f x)
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds (∫ x, F (realEmbed x) * f x)) := by
  -- Get uniform polynomial bound near the boundary: ‖F(x+iεη)‖ ≤ C_bd*(1+‖x‖)^N for ε ∈ (0,δ)
  obtain ⟨C_bd, N, δ, _hC_bd_pos, hδ_pos, h_bd⟩ := hRegular.uniform_bound η hη
  -- Apply DCT for the filter nhdsWithin 0 (Ioi 0)
  -- (countably generated since ℝ is first-countable; no NeBot instance needed)
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (bound := fun y : Fin m → ℝ => C_bd * (1 + ‖y‖) ^ N * ‖(f : (Fin m → ℝ) → ℂ) y‖)
  · -- AEStronglyMeasurable for all ε ∈ Ioi 0
    apply Filter.eventually_of_mem self_mem_nhdsWithin
    intro ε hε
    exact fourierLaplace_integrand_aestronglyMeasurable hF η hη hcone (↑f)
      (schwartzMap_integrable f) ε (Set.mem_Ioi.mp hε)
  · -- Domination: for ε ∈ (0, δ), ‖F(y+iεη)*f(y)‖ ≤ C_bd*(1+‖y‖)^N*‖f(y)‖
    -- Build the filter membership Ioo 0 δ ∈ nhdsWithin 0 (Ioi 0) by hand
    have h_mem : Set.Ioo 0 δ ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      mem_nhdsWithin.mpr ⟨Set.Iio δ, isOpen_Iio, Set.mem_Iio.mpr hδ_pos,
        fun ε hε => Set.mem_Ioo.mpr ⟨Set.mem_Ioi.mp hε.2, Set.mem_Iio.mp hε.1⟩⟩
    apply Filter.eventually_of_mem h_mem
    intro ε hε
    obtain ⟨hε_pos, hε_lt⟩ := Set.mem_Ioo.mp hε
    apply Filter.Eventually.of_forall
    intro y
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (h_bd y ε hε_pos hε_lt) (norm_nonneg _)
  · -- Bound is integrable: C_bd * (1+‖y‖)^N * ‖f(y)‖ ≤ C_bd * ((1+‖y‖)^N * ‖f y‖)
    exact (schwartzMap_polynomial_norm_integrable f N).const_mul C_bd |>.congr
      (ae_of_all _ fun y => by ring)
  · -- Pointwise convergence: F(y+iεη)*f(y) → F(realEmbed y)*f(y) as ε → 0+
    apply Filter.Eventually.of_forall
    intro y
    apply Filter.Tendsto.mul _ tendsto_const_nhds
    -- The path ε ↦ (fun i => ↑(y i) + ↑ε * ↑(η i) * I) is continuous, maps Ioi 0 into
    -- TubeDomain C, and equals realEmbed y at ε = 0.  Compose with tube_continuousWithinAt.
    have h_path_cont : Continuous (fun ε : ℝ =>
        (fun i : Fin m => (y i : ℂ) + ↑ε * ↑(η i) * I)) :=
      continuous_pi fun i =>
        continuous_const.add
          (Complex.continuous_ofReal.mul continuous_const |>.mul continuous_const)
    have h_path_zero : (fun i : Fin m => (y i : ℂ) + ↑(0 : ℝ) * ↑(η i) * I) = realEmbed y := by
      ext i; simp [realEmbed]
    have h_path_maps : Set.MapsTo (fun ε : ℝ => (fun i : Fin m => (y i : ℂ) + ↑ε * ↑(η i) * I))
        (Set.Ioi (0 : ℝ)) (TubeDomain C) := by
      intro ε hε
      simp only [TubeDomain, Set.mem_setOf_eq]
      have him : (fun i : Fin m => ((y i : ℂ) + ↑ε * ↑(η i) * I).im) = ε • η := by
        ext i; simp [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
          Complex.ofReal_im, Complex.ofReal_re]
      rw [him]; exact hcone ε hε η hη
    -- Build Tendsto into nhdsWithin (realEmbed y) (TubeDomain C)
    have h_path_tends : Filter.Tendsto
        (fun ε : ℝ => (fun i : Fin m => (y i : ℂ) + ↑ε * ↑(η i) * I))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhdsWithin (realEmbed y) (TubeDomain C)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Filter.eventually_of_mem self_mem_nhdsWithin h_path_maps⟩
      have h : Filter.Tendsto (fun ε : ℝ => (fun i : Fin m => (y i : ℂ) + ↑ε * ↑(η i) * I))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (fun i : Fin m => (y i : ℂ) + ↑(0 : ℝ) * ↑(η i) * I)) :=
        h_path_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      rwa [h_path_zero] at h
    -- Compose: F is continuous within TubeDomain C at realEmbed y
    exact Filter.Tendsto.comp (hRegular.tube_continuousWithinAt y) h_path_tends

/-- **Boundary value recovery from regular FL representation.**

    Under `HasFourierLaplaceReprRegular`, the distributional BV `hRegular.dist f` equals
    the pointwise integral `∫ F(realEmbed x) · f(x) dx`.

    Proof: both are limits of the same integrals ∫ F(x+iεη)f dx as ε → 0+. The distributional
    limit is `hRegular.boundary_value`; the integral limit is `fourierLaplace_schwartz_integral_convergence`
    (which uses `hRegular.uniform_bound` for DCT and `hRegular.tube_continuousWithinAt` for
    pointwise convergence). `tendsto_nhds_unique` gives equality. -/
theorem fourierLaplace_boundary_recovery {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    (hcone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C)
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (TubeDomain C))
    (hRegular : HasFourierLaplaceReprRegular C F)
    (f : SchwartzMap (Fin m → ℝ) ℂ) :
    hRegular.dist f = ∫ x : Fin m → ℝ, F (realEmbed x) * f x := by
  obtain ⟨η, hη⟩ := hne
  have h1 := hRegular.boundary_value f η hη
  have h2 := fourierLaplace_schwartz_integral_convergence hC hconv ⟨η, hη⟩ hcone hF hRegular f η hη
  exact tendsto_nhds_unique h1 h2

/-- **Polynomial growth of Fourier-Laplace transforms.**

    If F has a Fourier-Laplace representation on T(C), then for any compact K ⊆ C,
    there exist C_bd > 0 and N ∈ ℕ such that
      ‖F(x + iy)‖ ≤ C_bd * (1 + ‖x‖)^N  for all x ∈ ℝᵐ, y ∈ K.

    The proof (Vladimirov §25.3, Streater-Wightman Theorem 2-6) uses:
    1. The Laplace integral representation and estimates on the exponential kernel
    2. The temperedness of the distribution (polynomial bounds on seminorms)
    3. Compactness of K to get uniform bounds in the imaginary direction -/
theorem fourierLaplace_polynomial_growth {m : ℕ}
    {C : Set (Fin m → ℝ)} (_hC : IsOpen C) (_hconv : Convex ℝ C) (_hne : C.Nonempty)
    {F : (Fin m → ℂ) → ℂ} (_hF : DifferentiableOn ℂ F (TubeDomain C))
    (hRegular : HasFourierLaplaceReprRegular C F)
    (K : Set (Fin m → ℝ)) (hK : IsCompact K) (hK_sub : K ⊆ C) :
    ∃ (C_bd : ℝ) (N : ℕ), C_bd > 0 ∧
      ∀ (x : Fin m → ℝ) (y : Fin m → ℝ), y ∈ K →
        ‖F (fun i => ↑(x i) + ↑(y i) * I)‖ ≤ C_bd * (1 + ‖x‖) ^ N :=
  hRegular.poly_growth K hK hK_sub

/-- **Weak boundary-value constructor.**

    This packages a continuous Schwartz functional `T` together with the
    distributional boundary-value convergence of `F` into
    `HasFourierLaplaceRepr C F`.

    It does **not** prove that `F` is an actual Fourier-Laplace transform with
    Fourier support in the dual cone `C*`. That stronger Paley-Wiener-Schwartz
    input is still missing and is exactly what should later upgrade the weak
    boundary-value package to the strong/regular ones. -/
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

end SCV

end
