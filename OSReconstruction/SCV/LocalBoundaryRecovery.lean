/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.LaplaceSchwartz

/-!
# Local Boundary Recovery for Tempered Fourier-Laplace Packages

This file proves the local-open boundary recovery theorem for holomorphic tube
functions with tempered Fourier-Laplace boundary-value data.

## Mathematical content

If `F` is holomorphic on the tube domain `T(C)`, admits a tempered
Fourier-Laplace boundary-value package, and has a continuous boundary trace on
an open real set `U`, then the abstract boundary-value functional is given on
Schwartz tests with compact support in `U` by integration against the concrete
boundary trace `x ↦ F(realEmbed x)`.

This is the local/support-restricted analogue of
`SCV.fourierLaplace_boundary_recovery`.

## Proof

The proof localizes the existing global proof:

1. The distributional boundary value gives `∫ F(x+iεη) f(x) dx → T(f)`.
2. DCT gives `∫ F(x+iεη) f(x) dx → ∫ F(x) f(x) dx`, using:
   - `uniform_bound` for domination (same as global proof),
   - `hcontU` for pointwise convergence on U (local, not global),
   - `f = 0` outside U (from `tsupport f ⊆ U`) for trivial convergence there.
3. Limit uniqueness (`tendsto_nhds_unique`) gives `T(f) = ∫ F(x) f(x) dx`.
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set Filter

namespace SCV

/-- A Schwartz function with `tsupport ⊆ U` vanishes outside `U`. -/
private theorem schwartz_eq_zero_of_not_mem_tsupport {m : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ) (U : Set (Fin m → ℝ))
    (hsupp : tsupport (f : (Fin m → ℝ) → ℂ) ⊆ U)
    (x : Fin m → ℝ) (hx : x ∉ U) :
    (f : (Fin m → ℝ) → ℂ) x = 0 := by
  have hnotin : x ∉ tsupport (⇑f) := fun h => hx (hsupp h)
  exact image_eq_zero_of_notMem_tsupport hnotin

/-- Pointwise convergence of the integrand `F(x+iεη)*f(x) → F(x)*f(x)` ae,
using boundary continuity only on U and the fact that f vanishes outside U. -/
private theorem pointwise_convergence_local {m : ℕ}
    {C : Set (Fin m → ℝ)} (_hne : C.Nonempty)
    (hcone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C)
    {F : (Fin m → ℂ) → ℂ} (_hF : DifferentiableOn ℂ F (TubeDomain C))
    (U : Set (Fin m → ℝ))
    (hcontU : ∀ x ∈ U, ContinuousWithinAt F (TubeDomain C) (realEmbed x))
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hf_supp : tsupport (f : (Fin m → ℝ) → ℂ) ⊆ U)
    (η : Fin m → ℝ) (hη : η ∈ C) :
    ∀ᵐ y : Fin m → ℝ ∂volume,
      Filter.Tendsto (fun ε : ℝ =>
        F (fun i => ↑(y i) + ↑ε * ↑(η i) * I) * (f : (Fin m → ℝ) → ℂ) y)
      (nhdsWithin 0 (Ioi 0))
      (nhds (F (realEmbed y) * (f : (Fin m → ℝ) → ℂ) y)) := by
  apply Filter.Eventually.of_forall
  intro y
  by_cases hy : y ∈ U
  · -- y ∈ U: use hcontU to get F(y+iεη) → F(realEmbed y)
    apply Filter.Tendsto.mul _ tendsto_const_nhds
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
    have h_path_tends : Filter.Tendsto
        (fun ε : ℝ => (fun i : Fin m => (y i : ℂ) + ↑ε * ↑(η i) * I))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhdsWithin (realEmbed y) (TubeDomain C)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Filter.eventually_of_mem self_mem_nhdsWithin h_path_maps⟩
      rw [← h_path_zero]
      exact h_path_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact Filter.Tendsto.comp (hcontU y hy) h_path_tends
  · -- y ∉ U: f(y) = 0, so both sides are 0
    have hfy : (f : (Fin m → ℝ) → ℂ) y = 0 :=
      schwartz_eq_zero_of_not_mem_tsupport f U hf_supp y hy
    simp [hfy]

/-- Local version of `fourierLaplace_schwartz_integral_convergence`: the
integrals `∫ F(x+iεη) f(x) dx` converge to `∫ F(x) f(x) dx` as `ε → 0+`,
using boundary continuity only on U. -/
private theorem fourierLaplace_schwartz_integral_convergence_local {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (_hconv : Convex ℝ C) (hne : C.Nonempty)
    (hcone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C)
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (TubeDomain C))
    (hTempered : HasFourierLaplaceReprTempered C F)
    (U : Set (Fin m → ℝ)) (_hU : IsOpen U)
    (hcontU : ∀ x ∈ U, ContinuousWithinAt F (TubeDomain C) (realEmbed x))
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hf_supp : tsupport (f : (Fin m → ℝ) → ℂ) ⊆ U)
    (_hf_compact : HasCompactSupport (f : (Fin m → ℝ) → ℂ))
    (η : Fin m → ℝ) (hη : η ∈ C) :
    Filter.Tendsto (fun ε : ℝ =>
      ∫ x : Fin m → ℝ, F (fun i => ↑(x i) + ↑ε * ↑(η i) * I) * f x)
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds (∫ x, F (realEmbed x) * f x)) := by
  obtain ⟨C_bd, N, δ, _hC_bd_pos, hδ_pos, h_bd⟩ := hTempered.uniform_bound η hη
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (bound := fun y : Fin m → ℝ => C_bd * (1 + ‖y‖) ^ N * ‖(f : (Fin m → ℝ) → ℂ) y‖)
  · -- AEStronglyMeasurable
    apply Filter.eventually_of_mem self_mem_nhdsWithin
    intro ε hε
    exact fourierLaplace_integrand_aestronglyMeasurable hF η hη hcone (↑f)
      (schwartzMap_integrable f) ε (Set.mem_Ioi.mp hε)
  · -- Domination
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
  · -- Bound is integrable
    exact (schwartzMap_polynomial_norm_integrable f N).const_mul C_bd |>.congr
      (ae_of_all _ fun y => by ring)
  · -- Pointwise convergence (LOCAL — the key difference from the global proof)
    exact pointwise_convergence_local hne hcone hF U hcontU f hf_supp η hη

/-- **Local-open boundary recovery from a tempered Fourier-Laplace package.**

If `F` is holomorphic on the tube over an open convex cone `C`, already carries
the tempered boundary-value package `HasFourierLaplaceReprTempered C F`, and
has a continuous boundary trace on an open real set `U`, then the stored
distributional boundary value `hTempered.dist` is represented on Schwartz tests
with compact support in `U` by the pointwise boundary function
`x ↦ F (realEmbed x)`.

This is the local/support-restricted analogue of
`SCV.fourierLaplace_boundary_recovery`. -/
theorem fourierLaplace_boundary_recovery_on_open_of_tempered {m : ℕ}
    {C : Set (Fin m → ℝ)} (_hC : IsOpen C) (hconv : Convex ℝ C) (hne : C.Nonempty)
    (hcone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C)
    {F : (Fin m → ℂ) → ℂ} (hF : DifferentiableOn ℂ F (TubeDomain C))
    (hTempered : HasFourierLaplaceReprTempered C F)
    (U : Set (Fin m → ℝ)) (hU : IsOpen U)
    (hcontU : ∀ x ∈ U, ContinuousWithinAt F (TubeDomain C) (realEmbed x)) :
    ∀ f : SchwartzMap (Fin m → ℝ) ℂ,
      tsupport (f : (Fin m → ℝ) → ℂ) ⊆ U →
      HasCompactSupport (f : (Fin m → ℝ) → ℂ) →
        hTempered.dist f = ∫ x : Fin m → ℝ, F (realEmbed x) * f x := by
  intro f hf_supp hf_compact
  obtain ⟨η, hη⟩ := hne
  -- The distributional BV: ∫ F(x+iεη) f(x) dx → hTempered.dist f
  have h_dist := hTempered.boundary_value f η hη
  -- The integral convergence: ∫ F(x+iεη) f(x) dx → ∫ F(realEmbed x) f(x) dx
  have h_int := fourierLaplace_schwartz_integral_convergence_local
    _hC hconv ⟨η, hη⟩ hcone hF hTempered U hU hcontU f hf_supp hf_compact η hη
  -- By uniqueness of limits
  exact tendsto_nhds_unique h_dist h_int

end SCV
