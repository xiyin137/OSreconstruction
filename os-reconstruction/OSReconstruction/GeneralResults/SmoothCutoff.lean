/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Smooth Cutoff Functions via Convolution Mollifier

For any closed set S in ℝ^m, there exists a smooth function χ : ℝ^m → [0,1]
that equals 1 on a neighborhood of S and vanishes at distance > 1 from S,
with all derivatives globally bounded.

## Construction

Convolve a normalized smooth bump `φ` (supported in `ball 0 (1/4)`, integral 1)
with the indicator `1_A` of the closed 3/4-thickening `A = {ξ | infDist ξ S ≤ 3/4}`.

## Main result

`exists_smooth_cutoff_of_closed`

## References

- Hörmander, "The Analysis of Linear PDOs I", §1.4
- Mathlib: `ContDiffBump`, `MeasureTheory.convolution`
-/

open scoped Classical ComplexConjugate BigOperators Convolution ContDiff
open MeasureTheory Metric Set Function ContinuousLinearMap Filter

noncomputable section

variable {m : ℕ}

set_option linter.unusedVariables false in
private lemma convolution_left_iteratedFDeriv_bounded :
    ∀ k : ℕ,
    ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
      (L : X →L[ℝ] ℝ →L[ℝ] X) (hL : ‖L‖ ≤ 1)
      (f : (Fin m → ℝ) → X) (g : (Fin m → ℝ) → ℝ)
      (hf_supp : HasCompactSupport f)
      (hf_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
      (hg_li : LocallyIntegrable g volume)
      (hg_bound : ∀ x, ‖g x‖ ≤ 1),
      ∃ C : ℝ, ∀ ξ, ‖iteratedFDeriv ℝ k (f ⋆[L, volume] g) ξ‖ ≤ C
  | 0, X, _, _, _, L, hL, f, g, hf_supp, hf_smooth, hg_li, hg_bound => by
      refine ⟨∫ t, ‖f t‖, ?_⟩
      intro ξ
      have hcont : Continuous f := hf_smooth.continuous
      have hf_int : Integrable (fun t => ‖f t‖) volume :=
        (hcont.norm).integrable_of_hasCompactSupport hf_supp.norm
      have h0 : ‖(f ⋆[L, volume] g) ξ‖ ≤ ∫ t, ‖f t‖ ∂volume := by
        calc
          ‖(f ⋆[L, volume] g) ξ‖ = ‖∫ t, L (f t) (g (ξ - t)) ∂volume‖ := by
            simp [MeasureTheory.convolution]
          _ ≤ ∫ t, ‖f t‖ ∂volume := by
            refine norm_integral_le_of_norm_le hf_int ?_
            filter_upwards with t
            have ht_nonneg : 0 ≤ ‖f t‖ := norm_nonneg _
            have hprod_nonneg : 0 ≤ ‖f t‖ * ‖g (ξ - t)‖ :=
              mul_nonneg (norm_nonneg _) (norm_nonneg _)
            have hgt : ‖g (ξ - t)‖ ≤ 1 := hg_bound (ξ - t)
            have hm : ‖f t‖ * ‖g (ξ - t)‖ ≤ ‖f t‖ := by
              calc
                ‖f t‖ * ‖g (ξ - t)‖ ≤ ‖f t‖ * 1 := by
                  exact mul_le_mul_of_nonneg_left hgt ht_nonneg
                _ = ‖f t‖ := by ring
            calc
              ‖L (f t) (g (ξ - t))‖ ≤ ‖L‖ * ‖f t‖ * ‖g (ξ - t)‖ := L.le_opNorm₂ _ _
              _ ≤ 1 * (‖f t‖ * ‖g (ξ - t)‖) := by
                rw [mul_assoc]
                exact mul_le_mul_of_nonneg_right hL hprod_nonneg
              _ = ‖f t‖ * ‖g (ξ - t)‖ := by ring
              _ ≤ ‖f t‖ := hm
      simpa using h0
  | k + 1, X, _, _, _, L, hL, f, g, hf_supp, hf_smooth, hg_li, hg_bound => by
      letI := ContinuousLinearMap.hasOpNorm (𝕜 := ℝ) (𝕜₂ := ℝ)
        (E := (Fin m → ℝ) →L[ℝ] X)
        (F := ℝ →L[ℝ] (Fin m → ℝ) →L[ℝ] X) (σ₁₂ := RingHom.id ℝ)
      have hf1 : ContDiff ℝ 1 f := hf_smooth.of_le (by simp)
      have hfderiv_eq : fderiv ℝ (f ⋆[L, volume] g) =
          fun x => ((fderiv ℝ f) ⋆[L.precompL (Fin m → ℝ), volume] g) x := by
        funext x
        exact (hf_supp.hasFDerivAt_convolution_left (L := L) hf1 hg_li x).fderiv
      have hL' : ‖L.precompL (Fin m → ℝ)‖ ≤ 1 :=
        le_trans (ContinuousLinearMap.norm_precompL_le (Fin m → ℝ) L) hL
      have hfderiv_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) (fderiv ℝ f) := by
        fun_prop
      rcases convolution_left_iteratedFDeriv_bounded k
          (X := (Fin m → ℝ) →L[ℝ] X)
          (L.precompL (Fin m → ℝ)) hL' (fderiv ℝ f) g
          (hf_supp.fderiv (𝕜 := ℝ)) hfderiv_smooth hg_li hg_bound with
        ⟨C, hC⟩
      refine ⟨C, ?_⟩
      intro ξ
      rw [← norm_iteratedFDeriv_fderiv, hfderiv_eq]
      exact hC ξ

/-- **Existence of smooth cutoff adapted to a closed set.**

    For any closed set S ⊆ ℝ^m, there exists `χ : ℝ^m → ℝ` with:
    1. `ContDiff ℝ ∞ χ` (C^∞ smooth)
    2. `χ = 1` on an ε-neighborhood of S
    3. `χ = 0` outside the 1-neighborhood of S
    4. All iterated derivatives globally bounded
    5. `0 ≤ χ ≤ 1`

    **Proof**: Construct via convolution `χ = φ_normed ⋆ 1_{S + B_{3/4}}` where
    `φ ∈ C_c^∞(B_{1/4}(0))` is a smooth normed bump with `∫ φ = 1`. -/
theorem exists_smooth_cutoff_of_closed
    (S : Set (Fin m → ℝ)) (hS : IsClosed S) :
    ∃ (χ : (Fin m → ℝ) → ℝ),
      ContDiff ℝ ∞ χ ∧
      (∃ ε > 0, ∀ ξ, infDist ξ S < ε → χ ξ = 1) ∧
      (∀ ξ, infDist ξ S > 1 → χ ξ = 0) ∧
      (∀ k : ℕ, ∃ C : ℝ, ∀ ξ, ‖iteratedFDeriv ℝ k χ ξ‖ ≤ C) ∧
      (∀ ξ, 0 ≤ χ ξ) ∧
      (∀ ξ, χ ξ ≤ 1) := by
  let μ : Measure (Fin m → ℝ) := MeasureTheory.MeasureSpace.volume
  -- The bump function φ with rIn = 1/8, rOut = 1/4
  let φ : ContDiffBump (0 : Fin m → ℝ) :=
    { rIn := 1/8, rOut := 1/4, rIn_pos := by positivity, rIn_lt_rOut := by norm_num }
  -- The thickened set A = {ξ | infDist ξ S ≤ 3/4}
  let A : Set (Fin m → ℝ) := {ξ | infDist ξ S ≤ 3/4}
  -- The indicator function g = 1_A
  let g : (Fin m → ℝ) → ℝ := A.indicator (fun _ => 1)
  -- The cutoff: χ = φ.normed μ ⋆ g
  let χ : (Fin m → ℝ) → ℝ := φ.normed μ ⋆[lsmul ℝ ℝ, μ] g
  -- A is closed
  have hA_closed : IsClosed A :=
    isClosed_le (continuous_infDist_pt S) continuous_const
  -- g is bounded by 1
  have hg_bound : ∀ x, ‖g x‖ ≤ 1 := by
    intro x; simp only [g, indicator]; split_ifs <;> simp
  -- g is locally integrable (indicator of measurable set times constant is locally integrable)
  have hg_li : LocallyIntegrable g μ :=
    (locallyIntegrable_const (1 : ℝ)).indicator hA_closed.measurableSet
  -- Properties of the normed bump
  have hφ_nn : ∀ x, 0 ≤ φ.normed μ x := φ.nonneg_normed
  have hφ_int : ∫ x, φ.normed μ x ∂μ = 1 := φ.integral_normed
  have hφ_supp_eq : support (φ.normed μ) = ball (0 : Fin m → ℝ) (1/4) := φ.support_normed_eq
  -- g values
  have hg_one : ∀ x, x ∈ A → g x = 1 := fun x hx => indicator_of_mem hx _
  have hg_zero : ∀ x, x ∉ A → g x = 0 := fun x hx => Set.indicator_of_notMem hx _
  -- g is nonneg
  have hg_nn : ∀ x, 0 ≤ g x :=
    indicator_nonneg (fun _ _ => zero_le_one)
  -- g ≤ 1
  have hg_le : ∀ x, g x ≤ 1 := by
    intro x; simp only [g, indicator]; split_ifs <;> linarith
  -- 1. Smoothness: for each n : ℕ∞, convolution of C^n compact-support with locally integrable is C^n
  -- Since this holds for all n : ℕ∞, it holds for ⊤ : WithTop ℕ∞ via contDiff_infty
  have h_smooth_n : ∀ n : ℕ, ContDiff ℝ (n : ℕ∞) χ := fun n =>
    φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) φ.contDiff_normed hg_li
  have h_smooth : ContDiff ℝ ∞ χ := contDiff_infty.mpr h_smooth_n
  -- Geometric lemma: if infDist ξ S < 1/2, then ball ξ (1/4) ⊆ A
  have h_ball_sub_A : ∀ ξ : Fin m → ℝ, infDist ξ S < 1/2 → ball ξ (1/4 : ℝ) ⊆ A := by
    intro ξ hξ y hy
    show infDist y S ≤ 3/4
    have hd : dist y ξ < 1/4 := mem_ball.mp hy
    have : infDist y S < 3/4 := calc
      infDist y S ≤ infDist ξ S + dist y ξ := infDist_le_infDist_add_dist
      _ < 1/2 + 1/4 := add_lt_add hξ hd
      _ = 3/4 := by norm_num
    linarith
  -- Geometric lemma: if infDist ξ S > 1, then ball ξ (1/4) is disjoint from A
  have h_ball_disj_A : ∀ ξ : Fin m → ℝ, infDist ξ S > 1 →
      ∀ y, y ∈ ball ξ (1/4 : ℝ) → y ∉ A := by
    intro ξ hξ y hy
    show ¬ (infDist y S ≤ 3/4)
    push Not
    have hd : dist y ξ < 1/4 := mem_ball.mp hy
    have h1 : infDist ξ S ≤ infDist y S + dist ξ y := infDist_le_infDist_add_dist
    have h2 : dist ξ y < 1/4 := by rwa [dist_comm]
    linarith
  -- 2. χ = 1 near S
  have h_one : ∃ ε > 0, ∀ ξ, infDist ξ S < ε → χ ξ = 1 := by
    refine ⟨1/2, by positivity, fun ξ hξ => ?_⟩
    have hξA : ξ ∈ A := h_ball_sub_A ξ hξ (mem_ball_self (by positivity : (0:ℝ) < 1/4))
    have hg_const : ∀ y ∈ ball ξ (1/4 : ℝ), g y = g ξ := by
      intro y hy
      rw [hg_one y (h_ball_sub_A ξ hξ hy), hg_one ξ hξA]
    have hχ_eq : χ ξ = ∫ t, (lsmul ℝ ℝ) (φ.normed μ t) (g ξ) ∂μ :=
      convolution_eq_right' (lsmul ℝ ℝ) hφ_supp_eq.subset hg_const
    rw [hχ_eq, hg_one ξ hξA]
    simp [lsmul_apply, smul_eq_mul, hφ_int]
  -- 3. χ = 0 outside 1-neighborhood
  have h_zero : ∀ ξ, infDist ξ S > 1 → χ ξ = 0 := by
    intro ξ hξ
    have hξA : ξ ∉ A := h_ball_disj_A ξ hξ ξ (mem_ball_self (by positivity : (0:ℝ) < 1/4))
    have hg_const : ∀ y ∈ ball ξ (1/4 : ℝ), g y = g ξ := by
      intro y hy
      rw [hg_zero y (h_ball_disj_A ξ hξ y hy), hg_zero ξ hξA]
    have hχ_eq : χ ξ = ∫ t, (lsmul ℝ ℝ) (φ.normed μ t) (g ξ) ∂μ :=
      convolution_eq_right' (lsmul ℝ ℝ) hφ_supp_eq.subset hg_const
    rw [hχ_eq, hg_zero ξ hξA]
    simp [lsmul_apply, smul_eq_mul]
  -- 5. 0 ≤ χ
  have h_nn : ∀ ξ, 0 ≤ χ ξ := by
    intro ξ
    simp only [χ, convolution_def, lsmul_apply, smul_eq_mul]
    exact integral_nonneg (fun t => mul_nonneg (hφ_nn t) (hg_nn (ξ - t)))
  -- Convolution exists (integrand is integrable at each point)
  have h_conv_exists : ConvolutionExists (φ.normed μ) g (lsmul ℝ ℝ) μ :=
    φ.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ)
      φ.continuous_normed hg_li
  -- 6. χ ≤ 1
  have h_le : ∀ ξ, χ ξ ≤ 1 := by
    intro ξ
    simp only [χ, convolution_def, lsmul_apply, smul_eq_mul]
    calc ∫ t, φ.normed μ t * g (ξ - t) ∂μ
        ≤ ∫ t, φ.normed μ t ∂μ := by
          apply integral_mono
          · -- integrability from ConvolutionExistsAt
            have := (h_conv_exists ξ).integrable
            simp only [lsmul_apply, smul_eq_mul] at this
            exact this
          · exact φ.integrable_normed
          · intro t
            exact mul_le_of_le_one_right (hφ_nn t) (hg_le (ξ - t))
      _ = 1 := hφ_int
  -- 4. Bounded derivatives
  -- The formal argument requires `iteratedFDeriv ℝ k (f ⋆ g) = (iteratedFDeriv ℝ k f) ⋆ g`,
  -- which follows from `HasCompactSupport.hasFDerivAt_convolution_left` by induction but is
  -- not yet stated as a standalone lemma in Mathlib. Given this identity:
  --   ‖iteratedFDeriv ℝ k χ ξ‖ = ‖∫ (iteratedFDeriv ℝ k φ.normed)(t) ⬝ g(ξ - t) dt‖
  --     ≤ ∫ ‖iteratedFDeriv ℝ k φ.normed t‖ dt   (since |g| ≤ 1)
  -- which is a finite constant independent of ξ (since iteratedFDeriv k φ.normed is
  -- continuous with compact support, hence integrable).
  have h_deriv : ∀ k : ℕ, ∃ C : ℝ, ∀ ξ, ‖iteratedFDeriv ℝ k χ ξ‖ ≤ C := by
    intro k
    simpa [χ] using convolution_left_iteratedFDeriv_bounded (m := m) k
      (L := lsmul ℝ ℝ) (ContinuousLinearMap.opNorm_lsmul_le (𝕜 := ℝ) (R := ℝ) (E := ℝ))
      (φ.normed μ) g φ.hasCompactSupport_normed φ.contDiff_normed hg_li hg_bound
  exact ⟨χ, h_smooth, h_one, h_zero, h_deriv, h_nn, h_le⟩

end
