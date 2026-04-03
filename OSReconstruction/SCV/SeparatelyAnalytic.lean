/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Osgood's Lemma and Holomorphic Extension Infrastructure

This file develops infrastructure for the multi-dimensional edge-of-the-wedge theorem:

1. **Osgood's Lemma**: A continuous function of several complex variables that is
   holomorphic in each variable separately is jointly holomorphic.

2. **1D extension across real line**: A continuous function on an open set in ℂ that
   is holomorphic off the real line is holomorphic everywhere (via Morera's theorem).

3. **Holomorphic extension across totally real boundaries**: A continuous function
   that is holomorphic on two open sets separated by a real boundary is holomorphic
   on the union.

These are needed for the Bargmann-Hall-Wightman theorem.

## Mathematical Background

Osgood's Lemma (1899): Let U ⊂ ℂⁿ be open and f : U → ℂ continuous. If f is
holomorphic in each variable z_i (with the others fixed), then f is holomorphic
(jointly, in the sense of Fréchet differentiability over ℂ).

The proof uses: for each pair of variables (z₁, z₂), the Cauchy integral formula
in z₁ gives a representation of f that is visibly holomorphic in z₂ by
differentiation under the integral sign.

## References

* Osgood, "Note über analytische Functionen mehrerer Veränderlichen" (1899)
* Krantz-Parks, "A Primer of Real Analytic Functions", §2.2
* Streater-Wightman, "PCT, Spin and Statistics, and All That", Ch. 2
-/

noncomputable section

open Complex Filter Topology Set MeasureTheory intervalIntegral
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ### Osgood's Lemma Infrastructure -/

omit [NormedSpace ℂ E] in
/-- The z-derivative of f(z,x) at z₀ varies continuously in x, when f is jointly
    continuous and separately holomorphic in z.

    Proof: By Cauchy integral formula,
      deriv(z ↦ f(z,x))(z₀) = (2πI)⁻¹ ∮ f(ζ,x)/(ζ-z₀)² dζ
    The integrand is continuous in x (from joint continuity of f) and uniformly
    bounded on the circle, so the integral is continuous in x. -/
lemma continuousAt_deriv_of_continuousOn [CompleteSpace E]
    {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    {V : Set E} (hV : IsOpen V)
    (f : ℂ × E → ℂ)
    (hf_cont : ContinuousOn f (Metric.closedBall z₀ ρ ×ˢ V))
    (hf_z : ∀ x ∈ V, DifferentiableOn ℂ (fun z => f (z, x)) (Metric.closedBall z₀ ρ))
    {x₀ : E} (hx₀ : x₀ ∈ V) :
    ContinuousAt (fun x => deriv (fun z => f (z, x)) z₀) x₀ := by
  -- Strategy: Use Complex.cderiv (Cauchy integral for derivative) at radius ρ/2.
  -- cderiv = deriv by Cauchy formula, and norm_cderiv_sub_lt gives a Cauchy estimate.
  -- Tube lemma gives uniform bound on sphere → bound on derivative difference.
  rw [Metric.continuousAt_iff]
  intro ε hε
  -- Setup: radius ρ' = ρ/2 for cderiv, with closedBall z₀ ρ' ⊂ ball z₀ ρ
  set ρ' := ρ / 2 with hρ'_def
  have hρ' : 0 < ρ' := by positivity
  have hρ'_lt : ρ' < ρ := by linarith
  have h_sphere_sub : Metric.sphere z₀ ρ' ⊆ Metric.closedBall z₀ ρ :=
    Metric.sphere_subset_closedBall.trans (Metric.closedBall_subset_closedBall hρ'_lt.le)
  -- cderiv ρ' agrees with deriv for each x ∈ V
  have h_cderiv : ∀ x ∈ V,
      Complex.cderiv ρ' (fun z => f (z, x)) z₀ = deriv (fun z => f (z, x)) z₀ := by
    intro x hx
    exact Complex.cderiv_eq_deriv Metric.isOpen_ball
      ((hf_z x hx).mono Metric.ball_subset_closedBall) hρ'
      (Metric.closedBall_subset_ball hρ'_lt)
  -- ContinuousOn on sphere for norm_cderiv_sub_lt
  have h_cont_sp : ∀ x ∈ V,
      ContinuousOn (fun z => f (z, x)) (Metric.sphere z₀ ρ') := by
    intro x hx; exact ((hf_z x hx).continuousOn).mono h_sphere_sub
  -- Get δ_V with ball x₀ δ_V ⊆ V
  obtain ⟨δ_V, hδ_V, hball_V⟩ := Metric.isOpen_iff.mp hV x₀ hx₀
  -- Tube lemma: uniform bound ‖f(w,x) - f(w,x₀)‖ < ε*ρ' on closedBall z₀ ρ
  have h_nhds : ∀ w ∈ Metric.closedBall z₀ ρ,
      ∃ εw > 0, ∀ w' ∈ Metric.closedBall z₀ ρ, ∀ x ∈ V,
        ‖w' - w‖ < εw → ‖x - x₀‖ < εw → ‖f (w', x) - f (w, x₀)‖ < ε * ρ' / 2 := by
    intro w hw
    have h_cwa := hf_cont (w, x₀) ⟨hw, hx₀⟩
    rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds] at h_cwa
    obtain ⟨δw, hδw, hball⟩ := h_cwa (ε * ρ' / 2) (by positivity)
    refine ⟨δw, hδw, fun w' hw' x hx hw'_near hx_near => ?_⟩
    have h_dist : dist (w', x) (w, x₀) < δw := by
      rw [Prod.dist_eq]; exact max_lt (by rwa [dist_eq_norm]) (by rwa [dist_eq_norm])
    have := hball ⟨hw', hx⟩ h_dist
    rwa [dist_eq_norm] at this
  have h_choice : ∀ w, ∃ εw > 0, w ∈ Metric.closedBall z₀ ρ →
      ∀ w' ∈ Metric.closedBall z₀ ρ, ∀ x ∈ V,
        ‖w' - w‖ < εw → ‖x - x₀‖ < εw → ‖f (w', x) - f (w, x₀)‖ < ε * ρ' / 2 := by
    intro w
    by_cases hw : w ∈ Metric.closedBall z₀ ρ
    · obtain ⟨εw, hεw, hb⟩ := h_nhds w hw; exact ⟨εw, hεw, fun _ => hb⟩
    · exact ⟨1, one_pos, fun h => absurd h hw⟩
  choose εw hεw h_bound_εw using h_choice
  obtain ⟨t, ht_sub, ht_cover⟩ := (isCompact_closedBall z₀ ρ).elim_nhds_subcover
    (fun w => Metric.ball w (εw w)) (fun w _ => Metric.ball_mem_nhds w (hεw w))
  have ht_ne : t.Nonempty := by
    by_contra h_empty; rw [Finset.not_nonempty_iff_eq_empty] at h_empty
    exact absurd (ht_cover (Metric.mem_closedBall_self hρ.le)) (by simp [h_empty])
  set δ₁ := t.inf' ht_ne εw
  have hδ₁ : 0 < δ₁ := by rw [Finset.lt_inf'_iff]; intro w _; exact hεw w
  have h_unif : ∀ w ∈ Metric.closedBall z₀ ρ, ∀ x ∈ V, ‖x - x₀‖ < δ₁ →
      ‖f (w, x) - f (w, x₀)‖ < ε * ρ' := by
    intro w hw x hx hxδ
    obtain ⟨wᵢ, hwᵢ_mem, hw_in_ball⟩ := Set.mem_iUnion₂.mp (ht_cover hw)
    rw [Metric.mem_ball, dist_eq_norm] at hw_in_ball
    have hδ₁_le : δ₁ ≤ εw wᵢ := Finset.inf'_le _ hwᵢ_mem
    have hwᵢ_in := ht_sub wᵢ hwᵢ_mem
    have h1 := h_bound_εw wᵢ hwᵢ_in w hw x hx hw_in_ball (lt_of_lt_of_le hxδ hδ₁_le)
    have h2 := h_bound_εw wᵢ hwᵢ_in w hw x₀ hx₀ hw_in_ball
      (by rw [sub_self, norm_zero]; exact hεw wᵢ)
    have : f (w, x) - f (w, x₀) =
        (f (w, x) - f (wᵢ, x₀)) + (f (wᵢ, x₀) - f (w, x₀)) := by ring
    rw [this]
    calc ‖(f (w, x) - f (wᵢ, x₀)) + (f (wᵢ, x₀) - f (w, x₀))‖
        ≤ ‖f (w, x) - f (wᵢ, x₀)‖ + ‖f (wᵢ, x₀) - f (w, x₀)‖ := norm_add_le _ _
      _ < ε * ρ' / 2 + ε * ρ' / 2 := add_lt_add h1 (by rwa [norm_sub_rev])
      _ = ε * ρ' := by ring
  -- Main conclusion via norm_cderiv_sub_lt
  refine ⟨min δ₁ δ_V, lt_min hδ₁ hδ_V, fun x hx => ?_⟩
  rw [dist_eq_norm] at hx
  have hx_V : x ∈ V := hball_V (show dist x x₀ < δ_V by
    rw [dist_eq_norm]; exact lt_of_lt_of_le hx (min_le_right _ _))
  have hxδ₁ : ‖x - x₀‖ < δ₁ := lt_of_lt_of_le hx (min_le_left _ _)
  -- Sphere bound (sphere ⊆ closedBall)
  have h_sphere : ∀ w ∈ Metric.sphere z₀ ρ',
      ‖(fun z => f (z, x)) w - (fun z => f (z, x₀)) w‖ < ε * ρ' :=
    fun w hw => h_unif w (h_sphere_sub hw) x hx_V hxδ₁
  -- Apply Cauchy estimate
  have h_bound := Complex.norm_cderiv_sub_lt hρ' h_sphere (h_cont_sp x hx_V) (h_cont_sp x₀ hx₀)
  rw [dist_eq_norm, ← h_cderiv x hx_V, ← h_cderiv x₀ hx₀]
  calc ‖Complex.cderiv ρ' (fun z => f (z, x)) z₀ -
        Complex.cderiv ρ' (fun z => f (z, x₀)) z₀‖
      < ε * ρ' / ρ' := h_bound
    _ = ε := mul_div_cancel_right₀ ε (ne_of_gt hρ')

set_option maxHeartbeats 400000 in
/-- Helper 1: p 1 applied to h equals deriv * h for Cauchy power series. -/
private lemma cauchyPowerSeries_one_eq_deriv_mul (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g (Metric.closedBall z₀ ρ)) (h : ℂ) :
    (cauchyPowerSeries g z₀ ρ 1) (fun _ => h) = deriv g z₀ * h := by
  set R : NNReal := ⟨ρ, hρ.le⟩
  have hR : (0 : NNReal) < R := by exact_mod_cast hρ
  have hps := hg.hasFPowerSeriesOnBall hR
  set p := cauchyPowerSeries g z₀ ρ
  have hd : deriv g z₀ = (p 1) (fun _ => 1) := hps.hasFPowerSeriesAt.deriv
  -- p 1 (fun _ => h) = h • p 1 (fun _ => 1) by multilinearity
  have h_smul : (p 1) (fun _ => h) = h • (p 1) (fun _ => 1) := by
    conv_lhs => rw [show (fun _ : Fin 1 => h) = (fun i => h • (fun _ : Fin 1 => (1:ℂ)) i) from
      by ext; simp]
    rw [(p 1).map_smul_univ (fun _ => h) (fun _ => 1)]
    simp [Finset.prod_const, smul_eq_mul]
  rw [h_smul, hd, smul_eq_mul, mul_comm]

/-- Helper 2: Geometric tail bound Σ_{n≥0} M·r^(n+2) ≤ 2M·r² for r < 1/2. -/
private lemma tsum_geometric_tail_le (M r : ℝ) (hM : 0 ≤ M)
    (hr : 0 ≤ r) (hr2 : r < 1 / 2) :
    ∑' n, M * r ^ (n + 2) ≤ 2 * M * r ^ 2 := by
  have hr1 : r < 1 := by linarith
  have h1r : 0 < 1 - r := by linarith
  conv_lhs => rw [show (fun n => M * r ^ (n + 2)) = (fun n => M * r ^ 2 * r ^ n) from
    by ext n; ring]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr hr1]
  calc M * r ^ 2 * (1 - r)⁻¹
      ≤ M * r ^ 2 * 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [inv_le_comm₀ h1r (by norm_num : (0:ℝ) < 2)]
        linarith
    _ = 2 * M * r ^ 2 := by ring

set_option maxHeartbeats 800000 in
/-- Helper 3: Cauchy coefficient bound ‖p(n)(fun _ => h)‖ ≤ M * (‖h‖/ρ)^n. -/
private lemma cauchyPowerSeries_coeff_bound (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g (Metric.closedBall z₀ ρ))
    (M : ℝ) (hM : ∀ w ∈ Metric.closedBall z₀ ρ, ‖g w‖ ≤ M) (n : ℕ) (h : ℂ) :
    ‖(cauchyPowerSeries g z₀ ρ n) (fun _ => h)‖ ≤ M * (‖h‖ / ρ) ^ n := by
  set p := cauchyPowerSeries g z₀ ρ
  -- Step 1: ‖p n (fun _ => h)‖ ≤ ‖p n‖ * ‖h‖^n
  have h1 : ‖(p n) (fun _ => h)‖ ≤ ‖p n‖ * ‖h‖ ^ n := by
    have := (p n).le_opNorm (fun _ => h)
    simp only [Finset.prod_const, Finset.card_fin] at this
    exact this
  -- Step 2: ‖p n‖ ≤ A * |ρ|⁻¹^n by Cauchy estimates
  have h2 := norm_cauchyPowerSeries_le g z₀ ρ n
  set A := (2 * Real.pi)⁻¹ * ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, ‖g (circleMap z₀ ρ θ)‖ with hA_def
  -- Step 3: A ≤ M (bound the integral)
  have hg_cont : Continuous (fun θ => g (circleMap z₀ ρ θ)) :=
    hg.continuousOn.comp_continuous (lipschitzWith_circleMap z₀ ρ).continuous
      (fun θ => circleMap_mem_closedBall z₀ hρ.le θ)
  have h_int_bound : ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
      ‖g (circleMap z₀ ρ θ)‖ ≤ 2 * Real.pi * M := by
    have h_mono := intervalIntegral.integral_mono_on
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      (hg_cont.norm.intervalIntegrable _ _)
      (intervalIntegrable_const (μ := MeasureTheory.MeasureSpace.volume))
      (fun θ _ => hM _ (circleMap_mem_closedBall z₀ hρ.le θ))
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h_mono
    linarith
  have hA_le : A ≤ M := by
    calc A = (2 * Real.pi)⁻¹ * ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
        ‖g (circleMap z₀ ρ θ)‖ := rfl
      _ ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * M) := by
          apply mul_le_mul_of_nonneg_left h_int_bound (by positivity)
      _ = M := by field_simp
  -- Step 4: Combine all bounds
  have hρ_abs : |ρ| = ρ := abs_of_pos hρ
  have hM_nn : 0 ≤ M := le_trans (norm_nonneg _) (hM z₀ (Metric.mem_closedBall_self hρ.le))
  calc ‖(p n) (fun _ => h)‖
      ≤ ‖p n‖ * ‖h‖ ^ n := h1
    _ ≤ A * |ρ|⁻¹ ^ n * ‖h‖ ^ n := by
        exact mul_le_mul_of_nonneg_right h2 (pow_nonneg (norm_nonneg _) _)
    _ ≤ M * |ρ|⁻¹ ^ n * ‖h‖ ^ n := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hA_le (pow_nonneg (inv_nonneg.mpr (abs_nonneg _)) _))
          (pow_nonneg (norm_nonneg _) _)
    _ = M * (‖h‖ / ρ) ^ n := by
        rw [hρ_abs, div_eq_mul_inv, mul_pow]; ring

set_option maxHeartbeats 800000 in
/-- Helper 4: Taylor remainder equals power series tail. -/
private lemma taylor_remainder_eq_tsum (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g (Metric.closedBall z₀ ρ))
    (h : ℂ) (hh : ‖h‖ < ρ) :
    g (z₀ + h) - g z₀ - deriv g z₀ * h =
      ∑' n, (cauchyPowerSeries g z₀ ρ (n + 2)) (fun _ => h) := by
  set R : NNReal := ⟨ρ, hρ.le⟩
  have hR : (0 : NNReal) < R := by exact_mod_cast hρ
  have hps := hg.hasFPowerSeriesOnBall hR
  have hh_mem : h ∈ Metric.eball (0 : ℂ) R := by
    show edist h 0 < ↑R
    rw [edist_eq_enorm_sub, sub_zero]
    exact_mod_cast hh
  -- Full series sums to g(z₀ + h)
  have h_hassum : HasSum (fun n => (cauchyPowerSeries g z₀ ρ n) (fun _ => h))
      (g (z₀ + h)) := hps.hasSum hh_mem
  -- Use hasSum_nat_add_iff' to extract the tail
  have h_tail := (hasSum_nat_add_iff' (f := fun n =>
      (cauchyPowerSeries g z₀ ρ n) (fun _ => h)) 2).mpr h_hassum
  -- h_tail sums to g(z₀+h) - ∑ i in range 2, f i
  have h_range : ∑ i ∈ Finset.range 2,
      (cauchyPowerSeries g z₀ ρ i) (fun _ => h) =
    (cauchyPowerSeries g z₀ ρ 0) (fun _ : Fin 0 => h) +
    (cauchyPowerSeries g z₀ ρ 1) (fun _ => h) := by
    simp [Finset.sum_range_succ]
  -- Identify the two terms
  have hf0 : (cauchyPowerSeries g z₀ ρ 0) (fun _ : Fin 0 => h) = g z₀ :=
    hps.coeff_zero _
  have hf1 := cauchyPowerSeries_one_eq_deriv_mul z₀ ρ hρ g hg h
  rw [show g (z₀ + h) - g z₀ - deriv g z₀ * h =
    g (z₀ + h) - (∑ i ∈ Finset.range 2, (cauchyPowerSeries g z₀ ρ i) (fun _ => h))
    from by rw [h_range, hf0, hf1]; ring]
  exact h_tail.tsum_eq.symm

set_option maxHeartbeats 400000 in
/-- Helper 5: The tail of the Cauchy power series is summable. -/
private lemma taylor_tail_summable (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g (Metric.closedBall z₀ ρ))
    (h : ℂ) (hh : ‖h‖ < ρ) :
    Summable (fun n => (cauchyPowerSeries g z₀ ρ (n + 2)) (fun _ => h)) := by
  set R : NNReal := ⟨ρ, hρ.le⟩
  have hR : (0 : NNReal) < R := by exact_mod_cast hρ
  have hps := hg.hasFPowerSeriesOnBall hR
  have hh_mem : z₀ + h ∈ Metric.eball z₀ R := by
    show edist (z₀ + h) z₀ < ↑R
    rw [edist_eq_enorm_sub, add_sub_cancel_left]
    exact_mod_cast hh
  -- The full series is summable (HasSum implies Summable)
  have h_sum := (hps.hasSum_sub hh_mem).summable
  simp only [add_sub_cancel_left] at h_sum
  -- The tail of a summable series is summable
  exact h_sum.comp_injective (fun _ _ h => by omega)

set_option maxHeartbeats 800000 in
/-- Helper 6: Norm of tail tsum bounded by geometric series.
    Combines coefficient bound + summability + geometric tail. -/
private lemma taylor_tail_norm_le (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g (Metric.closedBall z₀ ρ))
    (M : ℝ) (hM : ∀ w ∈ Metric.closedBall z₀ ρ, ‖g w‖ ≤ M)
    (h : ℂ) (hh : ‖h‖ < ρ / 2) :
    ‖∑' n, (cauchyPowerSeries g z₀ ρ (n + 2)) (fun _ => h)‖ ≤
      4 * M / ρ ^ 2 * ‖h‖ ^ 2 := by
  have hh_lt_ρ : ‖h‖ < ρ := by linarith
  have hM_nn : 0 ≤ M := le_trans (norm_nonneg _) (hM z₀ (Metric.mem_closedBall_self hρ.le))
  -- Ratio r = ‖h‖/ρ < 1/2
  set r := ‖h‖ / ρ with hr_def
  have hr_nn : 0 ≤ r := div_nonneg (norm_nonneg _) hρ.le
  have hr_half : r < 1 / 2 := by
    rw [hr_def, div_lt_div_iff₀ hρ (by norm_num : (0:ℝ) < 2)]; linarith
  -- Step 1: ‖∑' an‖ ≤ ∑' ‖an‖
  -- Need summability of norms
  have h_tail_sum := taylor_tail_summable z₀ ρ hρ g hg h hh_lt_ρ
  have h_norm_sum : Summable (fun n => ‖(cauchyPowerSeries g z₀ ρ (n + 2)) (fun _ => h)‖) :=
    h_tail_sum.norm
  have h1 := norm_tsum_le_tsum_norm h_norm_sum
  -- Step 2: ‖an‖ ≤ M * r^(n+2) by coefficient bound
  have h_coeff : ∀ n, ‖(cauchyPowerSeries g z₀ ρ (n + 2)) (fun _ => h)‖ ≤ M * r ^ (n + 2) :=
    fun n => cauchyPowerSeries_coeff_bound z₀ ρ hρ g hg M hM (n + 2) h
  -- Step 3: ∑' ‖an‖ ≤ ∑' M * r^(n+2)
  have h_geom_sum : Summable (fun n => M * r ^ (n + 2)) := by
    have : Summable (fun n => M * r ^ 2 * r ^ n) :=
      (summable_geometric_of_lt_one hr_nn (by linarith)).mul_left (M * r ^ 2)
    convert this using 1; ext n; ring
  have h2 : ∑' n, ‖(cauchyPowerSeries g z₀ ρ (n + 2)) (fun _ => h)‖ ≤
      ∑' n, M * r ^ (n + 2) :=
    h_norm_sum.tsum_le_tsum h_coeff h_geom_sum
  -- Step 4: ∑' M * r^(n+2) ≤ 2 * M * r² by geometric tail
  have h3 := tsum_geometric_tail_le M r hM_nn hr_nn hr_half
  -- Step 5: 2 * M * r² ≤ 4 * M / ρ² * ‖h‖²
  -- Since r = ‖h‖/ρ, r² = ‖h‖²/ρ², so M * r² = M * ‖h‖² / ρ²
  have h4 : 2 * M * r ^ 2 ≤ 4 * M / ρ ^ 2 * ‖h‖ ^ 2 := by
    rw [hr_def, div_pow]
    have hρ2 : (ρ : ℝ) ^ 2 ≠ 0 := by positivity
    field_simp
    nlinarith [sq_nonneg ‖h‖]
  linarith

/-- Taylor remainder bound: ‖g(z₀+h) - g(z₀) - g'(z₀)·h‖ ≤ 4M/ρ² · ‖h‖² for ‖h‖ < ρ/2. -/
private lemma taylor_remainder_single {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (Metric.closedBall z₀ ρ))
    {M : ℝ} (hM : ∀ w ∈ Metric.closedBall z₀ ρ, ‖g w‖ ≤ M)
    {h : ℂ} (hh : ‖h‖ < ρ / 2) :
    ‖g (z₀ + h) - g z₀ - deriv g z₀ * h‖ ≤ 4 * M / ρ ^ 2 * ‖h‖ ^ 2 := by
  rw [taylor_remainder_eq_tsum z₀ ρ hρ g hg h (by linarith)]
  exact taylor_tail_norm_le z₀ ρ hρ g hg M hM h hh

omit [NormedSpace ℂ E] in
/-- Auxiliary: ContinuousOn f on K ×ˢ V with K compact gives uniform bound near x₀.
    Uses the generalized tube lemma: closedBall z₀ ρ × {x₀} is compact, and f is
    bounded on this set. By ContinuousOn, the preimage of {‖·‖ < M₀+1} relative to
    the domain contains this compact set. The tube lemma then gives a uniform δ. -/
private lemma uniform_bound_near_point [CompleteSpace E]
    {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    {V : Set E} (_hV : IsOpen V)
    (f : ℂ × E → ℂ)
    (hf_cont : ContinuousOn f (Metric.closedBall z₀ ρ ×ˢ V))
    {x₀ : E} (hx₀ : x₀ ∈ V) :
    ∃ (M : ℝ) (δ : ℝ), 0 ≤ M ∧ 0 < δ ∧
      ∀ w ∈ Metric.closedBall z₀ ρ, ∀ x ∈ V, ‖x - x₀‖ < δ → ‖f (w, x)‖ ≤ M := by
  -- Step 1: f is bounded on the compact slice closedBall z₀ ρ × {x₀}
  have hK₀ : IsCompact (Metric.closedBall z₀ ρ ×ˢ ({x₀} : Set E)) :=
    (isCompact_closedBall z₀ ρ).prod isCompact_singleton
  have hK₀_sub : Metric.closedBall z₀ ρ ×ˢ ({x₀} : Set E) ⊆ Metric.closedBall z₀ ρ ×ˢ V :=
    Set.prod_mono le_rfl (Set.singleton_subset_iff.mpr hx₀)
  obtain ⟨M₀, hM₀⟩ := hK₀.exists_bound_of_continuousOn (hf_cont.mono hK₀_sub)
  set M := |M₀| + 1 with hM_def
  -- Step 2: For each w ∈ closedBall z₀ ρ, ContinuousOn of f at (w, x₀) gives a neighborhood
  -- where ‖f‖ < M. We use the open preimage approach.
  -- The norm function (fun p => ‖f p‖) is ContinuousOn on the domain.
  -- The set {p | ‖f p‖ < M} is open in the ambient space when f is continuous.
  -- But f is only ContinuousOn, so we use nhdsWithin.
  -- For each (w, x₀) with w ∈ closedBall z₀ ρ:
  --   ‖f(w, x₀)‖ ≤ M₀ < |M₀| + 1 = M
  --   By ContinuousWithinAt: {p | ‖f p‖ < M} ∈ nhdsWithin (w,x₀) (domain)
  --   So there's an open U_w ∋ (w,x₀) with ‖f‖ < M on U_w ∩ domain
  -- By compactness of closedBall z₀ ρ, finitely many U_w cover.
  -- Extracting the "x-component" gives a uniform δ.
  have hM₀_lt_M : ∀ w ∈ Metric.closedBall z₀ ρ, ‖f (w, x₀)‖ < M := by
    intro w hw
    have := hM₀ (w, x₀) ⟨hw, Set.mem_singleton x₀⟩
    calc ‖f (w, x₀)‖ ≤ M₀ := this
      _ ≤ |M₀| := le_abs_self M₀
      _ < |M₀| + 1 := lt_add_one _
  -- For each w, get a neighborhood where ‖f‖ < M
  have h_nhds : ∀ w ∈ Metric.closedBall z₀ ρ,
      ∃ ε > 0, ∀ w' x', ‖w' - w‖ < ε → ‖x' - x₀‖ < ε → x' ∈ V →
        w' ∈ Metric.closedBall z₀ ρ → ‖f (w', x')‖ < M := by
    intro w hw
    have h_cont_at := hf_cont (w, x₀) ⟨hw, hx₀⟩
    rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds] at h_cont_at
    obtain ⟨ε, hε, hδ_ball⟩ := h_cont_at (M - ‖f (w, x₀)‖) (by linarith [hM₀_lt_M w hw])
    refine ⟨ε, hε, fun w' x' hw' hx' hxV hw'_ball => ?_⟩
    have h_mem : (w', x') ∈ Metric.closedBall z₀ ρ ×ˢ V := ⟨hw'_ball, hxV⟩
    have h_dist : dist (w', x') (w, x₀) < ε := by
      rw [Prod.dist_eq]
      exact max_lt (by rwa [dist_eq_norm]) (by rwa [dist_eq_norm])
    have := hδ_ball h_mem h_dist
    rw [dist_eq_norm] at this
    have h_tri := norm_sub_norm_le (f (w', x')) (f (w, x₀))
    linarith
  -- Step 3: By compactness of closedBall z₀ ρ, extract finite subcover and uniform δ
  -- Choose ε for each w (using classical choice; for w ∉ closedBall, pick 1)
  have h_choice : ∀ w, ∃ ε > 0, w ∈ Metric.closedBall z₀ ρ →
      ∀ w' x', ‖w' - w‖ < ε → ‖x' - x₀‖ < ε → x' ∈ V →
        w' ∈ Metric.closedBall z₀ ρ → ‖f (w', x')‖ < M := by
    intro w
    by_cases hw : w ∈ Metric.closedBall z₀ ρ
    · obtain ⟨ε, hε, hb⟩ := h_nhds w hw
      exact ⟨ε, hε, fun _ => hb⟩
    · exact ⟨1, one_pos, fun h => absurd h hw⟩
  choose ε hε h_bound_ε using h_choice
  -- Cover closedBall by balls
  have hK : IsCompact (Metric.closedBall z₀ ρ) := isCompact_closedBall z₀ ρ
  have h_cover_nhds : ∀ w ∈ Metric.closedBall z₀ ρ,
      Metric.ball w (ε w) ∈ nhds w :=
    fun w _ => Metric.ball_mem_nhds w (hε w)
  obtain ⟨t, ht_sub, ht_cover⟩ := hK.elim_nhds_subcover (fun w => Metric.ball w (ε w)) h_cover_nhds
  -- Take δ = min over t of ε values
  have ht_ne : t.Nonempty := by
    by_contra h_empty
    rw [Finset.not_nonempty_iff_eq_empty] at h_empty
    have := ht_cover (Metric.mem_closedBall_self (le_of_lt hρ))
    simp [h_empty] at this
  set δ₁ := t.inf' ht_ne ε
  have hδ₁_pos : 0 < δ₁ := by
    rw [Finset.lt_inf'_iff]
    intro w _; exact hε w
  refine ⟨M, δ₁, ?_, hδ₁_pos, fun w hw x hxV hxδ => ?_⟩
  · linarith [abs_nonneg M₀]
  -- For any w ∈ closedBall, find which ball in the cover contains it
  have hw_cover := ht_cover hw
  simp only [Set.mem_iUnion] at hw_cover
  obtain ⟨wᵢ, hwᵢ_mem, hw_in_ball⟩ := hw_cover
  rw [Metric.mem_ball, dist_eq_norm] at hw_in_ball
  have hδ₁_le : δ₁ ≤ ε wᵢ := Finset.inf'_le _ hwᵢ_mem
  have hwᵢ_in : wᵢ ∈ Metric.closedBall z₀ ρ := ht_sub wᵢ hwᵢ_mem
  have := h_bound_ε wᵢ hwᵢ_in w x hw_in_ball (lt_of_lt_of_le hxδ hδ₁_le) hxV hw
  linarith

omit [NormedSpace ℂ E] in
/-- Uniform Taylor remainder bound for a family of holomorphic functions.

    If f is continuous on closedBall z₀ ρ × V and holomorphic in z for each x ∈ V,
    then the first-order Taylor remainder in z is uniformly O(|h|²):
      |f(z₀+h, x) - f(z₀, x) - deriv_z f(z₀, x) · h| ≤ C · |h|²
    for |h| ≤ ρ/2 and x in a neighborhood of x₀.

    Proof: Power series expansion gives remainder = Σ_{n≥2} aₙ(x)hⁿ.
    Cauchy estimates: |aₙ(x)| ≤ M/ρⁿ where M = sup|f| on the compact set.
    Geometric series: |remainder| ≤ 2M|h|²/ρ² for |h| ≤ ρ/2. -/
lemma taylor_remainder_bound [CompleteSpace E]
    {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    {V : Set E} (hV : IsOpen V)
    (f : ℂ × E → ℂ)
    (hf_cont : ContinuousOn f (Metric.closedBall z₀ ρ ×ˢ V))
    (hf_z : ∀ x ∈ V, DifferentiableOn ℂ (fun z => f (z, x)) (Metric.closedBall z₀ ρ))
    {x₀ : E} (hx₀ : x₀ ∈ V) :
    ∃ (C : ℝ) (δ : ℝ), C ≥ 0 ∧ δ > 0 ∧
      ∀ (h : ℂ) (x : E), x ∈ V → ‖x - x₀‖ < δ → ‖h‖ < ρ / 2 →
      ‖f (z₀ + h, x) - f (z₀, x) - deriv (fun z => f (z, x)) z₀ * h‖ ≤ C * ‖h‖ ^ 2 := by
  obtain ⟨M, δ, hM_nn, hδ_pos, h_bound⟩ :=
    uniform_bound_near_point hρ hV f hf_cont hx₀
  exact ⟨4 * M / ρ ^ 2, δ, by positivity, hδ_pos, fun h x hxV hxδ hh =>
    taylor_remainder_single hρ (hf_z x hxV) (h_bound · · x hxV hxδ) hh⟩

/-! ### Osgood's Lemma -/

/-- **Osgood's Lemma (product form)**: A continuous function f : ℂ × E → ℂ on an
    open product U₁ × U₂ that is holomorphic in each factor separately is jointly
    holomorphic.

    The proof constructs the joint Fréchet derivative L(h,k) = a·h + B(k) where
    a = ∂f/∂z(z₀,x₀) and B = D_x f(z₀,x₀), then shows the remainder is o(‖(h,k)‖)
    using three estimates:
    1. Taylor remainder in z: O(|h|²) uniformly in x (Cauchy estimates)
    2. Derivative variation: [a(x₀+k) - a(x₀)]·h → 0 (continuity of z-derivative)
    3. Fréchet remainder in x: o(‖k‖) (from x-holomorphicity) -/
theorem osgood_lemma_prod [CompleteSpace E]
    {U₁ : Set ℂ} {U₂ : Set E} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    (f : ℂ × E → ℂ)
    (hf_cont : ContinuousOn f (U₁ ×ˢ U₂))
    (hf_z : ∀ x ∈ U₂, DifferentiableOn ℂ (fun z => f (z, x)) U₁)
    (hf_x : ∀ z ∈ U₁, DifferentiableOn ℂ (fun x => f (z, x)) U₂) :
    DifferentiableOn ℂ f (U₁ ×ˢ U₂) := by
  intro ⟨z₀, x₀⟩ ⟨hz₀, hx₀⟩
  -- Step 1: Find neighborhoods inside U₁ and U₂
  obtain ⟨ρ₀, hρ₀, hball_z⟩ := Metric.isOpen_iff.mp hU₁ z₀ hz₀
  obtain ⟨r_x, hr_x, hball_x⟩ := Metric.isOpen_iff.mp hU₂ x₀ hx₀
  set ρ := ρ₀ / 2
  have hρ : 0 < ρ := by positivity
  have hρ_lt : ρ < ρ₀ := by change ρ₀ / 2 < ρ₀; linarith
  have hcball_sub : Metric.closedBall z₀ ρ ⊆ U₁ :=
    fun w hw => hball_z (lt_of_le_of_lt (Metric.mem_closedBall.mp hw) hρ_lt)
  -- Step 2: DifferentiableAt in each variable
  have h_z_at : DifferentiableAt ℂ (fun z => f (z, x₀)) z₀ :=
    (hf_z x₀ hx₀ z₀ hz₀).differentiableAt (hU₁.mem_nhds hz₀)
  have h_x_at : DifferentiableAt ℂ (fun x => f (z₀, x)) x₀ :=
    (hf_x z₀ hz₀ x₀ hx₀).differentiableAt (hU₂.mem_nhds hx₀)
  -- Step 3: Candidate Fréchet derivative L(h,k) = a·h + B(k)
  -- a_of x = ∂f/∂z(z₀, x), the z-derivative as a function of x
  set a_of : E → ℂ := fun x => deriv (fun z => f (z, x)) z₀
  set B : E →L[ℂ] ℂ := fderiv ℂ (fun x => f (z₀, x)) x₀
  set L : ℂ × E →L[ℂ] ℂ :=
    ContinuousLinearMap.coprod (a_of x₀ • ContinuousLinearMap.id ℂ ℂ) B
  suffices HasFDerivAt f L (z₀, x₀) from this.differentiableAt.differentiableWithinAt
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  -- Step 4: Infrastructure for helper lemmas
  have hf_z_ball : ∀ x ∈ U₂, DifferentiableOn ℂ (fun z => f (z, x))
      (Metric.closedBall z₀ ρ) :=
    fun x hx => (hf_z x hx).mono hcball_sub
  have hf_cont_ball : ContinuousOn f (Metric.closedBall z₀ ρ ×ˢ U₂) :=
    hf_cont.mono (Set.prod_mono hcball_sub Subset.rfl)
  -- (i) Continuity of z-derivative in x
  have h_a_cont : ContinuousAt a_of x₀ :=
    continuousAt_deriv_of_continuousOn hρ hU₂ f hf_cont_ball hf_z_ball hx₀
  -- (ii) Taylor remainder bound
  obtain ⟨C_t, δ_t, hCt, hδt, h_taylor⟩ :=
    taylor_remainder_bound hρ hU₂ f hf_cont_ball hf_z_ball hx₀
  -- (iii) HasFDerivAt for x-part
  have h_x_fderiv : HasFDerivAt (fun x => f (z₀, x)) B x₀ := h_x_at.hasFDerivAt
  -- Step 5: ε-δ proof of isLittleO
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  -- Get δ₂ from continuity of a_of at x₀
  obtain ⟨δ₂, hδ₂, h_a_near⟩ := Metric.continuousAt_iff.mp h_a_cont (c / 3) (by positivity)
  -- Get δ₃ from HasFDerivAt of x-part
  have h_x_fderiv' := h_x_fderiv
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff] at h_x_fderiv'
  obtain ⟨δ₃, hδ₃, h_x_bound⟩ :=
    Metric.eventually_nhds_iff.mp (h_x_fderiv' (show (0 : ℝ) < c / 3 from by positivity))
  -- Choose overall δ
  have hCt1 : (0 : ℝ) < C_t + 1 := by linarith
  refine Metric.eventually_nhds_iff.mpr
    ⟨min (min (ρ / 2) (c / (3 * (C_t + 1)))) (min (min δ₂ δ₃) (min δ_t r_x)),
     by positivity, fun p hp => ?_⟩
  rw [dist_zero_right] at hp
  -- Extract individual bounds from the nested min
  simp only [lt_min_iff] at hp
  obtain ⟨⟨hp_ρ, hp_ct⟩, ⟨hp_δ₂, hp_δ₃⟩, hp_δt, hp_rx⟩ := hp
  -- Component norm bounds
  have h_fst : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
  have h_snd : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
  -- Membership: x₀ + p.2 ∈ U₂
  have hx_mem : x₀ + p.2 ∈ U₂ :=
    hball_x (show dist (x₀ + p.2) x₀ < r_x by
      simp [dist_eq_norm]; exact lt_of_le_of_lt h_snd hp_rx)
  -- Step 6: Decompose remainder into three terms
  -- T₁ = Taylor remainder in z, T₂ = derivative variation, T₃ = Fréchet in x
  set T₁ := f (z₀ + p.1, x₀ + p.2) - f (z₀, x₀ + p.2) - a_of (x₀ + p.2) * p.1
  set T₂ := (a_of (x₀ + p.2) - a_of x₀) * p.1
  set T₃ := f (z₀, x₀ + p.2) - f (z₀, x₀) - B p.2
  -- Show the remainder equals T₁ + T₂ + T₃
  have h_decomp : f ((z₀, x₀) + p) - f (z₀, x₀) - L p = T₁ + T₂ + T₃ := by
    -- Unfold L p and use definitional equality (z₀, x₀) + p = (z₀ + p.1, x₀ + p.2)
    have hLp : L p = a_of x₀ * p.1 + B p.2 := by
      simp [L, ContinuousLinearMap.coprod_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul]
    have hfp : f ((z₀, x₀) + p) = f (z₀ + p.1, x₀ + p.2) := rfl
    rw [hfp, hLp]; simp only [T₁, T₂, T₃]; ring
  rw [h_decomp]
  -- Step 7: Bound each term by (c/3) * ‖p‖
  -- T₁ bound: Taylor remainder ≤ C_t * ‖p.1‖² ≤ (c/3) * ‖p‖
  have hT₁ : ‖T₁‖ ≤ c / 3 * ‖p‖ := by
    have h_tay := h_taylor p.1 (x₀ + p.2) hx_mem
      (show ‖x₀ + p.2 - x₀‖ < δ_t by simp [add_sub_cancel_left]; exact lt_of_le_of_lt h_snd hp_δt)
      (show ‖p.1‖ < ρ / 2 from lt_of_le_of_lt h_fst hp_ρ)
    -- h_tay : ‖T₁‖ ≤ C_t * ‖p.1‖ ^ 2
    have hCt_mul : C_t * ‖p‖ ≤ c / 3 := by
      have h1 : (C_t + 1) * ‖p‖ < (C_t + 1) * (c / (3 * (C_t + 1))) :=
        mul_lt_mul_of_pos_left hp_ct hCt1
      have h2 : (C_t + 1) * (c / (3 * (C_t + 1))) = c / 3 := by field_simp
      nlinarith [norm_nonneg p]
    have hsq : ‖p.1‖ ^ 2 ≤ ‖p‖ ^ 2 :=
      sq_le_sq' (by linarith [norm_nonneg p.1, norm_nonneg p]) h_fst
    calc ‖T₁‖ ≤ C_t * ‖p.1‖ ^ 2 := h_tay
      _ ≤ C_t * ‖p‖ ^ 2 := by nlinarith
      _ = C_t * ‖p‖ * ‖p‖ := by ring
      _ ≤ c / 3 * ‖p‖ := by nlinarith [norm_nonneg p]
  -- T₂ bound: derivative variation * h ≤ (c/3) * ‖p‖
  have hT₂ : ‖T₂‖ ≤ c / 3 * ‖p‖ := by
    have h_an := h_a_near (show dist (x₀ + p.2) x₀ < δ₂ by
      simp [dist_eq_norm]; exact lt_of_le_of_lt h_snd hp_δ₂)
    -- h_an : dist (a_of (x₀ + p.2)) (a_of x₀) < c / 3
    rw [dist_eq_norm] at h_an
    calc ‖T₂‖ = ‖(a_of (x₀ + p.2) - a_of x₀) * p.1‖ := rfl
      _ = ‖a_of (x₀ + p.2) - a_of x₀‖ * ‖p.1‖ := norm_mul _ _
      _ ≤ ‖a_of (x₀ + p.2) - a_of x₀‖ * ‖p‖ := by nlinarith [norm_nonneg (a_of (x₀ + p.2) - a_of x₀)]
      _ ≤ c / 3 * ‖p‖ := by nlinarith [norm_nonneg p]
  -- T₃ bound: Fréchet remainder ≤ (c/3) * ‖p‖
  have hT₃ : ‖T₃‖ ≤ c / 3 * ‖p‖ := by
    have h_xb := h_x_bound (show dist p.2 0 < δ₃ by
      simp [dist_zero_right]; exact lt_of_le_of_lt h_snd hp_δ₃)
    -- h_xb : ‖f (z₀, x₀ + p.2) - f (z₀, x₀) - B p.2‖ ≤ c / 3 * ‖p.2‖
    calc ‖T₃‖ ≤ c / 3 * ‖p.2‖ := h_xb
      _ ≤ c / 3 * ‖p‖ := by nlinarith [norm_nonneg p.2, norm_nonneg p]
  -- Step 8: Combine via triangle inequality
  calc ‖T₁ + T₂ + T₃‖ ≤ ‖T₁ + T₂‖ + ‖T₃‖ := norm_add_le _ _
    _ ≤ (‖T₁‖ + ‖T₂‖) + ‖T₃‖ := by linarith [norm_add_le T₁ T₂]
    _ ≤ c / 3 * ‖p‖ + c / 3 * ‖p‖ + c / 3 * ‖p‖ := by linarith
    _ = c * ‖p‖ := by ring

/-! ### Osgood's Lemma (Fin m → ℂ version) -/

/-- **Osgood's Lemma (Fin m → ℂ version)**: A continuous function on an open
    subset of ℂᵐ that is holomorphic in each coordinate separately (with the
    others fixed) is jointly holomorphic. -/
theorem osgood_lemma {m : ℕ} {U' : Set (Fin m → ℂ)} (hU' : IsOpen U')
    (f' : (Fin m → ℂ) → ℂ)
    (hf'_cont : ContinuousOn f' U')
    (hf'_sep : ∀ z ∈ U', ∀ i : Fin m,
      DifferentiableAt ℂ (fun w => f' (Function.update z i w)) (z i)) :
    DifferentiableOn ℂ f' U' := by
  induction m with
  | zero =>
    have : Subsingleton (Fin 0 → ℂ) := inferInstance
    have hU'sub : U'.Subsingleton := fun a _ b _ => Subsingleton.elim a b
    exact hU'sub.differentiableOn
  | succ n ih =>
    intro z hz
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU' z hz
    set cons' : ℂ → (Fin n → ℂ) → (Fin (n + 1) → ℂ) :=
      @Fin.cons n (fun _ => ℂ) with hcons'_def
    set g : ℂ × (Fin n → ℂ) → ℂ := fun p => f' (cons' p.1 p.2) with hg_def
    have hcons_in_ball : ∀ a ∈ Metric.ball (z 0) ε,
        ∀ b ∈ Metric.ball (Fin.tail z) ε,
        cons' a b ∈ Metric.ball z ε := by
      intro a ha b hb
      rw [Metric.mem_ball] at ha hb ⊢
      rw [dist_pi_lt_iff hε]
      intro i
      cases i using Fin.cases with
      | zero => simp only [hcons'_def, Fin.cons_zero]; exact ha
      | succ j =>
        simp only [hcons'_def, Fin.cons_succ]
        exact lt_of_le_of_lt (dist_le_pi_dist b (Fin.tail z) j) hb
    have hcons_cont : Continuous (fun p : ℂ × (Fin n → ℂ) => cons' p.1 p.2) := by
      apply continuous_pi; intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · show Continuous (fun p : ℂ × (Fin n → ℂ) => cons' p.1 p.2 0)
        simp_rw [hcons'_def, Fin.cons_zero]; exact continuous_fst
      · show Continuous (fun p : ℂ × (Fin n → ℂ) => cons' p.1 p.2 j.succ)
        simp_rw [hcons'_def, Fin.cons_succ]; exact (continuous_apply j).comp continuous_snd
    have hg_cont : ContinuousOn g
        (Metric.ball (z 0) ε ×ˢ Metric.ball (Fin.tail z) ε) :=
      (hf'_cont.mono (fun w hw => hball hw)).comp hcons_cont.continuousOn
        (fun ⟨a, b⟩ ⟨ha, hb⟩ => hcons_in_ball a ha b hb)
    have hg_z : ∀ b ∈ Metric.ball (Fin.tail z) ε,
        DifferentiableOn ℂ (fun a => g (a, b)) (Metric.ball (z 0) ε) := by
      intro b hb a ha
      have hmem : cons' a b ∈ U' := hball (hcons_in_ball a ha b hb)
      have hsep := hf'_sep (cons' a b) hmem 0
      have hupd : (fun w => f' (Function.update (cons' a b) 0 w)) =
          (fun w => g (w, b)) := by
        ext w; simp only [hg_def, hcons'_def, Fin.update_cons_zero]
      have hcons0 : cons' a b 0 = a := by simp [hcons'_def, Fin.cons_zero]
      rw [hupd, hcons0] at hsep
      exact hsep.differentiableWithinAt
    have hg_x : ∀ a ∈ Metric.ball (z 0) ε,
        DifferentiableOn ℂ (fun b => g (a, b)) (Metric.ball (Fin.tail z) ε) := by
      intro a ha
      show DifferentiableOn ℂ (fun b => f' (cons' a b)) (Metric.ball (Fin.tail z) ε)
      apply ih Metric.isOpen_ball (fun b => f' (cons' a b))
      · exact (hf'_cont.mono (fun w hw => hball hw)).comp
          (hcons_cont.comp (continuous_const.prodMk continuous_id)).continuousOn
          (fun b hb => hcons_in_ball a ha b hb)
      · intro b hb j
        have hmem : cons' a b ∈ U' := hball (hcons_in_ball a ha b hb)
        have hsep := hf'_sep (cons' a b) hmem j.succ
        have hupd : (fun w => f' (Function.update (cons' a b) j.succ w)) =
            (fun w => f' (cons' a (Function.update b j w))) := by
          ext w; simp only [hcons'_def]; congr 1; rw [← Fin.cons_update]
        have hconsj : cons' a b j.succ = b j := by simp [hcons'_def, Fin.cons_succ]
        rw [hupd, hconsj] at hsep
        exact hsep
    have hg_diff : DifferentiableOn ℂ g
        (Metric.ball (z 0) ε ×ˢ Metric.ball (Fin.tail z) ε) :=
      osgood_lemma_prod Metric.isOpen_ball Metric.isOpen_ball g hg_cont hg_z hg_x
    have hg_at : DifferentiableAt ℂ g (z 0, Fin.tail z) := by
      have hmem : (z 0, Fin.tail z) ∈ Metric.ball (z 0) ε ×ˢ Metric.ball (Fin.tail z) ε :=
        ⟨Metric.mem_ball_self hε, Metric.mem_ball_self hε⟩
      exact (hg_diff _ hmem).differentiableAt
        ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds hmem)
    have hfg : ∀ w, f' w = g (w 0, Fin.tail w) := by
      intro w; simp only [hg_def, hcons'_def, Fin.cons_self_tail]
    have hψ_diff : DifferentiableAt ℂ (fun w : Fin (n+1) → ℂ => (w 0, Fin.tail w)) z := by
      exact DifferentiableAt.prodMk (differentiableAt_apply (𝕜 := ℂ) 0 z)
        (differentiableAt_pi.mpr (fun j => by
          show DifferentiableAt ℂ (fun w : Fin (n+1) → ℂ => w j.succ) z
          exact differentiableAt_apply (𝕜 := ℂ) j.succ z))
    have hf'_at : DifferentiableAt ℂ f' z := by
      have : f' = g ∘ (fun w => (w 0, Fin.tail w)) := by ext w; exact hfg w
      rw [this]; exact hg_at.comp z hψ_diff
    exact hf'_at.differentiableWithinAt

/-! ### Cauchy Integral with Holomorphic Parameter -/

set_option maxHeartbeats 400000 in
/-- The circle integral `∮ (ζ-z)⁻¹ f(ζ, L w) dζ` is differentiable in `w` when `f(ζ,·)` is
    holomorphic and `f` is jointly continuous. Uses the Leibniz rule for parametric integrals
    with a Cauchy estimate for the derivative bound. -/
private theorem differentiableAt_circleIntegral_param_coord
    [CompleteSpace E] [FiniteDimensional ℂ E]
    {z₀ z : ℂ} {r : ℝ} (hr : 0 < r) (hzr : dist z z₀ < r)
    {V : Set E} (hV : IsOpen V)
    {f : ℂ → E → ℂ}
    (hf_cont : ContinuousOn (fun p : ℂ × E => f p.1 p.2) (Metric.closedBall z₀ r ×ˢ V))
    (hf_x_holo : ∀ ζ ∈ Metric.closedBall z₀ r, DifferentiableOn ℂ (f ζ) V)
    {L : ℂ → E} (hL : Differentiable ℂ L) {w₀ : ℂ} (hLw₀ : L w₀ ∈ V) :
    DifferentiableAt ℂ
      (fun w => ∮ ζ in C(z₀, r), (ζ - z)⁻¹ • f ζ (L w)) w₀ := by
  haveI : ProperSpace E := FiniteDimensional.proper ℂ E
  haveI : ProperSpace ℂ := inferInstance
  -- Neighborhood where L maps into V
  obtain ⟨δ, hδ, hδV⟩ : ∃ δ > 0, ∀ w, dist w w₀ < δ → L w ∈ V :=
    Metric.eventually_nhds_iff.mp (hL.continuous.isOpen_preimage V hV |>.mem_nhds
      (Set.mem_preimage.mpr hLw₀))
  -- Uniform bound M on |f| on the relevant compact set
  have hcball_sub : L '' Metric.closedBall w₀ (3 * δ / 4) ⊆ V :=
    fun _ ⟨w, hw, e⟩ => e ▸ hδV w (lt_of_le_of_lt (Metric.mem_closedBall.mp hw) (by linarith))
  obtain ⟨M, hM⟩ := ((isCompact_closedBall z₀ r).prod
    ((isCompact_closedBall w₀ (3 * δ / 4)).image hL.continuous)).exists_bound_of_continuousOn
    (hf_cont.mono (Set.prod_mono le_rfl hcball_sub))
  -- Differentiability of g_ζ(w) = f(ζ, L w) for ζ on the circle, w near w₀
  have hg_diff : ∀ ζ ∈ Metric.closedBall z₀ r, ∀ w, dist w w₀ < δ →
      DifferentiableAt ℂ (fun w => f ζ (L w)) w := by
    intro ζ hζ w hw
    exact ((hf_x_holo ζ hζ _ (hδV w hw)).differentiableAt
      (hV.mem_nhds (hδV w hw))).comp w (hL w)
  -- Cauchy estimate: ‖deriv g_ζ w‖ ≤ M / (δ/4) for w ∈ closedBall(w₀, δ/2)
  have hderiv_bound : ∀ ζ ∈ Metric.closedBall z₀ r, ∀ w ∈ Metric.closedBall w₀ (δ / 2),
      ‖deriv (fun w => f ζ (L w)) w‖ ≤ M / (δ / 4) := by
    intro ζ hζ w hw
    have hδ4 : (0 : ℝ) < δ / 4 := by positivity
    have hw_near : ∀ η, dist η w ≤ δ / 4 → dist η w₀ < δ := by
      intro η hη; calc dist η w₀ ≤ dist η w + dist w w₀ := dist_triangle η w w₀
        _ ≤ δ / 4 + δ / 2 := by linarith [Metric.mem_closedBall.mp hw]
        _ < δ := by linarith
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ4
    · -- DiffContOnCl ℂ g_ζ (ball w (δ/4))
      constructor
      · intro η hη
        exact (hg_diff ζ hζ η (hw_near η (Metric.mem_ball.mp hη).le)).differentiableWithinAt
      · intro η hη
        have := Metric.closure_ball_subset_closedBall hη
        exact (hg_diff ζ hζ η (hw_near η (Metric.mem_closedBall.mp this))).continuousAt.continuousWithinAt
    · intro η hη
      exact hM ⟨ζ, L η⟩ ⟨hζ, ⟨η, Metric.mem_closedBall.mpr (by
        calc dist η w₀ ≤ dist η w + dist w w₀ := dist_triangle η w w₀
          _ = δ / 4 + dist w w₀ := by rw [Metric.mem_sphere.mp hη]
          _ ≤ δ / 4 + δ / 2 := by linarith [Metric.mem_closedBall.mp hw]
          _ ≤ 3 * δ / 4 := by linarith), rfl⟩⟩
  -- Separation of z from the circle
  have hd : 0 < r - dist z z₀ := by linarith
  have hinv_bound : ∀ θ : ℝ, ‖(circleMap z₀ r θ - z)⁻¹‖ ≤ 1 / (r - dist z z₀) := by
    intro θ; rw [norm_inv, one_div]
    apply inv_anti₀ hd
    have hζ_dist : dist (circleMap z₀ r θ) z₀ = r :=
      Metric.mem_sphere.mp (circleMap_mem_sphere z₀ hr.le θ)
    calc r - dist z z₀ = dist (circleMap z₀ r θ) z₀ - dist z z₀ := by rw [hζ_dist]
      _ ≤ dist (circleMap z₀ r θ) z := by
          linarith [dist_triangle (circleMap z₀ r θ) z z₀]
      _ = ‖circleMap z₀ r θ - z‖ := dist_eq_norm _ _
  -- Helper: continuity of integrand in θ for fixed w with L w ∈ V
  -- Helper: the integrand is continuous in θ for fixed w with L w ∈ V
  have hF_cts : ∀ w, L w ∈ V → Continuous (fun θ =>
      deriv (circleMap z₀ r) θ • ((circleMap z₀ r θ - z)⁻¹ • f (circleMap z₀ r θ) (L w))) := by
    intro w hLw
    apply Continuous.smul ((contDiff_circleMap z₀ r).continuous_deriv le_top)
    apply Continuous.smul
    · exact Continuous.inv₀
        ((continuous_circleMap z₀ r).sub continuous_const) fun θ heq => by
        rw [sub_eq_zero] at heq
        have := Metric.mem_sphere.mp (circleMap_mem_sphere z₀ hr.le θ)
        rw [heq] at this; linarith
    · exact (hf_cont.mono (Set.prod_mono Metric.sphere_subset_closedBall (fun x hx => hx))).comp_continuous
        ((continuous_circleMap z₀ r).prodMk continuous_const)
        fun θ => ⟨circleMap_mem_sphere z₀ hr.le θ, hLw⟩
  -- Unfold circle integral
  simp only [circleIntegral]
  -- Apply Leibniz rule (derivative bound version)
  set bnd := r * (1 / (r - dist z z₀)) * (M / (δ / 4))
  suffices h : HasDerivAt (fun w => ∫ θ in (0:ℝ)..2 * Real.pi,
      deriv (circleMap z₀ r) θ • ((circleMap z₀ r θ - z)⁻¹ • f (circleMap z₀ r θ) (L w)))
    (∫ θ in (0:ℝ)..2 * Real.pi, deriv (circleMap z₀ r) θ •
      ((circleMap z₀ r θ - z)⁻¹ • deriv (fun w => f (circleMap z₀ r θ) (L w)) w₀)) w₀
    from h.differentiableAt
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun w θ => deriv (circleMap z₀ r) θ • ((circleMap z₀ r θ - z)⁻¹ •
      deriv (fun w' => f (circleMap z₀ r θ) (L w')) w))
    (s := Metric.closedBall w₀ (δ / 2)) (bound := fun _ => bnd)
    (Metric.closedBall_mem_nhds w₀ (by positivity : (0:ℝ) < δ / 2))
    (by -- AE measurability of F w for w near w₀
      filter_upwards [Metric.ball_mem_nhds w₀ hδ] with w hw
      exact (hF_cts w (hδV w hw)).aestronglyMeasurable)
    (by -- IntervalIntegrable F w₀
      exact (hF_cts w₀ hLw₀).intervalIntegrable (μ := MeasureTheory.volume) 0 (2 * Real.pi))
    (by -- AE measurability of F' w₀ via limit of difference quotients
      -- Define sequence hₙ = δ/(2(n+1)) → 0 with L(w₀+hₙ) ∈ V for all n
      set hn : ℕ → ℂ := fun n => ((δ / (2 * ((n : ℝ) + 1)) : ℝ) : ℂ) with hn_def
      have hn_pos : ∀ n : ℕ, (0 : ℝ) < δ / (2 * ((n : ℝ) + 1)) := fun n =>
        div_pos hδ (mul_pos two_pos n.cast_add_one_pos)
      have hn_ne : ∀ n, hn n ≠ 0 := fun n => by
        simp only [hn_def, ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt (hn_pos n)
      have hn_small : ∀ n, dist (w₀ + hn n) w₀ < δ := by
        intro n
        rw [dist_eq_norm, add_sub_cancel_left]
        simp only [hn_def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hn_pos n)]
        have hle : (2 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
          have := Nat.cast_nonneg (α := ℝ) n; linarith
        calc δ / (2 * ((n : ℝ) + 1))
            ≤ δ / 2 := div_le_div_of_nonneg_left hδ.le two_pos hle
          _ < δ := by linarith
      have hn_tendsto : Tendsto hn atTop (𝓝 0) := by
        rw [Metric.tendsto_atTop]; intro ε hε
        obtain ⟨N, hN⟩ := exists_nat_gt (δ / (2 * ε))
        refine ⟨N, fun n hn_ge => ?_⟩
        simp only [dist_zero_right, hn_def, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (hn_pos n)]
        have h2n : (0 : ℝ) < 2 * ((n : ℝ) + 1) :=
          mul_pos two_pos n.cast_add_one_pos
        have h2ε : (0 : ℝ) < 2 * ε := mul_pos two_pos hε
        have hNn : δ / (2 * ε) < (n : ℝ) + 1 := by
          calc δ / (2 * ε) < ↑N := hN
            _ ≤ ↑n := Nat.cast_le.mpr hn_ge
            _ < (n : ℝ) + 1 := lt_add_one _
        rw [div_lt_iff₀ h2n]
        calc δ = δ / (2 * ε) * (2 * ε) := (div_mul_cancel₀ δ (ne_of_gt h2ε)).symm
          _ < ((n : ℝ) + 1) * (2 * ε) := mul_lt_mul_of_pos_right hNn h2ε
          _ = ε * (2 * ((n : ℝ) + 1)) := by ring
      -- Each difference quotient is AE strongly measurable
      -- Use transparent let instead of set to help unification
      refine aestronglyMeasurable_of_tendsto_ae (ι := ℕ) atTop
        (f := fun n θ => (hn n)⁻¹ • ((deriv (circleMap z₀ r) θ •
          ((circleMap z₀ r θ - z)⁻¹ • f (circleMap z₀ r θ) (L (w₀ + hn n)))) -
          (deriv (circleMap z₀ r) θ •
          ((circleMap z₀ r θ - z)⁻¹ • f (circleMap z₀ r θ) (L w₀))))) ?_ ?_
      · intro n
        exact ((hF_cts _ (hδV _ (hn_small n))).sub
          (hF_cts w₀ hLw₀)).aestronglyMeasurable.const_smul ((hn n)⁻¹)
      · -- Pointwise convergence from HasDerivAt via slope_zero
        apply ae_of_all; intro θ
        have hζ : circleMap z₀ r θ ∈ Metric.closedBall z₀ r :=
          Metric.sphere_subset_closedBall (circleMap_mem_sphere z₀ hr.le θ)
        have hda : HasDerivAt (fun w => deriv (circleMap z₀ r) θ •
            ((circleMap z₀ r θ - z)⁻¹ • f (circleMap z₀ r θ) (L w)))
          (deriv (circleMap z₀ r) θ • ((circleMap z₀ r θ - z)⁻¹ •
            deriv (fun w => f (circleMap z₀ r θ) (L w)) w₀)) w₀ :=
          ((hg_diff _ hζ w₀ (by rw [dist_self]; exact hδ)).hasDerivAt.const_smul
            ((circleMap z₀ r θ - z)⁻¹)).const_smul (deriv (circleMap z₀ r) θ)
        rw [hasDerivAt_iff_tendsto_slope_zero] at hda
        have htend_ne : Tendsto hn atTop (𝓝[≠] (0 : ℂ)) :=
          tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
            hn_tendsto (Eventually.of_forall fun n => hn_ne n)
        exact hda.comp htend_ne)
    (by -- Derivative bound: ‖F'(w, θ)‖ ≤ bnd
      apply Filter.Eventually.of_forall; intro θ _ w hw
      calc ‖deriv (circleMap z₀ r) θ • ((circleMap z₀ r θ - z)⁻¹ •
            deriv (fun w => f (circleMap z₀ r θ) (L w)) w)‖
          = ‖deriv (circleMap z₀ r) θ‖ * (‖(circleMap z₀ r θ - z)⁻¹‖ *
            ‖deriv (fun w => f (circleMap z₀ r θ) (L w)) w‖) := by
            rw [norm_smul, norm_smul]
        _ ≤ r * (1 / (r - dist z z₀)) * (M / (δ / 4)) := by
            rw [mul_assoc]
            apply mul_le_mul _ _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
            · simp only [deriv_circleMap, norm_mul, norm_circleMap_zero, abs_of_pos hr,
                Complex.norm_I, mul_one]; exact le_refl _
            · apply mul_le_mul (hinv_bound θ)
                (hderiv_bound _ (Metric.sphere_subset_closedBall
                  (circleMap_mem_sphere z₀ hr.le θ)) w hw) (norm_nonneg _) (by positivity))
    intervalIntegrable_const
    (by -- HasDerivAt for each θ and w ∈ s
      apply Filter.Eventually.of_forall; intro θ _ w hw
      have hwδ : dist w w₀ < δ :=
        lt_of_le_of_lt (Metric.mem_closedBall.mp hw) (by linarith)
      have hζ : circleMap z₀ r θ ∈ Metric.closedBall z₀ r :=
        Metric.sphere_subset_closedBall (circleMap_mem_sphere z₀ hr.le θ)
      exact ((hg_diff _ hζ w hwδ).hasDerivAt.const_smul
        ((circleMap z₀ r θ - z)⁻¹)).const_smul (deriv (circleMap z₀ r) θ))).2

private lemma differentiable_update_coord
    [FiniteDimensional ℂ E]
    (φ : E ≃L[ℂ] (Fin (Module.finrank ℂ E) → ℂ))
    (x₀ : E) (i : Fin (Module.finrank ℂ E)) :
    Differentiable ℂ (fun w => φ.symm (Function.update (φ x₀) i w)) := by
  apply φ.symm.differentiable.comp
  exact differentiable_pi.mpr fun j => by
    by_cases hji : j = i
    · subst hji
      have : (fun w => Function.update (φ x₀) j w j) = id :=
        funext fun w => Function.update_self j w (φ x₀)
      rw [this]; exact differentiable_id
    · have : (fun w => Function.update (φ x₀) i w j) = fun _ => (φ x₀) j :=
        funext fun w => Function.update_of_ne hji w (φ x₀)
      rw [this]; exact differentiable_const _

/-- Helper: the Cauchy integral `G(z,x) = (2πi)⁻¹ ∮ (ζ-z)⁻¹ f(ζ,x) dζ` is
    holomorphic in `x` for fixed `z`, given that `f(ζ,·)` is holomorphic for each `ζ`. -/
private theorem cauchyIntegral_param_x_holo [CompleteSpace E] [FiniteDimensional ℂ E]
    {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    {V : Set E} (hV : IsOpen V)
    (f : ℂ → E → ℂ)
    (hf_cont : ContinuousOn (fun p : ℂ × E => f p.1 p.2)
      (Metric.closedBall z₀ r ×ˢ V))
    (hf_x_holo : ∀ ζ ∈ Metric.closedBall z₀ r, DifferentiableOn ℂ (f ζ) V)
    (hG_cont : ContinuousOn
      (fun p : ℂ × E => (2 * ↑Real.pi * I)⁻¹ • ∮ ζ in C(z₀, r), (ζ - p.1)⁻¹ • f ζ p.2)
      (Metric.ball z₀ r ×ˢ V)) :
    ∀ z ∈ Metric.ball z₀ r,
      DifferentiableOn ℂ
        (fun x => (2 * ↑Real.pi * I)⁻¹ • ∮ ζ in C(z₀, r), (ζ - z)⁻¹ • f ζ x) V := by
  intro z hz
  haveI : ProperSpace E := FiniteDimensional.proper ℂ E
  have hzr := Metric.mem_ball.mp hz
  -- Transfer to coordinates via φ : E ≃L[ℂ] (Fin n → ℂ)
  set φ := (Module.finBasis ℂ E).equivFunL
  have hV' : IsOpen (φ '' V) := φ.toHomeomorph.isOpenMap V hV
  -- Define the transferred function (without (2πi)⁻¹ factor to keep kernel checks fast)
  let H : (Fin (Module.finrank ℂ E) → ℂ) → ℂ :=
    fun y => ∮ ζ in C(z₀, r), (ζ - z)⁻¹ • f ζ (φ.symm y)
  -- Suffices: H is DifferentiableOn φ '' V (then scale by (2πi)⁻¹)
  suffices hH : DifferentiableOn ℂ H (φ '' V) by
    intro x₀ hx₀
    have hH' := hH.const_smul ((2 * ↑Real.pi * I)⁻¹ : ℂ)
    -- hH' : DifferentiableOn ℂ ((2πi)⁻¹ • H) (φ '' V)
    have hda : DifferentiableAt ℂ (((2 * ↑Real.pi * I)⁻¹ • H) ∘ φ) x₀ :=
      ((hH' _ ⟨x₀, hx₀, rfl⟩).differentiableAt (hV'.mem_nhds ⟨x₀, hx₀, rfl⟩)).comp
        x₀ φ.toContinuousLinearMap.differentiableAt
    have : ((2 * ↑Real.pi * I)⁻¹ • H) ∘ φ =
        fun x => (2 * ↑Real.pi * I)⁻¹ • ∮ ζ in C(z₀, r), (ζ - z)⁻¹ • f ζ x := by
      ext x; simp [H, Function.comp, Pi.smul_apply, φ.symm_apply_apply]
    rw [this] at hda
    exact hda.differentiableWithinAt
  -- Apply osgood_lemma to H
  apply osgood_lemma hV' H
  · -- ContinuousOn H (φ '' V): extract from hG_cont by cancelling the (2πi)⁻¹ factor
    show ContinuousOn (fun y =>
      ∮ ζ in C(z₀, r), (ζ - z)⁻¹ • f ζ (φ.symm y)) (φ '' V)
    have hc : (2 * ↑Real.pi * I : ℂ) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero
      (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
    have h_with_factor : ContinuousOn (fun y => (2 * ↑Real.pi * I)⁻¹ •
        ∮ ζ in C(z₀, r), (ζ - z)⁻¹ • f ζ (φ.symm y)) (φ '' V) := by
      have : ContinuousOn (fun y => (fun p : ℂ × E =>
          (2 * ↑Real.pi * I)⁻¹ • ∮ ζ in C(z₀, r), (ζ - p.1)⁻¹ • f ζ p.2)
          (z, φ.symm y)) (φ '' V) :=
        hG_cont.comp (continuous_const.prodMk φ.symm.continuous).continuousOn
          (fun y (hy : y ∈ φ '' V) => by
            obtain ⟨x, hx, rfl⟩ := hy
            exact ⟨Metric.mem_ball.mpr hzr, by simp [φ.symm_apply_apply]; exact hx⟩)
      convert this using 1
    -- Recover ContinuousOn of the bare integral by scaling: g = (2πi) • ((2πi)⁻¹ • g)
    have : (fun y => ∮ ζ in C(z₀, r), (ζ - z)⁻¹ • f ζ (φ.symm y)) =
        (fun y => (2 * ↑Real.pi * I) • ((2 * ↑Real.pi * I)⁻¹ •
          ∮ ζ in C(z₀, r), (ζ - z)⁻¹ • f ζ (φ.symm y))) := by
      ext y; rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    rw [this]
    exact h_with_factor.const_smul _
  · -- Separately holomorphic in each coordinate
    intro y hy i
    obtain ⟨x₀, hx₀V, rfl⟩ := hy
    have hL_diff := differentiable_update_coord φ x₀ i
    have hLw₀_mem : φ.symm (Function.update (φ x₀) i (φ x₀ i)) ∈ V := by
      rw [Function.update_eq_self, φ.symm_apply_apply]; exact hx₀V
    exact differentiableAt_circleIntegral_param_coord hr hzr hV hf_cont hf_x_holo
      hL_diff hLw₀_mem

/-- **Cauchy integral with holomorphic parameter**: If f(ζ, x) is continuous on
    closedBall(z₀, r) × V and holomorphic in x for each ζ, then
    G(z, x) = (2πi)⁻¹ · ∮ f(ζ, x) / (ζ - z) dζ is jointly holomorphic
    on ball(z₀, r) × V.

    The proof uses Osgood's lemma: G is continuous on ball × V, holomorphic
    in z (by the Cauchy power series), and holomorphic in x (by parametric
    differentiation under the integral sign). -/
theorem differentiableOn_cauchyIntegral_param [CompleteSpace E] [FiniteDimensional ℂ E]
    {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    {V : Set E} (hV : IsOpen V)
    (f : ℂ → E → ℂ)
    (hf_cont : ContinuousOn (fun p : ℂ × E => f p.1 p.2)
      (Metric.closedBall z₀ r ×ˢ V))
    (hf_x_holo : ∀ ζ ∈ Metric.closedBall z₀ r, DifferentiableOn ℂ (f ζ) V) :
    DifferentiableOn ℂ
      (fun p : ℂ × E =>
        (2 * ↑Real.pi * I)⁻¹ • ∮ ζ in C(z₀, r), (ζ - p.1)⁻¹ • f ζ p.2)
      (Metric.ball z₀ r ×ˢ V) := by
  -- Define G for readability
  set G : ℂ × E → ℂ := fun p =>
    (2 * ↑Real.pi * I)⁻¹ • ∮ ζ in C(z₀, r), (ζ - p.1)⁻¹ • f ζ p.2
  -- Prove ContinuousOn as named hypothesis (needed for x-holomorphicity below)
  have hG_cont : ContinuousOn G (Metric.ball z₀ r ×ˢ V) := by
    -- G = (2πi)⁻¹ • (circle integral); suffices to show the integral is ContinuousOn
    suffices h : ContinuousOn (fun p : ℂ × E =>
        ∮ ζ in C(z₀, r), (ζ - p.1)⁻¹ • f ζ p.2) (Metric.ball z₀ r ×ˢ V)
      from h.const_smul _
    intro ⟨z', x'⟩ ⟨hz', hx'⟩
    apply ContinuousAt.continuousWithinAt
    simp only [circleIntegral]
    haveI : ProperSpace E := FiniteDimensional.proper ℂ E
    -- Distance from z' to the sphere
    have hz'r : dist z' z₀ < r := Metric.mem_ball.mp hz'
    set d := (r - dist z' z₀) / 2 with hd_def
    have hd : 0 < d := by linarith
    -- Compact neighborhood of x' inside V
    obtain ⟨δ, hδ, hcball_V⟩ : ∃ δ > 0, Metric.closedBall x' δ ⊆ V := by
      obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp hV x' hx'
      exact ⟨ε / 2, by positivity,
        fun y hy => hb (lt_of_le_of_lt (Metric.mem_closedBall.mp hy) (by linarith))⟩
    -- f bounded on compact sphere × closedBall(x', δ)
    have hKsub : Metric.sphere z₀ r ×ˢ Metric.closedBall x' δ ⊆
        Metric.closedBall z₀ r ×ˢ V :=
      Set.prod_mono Metric.sphere_subset_closedBall hcball_V
    obtain ⟨M, hM⟩ := ((isCompact_sphere z₀ r).prod
      (isCompact_closedBall x' δ)).exists_bound_of_continuousOn (hf_cont.mono hKsub)
    -- Neighborhood radius
    set ε₀ := min d δ with hε₀_def
    have hε₀ : 0 < ε₀ := lt_min hd hδ
    -- Key facts about the neighborhood
    have h_z_in_ball : ∀ p : ℂ × E, dist p (z', x') < ε₀ →
        p.1 ∈ Metric.ball z₀ r := by
      intro ⟨z, x⟩ hp
      rw [Metric.mem_ball]
      calc dist z z₀ ≤ dist z z' + dist z' z₀ := dist_triangle z z' z₀
        _ < ε₀ + dist z' z₀ := by
            have : dist z z' ≤ dist (z, x) (z', x') := by
              simp [Prod.dist_eq]
            linarith
        _ ≤ d + dist z' z₀ := by linarith [min_le_left d δ]
        _ < r := by linarith [hd_def]
    have h_x_in_cball : ∀ p : ℂ × E, dist p (z', x') < ε₀ →
        p.2 ∈ Metric.closedBall x' δ := by
      intro ⟨z, x⟩ hp
      rw [Metric.mem_closedBall]
      calc dist x x' ≤ dist (z, x) (z', x') := by simp [Prod.dist_eq]
        _ ≤ ε₀ := le_of_lt hp
        _ ≤ δ := min_le_right d δ
    have h_inv_bound : ∀ p : ℂ × E, dist p (z', x') < ε₀ → ∀ θ : ℝ,
        ‖(circleMap z₀ r θ - p.1)⁻¹‖ ≤ 1 / d := by
      intro ⟨z, x⟩ hp θ
      rw [norm_inv, one_div]
      apply inv_anti₀ hd
      have hζ : dist (circleMap z₀ r θ) z₀ = r :=
        Metric.mem_sphere.mp (circleMap_mem_sphere z₀ hr.le θ)
      have hfst : dist z z' ≤ dist (z, x) (z', x') := by
        simp [Prod.dist_eq]
      calc d ≤ r - dist z' z₀ - dist z z' := by linarith [min_le_left d δ]
        _ ≤ dist (circleMap z₀ r θ) z₀ - dist z₀ z' - dist z z' := by
              rw [hζ, dist_comm z₀ z']
        _ ≤ dist (circleMap z₀ r θ) z := by
              linarith [dist_triangle (circleMap z₀ r θ) z z₀,
                dist_triangle z z' z₀, dist_comm z' z₀]
        _ = ‖circleMap z₀ r θ - z‖ := dist_eq_norm_sub _ _
    have h_f_bound : ∀ p : ℂ × E, dist p (z', x') < ε₀ → ∀ θ : ℝ,
        ‖f (circleMap z₀ r θ) p.2‖ ≤ M := by
      intro ⟨z, x⟩ hp θ
      exact hM ⟨circleMap z₀ r θ, x⟩ ⟨circleMap_mem_sphere z₀ hr.le θ, h_x_in_cball ⟨z, x⟩ hp⟩
    -- Apply dominated convergence for continuity
    apply intervalIntegral.continuousAt_of_dominated_interval
      (bound := fun _ => r * (1 / d) * M)
    · -- AEStronglyMeasurable of integrand for p near p₀
      filter_upwards [Metric.ball_mem_nhds (z', x') hε₀] with p hp
      apply (ContinuousOn.aestronglyMeasurable · measurableSet_uIoc)
      apply ContinuousOn.smul ((contDiff_circleMap z₀ r).continuous_deriv le_top).continuousOn
      apply ContinuousOn.smul
      · -- (circleMap θ - z)⁻¹ continuous in θ on uIoc
        apply ContinuousOn.inv₀
          ((continuous_circleMap z₀ r).continuousOn.sub continuousOn_const) fun θ _ heq => by
          rw [sub_eq_zero] at heq
          have h1 := Metric.mem_sphere.mp (circleMap_mem_sphere z₀ hr.le θ)
          rw [heq] at h1; exact absurd (Metric.mem_ball.mp (h_z_in_ball p hp)) (not_lt.mpr h1.ge)
      · -- f(circleMap θ, x) continuous in θ on uIoc
        apply ContinuousOn.comp (hf_cont.mono hKsub)
          ((continuous_circleMap z₀ r).continuousOn.prodMk continuousOn_const)
          fun θ _ => ⟨circleMap_mem_sphere z₀ hr.le θ, h_x_in_cball p hp⟩
    · -- Uniform bound
      filter_upwards [Metric.ball_mem_nhds (z', x') hε₀] with p hp
      apply Eventually.of_forall; intro θ _
      calc ‖deriv (circleMap z₀ r) θ • (circleMap z₀ r θ - p.1)⁻¹ •
              f (circleMap z₀ r θ) p.2‖
          = ‖deriv (circleMap z₀ r) θ‖ * ‖(circleMap z₀ r θ - p.1)⁻¹‖ *
              ‖f (circleMap z₀ r θ) p.2‖ := by
              rw [norm_smul, norm_smul, mul_assoc]
        _ ≤ r * (1 / d) * M := by
            gcongr
            · simp only [deriv_circleMap, norm_mul, norm_circleMap_zero,
                norm_I, mul_one]; exact le_of_eq (abs_of_pos hr)
            · exact h_inv_bound p hp θ
            · exact h_f_bound p hp θ
    · -- Bound integrable (constant)
      exact intervalIntegrable_const
    · -- Pointwise continuity of integrand in p at p₀
      apply Eventually.of_forall; intro θ _
      apply ContinuousAt.smul continuousAt_const
      apply ContinuousAt.smul
      · -- (circleMap θ - p.1)⁻¹ ContinuousAt in p
        apply ContinuousAt.inv₀ (continuousAt_const.sub continuous_fst.continuousAt)
        intro heq; rw [sub_eq_zero] at heq
        have h1 := Metric.mem_sphere.mp (circleMap_mem_sphere z₀ hr.le θ)
        rw [heq] at h1; linarith
      · -- f(circleMap θ, p.2) ContinuousAt in p
        -- Factor as (fun x => f (circleMap z₀ r θ) x) ∘ Prod.snd
        -- f(circleMap θ, ·) is ContinuousOn V (slice of hf_cont)
        have hfζ_cont : ContinuousOn (fun x => f (circleMap z₀ r θ) x) V :=
          hf_cont.comp (continuous_const.prodMk continuous_id).continuousOn
            (fun x hx => ⟨Metric.sphere_subset_closedBall
              (circleMap_mem_sphere z₀ hr.le θ), hx⟩)
        exact (hfζ_cont.continuousAt (hV.mem_nhds hx')).comp
          continuous_snd.continuousAt
  have hG_z : ∀ x ∈ V, DifferentiableOn ℂ (fun z => G (z, x)) (Metric.ball z₀ r) := by
    -- For fixed x, the Cauchy integral has a power series in z
    intro x hx
    -- f(·, x) is continuous on closedBall, hence circle-integrable
    have hfx_cont : ContinuousOn (fun ζ => f ζ x) (Metric.closedBall z₀ r) :=
      hf_cont.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun ζ hζ => ⟨hζ, hx⟩)
    have hci : CircleIntegrable (fun ζ => f ζ x) z₀ r :=
      (hfx_cont.mono Metric.sphere_subset_closedBall).circleIntegrable hr.le
    -- Power series representation
    set R : NNReal := ⟨r, hr.le⟩
    have hR : (0 : NNReal) < R := by exact_mod_cast hr
    have hps := hasFPowerSeriesOn_cauchy_integral hci hR
    -- Convert DifferentiableOn from EMetric.ball to Metric.ball
    intro z hz
    have hz_emem : (z : ℂ) ∈ Metric.eball z₀ (↑R) := by
      show edist z z₀ < ↑R
      rw [edist_eq_enorm_sub]
      have : dist z z₀ < r := Metric.mem_ball.mp hz
      rw [dist_eq_norm] at this
      exact_mod_cast this
    exact (hps.analyticAt_of_mem hz_emem).differentiableAt.differentiableWithinAt
  have hG_x : ∀ z ∈ Metric.ball z₀ r, DifferentiableOn ℂ (fun x => G (z, x)) V :=
    cauchyIntegral_param_x_holo hr hV f hf_cont hf_x_holo hG_cont
  exact osgood_lemma_prod Metric.isOpen_ball hV G hG_cont hG_z hG_x

/-! ### 1D Extension Across the Real Line

A continuous function on an open set V ⊂ ℂ that is holomorphic on V \ {Im = 0}
is holomorphic on all of V. This is proved via Morera's theorem: the rectangle
integrals vanish because crossing rectangles split into sub-rectangles in the
upper and lower half-planes. -/

/-- A continuous function on an open set in ℂ that is holomorphic away from the
    real line is holomorphic everywhere. Uses Morera's theorem. -/
theorem differentiableOn_of_continuous_off_real_1d
    {V : Set ℂ} (hV : IsOpen V)
    (f : ℂ → ℂ) (hf_cont : ContinuousOn f V)
    (hf_holo : DifferentiableOn ℂ f (V \ {z : ℂ | z.im = 0})) :
    DifferentiableOn ℂ f V := by
  -- At each point z ∈ V, show DifferentiableWithinAt
  intro z₀ hz₀
  -- If z₀ is not on the real line, f is already holomorphic near z₀
  by_cases hzim : z₀.im ≠ 0
  · have : z₀ ∈ V \ {z | z.im = 0} := ⟨hz₀, hzim⟩
    have hopen : IsOpen (V \ {z : ℂ | z.im = 0}) :=
      hV.sdiff (isClosed_eq Complex.continuous_im continuous_const)
    exact ((hf_holo z₀ this).differentiableAt (hopen.mem_nhds this)).differentiableWithinAt
  · -- z₀ is on the real line. Use Morera's theorem.
    push_neg at hzim -- hzim : z₀.im = 0
    -- Find a ball around z₀ inside V
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV z₀ hz₀
    -- Prove DifferentiableOn on ball, then extract DifferentiableAt at z₀
    suffices h : DifferentiableOn ℂ f (Metric.ball z₀ r) from
      ((h z₀ (Metric.mem_ball_self hr)).differentiableAt
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).differentiableWithinAt
    apply (isConservativeOn_and_continuousOn_iff_isDifferentiableOn
      Metric.isOpen_ball).mp
    constructor
    · -- IsConservativeOn f (ball z₀ r)
      -- Helper: continuity on ball
      have hf_cont_ball : ContinuousOn f (Metric.ball z₀ r) :=
        hf_cont.mono (fun _ hw => hball hw)
      -- Helper: DifferentiableAt for points off the real line in the ball
      have hf_diff_at : ∀ c : ℂ, c.im ≠ 0 → c ∈ Metric.ball z₀ r →
          DifferentiableAt ℂ f c := by
        intro c hc hcball
        have hmem : c ∈ V \ {z | z.im = 0} := ⟨hball hcball, hc⟩
        exact (hf_holo c hmem).differentiableAt
          ((hV.sdiff (isClosed_eq Complex.continuous_im continuous_const)).mem_nhds hmem)
      intro z w hrect
      apply eq_neg_of_add_eq_zero_left
      rw [wedgeIntegral_add_wedgeIntegral_eq]
      by_cases hcross : min z.im w.im < 0 ∧ 0 < max z.im w.im
      · -- CROSSING case: rectangle straddles the real line
        obtain ⟨hmin_neg, hmax_pos⟩ := hcross
        let z₁ : ℂ := ⟨z.re, 0⟩
        let w₁ : ℂ := ⟨w.re, 0⟩
        have h0_mem : (0 : ℝ) ∈ [[z.im, w.im]] := by
          rcases le_total z.im w.im with h | h
          · rw [Set.mem_uIcc]; left
            exact ⟨le_of_lt (by rwa [min_eq_left h] at hmin_neg),
                   le_of_lt (by rwa [max_eq_right h] at hmax_pos)⟩
          · rw [Set.mem_uIcc]; right
            exact ⟨le_of_lt (by rwa [min_eq_right h] at hmin_neg),
                   le_of_lt (by rwa [max_eq_left h] at hmax_pos)⟩
        have hzim_ne : z.im ≠ 0 := by
          intro heq; rw [heq] at hmin_neg hmax_pos
          rcases le_or_gt w.im 0 with h | h
          · linarith [max_eq_left h (a := (0 : ℝ))]
          · linarith [min_eq_left (le_of_lt h) (a := (0 : ℝ))]
        have hwim_ne : w.im ≠ 0 := by
          intro heq; rw [heq] at hmin_neg hmax_pos
          rcases le_or_gt z.im 0 with h | h
          · linarith [max_eq_right h (a := z.im) (b := (0 : ℝ))]
          · linarith [min_eq_right (le_of_lt h) (a := z.im) (b := (0 : ℝ))]
        -- Sub-rectangle continuity (following EdgeOfWedge.lean pattern)
        have hcont_sub1 : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, (0 : ℝ)]]) :=
          hf_cont_ball.mono (fun c hc => hrect
            (show c ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]] from by
              rw [mem_reProdIm] at hc ⊢
              exact ⟨hc.1, Set.uIcc_subset_uIcc_left h0_mem hc.2⟩))
        have hcont_sub2 : ContinuousOn f ([[z.re, w.re]] ×ℂ [[(0 : ℝ), w.im]]) :=
          hf_cont_ball.mono (fun c hc => hrect
            (show c ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]] from by
              rw [mem_reProdIm] at hc ⊢
              exact ⟨hc.1, Set.uIcc_subset_uIcc_right h0_mem hc.2⟩))
        -- DifferentiableOn for sub-rectangles
        have hdiff_sub1 : DifferentiableOn ℂ f
            (Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im 0) (max z.im 0)) := by
          intro c hc; rw [mem_reProdIm] at hc
          have hcim := mem_Ioo.mp hc.2
          have hc_ne : c.im ≠ 0 := by
            rcases lt_or_gt_of_ne hzim_ne with hz | hz
            · exact ne_of_lt (lt_of_lt_of_le hcim.2 (by rw [max_eq_right (le_of_lt hz)]))
            · exact ne_of_gt (lt_of_le_of_lt (by rw [min_eq_right (le_of_lt hz)]) hcim.1)
          exact (hf_diff_at c hc_ne (hrect
            (show c ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]] from by
              rw [mem_reProdIm]; exact ⟨Ioo_subset_Icc_self hc.1,
              Set.uIcc_subset_uIcc_left h0_mem (Ioo_subset_Icc_self hc.2)⟩))).differentiableWithinAt
        have hdiff_sub2 : DifferentiableOn ℂ f
            (Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min 0 w.im) (max 0 w.im)) := by
          intro c hc; rw [mem_reProdIm] at hc
          have hcim := mem_Ioo.mp hc.2
          have hc_ne : c.im ≠ 0 := by
            rcases lt_or_gt_of_ne hwim_ne with hw | hw
            · exact ne_of_lt (lt_of_lt_of_le hcim.2 (by rw [max_eq_left (le_of_lt hw)]))
            · exact ne_of_gt (lt_of_le_of_lt (by rw [min_eq_left (le_of_lt hw)]) hcim.1)
          exact (hf_diff_at c hc_ne (hrect
            (show c ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]] from by
              rw [mem_reProdIm]; exact ⟨Ioo_subset_Icc_self hc.1,
              Set.uIcc_subset_uIcc_right h0_mem (Ioo_subset_Icc_self hc.2)⟩))).differentiableWithinAt
        -- Sub-rectangle integrals vanish by Cauchy-Goursat
        have h_sub1 := integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
          f z w₁ (by convert hcont_sub1 using 2) (by convert hdiff_sub1 using 2)
        have h_sub2 := integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
          f z₁ w (by convert hcont_sub2 using 2) (by convert hdiff_sub2 using 2)
        simp only [show (z₁.im : ℝ) = 0 from rfl, show (w₁.im : ℝ) = 0 from rfl,
          show re z₁ = z.re from rfl, show re w₁ = w.re from rfl,
          Complex.ofReal_zero, zero_mul, add_zero] at h_sub1 h_sub2
        simp only [smul_eq_mul] at h_sub1 h_sub2 ⊢
        -- IntervalIntegrable for splitting
        have hint : ∀ (ρ : ℝ), ρ ∈ [[z.re, w.re]] →
            ∀ a' b', [[a', b']] ⊆ [[z.im, w.im]] →
            IntervalIntegrable (fun y => f (↑ρ + ↑y * I)) volume a' b' := by
          intro ρ hρ a' b' hab'
          apply ContinuousOn.intervalIntegrable
          apply hf_cont_ball.comp ((continuousOn_const).add
            ((Complex.continuous_ofReal.continuousOn).mul continuousOn_const))
          intro y hy
          apply hrect
          show (↑ρ + ↑(y : ℝ) * I) ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]]
          rw [mem_reProdIm]
          constructor
          · simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
              Complex.ofReal_im, Complex.I_re, Complex.I_im]; exact hρ
          · simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
              Complex.ofReal_re, Complex.I_re, Complex.I_im]; exact hab' hy
        have hw_mem : w.re ∈ [[z.re, w.re]] := Set.right_mem_uIcc
        have hz_mem : z.re ∈ [[z.re, w.re]] := Set.left_mem_uIcc
        have hsub1 : [[z.im, (0 : ℝ)]] ⊆ [[z.im, w.im]] :=
          Set.uIcc_subset_uIcc_left h0_mem
        have hsub2 : [[(0 : ℝ), w.im]] ⊆ [[z.im, w.im]] :=
          Set.uIcc_subset_uIcc_right h0_mem
        rw [← integral_add_adjacent_intervals (hint w.re hw_mem z.im 0 hsub1)
              (hint w.re hw_mem 0 w.im hsub2),
            ← integral_add_adjacent_intervals (hint z.re hz_mem z.im 0 hsub1)
              (hint z.re hz_mem 0 w.im hsub2)]
        linear_combination h_sub1 + h_sub2
      · -- NON-CROSSING: f holomorphic on open interior, direct Cauchy-Goursat
        push_neg at hcross
        exact integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f z w
          (hf_cont_ball.mono hrect) (by
          intro c hc; rw [mem_reProdIm] at hc
          rcases le_or_gt 0 (min z.im w.im) with hge | hlt
          · exact (hf_diff_at c (ne_of_gt
              (lt_of_le_of_lt hge (mem_Ioo.mp hc.2).1)) (hrect
              (show c ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]] from by
                rw [mem_reProdIm]; exact ⟨Ioo_subset_Icc_self hc.1,
                Ioo_subset_Icc_self hc.2⟩))).differentiableWithinAt
          · exact (hf_diff_at c (ne_of_lt
              (lt_of_lt_of_le (mem_Ioo.mp hc.2).2 (hcross hlt))) (hrect
              (show c ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]] from by
                rw [mem_reProdIm]; exact ⟨Ioo_subset_Icc_self hc.1,
                Ioo_subset_Icc_self hc.2⟩))).differentiableWithinAt)
    · -- ContinuousOn
      exact hf_cont.mono (fun _ hw => hball hw)

/-! ### Holomorphic Extension Across Real Boundaries -/

/-- A continuous function on an open set in ℂᵐ that is holomorphic on the
    complement of the "real slice" {z : Im(z) = 0} is holomorphic everywhere.

    For each coordinate direction, the function restricted to a complex line
    is continuous and holomorphic off the real line. By
    `differentiableOn_of_continuous_off_real_1d`, it is holomorphic in that
    direction. Osgood's lemma then gives joint holomorphicity. -/
theorem holomorphic_extension_across_real {m : ℕ}
    {U : Set (Fin m → ℂ)} (hU : IsOpen U)
    (f : (Fin m → ℂ) → ℂ)
    (hf_cont : ContinuousOn f U)
    (hf_holo_off : DifferentiableOn ℂ f
      (U \ { z : Fin m → ℂ | ∀ i : Fin m, (z i).im = 0 })) :
    DifferentiableOn ℂ f U := by
  -- Apply Osgood's lemma
  apply osgood_lemma hU f hf_cont
  -- Show f is separately holomorphic at each point
  -- Helper: Function.update z i is continuous and differentiable
  -- Use update_apply to reduce to if/then/else on each component
  have hupdate_cont : ∀ (z₀ : Fin m → ℂ) (k : Fin m),
      Continuous (Function.update z₀ k) := by
    intro z₀ k; apply continuous_pi; intro j
    simp_rw [Function.update_apply]
    exact continuous_if_const _ (fun _ => continuous_id) (fun _ => continuous_const)
  have hupdate_diff : ∀ (z₀ : Fin m → ℂ) (k : Fin m) (w : ℂ),
      DifferentiableAt ℂ (Function.update z₀ k) w := by
    intro z₀ k w; rw [differentiableAt_pi]; intro j
    simp_rw [Function.update_apply]
    split <;> simp_all
  -- Helper: {z | ∀ j, (z j).im = 0} is closed
  have hreal_closed : IsClosed {z : Fin m → ℂ | ∀ j, (z j).im = 0} := by
    have : {z : Fin m → ℂ | ∀ j, (z j).im = 0} = ⋂ j, {z | (z j).im = 0} := by
      ext z; simp
    rw [this]
    exact isClosed_iInter (fun j => isClosed_eq
      (Complex.continuous_im.comp (continuous_apply j)) continuous_const)
  intro z hz i
  by_cases hreal : ∀ j : Fin m, (z j).im = 0
  · -- z IS on the real slice. Use 1D extension.
    set V : Set ℂ := (Function.update z i) ⁻¹' U with hV_def
    have hV_open : IsOpen V := hU.preimage (hupdate_cont z i)
    have hV_mem : z i ∈ V := by
      show Function.update z i (z i) ∈ U
      rw [Function.update_eq_self]; exact hz
    -- g = f ∘ (Function.update z i) is continuous on V
    have hg_cont : ContinuousOn (fun w => f (Function.update z i w)) V :=
      hf_cont.comp (hupdate_cont z i).continuousOn (fun _ hw => hw)
    -- g is holomorphic on V \ {Im = 0}
    have hg_holo : DifferentiableOn ℂ (fun w => f (Function.update z i w))
        (V \ {w : ℂ | w.im = 0}) := by
      intro w ⟨hwV, hwim⟩
      have hwim' : ¬w.im = 0 := hwim
      have hnotreal : ¬(∀ j, (Function.update z i w j).im = 0) := by
        push_neg; exact ⟨i, by simp [Function.update_self, hwim']⟩
      have hmem : Function.update z i w ∈ U \ {z | ∀ j, (z j).im = 0} :=
        ⟨hwV, hnotreal⟩
      have hopen := hU.sdiff hreal_closed
      have hf_at := (hf_holo_off _ hmem).differentiableAt (hopen.mem_nhds hmem)
      exact (hf_at.comp w ((hupdate_diff z i) w)).differentiableWithinAt
    -- By 1D extension, g is holomorphic on V
    have hg_diff : DifferentiableOn ℂ (fun w => f (Function.update z i w)) V :=
      differentiableOn_of_continuous_off_real_1d hV_open _ hg_cont hg_holo
    exact (hg_diff (z i) hV_mem).differentiableAt (hV_open.mem_nhds hV_mem)
  · -- z is NOT on the real slice. f is directly differentiable near z.
    -- hreal : ¬∀ j, (z j).im = 0, which is exactly z ∉ {z | ∀ j, ...}
    have hmem : z ∈ U \ {z | ∀ j, (z j).im = 0} := ⟨hz, hreal⟩
    have hopen := hU.sdiff hreal_closed
    have hf_at : DifferentiableAt ℂ f z :=
      (hf_holo_off z hmem).differentiableAt (hopen.mem_nhds hmem)
    -- f ∘ (Function.update z i) is differentiable at z i
    have hf_at' : DifferentiableAt ℂ f (Function.update z i (z i)) := by
      rwa [Function.update_eq_self]
    exact hf_at'.comp (z i) ((hupdate_diff z i) (z i))

/-! ### Gluing Lemma for Tube Domains -/

/-- Given a function F that is continuous on an open ball in ℂᵐ and holomorphic away
    from the real slice `{z : ∀ i, (z i).im = 0}`, F is holomorphic on the entire ball.

    This is a direct application of `holomorphic_extension_across_real`.

    **Limitation**: This only helps prove the edge-of-the-wedge theorem when the cone C
    satisfies `C ∪ (-C) ∪ {0} = ℝᵐ` (e.g., m = 1 with C = (0,∞)), because otherwise
    `TubeDomain(C) ∪ TubeDomain(-C)` does not cover all non-real points, and
    the `hF_holo_off` hypothesis cannot be established from the tube domain holomorphicity
    of f₊ and f₋ alone. For general convex cones (including the forward light cone),
    the multi-dimensional edge-of-the-wedge requires iterated 1D extensions. -/
theorem tube_domain_gluing {m : ℕ}
    (x₀ : Fin m → ℝ) (r : ℝ)
    (F : (Fin m → ℂ) → ℂ)
    -- F is continuous on the ball
    (hF_cont : ContinuousOn F (Metric.ball (fun i => (x₀ i : ℂ)) r))
    -- F is holomorphic away from the real slice
    (hF_holo_off : DifferentiableOn ℂ F
      (Metric.ball (fun i => (x₀ i : ℂ)) r \
       { z : Fin m → ℂ | ∀ i : Fin m, (z i).im = 0 })) :
    -- Conclusion: F is holomorphic on the ball
    DifferentiableOn ℂ F (Metric.ball (fun i => (x₀ i : ℂ)) r) :=
  holomorphic_extension_across_real Metric.isOpen_ball F hF_cont hF_holo_off

end
