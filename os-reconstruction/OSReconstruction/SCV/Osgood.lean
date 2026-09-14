/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral






















noncomputable section

open Complex Filter Topology Set MeasureTheory intervalIntegral
open scoped Interval

namespace SCV

set_option linter.unusedSectionVars false

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]



/-- The z-derivative of f(z,x) at z₀ varies continuously in x (F-valued output).

    Proof: By Cauchy integral formula,
      deriv(z ↦ f(z,x))(z₀) = (2πI)⁻¹ ∮ f(ζ,x)/(ζ-z₀)² dζ
    The integrand is continuous in x (from joint continuity of f) and uniformly
    bounded on the circle, so the integral is continuous in x. -/
lemma continuousAt_deriv_of_continuousOn [CompleteSpace E] [CompleteSpace F]
    {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    {V : Set E} (hV : IsOpen V)
    (f : ℂ × E → F)
    (hf_cont : ContinuousOn f (Metric.closedBall z₀ ρ ×ˢ V))
    (hf_z : ∀ x ∈ V, DifferentiableOn ℂ (fun z => f (z, x)) (Metric.closedBall z₀ ρ))
    {x₀ : E} (hx₀ : x₀ ∈ V) :
    ContinuousAt (fun x => deriv (fun z => f (z, x)) z₀) x₀ := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  set ρ' := ρ / 2 with hρ'_def
  have hρ' : 0 < ρ' := by positivity
  have hρ'_lt : ρ' < ρ := by linarith
  have h_sphere_sub : Metric.sphere z₀ ρ' ⊆ Metric.closedBall z₀ ρ :=
    Metric.sphere_subset_closedBall.trans (Metric.closedBall_subset_closedBall hρ'_lt.le)
  have h_cderiv : ∀ x ∈ V,
      Complex.cderiv ρ' (fun z => f (z, x)) z₀ = deriv (fun z => f (z, x)) z₀ := by
    intro x hx
    exact Complex.cderiv_eq_deriv Metric.isOpen_ball
      ((hf_z x hx).mono Metric.ball_subset_closedBall) hρ'
      (Metric.closedBall_subset_ball hρ'_lt)
  have h_cont_sp : ∀ x ∈ V,
      ContinuousOn (fun z => f (z, x)) (Metric.sphere z₀ ρ') := by
    intro x hx; exact ((hf_z x hx).continuousOn).mono h_sphere_sub
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
        (f (w, x) - f (wᵢ, x₀)) + (f (wᵢ, x₀) - f (w, x₀)) := by abel
    rw [this]
    calc ‖(f (w, x) - f (wᵢ, x₀)) + (f (wᵢ, x₀) - f (w, x₀))‖
        ≤ ‖f (w, x) - f (wᵢ, x₀)‖ + ‖f (wᵢ, x₀) - f (w, x₀)‖ := norm_add_le _ _
      _ < ε * ρ' / 2 + ε * ρ' / 2 := add_lt_add h1 (by rwa [norm_sub_rev])
      _ = ε * ρ' := by ring
  refine ⟨min δ₁ δ_V, lt_min hδ₁ hδ_V, fun x hx => ?_⟩
  rw [dist_eq_norm] at hx
  have hx_V : x ∈ V := hball_V (show dist x x₀ < δ_V by
    rw [dist_eq_norm]; exact lt_of_lt_of_le hx (min_le_right _ _))
  have hxδ₁ : ‖x - x₀‖ < δ₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have h_sphere : ∀ w ∈ Metric.sphere z₀ ρ',
      ‖(fun z => f (z, x)) w - (fun z => f (z, x₀)) w‖ < ε * ρ' :=
    fun w hw => h_unif w (h_sphere_sub hw) x hx_V hxδ₁
  have h_bound := Complex.norm_cderiv_sub_lt hρ' h_sphere (h_cont_sp x hx_V) (h_cont_sp x₀ hx₀)
  rw [dist_eq_norm, ← h_cderiv x hx_V, ← h_cderiv x₀ hx₀]
  calc ‖Complex.cderiv ρ' (fun z => f (z, x)) z₀ -
        Complex.cderiv ρ' (fun z => f (z, x₀)) z₀‖
      < ε * ρ' / ρ' := h_bound
    _ = ε := mul_div_cancel_right₀ ε (ne_of_gt hρ')



set_option maxHeartbeats 400000 in
/-- Cauchy power series p(1) applied to h equals h • deriv g z₀ (F-valued). -/
private lemma cauchyPowerSeries_one_eq_smul_deriv [CompleteSpace F]
    (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (g : ℂ → F) (hg : DifferentiableOn ℂ g (Metric.closedBall z₀ ρ)) (h : ℂ) :
    (cauchyPowerSeries g z₀ ρ 1) (fun _ => h) = h • deriv g z₀ := by
  set R : NNReal := ⟨ρ, hρ.le⟩
  have hR : (0 : NNReal) < R := by exact_mod_cast hρ
  have hps := hg.hasFPowerSeriesOnBall hR
  set p := cauchyPowerSeries g z₀ ρ
  have hd : deriv g z₀ = (p 1) (fun _ => 1) := hps.hasFPowerSeriesAt.deriv
  have h_smul : (p 1) (fun _ => h) = h • (p 1) (fun _ => 1) := by
    conv_lhs => rw [show (fun _ : Fin 1 => h) = (fun i => h • (fun _ : Fin 1 => (1:ℂ)) i) from
      by ext; simp]
    rw [(p 1).map_smul_univ (fun _ => h) (fun _ => 1)]
    simp [Finset.prod_const, pow_one]
  rw [h_smul, hd]

/-- Geometric tail bound ∑_{n≥0} M·r^(n+2) ≤ 2M·r² for r < 1/2. -/
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
/-- Cauchy coefficient bound ‖p(n)(fun _ => h)‖ ≤ M * (‖h‖/ρ)^n (F-valued). -/
private lemma cauchyPowerSeries_coeff_bound [CompleteSpace F]
    (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (g : ℂ → F) (hg : DifferentiableOn ℂ g (Metric.closedBall z₀ ρ))
    (M : ℝ) (hM : ∀ w ∈ Metric.closedBall z₀ ρ, ‖g w‖ ≤ M) (n : ℕ) (h : ℂ) :
    ‖(cauchyPowerSeries g z₀ ρ n) (fun _ => h)‖ ≤ M * (‖h‖ / ρ) ^ n := by
  set p := cauchyPowerSeries g z₀ ρ
  have h1 : ‖(p n) (fun _ => h)‖ ≤ ‖p n‖ * ‖h‖ ^ n := by
    have := (p n).le_opNorm (fun _ => h)
    simp only [Finset.prod_const, Finset.card_fin] at this
    exact this
  have h2 := norm_cauchyPowerSeries_le g z₀ ρ n
  set A := (2 * Real.pi)⁻¹ * ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, ‖g (circleMap z₀ ρ θ)‖ with hA_def
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
/-- Taylor remainder equals power series tail (F-valued). -/
private lemma taylor_remainder_eq_tsum [CompleteSpace F]
    (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (g : ℂ → F) (hg : DifferentiableOn ℂ g (Metric.closedBall z₀ ρ))
    (h : ℂ) (hh : ‖h‖ < ρ) :
    g (z₀ + h) - g z₀ - h • deriv g z₀ =
      ∑' n, (cauchyPowerSeries g z₀ ρ (n + 2)) (fun _ => h) := by
  set R : NNReal := ⟨ρ, hρ.le⟩
  have hR : (0 : NNReal) < R := by exact_mod_cast hρ
  have hps := hg.hasFPowerSeriesOnBall hR
  have hh_mem : h ∈ Metric.eball (0 : ℂ) R := by
    simp only [Metric.mem_eball, edist_eq_enorm_sub, sub_zero]
    exact_mod_cast hh
  have h_hassum : HasSum (fun n => (cauchyPowerSeries g z₀ ρ n) (fun _ => h))
      (g (z₀ + h)) := hps.hasSum hh_mem
  have h_tail := (hasSum_nat_add_iff' (f := fun n =>
      (cauchyPowerSeries g z₀ ρ n) (fun _ => h)) 2).mpr h_hassum
  have h_range : ∑ i ∈ Finset.range 2,
      (cauchyPowerSeries g z₀ ρ i) (fun _ => h) =
    (cauchyPowerSeries g z₀ ρ 0) (fun _ : Fin 0 => h) +
    (cauchyPowerSeries g z₀ ρ 1) (fun _ => h) := by
    simp [Finset.sum_range_succ]
  have hf0 : (cauchyPowerSeries g z₀ ρ 0) (fun _ : Fin 0 => h) = g z₀ :=
    hps.coeff_zero _
  have hf1 := cauchyPowerSeries_one_eq_smul_deriv z₀ ρ hρ g hg h
  rw [show g (z₀ + h) - g z₀ - h • deriv g z₀ =
    g (z₀ + h) - (∑ i ∈ Finset.range 2, (cauchyPowerSeries g z₀ ρ i) (fun _ => h))
    from by rw [h_range, hf0, hf1]; abel]
  exact h_tail.tsum_eq.symm

set_option maxHeartbeats 800000 in
/-- Norm of tail tsum bounded by geometric series (F-valued). -/
private lemma taylor_tail_norm_le [CompleteSpace F]
    (z₀ : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (g : ℂ → F) (hg : DifferentiableOn ℂ g (Metric.closedBall z₀ ρ))
    (M : ℝ) (hM : ∀ w ∈ Metric.closedBall z₀ ρ, ‖g w‖ ≤ M)
    (h : ℂ) (hh : ‖h‖ < ρ / 2) :
    ‖∑' n, (cauchyPowerSeries g z₀ ρ (n + 2)) (fun _ => h)‖ ≤
      4 * M / ρ ^ 2 * ‖h‖ ^ 2 := by
  have hh_lt_ρ : ‖h‖ < ρ := by linarith
  have hM_nn : 0 ≤ M := le_trans (norm_nonneg _) (hM z₀ (Metric.mem_closedBall_self hρ.le))
  set r := ‖h‖ / ρ with hr_def
  have hr_nn : 0 ≤ r := div_nonneg (norm_nonneg _) hρ.le
  have hr_half : r < 1 / 2 := by
    rw [hr_def, div_lt_div_iff₀ hρ (by norm_num : (0:ℝ) < 2)]; linarith
  have h_coeff : ∀ n, ‖(cauchyPowerSeries g z₀ ρ (n + 2)) (fun _ => h)‖ ≤ M * r ^ (n + 2) :=
    fun n => cauchyPowerSeries_coeff_bound z₀ ρ hρ g hg M hM (n + 2) h
  have h_geom_sum : Summable (fun n => M * r ^ (n + 2)) := by
    have : Summable (fun n => M * r ^ 2 * r ^ n) :=
      (summable_geometric_of_lt_one hr_nn (by linarith)).mul_left (M * r ^ 2)
    convert this using 1; ext n; ring
  -- Norm summability via comparison with geometric series (avoids FiniteDimensional)
  have h_norm_sum : Summable (fun n => ‖(cauchyPowerSeries g z₀ ρ (n + 2)) (fun _ => h)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) h_coeff h_geom_sum
  have h1 := norm_tsum_le_tsum_norm h_norm_sum
  have h2 : ∑' n, ‖(cauchyPowerSeries g z₀ ρ (n + 2)) (fun _ => h)‖ ≤
      ∑' n, M * r ^ (n + 2) :=
    h_norm_sum.tsum_le_tsum h_coeff h_geom_sum
  have h3 := tsum_geometric_tail_le M r hM_nn hr_nn hr_half
  have h4 : 2 * M * r ^ 2 ≤ 4 * M / ρ ^ 2 * ‖h‖ ^ 2 := by
    rw [hr_def, div_pow]
    have hρ2 : (ρ : ℝ) ^ 2 ≠ 0 := by positivity
    field_simp
    nlinarith [sq_nonneg ‖h‖]
  linarith

/-- Taylor remainder bound: ‖g(z₀+h) - g(z₀) - h • g'(z₀)‖ ≤ 4M/ρ² · ‖h‖² (F-valued). -/
private lemma taylor_remainder_single [CompleteSpace F]
    {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    {g : ℂ → F} (hg : DifferentiableOn ℂ g (Metric.closedBall z₀ ρ))
    {M : ℝ} (hM : ∀ w ∈ Metric.closedBall z₀ ρ, ‖g w‖ ≤ M)
    {h : ℂ} (hh : ‖h‖ < ρ / 2) :
    ‖g (z₀ + h) - g z₀ - h • deriv g z₀‖ ≤ 4 * M / ρ ^ 2 * ‖h‖ ^ 2 := by
  rw [taylor_remainder_eq_tsum z₀ ρ hρ g hg h (by linarith)]
  exact taylor_tail_norm_le z₀ ρ hρ g hg M hM h hh



/-- ContinuousOn f on K ×ˢ V with K compact gives uniform bound near x₀ (F-valued). -/
private lemma uniform_bound_near_point [CompleteSpace E] [CompleteSpace F]
    {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    {V : Set E} (_hV : IsOpen V)
    (f : ℂ × E → F)
    (hf_cont : ContinuousOn f (Metric.closedBall z₀ ρ ×ˢ V))
    {x₀ : E} (hx₀ : x₀ ∈ V) :
    ∃ (M : ℝ) (δ : ℝ), 0 ≤ M ∧ 0 < δ ∧
      ∀ w ∈ Metric.closedBall z₀ ρ, ∀ x ∈ V, ‖x - x₀‖ < δ → ‖f (w, x)‖ ≤ M := by
  have hK₀ : IsCompact (Metric.closedBall z₀ ρ ×ˢ ({x₀} : Set E)) :=
    (isCompact_closedBall z₀ ρ).prod isCompact_singleton
  have hK₀_sub : Metric.closedBall z₀ ρ ×ˢ ({x₀} : Set E) ⊆ Metric.closedBall z₀ ρ ×ˢ V :=
    Set.prod_mono le_rfl (Set.singleton_subset_iff.mpr hx₀)
  obtain ⟨M₀, hM₀⟩ := hK₀.exists_bound_of_continuousOn (hf_cont.mono hK₀_sub)
  set M := |M₀| + 1 with hM_def
  have hM₀_lt_M : ∀ w ∈ Metric.closedBall z₀ ρ, ‖f (w, x₀)‖ < M := by
    intro w hw
    have := hM₀ (w, x₀) ⟨hw, Set.mem_singleton x₀⟩
    calc ‖f (w, x₀)‖ ≤ M₀ := this
      _ ≤ |M₀| := le_abs_self M₀
      _ < |M₀| + 1 := lt_add_one _
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
  have h_choice : ∀ w, ∃ ε > 0, w ∈ Metric.closedBall z₀ ρ →
      ∀ w' x', ‖w' - w‖ < ε → ‖x' - x₀‖ < ε → x' ∈ V →
        w' ∈ Metric.closedBall z₀ ρ → ‖f (w', x')‖ < M := by
    intro w
    by_cases hw : w ∈ Metric.closedBall z₀ ρ
    · obtain ⟨ε, hε, hb⟩ := h_nhds w hw
      exact ⟨ε, hε, fun _ => hb⟩
    · exact ⟨1, one_pos, fun h => absurd h hw⟩
  choose ε hε h_bound_ε using h_choice
  have hK : IsCompact (Metric.closedBall z₀ ρ) := isCompact_closedBall z₀ ρ
  have h_cover_nhds : ∀ w ∈ Metric.closedBall z₀ ρ,
      Metric.ball w (ε w) ∈ nhds w :=
    fun w _ => Metric.ball_mem_nhds w (hε w)
  obtain ⟨t, ht_sub, ht_cover⟩ := hK.elim_nhds_subcover (fun w => Metric.ball w (ε w)) h_cover_nhds
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
  have hw_cover := ht_cover hw
  simp only [Set.mem_iUnion] at hw_cover
  obtain ⟨wᵢ, hwᵢ_mem, hw_in_ball⟩ := hw_cover
  rw [Metric.mem_ball, dist_eq_norm] at hw_in_ball
  have hδ₁_le : δ₁ ≤ ε wᵢ := Finset.inf'_le _ hwᵢ_mem
  have hwᵢ_in : wᵢ ∈ Metric.closedBall z₀ ρ := ht_sub wᵢ hwᵢ_mem
  have := h_bound_ε wᵢ hwᵢ_in w x hw_in_ball (lt_of_lt_of_le hxδ hδ₁_le) hxV hw
  linarith

/-- Uniform Taylor remainder bound for a family of holomorphic functions (F-valued). -/
lemma taylor_remainder_bound [CompleteSpace E] [CompleteSpace F]
    {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    {V : Set E} (hV : IsOpen V)
    (f : ℂ × E → F)
    (hf_cont : ContinuousOn f (Metric.closedBall z₀ ρ ×ˢ V))
    (hf_z : ∀ x ∈ V, DifferentiableOn ℂ (fun z => f (z, x)) (Metric.closedBall z₀ ρ))
    {x₀ : E} (hx₀ : x₀ ∈ V) :
    ∃ (C : ℝ) (δ : ℝ), C ≥ 0 ∧ δ > 0 ∧
      ∀ (h : ℂ) (x : E), x ∈ V → ‖x - x₀‖ < δ → ‖h‖ < ρ / 2 →
      ‖f (z₀ + h, x) - f (z₀, x) - h • deriv (fun z => f (z, x)) z₀‖ ≤ C * ‖h‖ ^ 2 := by
  obtain ⟨M, δ, hM_nn, hδ_pos, h_bound⟩ :=
    uniform_bound_near_point hρ hV f hf_cont hx₀
  exact ⟨4 * M / ρ ^ 2, δ, by positivity, hδ_pos, fun h x hxV hxδ hh =>
    taylor_remainder_single hρ (hf_z x hxV) (h_bound · · x hxV hxδ) hh⟩



/-- **Osgood's Lemma (product form, F-valued)**: A continuous function f : ℂ × E → F on
    an open product U₁ × U₂ that is holomorphic in each factor separately is jointly
    holomorphic.

    The proof constructs the joint Fréchet derivative L(h,k) = h • a + B(k) where
    a = ∂f/∂z(z₀,x₀) ∈ F and B = D_x f(z₀,x₀) : E →L[ℂ] F, then shows the remainder
    is o(‖(h,k)‖) using three estimates:
    1. Taylor remainder in z: O(|h|²) uniformly in x (Cauchy estimates)
    2. Derivative variation: h • [a(x₀+k) - a(x₀)] → 0 (continuity of z-derivative)
    3. Fréchet remainder in x: o(‖k‖) (from x-holomorphicity) -/
theorem osgood_lemma_prod [CompleteSpace E] [CompleteSpace F]
    {U₁ : Set ℂ} {U₂ : Set E} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    (f : ℂ × E → F)
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
  -- Step 3: Candidate Fréchet derivative L(h,k) = h • a + B(k)
  set a_of : E → F := fun x => deriv (fun z => f (z, x)) z₀
  set B : E →L[ℂ] F := fderiv ℂ (fun x => f (z₀, x)) x₀
  set L : ℂ × E →L[ℂ] F :=
    ContinuousLinearMap.coprod ((ContinuousLinearMap.id ℂ ℂ).smulRight (a_of x₀)) B
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
  set T₁ := f (z₀ + p.1, x₀ + p.2) - f (z₀, x₀ + p.2) - p.1 • a_of (x₀ + p.2)
  set T₂ := p.1 • (a_of (x₀ + p.2) - a_of x₀)
  set T₃ := f (z₀, x₀ + p.2) - f (z₀, x₀) - B p.2
  -- Show the remainder equals T₁ + T₂ + T₃
  have h_decomp : f ((z₀, x₀) + p) - f (z₀, x₀) - L p = T₁ + T₂ + T₃ := by
    have hLp : L p = p.1 • a_of x₀ + B p.2 := by
      simp [L, ContinuousLinearMap.coprod_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.id_apply]
    have hfp : f ((z₀, x₀) + p) = f (z₀ + p.1, x₀ + p.2) := rfl
    rw [hfp, hLp]; simp only [T₁, T₂, T₃, smul_sub]; abel
  rw [h_decomp]
  -- Step 7: Bound each term by (c/3) * ‖p‖
  -- T₁ bound: Taylor remainder ≤ C_t * ‖p.1‖² ≤ (c/3) * ‖p‖
  have hT₁ : ‖T₁‖ ≤ c / 3 * ‖p‖ := by
    have h_tay := h_taylor p.1 (x₀ + p.2) hx_mem
      (show ‖x₀ + p.2 - x₀‖ < δ_t by simp [add_sub_cancel_left]; exact lt_of_le_of_lt h_snd hp_δt)
      (show ‖p.1‖ < ρ / 2 from lt_of_le_of_lt h_fst hp_ρ)
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
    rw [dist_eq_norm] at h_an
    calc ‖T₂‖ = ‖p.1 • (a_of (x₀ + p.2) - a_of x₀)‖ := rfl
      _ = ‖p.1‖ * ‖a_of (x₀ + p.2) - a_of x₀‖ := norm_smul _ _
      _ ≤ ‖p‖ * ‖a_of (x₀ + p.2) - a_of x₀‖ := by
          nlinarith [norm_nonneg (a_of (x₀ + p.2) - a_of x₀)]
      _ ≤ c / 3 * ‖p‖ := by nlinarith [norm_nonneg p]
  -- T₃ bound: Fréchet remainder ≤ (c/3) * ‖p‖
  have hT₃ : ‖T₃‖ ≤ c / 3 * ‖p‖ := by
    have h_xb := h_x_bound (show dist p.2 0 < δ₃ by
      simp [dist_zero_right]; exact lt_of_le_of_lt h_snd hp_δ₃)
    calc ‖T₃‖ ≤ c / 3 * ‖p.2‖ := h_xb
      _ ≤ c / 3 * ‖p‖ := by nlinarith [norm_nonneg p.2, norm_nonneg p]
  -- Step 8: Combine via triangle inequality
  calc ‖T₁ + T₂ + T₃‖ ≤ ‖T₁ + T₂‖ + ‖T₃‖ := norm_add_le _ _
    _ ≤ (‖T₁‖ + ‖T₂‖) + ‖T₃‖ := by linarith [norm_add_le T₁ T₂]
    _ ≤ c / 3 * ‖p‖ + c / 3 * ‖p‖ + c / 3 * ‖p‖ := by linarith
    _ = c * ‖p‖ := by ring



/-- **Osgood's Lemma (Fin m → ℂ version, F-valued)**: A continuous function on an open
    subset of ℂᵐ that is holomorphic in each coordinate separately (with the
    others fixed) is jointly holomorphic. -/
theorem osgood_lemma [CompleteSpace F]
    {m : ℕ} {U' : Set (Fin m → ℂ)} (hU' : IsOpen U')
    (f' : (Fin m → ℂ) → F)
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
    set g : ℂ × (Fin n → ℂ) → F := fun p => f' (cons' p.1 p.2) with hg_def
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

end SCV
