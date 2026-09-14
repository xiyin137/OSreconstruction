import OSReconstruction.GeneralResults.SchwartzFlatness
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Uniform weighted flatness

Taylor flatness estimates with constants independent of the closed flatness set.
Polynomial weights yield uniform rapid decay and an integrable majorant for
kernels whose singularities are controlled by a power of distance to that set.
The finite nested-product domain includes arbitrary n-point spacetime domains,
including empty coordinate index types.
-/

noncomputable section

namespace OSReconstruction.SchwartzFlatness

/-- The weighted flatness constant is chosen before the closed set. -/
theorem schwartz_weight_mul_norm_le_infDist_pow_uniform
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : SchwartzMap E F) (w : E → ℝ) (hw : w.HasTemperateGrowth) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : Set E, IsClosed S → S.Nonempty →
      (∀ k : ℕ, ∀ y ∈ S, iteratedFDeriv ℝ k (f : E → F) y = 0) →
      ∀ x : E, ‖w x‖ * ‖f x‖ ≤ C * Metric.infDist x S ^ (m + 1) := by
  let g : SchwartzMap E F := SchwartzMap.smulLeftCLM F w f
  have hg : (g : E → F) = fun x => w x • f x :=
    SchwartzMap.smulLeftCLM_apply hw f
  let A := SchwartzMap.seminorm ℝ 0 (m + 1) g
  refine ⟨A / (Nat.factorial m : ℝ), by positivity, ?_⟩
  intro S hSc hSn hflat x
  have hgflat : ∀ k : ℕ, ∀ y ∈ S,
      iteratedFDeriv ℝ k (g : E → F) y = 0 := by
    intro k y hy
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    rw [hg]
    have h := norm_iteratedFDeriv_smul_le hw.1 (f.smooth (⊤ : ℕ∞)) y
      (show (k : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) by exact_mod_cast le_top)
    simpa only [hflat _ y hy, norm_zero, mul_zero, Finset.sum_const_zero] using h
  have h := norm_le_infDist_pow_of_flat_on_closed hSc hSn
    (g.smooth (⊤ : ℕ∞)) hgflat m (show 0 ≤ A by positivity)
    (fun y => SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ g (m + 1) y) x
  simpa only [hg, norm_smul] using h

/-- Rapid Schwartz decay and arbitrary-order flatness hold simultaneously,
with a constant independent of the closed flatness set. -/
theorem schwartz_one_add_norm_pow_mul_norm_le_infDist_pow_uniform_pi
    {ι κ F : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : SchwartzMap (ι → κ → ℝ) F) (N m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : Set (ι → κ → ℝ), IsClosed S → S.Nonempty →
      (∀ k : ℕ, ∀ y ∈ S, iteratedFDeriv ℝ k (f : (ι → κ → ℝ) → F) y = 0) →
      ∀ x, (1 + ‖x‖) ^ N * ‖f x‖ ≤ C * Metric.infDist x S ^ (m + 1) := by
  classical
  let w : (ι → κ → ℝ) → ℝ := fun x => (2 * (1 + ∑ i, ∑ j, (x i j) ^ 2)) ^ N
  have hw : w.HasTemperateGrowth := by
    have hcoord (i : ι) (j : κ) :
        (fun x : ι → κ → ℝ => x i j).HasTemperateGrowth :=
      ((ContinuousLinearMap.proj j : (κ → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.proj i : (ι → κ → ℝ) →L[ℝ] (κ → ℝ))).hasTemperateGrowth
    exact ((Function.HasTemperateGrowth.const 2).mul
      ((Function.HasTemperateGrowth.const 1).add
        (Function.HasTemperateGrowth.sum fun i _ =>
          Function.HasTemperateGrowth.sum fun j _ => (hcoord i j).pow 2))).pow N
  obtain ⟨C, hC, hbound⟩ := schwartz_weight_mul_norm_le_infDist_pow_uniform f w hw m
  refine ⟨C, hC, fun S hSc hSn hflat x => le_trans ?_ (hbound S hSc hSn hflat x)⟩
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have hsum : 0 ≤ ∑ i, ∑ j, (x i j) ^ 2 := by positivity
  have hnorm : ‖x‖ ≤ 1 + ∑ i, ∑ j, (x i j) ^ 2 := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro j
    have hcoord : (x i j) ^ 2 ≤ ∑ i, ∑ j, (x i j) ^ 2 := by
      exact le_trans (Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ j))
        (Finset.single_le_sum (f := fun i => ∑ j, (x i j) ^ 2)
          (fun _ _ => by positivity) (Finset.mem_univ i))
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (|x i j| - 1), sq_abs (x i j)]
  have hweight : 1 + ‖x‖ ≤ 2 * (1 + ∑ i, ∑ j, (x i j) ^ 2) := by linarith
  have hw_nonneg : 0 ≤ w x := by dsimp [w]; positivity
  rw [Real.norm_of_nonneg hw_nonneg]
  exact pow_le_pow_left₀ (by positivity) hweight N

/-- Flatness cancels a distance-weighted polynomial kernel bound, uniformly in
the closed set. The scalar `b` can be the norm of a kernel at `x`. -/
theorem schwartz_polynomial_kernel_bound_uniform_pi
    {ι κ F : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : SchwartzMap (ι → κ → ℝ) F) (N m q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : Set (ι → κ → ℝ), IsClosed S → S.Nonempty →
      (∀ k : ℕ, ∀ y ∈ S, iteratedFDeriv ℝ k (f : (ι → κ → ℝ) → F) y = 0) →
      ∀ x (b A : ℝ), 0 ≤ b →
        b * Metric.infDist x S ^ (m + 1) ≤ A * (1 + ‖x‖) ^ q →
        (1 + ‖x‖) ^ N * (b * ‖f x‖) ≤ A * C := by
  obtain ⟨C, hC, hbound⟩ :=
    schwartz_one_add_norm_pow_mul_norm_le_infDist_pow_uniform_pi f (N + q) m
  refine ⟨C, hC, ?_⟩
  intro S hSc hSn hflat x b A hb hgrowth
  have h : (1 + ‖x‖) ^ q * ((1 + ‖x‖) ^ N * (b * ‖f x‖)) ≤
      (1 + ‖x‖) ^ q * (A * C) := calc
    _ = b * ((1 + ‖x‖) ^ (N + q) * ‖f x‖) := by rw [pow_add]; ring
    _ ≤ b * (C * Metric.infDist x S ^ (m + 1)) :=
      mul_le_mul_of_nonneg_left (hbound S hSc hSn hflat x) hb
    _ = C * (b * Metric.infDist x S ^ (m + 1)) := by ring
    _ ≤ C * (A * (1 + ‖x‖) ^ q) := mul_le_mul_of_nonneg_left hgrowth hC
    _ = _ := by ring
  exact (mul_le_mul_iff_right₀ (pow_pos (by positivity : 0 < 1 + ‖x‖) q)).mp h

set_option synthInstance.maxSize 256 in
/-- One integrable envelope works for every closed flatness set and every
pointwise kernel bound with the prescribed exponents. -/
theorem schwartz_polynomial_kernel_integrable_majorant_uniform_pi
    {ι κ F : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : SchwartzMap (ι → κ → ℝ) F) (m q : ℕ) :
    ∃ B : (ι → κ → ℝ) → ℝ, MeasureTheory.Integrable B ∧ (∀ x, 0 ≤ B x) ∧
      ∀ S : Set (ι → κ → ℝ), IsClosed S → S.Nonempty →
        (∀ k : ℕ, ∀ y ∈ S, iteratedFDeriv ℝ k (f : (ι → κ → ℝ) → F) y = 0) →
        ∀ x (b A : ℝ), 0 ≤ b →
          b * Metric.infDist x S ^ (m + 1) ≤ A * (1 + ‖x‖) ^ q →
          b * ‖f x‖ ≤ A * B x := by
  classical
  let μ := (MeasureTheory.volume : MeasureTheory.Measure (ι → κ → ℝ))
  haveI : μ.HasTemperateGrowth := by dsimp [μ]; infer_instance
  let N := μ.integrablePower
  obtain ⟨C, hC, hbound⟩ := schwartz_polynomial_kernel_bound_uniform_pi f N m q
  refine ⟨fun x => C * (1 + ‖x‖) ^ (-(N : ℝ)),
    (μ.integrable_pow_neg_integrablePower).const_mul C, fun x => by positivity, ?_⟩
  intro S hSc hSn hflat x b A hb hgrowth
  have h := hbound S hSc hSn hflat x b A hb hgrowth
  have hx : 0 < (1 + ‖x‖) ^ N := pow_pos (by positivity) N
  have hdiv : b * ‖f x‖ ≤ (A * C) / (1 + ‖x‖) ^ N :=
    (le_div_iff₀ hx).2 (by simpa [mul_comm] using h)
  simpa only [Real.rpow_neg (by positivity : 0 ≤ 1 + ‖x‖), Real.rpow_natCast,
    div_eq_mul_inv, mul_assoc] using hdiv

end OSReconstruction.SchwartzFlatness
