/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.Prod
import OSReconstruction.SCV.Polydisc
import OSReconstruction.SCV.Osgood

/-!
# Iterated Circle Integrals

This file defines the iterated circle integral for several complex variables:
```
  ∮_{|w₁-c₁|=r₁} ⋯ ∮_{|wₘ-cₘ|=rₘ} f(w₁,...,wₘ) dwₘ⋯dw₁
```

The integral is defined recursively: the base case (m=0) is evaluation, and
the recursive case integrates over the last circle with the inner iterated integral.

## Main definitions

* `iteratedCircleIntegral` — the iterated circle integral over m circles
* `cauchyKernelPolydisc` — the Cauchy kernel `∏ᵢ (wᵢ - zᵢ)⁻¹`
* `cauchyIntegralPolydisc` — `(2πi)⁻ᵐ ∮...∮ f(w)/∏(wᵢ-zᵢ) dw`

## Main results

* `norm_iteratedCircleIntegral_le` — norm bound: `‖∮...∮ f‖ ≤ (2π)ᵐ · ∏ rᵢ · sup ‖f‖`
* `iteratedCircleIntegral_eq_zero` — vanishing when m ≥ 1 and integrand is zero

## References

* Krantz, S.G. (2001). *Function Theory of Several Complex Variables*. AMS, Ch. 1.
* Rudin, W. (1980). *Function Theory in the Unit Ball of ℂⁿ*. Springer.
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set SCV

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

namespace SCV

/-! ### Iterated Circle Integral

We define the iterated circle integral recursively on the number of variables `m`.
For `m = 0`, it evaluates the function at the (unique) point in `Fin 0 → ℂ`.
For `m + 1`, it integrates the last variable around the circle `C(c(last m), r(last m))`
with the remaining variables handled by the recursive call.
-/

/-- The iterated circle integral over `m` circles.
    `iteratedCircleIntegral m f c r` computes
    `∮_{|w₁-c₁|=r₁} ⋯ ∮_{|wₘ-cₘ|=rₘ} f(w₁,...,wₘ) dwₘ⋯dw₁`. -/
def iteratedCircleIntegral :
    (m : ℕ) → ((Fin m → ℂ) → E) → (Fin m → ℂ) → (Fin m → ℝ) → E
  | 0, f, _, _ => f Fin.elim0
  | m + 1, f, c, r =>
      iteratedCircleIntegral m
        (fun z => ∮ w in C(c (Fin.last m), r (Fin.last m)), f (Fin.snoc z w))
        (c ∘ Fin.castSucc)
        (r ∘ Fin.castSucc)

omit [CompleteSpace E] in
/-- Unfolding lemma for the successor case of `iteratedCircleIntegral`. -/
theorem iteratedCircleIntegral_succ (m : ℕ) (f : (Fin (m + 1) → ℂ) → E)
    (c : Fin (m + 1) → ℂ) (r : Fin (m + 1) → ℝ) :
    iteratedCircleIntegral (m + 1) f c r =
    iteratedCircleIntegral m
      (fun z => ∮ w in C(c (Fin.last m), r (Fin.last m)), f (Fin.snoc z w))
      (c ∘ Fin.castSucc) (r ∘ Fin.castSucc) := rfl

omit [CompleteSpace E] in
/-- The iterated circle integral of zero is zero. -/
theorem iteratedCircleIntegral_zero (m : ℕ) (c : Fin m → ℂ) (r : Fin m → ℝ) :
    iteratedCircleIntegral m (fun _ => (0 : E)) c r = 0 := by
  induction m with
  | zero => simp [iteratedCircleIntegral]
  | succ m ih =>
    simp only [iteratedCircleIntegral]
    convert ih (c ∘ Fin.castSucc) (r ∘ Fin.castSucc) using 1
    congr 1
    ext z
    simp [circleIntegral, smul_zero, intervalIntegral.integral_zero]

omit [CompleteSpace E] in
/-- The iterated circle integral is linear (scalar multiplication). -/
theorem iteratedCircleIntegral_smul (m : ℕ) (a : ℂ) (f : (Fin m → ℂ) → E)
    (c : Fin m → ℂ) (r : Fin m → ℝ) :
    iteratedCircleIntegral m (fun z => a • f z) c r =
      a • iteratedCircleIntegral m f c r := by
  induction m with
  | zero => simp [iteratedCircleIntegral]
  | succ m ih =>
    simp only [iteratedCircleIntegral]
    rw [← ih]
    congr 1
    ext z
    rw [circleIntegral.integral_smul]

omit [CompleteSpace E] in
/-- The iterated circle integral depends only on the values of the integrand
    on the distinguished boundary. -/
theorem iteratedCircleIntegral_congr (m : ℕ) (f g : (Fin m → ℂ) → E)
    (c : Fin m → ℂ) (r : Fin m → ℝ) (hr : ∀ i, 0 ≤ r i)
    (h : ∀ w ∈ distinguishedBoundary c r, f w = g w) :
    iteratedCircleIntegral m f c r = iteratedCircleIntegral m g c r := by
  induction m with
  | zero =>
    simp only [iteratedCircleIntegral]
    exact h Fin.elim0 (fun i => i.elim0)
  | succ m ih =>
    simp only [iteratedCircleIntegral]
    apply ih
    · intro i; exact hr (Fin.castSucc i)
    · intro z' hz'
      apply circleIntegral.integral_congr (hr (Fin.last m))
      intro t ht
      apply h (Fin.snoc z' t)
      intro i; refine Fin.lastCases ?_ ?_ i
      · simp only [Fin.snoc_last]; exact ht
      · intro j; simp only [Fin.snoc_castSucc]; exact hz' j

/-! ### Norm bounds -/

omit [CompleteSpace E] in
/-- Norm bound for the iterated circle integral.
    If `‖f(w)‖ ≤ C` for all `w` on the distinguished boundary, then
    `‖∮...∮ f‖ ≤ (2π)ᵐ · ∏ᵢ |rᵢ| · C`. -/
theorem norm_iteratedCircleIntegral_le (m : ℕ) (f : (Fin m → ℂ) → E)
    (c : Fin m → ℂ) (r : Fin m → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hr : ∀ i, 0 ≤ r i)
    (hf : ∀ w ∈ distinguishedBoundary c r, ‖f w‖ ≤ C) :
    ‖iteratedCircleIntegral m f c r‖ ≤
      (2 * Real.pi) ^ m * (∏ i : Fin m, |r i|) * C := by
  induction m generalizing C with
  | zero =>
    simp only [iteratedCircleIntegral, pow_zero, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    exact hf Fin.elim0 (fun i => i.elim0)
  | succ m ih =>
    simp only [iteratedCircleIntegral]
    set R := r (Fin.last m)
    set g := fun z => ∮ w in C(c (Fin.last m), R), f (Fin.snoc z w)
    set c' := c ∘ Fin.castSucc
    set r' := r ∘ Fin.castSucc
    have hr' : ∀ i, 0 ≤ r' i := fun i => hr (Fin.castSucc i)
    have hR : 0 ≤ R := hr (Fin.last m)
    -- Bound g on the inner distinguished boundary
    have hg : ∀ z ∈ distinguishedBoundary c' r',
        ‖g z‖ ≤ 2 * Real.pi * R * C := by
      intro z hz
      apply circleIntegral.norm_integral_le_of_norm_le_const hR
      intro w hw
      apply hf (Fin.snoc z w)
      intro i
      refine Fin.lastCases ?_ ?_ i
      · simp only [Fin.snoc_last]; exact hw
      · intro j; simp only [Fin.snoc_castSucc]; exact hz j
    have hC' : 0 ≤ 2 * Real.pi * R * C := by positivity
    calc ‖iteratedCircleIntegral m g c' r'‖
        ≤ (2 * Real.pi) ^ m * (∏ i : Fin m, |r' i|) *
          (2 * Real.pi * R * C) := ih g c' r' (2 * Real.pi * R * C) hC' hr' hg
      _ = (2 * Real.pi) ^ (m + 1) * (∏ i : Fin (m + 1), |r i|) * C := by
          rw [Fin.prod_univ_castSucc (fun i => |r i|)]
          simp only [r', R, Function.comp_apply, abs_of_nonneg hR]
          ring

/-! ### Cauchy kernel and Cauchy integral for polydiscs -/

/-- The Cauchy kernel for polydiscs: `∏ᵢ (wᵢ - zᵢ)⁻¹`. -/
def cauchyKernelPolydisc {m : ℕ} (z w : Fin m → ℂ) : ℂ :=
  ∏ i, (w i - z i)⁻¹

/-- The Cauchy integral for polydiscs:
    `(2πi)⁻ᵐ ∮_{|w₁-c₁|=r₁} ⋯ ∮_{|wₘ-cₘ|=rₘ} f(w)/∏(wᵢ-zᵢ) dw`. -/
def cauchyIntegralPolydisc {m : ℕ} (f : (Fin m → ℂ) → E)
    (c : Fin m → ℂ) (r : Fin m → ℝ) (z : Fin m → ℂ) : E :=
  (2 * Real.pi * I)⁻¹ ^ m •
    iteratedCircleIntegral m (fun w => cauchyKernelPolydisc z w • f w) c r

/-- The Cauchy kernel is nonzero when `z` is in the polydisc and `w` is on
    the distinguished boundary. -/
theorem cauchyKernelPolydisc_ne_zero {m : ℕ} {z w : Fin m → ℂ}
    {c : Fin m → ℂ} {r : Fin m → ℝ}
    (hz : z ∈ Polydisc c r)
    (hw : w ∈ distinguishedBoundary c r) :
    cauchyKernelPolydisc z w ≠ 0 := by
  -- The product ∏ᵢ (wᵢ - zᵢ)⁻¹ is nonzero because each factor is nonzero:
  -- wᵢ ∈ sphere(cᵢ, rᵢ) and zᵢ ∈ ball(cᵢ, rᵢ) implies wᵢ ≠ zᵢ.
  simp only [cauchyKernelPolydisc]
  rw [Finset.prod_ne_zero_iff]
  intro i _
  apply inv_ne_zero
  intro heq
  rw [sub_eq_zero] at heq
  have h_ball := Metric.mem_ball.mp (hz i)
  have h_sphere := Metric.mem_sphere.mp (hw i)
  rw [heq] at h_sphere
  linarith

/-- The Cauchy kernel factors when the argument is split via `Fin.snoc`:
    `∏ᵢ (snoc(w',t)ᵢ - zᵢ)⁻¹ = (∏ⱼ (w'ⱼ - z(castSucc j))⁻¹) · (t - z(last n))⁻¹`. -/
theorem cauchyKernelPolydisc_snoc {n : ℕ} (z : Fin (n+1) → ℂ)
    (w : Fin n → ℂ) (t : ℂ) :
    cauchyKernelPolydisc z (Fin.snoc w t) =
    cauchyKernelPolydisc (Fin.init z) w * (t - z (Fin.last n))⁻¹ := by
  simp only [cauchyKernelPolydisc, Fin.prod_univ_castSucc,
    Fin.snoc_castSucc, Fin.snoc_last, Fin.init]

/-! ### Cauchy integral formula for polydiscs -/

/-- **Cauchy integral formula for polydiscs.**
    If `f` is holomorphic on a closed polydisc and `z` is in the open polydisc, then
    `f(z) = (2πi)⁻ᵐ ∮...∮ f(w)/∏(wᵢ-zᵢ) dw`.

    The proof proceeds by induction on `m`. The base case uses the standard 1D Cauchy
    integral formula. The inductive step applies the 1D formula in the last variable,
    holding the other variables fixed, and uses Fubini to rearrange the integrals. -/
theorem cauchyIntegralPolydisc_eq {m : ℕ}
    (f : (Fin m → ℂ) → E) (c : Fin m → ℂ) (r : Fin m → ℝ)
    (hr : ∀ i, 0 < r i)
    (hf : ∀ w ∈ closedPolydisc c r,
      ∀ i, DifferentiableAt ℂ (fun t => f (Function.update w i t)) (w i))
    (hf_cont : ContinuousOn f (closedPolydisc c r))
    (z : Fin m → ℂ) (hz : z ∈ Polydisc c r) :
    cauchyIntegralPolydisc f c r z = f z := by
  induction m with
  | zero =>
    -- For m = 0, Fin 0 → ℂ has a unique element, so z = Fin.elim0
    simp only [cauchyIntegralPolydisc, iteratedCircleIntegral, pow_zero, one_smul,
      cauchyKernelPolydisc, Finset.univ_eq_empty, Finset.prod_empty, one_smul]
    exact congr_arg f (Subsingleton.elim _ _)
  | succ n ih =>
    -- Setup: key variables for the inductive step
    set z_n := z (Fin.last n) with hz_n_def
    set c' := c ∘ Fin.castSucc
    set r' := r ∘ Fin.castSucc
    set c_n := c (Fin.last n)
    set R := r (Fin.last n)
    -- g(w) = f(snoc w z_n): the function with last variable fixed at z_n
    set g : (Fin n → ℂ) → E := fun w => f (Fin.snoc w z_n)
    -- Hypotheses for the reduced problem
    have hr' : ∀ i, 0 < r' i := fun i => hr (Fin.castSucc i)
    have hz_init : Fin.init z ∈ Polydisc c' r' := fun i => hz (Fin.castSucc i)
    have hzn_ball : z_n ∈ Metric.ball c_n R := hz (Fin.last n)
    -- Helper: snoc w z_n lands in the closed polydisc when w is in the inner one
    have h_snoc_mem_of : ∀ w ∈ closedPolydisc c' r',
        Fin.snoc w z_n ∈ closedPolydisc c r := by
      intro w hw i; refine Fin.lastCases ?_ ?_ i
      · simp only [Fin.snoc_last]; exact Metric.ball_subset_closedBall hzn_ball
      · intro k; simp only [Fin.snoc_castSucc]; exact hw k
    -- Step 1: The main reduction using kernel splitting + 1D CIF + scalar algebra
    have h_twoπI_ne : (2 * (↑Real.pi : ℂ) * I) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
    -- On the distinguished boundary, the inner circle integral factors as (2πi) × reduced
    have h_circle_eq : ∀ z' ∈ distinguishedBoundary c' r',
        (∮ t in C(c (Fin.last n), r (Fin.last n)),
          cauchyKernelPolydisc z (Fin.snoc z' t) • f (Fin.snoc z' t)) =
        (2 * ↑Real.pi * I) •
          (cauchyKernelPolydisc (Fin.init z) z' •
            f (Fin.snoc z' (z (Fin.last n)))) := by
      intro z' hz'
      -- Factor the kernel: kernel(z, snoc z' t) = kernel(init z, z') * (t - z_n)⁻¹
      have h_factor : ∀ t,
          cauchyKernelPolydisc z (Fin.snoc z' t) • f (Fin.snoc z' t) =
          cauchyKernelPolydisc (Fin.init z) z' •
            ((t - z (Fin.last n))⁻¹ • f (Fin.snoc z' t)) := by
        intro t; rw [cauchyKernelPolydisc_snoc, mul_smul]
      simp_rw [h_factor]
      rw [circleIntegral.integral_smul, smul_comm]
      congr 1
      -- Apply 1D Cauchy integral formula
      apply DifferentiableOn.circleIntegral_sub_inv_smul
      · -- fun t => f(snoc z' t) is differentiable on closedBall c_n R
        intro t ht
        apply DifferentiableAt.differentiableWithinAt
        have hmem : Fin.snoc z' t ∈ closedPolydisc c r := by
          intro i; refine Fin.lastCases ?_ ?_ i
          · simp only [Fin.snoc_last]; exact ht
          · intro j; simp only [Fin.snoc_castSucc]
            exact distinguishedBoundary_subset_closedPolydisc hz' j
        have h_diff := hf (Fin.snoc z' t) hmem (Fin.last n)
        simp_rw [Fin.update_snoc_last] at h_diff
        simp only [Fin.snoc_last] at h_diff
        exact h_diff
      · exact hz (Fin.last n)
    -- Main reduction: use congr + linearity + scalar algebra
    have h_reduce : cauchyIntegralPolydisc f c r z =
        cauchyIntegralPolydisc g c' r' (Fin.init z) := by
      simp only [cauchyIntegralPolydisc, iteratedCircleIntegral]
      rw [iteratedCircleIntegral_congr n _ _
        (c ∘ Fin.castSucc) (r ∘ Fin.castSucc)
        (fun i => le_of_lt (hr (Fin.castSucc i))) h_circle_eq,
        iteratedCircleIntegral_smul,
        ← mul_smul, pow_succ, mul_assoc, inv_mul_cancel₀ h_twoπI_ne, mul_one]
    -- Step 2: g satisfies the hypotheses of the induction
    have hg_sep : ∀ w ∈ closedPolydisc c' r', ∀ j,
        DifferentiableAt ℂ (fun t => g (Function.update w j t)) (w j) := by
      intro w hw j
      -- g (update w j t) = f (snoc (update w j t) z_n) = f (update (snoc w z_n) (castSucc j) t)
      show DifferentiableAt ℂ (fun t => f (Fin.snoc (Function.update w j t) z_n)) (w j)
      simp_rw [Fin.snoc_update]
      have := hf (Fin.snoc w z_n) (h_snoc_mem_of w hw) (Fin.castSucc j)
      simp only [Fin.snoc_castSucc] at this
      exact this
    have hg_cont : ContinuousOn g (closedPolydisc c' r') := by
      -- g = f ∘ (fun w => snoc w z_n), composition of continuous maps
      have h_snoc_cont : Continuous
          (fun w : Fin n → ℂ => @Fin.snoc n (fun _ => ℂ) w z_n) := by
        apply continuous_pi; intro i; refine Fin.lastCases ?_ ?_ i
        · simp only [Fin.snoc_last]; exact continuous_const
        · intro j; simp only [Fin.snoc_castSucc]; exact continuous_apply j
      exact hf_cont.comp h_snoc_cont.continuousOn (fun w hw => h_snoc_mem_of w hw)
    -- Step 3: Apply IH and conclude
    rw [h_reduce, ih g c' r' hr' hg_sep hg_cont (Fin.init z) hz_init]
    -- g (init z) = f (snoc (init z) z_n) = f z
    show f (Fin.snoc (Fin.init z) z_n) = f z
    rw [hz_n_def, Fin.snoc_init_self]

/-! ### Infrastructure: Leibniz rule for circle integrals

The key technical tool needed for holomorphicity of the Cauchy integral is
the **Leibniz rule** (differentiation under the integral sign) for circle integrals.
If the integrand depends holomorphically on a complex parameter `t`, then the
circle integral is holomorphic in `t`. This is applied inductively to handle
iterated circle integrals.

**Formulation:** We use `DifferentiableOn ℂ ... S` (not `DifferentiableAt ... t₀`) because
the inductive step needs the inner circle integral to be holomorphic on all of `S`,
not just at a single point. The caller extracts `DifferentiableAt` via
`DifferentiableOn.differentiableAt`.

**Domain for continuity:** The continuity hypothesis uses `S ×ˢ distinguishedBoundary`
rather than `univ ×ˢ closedPolydisc`, because the Cauchy kernel `∏(wⱼ-zⱼ)⁻¹` has
singularities at `w = z` inside the closed polydisc but is smooth when `w` is restricted
to the distinguished boundary (where `|wⱼ - cⱼ| = rⱼ > |zⱼ - cⱼ|`).
-/

omit [CompleteSpace E] in
/-- **Leibniz rule for circle integrals with holomorphic parameter.**
    If `F(t, w)` depends holomorphically on `t ∈ S` for each `w` on the circle,
    and `(t, w) ↦ F(t, w)` is jointly continuous on `S × sphere`,
    then `t ↦ ∮ F(t, w) dw` is holomorphic on `S`.

    The proof unfolds the circle integral as an interval integral and applies
    `hasDerivAt_integral_of_dominated_loc_of_deriv_le` (Leibniz rule). The
    derivative bound comes from the Cauchy estimate; measurability of the
    derivative is established via `aestronglyMeasurable_of_tendsto_ae` applied
    to a difference-quotient sequence. -/
private theorem differentiableOn_circleIntegral_param
    {F : ℂ → ℂ → E} {c₀ : ℂ} {R : ℝ} {S : Set ℂ}
    (hR : 0 ≤ R) (hS_open : IsOpen S)
    (hF_diff : ∀ w ∈ Metric.sphere c₀ R, DifferentiableOn ℂ (F · w) S)
    (hF_cont : ContinuousOn (Function.uncurry F)
      (S ×ˢ Metric.sphere c₀ R)) :
    DifferentiableOn ℂ (fun t => ∮ w in C(c₀, R), F t w) S := by
  -- Case R = 0: circle integral is zero
  rcases eq_or_lt_of_le hR with rfl | hR_pos
  · simp only [circleIntegral.integral_radius_zero]; exact differentiableOn_const 0
  -- Case R > 0
  intro t₀ ht₀
  -- Find ε > 0 with closedBall(t₀, 2ε) ⊆ S
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.isOpen_iff.mp hS_open t₀ ht₀
  set ε := δ / 4 with hε_def
  have hε_pos : (0 : ℝ) < ε := by positivity
  have hcb_sub : Metric.closedBall t₀ (2 * ε) ⊆ S :=
    (Metric.closedBall_subset_ball (by linarith)).trans hδ_sub
  -- For t ∈ ball(t₀, ε), closedBall(t, ε) ⊆ closedBall(t₀, 2ε) ⊆ S
  have hcb_t : ∀ t ∈ Metric.ball t₀ ε, Metric.closedBall t ε ⊆ S := by
    intro t ht x hx; apply hcb_sub
    exact Metric.mem_closedBall.mpr (calc
      dist x t₀ ≤ dist x t + dist t t₀ := dist_triangle x t t₀
      _ ≤ ε + ε := add_le_add (Metric.mem_closedBall.mp hx) (le_of_lt (Metric.mem_ball.mp ht))
      _ = 2 * ε := by ring)
  -- F(·,w) is DiffContOnCl on ball(t, ε) for t near t₀ and w on sphere
  have h_dcoc : ∀ w ∈ Metric.sphere c₀ R, ∀ t ∈ Metric.ball t₀ ε,
      DiffContOnCl ℂ (F · w) (Metric.ball t ε) :=
    fun w hw t ht => ⟨(hF_diff w hw).mono (Metric.ball_subset_closedBall.trans (hcb_t t ht)),
      (hF_diff w hw).continuousOn.mono (Metric.closure_ball_subset_closedBall.trans (hcb_t t ht))⟩
  -- Uniform bound M on ‖F‖ over closedBall(t₀, 2ε) × sphere(c₀, R)
  obtain ⟨M, hM⟩ := ((isCompact_closedBall t₀ (2 * ε)).prod
    (isCompact_sphere c₀ R)).exists_bound_of_continuousOn
    (hF_cont.mono (Set.prod_mono hcb_sub Subset.rfl))
  -- Cauchy estimate: ‖deriv(F·w) t‖ ≤ M/ε for t ∈ ball(t₀, ε) and w on sphere
  have h_cauchy : ∀ w ∈ Metric.sphere c₀ R, ∀ t ∈ Metric.ball t₀ ε,
      ‖deriv (F · w) t‖ ≤ M / ε := by
    intro w hw t ht
    exact norm_deriv_le_of_forall_mem_sphere_norm_le hε_pos (h_dcoc w hw t ht) fun ζ hζ =>
      hM (ζ, w) ⟨Metric.mem_closedBall.mpr (calc
        dist ζ t₀ ≤ dist ζ t + dist t t₀ := dist_triangle ζ t t₀
        _ ≤ ε + ε := by linarith [Metric.mem_sphere.mp hζ, Metric.mem_ball.mp ht]
        _ = 2 * ε := by ring), hw⟩
  -- Abbreviations for the interval-integral representation
  set G : ℂ → ℝ → E := fun t θ => deriv (circleMap c₀ R) θ • F t (circleMap c₀ R θ)
  set G' : ℂ → ℝ → E := fun t θ => deriv (circleMap c₀ R) θ •
    deriv (F · (circleMap c₀ R θ)) t
  -- The circle integral equals ∫ θ in 0..2π, G t θ
  have hg_eq : ∀ t, (∮ w in C(c₀, R), F t w) = ∫ θ in (0:ℝ)..2 * Real.pi, G t θ := by
    intro t; rfl
  rw [show (fun t => ∮ w in C(c₀, R), F t w) = (fun t => ∫ θ in (0:ℝ)..2 * Real.pi, G t θ)
    from funext hg_eq]
  -- Helper: circleMap c₀ R θ ∈ sphere c₀ R
  have hcm_sphere : ∀ θ, circleMap c₀ R θ ∈ Metric.sphere c₀ R :=
    fun θ => circleMap_mem_sphere c₀ hR_pos.le θ
  -- Helper: G x is continuous for x ∈ S (hence AEStronglyMeasurable)
  have hG_cont : ∀ x ∈ S, Continuous (G x) := by
    intro x hx
    apply Continuous.smul
    · show Continuous fun θ => deriv (circleMap c₀ R) θ
      simp_rw [deriv_circleMap]
      exact (continuous_circleMap 0 R).mul continuous_const
    · exact hF_cont.comp_continuous
        (continuous_const.prodMk (continuous_circleMap c₀ R))
        (fun θ => Set.mk_mem_prod hx (hcm_sphere θ))
  -- HasDerivAt: for θ and t ∈ ball(t₀, ε), HasDerivAt (G · θ) (G' t θ) t
  have hG_deriv : ∀ θ, ∀ t ∈ Metric.ball t₀ ε, HasDerivAt (G · θ) (G' t θ) t := by
    intro θ t ht
    exact ((hF_diff _ (hcm_sphere θ)).differentiableAt
      (hS_open.mem_nhds (hcb_sub (Metric.ball_subset_closedBall
        (Metric.ball_subset_ball (by linarith : ε ≤ 2 * ε) ht))))).hasDerivAt.const_smul _
  -- Bound on ‖G' t θ‖: uses ‖deriv(circleMap)‖ = R and Cauchy estimate
  have h_norm_deriv : ∀ θ, ‖deriv (circleMap c₀ R) θ‖ = R := by
    intro θ; simp [deriv_circleMap, norm_circleMap_zero, abs_of_pos hR_pos]
  have hG'_bound : ∀ θ, ∀ t ∈ Metric.ball t₀ ε, ‖G' t θ‖ ≤ R * (M / ε) := by
    intro θ t ht
    show ‖deriv (circleMap c₀ R) θ • deriv (fun x => F x (circleMap c₀ R θ)) t‖ ≤ _
    rw [norm_smul, h_norm_deriv]
    exact mul_le_mul_of_nonneg_left (h_cauchy _ (hcm_sphere θ) t ht) hR_pos.le
  -- AEStronglyMeasurable of G'(t₀) via difference quotient sequence
  have hG'_meas : AEStronglyMeasurable (G' t₀) (MeasureTheory.volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
    -- Use difference quotient sequence: y_n = t₀ + ε/(2*(n+1)), always in ball(t₀, ε) ⊆ S
    set y : ℕ → ℂ := fun n => t₀ + ((ε / (2 * (↑n + 1)) : ℝ) : ℂ) with hy_def
    have hy_ball : ∀ n, y n ∈ Metric.ball t₀ ε := fun n => by
      have h1 : (0:ℝ) < ε / (2 * (↑n + 1)) := by positivity
      rw [Metric.mem_ball]
      calc dist (y n) t₀
          = ‖((ε / (2 * (↑n + 1)) : ℝ) : ℂ)‖ := by rw [dist_eq_norm]; simp [hy_def]
        _ = ε / (2 * (↑n + 1)) := by rw [Complex.norm_real]; exact abs_of_pos h1
        _ < ε := div_lt_self hε_pos (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hy_mem : ∀ n, y n ∈ S := fun n =>
      hcb_sub (Metric.ball_subset_closedBall
        (Metric.ball_subset_ball (by linarith : ε ≤ 2 * ε) (hy_ball n)))
    have hy_ne : ∀ n, y n ≠ t₀ := fun n => by
      intro h
      exact ne_of_gt (show (0:ℝ) < ε / (2 * (↑n + 1)) from by positivity)
        (Complex.ofReal_eq_zero.mp (by linear_combination h))
    have hy_tend : Filter.Tendsto y Filter.atTop (nhdsWithin t₀ {t₀}ᶜ) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · conv => rhs; rw [show t₀ = t₀ + (0 : ℂ) from by simp]
        apply Filter.Tendsto.const_add
        rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) from by simp]
        exact Complex.continuous_ofReal.continuousAt.tendsto.comp
          (Filter.Tendsto.div_atTop tendsto_const_nhds
            ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds
              |>.const_mul_atTop (by linarith : (0:ℝ) < 2)))
      · exact Filter.Eventually.of_forall fun n =>
          Set.mem_compl_singleton_iff.mpr (hy_ne n)
    -- Define difference quotient sequence explicitly
    set f : ℕ → ℝ → E := fun n θ => (y n - t₀)⁻¹ • (G (y n) θ - G t₀ θ) with hf_def
    -- f n θ = slope (G · θ) t₀ (y n)
    have hf_eq : ∀ n θ, f n θ = slope (fun x => G x θ) t₀ (y n) := by
      intro n θ; simp [hf_def, slope, vsub_eq_sub]
    -- Each f n is continuous (hence AEStronglyMeasurable)
    have hf_meas : ∀ n, AEStronglyMeasurable (f n)
        (MeasureTheory.volume.restrict (Set.uIoc 0 (2 * Real.pi))) := fun n =>
      (continuous_const.smul ((hG_cont _ (hy_mem n)).sub (hG_cont _ ht₀))).aestronglyMeasurable
    -- f n θ → G' t₀ θ by HasDerivAt.tendsto_slope
    have hf_tend : ∀ θ, Filter.Tendsto (fun n => f n θ) Filter.atTop (nhds (G' t₀ θ)) := by
      intro θ; simp_rw [hf_eq]
      exact (hG_deriv θ t₀ (Metric.mem_ball_self hε_pos)).tendsto_slope.comp hy_tend
    exact aestronglyMeasurable_of_tendsto_ae Filter.atTop hf_meas (ae_of_all _ hf_tend)
  -- Apply Leibniz rule
  apply DifferentiableAt.differentiableWithinAt
  apply HasDerivAt.differentiableAt
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds t₀ hε_pos)
    (Filter.eventually_iff_exists_mem.mpr ⟨Metric.ball t₀ ε, Metric.ball_mem_nhds t₀ hε_pos,
      fun x hx => (hG_cont x (hcb_sub (Metric.ball_subset_closedBall
        (Metric.ball_subset_ball (by linarith : ε ≤ 2 * ε) hx)))).aestronglyMeasurable⟩)
    ((hG_cont t₀ ht₀).intervalIntegrable 0 (2 * Real.pi))
    hG'_meas
    (ae_of_all _ fun θ hθ t ht => hG'_bound θ t ht)
    (intervalIntegrable_const)
    (ae_of_all _ fun θ hθ t ht => hG_deriv θ t ht)).2

omit [CompleteSpace E] in
/-- **Leibniz rule for iterated circle integrals.**
    If the integrand depends holomorphically on a parameter in an open set `S` for each
    point on the distinguished boundary, and is jointly continuous on
    `S × distinguishedBoundary`, then the iterated circle integral is holomorphic on `S`.

    Proved by induction on `m`, applying `differentiableOn_circleIntegral_param`
    at each level. The key point: when `z'` ranges over the inner distinguished
    boundary and `s` over a sphere, `snoc z' s` stays on the full distinguished
    boundary, so joint continuity is preserved at each inductive level. -/
private theorem differentiableOn_iteratedCircleIntegral_param {m : ℕ}
    {F : ℂ → (Fin m → ℂ) → E} {c : Fin m → ℂ} {r : Fin m → ℝ} {S : Set ℂ}
    (hr : ∀ i, 0 ≤ r i) (hS_open : IsOpen S)
    (hF_diff : ∀ w ∈ distinguishedBoundary c r,
      DifferentiableOn ℂ (fun t => F t w) S)
    (hF_cont : ContinuousOn (Function.uncurry F)
      (S ×ˢ distinguishedBoundary c r)) :
    DifferentiableOn ℂ (fun t => iteratedCircleIntegral m (F t) c r) S := by
  induction m with
  | zero =>
    simp only [iteratedCircleIntegral]
    exact hF_diff Fin.elim0 (fun j => Fin.elim0 j)
  | succ n ih =>
    simp only [iteratedCircleIntegral]
    apply ih (fun j => hr (Fin.castSucc j))
    · -- For z' on the inner distinguished boundary,
      -- show t ↦ ∮ s, F t (snoc z' s) ds is differentiable on S
      intro z' hz'
      apply differentiableOn_circleIntegral_param (hr (Fin.last n)) hS_open
      · -- F(·, snoc z' s) is differentiable on S for each s on the circle
        intro s hs
        exact hF_diff (Fin.snoc z' s) fun j =>
          Fin.lastCases (by simp [Fin.snoc_last]; exact hs)
            (fun k => by simp [Fin.snoc_castSucc]; exact hz' k) j
      · -- Joint continuity of (t, s) ↦ F(t, snoc z' s) on S × sphere
        show ContinuousOn
          (Function.uncurry F ∘ fun p : ℂ × ℂ => (p.1, Fin.snoc z' p.2))
          (S ×ˢ Metric.sphere (c (Fin.last n)) (r (Fin.last n)))
        apply ContinuousOn.comp hF_cont
        · exact (Continuous.prodMk continuous_fst
            (continuous_pi fun j => Fin.lastCases
              (by simp only [Fin.snoc_last]; exact continuous_snd)
              (fun k => by simp only [Fin.snoc_castSucc]; exact continuous_const) j)).continuousOn
        · intro ⟨t, s⟩ ⟨ht, hs⟩
          exact ⟨ht, fun j => Fin.lastCases
            (by simp only [Fin.snoc_last]; exact hs)
            (fun k => by simp only [Fin.snoc_castSucc]; exact hz' k) j⟩
    · -- Joint continuity: (t, z') ↦ ∮ s, F t (snoc z' s) is continuous on S × db'
      -- Strategy: restrict to subtype, use parametric interval integral continuity
      set cn := c (Fin.last n)
      set rn := r (Fin.last n)
      rw [continuousOn_iff_continuous_restrict]
      -- The circle integral equals an interval integral
      show Continuous fun p : ↥(S ×ˢ _) =>
        ∫ θ in (0:ℝ)..(2 * Real.pi), deriv (circleMap cn rn) θ • F p.1.1 (Fin.snoc p.1.2 (circleMap cn rn θ))
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      -- The uncurried integrand is continuous
      show Continuous fun p : ↥(S ×ˢ _) × ℝ =>
        deriv (circleMap cn rn) p.2 • F p.1.1.1 (Fin.snoc p.1.1.2 (circleMap cn rn p.2))
      apply Continuous.smul
      · -- deriv(circleMap) is continuous in θ
        simp_rw [deriv_circleMap]
        exact ((continuous_circleMap 0 rn).mul continuous_const).comp continuous_snd
      · -- F(t, snoc z' (circleMap θ)) is continuous via ContinuousOn.comp_continuous
        set db' := distinguishedBoundary (c ∘ Fin.castSucc) (r ∘ Fin.castSucc) with hdb'
        -- Build the auxiliary map g : ↥(S ×ˢ db') × ℝ → ℂ × (Fin (n+1) → ℂ)
        let g : ↥(S ×ˢ db') × ℝ → ℂ × (Fin (n + 1) → ℂ) := fun x =>
          (x.1.val.1, Fin.snoc x.1.val.2 (circleMap cn rn x.2))
        change Continuous (Function.uncurry F ∘ g)
        have hg_cont : Continuous g := by
          refine Continuous.prodMk ((continuous_subtype_val.fst).comp continuous_fst) ?_
          refine continuous_pi fun j => Fin.lastCases ?_ (fun k => ?_) j
          · -- j = Fin.last n: snoc _ w (last n) = w = circleMap
            have : (fun x : ↥(S ×ˢ db') × ℝ =>
                (g x).2 (Fin.last n)) = fun x => circleMap cn rn x.2 := by
              ext x; simp [g, Fin.snoc_last]
            rw [this]; exact (continuous_circleMap cn rn).comp continuous_snd
          · -- j = castSucc k: snoc v _ (castSucc k) = v k
            have : (fun x : ↥(S ×ˢ db') × ℝ =>
                (g x).2 (Fin.castSucc k)) = fun x => x.1.val.2 k := by
              ext x; simp [g, Fin.snoc_castSucc]
            rw [this]
            exact ((continuous_apply k).comp continuous_subtype_val.snd).comp continuous_fst
        have hg_range : ∀ x, g x ∈ S ×ˢ distinguishedBoundary c r := by
          intro ⟨⟨⟨t, z'⟩, ht, hz'⟩, θ⟩
          exact ⟨ht, fun j => j.lastCases
            (by simp only [g, Fin.snoc_last]; exact circleMap_mem_sphere cn (hr _) θ)
            (fun k => by simp only [g, Fin.snoc_castSucc]; exact hz' k)⟩
        exact hF_cont.comp_continuous hg_cont hg_range

omit [CompleteSpace E] in
/-- The Cauchy integral for polydiscs is holomorphic in `z`.

    The proof uses the Leibniz rule for iterated circle integrals. When we
    vary `z_i`, the Cauchy kernel `∏_j (w_j - z_j)⁻¹` depends on `z_i` only
    through the factor `(w_i - z_i)⁻¹`, which is holomorphic in `z_i` for
    `z_i ∈ ball(c_i, r_i)` and `w_i ∈ sphere(c_i, r_i)`. -/
theorem cauchyIntegralPolydisc_differentiableOn {m : ℕ}
    (f : (Fin m → ℂ) → E) (c : Fin m → ℂ) (r : Fin m → ℝ)
    (hr : ∀ i, 0 < r i)
    (hf_cont : ContinuousOn f (closedPolydisc c r))
    (i : Fin m) :
    ∀ z ∈ Polydisc c r,
      DifferentiableAt ℂ (fun t => cauchyIntegralPolydisc f c r (Function.update z i t))
        (z i) := by
  intro z hz
  unfold cauchyIntegralPolydisc
  apply DifferentiableAt.const_smul
  -- Use the DifferentiableOn version with S = ball(c i, r i), then extract DifferentiableAt
  apply DifferentiableOn.differentiableAt _ (Metric.isOpen_ball.mem_nhds (hz i))
  apply differentiableOn_iteratedCircleIntegral_param (fun j => le_of_lt (hr j)) Metric.isOpen_ball
  · -- The integrand is holomorphic in t on ball(c i, r i) for each w on distinguished boundary
    intro w hw t₁ ht₁
    apply DifferentiableAt.differentiableWithinAt
    -- F(t, w) = (∏_j (w_j - (update z i t)_j)⁻¹) • f w
    show DifferentiableAt ℂ
      (fun t => cauchyKernelPolydisc (Function.update z i t) w • f w) t₁
    apply DifferentiableAt.smul_const
    simp only [cauchyKernelPolydisc]
    apply DifferentiableAt.fun_finset_prod
    intro j _
    by_cases hij : j = i
    · -- The i-th factor: (w_i - t)⁻¹, holomorphic since w_i ∈ sphere, t ∈ ball
      subst hij
      simp only [Function.update_self]
      apply DifferentiableAt.inv
      · exact (differentiableAt_const _).sub differentiableAt_id
      · intro heq
        rw [sub_eq_zero] at heq
        have h1 := Metric.mem_ball.mp ht₁
        have h2 := Metric.mem_sphere.mp (hw j)
        rw [heq] at h2; linarith
    · -- Other factors: (w_j - z_j)⁻¹, constant in t
      have : (fun t => (w j - Function.update z i t j)⁻¹) =
          fun _ => (w j - z j)⁻¹ := by
        ext t; simp only [Function.update_of_ne hij]
      rw [this]; exact differentiableAt_const _
  · -- Joint continuity of (t, w) ↦ kernel(update z i t, w) • f(w)
    -- on ball(c i, r i) × distinguishedBoundary
    show ContinuousOn
      (fun p : ℂ × (Fin m → ℂ) =>
        cauchyKernelPolydisc (Function.update z i p.1) p.2 • f p.2)
      (Metric.ball (c i) (r i) ×ˢ distinguishedBoundary c r)
    apply ContinuousOn.smul
    · -- Cauchy kernel is continuous on ball × distinguishedBoundary
      simp only [cauchyKernelPolydisc]
      apply continuousOn_finset_prod
      intro j _
      apply ContinuousOn.inv₀
      · -- w_j - (update z i t)_j is continuous
        apply ContinuousOn.sub
        · exact ((continuous_apply j).comp continuous_snd).continuousOn
        · -- (update z i t)_j is continuous: equals t when j = i, constant z_j otherwise
          by_cases hij : j = i
          · subst hij; simp only [Function.update_self]
            exact continuous_fst.continuousOn
          · have : (fun p : ℂ × (Fin m → ℂ) => Function.update z i p.1 j) =
                fun _ => z j := by ext p; simp [Function.update_of_ne hij]
            rw [this]; exact continuousOn_const
      · -- w_j - (update z i t)_j ≠ 0 on ball × db
        intro ⟨t₁, w⟩ ⟨ht₁, hw⟩
        by_cases hij : j = i
        · subst hij; simp only [Function.update_self]
          intro heq; rw [sub_eq_zero] at heq
          have h1 : dist t₁ (c j) < r j := Metric.mem_ball.mp ht₁
          have h2 : dist (w j) (c j) = r j := Metric.mem_sphere.mp (hw j)
          rw [heq] at h2; linarith
        · simp only [Function.update_of_ne hij]
          intro heq; rw [sub_eq_zero] at heq
          have h1 : dist (z j) (c j) < r j := Metric.mem_ball.mp (hz j)
          have h2 : dist (w j) (c j) = r j := Metric.mem_sphere.mp (hw j)
          rw [heq] at h2; linarith
    · -- f ∘ snd is continuous on ball × db
      exact hf_cont.comp continuous_snd.continuousOn
        (fun ⟨_, w⟩ ⟨_, hw⟩ => distinguishedBoundary_subset_closedPolydisc hw)

end SCV
