/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import OSReconstruction.GeneralResults.SchwartzCutoffExp

/-!
# Schwartz Exponential Damping Convergence

Multiplying a Schwartz function by `exp(-ε · L)` (where L is a CLM)
converges to the original function in Schwartz topology as ε → 0⁺.

## Main result

`schwartz_exp_damping_tendsto`: For h ∈ S(ℝᵐ) and L : ℝᵐ →L[ℝ] ℝ,
if L is bounded below on the support of h, then the family
`exp(-εL) · h → h` in Schwartz topology as ε → 0⁺.

## Mathematical content

The hypothesis `hsupp : ∃ M, ∀ ξ, ξ ∈ Function.support h → -M ≤ L ξ` is
essential. Without it, `exp(-εL(ξ))` can grow exponentially in the direction
where L < 0, faster than any polynomial, and the product `exp(-εL)·h` need
not be Schwartz.

With the hypothesis, `exp(-εL(ξ)) ≤ exp(εM)` on supp(h) for ε > 0, and:

1. **Decay**: By Leibniz, `D^n[exp(-εL)·h]` involves terms
   `(-εL')^j exp(-εL(ξ)) · D^{n-j}h(ξ)`, each bounded by
   `(ε‖L‖)^j · exp(εM) · C_{k,n-j}` using Schwartz decay of h.
   Outside closure(supp h), the product vanishes nearby so all derivatives are 0.
2. **Convergence**: `|exp(-εL(ξ)) - 1| ≤ ε(‖L‖·‖ξ‖ + M·exp(εM))` on supp(h),
   giving each seminorm ≤ ε · (polynomial in ‖L‖, M, Schwartz constants).

## References

- Hörmander, "The Analysis of Linear PDOs I", §7.1
- Vladimirov, "Methods of Generalized Functions", §25
-/

open MeasureTheory Filter Complex
open scoped ContDiff
noncomputable section

variable {m : ℕ}

/-! ### Auxiliary lemmas -/

/-- The function `ξ ↦ exp(-ε * L(ξ)) * h(ξ)` is smooth for any fixed ε and smooth h. -/
private lemma smooth_exp_mul_schwartz
    (h : SchwartzMap (Fin m → ℝ) ℂ) (L : (Fin m → ℝ) →L[ℝ] ℝ) (ε : ℝ) :
    ContDiff ℝ ∞ (fun ξ => exp (-(ε : ℂ) * (L ξ : ℂ)) * h ξ) := by
  apply ContDiff.mul
  · apply ContDiff.cexp
    apply ContDiff.mul contDiff_const
    exact Complex.ofRealCLM.contDiff.comp L.contDiff
  · exact h.smooth'

/-- On closure(supp h), L is bounded below by -M (by continuity). -/
private lemma L_bounded_below_on_closure_support
    (h : SchwartzMap (Fin m → ℝ) ℂ) (L : (Fin m → ℝ) →L[ℝ] ℝ)
    (M : ℝ) (hsupp : ∀ ξ, ξ ∈ Function.support (⇑h) → -M ≤ L ξ) :
    ∀ ξ, ξ ∈ closure (Function.support (⇑h)) → -M ≤ L ξ := by
  intro ξ hξ
  apply closure_minimal (s := Function.support (⇑h)) _ (isClosed_Ici.preimage L.continuous) hξ
  intro x hx
  exact hsupp x hx

/-- Outside closure(supp h), the product `exp(-εL)·h` vanishes in a neighborhood. -/
private lemma expL_mul_h_eventuallyEq_zero
    (h : SchwartzMap (Fin m → ℝ) ℂ) (L : (Fin m → ℝ) →L[ℝ] ℝ) (ε : ℝ)
    (ξ : Fin m → ℝ) (hξ : ξ ∉ closure (Function.support (⇑h))) :
    (fun x => exp (-(ε : ℂ) * (L x : ℂ)) * h x) =ᶠ[nhds ξ] 0 := by
  rw [Filter.eventuallyEq_iff_exists_mem]
  exact ⟨(closure (Function.support (⇑h)))ᶜ,
    isClosed_closure.isOpen_compl.mem_nhds hξ,
    fun x hx => by
      have : h x = 0 := by
        by_contra hne
        exact hx (subset_closure (Function.mem_support.mpr hne))
      simp [this]⟩

/-- If f = 0 in a neighborhood of ξ, then iteratedFDeriv f ξ = 0. -/
private lemma iteratedFDeriv_eq_zero_of_eventuallyEq_zero
    {f : (Fin m → ℝ) → ℂ} {ξ : Fin m → ℝ}
    (hf : f =ᶠ[nhds ξ] 0) (n : ℕ) : iteratedFDeriv ℝ n f ξ = 0 := by
  rw [(hf.iteratedFDeriv ℝ n).eq_of_nhds]; simp

/-! ### Decay of exp(-εL)·h -/

/-- For ε ≥ 0 and L ≥ -M on supp(h), the product `exp(-εL(ξ))·h(ξ)` has rapid decay.

**Proof sketch** (the sorry is on the analytical bound, not the structure):

1. If ξ ∉ closure(supp h): the product is 0 nearby, so `iteratedFDeriv ℝ n ... ξ = 0`.
2. If ξ ∈ closure(supp h): by Leibniz (`norm_iteratedFDeriv_mul_le`),
   `‖D^n[exp(-εL)·h](ξ)‖ ≤ Σ_{i≤n} C(n,i) · ‖D^i[exp(-εL)](ξ)‖ · ‖D^{n-i}h(ξ)‖`.
   Each `‖D^i[exp(-εL)](ξ)‖ ≤ i! · exp(εM) · (ε‖L_clm‖)^i` by
   `norm_iteratedFDeriv_cexp_comp_clm_le` and the bound `‖cexp(-εL ξ)‖ ≤ exp(εM)`.
   Each `‖ξ‖^k · ‖D^{n-i}h(ξ)‖ ≤ seminorm(k,n-i)(h)` by Schwartz decay.
   So the total is `Σ C(n,i) · i! · exp(εM) · (ε‖L‖)^i · seminorm(k,n-i)(h)`. -/
private lemma decay_exp_mul_schwartz
    (h : SchwartzMap (Fin m → ℝ) ℂ) (L : (Fin m → ℝ) →L[ℝ] ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (M : ℝ) (hM : 0 ≤ M) (hsupp : ∀ ξ, ξ ∈ Function.support (⇑h) → -M ≤ L ξ) :
    ∀ k n : ℕ, ∃ C : ℝ,
      ∀ ξ, ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n
        (fun ξ => exp (-(ε : ℂ) * (L ξ : ℂ)) * h ξ) ξ‖ ≤ C := by
  intro k n
  -- Define the CLM L' = -ε • (ofRealCLM ∘ L) so that exp(-εL(ξ)) = cexp(L' ξ).
  let L' : (Fin m → ℝ) →L[ℝ] ℂ := -(ε : ℂ) • (Complex.ofRealCLM.comp L)
  -- The exponential factor is cexp ∘ L'
  have hfun_eq : (fun ξ => exp (-(ε : ℂ) * (L ξ : ℂ)) * h ξ) =
      (fun ξ => cexp (L' ξ) * h ξ) := by
    ext ξ; simp [L', ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  rw [hfun_eq]
  -- Exp is smooth, h is smooth
  have hexp_smooth : ContDiff ℝ ∞ (fun ξ => cexp (L' ξ)) :=
    Complex.contDiff_exp.comp L'.contDiff
  have hh_smooth : ContDiff ℝ ∞ (⇑h) := h.smooth'
  -- On closure(supp h), ‖cexp(L' ξ)‖ ≤ exp(εM)
  have hclosure := L_bounded_below_on_closure_support h L M hsupp
  have hexp_bound : ∀ ξ, ξ ∈ closure (Function.support (⇑h)) →
      ‖cexp (L' ξ)‖ ≤ Real.exp (ε * M) := by
    intro ξ hξ
    rw [Complex.norm_exp]
    have hLξ := hclosure ξ hξ
    have : (L' ξ).re = -ε * L ξ := by
      simp [L', ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        Complex.ofReal_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [this]
    exact Real.exp_le_exp.mpr (by nlinarith)
  -- Define the bound as a sum involving Schwartz seminorms
  let B := ∑ j ∈ Finset.range (n + 1),
    (n.choose j : ℝ) * (j.factorial : ℝ) * Real.exp (ε * M) *
      ‖L'‖ ^ j * (SchwartzMap.seminorm ℝ k (n - j) h)
  refine ⟨max B 0, ?_⟩
  intro ξ
  by_cases hξ : ξ ∈ closure (Function.support (⇑h))
  · -- Case: ξ ∈ closure(supp h)
    apply (le_max_left B 0).trans'
    -- Use Leibniz on the two-factor product
    let e : (Fin m → ℝ) → ℂ := fun ξ => cexp (L' ξ)
    have hLeib := norm_iteratedFDeriv_mul_le hexp_smooth hh_smooth ξ
      (show (n : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
    -- Distribute ‖ξ‖^k into the sum
    have hstep1 : ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => cexp (L' x) * h x) ξ‖ ≤
        ‖ξ‖ ^ k * ∑ j ∈ Finset.range (n + 1),
          (n.choose j : ℝ) * ‖iteratedFDeriv ℝ j e ξ‖ *
            ‖iteratedFDeriv ℝ (n - j) (⇑h) ξ‖ := by
      gcongr
      convert hLeib using 2 <;> rfl
    have hstep2 : ‖ξ‖ ^ k * ∑ j ∈ Finset.range (n + 1),
          (n.choose j : ℝ) * ‖iteratedFDeriv ℝ j e ξ‖ *
            ‖iteratedFDeriv ℝ (n - j) (⇑h) ξ‖ =
        ∑ j ∈ Finset.range (n + 1),
          (n.choose j : ℝ) * ‖iteratedFDeriv ℝ j e ξ‖ *
            (‖ξ‖ ^ k * ‖iteratedFDeriv ℝ (n - j) (⇑h) ξ‖) := by
      rw [Finset.mul_sum]; congr 1; ext j; ring
    have hstep3 : ∀ j ∈ Finset.range (n + 1),
        (n.choose j : ℝ) * ‖iteratedFDeriv ℝ j e ξ‖ *
          (‖ξ‖ ^ k * ‖iteratedFDeriv ℝ (n - j) (⇑h) ξ‖) ≤
        (n.choose j : ℝ) * (j.factorial * ‖cexp (L' ξ)‖ * ‖L'‖ ^ j) *
          (SchwartzMap.seminorm ℝ k (n - j) h) := by
      intro j _
      gcongr
      · exact norm_iteratedFDeriv_cexp_comp_clm_le L' ξ j
      · exact SchwartzMap.le_seminorm ℝ k (n - j) h ξ
    have hstep4 : ∀ j ∈ Finset.range (n + 1),
        (n.choose j : ℝ) * (j.factorial * ‖cexp (L' ξ)‖ * ‖L'‖ ^ j) *
          (SchwartzMap.seminorm ℝ k (n - j) h) ≤
        (n.choose j : ℝ) * (j.factorial * Real.exp (ε * M) * ‖L'‖ ^ j) *
          (SchwartzMap.seminorm ℝ k (n - j) h) := by
      intro j _
      gcongr
      exact hexp_bound ξ hξ
    calc ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (fun ξ => cexp (L' ξ) * h ξ) ξ‖
        ≤ ‖ξ‖ ^ k * ∑ j ∈ Finset.range (n + 1),
          (n.choose j : ℝ) * ‖iteratedFDeriv ℝ j e ξ‖ *
            ‖iteratedFDeriv ℝ (n - j) (⇑h) ξ‖ := hstep1
      _ = ∑ j ∈ Finset.range (n + 1),
            (n.choose j : ℝ) * ‖iteratedFDeriv ℝ j e ξ‖ *
              (‖ξ‖ ^ k * ‖iteratedFDeriv ℝ (n - j) (⇑h) ξ‖) := hstep2
      _ ≤ ∑ j ∈ Finset.range (n + 1),
            (n.choose j : ℝ) * (j.factorial * ‖cexp (L' ξ)‖ * ‖L'‖ ^ j) *
              (SchwartzMap.seminorm ℝ k (n - j) h) := Finset.sum_le_sum hstep3
      _ ≤ ∑ j ∈ Finset.range (n + 1),
            (n.choose j : ℝ) * (j.factorial * Real.exp (ε * M) * ‖L'‖ ^ j) *
              (SchwartzMap.seminorm ℝ k (n - j) h) := Finset.sum_le_sum hstep4
      _ = B := by dsimp only [B]; congr 1; ext j; ring
  · -- Case: ξ ∉ closure(supp h)
    apply (le_max_right B 0).trans'
    have hzero := expL_mul_h_eventuallyEq_zero h L ε ξ hξ
    have hfun_eq' : (fun x => cexp (L' x) * h x) =ᶠ[nhds ξ] 0 := by
      apply hzero.congr
      filter_upwards with x
      simp [L', ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
    rw [iteratedFDeriv_eq_zero_of_eventuallyEq_zero hfun_eq' n]
    simp

/-! ### Construction of the Schwartz family h_ε -/

/-- For ε ≥ 0, the function `ξ ↦ exp(-εL(ξ)) · h(ξ)` is Schwartz,
provided L ≥ -M on supp(h). -/
private def expDampingSchwartzPos
    (h : SchwartzMap (Fin m → ℝ) ℂ) (L : (Fin m → ℝ) →L[ℝ] ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hsupp : ∀ ξ, ξ ∈ Function.support (⇑h) → -M ≤ L ξ)
    (ε : ℝ) (hε : 0 ≤ ε) :
    SchwartzMap (Fin m → ℝ) ℂ where
  toFun ξ := exp (-(ε : ℂ) * (L ξ : ℂ)) * h ξ
  smooth' := smooth_exp_mul_schwartz h L ε
  decay' := decay_exp_mul_schwartz h L ε hε M hM hsupp

/-- The family h_ε: equals exp(-εL)·h for ε ≥ 0, equals h for ε < 0. -/
private def expDampingSchwartz
    (h : SchwartzMap (Fin m → ℝ) ℂ) (L : (Fin m → ℝ) →L[ℝ] ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hsupp : ∀ ξ, ξ ∈ Function.support (⇑h) → -M ≤ L ξ) :
    ℝ → SchwartzMap (Fin m → ℝ) ℂ :=
  fun ε => if hε : 0 ≤ ε then expDampingSchwartzPos h L M hM hsupp ε hε else h

private lemma expDampingSchwartz_apply_pos
    (h : SchwartzMap (Fin m → ℝ) ℂ) (L : (Fin m → ℝ) →L[ℝ] ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hsupp : ∀ ξ, ξ ∈ Function.support (⇑h) → -M ≤ L ξ)
    {ε : ℝ} (hε : 0 < ε) (ξ : Fin m → ℝ) :
    expDampingSchwartz h L M hM hsupp ε ξ = exp (-(ε : ℂ) * (L ξ : ℂ)) * h ξ := by
  unfold expDampingSchwartz
  rw [dif_pos hε.le]
  rfl

/-- For `-M ≤ r` and `0 < ε ≤ 1`, we have `‖cexp((-ε * r : ℝ) : ℂ) - 1‖ ≤ ε * (|r| + M * exp M)`.
This is the key pointwise bound used in the convergence proof. -/
private lemma norm_cexp_neg_eps_mul_sub_one_le
    {r M ε : ℝ} (hM : 0 ≤ M) (hr : -M ≤ r) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ‖cexp (((-ε * r : ℝ) : ℂ)) - 1‖ ≤ ε * (|r| + M * Real.exp M) := by
  have hconv : cexp (((-ε * r : ℝ) : ℂ)) = ((Real.exp (-ε * r) : ℝ) : ℂ) :=
    (Complex.ofReal_exp (-ε * r)).symm
  rw [hconv, show ((Real.exp (-ε * r) : ℝ) : ℂ) - (1 : ℂ) =
    ((Real.exp (-ε * r) - 1 : ℝ) : ℂ) from by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs]
  by_cases hr0 : 0 ≤ r
  · -- r ≥ 0: exp(-εr) ≤ 1, |exp(-εr) - 1| = 1 - exp(-εr) ≤ εr = ε|r|
    have harg : -ε * r ≤ 0 := by nlinarith
    have hexp_le : Real.exp (-ε * r) ≤ 1 := Real.exp_le_one_iff.mpr harg
    have hsub_nonpos : Real.exp (-ε * r) - 1 ≤ 0 := by linarith
    rw [abs_of_nonpos hsub_nonpos]
    -- 1 - exp(-εr) ≤ εr from exp(-εr) ≥ 1 - εr (i.e., exp(y) ≥ 1 + y with y = -εr)
    have h1 : 1 - Real.exp (-ε * r) ≤ ε * r := by
      have := Real.add_one_le_exp (-ε * r)
      linarith
    calc -(Real.exp (-ε * r) - 1) = 1 - Real.exp (-ε * r) := by ring
      _ ≤ ε * r := h1
      _ = ε * |r| := by rw [abs_of_nonneg hr0]
      _ ≤ ε * (|r| + M * Real.exp M) := by
          gcongr; exact le_add_of_nonneg_right (by positivity)
  · -- r < 0: -M ≤ r < 0, exp(-εr) > 1, |exp(-εr)-1| = exp(-εr)-1 ≤ εM·exp(M)
    push_neg at hr0
    have harg_pos : 0 < -ε * r := by nlinarith
    have hsub_nonneg : 0 ≤ Real.exp (-ε * r) - 1 := by
      linarith [Real.one_le_exp harg_pos.le]
    rw [abs_of_nonneg hsub_nonneg]
    have harg_le : -ε * r ≤ ε * M := by nlinarith
    -- exp(x) - 1 ≤ x · exp(x) for x ≥ 0: from exp(x) ≥ 1 + x, so exp(x) - 1 ≥ x,
    -- and for x ≥ 0: exp(x) - 1 ≤ (exp(x) - 1) ≤ x · exp(x) since exp(x) ≥ 1.
    have hx := -ε * r  -- this is ≥ 0
    have h_exp_sub : Real.exp (-ε * r) - 1 ≤ (-ε * r) * Real.exp (-ε * r) := by
      have h1 := Real.add_one_le_exp (-ε * r)  -- -εr + 1 ≤ exp(-εr)
      have h2 := Real.exp_nonneg (-ε * r)      -- 0 ≤ exp(-εr)
      -- Need: exp(-εr) - 1 ≤ (-εr) * exp(-εr)
      -- ↔ exp(-εr) ≤ 1 + (-εr) * exp(-εr)
      -- ↔ exp(-εr) * (1 - (-εr)) ≤ 1
      -- ↔ exp(-εr) * (1 + εr) ≤ 1  ... not obviously true for large εr!
      -- Actually for x ≥ 0: exp(x) - 1 ≤ x * exp(x) ↔ 1 - 1/exp(x) ≤ x ↔ 1 - exp(-x) ≤ x
      -- which is true since exp(-x) ≥ 1 - x.
      -- Cleaner: exp(x)(1 - x) ≤ 1 for all x. Check: f(x) = exp(x)(1-x), f(0) = 1, f'(x) = -x exp(x) ≤ 0 for x ≥ 0.
      -- So f is decreasing on [0,∞), hence f(x) ≤ f(0) = 1 for x ≥ 0.
      -- Alternatively: 1 = exp(x) * exp(-x) ≥ exp(x) * (1 - x)  since exp(-x) ≥ 1 - x.
      have h3 := Real.add_one_le_exp (-(- ε * r))  -- -(-εr) + 1 ≤ exp(-(-εr))
      -- h3: εr + 1 ≤ exp(εr), so exp(-(-εr)) = exp(εr) ≥ 1 + εr
      -- We want: exp(-εr) ≤ 1 + (-εr) * exp(-εr)
      -- i.e., exp(-εr) * (1 - (-εr)) ≤ 1, i.e., exp(-εr) * (1 + εr) ≤ 1
      -- From exp(εr) ≥ 1 + εr (h3 after simplification):
      -- 1 ≥ (1 + εr) / exp(εr) = (1 + εr) * exp(-εr)
      -- From exp(-y) ≥ 1 - y (with y = -εr), we get exp(εr) ≥ 1 + εr.
      -- Then: exp(-εr) * (1 + εr) ≤ exp(-εr) * exp(εr) = 1
      have h4 : Real.exp (-ε * r) * (1 + ε * r) ≤ 1 := by
        have : 1 + ε * r ≤ Real.exp (ε * r) := by
          have := Real.add_one_le_exp (ε * r)
          linarith
        calc Real.exp (-ε * r) * (1 + ε * r)
            ≤ Real.exp (-ε * r) * Real.exp (ε * r) := by
              gcongr
          _ = Real.exp ((-ε * r) + (ε * r)) := (Real.exp_add _ _).symm
          _ = 1 := by simp
      -- exp(-εr) ≤ 1 + (-εr) * exp(-εr) ↔ exp(-εr) * (1 - (-εr)) ≤ 1 ↔ exp(-εr) * (1 + εr) ≤ 1
      nlinarith
    calc Real.exp (-ε * r) - 1
        ≤ (-ε * r) * Real.exp (-ε * r) := h_exp_sub
      _ ≤ (ε * M) * Real.exp (ε * M) := by
          apply mul_le_mul harg_le (Real.exp_le_exp.mpr harg_le) (Real.exp_nonneg _) (by positivity)
      _ ≤ (ε * M) * Real.exp M := by
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)
      _ = ε * (M * Real.exp M) := by ring
      _ ≤ ε * (|r| + M * Real.exp M) := by
          gcongr; exact le_add_of_nonneg_left (abs_nonneg _)

/-! ### Linear-in-ε seminorm bound -/

/-- The (k,n)-Schwartz seminorm of `exp(-εL)·h - h` is O(ε) for ε ∈ (0,1].

On closure(supp h), the bound on the j=0 Leibniz term uses:
- L(ξ) ≥ 0: `|exp(-εL(ξ)) - 1| = 1 - exp(-εL(ξ)) ≤ εL(ξ) ≤ ε‖L₀‖·‖ξ‖`
- -M ≤ L(ξ) < 0: `|exp(-εL(ξ)) - 1| ≤ εM·exp(M)` (using `e^x - 1 ≤ xe^x`)
The j ≥ 1 terms carry `‖L'‖^j = (ε‖L₀‖)^j ≤ ε·‖L₀‖^j` for ε ≤ 1. -/
private lemma seminorm_expDamping_sub_le
    (h : SchwartzMap (Fin m → ℝ) ℂ) (L : (Fin m → ℝ) →L[ℝ] ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hsupp : ∀ ξ, ξ ∈ Function.support (⇑h) → -M ≤ L ξ)
    (k n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      SchwartzMap.seminorm ℝ k n (expDampingSchwartz h L M hM hsupp ε - h) ≤ C * ε := by
  let L₀ : (Fin m → ℝ) →L[ℝ] ℂ := Complex.ofRealCLM.comp L
  have hclosure := L_bounded_below_on_closure_support h L M hsupp
  -- Define the constant: j=0 contributes (‖L₀‖·seminorm(k+1,n) + M·exp(M)·seminorm(k,n))
  -- j≥1 contribute C(n,j)·j!·exp(M)·‖L₀‖^j·seminorm(k,n-j)
  let C₀ : ℝ := (‖L₀‖ * SchwartzMap.seminorm ℝ (k + 1) n h +
      M * Real.exp M * SchwartzMap.seminorm ℝ k n h) +
    ∑ j ∈ Finset.range n, ((n.choose (j + 1) : ℝ) * ((j + 1).factorial : ℝ) *
      Real.exp M * ‖L₀‖ ^ (j + 1) * SchwartzMap.seminorm ℝ k (n - (j + 1)) h)
  refine ⟨C₀ + 1, by positivity, ?_⟩
  intro ε hε hε1
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity : 0 ≤ (C₀ + 1) * ε)
  intro ξ
  -- Pointwise value
  have hval : ∀ x, (expDampingSchwartz h L M hM hsupp ε - h) x =
      (cexp (-(ε : ℂ) * (L x : ℂ)) - 1) * h x := by
    intro x; simp [SchwartzMap.sub_apply, expDampingSchwartz_apply_pos h L M hM hsupp hε, sub_mul]
  let L' : (Fin m → ℝ) →L[ℝ] ℂ := -(ε : ℂ) • L₀
  have hval' : ∀ x, (expDampingSchwartz h L M hM hsupp ε - h) x =
      (cexp (L' x) - 1) * h x := by
    intro x; rw [hval]
    simp [L', L₀, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  have hderiv_eq : iteratedFDeriv ℝ n (⇑(expDampingSchwartz h L M hM hsupp ε - h)) ξ =
      iteratedFDeriv ℝ n (fun x => (cexp (L' x) - 1) * h x) ξ := by
    congr 1; ext x; exact hval' x
  rw [hderiv_eq]
  by_cases hξ : ξ ∈ closure (Function.support (⇑h))
  · -- On closure(supp h): Leibniz bound
    have hexp_sub_smooth : ContDiff ℝ ∞ (fun x => cexp (L' x) - 1) :=
      (Complex.contDiff_exp.comp L'.contDiff).sub contDiff_const
    have hLeib := norm_iteratedFDeriv_mul_le hexp_sub_smooth h.smooth' ξ
      (show (n : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
    -- ‖cexp(L' ξ)‖ ≤ exp(M)
    have hexp_bd : ‖cexp (L' ξ)‖ ≤ Real.exp M := by
      rw [Complex.norm_exp]
      have : (L' ξ).re = -ε * L ξ := by
        simp [L', L₀, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
          Complex.ofReal_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero]
      rw [this]; exact Real.exp_le_exp.mpr (by nlinarith [hclosure ξ hξ])
    -- ‖L'‖ = ε · ‖L₀‖
    have hL'_norm : ‖L'‖ = ε * ‖L₀‖ := by
      show ‖(-(ε : ℂ)) • L₀‖ = ε * ‖L₀‖
      simp [norm_smul, RCLike.norm_ofReal, abs_of_nonneg hε.le]
    -- j=0 bound via norm_cexp_neg_eps_mul_sub_one_le
    have hj0 : ‖cexp (L' ξ) - 1‖ ≤ ε * (|L ξ| + M * Real.exp M) := by
      have : L' ξ = ((- ε * L ξ : ℝ) : ℂ) := by
        have hre : (L' ξ).re = -ε * L ξ := by
          simp [L', L₀, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
            Complex.ofReal_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero]
        have him : (L' ξ).im = 0 := by
          simp [L', L₀, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
            Complex.ofReal_im, Complex.neg_im, Complex.mul_im, Complex.ofReal_re, mul_zero, zero_mul, add_zero]
        exact Complex.ext hre him
      rw [this]
      exact norm_cexp_neg_eps_mul_sub_one_le hM (hclosure ξ hξ) hε hε1
    -- Leibniz: j=0 term
    -- ‖ξ‖^k * 1 * ‖cexp(L'ξ) - 1‖ * ‖D^n h‖
    -- ≤ ε * (|L ξ| + M·exp(M)) * (‖ξ‖^k * ‖D^n h(ξ)‖)
    -- ≤ ε * (‖L₀‖ * ‖ξ‖ * (‖ξ‖^k * ‖D^n h(ξ)‖) + M·exp(M) * seminorm(k,n)(h))
    -- ≤ ε * (‖L₀‖ * seminorm(k+1,n)(h) + M·exp(M) * seminorm(k,n)(h))
    -- Leibniz: j≥1 terms  (using D^j[cexp∘L' - 1] = D^j[cexp∘L'] for j≥1)
    -- ≤ C(n,j) * j! * exp(M) * (ε‖L₀‖)^j * seminorm(k,n-j)(h)
    -- ≤ ε * C(n,j) * j! * exp(M) * ‖L₀‖^j * seminorm(k,n-j)(h)  (since ε^{j-1} ≤ 1)
    -- Total ≤ ε * C₀
    -- Bound the full sum
    calc ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => (cexp (L' x) - 1) * h x) ξ‖
        ≤ ‖ξ‖ ^ k * ∑ j ∈ Finset.range (n + 1),
            (n.choose j : ℝ) * ‖iteratedFDeriv ℝ j (fun x => cexp (L' x) - 1) ξ‖ *
              ‖iteratedFDeriv ℝ (n - j) (⇑h) ξ‖ :=
          mul_le_mul_of_nonneg_left hLeib (pow_nonneg (norm_nonneg _) _)
      _ ≤ (C₀ + 1) * ε := by
          -- Distribute ‖ξ‖^k and split the sum into j=0 and j≥1 Leibniz terms.
          -- j=0: ‖cexp(L'ξ)-1‖ · (‖ξ‖^k · ‖D^n h‖) ≤ ε·(‖L₀‖·seminorm(k+1,n) + M·exp(M)·seminorm(k,n))
          --   using norm_cexp_neg_eps_mul_sub_one_le and Schwartz seminorm bounds.
          -- j≥1: D^j[cexp∘L'-1] = D^j[cexp∘L'] with ‖L'‖^j = (ε‖L₀‖)^j ≤ ε·‖L₀‖^j (ε ≤ 1).
          -- Each term ≤ ε · C(n,j) · j! · exp(M) · ‖L₀‖^j · seminorm(k,n-j)(h).
          -- Total ≤ C₀ · ε ≤ (C₀ + 1) · ε.
          sorry
  · -- Outside closure(supp h): vanishes
    have hzero : (fun x => (cexp (L' x) - 1) * h x) =ᶠ[nhds ξ] 0 := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      exact ⟨(closure (Function.support (⇑h)))ᶜ,
        isClosed_closure.isOpen_compl.mem_nhds hξ,
        fun x hx => by
          have : h x = 0 := by
            by_contra hne; exact hx (subset_closure (Function.mem_support.mpr hne))
          simp [this]⟩
    rw [iteratedFDeriv_eq_zero_of_eventuallyEq_zero hzero n, norm_zero, mul_zero]
    positivity

/-! ### Convergence in Schwartz topology -/

/-- The family `ε ↦ exp(-εL)·h` converges to h in the Schwartz topology as ε → 0⁺.

**Proof sketch** (uses `WithSeminorms.tendsto_nhds`):

By `schwartz_withSeminorms`, convergence in Schwartz topology is equivalent to:
for each seminorm index (k,n) and tolerance δ > 0, eventually (as ε → 0⁺)
  `SchwartzMap.seminorm ℝ k n (h_ε - h) < δ`.

The difference at ξ is `(exp(-εL(ξ)) - 1) · h(ξ)`.

**Seminorm bound**: On closure(supp h):
- For L(ξ) ≥ 0: `|exp(-εL(ξ)) - 1| = 1 - exp(-εL(ξ)) ≤ εL(ξ) ≤ ε‖L‖·‖ξ‖`
- For -M ≤ L(ξ) < 0: `|exp(-εL(ξ)) - 1| ≤ exp(εM) - 1 ≤ εM·exp(εM)` (for small ε)
Combined: `|exp(-εL(ξ)) - 1| ≤ ε · (‖L‖·‖ξ‖ + M·exp(εM))`

By Leibniz on `D^n[(exp(-εL)-1)·h]`:
- j=0 term: `(exp(-εL)-1) · D^n h` contributes O(ε) to the seminorm
- j≥1 terms: `D^j[exp(-εL)] · D^{n-j}h` are each O(ε) (since D^j[exp(-εL)]
  involves ε^j for j ≥ 1 and (εL')^j exp(-εL) is O(ε))

Total: seminorm(k,n)(h_ε - h) ≤ ε · (explicit polynomial in ‖L‖, M, seminorms of h). -/
private lemma tendsto_expDampingSchwartz
    (h : SchwartzMap (Fin m → ℝ) ℂ) (L : (Fin m → ℝ) →L[ℝ] ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hsupp : ∀ ξ, ξ ∈ Function.support (⇑h) → -M ≤ L ξ) :
    Tendsto (expDampingSchwartz h L M hM hsupp) (nhdsWithin 0 (Set.Ioi 0)) (nhds h) := by
  rw [(schwartz_withSeminorms ℝ (Fin m → ℝ) ℂ).tendsto_nhds _ _]
  intro p δ hδ
  obtain ⟨k, n⟩ := p
  -- Use the linear-in-ε seminorm bound
  obtain ⟨C, hC_pos, hC_bound⟩ :=
    seminorm_expDamping_sub_le h L M hM hsupp k n
  let ε₀ : ℝ := min 1 (δ / C)
  have hε₀_pos : 0 < ε₀ := lt_min zero_lt_one (div_pos hδ hC_pos)
  apply Filter.mem_of_superset (Ioo_mem_nhdsGT hε₀_pos)
  intro ε ⟨hε_pos, hε_lt⟩
  have hε_le_1 : ε ≤ 1 := le_trans (le_of_lt hε_lt) (min_le_left _ _)
  have hε_lt_δC : ε < δ / C := lt_of_lt_of_le hε_lt (min_le_right _ _)
  show schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ (k, n)
      (expDampingSchwartz h L M hM hsupp ε - h) < δ
  simp only [schwartzSeminormFamily]
  calc SchwartzMap.seminorm ℝ k n (expDampingSchwartz h L M hM hsupp ε - h)
      ≤ C * ε := hC_bound ε hε_pos hε_le_1
    _ < C * (δ / C) := by gcongr
    _ = δ := by field_simp

/-! ### Main theorem -/

/-- **Schwartz exponential damping convergence.**

For h ∈ S(ℝᵐ) and L : ℝᵐ →L[ℝ] ℝ with L bounded below on supp(h),
there exists a Schwartz family h_ε with h_ε(ξ) = exp(-εL(ξ))·h(ξ)
that converges to h in Schwartz topology as ε → 0⁺. -/
theorem schwartz_exp_damping_tendsto
    (h : SchwartzMap (Fin m → ℝ) ℂ)
    (L : (Fin m → ℝ) →L[ℝ] ℝ)
    (hsupp : ∃ M : ℝ, ∀ ξ, ξ ∈ Function.support (⇑h) → -M ≤ L ξ) :
    ∃ (h_ε : ℝ → SchwartzMap (Fin m → ℝ) ℂ),
      (∀ ε > 0, ∀ ξ, h_ε ε ξ = exp (-(ε : ℂ) * (L ξ : ℂ)) * h ξ) ∧
      Tendsto h_ε (nhdsWithin 0 (Set.Ioi 0)) (nhds h) := by
  obtain ⟨M₀, hM₀⟩ := hsupp
  -- Use max M₀ 0 to ensure M ≥ 0
  let M := max M₀ 0
  have hM : (0 : ℝ) ≤ M := le_max_right _ _
  have hsupp' : ∀ ξ, ξ ∈ Function.support (⇑h) → -M ≤ L ξ := by
    intro ξ hξ
    have := hM₀ ξ hξ
    linarith [le_max_left M₀ 0]
  exact ⟨expDampingSchwartz h L M hM hsupp',
    fun ε hε ξ => expDampingSchwartz_apply_pos h L M hM hsupp' hε ξ,
    tendsto_expDampingSchwartz h L M hM hsupp'⟩

end
