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
  -- Proof structure:
  -- 1. Outside closure(supp h): product vanishes nearby → all derivatives are 0
  -- 2. Inside closure(supp h): Leibniz + Faa di Bruno + exp bound + Schwartz seminorms
  --
  -- The function equals cexp(L' ξ) * h(ξ) where L' = -ε • (ofRealCLM ∘ L) : E →L[ℝ] ℂ.
  -- By norm_iteratedFDeriv_mul_le (Leibniz):
  --   ‖D^n[cexp∘L' · h](ξ)‖ ≤ Σ C(n,i) ‖D^i[cexp∘L'](ξ)‖ · ‖D^{n-i}h(ξ)‖
  -- By norm_iteratedFDeriv_cexp_comp_clm_le (Faa di Bruno):
  --   ‖D^i[cexp∘L'](ξ)‖ ≤ i! · ‖cexp(L' ξ)‖ · ‖L'‖^i
  -- On closure(supp h), L ≥ -M ⟹ ‖cexp(L' ξ)‖ = exp(-ε·L(ξ)) ≤ exp(εM).
  -- By Schwartz decay: ‖ξ‖^k · ‖D^{n-i}h(ξ)‖ ≤ seminorm(k,n-i)(h).
  -- Total bound: Σ C(n,i) · i! · exp(εM) · ‖L'‖^i · seminorm(k,n-i)(h).
  sorry

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
  sorry

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
