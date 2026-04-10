/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Mathlib429Compat
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

/-!
# Quantitative Schwartz Seminorm Bounds for Cutoff × Exponential

A smooth cutoff χ multiplied by an exponential `exp(L ξ)` (where L is a
continuous linear map with negative-real-part decay on the support) gives a
function whose Schwartz seminorms grow polynomially in ‖L‖.

## Main result

`schwartz_seminorm_cutoff_exp_bound`: For χ smooth with bounded derivatives,
and L : E →L[ℝ] ℂ with `Re(L ξ) ≤ -c‖ξ‖` on supp(χ), the (k,n)-Schwartz
seminorm of `ξ ↦ χ(ξ) * exp(L ξ)` is bounded by `B * (1 + ‖L‖)^n`,
where B depends on χ, c, k, n but NOT on L.

## Proof strategy

1. Case split on `ξ ∈ closure(supp χ)` vs outside.
2. Outside: `χ · exp(L) = 0` nearby ⟹ all derivatives vanish.
3. Inside: exp decay extends by continuity of `Re ∘ L`.
4. Leibniz rule + Faa di Bruno + polynomial×exponential bound.

## References

- Vladimirov, "Methods of Generalized Functions", §25
-/

open scoped Classical ComplexConjugate BigOperators NNReal ContDiff
open MeasureTheory Complex
noncomputable section

variable {m : ℕ}

/-! ### Helper lemmas -/

/-- `x^k * exp(-c*x)` is bounded on `[0, ∞)` for `c > 0`. -/
private lemma pow_mul_exp_neg_bounded (k : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, 0 ≤ x → x ^ k * Real.exp (-c * x) ≤ M := by
  have htend : Filter.Tendsto (fun x : ℝ => x ^ k * Real.exp (-c * x))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun x : ℝ => (c * x) ^ k * Real.exp (-(c * x)))
        Filter.atTop (nhds 0) :=
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
        (Filter.Tendsto.const_mul_atTop hc Filter.tendsto_id)
    have h2 : Filter.Tendsto (fun x : ℝ => c⁻¹ ^ k * ((c * x) ^ k * Real.exp (-(c * x))))
        Filter.atTop (nhds 0) := by
      rw [show (0 : ℝ) = c⁻¹ ^ k * 0 from (mul_zero _).symm]
      exact h1.const_mul _
    refine h2.congr (fun x => ?_)
    simp only [mul_pow, neg_mul, inv_pow]; field_simp
  have hcont : Continuous (fun x : ℝ => x ^ k * Real.exp (-c * x)) := by
    apply Continuous.mul (continuous_pow k)
    apply Real.continuous_exp.comp; exact continuous_const.mul continuous_id'
  have h1 : ∀ᶠ x in Filter.atTop, x ^ k * Real.exp (-c * x) ≤ 1 := by
    have : ∀ᶠ x in Filter.atTop, dist (x ^ k * Real.exp (-c * x)) 0 < 1 :=
      htend.eventually (Metric.ball_mem_nhds 0 one_pos)
    exact this.mono fun x hx => by
      rw [Real.dist_eq, sub_zero] at hx; exact le_of_lt (lt_of_abs_lt hx)
  obtain ⟨R, hR⟩ := h1.exists_forall_of_atTop
  obtain ⟨x₀, _, hx₀_max⟩ :=
    isCompact_Icc.exists_isMaxOn ⟨(0 : ℝ), Set.left_mem_Icc.mpr (le_max_right R 0)⟩
      hcont.continuousOn
  let M₀ := x₀ ^ k * Real.exp (-c * x₀)
  refine ⟨max M₀ 1 + 1, by linarith [le_max_right M₀ 1], ?_⟩
  intro x hx
  by_cases hxR : x ≤ max R 0
  · calc x ^ k * Real.exp (-c * x) ≤ M₀ := hx₀_max ⟨hx, hxR⟩
      _ ≤ max M₀ 1 := le_max_left _ _
      _ ≤ max M₀ 1 + 1 := le_add_of_nonneg_right one_pos.le
  · calc x ^ k * Real.exp (-c * x)
          ≤ 1 := hR x (le_of_lt (lt_of_le_of_lt (le_max_left R 0) (not_le.mp hxR)))
      _ ≤ max M₀ 1 := le_max_right _ _
      _ ≤ max M₀ 1 + 1 := le_add_of_nonneg_right one_pos.le

/-- `x^k * exp(-c*x)` is bounded by a constant times `c^{-k}`, uniformly in `c > 0`. -/
private lemma pow_mul_exp_neg_bounded_explicit (k : ℕ) :
    ∃ M : ℝ, 0 < M ∧
      ∀ c : ℝ, 0 < c → ∀ x : ℝ, 0 ≤ x →
        x ^ k * Real.exp (-c * x) ≤ M * c⁻¹ ^ k := by
  obtain ⟨M, hM_pos, hM⟩ := pow_mul_exp_neg_bounded k 1 zero_lt_one
  refine ⟨M, hM_pos, ?_⟩
  intro c hc x hx
  have hscaled : (c * x) ^ k * Real.exp (-(c * x)) ≤ M := by
    simpa using hM (c * x) (mul_nonneg hc.le hx)
  have hscaled' :
      c⁻¹ ^ k * ((c * x) ^ k * Real.exp (-(c * x))) ≤ c⁻¹ ^ k * M := by
    exact mul_le_mul_of_nonneg_left hscaled (pow_nonneg (inv_nonneg.mpr hc.le) _)
  have hleft :
      c⁻¹ ^ k * ((c * x) ^ k * Real.exp (-(c * x))) =
        x ^ k * Real.exp (-c * x) := by
    rw [show -(c * x) = -c * x by ring]
    have hpow : c⁻¹ ^ k * c ^ k = 1 := by
      rw [← mul_pow]
      have hc_inv : c⁻¹ * c = (1 : ℝ) := by field_simp [hc.ne']
      rw [hc_inv, one_pow]
    calc
      c⁻¹ ^ k * ((c * x) ^ k * Real.exp (-c * x))
          = c⁻¹ ^ k * ((c ^ k * x ^ k) * Real.exp (-c * x)) := by rw [mul_pow]
      _ = (c⁻¹ ^ k * c ^ k) * x ^ k * Real.exp (-c * x) := by ring
      _ = x ^ k * Real.exp (-c * x) := by rw [hpow, one_mul]
  calc
    x ^ k * Real.exp (-c * x)
      = c⁻¹ ^ k * ((c * x) ^ k * Real.exp (-(c * x))) := hleft.symm
    _ ≤ c⁻¹ ^ k * M := hscaled'
    _ = M * c⁻¹ ^ k := by ring

/-- Uniform derivative bound from per-order bounds. -/
private lemma extract_max_deriv_bound {χ : (Fin m → ℝ) → ℝ}
    (hχ : ∀ j : ℕ, ∃ C_j : ℝ, ∀ ξ : Fin m → ℝ, ‖iteratedFDeriv ℝ j χ ξ‖ ≤ C_j) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ j ≤ n, ∀ ξ : Fin m → ℝ, ‖iteratedFDeriv ℝ j χ ξ‖ ≤ C := by
  choose C hC using hχ
  refine ⟨(∑ j ∈ Finset.range (n + 1), |C j|) + 1, by positivity, ?_⟩
  intro j hj ξ
  calc ‖iteratedFDeriv ℝ j χ ξ‖ ≤ C j := hC j ξ
    _ ≤ |C j| := le_abs_self _
    _ ≤ ∑ i ∈ Finset.range (n + 1), |C i| :=
        Finset.single_le_sum (f := fun i => |C i|) (fun i _ => abs_nonneg _)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    _ ≤ _ := le_add_of_nonneg_right one_pos.le

/-- For a CLM `L`, `‖iteratedFDeriv ℝ i L ξ‖ ≤ ‖L‖^i` for `i ≥ 1`. -/
private lemma clm_iteratedFDeriv_norm_le (L : (Fin m → ℝ) →L[ℝ] ℂ) (ξ : Fin m → ℝ)
    (i : ℕ) (hi : 1 ≤ i) : ‖iteratedFDeriv ℝ i (L : (Fin m → ℝ) → ℂ) ξ‖ ≤ ‖L‖ ^ i := by
  rcases i with _ | i; · omega
  rcases i with _ | i
  · rw [pow_one, show (0 + 1 : ℕ) = 0 + 1 from rfl, iteratedFDeriv_succ_eq_comp_right]
    conv_lhs => rw [show (fun x => fderiv ℝ (↑L) x) = fun _ => (L : (Fin m → ℝ) →L[ℝ] ℂ)
      from funext (fun _ => ContinuousLinearMap.fderiv L)]
    simp
  · have : iteratedFDeriv ℝ (i + 2) (L : (Fin m → ℝ) → ℂ) ξ = 0 := by
      rw [show i + 2 = (i + 1) + 1 from by omega, iteratedFDeriv_succ_eq_comp_right]
      conv_lhs => rw [show (fun x => fderiv ℝ (↑L) x) = fun _ => (L : (Fin m → ℝ) →L[ℝ] ℂ)
        from funext (fun _ => ContinuousLinearMap.fderiv L)]
      rw [iteratedFDeriv_const_of_ne (by omega)]
      simp [LinearIsometryEquiv.map_zero]
    simp [this]

/-- `‖iteratedFDeriv ℝ i cexp z‖ ≤ ‖cexp z‖`. The n-th derivative of exp at z
is the multilinear map `(h₁,...,hₙ) ↦ exp(z) · h₁ · ... · hₙ`, which has
operator norm `‖exp(z)‖` by submultiplicativity in `ℂ`. -/
private lemma norm_iteratedFDeriv_cexp_le (z : ℂ) (i : ℕ) :
    ‖iteratedFDeriv ℝ i cexp z‖ ≤ ‖cexp z‖ := by
  have hiter_deriv : iteratedDeriv i (Complex.exp) z = cexp z := by
    rw [iteratedDeriv_eq_iterate]
    simp [Complex.iter_deriv_exp]
  have hComplex_norm : ‖iteratedFDeriv ℂ i cexp z‖ = ‖cexp z‖ := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact congrArg _ hiter_deriv
  have hSmooth : ContDiffAt ℂ (i : ℕ∞) cexp z := by
    exact (Complex.contDiff_exp (n := (i : ℕ∞))).contDiffAt
  have hRestrict : ((ContinuousMultilinearMap.restrictScalars ℝ) ∘
      iteratedFDeriv ℂ i cexp) z = iteratedFDeriv ℝ i cexp z :=
    hSmooth.restrictScalars_iteratedFDeriv (𝕜 := ℝ)
  rw [← hRestrict, Function.comp_apply,
    ContinuousMultilinearMap.norm_restrictScalars, hComplex_norm]

/-- `‖D^n[cexp ∘ L](ξ)‖ ≤ n! · ‖cexp(Lξ)‖ · ‖L‖^n` by Faa di Bruno. -/
private lemma norm_iteratedFDeriv_cexp_comp_clm
    (L : (Fin m → ℝ) →L[ℝ] ℂ) (ξ : Fin m → ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun x => cexp (L x)) ξ‖ ≤
      n.factorial * ‖cexp (L ξ)‖ * ‖L‖ ^ n := by
  rw [show (fun x => cexp (L x)) = cexp ∘ L from rfl]
  exact norm_iteratedFDeriv_comp_le Complex.contDiff_exp L.contDiff le_top ξ
    (fun i _ => norm_iteratedFDeriv_cexp_le (L ξ) i)
    (fun i hi _ => clm_iteratedFDeriv_norm_le L ξ i hi)

/-- If `f = 0` near `ξ`, then `iteratedFDeriv ℝ n f ξ = 0`. -/
private lemma iteratedFDeriv_eq_zero_of_eventuallyEq_zero
    {f : (Fin m → ℝ) → ℂ} {ξ : Fin m → ℝ}
    (h : f =ᶠ[nhds ξ] 0) (n : ℕ) : iteratedFDeriv ℝ n f ξ = 0 := by
  rw [(h.iteratedFDeriv ℝ n).eq_of_nhds]; simp

/-- On closure(supp χ), `Re(L ξ) ≤ -c · ‖ξ‖` by continuity. -/
private lemma decay_on_closure_support (χ : (Fin m → ℝ) → ℝ)
    (L : (Fin m → ℝ) →L[ℝ] ℂ) (c : ℝ)
    (hd : ∀ ξ : Fin m → ℝ, χ ξ ≠ 0 → (L ξ).re ≤ -c * ‖ξ‖)
    (ξ : Fin m → ℝ) (hξ : ξ ∈ closure (Function.support χ)) :
    (L ξ).re ≤ -c * ‖ξ‖ :=
  closure_minimal (fun x hx => hd x (Function.mem_support.mp hx))
    (isClosed_le (continuous_re.comp L.continuous) (continuous_const.neg.mul continuous_norm)) hξ

/-- On closure(supp χ), affine decay `Re(L ξ) ≤ A - c‖ξ‖` extends by continuity. -/
private lemma affineDecay_on_closure_support (χ : (Fin m → ℝ) → ℝ)
    (L : (Fin m → ℝ) →L[ℝ] ℂ) (A c : ℝ)
    (hd : ∀ ξ : Fin m → ℝ, χ ξ ≠ 0 → (L ξ).re ≤ A - c * ‖ξ‖)
    (ξ : Fin m → ℝ) (hξ : ξ ∈ closure (Function.support χ)) :
    (L ξ).re ≤ A - c * ‖ξ‖ :=
  closure_minimal (fun x hx => hd x (Function.mem_support.mp hx))
    (isClosed_le (continuous_re.comp L.continuous)
      (continuous_const.sub (continuous_const.mul continuous_norm))) hξ

/-- Outside closure(supp χ), the product `χ · g` vanishes nearby. -/
private lemma product_zero_outside_closure (χ : (Fin m → ℝ) → ℝ)
    (g : (Fin m → ℝ) → ℂ) (ξ : Fin m → ℝ)
    (hξ : ξ ∉ closure (Function.support χ)) :
    (fun x => (χ x : ℂ) * g x) =ᶠ[nhds ξ] 0 := by
  rw [Filter.eventuallyEq_iff_exists_mem]
  exact ⟨(closure (Function.support χ))ᶜ,
    isClosed_closure.isOpen_compl.mem_nhds hξ,
    fun x hx => by simp [show χ x = 0 from by
      by_contra h; exact hx (subset_closure (Function.mem_support.mpr h))]⟩

/-- Public wrapper for the cutoff-exponential derivative bound used downstream. -/
theorem norm_iteratedFDeriv_cexp_comp_clm_le
    (L : (Fin m → ℝ) →L[ℝ] ℂ) (ξ : Fin m → ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun x => cexp (L x)) ξ‖ ≤
      n.factorial * ‖cexp (L ξ)‖ * ‖L‖ ^ n :=
  norm_iteratedFDeriv_cexp_comp_clm L ξ n

/-- Public wrapper for the explicit polynomial-vs-exponential bound. -/
theorem pow_mul_exp_neg_bounded_explicit_le (k : ℕ) :
    ∃ M : ℝ, 0 < M ∧
      ∀ c : ℝ, 0 < c → ∀ x : ℝ, 0 ≤ x →
        x ^ k * Real.exp (-c * x) ≤ M * c⁻¹ ^ k :=
  pow_mul_exp_neg_bounded_explicit k

/-- Affine decay on the support extends to the closure of the support. -/
theorem affineDecay_on_closure_support_le
    (χ : (Fin m → ℝ) → ℝ)
    (L : (Fin m → ℝ) →L[ℝ] ℂ) (A c : ℝ)
    (hd : ∀ ξ : Fin m → ℝ, χ ξ ≠ 0 → (L ξ).re ≤ A - c * ‖ξ‖)
    (ξ : Fin m → ℝ) (hξ : ξ ∈ closure (Function.support χ)) :
    (L ξ).re ≤ A - c * ‖ξ‖ :=
  affineDecay_on_closure_support χ L A c hd ξ hξ

/-- Outside the closure of the support, a cutoff-times-anything product vanishes near the point. -/
theorem product_zero_outside_closure_support
    (χ : (Fin m → ℝ) → ℝ)
    (g : (Fin m → ℝ) → ℂ) (ξ : Fin m → ℝ)
    (hξ : ξ ∉ closure (Function.support χ)) :
    (fun x => (χ x : ℂ) * g x) =ᶠ[nhds ξ] 0 :=
  product_zero_outside_closure χ g ξ hξ

private lemma pow_mul_one_add_sq_exp_neg_bounded (k : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ M : ℝ, 0 < M ∧
      ∀ x : ℝ, 0 ≤ x →
        x ^ k * (1 + x) ^ 2 * Real.exp (-(c / 2) * x) ≤ M := by
  obtain ⟨M0, hM0_pos, hM0⟩ := pow_mul_exp_neg_bounded k (c / 2) (half_pos hc)
  obtain ⟨M1, hM1_pos, hM1⟩ := pow_mul_exp_neg_bounded (k + 1) (c / 2) (half_pos hc)
  obtain ⟨M2, hM2_pos, hM2⟩ := pow_mul_exp_neg_bounded (k + 2) (c / 2) (half_pos hc)
  refine ⟨M0 + 2 * M1 + M2 + 1, by positivity, ?_⟩
  intro x hx
  have hxk : x ^ k * (1 + x) ^ 2 * Real.exp (-(c / 2) * x) =
      x ^ k * Real.exp (-(c / 2) * x) +
        2 * (x ^ (k + 1) * Real.exp (-(c / 2) * x)) +
        x ^ (k + 2) * Real.exp (-(c / 2) * x) := by
    calc
      x ^ k * (1 + x) ^ 2 * Real.exp (-(c / 2) * x)
          = x ^ k * (1 + 2 * x + x ^ 2) * Real.exp (-(c / 2) * x) := by ring_nf
      _ = x ^ k * Real.exp (-(c / 2) * x) +
            2 * (x ^ (k + 1) * Real.exp (-(c / 2) * x)) +
            x ^ (k + 2) * Real.exp (-(c / 2) * x) := by
            rw [pow_succ, pow_succ]
            ring
  rw [hxk]
  calc
    x ^ k * Real.exp (-(c / 2) * x) +
        2 * (x ^ (k + 1) * Real.exp (-(c / 2) * x)) +
        x ^ (k + 2) * Real.exp (-(c / 2) * x)
      ≤ M0 + 2 * M1 + M2 := by
          gcongr
          · exact hM0 x hx
          · exact hM1 x hx
          · exact hM2 x hx
    _ ≤ M0 + 2 * M1 + M2 + 1 := by linarith

/-- Uniform affine cutoff-exponential bound with an auxiliary factor whose iterated
derivatives grow at most like `(1 + ‖ξ‖)^2 * exp((c/2)‖ξ‖)`.

The output constant is linear in the auxiliary bound `C_G` and uniform in the
linear exponential phase `L`. This is the form needed for the Paley-Wiener-Schwartz
local difference and Taylor-remainder kernels. -/
theorem schwartz_seminorm_cutoff_exp_mul_G_bound_affine_uniform
    (χ : (Fin m → ℝ) → ℝ)
    (hχ_smooth : ContDiff ℝ ∞ χ)
    (hχ_deriv_bound : ∀ j : ℕ, ∃ C_j : ℝ, ∀ ξ : Fin m → ℝ,
      ‖iteratedFDeriv ℝ j χ ξ‖ ≤ C_j)
    (A c : ℝ) (hc : 0 < c)
    (k n : ℕ) :
    ∃ (B : ℝ), 0 < B ∧
      ∀ (L : (Fin m → ℝ) →L[ℝ] ℂ)
        (hexp_decay : ∀ ξ : Fin m → ℝ, χ ξ ≠ 0 → (L ξ).re ≤ A - c * ‖ξ‖)
        (G : (Fin m → ℝ) → ℂ) (hG_smooth : ContDiff ℝ ∞ G)
        (C_G : ℝ) (hC_G : 0 ≤ C_G)
        (hG_bound : ∀ i ≤ n, ∀ ξ : Fin m → ℝ,
          ‖iteratedFDeriv ℝ i G ξ‖ ≤
            C_G * (i.factorial : ℝ) * (1 + ‖ξ‖) ^ 2 * Real.exp ((c / 2) * ‖ξ‖))
        (ξ : Fin m → ℝ),
        ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (fun ξ => (χ ξ : ℂ) * (cexp (L ξ) * G ξ)) ξ‖ ≤
          C_G * B * (1 + ‖L‖) ^ n := by
  obtain ⟨C, hC_pos, hC⟩ := extract_max_deriv_bound hχ_deriv_bound n
  obtain ⟨M, hM_pos, hM⟩ := pow_mul_one_add_sq_exp_neg_bounded k c hc
  let B := Real.exp A * C * (n.factorial : ℝ) * (↑n + 1) * (↑n + 1) * M + 1
  refine ⟨B, by positivity, ?_⟩
  intro L hexp_decay G hG_smooth C_G hC_G hG_bound ξ
  let f : (Fin m → ℝ) → ℂ := fun ξ => (χ ξ : ℂ)
  let g : (Fin m → ℝ) → ℂ := fun ξ => cexp (L ξ)
  let h : (Fin m → ℝ) → ℂ := fun ξ => cexp (L ξ) * G ξ
  have hf_smooth : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp hχ_smooth
  have hg_smooth : ContDiff ℝ ∞ g := Complex.contDiff_exp.comp L.contDiff
  have hh_smooth : ContDiff ℝ ∞ h := hg_smooth.mul hG_smooth
  have hfC : ∀ i ≤ n, ∀ ξ : Fin m → ℝ, ‖iteratedFDeriv ℝ i f ξ‖ ≤ C := by
    intro i hi ξ
    have : ‖iteratedFDeriv ℝ i f ξ‖ = ‖iteratedFDeriv ℝ i χ ξ‖ := by
      show ‖iteratedFDeriv ℝ i (fun x => (ofRealCLM (χ x) : ℂ)) ξ‖ = _
      rw [show (fun x => (ofRealCLM (χ x) : ℂ)) = (ofRealLI : ℝ →ₗᵢ[ℝ] ℂ) ∘ χ from rfl]
      exact ofRealLI.norm_iteratedFDeriv_comp_left (contDiff_infty.mp hχ_smooth i).contDiffAt le_rfl
    rw [this]
    exact hC i hi ξ
  by_cases hξ : ξ ∈ closure (Function.support χ)
  · have hdecay := affineDecay_on_closure_support_le χ L A c hexp_decay ξ hξ
    have hexp_bd : ‖cexp (L ξ)‖ ≤ Real.exp A * Real.exp (-c * ‖ξ‖) := by
      rw [Complex.norm_exp]
      calc
        Real.exp ((L ξ).re) ≤ Real.exp (A - c * ‖ξ‖) := Real.exp_le_exp.mpr hdecay
        _ = Real.exp A * Real.exp (-c * ‖ξ‖) := by
            rw [sub_eq_add_neg, Real.exp_add]
            simp
    have h_inner :
        ∀ i ≤ n,
          ‖iteratedFDeriv ℝ i h ξ‖ ≤
            C_G * (i.factorial : ℝ) * (↑i + 1) *
              (Real.exp A * Real.exp (-(c / 2) * ‖ξ‖)) *
              (1 + ‖ξ‖) ^ 2 * (1 + ‖L‖) ^ i := by
      intro i hi
      have hLeib_inner := norm_iteratedFDeriv_mul_le hg_smooth hG_smooth ξ
        (show (i : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
      have hterms :
          ∀ j ∈ Finset.range (i + 1),
            (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j g ξ‖ * ‖iteratedFDeriv ℝ (i - j) G ξ‖ ≤
              C_G * (i.factorial : ℝ) * ‖cexp (L ξ)‖ *
                (1 + ‖ξ‖) ^ 2 * Real.exp ((c / 2) * ‖ξ‖) * ‖L‖ ^ j := by
        intro j hj
        have hj_le : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hsub_le : i - j ≤ n := le_trans (Nat.sub_le i j) hi
        have hfac :
            (i.choose j : ℝ) * (j.factorial : ℝ) * ((i - j).factorial : ℝ) = (i.factorial : ℝ) := by
          exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj_le
        calc
          (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j g ξ‖ * ‖iteratedFDeriv ℝ (i - j) G ξ‖
              ≤ (i.choose j : ℝ) *
                  ((j.factorial : ℝ) * ‖cexp (L ξ)‖ * ‖L‖ ^ j) *
                  (C_G * ((i - j).factorial : ℝ) * (1 + ‖ξ‖) ^ 2 *
                    Real.exp ((c / 2) * ‖ξ‖)) := by
                    gcongr
                    exact norm_iteratedFDeriv_cexp_comp_clm_le L ξ j
                    exact hG_bound (i - j) hsub_le ξ
          _ = C_G * ((i.choose j : ℝ) * (j.factorial : ℝ) * ((i - j).factorial : ℝ)) *
                ‖cexp (L ξ)‖ * (1 + ‖ξ‖) ^ 2 * Real.exp ((c / 2) * ‖ξ‖) * ‖L‖ ^ j := by
                ring
          _ = C_G * (i.factorial : ℝ) * ‖cexp (L ξ)‖ *
                (1 + ‖ξ‖) ^ 2 * Real.exp ((c / 2) * ‖ξ‖) * ‖L‖ ^ j := by
                rw [hfac]
          _ = _ := by ring
      have hsum :
          ‖iteratedFDeriv ℝ i h ξ‖ ≤
            ∑ j ∈ Finset.range (i + 1),
              C_G * (i.factorial : ℝ) * ‖cexp (L ξ)‖ *
                (1 + ‖ξ‖) ^ 2 * Real.exp ((c / 2) * ‖ξ‖) * ‖L‖ ^ j := by
        calc
          ‖iteratedFDeriv ℝ i h ξ‖
              ≤ ∑ j ∈ Finset.range (i + 1),
                  (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j g ξ‖ *
                    ‖iteratedFDeriv ℝ (i - j) G ξ‖ := hLeib_inner
          _ ≤ _ := Finset.sum_le_sum hterms
      have hExpHalf :
          ‖cexp (L ξ)‖ * Real.exp ((c / 2) * ‖ξ‖) ≤
            Real.exp A * Real.exp (-(c / 2) * ‖ξ‖) := by
        calc
          ‖cexp (L ξ)‖ * Real.exp ((c / 2) * ‖ξ‖)
              ≤ (Real.exp A * Real.exp (-c * ‖ξ‖)) * Real.exp ((c / 2) * ‖ξ‖) := by
                  gcongr
          _ = Real.exp A * (Real.exp (-c * ‖ξ‖) * Real.exp ((c / 2) * ‖ξ‖)) := by ring
          _ = Real.exp A * Real.exp (-(c / 2) * ‖ξ‖) := by
                rw [← Real.exp_add]
                congr 1
                ring_nf
      calc
        ‖iteratedFDeriv ℝ i h ξ‖
            ≤ ∑ j ∈ Finset.range (i + 1),
                C_G * (i.factorial : ℝ) * ‖cexp (L ξ)‖ *
                  (1 + ‖ξ‖) ^ 2 * Real.exp ((c / 2) * ‖ξ‖) * ‖L‖ ^ j := hsum
        _ ≤ ∑ _j ∈ Finset.range (i + 1),
              C_G * (i.factorial : ℝ) * (Real.exp A * Real.exp (-(c / 2) * ‖ξ‖)) *
                (1 + ‖ξ‖) ^ 2 * (1 + ‖L‖) ^ i := by
              apply Finset.sum_le_sum
              intro j hj
              have hj_le : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
              have hL1 : ‖L‖ ≤ 1 + ‖L‖ := by linarith [norm_nonneg L]
              have hbase_ge_one : (1 : ℝ) ≤ 1 + ‖L‖ := by linarith [norm_nonneg L]
              have hpj : ‖L‖ ^ j ≤ (1 + ‖L‖) ^ i := by
                exact (pow_le_pow_left₀ (norm_nonneg _) hL1 j).trans
                  (pow_le_pow_right₀ hbase_ge_one hj_le)
              calc
                C_G * (i.factorial : ℝ) * ‖cexp (L ξ)‖ *
                    (1 + ‖ξ‖) ^ 2 * Real.exp ((c / 2) * ‖ξ‖) * ‖L‖ ^ j
                    = (C_G * (i.factorial : ℝ) * (1 + ‖ξ‖) ^ 2) *
                        ((‖cexp (L ξ)‖ * Real.exp ((c / 2) * ‖ξ‖)) * ‖L‖ ^ j) := by
                          ring_nf
                _ ≤ (C_G * (i.factorial : ℝ) * (1 + ‖ξ‖) ^ 2) *
                      ((Real.exp A * Real.exp (-(c / 2) * ‖ξ‖)) * (1 + ‖L‖) ^ i) := by
                        apply mul_le_mul_of_nonneg_left
                        · exact mul_le_mul hExpHalf hpj (pow_nonneg (norm_nonneg _) _) (by positivity)
                        · positivity
                _ = C_G * (i.factorial : ℝ) * (Real.exp A * Real.exp (-(c / 2) * ‖ξ‖)) *
                      (1 + ‖ξ‖) ^ 2 * (1 + ‖L‖) ^ i := by
                        ring_nf
        _ = (↑i + 1) *
              (C_G * (i.factorial : ℝ) * (Real.exp A * Real.exp (-(c / 2) * ‖ξ‖)) *
                (1 + ‖ξ‖) ^ 2 * (1 + ‖L‖) ^ i) := by
              simp [Finset.sum_const, Finset.card_range]
        _ = C_G * (i.factorial : ℝ) * (↑i + 1) *
              (Real.exp A * Real.exp (-(c / 2) * ‖ξ‖)) *
              (1 + ‖ξ‖) ^ 2 * (1 + ‖L‖) ^ i := by
              ring_nf
    have hLeib_outer := norm_iteratedFDeriv_mul_le hf_smooth hh_smooth ξ
      (show (n : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
    have h_outer :
        ‖iteratedFDeriv ℝ n (fun ξ => f ξ * h ξ) ξ‖ ≤
          C_G * C * (n.factorial : ℝ) * (↑n + 1) * (↑n + 1) *
            (Real.exp A * Real.exp (-(c / 2) * ‖ξ‖)) *
            (1 + ‖ξ‖) ^ 2 * (1 + ‖L‖) ^ n := by
      have hterms :
          ∀ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f ξ‖ * ‖iteratedFDeriv ℝ (n - i) h ξ‖ ≤
              C_G * C * (n.factorial : ℝ) * (↑n + 1) *
                (Real.exp A * Real.exp (-(c / 2) * ‖ξ‖)) *
                (1 + ‖ξ‖) ^ 2 * (1 + ‖L‖) ^ n := by
        intro i hi
        have hi_le : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hbase_ge_one : (1 : ℝ) ≤ 1 + ‖L‖ := by linarith [norm_nonneg L]
        have hchoose : (n.choose i : ℝ) * (((n - i).factorial : ℝ) * (↑(n - i) + 1))
            ≤ (n.factorial : ℝ) * (↑n + 1) := by
          have hfac : (n.choose i : ℝ) * ((n - i).factorial : ℝ) ≤ (n.factorial : ℝ) := by
            exact_mod_cast (show n.choose i * (n - i).factorial ≤ n.factorial by
              nlinarith [Nat.choose_mul_factorial_mul_factorial hi_le,
                Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero i)])
          have hi1 : (↑(n - i) + 1 : ℝ) ≤ (↑n + 1 : ℝ) := by
            exact_mod_cast Nat.succ_le_succ (Nat.sub_le _ _)
          have hmul :
              ((n.choose i : ℝ) * ((n - i).factorial : ℝ)) * (↑(n - i) + 1) ≤
                (n.factorial : ℝ) * (↑n + 1) := by
            exact mul_le_mul hfac hi1 (by positivity) (by positivity)
          simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
        have hpow : (1 + ‖L‖) ^ (n - i) ≤ (1 + ‖L‖) ^ n := by
          exact pow_le_pow_right₀ hbase_ge_one (Nat.sub_le _ _)
        calc
          (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f ξ‖ * ‖iteratedFDeriv ℝ (n - i) h ξ‖
              ≤ (n.choose i : ℝ) * C *
                  (C_G * ((n - i).factorial : ℝ) * (↑(n - i) + 1) *
                    (Real.exp A * Real.exp (-(c / 2) * ‖ξ‖)) *
                    (1 + ‖ξ‖) ^ 2 * (1 + ‖L‖) ^ (n - i)) := by
                    have hmul :
                        ‖iteratedFDeriv ℝ i f ξ‖ * ‖iteratedFDeriv ℝ (n - i) h ξ‖ ≤
                          C *
                            (C_G * ((n - i).factorial : ℝ) * (↑(n - i) + 1) *
                              (Real.exp A * Real.exp (-(c / 2) * ‖ξ‖)) *
                              (1 + ‖ξ‖) ^ 2 * (1 + ‖L‖) ^ (n - i)) := by
                      exact mul_le_mul
                        (hfC i hi_le ξ)
                        (h_inner (n - i) (Nat.sub_le _ _))
                        (norm_nonneg _)
                        (by positivity)
                    have hchoose_nonneg : 0 ≤ (n.choose i : ℝ) := by positivity
                    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hmul hchoose_nonneg
          _ = (C_G * C * (Real.exp A * Real.exp (-(c / 2) * ‖ξ‖)) *
                (1 + ‖ξ‖) ^ 2) *
                ((n.choose i : ℝ) * (((n - i).factorial : ℝ) * (↑(n - i) + 1)) *
                  (1 + ‖L‖) ^ (n - i)) := by
                ring_nf
          _ ≤ (C_G * C * (Real.exp A * Real.exp (-(c / 2) * ‖ξ‖)) *
                (1 + ‖ξ‖) ^ 2) *
                ((n.factorial : ℝ) * (↑n + 1) * (1 + ‖L‖) ^ n) := by
                apply mul_le_mul_of_nonneg_left
                · exact mul_le_mul hchoose hpow (pow_nonneg (by positivity) _) (by positivity)
                · positivity
          _ = C_G * C * (n.factorial : ℝ) * (↑n + 1) *
                (Real.exp A * Real.exp (-(c / 2) * ‖ξ‖)) *
                (1 + ‖ξ‖) ^ 2 * (1 + ‖L‖) ^ n := by
                ring_nf
      calc
        ‖iteratedFDeriv ℝ n (fun ξ => f ξ * h ξ) ξ‖
            ≤ ∑ i ∈ Finset.range (n + 1),
                (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f ξ‖ *
                  ‖iteratedFDeriv ℝ (n - i) h ξ‖ := hLeib_outer
        _ ≤ ∑ _i ∈ Finset.range (n + 1),
              C_G * C * (n.factorial : ℝ) * (↑n + 1) *
                (Real.exp A * Real.exp (-(c / 2) * ‖ξ‖)) *
                (1 + ‖ξ‖) ^ 2 * (1 + ‖L‖) ^ n := by
              exact Finset.sum_le_sum hterms
        _ = (↑n + 1) *
              (C_G * C * (n.factorial : ℝ) * (↑n + 1) *
                (Real.exp A * Real.exp (-(c / 2) * ‖ξ‖)) *
                (1 + ‖ξ‖) ^ 2 * (1 + ‖L‖) ^ n) := by
              simp [Finset.sum_const, Finset.card_range]
        _ = C_G * C * (n.factorial : ℝ) * (↑n + 1) * (↑n + 1) *
              (Real.exp A * Real.exp (-(c / 2) * ‖ξ‖)) *
              (1 + ‖ξ‖) ^ 2 * (1 + ‖L‖) ^ n := by
              ring_nf
    calc
      ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (fun ξ => (χ ξ : ℂ) * (cexp (L ξ) * G ξ)) ξ‖
          = ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (fun ξ => f ξ * h ξ) ξ‖ := rfl
      _ ≤ ‖ξ‖ ^ k *
            (C_G * C * (n.factorial : ℝ) * (↑n + 1) * (↑n + 1) *
              (Real.exp A * Real.exp (-(c / 2) * ‖ξ‖)) *
              (1 + ‖ξ‖) ^ 2 * (1 + ‖L‖) ^ n) := by
          exact mul_le_mul_of_nonneg_left h_outer (pow_nonneg (norm_nonneg _) _)
      _ = C_G * (Real.exp A * C * (n.factorial : ℝ) * (↑n + 1) * (↑n + 1)) *
            (‖ξ‖ ^ k * (1 + ‖ξ‖) ^ 2 * Real.exp (-(c / 2) * ‖ξ‖)) * (1 + ‖L‖) ^ n := by
          ring_nf
      _ ≤ C_G * (Real.exp A * C * (n.factorial : ℝ) * (↑n + 1) * (↑n + 1)) * M *
            (1 + ‖L‖) ^ n := by
          gcongr
          exact hM ‖ξ‖ (norm_nonneg _)
      _ = C_G * (Real.exp A * C * (n.factorial : ℝ) * (↑n + 1) * (↑n + 1) * M) *
            (1 + ‖L‖) ^ n := by
          ring_nf
      _ ≤ C_G * B * (1 + ‖L‖) ^ n := by
          gcongr
          linarith
  · have h0 : iteratedFDeriv ℝ n (fun ξ => (χ ξ : ℂ) * (cexp (L ξ) * G ξ)) ξ = 0 :=
      iteratedFDeriv_eq_zero_of_eventuallyEq_zero
        (product_zero_outside_closure_support χ (fun x => cexp (L x) * G x) ξ hξ) n
    simp [h0]
    positivity

/-! ### Main theorem -/

/-- **Quantitative seminorm bound for cutoff × exponential.** -/
theorem schwartz_seminorm_cutoff_exp_bound
    (χ : (Fin m → ℝ) → ℝ)
    (hχ_smooth : ContDiff ℝ ∞ χ)
    (hχ_deriv_bound : ∀ j : ℕ, ∃ C_j : ℝ, ∀ ξ : Fin m → ℝ,
      ‖iteratedFDeriv ℝ j χ ξ‖ ≤ C_j)
    -- NOTE: No compact support assumption needed! The exponential decay
    -- exp(-c‖ξ‖) from hexp_decay crushes polynomial growth at infinity.
    -- This is critical: the cone cutoff χ₁(ξ/R) is NOT compactly supported.
    (L : (Fin m → ℝ) →L[ℝ] ℂ)
    (c : ℝ) (hc : 0 < c)
    (hexp_decay : ∀ ξ : Fin m → ℝ, χ ξ ≠ 0 → (L ξ).re ≤ -c * ‖ξ‖)
    (k n : ℕ) :
    ∃ (B : ℝ) (hB : 0 < B),
      ∀ ξ : Fin m → ℝ,
        ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (fun ξ => (χ ξ : ℂ) * cexp (L ξ)) ξ‖ ≤
          B * (1 + ‖L‖) ^ n := by
  obtain ⟨C, hC_pos, hC⟩ := extract_max_deriv_bound hχ_deriv_bound n
  obtain ⟨M, hM_pos, hM⟩ := pow_mul_exp_neg_bounded k c hc
  -- f = χ↑ℂ, g = cexp ∘ L
  let f : (Fin m → ℝ) → ℂ := fun ξ => (χ ξ : ℂ)
  let g : (Fin m → ℝ) → ℂ := fun ξ => cexp (L ξ)
  have hf_smooth : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp hχ_smooth
  have hg_smooth : ContDiff ℝ ∞ g := Complex.contDiff_exp.comp L.contDiff
  -- ‖D^i[f](ξ)‖ ≤ C (via linear isometry ofRealLI)
  have hfC : ∀ i ≤ n, ∀ ξ : Fin m → ℝ, ‖iteratedFDeriv ℝ i f ξ‖ ≤ C := by
    intro i hi ξ
    have : ‖iteratedFDeriv ℝ i f ξ‖ = ‖iteratedFDeriv ℝ i χ ξ‖ := by
      show ‖iteratedFDeriv ℝ i (fun x => (ofRealCLM (χ x) : ℂ)) ξ‖ = _
      rw [show (fun x => (ofRealCLM (χ x) : ℂ)) = (ofRealLI : ℝ →ₗᵢ[ℝ] ℂ) ∘ χ from rfl]
      exact ofRealLI.norm_iteratedFDeriv_comp_left (contDiff_infty.mp hχ_smooth i).contDiffAt le_rfl
    rw [this]; exact hC i hi ξ
  -- B = M * C * n! * (n+1) + 1
  let B := M * C * (n.factorial : ℝ) * (↑n + 1) + 1
  refine ⟨B, by positivity, ?_⟩
  intro ξ
  by_cases hξ : ξ ∈ closure (Function.support χ)
  · -- On closure(supp χ): exponential decay holds
    have hdecay := decay_on_closure_support χ L c hexp_decay ξ hξ
    have hexp_bd : ‖cexp (L ξ)‖ ≤ Real.exp (-c * ‖ξ‖) := by
      rw [Complex.norm_exp]; exact Real.exp_le_exp_of_le hdecay
    -- Leibniz
    have hLeib := norm_iteratedFDeriv_mul_le hf_smooth hg_smooth ξ
      (show (n : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
    -- Each term: C(n,i) * ‖D^i f‖ * ‖D^{n-i} g‖ ≤ C(n,i) * C * (n-i)! * ‖exp(Lξ)‖ * ‖L‖^{n-i}
    have hterms : ∀ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f ξ‖ * ‖iteratedFDeriv ℝ (n - i) g ξ‖ ≤
        (n.choose i : ℝ) * C * ((n - i).factorial * ‖cexp (L ξ)‖ * ‖L‖ ^ (n - i)) := by
      intro i hi
      have hi_le : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      calc _ ≤ (n.choose i : ℝ) * C * ‖iteratedFDeriv ℝ (n - i) g ξ‖ := by
            gcongr; exact hfC i hi_le ξ
        _ ≤ _ := by gcongr; exact norm_iteratedFDeriv_cexp_comp_clm L ξ (n - i)
    -- Sum bound
    have hS : ‖iteratedFDeriv ℝ n (fun ξ => f ξ * g ξ) ξ‖ ≤
        C * ‖cexp (L ξ)‖ *
          ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * (n - i).factorial * ‖L‖ ^ (n - i) :=
      calc _ ≤ ∑ i ∈ Finset.range (n + 1), _ := hLeib
        _ ≤ ∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) * C * ((n - i).factorial * ‖cexp (L ξ)‖ * ‖L‖ ^ (n - i)) :=
            Finset.sum_le_sum hterms
        _ = C * ‖cexp (L ξ)‖ * ∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) * (n - i).factorial * ‖L‖ ^ (n - i) := by
            rw [Finset.mul_sum]; congr 1; ext i; ring
    -- Combinatorial sum bound: Σ C(n,i)*(n-i)!*‖L‖^{n-i} ≤ n!*(n+1)*(1+‖L‖)^n
    have hComb : ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * (n - i).factorial * ‖L‖ ^ (n - i) ≤
        n.factorial * (↑n + 1) * (1 + ‖L‖) ^ n := by
      calc ∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) * (n - i).factorial * ‖L‖ ^ (n - i)
          ≤ ∑ _ ∈ Finset.range (n + 1), ((n.factorial : ℝ) * (1 + ‖L‖) ^ n) := by
            apply Finset.sum_le_sum; intro i hi
            have hi_le := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            have h1 : (n.choose i : ℝ) * (n - i).factorial ≤ n.factorial := by
              exact_mod_cast (show n.choose i * (n - i).factorial ≤ n.factorial by
                nlinarith [Nat.choose_mul_factorial_mul_factorial hi_le,
                  Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero i)])
            have h2 : ‖L‖ ^ (n - i) ≤ (1 + ‖L‖) ^ n :=
              (pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_left one_pos.le) _).trans
                (pow_le_pow_right₀ (by linarith [norm_nonneg L]) (Nat.sub_le n i))
            exact mul_le_mul h1 h2 (pow_nonneg (norm_nonneg _) _) (Nat.cast_nonneg _)
        _ = (↑n + 1) * ((n.factorial : ℝ) * (1 + ‖L‖) ^ n) := by
            simp [Finset.sum_const, Finset.card_range]
        _ = _ := by ring
    -- Final calc
    calc ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (fun ξ => (χ ξ : ℂ) * cexp (L ξ)) ξ‖
        = ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (fun ξ => f ξ * g ξ) ξ‖ := rfl
      _ ≤ ‖ξ‖ ^ k * (C * ‖cexp (L ξ)‖ * ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * (n - i).factorial * ‖L‖ ^ (n - i)) := by
          apply mul_le_mul_of_nonneg_left hS (pow_nonneg (norm_nonneg _) _)
      _ ≤ ‖ξ‖ ^ k * (C * Real.exp (-c * ‖ξ‖) *
            (n.factorial * (↑n + 1) * (1 + ‖L‖) ^ n)) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (norm_nonneg _) _)
          apply mul_le_mul (mul_le_mul_of_nonneg_left hexp_bd (le_of_lt hC_pos))
            hComb (Finset.sum_nonneg (fun i _ => by positivity)) (by positivity)
      _ = (‖ξ‖ ^ k * Real.exp (-c * ‖ξ‖)) *
            (C * ↑n.factorial * (↑n + 1)) * (1 + ‖L‖) ^ n := by ring
      _ ≤ M * (C * ↑n.factorial * (↑n + 1)) * (1 + ‖L‖) ^ n := by
          gcongr; exact hM ‖ξ‖ (norm_nonneg _)
      _ = (M * C * ↑n.factorial * (↑n + 1)) * (1 + ‖L‖) ^ n := by ring
      _ ≤ B * (1 + ‖L‖) ^ n := by gcongr; linarith
  · -- Outside closure(supp χ): product = 0 nearby, so all derivatives vanish
    have h0 : iteratedFDeriv ℝ n (fun ξ => (χ ξ : ℂ) * cexp (L ξ)) ξ = 0 :=
      iteratedFDeriv_eq_zero_of_eventuallyEq_zero
        (product_zero_outside_closure χ (fun x => cexp (L x)) ξ hξ) n
    simp [h0]; exact mul_nonneg (by positivity) (pow_nonneg (by linarith [norm_nonneg L]) _)

/-- **Quantitative seminorm bound for cutoff × exponential with affine decay.**

If `Re(L ξ) ≤ A - c‖ξ‖` on the cutoff support, the same proof as
`schwartz_seminorm_cutoff_exp_bound` gives an extra multiplicative factor
`exp(A)` in the constant. -/
theorem schwartz_seminorm_cutoff_exp_bound_affine
    (χ : (Fin m → ℝ) → ℝ)
    (hχ_smooth : ContDiff ℝ ∞ χ)
    (hχ_deriv_bound : ∀ j : ℕ, ∃ C_j : ℝ, ∀ ξ : Fin m → ℝ,
      ‖iteratedFDeriv ℝ j χ ξ‖ ≤ C_j)
    (L : (Fin m → ℝ) →L[ℝ] ℂ)
    (A c : ℝ) (hc : 0 < c)
    (hexp_decay : ∀ ξ : Fin m → ℝ, χ ξ ≠ 0 → (L ξ).re ≤ A - c * ‖ξ‖)
    (k n : ℕ) :
    ∃ (B : ℝ) (hB : 0 < B),
      ∀ ξ : Fin m → ℝ,
        ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (fun ξ => (χ ξ : ℂ) * cexp (L ξ)) ξ‖ ≤
          B * (1 + ‖L‖) ^ n := by
  obtain ⟨C, hC_pos, hC⟩ := extract_max_deriv_bound hχ_deriv_bound n
  obtain ⟨M, hM_pos, hM⟩ := pow_mul_exp_neg_bounded k c hc
  let f : (Fin m → ℝ) → ℂ := fun ξ => (χ ξ : ℂ)
  let g : (Fin m → ℝ) → ℂ := fun ξ => cexp (L ξ)
  have hf_smooth : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp hχ_smooth
  have hg_smooth : ContDiff ℝ ∞ g := Complex.contDiff_exp.comp L.contDiff
  have hfC : ∀ i ≤ n, ∀ ξ : Fin m → ℝ, ‖iteratedFDeriv ℝ i f ξ‖ ≤ C := by
    intro i hi ξ
    have : ‖iteratedFDeriv ℝ i f ξ‖ = ‖iteratedFDeriv ℝ i χ ξ‖ := by
      show ‖iteratedFDeriv ℝ i (fun x => (ofRealCLM (χ x) : ℂ)) ξ‖ = _
      rw [show (fun x => (ofRealCLM (χ x) : ℂ)) = (ofRealLI : ℝ →ₗᵢ[ℝ] ℂ) ∘ χ from rfl]
      exact ofRealLI.norm_iteratedFDeriv_comp_left (contDiff_infty.mp hχ_smooth i).contDiffAt le_rfl
    rw [this]
    exact hC i hi ξ
  let B := Real.exp A * M * C * (n.factorial : ℝ) * (↑n + 1) + 1
  refine ⟨B, by positivity, ?_⟩
  intro ξ
  by_cases hξ : ξ ∈ closure (Function.support χ)
  · have hdecay := affineDecay_on_closure_support χ L A c hexp_decay ξ hξ
    have hexp_bd : ‖cexp (L ξ)‖ ≤ Real.exp A * Real.exp (-c * ‖ξ‖) := by
      rw [Complex.norm_exp]
      calc
        Real.exp ((L ξ).re) ≤ Real.exp (A - c * ‖ξ‖) := Real.exp_le_exp.mpr hdecay
        _ = Real.exp A * Real.exp (-c * ‖ξ‖) := by
            rw [sub_eq_add_neg, Real.exp_add]
            simp
    have hLeib := norm_iteratedFDeriv_mul_le hf_smooth hg_smooth ξ
      (show (n : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
    have hterms : ∀ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f ξ‖ * ‖iteratedFDeriv ℝ (n - i) g ξ‖ ≤
        (n.choose i : ℝ) * C * ((n - i).factorial * ‖cexp (L ξ)‖ * ‖L‖ ^ (n - i)) := by
      intro i hi
      have hi_le : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      calc
        _ ≤ (n.choose i : ℝ) * C * ‖iteratedFDeriv ℝ (n - i) g ξ‖ := by
          gcongr
          exact hfC i hi_le ξ
        _ ≤ _ := by
          gcongr
          exact norm_iteratedFDeriv_cexp_comp_clm L ξ (n - i)
    have hS : ‖iteratedFDeriv ℝ n (fun ξ => f ξ * g ξ) ξ‖ ≤
        C * ‖cexp (L ξ)‖ *
          ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * (n - i).factorial * ‖L‖ ^ (n - i) := by
      calc
        _ ≤ ∑ i ∈ Finset.range (n + 1), _ := hLeib
        _ ≤ ∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) * C * ((n - i).factorial * ‖cexp (L ξ)‖ * ‖L‖ ^ (n - i)) := by
            exact Finset.sum_le_sum hterms
        _ = C * ‖cexp (L ξ)‖ * ∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) * (n - i).factorial * ‖L‖ ^ (n - i) := by
            rw [Finset.mul_sum]
            congr 1
            ext i
            ring
    have hComb : ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * (n - i).factorial * ‖L‖ ^ (n - i) ≤
        n.factorial * (↑n + 1) * (1 + ‖L‖) ^ n := by
      calc
        ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * (n - i).factorial * ‖L‖ ^ (n - i)
          ≤ ∑ _ ∈ Finset.range (n + 1), ((n.factorial : ℝ) * (1 + ‖L‖) ^ n) := by
            apply Finset.sum_le_sum
            intro i hi
            have hi_le := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            have h1 : (n.choose i : ℝ) * (n - i).factorial ≤ n.factorial := by
              exact_mod_cast (show n.choose i * (n - i).factorial ≤ n.factorial by
                nlinarith [Nat.choose_mul_factorial_mul_factorial hi_le,
                  Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero i)])
            have h2 : ‖L‖ ^ (n - i) ≤ (1 + ‖L‖) ^ n :=
              (pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_left one_pos.le) _).trans
                (pow_le_pow_right₀ (by linarith [norm_nonneg L]) (Nat.sub_le n i))
            exact mul_le_mul h1 h2 (pow_nonneg (norm_nonneg _) _) (Nat.cast_nonneg _)
        _ = (↑n + 1) * ((n.factorial : ℝ) * (1 + ‖L‖) ^ n) := by
            simp [Finset.sum_const, Finset.card_range]
        _ = _ := by ring
    calc
      ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (fun ξ => (χ ξ : ℂ) * cexp (L ξ)) ξ‖
          = ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (fun ξ => f ξ * g ξ) ξ‖ := rfl
      _ ≤ ‖ξ‖ ^ k * (C * ‖cexp (L ξ)‖ * ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * (n - i).factorial * ‖L‖ ^ (n - i)) := by
          apply mul_le_mul_of_nonneg_left hS (pow_nonneg (norm_nonneg _) _)
      _ ≤ ‖ξ‖ ^ k * (C * (Real.exp A * Real.exp (-c * ‖ξ‖)) *
            (n.factorial * (↑n + 1) * (1 + ‖L‖) ^ n)) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (norm_nonneg _) _)
          apply mul_le_mul
            (mul_le_mul_of_nonneg_left hexp_bd (le_of_lt hC_pos))
            hComb
            (Finset.sum_nonneg (fun i _ => by positivity))
            (by positivity)
      _ = (Real.exp A * (‖ξ‖ ^ k * Real.exp (-c * ‖ξ‖))) *
            (C * ↑n.factorial * (↑n + 1)) * (1 + ‖L‖) ^ n := by ring
      _ ≤ (Real.exp A * M) * (C * ↑n.factorial * (↑n + 1)) * (1 + ‖L‖) ^ n := by
          gcongr
          exact hM ‖ξ‖ (norm_nonneg _)
      _ = (Real.exp A * M * C * ↑n.factorial * (↑n + 1)) * (1 + ‖L‖) ^ n := by
          ring
      _ ≤ B * (1 + ‖L‖) ^ n := by
          gcongr
          linarith
  · have h0 : iteratedFDeriv ℝ n (fun ξ => (χ ξ : ℂ) * cexp (L ξ)) ξ = 0 :=
      iteratedFDeriv_eq_zero_of_eventuallyEq_zero
        (product_zero_outside_closure χ (fun x => cexp (L x)) ξ hξ) n
    simp [h0]
    exact mul_nonneg (by positivity) (pow_nonneg (by linarith [norm_nonneg L]) _)

/-- Uniform-in-`L` affine version of `schwartz_seminorm_cutoff_exp_bound`.

The witness `B` depends only on the cutoff data and the affine decay
parameters `A,c,k,n`, not on the particular linear map `L`. -/
theorem schwartz_seminorm_cutoff_exp_bound_affine_uniform
    (χ : (Fin m → ℝ) → ℝ)
    (hχ_smooth : ContDiff ℝ ∞ χ)
    (hχ_deriv_bound : ∀ j : ℕ, ∃ C_j : ℝ, ∀ ξ : Fin m → ℝ,
      ‖iteratedFDeriv ℝ j χ ξ‖ ≤ C_j)
    (A c : ℝ) (hc : 0 < c)
    (k n : ℕ) :
    ∃ (B : ℝ) (hB : 0 < B),
      ∀ (L : (Fin m → ℝ) →L[ℝ] ℂ)
        (hexp_decay : ∀ ξ : Fin m → ℝ, χ ξ ≠ 0 → (L ξ).re ≤ A - c * ‖ξ‖)
        (ξ : Fin m → ℝ),
        ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (fun ξ => (χ ξ : ℂ) * cexp (L ξ)) ξ‖ ≤
          B * (1 + ‖L‖) ^ n := by
  obtain ⟨C, hC_pos, hC⟩ := extract_max_deriv_bound hχ_deriv_bound n
  obtain ⟨M, hM_pos, hM⟩ := pow_mul_exp_neg_bounded k c hc
  let B := Real.exp A * M * C * (n.factorial : ℝ) * (↑n + 1) + 1
  refine ⟨B, by positivity, ?_⟩
  intro L hexp_decay ξ
  let f : (Fin m → ℝ) → ℂ := fun ξ => (χ ξ : ℂ)
  let g : (Fin m → ℝ) → ℂ := fun ξ => cexp (L ξ)
  have hf_smooth : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp hχ_smooth
  have hg_smooth : ContDiff ℝ ∞ g := Complex.contDiff_exp.comp L.contDiff
  have hfC : ∀ i ≤ n, ∀ ξ : Fin m → ℝ, ‖iteratedFDeriv ℝ i f ξ‖ ≤ C := by
    intro i hi ξ
    have : ‖iteratedFDeriv ℝ i f ξ‖ = ‖iteratedFDeriv ℝ i χ ξ‖ := by
      show ‖iteratedFDeriv ℝ i (fun x => (ofRealCLM (χ x) : ℂ)) ξ‖ = _
      rw [show (fun x => (ofRealCLM (χ x) : ℂ)) = (ofRealLI : ℝ →ₗᵢ[ℝ] ℂ) ∘ χ from rfl]
      exact ofRealLI.norm_iteratedFDeriv_comp_left (contDiff_infty.mp hχ_smooth i).contDiffAt le_rfl
    rw [this]
    exact hC i hi ξ
  by_cases hξ : ξ ∈ closure (Function.support χ)
  · have hdecay := affineDecay_on_closure_support χ L A c hexp_decay ξ hξ
    have hexp_bd : ‖cexp (L ξ)‖ ≤ Real.exp A * Real.exp (-c * ‖ξ‖) := by
      rw [Complex.norm_exp]
      calc
        Real.exp ((L ξ).re) ≤ Real.exp (A - c * ‖ξ‖) := Real.exp_le_exp.mpr hdecay
        _ = Real.exp A * Real.exp (-c * ‖ξ‖) := by
            rw [sub_eq_add_neg, Real.exp_add]
            simp
    have hLeib := norm_iteratedFDeriv_mul_le hf_smooth hg_smooth ξ
      (show (n : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
    have hterms : ∀ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f ξ‖ * ‖iteratedFDeriv ℝ (n - i) g ξ‖ ≤
        (n.choose i : ℝ) * C * ((n - i).factorial * ‖cexp (L ξ)‖ * ‖L‖ ^ (n - i)) := by
      intro i hi
      have hi_le : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      calc
        _ ≤ (n.choose i : ℝ) * C * ‖iteratedFDeriv ℝ (n - i) g ξ‖ := by
          gcongr
          exact hfC i hi_le ξ
        _ ≤ _ := by
          gcongr
          exact norm_iteratedFDeriv_cexp_comp_clm L ξ (n - i)
    have hS : ‖iteratedFDeriv ℝ n (fun ξ => f ξ * g ξ) ξ‖ ≤
        C * ‖cexp (L ξ)‖ *
          ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * (n - i).factorial * ‖L‖ ^ (n - i) := by
      calc
        _ ≤ ∑ i ∈ Finset.range (n + 1), _ := hLeib
        _ ≤ ∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) * C * ((n - i).factorial * ‖cexp (L ξ)‖ * ‖L‖ ^ (n - i)) := by
            exact Finset.sum_le_sum hterms
        _ = C * ‖cexp (L ξ)‖ * ∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) * (n - i).factorial * ‖L‖ ^ (n - i) := by
            rw [Finset.mul_sum]
            congr 1
            ext i
            ring
    have hComb : ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * (n - i).factorial * ‖L‖ ^ (n - i) ≤
        n.factorial * (↑n + 1) * (1 + ‖L‖) ^ n := by
      calc
        ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * (n - i).factorial * ‖L‖ ^ (n - i)
          ≤ ∑ _ ∈ Finset.range (n + 1), ((n.factorial : ℝ) * (1 + ‖L‖) ^ n) := by
            apply Finset.sum_le_sum
            intro i hi
            have hi_le := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            have h1 : (n.choose i : ℝ) * (n - i).factorial ≤ n.factorial := by
              exact_mod_cast (show n.choose i * (n - i).factorial ≤ n.factorial by
                nlinarith [Nat.choose_mul_factorial_mul_factorial hi_le,
                  Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero i)])
            have h2 : ‖L‖ ^ (n - i) ≤ (1 + ‖L‖) ^ n :=
              (pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_left one_pos.le) _).trans
                (pow_le_pow_right₀ (by linarith [norm_nonneg L]) (Nat.sub_le n i))
            exact mul_le_mul h1 h2 (pow_nonneg (norm_nonneg _) _) (Nat.cast_nonneg _)
        _ = (↑n + 1) * ((n.factorial : ℝ) * (1 + ‖L‖) ^ n) := by
            simp [Finset.sum_const, Finset.card_range]
        _ = _ := by ring
    calc
      ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (fun ξ => (χ ξ : ℂ) * cexp (L ξ)) ξ‖
          = ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (fun ξ => f ξ * g ξ) ξ‖ := rfl
      _ ≤ ‖ξ‖ ^ k * (C * ‖cexp (L ξ)‖ * ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * (n - i).factorial * ‖L‖ ^ (n - i)) := by
          apply mul_le_mul_of_nonneg_left hS (pow_nonneg (norm_nonneg _) _)
      _ ≤ ‖ξ‖ ^ k * (C * (Real.exp A * Real.exp (-c * ‖ξ‖)) *
            (n.factorial * (↑n + 1) * (1 + ‖L‖) ^ n)) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (norm_nonneg _) _)
          apply mul_le_mul
            (mul_le_mul_of_nonneg_left hexp_bd (le_of_lt hC_pos))
            hComb
            (Finset.sum_nonneg (fun i _ => by positivity))
            (by positivity)
      _ = (Real.exp A * (‖ξ‖ ^ k * Real.exp (-c * ‖ξ‖))) *
            (C * ↑n.factorial * (↑n + 1)) * (1 + ‖L‖) ^ n := by ring
      _ ≤ (Real.exp A * M) * (C * ↑n.factorial * (↑n + 1)) * (1 + ‖L‖) ^ n := by
          gcongr
          exact hM ‖ξ‖ (norm_nonneg _)
      _ = (Real.exp A * M * C * ↑n.factorial * (↑n + 1)) * (1 + ‖L‖) ^ n := by
          ring
      _ ≤ B * (1 + ‖L‖) ^ n := by
          gcongr
          linarith
  · have h0 : iteratedFDeriv ℝ n (fun ξ => (χ ξ : ℂ) * cexp (L ξ)) ξ = 0 :=
      iteratedFDeriv_eq_zero_of_eventuallyEq_zero
        (product_zero_outside_closure χ (fun x => cexp (L x)) ξ hξ) n
    simp [h0]
    exact mul_nonneg (by positivity) (pow_nonneg (by linarith [norm_nonneg L]) _)

/-- Uniform-in-`L` affine version with explicit `c^{-k}` dependence.

The witness `B` depends only on the cutoff data and `A,k,n`, and the decay
parameter enters explicitly as `c^{-k}`. This is the form needed for global
Vladimirov-type bounds when `c` varies with the tube point. -/
theorem schwartz_seminorm_cutoff_exp_bound_affine_uniform_explicit
    (χ : (Fin m → ℝ) → ℝ)
    (hχ_smooth : ContDiff ℝ ∞ χ)
    (hχ_deriv_bound : ∀ j : ℕ, ∃ C_j : ℝ, ∀ ξ : Fin m → ℝ,
      ‖iteratedFDeriv ℝ j χ ξ‖ ≤ C_j)
    (A c : ℝ) (hc : 0 < c)
    (k n : ℕ) :
    ∃ (B : ℝ) (hB : 0 < B),
      ∀ (L : (Fin m → ℝ) →L[ℝ] ℂ)
        (hexp_decay : ∀ ξ : Fin m → ℝ, χ ξ ≠ 0 → (L ξ).re ≤ A - c * ‖ξ‖)
        (ξ : Fin m → ℝ),
        ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (fun ξ => (χ ξ : ℂ) * cexp (L ξ)) ξ‖ ≤
          B * c⁻¹ ^ k * (1 + ‖L‖) ^ n := by
  obtain ⟨C, hC_pos, hC⟩ := extract_max_deriv_bound hχ_deriv_bound n
  obtain ⟨M, hM_pos, hM⟩ := pow_mul_exp_neg_bounded_explicit k
  let B := Real.exp A * M * C * (n.factorial : ℝ) * (↑n + 1)
  refine ⟨B, by positivity, ?_⟩
  intro L hexp_decay ξ
  let f : (Fin m → ℝ) → ℂ := fun ξ => (χ ξ : ℂ)
  let g : (Fin m → ℝ) → ℂ := fun ξ => cexp (L ξ)
  have hf_smooth : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp hχ_smooth
  have hg_smooth : ContDiff ℝ ∞ g := Complex.contDiff_exp.comp L.contDiff
  have hfC : ∀ i ≤ n, ∀ ξ : Fin m → ℝ, ‖iteratedFDeriv ℝ i f ξ‖ ≤ C := by
    intro i hi ξ
    have : ‖iteratedFDeriv ℝ i f ξ‖ = ‖iteratedFDeriv ℝ i χ ξ‖ := by
      show ‖iteratedFDeriv ℝ i (fun x => (ofRealCLM (χ x) : ℂ)) ξ‖ = _
      rw [show (fun x => (ofRealCLM (χ x) : ℂ)) = (ofRealLI : ℝ →ₗᵢ[ℝ] ℂ) ∘ χ from rfl]
      exact ofRealLI.norm_iteratedFDeriv_comp_left (contDiff_infty.mp hχ_smooth i).contDiffAt le_rfl
    rw [this]
    exact hC i hi ξ
  by_cases hξ : ξ ∈ closure (Function.support χ)
  · have hdecay := affineDecay_on_closure_support χ L A c hexp_decay ξ hξ
    have hexp_bd : ‖cexp (L ξ)‖ ≤ Real.exp A * Real.exp (-c * ‖ξ‖) := by
      rw [Complex.norm_exp]
      calc
        Real.exp ((L ξ).re) ≤ Real.exp (A - c * ‖ξ‖) := Real.exp_le_exp.mpr hdecay
        _ = Real.exp A * Real.exp (-c * ‖ξ‖) := by
            rw [sub_eq_add_neg, Real.exp_add]
            simp
    have hLeib := norm_iteratedFDeriv_mul_le hf_smooth hg_smooth ξ
      (show (n : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
    have hterms : ∀ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f ξ‖ * ‖iteratedFDeriv ℝ (n - i) g ξ‖ ≤
        (n.choose i : ℝ) * C * ((n - i).factorial * ‖cexp (L ξ)‖ * ‖L‖ ^ (n - i)) := by
      intro i hi
      have hi_le : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      calc
        _ ≤ (n.choose i : ℝ) * C * ‖iteratedFDeriv ℝ (n - i) g ξ‖ := by
          gcongr
          exact hfC i hi_le ξ
        _ ≤ _ := by
          gcongr
          exact norm_iteratedFDeriv_cexp_comp_clm L ξ (n - i)
    have hS : ‖iteratedFDeriv ℝ n (fun ξ => f ξ * g ξ) ξ‖ ≤
        C * ‖cexp (L ξ)‖ *
          ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * (n - i).factorial * ‖L‖ ^ (n - i) := by
      calc
        _ ≤ ∑ i ∈ Finset.range (n + 1), _ := hLeib
        _ ≤ ∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) * C * ((n - i).factorial * ‖cexp (L ξ)‖ * ‖L‖ ^ (n - i)) := by
            exact Finset.sum_le_sum hterms
        _ = C * ‖cexp (L ξ)‖ * ∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) * (n - i).factorial * ‖L‖ ^ (n - i) := by
            rw [Finset.mul_sum]
            congr 1
            ext i
            ring
    have hComb : ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * (n - i).factorial * ‖L‖ ^ (n - i) ≤
        n.factorial * (↑n + 1) * (1 + ‖L‖) ^ n := by
      calc
        ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * (n - i).factorial * ‖L‖ ^ (n - i)
          ≤ ∑ _ ∈ Finset.range (n + 1), ((n.factorial : ℝ) * (1 + ‖L‖) ^ n) := by
            apply Finset.sum_le_sum
            intro i hi
            have hi_le := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            have h1 : (n.choose i : ℝ) * (n - i).factorial ≤ n.factorial := by
              exact_mod_cast (show n.choose i * (n - i).factorial ≤ n.factorial by
                nlinarith [Nat.choose_mul_factorial_mul_factorial hi_le,
                  Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero i)])
            have h2 : ‖L‖ ^ (n - i) ≤ (1 + ‖L‖) ^ n :=
              (pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_left one_pos.le) _).trans
                (pow_le_pow_right₀ (by linarith [norm_nonneg L]) (Nat.sub_le n i))
            exact mul_le_mul h1 h2 (pow_nonneg (norm_nonneg _) _) (Nat.cast_nonneg _)
        _ = (↑n + 1) * ((n.factorial : ℝ) * (1 + ‖L‖) ^ n) := by
            simp [Finset.sum_const, Finset.card_range]
        _ = _ := by ring
    calc
      ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (fun ξ => (χ ξ : ℂ) * cexp (L ξ)) ξ‖
          = ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (fun ξ => f ξ * g ξ) ξ‖ := rfl
      _ ≤ ‖ξ‖ ^ k * (C * ‖cexp (L ξ)‖ * ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * (n - i).factorial * ‖L‖ ^ (n - i)) := by
          apply mul_le_mul_of_nonneg_left hS (pow_nonneg (norm_nonneg _) _)
      _ ≤ ‖ξ‖ ^ k * (C * (Real.exp A * Real.exp (-c * ‖ξ‖)) *
            (n.factorial * (↑n + 1) * (1 + ‖L‖) ^ n)) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (norm_nonneg _) _)
          apply mul_le_mul
            (mul_le_mul_of_nonneg_left hexp_bd (le_of_lt hC_pos))
            hComb
            (Finset.sum_nonneg (fun i _ => by positivity))
            (by positivity)
      _ = (Real.exp A * (‖ξ‖ ^ k * Real.exp (-c * ‖ξ‖))) *
            ((C * ↑n.factorial * (↑n + 1)) * (1 + ‖L‖) ^ n) := by
          ring
      _ ≤ (Real.exp A * (M * c⁻¹ ^ k)) *
            ((C * ↑n.factorial * (↑n + 1)) * (1 + ‖L‖) ^ n) := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left
              (hM c hc ‖ξ‖ (norm_nonneg _)) (Real.exp_pos A).le
          · positivity
      _ = B * c⁻¹ ^ k * (1 + ‖L‖) ^ n := by
          dsimp [B]
          ring
  · have h0 : iteratedFDeriv ℝ n (fun ξ => (χ ξ : ℂ) * cexp (L ξ)) ξ = 0 :=
      iteratedFDeriv_eq_zero_of_eventuallyEq_zero
        (product_zero_outside_closure χ (fun x => cexp (L x)) ξ hξ) n
    simp [h0]
    positivity

/-- Uniform-in-`L` and uniform-in-`c` affine version with explicit `c^{-k}` dependence.

The witness `B` depends only on the cutoff data and `A,k,n`. This is the version
needed when the decay rate varies with an external parameter. -/
theorem schwartz_seminorm_cutoff_exp_bound_affine_uniform_explicit_uniform
    (χ : (Fin m → ℝ) → ℝ)
    (hχ_smooth : ContDiff ℝ ∞ χ)
    (hχ_deriv_bound : ∀ j : ℕ, ∃ C_j : ℝ, ∀ ξ : Fin m → ℝ,
      ‖iteratedFDeriv ℝ j χ ξ‖ ≤ C_j)
    (A : ℝ) (k n : ℕ) :
    ∃ (B : ℝ) (hB : 0 < B),
      ∀ (c : ℝ) (hc : 0 < c)
        (L : (Fin m → ℝ) →L[ℝ] ℂ)
        (hexp_decay : ∀ ξ : Fin m → ℝ, χ ξ ≠ 0 → (L ξ).re ≤ A - c * ‖ξ‖)
        (ξ : Fin m → ℝ),
        ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (fun ξ => (χ ξ : ℂ) * cexp (L ξ)) ξ‖ ≤
          B * c⁻¹ ^ k * (1 + ‖L‖) ^ n := by
  obtain ⟨C, hC_pos, hC⟩ := extract_max_deriv_bound hχ_deriv_bound n
  obtain ⟨M, hM_pos, hM⟩ := pow_mul_exp_neg_bounded_explicit k
  let B := Real.exp A * M * C * (n.factorial : ℝ) * (↑n + 1)
  refine ⟨B, by positivity, ?_⟩
  intro c hc L hexp_decay ξ
  let f : (Fin m → ℝ) → ℂ := fun ξ => (χ ξ : ℂ)
  let g : (Fin m → ℝ) → ℂ := fun ξ => cexp (L ξ)
  have hf_smooth : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp hχ_smooth
  have hg_smooth : ContDiff ℝ ∞ g := Complex.contDiff_exp.comp L.contDiff
  have hfC : ∀ i ≤ n, ∀ ξ : Fin m → ℝ, ‖iteratedFDeriv ℝ i f ξ‖ ≤ C := by
    intro i hi ξ
    have : ‖iteratedFDeriv ℝ i f ξ‖ = ‖iteratedFDeriv ℝ i χ ξ‖ := by
      show ‖iteratedFDeriv ℝ i (fun x => (ofRealCLM (χ x) : ℂ)) ξ‖ = _
      rw [show (fun x => (ofRealCLM (χ x) : ℂ)) = (ofRealLI : ℝ →ₗᵢ[ℝ] ℂ) ∘ χ from rfl]
      exact ofRealLI.norm_iteratedFDeriv_comp_left (contDiff_infty.mp hχ_smooth i).contDiffAt le_rfl
    rw [this]
    exact hC i hi ξ
  by_cases hξ : ξ ∈ closure (Function.support χ)
  · have hdecay := affineDecay_on_closure_support χ L A c hexp_decay ξ hξ
    have hexp_bd : ‖cexp (L ξ)‖ ≤ Real.exp A * Real.exp (-c * ‖ξ‖) := by
      rw [Complex.norm_exp]
      calc
        Real.exp ((L ξ).re) ≤ Real.exp (A - c * ‖ξ‖) := Real.exp_le_exp.mpr hdecay
        _ = Real.exp A * Real.exp (-c * ‖ξ‖) := by
            rw [sub_eq_add_neg, Real.exp_add]
            simp
    have hLeib := norm_iteratedFDeriv_mul_le hf_smooth hg_smooth ξ
      (show (n : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
    have hterms : ∀ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f ξ‖ * ‖iteratedFDeriv ℝ (n - i) g ξ‖ ≤
        (n.choose i : ℝ) * C * ((n - i).factorial * ‖cexp (L ξ)‖ * ‖L‖ ^ (n - i)) := by
      intro i hi
      have hi_le : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      calc
        _ ≤ (n.choose i : ℝ) * C * ‖iteratedFDeriv ℝ (n - i) g ξ‖ := by
          gcongr
          exact hfC i hi_le ξ
        _ ≤ _ := by
          gcongr
          exact norm_iteratedFDeriv_cexp_comp_clm L ξ (n - i)
    have hS : ‖iteratedFDeriv ℝ n (fun ξ => f ξ * g ξ) ξ‖ ≤
        C * ‖cexp (L ξ)‖ *
          ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * (n - i).factorial * ‖L‖ ^ (n - i) := by
      calc
        _ ≤ ∑ i ∈ Finset.range (n + 1), _ := hLeib
        _ ≤ ∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) * C * ((n - i).factorial * ‖cexp (L ξ)‖ * ‖L‖ ^ (n - i)) := by
            exact Finset.sum_le_sum hterms
        _ = C * ‖cexp (L ξ)‖ * ∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) * (n - i).factorial * ‖L‖ ^ (n - i) := by
            rw [Finset.mul_sum]
            congr 1
            ext i
            ring
    have hComb : ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * (n - i).factorial * ‖L‖ ^ (n - i) ≤
        n.factorial * (↑n + 1) * (1 + ‖L‖) ^ n := by
      calc
        ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * (n - i).factorial * ‖L‖ ^ (n - i)
          ≤ ∑ _ ∈ Finset.range (n + 1), ((n.factorial : ℝ) * (1 + ‖L‖) ^ n) := by
            apply Finset.sum_le_sum
            intro i hi
            have hi_le := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            have h1 : (n.choose i : ℝ) * (n - i).factorial ≤ n.factorial := by
              exact_mod_cast (show n.choose i * (n - i).factorial ≤ n.factorial by
                nlinarith [Nat.choose_mul_factorial_mul_factorial hi_le,
                  Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero i)])
            have h2 : ‖L‖ ^ (n - i) ≤ (1 + ‖L‖) ^ n :=
              (pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_left one_pos.le) _).trans
                (pow_le_pow_right₀ (by linarith [norm_nonneg L]) (Nat.sub_le n i))
            exact mul_le_mul h1 h2 (pow_nonneg (norm_nonneg _) _) (Nat.cast_nonneg _)
        _ = (↑n + 1) * ((n.factorial : ℝ) * (1 + ‖L‖) ^ n) := by
            simp [Finset.sum_const, Finset.card_range]
        _ = _ := by ring
    calc
      ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (fun ξ => (χ ξ : ℂ) * cexp (L ξ)) ξ‖
          = ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (fun ξ => f ξ * g ξ) ξ‖ := rfl
      _ ≤ ‖ξ‖ ^ k * (C * ‖cexp (L ξ)‖ * ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * (n - i).factorial * ‖L‖ ^ (n - i)) := by
          apply mul_le_mul_of_nonneg_left hS (pow_nonneg (norm_nonneg _) _)
      _ ≤ ‖ξ‖ ^ k * (C * (Real.exp A * Real.exp (-c * ‖ξ‖)) *
            (n.factorial * (↑n + 1) * (1 + ‖L‖) ^ n)) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (norm_nonneg _) _)
          apply mul_le_mul
            (mul_le_mul_of_nonneg_left hexp_bd (le_of_lt hC_pos))
            hComb
            (Finset.sum_nonneg (fun i _ => by positivity))
            (by positivity)
      _ = (Real.exp A * (‖ξ‖ ^ k * Real.exp (-c * ‖ξ‖))) *
            ((C * ↑n.factorial * (↑n + 1)) * (1 + ‖L‖) ^ n) := by
          ring
      _ ≤ (Real.exp A * (M * c⁻¹ ^ k)) *
            ((C * ↑n.factorial * (↑n + 1)) * (1 + ‖L‖) ^ n) := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left
              (hM c hc ‖ξ‖ (norm_nonneg _)) (Real.exp_pos A).le
          · positivity
      _ = B * c⁻¹ ^ k * (1 + ‖L‖) ^ n := by
          dsimp [B]
          ring
  · have h0 : iteratedFDeriv ℝ n (fun ξ => (χ ξ : ℂ) * cexp (L ξ)) ξ = 0 :=
      iteratedFDeriv_eq_zero_of_eventuallyEq_zero
        (product_zero_outside_closure χ (fun x => cexp (L x)) ξ hξ) n
    simp [h0]
    positivity

end
