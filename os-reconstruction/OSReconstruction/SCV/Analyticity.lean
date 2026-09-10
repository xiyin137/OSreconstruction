/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.IteratedFDeriv
import OSReconstruction.SCV.IteratedCauchyIntegral





























noncomputable section

open Complex Topology Filter Metric Set Finset SCV

namespace SCV

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]



omit [CompleteSpace E] in
/-- On the trivial space `Fin 0 → ℂ`, every function is analytic. -/
private lemma analyticAt_fin_zero (f : (Fin 0 → ℂ) → E) (z : Fin 0 → ℂ) :
    AnalyticAt ℂ f z := by
  have : f = fun _ => f z := funext (fun w => congr_arg f (funext (fun i => Fin.elim0 i)))
  rw [this]; exact analyticAt_const



/-- The Cauchy coefficient for multi-index `α` on a polydisc.
    `cauchyCoeffPolydisc f c r α = (2πi)⁻ᵐ ∮...∮ f(w) · ∏ᵢ (wᵢ-cᵢ)⁻⁽ᵅᵢ⁺¹⁾ dw` -/
def cauchyCoeffPolydisc {m : ℕ} (f : (Fin m → ℂ) → E)
    (c : Fin m → ℂ) (r : Fin m → ℝ) (α : Fin m → ℕ) : E :=
  (2 * Real.pi * I)⁻¹ ^ m •
    iteratedCircleIntegral m
      (fun w => (∏ i, (w i - c i)⁻¹ ^ (α i + 1)) • f w) c r



/-- The monomial multilinear map for `σ : Fin n → Fin m`:
    `monomialMLM σ (v₁,...,vₙ) = ∏ⱼ vⱼ(σ(j))`.

    Constructed as the `n`-fold product `mkPiAlgebraFin` composed with coordinate
    projections. -/
def monomialMLM {n m : ℕ} (σ : Fin n → Fin m) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => Fin m → ℂ) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ).compContinuousLinearMap
    (fun j => ContinuousLinearMap.proj (σ j))



/-- The multi-index of `σ : Fin n → Fin m`: counts how many `j` map to each `i`. -/
def multiIdx {n m : ℕ} (σ : Fin n → Fin m) (i : Fin m) : ℕ :=
  (univ.filter (fun j => σ j = i)).card

/-- The sum of a multi-index equals n (the total degree). -/
lemma multiIdx_sum {n m : ℕ} (σ : Fin n → Fin m) :
    ∑ i, multiIdx σ i = n := by
  simp only [multiIdx]
  rw [← Finset.card_biUnion (fun i _ j _ hij =>
    Finset.disjoint_filter.mpr (fun _ _ h1 h2 => hij (h1.symm.trans h2)))]
  have : Finset.univ.biUnion (fun i : Fin m =>
    Finset.univ.filter (fun j : Fin n => σ j = i)) = Finset.univ := by
    ext j; simp
  rw [this, Finset.card_univ, Fintype.card_fin]



/-- The multi-variable Cauchy power series on a polydisc.

    For each degree `n`, the `n`-th term is the sum over all `σ : Fin n → Fin m`
    of the monomial multilinear map weighted by the Cauchy coefficient:
    `p_n = ∑_σ mkPiRing(weight(σ) • a_{α(σ)}) ∘ proj^σ`

    On the diagonal: `p_n(y,...,y) = ∑_{|α|=n} a_α · y^α`. -/
def cauchyPowerSeriesPolydisc {m : ℕ} (f : (Fin m → ℂ) → E)
    (c : Fin m → ℂ) (r : Fin m → ℝ) : FormalMultilinearSeries ℂ (Fin m → ℂ) E := fun n =>
  ∑ σ : Fin n → Fin m,
    (ContinuousMultilinearMap.mkPiRing ℂ (Fin n)
      ((↑(∏ i : Fin m, (multiIdx σ i).factorial) / ↑n.factorial : ℂ) •
        cauchyCoeffPolydisc f c r (multiIdx σ))).compContinuousLinearMap
      (fun j => ContinuousLinearMap.proj (σ j))



omit [CompleteSpace E] in
/-- Norm bound for the Cauchy coefficient. -/
theorem norm_cauchyCoeffPolydisc_le {m : ℕ} (f : (Fin m → ℂ) → E)
    (c : Fin m → ℂ) (r : Fin m → ℝ) (hr : ∀ i, 0 < r i)
    (M : ℝ) (hM : 0 ≤ M)
    (hf_bound : ∀ w ∈ distinguishedBoundary c r, ‖f w‖ ≤ M)
    (α : Fin m → ℕ) :
    ‖cauchyCoeffPolydisc f c r α‖ ≤ M / ∏ i, r i ^ α i := by
  have hr' : ∀ i, 0 ≤ r i := fun i => le_of_lt (hr i)
  have hrne : ∀ i, r i ≠ 0 := fun i => ne_of_gt (hr i)
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  unfold cauchyCoeffPolydisc
  -- Step 1: Pull out scalar norm
  rw [norm_smul, norm_pow]
  -- Step 2: ‖(2πi)⁻¹‖ = (2π)⁻¹
  have h2pi_norm : ‖(2 * ↑Real.pi * I : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by linarith [Real.pi_pos]),
      Complex.norm_I, mul_one, Complex.norm_ofNat]
  rw [h2pi_norm]
  -- Step 3: Bound integrand on distinguished boundary
  set g := fun w => (∏ i, (w i - c i)⁻¹ ^ (α i + 1)) • f w
  have hg_bound : ∀ w ∈ distinguishedBoundary c r,
      ‖g w‖ ≤ (∏ i : Fin m, (r i)⁻¹ ^ (α i + 1)) * M := by
    intro w hw; simp only [g, norm_smul]
    apply mul_le_mul _ (hf_bound w hw) (norm_nonneg _)
      (Finset.prod_nonneg (fun i _ => pow_nonneg (inv_nonneg.mpr (hr' i)) _))
    calc ‖∏ i, (w i - c i)⁻¹ ^ (α i + 1)‖
        ≤ ∏ i, ‖(w i - c i)⁻¹ ^ (α i + 1)‖ := norm_prod_le _ _
      _ = ∏ i, (r i)⁻¹ ^ (α i + 1) := by
          congr 1; ext i; rw [norm_pow, norm_inv]
          have hi := hw i; rw [Metric.mem_sphere, Complex.dist_eq] at hi; rw [hi]
  -- Step 4: Apply integral norm bound and simplify
  have h_int := norm_iteratedCircleIntegral_le m g c r _
    (mul_nonneg (Finset.prod_nonneg (fun i _ => pow_nonneg (inv_nonneg.mpr (hr' i)) _)) hM)
    hr' hg_bound
  calc (2 * Real.pi)⁻¹ ^ m * ‖iteratedCircleIntegral m g c r‖
      ≤ (2 * Real.pi)⁻¹ ^ m *
        ((2 * Real.pi) ^ m * (∏ i : Fin m, |r i|) *
          ((∏ i : Fin m, (r i)⁻¹ ^ (α i + 1)) * M)) := by gcongr
    _ = (∏ i : Fin m, |r i|) * ((∏ i : Fin m, (r i)⁻¹ ^ (α i + 1)) * M) := by
        rw [inv_pow, mul_assoc ((2 * Real.pi) ^ m),
          inv_mul_cancel_left₀ (pow_ne_zero _ h2pi_pos.ne')]
    _ = M / ∏ i, r i ^ α i := by
        simp only [abs_of_pos (hr _)]
        rw [← mul_assoc]
        suffices h : (∏ x : Fin m, r x) * ∏ i : Fin m, (r i)⁻¹ ^ (α i + 1) =
            (∏ i : Fin m, r i ^ α i)⁻¹ by
          rw [h, mul_comm, div_eq_mul_inv]
        trans ∏ i : Fin m, r i * (r i)⁻¹ ^ (α i + 1)
        · exact Finset.prod_mul_distrib.symm
        trans ∏ i : Fin m, (r i ^ α i)⁻¹
        · congr 1; ext i
          rw [pow_succ', ← mul_assoc, mul_inv_cancel₀ (hrne i), one_mul, inv_pow]
        · simp only [Finset.prod_inv_distrib]



/-- Every point of an open set in `ℂᵐ` is contained in a closed polydisc inside the set. -/
private lemma exists_uniform_polydisc_subset {k : ℕ} {U : Set (Fin k → ℂ)}
    (hU : IsOpen U) {z : Fin k → ℂ} (hz : z ∈ U) :
    ∃ R > 0, closedPolydisc z (fun _ => R) ⊆ U := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU z hz
  refine ⟨ε / 2, by linarith, fun w hw => hεU ?_⟩
  exact lt_of_le_of_lt ((dist_pi_le_iff (by linarith)).mpr hw) (by linarith)



omit [CompleteSpace E] in
/-- Joint differentiability on an open set implies separate differentiability. -/
private lemma separateDiffAt_of_diffOn {k : ℕ} {f : (Fin k → ℂ) → E}
    {U : Set (Fin k → ℂ)} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {w : Fin k → ℂ} (hw : w ∈ U) (i : Fin k) :
    DifferentiableAt ℂ (fun t => f (Function.update w i t)) (w i) := by
  apply DifferentiableAt.comp (𝕜 := ℂ)
  · -- f is differentiable at Function.update w i (w i) = w
    rw [Function.update_eq_self]; exact hf.differentiableAt (hU.mem_nhds hw)
  · -- The update map t ↦ Function.update w i t is differentiable
    exact differentiableAt_pi.mpr fun j => by
      by_cases hij : j = i
      · subst hij; simp only [Function.update_self]; exact differentiableAt_id
      · simp only [Function.update_of_ne hij]; exact differentiableAt_const _



/-- The factorial product `∏ (αᵢ!)` is bounded by `n!` when `∑ αᵢ = n`.
    This is equivalent to the multinomial coefficient being at least 1. -/
private lemma prod_factorial_multiIdx_le {n d : ℕ} (σ : Fin n → Fin d) :
    (∏ i : Fin d, (multiIdx σ i).factorial : ℕ) ≤ n.factorial := by
  have h_dvd := Nat.prod_factorial_dvd_factorial_sum Finset.univ (fun i => multiIdx σ i)
  rw [multiIdx_sum σ] at h_dvd
  exact Nat.le_of_dvd (Nat.factorial_pos n) h_dvd

section NormBound
set_option maxHeartbeats 800000

omit [CompleteSpace E] in
/-- **Norm bound for Cauchy power series coefficients on a uniform polydisc.**

    `‖p_n‖ ≤ d^n · M / R^n` where `d` is the number of variables. This follows from:
    - Triangle inequality: `‖∑_σ ...‖ ≤ ∑_σ ‖...‖`
    - `‖mkPiRing(x)‖ ≤ ‖x‖`
    - `‖proj_i‖ ≤ 1`, so `∏ ‖proj_{σ(j)}‖ ≤ 1`
    - The weight `∏(αᵢ!)/n! ≤ 1` (from `prod_factorial_multiIdx_le`)
    - The Cauchy estimate: `‖a_α‖ ≤ M / R^n` (from `norm_cauchyCoeffPolydisc_le`)
    - Cardinality: `|{σ : Fin n → Fin d}| = d^n` -/
private lemma norm_cauchyPowerSeriesPolydisc_uniform_le {m : ℕ}
    (f : (Fin (m + 1) → ℂ) → E) (z : Fin (m + 1) → ℂ) (R : ℝ) (hR : 0 < R)
    (M : ℝ) (hM : 0 ≤ M)
    (hf_bound : ∀ w ∈ distinguishedBoundary z (fun _ => R), ‖f w‖ ≤ M) (n : ℕ) :
    ‖cauchyPowerSeriesPolydisc f z (fun _ => R) n‖ ≤ (m + 1) ^ n * (M / R ^ n) := by
  -- Extract summand as opaque local definition to avoid elaboration timeouts
  let F : (Fin n → Fin (m + 1)) →
      ContinuousMultilinearMap ℂ (fun _ : Fin n => Fin (m + 1) → ℂ) E := fun σ =>
    (ContinuousMultilinearMap.mkPiRing ℂ (Fin n)
      ((↑(∏ i, (multiIdx σ i).factorial) / ↑n.factorial : ℂ) •
        cauchyCoeffPolydisc f z (fun _ => R) (multiIdx σ))).compContinuousLinearMap
      (fun j => ContinuousLinearMap.proj (σ j))
  have hpF : cauchyPowerSeriesPolydisc f z (fun _ => R) n = ∑ σ, F σ := rfl
  suffices h : ∀ σ : Fin n → Fin (m + 1), ‖F σ‖ ≤ M / R ^ n by
    rw [hpF]
    calc ‖∑ σ : Fin n → Fin (m + 1), F σ‖
        ≤ ∑ _ : Fin n → Fin (m + 1), M / R ^ n :=
          norm_sum_le_of_le _ (fun σ _ => h σ)
      _ = (m + 1) ^ n * (M / R ^ n) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
              Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  intro σ
  show ‖F σ‖ ≤ M / R ^ n
  calc ‖(ContinuousMultilinearMap.mkPiRing ℂ (Fin n) _).compContinuousLinearMap _‖
      ≤ ‖ContinuousMultilinearMap.mkPiRing ℂ (Fin n) _‖ *
        ∏ j, ‖(ContinuousLinearMap.proj (σ j) : (Fin (m+1) → ℂ) →L[ℂ] ℂ)‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖ContinuousMultilinearMap.mkPiRing ℂ (Fin n) _‖ * 1 := by
        gcongr
        apply Finset.prod_le_one (fun j _ => norm_nonneg _) (fun j _ => by
          apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
          intro v; simp only [ContinuousLinearMap.proj_apply, one_mul]
          exact norm_le_pi_norm v (σ j))
    _ = ‖(↑(∏ i, (multiIdx σ i).factorial) / ↑n.factorial : ℂ) •
          cauchyCoeffPolydisc f z (fun _ => R) (multiIdx σ)‖ := by
        rw [ContinuousMultilinearMap.norm_mkPiRing, mul_one]
    _ ≤ 1 * ‖cauchyCoeffPolydisc f z (fun _ => R) (multiIdx σ)‖ := by
        rw [norm_smul]; gcongr
        rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
        exact div_le_one_of_le₀ (Nat.cast_le.mpr (prod_factorial_multiIdx_le σ))
          (Nat.cast_nonneg _)
    _ = ‖cauchyCoeffPolydisc f z (fun _ => R) (multiIdx σ)‖ := one_mul _
    _ ≤ M / ∏ i, R ^ multiIdx σ i :=
        norm_cauchyCoeffPolydisc_le f z _ (fun _ => hR) M hM hf_bound _
    _ = M / R ^ n := by congr 1; rw [Finset.prod_pow_eq_pow_sum, multiIdx_sum]

end NormBound



/-- The product `∏ j, y (σ j)` equals the multi-index monomial `∏ i, y i ^ (multiIdx σ i)`. -/
private lemma prod_eq_multiIdx_pow {n d : ℕ} (σ : Fin n → Fin d) (y : Fin d → ℂ) :
    ∏ j : Fin n, y (σ j) = ∏ i : Fin d, y i ^ multiIdx σ i := by
  simp_rw [multiIdx]
  rw [← Finset.prod_fiberwise_of_maps_to (t := Finset.univ)
    (fun j _ => Finset.mem_univ (σ j)) (fun j => y (σ j))]
  apply Finset.prod_congr rfl; intro i _
  rw [Finset.prod_congr rfl (fun j hj => by rw [(Finset.mem_filter.mp hj).2]),
    Finset.prod_const]



/-- The multi-index of `Fin.cons i σ'` updates the count at `i`. -/
private lemma multiIdx_cons_eq {n d : ℕ} (i : Fin d) (σ' : Fin n → Fin d) :
    multiIdx (Fin.cons i σ') = Function.update (multiIdx σ') i (multiIdx σ' i + 1) := by
  ext j; simp only [multiIdx, Finset.card_filter]
  by_cases h : j = i
  · subst h; rw [Function.update_self, Fin.sum_univ_succ]
    simp [Fin.cons_zero, Fin.cons_succ]; ring
  · rw [Function.update_of_ne h, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Ne.symm h, ite_false]; simp [multiIdx]

/-- If `σ 0 = i`, then `multiIdx σ i ≥ 1`. -/
private lemma multiIdx_pos_at_zero {n d : ℕ} (σ : Fin (n + 1) → Fin d) :
    1 ≤ multiIdx σ (σ 0) :=
  Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

/-- Taking `Fin.tail` of `σ` with `multiIdx σ = α` and `σ 0 = i` gives
    `multiIdx (tail σ) = update α i (α i - 1)`. -/
private lemma tail_in_fiber {n d : ℕ} (α : Fin d → ℕ) (i : Fin d)
    (σ : Fin (n + 1) → Fin d) (hα : multiIdx σ = α) (h0 : σ 0 = i) :
    multiIdx (Fin.tail σ) = Function.update α i (α i - 1) := by
  have hk : multiIdx (Fin.cons (σ 0) (Fin.tail σ)) = α := by rwa [Fin.cons_self_tail]
  rw [multiIdx_cons_eq, h0] at hk
  ext j; by_cases hj : j = i
  · subst hj; rw [Function.update_self]
    have := congr_fun hk j; rw [Function.update_self] at this; omega
  · rw [Function.update_of_ne hj]
    have := congr_fun hk j; rw [Function.update_of_ne hj] at this; exact this

/-- Bijection between `{σ | multiIdx σ = α, σ 0 = i}` and
    `{σ' | multiIdx σ' = update α i (α i - 1)}` via `Fin.tail`/`Fin.cons`. -/
private lemma card_fiber_cons {n d : ℕ} (α : Fin d → ℕ) (i : Fin d) (hi : 1 ≤ α i) :
    ((univ.filter (fun σ : Fin (n + 1) → Fin d => multiIdx σ = α)).filter
      (fun σ => σ 0 = i)).card =
    (univ.filter (fun σ' : Fin n → Fin d =>
      multiIdx σ' = Function.update α i (α i - 1))).card := by
  apply Finset.card_bij (fun σ _ => Fin.tail σ)
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    exact tail_in_fiber α i σ hσ.1 hσ.2
  · intro σ₁ hσ₁ σ₂ hσ₂ heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ₁ hσ₂
    funext k; rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩
    · exact hσ₁.2.trans hσ₂.2.symm
    · exact congr_fun heq j
  · intro σ' hσ'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ' ⊢
    refine ⟨Fin.cons i σ', ⟨?_, ?_⟩, ?_⟩
    · rw [multiIdx_cons_eq, hσ']
      ext j; by_cases hj : j = i
      · subst hj; rw [Function.update_self, Function.update_self]; omega
      · rw [Function.update_of_ne hj, Function.update_of_ne hj]
    · simp [Fin.cons_zero]
    · exact funext (fun j => by simp [Fin.tail, Fin.cons_succ])

/-- Sum of an updated multi-index decreases by 1. -/
private lemma sum_update_pred {d n : ℕ} (α : Fin d → ℕ) (i : Fin d) (hi : 1 ≤ α i)
    (hα : ∑ j, α j = n + 1) :
    ∑ j, Function.update α i (α i - 1) j = n := by
  have h1 := Finset.sum_update_of_mem (Finset.mem_univ i) α (α i - 1)
  rw [h1]; have h2 := Finset.add_sum_erase univ α (Finset.mem_univ i)
  rw [Finset.sdiff_singleton_eq_erase] at *; omega

/-- Factoring out `α i` from the product of factorials after an update. -/
private lemma prod_factorial_update_mul {d : ℕ} (α : Fin d → ℕ) (i : Fin d) (hi : 1 ≤ α i) :
    α i * ∏ j : Fin d, (Function.update α i (α i - 1) j).factorial =
    ∏ j : Fin d, (α j).factorial := by
  have h1 : ∏ j, (Function.update α i (α i - 1) j).factorial =
      (α i - 1).factorial * ∏ j ∈ univ.erase i, (α j).factorial := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    exact congr_arg₂ _ (congr_arg _ (Function.update_self ..))
      (Finset.prod_congr rfl fun j hj => congr_arg _
        (Function.update_of_ne (Finset.ne_of_mem_erase hj) ..))
  rw [h1, ← mul_assoc, Nat.mul_factorial_pred (by omega),
    Finset.mul_prod_erase _ (fun j => (α j).factorial) (Finset.mem_univ i)]

/-- Each term in the fiber decomposition: for `σ 0 = i`, the fiber contributes `α i * n!`. -/
private lemma fiber_term_eq {n d : ℕ}
    (ih : ∀ (α : Fin d → ℕ), ∑ j, α j = n →
      (univ.filter (fun σ : Fin n → Fin d => multiIdx σ = α)).card *
        ∏ j, (α j).factorial = n.factorial)
    (α : Fin d → ℕ) (hα : ∑ j, α j = n + 1) (i : Fin d) :
    ((univ.filter (fun σ : Fin (n + 1) → Fin d => multiIdx σ = α)).filter
      (fun σ => σ 0 = i)).card * ∏ j, (α j).factorial = α i * n.factorial := by
  by_cases hi : α i = 0
  · have : ((univ.filter (fun σ : Fin (n + 1) → Fin d => multiIdx σ = α)).filter
        (fun σ => σ 0 = i)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro σ hσ h0
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      have := multiIdx_pos_at_zero σ; rw [h0, hσ, hi] at this; omega
    rw [this, zero_mul, hi, zero_mul]
  · have hi' : 1 ≤ α i := Nat.one_le_iff_ne_zero.mpr hi
    rw [card_fiber_cons α i hi', ← prod_factorial_update_mul α i hi', ← mul_assoc,
      mul_comm _ (α i), mul_assoc]
    congr 1
    exact ih _ (sum_update_pred α i hi' hα)

set_option maxHeartbeats 800000 in
/-- **Multinomial identity for fiber cardinality.**
    `|{σ : Fin n → Fin d | multiIdx σ = α}| * ∏ (α_i!) = n!`
    when `∑ α_i = n`. This is the key combinatorial fact for the diagonal identity. -/
private theorem card_fiber_mul_prod_factorial {d : ℕ} :
    ∀ (n : ℕ) (α : Fin d → ℕ) (_hα : ∑ i, α i = n),
    (univ.filter (fun σ : Fin n → Fin d => multiIdx σ = α)).card *
      ∏ i, (α i).factorial = n.factorial := by
  intro n; induction n with
  | zero =>
    intro α hα
    have hα0 : α = 0 := funext fun i => Finset.sum_eq_zero_iff.mp hα i (Finset.mem_univ i)
    subst hα0; simp only [Nat.factorial_zero, Finset.prod_const_one, mul_one, Pi.zero_apply]
    have : Finset.univ.filter (fun σ : Fin 0 → Fin d => multiIdx σ = 0) = Finset.univ := by
      apply Finset.filter_true_of_mem; intro σ _; ext i
      simp only [multiIdx, Pi.zero_apply, Finset.card_eq_zero]
      exact Finset.filter_eq_empty_iff.mpr (fun j => Fin.elim0 j)
    rw [this, Finset.card_univ]; simp
  | succ n ih =>
    intro α hα
    have h_partition :
        (univ.filter (fun σ : Fin (n + 1) → Fin d => multiIdx σ = α)).card =
        ∑ i : Fin d, ((univ.filter (fun σ : Fin (n + 1) → Fin d => multiIdx σ = α)).filter
          (fun σ => σ 0 = i)).card := by
      set s := univ.filter (fun σ : Fin (n + 1) → Fin d => multiIdx σ = α)
      have h := Finset.sum_card_fiberwise_eq_card_filter s univ (fun σ => σ 0)
      simp only [Finset.mem_univ, Finset.filter_true] at h
      exact h.symm
    rw [h_partition, Finset.sum_mul]
    have h_terms : ∀ i ∈ (univ : Finset (Fin d)),
        ((univ.filter (fun σ : Fin (n + 1) → Fin d => multiIdx σ = α)).filter
          (fun σ => σ 0 = i)).card * ∏ j, (α j).factorial = α i * n.factorial :=
      fun i _ => fiber_term_eq ih α hα i
    rw [Finset.sum_congr rfl h_terms, ← Finset.sum_mul, hα, Nat.factorial_succ]

/-- A finite sequence realizing a prescribed multi-index. -/
private lemma exists_multiIdx_eq
    {d : ℕ}
    (α : Fin d → ℕ) :
    ∃ σ : Fin (∑ i, α i) → Fin d, multiIdx σ = α := by
  let n := ∑ i, α i
  let fiber :=
    Finset.univ.filter (fun σ : Fin n → Fin d => multiIdx σ = α)
  have hcard :
      fiber.card * ∏ i, (α i).factorial = n.factorial :=
    card_fiber_mul_prod_factorial n α rfl
  have hcard_ne : fiber.card ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hcard
    exact Nat.factorial_ne_zero n hcard.symm
  obtain ⟨σ, hσ⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hcard_ne)
  exact ⟨σ, (Finset.mem_filter.mp hσ).2⟩

/-- A canonical sequence of coordinate labels whose multiplicities are `α`. -/
noncomputable def multiIndexEnumeration
    {d : ℕ}
    (α : Fin d → ℕ) :
    Fin (∑ i, α i) → Fin d :=
  Classical.choose (exists_multiIdx_eq α)

@[simp] theorem multiIdx_multiIndexEnumeration
    {d : ℕ}
    (α : Fin d → ℕ) :
    multiIdx (multiIndexEnumeration α) = α :=
  Classical.choose_spec (exists_multiIdx_eq α)

private lemma multiIdx_comp_perm
    {d n : ℕ}
    (σ : Fin n → Fin d)
    (ρ : Equiv.Perm (Fin n)) :
    multiIdx (σ ∘ ρ) = multiIdx σ := by
  ext i
  simp only [multiIdx, Function.comp_apply]
  let s := Finset.univ.filter (fun j : Fin n => σ (ρ j) = i)
  let t := Finset.univ.filter (fun j : Fin n => σ j = i)
  have hmap : s.map ρ.toEmbedding = t := by
    ext j
    simp only [s, t, Finset.mem_map, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact hl
    · intro hj
      exact ⟨ρ.symm j, by simpa using hj, by simp⟩
  change s.card = t.card
  rw [← hmap, Finset.card_map]

omit [CompleteSpace E] in
private lemma cauchyPowerSeriesPolydisc_coordinateDirections
    {d n : ℕ}
    (f : (Fin d → ℂ) → E)
    (z : Fin d → ℂ)
    (r : Fin d → ℝ)
    (σ : Fin n → Fin d) :
    cauchyPowerSeriesPolydisc f z r n
        (fun j i => if i = σ j then 1 else 0) =
      ((↑(∏ i : Fin d, (multiIdx σ i).factorial) /
          ↑n.factorial : ℂ) •
        cauchyCoeffPolydisc f z r (multiIdx σ)) := by
  classical
  simp only [cauchyPowerSeriesPolydisc,
    ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiRing_apply,
    ContinuousLinearMap.proj_apply]
  rw [Finset.sum_eq_single σ]
  · simp
  · intro τ _ hτσ
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hτσ
    have hcoord :
        (if τ j = σ j then (1 : ℂ) else 0) = 0 :=
      if_neg hj
    rw [Finset.prod_eq_zero (Finset.mem_univ j) hcoord, zero_smul]
  · simp



/-- If a closed polydisc of radius R is inside an open set, there exists a slightly larger
    closed polydisc that is still inside the open set. -/
private lemma exists_larger_polydisc_in_open {k : ℕ} {z : Fin k → ℂ} {R : ℝ}
    {U : Set (Fin k → ℂ)} (hU : IsOpen U) (hRU : closedPolydisc z (fun _ => R) ⊆ U)
    (hR : 0 < R) :
    ∃ Rw > R, closedPolydisc z (fun _ => Rw) ⊆ U := by
  obtain ⟨δ, hδ, hth⟩ := isCompact_closedPolydisc.exists_thickening_subset_open hU hRU
  refine ⟨R + δ / 2, by linarith, fun w hw => hth ?_⟩
  -- Show w ∈ Metric.thickening δ (closedPolydisc z (fun _ => R))
  rw [Metric.mem_thickening_iff]
  -- Construct nearby point via uniform scaling: y = z + c*(w-z) where c = R/(R+δ/2)
  have hRd_pos : (0 : ℝ) < R + δ / 2 := by linarith
  set c : ℝ := R / (R + δ / 2) with hc_def
  have hc_pos : 0 < c := div_pos hR hRd_pos
  have hc_le : c ≤ 1 := div_le_one_of_le₀ (by linarith) hRd_pos.le
  refine ⟨fun i => z i + ↑c * (w i - z i), fun i => ?_, ?_⟩
  · -- y i ∈ Metric.closedBall (z i) R
    simp only [Metric.mem_closedBall, dist_eq_norm]
    rw [show z i + ↑c * (w i - z i) - z i = (↑c : ℂ) * (w i - z i) from by ring,
      norm_mul, Complex.norm_of_nonneg hc_pos.le]
    calc c * ‖w i - z i‖ ≤ c * (R + δ / 2) := by
          gcongr; rw [← dist_eq_norm]; exact hw i
      _ = R := div_mul_cancel₀ R hRd_pos.ne'
  · -- dist w y < δ
    calc dist w (fun i => z i + ↑c * (w i - z i))
        ≤ δ / 2 := by
          apply (dist_pi_le_iff (by linarith : (0 : ℝ) ≤ δ / 2)).mpr; intro i
          simp only [dist_eq_norm]
          rw [show w i - (z i + ↑c * (w i - z i)) = ((1 : ℂ) - ↑c) * (w i - z i) from by ring,
            norm_mul, show ‖(1 : ℂ) - (↑c : ℂ)‖ = 1 - c from by
              rw [show (1 : ℂ) - (↑c : ℂ) = ↑((1 : ℝ) - c) from by push_cast; ring,
                Complex.norm_of_nonneg (by linarith)]]
          calc (1 - c) * ‖w i - z i‖ ≤ (1 - c) * (R + δ / 2) := by
                gcongr
                · linarith
                · rw [← dist_eq_norm]; exact hw i
            _ = δ / 2 := by
                rw [hc_def, show 1 - R / (R + δ / 2) = (δ / 2) / (R + δ / 2) from by
                  field_simp; ring, div_mul_cancel₀ _ hRd_pos.ne']
      _ < δ := by linarith



set_option maxHeartbeats 800000 in
/-- Summability of the multi-index geometric product: if each `q i ∈ [0, 1)`, then
    `∑_{α : Fin n → ℕ} ∏ i, q i ^ α i` converges. -/
private lemma summable_geometric_piNat : ∀ (n : ℕ) (q : Fin n → ℝ),
    (∀ i, 0 ≤ q i) → (∀ i, q i < 1) →
    Summable (fun α : Fin n → ℕ => ∏ i : Fin n, q i ^ α i) := by
  intro n; induction n with
  | zero =>
    intro q _ _
    exact (hasSum_fintype _).summable
  | succ n ih =>
    intro q hq hq1
    set qL := q (Fin.last n)
    set q' : Fin n → ℝ := fun j => q (Fin.castSucc j)
    have h_inner : Summable (fun α' : Fin n → ℕ => ∏ j, q' j ^ α' j) :=
      ih q' (fun j => hq _) (fun j => hq1 _)
    have h_outer : Summable (fun k : ℕ => qL ^ k) :=
      summable_geometric_of_lt_one (hq (Fin.last n)) (hq1 (Fin.last n))
    have h_prod : Summable (fun p : ℕ × (Fin n → ℕ) => qL ^ p.1 * ∏ j, q' j ^ p.2 j) :=
      @Summable.mul_of_nonneg ℕ (Fin n → ℕ) (fun k => qL ^ k)
        (fun α' => ∏ j, q' j ^ α' j) h_outer h_inner
        (fun k => pow_nonneg (hq _) _)
        (fun α' => Finset.prod_nonneg (fun j _ => pow_nonneg (hq _) _))
    refine ((Equiv.summable_iff (Fin.snocEquiv (fun _ => ℕ)).symm).mpr h_prod).congr (fun α => ?_)
    simp only [Function.comp_def, Fin.snocEquiv, Equiv.coe_fn_symm_mk, qL, q',
      Fin.prod_univ_castSucc, mul_comm]; rfl



set_option linter.unusedVariables false in
set_option maxHeartbeats 1600000 in
/-- **Multi-index Cauchy expansion.**
    The sum of `y^α • cauchyCoeffPolydisc f z R α` over all multi-indices `α` converges
    to `f(z + y)`. This is proved by induction on the number of variables, using the
    one-variable Cauchy power series (`hasSum_two_pi_I_cauchyPowerSeries_integral`) and
    sum-integral exchange.

    The hypotheses require `f` to be separately differentiable and continuous on a
    closed polydisc of radius `Rw > R` (the "working radius"), providing room for the
    Leibniz integral rule in the inductive step. -/
private lemma hasSum_multiIdx_cauchyCoeff :
    ∀ (m : ℕ) (f : (Fin (m + 1) → ℂ) → E) (z : Fin (m + 1) → ℂ) (R Rw : ℝ) (hR : 0 < R)
    (hRw : R < Rw)
    (hf_sep : ∀ w ∈ closedPolydisc z (fun _ => Rw),
      ∀ i, DifferentiableAt ℂ (fun t => f (Function.update w i t)) (w i))
    (hf_cont : ContinuousOn f (closedPolydisc z (fun _ => Rw)))
    (y : Fin (m + 1) → ℂ) (hy : ∀ i, ‖y i‖ < R),
    HasSum (fun α : Fin (m + 1) → ℕ =>
      (∏ i, (y i) ^ (α i)) • cauchyCoeffPolydisc f z (fun _ => R) α)
      (f (z + y)) := by
  intro m; induction m with
  | zero =>
    -- Base case: Fin (0+1) ≅ Fin 1 (one variable). Connect to 1D Cauchy power series.
    intro f z R Rw hR hRw hf_sep hf_cont y hy
    -- Provide Subsingleton instance for Fin (0 + 1)
    haveI : Subsingleton (Fin (0 + 1)) := ⟨fun a b => Fin.ext (by omega)⟩
    -- Define 1D function g(t) = f(fun _ => t)
    set g : ℂ → E := fun t => f (fun _ => t) with hg_def
    -- g is differentiable on closedBall (z 0) R
    have hg_diff : DifferentiableOn ℂ g (Metric.closedBall (z 0) R) := by
      intro t ht
      have hw : (fun _ : Fin (0 + 1) => t) ∈ closedPolydisc z (fun _ => Rw) := by
        intro i; have hi : i = 0 := Subsingleton.elim i 0; subst hi
        exact Metric.closedBall_subset_closedBall hRw.le ht
      have h := hf_sep _ hw 0
      have key : (fun t₁ => f (Function.update (fun _ : Fin (0 + 1) => t) 0 t₁)) = g := by
        ext t₁; congr 1; ext i; simp [Function.update, Subsingleton.elim i (0 : Fin (0 + 1))]
      rw [key] at h; exact h.differentiableWithinAt
    -- g is circle integrable
    have hg_ci : CircleIntegrable g (z 0) R :=
      (hg_diff.continuousOn.mono Metric.sphere_subset_closedBall).circleIntegrable hR.le
    -- 1D HasSum for the Cauchy power series
    have h1d := hasSum_cauchyPowerSeries_integral hg_ci (hy 0)
    -- Sum value = f(z+y) by 1D Cauchy integral formula
    have hcauchy := DifferentiableOn.circleIntegral_sub_inv_smul hg_diff
      (Metric.mem_ball.mpr (show dist (z 0 + y 0) (z 0) < R by
        simp only [dist_eq_norm, add_sub_cancel_left]; exact hy 0))
    rw [hcauchy, inv_smul_smul₀ (by exact mul_ne_zero (mul_ne_zero
      two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero)] at h1d
    -- g(z 0 + y 0) = f(z + y)
    have hval : g (z 0 + y 0) = f (z + y) := by
      simp only [hg_def]; congr 1; ext i; simp [Pi.add_apply, Subsingleton.elim i 0]
    rw [hval] at h1d
    -- Term equality: 1D cauchyPowerSeries term = multi-index term
    have hterm : ∀ n, cauchyPowerSeries g (z 0) R n (fun _ => y 0) =
        (∏ i : Fin (0 + 1), (y i) ^ n) •
          cauchyCoeffPolydisc f z (fun _ => R) (fun _ => n) := by
      intro n
      simp only [cauchyPowerSeries, cauchyCoeffPolydisc, ContinuousMultilinearMap.mkPiRing_apply,
        iteratedCircleIntegral, Finset.prod_const, Finset.card_fin]
      rw [Fintype.prod_subsingleton _ (0 : Fin (0 + 1)), pow_one,
        show z (Fin.last 0) = z 0 from congr_arg z (Subsingleton.elim _ _)]
      congr 1; congr 1; congr 1; funext t
      rw [Fintype.prod_subsingleton _ (0 : Fin (0 + 1)),
        show (0 : Fin (0 + 1)) = Fin.last 0 from rfl, Fin.snoc_last,
        smul_smul, ← pow_succ]
      congr 2
    simp_rw [hterm] at h1d
    -- Transport via equiv (Fin (0+1) → ℕ) ≃ ℕ
    haveI : Unique (Fin (0 + 1)) := ⟨⟨0⟩, fun i => Subsingleton.elim i 0⟩
    set e := (Equiv.funUnique (Fin (0 + 1)) ℕ).symm
    rw [← Equiv.hasSum_iff e]
    convert h1d using 1
  | succ m ih =>
    intro f z R Rw hR hRw hf_sep hf_cont y hy
    -- Setup: split variables into first (m+1) and last
    set z' : Fin (m + 1) → ℂ := z ∘ Fin.castSucc with hz'_def
    set y' : Fin (m + 1) → ℂ := y ∘ Fin.castSucc with hy'_def
    set zL := z (Fin.last (m + 1)) with hzL_def
    set yL := y (Fin.last (m + 1)) with hyL_def
    -- Working radius for IH: Rw' = (R + Rw) / 2, sits strictly between R and Rw
    set Rw' := (R + Rw) / 2 with hRw'_def
    have hRw'_gt : R < Rw' := by linarith
    have hRw'_lt : Rw' < Rw := by linarith
    -- g_k: Cauchy coefficient in the last variable, as a function of the first (m+1) variables
    set gk : ℕ → (Fin (m + 1) → ℂ) → E := fun k w' =>
      (2 * ↑Real.pi * I)⁻¹ •
        ∮ t in C(zL, R), (t - zL)⁻¹ ^ (k + 1) • f (Fin.snoc w' t) with hgk_def
    -- h: restriction of f to the last variable with first (m+1) variables fixed at z'+y'
    set h : ℂ → E := fun t => f (Fin.snoc (z' + y') t) with hh_def
    -- h is differentiable on closedBall zL R
    have hh_diff : DifferentiableOn ℂ h (Metric.closedBall zL R) := by
      intro t ht
      have hw : Fin.snoc (z' + y') t ∈ closedPolydisc z (fun _ => Rw) := by
        intro i; refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [Fin.snoc_last]; exact Metric.closedBall_subset_closedBall hRw.le ht
        · simp only [Fin.snoc_castSucc, Pi.add_apply, Metric.mem_closedBall, dist_eq_norm]
          rw [show z' j + y' j - z (Fin.castSucc j) = y' j from by
            simp [hz'_def, Function.comp_apply, add_sub_cancel_left]]
          exact le_trans (hy (Fin.castSucc j)).le hRw.le
      have hsep := hf_sep _ hw (Fin.last (m + 1))
      have hkey : (fun s => f (Function.update (Fin.snoc (z' + y') t) (Fin.last (m + 1)) s)) =
          h := by
        ext s; simp only [hh_def]; congr 1; ext i; refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [Fin.snoc_last]
        · rw [Function.update_apply, if_neg (Fin.castSucc_lt_last j).ne,
            Fin.snoc_castSucc, Fin.snoc_castSucc]
      rw [hkey] at hsep; simp only [Fin.snoc_last] at hsep
      exact hsep.differentiableWithinAt
    -- h is circle integrable
    have hh_ci : CircleIntegrable h zL R :=
      (hh_diff.continuousOn.mono Metric.sphere_subset_closedBall).circleIntegrable hR.le
    -- 1D Cauchy HasSum
    have h1d := hasSum_cauchyPowerSeries_integral hh_ci (hy (Fin.last (m + 1)))
    -- Cauchy integral formula for h
    have hcauchy := DifferentiableOn.circleIntegral_sub_inv_smul hh_diff
      (Metric.mem_ball.mpr (show dist (zL + yL) zL < R by
        rw [dist_eq_norm, add_sub_cancel_left]; exact hy (Fin.last (m + 1))))
    rw [hcauchy, inv_smul_smul₀ (mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero)] at h1d
    -- h(zL + yL) = f(z + y)
    have hval : h (zL + yL) = f (z + y) := by
      simp only [hh_def]; congr 1; ext i; refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [Fin.snoc_last, Pi.add_apply, hzL_def, hyL_def]
      · simp [Fin.snoc_castSucc, Pi.add_apply, hz'_def, hy'_def, Function.comp]
    rw [hval] at h1d
    -- Term equality: cauchyPowerSeries h zL R k applied to yL = yL^k • gk k (z'+y')
    have hterm : ∀ k, cauchyPowerSeries h zL R k (fun _ => yL) =
        yL ^ k • gk k (z' + y') := by
      intro k
      simp only [cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply,
        Finset.prod_const, Finset.card_fin, hgk_def, hh_def]
      simp_rw [smul_smul, pow_succ]
    simp_rw [← hyL_def, hterm] at h1d
    -- h1d : HasSum (fun k => yL^k • gk k (z'+y')) (f(z+y))
    -- g_k satisfies IH hypotheses on the working radius Rw'
    -- Helper: snoc maps closedPolydisc z' Rw' to closedPolydisc z Rw (for circle integrals)
    have hsnoc_mem_Rw : ∀ w' ∈ closedPolydisc z' (fun _ => Rw'), ∀ θ,
        Fin.snoc w' (circleMap zL R θ) ∈ closedPolydisc z (fun _ => Rw) := by
      intro w' hw' θ i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last, Metric.mem_closedBall, dist_eq_norm]
        rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hR]
        exact hRw.le
      · simp only [Fin.snoc_castSucc, Metric.mem_closedBall]
        exact le_trans (Metric.mem_closedBall.mp (hw' j)) hRw'_lt.le
    -- Get a uniform bound M for ‖f‖ on the compact polydisc closedPolydisc z Rw
    have hRw_pos : (0 : ℝ) < Rw := by linarith
    obtain ⟨M, hM_nn, hM⟩ : ∃ M, 0 ≤ M ∧ ∀ w ∈ closedPolydisc z (fun _ => Rw), ‖f w‖ ≤ M := by
      obtain ⟨x, _, hxM⟩ := isCompact_closedPolydisc.exists_isMaxOn
        ⟨z, center_mem_closedPolydisc (fun _ => hRw_pos.le)⟩ hf_cont.norm
      exact ⟨‖f x‖, norm_nonneg _, fun w hw => hxM hw⟩
    have hgk_sep : ∀ k, ∀ w' ∈ closedPolydisc z' (fun _ => Rw'),
        ∀ i, DifferentiableAt ℂ (fun t => gk k (Function.update w' i t)) (w' i) := by
      intro k w₀ hw₀ ii
      -- Setup: ε = (Rw - Rw')/2, slack for Cauchy estimate
      set ε := (Rw - Rw') / 2 with hε_def
      have hε_pos : 0 < ε := by linarith
      set j := Fin.castSucc ii with hj_def
      -- Key identity: snoc (update w₀ ii t) s = update (snoc w₀ s) j t
      have hkey : ∀ (s t : ℂ), Fin.snoc (Function.update w₀ ii t) s =
          Function.update (β := fun _ => ℂ) (Fin.snoc w₀ s) j t := by
        intro s t; simp only [hj_def]; exact Fin.snoc_update (α := fun _ => ℂ) s w₀ ii t
      -- Membership: for t with dist < 2ε from w₀ ii, update ∈ closedPolydisc z Rw
      have hmem_wide : ∀ θ : ℝ, ∀ t, dist t (w₀ ii) < 2 * ε →
          Function.update (Fin.snoc w₀ (circleMap zL R θ)) j t ∈
            closedPolydisc z (fun _ => Rw) := by
        intro θ t ht ℓ; refine Fin.lastCases ?_ (fun ℓ' => ?_) ℓ
        · rw [Function.update_of_ne (Fin.castSucc_lt_last ii).ne', Fin.snoc_last,
            Metric.mem_closedBall, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero,
            abs_of_pos hR]; exact hRw.le
        · by_cases h : ℓ' = ii
          · have hℓ : Fin.castSucc ℓ' = j := by rw [h]
            rw [hℓ, Function.update_self, Metric.mem_closedBall]
            have h1 : dist (w₀ ii) (z j) ≤ Rw' := hw₀ ii
            linarith [dist_triangle t (w₀ ii) (z j)]
          · rw [Function.update_of_ne (Fin.castSucc_injective _ |>.ne h), Fin.snoc_castSucc]
            exact le_trans (hw₀ ℓ') hRw'_lt.le
      -- Membership for ball(w₀ ii, ε)
      have hmem : ∀ θ : ℝ, ∀ t ∈ Metric.ball (w₀ ii) ε,
          Function.update (Fin.snoc w₀ (circleMap zL R θ)) j t ∈
            closedPolydisc z (fun _ => Rw) :=
        fun θ t ht => hmem_wide θ t (by linarith [Metric.mem_ball.mp ht])
      -- Inner function: g_θ(s) = f(update (snoc w₀ (circleMap θ)) j s)
      -- DifferentiableAt for g_θ at points near w₀ ii
      have hdiff : ∀ θ : ℝ, ∀ t, dist t (w₀ ii) < 2 * ε →
          DifferentiableAt ℂ
            (fun s => f (Function.update (Fin.snoc w₀ (circleMap zL R θ)) j s)) t := by
        intro θ t ht
        have h := hf_sep _ (hmem_wide θ t ht) j
        simp only [Function.update_idem, Function.update_self] at h; exact h
      -- ContinuousOn for g_θ on closedBall(x, ε) when x ∈ ball(w₀ ii, ε)
      have hcont_gθ : ∀ θ : ℝ, ∀ x ∈ Metric.ball (w₀ ii) ε,
          ContinuousOn
            (fun s => f (Function.update (Fin.snoc w₀ (circleMap zL R θ)) j s))
            (Metric.closedBall x ε) := by
        intro θ x hx
        have hupdate_cont : Continuous
            (fun s => Function.update (β := fun _ => ℂ) (Fin.snoc w₀ (circleMap zL R θ)) j s) :=
          continuous_pi (fun ℓ => by
            by_cases h : ℓ = j
            · subst h; simp [Function.update_self]; exact continuous_id
            · simp [Function.update_of_ne h]; exact continuous_const)
        apply hf_cont.comp hupdate_cont.continuousOn
        intro s hs
        exact hmem_wide θ s (by
          linarith [Metric.mem_closedBall.mp hs, Metric.mem_ball.mp hx,
                    dist_triangle s x (w₀ ii)])
      -- DiffContOnCl for g_θ on ball(x, ε) when x ∈ ball(w₀ ii, ε)
      have hdiffcont : ∀ θ : ℝ, ∀ x ∈ Metric.ball (w₀ ii) ε,
          DiffContOnCl ℂ
            (fun s => f (Function.update (Fin.snoc w₀ (circleMap zL R θ)) j s))
            (Metric.ball x ε) := by
        intro θ x hx
        refine ⟨fun s hs => (hdiff θ s ?_).differentiableWithinAt, ?_⟩
        · linarith [Metric.mem_ball.mp hs, Metric.mem_ball.mp hx, dist_triangle s x (w₀ ii)]
        · rw [closure_ball x hε_pos.ne']; exact hcont_gθ θ x hx
      -- Cauchy estimate: ‖deriv g_θ x‖ ≤ M / ε for x ∈ ball(w₀ ii, ε)
      have hderiv_bound : ∀ θ : ℝ, ∀ x ∈ Metric.ball (w₀ ii) ε,
          ‖deriv (fun s => f (Function.update (Fin.snoc w₀ (circleMap zL R θ)) j s)) x‖ ≤
            M / ε := by
        intro θ x hx
        apply norm_deriv_le_of_forall_mem_sphere_norm_le hε_pos (hdiffcont θ x hx)
        intro s hs
        apply hM
        exact hmem_wide θ s (by
          rw [Metric.mem_sphere] at hs
          linarith [Metric.mem_ball.mp hx, dist_triangle s x (w₀ ii)])
      -- Define F(x, θ) and F'(x, θ) for the parametric integral theorem
      set F : ℂ → ℝ → E := fun x θ =>
        deriv (circleMap zL R) θ • ((circleMap zL R θ - zL)⁻¹ ^ (k + 1) •
          f (Function.update (Fin.snoc w₀ (circleMap zL R θ)) j x))
      set F' : ℂ → ℝ → E := fun x θ =>
        deriv (circleMap zL R) θ • ((circleMap zL R θ - zL)⁻¹ ^ (k + 1) •
          deriv (fun s => f (Function.update (Fin.snoc w₀ (circleMap zL R θ)) j s)) x)
      -- gk k (update w₀ ii x) = (2πi)⁻¹ • ∫ θ in 0..2π, F x θ
      have hgk_eq : ∀ x, gk k (Function.update w₀ ii x) =
          (2 * ↑Real.pi * I)⁻¹ • ∫ θ in (0:ℝ)..(2 * Real.pi), F x θ := by
        intro x; simp only [hgk_def, circleIntegral, F]; congr 2; ext θ
        rw [show Fin.snoc (Function.update w₀ ii x) (circleMap zL R θ) =
          Function.update (β := fun _ => ℂ) (Fin.snoc w₀ (circleMap zL R θ)) j x from hkey ..]
      -- HasDerivAt for each θ at all x ∈ ball(w₀ ii, ε)
      have h_hasderiv : ∀ θ : ℝ, ∀ x ∈ Metric.ball (w₀ ii) ε,
          HasDerivAt (F · θ) (F' x θ) x := by
        intro θ x hx
        exact ((hdiff θ x (by linarith [Metric.mem_ball.mp hx])).hasDerivAt.const_smul _).const_smul _
      -- Norm bound on F'
      have h_norm_F' : ∀ θ : ℝ, ∀ x ∈ Metric.ball (w₀ ii) ε, ‖F' x θ‖ ≤
          R * R⁻¹ ^ (k + 1) * (M / ε) := by
        intro θ x hx
        simp only [F', norm_smul, norm_pow, norm_inv]
        calc ‖deriv (circleMap zL R) θ‖ * (‖circleMap zL R θ - zL‖⁻¹ ^ (k + 1) *
              ‖deriv (fun s => f (Function.update (Fin.snoc w₀ (circleMap zL R θ)) j s)) x‖)
            ≤ R * (R⁻¹ ^ (k + 1) * (M / ε)) := by
              apply mul_le_mul _ _ (by positivity) (by positivity)
              · rw [deriv_circleMap, norm_mul, mul_comm]
                simp [circleMap, abs_of_pos hR]
              · apply mul_le_mul _ (hderiv_bound θ x hx) (norm_nonneg _) (by positivity)
                apply pow_le_pow_left₀ (by positivity)
                rw [circleMap_sub_center]; simp [circleMap, abs_of_pos hR]
          _ = R * R⁻¹ ^ (k + 1) * (M / ε) := by ring
      -- Continuity of F x in θ (for measurability)
      have hF_cont : ∀ x ∈ Metric.ball (w₀ ii) ε, Continuous (F x) := by
        intro x hx
        apply Continuous.smul (by rw [show deriv (circleMap zL R) = fun θ => circleMap 0 R θ * I
          from funext (deriv_circleMap zL R)]; exact (continuous_circleMap 0 R).mul continuous_const)
        apply Continuous.smul
          (((continuous_circleMap zL R).sub continuous_const).inv₀
            (fun θ => norm_ne_zero_iff.mp (by rw [circleMap_sub_center]; simp [circleMap]; exact hR.ne'))
            |>.pow _)
        exact hf_cont.comp_continuous
          (continuous_pi (fun ℓ => by
            by_cases h : ℓ = j
            · subst h; simp [Function.update_self]; exact continuous_const
            · simp only [Function.update_of_ne h]
              refine Fin.lastCases ?_ (fun ℓ' => ?_) ℓ
              · simp only [Fin.snoc_last]; exact continuous_circleMap zL R
              · simp only [Fin.snoc_castSucc]; exact continuous_const))
          (fun θ => hmem θ x hx)
      -- F'(w₀ ii) is AE strongly measurable: it's a pointwise limit of continuous
      -- difference quotients h_n⁻¹ • (F(w₀ ii + h_n) - F(w₀ ii)) where h_n → 0
      have hF'_meas : MeasureTheory.AEStronglyMeasurable (F' (w₀ ii))
          (MeasureTheory.Measure.restrict MeasureTheory.MeasureSpace.volume
            (Set.uIoc 0 (2 * Real.pi))) := by
        -- Sequence h_n = ε/2/(n+1) → 0 with h_n ≠ 0 and w₀ ii + h_n ∈ ball(w₀ ii, ε)
        set seq : ℕ → ℂ := fun n => ↑(ε / 2 / ((n : ℝ) + 1)) with hseq_def
        have hseq_mem : ∀ n, w₀ ii + seq n ∈ Metric.ball (w₀ ii) ε := by
          intro n; rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos (by positivity)]
          nlinarith [div_mul_cancel₀ (ε / 2) (show (0 : ℝ) < (n : ℝ) + 1 by positivity).ne']
        have hseq_real : Filter.Tendsto (fun n : ℕ => ε / 2 / ((n : ℝ) + 1))
            Filter.atTop (nhds 0) := by
          have h1 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) :=
            tendsto_inv_atTop_zero.comp
              (Filter.tendsto_atTop_add_const_right Filter.atTop 1
                (tendsto_natCast_atTop_atTop (R := ℝ)))
          have h2 : Filter.Tendsto (fun n : ℕ => ε / 2 * ((n : ℝ) + 1)⁻¹)
              Filter.atTop (nhds 0) := by simpa using tendsto_const_nhds.mul h1
          exact h2.congr (fun n => by ring)
        have hseq_tendsto : Filter.Tendsto seq Filter.atTop (nhdsWithin 0 {0}ᶜ) :=
          Filter.tendsto_inf.mpr ⟨by
            rw [show (0 : ℂ) = ↑(0 : ℝ) from Complex.ofReal_zero.symm]
            exact (Complex.continuous_ofReal.tendsto 0).comp hseq_real,
            Filter.tendsto_principal.mpr (Filter.Eventually.of_forall fun n =>
              Set.mem_compl_singleton_iff.mpr
                (Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))))⟩
        exact aestronglyMeasurable_of_tendsto_ae (u := Filter.atTop)
          (f := fun n θ => (seq n)⁻¹ • (F (w₀ ii + seq n) θ - F (w₀ ii) θ))
          (fun n => ((hF_cont _ (hseq_mem n)).sub
            (hF_cont _ (Metric.mem_ball_self hε_pos))).aestronglyMeasurable.const_smul _
            |>.restrict)
          (Filter.Eventually.of_forall fun θ =>
            (h_hasderiv θ (w₀ ii) (Metric.mem_ball_self hε_pos)).tendsto_slope_zero.comp
              hseq_tendsto)
      -- Apply intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      have h_result :=
        intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
          (F := F) (F' := F') (x₀ := w₀ ii) (s := Metric.ball (w₀ ii) ε)
          (bound := fun _ => R * R⁻¹ ^ (k + 1) * (M / ε))
          (a := 0) (b := 2 * Real.pi)
          (Metric.ball_mem_nhds _ hε_pos)
          (Filter.eventually_of_mem (Metric.ball_mem_nhds _ hε_pos) fun x hx =>
            (hF_cont x hx).aestronglyMeasurable.restrict)
          ((hF_cont _ (Metric.mem_ball_self hε_pos)).intervalIntegrable 0 (2 * Real.pi))
          hF'_meas
          (Filter.Eventually.of_forall fun θ _ x hx => h_norm_F' θ x hx)
          intervalIntegrable_const
          (Filter.Eventually.of_forall fun θ _ x hx => h_hasderiv θ x hx)
      -- Extract HasDerivAt and compose with (2πi)⁻¹ scalar
      exact (h_result.2.const_smul ((2 * (Real.pi : ℂ) * I)⁻¹)).differentiableAt
        |>.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => (hgk_eq x))
    have hgk_cont : ∀ k, ContinuousOn (gk k) (closedPolydisc z' (fun _ => Rw')) := by
      intro k
      simp only [hgk_def]
      apply ContinuousOn.const_smul
      -- Unfold ∮ to interval integral for dominated convergence
      show ContinuousOn (fun w' => ∫ θ in (0:ℝ)..(2 * Real.pi),
        deriv (circleMap zL R) θ •
          ((circleMap zL R θ - zL)⁻¹ ^ (k + 1) • f (Fin.snoc w' (circleMap zL R θ))))
        (closedPolydisc z' (fun _ => Rw'))
      -- Continuity helpers for the integrand
      have hcircle_ne : ∀ θ, circleMap zL R θ - zL ≠ 0 := fun θ =>
        norm_ne_zero_iff.mp (by
          rw [circleMap_sub_center]; simp [circleMap]; exact hR.ne')
      have hcont_deriv : Continuous (deriv (circleMap zL R)) := by
        rw [show deriv (circleMap zL R) = fun θ => circleMap 0 R θ * I from
          funext (deriv_circleMap zL R)]
        exact (continuous_circleMap 0 R).mul continuous_const
      have hcont_inv : Continuous (fun θ => (circleMap zL R θ - zL)⁻¹ ^ (k + 1)) :=
        (((continuous_circleMap zL R).sub continuous_const).inv₀ hcircle_ne).pow _
      have hcont_f_snoc : ∀ w' ∈ closedPolydisc z' (fun _ => Rw'), Continuous
          (fun θ => f (Fin.snoc w' (circleMap zL R θ))) := fun w' hw' =>
        hf_cont.comp_continuous
          (continuous_pi (fun i => Fin.lastCases
            (by simp only [Fin.snoc_last]; exact continuous_circleMap zL R)
            (fun j => by simp only [Fin.snoc_castSucc]; exact continuous_const) i))
          (fun θ => hsnoc_mem_Rw w' hw' θ)
      -- Apply dominated convergence at each point
      intro w₀ hw₀
      apply intervalIntegral.continuousWithinAt_of_dominated_interval
      · -- 1. AE measurability
        apply Filter.eventually_of_mem self_mem_nhdsWithin
        intro w' hw'
        exact (hcont_deriv.smul (hcont_inv.smul (hcont_f_snoc w' hw'))).aestronglyMeasurable.restrict
      · -- 2. Uniform norm bound
        apply Filter.eventually_of_mem self_mem_nhdsWithin
        intro w' hw'
        apply Filter.Eventually.of_forall
        intro θ _
        rw [norm_smul, norm_smul, norm_pow, norm_inv]
        calc ‖deriv (circleMap zL R) θ‖ * (‖circleMap zL R θ - zL‖⁻¹ ^ (k + 1) *
              ‖f (Fin.snoc w' (circleMap zL R θ))‖)
            ≤ R * (R⁻¹ ^ (k + 1) * M) := by
              apply mul_le_mul _ _ (by positivity) (by positivity)
              · rw [deriv_circleMap, norm_mul, mul_comm]
                simp [circleMap, abs_of_pos hR]
              · apply mul_le_mul _ (hM _ (hsnoc_mem_Rw w' hw' θ)) (norm_nonneg _) (by positivity)
                apply pow_le_pow_left₀ (by positivity)
                rw [circleMap_sub_center]; simp [circleMap, abs_of_pos hR]
          _ = R * R⁻¹ ^ (k + 1) * M := by ring
      · -- 3. Bound is interval integrable
        exact intervalIntegrable_const (by exact ENNReal.coe_ne_top)
      · -- 4. Continuity in w' for each θ
        apply Filter.Eventually.of_forall
        intro θ _
        apply ContinuousWithinAt.smul continuousWithinAt_const
        apply ContinuousWithinAt.smul continuousWithinAt_const
        exact (hf_cont.comp
          (continuous_pi (fun i => Fin.lastCases
            (by simp only [Fin.snoc_last]; exact continuous_const)
            (fun j => by simp only [Fin.snoc_castSucc]; exact continuous_apply j) i)).continuousOn
          (fun w' hw' => hsnoc_mem_Rw w' hw' θ)).continuousWithinAt hw₀
    -- Apply IH for each k
    have hIH : ∀ k, HasSum (fun α' : Fin (m + 1) → ℕ =>
        (∏ i, (y' i) ^ (α' i)) • cauchyCoeffPolydisc (gk k) z' (fun _ => R) α')
        (gk k (z' + y')) :=
      fun k => ih (gk k) z' R Rw' hR hRw'_gt (hgk_sep k) (hgk_cont k) y'
        (fun i => hy (Fin.castSucc i))
    
    set_option maxHeartbeats 400000 in
    have hcoeff : ∀ k (α' : Fin (m + 1) → ℕ),
        cauchyCoeffPolydisc (gk k) z' (fun _ => R) α' =
        cauchyCoeffPolydisc f z (fun _ => R) (Fin.snoc α' k) := by
      intro k α'
      simp only [cauchyCoeffPolydisc]
      -- Step 1: Unfold gk, factor (2πi)⁻¹ out, push prod inside integral
      simp_rw [hgk_def, smul_comm (∏ j : Fin (m + 1), _) ((2 * ↑Real.pi * I)⁻¹)]
      rw [iteratedCircleIntegral_smul, ← mul_smul, ← pow_succ]
      simp_rw [← circleIntegral.integral_smul]
      -- Both sides: (2πi)⁻¹^(m+2) • ICI(m+1, ..., z', R)
      -- Step 2: Unfold ICI(m+2) on the RHS and match
      congr 1
      -- Unfold ICI(m+1+1) to ICI(m+1, ∮ ...(snoc w' t)...)
      conv_rhs => rw [iteratedCircleIntegral_succ]
      -- Now both sides are ICI(m+1, ...) with z'=z∘castSucc, R=R definitionally
      -- Match the integrands pointwise
      congr 1; ext w'
      refine circleIntegral.integral_congr hR.le (fun t _ => ?_)
      -- LHS: (∏ i, (w' i - z' i)⁻¹^(α' i+1)) • (t - zL)⁻¹^(k+1) • f(snoc w' t)
      -- RHS: (∏ i, (snoc w' t i - z i)⁻¹^(snoc α' k i + 1)) • f(snoc w' t)
      rw [smul_smul]; congr 1; symm
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rfl
    -- Product factorization
    have hprod : ∀ k (α' : Fin (m + 1) → ℕ),
        yL ^ k * (∏ i, y' i ^ α' i) = ∏ i, y i ^ (Fin.snoc α' k) i := by
      intro k α'
      symm; conv_lhs => rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [mul_comm]; congr 1
    -- Rewrite IH using coefficient and product factorizations
    have hIH' : ∀ k, HasSum (fun α' : Fin (m + 1) → ℕ =>
        (∏ i, y i ^ (Fin.snoc α' k) i) • cauchyCoeffPolydisc f z (fun _ => R) (Fin.snoc α' k))
        (yL ^ k • gk k (z' + y')) := by
      intro k
      have := (hIH k).const_smul (yL ^ k)
      simp_rw [hcoeff k, smul_smul, hprod] at this
      exact this
    -- Use HasSum.sigma to combine the double sum
    -- Step 1: Build the Fin.snoc equivalence (sigma type ≃ Fin (m+2) → ℕ)
    set e : (Σ _ : ℕ, Fin (m + 1) → ℕ) ≃ (Fin (m + 2) → ℕ) :=
      (Equiv.sigmaEquivProd ℕ (Fin (m + 1) → ℕ)).trans (Fin.snocEquiv (fun _ => ℕ))
    -- Step 2: Prove summability of the target function via norm bound
    -- Cauchy estimate on distinguished boundary
    have hf_db : ∀ w ∈ distinguishedBoundary z (fun _ => R), ‖f w‖ ≤ M :=
      fun w hw => hM w (fun i => Metric.closedBall_subset_closedBall hRw.le
        (Metric.sphere_subset_closedBall (hw i)))
    -- Ratio ‖y_i‖/R < 1
    set qi : Fin (m + 2) → ℝ := fun i => ‖y i‖ / R
    have hqi_nn : ∀ i, 0 ≤ qi i := fun i => div_nonneg (norm_nonneg _) hR.le
    have hqi_lt : ∀ i, qi i < 1 := fun i => (div_lt_one hR).mpr (hy i)
    have h_qi_sum : Summable (fun α : Fin (m + 2) → ℕ => ∏ i, qi i ^ α i) :=
      summable_geometric_piNat _ qi hqi_nn hqi_lt
    -- The bound: ‖term α‖ ≤ M * ∏ i, qi i ^ α i
    set target := fun α : Fin (m + 2) → ℕ =>
      (∏ i, y i ^ α i) • cauchyCoeffPolydisc f z (fun _ => R) α
    have h_norm_bound : ∀ α, ‖target α‖ ≤ M * ∏ i, qi i ^ α i := by
      intro α
      simp only [target, norm_smul, norm_prod, norm_pow]
      have h_coeff_bound := norm_cauchyCoeffPolydisc_le f z (fun _ => R) (fun _ => hR)
        M hM_nn hf_db α
      have hR_prod_pos : (0 : ℝ) < ∏ i, R ^ α i :=
        Finset.prod_pos (fun i _ => pow_pos hR _)
      calc (∏ i, ‖y i‖ ^ α i) * ‖cauchyCoeffPolydisc f z (fun _ => R) α‖
          ≤ (∏ i, ‖y i‖ ^ α i) * (M / ∏ i, R ^ α i) :=
            mul_le_mul_of_nonneg_left h_coeff_bound
              (Finset.prod_nonneg (fun i _ => pow_nonneg (norm_nonneg _) _))
        _ = M * ∏ i, qi i ^ α i := by
            simp only [qi, div_pow, Finset.prod_div_distrib]
            field_simp [hR_prod_pos.ne']
    have h_target_summable : Summable target :=
      Summable.of_norm_bounded (h_qi_sum.mul_left M) h_norm_bound
    -- Step 3: Transport summability to sigma type and apply HasSum.sigma_of_hasSum
    have h_sigma_summable : Summable (fun p : Σ _ : ℕ, Fin (m + 1) → ℕ =>
        (∏ i, y i ^ (Fin.snoc p.2 p.1) i) •
          cauchyCoeffPolydisc f z (fun _ => R) (Fin.snoc p.2 p.1)) :=
      (Equiv.summable_iff e).mpr h_target_summable
    have h_sigma_hasSum := HasSum.sigma_of_hasSum h1d hIH' h_sigma_summable
    -- Step 4: Transport HasSum back to Fin (m+2) → ℕ
    exact (Equiv.hasSum_iff e).mp h_sigma_hasSum



set_option maxHeartbeats 400000 in
omit [CompleteSpace E] in
/-- On the diagonal, the Cauchy power series equals the sum over multi-indices
    of the given total degree (using `Finset.Nat.antidiagonalTuple`). -/
private lemma cauchyPowerSeriesPolydisc_diag_eq {m : ℕ}
    (f : (Fin (m + 1) → ℂ) → E) (z : Fin (m + 1) → ℂ) (r : Fin (m + 1) → ℝ)
    (y : Fin (m + 1) → ℂ) (n : ℕ) :
    cauchyPowerSeriesPolydisc f z r n (fun _ => y) =
    ∑ α ∈ Finset.Nat.antidiagonalTuple (m + 1) n,
      (∏ i, (y i) ^ (α i)) • cauchyCoeffPolydisc f z r α := by
  simp only [cauchyPowerSeriesPolydisc, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiRing_apply, ContinuousLinearMap.proj_apply]
  simp_rw [prod_eq_multiIdx_pow]
  set F : (Fin (m + 1) → ℕ) → E := fun α =>
    (∏ i, y i ^ α i) • ((↑(∏ i, (α i).factorial) / ↑n.factorial : ℂ) •
      cauchyCoeffPolydisc f z r α) with hF_def
  change ∑ σ, F (multiIdx σ) = _
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := multiIdx) (t := Finset.Nat.antidiagonalTuple (m + 1) n)
    (fun σ _ => Finset.Nat.mem_antidiagonalTuple.mpr (multiIdx_sum σ))]
  apply Finset.sum_congr rfl; intro α hα
  rw [Finset.sum_congr rfl (fun σ hσ => by rw [(Finset.mem_filter.mp hσ).2]),
    Finset.sum_const, hF_def]
  rw [(Nat.cast_smul_eq_nsmul ℂ _ _).symm, smul_smul, smul_smul]
  congr 1
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hαn := Finset.Nat.mem_antidiagonalTuple.mp hα
  have h := card_fiber_mul_prod_factorial n α hαn
  have hc : (↑(Finset.univ.filter (fun σ : Fin n → Fin (m + 1) => multiIdx σ = α)).card : ℂ) *
      ↑(∏ i, (α i).factorial) = ↑n.factorial := by exact_mod_cast h
  field_simp
  linear_combination (∏ i, y i ^ α i) * hc

/-- Public diagonal form of the multivariable Cauchy homogeneous term. -/
theorem cauchyPowerSeriesPolydisc_apply_diag {m : ℕ}
    (f : (Fin (m + 1) → ℂ) → E)
    (z : Fin (m + 1) → ℂ)
    (r : Fin (m + 1) → ℝ)
    (y : Fin (m + 1) → ℂ)
    (n : ℕ) :
    cauchyPowerSeriesPolydisc f z r n (fun _ => y) =
      ∑ α ∈ Finset.Nat.antidiagonalTuple (m + 1) n,
        (∏ i, y i ^ α i) • cauchyCoeffPolydisc f z r α :=
  cauchyPowerSeriesPolydisc_diag_eq f z r y n



/-- **The Cauchy power series converges to `f` on a sub-polydisc.**

    For `f` holomorphic on a closed uniform polydisc of radius `R`, the
    `cauchyPowerSeriesPolydisc` converges to `f` on a ball of radius `R / (2(m+2))`.

    **Proof idea:** By the Cauchy integral formula, `f(z+y) = (2πi)⁻ᵐ ∮...∮ K(z+y,w) f(w) dw`.
    The Cauchy kernel expands as a product of geometric series:
    `∏ᵢ (wᵢ-zᵢ-yᵢ)⁻¹ = ∑_α ∏ᵢ yᵢ^{αᵢ}/(wᵢ-zᵢ)^{αᵢ+1}`.
    Exchanging summation and iterated integration (justified by dominated convergence
    with the geometric series bound) and regrouping by total degree `|α| = n` gives
    `f(z+y) = ∑_n p_n(y,...,y)` where `p = cauchyPowerSeriesPolydisc`. -/
private lemma hasSum_cauchyPowerSeriesPolydisc_diag {m : ℕ}
    (f : (Fin (m + 1) → ℂ) → E) (z : Fin (m + 1) → ℂ) (R Rw : ℝ) (hR : 0 < R)
    (hRw : R < Rw)
    (hf_sep : ∀ w ∈ closedPolydisc z (fun _ => Rw),
      ∀ i, DifferentiableAt ℂ (fun t => f (Function.update w i t)) (w i))
    (hf_cont : ContinuousOn f (closedPolydisc z (fun _ => Rw)))
    {y : Fin (m + 1) → ℂ}
    (hy : ‖y‖ < R / (2 * ((m : ℝ) + 2))) :
    HasSum (fun n =>
      cauchyPowerSeriesPolydisc f z (fun _ => R) n (fun _ => y)) (f (z + y)) := by
  -- Component-wise norm bound: ‖y i‖ < R
  have hy_comp : ∀ i, ‖y i‖ < R := by
    intro i
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    calc ‖y i‖ ≤ ‖y‖ := norm_le_pi_norm y i
      _ < R / (2 * (↑m + 2)) := hy
      _ ≤ R := div_le_self hR.le (by linarith)
  -- Step 1: Multi-index HasSum over Fin (m+1) → ℕ
  set F : (Fin (m + 1) → ℕ) → E :=
    fun α => (∏ i, (y i) ^ (α i)) • cauchyCoeffPolydisc f z (fun _ => R) α
  have h_multi := hasSum_multiIdx_cauchyCoeff m f z R Rw hR hRw hf_sep hf_cont y hy_comp
  -- Step 2: Transport to sigma type via antidiagonalTuple equiv
  set e := Finset.Nat.sigmaAntidiagonalTupleEquivTuple (m + 1)
  have h_sigma : HasSum (F ∘ e) (f (z + y)) := (e.hasSum_iff (f := F)).mpr h_multi
  -- Step 3: Apply HasSum.sigma to regroup by total degree
  have h_regroup := h_sigma.sigma (fun n => hasSum_fintype _)
  -- h_regroup : HasSum (fun n => ∑ c, (F ∘ e) ⟨n, c⟩) (f (z + y))
  -- Step 4: Identify fiber sums with cauchyPowerSeriesPolydisc via diagonal identity
  suffices heq : (fun n => ∑ c, (F ∘ e) ⟨n, c⟩) =
      fun n => cauchyPowerSeriesPolydisc f z (fun _ => R) n (fun _ => y) by
    rwa [heq] at h_regroup
  funext n
  rw [cauchyPowerSeriesPolydisc_diag_eq]
  simp only [Function.comp, e, Finset.Nat.sigmaAntidiagonalTupleEquivTuple,
    Equiv.coe_fn_mk, F]
  exact Finset.sum_coe_sort (Finset.Nat.antidiagonalTuple (m + 1) n)
    (fun α => (∏ i, y i ^ α i) • cauchyCoeffPolydisc f z (fun _ => R) α)

/-- Explicit-radius form of the multivariable Cauchy expansion.

If `f` is holomorphic on an open neighborhood of a closed polydisc of radius
`Rw`, then the Cauchy series formed on any smaller radius `R` sums to `f` for
increments of norm less than `R / (2 * (m + 2))`. -/
theorem hasSum_cauchyPowerSeriesPolydisc_diag_of_differentiableOn
    {m : ℕ}
    {f : (Fin (m + 1) → ℂ) → E}
    {z : Fin (m + 1) → ℂ}
    {R Rw : ℝ}
    (hR : 0 < R)
    (hRw : R < Rw)
    {U : Set (Fin (m + 1) → ℂ)}
    (hU : IsOpen U)
    (hRwU : closedPolydisc z (fun _ => Rw) ⊆ U)
    (hf : DifferentiableOn ℂ f U)
    {y : Fin (m + 1) → ℂ}
    (hy : ‖y‖ < R / (2 * ((m : ℝ) + 2))) :
    HasSum
      (fun n =>
        cauchyPowerSeriesPolydisc f z (fun _ => R) n (fun _ => y))
      (f (z + y)) := by
  apply
    hasSum_cauchyPowerSeriesPolydisc_diag
      f z R Rw hR hRw
  · intro w hw i
    exact separateDiffAt_of_diffOn hU hf (hRwU hw) i
  · exact hf.continuousOn.mono hRwU
  · exact hy



/-- **The Cauchy power series gives a convergent power series for `f`.**

    For `f` holomorphic on a neighborhood of the closed uniform polydisc of radius `R`,
    the `cauchyPowerSeriesPolydisc` converges to `f` near `z`.

    The proof combines:
    1. **Norm bound** `‖p_n‖ ≤ (m+1)^n · M / R^n` → the series has radius ≥ `R/(2(m+2))`.
    2. **Cauchy integral expansion**: expand the kernel as a product of geometric series,
       exchange summation with iterated integration, and regroup by total degree. -/
private lemma hasFPowerSeriesAt_cauchyPowerSeriesPolydisc {m : ℕ}
    {f : (Fin (m + 1) → ℂ) → E} {z : Fin (m + 1) → ℂ} {R : ℝ} (hR : 0 < R)
    {U : Set (Fin (m + 1) → ℂ)} (hU : IsOpen U)
    (hRU : closedPolydisc z (fun _ => R) ⊆ U)
    (hf : DifferentiableOn ℂ f U) :
    HasFPowerSeriesAt f (cauchyPowerSeriesPolydisc f z (fun _ => R)) z := by
  -- Get a slightly larger polydisc still inside U (for the working radius)
  obtain ⟨Rw, hRw, hRwU⟩ := exists_larger_polydisc_in_open hU hRU hR
  -- Extract hypotheses on the larger polydisc
  have hf_cont_Rw : ContinuousOn f (closedPolydisc z (fun _ => Rw)) := hf.continuousOn.mono hRwU
  have hf_sep_Rw : ∀ w ∈ closedPolydisc z (fun _ => Rw),
      ∀ i, DifferentiableAt ℂ (fun t => f (Function.update w i t)) (w i) :=
    fun w hw i => separateDiffAt_of_diffOn hU hf (hRwU hw) i
  -- Bound f on the original polydisc for the Cauchy estimate
  have hf_cont : ContinuousOn f (closedPolydisc z (fun _ => R)) := hf.continuousOn.mono hRU
  have hcpt : IsCompact (closedPolydisc z (fun _ => R)) := by
    rw [closedPolydisc_eq_pi]; exact isCompact_univ_pi (fun _ => isCompact_closedBall _ _)
  obtain ⟨M, hM⟩ := (hcpt.image_of_continuousOn hf_cont).isBounded.exists_norm_le
  have hM_nn : 0 ≤ M :=
    le_trans (norm_nonneg _)
      (hM _ ⟨z, center_mem_closedPolydisc (fun _ => le_of_lt hR), rfl⟩)
  have hf_db : ∀ w ∈ distinguishedBoundary z (fun _ => R), ‖f w‖ ≤ M :=
    fun w hw => hM _ ⟨w, distinguishedBoundary_subset_closedPolydisc hw, rfl⟩
  -- ρ = R / (2(m+2)): the convergence radius
  set p := cauchyPowerSeriesPolydisc f z (fun _ => R)
  set ρ := R / (2 * ((m : ℝ) + 2))
  have hρ : 0 < ρ := by positivity
  -- Key ratio bound: (m+1) * ρ / R ≤ 1/2
  have h_ratio : (↑m + 1 : ℝ) * ρ / R ≤ 1 / 2 := by
    simp only [ρ]
    have key : (↑m + 1 : ℝ) * (R / (2 * (↑m + 2))) / R = (↑m + 1) / (2 * (↑m + 2)) := by
      field_simp
    rw [key]
    calc (↑m + 1 : ℝ) / (2 * (↑m + 2))
        ≤ (↑m + 2) / (2 * (↑m + 2)) :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = 1 / 2 := by field_simp
  -- Norm bound: ‖p n‖ * ρ^n ≤ M for all n
  have h_bound : ∀ n, ‖p n‖ * ρ ^ n ≤ M := by
    intro n
    have h1 := norm_cauchyPowerSeriesPolydisc_uniform_le f z R hR M hM_nn hf_db n
    calc ‖p n‖ * ρ ^ n
        ≤ ((↑m + 1) ^ n * (M / R ^ n)) * ρ ^ n :=
          mul_le_mul_of_nonneg_right h1 (pow_nonneg hρ.le n)
      _ = M * ((↑m + 1) * ρ / R) ^ n := by
          have hRn : (R ^ n : ℝ) ≠ 0 := pow_ne_zero _ (ne_of_gt hR)
          have lhs_eq : (↑m + 1 : ℝ) ^ n * (M / R ^ n) * ρ ^ n =
              ((↑m + 1) ^ n * ρ ^ n * M) / R ^ n := by field_simp
          have rhs_eq : M * ((↑m + 1 : ℝ) * ρ / R) ^ n =
              (((↑m + 1) * ρ) ^ n * M) / R ^ n := by rw [div_pow]; field_simp
          rw [lhs_eq, rhs_eq, mul_pow]
      _ ≤ M * (1 / 2) ^ n := by
          apply mul_le_mul_of_nonneg_left _ hM_nn
          exact pow_le_pow_left₀ (by positivity) h_ratio n
      _ ≤ M * 1 := by
          gcongr; exact pow_le_one₀ (by positivity) (by norm_num)
      _ = M := mul_one M
  -- Radius of convergence ≥ ρ
  let r : NNReal := Real.toNNReal ρ
  have hr_val : (r : ℝ) = ρ := Real.coe_toNNReal ρ hρ.le
  have h_radius : (↑r : ENNReal) ≤ p.radius := by
    apply p.le_radius_of_bound M
    intro n; rw [hr_val]; exact h_bound n
  have h_pos : (0 : ENNReal) < ↑r := by
    rw [ENNReal.coe_pos]; exact Real.toNNReal_pos.mpr hρ
  -- Construct HasFPowerSeriesAt
  refine ⟨↑r, h_radius, h_pos, fun {y} hy => ?_⟩
  rw [Metric.mem_eball, edist_zero_right, enorm_lt_coe] at hy
  have h_lt : (‖y‖₊ : ℝ) < (r : ℝ) := by exact_mod_cast hy
  rw [hr_val] at h_lt
  exact hasSum_cauchyPowerSeriesPolydisc_diag f z R Rw hR hRw hf_sep_Rw hf_cont_Rw h_lt

/-- A holomorphic function on a neighborhood of a closed uniform polydisc is
represented near its center by the corresponding Cauchy power series. -/
theorem hasFPowerSeriesAt_cauchyPowerSeriesPolydisc_of_differentiableOn
    {m : ℕ}
    {f : (Fin (m + 1) → ℂ) → E}
    {z : Fin (m + 1) → ℂ}
    {R : ℝ}
    (hR : 0 < R)
    {U : Set (Fin (m + 1) → ℂ)}
    (hU : IsOpen U)
    (hRU : closedPolydisc z (fun _ => R) ⊆ U)
    (hf : DifferentiableOn ℂ f U) :
    HasFPowerSeriesAt f
      (cauchyPowerSeriesPolydisc f z (fun _ => R)) z :=
  hasFPowerSeriesAt_cauchyPowerSeriesPolydisc hR hU hRU hf



/-- A Cauchy coefficient on a uniform polydisc is the corresponding mixed
coordinate derivative divided by the multi-index factorial. -/
theorem iteratedFDeriv_cauchyCoeffPolydisc
    {m : ℕ}
    {f : (Fin (m + 1) → ℂ) → E}
    {z : Fin (m + 1) → ℂ}
    {R : ℝ}
    (hR : 0 < R)
    {U : Set (Fin (m + 1) → ℂ)}
    (hU : IsOpen U)
    (hRU : closedPolydisc z (fun _ => R) ⊆ U)
    (hf : DifferentiableOn ℂ f U)
    (α : Fin (m + 1) → ℕ) :
    iteratedFDeriv ℂ (∑ i, α i) f z
        (fun j i =>
          if i = multiIndexEnumeration α j then 1 else 0) =
      (((∏ i, (α i).factorial : ℕ) : ℂ)) •
        cauchyCoeffPolydisc f z (fun _ => R) α := by
  classical
  obtain ⟨radius, hradius⟩ :=
    hasFPowerSeriesAt_cauchyPowerSeriesPolydisc hR hU hRU hf
  rw [hradius.iteratedFDeriv_eq_sum_of_completeSpace]
  let σ := multiIndexEnumeration α
  rw [Finset.sum_congr rfl (fun ρ _ => by
    simpa only [σ, Function.comp_apply] using
      cauchyPowerSeriesPolydisc_coordinateDirections
        f z (fun _ => R) (σ ∘ ρ))]
  simp only [multiIdx_comp_perm, multiIdx_multiIndexEnumeration]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin]
  rw [(Nat.cast_smul_eq_nsmul ℂ _ _).symm, smul_smul]
  congr 1
  have hfac :
      (((∑ i, α i).factorial : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr
      (Nat.factorial_ne_zero (∑ i, α i))
  exact mul_div_cancel₀
    (((∏ i, (α i).factorial : ℕ) : ℂ)) hfac

/-- Normalized form of `iteratedFDeriv_cauchyCoeffPolydisc`. -/
theorem cauchyCoeffPolydisc_eq_inv_multiFactorial_smul_iteratedFDeriv
    {m : ℕ}
    {f : (Fin (m + 1) → ℂ) → E}
    {z : Fin (m + 1) → ℂ}
    {R : ℝ}
    (hR : 0 < R)
    {U : Set (Fin (m + 1) → ℂ)}
    (hU : IsOpen U)
    (hRU : closedPolydisc z (fun _ => R) ⊆ U)
    (hf : DifferentiableOn ℂ f U)
    (α : Fin (m + 1) → ℕ) :
    cauchyCoeffPolydisc f z (fun _ => R) α =
      (((((∏ i, (α i).factorial : ℕ) : ℂ))⁻¹)) •
        iteratedFDeriv ℂ (∑ i, α i) f z
          (fun j i =>
            if i = multiIndexEnumeration α j then 1 else 0) := by
  rw [iteratedFDeriv_cauchyCoeffPolydisc hR hU hRU hf α,
    smul_smul]
  have hfac :
      (((∏ i, (α i).factorial : ℕ) : ℂ)) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr
      (Finset.prod_ne_zero_iff.mpr
        (fun i _ => Nat.factorial_ne_zero (α i)))
  rw [inv_mul_cancel₀ hfac, one_smul]



/-- **Multi-variable holomorphic implies analytic.**

    For `f : (Fin m → ℂ) → E` differentiable over `ℂ` on an open set `U`,
    `f` is analytic at every point of `U`.

    **Proof:** Take a uniform polydisc `P(z₀, R) ⊂ U`. The Cauchy integral formula
    gives `f(z) = (2πi)⁻ᵐ ∮...∮ f(w)/∏(wᵢ-zᵢ) dw`. Expanding the Cauchy kernel as
    a product of geometric series and swapping integration and summation (justified
    by absolute convergence) yields a multi-variable power series for `f` with
    convergence radius at least `R / (2(m+2))`. -/
theorem differentiableOn_analyticAt {m : ℕ}
    {f : (Fin m → ℂ) → E} {U : Set (Fin m → ℂ)} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {z : Fin m → ℂ} (hz : z ∈ U) :
    AnalyticAt ℂ f z := by
  induction m with
  | zero => exact analyticAt_fin_zero f z
  | succ m ih =>
    obtain ⟨R, hR, hRU⟩ := exists_uniform_polydisc_subset hU hz
    exact ⟨_, hasFPowerSeriesAt_cauchyPowerSeriesPolydisc hR hU hRU hf⟩

end SCV

end
