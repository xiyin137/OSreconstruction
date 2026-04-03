/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Topology.Algebra.IsUniformGroup.Defs
import Mathlib.Topology.Metrizable.CompletelyMetrizable
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Completeness and Barrelledness of the Schwartz Space

This file establishes completeness of the Schwartz space `𝓢(E, F)` and derives
the Banach-Steinhaus theorem for tempered distributions. This is the critical
infrastructure for distributional uniqueness on tube domains.

## Main results

* `SchwartzMap.instCompleteSpace` — completeness of `𝓢(E, F)`
* `SchwartzMap.instBarrelledSpace` — barrelledness (from completeness)
* `SchwartzMap.tempered_uniform_bound` — uniform seminorm bound for
  convergent sequences of tempered distributions

## Chain of reasoning

```
CompleteSpace 𝓢(E,F)
  → (countably generated uniformity) → BaireSpace
  → BarrelledSpace ℝ 𝓢(E,F)
  → WithSeminorms.banach_steinhaus
  → uniform seminorm bound for {T_ε}
```

## References

* Reed-Simon, "Methods of Modern Mathematical Physics I", Theorem V.13
* Treves, "Topological Vector Spaces", §51
-/

noncomputable section

open Filter Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace SchwartzMap

/-! ### Completeness

The proof that 𝓢(E, F) is complete follows the standard argument:
a Cauchy sequence `(f_m)` in each Schwartz seminorm `‖·‖_{k,n}` gives
uniform convergence of `iteratedFDeriv ℝ n f_m` for each `n`. The limit
is C^∞ by iterated `hasFDerivAt_of_tendstoUniformly` and has rapid decay
by the weighted uniform convergence from `(k,n)` seminorms. -/

/-- Cauchy sequences in the Schwartz topology are Cauchy in each seminorm. -/
private theorem cauchySeq_seminorm {u : ℕ → SchwartzMap E F} (hu : CauchySeq u)
    (k n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ m ≥ N, ∀ m' ≥ N, SchwartzMap.seminorm ℝ k n (u m - u m') < ε := by
  have hws := schwartz_withSeminorms ℝ E F
  -- CauchySeq u means Tendsto (u × u) atTop (uniformity)
  -- For additive groups: uniformity = comap (sub) (nhds 0)
  -- So CauchySeq u ↔ Tendsto (fun p => u p.1 - u p.2) (atTop ×ˢ atTop) (nhds 0)
  rw [cauchySeq_iff_tendsto, uniformity_eq_comap_nhds_zero, Filter.tendsto_comap_iff] at hu
  -- Now hu : Tendsto (fun p => u p.1 - u p.2) atTop (nhds 0)
  -- Normalize the topology to match WithSeminorms
  set_option backward.isDefEq.respectTransparency false in
  rw [hws.tendsto_nhds _ 0] at hu
  -- Now hu : ∀ i ε > 0, ∀ᶠ p in atTop, seminorm i (u p.1 - u p.2 - 0) < ε
  have h := hu (k, n) ε hε
  simp only [sub_zero, Filter.Eventually, Filter.mem_atTop_sets,
    Prod.forall, Function.comp, Prod.map] at h
  obtain ⟨⟨N₁, N₂⟩, hN⟩ := h
  refine ⟨max N₁ N₂, fun m hm m' hm' => ?_⟩
  have := hN m m' ⟨le_of_max_le_left hm, le_of_max_le_right hm'⟩
  simp only [Set.mem_setOf_eq] at this
  rwa [show u m' - u m = -(u m - u m') from (neg_sub _ _).symm,
    map_neg_eq_map] at this

/-- Pointwise evaluation of iteratedFDeriv on a Schwartz difference. -/
private theorem iteratedFDeriv_sub_schwartz (f g : SchwartzMap E F) (n : ℕ) (x : E) :
    iteratedFDeriv ℝ n (⇑(f - g)) x =
      iteratedFDeriv ℝ n (⇑f) x - iteratedFDeriv ℝ n (⇑g) x := by
  have hf : ContDiff ℝ n (⇑f) := f.smooth n
  have hg : ContDiff ℝ n (⇑g) := g.smooth n
  have hfg : (⇑(f - g) : E → F) = (⇑f) + fun x => -(⇑g x) := by
    ext y; simp [sub_eq_add_neg]
  rw [hfg, iteratedFDeriv_add hf hg.neg]
  simp only [Pi.add_apply, sub_eq_add_neg]
  congr 1
  have : (fun x => -(⇑g x)) = -⇑g := rfl
  rw [this, iteratedFDeriv_neg, Pi.neg_apply]

/-- The iteratedFDeriv of Schwartz functions is pointwise Cauchy when the
    sequence is Cauchy in the Schwartz topology. -/
private theorem iteratedFDeriv_cauchySeq {u : ℕ → SchwartzMap E F}
    (hu : CauchySeq u) (n : ℕ) (x : E) :
    CauchySeq (fun m => iteratedFDeriv ℝ n (u m) x) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := cauchySeq_seminorm hu 0 n ε hε
  exact ⟨N, fun m hm m' hm' => by
    rw [dist_eq_norm]
    rw [← iteratedFDeriv_sub_schwartz]
    calc ‖iteratedFDeriv ℝ n (⇑(u m - u m')) x‖
        ≤ ‖x‖ ^ 0 * ‖iteratedFDeriv ℝ n (⇑(u m - u m')) x‖ := by simp
      _ ≤ SchwartzMap.seminorm ℝ 0 n (u m - u m') := SchwartzMap.le_seminorm ℝ 0 n _ x
      _ < ε := hN m hm m' hm'⟩

/-- Combined Cauchy bound: for each total degree j, there exists a threshold beyond
    which ALL seminorms of degree ≤ j are bounded by (1/2)^j. -/
private theorem cauchySeq_combined_bound {u : ℕ → SchwartzMap E F} (hu : CauchySeq u)
    (j : ℕ) : ∃ N, ∀ m ≥ N, ∀ m' ≥ N, ∀ k n, k + n ≤ j →
      SchwartzMap.seminorm ℝ k n (u m - u m') < (1/2 : ℝ) ^ j := by
  choose N hN using fun k n => cauchySeq_seminorm hu k n ((1/2) ^ j) (by positivity)
  let S := Finset.range (j + 1) ×ˢ Finset.range (j + 1)
  refine ⟨S.sup (fun p => N p.1 p.2), fun m hm m' hm' k n hkn => hN k n m ?_ m' ?_⟩
  all_goals exact le_trans (Finset.le_sup (f := fun p => N p.1 p.2) (show (k, n) ∈ S from
    Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
      Finset.mem_range.mpr (by omega)⟩)) (by assumption)

/-- Weighted pointwise bound on the limit: if `u` is Cauchy in the Schwartz topology
    and the iteratedFDeriv converges pointwise, the weighted derivative error
    `‖x‖^k * ‖iteratedFDeriv (u m) x - lim x‖` is controlled by the Cauchy seminorm. -/
private theorem weighted_deriv_limit_le {u : ℕ → SchwartzMap E F} (hu : CauchySeq u)
    [CompleteSpace F] (k n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ m ≥ N, ∀ x,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑(u m)) x -
        limUnder atTop (fun m' => iteratedFDeriv ℝ n (⇑(u m')) x)‖ ≤ ε := by
  obtain ⟨N, hN⟩ := cauchySeq_seminorm hu k n ε hε
  refine ⟨N, fun m hm x => ?_⟩
  -- The limit exists by completeness
  have hc := iteratedFDeriv_cauchySeq hu n x
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  have hL_eq : L = limUnder atTop (fun m' => iteratedFDeriv ℝ n (⇑(u m')) x) :=
    hL.limUnder_eq.symm
  rw [← hL_eq]
  -- Pass to limit: ‖x‖^k * ‖a - iteratedFDeriv (u m') x‖ → ‖x‖^k * ‖a - L‖
  -- and each term is ≤ ε for m' ≥ N
  apply le_of_tendsto (x := atTop) (f := fun m' => ‖x‖ ^ k *
      ‖iteratedFDeriv ℝ n (⇑(u m)) x - iteratedFDeriv ℝ n (⇑(u m')) x‖)
  · exact (tendsto_const_nhds.sub hL).norm.const_mul _
  · exact Filter.eventually_atTop.mpr ⟨N, fun m' hm' => by
      have key := SchwartzMap.le_seminorm ℝ k n (u m - u m') x
      rw [iteratedFDeriv_sub_schwartz] at key
      calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑(u m)) x - iteratedFDeriv ℝ n (⇑(u m')) x‖
          ≤ SchwartzMap.seminorm ℝ k n (u m - u m') := key
        _ ≤ ε := le_of_lt (hN m hm m' hm')⟩

/-- For a sequence of SchwartzMaps with geometric seminorm decay, the shifted tail
    tsum has interchangeable iteratedFDeriv, and the weighted derivative is bounded
    by the geometric tail. -/
private theorem tail_tsum_iteratedFDeriv_bound [CompleteSpace F]
    {w : ℕ → SchwartzMap E F}
    (hw : ∀ j k n, k + n ≤ j → SchwartzMap.seminorm ℝ k n (w j) < (1/2 : ℝ) ^ j)
    (K : ℕ) (k n : ℕ) (hK : k + n ≤ K) (x : E) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => ∑' j, (w (j + K) : SchwartzMap E F) y) x‖ ≤
      2 * (1 / 2 : ℝ) ^ K := by
  -- Set up the bounds for iteratedFDeriv_tsum_apply
  have hf : ∀ j, ContDiff ℝ (↑K : ℕ∞) (⇑(w (j + K))) :=
    fun j => (w (j + K)).smooth _
  have hbound : ∀ (p : ℕ) (j : ℕ) (y : E), (↑p : ℕ∞) ≤ ↑K →
      ‖iteratedFDeriv ℝ p (⇑(w (j + K))) y‖ ≤ (1 / 2 : ℝ) ^ (j + K) := by
    intro p j y hp
    have hp' : p ≤ K := by exact_mod_cast hp
    have h1 := SchwartzMap.le_seminorm ℝ 0 p (w (j + K)) y
    simp only [pow_zero, one_mul] at h1
    exact le_of_lt (lt_of_le_of_lt h1 (hw (j + K) 0 p (by omega)))
  have hsum : ∀ p : ℕ, (↑p : ℕ∞) ≤ ↑K →
      Summable (fun j => (1 / 2 : ℝ) ^ (j + K)) :=
    fun _ _ => (summable_geometric_of_lt_one (by positivity) (by norm_num)).comp_injective
      (fun a b h => by omega)
  -- The interchange: iteratedFDeriv commutes with tsum
  have hinterchange := iteratedFDeriv_tsum_apply hf hsum hbound
    (show (↑n : ℕ∞) ≤ ↑K from by exact_mod_cast (show n ≤ K by omega)) x
  rw [hinterchange]
  -- Bound: ‖x‖^k * ‖∑' j, iteratedFDeriv n (w (j+K)) x‖
  --      ≤ ∑' j, ‖x‖^k * ‖iteratedFDeriv n (w (j+K)) x‖
  --      ≤ ∑' j, seminorm k n (w (j+K))
  --      ≤ ∑' j, (1/2)^(j+K)
  --      = 2 * (1/2)^K
  have hn_le_K : (↑n : ℕ∞) ≤ ↑K := by exact_mod_cast (show n ≤ K by omega)
  -- Each term satisfies the weighted bound
  have hterm : ∀ j, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑(w (j + K))) x‖ ≤
      (1 / 2 : ℝ) ^ (j + K) := by
    intro j
    exact le_of_lt (lt_of_le_of_lt (SchwartzMap.le_seminorm ℝ k n (w (j + K)) x)
      (hw (j + K) k n (by omega)))
  have hsummable_bound := hsum n hn_le_K
  have hsummable_norm : Summable (fun j => ‖iteratedFDeriv ℝ n (⇑(w (j + K))) x‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => hbound n j x hn_le_K)
      hsummable_bound
  calc ‖x‖ ^ k * ‖∑' j, iteratedFDeriv ℝ n (⇑(w (j + K))) x‖
      ≤ ∑' j, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑(w (j + K))) x‖ := by
        calc ‖x‖ ^ k * ‖∑' j, iteratedFDeriv ℝ n (⇑(w (j + K))) x‖
            ≤ ‖x‖ ^ k * (∑' j, ‖iteratedFDeriv ℝ n (⇑(w (j + K))) x‖) := by
              gcongr; exact norm_tsum_le_tsum_norm hsummable_norm
          _ = ∑' j, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑(w (j + K))) x‖ := (tsum_mul_left ..).symm
    _ ≤ ∑' j, (1 / 2 : ℝ) ^ (j + K) := by
        exact Summable.tsum_le_tsum hterm
          (Summable.of_nonneg_of_le (fun _ => by positivity) hterm hsummable_bound)
          hsummable_bound
    _ = 2 * (1 / 2 : ℝ) ^ K := by
        simp_rw [pow_add]
        rw [tsum_mul_right]
        congr 1
        convert tsum_geometric_two using 1

/-- The Schwartz space is complete in the seminorm topology. -/
instance instCompleteSpace [CompleteSpace F] : CompleteSpace (SchwartzMap E F) := by
  set_option backward.isDefEq.respectTransparency false in
  have : (uniformity (SchwartzMap E F)).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  apply UniformSpace.complete_of_cauchySeq_tendsto
  intro u hu
  -- Step 1: Pointwise convergence of the functions
  have hptwise : ∀ x, ∃ y, Filter.Tendsto (fun m => u m x) atTop (nhds y) := by
    intro x
    apply cauchySeq_tendsto_of_complete
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := cauchySeq_seminorm hu 0 0 ε hε
    exact ⟨N, fun m hm m' hm' => by
      rw [dist_eq_norm]
      have : ‖(u m - u m') x‖ ≤ SchwartzMap.seminorm ℝ 0 0 (u m - u m') := by
        have h := SchwartzMap.le_seminorm ℝ 0 0 (u m - u m') x; simp at h; exact h
      calc ‖u m x - u m' x‖ = ‖(u m - u m') x‖ := by simp [sub_apply]
        _ ≤ SchwartzMap.seminorm ℝ 0 0 (u m - u m') := this
        _ < ε := hN m hm m' hm'⟩
  choose _f _hf using hptwise
  -- Step 2: Extract subsequence with geometric seminorm decay
  choose M hM using fun j => cauchySeq_combined_bound hu j
  let φ : ℕ → ℕ := fun j => Nat.rec (M 0) (fun j prev => max (prev + 1) (M (j + 1))) j
  have hφ_ge : ∀ j, M j ≤ φ j := by
    intro j; induction j with
    | zero => exact le_refl _
    | succ j _ => exact le_max_right _ _
  have hφ_mono : StrictMono φ := by
    intro a b hab
    induction hab with
    | refl => exact lt_of_lt_of_le (Nat.lt_succ_of_le le_rfl) (le_max_left _ _)
    | step h ih => exact lt_of_lt_of_le ih (le_of_lt (lt_of_lt_of_le
        (Nat.lt_succ_of_le le_rfl) (le_max_left _ _)))
  -- Step 3: Telescoping differences and their seminorm decay
  let w : ℕ → SchwartzMap E F := fun j => u (φ (j + 1)) - u (φ j)
  have hw : ∀ j k n, k + n ≤ j →
      SchwartzMap.seminorm ℝ k n (w j) < (1 / 2 : ℝ) ^ j := by
    intro j k n hkn
    exact hM j (φ (j + 1)) (le_trans (hφ_ge j) (le_of_lt (hφ_mono (Nat.lt_succ_of_le le_rfl))))
      (φ j) (hφ_ge j) k n hkn
  -- Pointwise summability of the telescoping series
  have hconv : ∀ y, Summable (fun j => (w j : SchwartzMap E F) y) := by
    intro y
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    · intro j
      have h1 := SchwartzMap.le_seminorm ℝ 0 0 (w j) y
      simp only [pow_zero, one_mul] at h1
      calc ‖(w j) y‖ = ‖iteratedFDeriv ℝ 0 (⇑(w j)) y‖ := by
              rw [norm_iteratedFDeriv_zero]
        _ ≤ SchwartzMap.seminorm ℝ 0 0 (w j) := h1
        _ ≤ (1 / 2 : ℝ) ^ j := le_of_lt (hw j 0 0 (by omega))
    · exact summable_geometric_of_lt_one (by positivity) (by norm_num)
  -- Telescoping identity
  have htelescope : ∀ m y, u (φ m) y = u (φ 0) y +
      ∑ j ∈ Finset.range m, (w j) y := by
    intro m y; induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ← ih]
      simp only [w, sub_apply]; abel
  -- Splitting lemma: ∑' j, w j y = ∑ j ∈ range K, w j y + ∑' j, w (j+K) y
  have htsum_split : ∀ K y, ∑' j, (w j) y =
      ∑ j ∈ Finset.range K, (w j) y + ∑' j, (w (j + K)) y :=
    fun K y => ((hconv y).sum_add_tsum_nat_add K).symm
  -- Step 4: The limit function
  let g : E → F := fun x => u (φ 0) x + ∑' j, (w j) x
  -- Global splitting identity
  have hg_split : ∀ K x, g x = u (φ K) x + ∑' j, (w (j + K)) x := by
    intro K x
    simp only [g]
    rw [htsum_split K x, htelescope K x]
    abel
  -- Step 5: Auxiliary: contDiff for tsum of shifted tail
  -- ContDiff takes n : WithTop ℕ∞. SchwartzMap uses ↑(⊤ : ℕ∞) (= C^∞), not ⊤ (= C^ω).
  have htsum_contDiff : ∀ K, ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun x => ∑' j, (w (j + K) : SchwartzMap E F) x) := by
    intro K
    exact contDiff_tsum_of_eventually (N := (⊤ : ℕ∞))
      (f := fun j => ⇑(w (j + K))) (v := fun _ j => (1 / 2 : ℝ) ^ j)
      (fun j => (w (j + K)).smooth')
      (fun _ _ => summable_geometric_of_lt_one (by positivity) (by norm_num))
      (fun p _ => by
        apply Filter.eventually_cofinite.mpr
        apply Set.Finite.subset (Set.finite_Iio p)
        intro j hj
        simp only [Set.mem_setOf_eq, not_forall, Set.mem_Iio] at hj ⊢
        by_contra h; push_neg at h
        obtain ⟨y, hy⟩ := hj; apply hy
        have h1 := SchwartzMap.le_seminorm ℝ 0 p (w (j + K)) y
        simp only [pow_zero, one_mul] at h1
        exact le_of_lt (lt_of_le_of_lt h1 (lt_of_lt_of_le (hw (j + K) 0 p (by omega))
          (pow_le_pow_of_le_one (by positivity) (by norm_num) (Nat.le_add_right j K)))))
  -- Step 5: g is C^∞
  have hsmooth_g : ContDiff ℝ (↑(⊤ : ℕ∞)) g := by
    have htsum_smooth : ContDiff ℝ (↑(⊤ : ℕ∞))
        (fun x => ∑' j, (w j : SchwartzMap E F) x) := by
      convert htsum_contDiff 0 using 2
    exact (u (φ 0)).smooth'.add htsum_smooth
  -- Step 6: Rapid decay
  have hdecay : ∀ k n : ℕ, ∃ C : ℝ, ∀ x : E,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n g x‖ ≤ C := by
    intro k n
    let K := k + n
    refine ⟨SchwartzMap.seminorm ℝ k n (u (φ K)) + 1 +
      2 * (1 / 2 : ℝ) ^ K, fun x => ?_⟩
    -- g = u(φ K) + tail, as functions
    have hg_funext : g = fun y => u (φ K) y + ∑' j, (w (j + K)) y := funext (hg_split K)
    rw [hg_funext]
    -- iteratedFDeriv of sum at finite order n
    have hcd1 : ContDiff ℝ (↑n : ℕ∞) (⇑(u (φ K))) := (u (φ K)).smooth _
    have hcd2 : ContDiff ℝ (↑n : ℕ∞) (fun y => ∑' j, (w (j + K) : SchwartzMap E F) y) :=
      (htsum_contDiff K).of_le (WithTop.coe_le_coe.mpr le_top)
    rw [show (fun y => u (φ K) y + ∑' j, (w (j + K) : SchwartzMap E F) y) =
      (⇑(u (φ K))) + (fun y => ∑' j, (w (j + K) : SchwartzMap E F) y) from rfl,
      iteratedFDeriv_add_apply (hcd1.contDiffAt) (hcd2.contDiffAt)]
    have hmain :
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑(u (φ K))) x +
            iteratedFDeriv ℝ n (fun y => ∑' j, (w (j + K)) y) x‖
          ≤ SchwartzMap.seminorm ℝ k n (u (φ K)) + 2 * (1 / 2 : ℝ) ^ K := by
      calc
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑(u (φ K))) x +
            iteratedFDeriv ℝ n (fun y => ∑' j, (w (j + K)) y) x‖
            ≤ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑(u (φ K))) x‖ +
              ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => ∑' j, (w (j + K)) y) x‖ := by
                rw [← mul_add]
                gcongr
                exact norm_add_le _ _
        _ ≤ SchwartzMap.seminorm ℝ k n (u (φ K)) +
              2 * (1 / 2 : ℝ) ^ K := by
              exact add_le_add
                (SchwartzMap.le_seminorm ℝ k n (u (φ K)) x)
                (tail_tsum_iteratedFDeriv_bound hw K k n le_rfl x)
    have hone : (0 : ℝ) ≤ 1 := by positivity
    linarith
  -- Step 7: Build the SchwartzMap
  let a : SchwartzMap E F := ⟨g, hsmooth_g, hdecay⟩
  have hsub : Tendsto (u ∘ φ) atTop (𝓝 a) := by
    refine ((schwartz_withSeminorms ℝ E F).tendsto_nhds (u ∘ φ) a).2 ?_
    intro ⟨k, n⟩ ε hε
    simp only [Function.comp]
    -- Find threshold: need 2 * (1/2)^m < ε
    obtain ⟨m₀, hm₀⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one
      (by positivity : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 2).eventually
      (gt_mem_nhds (show (2 : ℝ) * 0 < ε by simp [hε])) |>.exists
    refine Filter.eventually_atTop.mpr ⟨max (k + n) m₀, fun m hm => ?_⟩
    have hfuneq : ⇑(u (φ m) - a) =
        -(fun y => ∑' j, (w (j + m) : SchwartzMap E F) y) := by
      ext y; simp only [sub_apply, Pi.neg_apply]
      change (u (φ m)) y - g y = -(∑' j, (w (j + m)) y)
      rw [hg_split m y]
      abel
    have htail :
        SchwartzMap.seminorm ℝ k n (u (φ m) - a) ≤ 2 * (1 / 2 : ℝ) ^ m := by
      refine SchwartzMap.seminorm_le_bound ℝ k n (u (φ m) - a) (by positivity) ?_
      intro x
      rw [hfuneq, iteratedFDeriv_neg_apply, norm_neg]
      exact tail_tsum_iteratedFDeriv_bound hw m k n (le_of_max_le_left hm) x
    have hpow : (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ m₀ := by
      exact pow_le_pow_of_le_one (by positivity) (by norm_num : (1 / 2 : ℝ) ≤ 1)
        (le_of_max_le_right hm)
    have htail_lt : 2 * (1 / 2 : ℝ) ^ m < ε := by
      nlinarith [hpow, hm₀]
    exact lt_of_le_of_lt htail htail_lt
  exact ⟨a, tendsto_nhds_of_cauchySeq_of_subseq hu hφ_mono.tendsto_atTop hsub⟩


/-! ### Barrelledness

The Schwartz space is barrelled because it is a complete metrizable locally
convex space (Fréchet space). The chain:
- `CompleteSpace` + `IsCountablyGenerated (uniformity)` → `BaireSpace`
- `BaireSpace` → `BarrelledSpace` (via `BaireSpace.instBarrelledSpace`)

The uniformity is countably generated because `SchwartzMap` is first-countable
and is a uniform add group (`IsUniformAddGroup.uniformity_countably_generated`). -/

/-- The Schwartz space is barrelled: every lower-semicontinuous seminorm
    is continuous. This is a consequence of being a Fréchet (complete
    metrizable locally convex) space. -/
instance instBarrelledSpace [CompleteSpace F] :
    BarrelledSpace ℝ (SchwartzMap E F) := by
  -- Chain: CompleteSpace + countably generated uniformity → BaireSpace → BarrelledSpace
  -- SchwartzMap has IsUniformAddGroup and Countable (ℕ × ℕ) index for seminorms
  set_option backward.isDefEq.respectTransparency false in
  have hcg : (uniformity (SchwartzMap E F)).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  -- CompleteSpace + countably generated uniformity → IsCompletelyPseudoMetrizableSpace
  have : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (SchwartzMap E F) :=
    TopologicalSpace.IsCompletelyPseudoMetrizableSpace.of_completeSpace_pseudometrizable
  -- IsCompletelyPseudoMetrizableSpace → BaireSpace (automatic instance)
  -- BaireSpace → BarrelledSpace (automatic instance)
  infer_instance

/-! ### Banach-Steinhaus for tempered distributions -/

/-- Uniform seminorm bound for a pointwise bounded family of tempered
    distributions. Given a family `{T_i}` of continuous linear maps
    `𝓢(E, F) →L[ℝ] F` that is pointwise bounded (for each `f`, the norms
    `‖T_i f‖` are bounded uniformly in `i`), the family is uniformly
    equicontinuous.

    In particular, there exist Schwartz seminorm indices and a constant `C`
    such that `‖T_i f‖ ≤ C · seminorm(f)` for all `i` and `f`. -/
theorem tempered_equicontinuous
    [CompleteSpace F] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {ι : Type*} {T : ι → SchwartzMap E F →L[ℝ] G}
    (hT : ∀ f, ∃ C, ∀ i, ‖T i f‖ ≤ C) :
    UniformEquicontinuous (fun i f => T i f) := by
  have hq := norm_withSeminorms ℝ G
  set_option backward.isDefEq.respectTransparency false in
  apply hq.banach_steinhaus
  intro k x
  rw [BddAbove]
  obtain ⟨C, hC⟩ := hT x
  exact ⟨C, by rintro _ ⟨i, rfl⟩; simp [normSeminorm]; exact hC i⟩

/-- Pointwise bounded tempered distributions admit a common finite Schwartz-seminorm bound.

This is the explicit Banach-Steinhaus payoff needed in distributional uniqueness arguments:
once a family of continuous linear functionals on Schwartz space is pointwise bounded, there
is a single finite supremum of Schwartz seminorms controlling all members of the family. -/
theorem tempered_uniform_schwartz_bound
    [CompleteSpace F] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {ι : Type*} {T : ι → SchwartzMap E F →L[ℝ] G}
    (hT : ∀ f, ∃ C, ∀ i, ‖T i f‖ ≤ C) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : NNReal, C ≠ 0 ∧
      ∀ i : ι, ∀ f : SchwartzMap E F,
        ‖T i f‖ ≤ (C • s.sup (schwartzSeminormFamily ℝ E F)) f := by
  have hEqui : UniformEquicontinuous (fun i f => T i f) := tempered_equicontinuous hT
  set_option backward.isDefEq.respectTransparency false in
  have hq :=
    ((norm_withSeminorms ℝ G).uniformEquicontinuous_iff_exists_continuous_seminorm
      (f := fun i => (T i).toLinearMap)).mp hEqui
  obtain ⟨p, hp_cont, hp_bound⟩ := hq (0 : Fin 1)
  obtain ⟨s, C, hCne, hp_dominate⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ E F) p hp_cont
  refine ⟨s, C, hCne, fun i f => ?_⟩
  calc
    ‖T i f‖ = ((normSeminorm ℝ G).comp (T i).toLinearMap) f := by rfl
    _ ≤ p f := hp_bound i f
    _ ≤ (C • s.sup (schwartzSeminormFamily ℝ E F)) f := hp_dominate f

/-- A convergent sequence of tempered distributions is uniformly bounded
    in some Schwartz seminorm. More precisely, if `T_n(f) → L(f)` for each
    Schwartz `f`, then `{T_n}` is equicontinuous. -/
theorem tempered_equicontinuous_of_tendsto
    [CompleteSpace F] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {T : ℕ → SchwartzMap E F →L[ℝ] G}
    (hT : ∀ f, ∃ L, Filter.Tendsto (fun n => T n f) atTop (nhds L)) :
    UniformEquicontinuous (fun n f => T n f) := by
  apply tempered_equicontinuous
  intro f
  obtain ⟨L, hL⟩ := hT f
  -- Convergent sequences in a normed space are bounded
  have hbdd := hL.norm.isBoundedUnder_le
  obtain ⟨b, hb⟩ := hbdd
  simp only [Filter.Eventually, Filter.mem_map, Filter.mem_atTop_sets] at hb
  obtain ⟨N, hN⟩ := hb
  -- Bound all terms: max of b and the finitely many initial terms
  refine ⟨max b (Finset.sup' (Finset.range (N + 1))
    ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun n => ‖T n f‖)), fun i => ?_⟩
  by_cases hi : N ≤ i
  · exact le_max_of_le_left (hN i hi)
  · push_neg at hi
    exact le_max_of_le_right
      (Finset.le_sup' (fun n => ‖T n f‖) (Finset.mem_range.mpr (by omega)))

/-- If a sequence of tempered distributions converges pointwise to `0`, then it also
converges to `0` on any convergent sequence of Schwartz test functions.

This is the exact Banach-Steinhaus payoff needed in distributional edge-of-the-wedge
arguments: the test functions vary with the boundary point, but a common finite seminorm
bound controls the error term. -/
theorem tempered_apply_tendsto_zero_of_tendsto
    [CompleteSpace F] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {T : ℕ → SchwartzMap E F →L[ℝ] G}
    (hT : ∀ f : SchwartzMap E F, Filter.Tendsto (fun n => T n f) atTop (nhds 0))
    {u : ℕ → SchwartzMap E F} {f : SchwartzMap E F}
    (hu : Filter.Tendsto u atTop (nhds f)) :
    Filter.Tendsto (fun n => T n (u n)) atTop (nhds 0) := by
  have hTbdd : ∀ f : SchwartzMap E F, ∃ C, ∀ n, ‖T n f‖ ≤ C := by
    intro f
    have hbdd := (hT f).norm.isBoundedUnder_le
    obtain ⟨b, hb⟩ := hbdd
    simp only [Filter.Eventually, Filter.mem_map, Filter.mem_atTop_sets] at hb
    obtain ⟨N, hN⟩ := hb
    refine ⟨max b (Finset.sup' (Finset.range (N + 1))
      ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun n => ‖T n f‖)), fun i => ?_⟩
    by_cases hi : N ≤ i
    · exact le_max_of_le_left (hN i hi)
    · push_neg at hi
      exact le_max_of_le_right
        (Finset.le_sup' (fun n => ‖T n f‖) (Finset.mem_range.mpr (by omega)))
  obtain ⟨s, C, hCne, hbound⟩ := tempered_uniform_schwartz_bound hTbdd
  have hCpos : 0 < (C : ℝ) := by
    exact_mod_cast (show 0 < C from pos_iff_ne_zero.mpr hCne)
  let p : Seminorm ℝ (SchwartzMap E F) := s.sup (schwartzSeminormFamily ℝ E F)
  have hp_small : Filter.Tendsto (fun n => p (u n - f)) atTop (nhds 0) := by
    have hsub : Filter.Tendsto (fun n => u n - f) atTop (nhds (0 : SchwartzMap E F)) := by
      simpa using (hu.sub tendsto_const_nhds : Filter.Tendsto (fun n => u n - f) atTop
        (nhds (f - f)))
    have hws := schwartz_withSeminorms ℝ E F
    have hp_cont : Continuous p := by
      refine Seminorm.continuous_of_le ?_
        (show p ≤ ∑ i ∈ s, schwartzSeminormFamily ℝ E F i by
          simpa [p] using Seminorm.finset_sup_le_sum (schwartzSeminormFamily ℝ E F) s)
      change Continuous (fun x => Seminorm.coeFnAddMonoidHom ℝ (SchwartzMap E F)
        (∑ i ∈ s, schwartzSeminormFamily ℝ E F i) x)
      simp_rw [map_sum, Finset.sum_apply]
      exact continuous_finset_sum _ fun i _ => hws.continuous_seminorm i
    simpa using (hp_cont.tendsto 0).comp hsub
  refine Metric.tendsto_nhds.mpr ?_
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  have h1 := (Metric.tendsto_nhds.mp (hT f)) (ε / 2) hε2
  have h2 := (Metric.tendsto_nhds.mp hp_small) (ε / (2 * C)) (by
    have hden : 0 < 2 * (C : ℝ) := by positivity
    exact div_pos hε hden)
  filter_upwards [h1, h2] with n hn1 hn2
  have hn1' : ‖T n f‖ < ε / 2 := by
    simpa [dist_eq_norm] using hn1
  have hn2' : p (u n - f) < ε / (2 * C) := by
    have hpnn : 0 ≤ p (u n - f) := apply_nonneg p _
    simpa [Real.dist_eq, abs_of_nonneg hpnn] using hn2
  have hsplit : T n (u n) = T n (u n - f) + T n f := by
    calc
      T n (u n) = T n ((u n - f) + f) := by
        congr 1
        abel
      _ = T n (u n - f) + T n f := map_add _ _ _
  calc
    dist (T n (u n)) 0
        = ‖T n (u n - f) + T n f‖ := by
            rw [dist_eq_norm, hsplit, sub_zero]
    _ ≤ ‖T n (u n - f)‖ + ‖T n f‖ := norm_add_le _ _
    _ ≤ (C : ℝ) * p (u n - f) + ‖T n f‖ := by
          gcongr
          exact hbound n (u n - f)
    _ < (C : ℝ) * (ε / (2 * C)) + ε / 2 := by
          have hmul : (C : ℝ) * p (u n - f) < (C : ℝ) * (ε / (2 * C)) := by
            nlinarith [hn2', hCpos]
          exact add_lt_add hmul hn1'
    _ = ε := by
          field_simp [show (C : ℝ) ≠ 0 by exact_mod_cast hCne]
          ring

/-- Filter-version Banach-Steinhaus payoff for the zero-limit case.

If `Tᵢ → 0` pointwise on Schwartz space along a countably generated filter `l`,
and `uᵢ → f` in the Schwartz topology along `l`, then `Tᵢ (uᵢ) → 0` along `l`.

This is the form needed for weak boundary-value arguments indexed by
`nhdsWithin 0 (Set.Ioi 0)`, where the parameter is not naturally a sequence. -/
theorem tempered_apply_tendsto_zero_of_tendsto_filter
    [CompleteSpace F] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    {T : α → SchwartzMap E F →L[ℝ] G}
    (hT : ∀ f : SchwartzMap E F, Filter.Tendsto (fun a => T a f) l (nhds 0))
    {u : α → SchwartzMap E F} {f : SchwartzMap E F}
    (hu : Filter.Tendsto u l (nhds f)) :
    Filter.Tendsto (fun a => T a (u a)) l (nhds 0) := by
  apply Filter.tendsto_of_seq_tendsto
  intro v hv
  have hT' : ∀ g : SchwartzMap E F,
      Filter.Tendsto (fun n => T (v n) g) atTop (nhds 0) := by
    intro g
    exact (hT g).comp hv
  have hu' : Filter.Tendsto (fun n => u (v n)) atTop (nhds f) := hu.comp hv
  simpa using tempered_apply_tendsto_zero_of_tendsto hT' hu'

/-- If `Tₙ → S` pointwise on Schwartz space and `uₙ → f` in the Schwartz topology,
then `Tₙ (uₙ) → S f`.

This is the nonzero-limit Banach-Steinhaus payoff used when a mollified boundary
trace converges to a continuous boundary functional rather than to `0`. -/
theorem tempered_apply_tendsto_of_tendsto
    [CompleteSpace F] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {T : ℕ → SchwartzMap E F →L[ℝ] G}
    {S : SchwartzMap E F →L[ℝ] G}
    (hT : ∀ f : SchwartzMap E F, Filter.Tendsto (fun n => T n f) atTop (nhds (S f)))
    {u : ℕ → SchwartzMap E F} {f : SchwartzMap E F}
    (hu : Filter.Tendsto u atTop (nhds f)) :
    Filter.Tendsto (fun n => T n (u n)) atTop (nhds (S f)) := by
  let T' : ℕ → SchwartzMap E F →L[ℝ] G := fun n => T n - S
  have hT' : ∀ g : SchwartzMap E F, Filter.Tendsto (fun n => T' n g) atTop (nhds 0) := by
    intro g
    have h : Filter.Tendsto (fun n => T n g - S g) atTop (nhds (S g - S g)) :=
      (hT g).sub tendsto_const_nhds
    simpa [T', ContinuousLinearMap.sub_apply] using h
  have hzero :
      Filter.Tendsto (fun n => T' n (u n)) atTop (nhds 0) :=
    tempered_apply_tendsto_zero_of_tendsto hT' hu
  have hSu : Filter.Tendsto (fun n => S (u n)) atTop (nhds (S f)) :=
    S.continuous.tendsto f |>.comp hu
  have hsplit : (fun n => T n (u n)) = fun n => T' n (u n) + S (u n) := by
    funext n
    dsimp [T']
    simp
  rw [hsplit]
  simpa using hzero.add hSu

/-- Filter-version Banach-Steinhaus payoff for a nonzero pointwise limit.

If `Tᵢ → S` pointwise on Schwartz space along a countably generated filter `l`,
and `uᵢ → f` in the Schwartz topology along `l`, then `Tᵢ (uᵢ) → S f` along `l`. -/
theorem tempered_apply_tendsto_of_tendsto_filter
    [CompleteSpace F] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    {T : α → SchwartzMap E F →L[ℝ] G}
    {S : SchwartzMap E F →L[ℝ] G}
    (hT : ∀ f : SchwartzMap E F, Filter.Tendsto (fun a => T a f) l (nhds (S f)))
    {u : α → SchwartzMap E F} {f : SchwartzMap E F}
    (hu : Filter.Tendsto u l (nhds f)) :
    Filter.Tendsto (fun a => T a (u a)) l (nhds (S f)) := by
  let T' : α → SchwartzMap E F →L[ℝ] G := fun a => T a - S
  have hT' : ∀ g : SchwartzMap E F,
      Filter.Tendsto (fun a => T' a g) l (nhds 0) := by
    intro g
    have h : Filter.Tendsto (fun a => T a g - S g) l (nhds (S g - S g)) :=
      (hT g).sub tendsto_const_nhds
    simpa [T', ContinuousLinearMap.sub_apply] using h
  have hzero :
      Filter.Tendsto (fun a => T' a (u a)) l (nhds 0) :=
    tempered_apply_tendsto_zero_of_tendsto_filter hT' hu
  have hSu : Filter.Tendsto (fun a => S (u a)) l (nhds (S f)) :=
    S.continuous.tendsto f |>.comp hu
  have hsplit : (fun a => T a (u a)) = fun a => T' a (u a) + S (u a) := by
    funext a
    dsimp [T']
    simp
  rw [hsplit]
  simpa using hzero.add hSu

end SchwartzMap

end
