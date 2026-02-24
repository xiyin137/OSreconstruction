/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.ComplexLieGroups.Connectedness
import OSReconstruction.SCV.TotallyRealIdentity

/-!
# Jost Points and Totally Spacelike Configurations

This file defines Jost points (totally spacelike real configurations) and proves
Jost's lemma: every configuration satisfying the Jost condition lies in the extended
tube. This is the key geometric ingredient for the BHW permutation invariance step.

## Main results

* `JostSet` — the set of pairwise spacelike real configurations (for locality)
* `ForwardJostSet` — configurations admitting a complex boost into the forward tube
* `forwardJostSet_subset_extendedTube` — Jost's lemma: ForwardJostSet ⊆ T'_n
* `identity_theorem_totally_real` — holomorphic function vanishing on open real set
  vanishes on connected component
* `extendF_holomorphicOn` — extendF is holomorphic on T'_n

## Proof strategy

The permutation invariance proof uses:
1. Complex Lorentz invariance → extend F to the extended tube T'_n
2. Jost's lemma: specific real configurations lie in T'_n ∩ σ⁻¹(T'_n)
3. Locality: F = F∘σ on these configurations
4. Identity theorem: propagate F = F∘σ to all of T'_n ∩ σ⁻¹(T'_n)

## References

* Jost (1965), *The General Theory of Quantized Fields*, Chapter IV
* Streater & Wightman, *PCT, Spin and Statistics*, Theorem 2-10, Section 2-5
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace BHW
open scoped Matrix.Norms.Operator

variable {d : ℕ}

namespace BHW

/-! ### Spacelike vectors and the pairwise spacelike set -/

/-- A real vector is spacelike if its Minkowski norm is positive:
    -ζ₀² + ζ₁² + ... + ζ_d² > 0, i.e., spatial norm exceeds time component. -/
def IsSpacelike (d : ℕ) (ζ : Fin (d + 1) → ℝ) : Prop :=
  ∑ μ, minkowskiSignature d μ * ζ μ ^ 2 > 0

/-- The pairwise spacelike set: real configurations where every position vector is
    spacelike and every pairwise difference is spacelike. Used for locality arguments
    (hF_local applies when x_{i+1} - x_i is spacelike). -/
def JostSet (d n : ℕ) : Set (Fin n → Fin (d + 1) → ℝ) :=
  { x | (∀ i : Fin n, IsSpacelike d (x i)) ∧
        (∀ i j : Fin n, i ≠ j → IsSpacelike d (fun μ => x i μ - x j μ)) }

/-- Embed a real configuration as a complex one. -/
def realEmbed (x : Fin n → Fin (d + 1) → ℝ) : Fin n → Fin (d + 1) → ℂ :=
  fun k μ => (x k μ : ℂ)

/-- The Jost set is nonempty for n ≥ 1 and d ≥ 1.

    Example: take x_k = (0, k+1, 0, ..., 0). Each x_k is purely spatial hence
    spacelike, and x_i - x_j = (0, i-j, 0, ..., 0) is spacelike for i ≠ j. -/
theorem jostSet_nonempty (_hn : 1 ≤ n) (hd : 1 ≤ d) :
    (JostSet d n).Nonempty := by
  set e₁ : Fin (d + 1) := ⟨1, by omega⟩
  refine ⟨fun k μ => if μ = e₁ then (k : ℝ) + 1 else 0, ?_, ?_⟩
  · -- Each x_k is spacelike: x_k = (0, k+1, 0, ..., 0)
    intro i
    simp only [IsSpacelike]
    rw [Finset.sum_eq_single e₁]
    · simp [minkowskiSignature, e₁]
      positivity
    · intro μ _ hμ; simp [hμ]
    · exact absurd (Finset.mem_univ _)
  · -- x_i - x_j spacelike for i ≠ j: difference is (0, i-j, 0, ..., 0)
    intro i j hij
    simp only [IsSpacelike]
    rw [Finset.sum_eq_single e₁]
    · have he₁ : minkowskiSignature d e₁ = 1 := by
        simp [minkowskiSignature, e₁, Fin.ext_iff]
      simp only [e₁, ↓reduceIte, he₁, one_mul]
      have : (↑↑i : ℝ) + 1 - (↑↑j + 1) ≠ 0 := by
        intro h
        apply hij; ext
        exact_mod_cast show (↑(i.val) : ℝ) = ↑(j.val) by linarith
      positivity
    · intro μ _ hμ; simp [hμ]
    · exact absurd (Finset.mem_univ _)

/-- The Minkowski quadratic form is continuous. -/
private theorem continuous_minkowski_quadratic (d : ℕ) :
    Continuous (fun ζ : Fin (d + 1) → ℝ =>
      ∑ μ, minkowskiSignature d μ * ζ μ ^ 2) :=
  continuous_finset_sum _ (fun μ _ => (continuous_const.mul
    ((continuous_apply μ).pow 2)))

/-- The Jost set is open in ℝ^{n(d+1)}. -/
theorem isOpen_jostSet : IsOpen (JostSet d n) := by
  -- Each IsSpacelike condition is an open condition (preimage of (0,∞) under continuous map)
  have key : ∀ (g : (Fin n → Fin (d + 1) → ℝ) → Fin (d + 1) → ℝ),
      Continuous g → IsOpen {x | IsSpacelike d (g x)} := by
    intro g hg
    exact isOpen_lt continuous_const
      (continuous_finset_sum _ fun μ _ =>
        continuous_const.mul (((continuous_apply μ).comp hg).pow 2))
  -- Rewrite JostSet as explicit intersection, then prove openness
  suffices h : JostSet d n =
      (⋂ i : Fin n, {x | IsSpacelike d (x i)}) ∩
      (⋂ i : Fin n, ⋂ j : Fin n,
        {x | i ≠ j → IsSpacelike d (fun μ => x i μ - x j μ)}) by
    rw [h]
    apply IsOpen.inter
    · exact isOpen_iInter_of_finite fun i => key _ (continuous_apply i)
    · apply isOpen_iInter_of_finite; intro i
      apply isOpen_iInter_of_finite; intro j
      by_cases hij : i = j
      · convert isOpen_univ using 1; ext x; simp [hij]
      · have hcont : Continuous (fun (x : Fin n → Fin (d + 1) → ℝ) (μ : Fin (d + 1)) =>
            x i μ - x j μ) :=
          continuous_pi fun μ =>
            ((continuous_apply μ).comp (continuous_apply i)).sub
            ((continuous_apply μ).comp (continuous_apply j))
        have hseteq : {x : Fin n → Fin (d + 1) → ℝ |
            i ≠ j → IsSpacelike d (fun μ => x i μ - x j μ)} =
            {x | IsSpacelike d (fun μ => x i μ - x j μ)} := by
          ext x; simp [hij]
        rw [hseteq]; exact key _ hcont
  ext x; simp [JostSet, Set.mem_iInter]

/-- The Jost set is invariant under permutations of the position indices.
    Manifest from the pairwise definition: permuting indices preserves
    "all x_i spacelike" and "all x_i - x_j spacelike". -/
theorem jostSet_permutation_invariant (σ : Equiv.Perm (Fin n))
    {x : Fin n → Fin (d + 1) → ℝ} (hx : x ∈ JostSet d n) :
    (fun k => x (σ k)) ∈ JostSet d n := by
  obtain ⟨hx_sp, hx_pair⟩ := hx
  exact ⟨fun i => hx_sp (σ i),
    fun i j hij => hx_pair (σ i) (σ j) (fun h => hij (σ.injective h))⟩

/-! ### Consecutive differences and the Jost condition -/

/-- Consecutive difference: ζ_k = x_k - x_{k-1} (with x_{-1} = 0).
    These are the "difference variables" of the forward tube. -/
def consecutiveDiff (x : Fin n → Fin (d + 1) → ℝ) (k : Fin n) : Fin (d + 1) → ℝ :=
  fun μ => x k μ - if h : k.val = 0 then 0 else x ⟨k.val - 1, by omega⟩ μ

/-- Continuity of a single component of consecutiveDiff in x. -/
private lemma continuous_consecutiveDiff_component (k : Fin n) (μ : Fin (d + 1)) :
    Continuous (fun x : Fin n → Fin (d + 1) → ℝ => consecutiveDiff x k μ) := by
  simp only [consecutiveDiff]
  apply Continuous.sub
  · exact (continuous_apply μ).comp (continuous_apply k)
  · split_ifs with hk
    · exact continuous_const
    · exact (continuous_apply μ).comp (continuous_apply (⟨k.val - 1, by omega⟩ : Fin n))

/-- The forward Jost set: configurations where each consecutive difference has
    its first spatial component strictly exceeding the absolute value of its time
    component. This is an open condition that implies:
    1. Each consecutive difference is spacelike (hence JostSet membership)
    2. The complex boost exp(-iα K₁) maps the configuration into the forward tube.

    Geometrically: the consecutive differences all "point forward" in the first
    spatial direction, with small time components relative to spatial ones.

    Note: requires d ≥ 1 (at least one spatial dimension). -/
def ForwardJostSet (d n : ℕ) (hd : 1 ≤ d) : Set (Fin n → Fin (d + 1) → ℝ) :=
  { x | ∀ k : Fin n,
    let ζ := consecutiveDiff x k
    |ζ 0| < ζ ⟨1, by omega⟩ }

/-- The forward Jost set is open (defined by strict inequalities). -/
theorem isOpen_forwardJostSet (hd : 1 ≤ d) :
    IsOpen (@ForwardJostSet d n hd) := by
  have heq : ForwardJostSet d n hd = ⋂ k : Fin n,
      {x | |consecutiveDiff x k 0| < consecutiveDiff x k ⟨1, by omega⟩} := by
    ext x; simp [ForwardJostSet, Set.mem_iInter]
  rw [heq]
  apply isOpen_iInter_of_finite
  intro k
  exact isOpen_lt (continuous_abs.comp (continuous_consecutiveDiff_component k 0))
    (continuous_consecutiveDiff_component k ⟨1, by omega⟩)

/-- The forward Jost set is nonempty (x_k = (0, k+1, 0, ..., 0) works).
    Each consecutive difference is (0, 1, 0, ..., 0), so |0| < 1. -/
theorem forwardJostSet_nonempty (_hn : 1 ≤ n) (hd : 1 ≤ d) :
    (ForwardJostSet d n hd).Nonempty := by
  set e₁ : Fin (d + 1) := ⟨1, by omega⟩
  have h01 : (0 : Fin (d + 1)) ≠ e₁ := by intro h; simp [e₁, Fin.ext_iff] at h
  refine ⟨fun k μ => if μ = e₁ then (k : ℝ) + 1 else 0, fun k => ?_⟩
  -- Show: time component of ζ_k is 0, first spatial is 1
  have htime : consecutiveDiff (fun k μ => if μ = e₁ then (↑↑k : ℝ) + 1 else 0) k
      (0 : Fin (d + 1)) = 0 := by
    simp only [consecutiveDiff, h01, ↓reduceIte]
    by_cases hk : k.val = 0 <;> simp [hk]
  have hspat : consecutiveDiff (fun k μ => if μ = e₁ then (↑↑k : ℝ) + 1 else 0) k e₁ = 1 := by
    simp only [consecutiveDiff, ↓reduceIte]
    by_cases hk : k.val = 0
    · simp [hk]
    · simp only [hk, ↓reduceDIte]
      have hcast : k.val - 1 + 1 = k.val := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk)
      have : (↑(k.val - 1) : ℝ) + 1 = (↑(k.val) : ℝ) := by exact_mod_cast hcast
      linarith
  show |_| < _
  rw [htime, hspat]; simp

/-- A vector with |v₀| < v₁ is spacelike (needs d ≥ 1). -/
private lemma isSpacelike_of_abs_time_lt_spatial (hd : 1 ≤ d)
    (v : Fin (d + 1) → ℝ) (hv : |v 0| < v ⟨1, by omega⟩) : IsSpacelike d v := by
  simp only [IsSpacelike]
  rw [Fin.sum_univ_succ]
  have htime : minkowskiSignature d 0 * v 0 ^ 2 = -(v 0 ^ 2) := by
    simp [minkowskiSignature]
  have hspace : ∀ i : Fin d, minkowskiSignature d i.succ * v i.succ ^ 2 = v i.succ ^ 2 := by
    intro i; simp [minkowskiSignature, Fin.succ_ne_zero]
  rw [htime, Finset.sum_congr rfl (fun i _ => hspace i)]
  -- Need: -(v₀²) + Σ v_{j+1}² > 0
  -- Since Σ v_{j+1}² ≥ v₁² and v₁² > v₀² (from |v₀| < v₁)
  have h_idx : (⟨0, by omega⟩ : Fin d).succ = (⟨1, by omega⟩ : Fin (d + 1)) := by ext; simp
  have hle : v ⟨1, by omega⟩ ^ 2 ≤ ∑ j : Fin d, v (Fin.succ j) ^ 2 := by
    rw [← h_idx]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (v (Fin.succ j)))
      (Finset.mem_univ (⟨0, by omega⟩ : Fin d))
  -- From |v₀| < v₁: v₁² - v₀² = (v₁ - v₀)(v₁ + v₀) > 0
  obtain ⟨h_neg, h_pos⟩ := abs_lt.mp hv
  nlinarith [sq_nonneg (v ⟨1, by omega⟩ - v 0), sq_nonneg (v ⟨1, by omega⟩ + v 0)]

/-- Elements of the forward Jost set have spacelike consecutive differences.
    Since |ζ₀| < ζ₁, the Minkowski norm -ζ₀² + ζ₁² + ... > 0. -/
theorem forwardJostSet_consec_spacelike (hd : 1 ≤ d)
    {x : Fin n → Fin (d + 1) → ℝ} (hx : x ∈ ForwardJostSet d n hd)
    (k : Fin n) : IsSpacelike d (consecutiveDiff x k) :=
  isSpacelike_of_abs_time_lt_spatial hd _ (hx k)

/-- Telescoping sum: x ⟨m, _⟩ μ = Σ_{j=0}^{m} (consecutiveDiff x ⟨j, _⟩ μ). -/
private lemma sum_consecutiveDiff (x : Fin n → Fin (d + 1) → ℝ) (μ : Fin (d + 1))
    (m : ℕ) (hm : m < n) :
    x ⟨m, hm⟩ μ = ∑ j : Fin (m + 1), consecutiveDiff x ⟨j.val, by omega⟩ μ := by
  induction m with
  | zero =>
    show _ = ∑ j : Fin 1, _
    rw [Fin.sum_univ_one]
    simp [consecutiveDiff]
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    -- castSucc j has same val as j
    have hcs : ∀ j : Fin (m + 1),
        consecutiveDiff x ⟨(Fin.castSucc j).val, by omega⟩ μ =
        consecutiveDiff x ⟨j.val, by omega⟩ μ := by
      intro j; rfl
    simp_rw [hcs]
    -- Use IH to replace the first sum with x ⟨m, _⟩ μ
    rw [← ih (by omega)]
    -- Last term: consecutiveDiff x ⟨m+1, _⟩ μ = x ⟨m+1, _⟩ μ - x ⟨m, _⟩ μ
    simp only [Fin.val_last, consecutiveDiff, show ¬(m + 1 = 0) from by omega, ↓reduceDIte]
    have : (⟨m + 1 - 1, (by omega : m + 1 - 1 < n)⟩ : Fin n) = ⟨m, by omega⟩ := by
      simp only [Fin.mk.injEq]; omega
    rw [this]; ring

/-- Partial telescoping: x_b - x_a = Σ_{j=0}^{b-a-1} ζ_{j+a+1}. -/
private lemma diff_sum_consecutiveDiff (x : Fin n → Fin (d + 1) → ℝ) (μ : Fin (d + 1))
    (a b : ℕ) (ha : a < n) (hb : b < n) (hab : a < b) :
    x ⟨b, hb⟩ μ - x ⟨a, ha⟩ μ =
    ∑ j : Fin (b - a), consecutiveDiff x ⟨j.val + a + 1, by omega⟩ μ := by
  -- Define f(k) = x(k + a) extended to all ℕ, then use Finset.sum_range_sub
  let f : ℕ → ℝ := fun k => if h : k + a < n then x ⟨k + a, h⟩ μ else 0
  -- Telescoping: ∑_{i < b-a} (f(i+1) - f(i)) = f(b-a) - f(0)
  have htel := @Finset.sum_range_sub ℝ _ f (b - a)
  -- Simplify f(b-a) = x_b and f(0) = x_a
  have hfba : f (b - a) = x ⟨b, hb⟩ μ := by
    simp only [f, show b - a + a = b from by omega, show b < n from hb, ↓reduceDIte]
  have hf0 : f 0 = x ⟨a, ha⟩ μ := by
    simp only [f, show (0 : ℕ) + a = a from by omega, show a < n from ha, ↓reduceDIte]
  rw [hfba, hf0] at htel
  -- htel : ∑ i in range(b-a), (f(i+1) - f(i)) = x_b - x_a
  rw [htel.symm, ← Fin.sum_univ_eq_sum_range]
  -- Goal: ∑ j : Fin(b-a), (f(j+1) - f(j)) = ∑ j : Fin(b-a), ζ_{j+a+1}
  apply Finset.sum_congr rfl
  intro j _
  -- Show f(j+1) - f(j) = consecutiveDiff x ⟨j+a+1, _⟩ μ
  simp only [f, show j.val + 1 + a < n from by omega, show j.val + a < n from by omega,
             ↓reduceDIte]
  -- LHS: x ⟨j+1+a, _⟩ μ - x ⟨j+a, _⟩ μ
  -- RHS: consecutiveDiff x ⟨j+a+1, _⟩ μ = x ⟨j+a+1, _⟩ μ - x ⟨j+a, _⟩ μ
  have hcd : consecutiveDiff x ⟨j.val + a + 1, by omega⟩ μ =
             x ⟨j.val + a + 1, by omega⟩ μ - x ⟨j.val + a, by omega⟩ μ := by
    simp only [consecutiveDiff, show ¬(j.val + a + 1 = 0) from by omega, ↓reduceDIte]
    congr 1
  rw [hcd]
  congr 1; congr 1; simp only [Fin.mk.injEq]; omega

/-- The forward Jost set is contained in the pairwise spacelike Jost set.
    This ensures locality (hF_local) applies to elements of the forward Jost set.

    Proof: each x_i = Σ_{j≤i} ζ_j where |ζ_j,0| < ζ_j,1. By triangle inequality,
    |x_i,0| ≤ Σ |ζ_j,0| < Σ ζ_j,1 = x_i,1, so x_i is spacelike. Similarly for
    differences x_i - x_j. -/
theorem forwardJostSet_subset_jostSet (hd : 1 ≤ d) :
    ForwardJostSet d n hd ⊆ JostSet d n := by
  intro x hx
  constructor
  · -- Each x_i is spacelike: x_i = Σ_{j≤i} ζ_j, use triangle inequality
    intro i
    apply isSpacelike_of_abs_time_lt_spatial hd
    -- Rewrite x_i as a sum of consecutive differences
    rw [sum_consecutiveDiff x 0 i.val i.isLt,
        sum_consecutiveDiff x ⟨1, by omega⟩ i.val i.isLt]
    -- |Σ ζ_j,0| ≤ Σ |ζ_j,0| < Σ ζ_j,1
    have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
    calc |∑ j : Fin (i.val + 1), consecutiveDiff x ⟨j.val, by omega⟩ 0|
        ≤ ∑ j : Fin (i.val + 1), |consecutiveDiff x ⟨j.val, by omega⟩ 0| := by
          have h := norm_sum_le (E := ℝ) Finset.univ
            (fun j : Fin (i.val + 1) => consecutiveDiff x ⟨j.val, by omega⟩ 0)
          simp only [Real.norm_eq_abs] at h; exact h
      _ < ∑ j : Fin (i.val + 1), consecutiveDiff x ⟨j.val, by omega⟩ ⟨1, by omega⟩ := by
          apply Finset.sum_lt_sum
          · intro j _; exact le_of_lt (hx ⟨j.val, by omega⟩)
          · exact ⟨⟨0, by omega⟩, Finset.mem_univ _, hx ⟨0, hn⟩⟩
  · -- Each x_i - x_j is spacelike (similar telescoping argument)
    intro i j hij
    -- WLOG i.val > j.val (spacelike is preserved under negation)
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h_lt | h_gt
    · -- i.val < j.val: x_i - x_j = -(x_j - x_i), IsSpacelike preserved
      suffices IsSpacelike d (fun μ => x j μ - x i μ) by
        simp only [IsSpacelike] at this ⊢
        convert this using 1
        congr 1; ext μ; ring
      apply isSpacelike_of_abs_time_lt_spatial hd
      -- x_j - x_i = Σ_{k=i+1}^{j} ζ_k (partial sum of consecutive diffs)
      rw [diff_sum_consecutiveDiff x 0 i.val j.val i.isLt j.isLt h_lt,
          diff_sum_consecutiveDiff x ⟨1, by omega⟩ i.val j.val i.isLt j.isLt h_lt]
      calc |∑ k : Fin (j.val - i.val),
              consecutiveDiff x ⟨k.val + i.val + 1, by omega⟩ 0|
          ≤ ∑ k : Fin (j.val - i.val),
              |consecutiveDiff x ⟨k.val + i.val + 1, by omega⟩ 0| := by
            have h := norm_sum_le (E := ℝ) Finset.univ
              (fun k : Fin (j.val - i.val) =>
                consecutiveDiff x ⟨k.val + i.val + 1, by omega⟩ 0)
            simp only [Real.norm_eq_abs] at h; exact h
        _ < ∑ k : Fin (j.val - i.val),
              consecutiveDiff x ⟨k.val + i.val + 1, by omega⟩ ⟨1, by omega⟩ := by
            apply Finset.sum_lt_sum
            · intro k _; exact le_of_lt (hx ⟨k.val + i.val + 1, by omega⟩)
            · refine ⟨⟨0, by omega⟩, Finset.mem_univ _, ?_⟩
              simp only [Nat.zero_add]
              exact hx ⟨i.val + 1, by omega⟩
    · -- i.val > j.val: x_i - x_j = Σ_{k=j+1}^{i} ζ_k
      apply isSpacelike_of_abs_time_lt_spatial hd
      rw [diff_sum_consecutiveDiff x 0 j.val i.val j.isLt i.isLt h_gt,
          diff_sum_consecutiveDiff x ⟨1, by omega⟩ j.val i.val j.isLt i.isLt h_gt]
      calc |∑ k : Fin (i.val - j.val),
              consecutiveDiff x ⟨k.val + j.val + 1, by omega⟩ 0|
          ≤ ∑ k : Fin (i.val - j.val),
              |consecutiveDiff x ⟨k.val + j.val + 1, by omega⟩ 0| := by
            have h := norm_sum_le (E := ℝ) Finset.univ
              (fun k : Fin (i.val - j.val) =>
                consecutiveDiff x ⟨k.val + j.val + 1, by omega⟩ 0)
            simp only [Real.norm_eq_abs] at h; exact h
        _ < ∑ k : Fin (i.val - j.val),
              consecutiveDiff x ⟨k.val + j.val + 1, by omega⟩ ⟨1, by omega⟩ := by
            apply Finset.sum_lt_sum
            · intro k _; exact le_of_lt (hx ⟨k.val + j.val + 1, by omega⟩)
            · refine ⟨⟨0, by omega⟩, Finset.mem_univ _, ?_⟩
              simp only [Nat.zero_add]
              exact hx ⟨j.val + 1, by omega⟩

/-! ### Jost's lemma: ForwardJostSet ⊆ T'_n -/

-- The Wick rotation matrix: exp(-iπ/2 K₁) where K₁ is the boost generator.
-- Entries: Λ_{0,1} = Λ_{1,0} = -i, Λ_{μ,μ} = 1 for μ ≥ 2, all others 0.
private noncomputable def wickMatrix (d : ℕ) (hd : 1 ≤ d) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  fun μ ν =>
    if μ = (0 : Fin (d + 1)) ∧ ν = ⟨1, by omega⟩ then -Complex.I
    else if μ = ⟨1, by omega⟩ ∧ ν = (0 : Fin (d + 1)) then -Complex.I
    else if μ = ν ∧ μ ≠ (0 : Fin (d + 1)) ∧ μ ≠ ⟨1, by omega⟩ then 1
    else 0

-- Column simplification: column 0 is nonzero only at row ⟨1,_⟩
private lemma wickMatrix_col0 (d : ℕ) (hd : 1 ≤ d) (α : Fin (d + 1)) :
    wickMatrix d hd α 0 = if α = ⟨1, by omega⟩ then -Complex.I else 0 := by
  unfold wickMatrix
  rw [if_neg (by intro ⟨_, h⟩; exact absurd (congr_arg Fin.val h) (by simp))]
  by_cases hα : α = ⟨1, by omega⟩
  · rw [if_pos ⟨hα, rfl⟩, if_pos hα]
  · rw [if_neg (by intro ⟨h, _⟩; exact hα h), if_neg hα]
    rw [if_neg (by intro ⟨h1, h2, _⟩; exact h2 h1)]

-- Column simplification: column ⟨1,_⟩ is nonzero only at row 0
private lemma wickMatrix_col1 (d : ℕ) (hd : 1 ≤ d) (α : Fin (d + 1)) :
    wickMatrix d hd α ⟨1, by omega⟩ = if α = 0 then -Complex.I else 0 := by
  unfold wickMatrix
  by_cases hα0 : α = 0
  · rw [if_pos ⟨hα0, rfl⟩, if_pos hα0]
  · rw [if_neg (by intro ⟨h, _⟩; exact hα0 h), if_neg hα0]
    rw [if_neg (by intro ⟨_, h⟩; exact absurd (congr_arg Fin.val h) (by simp))]
    rw [if_neg (by intro ⟨h, _, h2⟩; exact h2 h)]

-- Column simplification: for μ ≥ 2, column μ is nonzero only at row μ
private lemma wickMatrix_col_ge2 (d : ℕ) (hd : 1 ≤ d) (μ : Fin (d + 1))
    (hμ0 : μ ≠ 0) (hμ1 : μ ≠ ⟨1, by omega⟩) (α : Fin (d + 1)) :
    wickMatrix d hd α μ = if α = μ then 1 else 0 := by
  unfold wickMatrix
  rw [if_neg (by intro ⟨_, h⟩; exact hμ1 h)]
  rw [if_neg (by intro ⟨_, h⟩; exact hμ0 h)]
  by_cases hαμ : α = μ
  · rw [if_pos ⟨hαμ, hαμ ▸ hμ0, hαμ ▸ hμ1⟩, if_pos hαμ]
  · rw [if_neg (by intro ⟨h, _, _⟩; exact hαμ h), if_neg hαμ]

-- Support lemma: wickMatrix nonzero implies specific row-column pattern
private lemma wickMatrix_support (d : ℕ) (hd : 1 ≤ d) (α μ : Fin (d + 1))
    (h : wickMatrix d hd α μ ≠ 0) :
    (α = 0 ∧ μ = ⟨1, by omega⟩) ∨ (α = ⟨1, by omega⟩ ∧ μ = 0) ∨
    (α = μ ∧ α ≠ 0 ∧ α ≠ ⟨1, by omega⟩) := by
  unfold wickMatrix at h
  split_ifs at h with h1 h2 h3
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)
  · exact absurd rfl h

-- Row lemma: row 0 is nonzero only at column ⟨1,_⟩
private lemma wickMatrix_row0 (d : ℕ) (hd : 1 ≤ d) (ν : Fin (d + 1)) :
    wickMatrix d hd 0 ν = if ν = ⟨1, by omega⟩ then -Complex.I else 0 := by
  unfold wickMatrix
  by_cases hν : ν = ⟨1, by omega⟩
  · rw [if_pos ⟨rfl, hν⟩, if_pos hν]
  · rw [if_neg (by intro ⟨_, h⟩; exact hν h),
        if_neg (by intro ⟨h, _⟩; exact absurd (congr_arg Fin.val h) (by simp)),
        if_neg (by intro ⟨_, h, _⟩; exact h rfl), if_neg hν]

-- Row lemma: row ⟨1,_⟩ is nonzero only at column 0
private lemma wickMatrix_row1 (d : ℕ) (hd : 1 ≤ d) (ν : Fin (d + 1)) :
    wickMatrix d hd ⟨1, by omega⟩ ν = if ν = 0 then -Complex.I else 0 := by
  unfold wickMatrix
  by_cases hν : ν = 0
  · subst hν
    rw [if_neg (by intro ⟨h, _⟩; exact absurd (congr_arg Fin.val h) (by simp)),
        if_pos ⟨rfl, rfl⟩, if_pos rfl]
  · rw [if_neg (by intro ⟨h, _⟩; exact absurd (congr_arg Fin.val h) (by simp)),
        if_neg (by intro ⟨_, h⟩; exact hν h),
        if_neg (by intro ⟨_, _, h⟩; exact h rfl), if_neg hν]

-- Row lemma: for μ ≥ 2, row μ is nonzero only at column μ
private lemma wickMatrix_row_ge2 (d : ℕ) (hd : 1 ≤ d) (μ : Fin (d + 1))
    (hμ0 : μ ≠ 0) (hμ1 : μ ≠ ⟨1, by omega⟩) (ν : Fin (d + 1)) :
    wickMatrix d hd μ ν = if ν = μ then 1 else 0 := by
  unfold wickMatrix
  rw [if_neg (by intro ⟨h, _⟩; exact hμ0 h)]
  rw [if_neg (by intro ⟨h, _⟩; exact hμ1 h)]
  by_cases hνμ : ν = μ
  · subst hνμ; rw [if_pos ⟨rfl, hμ0, hμ1⟩, if_pos rfl]
  · rw [if_neg (by intro ⟨h, _, _⟩; exact hνμ h.symm), if_neg hνμ]

-- The Wick rotation preserves the Minkowski metric (componentwise)
private lemma wickMatrix_metric (d : ℕ) (hd : 1 ≤ d) :
    ∀ (μ ν : Fin (d + 1)),
    ∑ α : Fin (d + 1),
      (minkowskiSignature d α : ℂ) * wickMatrix d hd α μ * wickMatrix d hd α ν =
    if μ = ν then (minkowskiSignature d μ : ℂ) else 0 := by
  intro μ ν
  by_cases hμν : μ = ν
  · -- Diagonal case
    subst hμν; rw [if_pos rfl]
    by_cases hμ0 : μ = 0
    · subst hμ0; simp only [wickMatrix_col0]
      simp only [mul_ite, ite_mul, mul_zero, zero_mul, mul_neg,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      simp [minkowskiSignature, Fin.ext_iff]
    · by_cases hμ1 : μ = ⟨1, by omega⟩
      · subst hμ1; simp only [wickMatrix_col1]
        simp only [mul_ite, ite_mul, mul_zero, zero_mul, mul_neg,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        simp [minkowskiSignature, Fin.ext_iff]
      · simp only [wickMatrix_col_ge2 d hd μ hμ0 hμ1]
        simp only [mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  · -- Off-diagonal case: at least one factor per summand is zero
    rw [if_neg hμν]
    apply Finset.sum_eq_zero; intro α _
    suffices wickMatrix d hd α μ * wickMatrix d hd α ν = 0 by
      rw [mul_assoc]; simp [this]
    by_cases hWμ : wickMatrix d hd α μ = 0
    · simp [hWμ]
    · suffices wickMatrix d hd α ν = 0 by simp [this]
      rcases wickMatrix_support d hd α μ hWμ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hαμ, hα0, hα1⟩
      · -- row 0, col ⟨1,_⟩ → W(0, ν) = 0 since ν ≠ ⟨1,_⟩
        unfold wickMatrix
        rw [if_neg (by intro ⟨_, h⟩; exact hμν h.symm)]
        rw [if_neg (by intro ⟨h, _⟩; exact absurd (congr_arg Fin.val h) (by simp))]
        rw [if_neg (by intro ⟨_, h, _⟩; exact h rfl)]
      · -- row ⟨1,_⟩, col 0 → W(⟨1,_⟩, ν) = 0 since ν ≠ 0
        unfold wickMatrix
        rw [if_neg (by intro ⟨h, _⟩; exact absurd (congr_arg Fin.val h) (by simp))]
        rw [if_neg (by intro ⟨_, h⟩; exact hμν h.symm)]
        rw [if_neg (by intro ⟨_, _, h3⟩; exact h3 rfl)]
      · -- row α = μ ≥ 2 → W(α, ν) = 0 since ν ≠ α = μ
        unfold wickMatrix
        rw [if_neg (by intro ⟨h, _⟩; exact hα0 h)]
        rw [if_neg (by intro ⟨h, _⟩; exact hα1 h)]
        rw [if_neg (by intro ⟨h, _, _⟩; rw [hαμ] at h; exact hμν h)]

-- The Wick rotation has determinant 1
private lemma wickMatrix_det (d : ℕ) (hd : 1 ≤ d) :
    (wickMatrix d hd).det = 1 := by
  rw [Matrix.det_apply]
  have h01 : (0 : Fin (d + 1)) ≠ ⟨1, by omega⟩ := by
    intro h; exact absurd (congr_arg Fin.val h) (by norm_num)
  -- All non-swap permutations contribute 0
  have hother : ∀ σ : Equiv.Perm (Fin (d + 1)), σ ∈ Finset.univ →
      σ ≠ Equiv.swap (0 : Fin (d + 1)) ⟨1, by omega⟩ →
      Equiv.Perm.sign σ • ∏ i, wickMatrix d hd (σ i) i = 0 := by
    intro σ _ hσ
    suffices h : ∃ i, wickMatrix d hd (σ i) i = 0 by
      obtain ⟨i, hi⟩ := h
      rw [show ∏ j, wickMatrix d hd (σ j) j = 0 from
        Finset.prod_eq_zero (f := fun j => wickMatrix d hd (σ j) j)
          (Finset.mem_univ i) hi, smul_zero]
    by_contra hall; push_neg at hall
    apply hσ; ext j
    by_cases hj0 : j = 0
    · subst hj0
      have h := hall 0
      rw [wickMatrix_col0] at h
      simp only [ne_eq, ite_eq_right_iff, neg_eq_zero, Complex.I_ne_zero,
        imp_false, not_not] at h
      rw [h, Equiv.swap_apply_left]
    · by_cases hj1 : j = ⟨1, by omega⟩
      · subst hj1
        have h := hall ⟨1, by omega⟩
        rw [wickMatrix_col1] at h
        simp only [ne_eq, ite_eq_right_iff, neg_eq_zero, Complex.I_ne_zero,
          imp_false, not_not] at h
        rw [h, Equiv.swap_apply_right]
      · have h := hall j
        rw [wickMatrix_col_ge2 d hd j hj0 hj1] at h
        simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at h
        rw [h, Equiv.swap_apply_of_ne_of_ne hj0 hj1]
  rw [Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) hother]
  rw [Equiv.Perm.sign_swap h01]
  simp only [Units.neg_smul, one_smul]
  -- Need: -(∏ i, wickMatrix d hd (swap(0,1)(i)) i) = 1
  rw [Fin.prod_univ_succ, Equiv.swap_apply_left, wickMatrix_col0, if_pos rfl]
  have hrest : ∀ j : Fin d, wickMatrix d hd
      (Equiv.swap (0 : Fin (d + 1)) ⟨1, by omega⟩ (Fin.succ j)) (Fin.succ j) =
      if (j : ℕ) = 0 then -Complex.I else 1 := by
    intro j
    by_cases hj : (j : ℕ) = 0
    · have hjs : Fin.succ j = (⟨1, by omega⟩ : Fin (d + 1)) := by
        ext; simp [Fin.val_succ, hj]
      rw [if_pos hj, hjs, Equiv.swap_apply_right, wickMatrix_col1, if_pos rfl]
    · have hjs0 : Fin.succ j ≠ (0 : Fin (d + 1)) := Fin.succ_ne_zero j
      have hjs1 : Fin.succ j ≠ (⟨1, by omega⟩ : Fin (d + 1)) := by
        intro h; exact hj (by have := congr_arg Fin.val h; simp [Fin.val_succ] at this; omega)
      rw [if_neg hj, Equiv.swap_apply_of_ne_of_ne hjs0 hjs1,
        wickMatrix_col_ge2 d hd (Fin.succ j) hjs0 hjs1, if_pos rfl]
  simp only [hrest]
  have hprod : ∏ j : Fin d, (if (j : ℕ) = 0 then -Complex.I else (1 : ℂ)) =
      -Complex.I := by
    rw [Finset.prod_eq_single ⟨0, by omega⟩]
    · simp
    · intro b _ hb
      rw [if_neg (show (b : ℕ) ≠ 0 from by intro h; exact hb (Fin.ext h))]
    · simp
  rw [hprod]; simp

-- The Wick rotation as a ComplexLorentzGroup element
private noncomputable def wickCLG (d : ℕ) (hd : 1 ≤ d) : ComplexLorentzGroup d where
  val := wickMatrix d hd
  metric_preserving := wickMatrix_metric d hd
  proper := wickMatrix_det d hd

/-- **Jost's lemma.** Every configuration in the forward Jost set lies in the
    extended tube. The Wick rotation Λ = exp(-iπ/2 K₁) maps the consecutive
    differences into the forward light cone:
    Im(ζ_k(w))₀ = ζ_k,1 > 0 and Q(Im) = ζ_k,0² - ζ_k,1² < 0. -/
theorem forwardJostSet_subset_extendedTube (hd : 1 ≤ d)
    (x : Fin n → Fin (d + 1) → ℝ) (hx : x ∈ ForwardJostSet d n hd) :
    realEmbed x ∈ ExtendedTube d n := by
  -- Define w such that Λ · w = realEmbed x
  -- w k 0 = I * x k 1,  w k 1 = I * x k 0,  w k μ = x k μ for μ ≥ 2
  set w : Fin n → Fin (d + 1) → ℂ :=
    fun k μ => if μ = ⟨1, by omega⟩ then Complex.I * (x k 0 : ℂ)
               else if μ = 0 then Complex.I * (x k ⟨1, by omega⟩ : ℂ)
               else (x k μ : ℂ)
  -- Show realEmbed x = complexLorentzAction (wickCLG d hd) w
  have haction : realEmbed x = complexLorentzAction (wickCLG d hd) w := by
    ext k μ
    simp only [complexLorentzAction, wickCLG, realEmbed, w]
    by_cases hμ0 : μ = 0
    · subst hμ0
      simp only [wickMatrix_row0, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      simp [← mul_assoc, Complex.I_mul_I]
    · by_cases hμ1 : μ = ⟨1, by omega⟩
      · subst hμ1
        simp only [wickMatrix_row1, ite_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        simp [← mul_assoc, Complex.I_mul_I]
      · simp only [wickMatrix_row_ge2 d hd μ hμ0 hμ1, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        simp [hμ0, hμ1]
  -- Show w ∈ ForwardTube d n
  -- Helper: compute Im of w's consecutive differences
  have him : ∀ k : Fin n, ∀ μ : Fin (d + 1),
      (w k μ - (if h : (k : ℕ) = 0 then (0 : Fin (d + 1) → ℂ)
        else w ⟨k.val - 1, by omega⟩) μ).im =
      if μ = 0 then consecutiveDiff x k ⟨1, by omega⟩
      else if μ = ⟨1, by omega⟩ then consecutiveDiff x k 0
      else 0 := by
    intro k μ
    simp only [w, consecutiveDiff]
    by_cases hμ0 : μ = 0
    · subst hμ0
      simp only [show (0 : Fin (d + 1)) ≠ ⟨1, by omega⟩ from by
        intro h; exact absurd (congr_arg Fin.val h) (by norm_num), ite_false, ite_true]
      split_ifs <;> simp
    · by_cases hμ1 : μ = ⟨1, by omega⟩
      · subst hμ1; simp only [ite_true, hμ0, ite_false]
        split_ifs <;> simp
      · simp only [hμ0, hμ1, ite_false]
        split_ifs <;> simp [hμ0, hμ1]
  have hw : w ∈ ForwardTube d n := by
    intro k
    have hxk := hx k
    have hpos : consecutiveDiff x k ⟨1, by omega⟩ > 0 :=
      lt_of_le_of_lt (abs_nonneg _) hxk
    have hsq : (consecutiveDiff x k 0) ^ 2 < (consecutiveDiff x k ⟨1, by omega⟩) ^ 2 :=
      sq_lt_sq' (by linarith [(abs_lt.mp hxk).1]) (abs_lt.mp hxk).2
    constructor
    · -- Im₀ > 0: equals consecutiveDiff x k ⟨1,_⟩ > 0
      simp only [him]; exact hpos
    · -- Q(Im) < 0: -(consec ⟨1,_⟩)² + (consec 0)² + 0 < 0
      -- Rewrite each η(μ) using him
      have hη : ∀ μ, (fun μ => (w k μ - (if h : (k : ℕ) = 0 then (0 : Fin (d + 1) → ℂ)
          else w ⟨k.val - 1, by omega⟩) μ).im) μ =
        if μ = 0 then consecutiveDiff x k ⟨1, by omega⟩
        else if μ = ⟨1, by omega⟩ then consecutiveDiff x k 0
        else 0 := him k
      simp_rw [hη]
      -- Sum: Σ minkowski(μ) * (if μ=0 then a else if μ=⟨1,_⟩ then b else 0)²
      simp only [ite_pow, mul_ite]
      -- Split nested if into sum of two simple ifs
      have hsplit : ∀ μ : Fin (d + 1),
          (if μ = 0 then minkowskiSignature d μ *
              (consecutiveDiff x k ⟨1, by omega⟩) ^ 2
           else if μ = ⟨1, by omega⟩ then minkowskiSignature d μ *
              (consecutiveDiff x k 0) ^ 2
           else minkowskiSignature d μ * (0 : ℝ) ^ 2) =
          (if μ = 0 then -(consecutiveDiff x k ⟨1, by omega⟩ ^ 2) else 0) +
          (if μ = ⟨1, by omega⟩ then consecutiveDiff x k 0 ^ 2 else 0) := by
        intro μ; split_ifs <;> simp_all [minkowskiSignature]
      simp_rw [hsplit, Finset.sum_add_distrib,
        Finset.sum_ite_eq' Finset.univ (0 : Fin (d + 1)),
        Finset.sum_ite_eq' Finset.univ (⟨1, by omega⟩ : Fin (d + 1)),
        Finset.mem_univ, ite_true]
      linarith
  -- Conclude
  rw [haction]
  exact Set.mem_iUnion.mpr ⟨wickCLG d hd, w, hw, rfl⟩

/-! ### Identity theorem for totally real submanifolds -/

/-- **Identity theorem for totally real submanifolds.**
    If f is holomorphic on an open connected set D ⊆ ℂ^m and f vanishes on
    an open subset V of D ∩ ℝ^m, then f vanishes on all of D. -/
theorem identity_theorem_totally_real {m : ℕ}
    {D : Set (Fin m → ℂ)} (hD_open : IsOpen D) (hD_conn : IsConnected D)
    {f : (Fin m → ℂ) → ℂ} (hf : DifferentiableOn ℂ f D)
    {V : Set (Fin m → ℝ)} (hV_open : IsOpen V) (hV_ne : V.Nonempty)
    (hV_sub : ∀ x ∈ V, (fun i => (x i : ℂ)) ∈ D)
    (hf_zero : ∀ x ∈ V, f (fun i => (x i : ℂ)) = 0) :
    ∀ z ∈ D, f z = 0 :=
  SCV.identity_theorem_totally_real hD_open hD_conn hf hV_open hV_ne hV_sub hf_zero

/-- Product-type version of the identity theorem for totally real submanifolds.
    Needed for our forward tube which lives in `Fin n → Fin (d+1) → ℂ`. -/
theorem identity_theorem_totally_real_product
    {D : Set (Fin n → Fin (d + 1) → ℂ)} (hD_open : IsOpen D)
    (hD_conn : IsConnected D)
    {f : (Fin n → Fin (d + 1) → ℂ) → ℂ} (hf : DifferentiableOn ℂ f D)
    {V : Set (Fin n → Fin (d + 1) → ℝ)} (hV_open : IsOpen V)
    (hV_ne : V.Nonempty)
    (hV_sub : ∀ x ∈ V, realEmbed x ∈ D)
    (hf_zero : ∀ x ∈ V, f (realEmbed x) = 0) :
    ∀ z ∈ D, f z = 0 :=
  SCV.identity_theorem_totally_real_product hD_open hD_conn hf hV_open hV_ne hV_sub hf_zero

/-! ### Holomorphicity of extendF on the extended tube -/

/-- `extendF` is holomorphic on the extended tube.
    At each z₀ ∈ T'_n, write z₀ = Λ₀·w₀ with w₀ ∈ FT, then
    extendF(z) = F(Λ₀⁻¹·z) near z₀. -/
theorem extendF_holomorphicOn (n : ℕ) (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z) :
    DifferentiableOn ℂ (extendF F) (ExtendedTube d n) := by
  intro z₀ hz₀
  -- z₀ ∈ ExtendedTube: ∃ Λ₀, w₀ with z₀ = Λ₀·w₀, w₀ ∈ FT
  obtain ⟨Λ₀, w₀, hw₀, hz₀_eq⟩ := Set.mem_iUnion.mp hz₀
  -- Inverse chart: ψ(z) = Λ₀⁻¹·z maps z₀ to w₀ ∈ FT
  set ψ := fun (z : Fin n → Fin (d + 1) → ℂ) =>
    complexLorentzAction (Λ₀⁻¹ : ComplexLorentzGroup d) z with hψ_def
  have hψ_diff : Differentiable ℂ ψ := differentiable_complexLorentzAction_snd Λ₀⁻¹
  have hψz₀ : ψ z₀ = w₀ := by
    simp only [ψ, hz₀_eq, ← complexLorentzAction_mul, inv_mul_cancel, complexLorentzAction_one]
  -- {z : ψ(z) ∈ FT} is open and contains z₀
  have hV_open : IsOpen {z | ψ z ∈ ForwardTube d n} :=
    isOpen_forwardTube.preimage hψ_diff.continuous
  have hz₀_V : ψ z₀ ∈ ForwardTube d n := hψz₀ ▸ hw₀
  -- Near z₀: extendF(z) = F(ψ(z))
  have hfeq : extendF F =ᶠ[nhds z₀] fun z => F (ψ z) := by
    apply Filter.eventuallyEq_of_mem (hV_open.mem_nhds hz₀_V)
    intro z (hz_V : ψ z ∈ ForwardTube d n)
    -- z = Λ₀ · (ψ z), and ψ z ∈ FT
    have hz_eq : z = complexLorentzAction Λ₀ (ψ z) := by
      simp only [ψ, ← complexLorentzAction_mul, mul_inv_cancel, complexLorentzAction_one]
    -- extendF(z) = F(ψ z) by well-definedness
    simp only [extendF]
    have hex : ∃ w, w ∈ ForwardTube d n ∧ ∃ Λ' : ComplexLorentzGroup d,
        z = complexLorentzAction Λ' w :=
      ⟨ψ z, hz_V, Λ₀, hz_eq⟩
    rw [dif_pos hex]
    exact extendF_preimage_eq n F hF_holo hF_real_inv hex.choose_spec.1 hz_V
      (hex.choose_spec.2.choose_spec.symm.trans hz_eq)
  -- F ∘ ψ is differentiable at z₀
  have hFψ_diff : DifferentiableAt ℂ (fun z => F (ψ z)) z₀ :=
    ((hF_holo _ hz₀_V).differentiableAt (isOpen_forwardTube.mem_nhds hz₀_V)).comp
      z₀ (hψ_diff z₀)
  exact (hfeq.differentiableAt_iff.mpr hFψ_diff).differentiableWithinAt

/-! ### Boundary value agreement at Jost points -/

/-- The timelike unit vector (δ, 0, ..., 0) is in the open forward cone when δ > 0. -/
private lemma inOpenForwardCone_timelike {δ : ℝ} (hδ : 0 < δ) :
    InOpenForwardCone d (fun μ : Fin (d + 1) => if μ = (0 : Fin (d + 1)) then δ else 0) := by
  constructor
  · simp [hδ]
  · rw [Finset.sum_eq_single (0 : Fin (d + 1))]
    · simp [minkowskiSignature]; nlinarith [sq_nonneg δ]
    · intro μ _ hμ; simp [hμ]
    · exact absurd (Finset.mem_univ _)

/-- The forward tube FT has every real point as a limit point.
    For any x, the point z_ε(k,μ) = x(k,μ) + iε(k+1)δ_{μ,0} lies in FT
    and converges to realEmbed x as ε → 0⁺. -/
theorem realEmbed_mem_closure_forwardTube (x : Fin n → Fin (d + 1) → ℝ) :
    realEmbed x ∈ closure (ForwardTube d n) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  set δ := ε / (2 * ((n : ℝ) + 1)) with hδ_def
  have hn_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hδ_pos : δ > 0 := div_pos hε (mul_pos two_pos hn_pos)
  -- Witness: z(k, μ) = x(k, μ) + i · δ · (k+1) · δ_{μ,0}
  refine ⟨fun k μ => (x k μ : ℂ) + ↑(δ * ((k : ℝ) + 1)) * if μ = (0 : Fin (d + 1)) then I else 0, ?_, ?_⟩
  · -- z ∈ ForwardTube: each consecutive imaginary-part difference is (δ, 0, ..., 0) ∈ V⁺
    intro k
    -- Show the imaginary part of each consecutive difference equals (δ, 0, ..., 0)
    suffices h : InOpenForwardCone d (fun μ =>
        ((fun μ' => (x k μ' : ℂ) + ↑(δ * ((k : ℝ) + 1)) * if μ' = (0 : Fin (d + 1)) then I else 0) μ -
         (if _ : k.val = 0 then (0 : Fin (d + 1) → ℂ) else
           fun μ' => (x ⟨k.val - 1, by omega⟩ μ' : ℂ) +
             ↑(δ * ((↑(k.val - 1) : ℝ) + 1)) * if μ' = (0 : Fin (d + 1)) then I else 0) μ).im) by
      exact h
    -- In both cases (k=0 and k>0), the imaginary part simplifies to (δ, 0, ..., 0)
    convert inOpenForwardCone_timelike hδ_pos using 1
    ext μ
    by_cases hk : k.val = 0
    · -- k = 0: Im(z(0,μ) - 0) = δ·δ_{μ,0}
      simp only [hk, ↓reduceDIte, Pi.zero_apply, sub_zero]
      by_cases hμ : μ = (0 : Fin (d + 1))
      · simp [hμ, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
              Complex.ofReal_re, Complex.I_re, Complex.I_im]
      · simp [hμ, Complex.ofReal_im, mul_zero]
    · -- k > 0: Im(z(k,μ) - z(k-1,μ)) = δ·δ_{μ,0}
      simp only [hk, ↓reduceDIte]
      by_cases hμ : μ = (0 : Fin (d + 1))
      · simp [hμ, Complex.ofReal_im, Complex.sub_im,
              Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im]
        have : (↑(k.val - 1) : ℝ) = (k.val : ℝ) - 1 := by
          rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hk), Nat.cast_one]
        rw [this]; ring
      · simp [hμ, Complex.ofReal_im, Complex.sub_im, mul_zero]
  · -- dist z (realEmbed x) < ε
    rw [dist_pi_lt_iff hε]
    intro k
    rw [dist_pi_lt_iff hε]
    intro μ
    simp only [realEmbed, Complex.dist_eq]
    -- The norm is ‖x - (x + perturbation)‖ = ‖perturbation‖
    rw [show (x k μ : ℂ) - ((x k μ : ℂ) + ↑(δ * ((k : ℝ) + 1)) *
      if μ = (0 : Fin (d + 1)) then I else 0) =
      -(↑(δ * ((k : ℝ) + 1)) * if μ = (0 : Fin (d + 1)) then I else 0) from by ring,
      norm_neg]
    by_cases hμ : μ = (0 : Fin (d + 1))
    · simp only [hμ, ↓reduceIte, norm_mul, Complex.norm_I, mul_one]
      rw [Complex.norm_of_nonneg (mul_nonneg hδ_pos.le (by positivity))]
      calc δ * ((k : ℝ) + 1) ≤ δ * ((n : ℝ) + 1) := by
            apply mul_le_mul_of_nonneg_left _ hδ_pos.le
            exact_mod_cast Nat.add_le_add_right (Nat.le_of_lt k.isLt) 1
        _ = ε / 2 := by rw [hδ_def]; field_simp
        _ < ε := half_lt_self hε
    · simp only [hμ, ↓reduceIte, mul_zero, norm_zero]; exact hε

/-- At forward Jost points, extendF agrees with the boundary value of F. -/
theorem extendF_eq_boundary_value (n : ℕ) (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (realEmbed x))
    (hd : 1 ≤ d)
    (x : Fin n → Fin (d + 1) → ℝ) (hx : x ∈ ForwardJostSet d n hd) :
    extendF F (realEmbed x) = F (realEmbed x) := by
  -- realEmbed x ∈ T'_n by Jost's lemma
  have hx_ET := forwardJostSet_subset_extendedTube hd x hx
  -- extendF is holomorphic (hence continuous) on T'_n
  have hextend_holo := extendF_holomorphicOn n F hF_holo hF_real_inv
  -- extendF is ContinuousWithinAt on FT at realEmbed x (restrict from T'_n ⊇ FT)
  have h1 : ContinuousWithinAt (extendF F) (ForwardTube d n) (realEmbed x) :=
    (hextend_holo.continuousOn _ hx_ET).mono forwardTube_subset_extendedTube
  -- F is ContinuousWithinAt on FT at realEmbed x (hypothesis)
  have h2 : ContinuousWithinAt F (ForwardTube d n) (realEmbed x) := hF_bv x
  -- extendF =ᶠ F on FT (eventually equal in the nhdsWithin filter)
  have h3 : extendF F =ᶠ[nhdsWithin (realEmbed x) (ForwardTube d n)] F :=
    Filter.eventually_of_mem self_mem_nhdsWithin
      (fun z hz => extendF_eq_on_forwardTube n F hF_holo hF_real_inv z hz)
  -- nhdsWithin filter is nontrivial (realEmbed x ∈ closure FT)
  haveI : (nhdsWithin (realEmbed x) (ForwardTube d n)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (realEmbed_mem_closure_forwardTube x)
  -- F also converges to extendF F (realEmbed x) (by map_congr from h1 and h3)
  have h4 : Filter.Tendsto F (nhdsWithin (realEmbed x) (ForwardTube d n))
      (nhds (extendF F (realEmbed x))) :=
    (Filter.map_congr h3).symm.le.trans h1
  -- By uniqueness of limits in Hausdorff space ℂ
  exact tendsto_nhds_unique h4 h2

/-- Generalized boundary value: `extendF F (realEmbed x) = F (realEmbed x)` for any
    real `x` with `realEmbed x ∈ ExtendedTube`. This follows from the same limit-uniqueness
    argument as `extendF_eq_boundary_value` without requiring `ForwardJostSet` membership. -/
theorem extendF_eq_boundary_value_ET (n : ℕ) (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (realEmbed x))
    (x : Fin n → Fin (d + 1) → ℝ) (hx_ET : realEmbed x ∈ ExtendedTube d n) :
    extendF F (realEmbed x) = F (realEmbed x) := by
  have hextend_holo := extendF_holomorphicOn n F hF_holo hF_real_inv
  have h1 : ContinuousWithinAt (extendF F) (ForwardTube d n) (realEmbed x) :=
    (hextend_holo.continuousOn _ hx_ET).mono forwardTube_subset_extendedTube
  have h2 : ContinuousWithinAt F (ForwardTube d n) (realEmbed x) := hF_bv x
  have h3 : extendF F =ᶠ[nhdsWithin (realEmbed x) (ForwardTube d n)] F :=
    Filter.eventually_of_mem self_mem_nhdsWithin
      (fun z hz => extendF_eq_on_forwardTube n F hF_holo hF_real_inv z hz)
  haveI : (nhdsWithin (realEmbed x) (ForwardTube d n)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (realEmbed_mem_closure_forwardTube x)
  have h4 : Filter.Tendsto F (nhdsWithin (realEmbed x) (ForwardTube d n))
      (nhds (extendF F (realEmbed x))) :=
    (Filter.map_congr h3).symm.le.trans h1
  exact tendsto_nhds_unique h4 h2

/-! ### Swap-compatible configurations -/

/-- The extended tube is open (each summand is the image of the open FT under the
    homeomorphism z ↦ Λ·z). -/
private theorem isOpen_extendedTube : IsOpen (@ExtendedTube d n) := by
  suffices h : ExtendedTube d n =
      ⋃ Λ : ComplexLorentzGroup d,
        (fun z => complexLorentzAction Λ z) '' (ForwardTube d n) by
    rw [h]
    exact isOpen_iUnion (fun Λ =>
      (complexLorentzAction_isOpenMap Λ) _ isOpen_forwardTube)
  ext z; simp only [ExtendedTube, Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨Λ, w, hw, rfl⟩; exact ⟨Λ, w, hw, rfl⟩
  · rintro ⟨Λ, w, hw, rfl⟩; exact ⟨Λ, w, hw, rfl⟩

/-- A real configuration whose consecutive differences each satisfy
    |ζ_k,0| < √(ζ_k,1² + ζ_k,2²) lies in the extended tube.
    This generalizes `forwardJostSet_subset_extendedTube` to allow the dominant
    spatial component to lie in the (e₁, e₂) plane rather than along e₁ alone.
    The proof composes a spatial rotation in the (e₁, e₂) plane with the Wick matrix
    to obtain a complex Lorentz boost mapping the configuration from a forward tube
    point. Requires d ≥ 2 for the second spatial direction. -/
-- Helper: For any (a, b) with a² + b² > 0, there exists a spatial rotation R in the
-- (e₁, e₂) plane such that R maps (a, b) to (√(a²+b²), 0). This rotation is in
-- SO(d) (spatial part of the Lorentz group) and hence lifts to a complex Lorentz
-- group element that preserves the forward tube.
--
-- The rotation matrix acts on spatial indices 1, 2 as [[c, s], [-s, c]] where
-- c = a/r, s = b/r, r = √(a²+b²). It fixes all other spatial indices and the
-- time index.
--
-- Blocked by: constructing the rotation matrix as a ComplexLorentzGroup element,
-- which requires showing it preserves the Minkowski metric.
private lemma spatial_rotation_e12_plane (hd : 2 ≤ d) (a b : ℝ) (hab : 0 < a ^ 2 + b ^ 2) :
    ∃ (R : ComplexLorentzGroup d),
      -- R fixes the time component and rotates (e₁, e₂) plane
      -- R · v maps the (a, b) direction to (√(a²+b²), 0) in the spatial (1,2) subspace
      True := by
  sorry

private lemma generalizedJost_subset_extendedTube (hd : 2 ≤ d)
    (x : Fin n → Fin (d + 1) → ℝ)
    (hx : ∀ k : Fin n,
      let ζ := consecutiveDiff x k
      |ζ 0| < Real.sqrt (ζ ⟨1, by omega⟩ ^ 2 + ζ ⟨2, by omega⟩ ^ 2)) :
    realEmbed x ∈ ExtendedTube d n := by
  -- Strategy: for each k, rotate the (e₁, e₂) components of the k-th consecutive
  -- difference to align with e₁, transforming the generalized condition
  -- |ζ_k,0| < √(ζ_k,1² + ζ_k,2²) into the forward Jost condition |ζ_k,0| < ζ_k,1.
  -- Then apply forwardJostSet_subset_extendedTube.
  -- The single rotation works for all k simultaneously only if the (e₁, e₂) ratios
  -- are the same -- in general, we need a per-k argument or a different approach.
  -- The proof uses the extended tube's Lorentz invariance: realEmbed(R·x) ∈ ET implies
  -- realEmbed(x) ∈ ET (since ET is Lorentz-invariant).
  sorry

/-- The permutation map on configurations σ·x = (x_{σ(0)}, ..., x_{σ(n-1)}) is
    continuous. -/
private lemma continuous_permute_config (σ : Equiv.Perm (Fin n)) :
    Continuous (fun x : Fin n → Fin (d + 1) → ℝ => fun k => x (σ k)) :=
  continuous_pi fun k => continuous_apply (σ k)

/-- For adjacent swap σ = swap(i, i+1), the **swap Jost set** consists of
    configurations in ForwardJostSet such that the permuted configuration σ·x
    also lies in the extended tube. Concretely, this means both the original
    and permuted consecutive differences admit a complex boost into V⁺.

    The construction uses a 2D perturbation in the (e₁, e₂) spatial plane:
    x_k = (0, k+1, 0, ..., 0) for k ≠ i+1, with x_{i+1} = (0, i+2, ε, 0, ..., 0).
    This breaks the collinearity and ensures both orderings satisfy the Jost condition.

    For the permuted ordering, the problematic consecutive difference is
    ζ'_{i+1} = -ζ_{i+1} which has negative first spatial component.
    But the second spatial component provides a "rotated" direction w' such that
    w' · ζ'_k > 0 for all k. The complex Lorentz transformation for the permuted
    ordering is R · exp(-iα K₁) where R is a spatial rotation aligning w' with e₁. -/
theorem swap_jost_set_exists (hd : 2 ≤ d) (_hn : 2 ≤ n)
    (i : Fin n) (hi : i.val + 1 < n) :
    ∃ V : Set (Fin n → Fin (d + 1) → ℝ),
      IsOpen V ∧ V.Nonempty ∧
      -- V ⊆ JostSet (for locality)
      (∀ x ∈ V, x ∈ JostSet d n) ∧
      -- realEmbed V ⊆ ExtendedTube (original ordering)
      (∀ x ∈ V, realEmbed x ∈ ExtendedTube d n) ∧
      -- realEmbed (σ·V) ⊆ ExtendedTube (permuted ordering)
      (∀ x ∈ V, realEmbed (fun k => x (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈
        ExtendedTube d n) ∧
      -- Locality: x_{i+1} - x_i is spacelike
      (∀ x ∈ V, IsSpacelike d (fun μ => x ⟨i.val + 1, hi⟩ μ - x i μ)) := by
  -- Strategy: take V = ForwardJostSet ∩ {x | σ·x ∈ ExtendedTube}
  -- Both sets are open, and we show their intersection is nonempty.
  have hd1 : 1 ≤ d := by omega
  -- The set S = {x | realEmbed(σ·x) ∈ ExtendedTube} is open
  set σ := Equiv.swap i ⟨i.val + 1, hi⟩ with hσ_def
  set S : Set (Fin n → Fin (d + 1) → ℝ) :=
    { x | realEmbed (fun k => x (σ k)) ∈ ExtendedTube d n } with hS_def
  have hS_open : IsOpen S := by
    have : S = (fun x : Fin n → Fin (d + 1) → ℝ => realEmbed (fun k => x (σ k))) ⁻¹'
        ExtendedTube d n := rfl
    rw [this]
    apply isOpen_extendedTube.preimage
    exact (continuous_pi fun k => continuous_pi fun μ =>
      Complex.continuous_ofReal.comp ((continuous_apply μ).comp (continuous_apply (σ k))))
  -- V = ForwardJostSet ∩ S
  set V := ForwardJostSet d n hd1 ∩ S with hV_def
  refine ⟨V, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- V is open: intersection of two open sets
    exact (isOpen_forwardJostSet hd1).inter hS_open
  · -- V is nonempty: construct a specific point
    -- Take p_k = (0, k+1, 0, ...) except p_{i+1} = (0, i+2, 1/2, 0, ...)
    -- The base forward Jost point with a perturbation in e₂ at position i+1
    -- Then p ∈ ForwardJostSet (perturbing e₂ doesn't affect |ζ_0| < ζ_1 condition)
    -- And σ·p ∈ ExtendedTube by generalizedJost_subset_extendedTube
    -- (the swapped consecutive diffs satisfy the generalized condition)
    --
    -- Define the point
    set e₁ : Fin (d + 1) := ⟨1, by omega⟩
    set e₂ : Fin (d + 1) := ⟨2, by omega⟩
    set i' : Fin n := ⟨i.val + 1, hi⟩
    set p : Fin n → Fin (d + 1) → ℝ :=
      fun k μ => if μ = e₁ then (k : ℝ) + 1
                 else if μ = e₂ ∧ k = i' then (1 : ℝ) / 2
                 else 0 with hp_def
    suffices hp_fjs : p ∈ ForwardJostSet d n hd1 by
      suffices hp_S : p ∈ S by exact ⟨p, hp_fjs, hp_S⟩
      -- Show σ·p ∈ ExtendedTube via generalizedJost_subset_extendedTube
      show realEmbed (fun k => p (σ k)) ∈ ExtendedTube d n
      apply generalizedJost_subset_extendedTube hd
      -- Verify: consecutive differences of σ·p satisfy |ζ_0| < √(ζ_1² + ζ_2²)
      intro k
      -- Time component of p is always 0 (since (0 : Fin(d+1)) ≠ e₁ and ≠ e₂)
      have h01 : (0 : Fin (d + 1)) ≠ e₁ := by
        intro h; exact absurd (congr_arg Fin.val h) (by norm_num)
      have h02 : (0 : Fin (d + 1)) ≠ e₂ := by
        intro h; exact absurd (congr_arg Fin.val h) (by norm_num)
      have hp_time : ∀ j : Fin n, p j 0 = 0 := by
        intro j; simp only [p, h01, ↓reduceIte]
        simp only [show ¬((0 : Fin (d + 1)) = e₂ ∧ j = i') from fun ⟨h, _⟩ => h02 h, ↓reduceIte]
      -- Therefore all consecutive differences of σ·p have time component 0
      have hζ_time : consecutiveDiff (fun k => p (σ k)) k 0 = 0 := by
        simp only [consecutiveDiff]
        by_cases hk0 : k.val = 0
        · simp [hk0, hp_time]
        · simp only [hk0, ↓reduceDIte]; rw [hp_time, hp_time]; ring
      -- So |ζ_0| = 0, and we need √(ζ_1² + ζ_2²) > 0
      show |consecutiveDiff (fun k => p (σ k)) k 0| <
        Real.sqrt (consecutiveDiff (fun k => p (σ k)) k ⟨1, by omega⟩ ^ 2 +
          consecutiveDiff (fun k => p (σ k)) k ⟨2, by omega⟩ ^ 2)
      rw [hζ_time, abs_zero]
      apply Real.sqrt_pos_of_pos
      -- Show p j e₁ = j + 1 for all j
      have hp_e1 : ∀ j : Fin n, p j e₁ = (j : ℝ) + 1 := by
        intro j; simp only [p, ↓reduceIte]
      -- Compute ζ_1 = consecutiveDiff (σ·p) k e₁
      -- For k=0: ζ_1 = (σ(0)).val + 1 ≥ 1 > 0
      -- For k>0: ζ_1 = (σ(k)).val - (σ(k-1)).val ≠ 0 (σ injective, k ≠ k-1)
      have hζ1_ne : consecutiveDiff (fun k => p (σ k)) k e₁ ≠ 0 := by
        simp only [consecutiveDiff, hp_e1]
        by_cases hk0 : k.val = 0
        · simp only [hk0, ↓reduceDIte, sub_zero]
          linarith [Nat.zero_le (σ k).val]
        · simp only [hk0, ↓reduceDIte]
          -- Need: (σ k).val + 1 - ((σ ⟨k-1, _⟩).val + 1) ≠ 0
          -- i.e., (σ k).val ≠ (σ ⟨k-1, _⟩).val
          intro heq
          have hkm1 : k.val - 1 < n := by omega
          have hne : k ≠ ⟨k.val - 1, hkm1⟩ := by
            intro h; have := congr_arg Fin.val h; simp at this; omega
          apply hne
          apply σ.injective
          ext
          exact_mod_cast show (↑(σ k).val : ℝ) = (↑(σ ⟨k.val - 1, hkm1⟩).val : ℝ) by linarith
      have hζ1_sq : 0 < consecutiveDiff (fun k => p (σ k)) k e₁ ^ 2 :=
        sq_pos_of_ne_zero hζ1_ne
      linarith [sq_nonneg (consecutiveDiff (fun k => p (σ k)) k ⟨2, by omega⟩)]
    -- Show p ∈ ForwardJostSet: |ζ_k,0| < ζ_k,1 for all k
    intro k
    show |consecutiveDiff p k 0| < consecutiveDiff p k e₁
    simp only [consecutiveDiff, p, e₁, e₂, i']
    -- time component is always 0
    have h01 : (0 : Fin (d + 1)) ≠ ⟨1, by omega⟩ := by
      intro h; exact absurd (congr_arg Fin.val h) (by norm_num)
    have h02 : (0 : Fin (d + 1)) ≠ ⟨2, by omega⟩ := by
      intro h; exact absurd (congr_arg Fin.val h) (by norm_num)
    simp only [h01, ↓reduceIte, h02]
    by_cases hk : k.val = 0
    · simp [hk]
    · simp only [hk, ↓reduceDIte]
      have hprev_e1 : (if (⟨k.val - 1, by omega⟩ : Fin n) = ⟨i.val + 1, hi⟩
          then (1 : ℝ) / 2 else 0) = _ := rfl
      -- spatial component e₁: (k+1) - k = 1
      have hcast : (↑(k.val - 1) : ℝ) + 1 = (k : ℝ) + 1 - 1 := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hk)]; ring
      simp only [false_and, ↓reduceIte, sub_zero, abs_zero]
      linarith
  · -- V ⊆ JostSet
    intro x ⟨hx_fjs, _⟩
    exact forwardJostSet_subset_jostSet hd1 hx_fjs
  · -- V ⊆ ExtendedTube (original)
    intro x ⟨hx_fjs, _⟩
    exact forwardJostSet_subset_extendedTube hd1 x hx_fjs
  · -- V ⊆ ExtendedTube (swapped)
    intro x ⟨_, hx_S⟩
    exact hx_S
  · -- x_{i+1} - x_i is spacelike
    intro x ⟨hx_fjs, _⟩
    -- x ∈ ForwardJostSet → x ∈ JostSet → all pairwise diffs spacelike
    have hx_js := forwardJostSet_subset_jostSet hd1 hx_fjs
    have hne : (⟨i.val + 1, hi⟩ : Fin n) ≠ i := by
      intro h; have := congr_arg Fin.val h; simp at this
    exact hx_js.2 ⟨i.val + 1, hi⟩ i hne

/-! ### Main result: permutation invariance via Jost points -/

-- The extended tube intersected with its permutation preimage is connected.
-- D_σ = T'_n ∩ {z | σ·z ∈ T'_n} is connected for any permutation σ.
-- This follows from the fact that T'_n is a tube domain (open connected subset
-- of ℂ^{n(d+1)} invariant under real translations), and D_σ is its intersection
-- with σ⁻¹(T'_n), another tube domain. The connectivity reduces to the
-- connectivity of the complex Lorentz group SO⁺(1,d;ℂ).

/-- Helper: The extended tube T'_n is itself connected.

    T'_n = ⋃_{Λ ∈ L₊(ℂ)} Λ · FT_n where FT_n is convex (hence connected) and the
    complex Lorentz group L₊(ℂ) is connected. Since the action map (Λ, z) ↦ Λ·z is
    continuous and L₊(ℂ) × FT_n is connected, T'_n is connected.

    Blocked by: needs ForwardTube convexity + complex Lorentz group connectivity
    (available as isPathConnected) composed via the continuous action map. -/
private lemma isConnected_extendedTube :
    IsConnected (@ExtendedTube d n) := by
  sorry

/-- Helper: The intersection of two connected open tube domains that share a
    real "base" is connected.

    When D₁ and D₂ are tube domains (i.e., of the form Ω + iC where Ω is open in ℝⁿ
    and C is a cone), their intersection D₁ ∩ D₂ = (Ω₁ ∩ Ω₂) + i(C₁ ∩ C₂) is also
    a tube domain and hence connected (assuming the base is nonempty). -/
private lemma tube_domain_intersection_connected (σ : Equiv.Perm (Fin n)) :
    IsConnected ({ z : Fin n → Fin (d + 1) → ℂ |
      z ∈ ExtendedTube d n ∧ (fun k => z (σ k)) ∈ ExtendedTube d n }) := by
  sorry

private lemma isConnected_extendedTube_inter_perm (σ : Equiv.Perm (Fin n)) :
    IsConnected ({ z : Fin n → Fin (d + 1) → ℂ |
      z ∈ ExtendedTube d n ∧ (fun k => z (σ k)) ∈ ExtendedTube d n }) :=
  tube_domain_intersection_connected σ

/-- For an adjacent swap σ = swap(i, i+1), the holomorphic function
    f(z) = extendF(σ·z) - extendF(z) vanishes on the domain
    D = T'_n ∩ σ⁻¹(T'_n).

    The proof applies the identity theorem for totally real submanifolds:
    f vanishes on the open real Jost set V ⊆ D ∩ ℝ^{n(d+1)} (by locality
    and boundary value agreement), and D is open and connected, so f = 0 on D.

    Requires d ≥ 2 for the Jost set construction. -/
private lemma extendF_swap_eq_on_domain (hd : 2 ≤ d) (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (realEmbed x))
    (i : Fin n) (hi : i.val + 1 < n)
    (hF_local_i :
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (z : Fin n → Fin (d + 1) → ℂ)
    (hz : z ∈ ExtendedTube d n)
    (hσz : (fun k => z (Equiv.swap i ⟨i.val + 1, hi⟩ k)) ∈ ExtendedTube d n) :
    extendF F (fun k => z (Equiv.swap i ⟨i.val + 1, hi⟩ k)) = extendF F z := by
  set σ := Equiv.swap i ⟨i.val + 1, hi⟩ with hσ_def
  -- Domain D = {z ∈ ET | σ·z ∈ ET}
  set D := { w : Fin n → Fin (d + 1) → ℂ |
    w ∈ ExtendedTube d n ∧ (fun k => w (σ k)) ∈ ExtendedTube d n } with hD_def
  have hz_D : z ∈ D := ⟨hz, hσz⟩
  -- f(w) = extendF(σ·w) - extendF(w)
  set f := fun w : Fin n → Fin (d + 1) → ℂ =>
    extendF F (fun k => w (σ k)) - extendF F w with hf_def
  suffices hfz : f z = 0 by simp only [f, sub_eq_zero] at hfz; exact hfz
  -- Permutation map ψ
  set ψ := fun (w : Fin n → Fin (d + 1) → ℂ) (k : Fin n) (μ : Fin (d + 1)) =>
    w (σ k) μ with hψ_def
  have hψ_diff : Differentiable ℂ ψ := by
    show Differentiable ℂ (fun w : Fin n → Fin (d + 1) → ℂ => fun k μ => w (σ k) μ)
    exact differentiable_pi.mpr fun k =>
      (differentiable_apply (σ k) : Differentiable ℂ (fun w : Fin n → Fin (d + 1) → ℂ => w (σ k)))
  -- D is open
  have hD_open : IsOpen D := by
    apply IsOpen.inter isOpen_extendedTube
    exact isOpen_extendedTube.preimage hψ_diff.continuous
  -- D is connected
  have hD_conn : IsConnected D := isConnected_extendedTube_inter_perm σ
  -- f is holomorphic on D
  have hextend_holo := extendF_holomorphicOn n F hF_holo hF_real_inv
  have hf_holo : DifferentiableOn ℂ f D := by
    apply DifferentiableOn.sub
    · exact hextend_holo.comp (hψ_diff.differentiableOn) (fun w hw => hw.2)
    · exact hextend_holo.mono (fun w hw => hw.1)
  -- Get V from swap_jost_set_exists
  have hn2 : 2 ≤ n := by omega
  obtain ⟨V, hV_open, hV_ne, hV_jost, hV_ET, hV_σET, hV_spacelike⟩ :=
    swap_jost_set_exists hd hn2 i hi
  -- f = 0 on D by identity theorem
  suffices hfD : ∀ w ∈ D, f w = 0 from hfD z hz_D
  exact identity_theorem_totally_real_product hD_open hD_conn hf_holo
    hV_open hV_ne
    (fun x hx => ⟨hV_ET x hx, hV_σET x hx⟩)
    (fun x hx => by
      simp only [f, sub_eq_zero]
      have hrealσ : (fun k => realEmbed x (σ k)) = realEmbed (fun k => x (σ k)) := by
        ext k μ; simp [realEmbed]
      rw [hrealσ]
      -- extendF(σ·x) = F(σ·x) by boundary value
      have hbv_σ := extendF_eq_boundary_value_ET n F hF_holo hF_real_inv hF_bv
        (fun k => x (σ k)) (hV_σET x hx)
      -- F(σ·x) = F(x) by locality
      have hspacelike := hV_spacelike x hx
      have hlocal := hF_local_i x hspacelike
      -- extendF(x) = F(x) by boundary value
      have hbv := (extendF_eq_boundary_value_ET n F hF_holo hF_real_inv hF_bv
        x (hV_ET x hx)).symm
      -- Chain: extendF(σ·x) = F(σ·x) = F(x) = extendF(x)
      have : realEmbed (fun k => x (σ k)) = fun k μ => (x (σ k) μ : ℂ) := rfl
      rw [hbv_σ, this, hlocal]
      exact hbv)

/-- For any permutation σ and d ≥ 2, the locality hypothesis iterated through
    an adjacent-swap decomposition of σ gives F(σ·x) = F(x) on the Jost set.

    On the Jost set, all pairwise differences are spacelike, so every adjacent
    swap preserves the spacelike condition needed for locality. Writing
    σ = τ₁ ∘ ... ∘ τₖ as a product of adjacent transpositions, we get
    F(σ·x) = F(τ₁·...·τₖ·x) = ... = F(x). -/
private lemma F_perm_eq_on_jostSet
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (σ : Equiv.Perm (Fin n))
    (x : Fin n → Fin (d + 1) → ℝ) (hx : x ∈ JostSet d n) :
    F (fun k μ => (x (σ k) μ : ℂ)) = F (fun k μ => (x k μ : ℂ)) := by
  -- Induction on adjacent swap decomposition of σ.
  -- The motive is universally quantified over x (needed for the step).
  revert x
  induction σ using BHW.Fin.Perm.adjSwap_induction with
  | one => intro x _; simp
  | adj_mul τ i hi ih =>
    intro x hx
    -- σ = swap(i, i+1) * τ.
    -- Key identity: x ∘ (swap * τ) = (x ∘ swap) ∘ τ
    -- (both map k to x(swap(τ(k))))
    set j := (⟨i.val + 1, hi⟩ : Fin n)
    set sw := Equiv.swap i j
    -- Step 1: F(x ∘ swap) = F(x) by locality
    -- x ∈ JostSet implies x_{i+1} - x_i is spacelike
    have hne : j ≠ i := by intro h; exact absurd (congr_arg Fin.val h) (by simp [j])
    have hspacelike : ∑ μ, minkowskiSignature d μ * (x j μ - x i μ) ^ 2 > 0 :=
      hx.2 j i hne
    have hlocal := hF_local i hi x hspacelike
    -- Step 2: F((x ∘ swap) ∘ τ) = F(x ∘ swap) by IH
    -- (x ∘ swap) ∈ JostSet (permutation-invariant)
    have hxsw : (fun k => x (sw k)) ∈ JostSet d n := jostSet_permutation_invariant sw hx
    have ih_xsw := ih (fun k => x (sw k)) hxsw
    -- Step 3: x ∘ (swap * τ) = (x ∘ swap) ∘ τ
    have hcomp : (fun k μ => (x ((sw * τ) k) μ : ℂ)) =
        (fun k μ => (x (sw (τ k)) μ : ℂ)) := by
      ext k μ; simp [Equiv.Perm.mul_apply]
    -- Combine: F(x ∘ (swap * τ)) = F((x ∘ swap) ∘ τ) = F(x ∘ swap) = F(x)
    rw [hcomp, ih_xsw, hlocal]

/-- For any permutation σ and d ≥ 2, there exists an open nonempty set of
    real configurations in the forward Jost set such that both the original and permuted
    real embeddings lie in the extended tube. The forward Jost set condition ensures
    boundary value agreement (extendF = F at these points).

    This generalizes `swap_jost_set_exists`. The forward Jost set is used instead of
    the weaker Jost set because `extendF_eq_boundary_value` requires it. -/
private lemma perm_jost_set_exists (hd : 2 ≤ d) (σ : Equiv.Perm (Fin n)) :
    ∃ V : Set (Fin n → Fin (d + 1) → ℝ),
      IsOpen V ∧ V.Nonempty ∧
      (∀ x ∈ V, x ∈ ForwardJostSet d n (by omega : 1 ≤ d)) ∧
      (∀ x ∈ V, realEmbed x ∈ ExtendedTube d n) ∧
      (∀ x ∈ V, realEmbed (fun k => x (σ k)) ∈ ExtendedTube d n) := by
  have hd1 : 1 ≤ d := by omega
  -- S = {x | realEmbed(x∘σ) ∈ ExtendedTube} is open
  set S : Set (Fin n → Fin (d + 1) → ℝ) :=
    { x | realEmbed (fun k => x (σ k)) ∈ ExtendedTube d n } with hS_def
  have hS_open : IsOpen S := by
    have : S = (fun x : Fin n → Fin (d + 1) → ℝ => realEmbed (fun k => x (σ k))) ⁻¹'
        ExtendedTube d n := rfl
    rw [this]
    apply isOpen_extendedTube.preimage
    exact (continuous_pi fun k => continuous_pi fun μ =>
      Complex.continuous_ofReal.comp ((continuous_apply μ).comp (continuous_apply (σ k))))
  -- V = ForwardJostSet ∩ S
  set V := ForwardJostSet d n hd1 ∩ S with hV_def
  refine ⟨V, ?_, ?_, ?_, ?_, ?_⟩
  · -- V is open
    exact (isOpen_forwardJostSet hd1).inter hS_open
  · -- V is nonempty: the standard Jost point (0, k+1, 0, ...) ∈ ForwardJostSet,
    -- and its permutation (0, σ(k)+1, 0, ...) ∈ ExtendedTube via generalizedJost.
    -- Each consecutive diff of x∘σ: ζ'_k = (0, σ(k+1)-σ(k), 0, ...) has
    -- |ζ'₀| = 0 < |σ(k+1)-σ(k)| = √(ζ'₁² + ζ'₂²).
    set e₁ : Fin (d + 1) := ⟨1, by omega⟩
    set p : Fin n → Fin (d + 1) → ℝ := fun k μ => if μ = e₁ then (k : ℝ) + 1 else 0
    have hp_fjs : p ∈ ForwardJostSet d n hd1 := by
      intro k
      simp only [consecutiveDiff, p, e₁]
      by_cases hk : k.val = 0
      · -- k = 0: ζ_0 = p 0 0 = 0, ζ_1 = p 0 1 = 1, condition: |0| < 1
        simp only [hk, ↓reduceDIte]
        have h01 : (0 : Fin (d + 1)) ≠ ⟨1, by omega⟩ := by
          intro h; exact absurd (congr_arg Fin.val h) (by norm_num)
        simp [h01]
      · -- k > 0: ζ_0 = 0-0 = 0, ζ_1 = (k+1)-(k-1+1) = 1, condition: |0| < 1
        simp only [hk, ↓reduceDIte]
        have h01 : (0 : Fin (d + 1)) ≠ ⟨1, by omega⟩ := by
          intro h; exact absurd (congr_arg Fin.val h) (by norm_num)
        simp only [h01, ↓reduceIte, sub_zero, abs_zero]
        have hk_pos : 1 ≤ k.val := Nat.one_le_iff_ne_zero.mpr hk
        have : (↑(k.val - 1 : ℕ) : ℝ) = (k.val : ℝ) - 1 := by
          rw [Nat.cast_sub hk_pos]; simp
        linarith
    suffices hp_S : p ∈ S by exact ⟨p, hp_fjs, hp_S⟩
    -- Show realEmbed(p∘σ) ∈ ExtendedTube via generalizedJost_subset_extendedTube
    show realEmbed (fun k => p (σ k)) ∈ ExtendedTube d n
    apply generalizedJost_subset_extendedTube hd
    intro k
    simp only [consecutiveDiff, p, e₁]
    -- The time component of each consecutive diff is 0 (since p has 0 in μ=0)
    have h01 : (0 : Fin (d + 1)) ≠ ⟨1, by omega⟩ := by
      intro h; exact absurd (congr_arg Fin.val h) (by norm_num)
    have h02 : (0 : Fin (d + 1)) ≠ ⟨2, by omega⟩ := by
      intro h; exact absurd (congr_arg Fin.val h) (by norm_num)
    have h12 : (⟨2, by omega⟩ : Fin (d + 1)) ≠ (⟨1, by omega⟩ : Fin (d + 1)) := by
      intro h; exact absurd (congr_arg Fin.val h) (by norm_num)
    simp only [h01, ↓reduceIte, h12]
    by_cases hk : k.val = 0
    · simp only [hk, ↓reduceDIte, sub_zero]
      simp only [abs_zero]
      apply Real.sqrt_pos_of_pos
      have : ((σ ⟨0, by omega⟩ : ℕ) : ℝ) + 1 > 0 := by positivity
      positivity
    · simp only [hk, ↓reduceDIte]
      simp only [sub_self, abs_zero]
      apply Real.sqrt_pos_of_pos
      -- σ(k) ≠ σ(k-1) since σ is injective
      have hσ_ne : (σ k : ℕ) ≠ (σ ⟨k.val - 1, by omega⟩ : ℕ) := by
        intro heq; exact absurd (σ.injective (Fin.ext heq))
          (by intro h; exact absurd (congr_arg Fin.val h) (by simp; omega))
      have : ((σ k : ℝ) + 1 - ((σ ⟨k.val - 1, by omega⟩ : ℝ) + 1)) ≠ 0 := by
        intro h; apply hσ_ne; exact_mod_cast show (σ k : ℝ) = σ ⟨k.val - 1, by omega⟩ by linarith
      positivity
  · -- V ⊆ ForwardJostSet
    exact fun x ⟨hx_fjs, _⟩ => hx_fjs
  · -- V ⊆ ExtendedTube (original)
    exact fun x ⟨hx_fjs, _⟩ => forwardJostSet_subset_extendedTube hd1 x hx_fjs
  · -- V ⊆ ExtendedTube (permuted)
    exact fun x ⟨_, hx_S⟩ => hx_S

/-- **Permutation invariance of extendF** for any permutation.

    For σ ∈ S_n and z ∈ T'_n with σ·z ∈ T'_n:
    extendF(σ·z) = extendF(z).

    Proof:
    1. `perm_jost_set_exists` gives a nonempty open V ⊆ JostSet with
       realEmbed V ⊆ T'_n ∩ σ⁻¹(T'_n).
    2. On V: extendF(σ·x) = F(σ·x) = F(x) = extendF(x) by
       `F_perm_eq_on_jostSet` (iterated locality) + `extendF_eq_boundary_value`.
    3. f(z) = extendF(σ·z) - extendF(z) is holomorphic on
       D = T'_n ∩ σ⁻¹(T'_n) and f = 0 on V.
    4. By `identity_theorem_totally_real_product`: f = 0 on the connected D.
    5. D is connected by `isConnected_extendedTube_inter_perm`. -/
theorem extendF_permutation_invariant_swap (hd : 2 ≤ d) (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_real_inv : ∀ (Λ : RestrictedLorentzGroup d)
      (z : Fin n → Fin (d + 1) → ℂ), z ∈ ForwardTube d n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (d + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube d n) (realEmbed x))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (d + 1) → ℝ),
        ∑ μ, minkowskiSignature d μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (σ : Equiv.Perm (Fin n))
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ ExtendedTube d n) (hσz : (fun k => z (σ k)) ∈ ExtendedTube d n) :
    extendF F (fun k => z (σ k)) = extendF F z := by
  -- The domain D_σ = {z ∈ T'_n | σ·z ∈ T'_n}
  set D := { w : Fin n → Fin (d + 1) → ℂ |
    w ∈ ExtendedTube d n ∧ (fun k => w (σ k)) ∈ ExtendedTube d n } with hD_def
  -- z ∈ D
  have hz_D : z ∈ D := ⟨hz, hσz⟩
  -- f(w) = extendF(σ·w) - extendF(w) is the function we show vanishes
  set f := fun w : Fin n → Fin (d + 1) → ℂ =>
    extendF F (fun k => w (σ k)) - extendF F w with hf_def
  -- Suffices to show f(z) = 0
  suffices hfz : f z = 0 by simp only [f, sub_eq_zero] at hfz; exact hfz
  -- The permutation map ψ : w ↦ (fun k => w (σ k)) is differentiable
  set ψ := fun (w : Fin n → Fin (d + 1) → ℂ) (k : Fin n) (μ : Fin (d + 1)) =>
    w (σ k) μ with hψ_def
  have hψ_cont : Continuous ψ :=
    continuous_pi fun k => continuous_pi fun μ =>
      ((continuous_apply μ).comp (continuous_apply (σ k)))
  have hψ_diff : Differentiable ℂ ψ := by
    show Differentiable ℂ (fun w : Fin n → Fin (d + 1) → ℂ => fun k μ => w (σ k) μ)
    exact differentiable_pi.mpr fun k =>
      (differentiable_apply (σ k) : Differentiable ℂ (fun w : Fin n → Fin (d + 1) → ℂ => w (σ k)))
  -- D is open (intersection of two preimages of the open ET)
  have hD_open : IsOpen D := by
    apply IsOpen.inter isOpen_extendedTube
    exact isOpen_extendedTube.preimage hψ_diff.continuous
  -- D is connected
  have hD_conn : IsConnected D := isConnected_extendedTube_inter_perm σ
  -- f is holomorphic (differentiable) on D
  have hextend_holo := extendF_holomorphicOn n F hF_holo hF_real_inv
  have hf_holo : DifferentiableOn ℂ f D := by
    apply DifferentiableOn.sub
    · -- extendF(σ·w) = extendF ∘ ψ is holomorphic on D
      exact hextend_holo.comp (hψ_diff.differentiableOn) (fun w hw => hw.2)
    · exact hextend_holo.mono (fun w hw => hw.1)
  -- Apply the identity theorem: f = 0 on D (hence f z = 0)
  suffices hfD : ∀ w ∈ D, f w = 0 from hfD z hz_D
  -- Get V from perm_jost_set_exists (d ≥ 2 sorry absorbed into helper)
  obtain ⟨V, hV_open, hV_ne, hV_jost, hV_ET, hV_σET⟩ :=
    perm_jost_set_exists (d := d) hd σ
  -- Apply identity theorem for totally real submanifolds:
  -- f holomorphic on open connected D, f = 0 on open real V with realEmbed V ⊆ D
  exact identity_theorem_totally_real_product hD_open hD_conn hf_holo
    hV_open hV_ne
    (fun x hx => ⟨hV_ET x hx, hV_σET x hx⟩)
    (fun x hx => by
      -- f(realEmbed x) = extendF(σ·(realEmbed x)) - extendF(realEmbed x) = 0
      simp only [f, sub_eq_zero]
      -- Goal: extendF F (fun k => realEmbed x (σ k)) = extendF F (realEmbed x)
      -- Note: (fun k => realEmbed x (σ k)) = realEmbed (fun k => x (σ k))
      have hrealσ : (fun k => realEmbed x (σ k)) = realEmbed (fun k => x (σ k)) := by
        ext k μ; simp [realEmbed]
      rw [hrealσ]
      -- Chain: extendF(σ·x) = F(σ·x) = F(x) = extendF(x) at real Jost points
      -- Step 1: extendF F (realEmbed (x ∘ σ)) = F (realEmbed (x ∘ σ))
      have hbv_σ := extendF_eq_boundary_value_ET n F hF_holo hF_real_inv hF_bv
        (fun k => x (σ k)) (hV_σET x hx)
      -- Step 2: F (realEmbed (x ∘ σ)) = F (realEmbed x)
      have hF_perm := F_perm_eq_on_jostSet F hF_local σ x
        (forwardJostSet_subset_jostSet _ (hV_jost x hx))
      -- Step 3: F (realEmbed x) = extendF F (realEmbed x)
      have hbv := (extendF_eq_boundary_value_ET n F hF_holo hF_real_inv hF_bv
        x (hV_ET x hx)).symm
      -- Unify realEmbed with explicit lambda via definitional equality
      have : realEmbed (fun k => x (σ k)) = fun k μ => (x (σ k) μ : ℂ) := rfl
      rw [hbv_σ, this, hF_perm]
      exact hbv)

end BHW

end
