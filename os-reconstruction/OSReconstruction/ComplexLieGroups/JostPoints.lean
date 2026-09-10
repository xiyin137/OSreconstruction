/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.ComplexLieGroups.BHWCore
import OSReconstruction.ComplexLieGroups.GeodesicConvexity
import OSReconstruction.SCV.IdentityTheorem
import OSReconstruction.SCV.TotallyRealIdentity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv































noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace BHW
open scoped Matrix.Norms.Operator

variable {d : ℕ}

namespace BHW

open BHWCore



/-- A real vector is spacelike if its Minkowski norm is positive:
    -ζ₀² + ζ₁² + ... + ζ_d² > 0, i.e., spatial norm exceeds time component. -/
def IsSpacelike (d : ℕ) (ζ : Fin (d + 1) → ℝ) : Prop :=
  ∑ μ, minkowskiSignature d μ * ζ μ ^ 2 > 0

/-- A purely spatial unit vector is spacelike. -/
theorem isSpacelike_spatial_unit (hd : 1 ≤ d) :
    IsSpacelike d (fun μ : Fin (d + 1) => if μ = ⟨1, by omega⟩ then 1 else 0) := by
  simp only [IsSpacelike]
  rw [Finset.sum_eq_single ⟨1, by omega⟩]
  · simp [LorentzLieGroup.minkowskiSignature]
  · intro μ _ hμ
    simp [hμ]
  · exact absurd (Finset.mem_univ _)

/-- Scaling a spacelike vector by a nonzero scalar preserves spacelikeness. -/
theorem isSpacelike_smul {η : Fin (d + 1) → ℝ} (hη : IsSpacelike d η)
    {c : ℝ} (hc : c ≠ 0) :
    IsSpacelike d (c • η) := by
  simp only [IsSpacelike, Pi.smul_apply, smul_eq_mul] at *
  have hsum :
      ∑ μ, LorentzLieGroup.minkowskiSignature d μ * (c * η μ) ^ 2 =
        c ^ 2 * ∑ μ, LorentzLieGroup.minkowskiSignature d μ * η μ ^ 2 := by
    trans ∑ μ, c ^ 2 * (LorentzLieGroup.minkowskiSignature d μ * η μ ^ 2)
    · congr 1
      ext μ
      ring
    · rw [← Finset.mul_sum]
  rw [hsum]
  exact mul_pos (sq_pos_of_ne_zero hc) hη

/-- The pairwise spacelike set: real configurations where every position vector is
    spacelike and every pairwise difference is spacelike. Used for locality arguments
    (hF_local applies when x_{i+1} - x_i is spacelike). -/
def JostSet (d n : ℕ) : Set (Fin n → Fin (d + 1) → ℝ) :=
  { x | (∀ i : Fin n, IsSpacelike d (x i)) ∧
        (∀ i j : Fin n, i ≠ j → IsSpacelike d (fun μ => x i μ - x j μ)) }

/-- Embed a real configuration as a complex one. -/
def realEmbed (x : Fin n → Fin (d + 1) → ℝ) : Fin n → Fin (d + 1) → ℂ :=
  fun k μ => (x k μ : ℂ)

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



/-- `extendF` is holomorphic on the extended tube.
    At each z₀ ∈ T'_n, write z₀ = Λ₀·w₀ with w₀ ∈ FT, then
    extendF(z) = F(Λ₀⁻¹·z) near z₀. -/
theorem extendF_holomorphicOn (n : ℕ) (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_cinv : ∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ForwardTube d n → complexLorentzAction Λ z ∈ ForwardTube d n →
      F (complexLorentzAction Λ z) = F z) :
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
    exact extendF_preimage_eq n F hF_cinv hex.choose_spec.1 hz_V
      (hex.choose_spec.2.choose_spec.symm.trans hz_eq)
  -- F ∘ ψ is differentiable at z₀
  have hFψ_diff : DifferentiableAt ℂ (fun z => F (ψ z)) z₀ :=
    ((hF_holo _ hz₀_V).differentiableAt (isOpen_forwardTube.mem_nhds hz₀_V)).comp
      z₀ (hψ_diff z₀)
  exact (hfeq.differentiableAt_iff.mpr hFψ_diff).differentiableWithinAt



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

/-- For a compactly supported Schwartz test function whose real support lies in the
extended tube, the forward-tube boundary-value integrals converge to the pairing with
`extendF` on the real support.

This is the distributional replacement for pointwise boundary-value theorems such as
`extendF_eq_boundary_value_ET`: the conclusion is only an integral identity against a
test function, which is the natural boundary-value statement for tempered applications. -/
theorem tendsto_extendF_boundary_integral_of_hasCompactSupport_ET
    (n : ℕ) (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_cinv : ∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
      z ∈ ForwardTube d n → complexLorentzAction Λ z ∈ ForwardTube d n →
      F (complexLorentzAction Λ z) = F z)
    (φ : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ)
    (hφ_compact : HasCompactSupport (φ : (Fin n → Fin (d + 1) → ℝ) → ℂ))
    (η : Fin n → Fin (d + 1) → ℝ)
    (hη_FT : ∀ (x : Fin n → Fin (d + 1) → ℝ) (ε : ℝ), 0 < ε →
      (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) ∈ ForwardTube d n)
    (hφ_ET : ∀ x ∈ tsupport (φ : (Fin n → Fin (d + 1) → ℝ) → ℂ),
      realEmbed x ∈ ExtendedTube d n) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ x : Fin n → Fin (d + 1) → ℝ,
        F (fun k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I) * φ x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ x : Fin n → Fin (d + 1) → ℝ, extendF F (realEmbed x) * φ x)) := by
  let zε : (Fin n → Fin (d + 1) → ℝ) → ℝ → (Fin n → Fin (d + 1) → ℂ) :=
    fun x ε k μ => (x k μ : ℂ) + ε * (η k μ : ℂ) * Complex.I
  have hextend_holo := extendF_holomorphicOn n F hF_holo hF_cinv
  have hextend_cont : ContinuousOn (extendF F) (ExtendedTube d n) :=
    hextend_holo.continuousOn
  let K : Set ((Fin n → Fin (d + 1) → ℝ) × ℝ) :=
    tsupport (φ : (Fin n → Fin (d + 1) → ℝ) → ℂ) ×ˢ Set.Icc (0 : ℝ) 1
  have hK_compact : IsCompact K := by
    simpa [K] using hφ_compact.isCompact.prod (isCompact_Icc (a := (0 : ℝ)) (b := (1 : ℝ)))
  let q : ((Fin n → Fin (d + 1) → ℝ) × ℝ) → ℂ := fun p => extendF F (zε p.1 p.2)
  have hzε_cont : Continuous fun p : (Fin n → Fin (d + 1) → ℝ) × ℝ => zε p.1 p.2 := by
    refine continuous_pi ?_
    intro k
    refine continuous_pi ?_
    intro μ
    have h1' : Continuous fun p : (Fin n → Fin (d + 1) → ℝ) × ℝ => p.1 k μ :=
      (continuous_apply μ).comp ((continuous_apply k).comp continuous_fst)
    have h1 : Continuous fun p : (Fin n → Fin (d + 1) → ℝ) × ℝ => ((p.1 k μ : ℝ) : ℂ) := by
      exact Complex.continuous_ofReal.comp h1'
    have h2 : Continuous fun p : (Fin n → Fin (d + 1) → ℝ) × ℝ =>
        ((p.2 : ℝ) : ℂ) * (η k μ : ℂ) * Complex.I := by
      simpa using
        (((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const).mul continuous_const)
    simpa [zε] using h1.add h2
  have hK_sub : K ⊆ {p | zε p.1 p.2 ∈ ExtendedTube d n} := by
    intro p hp
    rcases hp with ⟨hx, hε⟩
    rcases Set.mem_Icc.mp hε with ⟨hε0, hε1⟩
    by_cases hzero : p.2 = 0
    · have hxET : realEmbed p.1 ∈ ExtendedTube d n := hφ_ET p.1 hx
      simpa [zε, realEmbed, hzero]
        using hxET
    · have hεpos : 0 < p.2 := lt_of_le_of_ne hε0 (Ne.symm hzero)
      exact forwardTube_subset_extendedTube (hη_FT p.1 p.2 hεpos)
  have hq_cont : ContinuousOn q K := by
    intro p hp
    have hpET : zε p.1 p.2 ∈ ExtendedTube d n := hK_sub hp
    change ContinuousWithinAt ((extendF F) ∘ fun p : (Fin n → Fin (d + 1) → ℝ) × ℝ => zε p.1 p.2) K p
    exact ContinuousWithinAt.comp
      (f := fun p : (Fin n → Fin (d + 1) → ℝ) × ℝ => zε p.1 p.2)
      (g := extendF F) (s := K) (t := ExtendedTube d n) (x := p)
      (hextend_cont.continuousWithinAt hpET)
      (hzε_cont.continuousAt.continuousWithinAt) hK_sub
  obtain ⟨C, hC⟩ := hK_compact.exists_bound_of_continuousOn (f := fun p => ‖q p‖) (hq_cont.norm)
  let bound : (Fin n → Fin (d + 1) → ℝ) → ℝ := fun x => C * ‖(φ : (Fin n → Fin (d + 1) → ℝ) → ℂ) x‖
  have hbound_cont : Continuous bound := continuous_const.mul φ.continuous.norm
  have hbound_support_subset :
      Function.support bound ⊆ Function.support (φ : (Fin n → Fin (d + 1) → ℝ) → ℂ) := by
    intro x hx
    by_contra hnot
    have hφx : φ x = 0 := by simpa [Function.mem_support] using hnot
    have : bound x = 0 := by simp [bound, hφx]
    exact hx (by simp [Function.mem_support, this])
  have hbound_compact : HasCompactSupport bound :=
    HasCompactSupport.of_support_subset_isCompact hφ_compact.isCompact
      (Set.Subset.trans hbound_support_subset subset_closure)
  have hbound_int : MeasureTheory.Integrable bound :=
    hbound_cont.integrable_of_hasCompactSupport hbound_compact
  have h_meas :
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        MeasureTheory.AEStronglyMeasurable
          (fun x : Fin n → Fin (d + 1) → ℝ =>
            F (zε x ε) * φ x) := by
    apply Filter.eventually_of_mem self_mem_nhdsWithin
    intro ε hε
    have hzε_cont_fixed :
        Continuous (fun x : Fin n → Fin (d + 1) → ℝ => zε x ε) := by
      refine continuous_pi ?_
      intro k
      refine continuous_pi ?_
      intro μ
      exact (Complex.continuous_ofReal.comp
          ((continuous_apply μ).comp ((continuous_apply k).comp continuous_id))).add
        (((Complex.continuous_ofReal.comp continuous_const).mul continuous_const).mul
          continuous_const)
    have hcont : Continuous fun x : Fin n → Fin (d + 1) → ℝ => F (zε x ε) :=
      hF_holo.continuousOn.comp_continuous hzε_cont_fixed
        (fun x => hη_FT x ε (Set.mem_Ioi.mp hε))
    exact (hcont.mul φ.continuous).aestronglyMeasurable
  have h_bound :
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ∀ᵐ x, ‖F (zε x ε) * φ x‖ ≤ bound x := by
    have h_mem : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      mem_nhdsWithin.mpr ⟨Set.Iio 1, isOpen_Iio, by norm_num, fun ε hε =>
        Set.mem_Ioo.mpr ⟨Set.mem_Ioi.mp hε.2, Set.mem_Iio.mp hε.1⟩⟩
    apply Filter.eventually_of_mem h_mem
    intro ε hε
    apply Filter.Eventually.of_forall
    intro x
    by_cases hx : x ∈ Function.support (φ : (Fin n → Fin (d + 1) → ℝ) → ℂ)
    · have hxK : (x, ε) ∈ K := ⟨subset_closure hx, Set.mem_Icc.mpr ⟨le_of_lt (Set.mem_Ioo.mp hε).1,
          le_of_lt (Set.mem_Ioo.mp hε).2⟩⟩
      have hqC : ‖q (x, ε)‖ ≤ C := by
        simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hC _ hxK
      have hEq : F (zε x ε) = q (x, ε) := by
        change F (zε x ε) = extendF F (zε x ε)
        symm
        exact extendF_eq_on_forwardTube n F hF_cinv _ (hη_FT x ε (Set.mem_Ioo.mp hε).1)
      calc
        ‖F (zε x ε) * φ x‖ = ‖q (x, ε)‖ * ‖φ x‖ := by rw [hEq, norm_mul]
        _ ≤ C * ‖φ x‖ := by exact mul_le_mul_of_nonneg_right hqC (norm_nonneg _)
        _ = bound x := by simp [bound]
    · have hφx : φ x = 0 := by simpa [Function.mem_support] using hx
      simp [bound, hφx]
  have h_pointwise :
      ∀ x : Fin n → Fin (d + 1) → ℝ,
        Filter.Tendsto
          (fun ε : ℝ => F (zε x ε) * φ x)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (extendF F (realEmbed x) * φ x)) := by
    intro x
    by_cases hx : x ∈ Function.support (φ : (Fin n → Fin (d + 1) → ℝ) → ℂ)
    · have hxET : realEmbed x ∈ ExtendedTube d n := hφ_ET x (subset_closure hx)
      have hpath_cont : Continuous fun ε : ℝ => zε x ε := by
        refine continuous_pi ?_
        intro k
        refine continuous_pi ?_
        intro μ
        exact continuous_const.add
          (((Complex.continuous_ofReal.comp continuous_id).mul continuous_const).mul
            continuous_const)
      have hpath_zero : zε x 0 = realEmbed x := by
        ext k μ
        simp [zε, realEmbed]
      have hpath_maps :
          Set.MapsTo (fun ε : ℝ => zε x ε) (Set.Ioi (0 : ℝ)) (ExtendedTube d n) := by
        intro ε hε
        exact forwardTube_subset_extendedTube (hη_FT x ε hε)
      have hpath_tends :
          Filter.Tendsto (fun ε : ℝ => zε x ε)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhdsWithin (realEmbed x) (ExtendedTube d n)) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, Filter.eventually_of_mem self_mem_nhdsWithin hpath_maps⟩
        have h :
            Filter.Tendsto (fun ε : ℝ => zε x ε)
              (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (zε x 0)) :=
          hpath_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        rwa [hpath_zero] at h
      have hcont_ext :
          Filter.Tendsto (fun ε : ℝ => extendF F (zε x ε))
            (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds (extendF F (realEmbed x))) :=
        (hextend_cont.continuousWithinAt hxET).tendsto.comp hpath_tends
      have h_eq_eventually :
          (fun ε : ℝ => extendF F (zε x ε)) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
            (fun ε : ℝ => F (zε x ε)) := by
        apply Filter.eventually_of_mem self_mem_nhdsWithin
        intro ε hε
        exact extendF_eq_on_forwardTube n F hF_cinv _ (hη_FT x ε (Set.mem_Ioi.mp hε))
      have hF_tends :
          Filter.Tendsto (fun ε : ℝ => F (zε x ε))
            (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds (extendF F (realEmbed x))) :=
        Filter.Tendsto.congr' h_eq_eventually hcont_ext
      exact hF_tends.mul tendsto_const_nhds
    · have hφx : φ x = 0 := by simpa [Function.mem_support] using hx
      simp [hφx]
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence (bound := bound)
  · exact h_meas
  · exact h_bound
  · exact hbound_int
  · apply Filter.Eventually.of_forall
    intro x
    exact h_pointwise x



-- Row simplification lemmas for the spatial rotation matrix.

-- The spatial rotation preserves the Minkowski metric.

-- The spatial rotation has determinant 1.
-- Strategy: MᵀηM = η gives det²=1. Then we use a continuous path argument:
-- the family M(t) for t ∈ [0,1] where M(0)=I and M(1)=M is continuous
-- with det(M(t))² = 1, so det is constant = det(I) = 1.
-- We implement this via the matrix equation approach and the intermediate value theorem.

-- The spatial rotation as a ComplexLorentzGroup element.

-- The action of the spatial rotation on a single vector:
-- (R·v)_0 = v_0 (time fixed)
-- (R·v)_1 = c * v_1 + s * v_2  where c = a/r, s = b/r
-- (R·v)_2 = -s * v_1 + c * v_2
-- (R·v)_μ = v_μ  for μ ≥ 3

end BHW

end
