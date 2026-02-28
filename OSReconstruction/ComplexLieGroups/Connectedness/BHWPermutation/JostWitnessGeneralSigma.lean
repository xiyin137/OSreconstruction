/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors

# Jost Witness Construction for General σ (d ≥ 2)

This file constructs a Jost point that lies in ET ∩ σ⁻¹·ET for any permutation σ,
when d ≥ 2. This is one of the two obligations needed to close the sorry at
PermutationFlow.lean:1490.

## Key idea

For d ≥ 2 (at least 2 spatial dimensions), we can simultaneously encode two
orderings in different spatial coordinates:
  - Coordinate 1 encodes the natural order: (k+1)·a increases with k
  - Coordinate 2 encodes the σ-order: (σ⁻¹(k)+1)·b increases when reindexed by σ

The Wick rotation in the (0,1) plane sends the natural ordering into V⁺,
while the Wick rotation in the (0,2) plane sends the σ-ordering into V⁺.

## Construction

  x_k = (0, (k+1)·a, (σ⁻¹(k)+1)·b, 0, ..., 0)   for a, b > 0

Then:
  1. x ∈ ForwardJostSet (using existing (0,1) Wick rotation from JostPoints.lean)
  2. x∘σ can be mapped to FT via the (0,2) Wick rotation (new infrastructure)
  3. x ∈ JostSet (all differences purely spatial)

## What this provides

Obligation (1) of `hExtPerm_of_geometric`: a Jost witness with
  realEmbed(x) ∈ ET and realEmbed(x∘σ) ∈ ET.
-/
import OSReconstruction.ComplexLieGroups.JostPoints
import OSReconstruction.ComplexLieGroups.BHWCore

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter
open BHW BHWCore

variable {d : ℕ}

namespace JostWitnessGeneralSigma

/-! ## Part 1: Generalized Wick rotation in the (0,j) plane -/

/-- Wick rotation matrix in the (0,j) plane for j ≥ 1.
Swaps coordinates 0 and j with a factor of -I:
  e₀ ↦ -I · eⱼ,  eⱼ ↦ -I · e₀,  eₖ ↦ eₖ for k ≠ 0,j.
This is the (0,j)-analog of `wickMatrix` (which is the j=1 case). -/
def wickMatrixJ (d : ℕ) (j : Fin (d + 1)) (_hj : j ≠ 0) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  fun μ ν =>
    if μ = 0 ∧ ν = j then -Complex.I
    else if μ = j ∧ ν = 0 then -Complex.I
    else if μ = ν ∧ μ ≠ 0 ∧ μ ≠ j then 1
    else 0

/-- Row 0 of wickMatrixJ: nonzero only at column j. -/
lemma wickMatrixJ_row0 (d : ℕ) (j : Fin (d + 1)) (hj : j ≠ 0)
    (ν : Fin (d + 1)) :
    wickMatrixJ d j hj 0 ν = if ν = j then -Complex.I else 0 := by
  unfold wickMatrixJ
  by_cases hν : ν = j
  · rw [if_pos ⟨rfl, hν⟩, if_pos hν]
  · rw [if_neg (by intro ⟨_, h⟩; exact hν h)]
    rw [if_neg (by intro ⟨h, _⟩; exact hj h.symm)]
    rw [if_neg (by intro ⟨_, h, _⟩; exact h rfl)]
    rw [if_neg hν]

/-- Row j of wickMatrixJ: nonzero only at column 0. -/
lemma wickMatrixJ_rowj (d : ℕ) (j : Fin (d + 1)) (hj : j ≠ 0)
    (ν : Fin (d + 1)) :
    wickMatrixJ d j hj j ν = if ν = 0 then -Complex.I else 0 := by
  unfold wickMatrixJ
  by_cases hν : ν = 0
  · subst hν
    rw [if_neg (by intro ⟨h, _⟩; exact hj h)]
    rw [if_pos ⟨rfl, rfl⟩, if_pos rfl]
  · rw [if_neg (by intro ⟨h, _⟩; exact hj h)]
    rw [if_neg (by intro ⟨_, h⟩; exact hν h)]
    rw [if_neg (by intro ⟨_, _, h⟩; exact h rfl)]
    rw [if_neg hν]

/-- Row μ ≠ 0, μ ≠ j of wickMatrixJ: nonzero only at column μ. -/
lemma wickMatrixJ_row_other (d : ℕ) (j : Fin (d + 1)) (hj : j ≠ 0)
    (μ : Fin (d + 1)) (hμ0 : μ ≠ 0) (hμj : μ ≠ j) (ν : Fin (d + 1)) :
    wickMatrixJ d j hj μ ν = if ν = μ then 1 else 0 := by
  unfold wickMatrixJ
  rw [if_neg (by intro ⟨h, _⟩; exact hμ0 h)]
  rw [if_neg (by intro ⟨h, _⟩; exact hμj h)]
  by_cases hνμ : ν = μ
  · rw [if_pos ⟨hνμ.symm, hμ0, hμj⟩, if_pos hνμ]
  · rw [if_neg (by intro ⟨h, _, _⟩; exact hνμ h.symm), if_neg hνμ]

lemma wickMatrixJ_col0 (d : ℕ) (j : Fin (d + 1)) (hj : j ≠ 0)
    (α : Fin (d + 1)) :
    wickMatrixJ d j hj α 0 = if α = j then -Complex.I else 0 := by
  unfold wickMatrixJ
  rw [if_neg (by intro ⟨_, h⟩; exact hj h.symm)]
  by_cases hαj : α = j
  · rw [if_pos ⟨hαj, rfl⟩, if_pos hαj]
  · rw [if_neg (by intro ⟨h, _⟩; exact hαj h), if_neg hαj]
    rw [if_neg (by intro ⟨h1, h2, _⟩; exact h2 h1)]

lemma wickMatrixJ_colj (d : ℕ) (j : Fin (d + 1)) (hj : j ≠ 0)
    (α : Fin (d + 1)) :
    wickMatrixJ d j hj α j = if α = 0 then -Complex.I else 0 := by
  unfold wickMatrixJ
  by_cases hα0 : α = 0
  · rw [if_pos ⟨hα0, rfl⟩, if_pos hα0]
  · rw [if_neg (by intro ⟨h, _⟩; exact hα0 h), if_neg hα0]
    rw [if_neg (by intro ⟨_, h⟩; exact hj h)]
    rw [if_neg (by intro ⟨h, _, h2⟩; exact h2 h)]

lemma wickMatrixJ_col_other (d : ℕ) (j : Fin (d + 1)) (hj : j ≠ 0)
    (μ : Fin (d + 1)) (hμ0 : μ ≠ 0) (hμj : μ ≠ j)
    (α : Fin (d + 1)) :
    wickMatrixJ d j hj α μ = if α = μ then 1 else 0 := by
  unfold wickMatrixJ
  rw [if_neg (by intro ⟨_, h⟩; exact hμj h)]
  rw [if_neg (by intro ⟨_, h⟩; exact hμ0 h)]
  by_cases hαμ : α = μ
  · rw [if_pos ⟨hαμ, hαμ ▸ hμ0, hαμ ▸ hμj⟩, if_pos hαμ]
  · rw [if_neg (by intro ⟨h, _, _⟩; exact hαμ h), if_neg hαμ]

lemma wickMatrixJ_support (d : ℕ) (j : Fin (d + 1)) (hj : j ≠ 0)
    (α μ : Fin (d + 1)) (h : wickMatrixJ d j hj α μ ≠ 0) :
    (α = 0 ∧ μ = j) ∨ (α = j ∧ μ = 0) ∨
    (α = μ ∧ α ≠ 0 ∧ α ≠ j) := by
  unfold wickMatrixJ at h
  split_ifs at h with h1 h2 h3
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)
  · exact absurd rfl h

/-- The (0,j) Wick rotation preserves the Minkowski metric. -/
lemma wickMatrixJ_metric (d : ℕ) (j : Fin (d + 1)) (hj : j ≠ 0) :
    ∀ (μ ν : Fin (d + 1)),
    ∑ α : Fin (d + 1),
      (minkowskiSignature d α : ℂ) * wickMatrixJ d j hj α μ * wickMatrixJ d j hj α ν =
    if μ = ν then (minkowskiSignature d μ : ℂ) else 0 := by
  intro μ ν
  by_cases hμν : μ = ν
  · -- Diagonal case
    subst hμν
    rw [if_pos rfl]
    by_cases hμ0 : μ = 0
    · subst hμ0
      simp only [wickMatrixJ_col0]
      simp only [mul_ite, ite_mul, mul_zero, zero_mul, mul_neg,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      simp [minkowskiSignature, hj]
    · by_cases hμj : μ = j
      · subst hμj
        simp only [wickMatrixJ_colj]
        simp only [mul_ite, ite_mul, mul_zero, zero_mul, mul_neg,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        simp [minkowskiSignature, hj]
      · simp only [wickMatrixJ_col_other d j hj μ hμ0 hμj]
        simp only [mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  · rw [if_neg hμν]
    -- Off-diagonal case: at least one factor per summand is zero
    apply Finset.sum_eq_zero
    intro α _
    suffices wickMatrixJ d j hj α μ * wickMatrixJ d j hj α ν = 0 by
      rw [mul_assoc]
      simp [this]
    by_cases hWμ : wickMatrixJ d j hj α μ = 0
    · simp [hWμ]
    · suffices wickMatrixJ d j hj α ν = 0 by
        simp [this]
      rcases wickMatrixJ_support d j hj α μ hWμ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hαμ, hα0, hαj⟩
      · -- row 0, col j -> W(0, ν) = 0 since ν ≠ j
        unfold wickMatrixJ
        rw [if_neg (by intro ⟨_, h⟩; exact hμν h.symm)]
        rw [if_neg (by intro ⟨h, _⟩; exact hj h.symm)]
        rw [if_neg (by intro ⟨_, h, _⟩; exact h rfl)]
      · -- row j, col 0 -> W(j, ν) = 0 since ν ≠ 0
        unfold wickMatrixJ
        rw [if_neg (by intro ⟨h, _⟩; exact hj h)]
        rw [if_neg (by intro ⟨_, h⟩; exact hμν h.symm)]
        rw [if_neg (by intro ⟨_, _, h3⟩; exact h3 rfl)]
      · -- row α = μ with α ≠ 0,j -> W(α, ν) = 0 since ν ≠ α = μ
        unfold wickMatrixJ
        rw [if_neg (by intro ⟨h, _⟩; exact hα0 h)]
        rw [if_neg (by intro ⟨h, _⟩; exact hαj h)]
        rw [if_neg (by intro ⟨h, _, _⟩; rw [hαμ] at h; exact hμν h)]

/-- The (0,j) Wick rotation has determinant 1. -/
lemma wickMatrixJ_det (d : ℕ) (j : Fin (d + 1)) (hj : j ≠ 0) :
    (wickMatrixJ d j hj).det = 1 := by
  rw [Matrix.det_apply]
  have h0j : (0 : Fin (d + 1)) ≠ j := by
    intro h
    exact hj h.symm
  -- All non-swap permutations contribute 0
  have hother : ∀ σ : Equiv.Perm (Fin (d + 1)), σ ∈ Finset.univ →
      σ ≠ Equiv.swap (0 : Fin (d + 1)) j →
      Equiv.Perm.sign σ • ∏ i, wickMatrixJ d j hj (σ i) i = 0 := by
    intro σ _ hσ
    suffices h : ∃ i, wickMatrixJ d j hj (σ i) i = 0 by
      obtain ⟨i, hi⟩ := h
      rw [show ∏ k, wickMatrixJ d j hj (σ k) k = 0 from
          Finset.prod_eq_zero (f := fun k => wickMatrixJ d j hj (σ k) k)
            (Finset.mem_univ i) hi, smul_zero]
    by_contra hall
    push_neg at hall
    apply hσ
    ext i
    by_cases hi0 : i = 0
    · subst hi0
      have h := hall 0
      rw [wickMatrixJ_col0] at h
      simp only [ne_eq, ite_eq_right_iff, neg_eq_zero, Complex.I_ne_zero,
        imp_false, not_not] at h
      rw [h, Equiv.swap_apply_left]
    · by_cases hij : i = j
      · have h := hall i
        rw [hij] at h
        rw [wickMatrixJ_colj] at h
        simp only [ne_eq, ite_eq_right_iff, neg_eq_zero, Complex.I_ne_zero,
          imp_false, not_not] at h
        simp [hij, h, Equiv.swap_apply_right]
      · have h := hall i
        rw [wickMatrixJ_col_other d j hj i hi0 hij] at h
        simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at h
        rw [h, Equiv.swap_apply_of_ne_of_ne hi0 hij]
  rw [Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) hother]
  rw [Equiv.Perm.sign_swap h0j]
  simp only [Units.neg_smul, one_smul]
  -- Need: -(∏ i, wickMatrixJ d j hj (swap(0,j)(i)) i) = 1
  rw [Fin.prod_univ_succ, Equiv.swap_apply_left, wickMatrixJ_col0, if_pos rfl]
  have hrest : ∀ k : Fin d, wickMatrixJ d j hj
      (Equiv.swap (0 : Fin (d + 1)) j (Fin.succ k)) (Fin.succ k) =
      if Fin.succ k = j then -Complex.I else 1 := by
    intro k
    by_cases hk : Fin.succ k = j
    · rw [if_pos hk, hk, Equiv.swap_apply_right, wickMatrixJ_colj, if_pos rfl]
    · have hks0 : Fin.succ k ≠ (0 : Fin (d + 1)) := Fin.succ_ne_zero k
      rw [if_neg hk, Equiv.swap_apply_of_ne_of_ne hks0 hk,
        wickMatrixJ_col_other d j hj (Fin.succ k) hks0 hk (Fin.succ k), if_pos rfl]
  simp only [hrest]
  obtain ⟨k0, hk0⟩ := Fin.exists_succ_eq_of_ne_zero hj
  have hprod :
      ∏ k : Fin d, (if Fin.succ k = j then -Complex.I else (1 : ℂ)) = -Complex.I := by
    rw [Finset.prod_eq_single k0]
    · simp [hk0]
    · intro b _ hb
      rw [if_neg]
      intro hbj
      apply hb
      apply Fin.ext
      have hval : (Fin.succ b).val = (Fin.succ k0).val := by
        exact congrArg Fin.val (hbj.trans hk0.symm)
      exact Nat.succ.inj (by simpa [Fin.val_succ] using hval)
    · simp
  rw [hprod]
  simp

/-- The (0,j) Wick rotation as a ComplexLorentzGroup element. -/
def wickCLGJ (d : ℕ) (j : Fin (d + 1)) (hj : j ≠ 0) : ComplexLorentzGroup d where
  val := wickMatrixJ d j hj
  metric_preserving := wickMatrixJ_metric d j hj
  proper := wickMatrixJ_det d j hj

/-! ## Part 2: The Jost witness point -/

/-- The Jost witness configuration: x_k = (0, (k+1)·a, (σ⁻¹(k)+1)·b, 0, ..., 0).
    For d ≥ 2, this uses coordinates 0, 1, and 2 of Fin (d+1). -/
def jostWitnessPoint (σ : Equiv.Perm (Fin n)) (a b : ℝ) (_ha : 0 < a) (_hb : 0 < b)
    (hd : 2 ≤ d) :
    Fin n → Fin (d + 1) → ℝ :=
  fun k μ =>
    if μ = ⟨1, by omega⟩ then ((k : ℕ) + 1 : ℝ) * a
    else if μ = ⟨2, by omega⟩ then ((σ⁻¹ k : ℕ) + 1 : ℝ) * b
    else 0

/-- The consecutive differences of the Jost witness in the first spatial coordinate
    are all equal to a > 0. -/
lemma jostWitness_consec_diff_coord1 (σ : Equiv.Perm (Fin n))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hd : 2 ≤ d)
    (k : Fin n) :
    consecutiveDiff (jostWitnessPoint σ a b ha hb hd) k ⟨1, by omega⟩ =
      if (k : ℕ) = 0 then a else a := by
  by_cases hk : (k : ℕ) = 0
  · simp [consecutiveDiff, jostWitnessPoint, hk]
  · have hk1 : 1 ≤ k.val := Nat.one_le_iff_ne_zero.mpr hk
    have hcast : (↑(k.val - 1) : ℝ) + 1 = (k : ℝ) := by
      have hnat : k.val - 1 + 1 = k.val := Nat.sub_add_cancel hk1
      exact_mod_cast hnat
    simp [consecutiveDiff, jostWitnessPoint, hk]
    nlinarith [hcast]

/-- The Jost witness lies in ForwardJostSet (using the (0,1) Wick rotation).
    This requires |ζ_0| < ζ_1, i.e., 0 < a for each consecutive difference. -/
theorem jostWitness_mem_forwardJostSet (σ : Equiv.Perm (Fin n))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hd : 2 ≤ d) (hd1 : 1 ≤ d := by omega) :
    jostWitnessPoint σ a b ha hb hd ∈ ForwardJostSet d n hd1 := by
  intro k
  have htime :
      consecutiveDiff (jostWitnessPoint σ a b ha hb hd) k 0 = 0 := by
    by_cases hk : (k : ℕ) = 0
    · simp [consecutiveDiff, jostWitnessPoint, hk]
    · simp [consecutiveDiff, jostWitnessPoint, hk]
  have hspat :
      consecutiveDiff (jostWitnessPoint σ a b ha hb hd) k ⟨1, by omega⟩ = a := by
    have h := jostWitness_consec_diff_coord1 σ a b ha hb hd k
    by_cases hk : (k : ℕ) = 0
    · simpa [hk] using h
    · simpa [hk] using h
  change |consecutiveDiff (jostWitnessPoint σ a b ha hb hd) k 0| <
      consecutiveDiff (jostWitnessPoint σ a b ha hb hd) k ⟨1, by omega⟩
  rw [htime, hspat]
  simpa using ha

/-- realEmbed of the Jost witness is in the extended tube.
    This follows from ForwardJostSet ⊆ ExtendedTube via the existing
    `forwardJostSet_subset_extendedTube`. -/
theorem jostWitness_realEmbed_mem_ET (σ : Equiv.Perm (Fin n))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hd : 2 ≤ d) :
    realEmbed (jostWitnessPoint σ a b ha hb hd) ∈ ExtendedTube d n := by
  have hd1 : 1 ≤ d := by omega
  have h := jostWitness_mem_forwardJostSet σ a b ha hb hd
  exact forwardJostSet_subset_extendedTube hd1
    (jostWitnessPoint σ a b ha hb hd) h

/-! ## Part 3: The σ-permuted witness is in ET via (0,2) Wick rotation -/

/-- Define w such that wickCLGJ d ⟨2,...⟩ · w = realEmbed(x∘σ).
    The (0,2) Wick rotation swaps coordinates 0 and 2: eₒ ↦ -Ie₂, e₂ ↦ -Ie₀.
    So w_k = (I·(x∘σ)_k,2, (x∘σ)_k,1, I·(x∘σ)_k,0, (x∘σ)_k,3, ...).
    Since (x∘σ)_k,0 = 0, we get w_k,2 = 0.
    Since (x∘σ)_k,2 = (k+1)·b, we get w_k,0 = I·(k+1)·b.
    Since (x∘σ)_k,1 = (σ(k)+1)·a (real), we get w_k,1 = (σ(k)+1)·a. -/
def wickPreimage_j2 (σ : Equiv.Perm (Fin n))
    (a b : ℝ) (_ha : 0 < a) (_hb : 0 < b) (hd : 2 ≤ d) :
    Fin n → Fin (d + 1) → ℂ :=
  fun k μ =>
    if μ = (0 : Fin (d + 1)) then
      Complex.I * (((k : ℕ) + 1 : ℝ) * b : ℝ)
    else if μ = ⟨1, by omega⟩ then
      (((σ k : ℕ) + 1 : ℝ) * a : ℝ)
    else 0

/-- Simplification: σ⁻¹(σ(k)) = k. -/
lemma wickPreimage_j2_coord0_simp (σ : Equiv.Perm (Fin n))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hd : 2 ≤ d)
    (k : Fin n) :
    (wickPreimage_j2 σ a b ha hb hd k) (0 : Fin (d + 1)) =
      Complex.I * (((k : ℕ) + 1 : ℝ) * b : ℝ) := by
  simp [wickPreimage_j2]

/-- The preimage w is in the forward tube.
    Im(w_k) = ((k+1)·b, 0, 0, ...) ∈ V⁺.
    Im(w_{k+1} - w_k) = (b, 0, 0, ...) ∈ V⁺. -/
theorem wickPreimage_j2_mem_forwardTube (σ : Equiv.Perm (Fin n))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hd : 2 ≤ d) :
    wickPreimage_j2 σ a b ha hb hd ∈ ForwardTube d n := by
  intro k
  let η : Fin (d + 1) → ℝ := fun μ =>
    (wickPreimage_j2 σ a b ha hb hd k μ -
      (if h : k.val = 0 then (0 : Fin (d + 1) → ℂ)
       else wickPreimage_j2 σ a b ha hb hd ⟨k.val - 1, by omega⟩) μ).im
  change InOpenForwardCone d η
  have hη0 : η 0 = b := by
    by_cases hk : k.val = 0
    · simp [η, wickPreimage_j2, hk]
    · have hk1 : 1 ≤ k.val := Nat.one_le_iff_ne_zero.mpr hk
      simp [η, wickPreimage_j2, hk]
      have hcast : ((k.val - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
        exact_mod_cast (Nat.sub_add_cancel hk1)
      have hcast' : ((k.val - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        linarith [hcast]
      nlinarith [hcast']
  have hη_other : ∀ μ : Fin (d + 1), μ ≠ 0 → η μ = 0 := by
    intro μ hμ0
    by_cases hk : k.val = 0
    · by_cases hμ1 : μ = ⟨1, by omega⟩
      · subst hμ1
        simp [η, wickPreimage_j2, hk]
      · simp [η, wickPreimage_j2, hk, hμ0, hμ1]
    · by_cases hμ1 : μ = ⟨1, by omega⟩
      · subst hμ1
        simp [η, wickPreimage_j2, hk]
      · simp [η, wickPreimage_j2, hk, hμ0, hμ1]
  refine ⟨?_, ?_⟩
  · rw [hη0]
    exact hb
  · rw [Finset.sum_eq_single (0 : Fin (d + 1))]
    · simp [minkowskiSignature, hη0]
      nlinarith [hb]
    · intro μ _ hμ
      rw [hη_other μ hμ]
      simp
    · exact absurd (Finset.mem_univ (0 : Fin (d + 1)))

/-- The (0,2) Wick rotation maps the preimage to realEmbed(x∘σ).
    wickCLGJ d ⟨2,...⟩ · w = realEmbed(jostWitnessPoint ∘ σ). -/
theorem wickJ2_action_eq_realEmbed_sigma (σ : Equiv.Perm (Fin n))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hd : 2 ≤ d) :
    complexLorentzAction (wickCLGJ d ⟨2, by omega⟩ (by intro h; exact absurd (congr_arg Fin.val h) (by norm_num)))
      (wickPreimage_j2 σ a b ha hb hd) =
    realEmbed (fun k => jostWitnessPoint σ a b ha hb hd (σ k)) := by
  let j2 : Fin (d + 1) := ⟨2, by omega⟩
  let e1 : Fin (d + 1) := ⟨1, by omega⟩
  have hj2 : j2 ≠ 0 := by
    intro h
    exact absurd (congrArg Fin.val h) (by norm_num)
  change complexLorentzAction (wickCLGJ d j2 hj2) (wickPreimage_j2 σ a b ha hb hd) =
    realEmbed (fun k => jostWitnessPoint σ a b ha hb hd (σ k))
  ext k μ
  by_cases hμ0 : μ = 0
  · subst hμ0
    have hsum0 :
        (∑ ν, wickMatrixJ d j2 hj2 0 ν * wickPreimage_j2 σ a b ha hb hd k ν) = 0 := by
      simp_rw [wickMatrixJ_row0 d j2 hj2]
      refine Finset.sum_eq_zero ?_
      intro ν hν
      by_cases hνj2 : ν = j2
      · subst hνj2
        simp [wickPreimage_j2, j2]
      · simp [hνj2]
    simpa [complexLorentzAction, wickCLGJ, realEmbed, jostWitnessPoint, j2, e1] using hsum0
  · by_cases hμ2 : μ = j2
    · subst hμ2
      have hsum2 :
          (∑ ν, wickMatrixJ d j2 hj2 j2 ν * wickPreimage_j2 σ a b ha hb hd k ν) =
            ((((k : ℕ) + 1 : ℝ) * b : ℝ) : ℂ) := by
        simp_rw [wickMatrixJ_rowj d j2 hj2]
        rw [Finset.sum_eq_single (0 : Fin (d + 1))]
        · simp [wickPreimage_j2]
          ring_nf
          norm_num
        · intro ν _ hν0
          by_cases hν0' : ν = 0
          · exact (hν0 hν0').elim
          · simp [hν0']
        · intro h0
          exact (h0 (Finset.mem_univ (0 : Fin (d + 1)))).elim
      have hrhs2 :
          realEmbed (fun k => jostWitnessPoint σ a b ha hb hd (σ k)) k j2 =
            ((((k : ℕ) + 1 : ℝ) * b : ℝ) : ℂ) := by
        simp [realEmbed, jostWitnessPoint, j2, Equiv.symm_apply_apply]
      simpa [complexLorentzAction, wickCLGJ] using hsum2.trans hrhs2.symm
    · have hrow := wickMatrixJ_row_other d j2 hj2 μ hμ0 hμ2
      have hsumμ :
          (∑ ν, wickMatrixJ d j2 hj2 μ ν * wickPreimage_j2 σ a b ha hb hd k ν) =
            wickPreimage_j2 σ a b ha hb hd k μ := by
        simp_rw [hrow]
        simp [Finset.sum_ite_eq', Finset.mem_univ]
      have hrhsμ :
          realEmbed (fun k => jostWitnessPoint σ a b ha hb hd (σ k)) k μ =
            wickPreimage_j2 σ a b ha hb hd k μ := by
        by_cases hμ1 : μ = e1
        · subst hμ1
          simp [realEmbed, wickPreimage_j2, jostWitnessPoint, e1]
        · have hμ2' : μ ≠ (⟨2, by omega⟩ : Fin (d + 1)) := by
            simpa [j2] using hμ2
          simp [realEmbed, wickPreimage_j2, jostWitnessPoint, hμ0, hμ1, hμ2', e1]
      simpa [complexLorentzAction, wickCLGJ] using hsumμ.trans hrhsμ.symm

/-- **Main result**: realEmbed(x ∘ σ) ∈ ExtendedTube.
    The (0,2) Wick rotation provides the complex Lorentz witness. -/
theorem jostWitness_sigma_realEmbed_mem_ET (σ : Equiv.Perm (Fin n))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hd : 2 ≤ d) :
    realEmbed (fun k => jostWitnessPoint σ a b ha hb hd (σ k)) ∈ ExtendedTube d n := by
  rw [show realEmbed (fun k => jostWitnessPoint σ a b ha hb hd (σ k)) =
    complexLorentzAction (wickCLGJ d ⟨2, by omega⟩ (by intro h; exact absurd (congr_arg Fin.val h) (by norm_num)))
      (wickPreimage_j2 σ a b ha hb hd) from
    (wickJ2_action_eq_realEmbed_sigma σ a b ha hb hd).symm]
  exact Set.mem_iUnion.mpr
    ⟨wickCLGJ d ⟨2, by omega⟩ _, wickPreimage_j2 σ a b ha hb hd,
     wickPreimage_j2_mem_forwardTube σ a b ha hb hd, rfl⟩

/-! ## Part 4: JostSet membership -/

/-- The Jost witness is in JostSet: all pairwise differences are spacelike.
    Since all time components are 0, the Minkowski norm of x_i - x_j is
    (i-j)²a² + (σ⁻¹(i)-σ⁻¹(j))²b² > 0 for i ≠ j. -/
theorem jostWitness_mem_jostSet (σ : Equiv.Perm (Fin n))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hd : 2 ≤ d) :
    jostWitnessPoint σ a b ha hb hd ∈ JostSet d n := by
  constructor
  · intro i
    let e1 : Fin (d + 1) := ⟨1, by omega⟩
    have he1_sig : minkowskiSignature d e1 = 1 := by
      simp [minkowskiSignature, e1]
    have hx_e1 :
        jostWitnessPoint σ a b ha hb hd i e1 = (((i : ℕ) + 1 : ℝ) * a) := by
      simp [jostWitnessPoint, e1]
    have hx_nonzero : (((i : ℕ) + 1 : ℝ) * a) ≠ 0 := by
      refine mul_ne_zero ?_ (ne_of_gt ha)
      exact_mod_cast Nat.succ_ne_zero i.val
    have hterm_pos :
        0 < minkowskiSignature d e1 *
            (jostWitnessPoint σ a b ha hb hd i e1) ^ 2 := by
      rw [he1_sig, hx_e1]
      simpa [one_mul] using sq_pos_of_ne_zero hx_nonzero
    have hterm_le :
        minkowskiSignature d e1 * (jostWitnessPoint σ a b ha hb hd i e1) ^ 2 ≤
          ∑ μ : Fin (d + 1), minkowskiSignature d μ *
            (jostWitnessPoint σ a b ha hb hd i μ) ^ 2 := by
      have hnonneg :
          ∀ μ : Fin (d + 1),
            0 ≤ minkowskiSignature d μ * (jostWitnessPoint σ a b ha hb hd i μ) ^ 2 := by
        intro μ
        by_cases hμ0 : μ = 0
        · subst hμ0
          simp [jostWitnessPoint]
        · have hsig : minkowskiSignature d μ = 1 := by
            simp [minkowskiSignature, hμ0]
          rw [hsig]
          simpa [one_mul] using (sq_nonneg (jostWitnessPoint σ a b ha hb hd i μ))
      have hsum :
          (minkowskiSignature d e1 * (jostWitnessPoint σ a b ha hb hd i e1) ^ 2)
            ≤ ∑ x ∈ (Finset.univ : Finset (Fin (d + 1))),
                (minkowskiSignature d x * (jostWitnessPoint σ a b ha hb hd i x) ^ 2) := by
        exact Finset.single_le_sum (fun μ hμ => hnonneg μ) (by simp [e1])
      simpa using hsum
    exact lt_of_lt_of_le hterm_pos hterm_le
  · intro i j hij
    let e1 : Fin (d + 1) := ⟨1, by omega⟩
    have he1_sig : minkowskiSignature d e1 = 1 := by
      simp [minkowskiSignature, e1]
    have hdiff_e1 :
        (jostWitnessPoint σ a b ha hb hd i e1 -
            jostWitnessPoint σ a b ha hb hd j e1) =
          ((((i : ℕ) + 1 : ℝ) - (((j : ℕ) + 1 : ℝ))) * a) := by
      simp [jostWitnessPoint, e1]
      ring
    have hij_nat : i.val ≠ j.val := by
      intro h
      exact hij (Fin.ext h)
    have hcoeff_ne :
        (((i : ℕ) + 1 : ℝ) - (((j : ℕ) + 1 : ℝ))) ≠ 0 := by
      intro h
      have hsucceq : ((i : ℕ) + 1 : ℝ) = (((j : ℕ) + 1 : ℝ)) := by linarith
      have hsucceq_nat : i.val + 1 = j.val + 1 := by
        exact_mod_cast hsucceq
      exact hij_nat (Nat.succ.inj hsucceq_nat)
    have ha_ne : a ≠ 0 := ne_of_gt ha
    have hdiff_ne :
        (jostWitnessPoint σ a b ha hb hd i e1 -
            jostWitnessPoint σ a b ha hb hd j e1) ≠ 0 := by
      rw [hdiff_e1]
      exact mul_ne_zero hcoeff_ne ha_ne
    have hterm_pos :
        0 < minkowskiSignature d e1 *
            (jostWitnessPoint σ a b ha hb hd i e1 -
              jostWitnessPoint σ a b ha hb hd j e1) ^ 2 := by
      rw [he1_sig]
      have : 0 < (jostWitnessPoint σ a b ha hb hd i e1 -
          jostWitnessPoint σ a b ha hb hd j e1) ^ 2 := by
        exact sq_pos_of_ne_zero hdiff_ne
      simpa using this
    have hterm_le :
        minkowskiSignature d e1 *
            (jostWitnessPoint σ a b ha hb hd i e1 -
              jostWitnessPoint σ a b ha hb hd j e1) ^ 2 ≤
          ∑ μ : Fin (d + 1), minkowskiSignature d μ *
            (jostWitnessPoint σ a b ha hb hd i μ -
              jostWitnessPoint σ a b ha hb hd j μ) ^ 2 := by
      have hnonneg :
          ∀ μ : Fin (d + 1),
            0 ≤ minkowskiSignature d μ *
              (jostWitnessPoint σ a b ha hb hd i μ -
                jostWitnessPoint σ a b ha hb hd j μ) ^ 2 := by
        intro μ
        by_cases hμ0 : μ = 0
        · subst hμ0
          simp [jostWitnessPoint]
        · have hsig : minkowskiSignature d μ = 1 := by
            simp [minkowskiSignature, hμ0]
          rw [hsig]
          simpa [one_mul] using
            (sq_nonneg (jostWitnessPoint σ a b ha hb hd i μ -
              jostWitnessPoint σ a b ha hb hd j μ))
      have hsum :
          (minkowskiSignature d e1 *
              (jostWitnessPoint σ a b ha hb hd i e1 -
                jostWitnessPoint σ a b ha hb hd j e1) ^ 2)
            ≤ ∑ x ∈ (Finset.univ : Finset (Fin (d + 1))),
                (minkowskiSignature d x *
                  (jostWitnessPoint σ a b ha hb hd i x -
                    jostWitnessPoint σ a b ha hb hd j x) ^ 2) := by
        exact Finset.single_le_sum (fun μ hμ => hnonneg μ) (by simp [e1])
      simpa using hsum
    exact lt_of_lt_of_le hterm_pos hterm_le

/-! ## Part 5: Assembling the Jost witness package -/

/-- **The complete Jost witness package for d ≥ 2.**
    For any permutation σ of Fin n, there exists a Jost point x such that:
    - x ∈ JostSet d n
    - realEmbed x ∈ ExtendedTube d n
    - realEmbed (x ∘ σ) ∈ ExtendedTube d n
    This is obligation (1) for closing the sorry at PermutationFlow.lean:1490. -/
theorem jostWitness_exists (hd : 2 ≤ d) (σ : Equiv.Perm (Fin n)) :
    ∃ x : Fin n → Fin (d + 1) → ℝ,
      x ∈ JostSet d n ∧
      realEmbed x ∈ ExtendedTube d n ∧
      realEmbed (fun k => x (σ k)) ∈ ExtendedTube d n := by
  refine ⟨jostWitnessPoint σ 1 1 one_pos one_pos hd,
    jostWitness_mem_jostSet σ 1 1 one_pos one_pos hd,
    jostWitness_realEmbed_mem_ET σ 1 1 one_pos one_pos hd,
    jostWitness_sigma_realEmbed_mem_ET σ 1 1 one_pos one_pos hd⟩

/-! ## Part 6: How this connects to the sorry

The sorry at PermutationFlow.lean:1490 is inside `iterated_eow_permutation_extension`.
It needs to produce:
```
∀ z ∈ ET, (fun k => z (σ k)) ∈ ET → extendF F (fun k => z (σ k)) = extendF F z
```

The existing code reduces this to two obligations via `hExtPerm_of_geometric`:
  (1) A Jost witness: ∃ x ∈ JostSet, realEmbed(x) ∈ ET ∧ realEmbed(x∘σ) ∈ ET
  (2) Real double-coset generation on `permForwardOverlapIndexSet`

**This file provides obligation (1) for d ≥ 2.**

Alternatively, one can bypass `hExtPerm_of_geometric` and use
`extendF_perm_overlap_of_jostWitness_and_forwardOverlapConnected` directly,
which takes:
  (1) The Jost witness (provided here)
  (2) `IsConnected (permForwardOverlapSet n σ)`

For (2), the reduction chain is:
  indexSet connected → forward overlap set connected
  (via `isConnected_permForwardOverlapSet_of_indexConnected`)

The index set connectivity can be proved via:
- Real double-coset generation (existing lemma)
- Or direct argument using KAK decomposition of SO(1,d;ℂ)/SO⁺(1,d;ℝ) (rank 1)
- Or by showing the index set is path-connected through the orbits

For d = 1: The two-axis trick doesn't work (only 1 spatial dimension).
A separate argument is needed, potentially using `wickPlus1` from
AdjacentOverlapWitness.lean and properties specific to SO(1,1;ℂ) ≅ ℂ*.
-/

end JostWitnessGeneralSigma
