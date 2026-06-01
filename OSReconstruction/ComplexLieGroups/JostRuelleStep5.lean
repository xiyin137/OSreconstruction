/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.ComplexLieGroups.BHWCore

set_option linter.unusedSimpArgs false

/-!
# Jost-Ruelle Appendix II Step 5

This file formalizes the explicit two-plane complex Lorentz transformation
used in Jost's Appendix II proof of Ruelle's theorem.  In coordinates
`0, e₁`, the matrix is

`L(iφ) = [[cos φ, i sin φ], [i sin φ, cos φ]]`,

with identity on the orthogonal complement.  It sends the seed
`(i, -cot φ, 0, …, 0)` to the real boundary point
`(0, -(sin φ)⁻¹, 0, …, 0)`.
-/

noncomputable section

open Complex Topology MeasureTheory Filter Matrix LorentzLieGroup

namespace BHW

/-- The first spatial coordinate used by the Step-5 two-plane block. -/
def jostRuelleE1 (d : ℕ) (hd : 1 ≤ d) : Fin (d + 1) :=
  ⟨1, by omega⟩

private theorem jostRuelleE1_ne_zero (d : ℕ) (hd : 1 ≤ d) :
    jostRuelleE1 d hd ≠ (0 : Fin (d + 1)) := by
  intro h
  exact absurd (congrArg Fin.val h) (by simp [jostRuelleE1])

/-- The block-diagonal complex Lorentz matrix `L(iφ)` in the `(0,e₁)` plane. -/
def jostRuelleLiPhiMatrix (d : ℕ) (hd : 1 ≤ d) (φ : ℝ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  fun μ ν =>
    if μ = 0 ∧ ν = 0 then (Real.cos φ : ℂ)
    else if μ = 0 ∧ ν = jostRuelleE1 d hd then
      Complex.I * (Real.sin φ : ℂ)
    else if μ = jostRuelleE1 d hd ∧ ν = 0 then
      Complex.I * (Real.sin φ : ℂ)
    else if μ = jostRuelleE1 d hd ∧ ν = jostRuelleE1 d hd then
      (Real.cos φ : ℂ)
    else if μ = ν then 1 else 0

theorem jostRuelleLiPhiMatrix_row0
    (d : ℕ) (hd : 1 ≤ d) (φ : ℝ) (ν : Fin (d + 1)) :
    jostRuelleLiPhiMatrix d hd φ 0 ν =
      if ν = 0 then (Real.cos φ : ℂ)
      else if ν = jostRuelleE1 d hd then
        Complex.I * (Real.sin φ : ℂ)
      else 0 := by
  unfold jostRuelleLiPhiMatrix
  by_cases hν0 : ν = 0
  · subst hν0
    simp [jostRuelleE1]
  · by_cases hν1 : ν = jostRuelleE1 d hd
    · subst hν1
      have h10 := jostRuelleE1_ne_zero d hd
      simp [h10, jostRuelleE1]
    · simp [hν0, hν1, Ne.symm hν0, Ne.symm hν1]

theorem jostRuelleLiPhiMatrix_row1
    (d : ℕ) (hd : 1 ≤ d) (φ : ℝ) (ν : Fin (d + 1)) :
    jostRuelleLiPhiMatrix d hd φ (jostRuelleE1 d hd) ν =
      if ν = 0 then Complex.I * (Real.sin φ : ℂ)
      else if ν = jostRuelleE1 d hd then (Real.cos φ : ℂ)
      else 0 := by
  unfold jostRuelleLiPhiMatrix
  by_cases hν0 : ν = 0
  · subst hν0
    have h10 := jostRuelleE1_ne_zero d hd
    simp [h10, jostRuelleE1]
  · by_cases hν1 : ν = jostRuelleE1 d hd
    · subst hν1
      have h10 := jostRuelleE1_ne_zero d hd
      simp [h10, jostRuelleE1]
    · simp [hν0, hν1, Ne.symm hν0, Ne.symm hν1]

theorem jostRuelleLiPhiMatrix_row_other
    (d : ℕ) (hd : 1 ≤ d) (φ : ℝ) (μ : Fin (d + 1))
    (hμ0 : μ ≠ 0) (hμ1 : μ ≠ jostRuelleE1 d hd)
    (ν : Fin (d + 1)) :
    jostRuelleLiPhiMatrix d hd φ μ ν = if ν = μ then 1 else 0 := by
  unfold jostRuelleLiPhiMatrix
  rw [if_neg (by intro h; exact hμ0 h.1)]
  rw [if_neg (by intro h; exact hμ0 h.1)]
  rw [if_neg (by intro h; exact hμ1 h.1)]
  rw [if_neg (by intro h; exact hμ1 h.1)]
  by_cases hνμ : ν = μ
  · rw [if_pos hνμ.symm, if_pos hνμ]
  · rw [if_neg (Ne.symm hνμ), if_neg hνμ]

theorem jostRuelleLiPhiMatrix_col0
    (d : ℕ) (hd : 1 ≤ d) (φ : ℝ) (α : Fin (d + 1)) :
    jostRuelleLiPhiMatrix d hd φ α 0 =
      if α = 0 then (Real.cos φ : ℂ)
      else if α = jostRuelleE1 d hd then
        Complex.I * (Real.sin φ : ℂ)
      else 0 := by
  unfold jostRuelleLiPhiMatrix
  by_cases hα0 : α = 0
  · subst hα0
    simp
  · by_cases hα1 : α = jostRuelleE1 d hd
    · subst hα1
      have h10 := jostRuelleE1_ne_zero d hd
      simp [h10, jostRuelleE1]
    · simp [hα0, hα1, Ne.symm hα0]

theorem jostRuelleLiPhiMatrix_col1
    (d : ℕ) (hd : 1 ≤ d) (φ : ℝ) (α : Fin (d + 1)) :
    jostRuelleLiPhiMatrix d hd φ α (jostRuelleE1 d hd) =
      if α = 0 then Complex.I * (Real.sin φ : ℂ)
      else if α = jostRuelleE1 d hd then (Real.cos φ : ℂ)
      else 0 := by
  unfold jostRuelleLiPhiMatrix
  by_cases hα0 : α = 0
  · subst hα0
    have h10 := jostRuelleE1_ne_zero d hd
    simp [h10]
  · by_cases hα1 : α = jostRuelleE1 d hd
    · subst hα1
      have h10 := jostRuelleE1_ne_zero d hd
      simp [h10, jostRuelleE1]
    · simp [hα0, hα1, Ne.symm hα0]

theorem jostRuelleLiPhiMatrix_col_other
    (d : ℕ) (hd : 1 ≤ d) (φ : ℝ) (μ : Fin (d + 1))
    (hμ0 : μ ≠ 0) (hμ1 : μ ≠ jostRuelleE1 d hd)
    (α : Fin (d + 1)) :
    jostRuelleLiPhiMatrix d hd φ α μ = if α = μ then 1 else 0 := by
  unfold jostRuelleLiPhiMatrix
  rw [if_neg (by intro h; exact hμ0 h.2)]
  rw [if_neg (by intro h; exact hμ1 h.2)]
  rw [if_neg (by intro h; exact hμ0 h.2)]
  rw [if_neg (by intro h; exact hμ1 h.2)]

theorem jostRuelleLiPhiMatrix_action_coord0
    (d : ℕ) (hd : 1 ≤ d) (φ : ℝ) (v : Fin (d + 1) → ℂ) :
    (∑ ν : Fin (d + 1), jostRuelleLiPhiMatrix d hd φ 0 ν * v ν) =
      (Real.cos φ : ℂ) * v 0 +
        Complex.I * (Real.sin φ : ℂ) * v (jostRuelleE1 d hd) := by
  rw [show
      (∑ ν : Fin (d + 1), jostRuelleLiPhiMatrix d hd φ 0 ν * v ν) =
        ∑ ν : Fin (d + 1),
          (if ν = 0 then (Real.cos φ : ℂ)
            else if ν = jostRuelleE1 d hd then
              Complex.I * (Real.sin φ : ℂ)
            else 0) * v ν by
    apply Finset.sum_congr rfl
    intro ν _
    rw [jostRuelleLiPhiMatrix_row0]]
  have h10 := jostRuelleE1_ne_zero d hd
  have hsplit :
      (∑ x : Fin (d + 1),
          (if x = 0 then (Real.cos φ : ℂ)
            else if x = jostRuelleE1 d hd then
              Complex.I * (Real.sin φ : ℂ)
            else 0) * v x) =
        ∑ x : Fin (d + 1),
          ((if x = 0 then (Real.cos φ : ℂ) * v x else 0) +
            (if x = jostRuelleE1 d hd then
              Complex.I * (Real.sin φ : ℂ) * v x else 0)) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx0 : x = 0
    · simp [hx0, h10, Ne.symm h10]
    · by_cases hx1 : x = jostRuelleE1 d hd
      · simp [hx0, hx1, h10]
      · simp [hx0, hx1]
  rw [hsplit, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp [h10, Ne.symm h10]

theorem jostRuelleLiPhiMatrix_action_coord1
    (d : ℕ) (hd : 1 ≤ d) (φ : ℝ) (v : Fin (d + 1) → ℂ) :
    (∑ ν : Fin (d + 1),
        jostRuelleLiPhiMatrix d hd φ (jostRuelleE1 d hd) ν * v ν) =
      Complex.I * (Real.sin φ : ℂ) * v 0 +
        (Real.cos φ : ℂ) * v (jostRuelleE1 d hd) := by
  rw [show
      (∑ ν : Fin (d + 1),
          jostRuelleLiPhiMatrix d hd φ (jostRuelleE1 d hd) ν * v ν) =
        ∑ ν : Fin (d + 1),
          (if ν = 0 then Complex.I * (Real.sin φ : ℂ)
            else if ν = jostRuelleE1 d hd then (Real.cos φ : ℂ)
            else 0) * v ν by
    apply Finset.sum_congr rfl
    intro ν _
    rw [jostRuelleLiPhiMatrix_row1]]
  have h10 := jostRuelleE1_ne_zero d hd
  have hsplit :
      (∑ x : Fin (d + 1),
          (if x = 0 then Complex.I * (Real.sin φ : ℂ)
            else if x = jostRuelleE1 d hd then (Real.cos φ : ℂ)
            else 0) * v x) =
        ∑ x : Fin (d + 1),
          ((if x = 0 then Complex.I * (Real.sin φ : ℂ) * v x else 0) +
            (if x = jostRuelleE1 d hd then
              (Real.cos φ : ℂ) * v x else 0)) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx0 : x = 0
    · simp [hx0, h10, Ne.symm h10]
    · by_cases hx1 : x = jostRuelleE1 d hd
      · simp [hx0, hx1, h10]
      · simp [hx0, hx1]
  rw [hsplit, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp [h10, Ne.symm h10]

theorem jostRuelleLiPhiMatrix_action_coord_other
    (d : ℕ) (hd : 1 ≤ d) (φ : ℝ) (v : Fin (d + 1) → ℂ)
    (μ : Fin (d + 1)) (hμ0 : μ ≠ 0)
    (hμ1 : μ ≠ jostRuelleE1 d hd) :
    (∑ ν : Fin (d + 1), jostRuelleLiPhiMatrix d hd φ μ ν * v ν) =
      v μ := by
  rw [show
      (∑ ν : Fin (d + 1), jostRuelleLiPhiMatrix d hd φ μ ν * v ν) =
        ∑ ν : Fin (d + 1), (if ν = μ then 1 else 0) * v ν by
    apply Finset.sum_congr rfl
    intro ν _
    rw [jostRuelleLiPhiMatrix_row_other d hd φ μ hμ0 hμ1]]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp

private theorem jostRuelle_sum_two_support
    (d : ℕ) (hd : 1 ≤ d) (a b : ℂ) :
    (∑ x : Fin (d + 1),
      (if x = 0 then a
       else if x = jostRuelleE1 d hd then b
       else 0)) = a + b := by
  have h10 := jostRuelleE1_ne_zero d hd
  have hsplit :
      (∑ x : Fin (d + 1),
        (if x = 0 then a
         else if x = jostRuelleE1 d hd then b
         else 0)) =
        ∑ x : Fin (d + 1),
          ((if x = 0 then a else 0) +
            (if x = jostRuelleE1 d hd then b else 0)) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx0 : x = 0
    · simp [hx0, Ne.symm h10]
    · by_cases hx1 : x = jostRuelleE1 d hd
      · subst hx1
        simp [h10]
      · simp [hx0, hx1]
  rw [hsplit, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp [h10, Ne.symm h10]

private theorem jostRuelle_prod_two_support
    (d : ℕ) (hd : 1 ≤ d) (a b : ℂ) :
    (∏ x : Fin (d + 1),
      (if x = 0 then a
       else if x = jostRuelleE1 d hd then b
       else 1)) = a * b := by
  have h10 := jostRuelleE1_ne_zero d hd
  have hsplit :
      (∏ x : Fin (d + 1),
        (if x = 0 then a
         else if x = jostRuelleE1 d hd then b
         else 1)) =
        ∏ x : Fin (d + 1),
          ((if x = 0 then a else 1) *
            (if x = jostRuelleE1 d hd then b else 1)) := by
    apply Finset.prod_congr rfl
    intro x _
    by_cases hx0 : x = 0
    · simp [hx0, Ne.symm h10]
    · by_cases hx1 : x = jostRuelleE1 d hd
      · subst hx1
        simp [h10]
      · simp [hx0, hx1]
  rw [hsplit, Finset.prod_mul_distrib]
  rw [Finset.prod_ite_eq', Finset.prod_ite_eq']
  simp [h10, Ne.symm h10]

private theorem jostRuelleLiPhiMatrix_det_perm_is_id_or_swap
    (d : ℕ) (hd : 1 ≤ d) (φ : ℝ)
    (σ : Equiv.Perm (Fin (d + 1)))
    (hall : ∀ i : Fin (d + 1),
      jostRuelleLiPhiMatrix d hd φ (σ i) i ≠ 0) :
    σ = 1 ∨
      σ = Equiv.swap (0 : Fin (d + 1)) (jostRuelleE1 d hd) := by
  have h10 := jostRuelleE1_ne_zero d hd
  have hσ0_cases :
      σ (0 : Fin (d + 1)) = 0 ∨
        σ (0 : Fin (d + 1)) = jostRuelleE1 d hd := by
    have h := hall 0
    rw [jostRuelleLiPhiMatrix_col0] at h
    by_cases h0 : σ (0 : Fin (d + 1)) = 0
    · exact Or.inl h0
    · by_cases h1 : σ (0 : Fin (d + 1)) = jostRuelleE1 d hd
      · exact Or.inr h1
      · simp [h0, h1] at h
  rcases hσ0_cases with hσ0 | hσ0
  · left
    ext j
    by_cases hj0 : j = 0
    · subst hj0
      simpa using hσ0
    · by_cases hj1 : j = jostRuelleE1 d hd
      · subst hj1
        have hne0 : σ (jostRuelleE1 d hd) ≠ 0 := by
          intro hse0
          have hEq :
              σ (jostRuelleE1 d hd) =
                σ (0 : Fin (d + 1)) := by
            rw [hse0, hσ0]
          exact h10 (σ.injective hEq)
        have h := hall (jostRuelleE1 d hd)
        rw [jostRuelleLiPhiMatrix_col1] at h
        by_cases h0 : σ (jostRuelleE1 d hd) = 0
        · exact absurd h0 hne0
        · by_cases h1 :
            σ (jostRuelleE1 d hd) = jostRuelleE1 d hd
          · exact congrArg Fin.val h1
          · simp [h0, h1] at h
      · have h := hall j
        rw [jostRuelleLiPhiMatrix_col_other d hd φ j hj0 hj1] at h
        by_cases hsj : σ j = j
        · exact congrArg Fin.val hsj
        · simp [hsj] at h
  · right
    ext j
    by_cases hj0 : j = 0
    · subst hj0
      rw [Equiv.swap_apply_left]
      exact congrArg Fin.val hσ0
    · by_cases hj1 : j = jostRuelleE1 d hd
      · subst hj1
        have hne1 :
            σ (jostRuelleE1 d hd) ≠ jostRuelleE1 d hd := by
          intro hse1
          have hEq :
              σ (jostRuelleE1 d hd) =
                σ (0 : Fin (d + 1)) := by
            rw [hse1, hσ0]
          exact h10 (σ.injective hEq)
        have h := hall (jostRuelleE1 d hd)
        rw [jostRuelleLiPhiMatrix_col1] at h
        by_cases h0 : σ (jostRuelleE1 d hd) = 0
        · rw [Equiv.swap_apply_right]
          exact congrArg Fin.val h0
        · by_cases h1 :
            σ (jostRuelleE1 d hd) = jostRuelleE1 d hd
          · exact absurd h1 hne1
          · simp [h0, h1] at h
      · have h := hall j
        rw [jostRuelleLiPhiMatrix_col_other d hd φ j hj0 hj1] at h
        have hfix : σ j = j := by
          by_cases hsj : σ j = j
          · exact hsj
          · simp [hsj] at h
        rw [Equiv.swap_apply_of_ne_of_ne hj0 hj1, hfix]

private theorem jostRuelleLiPhiMatrix_det_term_one
    (d : ℕ) (hd : 1 ≤ d) (φ : ℝ) :
    (∏ i : Fin (d + 1),
      jostRuelleLiPhiMatrix d hd φ i i) =
      (Real.cos φ : ℂ) * (Real.cos φ : ℂ) := by
  have h10 := jostRuelleE1_ne_zero d hd
  calc
    (∏ i : Fin (d + 1),
      jostRuelleLiPhiMatrix d hd φ i i)
        = ∏ i : Fin (d + 1),
          (if i = 0 then (Real.cos φ : ℂ)
           else if i = jostRuelleE1 d hd then (Real.cos φ : ℂ)
           else 1) := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi0 : i = 0
      · subst hi0
        simp [jostRuelleLiPhiMatrix_row0, h10]
      · by_cases hi1 : i = jostRuelleE1 d hd
        · subst hi1
          simp [jostRuelleLiPhiMatrix_row1, h10]
        · rw [jostRuelleLiPhiMatrix_row_other d hd φ i hi0 hi1]
          simp [hi0, hi1]
    _ = (Real.cos φ : ℂ) * (Real.cos φ : ℂ) := by
      rw [jostRuelle_prod_two_support]

private theorem jostRuelleLiPhiMatrix_det_term_swap
    (d : ℕ) (hd : 1 ≤ d) (φ : ℝ) :
    (∏ i : Fin (d + 1),
      jostRuelleLiPhiMatrix d hd φ
        (Equiv.swap (0 : Fin (d + 1)) (jostRuelleE1 d hd) i) i) =
      (Complex.I * (Real.sin φ : ℂ)) *
        (Complex.I * (Real.sin φ : ℂ)) := by
  have h10 := jostRuelleE1_ne_zero d hd
  calc
    (∏ i : Fin (d + 1),
      jostRuelleLiPhiMatrix d hd φ
        (Equiv.swap (0 : Fin (d + 1)) (jostRuelleE1 d hd) i) i)
        = ∏ i : Fin (d + 1),
          (if i = 0 then Complex.I * (Real.sin φ : ℂ)
           else if i = jostRuelleE1 d hd then
             Complex.I * (Real.sin φ : ℂ)
           else 1) := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi0 : i = 0
      · subst hi0
        rw [Equiv.swap_apply_left]
        simp [jostRuelleLiPhiMatrix_row1, h10]
      · by_cases hi1 : i = jostRuelleE1 d hd
        · subst hi1
          rw [Equiv.swap_apply_right]
          simp [jostRuelleLiPhiMatrix_row0, h10]
        · rw [Equiv.swap_apply_of_ne_of_ne hi0 hi1]
          rw [jostRuelleLiPhiMatrix_row_other d hd φ i hi0 hi1]
          simp [hi0, hi1]
    _ = (Complex.I * (Real.sin φ : ℂ)) *
          (Complex.I * (Real.sin φ : ℂ)) := by
      rw [jostRuelle_prod_two_support]

private theorem jostRuelleLiPhiMatrix_det
    (d : ℕ) (hd : 1 ≤ d) (φ : ℝ) :
    (jostRuelleLiPhiMatrix d hd φ).det = (1 : ℂ) := by
  rw [Matrix.det_apply]
  have h10 := jostRuelleE1_ne_zero d hd
  let τ : Equiv.Perm (Fin (d + 1)) :=
    Equiv.swap (0 : Fin (d + 1)) (jostRuelleE1 d hd)
  let good : Finset (Equiv.Perm (Fin (d + 1))) := {1, τ}
  let term : Equiv.Perm (Fin (d + 1)) → ℂ :=
    fun σ =>
      Equiv.Perm.sign σ •
        ∏ i : Fin (d + 1),
          jostRuelleLiPhiMatrix d hd φ (σ i) i
  change (∑ σ : Equiv.Perm (Fin (d + 1)), term σ) = (1 : ℂ)
  have hzero :
      ∀ σ ∈ Finset.univ, σ ∉ good → term σ = 0 := by
    intro σ _ hσgood
    suffices hprod :
        (∏ i : Fin (d + 1),
          jostRuelleLiPhiMatrix d hd φ (σ i) i) = 0 by
      simp [term, hprod]
    by_contra hprod_ne
    have hall :
        ∀ i : Fin (d + 1),
          jostRuelleLiPhiMatrix d hd φ (σ i) i ≠ 0 := by
      intro i hi
      exact hprod_ne
        (Finset.prod_eq_zero (Finset.mem_univ i) hi)
    have hclass :=
      jostRuelleLiPhiMatrix_det_perm_is_id_or_swap
        d hd φ σ hall
    have hmem : σ ∈ good := by
      rcases hclass with hσ | hσ
      · simp [good, hσ]
      · simp [good, τ, hσ]
    exact hσgood hmem
  rw [← Finset.sum_subset (Finset.subset_univ good) hzero]
  have hτ_ne_one : τ ≠ 1 := by
    intro hτ
    have h0 :=
      congrArg (fun σ : Equiv.Perm (Fin (d + 1)) =>
        σ (0 : Fin (d + 1))) hτ
    have heq : jostRuelleE1 d hd = (0 : Fin (d + 1)) := by
      simpa [τ, Equiv.swap_apply_left] using h0
    exact h10 heq
  have htrig : ((Real.sin φ : ℂ) ^ 2 + (Real.cos φ : ℂ) ^ 2) = 1 := by
    norm_cast
    exact Real.sin_sq_add_cos_sq φ
  rw [Finset.sum_insert (by simpa [τ] using Ne.symm hτ_ne_one)]
  rw [Finset.sum_singleton]
  have hterm_one :
      term 1 = (Real.cos φ : ℂ) * (Real.cos φ : ℂ) := by
    simp [term, jostRuelleLiPhiMatrix_det_term_one]
  have hterm_swap :
      term τ =
        -((Complex.I * (Real.sin φ : ℂ)) *
          (Complex.I * (Real.sin φ : ℂ))) := by
    dsimp [term, τ]
    rw [Equiv.Perm.sign_swap (Ne.symm h10)]
    rw [jostRuelleLiPhiMatrix_det_term_swap]
    simp
  rw [hterm_one, hterm_swap]
  ring_nf
  rw [Complex.I_sq]
  ring_nf
  linear_combination htrig

private theorem jostRuelleLiPhiMatrix_metric
    (d : ℕ) (hd : 1 ≤ d) (φ : ℝ) :
    ∀ (μ ν : Fin (d + 1)),
      ∑ α : Fin (d + 1),
        (minkowskiSignature d α : ℂ) *
          jostRuelleLiPhiMatrix d hd φ α μ *
          jostRuelleLiPhiMatrix d hd φ α ν =
      if μ = ν then (minkowskiSignature d μ : ℂ) else 0 := by
  intro μ ν
  have h10 := jostRuelleE1_ne_zero d hd
  have htrig : ((Real.sin φ : ℂ) ^ 2 + (Real.cos φ : ℂ) ^ 2) = 1 := by
    norm_cast
    exact Real.sin_sq_add_cos_sq φ
  by_cases hμ0 : μ = 0
  · subst hμ0
    by_cases hν0 : ν = 0
    · subst hν0
      rw [if_pos rfl]
      calc
        (∑ α : Fin (d + 1),
          (minkowskiSignature d α : ℂ) *
            jostRuelleLiPhiMatrix d hd φ α 0 *
            jostRuelleLiPhiMatrix d hd φ α 0)
            = ∑ α : Fin (d + 1),
              (if α = 0 then -((Real.cos φ : ℂ) ^ 2)
               else if α = jostRuelleE1 d hd then
                 -((Real.sin φ : ℂ) ^ 2)
               else 0) := by
          apply Finset.sum_congr rfl
          intro α _
          by_cases hα0 : α = 0
          · subst hα0
            simp [jostRuelleLiPhiMatrix_col0, minkowskiSignature]
            ring
          · by_cases hα1 : α = jostRuelleE1 d hd
            · subst hα1
              simp [jostRuelleLiPhiMatrix_col0, minkowskiSignature, h10,
                Complex.I_sq]
              ring_nf
              rw [Complex.I_sq]
              ring_nf
            · simp [jostRuelleLiPhiMatrix_col0, hα0, hα1]
        _ = (-1 : ℂ) := by
          rw [jostRuelle_sum_two_support]
          linear_combination -htrig
        _ = (minkowskiSignature d 0 : ℂ) := by
          simp [minkowskiSignature]
    · by_cases hν1 : ν = jostRuelleE1 d hd
      · subst hν1
        rw [if_neg (Ne.symm h10)]
        calc
          (∑ α : Fin (d + 1),
            (minkowskiSignature d α : ℂ) *
              jostRuelleLiPhiMatrix d hd φ α 0 *
              jostRuelleLiPhiMatrix d hd φ α (jostRuelleE1 d hd))
              = ∑ α : Fin (d + 1),
                (if α = 0 then
                  -((Real.cos φ : ℂ) *
                    (Complex.I * (Real.sin φ : ℂ)))
                 else if α = jostRuelleE1 d hd then
                  (Complex.I * (Real.sin φ : ℂ)) * (Real.cos φ : ℂ)
                 else 0) := by
            apply Finset.sum_congr rfl
            intro α _
            by_cases hα0 : α = 0
            · subst hα0
              simp [jostRuelleLiPhiMatrix_col0,
                jostRuelleLiPhiMatrix_col1, minkowskiSignature]
            · by_cases hα1 : α = jostRuelleE1 d hd
              · subst hα1
                simp [jostRuelleLiPhiMatrix_col0,
                  jostRuelleLiPhiMatrix_col1, minkowskiSignature, h10]
              · simp [jostRuelleLiPhiMatrix_col0,
                  jostRuelleLiPhiMatrix_col1, hα0, hα1]
          _ = 0 := by
            rw [jostRuelle_sum_two_support]
            ring
      · rw [if_neg (Ne.symm hν0)]
        apply Finset.sum_eq_zero
        intro α _
        by_cases hαν : α = ν
        · simp [jostRuelleLiPhiMatrix_col0,
            jostRuelleLiPhiMatrix_col_other d hd φ ν hν0 hν1,
            hαν, hν0, hν1]
        · simp [jostRuelleLiPhiMatrix_col_other d hd φ ν hν0 hν1,
            hαν]
  · by_cases hμ1 : μ = jostRuelleE1 d hd
    · subst hμ1
      by_cases hν0 : ν = 0
      · subst hν0
        rw [if_neg h10]
        calc
          (∑ α : Fin (d + 1),
            (minkowskiSignature d α : ℂ) *
              jostRuelleLiPhiMatrix d hd φ α (jostRuelleE1 d hd) *
              jostRuelleLiPhiMatrix d hd φ α 0)
              = ∑ α : Fin (d + 1),
                (if α = 0 then
                  -((Complex.I * (Real.sin φ : ℂ)) *
                    (Real.cos φ : ℂ))
                 else if α = jostRuelleE1 d hd then
                  (Real.cos φ : ℂ) * (Complex.I * (Real.sin φ : ℂ))
                 else 0) := by
            apply Finset.sum_congr rfl
            intro α _
            by_cases hα0 : α = 0
            · subst hα0
              simp [jostRuelleLiPhiMatrix_col0,
                jostRuelleLiPhiMatrix_col1, minkowskiSignature]
            · by_cases hα1 : α = jostRuelleE1 d hd
              · subst hα1
                simp [jostRuelleLiPhiMatrix_col0,
                  jostRuelleLiPhiMatrix_col1, minkowskiSignature, h10]
              · simp [jostRuelleLiPhiMatrix_col0,
                  jostRuelleLiPhiMatrix_col1, hα0, hα1]
          _ = 0 := by
            rw [jostRuelle_sum_two_support]
            ring
      · by_cases hν1 : ν = jostRuelleE1 d hd
        · subst hν1
          rw [if_pos rfl]
          change
            (∑ α : Fin (d + 1),
              (minkowskiSignature d α : ℂ) *
                jostRuelleLiPhiMatrix d hd φ α (jostRuelleE1 d hd) *
                jostRuelleLiPhiMatrix d hd φ α (jostRuelleE1 d hd)) =
              (1 : ℂ)
          calc
            (∑ α : Fin (d + 1),
              (minkowskiSignature d α : ℂ) *
                jostRuelleLiPhiMatrix d hd φ α (jostRuelleE1 d hd) *
                jostRuelleLiPhiMatrix d hd φ α (jostRuelleE1 d hd))
                = ∑ α : Fin (d + 1),
                  (if α = 0 then (Real.sin φ : ℂ) ^ 2
                   else if α = jostRuelleE1 d hd then
                     (Real.cos φ : ℂ) ^ 2
                   else 0) := by
              apply Finset.sum_congr rfl
              intro α _
              by_cases hα0 : α = 0
              · subst hα0
                simp [jostRuelleLiPhiMatrix_col1, minkowskiSignature,
                  Complex.I_sq]
                ring_nf
                rw [Complex.I_sq]
                ring_nf
              · by_cases hα1 : α = jostRuelleE1 d hd
                · subst hα1
                  simp [jostRuelleLiPhiMatrix_col1, minkowskiSignature, h10]
                  ring
                · simp [jostRuelleLiPhiMatrix_col1, hα0, hα1]
            _ = (1 : ℂ) := by
              rw [jostRuelle_sum_two_support]
              exact htrig
        · rw [if_neg (Ne.symm hν1)]
          apply Finset.sum_eq_zero
          intro α _
          by_cases hαν : α = ν
          · simp [jostRuelleLiPhiMatrix_col1,
              jostRuelleLiPhiMatrix_col_other d hd φ ν hν0 hν1,
              hαν, hν0, hν1]
          · simp [jostRuelleLiPhiMatrix_col_other d hd φ ν hν0 hν1,
              hαν]
    · by_cases hν0 : ν = 0
      · subst hν0
        rw [if_neg hμ0]
        apply Finset.sum_eq_zero
        intro α _
        by_cases hαμ : α = μ
        · simp [jostRuelleLiPhiMatrix_col0,
            jostRuelleLiPhiMatrix_col_other d hd φ μ hμ0 hμ1,
            hαμ, hμ0, hμ1]
        · simp [jostRuelleLiPhiMatrix_col_other d hd φ μ hμ0 hμ1,
            hαμ]
      · by_cases hν1 : ν = jostRuelleE1 d hd
        · subst hν1
          rw [if_neg hμ1]
          apply Finset.sum_eq_zero
          intro α _
          by_cases hαμ : α = μ
          · simp [jostRuelleLiPhiMatrix_col1,
              jostRuelleLiPhiMatrix_col_other d hd φ μ hμ0 hμ1,
              hαμ, hμ0, hμ1]
          · simp [jostRuelleLiPhiMatrix_col_other d hd φ μ hμ0 hμ1,
              hαμ]
        · by_cases hμν : μ = ν
          · subst hμν
            rw [if_pos rfl]
            simp only [jostRuelleLiPhiMatrix_col_other d hd φ μ hμ0 hμ1,
              mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
              Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
          · rw [if_neg hμν]
            simp only [jostRuelleLiPhiMatrix_col_other d hd φ μ hμ0 hμ1,
              jostRuelleLiPhiMatrix_col_other d hd φ ν hν0 hν1,
              mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
            apply Finset.sum_eq_zero
            intro α _
            by_cases hαμ : α = μ
            · subst hαμ
              simp [hμν]
            · simp [hαμ]

/-- Jost's `L(iφ)` as an actual element of the complex Lorentz group. -/
def jostRuelleLiPhiCLG (d : ℕ) (hd : 1 ≤ d) (φ : ℝ) :
    ComplexLorentzGroup d where
  val := jostRuelleLiPhiMatrix d hd φ
  metric_preserving := jostRuelleLiPhiMatrix_metric d hd φ
  proper := jostRuelleLiPhiMatrix_det d hd φ

/-- The Appendix-II Step-5 seed `(i, -cot φ, 0, …, 0)`. -/
def jostRuelleStep5Seed
    (d : ℕ) (hd : 1 ≤ d) (φ : ℝ) : Fin (d + 1) → ℂ :=
  fun μ =>
    if μ = 0 then
      Complex.I
    else if μ = jostRuelleE1 d hd then
      -((Real.cos φ / Real.sin φ : ℝ) : ℂ)
    else
      0

/-- The Step-5 seed is an honest one-point forward-tube configuration: its
imaginary part is the unit future-time vector. -/
theorem jostRuelleStep5Seed_mem_forwardTube
    (d : ℕ) (hd : 1 ≤ d) (φ : ℝ) :
    (fun _ : Fin 1 => jostRuelleStep5Seed d hd φ) ∈
      BHWCore.ForwardTube d 1 := by
  have h10 := jostRuelleE1_ne_zero d hd
  intro k
  fin_cases k
  change
    InOpenForwardCone d
      (fun μ : Fin (d + 1) => (jostRuelleStep5Seed d hd φ μ - 0).im)
  constructor
  · simp [jostRuelleStep5Seed]
  · have hquad :
        (∑ μ : Fin (d + 1),
          minkowskiSignature d μ *
            (jostRuelleStep5Seed d hd φ μ - 0).im ^ 2) = -1 := by
      rw [Finset.sum_eq_single (0 : Fin (d + 1))]
      · simp [jostRuelleStep5Seed, minkowskiSignature]
      · intro μ _ hμ0
        by_cases hμ1 : μ = jostRuelleE1 d hd
        · subst hμ1
          have him :
              (jostRuelleStep5Seed d hd φ (jostRuelleE1 d hd) - 0).im = 0 := by
            have hquot :
                (Complex.cos (φ : ℂ) / Complex.sin (φ : ℂ)).im = 0 := by
              simp [Complex.div_im, Complex.cos_ofReal_im, Complex.sin_ofReal_im]
            simpa [jostRuelleStep5Seed, h10] using hquot
          rw [him]
          ring
        · simp [jostRuelleStep5Seed, hμ0, hμ1]
      · intro h0
        exact (h0 (Finset.mem_univ 0)).elim
    rw [hquad]
    norm_num

/-- Real-coordinate version of the Step-5 boundary vector. -/
def jostRuelleStep5RealBoundaryReal
    (d : ℕ) (hd : 1 ≤ d) (φ : ℝ) : Fin (d + 1) → ℝ :=
  fun μ =>
    if μ = 0 then
      0
    else if μ = jostRuelleE1 d hd then
      -((Real.sin φ)⁻¹)
    else
      0

/-- The real boundary point `(0, -(sin φ)⁻¹, 0, …, 0)`. -/
def jostRuelleStep5RealBoundary
    (d : ℕ) (hd : 1 ≤ d) (φ : ℝ) : Fin (d + 1) → ℂ :=
  fun μ =>
    if μ = 0 then
      0
    else if μ = jostRuelleE1 d hd then
      -(((Real.sin φ)⁻¹ : ℝ) : ℂ)
    else
      0

/-- The complex Step-5 boundary vector is the coordinatewise complexification
of its real form. -/
theorem jostRuelleStep5RealBoundary_eq_ofReal
    (d : ℕ) (hd : 1 ≤ d) (φ : ℝ) :
    (fun _ : Fin 1 => jostRuelleStep5RealBoundary d hd φ) =
      (fun _ : Fin 1 => fun μ : Fin (d + 1) =>
        (jostRuelleStep5RealBoundaryReal d hd φ μ : ℂ)) := by
  have h10 := jostRuelleE1_ne_zero d hd
  ext k μ
  by_cases hμ0 : μ = 0
  · simp [jostRuelleStep5RealBoundary, jostRuelleStep5RealBoundaryReal, hμ0]
  · by_cases hμ1 : μ = jostRuelleE1 d hd
    · simp [jostRuelleStep5RealBoundary, jostRuelleStep5RealBoundaryReal,
        hμ0, hμ1, h10, Complex.ofReal_neg]
    · simp [jostRuelleStep5RealBoundary, jostRuelleStep5RealBoundaryReal,
        hμ0, hμ1]

/-- The Step-5 boundary vector is spacelike whenever `sin φ ≠ 0`. -/
theorem jostRuelleStep5RealBoundary_spacelike
    (d : ℕ) (hd : 1 ≤ d) (φ : ℝ) (hsin : Real.sin φ ≠ 0) :
    0 <
      ∑ μ : Fin (d + 1),
        minkowskiSignature d μ *
          (jostRuelleStep5RealBoundaryReal d hd φ μ) ^ 2 := by
  have h10 := jostRuelleE1_ne_zero d hd
  have hquad :
      (∑ μ : Fin (d + 1),
        minkowskiSignature d μ *
          (jostRuelleStep5RealBoundaryReal d hd φ μ) ^ 2) =
        ((Real.sin φ)⁻¹) ^ 2 := by
    rw [Finset.sum_eq_single (jostRuelleE1 d hd)]
    · simp [jostRuelleStep5RealBoundaryReal, h10, minkowskiSignature]
    · intro μ _ hμ1
      by_cases hμ0 : μ = 0
      · subst hμ0
        simp [jostRuelleStep5RealBoundaryReal, h10]
      · simp [jostRuelleStep5RealBoundaryReal, hμ0, hμ1]
    · intro hmem
      exact (hmem (Finset.mem_univ _)).elim
  rw [hquad]
  exact sq_pos_of_ne_zero (inv_ne_zero hsin)

theorem jostRuelleLiPhiMatrix_seed_action_eq_realBoundary
    (d : ℕ) (hd : 1 ≤ d) (φ : ℝ) (hsin : Real.sin φ ≠ 0) :
    (fun μ : Fin (d + 1) =>
      ∑ ν : Fin (d + 1),
        jostRuelleLiPhiMatrix d hd φ μ ν *
          jostRuelleStep5Seed d hd φ ν) =
      jostRuelleStep5RealBoundary d hd φ := by
  ext μ
  have h10 := jostRuelleE1_ne_zero d hd
  have hsinC : Complex.sin (φ : ℂ) ≠ 0 := by
    have hsinC' : (Real.sin φ : ℂ) ≠ 0 := by exact_mod_cast hsin
    simpa [Complex.ofReal_sin] using hsinC'
  by_cases hμ0 : μ = 0
  · subst hμ0
    rw [jostRuelleLiPhiMatrix_action_coord0]
    simp [jostRuelleStep5Seed, jostRuelleStep5RealBoundary, h10]
    field_simp [hsinC]
    ring_nf
  · by_cases hμ1 : μ = jostRuelleE1 d hd
    · subst hμ1
      rw [jostRuelleLiPhiMatrix_action_coord1]
      simp [jostRuelleStep5Seed, jostRuelleStep5RealBoundary, h10]
      field_simp [hsinC]
      rw [Complex.I_sq]
      ring_nf
      have htrig :
          Complex.sin (φ : ℂ) ^ 2 + Complex.cos (φ : ℂ) ^ 2 = 1 := by
        have hreal :
            ((Real.sin φ : ℂ) ^ 2 + (Real.cos φ : ℂ) ^ 2) = 1 := by
          norm_cast
          exact Real.sin_sq_add_cos_sq φ
        rw [← Complex.ofReal_sin, ← Complex.ofReal_cos]
        exact hreal
      linear_combination -htrig
    · rw [jostRuelleLiPhiMatrix_action_coord_other d hd φ
        (jostRuelleStep5Seed d hd φ) μ hμ0 hμ1]
      simp [jostRuelleStep5Seed, jostRuelleStep5RealBoundary, hμ0, hμ1]

/-- Applying Jost's `L(iφ)` group element to the Step-5 seed gives the real
boundary point from Appendix II. -/
theorem jostRuelleLiPhiCLG_action_seed_eq_realBoundary
    (d : ℕ) (hd : 1 ≤ d) (φ : ℝ) (hsin : Real.sin φ ≠ 0) :
    (fun μ : Fin (d + 1) =>
      BHWCore.complexLorentzAction (d := d) (n := 1)
        (jostRuelleLiPhiCLG d hd φ)
        (fun _ : Fin 1 => jostRuelleStep5Seed d hd φ) 0 μ) =
      jostRuelleStep5RealBoundary d hd φ := by
  simpa [BHWCore.complexLorentzAction, jostRuelleLiPhiCLG] using
    jostRuelleLiPhiMatrix_seed_action_eq_realBoundary d hd φ hsin

/-- The Step-5 real boundary point belongs to the extended tube: it is the
`L(iφ)` image of the explicit forward-tube seed. -/
theorem jostRuelleStep5RealBoundary_mem_extendedTube
    (d : ℕ) (hd : 1 ≤ d) (φ : ℝ) (hsin : Real.sin φ ≠ 0) :
    (fun _ : Fin 1 => jostRuelleStep5RealBoundary d hd φ) ∈
      BHWCore.ExtendedTube d 1 := by
  refine Set.mem_iUnion.mpr
    ⟨jostRuelleLiPhiCLG d hd φ,
      (fun _ : Fin 1 => jostRuelleStep5Seed d hd φ),
      jostRuelleStep5Seed_mem_forwardTube d hd φ, ?_⟩
  ext k μ
  fin_cases k
  simpa using
    (congrFun
      (jostRuelleLiPhiCLG_action_seed_eq_realBoundary d hd φ hsin) μ).symm

end BHW
