import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexTakagiPhase

/-!
# Entry bounds for Autonne-Takagi singular values

This file proves the finite entry-`ℓ¹` estimate used by the
entry-controlled Autonne-Takagi factorization.  Given a Takagi diagonalization
`S = U * diagonal σ * Uᵀ`, each singular value is recovered by conjugating
with the unitary columns and is therefore bounded by
`BHW.matrixEntryL1Bound m S`.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial Module
open scoped Matrix.Norms.Operator ComplexOrder ComplexConjugate

namespace BHW

theorem matrix_unitary_col_star_mul_eq_ite
    (m : ℕ) (U : Matrix.unitaryGroup (Fin m) ℂ) (a b : Fin m) :
    ∑ i : Fin m, star ((U : Matrix (Fin m) (Fin m) ℂ) i a) *
      (U : Matrix (Fin m) (Fin m) ℂ) i b = if a = b then 1 else 0 := by
  have h := congrFun (congrFun U.2.1 a) b
  simpa [Matrix.mul_apply] using h

theorem matrix_unitary_col_mul_star_eq_ite
    (m : ℕ) (U : Matrix.unitaryGroup (Fin m) ℂ) (a b : Fin m) :
    ∑ i : Fin m, (U : Matrix (Fin m) (Fin m) ℂ) i a *
      star ((U : Matrix (Fin m) (Fin m) ℂ) i b) = if a = b then 1 else 0 := by
  have h := congrArg star (congrFun (congrFun U.2.1 a) b)
  simp only [Matrix.mul_apply, Matrix.one_apply, star_sum, StarMul.star_mul] at h
  simpa [mul_comm] using h

/-- The transpose of a unitary complex matrix is unitary on the side needed by
the Takagi diagonal extraction. -/
theorem matrix_unitary_transpose_mul_star_transpose
    (m : ℕ) (U : Matrix.unitaryGroup (Fin m) ℂ) :
    ((U : Matrix (Fin m) (Fin m) ℂ).transpose) *
      star ((U : Matrix (Fin m) (Fin m) ℂ).transpose) = 1 := by
  ext i j
  simpa [Matrix.mul_apply] using matrix_unitary_col_mul_star_eq_ite m U i j

/-- Extract a Takagi singular value by multiplying the diagonalization by the
unitary inverses on the left and right. -/
theorem takagi_diagonal_extraction
    (m : ℕ)
    {S : Matrix (Fin m) (Fin m) ℂ}
    {U : Matrix.unitaryGroup (Fin m) ℂ}
    {σ : Fin m → ℝ}
    (hTakagi :
      S =
        (U : Matrix (Fin m) (Fin m) ℂ) *
          Matrix.diagonal (fun a => (σ a : ℂ)) *
          (U : Matrix (Fin m) (Fin m) ℂ).transpose)
    (a : Fin m) :
    (σ a : ℂ) =
      ∑ p : Fin m × Fin m,
        S p.2 p.1 *
          (star ((U : Matrix (Fin m) (Fin m) ℂ) p.1 a) *
            star ((U : Matrix (Fin m) (Fin m) ℂ) p.2 a)) := by
  have hTU := matrix_unitary_transpose_mul_star_transpose m U
  have hdiag :
      ((star (U : Matrix (Fin m) (Fin m) ℂ)) * S *
        star ((U : Matrix (Fin m) (Fin m) ℂ).transpose)) a a = (σ a : ℂ) := by
    rw [hTakagi]
    calc
      ((star (U : Matrix (Fin m) (Fin m) ℂ)) *
            (((U : Matrix (Fin m) (Fin m) ℂ) *
              Matrix.diagonal (fun a => (σ a : ℂ)) *
              (U : Matrix (Fin m) (Fin m) ℂ).transpose)) *
          star ((U : Matrix (Fin m) (Fin m) ℂ).transpose)) a a =
          (((star (U : Matrix (Fin m) (Fin m) ℂ) *
                (U : Matrix (Fin m) (Fin m) ℂ)) *
              Matrix.diagonal (fun a => (σ a : ℂ)) *
              (((U : Matrix (Fin m) (Fin m) ℂ).transpose) *
                star ((U : Matrix (Fin m) (Fin m) ℂ).transpose))) a a) := by
        noncomm_ring
      _ = (Matrix.diagonal (fun a => (σ a : ℂ)) a a) := by
        rw [U.2.1, hTU]
        simp
      _ = (σ a : ℂ) := by
        simp [Matrix.diagonal]
  have hexpand :
      ((star (U : Matrix (Fin m) (Fin m) ℂ)) * S *
        star ((U : Matrix (Fin m) (Fin m) ℂ).transpose)) a a =
        ∑ p : Fin m × Fin m,
          S p.2 p.1 *
            (star ((U : Matrix (Fin m) (Fin m) ℂ) p.1 a) *
              star ((U : Matrix (Fin m) (Fin m) ℂ) p.2 a)) := by
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [← Finset.sum_product' Finset.univ Finset.univ]
    simp [mul_comm, mul_left_comm]
  rw [← hdiag]
  exact hexpand

/-- In any Takagi diagonalization, each singular value is bounded by the
entrywise `ℓ¹` size of the original matrix. -/
theorem takagi_singularValue_le_entryL1Bound
    (m : ℕ)
    {S : Matrix (Fin m) (Fin m) ℂ}
    {U : Matrix.unitaryGroup (Fin m) ℂ}
    {σ : Fin m → ℝ}
    (hσ_nonneg : ∀ a, 0 ≤ σ a)
    (hTakagi :
      S =
        (U : Matrix (Fin m) (Fin m) ℂ) *
          Matrix.diagonal (fun a => (σ a : ℂ)) *
          (U : Matrix (Fin m) (Fin m) ℂ).transpose) :
    ∀ a, σ a ≤ matrixEntryL1Bound m S := by
  intro a
  have hσeq := takagi_diagonal_extraction (m := m) (S := S) (U := U)
    (σ := σ) hTakagi a
  have hnormσ : ‖(σ a : ℂ)‖ = σ a :=
    RCLike.norm_of_nonneg (K := ℂ) (hσ_nonneg a)
  have hsum_le :
      ‖∑ p : Fin m × Fin m,
        S p.2 p.1 *
          (star ((U : Matrix (Fin m) (Fin m) ℂ) p.1 a) *
            star ((U : Matrix (Fin m) (Fin m) ℂ) p.2 a))‖ ≤
      ∑ p : Fin m × Fin m, ‖S p.2 p.1‖ := by
    calc
      ‖∑ p : Fin m × Fin m,
        S p.2 p.1 *
          (star ((U : Matrix (Fin m) (Fin m) ℂ) p.1 a) *
            star ((U : Matrix (Fin m) (Fin m) ℂ) p.2 a))‖
          ≤ ∑ p : Fin m × Fin m,
              ‖S p.2 p.1 *
                (star ((U : Matrix (Fin m) (Fin m) ℂ) p.1 a) *
                  star ((U : Matrix (Fin m) (Fin m) ℂ) p.2 a))‖ := by
        exact norm_sum_le _ _
      _ ≤ ∑ p : Fin m × Fin m, ‖S p.2 p.1‖ := by
        apply Finset.sum_le_sum
        intro p _hp
        rw [norm_mul, norm_mul, norm_star, norm_star]
        have h1 := matrix_unitary_entry_norm_le_one m U p.1 a
        have h2 := matrix_unitary_entry_norm_le_one m U p.2 a
        have hprod :
            ‖(U : Matrix (Fin m) (Fin m) ℂ) p.1 a‖ *
              ‖(U : Matrix (Fin m) (Fin m) ℂ) p.2 a‖ ≤ 1 := by
          calc
            ‖(U : Matrix (Fin m) (Fin m) ℂ) p.1 a‖ *
                ‖(U : Matrix (Fin m) (Fin m) ℂ) p.2 a‖ ≤ 1 * 1 := by
              exact mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
            _ = 1 := by
              ring
        calc
          ‖S p.2 p.1‖ *
              (‖(U : Matrix (Fin m) (Fin m) ℂ) p.1 a‖ *
                ‖(U : Matrix (Fin m) (Fin m) ℂ) p.2 a‖) ≤
              ‖S p.2 p.1‖ * 1 := by
            exact mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
          _ = ‖S p.2 p.1‖ := by
            ring
  have hswap :
      (∑ p : Fin m × Fin m, ‖S p.2 p.1‖) = matrixEntryL1Bound m S := by
    unfold matrixEntryL1Bound
    refine Fintype.sum_equiv (Equiv.prodComm (Fin m) (Fin m)) _ _ ?_
    intro p
    rfl
  calc
    σ a = ‖(σ a : ℂ)‖ := by
      rw [hnormσ]
    _ = ‖∑ p : Fin m × Fin m,
        S p.2 p.1 *
          (star ((U : Matrix (Fin m) (Fin m) ℂ) p.1 a) *
            star ((U : Matrix (Fin m) (Fin m) ℂ) p.2 a))‖ := by
      rw [hσeq]
    _ ≤ ∑ p : Fin m × Fin m, ‖S p.2 p.1‖ := hsum_le
    _ = matrixEntryL1Bound m S := hswap

/-- Once the Takagi diagonalization and rank-support identity are available,
the entry-controlled rectangular factor is now mechanical. -/
theorem complexSymmetric_entryL1_of_autonneTakagiDiagonalization
    (m k : ℕ)
    {S : Matrix (Fin m) (Fin m) ℂ}
    {U : Matrix.unitaryGroup (Fin m) ℂ}
    {σ : Fin m → ℝ}
    (hσ_nonneg : ∀ a, 0 ≤ σ a)
    (hTakagi :
      S =
        (U : Matrix (Fin m) (Fin m) ℂ) *
          Matrix.diagonal (fun a => (σ a : ℂ)) *
          (U : Matrix (Fin m) (Fin m) ℂ).transpose)
    (hrankSupport : Fintype.card {a : Fin m // σ a ≠ 0} = S.rank)
    (hRank : S.rank ≤ k) :
    ∃ A : Matrix (Fin m) (Fin k) ℂ,
      S = A * A.transpose ∧
      ∀ i a, ‖A i a‖ ≤ Real.sqrt (matrixEntryL1Bound m S) := by
  exact complexSymmetric_entryL1_of_takagiDiagonalData_rankSupport
    (m := m) (k := k) (S := S) (U := U) (σ := σ)
    hσ_nonneg hTakagi hrankSupport hRank
    (takagi_singularValue_le_entryL1Bound (m := m) (S := S) (U := U)
      (σ := σ) hσ_nonneg hTakagi)

end BHW
