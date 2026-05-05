import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.CStarAlgebra.Matrix
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexGlobalIdentity

/-!
# Quantitative complex symmetric factorization support

This file isolates the finite entry-size estimates used to turn an
entry-controlled complex symmetric dot-factorization into the small-factor
statement needed by the Euclidean tail realization route.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial Module
open scoped Matrix.Norms.Operator

namespace BHW

/-- Entrywise `ℓ¹` size of a finite square complex matrix.  This avoids
choosing a matrix norm while proving the small-factor estimate. -/
noncomputable def matrixEntryL1Bound
    (m : ℕ) (S : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  ∑ p : Fin m × Fin m, ‖S p.1 p.2‖

theorem matrixEntryL1Bound_nonneg
    (m : ℕ) (S : Matrix (Fin m) (Fin m) ℂ) :
    0 ≤ matrixEntryL1Bound m S := by
  unfold matrixEntryL1Bound
  exact Finset.sum_nonneg (fun p _hp => norm_nonneg (S p.1 p.2))

/-- If every matrix entry is bounded by `δ`, then the finite entry-`ℓ¹`
bound is bounded by `((m*m)+1) δ`.  The `+1` keeps the empty case painless. -/
theorem matrixEntryL1Bound_lt_of_entry_bound
    (m : ℕ)
    {S : Matrix (Fin m) (Fin m) ℂ}
    {δ : ℝ} (hδ : 0 < δ)
    (hS : ∀ i j, ‖S i j‖ < δ) :
    matrixEntryL1Bound m S < (((m * m : ℕ) : ℝ) + 1) * δ := by
  unfold matrixEntryL1Bound
  have hle : (∑ p : Fin m × Fin m, ‖S p.1 p.2‖) ≤
      ∑ _p : Fin m × Fin m, δ := by
    exact Finset.sum_le_sum (fun p _hp => le_of_lt (hS p.1 p.2))
  have hsum : (∑ _p : Fin m × Fin m, δ) = ((m * m : ℕ) : ℝ) * δ := by
    simp
  calc
    (∑ p : Fin m × Fin m, ‖S p.1 p.2‖)
        ≤ ∑ _p : Fin m × Fin m, δ := hle
    _ = ((m * m : ℕ) : ℝ) * δ := hsum
    _ < (((m * m : ℕ) : ℝ) + 1) * δ := by
      nlinarith [hδ]

/-- Choose a positive entry bound whose square-root-scaled size is below the
target `ε`. -/
theorem exists_pos_mul_sqrt_lt
    {ε C : ℝ} (hε : 0 < ε) (hC : 0 < C) :
    ∃ δ : ℝ, 0 < δ ∧ Real.sqrt (C * δ) < ε := by
  refine ⟨ε ^ 2 / (4 * C), ?_, ?_⟩
  · positivity
  · have hmul : C * (ε ^ 2 / (4 * C)) = (ε / 2) ^ 2 := by
      field_simp [ne_of_gt hC]
      ring
    rw [hmul]
    rw [Real.sqrt_sq]
    · linarith
    · linarith

theorem real_sqrt_lt_of_lt_mul_bound
    {x C δ ε : ℝ}
    (hx : 0 ≤ x)
    (hxlt : x < C * δ)
    (hsmall : Real.sqrt (C * δ) < ε) :
    Real.sqrt x < ε := by
  exact (Real.sqrt_lt_sqrt hx hxlt).trans hsmall

/-- Entries of a unitary matrix have norm at most one. -/
theorem matrix_unitary_entry_norm_le_one
    (m : ℕ)
    (U : Matrix.unitaryGroup (Fin m) ℂ)
    (i a : Fin m) :
    ‖(U : Matrix (Fin m) (Fin m) ℂ) i a‖ ≤ 1 := by
  exact entry_norm_bound_of_unitary U.2 i a

/-- Unit-entry bound combined with a real square-root column scaling. -/
theorem matrix_unitary_entry_mul_real_sqrt_norm_le_sqrt
    (m : ℕ)
    (U : Matrix.unitaryGroup (Fin m) ℂ)
    (i a : Fin m)
    {σ L : ℝ}
    (hσ_le : σ ≤ L) :
    ‖(U : Matrix (Fin m) (Fin m) ℂ) i a * (Real.sqrt σ : ℂ)‖ ≤
      Real.sqrt L := by
  have hentry := matrix_unitary_entry_norm_le_one m U i a
  have hsqrtnorm : ‖(Real.sqrt σ : ℂ)‖ = Real.sqrt σ :=
    RCLike.norm_of_nonneg (K := ℂ) (Real.sqrt_nonneg σ)
  calc
    ‖(U : Matrix (Fin m) (Fin m) ℂ) i a * (Real.sqrt σ : ℂ)‖
        = ‖(U : Matrix (Fin m) (Fin m) ℂ) i a‖ *
            ‖(Real.sqrt σ : ℂ)‖ := by
          rw [norm_mul]
    _ = ‖(U : Matrix (Fin m) (Fin m) ℂ) i a‖ * Real.sqrt σ := by
          rw [hsqrtnorm]
    _ ≤ 1 * Real.sqrt σ := by
          exact mul_le_mul_of_nonneg_right hentry (Real.sqrt_nonneg σ)
    _ = Real.sqrt σ := by ring
    _ ≤ Real.sqrt L := Real.sqrt_le_sqrt hσ_le

/-- An entry-controlled complex symmetric factorization immediately gives the
small-entry factorization needed by the tail realization theorem. -/
theorem complexSymmetric_factorSmall_rankLE_of_entryL1
    (m k : ℕ)
    (hentry :
      ∀ {S : Matrix (Fin m) (Fin m) ℂ},
        S.transpose = S →
        S.rank ≤ k →
        ∃ A : Matrix (Fin m) (Fin k) ℂ,
          S = A * A.transpose ∧
          ∀ i a, ‖A i a‖ ≤ Real.sqrt (matrixEntryL1Bound m S))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ S : Matrix (Fin m) (Fin m) ℂ,
        S.transpose = S →
        S.rank ≤ k →
        (∀ i j, ‖S i j‖ < δ) →
        ∃ A : Matrix (Fin m) (Fin k) ℂ,
          (∀ i a, ‖A i a‖ < ε) ∧
          S = A * A.transpose := by
  let C : ℝ := (((m * m : ℕ) : ℝ) + 1)
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  rcases exists_pos_mul_sqrt_lt hε hC_pos with ⟨δ, hδ_pos, hδ_small⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro S hSym hRank hSmall
  rcases hentry hSym hRank with ⟨A, hA_factor, hA_bound⟩
  have hL1 : matrixEntryL1Bound m S < C * δ := by
    simpa [C] using matrixEntryL1Bound_lt_of_entry_bound (m := m) hδ_pos hSmall
  have hsqrt : Real.sqrt (matrixEntryL1Bound m S) < ε :=
    real_sqrt_lt_of_lt_mul_bound
      (matrixEntryL1Bound_nonneg m S) hL1 hδ_small
  refine ⟨A, ?_, hA_factor⟩
  intro i a
  exact lt_of_le_of_lt (hA_bound i a) hsqrt

/-- Source-coordinate version of `complexSymmetric_factorSmall_rankLE_of_entryL1`. -/
theorem sourceComplexSymmetric_factorSmall_rankLE_of_entryL1
    (m k : ℕ)
    (hentry :
      ∀ {S : Matrix (Fin m) (Fin m) ℂ},
        S.transpose = S →
        S.rank ≤ k →
        ∃ A : Matrix (Fin m) (Fin k) ℂ,
          S = A * A.transpose ∧
          ∀ i a, ‖A i a‖ ≤ Real.sqrt (matrixEntryL1Bound m S))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ S : Fin m → Fin m → ℂ,
        S ∈ sourceSymmetricMatrixSpace m →
        (Matrix.of fun i j : Fin m => S i j).rank ≤ k →
        (∀ i j, ‖S i j‖ < δ) →
        ∃ q : Fin m → Fin k → ℂ,
          (∀ i a, ‖q i a‖ < ε) ∧
          sourceComplexDotGram k m q = S := by
  rcases complexSymmetric_factorSmall_rankLE_of_entryL1
      (m := m) (k := k) hentry hε with
    ⟨δ, hδ_pos, hfactor⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro S hSym hRank hSmall
  let M : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i j : Fin m => S i j
  have hM_sym : M.transpose = M := by
    ext i j
    exact hSym j i
  have hM_small : ∀ i j, ‖M i j‖ < δ := by
    intro i j
    exact hSmall i j
  rcases hfactor M hM_sym hRank hM_small with ⟨A, hA_small, hA_factor⟩
  refine ⟨fun i a => A i a, hA_small, ?_⟩
  ext i j
  have hij := congrFun (congrFun hA_factor i) j
  simp [sourceComplexDotGram, M, Matrix.mul_apply] at hij ⊢
  exact hij.symm

end BHW
