import Mathlib.LinearAlgebra.Matrix.Permutation
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexSchurPatch
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedAdaptedRepresentative
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedHeadGaugeNormal
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedNormalParameter

/-!
# Finite source normal-form transport support

This file begins the checked finite-dimensional infrastructure for the
Hall-Wightman Lemma-3 normal-form transport.  It contains only source-label
bookkeeping, block matrices, and permutation invariance of scalar Gram rank;
the analytic continuation and perturbative estimates remain in the proof docs
until their finite support is all checked.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Reindex source labels as the first `r` head labels followed by the
remaining `n - r` tail labels. -/
noncomputable def sourceHeadTailEquiv
    (n r : ℕ) (hrn : r ≤ n) :
    Fin n ≃ Fin r ⊕ Fin (n - r) :=
  (Equiv.ofBijective
    (Sum.elim (finSourceHead hrn) (finSourceTail hrn))
    (by
      constructor
      · intro x y hxy
        cases x with
        | inl a =>
            cases y with
            | inl b =>
                exact congrArg Sum.inl ((finSourceHead_injective hrn) hxy)
            | inr v =>
                exact False.elim ((finSourceHead_ne_finSourceTail hrn a v) hxy)
        | inr u =>
            cases y with
            | inl b =>
                exact False.elim ((finSourceHead_ne_finSourceTail hrn b u) hxy.symm)
            | inr v =>
                exact congrArg Sum.inr ((finSourceTail_injective hrn) hxy)
      · intro i
        rcases finSourceHead_tail_cases hrn i with ⟨a, rfl⟩ | ⟨u, rfl⟩
        · exact ⟨Sum.inl a, rfl⟩
        · exact ⟨Sum.inr u, rfl⟩)).symm

@[simp]
theorem sourceHeadTailEquiv_apply_head
    {n r : ℕ} (hrn : r ≤ n) (a : Fin r) :
    sourceHeadTailEquiv n r hrn (finSourceHead hrn a) = Sum.inl a := by
  rw [sourceHeadTailEquiv, Equiv.symm_apply_eq]
  rfl

@[simp]
theorem sourceHeadTailEquiv_apply_tail
    {n r : ℕ} (hrn : r ≤ n) (u : Fin (n - r)) :
    sourceHeadTailEquiv n r hrn (finSourceTail hrn u) = Sum.inr u := by
  rw [sourceHeadTailEquiv, Equiv.symm_apply_eq]
  rfl

/-- Block matrix for the source head/tail split, with lower-left block `B`
and upper-right block `Bᵀ`. -/
def sourceBlockMatrix
    (n r : ℕ) (hrn : r ≤ n)
    (A : Matrix (Fin r) (Fin r) ℂ)
    (B : Matrix (Fin (n - r)) (Fin r) ℂ)
    (C : Matrix (Fin (n - r)) (Fin (n - r)) ℂ) :
    Fin n → Fin n → ℂ :=
  let E := sourceHeadTailEquiv n r hrn
  fun i j =>
    (Matrix.fromBlocks A B.transpose B C) (E i) (E j)

def sourceHeadHeadBlock
    (n r : ℕ) (hrn : r ≤ n)
    (G : Fin n → Fin n → ℂ) :
    Matrix (Fin r) (Fin r) ℂ :=
  fun a b => G (finSourceHead hrn a) (finSourceHead hrn b)

def sourceTailHeadBlock
    (n r : ℕ) (hrn : r ≤ n)
    (G : Fin n → Fin n → ℂ) :
    Matrix (Fin (n - r)) (Fin r) ℂ :=
  fun u a => G (finSourceTail hrn u) (finSourceHead hrn a)

def sourceTailTailBlock
    (n r : ℕ) (hrn : r ≤ n)
    (G : Fin n → Fin n → ℂ) :
    Matrix (Fin (n - r)) (Fin (n - r)) ℂ :=
  fun u v => G (finSourceTail hrn u) (finSourceTail hrn v)

/-- Source-index linear change on ordered source tuples. -/
def sourceTupleLinearChange
    (d n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    Fin n → Fin (d + 1) → ℂ :=
  fun i μ => ∑ a : Fin n, M i a * z a μ

theorem sourceTupleLinearChange_mul
    (d n : ℕ)
    (M N : Matrix (Fin n) (Fin n) ℂ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceTupleLinearChange d n (M * N) z =
      sourceTupleLinearChange d n M (sourceTupleLinearChange d n N z) := by
  ext i μ
  calc
    sourceTupleLinearChange d n (M * N) z i μ =
        ∑ a : Fin n, ∑ b : Fin n, M i b * (N b a * z a μ) := by
          simp [sourceTupleLinearChange, Matrix.mul_apply, Finset.sum_mul,
            mul_assoc]
    _ = ∑ b : Fin n, ∑ a : Fin n, M i b * (N b a * z a μ) := by
          rw [Finset.sum_comm]
    _ =
        sourceTupleLinearChange d n M
          (sourceTupleLinearChange d n N z) i μ := by
          simp [sourceTupleLinearChange, Finset.mul_sum]

theorem sourceTupleLinearChange_one
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceTupleLinearChange d n 1 z = z := by
  ext i μ
  simp [sourceTupleLinearChange, Matrix.one_apply]

/-- Linear map on source tuples induced by a source-label matrix. -/
def sourceTupleLinearMap
    (d n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    (Fin n → Fin (d + 1) → ℂ) →ₗ[ℂ]
      (Fin n → Fin (d + 1) → ℂ) where
  toFun := sourceTupleLinearChange d n M
  map_add' z w := by
    ext i μ
    simp [sourceTupleLinearChange, mul_add, Finset.sum_add_distrib]
  map_smul' c z := by
    ext i μ
    simp [sourceTupleLinearChange, Finset.mul_sum, mul_left_comm]

@[simp]
theorem sourceTupleLinearMap_apply
    (d n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceTupleLinearMap d n M z =
      sourceTupleLinearChange d n M z := rfl

/-- Invertible source-label matrices induce linear equivalences of source
tuples, applied independently in every spacetime coordinate. -/
def sourceTupleLinearEquivOfMatrix
    (d n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : IsUnit M.det) :
    (Fin n → Fin (d + 1) → ℂ) ≃ₗ[ℂ]
      (Fin n → Fin (d + 1) → ℂ) where
  toLinearMap := sourceTupleLinearMap d n M
  invFun := sourceTupleLinearChange d n M⁻¹
  left_inv z := by
    change sourceTupleLinearChange d n M⁻¹
      (sourceTupleLinearChange d n M z) = z
    rw [← sourceTupleLinearChange_mul]
    rw [Matrix.nonsing_inv_mul (A := M) hM]
    exact sourceTupleLinearChange_one d n z
  right_inv z := by
    change sourceTupleLinearChange d n M
      (sourceTupleLinearChange d n M⁻¹ z) = z
    rw [← sourceTupleLinearChange_mul]
    rw [Matrix.mul_nonsing_inv (A := M) hM]
    exact sourceTupleLinearChange_one d n z

@[simp]
theorem sourceTupleLinearEquivOfMatrix_apply
    (d n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : IsUnit M.det)
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceTupleLinearEquivOfMatrix d n M hM z =
      sourceTupleLinearChange d n M z := rfl

/-- Source-index congruence on scalar Gram matrices. -/
def sourceGramCongruence
    (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (Z : Fin n → Fin n → ℂ) :
    Fin n → Fin n → ℂ :=
  fun i j => ∑ a : Fin n, ∑ b : Fin n, M i a * Z a b * M j b

theorem sourceGramCongruence_eq_matrix_mul
    (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (Z : Fin n → Fin n → ℂ) :
    Matrix.of (sourceGramCongruence n M Z) =
      M * Matrix.of Z * M.transpose := by
  ext i j
  calc
    Matrix.of (sourceGramCongruence n M Z) i j =
        ∑ a : Fin n, ∑ b : Fin n, M i a * (Z a b * M j b) := by
          simp [sourceGramCongruence, mul_assoc]
    _ = ∑ b : Fin n, ∑ a : Fin n, M i a * (Z a b * M j b) := by
          rw [Finset.sum_comm]
    _ = (M * Matrix.of Z * M.transpose) i j := by
          simp [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum,
            mul_comm, mul_left_comm]

theorem sourceGramCongruence_mul
    (n : ℕ)
    (M N : Matrix (Fin n) (Fin n) ℂ)
    (Z : Fin n → Fin n → ℂ) :
    sourceGramCongruence n (M * N) Z =
      sourceGramCongruence n M (sourceGramCongruence n N Z) := by
  change Matrix.of (sourceGramCongruence n (M * N) Z) =
    Matrix.of (sourceGramCongruence n M (sourceGramCongruence n N Z))
  rw [sourceGramCongruence_eq_matrix_mul,
    sourceGramCongruence_eq_matrix_mul,
    sourceGramCongruence_eq_matrix_mul]
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

/-- Source-label block matrix for linear changes in the head/tail split. -/
def sourceLinearBlockMatrix
    (n r : ℕ) (hrn : r ≤ n)
    (X : Matrix (Fin r) (Fin r) ℂ)
    (Y : Matrix (Fin r) (Fin (n - r)) ℂ)
    (Z : Matrix (Fin (n - r)) (Fin r) ℂ)
    (W : Matrix (Fin (n - r)) (Fin (n - r)) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  let E := sourceHeadTailEquiv n r hrn
  fun i j => (Matrix.fromBlocks X Y Z W) (E i) (E j)

@[simp]
theorem sourceLinearBlockMatrix_head_head
    (n r : ℕ) (hrn : r ≤ n)
    (X : Matrix (Fin r) (Fin r) ℂ)
    (Y : Matrix (Fin r) (Fin (n - r)) ℂ)
    (Z : Matrix (Fin (n - r)) (Fin r) ℂ)
    (W : Matrix (Fin (n - r)) (Fin (n - r)) ℂ)
    (a b : Fin r) :
    sourceLinearBlockMatrix n r hrn X Y Z W
        (finSourceHead hrn a) (finSourceHead hrn b) =
      X a b := by
  simp [sourceLinearBlockMatrix]

@[simp]
theorem sourceLinearBlockMatrix_head_tail
    (n r : ℕ) (hrn : r ≤ n)
    (X : Matrix (Fin r) (Fin r) ℂ)
    (Y : Matrix (Fin r) (Fin (n - r)) ℂ)
    (Z : Matrix (Fin (n - r)) (Fin r) ℂ)
    (W : Matrix (Fin (n - r)) (Fin (n - r)) ℂ)
    (a : Fin r) (u : Fin (n - r)) :
    sourceLinearBlockMatrix n r hrn X Y Z W
        (finSourceHead hrn a) (finSourceTail hrn u) =
      Y a u := by
  simp [sourceLinearBlockMatrix]

@[simp]
theorem sourceLinearBlockMatrix_tail_head
    (n r : ℕ) (hrn : r ≤ n)
    (X : Matrix (Fin r) (Fin r) ℂ)
    (Y : Matrix (Fin r) (Fin (n - r)) ℂ)
    (Z : Matrix (Fin (n - r)) (Fin r) ℂ)
    (W : Matrix (Fin (n - r)) (Fin (n - r)) ℂ)
    (u : Fin (n - r)) (a : Fin r) :
    sourceLinearBlockMatrix n r hrn X Y Z W
        (finSourceTail hrn u) (finSourceHead hrn a) =
      Z u a := by
  simp [sourceLinearBlockMatrix]

@[simp]
theorem sourceLinearBlockMatrix_tail_tail
    (n r : ℕ) (hrn : r ≤ n)
    (X : Matrix (Fin r) (Fin r) ℂ)
    (Y : Matrix (Fin r) (Fin (n - r)) ℂ)
    (Z : Matrix (Fin (n - r)) (Fin r) ℂ)
    (W : Matrix (Fin (n - r)) (Fin (n - r)) ℂ)
    (u v : Fin (n - r)) :
    sourceLinearBlockMatrix n r hrn X Y Z W
        (finSourceTail hrn u) (finSourceTail hrn v) =
      W u v := by
  simp [sourceLinearBlockMatrix]

theorem sourceLinearBlockMatrix_reindex_headTail
    (n r : ℕ) (hrn : r ≤ n)
    (X : Matrix (Fin r) (Fin r) ℂ)
    (Y : Matrix (Fin r) (Fin (n - r)) ℂ)
    (Z : Matrix (Fin (n - r)) (Fin r) ℂ)
    (W : Matrix (Fin (n - r)) (Fin (n - r)) ℂ) :
    (sourceLinearBlockMatrix n r hrn X Y Z W).submatrix
        (sourceHeadTailEquiv n r hrn).symm (sourceHeadTailEquiv n r hrn).symm =
      Matrix.fromBlocks X Y Z W := by
  ext x y
  cases x with
  | inl a =>
      cases y with
      | inl b => simp [sourceLinearBlockMatrix]
      | inr v => simp [sourceLinearBlockMatrix]
  | inr u =>
      cases y with
      | inl b => simp [sourceLinearBlockMatrix]
      | inr v => simp [sourceLinearBlockMatrix]

theorem sourceGramCongruence_reindex_headTail
    (n r : ℕ) (hrn : r ≤ n)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (Z : Fin n → Fin n → ℂ) :
    (Matrix.of (sourceGramCongruence n M Z)).submatrix
        (sourceHeadTailEquiv n r hrn).symm (sourceHeadTailEquiv n r hrn).symm =
      M.submatrix (sourceHeadTailEquiv n r hrn).symm
          (sourceHeadTailEquiv n r hrn).symm *
        (Matrix.of Z).submatrix (sourceHeadTailEquiv n r hrn).symm
          (sourceHeadTailEquiv n r hrn).symm *
        (M.submatrix (sourceHeadTailEquiv n r hrn).symm
          (sourceHeadTailEquiv n r hrn).symm).transpose := by
  let E := (sourceHeadTailEquiv n r hrn).symm
  rw [sourceGramCongruence_eq_matrix_mul]
  rw [← Matrix.submatrix_mul_equiv
      (M := M * Matrix.of Z) (N := M.transpose)
      (e₁ := E) (e₂ := E) (e₃ := E),
    ← Matrix.submatrix_mul_equiv
      (M := M) (N := Matrix.of Z)
      (e₁ := E) (e₂ := E) (e₃ := E),
    Matrix.transpose_submatrix]

theorem matrix_eq_of_sourceHeadTail_reindex_eq
    (n r : ℕ) (hrn : r ≤ n)
    {M N : Matrix (Fin n) (Fin n) ℂ}
    (h :
      M.submatrix (sourceHeadTailEquiv n r hrn).symm
          (sourceHeadTailEquiv n r hrn).symm =
        N.submatrix (sourceHeadTailEquiv n r hrn).symm
          (sourceHeadTailEquiv n r hrn).symm) :
    M = N := by
  ext i j
  have hij :=
    congrFun (congrFun h (sourceHeadTailEquiv n r hrn i))
      (sourceHeadTailEquiv n r hrn j)
  simpa using hij

theorem sourceLinearBlockMatrix_det_eq_fromBlocks_det
    (n r : ℕ) (hrn : r ≤ n)
    (X : Matrix (Fin r) (Fin r) ℂ)
    (Y : Matrix (Fin r) (Fin (n - r)) ℂ)
    (Z : Matrix (Fin (n - r)) (Fin r) ℂ)
    (W : Matrix (Fin (n - r)) (Fin (n - r)) ℂ) :
    (sourceLinearBlockMatrix n r hrn X Y Z W).det =
      (Matrix.fromBlocks X Y Z W).det := by
  let E := sourceHeadTailEquiv n r hrn
  rw [← Matrix.det_submatrix_equiv_self E.symm
    (sourceLinearBlockMatrix n r hrn X Y Z W)]
  exact congrArg Matrix.det
    (sourceLinearBlockMatrix_reindex_headTail n r hrn X Y Z W)

/-- The Schur projection source change `tail ↦ tail - B A⁻¹ head`. -/
def hwLemma3_projectionSourceChangeMatrix
    (n r : ℕ) (hrn : r ≤ n)
    (A : Matrix (Fin r) (Fin r) ℂ)
    (B : Matrix (Fin (n - r)) (Fin r) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  sourceLinearBlockMatrix n r hrn 1 0 (-B * A⁻¹) 1

theorem hwLemma3_projectionSourceChangeMatrix_det_isUnit
    (n r : ℕ) (hrn : r ≤ n)
    (A : Matrix (Fin r) (Fin r) ℂ)
    (B : Matrix (Fin (n - r)) (Fin r) ℂ) :
    IsUnit (hwLemma3_projectionSourceChangeMatrix n r hrn A B).det := by
  apply isUnit_iff_ne_zero.mpr
  rw [hwLemma3_projectionSourceChangeMatrix,
    sourceLinearBlockMatrix_det_eq_fromBlocks_det,
    Matrix.det_fromBlocks_zero₁₂]
  simp

/-- Extend a selected-head change by the identity on the source tail. -/
def hwLemma3_extendHeadMatrix
    (n r : ℕ) (hrn : r ≤ n)
    (P : Matrix (Fin r) (Fin r) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  sourceLinearBlockMatrix n r hrn P 0 0 1

theorem hwLemma3_extendHeadMatrix_det_isUnit
    (n r : ℕ) (hrn : r ≤ n)
    {P : Matrix (Fin r) (Fin r) ℂ}
    (hP : IsUnit P.det) :
    IsUnit (hwLemma3_extendHeadMatrix n r hrn P).det := by
  rw [hwLemma3_extendHeadMatrix,
    sourceLinearBlockMatrix_det_eq_fromBlocks_det,
    Matrix.det_fromBlocks_zero₁₂]
  simpa using hP

/-- Canonical scalar Gram matrix for the Lemma-3 normal form.  The head block
is the inherited Minkowski-signature diagonal, not the Euclidean identity. -/
def hwLemma3CanonicalGram
    (d n r : ℕ) (hrD : r < d + 1) (hrn : r ≤ n) :
    Fin n → Fin n → ℂ :=
  sourceBlockMatrix n r hrn (sourceHeadMetric d r hrD) 0 0

theorem hwLemma3CanonicalGram_eq_sourceBlockMatrix
    (d n r : ℕ) (hrD : r < d + 1) (hrn : r ≤ n) :
    hwLemma3CanonicalGram d n r hrD hrn =
      sourceBlockMatrix n r hrn (sourceHeadMetric d r hrD) 0 0 := rfl

@[simp]
theorem sourceBlockMatrix_head_head
    (n r : ℕ) (hrn : r ≤ n)
    (A : Matrix (Fin r) (Fin r) ℂ)
    (B : Matrix (Fin (n - r)) (Fin r) ℂ)
    (C : Matrix (Fin (n - r)) (Fin (n - r)) ℂ)
    (a b : Fin r) :
    sourceBlockMatrix n r hrn A B C
        (finSourceHead hrn a) (finSourceHead hrn b) =
      A a b := by
  simp [sourceBlockMatrix]

@[simp]
theorem sourceBlockMatrix_tail_head
    (n r : ℕ) (hrn : r ≤ n)
    (A : Matrix (Fin r) (Fin r) ℂ)
    (B : Matrix (Fin (n - r)) (Fin r) ℂ)
    (C : Matrix (Fin (n - r)) (Fin (n - r)) ℂ)
    (u : Fin (n - r)) (a : Fin r) :
    sourceBlockMatrix n r hrn A B C
        (finSourceTail hrn u) (finSourceHead hrn a) =
      B u a := by
  simp [sourceBlockMatrix]

@[simp]
theorem sourceBlockMatrix_head_tail
    (n r : ℕ) (hrn : r ≤ n)
    (A : Matrix (Fin r) (Fin r) ℂ)
    (B : Matrix (Fin (n - r)) (Fin r) ℂ)
    (C : Matrix (Fin (n - r)) (Fin (n - r)) ℂ)
    (a : Fin r) (u : Fin (n - r)) :
    sourceBlockMatrix n r hrn A B C
        (finSourceHead hrn a) (finSourceTail hrn u) =
      B u a := by
  simp [sourceBlockMatrix]

@[simp]
theorem sourceBlockMatrix_tail_tail
    (n r : ℕ) (hrn : r ≤ n)
    (A : Matrix (Fin r) (Fin r) ℂ)
    (B : Matrix (Fin (n - r)) (Fin r) ℂ)
    (C : Matrix (Fin (n - r)) (Fin (n - r)) ℂ)
    (u v : Fin (n - r)) :
    sourceBlockMatrix n r hrn A B C
        (finSourceTail hrn u) (finSourceTail hrn v) =
      C u v := by
  simp [sourceBlockMatrix]

theorem sourceBlockMatrix_reindex_headTail
    (n r : ℕ) (hrn : r ≤ n)
    (A : Matrix (Fin r) (Fin r) ℂ)
    (B : Matrix (Fin (n - r)) (Fin r) ℂ)
    (C : Matrix (Fin (n - r)) (Fin (n - r)) ℂ) :
    ((Matrix.of fun i j : Fin n => sourceBlockMatrix n r hrn A B C i j).submatrix
        (sourceHeadTailEquiv n r hrn).symm (sourceHeadTailEquiv n r hrn).symm) =
      Matrix.fromBlocks A B.transpose B C := by
  ext x y
  cases x with
  | inl a =>
      cases y with
      | inl b => simp [sourceBlockMatrix]
      | inr v => simp [sourceBlockMatrix]
  | inr u =>
      cases y with
      | inl b => simp [sourceBlockMatrix]
      | inr v => simp [sourceBlockMatrix]

theorem sourceGramCongruence_sourceLinearBlockMatrix_sourceBlockMatrix_reindex
    (n r : ℕ) (hrn : r ≤ n)
    (X : Matrix (Fin r) (Fin r) ℂ)
    (Y : Matrix (Fin r) (Fin (n - r)) ℂ)
    (Z : Matrix (Fin (n - r)) (Fin r) ℂ)
    (W : Matrix (Fin (n - r)) (Fin (n - r)) ℂ)
    (A : Matrix (Fin r) (Fin r) ℂ)
    (B : Matrix (Fin (n - r)) (Fin r) ℂ)
    (C : Matrix (Fin (n - r)) (Fin (n - r)) ℂ) :
    (Matrix.of
      (sourceGramCongruence n
        (sourceLinearBlockMatrix n r hrn X Y Z W)
        (sourceBlockMatrix n r hrn A B C))).submatrix
        (sourceHeadTailEquiv n r hrn).symm
        (sourceHeadTailEquiv n r hrn).symm =
      Matrix.fromBlocks X Y Z W *
        Matrix.fromBlocks A B.transpose B C *
          (Matrix.fromBlocks X Y Z W).transpose := by
  rw [sourceGramCongruence_reindex_headTail,
    sourceLinearBlockMatrix_reindex_headTail,
    sourceBlockMatrix_reindex_headTail]

theorem hwLemma3_projectionSourceChangeMatrix_congruence
    (n r : ℕ) (hrn : r ≤ n)
    {A : Matrix (Fin r) (Fin r) ℂ}
    {B : Matrix (Fin (n - r)) (Fin r) ℂ}
    {C : Matrix (Fin (n - r)) (Fin (n - r)) ℂ}
    (hA : IsUnit A.det)
    (hAsym : A.transpose = A) :
    sourceGramCongruence n
        (hwLemma3_projectionSourceChangeMatrix n r hrn A B)
        (sourceBlockMatrix n r hrn A B C) =
      sourceBlockMatrix n r hrn A 0 (C - B * A⁻¹ * B.transpose) := by
  change Matrix.of
      (sourceGramCongruence n
        (hwLemma3_projectionSourceChangeMatrix n r hrn A B)
        (sourceBlockMatrix n r hrn A B C)) =
    Matrix.of (sourceBlockMatrix n r hrn A 0
      (C - B * A⁻¹ * B.transpose))
  apply matrix_eq_of_sourceHeadTail_reindex_eq n r hrn
  calc
    (Matrix.of
      (sourceGramCongruence n
        (hwLemma3_projectionSourceChangeMatrix n r hrn A B)
        (sourceBlockMatrix n r hrn A B C))).submatrix
        (sourceHeadTailEquiv n r hrn).symm
        (sourceHeadTailEquiv n r hrn).symm =
        Matrix.fromBlocks 1 0 (-B * A⁻¹) 1 *
          Matrix.fromBlocks A B.transpose B C *
            (Matrix.fromBlocks 1 0 (-B * A⁻¹) 1).transpose := by
          simpa [hwLemma3_projectionSourceChangeMatrix] using
            sourceGramCongruence_sourceLinearBlockMatrix_sourceBlockMatrix_reindex
              n r hrn 1 0 (-B * A⁻¹) 1 A B C
    _ = Matrix.fromBlocks A 0 0 (C - B * A⁻¹ * B.transpose) := by
          have hAinvT : (A⁻¹).transpose = A⁻¹ := by
            rw [Matrix.transpose_nonsing_inv, hAsym]
          have hUpper :
              A * (A⁻¹ * B.transpose) = B.transpose :=
            Matrix.mul_nonsing_inv_cancel_left (A := A) B.transpose hA
          have hLower : B * A⁻¹ * A = B :=
            Matrix.nonsing_inv_mul_cancel_right (A := A) B hA
          simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose,
            hAinvT, hUpper, hLower, ← Matrix.mul_assoc,
            sub_eq_add_neg, add_comm]
    _ =
        (Matrix.of (sourceBlockMatrix n r hrn A 0
          (C - B * A⁻¹ * B.transpose))).submatrix
          (sourceHeadTailEquiv n r hrn).symm
          (sourceHeadTailEquiv n r hrn).symm := by
          simpa using
            (sourceBlockMatrix_reindex_headTail n r hrn A
              (0 : Matrix (Fin (n - r)) (Fin r) ℂ)
              (C - B * A⁻¹ * B.transpose)).symm

theorem hwLemma3_extendHeadMatrix_congruence
    (n r : ℕ) (hrn : r ≤ n)
    (P A : Matrix (Fin r) (Fin r) ℂ) :
    sourceGramCongruence n
        (hwLemma3_extendHeadMatrix n r hrn P)
        (sourceBlockMatrix n r hrn A 0 0) =
      sourceBlockMatrix n r hrn (P * A * P.transpose) 0 0 := by
  change Matrix.of
      (sourceGramCongruence n
        (hwLemma3_extendHeadMatrix n r hrn P)
        (sourceBlockMatrix n r hrn A 0 0)) =
    Matrix.of (sourceBlockMatrix n r hrn (P * A * P.transpose) 0 0)
  apply matrix_eq_of_sourceHeadTail_reindex_eq n r hrn
  calc
    (Matrix.of
      (sourceGramCongruence n
        (hwLemma3_extendHeadMatrix n r hrn P)
        (sourceBlockMatrix n r hrn A 0 0))).submatrix
        (sourceHeadTailEquiv n r hrn).symm
        (sourceHeadTailEquiv n r hrn).symm =
        Matrix.fromBlocks P 0 0 1 *
          Matrix.fromBlocks A 0 0 0 *
            (Matrix.fromBlocks P 0 0 1).transpose := by
          simpa [hwLemma3_extendHeadMatrix] using
            sourceGramCongruence_sourceLinearBlockMatrix_sourceBlockMatrix_reindex
              n r hrn P 0 0 1 A 0 0
    _ = Matrix.fromBlocks (P * A * P.transpose) 0 0 0 := by
          simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose,
            Matrix.mul_assoc]
    _ =
        (Matrix.of (sourceBlockMatrix n r hrn
          (P * A * P.transpose) 0 0)).submatrix
          (sourceHeadTailEquiv n r hrn).symm
          (sourceHeadTailEquiv n r hrn).symm := by
          simpa using
            (sourceBlockMatrix_reindex_headTail n r hrn
              (P * A * P.transpose)
              (0 : Matrix (Fin (n - r)) (Fin r) ℂ)
              (0 : Matrix (Fin (n - r)) (Fin (n - r)) ℂ)).symm

theorem sourceBlockMatrix_of_headTailBlocks
    (n r : ℕ) (hrn : r ≤ n)
    (G : Fin n → Fin n → ℂ)
    (hG : G ∈ sourceSymmetricMatrixSpace n) :
    sourceBlockMatrix n r hrn
      (sourceHeadHeadBlock n r hrn G)
      (sourceTailHeadBlock n r hrn G)
      (sourceTailTailBlock n r hrn G) = G := by
  ext i j
  rcases finSourceHead_tail_cases hrn i with ⟨a, rfl⟩ | ⟨u, rfl⟩
  · rcases finSourceHead_tail_cases hrn j with ⟨b, rfl⟩ | ⟨v, rfl⟩
    · simp [sourceHeadHeadBlock]
    · simpa [sourceTailHeadBlock] using
        hG (finSourceTail hrn v) (finSourceHead hrn a)
  · rcases finSourceHead_tail_cases hrn j with ⟨b, rfl⟩ | ⟨v, rfl⟩
    · simp [sourceTailHeadBlock]
    · simp [sourceTailTailBlock]

theorem sourceHeadHeadBlock_symm_of_sourceSymmetric
    (n r : ℕ) (hrn : r ≤ n)
    {G : Fin n → Fin n → ℂ}
    (hG : G ∈ sourceSymmetricMatrixSpace n) :
    (sourceHeadHeadBlock n r hrn G).transpose =
      sourceHeadHeadBlock n r hrn G := by
  ext a b
  exact hG (finSourceHead hrn b) (finSourceHead hrn a)

/-- Matrix form of the ordinary complex dot-Gram map. -/
theorem sourceComplexDotGram_matrix_eq_mul_transpose
    (D n : ℕ)
    (z : Fin n → Fin D → ℂ) :
    Matrix.of (sourceComplexDotGram D n z) =
      (Matrix.of fun i a => z i a) *
        (Matrix.of fun i a => z i a).transpose := by
  ext i j
  simp [sourceComplexDotGram, Matrix.mul_apply]

/-- Any invertible complex symmetric matrix is congruent to the identity.
The proof uses the existing exact-rank dot-Gram factorization: write
`A = Q Qᵀ`; then invertibility of `A` forces `Q` invertible. -/
theorem complexSymmetric_invertible_congruence_to_identity
    (r : ℕ)
    {A : Matrix (Fin r) (Fin r) ℂ}
    (hSym : A.transpose = A)
    (hInv : IsUnit A.det) :
    ∃ P : Matrix (Fin r) (Fin r) ℂ,
      IsUnit P.det ∧
        P * A * P.transpose = 1 := by
  let Z : Fin r → Fin r → ℂ := fun i j => A i j
  have hZ : Z ∈ sourceSymmetricRankExactStratum r r := by
    constructor
    · intro i j
      change A i j = A j i
      have hij := congrFun (congrFun hSym j) i
      simpa [Matrix.transpose_apply] using hij
    · change A.rank = r
      have hAunit : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr hInv
      simpa using Matrix.rank_of_isUnit A hAunit
  rcases exists_fullRank_sourceComplexDotGram_of_rankExact hZ with
    ⟨Qfun, _hQfull, hQeq⟩
  let Q : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun i a => Qfun i a
  have hAeq : A = Q * Q.transpose := by
    change Matrix.of Z = Q * Q.transpose
    have h := congrArg Matrix.of hQeq
    exact h.symm.trans (by simpa [Q] using
      sourceComplexDotGram_matrix_eq_mul_transpose r r Qfun)
  have hdetQ_ne : Q.det ≠ 0 := by
    have hdetprod : Q.det * Q.det ≠ 0 := by
      have hdet_eq : A.det = Q.det * Q.det := by
        rw [hAeq, Matrix.det_mul, Matrix.det_transpose]
      intro hzero
      exact hInv.ne_zero (by simpa [hdet_eq] using hzero)
    exact fun hzero => hdetprod (by simp [hzero])
  have hQdet : IsUnit Q.det := isUnit_iff_ne_zero.mpr hdetQ_ne
  refine ⟨Q⁻¹, Matrix.isUnit_nonsing_inv_det Q hQdet, ?_⟩
  rw [hAeq]
  calc
    Q⁻¹ * (Q * Q.transpose) * (Q⁻¹).transpose =
        (Q⁻¹ * Q) * (Q.transpose * (Q⁻¹).transpose) := by
          simp [Matrix.mul_assoc]
    _ = 1 * (Q.transpose * (Q⁻¹).transpose) := by
          rw [Matrix.nonsing_inv_mul (A := Q) hQdet]
    _ = Q.transpose * (Q⁻¹).transpose := by simp
    _ = Q.transpose * (Q.transpose)⁻¹ := by
          rw [Matrix.transpose_nonsing_inv]
    _ = 1 := by
          rw [Matrix.mul_nonsing_inv (A := Q.transpose)
            (Matrix.isUnit_det_transpose Q hQdet)]

/-- Diagonal square-root of the canonical source head metric. -/
def sourceHeadMetricSquareRoot
    (d r : ℕ) (hrD : r < d + 1) :
    Matrix (Fin r) (Fin r) ℂ :=
  Matrix.diagonal fun a =>
    complexSquareRootChoice
      (MinkowskiSpace.metricSignature d
        (finSourceHead (Nat.le_of_lt hrD) a) : ℂ)

theorem sourceHeadMetricSquareRoot_det_isUnit
    (d r : ℕ) (hrD : r < d + 1) :
    IsUnit (sourceHeadMetricSquareRoot d r hrD).det := by
  rw [sourceHeadMetricSquareRoot]
  simp only [det_diagonal]
  apply isUnit_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro a _ha hsqrt_zero
  have hsq := complexSquareRootChoice_mul_self
    (MinkowskiSpace.metricSignature d
      (finSourceHead (Nat.le_of_lt hrD) a) : ℂ)
  have hmetric_zero :
      (MinkowskiSpace.metricSignature d
        (finSourceHead (Nat.le_of_lt hrD) a) : ℂ) = 0 := by
    rw [← hsq, hsqrt_zero, zero_mul]
  by_cases hzero : finSourceHead (Nat.le_of_lt hrD) a = (0 : Fin (d + 1))
  · simp [MinkowskiSpace.metricSignature, hzero] at hmetric_zero
  · simp [MinkowskiSpace.metricSignature, hzero] at hmetric_zero

theorem sourceHeadMetricSquareRoot_congruence
    (d r : ℕ) (hrD : r < d + 1) :
    sourceHeadMetricSquareRoot d r hrD * 1 *
        (sourceHeadMetricSquareRoot d r hrD).transpose =
      sourceHeadMetric d r hrD := by
  ext a b
  by_cases hab : a = b
  · subst b
    simp [sourceHeadMetricSquareRoot, sourceHeadMetric,
      complexSquareRootChoice_mul_self]
  · simp [sourceHeadMetricSquareRoot, sourceHeadMetric, hab]

/-- Any invertible complex symmetric head block is congruent to the canonical
Minkowski-signature source head metric. -/
theorem complexSymmetric_invertible_congruence_to_sourceHeadMetric
    (d r : ℕ) (hrD : r < d + 1)
    {A : Matrix (Fin r) (Fin r) ℂ}
    (hSym : A.transpose = A)
    (hInv : IsUnit A.det) :
    ∃ P : Matrix (Fin r) (Fin r) ℂ,
      IsUnit P.det ∧
        P * A * P.transpose = sourceHeadMetric d r hrD := by
  rcases complexSymmetric_invertible_congruence_to_identity
      r hSym hInv with
    ⟨P0, hP0det, hP0⟩
  let D := sourceHeadMetricSquareRoot d r hrD
  refine ⟨D * P0, ?_, ?_⟩
  · rw [Matrix.det_mul]
    exact (sourceHeadMetricSquareRoot_det_isUnit d r hrD).mul hP0det
  · calc
      (D * P0) * A * (D * P0).transpose =
          D * (P0 * A * P0.transpose) * D.transpose := by
            rw [Matrix.transpose_mul]
            simp [Matrix.mul_assoc]
      _ = D * 1 * D.transpose := by rw [hP0]
      _ = sourceHeadMetric d r hrD := by
            simpa [D] using sourceHeadMetricSquareRoot_congruence d r hrD

/-- A permutation matrix for source labels.  Its left action on a tuple sends
the `i`-th output source vector to the old `σ i` source vector. -/
def sourcePermutationMatrix
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Matrix (Fin n) (Fin n) ℂ :=
  σ.permMatrix ℂ

theorem sourcePermutationMatrix_det_isUnit
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    IsUnit (sourcePermutationMatrix n σ).det := by
  apply isUnit_iff_ne_zero.mpr
  simp [sourcePermutationMatrix]

/-- Full source normal-form change: first permute the selected principal block
to the head, then subtract its Schur projection from the tail, then apply the
head normalizer. -/
def hwLemma3_normalFormSourceChangeMatrix
    (n r : ℕ) (hrn : r ≤ n)
    (σ : Equiv.Perm (Fin n))
    (A : Matrix (Fin r) (Fin r) ℂ)
    (B : Matrix (Fin (n - r)) (Fin r) ℂ)
    (P : Matrix (Fin r) (Fin r) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  hwLemma3_extendHeadMatrix n r hrn P *
    hwLemma3_projectionSourceChangeMatrix n r hrn A B *
      sourcePermutationMatrix n σ

theorem hwLemma3_normalFormSourceChangeMatrix_det_isUnit
    (n r : ℕ) (hrn : r ≤ n)
    (σ : Equiv.Perm (Fin n))
    {A : Matrix (Fin r) (Fin r) ℂ}
    {B : Matrix (Fin (n - r)) (Fin r) ℂ}
    {P : Matrix (Fin r) (Fin r) ℂ}
    (_hA : IsUnit A.det)
    (hP : IsUnit P.det) :
    IsUnit (hwLemma3_normalFormSourceChangeMatrix
      n r hrn σ A B P).det := by
  rw [hwLemma3_normalFormSourceChangeMatrix, Matrix.det_mul, Matrix.det_mul]
  simpa [mul_assoc] using
    (hwLemma3_extendHeadMatrix_det_isUnit n r hrn hP).mul
      ((hwLemma3_projectionSourceChangeMatrix_det_isUnit n r hrn A B).mul
        (sourcePermutationMatrix_det_isUnit n σ))

theorem sourceTupleLinearChange_sourcePermutationMatrix
    (d n : ℕ) (σ : Equiv.Perm (Fin n))
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceTupleLinearChange d n
        (sourcePermutationMatrix n σ) z =
      fun i => z (σ i) := by
  ext i μ
  have h :=
    congrFun (Matrix.permMatrix_mulVec
      (R := ℂ) (σ := σ) (v := fun a : Fin n => z a μ)) i
  simp [sourceTupleLinearChange, sourcePermutationMatrix, Matrix.mulVec_eq_sum] at h ⊢

theorem sourceGramCongruence_sourcePermutationMatrix
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    (Z : Fin n → Fin n → ℂ) :
    sourceGramCongruence n (sourcePermutationMatrix n σ) Z =
      sourcePermuteComplexGram n σ Z := by
  ext i j
  simp [sourceGramCongruence, sourcePermutationMatrix,
    sourcePermuteComplexGram, Equiv.Perm.permMatrix]

theorem hwLemma3_normalFormSourceChangeMatrix_canonicalGram
    (d n r : ℕ) (hrD : r < d + 1) (hrn : r ≤ n)
    {G : Fin n → Fin n → ℂ}
    {σ : Equiv.Perm (Fin n)}
    {A : Matrix (Fin r) (Fin r) ℂ}
    {B : Matrix (Fin (n - r)) (Fin r) ℂ}
    {C : Matrix (Fin (n - r)) (Fin (n - r)) ℂ}
    {P : Matrix (Fin r) (Fin r) ℂ}
    (hBlock :
      sourcePermuteComplexGram n σ G =
        sourceBlockMatrix n r hrn A B C)
    (hA : IsUnit A.det)
    (hAsym : A.transpose = A)
    (hSchur : C - B * A⁻¹ * B.transpose = 0)
    (hP : P * A * P.transpose = sourceHeadMetric d r hrD) :
    sourceGramCongruence n
      (hwLemma3_normalFormSourceChangeMatrix n r hrn σ A B P) G =
        hwLemma3CanonicalGram d n r hrD hrn := by
  rw [hwLemma3_normalFormSourceChangeMatrix]
  rw [sourceGramCongruence_mul]
  rw [sourceGramCongruence_mul]
  rw [sourceGramCongruence_sourcePermutationMatrix, hBlock]
  rw [hwLemma3_projectionSourceChangeMatrix_congruence
    (n := n) (r := r) (hrn := hrn) hA hAsym]
  rw [hSchur]
  rw [hwLemma3_extendHeadMatrix_congruence]
  rw [hP]
  rfl

theorem sourceMinkowskiGram_sourceTupleLinearChange
    (d n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceMinkowskiGram d n (sourceTupleLinearChange d n M z) =
      sourceGramCongruence n M (sourceMinkowskiGram d n z) := by
  ext i j
  calc
    sourceMinkowskiGram d n (sourceTupleLinearChange d n M z) i j
        =
          ∑ μ : Fin (d + 1), ∑ a : Fin n, ∑ b : Fin n,
            M i a * (M j b *
              (z a μ * (z b μ * (MinkowskiSpace.metricSignature d μ : ℂ)))) := by
          simp [sourceMinkowskiGram, sourceTupleLinearChange,
            Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
    _ =
          ∑ a : Fin n, ∑ b : Fin n, ∑ μ : Fin (d + 1),
            M i a * (M j b *
              (z a μ * (z b μ * (MinkowskiSpace.metricSignature d μ : ℂ)))) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a _ha
          rw [Finset.sum_comm]
    _ =
        sourceGramCongruence n M (sourceMinkowskiGram d n z) i j := by
          simp [sourceMinkowskiGram, sourceGramCongruence,
            Finset.mul_sum, mul_comm, mul_left_comm]

/-- Coefficient evaluation after a source-label linear change is coefficient
evaluation against the original tuple after right multiplication of source
coefficients by the same matrix. -/
theorem sourceCoefficientEval_sourceTupleLinearChange
    (d n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (a : Fin n → ℂ) :
    sourceCoefficientEval d n (sourceTupleLinearChange d n M z) a =
      sourceCoefficientEval d n z (sourceCoefficientGramMap n M a) := by
  ext μ
  calc
    sourceCoefficientEval d n (sourceTupleLinearChange d n M z) a μ =
        ∑ i : Fin n, ∑ j : Fin n, a i * (M i j * z j μ) := by
          simp [sourceCoefficientEval, sourceTupleLinearChange, Pi.smul_apply,
            Finset.mul_sum]
    _ = ∑ j : Fin n, ∑ i : Fin n, a i * (M i j * z j μ) := by
          rw [Finset.sum_comm]
    _ = sourceCoefficientEval d n z (sourceCoefficientGramMap n M a) μ := by
          simp [sourceCoefficientEval, sourceCoefficientGramMap,
            Finset.mul_sum, mul_comm, mul_left_comm]

theorem sourceCoefficientEval_sourceTupleLinearChange_linear
    (d n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceCoefficientEval d n (sourceTupleLinearChange d n M z) =
      (sourceCoefficientEval d n z).comp (sourceCoefficientGramMap n M) := by
  apply LinearMap.ext
  intro a
  exact sourceCoefficientEval_sourceTupleLinearChange d n M z a

/-- Right multiplication of coefficient rows by an invertible source matrix is
surjective. -/
theorem sourceCoefficientGramMap_range_eq_top_of_isUnit_det
    (n : ℕ) {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : IsUnit M.det) :
    LinearMap.range (sourceCoefficientGramMap n M) = ⊤ := by
  apply LinearMap.range_eq_top.mpr
  intro a
  let Minv : Matrix (Fin n) (Fin n) ℂ := M⁻¹
  refine ⟨sourceCoefficientGramMap n Minv a, ?_⟩
  ext j
  calc
    sourceCoefficientGramMap n M (sourceCoefficientGramMap n Minv a) j =
        ∑ i : Fin n, ∑ k : Fin n, a k * (Minv k i * M i j) := by
          simp [sourceCoefficientGramMap, Finset.sum_mul, Minv, mul_assoc]
    _ = ∑ k : Fin n, a k * ∑ i : Fin n, Minv k i * M i j := by
          rw [Finset.sum_comm]
          simp [Finset.mul_sum]
    _ = ∑ k : Fin n, a k * (1 : Matrix (Fin n) (Fin n) ℂ) k j := by
          apply Finset.sum_congr rfl
          intro k _hk
          have hmul := Matrix.nonsing_inv_mul (A := M) hM
          exact congrArg (fun x => a k * x)
            (congrFun (congrFun hmul k) j)
    _ = a j := by
          simp [Matrix.one_apply]

/-- Invertible source-label changes preserve the source-vector span. -/
theorem sourceCoefficientEval_range_sourceTupleLinearChange_eq
    (d n : ℕ)
    {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : IsUnit M.det)
    (z : Fin n → Fin (d + 1) → ℂ) :
    LinearMap.range
        (sourceCoefficientEval d n (sourceTupleLinearChange d n M z)) =
      LinearMap.range (sourceCoefficientEval d n z) := by
  rw [sourceCoefficientEval_sourceTupleLinearChange_linear]
  rw [LinearMap.range_comp_of_range_eq_top
    (sourceCoefficientEval d n z)
    (sourceCoefficientGramMap_range_eq_top_of_isUnit_det n hM)]

theorem sourceGramMatrixRank_sourceGramCongruence
    (n : ℕ) {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : IsUnit M.det)
    (Z : Fin n → Fin n → ℂ) :
    sourceGramMatrixRank n (sourceGramCongruence n M Z) =
      sourceGramMatrixRank n Z := by
  change (Matrix.of (sourceGramCongruence n M Z)).rank = (Matrix.of Z).rank
  rw [sourceGramCongruence_eq_matrix_mul]
  rw [Matrix.rank_mul_eq_left_of_isUnit_det
    (A := M.transpose) (B := M * Matrix.of Z)
    (Matrix.isUnit_det_transpose M hM)]
  rw [Matrix.rank_mul_eq_right_of_isUnit_det
    (A := M) (B := Matrix.of Z) hM]

/-- Invertible source-label changes preserve adaptedness: the coefficient
span dimension still equals the scalar Gram rank. -/
theorem sourceTupleLinearChange_adapted_of_isUnit
    (d n : ℕ)
    {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : IsUnit M.det)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hadapt :
      Module.finrank ℂ (LinearMap.range (sourceCoefficientEval d n z)) =
        sourceGramMatrixRank n (sourceMinkowskiGram d n z)) :
    Module.finrank ℂ
        (LinearMap.range
          (sourceCoefficientEval d n (sourceTupleLinearChange d n M z))) =
      sourceGramMatrixRank n
        (sourceMinkowskiGram d n (sourceTupleLinearChange d n M z)) := by
  rw [sourceCoefficientEval_range_sourceTupleLinearChange_eq d n hM z]
  rw [sourceMinkowskiGram_sourceTupleLinearChange]
  rw [sourceGramMatrixRank_sourceGramCongruence n hM]
  exact hadapt

theorem sourceMinkowskiGram_hwLemma3CanonicalSource
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    sourceMinkowskiGram d n (hwLemma3CanonicalSource d n r) =
      hwLemma3CanonicalGram d n r hrD hrn := by
  ext i j
  rcases finSourceHead_tail_cases hrn i with ⟨a, rfl⟩ | ⟨u, rfl⟩
  · rcases finSourceHead_tail_cases hrn j with ⟨b, rfl⟩ | ⟨v, rfl⟩
    · simp [hwLemma3CanonicalGram,
        sourceMinkowskiGram_hwLemma3CanonicalSource_head d n r hrD hrn a b]
    · have htail := hwLemma3CanonicalSource_tail d n r hrn v
      simp [hwLemma3CanonicalGram, sourceMinkowskiGram, htail]
  · have htail_i := hwLemma3CanonicalSource_tail d n r hrn u
    rcases finSourceHead_tail_cases hrn j with ⟨b, rfl⟩ | ⟨v, rfl⟩
    · simp [hwLemma3CanonicalGram, sourceMinkowskiGram, htail_i]
    · have htail_j := hwLemma3CanonicalSource_tail d n r hrn v
      simp [hwLemma3CanonicalGram, sourceMinkowskiGram, htail_i, htail_j]

/-- If the restricted Minkowski rank equals the source-span dimension, then
the restricted form on that source span is nondegenerate. -/
theorem complexMinkowskiNondegenerate_of_restrictedRank_eq_finrank
    (d : ℕ) {M : Submodule ℂ (Fin (d + 1) → ℂ)}
    (h : restrictedMinkowskiRank d M = Module.finrank ℂ M) :
    ComplexMinkowskiNondegenerateSubspace d M := by
  by_contra hdeg
  have hlt := restrictedMinkowskiRank_lt_finrank_of_degenerate (d := d) hdeg
  rw [h] at hlt
  exact Nat.lt_irrefl _ hlt

/-- An adapted source tuple, whose coefficient-span dimension equals its
scalar Gram rank, has nondegenerate restricted Minkowski form on its source
span. -/
theorem complexMinkowskiNondegenerate_eval_range_of_adapted
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hadapt :
      Module.finrank ℂ (LinearMap.range (sourceCoefficientEval d n z)) =
        sourceGramMatrixRank n (sourceMinkowskiGram d n z)) :
    ComplexMinkowskiNondegenerateSubspace d
      (LinearMap.range (sourceCoefficientEval d n z)) := by
  apply complexMinkowskiNondegenerate_of_restrictedRank_eq_finrank
  rw [← sourceGramMatrixRank_eq_restrictedMinkowskiRank_range]
  exact hadapt.symm

/-- In the Lemma-3 canonical Gram normal form, adaptedness forces every tail
source vector to vanish.  Without adaptedness the zero tail Gram block would
only say that the tail vectors are radical/isotropic. -/
theorem hwLemma3_canonicalGram_tail_zero_of_adapted
    (d n r : ℕ) (hrD : r < d + 1) (hrn : r ≤ n)
    {w : Fin n → Fin (d + 1) → ℂ}
    (hGram : sourceMinkowskiGram d n w = hwLemma3CanonicalGram d n r hrD hrn)
    (hadapt :
      Module.finrank ℂ (LinearMap.range (sourceCoefficientEval d n w)) =
        sourceGramMatrixRank n (sourceMinkowskiGram d n w)) :
    ∀ u : Fin (n - r), w (finSourceTail hrn u) = 0 := by
  let evalW := sourceCoefficientEval d n w
  let M := LinearMap.range evalW
  have hNondeg : ComplexMinkowskiNondegenerateSubspace d M := by
    simpa [evalW, M] using
      complexMinkowskiNondegenerate_eval_range_of_adapted d n w hadapt
  intro u
  let t : Fin n := finSourceTail hrn u
  let coeffTail : Fin n → ℂ := Pi.single t 1
  have htail_eval : evalW coeffTail = w t := by
    simpa [evalW, coeffTail, t] using sourceCoefficientEval_single d n w t
  have htail_mem : w t ∈ M :=
    ⟨coeffTail, htail_eval⟩
  have htail_row_zero : ∀ j : Fin n, sourceMinkowskiGram d n w t j = 0 := by
    intro j
    have hentry := congrFun (congrFun hGram t) j
    rcases finSourceHead_tail_cases hrn j with ⟨a, rfl⟩ | ⟨v, rfl⟩
    · simpa [t, hwLemma3CanonicalGram] using hentry
    · simpa [t, hwLemma3CanonicalGram] using hentry
  have hgramMap_zero :
      sourceCoefficientGramMap n (sourceMinkowskiGram d n w) coeffTail = 0 := by
    ext j
    rw [sourceCoefficientGramMap]
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single t]
    · simp [coeffTail, htail_row_zero j]
    · intro i _hi hit
      simp [coeffTail, Pi.single_eq_of_ne hit]
    · intro htmem
      exact False.elim (htmem (Finset.mem_univ t))
  have horth_eval : ∀ b : Fin n → ℂ,
      sourceComplexMinkowskiInner d (evalW coeffTail) (evalW b) = 0 :=
    (sourceCoefficientGramMap_eq_zero_iff_eval_pair_eval_eq_zero d n w
      coeffTail).1 hgramMap_zero
  have horth : ∀ y : M,
      sourceComplexMinkowskiInner d
        ((⟨w t, htail_mem⟩ : M) : Fin (d + 1) → ℂ)
        (y : Fin (d + 1) → ℂ) = 0 := by
    intro y
    rcases y with ⟨_, b, rfl⟩
    simpa [htail_eval] using horth_eval b
  have hzero_sub : (⟨w t, htail_mem⟩ : M) = 0 :=
    hNondeg ⟨w t, htail_mem⟩ horth
  exact congrArg Subtype.val hzero_sub

/-- If an invertible source change sends the source Gram to the canonical
Lemma-3 Gram and the original tuple is adapted, then the changed tuple has
zero tail vectors. -/
theorem sourceTupleLinearChange_tail_zero_of_canonicalGram_adapted
    (d n r : ℕ) (hrD : r < d + 1) (hrn : r ≤ n)
    {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : IsUnit M.det)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hGram : sourceGramCongruence n M (sourceMinkowskiGram d n z) =
      hwLemma3CanonicalGram d n r hrD hrn)
    (hadapt :
      Module.finrank ℂ (LinearMap.range (sourceCoefficientEval d n z)) =
        sourceGramMatrixRank n (sourceMinkowskiGram d n z)) :
    ∀ u : Fin (n - r),
      sourceTupleLinearChange d n M z (finSourceTail hrn u) = 0 := by
  let w := sourceTupleLinearChange d n M z
  have hwGram :
      sourceMinkowskiGram d n w =
        hwLemma3CanonicalGram d n r hrD hrn := by
    simpa [w, sourceMinkowskiGram_sourceTupleLinearChange] using hGram
  have hwAdapt :
      Module.finrank ℂ (LinearMap.range (sourceCoefficientEval d n w)) =
        sourceGramMatrixRank n (sourceMinkowskiGram d n w) := by
    simpa [w] using sourceTupleLinearChange_adapted_of_isUnit d n hM hadapt
  exact hwLemma3_canonicalGram_tail_zero_of_adapted d n r hrD hrn hwGram hwAdapt

/-- Tail-zero for the concrete normal-form source-change matrix. -/
theorem hwLemma3_normalFormSourceChange_tail_zero_of_adapted
    (d n r : ℕ) (hrD : r < d + 1) (hrn : r ≤ n)
    (σ : Equiv.Perm (Fin n))
    {A : Matrix (Fin r) (Fin r) ℂ}
    {B : Matrix (Fin (n - r)) (Fin r) ℂ}
    {P : Matrix (Fin r) (Fin r) ℂ}
    (hA : IsUnit A.det)
    (hP : IsUnit P.det)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hGram :
      sourceGramCongruence n
        (hwLemma3_normalFormSourceChangeMatrix n r hrn σ A B P)
        (sourceMinkowskiGram d n z) =
          hwLemma3CanonicalGram d n r hrD hrn)
    (hadapt :
      Module.finrank ℂ (LinearMap.range (sourceCoefficientEval d n z)) =
        sourceGramMatrixRank n (sourceMinkowskiGram d n z)) :
    ∀ u : Fin (n - r),
      sourceTupleLinearChange d n
        (hwLemma3_normalFormSourceChangeMatrix n r hrn σ A B P) z
        (finSourceTail hrn u) = 0 := by
  apply sourceTupleLinearChange_tail_zero_of_canonicalGram_adapted
    (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)
    (M := hwLemma3_normalFormSourceChangeMatrix n r hrn σ A B P)
  · exact hwLemma3_normalFormSourceChangeMatrix_det_isUnit n r hrn σ hA hP
  · exact hGram
  · exact hadapt

/-- If an adapted source tuple already has the Lemma-3 canonical Gram, then a
complex Lorentz transformation sends it to the canonical source tuple.  The
head-frame normalization is the determinant-one complex Witt extension; the
tail labels vanish by the checked adapted canonical-tail theorem. -/
theorem hwLemma3_canonicalGram_exists_complexLorentz_to_canonicalSource_of_adapted
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {w : Fin n → Fin (d + 1) → ℂ}
    (hGram :
      sourceMinkowskiGram d n w =
        hwLemma3CanonicalGram d n r hrD hrn)
    (hadapt :
      Module.finrank ℂ
          (LinearMap.range (sourceCoefficientEval d n w)) =
        sourceGramMatrixRank n (sourceMinkowskiGram d n w)) :
    ∃ Λ : ComplexLorentzGroup d,
      complexLorentzAction Λ w = hwLemma3CanonicalSource d n r := by
  let x : Fin r → Fin (d + 1) → ℂ := fun a => w (finSourceHead hrn a)
  have hHeadGram :
      ∀ a b : Fin r,
        sourceVectorMinkowskiInner d (x a) (x b) =
          if a = b then
            (MinkowskiSpace.metricSignature d
              (finSourceHead (Nat.le_of_lt hrD) a) : ℂ)
          else 0 := by
    intro a b
    have h :=
      congrFun (congrFun hGram (finSourceHead hrn a)) (finSourceHead hrn b)
    simpa [x, hwLemma3CanonicalGram, sourceHeadMetric_apply] using h
  obtain ⟨Λ, hΛhead⟩ :=
    complexMinkowski_detOneWittExtension_to_canonicalHeadFrame
      d r hrD x hHeadGram
  refine ⟨Λ, ?_⟩
  ext i μ
  rcases finSourceHead_tail_cases hrn i with ⟨a, rfl⟩ | ⟨u, rfl⟩
  · have h := congrFun (hΛhead a) μ
    simpa [complexLorentzAction, x,
      hwLemma3CanonicalSource_head_apply (hrD := hrD)] using h
  · have htail :
        w (finSourceTail hrn u) = 0 :=
      hwLemma3_canonicalGram_tail_zero_of_adapted
        d n r hrD hrn hGram hadapt u
    have hΛtail :
        complexLorentzAction Λ w (finSourceTail hrn u) = 0 := by
      ext ν
      simp [complexLorentzAction, complexLorentzVectorAction, htail]
    have hcanon :
        hwLemma3CanonicalSource d n r (finSourceTail hrn u) = 0 :=
      hwLemma3CanonicalSource_tail d n r hrn u
    exact congrFun hΛtail μ |>.trans (congrFun hcanon μ).symm

/-- The checked normal-form source change has a complex Lorentz representative
to the canonical source tuple, provided its scalar Gram is the canonical
Lemma-3 Gram and the original tuple is adapted. -/
theorem hwLemma3_normalFormSourceChange_exists_complexLorentz_to_canonicalSource_of_adapted
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {σ : Equiv.Perm (Fin n)}
    {A : Matrix (Fin r) (Fin r) ℂ}
    {B : Matrix (Fin (n - r)) (Fin r) ℂ}
    {P : Matrix (Fin r) (Fin r) ℂ}
    (hA : IsUnit A.det)
    (hP : IsUnit P.det)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hGram :
      sourceGramCongruence n
        (hwLemma3_normalFormSourceChangeMatrix
          n r hrn σ A B P)
        (sourceMinkowskiGram d n z) =
      hwLemma3CanonicalGram d n r hrD hrn)
    (hadapt :
      Module.finrank ℂ
          (LinearMap.range (sourceCoefficientEval d n z)) =
        sourceGramMatrixRank n (sourceMinkowskiGram d n z)) :
    ∃ Λ : ComplexLorentzGroup d,
      complexLorentzAction Λ
        (sourceTupleLinearChange d n
          (hwLemma3_normalFormSourceChangeMatrix n r hrn σ A B P) z) =
        hwLemma3CanonicalSource d n r := by
  let M := hwLemma3_normalFormSourceChangeMatrix n r hrn σ A B P
  have hM : IsUnit M.det :=
    hwLemma3_normalFormSourceChangeMatrix_det_isUnit n r hrn σ hA hP
  apply
    hwLemma3_canonicalGram_exists_complexLorentz_to_canonicalSource_of_adapted
      d n r hrD hrn
  · simpa [M, sourceMinkowskiGram_sourceTupleLinearChange] using hGram
  · simpa [M] using sourceTupleLinearChange_adapted_of_isUnit d n hM hadapt

theorem hwLemma3_schurComplement_eq_zero_of_rank_eq
    (n r : ℕ) (hrn : r ≤ n)
    {G : Fin n → Fin n → ℂ}
    {A : Matrix (Fin r) (Fin r) ℂ}
    {B : Matrix (Fin (n - r)) (Fin r) ℂ}
    {C : Matrix (Fin (n - r)) (Fin (n - r)) ℂ}
    (hGsym : G ∈ sourceSymmetricMatrixSpace n)
    (hBlock : G = sourceBlockMatrix n r hrn A B C)
    (hRank : sourceGramMatrixRank n G = r)
    (hA : IsUnit A.det) :
    C - B * A⁻¹ * B.transpose = 0 := by
  let E := sourceHeadTailEquiv n r hrn
  have hA' :
      IsUnit ((((Matrix.of fun i j : Fin n => G i j).reindex E E).toBlocks₁₁).det) := by
    subst G
    simpa [E, sourceBlockMatrix_reindex_headTail] using hA
  have hRank' :
      (Matrix.of fun i j : Fin n => G i j).rank = Fintype.card (Fin r) := by
    simpa [sourceGramMatrixRank] using hRank
  have hschur :=
    (rank_eq_card_iff_reindexed_schur_complement_eq_zero
      (Z := (Matrix.of fun i j : Fin n => G i j))
      (e := E)
      (hZsym := hGsym)
      (hA := hA')).1 hRank'
  subst G
  simpa [E, sourceBlockMatrix_reindex_headTail] using hschur

theorem sourceGramMatrixRank_sourcePermuteComplexGram
    (n : ℕ) (σ : Equiv.Perm (Fin n))
  (G : Fin n → Fin n → ℂ) :
    sourceGramMatrixRank n (sourcePermuteComplexGram n σ G) =
      sourceGramMatrixRank n G := by
  change (Matrix.submatrix G σ σ).rank = Matrix.rank G
  exact Matrix.rank_submatrix (G : Matrix (Fin n) (Fin n) ℂ) σ σ

theorem sourcePermuteComplexGram_mem_sourceSymmetricMatrixSpace
    (n : ℕ) (σ : Equiv.Perm (Fin n))
    {G : Fin n → Fin n → ℂ}
    (hG : G ∈ sourceSymmetricMatrixSpace n) :
    sourcePermuteComplexGram n σ G ∈ sourceSymmetricMatrixSpace n := by
  intro i j
  exact hG (σ i) (σ j)

theorem exists_sourcePermutation_movingPrincipalBlockToHead
    (n r : ℕ)
    (hrn : r ≤ n)
    {I : Fin r → Fin n}
    (hI : Function.Injective I) :
  ∃ σ : Equiv.Perm (Fin n),
      ∀ a : Fin r, σ (finSourceHead hrn a) = I a := by
  classical
  have hcard_sum :
      n = r + Fintype.card (selectedIndexComplement I) := by
    simpa using Fintype.card_congr (selectedIndexSumEquiv I hI)
  have hcard_compl :
      Fintype.card (selectedIndexComplement I) = n - r := by
    omega
  have hcard_tail :
      Fintype.card (Fin (n - r)) =
        Fintype.card (selectedIndexComplement I) := by
    simp [hcard_compl]
  let eTail : Fin (n - r) ≃ selectedIndexComplement I :=
    Fintype.equivOfCardEq hcard_tail
  let σ : Equiv.Perm (Fin n) :=
    (sourceHeadTailEquiv n r hrn).trans
      ((Equiv.refl (Fin r)).sumCongr eTail) |>.trans
        (selectedIndexSumEquiv I hI).symm
  refine ⟨σ, ?_⟩
  intro a
  simp only [σ, Equiv.trans_apply, sourceHeadTailEquiv_apply_head,
    Equiv.sumCongr_apply]
  rw [Equiv.symm_apply_eq]
  simp [selectedIndexSumEquiv_apply_selected I hI a]

end BHW
