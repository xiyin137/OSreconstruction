import Mathlib.LinearAlgebra.Matrix.Permutation
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexSchurPatch
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedAdaptedRepresentative
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedHeadGaugeNormal
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedNormalParameter
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedTransport

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

/-- A complex Lorentz transformation acts linearly on ordered source tuples. -/
def complexLorentzActionLinearMap
    (d n : ℕ)
    (Λ : ComplexLorentzGroup d) :
    (Fin n → Fin (d + 1) → ℂ) →ₗ[ℂ]
      (Fin n → Fin (d + 1) → ℂ) where
  toFun := complexLorentzAction Λ
  map_add' z w := by
    ext i μ
    simp [complexLorentzAction, complexLorentzVectorAction, mul_add,
      Finset.sum_add_distrib]
  map_smul' c z := by
    ext i μ
    simp [complexLorentzAction, complexLorentzVectorAction, Finset.mul_sum,
      mul_left_comm]

@[simp]
theorem complexLorentzActionLinearMap_apply
    (d n : ℕ)
    (Λ : ComplexLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ) :
    complexLorentzActionLinearMap d n Λ z =
      complexLorentzAction Λ z := rfl

/-- A complex Lorentz transformation acts by a linear equivalence on ordered
source tuples. -/
def complexLorentzActionLinearEquiv
    (d n : ℕ)
    (Λ : ComplexLorentzGroup d) :
    (Fin n → Fin (d + 1) → ℂ) ≃ₗ[ℂ]
      (Fin n → Fin (d + 1) → ℂ) where
  toLinearMap := complexLorentzActionLinearMap d n Λ
  invFun := complexLorentzAction Λ⁻¹
  left_inv z := by
    exact complexLorentzAction_inv Λ z
  right_inv z := by
    simpa using complexLorentzAction_inv (Λ := Λ⁻¹) z

@[simp]
theorem complexLorentzActionLinearEquiv_apply
    (d n : ℕ)
    (Λ : ComplexLorentzGroup d)
    (z : Fin n → Fin (d + 1) → ℂ) :
    complexLorentzActionLinearEquiv d n Λ z =
      complexLorentzAction Λ z := rfl

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

theorem sourceGramCongruence_one
    (n : ℕ)
    (Z : Fin n → Fin n → ℂ) :
    sourceGramCongruence n 1 Z = Z := by
  ext i j
  simp [sourceGramCongruence, Matrix.one_apply]

/-- Source-index congruence is linear in the scalar Gram coordinate. -/
def sourceGramCongruenceLinearMap
    (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    (Fin n → Fin n → ℂ) →ₗ[ℂ] (Fin n → Fin n → ℂ) where
  toFun := sourceGramCongruence n M
  map_add' Z W := by
    ext i j
    calc
      sourceGramCongruence n M (Z + W) i j =
          ∑ a : Fin n, ∑ b : Fin n,
            (M i a * Z a b * M j b +
              M i a * W a b * M j b) := by
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            simp
            ring
      _ = sourceGramCongruence n M Z i j +
          sourceGramCongruence n M W i j := by
            simp [sourceGramCongruence, Finset.sum_add_distrib]
  map_smul' c Z := by
    ext i j
    simp [sourceGramCongruence, Finset.mul_sum, mul_assoc, mul_left_comm]

@[simp]
theorem sourceGramCongruenceLinearMap_apply
    (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (Z : Fin n → Fin n → ℂ) :
    sourceGramCongruenceLinearMap n M Z =
      sourceGramCongruence n M Z := rfl

/-- Invertible source-label matrices induce linear equivalences on scalar
Gram-coordinate matrices by congruence. -/
def sourceGramCongruenceLinearEquivOfMatrix
    (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : IsUnit M.det) :
    (Fin n → Fin n → ℂ) ≃ₗ[ℂ] (Fin n → Fin n → ℂ) where
  toLinearMap := sourceGramCongruenceLinearMap n M
  invFun := sourceGramCongruence n M⁻¹
  left_inv Z := by
    change sourceGramCongruence n M⁻¹ (sourceGramCongruence n M Z) = Z
    rw [← sourceGramCongruence_mul]
    rw [Matrix.nonsing_inv_mul (A := M) hM]
    exact sourceGramCongruence_one n Z
  right_inv Z := by
    change sourceGramCongruence n M (sourceGramCongruence n M⁻¹ Z) = Z
    rw [← sourceGramCongruence_mul]
    rw [Matrix.mul_nonsing_inv (A := M) hM]
    exact sourceGramCongruence_one n Z

@[simp]
theorem sourceGramCongruenceLinearEquivOfMatrix_apply
    (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : IsUnit M.det)
    (Z : Fin n → Fin n → ℂ) :
    sourceGramCongruenceLinearEquivOfMatrix n M hM Z =
      sourceGramCongruence n M Z := rfl

/-- Extend ordered full-frame determinant coordinates from embeddings to all
source-label functions by putting the non-injective functions to zero.  This
is the right coordinate model for Cauchy-Binet with ordered source frames:
the sum is over functions, not over all embeddings with duplicated orderings. -/
noncomputable def sourceFullFrameDetFunctionCoord
    (d n : ℕ)
    (δ : (Fin (d + 1) ↪ Fin n) → ℂ)
    (f : Fin (d + 1) → Fin n) : ℂ :=
  if hf : Function.Injective f then δ ⟨f, hf⟩ else 0

@[simp]
theorem sourceFullFrameDetFunctionCoord_of_injective
    (d n : ℕ)
    (δ : (Fin (d + 1) ↪ Fin n) → ℂ)
    {f : Fin (d + 1) → Fin n}
    (hf : Function.Injective f) :
    sourceFullFrameDetFunctionCoord d n δ f = δ ⟨f, hf⟩ := by
  simp [sourceFullFrameDetFunctionCoord, hf]

@[simp]
theorem sourceFullFrameDetFunctionCoord_of_not_injective
    (d n : ℕ)
    (δ : (Fin (d + 1) ↪ Fin n) → ℂ)
    {f : Fin (d + 1) → Fin n}
    (hf : ¬ Function.Injective f) :
    sourceFullFrameDetFunctionCoord d n δ f = 0 := by
  simp [sourceFullFrameDetFunctionCoord, hf]

@[simp]
theorem sourceFullFrameDetFunctionCoord_add
    (d n : ℕ)
    (δ ε : (Fin (d + 1) ↪ Fin n) → ℂ)
    (f : Fin (d + 1) → Fin n) :
    sourceFullFrameDetFunctionCoord d n (δ + ε) f =
      sourceFullFrameDetFunctionCoord d n δ f +
        sourceFullFrameDetFunctionCoord d n ε f := by
  by_cases hf : Function.Injective f <;>
    simp [sourceFullFrameDetFunctionCoord, hf]

@[simp]
theorem sourceFullFrameDetFunctionCoord_smul
    (d n : ℕ)
    (c : ℂ)
    (δ : (Fin (d + 1) ↪ Fin n) → ℂ)
    (f : Fin (d + 1) → Fin n) :
    sourceFullFrameDetFunctionCoord d n (c • δ) f =
      c * sourceFullFrameDetFunctionCoord d n δ f := by
  by_cases hf : Function.Injective f <;>
    simp [sourceFullFrameDetFunctionCoord, hf]

/-- Determinant-coordinate action induced by a source-label matrix.  This is
the Cauchy-Binet formula written as a function-indexed sum: non-injective
functions contribute zero via `sourceFullFrameDetFunctionCoord`, so the
identity matrix acts without overcounting ordered embeddings. -/
noncomputable def sourceFullFrameDetSourceMatrixTransform
    (d n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (δ : (Fin (d + 1) ↪ Fin n) → ℂ) :
    (Fin (d + 1) ↪ Fin n) → ℂ :=
  fun ι =>
    ∑ f : Fin (d + 1) → Fin n,
      (∏ a : Fin (d + 1), M (ι a) (f a)) *
        sourceFullFrameDetFunctionCoord d n δ f

theorem sourceFullFrameDetSourceMatrixTransform_one
    (d n : ℕ)
    (δ : (Fin (d + 1) ↪ Fin n) → ℂ) :
    sourceFullFrameDetSourceMatrixTransform d n 1 δ = δ := by
  funext ι
  rw [sourceFullFrameDetSourceMatrixTransform]
  let fι : Fin (d + 1) → Fin n := fun a => ι a
  rw [Finset.sum_eq_single fι]
  · have hcoord :
        sourceFullFrameDetFunctionCoord d n δ fι = δ ι := by
      have hfι : Function.Injective fι := by
        intro a b hab
        exact ι.injective hab
      have hι : (⟨fι, hfι⟩ : Fin (d + 1) ↪ Fin n) = ι := by
        ext a
        rfl
      rw [sourceFullFrameDetFunctionCoord_of_injective d n δ hfι]
      rw [hι]
    simp [fι, hcoord]
  · intro f _hf hne
    have hdiff : ∃ a : Fin (d + 1), f a ≠ ι a := by
      by_contra h
      apply hne
      funext a
      by_contra ha
      exact h ⟨a, ha⟩
    rcases hdiff with ⟨a, ha⟩
    have hprod :
        (∏ b : Fin (d + 1), (1 : Matrix (Fin n) (Fin n) ℂ) (ι b) (f b)) =
          0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ a)
      have hneq : ι a ≠ f a := fun h => ha h.symm
      simp [hneq]
    simp [hprod]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ fι))

/-- The determinant-coordinate source-matrix action is linear in the
determinant-coordinate data. -/
noncomputable def sourceFullFrameDetSourceMatrixTransformLinearMap
    (d n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    (((Fin (d + 1) ↪ Fin n) → ℂ) →ₗ[ℂ]
      ((Fin (d + 1) ↪ Fin n) → ℂ)) where
  toFun := sourceFullFrameDetSourceMatrixTransform d n M
  map_add' δ ε := by
    funext ι
    simp [sourceFullFrameDetSourceMatrixTransform,
      Finset.sum_add_distrib, mul_add]
  map_smul' c δ := by
    funext ι
    simp [sourceFullFrameDetSourceMatrixTransform, Finset.mul_sum,
      mul_left_comm]

@[simp]
theorem sourceFullFrameDetSourceMatrixTransformLinearMap_apply
    (d n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (δ : (Fin (d + 1) ↪ Fin n) → ℂ) :
    sourceFullFrameDetSourceMatrixTransformLinearMap d n M δ =
      sourceFullFrameDetSourceMatrixTransform d n M δ := rfl

/-- Source-label matrix action on the full oriented invariant coordinate
space: Gram coordinates transform by congruence, determinant coordinates by
the ordered function-indexed Cauchy-Binet transform. -/
noncomputable def sourceOrientedGramDataSourceMatrixTransform
    (d n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (G : SourceOrientedGramData d n) :
    SourceOrientedGramData d n :=
  (sourceGramCongruence n M G.gram,
    sourceFullFrameDetSourceMatrixTransform d n M G.det)

theorem sourceOrientedGramDataSourceMatrixTransform_one
    (d n : ℕ)
    (G : SourceOrientedGramData d n) :
    sourceOrientedGramDataSourceMatrixTransform d n 1 G = G := by
  apply SourceOrientedGramData.ext
  · exact sourceGramCongruence_one n G.gram
  · exact sourceFullFrameDetSourceMatrixTransform_one d n G.det

/-- Source Gram congruence is continuous in the Gram coordinate. -/
theorem continuous_sourceGramCongruence
    (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (sourceGramCongruence n M) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  continuity

/-- The function-coordinate extension is continuous in the ordered embedding
determinant-coordinate data. -/
theorem continuous_sourceFullFrameDetFunctionCoord
    (d n : ℕ)
    (f : Fin (d + 1) → Fin n) :
    Continuous (fun δ : (Fin (d + 1) ↪ Fin n) → ℂ =>
      sourceFullFrameDetFunctionCoord d n δ f) := by
  by_cases hfinj : Function.Injective f
  · simpa [sourceFullFrameDetFunctionCoord, hfinj] using
      (continuous_apply (⟨f, hfinj⟩ : Fin (d + 1) ↪ Fin n) :
        Continuous (fun δ : (Fin (d + 1) ↪ Fin n) → ℂ =>
          δ (⟨f, hfinj⟩ : Fin (d + 1) ↪ Fin n)))
  · simpa [sourceFullFrameDetFunctionCoord, hfinj] using
      (continuous_const : Continuous
        (fun _ : (Fin (d + 1) ↪ Fin n) → ℂ => (0 : ℂ)))

/-- The determinant-coordinate source-matrix transform is continuous in the
determinant-coordinate data. -/
theorem continuous_sourceFullFrameDetSourceMatrixTransform
    (d n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (sourceFullFrameDetSourceMatrixTransform d n M) := by
  apply continuous_pi
  intro ι
  simpa [sourceFullFrameDetSourceMatrixTransform] using
    (continuous_finset_sum
      (Finset.univ : Finset (Fin (d + 1) → Fin n))
      (fun f _hf =>
        continuous_const.mul
          (continuous_sourceFullFrameDetFunctionCoord d n f)))

/-- The full oriented source-coordinate source-matrix transform is continuous. -/
theorem continuous_sourceOrientedGramDataSourceMatrixTransform
    (d n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (sourceOrientedGramDataSourceMatrixTransform d n M) := by
  apply continuous_sourceOrientedGramData_mk
  · exact (continuous_sourceGramCongruence n M).comp
      (continuous_sourceOrientedGramData_gram (d := d) (n := n))
  · exact (continuous_sourceFullFrameDetSourceMatrixTransform d n M).comp
      (continuous_sourceOrientedGramData_det (d := d) (n := n))

/-- For determinant coordinates coming from an actual source tuple, the
function-coordinate extension is exactly the row-alternating determinant.
Non-injective source-label functions vanish by alternation. -/
theorem sourceFullFrameDetFunctionCoord_sourceFullFrameDet
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (f : Fin (d + 1) → Fin n) :
    sourceFullFrameDetFunctionCoord d n
        (fun κ => sourceFullFrameDet d n κ z) f =
      (Matrix.detRowAlternating :
          (Fin (d + 1) → ℂ) [⋀^Fin (d + 1)]→ₗ[ℂ] ℂ)
        (fun a => fun μ => z (f a) μ) := by
  by_cases hf : Function.Injective f
  · rw [sourceFullFrameDetFunctionCoord_of_injective d n
      (fun κ => sourceFullFrameDet d n κ z) hf]
    rfl
  · rw [sourceFullFrameDetFunctionCoord_of_not_injective d n
      (fun κ => sourceFullFrameDet d n κ z) hf]
    symm
    apply AlternatingMap.map_eq_zero_of_not_injective
    intro hrow
    apply hf
    intro a b hab
    apply hrow
    funext μ
    simp [hab]

/-- Cauchy-Binet for a source-label linear change, written in the
function-indexed determinant-coordinate model. -/
theorem sourceFullFrameDet_sourceTupleLinearChange
    (d n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (ι : Fin (d + 1) ↪ Fin n) :
    sourceFullFrameDet d n ι (sourceTupleLinearChange d n M z) =
      sourceFullFrameDetSourceMatrixTransform d n M
        (fun κ => sourceFullFrameDet d n κ z) ι := by
  let F :
      (Fin (d + 1) → ℂ) [⋀^Fin (d + 1)]→ₗ[ℂ] ℂ :=
    Matrix.detRowAlternating
  rw [sourceFullFrameDetSourceMatrixTransform]
  change
    F (fun a => fun μ => ∑ b : Fin n, M (ι a) b * z b μ) =
      ∑ f : Fin (d + 1) → Fin n,
        (∏ a : Fin (d + 1), M (ι a) (f a)) *
          sourceFullFrameDetFunctionCoord d n
            (fun κ => sourceFullFrameDet d n κ z) f
  calc
    F (fun a => fun μ => ∑ b : Fin n, M (ι a) b * z b μ)
        =
      F (fun a =>
          ∑ b : Fin n, M (ι a) b • (fun μ => z b μ)) := by
        congr 1
        ext a μ
        simp
    _ =
      ∑ f : Fin (d + 1) → Fin n,
        F (fun a => M (ι a) (f a) • (fun μ => z (f a) μ)) := by
        simpa using
          (F.toMultilinearMap.map_sum
            (g := fun a b => M (ι a) b • (fun μ => z b μ)))
    _ =
      ∑ f : Fin (d + 1) → Fin n,
        (∏ a : Fin (d + 1), M (ι a) (f a)) *
          F (fun a => fun μ => z (f a) μ) := by
        apply Finset.sum_congr rfl
        intro f _hf
        have hsmul :=
          F.toMultilinearMap.map_smul_univ
            (fun a : Fin (d + 1) => M (ι a) (f a))
            (fun a : Fin (d + 1) => fun μ => z (f a) μ)
        simpa using hsmul
    _ =
      ∑ f : Fin (d + 1) → Fin n,
        (∏ a : Fin (d + 1), M (ι a) (f a)) *
          sourceFullFrameDetFunctionCoord d n
            (fun κ => sourceFullFrameDet d n κ z) f := by
        apply Finset.sum_congr rfl
        intro f _hf
        rw [sourceFullFrameDetFunctionCoord_sourceFullFrameDet]

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

/-- Source-label linear changes transport the full oriented source invariant
by the Gram congruence and function-indexed determinant transform. -/
theorem sourceOrientedMinkowskiInvariant_sourceTupleLinearChange
    (d n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceOrientedMinkowskiInvariant d n
        (sourceTupleLinearChange d n M z) =
      sourceOrientedGramDataSourceMatrixTransform d n M
        (sourceOrientedMinkowskiInvariant d n z) := by
  apply SourceOrientedGramData.ext
  · exact sourceMinkowskiGram_sourceTupleLinearChange d n M z
  · funext ι
    exact sourceFullFrameDet_sourceTupleLinearChange d n M z ι

/-- The source-matrix oriented coordinate transform preserves the oriented
source variety.  This is the safe variety-level statement: no invertibility of
the determinant-coordinate transform on arbitrary non-alternating ordered-frame
coordinates is asserted. -/
theorem sourceOrientedGramDataSourceMatrixTransform_mem_variety
    (d n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n) :
    sourceOrientedGramDataSourceMatrixTransform d n M G ∈
      sourceOrientedGramVariety d n := by
  rcases hG with ⟨z, hz⟩
  refine ⟨sourceTupleLinearChange d n M z, ?_⟩
  rw [← hz]
  exact sourceOrientedMinkowskiInvariant_sourceTupleLinearChange d n M z

/-- Source-matrix transport as a self-map of the oriented source variety
subtype. -/
noncomputable def sourceOrientedGramVarietySourceMatrixMap
    (d n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    {G : SourceOrientedGramData d n // G ∈ sourceOrientedGramVariety d n} →
      {G : SourceOrientedGramData d n // G ∈ sourceOrientedGramVariety d n} :=
  fun G =>
    ⟨sourceOrientedGramDataSourceMatrixTransform d n M G.1,
      sourceOrientedGramDataSourceMatrixTransform_mem_variety d n M G.2⟩

/-- Invertible source matrices act by equivalences on the oriented source
variety.  The proof is variety-level: it uses tuple-level inverse source
changes, avoiding any false claim that the function-indexed ordered determinant
coordinate transform is invertible on all independent coordinates. -/
noncomputable def sourceOrientedGramVarietySourceMatrixEquivOfMatrix
    (d n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : IsUnit M.det) :
    {G : SourceOrientedGramData d n // G ∈ sourceOrientedGramVariety d n} ≃
      {G : SourceOrientedGramData d n // G ∈ sourceOrientedGramVariety d n} where
  toFun := sourceOrientedGramVarietySourceMatrixMap d n M
  invFun := sourceOrientedGramVarietySourceMatrixMap d n M⁻¹
  left_inv G := by
    rcases G with ⟨G, hG⟩
    rcases hG with ⟨z, hz⟩
    apply Subtype.ext
    change
      sourceOrientedGramDataSourceMatrixTransform d n M⁻¹
        (sourceOrientedGramDataSourceMatrixTransform d n M G) = G
    rw [← hz]
    rw [← sourceOrientedMinkowskiInvariant_sourceTupleLinearChange d n M z]
    rw [← sourceOrientedMinkowskiInvariant_sourceTupleLinearChange d n M⁻¹
      (sourceTupleLinearChange d n M z)]
    rw [← sourceTupleLinearChange_mul]
    rw [Matrix.nonsing_inv_mul (A := M) hM]
    rw [sourceTupleLinearChange_one]
  right_inv G := by
    rcases G with ⟨G, hG⟩
    rcases hG with ⟨z, hz⟩
    apply Subtype.ext
    change
      sourceOrientedGramDataSourceMatrixTransform d n M
        (sourceOrientedGramDataSourceMatrixTransform d n M⁻¹ G) = G
    rw [← hz]
    rw [← sourceOrientedMinkowskiInvariant_sourceTupleLinearChange d n M⁻¹ z]
    rw [← sourceOrientedMinkowskiInvariant_sourceTupleLinearChange d n M
      (sourceTupleLinearChange d n M⁻¹ z)]
    rw [← sourceTupleLinearChange_mul]
    rw [Matrix.mul_nonsing_inv (A := M) hM]
    rw [sourceTupleLinearChange_one]

/-- Invertible source matrices act homeomorphically on the oriented source
variety subtype.  This is the topological form of the safe variety-level
transport. -/
noncomputable def sourceOrientedGramVarietySourceMatrixHomeomorphOfMatrix
    (d n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : IsUnit M.det) :
    {G : SourceOrientedGramData d n // G ∈ sourceOrientedGramVariety d n} ≃ₜ
      {G : SourceOrientedGramData d n // G ∈ sourceOrientedGramVariety d n} where
  toEquiv := sourceOrientedGramVarietySourceMatrixEquivOfMatrix d n M hM
  continuous_toFun := by
    change Continuous
      (fun G :
        {G : SourceOrientedGramData d n // G ∈ sourceOrientedGramVariety d n} =>
          sourceOrientedGramVarietySourceMatrixMap d n M G)
    apply Continuous.subtype_mk
    exact (continuous_sourceOrientedGramDataSourceMatrixTransform d n M).comp
      continuous_subtype_val
  continuous_invFun := by
    change Continuous
      (fun G :
        {G : SourceOrientedGramData d n // G ∈ sourceOrientedGramVariety d n} =>
          sourceOrientedGramVarietySourceMatrixMap d n M⁻¹ G)
    apply Continuous.subtype_mk
    exact (continuous_sourceOrientedGramDataSourceMatrixTransform d n M⁻¹).comp
      continuous_subtype_val

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

/-- Invertible source-label changes preserve the maximal oriented source-rank
predicate through the safe oriented coordinate transform. -/
theorem sourceOrientedGramDataSourceMatrixTransform_maxRank_iff
    (d n : ℕ)
    {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : IsUnit M.det)
    (G : SourceOrientedGramData d n) :
    SourceOrientedMaxRankAt d n
        (sourceOrientedGramDataSourceMatrixTransform d n M G) ↔
      SourceOrientedMaxRankAt d n G := by
  change
    sourceGramMatrixRank n (sourceGramCongruence n M G.gram) =
        min (d + 1) n ↔
      sourceGramMatrixRank n G.gram = min (d + 1) n
  rw [sourceGramMatrixRank_sourceGramCongruence n hM]

/-- Invertible source matrices give the variety-relative transport interface. -/
noncomputable def sourceOrientedVarietySourceMatrixTransportEquivOfMatrix
    (d n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : IsUnit M.det) :
    SourceOrientedVarietyTransportEquiv d n where
  toHomeomorph :=
    sourceOrientedGramVarietySourceMatrixHomeomorphOfMatrix d n M hM
  maxRank_iff := by
    intro G
    simpa [sourceOrientedGramVarietySourceMatrixHomeomorphOfMatrix,
      sourceOrientedGramVarietySourceMatrixEquivOfMatrix,
      sourceOrientedGramVarietySourceMatrixMap] using
      sourceOrientedGramDataSourceMatrixTransform_maxRank_iff d n hM G.1

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

/-- Every exceptional oriented source point admits an invertible source-label
change whose oriented invariant is the canonical Hall-Wightman Lemma-3 source
invariant.  The proof first replaces the source realization by an adapted
representative, then selects a nonzero principal rank minor, Schur-reduces the
permuted scalar Gram matrix, normalizes the invertible head block to the
signature head metric, and finally uses the checked Witt-extension theorem to
remove the remaining Lorentz ambiguity. -/
theorem sourceOriented_lowRank_exists_normalFormSourceMatrix_to_canonical
    (d n : ℕ)
    {G0 : SourceOrientedGramData d n}
    (hG0 : G0 ∈ sourceOrientedGramVariety d n)
    (hlow : ¬ SourceOrientedMaxRankAt d n G0) :
    ∃ (r : ℕ) (_ : r < d + 1) (_ : r ≤ n)
      (M : Matrix (Fin n) (Fin n) ℂ),
        IsUnit M.det ∧
          sourceOrientedGramDataSourceMatrixTransform d n M G0 =
            sourceOrientedMinkowskiInvariant d n
              (hwLemma3CanonicalSource d n r) := by
  classical
  rcases sourceOriented_lowRank_exists_adaptedRepresentative
      d n hG0 hlow with
    ⟨z0, hz0, hadapt⟩
  let G : Fin n → Fin n → ℂ := sourceMinkowskiGram d n z0
  let r : ℕ := sourceGramMatrixRank n G
  have hrD : r < d + 1 := by
    have hlow_z0 :
        ¬ SourceOrientedMaxRankAt d n
          (sourceOrientedMinkowskiInvariant d n z0) := by
      intro hmax
      exact hlow (by simpa [hz0] using hmax)
    simpa [r, G] using
      sourceOriented_notMaxRank_sourceGramMatrixRank_lt_fullFrame
        d n z0 hlow_z0
  have hrn : r ≤ n := by
    simpa [r, G] using sourceGramMatrixRank_le_arity n G
  have hGsym : G ∈ sourceSymmetricMatrixSpace n := by
    intro i j
    exact sourceMinkowskiGram_symm d n z0 i j
  have hGrank : (Matrix.of fun i j : Fin n => G i j).rank = r := by
    change sourceGramMatrixRank n G = r
    rfl
  rcases exists_sourcePrincipalMinor_ne_zero_of_sourceSymmetricRank
      (n := n) (r := r) (Z := G) hGsym hGrank with
    ⟨I, hI, hminor⟩
  rcases exists_sourcePermutation_movingPrincipalBlockToHead
      n r hrn hI with
    ⟨σ, hσ⟩
  let Gp : Fin n → Fin n → ℂ := sourcePermuteComplexGram n σ G
  have hGpsym : Gp ∈ sourceSymmetricMatrixSpace n :=
    sourcePermuteComplexGram_mem_sourceSymmetricMatrixSpace n σ hGsym
  let A : Matrix (Fin r) (Fin r) ℂ := sourceHeadHeadBlock n r hrn Gp
  let B : Matrix (Fin (n - r)) (Fin r) ℂ := sourceTailHeadBlock n r hrn Gp
  let C : Matrix (Fin (n - r)) (Fin (n - r)) ℂ :=
    sourceTailTailBlock n r hrn Gp
  have hBlock :
      sourcePermuteComplexGram n σ G = sourceBlockMatrix n r hrn A B C := by
    simpa [Gp, A, B, C] using
      (sourceBlockMatrix_of_headTailBlocks n r hrn Gp hGpsym).symm
  have hA_det_eq : A.det = sourceMatrixMinor n r I I G := by
    change Matrix.det (sourceHeadHeadBlock n r hrn Gp) =
      sourceMatrixMinor n r I I G
    have hmat :
        sourceHeadHeadBlock n r hrn Gp =
          fun a b : Fin r => G (I a) (I b) := by
      ext a b
      simp [sourceHeadHeadBlock, Gp, sourcePermuteComplexGram, hσ a, hσ b]
    rw [hmat]
    rfl
  have hA : IsUnit A.det := by
    apply isUnit_iff_ne_zero.mpr
    rw [hA_det_eq]
    exact hminor
  have hAsym : A.transpose = A := by
    simpa [A] using
      sourceHeadHeadBlock_symm_of_sourceSymmetric n r hrn hGpsym
  have hRankGp : sourceGramMatrixRank n Gp = r := by
    simpa [Gp, r] using
      sourceGramMatrixRank_sourcePermuteComplexGram n σ G
  have hSchur : C - B * A⁻¹ * B.transpose = 0 := by
    exact hwLemma3_schurComplement_eq_zero_of_rank_eq
      n r hrn hGpsym hBlock hRankGp hA
  rcases complexSymmetric_invertible_congruence_to_sourceHeadMetric
      d r hrD hAsym hA with
    ⟨P, hPunit, hP⟩
  let M : Matrix (Fin n) (Fin n) ℂ :=
    hwLemma3_normalFormSourceChangeMatrix n r hrn σ A B P
  have hMunit : IsUnit M.det := by
    simpa [M] using
      hwLemma3_normalFormSourceChangeMatrix_det_isUnit
        n r hrn σ hA hPunit
  have hGram :
      sourceGramCongruence n M G =
        hwLemma3CanonicalGram d n r hrD hrn := by
    simpa [M, Gp, A, B, C] using
      hwLemma3_normalFormSourceChangeMatrix_canonicalGram
        d n r hrD hrn hBlock hA hAsym hSchur hP
  rcases
      hwLemma3_normalFormSourceChange_exists_complexLorentz_to_canonicalSource_of_adapted
        d n r hrD hrn (σ := σ) (A := A) (B := B) (P := P)
        hA hPunit hGram (by simpa [G] using hadapt) with
    ⟨Λ, hΛ⟩
  refine ⟨r, hrD, hrn, M, hMunit, ?_⟩
  have htransport :
      sourceOrientedGramDataSourceMatrixTransform d n M G0 =
        sourceOrientedMinkowskiInvariant d n
          (sourceTupleLinearChange d n M z0) := by
    rw [← hz0]
    exact
      (sourceOrientedMinkowskiInvariant_sourceTupleLinearChange
        d n M z0).symm
  have hcanon :
      sourceOrientedMinkowskiInvariant d n
          (hwLemma3CanonicalSource d n r) =
        sourceOrientedMinkowskiInvariant d n
          (sourceTupleLinearChange d n M z0) := by
    rw [← hΛ]
    exact sourceOrientedMinkowskiInvariant_complexLorentzAction Λ
      (sourceTupleLinearChange d n M z0)
  exact htransport.trans hcanon.symm

/-- The canonical Lemma-3 source point as a point of the oriented source
variety subtype. -/
noncomputable def hwLemma3CanonicalSourceOrientedVariety
    (d n r : ℕ) : SourceOrientedVariety d n :=
  ⟨sourceOrientedMinkowskiInvariant d n (hwLemma3CanonicalSource d n r),
    ⟨hwLemma3CanonicalSource d n r, rfl⟩⟩

/-- Variety-transport form of the exceptional normal-form theorem.  It is the
shape consumed by the rank-deficient local-image producer: the normal chart is
built at the canonical Lemma-3 source point, and the inverse
variety-relative source-matrix transport carries that canonical center back to
the original exceptional point. -/
theorem sourceOriented_lowRank_exists_normalFormVarietyTransport_from_canonical
    (d n : ℕ)
    {G0 : SourceOrientedGramData d n}
    (hG0 : G0 ∈ sourceOrientedGramVariety d n)
    (hlow : ¬ SourceOrientedMaxRankAt d n G0) :
    ∃ (r : ℕ) (_ : r < d + 1) (_ : r ≤ n)
      (T : SourceOrientedVarietyTransportEquiv d n),
        (T.invFun (hwLemma3CanonicalSourceOrientedVariety d n r)).1 =
          G0 := by
  classical
  rcases sourceOriented_lowRank_exists_normalFormSourceMatrix_to_canonical
      d n hG0 hlow with
    ⟨r, hrD, hrn, M, hM, hMcanon⟩
  let T : SourceOrientedVarietyTransportEquiv d n :=
    sourceOrientedVarietySourceMatrixTransportEquivOfMatrix d n M hM
  refine ⟨r, hrD, hrn, T, ?_⟩
  have hto :
      T.toFun ⟨G0, hG0⟩ =
        hwLemma3CanonicalSourceOrientedVariety d n r := by
    apply Subtype.ext
    simpa [T, SourceOrientedVarietyTransportEquiv.toFun,
      sourceOrientedVarietySourceMatrixTransportEquivOfMatrix,
      sourceOrientedGramVarietySourceMatrixHomeomorphOfMatrix,
      sourceOrientedGramVarietySourceMatrixEquivOfMatrix,
      sourceOrientedGramVarietySourceMatrixMap,
      hwLemma3CanonicalSourceOrientedVariety] using hMcanon
  have hleft := T.left_inv ⟨G0, hG0⟩
  rw [hto] at hleft
  exact congrArg Subtype.val hleft

end BHW
