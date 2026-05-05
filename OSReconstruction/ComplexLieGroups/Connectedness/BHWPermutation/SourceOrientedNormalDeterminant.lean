import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedNormalParameter

/-!
# Determinant support for source-oriented normal parameters

This companion file keeps determinant-specific finite linear algebra separate
from the head/tail normal-parameter bookkeeping.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- The canonical equivalence between the head/tail sum index and the ambient
source-coordinate index. -/
def sourceHeadTailSumEquiv
    (d r : ℕ)
    (hrD : r < d + 1) :
    (Fin r ⊕ Fin (d + 1 - r)) ≃ Fin (d + 1) :=
  finSumFinEquiv.trans
    (finCongr (Nat.add_sub_of_le (Nat.le_of_lt hrD)))

@[simp]
theorem sourceHeadTailSumEquiv_inl
    (d r : ℕ)
    (hrD : r < d + 1)
    (a : Fin r) :
    sourceHeadTailSumEquiv d r hrD (Sum.inl a) =
      finSourceHead (Nat.le_of_lt hrD) a := by
  apply Fin.ext
  simp [sourceHeadTailSumEquiv, finSourceHead]

@[simp]
theorem sourceHeadTailSumEquiv_inr
    (d r : ℕ)
    (hrD : r < d + 1)
    (u : Fin (d + 1 - r)) :
    sourceHeadTailSumEquiv d r hrD (Sum.inr u) =
      finSourceTail (Nat.le_of_lt hrD) u := by
  apply Fin.ext
  simp [sourceHeadTailSumEquiv, finSourceTail]

@[simp]
theorem sourceOrientedNormalHeadVector_headCoord
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (a b : Fin r) :
    sourceOrientedNormalHeadVector d n r hrD hrn p a
        (finSourceHead (Nat.le_of_lt hrD) b) = p.head a b := by
  rw [sourceOrientedNormalHeadVector]
  rw [Finset.sum_eq_single b]
  · rw [hwLemma3CanonicalSource_head_head
      (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)]
    simp
  · intro c _hc hcb
    rw [hwLemma3CanonicalSource_head_head
      (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)]
    simp [hcb]
  · intro hb
    simp at hb

@[simp]
theorem sourceOrientedNormalHeadVector_tailCoord
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (a : Fin r)
    (u : Fin (d + 1 - r)) :
    sourceOrientedNormalHeadVector d n r hrD hrn p a
        (finSourceTail (Nat.le_of_lt hrD) u) = 0 := by
  rw [sourceOrientedNormalHeadVector]
  simp

theorem sourceFullFrameMatrix_normalParameter_headTail_blocks
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (lam : Fin (d + 1 - r) ↪ Fin (n - r)) :
    Matrix.reindex
        (sourceHeadTailSumEquiv d r hrD).symm
        (sourceHeadTailSumEquiv d r hrD).symm
        (sourceFullFrameMatrix d n
          (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam)
          (sourceOrientedNormalParameterVector d n r hrD hrn p)) =
      Matrix.fromBlocks
        p.head
        (0 : Matrix (Fin r) (Fin (d + 1 - r)) ℂ)
        ((p.mixed.submatrix lam id) * p.head)
        (fun u μ => p.tail (lam u) μ) := by
  ext row col
  cases row with
  | inl a =>
      cases col with
      | inl b =>
          simp [sourceFullFrameMatrix, sourceOrientedNormalParameterVector_head]
      | inr μ =>
          simp [sourceFullFrameMatrix, sourceOrientedNormalParameterVector_head]
  | inr u =>
      cases col with
      | inl b =>
          simp [sourceFullFrameMatrix, sourceOrientedNormalParameterVector_tail,
            Matrix.mul_apply]
      | inr μ =>
          simp [sourceFullFrameMatrix, sourceOrientedNormalParameterVector_tail]

theorem sourceFullFrameDet_normalParameter_headTail_raw
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (lam : Fin (d + 1 - r) ↪ Fin (n - r)) :
    sourceFullFrameDet d n
        (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam)
        (sourceOrientedNormalParameterVector d n r hrD hrn p) =
      p.head.det *
        Matrix.det (fun u μ : Fin (d + 1 - r) => p.tail (lam u) μ) := by
  have hblocks :=
    sourceFullFrameMatrix_normalParameter_headTail_blocks d n r hrD hrn p lam
  have hdet := congrArg Matrix.det hblocks
  rw [Matrix.det_reindex_self] at hdet
  simpa [sourceFullFrameDet] using hdet

end BHW
