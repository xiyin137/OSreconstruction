import Mathlib.Data.Fintype.Sort
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

/-- Shifted residual-tail oriented coordinates: the shifted Gram matrix and all
top residual-tail determinants. -/
structure SourceShiftedTailOrientedData
    (d r : ℕ)
    (hrD : r < d + 1)
    (m : ℕ) where
  gram : Matrix (Fin m) (Fin m) ℂ
  det : (Fin (d + 1 - r) ↪ Fin m) → ℂ

/-- The shifted-tail oriented invariant of a residual-tail source tuple. -/
def sourceShiftedTailOrientedInvariant
    (d r : ℕ)
    (hrD : r < d + 1)
    (m : ℕ)
    (q : Fin m → Fin (d + 1 - r) → ℂ) :
    SourceShiftedTailOrientedData d r hrD m where
  gram := sourceShiftedTailGram d r hrD m q
  det := fun lam => Matrix.det (fun u μ : Fin (d + 1 - r) => q (lam u) μ)

@[simp]
theorem sourceShiftedTailOrientedInvariant_gram
    (d r : ℕ)
    (hrD : r < d + 1)
    (m : ℕ)
    (q : Fin m → Fin (d + 1 - r) → ℂ) :
    (sourceShiftedTailOrientedInvariant d r hrD m q).gram =
      sourceShiftedTailGram d r hrD m q := by
  rfl

@[simp]
theorem sourceShiftedTailOrientedInvariant_det
    (d r : ℕ)
    (hrD : r < d + 1)
    (m : ℕ)
    (q : Fin m → Fin (d + 1 - r) → ℂ)
    (lam : Fin (d + 1 - r) ↪ Fin m) :
    (sourceShiftedTailOrientedInvariant d r hrD m q).det lam =
      Matrix.det (fun u μ : Fin (d + 1 - r) => q (lam u) μ) := by
  rfl

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

theorem sourceFullFrameDet_normalParameter_headTail
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (lam : Fin (d + 1 - r) ↪ Fin (n - r)) :
    sourceFullFrameDet d n
        (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam)
        (sourceOrientedNormalParameterVector d n r hrD hrn p) =
      p.head.det *
        (sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail).det lam := by
  simpa using
    sourceFullFrameDet_normalParameter_headTail_raw d n r hrD hrn p lam

/-- Matrix formed by adjoining an `(r + D) × r` block to an
`(r + D) × D` block.  The first `r` columns come from `M`; the remaining
`D` columns come from `Q`. -/
def matrixBlockColumns
    (r D : ℕ)
    (M : Matrix (Fin (r + D)) (Fin r) ℂ)
    (Q : Matrix (Fin (r + D)) (Fin D) ℂ) :
    Matrix (Fin (r + D)) (Fin (r + D)) ℂ :=
  fun i j =>
    if h : j.val < r then
      M i ⟨j.val, h⟩
    else
      Q i ⟨j.val - r, by omega⟩

@[simp]
theorem matrixRowSubset_compl_card
    (r D : ℕ)
    (s : Finset (Fin (r + D)))
    (hs : s.card = r) :
    sᶜ.card = D := by
  rw [Finset.card_compl, hs, Fintype.card_fin]
  omega

/-- The canonical increasing enumeration of a chosen `r`-row subset. -/
def matrixRowSubsetHeadRows
    (r D : ℕ)
    (s : Finset (Fin (r + D)))
    (hs : s.card = r) :
    Fin r ↪ Fin (r + D) :=
  (s.orderEmbOfFin hs).toEmbedding

/-- The canonical increasing enumeration of the complement of a chosen
`r`-row subset. -/
def matrixRowSubsetTailRows
    (r D : ℕ)
    (s : Finset (Fin (r + D)))
    (hs : s.card = r) :
    Fin D ↪ Fin (r + D) :=
  (sᶜ.orderEmbOfFin (matrixRowSubset_compl_card r D s hs)).toEmbedding

/-- The canonical row equivalence that puts a chosen row subset first and its
complement second, preserving the internal order on each part. -/
noncomputable def matrixRowSubsetSumEquiv
    (r D : ℕ)
    (s : Finset (Fin (r + D)))
    (hs : s.card = r) :
    Fin r ⊕ Fin D ≃ Fin (r + D) :=
  finSumEquivOfFinset (s := s) hs
    (matrixRowSubset_compl_card r D s hs)

@[simp]
theorem matrixRowSubsetSumEquiv_inl
    (r D : ℕ)
    (s : Finset (Fin (r + D)))
    (hs : s.card = r)
    (a : Fin r) :
    matrixRowSubsetSumEquiv r D s hs (Sum.inl a) =
      matrixRowSubsetHeadRows r D s hs a := by
  simp [matrixRowSubsetSumEquiv, matrixRowSubsetHeadRows]

@[simp]
theorem matrixRowSubsetSumEquiv_inr
    (r D : ℕ)
    (s : Finset (Fin (r + D)))
    (hs : s.card = r)
    (u : Fin D) :
    matrixRowSubsetSumEquiv r D s hs (Sum.inr u) =
      matrixRowSubsetTailRows r D s hs u := by
  simp [matrixRowSubsetSumEquiv, matrixRowSubsetTailRows]

/-- The row-shuffle sign in the finite Laplace expansion along the first
`r` columns and the last `D` columns. -/
noncomputable def matrixRowSubsetLaplaceSign
    (r D : ℕ)
    (s : Finset (Fin (r + D)))
    (hs : s.card = r) : ℂ :=
  ((Equiv.Perm.sign
    ((finSumFinEquiv : (Fin r ⊕ Fin D) ≃ Fin (r + D)).symm.trans
      (matrixRowSubsetSumEquiv r D s hs)) : ℤ) : ℂ)

/-- The summand attached to one ordered row subset in the finite Laplace
expansion of a block-column determinant. -/
noncomputable def matrixBlockColumnLaplaceTerm
    (r D : ℕ)
    (M : Matrix (Fin (r + D)) (Fin r) ℂ)
    (Q : Matrix (Fin (r + D)) (Fin D) ℂ)
    (S : {s : Finset (Fin (r + D)) // s.card = r}) : ℂ :=
  matrixRowSubsetLaplaceSign r D S.1 S.2 *
    Matrix.det
      (fun a b => M (matrixRowSubsetHeadRows r D S.1 S.2 a) b) *
    Matrix.det
      (fun a b => Q (matrixRowSubsetTailRows r D S.1 S.2 a) b)

/-- The finite row-subset Laplace sum for a block-column determinant. -/
noncomputable def matrixBlockColumnLaplaceSum
    (r D : ℕ)
    (M : Matrix (Fin (r + D)) (Fin r) ℂ)
    (Q : Matrix (Fin (r + D)) (Fin D) ℂ) : ℂ :=
  ∑ S : {s : Finset (Fin (r + D)) // s.card = r},
    matrixBlockColumnLaplaceTerm r D M Q S

/-- Head-column coefficients for an arbitrary ordered full frame in the
rank-deficient Schur normal form.  Selected head labels contribute standard
basis rows; tail labels contribute their stored mixed rows. -/
def sourceNormalFullFrameCoeff
    (d n r : ℕ)
    (hrn : r ≤ n)
    (L : Matrix (Fin (n - r)) (Fin r) ℂ)
    (ι : Fin (d + 1) ↪ Fin n) :
    Matrix (Fin (d + 1)) (Fin r) ℂ :=
  fun k a =>
    if hhead : ∃ b : Fin r, ι k = finSourceHead hrn b then
      if Classical.choose hhead = a then 1 else 0
    else
      let htail : ∃ u : Fin (n - r), ι k = finSourceTail hrn u :=
        (finSourceHead_tail_cases hrn (ι k)).resolve_left hhead
      L (Classical.choose htail) a

/-- The head-coordinate block of an arbitrary ordered full frame after applying
the chosen head factor. -/
def sourceNormalFullFrameHeadBlock
    (d n r : ℕ)
    (hrn : r ≤ n)
    (H : Matrix (Fin r) (Fin r) ℂ)
    (L : Matrix (Fin (n - r)) (Fin r) ℂ)
    (ι : Fin (d + 1) ↪ Fin n) :
    Matrix (Fin (d + 1)) (Fin r) ℂ :=
  sourceNormalFullFrameCoeff d n r hrn L ι * H

/-- The residual-tail coordinate block for an arbitrary ordered full frame.
Rows selected from tail source labels contribute the corresponding shifted-tail
coordinate row; rows selected from head labels contribute zero. -/
def sourceNormalFullFrameTailBlock
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (q : Fin (n - r) → Fin (d + 1 - r) → ℂ)
    (ι : Fin (d + 1) ↪ Fin n) :
    Matrix (Fin (d + 1)) (Fin (d + 1 - r)) ℂ :=
  let _ := hrD
  fun k μ =>
    if htail :
        ∃ u : Fin (n - r), ι k = finSourceTail hrn u then
      q (Classical.choose htail) μ
    else
      0

/-- Residual-tail determinant attached to a chosen set of rows of an arbitrary
ordered full frame.  It is zero unless all chosen rows are tail source labels. -/
def sourceNormalFullFrameTailRowsDet
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (T : SourceShiftedTailOrientedData d r hrD (n - r))
    (ι : Fin (d + 1) ↪ Fin n)
    (rows : Fin (d + 1 - r) ↪ Fin (d + 1)) : ℂ :=
  if htail :
      ∀ μ : Fin (d + 1 - r),
        ∃ u : Fin (n - r), ι (rows μ) = finSourceTail hrn u then
    T.det
      { toFun := fun μ => Classical.choose (htail μ)
        inj' := by
          intro μ ν hμν
          apply rows.injective
          apply ι.injective
          calc
            ι (rows μ) = finSourceTail hrn (Classical.choose (htail μ)) :=
              Classical.choose_spec (htail μ)
            _ = finSourceTail hrn (Classical.choose (htail ν)) := by
              simpa using congrArg (finSourceTail hrn) hμν
            _ = ι (rows ν) := (Classical.choose_spec (htail ν)).symm }
  else
    0

theorem sourceNormalFullFrameTailRowsDet_eq_det_tailBlock
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (q : Fin (n - r) → Fin (d + 1 - r) → ℂ)
    (ι : Fin (d + 1) ↪ Fin n)
    (rows : Fin (d + 1 - r) ↪ Fin (d + 1)) :
    Matrix.det
        (fun μ ν =>
          sourceNormalFullFrameTailBlock d n r hrD hrn q ι (rows μ) ν) =
      sourceNormalFullFrameTailRowsDet d n r hrD hrn
        (sourceShiftedTailOrientedInvariant d r hrD (n - r) q) ι rows := by
  unfold sourceNormalFullFrameTailRowsDet sourceNormalFullFrameTailBlock
    sourceShiftedTailOrientedInvariant
  by_cases htail :
      ∀ μ : Fin (d + 1 - r),
        ∃ u : Fin (n - r), ι (rows μ) = finSourceTail hrn u
  · simp [htail]
  · have hrow :
        ∃ μ : Fin (d + 1 - r),
          ¬ ∃ u : Fin (n - r), ι (rows μ) = finSourceTail hrn u := by
      simpa [not_forall] using htail
    rcases hrow with ⟨μ0, hμ0⟩
    rw [Matrix.det_eq_zero_of_row_eq_zero μ0]
    · simp [htail]
    · intro ν
      simp [hμ0]

/-- The Schur/Laplace determinant formula for an arbitrary ordered full frame,
expressed using the chosen head factor, mixed Schur coefficients, and
shifted-tail oriented determinant coordinates. -/
def sourceNormalFullFrameDetFromSchur
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (H : Matrix (Fin r) (Fin r) ℂ)
    (L : Matrix (Fin (n - r)) (Fin r) ℂ)
    (T : SourceShiftedTailOrientedData d r hrD (n - r))
    (ι : Fin (d + 1) ↪ Fin n) : ℂ :=
  ∑ S : {s : Finset (Fin (r + (d + 1 - r))) // s.card = r},
    matrixRowSubsetLaplaceSign r (d + 1 - r) S.1 S.2 *
      Matrix.det
        (fun a b =>
          sourceNormalFullFrameHeadBlock d n r hrn H L ι
            (Fin.cast (Nat.add_sub_of_le (Nat.le_of_lt hrD))
              (matrixRowSubsetHeadRows r (d + 1 - r) S.1 S.2 a)) b) *
      sourceNormalFullFrameTailRowsDet d n r hrD hrn T ι
        { toFun := fun μ =>
            Fin.cast (Nat.add_sub_of_le (Nat.le_of_lt hrD))
              (matrixRowSubsetTailRows r (d + 1 - r) S.1 S.2 μ)
          inj' := by
            intro μ ν hμν
            exact (matrixRowSubsetTailRows r (d + 1 - r) S.1 S.2).injective
              (Fin.cast_injective
                (Nat.add_sub_of_le (Nat.le_of_lt hrD)) hμν) }

end BHW
