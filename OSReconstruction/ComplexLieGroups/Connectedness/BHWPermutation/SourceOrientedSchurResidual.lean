import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedNormalDeterminant

/-!
# Source-oriented Schur residual coordinates

This file records the rank-deficient Schur residual data used by the
source-oriented normal-parameter route.  It deliberately does not store the
full-frame determinant reconstruction theorem as data; that remains the
separate Plucker/Cauchy-Binet reconstruction step over the original oriented
datum.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Principal head block of the ordinary source Gram coordinate. -/
def sourceOrientedSchurHeadBlock
    (n r : ℕ)
    (hrn : r ≤ n)
    (G : SourceOrientedGramData d n) :
    Matrix (Fin r) (Fin r) ℂ :=
  fun a b => G.gram (finSourceHead hrn a) (finSourceHead hrn b)

@[simp]
theorem sourceOrientedSchurHeadBlock_apply
    (n r : ℕ)
    (hrn : r ≤ n)
    (G : SourceOrientedGramData d n)
    (a b : Fin r) :
    sourceOrientedSchurHeadBlock n r hrn G a b =
      G.gram (finSourceHead hrn a) (finSourceHead hrn b) := by
  rfl

/-- Tail/head mixed block of the ordinary source Gram coordinate. -/
def sourceOrientedSchurMixedBlock
    (n r : ℕ)
    (hrn : r ≤ n)
    (G : SourceOrientedGramData d n) :
    Matrix (Fin (n - r)) (Fin r) ℂ :=
  fun u a => G.gram (finSourceTail hrn u) (finSourceHead hrn a)

/-- Tail/tail block of the ordinary source Gram coordinate. -/
def sourceOrientedSchurTailBlock
    (n r : ℕ)
    (hrn : r ≤ n)
    (G : SourceOrientedGramData d n) :
    Matrix (Fin (n - r)) (Fin (n - r)) ℂ :=
  fun u v => G.gram (finSourceTail hrn u) (finSourceTail hrn v)

/-- Mixed coefficient matrix in the principal Schur chart. -/
def sourceSchurMixedCoeff
    (n r : ℕ)
    (hrn : r ≤ n)
    (G : SourceOrientedGramData d n)
    (A : Matrix (Fin r) (Fin r) ℂ) :
    Matrix (Fin (n - r)) (Fin r) ℂ :=
  sourceOrientedSchurMixedBlock n r hrn G * A⁻¹

/-- Residual Schur-complement Gram block in the principal Schur chart. -/
def sourceSchurComplement
    (n r : ℕ)
    (hrn : r ≤ n)
    (G : SourceOrientedGramData d n)
    (A : Matrix (Fin r) (Fin r) ℂ) :
    Matrix (Fin (n - r)) (Fin (n - r)) ℂ :=
  let L := sourceSchurMixedCoeff n r hrn G A
  sourceOrientedSchurTailBlock n r hrn G - L * A * L.transpose

/-- The Schur mixed coefficients recover the mixed Gram block after multiplying
back by the invertible principal head block. -/
theorem sourceSchurMixedCoeff_mul_headBlock
    (n r : ℕ)
    (hrn : r ≤ n)
    (G : SourceOrientedGramData d n)
    (A : Matrix (Fin r) (Fin r) ℂ)
    (hA : IsUnit A.det) :
    sourceSchurMixedCoeff n r hrn G A * A =
      sourceOrientedSchurMixedBlock n r hrn G := by
  rw [sourceSchurMixedCoeff, Matrix.mul_assoc, Matrix.nonsing_inv_mul A hA,
    Matrix.mul_one]

theorem sourceVectorMinkowskiInner_comm
    (d : ℕ)
    (x y : Fin (d + 1) → ℂ) :
    sourceVectorMinkowskiInner d x y =
      sourceVectorMinkowskiInner d y x := by
  simp [sourceVectorMinkowskiInner, mul_comm, mul_left_comm]

theorem sourceVectorMinkowskiInner_sub_left
    (d : ℕ)
    (x y z : Fin (d + 1) → ℂ) :
    sourceVectorMinkowskiInner d (fun μ => x μ - y μ) z =
      sourceVectorMinkowskiInner d x z -
        sourceVectorMinkowskiInner d y z := by
  simp only [sourceVectorMinkowskiInner]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro μ _hμ
  ring

theorem sourceVectorMinkowskiInner_sub_right
    (d : ℕ)
    (x y z : Fin (d + 1) → ℂ) :
    sourceVectorMinkowskiInner d x (fun μ => y μ - z μ) =
      sourceVectorMinkowskiInner d x y -
        sourceVectorMinkowskiInner d x z := by
  simp only [sourceVectorMinkowskiInner]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro μ _hμ
  ring

/-- Actual residual vector obtained by subtracting the Schur head projection
from an actual tail source vector. -/
def sourceActualSchurResidualVector
    (d n r : ℕ)
    (hrn : r ≤ n)
    (z : Fin n → Fin (d + 1) → ℂ)
    (L : Matrix (Fin (n - r)) (Fin r) ℂ)
    (u : Fin (n - r)) :
    Fin (d + 1) → ℂ :=
  fun μ =>
    z (finSourceTail hrn u) μ -
      ∑ a : Fin r, L u a * z (finSourceHead hrn a) μ

theorem sourceActualSchurResidualVector_decomp
    (d n r : ℕ)
    (hrn : r ≤ n)
    (z : Fin n → Fin (d + 1) → ℂ)
    (L : Matrix (Fin (n - r)) (Fin r) ℂ)
    (u : Fin (n - r)) :
    z (finSourceTail hrn u) =
      fun μ =>
        (∑ a : Fin r, L u a * z (finSourceHead hrn a) μ) +
          sourceActualSchurResidualVector d n r hrn z L u μ := by
  ext μ
  simp [sourceActualSchurResidualVector]

/-- Selected residual-tail full-frame determinant coordinates extracted from
the original oriented determinant coordinate and the chosen head factor. -/
def sourceSchurResidualDeterminants
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (G : SourceOrientedGramData d n)
    (headFactor : Matrix (Fin r) (Fin r) ℂ) :
    (Fin (d + 1 - r) ↪ Fin (n - r)) → ℂ :=
  fun lam =>
    G.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) /
      headFactor.det

/-- Shifted-tail oriented data lying on the shifted-tail source variety. -/
def sourceShiftedTailOrientedVariety
    (d r : ℕ)
    (hrD : r < d + 1)
    (m : ℕ) :
    Set (SourceShiftedTailOrientedData d r hrD m) :=
  Set.range (sourceShiftedTailOrientedInvariant d r hrD m)

/-- Schur residual data attached to an oriented source datum and a chosen
rank-deficient principal head block. -/
structure SourceOrientedSchurResidualData
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (G : SourceOrientedGramData d n) where
  A : Matrix (Fin r) (Fin r) ℂ
  A_eq : A = sourceOrientedSchurHeadBlock n r hrn G
  A_unit : IsUnit A.det
  headFactor : Matrix (Fin r) (Fin r) ℂ
  headFactor_gram :
    headFactor * sourceHeadMetric d r hrD * headFactor.transpose = A
  headFactor_det_unit : IsUnit headFactor.det
  L : Matrix (Fin (n - r)) (Fin r) ℂ
  L_eq : L = sourceSchurMixedCoeff n r hrn G A
  tail : SourceShiftedTailOrientedData d r hrD (n - r)
  tail_gram_eq : tail.gram = sourceSchurComplement n r hrn G A
  tail_det_eq :
    tail.det = sourceSchurResidualDeterminants d n r hrD hrn G headFactor
  tail_mem : tail ∈ sourceShiftedTailOrientedVariety d r hrD (n - r)

/-- Residual-data specialization of
`sourceSchurMixedCoeff_mul_headBlock`. -/
theorem SourceOrientedSchurResidualData.L_mul_A
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n}
    {G : SourceOrientedGramData d n}
    (R : SourceOrientedSchurResidualData d n r hrD hrn G) :
    R.L * R.A = sourceOrientedSchurMixedBlock n r hrn G := by
  rw [R.L_eq]
  exact sourceSchurMixedCoeff_mul_headBlock n r hrn G R.A R.A_unit

theorem sourceActualSchurResidualVector_inner_head
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (z : Fin n → Fin (d + 1) → ℂ)
    (R :
      SourceOrientedSchurResidualData d n r hrD hrn
        (sourceOrientedMinkowskiInvariant d n z))
    (u : Fin (n - r))
    (a : Fin r) :
    sourceVectorMinkowskiInner d
        (sourceActualSchurResidualVector d n r hrn z R.L u)
        (z (finSourceHead hrn a)) = 0 := by
  change
    sourceVectorMinkowskiInner d
        (fun μ =>
          z (finSourceTail hrn u) μ -
            ∑ b : Fin r, R.L u b * z (finSourceHead hrn b) μ)
        (z (finSourceHead hrn a)) = 0
  rw [sourceVectorMinkowskiInner_sub_left, sourceVectorMinkowskiInner_sum_left]
  simp_rw [sourceVectorMinkowskiInner_smul_left]
  have hsum :
      (∑ b : Fin r,
          R.L u b *
            sourceVectorMinkowskiInner d
              (z (finSourceHead hrn b)) (z (finSourceHead hrn a))) =
        (R.L * R.A) u a := by
    simp [Matrix.mul_apply, R.A_eq, sourceOrientedSchurHeadBlock,
      sourceOrientedMinkowskiInvariant, SourceOrientedGramData.gram,
      sourceMinkowskiGram, sourceVectorMinkowskiInner]
  have hentry :
      (R.L * R.A) u a =
        sourceVectorMinkowskiInner d
          (z (finSourceTail hrn u)) (z (finSourceHead hrn a)) := by
    have hLA := R.L_mul_A
    simpa [sourceOrientedSchurMixedBlock, sourceOrientedMinkowskiInvariant,
      SourceOrientedGramData.gram, sourceMinkowskiGram,
      sourceVectorMinkowskiInner] using
        congrFun (congrFun hLA u) a
  rw [hsum, hentry]
  ring

theorem sourceActualSchurResidualVector_head_inner
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (z : Fin n → Fin (d + 1) → ℂ)
    (R :
      SourceOrientedSchurResidualData d n r hrD hrn
        (sourceOrientedMinkowskiInvariant d n z))
    (a : Fin r)
    (u : Fin (n - r)) :
    sourceVectorMinkowskiInner d
        (z (finSourceHead hrn a))
        (sourceActualSchurResidualVector d n r hrn z R.L u) = 0 := by
  rw [sourceVectorMinkowskiInner_comm]
  exact sourceActualSchurResidualVector_inner_head d n r hrD hrn z R u a

/-- The actual Schur residual vectors have Gram matrix equal to the stored
residual-tail Schur complement. -/
theorem sourceActualSchurResidualVector_inner_residual
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (z : Fin n → Fin (d + 1) → ℂ)
    (R :
      SourceOrientedSchurResidualData d n r hrD hrn
        (sourceOrientedMinkowskiInvariant d n z))
    (u v : Fin (n - r)) :
    sourceVectorMinkowskiInner d
        (sourceActualSchurResidualVector d n r hrn z R.L u)
        (sourceActualSchurResidualVector d n r hrn z R.L v) =
      R.tail.gram u v := by
  have hproj_zero :
      sourceVectorMinkowskiInner d
          (fun μ =>
            ∑ a : Fin r,
              R.L u a * z (finSourceHead hrn a) μ)
          (sourceActualSchurResidualVector d n r hrn z R.L v) = 0 := by
    rw [sourceVectorMinkowskiInner_sum_left]
    simp_rw [sourceVectorMinkowskiInner_smul_left]
    simp_rw [sourceActualSchurResidualVector_head_inner]
    simp
  have hleft :
      sourceVectorMinkowskiInner d
          (z (finSourceTail hrn u))
          (sourceActualSchurResidualVector d n r hrn z R.L v) =
        sourceVectorMinkowskiInner d
          (sourceActualSchurResidualVector d n r hrn z R.L u)
          (sourceActualSchurResidualVector d n r hrn z R.L v) := by
    rw [sourceActualSchurResidualVector_decomp d n r hrn z R.L u]
    rw [sourceVectorMinkowskiInner_add_left, hproj_zero]
    simp
  have hsum :
      (∑ b : Fin r,
          R.L v b *
            sourceVectorMinkowskiInner d
              (z (finSourceTail hrn u))
              (z (finSourceHead hrn b))) =
        (R.L * R.A * R.Lᵀ) u v := by
    have hLA := R.L_mul_A
    have hentry : ∀ b : Fin r,
        sourceVectorMinkowskiInner d
              (z (finSourceTail hrn u))
              (z (finSourceHead hrn b)) =
          (R.L * R.A) u b := by
      intro b
      have h := congrFun (congrFun hLA u) b
      simpa [sourceOrientedSchurMixedBlock, sourceOrientedMinkowskiInvariant,
        SourceOrientedGramData.gram, sourceMinkowskiGram,
        sourceVectorMinkowskiInner] using h.symm
    simp_rw [hentry]
    simp [Matrix.mul_apply, Matrix.transpose_apply, mul_comm]
  have htail :
      R.tail.gram u v =
        sourceVectorMinkowskiInner d
          (z (finSourceTail hrn u))
          (z (finSourceTail hrn v)) -
        (R.L * R.A * R.Lᵀ) u v := by
    have h := congrFun (congrFun R.tail_gram_eq u) v
    simpa [sourceSchurComplement, sourceOrientedSchurTailBlock,
      R.L_eq, sourceOrientedMinkowskiInvariant, SourceOrientedGramData.gram,
      sourceMinkowskiGram, sourceVectorMinkowskiInner, Matrix.sub_apply] using h
  calc
    sourceVectorMinkowskiInner d
        (sourceActualSchurResidualVector d n r hrn z R.L u)
        (sourceActualSchurResidualVector d n r hrn z R.L v)
        = sourceVectorMinkowskiInner d
            (z (finSourceTail hrn u))
            (sourceActualSchurResidualVector d n r hrn z R.L v) := hleft.symm
    _ = sourceVectorMinkowskiInner d
            (z (finSourceTail hrn u))
            (z (finSourceTail hrn v)) -
          (∑ b : Fin r,
            R.L v b *
              sourceVectorMinkowskiInner d
                (z (finSourceTail hrn u))
                (z (finSourceHead hrn b))) := by
          change
            sourceVectorMinkowskiInner d
              (z (finSourceTail hrn u))
              (fun μ =>
                z (finSourceTail hrn v) μ -
                  ∑ b : Fin r,
                    R.L v b * z (finSourceHead hrn b) μ) = _
          rw [sourceVectorMinkowskiInner_sub_right]
          rw [sourceVectorMinkowskiInner_sum_right]
          simp_rw [sourceVectorMinkowskiInner_smul_right]
    _ = sourceVectorMinkowskiInner d
            (z (finSourceTail hrn u))
            (z (finSourceTail hrn v)) -
          (R.L * R.A * R.Lᵀ) u v := by
          rw [hsum]
    _ = R.tail.gram u v := htail.symm

/-- The selected original head-tail full-frame matrix, reindexed by the
head/tail row and column split. -/
def sourceActualSchurSelectedOriginalMatrix
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (z : Fin n → Fin (d + 1) → ℂ)
    (lam : Fin (d + 1 - r) ↪ Fin (n - r)) :
    Matrix (Fin r ⊕ Fin (d + 1 - r)) (Fin r ⊕ Fin (d + 1 - r)) ℂ :=
  Matrix.reindex
    (sourceHeadTailSumEquiv d r hrD).symm
    (sourceHeadTailSumEquiv d r hrD).symm
    (sourceFullFrameMatrix d n
      (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) z)

/-- The selected head-tail full-frame matrix after replacing the selected tail
rows by their actual Schur residual vectors. -/
def sourceActualSchurSelectedResidualMatrix
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (z : Fin n → Fin (d + 1) → ℂ)
    (L : Matrix (Fin (n - r)) (Fin r) ℂ)
    (lam : Fin (d + 1 - r) ↪ Fin (n - r)) :
    Matrix (Fin r ⊕ Fin (d + 1 - r)) (Fin r ⊕ Fin (d + 1 - r)) ℂ :=
  fun row col =>
    match row with
    | Sum.inl a =>
        z (finSourceHead hrn a) (sourceHeadTailSumEquiv d r hrD col)
    | Sum.inr u =>
        sourceActualSchurResidualVector d n r hrn z L (lam u)
          (sourceHeadTailSumEquiv d r hrD col)

/-- Block lower-triangular row operation subtracting the Schur head projection
from the selected tail rows. -/
def sourceSchurHeadTailRowOperation
    (d n r : ℕ)
    (_hrD : r < d + 1)
    (_hrn : r ≤ n)
    (L : Matrix (Fin (n - r)) (Fin r) ℂ)
    (lam : Fin (d + 1 - r) ↪ Fin (n - r)) :
    Matrix (Fin r ⊕ Fin (d + 1 - r)) (Fin r ⊕ Fin (d + 1 - r)) ℂ :=
  Matrix.fromBlocks
    (1 : Matrix (Fin r) (Fin r) ℂ)
    (0 : Matrix (Fin r) (Fin (d + 1 - r)) ℂ)
    (fun u a => - L (lam u) a)
    (1 : Matrix (Fin (d + 1 - r)) (Fin (d + 1 - r)) ℂ)

theorem sourceSchurHeadTailRowOperation_det
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (L : Matrix (Fin (n - r)) (Fin r) ℂ)
    (lam : Fin (d + 1 - r) ↪ Fin (n - r)) :
    (sourceSchurHeadTailRowOperation d n r hrD hrn L lam).det = 1 := by
  rw [sourceSchurHeadTailRowOperation]
  rw [Matrix.det_fromBlocks_zero₁₂]
  simp

theorem sourceActualSchurSelectedResidualMatrix_eq_rowOperation_mul
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (z : Fin n → Fin (d + 1) → ℂ)
    (L : Matrix (Fin (n - r)) (Fin r) ℂ)
    (lam : Fin (d + 1 - r) ↪ Fin (n - r)) :
    sourceActualSchurSelectedResidualMatrix d n r hrD hrn z L lam =
      sourceSchurHeadTailRowOperation d n r hrD hrn L lam *
        sourceActualSchurSelectedOriginalMatrix d n r hrD hrn z lam := by
  ext row col
  cases row with
  | inl a =>
      simp [sourceActualSchurSelectedResidualMatrix,
        sourceSchurHeadTailRowOperation,
        sourceActualSchurSelectedOriginalMatrix,
        sourceFullFrameMatrix, Matrix.mul_apply, Matrix.one_apply]
  | inr u =>
      simp [sourceActualSchurSelectedResidualMatrix,
        sourceSchurHeadTailRowOperation,
        sourceActualSchurSelectedOriginalMatrix,
        sourceFullFrameMatrix, sourceActualSchurResidualVector,
        Matrix.mul_apply, Matrix.one_apply]
      ring

/-- Selected head-tail determinant is unchanged when selected tail rows are
replaced by their actual Schur residuals. -/
theorem sourceActualSchurResidual_selectedFrameDet
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (z : Fin n → Fin (d + 1) → ℂ)
    (L : Matrix (Fin (n - r)) (Fin r) ℂ)
    (lam : Fin (d + 1 - r) ↪ Fin (n - r)) :
    (sourceActualSchurSelectedResidualMatrix d n r hrD hrn z L lam).det =
      sourceFullFrameDet d n
        (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) z := by
  have hmat :=
    sourceActualSchurSelectedResidualMatrix_eq_rowOperation_mul
      d n r hrD hrn z L lam
  calc
    (sourceActualSchurSelectedResidualMatrix d n r hrD hrn z L lam).det
        = (sourceSchurHeadTailRowOperation d n r hrD hrn L lam *
            sourceActualSchurSelectedOriginalMatrix d n r hrD hrn z lam).det := by
          rw [hmat]
    _ = (sourceSchurHeadTailRowOperation d n r hrD hrn L lam).det *
          (sourceActualSchurSelectedOriginalMatrix d n r hrD hrn z lam).det := by
          rw [Matrix.det_mul]
    _ = (sourceActualSchurSelectedOriginalMatrix d n r hrD hrn z lam).det := by
          rw [sourceSchurHeadTailRowOperation_det]
          simp
    _ = sourceFullFrameDet d n
        (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) z := by
          rw [sourceActualSchurSelectedOriginalMatrix, sourceFullFrameDet]
          rw [Matrix.det_reindex_self]

/-- Selected actual residual determinants are calibrated by the stored
shifted-tail determinant coordinates and the chosen head factor. -/
theorem sourceActualSchurResidual_selectedFrameDet_eq_headFactor_mul_tail_det
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (z : Fin n → Fin (d + 1) → ℂ)
    (R : SourceOrientedSchurResidualData d n r hrD hrn
      (sourceOrientedMinkowskiInvariant d n z))
    (lam : Fin (d + 1 - r) ↪ Fin (n - r)) :
    (sourceActualSchurSelectedResidualMatrix d n r hrD hrn z R.L lam).det =
      R.headFactor.det * R.tail.det lam := by
  rw [sourceActualSchurResidual_selectedFrameDet]
  have htail :
      R.tail.det lam =
        sourceFullFrameDet d n
          (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) z /
          R.headFactor.det := by
    simpa [sourceSchurResidualDeterminants, sourceOrientedMinkowskiInvariant,
      SourceOrientedGramData.det] using congrFun R.tail_det_eq lam
  rw [htail]
  field_simp [R.headFactor_det_unit.ne_zero]

/-- The normal Schur parameter realizes the ordinary Gram coordinates.  The
range hypothesis is needed because arbitrary product-coordinate `G.gram` need
not be symmetric. -/
theorem sourceOrientedNormalParameterVector_realizes_schur_gram
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (R : SourceOrientedSchurResidualData d n r hrD hrn G)
    {p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn}
    (hhead : p.head = R.headFactor)
    (hmixed : p.mixed = R.L)
    (htail :
      sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail = R.tail) :
    (sourceOrientedMinkowskiInvariant d n
      (sourceOrientedNormalParameterVector d n r hrD hrn p)).gram = G.gram := by
  rcases hGvar with ⟨z, rfl⟩
  funext i j
  rcases finSourceHead_tail_cases hrn i with ⟨a, hi⟩ | ⟨u, hi⟩
  · rcases finSourceHead_tail_cases hrn j with ⟨b, hj⟩ | ⟨v, hj⟩
    · rw [hi, hj]
      change
        sourceVectorMinkowskiInner d
            (sourceOrientedNormalParameterVector d n r hrD hrn p
              (finSourceHead hrn a))
            (sourceOrientedNormalParameterVector d n r hrD hrn p
              (finSourceHead hrn b)) =
          sourceMinkowskiGram d n z (finSourceHead hrn a)
            (finSourceHead hrn b)
      rw [sourceOrientedNormalParameterVector_head,
        sourceOrientedNormalParameterVector_head,
        sourceVectorMinkowskiInner_sourceOrientedNormalHeadVector]
      rw [hhead, R.headFactor_gram, R.A_eq]
      rfl
    · rw [hi, hj]
      change
        sourceVectorMinkowskiInner d
            (sourceOrientedNormalParameterVector d n r hrD hrn p
              (finSourceHead hrn a))
            (sourceOrientedNormalParameterVector d n r hrD hrn p
              (finSourceTail hrn v)) =
          sourceMinkowskiGram d n z (finSourceHead hrn a)
            (finSourceTail hrn v)
      rw [sourceVectorMinkowskiInner_comm]
      rw [sourceOrientedNormalParameterVector_head,
        sourceVectorMinkowskiInner_tailParameterVector_head]
      rw [hhead, hmixed, R.headFactor_gram]
      have hLA := R.L_mul_A
      have hentry :
          (R.L * R.A) v a =
            sourceMinkowskiGram d n z (finSourceTail hrn v)
              (finSourceHead hrn a) := by
        simpa [sourceOrientedSchurMixedBlock] using
          congrFun (congrFun hLA v) a
      rw [sourceMinkowskiGram_symm d n z (finSourceHead hrn a)
        (finSourceTail hrn v)]
      exact hentry
  · rcases finSourceHead_tail_cases hrn j with ⟨a, hj⟩ | ⟨v, hj⟩
    · rw [hi, hj]
      change
        sourceVectorMinkowskiInner d
            (sourceOrientedNormalParameterVector d n r hrD hrn p
              (finSourceTail hrn u))
            (sourceOrientedNormalParameterVector d n r hrD hrn p
              (finSourceHead hrn a)) =
          sourceMinkowskiGram d n z (finSourceTail hrn u)
            (finSourceHead hrn a)
      rw [sourceOrientedNormalParameterVector_head,
        sourceVectorMinkowskiInner_tailParameterVector_head]
      rw [hhead, hmixed, R.headFactor_gram]
      have hLA := R.L_mul_A
      simpa [sourceOrientedSchurMixedBlock] using
        congrFun (congrFun hLA u) a
    · rw [hi, hj]
      change
        sourceVectorMinkowskiInner d
            (sourceOrientedNormalParameterVector d n r hrD hrn p
              (finSourceTail hrn u))
            (sourceOrientedNormalParameterVector d n r hrD hrn p
              (finSourceTail hrn v)) =
          sourceMinkowskiGram d n z (finSourceTail hrn u)
            (finSourceTail hrn v)
      rw [sourceVectorMinkowskiInner_tailParameterVector_tail]
      rw [hhead, hmixed, R.headFactor_gram]
      have htailGram :
          sourceShiftedTailGram d r hrD (n - r) p.tail = R.tail.gram := by
        simpa using congrArg SourceShiftedTailOrientedData.gram htail
      rw [htailGram, R.tail_gram_eq]
      simp [sourceSchurComplement, sourceOrientedSchurTailBlock, R.L_eq,
        sourceOrientedMinkowskiInvariant, SourceOrientedGramData.gram]

/-- On selected head-tail full frames, the Schur determinant formula collapses
to the chosen head determinant times the stored residual-tail determinant. -/
theorem sourceNormalFullFrameDetFromSchur_headTail
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (R : SourceOrientedSchurResidualData d n r hrD hrn G)
    (lam : Fin (d + 1 - r) ↪ Fin (n - r)) :
    sourceNormalFullFrameDetFromSchur d n r hrD hrn
        R.headFactor R.L R.tail
        (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) =
      R.headFactor.det * R.tail.det lam := by
  rcases R.tail_mem with ⟨q, hq⟩
  let p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn :=
    { head := R.headFactor
      mixed := R.L
      tail := q }
  have hschur :=
    sourceFullFrameDet_normalParameter_eq_schurFormula
      d n r hrD hrn p
      (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam)
  have hheadTail :=
    sourceFullFrameDet_normalParameter_headTail d n r hrD hrn p lam
  simpa [p, hq] using hschur.symm.trans hheadTail

/-- The selected head-tail specialization agrees with the corresponding stored
determinant coordinate of the original oriented datum. -/
theorem sourceNormalFullFrameDetFromSchur_headTail_eq_source_det
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (R : SourceOrientedSchurResidualData d n r hrD hrn G)
    (lam : Fin (d + 1 - r) ↪ Fin (n - r)) :
    sourceNormalFullFrameDetFromSchur d n r hrD hrn
        R.headFactor R.L R.tail
        (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) =
      G.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) := by
  rw [sourceNormalFullFrameDetFromSchur_headTail]
  have htail :
      R.tail.det lam =
        G.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) /
          R.headFactor.det := by
    simpa [sourceSchurResidualDeterminants] using
      congrFun R.tail_det_eq lam
  rw [htail]
  field_simp [R.headFactor_det_unit.ne_zero]

/-- Mechanical Schur determinant reconstruction from a separate oriented
head-tail determinant propagation theorem on the source-oriented variety.  The
hard input `hprop` is the genuine Plucker/Cauchy-Binet propagation step. -/
theorem sourceOrientedSchur_fullFrameDet_reconstruct_of_headTailPropagation
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (hprop :
      ∀ {G H : SourceOrientedGramData d n},
        G ∈ sourceOrientedGramVariety d n →
        H ∈ sourceOrientedGramVariety d n →
        IsUnit (sourceOrientedSchurHeadBlock n r hrn G).det →
        H.gram = G.gram →
        (∀ lam : Fin (d + 1 - r) ↪ Fin (n - r),
          H.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) =
            G.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam)) →
        H.det = G.det)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (R : SourceOrientedSchurResidualData d n r hrD hrn G)
    (ι : Fin (d + 1) ↪ Fin n) :
    sourceNormalFullFrameDetFromSchur d n r hrD hrn
        R.headFactor R.L R.tail ι = G.det ι := by
  rcases R.tail_mem with ⟨q, hq⟩
  let p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn :=
    { head := R.headFactor
      mixed := R.L
      tail := q }
  let H : SourceOrientedGramData d n :=
    sourceOrientedMinkowskiInvariant d n
      (sourceOrientedNormalParameterVector d n r hrD hrn p)
  have hHvar : H ∈ sourceOrientedGramVariety d n := by
    exact ⟨sourceOrientedNormalParameterVector d n r hrD hrn p, rfl⟩
  have hAunit : IsUnit (sourceOrientedSchurHeadBlock n r hrn G).det := by
    rw [← R.A_eq]
    exact R.A_unit
  have hgram : H.gram = G.gram := by
    exact sourceOrientedNormalParameterVector_realizes_schur_gram
      d n r hrD hrn hGvar R rfl rfl (by simpa [p] using hq)
  have hheadTail :
      ∀ lam : Fin (d + 1 - r) ↪ Fin (n - r),
        H.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) =
          G.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) := by
    intro lam
    change sourceFullFrameDet d n
        (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam)
        (sourceOrientedNormalParameterVector d n r hrD hrn p) = _
    calc
      sourceFullFrameDet d n
          (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam)
          (sourceOrientedNormalParameterVector d n r hrD hrn p)
          = sourceNormalFullFrameDetFromSchur d n r hrD hrn
              p.head p.mixed
              (sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail)
              (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) :=
            sourceFullFrameDet_normalParameter_eq_schurFormula
              d n r hrD hrn p
              (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam)
      _ = sourceNormalFullFrameDetFromSchur d n r hrD hrn
              R.headFactor R.L R.tail
              (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) := by
            simp [p, hq]
      _ = G.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) :=
            sourceNormalFullFrameDetFromSchur_headTail_eq_source_det
              d n r hrD hrn R lam
  have hdet : H.det = G.det :=
    hprop hGvar hHvar hAunit hgram hheadTail
  calc
    sourceNormalFullFrameDetFromSchur d n r hrD hrn
        R.headFactor R.L R.tail ι
        = sourceNormalFullFrameDetFromSchur d n r hrD hrn
            p.head p.mixed
            (sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail)
            ι := by
          simp [p, hq]
    _ = H.det ι := by
          change sourceNormalFullFrameDetFromSchur d n r hrD hrn
            p.head p.mixed
            (sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail) ι =
              sourceFullFrameDet d n ι
                (sourceOrientedNormalParameterVector d n r hrD hrn p)
          exact (sourceFullFrameDet_normalParameter_eq_schurFormula
            d n r hrD hrn p ι).symm
    _ = G.det ι := congrFun hdet ι

/-- Mechanical determinant-coordinate consumer for the normal-parameter Schur
route.  The hard input is the genuine full-frame reconstruction theorem over
the original oriented datum `G`, supplied as `hdet`. -/
theorem sourceOrientedNormalParameterVector_realizes_schur_det_of_fullFrameReconstruct
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (R : SourceOrientedSchurResidualData d n r hrD hrn G)
    {p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn}
    (hhead : p.head = R.headFactor)
    (hmixed : p.mixed = R.L)
    (htail :
      sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail = R.tail)
    (hdet :
      ∀ ι : Fin (d + 1) ↪ Fin n,
        sourceNormalFullFrameDetFromSchur d n r hrD hrn
          R.headFactor R.L R.tail ι = G.det ι) :
    (sourceOrientedMinkowskiInvariant d n
      (sourceOrientedNormalParameterVector d n r hrD hrn p)).det = G.det := by
  funext ι
  change
    sourceFullFrameDet d n ι
        (sourceOrientedNormalParameterVector d n r hrD hrn p) =
      G.det ι
  calc
    sourceFullFrameDet d n ι
        (sourceOrientedNormalParameterVector d n r hrD hrn p)
        = sourceNormalFullFrameDetFromSchur d n r hrD hrn
            p.head p.mixed
            (sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail)
            ι :=
          sourceFullFrameDet_normalParameter_eq_schurFormula
            d n r hrD hrn p ι
    _ = sourceNormalFullFrameDetFromSchur d n r hrD hrn
            R.headFactor R.L R.tail ι := by
          rw [hhead, hmixed, htail]
    _ = G.det ι := hdet ι

/-- Full oriented-data consumer for the normal-parameter Schur route, assuming
the remaining Plucker/Cauchy-Binet full-frame reconstruction theorem over
`G`. -/
theorem sourceOrientedNormalParameterVector_realizes_schur_of_fullFrameReconstruct
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (R : SourceOrientedSchurResidualData d n r hrD hrn G)
    {p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn}
    (hhead : p.head = R.headFactor)
    (hmixed : p.mixed = R.L)
    (htail :
      sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail = R.tail)
    (hdet :
      ∀ ι : Fin (d + 1) ↪ Fin n,
        sourceNormalFullFrameDetFromSchur d n r hrD hrn
          R.headFactor R.L R.tail ι = G.det ι) :
    sourceOrientedMinkowskiInvariant d n
      (sourceOrientedNormalParameterVector d n r hrD hrn p) = G := by
  apply SourceOrientedGramData.ext
  · exact
      sourceOrientedNormalParameterVector_realizes_schur_gram
        d n r hrD hrn hGvar R hhead hmixed htail
  · exact
      sourceOrientedNormalParameterVector_realizes_schur_det_of_fullFrameReconstruct
        d n r hrD hrn R hhead hmixed htail hdet

end BHW
