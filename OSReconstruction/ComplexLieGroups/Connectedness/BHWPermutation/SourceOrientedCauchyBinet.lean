import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexGlobalIdentity
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedFullFrame

/-!
# Cauchy-Binet relations for oriented source invariants

This file records the forward determinant relation satisfied by actual
source tuples: the selected source Gram minor is the Minkowski metric
determinant times the two selected full-frame determinants.  This is one of
the finite algebraic equations later used to identify the oriented source
variety with its invariant-theoretic algebraic model.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Cauchy-Binet for two selected full-frame source matrices:
`det(Mι η Mκᵀ) = det(η) det(Mι) det(Mκ)`. -/
theorem sourceMatrixMinor_sourceMinkowskiGram_fullFrame
    (d n : ℕ)
    (ι κ : Fin (d + 1) ↪ Fin n)
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceMatrixMinor n (d + 1) ι κ (sourceMinkowskiGram d n z) =
      minkowskiMetricDet d * sourceFullFrameDet d n ι z *
        sourceFullFrameDet d n κ z := by
  let A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    sourceFullFrameMatrix d n ι z
  let B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    sourceFullFrameMatrix d n κ z
  have hmat :
      (fun a b : Fin (d + 1) => sourceMinkowskiGram d n z (ι a) (κ b)) =
        A * ComplexLorentzGroup.ηℂ (d := d) * B.transpose := by
    ext a b
    simp [A, B, sourceFullFrameMatrix, sourceMinkowskiGram,
      ComplexLorentzGroup.ηℂ, Matrix.diagonal, Matrix.mul_apply,
      MinkowskiSpace.metricSignature, minkowskiSignature,
      mul_left_comm, mul_comm]
  rw [sourceMatrixMinor]
  change
    Matrix.det
      (fun a b : Fin (d + 1) => sourceMinkowskiGram d n z (ι a) (κ b)) = _
  rw [hmat]
  simp [A, B, sourceFullFrameDet, minkowskiMetricDet, Matrix.det_mul,
    Matrix.det_transpose, mul_assoc, mul_left_comm, mul_comm]

/-- The same Cauchy-Binet equation written in oriented invariant
coordinates. -/
theorem sourceMatrixMinor_sourceOrientedInvariant_fullFrame
    (d n : ℕ)
    (ι κ : Fin (d + 1) ↪ Fin n)
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceMatrixMinor n (d + 1) ι κ
        (sourceOrientedMinkowskiInvariant d n z).gram =
      minkowskiMetricDet d *
        (sourceOrientedMinkowskiInvariant d n z).det ι *
        (sourceOrientedMinkowskiInvariant d n z).det κ := by
  simpa [sourceOrientedMinkowskiInvariant, SourceOrientedGramData.gram,
    SourceOrientedGramData.det] using
    sourceMatrixMinor_sourceMinkowskiGram_fullFrame d n ι κ z

/-- Reindexing a selected full frame multiplies its determinant by the sign of
the source-frame permutation. -/
theorem sourceFullFrameDet_reindex_selectedFrame
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (ρ : Equiv.Perm (Fin (d + 1)))
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceFullFrameDet d n (ρ.toEmbedding.trans ι) z =
      (ρ.sign : ℂ) * sourceFullFrameDet d n ι z := by
  unfold sourceFullFrameDet sourceFullFrameMatrix
  have hperm :=
    Matrix.det_permute ρ (fun a μ : Fin (d + 1) => z (ι a) μ)
  simpa [Matrix.submatrix, Function.comp_def, mul_comm] using hperm

/-- The same selected-frame alternation equation in oriented invariant
coordinates. -/
theorem sourceOrientedInvariant_det_reindex_selectedFrame
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (ρ : Equiv.Perm (Fin (d + 1)))
    (z : Fin n → Fin (d + 1) → ℂ) :
    (sourceOrientedMinkowskiInvariant d n z).det (ρ.toEmbedding.trans ι) =
      (ρ.sign : ℂ) * (sourceOrientedMinkowskiInvariant d n z).det ι := by
  simpa [sourceOrientedMinkowskiInvariant, SourceOrientedGramData.det] using
    sourceFullFrameDet_reindex_selectedFrame d n ι ρ z

end BHW
