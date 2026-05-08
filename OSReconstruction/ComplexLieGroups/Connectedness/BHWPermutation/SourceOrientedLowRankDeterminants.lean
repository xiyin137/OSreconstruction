import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexGlobalIdentity
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedFullFrame
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankBridge

/-!
# Low-rank determinant vanishing for oriented source data

This file records the finite-dimensional bridge used by the rank-deficient
normal-form route: below full spacetime source Gram rank, every ordered
full-frame determinant coordinate vanishes.  Consequently, in the low-rank
branch, same ordinary source Gram already implies equality of the full
oriented source invariant.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- The rank of an `n × n` source Gram coordinate is bounded by the source
arity. -/
theorem sourceGramMatrixRank_le_arity
    (n : ℕ)
    (Z : Fin n → Fin n → ℂ) :
    sourceGramMatrixRank n Z ≤ n := by
  simpa [sourceGramMatrixRank] using
    (Matrix.rank_le_width (A := Matrix.of fun i j : Fin n => Z i j))

/-- If the ordinary source Gram matrix has rank `< d + 1`, every selected
spacetime-size source frame has zero determinant. -/
theorem sourceFullFrameDet_eq_zero_of_sourceRank_lt
    (d n : ℕ)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hrank :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z) < d + 1)
    (ι : Fin (d + 1) ↪ Fin n) :
    sourceFullFrameDet d n ι z = 0 := by
  by_contra hdet
  let M := sourceFullFrameMatrix d n ι z
  have hGramDet :
      (Matrix.of (sourceFullFrameGram d M)).det ≠ 0 := by
    rw [sourceFullFrameGram_det_eq]
    exact mul_ne_zero (minkowskiMetricDet_ne_zero d) (pow_ne_zero 2 hdet)
  have hminor :
      Matrix.det
          (fun a b : Fin (d + 1) =>
            sourceMinkowskiGram d n z (ι a) (ι b)) ≠ 0 := by
    simpa [M, sourceFullFrameGram_sourceFullFrameMatrix] using hGramDet
  have hrank_ge :
      d + 1 ≤ sourceGramMatrixRank n (sourceMinkowskiGram d n z) := by
    have h :=
      matrix_rank_ge_of_nondegenerate_square_submatrix
        (A := Matrix.of fun i j : Fin n => sourceMinkowskiGram d n z i j)
        (I := ι) (J := ι) hminor
    simpa [sourceGramMatrixRank] using h
  exact (not_le_of_gt hrank) hrank_ge

/-- In the strict low-rank branch, equality of ordinary source Gram
coordinates implies equality of the full oriented source invariants.  The
determinant coordinates on both sides vanish by
`sourceFullFrameDet_eq_zero_of_sourceRank_lt`. -/
theorem sourceOrientedMinkowskiInvariant_eq_of_sameGram_rank_lt
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w)
    (hrank :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z) < d + 1) :
    sourceOrientedMinkowskiInvariant d n z =
      sourceOrientedMinkowskiInvariant d n w := by
  apply SourceOrientedGramData.ext
  · simpa [sourceOrientedMinkowskiInvariant, SourceOrientedGramData.gram]
      using hgram
  · funext ι
    have hzdet :
        sourceFullFrameDet d n ι z = 0 :=
      sourceFullFrameDet_eq_zero_of_sourceRank_lt d n hrank ι
    have hrank_w :
        sourceGramMatrixRank n (sourceMinkowskiGram d n w) < d + 1 := by
      simpa [hgram] using hrank
    have hwdet :
        sourceFullFrameDet d n ι w = 0 :=
      sourceFullFrameDet_eq_zero_of_sourceRank_lt d n hrank_w ι
    simp [sourceOrientedMinkowskiInvariant, SourceOrientedGramData.det,
      hzdet, hwdet]

end BHW
