import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedFullFrameChart
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedSchurResidual

/-!
# Source-oriented Schur determinant propagation

This companion file isolates the oriented determinant propagation theorem that
remains after the Schur residual packet has reduced the normal-form
reconstruction to head-tail determinant calibration.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Nonzero selected-head-tail branch of the oriented determinant propagation
theorem.  Once one selected `head ∪ lam` full-frame determinant is nonzero, the
checked full-frame chart identity theorem determines all determinant
coordinates from the selected full-frame coordinate and the mixed rows; both
are read from the ordinary Gram coordinate plus the calibrated selected
determinant. -/
theorem sourceOrientedGramVariety_det_eq_of_gram_eq_headTailDet_eq_of_exists_nonzero
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G H : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n)
    (hH : H ∈ sourceOrientedGramVariety d n)
    (hgram : H.gram = G.gram)
    (hheadTail :
      ∀ lam : Fin (d + 1 - r) ↪ Fin (n - r),
        H.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) =
          G.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam))
    (hNZ : ∃ lam : Fin (d + 1 - r) ↪ Fin (n - r),
      G.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) ≠ 0) :
    H.det = G.det := by
  rcases hNZ with ⟨lam, hdetG⟩
  let η := sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam
  have hsel :
      sourceFullFrameOrientedCoordOfSource d n η H =
        sourceFullFrameOrientedCoordOfSource d n η G := by
    ext a b
    · exact congrFun (congrFun hgram (η a)) (η b)
    · exact hheadTail lam
  have hmixed :
      sourceSelectedMixedRows d n η H =
        sourceSelectedMixedRows d n η G := by
    funext k a
    exact congrFun (congrFun hgram k.1) (η a)
  have hHG : H = G :=
    sourceOrientedGramData_eq_of_selectedCoord_eq_mixedRows_eq
      d n η hH hG hdetG hsel hmixed
  rw [hHG]

end BHW
