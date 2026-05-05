import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedHeadGauge
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedSchurPropagation

/-!
# Source-oriented head-gauge support lemmas

This small companion specializes the checked Schur determinant propagation
theorems to the local head-gauge interface.  These are the finite-dimensional
facts consumed by the remaining local Witt/head-normal-form producer: once the
selected head block lies in a signature-relative gauge chart, the head rows are
linearly independent, and max-rank source-variety points have a nonzero
selected head-tail full-frame determinant.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- A local head gauge makes the actual selected head rows linearly
independent for every realizing source tuple. -/
theorem sourceHeadRows_linearIndependent_of_headGauge
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hz : G = sourceOrientedMinkowskiInvariant d n z) :
    LinearIndependent ℂ (fun a : Fin r => z (finSourceHead hrn a)) := by
  have hA : IsUnit (sourceOrientedSchurHeadBlock n r hrn G).det :=
    sourceOrientedSchurHeadBlock_det_isUnit_of_headGauge
      d n r hrD hrn hGvar Head hHead
  subst G
  exact sourceHeadRows_linearIndependent_of_schurHeadBlock_isUnit
    d n r hrn z (by simpa using hA)

/-- Head-gauge specialization of the all-zero head-tail determinant
contrapositive: if every selected head-tail determinant vanishes, the point is
not in the max-rank stratum. -/
theorem sourceOrientedGramVariety_notMaxRank_of_headGauge_headTailDet_eq_zero
    (d n r : ℕ)
    (hn : d + 1 ≤ n)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    (hzero :
      ∀ lam : Fin (d + 1 - r) ↪ Fin (n - r),
        G.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) = 0) :
    ¬ SourceOrientedMaxRankAt d n G := by
  exact
    sourceOrientedGramVariety_notMaxRank_of_headTailDet_eq_zero
      d n r hn hrD hrn hGvar
      (sourceOrientedSchurHeadBlock_det_isUnit_of_headGauge
        d n r hrD hrn hGvar Head hHead)
      hzero

/-- At a max-rank source-variety point with a local head gauge, some selected
head-tail full-frame determinant is nonzero. -/
theorem exists_headTail_fullFrameDet_ne_zero_of_headGauge_maxRank
    (d n r : ℕ)
    (hn : d + 1 ≤ n)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    (hmax : SourceOrientedMaxRankAt d n G) :
    ∃ lam : Fin (d + 1 - r) ↪ Fin (n - r),
      G.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) ≠ 0 := by
  by_contra hnone
  have hzero :
      ∀ lam : Fin (d + 1 - r) ↪ Fin (n - r),
        G.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) = 0 := by
    intro lam
    by_contra hne
    exact hnone ⟨lam, hne⟩
  exact
    (sourceOrientedGramVariety_notMaxRank_of_headGauge_headTailDet_eq_zero
      d n r hn hrD hrn hGvar Head hHead hzero) hmax

/-- Head-gauge specialization of determinant propagation from selected
head-tail determinants. -/
theorem sourceOrientedGramVariety_det_eq_of_gram_eq_headTailDet_eq_of_headGauge
    (d n r : ℕ)
    (hn : d + 1 ≤ n)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G H : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (hHvar : H ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    (hgram : H.gram = G.gram)
    (hheadTail :
      ∀ lam : Fin (d + 1 - r) ↪ Fin (n - r),
        H.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) =
          G.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam)) :
    H.det = G.det :=
  sourceOrientedGramVariety_det_eq_of_gram_eq_headTailDet_eq
    d n r hn hrD hrn hGvar hHvar
    (sourceOrientedSchurHeadBlock_det_isUnit_of_headGauge
      d n r hrD hrn hGvar Head hHead)
    hgram hheadTail

/-- Full oriented-data equality from ordinary Gram equality and selected
head-tail determinant equality, specialized to a source point in a local head
gauge. -/
theorem sourceOrientedGramData_eq_of_gram_eq_headTailDet_eq_of_headGauge
    (d n r : ℕ)
    (hn : d + 1 ≤ n)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {G H : SourceOrientedGramData d n}
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (hHvar : H ∈ sourceOrientedGramVariety d n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    (hHead : sourceOrientedSchurHeadBlockSymm d n r hrD hrn hGvar ∈ Head.U)
    (hgram : H.gram = G.gram)
    (hheadTail :
      ∀ lam : Fin (d + 1 - r) ↪ Fin (n - r),
        H.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam) =
          G.det (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam)) :
    H = G := by
  apply SourceOrientedGramData.ext
  · exact hgram
  · exact
      sourceOrientedGramVariety_det_eq_of_gram_eq_headTailDet_eq_of_headGauge
        d n r hn hrD hrn hGvar hHvar Head hHead hgram hheadTail

end BHW
