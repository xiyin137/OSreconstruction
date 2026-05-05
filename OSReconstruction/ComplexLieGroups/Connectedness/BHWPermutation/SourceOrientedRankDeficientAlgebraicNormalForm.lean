import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceNormalFormTransport

/-!
# Rank-deficient algebraic normal-form data

This file packages the checked exceptional-to-canonical normal-form theorem in
the exact data shape consumed by the source-oriented rank-deficient local-image
producer.  The transport is variety-relative: source-matrix determinant
coordinates are only transported on actual oriented source invariants.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Algebraic normal-form data for an exceptional point of the oriented source
variety.  The canonical Lemma-3 source point is the normal-chart center, and
`varietyTransport.invFun` moves that center back to the original point. -/
structure SourceOrientedRankDeficientAlgebraicNormalFormData
    (d n : ℕ)
    (G0 : SourceOrientedGramData d n) where
  r : ℕ
  hrD : r < d + 1
  hrn : r ≤ n
  varietyTransport : SourceOrientedVarietyTransportEquiv d n
  canonical_to_original :
    (varietyTransport.invFun
      (hwLemma3CanonicalSourceOrientedVariety d n r)).1 = G0

/-- Construct the algebraic normal-form data for an exceptional oriented
source-variety point. -/
noncomputable def sourceOriented_rankDeficient_algebraicNormalFormData
    (d n : ℕ)
    {G0 : SourceOrientedGramData d n}
    (hG0 : G0 ∈ sourceOrientedGramVariety d n)
    (hlow : ¬ SourceOrientedMaxRankAt d n G0) :
    SourceOrientedRankDeficientAlgebraicNormalFormData d n G0 := by
  classical
  let h :=
    sourceOriented_lowRank_exists_normalFormVarietyTransport_from_canonical
      d n hG0 hlow
  let r : ℕ := Classical.choose h
  let hrD : r < d + 1 := Classical.choose (Classical.choose_spec h)
  let h2 := Classical.choose_spec (Classical.choose_spec h)
  let hrn : r ≤ n := Classical.choose h2
  let h3 := Classical.choose_spec h2
  let T : SourceOrientedVarietyTransportEquiv d n := Classical.choose h3
  let hT := Classical.choose_spec h3
  exact
    { r := r
      hrD := hrD
      hrn := hrn
      varietyTransport := T
      canonical_to_original := hT }

end BHW
