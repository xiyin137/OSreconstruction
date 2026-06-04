import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientAlgebraicNormalForm
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedHeadGaugeNormal

/-!
# Canonical rank-deficient center support

This file records the center facts for the rank-deficient Schur local-image
producer.  At the canonical Lemma-3 source point, the selected Schur head
block is the signature head metric, so every local head gauge contains the
center and the checked Witt/head-normalization consumer can be instantiated.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- The selected Schur head block of the canonical Lemma-3 source point is the
signature head metric, as a point of the symmetric-matrix coordinate subtype. -/
theorem sourceOrientedSchurHeadBlockSymm_canonical
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n) :
    sourceOrientedSchurHeadBlockSymm d n r hrD hrn
        (hwLemma3CanonicalSourceOrientedVariety d n r).2 =
      sourceHeadMetricSymmCoord d r hrD := by
  apply Subtype.ext
  ext a b
  exact sourceMinkowskiGram_hwLemma3CanonicalSource_head d n r hrD hrn a b

/-- The canonical Lemma-3 source point lies in every local head-gauge
neighborhood centered at the signature head metric. -/
theorem hwLemma3CanonicalSource_headGauge_mem
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD) :
    sourceOrientedSchurHeadBlockSymm d n r hrD hrn
        (hwLemma3CanonicalSourceOrientedVariety d n r).2 ∈ Head.U := by
  rw [sourceOrientedSchurHeadBlockSymm_canonical]
  exact Head.center_mem

/-- The checked head-gauge normal-parameter data specialized to the canonical
Lemma-3 source center. -/
noncomputable def sourceOriented_canonical_headGaugeNormalParameterData
    [NeZero d]
    (hd : 2 ≤ d)
    (n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (Head : SourceRankDeficientHeadGaugeData d r hrD) :
    SourceOrientedHeadGaugeNormalParameterData d n r hrD hrn
      (hwLemma3CanonicalSourceOrientedVariety d n r).2 Head.toHeadFactorData :=
  sourceOriented_headGaugeNormalParameterData
    hd hrD hrn Head.toHeadFactorData
    (hwLemma3CanonicalSourceOrientedVariety d n r).2
    (hwLemma3CanonicalSource_headGauge_mem d n r hrD hrn Head)
    (z := hwLemma3CanonicalSource d n r)
    rfl

end BHW
