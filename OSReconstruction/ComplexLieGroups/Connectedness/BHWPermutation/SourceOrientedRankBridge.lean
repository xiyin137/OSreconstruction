import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedContinuation

/-!
# Rank bridges for oriented source data

This file connects the oriented max-rank predicate used by the strict
BHW/Jost route with the existing scalar source-rank API.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d n : ℕ}

/-- Oriented maximal rank depends only on the ordinary Gram coordinate. -/
theorem sourceOrientedMaxRankAt_iff_of_gram_eq
    {G H : SourceOrientedGramData d n}
    (hgram : G.gram = H.gram) :
    SourceOrientedMaxRankAt d n G ↔
      SourceOrientedMaxRankAt d n H := by
  change
    sourceGramMatrixRank n G.gram = min (d + 1) n ↔
      sourceGramMatrixRank n H.gram = min (d + 1) n
  rw [hgram]

/-- Oriented exceptional rank depends only on the ordinary Gram coordinate,
once both points are known to lie in the oriented source variety. -/
theorem sourceOrientedExceptionalRank_iff_of_gram_eq
    {G H : SourceOrientedGramData d n}
    (hgram : G.gram = H.gram)
    (hGvar : G ∈ sourceOrientedGramVariety d n)
    (hHvar : H ∈ sourceOrientedGramVariety d n) :
    SourceOrientedExceptionalRank d n G ↔
      SourceOrientedExceptionalRank d n H := by
  have hmax :
      SourceOrientedMaxRankAt d n G ↔
        SourceOrientedMaxRankAt d n H :=
    sourceOrientedMaxRankAt_iff_of_gram_eq (d := d) (n := n) hgram
  simp [SourceOrientedExceptionalRank, hGvar, hHvar, hmax]

/-- The scalar source Gram rank of an actual source configuration is bounded
by the spacetime/source minimum. -/
theorem sourceGramMatrixRank_le_spacetime_source_min
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceGramMatrixRank n (sourceMinkowskiGram d n z) ≤
      min (d + 1) n := by
  let M := LinearMap.range (sourceCoefficientEval d n z)
  have hle_n : Module.finrank ℂ M ≤ n := by
    simpa [M] using finrank_range_sourceCoefficientEval_le d n z
  have hle_d1 : Module.finrank ℂ M ≤ d + 1 := by
    have h := Submodule.finrank_le M
    simpa [M, Module.finrank_fin_fun] using h
  have hrank_le_M : restrictedMinkowskiRank d M ≤ Module.finrank ℂ M := by
    simp [restrictedMinkowskiRank]
  rw [sourceGramMatrixRank_eq_restrictedMinkowskiRank_range]
  exact le_min (le_trans hrank_le_M hle_d1) (le_trans hrank_le_M hle_n)

/-- On actual source configurations, oriented max-rank equality is equivalent
to the older scalar max-rank `≤` predicate. -/
theorem sourceOrientedMaxRankAt_invariant_iff_hwSourceGramMaxRankAt
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    SourceOrientedMaxRankAt d n
        (sourceOrientedMinkowskiInvariant d n z) ↔
      HWSourceGramMaxRankAt d n z := by
  constructor
  · intro h
    simpa [SourceOrientedMaxRankAt, HWSourceGramMaxRankAt,
      HWSourceGramMaxRank, sourceOrientedMinkowskiInvariant,
      SourceOrientedGramData.gram] using h.ge
  · intro h
    have hle :
        sourceGramMatrixRank n (sourceMinkowskiGram d n z) ≤
          min (d + 1) n :=
      sourceGramMatrixRank_le_spacetime_source_min d n z
    have hge :
        min (d + 1) n ≤
          sourceGramMatrixRank n (sourceMinkowskiGram d n z) := by
      simpa [HWSourceGramMaxRankAt, HWSourceGramMaxRank] using h
    exact le_antisymm hle hge

/-- Transport oriented max-rank between source configurations with the same
oriented invariant, expressed through the scalar max-rank API. -/
theorem hwSourceGramMaxRankAt_of_sourceOrientedInvariant_eq
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hz : HWSourceGramMaxRankAt d n z)
    (hzw :
      sourceOrientedMinkowskiInvariant d n z =
        sourceOrientedMinkowskiInvariant d n w) :
    HWSourceGramMaxRankAt d n w := by
  have hz_oriented :
      SourceOrientedMaxRankAt d n
        (sourceOrientedMinkowskiInvariant d n z) :=
    (sourceOrientedMaxRankAt_invariant_iff_hwSourceGramMaxRankAt
      d n z).2 hz
  have hw_oriented :
      SourceOrientedMaxRankAt d n
        (sourceOrientedMinkowskiInvariant d n w) :=
    SourceOrientedMaxRankAt_of_invariant_eq
      (d := d) (n := n) hz_oriented hzw
  exact
    (sourceOrientedMaxRankAt_invariant_iff_hwSourceGramMaxRankAt
      d n w).1 hw_oriented

/-- On actual source configurations, oriented exceptional rank is equivalent
to the older scalar exceptional-rank predicate. -/
theorem sourceOrientedExceptionalRank_invariant_iff_hwSourceGramExceptionalRankAt
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    SourceOrientedExceptionalRank d n
        (sourceOrientedMinkowskiInvariant d n z) ↔
      HWSourceGramExceptionalRankAt d n z := by
  rw [sourceOrientedExceptionalRank_iff_not_maxRank]
  rw [sourceOrientedMaxRankAt_invariant_iff_hwSourceGramMaxRankAt]
  exact (hwSourceGram_exceptionalRank_iff_not_maxRank d n).symm
  exact ⟨z, rfl⟩

/-- Transport scalar exceptional rank between source configurations with the
same oriented invariant. -/
theorem hwSourceGramExceptionalRankAt_of_sourceOrientedInvariant_eq
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hz : HWSourceGramExceptionalRankAt d n z)
    (hzw :
      sourceOrientedMinkowskiInvariant d n z =
        sourceOrientedMinkowskiInvariant d n w) :
    HWSourceGramExceptionalRankAt d n w := by
  have hz_oriented :
      SourceOrientedExceptionalRank d n
        (sourceOrientedMinkowskiInvariant d n z) :=
    (sourceOrientedExceptionalRank_invariant_iff_hwSourceGramExceptionalRankAt
      d n z).2 hz
  have hz_not :
      ¬ SourceOrientedMaxRankAt d n
        (sourceOrientedMinkowskiInvariant d n z) :=
    hz_oriented.2
  have hw_not :
      ¬ SourceOrientedMaxRankAt d n
        (sourceOrientedMinkowskiInvariant d n w) := by
    intro hw
    exact hz_not
      (SourceOrientedMaxRankAt_of_invariant_eq
        (d := d) (n := n) hw hzw.symm)
  have hw_oriented :
      SourceOrientedExceptionalRank d n
        (sourceOrientedMinkowskiInvariant d n w) :=
    ⟨⟨w, rfl⟩, hw_not⟩
  exact
    (sourceOrientedExceptionalRank_invariant_iff_hwSourceGramExceptionalRankAt
      d n w).1 hw_oriented

end BHW
