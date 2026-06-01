import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceHWSeparateResidualFrame

/-!
# Hall-Wightman source branch law

This file assembles the checked high-rank proper-orbit branch and the checked
separate-frame low-rank singular-contraction branch into the source-oriented
Hall-Wightman branch law used by the OS-II route.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

/-- Data-valued Hall-Wightman branch alternative for equal oriented source
invariants: either the endpoints are in the same proper complex-Lorentz orbit,
or the low-rank singular contraction data are available. -/
inductive HWSameSourceOrientedInvariantBranchData
    (d n : ℕ)
    (z w : Fin n → Fin (d + 1) → ℂ) : Type where
  | orbit
      (Λ : ComplexLorentzGroup d)
      (hΛ : w = complexLorentzAction Λ z) :
      HWSameSourceOrientedInvariantBranchData d n z w
  | singular
      (data : HWSameSourceGramSingularContractionData d n z w) :
      HWSameSourceOrientedInvariantBranchData d n z w

/-- Low scalar rank plus equal source Gram data produce the singular
contraction data required by the analytic limit consumer. -/
noncomputable def hw_sameSourceGram_singular_contractionData
    [NeZero d]
    (hd : 2 ≤ d)
    (n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ ExtendedTube d n)
    (hw : w ∈ ExtendedTube d n)
    (hlow : HWSourceGramLowRankAt d n z)
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w) :
    HWSameSourceGramSingularContractionData d n z w := by
  classical
  let Sdata : HWLowRankSelectedSpanFrameData d n z w :=
    hw_lowRank_selectedSpanFrame_of_sameSourceGram d n hgram
  have hproper : Sdata.r < d + 1 := by
    have hrank :
        Sdata.r =
          sourceGramMatrixRank n (sourceMinkowskiGram d n z) :=
      Sdata.rank_eq
    have hlt_d :
        sourceGramMatrixRank n (sourceMinkowskiGram d n z) < d :=
      lt_of_lt_of_le hlow (min_le_left d n)
    rw [hrank]
    exact lt_trans hlt_d (Nat.lt_succ_self d)
  let A :
      HWLowRankSelectedSpanAlignment
        d n Sdata.r z w Sdata.I Sdata.frame :=
    hw_lowRank_selectedSpanAlignment_of_selectedSpanFrame
      d n Sdata.r Sdata.frame hproper
  exact
    hw_sameSourceGram_singular_contractionData_of_selectedAlignment
      (d := d) hd hz hw A

/-- Same source-oriented invariant gives either a determinant-one complex
Lorentz orbit or the low-rank singular two-curve contraction data. -/
noncomputable def same_sourceOrientedInvariant_detOneOrbit_or_singularLimit
    [NeZero d]
    (hd : 2 ≤ d)
    (n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ ExtendedTube d n)
    (hw : w ∈ ExtendedTube d n)
    (hinv :
      sourceOrientedMinkowskiInvariant d n z =
        sourceOrientedMinkowskiInvariant d n w) :
    HWSameSourceOrientedInvariantBranchData d n z w := by
  classical
  have hgram :
      sourceMinkowskiGram d n z = sourceMinkowskiGram d n w :=
    same_sourceOrientedInvariant_sourceGram hinv
  by_cases hzOrbit : HWSourceGramOrbitRankAt d n z
  · have hSO : HWSameSourceGramSOOrientationCompatible d n z w :=
      sourceOriented_soCompatible_of_sameInvariant d n hgram hinv
    let orbit := hw_sameSourceGram_regular_orbit d n hzOrbit hgram hSO
    let Λ : ComplexLorentzGroup d := Classical.choose orbit
    have hΛ : w = complexLorentzAction Λ z := Classical.choose_spec orbit
    exact HWSameSourceOrientedInvariantBranchData.orbit Λ hΛ
  · have hlow : HWSourceGramLowRankAt d n z := by
      exact
        (hwSourceGram_lowRank_iff_not_orbitRank
          (d := d) (n := n)
          (Z := sourceMinkowskiGram d n z)).2 hzOrbit
    exact
      HWSameSourceOrientedInvariantBranchData.singular
        (hw_sameSourceGram_singular_contractionData
          (d := d) hd n hz hw hlow hgram)

/-- The active source-oriented Hall-Wightman branch law on the extended tube:
`extendF` is single-valued on equal source-oriented invariants. -/
theorem extendedTube_same_sourceOrientedInvariant_extendF_eq
    [NeZero d]
    (hd : 2 ≤ d)
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_cinv :
      ∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ForwardTube d n → complexLorentzAction Λ z ∈ ForwardTube d n →
        F (complexLorentzAction Λ z) = F z)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hz : z ∈ ExtendedTube d n)
    (hw : w ∈ ExtendedTube d n)
    (hinv :
      sourceOrientedMinkowskiInvariant d n z =
        sourceOrientedMinkowskiInvariant d n w) :
    extendF F z = extendF F w := by
  match
      same_sourceOrientedInvariant_detOneOrbit_or_singularLimit
        (d := d) hd n hz hw hinv with
  | HWSameSourceOrientedInvariantBranchData.orbit Λ hΛ =>
    rw [hΛ]
    exact (extendF_complexLorentzInvariant_of_cinv n F hF_cinv Λ z hz).symm
  | HWSameSourceOrientedInvariantBranchData.singular hsingular =>
    exact
      hw_sameSourceGram_singularLimit_extendF_eq
        d n F hF_holo hF_cinv hz hw hsingular

end BHW
