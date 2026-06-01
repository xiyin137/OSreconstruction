import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceHWBranchLaw
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedMaxRankHolomorphicSection

/-!
# Source-oriented Hall-Wightman quotient support

This file specializes the checked source-oriented quotient-value holomorphy,
continuity, and local-boundedness results to the newly proved
Hall-Wightman branch law.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial
open scoped Matrix.Norms.Operator

namespace BHW

/-- Max-rank oriented quotient values are locally holomorphic for `extendF`,
with branch independence supplied by the checked source-oriented branch law. -/
theorem sourceOrientedQuotientValue_holomorphicOn_maxRank_of_extendF
    {d : ℕ}
    [NeZero d]
    (hd : 2 ≤ d)
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_cinv :
      ∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ForwardTube d n →
        complexLorentzAction Λ z ∈ ForwardTube d n →
        F (complexLorentzAction Λ z) = F z)
    {G0 : SourceOrientedGramData d n}
    (hG0 : G0 ∈ sourceOrientedExtendedTubeDomain d n)
    (hReg : SourceOrientedMaxRankAt d n G0) :
    ∃ Ω Ψ,
      IsOpen Ω ∧ G0 ∈ Ω ∧
        DifferentiableOn ℂ Ψ Ω ∧
          Ω ∩ sourceOrientedGramVariety d n ⊆
            sourceOrientedExtendedTubeDomain d n ∧
          Set.EqOn (sourceOrientedQuotientValue (d := d) n F) Ψ
            (Ω ∩ sourceOrientedGramVariety d n) := by
  exact
    sourceOrientedQuotientValue_holomorphicOn_maxRank
      (d := d) hd n F hF_holo hF_cinv
      (fun {z w} hz hw hinv =>
        extendedTube_same_sourceOrientedInvariant_extendF_eq
          (d := d) hd n F hF_holo hF_cinv hz hw hinv)
      hG0 hReg

/-- The source-oriented quotient value of `extendF` is continuous and locally
bounded on the oriented extended-tube image, with branch independence supplied
by the checked source-oriented branch law. -/
theorem sourceOrientedQuotientValue_continuous_locallyBounded_of_extendF
    {d : ℕ}
    [NeZero d]
    (hd : 2 ≤ d)
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_cinv :
      ∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ForwardTube d n →
        complexLorentzAction Λ z ∈ ForwardTube d n →
        F (complexLorentzAction Λ z) = F z) :
    ContinuousOn (sourceOrientedQuotientValue (d := d) n F)
        (sourceOrientedExtendedTubeDomain d n) ∧
      LocallyBoundedOn (sourceOrientedQuotientValue (d := d) n F)
        (sourceOrientedExtendedTubeDomain d n) := by
  exact
    sourceOrientedQuotientValue_continuous_locallyBounded
      (d := d) hd n F hF_holo hF_cinv
      (fun {z w} hz hw hinv =>
        extendedTube_same_sourceOrientedInvariant_extendF_eq
          (d := d) hd n F hF_holo hF_cinv hz hw hinv)

end BHW
