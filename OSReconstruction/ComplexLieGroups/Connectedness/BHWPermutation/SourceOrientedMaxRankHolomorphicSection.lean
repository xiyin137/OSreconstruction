import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedSmallArityHolomorphicSection
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedFullFrameHolomorphicSection

/-!
# Max-rank source-oriented holomorphic section producer

This file assembles the two checked max-rank branches: the small-arity
ordinary-Gram zero-section and the hard-range full-frame chart section.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial
open scoped Matrix.Norms.Operator

namespace BHW

/-- Every max-rank point in the oriented extended-tube image has an ambient
holomorphic local section through the extended tube. -/
noncomputable def sourceOrientedExtendedTube_holomorphicLocalSection
    {d n : ℕ}
    [NeZero d]
    {G0 : SourceOrientedGramData d n}
    (hG0 : G0 ∈ sourceOrientedExtendedTubeDomain d n)
    (hReg : SourceOrientedMaxRankAt d n G0) :
    SourceOrientedLocalHolomorphicSectionData (d := d) n G0 := by
  classical
  let z0 : Fin n → Fin (d + 1) → ℂ := Classical.choose hG0
  have hz0_spec :
      z0 ∈ ExtendedTube d n ∧
        sourceOrientedMinkowskiInvariant d n z0 = G0 :=
    Classical.choose_spec hG0
  have hz0 : z0 ∈ ExtendedTube d n := hz0_spec.1
  have hG0_eq : sourceOrientedMinkowskiInvariant d n z0 = G0 := hz0_spec.2
  rw [← hG0_eq] at hReg ⊢
  by_cases hn : n < d + 1
  · exact
      sourceOrientedMaxRank_localSection_smallArity
        (d := d) (n := n) hn hz0 hReg
  · have hn_le : d + 1 ≤ n := Nat.le_of_not_lt hn
    have hHW : HWSourceGramMaxRankAt d n z0 :=
      (sourceOrientedMaxRankAt_invariant_iff_hwSourceGramMaxRankAt d n z0).1
        hReg
    have hreg : SourceComplexGramRegularAt d n z0 :=
      sourceComplexGramRegularAt_of_HWSourceGramMaxRankAt d n hn_le hHW
    let hexDet :=
      exists_sourceFullFrameDet_ne_zero_of_sourceComplexGramRegularAt
        d n hn_le hreg
    let ι : Fin (d + 1) ↪ Fin n := Classical.choose hexDet
    have hdet : sourceFullFrameDet d n ι z0 ≠ 0 := Classical.choose_spec hexDet
    exact
      sourceOrientedMaxRank_localSection_fullFrame
        (d := d) (n := n) hn_le hz0 ι hdet

/-- Max-rank points in the oriented extended-tube image have local ambient
holomorphic representatives of the branch-defined quotient value. -/
theorem sourceOrientedQuotientValue_holomorphicOn_maxRank
    {d : ℕ}
    [NeZero d]
    (_hd : 2 ≤ d)
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_cinv :
      ∀ (Λ : ComplexLorentzGroup d) (z : Fin n → Fin (d + 1) → ℂ),
        z ∈ ForwardTube d n →
        complexLorentzAction Λ z ∈ ForwardTube d n →
        F (complexLorentzAction Λ z) = F z)
    (hBranch :
      ∀ {z w : Fin n → Fin (d + 1) → ℂ},
        z ∈ ExtendedTube d n →
        w ∈ ExtendedTube d n →
        sourceOrientedMinkowskiInvariant d n z =
          sourceOrientedMinkowskiInvariant d n w →
        extendF F z = extendF F w)
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
    sourceOrientedQuotientValue_holomorphicOn_of_localSection
      (d := d) n F
      (extendF_holomorphicOn (d := d) n F hF_holo hF_cinv)
      hBranch
      (sourceOrientedExtendedTube_holomorphicLocalSection
        (d := d) (n := n) hG0 hReg)

/-- Global continuity and local boundedness of the branch-defined quotient
value on the oriented extended-tube image, using the checked max-rank local
sections and rank-deficient residual charts. -/
theorem sourceOrientedQuotientValue_continuous_locallyBounded
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
    (hBranch :
      ∀ {z w : Fin n → Fin (d + 1) → ℂ},
        z ∈ ExtendedTube d n →
        w ∈ ExtendedTube d n →
        sourceOrientedMinkowskiInvariant d n z =
          sourceOrientedMinkowskiInvariant d n w →
        extendF F z = extendF F w) :
    ContinuousOn (sourceOrientedQuotientValue (d := d) n F)
        (sourceOrientedExtendedTubeDomain d n) ∧
      LocallyBoundedOn (sourceOrientedQuotientValue (d := d) n F)
        (sourceOrientedExtendedTubeDomain d n) := by
  exact
    sourceOrientedQuotientValue_continuous_locallyBounded_of_localSectionProducer
      (d := d) hd n F hF_holo hF_cinv hBranch
      (fun {G0} hG0 hReg =>
        sourceOrientedExtendedTube_holomorphicLocalSection
          (d := d) (n := n) (G0 := G0) hG0 hReg)

end BHW
