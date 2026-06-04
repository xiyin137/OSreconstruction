import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedHWQuotient
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedDomainDensity

/-!
# Source-oriented descent reducer

This file contains the mechanical descent step from the explicit
normal/Riemann extension input to the source-oriented scalar representative.
The normality and removable-singularity theorem itself remains an explicit
input; no new axiom or analytic shortcut is introduced here.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Exact hard input for the oriented normal/Riemann descent step.

Given a continuous, locally bounded scalar on the oriented extended-tube image
with local holomorphic representatives away from the exceptional-rank locus,
it returns a germ-holomorphic representative on the whole oriented image. -/
def SourceOrientedNormalRiemannExtensionInput
    (d n : ℕ) : Prop :=
  ∀ {Phi : SourceOrientedGramData d n → ℂ},
    ContinuousOn Phi (sourceOrientedExtendedTubeDomain d n) →
    LocallyBoundedOn Phi (sourceOrientedExtendedTubeDomain d n) →
    (∀ G0,
      G0 ∈ sourceOrientedExtendedTubeDomain d n \
        {G | SourceOrientedExceptionalRank d n G} →
        ∃ Ω Ψ,
          IsOpen Ω ∧ G0 ∈ Ω ∧
            DifferentiableOn ℂ Ψ Ω ∧
              Ω ∩ sourceOrientedGramVariety d n ⊆
                sourceOrientedExtendedTubeDomain d n ∧
              Set.EqOn Phi Ψ
                (Ω ∩ sourceOrientedGramVariety d n)) →
    SourceOrientedVarietyGermHolomorphicOn d n Phi
      (sourceOrientedExtendedTubeDomain d n)

/-- The branch-defined oriented quotient descends to a germ-holomorphic
representative once the normal/Riemann extension input is available. -/
theorem sourceOrientedVarietyGermHolomorphicOn_extendF_descent_of_normalRiemann
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
        extendF F z = extendF F w)
    (hRiemann : SourceOrientedNormalRiemannExtensionInput d n) :
    ∃ Phi : SourceOrientedGramData d n → ℂ,
      SourceOrientedVarietyGermHolomorphicOn d n Phi
        (sourceOrientedExtendedTubeDomain d n) ∧
        ∀ w, w ∈ ExtendedTube d n →
          Phi (sourceOrientedMinkowskiInvariant d n w) = extendF F w := by
  classical
  refine ⟨sourceOrientedQuotientValue n F, ?_, ?_⟩
  · have hcb :
        ContinuousOn (sourceOrientedQuotientValue (d := d) n F)
            (sourceOrientedExtendedTubeDomain d n) ∧
          LocallyBoundedOn (sourceOrientedQuotientValue (d := d) n F)
            (sourceOrientedExtendedTubeDomain d n) :=
      sourceOrientedQuotientValue_continuous_locallyBounded
        (d := d) hd n F hF_holo hF_cinv hBranch
    exact
      hRiemann hcb.1 hcb.2
        (by
          intro G0 hG0
          have hReg : SourceOrientedMaxRankAt d n G0 :=
            (not_exceptional_rank_iff_maxRank
              (d := d) (n := n) hG0.1).1 hG0.2
          exact
            sourceOrientedQuotientValue_holomorphicOn_maxRank
              (d := d) hd n F hF_holo hF_cinv hBranch hG0.1 hReg)
  · intro w hw
    exact
      sourceOrientedQuotientValue_wellDefined
        (d := d) F hBranch hw rfl

/-- The generic proper-complex Hall-Wightman source-oriented representative,
conditional only on the explicit normal/Riemann extension input. -/
noncomputable def hallWightman_sourceOrientedScalarRepresentativeData_of_normalRiemann
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
    (hRiemann : SourceOrientedNormalRiemannExtensionInput d n) :
    SourceOrientedScalarRepresentativeData (d := d) n F := by
  classical
  have hDesc :
      ∃ Phi : SourceOrientedGramData d n → ℂ,
        SourceOrientedVarietyGermHolomorphicOn d n Phi
          (sourceOrientedExtendedTubeDomain d n) ∧
          ∀ w, w ∈ ExtendedTube d n →
            Phi (sourceOrientedMinkowskiInvariant d n w) = extendF F w :=
    sourceOrientedVarietyGermHolomorphicOn_extendF_descent_of_normalRiemann
      (d := d) hd n F hF_holo hF_cinv
      (fun {z w} hz hw hinv =>
        extendedTube_same_sourceOrientedInvariant_extendF_eq
          (d := d) hd n F hF_holo hF_cinv hz hw hinv)
      hRiemann
  exact
    sourceOrientedScalarRepresentativeData_of_branchLaw
      (d := d) n F
      (sourceOrientedExtendedTubeDomain_relOpen_connected (d := d) hd n)
      hDesc

end BHW
