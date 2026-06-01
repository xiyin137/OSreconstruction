import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedScalarRepresentative

/-!
# Source-oriented holomorphic local sections

This file contains the consumer side of the max-rank scalar descent step:
given an actual ambient holomorphic section of the source-oriented invariant
map through the extended tube, the branch-defined quotient value has the
required local ambient holomorphic representative.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace SCV

/-- If a local homeomorphism has an invertible derivative and is smooth at
each inverse image of a set, then its inverse is differentiable on that set.
This packages the repeated `OpenPartialHomeomorph.contDiffAt_symm` pattern used
by selected zero-section and full-frame implicit-inverse charts. -/
theorem openPartialHomeomorph_symm_differentiableOn_of_hasFDerivAt
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (e : OpenPartialHomeomorph E F)
    {D : Set F}
    (hD_target : D ⊆ e.target)
    (hderiv :
      ∀ y, y ∈ D →
        ∃ e' : E ≃L[𝕜] F,
          HasFDerivAt e (e' : E →L[𝕜] F) (e.symm y))
    (hsmooth : ∀ y, y ∈ D → ContDiffAt 𝕜 ⊤ e (e.symm y)) :
    DifferentiableOn 𝕜 e.symm D := by
  intro y hy
  rcases hderiv y hy with ⟨e', he'⟩
  have hsymm : ContDiffAt 𝕜 ⊤ e.symm y :=
    e.contDiffAt_symm (hD_target hy) he' (hsmooth y hy)
  exact (hsymm.differentiableAt (by simp)).differentiableWithinAt

end SCV

namespace BHW

/-- A local ambient holomorphic section of the source-oriented invariant map
through the extended tube.  The section is only required to right-invert the
invariant on the source-oriented variety inside the ambient open set. -/
structure SourceOrientedLocalHolomorphicSectionData
    {d : ℕ}
    [NeZero d]
    (n : ℕ)
    (G0 : SourceOrientedGramData d n) where
  Ω : Set (SourceOrientedGramData d n)
  Ω_open : IsOpen Ω
  center_mem : G0 ∈ Ω
  toVec : SourceOrientedGramData d n → Fin n → Fin (d + 1) → ℂ
  toVec_mem : ∀ G, G ∈ Ω → toVec G ∈ ExtendedTube d n
  toVec_right_inv :
    ∀ G, G ∈ Ω ∩ sourceOrientedGramVariety d n →
      sourceOrientedMinkowskiInvariant d n (toVec G) = G
  toVec_holomorphic : DifferentiableOn ℂ toVec Ω

/-- A holomorphic local section turns the branch-defined quotient value into a
local ambient holomorphic representative on the oriented source variety. -/
theorem sourceOrientedQuotientValue_holomorphicOn_of_localSection
    {d : ℕ}
    [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_ext_holo : DifferentiableOn ℂ (extendF F) (ExtendedTube d n))
    (hBranch :
      ∀ {z w : Fin n → Fin (d + 1) → ℂ},
        z ∈ ExtendedTube d n →
        w ∈ ExtendedTube d n →
        sourceOrientedMinkowskiInvariant d n z =
          sourceOrientedMinkowskiInvariant d n w →
        extendF F z = extendF F w)
    {G0 : SourceOrientedGramData d n}
    (S : SourceOrientedLocalHolomorphicSectionData (d := d) n G0) :
    ∃ Ω Ψ,
      IsOpen Ω ∧ G0 ∈ Ω ∧
        DifferentiableOn ℂ Ψ Ω ∧
          Ω ∩ sourceOrientedGramVariety d n ⊆
            sourceOrientedExtendedTubeDomain d n ∧
          Set.EqOn (sourceOrientedQuotientValue (d := d) n F) Ψ
            (Ω ∩ sourceOrientedGramVariety d n) := by
  refine
    ⟨S.Ω, fun G => extendF F (S.toVec G),
      S.Ω_open, S.center_mem, ?_, ?_, ?_⟩
  · exact hF_ext_holo.comp S.toVec_holomorphic S.toVec_mem
  · intro G hG
    exact ⟨S.toVec G, S.toVec_mem G hG.1, S.toVec_right_inv G hG⟩
  · intro G hG
    exact
      sourceOrientedQuotientValue_wellDefined
        (d := d) F hBranch
        (S.toVec_mem G hG.1)
        (S.toVec_right_inv G hG)

/-- Max-rank local sections supply the max-rank-local hypothesis consumed by
the checked global continuity and local-boundedness assembly. -/
theorem sourceOrientedQuotientValue_maxRankLocal_of_localSectionProducer
    {d : ℕ}
    [NeZero d]
    (n : ℕ)
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_ext_holo : DifferentiableOn ℂ (extendF F) (ExtendedTube d n))
    (hBranch :
      ∀ {z w : Fin n → Fin (d + 1) → ℂ},
        z ∈ ExtendedTube d n →
        w ∈ ExtendedTube d n →
        sourceOrientedMinkowskiInvariant d n z =
          sourceOrientedMinkowskiInvariant d n w →
        extendF F z = extendF F w)
    (localSection :
      ∀ {G0 : SourceOrientedGramData d n},
        G0 ∈ sourceOrientedExtendedTubeDomain d n →
          SourceOrientedMaxRankAt d n G0 →
            SourceOrientedLocalHolomorphicSectionData (d := d) n G0) :
    ∀ {G0 : SourceOrientedGramData d n},
      G0 ∈ sourceOrientedExtendedTubeDomain d n →
        SourceOrientedMaxRankAt d n G0 →
          ∃ Ω Ψ,
            IsOpen Ω ∧ G0 ∈ Ω ∧
              DifferentiableOn ℂ Ψ Ω ∧
                Ω ∩ sourceOrientedGramVariety d n ⊆
                  sourceOrientedExtendedTubeDomain d n ∧
                Set.EqOn (sourceOrientedQuotientValue (d := d) n F) Ψ
                  (Ω ∩ sourceOrientedGramVariety d n) := by
  intro G0 hG0 hmax
  exact
    sourceOrientedQuotientValue_holomorphicOn_of_localSection
      (d := d) n F hF_ext_holo hBranch (localSection hG0 hmax)

/-- With max-rank local sections in hand, the checked residual-chart branch
gives global continuity and local boundedness of the quotient value. -/
theorem sourceOrientedQuotientValue_continuous_locallyBounded_of_localSectionProducer
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
    (localSection :
      ∀ {G0 : SourceOrientedGramData d n},
        G0 ∈ sourceOrientedExtendedTubeDomain d n →
          SourceOrientedMaxRankAt d n G0 →
            SourceOrientedLocalHolomorphicSectionData (d := d) n G0) :
    ContinuousOn (sourceOrientedQuotientValue (d := d) n F)
        (sourceOrientedExtendedTubeDomain d n) ∧
      LocallyBoundedOn (sourceOrientedQuotientValue (d := d) n F)
        (sourceOrientedExtendedTubeDomain d n) := by
  have hF_ext_holo :
      DifferentiableOn ℂ (extendF F) (ExtendedTube d n) :=
    extendF_holomorphicOn n F hF_holo hF_cinv
  exact
    sourceOrientedQuotientValue_continuous_locallyBounded_of_maxRankLocal
      (d := d) hd n F hF_ext_holo.continuousOn hBranch
      (sourceOrientedQuotientValue_maxRankLocal_of_localSectionProducer
        (d := d) n F hF_ext_holo hBranch localSection)

end BHW
