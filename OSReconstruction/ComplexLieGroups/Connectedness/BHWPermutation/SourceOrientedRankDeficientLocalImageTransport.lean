import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientLocalImage
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientNormalImage

/-!
# Rank-deficient local-image transport adapters

This file sits downstream of both the abstract local-image packets and the
canonical normal-image transport.  Keeping these adapters here avoids making
`SourceOrientedRankDeficientLocalImage` depend on the normal-form stack.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

variable {d n : ℕ}

namespace SourceOrientedRankDeficientVarietyLocalImageData

/-- Build a rank-deficient local-image packet from an open canonical normal
image and transport it back to the original exceptional point.  The concrete
Schur/residual producer should supply the open normal image `Ω`, the
surjectivity onto `Ω`, and the containment of the transported image in the
requested ambient neighborhood. -/
noncomputable def ofNormalImageTransport
    {G0 : SourceOrientedGramData d n}
    (N : SourceOrientedRankDeficientAlgebraicNormalFormData d n G0)
    {N0 : Set (SourceOrientedGramData d n)}
    {parameterBox :
      Set (SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn)}
    (parameterBox_open : IsOpen parameterBox)
    (parameterBox_connected : IsConnected parameterBox)
    (center_mem :
      sourceOrientedNormalCenterParameter d n N.r N.hrD N.hrn ∈ parameterBox)
    {Ω : Set (SourceOrientedVariety d n)}
    (hΩ_open : IsOpen Ω)
    (hsurj :
      Ω ⊆
        sourceOrientedNormalParameterVarietyPoint d n N.r N.hrD N.hrn ''
          parameterBox)
    (hmem :
      ∀ p ∈ parameterBox,
        sourceOrientedNormalParameterVarietyPoint d n N.r N.hrD N.hrn p ∈ Ω)
    (hsub :
      sourceOrientedVarietyUnderlyingSet d n
          (N.varietyTransport.invFun '' Ω) ⊆
        N0 ∩ sourceOrientedGramVariety d n) :
    SourceOrientedRankDeficientVarietyLocalImageData
      (d := d) (n := n)
      (P := SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn)
      G0 N0 := by
  have himage_eq :
      N.originalNormalVarietyPoint '' parameterBox =
        N.varietyTransport.invFun '' Ω := by
    simpa [SourceOrientedRankDeficientAlgebraicNormalFormData.originalNormalVarietyPoint]
      using
        (sourceOrientedVarietyTransport_invFun_image_eq
          (d := d) (n := n) N.varietyTransport
          (α := SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn)
          (Ω := Ω) (s := parameterBox)
          (f := sourceOrientedNormalParameterVarietyPoint d n N.r N.hrD N.hrn)
          hsurj hmem)
  exact
    SourceOrientedRankDeficientVarietyLocalImageData.ofSubtype
      (d := d) (n := n)
      parameterBox_open parameterBox_connected center_mem
      N.continuous_originalNormalVarietyPoint.continuousOn
      N.originalNormalVarietyPoint_center
      (by
        rw [himage_eq]
        exact N.varietyTransport.isOpen_invFun_image hΩ_open)
      (by
        rw [himage_eq]
        exact hsub)

/-- Variant of `ofNormalImageTransport` deriving transported ambient
containment from pointwise membership of the parameter-box image.  The concrete
Schur/residual producer only needs to prove that every parameter in the chosen
box maps into the requested ambient set, plus surjectivity onto the canonical
normal image `Ω`. -/
noncomputable def ofNormalImageTransport_of_parameter_mem
    {G0 : SourceOrientedGramData d n}
    (N : SourceOrientedRankDeficientAlgebraicNormalFormData d n G0)
    {N0 : Set (SourceOrientedGramData d n)}
    {parameterBox :
      Set (SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn)}
    (parameterBox_open : IsOpen parameterBox)
    (parameterBox_connected : IsConnected parameterBox)
    (center_mem :
      sourceOrientedNormalCenterParameter d n N.r N.hrD N.hrn ∈ parameterBox)
    {Ω : Set (SourceOrientedVariety d n)}
    (hΩ_open : IsOpen Ω)
    (hsurj :
      Ω ⊆
        sourceOrientedNormalParameterVarietyPoint d n N.r N.hrD N.hrn ''
          parameterBox)
    (hmem :
      ∀ p ∈ parameterBox,
        sourceOrientedNormalParameterVarietyPoint d n N.r N.hrD N.hrn p ∈ Ω)
    (himage :
      ∀ p ∈ parameterBox,
        (N.originalNormalVarietyPoint p).1 ∈
          N0 ∩ sourceOrientedGramVariety d n) :
    SourceOrientedRankDeficientVarietyLocalImageData
      (d := d) (n := n)
      (P := SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn)
      G0 N0 := by
  have himage_eq :
      N.originalNormalVarietyPoint '' parameterBox =
        N.varietyTransport.invFun '' Ω := by
    simpa [SourceOrientedRankDeficientAlgebraicNormalFormData.originalNormalVarietyPoint]
      using
        (sourceOrientedVarietyTransport_invFun_image_eq
          (d := d) (n := n) N.varietyTransport
          (α := SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn)
          (Ω := Ω) (s := parameterBox)
          (f := sourceOrientedNormalParameterVarietyPoint d n N.r N.hrD N.hrn)
          hsurj hmem)
  exact
    SourceOrientedRankDeficientVarietyLocalImageData.ofNormalImageTransport
      (d := d) (n := n) N
      parameterBox_open parameterBox_connected center_mem
      hΩ_open hsurj hmem
      (by
        rw [← himage_eq, sourceOrientedVarietyUnderlyingSet_image]
        intro G hG
        rcases hG with ⟨p, hp, rfl⟩
        exact himage p hp)

end SourceOrientedRankDeficientVarietyLocalImageData

namespace SourceOrientedRankDeficientMaxRankLocalImageData

/-- Strengthened max-rank local-image packet from an open canonical normal
image transported back to the original exceptional point. -/
noncomputable def ofNormalImageTransport
    {G0 : SourceOrientedGramData d n}
    (N : SourceOrientedRankDeficientAlgebraicNormalFormData d n G0)
    {N0 : Set (SourceOrientedGramData d n)}
    {parameterBox :
      Set (SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn)}
    (parameterBox_open : IsOpen parameterBox)
    (parameterBox_connected : IsConnected parameterBox)
    (center_mem :
      sourceOrientedNormalCenterParameter d n N.r N.hrD N.hrn ∈ parameterBox)
    {Ω : Set (SourceOrientedVariety d n)}
    (hΩ_open : IsOpen Ω)
    (hsurj :
      Ω ⊆
        sourceOrientedNormalParameterVarietyPoint d n N.r N.hrD N.hrn ''
          parameterBox)
    (hmem :
      ∀ p ∈ parameterBox,
        sourceOrientedNormalParameterVarietyPoint d n N.r N.hrD N.hrn p ∈ Ω)
    (hsub :
      sourceOrientedVarietyUnderlyingSet d n
          (N.varietyTransport.invFun '' Ω) ⊆
        N0 ∩ sourceOrientedGramVariety d n)
    (hpreimage_connected :
      IsConnected (parameterBox ∩
        {p | SourceOrientedMaxRankAt d n (N.originalNormalVarietyPoint p).1})) :
    SourceOrientedRankDeficientMaxRankLocalImageData
      (d := d) (n := n)
      (P := SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn)
      G0 N0 := by
  have himage_eq :
      N.originalNormalVarietyPoint '' parameterBox =
        N.varietyTransport.invFun '' Ω := by
    simpa [SourceOrientedRankDeficientAlgebraicNormalFormData.originalNormalVarietyPoint]
      using
        (sourceOrientedVarietyTransport_invFun_image_eq
          (d := d) (n := n) N.varietyTransport
          (α := SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn)
          (Ω := Ω) (s := parameterBox)
          (f := sourceOrientedNormalParameterVarietyPoint d n N.r N.hrD N.hrn)
          hsurj hmem)
  exact
    SourceOrientedRankDeficientMaxRankLocalImageData.ofSubtype
      (d := d) (n := n)
      parameterBox_open parameterBox_connected center_mem
      N.continuous_originalNormalVarietyPoint.continuousOn
      N.originalNormalVarietyPoint_center
      (by
        rw [himage_eq]
        exact N.varietyTransport.isOpen_invFun_image hΩ_open)
      (by
        rw [himage_eq]
        exact hsub)
      hpreimage_connected

/-- Strengthened variant deriving transported ambient containment from
pointwise membership of the parameter-box image. -/
noncomputable def ofNormalImageTransport_of_parameter_mem
    {G0 : SourceOrientedGramData d n}
    (N : SourceOrientedRankDeficientAlgebraicNormalFormData d n G0)
    {N0 : Set (SourceOrientedGramData d n)}
    {parameterBox :
      Set (SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn)}
    (parameterBox_open : IsOpen parameterBox)
    (parameterBox_connected : IsConnected parameterBox)
    (center_mem :
      sourceOrientedNormalCenterParameter d n N.r N.hrD N.hrn ∈ parameterBox)
    {Ω : Set (SourceOrientedVariety d n)}
    (hΩ_open : IsOpen Ω)
    (hsurj :
      Ω ⊆
        sourceOrientedNormalParameterVarietyPoint d n N.r N.hrD N.hrn ''
          parameterBox)
    (hmem :
      ∀ p ∈ parameterBox,
        sourceOrientedNormalParameterVarietyPoint d n N.r N.hrD N.hrn p ∈ Ω)
    (himage :
      ∀ p ∈ parameterBox,
        (N.originalNormalVarietyPoint p).1 ∈
          N0 ∩ sourceOrientedGramVariety d n)
    (hpreimage_connected :
      IsConnected (parameterBox ∩
        {p | SourceOrientedMaxRankAt d n (N.originalNormalVarietyPoint p).1})) :
    SourceOrientedRankDeficientMaxRankLocalImageData
      (d := d) (n := n)
      (P := SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn)
      G0 N0 := by
  have himage_eq :
      N.originalNormalVarietyPoint '' parameterBox =
        N.varietyTransport.invFun '' Ω := by
    simpa [SourceOrientedRankDeficientAlgebraicNormalFormData.originalNormalVarietyPoint]
      using
        (sourceOrientedVarietyTransport_invFun_image_eq
          (d := d) (n := n) N.varietyTransport
          (α := SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn)
          (Ω := Ω) (s := parameterBox)
          (f := sourceOrientedNormalParameterVarietyPoint d n N.r N.hrD N.hrn)
          hsurj hmem)
  exact
    SourceOrientedRankDeficientMaxRankLocalImageData.ofNormalImageTransport
      (d := d) (n := n) N
      parameterBox_open parameterBox_connected center_mem
      hΩ_open hsurj hmem
      (by
        rw [← himage_eq, sourceOrientedVarietyUnderlyingSet_image]
        intro G hG
        rcases hG with ⟨p, hp, rfl⟩
        exact himage p hp)
      hpreimage_connected

/-- Strengthened transport adapter whose connectedness hypothesis is already
rewritten to the residual-tail exact-rank slice.  This is the final topology
shape expected from the Schur-window connectedness proof. -/
noncomputable def ofNormalImageTransport_of_tailRank_connected
    {G0 : SourceOrientedGramData d n}
    (hn : d + 1 ≤ n)
    (N : SourceOrientedRankDeficientAlgebraicNormalFormData d n G0)
    {N0 : Set (SourceOrientedGramData d n)}
    {parameterBox :
      Set (SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn)}
    (parameterBox_open : IsOpen parameterBox)
    (parameterBox_connected : IsConnected parameterBox)
    (center_mem :
      sourceOrientedNormalCenterParameter d n N.r N.hrD N.hrn ∈ parameterBox)
    (hhead :
      parameterBox ⊆
        {p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn |
          IsUnit p.head.det})
    {Ω : Set (SourceOrientedVariety d n)}
    (hΩ_open : IsOpen Ω)
    (hsurj :
      Ω ⊆
        sourceOrientedNormalParameterVarietyPoint d n N.r N.hrD N.hrn ''
          parameterBox)
    (hmem :
      ∀ p ∈ parameterBox,
        sourceOrientedNormalParameterVarietyPoint d n N.r N.hrD N.hrn p ∈ Ω)
    (himage :
      ∀ p ∈ parameterBox,
        (N.originalNormalVarietyPoint p).1 ∈
          N0 ∩ sourceOrientedGramVariety d n)
    (htailRank_connected :
      IsConnected (parameterBox ∩
        {p |
          (sourceOrientedNormalParameterSchurTail d n N.r N.hrD N.hrn p).rank =
            d + 1 - N.r})) :
    SourceOrientedRankDeficientMaxRankLocalImageData
      (d := d) (n := n)
      (P := SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn)
      G0 N0 := by
  refine
    SourceOrientedRankDeficientMaxRankLocalImageData.ofNormalImageTransport_of_parameter_mem
      (d := d) (n := n) N
      parameterBox_open parameterBox_connected center_mem
      hΩ_open hsurj hmem himage ?_
  rw [N.parameterBox_maxRank_preimage_eq_tailRank hn hhead]
  exact htailRank_connected

end SourceOrientedRankDeficientMaxRankLocalImageData

end BHW
