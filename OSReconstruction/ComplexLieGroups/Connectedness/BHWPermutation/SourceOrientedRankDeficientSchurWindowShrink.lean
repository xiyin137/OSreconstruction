import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientNormalShrink
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientTailRankConnected
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientLocalImageTransport

/-!
# Schur-window shrink for transported rank-deficient normal images

This file chooses the actual Schur parameter window used by the
rank-deficient local-image producer.  The window is small enough to lie inside
the ambient normal-coordinate ball, and its residual-tail exact-rank slice is
connected by the checked tail-rank theorem.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW
namespace SourceOrientedRankDeficientAlgebraicNormalFormData

/-- Around a transported rank-deficient normal-form point, choose one
target-shaped Schur parameter window that is open, connected, centered, lies
in the invertible-head locus, maps into the requested ambient open set, and
has connected residual-tail exact-rank slice.  This is the shrink/topology
packet consumed by the concrete canonical Schur/residual local-image producer;
the remaining input is the image-openness and Schur extraction/surjectivity
for the canonical normal image. -/
theorem exists_schurParameterWindow_image_subset_open_head_tailRank_connected
    {d n : ℕ}
    {G0 : SourceOrientedGramData d n}
    (hn : d + 1 ≤ n)
    (N : SourceOrientedRankDeficientAlgebraicNormalFormData d n G0)
    {N0 : Set (SourceOrientedGramData d n)}
    (hN0_open : IsOpen N0)
    (hG0N0 : G0 ∈ N0) :
    ∃ (headRadius mixedRadius : ℝ)
      (Tail : SourceOrientedRankDeficientTailWindowChoice d n N.r N.hrD N.hrn),
      0 < headRadius ∧
        0 < mixedRadius ∧
        IsOpen
          (sourceOrientedRankDeficientSchurParameterWindow
            d n N.r N.hrD N.hrn headRadius mixedRadius Tail) ∧
        IsConnected
          (sourceOrientedRankDeficientSchurParameterWindow
            d n N.r N.hrD N.hrn headRadius mixedRadius Tail) ∧
        sourceOrientedNormalCenterParameter d n N.r N.hrD N.hrn ∈
          sourceOrientedRankDeficientSchurParameterWindow
            d n N.r N.hrD N.hrn headRadius mixedRadius Tail ∧
        sourceOrientedRankDeficientSchurParameterWindow
            d n N.r N.hrD N.hrn headRadius mixedRadius Tail ⊆
          {p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn |
            IsUnit p.head.det} ∧
        (∀ p,
          p ∈ sourceOrientedRankDeficientSchurParameterWindow
            d n N.r N.hrD N.hrn headRadius mixedRadius Tail →
            (N.originalNormalVarietyPoint p).1 ∈
              N0 ∩ sourceOrientedGramVariety d n) ∧
        IsConnected
          (sourceOrientedRankDeficientSchurParameterWindow
              d n N.r N.hrD N.hrn headRadius mixedRadius Tail ∩
            {p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn |
              (sourceOrientedNormalParameterSchurTail d n N.r N.hrD N.hrn p).rank =
                d + 1 - N.r}) := by
  rcases N.exists_normalParameterBall_image_subset_open_and_head
      hN0_open hG0N0 with
    ⟨ε, hε, _hball_open, _hball_conn, _hball_center, hball_head, hball_image⟩
  let ρ : ℝ := ε / 2
  have hρ_pos : 0 < ρ := by
    positivity
  have hρ_le : ρ ≤ ε := by
    dsimp [ρ]
    linarith
  let Tail : SourceOrientedRankDeficientTailWindowChoice d n N.r N.hrD N.hrn :=
    sourceOriented_rankDeficient_tailWindowChoice
      d n N.r N.hrD N.hrn hρ_pos
  have htail_le : Tail.tailCoordRadius ≤ ε := by
    simpa [Tail, sourceOriented_rankDeficient_tailWindowChoice] using hρ_le
  let W : Set (SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn) :=
    sourceOrientedRankDeficientSchurParameterWindow
      d n N.r N.hrD N.hrn ρ ρ Tail
  have hW_sub_ball :
      W ⊆
        sourceOrientedNormalParameterBall (d := d) (n := n) (r := N.r)
          (hrD := N.hrD) (hrn := N.hrn) ε := by
    exact
      sourceOrientedRankDeficientSchurParameterWindow_subset_normalParameterBall
        d n N.r N.hrD N.hrn hε hρ_le hρ_le Tail htail_le
  rcases sourceOrientedRankDeficientSchurParameterWindow_open_connected
      d n N.r N.hrD N.hrn hρ_pos hρ_pos Tail with
    ⟨hW_open, hW_conn, hW_center⟩
  have htailRank_conn :
      IsConnected
        (sourceShiftedTailTupleWindow d n N.r N.hrD N.hrn Tail ∩
          {q : Fin (n - N.r) → Fin (d + 1 - N.r) → ℂ |
            (sourceShiftedTailGram d N.r N.hrD (n - N.r) q).rank =
              d + 1 - N.r}) :=
    isConnected_sourceShiftedTailTupleWindow_tailRank
      d n N.r N.hrD N.hrn hn Tail
  have hW_tailRank_conn :
      IsConnected
        (W ∩
          {p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn |
            (sourceOrientedNormalParameterSchurTail d n N.r N.hrD N.hrn p).rank =
              d + 1 - N.r}) := by
    exact
      isConnected_sourceOrientedRankDeficientSchurParameterWindow_tailRank
        d n N.r N.hrD N.hrn hρ_pos hρ_pos Tail htailRank_conn
  refine
    ⟨ρ, ρ, Tail, hρ_pos, hρ_pos, hW_open, hW_conn, hW_center, ?_, ?_, ?_⟩
  · intro p hp
    exact hball_head (hW_sub_ball hp)
  · intro p hp
    exact hball_image p (hW_sub_ball hp)
  · simpa [W] using hW_tailRank_conn

/-- Assemble the strengthened rank-deficient local-image packet once the
remaining canonical Schur/residual image theorem has supplied the open normal
image and the two image-covering inclusions for the chosen Schur window.  All
ambient shrink, invertible-head, and max-rank-slice connectedness fields are
filled by `exists_schurParameterWindow_image_subset_open_head_tailRank_connected`. -/
noncomputable def maxRankLocalImageData_of_schurWindowCanonicalImage
    {d n : ℕ}
    {G0 : SourceOrientedGramData d n}
    (hn : d + 1 ≤ n)
    (N : SourceOrientedRankDeficientAlgebraicNormalFormData d n G0)
    {N0 : Set (SourceOrientedGramData d n)}
    (hN0_open : IsOpen N0)
    (hG0N0 : G0 ∈ N0)
    (hcanonical :
      ∀ {headRadius mixedRadius : ℝ}
        {Tail : SourceOrientedRankDeficientTailWindowChoice d n N.r N.hrD N.hrn},
        0 < headRadius →
          0 < mixedRadius →
            ∃ Ω : Set (SourceOrientedVariety d n),
              IsOpen Ω ∧
                Ω ⊆
                  sourceOrientedNormalParameterVarietyPoint d n N.r N.hrD N.hrn ''
                    sourceOrientedRankDeficientSchurParameterWindow
                      d n N.r N.hrD N.hrn headRadius mixedRadius Tail ∧
                (∀ p,
                  p ∈ sourceOrientedRankDeficientSchurParameterWindow
                    d n N.r N.hrD N.hrn headRadius mixedRadius Tail →
                    sourceOrientedNormalParameterVarietyPoint
                      d n N.r N.hrD N.hrn p ∈ Ω)) :
    Σ P : Type, Σ _ : TopologicalSpace P,
      SourceOrientedRankDeficientMaxRankLocalImageData
        (d := d) (n := n) (P := P) G0 N0 := by
  let hshrink_exists :=
    N.exists_schurParameterWindow_image_subset_open_head_tailRank_connected
      hn hN0_open hG0N0
  let headRadius := Classical.choose hshrink_exists
  let hshrink_exists₁ := Classical.choose_spec hshrink_exists
  let mixedRadius := Classical.choose hshrink_exists₁
  let hshrink_exists₂ := Classical.choose_spec hshrink_exists₁
  let Tail := Classical.choose hshrink_exists₂
  let hshrink := Classical.choose_spec hshrink_exists₂
  have hheadRadius : 0 < headRadius := hshrink.1
  have hmixedRadius : 0 < mixedRadius := hshrink.2.1
  have hW_open :
      IsOpen
        (sourceOrientedRankDeficientSchurParameterWindow
          d n N.r N.hrD N.hrn headRadius mixedRadius Tail) :=
    hshrink.2.2.1
  have hW_conn :
      IsConnected
        (sourceOrientedRankDeficientSchurParameterWindow
          d n N.r N.hrD N.hrn headRadius mixedRadius Tail) :=
    hshrink.2.2.2.1
  have hcenter :
      sourceOrientedNormalCenterParameter d n N.r N.hrD N.hrn ∈
        sourceOrientedRankDeficientSchurParameterWindow
          d n N.r N.hrD N.hrn headRadius mixedRadius Tail :=
    hshrink.2.2.2.2.1
  have hhead :
      sourceOrientedRankDeficientSchurParameterWindow
          d n N.r N.hrD N.hrn headRadius mixedRadius Tail ⊆
        {p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn |
          IsUnit p.head.det} :=
    hshrink.2.2.2.2.2.1
  have himage :
      ∀ p,
        p ∈ sourceOrientedRankDeficientSchurParameterWindow
          d n N.r N.hrD N.hrn headRadius mixedRadius Tail →
          (N.originalNormalVarietyPoint p).1 ∈
            N0 ∩ sourceOrientedGramVariety d n :=
    hshrink.2.2.2.2.2.2.1
  have htailRank_conn :
      IsConnected
        (sourceOrientedRankDeficientSchurParameterWindow
            d n N.r N.hrD N.hrn headRadius mixedRadius Tail ∩
          {p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn |
            (sourceOrientedNormalParameterSchurTail d n N.r N.hrD N.hrn p).rank =
              d + 1 - N.r}) :=
    hshrink.2.2.2.2.2.2.2
  let W : Set (SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn) :=
    sourceOrientedRankDeficientSchurParameterWindow
      d n N.r N.hrD N.hrn headRadius mixedRadius Tail
  let hcanonical_exists :=
    hcanonical (headRadius := headRadius) (mixedRadius := mixedRadius)
      (Tail := Tail) hheadRadius hmixedRadius
  let Ω := Classical.choose hcanonical_exists
  let hcanonical_spec := Classical.choose_spec hcanonical_exists
  have hΩ_open : IsOpen Ω := hcanonical_spec.1
  have hsurj :
      Ω ⊆
        sourceOrientedNormalParameterVarietyPoint d n N.r N.hrD N.hrn '' W := by
    simpa [W] using hcanonical_spec.2.1
  have hmem :
      ∀ p, p ∈ W →
        sourceOrientedNormalParameterVarietyPoint d n N.r N.hrD N.hrn p ∈ Ω := by
    simpa [W] using hcanonical_spec.2.2
  refine
    ⟨SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn,
      inferInstance, ?_⟩
  exact
    SourceOrientedRankDeficientMaxRankLocalImageData.ofNormalImageTransport_of_tailRank_connected
        (d := d) (n := n) hn N
        (N0 := N0) (parameterBox := W)
        hW_open hW_conn hcenter hhead hΩ_open hsurj hmem himage
        (by simpa [W] using htailRank_conn)

end SourceOrientedRankDeficientAlgebraicNormalFormData
end BHW
