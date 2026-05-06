import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientNormalShrink
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientTailRankConnected

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

end SourceOrientedRankDeficientAlgebraicNormalFormData
end BHW
