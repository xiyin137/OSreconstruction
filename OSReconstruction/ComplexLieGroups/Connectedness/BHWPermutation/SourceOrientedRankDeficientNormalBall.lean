import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedNormalParameterBall
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientNormalImage

/-!
# Normal-form parameter-ball shrink for transported exceptional points

This file proves the ambient-neighborhood shrink used by the exceptional
rank-deficient local-image producer.  Starting from an algebraic normal form
and an ambient open set containing the original exceptional point, we choose a
small connected normal-parameter ball whose transported source-variety image
stays in that open set and whose head block is invertible throughout.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW
namespace SourceOrientedRankDeficientAlgebraicNormalFormData

/-- Given an ambient open target around the original exceptional point, choose
a positive-radius connected normal-parameter ball around the canonical normal
center.  The ball lies in the invertible-head locus, and every transported
normal-image point lies in the requested open target and in the source-oriented
variety. -/
theorem exists_normalParameterBall_image_subset_open_and_head
    {d n : ℕ}
    {G0 : SourceOrientedGramData d n}
    (N : SourceOrientedRankDeficientAlgebraicNormalFormData d n G0)
    {N0 : Set (SourceOrientedGramData d n)}
    (hN0_open : IsOpen N0)
    (hG0N0 : G0 ∈ N0) :
    ∃ ε : ℝ,
      0 < ε ∧
        IsOpen (sourceOrientedNormalParameterBall (d := d) (n := n) (r := N.r)
          (hrD := N.hrD) (hrn := N.hrn) ε) ∧
        IsConnected (sourceOrientedNormalParameterBall (d := d) (n := n) (r := N.r)
          (hrD := N.hrD) (hrn := N.hrn) ε) ∧
        sourceOrientedNormalCenterParameter d n N.r N.hrD N.hrn ∈
          sourceOrientedNormalParameterBall (d := d) (n := n) (r := N.r)
            (hrD := N.hrD) (hrn := N.hrn) ε ∧
        sourceOrientedNormalParameterBall (d := d) (n := n) (r := N.r)
          (hrD := N.hrD) (hrn := N.hrn) ε ⊆
          {p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn |
            IsUnit p.head.det} ∧
        (∀ p,
          p ∈ sourceOrientedNormalParameterBall (d := d) (n := n) (r := N.r)
            (hrD := N.hrD) (hrn := N.hrn) ε →
            (N.originalNormalVarietyPoint p).1 ∈
              N0 ∩ sourceOrientedGramVariety d n) := by
  let p0 := sourceOrientedNormalCenterParameter d n N.r N.hrD N.hrn
  let image : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn →
      SourceOrientedGramData d n := fun p => (N.originalNormalVarietyPoint p).1
  have himage_cont : Continuous image :=
    continuous_subtype_val.comp N.continuous_originalNormalVarietyPoint
  have hp0N0 : image p0 ∈ N0 := by
    change (N.originalNormalVarietyPoint p0).1 ∈ N0
    rw [N.originalNormalVarietyPoint_center]
    exact hG0N0
  have hpreN0 : image ⁻¹' N0 ∈ 𝓝 p0 := by
    exact himage_cont.continuousAt (hN0_open.mem_nhds hp0N0)
  have hhead :
      {p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn |
        IsUnit p.head.det} ∈ 𝓝 p0 :=
    sourceOrientedNormalParameter_head_det_isUnit_mem_nhds_center d n N.r N.hrD N.hrn
  let U : Set (SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn) :=
    image ⁻¹' N0 ∩
      {p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn |
        IsUnit p.head.det}
  have hU : U ∈ 𝓝 p0 := Filter.inter_mem hpreN0 hhead
  rcases exists_sourceOrientedNormalParameterBall_subset_of_mem_nhds_center
      d n N.r N.hrD N.hrn hU with ⟨ε, hε, hεsub⟩
  rcases sourceOrientedNormalParameterBall_open_connected_center
      d n N.r N.hrD N.hrn hε with ⟨hopen, hconn, hcenter⟩
  refine ⟨ε, hε, hopen, hconn, hcenter, ?_, ?_⟩
  · intro p hp
    exact (hεsub hp).2
  · intro p hp
    have hpU := hεsub hp
    exact ⟨hpU.1, (N.originalNormalVarietyPoint p).2⟩

end SourceOrientedRankDeficientAlgebraicNormalFormData
end BHW
