import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientNormalBall
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientSchurShrink
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientTailWindow
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedHeadGaugeSupport

/-!
# Combined normal-parameter shrink for rank-deficient source patches

This file combines the independent normal-ball shrink theorems used by the
rank-deficient local-image producer.  It is still topology-only: the caller
chooses the Schur-coordinate neighborhoods and positive raw coordinate radii.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- A small normal-parameter ball can be chosen inside the full Schur
parameter window. -/
theorem exists_sourceOrientedNormalParameterBall_subset_schurParameterWindow
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    {headRadius mixedRadius : ℝ}
    (hheadRadius : 0 < headRadius)
    (hmixedRadius : 0 < mixedRadius)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn) :
    ∃ ε : ℝ,
      0 < ε ∧
        sourceOrientedNormalParameterBall (d := d) (n := n) (r := r)
          (hrD := hrD) (hrn := hrn) ε ⊆
          sourceOrientedRankDeficientSchurParameterWindow
            d n r hrD hrn headRadius mixedRadius Tail := by
  rcases sourceOrientedRankDeficientSchurParameterWindow_open_connected
      d n r hrD hrn hheadRadius hmixedRadius Tail with
    ⟨hopen, _hconn, hcenter⟩
  exact
    exists_sourceOrientedNormalParameterBall_subset_of_mem_nhds_center
      d n r hrD hrn (hopen.mem_nhds hcenter)

namespace SourceOrientedRankDeficientAlgebraicNormalFormData

/-- A single positive normal-parameter ball can be chosen to satisfy the
ambient-open image constraint, invertible-head constraint, Schur-coordinate
neighborhood constraints, and raw coordinate bounds simultaneously. -/
theorem exists_normalParameterBall_image_subset_open_head_schur_and_coordinate_bounds
    {d n : ℕ}
    {G0 : SourceOrientedGramData d n}
    (N : SourceOrientedRankDeficientAlgebraicNormalFormData d n G0)
    {N0 : Set (SourceOrientedGramData d n)}
    (hN0_open : IsOpen N0)
    (hG0N0 : G0 ∈ N0)
    {Uh : Set (Matrix (Fin N.r) (Fin N.r) ℂ)}
    (hUh : Uh ∈ 𝓝 (sourceHeadMetric d N.r N.hrD))
    {Um : Set (Matrix (Fin N.r) (Fin (n - N.r)) ℂ)}
    (hUm : Um ∈ 𝓝 (0 : Matrix (Fin N.r) (Fin (n - N.r)) ℂ))
    {Ut : Set (Matrix (Fin (n - N.r)) (Fin (n - N.r)) ℂ)}
    (hUt : Ut ∈ 𝓝 (0 : Matrix (Fin (n - N.r)) (Fin (n - N.r)) ℂ))
    {headRadius mixedRadius tailRadius : ℝ}
    (hheadRadius : 0 < headRadius)
    (hmixedRadius : 0 < mixedRadius)
    (htailRadius : 0 < tailRadius) :
    ∃ ε : ℝ,
      0 < ε ∧
        IsOpen (sourceOrientedNormalParameterBall (d := d) (n := n)
          (r := N.r) (hrD := N.hrD) (hrn := N.hrn) ε) ∧
        IsConnected (sourceOrientedNormalParameterBall (d := d) (n := n)
          (r := N.r) (hrD := N.hrD) (hrn := N.hrn) ε) ∧
        sourceOrientedNormalCenterParameter d n N.r N.hrD N.hrn ∈
          sourceOrientedNormalParameterBall (d := d) (n := n)
            (r := N.r) (hrD := N.hrD) (hrn := N.hrn) ε ∧
        sourceOrientedNormalParameterBall (d := d) (n := n)
          (r := N.r) (hrD := N.hrD) (hrn := N.hrn) ε ⊆
          {p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn |
            IsUnit p.head.det} ∧
        (∀ p,
          p ∈ sourceOrientedNormalParameterBall (d := d) (n := n)
            (r := N.r) (hrD := N.hrD) (hrn := N.hrn) ε →
            (N.originalNormalVarietyPoint p).1 ∈
              N0 ∩ sourceOrientedGramVariety d n) ∧
        sourceOrientedNormalParameterBall (d := d) (n := n)
          (r := N.r) (hrD := N.hrD) (hrn := N.hrn) ε ⊆
          {p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn |
            sourceOrientedNormalParameterSchurHead d n N.r N.hrD N.hrn p ∈ Uh ∧
              sourceOrientedNormalParameterSchurMixed d n N.r N.hrD N.hrn p ∈ Um ∧
              sourceOrientedNormalParameterSchurTail d n N.r N.hrD N.hrn p ∈ Ut} ∧
        sourceOrientedNormalParameterBall (d := d) (n := n)
          (r := N.r) (hrD := N.hrD) (hrn := N.hrn) ε ⊆
          {p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn |
            (∀ a b,
              ‖p.head a b -
                (1 : Matrix (Fin N.r) (Fin N.r) ℂ) a b‖ < headRadius) ∧
            (∀ u a, ‖p.mixed u a‖ < mixedRadius) ∧
            (∀ u μ, ‖p.tail u μ‖ < tailRadius)} := by
  rcases N.exists_normalParameterBall_image_subset_open_and_head
      hN0_open hG0N0 with
    ⟨ε₀, hε₀, _hopen₀, _hconn₀, _hcenter₀, hhead₀, himage₀⟩
  rcases exists_sourceOrientedNormalParameterBall_subset_schur_nhds
      d n N.r N.hrD N.hrn hUh hUm hUt with
    ⟨ε₁, hε₁, hschur₁⟩
  rcases exists_sourceOrientedNormalParameterBall_subset_coordinate_bounds
      d n N.r N.hrD N.hrn hheadRadius hmixedRadius htailRadius with
    ⟨ε₂, hε₂, hcoord₂⟩
  let ε : ℝ := min ε₀ (min ε₁ ε₂)
  have hε : 0 < ε := by
    exact lt_min hε₀ (lt_min hε₁ hε₂)
  have hε_le₀ : ε ≤ ε₀ := by
    dsimp [ε]
    exact min_le_left _ _
  have hε_le₁ : ε ≤ ε₁ := by
    dsimp [ε]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hε_le₂ : ε ≤ ε₂ := by
    dsimp [ε]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  rcases sourceOrientedNormalParameterBall_open_connected_center
      d n N.r N.hrD N.hrn hε with
    ⟨hopen, hconn, hcenter⟩
  refine
    ⟨ε, hε, hopen, hconn, hcenter, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact hhead₀
      (sourceOrientedNormalParameterBall_mono
        d n N.r N.hrD N.hrn hε_le₀ hp)
  · intro p hp
    exact himage₀ p
      (sourceOrientedNormalParameterBall_mono
        d n N.r N.hrD N.hrn hε_le₀ hp)
  · intro p hp
    exact hschur₁
      (sourceOrientedNormalParameterBall_mono
        d n N.r N.hrD N.hrn hε_le₁ hp)
  · intro p hp
    exact hcoord₂
      (sourceOrientedNormalParameterBall_mono
        d n N.r N.hrD N.hrn hε_le₂ hp)

/-- A single positive normal-parameter ball can also absorb the local
head-gauge chart.  The head Schur coordinate is routed through an ordinary
matrix neighborhood, then re-bundled into the symmetric subtype where the
head-gauge factor is defined. -/
theorem exists_normalParameterBall_image_subset_open_headGauge_schur_and_coordinate_bounds
    {d n : ℕ}
    {G0 : SourceOrientedGramData d n}
    (N : SourceOrientedRankDeficientAlgebraicNormalFormData d n G0)
    (Head : SourceRankDeficientHeadGaugeData d N.r N.hrD)
    {N0 : Set (SourceOrientedGramData d n)}
    (hN0_open : IsOpen N0)
    (hG0N0 : G0 ∈ N0)
    {Um : Set (Matrix (Fin N.r) (Fin (n - N.r)) ℂ)}
    (hUm : Um ∈ 𝓝 (0 : Matrix (Fin N.r) (Fin (n - N.r)) ℂ))
    {Ut : Set (Matrix (Fin (n - N.r)) (Fin (n - N.r)) ℂ)}
    (hUt : Ut ∈ 𝓝 (0 : Matrix (Fin (n - N.r)) (Fin (n - N.r)) ℂ))
    {factorRadius headRadius mixedRadius tailRadius : ℝ}
    (hfactorRadius : 0 < factorRadius)
    (hheadRadius : 0 < headRadius)
    (hmixedRadius : 0 < mixedRadius)
    (htailRadius : 0 < tailRadius) :
    ∃ ε : ℝ,
      0 < ε ∧
        IsOpen (sourceOrientedNormalParameterBall (d := d) (n := n)
          (r := N.r) (hrD := N.hrD) (hrn := N.hrn) ε) ∧
        IsConnected (sourceOrientedNormalParameterBall (d := d) (n := n)
          (r := N.r) (hrD := N.hrD) (hrn := N.hrn) ε) ∧
        sourceOrientedNormalCenterParameter d n N.r N.hrD N.hrn ∈
          sourceOrientedNormalParameterBall (d := d) (n := n)
            (r := N.r) (hrD := N.hrD) (hrn := N.hrn) ε ∧
        sourceOrientedNormalParameterBall (d := d) (n := n)
          (r := N.r) (hrD := N.hrD) (hrn := N.hrn) ε ⊆
          {p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn |
            IsUnit p.head.det} ∧
        (∀ p,
          p ∈ sourceOrientedNormalParameterBall (d := d) (n := n)
            (r := N.r) (hrD := N.hrD) (hrn := N.hrn) ε →
            (N.originalNormalVarietyPoint p).1 ∈
              N0 ∩ sourceOrientedGramVariety d n) ∧
        (∀ p,
          p ∈ sourceOrientedNormalParameterBall (d := d) (n := n)
            (r := N.r) (hrD := N.hrD) (hrn := N.hrn) ε →
            (⟨sourceOrientedNormalParameterSchurHead d n N.r N.hrD N.hrn p,
              sourceNormalHeadGram_transpose d n N.r N.hrD N.hrn p⟩ :
                SourceSymmetricMatrixCoord N.r) ∈ Head.U ∧
            ∀ a b,
              ‖Head.factor
                (⟨sourceOrientedNormalParameterSchurHead d n N.r N.hrD N.hrn p,
                  sourceNormalHeadGram_transpose d n N.r N.hrD N.hrn p⟩ :
                    SourceSymmetricMatrixCoord N.r) a b -
                  (1 : Matrix (Fin N.r) (Fin N.r) ℂ) a b‖ <
                factorRadius) ∧
        (∀ p,
          p ∈ sourceOrientedNormalParameterBall (d := d) (n := n)
            (r := N.r) (hrD := N.hrD) (hrn := N.hrn) ε →
            sourceOrientedNormalParameterSchurMixed d n N.r N.hrD N.hrn p ∈ Um ∧
              sourceOrientedNormalParameterSchurTail d n N.r N.hrD N.hrn p ∈ Ut) ∧
        sourceOrientedNormalParameterBall (d := d) (n := n)
          (r := N.r) (hrD := N.hrD) (hrn := N.hrn) ε ⊆
          {p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn |
            (∀ a b,
              ‖p.head a b -
                (1 : Matrix (Fin N.r) (Fin N.r) ℂ) a b‖ < headRadius) ∧
            (∀ u a, ‖p.mixed u a‖ < mixedRadius) ∧
            (∀ u μ, ‖p.tail u μ‖ < tailRadius)} := by
  rcases sourceRankDeficientHeadGauge_exists_matrix_nhds_factor_coordinate_bound
      d N.r N.hrD Head hfactorRadius with
    ⟨Uh, hUh, hUh_factor⟩
  rcases N.exists_normalParameterBall_image_subset_open_head_schur_and_coordinate_bounds
      hN0_open hG0N0 hUh hUm hUt hheadRadius hmixedRadius htailRadius with
    ⟨ε, hε, hopen, hconn, hcenter, hhead, himage, hschur, hcoord⟩
  refine
    ⟨ε, hε, hopen, hconn, hcenter, hhead, himage, ?_, ?_, hcoord⟩
  · intro p hp
    have hp_schur := hschur hp
    exact
      hUh_factor
        (sourceOrientedNormalParameterSchurHead d n N.r N.hrD N.hrn p)
        hp_schur.1
        (sourceNormalHeadGram_transpose d n N.r N.hrD N.hrn p)
  · intro p hp
    have hp_schur := hschur hp
    exact ⟨hp_schur.2.1, hp_schur.2.2⟩

/-- A single positive normal-parameter ball can be chosen inside the full
Schur parameter window while preserving the ambient image, invertible-head,
head-gauge, and Schur-coordinate shrink information. -/
theorem exists_normalParameterBall_image_subset_open_headGauge_schurParameterWindow
    {d n : ℕ}
    {G0 : SourceOrientedGramData d n}
    (N : SourceOrientedRankDeficientAlgebraicNormalFormData d n G0)
    (Head : SourceRankDeficientHeadGaugeData d N.r N.hrD)
    {N0 : Set (SourceOrientedGramData d n)}
    (hN0_open : IsOpen N0)
    (hG0N0 : G0 ∈ N0)
    {Um : Set (Matrix (Fin N.r) (Fin (n - N.r)) ℂ)}
    (hUm : Um ∈ 𝓝 (0 : Matrix (Fin N.r) (Fin (n - N.r)) ℂ))
    {Ut : Set (Matrix (Fin (n - N.r)) (Fin (n - N.r)) ℂ)}
    (hUt : Ut ∈ 𝓝 (0 : Matrix (Fin (n - N.r)) (Fin (n - N.r)) ℂ))
    {factorRadius headRadius mixedRadius : ℝ}
    (hfactorRadius : 0 < factorRadius)
    (hheadRadius : 0 < headRadius)
    (hmixedRadius : 0 < mixedRadius)
    (Tail : SourceOrientedRankDeficientTailWindowChoice d n N.r N.hrD N.hrn) :
    ∃ ε : ℝ,
      0 < ε ∧
        IsOpen (sourceOrientedNormalParameterBall (d := d) (n := n)
          (r := N.r) (hrD := N.hrD) (hrn := N.hrn) ε) ∧
        IsConnected (sourceOrientedNormalParameterBall (d := d) (n := n)
          (r := N.r) (hrD := N.hrD) (hrn := N.hrn) ε) ∧
        sourceOrientedNormalCenterParameter d n N.r N.hrD N.hrn ∈
          sourceOrientedNormalParameterBall (d := d) (n := n)
            (r := N.r) (hrD := N.hrD) (hrn := N.hrn) ε ∧
        sourceOrientedNormalParameterBall (d := d) (n := n)
          (r := N.r) (hrD := N.hrD) (hrn := N.hrn) ε ⊆
          {p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn |
            IsUnit p.head.det} ∧
        (∀ p,
          p ∈ sourceOrientedNormalParameterBall (d := d) (n := n)
            (r := N.r) (hrD := N.hrD) (hrn := N.hrn) ε →
            (N.originalNormalVarietyPoint p).1 ∈
              N0 ∩ sourceOrientedGramVariety d n) ∧
        (∀ p,
          p ∈ sourceOrientedNormalParameterBall (d := d) (n := n)
            (r := N.r) (hrD := N.hrD) (hrn := N.hrn) ε →
            (⟨sourceOrientedNormalParameterSchurHead d n N.r N.hrD N.hrn p,
              sourceNormalHeadGram_transpose d n N.r N.hrD N.hrn p⟩ :
                SourceSymmetricMatrixCoord N.r) ∈ Head.U ∧
            ∀ a b,
              ‖Head.factor
                (⟨sourceOrientedNormalParameterSchurHead d n N.r N.hrD N.hrn p,
                  sourceNormalHeadGram_transpose d n N.r N.hrD N.hrn p⟩ :
                    SourceSymmetricMatrixCoord N.r) a b -
                  (1 : Matrix (Fin N.r) (Fin N.r) ℂ) a b‖ <
                factorRadius) ∧
        (∀ p,
          p ∈ sourceOrientedNormalParameterBall (d := d) (n := n)
            (r := N.r) (hrD := N.hrD) (hrn := N.hrn) ε →
            sourceOrientedNormalParameterSchurMixed d n N.r N.hrD N.hrn p ∈ Um ∧
              sourceOrientedNormalParameterSchurTail d n N.r N.hrD N.hrn p ∈ Ut) ∧
        sourceOrientedNormalParameterBall (d := d) (n := n)
          (r := N.r) (hrD := N.hrD) (hrn := N.hrn) ε ⊆
          sourceOrientedRankDeficientSchurParameterWindow
            d n N.r N.hrD N.hrn headRadius mixedRadius Tail := by
  rcases N.exists_normalParameterBall_image_subset_open_headGauge_schur_and_coordinate_bounds
      Head hN0_open hG0N0 hUm hUt hfactorRadius hheadRadius hmixedRadius
      Tail.tailCoordRadius_pos with
    ⟨ε₀, hε₀, _hopen₀, _hconn₀, _hcenter₀, hhead₀, himage₀, hfactor₀,
      hschur₀, _hcoord₀⟩
  rcases exists_sourceOrientedNormalParameterBall_subset_schurParameterWindow
      d n N.r N.hrD N.hrn hheadRadius hmixedRadius Tail with
    ⟨ε₁, hε₁, hwindow₁⟩
  let ε : ℝ := min ε₀ ε₁
  have hε : 0 < ε := lt_min hε₀ hε₁
  have hε_le₀ : ε ≤ ε₀ := by
    dsimp [ε]
    exact min_le_left _ _
  have hε_le₁ : ε ≤ ε₁ := by
    dsimp [ε]
    exact min_le_right _ _
  rcases sourceOrientedNormalParameterBall_open_connected_center
      d n N.r N.hrD N.hrn hε with
    ⟨hopen, hconn, hcenter⟩
  refine ⟨ε, hε, hopen, hconn, hcenter, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact hhead₀
      (sourceOrientedNormalParameterBall_mono
        d n N.r N.hrD N.hrn hε_le₀ hp)
  · intro p hp
    exact himage₀ p
      (sourceOrientedNormalParameterBall_mono
        d n N.r N.hrD N.hrn hε_le₀ hp)
  · intro p hp
    exact hfactor₀ p
      (sourceOrientedNormalParameterBall_mono
        d n N.r N.hrD N.hrn hε_le₀ hp)
  · intro p hp
    exact hschur₀ p
      (sourceOrientedNormalParameterBall_mono
        d n N.r N.hrD N.hrn hε_le₀ hp)
  · intro p hp
    exact hwindow₁
      (sourceOrientedNormalParameterBall_mono
        d n N.r N.hrD N.hrn hε_le₁ hp)

end SourceOrientedRankDeficientAlgebraicNormalFormData
end BHW
