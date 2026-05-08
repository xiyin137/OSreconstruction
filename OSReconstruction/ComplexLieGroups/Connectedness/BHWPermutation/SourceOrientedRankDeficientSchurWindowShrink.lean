import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientNormalShrink
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientTailRankConnected
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientSliceParameter
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientLocalImageTransport
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedHeadSliceGaugeIFT

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

/-- Positive coordinate bounds forcing every sufficiently small sliced Schur
window into a prescribed sliced-neighborhood of the canonical center. -/
theorem exists_sourceOrientedRankDeficientSlicedSchurParameterWindow_coordinate_bounds_subset_of_mem_nhds_center
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n}
    {U : Set (SourceOrientedRankDeficientSlicedNormalParameter d n r hrD hrn)}
    (hU :
      U ∈ 𝓝 (sourceOrientedSlicedNormalCenterParameter d n r hrD hrn)) :
    ∃ headBound mixedBound tailBound : ℝ,
      0 < headBound ∧
        0 < mixedBound ∧
        0 < tailBound ∧
        ∀ {headRadius mixedRadius : ℝ}
          (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn),
          headRadius ≤ headBound →
          mixedRadius ≤ mixedBound →
          Tail.tailCoordRadius ≤ tailBound →
          sourceOrientedRankDeficientSlicedSchurParameterWindow
              d n r hrD hrn headRadius mixedRadius Tail ⊆ U := by
  let e :=
    sourceOrientedSlicedNormalParameterCoordHomeomorph
      (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)
  let p0 := sourceOrientedSlicedNormalCenterParameter d n r hrD hrn
  let H0 := sourceHeadGaugeSliceCenter d r hrD
  let M0 : Matrix (Fin (n - r)) (Fin r) ℂ := 0
  let T0 : Fin (n - r) → Fin (d + 1 - r) → ℂ := 0
  have hUprod : e.symm ⁻¹' U ∈ 𝓝 (H0, (M0, T0)) := by
    have hpre : e.symm ⁻¹' U ∈ 𝓝 (e p0) :=
      e.symm.continuous.continuousAt (by simpa [p0] using hU)
    simpa [e, p0, H0, M0, T0, sourceOrientedSlicedNormalParameterCoordHomeomorph,
      sourceOrientedSlicedNormalParameterCoordEquiv,
      sourceOrientedSlicedNormalParameterCoord,
      sourceOrientedSlicedNormalCenterParameter] using hpre
  rcases mem_nhds_prod_iff'.1 hUprod with
    ⟨Uh, Vmt, hUh_open, hH0_Uh, hVmt_open, hmt_Vmt, hprod_sub⟩
  have hVmt_nhds : Vmt ∈ 𝓝 (M0, T0) :=
    hVmt_open.mem_nhds hmt_Vmt
  rcases mem_nhds_prod_iff'.1 hVmt_nhds with
    ⟨Um, Ut, hUm_open, hM0_Um, hUt_open, hT0_Ut, hmt_sub⟩
  rcases exists_sourceHeadGaugeSliceCoordinateWindow_subset_of_mem_nhds_center
      d r hrD (hUh_open.mem_nhds hH0_Uh) with
    ⟨headBound, hheadBound, hhead_sub⟩
  rcases exists_sourceMatrixCoordinateWindow_subset_of_mem_nhds
      (M0 : Matrix (Fin (n - r)) (Fin r) ℂ)
      (hUm_open.mem_nhds hM0_Um) with
    ⟨mixedBound, hmixedBound, hmixed_sub⟩
  rcases exists_sourceMatrixCoordinateWindow_subset_of_mem_nhds
      (T0 : Fin (n - r) → Fin (d + 1 - r) → ℂ)
      (hUt_open.mem_nhds hT0_Ut) with
    ⟨tailBound, htailBound, htail_sub⟩
  refine
    ⟨headBound, mixedBound, tailBound, hheadBound, hmixedBound, htailBound,
      ?_⟩
  intro headRadius mixedRadius Tail hhead_le hmixed_le htail_le p hp
  have hhead_bound :
      p.head ∈ sourceHeadGaugeSliceCoordinateWindow d r hrD headBound := by
    intro a b
    exact lt_of_lt_of_le (hp.1 a b) hhead_le
  have hhead : p.head ∈ Uh := hhead_sub hhead_bound
  have hmixed_bound :
      p.mixed ∈ sourceMatrixCoordinateWindow M0 mixedBound := by
    intro u a
    have hcoord := hp.2.1 u a
    exact lt_of_lt_of_le (by simpa [sourceOrientedMixedCoordinateWindow,
      sourceMatrixCoordinateWindow, M0] using hcoord) hmixed_le
  have hmixed : p.mixed ∈ Um := hmixed_sub hmixed_bound
  have htail_bound : p.tail ∈ sourceMatrixCoordinateWindow T0 tailBound := by
    intro u μ
    have hcoord := hp.2.2.1 u μ
    exact lt_of_lt_of_le (by simpa [sourceMatrixCoordinateWindow, T0] using hcoord)
      htail_le
  have htail : p.tail ∈ Ut := htail_sub htail_bound
  have hcoord : e p ∈ Uh ×ˢ Vmt := by
    have hmt : (p.mixed, p.tail) ∈ Vmt :=
      hmt_sub (Set.mk_mem_prod hmixed htail)
    simpa [e, sourceOrientedSlicedNormalParameterCoordHomeomorph,
      sourceOrientedSlicedNormalParameterCoordEquiv,
      sourceOrientedSlicedNormalParameterCoord] using
      (Set.mk_mem_prod hhead hmt)
  have hpU : e p ∈ e.symm ⁻¹' U := hprod_sub hcoord
  simpa [e] using hpU

/-- Sliced Schur parameter windows form a neighborhood basis at the canonical
sliced center.  The tail window contributes only its raw coordinate radius for
this topological shrink; the invariant inequalities are kept for the later
Schur-image theorem. -/
theorem exists_sourceOrientedRankDeficientSlicedSchurParameterWindow_subset_of_mem_nhds_center
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n}
    {U : Set (SourceOrientedRankDeficientSlicedNormalParameter d n r hrD hrn)}
    (hU :
      U ∈ 𝓝 (sourceOrientedSlicedNormalCenterParameter d n r hrD hrn)) :
    ∃ (headRadius mixedRadius : ℝ)
      (Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn),
      0 < headRadius ∧
        0 < mixedRadius ∧
        sourceOrientedRankDeficientSlicedSchurParameterWindow
            d n r hrD hrn headRadius mixedRadius Tail ⊆ U := by
  let e :=
    sourceOrientedSlicedNormalParameterCoordHomeomorph
      (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)
  let p0 := sourceOrientedSlicedNormalCenterParameter d n r hrD hrn
  let H0 := sourceHeadGaugeSliceCenter d r hrD
  let M0 : Matrix (Fin (n - r)) (Fin r) ℂ := 0
  let T0 : Fin (n - r) → Fin (d + 1 - r) → ℂ := 0
  have hUprod : e.symm ⁻¹' U ∈ 𝓝 (H0, (M0, T0)) := by
    have hpre : e.symm ⁻¹' U ∈ 𝓝 (e p0) :=
      e.symm.continuous.continuousAt (by simpa [p0] using hU)
    simpa [e, p0, H0, M0, T0, sourceOrientedSlicedNormalParameterCoordHomeomorph,
      sourceOrientedSlicedNormalParameterCoordEquiv,
      sourceOrientedSlicedNormalParameterCoord,
      sourceOrientedSlicedNormalCenterParameter] using hpre
  rcases mem_nhds_prod_iff'.1 hUprod with
    ⟨Uh, Vmt, hUh_open, hH0_Uh, hVmt_open, hmt_Vmt, hprod_sub⟩
  have hVmt_nhds : Vmt ∈ 𝓝 (M0, T0) :=
    hVmt_open.mem_nhds hmt_Vmt
  rcases mem_nhds_prod_iff'.1 hVmt_nhds with
    ⟨Um, Ut, hUm_open, hM0_Um, hUt_open, hT0_Ut, hmt_sub⟩
  rcases exists_sourceHeadGaugeSliceCoordinateWindow_subset_of_mem_nhds_center
      d r hrD (hUh_open.mem_nhds hH0_Uh) with
    ⟨headRadius, hheadRadius, hhead_sub⟩
  rcases exists_sourceMatrixCoordinateWindow_subset_of_mem_nhds
      (M0 : Matrix (Fin (n - r)) (Fin r) ℂ)
      (hUm_open.mem_nhds hM0_Um) with
    ⟨mixedRadius, hmixedRadius, hmixed_sub⟩
  rcases exists_sourceMatrixCoordinateWindow_subset_of_mem_nhds
      (T0 : Fin (n - r) → Fin (d + 1 - r) → ℂ)
      (hUt_open.mem_nhds hT0_Ut) with
    ⟨tailRadius, htailRadius, htail_sub⟩
  let Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn :=
    sourceOriented_rankDeficient_tailWindowChoice
      d n r hrD hrn htailRadius
  refine ⟨headRadius, mixedRadius, Tail, hheadRadius, hmixedRadius, ?_⟩
  intro p hp
  have hhead : p.head ∈ Uh := hhead_sub hp.1
  have hmixed : p.mixed ∈ Um := hmixed_sub hp.2.1
  have htail_coord : p.tail ∈ sourceMatrixCoordinateWindow T0 tailRadius := by
    intro u μ
    have hcoord := hp.2.2.1 u μ
    simpa [Tail, sourceOriented_rankDeficient_tailWindowChoice,
      sourceMatrixCoordinateWindow, T0] using hcoord
  have htail : p.tail ∈ Ut := htail_sub htail_coord
  have hcoord : e p ∈ Uh ×ˢ Vmt := by
    have hmt : (p.mixed, p.tail) ∈ Vmt :=
      hmt_sub (Set.mk_mem_prod hmixed htail)
    simpa [e, sourceOrientedSlicedNormalParameterCoordHomeomorph,
      sourceOrientedSlicedNormalParameterCoordEquiv,
      sourceOrientedSlicedNormalParameterCoord] using
      (Set.mk_mem_prod hhead hmt)
  have hpU : e p ∈ e.symm ⁻¹' U := hprod_sub hcoord
  simpa [e] using hpU

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

/-- Head-domain-aware version of
`exists_schurParameterWindow_image_subset_open_head_tailRank_connected`.
It chooses the Schur head radius small enough that the entire head-coordinate
window lies in a prescribed near-identity head domain. -/
theorem exists_schurParameterWindow_image_subset_open_headDomain_tailRank_connected
    {d n : ℕ}
    {G0 : SourceOrientedGramData d n}
    (hn : d + 1 ≤ n)
    (N : SourceOrientedRankDeficientAlgebraicNormalFormData d n G0)
    {headDomain : Set (Matrix (Fin N.r) (Fin N.r) ℂ)}
    {headDomainRadius : ℝ}
    (hheadDomainRadius : 0 < headDomainRadius)
    (hheadDomain :
      sourceHeadFactorCoordinateWindow N.r headDomainRadius ⊆ headDomain)
    {N0 : Set (SourceOrientedGramData d n)}
    (hN0_open : IsOpen N0)
    (hG0N0 : G0 ∈ N0) :
    ∃ (headRadius mixedRadius : ℝ)
      (Tail : SourceOrientedRankDeficientTailWindowChoice d n N.r N.hrD N.hrn),
      0 < headRadius ∧
        0 < mixedRadius ∧
        sourceOrientedHeadCoordinateWindow N.r headRadius ⊆ headDomain ∧
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
    ⟨ε₀, hε₀, _hball_open, _hball_conn, _hball_center, hball_head,
      hball_image⟩
  let δ : ℝ := headDomainRadius
  have hδ : 0 < δ := hheadDomainRadius
  let ε : ℝ := min ε₀ δ
  have hε : 0 < ε := lt_min hε₀ hδ
  have hε_le₀ : ε ≤ ε₀ := by
    dsimp [ε]
    exact min_le_left _ _
  have hε_leδ : ε ≤ δ := by
    dsimp [ε]
    exact min_le_right _ _
  let ρ : ℝ := ε / 2
  have hρ_pos : 0 < ρ := by
    positivity
  have hρ_le_ε : ρ ≤ ε := by
    dsimp [ρ]
    linarith
  have hρ_le₀ : ρ ≤ ε₀ := le_trans hρ_le_ε hε_le₀
  have hρ_leδ : ρ ≤ δ := le_trans hρ_le_ε hε_leδ
  let Tail : SourceOrientedRankDeficientTailWindowChoice d n N.r N.hrD N.hrn :=
    sourceOriented_rankDeficient_tailWindowChoice
      d n N.r N.hrD N.hrn hρ_pos
  have htail_le : Tail.tailCoordRadius ≤ ε₀ := by
    simpa [Tail, sourceOriented_rankDeficient_tailWindowChoice] using hρ_le₀
  let W : Set (SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn) :=
    sourceOrientedRankDeficientSchurParameterWindow
      d n N.r N.hrD N.hrn ρ ρ Tail
  have hW_headDomain : sourceOrientedHeadCoordinateWindow N.r ρ ⊆ headDomain := by
    intro H hH
    exact hheadDomain (by
      intro a b
      exact lt_of_lt_of_le (hH a b) hρ_leδ)
  have hW_sub_ball :
      W ⊆
        sourceOrientedNormalParameterBall (d := d) (n := n) (r := N.r)
          (hrD := N.hrD) (hrn := N.hrn) ε₀ := by
    exact
      sourceOrientedRankDeficientSchurParameterWindow_subset_normalParameterBall
        d n N.r N.hrD N.hrn hε₀ hρ_le₀ hρ_le₀ Tail htail_le
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
    ⟨ρ, ρ, Tail, hρ_pos, hρ_pos, hW_headDomain, hW_open, hW_conn,
      hW_center, ?_, ?_, ?_⟩
  · intro p hp
    exact hball_head (hW_sub_ball hp)
  · intro p hp
    exact hball_image p (hW_sub_ball hp)
  · simpa [W] using hW_tailRank_conn

/-- Sliced-head-domain version of
`exists_schurParameterWindow_image_subset_open_headDomain_tailRank_connected`.
The chosen parameter space is the genuine sliced Schur window; the old normal
ball estimates are consumed after forgetting the slice proof on the head. -/
theorem exists_slicedSchurParameterWindow_image_subset_open_headDomain_tailRank_connected
    {d n : ℕ}
    {G0 : SourceOrientedGramData d n}
    (hn : d + 1 ≤ n)
    (N : SourceOrientedRankDeficientAlgebraicNormalFormData d n G0)
    {headDomain : Set (SourceHeadGaugeSlice d N.r N.hrD)}
    {headDomainRadius : ℝ}
    (hheadDomainRadius : 0 < headDomainRadius)
    (hheadDomain :
      sourceHeadGaugeSliceCoordinateWindow d N.r N.hrD headDomainRadius ⊆
        headDomain)
    {N0 : Set (SourceOrientedGramData d n)}
    (hN0_open : IsOpen N0)
    (hG0N0 : G0 ∈ N0) :
    ∃ (headRadius mixedRadius : ℝ)
      (Tail : SourceOrientedRankDeficientTailWindowChoice d n N.r N.hrD N.hrn),
      0 < headRadius ∧
        0 < mixedRadius ∧
        sourceHeadGaugeSliceCoordinateWindow d N.r N.hrD headRadius ⊆
          headDomain ∧
        IsOpen
          (sourceOrientedRankDeficientSlicedSchurParameterWindow
            d n N.r N.hrD N.hrn headRadius mixedRadius Tail) ∧
        IsConnected
          (sourceOrientedRankDeficientSlicedSchurParameterWindow
            d n N.r N.hrD N.hrn headRadius mixedRadius Tail) ∧
        sourceOrientedSlicedNormalCenterParameter d n N.r N.hrD N.hrn ∈
          sourceOrientedRankDeficientSlicedSchurParameterWindow
            d n N.r N.hrD N.hrn headRadius mixedRadius Tail ∧
        (∀ p,
          p ∈ sourceOrientedRankDeficientSlicedSchurParameterWindow
            d n N.r N.hrD N.hrn headRadius mixedRadius Tail →
          IsUnit p.toNormalParameter.head.det) ∧
        (∀ p,
          p ∈ sourceOrientedRankDeficientSlicedSchurParameterWindow
            d n N.r N.hrD N.hrn headRadius mixedRadius Tail →
            (N.originalNormalVarietyPoint p.toNormalParameter).1 ∈
              N0 ∩ sourceOrientedGramVariety d n) ∧
        IsConnected
          (sourceOrientedRankDeficientSlicedSchurParameterWindow
              d n N.r N.hrD N.hrn headRadius mixedRadius Tail ∩
            {p : SourceOrientedRankDeficientSlicedNormalParameter d n N.r N.hrD N.hrn |
              (sourceOrientedNormalParameterSchurTail d n N.r N.hrD N.hrn
                p.toNormalParameter).rank =
                d + 1 - N.r}) := by
  rcases N.exists_normalParameterBall_image_subset_open_and_head
      hN0_open hG0N0 with
    ⟨ε₀, hε₀, _hball_open, _hball_conn, _hball_center, hball_head,
      hball_image⟩
  let δ : ℝ := headDomainRadius
  have hδ : 0 < δ := hheadDomainRadius
  let ε : ℝ := min ε₀ δ
  have hε : 0 < ε := lt_min hε₀ hδ
  have hε_le₀ : ε ≤ ε₀ := by
    dsimp [ε]
    exact min_le_left _ _
  have hε_leδ : ε ≤ δ := by
    dsimp [ε]
    exact min_le_right _ _
  let ρ : ℝ := ε / 2
  have hρ_pos : 0 < ρ := by
    positivity
  have hρ_le_ε : ρ ≤ ε := by
    dsimp [ρ]
    linarith
  have hρ_le₀ : ρ ≤ ε₀ := le_trans hρ_le_ε hε_le₀
  have hρ_leδ : ρ ≤ δ := le_trans hρ_le_ε hε_leδ
  let Tail : SourceOrientedRankDeficientTailWindowChoice d n N.r N.hrD N.hrn :=
    sourceOriented_rankDeficient_tailWindowChoice
      d n N.r N.hrD N.hrn hρ_pos
  have htail_le : Tail.tailCoordRadius ≤ ε₀ := by
    simpa [Tail, sourceOriented_rankDeficient_tailWindowChoice] using hρ_le₀
  let W : Set (SourceOrientedRankDeficientSlicedNormalParameter d n N.r N.hrD N.hrn) :=
    sourceOrientedRankDeficientSlicedSchurParameterWindow
      d n N.r N.hrD N.hrn ρ ρ Tail
  have hW_headDomain :
      sourceHeadGaugeSliceCoordinateWindow d N.r N.hrD ρ ⊆ headDomain := by
    intro H hH
    exact hheadDomain (by
      intro a b
      exact lt_of_lt_of_le (hH a b) hρ_leδ)
  have hW_sub_ball :
      ∀ p ∈ W,
        p.toNormalParameter ∈
          sourceOrientedNormalParameterBall (d := d) (n := n) (r := N.r)
            (hrD := N.hrD) (hrn := N.hrn) ε₀ := by
    intro p hp
    exact
      sourceOrientedRankDeficientSchurParameterWindow_subset_normalParameterBall
        d n N.r N.hrD N.hrn hε₀ hρ_le₀ hρ_le₀ Tail htail_le
        (sourceOrientedSlicedSchurParameterWindow_toNormalParameter_mem hp)
  rcases sourceOrientedRankDeficientSlicedSchurParameterWindow_open_connected
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
          {p : SourceOrientedRankDeficientSlicedNormalParameter d n N.r N.hrD N.hrn |
            (sourceOrientedNormalParameterSchurTail d n N.r N.hrD N.hrn
              p.toNormalParameter).rank =
              d + 1 - N.r}) := by
    exact
      isConnected_sourceOrientedRankDeficientSlicedSchurParameterWindow_tailRank
        d n N.r N.hrD N.hrn hρ_pos hρ_pos Tail htailRank_conn
  refine
    ⟨ρ, ρ, Tail, hρ_pos, hρ_pos, hW_headDomain, hW_open, hW_conn,
      hW_center, ?_, ?_, ?_⟩
  · intro p hp
    exact hball_head (hW_sub_ball p hp)
  · intro p hp
    exact hball_image p.toNormalParameter (hW_sub_ball p hp)
  · simpa [W] using hW_tailRank_conn

/-- Sliced Schur-window shrink with an additional sliced-parameter
neighborhood constraint.  This is the topology packet needed to make the
finite-coordinate Schur image `e '' W` lie inside a prechosen compact
tube-control ball. -/
theorem exists_slicedSchurParameterWindow_subset_nhds_image_subset_open_headDomain_tailRank_connected
    {d n : ℕ}
    {G0 : SourceOrientedGramData d n}
    (hn : d + 1 ≤ n)
    (N : SourceOrientedRankDeficientAlgebraicNormalFormData d n G0)
    {U : Set (SourceOrientedRankDeficientSlicedNormalParameter d n N.r N.hrD N.hrn)}
    (hU :
      U ∈ 𝓝 (sourceOrientedSlicedNormalCenterParameter d n N.r N.hrD N.hrn))
    {headDomain : Set (SourceHeadGaugeSlice d N.r N.hrD)}
    {headDomainRadius : ℝ}
    (hheadDomainRadius : 0 < headDomainRadius)
    (hheadDomain :
      sourceHeadGaugeSliceCoordinateWindow d N.r N.hrD headDomainRadius ⊆
        headDomain)
    {N0 : Set (SourceOrientedGramData d n)}
    (hN0_open : IsOpen N0)
    (hG0N0 : G0 ∈ N0) :
    ∃ (headRadius mixedRadius : ℝ)
      (Tail : SourceOrientedRankDeficientTailWindowChoice d n N.r N.hrD N.hrn),
      0 < headRadius ∧
        0 < mixedRadius ∧
        sourceHeadGaugeSliceCoordinateWindow d N.r N.hrD headRadius ⊆
          headDomain ∧
        IsOpen
          (sourceOrientedRankDeficientSlicedSchurParameterWindow
            d n N.r N.hrD N.hrn headRadius mixedRadius Tail) ∧
        IsConnected
          (sourceOrientedRankDeficientSlicedSchurParameterWindow
            d n N.r N.hrD N.hrn headRadius mixedRadius Tail) ∧
        sourceOrientedSlicedNormalCenterParameter d n N.r N.hrD N.hrn ∈
          sourceOrientedRankDeficientSlicedSchurParameterWindow
            d n N.r N.hrD N.hrn headRadius mixedRadius Tail ∧
        sourceOrientedRankDeficientSlicedSchurParameterWindow
            d n N.r N.hrD N.hrn headRadius mixedRadius Tail ⊆ U ∧
        (∀ p,
          p ∈ sourceOrientedRankDeficientSlicedSchurParameterWindow
            d n N.r N.hrD N.hrn headRadius mixedRadius Tail →
          IsUnit p.toNormalParameter.head.det) ∧
        (∀ p,
          p ∈ sourceOrientedRankDeficientSlicedSchurParameterWindow
            d n N.r N.hrD N.hrn headRadius mixedRadius Tail →
            (N.originalNormalVarietyPoint p.toNormalParameter).1 ∈
              N0 ∩ sourceOrientedGramVariety d n) ∧
        IsConnected
          (sourceOrientedRankDeficientSlicedSchurParameterWindow
              d n N.r N.hrD N.hrn headRadius mixedRadius Tail ∩
            {p : SourceOrientedRankDeficientSlicedNormalParameter d n N.r N.hrD N.hrn |
              (sourceOrientedNormalParameterSchurTail d n N.r N.hrD N.hrn
                p.toNormalParameter).rank =
                d + 1 - N.r}) := by
  rcases N.exists_normalParameterBall_image_subset_open_and_head
      hN0_open hG0N0 with
    ⟨ε₀, hε₀, _hball_open, _hball_conn, _hball_center, hball_head,
      hball_image⟩
  rcases
      exists_sourceOrientedRankDeficientSlicedSchurParameterWindow_coordinate_bounds_subset_of_mem_nhds_center
        (d := d) (n := n) (r := N.r) (hrD := N.hrD) (hrn := N.hrn) hU with
    ⟨headBound, mixedBound, tailBound, hheadBound, hmixedBound, htailBound,
      hbounds_sub⟩
  let δ : ℝ := headDomainRadius
  have hδ : 0 < δ := hheadDomainRadius
  let ρ : ℝ :=
    min (ε₀ / 2)
      (min (δ / 2)
        (min (headBound / 2) (min (mixedBound / 2) (tailBound / 2))))
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    exact
      lt_min (half_pos hε₀)
        (lt_min (half_pos hδ)
          (lt_min (half_pos hheadBound)
            (lt_min (half_pos hmixedBound) (half_pos htailBound))))
  have hρ_le₀ : ρ ≤ ε₀ := by
    dsimp [ρ]
    exact le_trans (min_le_left _ _) (by linarith)
  have hρ_leδ : ρ ≤ δ := by
    dsimp [ρ]
    exact le_trans (le_trans (min_le_right _ _) (min_le_left _ _)) (by linarith)
  have hρ_le_head : ρ ≤ headBound := by
    dsimp [ρ]
    exact
      le_trans
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
        (by linarith)
  have hρ_le_mixed : ρ ≤ mixedBound := by
    dsimp [ρ]
    exact
      le_trans
        (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
        (by linarith)
  have hρ_le_tail : ρ ≤ tailBound := by
    dsimp [ρ]
    exact
      le_trans
        (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
        (by linarith)
  let Tail : SourceOrientedRankDeficientTailWindowChoice d n N.r N.hrD N.hrn :=
    sourceOriented_rankDeficient_tailWindowChoice
      d n N.r N.hrD N.hrn hρ_pos
  have htail_le₀ : Tail.tailCoordRadius ≤ ε₀ := by
    simpa [Tail, sourceOriented_rankDeficient_tailWindowChoice] using hρ_le₀
  have htail_le_bound : Tail.tailCoordRadius ≤ tailBound := by
    simpa [Tail, sourceOriented_rankDeficient_tailWindowChoice] using hρ_le_tail
  let W : Set (SourceOrientedRankDeficientSlicedNormalParameter d n N.r N.hrD N.hrn) :=
    sourceOrientedRankDeficientSlicedSchurParameterWindow
      d n N.r N.hrD N.hrn ρ ρ Tail
  have hW_headDomain :
      sourceHeadGaugeSliceCoordinateWindow d N.r N.hrD ρ ⊆ headDomain := by
    intro H hH
    exact hheadDomain (by
      intro a b
      exact lt_of_lt_of_le (hH a b) hρ_leδ)
  have hW_sub_U : W ⊆ U := by
    exact hbounds_sub Tail hρ_le_head hρ_le_mixed htail_le_bound
  have hW_sub_ball :
      ∀ p ∈ W,
        p.toNormalParameter ∈
          sourceOrientedNormalParameterBall (d := d) (n := n) (r := N.r)
            (hrD := N.hrD) (hrn := N.hrn) ε₀ := by
    intro p hp
    exact
      sourceOrientedRankDeficientSchurParameterWindow_subset_normalParameterBall
        d n N.r N.hrD N.hrn hε₀ hρ_le₀ hρ_le₀ Tail htail_le₀
        (sourceOrientedSlicedSchurParameterWindow_toNormalParameter_mem hp)
  rcases sourceOrientedRankDeficientSlicedSchurParameterWindow_open_connected
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
          {p : SourceOrientedRankDeficientSlicedNormalParameter d n N.r N.hrD N.hrn |
            (sourceOrientedNormalParameterSchurTail d n N.r N.hrD N.hrn
              p.toNormalParameter).rank =
              d + 1 - N.r}) := by
    exact
      isConnected_sourceOrientedRankDeficientSlicedSchurParameterWindow_tailRank
        d n N.r N.hrD N.hrn hρ_pos hρ_pos Tail htailRank_conn
  refine
    ⟨ρ, ρ, Tail, hρ_pos, hρ_pos, hW_headDomain, hW_open, hW_conn,
      hW_center, hW_sub_U, ?_, ?_, ?_⟩
  · intro p hp
    exact hball_head (hW_sub_ball p hp)
  · intro p hp
    exact hball_image p.toNormalParameter (hW_sub_ball p hp)
  · simpa [W] using hW_tailRank_conn

/-- If the head-coordinate part of a Schur window is contained in the
near-identity factor domain of a head gauge, then on that window the
gauge-selected residual tail of a normal image is exactly the stored shifted
tail invariant.  This is the forward-inclusion bridge needed by the canonical
normal-image theorem. -/
theorem schurWindow_normalParameter_headGauge_residualTail_eq
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n}
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    {headRadius mixedRadius : ℝ}
    {Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn}
    (hdomain :
      sourceOrientedHeadCoordinateWindow r headRadius ⊆ Head.factorDomain)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (hp :
      p ∈ sourceOrientedRankDeficientSchurParameterWindow
        d n r hrD hrn headRadius mixedRadius Tail) :
    sourceOrientedSchurResidualTailData d n r hrD hrn
        (sourceOrientedMinkowskiInvariant d n
          (sourceOrientedNormalParameterVector d n r hrD hrn p))
        (Head.factor
          (sourceOrientedSchurHeadBlockSymm d n r hrD hrn
            (G := sourceOrientedMinkowskiInvariant d n
              (sourceOrientedNormalParameterVector d n r hrD hrn p))
            ⟨sourceOrientedNormalParameterVector d n r hrD hrn p, rfl⟩)) =
      sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail := by
  exact
    sourceOrientedSchurResidualTailData_normalParameter_headGauge
      d n r hrD hrn Head p (hdomain hp.1)

/-- On a Schur window contained in the head-gauge factor domain, the extracted
Schur mixed coefficient of a normal image is the stored mixed coordinate. -/
theorem schurWindow_normalParameter_headGauge_mixedCoeff_eq
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n}
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    {headRadius mixedRadius : ℝ}
    {Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn}
    (hdomain :
      sourceOrientedHeadCoordinateWindow r headRadius ⊆ Head.factorDomain)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (hp :
      p ∈ sourceOrientedRankDeficientSchurParameterWindow
        d n r hrD hrn headRadius mixedRadius Tail) :
    sourceSchurMixedCoeff n r hrn
        (sourceOrientedMinkowskiInvariant d n
          (sourceOrientedNormalParameterVector d n r hrD hrn p))
        (sourceOrientedSchurHeadBlock n r hrn
          (sourceOrientedMinkowskiInvariant d n
            (sourceOrientedNormalParameterVector d n r hrD hrn p))) =
      p.mixed := by
  exact
    sourceSchurMixedCoeff_normalParameter_headGauge
      d n r hrD hrn Head p (hdomain hp.1)

/-- Membership form of
`schurWindow_normalParameter_headGauge_residualTail_eq`. -/
theorem schurWindow_normalParameter_headGauge_residualTail_mem_variety
    {d n r : ℕ}
    {hrD : r < d + 1}
    {hrn : r ≤ n}
    (Head : SourceRankDeficientHeadGaugeData d r hrD)
    {headRadius mixedRadius : ℝ}
    {Tail : SourceOrientedRankDeficientTailWindowChoice d n r hrD hrn}
    (hdomain :
      sourceOrientedHeadCoordinateWindow r headRadius ⊆ Head.factorDomain)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (hp :
      p ∈ sourceOrientedRankDeficientSchurParameterWindow
        d n r hrD hrn headRadius mixedRadius Tail) :
    sourceOrientedSchurResidualTailData d n r hrD hrn
        (sourceOrientedMinkowskiInvariant d n
          (sourceOrientedNormalParameterVector d n r hrD hrn p))
        (Head.factor
          (sourceOrientedSchurHeadBlockSymm d n r hrD hrn
            (G := sourceOrientedMinkowskiInvariant d n
              (sourceOrientedNormalParameterVector d n r hrD hrn p))
            ⟨sourceOrientedNormalParameterVector d n r hrD hrn p, rfl⟩)) ∈
      sourceShiftedTailOrientedVariety d r hrD (n - r) := by
  refine ⟨p.tail, ?_⟩
  exact
    (schurWindow_normalParameter_headGauge_residualTail_eq
      Head hdomain p hp).symm

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

/-- Sliced-head-gauge assembly of the strengthened rank-deficient local-image
packet.  This is the constructible replacement for the legacy ambient
head-gauge assembly: the parameter space is the sliced Schur window, and the
canonical-image input receives the slice-domain radius containment explicitly. -/
noncomputable def maxRankLocalImageData_of_slicedSchurWindowCanonicalImage
    {d n : ℕ}
    {G0 : SourceOrientedGramData d n}
    (hn : d + 1 ≤ n)
    (N : SourceOrientedRankDeficientAlgebraicNormalFormData d n G0)
    (Head : SourceRankDeficientHeadSliceGaugeData d N.r N.hrD)
    {N0 : Set (SourceOrientedGramData d n)}
    (hN0_open : IsOpen N0)
    (hG0N0 : G0 ∈ N0)
    (hcanonical :
      ∀ {headRadius mixedRadius : ℝ}
        {Tail : SourceOrientedRankDeficientTailWindowChoice d n N.r N.hrD N.hrn},
        0 < headRadius →
          0 < mixedRadius →
            sourceHeadGaugeSliceCoordinateWindow d N.r N.hrD headRadius ⊆
              Head.factorDomain →
              ∃ Ω : Set (SourceOrientedVariety d n),
                IsOpen Ω ∧
                  Ω ⊆
                    sourceOrientedSlicedNormalParameterVarietyPoint
                        d n N.r N.hrD N.hrn ''
                      sourceOrientedRankDeficientSlicedSchurParameterWindow
                        d n N.r N.hrD N.hrn headRadius mixedRadius Tail ∧
                  (∀ p,
                    p ∈ sourceOrientedRankDeficientSlicedSchurParameterWindow
                      d n N.r N.hrD N.hrn headRadius mixedRadius Tail →
                    sourceOrientedSlicedNormalParameterVarietyPoint
                      d n N.r N.hrD N.hrn p ∈ Ω)) :
    Σ P : Type, Σ _ : TopologicalSpace P,
      SourceOrientedRankDeficientMaxRankLocalImageData
        (d := d) (n := n) (P := P) G0 N0 := by
  let hdomain_exists := Head.factorDomain_coordinate
  let headDomainRadius := Classical.choose hdomain_exists
  let hdomain_spec := Classical.choose_spec hdomain_exists
  let hshrink_exists :=
    N.exists_slicedSchurParameterWindow_image_subset_open_headDomain_tailRank_connected
      hn (headDomain := Head.factorDomain)
      (headDomainRadius := headDomainRadius)
      hdomain_spec.1 hdomain_spec.2 hN0_open hG0N0
  let headRadius := Classical.choose hshrink_exists
  let hshrink_exists₁ := Classical.choose_spec hshrink_exists
  let mixedRadius := Classical.choose hshrink_exists₁
  let hshrink_exists₂ := Classical.choose_spec hshrink_exists₁
  let Tail := Classical.choose hshrink_exists₂
  let hshrink := Classical.choose_spec hshrink_exists₂
  rcases hshrink with
    ⟨hheadRadius, hmixedRadius, hdomain, hW_open, hW_conn, hcenter,
      hhead, himage, htailRank_conn⟩
  let W : Set (SourceOrientedRankDeficientSlicedNormalParameter d n N.r N.hrD N.hrn) :=
    sourceOrientedRankDeficientSlicedSchurParameterWindow
      d n N.r N.hrD N.hrn headRadius mixedRadius Tail
  let hcanonical_exists :=
    hcanonical (headRadius := headRadius) (mixedRadius := mixedRadius)
      (Tail := Tail) hheadRadius hmixedRadius hdomain
  let Ω := Classical.choose hcanonical_exists
  let hcanonical_spec := Classical.choose_spec hcanonical_exists
  have hΩ_open : IsOpen Ω := hcanonical_spec.1
  have hsurj :
      Ω ⊆
        sourceOrientedSlicedNormalParameterVarietyPoint
            d n N.r N.hrD N.hrn '' W := by
    simpa [W] using hcanonical_spec.2.1
  have hmem :
      ∀ p, p ∈ W →
        sourceOrientedSlicedNormalParameterVarietyPoint
          d n N.r N.hrD N.hrn p ∈ Ω := by
    simpa [W] using hcanonical_spec.2.2
  let imageV :
      SourceOrientedRankDeficientSlicedNormalParameter d n N.r N.hrD N.hrn →
        SourceOrientedVariety d n :=
    fun p =>
      N.varietyTransport.invFun
        (sourceOrientedSlicedNormalParameterVarietyPoint
          d n N.r N.hrD N.hrn p)
  have himage_eq :
      imageV '' W = N.varietyTransport.invFun '' Ω := by
    simpa [imageV] using
      (sourceOrientedVarietyTransport_invFun_image_eq
        (d := d) (n := n) N.varietyTransport
        (α := SourceOrientedRankDeficientSlicedNormalParameter
          d n N.r N.hrD N.hrn)
        (Ω := Ω) (s := W)
        (f := sourceOrientedSlicedNormalParameterVarietyPoint
          d n N.r N.hrD N.hrn)
        hsurj hmem)
  have hcont_imageV : Continuous imageV :=
    N.varietyTransport.continuous_invFun.comp
      (continuous_sourceOrientedSlicedNormalParameterVarietyPoint
        d n N.r N.hrD N.hrn)
  have hcenter_eq :
      (imageV (sourceOrientedSlicedNormalCenterParameter
        d n N.r N.hrD N.hrn)).1 = G0 := by
    simpa [imageV, sourceOrientedSlicedNormalParameterVarietyPoint,
      SourceOrientedRankDeficientAlgebraicNormalFormData.originalNormalVarietyPoint]
      using N.originalNormalVarietyPoint_center
  have himage_sub :
      sourceOrientedVarietyUnderlyingSet d n (imageV '' W) ⊆
        N0 ∩ sourceOrientedGramVariety d n := by
    rw [sourceOrientedVarietyUnderlyingSet_image]
    intro G hG
    rcases hG with ⟨p, hp, hGp⟩
    rw [← hGp]
    simpa [imageV,
      SourceOrientedRankDeficientAlgebraicNormalFormData.originalNormalVarietyPoint,
      sourceOrientedSlicedNormalParameterVarietyPoint] using himage p hp
  have hpre_eq :
      W ∩ {p |
          SourceOrientedMaxRankAt d n (imageV p).1} =
        W ∩ {p |
          (sourceOrientedNormalParameterSchurTail
            d n N.r N.hrD N.hrn p.toNormalParameter).rank =
            d + 1 - N.r} := by
    ext p
    constructor
    · rintro ⟨hp, hmax⟩
      exact
        ⟨hp,
          (N.originalNormalVarietyPoint_maxRank_iff_tail_rank
            hn p.toNormalParameter (hhead p hp)).1 (by
              simpa [imageV,
                SourceOrientedRankDeficientAlgebraicNormalFormData.originalNormalVarietyPoint,
                sourceOrientedSlicedNormalParameterVarietyPoint] using hmax)⟩
    · rintro ⟨hp, hrank⟩
      have hmax :
          SourceOrientedMaxRankAt d n
            (N.originalNormalVarietyPoint p.toNormalParameter).1 :=
        (N.originalNormalVarietyPoint_maxRank_iff_tail_rank
          hn p.toNormalParameter (hhead p hp)).2 hrank
      exact
        ⟨hp, by
          simpa [imageV,
            SourceOrientedRankDeficientAlgebraicNormalFormData.originalNormalVarietyPoint,
            sourceOrientedSlicedNormalParameterVarietyPoint] using hmax⟩
  have hpre_connected :
      IsConnected
        (W ∩ {p |
          SourceOrientedMaxRankAt d n (imageV p).1}) := by
    rw [hpre_eq]
    simpa [W, headRadius, mixedRadius, Tail] using htailRank_conn
  refine
    ⟨SourceOrientedRankDeficientSlicedNormalParameter d n N.r N.hrD N.hrn,
      inferInstance, ?_⟩
  exact
    SourceOrientedRankDeficientMaxRankLocalImageData.ofSubtype
      (d := d) (n := n)
      hW_open hW_conn hcenter
      hcont_imageV.continuousOn
      hcenter_eq
      (by
        rw [himage_eq]
        exact N.varietyTransport.isOpen_invFun_image hΩ_open)
      himage_sub
      hpre_connected

/-- Head-gauge-aware assembly of the strengthened rank-deficient local-image
packet.  This is the honest surface for the canonical Schur/residual image
theorem: the chosen Schur window is first shrunk so its head-coordinate window
lies in `Head.factorDomain`, and the canonical-image input receives that
domain containment explicitly. -/
noncomputable def maxRankLocalImageData_of_headGaugeSchurWindowCanonicalImage
    {d n : ℕ}
    {G0 : SourceOrientedGramData d n}
    (hn : d + 1 ≤ n)
    (N : SourceOrientedRankDeficientAlgebraicNormalFormData d n G0)
    (Head : SourceRankDeficientHeadGaugeData d N.r N.hrD)
    {N0 : Set (SourceOrientedGramData d n)}
    (hN0_open : IsOpen N0)
    (hG0N0 : G0 ∈ N0)
    (hcanonical :
      ∀ {headRadius mixedRadius : ℝ}
        {Tail : SourceOrientedRankDeficientTailWindowChoice d n N.r N.hrD N.hrn},
        0 < headRadius →
          0 < mixedRadius →
            sourceOrientedHeadCoordinateWindow N.r headRadius ⊆
              Head.factorDomain →
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
  let hdomain_exists := Head.factorDomain_coordinate
  let headDomainRadius := Classical.choose hdomain_exists
  let hdomain_spec := Classical.choose_spec hdomain_exists
  let hshrink_exists :=
    N.exists_schurParameterWindow_image_subset_open_headDomain_tailRank_connected
      hn (headDomain := Head.factorDomain)
      (headDomainRadius := headDomainRadius)
      hdomain_spec.1 hdomain_spec.2 hN0_open hG0N0
  let headRadius := Classical.choose hshrink_exists
  let hshrink_exists₁ := Classical.choose_spec hshrink_exists
  let mixedRadius := Classical.choose hshrink_exists₁
  let hshrink_exists₂ := Classical.choose_spec hshrink_exists₁
  let Tail := Classical.choose hshrink_exists₂
  let hshrink := Classical.choose_spec hshrink_exists₂
  have hheadRadius : 0 < headRadius := hshrink.1
  have hmixedRadius : 0 < mixedRadius := hshrink.2.1
  have hdomain :
      sourceOrientedHeadCoordinateWindow N.r headRadius ⊆ Head.factorDomain :=
    hshrink.2.2.1
  have hW_open :
      IsOpen
        (sourceOrientedRankDeficientSchurParameterWindow
          d n N.r N.hrD N.hrn headRadius mixedRadius Tail) :=
    hshrink.2.2.2.1
  have hW_conn :
      IsConnected
        (sourceOrientedRankDeficientSchurParameterWindow
          d n N.r N.hrD N.hrn headRadius mixedRadius Tail) :=
    hshrink.2.2.2.2.1
  have hcenter :
      sourceOrientedNormalCenterParameter d n N.r N.hrD N.hrn ∈
        sourceOrientedRankDeficientSchurParameterWindow
          d n N.r N.hrD N.hrn headRadius mixedRadius Tail :=
    hshrink.2.2.2.2.2.1
  have hhead :
      sourceOrientedRankDeficientSchurParameterWindow
          d n N.r N.hrD N.hrn headRadius mixedRadius Tail ⊆
        {p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn |
          IsUnit p.head.det} :=
    hshrink.2.2.2.2.2.2.1
  have himage :
      ∀ p,
        p ∈ sourceOrientedRankDeficientSchurParameterWindow
          d n N.r N.hrD N.hrn headRadius mixedRadius Tail →
          (N.originalNormalVarietyPoint p).1 ∈
            N0 ∩ sourceOrientedGramVariety d n :=
    hshrink.2.2.2.2.2.2.2.1
  have htailRank_conn :
      IsConnected
        (sourceOrientedRankDeficientSchurParameterWindow
            d n N.r N.hrD N.hrn headRadius mixedRadius Tail ∩
          {p : SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn |
            (sourceOrientedNormalParameterSchurTail d n N.r N.hrD N.hrn p).rank =
              d + 1 - N.r}) :=
    hshrink.2.2.2.2.2.2.2.2
  let W : Set (SourceOrientedRankDeficientNormalParameter d n N.r N.hrD N.hrn) :=
    sourceOrientedRankDeficientSchurParameterWindow
      d n N.r N.hrD N.hrn headRadius mixedRadius Tail
  let hcanonical_exists :=
    hcanonical (headRadius := headRadius) (mixedRadius := mixedRadius)
      (Tail := Tail) hheadRadius hmixedRadius hdomain
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
