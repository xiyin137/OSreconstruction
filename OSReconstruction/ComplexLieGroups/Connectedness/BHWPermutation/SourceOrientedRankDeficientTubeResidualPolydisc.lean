import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRankDeficientCanonicalImage
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedSlicedNormalParameterFinCoord
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedMaxRankIdentity
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedShiftedTailDensity

/-!
# Rank-deficient tube residual-polydisc assembly

This file assembles the rank-deficient tube-valued residual polydisc from the
checked sliced Schur window, finite-coordinate tube shrink, original-coordinate
variety transport, and all-arity max-rank density support.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW
namespace SourceOrientedRankDeficientNormalFormData

/-- Max-rank density in original coordinates for a sliced Schur window.  The
head and mixed coordinates are held fixed, shifted-tail max-rank parameters
are chosen densely in the tail fiber, and the checked tail/max-rank bridge
converts this to original-coordinate max rank. -/
theorem slicedSchurWindow_originalMaxRank_dense
    {d n : ℕ}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (N : SourceOrientedRankDeficientNormalFormData d n z0)
    {W :
      Set (SourceOrientedRankDeficientSlicedNormalParameter
        d n N.r N.hrD N.hrn)}
    (hW_open : IsOpen W)
    (hhead : ∀ p, p ∈ W → IsUnit p.toNormalParameter.head.det) :
    let e :=
      sourceOrientedSlicedNormalParameterFinCoordHomeomorph
        (d := d) (n := n) (r := N.r) (hrD := N.hrD) (hrn := N.hrn)
    let image :
        (Fin (sourceOrientedSlicedNormalParameterFinCoordDim d n N.r) → ℂ) →
          SourceOrientedGramData d n :=
      fun c =>
        sourceOrientedMinkowskiInvariant d n
          (N.toOriginal
            (sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn
              ((e.symm c).toNormalParameter)))
    ∀ c, c ∈ e '' W →
      image c ∈ closure
        (image ''
          {c' | c' ∈ e '' W ∧ SourceOrientedMaxRankAt d n (image c')}) := by
  classical
  intro e image c hc
  rcases hc with ⟨p, hpW, rfl⟩
  let pOfTail :
      (Fin (n - N.r) → Fin (d + 1 - N.r) → ℂ) →
        SourceOrientedRankDeficientSlicedNormalParameter
          d n N.r N.hrD N.hrn :=
    fun q => { head := p.head, mixed := p.mixed, tail := q }
  let Ptail : Set (Fin (n - N.r) → Fin (d + 1 - N.r) → ℂ) :=
    {q | pOfTail q ∈ W}
  have hpOfTail_cont : Continuous pOfTail := by
    change Continuous
      (fun q : Fin (n - N.r) → Fin (d + 1 - N.r) → ℂ =>
        ({ head := p.head, mixed := p.mixed, tail := q } :
          SourceOrientedRankDeficientSlicedNormalParameter
            d n N.r N.hrD N.hrn))
    rw [continuous_induced_rng]
    exact continuous_const.prodMk (continuous_const.prodMk continuous_id)
  have hPtail_open : IsOpen Ptail := hW_open.preimage hpOfTail_cont
  have hp_tail : p.tail ∈ Ptail := by
    simpa [Ptail, pOfTail] using hpW
  have htail_dense :
      p.tail ∈ closure
        {q' | q' ∈ Ptail ∧
          SourceShiftedTailOrientedMaxRankAt d N.r N.hrD (n - N.r)
            (sourceShiftedTailOrientedInvariant d N.r N.hrD (n - N.r) q')} :=
    sourceShiftedTailOrientedMaxRank_parameter_dense_in_open
      d N.r (n - N.r) N.hrD hPtail_open p.tail hp_tail
  let cOfTail :
      (Fin (n - N.r) → Fin (d + 1 - N.r) → ℂ) →
        Fin (sourceOrientedSlicedNormalParameterFinCoordDim d n N.r) → ℂ :=
    fun q => e (pOfTail q)
  let F :
      (Fin (n - N.r) → Fin (d + 1 - N.r) → ℂ) →
        SourceOrientedGramData d n :=
    fun q =>
      sourceOrientedMinkowskiInvariant d n
        (N.toOriginal
          (sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn
            (pOfTail q).toNormalParameter))
  have hnormal_cont :
      Continuous
        (fun q : Fin (n - N.r) → Fin (d + 1 - N.r) → ℂ =>
          sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn
            (pOfTail q).toNormalParameter) :=
    (continuous_sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn).comp
      ((continuous_sourceOrientedSlicedNormalParameter_toNormalParameter
          (d := d) (n := n) (r := N.r) (hrD := N.hrD) (hrn := N.hrn)).comp
        hpOfTail_cont)
  have hF_cont : Continuous F :=
    (continuous_sourceOrientedMinkowskiInvariant (d := d) (n := n)).comp
      (N.toOriginal_continuous.comp hnormal_cont)
  have hmaps :
      Set.MapsTo F
        {q' | q' ∈ Ptail ∧
          SourceShiftedTailOrientedMaxRankAt d N.r N.hrD (n - N.r)
            (sourceShiftedTailOrientedInvariant d N.r N.hrD (n - N.r) q')}
        (image ''
          {c' | c' ∈ e '' W ∧ SourceOrientedMaxRankAt d n (image c')}) := by
    intro q hq
    refine ⟨cOfTail q, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · exact ⟨pOfTail q, hq.1, rfl⟩
      · have hH : IsUnit (pOfTail q).toNormalParameter.head.det :=
          hhead (pOfTail q) hq.1
        have hmax :=
          (N.toOriginal_slicedNormalParameterVector_maxRank_iff_tail
            (pOfTail q) hH).2 hq.2
        simpa [image, cOfTail, pOfTail] using hmax
    · simp [F, image, cOfTail, pOfTail]
  have hclose := map_mem_closure hF_cont htail_dense hmaps
  simpa [F, image, cOfTail, pOfTail] using hclose

/-- Choose a sliced Schur window whose finite-coordinate image lies inside the
compact extended-tube control ball, and whose canonical sliced image is an
open source-variety neighborhood represented by the same window. -/
theorem exists_slicedSchurWindow_finCoordControl
    {d n : ℕ}
    [NeZero d]
    (hd : 2 ≤ d)
    (hn : d + 1 ≤ n)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (N : SourceOrientedRankDeficientNormalFormData d n z0) :
    ∃ (ε headRadius mixedRadius : ℝ)
      (Tail : SourceOrientedRankDeficientTailWindowChoice d n N.r N.hrD N.hrn)
      (Ωv : Set (SourceOrientedVariety d n)),
      let W :=
        sourceOrientedRankDeficientSlicedSchurParameterWindow
          d n N.r N.hrD N.hrn headRadius mixedRadius Tail
      let e :=
        sourceOrientedSlicedNormalParameterFinCoordHomeomorph
          (d := d) (n := n) (r := N.r) (hrD := N.hrD) (hrn := N.hrn)
      0 < ε ∧
        0 < headRadius ∧
        0 < mixedRadius ∧
        IsCompact
          (sourceOrientedSlicedNormalParameterFinCoordClosedBall
            d n N.r N.hrD N.hrn ε) ∧
        IsOpen W ∧
        sourceOrientedSlicedNormalCenterParameter d n N.r N.hrD N.hrn ∈ W ∧
        e '' W ⊆
          sourceOrientedSlicedNormalParameterFinCoordClosedBall
            d n N.r N.hrD N.hrn ε ∧
        (∀ c,
          c ∈ sourceOrientedSlicedNormalParameterFinCoordClosedBall
              d n N.r N.hrD N.hrn ε →
            N.toOriginal
                (sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn
                  ((e.symm c).toNormalParameter)) ∈
              ExtendedTube d n) ∧
        IsOpen Ωv ∧
        Ωv ⊆
          sourceOrientedSlicedNormalParameterVarietyPoint
            d n N.r N.hrD N.hrn '' W ∧
        (∀ p, p ∈ W →
          sourceOrientedSlicedNormalParameterVarietyPoint
            d n N.r N.hrD N.hrn p ∈ Ωv) ∧
        (∀ p, p ∈ W → IsUnit p.toNormalParameter.head.det) := by
  rcases N.exists_slicedFinCoordCompactOpen_toOriginal_mem_ET with
    ⟨ε, hε, hK_compact, hB_open, hB_subset_K, hcenter_B, hK_tube⟩
  let e :=
    sourceOrientedSlicedNormalParameterFinCoordHomeomorph
      (d := d) (n := n) (r := N.r) (hrD := N.hrD) (hrn := N.hrn)
  let B :=
    sourceOrientedSlicedNormalParameterFinCoordOpenBall
      d n N.r N.hrD N.hrn ε
  let U : Set (SourceOrientedRankDeficientSlicedNormalParameter d n N.r N.hrD N.hrn) :=
    e ⁻¹' B
  have hU :
      U ∈ 𝓝 (sourceOrientedSlicedNormalCenterParameter d n N.r N.hrD N.hrn) := by
    have hpre : e ⁻¹' B ∈
        𝓝 (sourceOrientedSlicedNormalCenterParameter d n N.r N.hrD N.hrn) :=
      e.continuous.continuousAt (hB_open.mem_nhds hcenter_B)
    simpa [U] using hpre
  let A := N.toAlgebraicNormalFormData
  let Head := sourceRankDeficientHeadSliceGaugeData d N.r N.hrD
  let headDomainRadius := Classical.choose Head.factorDomain_coordinate
  have hheadDomainSpec := Classical.choose_spec Head.factorDomain_coordinate
  rcases
      A.exists_slicedSchurParameterWindow_subset_nhds_image_subset_open_headDomain_tailRank_connected
        (d := d) (n := n) hn
        (U := U) hU
        (headDomain := Head.factorDomain)
        (headDomainRadius := headDomainRadius)
        hheadDomainSpec.1 hheadDomainSpec.2
        isOpen_univ (Set.mem_univ _) with
    ⟨headRadius, mixedRadius, Tail, hheadRadius, hmixedRadius, hdomain, hW_open,
      _hW_conn, hcenter_W, hW_sub_U, hhead_unit, _himage, _htailRank_conn⟩
  let W :=
    sourceOrientedRankDeficientSlicedSchurParameterWindow
      d n N.r N.hrD N.hrn headRadius mixedRadius Tail
  rcases
      sourceOrientedHeadSliceGaugeSchurWindowCanonicalImage
        (d := d) (n := n) hd hn (hrD := N.hrD) (hrn := N.hrn)
        Head Tail hdomain with
    ⟨Ωv, hΩv_open, hΩv_surj, hΩv_mem⟩
  have hW_closed :
      W ⊆ e ⁻¹'
        sourceOrientedSlicedNormalParameterFinCoordClosedBall
          d n N.r N.hrD N.hrn ε := by
    intro p hp
    exact hB_subset_K (hW_sub_U hp)
  have hP_subset_K :
      e '' W ⊆
        sourceOrientedSlicedNormalParameterFinCoordClosedBall
          d n N.r N.hrD N.hrn ε := by
    simpa [e] using
      sourceOrientedSlicedNormalParameterFinCoord_image_subset_closedBall
        (d := d) (n := n) (r := N.r) (hrD := N.hrD) (hrn := N.hrn)
        (ε := ε) (W := W) hW_closed
  refine
    ⟨ε, headRadius, mixedRadius, Tail, Ωv, hε, hheadRadius, hmixedRadius,
      hK_compact, hW_open, hcenter_W, hP_subset_K, ?_, hΩv_open, hΩv_surj,
      hΩv_mem, hhead_unit⟩
  intro c hc
  simpa [e] using hK_tube c hc

/-- Small-arity version of the compact/open sliced Schur-window control
packet.  It uses the determinant-vacuous small-arity canonical image theorem
and avoids the hard-range tail-rank-connectedness shrink. -/
theorem exists_slicedSchurWindow_finCoordControl_smallArity
    {d n : ℕ}
    [NeZero d]
    (hd : 2 ≤ d)
    (hn : n < d + 1)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (N : SourceOrientedRankDeficientNormalFormData d n z0) :
    ∃ (ε headRadius mixedRadius : ℝ)
      (Tail : SourceOrientedRankDeficientTailWindowChoice d n N.r N.hrD N.hrn)
      (Ωv : Set (SourceOrientedVariety d n)),
      let W :=
        sourceOrientedRankDeficientSlicedSchurParameterWindow
          d n N.r N.hrD N.hrn headRadius mixedRadius Tail
      let e :=
        sourceOrientedSlicedNormalParameterFinCoordHomeomorph
          (d := d) (n := n) (r := N.r) (hrD := N.hrD) (hrn := N.hrn)
      0 < ε ∧
        0 < headRadius ∧
        0 < mixedRadius ∧
        IsCompact
          (sourceOrientedSlicedNormalParameterFinCoordClosedBall
            d n N.r N.hrD N.hrn ε) ∧
        IsOpen W ∧
        sourceOrientedSlicedNormalCenterParameter d n N.r N.hrD N.hrn ∈ W ∧
        e '' W ⊆
          sourceOrientedSlicedNormalParameterFinCoordClosedBall
            d n N.r N.hrD N.hrn ε ∧
        (∀ c,
          c ∈ sourceOrientedSlicedNormalParameterFinCoordClosedBall
              d n N.r N.hrD N.hrn ε →
            N.toOriginal
                (sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn
                  ((e.symm c).toNormalParameter)) ∈
              ExtendedTube d n) ∧
        IsOpen Ωv ∧
        Ωv ⊆
          sourceOrientedSlicedNormalParameterVarietyPoint
            d n N.r N.hrD N.hrn '' W ∧
        (∀ p, p ∈ W →
          sourceOrientedSlicedNormalParameterVarietyPoint
            d n N.r N.hrD N.hrn p ∈ Ωv) ∧
        (∀ p, p ∈ W → IsUnit p.toNormalParameter.head.det) := by
  rcases N.exists_slicedFinCoordCompactOpen_toOriginal_mem_ET with
    ⟨ε, hε, hK_compact, hB_open, hB_subset_K, hcenter_B, hK_tube⟩
  let e :=
    sourceOrientedSlicedNormalParameterFinCoordHomeomorph
      (d := d) (n := n) (r := N.r) (hrD := N.hrD) (hrn := N.hrn)
  let B :=
    sourceOrientedSlicedNormalParameterFinCoordOpenBall
      d n N.r N.hrD N.hrn ε
  let Ufin :
      Set (SourceOrientedRankDeficientSlicedNormalParameter d n N.r N.hrD N.hrn) :=
    e ⁻¹' B
  have hUfin :
      Ufin ∈ 𝓝 (sourceOrientedSlicedNormalCenterParameter d n N.r N.hrD N.hrn) := by
    have hpre : e ⁻¹' B ∈
        𝓝 (sourceOrientedSlicedNormalCenterParameter d n N.r N.hrD N.hrn) :=
      e.continuous.continuousAt (hB_open.mem_nhds hcenter_B)
    simpa [Ufin] using hpre
  let A := N.toAlgebraicNormalFormData
  rcases A.exists_normalParameterBall_image_subset_open_and_head
      isOpen_univ (Set.mem_univ _) with
    ⟨εhead, _hεhead, hHeadBall_open, _hHeadBall_conn, hHeadBall_center,
      hHeadBall_head, _hHeadBall_image⟩
  let Uhead :
      Set (SourceOrientedRankDeficientSlicedNormalParameter d n N.r N.hrD N.hrn) :=
    {p | p.toNormalParameter ∈
      sourceOrientedNormalParameterBall (d := d) (n := n) (r := N.r)
        (hrD := N.hrD) (hrn := N.hrn) εhead}
  have hUhead :
      Uhead ∈ 𝓝 (sourceOrientedSlicedNormalCenterParameter d n N.r N.hrD N.hrn) := by
    have hUhead_open : IsOpen Uhead :=
      hHeadBall_open.preimage
        (continuous_sourceOrientedSlicedNormalParameter_toNormalParameter
          (d := d) (n := n) (r := N.r) (hrD := N.hrD) (hrn := N.hrn))
    have hcenter :
        sourceOrientedSlicedNormalCenterParameter d n N.r N.hrD N.hrn ∈ Uhead := by
      simpa [Uhead] using hHeadBall_center
    exact hUhead_open.mem_nhds hcenter
  let U :
      Set (SourceOrientedRankDeficientSlicedNormalParameter d n N.r N.hrD N.hrn) :=
    Ufin ∩ Uhead
  have hU :
      U ∈ 𝓝 (sourceOrientedSlicedNormalCenterParameter d n N.r N.hrD N.hrn) :=
    Filter.inter_mem hUfin hUhead
  let Head := sourceRankDeficientHeadSliceGaugeData d N.r N.hrD
  let headDomainRadius := Classical.choose Head.factorDomain_coordinate
  have hheadDomainSpec := Classical.choose_spec Head.factorDomain_coordinate
  rcases
      exists_sourceOrientedRankDeficientSlicedSchurParameterWindow_coordinate_bounds_subset_of_mem_nhds_center
        (d := d) (n := n) (r := N.r) (hrD := N.hrD) (hrn := N.hrn) hU with
    ⟨headBound, mixedBound, tailBound, hheadBound, hmixedBound, htailBound,
      hbounds_sub⟩
  let ρ : ℝ :=
    min (headDomainRadius / 2)
      (min (headBound / 2) (min (mixedBound / 2) (tailBound / 2)))
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    exact
      lt_min (half_pos hheadDomainSpec.1)
        (lt_min (half_pos hheadBound)
          (lt_min (half_pos hmixedBound) (half_pos htailBound)))
  have hρ_le_domain : ρ ≤ headDomainRadius := by
    dsimp [ρ]
    exact le_trans (min_le_left _ _) (by linarith)
  have hρ_le_head : ρ ≤ headBound := by
    dsimp [ρ]
    exact le_trans (le_trans (min_le_right _ _) (min_le_left _ _)) (by linarith)
  have hρ_le_mixed : ρ ≤ mixedBound := by
    dsimp [ρ]
    exact
      le_trans
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
        (by linarith)
  have hρ_le_tail : ρ ≤ tailBound := by
    dsimp [ρ]
    exact
      le_trans
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
        (by linarith)
  let Tail : SourceOrientedRankDeficientTailWindowChoice d n N.r N.hrD N.hrn :=
    sourceOriented_rankDeficient_tailWindowChoice
      d n N.r N.hrD N.hrn hρ_pos
  have htail_le_bound : Tail.tailCoordRadius ≤ tailBound := by
    simpa [Tail, sourceOriented_rankDeficient_tailWindowChoice] using hρ_le_tail
  let W :=
    sourceOrientedRankDeficientSlicedSchurParameterWindow
      d n N.r N.hrD N.hrn ρ ρ Tail
  have hdomain :
      sourceHeadGaugeSliceCoordinateWindow d N.r N.hrD ρ ⊆ Head.factorDomain := by
    intro H hH
    exact hheadDomainSpec.2 (by
      intro a b
      exact lt_of_lt_of_le (hH a b) hρ_le_domain)
  rcases sourceOrientedRankDeficientSlicedSchurParameterWindow_open_connected
      d n N.r N.hrD N.hrn hρ_pos hρ_pos Tail with
    ⟨hW_open, _hW_conn, hcenter_W⟩
  have hW_sub_U : W ⊆ U := by
    exact hbounds_sub Tail hρ_le_head hρ_le_mixed htail_le_bound
  rcases
      sourceOrientedHeadSliceGaugeSchurWindowCanonicalImage_smallArity
        (d := d) (n := n) hd hn (hrD := N.hrD) (hrn := N.hrn)
        Head Tail hdomain with
    ⟨Ωv, hΩv_open, hΩv_surj, hΩv_mem⟩
  have hW_closed :
      W ⊆ e ⁻¹'
        sourceOrientedSlicedNormalParameterFinCoordClosedBall
          d n N.r N.hrD N.hrn ε := by
    intro p hp
    exact hB_subset_K (hW_sub_U hp).1
  have hP_subset_K :
      e '' W ⊆
        sourceOrientedSlicedNormalParameterFinCoordClosedBall
          d n N.r N.hrD N.hrn ε := by
    simpa [e] using
      sourceOrientedSlicedNormalParameterFinCoord_image_subset_closedBall
        (d := d) (n := n) (r := N.r) (hrD := N.hrD) (hrn := N.hrn)
        (ε := ε) (W := W) hW_closed
  have hhead_unit :
      ∀ p, p ∈ W → IsUnit p.toNormalParameter.head.det := by
    intro p hp
    exact hHeadBall_head ((hW_sub_U hp).2)
  refine
    ⟨ε, ρ, ρ, Tail, Ωv, hε, hρ_pos, hρ_pos, hK_compact, hW_open,
      hcenter_W, hP_subset_K, ?_, hΩv_open, hΩv_surj, hΩv_mem, hhead_unit⟩
  intro c hc
  simpa [e] using hK_tube c hc

end SourceOrientedRankDeficientNormalFormData

/-- Hard-range rank-deficient tube residual-polydisc constructor.  The compact
tube-control set is the checked finite-coordinate closed ball, while the open
parameter set is the finite-coordinate image of the sliced Schur window. -/
noncomputable def sourceOriented_rankDeficient_tubeResidualPolydisc_hardRange
    {d n : ℕ}
    [NeZero d]
    (hd : 2 ≤ d)
    (hn : d + 1 ≤ n)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (N : SourceOrientedRankDeficientNormalFormData d n z0) :
    SourceOrientedResidualPolydiscData d n N := by
  let hcontrol_exists := N.exists_slicedSchurWindow_finCoordControl hd hn
  let ε := Classical.choose hcontrol_exists
  let hcontrol_exists₁ := Classical.choose_spec hcontrol_exists
  let headRadius := Classical.choose hcontrol_exists₁
  let hcontrol_exists₂ := Classical.choose_spec hcontrol_exists₁
  let mixedRadius := Classical.choose hcontrol_exists₂
  let hcontrol_exists₃ := Classical.choose_spec hcontrol_exists₂
  let Tail := Classical.choose hcontrol_exists₃
  let hcontrol_exists₄ := Classical.choose_spec hcontrol_exists₃
  let Ωv := Classical.choose hcontrol_exists₄
  let hcontrol := Classical.choose_spec hcontrol_exists₄
  let W :=
    sourceOrientedRankDeficientSlicedSchurParameterWindow
      d n N.r N.hrD N.hrn headRadius mixedRadius Tail
  let e :=
    sourceOrientedSlicedNormalParameterFinCoordHomeomorph
      (d := d) (n := n) (r := N.r) (hrD := N.hrD) (hrn := N.hrn)
  let K :=
    sourceOrientedSlicedNormalParameterFinCoordClosedBall
      d n N.r N.hrD N.hrn ε
  let P : Set (Fin (sourceOrientedSlicedNormalParameterFinCoordDim d n N.r) → ℂ) :=
    e '' W
  let residualVector :
      (Fin (sourceOrientedSlicedNormalParameterFinCoordDim d n N.r) → ℂ) →
        Fin n → Fin (d + 1) → ℂ :=
    fun c =>
      sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn
        ((e.symm c).toNormalParameter)
  let image :
      (Fin (sourceOrientedSlicedNormalParameterFinCoordDim d n N.r) → ℂ) →
        SourceOrientedGramData d n :=
    fun c => sourceOrientedMinkowskiInvariant d n (N.toOriginal (residualVector c))
  rcases hcontrol with
    ⟨_hε, _hheadRadius, _hmixedRadius, hK_compact, hW_open, hcenter_W,
      hP_subset_K, hK_tube, hΩv_open, hΩv_surj, hΩv_mem, _hhead_unit⟩
  have hc0P :
      sourceOrientedSlicedNormalParameterFinCenterCoord d n N.r N.hrD N.hrn ∈ P := by
    simpa [P, e] using
      sourceOrientedSlicedNormalParameterFinCenterCoord_mem_image
        (d := d) (n := n) (r := N.r) (hrD := N.hrD) (hrn := N.hrn)
        (W := W) hcenter_W
  have hcenter_symm :
      e.symm (sourceOrientedSlicedNormalParameterFinCenterCoord
          d n N.r N.hrD N.hrn) =
        sourceOrientedSlicedNormalCenterParameter d n N.r N.hrD N.hrn := by
    rw [← sourceOrientedSlicedNormalParameterFinCoordHomeomorph_center
      d n N.r N.hrD N.hrn]
    simp [e]
  have hresidual_center :
      residualVector
          (sourceOrientedSlicedNormalParameterFinCenterCoord
            d n N.r N.hrD N.hrn) =
        N.normalBase := by
    dsimp [residualVector]
    rw [hcenter_symm]
    rw [sourceOrientedSlicedNormalCenterParameter_toNormalParameter]
    rw [sourceOrientedNormalParameterVector_center]
    exact N.normalBase_eq.symm
  let Uvar : Set (SourceOrientedGramData d n) :=
    sourceOrientedVarietyUnderlyingSet d n (N.varietyTransport.invFun '' Ωv)
  let hUvar_rel :
      IsRelOpenInSourceOrientedGramVariety d n Uvar := by
    change
      IsRelOpenInSourceOrientedGramVariety d n
        (sourceOrientedVarietyUnderlyingSet d n
          (N.varietyTransport.invFun '' Classical.choose hcontrol_exists₄))
    exact
      sourceOrientedVarietyTransport_invFun_image_underlying_relOpen
        (d := d) (n := n) N.varietyTransport hΩv_open
  let Ω := Classical.choose hUvar_rel
  have hΩ_spec := Classical.choose_spec hUvar_rel
  have hΩ_open : IsOpen Ω := hΩ_spec.1
  have hΩ_eq : Uvar = Ω ∩ sourceOrientedGramVariety d n := hΩ_spec.2
  have hmem_bridge :
      ∀ c, c ∈ P → image c ∈ Uvar := by
    intro c hc
    simpa [P, e, residualVector, image, Uvar] using
      N.slicedFinCoord_originalImage_mem_varietyTransport
        (W := W) (Ω := Ωv) hΩv_mem c hc
  have hsurj_bridge :
      Uvar ⊆ image '' P := by
    intro G hG
    simpa [P, e, residualVector, image, Uvar] using
      N.slicedFinCoord_originalImage_surj_varietyTransport
        (W := W) (Ω := Ωv) hΩv_surj hG
  have hΩ_center_pair :
      sourceOrientedMinkowskiInvariant d n z0 ∈ Ω ∩ sourceOrientedGramVariety d n := by
    have hcenter_mem : image
        (sourceOrientedSlicedNormalParameterFinCenterCoord
          d n N.r N.hrD N.hrn) ∈ Uvar :=
      hmem_bridge _ hc0P
    have hcenter_mem' :
        sourceOrientedMinkowskiInvariant d n z0 ∈ Uvar := by
      simpa [image, residualVector, hresidual_center,
        N.toOriginal_normalBase_invariant] using hcenter_mem
    simpa [hΩ_eq] using hcenter_mem'
  refine
    { m := sourceOrientedSlicedNormalParameterFinCoordDim d n N.r
      c0 := sourceOrientedSlicedNormalParameterFinCenterCoord d n N.r N.hrD N.hrn
      K := K
      P := P
      K_compact := hK_compact
      P_open := by
        simpa [P, e] using
          isOpen_sourceOrientedSlicedNormalParameterFinCoord_image
            (d := d) (n := n) (r := N.r) (hrD := N.hrD) (hrn := N.hrn)
            (W := W) hW_open
      P_subset_K := hP_subset_K
      c0_mem := hc0P
      residualVector := residualVector
      residualVector_continuousOn := by
        simpa [K, e, residualVector] using
          N.continuousOn_slicedFinCoord_normalParameterVector_closedBall ε
      residualVector_c0 := hresidual_center
      toOriginal_residualVector_mem_ET := by
        intro c hc
        simpa [K, e, residualVector] using hK_tube c hc
      Ω := Ω
      Ω_open := hΩ_open
      Ω_center := hΩ_center_pair.1
      originalInvariant_mem := by
        intro c hc
        have hcU : image c ∈ Uvar := hmem_bridge c hc
        simpa [image, hΩ_eq] using hcU
      image_surj := by
        intro G hG
        have hGU : G ∈ Uvar := by
          simpa [hΩ_eq] using hG
        simpa [image] using hsurj_bridge hGU
      maxRank_dense_original := by
        intro c hcP
        have hcU : image c ∈ Uvar := hmem_bridge c hcP
        have hdenseU :
            image c ∈
              closure (Uvar ∩ {G | SourceOrientedMaxRankAt d n G}) :=
          sourceOrientedMaxRank_dense_in_relOpen_inter
            (d := d) (n := n) hn hUvar_rel hcU
        have hsubset :
            Uvar ∩ {G | SourceOrientedMaxRankAt d n G} ⊆
              image ''
                {c' | c' ∈ P ∧ SourceOrientedMaxRankAt d n (image c')} := by
          intro G hG
          rcases hsurj_bridge hG.1 with ⟨c', hc'P, hc'eq⟩
          refine ⟨c', ⟨hc'P, ?_⟩, hc'eq⟩
          simpa [hc'eq] using hG.2
        exact closure_mono hsubset hdenseU }

/-- Small-arity rank-deficient tube residual-polydisc constructor.  The image
assembly is the same as in the hard range, but the canonical Schur image is
the determinant-vacuous small-arity one and max-rank density is supplied from
the sliced parameter-density lift. -/
noncomputable def sourceOriented_rankDeficient_tubeResidualPolydisc_smallArity
    {d n : ℕ}
    [NeZero d]
    (hd : 2 ≤ d)
    (hn : n < d + 1)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (N : SourceOrientedRankDeficientNormalFormData d n z0) :
    SourceOrientedResidualPolydiscData d n N := by
  let hcontrol_exists := N.exists_slicedSchurWindow_finCoordControl_smallArity hd hn
  let ε := Classical.choose hcontrol_exists
  let hcontrol_exists₁ := Classical.choose_spec hcontrol_exists
  let headRadius := Classical.choose hcontrol_exists₁
  let hcontrol_exists₂ := Classical.choose_spec hcontrol_exists₁
  let mixedRadius := Classical.choose hcontrol_exists₂
  let hcontrol_exists₃ := Classical.choose_spec hcontrol_exists₂
  let Tail := Classical.choose hcontrol_exists₃
  let hcontrol_exists₄ := Classical.choose_spec hcontrol_exists₃
  let Ωv := Classical.choose hcontrol_exists₄
  let hcontrol := Classical.choose_spec hcontrol_exists₄
  let W :=
    sourceOrientedRankDeficientSlicedSchurParameterWindow
      d n N.r N.hrD N.hrn headRadius mixedRadius Tail
  let e :=
    sourceOrientedSlicedNormalParameterFinCoordHomeomorph
      (d := d) (n := n) (r := N.r) (hrD := N.hrD) (hrn := N.hrn)
  let K :=
    sourceOrientedSlicedNormalParameterFinCoordClosedBall
      d n N.r N.hrD N.hrn ε
  let P : Set (Fin (sourceOrientedSlicedNormalParameterFinCoordDim d n N.r) → ℂ) :=
    e '' W
  let residualVector :
      (Fin (sourceOrientedSlicedNormalParameterFinCoordDim d n N.r) → ℂ) →
        Fin n → Fin (d + 1) → ℂ :=
    fun c =>
      sourceOrientedNormalParameterVector d n N.r N.hrD N.hrn
        ((e.symm c).toNormalParameter)
  let image :
      (Fin (sourceOrientedSlicedNormalParameterFinCoordDim d n N.r) → ℂ) →
        SourceOrientedGramData d n :=
    fun c => sourceOrientedMinkowskiInvariant d n (N.toOriginal (residualVector c))
  rcases hcontrol with
    ⟨_hε, _hheadRadius, _hmixedRadius, hK_compact, hW_open, hcenter_W,
      hP_subset_K, hK_tube, hΩv_open, hΩv_surj, hΩv_mem, hhead_unit⟩
  have hc0P :
      sourceOrientedSlicedNormalParameterFinCenterCoord d n N.r N.hrD N.hrn ∈ P := by
    simpa [P, e] using
      sourceOrientedSlicedNormalParameterFinCenterCoord_mem_image
        (d := d) (n := n) (r := N.r) (hrD := N.hrD) (hrn := N.hrn)
        (W := W) hcenter_W
  have hcenter_symm :
      e.symm (sourceOrientedSlicedNormalParameterFinCenterCoord
          d n N.r N.hrD N.hrn) =
        sourceOrientedSlicedNormalCenterParameter d n N.r N.hrD N.hrn := by
    rw [← sourceOrientedSlicedNormalParameterFinCoordHomeomorph_center
      d n N.r N.hrD N.hrn]
    simp [e]
  have hresidual_center :
      residualVector
          (sourceOrientedSlicedNormalParameterFinCenterCoord
            d n N.r N.hrD N.hrn) =
        N.normalBase := by
    dsimp [residualVector]
    rw [hcenter_symm]
    rw [sourceOrientedSlicedNormalCenterParameter_toNormalParameter]
    rw [sourceOrientedNormalParameterVector_center]
    exact N.normalBase_eq.symm
  let Uvar : Set (SourceOrientedGramData d n) :=
    sourceOrientedVarietyUnderlyingSet d n (N.varietyTransport.invFun '' Ωv)
  let hUvar_rel :
      IsRelOpenInSourceOrientedGramVariety d n Uvar := by
    change
      IsRelOpenInSourceOrientedGramVariety d n
        (sourceOrientedVarietyUnderlyingSet d n
          (N.varietyTransport.invFun '' Classical.choose hcontrol_exists₄))
    exact
      sourceOrientedVarietyTransport_invFun_image_underlying_relOpen
        (d := d) (n := n) N.varietyTransport hΩv_open
  let Ω := Classical.choose hUvar_rel
  have hΩ_spec := Classical.choose_spec hUvar_rel
  have hΩ_open : IsOpen Ω := hΩ_spec.1
  have hΩ_eq : Uvar = Ω ∩ sourceOrientedGramVariety d n := hΩ_spec.2
  have hmem_bridge :
      ∀ c, c ∈ P → image c ∈ Uvar := by
    intro c hc
    simpa [P, e, residualVector, image, Uvar] using
      N.slicedFinCoord_originalImage_mem_varietyTransport
        (W := W) (Ω := Ωv) hΩv_mem c hc
  have hsurj_bridge :
      Uvar ⊆ image '' P := by
    intro G hG
    simpa [P, e, residualVector, image, Uvar] using
      N.slicedFinCoord_originalImage_surj_varietyTransport
        (W := W) (Ω := Ωv) hΩv_surj hG
  have hΩ_center_pair :
      sourceOrientedMinkowskiInvariant d n z0 ∈ Ω ∩ sourceOrientedGramVariety d n := by
    have hcenter_mem : image
        (sourceOrientedSlicedNormalParameterFinCenterCoord
          d n N.r N.hrD N.hrn) ∈ Uvar :=
      hmem_bridge _ hc0P
    have hcenter_mem' :
        sourceOrientedMinkowskiInvariant d n z0 ∈ Uvar := by
      simpa [image, residualVector, hresidual_center,
        N.toOriginal_normalBase_invariant] using hcenter_mem
    simpa [hΩ_eq] using hcenter_mem'
  refine
    { m := sourceOrientedSlicedNormalParameterFinCoordDim d n N.r
      c0 := sourceOrientedSlicedNormalParameterFinCenterCoord d n N.r N.hrD N.hrn
      K := K
      P := P
      K_compact := hK_compact
      P_open := by
        simpa [P, e] using
          isOpen_sourceOrientedSlicedNormalParameterFinCoord_image
            (d := d) (n := n) (r := N.r) (hrD := N.hrD) (hrn := N.hrn)
            (W := W) hW_open
      P_subset_K := hP_subset_K
      c0_mem := hc0P
      residualVector := residualVector
      residualVector_continuousOn := by
        simpa [K, e, residualVector] using
          N.continuousOn_slicedFinCoord_normalParameterVector_closedBall ε
      residualVector_c0 := hresidual_center
      toOriginal_residualVector_mem_ET := by
        intro c hc
        simpa [K, e, residualVector] using hK_tube c hc
      Ω := Ω
      Ω_open := hΩ_open
      Ω_center := hΩ_center_pair.1
      originalInvariant_mem := by
        intro c hc
        have hcU : image c ∈ Uvar := hmem_bridge c hc
        simpa [image, hΩ_eq] using hcU
      image_surj := by
        intro G hG
        have hGU : G ∈ Uvar := by
          simpa [hΩ_eq] using hG
        simpa [image] using hsurj_bridge hGU
      maxRank_dense_original := by
        intro c hcP
        simpa [P, e, image, residualVector] using
          N.slicedSchurWindow_originalMaxRank_dense
            (W := W) hW_open hhead_unit c hcP }

/-- All-arity rank-deficient tube residual-polydisc constructor, split between
the checked hard-range Schur chart and the small-arity determinant-vacuous
Schur chart. -/
noncomputable def sourceOriented_rankDeficient_tubeResidualPolydisc
    {d n : ℕ}
    [NeZero d]
    (hd : 2 ≤ d)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (N : SourceOrientedRankDeficientNormalFormData d n z0) :
    SourceOrientedResidualPolydiscData d n N := by
  by_cases hn : d + 1 ≤ n
  · exact sourceOriented_rankDeficient_tubeResidualPolydisc_hardRange hd hn N
  · exact
      sourceOriented_rankDeficient_tubeResidualPolydisc_smallArity
        hd (Nat.lt_of_not_ge hn) N

/-- All-arity tube residual-polydisc producer for rank-deficient extended-tube
centers. -/
noncomputable def sourceOriented_rankDeficient_tubeResidualPolydiscProducer
    (d n : ℕ)
    [NeZero d]
    (hd : 2 ≤ d) :
    SourceOrientedRankDeficientTubeResidualPolydiscProducer d n := by
  intro z0 hz0 hlow
  let hex :=
    SourceOrientedRankDeficientNormalFormData.exists_ofExtendedTube
      (d := d) hd (n := n) hz0 hlow
  let N := Classical.choose hex
  exact ⟨N, sourceOriented_rankDeficient_tubeResidualPolydisc hd N⟩

/-- All-arity residual-chart producer obtained from the checked tube
residual-polydisc producer. -/
noncomputable def sourceOriented_rankDeficient_residualChartProducer
    (d n : ℕ)
    [NeZero d]
    (hd : 2 ≤ d) :
    SourceOrientedRankDeficientResidualChartProducer d n :=
  sourceOrientedRankDeficientResidualChartProducer_of_tubeResidualPolydiscProducer
    (sourceOriented_rankDeficient_tubeResidualPolydiscProducer d n hd)

/-- Pointwise rank-deficient residual chart obtained from the all-arity
producer.  This is the fixed-center form consumed by later quotient-value
continuity and local-boundedness arguments. -/
noncomputable def sourceOriented_rankDeficient_residualChart
    {d : ℕ}
    [NeZero d]
    (hd : 2 ≤ d)
    (n : ℕ)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (hz0 : z0 ∈ ExtendedTube d n)
    (hlow :
      ¬ SourceOrientedMaxRankAt d n
        (sourceOrientedMinkowskiInvariant d n z0)) :
    SourceOrientedRankDeficientResidualChartData d n z0 :=
  sourceOriented_rankDeficient_residualChartProducer d n hd hz0 hlow

/-- The oriented extended-tube image is relatively open in the source-oriented
variety and connected.  The relative-openness half is now supplied by the
checked all-arity rank-deficient residual chart producer; connectedness is the
continuous image of the extended tube. -/
theorem sourceOrientedExtendedTubeDomain_relOpen_connected
    {d : ℕ}
    [NeZero d]
    (hd : 2 ≤ d)
    (n : ℕ) :
    IsRelOpenInSourceOrientedGramVariety d n
        (sourceOrientedExtendedTubeDomain d n) ∧
      IsConnected (sourceOrientedExtendedTubeDomain d n) :=
  sourceOrientedExtendedTubeDomain_relOpen_connected_of_rankDeficientResidualChartProducer
    (sourceOriented_rankDeficient_residualChartProducer d n hd)
end BHW
