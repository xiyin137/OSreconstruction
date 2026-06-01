import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45SourceSideMoving

/-!
# OS45 Jost/EOW Smearing Producer

This file opens the remaining Theorem 2 / E->R proof body at the point where
the OS-I Section 4.5 monograph argument has to be formalized: Jost real-edge
equality, distributional edge-of-the-wedge, and compact-test smearing on a
local Figure-2-4 source collar.

It deliberately does not introduce a new trusted constant or downstream
wrapper around the blocker.  The single placeholder below names the genuine
mathematical payload still to be proved.
-/

noncomputable section

open Complex Topology MeasureTheory Filter LorentzLieGroup

namespace BHW

variable {d n : ℕ}

/-- OS-I Section 4.5 Jost/EOW smearing should produce the local `(4.14)`
flat common-edge compact-test equality.

This is the paper-facing producer missing upstream of
`OS45BHWJostHullData.os45CommonEdge_sourceRepresentsZero_of_local414_integrals`
and `OS45BHWJostHullData.os45CommonEdge_sourceRepresentsZero_of_sourcePairings`.
The proof body should follow the monograph part-(b) lines 1356--1374:
construct Jost neighbourhoods on the local real edge, use Euclidean source
permutation symmetry plus the identity theorem to identify the two holomorphic
branches, apply distributional EOW on the common real edge, then smear by a
finite partition of unity over the compact support of `φ`.

The previous attempt tried to prove this through pointwise convergence of the
adjacent branch to the ordinary branch's boundary value.  That is stronger than
the OS-I argument and is not the theorem needed by the downstream Hdiff
handoff.  The live obligation is the distributional compact-test equality
itself. -/
theorem OS45BHWJostHullData.os45CommonEdge_local414_integrals_of_OSI45_jostEOW_smearing
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {U : Set (NPointDomain d n)}
    (hU_open : IsOpen U)
    (hU_compact : IsCompact (closure U))
    (hU_connected : IsConnected U)
    (hU_closure : closure U ⊆ P.V) :
    ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
      HasCompactSupport
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45CommonEdgeFlatCLE d n
          (1 : Equiv.Perm (Fin n)) '' U →
      (∫ x : BHW.OS45FlatCommonChartReal d n,
        BHW.os45FlatCommonChartBranch d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (SCV.realEmbed x) * φ x) =
        ∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (SCV.realEmbed x) * φ x := by
  classical
  intro φ hφ_compact hφU
  let D : BHW.OS45Figure24SourceCutoffData P :=
    Classical.choice (BHW.exists_os45Figure24SourceCutoffData (d := d) P)
  have hU_sub : U ⊆ P.V := fun u hu => hU_closure (subset_closure hu)
  have hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)) := by
    intro x hx
    rcases hφU hx with ⟨u, huU, rfl⟩
    exact
      (BHW.os45CommonEdgeFlatCLE_mem_edgeSet_iff d n P
        (1 : Equiv.Perm (Fin n)) u).mpr (hU_sub huU)
  have hn_pos : 0 < n := by omega
  haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn_pos⟩
  rcases BHW.os45FlatCommonChartCone_eowReady d n with
    ⟨_hC_open, _hC_convex, _hC_connected, _hC_smul, hC_nonempty⟩
  rcases hC_nonempty with ⟨η, hηC⟩
  let τside : Equiv.Perm (Fin n) :=
    (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
  let Ωplus : Set (Fin n → Fin (d + 1) → ℂ) :=
    BHW.ExtendedTube d n
  let Ωminus : Set (Fin n → Fin (d + 1) → ℂ) :=
    {z | BHW.permAct (d := d) τside z ∈ BHW.ExtendedTube d n}
  have hΩplus_open : IsOpen Ωplus := by
    simpa [Ωplus] using BHW.isOpen_extendedTube (d := d) (n := n)
  have hΩminus_open : IsOpen Ωminus := by
    simpa [Ωminus, τside] using
      BHW.isOpen_permAct_preimage_extendedTube
        (d := d) (n := n) τside
  have hFplus_cont :
      ContinuousOn
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n) z) Ωplus := by
    simpa [Ωplus] using
      (BHW.differentiableOn_extendF_bvt_F_extendedTube
        (d := d) OS lgc n).continuousOn
  have hFminus_cont :
      ContinuousOn
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm z)) Ωminus := by
    simpa [Ωminus, τside] using
      (BHW.differentiableOn_extendF_bvt_F_permAct_preimageExtendedTube
        (d := d) OS lgc n τside).continuousOn
  have h0_plus :
      ∀ u ∈ closure U,
        BHW.os45FlatCommonChartSourceSide d n
          (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u ∈ Ωplus := by
    intro u hu
    have hinit :
        BHW.os45Figure24IdentityPath (d := d) (n := n)
            u (1 : unitInterval) ∈
          BHW.ExtendedTube d n ∩
            BHW.permutedExtendedTubeSector d n P.τ :=
      BHW.os45Figure24IdentityPath_mem_initialSectorOverlap
        (d := d) (n := n) (hd := hd) (P := P)
        (subset_closure (hU_closure hu)) (1 : unitInterval)
    rw [BHW.os45FlatCommonChartSourceSide_zero_eq_identityPath_one]
    simpa [Ωplus] using hinit.1
  have h0_minus :
      ∀ u ∈ closure U,
        BHW.os45FlatCommonChartSourceSide d n
          (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η u ∈ Ωminus := by
    intro u hu
    have hinit :
        BHW.os45Figure24IdentityPath (d := d) (n := n)
            u (1 : unitInterval) ∈
          BHW.ExtendedTube d n ∩
            BHW.permutedExtendedTubeSector d n P.τ :=
      BHW.os45Figure24IdentityPath_mem_initialSectorOverlap
        (d := d) (n := n) (hd := hd) (P := P)
        (subset_closure (hU_closure hu)) (1 : unitInterval)
    rw [BHW.os45FlatCommonChartSourceSide_zero_eq_identityPath_one]
    simpa [Ωminus, τside, BHW.permutedExtendedTubeSector] using hinit.2
  have hsource_current :
      Tendsto
        (fun ε : ℝ =>
          (∫ u : NPointDomain d n,
            bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
              ((((D.toSideZeroDiagonalCLM
                (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
                  SchwartzNPoint d n) : NPointDomain d n → ℂ) u)) -
          ∫ u : NPointDomain d n,
            bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
              ((((D.toSideZeroDiagonalCLM
                (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
                  SchwartzNPoint d n) : NPointDomain d n → ℂ) u))
        (𝓝[Set.Ioi 0] (0 : ℝ))
        (𝓝 0) := by
    exact
      D.sourceSide_ordinaryPlus_adjacentMinus_difference_tendsto_zero
        OS lgc η hηC φ hφ_compact hφE
  have hsource_ext :
      Tendsto
        (fun ε : ℝ =>
          (∫ u : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
              (BHW.os45FlatCommonChartSourceSide d n
                (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η u) *
              ((((D.toSideZeroDiagonalCLM
                (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
                  SchwartzNPoint d n) : NPointDomain d n → ℂ) u)) -
          ∫ u : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d)
                (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
                (BHW.os45FlatCommonChartSourceSide d n
                  (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η u)) *
              ((((D.toSideZeroDiagonalCLM
                (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
                  SchwartzNPoint d n) : NPointDomain d n → ℂ) u))
        (𝓝[Set.Ioi 0] (0 : ℝ))
        (𝓝 0) := by
    /-
      Active OS-I Section 4.5 residual-transfer leaf.

      `hsource_current` is the formal Euclidean source-current comparison.
      What remains is the paper's mixed-tube Jost/EOW transport identifying
      those source currents with the deterministic `extendF` side branches
      above, in compact-test limit.  The open carriers and zero-height
      membership facts above are the exact local data used by the existing
      moving-test consumers; no downstream Hdiff or legacy Route A branch is
      being used here.
    -/
    exact ?os_i_section45_mixed_tube_jost_eow_residual_transfer
  have hflat :
      Tendsto
        (fun ε : ℝ =>
          (∫ x : BHW.OS45FlatCommonChartReal d n,
            BHW.os45FlatCommonChartBranch d n OS lgc
              (1 : Equiv.Perm (Fin n))
              (fun a =>
                (x a : ℂ) +
                  ((((1 : ℝ) * ε) • η) a : ℂ) * Complex.I) *
              φ x) -
          ∫ x : BHW.OS45FlatCommonChartReal d n,
            BHW.os45FlatCommonChartBranch d n OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin n)))
              (fun a =>
                (x a : ℂ) +
                  ((((-1 : ℝ) * ε) • η) a : ℂ) * Complex.I) *
              φ x)
        (𝓝[Set.Ioi 0] (0 : ℝ))
        (𝓝 0) :=
    D.tendsto_flatCommonChart_sideBranch_difference_zero_of_sourceSideDifference
      (d := d) OS lgc η hηC φ hφ_compact hφE hsource_ext
  have hzero :=
    D.zeroHeightPairing_of_tendsto_flatCommonChart_sideBranch_difference_zero
      (d := d) OS lgc η hηC φ hφ_compact hφE hflat
  simpa [SCV.realEmbed] using hzero

end BHW
