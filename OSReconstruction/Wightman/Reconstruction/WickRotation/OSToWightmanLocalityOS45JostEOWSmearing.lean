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
      Active OS-I Section 4.5 source-side leaf.

      `hsource_current` is the formal Euclidean source-current comparison.
      The checked moving-test theorem below reduces the deterministic
      `extendF` side-branch residual to the zero-height common-edge pairing.
      The remaining paper step is precisely the OS-I Jost/EOW identification
      of the adjacent and ordinary pulled-real branches on that common edge.

      A tempting ordinary-side shortcut would identify the zero source-side
      endpoint with the raw Wick section and then use `extendF_eq_on_forwardTube`.
      The checked coordinate identity rules that out: the endpoint is the
      `t = 1` Figure-2-4 identity-path/common-edge point, so the residual is
      genuinely the OS-I source-side transport, even on the ordinary side.
    -/
    have hzero_pairing :
        (∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.os45FlatCommonChartSourceSide d n
              (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u) *
            ((((D.toZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) φ).1 : SchwartzNPoint d n) :
                NPointDomain d n → ℂ) u)) =
          ∫ u : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d)
                (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
                (BHW.os45FlatCommonChartSourceSide d n
                  (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η u)) *
              ((((D.toZeroDiagonalCLM
                (1 : Equiv.Perm (Fin n)) φ).1 : SchwartzNPoint d n) :
                  NPointDomain d n → ℂ) u) := by
      let Aplus0 : ℂ :=
        ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.os45FlatCommonChartSourceSide d n
              (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u) *
            ((((D.toZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) φ).1 :
                SchwartzNPoint d n) : NPointDomain d n → ℂ) u)
      let Aminus0 : ℂ :=
        ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
              (BHW.os45FlatCommonChartSourceSide d n
                (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η u)) *
            ((((D.toZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) φ).1 :
                SchwartzNPoint d n) : NPointDomain d n → ℂ) u)
      let Acommon : ℂ :=
        ∫ u : NPointDomain d n,
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
              (1 : Equiv.Perm (Fin n))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u)) *
            (D.toSchwartzNPointCLM
              (1 : Equiv.Perm (Fin n)) φ : NPointDomain d n → ℂ) u
      let AadjCommon : ℂ :=
        ∫ u : NPointDomain d n,
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin n)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u)) *
            (D.toSchwartzNPointCLM
              (1 : Equiv.Perm (Fin n)) φ :
                NPointDomain d n → ℂ) u
      have hAplus_common : Aplus0 = Acommon := by
        dsimp [Aplus0, Acommon]
        refine MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall ?_)
        intro u
        let z0 : Fin n → Fin (d + 1) → ℂ :=
          (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u))
        have hsource_zero :
            BHW.os45FlatCommonChartSourceSide d n
                (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u = z0 := by
          simpa [z0] using
            BHW.os45FlatCommonChartSourceSide_zero_eq_commonEdge
              (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) (1 : ℝ) η u
        have hord :
            BHW.extendF (bvt_F OS lgc n) z0 =
              BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (1 : Equiv.Perm (Fin n))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u)) := by
          simp [BHW.os45PulledRealBranch, z0]
        change
          BHW.extendF (bvt_F OS lgc n)
              (BHW.os45FlatCommonChartSourceSide d n
                (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u) *
              (D.toSchwartzNPointCLM
                (1 : Equiv.Perm (Fin n)) φ :
                  NPointDomain d n → ℂ) u =
            BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (1 : Equiv.Perm (Fin n))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u)) *
              (D.toSchwartzNPointCLM
                (1 : Equiv.Perm (Fin n)) φ :
                  NPointDomain d n → ℂ) u
        rw [hsource_zero, hord]
      have hAminus_common : Aminus0 = AadjCommon := by
        dsimp [Aminus0, AadjCommon]
        refine MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall ?_)
        intro u
        let z0 : Fin n → Fin (d + 1) → ℂ :=
          (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u))
        have hsource_zero :
            BHW.os45FlatCommonChartSourceSide d n
                (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η u = z0 := by
          simpa [z0] using
            BHW.os45FlatCommonChartSourceSide_zero_eq_commonEdge
              (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) (-1 : ℝ) η u
        have hadj :
            BHW.extendF (bvt_F OS lgc n)
                (BHW.permAct (d := d) P.τ z0) =
              BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u)) := by
          simpa [z0] using
            BHW.os45Figure24CommonEdge_permAct_extendF_eq_adjacentPulledRealBranch
              (d := d) (n := n) hd OS lgc (P := P) u
        change
          BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d)
                (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
                (BHW.os45FlatCommonChartSourceSide d n
                  (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η u)) *
              (D.toSchwartzNPointCLM
                (1 : Equiv.Perm (Fin n)) φ :
                  NPointDomain d n → ℂ) u =
            BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u)) *
              (D.toSchwartzNPointCLM
                (1 : Equiv.Perm (Fin n)) φ :
                  NPointDomain d n → ℂ) u
        rw [hsource_zero]
        simpa using congrArg (fun c : ℂ =>
          c *
            (D.toSchwartzNPointCLM
              (1 : Equiv.Perm (Fin n)) φ :
                NPointDomain d n → ℂ) u) hadj
      have hsource_eq :
          ∀ u ∈ U,
            BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u)) =
              BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (1 : Equiv.Perm (Fin n))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u)) := by
        rcases
            BHW.os45CommonEdge_initialSectorOverlap_traces_except_adjacentWick
              (d := d) hd OS lgc (P := P)
              (U := U) hU_compact hU_connected hU_closure with
          ⟨Ucx, Ford, Fadj, hUcx_open, hUcx_connected, hwick_mem,
            hcommon_mem, _hUcx_sub, hFord_holo, hFadj_holo,
            hFord_wick, hFadj_wick_extendF, hFord_common, hFadj_common,
            hFadj_seed_trace⟩
        exact
          BHW.os45CommonEdge_pulledRealBranches_eqOn_of_E3_branchTraces
            (d := d) hd OS lgc (P := P)
            hU_open hU_connected.nonempty hU_sub hUcx_open hUcx_connected
            hwick_mem hcommon_mem Ford Fadj hFord_holo hFadj_holo
            hFord_wick
            (by
              intro u hu
              calc
                Fadj (fun k => wickRotatePoint (u k)) =
                  BHW.extendF (bvt_F OS lgc n)
                    (BHW.permAct (d := d) P.τ
                      (fun k => wickRotatePoint (u k))) := by
                    exact hFadj_wick_extendF u hu
                _ =
                  Fadj
                    (BHW.permAct (d := d) P.τ
                      (fun k => wickRotatePoint (u k))) := by
                    -- OS-I (4.12): transport the deterministic adjacent
                    -- `extendF` branch from the seed point to the local
                    -- adjacent branch on the common overlap chart.
                    exact
                      ?os_i_section45_adjacent_seed_to_wick_branch_transport
                _ =
                  bvt_F OS lgc n
                    (fun k => wickRotatePoint (u (P.τ k))) := by
                    exact hFadj_seed_trace u hu)
            hFord_common hFadj_common
      have hAadj_eq_Acommon : AadjCommon = Acommon := by
        dsimp [AadjCommon, Acommon]
        refine MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall ?_)
        intro u
        by_cases hu : u ∈ U
        · exact congrArg (fun c : ℂ =>
            c *
              (D.toSchwartzNPointCLM
                (1 : Equiv.Perm (Fin n)) φ :
                  NPointDomain d n → ℂ) u) (hsource_eq u hu)
        · have hφ0U :
              tsupport
                ((D.toSchwartzNPointCLM
                    (1 : Equiv.Perm (Fin n)) φ :
                      SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
                U := by
            simpa [BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM] using
              D.toSchwartzNPointCLM_tsupport_subset_image
                (1 : Equiv.Perm (Fin n)) φ hφU
          have hφ0_zero :
              ((D.toSchwartzNPointCLM
                  (1 : Equiv.Perm (Fin n)) φ :
                    SchwartzNPoint d n) : NPointDomain d n → ℂ) u = 0 :=
            image_eq_zero_of_notMem_tsupport
              (fun hφ0_supp => hu (hφ0U hφ0_supp))
          simp [hφ0_zero]
      change Aplus0 = Aminus0
      exact hAplus_common.trans
        (hAminus_common.trans hAadj_eq_Acommon).symm
    exact
      D.tendsto_sourceSide_extendF_difference_zero_of_zeroHeightPairing
        (d := d) OS lgc hΩplus_open hΩminus_open
        hFplus_cont hFminus_cont hU_open subset_closure hU_compact
        η h0_plus h0_minus φ hφ_compact hφU hzero_pairing
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
