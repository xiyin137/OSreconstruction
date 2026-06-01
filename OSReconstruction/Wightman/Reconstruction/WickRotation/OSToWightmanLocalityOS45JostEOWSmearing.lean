import OSReconstruction.SCV.VladimirovTillmann
import OSReconstruction.SCV.IdentityTheorem
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45Figure24Seed
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
      Active Vladimirov/BHW local collar transport leaf.

      The OS source-current side has already been proved as `hsource_current`.
      The remaining producer must compare that raw Wick-section source current
      with the deterministic BHW `extendF` pairings on the same compact
      Figure-2-4 collar.  This is the local tempered-BV uniqueness/recovery
      step; deriving it through transported Wick pairings or source
      representation would be circular, because those are downstream
      consumers of this collar transport.
    -/
    let Ext : ℝ → ℂ := fun ε =>
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
              SchwartzNPoint d n) : NPointDomain d n → ℂ) u)
    let Raw : ℝ → ℂ := fun ε =>
      (∫ u : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
          ((((D.toSideZeroDiagonalCLM
            (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
              SchwartzNPoint d n) : NPointDomain d n → ℂ) u)) -
      ∫ u : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
          ((((D.toSideZeroDiagonalCLM
            (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
              SchwartzNPoint d n) : NPointDomain d n → ℂ) u)
    change Tendsto Ext (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0)
    have hraw : Tendsto Raw (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
      simpa [Raw] using hsource_current
    have htransport_error :
        Tendsto (fun ε : ℝ => Ext ε - Raw ε)
          (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
      let φ0 : SchwartzNPoint d n :=
        ((D.toZeroDiagonalCLM
          (1 : Equiv.Perm (Fin n)) φ).1 : SchwartzNPoint d n)
      have hφ0U :
          tsupport (φ0 : NPointDomain d n → ℂ) ⊆ U := by
        simpa [φ0, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM] using
          D.toSchwartzNPointCLM_tsupport_subset_image
            (1 : Equiv.Perm (Fin n)) φ hφU
      have h0_minus_plus :
          ∀ u ∈ closure U,
            BHW.os45FlatCommonChartSourceSide d n
              (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η u ∈ Ωplus := by
        intro u hu
        simpa using h0_plus u hu
      have h0_plus_minus :
          ∀ u ∈ closure U,
            BHW.os45FlatCommonChartSourceSide d n
              (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u ∈ Ωminus := by
        intro u hu
        simpa using h0_minus u hu
      have hplus_pair :=
        D.tendsto_sourceSide_extendF_sideZeroDiagonalCLM_pair
          (d := d) OS lgc (1 : Equiv.Perm (Fin n))
          hΩplus_open hFplus_cont hU_open (fun u hu => subset_closure hu)
          hU_compact η h0_plus h0_minus_plus φ hφ_compact hφU
      have hminus_pair :=
        D.tendsto_sourceSide_extendF_sideZeroDiagonalCLM_pair
          (d := d) OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          hΩminus_open hFminus_cont hU_open (fun u hu => subset_closure hu)
          hU_compact η h0_plus_minus h0_minus φ hφ_compact hφU
      have hordinary_endpoint_ext_eq_bvt :
          ∀ u ∈ U,
            BHW.extendF (bvt_F OS lgc n)
                (BHW.os45FlatCommonChartSourceSide d n
                  (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u) =
              bvt_F OS lgc n
                (BHW.os45FlatCommonChartSourceSide d n
                  (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u) := by
        intro u hu
        have huP : u ∈ P.V := hU_sub hu
        have hsource_zero :
            BHW.os45FlatCommonChartSourceSide d n
                (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u =
              (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u)) := by
          exact
            BHW.os45FlatCommonChartSourceSide_zero_eq_commonEdge
              (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) (1 : ℝ) η u
        rw [hsource_zero]
        exact
          BHW.os45Figure24CommonEdge_ordinary_extendF_eq_bvt_F
            (d := d) (n := n) hd OS lgc (P := P) (u := u) huP
      have hplus_endpoint_integral :
          (∫ u : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
              (BHW.os45FlatCommonChartSourceSide d n
                (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u) *
              (φ0 : NPointDomain d n → ℂ) u) =
            ∫ u : NPointDomain d n,
              bvt_F OS lgc n
                (BHW.os45FlatCommonChartSourceSide d n
                  (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u) *
                (φ0 : NPointDomain d n → ℂ) u := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro u
        by_cases hu : u ∈ U
        · simpa using
            congrArg
              (fun c : ℂ => c * (φ0 : NPointDomain d n → ℂ) u)
              (hordinary_endpoint_ext_eq_bvt u hu)
        · have hnot : u ∉ tsupport (φ0 : NPointDomain d n → ℂ) := fun hut =>
            hu (hφ0U hut)
          have hzero : (φ0 : NPointDomain d n → ℂ) u = 0 :=
            image_eq_zero_of_notMem_tsupport hnot
          simp [hzero]
      have hplus_ext_to_quarterTurn_bvt :
          Tendsto
            (fun ε : ℝ =>
              ∫ u : NPointDomain d n,
                BHW.extendF (bvt_F OS lgc n)
                  (BHW.os45FlatCommonChartSourceSide d n
                    (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η u) *
                  ((((D.toSideZeroDiagonalCLM
                    (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
                      SchwartzNPoint d n) : NPointDomain d n → ℂ) u))
            (𝓝[Set.Ioi 0] (0 : ℝ))
            (𝓝
              (∫ u : NPointDomain d n,
                bvt_F OS lgc n
                  (BHW.os45FlatCommonChartSourceSide d n
                    (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u) *
                  (φ0 : NPointDomain d n → ℂ) u)) := by
        rw [← hplus_endpoint_integral]
        simpa [φ0] using hplus_pair.1
      /-
        Genuine local Vladimirov/BHW producer input.

        The ordinary deterministic side now reaches the quarter-turned
        common-edge `bvt_F` endpoint by checked moving-test continuity and the
        forward-tube endpoint normalization above.  What is still missing is
        the genuine OS-I §4.5 Vladimirov/BHW identification of that
        quarter-turned common-edge boundary distribution with the Wick-section
        raw source current, together with the selected adjacent/permuted
        analogue.  That requires constructing the local tempered BV package on
        the actual OS45 BHW collar from OS polynomial growth and proving that
        its boundary distribution is the raw `(4.12)` source current on compact
        tests.
      -/
      have hminus_endpoint_integral :
          (∫ u : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d)
                (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
                (BHW.os45FlatCommonChartSourceSide d n
                  (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η u)) *
              (φ0 : NPointDomain d n → ℂ) u) =
            ∫ u : NPointDomain d n,
              BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                  (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                  (BHW.realEmbed
                    (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                      (1 : Equiv.Perm (Fin n)) u)) *
                (φ0 : NPointDomain d n → ℂ) u := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
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
              (φ0 : NPointDomain d n → ℂ) u =
            BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u)) *
              (φ0 : NPointDomain d n → ℂ) u
        rw [hsource_zero]
        simpa using
          congrArg
            (fun c : ℂ => c * (φ0 : NPointDomain d n → ℂ) u) hadj
      have hminus_ext_to_adjacent_pulled :
          Tendsto
            (fun ε : ℝ =>
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
            (𝓝
              (∫ u : NPointDomain d n,
                BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                    (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                    (BHW.realEmbed
                      (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                        (1 : Equiv.Perm (Fin n)) u)) *
                  (φ0 : NPointDomain d n → ℂ) u)) := by
        rw [← hminus_endpoint_integral]
        simpa [φ0] using hminus_pair.2
      let A0 : ℂ :=
        ∫ u : NPointDomain d n,
          bvt_F OS lgc n
            (BHW.os45FlatCommonChartSourceSide d n
              (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u) *
            (φ0 : NPointDomain d n → ℂ) u
      let B0 : ℂ :=
        ∫ u : NPointDomain d n,
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin n)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u)) *
            (φ0 : NPointDomain d n → ℂ) u
      have hzero_height_boundary_distribution : A0 - B0 = 0 := by
        let Aord : ℂ :=
          ∫ u : NPointDomain d n,
            BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (1 : Equiv.Perm (Fin n))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u)) *
              (φ0 : NPointDomain d n → ℂ) u
        have hA0_eq_Aord : A0 = Aord := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
          intro u
          by_cases hu : u ∈ U
          · have huP : u ∈ P.V := hU_sub hu
            have hsource_zero :
                BHW.os45FlatCommonChartSourceSide d n
                    (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u =
                  (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
                    (BHW.realEmbed
                      (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                        (1 : Equiv.Perm (Fin n)) u)) := by
              exact
                BHW.os45FlatCommonChartSourceSide_zero_eq_commonEdge
                  (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) (1 : ℝ) η u
            have hcommon_ext_eq_bvt :
                BHW.extendF (bvt_F OS lgc n)
                    ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
                      (BHW.realEmbed
                        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                          (1 : Equiv.Perm (Fin n)) u))) =
                  bvt_F OS lgc n
                    ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
                      (BHW.realEmbed
                        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                          (1 : Equiv.Perm (Fin n)) u))) :=
              BHW.os45Figure24CommonEdge_ordinary_extendF_eq_bvt_F
                (d := d) (n := n) hd OS lgc (P := P) huP
            have hordinary_pulled :
                BHW.extendF (bvt_F OS lgc n)
                    ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
                      (BHW.realEmbed
                        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                          (1 : Equiv.Perm (Fin n)) u))) =
                  BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                    (1 : Equiv.Perm (Fin n))
                    (BHW.realEmbed
                      (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                        (1 : Equiv.Perm (Fin n)) u)) := by
              rcases
                  BHW.os45Figure24Path_endpoint_extendF_eq_ordinaryPulledRealBranch
                    (d := d) (n := n) hd OS lgc (P := P)
                    (u := u) (subset_closure huP) with
                ⟨Γ, _hΓ_cont, _hΓ_zero, hΓ_one, _hΓ_ET, hΓ_trace⟩
              rw [← hΓ_one]
              exact hΓ_trace
            have hpoint :
                bvt_F OS lgc n
                    (BHW.os45FlatCommonChartSourceSide d n
                      (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u) =
                  BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                    (1 : Equiv.Perm (Fin n))
                    (BHW.realEmbed
                      (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                        (1 : Equiv.Perm (Fin n)) u)) := by
              calc
                bvt_F OS lgc n
                    (BHW.os45FlatCommonChartSourceSide d n
                      (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u)
                    =
                  bvt_F OS lgc n
                    ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
                      (BHW.realEmbed
                        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                          (1 : Equiv.Perm (Fin n)) u))) := by
                    rw [hsource_zero]
                _ =
                  BHW.extendF (bvt_F OS lgc n)
                    ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
                      (BHW.realEmbed
                        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                          (1 : Equiv.Perm (Fin n)) u))) := hcommon_ext_eq_bvt.symm
                _ =
                  BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                    (1 : Equiv.Perm (Fin n))
                    (BHW.realEmbed
                      (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                        (1 : Equiv.Perm (Fin n)) u)) := hordinary_pulled
            simpa [A0, Aord] using
              congrArg (fun c : ℂ => c * (φ0 : NPointDomain d n → ℂ) u) hpoint
          · have hnot : u ∉ tsupport (φ0 : NPointDomain d n → ℂ) := fun hut =>
              hu (hφ0U hut)
            have hzero : (φ0 : NPointDomain d n → ℂ) u = 0 :=
              image_eq_zero_of_notMem_tsupport hnot
            simp [hzero]
        rcases
            BHW.os45CommonEdge_initialSectorOverlap_traces_except_adjacentWick
              (d := d) hd OS lgc (P := P) (U := U)
              hU_compact hU_connected hU_closure with
          ⟨Ucx, Ford, Fadj, hUcx_open, hUcx_connected, hwick_mem, hcommon_mem,
            _hUcx_sub, hFord_holo, hFadj_holo, hFord_wick, _hFadj_seed,
            hFord_common, hFadj_common, hFadj_seed_trace⟩
        have hFadj_wick :
            ∀ u ∈ U,
              Fadj (fun k => wickRotatePoint (u k)) =
                bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) := by
          intro u hu
          have huP : u ∈ P.V := hU_sub hu
          let zWick : Fin n → Fin (d + 1) → ℂ :=
            fun k => wickRotatePoint (u k)
          let zAdj : Fin n → Fin (d + 1) → ℂ :=
            BHW.permAct (d := d) P.τ zWick
          have hzAdj_eq :
              zAdj = fun k => wickRotatePoint (u (P.τ k)) := by
            simp [zAdj, zWick,
              BHW.os45Figure24_permAct_ordinaryWick_eq_adjacentWick
                (d := d) (n := n) (hd := hd) (P := P) u]
          have hFadj_to_extendF :
              Fadj zWick =
                BHW.extendF (bvt_F OS lgc n) zAdj := by
            simpa [zWick, zAdj] using _hFadj_seed u hu
          have hzAdj_seedWindow :
              zAdj ∈
                ({z : Fin n → Fin (d + 1) → ℂ |
                    BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n} ∩
                  H.ΩJ) := by
            simpa [zWick, zAdj] using
              H.permAct_ordinaryWick_mem_OS412SeedWindow u huP
          have hzAdj_not_forward :
              zAdj ∉ BHW.ForwardTube d n := by
            simpa [zWick, zAdj] using
              H.permAct_ordinaryWick_not_mem_forwardTube u huP
          have hFadj_seed_at_zAdj :
              Fadj zAdj =
                bvt_F OS lgc n
                  (fun k => wickRotatePoint (u (P.τ k))) := by
            simpa [zWick, zAdj, hzAdj_eq] using hFadj_seed_trace u hu
          have hdeterministic_adjacent_trace :
              BHW.extendF (bvt_F OS lgc n) zAdj =
                bvt_F OS lgc n
                  (fun k => wickRotatePoint (u (P.τ k))) := by
            have hzAdj_initialOverlap :
                zAdj ∈ BHW.ExtendedTube d n ∩
                  BHW.permutedExtendedTubeSector d n P.τ := by
              constructor
              · simpa [zAdj, zWick] using
                  BHW.os45Figure24_adjacentWick_mem_extendedTube
                    (d := d) (n := n) (hd := hd) (P := P) huP
              · exact (H.OS412SeedWindow_subset_permutedSector
                  hzAdj_seedWindow).1
            have hzAdj_seedBranch_arg :
                BHW.permAct (d := d) P.τ zAdj =
                  fun k => wickRotatePoint (u k) := by
              calc
                BHW.permAct (d := d) P.τ zAdj =
                    BHW.permAct (d := d) P.τ
                      (fun k => wickRotatePoint (u (P.τ k))) := by
                        rw [hzAdj_eq]
                _ = fun k => wickRotatePoint (u k) :=
                    BHW.os45Figure24_permAct_adjacentWick_eq_ordinaryWick
                      (d := d) (n := n) (hd := hd) (P := P) u
            have hseedBranch_value :
                bvt_F OS lgc n (BHW.permAct (d := d) P.τ zAdj) =
                  bvt_F OS lgc n
                    (fun k => wickRotatePoint (u (P.τ k))) := by
              have hperm_raw :
                  bvt_F OS lgc n
                      (fun k => wickRotatePoint (u (P.τ k))) =
                    bvt_F OS lgc n (fun k => wickRotatePoint (u k)) := by
                simpa [BHW.permAct] using
                  bvt_F_perm (d := d) OS lgc n P.τ
                    (fun k => wickRotatePoint (u k))
              calc
                bvt_F OS lgc n (BHW.permAct (d := d) P.τ zAdj) =
                    bvt_F OS lgc n (fun k => wickRotatePoint (u k)) := by
                      rw [hzAdj_seedBranch_arg]
                _ =
                    bvt_F OS lgc n
                      (fun k => wickRotatePoint (u (P.τ k))) :=
                        hperm_raw.symm
            have hoverlap_branch_eq :
                BHW.extendF (bvt_F OS lgc n) zAdj =
                  bvt_F OS lgc n
                    (BHW.permAct (d := d) P.τ zAdj) := by
              have hExt_holo_near :
                  DifferentiableOn ℂ (BHW.extendF (bvt_F OS lgc n))
                    (BHW.ExtendedTube d n) :=
                BHW.differentiableOn_extendF_bvt_F_extendedTube
                  (d := d) OS lgc n
              have hSeed_holo_near :
                  DifferentiableOn ℂ
                    (fun z : Fin n → Fin (d + 1) → ℂ =>
                      bvt_F OS lgc n (BHW.permAct (d := d) P.τ z))
                    ({z : Fin n → Fin (d + 1) → ℂ |
                      BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n} ∩
                        H.ΩJ) :=
                H.differentiableOn_OS412SeedBranch OS lgc
            /-
              Exact remaining Vladimirov/BHW tempered-BV uniqueness leaf.

              The deterministic adjacent seed is now proved to lie in the
              true initial-sector overlap (`hzAdj_initialOverlap`).  On this
              overlap there are two concrete holomorphic germs:

              * `extendF (bvt_F OS lgc n)` on the ordinary extended tube;
              * `z ↦ bvt_F OS lgc n (permAct P.τ z)` on the OS-I `(4.12)`
                preimage-forward-tube seed window.

              The target has been reduced only by the checked permutation
              normalization `hseedBranch_value`: the remaining mathematical
              content is exactly the Vladimirov tempered-BV uniqueness
              comparison of these two germs at `zAdj`, using OS polynomial
              growth and equality of their tempered boundary distributions on
              the local Figure-2-4 collar.  The local holomorphy handles are
              `hExt_holo_near` and `hSeed_holo_near`; the absent producer is
              the BHW-to-flat-tube tempered boundary package plus its boundary
              distribution equality.
            -/
            exact
              ?os45_vladimirov_tempered_BV_initial_overlap_branch_eq_at_adjacent_wick
            exact hoverlap_branch_eq.trans hseedBranch_value
          exact hFadj_to_extendF.trans hdeterministic_adjacent_trace
        have hbranches_eq :
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
                      (1 : Equiv.Perm (Fin n)) u)) :=
          BHW.os45CommonEdge_pulledRealBranches_eqOn_of_E3_branchTraces
            (d := d) hd OS lgc (P := P)
            hU_open hU_connected.nonempty hU_sub
            hUcx_open hUcx_connected hwick_mem hcommon_mem
            Ford Fadj hFord_holo hFadj_holo hFord_wick hFadj_wick
            hFord_common hFadj_common
        have hB0_eq_Aord : B0 = Aord := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
          intro u
          by_cases hu : u ∈ U
          · simpa [B0, Aord] using
              congrArg (fun c : ℂ => c * (φ0 : NPointDomain d n → ℂ) u)
                (hbranches_eq u hu)
          · have hnot : u ∉ tsupport (φ0 : NPointDomain d n → ℂ) := fun hut =>
              hu (hφ0U hut)
            have hzero : (φ0 : NPointDomain d n → ℂ) u = 0 :=
              image_eq_zero_of_notMem_tsupport hnot
            simp [hzero]
        exact sub_eq_zero.mpr (hA0_eq_Aord.trans hB0_eq_Aord.symm)
      have hExt_to_zeroHeight :
          Tendsto Ext (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 (A0 - B0)) := by
        have hpair :=
          hplus_ext_to_quarterTurn_bvt.sub hminus_ext_to_adjacent_pulled
        simpa [Ext, A0, B0] using hpair
      have hExt_zero : Tendsto Ext (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
        simpa [hzero_height_boundary_distribution] using hExt_to_zeroHeight
      simpa using hExt_zero.sub hraw
    have hsum := htransport_error.add hraw
    simpa only [sub_add_cancel, zero_add] using hsum
    /-
      Retired circular attempt kept temporarily as route evidence.

      The old proof tried to create the same `hsource_ext` by first deriving
      transported Wick pairings and a source-representation handoff.  The
      adjacent zero-height step in that route reintroduced the same local
      `Ext - Raw → 0` collar transport, so it is no longer part of the active
      proof body.

    have htransported_wick_pairing :
        ∀ ψ : SchwartzNPoint d n,
          HasCompactSupport (ψ : NPointDomain d n → ℂ) →
          tsupport (ψ : NPointDomain d n → ℂ) ⊆ U →
          (∫ u : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) P.τ
                (fun k => wickRotatePoint (u k))) * ψ u) =
            ∫ u : NPointDomain d n,
              bvt_F OS lgc n (fun k => wickRotatePoint (u k)) * ψ u := by
      intro ψ _hψ_compact hψU
      have hpoint_on_U :
          ∀ u ∈ U,
            BHW.extendF (bvt_F OS lgc n)
                (BHW.permAct (d := d) P.τ
                  (fun k => wickRotatePoint (u k))) =
              bvt_F OS lgc n (fun k => wickRotatePoint (u k)) := by
        intro u hu
        have huP : u ∈ P.V := hU_sub hu
        let z0 : Fin n → Fin (d + 1) → ℂ :=
          BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (u k))
        have hz0_ET : z0 ∈ BHW.ExtendedTube d n := by
          simpa [z0] using
            BHW.os45Figure24_adjacentWick_mem_extendedTube
              (d := d) (n := n) (hd := hd) (P := P) huP
        have hz0_seed :
            z0 ∈
              ({z : Fin n → Fin (d + 1) → ℂ |
                  BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n} ∩
                H.ΩJ) := by
          simpa [z0] using
            H.permAct_ordinaryWick_mem_OS412SeedWindow u huP
        have hseed_eval :
            bvt_F OS lgc n (BHW.permAct (d := d) P.τ z0) =
              bvt_F OS lgc n (fun k => wickRotatePoint (u k)) := by
          simpa [z0] using
            BHW.os45Figure24_OS412SeedBranch_permAct_ordinaryWick_eq_ordinaryWick
              (d := d) (n := n) (hd := hd) (P := P) OS lgc u
        have hvladimirov_endpoint :
            BHW.extendF (bvt_F OS lgc n) z0 =
              bvt_F OS lgc n (BHW.permAct (d := d) P.τ z0) := by
          /-
            Vladimirov/BHW endpoint uniqueness leaf.

            At the corrected OS-I `(4.12)` seed point `z0`, the raw seed
            branch is already an `extendF` value because
            `permAct P.τ z0` lies in the ordinary forward tube.  The genuine
            remaining step is therefore not a global tube-domain uniqueness
            statement for `bvt_F ∘ permAct`; it is the local BHW/Vladimirov
            overlap equality between the two deterministic branches
            `extendF z` and `extendF (permAct P.τ z)` at the seed.

            This is the precise interface where the OS-I `(4.12)`--`(4.14)`
            tempered boundary-value uniqueness argument must produce the
            local Figure-2-4 two-sector EOW seed.
          -/
          have hz0_perm_forward :
              BHW.permAct (d := d) P.τ z0 ∈ BHW.ForwardTube d n :=
            hz0_seed.1
          have hF_holo :
              DifferentiableOn ℂ (bvt_F OS lgc n)
                (BHW.ForwardTube d n) := by
            simpa [BHW_forwardTube_eq (d := d) (n := n)] using
              bvt_F_holomorphic (d := d) OS lgc n
          have hF_lorentz :
              ∀ (Λ : LorentzLieGroup.RestrictedLorentzGroup d)
                (w : Fin n → Fin (d + 1) → ℂ), w ∈ BHW.ForwardTube d n →
                bvt_F OS lgc n
                  (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * w k ν) =
                bvt_F OS lgc n w := by
            intro Λ w hw
            exact bvt_F_restrictedLorentzInvariant_forwardTube
              (d := d) OS lgc n Λ w
              ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hw)
          have hseed_extendF :
              BHW.extendF (bvt_F OS lgc n)
                  (BHW.permAct (d := d) P.τ z0) =
                bvt_F OS lgc n (BHW.permAct (d := d) P.τ z0) :=
            BHW.extendF_eq_on_forwardTube n (bvt_F OS lgc n)
              hF_holo hF_lorentz
              (BHW.permAct (d := d) P.τ z0) hz0_perm_forward
          have hz0_perm_ET :
              BHW.permAct (d := d) P.τ z0 ∈ BHW.ExtendedTube d n :=
            BHW.forwardTube_subset_extendedTube hz0_perm_forward
          have hz0_overlap :
              z0 ∈
                {z : Fin n → Fin (d + 1) → ℂ |
                  z ∈ BHW.ExtendedTube d n ∧
                    BHW.permAct (d := d) P.τ z ∈ BHW.ExtendedTube d n} :=
            ⟨hz0_ET, hz0_perm_ET⟩
          have hdeterministic_overlap :
              BHW.extendF (bvt_F OS lgc n) z0 =
                BHW.extendF (bvt_F OS lgc n)
                  (BHW.permAct (d := d) P.τ z0) :=
            by
              /-
                `hz0_overlap` is the exact BHW overlap point where the
                Vladimirov/common-tempered-BV uniqueness producer must act.

                  The raw OS-I `(4.12)` analytic element is available on a
                  genuine metric ball around `z0`: on that ball it is the
                  deterministic adjacent branch `extendF ∘ permAct P.τ`, and
                  at `z0` its value is the adjacent Wick boundary value.  The
                  Vladimirov/EOW seed is produced at the common real Jost edge;
                  the checked BHW corridor and SCV identity theorem then carry
                  that seed back to a smaller `(4.12)` collar through `z0`.
                -/
                let Fdet : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
                  BHW.extendF (bvt_F OS lgc n)
                let common0 : Fin n → Fin (d + 1) → ℂ :=
                  (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
                    (BHW.realEmbed
                      (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                        (1 : Equiv.Perm (Fin n)) u))
                let pcommon : Fin n → Fin (d + 1) → ℂ :=
                  BHW.permAct (d := d) P.τ common0
                have hcommon_edge_seed :
                    ∃ Wc : Set (Fin n → Fin (d + 1) → ℂ),
                      IsOpen Wc ∧
                      common0 ∈ Wc ∧
                    Wc ⊆ BHW.ExtendedTube d n ∩
                      BHW.permutedExtendedTubeSector d n P.τ ∧
                      Set.EqOn Fdet
                        (fun z =>
                          Fdet (BHW.permAct (d := d) P.τ z)) Wc := by
                  /-
                    Vladimirov/BHW interface, now opened at the actual
                    distributional EOW consumer.

                    The ordinary branch already represents the canonical
                    common-edge CLM.  The remaining OS-I `(4.12)`--`(4.14)`
                    producer must show that the adjacent boundary branch has the
                    same tempered boundary distribution on this local flat Jost
                    window.  Once that zero-height adjacent CLM equality is
                    supplied, the checked local distributional EOW theorem below
                    creates the required complex-open common-edge seed.
                  -/
                  let e :=
                    BHW.os45CommonEdgeFlatCLE d n
                      (1 : Equiv.Perm (Fin n))
                  let E : Set (BHW.OS45FlatCommonChartReal d n) := e '' U
                  let x0 : BHW.OS45FlatCommonChartReal d n := e u
                  let Tlocal :
                      SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ] ℂ :=
                    BHW.os45FlatCommonChart_ordinaryEdgeCLM hd OS lgc P
                  have hE_open : IsOpen E := by
                    simpa [E, e] using e.toHomeomorph.isOpenMap U hU_open
                  have hE_sub :
                      E ⊆ BHW.os45FlatCommonChartEdgeSet d n P
                        (1 : Equiv.Perm (Fin n)) := by
                    rintro x ⟨v, hvU, rfl⟩
                    exact
                      (BHW.os45CommonEdgeFlatCLE_mem_edgeSet_iff d n P
                        (1 : Equiv.Perm (Fin n)) v).mpr (hU_sub hvU)
                  have hx0 : x0 ∈ E := ⟨u, hu, rfl⟩
                  have hm :
                      0 < BHW.os45FlatCommonChartDim d n :=
                    BHW.os45FlatCommonChartDim_pos_of_adjacent d n hi
                  rcases BHW.os45FlatCommonChartCone_eowReady d n with
                    ⟨hC_open, _hC_conv, _hC_zero, _hC_cone,
                      hC_nonempty⟩
                  obtain ⟨ys, hys_mem, hys_li⟩ :=
                    open_set_contains_basis hm
                      (BHW.os45FlatCommonChartCone d n)
                      hC_open hC_nonempty
                  have hzero_plus :
                      ∀ ψ : SchwartzMap
                          (BHW.OS45FlatCommonChartReal d n) ℂ,
                        HasCompactSupport
                          (ψ : BHW.OS45FlatCommonChartReal d n → ℂ) →
                        tsupport
                            (ψ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆ E →
                        (∫ x : BHW.OS45FlatCommonChartReal d n,
                          BHW.os45FlatCommonChartBranch d n OS lgc
                            (1 : Equiv.Perm (Fin n))
                            (fun a => (x a : ℂ)) * ψ x)
                        = Tlocal ψ := by
                    intro ψ hψ_compact hψE
                    exact
                      BHW.os45FlatCommonChart_plus_zeroHeight_pairing_eq_CLM_of_localRepresents
                        (d := d) hd OS lgc (P := P) Tlocal
                        (BHW.os45FlatCommonChart_ordinaryEdgeCLM_represents
                          hd OS lgc)
                        ψ hψ_compact (hψE.trans hE_sub)
                  have hzero_minus :
                      ∀ ψ : SchwartzMap
                          (BHW.OS45FlatCommonChartReal d n) ℂ,
                        HasCompactSupport
                          (ψ : BHW.OS45FlatCommonChartReal d n → ℂ) →
                        tsupport
                            (ψ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆ E →
                        (∫ x : BHW.OS45FlatCommonChartReal d n,
                          BHW.os45FlatCommonChartBranch d n OS lgc
                            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                            (fun a => (x a : ℂ)) * ψ x)
                        = Tlocal ψ := by
                    intro ψ hψ_compact hψE
                    have hψEdge :
                        tsupport
                            (ψ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
                          BHW.os45FlatCommonChartEdgeSet d n P
                            (1 : Equiv.Perm (Fin n)) :=
                      hψE.trans hE_sub
                    have hη_singleton :
                        ({η} : Set (BHW.OS45FlatCommonChartReal d n)) ⊆
                          BHW.os45FlatCommonChartCone d n := by
                      intro ξ hξ
                      simpa [Set.mem_singleton_iff.mp hξ] using hηC
                    have hminus_zeroHeight_limit :
                        Tendsto
                          (fun ε : ℝ =>
                            ∫ x : BHW.OS45FlatCommonChartReal d n,
                              BHW.os45FlatCommonChartBranch d n OS lgc
                                (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                                (fun a => (x a : ℂ) -
                                  (ε : ℂ) * (η a : ℂ) * Complex.I) *
                                ψ x)
                          (𝓝[Set.Ioi 0] (0 : ℝ))
                          (𝓝
                            (∫ x : BHW.OS45FlatCommonChartReal d n,
                              BHW.os45FlatCommonChartBranch d n OS lgc
                                (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                                (fun a => (x a : ℂ)) * ψ x)) := by
                      have hF_cont :
                          ContinuousOn
                            (BHW.os45FlatCommonChartBranch d n OS lgc
                              (P.τ.symm * (1 : Equiv.Perm (Fin n))))
                            (BHW.os45FlatCommonChartOmega d n
                              (P.τ.symm * (1 : Equiv.Perm (Fin n)))) :=
                        (BHW.differentiableOn_os45FlatCommonChartBranch
                          d n OS lgc
                          (P.τ.symm * (1 : Equiv.Perm (Fin n)))).continuousOn
                      have hside :
                          ∀ K : Set (BHW.OS45FlatCommonChartReal d n),
                            IsCompact K →
                            K ⊆ BHW.os45FlatCommonChartEdgeSet d n P
                              (1 : Equiv.Perm (Fin n)) →
                            ∀ Kη : Set (BHW.OS45FlatCommonChartReal d n),
                              IsCompact Kη →
                              Kη ⊆ BHW.os45FlatCommonChartCone d n →
                              ∃ r : ℝ, 0 < r ∧
                                ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ,
                                  0 < ε → ε < r →
                                  (fun a => (x a : ℂ) +
                                    ((-1 : ℝ) : ℂ) * (ε : ℂ) *
                                      (η a : ℂ) * Complex.I) ∈
                                    BHW.os45FlatCommonChartOmega d n
                                      (P.τ.symm *
                                        (1 : Equiv.Perm (Fin n))) := by
                        intro K hK hKE Kη hKη hKηC
                        obtain ⟨r, hr_pos, hr_mem⟩ :=
                          BHW.os45_BHWJost_flatCommonChart_localWedge_of_figure24
                            (d := d) hd (P := P) K hK hKE Kη hKη hKηC
                        refine ⟨r, hr_pos, ?_⟩
                        intro x hx η hη ε hε_pos hε_lt
                        have hmem := (hr_mem x hx η hη ε hε_pos hε_lt).2
                        simpa [sub_eq_add_neg, neg_mul, one_mul] using hmem
                      have hunif :=
                        SCV.tendstoUniformlyOn_sideIntegral_of_zeroHeight_pairing
                          (m := BHW.os45FlatCommonChartDim d n)
                          (E := BHW.os45FlatCommonChartEdgeSet d n P
                            (1 : Equiv.Perm (Fin n)))
                          (C := BHW.os45FlatCommonChartCone d n)
                          (Ωc := BHW.os45FlatCommonChartOmega d n
                            (P.τ.symm * (1 : Equiv.Perm (Fin n))))
                          (BHW.isOpen_os45FlatCommonChartOmega d n
                            (P.τ.symm * (1 : Equiv.Perm (Fin n))))
                          (BHW.os45FlatCommonChartBranch d n OS lgc
                            (P.τ.symm * (1 : Equiv.Perm (Fin n))))
                          hF_cont
                          (BHW.os45FlatCommonChart_real_mem_omega_adjacent
                            (d := d) hd (P := P))
                          (-1 : ℝ) hside
                          ({η} : Set (BHW.OS45FlatCommonChartReal d n))
                          isCompact_singleton hη_singleton ψ hψ_compact hψEdge
                          (∫ x : BHW.OS45FlatCommonChartReal d n,
                            BHW.os45FlatCommonChartBranch d n OS lgc
                              (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                              (fun a => (x a : ℂ)) * ψ x)
                          rfl
                      have hη_mem :
                          η ∈
                            ({η} :
                              Set (BHW.OS45FlatCommonChartReal d n)) := by
                        simp
                      simpa [sub_eq_add_neg, neg_mul, one_mul] using
                        hunif.tendsto_at hη_mem
                    have hminus_vladimirov_to_Tlocal :
                        Tendsto
                          (fun ε : ℝ =>
                            ∫ x : BHW.OS45FlatCommonChartReal d n,
                              BHW.os45FlatCommonChartBranch d n OS lgc
                              (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                              (fun a => (x a : ℂ) -
                                  (ε : ℂ) * (η a : ℂ) * Complex.I) *
                                ψ x)
                          (𝓝[Set.Ioi 0] (0 : ℝ))
                          (𝓝 (Tlocal ψ)) := by
                      let Plus : ℝ → ℂ := fun ε =>
                        ∫ x : BHW.OS45FlatCommonChartReal d n,
                          BHW.os45FlatCommonChartBranch d n OS lgc
                            (1 : Equiv.Perm (Fin n))
                            (fun a => (x a : ℂ) +
                              (ε : ℂ) * (η a : ℂ) * Complex.I) * ψ x
                      let Minus : ℝ → ℂ := fun ε =>
                        ∫ x : BHW.OS45FlatCommonChartReal d n,
                          BHW.os45FlatCommonChartBranch d n OS lgc
                            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                            (fun a => (x a : ℂ) -
                              (ε : ℂ) * (η a : ℂ) * Complex.I) * ψ x
                      have hplus_to_Tlocal :
                          Tendsto Plus (𝓝[Set.Ioi 0] (0 : ℝ))
                            (𝓝 (Tlocal ψ)) := by
                        have hplus_uniform :=
                          BHW.os45_BHWJost_flatCommonChart_distributionalBoundaryValue_plus_of_zeroHeight_pairingCLM
                            (d := d) hd OS lgc Tlocal
                            ({η} :
                              Set (BHW.OS45FlatCommonChartReal d n))
                            isCompact_singleton hη_singleton ψ hψ_compact
                            hψEdge (hzero_plus ψ hψ_compact hψE)
                        have hη_mem :
                            η ∈
                              ({η} :
                                Set (BHW.OS45FlatCommonChartReal d n)) := by
                          simp
                        simpa [Plus, one_mul] using
                          hplus_uniform.tendsto_at hη_mem
                      have hlocal_collar_diff :
                          Tendsto (fun ε : ℝ => Plus ε - Minus ε)
                            (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
                        have hsource_ext_local :
                            Tendsto
                              (fun ε : ℝ =>
                                (∫ u : NPointDomain d n,
                                  BHW.extendF (bvt_F OS lgc n)
                                    (BHW.os45FlatCommonChartSourceSide d n
                                      (1 : Equiv.Perm (Fin n)) (1 : ℝ)
                                      ε η u) *
                                    ((((D.toSideZeroDiagonalCLM
                                      (1 : Equiv.Perm (Fin n)) (1 : ℝ)
                                      ε η ψ).1 : SchwartzNPoint d n) :
                                        NPointDomain d n → ℂ) u)) -
                                ∫ u : NPointDomain d n,
                                  BHW.extendF (bvt_F OS lgc n)
                                    (BHW.permAct (d := d)
                                      (P.τ.symm *
                                        (1 : Equiv.Perm (Fin n))).symm
                                      (BHW.os45FlatCommonChartSourceSide d n
                                        (1 : Equiv.Perm (Fin n)) (-1 : ℝ)
                                        ε η u)) *
                                    ((((D.toSideZeroDiagonalCLM
                                      (1 : Equiv.Perm (Fin n)) (-1 : ℝ)
                                      ε η ψ).1 : SchwartzNPoint d n) :
                                        NPointDomain d n → ℂ) u))
                              (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
                          let Ext : ℝ → ℂ := fun ε =>
                            (∫ u : NPointDomain d n,
                              BHW.extendF (bvt_F OS lgc n)
                                (BHW.os45FlatCommonChartSourceSide d n
                                  (1 : Equiv.Perm (Fin n)) (1 : ℝ)
                                  ε η u) *
                                ((((D.toSideZeroDiagonalCLM
                                  (1 : Equiv.Perm (Fin n)) (1 : ℝ)
                                  ε η ψ).1 : SchwartzNPoint d n) :
                                    NPointDomain d n → ℂ) u)) -
                            ∫ u : NPointDomain d n,
                              BHW.extendF (bvt_F OS lgc n)
                                (BHW.permAct (d := d)
                                  (P.τ.symm *
                                    (1 : Equiv.Perm (Fin n))).symm
                                  (BHW.os45FlatCommonChartSourceSide d n
                                    (1 : Equiv.Perm (Fin n)) (-1 : ℝ)
                                    ε η u)) *
                                ((((D.toSideZeroDiagonalCLM
                                  (1 : Equiv.Perm (Fin n)) (-1 : ℝ)
                                  ε η ψ).1 : SchwartzNPoint d n) :
                                    NPointDomain d n → ℂ) u)
                          let Raw : ℝ → ℂ := fun ε =>
                            (∫ u : NPointDomain d n,
                              bvt_F OS lgc n
                                (fun k => wickRotatePoint (u k)) *
                                ((((D.toSideZeroDiagonalCLM
                                  (1 : Equiv.Perm (Fin n)) (1 : ℝ)
                                  ε η ψ).1 : SchwartzNPoint d n) :
                                    NPointDomain d n → ℂ) u)) -
                            ∫ u : NPointDomain d n,
                              bvt_F OS lgc n
                                (fun k => wickRotatePoint (u (P.τ k))) *
                                ((((D.toSideZeroDiagonalCLM
                                  (1 : Equiv.Perm (Fin n)) (-1 : ℝ)
                                  ε η ψ).1 : SchwartzNPoint d n) :
                                    NPointDomain d n → ℂ) u)
                          change Tendsto Ext (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0)
                          have hraw :
                              Tendsto Raw (𝓝[Set.Ioi 0] (0 : ℝ))
                                (𝓝 0) := by
                            simpa [Raw] using
                              D.sourceSide_ordinaryPlus_adjacentMinus_difference_tendsto_zero
                                OS lgc η hηC ψ hψ_compact hψEdge
                          have htransport_error :
                              Tendsto (fun ε : ℝ => Ext ε - Raw ε)
                                (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
                            /-
                              Genuine local Vladimirov/BHW producer input.

                              The OS source current `Raw` is already checked.
                              What remains is the tempered-BV uniqueness
                              transport from raw Wick-section source pairings
                              to the deterministic `extendF` pairings on the
                              same compact Figure-2-4 collar.
                            -/
                            exact
                              ?os45_vladimirov_raw_to_extendF_local_collar_error_zero
                          have hsum := htransport_error.add hraw
                          simpa only [sub_add_cancel, zero_add] using hsum
                        have hflat :=
                          D.tendsto_flatCommonChart_sideBranch_difference_zero_of_sourceSideDifference
                            (d := d) OS lgc η hηC ψ hψ_compact hψEdge
                            hsource_ext_local
                        simpa [Plus, Minus, one_mul, neg_mul, sub_eq_add_neg,
                          smul_eq_mul, mul_assoc] using hflat
                      have hminus_as_plus_sub :
                          Tendsto (fun ε : ℝ =>
                              Plus ε - (Plus ε - Minus ε))
                            (𝓝[Set.Ioi 0] (0 : ℝ))
                            (𝓝 (Tlocal ψ - 0)) :=
                        hplus_to_Tlocal.sub hlocal_collar_diff
                      simpa [Plus, Minus, sub_eq_add_neg, sub_sub_cancel,
                        one_mul, neg_mul, mul_assoc] using hminus_as_plus_sub
                    exact
                      tendsto_nhds_unique hminus_zeroHeight_limit
                        hminus_vladimirov_to_Tlocal
                  rcases
                      BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localZeroHeight_pairingsCLM
                        (d := d) hd OS lgc (P := P)
                        hE_open hE_sub ys hys_mem hys_li x0 hx0
                        Tlocal hzero_plus hzero_minus with
                    ⟨Wc, hWc_open, _hWc_pre, hx0Wc, hWc_sub, hWc_eq⟩
                  refine ⟨Wc, hWc_open, ?_, hWc_sub, ?_⟩
                  · have hcommon0_flat :
                        common0 =
                          (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
                            (BHW.unflattenCfg n d
                              (SCV.realEmbed x0)) := by
                      have hsource_zero :=
                        BHW.os45FlatCommonChartSourceSide_zero_eq_commonEdge
                          (d := d) (n := n)
                          (1 : Equiv.Perm (Fin n)) (1 : ℝ)
                          (0 : BHW.OS45FlatCommonChartReal d n) u
                      calc
                        common0 =
                            (BHW.os45QuarterTurnCLE
                              (d := d) (n := n)).symm
                              (BHW.realEmbed
                                (BHW.os45CommonEdgeRealPoint
                                  (d := d) (n := n)
                                  (1 : Equiv.Perm (Fin n)) u)) := rfl
                        _ =
                            BHW.os45FlatCommonChartSourceSide d n
                              (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0
                              (0 : BHW.OS45FlatCommonChartReal d n) u :=
                              hsource_zero.symm
                        _ =
                            (BHW.os45QuarterTurnCLE
                              (d := d) (n := n)).symm
                              (BHW.unflattenCfg n d
                                (SCV.realEmbed x0)) := by
                          have hreal :
                              SCV.realEmbed x0 =
                                (fun a : Fin
                                  (BHW.os45FlatCommonChartDim d n) =>
                                  ((x0) a : ℂ)) := rfl
                          rw [hreal]
                          ext k μ
                          simp [BHW.os45FlatCommonChartSourceSide, e, x0]
                    simpa [hcommon0_flat] using hx0Wc
                  · simpa [Fdet] using hWc_eq
                rcases hcommon_edge_seed with
                  ⟨Wc, hWc_open, hcommon0Wc, hWc_sub, hWc_eq⟩
                let Wτ : Set (Fin n → Fin (d + 1) → ℂ) :=
                  {z | BHW.permAct (d := d) P.τ z ∈ Wc}
                have hWτ_open : IsOpen Wτ := by
                  simpa [Wτ] using
                    hWc_open.preimage
                      (BHW.continuous_permAct (d := d) (n := n) P.τ)
                have hττ :
                    ∀ z : Fin n → Fin (d + 1) → ℂ,
                      BHW.permAct (d := d) P.τ
                          (BHW.permAct (d := d) P.τ z) = z := by
                  intro z
                  ext k μ
                  simp [BHW.permAct, P.τ_eq]
                have hpcommonWτ : pcommon ∈ Wτ := by
                  simpa [Wτ, pcommon] using
                    show BHW.permAct (d := d) P.τ pcommon ∈ Wc by
                      simpa [pcommon, hττ common0] using hcommon0Wc
                have hWτ_eq :
                    Set.EqOn Fdet
                      (fun z =>
                        Fdet (BHW.permAct (d := d) P.τ z)) Wτ := by
                  intro z hz
                  have h := hWc_eq hz
                  simpa [hττ z] using h.symm
                have hWτ_sub :
                    Wτ ⊆ BHW.ExtendedTube d n ∩
                      BHW.permutedExtendedTubeSector d n P.τ := by
                  intro z hz
                  have hz' := hWc_sub hz
                  constructor
                  · have hzET :
                        BHW.permAct (d := d) P.τ
                            (BHW.permAct (d := d) P.τ z) ∈
                          BHW.ExtendedTube d n := by
                      simpa [BHW.permutedExtendedTubeSector] using hz'.2
                    simpa [hττ z] using hzET
                  · simpa [BHW.permutedExtendedTubeSector] using hz'.1
                rcases
                    BHW.os45Figure24_adjacentWick_to_permActCommonEdge_endpointMetricBall
                      (d := d) (n := n) (hd := hd) (P := P) huP
                      hWτ_open hpcommonWτ with
                  ⟨Uprop, rprop, hUprop_open, hUprop_connected,
                    hadjUprop, _hpcommonUprop, hUprop_sub, hrprop_pos,
                    hcommon_ball_sub⟩
                have hz0_eq_adjacent :
                    z0 = fun k => wickRotatePoint (u (P.τ k)) := by
                  simp [z0,
                    BHW.os45Figure24_permAct_ordinaryWick_eq_adjacentWick
                      (d := d) (n := n) (hd := hd) (P := P) u]
                have hz0Uprop : z0 ∈ Uprop := by
                  simpa [hz0_eq_adjacent] using hadjUprop
                have hFdet_holo_Uprop :
                    DifferentiableOn ℂ Fdet Uprop :=
                  (BHW.differentiableOn_extendF_bvt_F_extendedTube
                    (d := d) OS lgc n).mono (by
                      intro z hz
                      exact (hUprop_sub hz).1)
                have hFdet_perm_holo_Uprop :
                    DifferentiableOn ℂ
                      (fun z =>
                        Fdet (BHW.permAct (d := d) P.τ z)) Uprop :=
                  (BHW.differentiableOn_extendF_bvt_F_permAct_preimageExtendedTube
                    (d := d) OS lgc n P.τ).mono (by
                      intro z hz
                      exact (hUprop_sub hz).2)
                have hcommon_ball_ne :
                    (Metric.ball pcommon rprop).Nonempty :=
                  ⟨pcommon, Metric.mem_ball_self hrprop_pos⟩
                have hcommon_ball_sub_Uprop :
                    Metric.ball pcommon rprop ⊆ Uprop := by
                  intro z hz
                  exact (hcommon_ball_sub hz).1
                have hcommon_ball_eq :
                    Set.EqOn Fdet
                      (fun z =>
                        Fdet (BHW.permAct (d := d) P.τ z))
                      (Metric.ball pcommon rprop) := by
                  intro z hz
                  exact hWτ_eq (hcommon_ball_sub hz).2
                have hUprop_eq :
                    Set.EqOn Fdet
                      (fun z =>
                        Fdet (BHW.permAct (d := d) P.τ z)) Uprop :=
                  identity_theorem_product_of_eqOn_open
                    hUprop_open hUprop_connected Metric.isOpen_ball
                    hcommon_ball_ne hcommon_ball_sub_Uprop
                    hFdet_holo_Uprop hFdet_perm_holo_Uprop
                    hcommon_ball_eq
                rcases
                    H.OS412SeedWindow_metricBallChartInWindow
                      OS lgc huP hUprop_open hz0Uprop with
                  ⟨Cseed, Bseed, rseed, hrseed_pos, hCseed_ball,
                    hz0Cseed_raw, hCseed_open, hCseed_pre, hCseed_sub,
                    hBseed_holo, hBseed_eq_raw, hBseed_trace⟩
                have hBseed_eq_adj :
                    Set.EqOn Bseed
                      (fun z : Fin n → Fin (d + 1) → ℂ =>
                        BHW.extendF (bvt_F OS lgc n)
                          (BHW.permAct (d := d) P.τ z)) Cseed := by
                  intro z hz
                  have hz_forward :
                      BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n :=
                    (hCseed_sub hz).1.1
                  have hext :
                      BHW.extendF (bvt_F OS lgc n)
                          (BHW.permAct (d := d) P.τ z) =
                        bvt_F OS lgc n
                          (BHW.permAct (d := d) P.τ z) :=
                    BHW.extendF_eq_on_forwardTube n (bvt_F OS lgc n)
                      hF_holo hF_lorentz
                      (BHW.permAct (d := d) P.τ z) hz_forward
                  exact (hBseed_eq_raw hz).trans hext.symm
                have hz0Cseed : z0 ∈ Cseed := by
                  simpa [z0] using hz0Cseed_raw
                have hBseed_adj :
                    Bseed z0 =
                      BHW.extendF (bvt_F OS lgc n)
                        (BHW.permAct (d := d) P.τ z0) := by
                  simpa [z0] using hBseed_eq_adj hz0Cseed
                have hordinary_matches_OS412_seed :
                    BHW.extendF (bvt_F OS lgc n) z0 = Bseed z0 := by
                  /-
                    The common-edge Vladimirov/EOW seed has already been
                    propagated across the checked Figure-2-4 corridor as
                    `hUprop_eq`.  Since the raw OS-I `(4.12)` branch agrees
                    with the deterministic adjacent model on `Cseed`, the
                    ordinary BHW branch agrees with that seed branch on the
                    smaller collar through `z0`.

                    Both analytic branches are now present on the same OS-I
                    `(4.12)` seed collar `Cseed`:

                    * ordinary side: the BHW extension `extendF (bvt_F OS lgc n)`,
                      holomorphic because `Cseed ⊆ ExtendedTube`;
                    * adjacent seed side: the raw `(4.12)` branch `Bseed`,
                      already holomorphic and already identified with
                      `extendF (bvt_F) ∘ permAct P.τ` on `Cseed`;
                    * boundary representative at `z0`: the ordinary Wick value,
                      by the seed normalization above.

                    The only remaining external producer is therefore the
                    common-edge open seed above, not a second local uniqueness
                    obligation on `Cseed`.
                  -/
                    have hordinary_eq_seed_on_Cseed :
                        Set.EqOn
                          (BHW.extendF (bvt_F OS lgc n)) Bseed Cseed := by
                      intro z hz
                      have hzU : z ∈ Uprop := (hCseed_sub hz).2
                      exact (hUprop_eq hzU).trans (hBseed_eq_adj hz).symm
                    exact hordinary_eq_seed_on_Cseed hz0Cseed
                exact hordinary_matches_OS412_seed.trans hBseed_adj
          exact hdeterministic_overlap.trans hseed_extendF
        exact hvladimirov_endpoint.trans hseed_eval
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro u
      by_cases hu : u ∈ U
      · exact congrArg (fun c : ℂ => c * ψ u) (hpoint_on_U u hu)
      · have hψ_zero : ψ u = 0 :=
          image_eq_zero_of_notMem_tsupport
            (fun hψ_supp => hu (hψU hψ_supp))
        simp [hψ_zero]
    have hrep :
        SCV.RepresentsDistributionOn
          (0 : SchwartzMap (NPointDomain d n) ℂ →L[ℂ] ℂ)
          (fun u : NPointDomain d n =>
            BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u)) -
              BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (1 : Equiv.Perm (Fin n))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u))) U := by
      rcases
          BHW.os45CommonEdge_initialSectorOverlap_traces_except_adjacentWick
            (d := d) hd OS lgc (P := P) (U := U)
            hU_compact hU_connected hU_closure with
        ⟨Ucx, Ford, Fadj, hUcx_open, hUcx_connected, hwick_mem,
          hcommon_mem, _hUcx_sub, hFord_holo, hFadj_holo, hFord_wick,
          hFadj_wick_extendF, hFord_common, hFadj_common,
          _hFadj0_seed_trace⟩
      let Hdiff : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
        fun z => Fadj z - Ford z
      have hHdiff_holo : DifferentiableOn ℂ Hdiff Ucx :=
        hFadj_holo.sub hFord_holo
      have hwick_pairing :
          ∀ ψ : SchwartzNPoint d n,
            HasCompactSupport (ψ : NPointDomain d n → ℂ) →
            tsupport (ψ : NPointDomain d n → ℂ) ⊆ U →
            (∫ u : NPointDomain d n,
              Fadj (fun k => wickRotatePoint (u k)) * ψ u) =
              ∫ u : NPointDomain d n,
                Ford (fun k => wickRotatePoint (u k)) * ψ u := by
        intro ψ hψ_compact hψU
        calc
          ∫ u : NPointDomain d n,
              Fadj (fun k => wickRotatePoint (u k)) * ψ u =
            ∫ u : NPointDomain d n,
              BHW.extendF (bvt_F OS lgc n)
                (BHW.permAct (d := d) P.τ
                  (fun k => wickRotatePoint (u k))) * ψ u := by
              refine MeasureTheory.integral_congr_ae
                (Filter.Eventually.of_forall ?_)
              intro u
              by_cases hu : u ∈ U
              · exact congrArg (fun c : ℂ => c * ψ u)
                  (hFadj_wick_extendF u hu)
              · have hψ_zero : ψ u = 0 :=
                  image_eq_zero_of_notMem_tsupport
                    (fun hψ_supp => hu (hψU hψ_supp))
                simp [hψ_zero]
          _ =
            ∫ u : NPointDomain d n,
              bvt_F OS lgc n (fun k => wickRotatePoint (u k)) * ψ u :=
              htransported_wick_pairing ψ hψ_compact hψU
          _ =
            ∫ u : NPointDomain d n,
              Ford (fun k => wickRotatePoint (u k)) * ψ u := by
              refine MeasureTheory.integral_congr_ae
                (Filter.Eventually.of_forall ?_)
              intro u
              by_cases hu : u ∈ U
              · exact congrArg (fun c : ℂ => c * ψ u)
                  (hFord_wick u hu).symm
              · have hψ_zero : ψ u = 0 :=
                  image_eq_zero_of_notMem_tsupport
                    (fun hψ_supp => hu (hψU hψ_supp))
                simp [hψ_zero]
      have hwick_pairing_zero :
          ∀ ψ : SchwartzNPoint d n,
            HasCompactSupport (ψ : NPointDomain d n → ℂ) →
            tsupport (ψ : NPointDomain d n → ℂ) ⊆ U →
            ∫ u : NPointDomain d n,
              Hdiff (fun k => wickRotatePoint (u k)) * ψ u = 0 := by
        intro ψ hψ_compact hψU
        let wick : NPointDomain d n → Fin n → Fin (d + 1) → ℂ :=
          fun u => fun k => wickRotatePoint (u k)
        have hwick_cont : Continuous wick := by
          simpa [wick] using
            BHW.continuous_wickRotateRealConfig (d := d) (n := n)
        have hFadj_cont :
            ContinuousOn (fun u : NPointDomain d n => Fadj (wick u)) U := by
          exact hFadj_holo.continuousOn.comp hwick_cont.continuousOn
            (by intro u hu; simpa [wick] using hwick_mem u hu)
        have hFord_cont :
            ContinuousOn (fun u : NPointDomain d n => Ford (wick u)) U := by
          exact hFord_holo.continuousOn.comp hwick_cont.continuousOn
            (by intro u hu; simpa [wick] using hwick_mem u hu)
        have hFadj_int :
            Integrable
              (fun u : NPointDomain d n => Fadj (wick u) * ψ u) :=
          SCV.integrable_continuousOn_mul_schwartz_of_supportsInOpen
            (H := fun u : NPointDomain d n => Fadj (wick u))
            (ψ := ψ) (U := U) hU_open hFadj_cont
            ⟨hψ_compact, hψU⟩
        have hFord_int :
            Integrable
              (fun u : NPointDomain d n => Ford (wick u) * ψ u) :=
          SCV.integrable_continuousOn_mul_schwartz_of_supportsInOpen
            (H := fun u : NPointDomain d n => Ford (wick u))
            (ψ := ψ) (U := U) hU_open hFord_cont
            ⟨hψ_compact, hψU⟩
        calc
          ∫ u : NPointDomain d n,
              Hdiff (fun k => wickRotatePoint (u k)) * ψ u =
            ∫ u : NPointDomain d n,
              Fadj (wick u) * ψ u - Ford (wick u) * ψ u := by
                refine MeasureTheory.integral_congr_ae
                  (Filter.Eventually.of_forall ?_)
                intro u
                simp [Hdiff, wick, sub_mul]
          _ =
            (∫ u : NPointDomain d n, Fadj (wick u) * ψ u) -
              ∫ u : NPointDomain d n, Ford (wick u) * ψ u :=
                MeasureTheory.integral_sub hFadj_int hFord_int
          _ = 0 := by
                rw [hwick_pairing ψ hψ_compact hψU]
                exact sub_self _
      have hcommon_trace :
          ∀ u ∈ U,
            Hdiff
              ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u))) =
              BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                  (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                  (BHW.realEmbed
                    (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                      (1 : Equiv.Perm (Fin n)) u)) -
                BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                  (1 : Equiv.Perm (Fin n))
                  (BHW.realEmbed
                    (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                      (1 : Equiv.Perm (Fin n)) u)) := by
        intro u hu
        change
          Fadj
              ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u))) -
            Ford
              ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u))) =
            BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u)) -
              BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (1 : Equiv.Perm (Fin n))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u))
        rw [hFadj_common u hu, hFord_common u hu]
      exact
        BHW.os45CommonEdge_localHorizontalDifference_representsZero_of_germ
          (d := d) hd OS lgc (P := P) U hU_open
          hU_connected.nonempty Ucx Hdiff hUcx_open hUcx_connected
          hwick_mem hcommon_mem hHdiff_holo hwick_pairing_zero
          hcommon_trace
    exact
      D.tendsto_sourceSide_extendF_difference_zero_of_sourceRepresentsOn
        (d := d) OS lgc hΩplus_open hΩminus_open hFplus_cont
        hFminus_cont hU_open (fun u hu => subset_closure hu) hU_compact
        η h0_plus h0_minus hrep φ hφ_compact hφU
    -/
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
