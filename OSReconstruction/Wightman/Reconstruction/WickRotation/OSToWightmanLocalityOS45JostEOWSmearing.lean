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
      Active Vladimirov/BHW source-side transport leaf.

      `hsource_current` is the formal OS-I `(4.14)` Euclidean source-current
      comparison.  The remaining proof step is to identify, at each positive
      side height, those source-current pairings with the deterministic BHW
      `extendF` side-branch pairings.  This is the tempered-boundary-value
      uniqueness mechanism at the BHW/Vladimirov interface; the zero-height
      moving-test and flat-chart bookkeeping below is already checked.
    -/
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
    let Side : ℝ → ℂ := fun ε =>
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
    have hraw : Tendsto Raw (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
      simpa [Raw] using hsource_current
    have htransport :
        Tendsto (fun ε : ℝ => Side ε - Raw ε)
          (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
      let OrdinaryResidual : ℝ → ℂ := fun ε =>
        (∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.os45FlatCommonChartSourceSide d n
              (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η u) *
            ((((D.toSideZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
                SchwartzNPoint d n) : NPointDomain d n → ℂ) u)) -
        ∫ u : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
            ((((D.toSideZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
                SchwartzNPoint d n) : NPointDomain d n → ℂ) u)
      let AdjacentResidual : ℝ → ℂ := fun ε =>
        (∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
              (BHW.os45FlatCommonChartSourceSide d n
                (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η u)) *
            ((((D.toSideZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
                SchwartzNPoint d n) : NPointDomain d n → ℂ) u)) -
        ∫ u : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
            ((((D.toSideZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
                SchwartzNPoint d n) : NPointDomain d n → ℂ) u)
      have hdecompose :
          (fun ε : ℝ => Side ε - Raw ε) =
            fun ε : ℝ => OrdinaryResidual ε - AdjacentResidual ε := by
        funext ε
        dsimp [Side, Raw, OrdinaryResidual, AdjacentResidual]
        ring
      have hresidual_packet :
          Tendsto OrdinaryResidual
              (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) ∧
            Tendsto AdjacentResidual
              (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
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
        have hKηC :
            ({η} : Set (BHW.OS45FlatCommonChartReal d n)) ⊆
              BHW.os45FlatCommonChartCone d n := by
          intro ξ hξ
          simpa [Set.mem_singleton_iff.mp hξ] using hηC
        have hsource_pairings :=
          D.sideZeroDiagonal_sourcePairings_tendstoUniformlyOn_schwinger
            OS lgc ({η} : Set (BHW.OS45FlatCommonChartReal d n))
            isCompact_singleton hKηC φ hφ_compact hφE
        have hraw_plus :
            Tendsto
              (fun ε : ℝ =>
                ∫ u : NPointDomain d n,
                  bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
                    ((((D.toSideZeroDiagonalCLM
                      (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
                        SchwartzNPoint d n) : NPointDomain d n → ℂ) u))
              (𝓝[Set.Ioi 0] (0 : ℝ))
              (𝓝 (OS.S n
                (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ))) :=
          hsource_pairings.1.tendsto_at (by simp)
        have hraw_minus :
            Tendsto
              (fun ε : ℝ =>
                ∫ u : NPointDomain d n,
                  bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
                    ((((D.toSideZeroDiagonalCLM
                      (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
                        SchwartzNPoint d n) : NPointDomain d n → ℂ) u))
              (𝓝[Set.Ioi 0] (0 : ℝ))
              (𝓝 (OS.S n
                (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ))) :=
          hsource_pairings.2.2.2.tendsto_at (by simp)
        have hside_plus_pair :=
          D.tendsto_sourceSide_extendF_sideZeroDiagonalCLM_pair
            (d := d) OS lgc (1 : Equiv.Perm (Fin n))
            hΩplus_open (by simpa using hFplus_cont)
            hU_open (fun u hu => subset_closure hu) hU_compact η
            h0_plus h0_minus_plus φ hφ_compact hφU
        have hside_minus_pair :=
          D.tendsto_sourceSide_extendF_sideZeroDiagonalCLM_pair
            (d := d) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            hΩminus_open (by simpa using hFminus_cont)
            hU_open (fun u hu => subset_closure hu) hU_compact η
            h0_plus_minus h0_minus φ hφ_compact hφU
        have hordinary_zeroHeight_eq_schwinger :
            (∫ u : NPointDomain d n,
              BHW.extendF (bvt_F OS lgc n)
                (BHW.os45QuarterTurnConfig (d := d) (n := n)
                  (fun k => wickRotatePoint (u k))) *
                ((((D.toZeroDiagonalCLM
                  (1 : Equiv.Perm (Fin n)) φ).1 :
                    SchwartzNPoint d n) : NPointDomain d n → ℂ) u)) =
              OS.S n
                (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ) := by
          /-
            Vladimirov/BHW ordinary boundary-identification leaf.

            The checked moving-test theorem above reduces the ordinary
            residual to this scalar equality: the zero-height ordinary BHW
            common-edge boundary functional must be the same tempered
            boundary value as the Wick-section OS source current.  This is
            not endpoint continuity; it is the OS-I §4.5 mixed-tube
            uniqueness step from the Euclidean Wick section to the horizontal
            Figure-2-4 common edge.
          -/
          let SidePlus : ℝ → ℂ := fun ε =>
            ∫ u : NPointDomain d n,
              BHW.extendF (bvt_F OS lgc n)
                (BHW.os45FlatCommonChartSourceSide d n
                  (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η u) *
                ((((D.toSideZeroDiagonalCLM
                  (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
                    SchwartzNPoint d n) : NPointDomain d n → ℂ) u)
          let WickPlus : ℝ → ℂ := fun ε =>
            ∫ u : NPointDomain d n,
              bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
                ((((D.toSideZeroDiagonalCLM
                  (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
                    SchwartzNPoint d n) : NPointDomain d n → ℂ) u)
          have hside_limit :
              Tendsto SidePlus
                (𝓝[Set.Ioi 0] (0 : ℝ))
                (𝓝
                  (∫ u : NPointDomain d n,
                    BHW.extendF (bvt_F OS lgc n)
                      (BHW.os45QuarterTurnConfig (d := d) (n := n)
                        (fun k => wickRotatePoint (u k))) *
                      ((((D.toZeroDiagonalCLM
                        (1 : Equiv.Perm (Fin n)) φ).1 :
                          SchwartzNPoint d n) : NPointDomain d n → ℂ) u))) := by
            simpa [SidePlus] using hside_plus_pair.1
          have hwick_limit :
              Tendsto WickPlus
                (𝓝[Set.Ioi 0] (0 : ℝ))
                (𝓝
                  (OS.S n
                    (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ))) := by
            simpa [WickPlus] using hraw_plus
          have hordinary_transport :
              Tendsto (fun ε : ℝ => SidePlus ε - WickPlus ε)
                (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
            /-
              Vladimirov/BHW ordinary tempered-BV uniqueness leaf.

              This is the first honest OS-I `(4.12)` transport theorem still
              missing from the substrate: the ordinary BHW source-side tube
              branch and the Wick-section OS source-current branch have the
              same tempered boundary value on the local Figure-2-4 collar.
              Its proof should use the polynomial-growth/Vladimirov package for
              the pulled BHW branch, the Euclidean Wick-section source pairing,
              and uniqueness of the boundary value in the common tube chart.
            -/
            exact ?vladimirov_bhw_ordinary_sourceSide_to_wick_temperedBV
          have hside_minus_wick :
              Tendsto (fun ε : ℝ => SidePlus ε - WickPlus ε)
                (𝓝[Set.Ioi 0] (0 : ℝ))
                (𝓝
                  ((∫ u : NPointDomain d n,
                    BHW.extendF (bvt_F OS lgc n)
                      (BHW.os45QuarterTurnConfig (d := d) (n := n)
                        (fun k => wickRotatePoint (u k))) *
                      ((((D.toZeroDiagonalCLM
                        (1 : Equiv.Perm (Fin n)) φ).1 :
                          SchwartzNPoint d n) : NPointDomain d n → ℂ) u)) -
                    OS.S n
                      (D.toZeroDiagonalCLM
                        (1 : Equiv.Perm (Fin n)) φ))) :=
            hside_limit.sub hwick_limit
          have hzero :
              ((∫ u : NPointDomain d n,
                BHW.extendF (bvt_F OS lgc n)
                  (BHW.os45QuarterTurnConfig (d := d) (n := n)
                    (fun k => wickRotatePoint (u k))) *
                  ((((D.toZeroDiagonalCLM
                    (1 : Equiv.Perm (Fin n)) φ).1 :
                      SchwartzNPoint d n) : NPointDomain d n → ℂ) u)) -
                OS.S n
                  (D.toZeroDiagonalCLM
                    (1 : Equiv.Perm (Fin n)) φ)) = 0 :=
            tendsto_nhds_unique hside_minus_wick hordinary_transport
          exact sub_eq_zero.mp hzero
        have hadjacent_zeroHeight_eq_schwinger :
            (∫ u : NPointDomain d n,
              BHW.extendF (bvt_F OS lgc n)
                (BHW.permAct (d := d)
                  P.τ
                  (BHW.os45QuarterTurnConfig (d := d) (n := n)
                    (fun k => wickRotatePoint (u k)))) *
                ((((D.toZeroDiagonalCLM
                  (1 : Equiv.Perm (Fin n)) φ).1 :
                    SchwartzNPoint d n) : NPointDomain d n → ℂ) u)) =
              OS.S n
                (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ) := by
          /-
            Vladimirov/BHW adjacent boundary-identification leaf.

            This is the selected adjacent copy of the same mixed-tube
            uniqueness mechanism.  The existing
            `permAct_ordinaryWick_not_mem_forwardTube` obstruction rules out
            replacing it by `extendF_eq_on_forwardTube`; the proof has to
            identify the adjacent BHW source-side boundary value with the OS
            source current by tempered boundary-value uniqueness on the local
            Jost collar.
          -/
          let SideMinus : ℝ → ℂ := fun ε =>
            ∫ u : NPointDomain d n,
              BHW.extendF (bvt_F OS lgc n)
                (BHW.permAct (d := d)
                  (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
                  (BHW.os45FlatCommonChartSourceSide d n
                    (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η u)) *
                ((((D.toSideZeroDiagonalCLM
                  (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
                    SchwartzNPoint d n) : NPointDomain d n → ℂ) u)
          let WickMinus : ℝ → ℂ := fun ε =>
            ∫ u : NPointDomain d n,
              bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
                ((((D.toSideZeroDiagonalCLM
                  (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
                    SchwartzNPoint d n) : NPointDomain d n → ℂ) u)
          have hside_limit :
              Tendsto SideMinus
                (𝓝[Set.Ioi 0] (0 : ℝ))
                (𝓝
                  (∫ u : NPointDomain d n,
                    BHW.extendF (bvt_F OS lgc n)
                      (BHW.permAct (d := d)
                        P.τ
                        (BHW.os45QuarterTurnConfig (d := d) (n := n)
                          (fun k => wickRotatePoint (u k)))) *
                      ((((D.toZeroDiagonalCLM
                        (1 : Equiv.Perm (Fin n)) φ).1 :
                          SchwartzNPoint d n) : NPointDomain d n → ℂ) u))) := by
            simpa [SideMinus, P.τ_eq] using hside_minus_pair.2
          have hwick_limit :
              Tendsto WickMinus
                (𝓝[Set.Ioi 0] (0 : ℝ))
                (𝓝
                  (OS.S n
                    (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ))) := by
            simpa [WickMinus] using hraw_minus
          have hadjacent_transport :
              Tendsto (fun ε : ℝ => SideMinus ε - WickMinus ε)
                (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
            /-
              Vladimirov/BHW adjacent tempered-BV uniqueness leaf.

              This is the selected adjacent copy of the same OS-I transport,
              with the deterministic BHW branch `extendF ∘ permAct P.τ` in the
              local adjacent tube chart.  The forward-tube shortcut is blocked;
              the missing proof is the tempered boundary-value uniqueness
              argument on the adjacent Figure-2-4 collar.
            -/
            exact ?vladimirov_bhw_adjacent_sourceSide_to_wick_temperedBV
          have hside_minus_wick :
              Tendsto (fun ε : ℝ => SideMinus ε - WickMinus ε)
                (𝓝[Set.Ioi 0] (0 : ℝ))
                (𝓝
                  ((∫ u : NPointDomain d n,
                    BHW.extendF (bvt_F OS lgc n)
                      (BHW.permAct (d := d)
                        P.τ
                        (BHW.os45QuarterTurnConfig (d := d) (n := n)
                          (fun k => wickRotatePoint (u k)))) *
                      ((((D.toZeroDiagonalCLM
                        (1 : Equiv.Perm (Fin n)) φ).1 :
                          SchwartzNPoint d n) : NPointDomain d n → ℂ) u)) -
                    OS.S n
                      (D.toZeroDiagonalCLM
                        (1 : Equiv.Perm (Fin n)) φ))) :=
            hside_limit.sub hwick_limit
          have hzero :
              ((∫ u : NPointDomain d n,
                BHW.extendF (bvt_F OS lgc n)
                  (BHW.permAct (d := d)
                    P.τ
                    (BHW.os45QuarterTurnConfig (d := d) (n := n)
                      (fun k => wickRotatePoint (u k)))) *
                  ((((D.toZeroDiagonalCLM
                    (1 : Equiv.Perm (Fin n)) φ).1 :
                      SchwartzNPoint d n) : NPointDomain d n → ℂ) u)) -
                OS.S n
                  (D.toZeroDiagonalCLM
                    (1 : Equiv.Perm (Fin n)) φ)) = 0 :=
            tendsto_nhds_unique hside_minus_wick hadjacent_transport
          exact sub_eq_zero.mp hzero
        constructor
        · have hlim := hside_plus_pair.1.sub hraw_plus
          have hlim0 :
              Tendsto OrdinaryResidual
                (𝓝[Set.Ioi 0] (0 : ℝ))
                (𝓝
                  ((∫ u : NPointDomain d n,
                    BHW.extendF (bvt_F OS lgc n)
                      (BHW.os45FlatCommonChartSourceSide d n
                        (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u) *
                      ((((D.toZeroDiagonalCLM
                        (1 : Equiv.Perm (Fin n)) φ).1 :
                          SchwartzNPoint d n) : NPointDomain d n → ℂ) u)) -
                    OS.S n
                      (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ))) := by
            simpa [OrdinaryResidual] using hlim
          simpa [hordinary_zeroHeight_eq_schwinger] using hlim0
        · have hlim := hside_minus_pair.2.sub hraw_minus
          have hlim0 :
              Tendsto AdjacentResidual
                (𝓝[Set.Ioi 0] (0 : ℝ))
                (𝓝
                  ((∫ u : NPointDomain d n,
                    BHW.extendF (bvt_F OS lgc n)
                      (BHW.permAct (d := d)
                        (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
                        (BHW.os45FlatCommonChartSourceSide d n
                          (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η u)) *
                      ((((D.toZeroDiagonalCLM
                        (1 : Equiv.Perm (Fin n)) φ).1 :
                          SchwartzNPoint d n) : NPointDomain d n → ℂ) u)) -
                    OS.S n
                      (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ))) := by
            simpa [AdjacentResidual] using hlim
          simpa [hadjacent_zeroHeight_eq_schwinger] using hlim0
      rcases hresidual_packet with ⟨hOrdinary, hAdjacent⟩
      have hdiff := hOrdinary.sub hAdjacent
      simpa [hdecompose] using hdiff
    have hsum := htransport.add hraw
    have hside : Tendsto Side (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
      simpa only [Pi.add_apply, sub_add_cancel, zero_add] using hsum
    change Tendsto Side (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0)
    exact hside
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
