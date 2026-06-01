import OSReconstruction.SCV.VladimirovTillmann
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

      The honest OS-I `(4.12)` input is the transported adjacent Wick
      compact-test pairing.  Once that pairing is produced by the
      Vladimirov/BHW tempered-BV uniqueness argument, the existing
      initial-overlap trace theorem gives a holomorphic horizontal-difference
      germ; the checked source-representation moving theorem then supplies the
      finite-height `(4.14)` source-side residual.
    -/
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

            At the corrected OS-I `(4.12)` seed point `z0`, both the
            deterministic BHW branch `extendF (bvt_F)` and the raw seed branch
            `z ↦ bvt_F (permAct P.τ z)` are holomorphic in a local
            two-sector collar.  The missing producer is the tempered
            boundary-value uniqueness argument which shows that these two
            branches have the same distributional boundary value on the local
            Figure-2-4 Jost edge.  The facts `hz0_ET` and `hz0_seed` are the
            concrete domain carriers needed for that instantiation.
          -/
          let Fdet : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
            fun z => BHW.extendF (bvt_F OS lgc n) z
          let Fseed : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
            fun z => bvt_F OS lgc n (BHW.permAct (d := d) P.τ z)
          let Cseed : Set (Fin n → Fin (d + 1) → ℝ) :=
            ?os45_vladimirov_local_tube_cone
          let Wseed :
              SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
            ?os45_vladimirov_common_tempered_bv
          have hz0_tube : z0 ∈ TubeDomainSetPi Cseed :=
            ?os45_vladimirov_seed_mem_local_tube
          have hC_open : IsOpen Cseed :=
            ?os45_vladimirov_local_tube_open
          have hC_conv : Convex ℝ Cseed :=
            ?os45_vladimirov_local_tube_convex
          have hC_cone : IsCone Cseed :=
            ?os45_vladimirov_local_tube_conic
          have hC_salient : IsSalientCone Cseed :=
            ?os45_vladimirov_local_tube_salient
          have hC_nonempty : Cseed.Nonempty :=
            ?os45_vladimirov_local_tube_nonempty
          have hFdet_holo :
              DifferentiableOn ℂ Fdet (TubeDomainSetPi Cseed) :=
            ?os45_vladimirov_extendF_holomorphic_on_local_tube
          have hFseed_holo :
              DifferentiableOn ℂ Fseed (TubeDomainSetPi Cseed) :=
            ?os45_vladimirov_seed_branch_holomorphic_on_local_tube
          have hFG_int :
              ∀ y : Fin n → Fin (d + 1) → ℝ, y ∈ Cseed →
                ∀ ψ : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ,
                  Integrable (fun x : Fin n → Fin (d + 1) → ℝ =>
                    (Fdet (fun k μ =>
                        (x k μ : ℂ) + (y k μ : ℂ) * Complex.I) -
                      Fseed (fun k μ =>
                        (x k μ : ℂ) + (y k μ : ℂ) * Complex.I)) * ψ x) :=
            ?os45_vladimirov_difference_integrable_on_local_tube
          have hFdet_int :
              ∀ y : Fin n → Fin (d + 1) → ℝ, y ∈ Cseed →
                ∀ ψ : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ,
                  Integrable (fun x : Fin n → Fin (d + 1) → ℝ =>
                    Fdet (fun k μ =>
                        (x k μ : ℂ) + (y k μ : ℂ) * Complex.I) * ψ x) :=
            ?os45_vladimirov_extendF_integrable_on_local_tube
          have hFseed_int :
              ∀ y : Fin n → Fin (d + 1) → ℝ, y ∈ Cseed →
                ∀ ψ : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ,
                  Integrable (fun x : Fin n → Fin (d + 1) → ℝ =>
                    Fseed (fun k μ =>
                        (x k μ : ℂ) + (y k μ : ℂ) * Complex.I) * ψ x) :=
            ?os45_vladimirov_seed_branch_integrable_on_local_tube
          have hFdet_bv :
              ∀ η : Fin n → Fin (d + 1) → ℝ, η ∈ Cseed →
                ∀ φ : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ,
                  Filter.Tendsto
                    (fun ε : ℝ =>
                      ∫ x : Fin n → Fin (d + 1) → ℝ,
                        Fdet (fun k μ =>
                            (x k μ : ℂ) + (ε : ℂ) *
                              (η k μ : ℂ) * Complex.I) * φ x)
                    (nhdsWithin 0 (Set.Ioi 0)) (nhds (Wseed φ)) :=
            ?os45_vladimirov_extendF_boundary_value_on_jost_edge
          have hFseed_bv :
              ∀ η : Fin n → Fin (d + 1) → ℝ, η ∈ Cseed →
                ∀ φ : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ,
                  Filter.Tendsto
                    (fun ε : ℝ =>
                      ∫ x : Fin n → Fin (d + 1) → ℝ,
                        Fseed (fun k μ =>
                            (x k μ : ℂ) + (ε : ℂ) *
                              (η k μ : ℂ) * Complex.I) * φ x)
                    (nhdsWithin 0 (Set.Ioi 0)) (nhds (Wseed φ)) :=
            ?os45_vladimirov_seed_branch_boundary_value_on_jost_edge
          have hunique :
              Set.EqOn Fdet Fseed (TubeDomainSetPi Cseed) :=
            tube_holomorphic_unique_from_bv
              Cseed hC_open hC_conv hC_cone hC_salient hC_nonempty
              Fdet Fseed hFdet_holo hFseed_holo hFG_int hFdet_int
              hFseed_int Wseed hFdet_bv hFseed_bv
          exact hunique hz0_tube
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
