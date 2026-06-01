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
-/
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
  let e := BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n))
  let E : Set (BHW.OS45FlatCommonChartReal d n) := e '' U
  have hE_open : IsOpen E := by
    simpa [E, e] using e.toHomeomorph.isOpenMap U hU_open
  have hE_sub :
      E ⊆ BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)) := by
    rintro x ⟨u, huU, rfl⟩
    exact
      (BHW.os45CommonEdgeFlatCLE_mem_edgeSet_iff d n P
        (1 : Equiv.Perm (Fin n)) u).mpr
        (hU_closure (subset_closure huU))
  have hJost_edge_eq :
      ∀ x ∈ E,
        BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (SCV.realEmbed x) =
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (SCV.realEmbed x) := by
    rcases
        BHW.os45Figure24_initialSectorOverlap_chartNeighborhood
          (d := d) (n := n) (hd := hd) (P := P)
          hU_compact hU_connected hU_closure with
      ⟨Ucx, hUcx_open, hUcx_connected, hwick_mem, hcommon_mem, hUcx_sub⟩
    let Ford : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
      BHW.extendF (bvt_F OS lgc n)
    let Fadj : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
      fun z =>
        BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) P.τ z)
    have hFord_holo : DifferentiableOn ℂ Ford Ucx := by
      exact
        (BHW.differentiableOn_extendF_bvt_F_extendedTube
          (d := d) OS lgc n).mono (by
            intro z hz
            exact (hUcx_sub hz).1)
    have hFadj_holo : DifferentiableOn ℂ Fadj Ucx := by
      exact
        (BHW.differentiableOn_extendF_bvt_F_permAct_preimageExtendedTube
          (d := d) OS lgc n P.τ).mono (by
            intro z hz
            simpa [BHW.permutedExtendedTubeSector] using (hUcx_sub hz).2)
    have hFord_wick :
        ∀ u ∈ U,
          Ford (fun k => wickRotatePoint (u k)) =
            bvt_F OS lgc n (fun k => wickRotatePoint (u k)) := by
      intro u hu
      have huP : u ∈ P.V := hU_closure (subset_closure hu)
      have hF_holo :
          DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
        simpa [BHW_forwardTube_eq (d := d) (n := n)] using
          bvt_F_holomorphic (d := d) OS lgc n
      have hF_lorentz :
          ∀ (Λ : RestrictedLorentzGroup d)
            (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
            bvt_F OS lgc n
              (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) =
            bvt_F OS lgc n z := by
        intro Λ z hz
        exact bvt_F_restrictedLorentzInvariant_forwardTube
          (d := d) OS lgc n Λ z
          ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
      have hforward :
          (fun k => wickRotatePoint (u k)) ∈ BHW.ForwardTube d n :=
        BHW.os45Figure24_ordinaryWick_mem_forwardTube
          (d := d) (n := n) (hd := hd) (P := P) huP
      exact
        BHW.extendF_eq_on_forwardTube n (bvt_F OS lgc n)
          hF_holo hF_lorentz
          (fun k => wickRotatePoint (u k)) hforward
    have hFadj_wick_extend :
        ∀ u ∈ U,
          Fadj (fun k => wickRotatePoint (u k)) =
            BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) P.τ
                (fun k => wickRotatePoint (u k))) := by
      intro _u _hu
      rfl
    have hFord_common :
        ∀ u ∈ U,
          Ford
            ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u))) =
            BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
              (1 : Equiv.Perm (Fin n))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u)) := by
      intro u _hu
      simp [Ford, BHW.os45PulledRealBranch]
    have hFadj_common :
        ∀ u ∈ U,
          Fadj
            ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u))) =
            BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin n)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u)) := by
      intro u _hu
      simpa [Fadj] using
        BHW.os45Figure24CommonEdge_permAct_extendF_eq_adjacentPulledRealBranch
          (d := d) (n := n) hd OS lgc (P := P) u
    have htransported_wick_pairing :
        ∀ ψ : SchwartzNPoint d n,
          HasCompactSupport (ψ : NPointDomain d n → ℂ) →
          tsupport (ψ : NPointDomain d n → ℂ) ⊆ U →
          ∫ u : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) P.τ
                (fun k => wickRotatePoint (u k))) * ψ u =
          ∫ u : NPointDomain d n,
            bvt_F OS lgc n (fun k => wickRotatePoint (u k)) * ψ u := by
      have hlocal_eow_seed :
          ∃ W : Set (Fin n → Fin (d + 1) → ℂ),
            IsOpen W ∧ W.Nonempty ∧ W ⊆ Ucx ∧ Set.EqOn Fadj Ford W := by
        rcases hU_connected.nonempty with ⟨u0, hu0⟩
        let bv : BHW.OS45FlatCommonChartReal d n → ℂ := fun x =>
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n)) (SCV.realEmbed x)
        have hbv_cont : ContinuousOn bv E := by
          simpa [bv] using
            (BHW.continuousOn_os45FlatCommonChartBranch_realEdge
              (d := d) hd OS lgc (P := P)
              (1 : Equiv.Perm (Fin n)) (1 : Equiv.Perm (Fin n))
              (BHW.os45FlatCommonChart_real_mem_omega_id
                (d := d) hd (P := P))).mono hE_sub
        have hplus_bv :
            ∀ x ∈ E,
              Filter.Tendsto
                (BHW.os45FlatCommonChartBranch d n OS lgc
                  (1 : Equiv.Perm (Fin n)))
                (nhdsWithin (SCV.realEmbed x)
                  (BHW.os45FlatCommonChartOmega d n
                    (1 : Equiv.Perm (Fin n))))
                (nhds (bv x)) := by
          intro x hx
          have hxΩ :
              SCV.realEmbed x ∈
                BHW.os45FlatCommonChartOmega d n
                  (1 : Equiv.Perm (Fin n)) :=
            BHW.os45FlatCommonChart_real_mem_omega_id
              (d := d) hd (P := P) x (hE_sub hx)
          simpa [bv] using
            BHW.tendsto_os45FlatCommonChartBranch_realEdge
              (d := d) OS lgc (1 : Equiv.Perm (Fin n)) hxΩ
        have hminus_bv :
            ∀ x ∈ E,
              Filter.Tendsto
                (BHW.os45FlatCommonChartBranch d n OS lgc
                  (P.τ.symm * (1 : Equiv.Perm (Fin n))))
                (nhdsWithin (SCV.realEmbed x)
                  (BHW.os45FlatCommonChartOmega d n
                    (P.τ.symm * (1 : Equiv.Perm (Fin n)))))
                (nhds (bv x)) := by
          exact ?os_i_section45_adjacent_boundary_value_to_ordinary_trace
        let x0 : BHW.OS45FlatCommonChartReal d n := e u0
        have hx0 : x0 ∈ E := ⟨u0, hu0, rfl⟩
        rcases
            BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_continuousBoundaryOn
              (d := d) hd OS lgc (P := P)
              hE_open hE_sub bv hbv_cont hplus_bv hminus_bv x0 hx0 with
          ⟨W0, hW0_open, _hW0_pre, hz0W0, _hW0_sub, hW0_eq⟩
        let z0 : Fin n → Fin (d + 1) → ℂ :=
          (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.unflattenCfg n d (SCV.realEmbed x0))
        have hz0Ucx : z0 ∈ Ucx := by
          simpa [z0, x0, e, BHW.os45CommonEdgeFlatCLE, SCV.realEmbed,
            BHW.unflattenCfg, BHW.os45CommonEdgeRealPoint,
            flattenCLEquivReal_apply] using hcommon_mem u0 hu0
        refine ⟨W0 ∩ Ucx, hW0_open.inter hUcx_open, ?_, ?_, ?_⟩
        · exact ⟨z0, ⟨by simpa [z0] using hz0W0, hz0Ucx⟩⟩
        · intro z hz
          exact hz.2
        · intro z hz
          simpa [Ford, Fadj] using (hW0_eq hz.1).symm
      have hEqUcx : Set.EqOn Fadj Ford Ucx := by
        rcases hlocal_eow_seed with ⟨W, hW_open, hW_ne, hW_sub, hW_eq⟩
        exact
          identity_theorem_product_of_eqOn_open
            hUcx_open hUcx_connected hW_open hW_ne hW_sub
            hFadj_holo hFord_holo hW_eq
      intro ψ _hψ_compact hψU
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro u
      by_cases hu : u ∈ U
      · have hEq :
            Fadj (fun k => wickRotatePoint (u k)) =
              Ford (fun k => wickRotatePoint (u k)) :=
          hEqUcx (hwick_mem u hu)
        calc
          BHW.extendF (bvt_F OS lgc n)
                (BHW.permAct (d := d) P.τ
                  (fun k => wickRotatePoint (u k))) * ψ u =
              Fadj (fun k => wickRotatePoint (u k)) * ψ u := by
                exact congrArg (fun c : ℂ => c * ψ u)
                  (hFadj_wick_extend u hu).symm
          _ = Ford (fun k => wickRotatePoint (u k)) * ψ u := by
                exact congrArg (fun c : ℂ => c * ψ u) hEq
          _ = bvt_F OS lgc n (fun k => wickRotatePoint (u k)) * ψ u := by
                exact congrArg (fun c : ℂ => c * ψ u) (hFord_wick u hu)
      · have hψ_zero : ψ u = 0 :=
          image_eq_zero_of_notMem_tsupport
            (fun hψ_supp => hu (hψU hψ_supp))
        simp [hψ_zero]
    have hwick_pairing :
        ∀ ψ : SchwartzNPoint d n,
          HasCompactSupport (ψ : NPointDomain d n → ℂ) →
          tsupport (ψ : NPointDomain d n → ℂ) ⊆ U →
          ∫ u : NPointDomain d n,
            Fadj (fun k => wickRotatePoint (u k)) * ψ u =
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
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro u
            by_cases hu : u ∈ U
            · exact congrArg (fun c : ℂ => c * ψ u)
                (hFadj_wick_extend u hu)
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
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro u
            by_cases hu : u ∈ U
            · exact congrArg (fun c : ℂ => c * ψ u) (hFord_wick u hu).symm
            · have hψ_zero : ψ u = 0 :=
                image_eq_zero_of_notMem_tsupport
                  (fun hψ_supp => hu (hψU hψ_supp))
              simp [hψ_zero]
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
                  (1 : Equiv.Perm (Fin n)) u)) :=
      BHW.os45CommonEdge_pulledRealBranches_eqOn_of_wickPairings
        (d := d) hd OS lgc (P := P)
        hU_open hU_connected.nonempty hUcx_open hUcx_connected
        hwick_mem hcommon_mem Ford Fadj hFord_holo hFadj_holo
        hwick_pairing hFord_common hFadj_common
    exact
      BHW.os45FlatCommonChart_realEdge_branch_eq_of_source_commonEdge_branch_eqOn
        (d := d) hd OS lgc (P := P) (U := U) hsource_eq
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro x
  by_cases hxφ :
      x ∈ Function.support
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ)
  · have hxE : x ∈ E :=
      hφU (subset_tsupport _ hxφ)
    exact congrArg (fun c : ℂ => c * φ x) (hJost_edge_eq x hxE)
  · have hφx : φ x = 0 := by
      by_contra hne
      exact hxφ (by simpa [Function.mem_support] using hne)
    simp [hφx]

end BHW
