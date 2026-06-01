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

open Complex Topology MeasureTheory Filter

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
        BHW.os45CommonEdge_initialSectorOverlap_traces_except_adjacentWick
          (d := d) hd OS lgc (P := P)
          hU_compact hU_connected hU_closure with
      ⟨Ucx, Ford, Fadj, hUcx_open, hUcx_connected, hwick_mem, hcommon_mem,
        _hUcx_sub, hFord_holo, hFadj_holo, hFord_wick, hFadj_wick_extend,
        hFord_common, hFadj_common, _hFadj_perm_wick⟩
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
      exact ?os_i_section45_extendF_permAct_wick_transport
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
