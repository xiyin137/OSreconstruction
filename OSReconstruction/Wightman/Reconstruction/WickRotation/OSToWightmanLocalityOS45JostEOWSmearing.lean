import OSReconstruction.SCV.VladimirovTillmann
import OSReconstruction.SCV.LocalBoundaryRecovery
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
wrapper around the blocker. The named placeholder below sits inside the
opened proof body and marks the remaining Vladimirov/BHW
tempered-boundary-value producer obligation.
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
The proof body should follow the monograph part-(b) route: construct Jost
neighbourhoods on the local real edge, use Euclidean source permutation
symmetry plus the identity theorem to identify the two holomorphic branches,
apply distributional EOW on the common real edge, then smear by a finite
partition of unity over the compact support of `φ`.

The live obligation is the distributional compact-test equality itself, not a
pointwise adjacent-Wick trace statement or a source-representation wrapper. -/
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
    ⟨_hC_open, _hC_convex, _hC_zero, _hC_smul, hC_nonempty⟩
  rcases hC_nonempty with ⟨η, hηC⟩
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
        (𝓝 0) := by
      /-
        Vladimirov/BHW finite-height source-current leaf.

        The checked OS-I `(4.14)` source-current comparison gives the raw
        Wick-section difference limit.  What remains is the true BHW/Jost
        transport: identify the deterministic Figure-2-4 two-sheet source
        difference with that raw Wick-section difference in the same moving
        source tests.
      -/
      let ExtPlus : ℝ → ℂ := fun ε =>
        ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.os45FlatCommonChartSourceSide d n
              (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η u) *
            ((((D.toSideZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
                SchwartzNPoint d n) : NPointDomain d n → ℂ) u)
      let ExtMinus : ℝ → ℂ := fun ε =>
        ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
              (BHW.os45FlatCommonChartSourceSide d n
                (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η u)) *
            ((((D.toSideZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
                SchwartzNPoint d n) : NPointDomain d n → ℂ) u)
      let RawPlus : ℝ → ℂ := fun ε =>
        ∫ u : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
            ((((D.toSideZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
                SchwartzNPoint d n) : NPointDomain d n → ℂ) u)
      let RawMinus : ℝ → ℂ := fun ε =>
        ∫ u : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
            ((((D.toSideZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
                SchwartzNPoint d n) : NPointDomain d n → ℂ) u)
      have hraw :
          Tendsto
            (fun ε : ℝ => RawPlus ε - RawMinus ε)
            (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
        simpa [RawPlus, RawMinus] using
          D.sourceSide_ordinaryPlus_adjacentMinus_difference_tendsto_zero
            OS lgc η hηC φ hφ_compact hφE
      have hresidual :
          Tendsto
            (fun ε : ℝ =>
              (ExtPlus ε - ExtMinus ε) - (RawPlus ε - RawMinus ε))
            (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
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
          /-
            Remaining OS-I `(4.12)`/Vladimirov payload: the adjacent
            deterministic seed branch `extendF ∘ permAct P.τ` has the same
            compact source-window Wick-section boundary pairings as the
            ordinary Wightman branch.  This is the tempered BV uniqueness
            step at the Vladimirov/BHW interface.
          -/
          exact ?os45_vladimirov_OS412_seed_to_wick_pairing_transport
        have hsource :
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
                hU_compact hU_connected hU_closure with
            ⟨Ucx, Ford, Fadj, hUcx_open, hUcx_connected, hwick_mem,
              hcommon_mem, _hUcx_sub, hFord_holo, hFadj_holo,
              hFord_wick, hFadj_wick, hFord_common, hFadj_common,
              _hFadj_adjWick⟩
          refine
            BHW.os45CommonEdge_pulledRealBranches_eqOn_of_wickPairings
              (d := d) hd OS lgc (P := P) hU_open
              hU_connected.nonempty hUcx_open hUcx_connected hwick_mem
              hcommon_mem Ford Fadj hFord_holo hFadj_holo ?_
              hFord_common hFadj_common
          intro ψ hψ_compact hψU
          have hFadj_pair :
              (∫ u : NPointDomain d n,
                Fadj (fun k => wickRotatePoint (u k)) * ψ u) =
              ∫ u : NPointDomain d n,
                BHW.extendF (bvt_F OS lgc n)
                  (BHW.permAct (d := d) P.τ
                    (fun k => wickRotatePoint (u k))) * ψ u := by
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro u
            by_cases hu : u ∈ U
            · exact congrArg (fun c : ℂ => c * ψ u) (hFadj_wick u hu)
            · have hψ_zero : ψ u = 0 :=
                image_eq_zero_of_notMem_tsupport
                  (fun hψ_supp => hu (hψU hψ_supp))
              simp [hψ_zero]
          have hFord_pair :
              (∫ u : NPointDomain d n,
                Ford (fun k => wickRotatePoint (u k)) * ψ u) =
              ∫ u : NPointDomain d n,
                bvt_F OS lgc n (fun k => wickRotatePoint (u k)) * ψ u := by
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro u
            by_cases hu : u ∈ U
            · exact congrArg (fun c : ℂ => c * ψ u) (hFord_wick u hu)
            · have hψ_zero : ψ u = 0 :=
                image_eq_zero_of_notMem_tsupport
                  (fun hψ_supp => hu (hψU hψ_supp))
              simp [hψ_zero]
          exact
            hFadj_pair.trans
              ((htransported_wick_pairing ψ hψ_compact hψU).trans
                hFord_pair.symm)
        let Ghoriz : NPointDomain d n → ℂ := fun u =>
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
        have hrep :
            SCV.RepresentsDistributionOn
              (0 : SchwartzMap (NPointDomain d n) ℂ →L[ℂ] ℂ)
              Ghoriz U := by
          have hpoint : ∀ u ∈ U, Ghoriz u = 0 := by
            intro u hu
            exact sub_eq_zero.mpr (hsource u hu)
          intro ψ hψU
          calc
            (0 : SchwartzMap (NPointDomain d n) ℂ →L[ℂ] ℂ) ψ
                = ∫ u : NPointDomain d n, (0 : ℂ) * ψ u := by simp
            _ = ∫ u : NPointDomain d n, Ghoriz u * ψ u := by
                exact
                  BHW.integral_eq_of_tsupport_subset_of_pointwise_on
                    (d := d) (n := n) U (fun _ => 0) Ghoriz ψ hψU.2
                    (by
                      intro u hu
                      exact (hpoint u hu).symm)
        have hΩplus_open : IsOpen (BHW.ExtendedTube d n) :=
          BHW.isOpen_extendedTube
        have hΩminus_open :
            IsOpen (BHW.permutedExtendedTubeSector d n P.τ) :=
          BHW.isOpen_permutedExtendedTubeSector (d := d) (n := n) P.τ
        have hFplus_cont :
            ContinuousOn
              (fun z : Fin n → Fin (d + 1) → ℂ =>
                BHW.extendF (bvt_F OS lgc n) z)
              (BHW.ExtendedTube d n) :=
          (BHW.differentiableOn_extendF_bvt_F_extendedTube
            (d := d) OS lgc n).continuousOn
        have hFminus_cont :
            ContinuousOn
              (fun z : Fin n → Fin (d + 1) → ℂ =>
                BHW.extendF (bvt_F OS lgc n)
                  (BHW.permAct (d := d)
                    (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm z))
              (BHW.permutedExtendedTubeSector d n P.τ) := by
          simpa [BHW.permutedExtendedTubeSector] using
            (BHW.differentiableOn_extendF_bvt_F_permAct_preimageExtendedTube
              (d := d) OS lgc n P.τ).continuousOn
        have h0_plus :
            ∀ u ∈ closure U,
              BHW.os45FlatCommonChartSourceSide d n
                (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u ∈
                  BHW.ExtendedTube d n := by
          intro u hu
          have huV : u ∈ closure P.V :=
            subset_closure (hU_closure hu)
          have hmem :=
            BHW.os45Figure24_commonEdge_mem_initialSectorOverlap
              (d := d) (n := n) (hd := hd) (P := P) huV
          rw [BHW.os45FlatCommonChartSourceSide_zero_eq_commonEdge]
          exact hmem.1
        have h0_minus :
            ∀ u ∈ closure U,
              BHW.os45FlatCommonChartSourceSide d n
                (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η u ∈
                  BHW.permutedExtendedTubeSector d n P.τ := by
          intro u hu
          have huV : u ∈ closure P.V :=
            subset_closure (hU_closure hu)
          have hmem :=
            BHW.os45Figure24_commonEdge_mem_initialSectorOverlap
              (d := d) (n := n) (hd := hd) (P := P) huV
          rw [BHW.os45FlatCommonChartSourceSide_zero_eq_commonEdge]
          exact hmem.2
        have hsrc_ext :
            Tendsto
              (fun ε : ℝ => ExtPlus ε - ExtMinus ε)
              (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
          have hrep' :
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
            simpa [Ghoriz] using hrep
          simpa [ExtPlus, ExtMinus] using
            D.tendsto_sourceSide_extendF_difference_zero_of_sourceRepresentsOn
              (d := d) OS lgc hΩplus_open hΩminus_open
              hFplus_cont hFminus_cont hU_open subset_closure hU_compact
              η h0_plus h0_minus hrep' φ hφ_compact hφU
        simpa [ExtPlus, ExtMinus, RawPlus, RawMinus] using
          hsrc_ext.sub hraw
      have hsrc :
          Tendsto
            (fun ε : ℝ =>
              (RawPlus ε - RawMinus ε) +
                ((ExtPlus ε - ExtMinus ε) - (RawPlus ε - RawMinus ε)))
            (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
        simpa using hraw.add hresidual
      have hsrc_target :
          Tendsto
            (fun ε : ℝ => ExtPlus ε - ExtMinus ε)
            (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
        refine Tendsto.congr' ?_ hsrc
        filter_upwards with ε
        dsimp [ExtPlus, ExtMinus, RawPlus, RawMinus]
        ring
      exact
        D.tendsto_flatCommonChart_sideBranch_difference_zero_of_sourceSideDifference
          (d := d) OS lgc η hηC φ hφ_compact hφE
          (by simpa [ExtPlus, ExtMinus] using hsrc_target)
  have hzero :=
    D.zeroHeightPairing_of_tendsto_flatCommonChart_sideBranch_difference_zero
      (d := d) OS lgc η hηC φ hφ_compact hφE hflat
  simpa [SCV.realEmbed] using hzero

end BHW
