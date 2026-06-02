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
        Schwinger-side limit.  What remains is the true BHW/Jost transport:
        identify the deterministic Figure-2-4 `extendF` side branches with
        those raw Wick-section currents in the same moving source tests.
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
      have hplus_transfer :
          Tendsto
            (fun ε : ℝ => ExtPlus ε - RawPlus ε)
            (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
        have hKη : IsCompact ({η} : Set (BHW.OS45FlatCommonChartReal d n)) :=
          isCompact_singleton
        have hKηC :
            ({η} : Set (BHW.OS45FlatCommonChartReal d n)) ⊆
              BHW.os45FlatCommonChartCone d n := by
          intro ξ hξ
          rw [Set.mem_singleton_iff.mp hξ]
          exact hηC
        have hraw_plus_uniform :=
          (D.sideZeroDiagonal_sourcePairings_tendstoUniformlyOn_schwinger
            OS lgc ({η} : Set (BHW.OS45FlatCommonChartReal d n))
            hKη hKηC φ hφ_compact hφE).1
        have hraw_plus :
            Tendsto RawPlus (𝓝[Set.Ioi 0] (0 : ℝ))
              (𝓝 (OS.S n (D.toZeroDiagonalCLM
                (1 : Equiv.Perm (Fin n)) φ))) := by
          have hη_mem : η ∈ ({η} : Set (BHW.OS45FlatCommonChartReal d n)) := by
            simp
          simpa [RawPlus] using hraw_plus_uniform.tendsto_at hη_mem
        have hF_cont :
            ContinuousOn
              (fun z : Fin n → Fin (d + 1) → ℂ =>
                BHW.extendF (bvt_F OS lgc n)
                  (BHW.permAct (d := d)
                    (1 : Equiv.Perm (Fin n)).symm z))
              (BHW.ExtendedTube d n) := by
          simpa using
            (BHW.differentiableOn_extendF_bvt_F_extendedTube
              (d := d) OS lgc n).continuousOn
        have h0_plus :
            ∀ u ∈ closure U,
              BHW.os45FlatCommonChartSourceSide d n
                (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u ∈
                  BHW.ExtendedTube d n := by
          intro u hu
          have huV : u ∈ closure P.V :=
            subset_closure (hU_closure hu)
          have hmem :=
            (BHW.os45Figure24_commonEdge_mem_initialSectorOverlap
              (d := d) (n := n) (hd := hd) (P := P) huV).1
          rw [BHW.os45FlatCommonChartSourceSide_zero_eq_commonEdge]
          exact hmem
        have h0_minus :
            ∀ u ∈ closure U,
              BHW.os45FlatCommonChartSourceSide d n
                (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η u ∈
                  BHW.ExtendedTube d n := by
          intro u hu
          have huV : u ∈ closure P.V :=
            subset_closure (hU_closure hu)
          have hmem :=
            (BHW.os45Figure24_commonEdge_mem_initialSectorOverlap
              (d := d) (n := n) (hd := hd) (P := P) huV).1
          rw [BHW.os45FlatCommonChartSourceSide_zero_eq_commonEdge]
          exact hmem
        have hsource_pair :=
          D.tendsto_sourceSide_extendF_sideZeroDiagonalCLM_pair
            (d := d) OS lgc (1 : Equiv.Perm (Fin n))
            BHW.isOpen_extendedTube hF_cont hU_open subset_closure
            hU_compact η h0_plus h0_minus φ hφ_compact hφU
        have hsource_zero_eq_schwinger :
            (∫ u : NPointDomain d n,
              BHW.extendF (bvt_F OS lgc n)
                (BHW.os45QuarterTurnConfig (d := d) (n := n)
                  (fun k => wickRotatePoint (u k))) *
                ((((D.toZeroDiagonalCLM
                  (1 : Equiv.Perm (Fin n)) φ).1 :
                    SchwartzNPoint d n) : NPointDomain d n → ℂ) u)) =
              OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ) := by
          let J : ℂ := BHW.os45CommonEdgeFlatJacobianAbs n
          have hJ_ne : J ≠ 0 := by
            exact Complex.ofReal_ne_zero.mpr
              (ne_of_gt (BHW.os45CommonEdgeFlatJacobianAbs_pos n))
          have hφE0 :
              tsupport
                  (SCV.translateSchwartz
                    (((1 : ℝ) * 0) • η) φ :
                    BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
                BHW.os45FlatCommonChartEdgeSet d n P
                  (1 : Equiv.Perm (Fin n)) := by
            simpa using hφE
          have hΩ_zero :
              tsupport
                  (SCV.translateSchwartz
                    (((1 : ℝ) * 0) • η) φ :
                    BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
                {x |
                  (fun j =>
                    ((x + ((1 : ℝ) * 0) • η) j : ℂ) +
                      ((((1 : ℝ) * 0) • η) j : ℂ) * Complex.I) ∈
                    BHW.os45FlatCommonChartOmega d n
                      (1 : Equiv.Perm (Fin n))} := by
            intro x hx
            have hxE := hφE0 hx
            rcases hxE with ⟨y, hy, rfl⟩
            rcases hy with ⟨u, hu, rfl⟩
            simpa [BHW.os45FlatCommonChartOmega,
              BHW.unflattenCfg_ofReal_flattenCfgReal] using
              P.V_pulled_id u hu
          have hflat_int :
              Integrable
                (fun x : BHW.OS45FlatCommonChartReal d n =>
                  BHW.os45FlatCommonChartBranch d n OS lgc
                    (1 : Equiv.Perm (Fin n))
                    (fun j =>
                      ((x + ((1 : ℝ) * 0) • η) j : ℂ) +
                        ((((1 : ℝ) * 0) • η) j : ℂ) * Complex.I) *
                  φ (x + ((1 : ℝ) * 0) • η)) := by
            exact
              BHW.os45FlatCommonChart_branch_shifted_mul_integrable
                (d := d) (n := n) OS lgc
                (1 : Equiv.Perm (Fin n))
                (((1 : ℝ) * 0) • η) (((1 : ℝ) * 0) • η)
                φ hφ_compact hΩ_zero
          have hflat_source :=
            BHW.os45FlatCommonChart_branch_integral_eq_sourceSide_extendF_sideZeroDiagonalCLM
              (d := d) (n := n) OS lgc D
              (1 : Equiv.Perm (Fin n)) (1 : Equiv.Perm (Fin n))
              (1 : ℝ) 0 η φ hφE0 hflat_int
          have hflat_real_edge_eq_schwinger :
              (∫ x : BHW.OS45FlatCommonChartReal d n,
                BHW.os45FlatCommonChartBranch d n OS lgc
                  (1 : Equiv.Perm (Fin n))
                  (fun a => (x a : ℂ)) * φ x) =
                J * OS.S n
                  (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ) := by
            /-
              The remaining ordinary-side Vladimirov/BHW payload: the flat
              Figure-2-4 real-edge branch represents the Schwinger boundary CLM.
            -/
            exact ?os45_vladimirov_ordinary_flat_real_edge_pairing_eq_schwinger
          have hsource_to_flat :
              J *
                (∫ u : NPointDomain d n,
                  BHW.extendF (bvt_F OS lgc n)
                    (BHW.os45QuarterTurnConfig (d := d) (n := n)
                      (fun k => wickRotatePoint (u k))) *
                    ((((D.toZeroDiagonalCLM
                      (1 : Equiv.Perm (Fin n)) φ).1 :
                        SchwartzNPoint d n) : NPointDomain d n → ℂ) u)) =
              (∫ x : BHW.OS45FlatCommonChartReal d n,
                BHW.os45FlatCommonChartBranch d n OS lgc
                  (1 : Equiv.Perm (Fin n))
                  (fun a => (x a : ℂ)) * φ x) := by
            have htest :
                (∫ u : NPointDomain d n,
                  BHW.extendF (bvt_F OS lgc n)
                    (BHW.os45QuarterTurnConfig (d := d) (n := n)
                      (fun k => wickRotatePoint (u k))) *
                    ((((D.toZeroDiagonalCLM
                      (1 : Equiv.Perm (Fin n)) φ).1 :
                        SchwartzNPoint d n) : NPointDomain d n → ℂ) u)) =
                ∫ u : NPointDomain d n,
                  BHW.extendF (bvt_F OS lgc n)
                    (BHW.os45QuarterTurnConfig (d := d) (n := n)
                      (fun k => wickRotatePoint (u k))) *
                    (D.χ u *
                        φ (BHW.os45CommonEdgeFlatCLE d n
                          (1 : Equiv.Perm (Fin n)) u)) := by
              apply integral_congr_ae
              filter_upwards with u
              have hval :
                  ((((D.toZeroDiagonalCLM
                    (1 : Equiv.Perm (Fin n)) φ).1 :
                      SchwartzNPoint d n) : NPointDomain d n → ℂ) u) =
                    D.χ u *
                      φ (BHW.os45CommonEdgeFlatCLE d n
                        (1 : Equiv.Perm (Fin n)) u) := by
                change
                  (D.toSchwartzNPointCLM
                    (1 : Equiv.Perm (Fin n)) φ :
                    NPointDomain d n → ℂ) u =
                    D.χ u *
                      φ (BHW.os45CommonEdgeFlatCLE d n
                        (1 : Equiv.Perm (Fin n)) u)
                simp
              rw [hval]
            calc
              J *
                  (∫ u : NPointDomain d n,
                    BHW.extendF (bvt_F OS lgc n)
                      (BHW.os45QuarterTurnConfig (d := d) (n := n)
                        (fun k => wickRotatePoint (u k))) *
                      ((((D.toZeroDiagonalCLM
                        (1 : Equiv.Perm (Fin n)) φ).1 :
                          SchwartzNPoint d n) : NPointDomain d n → ℂ) u)) =
                J *
                  (∫ u : NPointDomain d n,
                    BHW.extendF (bvt_F OS lgc n)
                      (BHW.os45QuarterTurnConfig (d := d) (n := n)
                        (fun k => wickRotatePoint (u k))) *
                      (D.χ u *
                        φ (BHW.os45CommonEdgeFlatCLE d n
                          (1 : Equiv.Perm (Fin n)) u))) := by
                  rw [htest]
              _ =
                ∫ x : BHW.OS45FlatCommonChartReal d n,
                  BHW.os45FlatCommonChartBranch d n OS lgc
                    (1 : Equiv.Perm (Fin n))
                    (fun a => (x a : ℂ)) * φ x := by
                  simpa [J, BHW.os45FlatCommonChartSourceSide_zero_eq_commonEdge,
                    BHW.os45QuarterTurnCLE_symm_realEmbed_commonEdge_eq_wick]
                    using hflat_source.symm
          have hscaled :
              J *
                (∫ u : NPointDomain d n,
                  BHW.extendF (bvt_F OS lgc n)
                    (BHW.os45QuarterTurnConfig (d := d) (n := n)
                      (fun k => wickRotatePoint (u k))) *
                    ((((D.toZeroDiagonalCLM
                      (1 : Equiv.Perm (Fin n)) φ).1 :
                        SchwartzNPoint d n) : NPointDomain d n → ℂ) u)) =
                J *
                  OS.S n
                    (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ) := by
            calc
              J *
                  (∫ u : NPointDomain d n,
                    BHW.extendF (bvt_F OS lgc n)
                      (BHW.os45QuarterTurnConfig (d := d) (n := n)
                        (fun k => wickRotatePoint (u k))) *
                      ((((D.toZeroDiagonalCLM
                        (1 : Equiv.Perm (Fin n)) φ).1 :
                          SchwartzNPoint d n) : NPointDomain d n → ℂ) u)) =
                ∫ x : BHW.OS45FlatCommonChartReal d n,
                  BHW.os45FlatCommonChartBranch d n OS lgc
                    (1 : Equiv.Perm (Fin n))
                    (fun a => (x a : ℂ)) * φ x := hsource_to_flat
              _ = J *
                  OS.S n
                    (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ) :=
                hflat_real_edge_eq_schwinger
          exact mul_left_cancel₀ hJ_ne hscaled
        have hsource_plus :
            Tendsto ExtPlus (𝓝[Set.Ioi 0] (0 : ℝ))
              (𝓝 (OS.S n (D.toZeroDiagonalCLM
                (1 : Equiv.Perm (Fin n)) φ))) := by
          simpa [ExtPlus, hsource_zero_eq_schwinger] using hsource_pair.1
        simpa using hsource_plus.sub hraw_plus
      have hminus_transfer :
          Tendsto
            (fun ε : ℝ => ExtMinus ε - RawMinus ε)
            (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
        /-
          OS-I `(4.12)`/Vladimirov transfer for the adjacent side: the selected
          deterministic negative Figure-2-4 branch has the same moving-test
          boundary current as the raw permuted Wick section.
        -/
        exact ?os45_vladimirov_adjacent_sourceSide_extendF_to_raw_wick_current
      have hresidual :
          Tendsto
            (fun ε : ℝ =>
              (ExtPlus ε - RawPlus ε) - (ExtMinus ε - RawMinus ε))
            (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
        simpa using hplus_transfer.sub hminus_transfer
      have hsrc :
          Tendsto
            (fun ε : ℝ =>
              (RawPlus ε - RawMinus ε) +
                ((ExtPlus ε - RawPlus ε) - (ExtMinus ε - RawMinus ε)))
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
