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
        Flat-chart Vladimirov/BHW side-current leaf.

        The ordinary `+` side already has a checked zero-height boundary
        distribution, namely the local common-edge `ordinaryEdgeCLM`. Side
        continuity reduces the remaining OS-I `(4.12)`--`(4.14)` content to the
        selected adjacent zero-height pairing against that same CLM.
      -/
      let T := BHW.os45FlatCommonChart_ordinaryEdgeCLM hd OS lgc P
      let Kη : Set (BHW.OS45FlatCommonChartReal d n) := {η}
      have hKη : IsCompact Kη := isCompact_singleton
      have hKηC : Kη ⊆ BHW.os45FlatCommonChartCone d n := by
        intro η' hη'
        have hη'_eq : η' = η := by
          simpa [Kη] using hη'
        simpa [hη'_eq] using hηC
      have hplus_bv :
          Tendsto
            (fun ε : ℝ =>
              ∫ x : BHW.OS45FlatCommonChartReal d n,
                BHW.os45FlatCommonChartBranch d n OS lgc
                  (1 : Equiv.Perm (Fin n))
                  (fun a =>
                    (x a : ℂ) +
                      ((((1 : ℝ) * ε) • η) a : ℂ) * Complex.I) *
                  φ x)
            (𝓝[Set.Ioi 0] (0 : ℝ))
            (𝓝 (T φ)) := by
        have hplus_zero :
            (∫ x : BHW.OS45FlatCommonChartReal d n,
              BHW.os45FlatCommonChartBranch d n OS lgc
                (1 : Equiv.Perm (Fin n))
                (fun a => (x a : ℂ)) * φ x) =
              T φ := by
          simpa [T] using
            BHW.os45FlatCommonChart_plus_zeroHeight_pairing_eq_CLM_of_localRepresents
              (d := d) hd OS lgc (P := P)
              (BHW.os45FlatCommonChart_ordinaryEdgeCLM hd OS lgc P)
              (BHW.os45FlatCommonChart_ordinaryEdgeCLM_represents hd OS lgc)
              φ hφ_compact hφE
        have hplus_unif :=
          BHW.os45_BHWJost_flatCommonChart_distributionalBoundaryValue_plus_of_zeroHeight_pairingCLM
            (d := d) hd OS lgc (P := P) T Kη hKη hKηC
            φ hφ_compact hφE hplus_zero
        simpa [Kη, T, one_mul, Pi.smul_apply, smul_eq_mul, mul_assoc] using
          hplus_unif.tendsto_at (by simp [Kη])
      have hminus_bv :
          Tendsto
            (fun ε : ℝ =>
              ∫ x : BHW.OS45FlatCommonChartReal d n,
                BHW.os45FlatCommonChartBranch d n OS lgc
                  (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                  (fun a =>
                    (x a : ℂ) +
                      ((((-1 : ℝ) * ε) • η) a : ℂ) * Complex.I) *
                  φ x)
            (𝓝[Set.Ioi 0] (0 : ℝ))
            (𝓝 (T φ)) := by
        have hminus_zero :
            (∫ x : BHW.OS45FlatCommonChartReal d n,
              BHW.os45FlatCommonChartBranch d n OS lgc
                (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                (fun a => (x a : ℂ)) * φ x) =
              T φ := by
          /-
            Vladimirov/BHW lower-edge producer: identify the selected adjacent
            zero-height boundary distribution with the ordinary common-edge CLM
            by OS-I `(4.12)`--`(4.14)` Wick-section transport and tempered-BV
            uniqueness on the local Jost collar.
          -/
          exact ?os45_vladimirov_adjacent_zeroHeight_pairing_eq_ordinaryEdgeCLM
        have hminus_unif :=
          BHW.os45_BHWJost_flatCommonChart_distributionalBoundaryValue_minus_of_zeroHeight_pairingCLM
            (d := d) hd OS lgc (P := P) T Kη hKη hKηC
            φ hφ_compact hφE hminus_zero
        simpa [Kη, T, sub_eq_add_neg, neg_mul, one_mul, Pi.smul_apply,
            smul_eq_mul, mul_assoc] using
          hminus_unif.tendsto_at (by simp [Kη])
      have hdiff := hplus_bv.sub hminus_bv
      simpa [sub_self] using hdiff
  have hzero :=
    D.zeroHeightPairing_of_tendsto_flatCommonChart_sideBranch_difference_zero
      (d := d) OS lgc η hηC φ hφ_compact hφE hflat
  simpa [SCV.realEmbed] using hzero

end BHW
