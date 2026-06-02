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

        Prove that the ordinary `+` and selected adjacent `-` flat side-branch
        currents have the same Schwinger boundary distribution on the Figure-2-4
        collar. This is the OS-I `(4.12)`--`(4.14)` source-side Schwinger
        normalization plus local Vladimirov tempered-BV uniqueness on the common
        Jost edge. It is not a `sourceRepresentsOn`, Hdiff, local-S-prime, or
        downstream EOW-envelope input.
      -/
      let T :=
        BHW.os45_BHWJost_flatCommonChart_schwingerCLM
          (d := d) hd OS lgc P (1 : Equiv.Perm (Fin n))
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
        /-
          Vladimirov/BHW upper-side producer: construct the tempered boundary
          value package for the ordinary flat chart and identify its distribution
          with the OS Schwinger CLM pulled through the Figure-2-4 cutoff.
        -/
        exact ?os45_vladimirov_ordinary_upper_flat_bv_eq_schwinger
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
        /-
          Vladimirov/BHW lower-side producer: construct the adjacent lower-tube
          tempered boundary value and prove that the OS-I `(4.12)`--`(4.14)`
          Wick-section transport gives the same Schwinger CLM as the ordinary
          side. This is the current irreducible interface.
        -/
        exact ?os45_vladimirov_adjacent_lower_flat_bv_eq_schwinger
      have hdiff := hplus_bv.sub hminus_bv
      simpa [sub_self] using hdiff
  have hzero :=
    D.zeroHeightPairing_of_tendsto_flatCommonChart_sideBranch_difference_zero
      (d := d) OS lgc η hηC φ hφ_compact hφE hflat
  simpa [SCV.realEmbed] using hzero

end BHW
