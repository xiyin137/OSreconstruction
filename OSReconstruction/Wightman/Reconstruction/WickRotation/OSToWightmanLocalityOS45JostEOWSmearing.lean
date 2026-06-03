import OSReconstruction.SCV.VladimirovTillmann
import OSReconstruction.SCV.LocalBoundaryRecovery
import OSReconstruction.SCV.IdentityTheorem
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45Figure24Seed
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45SourceSideMoving
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanRuelleOverlap

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

private theorem os45_flat_plus_selector_to_sourceSide
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (η : BHW.OS45FlatCommonChartReal d n)
    (hηC : η ∈ BHW.os45FlatCommonChartCone d n)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact :
      HasCompactSupport
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)))
    (hflat :
      Tendsto
        (fun ε : ℝ =>
          ∫ x : BHW.OS45FlatCommonChartReal d n,
            BHW.os45FlatCommonChartBranch d n OS lgc
              (1 : Equiv.Perm (Fin n))
              (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) *
              φ x)
        (𝓝[Set.Ioi 0] (0 : ℝ))
        (𝓝
          ((BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) *
            OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ)))) :
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
      (𝓝 (OS.S n (D.toZeroDiagonalCLM
        (1 : Equiv.Perm (Fin n)) φ))) := by
  classical
  let Kη : Set (BHW.OS45FlatCommonChartReal d n) := {η}
  have hKη : IsCompact Kη := isCompact_singleton
  have hKηC : Kη ⊆ BHW.os45FlatCommonChartCone d n := by
    intro η' hη'
    have hηeq : η' = η := by
      simpa [Kη] using hη'
    simpa [hηeq] using hηC
  have hside_support :=
    BHW.os45FlatCommonChart_sideSupport_radius
      (d := d) (n := n) (P := P)
      Kη hKη hKηC φ hφ_compact hφE
  rcases hside_support with ⟨r_support, hr_support, hside_support⟩
  have hside_event :
      ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ), ∀ η ∈ Kη,
        tsupport (SCV.translateSchwartz (ε • η) φ :
          BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
            BHW.os45FlatCommonChartEdgeSet d n P
              (1 : Equiv.Perm (Fin n)) ∧
        tsupport (SCV.translateSchwartz ((-ε : ℝ) • η) φ :
          BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
            BHW.os45FlatCommonChartEdgeSet d n P
              (1 : Equiv.Perm (Fin n)) := by
    filter_upwards
      [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hr_support)]
      with ε hε_pos hε_lt η hη
    exact hside_support ε hε_pos hε_lt η hη
  have hinteg :=
    BHW.os45FlatCommonChart_branch_side_shifted_mul_integrable_eventually
      (d := d) OS lgc (P := P)
      Kη hKη hKηC φ hφ_compact hφE
  let J : ℂ := BHW.os45CommonEdgeFlatJacobianAbs n
  have hJ_ne : J ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (ne_of_gt (BHW.os45CommonEdgeFlatJacobianAbs_pos n))
  have hpull :
      (fun ε : ℝ =>
        ∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (fun a => (x a : ℂ) + (ε : ℂ) * (η a : ℂ) * Complex.I) *
            φ x)
      =ᶠ[𝓝[Set.Ioi 0] (0 : ℝ)]
      (fun ε : ℝ =>
        J *
          ∫ u : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
              (BHW.os45FlatCommonChartSourceSide d n
                (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η u) *
              ((((D.toSideZeroDiagonalCLM
                (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
                  SchwartzNPoint d n) : NPointDomain d n → ℂ) u)) := by
    filter_upwards [hside_event, hinteg] with ε hsupport hinteg
    have hφE_plus :
        tsupport (SCV.translateSchwartz (((1 : ℝ) * ε) • η) φ :
          BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
          BHW.os45FlatCommonChartEdgeSet d n P
            (1 : Equiv.Perm (Fin n)) := by
      simpa [Kη] using (hsupport η (by simp [Kη])).1
    have hg_plus :
        Integrable
          (fun x : BHW.OS45FlatCommonChartReal d n =>
            BHW.os45FlatCommonChartBranch d n OS lgc
              (1 : Equiv.Perm (Fin n))
              (fun j =>
                ((x + ((1 : ℝ) * ε) • η) j : ℂ) +
                  ((((1 : ℝ) * ε) • η) j : ℂ) * Complex.I) *
            φ (x + ((1 : ℝ) * ε) • η)) := by
      simpa [Kη] using (hinteg η (by simp [Kη])).1
    simpa [J, one_mul] using
      BHW.os45FlatCommonChart_branch_integral_eq_sourceSide_extendF_sideZeroDiagonalCLM
        (d := d) (n := n) OS lgc D
        (1 : Equiv.Perm (Fin n)) (1 : Equiv.Perm (Fin n))
        (1 : ℝ) ε η φ hφE_plus hg_plus
  have hscaled :
      Tendsto
        (fun ε : ℝ =>
          J *
            ∫ u : NPointDomain d n,
              BHW.extendF (bvt_F OS lgc n)
                (BHW.os45FlatCommonChartSourceSide d n
                  (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η u) *
                ((((D.toSideZeroDiagonalCLM
                  (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
                    SchwartzNPoint d n) : NPointDomain d n → ℂ) u))
        (𝓝[Set.Ioi 0] (0 : ℝ))
        (𝓝 (J * OS.S n
          (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ))) := by
    simpa [J] using hflat.congr' hpull
  have hdescaled :
      Tendsto
        (fun ε : ℝ =>
          J⁻¹ *
            (J *
              ∫ u : NPointDomain d n,
                BHW.extendF (bvt_F OS lgc n)
                  (BHW.os45FlatCommonChartSourceSide d n
                    (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η u) *
                  ((((D.toSideZeroDiagonalCLM
                    (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
                      SchwartzNPoint d n) : NPointDomain d n → ℂ) u)))
        (𝓝[Set.Ioi 0] (0 : ℝ))
        (𝓝 (J⁻¹ * (J * OS.S n
          (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ)))) := by
    exact tendsto_const_nhds.mul hscaled
  simpa [J, hJ_ne, mul_assoc] using hdescaled

private theorem os45_flat_minus_selector_to_sourceSide
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (η : BHW.OS45FlatCommonChartReal d n)
    (hηC : η ∈ BHW.os45FlatCommonChartCone d n)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact :
      HasCompactSupport
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)))
    (hflat :
      Tendsto
        (fun ε : ℝ =>
          ∫ x : BHW.OS45FlatCommonChartReal d n,
            BHW.os45FlatCommonChartBranch d n OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin n)))
              (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) *
              φ x)
        (𝓝[Set.Ioi 0] (0 : ℝ))
        (𝓝
          ((BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) *
            OS.S n (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ)))) :
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
      (𝓝 (OS.S n (D.toZeroDiagonalCLM
        (1 : Equiv.Perm (Fin n)) φ))) := by
  classical
  let Kη : Set (BHW.OS45FlatCommonChartReal d n) := {η}
  have hKη : IsCompact Kη := isCompact_singleton
  have hKηC : Kη ⊆ BHW.os45FlatCommonChartCone d n := by
    intro η' hη'
    have hηeq : η' = η := by
      simpa [Kη] using hη'
    simpa [hηeq] using hηC
  have hside_support :=
    BHW.os45FlatCommonChart_sideSupport_radius
      (d := d) (n := n) (P := P)
      Kη hKη hKηC φ hφ_compact hφE
  rcases hside_support with ⟨r_support, hr_support, hside_support⟩
  have hside_event :
      ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ), ∀ η ∈ Kη,
        tsupport (SCV.translateSchwartz (ε • η) φ :
          BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
            BHW.os45FlatCommonChartEdgeSet d n P
              (1 : Equiv.Perm (Fin n)) ∧
        tsupport (SCV.translateSchwartz ((-ε : ℝ) • η) φ :
          BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
            BHW.os45FlatCommonChartEdgeSet d n P
              (1 : Equiv.Perm (Fin n)) := by
    filter_upwards
      [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hr_support)]
      with ε hε_pos hε_lt η hη
    exact hside_support ε hε_pos hε_lt η hη
  have hinteg :=
    BHW.os45FlatCommonChart_branch_side_shifted_mul_integrable_eventually
      (d := d) OS lgc (P := P)
      Kη hKη hKηC φ hφ_compact hφE
  let J : ℂ := BHW.os45CommonEdgeFlatJacobianAbs n
  have hJ_ne : J ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (ne_of_gt (BHW.os45CommonEdgeFlatJacobianAbs_pos n))
  have hpull :
      (fun ε : ℝ =>
        ∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (fun a => (x a : ℂ) - (ε : ℂ) * (η a : ℂ) * Complex.I) *
            φ x)
      =ᶠ[𝓝[Set.Ioi 0] (0 : ℝ)]
      (fun ε : ℝ =>
        J *
          ∫ u : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d)
                (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
                (BHW.os45FlatCommonChartSourceSide d n
                  (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η u)) *
              ((((D.toSideZeroDiagonalCLM
                (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
                  SchwartzNPoint d n) : NPointDomain d n → ℂ) u)) := by
    filter_upwards [hside_event, hinteg] with ε hsupport hinteg
    have hφE_minus :
        tsupport (SCV.translateSchwartz (((-1 : ℝ) * ε) • η) φ :
          BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
          BHW.os45FlatCommonChartEdgeSet d n P
            (1 : Equiv.Perm (Fin n)) := by
      simpa [Kη, neg_smul] using (hsupport η (by simp [Kη])).2
    have hg_minus :
        Integrable
          (fun x : BHW.OS45FlatCommonChartReal d n =>
            BHW.os45FlatCommonChartBranch d n OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin n)))
              (fun j =>
                ((x + (((-1 : ℝ) * ε) • η)) j : ℂ) +
                  ((((-1 : ℝ) * ε) • η) j : ℂ) * Complex.I) *
            φ (x + (((-1 : ℝ) * ε) • η))) := by
      simpa [Kη, neg_smul] using (hinteg η (by simp [Kη])).2
    simpa [J, neg_mul, one_mul] using
      BHW.os45FlatCommonChart_branch_integral_eq_sourceSide_extendF_sideZeroDiagonalCLM
        (d := d) (n := n) OS lgc D
        (P.τ.symm * (1 : Equiv.Perm (Fin n)))
        (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ
        hφE_minus hg_minus
  have hscaled :
      Tendsto
        (fun ε : ℝ =>
          J *
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
        (𝓝 (J * OS.S n
          (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ))) := by
    simpa [J] using hflat.congr' hpull
  have hdescaled :
      Tendsto
        (fun ε : ℝ =>
          J⁻¹ *
            (J *
              ∫ u : NPointDomain d n,
                BHW.extendF (bvt_F OS lgc n)
                  (BHW.permAct (d := d)
                    (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
                    (BHW.os45FlatCommonChartSourceSide d n
                      (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η u)) *
                  ((((D.toSideZeroDiagonalCLM
                    (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
                      SchwartzNPoint d n) : NPointDomain d n → ℂ) u)))
        (𝓝[Set.Ioi 0] (0 : ℝ))
        (𝓝 (J⁻¹ * (J * OS.S n
          (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ)))) := by
    exact tendsto_const_nhds.mul hscaled
  simpa [J, hJ_ne, mul_assoc] using hdescaled

/-- OS-I Section 4.5 Jost/EOW smearing should produce the local `(4.14)`
flat common-edge compact-test equality.

This is the paper-facing consumer upstream of
`OS45BHWJostHullData.os45CommonEdge_sourceRepresentsZero_of_local414_integrals`
and `OS45BHWJostHullData.os45CommonEdge_sourceRepresentsZero_of_sourcePairings`.
The proof body should follow the monograph part-(b) route: construct Jost
neighbourhoods on the local real edge, use Euclidean source permutation
symmetry plus the identity theorem to identify the two holomorphic branches,
apply distributional EOW on the common real edge, then smear by a finite
partition of unity over the compact support of `φ`.

The checked proof now consumes the compact Figure-2-4 real Jost pairing packet
explicitly, transports it through the Ruelle/common-edge bridge to the
deterministic adjacent Wick pairing, and then uses the existing
source-representation and flat-chart EOW consumers.  Producing the compact
packet without theorem-2 locality remains the upstream OS-I `(4.12)`--`(4.14)`
branch/source step. -/
theorem OS45BHWJostHullData.os45CommonEdge_local414_integrals_of_OSI45_jostEOW_smearing
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    (_H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (hCompactFigure24 :
      BHW.OS45CompactFigure24WickPairingEq (d := d) n i hi OS lgc)
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
  have hn_pos : 0 < n := by omega
  haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn_pos⟩
  have hU_sub : U ⊆ P.V := fun u hu => hU_closure (subset_closure hu)
  have hAdjacentForwardOverlap_connected :
      IsConnected (BHW.adjSwapForwardOverlapSet (d := d) n i hi) :=
    by
      have hswap_ne :
          (Equiv.swap i ⟨i.val + 1, hi⟩ : Equiv.Perm (Fin n)) ≠ 1 := by
        intro hswap_eq
        have hfix :
            (Equiv.swap i ⟨i.val + 1, hi⟩ : Equiv.Perm (Fin n)) i = i := by
          simp [hswap_eq]
        have hswap :
            (Equiv.swap i ⟨i.val + 1, hi⟩ : Equiv.Perm (Fin n)) i =
              ⟨i.val + 1, hi⟩ := by
          exact Equiv.swap_apply_left i ⟨i.val + 1, hi⟩
        have hval : i.val + 1 = i.val :=
          congrArg Fin.val (hswap.symm.trans hfix)
        exact Nat.succ_ne_self i.val hval
      have hn_not_le_one : ¬ n ≤ 1 := by omega
      simpa [BHW.adjSwapForwardOverlapSet, BHW.permForwardOverlapSet, BHW.permAct] using
        BHW.permForwardOverlap_connected_nontrivial
          (d := d) n (Equiv.swap i ⟨i.val + 1, hi⟩)
          hswap_ne hn_not_le_one
  have hAdjacentOverlap_connected :
      IsConnected
        {z : Fin n → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d n ∧
            BHW.permAct (d := d) P.τ z ∈ BHW.ExtendedTube d n} :=
    by
      have hraw :=
        BHW.isConnected_adjSwapExtendedOverlap_of_forwardOverlapConnected
          (d := d) n i hi hAdjacentForwardOverlap_connected
      simpa [BHW.adjSwapExtendedOverlapSet, BHW.permAct, P.τ_eq] using hraw
  have hTransported_wick_pairing :
      ∀ ψ : SchwartzNPoint d n,
        HasCompactSupport (ψ : NPointDomain d n → ℂ) →
        tsupport (ψ : NPointDomain d n → ℂ) ⊆ U →
        ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ
              (fun k => wickRotatePoint (u k))) * ψ u =
        ∫ u : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (u k)) * ψ u :=
    BHW.os45CommonEdge_transported_wick_pairing_of_compactFigure24WickPairingEq
      (d := d) hd OS lgc (P := P) hAdjacentOverlap_connected
      hCompactFigure24 hU_sub
  have hSourceRepresentsZero :
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
                    (1 : Equiv.Perm (Fin n)) u))) U :=
    BHW.os45CommonEdge_sourceRepresentsZero_of_initialOverlap_adjacentBranch
      (d := d) hd OS lgc (P := P) hU_open hU_compact
      hU_connected hU_closure hTransported_wick_pairing
  intro φ hφ_compact hφU
  let Tedge : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ] ℂ :=
    BHW.os45FlatCommonChart_ordinaryEdgeCLM hd OS lgc P
  have hPairings :=
    BHW.os45FlatCommonChart_zeroHeight_pairings_eq_ordinaryEdgeCLM_of_sourceRepresentsOn
      (d := d) hd OS lgc (P := P) hU_sub hSourceRepresentsZero
  have hplus :
      (∫ x : BHW.OS45FlatCommonChartReal d n,
        BHW.os45FlatCommonChartBranch d n OS lgc
          (1 : Equiv.Perm (Fin n))
          (SCV.realEmbed x) * φ x) =
        Tedge φ := by
    have hplus_raw := (hPairings.1 φ hφ_compact hφU)
    simpa [Tedge, SCV.realEmbed] using hplus_raw
  have hminus :
      (∫ x : BHW.OS45FlatCommonChartReal d n,
        BHW.os45FlatCommonChartBranch d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (SCV.realEmbed x) * φ x) =
        Tedge φ := by
    have hminus_raw := (hPairings.2 φ hφ_compact hφU)
    simpa [Tedge, SCV.realEmbed] using hminus_raw
  exact hminus.trans hplus.symm

end BHW
