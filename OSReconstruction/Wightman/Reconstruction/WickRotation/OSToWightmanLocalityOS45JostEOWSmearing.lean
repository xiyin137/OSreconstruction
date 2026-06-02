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
  intro φ _hφ_compact hφU
  have hU_sub : U ⊆ P.V := fun u hu => hU_closure (subset_closure hu)
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
                (1 : Equiv.Perm (Fin n)) u)) := by
    rcases
        BHW.os45CommonEdge_initialSectorOverlap_traces_except_adjacentWick
          (d := d) hd OS lgc (P := P)
          (U := U) hU_compact hU_connected hU_closure with
      ⟨Ucx, Ford, Fadj, hUcx_open, hUcx_connected, hwick_mem,
        hcommon_mem, _hUcx_sub, hFord_holo, hFadj_holo, hFord_wick,
        hFadj_wick_extendF, hFord_common, hFadj_common,
        _hFadj_seed_trace⟩
    refine
      BHW.os45CommonEdge_pulledRealBranches_eqOn_of_wickPairings
        (d := d) hd OS lgc (P := P) hU_open hU_connected.nonempty
        hUcx_open hUcx_connected hwick_mem hcommon_mem Ford Fadj
        hFord_holo hFadj_holo ?_ hFord_common hFadj_common
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
          bvt_F OS lgc n
            (fun k => wickRotatePoint (u (P.τ k))) * ψ u := by
          /-
            Vladimirov/BHW deterministic-to-raw adjacent Wick BV leaf.

            The OS Euclidean source-pairing calculation below identifies the
            raw adjacent Wick boundary value with the ordinary Wick boundary
            value for arbitrary compact source tests supported in `U`.  The
            remaining analytic payload is the real Jost-edge common-boundary
            pairing for the two BHW `extendF` branches on this same source
            window.  The checked local-edge identity theorem then transports
            that Jost-edge equality through the adjacent ET overlap to the
            adjacent Wick point.
          -/
          have hrealEdge :
              ∀ χ : SchwartzNPoint d n,
                HasCompactSupport (χ : NPointDomain d n → ℂ) →
                tsupport (χ : NPointDomain d n → ℂ) ⊆ U →
                  (∫ x : NPointDomain d n,
                    BHW.extendF (bvt_F OS lgc n)
                      (BHW.realEmbed
                        (fun k => x
                          ((Equiv.swap i ⟨i.val + 1, hi⟩) k))) *
                      χ x)
                  =
                  ∫ x : NPointDomain d n,
                    BHW.extendF (bvt_F OS lgc n)
                      (BHW.realEmbed x) * χ x := by
            intro χ hχ_compact hχU
            have hid_int :
                Integrable
                  (fun u : NPointDomain d n =>
                    BHW.extendF (bvt_F OS lgc n)
                      (BHW.realEmbed u) * χ u) := by
              simpa using
                BHW.integrable_extendF_realSource_mul_schwartz_of_ET
                  (d := d) OS lgc n U hU_open
                  (1 : Equiv.Perm (Fin n))
                  (by
                    intro x hx
                    simpa using
                      H.realPatch_mem_extendedTube x (hU_sub hx))
                  χ hχ_compact hχU
            have hτ_int :
                Integrable
                  (fun u : NPointDomain d n =>
                    BHW.extendF (bvt_F OS lgc n)
                      (BHW.realEmbed
                        (fun k => u
                          ((Equiv.swap i ⟨i.val + 1, hi⟩) k))) *
                    χ u) := by
              refine
                BHW.integrable_extendF_realSource_mul_schwartz_of_ET
                  (d := d) OS lgc n U hU_open
                  (Equiv.swap i ⟨i.val + 1, hi⟩) ?_
                  χ hχ_compact hχU
              intro x hx
              have hx_sector :=
                H.realPatch_mem_permutedExtendedTubeSector x (hU_sub hx)
              simpa [P.τ_eq, BHW.permutedExtendedTubeSector,
                BHW.permAct_realEmbed, BHW.permAct] using hx_sector
            let τ : Equiv.Perm (Fin n) :=
              Equiv.swap i ⟨i.val + 1, hi⟩
            let e := flattenCLEquiv n (d + 1)
            have hn_pos : 0 < n := by omega
            haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn_pos⟩
            let Cflat : Set (Fin (n * (d + 1)) → ℝ) :=
              BHW.os45FlatCommonChartCone d n
            let Fflat : (Fin (n * (d + 1)) → ℂ) → ℂ :=
              fun z =>
                BHW.extendF (bvt_F OS lgc n)
                  (BHW.permAct (d := d) τ
                    (e.symm z))
            let Gflat : (Fin (n * (d + 1)) → ℂ) → ℂ :=
              fun z =>
                BHW.extendF (bvt_F OS lgc n)
                  (e.symm z)
            obtain ⟨hCflat_open_raw, hCflat_conv_raw, _hCflat_zero,
              hCflat_cone_raw, hCflat_ne_raw⟩ :=
              BHW.os45FlatCommonChartCone_eowReady d n
            have hCflat_open : IsOpen Cflat :=
              by simpa [Cflat] using hCflat_open_raw
            have hCflat_conv : Convex ℝ Cflat :=
              by simpa [Cflat] using hCflat_conv_raw
            have hCflat_ne : Cflat.Nonempty :=
              by simpa [Cflat] using hCflat_ne_raw
            have hCflat_cone :
                ∀ (t : ℝ), 0 < t → ∀ y ∈ Cflat, t • y ∈ Cflat :=
              by
                intro t ht y hy
                simpa [Cflat] using
                  hCflat_cone_raw t y ht (by simpa [Cflat] using hy)
            have hCflat_to_ET :
                Set.MapsTo
                  (fun z : Fin (n * (d + 1)) → ℂ => e.symm z)
                  (SCV.TubeDomain Cflat) (BHW.ExtendedTube d n) :=
              ?os45_vladimirov_realJostEdge_localFlatCone_mapsTo_ET
            have hCflat_to_permET :
                Set.MapsTo
                  (fun z : Fin (n * (d + 1)) → ℂ =>
                    BHW.permAct (d := d) τ (e.symm z))
                  (SCV.TubeDomain Cflat) (BHW.ExtendedTube d n) :=
              ?os45_vladimirov_realJostEdge_localFlatCone_mapsTo_permET
            have hFflat_holo :
                DifferentiableOn ℂ Fflat (SCV.TubeDomain Cflat) := by
              have hExtend :=
                BHW.differentiableOn_extendF_bvt_F_extendedTube
                  (d := d) OS lgc n
              have hinner :
                  DifferentiableOn ℂ
                    (fun z : Fin (n * (d + 1)) → ℂ =>
                      BHW.permAct (d := d) τ (e.symm z))
                    (SCV.TubeDomain Cflat) := by
                exact
                  ((BHW.differentiable_permAct (d := d) (n := n) τ).comp
                    e.symm.differentiable).differentiableOn
              simpa [Fflat] using
                hExtend.comp hinner hCflat_to_permET
            have hGflat_holo :
                DifferentiableOn ℂ Gflat (SCV.TubeDomain Cflat) := by
              have hExtend :=
                BHW.differentiableOn_extendF_bvt_F_extendedTube
                  (d := d) OS lgc n
              simpa [Gflat] using
                hExtend.comp e.symm.differentiableOn hCflat_to_ET
            have hFflat_tempered :
                SCV.HasFourierLaplaceReprTempered Cflat Fflat :=
              ?os45_vladimirov_realJostEdge_permExtendF_temperedBV
            have hGflat_tempered :
                SCV.HasFourierLaplaceReprTempered Cflat Gflat :=
              ?os45_vladimirov_realJostEdge_extendF_temperedBV
            have hBoundaryDist_eq :
                ∀ ρ : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ,
                  hFflat_tempered.dist ρ = hGflat_tempered.dist ρ :=
              ?os45_OSI45_sourceSide_commonBoundaryDistribution
            have hFflat_int :
                ∀ y ∈ Cflat,
                  ∀ ρ : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ,
                    MeasureTheory.Integrable
                      (fun x : Fin (n * (d + 1)) → ℝ =>
                        Fflat
                          (fun a => (x a : ℂ) +
                            (y a : ℂ) * Complex.I) * ρ x) :=
              by
                intro y hy ρ
                have hK_sub : ({y} : Set (Fin (n * (d + 1)) → ℝ)) ⊆
                    Cflat := by
                  intro y' hy'
                  simpa [Set.mem_singleton_iff.mp hy'] using hy
                obtain ⟨C_bd, N, _hC_bd_pos, hbound⟩ :=
                  hFflat_tempered.poly_growth {y} isCompact_singleton hK_sub
                have hslice_cont :
                    Continuous
                      (fun x : Fin (n * (d + 1)) → ℝ =>
                        Fflat
                          (fun a => (x a : ℂ) +
                            (y a : ℂ) * Complex.I)) := by
                  have hembed :
                      Continuous
                        (fun x : Fin (n * (d + 1)) → ℝ =>
                          (fun a => (x a : ℂ) +
                            (y a : ℂ) * Complex.I :
                            Fin (n * (d + 1)) → ℂ)) :=
                    continuous_pi fun a =>
                      (Complex.continuous_ofReal.comp
                        (continuous_apply a)).add continuous_const
                  have hmem :
                      ∀ x : Fin (n * (d + 1)) → ℝ,
                        (fun a => (x a : ℂ) +
                          (y a : ℂ) * Complex.I :
                          Fin (n * (d + 1)) → ℂ) ∈
                          SCV.TubeDomain Cflat := by
                    intro x
                    simpa [SCV.TubeDomain, Complex.add_im,
                      Complex.mul_im, Complex.ofReal_re,
                      Complex.ofReal_im, Complex.I_re, Complex.I_im] using hy
                  exact hFflat_holo.continuousOn.comp_continuous hembed hmem
                refine
                  SCV.integrable_poly_growth_schwartz
                    (fun x : Fin (n * (d + 1)) → ℝ =>
                      Fflat
                        (fun a => (x a : ℂ) +
                          (y a : ℂ) * Complex.I))
                    hslice_cont.aestronglyMeasurable C_bd N ?_ ρ
                intro x
                exact hbound x y (by simp)
            have hGflat_int :
                ∀ y ∈ Cflat,
                  ∀ ρ : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ,
                    MeasureTheory.Integrable
                      (fun x : Fin (n * (d + 1)) → ℝ =>
                        Gflat
                          (fun a => (x a : ℂ) +
                            (y a : ℂ) * Complex.I) * ρ x) :=
              by
                intro y hy ρ
                have hK_sub : ({y} : Set (Fin (n * (d + 1)) → ℝ)) ⊆
                    Cflat := by
                  intro y' hy'
                  simpa [Set.mem_singleton_iff.mp hy'] using hy
                obtain ⟨C_bd, N, _hC_bd_pos, hbound⟩ :=
                  hGflat_tempered.poly_growth {y} isCompact_singleton hK_sub
                have hslice_cont :
                    Continuous
                      (fun x : Fin (n * (d + 1)) → ℝ =>
                        Gflat
                          (fun a => (x a : ℂ) +
                            (y a : ℂ) * Complex.I)) := by
                  have hembed :
                      Continuous
                        (fun x : Fin (n * (d + 1)) → ℝ =>
                          (fun a => (x a : ℂ) +
                            (y a : ℂ) * Complex.I :
                            Fin (n * (d + 1)) → ℂ)) :=
                    continuous_pi fun a =>
                      (Complex.continuous_ofReal.comp
                        (continuous_apply a)).add continuous_const
                  have hmem :
                      ∀ x : Fin (n * (d + 1)) → ℝ,
                        (fun a => (x a : ℂ) +
                          (y a : ℂ) * Complex.I :
                          Fin (n * (d + 1)) → ℂ) ∈
                          SCV.TubeDomain Cflat := by
                    intro x
                    simpa [SCV.TubeDomain, Complex.add_im,
                      Complex.mul_im, Complex.ofReal_re,
                      Complex.ofReal_im, Complex.I_re, Complex.I_im] using hy
                  exact hGflat_holo.continuousOn.comp_continuous hembed hmem
                refine
                  SCV.integrable_poly_growth_schwartz
                    (fun x : Fin (n * (d + 1)) → ℝ =>
                      Gflat
                        (fun a => (x a : ℂ) +
                          (y a : ℂ) * Complex.I))
                    hslice_cont.aestronglyMeasurable C_bd N ?_ ρ
                intro x
                exact hbound x y (by simp)
            have hVladimirov_eqOn :
                Set.EqOn Fflat Gflat (SCV.TubeDomain Cflat) :=
              tube_holomorphic_unique_from_equal_tempered_bv_flat
                hCflat_open hCflat_conv hCflat_ne hCflat_cone
                hFflat_holo hGflat_holo
                hFflat_tempered hGflat_tempered
                hBoundaryDist_eq hFflat_int hGflat_int
            have hzero :
                ∫ u : NPointDomain d n,
                  (BHW.extendF (bvt_F OS lgc n)
                      (BHW.realEmbed
                        (fun k => u
                          ((Equiv.swap i ⟨i.val + 1, hi⟩) k))) -
                    BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u)) *
                    χ u = 0 := by
              let eR : NPointDomain d n ≃L[ℝ]
                  (Fin (n * (d + 1)) → ℝ) :=
                flattenCLEquivReal n (d + 1)
              let ρ : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ :=
                flattenSchwartzNPoint (d := d) χ
              let Uflat : Set (Fin (n * (d + 1)) → ℝ) :=
                eR '' U
              have hUflat_open : IsOpen Uflat := by
                simpa [Uflat, eR] using eR.toHomeomorph.isOpenMap U hU_open
              have hρ_support :
                  tsupport (ρ : (Fin (n * (d + 1)) → ℝ) → ℂ) ⊆
                    Uflat := by
                have hρ_tsupport :
                    tsupport (ρ : (Fin (n * (d + 1)) → ℝ) → ℂ) =
                      eR.symm.toHomeomorph ⁻¹'
                        tsupport (χ : NPointDomain d n → ℂ) := by
                  simpa [ρ, eR, flattenSchwartzNPoint,
                    SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
                    (tsupport_comp_eq_preimage
                      (g := (χ : NPointDomain d n → ℂ))
                      eR.symm.toHomeomorph)
                intro x hx
                have hxχ : eR.symm x ∈
                    tsupport (χ : NPointDomain d n → ℂ) := by
                  simpa [hρ_tsupport] using hx
                exact ⟨eR.symm x, hχU hxχ, by simp [eR]⟩
              have hρ_compact :
                  HasCompactSupport
                    (ρ : (Fin (n * (d + 1)) → ℝ) → ℂ) := by
                simpa [ρ, eR, flattenSchwartzNPoint] using
                  hχ_compact.comp_homeomorph eR.symm.toHomeomorph
              have hFflat_boundary_cont :
                  ∀ x ∈ Uflat,
                    ContinuousWithinAt Fflat (SCV.TubeDomain Cflat)
                      (SCV.realEmbed x) :=
                by
                  intro x hx
                  rcases hx with ⟨u, huU, rfl⟩
                  have hflat_real :
                      e.symm (SCV.realEmbed (eR u)) =
                        BHW.realEmbed u := by
                    ext k μ
                    simp [e, eR, SCV.realEmbed, BHW.realEmbed]
                  have hpointET :
                      BHW.permAct (d := d) τ
                        (e.symm (SCV.realEmbed (eR u))) ∈
                        BHW.ExtendedTube d n := by
                    have hu_sector :=
                      H.realPatch_mem_permutedExtendedTubeSector u
                        (hU_sub huU)
                    rw [hflat_real]
                    simpa [τ, P.τ_eq, BHW.permutedExtendedTubeSector,
                      BHW.permAct_realEmbed, BHW.permAct] using hu_sector
                  have hbranch_cont :
                      ContinuousWithinAt
                        (BHW.extendF (bvt_F OS lgc n))
                        (BHW.ExtendedTube d n)
                        (BHW.permAct (d := d) τ
                          (e.symm (SCV.realEmbed (eR u)))) :=
                    (BHW.differentiableOn_extendF_bvt_F_extendedTube
                      (d := d) OS lgc n).continuousOn.continuousWithinAt
                        hpointET
                  have hinner_cont :
                      ContinuousWithinAt
                        (fun z : Fin (n * (d + 1)) → ℂ =>
                          BHW.permAct (d := d) τ (e.symm z))
                        (SCV.TubeDomain Cflat)
                        (SCV.realEmbed (eR u)) :=
                    (((BHW.differentiable_permAct (d := d) (n := n) τ).continuous.comp
                      e.symm.continuous).continuousAt.continuousWithinAt)
                  simpa [Fflat] using
                    ContinuousWithinAt.comp
                      (f := fun z : Fin (n * (d + 1)) → ℂ =>
                        BHW.permAct (d := d) τ (e.symm z))
                      (g := BHW.extendF (bvt_F OS lgc n))
                      (s := SCV.TubeDomain Cflat)
                      (t := BHW.ExtendedTube d n)
                      (x := SCV.realEmbed (eR u))
                      hbranch_cont hinner_cont hCflat_to_permET
              have hGflat_boundary_cont :
                  ∀ x ∈ Uflat,
                    ContinuousWithinAt Gflat (SCV.TubeDomain Cflat)
                      (SCV.realEmbed x) :=
                by
                  intro x hx
                  rcases hx with ⟨u, huU, rfl⟩
                  have hflat_real :
                      e.symm (SCV.realEmbed (eR u)) =
                        BHW.realEmbed u := by
                    ext k μ
                    simp [e, eR, SCV.realEmbed, BHW.realEmbed]
                  have hpointET :
                      e.symm (SCV.realEmbed (eR u)) ∈
                        BHW.ExtendedTube d n := by
                    rw [hflat_real]
                    exact H.realPatch_mem_extendedTube u (hU_sub huU)
                  have hbranch_cont :
                      ContinuousWithinAt
                        (BHW.extendF (bvt_F OS lgc n))
                        (BHW.ExtendedTube d n)
                        (e.symm (SCV.realEmbed (eR u))) :=
                    (BHW.differentiableOn_extendF_bvt_F_extendedTube
                      (d := d) OS lgc n).continuousOn.continuousWithinAt
                        hpointET
                  have hinner_cont :
                      ContinuousWithinAt
                        (fun z : Fin (n * (d + 1)) → ℂ => e.symm z)
                        (SCV.TubeDomain Cflat)
                        (SCV.realEmbed (eR u)) :=
                    e.symm.continuous.continuousAt.continuousWithinAt
                  simpa [Gflat] using
                    ContinuousWithinAt.comp
                      (f := fun z : Fin (n * (d + 1)) → ℂ => e.symm z)
                      (g := BHW.extendF (bvt_F OS lgc n))
                      (s := SCV.TubeDomain Cflat)
                      (t := BHW.ExtendedTube d n)
                      (x := SCV.realEmbed (eR u))
                      hbranch_cont hinner_cont hCflat_to_ET
              have hFflat_recovery :
                  hFflat_tempered.dist ρ =
                    ∫ x : Fin (n * (d + 1)) → ℝ,
                      Fflat (SCV.realEmbed x) * ρ x :=
                SCV.fourierLaplace_boundary_recovery_on_open_of_tempered
                  hCflat_open hCflat_conv hCflat_ne hCflat_cone
                  hFflat_holo hFflat_tempered
                  Uflat hUflat_open hFflat_boundary_cont
                  ρ hρ_support hρ_compact
              have hGflat_recovery :
                  hGflat_tempered.dist ρ =
                    ∫ x : Fin (n * (d + 1)) → ℝ,
                      Gflat (SCV.realEmbed x) * ρ x :=
                SCV.fourierLaplace_boundary_recovery_on_open_of_tempered
                  hCflat_open hCflat_conv hCflat_ne hCflat_cone
                  hGflat_holo hGflat_tempered
                  Uflat hUflat_open hGflat_boundary_cont
                  ρ hρ_support hρ_compact
              have hflat_pairing_eq :
                  (∫ x : Fin (n * (d + 1)) → ℝ,
                    Fflat (SCV.realEmbed x) * ρ x) =
                  ∫ x : Fin (n * (d + 1)) → ℝ,
                    Gflat (SCV.realEmbed x) * ρ x := by
                calc
                  (∫ x : Fin (n * (d + 1)) → ℝ,
                    Fflat (SCV.realEmbed x) * ρ x)
                      = hFflat_tempered.dist ρ := hFflat_recovery.symm
                  _ = hGflat_tempered.dist ρ := hBoundaryDist_eq ρ
                  _ = ∫ x : Fin (n * (d + 1)) → ℝ,
                    Gflat (SCV.realEmbed x) * ρ x := hGflat_recovery
              let A : NPointDomain d n → ℂ :=
                fun u =>
                  BHW.extendF (bvt_F OS lgc n)
                    (BHW.realEmbed
                      (fun k => u
                        ((Equiv.swap i ⟨i.val + 1, hi⟩) k)))
              let B : NPointDomain d n → ℂ :=
                fun u =>
                  BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u)
              have hFflat_source :
                  (∫ x : Fin (n * (d + 1)) → ℝ,
                    Fflat (SCV.realEmbed x) * ρ x) =
                  ∫ u : NPointDomain d n, A u * χ u :=
                by
                  rw [integral_flatten_change_of_variables n (d + 1)]
                  congr 1
                  ext y
                  have hflat_real :
                      e.symm (SCV.realEmbed (eR y)) =
                        BHW.realEmbed y := by
                    ext k μ
                    simp [e, eR, SCV.realEmbed, BHW.realEmbed]
                  have hFarg :
                      Fflat (SCV.realEmbed (eR y)) = A y := by
                    simp [Fflat, A, τ, hflat_real,
                      BHW.permAct_realEmbed]
                  have hρarg : ρ (eR y) = χ y := by
                    simp [ρ, eR, flattenSchwartzNPoint]
                  simp [eR, hFarg, hρarg]
              have hGflat_source :
                  (∫ x : Fin (n * (d + 1)) → ℝ,
                    Gflat (SCV.realEmbed x) * ρ x) =
                  ∫ u : NPointDomain d n, B u * χ u :=
                by
                  rw [integral_flatten_change_of_variables n (d + 1)]
                  congr 1
                  ext y
                  have hflat_real :
                      e.symm (SCV.realEmbed (eR y)) =
                        BHW.realEmbed y := by
                    ext k μ
                    simp [e, eR, SCV.realEmbed, BHW.realEmbed]
                  have hGarg :
                      Gflat (SCV.realEmbed (eR y)) = B y := by
                    simp [Gflat, B, hflat_real]
                  have hρarg : ρ (eR y) = χ y := by
                    simp [ρ, eR, flattenSchwartzNPoint]
                  simp [eR, hGarg, hρarg]
              have hsource_pairing_eq :
                  (∫ u : NPointDomain d n, A u * χ u) =
                  ∫ u : NPointDomain d n, B u * χ u := by
                calc
                  (∫ u : NPointDomain d n, A u * χ u)
                      = ∫ x : Fin (n * (d + 1)) → ℝ,
                          Fflat (SCV.realEmbed x) * ρ x := hFflat_source.symm
                  _ = ∫ x : Fin (n * (d + 1)) → ℝ,
                          Gflat (SCV.realEmbed x) * ρ x := hflat_pairing_eq
                  _ = ∫ u : NPointDomain d n, B u * χ u := hGflat_source
              have hdiff_eq :
                  (∫ u : NPointDomain d n,
                    (BHW.extendF (bvt_F OS lgc n)
                        (BHW.realEmbed
                          (fun k => u
                            ((Equiv.swap i ⟨i.val + 1, hi⟩) k))) -
                      BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed u)) *
                      χ u) =
                    (∫ u : NPointDomain d n, A u * χ u) -
                      ∫ u : NPointDomain d n, B u * χ u := by
                trans ∫ u : NPointDomain d n, A u * χ u - B u * χ u
                · refine MeasureTheory.integral_congr_ae
                    (Filter.Eventually.of_forall ?_)
                  intro u
                  simp [A, B]
                  ring
                · simpa [A, B] using
                    MeasureTheory.integral_sub hτ_int hid_int
              simpa using
                hdiff_eq.trans (sub_eq_zero.mpr hsource_pairing_eq)
            have hpair :=
              BHW.integral_realSourceBranchDifference_eq_zero_to_pairing_eq
                (d := d) OS lgc n
                (Equiv.swap i ⟨i.val + 1, hi⟩) χ hid_int hτ_int hzero
            exact hpair.symm
          have hOverlap :
              IsConnected
                {z : Fin n → Fin (d + 1) → ℂ |
                  z ∈ BHW.ExtendedTube d n ∧
                    BHW.permAct (d := d)
                      (Equiv.swap i ⟨i.val + 1, hi⟩) z ∈
                      BHW.ExtendedTube d n} :=
            bvt_selectedAdjacentOverlap_connected_of_permSeedGeometry
              (d := d) n i hi
          have hF_holo :
              DifferentiableOn ℂ (bvt_F OS lgc n)
                (BHW.ForwardTube d n) := by
            simpa [BHW_forwardTube_eq (d := d) (n := n)] using
              bvt_F_holomorphic (d := d) OS lgc n
          have hF_lorentz :
              ∀ (Λ : RestrictedLorentzGroup d)
                (z : Fin n → Fin (d + 1) → ℂ),
                z ∈ BHW.ForwardTube d n →
                bvt_F OS lgc n
                  (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) =
                bvt_F OS lgc n z := by
            intro Λ z hz
            exact bvt_F_restrictedLorentzInvariant_forwardTube
              (d := d) OS lgc n Λ z
              ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
          refine MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall ?_)
          intro u
          by_cases hu : u ∈ U
          · have huP : u ∈ P.V := hU_sub hu
            let z : Fin n → Fin (d + 1) → ℂ :=
              fun k => wickRotatePoint (u k)
            have hz_forward : z ∈ BHW.ForwardTube d n := by
              simpa [z] using
                BHW.os45Figure24_ordinaryWick_mem_forwardTube
                  (d := d) (n := n) (hd := hd) (P := P) huP
            have hz_ET : z ∈ BHW.ExtendedTube d n :=
              H.ordinaryWick_mem_extendedTube u huP
            have hτz_ET :
                BHW.permAct (d := d) P.τ z ∈
                  BHW.ExtendedTube d n := by
              simpa [z, BHW.permAct] using
                BHW.os45Figure24_adjacentWick_mem_extendedTube
                  (d := d) (n := n) (hd := hd) (P := P) huP
            have hVedge_ET :
                ∀ x ∈ U, BHW.realEmbed x ∈
                  BHW.ExtendedTube d n := by
              intro x hx
              exact H.realPatch_mem_extendedTube x (hU_sub hx)
            have hVedge_swapET :
                ∀ x ∈ U,
                  BHW.realEmbed
                    (fun k => x
                      ((Equiv.swap i ⟨i.val + 1, hi⟩) k)) ∈
                    BHW.ExtendedTube d n := by
              intro x hx
              have hx_sector :=
                H.realPatch_mem_permutedExtendedTubeSector x (hU_sub hx)
              simpa [P.τ_eq, BHW.permutedExtendedTubeSector,
                BHW.permAct_realEmbed, BHW.permAct] using hx_sector
            have hbranch :
                BHW.extendF (bvt_F OS lgc n)
                    (BHW.permAct (d := d) P.τ z) =
                  BHW.extendF (bvt_F OS lgc n) z := by
              have hlocal :=
                BHW.bvt_F_extendF_adjacent_overlap_of_localEdgePairing
                  (d := d) OS lgc n i hi hOverlap
                  U hU_open hU_connected.nonempty
                  hVedge_ET hVedge_swapET hrealEdge
                  z hz_ET
                  (by simpa [P.τ_eq] using hτz_ET)
              simpa [P.τ_eq] using hlocal
            have hext :
                BHW.extendF (bvt_F OS lgc n) z =
                  bvt_F OS lgc n z :=
              BHW.extendF_eq_on_forwardTube n (bvt_F OS lgc n)
                hF_holo hF_lorentz z hz_forward
            have hperm :
                bvt_F OS lgc n
                    (fun k => wickRotatePoint (u (P.τ k))) =
                  bvt_F OS lgc n z := by
              simpa [z, BHW.permAct] using
                bvt_F_perm (d := d) OS lgc n P.τ
                  (fun k => wickRotatePoint (u k))
            have hpoint :
                BHW.extendF (bvt_F OS lgc n)
                    (BHW.permAct (d := d) P.τ z) =
                  bvt_F OS lgc n
                    (fun k => wickRotatePoint (u (P.τ k))) :=
              hbranch.trans (hext.trans hperm.symm)
            simpa [z] using congrArg (fun c : ℂ => c * ψ u) hpoint
          · have hψ_zero : ψ u = 0 :=
              image_eq_zero_of_notMem_tsupport
                (fun hψ_supp => hu (hψU hψ_supp))
            simp [hψ_zero]
      _ =
        ∫ u : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (u k)) * ψ u := by
          let D : BHW.OS45Figure24SourceCutoffData P :=
            Classical.choice
              (BHW.exists_os45Figure24SourceCutoffData (d := d) P)
          let ψflat :
              SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ :=
            (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
              (BHW.os45CommonEdgeFlatCLE d n
                (1 : Equiv.Perm (Fin n))).symm) ψ
          have hψP : tsupport (ψ : NPointDomain d n → ℂ) ⊆ P.V :=
            hψU.trans hU_sub
          have hψflatE :
              tsupport (ψflat :
                BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
                BHW.os45FlatCommonChartEdgeSet d n P
                  (1 : Equiv.Perm (Fin n)) := by
            simpa [ψflat] using
              BHW.tsupport_comp_os45CommonEdgeFlatCLE_symm_subset_edgeSet
                (d := d) (n := n) (hd := hd) (P := P)
                (1 : Equiv.Perm (Fin n)) ψ hψP
          have hDψ :
              D.toSchwartzNPointCLM (1 : Equiv.Perm (Fin n)) ψflat =
                ψ := by
            simpa [ψflat] using
              D.toSchwartzNPointCLM_flatPullback_eq
                (1 : Equiv.Perm (Fin n)) ψ hψP
          have hraw :=
            BHW.os45CommonEdge_adjacentWick_sourcePairing_eq_ordinaryWick
              (d := d) (hd := hd) (n := n) OS lgc (P := P)
              D ψflat hψflatE
          rw [hDψ] at hraw
          simpa using hraw
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
  have hflat_eq :
      ∀ x ∈ BHW.os45CommonEdgeFlatCLE d n
          (1 : Equiv.Perm (Fin n)) '' U,
        BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n))) (SCV.realEmbed x) =
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n)) (SCV.realEmbed x) :=
    BHW.os45FlatCommonChart_realEdge_branch_eq_of_source_commonEdge_branch_eqOn
      (d := d) hd OS lgc (P := P) hsource_eq
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro x
  by_cases hx : x ∈
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ)
  · exact congrArg (fun c : ℂ => c * φ x) (hflat_eq x (hφU hx))
  · have hφ_zero : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [hφ_zero]

end BHW
