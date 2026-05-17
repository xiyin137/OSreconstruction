import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45SourceSide

/-!
# OS45 Source-Side Moving Tests

This file contains the compact-support moving-test convergence step for the
strict OS45 theorem-2 route.  It is neutral analytic support: it combines the
checked endpoint dominated-convergence lemma, the checked moving-test error
estimate, and the explicit integral split.  It does not select a boundary
functional and does not assert any OS-I branch/source transfer.
-/

noncomputable section

open Complex Topology MeasureTheory Filter

namespace BHW

variable {d n : ℕ} [NeZero d]

/-- Moving source tests converge along the genuine OS45 source-side path when
they share an eventual compact support and converge in the zeroth Schwartz
seminorm.

This is the analytic moving-test leaf used after a fixed-test endpoint limit
has already been selected.  It packages no branch-selection statement: the
carrier `F` is an arbitrary continuous local branch on an open carrier. -/
theorem tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_moving_of_commonCompactSupport
    (ρperm : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    {U : Set (Fin n → Fin (d + 1) → ℂ)}
    (hU_open : IsOpen U)
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF_cont : ContinuousOn F U)
    {K : Set (NPointDomain d n)}
    (hK : IsCompact K)
    (h0 :
      ∀ u ∈ K,
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u ∈ U)
    {α : Type*} {l : Filter α}
    {εseq : α → ℝ}
    (hεseq : Tendsto εseq l (𝓝[Set.Ioi 0] (0 : ℝ)))
    {φseq : α → SchwartzNPoint d n} {φ0 : SchwartzNPoint d n}
    (hφ0K : tsupport (φ0 : NPointDomain d n → ℂ) ⊆ K)
    (hsupp :
      ∀ᶠ a in l,
        ∀ u ∉ K,
          ((φseq a - φ0 : SchwartzNPoint d n) :
            NPointDomain d n → ℂ) u = 0)
    (hseminorm :
      Tendsto
        (fun a : α =>
          SchwartzMap.seminorm ℝ 0 0
            (φseq a - φ0 : SchwartzNPoint d n))
        l (𝓝 0)) :
    Tendsto
      (fun a : α =>
        ∫ u : NPointDomain d n,
          F (BHW.os45FlatCommonChartSourceSide
            d n ρperm sgn (εseq a) η u) *
          (φseq a : NPointDomain d n → ℂ) u)
      l
      (𝓝
        (∫ u : NPointDomain d n,
          F (BHW.os45FlatCommonChartSourceSide
            d n ρperm sgn 0 η u) *
          (φ0 : NPointDomain d n → ℂ) u)) := by
  have hφ0_zero_off_K :
      ∀ u ∉ K, (φ0 : NPointDomain d n → ℂ) u = 0 := by
    intro u huK
    exact image_eq_zero_of_notMem_tsupport (fun hu => huK (hφ0K hu))
  have hφ0_compact :
      HasCompactSupport (φ0 : NPointDomain d n → ℂ) := by
    exact
      HasCompactSupport.of_support_subset_isCompact hK
        (by
          intro u hu
          by_contra huK
          exact hu (hφ0_zero_off_K u huK))
  have hfixed_zero :
      Tendsto
        (fun ε : ℝ =>
          ∫ u : NPointDomain d n,
            F (BHW.os45FlatCommonChartSourceSide
              d n ρperm sgn ε η u) *
            (φ0 : NPointDomain d n → ℂ) u)
        (𝓝[Set.Ioi 0] (0 : ℝ))
        (𝓝
          (∫ u : NPointDomain d n,
            F (BHW.os45FlatCommonChartSourceSide
              d n ρperm sgn 0 η u) *
            (φ0 : NPointDomain d n → ℂ) u)) := by
    exact
      BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_of_hasCompactSupport
        (d := d) (n := n) ρperm sgn η hU_open hF_cont
        hφ0_compact φ0.continuous
        (by
          intro u hu
          exact h0 u (hφ0K hu))
  have hfixed :
      Tendsto
        (fun a : α =>
          ∫ u : NPointDomain d n,
            F (BHW.os45FlatCommonChartSourceSide
              d n ρperm sgn (εseq a) η u) *
            (φ0 : NPointDomain d n → ℂ) u)
        l
        (𝓝
          (∫ u : NPointDomain d n,
            F (BHW.os45FlatCommonChartSourceSide
              d n ρperm sgn 0 η u) *
            (φ0 : NPointDomain d n → ℂ) u)) :=
    hfixed_zero.comp hεseq
  have hdiff :
      Tendsto
        (fun a : α =>
          ∫ u : NPointDomain d n,
            F (BHW.os45FlatCommonChartSourceSide
              d n ρperm sgn (εseq a) η u) *
            ((φseq a - φ0 : SchwartzNPoint d n) :
              NPointDomain d n → ℂ) u)
        l (𝓝 0) := by
    exact
      BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_sub_of_commonCompactSupport
        (d := d) (n := n) ρperm sgn η hU_open hF_cont
        hK h0 hεseq hsupp hseminorm
  have hsplit :
      (fun a : α =>
        ∫ u : NPointDomain d n,
          F (BHW.os45FlatCommonChartSourceSide
            d n ρperm sgn (εseq a) η u) *
          (φseq a : NPointDomain d n → ℂ) u)
      =ᶠ[l]
      (fun a : α =>
        (∫ u : NPointDomain d n,
          F (BHW.os45FlatCommonChartSourceSide
            d n ρperm sgn (εseq a) η u) *
          (φ0 : NPointDomain d n → ℂ) u) +
        (∫ u : NPointDomain d n,
          F (BHW.os45FlatCommonChartSourceSide
            d n ρperm sgn (εseq a) η u) *
          ((φseq a - φ0 : SchwartzNPoint d n) :
            NPointDomain d n → ℂ) u)) := by
    rcases
      BHW.exists_bound_eventually_forall_norm_comp_os45FlatCommonChartSourceSide
        (d := d) (n := n) ρperm sgn η
        hK hU_open h0 hF_cont with
      ⟨M, _hM_nonneg, hM_bound⟩
    have hmem :
        ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
          ∀ u ∈ K,
            BHW.os45FlatCommonChartSourceSide
              d n ρperm sgn ε η u ∈ U :=
      BHW.eventually_forall_os45FlatCommonChartSourceSide_mem_of_compact
        (d := d) (n := n) ρperm sgn η hK hU_open h0
    have hM_seq :
        ∀ᶠ a in l,
          ∀ u ∈ K,
            ‖F (BHW.os45FlatCommonChartSourceSide
                d n ρperm sgn (εseq a) η u)‖ ≤ M :=
      hεseq.eventually hM_bound
    have hmem_seq :
        ∀ᶠ a in l,
          ∀ u ∈ K,
            BHW.os45FlatCommonChartSourceSide
              d n ρperm sgn (εseq a) η u ∈ U :=
      hεseq.eventually hmem
    filter_upwards [hM_seq, hmem_seq, hsupp] with a hM_a hmem_a hsupp_a
    have hfixed_int :
        Integrable
          (fun u : NPointDomain d n =>
            F (BHW.os45FlatCommonChartSourceSide
              d n ρperm sgn (εseq a) η u) *
            (φ0 : NPointDomain d n → ℂ) u) :=
      BHW.integrable_comp_os45FlatCommonChartSourceSide_mul_of_commonCompactSupport
        (d := d) (n := n) ρperm sgn (εseq a) η
        hF_cont hK hmem_a hM_a φ0 hφ0_zero_off_K
    have hdiff_int :
        Integrable
          (fun u : NPointDomain d n =>
            F (BHW.os45FlatCommonChartSourceSide
              d n ρperm sgn (εseq a) η u) *
            ((φseq a - φ0 : SchwartzNPoint d n) :
              NPointDomain d n → ℂ) u) :=
      BHW.integrable_comp_os45FlatCommonChartSourceSide_mul_of_commonCompactSupport
        (d := d) (n := n) ρperm sgn (εseq a) η
        hF_cont hK hmem_a hM_a
        (φseq a - φ0 : SchwartzNPoint d n) hsupp_a
    rw [← MeasureTheory.integral_add hfixed_int hdiff_int]
    apply integral_congr_ae
    filter_upwards with u
    have htest :
        (φseq a : NPointDomain d n → ℂ) u =
          (φ0 : NPointDomain d n → ℂ) u +
            ((φseq a - φ0 : SchwartzNPoint d n) :
              NPointDomain d n → ℂ) u := by
      simp [sub_eq_add_neg]
    rw [htest, mul_add]
  simpa using (hfixed.add hdiff).congr' hsplit.symm

/-- Scalar cancellation for a fixed source-side test after the flat translated
test pullback.

This is the neutral coordinate/Jacobian step used inside the fixed-test
`sourceSide` leaves: once the flat translated-test integrals converge to
`J * L`, the checked translated-test pullback identifies them with
`J` times the fixed source-side integrals, and positivity of `J` cancels the
factor.  It does not select a boundary functional or assert any branch-transfer
theorem. -/
theorem tendsto_integral_comp_os45FlatCommonChartSourceSide_fixed_of_flatTranslatedTest
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (σ ρperm : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (ψFlat : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    {α : Type*} {l : Filter α}
    {εseq : α → ℝ}
    {L : ℂ}
    (hinteg :
      ∀ᶠ a in l,
        Integrable
          (fun x : BHW.OS45FlatCommonChartReal d n =>
            BHW.os45FlatCommonChartBranch d n OS lgc σ
              (fun j =>
                ((x + (sgn * εseq a) • η) j : ℂ) +
                  (((sgn * εseq a) • η) j : ℂ) * Complex.I) *
            (SCV.translateSchwartz (-(sgn * εseq a) • η) ψFlat)
              (x + (sgn * εseq a) • η)))
    (hflat :
      Tendsto
        (fun a : α =>
          ∫ x : BHW.OS45FlatCommonChartReal d n,
            BHW.os45FlatCommonChartBranch d n OS lgc σ
              (fun j =>
                (x j : ℂ) +
                  (((sgn * εseq a) • η) j : ℂ) * Complex.I) *
            (SCV.translateSchwartz (-(sgn * εseq a) • η) ψFlat) x)
        l
        (𝓝
          ((BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) * L))) :
    Tendsto
      (fun a : α =>
        ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) σ.symm
              (BHW.os45FlatCommonChartSourceSide
                d n ρperm sgn (εseq a) η u)) *
            ψFlat (BHW.os45CommonEdgeFlatCLE d n ρperm u))
      l (𝓝 L) := by
  let J : ℂ := BHW.os45CommonEdgeFlatJacobianAbs n
  have hJ_ne : J ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (ne_of_gt (BHW.os45CommonEdgeFlatJacobianAbs_pos n))
  have hpull :
      (fun a : α =>
        ∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc σ
            (fun j =>
              (x j : ℂ) +
                (((sgn * εseq a) • η) j : ℂ) * Complex.I) *
          (SCV.translateSchwartz (-(sgn * εseq a) • η) ψFlat) x)
      =ᶠ[l]
      (fun a : α =>
        J *
          ∫ u : NPointDomain d n,
            BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) σ.symm
                (BHW.os45FlatCommonChartSourceSide
                  d n ρperm sgn (εseq a) η u)) *
              ψFlat (BHW.os45CommonEdgeFlatCLE d n ρperm u)) := by
    filter_upwards [hinteg] with a ha
    simpa [J] using
      BHW.os45FlatCommonChart_branch_integral_eq_sourceSide_extendF_translatedTest
        (d := d) (n := n) OS lgc σ ρperm sgn (εseq a) η ψFlat ha
  have hscaled :
      Tendsto
        (fun a : α =>
          J *
            ∫ u : NPointDomain d n,
              BHW.extendF (bvt_F OS lgc n)
                (BHW.permAct (d := d) σ.symm
                  (BHW.os45FlatCommonChartSourceSide
                    d n ρperm sgn (εseq a) η u)) *
                ψFlat (BHW.os45CommonEdgeFlatCLE d n ρperm u))
        l (𝓝 (J * L)) := by
    simpa [J] using hflat.congr' hpull
  have hdescaled :
      Tendsto
        (fun a : α =>
          J⁻¹ *
            (J *
              ∫ u : NPointDomain d n,
                BHW.extendF (bvt_F OS lgc n)
                  (BHW.permAct (d := d) σ.symm
                    (BHW.os45FlatCommonChartSourceSide
                      d n ρperm sgn (εseq a) η u)) *
                  ψFlat (BHW.os45CommonEdgeFlatCLE d n ρperm u)))
        l (𝓝 (J⁻¹ * (J * L))) := by
    exact tendsto_const_nhds.mul hscaled
  simpa [J, hJ_ne, mul_assoc] using hdescaled

end BHW
