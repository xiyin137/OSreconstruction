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

/-- Concrete Figure-2-4 moving-test transfer for the two signed OS45
`sourceSide` test families.

This is the production specialization of
`tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_moving_of_commonCompactSupport`
to the actual side zero-diagonal cutoffs used in OS I `(4.14)`.  It packages
the checked source-window support and zeroth-seminorm convergence for the
`+` and `-` side tests, leaving only the local branch carrier continuity as an
explicit hypothesis. -/
theorem OS45Figure24SourceCutoffData.tendsto_sourceSide_extendF_sideZeroDiagonalCLM_pair
    {hd : 2 ≤ d}
    {i : Fin n} {hi : i.val + 1 < n}
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    (σ : Equiv.Perm (Fin n))
    {Ω : Set (Fin n → Fin (d + 1) → ℂ)}
    (hΩ_open : IsOpen Ω)
    (hF_cont :
      ContinuousOn
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) σ.symm z)) Ω)
    {Usrc Ksrc : Set (NPointDomain d n)}
    (hUsrc_open : IsOpen Usrc)
    (hUsrc_sub_K : Usrc ⊆ Ksrc)
    (hKsrc : IsCompact Ksrc)
    (η : BHW.OS45FlatCommonChartReal d n)
    (h0_plus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d n
          (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u ∈ Ω)
    (h0_minus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d n
          (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η u ∈ Ω)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact :
      HasCompactSupport
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφU :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45CommonEdgeFlatCLE d n
          (1 : Equiv.Perm (Fin n)) '' Usrc) :
    Tendsto
      (fun ε : ℝ =>
        ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) σ.symm
              (BHW.os45FlatCommonChartSourceSide d n
                (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η u)) *
            ((((D.toSideZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
                SchwartzNPoint d n) : NPointDomain d n → ℂ) u))
      (𝓝[Set.Ioi 0] (0 : ℝ))
      (𝓝
        (∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) σ.symm
              (BHW.os45FlatCommonChartSourceSide d n
                (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u)) *
            ((((D.toZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) φ).1 :
                SchwartzNPoint d n) : NPointDomain d n → ℂ) u))) ∧
    Tendsto
      (fun ε : ℝ =>
        ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) σ.symm
              (BHW.os45FlatCommonChartSourceSide d n
                (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η u)) *
            ((((D.toSideZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
                SchwartzNPoint d n) : NPointDomain d n → ℂ) u))
      (𝓝[Set.Ioi 0] (0 : ℝ))
      (𝓝
        (∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) σ.symm
              (BHW.os45FlatCommonChartSourceSide d n
                (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η u)) *
            ((((D.toZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) φ).1 :
                SchwartzNPoint d n) : NPointDomain d n → ℂ) u))) := by
  let F : (Fin n → Fin (d + 1) → ℂ) → ℂ := fun z =>
    BHW.extendF (bvt_F OS lgc n) (BHW.permAct (d := d) σ.symm z)
  let φ0 : SchwartzNPoint d n :=
    ((D.toZeroDiagonalCLM
      (1 : Equiv.Perm (Fin n)) φ).1 : SchwartzNPoint d n)
  have hφ0K : tsupport (φ0 : NPointDomain d n → ℂ) ⊆ Ksrc := by
    have hφ0U : tsupport (φ0 : NPointDomain d n → ℂ) ⊆ Usrc := by
      simpa [φ0, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM] using
        D.toSchwartzNPointCLM_tsupport_subset_image
          (1 : Equiv.Perm (Fin n)) φ hφU
    exact hφ0U.trans hUsrc_sub_K
  have hside_support :=
    D.toSideZeroDiagonalCLM_sub_toZeroDiagonalCLM_eq_zero_off_eventually
      hUsrc_open hUsrc_sub_K
      ({η} : Set (BHW.OS45FlatCommonChartReal d n))
      isCompact_singleton φ hφ_compact hφU
  have hseminorm_plus :
      Tendsto
        (fun ε : ℝ =>
          SchwartzMap.seminorm ℝ 0 0
            (((D.toSideZeroDiagonalCLM
                (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
                SchwartzNPoint d n) -
              φ0 : SchwartzNPoint d n))
        (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
    have h :=
      D.toSideZeroDiagonalCLM_sub_toZeroDiagonalCLM_seminorm_tendsto_zero
        (1 : Equiv.Perm (Fin n)) (1 : ℝ) η φ hφ_compact
    simpa [φ0] using h.mono_left nhdsWithin_le_nhds
  have hseminorm_minus :
      Tendsto
        (fun ε : ℝ =>
          SchwartzMap.seminorm ℝ 0 0
            (((D.toSideZeroDiagonalCLM
                (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
                SchwartzNPoint d n) -
              φ0 : SchwartzNPoint d n))
        (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
    have h :=
      D.toSideZeroDiagonalCLM_sub_toZeroDiagonalCLM_seminorm_tendsto_zero
        (1 : Equiv.Perm (Fin n)) (-1 : ℝ) η φ hφ_compact
    simpa [φ0] using h.mono_left nhdsWithin_le_nhds
  have hsupp_plus :
      ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
        ∀ u ∉ Ksrc,
          ((((D.toSideZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
              SchwartzNPoint d n) -
            φ0 : SchwartzNPoint d n) :
              NPointDomain d n → ℂ) u = 0 := by
    filter_upwards [hside_support] with ε hε u huK
    have h := (hε η (by simp)).1 u huK
    simpa [φ0, Pi.sub_apply] using h
  have hsupp_minus :
      ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
        ∀ u ∉ Ksrc,
          ((((D.toSideZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
              SchwartzNPoint d n) -
            φ0 : SchwartzNPoint d n) :
              NPointDomain d n → ℂ) u = 0 := by
    filter_upwards [hside_support] with ε hε u huK
    have h := (hε η (by simp)).2 u huK
    simpa [φ0, Pi.sub_apply] using h
  constructor
  · have h :=
      BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_moving_of_commonCompactSupport
        (d := d) (n := n)
        (1 : Equiv.Perm (Fin n)) (1 : ℝ) η
        hΩ_open (by simpa [F] using hF_cont)
        hKsrc h0_plus
        (tendsto_id :
          Tendsto (fun ε : ℝ => ε)
            (𝓝[Set.Ioi 0] (0 : ℝ))
            (𝓝[Set.Ioi 0] (0 : ℝ)))
        hφ0K hsupp_plus hseminorm_plus
    simpa [F, φ0] using h
  · have h :=
      BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_moving_of_commonCompactSupport
        (d := d) (n := n)
        (1 : Equiv.Perm (Fin n)) (-1 : ℝ) η
        hΩ_open (by simpa [F] using hF_cont)
        hKsrc h0_minus
        (tendsto_id :
          Tendsto (fun ε : ℝ => ε)
            (𝓝[Set.Ioi 0] (0 : ℝ))
            (𝓝[Set.Ioi 0] (0 : ℝ)))
        hφ0K hsupp_minus hseminorm_minus
    simpa [F, φ0] using h

/-- Difference form of the concrete Figure-2-4 source-side moving-test
transfer from a zero-height pairing equality.

This is the source-current-facing version of the moving-test bookkeeping:
after the selected OS-I argument has proved equality of the two zero-height
source pairings for the pulled-back test, the signed moving side-test
integrals have the same limit.  No pointwise common-edge equality is used
here. -/
theorem OS45Figure24SourceCutoffData.tendsto_sourceSide_extendF_difference_zero_of_zeroHeightPairing
    {hd : 2 ≤ d}
    {i : Fin n} {hi : i.val + 1 < n}
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    {Ωplus Ωminus : Set (Fin n → Fin (d + 1) → ℂ)}
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    (hFplus_cont :
      ContinuousOn
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n) z) Ωplus)
    (hFminus_cont :
      ContinuousOn
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm z)) Ωminus)
    {Usrc Ksrc : Set (NPointDomain d n)}
    (hUsrc_open : IsOpen Usrc)
    (hUsrc_sub_K : Usrc ⊆ Ksrc)
    (hKsrc : IsCompact Ksrc)
    (η : BHW.OS45FlatCommonChartReal d n)
    (h0_plus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d n
          (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u ∈ Ωplus)
    (h0_minus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d n
          (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η u ∈ Ωminus)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact :
      HasCompactSupport
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφU :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45CommonEdgeFlatCLE d n
          (1 : Equiv.Perm (Fin n)) '' Usrc)
    (hzero_pairing :
      (∫ u : NPointDomain d n,
        BHW.extendF (bvt_F OS lgc n)
          (BHW.os45FlatCommonChartSourceSide d n
            (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u) *
          ((((D.toZeroDiagonalCLM
            (1 : Equiv.Perm (Fin n)) φ).1 : SchwartzNPoint d n) :
              NPointDomain d n → ℂ) u)) =
        ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
              (BHW.os45FlatCommonChartSourceSide d n
                (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η u)) *
            ((((D.toZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) φ).1 : SchwartzNPoint d n) :
                NPointDomain d n → ℂ) u)) :
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
  let φ0 : SchwartzNPoint d n :=
    ((D.toZeroDiagonalCLM
      (1 : Equiv.Perm (Fin n)) φ).1 : SchwartzNPoint d n)
  have h0_minus_plus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d n
          (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η u ∈ Ωplus := by
    intro u hu
    simpa using h0_plus u hu
  have h0_plus_minus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d n
          (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u ∈ Ωminus := by
    intro u hu
    simpa using h0_minus u hu
  have hplus_pair :=
    D.tendsto_sourceSide_extendF_sideZeroDiagonalCLM_pair
      (d := d) OS lgc (1 : Equiv.Perm (Fin n))
      hΩplus_open (by simpa using hFplus_cont)
      hUsrc_open hUsrc_sub_K hKsrc η h0_plus h0_minus_plus
      φ hφ_compact hφU
  have hminus_pair :=
    D.tendsto_sourceSide_extendF_sideZeroDiagonalCLM_pair
      (d := d) OS lgc
      (P.τ.symm * (1 : Equiv.Perm (Fin n)))
      hΩminus_open (by simpa using hFminus_cont)
      hUsrc_open hUsrc_sub_K hKsrc η h0_plus_minus h0_minus
      φ hφ_compact hφU
  have hzero_integral' :
      (∫ u : NPointDomain d n,
        BHW.extendF (bvt_F OS lgc n)
          (BHW.os45QuarterTurnConfig (d := d) (n := n)
            (fun k => wickRotatePoint (u k))) *
          (φ0 : NPointDomain d n → ℂ) u) =
        ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ
              (BHW.os45QuarterTurnConfig (d := d) (n := n)
                (fun k => wickRotatePoint (u k)))) *
            (φ0 : NPointDomain d n → ℂ) u := by
    simpa [φ0] using hzero_pairing
  have hdiff := hplus_pair.1.sub hminus_pair.2
  simpa [φ0, hzero_integral'] using hdiff

/-- Difference form of the concrete Figure-2-4 source-side moving-test
transfer.

The hypothesis `hzero_eq` is the genuine local common-edge identification at
height zero.  This lemma only performs the checked analytic bookkeeping around
it: the two signed moving side-test integrals converge to the same zero-height
pairing, hence their difference tends to zero. -/
theorem OS45Figure24SourceCutoffData.tendsto_sourceSide_extendF_difference_zero_of_commonZero
    {hd : 2 ≤ d}
    {i : Fin n} {hi : i.val + 1 < n}
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    {Ωplus Ωminus : Set (Fin n → Fin (d + 1) → ℂ)}
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    (hFplus_cont :
      ContinuousOn
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n) z) Ωplus)
    (hFminus_cont :
      ContinuousOn
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm z)) Ωminus)
    {Usrc Ksrc : Set (NPointDomain d n)}
    (hUsrc_open : IsOpen Usrc)
    (hUsrc_sub_K : Usrc ⊆ Ksrc)
    (hKsrc : IsCompact Ksrc)
    (η : BHW.OS45FlatCommonChartReal d n)
    (h0_plus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d n
          (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u ∈ Ωplus)
    (h0_minus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d n
          (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η u ∈ Ωminus)
    (hzero_eq :
      ∀ u ∈ Ksrc,
        BHW.extendF (bvt_F OS lgc n)
            (BHW.os45FlatCommonChartSourceSide d n
              (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u) =
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
              (BHW.os45FlatCommonChartSourceSide d n
                (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η u)))
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact :
      HasCompactSupport
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφU :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45CommonEdgeFlatCLE d n
          (1 : Equiv.Perm (Fin n)) '' Usrc) :
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
  let φ0 : SchwartzNPoint d n :=
    ((D.toZeroDiagonalCLM
      (1 : Equiv.Perm (Fin n)) φ).1 : SchwartzNPoint d n)
  have hφ0K : tsupport (φ0 : NPointDomain d n → ℂ) ⊆ Ksrc := by
    have hφ0U : tsupport (φ0 : NPointDomain d n → ℂ) ⊆ Usrc := by
      simpa [φ0, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM] using
        D.toSchwartzNPointCLM_tsupport_subset_image
          (1 : Equiv.Perm (Fin n)) φ hφU
    exact hφ0U.trans hUsrc_sub_K
  have hzero_integral :
      (∫ u : NPointDomain d n,
        BHW.extendF (bvt_F OS lgc n)
          (BHW.os45FlatCommonChartSourceSide d n
            (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u) *
          (φ0 : NPointDomain d n → ℂ) u) =
        ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
              (BHW.os45FlatCommonChartSourceSide d n
                (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η u)) *
            (φ0 : NPointDomain d n → ℂ) u := by
    refine MeasureTheory.integral_congr_ae ?_
    exact Filter.Eventually.of_forall fun u => by
      by_cases hu : u ∈ Ksrc
      · exact congrArg (fun z : ℂ => z * (φ0 : NPointDomain d n → ℂ) u)
          (hzero_eq u hu)
      · have hφ0_zero : (φ0 : NPointDomain d n → ℂ) u = 0 :=
          image_eq_zero_of_notMem_tsupport (fun hu0 => hu (hφ0K hu0))
        simp [hφ0_zero]
  exact
    D.tendsto_sourceSide_extendF_difference_zero_of_zeroHeightPairing
      (d := d) OS lgc hΩplus_open hΩminus_open
      hFplus_cont hFminus_cont hUsrc_open hUsrc_sub_K hKsrc η
      h0_plus h0_minus φ hφ_compact hφU
      (by simpa [φ0] using hzero_integral)

/-- Source-common-edge form of
`OS45Figure24SourceCutoffData.tendsto_sourceSide_extendF_difference_zero_of_commonZero`.

This is the shape supplied by the OS45/Ruelle common-edge seed: equality of
the adjacent and ordinary pulled real branches on the local source window. -/
theorem OS45Figure24SourceCutoffData.tendsto_sourceSide_extendF_difference_zero_of_sourceCommonEdge
    {hd : 2 ≤ d}
    {i : Fin n} {hi : i.val + 1 < n}
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    {Ωplus Ωminus : Set (Fin n → Fin (d + 1) → ℂ)}
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    (hFplus_cont :
      ContinuousOn
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n) z) Ωplus)
    (hFminus_cont :
      ContinuousOn
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm z)) Ωminus)
    {Usrc Ksrc : Set (NPointDomain d n)}
    (hUsrc_open : IsOpen Usrc)
    (hUsrc_sub_K : Usrc ⊆ Ksrc)
    (hKsrc : IsCompact Ksrc)
    (η : BHW.OS45FlatCommonChartReal d n)
    (h0_plus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d n
          (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u ∈ Ωplus)
    (h0_minus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d n
          (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η u ∈ Ωminus)
    (hsource :
      ∀ u ∈ Ksrc,
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) =
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (1 : Equiv.Perm (Fin n))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)))
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact :
      HasCompactSupport
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφU :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45CommonEdgeFlatCLE d n
          (1 : Equiv.Perm (Fin n)) '' Usrc) :
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
  refine
    D.tendsto_sourceSide_extendF_difference_zero_of_commonZero
      (d := d) OS lgc hΩplus_open hΩminus_open
      hFplus_cont hFminus_cont hUsrc_open hUsrc_sub_K hKsrc η
      h0_plus h0_minus ?_ φ hφ_compact hφU
  intro u hu
  let z0 : Fin n → Fin (d + 1) → ℂ :=
    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
      (BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) u))
  have hz0 :
      z0 =
        BHW.os45QuarterTurnConfig (d := d) (n := n)
          (fun k => wickRotatePoint (u k)) := by
    simpa [z0] using
      BHW.os45QuarterTurnCLE_symm_realEmbed_commonEdge_eq_wick
        (d := d) (n := n) (1 : Equiv.Perm (Fin n)) u
  have h := (hsource u hu).symm
  change
    BHW.extendF (bvt_F OS lgc n)
        (BHW.permAct (d := d) (1 : Equiv.Perm (Fin n)).symm z0) =
      BHW.extendF (bvt_F OS lgc n)
        (BHW.permAct (d := d)
          (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm z0) at h
  simpa [BHW.os45FlatCommonChartSourceSide_zero, z0, hz0] using h

/-- Source-representation form of the moving source-side difference theorem.

This is the OS-I `(4.12)`--`(4.14)` input shape used on the active theorem-2
path: the adjacent-minus-ordinary horizontal source branch represents the zero
distribution on the source collar.  The proof feeds that representation to the
existing zero-height pairing slot for the concrete cutoff-pulled source test,
then reuses the checked moving-test bookkeeping. -/
theorem OS45Figure24SourceCutoffData.tendsto_sourceSide_extendF_difference_zero_of_sourceRepresentsOn
    {hd : 2 ≤ d}
    {i : Fin n} {hi : i.val + 1 < n}
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    {Ωplus Ωminus : Set (Fin n → Fin (d + 1) → ℂ)}
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    (hFplus_cont :
      ContinuousOn
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n) z) Ωplus)
    (hFminus_cont :
      ContinuousOn
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm z)) Ωminus)
    {Usrc Ksrc : Set (NPointDomain d n)}
    (hUsrc_open : IsOpen Usrc)
    (hUsrc_sub_K : Usrc ⊆ Ksrc)
    (hKsrc : IsCompact Ksrc)
    (η : BHW.OS45FlatCommonChartReal d n)
    (h0_plus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d n
          (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u ∈ Ωplus)
    (h0_minus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d n
          (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η u ∈ Ωminus)
    (hrep :
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
                  (1 : Equiv.Perm (Fin n)) u))) Usrc)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact :
      HasCompactSupport
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφU :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45CommonEdgeFlatCLE d n
          (1 : Equiv.Perm (Fin n)) '' Usrc) :
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
  let φ0 : SchwartzNPoint d n :=
    ((D.toZeroDiagonalCLM
      (1 : Equiv.Perm (Fin n)) φ).1 : SchwartzNPoint d n)
  let Fplus : NPointDomain d n → ℂ := fun u =>
    BHW.extendF (bvt_F OS lgc n)
      (BHW.os45FlatCommonChartSourceSide d n
        (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u)
  let Fminus : NPointDomain d n → ℂ := fun u =>
    BHW.extendF (bvt_F OS lgc n)
      (BHW.permAct (d := d)
        (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
        (BHW.os45FlatCommonChartSourceSide d n
          (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η u))
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
  have hφ0_compact :
      HasCompactSupport (φ0 : NPointDomain d n → ℂ) := by
    simpa [φ0, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM] using
      D.toSchwartzNPointCLM_hasCompactSupport
        (1 : Equiv.Perm (Fin n)) φ
  have hφ0U : tsupport (φ0 : NPointDomain d n → ℂ) ⊆ Usrc := by
    simpa [φ0, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM] using
      D.toSchwartzNPointCLM_tsupport_subset_image
        (1 : Equiv.Perm (Fin n)) φ hφU
  have hrep_zero :
      ∫ u : NPointDomain d n, Ghoriz u * (φ0 : NPointDomain d n → ℂ) u = 0 := by
    have h :=
      hrep φ0 ⟨hφ0_compact, hφ0U⟩
    simpa [Ghoriz] using h.symm
  have hFplus_cont_source : ContinuousOn Fplus Usrc := by
    exact hFplus_cont.comp
      (BHW.continuous_os45FlatCommonChartSourceSide_fixed_eps
        (d := d) (n := n)
        (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η).continuousOn
      (by
        intro u hu
        exact h0_plus u (hUsrc_sub_K hu))
  have hFminus_cont_source : ContinuousOn Fminus Usrc := by
    have hmap :
        Continuous fun u : NPointDomain d n =>
          BHW.os45FlatCommonChartSourceSide d n
            (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η u :=
      BHW.continuous_os45FlatCommonChartSourceSide_fixed_eps
        (d := d) (n := n)
        (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η
    exact hFminus_cont.comp hmap.continuousOn
      (by
        intro u hu
        exact h0_minus u (hUsrc_sub_K hu))
  have hFplus_int :
      Integrable (fun u : NPointDomain d n =>
        Fplus u * (φ0 : NPointDomain d n → ℂ) u) :=
    SCV.integrable_continuousOn_mul_schwartz_of_supportsInOpen
      (H := Fplus) (ψ := φ0) (U := Usrc)
      hUsrc_open hFplus_cont_source ⟨hφ0_compact, hφ0U⟩
  have hFminus_int :
      Integrable (fun u : NPointDomain d n =>
        Fminus u * (φ0 : NPointDomain d n → ℂ) u) :=
    SCV.integrable_continuousOn_mul_schwartz_of_supportsInOpen
      (H := Fminus) (ψ := φ0) (U := Usrc)
      hUsrc_open hFminus_cont_source ⟨hφ0_compact, hφ0U⟩
  have hdiff_zero :
      ∫ u : NPointDomain d n,
        (Fminus u - Fplus u) * (φ0 : NPointDomain d n → ℂ) u = 0 := by
    calc
      ∫ u : NPointDomain d n,
          (Fminus u - Fplus u) * (φ0 : NPointDomain d n → ℂ) u
          = ∫ u : NPointDomain d n,
              Ghoriz u * (φ0 : NPointDomain d n → ℂ) u := by
            refine MeasureTheory.integral_congr_ae
              (Filter.Eventually.of_forall ?_)
            intro u
            by_cases hu : u ∈ Usrc
            · let z0 : Fin n → Fin (d + 1) → ℂ :=
                (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
                  (BHW.realEmbed
                    (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                      (1 : Equiv.Perm (Fin n)) u))
              dsimp [Fminus, Fplus]
              rw [BHW.os45FlatCommonChartSourceSide_zero_eq_commonEdge,
                BHW.os45FlatCommonChartSourceSide_zero_eq_commonEdge]
              change
                (BHW.extendF (bvt_F OS lgc n)
                    (BHW.permAct (d := d)
                      (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm z0) -
                  BHW.extendF (bvt_F OS lgc n)
                    z0) *
                    (φ0 : NPointDomain d n → ℂ) u =
                  Ghoriz u * (φ0 : NPointDomain d n → ℂ) u
              simp [Ghoriz, BHW.os45PulledRealBranch, z0]
            · have hφ0_zero : (φ0 : NPointDomain d n → ℂ) u = 0 :=
                image_eq_zero_of_notMem_tsupport
                  (fun hu0 => hu (hφ0U hu0))
              simp [hφ0_zero]
      _ = 0 := hrep_zero
  have hzero_pairing :
      (∫ u : NPointDomain d n,
        BHW.extendF (bvt_F OS lgc n)
          (BHW.os45FlatCommonChartSourceSide d n
            (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u) *
          (φ0 : NPointDomain d n → ℂ) u) =
        ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
              (BHW.os45FlatCommonChartSourceSide d n
                (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η u)) *
            (φ0 : NPointDomain d n → ℂ) u := by
    have hsub :
        (∫ u : NPointDomain d n,
          Fminus u * (φ0 : NPointDomain d n → ℂ) u) -
          ∫ u : NPointDomain d n,
            Fplus u * (φ0 : NPointDomain d n → ℂ) u = 0 := by
      calc
        (∫ u : NPointDomain d n,
          Fminus u * (φ0 : NPointDomain d n → ℂ) u) -
          ∫ u : NPointDomain d n,
            Fplus u * (φ0 : NPointDomain d n → ℂ) u
            =
          ∫ u : NPointDomain d n,
            Fminus u * (φ0 : NPointDomain d n → ℂ) u -
              Fplus u * (φ0 : NPointDomain d n → ℂ) u := by
              exact (MeasureTheory.integral_sub hFminus_int hFplus_int).symm
        _ = ∫ u : NPointDomain d n,
            (Fminus u - Fplus u) *
              (φ0 : NPointDomain d n → ℂ) u := by
              refine MeasureTheory.integral_congr_ae
                (Filter.Eventually.of_forall ?_)
              intro u
              ring
        _ = 0 := hdiff_zero
    have hminus_eq_plus :
        (∫ u : NPointDomain d n,
          Fminus u * (φ0 : NPointDomain d n → ℂ) u) =
          ∫ u : NPointDomain d n,
            Fplus u * (φ0 : NPointDomain d n → ℂ) u :=
      sub_eq_zero.mp hsub
    simpa [Fplus, Fminus] using hminus_eq_plus.symm
  exact
    D.tendsto_sourceSide_extendF_difference_zero_of_zeroHeightPairing
      (d := d) OS lgc hΩplus_open hΩminus_open
      hFplus_cont hFminus_cont hUsrc_open hUsrc_sub_K hKsrc η
      h0_plus h0_minus φ hφ_compact hφU
      (by simpa [φ0] using hzero_pairing)

/-- Flat side-branch/source pullback from an already proved source-side moving
difference limit.

This is the coordinate/Jacobian part of the OS45 Figure-2-4 moving-test
comparison.  The input `hsrc` is the source-current comparison; this theorem
only transfers it to the flat side branches using the checked side-support and
branch/source pullback lemmas. -/
theorem OS45Figure24SourceCutoffData.tendsto_flatCommonChart_sideBranch_difference_zero_of_sourceSideDifference
    {hd : 2 ≤ d}
    {i : Fin n} {hi : i.val + 1 < n}
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
    (hsrc :
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
        (𝓝 0)) :
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
  let J : ℂ := (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ)
  have hscaled :
      Tendsto
        (fun ε : ℝ =>
          J *
            ((∫ u : NPointDomain d n,
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
                    SchwartzNPoint d n) : NPointDomain d n → ℂ) u)))
        (𝓝[Set.Ioi 0] (0 : ℝ))
        (𝓝 0) := by
    have hJ :
        Tendsto (fun _ : ℝ => J)
          (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 J) := tendsto_const_nhds
    have hmul := hJ.mul hsrc
    simpa [J] using hmul
  refine Tendsto.congr' ?_ hscaled
  filter_upwards [hside_event, hinteg] with ε hsupport hinteg
  have hplus_pull :
      (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (fun a =>
              (x a : ℂ) +
                ((((1 : ℝ) * ε) • η) a : ℂ) * Complex.I) *
            φ x)
        =
      J *
        ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.os45FlatCommonChartSourceSide d n
              (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η u) *
            ((((D.toSideZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
                SchwartzNPoint d n) : NPointDomain d n → ℂ) u) := by
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
  have hminus_pull :
      (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (fun a =>
              (x a : ℂ) +
                ((((-1 : ℝ) * ε) • η) a : ℂ) * Complex.I) *
            φ x)
        =
      J *
        ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
              (BHW.os45FlatCommonChartSourceSide d n
                (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η u)) *
            ((((D.toSideZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
                SchwartzNPoint d n) : NPointDomain d n → ℂ) u) := by
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
  rw [hplus_pull, hminus_pull]
  ring

/-- Flat side-branch form of the zero-height source-pairing comparison.

This connects the OS-I `(4.14)` pairing leaf to the flat side branches.  The
remaining mathematical input is exactly the zero-height source pairing equality
for the pulled-back test. -/
theorem OS45Figure24SourceCutoffData.tendsto_flatCommonChart_sideBranch_difference_zero_of_zeroHeightPairing
    {hd : 2 ≤ d}
    {i : Fin n} {hi : i.val + 1 < n}
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    {Ωplus Ωminus : Set (Fin n → Fin (d + 1) → ℂ)}
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    (hFplus_cont :
      ContinuousOn
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n) z) Ωplus)
    (hFminus_cont :
      ContinuousOn
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm z)) Ωminus)
    {Usrc Ksrc : Set (NPointDomain d n)}
    (hUsrc_open : IsOpen Usrc)
    (hUsrc_sub_K : Usrc ⊆ Ksrc)
    (hKsrc : IsCompact Ksrc)
    (η : BHW.OS45FlatCommonChartReal d n)
    (hηC : η ∈ BHW.os45FlatCommonChartCone d n)
    (h0_plus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d n
          (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u ∈ Ωplus)
    (h0_minus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d n
          (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η u ∈ Ωminus)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact :
      HasCompactSupport
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)))
    (hφU :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45CommonEdgeFlatCLE d n
          (1 : Equiv.Perm (Fin n)) '' Usrc)
    (hzero_pairing :
      (∫ u : NPointDomain d n,
        BHW.extendF (bvt_F OS lgc n)
          (BHW.os45FlatCommonChartSourceSide d n
            (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u) *
          ((((D.toZeroDiagonalCLM
            (1 : Equiv.Perm (Fin n)) φ).1 : SchwartzNPoint d n) :
              NPointDomain d n → ℂ) u)) =
        ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
              (BHW.os45FlatCommonChartSourceSide d n
                (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η u)) *
            ((((D.toZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) φ).1 : SchwartzNPoint d n) :
                NPointDomain d n → ℂ) u)) :
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
  have hsrc :=
    D.tendsto_sourceSide_extendF_difference_zero_of_zeroHeightPairing
      (d := d) OS lgc hΩplus_open hΩminus_open
      hFplus_cont hFminus_cont hUsrc_open hUsrc_sub_K hKsrc η
      h0_plus h0_minus φ hφ_compact hφU hzero_pairing
  exact
    D.tendsto_flatCommonChart_sideBranch_difference_zero_of_sourceSideDifference
      (d := d) OS lgc η hηC φ hφ_compact hφE hsrc

/-- Flat side-branch form of the source-side moving comparison.

This is the OS-I `(4.14)` moving-source transfer after applying the checked
Figure-2-4 branch/source pullback.  The hypotheses are the same local source
carrier data as
`OS45Figure24SourceCutoffData.tendsto_sourceSide_extendF_difference_zero_of_sourceCommonEdge`,
plus the ordinary flat support/cutoff assumptions needed to perform the
side-height pullback. -/
theorem OS45Figure24SourceCutoffData.tendsto_flatCommonChart_sideBranch_difference_zero_of_sourceCommonEdge
    {hd : 2 ≤ d}
    {i : Fin n} {hi : i.val + 1 < n}
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    {Ωplus Ωminus : Set (Fin n → Fin (d + 1) → ℂ)}
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    (hFplus_cont :
      ContinuousOn
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n) z) Ωplus)
    (hFminus_cont :
      ContinuousOn
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm z)) Ωminus)
    {Usrc Ksrc : Set (NPointDomain d n)}
    (hUsrc_open : IsOpen Usrc)
    (hUsrc_sub_K : Usrc ⊆ Ksrc)
    (hKsrc : IsCompact Ksrc)
    (η : BHW.OS45FlatCommonChartReal d n)
    (hηC : η ∈ BHW.os45FlatCommonChartCone d n)
    (h0_plus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d n
          (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u ∈ Ωplus)
    (h0_minus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d n
          (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η u ∈ Ωminus)
    (hsource :
      ∀ u ∈ Ksrc,
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) =
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (1 : Equiv.Perm (Fin n))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)))
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact :
      HasCompactSupport
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)))
    (hφU :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45CommonEdgeFlatCLE d n
          (1 : Equiv.Perm (Fin n)) '' Usrc) :
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
  have hsrc :=
    D.tendsto_sourceSide_extendF_difference_zero_of_sourceCommonEdge
      (d := d) OS lgc hΩplus_open hΩminus_open
      hFplus_cont hFminus_cont hUsrc_open hUsrc_sub_K hKsrc η
      h0_plus h0_minus hsource φ hφ_compact hφU
  exact
    D.tendsto_flatCommonChart_sideBranch_difference_zero_of_sourceSideDifference
      (d := d) OS lgc η hηC φ hφ_compact hφE hsrc

/-- Flat side-branch form of the source-representation moving comparison.

This is the flat-coordinate pullback of
`OS45Figure24SourceCutoffData.tendsto_sourceSide_extendF_difference_zero_of_sourceRepresentsOn`.
It keeps the paper-facing input as the local zero source representation and uses
only the checked source-to-flat Jacobian and side-support machinery. -/
theorem OS45Figure24SourceCutoffData.tendsto_flatCommonChart_sideBranch_difference_zero_of_sourceRepresentsOn
    {hd : 2 ≤ d}
    {i : Fin n} {hi : i.val + 1 < n}
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (D : BHW.OS45Figure24SourceCutoffData P)
    {Ωplus Ωminus : Set (Fin n → Fin (d + 1) → ℂ)}
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    (hFplus_cont :
      ContinuousOn
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n) z) Ωplus)
    (hFminus_cont :
      ContinuousOn
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d)
              (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm z)) Ωminus)
    {Usrc Ksrc : Set (NPointDomain d n)}
    (hUsrc_open : IsOpen Usrc)
    (hUsrc_sub_K : Usrc ⊆ Ksrc)
    (hKsrc : IsCompact Ksrc)
    (η : BHW.OS45FlatCommonChartReal d n)
    (hηC : η ∈ BHW.os45FlatCommonChartCone d n)
    (h0_plus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d n
          (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u ∈ Ωplus)
    (h0_minus :
      ∀ u ∈ Ksrc,
        BHW.os45FlatCommonChartSourceSide d n
          (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η u ∈ Ωminus)
    (hrep :
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
                  (1 : Equiv.Perm (Fin n)) u))) Usrc)
    (φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hφ_compact :
      HasCompactSupport
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hφE :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45FlatCommonChartEdgeSet d n P
          (1 : Equiv.Perm (Fin n)))
    (hφU :
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
        BHW.os45CommonEdgeFlatCLE d n
          (1 : Equiv.Perm (Fin n)) '' Usrc) :
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
  have hsrc :=
    D.tendsto_sourceSide_extendF_difference_zero_of_sourceRepresentsOn
      (d := d) OS lgc hΩplus_open hΩminus_open
      hFplus_cont hFminus_cont hUsrc_open hUsrc_sub_K hKsrc η
      h0_plus h0_minus hrep φ hφ_compact hφU
  exact
    D.tendsto_flatCommonChart_sideBranch_difference_zero_of_sourceSideDifference
      (d := d) OS lgc η hηC φ hφ_compact hφE hsrc

end BHW
