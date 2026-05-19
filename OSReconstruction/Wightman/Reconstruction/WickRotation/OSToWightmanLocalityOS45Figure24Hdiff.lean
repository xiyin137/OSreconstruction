import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45Figure24Seed
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45SourceSideMoving

/-!
# OS45 Figure 2-4 Hdiff Producer

This downstream companion is the Lean entry point for the direct
`os45CommonEdge_localFigure24DifferenceGerm_of_OSI45` proof.  It contains only
proof-local algebra and the eventual Hdiff producer; it does not wrap an
assumed difference germ or common-boundary CLM.
-/

noncomputable section

open Complex Topology MeasureTheory Filter

namespace BHW

variable {d n : ℕ}

/-- Compact-support collar for the fixed flat translated-test integrand.

This is the analytic support leaf needed by the fixed source-side scalar
cancellation: on the compact support of the fixed flat test, a sufficiently
small real-plus-imaginary side displacement stays in the same flat branch
domain. -/
private theorem os45FlatCommonChart_fixedTranslatedTest_integrable_eventually
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (σ : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (ψ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ)
    (hψ_compact : HasCompactSupport
      (ψ : BHW.OS45FlatCommonChartReal d n → ℂ))
    (hψ_omega :
      ∀ x ∈ tsupport (ψ : BHW.OS45FlatCommonChartReal d n → ℂ),
        (fun j => (x j : ℂ)) ∈
          BHW.os45FlatCommonChartOmega d n σ) :
    ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
      Integrable
        (fun x : BHW.OS45FlatCommonChartReal d n =>
          BHW.os45FlatCommonChartBranch d n OS lgc σ
            (fun j =>
              ((x + (sgn * ε) • η) j : ℂ) +
                (((sgn * ε) • η) j : ℂ) * Complex.I) *
          (SCV.translateSchwartz (-(sgn * ε) • η) ψ)
            (x + (sgn * ε) • η)) := by
  classical
  let R := BHW.OS45FlatCommonChartReal d n
  let Ω : Set (BHW.OS45FlatCommonChartSpace d n) :=
    BHW.os45FlatCommonChartOmega d n σ
  let S : Set R := tsupport (ψ : R → ℂ)
  let arg : R × ℝ → BHW.OS45FlatCommonChartSpace d n := fun p =>
    fun j =>
      (p.1 j : ℂ) +
        ((((sgn * p.2) • η) j : ℂ) +
          (((sgn * p.2) • η) j : ℂ) * Complex.I)
  let zeroEdge : Set (R × ℝ) := S ×ˢ ({0} : Set ℝ)
  let sideWindow : Set (R × ℝ) := {p | arg p ∈ Ω}
  have harg_cont : Continuous arg := by
    dsimp [arg]
    fun_prop
  have hside_open : IsOpen sideWindow := by
    simpa [sideWindow, Ω] using
      (BHW.isOpen_os45FlatCommonChartOmega d n σ).preimage harg_cont
  have hS_compact : IsCompact S := by
    simpa [S] using hψ_compact.isCompact
  have hzero_compact : IsCompact zeroEdge :=
    hS_compact.prod isCompact_singleton
  have hzero_sub : zeroEdge ⊆ sideWindow := by
    rintro ⟨x, ε⟩ ⟨hxS, hε0⟩
    have hε : ε = 0 := by simpa using hε0
    subst ε
    simpa [sideWindow, arg, Ω, S] using hψ_omega x hxS
  obtain ⟨r, hr_pos, hr_sub⟩ :=
    hzero_compact.exists_thickening_subset_open hside_open hzero_sub
  filter_upwards
    [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hr_pos)]
    with ε hε_pos hε_lt
  let a : R := (sgn * ε) • η
  let UΩ : Set R := {x | (fun j => (x j : ℂ) +
    ((a j : ℂ) + (a j : ℂ) * Complex.I)) ∈ Ω}
  let H : R → ℂ := fun x =>
    BHW.os45FlatCommonChartBranch d n OS lgc σ
      (fun j => (x j : ℂ) + ((a j : ℂ) + (a j : ℂ) * Complex.I))
  have hdomain : S ⊆ UΩ := by
    intro x hxS
    have hε_pos' : 0 < ε := by simpa using hε_pos
    have hx_window : ((x, ε) : R × ℝ) ∈ sideWindow := by
      apply hr_sub
      rw [Metric.mem_thickening_iff]
      refine ⟨((x, (0 : ℝ)) : R × ℝ), ?_, ?_⟩
      · exact ⟨hxS, by simp⟩
      · simpa [Prod.dist_eq, Real.dist_eq, abs_of_nonneg hε_pos'.le] using
          ⟨hr_pos, hε_lt⟩
    simpa [sideWindow, UΩ, arg, Ω, a] using hx_window
  have hUΩ_open : IsOpen UΩ := by
    have hmap : Continuous (fun x : R =>
        fun j => (x j : ℂ) + ((a j : ℂ) + (a j : ℂ) * Complex.I)) := by
      fun_prop
    simpa [UΩ, Ω] using
      (BHW.isOpen_os45FlatCommonChartOmega d n σ).preimage hmap
  have hH_cont : ContinuousOn H UΩ := by
    have hmap : Continuous (fun x : R =>
        fun j => (x j : ℂ) + ((a j : ℂ) + (a j : ℂ) * Complex.I)) := by
      fun_prop
    exact
      (BHW.differentiableOn_os45FlatCommonChartBranch
        d n OS lgc σ).continuousOn.comp
        hmap.continuousOn
        (by intro x hx; simpa [UΩ, Ω] using hx)
  have hHψ_cont : Continuous (fun x : R => H x * ψ x) := by
    have hψH :
        Continuous (fun x : R => ψ x * H x) :=
      SCV.continuous_mul_of_continuousOn_of_tsupport_subset_open
        hUΩ_open ψ.continuous
        (by simpa [S] using hdomain)
        hH_cont
    simpa [mul_comm] using hψH
  have hHψ_compact : HasCompactSupport (fun x : R => H x * ψ x) := by
    refine hψ_compact.mono' ?_
    intro x hx
    by_contra hxψ
    have hψx : ψ x = 0 := image_eq_zero_of_notMem_tsupport hxψ
    exact hx (by simp [hψx])
  have hHψ_int : Integrable (fun x : R => H x * ψ x) :=
    hHψ_cont.integrable_of_hasCompactSupport hHψ_compact
  simpa [H, a, SCV.translateSchwartz_apply, Pi.add_apply, Pi.smul_apply,
    add_assoc, mul_assoc] using hHψ_int

/-- Fixed-test boundary value for the ordinary OS-I `(4.1)` branch written in
the `extendF` model used by the Figure-2-4 charts. -/
private theorem ordinary41_fixed_test_boundaryValue_extendF
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (ψ : SchwartzNPoint d n)
    (η : Fin n → Fin (d + 1) → ℝ)
    (hη : InForwardCone d n η) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d n,
        BHW.extendF (bvt_F OS lgc n)
          (fun k μ =>
            (x k μ : ℂ) + (ε : ℂ) * (η k μ : ℂ) * Complex.I) *
        ψ x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (bvt_W OS lgc n ψ)) := by
  have hbvt :=
    bvt_boundary_values (d := d) OS lgc n ψ η hη
  refine hbvt.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  apply integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro x
  have hη_abs : η ∈ ForwardConeAbs d n :=
    (inForwardCone_iff_mem_forwardConeAbs (d := d) (n := n) η).1 hη
  have hscaled_abs : ε • η ∈ ForwardConeAbs d n :=
    forwardConeAbs_smul d n ε hε η hη_abs
  have hz :
      (fun k μ =>
        (x k μ : ℂ) + (ε : ℂ) * (η k μ : ℂ) * Complex.I) ∈
        BHW.ForwardTube d n := by
    have hz_root :
        (fun k μ =>
          (x k μ : ℂ) + (ε : ℂ) * (η k μ : ℂ) * Complex.I) ∈
          _root_.ForwardTube d n := by
      rw [_root_.forwardTube_eq_imPreimage, Set.mem_setOf_eq]
      convert hscaled_abs using 1
      ext k μ
      simp [Pi.smul_apply, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im]
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using hz_root
  have hF_holo :
      DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      bvt_F_holomorphic (d := d) OS lgc n
  have hF_real_inv :
      ∀ (Λ : LorentzLieGroup.RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
        bvt_F OS lgc n
          (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) =
          bvt_F OS lgc n z := by
    intro Λ z hz
    have hΛz : BHW.complexLorentzAction (ComplexLorentzGroup.ofReal Λ) z ∈
        BHW.ForwardTube d n :=
      BHW.ofReal_preserves_forwardTube Λ z hz
    have hcinv :=
      bvt_F_complexLorentzInvariant_forwardTube
        (d := d) OS lgc n (ComplexLorentzGroup.ofReal Λ) z
        ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
        ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hΛz)
    simpa [BHW.complexLorentzAction] using hcinv
  have heq :
      BHW.extendF (bvt_F OS lgc n)
        (fun k μ =>
          (x k μ : ℂ) + (ε : ℂ) * (η k μ : ℂ) * Complex.I) =
        bvt_F OS lgc n
          (fun k μ =>
            (x k μ : ℂ) + (ε : ℂ) * (η k μ : ℂ) * Complex.I) := by
    exact BHW.extendF_eq_on_forwardTube n (bvt_F OS lgc n)
      hF_holo hF_real_inv
      _ hz
  exact congrArg (fun c : ℂ => c * ψ x) heq.symm

/-- Moving-test boundary value for the ordinary OS-I `(4.1)` branch written in
the `extendF` model.  This is the ordinary moving-test input for the later
side-height/source comparison; it is still before the OS45 source-side
pullback, so it does not assert a side-transfer theorem. -/
private theorem ordinary41_moving_boundaryValue_extendF
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (η : Fin n → Fin (d + 1) → ℝ)
    (hη : InForwardCone d n η)
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (εseq : α → ℝ)
    (hεseq : Filter.Tendsto εseq l (nhdsWithin 0 (Set.Ioi 0)))
    {fseq : α → SchwartzNPoint d n}
    {f0 : SchwartzNPoint d n}
    (hfseq : Filter.Tendsto fseq l (nhds f0)) :
    Filter.Tendsto
      (fun a : α => ∫ x : NPointDomain d n,
        BHW.extendF (bvt_F OS lgc n)
          (fun k μ =>
            (x k μ : ℂ) + (εseq a : ℂ) *
              (η k μ : ℂ) * Complex.I) *
        fseq a x)
      l
      (nhds (bvt_W OS lgc n f0)) := by
  have hbvt :=
    bvt_boundary_values_moving
      (d := d) OS lgc n η hη εseq hεseq hfseq
  refine hbvt.congr' ?_
  have hpos : ∀ᶠ a in l, εseq a ∈ Set.Ioi (0 : ℝ) :=
    hεseq.eventually self_mem_nhdsWithin
  filter_upwards [hpos] with a ha
  apply integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro x
  have hη_abs : η ∈ ForwardConeAbs d n :=
    (inForwardCone_iff_mem_forwardConeAbs (d := d) (n := n) η).1 hη
  have hscaled_abs : εseq a • η ∈ ForwardConeAbs d n :=
    forwardConeAbs_smul d n (εseq a) ha η hη_abs
  have hz :
      (fun k μ =>
        (x k μ : ℂ) + (εseq a : ℂ) *
          (η k μ : ℂ) * Complex.I) ∈
        BHW.ForwardTube d n := by
    have hz_root :
        (fun k μ =>
          (x k μ : ℂ) + (εseq a : ℂ) *
            (η k μ : ℂ) * Complex.I) ∈
          _root_.ForwardTube d n := by
      rw [_root_.forwardTube_eq_imPreimage, Set.mem_setOf_eq]
      convert hscaled_abs using 1
      ext k μ
      simp [Pi.smul_apply, Complex.add_im, Complex.ofReal_im,
        Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im]
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using hz_root
  have hF_holo :
      DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      bvt_F_holomorphic (d := d) OS lgc n
  have hF_real_inv :
      ∀ (Λ : LorentzLieGroup.RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
        bvt_F OS lgc n
          (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) =
          bvt_F OS lgc n z := by
    intro Λ z hz
    have hΛz : BHW.complexLorentzAction (ComplexLorentzGroup.ofReal Λ) z ∈
        BHW.ForwardTube d n :=
      BHW.ofReal_preserves_forwardTube Λ z hz
    have hcinv :=
      bvt_F_complexLorentzInvariant_forwardTube
        (d := d) OS lgc n (ComplexLorentzGroup.ofReal Λ) z
        ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
        ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hΛz)
    simpa [BHW.complexLorentzAction] using hcinv
  have heq :
      BHW.extendF (bvt_F OS lgc n)
        (fun k μ =>
          (x k μ : ℂ) + (εseq a : ℂ) *
            (η k μ : ℂ) * Complex.I) =
        bvt_F OS lgc n
          (fun k μ =>
            (x k μ : ℂ) + (εseq a : ℂ) *
              (η k μ : ℂ) * Complex.I) := by
    exact BHW.extendF_eq_on_forwardTube n (bvt_F OS lgc n)
      hF_holo hF_real_inv _ hz
  exact congrArg (fun c : ℂ => c * fseq a x) heq.symm

/-- Fixed-test boundary value for the genuine raw OS-I `(4.12)` seed.

This is one of the two real side-height leaves used inside the eventual
`os45CommonEdge_localFigure24DifferenceGerm_of_OSI45` producer.  It proves the
raw adjacent seed limit directly from the selected OS boundary-value theorem
and the source-label change of variables; it does not introduce a transported
adjacent branch, `Wadj`, `Hdiff`, or a common-boundary packet. -/
private theorem raw412_fixed_test_boundaryValue
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (τ : Equiv.Perm (Fin n))
    (ψ : SchwartzNPoint d n)
    (η : Fin n → Fin (d + 1) → ℝ)
    (hητ : (fun k μ => η (τ k) μ) ∈ ForwardConeAbs d n) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d n,
        bvt_F OS lgc n
          (BHW.permAct (d := d) τ
            (fun k μ =>
              (x k μ : ℂ) + (ε : ℂ) * (η k μ : ℂ) * Complex.I)) *
        ψ x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (bvt_W OS lgc n
          (BHW.permuteSchwartz (d := d) τ.symm ψ))) := by
  let ητ : Fin n → Fin (d + 1) → ℝ :=
    fun k μ => η (τ k) μ
  let ψτ : SchwartzNPoint d n :=
    BHW.permuteSchwartz (d := d) τ.symm ψ
  have hbvt :
      Filter.Tendsto
        (fun ε : ℝ => ∫ y : NPointDomain d n,
          bvt_F OS lgc n
            (fun k μ =>
              (y k μ : ℂ) + (ε : ℂ) * (ητ k μ : ℂ) * Complex.I) *
          ψτ y)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (bvt_W OS lgc n ψτ)) := by
    exact bvt_boundary_values (d := d) OS lgc n ψτ ητ
      ((inForwardCone_iff_mem_forwardConeAbs (d := d) (n := n) ητ).2
        (by simpa [ητ] using hητ))
  refine hbvt.congr' ?_
  filter_upwards with ε
  have hperm :=
    BHW.integral_perm_eq_self (d := d) (n := n) τ
      (fun y : NPointDomain d n =>
        bvt_F OS lgc n
          (fun k μ =>
            (y k μ : ℂ) + (ε : ℂ) * (ητ k μ : ℂ) * Complex.I) *
        ψτ y)
  simpa [ητ, ψτ, BHW.permAct, BHW.permuteSchwartz_apply,
    Equiv.apply_symm_apply] using hperm.symm

/-- Moving-test boundary value for the genuine raw OS-I `(4.12)` seed.  This
is the adjacent moving-test input before terminal transport; the limit is the
permuted selected OS boundary functional, not a downstream deterministic
`extendF o permAct` branch. -/
private theorem raw412_moving_boundaryValue
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (τ : Equiv.Perm (Fin n))
    (η : Fin n → Fin (d + 1) → ℝ)
    (hητ : (fun k μ => η (τ k) μ) ∈ ForwardConeAbs d n)
    {α : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (εseq : α → ℝ)
    (hεseq : Filter.Tendsto εseq l (nhdsWithin 0 (Set.Ioi 0)))
    {fseq : α → SchwartzNPoint d n}
    {f0 : SchwartzNPoint d n}
    (hfseq : Filter.Tendsto fseq l (nhds f0)) :
    Filter.Tendsto
      (fun a : α => ∫ x : NPointDomain d n,
        bvt_F OS lgc n
          (BHW.permAct (d := d) τ
            (fun k μ =>
              (x k μ : ℂ) + (εseq a : ℂ) *
                (η k μ : ℂ) * Complex.I)) *
        fseq a x)
      l
      (nhds
        (bvt_W OS lgc n
          (BHW.permuteSchwartz (d := d) τ.symm f0))) := by
  let ητ : Fin n → Fin (d + 1) → ℝ :=
    fun k μ => η (τ k) μ
  let Lτ : SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      ((LinearEquiv.funCongrLeft ℝ
        (Fin (d + 1) → ℝ) τ.symm).toContinuousLinearEquiv)
  have hfseqτ :
      Filter.Tendsto (fun a : α => Lτ (fseq a)) l
        (nhds (Lτ f0)) :=
    (Lτ.continuous.tendsto f0).comp hfseq
  have hbvt :
      Filter.Tendsto
        (fun a : α => ∫ y : NPointDomain d n,
          bvt_F OS lgc n
            (fun k μ =>
              (y k μ : ℂ) + (εseq a : ℂ) *
                (ητ k μ : ℂ) * Complex.I) *
          (Lτ (fseq a)) y)
        l
        (nhds (bvt_W OS lgc n (Lτ f0))) := by
    exact bvt_boundary_values_moving (d := d) OS lgc n ητ
      ((inForwardCone_iff_mem_forwardConeAbs (d := d) (n := n) ητ).2
        (by simpa [ητ] using hητ))
      εseq hεseq hfseqτ
  have hfun :
      (fun a : α => ∫ y : NPointDomain d n,
        bvt_F OS lgc n
          (fun k μ =>
            (y k μ : ℂ) + (εseq a : ℂ) *
              (ητ k μ : ℂ) * Complex.I) *
        (Lτ (fseq a)) y)
      =ᶠ[l]
      (fun a : α => ∫ x : NPointDomain d n,
        bvt_F OS lgc n
          (BHW.permAct (d := d) τ
            (fun k μ =>
              (x k μ : ℂ) + (εseq a : ℂ) *
                (η k μ : ℂ) * Complex.I)) *
        fseq a x) := by
    filter_upwards with a
    have hperm :=
      BHW.integral_perm_eq_self (d := d) (n := n) τ
        (fun y : NPointDomain d n =>
          bvt_F OS lgc n
            (fun k μ =>
              (y k μ : ℂ) + (εseq a : ℂ) *
                (ητ k μ : ℂ) * Complex.I) *
          (Lτ (fseq a)) y)
    simpa [ητ, Lτ, BHW.permAct, BHW.permuteSchwartz_apply,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      Equiv.apply_symm_apply] using hperm.symm
  have hlim :
      bvt_W OS lgc n (Lτ f0) =
        bvt_W OS lgc n
          (BHW.permuteSchwartz (d := d) τ.symm f0) := by
    simp [Lτ, BHW.permuteSchwartz]
  simpa [hlim] using hbvt.congr' hfun

/-- Multiplying a zero-diagonal Schwartz test by a Schwartz scalar factor
preserves infinite-order vanishing on the coincidence locus.

This is the neutral local fact needed when the fixed selector partitions
`tsupport psi0Flat` and pulls each flat piece back to source variables. -/
private theorem VanishesToInfiniteOrderOnCoincidence.smulLeft_schwartzNPoint
    {d : ℕ} [NeZero d] {n : ℕ} {ψ f : SchwartzNPoint d n}
    (hf : VanishesToInfiniteOrderOnCoincidence f) :
    VanishesToInfiniteOrderOnCoincidence (SchwartzMap.smulLeftCLM ℂ ψ f) := by
  letI : Module ℝ ℂ := instInnerProductSpaceRealComplex.toModule
  intro k x hx
  have hfun :
      (((SchwartzMap.smulLeftCLM ℂ ψ f : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) =
        fun y : NPointDomain d n => ψ y * f y := by
    funext y
    simpa [smul_eq_mul] using
      (SchwartzMap.smulLeftCLM_apply_apply
        (g := ((ψ : SchwartzNPoint d n) : NPointDomain d n → ℂ))
        ψ.hasTemperateGrowth f y)
  have hle :=
    norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (ψ.smooth ⊤) (f.smooth ⊤) x
      (n := k) (by exact_mod_cast le_top)
  have hsum_zero :
      ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (ψ : NPointDomain d n → ℂ) x‖ *
          ‖iteratedFDeriv ℝ (k - i) (f : NPointDomain d n → ℂ) x‖ = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hfi :
        iteratedFDeriv ℝ (k - i) (f : NPointDomain d n → ℂ) x = 0 :=
      hf (k - i) x hx
    simp [hfi]
  have hnonneg :
      0 ≤ ‖iteratedFDeriv ℝ k
        (((SchwartzMap.smulLeftCLM ℂ ψ f : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) x‖ := norm_nonneg _
  have hzero_norm :
      ‖iteratedFDeriv ℝ k
        (((SchwartzMap.smulLeftCLM ℂ ψ f : SchwartzNPoint d n) :
          NPointDomain d n → ℂ)) x‖ = 0 := by
    apply le_antisymm
    · rw [hfun]
      calc
        ‖iteratedFDeriv ℝ k (fun y : NPointDomain d n => ψ y * f y) x‖
            ≤ ∑ i ∈ Finset.range (k + 1),
                (k.choose i : ℝ) *
                  ‖iteratedFDeriv ℝ i
                    (ψ : NPointDomain d n → ℂ) x‖ *
                  ‖iteratedFDeriv ℝ (k - i)
                    (f : NPointDomain d n → ℂ) x‖ := by
              simpa [smul_eq_mul] using hle
        _ = 0 := hsum_zero
    · exact hnonneg
  exact norm_eq_zero.mp hzero_norm

private theorem finite_pointed_eqOn_nat
    {E F : Type*} [TopologicalSpace E]
    {z0 : E} (N : ℕ → Set E) (f : ℕ → E → F) :
    ∀ len : ℕ,
      (∀ j, j ≤ len → IsOpen (N j)) →
      (∀ j, j ≤ len → z0 ∈ N j) →
      (∀ j, j < len →
        ∃ W : Set E,
          IsOpen W ∧ z0 ∈ W ∧ W ⊆ N j ∩ N (j + 1) ∧
          Set.EqOn (f j) (f (j + 1)) W) →
      ∃ W : Set E,
        IsOpen W ∧ z0 ∈ W ∧ W ⊆ N 0 ∩ N len ∧
        Set.EqOn (f 0) (f len) W
  | 0, hN_open, hzN, _hstep => by
      refine ⟨N 0, hN_open 0 le_rfl, hzN 0 le_rfl, ?_, ?_⟩
      · intro z hz
        exact ⟨hz, hz⟩
      · intro _z _hz
        rfl
  | len + 1, hN_open, hzN, hstep => by
      obtain ⟨Wprev, hWprev_open, hzWprev, hWprev_sub, hWprev_eq⟩ :=
        finite_pointed_eqOn_nat (N := N) (f := f) len
          (fun j hj => hN_open j (Nat.le_trans hj (Nat.le_succ len)))
          (fun j hj => hzN j (Nat.le_trans hj (Nat.le_succ len)))
          (fun j hj => hstep j (Nat.lt_trans hj (Nat.lt_succ_self len)))
      obtain ⟨Wedge, hWedge_open, hzWedge, hWedge_sub, hWedge_eq⟩ :=
        hstep len (Nat.lt_succ_self len)
      refine
        ⟨Wprev ∩ Wedge, hWprev_open.inter hWedge_open,
          ⟨hzWprev, hzWedge⟩, ?_, ?_⟩
      · intro z hz
        exact ⟨(hWprev_sub hz.1).1, (hWedge_sub hz.2).2⟩
      · intro z hz
        exact (hWprev_eq hz.1).trans (hWedge_eq hz.2)

private theorem finite_pointed_eqOn_fin
    {E F : Type*} [TopologicalSpace E]
    {z0 : E} {len : ℕ}
    (N : Fin (len + 1) → Set E) (f : Fin (len + 1) → E → F)
    (hN_open : ∀ j, IsOpen (N j))
    (hzN : ∀ j, z0 ∈ N j)
    (hstep :
      ∀ j : Fin len,
        ∃ W : Set E,
          IsOpen W ∧ z0 ∈ W ∧
          W ⊆ N (Fin.castSucc j) ∩ N (Fin.succ j) ∧
          Set.EqOn (f (Fin.castSucc j)) (f (Fin.succ j)) W) :
    ∃ W : Set E,
      IsOpen W ∧ z0 ∈ W ∧ W ⊆ N 0 ∩ N (Fin.last len) ∧
      Set.EqOn (f 0) (f (Fin.last len)) W := by
  classical
  let Nnat : ℕ → Set E := fun j =>
    if h : j ≤ len then N ⟨j, Nat.lt_succ_of_le h⟩ else ∅
  let fnat : ℕ → E → F := fun j =>
    if h : j ≤ len then f ⟨j, Nat.lt_succ_of_le h⟩ else f 0
  obtain ⟨W, hW_open, hzW, hW_sub, hW_eq⟩ :=
    finite_pointed_eqOn_nat (N := Nnat) (f := fnat) len
      (fun j hj => by
        dsimp [Nnat]
        rw [dif_pos hj]
        exact hN_open ⟨j, Nat.lt_succ_of_le hj⟩)
      (fun j hj => by
        dsimp [Nnat]
        rw [dif_pos hj]
        exact hzN ⟨j, Nat.lt_succ_of_le hj⟩)
      (fun j hj => by
        have hj_le : j ≤ len := Nat.le_of_lt hj
        have hjs_le : j + 1 ≤ len := Nat.succ_le_of_lt hj
        rcases hstep ⟨j, hj⟩ with
          ⟨Wj, hWj_open, hzWj, hWj_sub, hWj_eq⟩
        refine ⟨Wj, hWj_open, hzWj, ?_, ?_⟩
        · simpa [Nnat, hj_le, hjs_le] using hWj_sub
        · simpa [fnat, hj_le, hjs_le] using hWj_eq)
  refine ⟨W, hW_open, hzW, ?_, ?_⟩
  · simpa [Nnat] using hW_sub
  · simpa [fnat] using hW_eq

private structure PointedSeedEdge
    {E F : Type*} [TopologicalSpace E]
    (z0 : E) (N₁ N₂ : Set E) (f₁ f₂ : E → F) where
  W : Set E
  W_open : IsOpen W
  z0_mem : z0 ∈ W
  W_sub : W ⊆ N₁ ∩ N₂
  eqOn : Set.EqOn f₁ f₂ W

private def PointedSeedEdge.symm
    {E F : Type*} [TopologicalSpace E]
    {z0 : E} {N₁ N₂ : Set E} {f₁ f₂ : E → F}
    (h : PointedSeedEdge z0 N₁ N₂ f₁ f₂) :
    PointedSeedEdge z0 N₂ N₁ f₂ f₁ := by
  exact
    { W := h.W
      W_open := h.W_open
      z0_mem := h.z0_mem
      W_sub := by
        intro z hz
        exact ⟨(h.W_sub hz).2, (h.W_sub hz).1⟩
      eqOn := by
        intro z hz
        exact (h.eqOn hz).symm }

private theorem pointed_seed_gallery_endpoint_seed
    {E F : Type*} [TopologicalSpace E]
    {z0 : E} {len : ℕ}
    (N : Fin (len + 1) → Set E) (f : Fin (len + 1) → E → F)
    (hN_open : ∀ j, IsOpen (N j))
    (hzN : ∀ j, z0 ∈ N j)
    (hstep :
      ∀ j : Fin len,
        PointedSeedEdge z0
          (N (Fin.castSucc j)) (N (Fin.succ j))
          (f (Fin.castSucc j)) (f (Fin.succ j))) :
    ∃ W : Set E,
      IsOpen W ∧ z0 ∈ W ∧ W ⊆ N 0 ∩ N (Fin.last len) ∧
      Set.EqOn (f 0) (f (Fin.last len)) W :=
  finite_pointed_eqOn_fin N f hN_open hzN
    (fun j =>
      let E := hstep j
      ⟨E.W, E.W_open, E.z0_mem, E.W_sub, E.eqOn⟩)

private structure PointedMetricBranchChart
    (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] where
  center : E
  radius : ℝ
  radius_pos : 0 < radius
  branch : E → F
  holo : DifferentiableOn ℂ branch (Metric.ball center radius)

private def PointedMetricBranchChart.carrier
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A : PointedMetricBranchChart E F) : Set E :=
  Metric.ball A.center A.radius

private theorem PointedMetricBranchChart.carrier_open
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A : PointedMetricBranchChart E F) :
    IsOpen A.carrier := by
  simp [PointedMetricBranchChart.carrier]

private theorem PointedMetricBranchChart.center_mem
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A : PointedMetricBranchChart E F) :
    A.center ∈ A.carrier := by
  simpa [PointedMetricBranchChart.carrier] using
    Metric.mem_ball_self (x := A.center) A.radius_pos

private theorem PointedMetricBranchChart.restrict_center
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A : PointedMetricBranchChart E F)
    {z0 : E} (hz0 : z0 ∈ A.carrier) :
    ∃ A0 : PointedMetricBranchChart E F,
      A0.center = z0 ∧
      A0.carrier ⊆ A.carrier ∧
      Nonempty
        (PointedSeedEdge z0 A.carrier A0.carrier A.branch A0.branch) := by
  rcases
      SCV.exists_metric_ball_differentiableOn_subset_of_mem_open
        A.carrier_open hz0
        (by simpa [PointedMetricBranchChart.carrier] using A.holo) with
    ⟨r, hr_pos, hball_sub, hholo⟩
  let A0 : PointedMetricBranchChart E F :=
    { center := z0
      radius := r
      radius_pos := hr_pos
      branch := A.branch
      holo := by
        simpa [PointedMetricBranchChart.carrier] using hholo }
  refine ⟨A0, rfl, ?_, ⟨?_⟩⟩
  · simpa [A0, PointedMetricBranchChart.carrier] using hball_sub
  · refine
      { W := A0.carrier
        W_open := A0.carrier_open
        z0_mem := by
          simpa [A0] using A0.center_mem
        W_sub := ?_
        eqOn := ?_ }
    · intro z hz
      exact ⟨by simpa [A0, PointedMetricBranchChart.carrier] using
        hball_sub hz, hz⟩
    · intro _z _hz
      rfl

private theorem pointed_seed_gallery_endpoint_seed_chart
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {z0 : E} {len : ℕ}
    (chart : Fin (len + 1) → PointedMetricBranchChart E F)
    (hz : ∀ j, z0 ∈ (chart j).carrier)
    (hstep :
      ∀ j : Fin len,
        PointedSeedEdge z0
          ((chart (Fin.castSucc j)).carrier)
          ((chart (Fin.succ j)).carrier)
          ((chart (Fin.castSucc j)).branch)
          ((chart (Fin.succ j)).branch)) :
    ∃ W : Set E,
      IsOpen W ∧ z0 ∈ W ∧
        W ⊆ (chart 0).carrier ∩ (chart (Fin.last len)).carrier ∧
        Set.EqOn (chart 0).branch (chart (Fin.last len)).branch W :=
  pointed_seed_gallery_endpoint_seed
    (fun j => (chart j).carrier)
    (fun j => (chart j).branch)
    (fun j => (chart j).carrier_open)
    hz hstep

private theorem pointed_seed_via_common_center
    {E F : Type*} [TopologicalSpace E]
    {z0 : E} {NA NB NC : Set E} {fA fB fC : E → F}
    (hAC :
      ∃ WA : Set E,
        IsOpen WA ∧ z0 ∈ WA ∧ WA ⊆ NA ∩ NC ∧ Set.EqOn fA fC WA)
    (hBC :
      ∃ WB : Set E,
        IsOpen WB ∧ z0 ∈ WB ∧ WB ⊆ NB ∩ NC ∧ Set.EqOn fB fC WB) :
    ∃ W : Set E,
      IsOpen W ∧ z0 ∈ W ∧ W ⊆ NA ∩ NB ∧ Set.EqOn fA fB W := by
  rcases hAC with ⟨WA, hWA_open, hzWA, hWA_sub, hWA_eq⟩
  rcases hBC with ⟨WB, hWB_open, hzWB, hWB_sub, hWB_eq⟩
  refine ⟨WA ∩ WB, hWA_open.inter hWB_open, ⟨hzWA, hzWB⟩, ?_, ?_⟩
  · intro z hz
    exact ⟨(hWA_sub hz.1).1, (hWB_sub hz.2).1⟩
  · intro z hz
    exact (hWA_eq hz.1).trans ((hWB_eq hz.2).symm)

private structure PointedCommonCenterGalleryPair
    (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (z0 : E) where
  leftLen : ℕ
  rightLen : ℕ
  center : PointedMetricBranchChart E F
  left : Fin (leftLen + 1) → PointedMetricBranchChart E F
  right : Fin (rightLen + 1) → PointedMetricBranchChart E F
  left_last_eq_center : left (Fin.last leftLen) = center
  right_last_eq_center : right (Fin.last rightLen) = center
  left_mem : ∀ j, z0 ∈ (left j).carrier
  right_mem : ∀ j, z0 ∈ (right j).carrier
  left_step :
    ∀ j : Fin leftLen,
      PointedSeedEdge z0
        ((left (Fin.castSucc j)).carrier)
        ((left (Fin.succ j)).carrier)
        ((left (Fin.castSucc j)).branch)
        ((left (Fin.succ j)).branch)
  right_step :
    ∀ j : Fin rightLen,
      PointedSeedEdge z0
        ((right (Fin.castSucc j)).carrier)
        ((right (Fin.succ j)).carrier)
        ((right (Fin.castSucc j)).branch)
        ((right (Fin.succ j)).branch)

private theorem PointedCommonCenterGalleryPair.endpoint_seed
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {z0 : E} (G : PointedCommonCenterGalleryPair E F z0) :
    ∃ W : Set E,
      IsOpen W ∧ z0 ∈ W ∧
        W ⊆ (G.left 0).carrier ∩ (G.right 0).carrier ∧
        Set.EqOn (G.left 0).branch (G.right 0).branch W := by
  obtain ⟨WL, hWL_open, hzWL, hWL_sub, hWL_eq⟩ :=
    pointed_seed_gallery_endpoint_seed_chart G.left G.left_mem G.left_step
  obtain ⟨WR, hWR_open, hzWR, hWR_sub, hWR_eq⟩ :=
    pointed_seed_gallery_endpoint_seed_chart G.right G.right_mem G.right_step
  have hLC :
      ∃ W : Set E,
        IsOpen W ∧ z0 ∈ W ∧
          W ⊆ (G.left 0).carrier ∩ G.center.carrier ∧
          Set.EqOn (G.left 0).branch G.center.branch W := by
    refine ⟨WL, hWL_open, hzWL, ?_, ?_⟩
    · intro z hz
      exact ⟨(hWL_sub hz).1, by
        simpa [G.left_last_eq_center] using (hWL_sub hz).2⟩
    · intro z hz
      simpa [G.left_last_eq_center] using hWL_eq hz
  have hRC :
      ∃ W : Set E,
        IsOpen W ∧ z0 ∈ W ∧
          W ⊆ (G.right 0).carrier ∩ G.center.carrier ∧
          Set.EqOn (G.right 0).branch G.center.branch W := by
    refine ⟨WR, hWR_open, hzWR, ?_, ?_⟩
    · intro z hz
      exact ⟨(hWR_sub hz).1, by
        simpa [G.right_last_eq_center] using (hWR_sub hz).2⟩
    · intro z hz
      simpa [G.right_last_eq_center] using hWR_eq hz
  exact pointed_seed_via_common_center hLC hRC

private theorem pointed_seed_of_retargeted_common_center_gallery
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {z0 : E} (A B A0 B0 : PointedMetricBranchChart E F)
    (edgeA : PointedSeedEdge z0 A.carrier A0.carrier A.branch A0.branch)
    (edgeB : PointedSeedEdge z0 B.carrier B0.carrier B.branch B0.branch)
    (hA0B0 :
      ∃ W : Set E,
        IsOpen W ∧ z0 ∈ W ∧
          W ⊆ A0.carrier ∩ B0.carrier ∧ Set.EqOn A0.branch B0.branch W) :
    ∃ W : Set E,
      IsOpen W ∧ z0 ∈ W ∧
        W ⊆ A.carrier ∩ B.carrier ∧ Set.EqOn A.branch B.branch W := by
  rcases hA0B0 with ⟨WG, hWG_open, hzWG, hWG_sub, hWG_eq⟩
  refine
    ⟨edgeA.W ∩ (WG ∩ edgeB.W),
      edgeA.W_open.inter (hWG_open.inter edgeB.W_open),
      ⟨edgeA.z0_mem, hzWG, edgeB.z0_mem⟩, ?_, ?_⟩
  · intro z hz
    exact ⟨(edgeA.W_sub hz.1).1, (edgeB.W_sub hz.2.2).1⟩
  · intro z hz
    exact
      (edgeA.eqOn hz.1).trans
        ((hWG_eq hz.2.1).trans ((edgeB.eqOn hz.2.2).symm))

private theorem pointed_retargeted_gallery_pair_seed
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {z0 : E} {A B A0 B0 : PointedMetricBranchChart E F}
    (edgeA : PointedSeedEdge z0 A.carrier A0.carrier A.branch A0.branch)
    (edgeB : PointedSeedEdge z0 B.carrier B0.carrier B.branch B0.branch)
    (G : PointedCommonCenterGalleryPair E F z0)
    (hleft0 : G.left 0 = A0)
    (hright0 : G.right 0 = B0) :
    ∃ W : Set E,
      IsOpen W ∧ z0 ∈ W ∧
        W ⊆ A.carrier ∩ B.carrier ∧ Set.EqOn A.branch B.branch W := by
  obtain ⟨WG, hWG_open, hzWG, hWG_sub, hWG_eq⟩ := G.endpoint_seed
  have hA0B0 :
      ∃ W : Set E,
        IsOpen W ∧ z0 ∈ W ∧
          W ⊆ A0.carrier ∩ B0.carrier ∧ Set.EqOn A0.branch B0.branch W := by
    refine ⟨WG, hWG_open, hzWG, ?_, ?_⟩
    · intro z hz
      exact ⟨by simpa [hleft0] using (hWG_sub hz).1,
        by simpa [hright0] using (hWG_sub hz).2⟩
    · intro z hz
      simpa [hleft0, hright0] using hWG_eq hz
  exact
    pointed_seed_of_retargeted_common_center_gallery
      A B A0 B0 edgeA edgeB hA0B0

private theorem pointed_metric_seed_of_restricted_gallery_pair
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {z0 : E} (A B : PointedMetricBranchChart E F)
    (hzA : z0 ∈ A.carrier) (hzB : z0 ∈ B.carrier)
    (hgrid :
      ∀ (A0 B0 : PointedMetricBranchChart E F),
        A0.center = z0 →
        A0.carrier ⊆ A.carrier →
        B0.center = z0 →
        B0.carrier ⊆ B.carrier →
        ∃ G : PointedCommonCenterGalleryPair E F z0,
          G.left 0 = A0 ∧ G.right 0 = B0) :
    ∃ W : Set E,
      IsOpen W ∧ z0 ∈ W ∧
        W ⊆ A.carrier ∩ B.carrier ∧ Set.EqOn A.branch B.branch W := by
  rcases A.restrict_center hzA with
    ⟨A0, hA0_center, hA0_sub, ⟨edgeA⟩⟩
  rcases B.restrict_center hzB with
    ⟨B0, hB0_center, hB0_sub, ⟨edgeB⟩⟩
  rcases hgrid A0 B0 hA0_center hA0_sub hB0_center hB0_sub with
    ⟨G, hleft0, hright0⟩
  exact pointed_retargeted_gallery_pair_seed edgeA edgeB G hleft0 hright0

private theorem PointedMetricBranchChart.eqOn_inter_of_seed
    {p q : ℕ} {z0 : Fin p → Fin q → ℂ}
    (A B : PointedMetricBranchChart (Fin p → Fin q → ℂ) ℂ)
    (hseed :
      ∃ W : Set (Fin p → Fin q → ℂ),
        IsOpen W ∧ z0 ∈ W ∧
          W ⊆ A.carrier ∩ B.carrier ∧ Set.EqOn A.branch B.branch W) :
    Set.EqOn A.branch B.branch (A.carrier ∩ B.carrier) := by
  rcases hseed with ⟨W, hW_open, hzW, hW_sub, hW_eq⟩
  have hfull :
      Set.EqOn A.branch B.branch
        (Metric.ball A.center A.radius ∩ Metric.ball B.center B.radius) :=
    SCV.identity_theorem_product_inter_metric_ball_of_eqOn_open
      hW_open ⟨z0, hzW⟩
      (by simpa [PointedMetricBranchChart.carrier] using hW_sub)
      (by simpa [PointedMetricBranchChart.carrier] using A.holo)
      (by simpa [PointedMetricBranchChart.carrier] using B.holo)
      hW_eq
  simpa [PointedMetricBranchChart.carrier] using hfull

private theorem PointedMetricBranchChart.sub_eqOn_inter_of_two_seeds
    {p q : ℕ} {z0 : Fin p → Fin q → ℂ}
    (A B : PointedMetricBranchChart (Fin p → Fin q → ℂ) ℂ)
    {fA gA fB gB : (Fin p → Fin q → ℂ) → ℂ}
    (hfA : DifferentiableOn ℂ fA A.carrier)
    (hgA : DifferentiableOn ℂ gA A.carrier)
    (hfB : DifferentiableOn ℂ fB B.carrier)
    (hgB : DifferentiableOn ℂ gB B.carrier)
    (hf_seed :
      ∃ Wf : Set (Fin p → Fin q → ℂ),
        IsOpen Wf ∧ z0 ∈ Wf ∧
          Wf ⊆ A.carrier ∩ B.carrier ∧ Set.EqOn fA fB Wf)
    (hg_seed :
      ∃ Wg : Set (Fin p → Fin q → ℂ),
        IsOpen Wg ∧ z0 ∈ Wg ∧
          Wg ⊆ A.carrier ∩ B.carrier ∧ Set.EqOn gA gB Wg) :
    Set.EqOn
      (fun z => fA z - gA z)
      (fun z => fB z - gB z)
      (A.carrier ∩ B.carrier) := by
  rcases hf_seed with ⟨Wf, hWf_open, hzWf, hWf_sub, hf_eq⟩
  rcases hg_seed with ⟨Wg, hWg_open, hzWg, hWg_sub, hg_eq⟩
  have hfull :
      Set.EqOn
        (fun z => fA z - gA z)
        (fun z => fB z - gB z)
        (Metric.ball A.center A.radius ∩ Metric.ball B.center B.radius) :=
    SCV.identity_theorem_product_inter_metric_ball_sub_of_two_eqOn_open
      hWf_open hzWf
      (by simpa [PointedMetricBranchChart.carrier] using hWf_sub)
      hWg_open hzWg
      (by simpa [PointedMetricBranchChart.carrier] using hWg_sub)
      (by simpa [PointedMetricBranchChart.carrier] using hfA)
      (by simpa [PointedMetricBranchChart.carrier] using hgA)
      (by simpa [PointedMetricBranchChart.carrier] using hfB)
      (by simpa [PointedMetricBranchChart.carrier] using hgB)
      hf_eq hg_eq
  simpa [PointedMetricBranchChart.carrier] using hfull

private theorem pointed_seed_of_ambient_eqOn_models
    {E F : Type*} [TopologicalSpace E]
    {z0 : E} {NA NB M : Set E}
    {fA fB modelA modelB : E → F}
    (hNA_open : IsOpen NA) (hNB_open : IsOpen NB) (hM_open : IsOpen M)
    (hzA : z0 ∈ NA) (hzB : z0 ∈ NB) (hzM : z0 ∈ M)
    (hA_model : Set.EqOn fA modelA NA)
    (hB_model : Set.EqOn fB modelB NB)
    (hmodel : Set.EqOn modelA modelB M) :
    ∃ W : Set E,
      IsOpen W ∧ z0 ∈ W ∧ W ⊆ NA ∩ NB ∧ Set.EqOn fA fB W := by
  refine
    ⟨NA ∩ (NB ∩ M), hNA_open.inter (hNB_open.inter hM_open),
      ⟨hzA, hzB, hzM⟩, ?_, ?_⟩
  · intro z hz
    exact ⟨hz.1, hz.2.1⟩
  · intro z hz
    exact (hA_model hz.1).trans
      ((hmodel hz.2.2).trans ((hB_model hz.2.1).symm))

private noncomputable def pointed_seed_edge_of_exists
    {E F : Type*} [TopologicalSpace E]
    {z0 : E} {NA NB : Set E} {fA fB : E → F}
    (h :
      ∃ W : Set E,
        IsOpen W ∧ z0 ∈ W ∧ W ⊆ NA ∩ NB ∧ Set.EqOn fA fB W) :
    PointedSeedEdge z0 NA NB fA fB :=
  let W := Classical.choose h
  let hW := Classical.choose_spec h
  { W := W
    W_open := hW.1
    z0_mem := hW.2.1
    W_sub := hW.2.2.1
    eqOn := hW.2.2.2 }

private noncomputable def pointed_seed_edge_of_common_model
    {E F : Type*} [TopologicalSpace E]
    {z0 : E} {NA NB : Set E} {fA fB model : E → F}
    (hNA_open : IsOpen NA) (hNB_open : IsOpen NB)
    (hzA : z0 ∈ NA) (hzB : z0 ∈ NB)
    (hA_model : Set.EqOn fA model NA)
    (hB_model : Set.EqOn fB model NB) :
    PointedSeedEdge z0 NA NB fA fB :=
  pointed_seed_edge_of_exists
    (pointed_seed_of_ambient_eqOn_models
      hNA_open hNB_open isOpen_univ hzA hzB trivial
      hA_model hB_model (fun _ _ => rfl))

private def pointed_seed_edge_retarget_both
    {E F : Type*} [TopologicalSpace E]
    {z0 : E} {NA NB NA0 NB0 : Set E}
    {fA fB fA0 fB0 : E → F}
    (hA0 : PointedSeedEdge z0 NA NA0 fA fA0)
    (hAB : PointedSeedEdge z0 NA NB fA fB)
    (hB0 : PointedSeedEdge z0 NB NB0 fB fB0) :
    PointedSeedEdge z0 NA0 NB0 fA0 fB0 := by
  refine
    { W := hA0.W ∩ (hAB.W ∩ hB0.W)
      W_open := hA0.W_open.inter (hAB.W_open.inter hB0.W_open)
      z0_mem := ⟨hA0.z0_mem, hAB.z0_mem, hB0.z0_mem⟩
      W_sub := ?_
      eqOn := ?_ }
  · intro z hz
    exact ⟨(hA0.W_sub hz.1).2, (hB0.W_sub hz.2.2).2⟩
  · intro z hz
    exact (hA0.eqOn hz.1).symm.trans
      ((hAB.eqOn hz.2.1).trans (hB0.eqOn hz.2.2))

private noncomputable def flat_realJost_EOW_pointed_seed_of_localZeroHeight_pairingsCLM
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    {E : Set (BHW.OS45FlatCommonChartReal d n)}
    (hE_open : IsOpen E)
    (hE_sub :
      E ⊆ BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)))
    (ys : Fin (BHW.os45FlatCommonChartDim d n) →
      Fin (BHW.os45FlatCommonChartDim d n) → ℝ)
    (hys_mem : ∀ j, ys j ∈ BHW.os45FlatCommonChartCone d n)
    (hys_li : LinearIndependent ℝ ys)
    (x0 : BHW.OS45FlatCommonChartReal d n)
    (hx0 : x0 ∈ E)
    (T : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ] ℂ)
    (hzero_plus :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆ E →
        (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (fun a => (x a : ℂ)) * φ x)
        = T φ)
    (hzero_minus :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆ E →
        (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (fun a => (x a : ℂ)) * φ x)
        = T φ)
    (A B : PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ)
    (hzA :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.unflattenCfg n d (SCV.realEmbed x0)) ∈ A.carrier)
    (hzB :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.unflattenCfg n d (SCV.realEmbed x0)) ∈ B.carrier)
    (hA_model :
      Set.EqOn A.branch (BHW.extendF (bvt_F OS lgc n)) A.carrier)
    (hB_model :
      Set.EqOn B.branch
        (fun z =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z)) B.carrier) :
    PointedSeedEdge
      ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.unflattenCfg n d (SCV.realEmbed x0)))
      A.carrier B.carrier A.branch B.branch := by
  let hflat :
      ∃ W : Set (Fin n → Fin (d + 1) → ℂ),
        IsOpen W ∧
        IsPreconnected W ∧
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.unflattenCfg n d (SCV.realEmbed x0)) ∈ W ∧
        W ⊆
          BHW.ExtendedTube d n ∩
            BHW.permutedExtendedTubeSector d n P.τ ∧
        Set.EqOn
          (BHW.extendF (bvt_F OS lgc n))
          (fun z =>
            BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) P.τ z))
          W :=
      BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localZeroHeight_pairingsCLM
        (d := d) hd OS lgc (P := P)
        hE_open hE_sub ys hys_mem hys_li x0 hx0 T hzero_plus hzero_minus
  let Wflat := Classical.choose hflat
  let hWflat := Classical.choose_spec hflat
  exact pointed_seed_edge_of_exists
    (pointed_seed_of_ambient_eqOn_models
      A.carrier_open B.carrier_open hWflat.1 hzA hzB hWflat.2.2.1
      hA_model hB_model hWflat.2.2.2.2)

private theorem zeroHeight_pairings_eq_common_of_sideLimits
    {ι α : Type*} {l : Filter ι} [NeBot l]
    {K : Set α} (hK_nonempty : K.Nonempty)
    {F G : ι → α → ℂ} {cF cG c : ℂ}
    (hF_zero : TendstoUniformlyOn F (fun _ : α => cF) l K)
    (hG_zero : TendstoUniformlyOn G (fun _ : α => cG) l K)
    (hF_common : TendstoUniformlyOn F (fun _ : α => c) l K)
    (hG_common : TendstoUniformlyOn G (fun _ : α => c) l K) :
    cF = c ∧ cG = c := by
  rcases hK_nonempty with ⟨η, hηK⟩
  have hFη_zero : Tendsto (fun eps => F eps η) l (𝓝 cF) := by
    simpa using hF_zero.tendsto_at hηK
  have hFη_common : Tendsto (fun eps => F eps η) l (𝓝 c) := by
    simpa using hF_common.tendsto_at hηK
  have hGη_zero : Tendsto (fun eps => G eps η) l (𝓝 cG) := by
    simpa using hG_zero.tendsto_at hηK
  have hGη_common : Tendsto (fun eps => G eps η) l (𝓝 c) := by
    simpa using hG_common.tendsto_at hηK
  exact
    ⟨tendsto_nhds_unique hFη_zero hFη_common,
      tendsto_nhds_unique hGη_zero hGη_common⟩

private theorem tendstoUniformlyOn_range_of_tendsto
    {ι κ α β : Type*} [Fintype κ] [UniformSpace β]
    {l : Filter ι} {ys : κ → α}
    {F : ι → α → β} {f : α → β}
    (h : ∀ k : κ, Tendsto (fun i : ι => F i (ys k)) l (𝓝 (f (ys k)))) :
    TendstoUniformlyOn F f l (Set.range ys) := by
  intro u hu
  have hpoint :
      ∀ k : κ, ∀ᶠ i in l, (f (ys k), F i (ys k)) ∈ u := by
    intro k
    have hnhds : {y : β | (f (ys k), y) ∈ u} ∈ 𝓝 (f (ys k)) := by
      rw [nhds_eq_comap_uniformity]
      exact preimage_mem_comap hu
    exact h k hnhds
  have hall :
      ∀ᶠ i in l, ∀ k, k ∈ (Finset.univ : Finset κ) →
        (f (ys k), F i (ys k)) ∈ u := by
    classical
    let S : Finset κ := Finset.univ
    change ∀ᶠ i in l, ∀ k, k ∈ S → (f (ys k), F i (ys k)) ∈ u
    induction S using Finset.induction_on with
    | empty =>
        simp
    | insert a S ha ih =>
        exact ((hpoint a).and ih).mono (by
          intro i hi k hk
          rw [Finset.mem_insert] at hk
          rcases hk with rfl | hk
          · exact hi.1
          · exact hi.2 k hk)
  filter_upwards [hall] with i hi x hx
  rcases hx with ⟨k, rfl⟩
  exact hi k (Finset.mem_univ k)

private theorem tendsto_fin_chain_of_eventual_eq
    {α : Type*} {l : Filter α} [NeBot l]
    {len : ℕ} {L : ℂ}
    (I : Fin (len + 1) → α → ℂ)
    (h0 : Tendsto (fun a => I 0 a) l (𝓝 L))
    (hstep :
      ∀ j : Fin len,
        (fun a => I (Fin.castSucc j) a) =ᶠ[l]
          fun a => I (Fin.succ j) a) :
    Tendsto (fun a => I (Fin.last len) a) l (𝓝 L) := by
  have hchain :
      ∀ m : ℕ, ∀ hm : m ≤ len,
        Tendsto
          (fun a => I ⟨m, Nat.lt_succ_of_le hm⟩ a)
          l (𝓝 L) := by
    intro m hm
    induction m with
    | zero =>
        simpa using h0
    | succ m ih =>
        have hm_le_len : m ≤ len := Nat.le_trans (Nat.le_succ m) hm
        have hm_lt_len : m < len := Nat.lt_of_succ_le hm
        let j : Fin len := ⟨m, hm_lt_len⟩
        have hprev :
            Tendsto (fun a => I (Fin.castSucc j) a) l (𝓝 L) := by
          simpa [j] using ih hm_le_len
        exact hprev.congr' (hstep j)
  simpa using hchain len le_rfl

private theorem pointed_chart_integral_eventually_eq_of_seed
    {p q : ℕ} {α X : Type*} [MeasurableSpace X] [MeasureSpace X]
    {l : Filter α} {z0 : Fin p → Fin q → ℂ}
    (A B : PointedMetricBranchChart (Fin p → Fin q → ℂ) ℂ)
    (edge :
      PointedSeedEdge z0 A.carrier B.carrier A.branch B.branch)
    (approach : α → X → Fin p → Fin q → ℂ)
    (weight : α → X → ℂ)
    (hmem :
      ∀ᶠ a in l, ∀ x,
        x ∈ Function.support (weight a) →
          approach a x ∈ A.carrier ∩ B.carrier) :
    (fun a =>
        ∫ x : X, A.branch (approach a x) * weight a x)
      =ᶠ[l]
      fun a =>
        ∫ x : X, B.branch (approach a x) * weight a x := by
  have hEq :
      Set.EqOn A.branch B.branch (A.carrier ∩ B.carrier) :=
    PointedMetricBranchChart.eqOn_inter_of_seed
      A B
      ⟨edge.W, edge.W_open, edge.z0_mem, edge.W_sub, edge.eqOn⟩
  filter_upwards [hmem] with a ha
  apply integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro x
  by_cases hx : x ∈ Function.support (weight a)
  · have hbranch : A.branch (approach a x) = B.branch (approach a x) :=
      hEq (ha x hx)
    change
      A.branch (approach a x) * weight a x =
        B.branch (approach a x) * weight a x
    rw [hbranch]
  · have hzero : weight a x = 0 := by
      by_contra hne
      exact hx (by simpa [Function.mem_support] using hne)
    simp [hzero]

private abbrev OS45PointedChart (d n : ℕ) :=
  PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ

private structure OrdModelAtZ0
    (d n : ℕ) (z0 : Fin n → Fin (d + 1) → ℂ)
    (OrdGlobal : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (A : OS45PointedChart d n) where
  z0_mem : z0 ∈ A.carrier
  eq_ord : Set.EqOn A.branch OrdGlobal A.carrier

private structure RawRetargetAtZ0
    (d n : ℕ) (z0 : Fin n → Fin (d + 1) → ℂ)
    (A rawLocal : OS45PointedChart d n) where
  z0_mem : z0 ∈ A.carrier
  edge_to_raw :
    PointedSeedEdge z0 A.carrier rawLocal.carrier A.branch rawLocal.branch

private structure FlatMinusAtZ0
    (d n : ℕ) (z0 : Fin n → Fin (d + 1) → ℂ)
    (A Cminus : OS45PointedChart d n) where
  z0_mem : z0 ∈ A.carrier
  to_Cminus_edge :
    PointedSeedEdge z0 A.carrier Cminus.carrier A.branch Cminus.branch

private structure FlatCrossingAtZ0
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    (z0 : Fin n → Fin (d + 1) → ℂ)
    (Cplus Cminus : OS45PointedChart d n) where
  E : Set (BHW.OS45FlatCommonChartReal d n)
  E_open : IsOpen E
  E_sub :
    E ⊆ BHW.os45FlatCommonChartEdgeSet d n P
      (1 : Equiv.Perm (Fin n))
  ys :
    Fin (BHW.os45FlatCommonChartDim d n) →
      Fin (BHW.os45FlatCommonChartDim d n) → ℝ
  ys_mem : ∀ j, ys j ∈ BHW.os45FlatCommonChartCone d n
  ys_li : LinearIndependent ℝ ys
  x0 : BHW.OS45FlatCommonChartReal d n
  x0_mem : x0 ∈ E
  T : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ] ℂ
  zero_plus :
    ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
      HasCompactSupport
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆ E →
      (∫ x : BHW.OS45FlatCommonChartReal d n,
        BHW.os45FlatCommonChartBranch d n OS lgc
          (1 : Equiv.Perm (Fin n))
          (fun a => (x a : ℂ)) * φ x)
      = T φ
  zero_minus :
    ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
      HasCompactSupport
        (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
      tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆ E →
      (∫ x : BHW.OS45FlatCommonChartReal d n,
        BHW.os45FlatCommonChartBranch d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (fun a => (x a : ℂ)) * φ x)
      = T φ
  z0_flat :
    z0 =
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.unflattenCfg n d
          (SCV.realEmbed x0))
  z0_mem_plus : z0 ∈ Cplus.carrier
  z0_mem_minus : z0 ∈ Cminus.carrier
  plus_model :
    Set.EqOn Cplus.branch (BHW.extendF (bvt_F OS lgc n)) Cplus.carrier
  minus_model :
    Set.EqOn Cminus.branch
      (fun z =>
        BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) P.τ z)) Cminus.carrier

private inductive LocalOverlapAtZ0
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    (z0 : Fin n → Fin (d + 1) → ℂ)
    (A0 B0 : OS45PointedChart d n) : Type where
  | ordinary
      (hA_ord : OrdModelAtZ0 d n z0 (BHW.extendF (bvt_F OS lgc n)) A0)
      (hB_ord : OrdModelAtZ0 d n z0 (BHW.extendF (bvt_F OS lgc n)) B0)
      (Ccommon : OS45PointedChart d n)
      (hCcommon_ord :
        OrdModelAtZ0 d n z0 (BHW.extendF (bvt_F OS lgc n)) Ccommon) :
      LocalOverlapAtZ0 hd OS lgc z0 A0 B0
  | adjacent
      (rawLocal : OS45PointedChart d n)
      (hA_adj : RawRetargetAtZ0 d n z0 A0 rawLocal)
      (hB_adj : RawRetargetAtZ0 d n z0 B0 rawLocal)
      (hzRawLocal : z0 ∈ rawLocal.carrier) :
      LocalOverlapAtZ0 hd OS lgc z0 A0 B0
  | flat_plus_minus
      (Cplus Cminus : OS45PointedChart d n)
      (hflat : FlatCrossingAtZ0 (P := P) hd OS lgc z0 Cplus Cminus)
      (hA_plus : OrdModelAtZ0 d n z0 (BHW.extendF (bvt_F OS lgc n)) A0)
      (hB_minus : FlatMinusAtZ0 d n z0 B0 Cminus) :
      LocalOverlapAtZ0 hd OS lgc z0 A0 B0
  | flat_minus_plus
      (Cplus Cminus : OS45PointedChart d n)
      (hflat : FlatCrossingAtZ0 (P := P) hd OS lgc z0 Cplus Cminus)
      (hA_minus : FlatMinusAtZ0 d n z0 A0 Cminus)
      (hB_plus : OrdModelAtZ0 d n z0 (BHW.extendF (bvt_F OS lgc n)) B0) :
      LocalOverlapAtZ0 hd OS lgc z0 A0 B0

private theorem os45_pointed_gallery_pair_one_one
    {d n : ℕ} {z0 : Fin n → Fin (d + 1) → ℂ}
    (A B C : OS45PointedChart d n)
    (hzA : z0 ∈ A.carrier)
    (hzB : z0 ∈ B.carrier)
    (hzC : z0 ∈ C.carrier)
    (edgeAC : PointedSeedEdge z0 A.carrier C.carrier A.branch C.branch)
    (edgeBC : PointedSeedEdge z0 B.carrier C.carrier B.branch C.branch) :
    ∃ G : PointedCommonCenterGalleryPair
        (Fin n → Fin (d + 1) → ℂ) ℂ z0,
      G.left 0 = A ∧ G.right 0 = B := by
  classical
  let left : Fin (1 + 1) → OS45PointedChart d n :=
    fun j => if (j : ℕ) = 0 then A else C
  let right : Fin (1 + 1) → OS45PointedChart d n :=
    fun j => if (j : ℕ) = 0 then B else C
  have hleft_mem : ∀ j, z0 ∈ (left j).carrier := by
    intro j
    rcases j with ⟨j, hj⟩
    interval_cases j <;> simp [left, hzA, hzC]
  have hright_mem : ∀ j, z0 ∈ (right j).carrier := by
    intro j
    rcases j with ⟨j, hj⟩
    interval_cases j <;> simp [right, hzB, hzC]
  have hleft_step :
      ∀ j : Fin 1,
        PointedSeedEdge z0
          ((left (Fin.castSucc j)).carrier)
          ((left (Fin.succ j)).carrier)
          ((left (Fin.castSucc j)).branch)
          ((left (Fin.succ j)).branch) := by
    intro j
    have hj : j = 0 := Subsingleton.elim j 0
    subst j
    simpa [left] using edgeAC
  have hright_step :
      ∀ j : Fin 1,
        PointedSeedEdge z0
          ((right (Fin.castSucc j)).carrier)
          ((right (Fin.succ j)).carrier)
          ((right (Fin.castSucc j)).branch)
          ((right (Fin.succ j)).branch) := by
    intro j
    have hj : j = 0 := Subsingleton.elim j 0
    subst j
    simpa [right] using edgeBC
  let G : PointedCommonCenterGalleryPair
      (Fin n → Fin (d + 1) → ℂ) ℂ z0 :=
    { leftLen := 1
      rightLen := 1
      center := C
      left := left
      right := right
      left_last_eq_center := by simp [left]
      right_last_eq_center := by simp [right]
      left_mem := hleft_mem
      right_mem := hright_mem
      left_step := hleft_step
      right_step := hright_step }
  exact ⟨G, by simp [G, left], by simp [G, right]⟩

private theorem os45_pointed_gallery_pair_one_two
    {d n : ℕ} {z0 : Fin n → Fin (d + 1) → ℂ}
    (A B Cplus Cminus : OS45PointedChart d n)
    (hzA : z0 ∈ A.carrier)
    (hzB : z0 ∈ B.carrier)
    (hzPlus : z0 ∈ Cplus.carrier)
    (hzMinus : z0 ∈ Cminus.carrier)
    (edgeAPlus :
      PointedSeedEdge z0 A.carrier Cplus.carrier A.branch Cplus.branch)
    (edgeBMinus :
      PointedSeedEdge z0 B.carrier Cminus.carrier B.branch Cminus.branch)
    (edgeMinusPlus :
      PointedSeedEdge z0 Cminus.carrier Cplus.carrier
        Cminus.branch Cplus.branch) :
    ∃ G : PointedCommonCenterGalleryPair
        (Fin n → Fin (d + 1) → ℂ) ℂ z0,
      G.left 0 = A ∧ G.right 0 = B := by
  classical
  let left : Fin (1 + 1) → OS45PointedChart d n :=
    fun j => if (j : ℕ) = 0 then A else Cplus
  let right : Fin (2 + 1) → OS45PointedChart d n :=
    fun j =>
      if (j : ℕ) = 0 then B else
        if (j : ℕ) = 1 then Cminus else Cplus
  have hleft_mem : ∀ j, z0 ∈ (left j).carrier := by
    intro j
    rcases j with ⟨j, hj⟩
    interval_cases j <;> simp [left, hzA, hzPlus]
  have hright_mem : ∀ j, z0 ∈ (right j).carrier := by
    intro j
    rcases j with ⟨j, hj⟩
    interval_cases j <;> simp [right, hzB, hzMinus, hzPlus]
  have hleft_step :
      ∀ j : Fin 1,
        PointedSeedEdge z0
          ((left (Fin.castSucc j)).carrier)
          ((left (Fin.succ j)).carrier)
          ((left (Fin.castSucc j)).branch)
          ((left (Fin.succ j)).branch) := by
    intro j
    have hj : j = 0 := Subsingleton.elim j 0
    subst j
    simpa [left] using edgeAPlus
  have hright_step :
      ∀ j : Fin 2,
        PointedSeedEdge z0
          ((right (Fin.castSucc j)).carrier)
          ((right (Fin.succ j)).carrier)
          ((right (Fin.castSucc j)).branch)
          ((right (Fin.succ j)).branch) := by
    intro j
    rcases j with ⟨j, hj⟩
    interval_cases j
    · simpa [right] using edgeBMinus
    · simpa [right] using edgeMinusPlus
  let G : PointedCommonCenterGalleryPair
      (Fin n → Fin (d + 1) → ℂ) ℂ z0 :=
    { leftLen := 1
      rightLen := 2
      center := Cplus
      left := left
      right := right
      left_last_eq_center := by simp [left]
      right_last_eq_center := by simp [right]
      left_mem := hleft_mem
      right_mem := hright_mem
      left_step := hleft_step
      right_step := hright_step }
  exact ⟨G, by simp [G, left], by simp [G, right]⟩

private theorem os45_pointed_gallery_pair_two_one
    {d n : ℕ} {z0 : Fin n → Fin (d + 1) → ℂ}
    (A B Cplus Cminus : OS45PointedChart d n)
    (hzA : z0 ∈ A.carrier)
    (hzB : z0 ∈ B.carrier)
    (hzPlus : z0 ∈ Cplus.carrier)
    (hzMinus : z0 ∈ Cminus.carrier)
    (edgeAMinus :
      PointedSeedEdge z0 A.carrier Cminus.carrier A.branch Cminus.branch)
    (edgeMinusPlus :
      PointedSeedEdge z0 Cminus.carrier Cplus.carrier
        Cminus.branch Cplus.branch)
    (edgeBPlus :
      PointedSeedEdge z0 B.carrier Cplus.carrier B.branch Cplus.branch) :
    ∃ G : PointedCommonCenterGalleryPair
        (Fin n → Fin (d + 1) → ℂ) ℂ z0,
      G.left 0 = A ∧ G.right 0 = B := by
  classical
  let left : Fin (2 + 1) → OS45PointedChart d n :=
    fun j =>
      if (j : ℕ) = 0 then A else
        if (j : ℕ) = 1 then Cminus else Cplus
  let right : Fin (1 + 1) → OS45PointedChart d n :=
    fun j => if (j : ℕ) = 0 then B else Cplus
  have hleft_mem : ∀ j, z0 ∈ (left j).carrier := by
    intro j
    rcases j with ⟨j, hj⟩
    interval_cases j <;> simp [left, hzA, hzMinus, hzPlus]
  have hright_mem : ∀ j, z0 ∈ (right j).carrier := by
    intro j
    rcases j with ⟨j, hj⟩
    interval_cases j <;> simp [right, hzB, hzPlus]
  have hleft_step :
      ∀ j : Fin 2,
        PointedSeedEdge z0
          ((left (Fin.castSucc j)).carrier)
          ((left (Fin.succ j)).carrier)
          ((left (Fin.castSucc j)).branch)
          ((left (Fin.succ j)).branch) := by
    intro j
    rcases j with ⟨j, hj⟩
    interval_cases j
    · simpa [left] using edgeAMinus
    · simpa [left] using edgeMinusPlus
  have hright_step :
      ∀ j : Fin 1,
        PointedSeedEdge z0
          ((right (Fin.castSucc j)).carrier)
          ((right (Fin.succ j)).carrier)
          ((right (Fin.castSucc j)).branch)
          ((right (Fin.succ j)).branch) := by
    intro j
    have hj : j = 0 := Subsingleton.elim j 0
    subst j
    simpa [right] using edgeBPlus
  let G : PointedCommonCenterGalleryPair
      (Fin n → Fin (d + 1) → ℂ) ℂ z0 :=
    { leftLen := 2
      rightLen := 1
      center := Cplus
      left := left
      right := right
      left_last_eq_center := by simp [left]
      right_last_eq_center := by simp [right]
      left_mem := hleft_mem
      right_mem := hright_mem
      left_step := hleft_step
      right_step := hright_step }
  exact ⟨G, by simp [G, left], by simp [G, right]⟩

private theorem localOverlapAtZ0_galleryPair
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    {A0 B0 : OS45PointedChart d n}
    (hcase : LocalOverlapAtZ0 (P := P) hd OS lgc z0 A0 B0) :
    ∃ G : PointedCommonCenterGalleryPair
        (Fin n → Fin (d + 1) → ℂ) ℂ z0,
      G.left 0 = A0 ∧ G.right 0 = B0 := by
  classical
  have edge_symm
      {A B : OS45PointedChart d n}
      (h : PointedSeedEdge z0 A.carrier B.carrier A.branch B.branch) :
      PointedSeedEdge z0 B.carrier A.carrier B.branch A.branch :=
    h.symm
  have edge_common
      {A B : OS45PointedChart d n}
      (hzA : z0 ∈ A.carrier) (hzB : z0 ∈ B.carrier)
      (hA_model :
        Set.EqOn A.branch (BHW.extendF (bvt_F OS lgc n)) A.carrier)
      (hB_model :
        Set.EqOn B.branch (BHW.extendF (bvt_F OS lgc n)) B.carrier) :
      PointedSeedEdge z0 A.carrier B.carrier A.branch B.branch :=
    pointed_seed_edge_of_common_model
      A.carrier_open B.carrier_open hzA hzB hA_model hB_model
  cases hcase with
  | ordinary hA_ord hB_ord Ccommon hCcommon_ord =>
      exact
        os45_pointed_gallery_pair_one_one A0 B0 Ccommon
          hA_ord.z0_mem hB_ord.z0_mem hCcommon_ord.z0_mem
          (edge_common hA_ord.z0_mem hCcommon_ord.z0_mem
            hA_ord.eq_ord hCcommon_ord.eq_ord)
          (edge_common hB_ord.z0_mem hCcommon_ord.z0_mem
            hB_ord.eq_ord hCcommon_ord.eq_ord)
  | adjacent rawLocal hA_adj hB_adj hzRawLocal =>
      exact
        os45_pointed_gallery_pair_one_one A0 B0 rawLocal
          hA_adj.z0_mem hB_adj.z0_mem hzRawLocal
          hA_adj.edge_to_raw hB_adj.edge_to_raw
  | flat_plus_minus Cplus Cminus hflat hA_plus hB_minus =>
      have hflat_edge :
          PointedSeedEdge z0 Cplus.carrier Cminus.carrier
            Cplus.branch Cminus.branch := by
        simpa [hflat.z0_flat] using
          flat_realJost_EOW_pointed_seed_of_localZeroHeight_pairingsCLM
            (d := d) hd OS lgc (P := P)
            (E := hflat.E) hflat.E_open hflat.E_sub
            hflat.ys hflat.ys_mem hflat.ys_li hflat.x0 hflat.x0_mem
            hflat.T hflat.zero_plus hflat.zero_minus
            Cplus Cminus
            (by simpa [hflat.z0_flat] using hflat.z0_mem_plus)
            (by simpa [hflat.z0_flat] using hflat.z0_mem_minus)
            hflat.plus_model hflat.minus_model
      exact
        os45_pointed_gallery_pair_one_two A0 B0 Cplus Cminus
          hA_plus.z0_mem hB_minus.z0_mem
          hflat.z0_mem_plus hflat.z0_mem_minus
          (edge_common hA_plus.z0_mem hflat.z0_mem_plus
            hA_plus.eq_ord hflat.plus_model)
          hB_minus.to_Cminus_edge
          (edge_symm hflat_edge)
  | flat_minus_plus Cplus Cminus hflat hA_minus hB_plus =>
      have hflat_edge :
          PointedSeedEdge z0 Cplus.carrier Cminus.carrier
            Cplus.branch Cminus.branch := by
        simpa [hflat.z0_flat] using
          flat_realJost_EOW_pointed_seed_of_localZeroHeight_pairingsCLM
            (d := d) hd OS lgc (P := P)
            (E := hflat.E) hflat.E_open hflat.E_sub
            hflat.ys hflat.ys_mem hflat.ys_li hflat.x0 hflat.x0_mem
            hflat.T hflat.zero_plus hflat.zero_minus
            Cplus Cminus
            (by simpa [hflat.z0_flat] using hflat.z0_mem_plus)
            (by simpa [hflat.z0_flat] using hflat.z0_mem_minus)
            hflat.plus_model hflat.minus_model
      exact
        os45_pointed_gallery_pair_two_one A0 B0 Cplus Cminus
          hA_minus.z0_mem hB_plus.z0_mem
          hflat.z0_mem_plus hflat.z0_mem_minus
          hA_minus.to_Cminus_edge
          (edge_symm hflat_edge)
          (edge_common hB_plus.z0_mem hflat.z0_mem_plus
            hB_plus.eq_ord hflat.plus_model)

private theorem OS45BHWJostHullData.OS412SeedWindow_pointedChart
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {x : NPointDomain d n} (hx : x ∈ P.V) :
    ∃ A : PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ,
      A.center =
        BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k)) ∧
      A.center ∈ A.carrier ∧
      A.carrier ⊆
        (({z : Fin n → Fin (d + 1) → ℂ |
            BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n} ∩ H.ΩJ) ∩
          (BHW.ExtendedTube d n ∩
            BHW.permutedExtendedTubeSector d n P.τ)) ∧
      Set.EqOn A.branch
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          bvt_F OS lgc n (BHW.permAct (d := d) P.τ z)) A.carrier ∧
      A.branch A.center =
        bvt_F OS lgc n (fun k => wickRotatePoint (x (P.τ k))) := by
  classical
  let p0 : Fin n → Fin (d + 1) → ℂ :=
    BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k))
  rcases H.OS412SeedWindow_initialSectorOverlap_metricBallChart OS lgc hx with
    ⟨C0, C0branch, r, hr_pos, hC0_ball, _hcenter, _hC0_open, _hC0_pre,
      hC0_sub, hC0_holo, hC0_eq, hC0_trace⟩
  let A : PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ :=
    { center := p0
      radius := r
      radius_pos := hr_pos
      branch := C0branch
      holo := by
        simpa [PointedMetricBranchChart.carrier, p0, hC0_ball] using
          hC0_holo }
  refine ⟨A, rfl, ?_, ?_, ?_, ?_⟩
  · simpa [A] using A.center_mem
  · intro z hz
    exact hC0_sub (by
      simpa [A, PointedMetricBranchChart.carrier, p0, hC0_ball] using hz)
  · intro z hz
    exact hC0_eq (by
      simpa [A, PointedMetricBranchChart.carrier, p0, hC0_ball] using hz)
  · simpa [A, p0] using hC0_trace

private theorem OS45BHWJostHullData.ordinaryWick_pointedChartInWindow
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {x : NPointDomain d n} (hx : x ∈ P.V)
    {W : Set (Fin n → Fin (d + 1) → ℂ)}
    (hW_open : IsOpen W)
    (hwickW : (fun k => wickRotatePoint (x k)) ∈ W) :
    ∃ A : PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ,
      A.center = (fun k => wickRotatePoint (x k)) ∧
      A.center ∈ A.carrier ∧
      A.carrier ⊆ (BHW.ExtendedTube d n ∩ H.ΩJ) ∩ W ∧
      Set.EqOn A.branch (BHW.extendF (bvt_F OS lgc n)) A.carrier ∧
      A.branch A.center =
        bvt_F OS lgc n (fun k => wickRotatePoint (x k)) := by
  classical
  let p0 : Fin n → Fin (d + 1) → ℂ :=
    fun k => wickRotatePoint (x k)
  rcases H.ordinaryWick_metricBallChartInWindow OS lgc hx hW_open hwickW with
    ⟨C0, C0branch, r, hr_pos, hC0_ball, _hcenter, _hC0_open, _hC0_pre,
      hC0_sub, hC0_holo, hC0_eq, hC0_trace⟩
  let A : PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ :=
    { center := p0
      radius := r
      radius_pos := hr_pos
      branch := C0branch
      holo := by
        simpa [PointedMetricBranchChart.carrier, p0, hC0_ball] using
          hC0_holo }
  refine ⟨A, rfl, ?_, ?_, ?_, ?_⟩
  · simpa [A] using A.center_mem
  · intro z hz
    exact hC0_sub (by
      simpa [A, PointedMetricBranchChart.carrier, p0, hC0_ball] using hz)
  · intro z hz
    exact hC0_eq (by
      simpa [A, PointedMetricBranchChart.carrier, p0, hC0_ball] using hz)
  · simpa [A, p0] using hC0_trace

private theorem OS45BHWJostHullData.ordinaryCommonEdge_pointedChartInWindow
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {x : NPointDomain d n} (hx : x ∈ P.V)
    {W : Set (Fin n → Fin (d + 1) → ℂ)}
    (hW_open : IsOpen W)
    (hcommonW :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) x)) ∈ W) :
    ∃ A : PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ,
      A.center =
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) x)) ∧
      A.center ∈ A.carrier ∧
      A.carrier ⊆ (BHW.ExtendedTube d n ∩ H.ΩJ) ∩ W ∧
      Set.EqOn A.branch (BHW.extendF (bvt_F OS lgc n)) A.carrier ∧
      A.branch A.center =
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (1 : Equiv.Perm (Fin n))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) x)) := by
  classical
  let p0 : Fin n → Fin (d + 1) → ℂ :=
    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
      (BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) x))
  rcases H.ordinaryCommonEdge_metricBallChartInWindow hd OS lgc hx
      hW_open hcommonW with
    ⟨C0, C0branch, r, hr_pos, hC0_ball, _hcenter, _hC0_open, _hC0_pre,
      hC0_sub, hC0_holo, hC0_eq, hC0_trace⟩
  let A : PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ :=
    { center := p0
      radius := r
      radius_pos := hr_pos
      branch := C0branch
      holo := by
        simpa [PointedMetricBranchChart.carrier, p0, hC0_ball] using
          hC0_holo }
  refine ⟨A, rfl, ?_, ?_, ?_, ?_⟩
  · simpa [A] using A.center_mem
  · intro z hz
    exact hC0_sub (by
      simpa [A, PointedMetricBranchChart.carrier, p0, hC0_ball] using hz)
  · intro z hz
    exact hC0_eq (by
      simpa [A, PointedMetricBranchChart.carrier, p0, hC0_ball] using hz)
  · simpa [A, p0] using hC0_trace

private theorem OS45BHWJostHullData.adjacentCommonEdge_pointedChartInWindow
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {x : NPointDomain d n} (hx : x ∈ P.V)
    {W : Set (Fin n → Fin (d + 1) → ℂ)}
    (hW_open : IsOpen W)
    (hcommonW :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) x)) ∈ W) :
    ∃ A : PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ,
      A.center =
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) x)) ∧
      A.center ∈ A.carrier ∧
      A.carrier ⊆
        (BHW.permutedExtendedTubeSector d n P.τ ∩ H.ΩJ) ∩ W ∧
      Set.EqOn A.branch
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z)) A.carrier ∧
      A.branch A.center =
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) x)) := by
  classical
  let p0 : Fin n → Fin (d + 1) → ℂ :=
    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
      (BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) x))
  rcases H.adjacentCommonEdge_metricBallChartInWindow hd OS lgc hx
      hW_open hcommonW with
    ⟨C0, C0branch, r, hr_pos, hC0_ball, _hcenter, _hC0_open, _hC0_pre,
      hC0_sub, hC0_holo, hC0_eq, hC0_trace⟩
  let A : PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ :=
    { center := p0
      radius := r
      radius_pos := hr_pos
      branch := C0branch
      holo := by
        simpa [PointedMetricBranchChart.carrier, p0, hC0_ball] using
          hC0_holo }
  refine ⟨A, rfl, ?_, ?_, ?_, ?_⟩
  · simpa [A] using A.center_mem
  · intro z hz
    exact hC0_sub (by
      simpa [A, PointedMetricBranchChart.carrier, p0, hC0_ball] using hz)
  · intro z hz
    exact hC0_eq (by
      simpa [A, PointedMetricBranchChart.carrier, p0, hC0_ball] using hz)
  · simpa [A, p0] using hC0_trace

private theorem OS45BHWJostHullData.commonEdgeDifference_pointedChartInWindow
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {x : NPointDomain d n} (hx : x ∈ P.V)
    {W : Set (Fin n → Fin (d + 1) → ℂ)}
    (hW_open : IsOpen W)
    (hcommonW :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) x)) ∈ W) :
    ∃ A : PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ,
      A.center =
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) x)) ∧
      A.center ∈ A.carrier ∧
      A.carrier ⊆
        ((BHW.ExtendedTube d n ∩
            BHW.permutedExtendedTubeSector d n P.τ) ∩ H.ΩJ) ∩ W ∧
      Set.EqOn A.branch
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) P.τ z) -
            BHW.extendF (bvt_F OS lgc n) z) A.carrier ∧
      A.branch A.center =
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) x)) -
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (1 : Equiv.Perm (Fin n))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) x)) := by
  classical
  let p0 : Fin n → Fin (d + 1) → ℂ :=
    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
      (BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) x))
  rcases H.commonEdgeDifference_metricBallChartInWindow hd OS lgc hx
      hW_open hcommonW with
    ⟨C0, C0branch, r, hr_pos, hC0_ball, _hcenter, _hC0_open, _hC0_pre,
      hC0_sub, hC0_holo, hC0_eq, hC0_trace⟩
  let A : PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ :=
    { center := p0
      radius := r
      radius_pos := hr_pos
      branch := C0branch
      holo := by
        simpa [PointedMetricBranchChart.carrier, p0, hC0_ball] using
          hC0_holo }
  refine ⟨A, rfl, ?_, ?_, ?_, ?_⟩
  · simpa [A] using A.center_mem
  · intro z hz
    exact hC0_sub (by
      simpa [A, PointedMetricBranchChart.carrier, p0, hC0_ball] using hz)
  · intro z hz
    exact hC0_eq (by
      simpa [A, PointedMetricBranchChart.carrier, p0, hC0_ball] using hz)
  · simpa [A, p0] using hC0_trace

/-- Direct OS I §4.5 producer for the local Figure-2-4 common-edge
holomorphic difference germ.

This is the hard Stage-A producer consumed by
`os45CommonEdge_localHorizontalDifference_representsZero_of_germ`.  The proof
enters the flat real-Jost crossing directly: the ordinary zero-height pairing
is supplied by the checked ordinary edge representation, while the selected
raw-adjacent zero-height pairing is the live OS-I side-height
branch/source-transfer block. -/
theorem os45CommonEdge_localFigure24DifferenceGerm_of_OSI45
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (U : Set (NPointDomain d n))
    (hU_open : IsOpen U)
    (hU_nonempty : U.Nonempty)
    (hU_sub : U ⊆ P.V) :
    ∃ Ucx : Set (Fin n → Fin (d + 1) → ℂ),
      ∃ Hdiff : (Fin n → Fin (d + 1) → ℂ) → ℂ,
        IsOpen Ucx ∧
        IsConnected Ucx ∧
        (∀ u ∈ U, (fun k => wickRotatePoint (u k)) ∈ Ucx) ∧
        (∀ u ∈ U,
          (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) ∈ Ucx) ∧
        DifferentiableOn ℂ Hdiff Ucx ∧
        (∀ φ : SchwartzNPoint d n,
          HasCompactSupport (φ : NPointDomain d n → ℂ) →
          tsupport (φ : NPointDomain d n → ℂ) ⊆ U →
          ∫ u : NPointDomain d n,
            Hdiff (fun k => wickRotatePoint (u k)) * φ u = 0) ∧
        (∀ u ∈ U,
          Hdiff
            ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u))) =
            BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u)) -
              BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (1 : Equiv.Perm (Fin n))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u))) := by
  classical
  let e := BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n))
  let E : Set (BHW.OS45FlatCommonChartReal d n) := e '' U
  let Tlocal : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ] ℂ :=
    BHW.os45FlatCommonChart_ordinaryEdgeCLM hd OS lgc P
  have hE_open : IsOpen E := by
    simpa [E, e] using e.toHomeomorph.isOpenMap U hU_open
  have hE_sub :
      E ⊆ BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)) := by
    rintro x ⟨u, huU, rfl⟩
    exact
      (BHW.os45CommonEdgeFlatCLE_mem_edgeSet_iff d n P
        (1 : Equiv.Perm (Fin n)) u).mpr (hU_sub huU)
  rcases hU_nonempty with ⟨u0, hu0⟩
  have hx0 : e u0 ∈ E := ⟨u0, hu0, rfl⟩
  have hn_pos : 0 < n := by omega
  haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn_pos⟩
  have hm : 0 < BHW.os45FlatCommonChartDim d n :=
    BHW.os45FlatCommonChartDim_pos_of_adjacent d n hi
  obtain ⟨hC_open, _hC_conv, _hC_zero, _hC_cone, hC_nonempty⟩ :=
    BHW.os45FlatCommonChartCone_eowReady d n
  obtain ⟨ys, hys_mem, hys_li⟩ :=
    open_set_contains_basis hm
      (BHW.os45FlatCommonChartCone d n) hC_open hC_nonempty
  have hzero_plus :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆ E →
        (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (fun a => (x a : ℂ)) * φ x)
        = Tlocal φ := by
    intro φ hφ_compact hφE
    exact
      BHW.os45FlatCommonChart_plus_zeroHeight_pairing_eq_CLM_of_localRepresents
        (d := d) hd OS lgc (P := P) Tlocal
        (BHW.os45FlatCommonChart_ordinaryEdgeCLM_represents hd OS lgc)
        φ hφ_compact (hφE.trans hE_sub)
  have hzero_minus :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆ E →
        (∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (fun a => (x a : ℂ)) * φ x)
        = Tlocal φ := by
    intro φ hφ_compact hφE
    let D : BHW.OS45Figure24SourceCutoffData P :=
      Classical.choice (BHW.exists_os45Figure24SourceCutoffData (d := d) P)
    let ψ0 : SchwartzNPoint d n :=
      (D.toZeroDiagonalCLM (1 : Equiv.Perm (Fin n)) φ).1
    let Kη : Set (BHW.OS45FlatCommonChartReal d n) := Set.range ys
    have hKη_nonempty : Kη.Nonempty := by
      exact ⟨ys 0, ⟨0, rfl⟩⟩
    have hKη_compact : IsCompact Kη := by
      simpa [Kη] using (Set.finite_range ys).isCompact
    have hKη_cone : Kη ⊆ BHW.os45FlatCommonChartCone d n := by
      rintro η ⟨j, rfl⟩
      exact hys_mem j
    have hψ0_compact :
        HasCompactSupport (ψ0 : NPointDomain d n → ℂ) := by
      simpa [ψ0, D, BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM] using
        D.toSchwartzNPointCLM_hasCompactSupport
          (1 : Equiv.Perm (Fin n)) φ
    have hψ0_suppU :
        tsupport (ψ0 : NPointDomain d n → ℂ) ⊆ U := by
      simpa [ψ0, D,
        BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM] using
        D.toSchwartzNPointCLM_tsupport_subset_image
          (1 : Equiv.Perm (Fin n)) φ hφE
    let Ssrc : Set (NPointDomain d n) :=
      e.symm '' tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ)
    have hSsrc_compact : IsCompact Ssrc := by
      simpa [Ssrc] using hφ_compact.isCompact.image e.symm.continuous
    have hSsrcU : Ssrc ⊆ U := by
      rintro u ⟨x, hx, rfl⟩
      rcases hφE hx with ⟨u', hu', hu'_eq⟩
      have : e.symm x = u' := by
        simpa using congrArg e.symm hu'_eq.symm
      simpa [this] using hu'
    obtain ⟨Ksrc, hKsrc_compact, hSsrc_int, hKsrcU⟩ :=
      exists_compact_between hSsrc_compact hU_open hSsrcU
    let Usrc : Set (NPointDomain d n) := interior Ksrc
    have hUsrc_open : IsOpen Usrc := by
      simp [Usrc]
    have hUsrc_sub_Ksrc : Usrc ⊆ Ksrc := by
      intro u hu
      exact interior_subset hu
    have hφUsrc :
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
          e '' Usrc := by
      intro x hx
      refine ⟨e.symm x, ?_, ?_⟩
      · exact hSsrc_int ⟨x, hx, rfl⟩
      · simp [e]
    have hψ0_suppKsrc :
        tsupport (ψ0 : NPointDomain d n → ℂ) ⊆ Ksrc := by
      have hψ0_suppUsrc :
          tsupport (ψ0 : NPointDomain d n → ℂ) ⊆ Usrc := by
        simpa [ψ0, D, Usrc,
          BHW.OS45Figure24SourceCutoffData.toZeroDiagonalCLM] using
          D.toSchwartzNPointCLM_tsupport_subset_image
            (1 : Equiv.Perm (Fin n)) φ hφUsrc
      exact hψ0_suppUsrc.trans hUsrc_sub_Ksrc
    have hcommon_support :
        ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
          ∀ η ∈ Kη,
            (∀ u ∉ Ksrc,
              ((((D.toSideZeroDiagonalCLM
                (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
                  SchwartzNPoint d n) : NPointDomain d n → ℂ) u) -
                ((((D.toZeroDiagonalCLM
                  (1 : Equiv.Perm (Fin n)) φ).1 :
                    SchwartzNPoint d n) : NPointDomain d n → ℂ) u) = 0) ∧
            (∀ u ∉ Ksrc,
              ((((D.toSideZeroDiagonalCLM
                (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
                  SchwartzNPoint d n) : NPointDomain d n → ℂ) u) -
                ((((D.toZeroDiagonalCLM
                  (1 : Equiv.Perm (Fin n)) φ).1 :
                    SchwartzNPoint d n) : NPointDomain d n → ℂ) u) = 0) := by
      simpa [Usrc] using
        D.toSideZeroDiagonalCLM_sub_toZeroDiagonalCLM_eq_zero_off_eventually
          hUsrc_open hUsrc_sub_Ksrc Kη hKη_compact
          φ hφ_compact hφUsrc
    let Fplus :
        ℝ → BHW.OS45FlatCommonChartReal d n → ℂ :=
      fun ε η =>
        ∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n))
            (fun a => (x a : ℂ) +
              (ε : ℂ) * (η a : ℂ) * Complex.I) * φ x
    let Fminus :
        ℝ → BHW.OS45FlatCommonChartReal d n → ℂ :=
      fun ε η =>
        ∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (fun a => (x a : ℂ) -
              (ε : ℂ) * (η a : ℂ) * Complex.I) * φ x
    let cMinus : ℂ :=
      ∫ x : BHW.OS45FlatCommonChartReal d n,
        BHW.os45FlatCommonChartBranch d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (fun a => (x a : ℂ)) * φ x
    have hplus_zero_uniform :
        TendstoUniformlyOn Fplus
          (fun _ : BHW.OS45FlatCommonChartReal d n => Tlocal φ)
          (𝓝[Set.Ioi 0] (0 : ℝ)) Kη := by
      simpa [Fplus] using
        BHW.os45_BHWJost_flatCommonChart_distributionalBoundaryValue_plus_of_zeroHeight_pairingCLM
          (d := d) hd OS lgc (P := P)
          Tlocal Kη hKη_compact hKη_cone
          φ hφ_compact (hφE.trans hE_sub)
          (hzero_plus φ hφ_compact hφE)
    have hminus_zero_uniform :
        TendstoUniformlyOn Fminus
          (fun _ : BHW.OS45FlatCommonChartReal d n => cMinus)
          (𝓝[Set.Ioi 0] (0 : ℝ)) Kη := by
      have hF_cont :
          ContinuousOn
            (BHW.os45FlatCommonChartBranch d n OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin n))))
            (BHW.os45FlatCommonChartOmega d n
              (P.τ.symm * (1 : Equiv.Perm (Fin n)))) :=
        (BHW.differentiableOn_os45FlatCommonChartBranch
          d n OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))).continuousOn
      have hside :
          ∀ K : Set (BHW.OS45FlatCommonChartReal d n), IsCompact K →
            K ⊆ BHW.os45FlatCommonChartEdgeSet d n P
              (1 : Equiv.Perm (Fin n)) →
            ∀ Kη : Set (BHW.OS45FlatCommonChartReal d n), IsCompact Kη →
              Kη ⊆ BHW.os45FlatCommonChartCone d n →
              ∃ r : ℝ, 0 < r ∧
                ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
                  (fun a => (x a : ℂ) +
                    ((-1 : ℝ) : ℂ) * (ε : ℂ) * (η a : ℂ) * Complex.I) ∈
                    BHW.os45FlatCommonChartOmega d n
                      (P.τ.symm * (1 : Equiv.Perm (Fin n))) := by
        intro K hK hKE Kη hKη hKηC
        obtain ⟨r, hr_pos, hr_mem⟩ :=
          BHW.os45_BHWJost_flatCommonChart_localWedge_of_figure24
            (d := d) hd (P := P) K hK hKE Kη hKη hKηC
        refine ⟨r, hr_pos, ?_⟩
        intro x hx η hη ε hε_pos hε_lt
        have hmem := (hr_mem x hx η hη ε hε_pos hε_lt).2
        simpa [sub_eq_add_neg, neg_mul, one_mul] using hmem
      simpa [Fminus, cMinus, sub_eq_add_neg, neg_mul, one_mul] using
        (SCV.tendstoUniformlyOn_sideIntegral_of_zeroHeight_pairing
          (m := BHW.os45FlatCommonChartDim d n)
          (E := BHW.os45FlatCommonChartEdgeSet d n P
            (1 : Equiv.Perm (Fin n)))
          (C := BHW.os45FlatCommonChartCone d n)
          (Ωc := BHW.os45FlatCommonChartOmega d n
            (P.τ.symm * (1 : Equiv.Perm (Fin n))))
          (BHW.isOpen_os45FlatCommonChartOmega d n
            (P.τ.symm * (1 : Equiv.Perm (Fin n))))
          (BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n))))
          hF_cont
          (BHW.os45FlatCommonChart_real_mem_omega_adjacent
            (d := d) hd (P := P))
          (-1 : ℝ) hside
          Kη hKη_compact hKη_cone φ hφ_compact (hφE.trans hE_sub)
          cMinus
          (by rfl))
    have hsource_uniform :=
      D.sideZeroDiagonal_sourcePairings_tendstoUniformlyOn_schwinger
        OS lgc Kη hKη_compact hKη_cone
        φ hφ_compact (hφE.trans hE_sub)
    have hminus_common :
        TendstoUniformlyOn Fminus
          (fun _ : BHW.OS45FlatCommonChartReal d n => Tlocal φ)
          (𝓝[Set.Ioi 0] (0 : ℝ)) Kη := by
      let J : ℂ := BHW.os45CommonEdgeFlatJacobianAbs n
      have hTlocal_source :
          Tlocal φ =
            J * OS.S n (D.toZeroDiagonalCLM
              (1 : Equiv.Perm (Fin n)) φ) := by
        have hplus_source :
            TendstoUniformlyOn Fplus
              (fun _ : BHW.OS45FlatCommonChartReal d n =>
                J * OS.S n (D.toZeroDiagonalCLM
                  (1 : Equiv.Perm (Fin n)) φ))
                (𝓝[Set.Ioi 0] (0 : ℝ)) Kη := by
            have hsource_plus := hsource_uniform.1
            let Gplus :
                ℝ → BHW.OS45FlatCommonChartReal d n → ℂ :=
              fun ε η =>
                J * (∫ u : NPointDomain d n,
                  BHW.extendF (bvt_F OS lgc n)
                    (BHW.os45FlatCommonChartSourceSide d n
                      (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η u) *
                    ((((D.toSideZeroDiagonalCLM
                      (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
                        SchwartzNPoint d n) : NPointDomain d n → ℂ) u))
            have hFplus_eq_Gplus :
                ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
                  ∀ η ∈ Kη, Fplus ε η = Gplus ε η := by
              have hint :=
                BHW.os45FlatCommonChart_branch_side_shifted_mul_integrable_eventually
                  (d := d) (hd := hd) OS lgc (P := P)
                  Kη hKη_compact hKη_cone
                  φ hφ_compact (hφE.trans hE_sub)
              obtain ⟨r, hr_pos, hside_support⟩ :=
                BHW.os45FlatCommonChart_sideSupport_radius
                  (d := d) (hd := hd) (P := P)
                  Kη hKη_compact hKη_cone
                  φ hφ_compact (hφE.trans hE_sub)
              filter_upwards
                [self_mem_nhdsWithin,
                  nhdsWithin_le_nhds (Iio_mem_nhds hr_pos), hint]
                with ε hε_pos hε_lt hintε η hη
              have hφE_shift :
                  tsupport
                    (SCV.translateSchwartz ((ε : ℝ) • η) φ :
                      BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
                  BHW.os45FlatCommonChartEdgeSet d n P
                    (1 : Equiv.Perm (Fin n)) :=
                (hside_support ε hε_pos hε_lt η hη).1
              have hφE_shift' :
                  tsupport
                    (SCV.translateSchwartz (((1 : ℝ) * ε) • η) φ :
                      BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
                  BHW.os45FlatCommonChartEdgeSet d n P
                    (1 : Equiv.Perm (Fin n)) := by
                simpa [one_mul] using hφE_shift
              have hinteg :=
                (hintε η hη).1
              have hinteg' :
                  Integrable
                    (fun x : BHW.OS45FlatCommonChartReal d n =>
                      BHW.os45FlatCommonChartBranch d n OS lgc
                        (1 : Equiv.Perm (Fin n))
                        (fun j =>
                          ((x + ((1 : ℝ) * ε) • η) j : ℂ) +
                            ((((1 : ℝ) * ε) • η) j : ℂ) *
                              Complex.I) *
                      φ (x + ((1 : ℝ) * ε) • η)) := by
                simpa [one_mul] using hinteg
              have heq :=
                BHW.os45FlatCommonChart_branch_integral_eq_sourceSide_extendF_sideZeroDiagonalCLM
                  (d := d) (hd := hd) OS lgc (P := P) D
                  (1 : Equiv.Perm (Fin n))
                  (1 : Equiv.Perm (Fin n))
                  (1 : ℝ) ε η φ hφE_shift' hinteg'
              simpa [Fplus, Gplus, J, one_mul] using heq
            have hGplus_source :
                TendstoUniformlyOn Gplus
                  (fun _ : BHW.OS45FlatCommonChartReal d n =>
                    J * OS.S n (D.toZeroDiagonalCLM
                      (1 : Equiv.Perm (Fin n)) φ))
                  (𝓝[Set.Ioi 0] (0 : ℝ)) Kη := by
                change
                  TendstoUniformlyOn Gplus
                    (fun _ : BHW.OS45FlatCommonChartReal d n =>
                      J * OS.S n (D.toZeroDiagonalCLM
                        (1 : Equiv.Perm (Fin n)) φ))
                    (𝓝[Set.Ioi 0] (0 : ℝ)) (Set.range ys)
                refine tendstoUniformlyOn_range_of_tendsto (ys := ys) ?_
                intro k
                let η0 : BHW.OS45FlatCommonChartReal d n := ys k
                have hF_cont :
                    ContinuousOn (BHW.extendF (bvt_F OS lgc n))
                      (BHW.ExtendedTube d n) :=
                  (BHW.differentiableOn_extendF_bvt_F_extendedTube
                    (d := d) OS lgc n).continuousOn
                have h0 :
                    ∀ u ∈ Ksrc,
                      BHW.os45FlatCommonChartSourceSide d n
                        (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η0 u ∈
                        BHW.ExtendedTube d n := by
                    intro u huK
                    have huV : u ∈ P.V := hU_sub (hKsrcU huK)
                    have hpulled := P.V_pulled_id u huV
                    rw [BHW.os45FlatCommonChartSourceSide_zero_eq_commonEdge]
                    simpa [BHW.os45PulledRealBranchDomain] using hpulled
                have hsupp :
                    ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
                      ∀ u ∉ Ksrc,
                        ((((D.toSideZeroDiagonalCLM
                          (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η0 φ).1 :
                            SchwartzNPoint d n) -
                          ((D.toZeroDiagonalCLM
                            (1 : Equiv.Perm (Fin n)) φ).1 :
                            SchwartzNPoint d n) :
                            SchwartzNPoint d n) :
                            NPointDomain d n → ℂ) u = 0 := by
                  filter_upwards [hcommon_support] with ε hε u huK
                  simpa [η0] using (hε η0 ⟨k, rfl⟩).1 u huK
                have hseminorm :
                    Tendsto
                      (fun ε : ℝ =>
                        SchwartzMap.seminorm ℝ 0 0
                          (((D.toSideZeroDiagonalCLM
                            (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η0 φ).1 :
                              SchwartzNPoint d n) -
                            ((D.toZeroDiagonalCLM
                              (1 : Equiv.Perm (Fin n)) φ).1 :
                              SchwartzNPoint d n) :
                              SchwartzNPoint d n))
                      (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
                  exact
                    (D.toSideZeroDiagonalCLM_sub_toZeroDiagonalCLM_seminorm_tendsto_zero
                      (1 : Equiv.Perm (Fin n)) (1 : ℝ) η0 φ hφ_compact).mono_left
                      nhdsWithin_le_nhds
                have hOrd_endpoint_DCT :
                    Tendsto
                      (fun ε : ℝ =>
                        ∫ u : NPointDomain d n,
                            BHW.extendF (bvt_F OS lgc n)
                              (BHW.os45FlatCommonChartSourceSide d n
                                (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η0 u) *
                            ((((D.toSideZeroDiagonalCLM
                              (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η0 φ).1 :
                                SchwartzNPoint d n) :
                                NPointDomain d n → ℂ) u))
                      (𝓝[Set.Ioi 0] (0 : ℝ))
                      (𝓝
                        (∫ u : NPointDomain d n,
                          BHW.extendF (bvt_F OS lgc n)
                            (BHW.os45FlatCommonChartSourceSide d n
                              (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η0 u) *
                          (ψ0 : NPointDomain d n → ℂ) u)) := by
                  simpa [η0, ψ0] using
                    BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_moving_of_commonCompactSupport
                      (d := d) (n := n)
                      (1 : Equiv.Perm (Fin n)) (1 : ℝ) η0
                      (U := BHW.ExtendedTube d n)
                      BHW.isOpen_extendedTube hF_cont
                      (K := Ksrc) hKsrc_compact h0
                      (εseq := fun ε : ℝ => ε)
                      (φseq := fun ε : ℝ =>
                        ((D.toSideZeroDiagonalCLM
                          (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η0 φ).1 :
                          SchwartzNPoint d n))
                      (φ0 := ψ0)
                      tendsto_id hψ0_suppKsrc hsupp hseminorm
                suffices hOrd_endpoint_value :
                    (∫ u : NPointDomain d n,
                      BHW.extendF (bvt_F OS lgc n)
                        (BHW.os45FlatCommonChartSourceSide d n
                          (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η0 u) *
                      (ψ0 : NPointDomain d n → ℂ) u) =
                    OS.S n (D.toZeroDiagonalCLM
                      (1 : Equiv.Perm (Fin n)) φ) by
                  have hOrd_endpoint_value_qturn :
                      (∫ u : NPointDomain d n,
                        BHW.extendF (bvt_F OS lgc n)
                          (BHW.os45QuarterTurnConfig (d := d) (n := n)
                            (fun k => wickRotatePoint (u k))) *
                        (ψ0 : NPointDomain d n → ℂ) u) =
                      OS.S n (D.toZeroDiagonalCLM
                        (1 : Equiv.Perm (Fin n)) φ) := by
                    simpa [BHW.os45FlatCommonChartSourceSide_zero] using
                      hOrd_endpoint_value
                  simpa [Gplus, η0, hOrd_endpoint_value_qturn] using
                    hOrd_endpoint_DCT.const_mul J
                let OrdFixed : ℝ → ℂ := fun ε =>
                  ∫ u : NPointDomain d n,
                    BHW.extendF (bvt_F OS lgc n)
                      (BHW.os45FlatCommonChartSourceSide d n
                        (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η0 u) *
                    (ψ0 : NPointDomain d n → ℂ) u
                have hOrd_fixed_endpoint :
                    Tendsto OrdFixed (𝓝[Set.Ioi 0] (0 : ℝ))
                      (𝓝
                        (∫ u : NPointDomain d n,
                          BHW.extendF (bvt_F OS lgc n)
                            (BHW.os45FlatCommonChartSourceSide d n
                              (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η0 u) *
                          (ψ0 : NPointDomain d n → ℂ) u)) := by
                  have h0ψ :
                      ∀ u ∈ tsupport (ψ0 : NPointDomain d n → ℂ),
                        BHW.os45FlatCommonChartSourceSide d n
                          (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η0 u ∈
                        BHW.ExtendedTube d n := by
                    intro u hu
                    exact h0 u (hψ0_suppKsrc hu)
                  simpa [OrdFixed] using
                    BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_of_hasCompactSupport
                      (d := d) (n := n)
                      (1 : Equiv.Perm (Fin n)) (1 : ℝ) η0
                      (U := BHW.ExtendedTube d n)
                      BHW.isOpen_extendedTube hF_cont
                      hψ0_compact (ψ0 : SchwartzNPoint d n).continuous h0ψ
                have hOrd_fixed_selected :
                    Tendsto OrdFixed (𝓝[Set.Ioi 0] (0 : ℝ))
                      (𝓝
                        (OS.S n (D.toZeroDiagonalCLM
                          (1 : Equiv.Perm (Fin n)) φ))) := by
                  let eflat :=
                    BHW.os45CommonEdgeFlatCLE d n
                      (1 : Equiv.Perm (Fin n))
                  let ψ0Flat :
                      SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ :=
                    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
                      eflat.symm) (ψ0 : SchwartzNPoint d n)
                  have hψ0Flat_eq_phi : ψ0Flat = φ := by
                    ext x
                    have hplain :=
                      D.toSchwartzNPointCLM_eq_plain_of_tsupport_subset_edge
                        (1 : Equiv.Perm (Fin n)) φ (hφE.trans hE_sub)
                        (eflat.symm x)
                    change
                      ((D.toSchwartzNPointCLM
                        (1 : Equiv.Perm (Fin n)) φ :
                        NPointDomain d n → ℂ) (eflat.symm x)) = φ x
                    simpa [eflat] using hplain
                  have hUsrc_P : Usrc ⊆ P.V :=
                    hUsrc_sub_Ksrc.trans (hKsrcU.trans hU_sub)
                  have hψ0Flat_packet :
                      HasCompactSupport
                          (ψ0Flat : BHW.OS45FlatCommonChartReal d n → ℂ) ∧
                        tsupport
                          (ψ0Flat :
                            BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
                          BHW.os45FlatCommonChartEdgeSet d n P
                            (1 : Equiv.Perm (Fin n)) := by
                    simpa [ψ0Flat, ψ0, eflat] using
                      D.toZeroDiagonalCLM_flatPullback_support
                        (1 : Equiv.Perm (Fin n))
                        (U := Usrc) φ hφUsrc hUsrc_P
                  have hOrd_fixed_selected_direct :
                      Tendsto OrdFixed (𝓝[Set.Ioi 0] (0 : ℝ))
                        (𝓝
                          (OS.S n (D.toZeroDiagonalCLM
                            (1 : Equiv.Perm (Fin n)) φ))) := by
                      /-
                      Genuine remaining ordinary flat selector.  This is the
                      one-branch `(4.1)` translated-boundary chain, before scalar
                      cancellation back to the source variables.
                      -/
                      let K0 : Set (BHW.OS45FlatCommonChartReal d n) :=
                        tsupport
                          (ψ0Flat :
                            BHW.OS45FlatCommonChartReal d n → ℂ)
                      have hK0_compact : IsCompact K0 := by
                        simpa [K0] using hψ0Flat_packet.1.isCompact
                      have hK0_edge :
                          K0 ⊆ BHW.os45FlatCommonChartEdgeSet d n P
                            (1 : Equiv.Perm (Fin n)) := by
                        simpa [K0] using hψ0Flat_packet.2
                      have hK0_E : K0 ⊆ E := by
                        intro x hx
                        have hxφ :
                            x ∈ tsupport
                              (φ :
                                BHW.OS45FlatCommonChartReal d n → ℂ) := by
                          simpa [K0, hψ0Flat_eq_phi] using hx
                        exact hφE hxφ
                      have hK0_preimage_Usrc :
                          ∀ x ∈ K0, eflat.symm x ∈ Usrc := by
                        intro x hx
                        have hxφ :
                            x ∈ tsupport
                              (φ :
                                BHW.OS45FlatCommonChartReal d n → ℂ) := by
                          simpa [K0, hψ0Flat_eq_phi] using hx
                        rcases hφUsrc hxφ with ⟨u, hu, hu_eq⟩
                        have hx_eq : eflat.symm x = u := by
                          simpa [eflat, e] using congrArg eflat.symm hu_eq.symm
                        simpa [hx_eq] using hu
                      have hK0_preimage_P :
                          ∀ x ∈ K0, eflat.symm x ∈ P.V := by
                        intro x hx
                        exact hUsrc_P (hK0_preimage_Usrc x hx)
                      have hOrd_translated_tsupport :
                          ∀ ε : ℝ,
                            tsupport
                              (SCV.translateSchwartz
                                (-((1 : ℝ) * ε) • η0) ψ0Flat :
                                BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
                              {x | x + (-((1 : ℝ) * ε) • η0) ∈ K0} := by
                        intro ε
                        simpa [K0] using
                          (BHW.tsupport_translateSchwartz_subset_preimage
                            (m := BHW.os45FlatCommonChartDim d n)
                            (-((1 : ℝ) * ε) • η0) ψ0Flat)
                      have hOrd_translated_source_P :
                          ∀ ε : ℝ,
                            ∀ x ∈ tsupport
                              (SCV.translateSchwartz
                                (-((1 : ℝ) * ε) • η0) ψ0Flat :
                                BHW.OS45FlatCommonChartReal d n → ℂ),
                              eflat.symm
                                  (x + (-((1 : ℝ) * ε) • η0)) ∈ P.V := by
                        intro ε x hx
                        exact hK0_preimage_P
                          (x + (-((1 : ℝ) * ε) • η0))
                          (hOrd_translated_tsupport ε hx)
                      have hOrd_sourceSide_sheet :
                          ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
                            ∀ u : NPointDomain d n,
                              eflat u + ε • η0 ∈ K0 →
                                BHW.permAct (d := d)
                                  (1 : Equiv.Perm (Fin n)).symm
                                  (BHW.os45FlatCommonChartSourceSide d n
                                    (1 : Equiv.Perm (Fin n)) (1 : ℝ)
                                    ε η0 u) ∈
                                  BHW.ExtendedTube d n := by
                        have hsheet :=
                          BHW.os45FlatCommonChart_sourceSide_mem_extendedTube_eventually
                            (d := d) (hd := hd) (P := P)
                            Kη hKη_compact hKη_cone
                            ψ0Flat hψ0Flat_packet.1 hψ0Flat_packet.2
                        filter_upwards [hsheet] with ε hε u hu
                        exact (hε η0 ⟨k, rfl⟩).1 u
                          (by simpa [K0, eflat] using hu)
                      have hOrd_base_chart :
                          ∀ x ∈ K0,
                            ∃ A : PointedMetricBranchChart
                                (Fin n → Fin (d + 1) → ℂ) ℂ,
                              A.center =
                                  (fun k =>
                                    wickRotatePoint ((eflat.symm x) k)) ∧
                              A.center ∈ A.carrier ∧
                              A.carrier ⊆
                                  (BHW.ExtendedTube d n ∩ H.ΩJ) ∩
                                    Set.univ ∧
                              Set.EqOn A.branch
                                (BHW.extendF (bvt_F OS lgc n)) A.carrier ∧
                              A.branch A.center =
                                bvt_F OS lgc n
                                  (fun k =>
                                    wickRotatePoint ((eflat.symm x) k)) := by
                        intro x hx
                        simpa using
                          H.ordinaryWick_pointedChartInWindow OS lgc
                            (hK0_preimage_P x hx)
                            (W := Set.univ) isOpen_univ trivial
                      have hOrd_terminal_chart :
                          ∀ x ∈ K0,
                            ∃ A : PointedMetricBranchChart
                                (Fin n → Fin (d + 1) → ℂ) ℂ,
                              A.center =
                                  (BHW.os45QuarterTurnCLE
                                    (d := d) (n := n)).symm
                                    (BHW.realEmbed
                                      (BHW.os45CommonEdgeRealPoint
                                        (d := d) (n := n)
                                        (1 : Equiv.Perm (Fin n))
                                        (eflat.symm x))) ∧
                              A.center ∈ A.carrier ∧
                              A.carrier ⊆
                                  (BHW.ExtendedTube d n ∩ H.ΩJ) ∩
                                    Set.univ ∧
                              Set.EqOn A.branch
                                (BHW.extendF (bvt_F OS lgc n)) A.carrier ∧
                              A.branch A.center =
                                BHW.os45PulledRealBranch
                                  (d := d) (n := n) OS lgc
                                  (1 : Equiv.Perm (Fin n))
                                  (BHW.realEmbed
                                    (BHW.os45CommonEdgeRealPoint
                                      (d := d) (n := n)
                                      (1 : Equiv.Perm (Fin n))
                                      (eflat.symm x))) := by
                        intro x hx
                        simpa using
                          H.ordinaryCommonEdge_pointedChartInWindow
                            OS lgc (hK0_preimage_P x hx)
                            (W := Set.univ) isOpen_univ trivial
                      have hOrd_local_cover_data :
                          ∀ y : K0,
                            ∃ V : Set (BHW.OS45FlatCommonChartReal d n),
                              IsOpen V ∧ y.1 ∈ V ∧
                              (∃ c R, V ⊆ Metric.closedBall c R) ∧
                              V ⊆ BHW.os45FlatCommonChartEdgeSet d n P
                                (1 : Equiv.Perm (Fin n)) ∧
                              eflat.symm '' V ⊆ Usrc ∧
                              ∃ A0 A1 : PointedMetricBranchChart
                                  (Fin n → Fin (d + 1) → ℂ) ℂ,
                                A0.center =
                                    (fun k =>
                                      wickRotatePoint ((eflat.symm y.1) k)) ∧
                                A0.center ∈ A0.carrier ∧
                                A0.carrier ⊆
                                    (BHW.ExtendedTube d n ∩ H.ΩJ) ∩
                                      Set.univ ∧
                                Set.EqOn A0.branch
                                  (BHW.extendF (bvt_F OS lgc n)) A0.carrier ∧
                                A0.branch A0.center =
                                  bvt_F OS lgc n
                                    (fun k =>
                                      wickRotatePoint ((eflat.symm y.1) k)) ∧
                                A1.center =
                                    (BHW.os45QuarterTurnCLE
                                      (d := d) (n := n)).symm
                                      (BHW.realEmbed
                                        (BHW.os45CommonEdgeRealPoint
                                          (d := d) (n := n)
                                          (1 : Equiv.Perm (Fin n))
                                          (eflat.symm y.1))) ∧
                                A1.center ∈ A1.carrier ∧
                                A1.carrier ⊆
                                    (BHW.ExtendedTube d n ∩ H.ΩJ) ∩
                                      Set.univ ∧
                                Set.EqOn A1.branch
                                  (BHW.extendF (bvt_F OS lgc n)) A1.carrier ∧
                                A1.branch A1.center =
                                  BHW.os45PulledRealBranch
                                    (d := d) (n := n) OS lgc
                                    (1 : Equiv.Perm (Fin n))
                                    (BHW.realEmbed
                                      (BHW.os45CommonEdgeRealPoint
                                        (d := d) (n := n)
                                        (1 : Equiv.Perm (Fin n))
                                        (eflat.symm y.1))) ∧
                                (∀ x ∈ V,
                                  (fun k =>
                                    wickRotatePoint ((eflat.symm x) k)) ∈
                                      A0.carrier) ∧
                                (∀ x ∈ V,
                                  (BHW.os45QuarterTurnCLE
                                    (d := d) (n := n)).symm
                                    (BHW.realEmbed
                                      (BHW.os45CommonEdgeRealPoint
                                        (d := d) (n := n)
                                        (1 : Equiv.Perm (Fin n))
                                        (eflat.symm x))) ∈
                                      A1.carrier) ∧
                                ∃ Ucorr : Set
                                    (Fin n → Fin (d + 1) → ℂ),
                                  IsOpen Ucorr ∧
                                  IsConnected Ucorr ∧
                                  (fun k =>
                                    wickRotatePoint ((eflat.symm y.1) k)) ∈
                                    Ucorr ∧
                                  (BHW.os45QuarterTurnCLE
                                    (d := d) (n := n)).symm
                                    (BHW.realEmbed
                                      (BHW.os45CommonEdgeRealPoint
                                        (d := d) (n := n)
                                        (1 : Equiv.Perm (Fin n))
                                        (eflat.symm y.1))) ∈ Ucorr ∧
                                  Ucorr ⊆
                                    BHW.ExtendedTube d n ∩
                                      BHW.permutedExtendedTubeSector d n P.τ ∧
                                  (∀ x ∈ V,
                                    (fun k =>
                                      wickRotatePoint
                                        ((eflat.symm x) k)) ∈ Ucorr) ∧
                                  (∀ x ∈ V,
                                    (BHW.os45QuarterTurnCLE
                                      (d := d) (n := n)).symm
                                      (BHW.realEmbed
                                        (BHW.os45CommonEdgeRealPoint
                                          (d := d) (n := n)
                                          (1 : Equiv.Perm (Fin n))
                                          (eflat.symm x))) ∈ Ucorr) ∧
                                  ∀ z ∈ Ucorr,
                                    ∃ A : PointedMetricBranchChart
                                        (Fin n → Fin (d + 1) → ℂ) ℂ,
                                      A.center = z ∧
                                      A.center ∈ A.carrier ∧
                                      A.carrier ⊆
                                        (BHW.ExtendedTube d n ∩ H.ΩJ) ∩
                                          Ucorr ∧
                                      Set.EqOn A.branch
                                        (BHW.extendF (bvt_F OS lgc n))
                                        A.carrier := by
                        intro y
                        rcases hOrd_base_chart y.1 y.2 with
                          ⟨A0, hA0_center, hA0_mem, hA0_sub,
                            hA0_model, hA0_trace⟩
                        rcases hOrd_terminal_chart y.1 y.2 with
                          ⟨A1, hA1_center, hA1_mem, hA1_sub,
                            hA1_model, hA1_trace⟩
                        let zWick :
                            BHW.OS45FlatCommonChartReal d n →
                              Fin n → Fin (d + 1) → ℂ := fun x =>
                          fun k => wickRotatePoint ((eflat.symm x) k)
                        let zCommon :
                            BHW.OS45FlatCommonChartReal d n →
                              Fin n → Fin (d + 1) → ℂ := fun x =>
                          (BHW.os45QuarterTurnCLE
                            (d := d) (n := n)).symm
                            (BHW.realEmbed
                              (BHW.os45CommonEdgeRealPoint
                                (d := d) (n := n)
                                (1 : Equiv.Perm (Fin n))
                                (eflat.symm x)))
                        have hzWick_cont : Continuous zWick := by
                          change
                            Continuous
                              ((fun x : NPointDomain d n =>
                                fun k => wickRotatePoint (x k)) ∘
                                eflat.symm)
                          exact
                            (BHW.continuous_wickRotateRealConfig
                              (d := d) (n := n)).comp
                                eflat.symm.continuous
                        have hzCommon_cont : Continuous zCommon := by
                          change
                            Continuous
                              ((BHW.os45QuarterTurnCLE
                                (d := d) (n := n)).symm ∘
                                (fun x : NPointDomain d n =>
                                  BHW.realEmbed
                                    (BHW.os45CommonEdgeRealPoint
                                      (d := d) (n := n)
                                      (1 : Equiv.Perm (Fin n)) x)) ∘
                                eflat.symm)
                          exact
                            (BHW.os45QuarterTurnCLE
                              (d := d) (n := n)).symm.continuous.comp
                              ((BHW.continuous_realEmbed_os45CommonEdgeRealPoint
                                (d := d) (n := n)
                                (1 : Equiv.Perm (Fin n))).comp
                                  eflat.symm.continuous)
                        let uy : NPointDomain d n := eflat.symm y.1
                        have hOrd_join_y :
                            JoinedIn
                              (BHW.ExtendedTube d n ∩
                                BHW.permutedExtendedTubeSector d n P.τ)
                              (fun k => wickRotatePoint (uy k))
                              ((BHW.os45QuarterTurnCLE
                                (d := d) (n := n)).symm
                                (BHW.realEmbed
                                  (BHW.os45CommonEdgeRealPoint
                                    (d := d) (n := n)
                                    (1 : Equiv.Perm (Fin n)) uy))) := by
                          simpa [uy] using
                            BHW.os45Figure24_joined_ordinaryWick_to_commonEdge_initialSectorOverlap
                              (d := d) (n := n) (hd := hd) (P := P)
                              (x := uy)
                              (subset_closure
                                (hK0_preimage_P y.1 y.2))
                        obtain
                          ⟨Ucorr, hUcorr_open, hUcorr_connected,
                            hUcorr_wick, hUcorr_common, hUcorr_sub⟩ :=
                          BHW.initialSectorOverlap_connectedNeighborhood_of_joinedIn
                            (d := d) (n := n) P.τ hOrd_join_y
                        have hUcorr_sub_hull :
                            Ucorr ⊆ BHW.ExtendedTube d n ∩ H.ΩJ := by
                          intro z hz
                          have hzET : z ∈ BHW.ExtendedTube d n :=
                            (hUcorr_sub hz).1
                          exact ⟨hzET, H.extendedTube_subset_ΩJ hzET⟩
                        have hUcorr_chart :
                            ∀ z ∈ Ucorr,
                              ∃ A : PointedMetricBranchChart
                                  (Fin n → Fin (d + 1) → ℂ) ℂ,
                                A.center = z ∧
                                A.center ∈ A.carrier ∧
                                A.carrier ⊆
                                  (BHW.ExtendedTube d n ∩ H.ΩJ) ∩
                                    Ucorr ∧
                                Set.EqOn A.branch
                                  (BHW.extendF (bvt_F OS lgc n))
                                  A.carrier := by
                          intro z hz
                          let Ωcorr :
                              Set (Fin n → Fin (d + 1) → ℂ) :=
                            (BHW.ExtendedTube d n ∩ H.ΩJ) ∩ Ucorr
                          have hΩcorr_open : IsOpen Ωcorr := by
                            simpa [Ωcorr] using
                              (BHW.isOpen_extendedTube.inter
                                H.ΩJ_open).inter hUcorr_open
                          have hzΩcorr : z ∈ Ωcorr :=
                            ⟨hUcorr_sub_hull hz, hz⟩
                          rcases Metric.mem_nhds_iff.mp
                              (hΩcorr_open.mem_nhds hzΩcorr) with
                            ⟨r, hr_pos, hball_sub⟩
                          let A : PointedMetricBranchChart
                              (Fin n → Fin (d + 1) → ℂ) ℂ :=
                            { center := z
                              radius := r
                              radius_pos := hr_pos
                              branch := BHW.extendF (bvt_F OS lgc n)
                              holo := by
                                exact
                                  (BHW.differentiableOn_extendF_bvt_F_extendedTube
                                    (d := d) OS lgc n).mono
                                    (by
                                      intro w hw
                                      exact (hball_sub hw).1.1) }
                          refine ⟨A, rfl, ?_, ?_, ?_⟩
                          · simpa [A] using A.center_mem
                          · intro w hw
                            exact
                              hball_sub
                                (by
                                  simpa [A,
                                    PointedMetricBranchChart.carrier] using hw)
                          · intro _w _hw
                            rfl
                        let V : Set (BHW.OS45FlatCommonChartReal d n) :=
                          (((((E ∩ (eflat.symm ⁻¹' Usrc)) ∩
                                Metric.ball y.1 1) ∩
                              zWick ⁻¹' A0.carrier) ∩
                              zCommon ⁻¹' A1.carrier) ∩
                            zWick ⁻¹' Ucorr) ∩
                            zCommon ⁻¹' Ucorr
                        refine ⟨V, ?_, ?_, ?_, ?_, ?_⟩
                        · exact
                            (((((hE_open.inter
                              (hUsrc_open.preimage
                                eflat.symm.continuous)).inter
                                Metric.isOpen_ball).inter
                                (A0.carrier_open.preimage hzWick_cont)).inter
                                (A1.carrier_open.preimage hzCommon_cont)).inter
                                (hUcorr_open.preimage hzWick_cont)).inter
                                (hUcorr_open.preimage hzCommon_cont)
                        · exact
                            ⟨⟨⟨⟨⟨⟨hK0_E y.property,
                                  hK0_preimage_Usrc
                                    (y : BHW.OS45FlatCommonChartReal d n)
                                    y.property⟩,
                                Metric.mem_ball_self
                                  (by norm_num : (0 : ℝ) < 1)⟩,
                              by simpa [zWick, hA0_center] using hA0_mem⟩,
                              by simpa [zCommon, hA1_center] using hA1_mem⟩,
                              by simpa [zWick, uy, hA0_center] using
                                hUcorr_wick⟩,
                              by simpa [zCommon, uy, hA1_center] using
                                hUcorr_common⟩
                        · refine ⟨y.1, (1 : ℝ), ?_⟩
                          intro z hz
                          rcases hz with
                            ⟨⟨⟨⟨⟨⟨_hzE, _hzUsrc⟩, hzball⟩,
                                  _hzA0⟩, _hzA1⟩, _hzCorrW⟩, _hzCorrC⟩
                          exact Metric.ball_subset_closedBall hzball
                        · intro z hz
                          rcases hz with
                            ⟨⟨⟨⟨⟨⟨hzE, _hzUsrc⟩, _hzball⟩,
                                  _hzA0⟩, _hzA1⟩, _hzCorrW⟩, _hzCorrC⟩
                          exact hE_sub hzE
                        · constructor
                          · rintro u ⟨z, hz, rfl⟩
                            rcases hz with
                              ⟨⟨⟨⟨⟨⟨_hzE, hzUsrc⟩, _hzball⟩,
                                    _hzA0⟩, _hzA1⟩, _hzCorrW⟩, _hzCorrC⟩
                            exact hzUsrc
                          · exact
                              ⟨A0, A1, hA0_center, hA0_mem, hA0_sub,
                                hA0_model, hA0_trace, hA1_center, hA1_mem,
                                hA1_sub, hA1_model, hA1_trace,
                                (by
                                  intro x hx
                                  rcases hx with
                                    ⟨⟨⟨⟨⟨⟨_hxE, _hxUsrc⟩, _hxball⟩,
                                          hxA0⟩, _hxA1⟩, _hxCorrW⟩,
                                      _hxCorrC⟩
                                  exact hxA0),
                                (by
                                  intro x hx
                                  rcases hx with
                                    ⟨⟨⟨⟨⟨⟨_hxE, _hxUsrc⟩, _hxball⟩,
                                          _hxA0⟩, hxA1⟩, _hxCorrW⟩,
                                      _hxCorrC⟩
                                  exact hxA1),
                                ⟨Ucorr, hUcorr_open, hUcorr_connected,
                                  by simpa [uy] using hUcorr_wick,
                                  by simpa [uy] using hUcorr_common,
                                  hUcorr_sub,
                                  (by
                                    intro x hx
                                    rcases hx with
                                      ⟨⟨⟨⟨⟨⟨_hxE, _hxUsrc⟩, _hxball⟩,
                                            _hxA0⟩, _hxA1⟩, hxCorrW⟩,
                                        _hxCorrC⟩
                                    exact hxCorrW),
                                  (by
                                    intro x hx
                                    rcases hx with
                                      ⟨⟨⟨⟨⟨⟨_hxE, _hxUsrc⟩, _hxball⟩,
                                            _hxA0⟩, _hxA1⟩, _hxCorrW⟩,
                                        hxCorrC⟩
                                    exact hxCorrC),
                                  hUcorr_chart⟩⟩
                      obtain ⟨sOrd, hsOrd_cover⟩ :=
                        hK0_compact.elim_finite_subcover
                          (fun y : K0 =>
                            Classical.choose (hOrd_local_cover_data y))
                          (fun y =>
                            (Classical.choose_spec
                              (hOrd_local_cover_data y)).1)
                          (by
                            intro x hx
                            exact Set.mem_iUnion.mpr
                              ⟨⟨x, hx⟩,
                                (Classical.choose_spec
                                  (hOrd_local_cover_data ⟨x, hx⟩)).2.1⟩)
                      let αOrd := sOrd
                      let UOrdloc : αOrd →
                          Set (BHW.OS45FlatCommonChartReal d n) := fun a =>
                        Classical.choose (hOrd_local_cover_data a.1)
                      have hUOrdloc_open : ∀ a : αOrd, IsOpen (UOrdloc a) := by
                        intro a
                        exact
                          (Classical.choose_spec
                            (hOrd_local_cover_data a.1)).1
                      have hUOrdloc_relcompact :
                          ∀ a : αOrd, ∃ c R, UOrdloc a ⊆
                            Metric.closedBall c R := by
                        intro a
                        exact
                          (Classical.choose_spec
                            (hOrd_local_cover_data a.1)).2.2.1
                      have hUOrdloc_edge :
                          ∀ a : αOrd, UOrdloc a ⊆
                            BHW.os45FlatCommonChartEdgeSet d n P
                              (1 : Equiv.Perm (Fin n)) := by
                        intro a
                        exact
                          (Classical.choose_spec
                            (hOrd_local_cover_data a.1)).2.2.2.1
                      have hUOrdloc_source :
                          ∀ a : αOrd, eflat.symm '' UOrdloc a ⊆ Usrc := by
                        intro a
                        exact
                          (Classical.choose_spec
                            (hOrd_local_cover_data a.1)).2.2.2.2.1
                      have hcoverOrd_K0 :
                          K0 ⊆ ⋃ a : αOrd, UOrdloc a := by
                        intro x hx
                        have hxcover := hsOrd_cover hx
                        rcases Set.mem_iUnion.mp hxcover with ⟨y, hycover⟩
                        rcases Set.mem_iUnion.mp hycover with ⟨hys, hxy⟩
                        exact Set.mem_iUnion.mpr ⟨⟨y, hys⟩, hxy⟩
                      obtain ⟨χOrd, hχOrd_compact, hχOrd_sub, hχOrd_sum⟩ :=
                        SCV.exists_finite_schwartz_partitionOfUnity_on_compact
                          (E := BHW.OS45FlatCommonChartReal d n)
                          hK0_compact hUOrdloc_open hUOrdloc_relcompact
                          hcoverOrd_K0
                      let ψOrdPieceFlat : αOrd →
                          SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ :=
                        fun a =>
                          SchwartzMap.smulLeftCLM ℂ
                            (χOrd a :
                              BHW.OS45FlatCommonChartReal d n → ℂ)
                            ψ0Flat
                      have hψOrdFlat_sum :
                          ψ0Flat = ∑ a : αOrd, ψOrdPieceFlat a := by
                        simpa [ψOrdPieceFlat] using
                          SCV.schwartzMap_eq_finset_sum_smulLeftCLM_of_sum_eq_one_on_tsupport
                            (Finset.univ : Finset αOrd) χOrd ψ0Flat
                            (by
                              intro x hx
                              simpa using hχOrd_sum x hx)
                      let pullOrdFlat :
                          SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ]
                            SchwartzNPoint d n :=
                        SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eflat
                      let χOrdSource : αOrd → SchwartzNPoint d n := fun a =>
                        pullOrdFlat (χOrd a)
                      let ψOrdPieceSource : αOrd → SchwartzNPoint d n := fun a =>
                        pullOrdFlat (ψOrdPieceFlat a)
                      have hpullOrdFlat_ψ0 :
                          pullOrdFlat ψ0Flat = ψ0 := by
                        ext u
                        simp [pullOrdFlat, ψ0Flat, eflat,
                          SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
                      have hψOrdPieceSource_smul :
                          ∀ a : αOrd,
                            ψOrdPieceSource a =
                              SchwartzMap.smulLeftCLM ℂ
                                (χOrdSource a) ψ0 := by
                        intro a
                        have hχ_comp :
                            (((χOrdSource a : SchwartzNPoint d n) :
                                NPointDomain d n → ℂ) ∘ eflat.symm) =
                              ((χOrd a :
                                SchwartzMap
                                  (BHW.OS45FlatCommonChartReal d n) ℂ) :
                                BHW.OS45FlatCommonChartReal d n → ℂ) := by
                          funext x
                          simp [χOrdSource, pullOrdFlat,
                            SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
                        have hcomp :=
                          SchwartzMap.smulLeftCLM_compCLMOfContinuousLinearEquiv
                            (𝕜 := ℂ) (𝕜' := ℂ)
                            (D := NPointDomain d n)
                            (E := BHW.OS45FlatCommonChartReal d n)
                            (F := ℂ)
                            (u := ((χOrdSource a : SchwartzNPoint d n) :
                              NPointDomain d n → ℂ))
                            (χOrdSource a).hasTemperateGrowth
                            eflat ψ0Flat
                        calc
                          ψOrdPieceSource a =
                              pullOrdFlat (ψOrdPieceFlat a) := rfl
                          _ =
                              pullOrdFlat
                                (SchwartzMap.smulLeftCLM ℂ
                                  (((χOrdSource a : SchwartzNPoint d n) :
                                    NPointDomain d n → ℂ) ∘ eflat.symm)
                                  ψ0Flat) := by
                                simp [ψOrdPieceFlat, hχ_comp]
                          _ =
                              SchwartzMap.smulLeftCLM ℂ
                                (χOrdSource a) (pullOrdFlat ψ0Flat) := by
                                simpa [pullOrdFlat] using hcomp.symm
                          _ =
                              SchwartzMap.smulLeftCLM ℂ
                                (χOrdSource a) ψ0 := by
                                rw [hpullOrdFlat_ψ0]
                      have hψOrdPieceSource_zd :
                          ∀ a : αOrd,
                            VanishesToInfiniteOrderOnCoincidence
                              (ψOrdPieceSource a) := by
                        intro a
                        have hψ0_zd :
                            VanishesToInfiniteOrderOnCoincidence ψ0 :=
                          (D.toZeroDiagonalCLM
                            (1 : Equiv.Perm (Fin n)) φ).property
                        rw [hψOrdPieceSource_smul a]
                        exact
                          VanishesToInfiniteOrderOnCoincidence.smulLeft_schwartzNPoint
                            hψ0_zd
                      let ψOrdPieceZD : αOrd → ZeroDiagonalSchwartz d n :=
                        fun a => ⟨ψOrdPieceSource a, hψOrdPieceSource_zd a⟩
                      have hψOrdSource_sum :
                          (∑ a : αOrd, ψOrdPieceSource a) = ψ0 := by
                        calc
                          (∑ a : αOrd, ψOrdPieceSource a)
                              = pullOrdFlat (∑ a : αOrd,
                                  ψOrdPieceFlat a) := by
                                simp [ψOrdPieceSource, pullOrdFlat,
                                  map_sum]
                          _ = pullOrdFlat ψ0Flat := by
                                rw [← hψOrdFlat_sum]
                          _ = ψ0 := hpullOrdFlat_ψ0
                      have hψOrdZD_sum :
                          (∑ a : αOrd, ψOrdPieceZD a) =
                            D.toZeroDiagonalCLM
                              (1 : Equiv.Perm (Fin n)) φ := by
                        apply Subtype.ext
                        change
                          (zeroDiagonalSubmodule d n).subtype
                            (∑ a : αOrd, ψOrdPieceZD a) = ψ0
                        rw [_root_.map_sum]
                        simpa [ψOrdPieceZD, ψ0] using hψOrdSource_sum
                      have hOrd_flat_integrable :
                          ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
                            Integrable
                            (fun x : BHW.OS45FlatCommonChartReal d n =>
                            BHW.os45FlatCommonChartBranch d n OS lgc
                              (1 : Equiv.Perm (Fin n))
                              (fun j =>
                                ((x + ((1 : ℝ) * ε) • η0) j : ℂ) +
                                  ((((1 : ℝ) * ε) • η0) j : ℂ) *
                                    Complex.I) *
                              (SCV.translateSchwartz
                                (-((1 : ℝ) * ε) • η0) ψ0Flat)
                                (x + ((1 : ℝ) * ε) • η0)) := by
                        have hψ0Flat_omega :
                            ∀ x ∈ tsupport
                                (ψ0Flat :
                                  BHW.OS45FlatCommonChartReal d n → ℂ),
                              (fun j => (x j : ℂ)) ∈
                                BHW.os45FlatCommonChartOmega d n
                                  (1 : Equiv.Perm (Fin n)) := by
                          intro x hx
                          exact
                            BHW.os45FlatCommonChart_real_mem_omega_id
                              (d := d) hd (P := P) x
                              (hψ0Flat_packet.2 hx)
                        simpa [one_mul] using
                          BHW.os45FlatCommonChart_fixedTranslatedTest_integrable_eventually
                            (d := d) (n := n) OS lgc
                            (1 : Equiv.Perm (Fin n)) (1 : ℝ)
                            η0 ψ0Flat hψ0Flat_packet.1 hψ0Flat_omega
                      have hOrd_flat_eq_fixed :
                          (fun ε : ℝ =>
                            ∫ x : BHW.OS45FlatCommonChartReal d n,
                              BHW.os45FlatCommonChartBranch d n OS lgc
                                (1 : Equiv.Perm (Fin n))
                                (fun j =>
                                  (x j : ℂ) +
                                    ((((1 : ℝ) * ε) • η0) j : ℂ) *
                                      Complex.I) *
                              (SCV.translateSchwartz
                                (-((1 : ℝ) * ε) • η0) ψ0Flat) x)
                            =ᶠ[𝓝[Set.Ioi 0] (0 : ℝ)]
                          fun ε : ℝ => J * OrdFixed ε := by
                        filter_upwards [hOrd_flat_integrable] with ε hε
                        have heq :=
                          BHW.os45FlatCommonChart_branch_integral_eq_sourceSide_extendF_translatedTest
                            (d := d) (n := n) OS lgc
                            (1 : Equiv.Perm (Fin n))
                            (1 : Equiv.Perm (Fin n))
                            (1 : ℝ) ε η0 ψ0Flat hε
                        simpa [OrdFixed, J, ψ0Flat, eflat,
                          SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
                          one_mul] using heq
                      have hflatOrd_selected :
                          Tendsto
                            (fun ε : ℝ =>
                              ∫ x : BHW.OS45FlatCommonChartReal d n,
                                BHW.os45FlatCommonChartBranch d n OS lgc
                                  (1 : Equiv.Perm (Fin n))
                                  (fun j =>
                                    (x j : ℂ) +
                                      ((((1 : ℝ) * ε) • η0) j : ℂ) *
                                        Complex.I) *
                                (SCV.translateSchwartz
                                  (-((1 : ℝ) * ε) • η0) ψ0Flat) x)
                            (𝓝[Set.Ioi 0] (0 : ℝ))
                            (𝓝
                              (J * OS.S n (D.toZeroDiagonalCLM
                                (1 : Equiv.Perm (Fin n)) φ))) := by
                        /-
                        Ordinary finite flat translated-boundary selector.
                        The global fixed test has already been localized into
                        compact source pieces.  The remaining genuinely hard
                        obligations are the per-piece one-branch chart
                        transport and the finite integral-sum reconstruction.
                        -/
                        let FlatOrdPiece : αOrd → ℝ → ℂ := fun a ε =>
                          ∫ x : BHW.OS45FlatCommonChartReal d n,
                            BHW.os45FlatCommonChartBranch d n OS lgc
                              (1 : Equiv.Perm (Fin n))
                              (fun j =>
                                (x j : ℂ) +
                                  ((((1 : ℝ) * ε) • η0) j : ℂ) *
                                    Complex.I) *
                            (SCV.translateSchwartz
                              (-((1 : ℝ) * ε) • η0)
                              (ψOrdPieceFlat a)) x
                        have hψOrdPieceFlat_compact :
                            ∀ a : αOrd,
                              HasCompactSupport
                                (ψOrdPieceFlat a :
                                  BHW.OS45FlatCommonChartReal d n → ℂ) := by
                          intro a
                          refine hψ0Flat_packet.1.mono' ?_
                          intro x hx
                          have hx_ts :
                              x ∈ tsupport
                                (ψOrdPieceFlat a :
                                  BHW.OS45FlatCommonChartReal d n → ℂ) :=
                            subset_closure hx
                          exact
                            ((SchwartzMap.tsupport_smulLeftCLM_subset
                              (F := ℂ)
                              (g := (χOrd a :
                                BHW.OS45FlatCommonChartReal d n → ℂ))
                              (f := ψ0Flat)) hx_ts).1
                        have hψOrdPieceFlat_omega :
                            ∀ a : αOrd,
                              ∀ x ∈ tsupport
                                  (ψOrdPieceFlat a :
                                    BHW.OS45FlatCommonChartReal d n → ℂ),
                                (fun j => (x j : ℂ)) ∈
                                  BHW.os45FlatCommonChartOmega d n
                                    (1 : Equiv.Perm (Fin n)) := by
                          intro a x hx
                          have hx0 :
                              x ∈ tsupport
                                (ψ0Flat :
                                  BHW.OS45FlatCommonChartReal d n → ℂ) :=
                            ((SchwartzMap.tsupport_smulLeftCLM_subset
                              (F := ℂ)
                              (g := (χOrd a :
                                BHW.OS45FlatCommonChartReal d n → ℂ))
                              (f := ψ0Flat)) hx).1
                          exact
                            BHW.os45FlatCommonChart_real_mem_omega_id
                              (d := d) hd (P := P) x
                              (hψ0Flat_packet.2 hx0)
                        have hOrd_piece_shifted_integrable :
                            ∀ a : αOrd,
                              ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
                                Integrable
                                (fun x :
                                  BHW.OS45FlatCommonChartReal d n =>
                                BHW.os45FlatCommonChartBranch d n OS lgc
                                  (1 : Equiv.Perm (Fin n))
                                  (fun j =>
                                    ((x + ((1 : ℝ) * ε) • η0) j : ℂ) +
                                      ((((1 : ℝ) * ε) • η0) j : ℂ) *
                                        Complex.I) *
                                  (SCV.translateSchwartz
                                    (-((1 : ℝ) * ε) • η0)
                                    (ψOrdPieceFlat a))
                                    (x + ((1 : ℝ) * ε) • η0)) := by
                          intro a
                          simpa [one_mul] using
                            BHW.os45FlatCommonChart_fixedTranslatedTest_integrable_eventually
                              (d := d) (n := n) OS lgc
                              (1 : Equiv.Perm (Fin n)) (1 : ℝ)
                              η0 (ψOrdPieceFlat a)
                              (hψOrdPieceFlat_compact a)
                              (hψOrdPieceFlat_omega a)
                        have hOrd_piece_integrable :
                            ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
                              ∀ a : αOrd,
                                Integrable
                                (fun x :
                                  BHW.OS45FlatCommonChartReal d n =>
                                BHW.os45FlatCommonChartBranch d n OS lgc
                                  (1 : Equiv.Perm (Fin n))
                                  (fun j =>
                                    (x j : ℂ) +
                                      ((((1 : ℝ) * ε) • η0) j : ℂ) *
                                        Complex.I) *
                                  (SCV.translateSchwartz
                                    (-((1 : ℝ) * ε) • η0)
                                    (ψOrdPieceFlat a)) x) := by
                          have hall_shifted :
                              ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
                                ∀ a : αOrd,
                                  Integrable
                                  (fun x :
                                    BHW.OS45FlatCommonChartReal d n =>
                                  BHW.os45FlatCommonChartBranch d n OS lgc
                                    (1 : Equiv.Perm (Fin n))
                                    (fun j =>
                                      ((x + ((1 : ℝ) * ε) • η0) j : ℂ) +
                                        ((((1 : ℝ) * ε) • η0) j : ℂ) *
                                          Complex.I) *
                                    (SCV.translateSchwartz
                                      (-((1 : ℝ) * ε) • η0)
                                      (ψOrdPieceFlat a))
                                      (x + ((1 : ℝ) * ε) • η0)) :=
                            Filter.eventually_all.mpr
                              hOrd_piece_shifted_integrable
                          filter_upwards [hall_shifted] with ε hε a
                          let s : BHW.OS45FlatCommonChartReal d n :=
                            ((1 : ℝ) * ε) • η0
                          have hcomp := (hε a).comp_add_right (-s)
                          refine hcomp.congr (Filter.Eventually.of_forall ?_)
                          intro x
                          simp [s, one_mul, add_assoc, add_left_comm,
                            add_comm]
                        have hψOrdPieceFlat_sub_U :
                            ∀ a : αOrd,
                              tsupport
                                  (ψOrdPieceFlat a :
                                    BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
                                UOrdloc a := by
                          intro a x hx
                          exact
                            hχOrd_sub a
                              ((SchwartzMap.tsupport_smulLeftCLM_subset
                                (F := ℂ)
                                (g := (χOrd a :
                                  BHW.OS45FlatCommonChartReal d n → ℂ))
                                (f := ψ0Flat)) hx).2
                        have hψOrdPieceSource_compact :
                            ∀ a : αOrd,
                              HasCompactSupport
                                (ψOrdPieceSource a :
                                  NPointDomain d n → ℂ) := by
                          intro a
                          simpa [ψOrdPieceSource, pullOrdFlat,
                            SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
                            using
                              (hψOrdPieceFlat_compact a).comp_homeomorph
                                eflat.toHomeomorph
                        have hψOrdPieceSource_Usrc :
                            ∀ a : αOrd,
                              tsupport
                                  (ψOrdPieceSource a :
                                    NPointDomain d n → ℂ) ⊆ Usrc := by
                          intro a u hu
                          have hu_flat :
                              eflat u ∈ tsupport
                                (ψOrdPieceFlat a :
                                  BHW.OS45FlatCommonChartReal d n → ℂ) := by
                            have hpre :=
                              tsupport_comp_subset_preimage
                                (ψOrdPieceFlat a :
                                  BHW.OS45FlatCommonChartReal d n → ℂ)
                                eflat.continuous
                            simpa [ψOrdPieceSource, pullOrdFlat,
                              SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
                              using hpre hu
                          exact
                            hUOrdloc_source a
                              ⟨eflat u,
                                hψOrdPieceFlat_sub_U a hu_flat,
                                by simp [eflat]⟩
                        have hflatOrd_piece :
                            ∀ a : αOrd,
                              Tendsto (FlatOrdPiece a)
                                (𝓝[Set.Ioi 0] (0 : ℝ))
                                (𝓝 (J * OS.S n (ψOrdPieceZD a))) := by
                          intro a
                          let OrdPieceFixed : ℝ → ℂ := fun ε =>
                            ∫ u : NPointDomain d n,
                              BHW.extendF (bvt_F OS lgc n)
                                (BHW.os45FlatCommonChartSourceSide d n
                                  (1 : Equiv.Perm (Fin n)) (1 : ℝ)
                                  ε η0 u) *
                              (ψOrdPieceSource a : NPointDomain d n → ℂ) u
                          have hFlat_piece_eq_fixed :
                              FlatOrdPiece a
                                =ᶠ[𝓝[Set.Ioi 0] (0 : ℝ)]
                              fun ε : ℝ => J * OrdPieceFixed ε := by
                            filter_upwards
                              [hOrd_piece_shifted_integrable a] with ε hε
                            have heq :=
                              BHW.os45FlatCommonChart_branch_integral_eq_sourceSide_extendF_translatedTest
                                (d := d) (n := n) OS lgc
                                (1 : Equiv.Perm (Fin n))
                                (1 : Equiv.Perm (Fin n))
                                (1 : ℝ) ε η0 (ψOrdPieceFlat a) hε
                            have hsource :
                                (∫ u : NPointDomain d n,
                                  BHW.extendF (bvt_F OS lgc n)
                                    (BHW.permAct (d := d)
                                      (1 : Equiv.Perm (Fin n)).symm
                                      (BHW.os45FlatCommonChartSourceSide d n
                                        (1 : Equiv.Perm (Fin n)) (1 : ℝ)
                                        ε η0 u)) *
                                (ψOrdPieceFlat a)
                                    (BHW.os45CommonEdgeFlatCLE d n
                                      (1 : Equiv.Perm (Fin n)) u)) =
                                OrdPieceFixed ε := by
                              apply integral_congr_ae
                              refine Filter.Eventually.of_forall ?_
                              intro u
                              let zss : Fin n → Fin (d + 1) → ℂ :=
                                BHW.os45FlatCommonChartSourceSide d n
                                  (1 : Equiv.Perm (Fin n)) (1 : ℝ)
                                  ε η0 u
                              have hperm :
                                  BHW.permAct (d := d)
                                      (1 : Equiv.Perm (Fin n)).symm
                                      zss = zss := by
                                change
                                  BHW.permAct (d := d)
                                      (1 : Equiv.Perm (Fin n)) zss = zss
                                ext k μ
                                simp [BHW.permAct]
                              have hψu :
                                  (ψOrdPieceFlat a)
                                      (BHW.os45CommonEdgeFlatCLE d n
                                        (1 : Equiv.Perm (Fin n)) u) =
                                    (ψOrdPieceSource a :
                                      NPointDomain d n → ℂ) u := by
                                simp [ψOrdPieceSource, pullOrdFlat, eflat,
                                  SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
                              change
                                BHW.extendF (bvt_F OS lgc n)
                                      (BHW.permAct (d := d)
                                        (1 : Equiv.Perm (Fin n)).symm zss) *
                                    (ψOrdPieceFlat a)
                                      (BHW.os45CommonEdgeFlatCLE d n
                                        (1 : Equiv.Perm (Fin n)) u) =
                                  BHW.extendF (bvt_F OS lgc n) zss *
                                    (ψOrdPieceSource a :
                                      NPointDomain d n → ℂ) u
                              rw [hperm, hψu]
                            simpa [FlatOrdPiece, J, hsource] using heq
                          let ua : NPointDomain d n :=
                            eflat.symm
                              (a.1 : BHW.OS45FlatCommonChartReal d n)
                          have hua_P : ua ∈ P.V := by
                            have hya :
                                (a.1 :
                                  BHW.OS45FlatCommonChartReal d n) ∈ K0 :=
                              a.1.property
                            simpa [ua] using
                              hK0_preimage_P
                                (a.1 :
                                  BHW.OS45FlatCommonChartReal d n) hya
                          have hOrd_piece_join :
                              JoinedIn
                                (BHW.ExtendedTube d n ∩
                                  BHW.permutedExtendedTubeSector d n P.τ)
                                (fun k => wickRotatePoint (ua k))
                                ((BHW.os45QuarterTurnCLE
                                  (d := d) (n := n)).symm
                                  (BHW.realEmbed
                                    (BHW.os45CommonEdgeRealPoint
                                      (d := d) (n := n)
                                      (1 : Equiv.Perm (Fin n)) ua))) := by
                            simpa [ua] using
                              BHW.os45Figure24_joined_ordinaryWick_to_commonEdge_initialSectorOverlap
                                (d := d) (n := n) (hd := hd) (P := P)
                                (x := ua) (subset_closure hua_P)
                          obtain
                            ⟨UcorrOrd, hUcorrOrd_open, hUcorrOrd_connected,
                              hUcorrOrd_wick, hUcorrOrd_common,
                              hUcorrOrd_sub⟩ :=
                            BHW.initialSectorOverlap_connectedNeighborhood_of_joinedIn
                              (d := d) (n := n) P.τ hOrd_piece_join
                          have hUcorrOrd_sub_hull :
                              UcorrOrd ⊆ BHW.ExtendedTube d n ∩ H.ΩJ := by
                            intro z hz
                            have hzET : z ∈ BHW.ExtendedTube d n :=
                              (hUcorrOrd_sub hz).1
                            exact ⟨hzET, H.extendedTube_subset_ΩJ hzET⟩
                          have hOrd_corridor_chart :
                              ∀ z ∈ UcorrOrd,
                                ∃ A : PointedMetricBranchChart
                                    (Fin n → Fin (d + 1) → ℂ) ℂ,
                                  A.center = z ∧
                                  A.center ∈ A.carrier ∧
                                  A.carrier ⊆
                                    (BHW.ExtendedTube d n ∩ H.ΩJ) ∩
                                      UcorrOrd ∧
                                  Set.EqOn A.branch
                                    (BHW.extendF (bvt_F OS lgc n))
                                    A.carrier := by
                            intro z hz
                            let Ωcorr :
                                Set (Fin n → Fin (d + 1) → ℂ) :=
                              (BHW.ExtendedTube d n ∩ H.ΩJ) ∩ UcorrOrd
                            have hΩcorr_open : IsOpen Ωcorr := by
                              simpa [Ωcorr] using
                                (BHW.isOpen_extendedTube.inter
                                  H.ΩJ_open).inter hUcorrOrd_open
                            have hzΩcorr : z ∈ Ωcorr := by
                              exact ⟨hUcorrOrd_sub_hull hz, hz⟩
                            rcases Metric.mem_nhds_iff.mp
                                (hΩcorr_open.mem_nhds hzΩcorr) with
                              ⟨r, hr_pos, hball_sub⟩
                            let A : PointedMetricBranchChart
                                (Fin n → Fin (d + 1) → ℂ) ℂ :=
                              { center := z
                                radius := r
                                radius_pos := hr_pos
                                branch := BHW.extendF (bvt_F OS lgc n)
                                holo := by
                                  exact
                                    (BHW.differentiableOn_extendF_bvt_F_extendedTube
                                      (d := d) OS lgc n).mono
                                      (by
                                        intro w hw
                                        exact
                                          (hball_sub hw).1.1) }
                            refine ⟨A, rfl, ?_, ?_, ?_⟩
                            · simpa [A] using A.center_mem
                            · intro w hw
                              exact
                                hball_sub
                                  (by
                                    simpa [A,
                                      PointedMetricBranchChart.carrier] using hw)
                            · intro _w _hw
                              rfl
                          /-
                          Genuine remaining ordinary fixed flat selector for
                          this compact piece.  This must be proved from the
                          ordinary `(4.1)` incoming OS-I ray and the finite
                          one-branch Figure-2-4 chain.  The terminal
                          source-side DCT is used only after this flat selector
                          has picked the current.
                          -/
                          have hψOrdPieceFlat_edge :
                              tsupport
                                  (ψOrdPieceFlat a :
                                    BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
                                BHW.os45FlatCommonChartEdgeSet d n P
                                  (1 : Equiv.Perm (Fin n)) :=
                            (hψOrdPieceFlat_sub_U a).trans
                              (hUOrdloc_edge a)
                          have hD_piece_plain :
                              D.toSchwartzNPointCLM
                                  (1 : Equiv.Perm (Fin n))
                                  (ψOrdPieceFlat a) =
                                ψOrdPieceSource a := by
                            ext u
                            have hplain :=
                              D.toSchwartzNPointCLM_eq_plain_of_tsupport_subset_edge
                                (1 : Equiv.Perm (Fin n))
                                (ψOrdPieceFlat a) hψOrdPieceFlat_edge u
                            simpa [ψOrdPieceSource, pullOrdFlat, eflat,
                              SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
                              using hplain
                          have hD_piece_zd :
                              D.toZeroDiagonalCLM
                                  (1 : Equiv.Perm (Fin n))
                                  (ψOrdPieceFlat a) =
                                ψOrdPieceZD a := by
                            apply Subtype.ext
                            change
                              D.toSchwartzNPointCLM
                                  (1 : Equiv.Perm (Fin n))
                                  (ψOrdPieceFlat a) =
                                ψOrdPieceSource a
                            exact hD_piece_plain
                          have hOrdPieceFixed_endpoint :
                              Tendsto OrdPieceFixed
                                (𝓝[Set.Ioi 0] (0 : ℝ))
                                (𝓝
                                  (∫ u : NPointDomain d n,
                                    BHW.extendF (bvt_F OS lgc n)
                                      (BHW.os45FlatCommonChartSourceSide d n
                                        (1 : Equiv.Perm (Fin n)) (1 : ℝ)
                                        0 η0 u) *
                                    (ψOrdPieceSource a :
                                      NPointDomain d n → ℂ) u)) := by
                            have h0_piece :
                                ∀ u ∈ tsupport
                                    (ψOrdPieceSource a :
                                      NPointDomain d n → ℂ),
                                  BHW.os45FlatCommonChartSourceSide d n
                                    (1 : Equiv.Perm (Fin n)) (1 : ℝ)
                                    0 η0 u ∈ BHW.ExtendedTube d n := by
                              intro u hu
                              exact h0 u
                                (hUsrc_sub_Ksrc
                                  (hψOrdPieceSource_Usrc a hu))
                            simpa [OrdPieceFixed] using
                              BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_of_hasCompactSupport
                                (d := d) (n := n)
                                (1 : Equiv.Perm (Fin n)) (1 : ℝ) η0
                                (U := BHW.ExtendedTube d n)
                                BHW.isOpen_extendedTube hF_cont
                                (hψOrdPieceSource_compact a)
                                (ψOrdPieceSource a : SchwartzNPoint d n).continuous
                                h0_piece
                          have hUOrdloc_chart_data :
                              ∃ A0 A1 : PointedMetricBranchChart
                                  (Fin n → Fin (d + 1) → ℂ) ℂ,
                                A0.center =
                                    (fun k =>
                                      wickRotatePoint ((eflat.symm a.1.1) k)) ∧
                                A0.center ∈ A0.carrier ∧
                                A0.carrier ⊆
                                    (BHW.ExtendedTube d n ∩ H.ΩJ) ∩
                                      Set.univ ∧
                                Set.EqOn A0.branch
                                  (BHW.extendF (bvt_F OS lgc n)) A0.carrier ∧
                                A0.branch A0.center =
                                  bvt_F OS lgc n
                                    (fun k =>
                                      wickRotatePoint ((eflat.symm a.1.1) k)) ∧
                                A1.center =
                                    (BHW.os45QuarterTurnCLE
                                      (d := d) (n := n)).symm
                                      (BHW.realEmbed
                                        (BHW.os45CommonEdgeRealPoint
                                          (d := d) (n := n)
                                          (1 : Equiv.Perm (Fin n))
                                          (eflat.symm a.1.1))) ∧
                                A1.center ∈ A1.carrier ∧
                                A1.carrier ⊆
                                    (BHW.ExtendedTube d n ∩ H.ΩJ) ∩
                                      Set.univ ∧
                                Set.EqOn A1.branch
                                  (BHW.extendF (bvt_F OS lgc n)) A1.carrier ∧
                                A1.branch A1.center =
                                  BHW.os45PulledRealBranch
                                    (d := d) (n := n) OS lgc
                                    (1 : Equiv.Perm (Fin n))
                                    (BHW.realEmbed
                                      (BHW.os45CommonEdgeRealPoint
                                        (d := d) (n := n)
                                        (1 : Equiv.Perm (Fin n))
                                        (eflat.symm a.1.1))) ∧
                                (∀ x ∈ UOrdloc a,
                                  (fun k =>
                                    wickRotatePoint ((eflat.symm x) k)) ∈
                                      A0.carrier) ∧
                                (∀ x ∈ UOrdloc a,
                                  (BHW.os45QuarterTurnCLE
                                    (d := d) (n := n)).symm
                                    (BHW.realEmbed
                                      (BHW.os45CommonEdgeRealPoint
                                        (d := d) (n := n)
                                        (1 : Equiv.Perm (Fin n))
                                        (eflat.symm x))) ∈
                                      A1.carrier) ∧
                                ∃ Ucorr : Set
                                    (Fin n → Fin (d + 1) → ℂ),
                                  IsOpen Ucorr ∧
                                  IsConnected Ucorr ∧
                                  (fun k =>
                                    wickRotatePoint ((eflat.symm a.1.1) k)) ∈
                                    Ucorr ∧
                                  (BHW.os45QuarterTurnCLE
                                    (d := d) (n := n)).symm
                                    (BHW.realEmbed
                                      (BHW.os45CommonEdgeRealPoint
                                        (d := d) (n := n)
                                        (1 : Equiv.Perm (Fin n))
                                        (eflat.symm a.1.1))) ∈ Ucorr ∧
                                  Ucorr ⊆
                                    BHW.ExtendedTube d n ∩
                                      BHW.permutedExtendedTubeSector d n P.τ ∧
                                  (∀ x ∈ UOrdloc a,
                                    (fun k =>
                                      wickRotatePoint
                                        ((eflat.symm x) k)) ∈ Ucorr) ∧
                                  (∀ x ∈ UOrdloc a,
                                    (BHW.os45QuarterTurnCLE
                                      (d := d) (n := n)).symm
                                      (BHW.realEmbed
                                        (BHW.os45CommonEdgeRealPoint
                                          (d := d) (n := n)
                                          (1 : Equiv.Perm (Fin n))
                                          (eflat.symm x))) ∈ Ucorr) ∧
                                  ∀ z ∈ Ucorr,
                                    ∃ A : PointedMetricBranchChart
                                        (Fin n → Fin (d + 1) → ℂ) ℂ,
                                      A.center = z ∧
                                      A.center ∈ A.carrier ∧
                                      A.carrier ⊆
                                        (BHW.ExtendedTube d n ∩ H.ΩJ) ∩
                                          Ucorr ∧
                                      Set.EqOn A.branch
                                        (BHW.extendF (bvt_F OS lgc n))
                                        A.carrier := by
                            simpa [UOrdloc] using
                              (Classical.choose_spec
                                (hOrd_local_cover_data a.1)).2.2.2.2.2
                          obtain
                            ⟨A0a, A1a, _hA0a_center, _hA0a_mem,
                              _hA0a_sub, _hA0a_model, _hA0a_trace,
                              _hA1a_center, _hA1a_mem, _hA1a_sub,
                              hA1a_model, _hA1a_trace, hA0a_all,
                              hA1a_all, hOrd_corridor_packet⟩ :=
                            hUOrdloc_chart_data
                          have hOrd_piece_source_to_flat_tsupport :
                              ∀ u ∈ tsupport
                                  (ψOrdPieceSource a :
                                    NPointDomain d n → ℂ),
                                eflat u ∈ tsupport
                                  (ψOrdPieceFlat a :
                                    BHW.OS45FlatCommonChartReal d n → ℂ) := by
                            intro u hu
                            have hpre :=
                              tsupport_comp_subset_preimage
                                (ψOrdPieceFlat a :
                                  BHW.OS45FlatCommonChartReal d n → ℂ)
                                eflat.continuous
                            simpa [ψOrdPieceSource, pullOrdFlat,
                              SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
                              using hpre hu
                          have hOrd_piece_wick_in_A0 :
                              ∀ u ∈ tsupport
                                  (ψOrdPieceSource a :
                                    NPointDomain d n → ℂ),
                                (fun k => wickRotatePoint (u k)) ∈
                                  A0a.carrier := by
                            intro u hu
                            have hu_flat :=
                              hOrd_piece_source_to_flat_tsupport u hu
                            have hu_U :
                                eflat u ∈ UOrdloc a :=
                              hψOrdPieceFlat_sub_U a hu_flat
                            simpa [eflat] using
                              hA0a_all (eflat u) hu_U
                          have hOrd_piece_common_in_A1 :
                              ∀ u ∈ tsupport
                                  (ψOrdPieceSource a :
                                    NPointDomain d n → ℂ),
                                (BHW.os45QuarterTurnCLE
                                  (d := d) (n := n)).symm
                                  (BHW.realEmbed
                                    (BHW.os45CommonEdgeRealPoint
                                      (d := d) (n := n)
                                      (1 : Equiv.Perm (Fin n)) u)) ∈
                                  A1a.carrier := by
                            intro u hu
                            have hu_flat :=
                              hOrd_piece_source_to_flat_tsupport u hu
                            have hu_U :
                                eflat u ∈ UOrdloc a :=
                              hψOrdPieceFlat_sub_U a hu_flat
                            simpa [eflat] using
                              hA1a_all (eflat u) hu_U
                          obtain
                            ⟨UcorrPiece, hUcorrPiece_open,
                              hUcorrPiece_connected,
                              hUcorrPiece_wick_center,
                              hUcorrPiece_common_center,
                              hUcorrPiece_sub,
                              hUcorrPiece_wick_all,
                              hUcorrPiece_common_all,
                              hUcorrPiece_chart⟩ :=
                            hOrd_corridor_packet
                          have hOrd_piece_wick_in_corridor :
                              ∀ u ∈ tsupport
                                  (ψOrdPieceSource a :
                                    NPointDomain d n → ℂ),
                                (fun k => wickRotatePoint (u k)) ∈
                                  UcorrPiece := by
                            intro u hu
                            have hu_flat :=
                              hOrd_piece_source_to_flat_tsupport u hu
                            have hu_U :
                                eflat u ∈ UOrdloc a :=
                              hψOrdPieceFlat_sub_U a hu_flat
                            simpa [eflat] using
                              hUcorrPiece_wick_all (eflat u) hu_U
                          have hOrd_piece_common_in_corridor :
                              ∀ u ∈ tsupport
                                  (ψOrdPieceSource a :
                                    NPointDomain d n → ℂ),
                                (BHW.os45QuarterTurnCLE
                                  (d := d) (n := n)).symm
                                  (BHW.realEmbed
                                    (BHW.os45CommonEdgeRealPoint
                                      (d := d) (n := n)
                                      (1 : Equiv.Perm (Fin n)) u)) ∈
                                  UcorrPiece := by
                            intro u hu
                            have hu_flat :=
                              hOrd_piece_source_to_flat_tsupport u hu
                            have hu_U :
                                eflat u ∈ UOrdloc a :=
                              hψOrdPieceFlat_sub_U a hu_flat
                            simpa [eflat] using
                              hUcorrPiece_common_all (eflat u) hu_U
                          have hOrd_piece_sourceSide0_in_A1 :
                              ∀ u ∈ tsupport
                                  (ψOrdPieceSource a :
                                    NPointDomain d n → ℂ),
                                BHW.os45FlatCommonChartSourceSide d n
                                  (1 : Equiv.Perm (Fin n)) (1 : ℝ)
                                  0 η0 u ∈ A1a.carrier := by
                            intro u hu
                            rw [BHW.os45FlatCommonChartSourceSide_zero_eq_commonEdge]
                            exact hOrd_piece_common_in_A1 u hu
                          have hendpoint_to_terminal :
                              (∫ u : NPointDomain d n,
                                BHW.extendF (bvt_F OS lgc n)
                                  (BHW.os45FlatCommonChartSourceSide d n
                                    (1 : Equiv.Perm (Fin n)) (1 : ℝ)
                                    0 η0 u) *
                                (ψOrdPieceSource a :
                                  NPointDomain d n → ℂ) u) =
                              ∫ u : NPointDomain d n,
                                A1a.branch
                                  (BHW.os45FlatCommonChartSourceSide d n
                                    (1 : Equiv.Perm (Fin n)) (1 : ℝ)
                                    0 η0 u) *
                                (ψOrdPieceSource a :
                                  NPointDomain d n → ℂ) u := by
                            apply integral_congr_ae
                            refine Filter.Eventually.of_forall ?_
                            intro u
                            by_cases hu :
                                u ∈ tsupport
                                  (ψOrdPieceSource a :
                                    NPointDomain d n → ℂ)
                            · have hmodel :=
                                hA1a_model
                                  (hOrd_piece_sourceSide0_in_A1 u hu)
                              change
                                BHW.extendF (bvt_F OS lgc n)
                                    (BHW.os45FlatCommonChartSourceSide d n
                                      (1 : Equiv.Perm (Fin n)) (1 : ℝ)
                                      0 η0 u) *
                                  (ψOrdPieceSource a :
                                    NPointDomain d n → ℂ) u =
                                A1a.branch
                                    (BHW.os45FlatCommonChartSourceSide d n
                                      (1 : Equiv.Perm (Fin n)) (1 : ℝ)
                                      0 η0 u) *
                                  (ψOrdPieceSource a :
                                    NPointDomain d n → ℂ) u
                              rw [← hmodel]
                            · have hzero :
                                  (ψOrdPieceSource a :
                                    NPointDomain d n → ℂ) u = 0 :=
                                image_eq_zero_of_notMem_tsupport hu
                              simp [hzero]
                          have hOrdPieceFixed_terminal :
                              OrdPieceFixed
                                =ᶠ[𝓝[Set.Ioi 0] (0 : ℝ)]
                              fun ε : ℝ =>
                                ∫ u : NPointDomain d n,
                                  A1a.branch
                                    (BHW.os45FlatCommonChartSourceSide d n
                                      (1 : Equiv.Perm (Fin n)) (1 : ℝ)
                                      ε η0 u) *
                                  (ψOrdPieceSource a :
                                    NPointDomain d n → ℂ) u := by
                            have hmem :
                                ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
                                  ∀ u ∈ tsupport
                                      (ψOrdPieceSource a :
                                        NPointDomain d n → ℂ),
                                    BHW.os45FlatCommonChartSourceSide d n
                                      (1 : Equiv.Perm (Fin n)) (1 : ℝ)
                                      ε η0 u ∈ A1a.carrier :=
                              BHW.eventually_forall_os45FlatCommonChartSourceSide_mem_of_compact
                                (d := d) (n := n)
                                (1 : Equiv.Perm (Fin n)) (1 : ℝ) η0
                                (hψOrdPieceSource_compact a).isCompact
                                A1a.carrier_open
                                hOrd_piece_sourceSide0_in_A1
                            filter_upwards [hmem] with ε hε
                            apply integral_congr_ae
                            refine Filter.Eventually.of_forall ?_
                            intro u
                            by_cases hu :
                                u ∈ Function.support
                                  (ψOrdPieceSource a :
                                    NPointDomain d n → ℂ)
                            · have huK :
                                  u ∈ tsupport
                                    (ψOrdPieceSource a :
                                      NPointDomain d n → ℂ) :=
                                subset_tsupport _ hu
                              have hmodel :=
                                hA1a_model (hε u huK)
                              change
                                BHW.extendF (bvt_F OS lgc n)
                                    (BHW.os45FlatCommonChartSourceSide d n
                                      (1 : Equiv.Perm (Fin n)) (1 : ℝ)
                                      ε η0 u) *
                                  (ψOrdPieceSource a :
                                    NPointDomain d n → ℂ) u =
                                A1a.branch
                                    (BHW.os45FlatCommonChartSourceSide d n
                                      (1 : Equiv.Perm (Fin n)) (1 : ℝ)
                                      ε η0 u) *
                                  (ψOrdPieceSource a :
                                    NPointDomain d n → ℂ) u
                              rw [← hmodel]
                            · have hzero :
                                  (ψOrdPieceSource a :
                                    NPointDomain d n → ℂ) u = 0 := by
                                by_contra hne
                                exact hu (by
                                  simpa [Function.mem_support] using hne)
                              simp [hzero]
                          have hOrdWick_value :
                              (∫ u : NPointDomain d n,
                                bvt_F OS lgc n
                                  (fun k => wickRotatePoint (u k)) *
                                (ψOrdPieceSource a :
                                  NPointDomain d n → ℂ) u) =
                              OS.S n (ψOrdPieceZD a) := by
                            simpa [ψOrdPieceZD] using
                              (bvt_euclidean_restriction
                                (d := d) OS lgc n (ψOrdPieceZD a)).symm
                          have hOrdWick_to_A0 :
                              (∫ u : NPointDomain d n,
                                A0a.branch
                                  (fun k => wickRotatePoint (u k)) *
                                (ψOrdPieceSource a :
                                  NPointDomain d n → ℂ) u) =
                              ∫ u : NPointDomain d n,
                                bvt_F OS lgc n
                                  (fun k => wickRotatePoint (u k)) *
                                (ψOrdPieceSource a :
                                  NPointDomain d n → ℂ) u := by
                            apply integral_congr_ae
                            refine Filter.Eventually.of_forall ?_
                            intro u
                            by_cases hu :
                                u ∈ tsupport
                                  (ψOrdPieceSource a :
                                    NPointDomain d n → ℂ)
                            · have huP : u ∈ P.V := by
                                exact hUsrc_P
                                  (hψOrdPieceSource_Usrc a hu)
                              have hforward :
                                  (fun k => wickRotatePoint (u k)) ∈
                                    BHW.ForwardTube d n := by
                                have hroot :
                                    (fun k => wickRotatePoint (u k)) ∈
                                      _root_.ForwardTube d n :=
                                  wickRotate_mem_forwardTube_of_mem_orderedPositiveTimeSector
                                    (d := d) (n := n)
                                    (1 : Equiv.Perm (Fin n))
                                    (by
                                      simpa using P.V_ordered u huP)
                                simpa [BHW_forwardTube_eq (d := d) (n := n)]
                                  using hroot
                              have hF_holo :
                                  DifferentiableOn ℂ (bvt_F OS lgc n)
                                    (BHW.ForwardTube d n) := by
                                simpa [BHW_forwardTube_eq (d := d) (n := n)]
                                  using bvt_F_holomorphic (d := d) OS lgc n
                              have hF_real_inv :
                                  ∀ (Λ :
                                      LorentzLieGroup.RestrictedLorentzGroup d)
                                    (z : Fin n → Fin (d + 1) → ℂ),
                                    z ∈ BHW.ForwardTube d n →
                                    bvt_F OS lgc n
                                      (fun k μ =>
                                        ∑ ν,
                                          (Λ.val.val μ ν : ℂ) * z k ν) =
                                      bvt_F OS lgc n z := by
                                intro Λ z hz
                                have hΛz :
                                    BHW.complexLorentzAction
                                        (ComplexLorentzGroup.ofReal Λ) z ∈
                                      BHW.ForwardTube d n :=
                                  BHW.ofReal_preserves_forwardTube Λ z hz
                                have hcinv :=
                                  bvt_F_complexLorentzInvariant_forwardTube
                                    (d := d) OS lgc n
                                    (ComplexLorentzGroup.ofReal Λ) z
                                    ((BHW_forwardTube_eq
                                      (d := d) (n := n)) ▸ hz)
                                    ((BHW_forwardTube_eq
                                      (d := d) (n := n)) ▸ hΛz)
                                simpa [BHW.complexLorentzAction] using hcinv
                              have hmodel :=
                                _hA0a_model
                                  (hOrd_piece_wick_in_A0 u hu)
                              have hext :
                                  BHW.extendF (bvt_F OS lgc n)
                                      (fun k => wickRotatePoint (u k)) =
                                    bvt_F OS lgc n
                                      (fun k => wickRotatePoint (u k)) :=
                                BHW.extendF_eq_on_forwardTube n
                                  (bvt_F OS lgc n)
                                  hF_holo hF_real_inv
                                  (fun k => wickRotatePoint (u k))
                                  hforward
                              calc
                                A0a.branch
                                      (fun k => wickRotatePoint (u k)) *
                                    (ψOrdPieceSource a :
                                      NPointDomain d n → ℂ) u
                                    =
                                  BHW.extendF (bvt_F OS lgc n)
                                      (fun k => wickRotatePoint (u k)) *
                                    (ψOrdPieceSource a :
                                      NPointDomain d n → ℂ) u := by
                                      rw [hmodel]
                                _ =
                                  bvt_F OS lgc n
                                      (fun k => wickRotatePoint (u k)) *
                                    (ψOrdPieceSource a :
                                      NPointDomain d n → ℂ) u := by
                                      rw [hext]
                            · have hzero :
                                  (ψOrdPieceSource a :
                                    NPointDomain d n → ℂ) u = 0 :=
                                image_eq_zero_of_notMem_tsupport hu
                              simp [hzero]
                          let gammaOrdPiece : unitInterval →
                              Fin n → Fin (d + 1) → ℂ :=
                            BHW.os45Figure24IdentityPath
                              (d := d) (n := n) ua
                          let ReachOrd : Set unitInterval := {t |
                            ∃ len : ℕ,
                            ∃ chart :
                                Fin (len + 1) →
                                  PointedMetricBranchChart
                                    (Fin n → Fin (d + 1) → ℂ) ℂ,
                            ∃ edge :
                                ∀ j : Fin len,
                                  PointedSeedEdge
                                    ((chart (Fin.castSucc j)).center)
                                    ((chart (Fin.castSucc j)).carrier)
                                    ((chart (Fin.succ j)).carrier)
                                    ((chart (Fin.castSucc j)).branch)
                                    ((chart (Fin.succ j)).branch),
                              (chart 0).center = gammaOrdPiece 0 ∧
                              (chart (Fin.last len)).center =
                                gammaOrdPiece t ∧
                              ∀ j,
                                OrdModelAtZ0 d n ((chart j).center)
                                  (BHW.extendF (bvt_F OS lgc n))
                                  (chart j)}
                          have hReachOrd0 :
                              (0 : unitInterval) ∈ ReachOrd := by
                            refine ⟨0, (fun _ => A0a), ?_, ?_, ?_, ?_⟩
                            · intro j
                              exact Fin.elim0 j
                            · change A0a.center = gammaOrdPiece 0
                              calc
                                A0a.center =
                                    (fun k => wickRotatePoint (ua k)) := by
                                  simpa [ua] using _hA0a_center
                                _ = gammaOrdPiece 0 := by
                                  simpa [gammaOrdPiece] using
                                    (BHW.os45Figure24IdentityPath_zero
                                      (d := d) (n := n) ua).symm
                            · change A0a.center = gammaOrdPiece 0
                              calc
                                A0a.center =
                                    (fun k => wickRotatePoint (ua k)) := by
                                  simpa [ua] using _hA0a_center
                                _ = gammaOrdPiece 0 := by
                                  simpa [gammaOrdPiece] using
                                    (BHW.os45Figure24IdentityPath_zero
                                      (d := d) (n := n) ua).symm
                            · intro j
                              exact
                                { z0_mem := by
                                    simpa using _hA0a_mem
                                  eq_ord := by
                                    simpa using _hA0a_model }
                          have hgammaOrd_cont :
                              Continuous gammaOrdPiece := by
                            simpa [gammaOrdPiece] using
                              BHW.continuous_os45Figure24IdentityPath
                                (d := d) (n := n) ua
                          have hgammaOrd_mem :
                              ∀ t : unitInterval,
                                gammaOrdPiece t ∈
                                  BHW.ExtendedTube d n ∩ H.ΩJ := by
                            intro t
                            have ht :=
                              BHW.os45Figure24IdentityPath_mem_initialSectorOverlap
                                (d := d) (n := n) (hd := hd) (P := P)
                                (x := ua) (subset_closure hua_P) t
                            exact ⟨ht.1, H.extendedTube_subset_ΩJ ht.1⟩
                          have hOmegaOrd_open :
                              IsOpen (BHW.ExtendedTube d n ∩ H.ΩJ) :=
                            BHW.isOpen_extendedTube.inter H.ΩJ_open
                          have hReachOrd_local :
                              ∀ t : unitInterval,
                                ∃ U : Set unitInterval, IsOpen U ∧ t ∈ U ∧
                                  ∀ ⦃s r : unitInterval⦄,
                                    s ∈ U → r ∈ U → s ∈ ReachOrd →
                                      r ∈ ReachOrd := by
                            intro t
                            rcases Metric.mem_nhds_iff.mp
                                (hOmegaOrd_open.mem_nhds
                                  (hgammaOrd_mem t)) with
                              ⟨R, hR_pos, hR_sub⟩
                            let δ : ℝ := R / 4
                            let ρ : ℝ := R / 2
                            have hδ_pos : 0 < δ := by
                              dsimp [δ]
                              linarith
                            have hρ_pos : 0 < ρ := by
                              dsimp [ρ]
                              linarith
                            have hρ_add_δ_lt_R : ρ + δ < R := by
                              dsimp [ρ, δ]
                              linarith
                            let U : Set unitInterval :=
                              gammaOrdPiece ⁻¹'
                                Metric.ball (gammaOrdPiece t) δ
                            refine
                              ⟨U, Metric.isOpen_ball.preimage hgammaOrd_cont,
                                ?_, ?_⟩
                            · exact Metric.mem_ball_self hδ_pos
                            · intro s r hsU hrU hsReach
                              rcases hsReach with
                                ⟨len, chart, edge, hstart, hend, hmodel⟩
                              have hs_near :
                                  dist (gammaOrdPiece s) (gammaOrdPiece t) <
                                    δ := by
                                simpa [U, Metric.mem_ball] using hsU
                              have hr_near :
                                  dist (gammaOrdPiece r) (gammaOrdPiece t) <
                                    δ := by
                                simpa [U, Metric.mem_ball] using hrU
                              have hsr_near :
                                  dist (gammaOrdPiece s) (gammaOrdPiece r) <
                                    ρ := by
                                have htri :
                                    dist (gammaOrdPiece s)
                                        (gammaOrdPiece r) ≤
                                      dist (gammaOrdPiece s)
                                          (gammaOrdPiece t) +
                                        dist (gammaOrdPiece t)
                                          (gammaOrdPiece r) :=
                                  dist_triangle _ _ _
                                have hrt :
                                    dist (gammaOrdPiece t)
                                        (gammaOrdPiece r) <
                                      δ := by
                                  simpa [dist_comm] using hr_near
                                calc
                                  dist (gammaOrdPiece s) (gammaOrdPiece r)
                                      ≤
                                        dist (gammaOrdPiece s)
                                            (gammaOrdPiece t) +
                                          dist (gammaOrdPiece t)
                                            (gammaOrdPiece r) := htri
                                  _ < δ + δ := add_lt_add hs_near hrt
                                  _ = ρ := by
                                    dsimp [δ, ρ]
                                    ring
                              let B : PointedMetricBranchChart
                                  (Fin n → Fin (d + 1) → ℂ) ℂ :=
                                { center := gammaOrdPiece r
                                  radius := ρ
                                  radius_pos := hρ_pos
                                  branch := BHW.extendF (bvt_F OS lgc n)
                                  holo := by
                                    exact
                                      (BHW.differentiableOn_extendF_bvt_F_extendedTube
                                        (d := d) OS lgc n).mono
                                        (by
                                          intro w hw
                                          have hwρ :
                                              dist w (gammaOrdPiece r) <
                                                ρ := by
                                            simpa [Metric.mem_ball] using hw
                                          have hrt :
                                              dist (gammaOrdPiece r)
                                                  (gammaOrdPiece t) <
                                                δ := hr_near
                                          have hwt :
                                              dist w (gammaOrdPiece t) <
                                                R := by
                                            have htri :
                                                dist w (gammaOrdPiece t) ≤
                                                  dist w (gammaOrdPiece r) +
                                                    dist (gammaOrdPiece r)
                                                      (gammaOrdPiece t) :=
                                              dist_triangle _ _ _
                                            calc
                                              dist w (gammaOrdPiece t)
                                                  ≤
                                                    dist w
                                                        (gammaOrdPiece r) +
                                                      dist (gammaOrdPiece r)
                                                        (gammaOrdPiece t) :=
                                                htri
                                              _ < ρ + δ :=
                                                add_lt_add hwρ hrt
                                              _ < R := hρ_add_δ_lt_R
                                          exact
                                            (hR_sub
                                              (by
                                                simpa [Metric.mem_ball]
                                                  using hwt)).1) }
                              have hB_center_mem : B.center ∈ B.carrier :=
                                B.center_mem
                              have hB_sub :
                                  B.carrier ⊆
                                    BHW.ExtendedTube d n ∩ H.ΩJ := by
                                intro w hw
                                have hwρ :
                                    dist w (gammaOrdPiece r) < ρ := by
                                  simpa [B,
                                    PointedMetricBranchChart.carrier,
                                    Metric.mem_ball] using hw
                                have hrt :
                                    dist (gammaOrdPiece r)
                                        (gammaOrdPiece t) < δ := hr_near
                                have hwt :
                                    dist w (gammaOrdPiece t) < R := by
                                  have htri :
                                      dist w (gammaOrdPiece t) ≤
                                        dist w (gammaOrdPiece r) +
                                          dist (gammaOrdPiece r)
                                            (gammaOrdPiece t) :=
                                    dist_triangle _ _ _
                                  calc
                                    dist w (gammaOrdPiece t)
                                        ≤
                                          dist w (gammaOrdPiece r) +
                                            dist (gammaOrdPiece r)
                                              (gammaOrdPiece t) := htri
                                    _ < ρ + δ := add_lt_add hwρ hrt
                                    _ < R := hρ_add_δ_lt_R
                                exact
                                  hR_sub
                                    (by simpa [Metric.mem_ball] using hwt)
                              have hB_ord :
                                  OrdModelAtZ0 d n B.center
                                    (BHW.extendF (bvt_F OS lgc n)) B :=
                                { z0_mem := hB_center_mem
                                  eq_ord := by
                                    intro _w _hw
                                    rfl }
                              have hs_in_B :
                                  (chart (Fin.last len)).center ∈
                                    B.carrier := by
                                have hsB :
                                    gammaOrdPiece s ∈ B.carrier := by
                                  simpa [B,
                                    PointedMetricBranchChart.carrier,
                                    Metric.mem_ball, dist_comm] using
                                    hsr_near
                                simpa [hend] using hsB
                              let chart' :
                                  Fin ((len + 1) + 1) →
                                    PointedMetricBranchChart
                                      (Fin n → Fin (d + 1) → ℂ) ℂ :=
                                Fin.snoc chart B
                              refine ⟨len + 1, chart', ?_, ?_, ?_, ?_⟩
                              · intro j
                                refine Fin.lastCases ?_ ?_ j
                                · have hprev_model :=
                                    hmodel (Fin.last len)
                                  have hnew_edge :
                                      PointedSeedEdge
                                        ((chart (Fin.last len)).center)
                                        ((chart (Fin.last len)).carrier)
                                        B.carrier
                                        ((chart (Fin.last len)).branch)
                                        B.branch :=
                                    pointed_seed_edge_of_common_model
                                      (chart (Fin.last len)).carrier_open
                                      B.carrier_open
                                      hprev_model.z0_mem hs_in_B
                                      hprev_model.eq_ord
                                      (by
                                        intro _w _hw
                                        rfl)
                                  simpa [chart', Fin.snoc_castSucc,
                                    Fin.snoc_last] using hnew_edge
                                · intro j
                                  simpa [chart', Fin.snoc_castSucc,
                                    ← Fin.castSucc_succ] using
                                    edge j
                              · change (chart' 0).center =
                                  gammaOrdPiece 0
                                rw [show (0 : Fin ((len + 1) + 1)) =
                                  Fin.castSucc (0 : Fin (len + 1)) from rfl]
                                simpa [chart', Fin.snoc_castSucc] using
                                  hstart
                              · change
                                  (chart' (Fin.last (len + 1))).center =
                                    gammaOrdPiece r
                                simpa [chart', Fin.snoc_last, B]
                              · intro j
                                refine Fin.lastCases ?_ ?_ j
                                · simpa [chart', Fin.snoc_last] using
                                    hB_ord
                                · intro j
                                  simpa [chart', Fin.snoc_castSucc] using
                                    hmodel j
                          have hReachOrd_all : ReachOrd = Set.univ :=
                            SCV.reachable_eq_univ_of_local_symmetric_extension
                              (E := unitInterval) (Reach := ReachOrd)
                              ⟨0, hReachOrd0⟩ hReachOrd_local
                          obtain
                              ⟨lenOrd, chartOrd, edgeOrd, hstartOrd,
                                hendOrd, hmodelOrd⟩ :
                              ∃ len : ℕ,
                              ∃ chart :
                                  Fin (len + 1) →
                                    PointedMetricBranchChart
                                      (Fin n → Fin (d + 1) → ℂ) ℂ,
                              ∃ edge :
                                  ∀ j : Fin len,
                                    PointedSeedEdge
                                      ((chart (Fin.castSucc j)).center)
                                      ((chart (Fin.castSucc j)).carrier)
                                      ((chart (Fin.succ j)).carrier)
                                      ((chart (Fin.castSucc j)).branch)
                                      ((chart (Fin.succ j)).branch),
                                (chart 0).center = gammaOrdPiece 0 ∧
                                (chart (Fin.last len)).center =
                                  gammaOrdPiece 1 ∧
                                ∀ j,
                                  OrdModelAtZ0 d n ((chart j).center)
                                    (BHW.extendF (bvt_F OS lgc n))
                                    (chart j) := by
                            have hterminal :
                                (1 : unitInterval) ∈ ReachOrd := by
                              simpa [hReachOrd_all]
                            simpa [ReachOrd] using hterminal
                          have hOrd_terminal_center :
                              (chartOrd (Fin.last lenOrd)).center =
                                A1a.center := by
                            calc
                              (chartOrd (Fin.last lenOrd)).center =
                                  gammaOrdPiece 1 := hendOrd
                              _ =
                                  (BHW.os45QuarterTurnCLE
                                    (d := d) (n := n)).symm
                                    (BHW.realEmbed
                                      (BHW.os45CommonEdgeRealPoint
                                        (d := d) (n := n)
                                        (1 : Equiv.Perm (Fin n)) ua)) := by
                                    simpa [gammaOrdPiece] using
                                      BHW.os45Figure24IdentityPath_one
                                        (d := d) (n := n) ua
                              _ = A1a.center := by
                                    simpa [ua] using _hA1a_center.symm
                          have hOrd_terminal_model :
                              OrdModelAtZ0 d n A1a.center
                                (BHW.extendF (bvt_F OS lgc n))
                                (chartOrd (Fin.last lenOrd)) := by
                            simpa [hOrd_terminal_center] using
                              hmodelOrd (Fin.last lenOrd)
                          have hOrd_terminal_edge_to_A1 :
                              PointedSeedEdge A1a.center
                                ((chartOrd (Fin.last lenOrd)).carrier)
                                A1a.carrier
                                ((chartOrd (Fin.last lenOrd)).branch)
                                A1a.branch :=
                            pointed_seed_edge_of_common_model
                              (chartOrd (Fin.last lenOrd)).carrier_open
                              A1a.carrier_open
                              hOrd_terminal_model.z0_mem _hA1a_mem
                              hOrd_terminal_model.eq_ord hA1a_model
                          let chartOrdTerm :
                              Fin ((lenOrd + 1) + 1) →
                                PointedMetricBranchChart
                                  (Fin n → Fin (d + 1) → ℂ) ℂ :=
                            Fin.snoc chartOrd A1a
                          have edgeOrdTerm :
                              ∀ j : Fin (lenOrd + 1),
                                PointedSeedEdge
                                  ((chartOrdTerm (Fin.castSucc j)).center)
                                  ((chartOrdTerm (Fin.castSucc j)).carrier)
                                  ((chartOrdTerm (Fin.succ j)).carrier)
                                  ((chartOrdTerm (Fin.castSucc j)).branch)
                                  ((chartOrdTerm (Fin.succ j)).branch) := by
                            intro j
                            refine Fin.lastCases ?_ ?_ j
                            · simpa [chartOrdTerm, Fin.snoc_castSucc,
                                Fin.snoc_last, hOrd_terminal_center] using
                                hOrd_terminal_edge_to_A1
                            · intro j
                              simpa [chartOrdTerm, Fin.snoc_castSucc,
                                ← Fin.castSucc_succ] using edgeOrd j
                          have hOrdTerm_last_center :
                              (chartOrdTerm (Fin.last (lenOrd + 1))).center =
                                A1a.center := by
                            simpa [chartOrdTerm, Fin.snoc_last]
                          have hOrd_edge_eqOn :
                              ∀ j : Fin (lenOrd + 1),
                                Set.EqOn
                                  (chartOrdTerm (Fin.castSucc j)).branch
                                  (chartOrdTerm (Fin.succ j)).branch
                                  ((chartOrdTerm
                                      (Fin.castSucc j)).carrier ∩
                                    (chartOrdTerm (Fin.succ j)).carrier) := by
                            intro j
                            exact
                              PointedMetricBranchChart.eqOn_inter_of_seed
                                (chartOrdTerm (Fin.castSucc j))
                                (chartOrdTerm (Fin.succ j))
                                ⟨(edgeOrdTerm j).W,
                                  (edgeOrdTerm j).W_open,
                                  (edgeOrdTerm j).z0_mem,
                                  (edgeOrdTerm j).W_sub,
                                  (edgeOrdTerm j).eqOn⟩
                          /-
                          Genuine ordinary fixed translated-boundary selector.
                          The checked data above are the endpoint DCT
                          (`hOrdPieceFixed_endpoint`), the terminal chart
                          normalization (`hendpoint_to_terminal`), and the
                          incoming Wick normalization (`hOrdWick_value`).
                          The missing proof is the one-branch `(4.1)` flat
                          selector itself; it must not be replaced by a false
                          endpoint-current equality between the common-edge
                          value and the Wick value.
                          -/
                          -- The remaining obligation is the terminal ordinary
                          -- chart current.  The outer flat selector and fixed
                          -- source-side normal form have both been discharged
                          -- locally by `hFlat_piece_eq_fixed` and
                          -- `hOrdPieceFixed_terminal`; the actual OS-I content
                          -- left here is the fixed current transport from the
                          -- incoming ordinary Wick chart to this terminal
                          -- branch current.
                          have hOrd_terminal_selected :
                              Tendsto
                                (fun ε : ℝ =>
                                  ∫ u : NPointDomain d n,
                                    A1a.branch
                                      (BHW.os45FlatCommonChartSourceSide d n
                                        (1 : Equiv.Perm (Fin n)) (1 : ℝ)
                                        ε η0 u) *
                                    (ψOrdPieceSource a :
                                      NPointDomain d n → ℂ) u)
                                (𝓝[Set.Ioi 0] (0 : ℝ))
                                (𝓝 (OS.S n (ψOrdPieceZD a))) := by
                            have hOrd_base_value :
                                (∫ u : NPointDomain d n,
                                  A0a.branch
                                    (fun k => wickRotatePoint (u k)) *
                                  (ψOrdPieceSource a :
                                    NPointDomain d n → ℂ) u) =
                                OS.S n (ψOrdPieceZD a) :=
                              hOrdWick_to_A0.trans hOrdWick_value
                            have hOrd_base_selected :
                                Tendsto
                                  (fun _ε : ℝ =>
                                    ∫ u : NPointDomain d n,
                                      A0a.branch
                                        (fun k => wickRotatePoint (u k)) *
                                      (ψOrdPieceSource a :
                                        NPointDomain d n → ℂ) u)
                                  (𝓝[Set.Ioi 0] (0 : ℝ))
                                  (𝓝 (OS.S n (ψOrdPieceZD a))) := by
                              simpa [hOrd_base_value] using
                                (tendsto_const_nhds :
                                  Tendsto
                                    (fun _ε : ℝ =>
                                      ∫ u : NPointDomain d n,
                                        A0a.branch
                                          (fun k => wickRotatePoint (u k)) *
                                        (ψOrdPieceSource a :
                                          NPointDomain d n → ℂ) u)
                                    (𝓝[Set.Ioi 0] (0 : ℝ))
                                    (𝓝
                                      (∫ u : NPointDomain d n,
                                        A0a.branch
                                          (fun k => wickRotatePoint (u k)) *
                                        (ψOrdPieceSource a :
                                          NPointDomain d n → ℂ) u)))
                            -- The endpoint-continuity part is already checked
                            -- by `hOrdPieceFixed_endpoint` and the terminal
                            -- chart normalization.  What remains is precisely
                            -- the OS-I current value at the horizontal
                            -- common-edge endpoint.
                            suffices hOrd_terminal_endpoint_value :
                                (∫ u : NPointDomain d n,
                                  A1a.branch
                                    (BHW.os45FlatCommonChartSourceSide d n
                                      (1 : Equiv.Perm (Fin n)) (1 : ℝ)
                                      0 η0 u) *
                                  (ψOrdPieceSource a :
                                    NPointDomain d n → ℂ) u) =
                                OS.S n (ψOrdPieceZD a) by
                              have hOrd_terminal_endpoint :
                                  Tendsto
                                    (fun ε : ℝ =>
                                      ∫ u : NPointDomain d n,
                                        A1a.branch
                                          (BHW.os45FlatCommonChartSourceSide d n
                                            (1 : Equiv.Perm (Fin n)) (1 : ℝ)
                                            ε η0 u) *
                                        (ψOrdPieceSource a :
                                          NPointDomain d n → ℂ) u)
                                    (𝓝[Set.Ioi 0] (0 : ℝ))
                                    (𝓝
                                      (∫ u : NPointDomain d n,
                                        A1a.branch
                                          (BHW.os45FlatCommonChartSourceSide d n
                                            (1 : Equiv.Perm (Fin n)) (1 : ℝ)
                                            0 η0 u) *
                                        (ψOrdPieceSource a :
                                          NPointDomain d n → ℂ) u)) := by
                                rw [← hendpoint_to_terminal]
                                exact
                                  hOrdPieceFixed_endpoint.congr'
                                    hOrdPieceFixed_terminal
                              have hOrd_terminal_endpoint_value_qturn :
                                  (∫ u : NPointDomain d n,
                                    A1a.branch
                                      (BHW.os45QuarterTurnConfig
                                        (d := d) (n := n)
                                        (fun k => wickRotatePoint (u k))) *
                                    (ψOrdPieceSource a :
                                      NPointDomain d n → ℂ) u) =
                                  OS.S n (ψOrdPieceZD a) := by
                                simpa [BHW.os45FlatCommonChartSourceSide_zero]
                                  using hOrd_terminal_endpoint_value
                              simpa [BHW.os45FlatCommonChartSourceSide_zero,
                                hOrd_terminal_endpoint_value_qturn] using
                                hOrd_terminal_endpoint
                          have hOrdPieceFixed_selected :
                              Tendsto OrdPieceFixed
                                (𝓝[Set.Ioi 0] (0 : ℝ))
                                (𝓝 (OS.S n (ψOrdPieceZD a))) :=
                            hOrd_terminal_selected.congr'
                              hOrdPieceFixed_terminal.symm
                          exact
                            (hOrdPieceFixed_selected.const_mul J).congr'
                              hFlat_piece_eq_fixed.symm
                        have hsum_piece :
                            Tendsto
                              (fun ε : ℝ =>
                                ∑ a : αOrd, FlatOrdPiece a ε)
                              (𝓝[Set.Ioi 0] (0 : ℝ))
                              (𝓝
                                (∑ a : αOrd,
                                  J * OS.S n (ψOrdPieceZD a))) := by
                          refine tendsto_finset_sum Finset.univ ?_
                          intro a _ha
                          exact hflatOrd_piece a
                        have hschwinger_sum :
                            OS.S n (∑ a : αOrd, ψOrdPieceZD a) =
                              ∑ a : αOrd, OS.S n (ψOrdPieceZD a) := by
                          change
                            (OsterwalderSchraderAxioms.schwingerCLM
                              (d := d) OS n)
                                (∑ a : αOrd, ψOrdPieceZD a) =
                              ∑ a : αOrd,
                                (OsterwalderSchraderAxioms.schwingerCLM
                                  (d := d) OS n) (ψOrdPieceZD a)
                          rw [_root_.map_sum]
                        have hlimit_sum :
                            (∑ a : αOrd,
                                J * OS.S n (ψOrdPieceZD a)) =
                              J * OS.S n (D.toZeroDiagonalCLM
                                (1 : Equiv.Perm (Fin n)) φ) := by
                          calc
                            (∑ a : αOrd,
                                J * OS.S n (ψOrdPieceZD a))
                                = J * (∑ a : αOrd,
                                    OS.S n (ψOrdPieceZD a)) := by
                                  rw [Finset.mul_sum]
                            _ = J * OS.S n
                                  (∑ a : αOrd, ψOrdPieceZD a) := by
                                  rw [hschwinger_sum]
                            _ = J * OS.S n (D.toZeroDiagonalCLM
                                  (1 : Equiv.Perm (Fin n)) φ) := by
                                  rw [hψOrdZD_sum]
                        have hsum_global :
                            Tendsto
                              (fun ε : ℝ =>
                                ∑ a : αOrd, FlatOrdPiece a ε)
                              (𝓝[Set.Ioi 0] (0 : ℝ))
                              (𝓝
                                (J * OS.S n (D.toZeroDiagonalCLM
                                  (1 : Equiv.Perm (Fin n)) φ))) := by
                          exact hlimit_sum ▸ hsum_piece
                        have hFlatOrd_sum :
                            (fun ε : ℝ =>
                              ∫ x : BHW.OS45FlatCommonChartReal d n,
                                BHW.os45FlatCommonChartBranch d n OS lgc
                                  (1 : Equiv.Perm (Fin n))
                                  (fun j =>
                                    (x j : ℂ) +
                                      ((((1 : ℝ) * ε) • η0) j : ℂ) *
                                        Complex.I) *
                                (SCV.translateSchwartz
                                  (-((1 : ℝ) * ε) • η0) ψ0Flat) x)
                              =ᶠ[𝓝[Set.Ioi 0] (0 : ℝ)]
                            (fun ε : ℝ =>
                              ∑ a : αOrd, FlatOrdPiece a ε) := by
                          filter_upwards [hOrd_piece_integrable] with ε hε
                          let t : BHW.OS45FlatCommonChartReal d n :=
                            -((1 : ℝ) * ε) • η0
                          let Hε :
                              BHW.OS45FlatCommonChartReal d n → ℂ :=
                            fun x =>
                              BHW.os45FlatCommonChartBranch d n OS lgc
                                (1 : Equiv.Perm (Fin n))
                                (fun j =>
                                  (x j : ℂ) +
                                    ((((1 : ℝ) * ε) • η0) j : ℂ) *
                                      Complex.I)
                          have htranslate_sum :
                              SCV.translateSchwartz t ψ0Flat =
                                ∑ a : αOrd,
                                  SCV.translateSchwartz t
                                    (ψOrdPieceFlat a) := by
                            calc
                              SCV.translateSchwartz t ψ0Flat =
                                  (SCV.translateSchwartzCLM t) ψ0Flat := by
                                    rw [SCV.translateSchwartzCLM_apply]
                              _ =
                                  (SCV.translateSchwartzCLM t)
                                    (∑ a : αOrd, ψOrdPieceFlat a) := by
                                    rw [← hψOrdFlat_sum]
                              _ =
                                  ∑ a : αOrd,
                                    (SCV.translateSchwartzCLM t)
                                      (ψOrdPieceFlat a) := by
                                    rw [_root_.map_sum]
                              _ =
                                  ∑ a : αOrd,
                                    SCV.translateSchwartz t
                                      (ψOrdPieceFlat a) := by
                                    simp [SCV.translateSchwartzCLM_apply]
                          calc
                            (∫ x : BHW.OS45FlatCommonChartReal d n,
                                BHW.os45FlatCommonChartBranch d n OS lgc
                                  (1 : Equiv.Perm (Fin n))
                                  (fun j =>
                                    (x j : ℂ) +
                                      ((((1 : ℝ) * ε) • η0) j : ℂ) *
                                        Complex.I) *
                                (SCV.translateSchwartz
                                  (-((1 : ℝ) * ε) • η0) ψ0Flat) x)
                                =
                              ∫ x : BHW.OS45FlatCommonChartReal d n,
                                Hε x *
                                  (∑ a : αOrd,
                                    (SCV.translateSchwartz t
                                      (ψOrdPieceFlat a)) x) := by
                                  apply integral_congr_ae
                                  filter_upwards with x
                                  have htranslate_sum_apply :
                                      (SCV.translateSchwartz
                                        (-((1 : ℝ) * ε) • η0) ψ0Flat) x =
                                        (∑ a : αOrd,
                                          SCV.translateSchwartz t
                                            (ψOrdPieceFlat a)) x := by
                                    simpa [t] using
                                      congrArg
                                        (fun f :
                                          SchwartzMap
                                            (BHW.OS45FlatCommonChartReal d n)
                                            ℂ => f x)
                                        htranslate_sum
                                  rw [htranslate_sum_apply]
                                  simp [Hε]
                            _ =
                              ∫ x : BHW.OS45FlatCommonChartReal d n,
                                ∑ a : αOrd,
                                  Hε x *
                                    (SCV.translateSchwartz t
                                      (ψOrdPieceFlat a)) x := by
                                  apply integral_congr_ae
                                  filter_upwards with x
                                  simp [Finset.mul_sum]
                            _ =
                              ∑ a : αOrd, FlatOrdPiece a ε := by
                                  have hint :
                                      ∀ a ∈ (Finset.univ : Finset αOrd),
                                        Integrable
                                        (fun x :
                                          BHW.OS45FlatCommonChartReal d n =>
                                        Hε x *
                                          (SCV.translateSchwartz t
                                            (ψOrdPieceFlat a)) x) := by
                                    intro a _ha
                                    simpa [Hε, t] using hε a
                                  simpa [FlatOrdPiece, Hε, t] using
                                    (MeasureTheory.integral_finset_sum
                                      (s := (Finset.univ : Finset αOrd))
                                      (f := fun a =>
                                        fun x :
                                          BHW.OS45FlatCommonChartReal d n =>
                                        Hε x *
                                          (SCV.translateSchwartz t
                                            (ψOrdPieceFlat a)) x)
                                      hint)
                        exact hsum_global.congr' hFlatOrd_sum.symm
                      have hcancel :=
                        BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_fixed_of_flatTranslatedTest
                          (d := d) (n := n) OS lgc
                          (1 : Equiv.Perm (Fin n))
                          (1 : Equiv.Perm (Fin n))
                          (1 : ℝ) η0 ψ0Flat
                          (α := ℝ)
                          (l := 𝓝[Set.Ioi 0] (0 : ℝ))
                          (εseq := fun ε : ℝ => ε)
                          (L := OS.S n (D.toZeroDiagonalCLM
                            (1 : Equiv.Perm (Fin n)) φ))
                          hOrd_flat_integrable hflatOrd_selected
                      simpa [OrdFixed, J, ψ0Flat, eflat,
                        SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
                        one_mul] using hcancel
                  exact hOrd_fixed_selected_direct
                exact
                  tendsto_nhds_unique hOrd_fixed_endpoint
                    hOrd_fixed_selected
            refine hGplus_source.congr ?_
            filter_upwards [hFplus_eq_Gplus] with ε hε η hη
            exact (hε η hη).symm
        rcases hKη_nonempty with ⟨η0, hη0⟩
        exact tendsto_nhds_unique
          (hplus_zero_uniform.tendsto_at hη0)
          (hplus_source.tendsto_at hη0)
      have hminus_source :
          TendstoUniformlyOn Fminus
            (fun _ : BHW.OS45FlatCommonChartReal d n =>
              J * OS.S n (D.toZeroDiagonalCLM
                (1 : Equiv.Perm (Fin n)) φ))
            (𝓝[Set.Ioi 0] (0 : ℝ)) Kη := by
        have hsource_minus :=
          hsource_uniform.2.2.2
        let Gminus :
            ℝ → BHW.OS45FlatCommonChartReal d n → ℂ :=
          fun ε η =>
            J * (∫ u : NPointDomain d n,
              BHW.extendF (bvt_F OS lgc n)
                (BHW.permAct (d := d)
                  (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
                  (BHW.os45FlatCommonChartSourceSide d n
                    (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η u)) *
              ((((D.toSideZeroDiagonalCLM
                (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
                  SchwartzNPoint d n) : NPointDomain d n → ℂ) u))
        have hFminus_eq_Gminus :
            ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
              ∀ η ∈ Kη, Fminus ε η = Gminus ε η := by
          have hint :=
            BHW.os45FlatCommonChart_branch_side_shifted_mul_integrable_eventually
              (d := d) (hd := hd) OS lgc (P := P)
              Kη hKη_compact hKη_cone
              φ hφ_compact (hφE.trans hE_sub)
          obtain ⟨r, hr_pos, hside_support⟩ :=
            BHW.os45FlatCommonChart_sideSupport_radius
              (d := d) (hd := hd) (P := P)
              Kη hKη_compact hKη_cone
              φ hφ_compact (hφE.trans hE_sub)
          filter_upwards
            [self_mem_nhdsWithin,
              nhdsWithin_le_nhds (Iio_mem_nhds hr_pos), hint]
            with ε hε_pos hε_lt hintε η hη
          have hφE_shift :
              tsupport
                (SCV.translateSchwartz ((-ε : ℝ) • η) φ :
                  BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
              BHW.os45FlatCommonChartEdgeSet d n P
                (1 : Equiv.Perm (Fin n)) :=
            (hside_support ε hε_pos hε_lt η hη).2
          have hφE_shift' :
              tsupport
                (SCV.translateSchwartz (((-1 : ℝ) * ε) • η) φ :
                  BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
              BHW.os45FlatCommonChartEdgeSet d n P
                (1 : Equiv.Perm (Fin n)) := by
            simpa using hφE_shift
          have hinteg :=
            (hintε η hη).2
          have hinteg' :
              Integrable
                (fun x : BHW.OS45FlatCommonChartReal d n =>
                  BHW.os45FlatCommonChartBranch d n OS lgc
                    (P.τ.symm * (1 : Equiv.Perm (Fin n)))
                    (fun j =>
                      ((x + ((-1 : ℝ) * ε) • η) j : ℂ) +
                        ((((-1 : ℝ) * ε) • η) j : ℂ) *
                          Complex.I) *
                  φ (x + ((-1 : ℝ) * ε) • η)) := by
            simpa using hinteg
          have heq :=
            BHW.os45FlatCommonChart_branch_integral_eq_sourceSide_extendF_sideZeroDiagonalCLM
              (d := d) (hd := hd) OS lgc (P := P) D
              (P.τ.symm * (1 : Equiv.Perm (Fin n)))
              (1 : Equiv.Perm (Fin n))
              (-1 : ℝ) ε η φ hφE_shift' hinteg'
          simpa [Fminus, Gminus, J, sub_eq_add_neg, neg_mul, one_mul] using heq
        have hGminus_source :
            TendstoUniformlyOn Gminus
              (fun _ : BHW.OS45FlatCommonChartReal d n =>
                J * OS.S n (D.toZeroDiagonalCLM
                  (1 : Equiv.Perm (Fin n)) φ))
              (𝓝[Set.Ioi 0] (0 : ℝ)) Kη := by
          change
            TendstoUniformlyOn Gminus
              (fun _ : BHW.OS45FlatCommonChartReal d n =>
                J * OS.S n (D.toZeroDiagonalCLM
                  (1 : Equiv.Perm (Fin n)) φ))
              (𝓝[Set.Ioi 0] (0 : ℝ)) (Set.range ys)
          refine tendstoUniformlyOn_range_of_tendsto (ys := ys) ?_
          intro k
          let η0 : BHW.OS45FlatCommonChartReal d n := ys k
          let τout : Equiv.Perm (Fin n) :=
            (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
          let Uadj : Set (Fin n → Fin (d + 1) → ℂ) :=
            {z | BHW.permAct (d := d) τout z ∈
              BHW.ExtendedTube d n}
          have hUadj_open : IsOpen Uadj := by
            exact BHW.isOpen_permAct_preimage_extendedTube τout
          have hF_cont :
              ContinuousOn
                (fun z : Fin n → Fin (d + 1) → ℂ =>
                  BHW.extendF (bvt_F OS lgc n)
                    (BHW.permAct (d := d) τout z)) Uadj :=
            (BHW.differentiableOn_extendF_bvt_F_permAct_preimageExtendedTube
              (d := d) OS lgc n τout).continuousOn
          have h0 :
              ∀ u ∈ Ksrc,
                BHW.os45FlatCommonChartSourceSide d n
                  (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η0 u ∈ Uadj := by
            intro u huK
            have huV : u ∈ P.V := hU_sub (hKsrcU huK)
            have hpulled := P.V_pulled_tau u huV
            rw [BHW.os45FlatCommonChartSourceSide_zero_eq_commonEdge]
            simpa [Uadj, τout, BHW.os45PulledRealBranchDomain,
              one_mul, P.τ_eq] using hpulled
          have hsupp :
              ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
                ∀ u ∉ Ksrc,
                  ((((D.toSideZeroDiagonalCLM
                    (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η0 φ).1 :
                      SchwartzNPoint d n) -
                    ((D.toZeroDiagonalCLM
                      (1 : Equiv.Perm (Fin n)) φ).1 :
                      SchwartzNPoint d n) :
                      SchwartzNPoint d n) :
                      NPointDomain d n → ℂ) u = 0 := by
            filter_upwards [hcommon_support] with ε hε u huK
            simpa [η0] using (hε η0 ⟨k, rfl⟩).2 u huK
          have hseminorm :
              Tendsto
                (fun ε : ℝ =>
                  SchwartzMap.seminorm ℝ 0 0
                    (((D.toSideZeroDiagonalCLM
                      (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η0 φ).1 :
                        SchwartzNPoint d n) -
                      ((D.toZeroDiagonalCLM
                        (1 : Equiv.Perm (Fin n)) φ).1 :
                        SchwartzNPoint d n) :
                        SchwartzNPoint d n))
                (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
            exact
              (D.toSideZeroDiagonalCLM_sub_toZeroDiagonalCLM_seminorm_tendsto_zero
                (1 : Equiv.Perm (Fin n)) (-1 : ℝ) η0 φ hφ_compact).mono_left
                nhdsWithin_le_nhds
          have hAdj_endpoint_DCT :
              Tendsto
                (fun ε : ℝ =>
                  ∫ u : NPointDomain d n,
                      BHW.extendF (bvt_F OS lgc n)
                        (BHW.permAct (d := d) τout
                          (BHW.os45FlatCommonChartSourceSide d n
                            (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η0 u)) *
                      ((((D.toSideZeroDiagonalCLM
                        (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η0 φ).1 :
                          SchwartzNPoint d n) :
                          NPointDomain d n → ℂ) u))
                (𝓝[Set.Ioi 0] (0 : ℝ))
                (𝓝
                  (∫ u : NPointDomain d n,
                    BHW.extendF (bvt_F OS lgc n)
                      (BHW.permAct (d := d) τout
                        (BHW.os45FlatCommonChartSourceSide d n
                          (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η0 u)) *
                    (ψ0 : NPointDomain d n → ℂ) u)) := by
            simpa [η0, ψ0, Uadj] using
              BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_moving_of_commonCompactSupport
                (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) (-1 : ℝ) η0
                (U := Uadj) hUadj_open hF_cont
                (K := Ksrc) hKsrc_compact h0
                (εseq := fun ε : ℝ => ε)
                (φseq := fun ε : ℝ =>
                  ((D.toSideZeroDiagonalCLM
                    (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η0 φ).1 :
                    SchwartzNPoint d n))
                (φ0 := ψ0)
                tendsto_id hψ0_suppKsrc hsupp hseminorm
          suffices hAdj_endpoint_value :
              (∫ u : NPointDomain d n,
                BHW.extendF (bvt_F OS lgc n)
                  (BHW.permAct (d := d) τout
                    (BHW.os45FlatCommonChartSourceSide d n
                      (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η0 u)) *
                (ψ0 : NPointDomain d n → ℂ) u) =
              OS.S n (D.toZeroDiagonalCLM
                (1 : Equiv.Perm (Fin n)) φ) by
            have hAdj_endpoint_value_qturn :
                (∫ u : NPointDomain d n,
                  BHW.extendF (bvt_F OS lgc n)
                    (BHW.permAct (d := d) P.τ
                      (BHW.os45QuarterTurnConfig (d := d) (n := n)
                        (fun k => wickRotatePoint (u k)))) *
                  (ψ0 : NPointDomain d n → ℂ) u) =
                OS.S n (D.toZeroDiagonalCLM
                  (1 : Equiv.Perm (Fin n)) φ) := by
              simpa [τout, one_mul,
                BHW.permAct_os45FlatCommonChartSourceSide_zero] using
                hAdj_endpoint_value
            simpa [Gminus, η0, τout, hAdj_endpoint_value_qturn] using
              hAdj_endpoint_DCT.const_mul J
          let AdjFixed : ℝ → ℂ := fun ε =>
            ∫ u : NPointDomain d n,
              BHW.extendF (bvt_F OS lgc n)
                (BHW.permAct (d := d) τout
                  (BHW.os45FlatCommonChartSourceSide d n
                    (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η0 u)) *
              (ψ0 : NPointDomain d n → ℂ) u
          have hAdj_fixed_endpoint :
              Tendsto AdjFixed (𝓝[Set.Ioi 0] (0 : ℝ))
                (𝓝
                  (∫ u : NPointDomain d n,
                    BHW.extendF (bvt_F OS lgc n)
                      (BHW.permAct (d := d) τout
                        (BHW.os45FlatCommonChartSourceSide d n
                          (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η0 u)) *
                    (ψ0 : NPointDomain d n → ℂ) u)) := by
            have h0ψ :
                ∀ u ∈ tsupport (ψ0 : NPointDomain d n → ℂ),
                  BHW.os45FlatCommonChartSourceSide d n
                    (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η0 u ∈ Uadj := by
              intro u hu
              exact h0 u (hψ0_suppKsrc hu)
            simpa [AdjFixed, Uadj] using
              BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_of_hasCompactSupport
                (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) (-1 : ℝ) η0
                (U := Uadj) hUadj_open hF_cont
                hψ0_compact (ψ0 : SchwartzNPoint d n).continuous h0ψ
          have hAdj_fixed_selected :
              Tendsto AdjFixed (𝓝[Set.Ioi 0] (0 : ℝ))
                (𝓝
                  (OS.S n (D.toZeroDiagonalCLM
                    (1 : Equiv.Perm (Fin n)) φ))) := by
            let eflat :=
              BHW.os45CommonEdgeFlatCLE d n
                (1 : Equiv.Perm (Fin n))
            let ψ0Flat :
                SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ :=
              (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
                eflat.symm) (ψ0 : SchwartzNPoint d n)
            have hψ0Flat_eq_phi : ψ0Flat = φ := by
              ext x
              have hplain :=
                D.toSchwartzNPointCLM_eq_plain_of_tsupport_subset_edge
                  (1 : Equiv.Perm (Fin n)) φ (hφE.trans hE_sub)
                  (eflat.symm x)
              change
                ((D.toSchwartzNPointCLM
                  (1 : Equiv.Perm (Fin n)) φ :
                  NPointDomain d n → ℂ) (eflat.symm x)) = φ x
              simpa [eflat] using hplain
            let σAdj : Equiv.Perm (Fin n) :=
              P.τ.symm * (1 : Equiv.Perm (Fin n))
            have hUsrc_P : Usrc ⊆ P.V :=
              hUsrc_sub_Ksrc.trans (hKsrcU.trans hU_sub)
            have hψ0Flat_packet :
                HasCompactSupport
                    (ψ0Flat : BHW.OS45FlatCommonChartReal d n → ℂ) ∧
                  tsupport
                    (ψ0Flat :
                      BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
                    BHW.os45FlatCommonChartEdgeSet d n P
                      (1 : Equiv.Perm (Fin n)) := by
              simpa [ψ0Flat, ψ0, eflat] using
                D.toZeroDiagonalCLM_flatPullback_support
                  (1 : Equiv.Perm (Fin n))
                  (U := Usrc) φ hφUsrc hUsrc_P
            have hAdj_fixed_selected_direct :
                Tendsto AdjFixed (𝓝[Set.Ioi 0] (0 : ℝ))
                  (𝓝
                    (OS.S n (D.toZeroDiagonalCLM
                      (1 : Equiv.Perm (Fin n)) φ))) := by
              /-
                Genuine remaining retained raw `(4.12)` flat selector.  The
                downstream `extendF ∘ permAct` expression is only the terminal
                normal form after this raw one-branch chain is selected.
                -/
                let K0 : Set (BHW.OS45FlatCommonChartReal d n) :=
                  tsupport
                    (ψ0Flat :
                      BHW.OS45FlatCommonChartReal d n → ℂ)
                have hK0_compact : IsCompact K0 := by
                  simpa [K0] using hψ0Flat_packet.1.isCompact
                have hK0_edge :
                    K0 ⊆ BHW.os45FlatCommonChartEdgeSet d n P
                      (1 : Equiv.Perm (Fin n)) := by
                  simpa [K0] using hψ0Flat_packet.2
                have hK0_E : K0 ⊆ E := by
                  intro x hx
                  have hxφ :
                      x ∈ tsupport
                        (φ :
                          BHW.OS45FlatCommonChartReal d n → ℂ) := by
                    simpa [K0, hψ0Flat_eq_phi] using hx
                  exact hφE hxφ
                have hK0_preimage_Usrc :
                    ∀ x ∈ K0, eflat.symm x ∈ Usrc := by
                  intro x hx
                  have hxφ :
                      x ∈ tsupport
                        (φ :
                          BHW.OS45FlatCommonChartReal d n → ℂ) := by
                    simpa [K0, hψ0Flat_eq_phi] using hx
                  rcases hφUsrc hxφ with ⟨u, hu, hu_eq⟩
                  have hx_eq : eflat.symm x = u := by
                    simpa [eflat, e] using congrArg eflat.symm hu_eq.symm
                  simpa [hx_eq] using hu
                have hK0_preimage_P :
                    ∀ x ∈ K0, eflat.symm x ∈ P.V := by
                  intro x hx
                  exact hUsrc_P (hK0_preimage_Usrc x hx)
                have hAdj_translated_tsupport :
                    ∀ ε : ℝ,
                      tsupport
                        (SCV.translateSchwartz
                          (-((-1 : ℝ) * ε) • η0) ψ0Flat :
                          BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
                        {x | x + (-((-1 : ℝ) * ε) • η0) ∈ K0} := by
                  intro ε
                  simpa [K0] using
                    (BHW.tsupport_translateSchwartz_subset_preimage
                      (m := BHW.os45FlatCommonChartDim d n)
                      (-((-1 : ℝ) * ε) • η0) ψ0Flat)
                have hAdj_translated_source_P :
                    ∀ ε : ℝ,
                      ∀ x ∈ tsupport
                        (SCV.translateSchwartz
                          (-((-1 : ℝ) * ε) • η0) ψ0Flat :
                          BHW.OS45FlatCommonChartReal d n → ℂ),
                        eflat.symm
                            (x + (-((-1 : ℝ) * ε) • η0)) ∈ P.V := by
                  intro ε x hx
                  exact hK0_preimage_P
                    (x + (-((-1 : ℝ) * ε) • η0))
                    (hAdj_translated_tsupport ε hx)
                have hAdj_sourceSide_sheet :
                    ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
                      ∀ u : NPointDomain d n,
                        eflat u + (-ε : ℝ) • η0 ∈ K0 →
                          BHW.permAct (d := d) σAdj.symm
                            (BHW.os45FlatCommonChartSourceSide d n
                              (1 : Equiv.Perm (Fin n)) (-1 : ℝ)
                              ε η0 u) ∈
                            BHW.ExtendedTube d n := by
                  have hsheet :=
                    BHW.os45FlatCommonChart_sourceSide_mem_extendedTube_eventually
                      (d := d) (hd := hd) (P := P)
                      Kη hKη_compact hKη_cone
                      ψ0Flat hψ0Flat_packet.1 hψ0Flat_packet.2
                  filter_upwards [hsheet] with ε hε u hu
                  simpa [σAdj, K0, eflat] using
                    (hε η0 ⟨k, rfl⟩).2 u
                      (by simpa [K0, eflat] using hu)
                have hAdj_base_chart :
                    ∀ x ∈ K0,
                      ∃ A : PointedMetricBranchChart
                          (Fin n → Fin (d + 1) → ℂ) ℂ,
                        A.center =
                            BHW.permAct (d := d) P.τ
                              (fun k =>
                                wickRotatePoint ((eflat.symm x) k)) ∧
                        A.center ∈ A.carrier ∧
                        A.carrier ⊆
                            (({z : Fin n → Fin (d + 1) → ℂ |
                                BHW.permAct (d := d) P.τ z ∈
                                  BHW.ForwardTube d n} ∩ H.ΩJ) ∩
                              (BHW.ExtendedTube d n ∩
                                BHW.permutedExtendedTubeSector d n P.τ)) ∧
                        Set.EqOn A.branch
                          (fun z : Fin n → Fin (d + 1) → ℂ =>
                            bvt_F OS lgc n
                              (BHW.permAct (d := d) P.τ z)) A.carrier ∧
                        A.branch A.center =
                          bvt_F OS lgc n
                            (fun k =>
                              wickRotatePoint ((eflat.symm x) (P.τ k))) := by
                  intro x hx
                  simpa using
                    H.OS412SeedWindow_pointedChart OS lgc
                      (hK0_preimage_P x hx)
                have hAdj_flat_integrable :
                    ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
                      Integrable
                        (fun x : BHW.OS45FlatCommonChartReal d n =>
                        BHW.os45FlatCommonChartBranch d n OS lgc σAdj
                          (fun j =>
                            ((x + ((-1 : ℝ) * ε) • η0) j : ℂ) +
                              ((((-1 : ℝ) * ε) • η0) j : ℂ) *
                                Complex.I) *
                          (SCV.translateSchwartz
                            (-((-1 : ℝ) * ε) • η0) ψ0Flat)
                            (x + ((-1 : ℝ) * ε) • η0)) := by
                  have hψ0Flat_omega :
                      ∀ x ∈ tsupport
                          (ψ0Flat :
                            BHW.OS45FlatCommonChartReal d n → ℂ),
                        (fun j => (x j : ℂ)) ∈
                          BHW.os45FlatCommonChartOmega d n σAdj := by
                    intro x hx
                    simpa [σAdj] using
                      BHW.os45FlatCommonChart_real_mem_omega_adjacent
                        (d := d) hd (P := P) x
                        (hψ0Flat_packet.2 hx)
                  simpa using
                    BHW.os45FlatCommonChart_fixedTranslatedTest_integrable_eventually
                      (d := d) (n := n) OS lgc
                      σAdj (-1 : ℝ) η0 ψ0Flat
                      hψ0Flat_packet.1 hψ0Flat_omega
                have hAdj_flat_eq_fixed :
                    (fun ε : ℝ =>
                      ∫ x : BHW.OS45FlatCommonChartReal d n,
                        BHW.os45FlatCommonChartBranch d n OS lgc σAdj
                          (fun j =>
                            (x j : ℂ) +
                              ((((-1 : ℝ) * ε) • η0) j : ℂ) *
                                Complex.I) *
                        (SCV.translateSchwartz
                          (-((-1 : ℝ) * ε) • η0) ψ0Flat) x)
                      =ᶠ[𝓝[Set.Ioi 0] (0 : ℝ)]
                    fun ε : ℝ => J * AdjFixed ε := by
                  filter_upwards [hAdj_flat_integrable] with ε hε
                  have heq :=
                    BHW.os45FlatCommonChart_branch_integral_eq_sourceSide_extendF_translatedTest
                      (d := d) (n := n) OS lgc
                      σAdj (1 : Equiv.Perm (Fin n))
                      (-1 : ℝ) ε η0 ψ0Flat hε
                  simpa [AdjFixed, J, ψ0Flat, eflat, σAdj, τout,
                    SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
                    one_mul] using heq
                have hAdj_raw_path_mem :
                    ∀ x ∈ K0, ∀ t : unitInterval,
                      BHW.permAct (d := d) P.τ
                          (BHW.os45Figure24IdentityPath
                            (d := d) (n := n) (eflat.symm x) t) ∈
                        ({z : Fin n → Fin (d + 1) → ℂ |
                            BHW.permAct (d := d) P.τ z ∈
                              BHW.ForwardTube d n} ∩ H.ΩJ) := by
                  intro x hx t
                  have hxP : eflat.symm x ∈ P.V :=
                    hK0_preimage_P x hx
                  let Γ : Fin n → Fin (d + 1) → ℂ :=
                    BHW.os45Figure24IdentityPath
                      (d := d) (n := n) (eflat.symm x) t
                  have hΓ_forward : Γ ∈ BHW.ForwardTube d n := by
                    simpa [Γ] using
                      BHW.os45Figure24IdentityPath_mem_forwardTube
                        (d := d) (n := n)
                        (P.V_ordered (eflat.symm x) hxP) t
                  have hΓ_init :
                      BHW.permAct (d := d) P.τ Γ ∈
                        BHW.ExtendedTube d n ∩
                          BHW.permutedExtendedTubeSector d n P.τ := by
                    simpa [Γ] using
                      BHW.os45Figure24_permActIdentityPath_mem_initialSectorOverlap
                        (d := d) (n := n) (hd := hd) (P := P)
                        (x := eflat.symm x) (subset_closure hxP) t
                  have hττ :
                      BHW.permAct (d := d) P.τ
                          (BHW.permAct (d := d) P.τ Γ) = Γ := by
                    ext k μ
                    simp [BHW.permAct, P.τ_eq]
                  constructor
                  · simpa [Γ, hττ] using hΓ_forward
                  · exact H.extendedTube_subset_ΩJ hΓ_init.1
                have hAdj_raw_corridor :
                    ∀ x ∈ K0,
                      ∃ Ucorr : Set (Fin n → Fin (d + 1) → ℂ),
                        IsOpen Ucorr ∧ IsConnected Ucorr ∧
                        BHW.permAct (d := d) P.τ
                            (fun k => wickRotatePoint ((eflat.symm x) k)) ∈
                          Ucorr ∧
                        BHW.permAct (d := d) P.τ
                            ((BHW.os45QuarterTurnCLE
                              (d := d) (n := n)).symm
                              (BHW.realEmbed
                                (BHW.os45CommonEdgeRealPoint
                                  (d := d) (n := n)
                                  (1 : Equiv.Perm (Fin n))
                                  (eflat.symm x)))) ∈
                          Ucorr ∧
                        Ucorr ⊆
                          BHW.ExtendedTube d n ∩
                            BHW.permutedExtendedTubeSector d n P.τ := by
                  intro x hx
                  have hxP : eflat.symm x ∈ P.V :=
                    hK0_preimage_P x hx
                  have hjoin :=
                    BHW.os45Figure24_joined_permActOrdinaryWick_to_permActCommonEdge_initialSectorOverlap
                      (d := d) (n := n) (hd := hd) (P := P)
                      (x := eflat.symm x) (subset_closure hxP)
                  exact
                    BHW.initialSectorOverlap_connectedNeighborhood_of_joinedIn
                      (d := d) (n := n) P.τ hjoin
                have hAdj_raw_path_chart :
                    ∀ x ∈ K0, ∀ t : unitInterval,
                      ∃ A : PointedMetricBranchChart
                          (Fin n → Fin (d + 1) → ℂ) ℂ,
                        A.center =
                          BHW.permAct (d := d) P.τ
                            (BHW.os45Figure24IdentityPath
                              (d := d) (n := n)
                              (eflat.symm x) t) ∧
                        A.center ∈ A.carrier ∧
                        A.carrier ⊆
                          ({z : Fin n → Fin (d + 1) → ℂ |
                            BHW.permAct (d := d) P.τ z ∈
                              BHW.ForwardTube d n} ∩ H.ΩJ) ∧
                        Set.EqOn A.branch
                          (fun z : Fin n → Fin (d + 1) → ℂ =>
                            bvt_F OS lgc n
                              (BHW.permAct (d := d) P.τ z))
                          A.carrier := by
                  intro x hx t
                  let z0 : Fin n → Fin (d + 1) → ℂ :=
                    BHW.permAct (d := d) P.τ
                      (BHW.os45Figure24IdentityPath
                        (d := d) (n := n) (eflat.symm x) t)
                  let Ωraw : Set (Fin n → Fin (d + 1) → ℂ) :=
                    {z : Fin n → Fin (d + 1) → ℂ |
                      BHW.permAct (d := d) P.τ z ∈
                        BHW.ForwardTube d n} ∩ H.ΩJ
                  have hΩraw_open : IsOpen Ωraw := by
                    simpa [Ωraw] using H.OS412SeedWindow_open
                  have hz0Ωraw : z0 ∈ Ωraw := by
                    simpa [z0, Ωraw] using hAdj_raw_path_mem x hx t
                  rcases Metric.mem_nhds_iff.mp
                      (hΩraw_open.mem_nhds hz0Ωraw) with
                    ⟨r, hr_pos, hball_sub⟩
                  let A : PointedMetricBranchChart
                      (Fin n → Fin (d + 1) → ℂ) ℂ :=
                    { center := z0
                      radius := r
                      radius_pos := hr_pos
                      branch := fun z : Fin n → Fin (d + 1) → ℂ =>
                        bvt_F OS lgc n
                          (BHW.permAct (d := d) P.τ z)
                      holo := by
                        exact (H.differentiableOn_OS412SeedBranch OS lgc).mono
                          (by
                            intro w hw
                            simpa [Ωraw] using hball_sub hw) }
                  refine ⟨A, ?_, ?_, ?_, ?_⟩
                  · rfl
                  · simpa [A] using A.center_mem
                  · intro w hw
                    exact
                      (by
                        simpa [A, PointedMetricBranchChart.carrier, Ωraw] using
                          hball_sub
                            (by
                              simpa [A, PointedMetricBranchChart.carrier]
                                using hw))
                  · intro _w _hw
                    rfl
                have hAdj_raw_terminal_chart :
                    ∀ x ∈ K0,
                      ∃ A : PointedMetricBranchChart
                          (Fin n → Fin (d + 1) → ℂ) ℂ,
                        A.center =
                          BHW.permAct (d := d) P.τ
                            ((BHW.os45QuarterTurnCLE
                              (d := d) (n := n)).symm
                              (BHW.realEmbed
                                (BHW.os45CommonEdgeRealPoint
                                  (d := d) (n := n)
                                  (1 : Equiv.Perm (Fin n))
                                  (eflat.symm x)))) ∧
                        A.center ∈ A.carrier ∧
                        A.carrier ⊆
                          ({z : Fin n → Fin (d + 1) → ℂ |
                            BHW.permAct (d := d) P.τ z ∈
                              BHW.ForwardTube d n} ∩ H.ΩJ) ∧
                        Set.EqOn A.branch
                          (fun z : Fin n → Fin (d + 1) → ℂ =>
                            bvt_F OS lgc n
                              (BHW.permAct (d := d) P.τ z))
                          A.carrier := by
                  intro x hx
                  have hterm := hAdj_raw_path_chart x hx (1 : unitInterval)
                  simpa [BHW.os45Figure24IdentityPath_one] using hterm
                have hAdj_local_cover_data :
                    ∀ y : K0,
                      ∃ V : Set (BHW.OS45FlatCommonChartReal d n),
                        IsOpen V ∧ y.1 ∈ V ∧
                        (∃ c R, V ⊆ Metric.closedBall c R) ∧
                        V ⊆ BHW.os45FlatCommonChartEdgeSet d n P
                          (1 : Equiv.Perm (Fin n)) ∧
                        eflat.symm '' V ⊆ Usrc ∧
                        ∃ A0 A1 : PointedMetricBranchChart
                            (Fin n → Fin (d + 1) → ℂ) ℂ,
                          A0.center =
                              BHW.permAct (d := d) P.τ
                                (fun k =>
                                  wickRotatePoint ((eflat.symm y.1) k)) ∧
                          A0.center ∈ A0.carrier ∧
                          A0.carrier ⊆
                              (({z : Fin n → Fin (d + 1) → ℂ |
                                  BHW.permAct (d := d) P.τ z ∈
                                    BHW.ForwardTube d n} ∩ H.ΩJ) ∩
                                (BHW.ExtendedTube d n ∩
                                  BHW.permutedExtendedTubeSector d n P.τ)) ∧
                          Set.EqOn A0.branch
                            (fun z : Fin n → Fin (d + 1) → ℂ =>
                              bvt_F OS lgc n
                                (BHW.permAct (d := d) P.τ z))
                            A0.carrier ∧
                          A0.branch A0.center =
                            bvt_F OS lgc n
                              (fun k =>
                                wickRotatePoint ((eflat.symm y.1) (P.τ k))) ∧
                          A1.center =
                              BHW.permAct (d := d) P.τ
                                ((BHW.os45QuarterTurnCLE
                                  (d := d) (n := n)).symm
                                  (BHW.realEmbed
                                    (BHW.os45CommonEdgeRealPoint
                                      (d := d) (n := n)
                                      (1 : Equiv.Perm (Fin n))
                                      (eflat.symm y.1)))) ∧
                          A1.center ∈ A1.carrier ∧
                          A1.carrier ⊆
                            ({z : Fin n → Fin (d + 1) → ℂ |
                              BHW.permAct (d := d) P.τ z ∈
                                BHW.ForwardTube d n} ∩ H.ΩJ) ∧
                          Set.EqOn A1.branch
                            (fun z : Fin n → Fin (d + 1) → ℂ =>
                              bvt_F OS lgc n
                                (BHW.permAct (d := d) P.τ z))
                            A1.carrier ∧
                          (∀ x ∈ V,
                            BHW.permAct (d := d) P.τ
                              (fun k => wickRotatePoint ((eflat.symm x) k)) ∈
                                A0.carrier) ∧
                          (∀ x ∈ V,
                            BHW.permAct (d := d) P.τ
                              ((BHW.os45QuarterTurnCLE
                                (d := d) (n := n)).symm
                                (BHW.realEmbed
                                  (BHW.os45CommonEdgeRealPoint
                                    (d := d) (n := n)
                                    (1 : Equiv.Perm (Fin n))
                                    (eflat.symm x)))) ∈
                                A1.carrier) ∧
                          ∃ Ucorr : Set
                              (Fin n → Fin (d + 1) → ℂ),
                            IsOpen Ucorr ∧
                            IsConnected Ucorr ∧
                            BHW.permAct (d := d) P.τ
                              (fun k =>
                                wickRotatePoint ((eflat.symm y.1) k)) ∈
                              Ucorr ∧
                            BHW.permAct (d := d) P.τ
                              ((BHW.os45QuarterTurnCLE
                                (d := d) (n := n)).symm
                                (BHW.realEmbed
                                  (BHW.os45CommonEdgeRealPoint
                                    (d := d) (n := n)
                                    (1 : Equiv.Perm (Fin n))
                                    (eflat.symm y.1)))) ∈ Ucorr ∧
                            Ucorr ⊆
                              BHW.ExtendedTube d n ∩
                                BHW.permutedExtendedTubeSector d n P.τ ∧
                            (∀ x ∈ V,
                              BHW.permAct (d := d) P.τ
                                (fun k =>
                                  wickRotatePoint ((eflat.symm x) k)) ∈
                                Ucorr) ∧
                            ∀ x ∈ V,
                              BHW.permAct (d := d) P.τ
                                ((BHW.os45QuarterTurnCLE
                                  (d := d) (n := n)).symm
                                  (BHW.realEmbed
                                    (BHW.os45CommonEdgeRealPoint
                                      (d := d) (n := n)
                                      (1 : Equiv.Perm (Fin n))
                                      (eflat.symm x)))) ∈ Ucorr := by
                  intro y
                  rcases hAdj_base_chart y.1 y.2 with
                    ⟨A0, hA0_center, hA0_mem, hA0_sub,
                      hA0_model, hA0_trace⟩
                  rcases hAdj_raw_terminal_chart y.1 y.2 with
                    ⟨A1, hA1_center, hA1_mem, hA1_sub, hA1_model⟩
                  let zAdjWick :
                      BHW.OS45FlatCommonChartReal d n →
                        Fin n → Fin (d + 1) → ℂ := fun x =>
                    BHW.permAct (d := d) P.τ
                      (fun k => wickRotatePoint ((eflat.symm x) k))
                  let zAdjCommon :
                      BHW.OS45FlatCommonChartReal d n →
                        Fin n → Fin (d + 1) → ℂ := fun x =>
                    BHW.permAct (d := d) P.τ
                      ((BHW.os45QuarterTurnCLE
                        (d := d) (n := n)).symm
                        (BHW.realEmbed
                          (BHW.os45CommonEdgeRealPoint
                            (d := d) (n := n)
                            (1 : Equiv.Perm (Fin n))
                            (eflat.symm x))))
                  have hzAdjWick_cont : Continuous zAdjWick := by
                    change
                      Continuous
                        ((BHW.permAct (d := d) P.τ) ∘
                          ((fun x : NPointDomain d n =>
                            fun k => wickRotatePoint (x k)) ∘ eflat.symm))
                    exact
                      (BHW.differentiable_permAct
                        (d := d) (n := n) P.τ).continuous.comp
                        ((BHW.continuous_wickRotateRealConfig
                          (d := d) (n := n)).comp
                          eflat.symm.continuous)
                  have hzAdjCommon_cont : Continuous zAdjCommon := by
                    change
                      Continuous
                        ((BHW.permAct (d := d) P.τ) ∘
                          ((BHW.os45QuarterTurnCLE
                            (d := d) (n := n)).symm ∘
                            (fun x : NPointDomain d n =>
                              BHW.realEmbed
                                (BHW.os45CommonEdgeRealPoint
                                  (d := d) (n := n)
                                  (1 : Equiv.Perm (Fin n)) x)) ∘
                            eflat.symm))
                    exact
                      (BHW.differentiable_permAct
                        (d := d) (n := n) P.τ).continuous.comp
                        ((BHW.os45QuarterTurnCLE
                          (d := d) (n := n)).symm.continuous.comp
                          ((BHW.continuous_realEmbed_os45CommonEdgeRealPoint
                            (d := d) (n := n)
                            (1 : Equiv.Perm (Fin n))).comp
                            eflat.symm.continuous))
                  rcases hAdj_raw_corridor y.1 y.2 with
                    ⟨Ucorr, hUcorr_open, hUcorr_connected,
                      hUcorr_wick, hUcorr_common, hUcorr_sub⟩
                  let V : Set (BHW.OS45FlatCommonChartReal d n) :=
                    (((((E ∩ (eflat.symm ⁻¹' Usrc)) ∩
                          Metric.ball y.1 1) ∩
                        zAdjWick ⁻¹' A0.carrier) ∩
                        zAdjCommon ⁻¹' A1.carrier) ∩
                      zAdjWick ⁻¹' Ucorr) ∩
                      zAdjCommon ⁻¹' Ucorr
                  refine ⟨V, ?_, ?_, ?_, ?_, ?_⟩
                  · exact
                      (((((hE_open.inter
                        (hUsrc_open.preimage
                          eflat.symm.continuous)).inter
                          Metric.isOpen_ball).inter
                          (A0.carrier_open.preimage hzAdjWick_cont)).inter
                          (A1.carrier_open.preimage hzAdjCommon_cont)).inter
                          (hUcorr_open.preimage hzAdjWick_cont)).inter
                          (hUcorr_open.preimage hzAdjCommon_cont)
                  · exact
                      ⟨⟨⟨⟨⟨⟨hK0_E y.property,
                            hK0_preimage_Usrc
                              (y : BHW.OS45FlatCommonChartReal d n)
                              y.property⟩,
                          Metric.mem_ball_self
                            (by norm_num : (0 : ℝ) < 1)⟩,
                        by simpa [zAdjWick, hA0_center] using hA0_mem⟩,
                        by simpa [zAdjCommon, hA1_center] using hA1_mem⟩,
                        by simpa [zAdjWick, hA0_center] using hUcorr_wick⟩,
                        by simpa [zAdjCommon, hA1_center] using hUcorr_common⟩
                  · refine ⟨y.1, (1 : ℝ), ?_⟩
                    intro z hz
                    rcases hz with
                      ⟨⟨⟨⟨⟨⟨_hzE, _hzUsrc⟩, hzball⟩,
                            _hzA0⟩, _hzA1⟩, _hzCorrW⟩, _hzCorrC⟩
                    exact Metric.ball_subset_closedBall hzball
                  · intro z hz
                    rcases hz with
                      ⟨⟨⟨⟨⟨⟨hzE, _hzUsrc⟩, _hzball⟩,
                            _hzA0⟩, _hzA1⟩, _hzCorrW⟩, _hzCorrC⟩
                    exact hE_sub hzE
                  · constructor
                    · rintro u ⟨z, hz, rfl⟩
                      rcases hz with
                        ⟨⟨⟨⟨⟨⟨_hzE, hzUsrc⟩, _hzball⟩,
                              _hzA0⟩, _hzA1⟩, _hzCorrW⟩, _hzCorrC⟩
                      exact hzUsrc
                    · exact
                        ⟨A0, A1, hA0_center, hA0_mem, hA0_sub,
                          hA0_model, hA0_trace, hA1_center, hA1_mem,
                          hA1_sub, hA1_model,
                          (by
                              intro x hx
                              rcases hx with
                                ⟨⟨⟨⟨⟨⟨_hxE, _hxUsrc⟩, _hxball⟩,
                                      hxA0⟩, _hxA1⟩, _hxCorrW⟩,
                                  _hxCorrC⟩
                              exact hxA0),
                            (by
                              intro x hx
                              rcases hx with
                                ⟨⟨⟨⟨⟨⟨_hxE, _hxUsrc⟩, _hxball⟩,
                                      _hxA0⟩, hxA1⟩, _hxCorrW⟩,
                                  _hxCorrC⟩
                              exact hxA1),
                            ⟨Ucorr, hUcorr_open, hUcorr_connected,
                              by simpa [zAdjWick] using hUcorr_wick,
                              by simpa [zAdjCommon] using hUcorr_common,
                              hUcorr_sub,
                              (by
                                intro x hx
                                rcases hx with
                                  ⟨⟨⟨⟨⟨⟨_hxE, _hxUsrc⟩, _hxball⟩,
                                        _hxA0⟩, _hxA1⟩, hxCorrW⟩,
                                    _hxCorrC⟩
                                exact hxCorrW),
                              (by
                                intro x hx
                                rcases hx with
                                  ⟨⟨⟨⟨⟨⟨_hxE, _hxUsrc⟩, _hxball⟩,
                                        _hxA0⟩, _hxA1⟩, _hxCorrW⟩,
                                    hxCorrC⟩
                                exact hxCorrC)⟩⟩
                obtain ⟨sAdj, hsAdj_cover⟩ :=
                  hK0_compact.elim_finite_subcover
                    (fun y : K0 =>
                      Classical.choose (hAdj_local_cover_data y))
                    (fun y =>
                      (Classical.choose_spec
                        (hAdj_local_cover_data y)).1)
                    (by
                      intro x hx
                      exact Set.mem_iUnion.mpr
                        ⟨⟨x, hx⟩,
                          (Classical.choose_spec
                            (hAdj_local_cover_data ⟨x, hx⟩)).2.1⟩)
                let αAdj := sAdj
                let UAdjloc : αAdj →
                    Set (BHW.OS45FlatCommonChartReal d n) := fun a =>
                  Classical.choose (hAdj_local_cover_data a.1)
                have hUAdjloc_open :
                    ∀ a : αAdj, IsOpen (UAdjloc a) := by
                  intro a
                  exact
                    (Classical.choose_spec
                      (hAdj_local_cover_data a.1)).1
                have hUAdjloc_relcompact :
                    ∀ a : αAdj, ∃ c R, UAdjloc a ⊆
                      Metric.closedBall c R := by
                  intro a
                  exact
                    (Classical.choose_spec
                      (hAdj_local_cover_data a.1)).2.2.1
                have hUAdjloc_edge :
                    ∀ a : αAdj, UAdjloc a ⊆
                      BHW.os45FlatCommonChartEdgeSet d n P
                        (1 : Equiv.Perm (Fin n)) := by
                  intro a
                  exact
                    (Classical.choose_spec
                      (hAdj_local_cover_data a.1)).2.2.2.1
                have hUAdjloc_source :
                    ∀ a : αAdj, eflat.symm '' UAdjloc a ⊆ Usrc := by
                  intro a
                  exact
                    (Classical.choose_spec
                      (hAdj_local_cover_data a.1)).2.2.2.2.1
                have hcoverAdj_K0 :
                    K0 ⊆ ⋃ a : αAdj, UAdjloc a := by
                  intro x hx
                  have hxcover := hsAdj_cover hx
                  rcases Set.mem_iUnion.mp hxcover with ⟨y, hycover⟩
                  rcases Set.mem_iUnion.mp hycover with ⟨hys, hxy⟩
                  exact Set.mem_iUnion.mpr ⟨⟨y, hys⟩, hxy⟩
                obtain ⟨χAdj, hχAdj_compact, hχAdj_sub, hχAdj_sum⟩ :=
                  SCV.exists_finite_schwartz_partitionOfUnity_on_compact
                    (E := BHW.OS45FlatCommonChartReal d n)
                    hK0_compact hUAdjloc_open hUAdjloc_relcompact
                    hcoverAdj_K0
                let ψAdjPieceFlat : αAdj →
                    SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ :=
                  fun a =>
                    SchwartzMap.smulLeftCLM ℂ
                      (χAdj a :
                        BHW.OS45FlatCommonChartReal d n → ℂ)
                      ψ0Flat
                have hψAdjFlat_sum :
                    ψ0Flat = ∑ a : αAdj, ψAdjPieceFlat a := by
                  simpa [ψAdjPieceFlat] using
                    SCV.schwartzMap_eq_finset_sum_smulLeftCLM_of_sum_eq_one_on_tsupport
                      (Finset.univ : Finset αAdj) χAdj ψ0Flat
                      (by
                        intro x hx
                        simpa using hχAdj_sum x hx)
                let pullAdjFlat :
                    SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ]
                      SchwartzNPoint d n :=
                  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eflat
                let χAdjSource : αAdj → SchwartzNPoint d n := fun a =>
                  pullAdjFlat (χAdj a)
                let ψAdjPieceSource : αAdj → SchwartzNPoint d n := fun a =>
                  pullAdjFlat (ψAdjPieceFlat a)
                have hpullAdjFlat_ψ0 : pullAdjFlat ψ0Flat = ψ0 := by
                  ext u
                  simp [pullAdjFlat, ψ0Flat, eflat,
                    SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
                have hψAdjPieceSource_smul :
                    ∀ a : αAdj,
                      ψAdjPieceSource a =
                        SchwartzMap.smulLeftCLM ℂ
                          (χAdjSource a) ψ0 := by
                  intro a
                  have hχ_comp :
                      (((χAdjSource a : SchwartzNPoint d n) :
                          NPointDomain d n → ℂ) ∘ eflat.symm) =
                        ((χAdj a :
                          SchwartzMap
                            (BHW.OS45FlatCommonChartReal d n) ℂ) :
                          BHW.OS45FlatCommonChartReal d n → ℂ) := by
                    funext x
                    simp [χAdjSource, pullAdjFlat,
                      SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
                  have hcomp :=
                    SchwartzMap.smulLeftCLM_compCLMOfContinuousLinearEquiv
                      (𝕜 := ℂ) (𝕜' := ℂ)
                      (D := NPointDomain d n)
                      (E := BHW.OS45FlatCommonChartReal d n)
                      (F := ℂ)
                      (u := ((χAdjSource a : SchwartzNPoint d n) :
                        NPointDomain d n → ℂ))
                      (χAdjSource a).hasTemperateGrowth
                      eflat ψ0Flat
                  calc
                    ψAdjPieceSource a =
                        pullAdjFlat (ψAdjPieceFlat a) := rfl
                    _ =
                        pullAdjFlat
                          (SchwartzMap.smulLeftCLM ℂ
                            (((χAdjSource a : SchwartzNPoint d n) :
                              NPointDomain d n → ℂ) ∘ eflat.symm)
                            ψ0Flat) := by
                          simp [ψAdjPieceFlat, hχ_comp]
                    _ =
                        SchwartzMap.smulLeftCLM ℂ
                          (χAdjSource a) (pullAdjFlat ψ0Flat) := by
                          simpa [pullAdjFlat] using hcomp.symm
                    _ =
                        SchwartzMap.smulLeftCLM ℂ
                          (χAdjSource a) ψ0 := by
                          rw [hpullAdjFlat_ψ0]
                have hψAdjPieceSource_zd :
                    ∀ a : αAdj,
                      VanishesToInfiniteOrderOnCoincidence
                        (ψAdjPieceSource a) := by
                  intro a
                  have hψ0_zd :
                      VanishesToInfiniteOrderOnCoincidence ψ0 :=
                    (D.toZeroDiagonalCLM
                      (1 : Equiv.Perm (Fin n)) φ).property
                  rw [hψAdjPieceSource_smul a]
                  exact
                    VanishesToInfiniteOrderOnCoincidence.smulLeft_schwartzNPoint
                      hψ0_zd
                let ψAdjPieceZD : αAdj → ZeroDiagonalSchwartz d n :=
                  fun a => ⟨ψAdjPieceSource a, hψAdjPieceSource_zd a⟩
                have hψAdjSource_sum :
                    (∑ a : αAdj, ψAdjPieceSource a) = ψ0 := by
                  calc
                    (∑ a : αAdj, ψAdjPieceSource a)
                        = pullAdjFlat (∑ a : αAdj,
                            ψAdjPieceFlat a) := by
                          simp [ψAdjPieceSource, pullAdjFlat, map_sum]
                    _ = pullAdjFlat ψ0Flat := by
                          rw [← hψAdjFlat_sum]
                    _ = ψ0 := hpullAdjFlat_ψ0
                have hψAdjZD_sum :
                    (∑ a : αAdj, ψAdjPieceZD a) =
                      D.toZeroDiagonalCLM
                        (1 : Equiv.Perm (Fin n)) φ := by
                  apply Subtype.ext
                  change
                    (zeroDiagonalSubmodule d n).subtype
                      (∑ a : αAdj, ψAdjPieceZD a) = ψ0
                  rw [_root_.map_sum]
                  simpa [ψAdjPieceZD, ψ0] using hψAdjSource_sum
                have hflatAdj_selected :
                    Tendsto
                      (fun ε : ℝ =>
                      ∫ x : BHW.OS45FlatCommonChartReal d n,
                        BHW.os45FlatCommonChartBranch d n OS lgc σAdj
                          (fun j =>
                            (x j : ℂ) +
                              ((((-1 : ℝ) * ε) • η0) j : ℂ) *
                                Complex.I) *
                        (SCV.translateSchwartz
                          (-((-1 : ℝ) * ε) • η0) ψ0Flat) x)
                    (𝓝[Set.Ioi 0] (0 : ℝ))
                    (𝓝
                      (J * OS.S n (D.toZeroDiagonalCLM
                        (1 : Equiv.Perm (Fin n)) φ))) := by
                  /-
                  Retained raw `(4.12)` fixed flat selector, now localized
                  over the compact flat support.  The remaining hard leaf is
                  per-piece: transport the raw incoming current through the
                  one-branch chain to the terminal source-side chart.
                  -/
                  let FlatAdjPiece : αAdj → ℝ → ℂ := fun a ε =>
                    ∫ x : BHW.OS45FlatCommonChartReal d n,
                      BHW.os45FlatCommonChartBranch d n OS lgc σAdj
                        (fun j =>
                          (x j : ℂ) +
                            ((((-1 : ℝ) * ε) • η0) j : ℂ) *
                              Complex.I) *
                      (SCV.translateSchwartz
                        (-((-1 : ℝ) * ε) • η0)
                        (ψAdjPieceFlat a)) x
                  have hψAdjPieceFlat_compact :
                      ∀ a : αAdj,
                        HasCompactSupport
                          (ψAdjPieceFlat a :
                            BHW.OS45FlatCommonChartReal d n → ℂ) := by
                    intro a
                    refine hψ0Flat_packet.1.mono' ?_
                    intro x hx
                    have hx_ts :
                        x ∈ tsupport
                          (ψAdjPieceFlat a :
                            BHW.OS45FlatCommonChartReal d n → ℂ) :=
                      subset_closure hx
                    exact
                      ((SchwartzMap.tsupport_smulLeftCLM_subset
                        (F := ℂ)
                        (g := (χAdj a :
                          BHW.OS45FlatCommonChartReal d n → ℂ))
                        (f := ψ0Flat)) hx_ts).1
                  have hψAdjPieceFlat_omega :
                      ∀ a : αAdj,
                        ∀ x ∈ tsupport
                            (ψAdjPieceFlat a :
                              BHW.OS45FlatCommonChartReal d n → ℂ),
                          (fun j => (x j : ℂ)) ∈
                            BHW.os45FlatCommonChartOmega d n σAdj := by
                    intro a x hx
                    have hx0 :
                        x ∈ tsupport
                          (ψ0Flat :
                            BHW.OS45FlatCommonChartReal d n → ℂ) :=
                      ((SchwartzMap.tsupport_smulLeftCLM_subset
                        (F := ℂ)
                        (g := (χAdj a :
                          BHW.OS45FlatCommonChartReal d n → ℂ))
                        (f := ψ0Flat)) hx).1
                    simpa [σAdj] using
                      BHW.os45FlatCommonChart_real_mem_omega_adjacent
                        (d := d) hd (P := P) x
                        (hψ0Flat_packet.2 hx0)
                  have hAdj_piece_shifted_integrable :
                      ∀ a : αAdj,
                        ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
                          Integrable
                          (fun x :
                            BHW.OS45FlatCommonChartReal d n =>
                          BHW.os45FlatCommonChartBranch d n OS lgc σAdj
                            (fun j =>
                              ((x + ((-1 : ℝ) * ε) • η0) j : ℂ) +
                                ((((-1 : ℝ) * ε) • η0) j : ℂ) *
                                  Complex.I) *
                            (SCV.translateSchwartz
                              (-((-1 : ℝ) * ε) • η0)
                              (ψAdjPieceFlat a))
                              (x + ((-1 : ℝ) * ε) • η0)) := by
                    intro a
                    simpa using
                      BHW.os45FlatCommonChart_fixedTranslatedTest_integrable_eventually
                        (d := d) (n := n) OS lgc
                        σAdj (-1 : ℝ) η0
                        (ψAdjPieceFlat a)
                        (hψAdjPieceFlat_compact a)
                        (hψAdjPieceFlat_omega a)
                  have hAdj_piece_integrable :
                      ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
                        ∀ a : αAdj,
                          Integrable
                          (fun x :
                            BHW.OS45FlatCommonChartReal d n =>
                          BHW.os45FlatCommonChartBranch d n OS lgc σAdj
                            (fun j =>
                              (x j : ℂ) +
                                ((((-1 : ℝ) * ε) • η0) j : ℂ) *
                                  Complex.I) *
                            (SCV.translateSchwartz
                              (-((-1 : ℝ) * ε) • η0)
                              (ψAdjPieceFlat a)) x) := by
                    have hall_shifted :
                        ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
                          ∀ a : αAdj,
                            Integrable
                            (fun x :
                              BHW.OS45FlatCommonChartReal d n =>
                            BHW.os45FlatCommonChartBranch d n OS lgc σAdj
                              (fun j =>
                                ((x + ((-1 : ℝ) * ε) • η0) j : ℂ) +
                                  ((((-1 : ℝ) * ε) • η0) j : ℂ) *
                                    Complex.I) *
                              (SCV.translateSchwartz
                                (-((-1 : ℝ) * ε) • η0)
                                (ψAdjPieceFlat a))
                                (x + ((-1 : ℝ) * ε) • η0)) :=
                      Filter.eventually_all.mpr
                        hAdj_piece_shifted_integrable
                    filter_upwards [hall_shifted] with ε hε a
                    let s : BHW.OS45FlatCommonChartReal d n :=
                      ((-1 : ℝ) * ε) • η0
                    have hcomp := (hε a).comp_add_right (-s)
                    refine hcomp.congr (Filter.Eventually.of_forall ?_)
                    intro x
                    simp [s, add_left_comm, add_comm]
                  have hψAdjPieceFlat_sub_U :
                      ∀ a : αAdj,
                        tsupport
                            (ψAdjPieceFlat a :
                              BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
                          UAdjloc a := by
                    intro a x hx
                    exact
                      hχAdj_sub a
                        ((SchwartzMap.tsupport_smulLeftCLM_subset
                          (F := ℂ)
                          (g := (χAdj a :
                            BHW.OS45FlatCommonChartReal d n → ℂ))
                          (f := ψ0Flat)) hx).2
                  have hψAdjPieceSource_compact :
                      ∀ a : αAdj,
                        HasCompactSupport
                          (ψAdjPieceSource a :
                            NPointDomain d n → ℂ) := by
                    intro a
                    simpa [ψAdjPieceSource, pullAdjFlat,
                      SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
                      using
                        (hψAdjPieceFlat_compact a).comp_homeomorph
                          eflat.toHomeomorph
                  have hψAdjPieceSource_Usrc :
                      ∀ a : αAdj,
                        tsupport
                            (ψAdjPieceSource a :
                              NPointDomain d n → ℂ) ⊆ Usrc := by
                    intro a u hu
                    have hu_flat :
                        eflat u ∈ tsupport
                          (ψAdjPieceFlat a :
                            BHW.OS45FlatCommonChartReal d n → ℂ) := by
                      have hpre :=
                        tsupport_comp_subset_preimage
                          (ψAdjPieceFlat a :
                            BHW.OS45FlatCommonChartReal d n → ℂ)
                          eflat.continuous
                      simpa [ψAdjPieceSource, pullAdjFlat,
                        SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
                        using hpre hu
                    exact
                      hUAdjloc_source a
                        ⟨eflat u,
                          hψAdjPieceFlat_sub_U a hu_flat,
                          by simp [eflat]⟩
                  have hflatAdj_piece :
                      ∀ a : αAdj,
                        Tendsto (FlatAdjPiece a)
                          (𝓝[Set.Ioi 0] (0 : ℝ))
                          (𝓝 (J * OS.S n (ψAdjPieceZD a))) := by
                    intro a
                    let AdjPieceFixed : ℝ → ℂ := fun ε =>
                      ∫ u : NPointDomain d n,
                        BHW.extendF (bvt_F OS lgc n)
                          (BHW.permAct (d := d) τout
                            (BHW.os45FlatCommonChartSourceSide d n
                              (1 : Equiv.Perm (Fin n)) (-1 : ℝ)
                              ε η0 u)) *
                        (ψAdjPieceSource a : NPointDomain d n → ℂ) u
                    have hFlat_piece_eq_fixed :
                        FlatAdjPiece a
                          =ᶠ[𝓝[Set.Ioi 0] (0 : ℝ)]
                        fun ε : ℝ => J * AdjPieceFixed ε := by
                      filter_upwards
                        [hAdj_piece_shifted_integrable a] with ε hε
                      have heq :=
                        BHW.os45FlatCommonChart_branch_integral_eq_sourceSide_extendF_translatedTest
                          (d := d) (n := n) OS lgc
                          σAdj (1 : Equiv.Perm (Fin n))
                          (-1 : ℝ) ε η0 (ψAdjPieceFlat a) hε
                      simpa [FlatAdjPiece, AdjPieceFixed, J,
                        ψAdjPieceSource, pullAdjFlat, eflat, σAdj, τout,
                        SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
                        one_mul] using heq
                    have hψAdjPieceFlat_edge :
                        tsupport
                            (ψAdjPieceFlat a :
                              BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
                          BHW.os45FlatCommonChartEdgeSet d n P
                            (1 : Equiv.Perm (Fin n)) :=
                      (hψAdjPieceFlat_sub_U a).trans
                        (hUAdjloc_edge a)
                    have hD_adj_piece_plain :
                        D.toSchwartzNPointCLM
                            (1 : Equiv.Perm (Fin n))
                            (ψAdjPieceFlat a) =
                          ψAdjPieceSource a := by
                      ext u
                      have hplain :=
                        D.toSchwartzNPointCLM_eq_plain_of_tsupport_subset_edge
                          (1 : Equiv.Perm (Fin n))
                          (ψAdjPieceFlat a) hψAdjPieceFlat_edge u
                      simpa [ψAdjPieceSource, pullAdjFlat, eflat,
                        SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
                        using hplain
                    have hD_adj_piece_zd :
                        D.toZeroDiagonalCLM
                            (1 : Equiv.Perm (Fin n))
                            (ψAdjPieceFlat a) =
                          ψAdjPieceZD a := by
                      apply Subtype.ext
                      change
                        D.toSchwartzNPointCLM
                            (1 : Equiv.Perm (Fin n))
                            (ψAdjPieceFlat a) =
                          ψAdjPieceSource a
                      exact hD_adj_piece_plain
                    have hUAdjloc_chart_data :
                        ∃ A0 A1 : PointedMetricBranchChart
                            (Fin n → Fin (d + 1) → ℂ) ℂ,
                          A0.center =
                              BHW.permAct (d := d) P.τ
                                (fun k =>
                                  wickRotatePoint ((eflat.symm a.1.1) k)) ∧
                          A0.center ∈ A0.carrier ∧
                          A0.carrier ⊆
                              (({z : Fin n → Fin (d + 1) → ℂ |
                                  BHW.permAct (d := d) P.τ z ∈
                                    BHW.ForwardTube d n} ∩ H.ΩJ) ∩
                                (BHW.ExtendedTube d n ∩
                                  BHW.permutedExtendedTubeSector d n P.τ)) ∧
                          Set.EqOn A0.branch
                            (fun z : Fin n → Fin (d + 1) → ℂ =>
                              bvt_F OS lgc n
                                (BHW.permAct (d := d) P.τ z))
                            A0.carrier ∧
                          A0.branch A0.center =
                            bvt_F OS lgc n
                              (fun k =>
                                wickRotatePoint ((eflat.symm a.1.1) (P.τ k))) ∧
                          A1.center =
                              BHW.permAct (d := d) P.τ
                                ((BHW.os45QuarterTurnCLE
                                  (d := d) (n := n)).symm
                                  (BHW.realEmbed
                                    (BHW.os45CommonEdgeRealPoint
                                      (d := d) (n := n)
                                      (1 : Equiv.Perm (Fin n))
                                      (eflat.symm a.1.1)))) ∧
                          A1.center ∈ A1.carrier ∧
                          A1.carrier ⊆
                            ({z : Fin n → Fin (d + 1) → ℂ |
                              BHW.permAct (d := d) P.τ z ∈
                                BHW.ForwardTube d n} ∩ H.ΩJ) ∧
                          Set.EqOn A1.branch
                            (fun z : Fin n → Fin (d + 1) → ℂ =>
                              bvt_F OS lgc n
                                (BHW.permAct (d := d) P.τ z))
                            A1.carrier ∧
                          (∀ x ∈ UAdjloc a,
                            BHW.permAct (d := d) P.τ
                              (fun k => wickRotatePoint ((eflat.symm x) k)) ∈
                                A0.carrier) ∧
                          (∀ x ∈ UAdjloc a,
                            BHW.permAct (d := d) P.τ
                              ((BHW.os45QuarterTurnCLE
                                (d := d) (n := n)).symm
                                (BHW.realEmbed
                                  (BHW.os45CommonEdgeRealPoint
                                    (d := d) (n := n)
                                    (1 : Equiv.Perm (Fin n))
                                    (eflat.symm x)))) ∈
                                A1.carrier) ∧
                          ∃ Ucorr : Set
                              (Fin n → Fin (d + 1) → ℂ),
                            IsOpen Ucorr ∧
                            IsConnected Ucorr ∧
                            BHW.permAct (d := d) P.τ
                              (fun k =>
                                wickRotatePoint ((eflat.symm a.1.1) k)) ∈
                              Ucorr ∧
                            BHW.permAct (d := d) P.τ
                              ((BHW.os45QuarterTurnCLE
                                (d := d) (n := n)).symm
                                (BHW.realEmbed
                                  (BHW.os45CommonEdgeRealPoint
                                    (d := d) (n := n)
                                    (1 : Equiv.Perm (Fin n))
                                    (eflat.symm a.1.1)))) ∈ Ucorr ∧
                            Ucorr ⊆
                              BHW.ExtendedTube d n ∩
                                BHW.permutedExtendedTubeSector d n P.τ ∧
                            (∀ x ∈ UAdjloc a,
                              BHW.permAct (d := d) P.τ
                                (fun k =>
                                  wickRotatePoint ((eflat.symm x) k)) ∈
                                Ucorr) ∧
                            ∀ x ∈ UAdjloc a,
                              BHW.permAct (d := d) P.τ
                                ((BHW.os45QuarterTurnCLE
                                  (d := d) (n := n)).symm
                                  (BHW.realEmbed
                                    (BHW.os45CommonEdgeRealPoint
                                      (d := d) (n := n)
                                      (1 : Equiv.Perm (Fin n))
                                      (eflat.symm x)))) ∈ Ucorr := by
                      simpa [UAdjloc] using
                        (Classical.choose_spec
                          (hAdj_local_cover_data a.1)).2.2.2.2.2
                    obtain
                      ⟨A0a, A1a, _hA0a_center, _hA0a_mem,
                        _hA0a_sub, _hA0a_model, _hA0a_trace,
                        _hA1a_center, _hA1a_mem, _hA1a_sub,
                        hA1a_model, hA0a_all, hA1a_all,
                        hAdj_corridor_packet⟩ :=
                      hUAdjloc_chart_data
                    have hAdj_piece_source_to_flat_tsupport :
                        ∀ u ∈ tsupport
                            (ψAdjPieceSource a :
                              NPointDomain d n → ℂ),
                          eflat u ∈ tsupport
                            (ψAdjPieceFlat a :
                              BHW.OS45FlatCommonChartReal d n → ℂ) := by
                      intro u hu
                      have hpre :=
                        tsupport_comp_subset_preimage
                          (ψAdjPieceFlat a :
                            BHW.OS45FlatCommonChartReal d n → ℂ)
                          eflat.continuous
                      simpa [ψAdjPieceSource, pullAdjFlat,
                        SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
                        using hpre hu
                    have hAdj_piece_wick_in_A0 :
                        ∀ u ∈ tsupport
                            (ψAdjPieceSource a :
                              NPointDomain d n → ℂ),
                          BHW.permAct (d := d) P.τ
                            (fun k => wickRotatePoint (u k)) ∈
                            A0a.carrier := by
                      intro u hu
                      have hu_flat :=
                        hAdj_piece_source_to_flat_tsupport u hu
                      have hu_U :
                          eflat u ∈ UAdjloc a :=
                        hψAdjPieceFlat_sub_U a hu_flat
                      simpa [eflat] using
                        hA0a_all (eflat u) hu_U
                    have hAdj_piece_common_in_A1 :
                        ∀ u ∈ tsupport
                            (ψAdjPieceSource a :
                              NPointDomain d n → ℂ),
                          BHW.permAct (d := d) P.τ
                            ((BHW.os45QuarterTurnCLE
                              (d := d) (n := n)).symm
                              (BHW.realEmbed
                                (BHW.os45CommonEdgeRealPoint
                                  (d := d) (n := n)
                                  (1 : Equiv.Perm (Fin n)) u))) ∈
                            A1a.carrier := by
                      intro u hu
                      have hu_flat :=
                        hAdj_piece_source_to_flat_tsupport u hu
                      have hu_U :
                          eflat u ∈ UAdjloc a :=
                        hψAdjPieceFlat_sub_U a hu_flat
                      simpa [eflat] using
                        hA1a_all (eflat u) hu_U
                    obtain
                      ⟨UcorrAdjPiece, hUcorrAdjPiece_open,
                        hUcorrAdjPiece_connected,
                        hUcorrAdjPiece_wick_center,
                        hUcorrAdjPiece_common_center,
                        hUcorrAdjPiece_sub,
                        hUcorrAdjPiece_wick_all,
                        hUcorrAdjPiece_common_all⟩ :=
                      hAdj_corridor_packet
                    have hAdj_piece_wick_in_corridor :
                        ∀ u ∈ tsupport
                            (ψAdjPieceSource a :
                              NPointDomain d n → ℂ),
                          BHW.permAct (d := d) P.τ
                            (fun k => wickRotatePoint (u k)) ∈
                            UcorrAdjPiece := by
                      intro u hu
                      have hu_flat :=
                        hAdj_piece_source_to_flat_tsupport u hu
                      have hu_U :
                          eflat u ∈ UAdjloc a :=
                        hψAdjPieceFlat_sub_U a hu_flat
                      simpa [eflat] using
                        hUcorrAdjPiece_wick_all (eflat u) hu_U
                    have hAdj_piece_common_in_corridor :
                        ∀ u ∈ tsupport
                            (ψAdjPieceSource a :
                              NPointDomain d n → ℂ),
                          BHW.permAct (d := d) P.τ
                            ((BHW.os45QuarterTurnCLE
                              (d := d) (n := n)).symm
                              (BHW.realEmbed
                                (BHW.os45CommonEdgeRealPoint
                                  (d := d) (n := n)
                                  (1 : Equiv.Perm (Fin n)) u))) ∈
                            UcorrAdjPiece := by
                      intro u hu
                      have hu_flat :=
                        hAdj_piece_source_to_flat_tsupport u hu
                      have hu_U :
                          eflat u ∈ UAdjloc a :=
                        hψAdjPieceFlat_sub_U a hu_flat
                      simpa [eflat] using
                        hUcorrAdjPiece_common_all (eflat u) hu_U
                    have hAdj_piece_sourceSide0_in_A1 :
                        ∀ u ∈ tsupport
                            (ψAdjPieceSource a :
                              NPointDomain d n → ℂ),
                          BHW.permAct (d := d) τout
                            (BHW.os45FlatCommonChartSourceSide d n
                              (1 : Equiv.Perm (Fin n)) (-1 : ℝ)
                              0 η0 u) ∈ A1a.carrier := by
                      intro u hu
                      rw [BHW.os45FlatCommonChartSourceSide_zero_eq_commonEdge]
                      simpa [τout, one_mul] using
                        hAdj_piece_common_in_A1 u hu
                    have hAdjWick_eq_ordWick :
                        (∫ u : NPointDomain d n,
                          bvt_F OS lgc n
                            (fun k => wickRotatePoint (u (P.τ k))) *
                          (ψAdjPieceSource a :
                            NPointDomain d n → ℂ) u) =
                        ∫ u : NPointDomain d n,
                          bvt_F OS lgc n
                            (fun k => wickRotatePoint (u k)) *
                          (ψAdjPieceSource a :
                            NPointDomain d n → ℂ) u := by
                      have hraw :=
                        BHW.os45CommonEdge_adjacentWick_sourcePairing_eq_ordinaryWick
                          (d := d) (hd := hd) OS lgc
                          (P := P) D (ψAdjPieceFlat a)
                          hψAdjPieceFlat_edge
                      simpa [hD_adj_piece_plain] using hraw
                    have hAdjRawWick_to_A0 :
                        (∫ u : NPointDomain d n,
                          A0a.branch
                            (BHW.permAct (d := d) P.τ
                              (fun k => wickRotatePoint (u k))) *
                          (ψAdjPieceSource a :
                            NPointDomain d n → ℂ) u) =
                        ∫ u : NPointDomain d n,
                          bvt_F OS lgc n
                            (fun k => wickRotatePoint (u k)) *
                          (ψAdjPieceSource a :
                            NPointDomain d n → ℂ) u := by
                      apply integral_congr_ae
                      refine Filter.Eventually.of_forall ?_
                      intro u
                      by_cases hu :
                          u ∈ tsupport
                            (ψAdjPieceSource a :
                              NPointDomain d n → ℂ)
                      · have hmodel :=
                          _hA0a_model (hAdj_piece_wick_in_A0 u hu)
                        have hseed :=
                          BHW.os45Figure24_OS412SeedBranch_permAct_ordinaryWick_eq_ordinaryWick
                            (d := d) (n := n) (hd := hd) (P := P)
                            OS lgc u
                        calc
                          A0a.branch
                                (BHW.permAct (d := d) P.τ
                                  (fun k => wickRotatePoint (u k))) *
                              (ψAdjPieceSource a :
                                NPointDomain d n → ℂ) u
                              =
                            bvt_F OS lgc n
                                (BHW.permAct (d := d) P.τ
                                  (BHW.permAct (d := d) P.τ
                                    (fun k => wickRotatePoint (u k)))) *
                              (ψAdjPieceSource a :
                                NPointDomain d n → ℂ) u := by
                                rw [hmodel]
                            _ =
                              bvt_F OS lgc n
                                  (fun k => wickRotatePoint (u k)) *
                                (ψAdjPieceSource a :
                                  NPointDomain d n → ℂ) u := by
                                  simpa using
                                    congrArg
                                      (fun c : ℂ =>
                                        c *
                                          (ψAdjPieceSource a :
                                            NPointDomain d n → ℂ) u)
                                      hseed
                      · have hzero :
                            (ψAdjPieceSource a :
                              NPointDomain d n → ℂ) u = 0 :=
                          image_eq_zero_of_notMem_tsupport hu
                        simp [hzero]
                    have hAdjWickPiece_value :
                        (∫ u : NPointDomain d n,
                          bvt_F OS lgc n
                            (fun k => wickRotatePoint (u (P.τ k))) *
                          (ψAdjPieceSource a :
                            NPointDomain d n → ℂ) u) =
                        OS.S n (ψAdjPieceZD a) := by
                      have hraw :=
                        BHW.os45CommonEdge_adjacentWick_sourcePairing_eq_schwinger
                          (d := d) (hd := hd) OS lgc
                          (P := P) D (ψAdjPieceFlat a)
                          hψAdjPieceFlat_edge
                      simpa [ψAdjPieceZD, hD_adj_piece_plain,
                        hD_adj_piece_zd] using hraw
                    have hAdjPieceFixed_endpoint :
                        Tendsto AdjPieceFixed
                          (𝓝[Set.Ioi 0] (0 : ℝ))
                          (𝓝
                            (∫ u : NPointDomain d n,
                              BHW.extendF (bvt_F OS lgc n)
                                (BHW.permAct (d := d) τout
                                  (BHW.os45FlatCommonChartSourceSide d n
                                    (1 : Equiv.Perm (Fin n)) (-1 : ℝ)
                                    0 η0 u)) *
                              (ψAdjPieceSource a :
                                NPointDomain d n → ℂ) u)) := by
                      have h0_piece :
                          ∀ u ∈ tsupport
                              (ψAdjPieceSource a :
                                NPointDomain d n → ℂ),
                            BHW.os45FlatCommonChartSourceSide d n
                              (1 : Equiv.Perm (Fin n)) (-1 : ℝ)
                              0 η0 u ∈ Uadj := by
                        intro u hu
                        exact h0 u
                          (hUsrc_sub_Ksrc
                            (hψAdjPieceSource_Usrc a hu))
                      simpa [AdjPieceFixed] using
                        BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_of_hasCompactSupport
                          (d := d) (n := n)
                          (1 : Equiv.Perm (Fin n)) (-1 : ℝ) η0
                          (U := Uadj) hUadj_open hF_cont
                          (hψAdjPieceSource_compact a)
                          (ψAdjPieceSource a : SchwartzNPoint d n).continuous
                          h0_piece
                    let uaAdj : NPointDomain d n := eflat.symm a.1.1
                    let gammaAdjPiece : unitInterval →
                        Fin n → Fin (d + 1) → ℂ := fun t =>
                      BHW.permAct (d := d) P.τ
                        (BHW.os45Figure24IdentityPath
                          (d := d) (n := n) uaAdj t)
                    let ΩrawAdj :
                        Set (Fin n → Fin (d + 1) → ℂ) :=
                      {z : Fin n → Fin (d + 1) → ℂ |
                        BHW.permAct (d := d) P.τ z ∈
                          BHW.ForwardTube d n} ∩ H.ΩJ
                    let BSeedAdj :
                        (Fin n → Fin (d + 1) → ℂ) → ℂ := fun z =>
                      bvt_F OS lgc n (BHW.permAct (d := d) P.τ z)
                    let ReachAdj : Set unitInterval := {t |
                      ∃ len : ℕ,
                      ∃ chart :
                          Fin (len + 1) →
                            PointedMetricBranchChart
                              (Fin n → Fin (d + 1) → ℂ) ℂ,
                      ∃ edge :
                          ∀ j : Fin len,
                            PointedSeedEdge
                              ((chart (Fin.castSucc j)).center)
                              ((chart (Fin.castSucc j)).carrier)
                              ((chart (Fin.succ j)).carrier)
                              ((chart (Fin.castSucc j)).branch)
                              ((chart (Fin.succ j)).branch),
                        (chart 0).center = gammaAdjPiece 0 ∧
                        (chart (Fin.last len)).center =
                          gammaAdjPiece t ∧
                          ∀ j,
                            Set.EqOn (chart j).branch BSeedAdj
                              (chart j).carrier}
                    have hReachAdj0 :
                        (0 : unitInterval) ∈ ReachAdj := by
                      refine ⟨0, (fun _ => A0a), ?_, ?_, ?_, ?_⟩
                      · intro j
                        exact Fin.elim0 j
                      · change A0a.center = gammaAdjPiece 0
                        calc
                          A0a.center =
                              BHW.permAct (d := d) P.τ
                                (fun k => wickRotatePoint (uaAdj k)) := by
                            simpa [uaAdj] using _hA0a_center
                          _ = gammaAdjPiece 0 := by
                            simpa [gammaAdjPiece] using
                              congrArg (BHW.permAct (d := d) P.τ)
                                (BHW.os45Figure24IdentityPath_zero
                                  (d := d) (n := n) uaAdj).symm
                      · change A0a.center = gammaAdjPiece 0
                        calc
                          A0a.center =
                              BHW.permAct (d := d) P.τ
                                (fun k => wickRotatePoint (uaAdj k)) := by
                            simpa [uaAdj] using _hA0a_center
                          _ = gammaAdjPiece 0 := by
                            simpa [gammaAdjPiece] using
                              congrArg (BHW.permAct (d := d) P.τ)
                                (BHW.os45Figure24IdentityPath_zero
                                  (d := d) (n := n) uaAdj).symm
                      · intro j
                        simpa [BSeedAdj] using _hA0a_model
                    have hgammaAdj_cont :
                        Continuous gammaAdjPiece := by
                      change
                        Continuous
                          ((BHW.permAct (d := d) P.τ) ∘
                            BHW.os45Figure24IdentityPath
                              (d := d) (n := n) uaAdj)
                      exact
                        (BHW.differentiable_permAct
                          (d := d) (n := n) P.τ).continuous.comp
                          (BHW.continuous_os45Figure24IdentityPath
                            (d := d) (n := n) uaAdj)
                    have hgammaAdj_mem :
                        ∀ t : unitInterval, gammaAdjPiece t ∈ ΩrawAdj := by
                      intro t
                      simpa [gammaAdjPiece, ΩrawAdj, uaAdj] using
                        hAdj_raw_path_mem
                          (a.1 : BHW.OS45FlatCommonChartReal d n)
                          a.1.property t
                    have hΩrawAdj_open : IsOpen ΩrawAdj := by
                      simpa [ΩrawAdj] using H.OS412SeedWindow_open
                    have hReachAdj_local :
                        ∀ t : unitInterval,
                          ∃ U : Set unitInterval, IsOpen U ∧ t ∈ U ∧
                            ∀ ⦃s r : unitInterval⦄,
                              s ∈ U → r ∈ U → s ∈ ReachAdj →
                                r ∈ ReachAdj := by
                      intro t
                      rcases Metric.mem_nhds_iff.mp
                          (hΩrawAdj_open.mem_nhds
                            (hgammaAdj_mem t)) with
                        ⟨R, hR_pos, hR_sub⟩
                      let δ : ℝ := R / 4
                      let ρ : ℝ := R / 2
                      have hδ_pos : 0 < δ := by
                        dsimp [δ]
                        linarith
                      have hρ_pos : 0 < ρ := by
                        dsimp [ρ]
                        linarith
                      have hρ_add_δ_lt_R : ρ + δ < R := by
                        dsimp [ρ, δ]
                        linarith
                      let U : Set unitInterval :=
                        gammaAdjPiece ⁻¹'
                          Metric.ball (gammaAdjPiece t) δ
                      refine
                        ⟨U, Metric.isOpen_ball.preimage hgammaAdj_cont,
                          ?_, ?_⟩
                      · exact Metric.mem_ball_self hδ_pos
                      · intro s r hsU hrU hsReach
                        rcases hsReach with
                          ⟨len, chart, edge, hstart, hend, hmodel⟩
                        have hs_near :
                            dist (gammaAdjPiece s) (gammaAdjPiece t) <
                              δ := by
                          simpa [U, Metric.mem_ball] using hsU
                        have hr_near :
                            dist (gammaAdjPiece r) (gammaAdjPiece t) <
                              δ := by
                          simpa [U, Metric.mem_ball] using hrU
                        have hsr_near :
                            dist (gammaAdjPiece s) (gammaAdjPiece r) <
                              ρ := by
                          have htri :
                              dist (gammaAdjPiece s)
                                  (gammaAdjPiece r) ≤
                                dist (gammaAdjPiece s)
                                    (gammaAdjPiece t) +
                                  dist (gammaAdjPiece t)
                                    (gammaAdjPiece r) :=
                            dist_triangle _ _ _
                          have hrt :
                              dist (gammaAdjPiece t)
                                  (gammaAdjPiece r) <
                                δ := by
                            simpa [dist_comm] using hr_near
                          calc
                            dist (gammaAdjPiece s) (gammaAdjPiece r)
                                ≤
                                  dist (gammaAdjPiece s)
                                      (gammaAdjPiece t) +
                                    dist (gammaAdjPiece t)
                                      (gammaAdjPiece r) := htri
                            _ < δ + δ := add_lt_add hs_near hrt
                            _ = ρ := by
                              dsimp [δ, ρ]
                              ring
                        let B : PointedMetricBranchChart
                            (Fin n → Fin (d + 1) → ℂ) ℂ :=
                          { center := gammaAdjPiece r
                            radius := ρ
                            radius_pos := hρ_pos
                            branch := BSeedAdj
                            holo := by
                              exact
                                (H.differentiableOn_OS412SeedBranch
                                  OS lgc).mono
                                  (by
                                    intro w hw
                                    have hwρ :
                                        dist w (gammaAdjPiece r) <
                                          ρ := by
                                      simpa [Metric.mem_ball] using hw
                                    have hrt :
                                        dist (gammaAdjPiece r)
                                            (gammaAdjPiece t) <
                                          δ := hr_near
                                    have hwt :
                                        dist w (gammaAdjPiece t) < R := by
                                      have htri :
                                          dist w (gammaAdjPiece t) ≤
                                            dist w (gammaAdjPiece r) +
                                              dist (gammaAdjPiece r)
                                                (gammaAdjPiece t) :=
                                        dist_triangle _ _ _
                                      calc
                                        dist w (gammaAdjPiece t)
                                            ≤
                                              dist w (gammaAdjPiece r) +
                                                dist (gammaAdjPiece r)
                                                  (gammaAdjPiece t) := htri
                                        _ < ρ + δ := add_lt_add hwρ hrt
                                        _ < R := hρ_add_δ_lt_R
                                    exact
                                      hR_sub
                                        (by simpa [Metric.mem_ball]
                                          using hwt)) }
                        have hB_center_mem : B.center ∈ B.carrier :=
                          B.center_mem
                        have hs_in_B :
                            (chart (Fin.last len)).center ∈ B.carrier := by
                          have hsB : gammaAdjPiece s ∈ B.carrier := by
                            simpa [B, PointedMetricBranchChart.carrier,
                              Metric.mem_ball, dist_comm] using hsr_near
                          simpa [hend] using hsB
                        have hB_model :
                            Set.EqOn B.branch BSeedAdj B.carrier := by
                          intro _w _hw
                          rfl
                        have hB_raw :
                            RawRetargetAtZ0 d n B.center B B :=
                          { z0_mem := hB_center_mem
                            edge_to_raw :=
                              { W := B.carrier
                                W_open := B.carrier_open
                                z0_mem := hB_center_mem
                                W_sub := by
                                  intro z hz
                                  exact ⟨hz, hz⟩
                                eqOn := by
                                  intro _z _hz
                                  rfl } }
                        let chart' :
                            Fin ((len + 1) + 1) →
                              PointedMetricBranchChart
                                (Fin n → Fin (d + 1) → ℂ) ℂ :=
                          Fin.snoc chart B
                        refine ⟨len + 1, chart', ?_, ?_, ?_, ?_⟩
                        · intro j
                          refine Fin.lastCases ?_ ?_ j
                          · have hprev_model := hmodel (Fin.last len)
                            have hnew_edge :
                                PointedSeedEdge
                                  ((chart (Fin.last len)).center)
                                  ((chart (Fin.last len)).carrier)
                                  B.carrier
                                  ((chart (Fin.last len)).branch)
                                  B.branch :=
                              pointed_seed_edge_of_common_model
                                (chart (Fin.last len)).carrier_open
                                B.carrier_open
                                (chart (Fin.last len)).center_mem
                                hs_in_B hprev_model hB_model
                            simpa [chart', Fin.snoc_castSucc,
                              Fin.snoc_last] using hnew_edge
                          · intro j
                            simpa [chart', Fin.snoc_castSucc,
                              ← Fin.castSucc_succ] using edge j
                        · change (chart' 0).center = gammaAdjPiece 0
                          rw [show (0 : Fin ((len + 1) + 1)) =
                            Fin.castSucc (0 : Fin (len + 1)) from rfl]
                          simpa [chart', Fin.snoc_castSucc] using hstart
                        · change
                            (chart' (Fin.last (len + 1))).center =
                              gammaAdjPiece r
                          simpa [chart', Fin.snoc_last, B]
                        · intro j
                          refine Fin.lastCases ?_ ?_ j
                          · simpa [chart', Fin.snoc_last] using hB_model
                          · intro j
                            simpa [chart', Fin.snoc_castSucc] using hmodel j
                    have hReachAdj_all : ReachAdj = Set.univ :=
                      SCV.reachable_eq_univ_of_local_symmetric_extension
                        (E := unitInterval) (Reach := ReachAdj)
                        ⟨0, hReachAdj0⟩ hReachAdj_local
                    obtain
                        ⟨lenAdj, chartAdj, edgeAdj, hstartAdj,
                          hendAdj, hmodelAdj⟩ :
                        ∃ len : ℕ,
                        ∃ chart :
                            Fin (len + 1) →
                              PointedMetricBranchChart
                                (Fin n → Fin (d + 1) → ℂ) ℂ,
                        ∃ edge :
                            ∀ j : Fin len,
                              PointedSeedEdge
                                ((chart (Fin.castSucc j)).center)
                                ((chart (Fin.castSucc j)).carrier)
                                ((chart (Fin.succ j)).carrier)
                                ((chart (Fin.castSucc j)).branch)
                                ((chart (Fin.succ j)).branch),
                          (chart 0).center = gammaAdjPiece 0 ∧
                          (chart (Fin.last len)).center =
                            gammaAdjPiece 1 ∧
                            ∀ j,
                              Set.EqOn (chart j).branch BSeedAdj
                                (chart j).carrier := by
                      have hterminal :
                          (1 : unitInterval) ∈ ReachAdj := by
                        simpa [hReachAdj_all]
                      simpa [ReachAdj] using hterminal
                    have hAdj_terminal_center :
                        (chartAdj (Fin.last lenAdj)).center =
                          A1a.center := by
                      calc
                        (chartAdj (Fin.last lenAdj)).center =
                            gammaAdjPiece 1 := hendAdj
                        _ =
                            BHW.permAct (d := d) P.τ
                              ((BHW.os45QuarterTurnCLE
                                (d := d) (n := n)).symm
                                (BHW.realEmbed
                                  (BHW.os45CommonEdgeRealPoint
                                    (d := d) (n := n)
                                    (1 : Equiv.Perm (Fin n)) uaAdj))) := by
                              simpa [gammaAdjPiece] using
                                congrArg (BHW.permAct (d := d) P.τ)
                                  (BHW.os45Figure24IdentityPath_one
                                    (d := d) (n := n) uaAdj)
                        _ = A1a.center := by
                              simpa [uaAdj] using _hA1a_center.symm
                    have hAdj_terminal_model :
                        Set.EqOn
                          ((chartAdj (Fin.last lenAdj)).branch) BSeedAdj
                          ((chartAdj (Fin.last lenAdj)).carrier) :=
                      hmodelAdj (Fin.last lenAdj)
                    have hA1a_raw_model :
                        Set.EqOn A1a.branch BSeedAdj A1a.carrier := by
                      simpa [BSeedAdj] using hA1a_model
                    have hAdj_terminal_edge_to_A1 :
                        PointedSeedEdge A1a.center
                          ((chartAdj (Fin.last lenAdj)).carrier)
                          A1a.carrier
                          ((chartAdj (Fin.last lenAdj)).branch)
                          A1a.branch := by
                      have hlast_in_A1 :
                          (chartAdj (Fin.last lenAdj)).center ∈
                            A1a.carrier := by
                        simpa [hAdj_terminal_center] using _hA1a_mem
                      have hedge :
                          PointedSeedEdge
                            ((chartAdj (Fin.last lenAdj)).center)
                            ((chartAdj (Fin.last lenAdj)).carrier)
                            A1a.carrier
                            ((chartAdj (Fin.last lenAdj)).branch)
                            A1a.branch :=
                        pointed_seed_edge_of_common_model
                          (chartAdj (Fin.last lenAdj)).carrier_open
                          A1a.carrier_open
                          (chartAdj (Fin.last lenAdj)).center_mem
                          hlast_in_A1 hAdj_terminal_model hA1a_raw_model
                      simpa [hAdj_terminal_center] using hedge
                    let chartAdjTerm :
                        Fin ((lenAdj + 1) + 1) →
                          PointedMetricBranchChart
                            (Fin n → Fin (d + 1) → ℂ) ℂ :=
                      Fin.snoc chartAdj A1a
                    have edgeAdjTerm :
                        ∀ j : Fin (lenAdj + 1),
                          PointedSeedEdge
                            ((chartAdjTerm (Fin.castSucc j)).center)
                            ((chartAdjTerm (Fin.castSucc j)).carrier)
                            ((chartAdjTerm (Fin.succ j)).carrier)
                            ((chartAdjTerm (Fin.castSucc j)).branch)
                            ((chartAdjTerm (Fin.succ j)).branch) := by
                      intro j
                      refine Fin.lastCases ?_ ?_ j
                      · simpa [chartAdjTerm, Fin.snoc_castSucc,
                          Fin.snoc_last, hAdj_terminal_center] using
                          hAdj_terminal_edge_to_A1
                      · intro j
                        simpa [chartAdjTerm, Fin.snoc_castSucc,
                          ← Fin.castSucc_succ] using edgeAdj j
                    have hAdjTerm_last_center :
                        (chartAdjTerm (Fin.last (lenAdj + 1))).center =
                          A1a.center := by
                      simpa [chartAdjTerm, Fin.snoc_last]
                    have hAdj_edge_eqOn :
                        ∀ j : Fin (lenAdj + 1),
                          Set.EqOn
                            (chartAdjTerm (Fin.castSucc j)).branch
                            (chartAdjTerm (Fin.succ j)).branch
                            ((chartAdjTerm (Fin.castSucc j)).carrier ∩
                              (chartAdjTerm (Fin.succ j)).carrier) := by
                      intro j
                      exact
                        PointedMetricBranchChart.eqOn_inter_of_seed
                          (chartAdjTerm (Fin.castSucc j))
                          (chartAdjTerm (Fin.succ j))
                          ⟨(edgeAdjTerm j).W,
                            (edgeAdjTerm j).W_open,
                            (edgeAdjTerm j).z0_mem,
                            (edgeAdjTerm j).W_sub,
                            (edgeAdjTerm j).eqOn⟩
                    /-
                    Genuine raw-adjacent fixed translated-boundary selector.
                    The checked data above are the retained `(4.12)` Wick
                    normalization (`hAdjWickPiece_value`) and the endpoint DCT
                    (`hAdjPieceFixed_endpoint`).  The missing proof is the
                    one-branch raw `(4.12)` flat selector through the terminal
                    outgoing sheet, not an endpoint equality obtained from
                    `extendF_eq_on_forwardTube`.
                    -/
                    -- The remaining adjacent obligation is now the endpoint
                    -- current selected by the retained raw chain.  The outer
                    -- flat selector has been reduced through the fixed
                    -- translated-test pullback and `hAdjPieceFixed_endpoint`;
                    -- no deterministic `extendF ∘ permAct` adjacent seed is
                    -- introduced here.
                    have hAdjPieceFixed_selected :
                        Tendsto AdjPieceFixed
                          (𝓝[Set.Ioi 0] (0 : ℝ))
                          (𝓝 (OS.S n (ψAdjPieceZD a))) := by
                      have hAdj_base_value :
                          (∫ u : NPointDomain d n,
                            A0a.branch
                              (BHW.permAct (d := d) P.τ
                                (fun k => wickRotatePoint (u k))) *
                            (ψAdjPieceSource a :
                              NPointDomain d n → ℂ) u) =
                          OS.S n (ψAdjPieceZD a) := by
                        calc
                          (∫ u : NPointDomain d n,
                            A0a.branch
                              (BHW.permAct (d := d) P.τ
                                (fun k => wickRotatePoint (u k))) *
                            (ψAdjPieceSource a :
                              NPointDomain d n → ℂ) u)
                              =
                            ∫ u : NPointDomain d n,
                              bvt_F OS lgc n
                                (fun k => wickRotatePoint (u k)) *
                              (ψAdjPieceSource a :
                                NPointDomain d n → ℂ) u :=
                              hAdjRawWick_to_A0
                          _ =
                            (∫ u : NPointDomain d n,
                              bvt_F OS lgc n
                                (fun k => wickRotatePoint (u (P.τ k))) *
                              (ψAdjPieceSource a :
                                NPointDomain d n → ℂ) u) :=
                              hAdjWick_eq_ordWick.symm
                          _ = OS.S n (ψAdjPieceZD a) :=
                              hAdjWickPiece_value
                      have hAdj_base_selected :
                          Tendsto
                            (fun _ε : ℝ =>
                              ∫ u : NPointDomain d n,
                                A0a.branch
                                  (BHW.permAct (d := d) P.τ
                                    (fun k => wickRotatePoint (u k))) *
                                (ψAdjPieceSource a :
                                  NPointDomain d n → ℂ) u)
                            (𝓝[Set.Ioi 0] (0 : ℝ))
                            (𝓝 (OS.S n (ψAdjPieceZD a))) := by
                          exact hAdj_base_value ▸
                            (tendsto_const_nhds :
                              Tendsto
                                (fun _ε : ℝ =>
                                  ∫ u : NPointDomain d n,
                                    A0a.branch
                                      (BHW.permAct (d := d) P.τ
                                        (fun k => wickRotatePoint (u k))) *
                                    (ψAdjPieceSource a :
                                      NPointDomain d n → ℂ) u)
                                (𝓝[Set.Ioi 0] (0 : ℝ))
                                (𝓝
                                  (∫ u : NPointDomain d n,
                                    A0a.branch
                                      (BHW.permAct (d := d) P.τ
                                        (fun k => wickRotatePoint (u k))) *
                                    (ψAdjPieceSource a :
                                      NPointDomain d n → ℂ) u)))
                      -- The fixed source-side endpoint continuity is already
                      -- checked.  The remaining retained raw `(4.12)/(4.14)`
                      -- content is the endpoint current value itself.
                      suffices hAdj_terminal_endpoint_value :
                          (∫ u : NPointDomain d n,
                            BHW.extendF (bvt_F OS lgc n)
                              (BHW.permAct (d := d) τout
                                (BHW.os45FlatCommonChartSourceSide d n
                                  (1 : Equiv.Perm (Fin n)) (-1 : ℝ)
                                  0 η0 u)) *
                            (ψAdjPieceSource a :
                              NPointDomain d n → ℂ) u) =
                          OS.S n (ψAdjPieceZD a) by
                          have hAdj_terminal_endpoint_value_qturn :
                              (∫ u : NPointDomain d n,
                                BHW.extendF (bvt_F OS lgc n)
                                  (BHW.permAct (d := d) τout
                                    (BHW.os45QuarterTurnConfig
                                      (d := d) (n := n)
                                      (fun k => wickRotatePoint (u k)))) *
                                (ψAdjPieceSource a :
                                  NPointDomain d n → ℂ) u) =
                              OS.S n (ψAdjPieceZD a) := by
                            simpa [BHW.os45FlatCommonChartSourceSide_zero]
                              using hAdj_terminal_endpoint_value
                          simpa [AdjPieceFixed,
                            BHW.os45FlatCommonChartSourceSide_zero,
                            hAdj_terminal_endpoint_value_qturn] using
                            hAdjPieceFixed_endpoint
                    exact
                      (hAdjPieceFixed_selected.const_mul J).congr'
                        hFlat_piece_eq_fixed.symm
                  have hsum_piece :
                      Tendsto
                        (fun ε : ℝ =>
                          ∑ a : αAdj, FlatAdjPiece a ε)
                        (𝓝[Set.Ioi 0] (0 : ℝ))
                        (𝓝
                          (∑ a : αAdj,
                            J * OS.S n (ψAdjPieceZD a))) := by
                    refine tendsto_finset_sum Finset.univ ?_
                    intro a _ha
                    exact hflatAdj_piece a
                  have hschwinger_sum :
                      OS.S n (∑ a : αAdj, ψAdjPieceZD a) =
                        ∑ a : αAdj, OS.S n (ψAdjPieceZD a) := by
                    change
                      (OsterwalderSchraderAxioms.schwingerCLM
                        (d := d) OS n)
                          (∑ a : αAdj, ψAdjPieceZD a) =
                        ∑ a : αAdj,
                          (OsterwalderSchraderAxioms.schwingerCLM
                            (d := d) OS n) (ψAdjPieceZD a)
                    rw [_root_.map_sum]
                  have hlimit_sum :
                      (∑ a : αAdj,
                          J * OS.S n (ψAdjPieceZD a)) =
                        J * OS.S n (D.toZeroDiagonalCLM
                          (1 : Equiv.Perm (Fin n)) φ) := by
                    calc
                      (∑ a : αAdj,
                          J * OS.S n (ψAdjPieceZD a))
                          = J * (∑ a : αAdj,
                              OS.S n (ψAdjPieceZD a)) := by
                            rw [Finset.mul_sum]
                      _ = J * OS.S n
                            (∑ a : αAdj, ψAdjPieceZD a) := by
                            rw [hschwinger_sum]
                      _ = J * OS.S n (D.toZeroDiagonalCLM
                            (1 : Equiv.Perm (Fin n)) φ) := by
                            rw [hψAdjZD_sum]
                  have hsum_global :
                      Tendsto
                        (fun ε : ℝ =>
                          ∑ a : αAdj, FlatAdjPiece a ε)
                        (𝓝[Set.Ioi 0] (0 : ℝ))
                        (𝓝
                          (J * OS.S n (D.toZeroDiagonalCLM
                            (1 : Equiv.Perm (Fin n)) φ))) := by
                    exact hlimit_sum ▸ hsum_piece
                  have hFlatAdj_sum :
                      (fun ε : ℝ =>
                        ∫ x : BHW.OS45FlatCommonChartReal d n,
                          BHW.os45FlatCommonChartBranch d n OS lgc σAdj
                            (fun j =>
                              (x j : ℂ) +
                                ((((-1 : ℝ) * ε) • η0) j : ℂ) *
                                  Complex.I) *
                          (SCV.translateSchwartz
                            (-((-1 : ℝ) * ε) • η0) ψ0Flat) x)
                        =ᶠ[𝓝[Set.Ioi 0] (0 : ℝ)]
                      (fun ε : ℝ =>
                        ∑ a : αAdj, FlatAdjPiece a ε) := by
                    filter_upwards [hAdj_piece_integrable] with ε hε
                    let t : BHW.OS45FlatCommonChartReal d n :=
                      -((-1 : ℝ) * ε) • η0
                    let Hε :
                        BHW.OS45FlatCommonChartReal d n → ℂ :=
                      fun x =>
                        BHW.os45FlatCommonChartBranch d n OS lgc σAdj
                          (fun j =>
                            (x j : ℂ) +
                              ((((-1 : ℝ) * ε) • η0) j : ℂ) *
                                Complex.I)
                    have htranslate_sum :
                        SCV.translateSchwartz t ψ0Flat =
                          ∑ a : αAdj,
                            SCV.translateSchwartz t
                              (ψAdjPieceFlat a) := by
                      calc
                        SCV.translateSchwartz t ψ0Flat =
                            (SCV.translateSchwartzCLM t) ψ0Flat := by
                              rw [SCV.translateSchwartzCLM_apply]
                        _ =
                            (SCV.translateSchwartzCLM t)
                              (∑ a : αAdj, ψAdjPieceFlat a) := by
                              rw [← hψAdjFlat_sum]
                        _ =
                            ∑ a : αAdj,
                              (SCV.translateSchwartzCLM t)
                                (ψAdjPieceFlat a) := by
                              rw [_root_.map_sum]
                        _ =
                            ∑ a : αAdj,
                              SCV.translateSchwartz t
                                (ψAdjPieceFlat a) := by
                              simp [SCV.translateSchwartzCLM_apply]
                    calc
                      (∫ x : BHW.OS45FlatCommonChartReal d n,
                          BHW.os45FlatCommonChartBranch d n OS lgc σAdj
                            (fun j =>
                              (x j : ℂ) +
                                ((((-1 : ℝ) * ε) • η0) j : ℂ) *
                                  Complex.I) *
                          (SCV.translateSchwartz
                            (-((-1 : ℝ) * ε) • η0) ψ0Flat) x)
                          =
                        ∫ x : BHW.OS45FlatCommonChartReal d n,
                          Hε x *
                            (∑ a : αAdj,
                              (SCV.translateSchwartz t
                                (ψAdjPieceFlat a)) x) := by
                            apply integral_congr_ae
                            filter_upwards with x
                            have htranslate_sum_apply :
                                (SCV.translateSchwartz
                                  (-((-1 : ℝ) * ε) • η0) ψ0Flat) x =
                                  (∑ a : αAdj,
                                    SCV.translateSchwartz t
                                      (ψAdjPieceFlat a)) x := by
                              simpa [t] using
                                congrArg
                                  (fun f :
                                    SchwartzMap
                                      (BHW.OS45FlatCommonChartReal d n)
                                      ℂ => f x)
                                  htranslate_sum
                            rw [htranslate_sum_apply]
                            simp [Hε]
                      _ =
                        ∫ x : BHW.OS45FlatCommonChartReal d n,
                          ∑ a : αAdj,
                            Hε x *
                              (SCV.translateSchwartz t
                                (ψAdjPieceFlat a)) x := by
                            apply integral_congr_ae
                            filter_upwards with x
                            simp [Finset.mul_sum]
                      _ =
                        ∑ a : αAdj, FlatAdjPiece a ε := by
                            have hint :
                                ∀ a ∈ (Finset.univ : Finset αAdj),
                                  Integrable
                                  (fun x :
                                    BHW.OS45FlatCommonChartReal d n =>
                                  Hε x *
                                    (SCV.translateSchwartz t
                                      (ψAdjPieceFlat a)) x) := by
                              intro a _ha
                              simpa [Hε, t] using hε a
                            simpa [FlatAdjPiece, Hε, t] using
                              (MeasureTheory.integral_finset_sum
                                (s := (Finset.univ : Finset αAdj))
                                (f := fun a =>
                                  fun x :
                                    BHW.OS45FlatCommonChartReal d n =>
                                  Hε x *
                                    (SCV.translateSchwartz t
                                      (ψAdjPieceFlat a)) x)
                                hint)
                  exact hsum_global.congr' hFlatAdj_sum.symm
                have hcancel :=
                  BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_fixed_of_flatTranslatedTest
                    (d := d) (n := n) OS lgc
                    σAdj (1 : Equiv.Perm (Fin n))
                    (-1 : ℝ) η0 ψ0Flat
                    (α := ℝ)
                    (l := 𝓝[Set.Ioi 0] (0 : ℝ))
                    (εseq := fun ε : ℝ => ε)
                    (L := OS.S n (D.toZeroDiagonalCLM
                      (1 : Equiv.Perm (Fin n)) φ))
                    hAdj_flat_integrable hflatAdj_selected
                simpa [AdjFixed, J, ψ0Flat, eflat, σAdj, τout,
                  SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
                  one_mul] using hcancel
            exact hAdj_fixed_selected_direct
          exact
            tendsto_nhds_unique hAdj_fixed_endpoint hAdj_fixed_selected
        refine hGminus_source.congr ?_
        filter_upwards [hFminus_eq_Gminus] with ε hε η hη
        exact (hε η hη).symm
      simpa [hTlocal_source] using hminus_source
    have hcMinus :
        cMinus = Tlocal φ :=
      SCV.eq_zeroHeight_of_common_sideLimit hKη_nonempty
        hminus_zero_uniform hplus_zero_uniform
        hminus_common hplus_zero_uniform
    simpa [cMinus] using hcMinus
  have hflat_seed :
        ∃ W : Set (Fin n → Fin (d + 1) → ℂ),
          IsOpen W ∧
          IsPreconnected W ∧
          (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.unflattenCfg n d (SCV.realEmbed (e u0))) ∈ W ∧
          W ⊆
            BHW.ExtendedTube d n ∩
              BHW.permutedExtendedTubeSector d n P.τ ∧
          Set.EqOn
            (BHW.extendF (bvt_F OS lgc n))
            (fun z =>
              BHW.extendF (bvt_F OS lgc n)
                (BHW.permAct (d := d) P.τ z))
            W := by
      exact
        BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_localZeroHeight_pairingsCLM
          (d := d) hd OS lgc (P := P)
          hE_open hE_sub ys hys_mem hys_li (e u0) hx0
          Tlocal hzero_plus hzero_minus
  rcases hflat_seed with
    ⟨Wflat, hWflat_open, hWflat_pre, hzseedW, hWflat_sub, hWflat_eq⟩
  let zseed : Fin n → Fin (d + 1) → ℂ :=
    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
      (BHW.unflattenCfg n d (SCV.realEmbed (e u0)))
  have hzseed_overlap :
      zseed ∈ H.ΩJ ∩ BHW.ExtendedTube d n ∩
        BHW.permutedExtendedTubeSector d n P.τ := by
    have hzET : zseed ∈ BHW.ExtendedTube d n := (hWflat_sub hzseedW).1
    have hzPerm : zseed ∈ BHW.permutedExtendedTubeSector d n P.τ :=
      (hWflat_sub hzseedW).2
    exact ⟨⟨H.extendedTube_subset_ΩJ hzET, hzET⟩, hzPerm⟩
  have hSPrime_seed :
      ∃ W : Set (Fin n → Fin (d + 1) → ℂ),
        IsOpen W ∧ IsPreconnected W ∧ zseed ∈ W ∧
        W ⊆ BHW.localSPrimeTwoSectorHull d n P.τ H.zbase ∩
          BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ ∧
        Set.EqOn
          (BHW.extendF (bvt_F OS lgc n))
          (fun z =>
            BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) P.τ z))
          W := by
    refine
      ⟨Wflat, hWflat_open, hWflat_pre, by simpa [zseed] using hzseedW,
        ?_, hWflat_eq⟩
    intro z hz
    have hzET : z ∈ BHW.ExtendedTube d n := (hWflat_sub hz).1
    have hzPerm : z ∈ BHW.permutedExtendedTubeSector d n P.τ :=
      (hWflat_sub hz).2
    have hzΩ : z ∈ BHW.localSPrimeTwoSectorHull d n P.τ H.zbase := by
      have hzΩJ : z ∈ H.ΩJ := H.extendedTube_subset_ΩJ hzET
      simpa [H.ΩJ_eq_localSPrimeTwoSectorHull] using hzΩJ
    exact ⟨⟨hzΩ, hzET⟩, hzPerm⟩
  let S : BHW.OS45BHWJostSPrimeBranchData hd OS lgc H :=
    BHW.os45_BHWJost_SPrimeBranchData_of_localSPrimeEOWSeedAt
      (d := d) hd OS lgc H zseed hzseed_overlap hSPrime_seed
  refine
    ⟨H.ΩJ, (fun _ => (0 : ℂ)), H.ΩJ_open, H.ΩJ_connected,
      ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    exact H.ordinaryWick_mem u (hU_sub hu)
  · intro u hu
    let zc : Fin n → Fin (d + 1) → ℂ :=
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u))
    have hzc_overlap :
        zc ∈ BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ := by
      simpa [zc] using
        BHW.os45Figure24_commonEdge_mem_initialSectorOverlap
          (d := d) (n := n) (hd := hd) (P := P)
          (subset_closure (hU_sub hu))
    exact H.extendedTube_subset_ΩJ hzc_overlap.1
  · exact differentiableOn_const (c := (0 : ℂ))
  · intro φ _hφ_compact _hφU
    simp
  · intro u hu
    let zc : Fin n → Fin (d + 1) → ℂ :=
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u))
    have hzc_overlap :
        zc ∈ BHW.ExtendedTube d n ∩
          BHW.permutedExtendedTubeSector d n P.τ := by
      simpa [zc] using
        BHW.os45Figure24_commonEdge_mem_initialSectorOverlap
          (d := d) (n := n) (hd := hd) (P := P)
          (subset_closure (hU_sub hu))
    have hzcΩ : zc ∈ H.ΩJ := H.extendedTube_subset_ΩJ hzc_overlap.1
    have hOrd :
        S.B zc =
          BHW.extendF (bvt_F OS lgc n) zc :=
      S.eq_ordinary ⟨hzc_overlap.1, hzcΩ⟩
    have hAdj :
        S.B zc =
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ zc) :=
      S.eq_adjacent ⟨hzc_overlap.2, hzcΩ⟩
    have hEq :
        BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ zc) =
          BHW.extendF (bvt_F OS lgc n) zc :=
      hAdj.symm.trans hOrd
    have hAdjPull :
        BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ zc) =
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) := by
      simpa [zc] using
        BHW.os45Figure24CommonEdge_permAct_extendF_eq_adjacentPulledRealBranch
          (d := d) (n := n) hd OS lgc (P := P) u
    have hOrdPull :
        BHW.extendF (bvt_F OS lgc n) zc =
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
            (1 : Equiv.Perm (Fin n))
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)) := by
      simp [BHW.os45PulledRealBranch, zc]
    rw [← hAdjPull, ← hOrdPull]
    exact (sub_eq_zero.mpr hEq).symm

end BHW
