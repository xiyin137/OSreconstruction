import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45Figure24Seed
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45SourceSideMoving
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValuesBase
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanRuelleOverlap

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

private theorem integral_mul_eq_sum_integral_mul_of_finite_sum
    {ι X : Type*} [Fintype ι] [MeasurableSpace X] [MeasureSpace X]
    (F w : X → ℂ) (piece : ι → X → ℂ)
    (hsum : ∀ x, w x = ∑ i, piece i x)
    (hint : ∀ i ∈ (Finset.univ : Finset ι),
      Integrable (fun x : X => F x * piece i x) (μ := volume)) :
    (∫ x : X, F x * w x) =
      ∑ i, ∫ x : X, F x * piece i x := by
  calc
    (∫ x : X, F x * w x)
        = ∫ x : X, F x * (∑ i, piece i x) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [hsum x]
    _ = ∫ x : X, ∑ i, F x * piece i x := by
          apply integral_congr_ae
          filter_upwards with x
          simp [Finset.mul_sum]
    _ = ∑ i, ∫ x : X, F x * piece i x := by
          simpa using
            (MeasureTheory.integral_finset_sum
              (μ := volume)
              (s := (Finset.univ : Finset ι))
              (f := fun i => fun x : X => F x * piece i x)
              hint)

private theorem eventually_integrable_two_pointed_sourceSide_pieces
    {d n : ℕ} [NeZero d]
    (ρperm : Equiv.Perm (Fin n)) (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (A B : PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ)
    (w : SchwartzNPoint d n)
    (hw_comp : HasCompactSupport (w : NPointDomain d n → ℂ))
    (h0 :
      ∀ u ∈ tsupport (w : NPointDomain d n → ℂ),
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u ∈
          A.carrier ∩ B.carrier) :
    ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
      Integrable
        (fun u : NPointDomain d n =>
          A.branch
            (BHW.os45FlatCommonChartSourceSide
              d n ρperm sgn ε η u) *
          (w : NPointDomain d n → ℂ) u) ∧
      Integrable
        (fun u : NPointDomain d n =>
          B.branch
            (BHW.os45FlatCommonChartSourceSide
              d n ρperm sgn ε η u) *
          (w : NPointDomain d n → ℂ) u) := by
  have hA_cont : ContinuousOn A.branch A.carrier :=
    A.holo.continuousOn
  have hB_cont : ContinuousOn B.branch B.carrier :=
    B.holo.continuousOn
  have hzero_A :
      ∀ u ∈ tsupport (w : NPointDomain d n → ℂ),
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u ∈
          A.carrier := by
    intro u hu
    exact (h0 u hu).1
  have hzero_B :
      ∀ u ∈ tsupport (w : NPointDomain d n → ℂ),
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u ∈
          B.carrier := by
    intro u hu
    exact (h0 u hu).2
  have hzero_off :
      ∀ u ∉ tsupport (w : NPointDomain d n → ℂ),
        (w : NPointDomain d n → ℂ) u = 0 := by
    intro u hu
    exact image_eq_zero_of_notMem_tsupport hu
  have hA_int :
      ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
        Integrable
          (fun u : NPointDomain d n =>
            A.branch
              (BHW.os45FlatCommonChartSourceSide
                d n ρperm sgn ε η u) *
            (w : NPointDomain d n → ℂ) u) :=
    BHW.eventually_integrable_comp_os45FlatCommonChartSourceSide_mul_of_commonCompactSupport
      (d := d) (n := n) ρperm sgn η
      A.carrier_open hA_cont hw_comp.isCompact hzero_A w hzero_off
  have hB_int :
      ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
        Integrable
          (fun u : NPointDomain d n =>
            B.branch
              (BHW.os45FlatCommonChartSourceSide
                d n ρperm sgn ε η u) *
            (w : NPointDomain d n → ℂ) u) :=
    BHW.eventually_integrable_comp_os45FlatCommonChartSourceSide_mul_of_commonCompactSupport
      (d := d) (n := n) ρperm sgn η
      B.carrier_open hB_cont hw_comp.isCompact hzero_B w hzero_off
  filter_upwards [hA_int, hB_int] with ε hAε hBε
  exact ⟨hAε, hBε⟩

private theorem exists_finite_schwartz_partitionOfUnity_on_compact_openCover
    {α E : Type*} [Fintype α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsCompact K)
    {U : α → Set E}
    (hU_open : ∀ i, IsOpen (U i))
    (hcover : K ⊆ ⋃ i, U i) :
    ∃ χ : α → SchwartzMap E ℂ,
      (∀ i, HasCompactSupport (χ i : E → ℂ)) ∧
      (∀ i, tsupport (χ i : E → ℂ) ⊆ U i) ∧
      (∀ x ∈ K, ∑ i, χ i x = 1) := by
  rcases hK.isBounded.subset_closedBall (0 : E) with ⟨R, hR⟩
  let V : α → Set E := fun i => U i ∩ Metric.ball (0 : E) (R + 1)
  have hV_open : ∀ i, IsOpen (V i) := by
    intro i
    exact (hU_open i).inter Metric.isOpen_ball
  have hV_relcompact : ∀ i, ∃ c r, V i ⊆ Metric.closedBall c r := by
    intro i
    refine ⟨(0 : E), R + 1, ?_⟩
    intro x hx
    exact Metric.ball_subset_closedBall hx.2
  have hV_cover : K ⊆ ⋃ i, V i := by
    intro x hx
    rcases Set.mem_iUnion.mp (hcover hx) with ⟨i, hxi⟩
    have hxR : dist x (0 : E) ≤ R := by
      simpa [dist_comm] using Metric.mem_closedBall.mp (hR hx)
    have hxball : x ∈ Metric.ball (0 : E) (R + 1) := by
      rw [Metric.mem_ball]
      linarith
    exact Set.mem_iUnion.mpr ⟨i, ⟨hxi, hxball⟩⟩
  obtain ⟨χ, hχ_compact, hχ_sub, hχ_sum⟩ :=
    SCV.exists_finite_schwartz_partitionOfUnity_on_compact
      (E := E) hK hV_open hV_relcompact hV_cover
  refine ⟨χ, hχ_compact, ?_, hχ_sum⟩
  intro i
  exact (hχ_sub i).trans Set.inter_subset_left

private theorem exists_finite_schwartz_smul_partition_on_tsupport
    {α E : Type*} [Fintype α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (w : SchwartzMap E ℂ)
    (hw_comp : HasCompactSupport (w : E → ℂ))
    {U : α → Set E}
    (hU_open : ∀ i, IsOpen (U i))
    (hcover : tsupport (w : E → ℂ) ⊆ ⋃ i, U i) :
    ∃ piece : α → SchwartzMap E ℂ,
      (∀ i, ∃ χ : SchwartzMap E ℂ,
        piece i = SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) w) ∧
      (∀ i, HasCompactSupport (piece i : E → ℂ)) ∧
      (∀ i, tsupport (piece i : E → ℂ) ⊆
        tsupport (w : E → ℂ)) ∧
      (∀ i, tsupport (piece i : E → ℂ) ⊆ U i) ∧
      w = ∑ i, piece i := by
  obtain ⟨χ, _hχ_compact, hχ_sub, hχ_sum⟩ :=
    exists_finite_schwartz_partitionOfUnity_on_compact_openCover
      (E := E) hw_comp.isCompact hU_open hcover
  let piece : α → SchwartzMap E ℂ := fun i =>
    SchwartzMap.smulLeftCLM ℂ (χ i : E → ℂ) w
  have hpiece_factor :
      ∀ i, ∃ χi : SchwartzMap E ℂ,
        piece i = SchwartzMap.smulLeftCLM ℂ (χi : E → ℂ) w := by
    intro i
    exact ⟨χ i, rfl⟩
  have hpiece_compact :
      ∀ i, HasCompactSupport (piece i : E → ℂ) := by
    intro i
    refine hw_comp.mono' ?_
    intro x hx
    have hx_ts : x ∈ tsupport (piece i : E → ℂ) :=
      subset_closure hx
    exact
      ((SchwartzMap.tsupport_smulLeftCLM_subset
        (F := ℂ)
        (g := (χ i : E → ℂ))
        (f := w)) hx_ts).1
  have hpiece_base :
      ∀ i, tsupport (piece i : E → ℂ) ⊆
        tsupport (w : E → ℂ) := by
    intro i x hx
    exact
      ((SchwartzMap.tsupport_smulLeftCLM_subset
        (F := ℂ)
        (g := (χ i : E → ℂ))
        (f := w)) hx).1
  have hpiece_sub :
      ∀ i, tsupport (piece i : E → ℂ) ⊆ U i := by
    intro i x hx
    exact
      hχ_sub i
        ((SchwartzMap.tsupport_smulLeftCLM_subset
          (F := ℂ)
          (g := (χ i : E → ℂ))
          (f := w)) hx).2
  have hsum :
      w = ∑ i, piece i := by
    simpa [piece] using
      SCV.schwartzMap_eq_finset_sum_smulLeftCLM_of_sum_eq_one_on_tsupport
        (Finset.univ : Finset α) χ w
        (by
          intro x hx
          simpa using hχ_sum x hx)
  exact
    ⟨piece, hpiece_factor, hpiece_compact, hpiece_base, hpiece_sub, hsum⟩

private theorem sourceSide_integral_eventually_eq_sum_chart_partition
    {d n : ℕ} [NeZero d] {α : Type*} [Fintype α]
    (ρperm : Equiv.Perm (Fin n)) (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (A : PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ)
    (B : α → PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ)
    (w : SchwartzNPoint d n)
    (hw_comp : HasCompactSupport (w : NPointDomain d n → ℂ))
    (U : α → Set (NPointDomain d n))
    (hU_open : ∀ c, IsOpen (U c))
    (hcover : tsupport (w : NPointDomain d n → ℂ) ⊆ ⋃ c, U c)
    (hzero :
      ∀ c, ∀ u ∈ U c,
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u ∈
          A.carrier ∩ (B c).carrier)
    (hEqOn :
      ∀ c, Set.EqOn A.branch (B c).branch
        (A.carrier ∩ (B c).carrier)) :
    ∃ piece : α → SchwartzNPoint d n,
      (∀ c, HasCompactSupport (piece c : NPointDomain d n → ℂ)) ∧
      (∀ c, tsupport (piece c : NPointDomain d n → ℂ) ⊆ U c) ∧
      (w = ∑ c, piece c) ∧
      ((fun ε : ℝ =>
        ∫ u : NPointDomain d n,
          A.branch
            (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u) *
          (w : NPointDomain d n → ℂ) u)
        =ᶠ[𝓝[Set.Ioi 0] (0 : ℝ)]
      fun ε : ℝ =>
        ∑ c : α,
          ∫ u : NPointDomain d n,
            (B c).branch
              (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u) *
            (piece c : NPointDomain d n → ℂ) u) := by
  obtain
      ⟨piece, _hpiece_factor, hpiece_compact, _hpiece_base,
        hpiece_sub, hpiece_sum⟩ :=
    exists_finite_schwartz_smul_partition_on_tsupport
      (w := w) hw_comp hU_open hcover
  refine ⟨piece, hpiece_compact, hpiece_sub, hpiece_sum, ?_⟩
  have hsum_fun :
      ∀ u,
        (w : NPointDomain d n → ℂ) u =
          ∑ c : α, (piece c : NPointDomain d n → ℂ) u := by
    intro u
    have happly :=
      congrArg
        (fun f : SchwartzNPoint d n =>
          (f : NPointDomain d n → ℂ) u)
        hpiece_sum
    simpa using happly
  have hint :
      ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
        ∀ c : α,
          Integrable
            (fun u : NPointDomain d n =>
              A.branch
                (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u) *
              (piece c : NPointDomain d n → ℂ) u) ∧
          Integrable
            (fun u : NPointDomain d n =>
              (B c).branch
                (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u) *
              (piece c : NPointDomain d n → ℂ) u) := by
    refine Filter.eventually_all.mpr ?_
    intro c
    have h0 :
        ∀ u ∈ tsupport (piece c : NPointDomain d n → ℂ),
          BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u ∈
            A.carrier ∩ (B c).carrier := by
      intro u hu
      exact hzero c u (hpiece_sub c hu)
    exact
      eventually_integrable_two_pointed_sourceSide_pieces
        (d := d) (n := n) ρperm sgn η A (B c)
        (piece c) (hpiece_compact c) h0
  have hsplit :
      (fun ε : ℝ =>
        ∫ u : NPointDomain d n,
          A.branch
            (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u) *
          (w : NPointDomain d n → ℂ) u)
        =ᶠ[𝓝[Set.Ioi 0] (0 : ℝ)]
      fun ε : ℝ =>
        ∑ c : α,
          ∫ u : NPointDomain d n,
            A.branch
              (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u) *
            (piece c : NPointDomain d n → ℂ) u := by
    filter_upwards [hint] with ε hε
    exact
      integral_mul_eq_sum_integral_mul_of_finite_sum
        (X := NPointDomain d n)
        (F := fun u : NPointDomain d n =>
          A.branch
            (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u))
        (w := fun u : NPointDomain d n =>
          (w : NPointDomain d n → ℂ) u)
        (piece := fun c u => (piece c : NPointDomain d n → ℂ) u)
        hsum_fun
        (by
          intro c _hc
          exact (hε c).1)
  have hto_chart :
      (fun ε : ℝ =>
        ∑ c : α,
          ∫ u : NPointDomain d n,
            A.branch
              (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u) *
            (piece c : NPointDomain d n → ℂ) u)
        =ᶠ[𝓝[Set.Ioi 0] (0 : ℝ)]
      fun ε : ℝ =>
        ∑ c : α,
          ∫ u : NPointDomain d n,
            (B c).branch
              (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u) *
            (piece c : NPointDomain d n → ℂ) u := by
    have hpieces :
        ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
          ∀ c : α,
            (∫ u : NPointDomain d n,
              A.branch
                (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u) *
              (piece c : NPointDomain d n → ℂ) u) =
            ∫ u : NPointDomain d n,
              (B c).branch
                (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u) *
              (piece c : NPointDomain d n → ℂ) u := by
      refine Filter.eventually_all.mpr ?_
      intro c
      have hmem :
          ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
            ∀ u,
              u ∈ Function.support
                  (piece c : NPointDomain d n → ℂ) →
                BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u ∈
                  A.carrier ∩ (B c).carrier := by
        have hmem_tsupport :
            ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
              ∀ u ∈ tsupport (piece c : NPointDomain d n → ℂ),
                BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u ∈
                  A.carrier ∩ (B c).carrier :=
          BHW.eventually_forall_os45FlatCommonChartSourceSide_mem_of_compact
            (d := d) (n := n) ρperm sgn η
            (hpiece_compact c).isCompact
            (A.carrier_open.inter (B c).carrier_open)
            (by
              intro u hu
              exact hzero c u (hpiece_sub c hu))
        filter_upwards [hmem_tsupport] with ε hε u hu
        exact hε u (subset_tsupport _ hu)
      filter_upwards [hmem] with ε hε
      apply integral_congr_ae
      refine Filter.Eventually.of_forall ?_
      intro u
      by_cases hu :
          u ∈ Function.support (piece c : NPointDomain d n → ℂ)
      · have hbranch := hEqOn c (hε u hu)
        change
          A.branch
              (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u) *
            (piece c : NPointDomain d n → ℂ) u =
          (B c).branch
              (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u) *
            (piece c : NPointDomain d n → ℂ) u
        rw [hbranch]
      · have hzero_piece :
            (piece c : NPointDomain d n → ℂ) u = 0 := by
          by_contra hne
          exact hu (by simpa [Function.mem_support] using hne)
        simp [hzero_piece]
    filter_upwards [hpieces] with ε hε
    exact Finset.sum_congr rfl
      (by
        intro c _hc
        exact hε c)
  exact hsplit.trans hto_chart

private theorem integrable_pointed_fixedApproach_mul_of_compactSupport
    {d n : ℕ} [NeZero d]
    (A : PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ)
    (approach : NPointDomain d n → Fin n → Fin (d + 1) → ℂ)
    (happroach_cont : Continuous approach)
    (w : SchwartzNPoint d n)
    (hw_comp : HasCompactSupport (w : NPointDomain d n → ℂ))
    (hmem :
      ∀ u ∈ tsupport (w : NPointDomain d n → ℂ),
        approach u ∈ A.carrier) :
    Integrable
      (fun u : NPointDomain d n =>
        A.branch (approach u) *
        (w : NPointDomain d n → ℂ) u) := by
  let U : Set (NPointDomain d n) := approach ⁻¹' A.carrier
  have hU_open : IsOpen U := by
    simpa [U] using A.carrier_open.preimage happroach_cont
  have hH_cont :
      ContinuousOn (fun u : NPointDomain d n =>
        A.branch (approach u)) U := by
    exact A.holo.continuousOn.comp happroach_cont.continuousOn
      (by intro u hu; simpa [U] using hu)
  have hw_sub : tsupport (w : NPointDomain d n → ℂ) ⊆ U := by
    intro u hu
    simpa [U] using hmem u hu
  have hprod_cont :
      Continuous
        (fun u : NPointDomain d n =>
          (w : NPointDomain d n → ℂ) u *
            A.branch (approach u)) :=
    SCV.continuous_mul_of_continuousOn_of_tsupport_subset_open
      hU_open w.continuous hw_sub hH_cont
  have hprod_cont' :
      Continuous
        (fun u : NPointDomain d n =>
          A.branch (approach u) *
            (w : NPointDomain d n → ℂ) u) := by
    simpa [mul_comm] using hprod_cont
  have hprod_comp :
      HasCompactSupport
        (fun u : NPointDomain d n =>
          A.branch (approach u) *
            (w : NPointDomain d n → ℂ) u) := by
    refine hw_comp.mono' ?_
    intro u hu
    by_contra huw
    have hw_zero :
        (w : NPointDomain d n → ℂ) u = 0 :=
      image_eq_zero_of_notMem_tsupport huw
    exact hu (by simp [hw_zero])
  exact hprod_cont'.integrable_of_hasCompactSupport hprod_comp

private theorem fixedApproach_integral_eq_sum_chart_partition
    {d n : ℕ} [NeZero d] {α : Type*} [Fintype α]
    (A : PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ)
    (B : α → PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ)
    (approach : NPointDomain d n → Fin n → Fin (d + 1) → ℂ)
    (happroach_cont : Continuous approach)
    (w : SchwartzNPoint d n)
    (hw_comp : HasCompactSupport (w : NPointDomain d n → ℂ))
    (U : α → Set (NPointDomain d n))
    (hU_open : ∀ c, IsOpen (U c))
    (hcover : tsupport (w : NPointDomain d n → ℂ) ⊆ ⋃ c, U c)
    (hzero :
      ∀ c, ∀ u ∈ U c,
        approach u ∈ A.carrier ∩ (B c).carrier)
    (hEqOn :
      ∀ c, Set.EqOn A.branch (B c).branch
        (A.carrier ∩ (B c).carrier)) :
    ∃ piece : α → SchwartzNPoint d n,
      (∀ c, HasCompactSupport (piece c : NPointDomain d n → ℂ)) ∧
      (∀ c, tsupport (piece c : NPointDomain d n → ℂ) ⊆ U c) ∧
      (w = ∑ c, piece c) ∧
      ((∫ u : NPointDomain d n,
        A.branch (approach u) *
        (w : NPointDomain d n → ℂ) u) =
      ∑ c : α,
        ∫ u : NPointDomain d n,
          (B c).branch (approach u) *
          (piece c : NPointDomain d n → ℂ) u) := by
  obtain
      ⟨piece, _hpiece_factor, hpiece_compact, _hpiece_base,
        hpiece_sub, hpiece_sum⟩ :=
    exists_finite_schwartz_smul_partition_on_tsupport
      (w := w) hw_comp hU_open hcover
  refine ⟨piece, hpiece_compact, hpiece_sub, hpiece_sum, ?_⟩
  have hsum_fun :
      ∀ u,
        (w : NPointDomain d n → ℂ) u =
          ∑ c : α, (piece c : NPointDomain d n → ℂ) u := by
    intro u
    have happly :=
      congrArg
        (fun f : SchwartzNPoint d n =>
          (f : NPointDomain d n → ℂ) u)
        hpiece_sum
    simpa using happly
  have hsplit :
      (∫ u : NPointDomain d n,
        A.branch (approach u) *
        (w : NPointDomain d n → ℂ) u) =
      ∑ c : α,
        ∫ u : NPointDomain d n,
          A.branch (approach u) *
          (piece c : NPointDomain d n → ℂ) u := by
    exact
      integral_mul_eq_sum_integral_mul_of_finite_sum
        (X := NPointDomain d n)
        (F := fun u : NPointDomain d n =>
          A.branch (approach u))
        (w := fun u : NPointDomain d n =>
          (w : NPointDomain d n → ℂ) u)
        (piece := fun c u => (piece c : NPointDomain d n → ℂ) u)
        hsum_fun
        (by
          intro c _hc
          exact
            integrable_pointed_fixedApproach_mul_of_compactSupport
              (d := d) (n := n) A approach happroach_cont
              (piece c) (hpiece_compact c)
              (by
                intro u hu
                exact (hzero c u (hpiece_sub c hu)).1))
  have hto_chart :
      (∑ c : α,
        ∫ u : NPointDomain d n,
          A.branch (approach u) *
          (piece c : NPointDomain d n → ℂ) u) =
      ∑ c : α,
        ∫ u : NPointDomain d n,
          (B c).branch (approach u) *
          (piece c : NPointDomain d n → ℂ) u := by
    apply Finset.sum_congr rfl
    intro c _hc
    apply integral_congr_ae
    refine Filter.Eventually.of_forall ?_
    intro u
    by_cases hu :
        u ∈ Function.support (piece c : NPointDomain d n → ℂ)
    · have hmem :
          approach u ∈ A.carrier ∩ (B c).carrier :=
        hzero c u (hpiece_sub c (subset_tsupport _ hu))
      have hbranch := hEqOn c hmem
      change
        A.branch (approach u) *
          (piece c : NPointDomain d n → ℂ) u =
        (B c).branch (approach u) *
          (piece c : NPointDomain d n → ℂ) u
      rw [hbranch]
    · have hzero_piece :
          (piece c : NPointDomain d n → ℂ) u = 0 := by
        by_contra hne
        exact hu (by simpa [Function.mem_support] using hne)
      simp [hzero_piece]
  exact hsplit.trans hto_chart

private theorem fixed_sourceSide_integral_common_chart_partition
    {d n : ℕ} [NeZero d] {α : Type*} [Fintype α]
    (ρperm : Equiv.Perm (Fin n)) (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (Astatic Amoving :
      PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ)
    (Bstatic Bmoving :
      α → PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ)
    (staticApproach : NPointDomain d n → Fin n → Fin (d + 1) → ℂ)
    (hstatic_cont : Continuous staticApproach)
    (w : SchwartzNPoint d n)
    (hw_comp : HasCompactSupport (w : NPointDomain d n → ℂ))
    (hw_vanish : VanishesToInfiniteOrderOnCoincidence w)
    (U : α → Set (NPointDomain d n))
    (hU_open : ∀ c, IsOpen (U c))
    (hcover : tsupport (w : NPointDomain d n → ℂ) ⊆ ⋃ c, U c)
    (hstatic_zero :
      ∀ c, ∀ u ∈ U c,
        staticApproach u ∈ Astatic.carrier ∩ (Bstatic c).carrier)
    (hmoving_zero :
      ∀ c, ∀ u ∈ U c,
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u ∈
          Amoving.carrier ∩ (Bmoving c).carrier)
    (hstatic_eqOn :
      ∀ c, Set.EqOn Astatic.branch (Bstatic c).branch
        (Astatic.carrier ∩ (Bstatic c).carrier))
    (hmoving_eqOn :
      ∀ c, Set.EqOn Amoving.branch (Bmoving c).branch
        (Amoving.carrier ∩ (Bmoving c).carrier)) :
    ∃ piece : α → SchwartzNPoint d n,
      (∀ c, HasCompactSupport (piece c : NPointDomain d n → ℂ)) ∧
      (∀ c, VanishesToInfiniteOrderOnCoincidence (piece c)) ∧
      (∀ c, tsupport (piece c : NPointDomain d n → ℂ) ⊆
        tsupport (w : NPointDomain d n → ℂ)) ∧
      (∀ c, tsupport (piece c : NPointDomain d n → ℂ) ⊆ U c) ∧
      (w = ∑ c, piece c) ∧
      ((∫ u : NPointDomain d n,
        Astatic.branch (staticApproach u) *
        (w : NPointDomain d n → ℂ) u) =
      ∑ c : α,
        ∫ u : NPointDomain d n,
          (Bstatic c).branch (staticApproach u) *
          (piece c : NPointDomain d n → ℂ) u) ∧
      ((fun ε : ℝ =>
        ∫ u : NPointDomain d n,
          Amoving.branch
            (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u) *
          (w : NPointDomain d n → ℂ) u)
        =ᶠ[𝓝[Set.Ioi 0] (0 : ℝ)]
      fun ε : ℝ =>
        ∑ c : α,
          ∫ u : NPointDomain d n,
            (Bmoving c).branch
              (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u) *
            (piece c : NPointDomain d n → ℂ) u) := by
  obtain
      ⟨piece, hpiece_factor, hpiece_compact, hpiece_base, hpiece_sub,
        hpiece_sum⟩ :=
    exists_finite_schwartz_smul_partition_on_tsupport
      (w := w) hw_comp hU_open hcover
  have hpiece_vanish :
      ∀ c, VanishesToInfiniteOrderOnCoincidence (piece c) := by
    intro c
    rcases hpiece_factor c with ⟨χ, hχ⟩
    have h :=
      VanishesToInfiniteOrderOnCoincidence.smulLeft_schwartzNPoint
        (ψ := χ) (f := w) hw_vanish
    simpa [hχ] using h
  refine
    ⟨piece, hpiece_compact, hpiece_vanish, hpiece_base, hpiece_sub,
      hpiece_sum, ?_, ?_⟩
  have hsum_fun :
      ∀ u,
        (w : NPointDomain d n → ℂ) u =
          ∑ c : α, (piece c : NPointDomain d n → ℂ) u := by
    intro u
    have happly :=
      congrArg
        (fun f : SchwartzNPoint d n =>
          (f : NPointDomain d n → ℂ) u)
        hpiece_sum
    simpa using happly
  · have hsplit :
        (∫ u : NPointDomain d n,
          Astatic.branch (staticApproach u) *
          (w : NPointDomain d n → ℂ) u) =
        ∑ c : α,
          ∫ u : NPointDomain d n,
            Astatic.branch (staticApproach u) *
            (piece c : NPointDomain d n → ℂ) u := by
      exact
        integral_mul_eq_sum_integral_mul_of_finite_sum
          (X := NPointDomain d n)
          (F := fun u : NPointDomain d n =>
            Astatic.branch (staticApproach u))
          (w := fun u : NPointDomain d n =>
            (w : NPointDomain d n → ℂ) u)
          (piece := fun c u => (piece c : NPointDomain d n → ℂ) u)
          hsum_fun
          (by
            intro c _hc
            exact
              integrable_pointed_fixedApproach_mul_of_compactSupport
                (d := d) (n := n) Astatic staticApproach
                hstatic_cont (piece c) (hpiece_compact c)
                (by
                  intro u hu
                  exact (hstatic_zero c u (hpiece_sub c hu)).1))
    have hto_chart :
        (∑ c : α,
          ∫ u : NPointDomain d n,
            Astatic.branch (staticApproach u) *
            (piece c : NPointDomain d n → ℂ) u) =
        ∑ c : α,
          ∫ u : NPointDomain d n,
            (Bstatic c).branch (staticApproach u) *
            (piece c : NPointDomain d n → ℂ) u := by
      apply Finset.sum_congr rfl
      intro c _hc
      apply integral_congr_ae
      refine Filter.Eventually.of_forall ?_
      intro u
      by_cases hu :
          u ∈ Function.support (piece c : NPointDomain d n → ℂ)
      · have hmem :
            staticApproach u ∈ Astatic.carrier ∩ (Bstatic c).carrier :=
          hstatic_zero c u (hpiece_sub c (subset_tsupport _ hu))
        have hbranch := hstatic_eqOn c hmem
        change
          Astatic.branch (staticApproach u) *
            (piece c : NPointDomain d n → ℂ) u =
          (Bstatic c).branch (staticApproach u) *
            (piece c : NPointDomain d n → ℂ) u
        rw [hbranch]
      · have hzero_piece :
            (piece c : NPointDomain d n → ℂ) u = 0 := by
          by_contra hne
          exact hu (by simpa [Function.mem_support] using hne)
        simp [hzero_piece]
    exact hsplit.trans hto_chart
  · have hsum_fun :
        ∀ u,
          (w : NPointDomain d n → ℂ) u =
            ∑ c : α, (piece c : NPointDomain d n → ℂ) u := by
      intro u
      have happly :=
        congrArg
          (fun f : SchwartzNPoint d n =>
            (f : NPointDomain d n → ℂ) u)
          hpiece_sum
      simpa using happly
    have hint :
        ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
          ∀ c : α,
            Integrable
              (fun u : NPointDomain d n =>
                Amoving.branch
                  (BHW.os45FlatCommonChartSourceSide
                    d n ρperm sgn ε η u) *
                (piece c : NPointDomain d n → ℂ) u) ∧
            Integrable
              (fun u : NPointDomain d n =>
                (Bmoving c).branch
                  (BHW.os45FlatCommonChartSourceSide
                    d n ρperm sgn ε η u) *
                (piece c : NPointDomain d n → ℂ) u) := by
      refine Filter.eventually_all.mpr ?_
      intro c
      have h0 :
          ∀ u ∈ tsupport (piece c : NPointDomain d n → ℂ),
            BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u ∈
              Amoving.carrier ∩ (Bmoving c).carrier := by
        intro u hu
        exact hmoving_zero c u (hpiece_sub c hu)
      exact
        eventually_integrable_two_pointed_sourceSide_pieces
          (d := d) (n := n) ρperm sgn η Amoving (Bmoving c)
          (piece c) (hpiece_compact c) h0
    have hsplit :
        (fun ε : ℝ =>
          ∫ u : NPointDomain d n,
            Amoving.branch
              (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u) *
            (w : NPointDomain d n → ℂ) u)
          =ᶠ[𝓝[Set.Ioi 0] (0 : ℝ)]
        fun ε : ℝ =>
          ∑ c : α,
            ∫ u : NPointDomain d n,
              Amoving.branch
                (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u) *
              (piece c : NPointDomain d n → ℂ) u := by
      filter_upwards [hint] with ε hε
      exact
        integral_mul_eq_sum_integral_mul_of_finite_sum
          (X := NPointDomain d n)
          (F := fun u : NPointDomain d n =>
            Amoving.branch
              (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u))
          (w := fun u : NPointDomain d n =>
            (w : NPointDomain d n → ℂ) u)
          (piece := fun c u => (piece c : NPointDomain d n → ℂ) u)
          hsum_fun
          (by
            intro c _hc
            exact (hε c).1)
    have hto_chart :
        (fun ε : ℝ =>
          ∑ c : α,
            ∫ u : NPointDomain d n,
              Amoving.branch
                (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u) *
              (piece c : NPointDomain d n → ℂ) u)
          =ᶠ[𝓝[Set.Ioi 0] (0 : ℝ)]
        fun ε : ℝ =>
          ∑ c : α,
            ∫ u : NPointDomain d n,
              (Bmoving c).branch
                (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u) *
              (piece c : NPointDomain d n → ℂ) u := by
      have hpieces :
          ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
            ∀ c : α,
              (∫ u : NPointDomain d n,
                Amoving.branch
                  (BHW.os45FlatCommonChartSourceSide
                    d n ρperm sgn ε η u) *
                (piece c : NPointDomain d n → ℂ) u) =
              ∫ u : NPointDomain d n,
                (Bmoving c).branch
                  (BHW.os45FlatCommonChartSourceSide
                    d n ρperm sgn ε η u) *
                (piece c : NPointDomain d n → ℂ) u := by
        refine Filter.eventually_all.mpr ?_
        intro c
        have hmem :
            ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
              ∀ u,
                u ∈ Function.support
                    (piece c : NPointDomain d n → ℂ) →
                  BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u ∈
                    Amoving.carrier ∩ (Bmoving c).carrier := by
          have hmem_tsupport :
              ∀ᶠ ε in 𝓝[Set.Ioi 0] (0 : ℝ),
                ∀ u ∈ tsupport (piece c : NPointDomain d n → ℂ),
                  BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u ∈
                    Amoving.carrier ∩ (Bmoving c).carrier :=
            BHW.eventually_forall_os45FlatCommonChartSourceSide_mem_of_compact
              (d := d) (n := n) ρperm sgn η
              (hpiece_compact c).isCompact
              (Amoving.carrier_open.inter (Bmoving c).carrier_open)
              (by
                intro u hu
                exact hmoving_zero c u (hpiece_sub c hu))
          filter_upwards [hmem_tsupport] with ε hε u hu
          exact hε u (subset_tsupport _ hu)
        filter_upwards [hmem] with ε hε
        apply integral_congr_ae
        refine Filter.Eventually.of_forall ?_
        intro u
        by_cases hu :
            u ∈ Function.support (piece c : NPointDomain d n → ℂ)
        · have hbranch := hmoving_eqOn c (hε u hu)
          change
            Amoving.branch
                (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u) *
              (piece c : NPointDomain d n → ℂ) u =
            (Bmoving c).branch
                (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u) *
              (piece c : NPointDomain d n → ℂ) u
          rw [hbranch]
        · have hzero_piece :
              (piece c : NPointDomain d n → ℂ) u = 0 := by
            by_contra hne
            exact hu (by simpa [Function.mem_support] using hne)
          simp [hzero_piece]
      filter_upwards [hpieces] with ε hε
      exact Finset.sum_congr rfl
        (by
          intro c _hc
          exact hε c)
    exact hsplit.trans hto_chart

private theorem fixed_sourceSide_integral_refined_chart_partition
    {d n : ℕ} [NeZero d]
    {α β : Type*} [Fintype α] [Fintype β]
    (ρperm : Equiv.Perm (Fin n)) (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (Astatic Amoving :
      PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ)
    (Bstatic : α →
      PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ)
    (Bmoving : β →
      PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ)
    (staticApproach : NPointDomain d n → Fin n → Fin (d + 1) → ℂ)
    (hstatic_cont : Continuous staticApproach)
    (w : SchwartzNPoint d n)
    (hw_comp : HasCompactSupport (w : NPointDomain d n → ℂ))
    (hw_vanish : VanishesToInfiniteOrderOnCoincidence w)
    (Ustatic : α → Set (NPointDomain d n))
    (Umoving : β → Set (NPointDomain d n))
    (hUstatic_open : ∀ c, IsOpen (Ustatic c))
    (hUmoving_open : ∀ c, IsOpen (Umoving c))
    (hstatic_cover :
      tsupport (w : NPointDomain d n → ℂ) ⊆ ⋃ c, Ustatic c)
    (hmoving_cover :
      tsupport (w : NPointDomain d n → ℂ) ⊆ ⋃ c, Umoving c)
    (hstatic_zero :
      ∀ c, ∀ u ∈ Ustatic c,
        staticApproach u ∈ Astatic.carrier ∩ (Bstatic c).carrier)
    (hmoving_zero :
      ∀ c, ∀ u ∈ Umoving c,
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u ∈
          Amoving.carrier ∩ (Bmoving c).carrier)
    (hstatic_eqOn :
      ∀ c, Set.EqOn Astatic.branch (Bstatic c).branch
        (Astatic.carrier ∩ (Bstatic c).carrier))
    (hmoving_eqOn :
      ∀ c, Set.EqOn Amoving.branch (Bmoving c).branch
        (Amoving.carrier ∩ (Bmoving c).carrier)) :
    ∃ piece : α × β → SchwartzNPoint d n,
      (∀ c, HasCompactSupport (piece c : NPointDomain d n → ℂ)) ∧
      (∀ c, VanishesToInfiniteOrderOnCoincidence (piece c)) ∧
      (∀ c, tsupport (piece c : NPointDomain d n → ℂ) ⊆
        tsupport (w : NPointDomain d n → ℂ)) ∧
      (∀ c,
        tsupport (piece c : NPointDomain d n → ℂ) ⊆
          Ustatic c.1 ∩ Umoving c.2) ∧
      (w = ∑ c, piece c) ∧
      ((∫ u : NPointDomain d n,
        Astatic.branch (staticApproach u) *
        (w : NPointDomain d n → ℂ) u) =
      ∑ c : α × β,
        ∫ u : NPointDomain d n,
          (Bstatic c.1).branch (staticApproach u) *
          (piece c : NPointDomain d n → ℂ) u) ∧
      ((fun ε : ℝ =>
        ∫ u : NPointDomain d n,
          Amoving.branch
            (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u) *
          (w : NPointDomain d n → ℂ) u)
        =ᶠ[𝓝[Set.Ioi 0] (0 : ℝ)]
      fun ε : ℝ =>
        ∑ c : α × β,
          ∫ u : NPointDomain d n,
            (Bmoving c.2).branch
              (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u) *
            (piece c : NPointDomain d n → ℂ) u) := by
  let U : α × β → Set (NPointDomain d n) := fun c =>
    Ustatic c.1 ∩ Umoving c.2
  have hU_open : ∀ c : α × β, IsOpen (U c) := by
    intro c
    exact (hUstatic_open c.1).inter (hUmoving_open c.2)
  have hcover :
      tsupport (w : NPointDomain d n → ℂ) ⊆ ⋃ c : α × β, U c := by
    intro u hu
    rcases Set.mem_iUnion.mp (hstatic_cover hu) with ⟨cs, hcs⟩
    rcases Set.mem_iUnion.mp (hmoving_cover hu) with ⟨cm, hcm⟩
    exact Set.mem_iUnion.mpr ⟨(cs, cm), ⟨hcs, hcm⟩⟩
  obtain
      ⟨piece, hpiece_compact, hpiece_vanish, hpiece_base, hpiece_sub,
        hpiece_sum, hstatic, hmoving⟩ :=
    fixed_sourceSide_integral_common_chart_partition
      (d := d) (n := n) ρperm sgn η Astatic Amoving
      (fun c : α × β => Bstatic c.1)
      (fun c : α × β => Bmoving c.2)
      staticApproach hstatic_cont w hw_comp hw_vanish U hU_open hcover
      (by
        intro c u hu
        exact hstatic_zero c.1 u hu.1)
      (by
        intro c u hu
        exact hmoving_zero c.2 u hu.2)
      (by
        intro c
        exact hstatic_eqOn c.1)
      (by
        intro c
        exact hmoving_eqOn c.2)
  exact
    ⟨piece, hpiece_compact, hpiece_vanish, hpiece_base, hpiece_sub,
      hpiece_sum, hstatic, hmoving⟩

private theorem fixed_sourceSide_integral_refined_chart_partition_tendsto_of_local
    {d n : ℕ} [NeZero d]
    {α β : Type*} [Fintype α] [Fintype β]
    (ρperm : Equiv.Perm (Fin n)) (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (Astatic Amoving :
      PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ)
    (Bstatic : α →
      PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ)
    (Bmoving : β →
      PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ)
    (staticApproach : NPointDomain d n → Fin n → Fin (d + 1) → ℂ)
    (hstatic_cont : Continuous staticApproach)
    (w : SchwartzNPoint d n)
    (hw_comp : HasCompactSupport (w : NPointDomain d n → ℂ))
    (hw_vanish : VanishesToInfiniteOrderOnCoincidence w)
    (Ustatic : α → Set (NPointDomain d n))
    (Umoving : β → Set (NPointDomain d n))
    (hUstatic_open : ∀ c, IsOpen (Ustatic c))
    (hUmoving_open : ∀ c, IsOpen (Umoving c))
    (hstatic_cover :
      tsupport (w : NPointDomain d n → ℂ) ⊆ ⋃ c, Ustatic c)
    (hmoving_cover :
      tsupport (w : NPointDomain d n → ℂ) ⊆ ⋃ c, Umoving c)
    (hstatic_zero :
      ∀ c, ∀ u ∈ Ustatic c,
        staticApproach u ∈ Astatic.carrier ∩ (Bstatic c).carrier)
    (hmoving_zero :
      ∀ c, ∀ u ∈ Umoving c,
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u ∈
          Amoving.carrier ∩ (Bmoving c).carrier)
    (hstatic_eqOn :
      ∀ c, Set.EqOn Astatic.branch (Bstatic c).branch
        (Astatic.carrier ∩ (Bstatic c).carrier))
    (hmoving_eqOn :
      ∀ c, Set.EqOn Amoving.branch (Bmoving c).branch
        (Amoving.carrier ∩ (Bmoving c).carrier))
    (hlocal :
      ∀ (cs : α) (cm : β) (piece : SchwartzNPoint d n),
        HasCompactSupport (piece : NPointDomain d n → ℂ) →
        VanishesToInfiniteOrderOnCoincidence piece →
        tsupport (piece : NPointDomain d n → ℂ) ⊆
          tsupport (w : NPointDomain d n → ℂ) →
        tsupport (piece : NPointDomain d n → ℂ) ⊆
          Ustatic cs ∩ Umoving cm →
        Tendsto
          (fun ε : ℝ =>
            ∫ u : NPointDomain d n,
              (Bmoving cm).branch
                (BHW.os45FlatCommonChartSourceSide
                  d n ρperm sgn ε η u) *
              (piece : NPointDomain d n → ℂ) u)
          (𝓝[Set.Ioi 0] (0 : ℝ))
          (𝓝
            (∫ u : NPointDomain d n,
              (Bstatic cs).branch (staticApproach u) *
              (piece : NPointDomain d n → ℂ) u))) :
    Tendsto
      (fun ε : ℝ =>
        ∫ u : NPointDomain d n,
          Amoving.branch
            (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u) *
          (w : NPointDomain d n → ℂ) u)
      (𝓝[Set.Ioi 0] (0 : ℝ))
      (𝓝
        (∫ u : NPointDomain d n,
          Astatic.branch (staticApproach u) *
          (w : NPointDomain d n → ℂ) u)) := by
  obtain
      ⟨piece, hpiece_compact, hpiece_vanish, hpiece_base, hpiece_sub,
        _hpiece_sum, hstatic, hmoving⟩ :=
    fixed_sourceSide_integral_refined_chart_partition
      (d := d) (n := n) ρperm sgn η Astatic Amoving
      Bstatic Bmoving staticApproach hstatic_cont w hw_comp
      hw_vanish
      Ustatic Umoving hUstatic_open hUmoving_open
      hstatic_cover hmoving_cover hstatic_zero hmoving_zero
      hstatic_eqOn hmoving_eqOn
  have hsum :
      Tendsto
        (fun ε : ℝ =>
          ∑ c : α × β,
            ∫ u : NPointDomain d n,
              (Bmoving c.2).branch
                (BHW.os45FlatCommonChartSourceSide
                  d n ρperm sgn ε η u) *
              (piece c : NPointDomain d n → ℂ) u)
        (𝓝[Set.Ioi 0] (0 : ℝ))
        (𝓝
          (∑ c : α × β,
            ∫ u : NPointDomain d n,
              (Bstatic c.1).branch (staticApproach u) *
              (piece c : NPointDomain d n → ℂ) u)) := by
    refine tendsto_finset_sum Finset.univ ?_
    intro c _hc
    exact
      hlocal c.1 c.2 (piece c) (hpiece_compact c)
        (hpiece_vanish c) (hpiece_base c) (hpiece_sub c)
  have htarget :
      (∑ c : α × β,
        ∫ u : NPointDomain d n,
          (Bstatic c.1).branch (staticApproach u) *
          (piece c : NPointDomain d n → ℂ) u) =
      ∫ u : NPointDomain d n,
        Astatic.branch (staticApproach u) *
        (w : NPointDomain d n → ℂ) u :=
    hstatic.symm
  exact (htarget ▸ hsum).congr' hmoving.symm

private theorem commonEdge_pulledRealBranch_sub_eq_zero_of_extendF_perm_eq
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (u : NPointDomain d n)
    (hEq :
      BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) P.τ
            ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u)))) =
        BHW.extendF (bvt_F OS lgc n)
          ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u)))) :
    (0 : ℂ) =
      BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) -
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (1 : Equiv.Perm (Fin n))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) := by
  let p0 : Fin n → Fin (d + 1) → ℂ :=
    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
      (BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) u))
  have hAdj :
      BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) P.τ p0) =
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (P.τ.symm * (1 : Equiv.Perm (Fin n)))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) := by
    simpa [p0] using
      BHW.os45Figure24CommonEdge_permAct_extendF_eq_adjacentPulledRealBranch
        (d := d) (n := n) hd OS lgc (P := P) u
  have hOrd :
      BHW.extendF (bvt_F OS lgc n) p0 =
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (1 : Equiv.Perm (Fin n))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) := by
    simp [BHW.os45PulledRealBranch, p0]
  rw [← hAdj, ← hOrd]
  exact (sub_eq_zero.mpr (by simpa [p0] using hEq)).symm

private theorem eventually_forall_os45FlatCommonChartSourceSide_mem_finset_cover
    {d n : ℕ} [NeZero d] {ι : Type*}
    (ρperm : Equiv.Perm (Fin n)) (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (s : Finset ι)
    (U : ι → Set (Fin n → Fin (d + 1) → ℂ))
    (hU_open : ∀ i ∈ s, IsOpen (U i))
    {φ : NPointDomain d n → ℂ}
    (hφ_compact : HasCompactSupport φ)
    (h0 :
      ∀ u ∈ tsupport φ,
        ∃ i : ι,
          i ∈ s ∧
            BHW.os45FlatCommonChartSourceSide
              d n ρperm sgn 0 η u ∈ U i) :
    ∀ᶠ eps in 𝓝[Set.Ioi 0] (0 : ℝ),
      ∀ u,
        u ∈ Function.support φ →
          ∃ i : ι,
            i ∈ s ∧
              BHW.os45FlatCommonChartSourceSide
                d n ρperm sgn eps η u ∈ U i := by
  classical
  let V : Set (Fin n → Fin (d + 1) → ℂ) :=
    {z | ∃ i : ι, i ∈ s ∧ z ∈ U i}
  have hV_open : IsOpen V := by
    have hset : V = ⋃ i ∈ s, U i := by
      ext z
      simp [V]
    rw [hset]
    exact isOpen_biUnion hU_open
  have h0V :
      ∀ u ∈ tsupport φ,
        BHW.os45FlatCommonChartSourceSide
          d n ρperm sgn 0 η u ∈ V := by
    intro u hu
    simpa [V] using h0 u hu
  have hcover :
      ∀ᶠ eps in 𝓝[Set.Ioi 0] (0 : ℝ),
        ∀ u ∈ tsupport φ,
          BHW.os45FlatCommonChartSourceSide
            d n ρperm sgn eps η u ∈ V :=
    BHW.eventually_forall_os45FlatCommonChartSourceSide_mem_of_compact
      (d := d) (n := n) ρperm sgn η
      hφ_compact.isCompact hV_open h0V
  filter_upwards [hcover] with eps heps u hu
  have huK : u ∈ tsupport φ := subset_tsupport _ hu
  simpa [V] using heps u huK

private theorem eventually_forall_os45FlatCommonChartSourceSide_mem_finset_cover_inter
    {d n : ℕ} [NeZero d] {ι : Type*}
    (ρperm : Equiv.Perm (Fin n)) (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (s : Finset ι)
    (U : ι → Set (Fin n → Fin (d + 1) → ℂ))
    (C : Set (Fin n → Fin (d + 1) → ℂ))
    (hU_open : ∀ i ∈ s, IsOpen (U i))
    {φ : NPointDomain d n → ℂ}
    (hφ_compact : HasCompactSupport φ)
    (h0 :
      ∀ u ∈ tsupport φ,
        ∃ i : ι,
          i ∈ s ∧
            BHW.os45FlatCommonChartSourceSide
              d n ρperm sgn 0 η u ∈ U i)
    (hC :
      ∀ᶠ eps in 𝓝[Set.Ioi 0] (0 : ℝ),
        ∀ u,
          u ∈ Function.support φ →
            BHW.os45FlatCommonChartSourceSide
              d n ρperm sgn eps η u ∈ C) :
    ∀ᶠ eps in 𝓝[Set.Ioi 0] (0 : ℝ),
      ∀ u,
        u ∈ Function.support φ →
          BHW.os45FlatCommonChartSourceSide
            d n ρperm sgn eps η u ∈
            ({z | ∃ i : ι, i ∈ s ∧ z ∈ U i} ∩ C) := by
  classical
  have hcover :
      ∀ᶠ eps in 𝓝[Set.Ioi 0] (0 : ℝ),
        ∀ u,
          u ∈ Function.support φ →
            ∃ i : ι,
              i ∈ s ∧
                BHW.os45FlatCommonChartSourceSide
                  d n ρperm sgn eps η u ∈ U i :=
    eventually_forall_os45FlatCommonChartSourceSide_mem_finset_cover
      ρperm sgn η s U hU_open hφ_compact h0
  filter_upwards [hcover, hC] with eps hcover_eps hC_eps u hu
  exact ⟨hcover_eps u hu, hC_eps u hu⟩

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

/-- Selected-data adapter for the local Figure-2-4 common-edge holomorphic
difference germ.

This is the Stage-A producer consumed by
`os45CommonEdge_localHorizontalDifference_representsZero_of_germ`.  The proof
now delegates the selected Jost/Ruelle and post-seed Hdiff construction to the
checked companion theorem `os45_hdiff_of_selectedJostData`, keeping this
frontier file as the public entry point.

Route guard: because this adapter requires selected Jost/Ruelle data, it is a
legacy/diagnostic route for theorem-2 closure.  The active boundary-value
frontier should consume concrete local Hdiff/source-representation packets via
the reduced local CLM path, and should not use this adapter to feed the old
local `S'_n` trust boundary into `bvt_W_swap_pairing_of_spacelike`. -/
theorem os45CommonEdge_localFigure24DifferenceGerm_of_OSI45
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (hOverlap :
      ∀ (j : Fin n) (hj : j.val + 1 < n),
        IsConnected
          {z : Fin n → Fin (d + 1) → ℂ |
            z ∈ BHW.ExtendedTube d n ∧
              BHW.permAct (d := d)
                (Equiv.swap j ⟨j.val + 1, hj⟩) z ∈
                BHW.ExtendedTube d n})
    (hData : SelectedAdjacentDistributionalJostAnchorData OS lgc n)
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
  exact
    BHW.os45_hdiff_of_selectedJostData
      (d := d) hd OS lgc (P := P) H hOverlap hData
      U hU_open hU_nonempty hU_sub

end BHW
