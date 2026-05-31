import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45Figure24Seed
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanLocalityOS45SourceSideMoving
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValuesBase
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanRuelleOverlap
import OSReconstruction.SCV.IdentityTheorem

/-!
# OS45 Figure 2-4 Hdiff Producer

This downstream companion contains the proof-local algebra for the direct
OS-I Figure-2-4 Hdiff proof body.  The selected-Jost/Ruelle adapter at the end
is kept under an explicit legacy name only; it is not the theorem-2 producer.
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

This is one of the two real side-height leaves used by the direct OS-I
Figure-2-4 Hdiff proof body.  It proves the raw adjacent seed limit directly
from the selected OS boundary-value theorem and the source-label change of
variables; it does not introduce a transported adjacent branch, `Wadj`,
`Hdiff`, or a common-boundary packet. -/
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

/-- Fixed-test boundary value for the genuine raw OS-I `(4.12)` seed, in the
`extendF` model used by the adjacent branch charts.

This is the adjacent analogue of
`ordinary41_fixed_test_boundaryValue_extendF`: it removes the temporary
`bvt_F` presentation from `raw412_fixed_test_boundaryValue` once the selected
permuted point is known to lie in the forward tube.  The statement is still the
raw `(4.12)` source selector; it does not introduce an `Hdiff` carrier or any
locality conclusion. -/
private theorem raw412_fixed_test_boundaryValue_extendF
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (τ : Equiv.Perm (Fin n))
    (ψ : SchwartzNPoint d n)
    (η : Fin n → Fin (d + 1) → ℝ)
    (hητ : (fun k μ => η (τ k) μ) ∈ ForwardConeAbs d n) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ x : NPointDomain d n,
        BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) τ
            (fun k μ =>
              (x k μ : ℂ) + (ε : ℂ) * (η k μ : ℂ) * Complex.I)) *
        ψ x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (bvt_W OS lgc n
          (BHW.permuteSchwartz (d := d) τ.symm ψ))) := by
  let ητ : Fin n → Fin (d + 1) → ℝ := fun k μ => η (τ k) μ
  have hbvt :=
    raw412_fixed_test_boundaryValue (d := d) OS lgc τ ψ η
      (by simpa [ητ] using hητ)
  refine hbvt.congr' ?_
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
  filter_upwards [self_mem_nhdsWithin] with ε hε
  apply integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro x
  have hscaled_abs : ε • ητ ∈ ForwardConeAbs d n :=
    forwardConeAbs_smul d n ε hε ητ (by simpa [ητ] using hητ)
  have hz :
      BHW.permAct (d := d) τ
        (fun k μ =>
          (x k μ : ℂ) + (ε : ℂ) * (η k μ : ℂ) * Complex.I) ∈
        BHW.ForwardTube d n := by
    have hz_root :
        BHW.permAct (d := d) τ
          (fun k μ =>
            (x k μ : ℂ) + (ε : ℂ) * (η k μ : ℂ) * Complex.I) ∈
          _root_.ForwardTube d n := by
      rw [_root_.forwardTube_eq_imPreimage, Set.mem_setOf_eq]
      convert hscaled_abs using 1
      ext k μ
      simp [BHW.permAct, ητ, Pi.smul_apply, Complex.add_im,
        Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im]
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using hz_root
  have hext :
      BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) τ
            (fun k μ =>
              (x k μ : ℂ) + (ε : ℂ) * (η k μ : ℂ) * Complex.I)) =
        bvt_F OS lgc n
          (BHW.permAct (d := d) τ
            (fun k μ =>
              (x k μ : ℂ) + (ε : ℂ) * (η k μ : ℂ) * Complex.I)) :=
    BHW.extendF_eq_on_forwardTube n (bvt_F OS lgc n)
      hF_holo hF_real_inv _ hz
  exact congrArg (fun c : ℂ => c * ψ x) hext.symm

/-- Moving-test boundary value for the genuine raw OS-I `(4.12)` seed, in the
`extendF` model used by the adjacent branch charts. -/
private theorem raw412_moving_boundaryValue_extendF
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
        BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) τ
            (fun k μ =>
              (x k μ : ℂ) + (εseq a : ℂ) *
                (η k μ : ℂ) * Complex.I)) *
        fseq a x)
      l
      (nhds
        (bvt_W OS lgc n
          (BHW.permuteSchwartz (d := d) τ.symm f0))) := by
  let ητ : Fin n → Fin (d + 1) → ℝ := fun k μ => η (τ k) μ
  have hbvt :=
    raw412_moving_boundaryValue (d := d) OS lgc τ η
      (by simpa [ητ] using hητ) εseq hεseq hfseq
  refine hbvt.congr' ?_
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
  have hpos : ∀ᶠ a in l, εseq a ∈ Set.Ioi (0 : ℝ) :=
    hεseq.eventually self_mem_nhdsWithin
  filter_upwards [hpos] with a ha
  apply integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro x
  have hscaled_abs : εseq a • ητ ∈ ForwardConeAbs d n :=
    forwardConeAbs_smul d n (εseq a) ha ητ (by simpa [ητ] using hητ)
  have hz :
      BHW.permAct (d := d) τ
        (fun k μ =>
          (x k μ : ℂ) + (εseq a : ℂ) *
            (η k μ : ℂ) * Complex.I) ∈
        BHW.ForwardTube d n := by
    have hz_root :
        BHW.permAct (d := d) τ
          (fun k μ =>
            (x k μ : ℂ) + (εseq a : ℂ) *
              (η k μ : ℂ) * Complex.I) ∈
          _root_.ForwardTube d n := by
      rw [_root_.forwardTube_eq_imPreimage, Set.mem_setOf_eq]
      convert hscaled_abs using 1
      ext k μ
      simp [BHW.permAct, ητ, Pi.smul_apply, Complex.add_im,
        Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im]
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using hz_root
  have hext :
      BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) τ
            (fun k μ =>
              (x k μ : ℂ) + (εseq a : ℂ) *
                (η k μ : ℂ) * Complex.I)) =
        bvt_F OS lgc n
          (BHW.permAct (d := d) τ
            (fun k μ =>
              (x k μ : ℂ) + (εseq a : ℂ) *
                (η k μ : ℂ) * Complex.I)) :=
    BHW.extendF_eq_on_forwardTube n (bvt_F OS lgc n)
      hF_holo hF_real_inv _ hz
  exact congrArg (fun c : ℂ => c * fseq a x) hext.symm

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

private theorem PointedMetricBranchChart.eventually_integral_eq_os45FlatCommonChartSourceSide_of_seed
    [NeZero d]
    (ρperm : Equiv.Perm (Fin n))
    (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (A B : PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ)
    (hseed :
      ∃ W : Set (Fin n → Fin (d + 1) → ℂ),
        IsOpen W ∧ z0 ∈ W ∧
          W ⊆ A.carrier ∩ B.carrier ∧ Set.EqOn A.branch B.branch W)
    {K : Set (NPointDomain d n)}
    (hK : IsCompact K)
    (hA0 :
      ∀ u ∈ K,
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u ∈
          A.carrier)
    (hB0 :
      ∀ u ∈ K,
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u ∈
          B.carrier)
    (φ : SchwartzNPoint d n)
    (hφK : tsupport (φ : NPointDomain d n → ℂ) ⊆ K) :
    ∀ᶠ eps in 𝓝[Set.Ioi 0] (0 : ℝ),
      (∫ u : NPointDomain d n,
        A.branch
            (BHW.os45FlatCommonChartSourceSide d n ρperm sgn eps η u) *
          (φ : NPointDomain d n → ℂ) u) =
        ∫ u : NPointDomain d n,
          B.branch
              (BHW.os45FlatCommonChartSourceSide d n ρperm sgn eps η u) *
            (φ : NPointDomain d n → ℂ) u := by
  have hEq :
      Set.EqOn A.branch B.branch (A.carrier ∩ B.carrier) :=
    PointedMetricBranchChart.eqOn_inter_of_seed
      (z0 := z0) A B hseed
  have hAevent :
      ∀ᶠ eps in 𝓝[Set.Ioi 0] (0 : ℝ),
        ∀ u ∈ K,
          BHW.os45FlatCommonChartSourceSide d n ρperm sgn eps η u ∈
            A.carrier :=
    BHW.eventually_forall_os45FlatCommonChartSourceSide_mem_of_compact
      (d := d) (n := n) ρperm sgn η hK A.carrier_open hA0
  have hBevent :
      ∀ᶠ eps in 𝓝[Set.Ioi 0] (0 : ℝ),
        ∀ u ∈ K,
          BHW.os45FlatCommonChartSourceSide d n ρperm sgn eps η u ∈
            B.carrier :=
    BHW.eventually_forall_os45FlatCommonChartSourceSide_mem_of_compact
      (d := d) (n := n) ρperm sgn η hK B.carrier_open hB0
  filter_upwards [hAevent, hBevent] with eps hAeps hBeps
  apply integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro u
  by_cases hu : u ∈ K
  · have hz :
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn eps η u ∈
          A.carrier ∩ B.carrier :=
      ⟨hAeps u hu, hBeps u hu⟩
    exact
      congrArg
        (fun c : ℂ => c * (φ : NPointDomain d n → ℂ) u)
        (hEq hz)
  · have hφ_zero : (φ : NPointDomain d n → ℂ) u = 0 :=
      image_eq_zero_of_notMem_tsupport (fun huφ => hu (hφK huφ))
    simp [hφ_zero]

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

private noncomputable def flat_realJost_EOW_pointed_seed_of_local414_integrals
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
    (x0 : BHW.OS45FlatCommonChartReal d n)
    (hx0 : x0 ∈ E)
    (bvIn bvOut : BHW.OS45FlatCommonChartReal d n → ℂ)
    (hbvIn_cont : ContinuousOn bvIn E)
    (hbvOut_cont : ContinuousOn bvOut E)
    (hsideIn_bvIn :
      ∀ x ∈ E,
        Filter.Tendsto
          (BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n)))
          (nhdsWithin (SCV.realEmbed x)
            (BHW.os45FlatCommonChartOmega d n
              (1 : Equiv.Perm (Fin n))))
          (nhds (bvIn x)))
    (hsideOut_bvOut :
      ∀ x ∈ E,
        Filter.Tendsto
          (BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n))))
          (nhdsWithin (SCV.realEmbed x)
            (BHW.os45FlatCommonChartOmega d n
              (P.τ.symm * (1 : Equiv.Perm (Fin n)))))
          (nhds (bvOut x)))
    (h414_integrals :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆ E →
        (∫ x : BHW.OS45FlatCommonChartReal d n, bvOut x * φ x) =
          ∫ x : BHW.OS45FlatCommonChartReal d n, bvIn x * φ x)
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
  have h414_bv_eq : Set.EqOn bvOut bvIn E :=
    SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn
      hE_open hbvOut_cont hbvIn_cont h414_integrals
  have hsideOut_bvIn :
      ∀ x ∈ E,
        Filter.Tendsto
          (BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n))))
          (nhdsWithin (SCV.realEmbed x)
            (BHW.os45FlatCommonChartOmega d n
              (P.τ.symm * (1 : Equiv.Perm (Fin n)))))
          (nhds (bvIn x)) := by
    intro x hx
    simpa [h414_bv_eq hx] using hsideOut_bvOut x hx
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
    BHW.os45_BHWJost_initialSectorEqOn_open_of_flatCommonChart_continuousBoundaryOn
      (d := d) hd OS lgc (P := P) hE_open hE_sub
      bvIn hbvIn_cont hsideIn_bvIn hsideOut_bvIn x0 hx0
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

private noncomputable def flatCrossingAtZ0_of_sourceCommonEdge_eqOn
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    {U : Set (NPointDomain d n)}
    (hU_open : IsOpen U)
    (hU_sub : U ⊆ P.V)
    (hsource_eq :
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
                (1 : Equiv.Perm (Fin n)) u)))
    (u0 : NPointDomain d n) (hu0 : u0 ∈ U)
    {Cplus Cminus : OS45PointedChart d n}
    (hzCplus :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u0)) ∈ Cplus.carrier)
    (hzCminus :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u0)) ∈ Cminus.carrier)
    (hCplus_model :
      Set.EqOn Cplus.branch (BHW.extendF (bvt_F OS lgc n))
        Cplus.carrier)
    (hCminus_model :
      Set.EqOn Cminus.branch
        (fun z =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z)) Cminus.carrier) :
    FlatCrossingAtZ0 (P := P) hd OS lgc
      ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) u0)))
      Cplus Cminus := by
  classical
  let e := BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n))
  let E : Set (BHW.OS45FlatCommonChartReal d n) := e '' U
  let D : BHW.OS45Figure24SourceCutoffData P :=
    Classical.choice (BHW.exists_os45Figure24SourceCutoffData (d := d) P)
  let Tlocal : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ →L[ℂ] ℂ :=
    BHW.os45FlatCommonChart_ordinaryEdgeCLM hd OS lgc P
  have hn_pos : 0 < n := by omega
  haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn_pos⟩
  have hm : 0 < BHW.os45FlatCommonChartDim d n :=
    BHW.os45FlatCommonChartDim_pos_of_adjacent d n hi
  obtain ⟨hC_open, _hC_conv, _hC_zero, _hC_cone, hC_nonempty⟩ :=
    BHW.os45FlatCommonChartCone_eowReady d n
  let hBasis :=
    open_set_contains_basis hm
      (BHW.os45FlatCommonChartCone d n) hC_open hC_nonempty
  let ys := Classical.choose hBasis
  have hys_mem : ∀ j, ys j ∈ BHW.os45FlatCommonChartCone d n :=
    (Classical.choose_spec hBasis).1
  have hys_li : LinearIndependent ℝ ys :=
    (Classical.choose_spec hBasis).2
  have hE_open : IsOpen E := by
    simpa [E, e] using e.toHomeomorph.isOpenMap U hU_open
  have hE_sub :
      E ⊆ BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)) := by
    rintro x ⟨u, huU, rfl⟩
    exact
      (BHW.os45CommonEdgeFlatCLE_mem_edgeSet_iff d n P
        (1 : Equiv.Perm (Fin n)) u).mpr (hU_sub huU)
  have hx0 : e u0 ∈ E := ⟨u0, hu0, rfl⟩
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
    exact
      (BHW.os45FlatCommonChart_zeroHeight_pairings_eq_of_sourceCommonEdge_eqOn
        (d := d) hd OS lgc D hU_sub hsource_eq φ hφ_compact hφE).trans
        (hzero_plus φ hφ_compact hφE)
  have hz0_flat :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u0)) =
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.unflattenCfg n d (SCV.realEmbed (e u0))) := by
    have hsource_zero :=
      BHW.os45FlatCommonChartSourceSide_zero_eq_commonEdge
        (d := d) (n := n)
        (1 : Equiv.Perm (Fin n)) (1 : ℝ)
        (0 : BHW.OS45FlatCommonChartReal d n) u0
    calc
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u0)) =
          BHW.os45FlatCommonChartSourceSide d n
            (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0
            (0 : BHW.OS45FlatCommonChartReal d n) u0 := hsource_zero.symm
      _ = (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.unflattenCfg n d (SCV.realEmbed (e u0))) := by
            have hreal :
                SCV.realEmbed (e u0) =
                  (fun a : Fin (BHW.os45FlatCommonChartDim d n) =>
                    ((e u0) a : ℂ)) := rfl
            rw [hreal]
            ext k μ
            simp [BHW.os45FlatCommonChartSourceSide, e]
  exact
    { E := E
      E_open := hE_open
      E_sub := hE_sub
      ys := ys
      ys_mem := hys_mem
      ys_li := hys_li
      x0 := e u0
      x0_mem := hx0
      T := Tlocal
      zero_plus := hzero_plus
      zero_minus := hzero_minus
      z0_flat := hz0_flat
      z0_mem_plus := hzCplus
      z0_mem_minus := hzCminus
      plus_model := hCplus_model
      minus_model := hCminus_model }

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

private def localOverlapAtZ0_ordinary_of_ordModels
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    {A0 B0 : OS45PointedChart d n}
    (hA : OrdModelAtZ0 d n z0 (BHW.extendF (bvt_F OS lgc n)) A0)
    (hB : OrdModelAtZ0 d n z0 (BHW.extendF (bvt_F OS lgc n)) B0) :
    LocalOverlapAtZ0 (P := P) hd OS lgc z0 A0 B0 :=
  LocalOverlapAtZ0.ordinary hA hB A0 hA

private def localOverlapAtZ0_adjacent_of_commonModel
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    {A0 B0 rawLocal : OS45PointedChart d n}
    {model : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hzA : z0 ∈ A0.carrier)
    (hzB : z0 ∈ B0.carrier)
    (hzRaw : z0 ∈ rawLocal.carrier)
    (hA_model : Set.EqOn A0.branch model A0.carrier)
    (hB_model : Set.EqOn B0.branch model B0.carrier)
    (hRaw_model : Set.EqOn rawLocal.branch model rawLocal.carrier) :
    LocalOverlapAtZ0 (P := P) hd OS lgc z0 A0 B0 := by
  let hA_adj : RawRetargetAtZ0 d n z0 A0 rawLocal :=
    { z0_mem := hzA
      edge_to_raw :=
        pointed_seed_edge_of_common_model
          A0.carrier_open rawLocal.carrier_open hzA hzRaw
          hA_model hRaw_model }
  let hB_adj : RawRetargetAtZ0 d n z0 B0 rawLocal :=
    { z0_mem := hzB
      edge_to_raw :=
        pointed_seed_edge_of_common_model
          B0.carrier_open rawLocal.carrier_open hzB hzRaw
          hB_model hRaw_model }
  exact LocalOverlapAtZ0.adjacent rawLocal hA_adj hB_adj hzRaw

private def localOverlapAtZ0_flat_plus_minus_of_models
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    {A0 B0 Cplus Cminus : OS45PointedChart d n}
    (hflat : FlatCrossingAtZ0 (P := P) hd OS lgc z0 Cplus Cminus)
    (hA_plus :
      OrdModelAtZ0 d n z0 (BHW.extendF (bvt_F OS lgc n)) A0)
    (hzB : z0 ∈ B0.carrier)
    (hB_minus :
      Set.EqOn B0.branch
        (fun z =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z)) B0.carrier) :
    LocalOverlapAtZ0 (P := P) hd OS lgc z0 A0 B0 := by
  let hB_flat : FlatMinusAtZ0 d n z0 B0 Cminus :=
    { z0_mem := hzB
      to_Cminus_edge :=
        pointed_seed_edge_of_common_model
          B0.carrier_open Cminus.carrier_open hzB hflat.z0_mem_minus
          hB_minus hflat.minus_model }
  exact LocalOverlapAtZ0.flat_plus_minus Cplus Cminus hflat hA_plus hB_flat

private def localOverlapAtZ0_flat_minus_plus_of_models
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    {A0 B0 Cplus Cminus : OS45PointedChart d n}
    (hflat : FlatCrossingAtZ0 (P := P) hd OS lgc z0 Cplus Cminus)
    (hzA : z0 ∈ A0.carrier)
    (hA_minus :
      Set.EqOn A0.branch
        (fun z =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z)) A0.carrier)
    (hB_plus :
      OrdModelAtZ0 d n z0 (BHW.extendF (bvt_F OS lgc n)) B0) :
    LocalOverlapAtZ0 (P := P) hd OS lgc z0 A0 B0 := by
  let hA_flat : FlatMinusAtZ0 d n z0 A0 Cminus :=
    { z0_mem := hzA
      to_Cminus_edge :=
        pointed_seed_edge_of_common_model
          A0.carrier_open Cminus.carrier_open hzA hflat.z0_mem_minus
          hA_minus hflat.minus_model }
  exact LocalOverlapAtZ0.flat_minus_plus Cplus Cminus hflat hA_flat hB_plus

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

private theorem LocalOverlapAtZ0.eqOn_inter
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    {z0 : Fin n → Fin (d + 1) → ℂ}
    {A0 B0 : OS45PointedChart d n}
    (hcase : LocalOverlapAtZ0 (P := P) hd OS lgc z0 A0 B0) :
    Set.EqOn A0.branch B0.branch (A0.carrier ∩ B0.carrier) := by
  obtain ⟨G, hleft0, hright0⟩ :=
    localOverlapAtZ0_galleryPair
      (d := d) hd OS lgc (P := P) hcase
  have hseed := G.endpoint_seed
  have hseed_AB :
      ∃ W : Set (Fin n → Fin (d + 1) → ℂ),
        IsOpen W ∧ z0 ∈ W ∧
          W ⊆ A0.carrier ∩ B0.carrier ∧
          Set.EqOn A0.branch B0.branch W := by
    rcases hseed with ⟨W, hW_open, hzW, hW_sub, hW_eq⟩
    refine ⟨W, hW_open, hzW, ?_, ?_⟩
    · intro z hz
      exact ⟨by simpa [hleft0] using (hW_sub hz).1,
        by simpa [hright0] using (hW_sub hz).2⟩
    · intro z hz
      simpa [hleft0, hright0] using hW_eq hz
  exact PointedMetricBranchChart.eqOn_inter_of_seed A0 B0 hseed_AB

private theorem fixed_sourceSide_integral_refined_chart_partition_tendsto_of_localOverlaps
    {d n : ℕ} [NeZero d] {hd : 2 ≤ d}
    {i : Fin n} {hi : i.val + 1 < n}
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
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
    (zstatic : α → Fin n → Fin (d + 1) → ℂ)
    (zmoving : β → Fin n → Fin (d + 1) → ℂ)
    (hstatic_overlap :
      ∀ c, LocalOverlapAtZ0 (P := P) hd OS lgc
        (zstatic c) Astatic (Bstatic c))
    (hmoving_overlap :
      ∀ c, LocalOverlapAtZ0 (P := P) hd OS lgc
        (zmoving c) Amoving (Bmoving c))
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
  exact
    fixed_sourceSide_integral_refined_chart_partition_tendsto_of_local
      (d := d) (n := n) ρperm sgn η Astatic Amoving
      Bstatic Bmoving staticApproach hstatic_cont w hw_comp hw_vanish
      Ustatic Umoving hUstatic_open hUmoving_open
      hstatic_cover hmoving_cover hstatic_zero hmoving_zero
      (fun c =>
        LocalOverlapAtZ0.eqOn_inter
          (d := d) hd OS lgc (P := P) (hstatic_overlap c))
      (fun c =>
        LocalOverlapAtZ0.eqOn_inter
          (d := d) hd OS lgc (P := P) (hmoving_overlap c))
      hlocal

private theorem fixed_sourceSide_integral_refined_chart_partition_tendsto_of_commonAnchorOverlaps
    {d n : ℕ} [NeZero d] {hd : 2 ≤ d}
    {i : Fin n} {hi : i.val + 1 < n}
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {α β : Type*} [Fintype α] [Fintype β]
    (ρperm : Equiv.Perm (Fin n)) (sgn : ℝ)
    (η : BHW.OS45FlatCommonChartReal d n)
    (A : PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ)
    (Bstatic : α →
      PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ)
    (Bmoving : β →
      PointedMetricBranchChart (Fin n → Fin (d + 1) → ℂ) ℂ)
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
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u ∈
          A.carrier ∩ (Bstatic c).carrier)
    (hmoving_zero :
      ∀ c, ∀ u ∈ Umoving c,
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u ∈
          A.carrier ∩ (Bmoving c).carrier)
    (zstatic : α → Fin n → Fin (d + 1) → ℂ)
    (zmoving : β → Fin n → Fin (d + 1) → ℂ)
    (hstatic_overlap :
      ∀ c, LocalOverlapAtZ0 (P := P) hd OS lgc
        (zstatic c) A (Bstatic c))
    (hmoving_overlap :
      ∀ c, LocalOverlapAtZ0 (P := P) hd OS lgc
        (zmoving c) A (Bmoving c)) :
    Tendsto
      (fun ε : ℝ =>
        ∫ u : NPointDomain d n,
          A.branch
            (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u) *
          (w : NPointDomain d n → ℂ) u)
      (𝓝[Set.Ioi 0] (0 : ℝ))
      (𝓝
        (∫ u : NPointDomain d n,
          A.branch
            (BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u) *
          (w : NPointDomain d n → ℂ) u)) := by
  let staticApproach : NPointDomain d n → Fin n → Fin (d + 1) → ℂ :=
    fun u => BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u
  have hstatic_cont : Continuous staticApproach := by
    simpa [staticApproach] using
      BHW.continuous_os45FlatCommonChartSourceSide_fixed_eps
        (d := d) (n := n) ρperm sgn (0 : ℝ) η
  refine
    fixed_sourceSide_integral_refined_chart_partition_tendsto_of_localOverlaps
      (d := d) (n := n) OS lgc (P := P)
      ρperm sgn η A A Bstatic Bmoving staticApproach hstatic_cont
      w hw_comp hw_vanish Ustatic Umoving hUstatic_open hUmoving_open
      hstatic_cover hmoving_cover hstatic_zero hmoving_zero
      zstatic zmoving hstatic_overlap hmoving_overlap ?_
  intro cs cm piece hpiece_comp _hpiece_vanish _hpiece_base hpiece_sub
  let l : Filter ℝ := 𝓝[Set.Ioi 0] (0 : ℝ)
  let F : (Fin n → Fin (d + 1) → ℂ) → ℂ := (Bmoving cm).branch
  have h0 :
      ∀ u ∈ tsupport (piece : NPointDomain d n → ℂ),
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u ∈
          (Bmoving cm).carrier := by
    intro u hu
    exact (hmoving_zero cm u (hpiece_sub hu).2).2
  have hsupp :
      ∀ᶠ _ε in l, ∀ u ∉ tsupport (piece : NPointDomain d n → ℂ),
        ((piece - piece : SchwartzNPoint d n) :
          NPointDomain d n → ℂ) u = 0 := by
    filter_upwards with ε u hu
    simp
  have hseminorm :
      Tendsto
        (fun _ε : ℝ =>
          SchwartzMap.seminorm ℝ 0 0
            (piece - piece : SchwartzNPoint d n))
        l (𝓝 0) := by
    have hzero :
        (fun _ε : ℝ =>
          SchwartzMap.seminorm ℝ 0 0
            (piece - piece : SchwartzNPoint d n)) =
          fun _ε : ℝ => (0 : ℝ) := by
      funext ε
      simp
    rw [hzero]
    exact tendsto_const_nhds
  have hmove :
      Tendsto
        (fun ε : ℝ =>
          ∫ u : NPointDomain d n,
            (Bmoving cm).branch
              (BHW.os45FlatCommonChartSourceSide d n ρperm sgn ε η u) *
            (piece : NPointDomain d n → ℂ) u)
        l
        (𝓝
          (∫ u : NPointDomain d n,
            (Bmoving cm).branch
              (BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u) *
            (piece : NPointDomain d n → ℂ) u)) := by
    exact
      BHW.tendsto_integral_comp_os45FlatCommonChartSourceSide_mul_moving_of_commonCompactSupport
        (d := d) (n := n) ρperm sgn η
        (Bmoving cm).carrier_open (Bmoving cm).holo.continuousOn
        hpiece_comp.isCompact h0
        (tendsto_id :
          Tendsto (fun ε : ℝ => ε) l (𝓝[Set.Ioi 0] (0 : ℝ)))
        (fun u hu => hu) hsupp hseminorm
  have htarget :
      (∫ u : NPointDomain d n,
        (Bmoving cm).branch
          (BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u) *
        (piece : NPointDomain d n → ℂ) u) =
      ∫ u : NPointDomain d n,
        (Bstatic cs).branch
          (BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u) *
        (piece : NPointDomain d n → ℂ) u := by
    apply integral_congr_ae
    filter_upwards with u
    by_cases hu :
        u ∈ tsupport (piece : NPointDomain d n → ℂ)
    · let z : Fin n → Fin (d + 1) → ℂ :=
        BHW.os45FlatCommonChartSourceSide d n ρperm sgn 0 η u
      have hz_static :
          z ∈ A.carrier ∩ (Bstatic cs).carrier := by
        simpa [z] using hstatic_zero cs u (hpiece_sub hu).1
      have hz_moving :
          z ∈ A.carrier ∩ (Bmoving cm).carrier := by
        simpa [z] using hmoving_zero cm u (hpiece_sub hu).2
      have hstatic_eq :=
        (LocalOverlapAtZ0.eqOn_inter
          (d := d) hd OS lgc (P := P)
          (hstatic_overlap cs)) hz_static
      have hmoving_eq :=
        (LocalOverlapAtZ0.eqOn_inter
          (d := d) hd OS lgc (P := P)
          (hmoving_overlap cm)) hz_moving
      have hbranch :
          (Bmoving cm).branch z = (Bstatic cs).branch z :=
        hmoving_eq.symm.trans hstatic_eq
      simpa [z] using
        congrArg (fun c : ℂ =>
          c * (piece : NPointDomain d n → ℂ) u) hbranch
    · have hpiece_zero :
          (piece : NPointDomain d n → ℂ) u = 0 :=
        image_eq_zero_of_notMem_tsupport hu
      simp [hpiece_zero]
  rw [htarget] at hmove
  simpa [l, F, staticApproach] using hmove

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

private theorem OS45BHWJostHullData.OS412SeedWindow_pointedChart_extendFPermActModel
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {x : NPointDomain d n} (hx : x ∈ P.V) :
    ∃ A : OS45PointedChart d n,
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
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z)) A.carrier ∧
      A.branch A.center =
        bvt_F OS lgc n (fun k => wickRotatePoint (x (P.τ k))) := by
  classical
  rcases H.OS412SeedWindow_pointedChart OS lgc hx with
    ⟨A, hA_center, hA_mem, hA_sub, hA_raw, hA_trace⟩
  have hF_holo :
      DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      bvt_F_holomorphic (d := d) OS lgc n
  have hF_lorentz :
      ∀ (Λ : LorentzLieGroup.RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
        bvt_F OS lgc n
          (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) =
        bvt_F OS lgc n z := by
    intro Λ z hz
    exact bvt_F_restrictedLorentzInvariant_forwardTube
      (d := d) OS lgc n Λ z
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
  refine ⟨A, hA_center, hA_mem, hA_sub, ?_, hA_trace⟩
  intro z hz
  have hz_forward :
      BHW.permAct (d := d) P.τ z ∈ BHW.ForwardTube d n :=
    (hA_sub hz).1.1
  have hext :
      BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) P.τ z) =
        bvt_F OS lgc n (BHW.permAct (d := d) P.τ z) :=
    BHW.extendF_eq_on_forwardTube n (bvt_F OS lgc n)
      hF_holo hF_lorentz
      (BHW.permAct (d := d) P.τ z) hz_forward
  exact (hA_raw hz).trans hext.symm

private theorem OS45BHWJostHullData.OS412SeedWindow_localOverlapAtZ0_adjacentModel
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {x : NPointDomain d n} (hx : x ∈ P.V)
    {Aadj : OS45PointedChart d n}
    (hzAadj :
      BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k)) ∈
        Aadj.carrier)
    (hAadj_model :
      Set.EqOn Aadj.branch
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z)) Aadj.carrier) :
    ∃ rawLocal : OS45PointedChart d n,
      rawLocal.center =
        BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k)) ∧
      BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k)) ∈
        rawLocal.carrier ∧
      Set.EqOn rawLocal.branch
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z)) rawLocal.carrier ∧
      Nonempty (LocalOverlapAtZ0 (P := P) hd OS lgc
        (BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k)))
        Aadj rawLocal) := by
  classical
  rcases H.OS412SeedWindow_pointedChart_extendFPermActModel OS lgc hx with
    ⟨rawLocal, hraw_center, hraw_mem_center, _hraw_sub, hraw_model,
      _hraw_trace⟩
  have hzRaw :
      BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k)) ∈
        rawLocal.carrier := by
    rw [← hraw_center]
    exact hraw_mem_center
  refine ⟨rawLocal, hraw_center, hzRaw, hraw_model, ⟨?_⟩⟩
  exact
    localOverlapAtZ0_adjacent_of_commonModel
      (d := d) hd OS lgc (P := P)
      (z0 := BHW.permAct (d := d) P.τ
        (fun k => wickRotatePoint (x k)))
      (A0 := Aadj) (B0 := rawLocal) (rawLocal := rawLocal)
      hzAadj hzRaw hzRaw hAadj_model hraw_model hraw_model

private theorem OS45BHWJostHullData.OS412SeedWindow_adjacentModel_trace_at_seed
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {x : NPointDomain d n} (hx : x ∈ P.V)
    {Aadj : OS45PointedChart d n}
    (hzAadj :
      BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k)) ∈
        Aadj.carrier)
    (hAadj_model :
      Set.EqOn Aadj.branch
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z)) Aadj.carrier) :
    Aadj.branch
        (BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k))) =
      bvt_F OS lgc n (fun k => wickRotatePoint (x (P.τ k))) := by
  classical
  let z0 : Fin n → Fin (d + 1) → ℂ :=
    BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k))
  rcases H.OS412SeedWindow_pointedChart_extendFPermActModel OS lgc hx with
    ⟨rawLocal, hraw_center, hraw_mem_center, _hraw_sub, hraw_model,
      hraw_trace⟩
  have hraw_center_z0 : rawLocal.center = z0 := by
    simpa [z0] using hraw_center
  have hzRaw : z0 ∈ rawLocal.carrier := by
    rw [← hraw_center_z0]
    exact hraw_mem_center
  have hover :
      LocalOverlapAtZ0 (P := P) hd OS lgc z0 Aadj rawLocal :=
    localOverlapAtZ0_adjacent_of_commonModel
      (d := d) hd OS lgc (P := P)
      (z0 := z0) (A0 := Aadj) (B0 := rawLocal) (rawLocal := rawLocal)
      (by simpa [z0] using hzAadj) hzRaw hzRaw
      hAadj_model hraw_model hraw_model
  have heqOn :
      Set.EqOn Aadj.branch rawLocal.branch
        (Aadj.carrier ∩ rawLocal.carrier) :=
    LocalOverlapAtZ0.eqOn_inter (d := d) hd OS lgc
      (P := P) hover
  have heq : Aadj.branch z0 = rawLocal.branch z0 :=
    heqOn ⟨by simpa [z0] using hzAadj, hzRaw⟩
  calc
    Aadj.branch z0 = rawLocal.branch z0 := heq
    _ = rawLocal.branch rawLocal.center := by rw [← hraw_center_z0]
    _ = bvt_F OS lgc n (fun k => wickRotatePoint (x (P.τ k))) :=
      hraw_trace

/-- The same raw `(4.12)` seed trace, normalized to the ordinary Wick value.

This is the value targeted by the source-side compact-test transport: the
selected adjacent seed chart is still the genuine raw `(4.12)` element, but at
its seed the OS permutation symmetry rewrites the trace as the ordinary Wick
boundary value. -/
private theorem OS45BHWJostHullData.OS412SeedWindow_adjacentModel_trace_at_seed_ordinaryWick
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    (H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {x : NPointDomain d n} (hx : x ∈ P.V)
    {Aadj : OS45PointedChart d n}
    (hzAadj :
      BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k)) ∈
        Aadj.carrier)
    (hAadj_model :
      Set.EqOn Aadj.branch
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z)) Aadj.carrier) :
    Aadj.branch
        (BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (x k))) =
      bvt_F OS lgc n (fun k => wickRotatePoint (x k)) := by
  classical
  have hseed :=
    H.OS412SeedWindow_adjacentModel_trace_at_seed
      OS lgc hx hzAadj hAadj_model
  have hperm :
      bvt_F OS lgc n (fun k => wickRotatePoint (x (P.τ k))) =
        bvt_F OS lgc n (fun k => wickRotatePoint (x k)) := by
    simpa [BHW.permAct] using
      bvt_F_perm (d := d) OS lgc n P.τ
        (fun k => wickRotatePoint (x k))
  exact hseed.trans hperm

/-- Fixed-chart compact-test form of the raw `(4.12)` adjacent seed
normalization.

If a local adjacent chart modeled by `extendF ∘ permAct P.τ` covers the
selected adjacent Wick seeds over a source window, then its compact-test
pairing on those seeds is the ordinary Wick pairing.  This is the local
piece consumed by the later finite source-side branch-transfer partition. -/
private theorem OS45BHWJostHullData.OS412SeedWindow_adjacentModel_permActWick_pairing_eq_ordinaryWick
    [NeZero d]
    {hd : 2 ≤ d} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi}
    (_H : BHW.OS45BHWJostHullData (d := d) hd n i hi P)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {U : Set (NPointDomain d n)}
    (hU_sub : U ⊆ P.V)
    {Aadj : OS45PointedChart d n}
    (hAadj_mem :
      ∀ u ∈ U,
        BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (u k)) ∈
          Aadj.carrier)
    (hAadj_model :
      Set.EqOn Aadj.branch
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z)) Aadj.carrier)
    (φ : SchwartzNPoint d n)
    (hφU : tsupport (φ : NPointDomain d n → ℂ) ⊆ U) :
    ∫ u : NPointDomain d n,
        Aadj.branch
          (BHW.permAct (d := d) P.τ
            (fun k => wickRotatePoint (u k))) * φ u =
      ∫ u : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (u k)) * φ u := by
  classical
  have hF_holo :
      DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      bvt_F_holomorphic (d := d) OS lgc n
  have hF_lorentz :
      ∀ (Λ : LorentzLieGroup.RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
        bvt_F OS lgc n
          (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) =
        bvt_F OS lgc n z := by
    intro Λ z hz
    exact bvt_F_restrictedLorentzInvariant_forwardTube
      (d := d) OS lgc n Λ z
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro u
  by_cases hu : u ∈ U
  · let z : Fin n → Fin (d + 1) → ℂ :=
      BHW.permAct (d := d) P.τ (fun k => wickRotatePoint (u k))
    have hzA : z ∈ Aadj.carrier := by
      simpa [z] using hAadj_mem u hu
    have hmodel :
        Aadj.branch z =
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z) :=
      hAadj_model hzA
    have hdouble :
        BHW.permAct (d := d) P.τ z =
          fun k => wickRotatePoint (u k) := by
      ext k μ
      simp [z, BHW.permAct, P.τ_eq]
    have hforward :
        (fun k => wickRotatePoint (u k)) ∈ BHW.ForwardTube d n :=
      BHW.os45Figure24_ordinaryWick_mem_forwardTube
        (d := d) (n := n) (hd := hd) (P := P) (hU_sub hu)
    have hext :
        BHW.extendF (bvt_F OS lgc n)
            (fun k => wickRotatePoint (u k)) =
          bvt_F OS lgc n (fun k => wickRotatePoint (u k)) :=
      BHW.extendF_eq_on_forwardTube n (bvt_F OS lgc n)
        hF_holo hF_lorentz (fun k => wickRotatePoint (u k)) hforward
    have hpoint :
        Aadj.branch z =
          bvt_F OS lgc n (fun k => wickRotatePoint (u k)) := by
      calc
        Aadj.branch z =
            BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) P.τ z) := hmodel
        _ = BHW.extendF (bvt_F OS lgc n)
              (fun k => wickRotatePoint (u k)) := by rw [hdouble]
        _ = bvt_F OS lgc n (fun k => wickRotatePoint (u k)) := hext
    exact congrArg (fun c : ℂ => c * φ u) hpoint
  · have hφ_zero : φ u = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun hφ_supp => hu (hφU hφ_supp))
    simp [hφ_zero]

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

private theorem OS45BHWJostHullData.ordinaryCommonEdge_ordModelAtZ0InWindow
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
    ∃ A : OS45PointedChart d n,
      A.center =
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) x)) ∧
      OrdModelAtZ0 d n
        ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) x)))
        (BHW.extendF (bvt_F OS lgc n)) A ∧
      A.branch A.center =
        BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
          (1 : Equiv.Perm (Fin n))
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) x)) := by
  rcases H.ordinaryCommonEdge_pointedChartInWindow
      OS lgc hx hW_open hcommonW with
    ⟨A, hcenter, hmem, _hsub, heq, htrace⟩
  refine ⟨A, hcenter, ?_, htrace⟩
  exact
    { z0_mem := by simpa [hcenter] using hmem
      eq_ord := heq }

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

private theorem OS45BHWJostHullData.adjacentCommonEdge_minusModelAtZ0InWindow
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
    ∃ A : OS45PointedChart d n,
      A.center =
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) x)) ∧
      A.center ∈ A.carrier ∧
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
  rcases H.adjacentCommonEdge_pointedChartInWindow
      OS lgc hx hW_open hcommonW with
    ⟨A, hcenter, hmem, _hsub, heq, htrace⟩
  exact ⟨A, hcenter, hmem, heq, htrace⟩

private structure CommonEdgeOrdAdjOverlapData
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    (P : BHW.OS45Figure24CanonicalSourcePatchData (d := d) hd n i hi)
    (x : NPointDomain d n) where
  Aord : OS45PointedChart d n
  Aadj : OS45PointedChart d n
  Aord_center :
    Aord.center =
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) x))
  Aadj_center :
    Aadj.center =
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) x))
  Aord_model :
    OrdModelAtZ0 d n
      ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) x)))
      (BHW.extendF (bvt_F OS lgc n)) Aord
  Aadj_mem :
    ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
      (BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) x))) ∈ Aadj.carrier
  Aadj_model :
    Set.EqOn Aadj.branch
      (fun z : Fin n → Fin (d + 1) → ℂ =>
        BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) P.τ z)) Aadj.carrier
  overlap :
    LocalOverlapAtZ0 (P := P) hd OS lgc
      ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) x)))
      Aord Aadj
  Aord_trace :
    Aord.branch Aord.center =
      BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
        (1 : Equiv.Perm (Fin n))
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) x))
  Aadj_trace :
    Aadj.branch Aadj.center =
      BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin n)))
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) x))

private def OS45BHWJostHullData.commonEdge_ordinary_adjacent_localOverlapAtZ0InWindow
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
            (1 : Equiv.Perm (Fin n)) x)) ∈ W)
    {Cplus Cminus : OS45PointedChart d n}
    (hflat :
      FlatCrossingAtZ0 (P := P) hd OS lgc
        ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) x)))
        Cplus Cminus) :
    CommonEdgeOrdAdjOverlapData (d := d) hd OS lgc P x := by
  classical
  let hord :=
    H.ordinaryCommonEdge_ordModelAtZ0InWindow
      OS lgc hx hW_open hcommonW
  let Aord : OS45PointedChart d n := Classical.choose hord
  have hAord_spec := Classical.choose_spec hord
  let hadj :=
    H.adjacentCommonEdge_minusModelAtZ0InWindow
      OS lgc hx hW_open hcommonW
  let Aadj : OS45PointedChart d n := Classical.choose hadj
  have hAadj_spec := Classical.choose_spec hadj
  have hAadj_center :
      Aadj.center =
        ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) x))) := by
    simpa [Aadj] using hAadj_spec.1
  have hzAadj :
      ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) x))) ∈ Aadj.carrier := by
    rw [← hAadj_center]
    simpa [Aadj] using hAadj_spec.2.1
  have hoverlap :
      LocalOverlapAtZ0 (P := P) hd OS lgc
        ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) x)))
        Aord Aadj :=
    localOverlapAtZ0_flat_plus_minus_of_models
      (d := d) hd OS lgc (P := P) hflat hAord_spec.2.1
      hzAadj hAadj_spec.2.2.1
  exact
    { Aord := Aord
      Aadj := Aadj
      Aord_center := hAord_spec.1
      Aadj_center := hAadj_center
      Aord_model := hAord_spec.2.1
      Aadj_mem := hzAadj
      Aadj_model := hAadj_spec.2.2.1
      overlap := hoverlap
      Aord_trace := hAord_spec.2.2
      Aadj_trace := hAadj_spec.2.2.2 }

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

private theorem OS45BHWJostHullData.commonEdgeDifference_localZero_of_flatCrossingInWindow
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
            (1 : Equiv.Perm (Fin n)) x)) ∈ W)
    {Cplus Cminus : OS45PointedChart d n}
    (hflat :
      FlatCrossingAtZ0 (P := P) hd OS lgc
        ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) x)))
        Cplus Cminus) :
    ∃ Aord Aadj Adiff : OS45PointedChart d n,
      Aord.center =
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) x)) ∧
      Aadj.center =
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) x)) ∧
      Adiff.center =
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) x)) ∧
      ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
        (BHW.realEmbed
          (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
            (1 : Equiv.Perm (Fin n)) x))) ∈
        Adiff.carrier ∩ (Aord.carrier ∩ Aadj.carrier) ∧
      IsOpen (Adiff.carrier ∩ (Aord.carrier ∩ Aadj.carrier)) ∧
      Adiff.carrier ⊆ W ∧
      Set.EqOn Adiff.branch
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) P.τ z) -
            BHW.extendF (bvt_F OS lgc n) z) Adiff.carrier ∧
      Set.EqOn Adiff.branch (fun _ => 0)
        (Adiff.carrier ∩ (Aord.carrier ∩ Aadj.carrier)) ∧
      Adiff.branch Adiff.center = 0 := by
  classical
  let z0 : Fin n → Fin (d + 1) → ℂ :=
    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
      (BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) x))
  let D :=
    H.commonEdge_ordinary_adjacent_localOverlapAtZ0InWindow
      OS lgc hx hW_open hcommonW hflat
  let hdiff :=
    H.commonEdgeDifference_pointedChartInWindow
      OS lgc hx hW_open hcommonW
  let Adiff : OS45PointedChart d n := Classical.choose hdiff
  have hAdiff_spec := Classical.choose_spec hdiff
  have hAdiff_center : Adiff.center = z0 := by
    simpa [Adiff, z0] using hAdiff_spec.1
  have hzAdiff : z0 ∈ Adiff.carrier := by
    rw [← hAdiff_center]
    simpa [Adiff] using hAdiff_spec.2.1
  have hAord_center : D.Aord.center = z0 := by
    simpa [D, z0] using D.Aord_center
  have hAadj_center : D.Aadj.center = z0 := by
    simpa [D, z0] using D.Aadj_center
  have hlocal_overlap :
      Set.EqOn D.Aord.branch D.Aadj.branch
        (D.Aord.carrier ∩ D.Aadj.carrier) :=
    LocalOverlapAtZ0.eqOn_inter (d := d) hd OS lgc
      (P := P) D.overlap
  have hzero_on :
      Set.EqOn Adiff.branch (fun _ => 0)
        (Adiff.carrier ∩ (D.Aord.carrier ∩ D.Aadj.carrier)) := by
    intro z hz
    have hdiff_model := hAdiff_spec.2.2.2.1 hz.1
    have hord_model := D.Aord_model.eq_ord hz.2.1
    have hadj_model := D.Aadj_model hz.2.2
    have hover := hlocal_overlap ⟨hz.2.1, hz.2.2⟩
    have hadj_model' :
        BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z) =
          D.Aadj.branch z := by
      simpa using hadj_model.symm
    have hord_model' :
        BHW.extendF (bvt_F OS lgc n) z = D.Aord.branch z := by
      simpa using hord_model.symm
    calc
      Adiff.branch z =
          BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) P.τ z) -
            BHW.extendF (bvt_F OS lgc n) z := hdiff_model
      _ = D.Aadj.branch z - D.Aord.branch z := by
            rw [hadj_model', hord_model']
      _ = 0 := by
            rw [← hover]
            simp
  have hcenter_mem :
      z0 ∈ Adiff.carrier ∩ (D.Aord.carrier ∩ D.Aadj.carrier) :=
    ⟨hzAdiff, D.Aord_model.z0_mem, D.Aadj_mem⟩
  have hzero_center : Adiff.branch Adiff.center = 0 := by
    have hmem :
        Adiff.center ∈
          Adiff.carrier ∩ (D.Aord.carrier ∩ D.Aadj.carrier) := by
      rw [hAdiff_center]
      exact hcenter_mem
    simpa using hzero_on hmem
  refine
    ⟨D.Aord, D.Aadj, Adiff, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hzero_on, hzero_center⟩
  · simpa [z0] using hAord_center
  · simpa [z0] using hAadj_center
  · simpa [z0] using hAdiff_center
  · simpa [z0] using hcenter_mem
  · exact Adiff.carrier_open.inter
      (D.Aord.carrier_open.inter D.Aadj.carrier_open)
  · intro z hz
    exact (hAdiff_spec.2.2.1 hz).2
  · exact hAdiff_spec.2.2.2.1

/-- Source-side common-edge equality supplies the local horizontal-difference
germ on the Figure-2-4 initial-overlap chart.

This is a Path-2 proof-body step, not another public theorem-2 input gate.  The
OS-I `(4.12)`--`(4.14)` source equality first builds a flat crossing, the
checked common-edge overlap selects an open zero seed for the concrete
`extendF ∘ permAct - extendF` difference, and the SCV identity theorem
propagates that zero to the whole connected initial-overlap carrier. -/
theorem OS45BHWJostHullData.os45CommonEdge_localHdiffGerm_of_sourceCommonEdge_eqOn
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
    (hU_closure : closure U ⊆ P.V)
    (hsource_eq :
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
                (1 : Equiv.Perm (Fin n)) u))) :
    ∃ Ucx : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen Ucx ∧
      IsConnected Ucx ∧
      (∀ u ∈ U, (fun k => wickRotatePoint (u k)) ∈ Ucx) ∧
      (∀ u ∈ U,
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) ∈ Ucx) ∧
      ∃ Hdiff : (Fin n → Fin (d + 1) → ℂ) → ℂ,
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
  rcases
      BHW.os45Figure24_initialSectorOverlap_chartNeighborhood
        (d := d) (n := n) (hd := hd) (P := P)
        hU_compact hU_connected hU_closure with
    ⟨Ucx, hUcx_open, hUcx_connected, hwick_mem, hcommon_mem, hUcx_sub⟩
  let Hdiff : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
    fun z =>
      BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) P.τ z) -
        BHW.extendF (bvt_F OS lgc n) z
  have hHdiff_holo : DifferentiableOn ℂ Hdiff Ucx := by
    have hFord :
        DifferentiableOn ℂ (BHW.extendF (bvt_F OS lgc n)) Ucx :=
      (BHW.differentiableOn_extendF_bvt_F_extendedTube
        (d := d) OS lgc n).mono (by
          intro z hz
          exact (hUcx_sub hz).1)
    have hFadj :
        DifferentiableOn ℂ
          (fun z : Fin n → Fin (d + 1) → ℂ =>
            BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) P.τ z)) Ucx :=
      (BHW.differentiableOn_extendF_bvt_F_permAct_preimageExtendedTube
        (d := d) OS lgc n P.τ).mono (by
          intro z hz
          simpa [BHW.permutedExtendedTubeSector] using (hUcx_sub hz).2)
    exact hFadj.sub hFord
  rcases hU_connected.nonempty with ⟨u0, hu0⟩
  have hU_sub : U ⊆ P.V := fun u hu => hU_closure (subset_closure hu)
  let z0 : Fin n → Fin (d + 1) → ℂ :=
    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
      (BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) u0))
  have hu0P : u0 ∈ P.V := hU_sub hu0
  have hz0Ucx : z0 ∈ Ucx := by
    simpa [z0] using hcommon_mem u0 hu0
  let CplusData :=
    H.ordinaryCommonEdge_ordModelAtZ0InWindow
      OS lgc hu0P hUcx_open hz0Ucx
  let Cplus : OS45PointedChart d n := Classical.choose CplusData
  have hCplus_spec := Classical.choose_spec CplusData
  let CminusData :=
    H.adjacentCommonEdge_minusModelAtZ0InWindow
      OS lgc hu0P hUcx_open hz0Ucx
  let Cminus : OS45PointedChart d n := Classical.choose CminusData
  have hCminus_spec := Classical.choose_spec CminusData
  have hzCminus : z0 ∈ Cminus.carrier := by
    rw [show z0 = Cminus.center by
      simpa [z0, Cminus] using hCminus_spec.1.symm]
    exact hCminus_spec.2.1
  have hflat :
      FlatCrossingAtZ0 (P := P) hd OS lgc z0 Cplus Cminus := by
    simpa [z0, Cplus, Cminus] using
      flatCrossingAtZ0_of_sourceCommonEdge_eqOn
        (d := d) (n := n) hd OS lgc
        hU_open hU_sub hsource_eq u0 hu0
        (Cplus := Cplus) (Cminus := Cminus)
        hCplus_spec.2.1.z0_mem hzCminus
        hCplus_spec.2.1.eq_ord hCminus_spec.2.2.1
  rcases
      H.commonEdgeDifference_localZero_of_flatCrossingInWindow
        OS lgc hu0P hUcx_open hz0Ucx hflat with
    ⟨Aord, Aadj, Adiff, _hAord_center, _hAadj_center, _hAdiff_center,
      hseed_mem, hseed_open, hAdiff_sub, hAdiff_model, hAdiff_zero,
      _hzero_center⟩
  let S : Set (Fin n → Fin (d + 1) → ℂ) :=
    Adiff.carrier ∩ (Aord.carrier ∩ Aadj.carrier)
  have hS_ne : S.Nonempty := by
    exact ⟨z0, by simpa [S, z0] using hseed_mem⟩
  have hS_sub : S ⊆ Ucx := by
    intro z hz
    exact hAdiff_sub hz.1
  have hHdiff_zero_seed : Set.EqOn Hdiff (fun _ => 0) S := by
    intro z hz
    calc
      Hdiff z = Adiff.branch z := by
        exact (hAdiff_model hz.1).symm
      _ = 0 := hAdiff_zero (by simpa [S] using hz)
  have hHdiff_zero : Set.EqOn Hdiff (fun _ => 0) Ucx :=
    identity_theorem_product_of_eqOn_open
      hUcx_open hUcx_connected hseed_open hS_ne hS_sub
      hHdiff_holo (differentiableOn_const (c := (0 : ℂ)))
      hHdiff_zero_seed
  refine
    ⟨Ucx, hUcx_open, hUcx_connected, hwick_mem, hcommon_mem,
      Hdiff, hHdiff_holo, ?_, ?_⟩
  · intro φ hφ_compact hφU
    calc
      ∫ u : NPointDomain d n,
          Hdiff (fun k => wickRotatePoint (u k)) * φ u
          = ∫ u : NPointDomain d n, (0 : ℂ) * φ u := by
            refine MeasureTheory.integral_congr_ae
              (Filter.Eventually.of_forall ?_)
            intro u
            by_cases hu : u ∈ U
            · simp [hHdiff_zero (hwick_mem u hu)]
            · have hφ_zero : φ u = 0 :=
                image_eq_zero_of_notMem_tsupport
                  (fun hφ_supp => hu (hφU hφ_supp))
              simp [hφ_zero]
      _ = 0 := by simp
  · intro u hu
    dsimp [Hdiff]
    rw [BHW.os45Figure24CommonEdge_permAct_extendF_eq_adjacentPulledRealBranch
      (d := d) (n := n) hd OS lgc (P := P) u]
    simp [BHW.os45PulledRealBranch]

/-- Local `(4.14)` compact-test boundary equality supplies the local
horizontal-difference germ on the Figure-2-4 initial-overlap chart.

This is the direct proof-body form of
`OS45BHWJostHullData.os45CommonEdge_localHdiffGerm_of_sourceCommonEdge_eqOn`:
instead of assuming pointwise equality of the two common-edge branches, it
uses the two one-sided flat boundary traces and their compact-test equality on
the current flat edge window.  The flat EOW seed is then inserted directly into
the common-edge initial-overlap identity theorem. -/
theorem OS45BHWJostHullData.os45CommonEdge_localHdiffGerm_of_local414_integrals
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
    (hU_closure : closure U ⊆ P.V)
    (bvIn bvOut : BHW.OS45FlatCommonChartReal d n → ℂ)
    (hbvIn_cont :
      ContinuousOn bvIn
        (BHW.os45CommonEdgeFlatCLE d n
          (1 : Equiv.Perm (Fin n)) '' U))
    (hbvOut_cont :
      ContinuousOn bvOut
        (BHW.os45CommonEdgeFlatCLE d n
          (1 : Equiv.Perm (Fin n)) '' U))
    (hsideIn_bvIn :
      ∀ x ∈
          BHW.os45CommonEdgeFlatCLE d n
            (1 : Equiv.Perm (Fin n)) '' U,
        Filter.Tendsto
          (BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n)))
          (nhdsWithin (SCV.realEmbed x)
            (BHW.os45FlatCommonChartOmega d n
              (1 : Equiv.Perm (Fin n))))
          (nhds (bvIn x)))
    (hsideOut_bvOut :
      ∀ x ∈
          BHW.os45CommonEdgeFlatCLE d n
            (1 : Equiv.Perm (Fin n)) '' U,
        Filter.Tendsto
          (BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n))))
          (nhdsWithin (SCV.realEmbed x)
            (BHW.os45FlatCommonChartOmega d n
              (P.τ.symm * (1 : Equiv.Perm (Fin n)))))
          (nhds (bvOut x)))
    (h414_integrals :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
          BHW.os45CommonEdgeFlatCLE d n
            (1 : Equiv.Perm (Fin n)) '' U →
        (∫ x : BHW.OS45FlatCommonChartReal d n, bvOut x * φ x) =
          ∫ x : BHW.OS45FlatCommonChartReal d n, bvIn x * φ x) :
    ∃ Ucx : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen Ucx ∧
      IsConnected Ucx ∧
      (∀ u ∈ U, (fun k => wickRotatePoint (u k)) ∈ Ucx) ∧
      (∀ u ∈ U,
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) ∈ Ucx) ∧
      ∃ Hdiff : (Fin n → Fin (d + 1) → ℂ) → ℂ,
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
  rcases
      BHW.os45Figure24_initialSectorOverlap_chartNeighborhood
        (d := d) (n := n) (hd := hd) (P := P)
        hU_compact hU_connected hU_closure with
    ⟨Ucx, hUcx_open, hUcx_connected, hwick_mem, hcommon_mem, hUcx_sub⟩
  let Hdiff : (Fin n → Fin (d + 1) → ℂ) → ℂ :=
    fun z =>
      BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) P.τ z) -
        BHW.extendF (bvt_F OS lgc n) z
  have hHdiff_holo : DifferentiableOn ℂ Hdiff Ucx := by
    have hFord :
        DifferentiableOn ℂ (BHW.extendF (bvt_F OS lgc n)) Ucx :=
      (BHW.differentiableOn_extendF_bvt_F_extendedTube
        (d := d) OS lgc n).mono (by
          intro z hz
          exact (hUcx_sub hz).1)
    have hFadj :
        DifferentiableOn ℂ
          (fun z : Fin n → Fin (d + 1) → ℂ =>
            BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) P.τ z)) Ucx :=
      (BHW.differentiableOn_extendF_bvt_F_permAct_preimageExtendedTube
        (d := d) OS lgc n P.τ).mono (by
          intro z hz
          simpa [BHW.permutedExtendedTubeSector] using (hUcx_sub hz).2)
    exact hFadj.sub hFord
  rcases hU_connected.nonempty with ⟨u0, hu0⟩
  have hU_sub : U ⊆ P.V := fun u hu => hU_closure (subset_closure hu)
  have hu0P : u0 ∈ P.V := hU_sub hu0
  let e := BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n))
  let E : Set (BHW.OS45FlatCommonChartReal d n) := e '' U
  let x0 : BHW.OS45FlatCommonChartReal d n := e u0
  let z0 : Fin n → Fin (d + 1) → ℂ :=
    (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
      (BHW.realEmbed
        (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
          (1 : Equiv.Perm (Fin n)) u0))
  have hz0Ucx : z0 ∈ Ucx := by
    simpa [z0] using hcommon_mem u0 hu0
  have hE_open : IsOpen E := by
    simpa [E, e] using e.toHomeomorph.isOpenMap U hU_open
  have hE_sub :
      E ⊆ BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)) := by
    rintro x ⟨u, huU, rfl⟩
    exact
      (BHW.os45CommonEdgeFlatCLE_mem_edgeSet_iff d n P
        (1 : Equiv.Perm (Fin n)) u).mpr (hU_sub huU)
  have hx0 : x0 ∈ E := ⟨u0, hu0, rfl⟩
  have hz0_flat :
      z0 =
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.unflattenCfg n d (SCV.realEmbed x0)) := by
    have hsource_zero :=
      BHW.os45FlatCommonChartSourceSide_zero_eq_commonEdge
        (d := d) (n := n)
        (1 : Equiv.Perm (Fin n)) (1 : ℝ)
        (0 : BHW.OS45FlatCommonChartReal d n) u0
    calc
      z0 =
          (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
            (BHW.realEmbed
              (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                (1 : Equiv.Perm (Fin n)) u0)) := rfl
      _ =
          BHW.os45FlatCommonChartSourceSide d n
            (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0
            (0 : BHW.OS45FlatCommonChartReal d n) u0 := hsource_zero.symm
      _ = (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.unflattenCfg n d (SCV.realEmbed x0)) := by
            have hreal :
                SCV.realEmbed x0 =
                  (fun a : Fin (BHW.os45FlatCommonChartDim d n) =>
                    ((x0) a : ℂ)) := rfl
            rw [hreal]
            ext k μ
            simp [BHW.os45FlatCommonChartSourceSide, e, x0]
  let CplusData :=
    H.ordinaryCommonEdge_ordModelAtZ0InWindow
      OS lgc hu0P hUcx_open hz0Ucx
  let Cplus : OS45PointedChart d n := Classical.choose CplusData
  have hCplus_spec := Classical.choose_spec CplusData
  let CminusData :=
    H.adjacentCommonEdge_minusModelAtZ0InWindow
      OS lgc hu0P hUcx_open hz0Ucx
  let Cminus : OS45PointedChart d n := Classical.choose CminusData
  have hCminus_spec := Classical.choose_spec CminusData
  have hzCplus_flat :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.unflattenCfg n d (SCV.realEmbed x0)) ∈
        Cplus.carrier := by
    rw [← hz0_flat]
    exact hCplus_spec.2.1.z0_mem
  have hzCminus : z0 ∈ Cminus.carrier := by
    rw [show z0 = Cminus.center by
      simpa [z0, Cminus] using hCminus_spec.1.symm]
    exact hCminus_spec.2.1
  have hzCminus_flat :
      (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.unflattenCfg n d (SCV.realEmbed x0)) ∈
        Cminus.carrier := by
    rw [← hz0_flat]
    exact hzCminus
  have hflat_edge_flat :
      PointedSeedEdge
        ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.unflattenCfg n d (SCV.realEmbed x0)))
        Cplus.carrier Cminus.carrier Cplus.branch Cminus.branch :=
    flat_realJost_EOW_pointed_seed_of_local414_integrals
      (d := d) hd OS lgc (P := P)
      (E := E) hE_open hE_sub x0 hx0 bvIn bvOut
      (by simpa [E, e] using hbvIn_cont)
      (by simpa [E, e] using hbvOut_cont)
      (by simpa [E, e] using hsideIn_bvIn)
      (by simpa [E, e] using hsideOut_bvOut)
      (by simpa [E, e] using h414_integrals)
      Cplus Cminus hzCplus_flat hzCminus_flat
      hCplus_spec.2.1.eq_ord hCminus_spec.2.2.1
  have hflat_edge :
      PointedSeedEdge z0
        Cplus.carrier Cminus.carrier Cplus.branch Cminus.branch := by
    simpa [hz0_flat] using hflat_edge_flat
  have hplus_minus_eq :
      Set.EqOn Cplus.branch Cminus.branch
        (Cplus.carrier ∩ Cminus.carrier) :=
    PointedMetricBranchChart.eqOn_inter_of_seed Cplus Cminus
      ⟨hflat_edge.W, hflat_edge.W_open, hflat_edge.z0_mem,
        hflat_edge.W_sub, hflat_edge.eqOn⟩
  let hdiff :=
    H.commonEdgeDifference_pointedChartInWindow
      OS lgc hu0P hUcx_open hz0Ucx
  let Adiff : OS45PointedChart d n := Classical.choose hdiff
  have hAdiff_spec := Classical.choose_spec hdiff
  have hAdiff_center : Adiff.center = z0 := by
    simpa [Adiff, z0] using hAdiff_spec.1
  have hzAdiff : z0 ∈ Adiff.carrier := by
    rw [← hAdiff_center]
    simpa [Adiff] using hAdiff_spec.2.1
  let S : Set (Fin n → Fin (d + 1) → ℂ) :=
    Adiff.carrier ∩ (Cplus.carrier ∩ Cminus.carrier)
  have hS_ne : S.Nonempty := by
    exact ⟨z0, by simpa [S] using
      ⟨hzAdiff, hCplus_spec.2.1.z0_mem, hzCminus⟩⟩
  have hS_open : IsOpen S :=
    Adiff.carrier_open.inter (Cplus.carrier_open.inter Cminus.carrier_open)
  have hS_sub : S ⊆ Ucx := by
    intro z hz
    exact (hAdiff_spec.2.2.1 hz.1).2
  have hAdiff_zero :
      Set.EqOn Adiff.branch (fun _ => 0) S := by
    intro z hz
    have hdiff_model := hAdiff_spec.2.2.2.1 hz.1
    have hplus_model := hCplus_spec.2.1.eq_ord hz.2.1
    have hminus_model := hCminus_spec.2.2.1 hz.2.2
    have hover := hplus_minus_eq ⟨hz.2.1, hz.2.2⟩
    have hminus_model' :
        BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z) =
          Cminus.branch z := by
      simpa [Cminus] using hminus_model.symm
    have hplus_model' :
        BHW.extendF (bvt_F OS lgc n) z = Cplus.branch z := by
      simpa [Cplus] using hplus_model.symm
    calc
      Adiff.branch z =
          BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d) P.τ z) -
            BHW.extendF (bvt_F OS lgc n) z := hdiff_model
      _ = Cminus.branch z - Cplus.branch z := by
            rw [hminus_model', hplus_model']
      _ = 0 := by
            rw [← hover]
            simp
  have hHdiff_zero_seed : Set.EqOn Hdiff (fun _ => 0) S := by
    intro z hz
    calc
      Hdiff z = Adiff.branch z := by
        exact (hAdiff_spec.2.2.2.1 hz.1).symm
      _ = 0 := hAdiff_zero hz
  have hHdiff_zero : Set.EqOn Hdiff (fun _ => 0) Ucx :=
    identity_theorem_product_of_eqOn_open
      hUcx_open hUcx_connected hS_open hS_ne hS_sub
      hHdiff_holo (differentiableOn_const (c := (0 : ℂ)))
      hHdiff_zero_seed
  refine
    ⟨Ucx, hUcx_open, hUcx_connected, hwick_mem, hcommon_mem,
      Hdiff, hHdiff_holo, ?_, ?_⟩
  · intro φ hφ_compact hφU
    calc
      ∫ u : NPointDomain d n,
          Hdiff (fun k => wickRotatePoint (u k)) * φ u
          = ∫ u : NPointDomain d n, (0 : ℂ) * φ u := by
            refine MeasureTheory.integral_congr_ae
              (Filter.Eventually.of_forall ?_)
            intro u
            by_cases hu : u ∈ U
            · simp [hHdiff_zero (hwick_mem u hu)]
            · have hφ_zero : φ u = 0 :=
                image_eq_zero_of_notMem_tsupport
                  (fun hφ_supp => hu (hφU hφ_supp))
              simp [hφ_zero]
      _ = 0 := by simp
  · intro u hu
    dsimp [Hdiff]
    rw [BHW.os45Figure24CommonEdge_permAct_extendF_eq_adjacentPulledRealBranch
      (d := d) (n := n) hd OS lgc (P := P) u]
    simp [BHW.os45PulledRealBranch]

/-- Local `(4.14)` compact-test boundary equality supplies the paper-facing
source-zero representation on the Figure-2-4 initial-overlap collar.

This is the direct Path-2 handoff from the actual OS-I local boundary packet to
`RepresentsDistributionOn 0`.  It deliberately leaves the remaining analytic
payload visible as `h414_integrals`; no compact Jost packet, selected-data
adapter, or deterministic transported Wick shortcut is used here. -/
theorem OS45BHWJostHullData.os45CommonEdge_sourceRepresentsZero_of_local414_integrals
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
    (hU_closure : closure U ⊆ P.V)
    (bvIn bvOut : BHW.OS45FlatCommonChartReal d n → ℂ)
    (hbvIn_cont :
      ContinuousOn bvIn
        (BHW.os45CommonEdgeFlatCLE d n
          (1 : Equiv.Perm (Fin n)) '' U))
    (hbvOut_cont :
      ContinuousOn bvOut
        (BHW.os45CommonEdgeFlatCLE d n
          (1 : Equiv.Perm (Fin n)) '' U))
    (hsideIn_bvIn :
      ∀ x ∈
          BHW.os45CommonEdgeFlatCLE d n
            (1 : Equiv.Perm (Fin n)) '' U,
        Filter.Tendsto
          (BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n)))
          (nhdsWithin (SCV.realEmbed x)
            (BHW.os45FlatCommonChartOmega d n
              (1 : Equiv.Perm (Fin n))))
          (nhds (bvIn x)))
    (hsideOut_bvOut :
      ∀ x ∈
          BHW.os45CommonEdgeFlatCLE d n
            (1 : Equiv.Perm (Fin n)) '' U,
        Filter.Tendsto
          (BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n))))
          (nhdsWithin (SCV.realEmbed x)
            (BHW.os45FlatCommonChartOmega d n
              (P.τ.symm * (1 : Equiv.Perm (Fin n)))))
          (nhds (bvOut x)))
    (h414_integrals :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
          BHW.os45CommonEdgeFlatCLE d n
            (1 : Equiv.Perm (Fin n)) '' U →
        (∫ x : BHW.OS45FlatCommonChartReal d n, bvOut x * φ x) =
          ∫ x : BHW.OS45FlatCommonChartReal d n, bvIn x * φ x) :
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
  classical
  rcases
      H.os45CommonEdge_localHdiffGerm_of_local414_integrals
        OS lgc hU_open hU_compact hU_connected hU_closure
        bvIn bvOut hbvIn_cont hbvOut_cont hsideIn_bvIn
        hsideOut_bvOut h414_integrals with
    ⟨Ucx, hUcx_open, hUcx_connected, hwick_mem, hcommon_mem,
      Hdiff, hHdiff_holo, hwick_pairing_zero, hcommon_trace⟩
  exact
    BHW.os45CommonEdge_localHorizontalDifference_representsZero_of_germ
      (d := d) hd OS lgc (P := P) U hU_open
      hU_connected.nonempty Ucx Hdiff hUcx_open hUcx_connected
      hwick_mem hcommon_mem hHdiff_holo hwick_pairing_zero hcommon_trace

/-- Source-pairing form of the local `(4.14)` handoff.

The remaining OS-I transport can feed this theorem directly: it only has to
prove equality of the two pulled real common-edge source pairings against the
cutoff-pulled flat tests on the current source window.  The proof below does
the checked source-to-flat change of variables, supplies the real-edge
continuity/side-limit fields, and then invokes the existing local EOW consumer.
-/
theorem OS45BHWJostHullData.os45CommonEdge_sourceRepresentsZero_of_sourcePairings
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
    (hU_closure : closure U ⊆ P.V)
    (D : BHW.OS45Figure24SourceCutoffData P)
    (hsource_pairings :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
          BHW.os45CommonEdgeFlatCLE d n
            (1 : Equiv.Perm (Fin n)) '' U →
        (∫ u : NPointDomain d n,
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin n)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u)) *
            (D.toSchwartzNPointCLM
              (1 : Equiv.Perm (Fin n)) φ : NPointDomain d n → ℂ) u) =
          ∫ u : NPointDomain d n,
            BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (1 : Equiv.Perm (Fin n))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u)) *
              (D.toSchwartzNPointCLM
                (1 : Equiv.Perm (Fin n)) φ : NPointDomain d n → ℂ) u) :
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
  classical
  let e := BHW.os45CommonEdgeFlatCLE d n (1 : Equiv.Perm (Fin n))
  let E : Set (BHW.OS45FlatCommonChartReal d n) := e '' U
  let bvIn : BHW.OS45FlatCommonChartReal d n → ℂ := fun x =>
    BHW.os45FlatCommonChartBranch d n OS lgc
      (1 : Equiv.Perm (Fin n)) (SCV.realEmbed x)
  let bvOut : BHW.OS45FlatCommonChartReal d n → ℂ := fun x =>
    BHW.os45FlatCommonChartBranch d n OS lgc
      (P.τ.symm * (1 : Equiv.Perm (Fin n))) (SCV.realEmbed x)
  have hU_sub : U ⊆ P.V := fun u hu => hU_closure (subset_closure hu)
  have hE_sub :
      E ⊆ BHW.os45FlatCommonChartEdgeSet d n P
        (1 : Equiv.Perm (Fin n)) := by
    rintro x ⟨u, huU, rfl⟩
    exact
      (BHW.os45CommonEdgeFlatCLE_mem_edgeSet_iff d n P
        (1 : Equiv.Perm (Fin n)) u).mpr (hU_sub huU)
  have hbvIn_cont : ContinuousOn bvIn E := by
    exact
      (BHW.continuousOn_os45FlatCommonChartBranch_realEdge
        (d := d) hd OS lgc (P := P)
        (1 : Equiv.Perm (Fin n)) (1 : Equiv.Perm (Fin n))
        (BHW.os45FlatCommonChart_real_mem_omega_id
          (d := d) hd (P := P))).mono hE_sub
  have hbvOut_cont : ContinuousOn bvOut E := by
    exact
      (BHW.continuousOn_os45FlatCommonChartBranch_realEdge
        (d := d) hd OS lgc (P := P)
        (P.τ.symm * (1 : Equiv.Perm (Fin n)))
        (1 : Equiv.Perm (Fin n))
        (BHW.os45FlatCommonChart_real_mem_omega_adjacent
          (d := d) hd (P := P))).mono hE_sub
  have hsideIn_bvIn :
      ∀ x ∈ E,
        Filter.Tendsto
          (BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n)))
          (nhdsWithin (SCV.realEmbed x)
            (BHW.os45FlatCommonChartOmega d n
              (1 : Equiv.Perm (Fin n))))
          (nhds (bvIn x)) := by
    intro x hx
    have hxΩ :
        SCV.realEmbed x ∈
          BHW.os45FlatCommonChartOmega d n
            (1 : Equiv.Perm (Fin n)) :=
      BHW.os45FlatCommonChart_real_mem_omega_id
        (d := d) hd (P := P) x (hE_sub hx)
    simpa [bvIn] using
      BHW.tendsto_os45FlatCommonChartBranch_realEdge
        (d := d) OS lgc (1 : Equiv.Perm (Fin n)) hxΩ
  have hsideOut_bvOut :
      ∀ x ∈ E,
        Filter.Tendsto
          (BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n))))
          (nhdsWithin (SCV.realEmbed x)
            (BHW.os45FlatCommonChartOmega d n
              (P.τ.symm * (1 : Equiv.Perm (Fin n)))))
          (nhds (bvOut x)) := by
    intro x hx
    have hxΩ :
        SCV.realEmbed x ∈
          BHW.os45FlatCommonChartOmega d n
            (P.τ.symm * (1 : Equiv.Perm (Fin n))) :=
      BHW.os45FlatCommonChart_real_mem_omega_adjacent
        (d := d) hd (P := P) x (hE_sub hx)
    simpa [bvOut] using
      BHW.tendsto_os45FlatCommonChartBranch_realEdge
        (d := d) OS lgc
        (P.τ.symm * (1 : Equiv.Perm (Fin n))) hxΩ
  have h414_integrals :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆ E →
        (∫ x : BHW.OS45FlatCommonChartReal d n, bvOut x * φ x) =
          ∫ x : BHW.OS45FlatCommonChartReal d n, bvIn x * φ x := by
    intro φ hφ_compact hφE
    have hφEdge :
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
          BHW.os45FlatCommonChartEdgeSet d n P
            (1 : Equiv.Perm (Fin n)) :=
      hφE.trans hE_sub
    have hAdj :=
      BHW.os45FlatCommonChart_adjacentCommonBoundary_integral_eq_sourcePullback
        (d := d) hd OS lgc (P := P) D φ hφ_compact hφEdge
    have hOrd :=
      BHW.os45FlatCommonChart_ordinaryCommonBoundary_integral_eq_sourcePullback
        (d := d) hd OS lgc (P := P) D φ hφ_compact hφEdge
    have hsrc := hsource_pairings φ hφ_compact (by simpa [E] using hφE)
    calc
      ∫ x : BHW.OS45FlatCommonChartReal d n, bvOut x * φ x
          =
        ∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (P.τ.symm * (1 : Equiv.Perm (Fin n)))
            (fun a => (x a : ℂ)) * φ x := by
            rfl
      _ =
        (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) *
          ∫ u : NPointDomain d n,
            BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin n)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u)) *
              (D.toSchwartzNPointCLM
                (1 : Equiv.Perm (Fin n)) φ : NPointDomain d n → ℂ) u :=
          hAdj
      _ =
        (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) *
          ∫ u : NPointDomain d n,
            BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
              (1 : Equiv.Perm (Fin n))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u)) *
              (D.toSchwartzNPointCLM
                (1 : Equiv.Perm (Fin n)) φ : NPointDomain d n → ℂ) u := by
            exact congrArg
              (fun I : ℂ => (BHW.os45CommonEdgeFlatJacobianAbs n : ℂ) * I)
              hsrc
      _ =
        ∫ x : BHW.OS45FlatCommonChartReal d n,
          BHW.os45FlatCommonChartBranch d n OS lgc
            (1 : Equiv.Perm (Fin n)) (fun a => (x a : ℂ)) * φ x :=
          hOrd.symm
      _ = ∫ x : BHW.OS45FlatCommonChartReal d n, bvIn x * φ x := by
            rfl
  exact
    H.os45CommonEdge_sourceRepresentsZero_of_local414_integrals
      OS lgc hU_open hU_compact hU_connected hU_closure
      bvIn bvOut hbvIn_cont hbvOut_cont hsideIn_bvIn
      hsideOut_bvOut (by simpa [E] using h414_integrals)

/-- Compact Jost-edge equality supplies the active transported Wick pairing.

This is the monograph part-(b) bridge in local Figure-2-4 form: once the
compact-test equality is known on a real Jost edge for the adjacent
transposition, the existing BHW overlap identity theorem propagates it through
the connected `T'_n ∩ τ T'_n` overlap.  Evaluating that overlap equality on the
ordinary Wick section gives exactly the deterministic adjacent branch pairing
consumed by `os45CommonEdge_localHdiffGerm_of_initialOverlap_adjacentBranch`.
-/
theorem os45CommonEdge_transported_wick_pairing_of_compactFigure24WickPairingEq
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (hOverlap :
      IsConnected
        {z : Fin n → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d n ∧
            BHW.permAct (d := d) P.τ z ∈ BHW.ExtendedTube d n})
    (hCompact :
      BHW.OS45CompactFigure24WickPairingEq (d := d) n i hi OS lgc)
    {U : Set (NPointDomain d n)}
    (hU_sub : U ⊆ P.V) :
    ∀ φ : SchwartzNPoint d n,
      HasCompactSupport (φ : NPointDomain d n → ℂ) →
      tsupport (φ : NPointDomain d n → ℂ) ⊆ U →
      ∫ u : NPointDomain d n,
        BHW.extendF (bvt_F OS lgc n)
          (BHW.permAct (d := d) P.τ
            (fun k => wickRotatePoint (u k))) * φ u =
      ∫ u : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (u k)) * φ u := by
  classical
  have hF_holo :
      DifferentiableOn ℂ (bvt_F OS lgc n) (BHW.ForwardTube d n) := by
    simpa [BHW_forwardTube_eq (d := d) (n := n)] using
      bvt_F_holomorphic (d := d) OS lgc n
  have hF_lorentz :
      ∀ (Λ : LorentzLieGroup.RestrictedLorentzGroup d)
        (z : Fin n → Fin (d + 1) → ℂ), z ∈ BHW.ForwardTube d n →
        bvt_F OS lgc n
          (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) =
        bvt_F OS lgc n z := by
    intro Λ z hz
    exact bvt_F_restrictedLorentzInvariant_forwardTube
      (d := d) OS lgc n Λ z
      ((BHW_forwardTube_eq (d := d) (n := n)) ▸ hz)
  have hV_ET :
      ∀ x ∈ hCompact.realPatch 1,
        BHW.realEmbed x ∈ BHW.ExtendedTube d n := by
    intro x hx
    simpa [BHW.permutedExtendedTubeSector] using
      hCompact.realPatch_left_sector 1 x hx
  have hV_permET :
      ∀ x ∈ hCompact.realPatch 1,
        BHW.realEmbed (fun k => x (P.τ k)) ∈ BHW.ExtendedTube d n := by
    intro x hx
    have hxright := hCompact.realPatch_right_sector 1 x hx
    simpa [BHW.permutedExtendedTubeSector, P.τ_eq, BHW.realEmbed,
      Equiv.Perm.mul_apply] using hxright
  have hEdge :
      ∀ φ : SchwartzNPoint d n,
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ hCompact.realPatch 1 →
        ∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.realEmbed (fun k => x (P.τ k))) * φ x =
        ∫ x : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n) (BHW.realEmbed x) * φ x := by
    intro φ hφ_compact hφ_supp
    have h := hCompact.compact_branch_eq 1 φ hφ_compact hφ_supp
    simpa [P.τ_eq, BHW.realEmbed, Equiv.Perm.mul_apply] using h.symm
  have hOverlap_eq :
      ∀ z : Fin n → Fin (d + 1) → ℂ,
        z ∈ BHW.ExtendedTube d n →
        BHW.permAct (d := d) P.τ z ∈ BHW.ExtendedTube d n →
        BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ z) =
          BHW.extendF (bvt_F OS lgc n) z :=
    BHW.extendF_perm_overlap_of_edgePairingEquality
      (d := d) n (bvt_F OS lgc n) hF_holo hF_lorentz P.τ
      hOverlap (hCompact.realPatch 1) (hCompact.realPatch_open 1)
      (hCompact.realPatch_nonempty 1) hV_ET hV_permET hEdge
  intro φ _hφ_compact hφU
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro u
  by_cases hu : u ∈ U
  · have huP : u ∈ P.V := hU_sub hu
    let z : Fin n → Fin (d + 1) → ℂ := fun k => wickRotatePoint (u k)
    have hforward : z ∈ BHW.ForwardTube d n :=
      BHW.os45Figure24_ordinaryWick_mem_forwardTube
        (d := d) (n := n) (hd := hd) (P := P) huP
    have hz_ET : z ∈ BHW.ExtendedTube d n :=
      BHW.forwardTube_subset_extendedTube hforward
    have hτz_ET :
        BHW.permAct (d := d) P.τ z ∈ BHW.ExtendedTube d n := by
      simpa [z] using
        BHW.os45Figure24_adjacentWick_mem_extendedTube
          (d := d) (n := n) (hd := hd) (P := P) huP
    have heq := hOverlap_eq z hz_ET hτz_ET
    have hext :
        BHW.extendF (bvt_F OS lgc n) z =
          bvt_F OS lgc n z :=
      BHW.extendF_eq_on_forwardTube n (bvt_F OS lgc n)
        hF_holo hF_lorentz z hforward
    exact congrArg (fun c : ℂ => c * φ u) (heq.trans hext)
  · have hφ_zero : φ u = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun hφ_supp => hu (hφU hφ_supp))
    simp [hφ_zero]

/-- Initial-overlap ordinary branch data plus the concrete transported adjacent
Wick pairing give the active local horizontal difference germ.

This is a Path-2 proof-body assembly step, not a new theorem-2 input gate.  The
ordinary branch, the concrete deterministic adjacent branch
`extendF ∘ permAct P.τ`, and both common-edge traces are supplied by the checked
Figure-2-4 initial-overlap chart.  The remaining analytic payload is now the
paper's actual `(4.12)` seed-to-Wick compact-test transport for that concrete
adjacent branch; after that pairing is supplied, the proof packages the genuine
horizontal difference germ `Fadj - Ford`, whose Wick-section pairing vanishes and
whose common-edge trace is adjacent-minus-ordinary. -/
theorem os45CommonEdge_localHdiffGerm_of_initialOverlap_adjacentBranch
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {U : Set (NPointDomain d n)}
    (hU_open : IsOpen U)
    (hU_compact : IsCompact (closure U))
    (hU_connected : IsConnected U)
    (hU_closure : closure U ⊆ P.V)
    (htransported_wick_pairing :
      ∀ φ : SchwartzNPoint d n,
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ U →
        ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ
              (fun k => wickRotatePoint (u k))) * φ u =
        ∫ u : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (u k)) * φ u) :
    ∃ Ucx : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen Ucx ∧
      IsConnected Ucx ∧
      (∀ u ∈ U, (fun k => wickRotatePoint (u k)) ∈ Ucx) ∧
      (∀ u ∈ U,
        (BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u)) ∈ Ucx) ∧
      ∃ Hdiff : (Fin n → Fin (d + 1) → ℂ) → ℂ,
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
  rcases
      BHW.os45CommonEdge_initialSectorOverlap_traces_except_adjacentWick
        (d := d) hd OS lgc (P := P)
        (U := U) hU_compact hU_connected hU_closure with
    ⟨Ucx, Ford, Fadj, hUcx_open, htail⟩
  rcases htail with ⟨hUcx_connected, htail⟩
  rcases htail with ⟨hwick_mem, htail⟩
  rcases htail with ⟨hcommon_mem, htail⟩
  rcases htail with ⟨_hUcx_sub, htail⟩
  rcases htail with ⟨hFord_holo, htail⟩
  rcases htail with ⟨hFadj_holo, htail⟩
  rcases htail with ⟨hFord_wick, htail⟩
  rcases htail with ⟨hFadj_wick_extendF, htail⟩
  rcases htail with ⟨hFord_common, htail⟩
  rcases htail with ⟨hFadj_common, _hFadj0_seed_trace⟩
  have hwick_pairing :
      ∀ φ : SchwartzNPoint d n,
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ U →
        ∫ u : NPointDomain d n,
          Fadj (fun k => wickRotatePoint (u k)) * φ u =
        ∫ u : NPointDomain d n,
          Ford (fun k => wickRotatePoint (u k)) * φ u := by
    intro φ hφ_compact hφU
    calc
      ∫ u : NPointDomain d n,
          Fadj (fun k => wickRotatePoint (u k)) * φ u =
        ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ
              (fun k => wickRotatePoint (u k))) * φ u := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
          intro u
          by_cases hu : u ∈ U
          · exact congrArg (fun c : ℂ => c * φ u)
              (hFadj_wick_extendF u hu)
          · have hφ_zero : φ u = 0 :=
              image_eq_zero_of_notMem_tsupport
                (fun hφ_supp => hu (hφU hφ_supp))
            simp [hφ_zero]
      _ =
        ∫ u : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (u k)) * φ u :=
          htransported_wick_pairing φ hφ_compact hφU
      _ =
        ∫ u : NPointDomain d n,
          Ford (fun k => wickRotatePoint (u k)) * φ u := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
          intro u
          by_cases hu : u ∈ U
          · exact congrArg (fun c : ℂ => c * φ u) (hFord_wick u hu).symm
          · have hφ_zero : φ u = 0 :=
              image_eq_zero_of_notMem_tsupport
                (fun hφ_supp => hu (hφU hφ_supp))
            simp [hφ_zero]
  let Hdiff : (Fin n → Fin (d + 1) → ℂ) → ℂ := fun z => Fadj z - Ford z
  have hHdiff_holo : DifferentiableOn ℂ Hdiff Ucx :=
    hFadj_holo.sub hFord_holo
  refine
    ⟨Ucx, hUcx_open, hUcx_connected, hwick_mem, hcommon_mem,
      Hdiff, hHdiff_holo, ?_, ?_⟩
  · intro φ hφ_compact hφU
    let wick : NPointDomain d n → Fin n → Fin (d + 1) → ℂ :=
      fun u => fun k => wickRotatePoint (u k)
    have hwick_cont : Continuous wick := by
      simpa [wick] using BHW.continuous_wickRotateRealConfig (d := d) (n := n)
    have hFadj_cont :
        ContinuousOn (fun u : NPointDomain d n => Fadj (wick u)) U := by
      exact hFadj_holo.continuousOn.comp hwick_cont.continuousOn
        (by intro u hu; simpa [wick] using hwick_mem u hu)
    have hFord_cont :
        ContinuousOn (fun u : NPointDomain d n => Ford (wick u)) U := by
      exact hFord_holo.continuousOn.comp hwick_cont.continuousOn
        (by intro u hu; simpa [wick] using hwick_mem u hu)
    have hFadj_int :
        Integrable
          (fun u : NPointDomain d n => Fadj (wick u) * φ u) :=
      SCV.integrable_continuousOn_mul_schwartz_of_supportsInOpen
        (H := fun u : NPointDomain d n => Fadj (wick u))
        (ψ := φ) (U := U) hU_open hFadj_cont
        ⟨hφ_compact, hφU⟩
    have hFord_int :
        Integrable
          (fun u : NPointDomain d n => Ford (wick u) * φ u) :=
      SCV.integrable_continuousOn_mul_schwartz_of_supportsInOpen
        (H := fun u : NPointDomain d n => Ford (wick u))
        (ψ := φ) (U := U) hU_open hFord_cont
        ⟨hφ_compact, hφU⟩
    calc
      ∫ u : NPointDomain d n, Hdiff (fun k => wickRotatePoint (u k)) * φ u
          =
        ∫ u : NPointDomain d n,
          Fadj (wick u) * φ u - Ford (wick u) * φ u := by
            refine MeasureTheory.integral_congr_ae
              (Filter.Eventually.of_forall ?_)
            intro u
            simp [Hdiff, wick, sub_mul]
      _ =
        (∫ u : NPointDomain d n, Fadj (wick u) * φ u) -
          ∫ u : NPointDomain d n, Ford (wick u) * φ u :=
            MeasureTheory.integral_sub hFadj_int hFord_int
      _ = 0 := by
            rw [hwick_pairing φ hφ_compact hφU]
            exact sub_self _
  · intro u hu
    change
      Fadj
        ((BHW.os45QuarterTurnCLE (d := d) (n := n)).symm
          (BHW.realEmbed
            (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
              (1 : Equiv.Perm (Fin n)) u))) -
        Ford
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
                (1 : Equiv.Perm (Fin n)) u))
    rw [hFadj_common u hu, hFord_common u hu]

/-- The active source-representation handoff from the concrete OS-I adjacent
branch transport.

Once the `(4.12)` seed-to-Wick compact-test transport has supplied the
deterministic adjacent branch pairing used by
`os45CommonEdge_localHdiffGerm_of_initialOverlap_adjacentBranch`, the checked
horizontal difference germ immediately represents the zero source
distribution on the same collar.  This keeps the theorem-2 Path 2 input in the
paper-facing `RepresentsDistributionOn 0` form and leaves the remaining
analytic leaf as exactly the transported Wick pairing hypothesis below. -/
theorem os45CommonEdge_sourceRepresentsZero_of_initialOverlap_adjacentBranch
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    {U : Set (NPointDomain d n)}
    (hU_open : IsOpen U)
    (hU_compact : IsCompact (closure U))
    (hU_connected : IsConnected U)
    (hU_closure : closure U ⊆ P.V)
    (htransported_wick_pairing :
      ∀ φ : SchwartzNPoint d n,
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ U →
        ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ
              (fun k => wickRotatePoint (u k))) * φ u =
        ∫ u : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (u k)) * φ u) :
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
  classical
  rcases
      BHW.os45CommonEdge_localHdiffGerm_of_initialOverlap_adjacentBranch
        (d := d) hd OS lgc (P := P) hU_open hU_compact
        hU_connected hU_closure htransported_wick_pairing with
    ⟨Ucx, hUcx_open, hUcx_connected, hwick_mem, hcommon_mem,
      Hdiff, hHdiff_holo, hwick_pairing_zero, hcommon_trace⟩
  exact
    BHW.os45CommonEdge_localHorizontalDifference_representsZero_of_germ
      (d := d) hd OS lgc (P := P) U hU_open
      hU_connected.nonempty Ucx Hdiff hUcx_open hUcx_connected
      hwick_mem hcommon_mem hHdiff_holo hwick_pairing_zero hcommon_trace

/-- Production entry for the OS-I `(4.12)`--`(4.14)` source-side transport.

The live proof body is the monograph part-(b) common-edge step: prove equality
of the two pulled real source pairings on the local Figure-2-4 Jost collar, then
feed that equality through the checked source-representation/Hdiff envelope. -/
theorem OS45BHWJostHullData.os45CommonEdge_sourceRepresentsZero_of_OS412_sourceSide
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
    (hU_closure : closure U ⊆ P.V)
    (D : BHW.OS45Figure24SourceCutoffData P) :
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
  classical
  have hsource_pairings :
      ∀ φ : SchwartzMap (BHW.OS45FlatCommonChartReal d n) ℂ,
        HasCompactSupport
          (φ : BHW.OS45FlatCommonChartReal d n → ℂ) →
        tsupport (φ : BHW.OS45FlatCommonChartReal d n → ℂ) ⊆
          BHW.os45CommonEdgeFlatCLE d n
            (1 : Equiv.Perm (Fin n)) '' U →
        (∫ u : NPointDomain d n,
          BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
              (P.τ.symm * (1 : Equiv.Perm (Fin n)))
              (BHW.realEmbed
                (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                  (1 : Equiv.Perm (Fin n)) u)) *
            (D.toSchwartzNPointCLM
              (1 : Equiv.Perm (Fin n)) φ : NPointDomain d n → ℂ) u) =
          ∫ u : NPointDomain d n,
            BHW.os45PulledRealBranch (d := d) (n := n) OS lgc
                (1 : Equiv.Perm (Fin n))
                (BHW.realEmbed
                  (BHW.os45CommonEdgeRealPoint (d := d) (n := n)
                    (1 : Equiv.Perm (Fin n)) u)) *
              (D.toSchwartzNPointCLM
                (1 : Equiv.Perm (Fin n)) φ : NPointDomain d n → ℂ) u := by
    intro φ hφ_compact hφU
    let τside : Equiv.Perm (Fin n) :=
      (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm
    let Ωplus : Set (Fin n → Fin (d + 1) → ℂ) :=
      BHW.ExtendedTube d n
    let Ωminus : Set (Fin n → Fin (d + 1) → ℂ) :=
      {z | BHW.permAct (d := d) τside z ∈ BHW.ExtendedTube d n}
    have hΩplus_open : IsOpen Ωplus := by
      simpa [Ωplus] using BHW.isOpen_extendedTube (d := d) (n := n)
    have hΩminus_open : IsOpen Ωminus := by
      simpa [Ωminus, τside] using
        BHW.isOpen_permAct_preimage_extendedTube
          (d := d) (n := n) τside
    have hFplus_cont :
        ContinuousOn
          (fun z : Fin n → Fin (d + 1) → ℂ =>
            BHW.extendF (bvt_F OS lgc n) z) Ωplus := by
      simpa [Ωplus] using
        (BHW.differentiableOn_extendF_bvt_F_extendedTube
          (d := d) OS lgc n).continuousOn
    have hFminus_cont :
        ContinuousOn
          (fun z : Fin n → Fin (d + 1) → ℂ =>
            BHW.extendF (bvt_F OS lgc n)
              (BHW.permAct (d := d)
                (P.τ.symm * (1 : Equiv.Perm (Fin n))).symm z)) Ωminus := by
      simpa [Ωminus, τside] using
        (BHW.differentiableOn_extendF_bvt_F_permAct_preimageExtendedTube
          (d := d) OS lgc n τside).continuousOn
    have hn_pos : 0 < n := by omega
    haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn_pos⟩
    rcases BHW.os45FlatCommonChartCone_eowReady d n with
      ⟨_hC_open, _hC_convex, _hC_connected, _hC_smul, hC_nonempty⟩
    rcases hC_nonempty with ⟨η, hηC⟩
    have h0_plus :
        ∀ u ∈ closure U,
          BHW.os45FlatCommonChartSourceSide d n
            (1 : Equiv.Perm (Fin n)) (1 : ℝ) 0 η u ∈ Ωplus := by
      intro u hu
      have hinit :
          BHW.os45Figure24IdentityPath (d := d) (n := n)
              u (1 : unitInterval) ∈
            BHW.ExtendedTube d n ∩
              BHW.permutedExtendedTubeSector d n P.τ :=
        BHW.os45Figure24IdentityPath_mem_initialSectorOverlap
          (d := d) (n := n) (hd := hd) (P := P)
          (subset_closure (hU_closure hu)) (1 : unitInterval)
      rw [BHW.os45FlatCommonChartSourceSide_zero_eq_identityPath_one]
      simpa [Ωplus] using hinit.1
    have h0_minus :
        ∀ u ∈ closure U,
          BHW.os45FlatCommonChartSourceSide d n
            (1 : Equiv.Perm (Fin n)) (-1 : ℝ) 0 η u ∈ Ωminus := by
      intro u hu
      have hinit :
          BHW.os45Figure24IdentityPath (d := d) (n := n)
              u (1 : unitInterval) ∈
            BHW.ExtendedTube d n ∩
              BHW.permutedExtendedTubeSector d n P.τ :=
        BHW.os45Figure24IdentityPath_mem_initialSectorOverlap
          (d := d) (n := n) (hd := hd) (P := P)
          (subset_closure (hU_closure hu)) (1 : unitInterval)
      rw [BHW.os45FlatCommonChartSourceSide_zero_eq_identityPath_one]
      simpa [Ωminus, τside, BHW.permutedExtendedTubeSector] using hinit.2
    refine
      D.sourcePairing_of_tendsto_sourceSide_extendF_difference_zero
        (d := d) OS lgc hΩplus_open hΩminus_open
        hFplus_cont hFminus_cont hU_open subset_closure hU_compact
        η h0_plus h0_minus φ hφ_compact hφU ?_
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
    let Fext : ℝ → ℂ := fun ε =>
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
              SchwartzNPoint d n) : NPointDomain d n → ℂ) u)
    let Fcur : ℝ → ℂ := fun ε =>
      (∫ u : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (u k)) *
          ((((D.toSideZeroDiagonalCLM
            (1 : Equiv.Perm (Fin n)) (1 : ℝ) ε η φ).1 :
              SchwartzNPoint d n) : NPointDomain d n → ℂ) u)) -
      ∫ u : NPointDomain d n,
        bvt_F OS lgc n (fun k => wickRotatePoint (u (P.τ k))) *
          ((((D.toSideZeroDiagonalCLM
            (1 : Equiv.Perm (Fin n)) (-1 : ℝ) ε η φ).1 :
              SchwartzNPoint d n) : NPointDomain d n → ℂ) u)
    have hside_ext :
        Tendsto Fext (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
      have hsource_current :
          Tendsto Fcur (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
        dsimp only [Fcur]
        exact
        D.sourceSide_ordinaryPlus_adjacentMinus_difference_tendsto_zero
          OS lgc η hηC φ hφ_compact hφE
      /-
        OS-I `(4.12)`--`(4.14)` Wick-section transport leaf.

        The source-current side of the paper proof is already formalized in
        `hsource_current`: Euclidean permutation symmetry makes the ordinary
        plus and adjacent minus source tests have the same Schwinger limit.
        The remaining production step is not finite-height eventual equality:
        it is the boundary-value transport saying that the deterministic
        source-side branch pairings in `Fext` and the Wick-section source
        currents in `Fcur` have asymptotically the same compact-test limit.
      -/
      have htransport :
          Tendsto (fun ε : ℝ => Fext ε - Fcur ε)
            (𝓝[Set.Ioi 0] (0 : ℝ)) (𝓝 0) := by
        /-
          Active OS-I `(4.12)`--`(4.14)` transport body.

          The endpoint equality shortcut above would require pointwise
          common-edge equality before the EOW/partition argument has produced
          it.  The remaining task is instead the compact-test source-side
          transport: cover the source support by local pointed charts, use the
          OS-I Jost/EOW seed equality on each chart, and combine the fixed-test
          partition limit with the moving-test error estimates for
          `D.toSideZeroDiagonalCLM`.
        -/
        exact ?os45_OS412_sourceSide_boundary_transport_compact_test
      have hsum := htransport.add hsource_current
      simpa [sub_eq_add_neg] using hsum
    simpa [Fext] using hside_ext
  exact
    H.os45CommonEdge_sourceRepresentsZero_of_sourcePairings
      OS lgc hU_open hU_compact hU_connected hU_closure
      D hsource_pairings

/-- Compact Figure-2-4 edge equality supplies the active source-zero
representation on a local initial-overlap collar.

This is only the checked Path-2 handoff from the monograph compact Jost-edge
packet to the source-side zero representation consumed downstream.  It keeps
the remaining mathematical input visible as `OS45CompactFigure24WickPairingEq`;
the producer of that compact packet is still the OS-I `(4.12)`--`(4.14)`
branch/source construction. -/
theorem os45CommonEdge_sourceRepresentsZero_of_compactFigure24WickPairingEq
    [NeZero d] (hd : 2 ≤ d)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n : ℕ} {i : Fin n} {hi : i.val + 1 < n}
    {P : BHW.OS45Figure24CanonicalSourcePatchData
      (d := d) hd n i hi}
    (hOverlap :
      IsConnected
        {z : Fin n → Fin (d + 1) → ℂ |
          z ∈ BHW.ExtendedTube d n ∧
            BHW.permAct (d := d) P.τ z ∈ BHW.ExtendedTube d n})
    (hCompact :
      BHW.OS45CompactFigure24WickPairingEq (d := d) n i hi OS lgc)
    {U : Set (NPointDomain d n)}
    (hU_open : IsOpen U)
    (hU_compact : IsCompact (closure U))
    (hU_connected : IsConnected U)
    (hU_closure : closure U ⊆ P.V) :
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
  classical
  have hU_sub : U ⊆ P.V := fun u hu => hU_closure (subset_closure hu)
  have htransported :
      ∀ φ : SchwartzNPoint d n,
        HasCompactSupport (φ : NPointDomain d n → ℂ) →
        tsupport (φ : NPointDomain d n → ℂ) ⊆ U →
        ∫ u : NPointDomain d n,
          BHW.extendF (bvt_F OS lgc n)
            (BHW.permAct (d := d) P.τ
              (fun k => wickRotatePoint (u k))) * φ u =
        ∫ u : NPointDomain d n,
          bvt_F OS lgc n (fun k => wickRotatePoint (u k)) * φ u :=
    BHW.os45CommonEdge_transported_wick_pairing_of_compactFigure24WickPairingEq
      (d := d) hd OS lgc (P := P) hOverlap hCompact hU_sub
  exact
    BHW.os45CommonEdge_sourceRepresentsZero_of_initialOverlap_adjacentBranch
      (d := d) hd OS lgc (P := P) hU_open hU_compact
      hU_connected hU_closure htransported

/-- Legacy selected-data adapter for the local Figure-2-4 common-edge
holomorphic difference germ.

Route guard: this adapter requires selected Jost/Ruelle data and delegates to
`os45_hdiff_of_selectedJostData`.  It is retained only as a checked diagnostic
surface.  The theorem-2/E-to-R frontier must use the direct OS-I
`(4.12)`--`(4.14)` moving-source Hdiff proof body instead of this route, so the
name deliberately includes `selectedJostData_legacy`. -/
theorem os45CommonEdge_localFigure24DifferenceGerm_of_selectedJostData_legacy
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
