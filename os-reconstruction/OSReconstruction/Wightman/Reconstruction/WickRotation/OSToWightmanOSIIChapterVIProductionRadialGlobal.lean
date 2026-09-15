import Mathlib.Analysis.Complex.OperatorNorm
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIProductionRadialOperatorNorm

/-!
# OS II Chapter VI: global normalized production radial Gevrey bounds

The actual inner-product bump is globally smooth. Its annular Gevrey operator
estimate extends across both flat regions and transition boundaries, and its
exact normalized production density has inverse-radius degree `2 * q + n`.
-/

noncomputable section

open Complex Topology
open scoped BigOperators Classical

namespace OSReconstruction

def osiiProductionRealRadialProfile
    {m : Nat} (v : Fin m → Real) : Complex :=
  ((ContDiffBumpBase.ofInnerProductSpace
    (EuclideanSpace Real (Fin m))).toFun 2
      ((PiLp.continuousLinearEquiv 2 Real
        (fun _ : Fin m => Real)).symm v) : Complex)

theorem osiiProductionRealRadialProfile_apply
    {m : Nat} (v : Fin m → Real) :
    osiiProductionRealRadialProfile v =
      (Real.smoothTransition
        (2 - ‖(PiLp.continuousLinearEquiv 2 Real
          (fun _ : Fin m => Real)).symm v‖) : Complex) := by
  norm_num [osiiProductionRealRadialProfile,
    ContDiffBumpBase.ofInnerProductSpace]

theorem osiiProductionRealRadialProfile_contDiff
    (m : Nat) :
    ContDiff Real (⊤ : ℕ∞)
      (osiiProductionRealRadialProfile (m := m)) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  have hbase :
      ContDiffAt Real (⊤ : ℕ∞)
        (Function.uncurry
          (ContDiffBumpBase.ofInnerProductSpace
            (EuclideanSpace Real (Fin m))).toFun)
        ((2 : Real),
          (PiLp.continuousLinearEquiv 2 Real
            (fun _ : Fin m => Real)).symm v) :=
    (ContDiffBumpBase.ofInnerProductSpace
      (EuclideanSpace Real (Fin m))).smooth.contDiffAt
        (prod_mem_nhds (Ioi_mem_nhds (by norm_num)) Filter.univ_mem)
  have hpair :
      ContDiffAt Real (⊤ : ℕ∞)
        (fun w : Fin m → Real =>
          ((2 : Real),
            (PiLp.continuousLinearEquiv 2 Real
              (fun _ : Fin m => Real)).symm w)) v := by
    fun_prop
  have hreal :
      ContDiffAt Real (⊤ : ℕ∞)
        (fun w : Fin m → Real =>
          (ContDiffBumpBase.ofInnerProductSpace
            (EuclideanSpace Real (Fin m))).toFun 2
            ((PiLp.continuousLinearEquiv 2 Real
              (fun _ : Fin m => Real)).symm w)) v := by
    convert hbase.comp v hpair using 1
    funext w
    rfl
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp v hreal

theorem osiiProductionRealRadialSlice_eq_profile_sub
    {m : Nat} (x : EuclideanSpace Real (Fin m)) (v : Fin m → Real) :
    osiiProductionRealRadialSlice x v =
      osiiProductionRealRadialProfile ((fun i => x i) + v) -
        osiiProductionRadialAnnulusBaseline x := by
  rw [osiiProductionRealRadialProfile_apply]
  rfl

theorem osiiProductionRealRadialProfile_iteratedFDeriv_eq_slice
    {m : Nat} (x : EuclideanSpace Real (Fin m))
    (n : Nat) (hn : n ≠ 0) :
    iteratedFDeriv Real n (osiiProductionRealRadialSlice x) 0 =
      iteratedFDeriv Real n osiiProductionRealRadialProfile
        (fun i => x i) := by
  let a : Fin m → Real := fun i => x i
  have hslice :
      osiiProductionRealRadialSlice x =
        (fun v => osiiProductionRealRadialProfile (a + v)) -
          fun _ => osiiProductionRadialAnnulusBaseline x := by
    funext v
    exact osiiProductionRealRadialSlice_eq_profile_sub x v
  have hshift :
      ContDiff Real (⊤ : ℕ∞)
        (fun v : Fin m → Real =>
          osiiProductionRealRadialProfile (a + v)) :=
    (osiiProductionRealRadialProfile_contDiff m).comp
      (contDiff_const.add contDiff_id)
  rw [hslice, iteratedFDeriv_sub_apply
    (hshift.contDiffAt.of_le (by exact_mod_cast le_top))
    (contDiffAt_const (c := osiiProductionRadialAnnulusBaseline x)),
    iteratedFDeriv_const_of_ne hn, Pi.zero_apply, sub_zero,
    iteratedFDeriv_comp_add_left, add_zero]

theorem osiiProductionRealRadialProfile_annulus_gevrey_bound
    {m : Nat}
    (x : EuclideanSpace Real (Fin (m + 1)))
    (hx_lower : 1 < ‖x‖) (hx_upper : ‖x‖ < 2)
    (n : Nat) (hn : n ≠ 0) :
    ‖iteratedFDeriv Real n osiiProductionRealRadialProfile
        (fun i => x i)‖ ≤
      Real.exp 6 *
        (98304 * ((m + 1 : Nat) : Real) ^ 2) ^ n *
          (n.factorial : Real) ^ 2 := by
  rw [← osiiProductionRealRadialProfile_iteratedFDeriv_eq_slice x n hn]
  exact osiiProductionRealRadialBump_iteratedFDeriv_gevrey_bound
    x hx_lower hx_upper n

theorem osiiProductionRealRadialProfile_iteratedFDeriv_zero_of_norm_lt_one
    {m : Nat} (v : Fin m → Real) (n : Nat) (hn : n ≠ 0)
    (hv : ‖(PiLp.continuousLinearEquiv 2 Real
      (fun _ : Fin m => Real)).symm v‖ < 1) :
    iteratedFDeriv Real n osiiProductionRealRadialProfile v = 0 := by
  let e := (PiLp.continuousLinearEquiv 2 Real
    (fun _ : Fin m => Real)).symm
  have hnorm : Continuous (fun w : Fin m → Real => ‖e w‖) :=
    continuous_norm.comp e.continuous
  have hnear :
      ∀ᶠ w : Fin m → Real in 𝓝 v, ‖e w‖ < 1 :=
    (isOpen_Iio.preimage hnorm).mem_nhds hv
  have hlocal :
      osiiProductionRealRadialProfile =ᶠ[𝓝 v]
        fun _ : Fin m → Real => (1 : Complex) := by
    filter_upwards [hnear] with w hw
    rw [osiiProductionRealRadialProfile_apply,
      Real.smoothTransition.one_of_one_le (by linarith)]
    norm_num
  have heq :=
    (Filter.EventuallyEq.iteratedFDeriv (𝕜 := Real) hlocal n).eq_of_nhds
  rw [heq, iteratedFDeriv_const_of_ne hn, Pi.zero_apply]

theorem osiiProductionRealRadialProfile_iteratedFDeriv_zero_of_two_lt_norm
    {m : Nat} (v : Fin m → Real) (n : Nat) (hn : n ≠ 0)
    (hv : 2 < ‖(PiLp.continuousLinearEquiv 2 Real
      (fun _ : Fin m => Real)).symm v‖) :
    iteratedFDeriv Real n osiiProductionRealRadialProfile v = 0 := by
  let e := (PiLp.continuousLinearEquiv 2 Real
    (fun _ : Fin m => Real)).symm
  have hnorm : Continuous (fun w : Fin m → Real => ‖e w‖) :=
    continuous_norm.comp e.continuous
  have hnear :
      ∀ᶠ w : Fin m → Real in 𝓝 v, 2 < ‖e w‖ :=
    (isOpen_Ioi.preimage hnorm).mem_nhds hv
  have hlocal :
      osiiProductionRealRadialProfile =ᶠ[𝓝 v]
        fun _ : Fin m → Real => (0 : Complex) := by
    filter_upwards [hnear] with w hw
    rw [osiiProductionRealRadialProfile_apply,
      Real.smoothTransition.zero_of_nonpos (by linarith)]
    norm_num
  have heq :=
    (Filter.EventuallyEq.iteratedFDeriv (𝕜 := Real) hlocal n).eq_of_nhds
  rw [heq, iteratedFDeriv_const_of_ne hn, Pi.zero_apply]

theorem osiiProductionRealRadialProfile_boundary_gevrey_bound
    {m : Nat} (v : Fin (m + 1) → Real) (n : Nat) (hn : n ≠ 0)
    (hv :
      ‖(PiLp.continuousLinearEquiv 2 Real
        (fun _ : Fin (m + 1) => Real)).symm v‖ = 1 ∨
      ‖(PiLp.continuousLinearEquiv 2 Real
        (fun _ : Fin (m + 1) => Real)).symm v‖ = 2) :
    ‖iteratedFDeriv Real n osiiProductionRealRadialProfile v‖ ≤
      Real.exp 6 *
        (98304 * ((m + 1 : Nat) : Real) ^ 2) ^ n *
          (n.factorial : Real) ^ 2 := by
  let e := (PiLp.continuousLinearEquiv 2 Real
    (fun _ : Fin (m + 1) => Real)).symm
  let epsilon : Nat → Real := fun k => 1 / ((k : Real) + 1)
  have hepsilon : Filter.Tendsto epsilon Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hsmall : ∀ᶠ k : Nat in Filter.atTop, epsilon k < 1 :=
    hepsilon.eventually (Iio_mem_nhds (by norm_num))
  have hpositive : ∀ k : Nat, 0 < epsilon k := by
    intro k
    dsimp [epsilon]
    positivity
  have hcontinuous :
      Continuous (fun w : Fin (m + 1) → Real =>
        ‖iteratedFDeriv Real n osiiProductionRealRadialProfile w‖) :=
    continuous_norm.comp
      ((osiiProductionRealRadialProfile_contDiff (m + 1)).continuous_iteratedFDeriv
        (by exact_mod_cast le_top))
  rcases hv with hv | hv
  · let path : Nat → (Fin (m + 1) → Real) :=
      fun k => (1 + epsilon k) • v
    have hfactor :
        Filter.Tendsto (fun k : Nat => 1 + epsilon k)
          Filter.atTop (𝓝 (1 : Real)) := by
      simpa using tendsto_const_nhds.add hepsilon
    have hpath : Filter.Tendsto path Filter.atTop (𝓝 v) := by
      simpa [path] using hfactor.smul_const v
    apply le_of_tendsto (hcontinuous.continuousAt.tendsto.comp hpath)
    filter_upwards [hsmall] with k hk
    let x : EuclideanSpace Real (Fin (m + 1)) := e (path k)
    have hnorm : ‖x‖ = 1 + epsilon k := by
      dsimp [x, path]
      rw [map_smul, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by linarith [hpositive k]), hv, mul_one]
    have hxlower : 1 < ‖x‖ := by
      rw [hnorm]
      linarith [hpositive k]
    have hxupper : ‖x‖ < 2 := by
      rw [hnorm]
      linarith
    have hflat : (fun i => x i) = path k := by
      funext i
      rfl
    simpa [hflat] using
      osiiProductionRealRadialProfile_annulus_gevrey_bound
        x hxlower hxupper n hn
  · let path : Nat → (Fin (m + 1) → Real) :=
      fun k => (1 - epsilon k / 2) • v
    have hfactor :
        Filter.Tendsto (fun k : Nat => 1 - epsilon k / 2)
          Filter.atTop (𝓝 (1 : Real)) := by
      convert tendsto_const_nhds.sub (hepsilon.div_const 2) using 1 <;>
        norm_num
    have hpath : Filter.Tendsto path Filter.atTop (𝓝 v) := by
      simpa [path] using hfactor.smul_const v
    apply le_of_tendsto (hcontinuous.continuousAt.tendsto.comp hpath)
    filter_upwards [hsmall] with k hk
    let x : EuclideanSpace Real (Fin (m + 1)) := e (path k)
    have hfactor_pos : 0 < 1 - epsilon k / 2 := by
      linarith [hpositive k]
    have hnorm : ‖x‖ = 2 - epsilon k := by
      dsimp [x, path]
      rw [map_smul, norm_smul, Real.norm_eq_abs,
        abs_of_pos hfactor_pos, hv]
      ring
    have hxlower : 1 < ‖x‖ := by
      rw [hnorm]
      linarith
    have hxupper : ‖x‖ < 2 := by
      rw [hnorm]
      linarith [hpositive k]
    have hflat : (fun i => x i) = path k := by
      funext i
      rfl
    simpa [hflat] using
      osiiProductionRealRadialProfile_annulus_gevrey_bound
        x hxlower hxupper n hn

theorem osiiProductionRealRadialProfile_global_gevrey_bound
    {m : Nat} (v : Fin (m + 1) → Real) (n : Nat) :
    ‖iteratedFDeriv Real n osiiProductionRealRadialProfile v‖ ≤
      Real.exp 6 *
        (98304 * ((m + 1 : Nat) : Real) ^ 2) ^ n *
          (n.factorial : Real) ^ 2 := by
  by_cases hn : n = 0
  · subst n
    simp only [norm_iteratedFDeriv_zero, Nat.factorial_zero, Nat.cast_one,
      one_pow, pow_zero, mul_one]
    rw [osiiProductionRealRadialProfile_apply, Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact (Real.smoothTransition.le_one _).trans
      (by nlinarith [Real.add_one_le_exp (6 : Real)])
  let e := (PiLp.continuousLinearEquiv 2 Real
    (fun _ : Fin (m + 1) => Real)).symm
  let x : EuclideanSpace Real (Fin (m + 1)) := e v
  by_cases hlower : ‖x‖ < 1
  · rw [osiiProductionRealRadialProfile_iteratedFDeriv_zero_of_norm_lt_one
      v n hn hlower, norm_zero]
    positivity
  by_cases hupper : 2 < ‖x‖
  · rw [osiiProductionRealRadialProfile_iteratedFDeriv_zero_of_two_lt_norm
      v n hn hupper, norm_zero]
    positivity
  have hlower' : 1 ≤ ‖x‖ := le_of_not_gt hlower
  have hupper' : ‖x‖ ≤ 2 := le_of_not_gt hupper
  rcases hlower'.eq_or_lt with hboundary | hlower''
  · exact osiiProductionRealRadialProfile_boundary_gevrey_bound
      v n hn (Or.inl hboundary.symm)
  rcases hupper'.eq_or_lt with hboundary | hupper''
  · exact osiiProductionRealRadialProfile_boundary_gevrey_bound
      v n hn (Or.inr hboundary)
  have hflat : (fun i => x i) = v := by
    funext i
    rfl
  simpa [hflat] using
    osiiProductionRealRadialProfile_annulus_gevrey_bound
      x hlower'' hupper'' n hn

def osiiProductionComplexBlockRealCoordinateCLM
    (q : Nat) :
    (Fin q → Complex) →L[Real] (Fin (q * 2) → Real) :=
  ContinuousLinearMap.pi fun j =>
    let p := (finProdFinEquiv : Fin q × Fin 2 ≃ Fin (q * 2)).symm j
    if p.2 = 0 then
      Complex.reCLM.comp (ContinuousLinearMap.proj p.1)
    else
      Complex.imCLM.comp (ContinuousLinearMap.proj p.1)

theorem osiiProductionComplexBlockRealCoordinateCLM_apply
    (q : Nat) (z : Fin q → Complex) (j : Fin (q * 2)) :
    osiiProductionComplexBlockRealCoordinateCLM q z j =
      osiiProductionComplexBlockRealCoordinates q z j := by
  dsimp [osiiProductionComplexBlockRealCoordinateCLM,
    osiiProductionComplexBlockRealCoordinates]
  split <;> rfl

theorem osiiProductionComplexBlockRealCoordinateCLM_apply_norm_le
    (q : Nat) (z : Fin q → Complex) :
    ‖osiiProductionComplexBlockRealCoordinateCLM q z‖ ≤ ‖z‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
  intro j
  let p := (finProdFinEquiv : Fin q × Fin 2 ≃ Fin (q * 2)).symm j
  by_cases hp : p.2 = 0
  · have hcoord :
        osiiProductionComplexBlockRealCoordinateCLM q z j = (z p.1).re := by
      rw [osiiProductionComplexBlockRealCoordinateCLM_apply]
      change (if p.2 = 0 then (z p.1).re else (z p.1).im) = _
      simp [hp]
    rw [hcoord, Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm (z p.1)).trans
      (norm_le_pi_norm z p.1)
  · have hcoord :
        osiiProductionComplexBlockRealCoordinateCLM q z j = (z p.1).im := by
      rw [osiiProductionComplexBlockRealCoordinateCLM_apply]
      change (if p.2 = 0 then (z p.1).re else (z p.1).im) = _
      simp [hp]
    rw [hcoord, Real.norm_eq_abs]
    exact (Complex.abs_im_le_norm (z p.1)).trans
      (norm_le_pi_norm z p.1)

theorem osiiStep4ComplexBlockRadialRaw_eq_productionRealProfile
    (q : Nat) (rho : Real) (z : Fin q → Complex) :
    (osiiStep4ComplexBlockRadialRaw q rho z : Complex) =
      osiiProductionRealRadialProfile
        (osiiProductionComplexBlockRealCoordinateCLM q
          ((16 / rho) • z)) := by
  rw [osiiStep4ComplexBlockRadialRaw_apply,
    osiiProductionRealRadialProfile_apply]
  congr 2
  have hcoordinates :
      (PiLp.continuousLinearEquiv 2 Real
          (fun _ : Fin (q * 2) => Real)).symm
        (osiiProductionComplexBlockRealCoordinateCLM q
          ((16 / rho) • z)) =
        osiiProductionComplexBlockRealCoordinates q
          ((16 / rho) • z) := by
    ext j
    exact osiiProductionComplexBlockRealCoordinateCLM_apply
      q ((16 / rho) • z) j
  rw [hcoordinates,
    osiiProductionComplexBlockRealCoordinates_norm]
  congr 1

theorem osiiProductionRealRadialProfile_global_gevrey_bound_of_pos
    {m : Nat} (hm : 0 < m) (v : Fin m → Real) (n : Nat) :
    ‖iteratedFDeriv Real n osiiProductionRealRadialProfile v‖ ≤
      Real.exp 6 * (98304 * (m : Real) ^ 2) ^ n *
        (n.factorial : Real) ^ 2 := by
  cases m with
  | zero => omega
  | succ m =>
    exact osiiProductionRealRadialProfile_global_gevrey_bound v n

def osiiProductionRealRadialScalarProfile
    {m : Nat} (v : Fin m → Real) : Real :=
  (osiiProductionRealRadialProfile v).re

theorem osiiProductionRealRadialScalarProfile_contDiff
    (m : Nat) :
    ContDiff Real (⊤ : ℕ∞)
      (osiiProductionRealRadialScalarProfile (m := m)) := by
  exact Complex.reCLM.contDiff.comp
    (osiiProductionRealRadialProfile_contDiff m)

theorem osiiProductionRealRadialScalarProfile_global_gevrey_bound
    {m : Nat} (hm : 0 < m) (v : Fin m → Real) (n : Nat) :
    ‖iteratedFDeriv Real n osiiProductionRealRadialScalarProfile v‖ ≤
      Real.exp 6 * (98304 * (m : Real) ^ 2) ^ n *
        (n.factorial : Real) ^ 2 := by
  have hprofile :
      (osiiProductionRealRadialProfile (m := m)) =
        Complex.ofRealLI ∘
          (osiiProductionRealRadialScalarProfile (m := m)) := by
    funext w
    rw [osiiProductionRealRadialProfile_apply]
    simp [osiiProductionRealRadialScalarProfile,
      osiiProductionRealRadialProfile_apply]
  have hnorm :
      ‖iteratedFDeriv Real n osiiProductionRealRadialProfile v‖ =
        ‖iteratedFDeriv Real n
          osiiProductionRealRadialScalarProfile v‖ := by
    rw [hprofile]
    exact Complex.ofRealLI.norm_iteratedFDeriv_comp_left
      (osiiProductionRealRadialScalarProfile_contDiff m).contDiffAt
      (by exact_mod_cast le_top)
  rw [← hnorm]
  exact osiiProductionRealRadialProfile_global_gevrey_bound_of_pos
    hm v n

def osiiProductionNormalizedRadialRealProfile
    (q : Nat) (rho : Real) (v : Fin (q * 2) → Real) : Real :=
  (16 / rho) ^ (2 * q) *
      osiiProductionRealRadialScalarProfile ((16 / rho) • v) /
    ∫ z : Fin q → Complex, osiiStep4ComplexBlockRadialRaw q 16 z

theorem osiiStep4ComplexBlockRadialG_eq_normalizedRealProfile
    (q : Nat) {rho : Real} (hrho : 0 < rho)
    (z : Fin q → Complex) :
    osiiStep4ComplexBlockRadialG q rho z =
      osiiProductionNormalizedRadialRealProfile q rho
        (osiiProductionComplexBlockRealCoordinateCLM q z) := by
  rw [osiiStep4ComplexBlockRadialG_scale q hrho z]
  unfold osiiStep4ComplexBlockRadialG
  unfold osiiProductionNormalizedRadialRealProfile
  have hraw := congrArg Complex.re
    (osiiStep4ComplexBlockRadialRaw_eq_productionRealProfile
      q 16 ((16 / rho) • z))
  have hraw' :
      osiiStep4ComplexBlockRadialRaw q 16 ((16 / rho) • z) =
        osiiProductionRealRadialScalarProfile
          ((16 / rho) •
            osiiProductionComplexBlockRealCoordinateCLM q z) := by
    simpa [osiiProductionRealRadialScalarProfile, map_smul] using hraw
  rw [hraw']
  ring

theorem osiiProductionNormalizedRadialRealProfile_global_gevrey_bound
    (q : Nat) {rho : Real} (hrho : 0 < rho)
    (v : Fin ((q + 1) * 2) → Real) (n : Nat) :
    ‖iteratedFDeriv Real n
        (osiiProductionNormalizedRadialRealProfile (q + 1) rho) v‖ ≤
      ((∫ z : Fin (q + 1) → Complex,
          osiiStep4ComplexBlockRadialRaw (q + 1) 16 z)⁻¹ *
        Real.exp 6 *
        (98304 * (((q + 1) * 2 : Nat) : Real) ^ 2) ^ n *
          (n.factorial : Real) ^ 2) *
        (16 / rho) ^ (2 * (q + 1) + n) := by
  let a : Real := 16 / rho
  let I : Real := ∫ z : Fin (q + 1) → Complex,
    osiiStep4ComplexBlockRadialRaw (q + 1) 16 z
  let G : (Fin ((q + 1) * 2) → Real) → Real :=
    osiiProductionRealRadialScalarProfile
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hI : 0 < I :=
    osiiStep4ComplexBlockRadialRaw_integral_pos
      (q + 1) (by norm_num)
  have hG : ContDiff Real (⊤ : ℕ∞) G :=
    osiiProductionRealRadialScalarProfile_contDiff ((q + 1) * 2)
  have hcomp :
      ContDiff Real n (fun w : Fin ((q + 1) * 2) → Real => G (a • w)) :=
    (hG.of_le (by exact_mod_cast le_top)).comp (contDiff_const_smul a)
  have hfun :
      osiiProductionNormalizedRadialRealProfile (q + 1) rho =
        fun w : Fin ((q + 1) * 2) → Real =>
          (a ^ (2 * (q + 1)) / I) • G (a • w) := by
    funext w
    simp [osiiProductionNormalizedRadialRealProfile, a, I, G,
      smul_eq_mul]
    ring
  have hderiv :
      iteratedFDeriv Real n
          (osiiProductionNormalizedRadialRealProfile (q + 1) rho) v =
        (a ^ (2 * (q + 1)) / I) •
          (a ^ n : Real) • iteratedFDeriv Real n G (a • v) := by
    rw [hfun]
    calc
      iteratedFDeriv Real n
          (fun w : Fin ((q + 1) * 2) → Real =>
            (a ^ (2 * (q + 1)) / I) • G (a • w)) v =
        (a ^ (2 * (q + 1)) / I) •
          iteratedFDeriv Real n
            (fun w : Fin ((q + 1) * 2) → Real => G (a • w)) v :=
        iteratedFDeriv_const_smul_apply' hcomp.contDiffAt
      _ = (a ^ (2 * (q + 1)) / I) •
          (a ^ n : Real) • iteratedFDeriv Real n G (a • v) := by
        rw [show iteratedFDeriv Real n
              (fun w : Fin ((q + 1) * 2) → Real => G (a • w)) v =
            (a ^ n : Real) • iteratedFDeriv Real n G (a • v) by
              simpa using congrFun
                (iteratedFDeriv_comp_const_smul a
                  (hG.of_le (by exact_mod_cast le_top))) v]
  have hglobal :=
    osiiProductionRealRadialScalarProfile_global_gevrey_bound
      (m := (q + 1) * 2) (by omega) (a • v) n
  rw [hderiv, norm_smul, norm_smul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ a ^ (2 * (q + 1)) / I),
    abs_of_nonneg (pow_nonneg ha.le n)]
  calc
    a ^ (2 * (q + 1)) / I *
        (a ^ n * ‖iteratedFDeriv Real n G (a • v)‖) ≤
      a ^ (2 * (q + 1)) / I *
        (a ^ n *
          (Real.exp 6 *
            (98304 * (((q + 1) * 2 : Nat) : Real) ^ 2) ^ n *
              (n.factorial : Real) ^ 2)) := by
        gcongr
    _ = ((∫ z : Fin (q + 1) → Complex,
          osiiStep4ComplexBlockRadialRaw (q + 1) 16 z)⁻¹ *
        Real.exp 6 *
        (98304 * (((q + 1) * 2 : Nat) : Real) ^ 2) ^ n *
          (n.factorial : Real) ^ 2) *
        (16 / rho) ^ (2 * (q + 1) + n) := by
      rw [pow_add]
      dsimp [a, I]
      field_simp

end OSReconstruction
