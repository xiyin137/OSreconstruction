/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.GeneralResults.SchwartzCutoffExp
import OSReconstruction.SCV.TranslationDifferentiation
import OSReconstruction.Wightman.Reconstruction.TranslationInvariantSchwartz
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option backward.isDefEq.respectTransparency false










noncomputable section

open Complex Filter Set Topology
open scoped Classical LineDeriv ContDiff

namespace OSReconstruction.OSIIChapterVI

variable {k : Nat}

/-- Exponential multiplication on an actual compact momentum test. -/
def compactExponentialTest
    (L : (Fin k -> Real) →L[Real] Complex)
    (psi : SchwartzMap (Fin k -> Real) Complex)
    (hpsi : HasCompactSupport (psi : (Fin k -> Real) -> Complex))
    (t : Real) : SchwartzMap (Fin k -> Real) Complex :=
  (hpsi.mul_left (f := fun p => Complex.exp ((t • L) p))).toSchwartzMap
    ((Complex.contDiff_exp.comp (t • L).contDiff).mul (psi.smooth ⊤))

@[simp] theorem compactExponentialTest_apply
    (L : (Fin k -> Real) →L[Real] Complex)
    (psi : SchwartzMap (Fin k -> Real) Complex)
    (hpsi : HasCompactSupport (psi : (Fin k -> Real) -> Complex))
    (t : Real) (p : Fin k -> Real) :
    compactExponentialTest L psi hpsi t p = Complex.exp ((t • L) p) * psi p := rfl

@[simp] theorem compactExponentialTest_zero
    (L : (Fin k -> Real) →L[Real] Complex)
    (psi : SchwartzMap (Fin k -> Real) Complex)
    (hpsi : HasCompactSupport (psi : (Fin k -> Real) -> Complex)) :
    compactExponentialTest L psi hpsi 0 = psi := by
  ext p
  simp

private def compactExponentialTimeCutoff : ContDiffBump (0 : Real) :=
  ⟨1, 2, zero_lt_one, one_lt_two⟩

private theorem exists_compactExponentialKernel
    (L : (Fin k -> Real) →L[Real] Complex)
    (psi : SchwartzMap (Fin k -> Real) Complex)
    (hpsi : HasCompactSupport (psi : (Fin k -> Real) -> Complex))
    (t : Real) :
    exists K : SchwartzMap (Fin (k + 1) -> Real) Complex,
      forall h p, K (Fin.cons h p) =
        (compactExponentialTimeCutoff h : Complex) *
          compactExponentialTest L psi hpsi (t + h) p := by
  let b : SchwartzMap Real Complex :=
    (compactExponentialTimeCutoff.hasCompactSupport.comp_left
      Complex.ofReal_zero).toSchwartzMap
        (Complex.ofRealCLM.contDiff.comp compactExponentialTimeCutoff.contDiff)
  let base := b.prependField psi
  have hbase : HasCompactSupport
      (base : (Fin (k + 1) -> Real) -> Complex) :=
    hasCompactSupport_prependField b psi
      (compactExponentialTimeCutoff.hasCompactSupport.comp_left
        Complex.ofReal_zero) hpsi
  let f : (Fin (k + 1) -> Real) -> Complex :=
    fun x => Complex.exp (((t + x 0 : Real) : Complex) * L (tailCLM k x))
  have hf : ContDiff Real (⊤ : ℕ∞) f := by
    dsimp [f]
    have htail : ContDiff Real (⊤ : ℕ∞)
        (fun x : Fin (k + 1) -> Real => fun i : Fin k => x i.succ) :=
      (tailCLM k (E := Real)).contDiff
    exact Complex.contDiff_exp.comp
      ((Complex.ofRealCLM.contDiff.comp
        (contDiff_const.add (headCoordProjCLM k).contDiff)).mul
          (L.contDiff.comp htail))
  let K := (hbase.mul_left (f := f)).toSchwartzMap (hf.mul (base.smooth ⊤))
  refine ⟨K, ?_⟩
  intro h p
  change Complex.exp (((t + h : Real) : Complex) * L p) *
    ((compactExponentialTimeCutoff h : Complex) * psi p) = _
  simp only [compactExponentialTest_apply, ContinuousLinearMap.smul_apply,
    Complex.real_smul]
  ring

/-- A compact exponential test is differentiable in the actual Schwartz
topology. Localizing the parameter reduces this to Schwartz translation. -/
theorem tendsto_diffQuotient_compactExponentialTest
    (L : (Fin k -> Real) →L[Real] Complex)
    (psi : SchwartzMap (Fin k -> Real) Complex)
    (hpsi : HasCompactSupport (psi : (Fin k -> Real) -> Complex))
    (t : Real) :
    Tendsto (fun h : Real => h⁻¹ •
      (compactExponentialTest L psi hpsi (t + h) -
        compactExponentialTest L psi hpsi t))
      (nhdsWithin 0 ({0}ᶜ))
      (nhds (SchwartzMap.smulLeftCLM Complex L
        (compactExponentialTest L psi hpsi t))) := by
  obtain ⟨K, hK⟩ := exists_compactExponentialKernel L psi hpsi t
  let e : Fin (k + 1) -> Real := Pi.single 0 1
  have hcons (h : Real) (p : Fin k -> Real) :
      Fin.cons 0 p + h • e = Fin.cons h p := by
    ext j
    refine Fin.cases ?_ (fun i => ?_) j <;> simp [e]
  have hb0 : compactExponentialTimeCutoff 0 = 1 :=
    compactExponentialTimeCutoff.eventuallyEq_one.eq_of_nhds
  have hlocal : ∀ᶠ h : Real in nhds 0,
      headSectionCLM k (SCV.translateSchwartz (h • e) K) =
        compactExponentialTest L psi hpsi (t + h) := by
    filter_upwards [compactExponentialTimeCutoff.eventuallyEq_one] with h hh
    ext p
    rw [headSectionCLM_apply, SCV.translateSchwartz_apply, hcons, hK]
    simp only [hh, Pi.one_apply, Complex.ofReal_one, one_mul]
  have hbase : headSectionCLM k K = compactExponentialTest L psi hpsi t := by
    ext p
    rw [headSectionCLM_apply, hK, hb0]
    simp
  have hderiv : headSectionCLM k (∂_{e} K) =
      SchwartzMap.smulLeftCLM Complex L (compactExponentialTest L psi hpsi t) := by
    ext p
    rw [headSectionCLM_apply, SchwartzMap.lineDerivOp_apply,
      SchwartzMap.smulLeftCLM_apply_apply (F := Complex) L.hasTemperateGrowth]
    change deriv (fun h : Real => K (Fin.cons 0 p + h • e)) 0 = _
    have heq : (fun h : Real => K (Fin.cons 0 p + h • e)) =ᶠ[nhds 0]
        (fun h => Complex.exp (((t + h : Real) : Complex) * L p) * psi p) := by
      filter_upwards [compactExponentialTimeCutoff.eventuallyEq_one] with h hh
      rw [hcons, hK]
      simp only [hh, Pi.one_apply, Complex.ofReal_one, one_mul,
        compactExponentialTest_apply, ContinuousLinearMap.smul_apply, Complex.real_smul]
    have hlin : HasDerivAt
        (fun h : Real => ((t + h : Real) : Complex) * L p) (L p) 0 := by
      simpa [Complex.ofReal_add, add_comm] using
        ((Complex.ofRealCLM.hasDerivAt (x := 0)).const_add (t : Complex)).mul_const (L p)
    rw [heq.deriv_eq]
    simpa [compactExponentialTest_apply, Complex.real_smul, smul_eq_mul,
      mul_comm, mul_left_comm] using (hlin.cexp.mul_const (psi p)).deriv
  have h := (headSectionCLM k).continuous.tendsto (∂_{e} K) |>.comp
    (SCV.tendsto_diffQuotient_translateSchwartz_zero K e)
  rw [hderiv] at h
  apply h.congr'
  filter_upwards [hlocal.filter_mono nhdsWithin_le_nhds] with u hu
  change headSectionCLM k (u⁻¹ • (SCV.translateSchwartz (u • e) K - K)) = _
  rw [ContinuousLinearMap.map_smul_of_tower, map_sub, hu, hbase]

/-- Compact exponential multiplication is continuous as a Schwartz-valued
curve, including at zero. -/
theorem continuous_compactExponentialTest
    (L : (Fin k -> Real) →L[Real] Complex)
    (psi : SchwartzMap (Fin k -> Real) Complex)
    (hpsi : HasCompactSupport (psi : (Fin k -> Real) -> Complex)) :
    Continuous (compactExponentialTest L psi hpsi) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let F := compactExponentialTest L psi hpsi
  have hq := tendsto_diffQuotient_compactExponentialTest L psi hpsi t
  have hid : Tendsto (fun h : Real => h) (nhdsWithin 0 ({0}ᶜ)) (nhds 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hdiff : Tendsto (fun h => F (t + h) - F t)
      (nhdsWithin 0 ({0}ᶜ)) (nhds 0) := by
    have h := hid.smul hq
    simp only [zero_smul] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu0 : u ≠ 0 := by simpa using hu
    simp [F, smul_smul, hu0]
  have hpunctured : Tendsto (fun h => F (t + h))
      (nhdsWithin 0 ({0}ᶜ)) (nhds (F t)) := by
    simpa only [sub_add_cancel, zero_add] using hdiff.add_const (F t)
  have hcont : ContinuousAt (fun h => F (t + h)) 0 := by
    apply continuousAt_iff_punctured_nhds.mpr
    simpa only [add_zero] using hpunctured
  have hshift : Tendsto (fun u : Real => u - t) (nhds t) (nhds 0) := by
    convert tendsto_id.sub_const t using 1 <;> simp
  change Tendsto F (nhds t) (nhds (F t))
  convert hcont.tendsto.comp hshift using 1 <;> simp [Function.comp_def]

/-- The weak distribution equation and the moving compact test have opposite
derivatives. Banach-Steinhaus justifies their product rule. -/
theorem hasDerivAt_compactExponential_pairing
    (P : Real -> SchwartzMap (Fin k -> Real) Complex →L[Complex] Complex)
    (L : (Fin k -> Real) →L[Real] Complex)
    (psi : SchwartzMap (Fin k -> Real) Complex)
    (hpsi : HasCompactSupport (psi : (Fin k -> Real) -> Complex))
    (t : Real)
    (hP : forall phi : SchwartzMap (Fin k -> Real) Complex,
      HasDerivAt (fun u => P u phi)
        (-P t (SchwartzMap.smulLeftCLM Complex L phi)) t) :
    HasDerivAt (fun u => P u (compactExponentialTest L psi hpsi u)) 0 t := by
  let F := compactExponentialTest L psi hpsi
  let M := SchwartzMap.smulLeftCLM Complex L
  have hshift : Tendsto (fun h : Real => t + h)
      (nhdsWithin 0 ({0}ᶜ)) (nhds t) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun h : Real => t + h) (nhdsWithin 0 ({0}ᶜ)) (nhds (t + 0)))
  have hweak : forall phi : SchwartzMap (Fin k -> Real) Complex,
      Tendsto (fun h => ((P (t + h)).restrictScalars Real) phi)
        (nhdsWithin 0 ({0}ᶜ)) (nhds (((P t).restrictScalars Real) phi)) := by
    intro phi
    exact (hP phi).continuousAt.tendsto.comp hshift
  have hfirst : Tendsto (fun h : Real =>
      P (t + h) (h⁻¹ • (F (t + h) - F t)))
      (nhdsWithin 0 ({0}ᶜ)) (nhds (P t (M (F t)))) :=
    SchwartzMap.tempered_apply_tendsto_of_tendsto_filter hweak
      (tendsto_diffQuotient_compactExponentialTest L psi hpsi t)
  have hsecond := (hP (F t)).tendsto_slope_zero
  have hsum : Tendsto (fun h : Real =>
      P (t + h) (h⁻¹ • (F (t + h) - F t)) +
        h⁻¹ • (P (t + h) (F t) - P t (F t)))
      (nhdsWithin 0 ({0}ᶜ)) (nhds 0) := by
    simpa only [M, add_neg_cancel] using hfirst.add hsecond
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  apply hsum.congr'
  filter_upwards with h
  rw [ContinuousLinearMap.map_smul_of_tower, map_sub, ← smul_add]
  congr 1
  abel

private def compactExponentialSeminormConstant
    (L : (Fin k -> Real) →L[Real] Complex)
    (psi : SchwartzMap (Fin k -> Real) Complex) (a n : Nat) : Real :=
  ∑ j ∈ Finset.range (n + 1),
    (n.choose j : Real) * (j.factorial : Real) * ‖L‖ ^ j *
      SchwartzMap.seminorm Complex a (n - j) psi

private theorem compactExponentialSeminormConstant_nonneg
    (L : (Fin k -> Real) →L[Real] Complex)
    (psi : SchwartzMap (Fin k -> Real) Complex) (a n : Nat) :
    0 <= compactExponentialSeminormConstant L psi a n := by
  unfold compactExponentialSeminormConstant
  exact Finset.sum_nonneg fun j _ => by positivity

set_option backward.isDefEq.respectTransparency false in
/-- Every derivative of a compact test acquires only a polynomial loss while
the exponential retains the strict negative-support gap. -/
theorem seminorm_compactExponentialTest_le
    (L : (Fin k -> Real) →L[Real] Complex)
    (psi : SchwartzMap (Fin k -> Real) Complex)
    (hpsi : HasCompactSupport (psi : (Fin k -> Real) -> Complex))
    {c : Real}
    (hsupport : forall p, p ∈ tsupport (psi : (Fin k -> Real) -> Complex) ->
      (L p).re <= -c)
    (a n : Nat) {t : Real} (ht : 0 <= t) :
    SchwartzMap.seminorm Complex a n (compactExponentialTest L psi hpsi t) <=
      compactExponentialSeminormConstant L psi a n *
        (1 + t) ^ n * Real.exp (-c * t) := by
  have hC := compactExponentialSeminormConstant_nonneg L psi a n
  apply SchwartzMap.seminorm_le_bound Complex a n _ (by positivity)
  intro p
  by_cases hp : p ∈ tsupport (psi : (Fin k -> Real) -> Complex)
  · have hexp : ‖Complex.exp ((t • L) p)‖ <= Real.exp (-c * t) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      change (t • L p).re <= -c * t
      rw [Complex.real_smul]
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, mul_neg, neg_mul, mul_comm] using
          mul_le_mul_of_nonneg_left (hsupport p hp) ht
    have hjet (j : Nat) :
        ‖iteratedFDeriv Real j (fun x => Complex.exp ((t • L) x)) p‖ <=
          (j.factorial : Real) * Real.exp (-c * t) * (t * ‖L‖) ^ j := by
      calc
        _ <= (j.factorial : Real) * ‖Complex.exp ((t • L) p)‖ * ‖t • L‖ ^ j :=
          norm_iteratedFDeriv_cexp_comp_clm_le (t • L) p j
        _ <= _ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
          gcongr
    have hleibniz := norm_iteratedFDeriv_mul_le
      (Complex.contDiff_exp.comp (t • L).contDiff)
      (psi.smooth ⊤) p (n := n) (by exact_mod_cast le_top)
    change ‖p‖ ^ a * ‖iteratedFDeriv Real n
      (fun x => Complex.exp ((t • L) x) * psi x) p‖ <= _
    apply (mul_le_mul_of_nonneg_left hleibniz (by positivity)).trans
    rw [Finset.mul_sum]
    unfold compactExponentialSeminormConstant
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    have hjn : j <= n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have htpow : t ^ j <= (1 + t) ^ n :=
      (pow_le_pow_left₀ ht (by linarith) j).trans
        (pow_le_pow_right₀ (by linarith) hjn)
    have hpsiJet := SchwartzMap.le_seminorm Complex a (n - j) psi p
    calc
      _ <= ‖p‖ ^ a * ((n.choose j : Real) *
          ((j.factorial : Real) * Real.exp (-c * t) * (t * ‖L‖) ^ j) *
          ‖iteratedFDeriv Real (n - j) (psi : (Fin k -> Real) -> Complex) p‖) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hjet j) (Nat.cast_nonneg _)) (norm_nonneg _))
          (pow_nonneg (norm_nonneg _) _)
      _ = ((n.choose j : Real) * (j.factorial : Real) * ‖L‖ ^ j) *
          t ^ j * Real.exp (-c * t) *
          (‖p‖ ^ a * ‖iteratedFDeriv Real (n - j)
            (psi : (Fin k -> Real) -> Complex) p‖) := by rw [mul_pow]; ring
      _ <= ((n.choose j : Real) * (j.factorial : Real) * ‖L‖ ^ j) *
          (1 + t) ^ n * Real.exp (-c * t) *
          SchwartzMap.seminorm Complex a (n - j) psi := by
        gcongr
      _ = _ := by ring
  · have hzero : (fun x => Complex.exp ((t • L) x) * psi x) =ᶠ[nhds p] 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hp] with x hx
      simp only [hx, mul_zero, Pi.zero_apply]
    change ‖p‖ ^ a * ‖iteratedFDeriv Real n
      (fun x => Complex.exp ((t • L) x) * psi x) p‖ <= _
    rw [(hzero.iteratedFDeriv Real n).eq_of_nhds]
    simpa using mul_nonneg (mul_nonneg hC (by positivity)) (Real.exp_nonneg _)

/-- One finite family of Schwartz seminorms has a uniform exponential bound. -/
theorem exists_finsetSeminorm_compactExponentialTest_bound
    (L : (Fin k -> Real) →L[Real] Complex)
    (psi : SchwartzMap (Fin k -> Real) Complex)
    (hpsi : HasCompactSupport (psi : (Fin k -> Real) -> Complex))
    {c : Real}
    (hsupport : forall p, p ∈ tsupport (psi : (Fin k -> Real) -> Complex) ->
      (L p).re <= -c)
    (s : Finset (Nat × Nat)) :
    exists C : Real, 0 < C ∧ forall t : Real, 0 <= t ->
      s.sup (schwartzSeminormFamily Complex (Fin k -> Real) Complex)
        (compactExponentialTest L psi hpsi t) <=
      C * (1 + t) ^ (s.sup Prod.snd) * Real.exp (-c * t) := by
  let C := 1 + ∑ q ∈ s, compactExponentialSeminormConstant L psi q.1 q.2
  have hC : 0 < C := by
    dsimp [C]
    linarith [Finset.sum_nonneg (s := s) (fun q _ =>
      compactExponentialSeminormConstant_nonneg L psi q.1 q.2)]
  refine ⟨C, hC, ?_⟩
  intro t ht
  apply Seminorm.finset_sup_apply_le
  · positivity
  intro q hq
  have hqC : compactExponentialSeminormConstant L psi q.1 q.2 <= C := by
    have hsum := Finset.single_le_sum
      (fun q _ => compactExponentialSeminormConstant_nonneg L psi q.1 q.2) hq
    dsimp [C]
    linarith
  exact (seminorm_compactExponentialTest_le L psi hpsi hsupport q.1 q.2 ht).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul hqC (pow_le_pow_right₀ (by linarith) (Finset.le_sup hq))
        (by positivity) hC.le) (Real.exp_nonneg _))

/-- Exponential decay on a strict negative half-space beats every fixed
polynomial growth of the horizontal frequency distribution. -/
theorem tendsto_pow_mul_finsetSeminorm_compactExponentialTest
    (L : (Fin k -> Real) →L[Real] Complex)
    (psi : SchwartzMap (Fin k -> Real) Complex)
    (hpsi : HasCompactSupport (psi : (Fin k -> Real) -> Complex))
    {c : Real} (hc : 0 < c)
    (hsupport : forall p, p ∈ tsupport (psi : (Fin k -> Real) -> Complex) ->
      (L p).re <= -c)
    (s : Finset (Nat × Nat)) (N : Nat) :
    Tendsto (fun t : Real => t ^ N *
      s.sup (schwartzSeminormFamily Complex (Fin k -> Real) Complex)
        (compactExponentialTest L psi hpsi t)) atTop (nhds 0) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_finsetSeminorm_compactExponentialTest_bound L psi hpsi hsupport s
  let b := s.sup Prod.snd
  have hlim : Tendsto (fun t : Real =>
      (C * 2 ^ b) * (t ^ (N + b) * Real.exp (-c * t))) atTop (nhds 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      ((N + b : Nat) : Real) c hc
    simpa only [Real.rpow_natCast, mul_zero] using h.const_mul (C * 2 ^ b)
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop (0 : Real)] with t ht
    exact mul_nonneg (pow_nonneg ht _) (apply_nonneg _ _)
  · filter_upwards [eventually_ge_atTop (1 : Real)] with t ht
    have ht0 : 0 <= t := zero_le_one.trans ht
    have hpow : (1 + t) ^ b <= 2 ^ b * t ^ b := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
    calc
      _ <= t ^ N * (C * (1 + t) ^ b * Real.exp (-c * t)) :=
        mul_le_mul_of_nonneg_left (hbound t ht0) (pow_nonneg ht0 _)
      _ <= t ^ N * (C * (2 ^ b * t ^ b) * Real.exp (-c * t)) := by
        gcongr
      _ = _ := by rw [pow_add]; ring

end OSReconstruction.OSIIChapterVI
