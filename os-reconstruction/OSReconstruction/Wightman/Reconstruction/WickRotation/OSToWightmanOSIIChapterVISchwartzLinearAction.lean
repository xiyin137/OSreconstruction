import OSReconstruction.SCV.SchwartzPartialEval
import OSReconstruction.SCV.TranslationDifferentiation
import OSReconstruction.Wightman.Reconstruction.TranslationInvariantSchwartz

/-!
# Linear actions on compact Schwartz sources

A smooth family of linear equivalences acts differentiably on compact
Schwartz sources. Localizing its parameter gives one compact smooth kernel;
Schwartz translation differentiation then proves the limit in the source
topology. This is the common calculus needed for Euclidean rotations and
Lorentz boosts.
-/

noncomputable section

open Complex Filter Set Topology
open scoped Classical LineDeriv ContDiff

set_option backward.isDefEq.respectTransparency false

namespace OSReconstruction.OSIIChapterVI

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

private def linearVectorFieldRealCLM (A : E →L[Real] E) :
    SchwartzMap E Complex →L[Real] SchwartzMap E Complex :=
  (SchwartzMap.bilinLeftCLM
    (ContinuousLinearMap.id Real (E →L[Real] Complex)) A.hasTemperateGrowth).comp
      (SchwartzMap.fderivCLM Real E Complex)

/-- The first-order Schwartz operator `phi |-> (x |-> D phi(x)(A x))`. -/
def linearVectorFieldCLM (A : E →L[Real] E) :
    SchwartzMap E Complex →L[Complex] SchwartzMap E Complex where
  toFun := linearVectorFieldRealCLM A
  map_add' := (linearVectorFieldRealCLM A).map_add
  map_smul' := by
    intro c phi
    ext x
    change fderiv Real (fun y => c • phi y) x (A x) =
      c • fderiv Real phi x (A x)
    rw [fderiv_fun_const_smul phi.differentiableAt c]
    rfl
  cont := (linearVectorFieldRealCLM A).continuous

@[simp] theorem linearVectorFieldCLM_apply
    (A : E →L[Real] E) (phi : SchwartzMap E Complex) (x : E) :
    linearVectorFieldCLM A phi x = fderiv Real phi x (A x) := rfl

theorem tsupport_linearVectorFieldCLM_subset
    (A : E →L[Real] E) (phi : SchwartzMap E Complex) :
    tsupport (linearVectorFieldCLM A phi : E -> Complex) ⊆ tsupport phi := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hnot
  exact hx (by simp [linearVectorFieldCLM_apply, fderiv_of_notMem_tsupport Real hnot])

theorem linearVectorFieldCLM_hasCompactSupport
    (A : E →L[Real] E) (phi : SchwartzMap E Complex)
    (hphi : HasCompactSupport (phi : E -> Complex)) :
    HasCompactSupport (linearVectorFieldCLM A phi : E -> Complex) :=
  hphi.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_linearVectorFieldCLM_subset A phi)

variable [FiniteDimensional Real E]

/-- Partial evaluation of one Schwartz kernel has the expected parameter
derivative in the Schwartz topology of its remaining variables. -/
theorem tendsto_diffQuotient_schwartzPartialEval_zero
    (K : SchwartzMap (Real × E) Complex) :
    Tendsto (fun h : Real => h⁻¹ •
      (SCV.schwartzPartialEval₁ K h - SCV.schwartzPartialEval₁ K 0))
      (nhdsWithin 0 ({0}ᶜ))
      (nhds (SCV.schwartzPartialEval₁ (∂_{((1 : Real), (0 : E))} K) 0)) := by
  let m := Module.finrank Real E
  let c : E ≃L[Real] (Fin m -> Real) := (Module.finBasis Real E).equivFunL
  let a : (Fin (m + 1) -> Real) ≃L[Real] (Real × E) :=
    (Fin.consEquivL Real (fun _ : Fin (m + 1) => Real)).symm.trans
      ((ContinuousLinearEquiv.refl Real Real).prodCongr c.symm)
  let Kflat := SchwartzMap.compCLMOfContinuousLinearEquiv Complex a K
  let P := (SchwartzMap.compCLMOfContinuousLinearEquiv Complex c).comp
    (headSectionCLM m)
  let v : Fin (m + 1) -> Real := Pi.single 0 1
  have hcons (h : Real) (x : E) : a (Fin.cons h (c x)) = (h, x) := by
    simp [a]
  have hshift (h : Real) (x : E) :
      Fin.cons 0 (c x) + h • v = Fin.cons h (c x) := by
    ext j
    refine Fin.cases ?_ (fun i => ?_) j <;> simp [v]
  have hv : a v = ((1 : Real), (0 : E)) := by
    have hvcons : v = Fin.cons 1 (c (0 : E)) := by
      ext j
      refine Fin.cases ?_ (fun i => ?_) j <;> simp [v]
    rw [hvcons, hcons]
  have hbase : P Kflat = SCV.schwartzPartialEval₁ K 0 := by
    ext x
    change K (a (Fin.cons 0 (c x))) = K (0, x)
    rw [hcons]
  have hslice (h : Real) :
      P (SCV.translateSchwartz (h • v) Kflat) = SCV.schwartzPartialEval₁ K h := by
    ext x
    change K (a (Fin.cons 0 (c x) + h • v)) = K (h, x)
    rw [hshift, hcons]
  have hderiv : P (∂_{v} Kflat) =
      SCV.schwartzPartialEval₁ (∂_{((1 : Real), (0 : E))} K) 0 := by
    rw [show ∂_{v} Kflat =
      SchwartzMap.compCLMOfContinuousLinearEquiv Complex a (∂_{a v} K) from
        SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv Complex v a K]
    rw [hv]
    ext x
    change (∂_{((1 : Real), (0 : E))} K) (a (Fin.cons 0 (c x))) =
      (∂_{((1 : Real), (0 : E))} K) (0, x)
    rw [hcons]
  have h := P.continuous.tendsto (∂_{v} Kflat) |>.comp
    (SCV.tendsto_diffQuotient_translateSchwartz_zero Kflat v)
  rw [hderiv] at h
  apply h.congr'
  filter_upwards with u
  change P (u⁻¹ • (SCV.translateSchwartz (u • v) Kflat - Kflat)) = _
  rw [ContinuousLinearMap.map_smul_of_tower, map_sub, hslice, hbase]

private def parameterCutoff : ContDiffBump (0 : Real) :=
  ⟨1, 2, zero_lt_one, one_lt_two⟩

private def linearActionParameterHomeomorph
    (e : Real -> E ≃L[Real] E)
    (he : Continuous (fun p : Real × E => e p.1 p.2))
    (hinv : Continuous (fun p : Real × E => (e p.1).symm p.2)) :
    (Real × E) ≃ₜ (Real × E) where
  toFun := fun p => (p.1, e p.1 p.2)
  invFun := fun p => (p.1, (e p.1).symm p.2)
  left_inv := by rintro ⟨t, x⟩; simp
  right_inv := by rintro ⟨t, x⟩; simp
  continuous_toFun := continuous_fst.prodMk he
  continuous_invFun := continuous_fst.prodMk hinv

omit [FiniteDimensional Real E] in
private theorem exists_compactLinearActionKernel
    (e : Real -> E ≃L[Real] E)
    (he : ContDiff Real (⊤ : ℕ∞) (fun p : Real × E => e p.1 p.2))
    (hinv : Continuous (fun p : Real × E => (e p.1).symm p.2))
    (phi : SchwartzMap E Complex) (hphi : HasCompactSupport (phi : E -> Complex))
    (t : Real) :
    exists K : SchwartzMap (Real × E) Complex,
      forall h x, K (h, x) = (parameterCutoff h : Complex) * phi (e (t + h) x) := by
  let b : Real -> Complex := fun h => (parameterCutoff h : Complex)
  have hb : HasCompactSupport b :=
    parameterCutoff.hasCompactSupport.comp_left Complex.ofReal_zero
  have hb_smooth : ContDiff Real (⊤ : ℕ∞) b :=
    Complex.ofRealCLM.contDiff.comp parameterCutoff.contDiff
  have hbase : HasCompactSupport (fun p : Real × E => b p.1 * phi p.2) := by
    apply HasCompactSupport.of_support_subset_isCompact (hb.isCompact.prod hphi.isCompact)
    intro p hp
    exact ⟨subset_tsupport _ (mul_ne_zero_iff.mp hp).1,
      subset_tsupport _ (mul_ne_zero_iff.mp hp).2⟩
  have hshift : ContDiff Real (⊤ : ℕ∞) (fun p : Real × E => (t + p.1, p.2)) :=
    (contDiff_const.add contDiff_fst).prodMk contDiff_snd
  let H := linearActionParameterHomeomorph (fun h => e (t + h))
    (he.continuous.comp hshift.continuous) (hinv.comp hshift.continuous)
  have hcompact : HasCompactSupport
      (fun p : Real × E => b p.1 * phi (e (t + p.1) p.2)) :=
    hbase.comp_homeomorph H
  have hsmooth : ContDiff Real (⊤ : ℕ∞)
      (fun p : Real × E => b p.1 * phi (e (t + p.1) p.2)) :=
    (hb_smooth.comp contDiff_fst).mul ((phi.smooth ⊤).comp (he.comp hshift))
  exact ⟨hcompact.toSchwartzMap hsmooth, fun _ _ => rfl⟩

/-- A smooth proper linear action has its pointwise derivative in the actual
Schwartz topology when the original source is compactly supported. -/
theorem tendsto_diffQuotient_compactLinearAction
    (e : Real -> E ≃L[Real] E)
    (he : ContDiff Real (⊤ : ℕ∞) (fun p : Real × E => e p.1 p.2))
    (hinv : Continuous (fun p : Real × E => (e p.1).symm p.2))
    (phi : SchwartzMap E Complex) (hphi : HasCompactSupport (phi : E -> Complex))
    (t : Real) (phi' : SchwartzMap E Complex)
    (hderiv : forall x, HasDerivAt (fun u : Real => phi (e u x)) (phi' x) t) :
    Tendsto (fun h : Real => h⁻¹ •
      (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (e (t + h)) phi -
        SchwartzMap.compCLMOfContinuousLinearEquiv Complex (e t) phi))
      (nhdsWithin 0 ({0}ᶜ)) (nhds phi') := by
  obtain ⟨K, hK⟩ := exists_compactLinearActionKernel e he hinv phi hphi t
  have hlocal : ∀ᶠ h : Real in nhds 0,
      SCV.schwartzPartialEval₁ K h =
        SchwartzMap.compCLMOfContinuousLinearEquiv Complex (e (t + h)) phi := by
    filter_upwards [parameterCutoff.eventuallyEq_one] with h hh
    ext x
    simp [hK, hh]
  have hbase : SCV.schwartzPartialEval₁ K 0 =
      SchwartzMap.compCLMOfContinuousLinearEquiv Complex (e t) phi := by
    simpa using hlocal.self_of_nhds
  have htarget : SCV.schwartzPartialEval₁ (∂_{((1 : Real), (0 : E))} K) 0 = phi' := by
    ext x
    rw [SCV.schwartzPartialEval₁_apply, SchwartzMap.lineDerivOp_apply]
    change deriv (fun h : Real => K ((0, x) + h • ((1 : Real), (0 : E)))) 0 = _
    have heq : (fun h : Real => K ((0, x) + h • ((1 : Real), (0 : E)))) =ᶠ[nhds 0]
        (fun h => phi (e (t + h) x)) := by
      filter_upwards [parameterCutoff.eventuallyEq_one] with h hh
      simp [hK, hh]
    rw [heq.deriv_eq]
    exact (HasDerivAt.comp_const_add t 0 (by simpa using hderiv x)).deriv
  have h := tendsto_diffQuotient_schwartzPartialEval_zero K
  rw [htarget] at h
  apply h.congr'
  filter_upwards [hlocal.filter_mono nhdsWithin_le_nhds] with u hu
  rw [hu, hbase]

/-- Applying a tempered distribution to the preceding compact-source curve
commutes with its parameter derivative. -/
theorem hasDerivAt_compactLinearAction_pairing
    (T : SchwartzMap E Complex →L[Complex] Complex)
    (e : Real -> E ≃L[Real] E)
    (he : ContDiff Real (⊤ : ℕ∞) (fun p : Real × E => e p.1 p.2))
    (hinv : Continuous (fun p : Real × E => (e p.1).symm p.2))
    (phi : SchwartzMap E Complex) (hphi : HasCompactSupport (phi : E -> Complex))
    (t : Real) (phi' : SchwartzMap E Complex)
    (hderiv : forall x, HasDerivAt (fun u : Real => phi (e u x)) (phi' x) t) :
    HasDerivAt
      (fun u => T (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (e u) phi))
      (T phi') t := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have h := T.continuous.tendsto phi' |>.comp
    (tendsto_diffQuotient_compactLinearAction e he hinv phi hphi t phi' hderiv)
  apply h.congr'
  filter_upwards with u
  change T (u⁻¹ •
    (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (e (t + u)) phi -
      SchwartzMap.compCLMOfContinuousLinearEquiv Complex (e t) phi)) = _
  rw [ContinuousLinearMap.map_smul_of_tower, map_sub]

omit [FiniteDimensional Real E] in
/-- Nearby inverse images of a compact source fit in one compact subset of
the same open source region. -/
theorem exists_compact_tsupport_linearAction_subset
    (e : Real -> E ≃L[Real] E)
    (hinv : Continuous (fun p : Real × E => (e p.1).symm p.2))
    (phi : SchwartzMap E Complex) (hphi : HasCompactSupport (phi : E -> Complex))
    (U : Set E) (hU : IsOpen U)
    (hzero : ∀ x ∈ tsupport (phi : E -> Complex), (e 0).symm x ∈ U) :
    exists K : Set E, IsCompact K ∧ K ⊆ U ∧
      ∀ᶠ t : Real in nhds 0,
        tsupport (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (e t) phi :
          E -> Complex) ⊆ K := by
  have hnear : ∀ᶠ t : Real in nhds 0,
      ∀ x ∈ tsupport (phi : E -> Complex), (e t).symm x ∈ U :=
    hphi.isCompact.eventually_forall_of_forall_eventually
      (fun x hx => (hinv.tendsto (0, x)).eventually (hU.mem_nhds (hzero x hx)))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let K := (fun p : Real × E => (e p.1).symm p.2) ''
    (Metric.closedBall (0 : Real) (r / 2) ×ˢ tsupport (phi : E -> Complex))
  refine ⟨K, ((isCompact_closedBall (0 : Real) (r / 2)).prod
    hphi.isCompact).image hinv, ?_, ?_⟩
  · rintro x ⟨⟨t, y⟩, ⟨ht, hy⟩, rfl⟩
    apply hball (show t ∈ Metric.ball 0 r from ?_) y hy
    exact Metric.mem_ball.mpr
      (lt_of_le_of_lt (Metric.mem_closedBall.mp ht) (by linarith))
  · filter_upwards [Metric.ball_mem_nhds (0 : Real) (half_pos hr)] with t ht
    intro x hx
    have hpre : e t x ∈ tsupport (phi : E -> Complex) :=
      tsupport_comp_subset_preimage (phi : E -> Complex) (e t).continuous hx
    exact ⟨(t, e t x), ⟨Metric.mem_closedBall.mpr (Metric.mem_ball.mp ht).le, hpre⟩,
      (e t).symm_apply_apply x⟩

end OSReconstruction.OSIIChapterVI
