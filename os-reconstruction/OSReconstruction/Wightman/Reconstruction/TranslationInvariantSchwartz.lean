/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.Core
import OSReconstruction.Wightman.Reconstruction.SchwartzPartialEval
import Init
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import OSReconstruction.Mathlib429Compat
import OSReconstruction.Wightman.Reconstruction.SliceIntegral
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import OSReconstruction.SCV.DistributionalUniqueness
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Classical LineDeriv Topology ContDiff

open SchwartzMap

namespace OSReconstruction

set_option maxHeartbeats 1200000









theorem norm_tailInsertCLM_eq {n : ℕ} (y : Fin n → ℝ) :
    ‖tailInsertCLM n y‖ = ‖y‖ := by
  have hle : ‖tailInsertCLM n y‖ ≤ ‖y‖ := by
    calc
      ‖tailInsertCLM n y‖ ≤ ‖tailInsertCLM n‖ * ‖y‖ := by
        exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖y‖ := by
        gcongr
        exact tailInsertCLM_opNorm_le n
      _ = ‖y‖ := by ring
  have hge : ‖y‖ ≤ ‖tailInsertCLM n y‖ := by
    calc
      ‖y‖ = ‖tailCLM n (E := ℝ) (tailInsertCLM n y)‖ := by
        simp [tailInsertCLM_apply, tailCLM_apply]
      _ ≤ ‖tailCLM n (E := ℝ)‖ * ‖tailInsertCLM n y‖ := by
        exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖tailInsertCLM n y‖ := by
        gcongr
        exact tailCLM_opNorm_le (E := ℝ) n
      _ = ‖tailInsertCLM n y‖ := by ring
  exact le_antisymm hle hge

/-- Head evaluation at the zero head coordinate, as a continuous linear map on
Schwartz space. -/
noncomputable def headSectionCLM (n : ℕ) :
    SchwartzMap (Fin (n + 1) → ℝ) ℂ →L[ℂ] SchwartzMap (Fin n → ℝ) ℂ :=
  SchwartzMap.compCLM ℂ (tailInsertCLM n).hasTemperateGrowth
    ⟨1, 1, fun y => by
      calc
        ‖y‖ = ‖tailInsertCLM n y‖ := (norm_tailInsertCLM_eq y).symm
        _ ≤ 1 * (1 + ‖tailInsertCLM n y‖) ^ (1 : ℕ) := by
          have h : ‖tailInsertCLM n y‖ ≤ 1 + ‖tailInsertCLM n y‖ := by linarith
          simpa using h
    ⟩

@[simp] theorem headSectionCLM_apply {n : ℕ}
    (F : SchwartzMap (Fin (n + 1) → ℝ) ℂ) (y : Fin n → ℝ) :
    headSectionCLM n F y = F (Fin.cons 0 y) := by
  simp [headSectionCLM, tailInsertCLM_apply]

/-- Project to the head coordinate. -/
noncomputable def headCoordProjCLM (n : ℕ) :
    (Fin (n + 1) → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (ι := Fin (n + 1)) (φ := fun _ => ℝ) 0

@[simp] theorem headCoordProjCLM_apply {n : ℕ} (x : Fin (n + 1) → ℝ) :
    headCoordProjCLM n x = x 0 := rfl

/-- Insert into the head coordinate. -/
noncomputable def headCoordSingleCLM (n : ℕ) :
    ℝ →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
    (((Pi.single 0 (1 : ℝ)) : Fin (n + 1) → ℝ))

@[simp] theorem headCoordSingleCLM_apply {n : ℕ} (a : ℝ) :
    headCoordSingleCLM n a = ((Pi.single 0 a) : Fin (n + 1) → ℝ) := by
  ext j
  refine Fin.cases ?_ ?_ j
  · simp [headCoordSingleCLM, Pi.single_apply]
  · intro i
    simp [headCoordSingleCLM, Pi.single_apply]

/-- Project to the head-axis component. -/
noncomputable def headCoordProjectorCLM (n : ℕ) :
    (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  (headCoordSingleCLM n).comp (headCoordProjCLM n)

@[simp] theorem headCoordProjectorCLM_apply {n : ℕ} (x : Fin (n + 1) → ℝ) :
    headCoordProjectorCLM n x = ((Pi.single 0 (x 0)) : Fin (n + 1) → ℝ) := by
  simp [headCoordProjectorCLM, headCoordSingleCLM_apply]

/-- A first-order translation estimate in Schwartz seminorms. This is the core
quantitative input behind the difference-quotient convergence theorem. -/
theorem exists_seminorm_translateSchwartz_sub_le_linear {m : ℕ}
    (g : SchwartzMap (Fin m → ℝ) ℂ)
    (v : Fin m → ℝ) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, |t| ≤ 1 →
        SchwartzMap.seminorm ℝ k n (SCV.translateSchwartz (t • v) g - g) ≤ C * |t| := by
  obtain ⟨D, hD_nonneg, hD⟩ := SCV.seminorm_translateSchwartz_le (m := m) k (n + 1) g
  let C : ℝ := ‖v‖ * D * (1 + ‖v‖) ^ k
  refine ⟨C, by positivity, ?_⟩
  intro t ht
  refine SchwartzMap.seminorm_le_bound ℝ k n (SCV.translateSchwartz (t • v) g - g)
    (by positivity) ?_
  intro x
  let H :
      (Fin m → ℝ) →
        ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ :=
    iteratedFDeriv ℝ n (g : (Fin m → ℝ) → ℂ)
  let hxFun : ℝ →
      ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ :=
    fun s => ‖x‖ ^ k • H (x + s • (t • v))
  have hH_diff : Differentiable ℝ H := by
    simpa [H] using
      (g.smooth (n + 1)).differentiable_iteratedFDeriv (by
        exact_mod_cast Nat.lt_succ_self n)
  have hxFun_hasDeriv :
      ∀ s : ℝ,
        HasDerivAt hxFun
          (‖x‖ ^ k • (fderiv ℝ H (x + s • (t • v)) (t • v))) s := by
    intro s
    have hgamma :
        HasDerivAt (fun r : ℝ => x + r • (t • v)) (t • v) s := by
      let L : ℝ →L[ℝ] (Fin m → ℝ) :=
        ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (t • v)
      simpa [L, ContinuousLinearMap.smulRight_apply, one_smul, add_comm, add_left_comm, add_assoc]
        using (L.hasDerivAt).const_add x
    have hcomp :
        HasDerivAt (fun r : ℝ => H (x + r • (t • v)))
          ((fderiv ℝ H (x + s • (t • v))) (t • v)) s := by
      exact (hH_diff (x + s • (t • v))).hasFDerivAt.comp_hasDerivAt s hgamma
    exact hcomp.const_smul (‖x‖ ^ k)
  have hxFun_bound :
      ∀ s ∈ Set.Ico (0 : ℝ) 1,
        ‖‖x‖ ^ k • (fderiv ℝ H (x + s • (t • v)) (t • v))‖ ≤ C * |t| := by
    intro s hs
    have hs_mem : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, le_of_lt hs.2⟩
    have hs_abs : |s| ≤ 1 := by
      have hs0 : 0 ≤ s := hs.1
      have hs1 : s ≤ 1 := le_of_lt hs.2
      rw [abs_of_nonneg hs0]
      exact hs1
    have hstv_norm : ‖s • (t • v)‖ ≤ ‖v‖ := by
      calc
        ‖s • (t • v)‖ = |s| * (|t| * ‖v‖) := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ 1 * (1 * ‖v‖) := by
          gcongr
        _ = ‖v‖ := by ring
    have hone_pow :
        (1 + ‖s • (t • v)‖) ^ k ≤ (1 + ‖v‖) ^ k := by
      gcongr
    have hseminorm0 :
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n + 1) (⇑(SCV.translateSchwartz (s • (t • v)) g)) x‖ ≤
          D * (1 + ‖s • (t • v)‖) ^ k := by
      exact le_trans (SchwartzMap.le_seminorm ℂ k (n + 1) _ x) (hD (s • (t • v)))
    have hseminorm :
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n + 1) (g : (Fin m → ℝ) → ℂ) (x + s • (t • v))‖ ≤
          D * (1 + ‖s • (t • v)‖) ^ k := by
      have htrans :
          iteratedFDeriv ℝ (n + 1) (⇑(SCV.translateSchwartz (s • (t • v)) g)) x =
            iteratedFDeriv ℝ (n + 1) (g : (Fin m → ℝ) → ℂ) (x + s • (t • v)) := by
        change iteratedFDeriv ℝ (n + 1) (fun z => g (z + s • (t • v))) x = _
        exact iteratedFDeriv_comp_add_right
          (f := (g : (Fin m → ℝ) → ℂ)) (n + 1) (s • (t • v)) x
      simpa [htrans] using hseminorm0
    have hxpow_nonneg : 0 ≤ ‖x‖ ^ k := by positivity
    calc
      ‖‖x‖ ^ k • (fderiv ℝ H (x + s • (t • v)) (t • v))‖
          = ‖x‖ ^ k * ‖(fderiv ℝ H (x + s • (t • v))) (t • v)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hxpow_nonneg]
      _ ≤ ‖x‖ ^ k * (‖fderiv ℝ H (x + s • (t • v))‖ * ‖t • v‖) := by
            gcongr
            exact ContinuousLinearMap.le_opNorm _ _
      _ = (‖x‖ ^ k * ‖fderiv ℝ H (x + s • (t • v))‖) * ‖t • v‖ := by ring
      _ = (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n + 1) (g : (Fin m → ℝ) → ℂ)
            (x + s • (t • v))‖) * ‖t • v‖ := by
            rw [norm_fderiv_iteratedFDeriv]
      _ ≤ (D * (1 + ‖s • (t • v)‖) ^ k) * ‖t • v‖ := by
            gcongr
      _ ≤ (D * (1 + ‖v‖) ^ k) * ‖t • v‖ := by
            gcongr
      _ = (D * (1 + ‖v‖) ^ k) * (|t| * ‖v‖) := by
            rw [norm_smul, Real.norm_eq_abs]
      _ = C * |t| := by
            dsimp [C]
            ring
  have hmv :=
    norm_image_sub_le_of_norm_deriv_le_segment_01'
      (f := hxFun)
      (f' := fun s => ‖x‖ ^ k • (fderiv ℝ H (x + s • (t • v)) (t • v)))
      (fun s hs => (hxFun_hasDeriv s).hasDerivWithinAt)
      hxFun_bound
  have hiter_eq :
      iteratedFDeriv ℝ n (⇑(SCV.translateSchwartz (t • v) g - g)) x =
        H (x + t • v) - H x := by
    have hf : ContDiff ℝ n (⇑(SCV.translateSchwartz (t • v) g)) :=
      (SCV.translateSchwartz (t • v) g).smooth n
    have hg : ContDiff ℝ n (⇑g) := g.smooth n
    have hfg :
        (⇑(SCV.translateSchwartz (t • v) g - g) : (Fin m → ℝ) → ℂ) =
          (⇑(SCV.translateSchwartz (t • v) g)) + fun z => -(⇑g z) := by
      ext z
      simp [sub_eq_add_neg]
    have hneg : (fun z => -(⇑g z)) = -⇑g := rfl
    rw [hfg, iteratedFDeriv_add_apply hf.contDiffAt hg.neg.contDiffAt, hneg, iteratedFDeriv_neg_apply]
    have htrans :
        iteratedFDeriv ℝ n (⇑(SCV.translateSchwartz (t • v) g)) x =
          H (x + t • v) := by
      change iteratedFDeriv ℝ n (fun z => g (z + t • v)) x = _
      exact iteratedFDeriv_comp_add_right
        (f := (g : (Fin m → ℝ) → ℂ)) n (t • v) x
    simp [H, htrans, sub_eq_add_neg]
  have hxFun_diff :
      hxFun 1 - hxFun 0 = ‖x‖ ^ k • (H (x + t • v) - H x) := by
    simp [hxFun, smul_sub]
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑(SCV.translateSchwartz (t • v) g - g)) x‖
        = ‖hxFun 1 - hxFun 0‖ := by
            rw [hxFun_diff, hiter_eq, norm_smul, Real.norm_eq_abs]
            have hxpow_nonneg : 0 ≤ ‖x‖ ^ k := by positivity
            simp [abs_of_nonneg hxpow_nonneg]
    _ ≤ C * |t| := by simpa [sub_eq_add_neg] using hmv

/-- Directional derivatives of Schwartz functions commute. -/
theorem lineDerivOp_comm {m : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (v w : Fin m → ℝ) :
    ∂_{v} ((∂_{w} f : SchwartzMap (Fin m → ℝ) ℂ)) =
      ∂_{w} ((∂_{v} f : SchwartzMap (Fin m → ℝ) ℂ)) := by
  ext x
  have hsym :=
    (f.contDiffAt (2 : ℕ∞) (x := x)).isSymmSndFDerivAt
      (n := (2 : WithTop ℕ∞)) (by simp)
  calc
    (∂_{v} ((∂_{w} f : SchwartzMap (Fin m → ℝ) ℂ))) x = (∂^{![v, w]} f) x := by
      simp [LineDeriv.iteratedLineDerivOp_succ_left]
    _ = iteratedFDeriv ℝ 2 (f : (Fin m → ℝ) → ℂ) x ![v, w] := by
      simpa using
        (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
          (f := f) (m := ![v, w]) (x := x))
    _ = iteratedFDeriv ℝ 2 (f : (Fin m → ℝ) → ℂ) x ![w, v] := by
      exact hsym.iteratedFDeriv_cons
    _ = (∂^{![w, v]} f) x := by
      simpa using
        (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
          (f := f) (m := ![w, v]) (x := x)).symm
    _ = (∂_{w} ((∂_{v} f : SchwartzMap (Fin m → ℝ) ℂ))) x := by
      simp [LineDeriv.iteratedLineDerivOp_succ_left]

/-- A single directional derivative commutes past an iterated directional derivative. -/
theorem lineDerivOp_iterated_comm {m n : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (v : Fin m → ℝ) (u : Fin n → Fin m → ℝ) :
    ∂_{v} (∂^{u} f) = ∂^{u} (∂_{v} f) := by
  induction n generalizing f with
  | zero =>
      ext x
      simp [LineDeriv.iteratedLineDerivOp_fin_zero]
  | succ n ih =>
      rw [LineDeriv.iteratedLineDerivOp_succ_right,
        LineDeriv.iteratedLineDerivOp_succ_right]
      rw [ih (f := ∂_{u (Fin.last n)} f)]
      congr 1
      exact lineDerivOp_comm f v (u (Fin.last n))

/-- Differentiating the `n`-th iterated derivative of a Schwartz function in the
direction `v` agrees with taking the `n`-th iterated derivative of `∂_{v} f`. -/
theorem fderiv_iteratedFDeriv_eq_iteratedFDeriv_lineDeriv {m n : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (v x : Fin m → ℝ) :
    fderiv ℝ (iteratedFDeriv ℝ n (f : (Fin m → ℝ) → ℂ)) x v =
      iteratedFDeriv ℝ n (((∂_{v} f : SchwartzMap (Fin m → ℝ) ℂ) : (Fin m → ℝ) → ℂ)) x := by
  ext u
  calc
    (fderiv ℝ (iteratedFDeriv ℝ n (f : (Fin m → ℝ) → ℂ)) x v) u
        = iteratedFDeriv ℝ (n + 1) (f : (Fin m → ℝ) → ℂ) x (Fin.cons v u) := by
            simp [iteratedFDeriv_succ_apply_left]
    _ = (∂^{Fin.cons v u} f) x := by
            symm
            simpa using
              (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
                (f := f) (m := Fin.cons v u) (x := x))
    _ = (∂_{v} (∂^{u} f)) x := by
            simpa using (congrArg (fun g : SchwartzMap (Fin m → ℝ) ℂ => g x)
              (LineDeriv.iteratedLineDerivOp_succ_left (m := Fin.cons v u) (f := f)))
    _ = (∂^{u} (∂_{v} f)) x := by
            rw [lineDerivOp_iterated_comm (f := f) (v := v) (u := u)]
    _ = iteratedFDeriv ℝ n
          (((∂_{v} f : SchwartzMap (Fin m → ℝ) ℂ) : (Fin m → ℝ) → ℂ)) x u := by
            simpa using
              (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
                (f := (∂_{v} f : SchwartzMap (Fin m → ℝ) ℂ)) (m := u) (x := x))

/-- The key first-order translation estimate behind the derivative route:
every Schwartz seminorm of the translation difference quotient error should be
`O(|t|)` near `0`. -/
theorem exists_seminorm_diffQuotient_translateSchwartz_sub_lineDeriv_le {m : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (v : Fin m → ℝ) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, t ≠ 0 → |t| ≤ 1 →
        SchwartzMap.seminorm ℝ k n
          (t⁻¹ • (SCV.translateSchwartz (t • v) f - f) - ∂_{v} f) ≤ C * |t| := by
  let g : SchwartzMap (Fin m → ℝ) ℂ := ∂_{v} f
  obtain ⟨C, hC_nonneg, hC⟩ := exists_seminorm_translateSchwartz_sub_le_linear g v k n
  refine ⟨C, hC_nonneg, ?_⟩
  intro t ht_ne ht_abs
  refine SchwartzMap.seminorm_le_bound ℝ k n
    (t⁻¹ • (SCV.translateSchwartz (t • v) f - f) - ∂_{v} f)
    (by positivity) ?_
  intro x
  let H :
      (Fin m → ℝ) →
        ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ :=
    iteratedFDeriv ℝ n (f : (Fin m → ℝ) → ℂ)
  let K :
      (Fin m → ℝ) →
        ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ :=
    iteratedFDeriv ℝ n (g : (Fin m → ℝ) → ℂ)
  let ψ : ℝ →
      ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ :=
    fun s => ‖x‖ ^ k • (t⁻¹ • H (x + s • (t • v)) - t⁻¹ • H x) - ‖x‖ ^ k • (s • K x)
  have hH_diff : Differentiable ℝ H := by
    simpa [H] using
      (f.smooth (n + 1)).differentiable_iteratedFDeriv (by
        exact_mod_cast Nat.lt_succ_self n)
  have hpsi_hasDeriv :
      ∀ s : ℝ,
        HasDerivAt ψ (‖x‖ ^ k • (K (x + s • (t • v)) - K x)) s := by
    intro s
    have hgamma :
        HasDerivAt (fun r : ℝ => x + r • (t • v)) (t • v) s := by
      let L : ℝ →L[ℝ] (Fin m → ℝ) :=
        ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (t • v)
      simpa [L, ContinuousLinearMap.smulRight_apply, one_smul, add_comm, add_left_comm, add_assoc]
        using (L.hasDerivAt).const_add x
    have hcomp :
        HasDerivAt (fun r : ℝ => H (x + r • (t • v)))
          ((fderiv ℝ H (x + s • (t • v))) (t • v)) s := by
      exact (hH_diff (x + s • (t • v))).hasFDerivAt.comp_hasDerivAt s hgamma
    have hmain0 :
        HasDerivAt
          (fun r : ℝ => t⁻¹ • H (x + r • (t • v)) - t⁻¹ • H x)
          (t⁻¹ • ((fderiv ℝ H (x + s • (t • v))) (t • v))) s := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_sub] using
        (hcomp.const_smul t⁻¹).sub_const (t⁻¹ • H x)
    have hscale :
        t⁻¹ • ((fderiv ℝ H (x + s • (t • v))) (t • v)) =
          K (x + s • (t • v)) := by
      calc
        t⁻¹ • ((fderiv ℝ H (x + s • (t • v))) (t • v))
            = t⁻¹ • (t • ((fderiv ℝ H (x + s • (t • v))) v)) := by
                rw [ContinuousLinearMap.map_smul]
        _ = (t⁻¹ * t) • ((fderiv ℝ H (x + s • (t • v))) v) := by
                rw [smul_smul]
        _ = (fderiv ℝ H (x + s • (t • v))) v := by
                rw [inv_mul_cancel₀ ht_ne, one_smul]
        _ = K (x + s • (t • v)) := by
                rw [fderiv_iteratedFDeriv_eq_iteratedFDeriv_lineDeriv
                  (f := f) (v := v) (x := x + s • (t • v))]
    have hlin :
        HasDerivAt (fun r : ℝ => r • K x) (K x) s := by
      simpa [one_smul] using (hasDerivAt_id s).smul_const (K x)
    have hsub' :
        HasDerivAt
          (fun r : ℝ =>
            ‖x‖ ^ k • (t⁻¹ • H (x + r • (t • v)) - t⁻¹ • H x) - ‖x‖ ^ k • (r • K x))
          (‖x‖ ^ k • (t⁻¹ • ((fderiv ℝ H (x + s • (t • v))) (t • v))) - ‖x‖ ^ k • K x) s := by
      exact (hmain0.const_smul (‖x‖ ^ k)).sub (hlin.const_smul (‖x‖ ^ k))
    have hsub :
        HasDerivAt
          (fun r : ℝ =>
            ‖x‖ ^ k • (t⁻¹ • H (x + r • (t • v)) - t⁻¹ • H x) - ‖x‖ ^ k • (r • K x))
          (‖x‖ ^ k • (K (x + s • (t • v)) - K x)) s := by
      convert hsub' using 1
      calc
        ‖x‖ ^ k • (K (x + s • (t • v)) - K x)
            = ‖x‖ ^ k • K (x + s • (t • v)) - ‖x‖ ^ k • K x := by
                rw [smul_sub]
        _ = ‖x‖ ^ k • (t⁻¹ • ((fderiv ℝ H (x + s • (t • v))) (t • v))) - ‖x‖ ^ k • K x := by
                rw [hscale]
    exact hsub
  have hpsi_bound :
      ∀ s ∈ Set.Ico (0 : ℝ) 1,
        ‖‖x‖ ^ k • (K (x + s • (t • v)) - K x)‖ ≤ C * |t| := by
    intro s hs
    have hs_nonneg : 0 ≤ s := hs.1
    have hs_le_one : s ≤ 1 := le_of_lt hs.2
    have hs_abs : |s| ≤ 1 := by
      rw [abs_of_nonneg hs_nonneg]
      exact hs_le_one
    have hst_abs : |s * t| ≤ 1 := by
      calc
        |s * t| = |s| * |t| := by rw [abs_mul]
        _ ≤ 1 * 1 := by gcongr
        _ = 1 := by ring
    have hiter_eq :
        iteratedFDeriv ℝ n (⇑(SCV.translateSchwartz ((s * t) • v) g - g)) x =
          K (x + s • (t • v)) - K x := by
      have hshift :
          iteratedFDeriv ℝ n (⇑(SCV.translateSchwartz ((s * t) • v) g)) x =
            K (x + s • (t • v)) := by
        change iteratedFDeriv ℝ n (fun z => g (z + (s * t) • v)) x = _
        simpa [K, smul_smul, mul_comm, mul_left_comm, mul_assoc] using
          (iteratedFDeriv_comp_add_right
            (f := (g : (Fin m → ℝ) → ℂ)) n ((s * t) • v) x)
      rw [show (⇑(SCV.translateSchwartz ((s * t) • v) g - g) : (Fin m → ℝ) → ℂ) =
            (⇑(SCV.translateSchwartz ((s * t) • v) g)) + fun z => -(⇑g z) by
              ext z; simp [sub_eq_add_neg]]
      rw [iteratedFDeriv_add_apply
          ((SCV.translateSchwartz ((s * t) • v) g).smooth n).contDiffAt
          (g.smooth n).neg.contDiffAt]
      rw [show (fun z => -(⇑g z)) = -⇑g by rfl, iteratedFDeriv_neg_apply]
      simp [K, hshift, sub_eq_add_neg]
    have hpoint :
        ‖x‖ ^ k * ‖K (x + s • (t • v)) - K x‖ ≤ C * |s * t| := by
      calc
        ‖x‖ ^ k * ‖K (x + s • (t • v)) - K x‖
            = ‖x‖ ^ k *
                ‖iteratedFDeriv ℝ n (⇑(SCV.translateSchwartz ((s * t) • v) g - g)) x‖ := by
                  rw [hiter_eq]
        _ ≤ SchwartzMap.seminorm ℝ k n (SCV.translateSchwartz ((s * t) • v) g - g) := by
              exact SchwartzMap.le_seminorm ℂ k n _ x
        _ ≤ C * |s * t| := hC (s * t) hst_abs
    calc
      ‖‖x‖ ^ k • (K (x + s • (t • v)) - K x)‖
          = ‖x‖ ^ k * ‖K (x + s • (t • v)) - K x‖ := by
              rw [norm_smul, Real.norm_eq_abs]
              have hxpow_nonneg : 0 ≤ ‖x‖ ^ k := by positivity
              simp [abs_of_nonneg hxpow_nonneg]
      _ ≤ C * |s * t| := hpoint
      _ = C * (|s| * |t|) := by rw [abs_mul]
      _ ≤ C * |t| := by
            have hs_t : |s| * |t| ≤ |t| := by
              simpa [one_mul] using
                (mul_le_mul_of_nonneg_right hs_abs (abs_nonneg t))
            gcongr
  have hmv :=
    norm_image_sub_le_of_norm_deriv_le_segment_01'
      (hf := fun s hs => (hpsi_hasDeriv s).hasDerivWithinAt)
      (bound := hpsi_bound)
  have htarget :
      iteratedFDeriv ℝ n
        (↑(t⁻¹ • (SCV.translateSchwartz (t • v) f - f) - ∂_{v} f) :
          (Fin m → ℝ) → ℂ) x =
        t⁻¹ • (H (x + t • v) - H x) - K x := by
    have hshift_sub :
        iteratedFDeriv ℝ n (⇑(SCV.translateSchwartz (t • v) f - f)) x =
          H (x + t • v) - H x := by
      have hshift :
          iteratedFDeriv ℝ n (⇑(SCV.translateSchwartz (t • v) f)) x = H (x + t • v) := by
        change iteratedFDeriv ℝ n (fun z => f (z + t • v)) x = _
        exact iteratedFDeriv_comp_add_right
          (f := (f : (Fin m → ℝ) → ℂ)) n (t • v) x
      rw [show (⇑(SCV.translateSchwartz (t • v) f - f) : (Fin m → ℝ) → ℂ) =
            (⇑(SCV.translateSchwartz (t • v) f)) + fun z => -(⇑f z) by
              ext z; simp [sub_eq_add_neg]]
      rw [iteratedFDeriv_add_apply ((SCV.translateSchwartz (t • v) f).smooth n).contDiffAt
          (f.smooth n).neg.contDiffAt]
      rw [show (fun z => -(⇑f z)) = -⇑f by rfl, iteratedFDeriv_neg_apply]
      simp [H, hshift, sub_eq_add_neg]
    change
      iteratedFDeriv ℝ n
        (⇑(t⁻¹ • (SCV.translateSchwartz (t • v) f - f)) + fun z => -((g : (Fin m → ℝ) → ℂ) z)) x =
        t⁻¹ • (H (x + t • v) - H x) - K x
    rw [iteratedFDeriv_add_apply
      ((t⁻¹ • (SCV.translateSchwartz (t • v) f - f)).smooth n).contDiffAt
      (g.smooth n).neg.contDiffAt]
    have hsc :
        iteratedFDeriv ℝ n (⇑(t⁻¹ • (SCV.translateSchwartz (t • v) f - f))) x =
          t⁻¹ • iteratedFDeriv ℝ n (⇑(SCV.translateSchwartz (t • v) f - f)) x := by
      change iteratedFDeriv ℝ n (t⁻¹ • (⇑(SCV.translateSchwartz (t • v) f - f))) x =
        t⁻¹ • iteratedFDeriv ℝ n (⇑(SCV.translateSchwartz (t • v) f - f)) x
      rw [iteratedFDeriv_const_smul_apply ((SCV.translateSchwartz (t • v) f - f).smooth n).contDiffAt]
    have hneg :
        iteratedFDeriv ℝ n (fun z => -((g : (Fin m → ℝ) → ℂ) z)) x = - K x := by
      change iteratedFDeriv ℝ n (-(g : (Fin m → ℝ) → ℂ)) x = _
      simpa [K] using
        (iteratedFDeriv_neg_apply (𝕜 := ℝ) (i := n)
          (f := (g : (Fin m → ℝ) → ℂ)) (x := x))
    rw [hsc, hneg, hshift_sub]
    simp [sub_eq_add_neg, add_left_comm, add_comm]
  have hψ0 : ψ 0 = 0 := by
    ext u
    simp [ψ]
  have hψ1 :
      ψ 1 =
        ‖x‖ ^ k •
          iteratedFDeriv ℝ n
            (↑(t⁻¹ • (SCV.translateSchwartz (t • v) f - f) - ∂_{v} f) :
              (Fin m → ℝ) → ℂ) x := by
    rw [show ψ 1 =
          ‖x‖ ^ k • (t⁻¹ • (H (x + t • v) - H x) - K x) by
            simp [ψ, sub_eq_add_neg, add_left_comm, add_comm]]
    rw [htarget]
  calc
    ‖x‖ ^ k *
        ‖iteratedFDeriv ℝ n
          (↑(t⁻¹ • (SCV.translateSchwartz (t • v) f - f) - ∂_{v} f) :
            (Fin m → ℝ) → ℂ) x‖
        = ‖ψ 1 - ψ 0‖ := by
            rw [hψ0, hψ1, sub_zero, norm_smul, Real.norm_eq_abs]
            have hxpow_nonneg : 0 ≤ ‖x‖ ^ k := by positivity
            simp [abs_of_nonneg hxpow_nonneg]
    _ ≤ C * |t| := hmv

noncomputable def unitBumpSchwartz : SchwartzMap ℝ ℂ := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let f : ℝ → ℂ := fun x => (b x : ℂ)
  have hf_smooth : ContDiff ℝ (⊤ : ENat) f := by
    exact (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff
  have hf_compact : HasCompactSupport f :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  exact hf_compact.toSchwartzMap hf_smooth

theorem unitBumpSchwartz_zero : unitBumpSchwartz 0 = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  have hf_smooth : ContDiff ℝ (⊤ : ENat) (fun x : ℝ => (b x : ℂ)) := by
    exact (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff
  have hf_compact : HasCompactSupport (fun x : ℝ => (b x : ℂ)) :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  have happly :
      unitBumpSchwartz 0 = ((fun x : ℝ => (b x : ℂ)) 0) := by
    simpa [unitBumpSchwartz, b] using
      (HasCompactSupport.toSchwartzMap_toFun hf_compact hf_smooth 0)
  rw [happly]
  have hball : (0 : ℝ) ∈ Metric.closedBall (0 : ℝ) (1 : ℝ) := by
    simp [Metric.mem_closedBall]
  exact congrArg (fun r : ℝ => (r : ℂ)) (b.one_of_mem_closedBall hball)

noncomputable def unitBallBumpSchwartzPi (m : ℕ) :
    SchwartzMap (Fin m → ℝ) ℂ := by
  let b : ContDiffBump (0 : Fin m → ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let f : (Fin m → ℝ) → ℂ := fun x => (b x : ℂ)
  have hf_smooth : ContDiff ℝ (⊤ : ENat) f := by
    exact (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff
  have hf_compact : HasCompactSupport f :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  exact hf_compact.toSchwartzMap hf_smooth

theorem unitBallBumpSchwartzPi_one_of_mem_closedBall {m : ℕ}
    {x : Fin m → ℝ} (hx : x ∈ Metric.closedBall (0 : Fin m → ℝ) 1) :
    unitBallBumpSchwartzPi m x = 1 := by
  let b : ContDiffBump (0 : Fin m → ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let f : (Fin m → ℝ) → ℂ := fun y => (b y : ℂ)
  have hf_smooth : ContDiff ℝ (⊤ : ENat) f := by
    exact (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff
  have hf_compact : HasCompactSupport f :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  have happly :
      unitBallBumpSchwartzPi m x = f x := by
    simpa [unitBallBumpSchwartzPi, b, f] using
      (HasCompactSupport.toSchwartzMap_toFun hf_compact hf_smooth x)
  rw [happly]
  exact congrArg (fun r : ℝ => (r : ℂ)) (b.one_of_mem_closedBall hx)

theorem hasCompactSupport_unitBallBumpSchwartzPi (m : ℕ) :
    HasCompactSupport ((unitBallBumpSchwartzPi m : SchwartzMap (Fin m → ℝ) ℂ) :
      (Fin m → ℝ) → ℂ) := by
  let b : ContDiffBump (0 : Fin m → ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let f : (Fin m → ℝ) → ℂ := fun x => (b x : ℂ)
  have hf_smooth : ContDiff ℝ (⊤ : ENat) f := by
    exact (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff
  have hf_compact : HasCompactSupport f :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  rw [show (⇑(unitBallBumpSchwartzPi m) : (Fin m → ℝ) → ℂ) = f by
    funext x
    exact HasCompactSupport.toSchwartzMap_toFun hf_compact hf_smooth x]
  exact hf_compact

/-- The unit-ball Schwartz bump rescaled to radius `R`. -/
noncomputable def unitBallBumpSchwartzPiRadius (m : ℕ) (R : ℝ) (hR : 0 < R) :
    SchwartzMap (Fin m → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft (Units.mk0 R hR.ne')).symm
    (unitBallBumpSchwartzPi m)

@[simp] theorem unitBallBumpSchwartzPiRadius_apply {m : ℕ} (R : ℝ) (hR : 0 < R)
    (x : Fin m → ℝ) :
    unitBallBumpSchwartzPiRadius m R hR x =
      unitBallBumpSchwartzPi m (R⁻¹ • x) := by
  rw [unitBallBumpSchwartzPiRadius, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  have hsmul :
      (((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Fin m → ℝ)
          (Units.mk0 R hR.ne')).symm) x) = R⁻¹ • x := by
    rw [show (((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Fin m → ℝ)
          (Units.mk0 R hR.ne')).symm) x) = ((↑((Units.mk0 R hR.ne')⁻¹) : ℝ) • x) by rfl]
    simp [Units.val_inv_eq_inv_val]
  simpa [Function.comp] using congrArg (unitBallBumpSchwartzPi m) hsmul

theorem unitBallBumpSchwartzPiRadius_one_of_mem_closedBall {m : ℕ}
    {R : ℝ} (hR : 0 < R) {x : Fin m → ℝ}
    (hx : x ∈ Metric.closedBall (0 : Fin m → ℝ) R) :
    unitBallBumpSchwartzPiRadius m R hR x = 1 := by
  rw [unitBallBumpSchwartzPiRadius_apply]
  apply unitBallBumpSchwartzPi_one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_eq_norm] at hx ⊢
  have hx' : ‖x‖ ≤ R := by simpa using hx
  have hscaled : R⁻¹ * ‖x‖ ≤ 1 := by
    rw [inv_mul_le_iff₀ hR]
    simpa using hx'
  have hRinv_nonneg : 0 ≤ R⁻¹ := inv_nonneg.mpr hR.le
  simpa [norm_smul, Real.norm_of_nonneg hRinv_nonneg] using hscaled

theorem hasCompactSupport_unitBallBumpSchwartzPiRadius (m : ℕ) (R : ℝ) (hR : 0 < R) :
    HasCompactSupport ((unitBallBumpSchwartzPiRadius m R hR :
      SchwartzMap (Fin m → ℝ) ℂ) : (Fin m → ℝ) → ℂ) := by
  change HasCompactSupport
    ((unitBallBumpSchwartzPi m : (Fin m → ℝ) → ℂ) ∘ fun x => R⁻¹ • x)
  exact (hasCompactSupport_unitBallBumpSchwartzPi m).comp_homeomorph
    ((Homeomorph.smulOfNeZero R hR.ne').symm)

theorem hasCompactSupport_cutoff_mul_radius {m : ℕ}
    (R : ℝ) (hR : 0 < R) (f : SchwartzMap (Fin m → ℝ) ℂ) :
    HasCompactSupport
      ((SchwartzMap.smulLeftCLM ℂ (unitBallBumpSchwartzPiRadius m R hR)
        f : SchwartzMap (Fin m → ℝ) ℂ) : (Fin m → ℝ) → ℂ) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (hasCompactSupport_unitBallBumpSchwartzPiRadius m R hR).isCompact ?_
  intro x hx
  exact (SchwartzMap.tsupport_smulLeftCLM_subset
    (g := unitBallBumpSchwartzPiRadius m R hR) (f := f) (subset_tsupport _ hx)).2

theorem cutoff_compl_eq_zero_on_closedBall_radius {m : ℕ}
    (R : ℝ) (hR : 0 < R) (f : SchwartzMap (Fin m → ℝ) ℂ)
    {x : Fin m → ℝ} (hx : x ∈ Metric.closedBall (0 : Fin m → ℝ) R) :
    (f - SchwartzMap.smulLeftCLM ℂ (unitBallBumpSchwartzPiRadius m R hR) f) x = 0 := by
  have hψ : unitBallBumpSchwartzPiRadius m R hR x = 1 :=
    unitBallBumpSchwartzPiRadius_one_of_mem_closedBall hR hx
  have hsmul :
      (SchwartzMap.smulLeftCLM ℂ (unitBallBumpSchwartzPiRadius m R hR) f) x = f x := by
    rw [SchwartzMap.smulLeftCLM_apply_apply]
    · simp [hψ]
    · exact (unitBallBumpSchwartzPiRadius m R hR).hasTemperateGrowth
  simp [hsmul]

theorem iteratedFDeriv_cutoff_compl_radius_add_one_eq_zero_on_closedBall {m l : ℕ}
    (R : ℝ) (hR : 0 < R) (f : SchwartzMap (Fin m → ℝ) ℂ)
    {x : Fin m → ℝ} (hx : x ∈ Metric.closedBall (0 : Fin m → ℝ) R) :
    iteratedFDeriv ℝ l
      (⇑(f - SchwartzMap.smulLeftCLM ℂ
        (unitBallBumpSchwartzPiRadius m (R + 1) (add_pos hR zero_lt_one)) f)) x = 0 := by
  let g : (Fin m → ℝ) → ℂ :=
    ⇑(f - SchwartzMap.smulLeftCLM ℂ
      (unitBallBumpSchwartzPiRadius m (R + 1) (add_pos hR zero_lt_one)) f)
  have hEq : g =ᶠ[𝓝 x] fun _ : Fin m → ℝ => (0 : ℂ) := by
    refine Filter.mem_of_superset
      (Metric.ball_mem_nhds x (show 0 < (1 : ℝ) / 2 by positivity)) ?_
    intro y hy
    have hy_norm : ‖y‖ ≤ R + 1 := by
      have hy_dist : ‖y - x‖ < (1 : ℝ) / 2 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hy
      have hx_norm : ‖x‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hx
      have htri : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using norm_add_le (y - x) x
      linarith
    have hy_ball : y ∈ Metric.closedBall (0 : Fin m → ℝ) (R + 1) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hy_norm
    exact cutoff_compl_eq_zero_on_closedBall_radius (R := R + 1) (hR := add_pos hR zero_lt_one)
      (f := f) hy_ball
  have hx0 : g x = 0 := hEq.eq_of_nhds
  have hiter :
      iteratedFDeriv ℝ l g x = 0 := by
    have hiterWithin :
        iteratedFDerivWithin ℝ l g Set.univ x =
          iteratedFDerivWithin ℝ l (fun _ : Fin m → ℝ => (0 : ℂ)) Set.univ x :=
      (hEq.filter_mono inf_le_left).iteratedFDerivWithin_eq hx0 l
    simpa [iteratedFDerivWithin_univ, iteratedFDeriv_zero_fun] using hiterWithin
  simpa [g] using hiter

private theorem norm_iteratedFDeriv_cutoff_compl_radius_le_uniform {m n : ℕ} :
    ∃ (a : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (R : ℝ) (hR : 0 < R) (N : ℕ), N ≤ n → ∀ x : Fin m → ℝ,
        ‖iteratedFDeriv ℝ N
          (fun y : Fin m → ℝ =>
            (1 : ℂ) - unitBallBumpSchwartzPiRadius m (R + 1) (add_pos hR zero_lt_one) y) x‖ ≤
          C * (1 + ‖x‖) ^ a := by
  let ψ : (Fin m → ℝ) → ℂ := fun y => (1 : ℂ) - unitBallBumpSchwartzPi m y
  have hψ : ψ.HasTemperateGrowth := by
    change ((fun _ : Fin m → ℝ => (1 : ℂ)) -
      (unitBallBumpSchwartzPi m : (Fin m → ℝ) → ℂ)).HasTemperateGrowth
    exact (Function.HasTemperateGrowth.const (1 : ℂ)).sub
      (unitBallBumpSchwartzPi m).hasTemperateGrowth
  obtain ⟨a, C, hC, hψbound⟩ := hψ.norm_iteratedFDeriv_le_uniform n
  refine ⟨a, C, hC, ?_⟩
  intro R hR N hN x
  let ρ : ℝ := R + 1
  have hρ : 0 < ρ := add_pos hR zero_lt_one
  let e :
      (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) :=
    (((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Fin m → ℝ)
      (Units.mk0 ρ hρ.ne')).symm) : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ)).toContinuousLinearMap
  have he_apply (y : Fin m → ℝ) : e y = ρ⁻¹ • y := by
    change
      (((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Fin m → ℝ)
        (Units.mk0 ρ hρ.ne')).symm) y) = ρ⁻¹ • y
    rw [show
      (((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Fin m → ℝ)
        (Units.mk0 ρ hρ.ne')).symm) y) =
        ((↑((Units.mk0 ρ hρ.ne')⁻¹) : ℝ) • y) by rfl]
    simp [Units.val_inv_eq_inv_val]
  have he_norm_le : ‖e‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound e zero_le_one ?_
    intro y
    calc
      ‖e y‖ = ‖ρ⁻¹ • y‖ := by rw [he_apply]
      _ = ‖ρ⁻¹‖ * ‖y‖ := norm_smul _ _
      _ ≤ 1 * ‖y‖ := by
            gcongr
            · rw [Real.norm_of_nonneg (inv_nonneg.mpr hρ.le)]
              exact inv_le_one_of_one_le₀ (by linarith : 1 ≤ ρ)
  have hcomp :
      (fun y : Fin m → ℝ =>
        (1 : ℂ) - unitBallBumpSchwartzPiRadius m ρ hρ y) = ψ ∘ e := by
    funext y
    simp [ψ, unitBallBumpSchwartzPiRadius_apply, he_apply, Function.comp]
  have hitercomp :
      iteratedFDeriv ℝ N (ψ ∘ e) x =
        (iteratedFDeriv ℝ N ψ (e x)).compContinuousLinearMap (fun _ : Fin N => e) := by
    simpa using e.iteratedFDeriv_comp_right
      (f := ψ) hψ.1 (x := x) (i := N) (by exact_mod_cast le_top)
  rw [hcomp, hitercomp]
  have hprod_le : ∏ _ : Fin N, ‖e‖ ≤ 1 := by
    simpa [Finset.prod_const] using Finset.prod_le_one (s := (Finset.univ : Finset (Fin N)))
      (fun _ _ => norm_nonneg _)
      (fun _ _ => he_norm_le)
  calc
    ‖(iteratedFDeriv ℝ N ψ (e x)).compContinuousLinearMap (fun _ : Fin N => e)‖
        ≤ ‖iteratedFDeriv ℝ N ψ (e x)‖ * ∏ _ : Fin N, ‖e‖ := by
          exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ N ψ (e x)‖ * 1 := by
          exact mul_le_mul_of_nonneg_left hprod_le (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ N ψ (e x)‖ := by ring
    _ ≤ C * (1 + ‖e x‖) ^ a := hψbound N hN (e x)
    _ ≤ C * (1 + ‖x‖) ^ a := by
          gcongr
          calc
            ‖e x‖ = ‖ρ⁻¹ • x‖ := by rw [he_apply]
            _ = ‖ρ⁻¹‖ * ‖x‖ := norm_smul _ _
            _ ≤ 1 * ‖x‖ := by
                  gcongr
                  · rw [Real.norm_of_nonneg (inv_nonneg.mpr hρ.le)]
                    exact inv_le_one_of_one_le₀ (by linarith : 1 ≤ ρ)
            _ = ‖x‖ := by ring

/-- Uniform Schwartz seminorm bound for the cutoff complements `f - χ_R f`. -/
theorem smulLeftCLM_cutoff_compl_uniform_seminorm_bound {m : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ) (k l : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (R : ℝ) (hR : 0 < R),
      (SchwartzMap.seminorm ℝ k l)
        (f - SchwartzMap.smulLeftCLM ℂ
          (unitBallBumpSchwartzPiRadius m (R + 1) (add_pos hR zero_lt_one)) f) ≤ M := by
  obtain ⟨a, C, hC, hψbound⟩ :=
    norm_iteratedFDeriv_cutoff_compl_radius_le_uniform (m := m) (n := l)
  let M : ℝ :=
    (((l : ℝ) + 1) * (Nat.choose l (l / 2) : ℝ) * (C * 2 ^ (a + k))) *
      (Finset.Iic (a + k, l)).sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ) f
  refine ⟨M, by positivity, ?_⟩
  intro R hR
  let ψR : (Fin m → ℝ) → ℂ := fun y =>
    (1 : ℂ) - unitBallBumpSchwartzPiRadius m (R + 1) (add_pos hR zero_lt_one) y
  have hψR_temp : ψR.HasTemperateGrowth := by
    change ((fun _ : Fin m → ℝ => (1 : ℂ)) -
      (unitBallBumpSchwartzPiRadius m (R + 1) (add_pos hR zero_lt_one) :
        (Fin m → ℝ) → ℂ)).HasTemperateGrowth
    exact (Function.HasTemperateGrowth.const (1 : ℂ)).sub
      (unitBallBumpSchwartzPiRadius m (R + 1)
        (add_pos hR zero_lt_one)).hasTemperateGrowth
  have hEq :
      f - SchwartzMap.smulLeftCLM ℂ
        (unitBallBumpSchwartzPiRadius m (R + 1) (add_pos hR zero_lt_one)) f =
      SchwartzMap.smulLeftCLM ℂ ψR f := by
    ext x
    have hleft :
        (SchwartzMap.smulLeftCLM ℂ
          (unitBallBumpSchwartzPiRadius m (R + 1) (add_pos hR zero_lt_one)) f) x =
          unitBallBumpSchwartzPiRadius m (R + 1) (add_pos hR zero_lt_one) x * f x := by
      simpa [smul_eq_mul] using
        (SchwartzMap.smulLeftCLM_apply_apply
          (unitBallBumpSchwartzPiRadius m (R + 1) (add_pos hR zero_lt_one)).hasTemperateGrowth
          f x)
    have hright :
        (SchwartzMap.smulLeftCLM ℂ ψR f) x = ψR x * f x := by
      simpa [smul_eq_mul] using
        (SchwartzMap.smulLeftCLM_apply_apply hψR_temp f x)
    calc
      (f - SchwartzMap.smulLeftCLM ℂ
        (unitBallBumpSchwartzPiRadius m (R + 1) (add_pos hR zero_lt_one)) f) x
          = f x - unitBallBumpSchwartzPiRadius m (R + 1) (add_pos hR zero_lt_one) x * f x := by
              simp [hleft]
      _ = ψR x * f x := by
            simp [ψR]
            ring
      _ = (SchwartzMap.smulLeftCLM ℂ ψR f) x := hright.symm
  rw [hEq]
  refine SchwartzMap.seminorm_le_bound ℝ k l (SchwartzMap.smulLeftCLM ℂ ψR f)
    (M := M) (by positivity) ?_
  intro x
  have hmul :=
    norm_iteratedFDeriv_smul_le (𝕜 := ℝ) hψR_temp.1 (f.smooth ⊤) x
      (n := l) (by exact_mod_cast le_top)
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (⇑(SchwartzMap.smulLeftCLM ℂ ψR f)) x‖
        = ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun y => ψR y * f y) x‖ := by
            simp [SchwartzMap.smulLeftCLM_apply hψR_temp, smul_eq_mul]
    _ ≤ ‖x‖ ^ k *
        ∑ i ∈ Finset.range (l + 1),
          (l.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψR x‖ *
            ‖iteratedFDeriv ℝ (l - i) (⇑f) x‖ := by
              exact mul_le_mul_of_nonneg_left hmul (by positivity)
    _ ≤ M := by
      rw [Finset.mul_sum]
      let B : ℝ :=
        (Nat.choose l (l / 2) : ℝ) * (C * 2 ^ (a + k)) *
          (Finset.Iic (a + k, l)).sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ) f
      have hsum :
          ∑ i ∈ Finset.range (l + 1),
            ‖x‖ ^ k * ((l.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψR x‖ *
              ‖iteratedFDeriv ℝ (l - i) (⇑f) x‖) ≤
            ∑ _i ∈ Finset.range (l + 1), B := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [Finset.mem_range_succ_iff] at hi
        specialize hψbound R hR i hi x
        have hpow :
            ‖x‖ ^ k * (1 + ‖x‖) ^ a ≤ (1 + ‖x‖) ^ (a + k) := by
          have hbase : ‖x‖ ≤ 1 + ‖x‖ := by
            nlinarith [norm_nonneg x]
          have hpowk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := by
            exact pow_le_pow_left₀ (norm_nonneg x) hbase k
          calc
            ‖x‖ ^ k * (1 + ‖x‖) ^ a ≤ (1 + ‖x‖) ^ k * (1 + ‖x‖) ^ a := by
              exact mul_le_mul_of_nonneg_right hpowk (by positivity)
            _ = (1 + ‖x‖) ^ a * (1 + ‖x‖) ^ k := by ring
            _ = (1 + ‖x‖) ^ (a + k) := by rw [pow_add]
        have hsup :
            (1 + ‖x‖) ^ (a + k) * ‖iteratedFDeriv ℝ (l - i) (⇑f) x‖ ≤
              2 ^ (a + k) *
                (Finset.Iic (a + k, l)).sup
                  (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ) f :=
          SchwartzMap.one_add_le_sup_seminorm_apply
            (𝕜 := ℝ) (m := (a + k, l)) (k := a + k) (n := l - i)
            le_rfl (by omega) f x
        have hmain :
            ‖x‖ ^ k * ‖iteratedFDeriv ℝ i ψR x‖ *
                ‖iteratedFDeriv ℝ (l - i) (⇑f) x‖ ≤
              (C * 2 ^ (a + k)) *
                (Finset.Iic (a + k, l)).sup
                  (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ) f := by
          calc
            ‖x‖ ^ k * ‖iteratedFDeriv ℝ i ψR x‖ *
                ‖iteratedFDeriv ℝ (l - i) (⇑f) x‖
                = (‖x‖ ^ k * ‖iteratedFDeriv ℝ (l - i) (⇑f) x‖) *
                    ‖iteratedFDeriv ℝ i ψR x‖ := by ring
            _ ≤ (‖x‖ ^ k * ‖iteratedFDeriv ℝ (l - i) (⇑f) x‖) *
                (C * (1 + ‖x‖) ^ a) := by
                  exact mul_le_mul_of_nonneg_left hψbound (by positivity)
            _ = C * ((‖x‖ ^ k * (1 + ‖x‖) ^ a) *
                ‖iteratedFDeriv ℝ (l - i) (⇑f) x‖) := by ring
            _ ≤ C * ((1 + ‖x‖) ^ (a + k) *
                ‖iteratedFDeriv ℝ (l - i) (⇑f) x‖) := by
                  exact mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_right hpow
                      (norm_nonneg (iteratedFDeriv ℝ (l - i) (⇑f) x)))
                    hC
            _ ≤ C * (2 ^ (a + k) *
                (Finset.Iic (a + k, l)).sup
                  (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ) f) := by
                    exact mul_le_mul_of_nonneg_left hsup hC
            _ = (C * 2 ^ (a + k)) *
                (Finset.Iic (a + k, l)).sup
                  (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ) f := by ring
        calc
          ‖x‖ ^ k * ((l.choose i : ℝ) * ‖iteratedFDeriv ℝ i ψR x‖ *
              ‖iteratedFDeriv ℝ (l - i) (⇑f) x‖)
              = (l.choose i : ℝ) *
                  (‖x‖ ^ k * ‖iteratedFDeriv ℝ i ψR x‖ *
                    ‖iteratedFDeriv ℝ (l - i) (⇑f) x‖) := by ring
          _ ≤ (Nat.choose l (l / 2) : ℝ) *
              (‖x‖ ^ k * ‖iteratedFDeriv ℝ i ψR x‖ *
                ‖iteratedFDeriv ℝ (l - i) (⇑f) x‖) := by
                  exact mul_le_mul_of_nonneg_right
                    (by exact_mod_cast i.choose_le_middle l) (by positivity)
          _ ≤ (Nat.choose l (l / 2) : ℝ) *
              ((C * 2 ^ (a + k)) *
                (Finset.Iic (a + k, l)).sup
                  (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ) f) := by
                    exact mul_le_mul_of_nonneg_left hmain (by positivity)
          _ = B := by simp [B, mul_assoc, mul_left_comm]
      refine hsum.trans ?_
      simp [B, M, mul_assoc, mul_left_comm, mul_comm]

theorem hasCompactSupport_prependField {n : ℕ}
    (φ : SchwartzMap ℝ ℂ) (g : SchwartzMap (Fin n → ℝ) ℂ)
    (hφ : HasCompactSupport φ) (hg : HasCompactSupport g) :
    HasCompactSupport (φ.prependField g) := by
  let K : Set (Fin (n + 1) → ℝ) :=
    (fun p : ℝ × (Fin n → ℝ) => (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ)) ''
      (tsupport φ ×ˢ tsupport g)
  have hKcompact : IsCompact K := by
    have hcont :
        Continuous (fun p : ℝ × (Fin n → ℝ) => (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ)) := by
      refine continuous_pi ?_
      intro j
      refine Fin.cases ?_ ?_ j
      · exact continuous_fst
      · intro i
        exact (continuous_apply i).comp continuous_snd
    simpa [K] using (hφ.isCompact.prod hg.isCompact).image hcont
  refine HasCompactSupport.of_support_subset_isCompact hKcompact ?_
  intro x hx
  rw [Function.mem_support] at hx
  have hφx : φ (x 0) ≠ 0 := by
    intro h0
    apply hx
    simp [SchwartzMap.prependField_apply, h0]
  have hgx : g (fun i : Fin n => x i.succ) ≠ 0 := by
    intro h0
    apply hx
    simp [SchwartzMap.prependField_apply, h0]
  refine ⟨(x 0, fun i : Fin n => x i.succ), ?_, ?_⟩
  · exact ⟨subset_tsupport _ (Function.mem_support.mpr hφx),
      subset_tsupport _ (Function.mem_support.mpr hgx)⟩
  · ext j
    refine Fin.cases ?_ ?_ j
    · simp
    · intro i
      simp

/-- Translation difference quotients converge to the directional derivative in
the Schwartz topology. -/
theorem tendsto_diffQuotient_translateSchwartz_zero {m : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (v : Fin m → ℝ) :
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (SCV.translateSchwartz (t • v) f - f))
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (𝓝 (∂_{v} f)) := by
  rw [(schwartz_withSeminorms ℝ (Fin m → ℝ) ℂ).tendsto_nhds _ _]
  intro p ε hε
  obtain ⟨C, hC_nonneg, hC⟩ :=
    exists_seminorm_diffQuotient_translateSchwartz_sub_lineDeriv_le f v p.1 p.2
  let δ : ℝ := min 1 (ε / (C + 1))
  have hδ_pos : 0 < δ := by
    have hC1 : 0 < C + 1 := by linarith
    have hquot : 0 < ε / (C + 1) := by positivity
    exact lt_min zero_lt_one hquot
  have hball :
      Metric.ball (0 : ℝ) δ ∩ ({0}ᶜ : Set ℝ) ∈ nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ) := by
    simpa [Set.inter_comm] using
      (inter_mem_nhdsWithin ({0}ᶜ : Set ℝ) (Metric.ball_mem_nhds (0 : ℝ) hδ_pos))
  refine Filter.mem_of_superset hball ?_
  intro t ht
  rcases ht with ⟨ht_ball, ht_punctured⟩
  have ht_abs : |t| < δ := by
    simpa [Real.dist_eq] using ht_ball
  have ht_one : |t| ≤ 1 := by
    have hδ_le_one : δ ≤ 1 := min_le_left _ _
    exact le_trans (le_of_lt ht_abs) hδ_le_one
  have ht_ne : t ≠ 0 := by
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using ht_punctured
  show (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ p)
      (t⁻¹ • (SCV.translateSchwartz (t • v) f - f) - ∂_{v} f) < ε
  refine lt_of_le_of_lt (hC t ht_ne ht_one) ?_
  have hC1 : 0 < C + 1 := by linarith
  have ht_eps : |t| < ε / (C + 1) := by
    exact lt_of_lt_of_le ht_abs (min_le_right _ _)
  have hbound1 : C * |t| ≤ C * (ε / (C + 1)) := by
    have ht_eps_le : |t| ≤ ε / (C + 1) := le_of_lt ht_eps
    gcongr
  have hbound2 : C * (ε / (C + 1)) < ε := by
    have htmp : (C * ε) / (C + 1) < ε := by
      refine (div_lt_iff₀ hC1).2 ?_
      nlinarith [hε, hC_nonneg, hC1]
    have hEq : (C * ε) / (C + 1) = C * (ε / (C + 1)) := by
      field_simp [hC1.ne']
    simpa [hEq] using htmp
  exact lt_of_le_of_lt hbound1 hbound2

end OSReconstruction
