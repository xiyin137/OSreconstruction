/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorTimeSmearingRealEdge
import OSReconstruction.SCV.DistributionalUniqueness
import OSReconstruction.SCV.EuclideanWeylApproxIdentity
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace

noncomputable section

open MeasureTheory
open Filter
open Topology
open scoped Convolution LineDeriv Pointwise

namespace OSReconstruction
namespace OSIIChapterV
namespace SchwartzTimeApproximateIdentity

variable {n : ℕ} [Nonempty (Fin n)]

noncomputable local instance timeComplexCLMNormedAddCommGroup
    {n : ℕ} [Nonempty (Fin n)] :
    NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance timeContinuousMultilinearMapNorm
    {n j : ℕ} [Nonempty (Fin n)] :
    Norm (ContinuousMultilinearMap ℝ
      (fun _ : Fin j => Fin n → ℝ) ℂ) :=
  ContinuousMultilinearMap.hasOpNorm

noncomputable local instance timeContinuousMultilinearMapNormedAddCommGroup
    {n j : ℕ} [Nonempty (Fin n)] :
    NormedAddCommGroup (ContinuousMultilinearMap ℝ
      (fun _ : Fin j => Fin n → ℝ) ℂ) :=
  ContinuousMultilinearMap.normedAddCommGroup

noncomputable local instance timeContinuousMultilinearMapNormedSpace
    {n j : ℕ} [Nonempty (Fin n)] :
    NormedSpace ℝ (ContinuousMultilinearMap ℝ
      (fun _ : Fin j => Fin n → ℝ) ℂ) :=
  ContinuousMultilinearMap.normedSpace

/-- Convolution of a finite-dimensional time approximate identity with a fixed
Schwartz test. Derivatives are intended to fall on the fixed second factor. -/
noncomputable def convolutionTest
    (I : SchwartzTimeApproximateIdentity n)
    (N : ℕ)
    (h : SchwartzMap (Fin n → ℝ) ℂ)
    (hcompact : HasCompactSupport (h : (Fin n → ℝ) → ℂ)) :
    SchwartzMap (Fin n → ℝ) ℂ := by
  let fconv : (Fin n → ℝ) → ℂ :=
    (I.test N : (Fin n → ℝ) → ℂ) ⋆[
      ContinuousLinearMap.mul ℝ ℂ, volume]
      (h : (Fin n → ℝ) → ℂ)
  have hconv_compact : HasCompactSupport fconv := by
    simpa [fconv] using
      (I.compact N).convolution
        (L := ContinuousLinearMap.mul ℝ ℂ) hcompact
  have hconv_smooth : ContDiff ℝ (⊤ : ℕ∞) fconv := by
    have hI_locallyIntegrable :
        LocallyIntegrable
          (I.test N : (Fin n → ℝ) → ℂ) volume :=
      (SchwartzMap.integrable (I.test N)).locallyIntegrable
    simpa [fconv] using
      hcompact.contDiff_convolution_right
        (L := ContinuousLinearMap.mul ℝ ℂ)
        (μ := volume)
        hI_locallyIntegrable
        (h.smooth' :
          ContDiff ℝ (⊤ : ℕ∞) (h : (Fin n → ℝ) → ℂ))
  exact hconv_compact.toSchwartzMap hconv_smooth

@[simp]
theorem convolutionTest_apply
    (I : SchwartzTimeApproximateIdentity n)
    (N : ℕ)
    (h : SchwartzMap (Fin n → ℝ) ℂ)
    (hcompact : HasCompactSupport (h : (Fin n → ℝ) → ℂ))
    (x : Fin n → ℝ) :
    I.convolutionTest N h hcompact x =
      ∫ z : Fin n → ℝ, I.test N z * h (x - z) := by
  rw [convolutionTest]
  simp [MeasureTheory.convolution]

private theorem test_L1_norm_eq_one
    (I : SchwartzTimeApproximateIdentity n)
    (N : ℕ) :
    ∫ x : Fin n → ℝ, ‖I.test N x‖ = 1 := by
  have hnorm_re : ∀ x : Fin n → ℝ, ‖I.test N x‖ = (I.test N x).re := by
    intro x
    rw [← Complex.re_eq_norm.mpr ⟨I.nonnegative N x, (I.real N x).symm⟩]
  simp_rw [hnorm_re]
  rw [show (fun x => (I.test N x).re) =
    (fun x => RCLike.re (I.test N x)) from rfl]
  rw [integral_re (SchwartzMap.integrable (I.test N))]
  have h := congrArg Complex.re (I.integral_one N)
  simpa using h

private theorem lineDeriv_convolution_eq_convolution_lineDeriv
    (φ h : SchwartzMap (Fin n → ℝ) ℂ)
    (hcompact : HasCompactSupport (h : (Fin n → ℝ) → ℂ))
    (x v : Fin n → ℝ) :
    lineDeriv ℝ
      (fun y : Fin n → ℝ =>
        ∫ z : Fin n → ℝ, φ z * h (y - z))
      x v =
      ∫ z : Fin n → ℝ,
        φ z *
          ((LineDeriv.lineDerivOp v h :
            SchwartzMap (Fin n → ℝ) ℂ) (x - z)) := by
  letI : NormedSpace ℝ ((Fin n → ℝ) →L[ℝ] ℂ) :=
    ContinuousLinearMap.toNormedSpace
  have hfd : HasFDerivAt
      (fun y : Fin n → ℝ =>
        ∫ z : Fin n → ℝ, φ z * h (y - z))
      (MeasureTheory.convolution
        (𝕜 := ℝ)
        (f := (φ : (Fin n → ℝ) → ℂ))
        (g := fderiv ℝ (h : (Fin n → ℝ) → ℂ))
        (L := (ContinuousLinearMap.mul ℝ ℂ).precompR (Fin n → ℝ))
        (μ := volume) x)
      x := by
    simpa [MeasureTheory.convolution] using
      (hcompact.hasFDerivAt_convolution_right
        (L := ContinuousLinearMap.mul ℝ ℂ)
        (hf := (SchwartzMap.integrable φ).locallyIntegrable)
        (hg := (SchwartzMap.smooth h ⊤).of_le (by simp)) x)
  rw [hfd.hasLineDerivAt v |>.lineDeriv]
  have hconv_apply :
      ((MeasureTheory.convolution
          (𝕜 := ℝ)
          (f := (φ : (Fin n → ℝ) → ℂ))
          (g := fderiv ℝ (h : (Fin n → ℝ) → ℂ))
          (L := (ContinuousLinearMap.mul ℝ ℂ).precompR (Fin n → ℝ))
          (μ := volume) x) v) =
        MeasureTheory.convolution
          (𝕜 := ℝ)
          (f := (φ : (Fin n → ℝ) → ℂ))
          (g := fun a => fderiv ℝ (h : (Fin n → ℝ) → ℂ) a v)
          (L := ContinuousLinearMap.mul ℝ ℂ)
          (μ := volume) x := by
    exact
      convolution_precompR_apply
        (𝕜 := ℝ)
        (μ := volume)
        (L := ContinuousLinearMap.mul ℝ ℂ)
        (hf := (SchwartzMap.integrable φ).locallyIntegrable)
        (hcg := hcompact.fderiv ℝ)
        (hg := ((SchwartzMap.smooth h ⊤).of_le
          (by simp)).continuous_fderiv one_ne_zero)
        (x₀ := x) (x := v)
  rw [hconv_apply]
  simp [MeasureTheory.convolution, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rfl

private theorem convolutionTest_iteratedLineDeriv_eq
    (I : SchwartzTimeApproximateIdentity n)
    (N : ℕ)
    (h : SchwartzMap (Fin n → ℝ) ℂ)
    (hcompact : HasCompactSupport (h : (Fin n → ℝ) → ℂ))
    {j : ℕ}
    (u : Fin j → (Fin n → ℝ)) :
    (LineDeriv.iteratedLineDerivOp u
      (I.convolutionTest N h hcompact) :
      SchwartzMap (Fin n → ℝ) ℂ) =
      I.convolutionTest N
        (LineDeriv.iteratedLineDerivOp u h :
          SchwartzMap (Fin n → ℝ) ℂ)
        (hcompact.of_isClosed_subset
          (isClosed_tsupport _)
          (SchwartzMap.tsupport_iteratedLineDerivOp_subset
            (m := u) (f := h))) := by
  induction j generalizing h with
  | zero =>
      simp [LineDeriv.iteratedLineDerivOp_fin_zero]
  | succ j ih =>
      let htail : SchwartzMap (Fin n → ℝ) ℂ :=
        LineDeriv.iteratedLineDerivOp (Fin.tail u) h
      have htail_compact :
          HasCompactSupport (htail : (Fin n → ℝ) → ℂ) := by
        exact hcompact.of_isClosed_subset
          (isClosed_tsupport _)
          (SchwartzMap.tsupport_iteratedLineDerivOp_subset
            (m := Fin.tail u) (f := h))
      have htail_eq :
            (LineDeriv.iteratedLineDerivOp (Fin.tail u)
            (I.convolutionTest N h hcompact) :
              SchwartzMap (Fin n → ℝ) ℂ) =
            I.convolutionTest N htail htail_compact := by
        simpa [htail] using
          ih (h := h) (hcompact := hcompact) (u := Fin.tail u)
      ext x
      rw [LineDeriv.iteratedLineDerivOp_succ_left,
        SchwartzMap.lineDerivOp_apply]
      have hstep :
          lineDeriv ℝ
              (fun y : Fin n → ℝ =>
                (LineDeriv.iteratedLineDerivOp (Fin.tail u)
                  (I.convolutionTest N h hcompact) :
                    SchwartzMap (Fin n → ℝ) ℂ) y)
              x (u 0) =
            lineDeriv ℝ
              (fun y : Fin n → ℝ =>
                I.convolutionTest N htail htail_compact y)
              x (u 0) := by
        simpa using congrArg
          (fun F : SchwartzMap (Fin n → ℝ) ℂ =>
            lineDeriv ℝ (fun y => F y) x (u 0))
          htail_eq
      rw [hstep]
      simpa [convolutionTest_apply, htail,
        LineDeriv.iteratedLineDerivOp_succ_left] using
        lineDeriv_convolution_eq_convolution_lineDeriv
          (I.test N) htail htail_compact x (u 0)

private theorem iteratedFDeriv_convolutionTest_sub_apply_eq_integral
    (I : SchwartzTimeApproximateIdentity n)
    (N : ℕ)
    (h : SchwartzMap (Fin n → ℝ) ℂ)
    (hcompact : HasCompactSupport (h : (Fin n → ℝ) → ℂ))
    (j : ℕ)
    (x : Fin n → ℝ)
    (u : Fin j → (Fin n → ℝ)) :
    (iteratedFDeriv ℝ j
        (I.convolutionTest N h hcompact - h :
          (Fin n → ℝ) → ℂ) x) u =
      ∫ z : Fin n → ℝ,
        I.test N z *
          ((iteratedFDeriv ℝ j
              (h : (Fin n → ℝ) → ℂ) (x - z)) u -
            (iteratedFDeriv ℝ j
              (h : (Fin n → ℝ) → ℂ) x) u) := by
  let hu : SchwartzMap (Fin n → ℝ) ℂ :=
    LineDeriv.iteratedLineDerivOp u h
  have hu_compact : HasCompactSupport (hu : (Fin n → ℝ) → ℂ) := by
    exact hcompact.of_isClosed_subset
      (isClosed_tsupport _)
      (SchwartzMap.tsupport_iteratedLineDerivOp_subset
        (m := u) (f := h))
  have hconv_deriv :
      (LineDeriv.iteratedLineDerivOp u
        (I.convolutionTest N h hcompact) :
          SchwartzMap (Fin n → ℝ) ℂ) =
        I.convolutionTest N hu hu_compact := by
    simpa [hu] using
      convolutionTest_iteratedLineDeriv_eq I N h hcompact u
  have hIntDiff :
      Integrable (fun z : Fin n → ℝ =>
        I.test N z *
          (hu (x - z) - hu x)) := by
    have hbound :
        ∀ z : Fin n → ℝ,
          ‖I.test N z * (hu (x - z) - hu x)‖ ≤
            ‖I.test N z‖ *
              (2 * SchwartzMap.seminorm ℝ 0 0 hu) := by
      intro z
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc
        ‖hu (x - z) - hu x‖
            ≤ ‖hu (x - z)‖ + ‖hu x‖ := norm_sub_le _ _
        _ ≤ SchwartzMap.seminorm ℝ 0 0 hu +
              SchwartzMap.seminorm ℝ 0 0 hu := by
            gcongr <;>
              simpa using
                (SchwartzMap.norm_pow_mul_le_seminorm ℝ hu 0 _)
        _ = 2 * SchwartzMap.seminorm ℝ 0 0 hu := by ring
    refine Integrable.mono'
      ((SchwartzMap.integrable (I.test N)).norm.mul_const
        (2 * SchwartzMap.seminorm ℝ 0 0 hu))
      ?_ (Filter.Eventually.of_forall hbound)
    fun_prop
  have hIntConst :
      Integrable (fun z : Fin n → ℝ => I.test N z * hu x) := by
    simpa [mul_comm] using
      (SchwartzMap.integrable (I.test N)).const_mul (hu x)
  have hIntProd :
      Integrable (fun z : Fin n → ℝ =>
        I.test N z * hu (x - z)) := by
    convert hIntDiff.add hIntConst using 1
    funext z
    simp only [Pi.add_apply]
    ring
  calc
    (iteratedFDeriv ℝ j
        (I.convolutionTest N h hcompact - h :
          (Fin n → ℝ) → ℂ) x) u =
        (LineDeriv.iteratedLineDerivOp u
          (I.convolutionTest N h hcompact - h) :
            SchwartzMap (Fin n → ℝ) ℂ) x := by
      exact
        (SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv
          (m := u)
          (f := I.convolutionTest N h hcompact - h)
          (x := x)).symm
    _ =
        (LineDeriv.iteratedLineDerivOp u
          (I.convolutionTest N h hcompact) :
            SchwartzMap (Fin n → ℝ) ℂ) x -
          (LineDeriv.iteratedLineDerivOp u h :
            SchwartzMap (Fin n → ℝ) ℂ) x := by
      rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv,
        SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv,
        SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
      change
        (iteratedFDeriv ℝ j
          (fun y : Fin n → ℝ =>
            I.convolutionTest N h hcompact y - h y) x) u =
          (iteratedFDeriv ℝ j
            (I.convolutionTest N h hcompact :
              (Fin n → ℝ) → ℂ) x) u -
            (iteratedFDeriv ℝ j
              (h : (Fin n → ℝ) → ℂ) x) u
      have hsub :=
        iteratedFDeriv_sub_apply
          (x := x)
          ((I.convolutionTest N h hcompact).smooth j).contDiffAt
          (h.smooth j).contDiffAt
      exact congrArg (fun D => D u) hsub
    _ = I.convolutionTest N hu hu_compact x - hu x := by
      rw [hconv_deriv]
    _ =
        (∫ z : Fin n → ℝ, I.test N z * hu (x - z)) -
          ∫ z : Fin n → ℝ, I.test N z * hu x := by
      rw [I.convolutionTest_apply N hu hu_compact]
      congr 1
      symm
      calc
        ∫ z : Fin n → ℝ, I.test N z * hu x =
            ∫ z : Fin n → ℝ, hu x * I.test N z := by
          apply integral_congr_ae
          filter_upwards with z
          ring
        _ = hu x * ∫ z : Fin n → ℝ, I.test N z := by
          exact
            MeasureTheory.integral_const_mul
              (hu x) (fun z : Fin n → ℝ => I.test N z)
        _ = hu x := by rw [I.integral_one N, mul_one]
    _ =
        ∫ z : Fin n → ℝ,
          (I.test N z * hu (x - z) -
            I.test N z * hu x) := by
      rw [MeasureTheory.integral_sub]
      · exact hIntProd
      · exact hIntConst
    _ =
        ∫ z : Fin n → ℝ,
          I.test N z * (hu (x - z) - hu x) := by
      apply integral_congr_ae
      filter_upwards with z
      ring
    _ =
        ∫ z : Fin n → ℝ,
          I.test N z *
            ((iteratedFDeriv ℝ j
                (h : (Fin n → ℝ) → ℂ) (x - z)) u -
              (iteratedFDeriv ℝ j
                (h : (Fin n → ℝ) → ℂ) x) u) := by
      apply integral_congr_ae
      filter_upwards with z
      simp only [hu]
      rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv,
        SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]

/-- A normalized nonnegative Schwartz approximate identity converges on every
fixed compactly supported Schwartz test in the Schwartz topology. -/
theorem tendsto_convolutionTest
    (I : SchwartzTimeApproximateIdentity n)
    (h : SchwartzMap (Fin n → ℝ) ℂ)
    (hcompact : HasCompactSupport (h : (Fin n → ℝ) → ℂ)) :
    Tendsto
      (fun N => I.convolutionTest N h hcompact)
      atTop
      (𝓝 h) := by
  rw [(schwartz_withSeminorms ℝ (Fin n → ℝ) ℂ).tendsto_nhds_atTop _ _]
  intro ⟨p, j⟩ ε hε
  letI : NormSMulClass ℝ (ContinuousMultilinearMap ℝ
      (fun _ : Fin j => Fin n → ℝ) ℂ) :=
    NormedSpace.toNormSMulClass
  have hε2 : 0 < ε / 2 := by positivity
  have htranslate :
      Tendsto
        (fun z : Fin n → ℝ => SCV.translateSchwartz (-z) h)
        (𝓝 0)
        (𝓝 h) := by
    have hbase :=
      (SCV.tendsto_translateSchwartz_nhds_of_isCompactSupport
        h hcompact (0 : Fin n → ℝ)).comp
        (show Tendsto
            (fun z : Fin n → ℝ => -z)
            (𝓝 0) (𝓝 0) by
          simpa using
            (continuous_neg.tendsto (0 : Fin n → ℝ)))
    simpa using hbase
  have hseminorm :
      Tendsto
        (fun z : Fin n → ℝ =>
          SchwartzMap.seminorm ℝ p j
            (SCV.translateSchwartz (-z) h - h))
        (𝓝 0)
        (𝓝 0) := by
    have hsub :
        Tendsto
          (fun z : Fin n → ℝ =>
            SCV.translateSchwartz (-z) h - h)
          (𝓝 0)
          (𝓝 0) := by
      have hconst :
          Tendsto
            (fun _ : Fin n → ℝ => h)
            (𝓝 0) (𝓝 h) :=
        tendsto_const_nhds
      simpa using htranslate.sub hconst
    simpa only [Function.comp_apply, map_zero] using
      ((schwartz_withSeminorms ℝ
        (Fin n → ℝ) ℂ).continuous_seminorm (p, j)).continuousAt.tendsto.comp
        hsub
  have hsmall_nhds :
      {z : Fin n → ℝ |
          SchwartzMap.seminorm ℝ p j
            (SCV.translateSchwartz (-z) h - h) < ε / 2} ∈
        𝓝 0 := by
    exact hseminorm (Iio_mem_nhds hε2)
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    Metric.mem_nhds_iff.mp hsmall_nhds
  have hradius :
      ∀ᶠ N : ℕ in atTop, I.radius N < δ := by
    have hdist :
        ∀ᶠ N : ℕ in atTop, dist (I.radius N) 0 < δ :=
      (Metric.tendsto_nhds.mp I.radius_tendsto) δ hδ_pos
    filter_upwards [hdist] with N hN
    rw [Real.dist_eq] at hN
    exact lt_of_le_of_lt (le_abs_self (I.radius N)) (by simpa using hN)
  rw [eventually_atTop] at hradius
  obtain ⟨N₀, hN₀⟩ := hradius
  refine ⟨N₀, ?_⟩
  intro N hNN₀
  have hN := hN₀ N hNN₀
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  refine SchwartzMap.seminorm_le_bound ℝ p j
    (I.convolutionTest N h hcompact - h) hε2.le ?_
  intro x
  let L : ContinuousMultilinearMap ℝ
      (fun _ : Fin j => Fin n → ℝ) ℂ :=
    iteratedFDeriv ℝ j
      (I.convolutionTest N h hcompact - h :
        (Fin n → ℝ) → ℂ) x
  have hpoint :
      ∀ u : Fin j → (Fin n → ℝ),
        ‖((‖x‖ ^ p : ℝ) • L) u‖ ≤
          (ε / 2) * ∏ i, ‖u i‖ := by
    intro u
    let Δ : (Fin n → ℝ) → ℂ := fun z =>
      ((iteratedFDeriv ℝ j
          (h : (Fin n → ℝ) → ℂ) (x - z)) u -
        (iteratedFDeriv ℝ j
          (h : (Fin n → ℝ) → ℂ) x) u)
    have hbound :
        ∀ z : Fin n → ℝ,
          ‖(‖x‖ ^ p : ℝ) • (I.test N z * Δ z)‖ ≤
            ((ε / 2) * ∏ i, ‖u i‖) * ‖I.test N z‖ := by
      intro z
      by_cases hz : I.test N z = 0
      · simp [hz]
      · have hz_support :
            z ∈ Function.support
              (I.test N : (Fin n → ℝ) → ℂ) := by
          simpa [Function.mem_support] using hz
        have hz_ball := I.support N hz_support
        have hz_delta : z ∈ Metric.ball (0 : Fin n → ℝ) δ := by
          rw [Metric.mem_ball] at hz_ball ⊢
          exact hz_ball.trans hN
        have htranslate_small :
            SchwartzMap.seminorm ℝ p j
              (SCV.translateSchwartz (-z) h - h) < ε / 2 :=
          hδ hz_delta
        have hderiv :
            ‖x‖ ^ p * ‖Δ z‖ ≤
              (ε / 2) * ∏ i, ‖u i‖ := by
          calc
            ‖x‖ ^ p * ‖Δ z‖ =
                ‖x‖ ^ p *
                  ‖(iteratedFDeriv ℝ j
                    (SCV.translateSchwartz (-z) h - h :
                      (Fin n → ℝ) → ℂ) x) u‖ := by
              congr 2
              simp only [Δ]
              rw [show
                  iteratedFDeriv ℝ j
                      (SCV.translateSchwartz (-z) h - h :
                        (Fin n → ℝ) → ℂ) x =
                    iteratedFDeriv ℝ j
                        (SCV.translateSchwartz (-z) h :
                          (Fin n → ℝ) → ℂ) x -
                      iteratedFDeriv ℝ j
                        (h : (Fin n → ℝ) → ℂ) x by
                    exact
                      iteratedFDeriv_sub_apply
                        (x := x)
                        ((SCV.translateSchwartz (-z) h).smooth j).contDiffAt
                        (h.smooth j).contDiffAt]
              rw [show
                  iteratedFDeriv ℝ j
                      (SCV.translateSchwartz (-z) h :
                        (Fin n → ℝ) → ℂ) x =
                    iteratedFDeriv ℝ j
                      (h : (Fin n → ℝ) → ℂ) (x - z) by
                    simpa [SCV.translateSchwartz] using
                      (iteratedFDeriv_comp_add_right
                        (f := (h : (Fin n → ℝ) → ℂ))
                        j (-z) x)]
              rfl
            _ ≤
                SchwartzMap.seminorm ℝ p j
                    (SCV.translateSchwartz (-z) h - h) *
                  ∏ i, ‖u i‖ := by
              let D : ContinuousMultilinearMap ℝ
                  (fun _ : Fin j => Fin n → ℝ) ℂ :=
                iteratedFDeriv ℝ j
                  (SCV.translateSchwartz (-z) h - h :
                    (Fin n → ℝ) → ℂ) x
              calc
                ‖x‖ ^ p * ‖D u‖
                    ≤ ‖x‖ ^ p *
                        (‖D‖ * ∏ i, ‖u i‖) := by
                      gcongr
                      exact ContinuousMultilinearMap.le_opNorm D u
                _ = (‖x‖ ^ p * ‖D‖) *
                      ∏ i, ‖u i‖ := by ring
                _ ≤
                    SchwartzMap.seminorm ℝ p j
                        (SCV.translateSchwartz (-z) h - h) *
                      ∏ i, ‖u i‖ := by
                  exact mul_le_mul_of_nonneg_right
                    (by
                      simpa [D] using
                        (SchwartzMap.le_seminorm ℝ p j
                          (SCV.translateSchwartz (-z) h - h) x))
                    (Finset.prod_nonneg fun _ _ => norm_nonneg _)
            _ ≤ (ε / 2) * ∏ i, ‖u i‖ := by
              exact mul_le_mul_of_nonneg_right
                htranslate_small.le
                (Finset.prod_nonneg fun _ _ => norm_nonneg _)
        calc
          ‖(‖x‖ ^ p : ℝ) • (I.test N z * Δ z)‖ =
              ‖I.test N z‖ * (‖x‖ ^ p * ‖Δ z‖) := by
            simp only [norm_smul, Real.norm_eq_abs,
              abs_of_nonneg (pow_nonneg (norm_nonneg x) p), norm_mul]
            ring
          _ ≤ ‖I.test N z‖ *
                ((ε / 2) * ∏ i, ‖u i‖) := by
            exact mul_le_mul_of_nonneg_left hderiv (norm_nonneg _)
          _ = ((ε / 2) * ∏ i, ‖u i‖) *
                ‖I.test N z‖ := by ring
    have hmajor :
        Integrable (fun z : Fin n → ℝ =>
          ((ε / 2) * ∏ i, ‖u i‖) * ‖I.test N z‖) :=
      (SchwartzMap.integrable (I.test N)).norm.const_mul
        ((ε / 2) * ∏ i, ‖u i‖)
    have hLu :
        L u =
          ∫ z : Fin n → ℝ, I.test N z * Δ z := by
      dsimp [L, Δ]
      exact
        iteratedFDeriv_convolutionTest_sub_apply_eq_integral
          I N h hcompact j x u
    calc
      ‖((‖x‖ ^ p : ℝ) • L) u‖ =
          ‖(‖x‖ ^ p : ℝ) •
            ∫ z : Fin n → ℝ, I.test N z * Δ z‖ := by
        rw [show
          (((‖x‖ ^ p : ℝ) • L) u) =
            (‖x‖ ^ p : ℝ) • (L u) by rfl, hLu]
      _ =
          ‖∫ z : Fin n → ℝ,
            (‖x‖ ^ p : ℝ) • (I.test N z * Δ z)‖ := by
        rw [MeasureTheory.integral_smul]
      _ ≤ ∫ z : Fin n → ℝ,
          ‖(‖x‖ ^ p : ℝ) • (I.test N z * Δ z)‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ z : Fin n → ℝ,
          ((ε / 2) * ∏ i, ‖u i‖) * ‖I.test N z‖ := by
        exact integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          hmajor
          (Filter.Eventually.of_forall hbound)
      _ = ((ε / 2) * ∏ i, ‖u i‖) *
          ∫ z : Fin n → ℝ, ‖I.test N z‖ := by
        rw [integral_const_mul]
      _ = (ε / 2) * ∏ i, ‖u i‖ := by
        rw [I.test_L1_norm_eq_one N, mul_one]
  have hL :
      ‖((‖x‖ ^ p : ℝ) • L)‖ ≤ ε / 2 :=
    (ContinuousMultilinearMap.opNorm_le_iff hε2.le).2 hpoint
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (norm_nonneg x) p)] at hL
  exact hL

/-- Pairing a flat Schwartz distribution against translated kernels is the
distribution applied to the corresponding convolution test. -/
theorem integral_apply_translate_test_mul_eq_apply_convolutionTest
    (I : SchwartzTimeApproximateIdentity n)
    (N : ℕ)
    (h : SchwartzMap (Fin n → ℝ) ℂ)
    (hcompact : HasCompactSupport (h : (Fin n → ℝ) → ℂ))
    (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ) :
    ∫ x : Fin n → ℝ,
        T (SCV.translateSchwartz (-x) (I.test N)) * h x =
      T (I.convolutionTest N h hcompact) := by
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
    EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
  let testE : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e) (I.test N)
  let hE : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e) h
  let TE : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ →L[ℂ] ℂ :=
    T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm)
  have htestE_compact :
      HasCompactSupport
        (testE : EuclideanSpace ℝ (Fin n) → ℂ) := by
    simpa [testE, e] using
      (I.compact N).comp_homeomorph e.toHomeomorph
  have hhE_compact :
      HasCompactSupport
        (hE : EuclideanSpace ℝ (Fin n) → ℂ) := by
    simpa [hE, e] using
      hcompact.comp_homeomorph e.toHomeomorph
  have hpair :=
    SCV.regularizedDistribution_integral_pairing
      TE testE hE htestE_compact hhE_compact
  have hleft_change :=
    (((PiLp.volume_preserving_toLp (ι := Fin n)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
      (fun x : EuclideanSpace ℝ (Fin n) =>
        TE (SCV.euclideanReflectedTranslate x testE) * hE x)).symm)
  have hleft :
      ∫ x : EuclideanSpace ℝ (Fin n),
          TE (SCV.euclideanReflectedTranslate x testE) * hE x =
        ∫ x : Fin n → ℝ,
          T (SCV.translateSchwartz (-x) (I.test N)) * h x := by
    calc
      ∫ x : EuclideanSpace ℝ (Fin n),
          TE (SCV.euclideanReflectedTranslate x testE) * hE x =
          ∫ x : Fin n → ℝ,
            TE (SCV.euclideanReflectedTranslate (e.symm x) testE) *
              hE (e.symm x) := by
        simpa [e, PiLp.coe_symm_continuousLinearEquiv] using hleft_change
      _ =
          ∫ x : Fin n → ℝ,
            T (SCV.translateSchwartz (-x) (I.test N)) * h x := by
        apply integral_congr_ae
        filter_upwards with x
        have hT :
            TE (SCV.euclideanReflectedTranslate (e.symm x) testE) =
              T (SCV.translateSchwartz (-x) (I.test N)) := by
          apply congrArg T
          ext y
          simp [TE, testE, e, SCV.euclideanReflectedTranslate_apply,
            SCV.translateSchwartz_apply, PiLp.coe_continuousLinearEquiv,
            sub_eq_add_neg]
        have hh : hE (e.symm x) = h x := by
          simp [hE, e, PiLp.coe_continuousLinearEquiv]
        rw [hT, hh]
  have harg :
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm)
          (SCV.euclideanConvolutionTest hE testE) =
        I.convolutionTest N h hcompact := by
    ext x
    rw [I.convolutionTest_apply N h hcompact]
    change
      SCV.euclideanConvolutionTest hE testE (e.symm x) =
        ∫ y : Fin n → ℝ, I.test N y * h (x - y)
    rw [SCV.euclideanConvolutionTest_apply_swap]
    have hchange :=
      (((PiLp.volume_preserving_toLp (ι := Fin n)).integral_comp
        (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
        (fun y : EuclideanSpace ℝ (Fin n) =>
          hE (e.symm x - y) * testE y)).symm)
    change
      ∫ y : EuclideanSpace ℝ (Fin n),
          hE (e.symm x - y) * testE y =
        ∫ y : Fin n → ℝ, I.test N y * h (x - y)
    calc
      ∫ y : EuclideanSpace ℝ (Fin n),
          hE (e.symm x - y) * testE y =
          ∫ y : Fin n → ℝ,
            hE (e.symm x - e.symm y) * testE (e.symm y) := by
        simpa [e, PiLp.coe_symm_continuousLinearEquiv] using hchange
      _ = ∫ y : Fin n → ℝ, I.test N y * h (x - y) := by
        apply integral_congr_ae
        filter_upwards with y
        simp [hE, testE, e, PiLp.coe_continuousLinearEquiv]
        ring
  have hright :
      TE (SCV.euclideanConvolutionTest hE testE) =
        T (I.convolutionTest N h hcompact) := by
    simp [TE, harg]
  rw [hleft, hright] at hpair
  exact hpair

/-- Distributional convergence of translated shrinking kernels against a
fixed compactly supported time test. -/
theorem tendsto_integral_apply_translate_test_mul
    (I : SchwartzTimeApproximateIdentity n)
    (h : SchwartzMap (Fin n → ℝ) ℂ)
    (hcompact : HasCompactSupport (h : (Fin n → ℝ) → ℂ))
    (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ) :
    Tendsto
      (fun N =>
        ∫ x : Fin n → ℝ,
          T (SCV.translateSchwartz (-x) (I.test N)) * h x)
      atTop
      (𝓝 (T h)) := by
  have hconv :
      Tendsto
        (fun N => T (I.convolutionTest N h hcompact))
        atTop
        (𝓝 (T h)) :=
    T.continuous.continuousAt.tendsto.comp
      (I.tendsto_convolutionTest h hcompact)
  apply (tendsto_congr' ?_).2 hconv
  exact Filter.Eventually.of_forall fun N =>
    I.integral_apply_translate_test_mul_eq_apply_convolutionTest
      N h hcompact T

end SchwartzTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
