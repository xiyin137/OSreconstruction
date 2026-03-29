import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.Regularization
import Mathlib.Analysis.Calculus.ContDiff.Convolution

noncomputable section

open MeasureTheory
open scoped LineDeriv

private theorem lineDeriv_convolution_eq_convolution_lineDeriv_local
    {d : ℕ}
    (φ g : SchwartzSpacetime d)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (x v : SpacetimeDim d) :
    lineDeriv ℝ
      (fun y : SpacetimeDim d =>
        ∫ z : SpacetimeDim d, (φ : SpacetimeDim d → ℂ) z * (g : SpacetimeDim d → ℂ) (y - z))
      x v
    =
      ∫ z : SpacetimeDim d,
        (φ : SpacetimeDim d → ℂ) z *
          (((LineDeriv.lineDerivOp v g : SchwartzSpacetime d) : SpacetimeDim d → ℂ) (x - z)) := by
  have hfd : HasFDerivAt
      (fun y : SpacetimeDim d =>
        ∫ z : SpacetimeDim d, (φ : SpacetimeDim d → ℂ) z * (g : SpacetimeDim d → ℂ) (y - z))
      (MeasureTheory.convolution
        (f := (φ : SpacetimeDim d → ℂ))
        (g := fderiv ℝ (g : SpacetimeDim d → ℂ))
        (L := (ContinuousLinearMap.lsmul ℝ ℂ).precompR (SpacetimeDim d))
        (μ := volume) x)
      x := by
    simpa [MeasureTheory.convolution] using
      (hg_compact.hasFDerivAt_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℂ)
        (hf := (SchwartzMap.integrable (φ : SchwartzSpacetime d)).locallyIntegrable)
        (hg := (SchwartzMap.smooth (g : SchwartzSpacetime d) ⊤).of_le (by simp)) x)
  rw [hfd.hasLineDerivAt v |>.lineDeriv]
  rw [convolution_precompR_apply
    (L := ContinuousLinearMap.lsmul ℝ ℂ)
    (hf := (SchwartzMap.integrable (φ : SchwartzSpacetime d)).locallyIntegrable)
    (hcg := (hg_compact.fderiv ℝ))
    (hg := ((SchwartzMap.smooth (g : SchwartzSpacetime d) ⊤).of_le (by simp)).continuous_fderiv
      one_ne_zero)
    (x₀ := x) (x := v)]
  simp [MeasureTheory.convolution, SchwartzMap.lineDerivOp_apply_eq_fderiv]

private theorem lineDeriv_convolution_norm_le_L1_mul_seminorm_one_local
    {d : ℕ}
    (φ g : SchwartzSpacetime d)
    (hL1 : ∫ z : SpacetimeDim d, ‖(φ : SpacetimeDim d → ℂ) z‖ = 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (x v : SpacetimeDim d) :
    ‖lineDeriv ℝ
        (fun y : SpacetimeDim d =>
          ∫ z : SpacetimeDim d, (φ : SpacetimeDim d → ℂ) z * (g : SpacetimeDim d → ℂ) (y - z))
        x v‖
      ≤ ‖v‖ * SchwartzMap.seminorm ℝ 0 1 g := by
  rw [lineDeriv_convolution_eq_convolution_lineDeriv_local (d := d) φ g hg_compact x v]
  let S : ℝ := ‖v‖ * SchwartzMap.seminorm ℝ 0 1 g
  have hbound :
      ∀ z : SpacetimeDim d,
        ‖(φ : SpacetimeDim d → ℂ) z *
            (((LineDeriv.lineDerivOp v g : SchwartzSpacetime d) : SpacetimeDim d → ℂ) (x - z))‖
          ≤ S * ‖(φ : SpacetimeDim d → ℂ) z‖ := by
    intro z
    have hline_pt :
        ‖(((LineDeriv.lineDerivOp v g : SchwartzSpacetime d) : SchwartzSpacetime d) (x - z))‖
          ≤ S := by
      dsimp [S]
      calc
        ‖(((LineDeriv.lineDerivOp v g : SchwartzSpacetime d) : SchwartzSpacetime d) (x - z))‖
            = ‖(fderiv ℝ (g : SpacetimeDim d → ℂ) (x - z)) v‖ := by
                simp [SchwartzMap.lineDerivOp_apply_eq_fderiv]
        _ ≤ ‖fderiv ℝ (g : SpacetimeDim d → ℂ) (x - z)‖ * ‖v‖ := by
              exact ContinuousLinearMap.le_opNorm _ _
        _ = ‖iteratedFDeriv ℝ 1 (g : SpacetimeDim d → ℂ) (x - z)‖ * ‖v‖ := by
              exact by
                simpa using
                  (norm_fderiv_iteratedFDeriv (𝕜 := ℝ)
                    (f := (g : SpacetimeDim d → ℂ)) (x := x - z) (n := 0))
        _ ≤ ‖v‖ * SchwartzMap.seminorm ℝ 0 1 g := by
              calc
                ‖iteratedFDeriv ℝ 1 (g : SpacetimeDim d → ℂ) (x - z)‖ * ‖v‖
                    ≤ SchwartzMap.seminorm ℝ 0 1 g * ‖v‖ := by
                        exact mul_le_mul_of_nonneg_right
                          (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ g 1 (x - z))
                          (norm_nonneg _)
                _ = ‖v‖ * SchwartzMap.seminorm ℝ 0 1 g := by ring
        _ = S := by ring
    calc
      ‖(φ : SpacetimeDim d → ℂ) z *
          (((LineDeriv.lineDerivOp v g : SchwartzSpacetime d) : SchwartzSpacetime d) (x - z))‖
          = ‖(φ : SpacetimeDim d → ℂ) z‖ *
            ‖(((LineDeriv.lineDerivOp v g : SchwartzSpacetime d) : SchwartzSpacetime d) (x - z))‖ := by
              rw [norm_mul]
      _ ≤ S * ‖(φ : SpacetimeDim d → ℂ) z‖ := by
            calc
              ‖(φ : SpacetimeDim d → ℂ) z‖ *
                  ‖(((LineDeriv.lineDerivOp v g : SchwartzSpacetime d) : SchwartzSpacetime d) (x - z))‖
                  ≤ ‖(φ : SpacetimeDim d → ℂ) z‖ * S := by
                    exact mul_le_mul_of_nonneg_left hline_pt (norm_nonneg _)
              _ = S * ‖(φ : SpacetimeDim d → ℂ) z‖ := by ring
  have hIntUpper : Integrable (fun z : SpacetimeDim d => S * ‖(φ : SpacetimeDim d → ℂ) z‖) := by
    simpa [S] using MeasureTheory.Integrable.const_mul
      (c := ‖v‖ * SchwartzMap.seminorm ℝ 0 1 g)
      ((SchwartzMap.integrable (φ : SchwartzSpacetime d)).norm)
  have hIntLower : Integrable (fun z : SpacetimeDim d =>
      ‖(φ : SpacetimeDim d → ℂ) z *
          (((LineDeriv.lineDerivOp v g : SchwartzSpacetime d) : SchwartzSpacetime d) (x - z))‖) := by
    refine Integrable.mono' hIntUpper ?_ (Filter.Eventually.of_forall ?_)
    · fun_prop
    · intro z
      simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hbound z
  have hmain :
      ‖∫ z : SpacetimeDim d,
          (φ : SpacetimeDim d → ℂ) z *
            (((LineDeriv.lineDerivOp v g : SchwartzSpacetime d) : SchwartzSpacetime d) (x - z))‖
        ≤ S := by
    calc
      ‖∫ z : SpacetimeDim d,
          (φ : SpacetimeDim d → ℂ) z *
            (((LineDeriv.lineDerivOp v g : SchwartzSpacetime d) : SchwartzSpacetime d) (x - z))‖
        ≤ ∫ z : SpacetimeDim d,
            ‖(φ : SpacetimeDim d → ℂ) z *
              (((LineDeriv.lineDerivOp v g : SchwartzSpacetime d) : SchwartzSpacetime d) (x - z))‖ := by
              exact norm_integral_le_integral_norm _
      _ ≤ ∫ z : SpacetimeDim d, S * ‖(φ : SpacetimeDim d → ℂ) z‖ := by
            exact integral_mono_ae hIntLower hIntUpper (Filter.Eventually.of_forall hbound)
      _ = S * ∫ z : SpacetimeDim d, ‖(φ : SpacetimeDim d → ℂ) z‖ := by
            rw [MeasureTheory.integral_const_mul]
      _ = S := by rw [hL1]; ring
  simpa [S] using hmain

private theorem fderiv_convolution_norm_le_L1_mul_seminorm_one_local
    {d : ℕ}
    (φ g : SchwartzSpacetime d)
    (hL1 : ∫ z : SpacetimeDim d, ‖(φ : SpacetimeDim d → ℂ) z‖ = 1)
    (hg_compact : HasCompactSupport (g : SpacetimeDim d → ℂ))
    (x : SpacetimeDim d) :
    ‖fderiv ℝ
        (fun y : SpacetimeDim d =>
          ∫ z : SpacetimeDim d, (φ : SpacetimeDim d → ℂ) z * (g : SpacetimeDim d → ℂ) (y - z))
        x‖
      ≤ SchwartzMap.seminorm ℝ 0 1 g := by
  have hfd : HasFDerivAt
      (fun y : SpacetimeDim d =>
        ∫ z : SpacetimeDim d, (φ : SpacetimeDim d → ℂ) z * (g : SpacetimeDim d → ℂ) (y - z))
      (MeasureTheory.convolution
        (f := (φ : SpacetimeDim d → ℂ))
        (g := fderiv ℝ (g : SpacetimeDim d → ℂ))
        (L := (ContinuousLinearMap.lsmul ℝ ℂ).precompR (SpacetimeDim d))
        (μ := volume) x)
      x := by
    simpa [MeasureTheory.convolution] using
      (hg_compact.hasFDerivAt_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℂ)
        (hf := (SchwartzMap.integrable (φ : SchwartzSpacetime d)).locallyIntegrable)
        (hg := (SchwartzMap.smooth (g : SchwartzSpacetime d) ⊤).of_le (by simp)) x)
  refine (ContinuousLinearMap.opNorm_le_iff (show 0 ≤ SchwartzMap.seminorm ℝ 0 1 g by positivity)).2 ?_
  intro v
  have hv_conv :
      ‖(MeasureTheory.convolution
          (f := (φ : SpacetimeDim d → ℂ))
          (g := fderiv ℝ (g : SpacetimeDim d → ℂ))
          (L := (ContinuousLinearMap.lsmul ℝ ℂ).precompR (SpacetimeDim d))
          (μ := volume) x) v‖
        ≤ ‖v‖ * SchwartzMap.seminorm ℝ 0 1 g := by
    simpa [hfd.hasLineDerivAt v |>.lineDeriv] using
      lineDeriv_convolution_norm_le_L1_mul_seminorm_one_local
        (d := d) φ g hL1 hg_compact x v
  have hv_fderiv :
      ‖(fderiv ℝ
          (fun y : SpacetimeDim d =>
            ∫ z : SpacetimeDim d, (φ : SpacetimeDim d → ℂ) z * (g : SpacetimeDim d → ℂ) (y - z))
          x) v‖
        ≤ ‖v‖ * SchwartzMap.seminorm ℝ 0 1 g := by
    simpa [hfd.fderiv] using hv_conv
  simpa [mul_comm] using hv_fderiv

variable {d : ℕ} [NeZero d]

/-- The reflected positive-time convolution sequence has a uniform first
derivative pointwise bound by the first Schwartz seminorm of the fixed target
test. This is the `M = 1` analogue of the zeroth-order VI.1 Young bound. -/
theorem positiveTimeCompactSupportConvolution_reflected_negativeApproxIdentity_fderiv_norm_le_seminorm_one_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (h : positiveTimeCompactSupportSubmodule d) :
    ∀ n x,
      ‖fderiv ℝ
          ((((positiveTimeCompactSupportConvolution
              (⟨reflectedSchwartzSpacetime (φ_seq n),
                ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
                  reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
                    (hφ_compact n)⟩⟩)
              h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ)) x‖
        ≤ SchwartzMap.seminorm ℝ 0 1 (h : SchwartzSpacetime d) := by
  intro n x
  let ψn : positiveTimeCompactSupportSubmodule d :=
    ⟨reflectedSchwartzSpacetime (φ_seq n),
      ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
        reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
          (hφ_compact n)⟩⟩
  have hψ_L1 :
      ∫ z : SpacetimeDim d, ‖((ψn : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) z‖ = 1 := by
    simpa [ψn] using
      reflected_approxIdentity_L1_norm_eq_one_vi1Bounds_local
        (d := d) (φ_seq n) (hφ_nonneg n) (hφ_real n) (hφ_int n)
  simpa [positiveTimeCompactSupportConvolution_apply, MeasureTheory.convolution, ψn] using
    fderiv_convolution_norm_le_L1_mul_seminorm_one_local
      (((ψn : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d))
      (h : SchwartzSpacetime d) hψ_L1 h.property.2 x

/-- The reflected positive-time convolution sequence has a uniform weighted
first Schwartz seminorm bound. This is the `M = 1` direct OS-side regularity
estimate needed before feeding VI.1 into the frontier theorem. -/
theorem positiveTimeCompactSupportConvolution_reflected_negativeApproxIdentity_seminorm_one_uniform_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (N : ℕ)
    (h : positiveTimeCompactSupportSubmodule d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      SchwartzMap.seminorm ℝ N 1
        (((positiveTimeCompactSupportConvolution
            (⟨reflectedSchwartzSpacetime (φ_seq n),
              ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
                reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
                  (hφ_compact n)⟩⟩)
            h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d)) ≤ C := by
  rcases
      exists_uniform_closedBall_support_reflected_negativeApproxIdentity_convolution_local
        (d := d) φ_seq hφ_compact hφ_neg hφ_ball h with
    ⟨R, hR_pos, hR⟩
  let C1 : ℝ := SchwartzMap.seminorm ℝ 0 1 (h : SchwartzSpacetime d)
  let C : ℝ := R ^ N * C1
  refine ⟨C, by
    dsimp [C, C1]
    exact mul_nonneg (pow_nonneg (le_of_lt hR_pos) _) (apply_nonneg (SchwartzMap.seminorm ℝ 0 1) _), ?_⟩
  intro n
  let ψn : positiveTimeCompactSupportSubmodule d :=
    ⟨reflectedSchwartzSpacetime (φ_seq n),
      ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
        reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
          (hφ_compact n)⟩⟩
  let convn : SchwartzSpacetime d := (((positiveTimeCompactSupportConvolution ψn h :
    positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d))
  refine SchwartzMap.seminorm_le_bound ℝ N 1 convn
    (by
      dsimp [C, C1]
      exact mul_nonneg (pow_nonneg (le_of_lt hR_pos) _) (apply_nonneg (SchwartzMap.seminorm ℝ 0 1) _)) ?_
  intro x
  rw [norm_iteratedFDeriv_one]
  by_cases hx :
      x ∈ tsupport ((convn : SchwartzSpacetime d) : SpacetimeDim d → ℂ)
  · have hx_ball : x ∈ Metric.closedBall (0 : SpacetimeDim d) R := by
      simpa [convn, ψn] using hR n hx
    have hx_norm : ‖x‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx_ball
    have hnorm :
        ‖fderiv ℝ ((convn : SchwartzSpacetime d) : SpacetimeDim d → ℂ) x‖ ≤ C1 := by
      simpa [convn, ψn, C1] using
        positiveTimeCompactSupportConvolution_reflected_negativeApproxIdentity_fderiv_norm_le_seminorm_one_local
          (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg h n x
    calc
      ‖x‖ ^ N * ‖fderiv ℝ ((convn : SchwartzSpacetime d) : SpacetimeDim d → ℂ) x‖
          ≤ R ^ N * ‖fderiv ℝ ((convn : SchwartzSpacetime d) : SpacetimeDim d → ℂ) x‖ := by
            gcongr
      _ ≤ R ^ N * C1 := by
            exact mul_le_mul_of_nonneg_left hnorm (pow_nonneg (le_of_lt hR_pos) _)
      _ = C := by rfl
  · have hzero : fderiv ℝ ((convn : SchwartzSpacetime d) : SpacetimeDim d → ℂ) x = 0 :=
      fderiv_of_notMem_tsupport (𝕜 := ℝ) hx
    have hC_nonneg : 0 ≤ C := by
      dsimp [C, C1]
      exact mul_nonneg (pow_nonneg (le_of_lt hR_pos) _) (apply_nonneg (SchwartzMap.seminorm ℝ 0 1) _)
    simp [convn, hzero, C, hC_nonneg]
