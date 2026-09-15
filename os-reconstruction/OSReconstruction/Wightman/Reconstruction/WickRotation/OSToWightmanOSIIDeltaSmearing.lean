/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSpatialMomentum
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBase
import OSReconstruction.Wightman.Reconstruction.BlockIntegral
import OSReconstruction.Wightman.Reconstruction.HeadBlockTranslationInvariant
import OSReconstruction.Wightman.Reconstruction.DenseCLM
import OSReconstruction.Wightman.Reconstruction.SchwartzDensity
import OSReconstruction.Wightman.Reconstruction.SchwingerOS
import OSReconstruction.Wightman.Reconstruction.WickRotation.SchwingerAxioms
import OSReconstruction.Wightman.Reconstruction.SliceIntegral
import OSReconstruction.SCV.LaplaceHolomorphic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv










noncomputable section

open Complex Topology MeasureTheory Filter
open scoped Classical NNReal BigOperators

namespace OSReconstruction

/-- Translating a positive-orthant compact-support test by a positive-orthant
center keeps the translated test supported in the positive orthant. -/
theorem translate_positiveOrthant_schwartz_mem
    {m : ℕ}
    (φ : SchwartzMap (Fin m → ℝ) ℂ)
    (hφ_pos : tsupport (φ : (Fin m → ℝ) → ℂ) ⊆
      {x : Fin m → ℝ | ∀ i : Fin m, 0 < x i})
    (hφ_compact : HasCompactSupport (φ : (Fin m → ℝ) → ℂ))
    (x0 : Fin m → ℝ) (hx0 : ∀ i : Fin m, 0 < x0 i) :
    tsupport (SCV.translateSchwartz (-x0) φ : (Fin m → ℝ) → ℂ) ⊆
        {x : Fin m → ℝ | ∀ i : Fin m, 0 < x i} ∧
      HasCompactSupport
        (SCV.translateSchwartz (-x0) φ : (Fin m → ℝ) → ℂ) := by
  constructor
  · intro x hx i
    have hx_pre :
        x + (-x0) ∈ tsupport (φ : (Fin m → ℝ) → ℂ) := by
      exact tsupport_comp_subset_preimage
        (φ : (Fin m → ℝ) → ℂ)
        (f := fun y : Fin m → ℝ => y + (-x0))
        (Homeomorph.addRight (-x0)).continuous hx
    have hpre : 0 < (x + (-x0)) i := hφ_pos hx_pre i
    have hx_gt : x0 i < x i := by
      simpa [Pi.add_apply, sub_eq_add_neg] using hpre
    exact lt_trans (hx0 i) hx_gt
  · simpa [SCV.translateSchwartz_apply, Function.comp_def] using
      hφ_compact.comp_homeomorph (Homeomorph.addRight (-x0))

/-- A normalized, pointwise nonnegative real-valued Schwartz test has
`L¹`-norm one. -/
theorem integral_norm_eq_one_of_nonnegative_real_schwartz
    {m : ℕ}
    (φ : SchwartzMap (Fin m → ℝ) ℂ)
    (hφ_nonneg : ∀ x, 0 ≤ (φ x).re)
    (hφ_real : ∀ x, (φ x).im = 0)
    (hφ_int : ∫ x : Fin m → ℝ, φ x = 1) :
    ∫ x : Fin m → ℝ, ‖φ x‖ = 1 := by
  have hnorm_re : ∀ x : Fin m → ℝ, ‖φ x‖ = (φ x).re := by
    intro x
    rw [← Complex.re_eq_norm.mpr ⟨hφ_nonneg x, (hφ_real x).symm⟩]
  simp_rw [hnorm_re]
  rw [show (fun x : Fin m → ℝ => (φ x).re) =
      (fun x : Fin m → ℝ => RCLike.re (φ x)) from rfl]
  rw [integral_re (SchwartzMap.integrable φ)]
  have := congrArg Complex.re hφ_int
  simpa using this

/-- Shrinking compact Schwartz bumps, translated to `x0`, eventually have
compact support inside every neighborhood of `x0`.  Simultaneously, adding
`x0` maps the original shrinking supports into that neighborhood. -/
theorem eventually_translate_shrinking_schwartz_supportsInOpen_and_mapsTo
    {m : ℕ}
    (φ : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (r : ℕ → ℝ)
    (x0 : Fin m → ℝ)
    (U : Set (Fin m → ℝ))
    (hφ_compact :
      ∀ n, HasCompactSupport (φ n : (Fin m → ℝ) → ℂ))
    (hφ_support :
      ∀ n, Function.support (φ n : (Fin m → ℝ) → ℂ) ⊆
        Metric.ball (0 : Fin m → ℝ) (r n))
    (hr : Tendsto r atTop (𝓝 0))
    (hU : U ∈ 𝓝 x0) :
    ∀ᶠ n in atTop,
      SCV.SupportsInOpen
          (SCV.translateSchwartz (-x0) (φ n) :
            (Fin m → ℝ) → ℂ) U ∧
        Set.MapsTo (fun y : Fin m → ℝ => x0 + y)
          (tsupport (φ n : (Fin m → ℝ) → ℂ)) U := by
  obtain ⟨ε, hε_pos, hε_sub⟩ := Metric.mem_nhds_iff.mp hU
  have hr_small : ∀ᶠ n : ℕ in atTop, r n < ε := by
    have hdist : ∀ᶠ n : ℕ in atTop, dist (r n) 0 < ε :=
      (Metric.tendsto_nhds.mp hr) ε hε_pos
    filter_upwards [hdist] with n hn
    rw [Real.dist_eq] at hn
    exact lt_of_le_of_lt (le_abs_self (r n)) (by simpa using hn)
  filter_upwards [hr_small] with n hn_small
  have hφ_tsupport_closed :
      tsupport (φ n : (Fin m → ℝ) → ℂ) ⊆
        Metric.closedBall (0 : Fin m → ℝ) (r n) := by
    change closure (Function.support (φ n : (Fin m → ℝ) → ℂ)) ⊆
      Metric.closedBall (0 : Fin m → ℝ) (r n)
    exact
      closure_minimal
        (fun y hy => Metric.ball_subset_closedBall (hφ_support n hy))
        Metric.isClosed_closedBall
  constructor
  · constructor
    · simpa [SCV.translateSchwartz_apply, Function.comp_def] using
        (hφ_compact n).comp_homeomorph (Homeomorph.addRight (-x0))
    · intro x hx
      have hx_pre :
          x + (-x0) ∈ tsupport (φ n : (Fin m → ℝ) → ℂ) := by
        exact
          tsupport_comp_subset_preimage
            (φ n : (Fin m → ℝ) → ℂ)
            (f := fun y : Fin m → ℝ => y + (-x0))
            (Homeomorph.addRight (-x0)).continuous hx
      have hclosed := hφ_tsupport_closed hx_pre
      have hdist_eq : dist x x0 = dist (x + (-x0)) 0 := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        ext i
        simp [Pi.sub_apply, sub_eq_add_neg]
      apply hε_sub
      rw [Metric.mem_ball, hdist_eq]
      exact lt_of_le_of_lt (Metric.mem_closedBall.mp hclosed) hn_small
  · intro y hy
    have hclosed := hφ_tsupport_closed hy
    have hdist_eq : dist (x0 + y) x0 = dist y 0 := by
      rw [dist_eq_norm, dist_eq_norm]
      congr 1
      ext i
      simp [Pi.sub_apply]
    apply hε_sub
    rw [Metric.mem_ball, hdist_eq]
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hclosed) hn_small

/-- Compact-support integrability against a scalar branch that is continuous
on the neighborhood reached by the shifted support. -/
theorem integrable_schwartz_mul_continuousOn_shift_of_tsupport_mapsTo
    {m : ℕ}
    (h : SchwartzMap (Fin m → ℝ) ℂ)
    (F : (Fin m → ℝ) → ℂ)
    (x0 : Fin m → ℝ)
    (U : Set (Fin m → ℝ))
    (hh_compact : HasCompactSupport (h : (Fin m → ℝ) → ℂ))
    (hmaps :
      Set.MapsTo (fun y : Fin m → ℝ => x0 + y)
        (tsupport (h : (Fin m → ℝ) → ℂ)) U)
    (hF_cont : ContinuousOn F U) :
    Integrable (fun y : Fin m → ℝ => h y * F (x0 + y)) := by
  let K : Set (Fin m → ℝ) := tsupport (h : (Fin m → ℝ) → ℂ)
  let f : (Fin m → ℝ) → ℂ := fun y => h y * F (x0 + y)
  have hK_compact : IsCompact K := hh_compact
  have hshift_cont :
      ContinuousOn (fun y : Fin m → ℝ => F (x0 + y)) K := by
    exact hF_cont.comp
      ((continuous_const.add continuous_id).continuousOn) hmaps
  have hf_cont : ContinuousOn f K := by
    exact (SchwartzMap.continuous h).continuousOn.mul hshift_cont
  have hf_integrableOn : IntegrableOn f K :=
    hf_cont.integrableOn_compact hK_compact
  have hindicator_integrable : Integrable (K.indicator f) := by
    rw [integrable_indicator_iff hK_compact.measurableSet]
    exact hf_integrableOn
  have hindicator_eq : K.indicator f = f := by
    funext y
    by_cases hy : y ∈ K
    · simp [Set.indicator_of_mem hy]
    · have hzero : h y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [Set.indicator_of_notMem hy, f, hzero]
  simpa [hindicator_eq, f] using hindicator_integrable

end OSReconstruction
