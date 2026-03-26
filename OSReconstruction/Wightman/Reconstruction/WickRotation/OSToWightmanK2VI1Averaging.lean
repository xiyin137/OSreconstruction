import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanK2VI1RegularizationDeriv
import OSReconstruction.Wightman.Reconstruction.TwoPointDescent

noncomputable section

open MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- The regularized reflected-probe family has a uniform global Lipschitz
constant, controlled only by the fixed target test `h`. This is the direct
OS-side replacement for the fixed-test Lipschitz input used in the older
descended-center estimate. -/
theorem positiveTimeCompactSupportConvolution_reflected_negativeApproxIdentity_lipschitz_uniform_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (h : positiveTimeCompactSupportSubmodule d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n (x y : SpacetimeDim d),
      let ψn : positiveTimeCompactSupportSubmodule d :=
        ⟨reflectedSchwartzSpacetime (φ_seq n),
          ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
            reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
              (hφ_compact n)⟩⟩
      let convn : SchwartzSpacetime d :=
        (((positiveTimeCompactSupportConvolution ψn h : positiveTimeCompactSupportSubmodule d) :
          SchwartzSpacetime d))
      ‖convn x - convn y‖ ≤ C * ‖x - y‖ := by
  let C0 : ℝ := SchwartzMap.seminorm ℝ 0 1 (h : SchwartzSpacetime d)
  refine ⟨max C0 1, by positivity, ?_⟩
  intro n x y
  let ψn : positiveTimeCompactSupportSubmodule d :=
    ⟨reflectedSchwartzSpacetime (φ_seq n),
      ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
        reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
          (hφ_compact n)⟩⟩
  let convn : SchwartzSpacetime d :=
    (((positiveTimeCompactSupportConvolution ψn h : positiveTimeCompactSupportSubmodule d) :
      SchwartzSpacetime d))
  have hfderiv_bound : ∀ z : SpacetimeDim d, ‖fderiv ℝ (convn : SpacetimeDim d → ℂ) z‖ ≤ C0 := by
    intro z
    simpa [C0, ψn, convn] using
      positiveTimeCompactSupportConvolution_reflected_negativeApproxIdentity_fderiv_norm_le_seminorm_one_local
        (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg h n z
  have hdiff : Differentiable ℝ (convn : SpacetimeDim d → ℂ) := convn.differentiable
  have hmain :
    ‖(convn : SpacetimeDim d → ℂ) x - convn y‖ = ‖(convn : SpacetimeDim d → ℂ) y - convn x‖ := by
      rw [norm_sub_rev]
  calc
    ‖(convn : SpacetimeDim d → ℂ) x - convn y‖ = ‖(convn : SpacetimeDim d → ℂ) y - convn x‖ := hmain
    _ ≤ C0 * ‖y - x‖ := by
          exact Convex.norm_image_sub_le_of_norm_fderiv_le
            (fun z _ => hdiff.differentiableAt) (fun z _ => hfderiv_bound z)
            convex_univ (Set.mem_univ y) (Set.mem_univ x)
    _ ≤ max C0 1 * ‖y - x‖ := by
          apply mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    _ = max C0 1 * ‖x - y‖ := by rw [norm_sub_rev]

/-- The descended center-shear kernels act as a quantitative approximate
identity on the `n`-dependent regularized reflected-probe family. The error is
uniform in both `n` and the evaluation point. -/
theorem exists_descended_center_regularized_translate_uniform_error_bound_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (h : positiveTimeCompactSupportSubmodule d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n ξ,
      let ψn : positiveTimeCompactSupportSubmodule d :=
        ⟨reflectedSchwartzSpacetime (φ_seq n),
          ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
            reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
              (hφ_compact n)⟩⟩
      let gn : SchwartzSpacetime d :=
        (((positiveTimeCompactSupportConvolution ψn h : positiveTimeCompactSupportSubmodule d) :
          SchwartzSpacetime d))
      dist
          (∫ u : SpacetimeDim d,
            (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
              (reflectedSchwartzSpacetime (φ_seq n))) u *
                (SCV.translateSchwartz (-u) gn) ξ)
          (gn ξ) ≤
        C * (2 / (n + 1 : ℝ)) := by
  obtain ⟨C, hC_pos, hLip⟩ :=
    positiveTimeCompactSupportConvolution_reflected_negativeApproxIdentity_lipschitz_uniform_local
      (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg h
  refine ⟨C, hC_pos, ?_⟩
  intro n ξ
  let ψn : positiveTimeCompactSupportSubmodule d :=
    ⟨reflectedSchwartzSpacetime (φ_seq n),
      ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
        reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
          (hφ_compact n)⟩⟩
  let gn : SchwartzSpacetime d :=
    (((positiveTimeCompactSupportConvolution ψn h : positiveTimeCompactSupportSubmodule d) :
      SchwartzSpacetime d))
  let χn : SchwartzSpacetime d :=
    OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
      (reflectedSchwartzSpacetime (φ_seq n))
  have hψ_nonneg : ∀ x : SpacetimeDim d, 0 ≤ (reflectedSchwartzSpacetime (φ_seq n) x).re := by
    intro x
    change 0 ≤ (φ_seq n (timeReflection d x)).re
    simpa [timeReflection] using hφ_nonneg n (timeReflection d x)
  have hψ_real : ∀ x : SpacetimeDim d, (reflectedSchwartzSpacetime (φ_seq n) x).im = 0 := by
    intro x
    change (φ_seq n (timeReflection d x)).im = 0
    simpa [timeReflection] using hφ_real n (timeReflection d x)
  have hχ_nonneg : ∀ x : SpacetimeDim d, 0 ≤ (χn x).re := by
    simpa [χn] using
      (OSReconstruction.twoPointCenterShearDescent_re_nonneg_of_re_nonneg
        (d := d) (φ_seq n) (reflectedSchwartzSpacetime (φ_seq n))
        (hφ_real n) hψ_real (hφ_nonneg n) hψ_nonneg)
  have hχ_real : ∀ x : SpacetimeDim d, (χn x).im = 0 := by
    simpa [χn] using
      (OSReconstruction.twoPointCenterShearDescent_im_eq_zero_of_im_eq_zero
        (d := d) (φ_seq n) (reflectedSchwartzSpacetime (φ_seq n))
        (hφ_real n) hψ_real)
  have hχ_int : ∫ u : SpacetimeDim d, χn u = 1 := by
    rw [show χn = OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
      (reflectedSchwartzSpacetime (φ_seq n)) by rfl]
    rw [OSReconstruction.integral_twoPointCenterShearDescent_eq_mul,
      reflectedSchwartzSpacetime_integral_eq_local]
    simp [hφ_int n]
  have hχ_norm_int : ∫ u : SpacetimeDim d, ‖χn u‖ = 1 := by
    have hnorm_re : ∀ u : SpacetimeDim d, ‖χn u‖ = (χn u).re := by
      intro u
      rw [← Complex.re_eq_norm.mpr ⟨hχ_nonneg u, (hχ_real u).symm⟩]
    simp_rw [hnorm_re]
    rw [show (fun u => (χn u).re) = (fun u => RCLike.re (χn u)) from rfl]
    rw [integral_re (SchwartzMap.integrable χn)]
    exact congrArg Complex.re hχ_int
  have hχ_ball :
      tsupport ((reflectedSchwartzSpacetime (φ_seq n) : SpacetimeDim d → ℂ)) ⊆
        Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)) :=
    reflectedSchwartzSpacetime_tsupport_ball (d := d) (φ_seq n) (hφ_ball n)
  have hχ_closed :
      tsupport (χn : SpacetimeDim d → ℂ) ⊆
        Metric.closedBall (0 : SpacetimeDim d)
          ((1 / (n + 1 : ℝ)) + (1 / (n + 1 : ℝ))) := by
    have hrad : 0 ≤ (1 / (n + 1 : ℝ)) := by positivity
    have hclosed :=
      OSReconstruction.twoPointCenterShearDescent_tsupport_subset_closedBall
        (d := d) (φ_seq n) (reflectedSchwartzSpacetime (φ_seq n))
        hrad hrad (hφ_ball n) hχ_ball
    simpa [χn] using hclosed
  have hrad_sum : ((1 / (n + 1 : ℝ)) + (1 / (n + 1 : ℝ))) = 2 / (n + 1 : ℝ) := by
    have hne : (n + 1 : ℝ) ≠ 0 := by positivity
    field_simp [hne]
    ring
  have hbound :
      ∀ u : SpacetimeDim d,
        ‖χn u * ((SCV.translateSchwartz (-u) gn) ξ - gn ξ)‖ ≤
          (C * (2 / (n + 1 : ℝ))) * ‖χn u‖ := by
    intro u
    by_cases hu : u ∈ tsupport (χn : SpacetimeDim d → ℂ)
    · have hu_ball : u ∈ Metric.closedBall (0 : SpacetimeDim d)
          ((1 / (n + 1 : ℝ)) + (1 / (n + 1 : ℝ))) := hχ_closed hu
      have hu_norm : ‖u‖ ≤ 2 / (n + 1 : ℝ) := by
        have hu_norm' : ‖u‖ ≤ (1 / (n + 1 : ℝ)) + (1 / (n + 1 : ℝ)) := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hu_ball
        rwa [hrad_sum] at hu_norm'
      have htrans :
          ‖(SCV.translateSchwartz (-u) gn) ξ - gn ξ‖ ≤ C * (2 / (n + 1 : ℝ)) := by
        calc
          ‖(SCV.translateSchwartz (-u) gn) ξ - gn ξ‖
              = ‖gn (ξ + -u) - gn ξ‖ := by
                  simp [SCV.translateSchwartz_apply]
          _ ≤ C * ‖(ξ + -u) - ξ‖ := hLip n (ξ + -u) ξ
          _ = C * ‖u‖ := by
                congr 1
                simp [sub_eq_add_neg, add_left_comm, add_comm]
          _ ≤ C * (2 / (n + 1 : ℝ)) := by
                gcongr
      calc
        ‖χn u * ((SCV.translateSchwartz (-u) gn) ξ - gn ξ)‖
            = ‖χn u‖ * ‖(SCV.translateSchwartz (-u) gn) ξ - gn ξ‖ := by
                rw [norm_mul]
        _ ≤ ‖χn u‖ * (C * (2 / (n + 1 : ℝ))) := by
              gcongr
        _ = (C * (2 / (n + 1 : ℝ))) * ‖χn u‖ := by ring
    · have hu0 : χn u = 0 := by
        by_contra hu0
        exact hu (subset_tsupport _ (Function.mem_support.mpr hu0))
      simp [hu0]
  have hψ_cont :
      Continuous fun u : SpacetimeDim d =>
        (SCV.translateSchwartz (-u) gn) ξ - gn ξ := by
    change Continuous (fun u : SpacetimeDim d => gn (ξ + -u) - gn ξ)
    exact (gn.continuous.comp (continuous_const.add continuous_neg)).sub continuous_const
  have hmeas :
      AEStronglyMeasurable
        (fun u : SpacetimeDim d =>
          χn u * ((SCV.translateSchwartz (-u) gn) ξ - gn ξ)) := by
    exact ((SchwartzMap.continuous χn).mul hψ_cont).aestronglyMeasurable
  have hIntDiff :
      Integrable
        (fun u : SpacetimeDim d =>
          χn u * ((SCV.translateSchwartz (-u) gn) ξ - gn ξ)) := by
    refine Integrable.mono'
      (((SchwartzMap.integrable χn).norm).const_mul (C * (2 / (n + 1 : ℝ))))
      hmeas ?_
    exact Filter.Eventually.of_forall hbound
  have hIntProd :
      Integrable
        (fun u : SpacetimeDim d => χn u * (SCV.translateSchwartz (-u) gn) ξ) := by
    have hEq :
        (fun u : SpacetimeDim d => χn u * (SCV.translateSchwartz (-u) gn) ξ) =
          fun u =>
            χn u * ((SCV.translateSchwartz (-u) gn) ξ - gn ξ) + (gn ξ) * χn u := by
      funext u
      ring
    rw [hEq]
    exact hIntDiff.add ((SchwartzMap.integrable χn).const_mul (gn ξ))
  have hEqInt :
      (∫ u : SpacetimeDim d, χn u * (SCV.translateSchwartz (-u) gn) ξ) - gn ξ =
        ∫ u : SpacetimeDim d,
          χn u * ((SCV.translateSchwartz (-u) gn) ξ - gn ξ) := by
    calc
      (∫ u : SpacetimeDim d, χn u * (SCV.translateSchwartz (-u) gn) ξ) - gn ξ
          =
        (∫ u : SpacetimeDim d, χn u * (SCV.translateSchwartz (-u) gn) ξ) -
          ∫ u : SpacetimeDim d, (gn ξ) * χn u := by
            rw [MeasureTheory.integral_const_mul, hχ_int]
            ring
      _ =
        ∫ u : SpacetimeDim d,
          (χn u * (SCV.translateSchwartz (-u) gn) ξ - (gn ξ) * χn u) := by
            rw [← MeasureTheory.integral_sub hIntProd
              ((SchwartzMap.integrable χn).const_mul (gn ξ))]
      _ =
        ∫ u : SpacetimeDim d,
          χn u * ((SCV.translateSchwartz (-u) gn) ξ - gn ξ) := by
            congr with u
            ring
  calc
    dist
        (∫ u : SpacetimeDim d,
          (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
            (reflectedSchwartzSpacetime (φ_seq n))) u *
              (SCV.translateSchwartz (-u) gn) ξ)
        (gn ξ)
        =
      ‖(∫ u : SpacetimeDim d, χn u * (SCV.translateSchwartz (-u) gn) ξ) - gn ξ‖ := by
          rw [dist_eq_norm]
    _ =
      ‖∫ u : SpacetimeDim d,
          χn u * ((SCV.translateSchwartz (-u) gn) ξ - gn ξ)‖ := by
            rw [hEqInt]
    _ ≤
      ∫ u : SpacetimeDim d,
        ‖χn u * ((SCV.translateSchwartz (-u) gn) ξ - gn ξ)‖ := by
          exact norm_integral_le_integral_norm _
    _ ≤
      ∫ u : SpacetimeDim d, (C * (2 / (n + 1 : ℝ))) * ‖χn u‖ := by
          apply MeasureTheory.integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
          · exact (((SchwartzMap.integrable χn).norm).const_mul (C * (2 / (n + 1 : ℝ))))
          · exact Filter.Eventually.of_forall hbound
    _ = (C * (2 / (n + 1 : ℝ))) * ∫ u : SpacetimeDim d, ‖χn u‖ := by
          rw [MeasureTheory.integral_const_mul]
    _ = C * (2 / (n + 1 : ℝ)) := by
          simp [hχ_norm_int]

end OSReconstruction
