import OSReconstruction.Wightman.Reconstruction.TwoPointKernelFunctional
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAOneVariableUniqueness
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.Support

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Complex Filter MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- If the fixed-strip diagonal matrix elements are represented by a common
one-variable difference kernel against the descended center-shear test, then
the exact center factorization needed for VI.1 Input A is automatic from the
existing difference-kernel factorization theorem. -/
theorem fixed_strip_diagonal_eq_center_factorization_of_difference_kernel_pairing_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (s : ℝ)
    (K_s : SpacetimeDim d → ℂ)
    (hpair : ∀ n,
      let xφ : OSHilbertSpace OS :=
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
                (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                  (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧)) :
            OSHilbertSpace OS))
      osSemigroupGroupMatrixElement (d := d) OS lgc xφ (s + s) (0 : Fin d → ℝ) =
        ∫ x : NPointDomain d 2,
          twoPointDifferenceKernel (d := d) K_s x *
            (twoPointDifferenceLift χ₀
              (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
                (reflectedSchwartzSpacetime (φ_seq n))) x)) :
    ∀ n,
      let xφ : OSHilbertSpace OS :=
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
                (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                  (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧)) :
            OSHilbertSpace OS))
      osSemigroupGroupMatrixElement (d := d) OS lgc xφ (s + s) (0 : Fin d → ℝ) =
        ∫ ξ : SpacetimeDim d,
          (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
            (reflectedSchwartzSpacetime (φ_seq n))) ξ * K_s ξ := by
  intro n
  let χn : SchwartzSpacetime d :=
    OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
      (reflectedSchwartzSpacetime (φ_seq n))
  let I_n : ℂ :=
    let xφ : OSHilbertSpace OS :=
      (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single 1
              (SchwartzNPoint.osConj (d := d) (n := 1)
                (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
              (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧)) :
          OSHilbertSpace OS))
    osSemigroupGroupMatrixElement (d := d) OS lgc xφ (s + s) (0 : Fin d → ℝ)
  have hpair_n :
      I_n =
        ∫ x : NPointDomain d 2,
          twoPointDifferenceKernel (d := d) K_s x *
            twoPointDifferenceLift χ₀ χn x := by
    simpa [I_n, χn] using (hpair n)
  have hmain : I_n = ∫ ξ : SpacetimeDim d, χn ξ * K_s ξ := by
    calc
      I_n = ∫ x : NPointDomain d 2,
          twoPointDifferenceKernel (d := d) K_s x *
            twoPointDifferenceLift χ₀ χn x := hpair_n
      _ = (∫ u : SpacetimeDim d, χ₀ u) * ∫ ξ : SpacetimeDim d, K_s ξ * χn ξ := by
          exact integral_twoPointDifferenceKernel_mul_differenceLift_factorizes
            (d := d) K_s χ₀ χn
      _ = ∫ ξ : SpacetimeDim d, K_s ξ * χn ξ := by
          simp [hχ₀]
      _ = ∫ ξ : SpacetimeDim d, χn ξ * K_s ξ := by
          refine integral_congr_ae ?_
          filter_upwards with ξ
          ring
  simpa [I_n, χn] using hmain

/-- The descended VI.1 regularizers only need continuity on a fixed positive-time
strip around the origin to recover the value at `0`. This is the honest
one-variable input produced by the fixed-strip kernel route. -/
theorem descended_center_approxIdentity_integral_tendsto_of_continuousOn_fixedStrip_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (t : ℝ)
    (ht : 0 < t)
    {ψ : SpacetimeDim d → ℂ}
    (hψ_cont : ContinuousOn ψ {ξ : SpacetimeDim d | -t < ξ 0}) :
    Filter.Tendsto
      (fun n =>
        ∫ ξ : SpacetimeDim d,
          (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
            (reflectedSchwartzSpacetime (φ_seq n))) ξ * ψ ξ)
      Filter.atTop
      (nhds (ψ 0)) := by
  obtain ⟨χ_seq, hχ_seq_desc, hχ_seq_nonneg, hχ_seq_real, hχ_seq_int, _,
      _hχ_seq_ball_closed⟩ :=
    exists_k2_VI1_descended_center_package_local
      (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_ball
  have hrewrite :
      (fun n =>
        ∫ ξ : SpacetimeDim d,
          (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
            (reflectedSchwartzSpacetime (φ_seq n))) ξ * ψ ξ) =
      (fun n => ∫ ξ : SpacetimeDim d, χ_seq n ξ * ψ ξ) := by
    funext n
    simp [hχ_seq_desc n]
  rw [hrewrite]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hψ_cont0 :
      ContinuousAt ψ 0 :=
    OSReconstruction.continuousAt_zero_of_continuousOn_fixedStrip_local
      (d := d) t ht hψ_cont
  rw [Metric.continuousAt_iff] at hψ_cont0
  obtain ⟨δ0, hδ0_pos, hδ0⟩ := hψ_cont0 (ε / 2) hε2
  have heval0 : ContinuousAt (fun ξ : SpacetimeDim d => ξ 0) 0 :=
    (continuous_apply (0 : Fin (d + 1))).continuousAt
  rw [Metric.continuousAt_iff] at heval0
  obtain ⟨δ1, hδ1_pos, hδ1⟩ := heval0 t ht
  let δ : ℝ := min δ0 δ1
  have hδ_pos : 0 < δ := lt_min hδ0_pos hδ1_pos
  have hsmall :
      ∀ᶠ n : ℕ in Filter.atTop,
        tsupport ((χ_seq n : SchwartzSpacetime d) : SpacetimeDim d → ℂ) ⊆
          Metric.ball (0 : SpacetimeDim d) δ := by
    have hsmall_raw :=
      eventually_tsupport_descended_center_package_subset_ball_local
        (d := d) φ_seq hφ_ball hδ_pos
    filter_upwards [hsmall_raw] with n hn
    simpa [hχ_seq_desc n, δ] using hn
  filter_upwards [hsmall] with n hn
  let U : Set (SpacetimeDim d) := {ξ : SpacetimeDim d | -t < ξ 0}
  have hU : IsOpen U := by
    simpa [U] using isOpen_lt continuous_const (continuous_apply (0 : Fin (d + 1)))
  have hχ_compact :
      HasCompactSupport ((χ_seq n : SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : SpacetimeDim d) δ) ?_
    intro x hx
    have hxball : x ∈ Metric.ball (0 : SpacetimeDim d) δ := hn (subset_closure hx)
    have hxdist : dist x 0 < δ := by
      simpa [Metric.mem_ball] using hxball
    exact Metric.mem_closedBall.mpr (le_of_lt hxdist)
  let S : Set (SpacetimeDim d) :=
    tsupport ((χ_seq n : SchwartzSpacetime d) : SpacetimeDim d → ℂ)
  have hS_compact : IsCompact S := by
    simpa [S, HasCompactSupport] using hχ_compact
  have hS_subset_U : S ⊆ U := by
    intro x hx
    have hxball : x ∈ Metric.ball (0 : SpacetimeDim d) δ := hn hx
    have hxdist1 : dist x 0 < δ1 := by
      have hxdist : dist x 0 < δ := by
        simpa [Metric.mem_ball] using hxball
      exact lt_of_lt_of_le hxdist (min_le_right _ _)
    have hx0dist : dist (x 0) 0 < t := by
      simpa using hδ1 hxdist1
    have hx0abs : |x 0| < t := by
      simpa [dist_eq_norm] using hx0dist
    have hneg : -(abs (x 0)) ≤ x 0 := by
      exact neg_abs_le (x 0)
    have habs_le : -t < -(abs (x 0)) := by
      linarith
    have : -t < x 0 := lt_of_lt_of_le habs_le hneg
    simpa [U] using this
  have hnorm_int : ∫ x : SpacetimeDim d, ‖χ_seq n x‖ = 1 := by
    have hnorm_re : ∀ x : SpacetimeDim d, ‖χ_seq n x‖ = (χ_seq n x).re := by
      intro x
      rw [← Complex.re_eq_norm.mpr ⟨hχ_seq_nonneg n x, (hχ_seq_real n x).symm⟩]
    simp_rw [hnorm_re]
    rw [show (fun x => (χ_seq n x).re) = (fun x => RCLike.re (χ_seq n x)) from rfl]
    rw [integral_re (SchwartzMap.integrable (χ_seq n))]
    exact congrArg Complex.re (hχ_seq_int n)
  have hbound :
      ∀ x : SpacetimeDim d,
        ‖χ_seq n x * (ψ x - ψ 0)‖ ≤ (ε / 2) * ‖χ_seq n x‖ := by
    intro x
    by_cases hx : x ∈ tsupport ((χ_seq n : SchwartzSpacetime d) : SpacetimeDim d → ℂ)
    · have hxball : x ∈ Metric.ball (0 : SpacetimeDim d) δ := hn hx
      have hxdist0 : dist x 0 < δ0 := by
        have hxdist : dist x 0 < δ := by
          simpa [Metric.mem_ball] using hxball
        exact lt_of_lt_of_le hxdist (min_le_left _ _)
      have hψx : ‖ψ x - ψ 0‖ < ε / 2 := by
        simpa [dist_eq_norm] using hδ0 hxdist0
      calc
        ‖χ_seq n x * (ψ x - ψ 0)‖ = ‖χ_seq n x‖ * ‖ψ x - ψ 0‖ := by
          rw [norm_mul]
        _ ≤ ‖χ_seq n x‖ * (ε / 2) := by
          gcongr
        _ = (ε / 2) * ‖χ_seq n x‖ := by ring
    · have hx0 : χ_seq n x = 0 := by
        by_contra hx0
        exact hx (subset_tsupport _ (Function.mem_support.mpr hx0))
      simp [hx0]
  have hψS :
      IntegrableOn ψ S volume := by
    exact (hψ_cont.locallyIntegrableOn hU.measurableSet).integrableOn_compact_subset
      hS_subset_U hS_compact
  have hψ_prod :
      Integrable (fun x : SpacetimeDim d => χ_seq n x * ψ x) := by
    have hprod_on :
        IntegrableOn (fun x : SpacetimeDim d => χ_seq n x * ψ x) S volume := by
      simpa [smul_eq_mul] using
        hψS.continuousOn_smul (SchwartzMap.continuous (χ_seq n)).continuousOn hS_compact
    refine hprod_on.integrable_of_forall_notMem_eq_zero ?_
    intro x hx
    have hx_support :
        x ∉ Function.support ((χ_seq n : SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
      exact fun hx' => hx (subset_closure hx')
    simp [Function.mem_support] at hx_support
    simp [hx_support]
  have hEqInt :
      (∫ x : SpacetimeDim d, χ_seq n x * ψ x) - ψ 0 =
        ∫ x : SpacetimeDim d, χ_seq n x * (ψ x - ψ 0) := by
    have hconst_int :
        ∫ x : SpacetimeDim d, (ψ 0) * χ_seq n x = ψ 0 := by
      calc
        ∫ x : SpacetimeDim d, (ψ 0) * χ_seq n x
            = (ψ 0) * ∫ x : SpacetimeDim d, χ_seq n x := by
                exact MeasureTheory.integral_const_mul (ψ 0) (fun x : SpacetimeDim d => χ_seq n x)
        _ = ψ 0 := by simpa [hχ_seq_int n]
    calc
      (∫ x : SpacetimeDim d, χ_seq n x * ψ x) - ψ 0
          = (∫ x : SpacetimeDim d, χ_seq n x * ψ x) -
              ∫ x : SpacetimeDim d, (ψ 0) * χ_seq n x := by
                rw [hconst_int]
      _ = ∫ x : SpacetimeDim d, ((χ_seq n x * ψ x) - (ψ 0) * χ_seq n x) := by
            rw [← MeasureTheory.integral_sub hψ_prod
              ((SchwartzMap.integrable (χ_seq n)).const_mul (ψ 0))]
      _ = ∫ x : SpacetimeDim d, χ_seq n x * (ψ x - ψ 0) := by
            congr with x
            ring
  calc
    dist (∫ x : SpacetimeDim d, χ_seq n x * ψ x) (ψ 0)
        = ‖(∫ x : SpacetimeDim d, χ_seq n x * ψ x) - ψ 0‖ := by
            rw [dist_eq_norm]
    _ = ‖∫ x : SpacetimeDim d, χ_seq n x * (ψ x - ψ 0)‖ := by
          rw [hEqInt]
    _ ≤ ∫ x : SpacetimeDim d, ‖χ_seq n x * (ψ x - ψ 0)‖ := by
          exact norm_integral_le_integral_norm _
    _ ≤ ∫ x : SpacetimeDim d, (ε / 2) * ‖χ_seq n x‖ := by
          apply MeasureTheory.integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
          · exact (((SchwartzMap.integrable (χ_seq n)).norm).const_mul (ε / 2))
          · exact Filter.Eventually.of_forall hbound
    _ = (ε / 2) * ∫ x : SpacetimeDim d, ‖χ_seq n x‖ := by
          rw [MeasureTheory.integral_const_mul]
    _ = ε / 2 := by
          simp [hnorm_int]
    _ < ε := by
          linarith

/-- Fixed-strip variant of the Input-A diagonal limit theorem: continuity on the
strip `{- (s+s) < ξ₀}` already suffices because the descended center package is
eventually supported inside that strip. -/
theorem exists_fixed_strip_diagonal_limit_of_difference_kernel_pairing_on_fixedStrip_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (s : ℝ)
    (hs : 0 < s)
    (K_s : SpacetimeDim d → ℂ)
    (hK_strip : ContinuousOn K_s {ξ : SpacetimeDim d | -(s + s) < ξ 0})
    (hpair : ∀ n,
      let xφ : OSHilbertSpace OS :=
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
                (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                  (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧)) :
            OSHilbertSpace OS))
      osSemigroupGroupMatrixElement (d := d) OS lgc xφ (s + s) (0 : Fin d → ℝ) =
        ∫ x : NPointDomain d 2,
          twoPointDifferenceKernel (d := d) K_s x *
            (twoPointDifferenceLift χ₀
              (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
                (reflectedSchwartzSpacetime (φ_seq n))) x)) :
    ∃ z : ℂ,
      Filter.Tendsto
        (fun n =>
          let xφ : OSHilbertSpace OS :=
            (((show OSPreHilbertSpace OS from
                (⟦PositiveTimeBorchersSequence.single 1
                    (SchwartzNPoint.osConj (d := d) (n := 1)
                      (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
                (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                      (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧)) :
                OSHilbertSpace OS))
          osSemigroupGroupMatrixElement (d := d) OS lgc xφ (s + s) (0 : Fin d → ℝ))
        Filter.atTop
        (nhds z) := by
  refine ⟨K_s 0, ?_⟩
  have happrox :=
    descended_center_approxIdentity_integral_tendsto_of_continuousOn_fixedStrip_local
      (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_ball (s + s) (add_pos hs hs) hK_strip
  refine Filter.Tendsto.congr' ?_ happrox
  filter_upwards with n
  exact (fixed_strip_diagonal_eq_center_factorization_of_difference_kernel_pairing_local
    (d := d) OS lgc χ₀ hχ₀ φ_seq hφ_compact hφ_neg s K_s hpair n).symm

/-- So the only genuine remaining content of VI.1 Input A can be taken to be a
fixed-strip common difference-kernel pairing theorem. Once that is available,
the existing descended-center approximate-identity theorem closes the diagonal
convergence immediately. -/
theorem exists_fixed_strip_diagonal_limit_of_difference_kernel_pairing_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ u : SpacetimeDim d, χ₀ u = 1)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (s : ℝ)
    (_hs : 0 < s)
    (K_s : SpacetimeDim d → ℂ)
    (hK_cont : Continuous K_s)
    (hpair : ∀ n,
      let xφ : OSHilbertSpace OS :=
        (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single 1
                (SchwartzNPoint.osConj (d := d) (n := 1)
                  (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
                (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                  (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧)) :
            OSHilbertSpace OS))
      osSemigroupGroupMatrixElement (d := d) OS lgc xφ (s + s) (0 : Fin d → ℝ) =
        ∫ x : NPointDomain d 2,
          twoPointDifferenceKernel (d := d) K_s x *
            (twoPointDifferenceLift χ₀
              (OSReconstruction.twoPointCenterShearDescent (d := d) (φ_seq n)
                (reflectedSchwartzSpacetime (φ_seq n))) x)) :
    ∃ z : ℂ,
      Filter.Tendsto
        (fun n =>
          let xφ : OSHilbertSpace OS :=
            (((show OSPreHilbertSpace OS from
                (⟦PositiveTimeBorchersSequence.single 1
                    (SchwartzNPoint.osConj (d := d) (n := 1)
                      (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
                    (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
                      (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧)) :
                OSHilbertSpace OS))
          osSemigroupGroupMatrixElement (d := d) OS lgc xφ (s + s) (0 : Fin d → ℝ))
        Filter.atTop
        (nhds z) := by
  refine ⟨K_s 0, ?_⟩
  have happrox :=
    descended_center_approxIdentity_integral_tendsto_of_continuousAt_zero_local
      (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_ball hK_cont
  refine Filter.Tendsto.congr' ?_ happrox
  filter_upwards with n
  exact (fixed_strip_diagonal_eq_center_factorization_of_difference_kernel_pairing_local
    (d := d) OS lgc χ₀ hχ₀ φ_seq hφ_compact hφ_neg s K_s hpair n).symm

end OSReconstruction
