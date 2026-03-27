import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanK2VI1Support

noncomputable section

open Complex Filter MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- A normalized real nonnegative approximate identity with shrinking support
recovers the value of any function continuous at `0`. This is the direct
one-variable convergence input needed for the sharpened Input A route. -/
theorem approxIdentity_integral_tendsto_of_continuousAt_zero_vi1InputA_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_support : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    {ψ : SpacetimeDim d → ℂ}
    (hψ_cont : Continuous ψ) :
    Filter.Tendsto (fun n => ∫ x : SpacetimeDim d, φ_seq n x * ψ x)
      Filter.atTop (nhds (ψ 0)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hψ_cont0 : ContinuousAt ψ 0 := hψ_cont.continuousAt
  rw [Metric.continuousAt_iff] at hψ_cont0
  obtain ⟨δ, hδpos, hδ⟩ := hψ_cont0 (ε / 2) hε2
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop, 1 / (n + 1 : ℝ) < δ := by
    rcases exists_nat_one_div_lt hδpos with ⟨N, hN⟩
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hmono : 1 / (n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) := by
      have hNle : (N + 1 : ℝ) ≤ n + 1 := by
        exact_mod_cast Nat.succ_le_succ hn
      exact one_div_le_one_div_of_le (by positivity) hNle
    exact lt_of_le_of_lt hmono hN
  filter_upwards [hsmall] with n hn
  have hnorm_int : ∫ x : SpacetimeDim d, ‖φ_seq n x‖ = 1 := by
    have hnorm_re : ∀ x : SpacetimeDim d, ‖φ_seq n x‖ = (φ_seq n x).re := by
      intro x
      rw [← Complex.re_eq_norm.mpr ⟨hφ_nonneg n x, (hφ_real n x).symm⟩]
    simp_rw [hnorm_re]
    rw [show (fun x => (φ_seq n x).re) = (fun x => RCLike.re (φ_seq n x)) from rfl]
    rw [integral_re (SchwartzMap.integrable (φ_seq n))]
    exact congrArg Complex.re (hφ_int n)
  have hbound : ∀ x : SpacetimeDim d,
      ‖φ_seq n x * (ψ x - ψ 0)‖ ≤ (ε / 2) * ‖φ_seq n x‖ := by
    intro x
    by_cases hx : x ∈ tsupport (φ_seq n : SpacetimeDim d → ℂ)
    ·
      have hxball : x ∈ Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)) := hφ_support n hx
      have hxdist : dist x 0 < δ := by
        have : dist x 0 < 1 / (n + 1 : ℝ) := by
          simpa [Metric.mem_ball] using hxball
        exact lt_of_lt_of_le this hn.le
      have hψx : ‖ψ x - ψ 0‖ < ε / 2 := by
        simpa [dist_eq_norm] using hδ hxdist
      calc
        ‖φ_seq n x * (ψ x - ψ 0)‖ = ‖φ_seq n x‖ * ‖ψ x - ψ 0‖ := by
          rw [norm_mul]
        _ ≤ ‖φ_seq n x‖ * (ε / 2) := by
          gcongr
        _ = (ε / 2) * ‖φ_seq n x‖ := by ring
    ·
      have hx0 : φ_seq n x = 0 := by
        by_contra hx0
        exact hx (subset_tsupport _ (Function.mem_support.mpr hx0))
      simp [hx0]
  have hmeas : AEStronglyMeasurable (fun x => φ_seq n x * (ψ x - ψ 0)) := by
    exact ((SchwartzMap.continuous (φ_seq n)).mul
      (hψ_cont.sub continuous_const)).aestronglyMeasurable
  have hIntDiff : Integrable (fun x : SpacetimeDim d => φ_seq n x * (ψ x - ψ 0)) := by
    refine Integrable.mono'
      (((SchwartzMap.integrable (φ_seq n)).norm).const_mul (ε / 2)) hmeas ?_
    exact Filter.Eventually.of_forall hbound
  have hIntProd : Integrable (fun x : SpacetimeDim d => φ_seq n x * ψ x) := by
    have hEq : (fun x : SpacetimeDim d => φ_seq n x * ψ x) =
        fun x => φ_seq n x * (ψ x - ψ 0) + (ψ 0) * φ_seq n x := by
      funext x
      ring
    rw [hEq]
    exact hIntDiff.add ((SchwartzMap.integrable (φ_seq n)).const_mul (ψ 0))
  have hEqInt :
      (∫ x : SpacetimeDim d, φ_seq n x * ψ x) - ψ 0 =
        ∫ x : SpacetimeDim d, φ_seq n x * (ψ x - ψ 0) := by
    calc
      (∫ x : SpacetimeDim d, φ_seq n x * ψ x) - ψ 0
          = (∫ x : SpacetimeDim d, φ_seq n x * ψ x) -
              ∫ x : SpacetimeDim d, (ψ 0) * φ_seq n x := by
                rw [MeasureTheory.integral_const_mul, hφ_int n]
                ring
      _ = ∫ x : SpacetimeDim d, ((φ_seq n x * ψ x) - (ψ 0) * φ_seq n x) := by
            rw [← MeasureTheory.integral_sub hIntProd
              ((SchwartzMap.integrable (φ_seq n)).const_mul (ψ 0))]
      _ = ∫ x : SpacetimeDim d, φ_seq n x * (ψ x - ψ 0) := by
            congr with x
            ring
  calc
    dist (∫ x : SpacetimeDim d, φ_seq n x * ψ x) (ψ 0)
        = ‖(∫ x : SpacetimeDim d, φ_seq n x * ψ x) - ψ 0‖ := by
            rw [dist_eq_norm]
    _ = ‖∫ x : SpacetimeDim d, φ_seq n x * (ψ x - ψ 0)‖ := by
          rw [hEqInt]
    _ ≤ ∫ x : SpacetimeDim d, ‖φ_seq n x * (ψ x - ψ 0)‖ := by
          exact norm_integral_le_integral_norm _
    _ ≤ ∫ x : SpacetimeDim d, (ε / 2) * ‖φ_seq n x‖ := by
          apply MeasureTheory.integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
          · exact (((SchwartzMap.integrable (φ_seq n)).norm).const_mul (ε / 2))
          · exact Filter.Eventually.of_forall hbound
    _ = (ε / 2) * ∫ x : SpacetimeDim d, ‖φ_seq n x‖ := by
          rw [MeasureTheory.integral_const_mul]
    _ = ε / 2 := by
          simp [hnorm_int]
    _ < ε := by
          linarith

/-- The reflected companions of a shrinking negative approximate identity are
again an honest approximate identity for continuous one-variable kernels. -/
theorem reflected_negativeApproxIdentity_integral_tendsto_of_continuousAt_zero_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    {K : SpacetimeDim d → ℂ}
    (hK_cont : Continuous K) :
    Filter.Tendsto
      (fun n =>
        ∫ ξ : SpacetimeDim d,
          reflectedSchwartzSpacetime (φ_seq n) ξ * K ξ)
      Filter.atTop (nhds (K 0)) := by
  have hψ_nonneg : ∀ n y, 0 ≤ (reflectedSchwartzSpacetime (φ_seq n) y).re := by
    intro n y
    simpa [reflectedSchwartzSpacetime,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
      hφ_nonneg n (timeReflection d y)
  have hψ_real : ∀ n y, (reflectedSchwartzSpacetime (φ_seq n) y).im = 0 := by
    intro n y
    simpa [reflectedSchwartzSpacetime,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
      hφ_real n (timeReflection d y)
  have hψ_int :
      ∀ n, ∫ y : SpacetimeDim d, reflectedSchwartzSpacetime (φ_seq n) y = 1 := by
    intro n
    rw [reflectedSchwartzSpacetime_integral_eq_local]
    exact hφ_int n
  have hψ_ball :
      ∀ n, tsupport (reflectedSchwartzSpacetime (φ_seq n) : SpacetimeDim d → ℂ) ⊆
        Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)) := by
    intro n
    exact reflectedSchwartzSpacetime_tsupport_ball (d := d) (φ_seq n) (hφ_ball n)
  simpa using
    approxIdentity_integral_tendsto_of_continuousAt_zero_vi1InputA_local
      (d := d) (fun n => reflectedSchwartzSpacetime (φ_seq n))
      hψ_nonneg hψ_real hψ_int hψ_ball hK_cont

/-- If the fixed-strip diagonal matrix elements are represented by a common
continuous kernel against the reflected approximate identity itself, then the
Input A diagonal limit is immediate from one-variable approximate-identity
convergence. -/
theorem exists_fixed_strip_diagonal_limit_of_reflected_kernel_pairing_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
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
        ∫ ξ : SpacetimeDim d,
          K_s ξ * reflectedSchwartzSpacetime (φ_seq n) ξ) :
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
    reflected_negativeApproxIdentity_integral_tendsto_of_continuousAt_zero_local
      (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_ball hK_cont
  refine Filter.Tendsto.congr' ?_ happrox
  filter_upwards with n
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
  have hpair_n : I_n = ∫ ξ : SpacetimeDim d, K_s ξ * reflectedSchwartzSpacetime (φ_seq n) ξ := by
    simpa [I_n] using hpair n
  have hpair_swapped :
      ∫ ξ : SpacetimeDim d, reflectedSchwartzSpacetime (φ_seq n) ξ * K_s ξ = I_n := by
    calc
      ∫ ξ : SpacetimeDim d, reflectedSchwartzSpacetime (φ_seq n) ξ * K_s ξ
        = ∫ ξ : SpacetimeDim d, K_s ξ * reflectedSchwartzSpacetime (φ_seq n) ξ := by
            refine integral_congr_ae ?_
            filter_upwards with ξ
            ring
      _ = I_n := hpair_n.symm
  simpa [I_n] using hpair_swapped

end OSReconstruction
