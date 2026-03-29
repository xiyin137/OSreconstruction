import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.Bounds

noncomputable section

open MeasureTheory
open scoped BigOperators Pointwise

variable {d : ℕ} [NeZero d]

/-- The reflected approximate-identity smoothing sequence of a fixed positive-time
compactly supported test stays inside one uniform closed ball. This isolates the
support-control part of the OS II VI.1 spatial regularization argument in a
small companion file, without reopening the large support layer. -/
theorem exists_uniform_closedBall_support_reflected_negativeApproxIdentity_convolution_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (h : positiveTimeCompactSupportSubmodule d) :
    ∃ R : ℝ, 0 < R ∧ ∀ n,
      tsupport
          (((positiveTimeCompactSupportConvolution
              (⟨reflectedSchwartzSpacetime (φ_seq n),
                ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
                  reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
                    (hφ_compact n)⟩⟩)
              h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) ⊆
        Metric.closedBall (0 : SpacetimeDim d) R := by
  rcases h.property.2.isCompact.isBounded.subset_closedBall (0 : SpacetimeDim d) with ⟨Rh, hRh⟩
  refine ⟨|Rh| + 1, by positivity, ?_⟩
  intro n x hx
  let ψn : positiveTimeCompactSupportSubmodule d :=
    ⟨reflectedSchwartzSpacetime (φ_seq n),
      ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
        reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
          (hφ_compact n)⟩⟩
  have hψ_ball :
      tsupport ((ψn : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ⊆
        Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)) := by
    simpa [ψn] using
      reflectedSchwartzSpacetime_tsupport_ball (d := d) (φ_seq n) (hφ_ball n)
  have hsum_closed :
      IsClosed
        (tsupport (((ψn : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) +
          tsupport (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ)) := by
    exact (ψn.property.2.isCompact.add h.property.2.isCompact).isClosed
  have htsupp_subset :
      tsupport
          (((positiveTimeCompactSupportConvolution ψn h : positiveTimeCompactSupportSubmodule d) :
              SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) ⊆
        tsupport (((ψn : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) +
          tsupport (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) := by
    refine closure_minimal ?_ hsum_closed
    exact
      (support_convolution_subset (L := ContinuousLinearMap.lsmul ℝ ℂ)).trans
        (Set.add_subset_add subset_closure subset_closure)
  rcases htsupp_subset hx with ⟨u, hu, v, hv, rfl⟩
  have hu_norm_lt : ‖u‖ < 1 / (n + 1 : ℝ) := by
    simpa [Metric.mem_ball, dist_eq_norm] using hψ_ball hu
  have hu_norm_le_one : ‖u‖ ≤ 1 := by
    have hsmall : (1 / (n + 1 : ℝ)) ≤ 1 := by
      have hden_nat : (1 : ℕ) ≤ n + 1 := by exact Nat.succ_le_succ (Nat.zero_le n)
      have hden : (1 : ℝ) ≤ n + 1 := by exact_mod_cast hden_nat
      have hpos1 : (0 : ℝ) < 1 := by norm_num
      simpa [one_div] using (one_div_le_one_div_of_le hpos1 hden)
    exact le_trans hu_norm_lt.le hsmall
  have hv_ball : v ∈ Metric.closedBall (0 : SpacetimeDim d) Rh := hRh hv
  have hv_norm : ‖v‖ ≤ Rh := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hv_ball
  have hv_abs : ‖v‖ ≤ |Rh| := by
    exact le_trans hv_norm (le_abs_self _)
  have hx_norm : ‖u + v‖ ≤ |Rh| + 1 := by
    calc
      ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le _ _
      _ ≤ 1 + |Rh| := add_le_add hu_norm_le_one hv_abs
      _ = |Rh| + 1 := by ring
  simpa [Metric.mem_closedBall, dist_eq_norm, add_comm, add_left_comm, add_assoc] using hx_norm

/-- The reflected approximate-identity probes have a uniform weighted `L¹`
moment bound on the unit ball. This is the scalar side of the VI.1 smoothing
estimate: once the probe is reflected, the shrinking-support hypothesis forces
all polynomial weights of fixed order to stay uniformly bounded. -/
theorem reflected_negativeApproxIdentity_weighted_L1_moment_le_two_pow_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (k : ℕ) :
    ∀ n,
      ∫ ξ : SpacetimeDim d,
        ‖reflectedSchwartzSpacetime (φ_seq n) ξ‖ * (1 + ‖ξ‖) ^ k ≤ 2 ^ k := by
  intro n
  have hL1 :
      ∫ ξ : SpacetimeDim d, ‖reflectedSchwartzSpacetime (φ_seq n) ξ‖ = 1 :=
    reflected_approxIdentity_L1_norm_eq_one_vi1Bounds_local
      (d := d) (φ_seq n) (hφ_nonneg n) (hφ_real n) (hφ_int n)
  have hreflect_ball :
      tsupport (reflectedSchwartzSpacetime (φ_seq n) : SpacetimeDim d → ℂ) ⊆
        Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)) :=
    reflectedSchwartzSpacetime_tsupport_ball (d := d) (φ_seq n) (hφ_ball n)
  have hbound :
      ∀ ξ : SpacetimeDim d,
        ‖reflectedSchwartzSpacetime (φ_seq n) ξ‖ * (1 + ‖ξ‖) ^ k ≤
          (2 : ℝ) ^ k * ‖reflectedSchwartzSpacetime (φ_seq n) ξ‖ := by
    intro ξ
    by_cases hξ :
        ξ ∈ tsupport (reflectedSchwartzSpacetime (φ_seq n) : SpacetimeDim d → ℂ)
    · have hξ_ball : ξ ∈ Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)) :=
        hreflect_ball hξ
      have hξ_norm_lt : ‖ξ‖ < 1 / (n + 1 : ℝ) := by
        simpa [Metric.mem_ball, dist_eq_norm] using hξ_ball
      have hξ_norm_le_one : ‖ξ‖ ≤ 1 := by
        have hsmall : (1 / (n + 1 : ℝ)) ≤ 1 := by
          have hden_nat : (1 : ℕ) ≤ n + 1 := by exact Nat.succ_le_succ (Nat.zero_le n)
          have hden : (1 : ℝ) ≤ n + 1 := by exact_mod_cast hden_nat
          have hpos1 : (0 : ℝ) < 1 := by norm_num
          simpa [one_div] using (one_div_le_one_div_of_le hpos1 hden)
        exact le_trans hξ_norm_lt.le hsmall
      have hpow : (1 + ‖ξ‖) ^ k ≤ (2 : ℝ) ^ k := by
        apply pow_le_pow_left₀
        · positivity
        · linarith
      calc
        ‖reflectedSchwartzSpacetime (φ_seq n) ξ‖ * (1 + ‖ξ‖) ^ k
            ≤ ‖reflectedSchwartzSpacetime (φ_seq n) ξ‖ * (2 : ℝ) ^ k := by
              exact mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
        _ = (2 : ℝ) ^ k * ‖reflectedSchwartzSpacetime (φ_seq n) ξ‖ := by ring
    · have hzero : reflectedSchwartzSpacetime (φ_seq n) ξ = 0 :=
        image_eq_zero_of_notMem_tsupport hξ
      simp [hzero]
  let lower : SpacetimeDim d → ℝ :=
    fun ξ => ‖reflectedSchwartzSpacetime (φ_seq n) ξ‖ * (1 + ‖ξ‖) ^ k
  let upper : SpacetimeDim d → ℝ :=
    fun ξ => (2 : ℝ) ^ k * ‖reflectedSchwartzSpacetime (φ_seq n) ξ‖
  have hIntUpper : Integrable upper := by
    simpa [upper] using
      (((SchwartzMap.integrable (reflectedSchwartzSpacetime (φ_seq n))).norm).const_mul
        ((2 : ℝ) ^ k))
  have hIntLower : Integrable lower := by
    have hbound_norm : ∀ ξ : SpacetimeDim d, ‖lower ξ‖ ≤ upper ξ := by
      intro ξ
      have hweight_nonneg : 0 ≤ (1 + ‖ξ‖ : ℝ) := by positivity
      have hlower_nonneg : 0 ≤ lower ξ := by
        exact mul_nonneg (norm_nonneg _) (pow_nonneg hweight_nonneg _)
      simpa [Real.norm_eq_abs, abs_of_nonneg hlower_nonneg, abs_of_nonneg hweight_nonneg,
        lower, upper] using hbound ξ
    refine MeasureTheory.Integrable.mono' hIntUpper ?_ ?_
    · exact
        ((((reflectedSchwartzSpacetime (φ_seq n)).continuous.norm).mul
          ((continuous_const.add continuous_norm).pow k)).aestronglyMeasurable)
    · exact Filter.Eventually.of_forall hbound_norm
  calc
    ∫ ξ : SpacetimeDim d, lower ξ ≤ ∫ ξ : SpacetimeDim d, upper ξ := by
          exact MeasureTheory.integral_mono_ae hIntLower hIntUpper (Filter.Eventually.of_forall hbound)
    _ = (2 : ℝ) ^ k * ∫ ξ : SpacetimeDim d, ‖reflectedSchwartzSpacetime (φ_seq n) ξ‖ := by
          rw [show (∫ ξ : SpacetimeDim d, upper ξ) =
              (2 : ℝ) ^ k * ∫ ξ : SpacetimeDim d, ‖reflectedSchwartzSpacetime (φ_seq n) ξ‖ by
                simp [upper, MeasureTheory.integral_const_mul]]
    _ = (2 : ℝ) ^ k := by
          rw [hL1]
          ring

/-- A directional derivative of a positive-time compact-support test remains in
the same reduced domain. This is the minimal closure property needed to lift the
zeroth-seminorm regularization bound to higher derivative order without
reopening the large frozen support file. -/
private def positiveTimeCompactSupportLineDeriv_local
    (h : positiveTimeCompactSupportSubmodule d)
    (v : SpacetimeDim d) :
    positiveTimeCompactSupportSubmodule d := by
  refine ⟨LineDeriv.lineDerivOp v (h : SchwartzSpacetime d), ?_⟩
  constructor
  · intro x hx
    exact h.property.1
      ((SchwartzMap.tsupport_lineDerivOp_subset (m := v) (f := (h : SchwartzSpacetime d))) hx)
  · exact h.property.2.of_isClosed_subset (isClosed_tsupport _)
      (SchwartzMap.tsupport_lineDerivOp_subset (m := v) (f := (h : SchwartzSpacetime d)))

@[simp] private theorem positiveTimeCompactSupportLineDeriv_local_coe
    (h : positiveTimeCompactSupportSubmodule d)
    (v : SpacetimeDim d) :
    ((positiveTimeCompactSupportLineDeriv_local (d := d) h v :
        positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) =
      LineDeriv.lineDerivOp v (h : SchwartzSpacetime d) := by
  rfl


/-- The reflected positive-time convolution sequence is uniformly bounded in
sup norm by the zeroth Schwartz seminorm of the fixed target test. This is the
`L¹ * L∞` part of the VI.1 regularization estimate on the actual OS-side
sequence, not an auxiliary model kernel. -/
theorem positiveTimeCompactSupportConvolution_reflected_negativeApproxIdentity_norm_le_seminorm_zero_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (h : positiveTimeCompactSupportSubmodule d) :
    ∀ n x,
      ‖(((positiveTimeCompactSupportConvolution
          (⟨reflectedSchwartzSpacetime (φ_seq n),
            ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
              reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
                (hφ_compact n)⟩⟩)
          h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) x)‖ ≤
        SchwartzMap.seminorm ℝ 0 0 (h : SchwartzSpacetime d) := by
  intro n x
  let ψn : positiveTimeCompactSupportSubmodule d :=
    ⟨reflectedSchwartzSpacetime (φ_seq n),
      ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
        reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
          (hφ_compact n)⟩⟩
  let C0 : ℝ := SchwartzMap.seminorm ℝ 0 0 (h : SchwartzSpacetime d)
  have hC0_nonneg : 0 ≤ C0 := by
    exact apply_nonneg (SchwartzMap.seminorm ℝ 0 0) _
  have hψ_L1 :
      ∫ ξ : SpacetimeDim d, ‖((ψn : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ‖ = 1 := by
    simpa [ψn] using
      reflected_approxIdentity_L1_norm_eq_one_vi1Bounds_local
        (d := d) (φ_seq n) (hφ_nonneg n) (hφ_real n) (hφ_int n)
  have htranslate_bound :
      ∀ ξ : SpacetimeDim d,
        ‖(SCV.translateSchwartz (-ξ) (h : SchwartzSpacetime d)) x‖ ≤ C0 := by
    intro ξ
    simpa [C0, SCV.translateSchwartz_apply, sub_eq_add_neg] using
      (SchwartzMap.norm_pow_mul_le_seminorm ℝ (h : SchwartzSpacetime d) 0 (x - ξ))
  have hIntUpper :
      Integrable (fun ξ : SpacetimeDim d =>
        ‖((ψn : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ‖ * C0) := by
    simpa [C0, mul_comm] using
      ((((SchwartzMap.integrable
          (μ := (volume : Measure (SpacetimeDim d)))
          ((ψn : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d)).norm).const_mul C0))
  have hIntLower :
      Integrable (fun ξ : SpacetimeDim d =>
        ‖((ψn : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ *
          (SCV.translateSchwartz (-ξ) (h : SchwartzSpacetime d)) x‖) := by
    refine MeasureTheory.Integrable.mono' hIntUpper ?_ ?_
    · exact
        ((((ψn : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d).continuous.mul
          ((h : SchwartzSpacetime d).continuous.comp (continuous_const.sub continuous_id'))).norm).aestronglyMeasurable
    · refine Filter.Eventually.of_forall ?_
      intro ξ
      have hmain :
          ‖((ψn : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ *
              (SCV.translateSchwartz (-ξ) (h : SchwartzSpacetime d)) x‖
              ≤ ‖((ψn : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ‖ * C0 := by
        calc
          ‖((ψn : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ *
              (SCV.translateSchwartz (-ξ) (h : SchwartzSpacetime d)) x‖
              = ‖((ψn : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ‖ *
                  ‖(SCV.translateSchwartz (-ξ) (h : SchwartzSpacetime d)) x‖ := by
                    rw [norm_mul]
          _ ≤ ‖((ψn : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ‖ * C0 := by
                exact mul_le_mul_of_nonneg_left (htranslate_bound ξ) (norm_nonneg _)
      simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hmain
  rw [positiveTimeCompactSupportConvolution_apply_eq_integral_translate (h := ψn) (g := h) x]
  calc
    ‖∫ ξ : SpacetimeDim d,
        ((ψn : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ *
          (SCV.translateSchwartz (-ξ) (h : SchwartzSpacetime d)) x‖
        ≤ ∫ ξ : SpacetimeDim d,
            ‖((ψn : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ *
              (SCV.translateSchwartz (-ξ) (h : SchwartzSpacetime d)) x‖ := by
              exact MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ ξ : SpacetimeDim d,
          ‖((ψn : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ‖ * C0 := by
            exact
              MeasureTheory.integral_mono_ae hIntLower hIntUpper
                (Filter.Eventually.of_forall fun ξ => by
                  calc
                    ‖((ψn : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ *
                        (SCV.translateSchwartz (-ξ) (h : SchwartzSpacetime d)) x‖
                        = ‖((ψn : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ‖ *
                            ‖(SCV.translateSchwartz (-ξ) (h : SchwartzSpacetime d)) x‖ := by
                              rw [norm_mul]
                    _ ≤ ‖((ψn : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) ξ‖ * C0 := by
                          exact mul_le_mul_of_nonneg_left (htranslate_bound ξ) (norm_nonneg _))
    _ = C0 := by
          rw [MeasureTheory.integral_mul_const]
          rw [hψ_L1]
          ring

/-- The reflected positive-time convolution sequence has a uniform weighted
zeroth Schwartz seminorm bound. This is the first direct OS-side seminorm
estimate needed for the VI.1 regularization step. -/
theorem positiveTimeCompactSupportConvolution_reflected_negativeApproxIdentity_seminorm_zero_uniform_local
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
      SchwartzMap.seminorm ℝ N 0
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
  let C0 : ℝ := SchwartzMap.seminorm ℝ 0 0 (h : SchwartzSpacetime d)
  let C : ℝ := R ^ N * C0
  refine ⟨C, by
    dsimp [C, C0]
    exact mul_nonneg (pow_nonneg (le_of_lt hR_pos) _) (apply_nonneg (SchwartzMap.seminorm ℝ 0 0) _), ?_⟩
  intro n
  let ψn : positiveTimeCompactSupportSubmodule d :=
    ⟨reflectedSchwartzSpacetime (φ_seq n),
      ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
        reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
          (hφ_compact n)⟩⟩
  let convn : SchwartzSpacetime d := (((positiveTimeCompactSupportConvolution ψn h :
    positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d))
  refine SchwartzMap.seminorm_le_bound ℝ N 0 convn
    (by
      dsimp [C, C0]
      exact mul_nonneg (pow_nonneg (le_of_lt hR_pos) _) (apply_nonneg (SchwartzMap.seminorm ℝ 0 0) _)) ?_
  intro x
  rw [norm_iteratedFDeriv_zero]
  by_cases hx :
      x ∈ tsupport ((convn : SchwartzSpacetime d) : SpacetimeDim d → ℂ)
  · have hx_ball : x ∈ Metric.closedBall (0 : SpacetimeDim d) R := by
      simpa [convn, ψn] using hR n hx
    have hx_norm : ‖x‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx_ball
    have hnorm :
        ‖(convn : SchwartzSpacetime d) x‖ ≤ C0 := by
      simpa [convn, ψn, C0] using
        positiveTimeCompactSupportConvolution_reflected_negativeApproxIdentity_norm_le_seminorm_zero_local
          (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg h n x
    calc
      ‖x‖ ^ N * ‖(convn : SchwartzSpacetime d) x‖ ≤ R ^ N * ‖(convn : SchwartzSpacetime d) x‖ := by
            gcongr
      _ ≤ R ^ N * C0 := by
            exact mul_le_mul_of_nonneg_left hnorm (pow_nonneg (le_of_lt hR_pos) _)
      _ = C := by rfl
  · have hzero : (convn : SchwartzSpacetime d) x = 0 := image_eq_zero_of_notMem_tsupport hx
    have hC_nonneg : 0 ≤ C := by
      dsimp [C, C0]
      exact mul_nonneg (pow_nonneg (le_of_lt hR_pos) _) (apply_nonneg (SchwartzMap.seminorm ℝ 0 0) _)
    simp [convn, hzero, C, hC_nonneg]
