import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.RegularizationDeriv

noncomputable section

open MeasureTheory
open scoped LineDeriv

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- A directional derivative of a positive-time compact-support test stays in the
same reduced domain. We keep a local copy here so the iterated regularization
layer can live in its own small file. -/
private def positiveTimeCompactSupportLineDeriv_vi1Iter_local
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

omit [NeZero d] in
@[simp] private theorem positiveTimeCompactSupportLineDeriv_vi1Iter_local_coe
    (h : positiveTimeCompactSupportSubmodule d)
    (v : SpacetimeDim d) :
    ((positiveTimeCompactSupportLineDeriv_vi1Iter_local (d := d) h v :
        positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) =
      LineDeriv.lineDerivOp v (h : SchwartzSpacetime d) := by
  rfl

/-- Iterated closure of the positive-time compact-support test space under
directional derivatives. -/
private def positiveTimeCompactSupportIteratedLineDeriv_local
    (h : positiveTimeCompactSupportSubmodule d) :
    {j : ℕ} → (Fin j → SpacetimeDim d) → positiveTimeCompactSupportSubmodule d
  | 0, _ => h
  | j + 1, u =>
      positiveTimeCompactSupportLineDeriv_vi1Iter_local
        (d := d)
        (positiveTimeCompactSupportIteratedLineDeriv_local h (Fin.tail u))
        (u 0)
termination_by j => j

omit [NeZero d] in
@[simp] private theorem positiveTimeCompactSupportIteratedLineDeriv_local_coe
    (h : positiveTimeCompactSupportSubmodule d)
    {j : ℕ} (u : Fin j → SpacetimeDim d) :
    ((positiveTimeCompactSupportIteratedLineDeriv_local (d := d) h u :
        positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) =
      LineDeriv.iteratedLineDerivOp u (h : SchwartzSpacetime d) := by
  induction j generalizing h with
  | zero =>
      ext x
      simp [positiveTimeCompactSupportIteratedLineDeriv_local,
        LineDeriv.iteratedLineDerivOp_fin_zero]
  | succ j ih =>
      simp [positiveTimeCompactSupportIteratedLineDeriv_local, ih,
        LineDeriv.iteratedLineDerivOp_succ_left]

omit [NeZero d] in
/-- A single directional derivative costs one derivative-order Schwartz seminorm
and one factor of the direction norm. -/
private theorem seminorm_zero_lineDeriv_le_vi1Iter_local
    (h : SchwartzSpacetime d) (v : SpacetimeDim d) (n : ℕ) :
    SchwartzMap.seminorm ℝ 0 n (LineDeriv.lineDerivOp v h : SchwartzSpacetime d) ≤
      ‖v‖ * SchwartzMap.seminorm ℝ 0 (n + 1) h := by
  refine SchwartzMap.seminorm_le_bound ℝ 0 n
    (LineDeriv.lineDerivOp v h : SchwartzSpacetime d) (by positivity) ?_
  intro x
  calc
    ‖x‖ ^ 0 *
        ‖iteratedFDeriv ℝ n
            (((LineDeriv.lineDerivOp v h : SchwartzSpacetime d) : SchwartzSpacetime d) :
              SpacetimeDim d → ℂ) x‖
        =
      ‖iteratedFDeriv ℝ n
          (((LineDeriv.lineDerivOp v h : SchwartzSpacetime d) : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) x‖ := by
            simp
    _ = ‖fderiv ℝ (iteratedFDeriv ℝ n (h : SpacetimeDim d → ℂ)) x v‖ := by
          rw [fderiv_iteratedFDeriv_eq_iteratedFDeriv_lineDeriv]
    _ ≤ ‖fderiv ℝ (iteratedFDeriv ℝ n (h : SpacetimeDim d → ℂ)) x‖ * ‖v‖ := by
          exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ (n + 1) (h : SpacetimeDim d → ℂ) x‖ * ‖v‖ := by
          rw [norm_fderiv_iteratedFDeriv]
    _ ≤ (SchwartzMap.seminorm ℝ 0 (n + 1) h) * ‖v‖ := by
          gcongr
          exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ h (n + 1) x
    _ = ‖v‖ * SchwartzMap.seminorm ℝ 0 (n + 1) h := by
          ring_nf

omit [NeZero d] in
/-- Iterated directional derivatives are uniformly controlled by the matching
zero-weight higher Schwartz seminorm, with one factor of `‖u i‖` per direction. -/
private theorem iteratedLineDeriv_seminorm_zero_le_vi1Iter_local
    (h : SchwartzSpacetime d) (j n : ℕ) :
    ∀ u : Fin j → SpacetimeDim d,
      SchwartzMap.seminorm ℝ 0 n (LineDeriv.iteratedLineDerivOp u h : SchwartzSpacetime d) ≤
        (∏ i, ‖u i‖) * SchwartzMap.seminorm ℝ 0 (n + j) h := by
  induction j generalizing h n with
  | zero =>
      intro u
      simp [LineDeriv.iteratedLineDerivOp_fin_zero]
  | succ j ih =>
      intro u
      rw [LineDeriv.iteratedLineDerivOp_succ_left]
      calc
        SchwartzMap.seminorm ℝ 0 n (∂_{u 0} (∂^{Fin.tail u} h) : SchwartzSpacetime d)
            ≤ ‖u 0‖ * SchwartzMap.seminorm ℝ 0 (n + 1) (∂^{Fin.tail u} h : SchwartzSpacetime d) := by
              exact seminorm_zero_lineDeriv_le_vi1Iter_local
                (h := ∂^{Fin.tail u} h) (v := u 0) (n := n)
        _ ≤ ‖u 0‖ *
              ((∏ i, ‖Fin.tail u i‖) * SchwartzMap.seminorm ℝ 0 (n + 1 + j) h) := by
              gcongr
              exact ih (h := h) (n := n + 1) (u := Fin.tail u)
        _ = (∏ i, ‖u i‖) * SchwartzMap.seminorm ℝ 0 (n + (j + 1)) h := by
              rw [Fin.prod_univ_succ, add_assoc]
              have htail : (∏ i : Fin j, ‖Fin.tail u i‖) = ∏ i : Fin j, ‖u i.succ‖ := rfl
              rw [htail]
              ring_nf

omit [NeZero d] in
private theorem lineDeriv_convolution_eq_convolution_lineDeriv_vi1Iter_local
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

omit [NeZero d] in
private theorem tsupport_iteratedLineDerivOp_subset_vi1Iter_local
    (f : SchwartzSpacetime d) {j : ℕ} (u : Fin j → SpacetimeDim d) :
    tsupport (LineDeriv.iteratedLineDerivOp u f : SpacetimeDim d → ℂ) ⊆
      tsupport (f : SpacetimeDim d → ℂ) := by
  induction j generalizing f with
  | zero =>
      simp [LineDeriv.iteratedLineDerivOp_fin_zero]
  | succ j ih =>
      rw [LineDeriv.iteratedLineDerivOp_succ_left]
      exact
        (SchwartzMap.tsupport_lineDerivOp_subset (m := u 0)
          (f := (LineDeriv.iteratedLineDerivOp (Fin.tail u) f : SchwartzSpacetime d))).trans
          (ih (f := f) (u := Fin.tail u))

omit [NeZero d] in
private theorem positiveTimeCompactSupportConvolution_iteratedLineDeriv_eq_vi1Iter_local
    (ψ : positiveTimeCompactSupportSubmodule d)
    (h : positiveTimeCompactSupportSubmodule d)
    {j : ℕ} (u : Fin j → SpacetimeDim d) :
    (LineDeriv.iteratedLineDerivOp u
      ((((positiveTimeCompactSupportConvolution ψ h :
          positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d))) : SchwartzSpacetime d) =
    (((positiveTimeCompactSupportConvolution ψ
        (positiveTimeCompactSupportIteratedLineDeriv_local (d := d) h u) :
          positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d)) := by
  induction j generalizing h with
  | zero =>
      ext x
      simp [LineDeriv.iteratedLineDerivOp_fin_zero,
        positiveTimeCompactSupportIteratedLineDeriv_local]
  | succ j ih =>
      let htail : positiveTimeCompactSupportSubmodule d :=
        positiveTimeCompactSupportIteratedLineDeriv_local (d := d) h (Fin.tail u)
      have htail_eq :
          (LineDeriv.iteratedLineDerivOp (Fin.tail u)
            ((((positiveTimeCompactSupportConvolution ψ h :
                positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d))) :
              SchwartzSpacetime d) =
          (((positiveTimeCompactSupportConvolution ψ htail :
              positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d)) := by
        simpa [htail] using ih (h := h) (u := Fin.tail u)
      ext x
      rw [LineDeriv.iteratedLineDerivOp_succ_left, SchwartzMap.lineDerivOp_apply]
      have hstep :
          lineDeriv ℝ
            (fun y : SpacetimeDim d =>
              ((LineDeriv.iteratedLineDerivOp (Fin.tail u)
                ((((positiveTimeCompactSupportConvolution ψ h :
                    positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d))) :
                  SchwartzSpacetime d) y))
            x (u 0)
          =
            lineDeriv ℝ
              (fun y : SpacetimeDim d =>
                (((positiveTimeCompactSupportConvolution ψ htail :
                    positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) y))
              x (u 0) := by
                simpa using congrArg
                  (fun F : SchwartzSpacetime d => lineDeriv ℝ (fun y => F y) x (u 0))
                  htail_eq
      rw [hstep]
      simpa [positiveTimeCompactSupportConvolution_apply, MeasureTheory.convolution,
        htail, positiveTimeCompactSupportIteratedLineDeriv_local_coe,
        LineDeriv.iteratedLineDerivOp_succ_left] using
        lineDeriv_convolution_eq_convolution_lineDeriv_vi1Iter_local
          (((ψ : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d))
          ((htail : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d)
          (htail.property.2)
          x (u 0)

/-- Uniform weighted zeroth-seminorm control for every iterated directional
derivative of the reflected positive-time convolution sequence. -/
theorem positiveTimeCompactSupportConvolution_reflected_negativeApproxIdentity_iteratedLineDeriv_seminorm_zero_uniform_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (N j : ℕ)
    (h : positiveTimeCompactSupportSubmodule d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Fin j → SpacetimeDim d) n,
      let ψn : positiveTimeCompactSupportSubmodule d :=
        ⟨reflectedSchwartzSpacetime (φ_seq n),
          ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
            reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
              (hφ_compact n)⟩⟩
      let convn : SchwartzSpacetime d :=
        (((positiveTimeCompactSupportConvolution ψn h : positiveTimeCompactSupportSubmodule d) :
          SchwartzSpacetime d))
      SchwartzMap.seminorm ℝ N 0 (LineDeriv.iteratedLineDerivOp u convn : SchwartzSpacetime d) ≤
        C * (∏ i, ‖u i‖) := by
  rcases
      exists_uniform_closedBall_support_reflected_negativeApproxIdentity_convolution_local
        (d := d) φ_seq hφ_compact hφ_neg hφ_ball h with
    ⟨R, hR_pos, hR⟩
  let C0 : ℝ := SchwartzMap.seminorm ℝ 0 j (h : SchwartzSpacetime d)
  let C : ℝ := R ^ N * C0
  refine ⟨C, by
    dsimp [C, C0]
    exact mul_nonneg (pow_nonneg (le_of_lt hR_pos) _) (apply_nonneg (SchwartzMap.seminorm ℝ 0 j) _), ?_⟩
  intro u n
  dsimp
  let hu : positiveTimeCompactSupportSubmodule d :=
    positiveTimeCompactSupportIteratedLineDeriv_local (d := d) h u
  let ψn : positiveTimeCompactSupportSubmodule d :=
    ⟨reflectedSchwartzSpacetime (φ_seq n),
      ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
        reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
          (hφ_compact n)⟩⟩
  let convOrig : SchwartzSpacetime d :=
    (((positiveTimeCompactSupportConvolution ψn h : positiveTimeCompactSupportSubmodule d) :
      SchwartzSpacetime d))
  let convDeriv : SchwartzSpacetime d :=
    (((positiveTimeCompactSupportConvolution ψn hu : positiveTimeCompactSupportSubmodule d) :
      SchwartzSpacetime d))
  have hconv_eq :
      (LineDeriv.iteratedLineDerivOp u
        convOrig : SchwartzSpacetime d) =
      convDeriv := by
    simpa [convOrig, convDeriv, hu] using
      positiveTimeCompactSupportConvolution_iteratedLineDeriv_eq_vi1Iter_local
        (d := d) ψn h u
  have hbase :
      SchwartzMap.seminorm ℝ N 0 convDeriv ≤ R ^ N * SchwartzMap.seminorm ℝ 0 0 (hu : SchwartzSpacetime d) := by
    refine SchwartzMap.seminorm_le_bound ℝ N 0 convDeriv
      (by
        exact mul_nonneg (pow_nonneg (le_of_lt hR_pos) _)
          (apply_nonneg (SchwartzMap.seminorm ℝ 0 0) _)) ?_
    intro x
    rw [norm_iteratedFDeriv_zero]
    by_cases hx :
        x ∈ tsupport ((convDeriv : SchwartzSpacetime d) : SpacetimeDim d → ℂ)
    · have hx_ball : x ∈ Metric.closedBall (0 : SpacetimeDim d) R := by
        have htsub :
            tsupport ((convDeriv : SchwartzSpacetime d) : SpacetimeDim d → ℂ) ⊆
              tsupport ((convOrig : SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
          intro y hy
          have hy' :
              y ∈ tsupport
                ((LineDeriv.iteratedLineDerivOp u (convOrig : SchwartzSpacetime d) :
                    SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
            simpa [hconv_eq, convDeriv] using hy
          exact tsupport_iteratedLineDerivOp_subset_vi1Iter_local
            (convOrig : SchwartzSpacetime d) u hy'
        have hx' :
            x ∈ tsupport ((convOrig : SchwartzSpacetime d) : SpacetimeDim d → ℂ) := htsub hx
        simpa [ψn, convOrig] using hR n hx'
      have hx_norm : ‖x‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hx_ball
      have hnorm :
          ‖(convDeriv : SchwartzSpacetime d) x‖ ≤ SchwartzMap.seminorm ℝ 0 0 (hu : SchwartzSpacetime d) := by
        simpa [convDeriv, ψn, hu] using
          positiveTimeCompactSupportConvolution_reflected_negativeApproxIdentity_norm_le_seminorm_zero_local
            (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg hu n x
      calc
        ‖x‖ ^ N * ‖(convDeriv : SchwartzSpacetime d) x‖ ≤ R ^ N * ‖(convDeriv : SchwartzSpacetime d) x‖ := by
              gcongr
        _ ≤ R ^ N * SchwartzMap.seminorm ℝ 0 0 (hu : SchwartzSpacetime d) := by
              exact mul_le_mul_of_nonneg_left hnorm (pow_nonneg (le_of_lt hR_pos) _)
    · have hzero : (convDeriv : SchwartzSpacetime d) x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hC_nonneg : 0 ≤ R ^ N * SchwartzMap.seminorm ℝ 0 0 (hu : SchwartzSpacetime d) := by
        exact mul_nonneg (pow_nonneg (le_of_lt hR_pos) _)
          (apply_nonneg (SchwartzMap.seminorm ℝ 0 0) _)
      simp [hzero, hC_nonneg]
  have hu_bound :
      SchwartzMap.seminorm ℝ 0 0 (hu : SchwartzSpacetime d) ≤
        (∏ i, ‖u i‖) * SchwartzMap.seminorm ℝ 0 j (h : SchwartzSpacetime d) := by
    simpa [hu, positiveTimeCompactSupportIteratedLineDeriv_local_coe] using
      iteratedLineDeriv_seminorm_zero_le_vi1Iter_local
        (h := (h : SchwartzSpacetime d)) (j := j) (n := 0) u
  rw [hconv_eq]
  calc
    SchwartzMap.seminorm ℝ N 0 convDeriv
        ≤ R ^ N * ((∏ i, ‖u i‖) * SchwartzMap.seminorm ℝ 0 j (h : SchwartzSpacetime d)) := by
          exact le_trans hbase (by
            gcongr)
    _ = (R ^ N * SchwartzMap.seminorm ℝ 0 j (h : SchwartzSpacetime d)) * (∏ i, ‖u i‖) := by
          ring_nf
    _ = C * (∏ i, ‖u i‖) := by
          rfl

end OSReconstruction
