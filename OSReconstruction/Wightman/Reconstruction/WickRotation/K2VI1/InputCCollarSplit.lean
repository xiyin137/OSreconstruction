import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputCReduced
import OSReconstruction.SCV.FourierLaplaceCore

noncomputable section

open Complex MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

private def posTimeCollarCutoff_local (a : ℝ) : SpacetimeDim d → ℂ :=
  fun ξ => (SCV.smoothCutoff (((2 / a) * ξ 0) - 2) : ℂ)

private def negTimeCollarCutoff_local (a : ℝ) : SpacetimeDim d → ℂ :=
  fun ξ => (SCV.smoothCutoff (((-2 / a) * ξ 0) - 2) : ℂ)

private def centerCollarCutoff_local (a : ℝ) : SpacetimeDim d → ℂ :=
  fun ξ => 1 - posTimeCollarCutoff_local (d := d) a ξ -
    negTimeCollarCutoff_local (d := d) a ξ

private theorem posTimeCollarCutoff_hasTemperateGrowth_local (a : ℝ) :
    (posTimeCollarCutoff_local (d := d) a).HasTemperateGrowth := by
  let g : ℝ → ℂ := fun t => (SCV.smoothCutoff t : ℂ)
  have hg : g.HasTemperateGrowth := by
    simpa [g] using SCV.smoothCutoff_complex_hasTemperateGrowth
  have hcoord : (fun ξ : SpacetimeDim d => ξ 0).HasTemperateGrowth := by
    simpa using
      (ContinuousLinearMap.proj (R := ℝ) (ι := Fin (d + 1)) (φ := fun _ => ℝ) 0).hasTemperateGrowth
  have hf : (fun ξ : SpacetimeDim d => ((2 / a) * ξ 0) + (-2)).HasTemperateGrowth := by
    simpa [add_comm, add_left_comm, add_assoc] using
      ((Function.HasTemperateGrowth.const (2 / a)).mul hcoord).add
        (Function.HasTemperateGrowth.const (-2 : ℝ))
  simpa [g, posTimeCollarCutoff_local] using hg.comp hf

private theorem negTimeCollarCutoff_hasTemperateGrowth_local (a : ℝ) :
    (negTimeCollarCutoff_local (d := d) a).HasTemperateGrowth := by
  let g : ℝ → ℂ := fun t => (SCV.smoothCutoff t : ℂ)
  have hg : g.HasTemperateGrowth := by
    simpa [g] using SCV.smoothCutoff_complex_hasTemperateGrowth
  have hcoord : (fun ξ : SpacetimeDim d => ξ 0).HasTemperateGrowth := by
    simpa using
      (ContinuousLinearMap.proj (R := ℝ) (ι := Fin (d + 1)) (φ := fun _ => ℝ) 0).hasTemperateGrowth
  have hf : (fun ξ : SpacetimeDim d => ((-2 / a) * ξ 0) + (-2)).HasTemperateGrowth := by
    simpa [add_comm, add_left_comm, add_assoc] using
      ((Function.HasTemperateGrowth.const (-2 / a)).mul hcoord).add
        (Function.HasTemperateGrowth.const (-2 : ℝ))
  simpa [g, negTimeCollarCutoff_local] using hg.comp hf

private theorem centerCollarCutoff_hasTemperateGrowth_local (a : ℝ) :
    (centerCollarCutoff_local (d := d) a).HasTemperateGrowth := by
  simpa [centerCollarCutoff_local] using
    ((Function.HasTemperateGrowth.const (1 : ℂ)).sub
      (posTimeCollarCutoff_hasTemperateGrowth_local (d := d) a)).sub
      (negTimeCollarCutoff_hasTemperateGrowth_local (d := d) a)

private theorem posTimeCollarCutoff_zero_of_le_half_local
    {a : ℝ} (ha : 0 < a) {ξ : SpacetimeDim d} (hξ : ξ 0 ≤ a / 2) :
    posTimeCollarCutoff_local (d := d) a ξ = 0 := by
  rw [posTimeCollarCutoff_local]
  have harg : ((2 / a) * ξ 0 - 2) ≤ -1 := by
    have hmul : (2 / a) * ξ 0 ≤ (2 / a) * (a / 2) := by
      gcongr
    have htwo : (2 / a) * (a / 2) = 1 := by
      field_simp [ha.ne']
    nlinarith [hmul, htwo]
  exact_mod_cast SCV.smoothCutoff_zero_of_le_neg_one harg

private theorem posTimeCollarCutoff_one_of_ge_local
    {a : ℝ} (ha : 0 < a) {ξ : SpacetimeDim d} (hξ : a ≤ ξ 0) :
    posTimeCollarCutoff_local (d := d) a ξ = 1 := by
  rw [posTimeCollarCutoff_local]
  have harg : 0 ≤ ((2 / a) * ξ 0 - 2) := by
    have hmul : (2 / a) * a ≤ (2 / a) * ξ 0 := by
      gcongr
    have htwo : (2 / a) * a = 2 := by
      field_simp [ha.ne']
    nlinarith [hmul, htwo]
  exact_mod_cast SCV.smoothCutoff_one_of_nonneg harg

private theorem negTimeCollarCutoff_zero_of_neg_half_le_local
    {a : ℝ} (ha : 0 < a) {ξ : SpacetimeDim d} (hξ : -a / 2 ≤ ξ 0) :
    negTimeCollarCutoff_local (d := d) a ξ = 0 := by
  rw [negTimeCollarCutoff_local]
  have harg : (((-2 / a) * ξ 0) - 2) ≤ -1 := by
    have hmul : (-2 / a) * ξ 0 ≤ 1 := by
      have haux : -2 * ξ 0 ≤ a := by
        nlinarith
      have hdiv : (-2 * ξ 0) / a ≤ 1 := by
        field_simp [ha.ne']
        linarith
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
    nlinarith [hmul]
  exact_mod_cast SCV.smoothCutoff_zero_of_le_neg_one harg

private theorem negTimeCollarCutoff_one_of_le_neg_local
    {a : ℝ} (ha : 0 < a) {ξ : SpacetimeDim d} (hξ : ξ 0 ≤ -a) :
    negTimeCollarCutoff_local (d := d) a ξ = 1 := by
  rw [negTimeCollarCutoff_local]
  have harg : 0 ≤ (((-2 / a) * ξ 0) - 2) := by
    have hmul : 2 ≤ (-2 / a) * ξ 0 := by
      have haux : 2 * a ≤ -2 * ξ 0 := by
        nlinarith
      have hdiv : 2 ≤ (-2 * ξ 0) / a := by
        field_simp [ha.ne']
        linarith
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
    nlinarith [hmul]
  exact_mod_cast SCV.smoothCutoff_one_of_nonneg harg

private theorem support_posTimeCollarCutoff_subset_local
    {a : ℝ} (ha : 0 < a) :
    Function.support (posTimeCollarCutoff_local (d := d) a) ⊆
      {ξ : SpacetimeDim d | a / 2 < ξ 0} := by
  intro ξ hξ
  by_contra hnot
  simp only [Set.mem_setOf_eq, not_lt] at hnot
  exact hξ (by simpa [Function.mem_support] using
    posTimeCollarCutoff_zero_of_le_half_local (d := d) ha hnot)

private theorem support_negTimeCollarCutoff_subset_local
    {a : ℝ} (ha : 0 < a) :
    Function.support (negTimeCollarCutoff_local (d := d) a) ⊆
      {ξ : SpacetimeDim d | ξ 0 < -a / 2} := by
  intro ξ hξ
  by_contra hnot
  simp only [Set.mem_setOf_eq, not_lt] at hnot
  exact hξ (by simpa [Function.mem_support] using
    negTimeCollarCutoff_zero_of_neg_half_le_local (d := d) ha hnot)

private theorem tsupport_posTimeCollarCutoff_subset_local
    {a : ℝ} (ha : 0 < a) :
    tsupport (posTimeCollarCutoff_local (d := d) a) ⊆
      {ξ : SpacetimeDim d | a / 2 ≤ ξ 0} := by
  refine closure_minimal ?_ ?_
  · exact (support_posTimeCollarCutoff_subset_local (d := d) ha).trans <| by
      intro ξ hξ
      simpa [Set.mem_setOf_eq] using le_of_lt hξ
  · have hclosed :
        IsClosed {ξ : SpacetimeDim d | a / 2 ≤ ξ 0} := by
      simpa using isClosed_le (continuous_const : Continuous fun _ : SpacetimeDim d => a / 2)
        (continuous_apply (0 : Fin (d + 1)))
    simpa [tsupport] using hclosed

private theorem tsupport_negTimeCollarCutoff_subset_local
    {a : ℝ} (ha : 0 < a) :
    tsupport (negTimeCollarCutoff_local (d := d) a) ⊆
      {ξ : SpacetimeDim d | ξ 0 ≤ -a / 2} := by
  refine closure_minimal ?_ ?_
  · exact (support_negTimeCollarCutoff_subset_local (d := d) ha).trans <| by
      intro ξ hξ
      simpa [Set.mem_setOf_eq] using le_of_lt hξ
  · have hclosed :
        IsClosed {ξ : SpacetimeDim d | ξ 0 ≤ -a / 2} := by
      simpa using isClosed_le (continuous_apply (0 : Fin (d + 1)))
        (continuous_const : Continuous fun _ : SpacetimeDim d => -a / 2)
    simpa [tsupport] using hclosed

private theorem centerCollarCutoff_zero_of_outside_local
    {a : ℝ} (ha : 0 < a) {ξ : SpacetimeDim d}
    (hξ : a ≤ |ξ 0|) :
    centerCollarCutoff_local (d := d) a ξ = 0 := by
  rw [centerCollarCutoff_local]
  by_cases hpos : a ≤ ξ 0
  · have hneg_zero : negTimeCollarCutoff_local (d := d) a ξ = 0 := by
      apply negTimeCollarCutoff_zero_of_neg_half_le_local (d := d) ha
      linarith
    simp [posTimeCollarCutoff_one_of_ge_local (d := d) ha hpos, hneg_zero]
  · have habs : |ξ 0| = -ξ 0 := by
      apply abs_of_nonpos
      by_contra hneg
      have hnonneg' : 0 < ξ 0 := lt_of_not_ge hneg
      have habs' : |ξ 0| = ξ 0 := abs_of_nonneg (le_of_lt hnonneg')
      rw [habs'] at hξ
      linarith
    have hneg : ξ 0 ≤ -a := by
      rw [habs] at hξ
      linarith
    have hpos_zero : posTimeCollarCutoff_local (d := d) a ξ = 0 := by
      apply posTimeCollarCutoff_zero_of_le_half_local (d := d) ha
      linarith
    simp [hpos_zero, negTimeCollarCutoff_one_of_le_neg_local (d := d) ha hneg]

private theorem support_centerCollarCutoff_subset_local
    {a : ℝ} (ha : 0 < a) :
    Function.support (centerCollarCutoff_local (d := d) a) ⊆
      {ξ : SpacetimeDim d | |ξ 0| < a} := by
  intro ξ hξ
  by_contra hnot
  simp only [Set.mem_setOf_eq, not_lt] at hnot
  exact hξ (by simpa [Function.mem_support] using
    centerCollarCutoff_zero_of_outside_local (d := d) ha hnot)

private theorem tsupport_centerCollarCutoff_subset_local
    {a : ℝ} (ha : 0 < a) :
    tsupport (centerCollarCutoff_local (d := d) a) ⊆
      {ξ : SpacetimeDim d | |ξ 0| ≤ a} := by
  refine closure_minimal ?_ ?_
  · exact (support_centerCollarCutoff_subset_local (d := d) ha).trans <| by
      intro ξ hξ
      simpa [Set.mem_setOf_eq] using le_of_lt hξ
  · have hclosed :
        IsClosed {ξ : SpacetimeDim d | |ξ 0| ≤ a} := by
      simpa using isClosed_le ((continuous_apply (0 : Fin (d + 1))).norm)
        (continuous_const : Continuous fun _ : SpacetimeDim d => a)
    simpa [tsupport] using hclosed

private def posTimeCollarPart_local
    (a : ℝ) (h : SchwartzSpacetime d) : SchwartzSpacetime d :=
  SchwartzMap.smulLeftCLM ℂ (posTimeCollarCutoff_local (d := d) a) h

private def negTimeCollarPart_local
    (a : ℝ) (h : SchwartzSpacetime d) : SchwartzSpacetime d :=
  SchwartzMap.smulLeftCLM ℂ (negTimeCollarCutoff_local (d := d) a) h

private def centerCollarPart_local
    (a : ℝ) (h : SchwartzSpacetime d) : SchwartzSpacetime d :=
  SchwartzMap.smulLeftCLM ℂ (centerCollarCutoff_local (d := d) a) h

private theorem posTimeCollarPart_apply_local
    (a : ℝ) (h : SchwartzSpacetime d) (ξ : SpacetimeDim d) :
    posTimeCollarPart_local (d := d) a h ξ =
      posTimeCollarCutoff_local (d := d) a ξ * h ξ := by
  rw [posTimeCollarPart_local,
    SchwartzMap.smulLeftCLM_apply_apply
      (posTimeCollarCutoff_hasTemperateGrowth_local (d := d) a)]
  simp [smul_eq_mul]

private theorem negTimeCollarPart_apply_local
    (a : ℝ) (h : SchwartzSpacetime d) (ξ : SpacetimeDim d) :
    negTimeCollarPart_local (d := d) a h ξ =
      negTimeCollarCutoff_local (d := d) a ξ * h ξ := by
  rw [negTimeCollarPart_local,
    SchwartzMap.smulLeftCLM_apply_apply
      (negTimeCollarCutoff_hasTemperateGrowth_local (d := d) a)]
  simp [smul_eq_mul]

private theorem centerCollarPart_apply_local
    (a : ℝ) (h : SchwartzSpacetime d) (ξ : SpacetimeDim d) :
    centerCollarPart_local (d := d) a h ξ =
      centerCollarCutoff_local (d := d) a ξ * h ξ := by
  rw [centerCollarPart_local,
    SchwartzMap.smulLeftCLM_apply_apply
      (centerCollarCutoff_hasTemperateGrowth_local (d := d) a)]
  simp [smul_eq_mul]

private theorem hasCompactSupport_posTimeCollarPart_local
    (a : ℝ) (h : SchwartzSpacetime d)
    (hh_compact : HasCompactSupport (h : SpacetimeDim d → ℂ)) :
    HasCompactSupport ((posTimeCollarPart_local (d := d) a h : SchwartzSpacetime d) :
      SpacetimeDim d → ℂ) := by
  refine HasCompactSupport.of_support_subset_isCompact hh_compact.isCompact ?_
  intro x hx
  exact (SchwartzMap.tsupport_smulLeftCLM_subset
    (g := posTimeCollarCutoff_local (d := d) a) (f := h) (subset_tsupport _ hx)).1

private theorem hasCompactSupport_negTimeCollarPart_local
    (a : ℝ) (h : SchwartzSpacetime d)
    (hh_compact : HasCompactSupport (h : SpacetimeDim d → ℂ)) :
    HasCompactSupport ((negTimeCollarPart_local (d := d) a h : SchwartzSpacetime d) :
      SpacetimeDim d → ℂ) := by
  refine HasCompactSupport.of_support_subset_isCompact hh_compact.isCompact ?_
  intro x hx
  exact (SchwartzMap.tsupport_smulLeftCLM_subset
    (g := negTimeCollarCutoff_local (d := d) a) (f := h) (subset_tsupport _ hx)).1

private theorem hasCompactSupport_centerCollarPart_local
    (a : ℝ) (h : SchwartzSpacetime d)
    (hh_compact : HasCompactSupport (h : SpacetimeDim d → ℂ)) :
    HasCompactSupport ((centerCollarPart_local (d := d) a h : SchwartzSpacetime d) :
      SpacetimeDim d → ℂ) := by
  refine HasCompactSupport.of_support_subset_isCompact hh_compact.isCompact ?_
  intro x hx
  exact (SchwartzMap.tsupport_smulLeftCLM_subset
    (g := centerCollarCutoff_local (d := d) a) (f := h) (subset_tsupport _ hx)).1

private theorem tsupport_posTimeCollarPart_subset_pos_local
    {a : ℝ} (ha : 0 < a) (h : SchwartzSpacetime d) :
    tsupport ((posTimeCollarPart_local (d := d) a h : SchwartzSpacetime d) :
      SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | 0 < ξ 0} := by
  intro ξ hξ
  have hcut :
      ξ ∈ tsupport (posTimeCollarCutoff_local (d := d) a) :=
    (SchwartzMap.tsupport_smulLeftCLM_subset
      (g := posTimeCollarCutoff_local (d := d) a) (f := h) hξ).2
  have hhalf : a / 2 ≤ ξ 0 :=
    tsupport_posTimeCollarCutoff_subset_local (d := d) ha hcut
  have hξpos : 0 < ξ 0 := by
    have hhalf_pos : 0 < a / 2 := by nlinarith
    exact lt_of_lt_of_le hhalf_pos hhalf
  simpa [Set.mem_setOf_eq] using hξpos

private theorem tsupport_negTimeCollarPart_subset_neg_local
    {a : ℝ} (ha : 0 < a) (h : SchwartzSpacetime d) :
    tsupport ((negTimeCollarPart_local (d := d) a h : SchwartzSpacetime d) :
      SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | ξ 0 < 0} := by
  intro ξ hξ
  have hcut :
      ξ ∈ tsupport (negTimeCollarCutoff_local (d := d) a) :=
    (SchwartzMap.tsupport_smulLeftCLM_subset
      (g := negTimeCollarCutoff_local (d := d) a) (f := h) hξ).2
  have hhalf : ξ 0 ≤ -a / 2 :=
    tsupport_negTimeCollarCutoff_subset_local (d := d) ha hcut
  have hξneg : ξ 0 < 0 := by
    have hhalf_neg : -a / 2 < 0 := by nlinarith
    exact lt_of_le_of_lt hhalf hhalf_neg
  simpa [Set.mem_setOf_eq] using hξneg

private theorem tsupport_centerCollarPart_subset_local
    {a : ℝ} (ha : 0 < a) (h : SchwartzSpacetime d) :
    tsupport ((centerCollarPart_local (d := d) a h : SchwartzSpacetime d) :
      SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | |ξ 0| ≤ a} := by
  intro ξ hξ
  have hcut :
      ξ ∈ tsupport (centerCollarCutoff_local (d := d) a) :=
    (SchwartzMap.tsupport_smulLeftCLM_subset
      (g := centerCollarCutoff_local (d := d) a) (f := h) hξ).2
  exact tsupport_centerCollarCutoff_subset_local (d := d) ha hcut

private theorem zero_not_mem_tsupport_posTimeCollarPart_local
    (a : ℝ) (h : zeroOriginAvoidingSubmodule d) :
    (0 : SpacetimeDim d) ∉ tsupport
      ((posTimeCollarPart_local (d := d) a (h : SchwartzSpacetime d) : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ) := by
  intro hmem
  exact h.property <|
    (SchwartzMap.tsupport_smulLeftCLM_subset
      (g := posTimeCollarCutoff_local (d := d) a) (f := (h : SchwartzSpacetime d)) hmem).1

private theorem zero_not_mem_tsupport_negTimeCollarPart_local
    (a : ℝ) (h : zeroOriginAvoidingSubmodule d) :
    (0 : SpacetimeDim d) ∉ tsupport
      ((negTimeCollarPart_local (d := d) a (h : SchwartzSpacetime d) : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ) := by
  intro hmem
  exact h.property <|
    (SchwartzMap.tsupport_smulLeftCLM_subset
      (g := negTimeCollarCutoff_local (d := d) a) (f := (h : SchwartzSpacetime d)) hmem).1

private theorem zero_not_mem_tsupport_centerCollarPart_local
    (a : ℝ) (h : zeroOriginAvoidingSubmodule d) :
    (0 : SpacetimeDim d) ∉ tsupport
      ((centerCollarPart_local (d := d) a (h : SchwartzSpacetime d) : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ) := by
  intro hmem
  exact h.property <|
    (SchwartzMap.tsupport_smulLeftCLM_subset
      (g := centerCollarCutoff_local (d := d) a) (f := (h : SchwartzSpacetime d)) hmem).1

private theorem collarCutoff_partition_local
    (a : ℝ) (ξ : SpacetimeDim d) :
    posTimeCollarCutoff_local (d := d) a ξ +
      negTimeCollarCutoff_local (d := d) a ξ +
      centerCollarCutoff_local (d := d) a ξ = 1 := by
  simp [centerCollarCutoff_local]

private theorem collarParts_sum_local
    (a : ℝ) (h : SchwartzSpacetime d) :
    posTimeCollarPart_local (d := d) a h +
      negTimeCollarPart_local (d := d) a h +
      centerCollarPart_local (d := d) a h = h := by
  ext ξ
  change
    posTimeCollarPart_local (d := d) a h ξ +
      negTimeCollarPart_local (d := d) a h ξ +
      centerCollarPart_local (d := d) a h ξ = h ξ
  rw [posTimeCollarPart_apply_local, negTimeCollarPart_apply_local,
    centerCollarPart_apply_local]
  calc
    posTimeCollarCutoff_local (d := d) a ξ * h ξ +
        negTimeCollarCutoff_local (d := d) a ξ * h ξ +
        centerCollarCutoff_local (d := d) a ξ * h ξ
      = (posTimeCollarCutoff_local (d := d) a ξ +
          negTimeCollarCutoff_local (d := d) a ξ +
          centerCollarCutoff_local (d := d) a ξ) * h ξ := by ring
    _ = h ξ := by rw [collarCutoff_partition_local, one_mul]

/-- Reduction of the final compact fixed-center shell theorem to the equal-time
collar.

Once compact origin-avoiding shell equality is known for reduced tests whose
support lies in a fixed collar `|ξ₀| ≤ a`, the positive-time and negative-time
pieces are already paid by `InputCAssembly`. So arbitrary compact reduced tests
decompose into two solved sector pieces plus one collar piece. -/
theorem commonK2TimeParametricKernel_real_eq_schwinger_on_differenceShell_of_zeroOriginCompactFixedCenter_of_timeCollar_local
    (OS : OsterwalderSchraderAxioms d)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) = v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v)
    (hK_meas : AEStronglyMeasurable
      (commonK2TimeParametricKernel_real_local (d := d) G) volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ x : NPointDomain d 2 ∂volume,
      ‖commonK2TimeParametricKernel_real_local (d := d) G x‖ ≤
        C_bd * (1 + ‖x‖) ^ N)
    (a : ℝ) (ha : 0 < a)
    (hCollar :
      ∀ h : zeroOriginAvoidingSubmodule d,
        HasCompactSupport (((h : zeroOriginAvoidingSubmodule d) :
          SchwartzSpacetime d) : SpacetimeDim d → ℂ) →
        tsupport (((h : zeroOriginAvoidingSubmodule d) :
          SchwartzSpacetime d) : SpacetimeDim d → ℂ) ⊆
          {ξ : SpacetimeDim d | |ξ 0| ≤ a} →
          OSReconstruction.twoPointZeroDiagonalKernelCLM
              (d := d)
              (commonK2TimeParametricKernel_real_local (d := d) G)
              hK_meas C_bd N hC hK_bound
              (ZeroDiagonalSchwartz.ofClassical
                (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d))) =
            OS.S 2
              (ZeroDiagonalSchwartz.ofClassical
                (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d))))
    (h : zeroOriginAvoidingSubmodule d)
    (hh_compact : HasCompactSupport (((h : zeroOriginAvoidingSubmodule d) :
      SchwartzSpacetime d) : SpacetimeDim d → ℂ)) :
    OSReconstruction.twoPointZeroDiagonalKernelCLM
        (d := d)
        (commonK2TimeParametricKernel_real_local (d := d) G)
        hK_meas C_bd N hC hK_bound
        (ZeroDiagonalSchwartz.ofClassical
          (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d))) =
      OS.S 2
        (ZeroDiagonalSchwartz.ofClassical
          (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d))) := by
  let hPos : positiveTimeCompactSupportSubmodule d := by
    refine ⟨posTimeCollarPart_local (d := d) a (h : SchwartzSpacetime d), ?_⟩
    constructor
    · exact tsupport_posTimeCollarPart_subset_pos_local (d := d) ha (h : SchwartzSpacetime d)
    · exact hasCompactSupport_posTimeCollarPart_local (d := d) a (h : SchwartzSpacetime d) hh_compact
  let hPos₀ : zeroOriginAvoidingSubmodule d :=
    positiveTimeCompactSupportToZeroOriginAvoidingCLM d hPos
  let hNeg : zeroOriginAvoidingSubmodule d := by
    refine ⟨negTimeCollarPart_local (d := d) a (h : SchwartzSpacetime d), ?_⟩
    exact zero_not_mem_tsupport_negTimeCollarPart_local (d := d) a h
  let hMid : zeroOriginAvoidingSubmodule d := by
    refine ⟨centerCollarPart_local (d := d) a (h : SchwartzSpacetime d), ?_⟩
    exact zero_not_mem_tsupport_centerCollarPart_local (d := d) a h
  let hPosS : SchwartzSpacetime d := ((hPos₀ : zeroOriginAvoidingSubmodule d) : SchwartzSpacetime d)
  let hNegS : SchwartzSpacetime d := ((hNeg : zeroOriginAvoidingSubmodule d) : SchwartzSpacetime d)
  let L₁ : zeroOriginAvoidingSubmodule d →L[ℂ] ℂ :=
    (OSReconstruction.twoPointZeroDiagonalKernelCLM
      (d := d)
      (commonK2TimeParametricKernel_real_local (d := d) G)
      hK_meas C_bd N hC hK_bound).comp
        (twoPointDifferenceLiftFixedCenterZeroDiagCLM χ₀)
  let L₂ : zeroOriginAvoidingSubmodule d →L[ℂ] ℂ :=
    OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM
      (d := d) OS χ₀
  have hShell_eq_zeroOrigin :
      ∀ g : zeroOriginAvoidingSubmodule d,
        OSReconstruction.twoPointZeroDiagonalKernelCLM
            (d := d)
            (commonK2TimeParametricKernel_real_local (d := d) G)
            hK_meas C_bd N hC hK_bound
            (ZeroDiagonalSchwartz.ofClassical
              (twoPointDifferenceLift χ₀ (g : SchwartzSpacetime d))) =
          OS.S 2
            (ZeroDiagonalSchwartz.ofClassical
              (twoPointDifferenceLift χ₀ (g : SchwartzSpacetime d))) →
          L₁ g = L₂ g := by
    intro g hg
    calc
      L₁ g =
          OSReconstruction.twoPointZeroDiagonalKernelCLM
              (d := d)
              (commonK2TimeParametricKernel_real_local (d := d) G)
              hK_meas C_bd N hC hK_bound
              (ZeroDiagonalSchwartz.ofClassical
                (twoPointDifferenceLift χ₀ (g : SchwartzSpacetime d))) := by
            simp [L₁, ContinuousLinearMap.comp_apply,
              twoPointDifferenceLiftFixedCenterZeroDiagCLM_eq_ofClassical]
      _ =
          OS.S 2
            (ZeroDiagonalSchwartz.ofClassical
              (twoPointDifferenceLift χ₀ (g : SchwartzSpacetime d))) := hg
      _ = L₂ g := by
            symm
            rw [OsterwalderSchraderAxioms.schwingerDifferenceZeroOriginCLM_eq_centerValue
              (d := d) (OS := OS) χ₀ hχ₀ χ₀ g]
            rw [hχ₀, mul_one]
  have hPos_eq : L₁ hPos₀ = L₂ hPos₀ := by
    have hPos_shell :
        OSReconstruction.twoPointZeroDiagonalKernelCLM
            (d := d)
            (commonK2TimeParametricKernel_real_local (d := d) G)
            hK_meas C_bd N hC hK_bound
            (ZeroDiagonalSchwartz.ofClassical
              (twoPointDifferenceLift χ₀ hPosS)) =
          OS.S 2
            (ZeroDiagonalSchwartz.ofClassical
              (twoPointDifferenceLift χ₀ hPosS)) := by
      have hv :
          VanishesToInfiniteOrderOnCoincidence
            (twoPointDifferenceLift χ₀ hPosS) := by
        exact twoPointDifferenceLift_vanishes_of_zero_not_mem_tsupport χ₀
          hPosS hPos₀.property
      calc
        OSReconstruction.twoPointZeroDiagonalKernelCLM
            (d := d)
            (commonK2TimeParametricKernel_real_local (d := d) G)
            hK_meas C_bd N hC hK_bound
            (ZeroDiagonalSchwartz.ofClassical
              (twoPointDifferenceLift χ₀ hPosS)) =
            ∫ x : NPointDomain d 2,
              commonK2TimeParametricKernel_real_local (d := d) G x *
                twoPointDifferenceLift χ₀ hPosS x := by
              rw [OSReconstruction.twoPointZeroDiagonalKernelCLM_apply]
              rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
                (f := twoPointDifferenceLift χ₀ hPosS) hv]
        _ = OS.S 2
              (ZeroDiagonalSchwartz.ofClassical
                (twoPointDifferenceLift χ₀ hPosS)) := by
              simpa [hPosS, hPos₀, hPos,
                positiveTimeCompactSupportToZeroOriginAvoidingCLM_apply]
                using
                  commonK2TimeParametricKernel_real_eq_schwinger_on_differenceShell_of_positiveSupport_local
                    (d := d) OS χ₀ hχ₀ G hG_euclid hG_diff χ₀ hPos
    exact hShell_eq_zeroOrigin hPos₀ hPos_shell
  have hNeg_compact :
      HasCompactSupport (((hNeg : zeroOriginAvoidingSubmodule d) :
        SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
    simpa [hNeg] using
      hasCompactSupport_negTimeCollarPart_local (d := d) a (h : SchwartzSpacetime d) hh_compact
  have hNeg_neg :
      tsupport (((hNeg : zeroOriginAvoidingSubmodule d) :
        SchwartzSpacetime d) : SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | ξ 0 < 0} := by
    simpa [hNeg] using
      tsupport_negTimeCollarPart_subset_neg_local (d := d) ha (h : SchwartzSpacetime d)
  have hNeg_eq : L₁ hNeg = L₂ hNeg := by
    have hNeg_shell :
        OSReconstruction.twoPointZeroDiagonalKernelCLM
            (d := d)
            (commonK2TimeParametricKernel_real_local (d := d) G)
            hK_meas C_bd N hC hK_bound
            (ZeroDiagonalSchwartz.ofClassical
              (twoPointDifferenceLift χ₀ hNegS)) =
          OS.S 2
            (ZeroDiagonalSchwartz.ofClassical
              (twoPointDifferenceLift χ₀ hNegS)) := by
      have hv :
          VanishesToInfiniteOrderOnCoincidence
            (twoPointDifferenceLift χ₀ hNegS) := by
        exact twoPointDifferenceLift_vanishes_of_zero_not_mem_tsupport χ₀
          hNegS hNeg.property
      calc
        OSReconstruction.twoPointZeroDiagonalKernelCLM
            (d := d)
            (commonK2TimeParametricKernel_real_local (d := d) G)
            hK_meas C_bd N hC hK_bound
            (ZeroDiagonalSchwartz.ofClassical
              (twoPointDifferenceLift χ₀ hNegS)) =
            ∫ x : NPointDomain d 2,
              commonK2TimeParametricKernel_real_local (d := d) G x *
                twoPointDifferenceLift χ₀ hNegS x := by
              rw [OSReconstruction.twoPointZeroDiagonalKernelCLM_apply]
              rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
                (f := twoPointDifferenceLift χ₀ hNegS) hv]
        _ = OS.S 2
              (ZeroDiagonalSchwartz.ofClassical
                (twoPointDifferenceLift χ₀ hNegS)) := by
              simpa [hNegS, hNeg]
                using
                  commonK2TimeParametricKernel_real_eq_schwinger_on_differenceShell_of_negativeSupport_local
                    (d := d) OS χ₀ hχ₀ G hG_euclid hG_diff χ₀
                    hNegS hNeg_neg hNeg_compact
    exact hShell_eq_zeroOrigin hNeg hNeg_shell
  have hMid_compact :
      HasCompactSupport (((hMid : zeroOriginAvoidingSubmodule d) :
        SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
    simpa [hMid] using
      hasCompactSupport_centerCollarPart_local (d := d) a (h : SchwartzSpacetime d) hh_compact
  have hMid_collar :
      tsupport (((hMid : zeroOriginAvoidingSubmodule d) :
        SchwartzSpacetime d) : SpacetimeDim d → ℂ) ⊆
          {ξ : SpacetimeDim d | |ξ 0| ≤ a} := by
    simpa [hMid] using
      tsupport_centerCollarPart_subset_local (d := d) ha (h : SchwartzSpacetime d)
  have hMid_eq : L₁ hMid = L₂ hMid := by
    exact hShell_eq_zeroOrigin hMid (hCollar hMid hMid_compact hMid_collar)
  have hdecomp :
      h = hPos₀ + hNeg + hMid := by
    ext ξ
    have hsumξ :
        (posTimeCollarPart_local (d := d) a (h : SchwartzSpacetime d) +
            negTimeCollarPart_local (d := d) a (h : SchwartzSpacetime d) +
            centerCollarPart_local (d := d) a (h : SchwartzSpacetime d)) ξ =
          (h : SchwartzSpacetime d) ξ :=
      congrArg (fun f : SchwartzSpacetime d => f ξ)
        (collarParts_sum_local (d := d) a (h : SchwartzSpacetime d))
    simpa [hPos₀, hPos, hNeg, hMid,
      positiveTimeCompactSupportToZeroOriginAvoidingCLM_apply, add_assoc]
      using hsumξ.symm
  have hEqL : L₁ h = L₂ h := by
    calc
      L₁ h = L₁ (hPos₀ + hNeg + hMid) := by simpa [hdecomp]
    _ = L₁ hPos₀ + L₁ hNeg + L₁ hMid := by
          simp [map_add, add_assoc]
    _ = L₂ hPos₀ + L₂ hNeg + L₂ hMid := by
          rw [hPos_eq, hNeg_eq, hMid_eq]
    _ = L₂ (hPos₀ + hNeg + hMid) := by
          simp [map_add, add_assoc]
    _ = L₂ h := by simpa [hdecomp]
  simpa [L₁, L₂, ContinuousLinearMap.comp_apply,
    twoPointDifferenceLiftFixedCenterZeroDiagCLM_eq_ofClassical]
    using hEqL

end OSReconstruction
