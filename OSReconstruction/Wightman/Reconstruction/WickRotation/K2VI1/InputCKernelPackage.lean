import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputCAssembly

noncomputable section

open Complex MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- The common reflected zero-anchor difference kernel is measurable once the
positive-time zero-anchor section is continuous on the upper half-space. -/
private theorem measurable_commonDifferenceKernel_real_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G)
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) = v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v) :
    Measurable
      (commonDifferenceKernel_real_local (d := d) G) := by
  let Spos : Set (SpacetimeDim d) := {η : SpacetimeDim d | 0 < η 0}
  let Sneg : Set (SpacetimeDim d) := {η : SpacetimeDim d | η 0 < 0}
  let fpos : SpacetimeDim d → ℂ := fun η =>
    k2TimeParametricKernel (d := d) G
      (![(0 : SpacetimeDim d), η] : NPointDomain d 2)
  let fneg : SpacetimeDim d → ℂ := fun η =>
    k2TimeParametricKernel (d := d) G
      (![(0 : SpacetimeDim d), -η] : NPointDomain d 2)
  have hSpos_meas : MeasurableSet Spos := by
    have hSpos_open : IsOpen Spos := by
      simpa [Spos] using
        isOpen_lt
          (continuous_const : Continuous fun _ : SpacetimeDim d => (0 : ℝ))
          (continuous_apply (0 : Fin (d + 1)))
    exact hSpos_open.measurableSet
  have hSneg_meas : MeasurableSet Sneg := by
    have hSneg_open : IsOpen Sneg := by
      simpa [Sneg] using
        isOpen_lt
          (continuous_apply (0 : Fin (d + 1)))
          (continuous_const : Continuous fun _ : SpacetimeDim d => (0 : ℝ))
    exact hSneg_open.measurableSet
  have hshift0 : timeShiftVec d (0 : ℝ) = 0 := by
    ext μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [timeShiftVec]
    · simp [timeShiftVec, hμ]
  have hpos_cont :
      ContinuousOn fpos Spos := by
    have hsec0 :
        commonZeroCenterShiftSection_local (d := d) G (0 : ℝ) = fpos := by
      funext η
      simp [commonZeroCenterShiftSection_local, fpos, hshift0]
    simpa [Spos, hsec0] using
      (continuousOn_commonZeroCenterShiftSection_on_fixedStrip_local
        (d := d) G hG_holo hG_diff (0 : ℝ))
  have hneg_cont :
      ContinuousOn fneg Sneg := by
    refine hpos_cont.comp ?_ ?_
    · simpa [fneg] using
        (continuous_neg : Continuous fun η : SpacetimeDim d => -η).continuousOn
    · intro η hη
      show 0 < (-η) 0
      simpa using hη
  have hpos_meas :
      Measurable (Spos.piecewise fpos (fun _ : SpacetimeDim d => (0 : ℂ))) := by
    exact hpos_cont.measurable_piecewise continuous_zero.continuousOn hSpos_meas
  have hneg_meas :
      Measurable (Sneg.piecewise fneg (fun _ : SpacetimeDim d => (0 : ℂ))) := by
    exact hneg_cont.measurable_piecewise continuous_zero.continuousOn hSneg_meas
  have hsum_meas :
      Measurable
        (fun η : SpacetimeDim d =>
          Spos.piecewise fpos (fun _ : SpacetimeDim d => (0 : ℂ)) η +
            Sneg.piecewise fneg (fun _ : SpacetimeDim d => (0 : ℂ)) η) := by
    exact hpos_meas.add hneg_meas
  have hsum_eq :
      (fun η : SpacetimeDim d =>
        Spos.piecewise fpos (fun _ : SpacetimeDim d => (0 : ℂ)) η +
          Sneg.piecewise fneg (fun _ : SpacetimeDim d => (0 : ℂ)) η) =
        commonDifferenceKernel_real_local (d := d) G := by
    funext η
    by_cases hpos : 0 < η 0
    · have hneg : ¬ η 0 < 0 := by linarith
      simp [commonDifferenceKernel_real_local, Spos, Sneg, fpos, fneg, hpos, hneg]
    · by_cases hneg : η 0 < 0
      · have hpos' : ¬ 0 < η 0 := hpos
        simp [commonDifferenceKernel_real_local, Spos, Sneg, fpos, fneg, hpos', hneg]
      · simp [commonDifferenceKernel_real_local, Spos, Sneg, fpos, fneg, hpos, hneg]
  simpa [hsum_eq] using hsum_meas

/-- AE-strong measurability of the common reflected zero-anchor difference
kernel. -/
theorem aestronglyMeasurable_commonDifferenceKernel_real_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G)
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) = v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v) :
    AEStronglyMeasurable
      (commonDifferenceKernel_real_local (d := d) G) volume := by
  exact
    (measurable_commonDifferenceKernel_real_local
      (d := d) G hG_holo hG_diff).aestronglyMeasurable

/-- The common reflected zero-anchor difference kernel inherits the same
polynomial bound as the positive-time zero-anchor section. -/
theorem commonDifferenceKernel_real_polyBound_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hG_bound : ∀ ξ : SpacetimeDim d, 0 < ξ 0 →
      ‖k2TimeParametricKernel (d := d) G
          (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2)‖ ≤
        C_bd * (1 + ‖ξ‖) ^ N) :
    ∀ ξ : SpacetimeDim d,
      ‖commonDifferenceKernel_real_local (d := d) G ξ‖ ≤
        C_bd * (1 + ‖ξ‖) ^ N := by
  intro ξ
  by_cases hpos : 0 < ξ 0
  · simp [commonDifferenceKernel_real_local, hpos]
    exact hG_bound ξ hpos
  · by_cases hneg : ξ 0 < 0
    · have hneg_pos : 0 < (-ξ) 0 := by
        simpa using hneg
      have hbase := hG_bound (-ξ) hneg_pos
      simpa [commonDifferenceKernel_real_local, hpos, hneg, norm_neg] using hbase
    · simp [commonDifferenceKernel_real_local, hpos, hneg]
      exact mul_nonneg (le_of_lt hC) (pow_nonneg (by positivity) _)

/-- Measurability of the honest common two-point real Euclidean kernel. -/
theorem aestronglyMeasurable_commonK2TimeParametricKernel_real_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G)
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) = v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v) :
    AEStronglyMeasurable
      (commonK2TimeParametricKernel_real_local (d := d) G) volume := by
  let e : NPointDomain d 2 → SpacetimeDim d := fun x => x 1 - x 0
  have he : Measurable e := by
    exact ((continuous_apply (1 : Fin 2)).sub (continuous_apply (0 : Fin 2))).measurable
  have hmeas :
      Measurable (commonDifferenceKernel_real_local (d := d) G) :=
    measurable_commonDifferenceKernel_real_local
      (d := d) G hG_holo hG_diff
  simpa [commonK2TimeParametricKernel_real_local, twoPointDifferenceKernel, e] using
    (hmeas.comp he).aestronglyMeasurable

/-- Polynomial-growth package for the honest common two-point real Euclidean
kernel coming from the common diff-block witness. -/
theorem exists_commonK2TimeParametricKernel_real_package_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G)
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) = v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hG_bound : ∀ ξ : SpacetimeDim d, 0 < ξ 0 →
      ‖k2TimeParametricKernel (d := d) G
          (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2)‖ ≤
        C_bd * (1 + ‖ξ‖) ^ N) :
    ∃ C' : ℝ,
      0 < C' ∧
      AEStronglyMeasurable
        (commonK2TimeParametricKernel_real_local (d := d) G) volume ∧
      ∀ᵐ x : NPointDomain d 2 ∂volume,
        ‖commonK2TimeParametricKernel_real_local (d := d) G x‖ ≤
          C' * (1 + ‖x‖) ^ N := by
  refine ⟨C_bd * (2 : ℝ) ^ N, ?_, ?_, ?_⟩
  · positivity
  · exact
      aestronglyMeasurable_commonK2TimeParametricKernel_real_local
        (d := d) G hG_holo hG_diff
  · refine Filter.Eventually.of_forall ?_
    intro x
    have hdiff :
        ‖commonDifferenceKernel_real_local (d := d) G (x 1 - x 0)‖ ≤
          C_bd * (1 + ‖x 1 - x 0‖) ^ N :=
      commonDifferenceKernel_real_polyBound_local
        (d := d) G C_bd N hC hG_bound (x 1 - x 0)
    have hcoord :
        ‖x 1 - x 0‖ ≤ (2 : ℝ) * ‖x‖ := by
      calc
        ‖x 1 - x 0‖ ≤ ‖x 1‖ + ‖x 0‖ := norm_sub_le _ _
        _ ≤ ‖x‖ + ‖x‖ := by
          gcongr <;> exact norm_le_pi_norm x _
        _ = (2 : ℝ) * ‖x‖ := by ring
    have hbase :
        1 + ‖x 1 - x 0‖ ≤ (2 : ℝ) * (1 + ‖x‖) := by
      nlinarith [hcoord, norm_nonneg x]
    calc
      ‖commonK2TimeParametricKernel_real_local (d := d) G x‖
          = ‖commonDifferenceKernel_real_local (d := d) G (x 1 - x 0)‖ := by
              simp [commonK2TimeParametricKernel_real_local, twoPointDifferenceKernel]
      _ ≤ C_bd * (1 + ‖x 1 - x 0‖) ^ N := hdiff
      _ ≤ C_bd * ((2 : ℝ) * (1 + ‖x‖)) ^ N := by
            gcongr
      _ = (C_bd * (2 : ℝ) ^ N) * (1 + ‖x‖) ^ N := by
            rw [mul_assoc, mul_pow]

end OSReconstruction
