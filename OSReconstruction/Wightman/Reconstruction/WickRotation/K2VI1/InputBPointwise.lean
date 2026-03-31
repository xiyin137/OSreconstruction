import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputA
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputACommonBoundary
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.InputAStripUniqueness

noncomputable section

open Complex Filter MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Weighted pointwise descended-center approximate identity on a fixed strip.

For a reduced test `h` supported in the positive-time region `ξ₀ > 2s`, the
descended center package may be paired against any strip-continuous one-variable
kernel `ψ` after translating by `ξ`. The resulting scalar sequence converges
pointwise to `ψ ξ`, and multiplying by `h ξ` preserves the limit. This is the
exact one-variable convergence surface needed for the live Input-B shell limit,
once the shell integrand is rewritten as a descended-center convolution against
the candidate limiting kernel. -/
theorem weighted_descended_center_translate_tendsto_of_continuousOn_fixedStrip_local
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (s : ℝ)
    (hs : 0 < s)
    (ψ : SpacetimeDim d → ℂ)
    (hψ_cont : ContinuousOn ψ {ξ : SpacetimeDim d | -(s + s) < ξ 0})
    (h : positiveTimeCompactSupportSubmodule d)
    (hmargin :
      tsupport (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | s + s < ξ 0}) :
    ∀ ξ : SpacetimeDim d,
      Filter.Tendsto
        (fun n =>
          (∫ u : SpacetimeDim d,
            (twoPointCenterShearDescent (d := d) (φ_seq n)
              (reflectedSchwartzSpacetime (φ_seq n))) u * ψ (u + ξ)) *
            ((h : SchwartzSpacetime d) ξ))
        Filter.atTop
        (nhds (ψ ξ * ((h : SchwartzSpacetime d) ξ))) := by
  intro ξ
  by_cases hhξ : ((h : SchwartzSpacetime d) ξ) = 0
  · simpa [hhξ, mul_comm, mul_left_comm, mul_assoc] using
      (Filter.tendsto_const_nhds :
        Filter.Tendsto
          (fun _n : ℕ => (0 : ℂ))
          Filter.atTop
          (nhds (0 : ℂ)))
  · have hξ_mem :
      ξ ∈ tsupport (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ) := by
      exact subset_tsupport _ (Function.mem_support.mpr hhξ)
    have hξ_strip : s + s < ξ 0 := hmargin hξ_mem
    let ψξ : SpacetimeDim d → ℂ := fun u => ψ (u + ξ)
    have hψξ_cont :
        ContinuousOn ψξ {u : SpacetimeDim d | -(s + s) < u 0} := by
      refine hψ_cont.comp ?_ ?_
      · simpa [ψξ] using
          ((continuous_id : Continuous fun u : SpacetimeDim d => u).add continuous_const).continuousOn
      · intro u hu
        change -(s + s) < (u + ξ) 0
        simp only [Pi.add_apply]
        have hu' : -(s + s) < u 0 := hu
        have hξ' : s + s < ξ 0 := hξ_strip
        linarith
    have hbase :
        Filter.Tendsto
          (fun n =>
            ∫ u : SpacetimeDim d,
              (twoPointCenterShearDescent (d := d) (φ_seq n)
                (reflectedSchwartzSpacetime (φ_seq n))) u * ψξ u)
          Filter.atTop
          (nhds (ψξ 0)) :=
      descended_center_approxIdentity_integral_tendsto_of_continuousOn_fixedStrip_local
        (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_ball (s + s)
        (by linarith [hs]) hψξ_cont
    have hmul :
        Filter.Tendsto
          (fun n =>
            ((h : SchwartzSpacetime d) ξ) *
              (∫ u : SpacetimeDim d,
                (twoPointCenterShearDescent (d := d) (φ_seq n)
                  (reflectedSchwartzSpacetime (φ_seq n))) u * ψξ u))
          Filter.atTop
          (nhds (((h : SchwartzSpacetime d) ξ) * ψξ 0)) :=
      Filter.Tendsto.const_mul ((h : SchwartzSpacetime d) ξ) hbase
    simpa [ψξ, mul_comm, mul_left_comm, mul_assoc] using hmul

/-- Specialized common-slice version of the weighted descended-center pointwise
approximate-identity theorem. This is the direct common-witness convergence
surface underlying the live Input-B shell limit. -/
theorem weighted_descended_center_translate_tendsto_commonLiftedDifferenceSlice_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (s : ℝ)
    (hs : 0 < s)
    (h : positiveTimeCompactSupportSubmodule d)
    (hmargin :
      tsupport (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | s + s < ξ 0}) :
    ∀ ξ : SpacetimeDim d,
      Filter.Tendsto
        (fun n =>
          (∫ u : SpacetimeDim d,
            (twoPointCenterShearDescent (d := d) (φ_seq n)
              (reflectedSchwartzSpacetime (φ_seq n))) u *
              commonLiftedDifferenceSliceKernel_local (d := d) G s (u + ξ)) *
            ((h : SchwartzSpacetime d) ξ))
        Filter.atTop
        (nhds
          (commonLiftedDifferenceSliceKernel_local (d := d) G s ξ *
            ((h : SchwartzSpacetime d) ξ))) := by
  intro ξ
  exact
    weighted_descended_center_translate_tendsto_of_continuousOn_fixedStrip_local
      (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_ball s hs
      (commonLiftedDifferenceSliceKernel_local (d := d) G s)
      (commonLiftedDifferenceSliceKernel_continuousOn_local (d := d) G hG_holo s)
      h hmargin ξ

/-- Specialized positive-time version of the weighted descended-center
approximate-identity theorem for the unshifted common zero-anchor section
`ξ ↦ k2TimeParametricKernel G ![0, ξ]`. The support margin `ξ₀ > 2s` is enough
to move the translated kernel entirely inside the positive-time region where the
common zero-anchor section is continuous. -/
theorem weighted_descended_center_translate_tendsto_commonZeroAnchor_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G)
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) = v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (s : ℝ)
    (hs : 0 < s)
    (h : positiveTimeCompactSupportSubmodule d)
    (hmargin :
      tsupport (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | s + s < ξ 0}) :
    ∀ ξ : SpacetimeDim d,
      Filter.Tendsto
        (fun n =>
          (∫ u : SpacetimeDim d,
            (twoPointCenterShearDescent (d := d) (φ_seq n)
              (reflectedSchwartzSpacetime (φ_seq n))) u *
              k2TimeParametricKernel (d := d) G
                (![(0 : SpacetimeDim d), u + ξ] : NPointDomain d 2)) *
            ((h : SchwartzSpacetime d) ξ))
      Filter.atTop
      (nhds
        (k2TimeParametricKernel (d := d) G
            (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2) *
          ((h : SchwartzSpacetime d) ξ))) := by
  intro ξ
  by_cases hhξ : ((h : SchwartzSpacetime d) ξ) = 0
  · simp [hhξ]
  · have hξ_mem :
      ξ ∈ tsupport (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ) := by
      exact subset_tsupport _ (Function.mem_support.mpr hhξ)
    have hξ_pos : s + s < ξ 0 := hmargin hξ_mem
    let ψξ : SpacetimeDim d → ℂ := fun u =>
      k2TimeParametricKernel (d := d) G
        (![(0 : SpacetimeDim d), u + ξ] : NPointDomain d 2)
    have hψ_cont0 :
        ContinuousOn
          (fun η : SpacetimeDim d =>
            k2TimeParametricKernel (d := d) G
              (![(0 : SpacetimeDim d), η] : NPointDomain d 2))
          {η : SpacetimeDim d | 0 < η 0} := by
      have hshift0 : timeShiftVec d (0 : ℝ) = 0 := by
        ext μ
        by_cases hμ : μ = 0
        · subst hμ
          simp [timeShiftVec]
        · simp [timeShiftVec, hμ]
      have hsec0 :
          commonZeroCenterShiftSection_local (d := d) G (0 : ℝ) =
            (fun η : SpacetimeDim d =>
              k2TimeParametricKernel (d := d) G
                (![(0 : SpacetimeDim d), η] : NPointDomain d 2)) := by
        funext η
        simp [commonZeroCenterShiftSection_local, hshift0]
      simpa [hsec0] using
        (continuousOn_commonZeroCenterShiftSection_on_fixedStrip_local
          (d := d) G hG_holo hG_diff (0 : ℝ))
    have hψξ_cont :
        ContinuousOn ψξ {u : SpacetimeDim d | -(s + s) < u 0} := by
      refine hψ_cont0.comp ?_ ?_
      · simpa [ψξ] using
          ((continuous_id : Continuous fun u : SpacetimeDim d => u).add continuous_const).continuousOn
      · intro u hu
        change 0 < (u + ξ) 0
        simp only [Pi.add_apply]
        have hu' : -(s + s) < u 0 := hu
        linarith
    have hbase :
        Filter.Tendsto
          (fun n =>
            ∫ u : SpacetimeDim d,
              (twoPointCenterShearDescent (d := d) (φ_seq n)
                (reflectedSchwartzSpacetime (φ_seq n))) u * ψξ u)
          Filter.atTop
          (nhds (ψξ 0)) :=
      descended_center_approxIdentity_integral_tendsto_of_continuousOn_fixedStrip_local
        (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_ball (s + s)
        (by linarith [hs]) hψξ_cont
    have hmul :
        Filter.Tendsto
          (fun n =>
            ((h : SchwartzSpacetime d) ξ) *
              (∫ u : SpacetimeDim d,
                (twoPointCenterShearDescent (d := d) (φ_seq n)
                  (reflectedSchwartzSpacetime (φ_seq n))) u * ψξ u))
          Filter.atTop
          (nhds
            (((h : SchwartzSpacetime d) ξ) * ψξ 0)) :=
      Filter.Tendsto.const_mul ((h : SchwartzSpacetime d) ξ) hbase
    simpa [ψξ, mul_comm, mul_left_comm, mul_assoc] using hmul

/-- If the translated product-shell scalar already admits the common
zero-anchor descended-convolution formula on the support margin of `h`, then
the weighted pointwise shell limit follows automatically from the descended
approximate-identity theorem for the common zero-anchor section. -/
theorem weighted_shell_pointwise_tendsto_commonZeroAnchor_of_descended_convolution_local
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G)
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) = v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (s : ℝ)
    (hs : 0 < s)
    (h : positiveTimeCompactSupportSubmodule d)
    (hmargin :
      tsupport (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | s + s < ξ 0})
    (hshell_repr :
      ∀ n : ℕ, ∀ ξ : SpacetimeDim d, s + s < ξ 0 →
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (twoPointProductLift (φ_seq n)
            (SCV.translateSchwartz (-ξ)
              (reflectedSchwartzSpacetime (d := d) (φ_seq n))))) =
          ∫ u : SpacetimeDim d,
            (twoPointCenterShearDescent (d := d) (φ_seq n)
              (reflectedSchwartzSpacetime (d := d) (φ_seq n))) u *
              k2TimeParametricKernel (d := d) G
                (![(0 : SpacetimeDim d), u + ξ] : NPointDomain d 2)) :
    ∀ ξ : SpacetimeDim d,
      Filter.Tendsto
        (fun n =>
          (if hξ : 0 < ξ 0 then
            OS.S 2 (ZeroDiagonalSchwartz.ofClassical
              (twoPointProductLift (φ_seq n)
                (SCV.translateSchwartz (-ξ)
                  (reflectedSchwartzSpacetime (d := d) (φ_seq n)))))
          else 0) * ((h : SchwartzSpacetime d) ξ))
        Filter.atTop
        (nhds
          (k2TimeParametricKernel (d := d) G
              (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2) *
            ((h : SchwartzSpacetime d) ξ))) := by
  intro ξ
  by_cases hhξ : ((h : SchwartzSpacetime d) ξ) = 0
  · simp [hhξ]
  · have hξ_mem :
      ξ ∈ tsupport (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ) := by
      exact subset_tsupport _ (Function.mem_support.mpr hhξ)
    have hξ_strip : s + s < ξ 0 := hmargin hξ_mem
    have hξ_pos : 0 < ξ 0 := by linarith
    have hrepr :
        (fun n =>
          (if hξ' : 0 < ξ 0 then
            OS.S 2 (ZeroDiagonalSchwartz.ofClassical
              (twoPointProductLift (φ_seq n)
                (SCV.translateSchwartz (-ξ)
                  (reflectedSchwartzSpacetime (d := d) (φ_seq n)))))
          else 0) * ((h : SchwartzSpacetime d) ξ)) =
        (fun n =>
          (∫ u : SpacetimeDim d,
            (twoPointCenterShearDescent (d := d) (φ_seq n)
              (reflectedSchwartzSpacetime (d := d) (φ_seq n))) u *
              k2TimeParametricKernel (d := d) G
                (![(0 : SpacetimeDim d), u + ξ] : NPointDomain d 2)) *
            ((h : SchwartzSpacetime d) ξ)) := by
      funext n
      rw [dif_pos hξ_pos, hshell_repr n ξ hξ_strip]
    rw [hrepr]
    exact
      weighted_descended_center_translate_tendsto_commonZeroAnchor_local
        (d := d) G hG_holo hG_diff
        φ_seq hφ_nonneg hφ_real hφ_int hφ_ball s hs h hmargin ξ

/-- Under diff-block dependence, the Euclidean two-point witness integrand only
depends on the difference variable. On the real two-point domain, it is exactly
the unshifted zero-anchor section `ξ ↦ k2TimeParametricKernel G ![(0), ξ]`
evaluated at the difference `x₁ - x₀`. -/
theorem euclidIntegrand_eq_commonZeroAnchorDifferenceKernel_of_diffBlockDependence_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) = v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v)
    (x : NPointDomain d 2) :
    G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) =
      k2TimeParametricKernel (d := d) G
        (![(0 : SpacetimeDim d), x 1 - x 0] : NPointDomain d 2) := by
  rw [k2TimeParametricKernel]
  apply hG_diff
  intro μ
  by_cases hμ : μ = 0
  · subst hμ
    simp [BHW.toDiffFlat, BHW.flattenCfg, BHW.diffCoordEquiv_apply,
      finProdFinEquiv.symm_apply_apply, wickRotatePoint]
    ring
  · simp [BHW.toDiffFlat, BHW.flattenCfg, BHW.diffCoordEquiv_apply,
      finProdFinEquiv.symm_apply_apply, wickRotatePoint, hμ]

/-- A difference-only kernel paired against the translated reflected product
shell factors through the translated descended-center representative. This is
the exact deterministic Fubini/change-of-variables step needed in Input B once
the shell witness has been rewritten as a common zero-anchor difference kernel.
-/
theorem integral_differenceOnlyKernel_translated_reflected_productShell_eq_descended_center_local
    (K : SpacetimeDim d → ℂ)
    (hK_meas : AEStronglyMeasurable
      (fun z : NPointDomain d 2 => K (z 1)) volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ z : NPointDomain d 2 ∂volume,
      ‖K (z 1)‖ ≤ C_bd * (1 + ‖z‖) ^ N)
    (φ : SchwartzSpacetime d)
    (hφ_int : ∫ x : SpacetimeDim d, φ x = 1)
    (ξ : SpacetimeDim d) :
    ∫ z : NPointDomain d 2,
      K (z 1) *
        ((φ (z 0)) *
          SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime (d := d) φ) (z 0 + z 1)) =
      ∫ η : SpacetimeDim d,
        K η *
          (SCV.translateSchwartz (-ξ)
            (twoPointCenterShearDescent (d := d) φ
              (reflectedSchwartzSpacetime (d := d) φ))) η := by
  have hsame_center :=
    differenceOnlyKernel_productShell_to_same_center_of_package_local
      (d := d) K hK_meas C_bd N hC hK_bound φ hφ_int
      (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime (d := d) φ))
  calc
    ∫ z : NPointDomain d 2,
        K (z 1) *
          ((φ (z 0)) *
            SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime (d := d) φ) (z 0 + z 1))
      =
      ∫ z : NPointDomain d 2,
        K (z 1) *
          ((φ (z 0)) *
            (twoPointCenterShearDescent (d := d) φ
              (SCV.translateSchwartz (-ξ)
                (reflectedSchwartzSpacetime (d := d) φ))) (z 1)) := by
          simpa using hsame_center
    _ =
      ∫ z : NPointDomain d 2,
        K (z 1) *
          ((φ (z 0)) *
            (SCV.translateSchwartz (-ξ)
              (twoPointCenterShearDescent (d := d) φ
                (reflectedSchwartzSpacetime (d := d) φ))) (z 1)) := by
          refine integral_congr_ae ?_
          filter_upwards with z
          rw [twoPointCenterShearDescent_translated_reflected_eq_translated_local
            (d := d) φ ξ]
    _ =
      (∫ u : SpacetimeDim d, φ u) *
        ∫ η : SpacetimeDim d,
          K η *
            (SCV.translateSchwartz (-ξ)
              (twoPointCenterShearDescent (d := d) φ
                (reflectedSchwartzSpacetime (d := d) φ))) η := by
          exact integral_centerDiff_differenceOnly_kernel_factorizes
            (d := d) K φ
            (SCV.translateSchwartz (-ξ)
              (twoPointCenterShearDescent (d := d) φ
                (reflectedSchwartzSpacetime (d := d) φ)))
    _ =
      ∫ η : SpacetimeDim d,
        K η *
          (SCV.translateSchwartz (-ξ)
            (twoPointCenterShearDescent (d := d) φ
              (reflectedSchwartzSpacetime (d := d) φ))) η := by
          rw [hφ_int, one_mul]

/-- Rewriting the translated descended-center pairing in the weighted
approximate-identity form used later in Input B. -/
theorem integral_mul_translateSchwartz_eq_integral_weighted_shift_local
    (K : SpacetimeDim d → ℂ)
    (χ : SchwartzSpacetime d)
    (ξ : SpacetimeDim d) :
    ∫ η : SpacetimeDim d, K η * (SCV.translateSchwartz (-ξ) χ) η =
      ∫ u : SpacetimeDim d, χ u * K (u + ξ) := by
  calc
    ∫ η : SpacetimeDim d, K η * (SCV.translateSchwartz (-ξ) χ) η
      = ∫ u : SpacetimeDim d,
          (fun η : SpacetimeDim d => K η * (SCV.translateSchwartz (-ξ) χ) η) (u + ξ) := by
            symm
            exact MeasureTheory.integral_add_right_eq_self
              (μ := (volume : Measure (SpacetimeDim d)))
              (f := fun η : SpacetimeDim d =>
                K η * (SCV.translateSchwartz (-ξ) χ) η)
              ξ
    _ = ∫ u : SpacetimeDim d, χ u * K (u + ξ) := by
          refine integral_congr_ae ?_
          filter_upwards with u
          rw [SCV.translateSchwartz_apply]
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_comm]

private theorem translated_reflected_tsupport_pos_local
    (φ : SchwartzSpacetime d)
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0})
    (ξ : SpacetimeDim d)
    (hξ : 0 < ξ 0) :
    tsupport ((SCV.translateSchwartz (-ξ)
        (reflectedSchwartzSpacetime (d := d) φ) : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | 0 < x 0} := by
  intro x hx
  have hx_pre :
      x + (-ξ) ∈ tsupport (reflectedSchwartzSpacetime (d := d) φ : SpacetimeDim d → ℂ) := by
    exact tsupport_comp_subset_preimage
      (reflectedSchwartzSpacetime (d := d) φ : SpacetimeDim d → ℂ)
      (f := fun y : SpacetimeDim d => y + (-ξ))
      (Homeomorph.addRight (-ξ)).continuous hx
  have hx_shift : 0 < (x + (-ξ)) 0 :=
    reflectedSchwartzSpacetime_tsupport_pos (d := d) φ hφ_neg hx_pre
  have hx0 : 0 < x 0 := by
    have hx_gt_xi : ξ 0 < x 0 := by
      simpa [sub_eq_add_neg] using hx_shift
    linarith
  exact hx0

private theorem translated_reflected_productLift_vanishes_local
    (φ : SchwartzSpacetime d)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0})
    (ξ : SpacetimeDim d)
    (hξ : 0 < ξ 0) :
    VanishesToInfiniteOrderOnCoincidence
      (twoPointProductLift φ
        (SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime (d := d) φ))) := by
  let ψ : SchwartzSpacetime d :=
    SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime (d := d) φ)
  have hφ_pos :
      tsupport (((SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d φ : SchwartzNPoint d 1) : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 :=
    osConj_onePointToFin1_tsupport_orderedPositiveTime_local
      (d := d) φ hφ_compact hφ_neg
  have hψ_pos_time :
      tsupport (ψ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0} :=
    translated_reflected_tsupport_pos_local (d := d) φ hφ_neg ξ hξ
  have hψ_pos :
      tsupport ((onePointToFin1CLM d ψ : SchwartzNPoint d 1) :
        NPointDomain d 1 → ℂ) ⊆ OrderedPositiveTimeRegion d 1 :=
    onePointToFin1_tsupport_orderedPositiveTime_vi1_local (d := d) ψ hψ_pos_time
  have hvanish :
      VanishesToInfiniteOrderOnCoincidence
        ((SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d φ)).osConjTensorProduct
          (onePointToFin1CLM d ψ)) :=
    VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d)
      (f := SchwartzNPoint.osConj (d := d) (n := 1)
        (onePointToFin1CLM d φ : SchwartzNPoint d 1))
      (g := onePointToFin1CLM d ψ)
      hφ_pos hψ_pos
  have hprod_eq :
      (SchwartzNPoint.osConj (d := d) (n := 1)
          (onePointToFin1CLM d φ)).osConjTensorProduct
        (onePointToFin1CLM d ψ) =
        twoPointProductLift φ ψ := by
    ext x
    exact onePoint_osConjTensorProduct_apply (d := d) φ ψ x
  simpa [ψ, hprod_eq] using hvanish

private theorem aestronglyMeasurable_indicator_commonZeroAnchor_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G)
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) = v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v) :
    AEStronglyMeasurable
      (fun z : NPointDomain d 2 =>
        if 0 < z 1 0 then
          k2TimeParametricKernel (d := d) G
            (![(0 : SpacetimeDim d), z 1] : NPointDomain d 2)
        else 0)
      volume := by
  let S : Set (SpacetimeDim d) := {η : SpacetimeDim d | 0 < η 0}
  have hS_meas : MeasurableSet S := by
    have hS_open : IsOpen S := by
      simpa [S] using
        isOpen_lt
          (continuous_const : Continuous fun _ : SpacetimeDim d => (0 : ℝ))
          (continuous_apply (0 : Fin (d + 1)))
    exact hS_open.measurableSet
  have hshift0 : timeShiftVec d (0 : ℝ) = 0 := by
    ext μ
    by_cases hμ : μ = 0
    · subst hμ
      simp [timeShiftVec]
    · simp [timeShiftVec, hμ]
  have hcont :
      ContinuousOn
        (fun η : SpacetimeDim d =>
          k2TimeParametricKernel (d := d) G
            (![(0 : SpacetimeDim d), η] : NPointDomain d 2))
        S := by
    have hsec0 :
        commonZeroCenterShiftSection_local (d := d) G (0 : ℝ) =
          (fun η : SpacetimeDim d =>
            k2TimeParametricKernel (d := d) G
              (![(0 : SpacetimeDim d), η] : NPointDomain d 2)) := by
      funext η
      simp [commonZeroCenterShiftSection_local, hshift0]
    simpa [S, hsec0] using
      (continuousOn_commonZeroCenterShiftSection_on_fixedStrip_local
        (d := d) G hG_holo hG_diff (0 : ℝ))
  have hmeas :
      Measurable (S.piecewise
        (fun η : SpacetimeDim d =>
          k2TimeParametricKernel (d := d) G
            (![(0 : SpacetimeDim d), η] : NPointDomain d 2))
        (fun _ : SpacetimeDim d => (0 : ℂ))) := by
    exact hcont.measurable_piecewise continuous_zero.continuousOn hS_meas
  have hcomp :
      Measurable
        (fun z : NPointDomain d 2 =>
          S.piecewise
            (fun η : SpacetimeDim d =>
              k2TimeParametricKernel (d := d) G
                (![(0 : SpacetimeDim d), η] : NPointDomain d 2))
            (fun _ : SpacetimeDim d => (0 : ℂ)) (z 1)) := by
    exact Measurable.comp hmeas (continuous_apply (1 : Fin 2)).measurable
  simpa [S, Set.piecewise] using hcomp.aestronglyMeasurable

private theorem ae_indicator_commonZeroAnchor_polyBound_local
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (C_bd : ℝ) (N : ℕ)
    (hC : 0 < C_bd)
    (hG_bound : ∀ ξ : SpacetimeDim d, 0 < ξ 0 →
      ‖k2TimeParametricKernel (d := d) G
          (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2)‖ ≤
        C_bd * (1 + ‖ξ‖) ^ N) :
    ∀ᵐ z : NPointDomain d 2 ∂volume,
      ‖if 0 < z 1 0 then
          k2TimeParametricKernel (d := d) G
            (![(0 : SpacetimeDim d), z 1] : NPointDomain d 2)
        else 0‖ ≤
        C_bd * (1 + ‖z‖) ^ N := by
  refine Filter.Eventually.of_forall ?_
  intro z
  by_cases hz : 0 < z 1 0
  · simp [hz]
    have hpow :
        (1 + ‖z 1‖) ^ N ≤ (1 + ‖z‖) ^ N := by
      gcongr
      exact norm_le_pi_norm z 1
    exact le_trans (hG_bound (z 1) hz) <|
      mul_le_mul_of_nonneg_left hpow (le_of_lt hC)
  · simp [hz]
    exact mul_nonneg (le_of_lt hC) (pow_nonneg (by positivity) _)

/-- Direct common-witness shell representation for Input B.

On the positive-time shell `ξ₀ > 0`, the translated reflected product shell is
already represented by the descended-center convolution against the common
zero-anchor kernel. The only analytic input is the common witness itself:
Euclidean reproduction, diff-block dependence, and the positive-time polynomial
bound needed to run the same-center transport theorem with the zeroed-off-strip
kernel. -/
theorem shell_scalar_eq_descended_convolution_commonZeroAnchor_local
    (OS : OsterwalderSchraderAxioms d)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) = v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hG_bound : ∀ ξ : SpacetimeDim d, 0 < ξ 0 →
      ‖k2TimeParametricKernel (d := d) G
          (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2)‖ ≤
        C_bd * (1 + ‖ξ‖) ^ N)
    (φ : SchwartzSpacetime d)
    (hφ_int : ∫ x : SpacetimeDim d, φ x = 1)
    (hφ_compact : HasCompactSupport (φ : SpacetimeDim d → ℂ))
    (hφ_neg : tsupport (φ : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | x 0 < 0})
    (ξ : SpacetimeDim d)
    (hξ : 0 < ξ 0) :
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical
      (twoPointProductLift φ
        (SCV.translateSchwartz (-ξ)
          (reflectedSchwartzSpacetime (d := d) φ)))) =
      ∫ u : SpacetimeDim d,
        (twoPointCenterShearDescent (d := d) φ
          (reflectedSchwartzSpacetime (d := d) φ)) u *
          k2TimeParametricKernel (d := d) G
            (![(0 : SpacetimeDim d), u + ξ] : NPointDomain d 2) := by
  let ψ : SchwartzSpacetime d :=
    SCV.translateSchwartz (-ξ) (reflectedSchwartzSpacetime (d := d) φ)
  let K : SpacetimeDim d → ℂ := fun η =>
    if 0 < η 0 then
      k2TimeParametricKernel (d := d) G
        (![(0 : SpacetimeDim d), η] : NPointDomain d 2)
    else 0
  have hvanish :
      VanishesToInfiniteOrderOnCoincidence (twoPointProductLift φ ψ) :=
    translated_reflected_productLift_vanishes_local
      (d := d) φ hφ_compact hφ_neg ξ hξ
  have hS₂ :
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointProductLift φ ψ)) =
        ∫ x : NPointDomain d 2,
          G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) *
            (twoPointProductLift φ ψ x) := by
    simpa [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
      (f := twoPointProductLift φ ψ) hvanish] using
      hG_euclid (ZeroDiagonalSchwartz.ofClassical (twoPointProductLift φ ψ))
  have hK_meas :
      AEStronglyMeasurable (fun z : NPointDomain d 2 => K (z 1)) volume :=
    aestronglyMeasurable_indicator_commonZeroAnchor_local
      (d := d) G hG_holo hG_diff
  have hK_bound :
      ∀ᵐ z : NPointDomain d 2 ∂volume,
        ‖K (z 1)‖ ≤ C_bd * (1 + ‖z‖) ^ N :=
    ae_indicator_commonZeroAnchor_polyBound_local
      (d := d) G C_bd N hC hG_bound
  have hsame_shell :
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointProductLift φ ψ)) =
        ∫ z : NPointDomain d 2,
          K (z 1) *
            ((φ (z 0)) * ψ (z 0 + z 1)) := by
    calc
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical (twoPointProductLift φ ψ))
        = ∫ x : NPointDomain d 2,
            G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) *
              (twoPointProductLift φ ψ x) := hS₂
      _ =
        ∫ z : NPointDomain d 2,
          G (BHW.toDiffFlat 2 d
              (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))) *
            ((φ (z 0)) * ψ (z 0 + z 1)) := by
              simpa [ψ] using
                (integral_mul_twoPointProductLift_eq_centerShear
                  (d := d)
                  (Ψ := fun y : NPointDomain d 2 =>
                    G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (y i))))
                  φ ψ)
      _ =
        ∫ z : NPointDomain d 2,
          K (z 1) * ((φ (z 0)) * ψ (z 0 + z 1)) := by
            refine integral_congr_ae ?_
            filter_upwards with z
            by_cases hz :
                (φ (z 0)) * ψ (z 0 + z 1) = 0
            · simp [hz]
            · have hz_mem :
                z ∈ Function.support
                  (fun z : NPointDomain d 2 =>
                    (φ (z 0)) * ψ (z 0 + z 1)) := Function.mem_support.mpr hz
              have hz0_neg : (z 0) 0 < 0 := by
                have hzφ : φ (z 0) ≠ 0 := by
                  intro hzφ
                  exact hz (by simp [hzφ])
                have hz0_mem : z 0 ∈ tsupport (φ : SpacetimeDim d → ℂ) :=
                  subset_tsupport _ (Function.mem_support.mpr hzφ)
                exact hφ_neg hz0_mem
              have hzψ_pos :
                  0 < (z 0 + z 1 + (-ξ)) 0 := by
                have hzψ : ψ (z 0 + z 1) ≠ 0 := by
                  intro hzψ
                  exact hz (by simp [hzψ])
                have hzψ_mem :
                    z 0 + z 1 ∈ tsupport (ψ : SpacetimeDim d → ℂ) :=
                  subset_tsupport _ (Function.mem_support.mpr hzψ)
                have hzpre :
                    z 0 + z 1 + (-ξ) ∈
                      tsupport (reflectedSchwartzSpacetime (d := d) φ : SpacetimeDim d → ℂ) := by
                  simpa [ψ] using
                    (tsupport_comp_subset_preimage
                      (reflectedSchwartzSpacetime (d := d) φ : SpacetimeDim d → ℂ)
                      (f := fun y : SpacetimeDim d => y + (-ξ))
                      (Homeomorph.addRight (-ξ)).continuous hzψ_mem)
                exact reflectedSchwartzSpacetime_tsupport_pos (d := d) φ hφ_neg hzpre
              have hz1_pos : 0 < (z 1) 0 := by
                have hz1_gt : ξ 0 - z 0 0 < z 1 0 := by
                  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hzψ_pos
                linarith
              have hk :
                  G (BHW.toDiffFlat 2 d
                      (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))) =
                    k2TimeParametricKernel (d := d) G
                      (![(0 : SpacetimeDim d), z 1] : NPointDomain d 2) := by
                calc
                  G (BHW.toDiffFlat 2 d
                      (fun i => wickRotatePoint (((twoPointCenterDiffCLE d) z) i))) =
                    k2TimeParametricKernel (d := d) G
                      (![(0 : SpacetimeDim d),
                        ((twoPointCenterDiffCLE d) z) 1 -
                          ((twoPointCenterDiffCLE d) z) 0] : NPointDomain d 2) := by
                        exact
                          euclidIntegrand_eq_commonZeroAnchorDifferenceKernel_of_diffBlockDependence_local
                            (d := d) G hG_diff ((twoPointCenterDiffCLE d) z)
                  _ =
                    k2TimeParametricKernel (d := d) G
                      (![(0 : SpacetimeDim d), z 1] : NPointDomain d 2) := by
                        simp [twoPointCenterDiffCLE, twoPointCenterDiffLinearEquiv]
              simp [K, hz1_pos, hk]
  calc
    OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift φ
          (SCV.translateSchwartz (-ξ)
            (reflectedSchwartzSpacetime (d := d) φ)))) =
      ∫ z : NPointDomain d 2,
        K (z 1) * ((φ (z 0)) * ψ (z 0 + z 1)) := hsame_shell
    _ =
      ∫ u : SpacetimeDim d,
        (twoPointCenterShearDescent (d := d) φ
          (reflectedSchwartzSpacetime (d := d) φ)) u * K (u + ξ) := by
        calc
          ∫ z : NPointDomain d 2,
              K (z 1) * ((φ (z 0)) * ψ (z 0 + z 1))
            =
              ∫ η : SpacetimeDim d,
                K η *
                  (SCV.translateSchwartz (-ξ)
                    (twoPointCenterShearDescent (d := d) φ
                      (reflectedSchwartzSpacetime (d := d) φ))) η := by
                  simpa [K, ψ] using
                    integral_differenceOnlyKernel_translated_reflected_productShell_eq_descended_center_local
                      (d := d) K hK_meas C_bd N hC hK_bound φ hφ_int ξ
          _ =
              ∫ u : SpacetimeDim d,
                (twoPointCenterShearDescent (d := d) φ
                  (reflectedSchwartzSpacetime (d := d) φ)) u * K (u + ξ) := by
                    exact integral_mul_translateSchwartz_eq_integral_weighted_shift_local
                      (d := d) K
                      (twoPointCenterShearDescent (d := d) φ
                        (reflectedSchwartzSpacetime (d := d) φ))
                      ξ
    _ =
      ∫ u : SpacetimeDim d,
        (twoPointCenterShearDescent (d := d) φ
          (reflectedSchwartzSpacetime (d := d) φ)) u *
          k2TimeParametricKernel (d := d) G
            (![(0 : SpacetimeDim d), u + ξ] : NPointDomain d 2) := by
        refine integral_congr_ae ?_
        filter_upwards with u
        by_cases hu :
            (twoPointCenterShearDescent (d := d) φ
              (reflectedSchwartzSpacetime (d := d) φ)) u = 0
        · simp [hu]
        · have hu_mem :
            u ∈ tsupport
              (((twoPointCenterShearDescent (d := d) φ
                (reflectedSchwartzSpacetime (d := d) φ)) : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ) :=
            subset_tsupport _ (Function.mem_support.mpr hu)
          have hu_pos : 0 < u 0 :=
            twoPointCenterShearDescent_reflected_tsupport_pos_local
              (d := d) φ hφ_compact hφ_neg hu_mem
          have huξ_pos : 0 < (u + ξ) 0 := by
            simp only [Pi.add_apply]
            linarith
          have huK :
              K (u + ξ) =
                k2TimeParametricKernel (d := d) G
                  (![(0 : SpacetimeDim d), u + ξ] : NPointDomain d 2) := by
            dsimp [K]
            change
              (if 0 < u 0 + ξ 0 then
                k2TimeParametricKernel (d := d) G
                  (![(0 : SpacetimeDim d), u + ξ] : NPointDomain d 2)
              else 0) =
                k2TimeParametricKernel (d := d) G
                  (![(0 : SpacetimeDim d), u + ξ] : NPointDomain d 2)
            have huξ_pos' : 0 < u 0 + ξ 0 := by
              simpa [Pi.add_apply] using huξ_pos
            rw [if_pos huξ_pos']
          rw [huK]

/-- Once a shell scalar is represented by a difference-only product-shell
pairing, the descended-center convolution form follows automatically. This
isolates the remaining Input-B work to the genuinely OS-specific step of
producing the common zero-anchor kernel representation. -/
theorem shell_scalar_eq_descended_convolution_of_differenceOnly_productShell_local
    (I : ℂ)
    (K : SpacetimeDim d → ℂ)
    (φ : SchwartzSpacetime d)
    (hφ_int : ∫ x : SpacetimeDim d, φ x = 1)
    (ξ : SpacetimeDim d)
    (hI :
      I =
        ∫ z : NPointDomain d 2,
          K (z 1) *
            ((φ (z 0)) *
              SCV.translateSchwartz (-ξ)
                (reflectedSchwartzSpacetime (d := d) φ) (z 0 + z 1)))
    (hK_meas : AEStronglyMeasurable
      (fun z : NPointDomain d 2 => K (z 1)) volume)
    (C_bd : ℝ) (N : ℕ) (hC : 0 < C_bd)
    (hK_bound : ∀ᵐ z : NPointDomain d 2 ∂volume,
      ‖K (z 1)‖ ≤ C_bd * (1 + ‖z‖) ^ N) :
    I =
      ∫ u : SpacetimeDim d,
        (twoPointCenterShearDescent (d := d) φ
          (reflectedSchwartzSpacetime (d := d) φ)) u * K (u + ξ) := by
  rw [hI]
  rw [integral_differenceOnlyKernel_translated_reflected_productShell_eq_descended_center_local
    (d := d) K hK_meas C_bd N hC hK_bound φ hφ_int ξ]
  rw [integral_mul_translateSchwartz_eq_integral_weighted_shift_local
    (d := d) K
    (twoPointCenterShearDescent (d := d) φ (reflectedSchwartzSpacetime (d := d) φ))
    ξ]

/-- The unshifted common zero-anchor section already represents the reduced
positive-time Schwinger functional once the common witness has Euclidean
reproduction and diff-block dependence. This is the natural candidate target
function for the live Input-B shell limit. -/
theorem schwingerDifferencePositiveCLM_eq_integral_commonZeroAnchor_local
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
    (h : positiveTimeCompactSupportSubmodule d) :
    (OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
      (d := d) OS χ₀) h =
      ∫ ξ : SpacetimeDim d,
        k2TimeParametricKernel (d := d) G
          (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2) *
          ((h : SchwartzSpacetime d) ξ) := by
  have hrepr :
      OS.S 2
        (ZeroDiagonalSchwartz.ofClassical
          (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d))) =
        ∫ x : NPointDomain d 2,
          k2TimeParametricKernel (d := d) G
              (![(0 : SpacetimeDim d), x 1 - x 0] : NPointDomain d 2) *
            twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d) x := by
    have hrepr0 := hG_euclid (twoPointDifferenceLiftPositiveZeroDiagCLM χ₀ h)
    have hv :
        VanishesToInfiniteOrderOnCoincidence
          (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d)) :=
      twoPointDifferenceLift_vanishes_of_zero_not_mem_tsupport χ₀
        (h : SchwartzSpacetime d)
        (zero_not_mem_tsupport_of_mem_positiveTimeCompactSupportSubmodule h)
    rw [twoPointDifferenceLiftPositiveZeroDiagCLM_eq_ofClassical] at hrepr0
    rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
      (f := twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d)) hv] at hrepr0
    calc
      OS.S 2
          (ZeroDiagonalSchwartz.ofClassical
            (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d))) =
        ∫ x : NPointDomain d 2,
          G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) *
            twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d) x := by
              exact hrepr0
      _ =
        ∫ x : NPointDomain d 2,
          k2TimeParametricKernel (d := d) G
              (![(0 : SpacetimeDim d), x 1 - x 0] : NPointDomain d 2) *
            twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d) x := by
              refine integral_congr_ae ?_
              filter_upwards with x
              rw [euclidIntegrand_eq_commonZeroAnchorDifferenceKernel_of_diffBlockDependence_local
                (d := d) G hG_diff x]
  calc
    (OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
        (d := d) OS χ₀) h =
      OS.S 2
        (ZeroDiagonalSchwartz.ofClassical
          (twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d))) := by
        rw [OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM_apply]
    _ =
      ∫ x : NPointDomain d 2,
        k2TimeParametricKernel (d := d) G
            (![(0 : SpacetimeDim d), x 1 - x 0] : NPointDomain d 2) *
          twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d) x := hrepr
    _ =
      ∫ x : NPointDomain d 2,
        twoPointDifferenceKernel
          (d := d)
          (fun ξ : SpacetimeDim d =>
            k2TimeParametricKernel (d := d) G
              (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2)) x *
          twoPointDifferenceLift χ₀ (h : SchwartzSpacetime d) x := by
        simp [OSReconstruction.twoPointDifferenceKernel]
    _ =
      (∫ u : SpacetimeDim d, χ₀ u) *
        ∫ ξ : SpacetimeDim d,
          k2TimeParametricKernel (d := d) G
            (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2) *
            ((h : SchwartzSpacetime d) ξ) := by
        exact integral_twoPointDifferenceKernel_mul_differenceLift_factorizes
          (d := d)
          (fun ξ : SpacetimeDim d =>
            k2TimeParametricKernel (d := d) G
              (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2))
          χ₀ (h : SchwartzSpacetime d)
    _ =
      ∫ ξ : SpacetimeDim d,
        k2TimeParametricKernel (d := d) G
          (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2) *
          ((h : SchwartzSpacetime d) ξ) := by
        rw [hχ₀, one_mul]

/-- The reduced positive-time Schwinger functional is the integral of the
common zero-anchor section, extended by `0` off positive time. This is the
exact target-integrand shape needed in the live Input-B DCT theorem. -/
theorem schwingerDifferencePositiveCLM_eq_integral_indicator_commonZeroAnchor_local
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
    (h : positiveTimeCompactSupportSubmodule d) :
    let g : SpacetimeDim d → ℂ := fun ξ =>
      if 0 < ξ 0 then
        k2TimeParametricKernel (d := d) G
          (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2)
      else 0
    (OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
      (d := d) OS χ₀) h =
      ∫ ξ : SpacetimeDim d, g ξ * ((h : SchwartzSpacetime d) ξ) := by
  dsimp
  rw [schwingerDifferencePositiveCLM_eq_integral_commonZeroAnchor_local
    (d := d) OS χ₀ hχ₀ G hG_euclid hG_diff h]
  refine integral_congr_ae ?_
  filter_upwards with ξ
  by_cases hξ : 0 < ξ 0
  · simp [hξ]
  · have hzero :
        ((h : SchwartzSpacetime d) ξ) = 0 := by
        by_contra hh
        have hmem : ξ ∈ tsupport (((h : positiveTimeCompactSupportSubmodule d) :
          SchwartzSpacetime d) : SpacetimeDim d → ℂ) :=
          subset_tsupport _ (Function.mem_support.mpr hh)
        exact hξ (h.property.1 hmem)
    simp [hξ, hzero]

/-- Once the translated product shell is represented by the common zero-anchor
descended convolution on the support margin of `h`, the full pointwise-limit and
target-integral package for Input B follows with the honest limiting kernel
`g(ξ) = if 0 < ξ₀ then k2TimeParametricKernel G ![0, ξ] else 0`. This isolates
the remaining Input-B work to the common-witness representation step. -/
theorem exists_shell_pointwise_limit_function_of_commonZeroAnchor_local
    (OS : OsterwalderSchraderAxioms d)
    (χ₀ : SchwartzSpacetime d)
    (hχ₀ : ∫ x : SpacetimeDim d, χ₀ x = 1)
    (G : (Fin (2 * (d + 1)) → ℂ) → ℂ)
    (hG_holo : IsTimeHolomorphicFlatPositiveTimeDiffWitness G)
    (hG_euclid : ∀ (f : ZeroDiagonalSchwartz d 2),
      OS.S 2 f = ∫ x : NPointDomain d 2,
        G (BHW.toDiffFlat 2 d (fun i => wickRotatePoint (x i))) * (f.1 x))
    (hG_diff : ∀ u v : Fin (2 * (d + 1)) → ℂ,
      (∀ μ : Fin (d + 1),
        u (finProdFinEquiv (⟨1, by omega⟩, μ)) = v (finProdFinEquiv (⟨1, by omega⟩, μ))) →
      G u = G v)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_nonneg : ∀ n x, 0 ≤ (φ_seq n x).re)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_int : ∀ n, ∫ x : SpacetimeDim d, φ_seq n x = 1)
    (hφ_ball : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      Metric.ball (0 : SpacetimeDim d) (1 / (n + 1 : ℝ)))
    (s : ℝ)
    (hs : 0 < s)
    (h : positiveTimeCompactSupportSubmodule d)
    (hmargin :
      tsupport (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | s + s < ξ 0})
    (hshell_repr :
      ∀ n : ℕ, ∀ ξ : SpacetimeDim d, s + s < ξ 0 →
        OS.S 2 (ZeroDiagonalSchwartz.ofClassical
          (twoPointProductLift (φ_seq n)
            (SCV.translateSchwartz (-ξ)
              (reflectedSchwartzSpacetime (d := d) (φ_seq n))))) =
          ∫ u : SpacetimeDim d,
            (twoPointCenterShearDescent (d := d) (φ_seq n)
              (reflectedSchwartzSpacetime (d := d) (φ_seq n))) u *
              k2TimeParametricKernel (d := d) G
                (![(0 : SpacetimeDim d), u + ξ] : NPointDomain d 2)) :
    ∃ g : SpacetimeDim d → ℂ,
      (∀ᵐ ξ : SpacetimeDim d ∂volume,
        Filter.Tendsto
          (fun n =>
            (if hξ : 0 < ξ 0 then
              OS.S 2 (ZeroDiagonalSchwartz.ofClassical
                (twoPointProductLift (φ_seq n)
                  (SCV.translateSchwartz (-ξ)
                    (reflectedSchwartzSpacetime (d := d) (φ_seq n)))))
            else 0) * ((h : SchwartzSpacetime d) ξ))
          Filter.atTop
          (nhds (g ξ * ((h : SchwartzSpacetime d) ξ)))) ∧
      ((OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
          (d := d) OS χ₀) h =
        ∫ ξ : SpacetimeDim d, g ξ * ((h : SchwartzSpacetime d) ξ)) := by
  let g : SpacetimeDim d → ℂ := fun ξ =>
    if 0 < ξ 0 then
      k2TimeParametricKernel (d := d) G
        (![(0 : SpacetimeDim d), ξ] : NPointDomain d 2)
    else 0
  refine ⟨g, ?_, ?_⟩
  · refine Filter.Eventually.of_forall ?_
    intro ξ
    have hbase :=
      weighted_shell_pointwise_tendsto_commonZeroAnchor_of_descended_convolution_local
        (d := d) OS G hG_holo hG_diff
        φ_seq hφ_nonneg hφ_real hφ_int hφ_ball s hs h hmargin hshell_repr ξ
    dsimp [g]
    by_cases hξ : 0 < ξ 0
    · simpa [hξ] using hbase
    · have hzero : ((h : SchwartzSpacetime d) ξ) = 0 := by
        by_contra hh
        have hmem : ξ ∈ tsupport (((h : positiveTimeCompactSupportSubmodule d) :
          SchwartzSpacetime d) : SpacetimeDim d → ℂ) :=
          subset_tsupport _ (Function.mem_support.mpr hh)
        exact hξ (h.property.1 hmem)
      simpa [hξ, hzero] using hbase
  · simpa [g] using
      schwingerDifferencePositiveCLM_eq_integral_indicator_commonZeroAnchor_local
        (d := d) OS χ₀ hχ₀ G hG_euclid hG_diff h

end OSReconstruction
