import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.DampedNorm
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.OrbitBridge

noncomputable section

open Complex MeasureTheory Filter

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Direct OS VI.1 DCT closeout on a fixed positive-time strip.

Once the diagonal one-point matrix elements converge at time `2s`, the damping
layer supplies the uniform integrable majorant `C * ‖h ξ‖` for the original
translated product-shell boundary integrands on the strip `ξ₀ > 2s`. If the
same shell integrands also converge pointwise almost everywhere to `g ξ * h ξ`,
then the weighted shell integrals converge to the Schwinger target represented
by `g`. This packages the DCT bookkeeping behind the first live `K2VI1`
frontier `sorry`, leaving only the genuine fixed-strip convergence input. -/
theorem translatedProductShell_boundary_tendsto_of_tendsto_damped_diagonal_and_ae_pointwise_vi1DCT_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (χ₀ : SchwartzSpacetime d)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆
      {x : SpacetimeDim d | x 0 < 0})
    (h : positiveTimeCompactSupportSubmodule d)
    (s : ℝ)
    (hs : 0 < s)
    (hmargin : tsupport (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | s + s < ξ 0})
    (g : SpacetimeDim d → ℂ)
    {z : ℂ}
    (hdiag : Filter.Tendsto
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
      (nhds z))
    (hpointwise : ∀ᵐ ξ : SpacetimeDim d ∂volume,
      Filter.Tendsto
        (fun n =>
          (if 0 < ξ 0 then
            OS.S 2 (ZeroDiagonalSchwartz.ofClassical
              (twoPointProductLift (φ_seq n)
                (SCV.translateSchwartz (-ξ)
                  (reflectedSchwartzSpacetime (φ_seq n)))))
          else 0) * ((h : SchwartzSpacetime d) ξ))
        Filter.atTop
        (nhds (g ξ * ((h : SchwartzSpacetime d) ξ))))
    (htarget :
      (OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
        (d := d) OS χ₀) h =
        ∫ ξ : SpacetimeDim d, g ξ * ((h : SchwartzSpacetime d) ξ)) :
    Filter.Tendsto
      (fun n =>
        ∫ ξ : SpacetimeDim d,
          (if 0 < ξ 0 then
            OS.S 2 (ZeroDiagonalSchwartz.ofClassical
              (twoPointProductLift (φ_seq n)
                (SCV.translateSchwartz (-ξ)
                  (reflectedSchwartzSpacetime (φ_seq n)))))
          else 0) * ((h : SchwartzSpacetime d) ξ))
      Filter.atTop
      (nhds ((OsterwalderSchraderAxioms.schwingerDifferencePositiveCLM
        (d := d) OS χ₀) h)) := by
  let F : ℕ → SpacetimeDim d → ℂ := fun n ξ =>
    (if hξ : 0 < ξ 0 then
      OS.S 2 (ZeroDiagonalSchwartz.ofClassical
        (twoPointProductLift (φ_seq n)
          (SCV.translateSchwartz (-ξ)
            (reflectedSchwartzSpacetime (φ_seq n)))))
    else 0) * ((h : SchwartzSpacetime d) ξ)
  obtain ⟨C, hC_nonneg, hbound⟩ :=
    ae_norm_translatedProductShell_boundary_weight_le_of_tendsto_damped_diagonal_vi1DampedNorm_local
      (d := d) OS lgc φ_seq hφ_real hφ_compact hφ_neg h s hs hmargin hdiag
  have hF_meas : ∀ n, AEStronglyMeasurable (F n) volume := by
    intro n
    exact
      (integrable_translatedProductShell_boundary_weight_vi1Bridge_local
        (d := d) OS lgc (φ_seq n) (hφ_real n) (hφ_compact n) (hφ_neg n) h).aestronglyMeasurable
  have hdom_int : Integrable (fun ξ : SpacetimeDim d => C * ‖((h : SchwartzSpacetime d) ξ)‖) volume := by
    simpa using (((SchwartzMap.integrable (h : SchwartzSpacetime d)).norm).const_mul C)
  have hlim :
      Filter.Tendsto
        (fun n => ∫ ξ : SpacetimeDim d, F n ξ)
        Filter.atTop
        (nhds (∫ ξ : SpacetimeDim d, g ξ * ((h : SchwartzSpacetime d) ξ))) := by
    simpa [F] using
      (MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun ξ : SpacetimeDim d => C * ‖((h : SchwartzSpacetime d) ξ)‖)
        hF_meas hdom_int
        (fun n => by simpa [F] using hbound n)
        hpointwise)
  rw [htarget]
  simpa [F] using hlim

end OSReconstruction
