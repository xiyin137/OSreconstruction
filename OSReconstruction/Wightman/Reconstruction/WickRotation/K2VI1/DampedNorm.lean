import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.Damping

noncomputable section

open Complex MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- A convergent complex sequence is uniformly bounded in norm. This local copy
keeps the new VI.1 damping layer independent of the more global Banach-Steinhaus
infrastructure. -/
private theorem exists_uniform_norm_bound_of_tendsto_vi1DampedNorm_local
    {u : ℕ → ℂ} {z : ℂ}
    (hu : Filter.Tendsto u Filter.atTop (nhds z)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖u n‖ ≤ C := by
  have hbdd := hu.norm.isBoundedUnder_le
  obtain ⟨b, hb⟩ := hbdd
  simp only [Filter.Eventually, Filter.mem_map, Filter.mem_atTop_sets] at hb
  obtain ⟨N, hN⟩ := hb
  refine ⟨max 0 (max b (Finset.sup' (Finset.range (N + 1))
    ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun n => ‖u n‖))), le_max_left _ _, ?_⟩
  intro n
  by_cases hn : N ≤ n
  · exact le_trans (hN n hn) (le_max_of_le_right (le_max_left _ _))
  · push_neg at hn
    exact le_trans
      (Finset.le_sup' (fun k => ‖u k‖) (Finset.mem_range.mpr (by omega)))
      (le_max_of_le_right (le_max_of_le_right le_rfl))

/-- If the diagonal one-point OS semigroup matrix elements at time `2s`
converge, then the damped probes `T(s)x_n` are uniformly bounded. This is the
direct Hilbert-space reduction behind the DCT domination step on the original
VI.1 shell. -/
theorem exists_uniform_damped_bound_of_tendsto_diagonal_vi1DampedNorm_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (x_seq : ℕ → OSHilbertSpace OS)
    (s : ℝ)
    (hs : 0 < s)
    {z : ℂ}
    (hdiag : Filter.Tendsto
      (fun n =>
        osSemigroupGroupMatrixElement (d := d) OS lgc (x_seq n) (s + s) (0 : Fin d → ℝ))
      Filter.atTop
      (nhds z)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      2 * ‖(osTimeShiftHilbertComplex (d := d) OS lgc (s : ℂ)) (x_seq n)‖ ^ 2 ≤ C := by
  obtain ⟨B, hB_nonneg, hB⟩ :=
    exists_uniform_norm_bound_of_tendsto_vi1DampedNorm_local hdiag
  refine ⟨2 * B, by positivity, ?_⟩
  intro n
  let T : OSHilbertSpace OS →L[ℂ] OSHilbertSpace OS :=
    osTimeShiftHilbertComplex (d := d) OS lgc (s : ℂ)
  have hTsa : ContinuousLinearMap.adjoint T = T := by
    exact (osTimeShiftHilbertComplex_isSelfAdjoint (d := d) OS lgc s hs).adjoint_eq
  have hnormsq :
      ‖T (x_seq n)‖ ^ 2 ≤
        ‖osSemigroupGroupMatrixElement (d := d) OS lgc (x_seq n) (s + s) (0 : Fin d → ℝ)‖ := by
    have hinner :
        @inner ℂ (OSHilbertSpace OS) _
            (x_seq n)
            ((osTimeShiftHilbertComplex (d := d) OS lgc ((s + s : ℝ) : ℂ))
              (x_seq n)) =
          osSemigroupGroupMatrixElement (d := d) OS lgc (x_seq n) (s + s) (0 : Fin d → ℝ) := by
      simpa [osSpatialTranslateHilbert_zero] using
        (osSemigroupGroupMatrixElement_eq_inner_timeShift_right
          (d := d) OS lgc (x_seq n) (0 : Fin d → ℝ) (0 : Fin d → ℝ) (s + s) (add_pos hs hs)).symm
    calc
      ‖T (x_seq n)‖ ^ 2
          = RCLike.re (@inner ℂ (OSHilbertSpace OS) _
              (x_seq n) (((ContinuousLinearMap.adjoint T).comp T) (x_seq n))) := by
              simpa using ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right T (x_seq n)
      _ = RCLike.re (@inner ℂ (OSHilbertSpace OS) _
            (x_seq n)
            ((osTimeShiftHilbertComplex (d := d) OS lgc ((s + s : ℝ) : ℂ))
              (x_seq n))) := by
              rw [hTsa, osTimeShiftHilbertComplex_comp (d := d) OS lgc s s hs hs]
      _ ≤ ‖@inner ℂ (OSHilbertSpace OS) _
            (x_seq n)
            ((osTimeShiftHilbertComplex (d := d) OS lgc ((s + s : ℝ) : ℂ))
              (x_seq n))‖ := by
              exact RCLike.re_le_norm _
      _ = ‖osSemigroupGroupMatrixElement (d := d) OS lgc (x_seq n) (s + s) (0 : Fin d → ℝ)‖ := by
              rw [hinner]
  calc
    2 * ‖(osTimeShiftHilbertComplex (d := d) OS lgc (s : ℂ)) (x_seq n)‖ ^ 2
        ≤ 2 * B := by
            exact mul_le_mul_of_nonneg_left (le_trans hnormsq (hB n)) (by positivity)
    _ = (2 * B) := rfl

/-- A convergent fixed-strip diagonal sequence is enough to trigger the direct
OS damping domination theorem for the original VI.1 shell. This packages the
DCT majorant step so the remaining blocker is only the actual pointwise/diagonal
convergence theorem. -/
theorem ae_norm_translatedProductShell_boundary_weight_le_of_tendsto_damped_diagonal_vi1DampedNorm_local
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (φ_seq : ℕ → SchwartzSpacetime d)
    (hφ_real : ∀ n x, (φ_seq n x).im = 0)
    (hφ_compact : ∀ n, HasCompactSupport (φ_seq n : SpacetimeDim d → ℂ))
    (hφ_neg : ∀ n, tsupport (φ_seq n : SpacetimeDim d → ℂ) ⊆ {x | x 0 < 0})
    (h : positiveTimeCompactSupportSubmodule d)
    (s : ℝ)
    (hs : 0 < s)
    (hmargin : tsupport (((h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ) ⊆ {ξ : SpacetimeDim d | s + s < ξ 0})
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
      (nhds z)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      ∀ᵐ ξ : SpacetimeDim d ∂volume,
        ‖((if _hξ : 0 < ξ 0 then
            OS.S 2 (ZeroDiagonalSchwartz.ofClassical
              (twoPointProductLift (φ_seq n)
                (SCV.translateSchwartz (-ξ)
                  (reflectedSchwartzSpacetime (φ_seq n)))))
          else 0) * ((h : SchwartzSpacetime d) ξ))‖ ≤
            C * ‖((h : SchwartzSpacetime d) ξ)‖ := by
  let x_seq : ℕ → OSHilbertSpace OS := fun n =>
    (((show OSPreHilbertSpace OS from
        (⟦PositiveTimeBorchersSequence.single 1
            (SchwartzNPoint.osConj (d := d) (n := 1)
              (onePointToFin1CLM d (φ_seq n) : SchwartzNPoint d 1))
            (osConj_onePointToFin1_tsupport_orderedPositiveTime_local
              (d := d) (φ_seq n) (hφ_compact n) (hφ_neg n))⟧)) :
        OSHilbertSpace OS))
  obtain ⟨C, hC_nonneg, hC⟩ :=
    exists_uniform_damped_bound_of_tendsto_diagonal_vi1DampedNorm_local
      (d := d) OS lgc x_seq s hs hdiag
  refine ⟨C, hC_nonneg, ?_⟩
  intro n
  have hdamp_n :
      2 * ‖(osTimeShiftHilbertComplex (d := d) OS lgc (s : ℂ)) (x_seq n)‖ ^ 2 ≤ C := hC n
  simpa [x_seq] using
    ae_norm_translatedProductShell_boundary_weight_le_of_uniform_damped_bound_vi1Damping_local
      (d := d) OS lgc φ_seq hφ_real hφ_compact hφ_neg h s C hs hmargin
      (fun n => by simpa [x_seq] using hC n) n

end OSReconstruction
