import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.RegularizationSeminorm
import OSReconstruction.Wightman.Reconstruction.WickRotation.K2VI1.Bounds

noncomputable section

open MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Public one-point positive-time support bridge for the new small VI.1 orbit
bound layer. -/
private theorem onePointToFin1_tsupport_orderedPositiveTime_vi1RegularizedOrbit_local
    (f : SchwartzSpacetime d)
    (hf : tsupport (f : SpacetimeDim d → ℂ) ⊆ {x : SpacetimeDim d | 0 < x 0}) :
    tsupport (((onePointToFin1CLM d f : SchwartzNPoint d 1) :
      NPointDomain d 1 → ℂ)) ⊆ OrderedPositiveTimeRegion d 1 := by
  intro v hv i
  refine ⟨?_, fun j hij => absurd hij (by omega)⟩
  rw [Fin.eq_zero i]
  have hv0 : v 0 ∈ tsupport (f : SpacetimeDim d → ℂ) := by
    exact
      tsupport_comp_subset_preimage (f : SpacetimeDim d → ℂ)
        (f := fun w : Fin 1 → SpacetimeDim d => w 0) (continuous_apply 0) hv
  exact Set.mem_setOf.mp (hf hv0)

private theorem norm_funUnique_apply_eq_vi1RegularizedOrbit_local
    (x : Fin 1 → SpacetimeDim d) :
    ‖(ContinuousLinearEquiv.funUnique (Fin 1) ℝ (SpacetimeDim d)) x‖ = ‖x‖ := by
  have hx : x = fun _ : Fin 1 => x 0 := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
  simpa using (pi_norm_const' (ι := Fin 1) (a := x 0)).symm

/-- The `Fin 1` lift of a spacetime Schwartz function does not enlarge any
Schwartz seminorm. This is the transport lemma needed to feed the new
regularization bounds into the one-point OS Hilbert estimates. -/
private theorem onePointToFin1_seminorm_le_vi1RegularizedOrbit_local
    (f : SchwartzSpacetime d) (N j : ℕ) :
    SchwartzMap.seminorm ℝ N j (onePointToFin1CLM d f : SchwartzNPoint d 1) ≤
      SchwartzMap.seminorm ℝ N j f := by
  let e : (Fin 1 → SpacetimeDim d) ≃L[ℝ] SpacetimeDim d :=
    ContinuousLinearEquiv.funUnique (Fin 1) ℝ (SpacetimeDim d)
  have he_norm_le : ‖(e : (Fin 1 → SpacetimeDim d) →L[ℝ] SpacetimeDim d)‖ ≤ 1 := by
    rw [ContinuousLinearMap.opNorm_le_iff]
    · intro x
      simpa [one_mul] using
        le_of_eq (norm_funUnique_apply_eq_vi1RegularizedOrbit_local (d := d) x)
    · positivity
  refine
    SchwartzMap.seminorm_le_bound ℝ N j (onePointToFin1CLM d f : SchwartzNPoint d 1)
      (by positivity) ?_
  intro x
  have hiter :
      iteratedFDeriv ℝ j
          ((onePointToFin1CLM d f : SchwartzNPoint d 1) :
            (Fin 1 → SpacetimeDim d) → ℂ) x =
        (iteratedFDeriv ℝ j (f : SpacetimeDim d → ℂ) (e x)).compContinuousLinearMap
          (fun _ : Fin j => (e : (Fin 1 → SpacetimeDim d) →L[ℝ] SpacetimeDim d)) := by
    simpa [onePointToFin1CLM, e] using
      (e.toContinuousLinearMap.iteratedFDeriv_comp_right
        (f := (f : SpacetimeDim d → ℂ)) f.smooth' (x := x) (i := j)
        (by exact_mod_cast le_top))
  rw [hiter]
  have hprod_le :
      ∏ _ : Fin j, ‖(e : (Fin 1 → SpacetimeDim d) →L[ℝ] SpacetimeDim d)‖ ≤ 1 := by
    simpa [Finset.prod_const] using
      Finset.prod_le_one (s := (Finset.univ : Finset (Fin j)))
        (fun _ _ => norm_nonneg _)
        (fun _ _ => he_norm_le)
  calc
    ‖x‖ ^ N *
        ‖(iteratedFDeriv ℝ j (f : SpacetimeDim d → ℂ) (e x)).compContinuousLinearMap
            (fun _ => (e : (Fin 1 → SpacetimeDim d) →L[ℝ] SpacetimeDim d))‖
      ≤ ‖x‖ ^ N *
          (‖iteratedFDeriv ℝ j (f : SpacetimeDim d → ℂ) (e x)‖ *
            ∏ _ : Fin j, ‖(e : (Fin 1 → SpacetimeDim d) →L[ℝ] SpacetimeDim d)‖) := by
          gcongr
          exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖x‖ ^ N * ‖iteratedFDeriv ℝ j (f : SpacetimeDim d → ℂ) (e x)‖ := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (norm_nonneg x) _)
          have hnonneg : 0 ≤ ‖iteratedFDeriv ℝ j (f : SpacetimeDim d → ℂ) (e x)‖ :=
            norm_nonneg _
          calc
            ‖iteratedFDeriv ℝ j (f : SpacetimeDim d → ℂ) (e x)‖ *
                ∏ _ : Fin j, ‖(e : (Fin 1 → SpacetimeDim d) →L[ℝ] SpacetimeDim d)‖
              ≤ ‖iteratedFDeriv ℝ j (f : SpacetimeDim d → ℂ) (e x)‖ * 1 := by
                  exact mul_le_mul_of_nonneg_left hprod_le hnonneg
            _ = ‖iteratedFDeriv ℝ j (f : SpacetimeDim d → ℂ) (e x)‖ := by ring
    _ = ‖e x‖ ^ N * ‖iteratedFDeriv ℝ j (f : SpacetimeDim d → ℂ) (e x)‖ := by
          rw [norm_funUnique_apply_eq_vi1RegularizedOrbit_local (d := d) x]
    _ ≤ SchwartzMap.seminorm ℝ N j f := by
          exact SchwartzMap.le_seminorm ℝ N j f (e x)

/-- Uniform OS-pre-Hilbert diagonal bound for the reflected positive-time
convolution regularization family, transported through the one-point lift. This
is the first direct `lgc`-input consumer behind the next VI.1 mean-value step. -/
theorem onePointToFin1_reflected_negativeApproxIdentity_convolution_seminorm_uniform_local
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
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      let ψn : positiveTimeCompactSupportSubmodule d :=
        positiveTimeCompactSupportConvolution
          (⟨reflectedSchwartzSpacetime (φ_seq n),
            ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
              reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
                (hφ_compact n)⟩⟩)
          h
      SchwartzMap.seminorm ℝ N j
        (onePointToFin1CLM d (ψn : SchwartzSpacetime d) : SchwartzNPoint d 1) ≤ C := by
  rcases
      positiveTimeCompactSupportConvolution_reflected_negativeApproxIdentity_seminorm_uniform_local
        (d := d) φ_seq hφ_nonneg hφ_real hφ_int hφ_compact hφ_neg hφ_ball N j h with
    ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro n
  exact
    (onePointToFin1_seminorm_le_vi1RegularizedOrbit_local
      (d := d)
      (((positiveTimeCompactSupportConvolution
          (⟨reflectedSchwartzSpacetime (φ_seq n),
            ⟨reflectedSchwartzSpacetime_tsupport_pos (d := d) (φ_seq n) (hφ_neg n),
              reflectedSchwartzSpacetime_hasCompactSupport (d := d) (φ_seq n)
                (hφ_compact n)⟩⟩)
          h : positiveTimeCompactSupportSubmodule d) : SchwartzSpacetime d)) N j).trans
      (hC n)

end OSReconstruction
