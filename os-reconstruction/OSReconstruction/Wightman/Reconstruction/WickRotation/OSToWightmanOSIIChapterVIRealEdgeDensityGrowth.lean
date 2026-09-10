/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRealEdgeRegularizedGrowth
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIMixedSpatialCoordinates
import OSReconstruction.SCV.DistributionalEOWKernel














noncomputable section

open Complex MeasureTheory Set
open scoped Classical

namespace OSReconstruction

/-- A polynomially bounded continuous density acts on Schwartz tests with one
finite seminorm family and one constant depending only on the dimension and
the polynomial degree. -/
theorem exists_polynomialGrowth_integral_schwartz_bound
    (m N : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ K : ℝ, 0 < K ∧
      ∀ (F : (Fin m → ℝ) → ℂ), Continuous F →
        ∀ (A : ℝ), 0 ≤ A →
          (∀ x : Fin m → ℝ, ‖F x‖ ≤ A * (1 + ‖x‖) ^ N) →
          ∀ phi : SchwartzMap (Fin m → ℝ) ℂ,
            ‖∫ x : Fin m → ℝ, F x * phi x‖ ≤
              A * K *
                s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ) phi := by
  let n : ℕ := (volume : Measure (Fin m → ℝ)).integrablePower
  let s : Finset (ℕ × ℕ) := Finset.Iic (N + n, 0)
  let decay : (Fin m → ℝ) → ℝ := fun x =>
    (1 + ‖x‖) ^ (-(n : ℝ))
  have hdecay_integrable : Integrable decay := by
    simpa [decay, n] using
      (MeasureTheory.Measure.integrable_pow_neg_integrablePower
        (μ := (volume : Measure (Fin m → ℝ))))
  let J : ℝ := ∫ x : Fin m → ℝ, decay x
  have hJ_nonneg : 0 ≤ J := by
    dsimp [J]
    exact integral_nonneg fun x => Real.rpow_nonneg (by positivity) _
  let K : ℝ := 2 ^ (N + n) * (1 + J)
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨s, K, hK, ?_⟩
  intro F hF A hA hgrowth phi
  let sem : ℝ :=
    s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ) phi
  have hsem : 0 ≤ sem := apply_nonneg _ _
  have hpointwise :
      ∀ x : Fin m → ℝ,
        ‖F x * phi x‖ ≤
          decay x * (A * (2 ^ (N + n) * sem)) := by
    intro x
    have hsch :
        (1 + ‖x‖) ^ (N + n) * ‖phi x‖ ≤
          2 ^ (N + n) * sem := by
      simpa [s, sem] using
        (SchwartzMap.one_add_le_sup_seminorm_apply
          (𝕜 := ℂ) (m := (N + n, 0)) (k := N + n) (n := 0)
          le_rfl le_rfl phi x)
    have hphi_decay :
        (1 + ‖x‖) ^ N * ‖phi x‖ ≤
          decay x * (2 ^ (N + n) * sem) := by
      rw [show decay x = (1 + ‖x‖) ^ (-(n : ℝ)) by rfl]
      rw [Real.rpow_neg (by positivity), ← div_eq_inv_mul,
        le_div_iff₀' (by positivity), Real.rpow_natCast]
      simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using hsch
    rw [Complex.norm_mul]
    calc
      ‖F x‖ * ‖phi x‖ ≤
          (A * (1 + ‖x‖) ^ N) * ‖phi x‖ := by
        gcongr
        exact hgrowth x
      _ = A * ((1 + ‖x‖) ^ N * ‖phi x‖) := by ring
      _ ≤ A * (decay x * (2 ^ (N + n) * sem)) := by
        exact mul_le_mul_of_nonneg_left hphi_decay hA
      _ = decay x * (A * (2 ^ (N + n) * sem)) := by ring
  have hdom : Integrable (fun x : Fin m → ℝ =>
      decay x * (A * (2 ^ (N + n) * sem))) :=
    hdecay_integrable.mul_const _
  calc
    ‖∫ x : Fin m → ℝ, F x * phi x‖ ≤
        ∫ x : Fin m → ℝ,
          decay x * (A * (2 ^ (N + n) * sem)) := by
      exact MeasureTheory.norm_integral_le_of_norm_le
        hdom (Filter.Eventually.of_forall hpointwise)
    _ = A * (2 ^ (N + n) * J) * sem := by
      rw [integral_mul_const]
      dsimp [J]
      ring
    _ ≤ A * K * sem := by
      apply mul_le_mul_of_nonneg_right _ hsem
      apply mul_le_mul_of_nonneg_left _ hA
      dsimp [K]
      have hpow : 0 ≤ (2 : ℝ) ^ (N + n) := pow_nonneg (by norm_num) _
      nlinarith

/-- The mixed real spacetime center is controlled by the norm of its complex
time point plus the free spatial center. -/
theorem osiiStep4MixedSpatialRealPoint_norm_le
    (d k : ℕ)
    (tau : Fin k → ℝ)
    (x : Fin (k * d) → ℝ) :
    ‖osiiStep4MixedSpatialRealPoint d k tau x‖ ≤
      ‖osiiPositiveRealTimeEmbed tau‖ + ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg
    (add_nonneg (norm_nonneg _) (norm_nonneg _))).2
  intro q
  obtain ⟨⟨i, mu⟩, rfl⟩ := finProdFinEquiv.surjective q
  cases mu using Fin.cases with
  | zero =>
      have ht : ‖tau i‖ ≤ ‖osiiPositiveRealTimeEmbed tau‖ := by
        simpa [osiiPositiveRealTimeEmbed, Real.norm_eq_abs] using
          (norm_le_pi_norm (osiiPositiveRealTimeEmbed tau) i)
      simpa [osiiStep4MixedSpatialRealPoint] using
        ht.trans (le_add_of_nonneg_right (norm_nonneg x))
  | succ j =>
      simpa [osiiStep4MixedSpatialRealPoint] using
        (norm_le_pi_norm x (finProdFinEquiv (i, j))).trans
          (le_add_of_nonneg_left
            (norm_nonneg (osiiPositiveRealTimeEmbed tau)))

/-- Polynomial center growth separates into the positive-time point and the
free spatial variable. -/
theorem osiiStep4MixedSpatialRealPoint_one_add_norm_pow_le
    (d k N : ℕ)
    (tau : Fin k → ℝ)
    (x : Fin (k * d) → ℝ) :
    (1 + ‖osiiStep4MixedSpatialRealPoint d k tau x‖) ^ N ≤
      (1 + ‖osiiPositiveRealTimeEmbed tau‖) ^ N *
        (1 + ‖x‖) ^ N := by
  have hsum := osiiStep4MixedSpatialRealPoint_norm_le d k tau x
  have hfactor :
      1 + ‖osiiPositiveRealTimeEmbed tau‖ + ‖x‖ ≤
        (1 + ‖osiiPositiveRealTimeEmbed tau‖) * (1 + ‖x‖) := by
    nlinarith [norm_nonneg (osiiPositiveRealTimeEmbed tau), norm_nonneg x,
      mul_nonneg (norm_nonneg (osiiPositiveRealTimeEmbed tau)) (norm_nonneg x)]
  calc
    (1 + ‖osiiStep4MixedSpatialRealPoint d k tau x‖) ^ N ≤
        (1 + ‖osiiPositiveRealTimeEmbed tau‖ + ‖x‖) ^ N := by
      exact pow_le_pow_left₀ (by positivity) (by linarith) N
    _ ≤ ((1 + ‖osiiPositiveRealTimeEmbed tau‖) *
          (1 + ‖x‖)) ^ N :=
      pow_le_pow_left₀ (by positivity) hfactor N
    _ = (1 + ‖osiiPositiveRealTimeEmbed tau‖) ^ N *
        (1 + ‖x‖) ^ N := by rw [mul_pow]

/-- The exact non-circular VI.1 density contract.  The density is written in
flat spatial coordinates, while `represents` ties it to the native exhausted
Chapter V spatial distribution. -/
structure OSIITimeContinuationLadderRealEdgeDensityGrowthData
    {d k : ℕ}
    (L : OSIITimeContinuationLadder d k) where
  arity_pos : 0 < k
  density : (Fin k → ℝ) → (Fin (k * d) → ℝ) → ℂ
  density_continuous :
    ∀ tau,
      tau ∈ section43TimeStrictPositiveRegion k →
        Continuous (density tau)
  represents :
    ∀ tau,
      tau ∈ section43TimeStrictPositiveRegion k →
        ∀ chi : SchwartzMap (Section43SpatialSpace d k) ℂ,
          L.fullDistribution (osiiPositiveRealTimeEmbed tau) chi =
            ∫ x : Fin (k * d) → ℝ,
              density tau x * (section43SpatialFlatSchwartzCLE d k chi) x
  constant : ℝ
  timeDegree : ℕ
  boundaryDegree : ℕ
  spatialDegree : ℕ
  constant_pos : 0 < constant
  pointwise_bound :
    ∀ tau,
      tau ∈ section43TimeStrictPositiveRegion k →
        ∀ x : Fin (k * d) → ℝ,
          ‖density tau x‖ ≤
            constant *
              (1 + ‖osiiPositiveRealTimeEmbed tau‖) ^ timeDegree *
              (1 + (osiiTimeBoundaryDistance k
                (osiiPositiveRealTimeEmbed tau))⁻¹) ^ boundaryDegree *
              (1 + ‖x‖) ^ spatialDegree

namespace OSIITimeContinuationLadderRealEdgeDensityGrowthData

variable {d k : ℕ}
variable {L : OSIITimeContinuationLadder d k}

end OSIITimeContinuationLadderRealEdgeDensityGrowthData

end OSReconstruction
