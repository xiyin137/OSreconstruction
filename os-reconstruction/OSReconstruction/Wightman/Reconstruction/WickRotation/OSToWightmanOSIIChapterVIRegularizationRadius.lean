/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIGrowthBoundaryHandoff










noncomputable section

open Complex Set

namespace OSReconstruction

/-- The Chapter VI Step-4 radius at a complex time-gap point. -/
def osiiChapterVIRegularizationRadius
    (k : ℕ) (ζ : Fin k → ℂ) : ℝ :=
  min 16 (osiiTimeBoundaryDistance k ζ)

/-- For positive arity, the complement of the strict positive time cone is
nonempty. -/
theorem osiiTimePositiveCone_compl_nonempty
    {k : ℕ} (hk : 0 < k) :
    (osiiTimePositiveCone k)ᶜ.Nonempty := by
  refine ⟨0, ?_⟩
  intro hzero
  have hcoord := hzero (⟨0, hk⟩ : Fin k)
  simp at hcoord

/-- A point in the product right half-plane has positive distance from the
boundary of the strict positive real time cone. -/
theorem osiiTimeBoundaryDistance_pos
    {k : ℕ} (hk : 0 < k)
    {ζ : Fin k → ℂ} (hζ : ζ ∈ osiiTimeRightHalfPlane k) :
    0 < osiiTimeBoundaryDistance k ζ := by
  apply
    ((osiiTimePositiveCone_open k).isClosed_compl
      |>.notMem_iff_infDist_pos
        (osiiTimePositiveCone_compl_nonempty hk)).1
  simpa [osiiTimeBoundaryDistance, osiiTimePositiveCone,
    osiiTimeRightHalfPlane, section43TimeStrictPositiveRegion] using hζ

/-- The canonical Chapter VI regularization radius is positive in the
physical right half-plane. -/
theorem osiiChapterVIRegularizationRadius_pos
    {k : ℕ} (hk : 0 < k)
    {ζ : Fin k → ℂ} (hζ : ζ ∈ osiiTimeRightHalfPlane k) :
    0 < osiiChapterVIRegularizationRadius k ζ := by
  exact lt_min (by norm_num) (osiiTimeBoundaryDistance_pos hk hζ)

/-- The canonical radius stays below the reference scale used by the exact
regularizer dilation formula. -/
theorem osiiChapterVIRegularizationRadius_le_sixteen
    (k : ℕ) (ζ : Fin k → ℂ) :
    osiiChapterVIRegularizationRadius k ζ ≤ 16 :=
  min_le_left _ _

/-- The canonical radius stays below the distance to the time-cone boundary. -/
theorem osiiChapterVIRegularizationRadius_le_boundaryDistance
    (k : ℕ) (ζ : Fin k → ℂ) :
    osiiChapterVIRegularizationRadius k ζ ≤
      osiiTimeBoundaryDistance k ζ :=
  min_le_right _ _

/-- The distance from a right-half-plane point to the boundary of the strict
positive time cone is no larger than any of its real time-gap coordinates. -/
theorem osiiTimeBoundaryDistance_le_re
    {k : ℕ} {ζ : Fin k → ℂ}
    (hζ : ζ ∈ osiiTimeRightHalfPlane k)
    (i : Fin k) :
    osiiTimeBoundaryDistance k ζ ≤ (ζ i).re := by
  let x : Fin k → ℝ := fun j => (ζ j).re
  let boundary : Fin k → ℝ := Function.update x i 0
  have hboundary : boundary ∈ (osiiTimePositiveCone k)ᶜ := by
    intro hpositive
    have hi := hpositive i
    simp [boundary] at hi
  have hdist : dist x boundary ≤ (ζ i).re := by
    have hrei : 0 ≤ (ζ i).re := (hζ i).le
    rw [dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg hrei).2
    intro j
    by_cases hji : j = i
    · subst j
      simp [x, boundary, abs_of_nonneg hrei]
    · simp [x, boundary, hji, hrei]
  exact (Metric.infDist_le_dist_of_mem hboundary).trans hdist

/-- The canonical radius is no larger than any positive real time-gap
coordinate. -/
theorem osiiChapterVIRegularizationRadius_le_re
    {k : ℕ} {ζ : Fin k → ℂ}
    (hζ : ζ ∈ osiiTimeRightHalfPlane k)
    (i : Fin k) :
    osiiChapterVIRegularizationRadius k ζ ≤ (ζ i).re := by
  calc
    osiiChapterVIRegularizationRadius k ζ ≤
        osiiTimeBoundaryDistance k ζ :=
      osiiChapterVIRegularizationRadius_le_boundaryDistance k ζ
    _ ≤ (ζ i).re := osiiTimeBoundaryDistance_le_re hζ i

/-- The inverse canonical radius is controlled by the standard Chapter VI
inverse-boundary-distance factor. -/
theorem osiiChapterVIRegularizationRadius_ratio_le
    {k : ℕ} (hk : 0 < k)
    {ζ : Fin k → ℂ} (hζ : ζ ∈ osiiTimeRightHalfPlane k) :
    16 / osiiChapterVIRegularizationRadius k ζ ≤
      16 * (1 + (osiiTimeBoundaryDistance k ζ)⁻¹) := by
  let δ := osiiTimeBoundaryDistance k ζ
  have hδ_pos : 0 < δ := by
    simpa [δ] using osiiTimeBoundaryDistance_pos hk hζ
  by_cases h : (16 : ℝ) ≤ δ
  · rw [osiiChapterVIRegularizationRadius, min_eq_left h]
    have hinv_nonneg : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ_pos.le
    norm_num
    nlinarith
  · have hδ_le : δ ≤ (16 : ℝ) := le_of_not_ge h
    rw [osiiChapterVIRegularizationRadius, min_eq_right hδ_le,
      div_eq_mul_inv]
    have hinv_nonneg : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ_pos.le
    nlinarith

/-- Power form of the inverse-radius to inverse-boundary-distance comparison. -/
theorem osiiChapterVIRegularizationRadius_ratio_pow_le
    {k : ℕ} (hk : 0 < k)
    {ζ : Fin k → ℂ} (hζ : ζ ∈ osiiTimeRightHalfPlane k)
    (M : ℕ) :
    (16 / osiiChapterVIRegularizationRadius k ζ) ^ M ≤
      16 ^ M * (1 + (osiiTimeBoundaryDistance k ζ)⁻¹) ^ M := by
  have hbase_nonneg :
      0 ≤ 16 / osiiChapterVIRegularizationRadius k ζ := by
    exact div_nonneg (by norm_num)
      (osiiChapterVIRegularizationRadius_pos hk hζ).le
  simpa [mul_pow] using
    pow_le_pow_left₀ hbase_nonneg
      (osiiChapterVIRegularizationRadius_ratio_le hk hζ) M

end OSReconstruction
