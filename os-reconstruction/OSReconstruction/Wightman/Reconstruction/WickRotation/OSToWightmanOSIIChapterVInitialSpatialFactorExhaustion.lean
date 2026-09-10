/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialSpatialSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceSpatialDensity















noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d] [NeZero k]

/-- A compactly supported flat Schwartz function is fixed exactly by all
sufficiently large standard radial bump truncations. -/
theorem eventually_bumpTruncationRadius_eq_of_hasCompactSupport
    {m : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hf : HasCompactSupport (f : (Fin m → ℝ) → ℂ)) :
    ∀ᶠ N : ℕ in atTop, bumpTruncationRadius f N = f := by
  obtain ⟨R, hR⟩ :=
    hf.isCompact.isBounded.subset_closedBall
      (0 : Fin m → ℝ)
  obtain ⟨N₀, hRN₀⟩ := exists_nat_ge R
  refine Filter.eventually_atTop.2 ⟨N₀, ?_⟩
  intro N hN
  have hRN : R ≤ (N : ℝ) :=
    hRN₀.trans (by exact_mod_cast hN)
  have hN_radius :
      (N : ℝ) ≤ bumpTruncationRadiusValue N := by
    simp only [bumpTruncationRadiusValue]
    linarith
  ext x
  rw [bumpTruncationRadius]
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (unitBallBumpSchwartzPiRadius
      m (bumpTruncationRadiusValue N)
      (bumpTruncationRadiusValue_pos N)).hasTemperateGrowth]
  by_cases hx : x ∈ tsupport (f : (Fin m → ℝ) → ℂ)
  · have hxR :
        x ∈ Metric.closedBall (0 : Fin m → ℝ) R :=
      hR hx
    have hxnorm : ‖x‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hxR
    have hball :
        x ∈ Metric.closedBall
          (0 : Fin m → ℝ)
          (bumpTruncationRadiusValue N) := by
      simpa [Metric.mem_closedBall, dist_zero_right] using
        hxnorm.trans (hRN.trans hN_radius)
    have hbump :
        unitBallBumpSchwartzPiRadius
            m (bumpTruncationRadiusValue N)
            (bumpTruncationRadiusValue_pos N) x =
          1 :=
      unitBallBumpSchwartzPiRadius_one_of_mem_closedBall
        (bumpTruncationRadiusValue_pos N) hball
    simp [hbump, smul_eq_mul]
  · have hzero : f x = 0 :=
      image_eq_zero_of_notMem_tsupport hx
    simp [hzero, smul_eq_mul]

/-- Standard radial truncation transported to the reduced spatial block. -/
noncomputable def initialSpatialFactorTruncationCLM
    (d k N : ℕ) :
    SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
      SchwartzMap (Section43SpatialSpace d k) ℂ :=
  (section43SpatialFlatSchwartzCLE d k).symm.toContinuousLinearMap.comp
    ((SchwartzMap.smulLeftCLM ℂ
      (unitBallBumpSchwartzPiRadius
        (k * d) (bumpTruncationRadiusValue N)
        (bumpTruncationRadiusValue_pos N))).comp
      (section43SpatialFlatSchwartzCLE d k).toContinuousLinearMap)

@[simp] theorem initialSpatialFactorTruncationCLM_apply
    (N : ℕ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    initialSpatialFactorTruncationCLM d k N χ =
      (section43SpatialFlatSchwartzCLE d k).symm
        (bumpTruncationRadius
          (section43SpatialFlatSchwartzCLE d k χ) N) := by
  rfl

/-- Spatial-factor truncations converge in the reduced spatial Schwartz
topology. -/
theorem initialSpatialFactorTruncation_tendsto
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    Tendsto
      (fun N : ℕ => initialSpatialFactorTruncationCLM d k N χ)
      atTop (nhds χ) := by
  have hflat :=
    SchwartzMap.tendsto_bump_truncation_nhds
      (section43SpatialFlatSchwartzCLE d k χ)
  have htransport :=
    ((section43SpatialFlatSchwartzCLE d k).symm.continuous.tendsto
      (section43SpatialFlatSchwartzCLE d k χ)).comp hflat
  simpa only [initialSpatialFactorTruncationCLM_apply,
    (section43SpatialFlatSchwartzCLE d k).symm_apply_apply] using
    htransport

/-- A compactly supported reduced spatial test is eventually fixed exactly
by the spatial-factor truncation. -/
theorem eventually_initialSpatialFactorTruncation_eq
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (hχ :
      HasCompactSupport
        (χ : Section43SpatialSpace d k → ℂ)) :
    ∀ᶠ N : ℕ in atTop,
      initialSpatialFactorTruncationCLM d k N χ = χ := by
  have hflat :
      HasCompactSupport
        ((section43SpatialFlatSchwartzCLE d k χ :
          SchwartzMap (Fin (k * d) → ℝ) ℂ) :
            (Fin (k * d) → ℝ) → ℂ) := by
    simpa [section43SpatialFlatSchwartzCLE_apply] using
      hχ.comp_homeomorph
        (section43SpatialFlatCLE d k).symm.toHomeomorph
  filter_upwards [
    eventually_bumpTruncationRadius_eq_of_hasCompactSupport
      (section43SpatialFlatSchwartzCLE d k χ) hflat] with N hN
  rw [initialSpatialFactorTruncationCLM_apply, hN]
  exact (section43SpatialFlatSchwartzCLE d k).symm_apply_apply χ

/-- The compact initial source obtained by truncating only its reduced
spatial factor. -/
noncomputable def initialReducedSpatialFactorCompactSourceCLM
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (N : ℕ) :
    SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
      SchwartzNPoint d (k + 1) :=
  (initialReducedSpatialFullSourceCLM (d := d) φ).comp
    (initialSpatialFactorTruncationCLM d k N)

@[simp] theorem initialReducedSpatialFactorCompactSourceCLM_apply
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (N : ℕ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    initialReducedSpatialFactorCompactSourceCLM (d := d) φ N χ =
      initialReducedSpatialFullSourceCLM (d := d) φ
        (initialSpatialFactorTruncationCLM d k N χ) :=
  rfl

/-- Spatial-factor compact sources converge to the canonical initial full
source in Schwartz topology. -/
theorem initialReducedSpatialFactorCompactSource_tendsto
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    Tendsto
      (fun N : ℕ =>
        initialReducedSpatialFactorCompactSourceCLM
          (d := d) φ N χ)
      atTop
      (nhds
        (initialReducedSpatialFullSourceCLM (d := d) φ χ)) := by
  exact
    ((initialReducedSpatialFullSourceCLM
      (d := d) φ).continuous.tendsto χ).comp
      (initialSpatialFactorTruncation_tendsto
        (d := d) (k := k) χ)

/-- On compactly supported spatial tests, the factorwise compact source is
eventually exactly the canonical full source. -/
theorem eventually_initialReducedSpatialFactorCompactSource_eq
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (hχ :
      HasCompactSupport
        (χ : Section43SpatialSpace d k → ℂ)) :
    ∀ᶠ N : ℕ in atTop,
      initialReducedSpatialFactorCompactSourceCLM
          (d := d) φ N χ =
        initialReducedSpatialFullSourceCLM (d := d) φ χ := by
  filter_upwards [
    eventually_initialSpatialFactorTruncation_eq
      (d := d) (k := k) χ hχ] with N hN
  simp [initialReducedSpatialFactorCompactSourceCLM_apply, hN]

end OSIIChapterV
end OSReconstruction
