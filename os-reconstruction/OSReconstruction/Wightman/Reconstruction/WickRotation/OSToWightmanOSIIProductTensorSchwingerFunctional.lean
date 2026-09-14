/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSchwingerSourceCurrent
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSourceCurrent
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIA0LocalSchwinger
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceOrderedDensity
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTotalTimePushforward
import OSReconstruction.SCV.EuclideanWeylOpen












noncomputable section

open Complex Topology MeasureTheory
open scoped Classical NNReal BigOperators

namespace OSReconstruction

variable {d : ℕ}

/-- Subtracting a common Euclidean time shift changes only the first
difference-time coordinate. -/
theorem section43DiffCoordRealCLE_sub_timeShiftVec_time
    {n : ℕ} (x : NPointDomain d n) (t : ℝ) (i : Fin n) :
    section43DiffCoordRealCLE d n (fun j => x j - timeShiftVec d t) i 0 =
      if i.val = 0 then section43DiffCoordRealCLE d n x i 0 - t
      else section43DiffCoordRealCLE d n x i 0 := by
  rw [section43DiffCoordRealCLE_apply, section43DiffCoordRealCLE_apply]
  by_cases hi : i.val = 0
  · simp [hi, timeShiftVec]
  · simp [hi, timeShiftVec]

/-- Common Euclidean time shifts do not change spatial difference
coordinates. -/
theorem section43DiffCoordRealCLE_sub_timeShiftVec_spatial
    {n : ℕ} (x : NPointDomain d n) (t : ℝ)
    (i : Fin n) {μ : Fin (d + 1)} (hμ : μ ≠ 0) :
    section43DiffCoordRealCLE d n (fun j => x j - timeShiftVec d t) i μ =
      section43DiffCoordRealCLE d n x i μ := by
  rw [section43DiffCoordRealCLE_apply, section43DiffCoordRealCLE_apply]
  by_cases hi : i.val = 0
  · simp [hi, timeShiftVec, hμ]
  · simp [hi, timeShiftVec, hμ]

variable [NeZero d]

/-- A common time shift of an ordered-pullback time/spatial tensor shifts only
the first finite-time difference argument and leaves the spatial factor
unchanged. -/
theorem timeShift_orderedPullbackTimeSpatialTensorCLM_apply
    {n : ℕ}
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (φ : SchwartzMap (Fin n → ℝ) ℂ)
    (t : ℝ) (y : NPointDomain d n) :
    timeShiftSchwartzNPoint (d := d) t
        (section43OrderedPullbackTimeSpatialTensorCLM d n χ φ) y =
      φ (fun i : Fin n =>
          if i.val = 0 then
            section43QTime (d := d) (n := n)
              (section43DiffCoordRealCLE d n y) i - t
          else
            section43QTime (d := d) (n := n)
              (section43DiffCoordRealCLE d n y) i) *
        χ (section43QSpatial (d := d) (n := n)
          (section43DiffCoordRealCLE d n y)) := by
  have htime :
      section43QTime (d := d) (n := n)
          (section43DiffCoordRealCLE d n
            (fun j => y j - timeShiftVec d t)) =
        fun i : Fin n =>
          if i.val = 0 then
            section43QTime (d := d) (n := n)
              (section43DiffCoordRealCLE d n y) i - t
          else
            section43QTime (d := d) (n := n)
              (section43DiffCoordRealCLE d n y) i := by
    funext i
    simpa [section43QTime, nPointTimeSpatialCLE] using
      section43DiffCoordRealCLE_sub_timeShiftVec_time
        (d := d) (x := y) (t := t) i
  have hspatial :
      section43QSpatial (d := d) (n := n)
          (section43DiffCoordRealCLE d n
            (fun j => y j - timeShiftVec d t)) =
        section43QSpatial (d := d) (n := n)
          (section43DiffCoordRealCLE d n y) := by
    apply (EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ)).injective
    funext p
    rw [section43QSpatial_apply, section43QSpatial_apply]
    exact
      section43DiffCoordRealCLE_sub_timeShiftVec_spatial
        (d := d) (x := y) (t := t) p.1
        (μ := Fin.succ p.2) (Fin.succ_ne_zero p.2)
  rw [timeShiftSchwartzNPoint_apply]
  rw [section43OrderedPullbackTimeSpatialTensorCLM_apply]
  simp [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    section43NPointTimeSpatialTensor_apply, htime, hspatial]

/-- Translation of the first finite difference-time coordinate by `-t`. -/
def section43FirstTimeShift {m : ℕ} (hm : 0 < m) (t : ℝ) : Fin m → ℝ :=
  fun i => if i = (⟨0, hm⟩ : Fin m) then -t else 0

/-- Common Euclidean time translation of an ordered-pullback source is
translation of only the first finite difference-time coordinate. -/
theorem timeShift_orderedPullbackTimeSpatialTensorCLM_eq_translate_firstTime
    {m : ℕ} (hm : 0 < m)
    (χ : SchwartzMap (Section43SpatialSpace d m) ℂ)
    (φ : SchwartzMap (Fin m → ℝ) ℂ)
    (t : ℝ) :
    timeShiftSchwartzNPoint (d := d) t
        (section43OrderedPullbackTimeSpatialTensorCLM d m χ φ) =
      section43OrderedPullbackTimeSpatialTensorCLM d m χ
        (SCV.translateSchwartz (section43FirstTimeShift (m := m) hm t) φ) := by
  ext y
  rw [timeShift_orderedPullbackTimeSpatialTensorCLM_apply]
  rw [section43OrderedPullbackTimeSpatialTensorCLM_apply]
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    section43NPointTimeSpatialTensor_apply, SCV.translateSchwartz_apply]
  congr 2
  · funext i
    by_cases hi0 : i.val = 0
    · have hi : i = (⟨0, hm⟩ : Fin m) := by
        ext
        exact hi0
      simp [section43FirstTimeShift, hi]
      ring
    · have hi : i ≠ (⟨0, hm⟩ : Fin m) := by
        intro h
        exact hi0 (by simpa using congrArg Fin.val h)
      simp [section43FirstTimeShift, hi0, hi]

end OSReconstruction
