import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceSpatialDensity

/-!
# Section 4.3 Ordered Difference Geometry

This upstream companion contains only the neutral geometry that sends strict
positive time-difference support to ordered positive Euclidean support.  It is
kept separate from the downstream Fourier-Laplace closure file so source-current
constructions can use the ordered zero-diagonal fact without importing
boundary-value data.
-/

noncomputable section

open scoped Topology FourierTransform BoundedContinuousFunction BigOperators
open Set MeasureTheory Filter

namespace OSReconstruction

/-- Positive time-difference coordinates give ordered positive Euclidean
times after applying the inverse difference-coordinate map. -/
theorem section43DiffCoordRealCLE_symm_mem_orderedPositiveTimeRegion_of_pos_time
    (d n : ℕ) [NeZero d]
    {δ : NPointDomain d n}
    (hδ : ∀ i : Fin n, 0 < δ i 0) :
    (section43DiffCoordRealCLE d n).symm δ ∈
      OrderedPositiveTimeRegion d n := by
  intro i
  constructor
  · rw [section43DiffCoordRealCLE_symm_apply]
    rw [Finset.sum_fin_eq_sum_range]
    have hnonempty : (Finset.range (i.val + 1)).Nonempty := by
      exact ⟨0, by simp⟩
    refine Finset.sum_pos ?_ hnonempty
    intro r hr
    have hrlt : r < i.val + 1 := Finset.mem_range.mp hr
    simpa [hrlt] using hδ ⟨r, by
        have hr' := Finset.mem_range.mp hr
        omega⟩
  · intro j hij
    rw [section43DiffCoordRealCLE_symm_apply,
      section43DiffCoordRealCLE_symm_apply]
    rw [Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range]
    have hijv : i.val < j.val := by exact hij
    have hle : i.val + 1 ≤ j.val + 1 := Nat.succ_le_succ hijv.le
    let fj : ℕ → ℝ := fun r =>
      if h : r < j.val + 1 then
        δ ⟨(⟨r, h⟩ : Fin (j.val + 1)).val, by
          have hj := j.isLt
          omega⟩ 0
      else 0
    have hblock_nonempty :
        (Finset.Ico (i.val + 1) (j.val + 1)).Nonempty := by
      refine ⟨i.val + 1, ?_⟩
      exact Finset.mem_Ico.mpr ⟨le_rfl, Nat.succ_lt_succ hijv⟩
    have hleft :
        (∑ r ∈ Finset.range (i.val + 1),
          if h : r < i.val + 1 then
            δ ⟨(⟨r, h⟩ : Fin (i.val + 1)).val, by
              have hi := i.isLt
              omega⟩ 0
          else 0) =
        (∑ r ∈ Finset.range (i.val + 1), fj r) := by
      refine Finset.sum_congr rfl ?_
      intro r hr
      have hri : r < i.val + 1 := Finset.mem_range.mp hr
      have hrj : r < j.val + 1 := lt_of_lt_of_le hri hle
      have hrjle : r ≤ j.val := Nat.lt_succ_iff.mp hrj
      rw [dif_pos hri]
      simp [fj, hrjle]
    have hblock_pos :
        0 < ∑ r ∈ Finset.Ico (i.val + 1) (j.val + 1), fj r := by
      refine Finset.sum_pos ?_ hblock_nonempty
      intro r hr
      have hrj : r < j.val + 1 := (Finset.mem_Ico.mp hr).2
      have hrjle : r ≤ j.val := Nat.lt_succ_iff.mp hrj
      simpa [fj, hrjle] using hδ ⟨r, by
        have hj := j.isLt
        omega⟩
    rw [hleft]
    change (∑ r ∈ Finset.range (i.val + 1), fj r) <
      ∑ r ∈ Finset.range (j.val + 1), fj r
    rw [← Finset.sum_range_add_sum_Ico fj hle]
    exact lt_add_of_pos_right _ hblock_pos

/-- Pulling a Section 4.3 time/spatial tensor back from positive
difference-time coordinates to ordered Euclidean coordinates gives a
zero-diagonal Schwartz test.

The strict-positive hypothesis is on the difference-time factor, and the
`section43DiffCoordRealCLE` pullback is essential: positivity of the raw
Euclidean time coordinates alone would not imply ordered support. -/
theorem VanishesToInfiniteOrderOnCoincidence_orderedPullback_section43NPointTimeSpatialTensor
    (d n : ℕ) [NeZero d]
    (φ : SchwartzMap (Fin n → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (hφ : tsupport (φ : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n) :
    VanishesToInfiniteOrderOnCoincidence
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (section43DiffCoordRealCLE d n)
        (section43NPointTimeSpatialTensor d n φ χ)) := by
  apply VanishesToInfiniteOrderOnCoincidence_of_support_subset_orderedPositiveTimeRegion
  intro y hy
  have hy_pre :
      section43DiffCoordRealCLE d n y ∈
        tsupport
          ((section43NPointTimeSpatialTensor d n φ χ :
            SchwartzNPoint d n) : NPointDomain d n → ℂ) := by
    exact
      tsupport_comp_subset_preimage
        ((section43NPointTimeSpatialTensor d n φ χ :
          SchwartzNPoint d n) : NPointDomain d n → ℂ)
        (section43DiffCoordRealCLE d n).continuous hy
  have hq_time_support :
      section43QTime (d := d) (n := n) (section43DiffCoordRealCLE d n y) ∈
        tsupport (φ : (Fin n → ℝ) → ℂ) :=
    tsupport_section43NPointTimeSpatialTensor_subset_time_preimage
      d n φ χ hy_pre
  have htime_pos :
      ∀ i : Fin n,
        0 < section43QTime (d := d) (n := n)
          (section43DiffCoordRealCLE d n y) i :=
    hφ hq_time_support
  have hδ_pos : ∀ i : Fin n, 0 < (section43DiffCoordRealCLE d n y) i 0 := by
    intro i
    simpa [section43QTime, nPointTimeSpatialCLE]
      using htime_pos i
  have hordered :=
    section43DiffCoordRealCLE_symm_mem_orderedPositiveTimeRegion_of_pos_time
      d n (δ := section43DiffCoordRealCLE d n y) hδ_pos
  simpa using hordered

end OSReconstruction
