/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib.Data.Fin.Tuple.Sort
import OSReconstruction.Wightman.Reconstruction.UniversalProjection
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIEuclideanRotationSource










noncomputable section

open Set
open Topology
open scoped Classical

namespace OSReconstruction

variable {d k : ℕ} [NeZero d]

/-- The Euclidean time coordinate seen after applying a real rotation. -/
def osiiRotatedTime
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (y : SpacetimeDim d) : ℝ :=
  (R.mulVec y) 0

/-- The open time cell around the `q`th point of a configuration.

For every point with smaller rotated center time, the cell lies above the
midpoint; for every point with larger rotated center time, it lies below the
midpoint. Thus cells belonging to distinct center times are disjoint and
retain the same order throughout their product. -/
def osiiOrderedTimeCell
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (t : Fin k → ℝ) (q : Fin k) :
    Set (SpacetimeDim d) :=
  (⋂ r : Fin k,
      if t r < t q then
        {y | (t r + t q) / 2 < osiiRotatedTime R y}
      else Set.univ) ∩
    ⋂ r : Fin k,
      if t q < t r then
        {y | osiiRotatedTime R y < (t q + t r) / 2}
      else Set.univ

omit [NeZero d] in
theorem continuous_osiiRotatedTime
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    Continuous (osiiRotatedTime R) := by
  unfold osiiRotatedTime Matrix.mulVec dotProduct
  fun_prop

omit [NeZero d] in
theorem isOpen_osiiOrderedTimeCell
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (t : Fin k → ℝ) (q : Fin k) :
    IsOpen (osiiOrderedTimeCell R t q) := by
  apply IsOpen.inter
  · apply isOpen_iInter_of_finite
    intro r
    split_ifs
    · exact isOpen_lt continuous_const (continuous_osiiRotatedTime R)
    · exact isOpen_univ
  · apply isOpen_iInter_of_finite
    intro r
    split_ifs
    · exact isOpen_lt (continuous_osiiRotatedTime R) continuous_const
    · exact isOpen_univ

omit [NeZero d] in
theorem mem_osiiOrderedTimeCell_self
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (x : Fin k → SpacetimeDim d)
    (q : Fin k)
    (ht : ∀ i, osiiRotatedTime R (x i) = t i) :
    x q ∈ osiiOrderedTimeCell R t q := by
  constructor
  · rw [Set.mem_iInter]
    intro r
    by_cases hrq : t r < t q
    · simp only [hrq, if_true, Set.mem_setOf_eq]
      rw [ht q]
      linarith
    · simp [hrq]
  · rw [Set.mem_iInter]
    intro r
    by_cases hqr : t q < t r
    · simp only [hqr, if_true, Set.mem_setOf_eq]
      rw [ht q]
      linarith
    · simp [hqr]

omit [NeZero d] in
theorem osiiOrderedTimeCell_lt
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (t : Fin k → ℝ)
    {q r : Fin k} (hqr : t q < t r)
    {y z : SpacetimeDim d}
    (hy : y ∈ osiiOrderedTimeCell R t q)
    (hz : z ∈ osiiOrderedTimeCell R t r) :
    osiiRotatedTime R y < osiiRotatedTime R z := by
  have hy_upper := Set.mem_iInter.mp hy.2 r
  have hz_lower := Set.mem_iInter.mp hz.1 q
  simp only [hqr, if_true, Set.mem_setOf_eq] at hy_upper hz_lower
  linarith

/-- A product neighborhood carrying one fixed proper rotation and one fixed
strict chronological ordering permutation. -/
structure OSIIOrderedProductNeighborhood
    (x : NPointDomain d k) where
  rotation : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ
  orthogonal : rotation.transpose * rotation = 1
  det_one : rotation.det = 1
  order : Equiv.Perm (Fin k)
  cell : Fin k → Set (SpacetimeDim d)
  cell_open : ∀ i, IsOpen (cell i)
  center_mem : ∀ i, x i ∈ cell i
  ordered :
    ∀ (y : NPointDomain d k),
      (∀ i, y i ∈ cell i) →
      ∀ i j : Fin k, i < j →
        osiiRotatedTime rotation (y (order i)) <
          osiiRotatedTime rotation (y (order j))

namespace OSIIOrderedProductNeighborhood

end OSIIOrderedProductNeighborhood

/-- Every configuration away from the coincidence locus has an open product
neighborhood with one proper rotation and one strict chronological order. -/
theorem exists_osiiOrderedProductNeighborhood
    (x : NPointDomain d k)
    (hx : x ∉ CoincidenceLocus d k) :
    Nonempty (OSIIOrderedProductNeighborhood x) := by
  obtain ⟨c, hc, hprojection⟩ :=
    exists_universal_time_projection' d k
  obtain ⟨R, hR, hdet, hproj⟩ := hprojection x
  let t : Fin k → ℝ := fun i => osiiRotatedTime R (x i)
  have ht_injective : Function.Injective t := by
    intro i j hij
    by_contra hne
    have hxne : x i ≠ x j := by
      intro hEq
      exact hx ⟨i, j, hne, hEq⟩
    have hnorm : 0 < ‖x i - x j‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hxne)
    have hbound := hproj i j hne
    have htime_zero :
        (R.mulVec (x i - x j)) 0 = 0 := by
      rw [Matrix.mulVec_sub]
      change t i - t j = 0
      rw [hij, sub_self]
    rw [htime_zero, abs_zero] at hbound
    nlinarith
  let σ : Equiv.Perm (Fin k) := Tuple.sort t
  have hstrict :
      ∀ i j : Fin k, i < j → t (σ i) < t (σ j) := by
    intro i j hij
    have hle : t (σ i) ≤ t (σ j) :=
      Tuple.monotone_sort t (le_of_lt hij)
    have hne : t (σ i) ≠ t (σ j) := by
      apply ht_injective.ne
      exact σ.injective.ne (ne_of_lt hij)
    exact lt_of_le_of_ne hle hne
  refine ⟨{
    rotation := R
    orthogonal := hR
    det_one := hdet
    order := σ
    cell := osiiOrderedTimeCell R t
    cell_open := isOpen_osiiOrderedTimeCell R t
    center_mem := fun i =>
      mem_osiiOrderedTimeCell_self R x i (fun q => rfl)
    ordered := ?_ }⟩
  intro y hy i j hij
  exact
    osiiOrderedTimeCell_lt R t (hstrict i j hij)
      (hy (σ i)) (hy (σ j))

/-- A compact factorized source whose one-point supports have one uniform
strict chronological order after a proper Euclidean rotation. -/
structure OSIIOrderedCompactProductSource (d k : ℕ) [NeZero d] where
  factors : Fin k → SchwartzSpacetime d
  factor_compact :
    ∀ i, HasCompactSupport
      ((factors i : SchwartzSpacetime d) : SpacetimeDim d → ℂ)
  rotation : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ
  orthogonal : rotation.transpose * rotation = 1
  det_one : rotation.det = 1
  order : Equiv.Perm (Fin k)
  ordered_support :
    ∀ i j : Fin k, i < j →
      ∀ y ∈ tsupport
          ((factors (order i) : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ),
        ∀ z ∈ tsupport
            ((factors (order j) : SchwartzSpacetime d) :
              SpacetimeDim d → ℂ),
          osiiRotatedTime rotation y < osiiRotatedTime rotation z

namespace OSIIOrderedCompactProductSource

/-- Compact factors supported in an ordered product neighborhood define an
ordered compact product source. -/
noncomputable def ofNeighborhood
    {x : NPointDomain d k}
    (P : OSIIOrderedProductNeighborhood x)
    (fs : Fin k → SchwartzSpacetime d)
    (hcompact :
      ∀ i, HasCompactSupport
        ((fs i : SchwartzSpacetime d) : SpacetimeDim d → ℂ))
    (hsupport :
      ∀ i,
        tsupport
            ((fs i : SchwartzSpacetime d) : SpacetimeDim d → ℂ) ⊆
          P.cell i) :
    OSIIOrderedCompactProductSource d k where
  factors := fs
  factor_compact := hcompact
  rotation := P.rotation
  orthogonal := P.orthogonal
  det_one := P.det_one
  order := P.order
  ordered_support := by
    intro i j hij y hy z hz
    let config : NPointDomain d k := fun q =>
      if q = P.order i then y
      else if q = P.order j then z
      else x q
    have hconfig : ∀ q, config q ∈ P.cell q := by
      intro q
      by_cases hqi : q = P.order i
      · subst q
        simp [config, hsupport (P.order i) hy]
      · by_cases hqj : q = P.order j
        · subst q
          simp [config, hqi, hsupport (P.order j) hz]
        · simp [config, hqi, hqj, P.center_mem q]
    have hordered := P.ordered config hconfig i j hij
    have hij_ne : P.order i ≠ P.order j :=
      P.order.injective.ne (ne_of_lt hij)
    simpa [config, hij_ne, hij_ne.symm] using hordered

theorem pairwise_disjoint_tsupport
    (P : OSIIOrderedCompactProductSource d k) :
    ∀ q r : Fin k, q ≠ r →
      Disjoint
        (tsupport
          ((P.factors q : SchwartzSpacetime d) : SpacetimeDim d → ℂ))
        (tsupport
          ((P.factors r : SchwartzSpacetime d) : SpacetimeDim d → ℂ)) := by
  intro q r hqr
  rw [Set.disjoint_left]
  intro y hyq hyr
  let i := P.order.symm q
  let j := P.order.symm r
  have hij : i ≠ j := by
    intro h
    apply hqr
    simpa [i, j] using congrArg P.order h
  rcases lt_or_gt_of_ne hij with hij_lt | hji_lt
  · have hlt := P.ordered_support i j hij_lt y (by simpa [i] using hyq)
      y (by simpa [j] using hyr)
    exact (lt_irrefl _) hlt
  · have hlt := P.ordered_support j i hji_lt y (by simpa [j] using hyr)
      y (by simpa [i] using hyq)
    exact (lt_irrefl _) hlt

theorem vanishes
    (P : OSIIOrderedCompactProductSource d k) :
    VanishesToInfiniteOrderOnCoincidence
      (SchwartzMap.productTensor P.factors) := by
  apply VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint
  rw [Set.disjoint_left]
  intro x hx hcoin
  rcases hcoin with ⟨i, j, hij, hEq⟩
  have hsupp :
      ∀ q,
        x q ∈ tsupport
          ((P.factors q : SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
    intro q
    by_contra hq
    have hlocal :
        ((P.factors q : SchwartzSpacetime d) : SpacetimeDim d → ℂ)
            =ᶠ[𝓝 (x q)] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp hq
    have hcoord :
        Filter.Tendsto (fun y : NPointDomain d k => y q)
          (𝓝 x) (𝓝 (x q)) :=
      (continuous_apply q).continuousAt
    have hprod :
        ((SchwartzMap.productTensor P.factors : SchwartzNPoint d k) :
            NPointDomain d k → ℂ) =ᶠ[𝓝 x] 0 := by
      filter_upwards [hcoord.eventually hlocal] with y hy
      rw [SchwartzMap.productTensor_apply]
      exact Finset.prod_eq_zero (Finset.mem_univ q) hy
    exact (notMem_tsupport_iff_eventuallyEq.mpr hprod) hx
  exact Set.disjoint_left.mp (P.pairwise_disjoint_tsupport i j hij)
    (hsupp i) (by simpa [hEq] using hsupp j)

end OSIIOrderedCompactProductSource

end OSReconstruction
