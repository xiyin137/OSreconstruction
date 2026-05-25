import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSourceCurrent
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceOrderedDensity
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceProductSourceCarrier
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTotalTimePushforward

/-!
# OS II Product-Tensor Schwinger Functionals

This companion records the Schwinger-side source of the finite time-product
multilinear functionals used by the OS-II product-source bridge.  The honest
producer is a continuous linear map from the finite time-difference Schwartz
space into the zero-diagonal Schwinger test space.  Composing that map with
the Schwinger CLM and the finite product tensor gives the scalar multilinear
probe required by the Fubini reassembly theorem.
-/

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

/-- Adding a common Euclidean time shift changes only the first
difference-time coordinate. -/
theorem section43DiffCoordRealCLE_add_timeShiftVec_time
    {n : ℕ} (x : NPointDomain d n) (t : ℝ) (i : Fin n) :
    section43DiffCoordRealCLE d n (fun j => x j + timeShiftVec d t) i 0 =
      if i.val = 0 then section43DiffCoordRealCLE d n x i 0 + t
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

/-- Common Euclidean time shifts do not change spatial difference
coordinates. -/
theorem section43DiffCoordRealCLE_add_timeShiftVec_spatial
    {n : ℕ} (x : NPointDomain d n) (t : ℝ)
    (i : Fin n) {μ : Fin (d + 1)} (hμ : μ ≠ 0) :
    section43DiffCoordRealCLE d n (fun j => x j + timeShiftVec d t) i μ =
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

private theorem tsupport_precomp_subset_local {X Y α : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Zero α]
    {f : Y → α} {h : X → Y} (hh : Continuous h) :
    tsupport (fun x => f (h x)) ⊆ h ⁻¹' tsupport f := by
  refine closure_minimal ?_ ((isClosed_tsupport _).preimage hh)
  intro x hx
  exact subset_closure (by simpa [Function.mem_support] using hx)

omit [NeZero d] in
private theorem continuous_translateNPointDomain_local
    (a : SpacetimeDim d) {n : ℕ} :
    Continuous (translateNPointDomain (d := d) (n := n) a) := by
  apply continuous_pi
  intro i
  exact (continuous_apply i).sub continuous_const

/-- A strictly positive Euclidean time shift preserves zero-diagonal
admissibility of an OS tensor product whose two factors have ordered
positive-time support. -/
theorem VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_of_ordered_positive
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (t : ℝ) (ht : 0 < t) :
    VanishesToInfiniteOrderOnCoincidence
      (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) := by
  exact
    VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d) (f := f)
      (g := timeShiftSchwartzNPoint (d := d) t g)
      hf_ord
      (timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport
        (d := d) t ht g hg_ord)

/-- On the strict positive orthant, the total OS-II finite-time shift is
strictly positive. -/
theorem section43TimeStrictPositiveRegion_sum_pos
    {m : ℕ} [Nonempty (Fin m)] {ξ : Fin m → ℝ}
    (hξ : ξ ∈ section43TimeStrictPositiveRegion m) :
    0 < ∑ p : Fin m, ξ p := by
  classical
  exact
    Finset.sum_pos
      (fun p _ => hξ p)
      Finset.univ_nonempty

/-- The OS-II strict positive orthant gives honest zero-diagonal shifted shells
for the Schwinger functional. -/
theorem VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_sum_of_strictPositive
    {m n r : ℕ} [Nonempty (Fin m)]
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (ξ : Fin m → ℝ) (hξ : ξ ∈ section43TimeStrictPositiveRegion m) :
    VanishesToInfiniteOrderOnCoincidence
      (f.osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) (∑ p : Fin m, ξ p) g)) := by
  exact
    VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_of_ordered_positive
      (d := d) f hf_ord g hg_ord
      (∑ p : Fin m, ξ p)
      (section43TimeStrictPositiveRegion_sum_pos (m := m) hξ)

/-- The totalized `ofClassical` branch is the honest shifted-shell subtype on
the OS-II strict positive orthant. -/
theorem ZeroDiagonalSchwartz_ofClassical_osConjTensorProduct_timeShift_sum_of_strictPositive
    {m n r : ℕ} [Nonempty (Fin m)]
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (ξ : Fin m → ℝ) (hξ : ξ ∈ section43TimeStrictPositiveRegion m) :
    ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (∑ p : Fin m, ξ p) g)) =
      ⟨f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (∑ p : Fin m, ξ p) g),
        VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_sum_of_strictPositive
          (d := d) f hf_ord g hg_ord ξ hξ⟩ := by
  exact
    ZeroDiagonalSchwartz.ofClassical_of_vanishes
      (f := f.osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) (∑ p : Fin m, ξ p) g))
      (VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_sum_of_strictPositive
        (d := d) f hf_ord g hg_ord ξ hξ)

omit [NeZero d] in
theorem timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport_of_nonneg
    {n : ℕ} (a : ℝ) (ha : 0 ≤ a)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n) :
    tsupport (((timeShiftSchwartzNPoint (d := d) a f : SchwartzNPoint d n) :
      NPointDomain d n → ℂ)) ⊆ OrderedPositiveTimeRegion d n := by
  intro x hx
  have hxpre :
      (fun i => x i - timeShiftVec d a) ∈
        tsupport ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ) := by
    exact tsupport_precomp_subset_local
      (f := ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ))
      (h := translateNPointDomain (d := d) (n := n) (timeShiftVec d a))
      (continuous_translateNPointDomain_local (d := d) (n := n) (timeShiftVec d a)) hx
  have hord := hf_ord hxpre
  intro i
  constructor
  · have hi := (hord i).1
    have htime : timeShiftVec d a 0 = a := by simp [timeShiftVec]
    have : x i 0 - a > 0 := by
      simpa [OrderedPositiveTimeRegion, htime] using hi
    linarith
  · intro j hij
    have hij' := (hord i).2 j hij
    have htime : timeShiftVec d a 0 = a := by simp [timeShiftVec]
    have : x i 0 - a < x j 0 - a := by
      simpa [OrderedPositiveTimeRegion, htime] using hij'
    linarith

/-- Common-time transport gives a left-shifted and right-total-shifted
Schwinger shell; this is the honest zero-diagonal subtype on the strict
positive source orthant. -/
theorem VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_leftTimeShift_timeShift_sum_of_strictPositive
    {m n r : ℕ} [Nonempty (Fin m)]
    (a : ℝ) (ha : 0 ≤ a)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (ξ : Fin m → ℝ) (hξ : ξ ∈ section43TimeStrictPositiveRegion m) :
    VanishesToInfiniteOrderOnCoincidence
      ((timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) (∑ p : Fin m, ξ p) g)) := by
  exact
    VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
      (d := d)
      (f := timeShiftSchwartzNPoint (d := d) a f)
      (g := timeShiftSchwartzNPoint (d := d) (∑ p : Fin m, ξ p) g)
      (timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport_of_nonneg
        (d := d) a ha f hf_ord)
      (timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport
        (d := d) (∑ p : Fin m, ξ p)
        (section43TimeStrictPositiveRegion_sum_pos (m := m) hξ)
        g hg_ord)

/-- The `ofClassical` branch is the honest left/right shifted subtype for the
common-time transported shell. -/
theorem ZeroDiagonalSchwartz_ofClassical_osConjTensorProduct_leftTimeShift_timeShift_sum_of_strictPositive
    {m n r : ℕ} [Nonempty (Fin m)]
    (a : ℝ) (ha : 0 ≤ a)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (ξ : Fin m → ℝ) (hξ : ξ ∈ section43TimeStrictPositiveRegion m) :
    ZeroDiagonalSchwartz.ofClassical
        ((timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (∑ p : Fin m, ξ p) g)) =
      ⟨(timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (∑ p : Fin m, ξ p) g),
        VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_leftTimeShift_timeShift_sum_of_strictPositive
          (d := d) a ha f hf_ord g hg_ord ξ hξ⟩ := by
  exact
    ZeroDiagonalSchwartz.ofClassical_of_vanishes
      (f := (timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) (∑ p : Fin m, ξ p) g))
      (VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_leftTimeShift_timeShift_sum_of_strictPositive
        (d := d) a ha f hf_ord g hg_ord ξ hξ)

/-- Pairing a fixed left Section 4.3 quotient with a fixed-spatial right
time/spatial shell gives a scalar continuous linear functional of the right
finite-time Schwartz test. -/
noncomputable def bvt_W_pairing_descended_timeSpatialRightCLM
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n k : ℕ)
    (u : Section43PositiveEnergyComponent (d := d) n)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    SchwartzMap (Fin k → ℝ) ℂ →L[ℂ] ℂ :=
  ((bvt_W_pairing_descended_frequencyProjection_rightCLM
        (d := d) OS lgc n k u).comp
      (section43PositiveEnergyQuotientMap (d := d) k)).comp
    (section43TimeSpatialTensorCLM d k χ)

@[simp] theorem bvt_W_pairing_descended_timeSpatialRightCLM_apply
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n k : ℕ)
    (u : Section43PositiveEnergyComponent (d := d) n)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (φ : SchwartzMap (Fin k → ℝ) ℂ) :
    bvt_W_pairing_descended_timeSpatialRightCLM
        (d := d) OS lgc n k u χ φ =
      bvt_W_pairing_descended_frequencyProjection (d := d) OS lgc n k u
        (section43PositiveEnergyQuotientMap (d := d) k
          (section43NPointTimeSpatialTensor d k φ χ)) := rfl

/-- Product-source values of the fixed-left BVT time/spatial right CLM are the
ordered-source OS Schwinger scalars supplied by the Section 4.3 carrier. -/
theorem bvt_timeSpatialRightCLM_productSource_eq_osScalar_orderedSources
    (d n k : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (gs₁ : Fin n → Section43CompactPositiveTimeSource1D)
    (χ₁ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (hχ₁ : χ₁ ∈ section43SpatialFourierCompactRange d n)
    (gs₂ : Fin k → Section43CompactPositiveTimeSource1D)
    (χ₂ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (hχ₂ : χ₂ ∈ section43SpatialFourierCompactRange d k) :
    ∃ (src₁ : Section43CompactOrderedSource d n)
      (src₂ : Section43CompactOrderedSource d k),
      section43PositiveEnergyQuotientMap (d := d) n
        (section43NPointTimeSpatialTensor d n
          (section43TimeProductTensor
            (fun i : Fin n =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs₁ i)))
          χ₁) =
        section43FourierLaplaceTransformComponent d n
          src₁.f src₁.ordered src₁.compact ∧
      section43PositiveEnergyQuotientMap (d := d) k
        (section43NPointTimeSpatialTensor d k
          (section43TimeProductTensor
            (fun i : Fin k =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs₂ i)))
          χ₂) =
        section43FourierLaplaceTransformComponent d k
          src₂.f src₂.ordered src₂.compact ∧
      bvt_W_pairing_descended_timeSpatialRightCLM
          (d := d) OS lgc n k
          (section43PositiveEnergyQuotientMap (d := d) n
            (section43NPointTimeSpatialTensor d n
              (section43TimeProductTensor
                (fun i : Fin n =>
                  section43OneSidedLaplaceSchwartzRepresentative1D (gs₁ i)))
              χ₁))
          χ₂
          (section43TimeProductTensor
            (fun i : Fin k =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs₂ i))) =
        OS.S (n + k)
          (ZeroDiagonalSchwartz.ofClassical
            (src₁.f.osConjTensorProduct src₂.f)) := by
  simpa using
    bvt_pairing_productSource_eq_osScalar_orderedSources
      d n k OS lgc gs₁ χ₁ hχ₁ gs₂ χ₂ hχ₂

/-- Product-time multilinear form of the fixed-left BVT time/spatial right
scalar functional. -/
noncomputable def bvt_W_pairing_descended_timeSpatialRightProductMultilinear
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n k : ℕ)
    (u : Section43PositiveEnergyComponent (d := d) n)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    ContinuousMultilinearMap ℂ
      (fun _ : Fin k => SchwartzMap ℝ ℂ) ℂ :=
  (bvt_W_pairing_descended_timeSpatialRightCLM
      (d := d) OS lgc n k u χ).compContinuousMultilinearMap
    (SchwartzMap.productTensorMLM (E := ℝ) k)

@[simp] theorem bvt_W_pairing_descended_timeSpatialRightProductMultilinear_apply
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n k : ℕ)
    (u : Section43PositiveEnergyComponent (d := d) n)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (fs : Fin k → SchwartzMap ℝ ℂ) :
    bvt_W_pairing_descended_timeSpatialRightProductMultilinear
        (d := d) OS lgc n k u χ fs =
    bvt_W_pairing_descended_frequencyProjection (d := d) OS lgc n k u
        (section43PositiveEnergyQuotientMap (d := d) k
          (section43NPointTimeSpatialTensor d k
            (section43TimeProductTensor fs) χ)) := by
  rfl

/-- The strict-positive imaginary-axis kernel of the fixed-left BVT
time/spatial product probe is continuous.  This is the producer-side
continuity datum needed when this scalar probe is matched with the OS-II
real-edge/delta-smearing branch. -/
theorem continuousOn_bvt_W_pairing_descended_timeSpatialRightProductMultilinear_imagAxis
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (n k : ℕ)
    (u : Section43PositiveEnergyComponent (d := d) n)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    ContinuousOn
      (fun τ : Fin k → ℝ =>
        bvt_W_pairing_descended_timeSpatialRightProductMultilinear
          (d := d) OS lgc n k u χ
          (fun i : Fin k => section43ImagAxisPsiKernel (τ i)))
      (section43TimeStrictPositiveRegion k) := by
  let T : SchwartzMap (Fin k → ℝ) ℂ →L[ℂ] ℂ :=
    bvt_W_pairing_descended_timeSpatialRightCLM
      (d := d) OS lgc n k u χ
  have hkernel :
      ContinuousOn section43TimeImagAxisProductKernel
        (section43TimeStrictPositiveRegion k) :=
    continuousOn_section43TimeImagAxisProductKernel_strictPositive
  have hcomp :
      ContinuousOn
        (fun τ : Fin k → ℝ => T (section43TimeImagAxisProductKernel τ))
        (section43TimeStrictPositiveRegion k) :=
    T.continuous.continuousOn.comp hkernel (fun _ _ => Set.mem_univ _)
  simpa [T, bvt_W_pairing_descended_timeSpatialRightProductMultilinear,
    bvt_W_pairing_descended_timeSpatialRightCLM,
    section43TimeImagAxisProductKernel] using hcomp

/-- Delta-smearing recovery for the BVT imaginary-axis kernel against a
left-shifted Schwinger shell.

This is the OS-II product-source approximate-identity step: if the fixed-left
BVT imaginary-axis probe and the left-shifted Schwinger shell have equal
compact positive product-source pairings, then they agree pointwise on the
strict-positive orthant.  The proof supplies the continuity inputs from the
actual BVT multilinear probe and from the OS-II total real-edge package. -/
theorem bvt_imagAxis_eq_leftShiftedShell_of_productSource_pairings_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n m r : ℕ} [Nonempty (Fin m)]
    (u : Section43PositiveEnergyComponent (d := d) n)
    (χ : SchwartzMap (Section43SpatialSpace d m) ℂ)
    (a : ℝ) (ha : 0 ≤ a)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (x0 : Fin m → ℝ) (hx0 : ∀ i : Fin m, 0 < x0 i)
    (hpair :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        (∫ ξ : Fin m → ℝ,
          bvt_W_pairing_descended_timeSpatialRightProductMultilinear
              (d := d) OS lgc n m u χ
              (fun i : Fin m => section43ImagAxisPsiKernel (ξ i)) *
            (section43TimeProductSource gs).f ξ) =
          ∫ ξ : Fin m → ℝ,
            OS.S (n + r)
              (ZeroDiagonalSchwartz.ofClassical
                ((timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
                  (timeShiftSchwartzNPoint (d := d)
                    (∑ p : Fin m, ξ p) g))) *
              (section43TimeProductSource gs).f ξ) :
    bvt_W_pairing_descended_timeSpatialRightProductMultilinear
        (d := d) OS lgc n m u χ
        (fun i : Fin m => section43ImagAxisPsiKernel (x0 i)) =
      OS.S (n + r)
        (ZeroDiagonalSchwartz.ofClassical
          ((timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, x0 p) g))) := by
  classical
  let KBVT : (Fin m → ℝ) → ℂ := fun ξ =>
    bvt_W_pairing_descended_timeSpatialRightProductMultilinear
      (d := d) OS lgc n m u χ
      (fun i : Fin m => section43ImagAxisPsiKernel (ξ i))
  have hf_shift :
      tsupport (((timeShiftSchwartzNPoint (d := d) a f :
        SchwartzNPoint d n) : NPointDomain d n → ℂ)) ⊆
        OrderedPositiveTimeRegion d n :=
    timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport_of_nonneg
      a ha f hf_ord
  let Fshell : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single n
      (timeShiftSchwartzNPoint (d := d) a f) hf_shift
  let Gshell : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single r g hg_ord
  have hGshell_compact :
      ∀ s,
        HasCompactSupport ((((Gshell : BorchersSequence d).funcs s :
          SchwartzNPoint d s) : NPointDomain d s → ℂ)) := by
    intro s
    by_cases hs : s = r
    · subst hs
      simpa [Gshell, PositiveTimeBorchersSequence.single_toBorchersSequence] using
        hg_compact
    · have hzero :
        (((Gshell : BorchersSequence d).funcs s : SchwartzNPoint d s) :
          NPointDomain d s → ℂ) = 0 := by
          simp [Gshell, PositiveTimeBorchersSequence.single_toBorchersSequence,
            BorchersSequence.single, hs]
      rw [hzero]
      simpa using (HasCompactSupport.zero :
        HasCompactSupport (0 : NPointDomain d s → ℂ))
  let Kedge : (Fin m → ℝ) → ℂ := fun ξ =>
    OSInnerProduct d OS.S (Fshell : BorchersSequence d)
      (timeShiftBorchers (d := d)
        (∑ p : Fin m, ξ p)
        (Gshell : BorchersSequence d))
  have hdelta : KBVT x0 = Kedge x0 := by
    refine
      eq_of_positiveOrthant_productSource_pairings_eq KBVT Kedge x0 hx0
        ?_ ?_ ?_ ?_ ?_
    · exact
        (continuousOn_bvt_W_pairing_descended_timeSpatialRightProductMultilinear_imagAxis
          (d := d) OS lgc n m u χ).continuousAt
          ((isOpen_section43TimeStrictPositiveRegion m).mem_nhds hx0)
    · exact
        continuousAt_osii_total_positive_time_real_edge_positiveOrthant
          (d := d) OS lgc Fshell Gshell hGshell_compact x0 hx0
    · exact
        continuousOn_bvt_W_pairing_descended_timeSpatialRightProductMultilinear_imagAxis
          (d := d) OS lgc n m u χ
    · exact
        continuousOn_osii_total_positive_time_real_edge_positiveOrthant
          (d := d) OS lgc Fshell Gshell hGshell_compact
    · intro gs
      calc
        (∫ ξ : Fin m → ℝ, KBVT ξ * (section43TimeProductSource gs).f ξ)
            =
          ∫ ξ : Fin m → ℝ,
            OS.S (n + r)
              (ZeroDiagonalSchwartz.ofClassical
                ((timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
                  (timeShiftSchwartzNPoint (d := d)
                    (∑ p : Fin m, ξ p) g))) *
              (section43TimeProductSource gs).f ξ := by
              exact hpair gs
        _ =
          ∫ ξ : Fin m → ℝ, Kedge ξ * (section43TimeProductSource gs).f ξ := by
            refine integral_congr_ae ?_
            filter_upwards with ξ
            have hξ :=
              osii_total_positive_time_real_edge_single_eq_schwinger_timeShift
                (d := d) OS
                (timeShiftSchwartzNPoint (d := d) a f) hf_shift
                g hg_ord ξ
            simpa [Kedge, Fshell, Gshell] using
              congrArg (fun z : ℂ => z * (section43TimeProductSource gs).f ξ)
                hξ.symm
  calc
    bvt_W_pairing_descended_timeSpatialRightProductMultilinear
        (d := d) OS lgc n m u χ
        (fun i : Fin m => section43ImagAxisPsiKernel (x0 i)) =
      KBVT x0 := by rfl
    _ = Kedge x0 := hdelta
    _ =
      OS.S (n + r)
        (ZeroDiagonalSchwartz.ofClassical
          ((timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, x0 p) g))) := by
        simpa [Kedge, Fshell, Gshell] using
          osii_total_positive_time_real_edge_single_eq_schwinger_timeShift
            (d := d) OS
            (timeShiftSchwartzNPoint (d := d) a f) hf_shift
            g hg_ord x0

/-- Product-source values of the fixed-left BVT time/spatial right multilinear
probe are the ordered-source OS Schwinger scalars supplied by the Section 4.3
carrier. -/
theorem bvt_timeSpatialRightProductMultilinear_oneSidedLaplace_eq_osScalar_orderedSources
    (d n k : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (gs₁ : Fin n → Section43CompactPositiveTimeSource1D)
    (χ₁ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (hχ₁ : χ₁ ∈ section43SpatialFourierCompactRange d n)
    (gs₂ : Fin k → Section43CompactPositiveTimeSource1D)
    (χ₂ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (hχ₂ : χ₂ ∈ section43SpatialFourierCompactRange d k) :
    ∃ (src₁ : Section43CompactOrderedSource d n)
      (src₂ : Section43CompactOrderedSource d k),
      section43PositiveEnergyQuotientMap (d := d) n
        (section43NPointTimeSpatialTensor d n
          (section43TimeProductTensor
            (fun i : Fin n =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs₁ i)))
          χ₁) =
        section43FourierLaplaceTransformComponent d n
          src₁.f src₁.ordered src₁.compact ∧
      section43PositiveEnergyQuotientMap (d := d) k
        (section43NPointTimeSpatialTensor d k
          (section43TimeProductTensor
            (fun i : Fin k =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs₂ i)))
          χ₂) =
        section43FourierLaplaceTransformComponent d k
          src₂.f src₂.ordered src₂.compact ∧
      bvt_W_pairing_descended_timeSpatialRightProductMultilinear
          (d := d) OS lgc n k
          (section43PositiveEnergyQuotientMap (d := d) n
            (section43NPointTimeSpatialTensor d n
              (section43TimeProductTensor
                (fun i : Fin n =>
                  section43OneSidedLaplaceSchwartzRepresentative1D (gs₁ i)))
              χ₁))
          χ₂
          (fun i : Fin k =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs₂ i)) =
        OS.S (n + k)
          (ZeroDiagonalSchwartz.ofClassical
            (src₁.f.osConjTensorProduct src₂.f)) := by
  simpa using
    bvt_timeSpatialRightCLM_productSource_eq_osScalar_orderedSources
      d n k OS lgc gs₁ χ₁ hχ₁ gs₂ χ₂ hχ₂

/-- Explicit compact-spatial-source form of
`bvt_timeSpatialRightProductMultilinear_oneSidedLaplace_eq_osScalar_orderedSources`,
rewritten as a source-current identity for the ordered-pullback compact
currents. -/
theorem bvt_timeSpatialRightProductMultilinear_oneSidedLaplace_eq_osScalar_orderedPullbackSources
    (d n k : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (gs₁ : Fin n → Section43CompactPositiveTimeSource1D)
    (κ₁ : Section43SpatialCompactSource d n)
    (gs₂ : Fin k → Section43CompactPositiveTimeSource1D)
    (κ₂ : Section43SpatialCompactSource d k) :
    bvt_W_pairing_descended_timeSpatialRightProductMultilinear
        (d := d) OS lgc n k
        (section43PositiveEnergyQuotientMap (d := d) n
          (section43NPointTimeSpatialTensor d n
            (section43TimeProductTensor
              (fun i : Fin n =>
                section43OneSidedLaplaceSchwartzRepresentative1D (gs₁ i)))
            (SchwartzMap.fourierTransformCLM ℂ κ₁.1)))
        (SchwartzMap.fourierTransformCLM ℂ κ₂.1)
        (fun i : Fin k =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs₂ i)) =
      OS.S (n + k)
        (ZeroDiagonalSchwartz.ofClassical
          ((section43OrderedPullbackTimeSpatialTensorCLM d n κ₁.1
              (section43TimeProductSource gs₁).f).osConjTensorProduct
            (section43OrderedPullbackTimeSpatialTensorCLM d k κ₂.1
              (section43TimeProductSource gs₂).f))) := by
  simpa [bvt_W_pairing_descended_timeSpatialRightProductMultilinear,
    bvt_W_pairing_descended_timeSpatialRightCLM]
    using
      bvt_pairing_productSource_eq_osScalar_orderedPullbackSources
        d n k OS lgc gs₁ κ₁ gs₂ κ₂

/-- Compact-source pairing of the fixed-left BVT product-time real-edge kernel.

This rewrites the one-sided Laplace product value by the checked Section 4.3
Fubini theorem: the BVT scalar probe integrated against a compact positive
product source recovers the ordered-source Schwinger scalar produced by the
Fourier-Laplace carrier. -/
theorem integral_bvt_timeSpatialRightProductMultilinear_imagAxis_eq_osScalar_orderedSources
    (d n k : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (gs₁ : Fin n → Section43CompactPositiveTimeSource1D)
    (χ₁ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (hχ₁ : χ₁ ∈ section43SpatialFourierCompactRange d n)
    (gs₂ : Fin k → Section43CompactPositiveTimeSource1D)
    (χ₂ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (hχ₂ : χ₂ ∈ section43SpatialFourierCompactRange d k) :
    ∃ (src₁ : Section43CompactOrderedSource d n)
      (src₂ : Section43CompactOrderedSource d k),
      section43PositiveEnergyQuotientMap (d := d) n
        (section43NPointTimeSpatialTensor d n
          (section43TimeProductTensor
            (fun i : Fin n =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs₁ i)))
          χ₁) =
        section43FourierLaplaceTransformComponent d n
          src₁.f src₁.ordered src₁.compact ∧
      section43PositiveEnergyQuotientMap (d := d) k
        (section43NPointTimeSpatialTensor d k
          (section43TimeProductTensor
            (fun i : Fin k =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs₂ i)))
          χ₂) =
        section43FourierLaplaceTransformComponent d k
          src₂.f src₂.ordered src₂.compact ∧
      (∫ ξ : Fin k → ℝ,
          bvt_W_pairing_descended_timeSpatialRightProductMultilinear
            (d := d) OS lgc n k
            (section43PositiveEnergyQuotientMap (d := d) n
              (section43NPointTimeSpatialTensor d n
                (section43TimeProductTensor
                  (fun i : Fin n =>
                    section43OneSidedLaplaceSchwartzRepresentative1D (gs₁ i)))
                χ₁))
            χ₂
            (fun i : Fin k => section43ImagAxisPsiKernel (ξ i)) *
          (section43TimeProductSource gs₂).f ξ) =
        OS.S (n + k)
          (ZeroDiagonalSchwartz.ofClassical
            (src₁.f.osConjTensorProduct src₂.f)) := by
  rcases
    bvt_timeSpatialRightProductMultilinear_oneSidedLaplace_eq_osScalar_orderedSources
      d n k OS lgc gs₁ χ₁ hχ₁ gs₂ χ₂ hχ₂ with
    ⟨src₁, src₂, hsrc₁, hsrc₂, hprod⟩
  refine ⟨src₁, src₂, hsrc₁, hsrc₂, ?_⟩
  let u : Section43PositiveEnergyComponent (d := d) n :=
    section43PositiveEnergyQuotientMap (d := d) n
      (section43NPointTimeSpatialTensor d n
        (section43TimeProductTensor
          (fun i : Fin n =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs₁ i)))
        χ₁)
  let T : SchwartzMap (Fin k → ℝ) ℂ →L[ℂ] ℂ :=
    bvt_W_pairing_descended_timeSpatialRightCLM
      (d := d) OS lgc n k u χ₂
  have hflat :=
    section43TimeProductTensor_allSlots_flattened
      T gs₂ (fun _ : Fin k => 0)
  calc
    (∫ ξ : Fin k → ℝ,
        bvt_W_pairing_descended_timeSpatialRightProductMultilinear
          (d := d) OS lgc n k u χ₂
          (fun i : Fin k => section43ImagAxisPsiKernel (ξ i)) *
        (section43TimeProductSource gs₂).f ξ) =
      T (section43TimeProductTensor
        (fun i : Fin k =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs₂ i))) := by
        simpa [T, bvt_W_pairing_descended_timeSpatialRightProductMultilinear,
          section43TimeImagAxisProductKernel] using hflat.symm
    _ =
      bvt_W_pairing_descended_timeSpatialRightProductMultilinear
          (d := d) OS lgc n k u χ₂
          (fun i : Fin k =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs₂ i)) := by
        rfl
    _ =
      OS.S (n + k)
          (ZeroDiagonalSchwartz.ofClassical
            (src₁.f.osConjTensorProduct src₂.f)) := by
        simpa [u] using hprod

/-- Compact-source pairing of the fixed-left BVT product-time real-edge
kernel, with the ordered sources specified by the concrete time/spatial
product data rather than an existential carrier. -/
theorem integral_bvt_timeSpatialRightProductMultilinear_imagAxis_eq_osScalar_explicitOrderedSources
    (n k : ℕ)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (gs1 : Fin n → Section43CompactPositiveTimeSource1D)
    (kappa1 : Section43SpatialCompactSource d n)
    (gs2 : Fin k → Section43CompactPositiveTimeSource1D)
    (kappa2 : Section43SpatialCompactSource d k) :
    let src1 : Section43CompactOrderedSource d n :=
      section43OrderedSourceOfTimeSpatialSource d n
        (section43TimeSpatialProductSource d n
          (section43TimeProductSource gs1) kappa1)
    let src2 : Section43CompactOrderedSource d k :=
      section43OrderedSourceOfTimeSpatialSource d k
        (section43TimeSpatialProductSource d k
          (section43TimeProductSource gs2) kappa2)
    (∫ ξ : Fin k → ℝ,
        bvt_W_pairing_descended_timeSpatialRightProductMultilinear
          (d := d) OS lgc n k
          (section43PositiveEnergyQuotientMap (d := d) n
            (section43NPointTimeSpatialTensor d n
              (section43TimeProductTensor
                (fun i : Fin n =>
                  section43OneSidedLaplaceSchwartzRepresentative1D (gs1 i)))
              (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
          (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
          (fun i : Fin k => section43ImagAxisPsiKernel (ξ i)) *
        (section43TimeProductSource gs2).f ξ) =
      OS.S (n + k)
        (ZeroDiagonalSchwartz.ofClassical
          (src1.f.osConjTensorProduct src2.f)) := by
  intro src1 src2
  let u : Section43PositiveEnergyComponent (d := d) n :=
    section43PositiveEnergyQuotientMap (d := d) n
      (section43NPointTimeSpatialTensor d n
        (section43TimeProductTensor
          (fun i : Fin n =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs1 i)))
        (SchwartzMap.fourierTransformCLM ℂ kappa1.1))
  let chi2 : SchwartzMap (Section43SpatialSpace d k) ℂ :=
    SchwartzMap.fourierTransformCLM ℂ kappa2.1
  let T : SchwartzMap (Fin k → ℝ) ℂ →L[ℂ] ℂ :=
    bvt_W_pairing_descended_timeSpatialRightCLM
      (d := d) OS lgc n k u chi2
  have hprod :
      bvt_W_pairing_descended_timeSpatialRightProductMultilinear
          (d := d) OS lgc n k u chi2
          (fun i : Fin k =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs2 i)) =
        OS.S (n + k)
          (ZeroDiagonalSchwartz.ofClassical
            (src1.f.osConjTensorProduct src2.f)) := by
    simpa [u, chi2, src1, src2] using
      bvt_pairing_productSource_eq_osScalar_explicitOrderedSources
        d n k OS lgc gs1 kappa1 gs2 kappa2
  have hflat :=
    section43TimeProductTensor_allSlots_flattened
      T gs2 (fun _ : Fin k => 0)
  calc
    (∫ ξ : Fin k → ℝ,
        bvt_W_pairing_descended_timeSpatialRightProductMultilinear
          (d := d) OS lgc n k u chi2
          (fun i : Fin k => section43ImagAxisPsiKernel (ξ i)) *
        (section43TimeProductSource gs2).f ξ) =
      T (section43TimeProductTensor
        (fun i : Fin k =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs2 i))) := by
        simpa [T, bvt_W_pairing_descended_timeSpatialRightProductMultilinear,
          section43TimeImagAxisProductKernel] using hflat.symm
    _ =
      bvt_W_pairing_descended_timeSpatialRightProductMultilinear
          (d := d) OS lgc n k u chi2
          (fun i : Fin k =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs2 i)) := by
        rfl
    _ =
      OS.S (n + k)
        (ZeroDiagonalSchwartz.ofClassical
          (src1.f.osConjTensorProduct src2.f)) := hprod

/-- Producer-side selected source-current packet for the compact BVT
imaginary-axis product integral.

The cutoff current is built from the raw Euclidean spatial source, while the
BVT probe uses the Fourier-transformed spatial source on the frequency side.
The theorem only identifies the compact product integral with the value
selected by that current at `(section43TimeProductSource gs2).f`; it does not
assert a pointwise imaginary-axis kernel identity for the cutoff current. -/
theorem integral_bvt_timeSpatialRightProductMultilinear_imagAxis_eq_selected_fixedLeftOrderedPullbackCutoffZeroCLM
    (n k : ℕ)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (gs1 : Fin n → Section43CompactPositiveTimeSource1D)
    (kappa1 : Section43SpatialCompactSource d n)
    (gs2 : Fin k → Section43CompactPositiveTimeSource1D)
    (kappa2 : Section43SpatialCompactSource d k) :
    ∃ η : SchwartzMap (Fin k → ℝ) ℂ,
      (∀ x ∈ tsupport ((section43TimeProductSource gs2).f :
          (Fin k → ℝ) → ℂ), η x = 1) ∧
      tsupport (η : (Fin k → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion k ∧
      ∃ Z : SchwartzMap (Fin k → ℝ) ℂ →L[ℂ]
          ZeroDiagonalSchwartz d (n + k),
        (∀ φ,
          (Z φ).1 =
            (section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
                (section43TimeProductSource gs1).f).osConjTensorProduct
              (section43OrderedPullbackTimeSpatialTensorCLM d k kappa2.1
                (SchwartzMap.smulLeftCLM ℂ
                  (η : (Fin k → ℝ) → ℂ) φ))) ∧
        (∫ ξ : Fin k → ℝ,
            bvt_W_pairing_descended_timeSpatialRightProductMultilinear
              (d := d) OS lgc n k
              (section43PositiveEnergyQuotientMap (d := d) n
                (section43NPointTimeSpatialTensor d n
                  (section43TimeProductTensor
                    (fun i : Fin n =>
                      section43OneSidedLaplaceSchwartzRepresentative1D
                        (gs1 i)))
                  (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
              (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
              (fun i : Fin k => section43ImagAxisPsiKernel (ξ i)) *
            (section43TimeProductSource gs2).f ξ) =
          OS.S (n + k) (Z (section43TimeProductSource gs2).f) := by
  classical
  let fLeft : SchwartzNPoint d n :=
    section43OrderedPullbackTimeSpatialTensorCLM d n kappa1.1
      (section43TimeProductSource gs1).f
  have hfLeft :
      tsupport (fLeft : NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n := by
    simpa [fLeft] using
      section43OrderedPullbackTimeSpatialTensorCLM_tsupport_subset_orderedPositive_of_tsupport_strictPositive
        d n kappa1.1 (section43TimeProductSource gs1).f
        (section43TimeProductSource gs1).positive
  rcases
    exists_section43FixedLeftOrderedPullbackCutoffZeroCLM
      (d := d) fLeft hfLeft kappa2.1
      (section43TimeProductSource gs2) with
  ⟨η, hη_one, hη_support, Z, hZ_coe, hZ_product⟩
  refine ⟨η, hη_one, hη_support, Z, ?_, ?_⟩
  · intro φ
    simpa [fLeft] using hZ_coe φ
  · let right : SchwartzNPoint d k :=
      section43OrderedPullbackTimeSpatialTensorCLM d k
        kappa2.1 (section43TimeProductSource gs2).f
    let F : SchwartzNPoint d (n + k) := fLeft.osConjTensorProduct right
    have hright :
        tsupport (right : NPointDomain d k → ℂ) ⊆
          OrderedPositiveTimeRegion d k := by
      simpa [right] using
        section43OrderedPullbackTimeSpatialTensorCLM_tsupport_subset_orderedPositive_of_tsupport_strictPositive
          d k kappa2.1
          (section43TimeProductSource gs2).f
          (section43TimeProductSource gs2).positive
    have hvanish : VanishesToInfiniteOrderOnCoincidence F := by
      simpa [F] using
        VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
          (d := d) fLeft right hfLeft hright
    have hZ_eq :
        Z (section43TimeProductSource gs2).f =
          ZeroDiagonalSchwartz.ofClassical F := by
      apply Subtype.ext
      have hZ_val :
          (Z (section43TimeProductSource gs2).f).1 = F := by
        simpa [F, right] using congrArg Subtype.val hZ_product
      calc
        (Z (section43TimeProductSource gs2).f).1 = F := hZ_val
        _ = (ZeroDiagonalSchwartz.ofClassical F).1 := by
          exact
            (ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
              (f := F) hvanish).symm
    calc
      (∫ ξ : Fin k → ℝ,
          bvt_W_pairing_descended_timeSpatialRightProductMultilinear
            (d := d) OS lgc n k
            (section43PositiveEnergyQuotientMap (d := d) n
              (section43NPointTimeSpatialTensor d n
                (section43TimeProductTensor
                  (fun i : Fin n =>
                    section43OneSidedLaplaceSchwartzRepresentative1D
                      (gs1 i)))
                (SchwartzMap.fourierTransformCLM ℂ kappa1.1)))
            (SchwartzMap.fourierTransformCLM ℂ kappa2.1)
            (fun i : Fin k => section43ImagAxisPsiKernel (ξ i)) *
          (section43TimeProductSource gs2).f ξ) =
        OS.S (n + k) (ZeroDiagonalSchwartz.ofClassical F) := by
          simpa [F, right, fLeft] using
            integral_bvt_timeSpatialRightProductMultilinear_imagAxis_eq_osScalar_explicitOrderedSources
              (d := d) n k OS lgc gs1 kappa1 gs2 kappa2
      _ = OS.S (n + k) (Z (section43TimeProductSource gs2).f) := by
          rw [hZ_eq]

/-- The checked OS-II `ψ_Z` time-shift bridge through the descended Section
4.3 pairing.

This is the quotient-safe transport packet for the single successor-right
edge: the approach and the weight are exactly those in
`section43TimeShiftKernel_psiZ_pairing_eq_osScalar_of_transformComponent_succRight`.
It rewrites only the raw Wightman scalar in that theorem through
`bvt_W_pairing_descended_frequencyProjection_apply`; no extra branch equality
is assumed. -/
theorem section43TimeShiftKernel_psiZ_descended_pairing_eq_osScalar_of_transformComponent_succRight
    (d n m : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d (m + 1))
    (hg_ord :
      tsupport (g : NPointDomain d (m + 1) → ℂ) ⊆
        OrderedPositiveTimeRegion d (m + 1))
    (hg_compact : HasCompactSupport (g : NPointDomain d (m + 1) → ℂ))
    (hφ_freq :
      section43FrequencyProjection (d := d) n φ =
        section43FourierLaplaceTransformComponent d n f hf_ord hf_compact)
    (hψ_freq :
      section43FrequencyProjection (d := d) (m + 1) ψ =
        section43FourierLaplaceTransformComponent d (m + 1) g hg_ord hg_compact)
    {t : ℝ} (ht : 0 < t) :
    (∫ τ : ℝ,
      bvt_W_pairing_descended_frequencyProjection
          (d := d) OS lgc n (m + 1)
          (section43FrequencyProjection (d := d) n φ)
          (section43FrequencyProjection (d := d) (m + 1)
            (timeShiftSchwartzNPoint (d := d) τ ψ)) *
        (SchwartzMap.fourierTransformCLM ℂ
          (section43PsiZTimeTest t ht)) τ) =
      OS.S (n + (m + 1))
        (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t g))) := by
  calc
    (∫ τ : ℝ,
      bvt_W_pairing_descended_frequencyProjection
          (d := d) OS lgc n (m + 1)
          (section43FrequencyProjection (d := d) n φ)
          (section43FrequencyProjection (d := d) (m + 1)
            (timeShiftSchwartzNPoint (d := d) τ ψ)) *
        (SchwartzMap.fourierTransformCLM ℂ
          (section43PsiZTimeTest t ht)) τ)
        =
      ∫ τ : ℝ,
        bvt_W OS lgc (n + (m + 1))
          (φ.conjTensorProduct
            (timeShiftSchwartzNPoint (d := d) τ ψ)) *
          (SchwartzMap.fourierTransformCLM ℂ
            (section43PsiZTimeTest t ht)) τ := by
        refine integral_congr_ae ?_
        filter_upwards with τ
        rw [bvt_W_pairing_descended_frequencyProjection_apply]
    _ =
      OS.S (n + (m + 1))
        (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t g))) :=
        section43TimeShiftKernel_psiZ_pairing_eq_osScalar_of_transformComponent_succRight
          (d := d) (n := n) (m := m) OS lgc φ ψ
          f hf_ord hf_compact g hg_ord hg_compact hφ_freq hψ_freq ht

/-- Canonical-target form of the descended `ψ_Z` edge packet.

The left component is exactly the Fourier-Laplace transform component of the
compact ordered source, and the right ambient representative is the canonical
transform-component target for the right source. -/
theorem section43TimeShiftKernel_psiZ_descended_transformComponentTarget_eq_osScalar_succRight
    (d n m : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d (m + 1))
    (hg_ord :
      tsupport (g : NPointDomain d (m + 1) → ℂ) ⊆
        OrderedPositiveTimeRegion d (m + 1))
    (hg_compact : HasCompactSupport (g : NPointDomain d (m + 1) → ℂ))
    {t : ℝ} (ht : 0 < t) :
    (∫ τ : ℝ,
      bvt_W_pairing_descended_frequencyProjection
          (d := d) OS lgc n (m + 1)
          (section43FourierLaplaceTransformComponent d n f hf_ord hf_compact)
          (section43FrequencyProjection (d := d) (m + 1)
            (timeShiftSchwartzNPoint (d := d) τ
              (section43TransformComponentTarget d (m + 1)
                g hg_ord hg_compact))) *
        (SchwartzMap.fourierTransformCLM ℂ
          (section43PsiZTimeTest t ht)) τ) =
      OS.S (n + (m + 1))
        (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t g))) := by
  let φ : SchwartzNPoint d n :=
    section43TransformComponentTarget d n f hf_ord hf_compact
  let ψ : SchwartzNPoint d (m + 1) :=
    section43TransformComponentTarget d (m + 1) g hg_ord hg_compact
  have hφ_freq :
      section43FrequencyProjection (d := d) n φ =
        section43FourierLaplaceTransformComponent d n f hf_ord hf_compact := by
    simpa [φ] using
      section43TransformComponentTarget_freq_eq d n f hf_ord hf_compact
  have hψ_freq :
      section43FrequencyProjection (d := d) (m + 1) ψ =
        section43FourierLaplaceTransformComponent d (m + 1) g hg_ord hg_compact := by
    simpa [ψ] using
      section43TransformComponentTarget_freq_eq d (m + 1) g hg_ord hg_compact
  simpa [φ, ψ, hφ_freq] using
    section43TimeShiftKernel_psiZ_descended_pairing_eq_osScalar_of_transformComponent_succRight
      (d := d) (n := n) (m := m) OS lgc φ ψ
      f hf_ord hf_compact g hg_ord hg_compact hφ_freq hψ_freq ht

/-- Left-shifted canonical-target form of the descended `ψ_Z` edge packet.

This is the BVT/source-current bridge used by the common-time transport lane:
the existing successor-right edge theorem is instantiated with a nonnegative
common Euclidean time shift on the left source. -/
theorem section43TimeShiftKernel_psiZ_descended_transformComponentTarget_eq_osScalar_succRight_leftTimeShift
    (d n m : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (a : ℝ) (ha : 0 ≤ a)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d (m + 1))
    (hg_ord :
      tsupport (g : NPointDomain d (m + 1) → ℂ) ⊆
        OrderedPositiveTimeRegion d (m + 1))
    (hg_compact : HasCompactSupport (g : NPointDomain d (m + 1) → ℂ))
    {t : ℝ} (ht : 0 < t) :
    (∫ τ : ℝ,
      bvt_W_pairing_descended_frequencyProjection
          (d := d) OS lgc n (m + 1)
          (section43FourierLaplaceTransformComponent d n
            (timeShiftSchwartzNPoint (d := d) a f)
            (timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport_of_nonneg
              a ha f hf_ord)
            (hasCompactSupport_timeShiftSchwartzNPoint
              (d := d) (n := n) a f hf_compact))
          (section43FrequencyProjection (d := d) (m + 1)
            (timeShiftSchwartzNPoint (d := d) τ
              (section43TransformComponentTarget d (m + 1)
                g hg_ord hg_compact))) *
        (SchwartzMap.fourierTransformCLM ℂ
          (section43PsiZTimeTest t ht)) τ) =
      OS.S (n + (m + 1))
        (ZeroDiagonalSchwartz.ofClassical
          ((timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t g))) := by
  exact
    section43TimeShiftKernel_psiZ_descended_transformComponentTarget_eq_osScalar_succRight
      (d := d) (n := n) (m := m) OS lgc
      (timeShiftSchwartzNPoint (d := d) a f)
      (timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport_of_nonneg
        a ha f hf_ord)
      (hasCompactSupport_timeShiftSchwartzNPoint
        (d := d) (n := n) a f hf_compact)
      g hg_ord hg_compact ht

/-- Concrete BVT selector for common-left-shifted successor-right shells.

If two actual descended Section 4.3 `ψ_Z` source-current integrals agree, then
the Schwinger values selected by those integrals agree.  This is the
non-abstract handoff for the common-time transport lane: the remaining producer
is equality of the concrete BVT integrals, not an assumed time-shell kernel. -/
theorem eq_leftShifted_schwinger_timeShift_of_bvt_psiZ_integrals_eq
    (d n₁ m₁ n₂ m₂ : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (a₁ : ℝ) (ha₁ : 0 ≤ a₁)
    (f₁ : SchwartzNPoint d n₁)
    (hf₁_ord : tsupport (f₁ : NPointDomain d n₁ → ℂ) ⊆
      OrderedPositiveTimeRegion d n₁)
    (hf₁_compact : HasCompactSupport (f₁ : NPointDomain d n₁ → ℂ))
    (g₁ : SchwartzNPoint d (m₁ + 1))
    (hg₁_ord :
      tsupport (g₁ : NPointDomain d (m₁ + 1) → ℂ) ⊆
        OrderedPositiveTimeRegion d (m₁ + 1))
    (hg₁_compact : HasCompactSupport (g₁ : NPointDomain d (m₁ + 1) → ℂ))
    (a₂ : ℝ) (ha₂ : 0 ≤ a₂)
    (f₂ : SchwartzNPoint d n₂)
    (hf₂_ord : tsupport (f₂ : NPointDomain d n₂ → ℂ) ⊆
      OrderedPositiveTimeRegion d n₂)
    (hf₂_compact : HasCompactSupport (f₂ : NPointDomain d n₂ → ℂ))
    (g₂ : SchwartzNPoint d (m₂ + 1))
    (hg₂_ord :
      tsupport (g₂ : NPointDomain d (m₂ + 1) → ℂ) ⊆
        OrderedPositiveTimeRegion d (m₂ + 1))
    (hg₂_compact : HasCompactSupport (g₂ : NPointDomain d (m₂ + 1) → ℂ))
    {t : ℝ} (ht : 0 < t)
    (hBVT :
      (∫ τ : ℝ,
        bvt_W_pairing_descended_frequencyProjection
            (d := d) OS lgc n₁ (m₁ + 1)
            (section43FourierLaplaceTransformComponent d n₁
              (timeShiftSchwartzNPoint (d := d) a₁ f₁)
              (timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport_of_nonneg
                a₁ ha₁ f₁ hf₁_ord)
              (hasCompactSupport_timeShiftSchwartzNPoint
                (d := d) (n := n₁) a₁ f₁ hf₁_compact))
            (section43FrequencyProjection (d := d) (m₁ + 1)
              (timeShiftSchwartzNPoint (d := d) τ
                (section43TransformComponentTarget d (m₁ + 1)
                  g₁ hg₁_ord hg₁_compact))) *
          (SchwartzMap.fourierTransformCLM ℂ
            (section43PsiZTimeTest t ht)) τ) =
        ∫ τ : ℝ,
          bvt_W_pairing_descended_frequencyProjection
              (d := d) OS lgc n₂ (m₂ + 1)
              (section43FourierLaplaceTransformComponent d n₂
                (timeShiftSchwartzNPoint (d := d) a₂ f₂)
                (timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport_of_nonneg
                  a₂ ha₂ f₂ hf₂_ord)
                (hasCompactSupport_timeShiftSchwartzNPoint
                  (d := d) (n := n₂) a₂ f₂ hf₂_compact))
              (section43FrequencyProjection (d := d) (m₂ + 1)
                (timeShiftSchwartzNPoint (d := d) τ
                  (section43TransformComponentTarget d (m₂ + 1)
                    g₂ hg₂_ord hg₂_compact))) *
            (SchwartzMap.fourierTransformCLM ℂ
              (section43PsiZTimeTest t ht)) τ) :
    OS.S (n₁ + (m₁ + 1))
        (ZeroDiagonalSchwartz.ofClassical
          ((timeShiftSchwartzNPoint (d := d) a₁ f₁).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t g₁))) =
      OS.S (n₂ + (m₂ + 1))
        (ZeroDiagonalSchwartz.ofClassical
          ((timeShiftSchwartzNPoint (d := d) a₂ f₂).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t g₂))) := by
  have h₁ :=
    section43TimeShiftKernel_psiZ_descended_transformComponentTarget_eq_osScalar_succRight_leftTimeShift
      (d := d) n₁ m₁ OS lgc a₁ ha₁ f₁ hf₁_ord hf₁_compact
      g₁ hg₁_ord hg₁_compact ht
  have h₂ :=
    section43TimeShiftKernel_psiZ_descended_transformComponentTarget_eq_osScalar_succRight_leftTimeShift
      (d := d) n₂ m₂ OS lgc a₂ ha₂ f₂ hf₂_ord hf₂_compact
      g₂ hg₂_ord hg₂_compact ht
  exact h₁.symm.trans (hBVT.trans h₂)

/-- One-sided product-source evaluation for a shifted Schwinger shell.

This is the producer-side form needed to compare the BVT compact-source real
edge with the OS-II total semigroup branch.  A genuine time-shell CLM `Z` whose
strict-positive imaginary-axis kernels are the shifted Schwinger shells
evaluates on a compact product source by the corresponding shifted-shell
integral. -/
theorem schwinger_shiftedShell_productSource_integral_eq_timeCLM_on_positive
    (OS : OsterwalderSchraderAxioms d)
    {m : ℕ} [Nonempty (Fin m)]
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (Z : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ZeroDiagonalSchwartz d (n + r))
    (hZ : ∀ (ξ : Fin m → ℝ) (hξ : ξ ∈ section43TimeStrictPositiveRegion m),
      Z (section43TimeImagAxisProductKernel ξ) =
        ⟨f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g),
          VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_sum_of_strictPositive
            (d := d) f hf_ord g hg_ord ξ hξ⟩)
    (gs : Fin m → Section43CompactPositiveTimeSource1D) :
    (∫ ξ : Fin m → ℝ,
      OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, ξ p) g))) *
        (section43TimeProductSource gs).f ξ) =
      OS.S (n + r)
        (Z (section43TimeProductTensor
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) := by
  let T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ :=
    (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS (n + r)).comp Z
  have hflat :=
    section43TimeProductTensor_allSlots_flattened
      T gs (fun _ : Fin m => 0)
  calc
    (∫ ξ : Fin m → ℝ,
      OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, ξ p) g))) *
        (section43TimeProductSource gs).f ξ)
        =
      ∫ ξ : Fin m → ℝ,
        T (section43TimeImagAxisProductKernel ξ) *
          (section43TimeProductSource gs).f ξ := by
        refine
          integral_mul_eq_of_eqOn_tsupport
            (fun ξ : Fin m → ℝ =>
              OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
                (f.osConjTensorProduct
                  (timeShiftSchwartzNPoint (d := d)
                    (∑ p : Fin m, ξ p) g))))
            (fun ξ : Fin m → ℝ =>
              T (section43TimeImagAxisProductKernel ξ))
            ((section43TimeProductSource gs).f : (Fin m → ℝ) → ℂ)
            ?_
        intro ξ hξ
        have hξpos : ξ ∈ section43TimeStrictPositiveRegion m :=
          (section43TimeProductSource gs).positive hξ
        calc
          OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
              (f.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d)
                  (∑ p : Fin m, ξ p) g)))
              =
            OS.S (n + r)
              (⟨f.osConjTensorProduct
                  (timeShiftSchwartzNPoint (d := d)
                    (∑ p : Fin m, ξ p) g),
                VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_sum_of_strictPositive
                  (d := d) f hf_ord g hg_ord ξ hξpos⟩) := by
                rw [ZeroDiagonalSchwartz_ofClassical_osConjTensorProduct_timeShift_sum_of_strictPositive
                  (d := d) f hf_ord g hg_ord ξ hξpos]
          _ =
            OS.S (n + r)
              (Z (section43TimeImagAxisProductKernel ξ)) := by
                rw [hZ ξ hξpos]
          _ =
            T (section43TimeImagAxisProductKernel ξ) := by
                rfl
    _ =
      T (section43TimeProductTensor
        (fun i : Fin m =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) :=
        hflat.symm
    _ =
      OS.S (n + r)
        (Z (section43TimeProductTensor
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) := by
        rfl

/-- Product-source evaluation for a common-time left-shifted Schwinger shell.

This is the CLM/Fubini interface for the common-time transport lane: on the
strict-positive imaginary-axis the time-shell CLM carries the left-shifted
Schwinger shell, and compact positive product sources integrate exactly those
shell values. -/
theorem schwinger_leftShiftedShell_productSource_integral_eq_timeCLM_on_positive
    (OS : OsterwalderSchraderAxioms d)
    {m : ℕ} [Nonempty (Fin m)]
    {n r : ℕ}
    (a : ℝ) (ha : 0 ≤ a)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (Z : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ZeroDiagonalSchwartz d (n + r))
    (hZ : ∀ (ξ : Fin m → ℝ) (hξ : ξ ∈ section43TimeStrictPositiveRegion m),
      Z (section43TimeImagAxisProductKernel ξ) =
        ⟨(timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g),
          VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_leftTimeShift_timeShift_sum_of_strictPositive
            (d := d) a ha f hf_ord g hg_ord ξ hξ⟩)
    (gs : Fin m → Section43CompactPositiveTimeSource1D) :
    (∫ ξ : Fin m → ℝ,
      OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
        ((timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, ξ p) g))) *
        (section43TimeProductSource gs).f ξ) =
      OS.S (n + r)
        (Z (section43TimeProductTensor
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) := by
  exact
    schwinger_shiftedShell_productSource_integral_eq_timeCLM_on_positive
      (d := d) OS
      (timeShiftSchwartzNPoint (d := d) a f)
      (timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport_of_nonneg
        a ha f hf_ord)
      g hg_ord Z hZ gs

/-- Localized product-source evaluation for a common-time left-shifted
Schwinger shell.

For a fixed compact positive product source, the time-shell CLM only has to
agree with the honest shifted-shell kernel on that source's topological support.
This is the producer-facing form needed by cutoff source currents: the global
strict-positive kernel identity is stronger than necessary for one compact
source. -/
theorem schwinger_leftShiftedShell_productSource_integral_eq_timeCLM_on_tsupport
    (OS : OsterwalderSchraderAxioms d)
    {m : ℕ} [Nonempty (Fin m)]
    {n r : ℕ}
    (a : ℝ) (ha : 0 ≤ a)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (Z : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ZeroDiagonalSchwartz d (n + r))
    (gs : Fin m → Section43CompactPositiveTimeSource1D)
    (hZ : ∀ (ξ : Fin m → ℝ)
      (hξ : ξ ∈ tsupport ((section43TimeProductSource gs).f : (Fin m → ℝ) → ℂ)),
      Z (section43TimeImagAxisProductKernel ξ) =
        ⟨(timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g),
          VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_leftTimeShift_timeShift_sum_of_strictPositive
            (d := d) a ha f hf_ord g hg_ord ξ
            ((section43TimeProductSource gs).positive hξ)⟩) :
    (∫ ξ : Fin m → ℝ,
      OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
        ((timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, ξ p) g))) *
        (section43TimeProductSource gs).f ξ) =
      OS.S (n + r)
        (Z (section43TimeProductTensor
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) := by
  let T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ :=
    (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS (n + r)).comp Z
  have hflat :=
    section43TimeProductTensor_allSlots_flattened
      T gs (fun _ : Fin m => 0)
  calc
    (∫ ξ : Fin m → ℝ,
      OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
        ((timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, ξ p) g))) *
        (section43TimeProductSource gs).f ξ)
        =
      ∫ ξ : Fin m → ℝ,
        T (section43TimeImagAxisProductKernel ξ) *
          (section43TimeProductSource gs).f ξ := by
        refine
          integral_mul_eq_of_eqOn_tsupport
            (fun ξ : Fin m → ℝ =>
              OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
                ((timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
                  (timeShiftSchwartzNPoint (d := d)
                    (∑ p : Fin m, ξ p) g))))
            (fun ξ : Fin m → ℝ =>
              T (section43TimeImagAxisProductKernel ξ))
            ((section43TimeProductSource gs).f : (Fin m → ℝ) → ℂ)
            ?_
        intro ξ hξ
        have hξpos : ξ ∈ section43TimeStrictPositiveRegion m :=
          (section43TimeProductSource gs).positive hξ
        calc
          OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
              ((timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d)
                  (∑ p : Fin m, ξ p) g)))
              =
            OS.S (n + r)
              (⟨(timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
                  (timeShiftSchwartzNPoint (d := d)
                    (∑ p : Fin m, ξ p) g),
                VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_leftTimeShift_timeShift_sum_of_strictPositive
                  (d := d) a ha f hf_ord g hg_ord ξ hξpos⟩) := by
                rw [ZeroDiagonalSchwartz_ofClassical_osConjTensorProduct_leftTimeShift_timeShift_sum_of_strictPositive
                  (d := d) a ha f hf_ord g hg_ord ξ hξpos]
          _ =
            OS.S (n + r)
              (Z (section43TimeImagAxisProductKernel ξ)) := by
                rw [hZ ξ hξ]
          _ =
            T (section43TimeImagAxisProductKernel ξ) := by
                rfl
    _ =
      T (section43TimeProductTensor
        (fun i : Fin m =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) :=
        hflat.symm
    _ =
      OS.S (n + r)
        (Z (section43TimeProductTensor
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) := by
        rfl

omit [NeZero d] in
private theorem timeShiftSchwartzNPoint_zero_eq_local
    (a : ℝ) (f : SchwartzNPoint d 0) :
    timeShiftSchwartzNPoint (d := d) a f = f := by
  ext y
  rw [timeShiftSchwartzNPoint_apply]
  congr 1
  ext i
  exact Fin.elim0 i

/-- Vacuum-left specialization of the common-time source-current shell.

If the time-shell CLM carries the common-left-shifted honest kernel, then for a
zero-point left source its compact product-source value is already the
unshifted Schwinger shell.  This is the source-current form of the OS `E1`
transport becoming invisible on the vacuum-left factor. -/
theorem schwinger_leftShiftedShell_vacuumLeft_productSource_integral_eq_timeCLM_on_tsupport
    (OS : OsterwalderSchraderAxioms d)
    {m : ℕ} [Nonempty (Fin m)]
    {r : ℕ}
    (a : ℝ) (ha : 0 ≤ a)
    (f0 : SchwartzNPoint d 0)
    (hf0_ord : tsupport (f0 : NPointDomain d 0 → ℂ) ⊆
      OrderedPositiveTimeRegion d 0)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (Z : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ZeroDiagonalSchwartz d (0 + r))
    (gs : Fin m → Section43CompactPositiveTimeSource1D)
    (hZ : ∀ (ξ : Fin m → ℝ)
      (hξ : ξ ∈ tsupport ((section43TimeProductSource gs).f : (Fin m → ℝ) → ℂ)),
      Z (section43TimeImagAxisProductKernel ξ) =
        ⟨(timeShiftSchwartzNPoint (d := d) a f0).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g),
          VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_leftTimeShift_timeShift_sum_of_strictPositive
            (d := d) a ha f0 hf0_ord g hg_ord ξ
            ((section43TimeProductSource gs).positive hξ)⟩) :
    (∫ ξ : Fin m → ℝ,
      OS.S (0 + r) (ZeroDiagonalSchwartz.ofClassical
        (f0.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, ξ p) g))) *
        (section43TimeProductSource gs).f ξ) =
      OS.S (0 + r)
        (Z (section43TimeProductTensor
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) := by
  have hshift0 :
      timeShiftSchwartzNPoint (d := d) a f0 = f0 :=
    timeShiftSchwartzNPoint_zero_eq_local (d := d) a f0
  have hleft :=
    schwinger_leftShiftedShell_productSource_integral_eq_timeCLM_on_tsupport
      (d := d) OS a ha f0 hf0_ord g hg_ord Z gs hZ
  calc
    (∫ ξ : Fin m → ℝ,
      OS.S (0 + r) (ZeroDiagonalSchwartz.ofClassical
        (f0.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, ξ p) g))) *
        (section43TimeProductSource gs).f ξ)
        =
      ∫ ξ : Fin m → ℝ,
        OS.S (0 + r) (ZeroDiagonalSchwartz.ofClassical
          ((timeShiftSchwartzNPoint (d := d) a f0).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g))) *
          (section43TimeProductSource gs).f ξ := by
        refine integral_congr_ae ?_
        filter_upwards with ξ
        rw [hshift0]
    _ =
      OS.S (0 + r)
        (Z (section43TimeProductTensor
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) := hleft

/-- Vacuum-left pointwise BVT kernel recovery from left-shifted compact-source
pairings.

The delta-smearing step first recovers the common-left-shifted shell.  Because
the left source has arity zero, the common shift is trivial, so the recovered
BVT imaginary-axis value is the unshifted vacuum-left Schwinger shell. -/
theorem bvt_imagAxis_eq_vacuumLeftShell_of_leftShifted_productSource_pairings_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m r : ℕ} [Nonempty (Fin m)]
    (u : Section43PositiveEnergyComponent (d := d) 0)
    (χ : SchwartzMap (Section43SpatialSpace d m) ℂ)
    (a : ℝ) (ha : 0 ≤ a)
    (f0 : SchwartzNPoint d 0)
    (hf0_ord : tsupport (f0 : NPointDomain d 0 → ℂ) ⊆
      OrderedPositiveTimeRegion d 0)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (x0 : Fin m → ℝ) (hx0 : ∀ i : Fin m, 0 < x0 i)
    (hpair :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        (∫ ξ : Fin m → ℝ,
          bvt_W_pairing_descended_timeSpatialRightProductMultilinear
              (d := d) OS lgc 0 m u χ
              (fun i : Fin m => section43ImagAxisPsiKernel (ξ i)) *
            (section43TimeProductSource gs).f ξ) =
          ∫ ξ : Fin m → ℝ,
            OS.S (0 + r)
              (ZeroDiagonalSchwartz.ofClassical
                ((timeShiftSchwartzNPoint (d := d) a f0).osConjTensorProduct
                  (timeShiftSchwartzNPoint (d := d)
                    (∑ p : Fin m, ξ p) g))) *
              (section43TimeProductSource gs).f ξ) :
    bvt_W_pairing_descended_timeSpatialRightProductMultilinear
        (d := d) OS lgc 0 m u χ
        (fun i : Fin m => section43ImagAxisPsiKernel (x0 i)) =
      OS.S (0 + r)
        (ZeroDiagonalSchwartz.ofClassical
          (f0.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, x0 p) g))) := by
  have hshift0 :
      timeShiftSchwartzNPoint (d := d) a f0 = f0 :=
    timeShiftSchwartzNPoint_zero_eq_local (d := d) a f0
  have hleft :=
    bvt_imagAxis_eq_leftShiftedShell_of_productSource_pairings_eq
      (d := d) OS lgc u χ a ha f0 hf0_ord g hg_ord hg_compact x0 hx0 hpair
  calc
    bvt_W_pairing_descended_timeSpatialRightProductMultilinear
        (d := d) OS lgc 0 m u χ
        (fun i : Fin m => section43ImagAxisPsiKernel (x0 i)) =
      OS.S (0 + r)
        (ZeroDiagonalSchwartz.ofClassical
          ((timeShiftSchwartzNPoint (d := d) a f0).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, x0 p) g))) := hleft
    _ =
      OS.S (0 + r)
        (ZeroDiagonalSchwartz.ofClassical
          (f0.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, x0 p) g))) := by
        rw [hshift0]

/-- Two-source total-time convolution form of the left-shifted Schwinger shell
CLM identity.

This is the source-current transport needed by the OS-II shell lane.  The
left-shifted Schwinger shell is first identified on the compact positive
two-variable product source, then the actual Section 4.3 shear pushes that
product source to the one-dimensional total-time convolution. -/
theorem schwinger_leftShiftedShell_fin_two_convolution_integral_eq_timeCLM_on_tsupport
    (OS : OsterwalderSchraderAxioms d)
    {n r : ℕ}
    (a : ℝ) (ha : 0 ≤ a)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (Z : SchwartzMap (Fin 2 → ℝ) ℂ →L[ℂ] ZeroDiagonalSchwartz d (n + r))
    (gs : Fin 2 → Section43CompactPositiveTimeSource1D)
    (hZ : ∀ (ξ : Fin 2 → ℝ)
      (hξ : ξ ∈ tsupport ((section43TimeProductSource gs).f :
        (Fin 2 → ℝ) → ℂ)),
      Z (section43TimeImagAxisProductKernel ξ) =
        ⟨(timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin 2, ξ p) g),
          VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_leftTimeShift_timeShift_sum_of_strictPositive
            (d := d) a ha f hf_ord g hg_ord ξ
            ((section43TimeProductSource gs).positive hξ)⟩) :
    (∫ t : ℝ,
      OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
        ((timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) t g))) *
        (section43CompactPositiveTimeSource1D_convolution
          (gs 0) (gs 1)).f t) =
      OS.S (n + r)
        (Z (section43TimeProductTensor
          (fun i : Fin 2 =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) := by
  let K : ℝ → ℂ := fun t =>
    OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
      ((timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
        (timeShiftSchwartzNPoint (d := d) t g)))
  have hf_shift_ord :
      tsupport (((timeShiftSchwartzNPoint (d := d) a f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ)) ⊆ OrderedPositiveTimeRegion d n :=
    timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport_of_nonneg
      (d := d) a ha f hf_ord
  have hK_cont :
      ContinuousOn K (Set.Ioi 0) := by
    simpa [K] using
      continuousOn_os_pairing_term_timeShift_of_isCompactSupport
        (d := d) OS (timeShiftSchwartzNPoint (d := d) a f) g
        hf_shift_ord hg_ord hg_compact
  have hpush :
      (∫ ξ : Fin 2 → ℝ,
        K (∑ p : Fin 2, ξ p) *
          (section43TimeProductSource gs).f ξ) =
        ∫ t : ℝ,
          K t *
            (section43CompactPositiveTimeSource1D_convolution
              (gs 0) (gs 1)).f t :=
    section43_totalTimeProductSource_integral_fin_two_convolution
      K gs
      (section43_totalTimeProductSource_integrable_fin_two_convolution_kernel_of_continuousOn_Ioi
        K hK_cont gs)
  have hshell :
      (∫ ξ : Fin 2 → ℝ,
        K (∑ p : Fin 2, ξ p) *
          (section43TimeProductSource gs).f ξ) =
        OS.S (n + r)
          (Z (section43TimeProductTensor
            (fun i : Fin 2 =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) := by
    simpa [K] using
      schwinger_leftShiftedShell_productSource_integral_eq_timeCLM_on_tsupport
        (d := d) OS a ha f hf_ord g hg_ord Z gs hZ
  exact hpush.symm.trans hshell

/-- Direct pointwise common-left-shifted Schwinger-shell equality from
positive-branch split pairings.

This is the OS-II real-edge consumer before the BVT/time-shell layer: once the
two left-shifted positive-branch split pairings agree against every compact
positive product source, the positive-orthant delta argument identifies the
corresponding left-shifted Schwinger shells pointwise. -/
theorem eq_leftShifted_schwinger_timeShift_single_of_positiveBranch_pairings_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    {n₁ r₁ n₂ r₂ : ℕ}
    (a₁ : ℝ) (ha₁ : 0 ≤ a₁)
    (f₁ : SchwartzNPoint d n₁)
    (hf₁_ord : tsupport (f₁ : NPointDomain d n₁ → ℂ) ⊆
      OrderedPositiveTimeRegion d n₁)
    (g₁ : SchwartzNPoint d r₁)
    (hg₁_ord : tsupport (g₁ : NPointDomain d r₁ → ℂ) ⊆
      OrderedPositiveTimeRegion d r₁)
    (hg₁_compact : HasCompactSupport (g₁ : NPointDomain d r₁ → ℂ))
    (a₂ : ℝ) (ha₂ : 0 ≤ a₂)
    (f₂ : SchwartzNPoint d n₂)
    (hf₂_ord : tsupport (f₂ : NPointDomain d n₂ → ℂ) ⊆
      OrderedPositiveTimeRegion d n₂)
    (g₂ : SchwartzNPoint d r₂)
    (hg₂_ord : tsupport (g₂ : NPointDomain d r₂ → ℂ) ⊆
      OrderedPositiveTimeRegion d r₂)
    (hg₂_compact : HasCompactSupport (g₂ : NPointDomain d r₂ → ℂ))
    (x0 : Fin m → ℝ) (hx0 : ∀ i : Fin m, 0 < x0 i)
    (q₁ q₂ : Fin m)
    (hbranch :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        (∫ ξ : Fin m → ℝ,
          (if hξ : ∀ p : Fin m, 0 ≤ ξ p then
            OSInnerProduct d OS.S
              (osiiLeftSplitPositiveBranch (d := d) ξ hξ
                (timeShiftNonnegPositiveTimeBorchers (d := d) a₁ ha₁
                  (PositiveTimeBorchersSequence.single n₁ f₁ hf₁_ord)) q₁ :
                  BorchersSequence d)
              (timeShiftBorchers (d := d) (ξ q₁)
                (osiiRightSplitPositiveBranch (d := d) ξ hξ
                  (PositiveTimeBorchersSequence.single r₁ g₁ hg₁_ord) q₁ :
                    BorchersSequence d))
          else 0) * (section43TimeProductSource gs).f ξ) =
          ∫ ξ : Fin m → ℝ,
            (if hξ : ∀ p : Fin m, 0 ≤ ξ p then
              OSInnerProduct d OS.S
                (osiiLeftSplitPositiveBranch (d := d) ξ hξ
                  (timeShiftNonnegPositiveTimeBorchers (d := d) a₂ ha₂
                    (PositiveTimeBorchersSequence.single n₂ f₂ hf₂_ord)) q₂ :
                    BorchersSequence d)
                (timeShiftBorchers (d := d) (ξ q₂)
                  (osiiRightSplitPositiveBranch (d := d) ξ hξ
                    (PositiveTimeBorchersSequence.single r₂ g₂ hg₂_ord) q₂ :
                      BorchersSequence d))
            else 0) * (section43TimeProductSource gs).f ξ) :
    OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
        ((timeShiftSchwartzNPoint (d := d) a₁ f₁).osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, x0 p) g₁))) =
      OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
        ((timeShiftSchwartzNPoint (d := d) a₂ f₂).osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, x0 p) g₂))) := by
  have hf₁_shift :
      tsupport (((timeShiftSchwartzNPoint (d := d) a₁ f₁ :
        SchwartzNPoint d n₁) : NPointDomain d n₁ → ℂ)) ⊆
        OrderedPositiveTimeRegion d n₁ :=
    timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport_of_nonneg
      a₁ ha₁ f₁ hf₁_ord
  have hf₂_shift :
      tsupport (((timeShiftSchwartzNPoint (d := d) a₂ f₂ :
        SchwartzNPoint d n₂) : NPointDomain d n₂ → ℂ)) ⊆
        OrderedPositiveTimeRegion d n₂ :=
    timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport_of_nonneg
      a₂ ha₂ f₂ hf₂_ord
  refine
    eq_schwinger_timeShift_single_of_positiveOrthant_productSource_pairings_eq
      (d := d) OS lgc
      (timeShiftSchwartzNPoint (d := d) a₁ f₁) hf₁_shift
      g₁ hg₁_ord hg₁_compact
      (timeShiftSchwartzNPoint (d := d) a₂ f₂) hf₂_shift
      g₂ hg₂_ord hg₂_compact x0 hx0 ?_
  exact
    schwinger_leftShifted_productSource_pairings_eq_of_positiveBranch_pairings_eq
      (d := d) OS
      a₁ ha₁ f₁ hf₁_ord g₁ hg₁_ord
      a₂ ha₂ f₂ hf₂_ord g₂ hg₂_ord q₁ q₂ hbranch

/-- Product-source pairing equality after the scalar probes have been produced
from concrete zero-diagonal time-shell CLMs. -/
theorem section43_productSource_pairing_eq_of_schwinger_timeCLM_eq
    (OS : OsterwalderSchraderAxioms d)
    {m k₁ k₂ : ℕ}
    (Z₁ : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ZeroDiagonalSchwartz d k₁)
    (Z₂ : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ZeroDiagonalSchwartz d k₂)
    (K₁ K₂ : (Fin m → ℝ) → ℂ)
    (hK₁ : ∀ ξ : Fin m → ℝ,
      OS.S k₁ (Z₁ (section43TimeImagAxisProductKernel ξ)) = K₁ ξ)
    (hK₂ : ∀ ξ : Fin m → ℝ,
      OS.S k₂ (Z₂ (section43TimeImagAxisProductKernel ξ)) = K₂ ξ)
    (hprod :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        OS.S k₁ (Z₁ (section43TimeProductTensor
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) =
          OS.S k₂ (Z₂ (section43TimeProductTensor
            (fun i : Fin m =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i))))) :
    ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
      (∫ ξ : Fin m → ℝ, K₁ ξ * (section43TimeProductSource gs).f ξ) =
        ∫ ξ : Fin m → ℝ, K₂ ξ * (section43TimeProductSource gs).f ξ := by
  refine
    section43_productSource_pairing_eq_of_timeProductTensor_multilinear_eq
      (section43SchwingerTimeProductMultilinearOfCLM
        (d := d) OS Z₁)
      (section43SchwingerTimeProductMultilinearOfCLM
        (d := d) OS Z₂)
      K₁ K₂ ?_ ?_ ?_
  · intro ξ
    simpa [section43TimeImagAxisProductKernel] using hK₁ ξ
  · intro ξ
    simpa [section43TimeImagAxisProductKernel] using hK₂ ξ
  · intro gs
    simpa using hprod gs

/-- Product-source pairing equality from zero-diagonal time-shell CLMs when the
imaginary-axis kernel identifications are only known on the strict positive
orthant.  Compact product sources never see the complementary region. -/
theorem section43_productSource_pairing_eq_of_schwinger_timeCLM_eq_on_positive
    (OS : OsterwalderSchraderAxioms d)
    {m k₁ k₂ : ℕ}
    (Z₁ : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ZeroDiagonalSchwartz d k₁)
    (Z₂ : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ZeroDiagonalSchwartz d k₂)
    (K₁ K₂ : (Fin m → ℝ) → ℂ)
    (hK₁ : ∀ ξ : Fin m → ℝ, ξ ∈ section43TimeStrictPositiveRegion m →
      OS.S k₁ (Z₁ (section43TimeImagAxisProductKernel ξ)) = K₁ ξ)
    (hK₂ : ∀ ξ : Fin m → ℝ, ξ ∈ section43TimeStrictPositiveRegion m →
      OS.S k₂ (Z₂ (section43TimeImagAxisProductKernel ξ)) = K₂ ξ)
    (hprod :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        OS.S k₁ (Z₁ (section43TimeProductTensor
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) =
          OS.S k₂ (Z₂ (section43TimeProductTensor
            (fun i : Fin m =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i))))) :
    ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
      (∫ ξ : Fin m → ℝ, K₁ ξ * (section43TimeProductSource gs).f ξ) =
        ∫ ξ : Fin m → ℝ, K₂ ξ * (section43TimeProductSource gs).f ξ := by
  refine
    section43_productSource_pairing_eq_of_timeProductTensor_multilinear_eq_on_positive
      (section43SchwingerTimeProductMultilinearOfCLM
        (d := d) OS Z₁)
      (section43SchwingerTimeProductMultilinearOfCLM
        (d := d) OS Z₂)
      K₁ K₂ ?_ ?_ ?_
  · intro ξ hξ
    simpa [section43TimeImagAxisProductKernel] using hK₁ ξ hξ
  · intro ξ hξ
    simpa [section43TimeImagAxisProductKernel] using hK₂ ξ hξ
  · intro gs
    simpa using hprod gs

/-- One-sided Laplace product equality for concrete Schwinger time-shell CLMs,
derived from positive-orthant kernel identification and compact product-source
pairing equality.

This is the OS-II product-source Fubini step in the reverse direction from
`section43_productSource_pairing_eq_of_schwinger_timeCLM_eq_on_positive`: once
the scalar kernels have been identified on the strict positive support of the
source, equality of those compact-source pairings supplies the `hprod` input
for the Schwinger time-CLM consumer. -/
theorem section43_schwinger_timeCLM_oneSidedLaplaceProduct_eq_of_pairings_eq_on_positive
    (OS : OsterwalderSchraderAxioms d)
    {m k₁ k₂ : ℕ}
    (Z₁ : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ZeroDiagonalSchwartz d k₁)
    (Z₂ : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ZeroDiagonalSchwartz d k₂)
    (K₁ K₂ : (Fin m → ℝ) → ℂ)
    (hK₁ : ∀ ξ : Fin m → ℝ, ξ ∈ section43TimeStrictPositiveRegion m →
      OS.S k₁ (Z₁ (section43TimeImagAxisProductKernel ξ)) = K₁ ξ)
    (hK₂ : ∀ ξ : Fin m → ℝ, ξ ∈ section43TimeStrictPositiveRegion m →
      OS.S k₂ (Z₂ (section43TimeImagAxisProductKernel ξ)) = K₂ ξ)
    (hpair :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        (∫ ξ : Fin m → ℝ, K₁ ξ * (section43TimeProductSource gs).f ξ) =
          ∫ ξ : Fin m → ℝ, K₂ ξ * (section43TimeProductSource gs).f ξ) :
    ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
      OS.S k₁ (Z₁ (section43TimeProductTensor
        (fun i : Fin m =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) =
        OS.S k₂ (Z₂ (section43TimeProductTensor
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) := by
  intro gs
  let T₁ : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ :=
    (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS k₁).comp Z₁
  let T₂ : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ :=
    (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS k₂).comp Z₂
  have hleft :=
    section43TimeProductTensor_allSlots_flattened
      T₁ gs (fun _ : Fin m => 0)
  have hright :=
    section43TimeProductTensor_allSlots_flattened
      T₂ gs (fun _ : Fin m => 0)
  change
    T₁ (section43TimeProductTensor
      (fun i : Fin m =>
        section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) =
      T₂ (section43TimeProductTensor
        (fun i : Fin m =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))
  calc
    T₁ (section43TimeProductTensor
        (fun i : Fin m =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))
        =
      ∫ ξ : Fin m → ℝ,
        T₁ (section43TimeImagAxisProductKernel ξ) *
          (section43TimeProductSource gs).f ξ := hleft
    _ =
      ∫ ξ : Fin m → ℝ, K₁ ξ * (section43TimeProductSource gs).f ξ := by
        refine
          integral_mul_eq_of_eqOn_tsupport
            (fun ξ : Fin m → ℝ =>
              T₁ (section43TimeImagAxisProductKernel ξ))
            K₁
            ((section43TimeProductSource gs).f : (Fin m → ℝ) → ℂ)
            ?_
        intro ξ hξ
        change OS.S k₁ (Z₁ (section43TimeImagAxisProductKernel ξ)) = K₁ ξ
        exact hK₁ ξ ((section43TimeProductSource gs).positive hξ)
    _ =
      ∫ ξ : Fin m → ℝ, K₂ ξ * (section43TimeProductSource gs).f ξ :=
        hpair gs
    _ =
      ∫ ξ : Fin m → ℝ,
        T₂ (section43TimeImagAxisProductKernel ξ) *
          (section43TimeProductSource gs).f ξ := by
        exact
          integral_mul_eq_of_eqOn_tsupport
            K₂
            (fun ξ : Fin m → ℝ =>
              T₂ (section43TimeImagAxisProductKernel ξ))
            ((section43TimeProductSource gs).f : (Fin m → ℝ) → ℂ)
            (fun ξ hξ =>
              (hK₂ ξ ((section43TimeProductSource gs).positive hξ)).symm)
    _ =
      T₂ (section43TimeProductTensor
        (fun i : Fin m =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) :=
        hright.symm

/-- One-sided Laplace product equality for two branch-specific time-shell CLMs
with the same honest positive imaginary-axis kernel.

The compact product-source pairing identity is not assumed here: it is supplied
by the checked OS positive-branch semigroup equality for the two split
coordinates, then transported to shifted Schwinger-shell pairings by
`schwinger_shifted_productSource_pairings_eq_of_positiveBranch_pairings_eq`. -/
theorem section43_schwinger_timeCLM_oneSidedLaplaceProduct_eq_of_same_honest_kernel
    (OS : OsterwalderSchraderAxioms d)
    {m : ℕ} [Nonempty (Fin m)]
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (q₁ q₂ : Fin m)
    (Z₁ Z₂ : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n + r))
    (hZ₁ : ∀ ξ : Fin m → ℝ, ∀ hξ : ξ ∈ section43TimeStrictPositiveRegion m,
      Z₁ (section43TimeImagAxisProductKernel ξ) =
        ⟨f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g),
          VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_sum_of_strictPositive
            (d := d) f hf_ord g hg_ord ξ hξ⟩)
    (hZ₂ : ∀ ξ : Fin m → ℝ, ∀ hξ : ξ ∈ section43TimeStrictPositiveRegion m,
      Z₂ (section43TimeImagAxisProductKernel ξ) =
        ⟨f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g),
          VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_sum_of_strictPositive
            (d := d) f hf_ord g hg_ord ξ hξ⟩) :
    ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
      OS.S (n + r) (Z₁ (section43TimeProductTensor
        (fun i : Fin m =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) =
        OS.S (n + r) (Z₂ (section43TimeProductTensor
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) := by
  refine
    section43_schwinger_timeCLM_oneSidedLaplaceProduct_eq_of_pairings_eq_on_positive
      (d := d) OS Z₁ Z₂
      (fun ξ : Fin m → ℝ =>
        OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g))))
      (fun ξ : Fin m → ℝ =>
        OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g))))
      ?_ ?_ ?_
  · intro ξ hξ
    rw [hZ₁ ξ hξ]
    rw [← ZeroDiagonalSchwartz_ofClassical_osConjTensorProduct_timeShift_sum_of_strictPositive
      (d := d) f hf_ord g hg_ord ξ hξ]
  · intro ξ hξ
    rw [hZ₂ ξ hξ]
    rw [← ZeroDiagonalSchwartz_ofClassical_osConjTensorProduct_timeShift_sum_of_strictPositive
      (d := d) f hf_ord g hg_ord ξ hξ]
  · refine
      schwinger_shifted_productSource_pairings_eq_of_positiveBranch_pairings_eq
        (d := d) OS f hf_ord g hg_ord f hf_ord g hg_ord q₁ q₂ ?_
    intro gs
    exact
      integral_osii_real_edge_positiveBranch_pairings_agree_of_tsupport_positive
        (d := d) OS
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single r g hg_ord)
        q₁ q₂ (section43TimeProductSource gs).f
        (section43TimeProductSource gs).positive

/-- One-sided Laplace product equality for two branch-specific time-shell CLMs
with the same honest common-time left-shifted positive imaginary-axis kernel.

The compact product-source pairing identity is supplied by the OS-II
positive-branch semigroup equality after the common nonnegative time shift is
absorbed into the left Borchers vector. -/
theorem section43_schwinger_timeCLM_oneSidedLaplaceProduct_eq_of_same_leftShifted_honest_kernel
    (OS : OsterwalderSchraderAxioms d)
    {m : ℕ} [Nonempty (Fin m)]
    {n r : ℕ}
    (a : ℝ) (ha : 0 ≤ a)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (q₁ q₂ : Fin m)
    (Z₁ Z₂ : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n + r))
    (hZ₁ : ∀ ξ : Fin m → ℝ, ∀ hξ : ξ ∈ section43TimeStrictPositiveRegion m,
      Z₁ (section43TimeImagAxisProductKernel ξ) =
        ⟨(timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g),
          VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_leftTimeShift_timeShift_sum_of_strictPositive
            (d := d) a ha f hf_ord g hg_ord ξ hξ⟩)
    (hZ₂ : ∀ ξ : Fin m → ℝ, ∀ hξ : ξ ∈ section43TimeStrictPositiveRegion m,
      Z₂ (section43TimeImagAxisProductKernel ξ) =
        ⟨(timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g),
          VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_leftTimeShift_timeShift_sum_of_strictPositive
            (d := d) a ha f hf_ord g hg_ord ξ hξ⟩) :
    ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
      OS.S (n + r) (Z₁ (section43TimeProductTensor
        (fun i : Fin m =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) =
        OS.S (n + r) (Z₂ (section43TimeProductTensor
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) := by
  refine
    section43_schwinger_timeCLM_oneSidedLaplaceProduct_eq_of_pairings_eq_on_positive
      (d := d) OS Z₁ Z₂
      (fun ξ : Fin m → ℝ =>
        OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
          ((timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g))))
      (fun ξ : Fin m → ℝ =>
        OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
          ((timeShiftSchwartzNPoint (d := d) a f).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g))))
      ?_ ?_ ?_
  · intro ξ hξ
    rw [hZ₁ ξ hξ]
    rw [← ZeroDiagonalSchwartz_ofClassical_osConjTensorProduct_leftTimeShift_timeShift_sum_of_strictPositive
      (d := d) a ha f hf_ord g hg_ord ξ hξ]
  · intro ξ hξ
    rw [hZ₂ ξ hξ]
    rw [← ZeroDiagonalSchwartz_ofClassical_osConjTensorProduct_leftTimeShift_timeShift_sum_of_strictPositive
      (d := d) a ha f hf_ord g hg_ord ξ hξ]
  · refine
      schwinger_leftShifted_productSource_pairings_eq_of_positiveBranch_pairings_eq
        (d := d) OS
        a ha f hf_ord g hg_ord
        a ha f hf_ord g hg_ord q₁ q₂ ?_
    intro gs
    exact
      integral_osii_real_edge_positiveBranch_pairings_agree_of_tsupport_positive
        (d := d) OS
        (timeShiftNonnegPositiveTimeBorchers (d := d) a ha
          (PositiveTimeBorchersSequence.single n f hf_ord))
        (PositiveTimeBorchersSequence.single r g hg_ord)
        q₁ q₂ (section43TimeProductSource gs).f
        (section43TimeProductSource gs).positive

/-- Concentrated shifted-shell equality from concrete zero-diagonal time-shell
CLMs.  This is the Schwinger-functional version of the OS-II product-source
consumer: the remaining producer is to construct the two CLMs and prove their
kernel/restricted-source identities. -/
theorem eq_schwinger_timeShift_single_of_schwinger_timeCLM_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    {n₁ r₁ n₂ r₂ : ℕ}
    (f₁ : SchwartzNPoint d n₁)
    (hf₁_ord : tsupport (f₁ : NPointDomain d n₁ → ℂ) ⊆
      OrderedPositiveTimeRegion d n₁)
    (g₁ : SchwartzNPoint d r₁)
    (hg₁_ord : tsupport (g₁ : NPointDomain d r₁ → ℂ) ⊆
      OrderedPositiveTimeRegion d r₁)
    (hg₁_compact : HasCompactSupport (g₁ : NPointDomain d r₁ → ℂ))
    (f₂ : SchwartzNPoint d n₂)
    (hf₂_ord : tsupport (f₂ : NPointDomain d n₂ → ℂ) ⊆
      OrderedPositiveTimeRegion d n₂)
    (g₂ : SchwartzNPoint d r₂)
    (hg₂_ord : tsupport (g₂ : NPointDomain d r₂ → ℂ) ⊆
      OrderedPositiveTimeRegion d r₂)
    (hg₂_compact : HasCompactSupport (g₂ : NPointDomain d r₂ → ℂ))
    (x0 : Fin m → ℝ) (hx0 : ∀ i : Fin m, 0 < x0 i)
    (Z₁ : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n₁ + r₁))
    (Z₂ : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n₂ + r₂))
    (hK₁ : ∀ ξ : Fin m → ℝ,
      OS.S (n₁ + r₁) (Z₁ (section43TimeImagAxisProductKernel ξ)) =
        OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
          (f₁.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₁))))
    (hK₂ : ∀ ξ : Fin m → ℝ,
      OS.S (n₂ + r₂) (Z₂ (section43TimeImagAxisProductKernel ξ)) =
        OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
          (f₂.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₂))))
    (hprod :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        OS.S (n₁ + r₁) (Z₁ (section43TimeProductTensor
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) =
          OS.S (n₂ + r₂) (Z₂ (section43TimeProductTensor
            (fun i : Fin m =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i))))) :
    OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
        (f₁.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, x0 p) g₁))) =
      OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
        (f₂.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, x0 p) g₂))) := by
  refine
    eq_schwinger_timeShift_single_of_timeProductTensor_multilinear_eq
      (d := d) OS lgc
      f₁ hf₁_ord g₁ hg₁_ord hg₁_compact
      f₂ hf₂_ord g₂ hg₂_ord hg₂_compact
      x0 hx0
      (section43SchwingerTimeProductMultilinearOfCLM
        (d := d) OS Z₁)
      (section43SchwingerTimeProductMultilinearOfCLM
        (d := d) OS Z₂)
      ?_ ?_ ?_
  · intro ξ
    simpa [section43TimeImagAxisProductKernel] using hK₁ ξ
  · intro ξ
    simpa [section43TimeImagAxisProductKernel] using hK₂ ξ
  · intro gs
    simpa using hprod gs

/-- Concentrated shifted-shell equality from concrete zero-diagonal time-shell
CLMs, with imaginary-axis kernel identities localized to the strict positive
orthant. -/
theorem eq_schwinger_timeShift_single_of_schwinger_timeCLM_eq_on_positive
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    {n₁ r₁ n₂ r₂ : ℕ}
    (f₁ : SchwartzNPoint d n₁)
    (hf₁_ord : tsupport (f₁ : NPointDomain d n₁ → ℂ) ⊆
      OrderedPositiveTimeRegion d n₁)
    (g₁ : SchwartzNPoint d r₁)
    (hg₁_ord : tsupport (g₁ : NPointDomain d r₁ → ℂ) ⊆
      OrderedPositiveTimeRegion d r₁)
    (hg₁_compact : HasCompactSupport (g₁ : NPointDomain d r₁ → ℂ))
    (f₂ : SchwartzNPoint d n₂)
    (hf₂_ord : tsupport (f₂ : NPointDomain d n₂ → ℂ) ⊆
      OrderedPositiveTimeRegion d n₂)
    (g₂ : SchwartzNPoint d r₂)
    (hg₂_ord : tsupport (g₂ : NPointDomain d r₂ → ℂ) ⊆
      OrderedPositiveTimeRegion d r₂)
    (hg₂_compact : HasCompactSupport (g₂ : NPointDomain d r₂ → ℂ))
    (x0 : Fin m → ℝ) (hx0 : ∀ i : Fin m, 0 < x0 i)
    (Z₁ : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n₁ + r₁))
    (Z₂ : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n₂ + r₂))
    (hK₁ : ∀ ξ : Fin m → ℝ, ξ ∈ section43TimeStrictPositiveRegion m →
      OS.S (n₁ + r₁) (Z₁ (section43TimeImagAxisProductKernel ξ)) =
        OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
          (f₁.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₁))))
    (hK₂ : ∀ ξ : Fin m → ℝ, ξ ∈ section43TimeStrictPositiveRegion m →
      OS.S (n₂ + r₂) (Z₂ (section43TimeImagAxisProductKernel ξ)) =
        OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
          (f₂.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₂))))
    (hprod :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        OS.S (n₁ + r₁) (Z₁ (section43TimeProductTensor
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) =
          OS.S (n₂ + r₂) (Z₂ (section43TimeProductTensor
            (fun i : Fin m =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i))))) :
    OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
        (f₁.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, x0 p) g₁))) =
      OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
        (f₂.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, x0 p) g₂))) := by
  refine
    eq_schwinger_timeShift_single_of_positiveOrthant_productSource_pairings_eq
      (d := d) OS lgc
      f₁ hf₁_ord g₁ hg₁_ord hg₁_compact
      f₂ hf₂_ord g₂ hg₂_ord hg₂_compact
      x0 hx0 ?_
  exact
    section43_productSource_pairing_eq_of_schwinger_timeCLM_eq_on_positive
      (d := d) OS Z₁ Z₂
      (fun ξ : Fin m → ℝ =>
        OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
          (f₁.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₁))))
      (fun ξ : Fin m → ℝ =>
        OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
          (f₂.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₂))))
      hK₁ hK₂ hprod

/-- Concentrated shifted-shell equality from zero-diagonal time-shell CLMs whose
positive imaginary-axis kernels are identified as honest shifted-shell subtypes
in `ZeroDiagonalSchwartz`. -/
theorem eq_schwinger_timeShift_single_of_schwinger_timeCLM_honest_kernel_eq_on_positive
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    {n₁ r₁ n₂ r₂ : ℕ}
    (f₁ : SchwartzNPoint d n₁)
    (hf₁_ord : tsupport (f₁ : NPointDomain d n₁ → ℂ) ⊆
      OrderedPositiveTimeRegion d n₁)
    (g₁ : SchwartzNPoint d r₁)
    (hg₁_ord : tsupport (g₁ : NPointDomain d r₁ → ℂ) ⊆
      OrderedPositiveTimeRegion d r₁)
    (hg₁_compact : HasCompactSupport (g₁ : NPointDomain d r₁ → ℂ))
    (f₂ : SchwartzNPoint d n₂)
    (hf₂_ord : tsupport (f₂ : NPointDomain d n₂ → ℂ) ⊆
      OrderedPositiveTimeRegion d n₂)
    (g₂ : SchwartzNPoint d r₂)
    (hg₂_ord : tsupport (g₂ : NPointDomain d r₂ → ℂ) ⊆
      OrderedPositiveTimeRegion d r₂)
    (hg₂_compact : HasCompactSupport (g₂ : NPointDomain d r₂ → ℂ))
    (x0 : Fin m → ℝ) (hx0 : ∀ i : Fin m, 0 < x0 i)
    (Z₁ : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n₁ + r₁))
    (Z₂ : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n₂ + r₂))
    (hZ₁ : ∀ ξ : Fin m → ℝ, ∀ hξ : ξ ∈ section43TimeStrictPositiveRegion m,
      Z₁ (section43TimeImagAxisProductKernel ξ) =
        ⟨f₁.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₁),
          VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_sum_of_strictPositive
            (d := d) f₁ hf₁_ord g₁ hg₁_ord ξ hξ⟩)
    (hZ₂ : ∀ ξ : Fin m → ℝ, ∀ hξ : ξ ∈ section43TimeStrictPositiveRegion m,
      Z₂ (section43TimeImagAxisProductKernel ξ) =
        ⟨f₂.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₂),
          VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_sum_of_strictPositive
            (d := d) f₂ hf₂_ord g₂ hg₂_ord ξ hξ⟩)
    (hprod :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        OS.S (n₁ + r₁) (Z₁ (section43TimeProductTensor
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) =
          OS.S (n₂ + r₂) (Z₂ (section43TimeProductTensor
            (fun i : Fin m =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i))))) :
    OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
        (f₁.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, x0 p) g₁))) =
      OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
        (f₂.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, x0 p) g₂))) := by
  refine
    eq_schwinger_timeShift_single_of_schwinger_timeCLM_eq_on_positive
      (d := d) OS lgc
      f₁ hf₁_ord g₁ hg₁_ord hg₁_compact
      f₂ hf₂_ord g₂ hg₂_ord hg₂_compact
      x0 hx0 Z₁ Z₂ ?_ ?_ hprod
  · intro ξ hξ
    rw [hZ₁ ξ hξ]
    rw [ZeroDiagonalSchwartz_ofClassical_osConjTensorProduct_timeShift_sum_of_strictPositive
      (d := d) f₁ hf₁_ord g₁ hg₁_ord ξ hξ]
  · intro ξ hξ
    rw [hZ₂ ξ hξ]
    rw [ZeroDiagonalSchwartz_ofClassical_osConjTensorProduct_timeShift_sum_of_strictPositive
      (d := d) f₂ hf₂_ord g₂ hg₂_ord ξ hξ]

/-- Concentrated shifted-shell equality from honest positive kernels and the
compact product-source pairing identity.

This packages the current OS-II producer obligation in the form closest to the
book argument: the time-shell CLMs identify the strict-positive
imaginary-axis kernels as honest shifted Schwinger shells, and the remaining
distributional step supplies equality of compact positive product-source
pairings.  The one-sided Laplace representative equality is then supplied by
`section43_schwinger_timeCLM_oneSidedLaplaceProduct_eq_of_pairings_eq_on_positive`. -/
theorem eq_schwinger_timeShift_single_of_schwinger_timeCLM_honest_kernel_eq_and_pairings
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    {n₁ r₁ n₂ r₂ : ℕ}
    (f₁ : SchwartzNPoint d n₁)
    (hf₁_ord : tsupport (f₁ : NPointDomain d n₁ → ℂ) ⊆
      OrderedPositiveTimeRegion d n₁)
    (g₁ : SchwartzNPoint d r₁)
    (hg₁_ord : tsupport (g₁ : NPointDomain d r₁ → ℂ) ⊆
      OrderedPositiveTimeRegion d r₁)
    (hg₁_compact : HasCompactSupport (g₁ : NPointDomain d r₁ → ℂ))
    (f₂ : SchwartzNPoint d n₂)
    (hf₂_ord : tsupport (f₂ : NPointDomain d n₂ → ℂ) ⊆
      OrderedPositiveTimeRegion d n₂)
    (g₂ : SchwartzNPoint d r₂)
    (hg₂_ord : tsupport (g₂ : NPointDomain d r₂ → ℂ) ⊆
      OrderedPositiveTimeRegion d r₂)
    (hg₂_compact : HasCompactSupport (g₂ : NPointDomain d r₂ → ℂ))
    (x0 : Fin m → ℝ) (hx0 : ∀ i : Fin m, 0 < x0 i)
    (Z₁ : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n₁ + r₁))
    (Z₂ : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n₂ + r₂))
    (hZ₁ : ∀ ξ : Fin m → ℝ, ∀ hξ : ξ ∈ section43TimeStrictPositiveRegion m,
      Z₁ (section43TimeImagAxisProductKernel ξ) =
        ⟨f₁.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₁),
          VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_sum_of_strictPositive
            (d := d) f₁ hf₁_ord g₁ hg₁_ord ξ hξ⟩)
    (hZ₂ : ∀ ξ : Fin m → ℝ, ∀ hξ : ξ ∈ section43TimeStrictPositiveRegion m,
      Z₂ (section43TimeImagAxisProductKernel ξ) =
        ⟨f₂.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₂),
          VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_sum_of_strictPositive
            (d := d) f₂ hf₂_ord g₂ hg₂_ord ξ hξ⟩)
    (hpair :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        (∫ ξ : Fin m → ℝ,
          OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
            (f₁.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d)
                (∑ p : Fin m, ξ p) g₁))) *
            (section43TimeProductSource gs).f ξ) =
          ∫ ξ : Fin m → ℝ,
            OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
              (f₂.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d)
                  (∑ p : Fin m, ξ p) g₂))) *
              (section43TimeProductSource gs).f ξ) :
    OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
        (f₁.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, x0 p) g₁))) =
      OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
        (f₂.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, x0 p) g₂))) := by
  refine
    eq_schwinger_timeShift_single_of_schwinger_timeCLM_honest_kernel_eq_on_positive
      (d := d) OS lgc
      f₁ hf₁_ord g₁ hg₁_ord hg₁_compact
      f₂ hf₂_ord g₂ hg₂_ord hg₂_compact
      x0 hx0 Z₁ Z₂ hZ₁ hZ₂ ?_
  refine
    section43_schwinger_timeCLM_oneSidedLaplaceProduct_eq_of_pairings_eq_on_positive
      (d := d) OS Z₁ Z₂
      (fun ξ : Fin m → ℝ =>
        OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
          (f₁.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₁))))
      (fun ξ : Fin m → ℝ =>
        OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
          (f₂.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₂))))
      ?_ ?_ hpair
  · intro ξ hξ
    rw [hZ₁ ξ hξ]
    rw [← ZeroDiagonalSchwartz_ofClassical_osConjTensorProduct_timeShift_sum_of_strictPositive
      (d := d) f₁ hf₁_ord g₁ hg₁_ord ξ hξ]
  · intro ξ hξ
    rw [hZ₂ ξ hξ]
    rw [← ZeroDiagonalSchwartz_ofClassical_osConjTensorProduct_timeShift_sum_of_strictPositive
      (d := d) f₂ hf₂_ord g₂ hg₂_ord ξ hξ]

/-- Concentrated left-shifted shifted-shell equality from honest time-shell
CLM kernels and equality of the corresponding left-shifted positive-branch
split pairings.

This is the pointwise OS-II `(A_0) -> (P_0)` consumer for the common-time
transport lane: the product-source delta-smearing step is supplied by
`eq_schwinger_timeShift_single_of_schwinger_timeCLM_honest_kernel_eq_and_pairings`,
while the compact source pairings are obtained from the genuine OS split
branch equality. -/
theorem eq_leftShifted_schwinger_timeShift_single_of_timeCLM_honest_kernel_eq_and_positiveBranch_pairings
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    {n₁ r₁ n₂ r₂ : ℕ}
    (a₁ : ℝ) (ha₁ : 0 ≤ a₁)
    (f₁ : SchwartzNPoint d n₁)
    (hf₁_ord : tsupport (f₁ : NPointDomain d n₁ → ℂ) ⊆
      OrderedPositiveTimeRegion d n₁)
    (g₁ : SchwartzNPoint d r₁)
    (hg₁_ord : tsupport (g₁ : NPointDomain d r₁ → ℂ) ⊆
      OrderedPositiveTimeRegion d r₁)
    (hg₁_compact : HasCompactSupport (g₁ : NPointDomain d r₁ → ℂ))
    (a₂ : ℝ) (ha₂ : 0 ≤ a₂)
    (f₂ : SchwartzNPoint d n₂)
    (hf₂_ord : tsupport (f₂ : NPointDomain d n₂ → ℂ) ⊆
      OrderedPositiveTimeRegion d n₂)
    (g₂ : SchwartzNPoint d r₂)
    (hg₂_ord : tsupport (g₂ : NPointDomain d r₂ → ℂ) ⊆
      OrderedPositiveTimeRegion d r₂)
    (hg₂_compact : HasCompactSupport (g₂ : NPointDomain d r₂ → ℂ))
    (x0 : Fin m → ℝ) (hx0 : ∀ i : Fin m, 0 < x0 i)
    (Z₁ : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n₁ + r₁))
    (Z₂ : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d (n₂ + r₂))
    (hZ₁ : ∀ ξ : Fin m → ℝ, ∀ hξ : ξ ∈ section43TimeStrictPositiveRegion m,
      Z₁ (section43TimeImagAxisProductKernel ξ) =
        ⟨(timeShiftSchwartzNPoint (d := d) a₁ f₁).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₁),
          VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_leftTimeShift_timeShift_sum_of_strictPositive
            (d := d) a₁ ha₁ f₁ hf₁_ord g₁ hg₁_ord ξ hξ⟩)
    (hZ₂ : ∀ ξ : Fin m → ℝ, ∀ hξ : ξ ∈ section43TimeStrictPositiveRegion m,
      Z₂ (section43TimeImagAxisProductKernel ξ) =
        ⟨(timeShiftSchwartzNPoint (d := d) a₂ f₂).osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (∑ p : Fin m, ξ p) g₂),
          VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_leftTimeShift_timeShift_sum_of_strictPositive
            (d := d) a₂ ha₂ f₂ hf₂_ord g₂ hg₂_ord ξ hξ⟩)
    (q₁ q₂ : Fin m)
    (hbranch :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        (∫ ξ : Fin m → ℝ,
          (if hξ : ∀ p : Fin m, 0 ≤ ξ p then
            OSInnerProduct d OS.S
              (osiiLeftSplitPositiveBranch (d := d) ξ hξ
                (timeShiftNonnegPositiveTimeBorchers (d := d) a₁ ha₁
                  (PositiveTimeBorchersSequence.single n₁ f₁ hf₁_ord)) q₁ :
                  BorchersSequence d)
              (timeShiftBorchers (d := d) (ξ q₁)
                (osiiRightSplitPositiveBranch (d := d) ξ hξ
                  (PositiveTimeBorchersSequence.single r₁ g₁ hg₁_ord) q₁ :
                    BorchersSequence d))
          else 0) * (section43TimeProductSource gs).f ξ) =
          ∫ ξ : Fin m → ℝ,
            (if hξ : ∀ p : Fin m, 0 ≤ ξ p then
              OSInnerProduct d OS.S
                (osiiLeftSplitPositiveBranch (d := d) ξ hξ
                  (timeShiftNonnegPositiveTimeBorchers (d := d) a₂ ha₂
                    (PositiveTimeBorchersSequence.single n₂ f₂ hf₂_ord)) q₂ :
                    BorchersSequence d)
                (timeShiftBorchers (d := d) (ξ q₂)
                  (osiiRightSplitPositiveBranch (d := d) ξ hξ
                    (PositiveTimeBorchersSequence.single r₂ g₂ hg₂_ord) q₂ :
                      BorchersSequence d))
            else 0) * (section43TimeProductSource gs).f ξ) :
    OS.S (n₁ + r₁) (ZeroDiagonalSchwartz.ofClassical
        ((timeShiftSchwartzNPoint (d := d) a₁ f₁).osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, x0 p) g₁))) =
      OS.S (n₂ + r₂) (ZeroDiagonalSchwartz.ofClassical
        ((timeShiftSchwartzNPoint (d := d) a₂ f₂).osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, x0 p) g₂))) := by
  have hf₁_shift :
      tsupport (((timeShiftSchwartzNPoint (d := d) a₁ f₁ :
        SchwartzNPoint d n₁) : NPointDomain d n₁ → ℂ)) ⊆
        OrderedPositiveTimeRegion d n₁ :=
    timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport_of_nonneg
      a₁ ha₁ f₁ hf₁_ord
  have hf₂_shift :
      tsupport (((timeShiftSchwartzNPoint (d := d) a₂ f₂ :
        SchwartzNPoint d n₂) : NPointDomain d n₂ → ℂ)) ⊆
        OrderedPositiveTimeRegion d n₂ :=
    timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport_of_nonneg
      a₂ ha₂ f₂ hf₂_ord
  refine
    eq_schwinger_timeShift_single_of_schwinger_timeCLM_honest_kernel_eq_and_pairings
      (d := d) OS lgc
      (timeShiftSchwartzNPoint (d := d) a₁ f₁) hf₁_shift
      g₁ hg₁_ord hg₁_compact
      (timeShiftSchwartzNPoint (d := d) a₂ f₂) hf₂_shift
      g₂ hg₂_ord hg₂_compact x0 hx0 Z₁ Z₂ ?_ ?_ ?_
  · intro ξ hξ
    rw [hZ₁ ξ hξ]
  · intro ξ hξ
    rw [hZ₂ ξ hξ]
  · exact
      schwinger_leftShifted_productSource_pairings_eq_of_positiveBranch_pairings_eq
        (d := d) OS
        a₁ ha₁ f₁ hf₁_ord g₁ hg₁_ord
        a₂ ha₂ f₂ hf₂_ord g₂ hg₂_ord q₁ q₂ hbranch

end OSReconstruction
