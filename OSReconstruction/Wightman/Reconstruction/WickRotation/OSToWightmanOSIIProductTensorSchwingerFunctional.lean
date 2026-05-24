import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceOrderedDensity

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

variable {d : ℕ} [NeZero d]

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

/-- Fixed-spatial Section 4.3 tensoring, as a continuous linear map from the
finite-time Schwartz space to spacetime Schwartz tests. -/
noncomputable def section43TimeSpatialTensorCLM
    (d n : ℕ) [NeZero d]
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ) :
    SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] SchwartzNPoint d n where
  toLinearMap :=
    { toFun := fun φ => section43NPointTimeSpatialTensor d n φ χ
      map_add' := by
        intro φ ψ
        ext q
        simp [section43NPointTimeSpatialTensor_apply, add_mul]
      map_smul' := by
        intro c φ
        ext q
        simp [section43NPointTimeSpatialTensor_apply, smul_eq_mul, mul_assoc] }
  cont := by
    let toFlat :
        SchwartzMap (Fin n → ℝ) ℂ →
          SchwartzMap (Fin (n + n * d) → ℝ) ℂ := fun φ =>
        SchwartzMap.tensorProduct φ (section43SpatialFlatSchwartzCLE d n χ)
    have hflat : Continuous toFlat := by
      simpa [toFlat] using
        (SchwartzMap.tensorProduct_continuous_left
          (E := ℝ) (m := n) (k := n * d)
          (section43SpatialFlatSchwartzCLE d n χ))
    let toTimeSpatial :
        SchwartzMap (Fin (n + n * d) → ℝ) ℂ →L[ℂ]
          SchwartzMap (Section43TimeSpatialSpace d n) ℂ :=
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (section43TimeSpatialFlatCLE d n)
    have hts :
        Continuous (fun φ : SchwartzMap (Fin n → ℝ) ℂ =>
          toTimeSpatial (toFlat φ)) :=
      toTimeSpatial.continuous.comp hflat
    let toNPoint :
        SchwartzMap (Section43TimeSpatialSpace d n) ℂ →L[ℂ]
          SchwartzNPoint d n :=
      (nPointTimeSpatialSchwartzCLE (d := d) (n := n)).symm
    have hn :
        Continuous (fun φ : SchwartzMap (Fin n → ℝ) ℂ =>
          toNPoint (toTimeSpatial (toFlat φ))) :=
      toNPoint.continuous.comp hts
    simpa [section43NPointTimeSpatialTensor, section43TimeSpatialTensor,
      toFlat, toTimeSpatial, toNPoint] using hn

@[simp] theorem section43TimeSpatialTensorCLM_apply
    (d n : ℕ) [NeZero d]
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (φ : SchwartzMap (Fin n → ℝ) ℂ) :
    section43TimeSpatialTensorCLM d n χ φ =
      section43NPointTimeSpatialTensor d n φ χ := rfl

/-- The ordered Euclidean pullback of the fixed-spatial Section 4.3 tensoring
map.  This is linear on all finite-time Schwartz tests; zero-diagonal
membership is supplied separately for tests whose difference-time support lies
in the strict positive orthant. -/
noncomputable def section43OrderedPullbackTimeSpatialTensorCLM
    (d n : ℕ) [NeZero d]
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ) :
    SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] SchwartzNPoint d n :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (section43DiffCoordRealCLE d n)).comp
      (section43TimeSpatialTensorCLM d n χ)

@[simp] theorem section43OrderedPullbackTimeSpatialTensorCLM_apply
    (d n : ℕ) [NeZero d]
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (φ : SchwartzMap (Fin n → ℝ) ℂ) :
    section43OrderedPullbackTimeSpatialTensorCLM d n χ φ =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (section43DiffCoordRealCLE d n)
        (section43NPointTimeSpatialTensor d n φ χ) := rfl

theorem section43OrderedPullbackTimeSpatialTensorCLM_mem_zeroDiagonal_of_tsupport_strictPositive
    (d n : ℕ) [NeZero d]
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (φ : SchwartzMap (Fin n → ℝ) ℂ)
    (hφ : tsupport (φ : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n) :
    VanishesToInfiniteOrderOnCoincidence
      (section43OrderedPullbackTimeSpatialTensorCLM d n χ φ) := by
  simpa using
    VanishesToInfiniteOrderOnCoincidence_orderedPullback_section43NPointTimeSpatialTensor
      d n φ χ hφ

/-- Fixed-spatial Section 4.3 tensoring into the zero-diagonal test space,
provided the fixed spatial block keeps every time factor away from the
coincidence locus to infinite order. -/
noncomputable def section43TimeSpatialTensorZeroCLM
    (d n : ℕ) [NeZero d]
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (hχ_vanish : ∀ φ : SchwartzMap (Fin n → ℝ) ℂ,
      VanishesToInfiniteOrderOnCoincidence
        (section43NPointTimeSpatialTensor d n φ χ)) :
    SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ZeroDiagonalSchwartz d n where
  toLinearMap :=
    { toFun := fun φ =>
        ⟨section43NPointTimeSpatialTensor d n φ χ, hχ_vanish φ⟩
      map_add' := by
        intro φ ψ
        apply Subtype.ext
        change section43NPointTimeSpatialTensor d n (φ + ψ) χ =
          section43NPointTimeSpatialTensor d n φ χ +
            section43NPointTimeSpatialTensor d n ψ χ
        ext q
        simp [section43NPointTimeSpatialTensor_apply, add_mul]
      map_smul' := by
        intro c φ
        apply Subtype.ext
        change section43NPointTimeSpatialTensor d n (c • φ) χ =
          c • section43NPointTimeSpatialTensor d n φ χ
        ext q
        simp [section43NPointTimeSpatialTensor_apply, smul_eq_mul, mul_assoc] }
  cont := by
    exact
      (section43TimeSpatialTensorCLM d n χ).continuous.subtype_mk
        hχ_vanish

@[simp] theorem section43TimeSpatialTensorZeroCLM_coe
    (d n : ℕ) [NeZero d]
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (hχ_vanish : ∀ φ : SchwartzMap (Fin n → ℝ) ℂ,
      VanishesToInfiniteOrderOnCoincidence
        (section43NPointTimeSpatialTensor d n φ χ))
    (φ : SchwartzMap (Fin n → ℝ) ℂ) :
    (section43TimeSpatialTensorZeroCLM d n χ hχ_vanish φ).1 =
      section43NPointTimeSpatialTensor d n φ χ := rfl

/-- The Schwinger functional restricted to a fixed spatial block and finite
time product tensors is a continuous multilinear functional of the one-variable
time slots. -/
noncomputable def section43SchwingerTimeSpatialProductMultilinear
    (OS : OsterwalderSchraderAxioms d)
    (n : ℕ)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (hχ_vanish : ∀ φ : SchwartzMap (Fin n → ℝ) ℂ,
      VanishesToInfiniteOrderOnCoincidence
        (section43NPointTimeSpatialTensor d n φ χ)) :
    ContinuousMultilinearMap ℂ
      (fun _ : Fin n => SchwartzMap ℝ ℂ) ℂ :=
  ((OsterwalderSchraderAxioms.schwingerCLM (d := d) OS n).comp
      (section43TimeSpatialTensorZeroCLM d n χ hχ_vanish)).compContinuousMultilinearMap
    (SchwartzMap.productTensorMLM (E := ℝ) n)

@[simp] theorem section43SchwingerTimeSpatialProductMultilinear_apply
    (OS : OsterwalderSchraderAxioms d)
    (n : ℕ)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (hχ_vanish : ∀ φ : SchwartzMap (Fin n → ℝ) ℂ,
      VanishesToInfiniteOrderOnCoincidence
        (section43NPointTimeSpatialTensor d n φ χ))
    (fs : Fin n → SchwartzMap ℝ ℂ) :
    section43SchwingerTimeSpatialProductMultilinear
        (d := d) OS n χ hχ_vanish fs =
      OS.S n ⟨section43NPointTimeSpatialTensor d n
        (section43TimeProductTensor fs) χ,
        hχ_vanish (section43TimeProductTensor fs)⟩ := by
  rfl

@[simp] theorem section43TimeSpatialTensorZeroCLM_timeImagAxisProductKernel_coe
    (d n : ℕ) [NeZero d]
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (hχ_vanish : ∀ φ : SchwartzMap (Fin n → ℝ) ℂ,
      VanishesToInfiniteOrderOnCoincidence
        (section43NPointTimeSpatialTensor d n φ χ))
    (τ : Fin n → ℝ) :
    (section43TimeSpatialTensorZeroCLM d n χ hχ_vanish
        (section43TimeImagAxisProductKernel τ)).1 =
      section43NPointTimeSpatialTensor d n
        (section43TimeImagAxisProductKernel τ) χ := rfl

@[simp] theorem section43TimeSpatialTensorZeroCLM_oneSidedLaplaceProduct_coe
    (d n : ℕ) [NeZero d]
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (hχ_vanish : ∀ φ : SchwartzMap (Fin n → ℝ) ℂ,
      VanishesToInfiniteOrderOnCoincidence
        (section43NPointTimeSpatialTensor d n φ χ))
    (gs : Fin n → Section43CompactPositiveTimeSource1D) :
    (section43TimeSpatialTensorZeroCLM d n χ hχ_vanish
        (section43TimeProductTensor
          (fun i : Fin n =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))).1 =
      section43NPointTimeSpatialTensor d n
        (section43TimeProductTensor
          (fun i : Fin n =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) χ := rfl

theorem section43SchwingerTimeSpatialProductMultilinear_imagAxisKernel
    (OS : OsterwalderSchraderAxioms d)
    (n : ℕ)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (hχ_vanish : ∀ φ : SchwartzMap (Fin n → ℝ) ℂ,
      VanishesToInfiniteOrderOnCoincidence
        (section43NPointTimeSpatialTensor d n φ χ))
    (τ : Fin n → ℝ) :
    section43SchwingerTimeSpatialProductMultilinear
        (d := d) OS n χ hχ_vanish
        (fun i : Fin n => section43ImagAxisPsiKernel (τ i)) =
      OS.S n ⟨section43NPointTimeSpatialTensor d n
        (section43TimeImagAxisProductKernel τ) χ,
        hχ_vanish (section43TimeImagAxisProductKernel τ)⟩ := by
  simp [section43TimeImagAxisProductKernel]

theorem section43SchwingerTimeSpatialProductMultilinear_oneSidedLaplaceProduct
    (OS : OsterwalderSchraderAxioms d)
    (n : ℕ)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (hχ_vanish : ∀ φ : SchwartzMap (Fin n → ℝ) ℂ,
      VanishesToInfiniteOrderOnCoincidence
        (section43NPointTimeSpatialTensor d n φ χ))
    (gs : Fin n → Section43CompactPositiveTimeSource1D) :
    section43SchwingerTimeSpatialProductMultilinear
        (d := d) OS n χ hχ_vanish
        (fun i : Fin n =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs i)) =
      OS.S n ⟨section43NPointTimeSpatialTensor d n
        (section43TimeProductTensor
          (fun i : Fin n =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) χ,
        hχ_vanish
          (section43TimeProductTensor
            (fun i : Fin n =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))⟩ := by
  rfl

/-- A zero-diagonal time-shell CLM produces a Schwinger scalar functional on
finite products of one-variable time factors. -/
noncomputable def section43SchwingerTimeProductMultilinearOfCLM
    (OS : OsterwalderSchraderAxioms d)
    {m k : ℕ}
    (Z : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ZeroDiagonalSchwartz d k) :
    ContinuousMultilinearMap ℂ
      (fun _ : Fin m => SchwartzMap ℝ ℂ) ℂ :=
  ((OsterwalderSchraderAxioms.schwingerCLM (d := d) OS k).comp
      Z).compContinuousMultilinearMap
    (SchwartzMap.productTensorMLM (E := ℝ) m)

@[simp] theorem section43SchwingerTimeProductMultilinearOfCLM_apply
    (OS : OsterwalderSchraderAxioms d)
    {m k : ℕ}
    (Z : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ZeroDiagonalSchwartz d k)
    (fs : Fin m → SchwartzMap ℝ ℂ) :
    section43SchwingerTimeProductMultilinearOfCLM
        (d := d) OS Z fs =
      OS.S k (Z (section43TimeProductTensor fs)) := by
  rfl

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

end OSReconstruction
