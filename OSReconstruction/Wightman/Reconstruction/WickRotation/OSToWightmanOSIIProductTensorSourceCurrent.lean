import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceOrderedGeometry
import OSReconstruction.SCV.DistributionalEOWCutoff

/-!
# OS II Product-Tensor Source Currents

This file contains the source-current side of the OS-II product-tensor bridge:
continuous linear maps from finite time tests into spacetime Schwartz tests,
their zero-diagonal variants, and the induced Schwinger multilinear pairings.

It deliberately avoids the downstream boundary-value carriers.  The intended
use in the E-to-R/W4 route is to construct the zero-diagonal current first, then
compare its Schwinger pairing with the scalar OS-II semigroup real edge.
-/

noncomputable section

open Complex Topology MeasureTheory
open Set
open scoped Classical NNReal BigOperators

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

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

/-- Pointwise OS-II formula for the ordered-pullback source current on the
strict positive imaginary axis.

On ordered Euclidean configurations, the difference-time coordinates are
nonnegative, so the imaginary-axis product kernel evaluates to the usual
multitime Laplace exponential.  This is the concrete source-current edge value
used before comparing the BVT boundary value with the time-shifted Schwinger
shell. -/
theorem section43OrderedPullbackTimeSpatialTensorCLM_timeImagAxisProductKernel_apply_of_pos_of_ordered
    (d n : ℕ) [NeZero d]
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    {τ : Fin n → ℝ}
    (hτ : τ ∈ section43TimeStrictPositiveRegion n)
    {y : NPointDomain d n}
    (hy : y ∈ OrderedPositiveTimeRegion d n) :
    section43OrderedPullbackTimeSpatialTensorCLM d n χ
        (section43TimeImagAxisProductKernel τ) y =
      Complex.exp
          (-(∑ i : Fin n,
            (τ i : ℂ) *
              (section43QTime (d := d) (n := n)
                (section43DiffCoordRealCLE d n y) i : ℂ))) *
        χ (section43QSpatial (d := d) (n := n)
          (section43DiffCoordRealCLE d n y)) := by
  have hδ_nonneg :
      section43QTime (d := d) (n := n)
          (section43DiffCoordRealCLE d n y) ∈
        section43TimePositiveRegion n := by
    intro i
    have hpos : 0 < (section43DiffCoordRealCLE d n y) i 0 := by
      rw [section43DiffCoordRealCLE_apply]
      by_cases hi : i.val = 0
      · simpa [hi] using (hy i).1
      · have hpred_lt : (⟨i.val - 1, by omega⟩ : Fin n) < i := by
          change i.val - 1 < i.val
          omega
        have hlt : y ⟨i.val - 1, by omega⟩ 0 < y i 0 :=
          (hy ⟨i.val - 1, by omega⟩).2 i hpred_lt
        simpa [hi, sub_pos] using hlt
    simpa [section43QTime, nPointTimeSpatialCLE] using le_of_lt hpos
  rw [section43OrderedPullbackTimeSpatialTensorCLM_apply]
  simp [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    section43NPointTimeSpatialTensor_apply,
    section43TimeImagAxisProductKernel_apply_of_pos_of_nonneg hτ hδ_nonneg]

/-- Cutoff version of the pointwise OS-II ordered-pullback source current on
the strict positive imaginary axis.

This is the exact value carried by the selected compact source current before
using the later compact-support fact that the cutoff is equal to `1` on the
chosen source support. -/
theorem section43OrderedPullbackTimeSpatialTensorCLM_cutoff_timeImagAxisProductKernel_apply_of_pos_of_ordered
    (d n : ℕ) [NeZero d]
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (η : SchwartzMap (Fin n → ℝ) ℂ)
    {τ : Fin n → ℝ}
    (hτ : τ ∈ section43TimeStrictPositiveRegion n)
    {y : NPointDomain d n}
    (hy : y ∈ OrderedPositiveTimeRegion d n) :
    section43OrderedPullbackTimeSpatialTensorCLM d n χ
        (SchwartzMap.smulLeftCLM ℂ (η : (Fin n → ℝ) → ℂ)
          (section43TimeImagAxisProductKernel τ)) y =
      η (section43QTime (d := d) (n := n)
          (section43DiffCoordRealCLE d n y)) *
        Complex.exp
          (-(∑ i : Fin n,
            (τ i : ℂ) *
              (section43QTime (d := d) (n := n)
                (section43DiffCoordRealCLE d n y) i : ℂ))) *
        χ (section43QSpatial (d := d) (n := n)
          (section43DiffCoordRealCLE d n y)) := by
  have hδ_nonneg :
      section43QTime (d := d) (n := n)
          (section43DiffCoordRealCLE d n y) ∈
        section43TimePositiveRegion n := by
    intro i
    have hpos : 0 < (section43DiffCoordRealCLE d n y) i 0 := by
      rw [section43DiffCoordRealCLE_apply]
      by_cases hi : i.val = 0
      · simpa [hi] using (hy i).1
      · have hpred_lt : (⟨i.val - 1, by omega⟩ : Fin n) < i := by
          change i.val - 1 < i.val
          omega
        have hlt : y ⟨i.val - 1, by omega⟩ 0 < y i 0 :=
          (hy ⟨i.val - 1, by omega⟩).2 i hpred_lt
        simpa [hi, sub_pos] using hlt
    simpa [section43QTime, nPointTimeSpatialCLE] using le_of_lt hpos
  rw [section43OrderedPullbackTimeSpatialTensorCLM_apply]
  simp [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    section43NPointTimeSpatialTensor_apply,
    SchwartzMap.smulLeftCLM_apply_apply η.hasTemperateGrowth,
    section43TimeImagAxisProductKernel_apply_of_pos_of_nonneg hτ hδ_nonneg,
    mul_assoc]

/-- Product-source recovery before scalarization.

On a configuration whose difference-time coordinates lie in the closed positive
orthant, the ordered pullback of the product of one-sided Laplace
representatives is the compact product-source integral of the ordered-pullback
imaginary-axis kernels.  This is the source-current form of the OS-II
Laplace-product bridge used before applying Schwinger functionals. -/
theorem section43OrderedPullbackTimeSpatialTensorCLM_oneSidedLaplaceProduct_eq_integral_kernel
    (d n : ℕ) [NeZero d]
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (gs : Fin n → Section43CompactPositiveTimeSource1D)
    {y : NPointDomain d n}
    (hy : section43QTime (d := d) (n := n)
        (section43DiffCoordRealCLE d n y) ∈ section43TimePositiveRegion n) :
    section43OrderedPullbackTimeSpatialTensorCLM d n χ
        (section43TimeProductTensor
          (fun i : Fin n =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) y =
      ∫ τ : Fin n → ℝ,
        section43OrderedPullbackTimeSpatialTensorCLM d n χ
            (section43TimeImagAxisProductKernel τ) y *
          (section43TimeProductSource gs).f τ := by
  let σ : Fin n → ℝ :=
    section43QTime (d := d) (n := n)
      (section43DiffCoordRealCLE d n y)
  let z : Section43SpatialSpace d n :=
    section43QSpatial (d := d) (n := n)
      (section43DiffCoordRealCLE d n y)
  calc
    section43OrderedPullbackTimeSpatialTensorCLM d n χ
        (section43TimeProductTensor
          (fun i : Fin n =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) y
        = (section43TimeProductTensor
            (fun i : Fin n =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i)) :
              SchwartzMap (Fin n → ℝ) ℂ) σ * χ z := by
          rw [section43OrderedPullbackTimeSpatialTensorCLM_apply]
          simp [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
            section43NPointTimeSpatialTensor_apply, σ, z]
    _ = (∫ τ : Fin n → ℝ,
            section43TimeImagAxisProductKernel τ σ *
              (section43TimeProductSource gs).f τ) * χ z := by
          rw [section43TimeProductTensor_oneSidedLaplaceRepresentative_eq_integral_kernel
            gs hy]
    _ = ∫ τ : Fin n → ℝ,
          (section43TimeImagAxisProductKernel τ σ *
              (section43TimeProductSource gs).f τ) * χ z := by
          exact
            (MeasureTheory.integral_mul_const (χ z)
              (fun τ : Fin n → ℝ =>
                section43TimeImagAxisProductKernel τ σ *
                  (section43TimeProductSource gs).f τ)).symm
    _ = ∫ τ : Fin n → ℝ,
          section43OrderedPullbackTimeSpatialTensorCLM d n χ
              (section43TimeImagAxisProductKernel τ) y *
            (section43TimeProductSource gs).f τ := by
          refine integral_congr_ae ?_
          filter_upwards with τ
          rw [section43OrderedPullbackTimeSpatialTensorCLM_apply]
          simp [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
            section43NPointTimeSpatialTensor_apply, σ, z]
          ring

/-- Cutoff product-source recovery before scalarization.

This is the selected-current version of
`section43OrderedPullbackTimeSpatialTensorCLM_oneSidedLaplaceProduct_eq_integral_kernel`:
the same compact product-source integral represents the ordered pullback after
the strict-positive cutoff used by the source-current selector is applied. -/
theorem section43OrderedPullbackTimeSpatialTensorCLM_cutoff_oneSidedLaplaceProduct_eq_integral_kernel
    (d n : ℕ) [NeZero d]
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (η : SchwartzMap (Fin n → ℝ) ℂ)
    (gs : Fin n → Section43CompactPositiveTimeSource1D)
    {y : NPointDomain d n}
    (hy : section43QTime (d := d) (n := n)
        (section43DiffCoordRealCLE d n y) ∈ section43TimePositiveRegion n) :
    section43OrderedPullbackTimeSpatialTensorCLM d n χ
        (SchwartzMap.smulLeftCLM ℂ (η : (Fin n → ℝ) → ℂ)
          (section43TimeProductTensor
            (fun i : Fin n =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) y =
      ∫ τ : Fin n → ℝ,
        section43OrderedPullbackTimeSpatialTensorCLM d n χ
            (SchwartzMap.smulLeftCLM ℂ (η : (Fin n → ℝ) → ℂ)
              (section43TimeImagAxisProductKernel τ)) y *
          (section43TimeProductSource gs).f τ := by
  let σ : Fin n → ℝ :=
    section43QTime (d := d) (n := n)
      (section43DiffCoordRealCLE d n y)
  let z : Section43SpatialSpace d n :=
    section43QSpatial (d := d) (n := n)
      (section43DiffCoordRealCLE d n y)
  calc
    section43OrderedPullbackTimeSpatialTensorCLM d n χ
        (SchwartzMap.smulLeftCLM ℂ (η : (Fin n → ℝ) → ℂ)
          (section43TimeProductTensor
            (fun i : Fin n =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) y
        = (η σ *
            (section43TimeProductTensor
              (fun i : Fin n =>
                section43OneSidedLaplaceSchwartzRepresentative1D (gs i)) :
                SchwartzMap (Fin n → ℝ) ℂ) σ) * χ z := by
          rw [section43OrderedPullbackTimeSpatialTensorCLM_apply]
          simp [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
            section43NPointTimeSpatialTensor_apply,
            SchwartzMap.smulLeftCLM_apply_apply η.hasTemperateGrowth, σ, z]
    _ = (η σ *
          (∫ τ : Fin n → ℝ,
            section43TimeImagAxisProductKernel τ σ *
              (section43TimeProductSource gs).f τ)) * χ z := by
          rw [section43TimeProductTensor_oneSidedLaplaceRepresentative_eq_integral_kernel
            gs hy]
    _ = (∫ τ : Fin n → ℝ,
          η σ *
            (section43TimeImagAxisProductKernel τ σ *
              (section43TimeProductSource gs).f τ)) * χ z := by
          exact
            congrArg (fun w : ℂ => w * χ z)
              (MeasureTheory.integral_const_mul (η σ)
                (fun τ : Fin n → ℝ =>
                  section43TimeImagAxisProductKernel τ σ *
                    (section43TimeProductSource gs).f τ)).symm
    _ = ∫ τ : Fin n → ℝ,
          (η σ *
            (section43TimeImagAxisProductKernel τ σ *
              (section43TimeProductSource gs).f τ)) * χ z := by
          exact
            (MeasureTheory.integral_mul_const (χ z)
              (fun τ : Fin n → ℝ =>
                η σ *
                  (section43TimeImagAxisProductKernel τ σ *
                    (section43TimeProductSource gs).f τ))).symm
    _ = ∫ τ : Fin n → ℝ,
          section43OrderedPullbackTimeSpatialTensorCLM d n χ
              (SchwartzMap.smulLeftCLM ℂ (η : (Fin n → ℝ) → ℂ)
                (section43TimeImagAxisProductKernel τ)) y *
            (section43TimeProductSource gs).f τ := by
          refine integral_congr_ae ?_
          filter_upwards with τ
          rw [section43OrderedPullbackTimeSpatialTensorCLM_apply]
          simp [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
            section43NPointTimeSpatialTensor_apply,
            SchwartzMap.smulLeftCLM_apply_apply η.hasTemperateGrowth, σ, z]
          ring

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

/-- The ordered pullback of a strict-positive difference-time source has
topological support in the ordered positive Euclidean time region. -/
theorem section43OrderedPullbackTimeSpatialTensorCLM_tsupport_subset_orderedPositive_of_tsupport_strictPositive
    (d n : ℕ) [NeZero d]
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (φ : SchwartzMap (Fin n → ℝ) ℂ)
    (hφ : tsupport (φ : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n) :
    tsupport
        (((section43OrderedPullbackTimeSpatialTensorCLM d n χ φ :
          SchwartzNPoint d n) : NPointDomain d n → ℂ)) ⊆
      OrderedPositiveTimeRegion d n := by
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
      d n hδ_pos
  simpa using hordered

/-- The finite strict-positive time-difference orthant is open. -/
theorem isOpen_section43TimeStrictPositiveRegion
    (n : ℕ) : IsOpen (section43TimeStrictPositiveRegion n) := by
  simp only [section43TimeStrictPositiveRegion, Set.setOf_forall]
  exact isOpen_iInter_of_finite fun i : Fin n =>
    isOpen_lt continuous_const (continuous_apply i)

/-- A compact strict-positive finite-time source admits a Schwartz cutoff
which is identically one on its topological support and whose own topological
support remains in the strict-positive orthant. -/
theorem exists_section43StrictPositiveSchwartzCutoff_eq_one_on_tsupport
    {n : ℕ} (g : Section43CompactStrictPositiveTimeSource n) :
    ∃ χ : SchwartzMap (Fin n → ℝ) ℂ,
      (∀ x ∈ tsupport (g.f : (Fin n → ℝ) → ℂ), χ x = 1) ∧
      tsupport (χ : (Fin n → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion n := by
  let K : Set (Fin n → ℝ) := tsupport (g.f : (Fin n → ℝ) → ℂ)
  have hK : IsCompact K := by
    simpa [K, HasCompactSupport] using g.compact
  have hU : IsOpen (section43TimeStrictPositiveRegion n) :=
    isOpen_section43TimeStrictPositiveRegion n
  have hKU : K ⊆ section43TimeStrictPositiveRegion n := by
    simpa [K] using g.positive
  exact SCV.exists_schwartz_cutoff_eq_one_on_compact_subset_open hK hU hKU

/-- A cutoff which is one on the support of a compact strict-positive source
acts as the identity on that source. -/
theorem section43StrictPositiveCutoff_smulLeftCLM_eq_of_eq_one_on_tsupport
    {n : ℕ}
    (χ : SchwartzMap (Fin n → ℝ) ℂ)
    (g : Section43CompactStrictPositiveTimeSource n)
    (hχ_one : ∀ x ∈ tsupport (g.f : (Fin n → ℝ) → ℂ), χ x = 1) :
    SchwartzMap.smulLeftCLM ℂ (χ : (Fin n → ℝ) → ℂ) g.f = g.f := by
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth]
  by_cases hx : x ∈ tsupport (g.f : (Fin n → ℝ) → ℂ)
  · simp [hχ_one x hx]
  · have hgx : g.f x = 0 := by
      have hxsupp : x ∉ Function.support (g.f : (Fin n → ℝ) → ℂ) := by
        intro hs
        exact hx (subset_closure hs)
      simpa [Function.mem_support] using hxsupp
    simp [hgx]

/-- Multiplying a finite-time test by a strict-positive cutoff makes its
ordered pullback source current zero-diagonal. -/
theorem section43OrderedPullbackTimeSpatialTensorCLM_smulLeft_mem_zeroDiagonal
    (d n : ℕ) [NeZero d]
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (η : SchwartzMap (Fin n → ℝ) ℂ)
    (hη : tsupport (η : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n)
    (φ : SchwartzMap (Fin n → ℝ) ℂ) :
    VanishesToInfiniteOrderOnCoincidence
      (section43OrderedPullbackTimeSpatialTensorCLM d n χ
        (SchwartzMap.smulLeftCLM ℂ (η : (Fin n → ℝ) → ℂ) φ)) := by
  apply section43OrderedPullbackTimeSpatialTensorCLM_mem_zeroDiagonal_of_tsupport_strictPositive
  intro x hx
  have hxpair := SchwartzMap.tsupport_smulLeftCLM_subset
    (F := ℂ) (g := (η : (Fin n → ℝ) → ℂ)) (f := φ) hx
  exact hη hxpair.2

/-- Multiplying a finite-time test by a strict-positive cutoff makes the
ordered pullback source current supported in ordered positive Euclidean time. -/
theorem section43OrderedPullbackTimeSpatialTensorCLM_smulLeft_tsupport_subset_orderedPositive
    (d n : ℕ) [NeZero d]
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (η : SchwartzMap (Fin n → ℝ) ℂ)
    (hη : tsupport (η : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n)
    (φ : SchwartzMap (Fin n → ℝ) ℂ) :
    tsupport
        (((section43OrderedPullbackTimeSpatialTensorCLM d n χ
          (SchwartzMap.smulLeftCLM ℂ (η : (Fin n → ℝ) → ℂ) φ) :
          SchwartzNPoint d n) : NPointDomain d n → ℂ)) ⊆
      OrderedPositiveTimeRegion d n := by
  apply
    section43OrderedPullbackTimeSpatialTensorCLM_tsupport_subset_orderedPositive_of_tsupport_strictPositive
  intro x hx
  have hxpair := SchwartzMap.tsupport_smulLeftCLM_subset
    (F := ℂ) (g := (η : (Fin n → ℝ) → ℂ)) (f := φ) hx
  exact hη hxpair.2

/-- The ordered pullback source-current map, made into a global zero-diagonal
CLM by multiplying every input time test with a strict-positive cutoff. -/
noncomputable def section43OrderedPullbackTimeSpatialTensorCutoffZeroCLM
    (d n : ℕ) [NeZero d]
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (η : SchwartzMap (Fin n → ℝ) ℂ)
    (hη : tsupport (η : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n) :
    SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ZeroDiagonalSchwartz d n :=
  ((section43OrderedPullbackTimeSpatialTensorCLM d n χ).comp
      (SchwartzMap.smulLeftCLM ℂ (η : (Fin n → ℝ) → ℂ))).codRestrict
    (zeroDiagonalSubmodule d n)
    (fun φ => by
      change VanishesToInfiniteOrderOnCoincidence _
      exact
        section43OrderedPullbackTimeSpatialTensorCLM_smulLeft_mem_zeroDiagonal
          d n χ η hη φ)

@[simp] theorem section43OrderedPullbackTimeSpatialTensorCutoffZeroCLM_coe
    (d n : ℕ) [NeZero d]
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (η : SchwartzMap (Fin n → ℝ) ℂ)
    (hη : tsupport (η : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n)
    (φ : SchwartzMap (Fin n → ℝ) ℂ) :
    (section43OrderedPullbackTimeSpatialTensorCutoffZeroCLM d n χ η hη φ).1 =
      section43OrderedPullbackTimeSpatialTensorCLM d n χ
        (SchwartzMap.smulLeftCLM ℂ (η : (Fin n → ℝ) → ℂ) φ) := rfl

/-- Local source-current package for compact strict-positive time sources:
choose a strict-positive cutoff, codrestrict the ordered pullback current with
it, and recover the uncut current on the chosen source. -/
theorem exists_section43OrderedPullbackTimeSpatialTensorCutoffZeroCLM
    (d n : ℕ) [NeZero d]
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (g : Section43CompactStrictPositiveTimeSource n) :
    ∃ η : SchwartzMap (Fin n → ℝ) ℂ,
      (∀ x ∈ tsupport (g.f : (Fin n → ℝ) → ℂ), η x = 1) ∧
      tsupport (η : (Fin n → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion n ∧
      ∃ Z : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ZeroDiagonalSchwartz d n,
        (∀ φ,
          (Z φ).1 =
            section43OrderedPullbackTimeSpatialTensorCLM d n χ
              (SchwartzMap.smulLeftCLM ℂ (η : (Fin n → ℝ) → ℂ) φ)) ∧
        Z g.f =
          ⟨section43OrderedPullbackTimeSpatialTensorCLM d n χ g.f,
            section43OrderedPullbackTimeSpatialTensorCLM_mem_zeroDiagonal_of_tsupport_strictPositive
              d n χ g.f g.positive⟩ := by
  obtain ⟨η, hη_one, hη_support⟩ :=
    exists_section43StrictPositiveSchwartzCutoff_eq_one_on_tsupport g
  let Z := section43OrderedPullbackTimeSpatialTensorCutoffZeroCLM d n χ η hη_support
  refine ⟨η, hη_one, hη_support, Z, ?_, ?_⟩
  · intro φ
    rfl
  · apply Subtype.ext
    simp [Z, section43StrictPositiveCutoff_smulLeftCLM_eq_of_eq_one_on_tsupport
      η g hη_one]

/-- Tensor a fixed left Schwinger source with a right time-shell CLM through
the OS conjugated tensor product. -/
noncomputable def section43FixedLeftOsConjRightCLM
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (R : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] SchwartzNPoint d m) :
    SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] SchwartzNPoint d (n + m) where
  toLinearMap :=
    { toFun := fun φ => f.osConjTensorProduct (R φ)
      map_add' := by
        intro φ ψ
        simp [SchwartzNPoint.osConjTensorProduct_add_right]
      map_smul' := by
        intro c φ
        simp [SchwartzNPoint.osConjTensorProduct_smul_right] }
  cont := by
    exact
      (SchwartzNPoint.osConjTensorProduct_continuous (d := d)).comp
        (continuous_const.prodMk R.continuous)

@[simp] theorem section43FixedLeftOsConjRightCLM_apply
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (R : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] SchwartzNPoint d m)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) :
    section43FixedLeftOsConjRightCLM (d := d) f R φ =
      f.osConjTensorProduct (R φ) := rfl

/-- If the fixed left source and all right-shell values are supported in
ordered positive Euclidean time, the OS-conjugated tensor product is a
zero-diagonal time-shell CLM. -/
noncomputable def section43FixedLeftOrderedRightZeroCLM
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (hf : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (R : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] SchwartzNPoint d m)
    (hR : ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
      tsupport ((R φ : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        OrderedPositiveTimeRegion d m) :
    SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ZeroDiagonalSchwartz d (n + m) :=
  (section43FixedLeftOsConjRightCLM (d := d) f R).codRestrict
    (zeroDiagonalSubmodule d (n + m))
    (fun φ => by
      change VanishesToInfiniteOrderOnCoincidence _
      exact
        VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
          (d := d) f (R φ) hf (hR φ))

@[simp] theorem section43FixedLeftOrderedRightZeroCLM_coe
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (hf : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (R : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] SchwartzNPoint d m)
    (hR : ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
      tsupport ((R φ : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        OrderedPositiveTimeRegion d m)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) :
    (section43FixedLeftOrderedRightZeroCLM (d := d) f hf R hR φ).1 =
      f.osConjTensorProduct (R φ) := rfl

/-- Concrete producer-side time-shell CLM: a fixed ordered left source tensored
with a cutoff ordered-pullback Section 4.3 right source current. -/
noncomputable def section43FixedLeftOrderedPullbackCutoffZeroCLM
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (hf : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (χ : SchwartzMap (Section43SpatialSpace d m) ℂ)
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη : tsupport (η : (Fin m → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion m) :
    SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ZeroDiagonalSchwartz d (n + m) :=
  let R : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] SchwartzNPoint d m :=
    (section43OrderedPullbackTimeSpatialTensorCLM d m χ).comp
      (SchwartzMap.smulLeftCLM ℂ (η : (Fin m → ℝ) → ℂ))
  section43FixedLeftOrderedRightZeroCLM (d := d) f hf R
    (fun φ => by
      simpa [R] using
        section43OrderedPullbackTimeSpatialTensorCLM_smulLeft_tsupport_subset_orderedPositive
          d m χ η hη φ)

@[simp] theorem section43FixedLeftOrderedPullbackCutoffZeroCLM_coe
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (hf : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (χ : SchwartzMap (Section43SpatialSpace d m) ℂ)
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη : tsupport (η : (Fin m → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion m)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) :
    (section43FixedLeftOrderedPullbackCutoffZeroCLM
        (d := d) f hf χ η hη φ).1 =
      f.osConjTensorProduct
        (section43OrderedPullbackTimeSpatialTensorCLM d m χ
          (SchwartzMap.smulLeftCLM ℂ (η : (Fin m → ℝ) → ℂ) φ)) := rfl

/-- The fixed-left selected source current on an imaginary-axis product kernel
as an honest zero-diagonal classical source.

This is the exact object evaluated by `OS.S` at the selected-current seam:
the right time shell is the cutoff ordered pullback of the imaginary-axis
kernel, while the left block is kept as the fixed OS-conjugated source. -/
theorem section43FixedLeftOrderedPullbackCutoffZeroCLM_timeImagAxisProductKernel_eq_ofClassical
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (hf : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (χ : SchwartzMap (Section43SpatialSpace d m) ℂ)
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη : tsupport (η : (Fin m → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion m)
    (τ : Fin m → ℝ) :
    section43FixedLeftOrderedPullbackCutoffZeroCLM
        (d := d) f hf χ η hη
        (section43TimeImagAxisProductKernel τ) =
      ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (section43OrderedPullbackTimeSpatialTensorCLM d m χ
            (SchwartzMap.smulLeftCLM ℂ (η : (Fin m → ℝ) → ℂ)
              (section43TimeImagAxisProductKernel τ)))) := by
  let right : SchwartzNPoint d m :=
    section43OrderedPullbackTimeSpatialTensorCLM d m χ
      (SchwartzMap.smulLeftCLM ℂ (η : (Fin m → ℝ) → ℂ)
        (section43TimeImagAxisProductKernel τ))
  let F : SchwartzNPoint d (n + m) := f.osConjTensorProduct right
  have hright :
      tsupport (right : NPointDomain d m → ℂ) ⊆
        OrderedPositiveTimeRegion d m := by
    simpa [right] using
      section43OrderedPullbackTimeSpatialTensorCLM_smulLeft_tsupport_subset_orderedPositive
        d m χ η hη (section43TimeImagAxisProductKernel τ)
  have hvanish : VanishesToInfiniteOrderOnCoincidence F := by
    simpa [F] using
      VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
        (d := d) f right hf hright
  apply Subtype.ext
  calc
    (section43FixedLeftOrderedPullbackCutoffZeroCLM
        (d := d) f hf χ η hη
        (section43TimeImagAxisProductKernel τ)).1 = F := by
        simp [F, right]
    _ = (ZeroDiagonalSchwartz.ofClassical F).1 := by
        exact (ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
          (f := F) hvanish).symm

/-- Scalar Fubini packet for the fixed-left selected source current.

Evaluating the cutoff time-shell CLM on a product of one-sided Laplace
representatives is the same as integrating its honest imaginary-axis selected
currents against the compact product source.  This is the scalarized
source-current transport used before the final BVT/Schwinger shell
identification. -/
theorem section43FixedLeftOrderedPullbackCutoffZeroCLM_oneSidedLaplaceProduct_eq_integral_kernel
    {n m : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (f : SchwartzNPoint d n)
    (hf : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (χ : SchwartzMap (Section43SpatialSpace d m) ℂ)
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη : tsupport (η : (Fin m → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion m)
    (gs : Fin m → Section43CompactPositiveTimeSource1D) :
    OS.S (n + m)
        (section43FixedLeftOrderedPullbackCutoffZeroCLM
          (d := d) f hf χ η hη
          (section43TimeProductTensor
            (fun i : Fin m =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) =
      ∫ τ : Fin m → ℝ,
        OS.S (n + m)
          (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (section43OrderedPullbackTimeSpatialTensorCLM d m χ
                (SchwartzMap.smulLeftCLM ℂ
                  (η : (Fin m → ℝ) → ℂ)
                  (section43TimeImagAxisProductKernel τ))))) *
          (section43TimeProductSource gs).f τ := by
  let Z : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ZeroDiagonalSchwartz d (n + m) :=
    section43FixedLeftOrderedPullbackCutoffZeroCLM
      (d := d) f hf χ η hη
  let T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ :=
    (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS (n + m)).comp Z
  have hflat :=
    section43TimeProductTensor_allSlots_flattened
      T gs (fun _ : Fin m => 0)
  calc
    OS.S (n + m)
        (section43FixedLeftOrderedPullbackCutoffZeroCLM
          (d := d) f hf χ η hη
          (section43TimeProductTensor
            (fun i : Fin m =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i))))
        = T (section43TimeProductTensor
            (fun i : Fin m =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) := by
          rfl
    _ = ∫ τ : Fin m → ℝ,
          T (section43TimeImagAxisProductKernel τ) *
            (section43TimeProductSource gs).f τ := hflat
    _ = ∫ τ : Fin m → ℝ,
        OS.S (n + m)
          (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (section43OrderedPullbackTimeSpatialTensorCLM d m χ
                (SchwartzMap.smulLeftCLM ℂ
                  (η : (Fin m → ℝ) → ℂ)
                  (section43TimeImagAxisProductKernel τ))))) *
          (section43TimeProductSource gs).f τ := by
          refine integral_congr_ae ?_
          filter_upwards with τ
          change
            OS.S (n + m)
              (Z (section43TimeImagAxisProductKernel τ)) *
              (section43TimeProductSource gs).f τ =
            OS.S (n + m)
              (ZeroDiagonalSchwartz.ofClassical
                (f.osConjTensorProduct
                  (section43OrderedPullbackTimeSpatialTensorCLM d m χ
                    (SchwartzMap.smulLeftCLM ℂ
                      (η : (Fin m → ℝ) → ℂ)
                      (section43TimeImagAxisProductKernel τ))))) *
              (section43TimeProductSource gs).f τ
          rw [section43FixedLeftOrderedPullbackCutoffZeroCLM_timeImagAxisProductKernel_eq_ofClassical]

/-- Compact-current package for the fixed-left OS-conjugated time shell:
choose a strict-positive cutoff for the right compact source, build the
zero-diagonal CLM, and recover the uncut compact right source current on that
source. -/
theorem exists_section43FixedLeftOrderedPullbackCutoffZeroCLM
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (hf : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (χ : SchwartzMap (Section43SpatialSpace d m) ℂ)
    (g : Section43CompactStrictPositiveTimeSource m) :
    ∃ η : SchwartzMap (Fin m → ℝ) ℂ,
      (∀ x ∈ tsupport (g.f : (Fin m → ℝ) → ℂ), η x = 1) ∧
      tsupport (η : (Fin m → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion m ∧
      ∃ Z : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
          ZeroDiagonalSchwartz d (n + m),
        (∀ φ,
          (Z φ).1 =
            f.osConjTensorProduct
              (section43OrderedPullbackTimeSpatialTensorCLM d m χ
                (SchwartzMap.smulLeftCLM ℂ
                  (η : (Fin m → ℝ) → ℂ) φ))) ∧
        Z g.f =
          ⟨f.osConjTensorProduct
              (section43OrderedPullbackTimeSpatialTensorCLM d m χ g.f),
            VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
              (d := d) f
              (section43OrderedPullbackTimeSpatialTensorCLM d m χ g.f)
              hf
              (section43OrderedPullbackTimeSpatialTensorCLM_tsupport_subset_orderedPositive_of_tsupport_strictPositive
                d m χ g.f g.positive)⟩ := by
  obtain ⟨η, hη_one, hη_support⟩ :=
    exists_section43StrictPositiveSchwartzCutoff_eq_one_on_tsupport g
  let Z :=
    section43FixedLeftOrderedPullbackCutoffZeroCLM
      (d := d) f hf χ η hη_support
  refine ⟨η, hη_one, hη_support, Z, ?_, ?_⟩
  · intro φ
    rfl
  · apply Subtype.ext
    simp [Z, section43StrictPositiveCutoff_smulLeftCLM_eq_of_eq_one_on_tsupport
      η g hη_one]

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

end OSReconstruction
