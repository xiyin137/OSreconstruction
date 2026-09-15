/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceOrderedGeometry
import OSReconstruction.SCV.DistributionalEOWCutoff













noncomputable section

open Complex Topology MeasureTheory
open Set
open scoped Classical NNReal BigOperators

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Section 4.3 time/spatial tensoring is jointly continuous in both Schwartz
factors after transport back to the `n`-point space. -/
theorem section43NPointTimeSpatialTensor_continuous
    (d n : ℕ) [NeZero d] :
    Continuous
      (fun p :
          SchwartzMap (Fin n → ℝ) ℂ ×
            SchwartzMap (Section43SpatialSpace d n) ℂ =>
        section43NPointTimeSpatialTensor d n p.1 p.2) := by
  let toFlat :
      SchwartzMap (Fin n → ℝ) ℂ ×
          SchwartzMap (Section43SpatialSpace d n) ℂ →
        SchwartzMap (Fin (n + n * d) → ℝ) ℂ := fun p =>
      SchwartzMap.tensorProduct p.1
        (section43SpatialFlatSchwartzCLE d n p.2)
  have hflat : Continuous toFlat := by
    exact
      (SchwartzMap.tensorProduct_continuous
        (E := ℝ) (m := n) (k := n * d)).comp
        (continuous_fst.prodMk
          ((section43SpatialFlatSchwartzCLE d n).continuous.comp
            continuous_snd))
  let toTimeSpatial :
      SchwartzMap (Fin (n + n * d) → ℝ) ℂ →L[ℂ]
        SchwartzMap (Section43TimeSpatialSpace d n) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (section43TimeSpatialFlatCLE d n)
  let toNPoint :
      SchwartzMap (Section43TimeSpatialSpace d n) ℂ →L[ℂ]
        SchwartzNPoint d n :=
    (nPointTimeSpatialSchwartzCLE (d := d) (n := n)).symm
  have hcont :
      Continuous (fun p =>
        toNPoint (toTimeSpatial (toFlat p))) :=
    toNPoint.continuous.comp (toTimeSpatial.continuous.comp hflat)
  simpa [section43NPointTimeSpatialTensor, section43TimeSpatialTensor,
    toFlat, toTimeSpatial, toNPoint] using hcont

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
  cont :=
    (section43NPointTimeSpatialTensor_continuous d n).comp
      (continuous_id.prodMk continuous_const)

@[simp] theorem section43TimeSpatialTensorCLM_apply
    (d n : ℕ) [NeZero d]
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (φ : SchwartzMap (Fin n → ℝ) ℂ) :
    section43TimeSpatialTensorCLM d n χ φ =
      section43NPointTimeSpatialTensor d n φ χ := rfl

/-- Fixed-time Section 4.3 tensoring, as a continuous linear map in the
spatial Schwartz factor. -/
noncomputable def section43TimeSpatialTensorSpatialCLM
    (d n : ℕ) [NeZero d]
    (φ : SchwartzMap (Fin n → ℝ) ℂ) :
    SchwartzMap (Section43SpatialSpace d n) ℂ →L[ℂ]
      SchwartzNPoint d n where
  toLinearMap :=
    { toFun := fun χ => section43NPointTimeSpatialTensor d n φ χ
      map_add' := by
        intro χ ψ
        ext q
        simp [section43NPointTimeSpatialTensor_apply, mul_add]
      map_smul' := by
        intro c χ
        ext q
        simp [section43NPointTimeSpatialTensor_apply, smul_eq_mul,
          mul_left_comm] }
  cont :=
    (section43NPointTimeSpatialTensor_continuous d n).comp
      (continuous_const.prodMk continuous_id)

@[simp] theorem section43TimeSpatialTensorSpatialCLM_apply
    (d n : ℕ) [NeZero d]
    (φ : SchwartzMap (Fin n → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ) :
    section43TimeSpatialTensorSpatialCLM d n φ χ =
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

/-- Ordered Euclidean pullback with fixed time factor, continuous and linear in
the spatial Schwartz source. -/
noncomputable def section43OrderedPullbackTimeSpatialTensorSpatialCLM
    (d n : ℕ) [NeZero d]
    (φ : SchwartzMap (Fin n → ℝ) ℂ) :
    SchwartzMap (Section43SpatialSpace d n) ℂ →L[ℂ]
      SchwartzNPoint d n :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (section43DiffCoordRealCLE d n)).comp
      (section43TimeSpatialTensorSpatialCLM d n φ)

@[simp] theorem section43OrderedPullbackTimeSpatialTensorSpatialCLM_apply
    (d n : ℕ) [NeZero d]
    (φ : SchwartzMap (Fin n → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ) :
    section43OrderedPullbackTimeSpatialTensorSpatialCLM d n φ χ =
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

/-- Lift a finite difference-time cutoff to the full difference-coordinate
Schwartz domain by ignoring the spatial coordinates. -/
noncomputable def section43NPointTimeCutoffWeight
    (d n : ℕ) [NeZero d]
    (η : SchwartzMap (Fin n → ℝ) ℂ) :
    NPointDomain d n → ℂ :=
  fun q => η (section43QTime (d := d) (n := n) q)

theorem section43NPointTimeCutoffWeight_hasTemperateGrowth
    (d n : ℕ) [NeZero d]
    (η : SchwartzMap (Fin n → ℝ) ℂ) :
    Function.HasTemperateGrowth
      (section43NPointTimeCutoffWeight d n η) := by
  change Function.HasTemperateGrowth
    ((η : (Fin n → ℝ) → ℂ) ∘ section43QTimeCLM d n)
  exact η.hasTemperateGrowth.comp (section43QTimeCLM d n).hasTemperateGrowth

/-- Multiply an arbitrary difference-coordinate Schwartz test by a
strict-positive time cutoff, then pull it back to ordered Euclidean
coordinates. -/
noncomputable def section43OrderedPullbackFullCutoffCLM
    (d n : ℕ) [NeZero d]
    (η : SchwartzMap (Fin n → ℝ) ℂ) :
    SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (section43DiffCoordRealCLE d n)).comp
    (SchwartzMap.smulLeftCLM ℂ
      (section43NPointTimeCutoffWeight d n η))

@[simp] theorem section43OrderedPullbackFullCutoffCLM_apply
    (d n : ℕ) [NeZero d]
    (η : SchwartzMap (Fin n → ℝ) ℂ)
    (F : SchwartzNPoint d n) :
    section43OrderedPullbackFullCutoffCLM d n η F =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (section43DiffCoordRealCLE d n)
        (SchwartzMap.smulLeftCLM ℂ
          (section43NPointTimeCutoffWeight d n η) F) := rfl

/-- A strict-positive time cutoff sends every full difference-coordinate
Schwartz test into the ordered positive Euclidean support sector. -/
theorem section43OrderedPullbackFullCutoffCLM_tsupport_subset_orderedPositive
    (d n : ℕ) [NeZero d]
    (η : SchwartzMap (Fin n → ℝ) ℂ)
    (hη : tsupport (η : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n)
    (F : SchwartzNPoint d n) :
    tsupport
        (((section43OrderedPullbackFullCutoffCLM d n η F :
          SchwartzNPoint d n) : NPointDomain d n → ℂ)) ⊆
      OrderedPositiveTimeRegion d n := by
  intro y hy
  have hy_pre :
      section43DiffCoordRealCLE d n y ∈
        tsupport
          ((SchwartzMap.smulLeftCLM ℂ
            (section43NPointTimeCutoffWeight d n η) F :
            SchwartzNPoint d n) : NPointDomain d n → ℂ) := by
    exact
      tsupport_comp_subset_preimage
        ((SchwartzMap.smulLeftCLM ℂ
          (section43NPointTimeCutoffWeight d n η) F :
          SchwartzNPoint d n) : NPointDomain d n → ℂ)
        (section43DiffCoordRealCLE d n).continuous hy
  have hweight :=
    (SchwartzMap.tsupport_smulLeftCLM_subset
      (F := ℂ)
      (g := section43NPointTimeCutoffWeight d n η)
      (f := F) hy_pre).2
  have htime_support :
      section43QTime (d := d) (n := n)
          (section43DiffCoordRealCLE d n y) ∈
        tsupport (η : (Fin n → ℝ) → ℂ) := by
    have hcomp :
        section43DiffCoordRealCLE d n y ∈
          tsupport
            ((η : (Fin n → ℝ) → ℂ) ∘ section43QTimeCLM d n) := by
      exact hweight
    have hpre :=
      (tsupport_comp_subset_preimage
        (η : (Fin n → ℝ) → ℂ)
        (section43QTimeCLM d n).continuous) hcomp
    simpa [section43QTimeCLM_apply] using hpre
  have hδ_pos :
      ∀ i : Fin n, 0 < (section43DiffCoordRealCLE d n y) i 0 := by
    intro i
    simpa [section43QTime, nPointTimeSpatialCLE] using
      hη htime_support i
  have hordered :=
    section43DiffCoordRealCLE_symm_mem_orderedPositiveTimeRegion_of_pos_time
      d n (δ := section43DiffCoordRealCLE d n y) hδ_pos
  simpa using hordered

/-- The full cutoff/ordered-pullback operator as a continuous linear map into
the honest positive-time source space. -/
noncomputable def section43OrderedPullbackFullCutoffPositiveCLM
    (d n : ℕ) [NeZero d]
    (η : SchwartzMap (Fin n → ℝ) ℂ)
    (hη : tsupport (η : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n) :
    SchwartzNPoint d n →L[ℂ]
      euclideanPositiveTimeSubmodule (d := d) n :=
  (section43OrderedPullbackFullCutoffCLM d n η).codRestrict
    (euclideanPositiveTimeSubmodule (d := d) n)
    (section43OrderedPullbackFullCutoffCLM_tsupport_subset_orderedPositive
      d n η hη)

@[simp] theorem section43OrderedPullbackFullCutoffPositiveCLM_coe
    (d n : ℕ) [NeZero d]
    (η : SchwartzMap (Fin n → ℝ) ℂ)
    (hη : tsupport (η : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n)
    (F : SchwartzNPoint d n) :
    (section43OrderedPullbackFullCutoffPositiveCLM d n η hη F).1 =
      section43OrderedPullbackFullCutoffCLM d n η F := rfl

/-- The full-space cutoff and ordered pullback, codrestricted to the honest
zero-diagonal Schwinger test space. -/
noncomputable def section43OrderedPullbackFullCutoffZeroCLM
    (d n : ℕ) [NeZero d]
    (η : SchwartzMap (Fin n → ℝ) ℂ)
    (hη : tsupport (η : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n) :
    SchwartzNPoint d n →L[ℂ] ZeroDiagonalSchwartz d n :=
  (section43OrderedPullbackFullCutoffCLM d n η).codRestrict
    (zeroDiagonalSubmodule d n)
    (fun F => by
      change VanishesToInfiniteOrderOnCoincidence _
      exact
        VanishesToInfiniteOrderOnCoincidence_of_support_subset_orderedPositiveTimeRegion
          _
          (section43OrderedPullbackFullCutoffCLM_tsupport_subset_orderedPositive
            d n η hη F))

@[simp] theorem section43OrderedPullbackFullCutoffZeroCLM_coe
    (d n : ℕ) [NeZero d]
    (η : SchwartzMap (Fin n → ℝ) ℂ)
    (hη : tsupport (η : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n)
    (F : SchwartzNPoint d n) :
    (section43OrderedPullbackFullCutoffZeroCLM d n η hη F).1 =
      section43OrderedPullbackFullCutoffCLM d n η F := rfl

/-- On a Section 4.3 product tensor, the full-space cutoff operator agrees
with cutting off the finite-time factor before tensoring. -/
theorem section43OrderedPullbackFullCutoffCLM_timeSpatialTensor
    (d n : ℕ) [NeZero d]
    (η φ : SchwartzMap (Fin n → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ) :
    section43OrderedPullbackFullCutoffCLM d n η
        (section43NPointTimeSpatialTensor d n φ χ) =
      section43OrderedPullbackTimeSpatialTensorCLM d n χ
        (SchwartzMap.smulLeftCLM ℂ
          (η : (Fin n → ℝ) → ℂ) φ) := by
  ext y
  simp [section43OrderedPullbackFullCutoffCLM,
    section43NPointTimeCutoffWeight,
    section43OrderedPullbackTimeSpatialTensorCLM_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    section43NPointTimeSpatialTensor_apply,
    SchwartzMap.smulLeftCLM_apply_apply
      (section43NPointTimeCutoffWeight_hasTemperateGrowth d n η),
    SchwartzMap.smulLeftCLM_apply_apply η.hasTemperateGrowth, mul_assoc]

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

/-- The cutoff-localized ordered source current, jointly parameterized by its
time and spatial Schwartz factors. -/
noncomputable def section43OrderedPullbackTimeSpatialTensorCutoffZero
    (d n : ℕ) [NeZero d]
    (η : SchwartzMap (Fin n → ℝ) ℂ)
    (hη : tsupport (η : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n)
    (φ : SchwartzMap (Fin n → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ) :
    ZeroDiagonalSchwartz d n :=
  ⟨section43OrderedPullbackTimeSpatialTensorCLM d n χ
      (SchwartzMap.smulLeftCLM ℂ (η : (Fin n → ℝ) → ℂ) φ),
    section43OrderedPullbackTimeSpatialTensorCLM_smulLeft_mem_zeroDiagonal
      d n χ η hη φ⟩

@[simp] theorem section43OrderedPullbackTimeSpatialTensorCutoffZero_coe
    (d n : ℕ) [NeZero d]
    (η : SchwartzMap (Fin n → ℝ) ℂ)
    (hη : tsupport (η : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n)
    (φ : SchwartzMap (Fin n → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ) :
    (section43OrderedPullbackTimeSpatialTensorCutoffZero
      d n η hη φ χ).1 =
      section43OrderedPullbackTimeSpatialTensorCLM d n χ
        (SchwartzMap.smulLeftCLM ℂ (η : (Fin n → ℝ) → ℂ) φ) := rfl

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

/-- A fixed cutoff and time test give a zero-diagonal source current that is
continuous and linear in the spatial Schwartz factor. -/
noncomputable def section43OrderedPullbackTimeSpatialTensorCutoffSpatialZeroCLM
    (d n : ℕ) [NeZero d]
    (η : SchwartzMap (Fin n → ℝ) ℂ)
    (hη : tsupport (η : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n)
    (φ : SchwartzMap (Fin n → ℝ) ℂ) :
    SchwartzMap (Section43SpatialSpace d n) ℂ →L[ℂ]
      ZeroDiagonalSchwartz d n :=
  (section43OrderedPullbackTimeSpatialTensorSpatialCLM d n
      (SchwartzMap.smulLeftCLM ℂ
        (η : (Fin n → ℝ) → ℂ) φ)).codRestrict
    (zeroDiagonalSubmodule d n)
    (fun χ => by
      change VanishesToInfiniteOrderOnCoincidence _
      exact
        section43OrderedPullbackTimeSpatialTensorCLM_smulLeft_mem_zeroDiagonal
          d n χ η hη φ)

@[simp] theorem section43OrderedPullbackTimeSpatialTensorCutoffSpatialZeroCLM_coe
    (d n : ℕ) [NeZero d]
    (η : SchwartzMap (Fin n → ℝ) ℂ)
    (hη : tsupport (η : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n)
    (φ : SchwartzMap (Fin n → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ) :
    (section43OrderedPullbackTimeSpatialTensorCutoffSpatialZeroCLM
      d n η hη φ χ).1 =
      section43OrderedPullbackTimeSpatialTensorCLM d n χ
        (SchwartzMap.smulLeftCLM ℂ
          (η : (Fin n → ℝ) → ℂ) φ) := rfl

/-- The Schwinger functional induced by the cutoff on the entire
difference-coordinate Schwartz space. -/
noncomputable def section43SchwingerFullCutoffCLM
    (OS : OsterwalderSchraderAxioms d)
    (n : ℕ)
    (η : SchwartzMap (Fin n → ℝ) ℂ)
    (hη : tsupport (η : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n) :
    SchwartzNPoint d n →L[ℂ] ℂ :=
  (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS n).comp
    (section43OrderedPullbackFullCutoffZeroCLM d n η hη)

/-- The simultaneous cutoff Schwinger functional restricted to ordinary
spacetime product tensors.

This is the factorized producer surface used by the per-slot semigroup
construction.  Nuclear uniqueness below reconnects it to the full Schwartz
distribution. -/
noncomputable def section43SchwingerFullCutoffProductMultilinear
    (OS : OsterwalderSchraderAxioms d)
    (n : ℕ)
    (η : SchwartzMap (Fin n → ℝ) ℂ)
    (hη : tsupport (η : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n) :
    ContinuousMultilinearMap ℂ
      (fun _ : Fin n => SchwartzSpacetime d) ℂ :=
  (section43SchwingerFullCutoffCLM (d := d) OS n η hη).compContinuousMultilinearMap
    (SchwartzMap.productTensorMLM (E := SpacetimeDim d) n)

/-- The cutoff-localized product tensor as one continuous multilinear
positive-time source. This is the all-slot right-source adapter consumed by
the OS-II semigroup branch. -/
noncomputable def section43FullCutoffProductPositiveMultilinear
    (d n : ℕ) [NeZero d]
    (η : SchwartzMap (Fin n → ℝ) ℂ)
    (hη : tsupport (η : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n) :
    ContinuousMultilinearMap ℂ
      (fun _ : Fin n => SchwartzSpacetime d)
      (euclideanPositiveTimeSubmodule (d := d) n) :=
  (section43OrderedPullbackFullCutoffPositiveCLM d n η hη
    ).compContinuousMultilinearMap
      (SchwartzMap.productTensorMLM (E := SpacetimeDim d) n)

@[simp] theorem section43FullCutoffProductPositiveMultilinear_coe
    (d n : ℕ) [NeZero d]
    (η : SchwartzMap (Fin n → ℝ) ℂ)
    (hη : tsupport (η : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n)
    (fs : Fin n → SchwartzSpacetime d) :
    (section43FullCutoffProductPositiveMultilinear d n η hη fs).1 =
      section43OrderedPullbackFullCutoffCLM d n η
        (SchwartzMap.productTensor fs) := rfl

@[simp] theorem section43SchwingerFullCutoffProductMultilinear_apply
    (OS : OsterwalderSchraderAxioms d)
    (n : ℕ)
    (η : SchwartzMap (Fin n → ℝ) ℂ)
    (hη : tsupport (η : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n)
    (fs : Fin n → SchwartzSpacetime d) :
    section43SchwingerFullCutoffProductMultilinear
        (d := d) OS n η hη fs =
      section43SchwingerFullCutoffCLM (d := d) OS n η hη
        (SchwartzMap.productTensor fs) :=
  rfl

/-- The cutoff-localized Schwinger pairing, simultaneously parameterized by
the finite-time and spatial Schwartz factors. -/
noncomputable def section43SchwingerTimeSpatialCutoffPairing
    (OS : OsterwalderSchraderAxioms d)
    (n : ℕ)
    (η : SchwartzMap (Fin n → ℝ) ℂ)
    (hη : tsupport (η : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n) :
    SchwartzMap (Fin n → ℝ) ℂ ×
        SchwartzMap (Section43SpatialSpace d n) ℂ → ℂ :=
  fun p =>
    OS.S n
      (section43OrderedPullbackTimeSpatialTensorCutoffZero
        d n η hη p.1 p.2)

/-- With the cutoff and time test fixed, the localized Schwinger pairing is a
continuous linear functional of the spatial Schwartz source. -/
noncomputable def section43SchwingerTimeSpatialCutoffSpatialCLM
    (OS : OsterwalderSchraderAxioms d)
    (n : ℕ)
    (η : SchwartzMap (Fin n → ℝ) ℂ)
    (hη : tsupport (η : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n)
    (φ : SchwartzMap (Fin n → ℝ) ℂ) :
    SchwartzMap (Section43SpatialSpace d n) ℂ →L[ℂ] ℂ :=
  (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS n).comp
    (section43OrderedPullbackTimeSpatialTensorCutoffSpatialZeroCLM
      d n η hη φ)

@[simp] theorem section43SchwingerTimeSpatialCutoffSpatialCLM_apply
    (OS : OsterwalderSchraderAxioms d)
    (n : ℕ)
    (η : SchwartzMap (Fin n → ℝ) ℂ)
    (hη : tsupport (η : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n)
    (φ : SchwartzMap (Fin n → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ) :
    section43SchwingerTimeSpatialCutoffSpatialCLM
        (d := d) OS n η hη φ χ =
      section43SchwingerTimeSpatialCutoffPairing
        (d := d) OS n η hη (φ, χ) := rfl

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

end OSReconstruction
