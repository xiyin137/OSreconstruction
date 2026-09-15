import OSReconstruction.SCV.HeadBlockIntegral
import OSReconstruction.SCV.HeadFiberAntideriv
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSourceCurrent
import OSReconstruction.Wightman.SpectralEquivalence

/-!
# OS-II Chapter V reduction of ordered time/spatial tensors

The Chapter V reflected source is first transported to one global ordered
difference-coordinate chart.  In that chart it is a tensor of a full time
test and a full spatial test.  Fiber integration over the common spacetime
basepoint then separates into:

* the one-dimensional head integral of the time test;
* the `d`-dimensional head-block integral of the spatial test.

This file records that separation before any source-specific approximate
identity is inserted.
-/

noncomputable section

open Complex MeasureTheory
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d]

/-- Transport a finite-arity time Schwartz test across an equality of
coordinate counts. -/
noncomputable def section43TimeSchwartzTransport
    {n m : ℕ}
    (h : n = m)
    (φ : SchwartzMap (Fin n → ℝ) ℂ) :
    SchwartzMap (Fin m → ℝ) ℂ :=
  h ▸ φ

/-- Transport a real finite tuple across an equality of coordinate counts. -/
def section43TimeTupleTransport
    {n m : ℕ}
    (h : n = m)
    (x : Fin n → ℝ) :
    Fin m → ℝ :=
  h ▸ x

@[simp]
theorem section43TimeSchwartzTransport_apply
    {n m : ℕ}
    (h : n = m)
    (φ : SchwartzMap (Fin n → ℝ) ℂ)
    (x : Fin n → ℝ) :
    section43TimeSchwartzTransport h φ
        (section43TimeTupleTransport h x) =
      φ x := by
  subst m
  rfl

/-- Equality transport of finite real tuples preserves Lebesgue
integration. -/
theorem integral_comp_section43TimeTupleTransport
    {n m : ℕ}
    (h : n = m)
    (F : (Fin m → ℝ) → ℂ) :
    (∫ x : Fin n → ℝ,
        F (section43TimeTupleTransport h x)) =
      ∫ y : Fin m → ℝ, F y := by
  subst m
  rfl

/-- Equality transport of finite real tuples is continuous. -/
theorem continuous_section43TimeTupleTransport
    {n m : ℕ}
    (h : n = m) :
    Continuous
      (section43TimeTupleTransport h :
        (Fin n → ℝ) → (Fin m → ℝ)) := by
  subst m
  exact continuous_id

/-- Transport a finite-arity spatial Schwartz test across an equality of
particle counts. -/
noncomputable def section43SpatialSchwartzTransport
    (d : ℕ)
    {n m : ℕ}
    (h : n = m)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ) :
    SchwartzMap (Section43SpatialSpace d m) ℂ :=
  h ▸ χ

/-- Transport a finite-particle spatial tuple across an equality of particle
counts.  Naming this transport keeps spatial chart identities out of raw
dependent equality reduction. -/
def section43SpatialTupleTransport
    (d : ℕ)
    {n m : ℕ}
    (h : n = m)
    (x : Section43SpatialSpace d n) :
    Section43SpatialSpace d m :=
  h ▸ x

@[simp]
theorem section43SpatialSchwartzTransport_apply
    (d : ℕ)
    {n m : ℕ}
    (h : n = m)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (x : Section43SpatialSpace d n) :
    section43SpatialSchwartzTransport d h χ
        (section43SpatialTupleTransport d h x) =
      χ x := by
  subst m
  rfl

@[simp]
theorem section43SpatialTupleTransport_symm
    (d : ℕ)
    {n m : ℕ}
    (h : n = m)
    (x : Section43SpatialSpace d m) :
    section43SpatialTupleTransport d h
        (section43SpatialTupleTransport d h.symm x) = x := by
  subst m
  rfl

/-- Transport across an equality of arities preserves compact support of a
time Schwartz test. -/
theorem section43TimeSchwartzTransport_hasCompactSupport
    {n m : ℕ}
    (h : n = m)
    (φ : SchwartzMap (Fin n → ℝ) ℂ)
    (hφ : HasCompactSupport (φ : (Fin n → ℝ) → ℂ)) :
    HasCompactSupport
      (section43TimeSchwartzTransport h φ :
        (Fin m → ℝ) → ℂ) := by
  subst m
  exact hφ

/-- Equality transport carries topological support by the corresponding tuple
transport. -/
theorem tsupport_section43TimeSchwartzTransport
    {n m : ℕ}
    (h : n = m)
    (φ : SchwartzMap (Fin n → ℝ) ℂ) :
    tsupport
        (section43TimeSchwartzTransport h φ :
          (Fin m → ℝ) → ℂ) =
      section43TimeTupleTransport h ''
        tsupport (φ : (Fin n → ℝ) → ℂ) := by
  cases h
  change tsupport (φ : (Fin n → ℝ) → ℂ) = id '' tsupport (φ : (Fin n → ℝ) → ℂ)
  exact (Set.image_id _).symm

/-- Reindexing an ordered time/spatial tensor by an equality of arities is
the ordered tensor of the transported factors. -/
theorem reindexSchwartz_orderedPullback_timeSpatialTensor
    {n m : ℕ}
    (h : n = m)
    (φ : SchwartzMap (Fin n → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ) :
    reindexSchwartz (d := d) (finCongr h)
        (section43OrderedPullbackTimeSpatialTensorCLM d n χ φ) =
      section43OrderedPullbackTimeSpatialTensorCLM d m
        (section43SpatialSchwartzTransport d h χ)
        (section43TimeSchwartzTransport h φ) := by
  subst m
  ext x
  rfl

/-- Reindex flat `k + 1`-particle spatial coordinates as one `d`-dimensional
head followed by the `k * d` reduced tail coordinates. -/
abbrev section43SpatialHeadTailCast (d k : ℕ) :
    (Fin ((k + 1) * d) → ℝ) ≃L[ℝ] (Fin (d + k * d) → ℝ) :=
  ContinuousLinearEquiv.piCongrLeft ℝ
    (fun _ : Fin (d + k * d) => ℝ)
    (finCongr (by ring : (k + 1) * d = d + k * d))

/-- Insert one spatial basepoint before a reduced spatial difference tuple. -/
noncomputable def section43SpatialPrependBasepoint
    (x₀ : Fin d → ℝ)
    (η : Section43SpatialSpace d k) :
    Section43SpatialSpace d (k + 1) :=
  (EuclideanSpace.equiv
    (ι := Fin (k + 1) × Fin d) (𝕜 := ℝ)).symm
      (fun p =>
        Fin.cases (x₀ p.2)
          (fun i =>
            (EuclideanSpace.equiv
              (ι := Fin k × Fin d) (𝕜 := ℝ) η) (i, p.2))
          p.1)

@[simp]
theorem section43SpatialPrependBasepoint_zero
    (x₀ : Fin d → ℝ)
    (η : Section43SpatialSpace d k)
    (j : Fin d) :
    (EuclideanSpace.equiv
      (ι := Fin (k + 1) × Fin d) (𝕜 := ℝ)
      (section43SpatialPrependBasepoint x₀ η)) (0, j) =
      x₀ j := by
  simp [section43SpatialPrependBasepoint]

@[simp]
theorem section43SpatialPrependBasepoint_succ
    (x₀ : Fin d → ℝ)
    (η : Section43SpatialSpace d k)
    (i : Fin k) (j : Fin d) :
    (EuclideanSpace.equiv
      (ι := Fin (k + 1) × Fin d) (𝕜 := ℝ)
      (section43SpatialPrependBasepoint x₀ η)) (i.succ, j) =
      (EuclideanSpace.equiv
        (ι := Fin k × Fin d) (𝕜 := ℝ) η) (i, j) := by
  simp [section43SpatialPrependBasepoint]

private theorem section43SpatialPrependBasepoint_eq_flat
    (x₀ : Fin d → ℝ)
    (η : Section43SpatialSpace d k) :
    (section43SpatialFlatCLE d (k + 1)).symm
        ((section43SpatialHeadTailCast d k).symm
          (Fin.append x₀ (section43SpatialFlatCLE d k η))) =
      section43SpatialPrependBasepoint x₀ η := by
  apply (EuclideanSpace.equiv
    (ι := Fin (k + 1) × Fin d) (𝕜 := ℝ)).injective
  funext p
  rcases p with ⟨i, j⟩
  refine Fin.cases ?_ ?_ i
  · change
      (Fin.append x₀ (section43SpatialFlatCLE d k η))
          ((finCongr (by ring : (k + 1) * d = d + k * d))
            (finProdFinEquiv (0, j))) =
        x₀ j
    have hindex :
        (finCongr (by ring : (k + 1) * d = d + k * d))
            (finProdFinEquiv (0, j)) =
          Fin.castAdd (k * d) j := by
      apply Fin.ext
      simp [finProdFinEquiv]
    rw [hindex, Fin.append_left]
  · intro i
    change
      (Fin.append x₀ (section43SpatialFlatCLE d k η))
          ((finCongr (by ring : (k + 1) * d = d + k * d))
            (finProdFinEquiv (i.succ, j))) =
        (EuclideanSpace.equiv
          (ι := Fin k × Fin d) (𝕜 := ℝ) η) (i, j)
    have hindex :
        (finCongr (by ring : (k + 1) * d = d + k * d))
            (finProdFinEquiv (i.succ, j)) =
          Fin.natAdd d (finProdFinEquiv (i, j)) := by
      apply Fin.ext
      simp [finProdFinEquiv, Nat.mul_succ, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm]
    rw [hindex, Fin.append_right, section43SpatialFlatCLE_apply]
    simp

/-- Integrate the first spatial point of a full Section 4.3 spatial test. -/
noncomputable def section43SpatialHeadMarginal
    (χ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    SchwartzMap (Section43SpatialSpace d k) ℂ :=
  (section43SpatialFlatSchwartzCLE d k).symm
    (SCV.integrateHeadBlock (m := d) (n := k * d)
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (section43SpatialHeadTailCast d k).symm
        (section43SpatialFlatSchwartzCLE d (k + 1) χ)))

@[simp]
theorem section43SpatialHeadMarginal_apply
    (χ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (η : Section43SpatialSpace d k) :
    section43SpatialHeadMarginal χ η =
      ∫ x₀ : Fin d → ℝ, χ (section43SpatialPrependBasepoint x₀ η) := by
  rw [section43SpatialHeadMarginal,
    section43SpatialFlatSchwartzCLE_symm_apply,
    SCV.integrateHeadBlock_apply_finAppend]
  apply integral_congr_ae
  filter_upwards with x₀
  change
    section43SpatialFlatSchwartzCLE d (k + 1) χ
        ((section43SpatialHeadTailCast d k).symm
          (Fin.append x₀ (section43SpatialFlatCLE d k η))) =
      χ (section43SpatialPrependBasepoint x₀ η)
  rw [section43SpatialFlatSchwartzCLE_apply,
    section43SpatialPrependBasepoint_eq_flat]

/-- Applying the full successive-difference chart to a configuration obtained
from a common basepoint and a reduced difference tuple gives exactly the
basepoint followed by those differences. -/
theorem section43DiffCoordRealCLE_basepoint_diffVarSection
    (a : SpacetimeDim d) (ξ : NPointDomain d k) :
    section43DiffCoordRealCLE d (k + 1)
        (fun i μ => a μ + diffVarSection d k ξ i μ) =
      Fin.cons a ξ := by
  ext i μ
  refine Fin.cases ?_ ?_ i
  · simp [section43DiffCoordRealCLE_apply]
  · intro j
    rw [section43DiffCoordRealCLE_apply]
    simp only [Fin.val_succ, Nat.succ_ne_zero, ↓reduceDIte]
    have hpred :
        (⟨j.val + 1 - 1, by omega⟩ : Fin (k + 1)) =
          j.castSucc := by
      apply Fin.ext
      simp
    rw [hpred, diffVarSection_succ]
    simp

@[simp]
theorem section43QTime_basepoint_diffVarSection
    (a : SpacetimeDim d) (ξ : NPointDomain d k) :
    section43QTime (d := d) (n := k + 1)
        (section43DiffCoordRealCLE d (k + 1)
          (fun i μ => a μ + diffVarSection d k ξ i μ)) =
      Fin.cons (a 0) (section43QTime (d := d) (n := k) ξ) := by
  rw [section43DiffCoordRealCLE_basepoint_diffVarSection]
  ext i
  refine Fin.cases ?_ ?_ i <;>
    simp [section43QTime, nPointTimeSpatialCLE]

@[simp]
theorem section43QSpatial_basepoint_diffVarSection
    (a : SpacetimeDim d) (ξ : NPointDomain d k) :
    section43QSpatial (d := d) (n := k + 1)
        (section43DiffCoordRealCLE d (k + 1)
          (fun i μ => a μ + diffVarSection d k ξ i μ)) =
      section43SpatialPrependBasepoint
        (fun j => a (Fin.succ j))
        (section43QSpatial (d := d) (n := k) ξ) := by
  rw [section43DiffCoordRealCLE_basepoint_diffVarSection]
  apply (EuclideanSpace.equiv
    (ι := Fin (k + 1) × Fin d) (𝕜 := ℝ)).injective
  funext p
  rcases p with ⟨i, j⟩
  refine Fin.cases ?_ ?_ i
  · rw [section43SpatialPrependBasepoint_zero]
    exact section43QSpatial_apply d (k + 1) (Fin.cons a ξ) (0, j)
  · intro i
    rw [section43SpatialPrependBasepoint_succ]
    rw [section43QSpatial_apply, section43QSpatial_apply]
    rfl

/-- Fiber reduction of an ordered full time/spatial tensor separates into the
head time integral and the head spatial block integral. -/
theorem diffVarReduction_orderedPullback_timeSpatialTensor
    (φ : SchwartzMap (Fin (k + 1) → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    diffVarReduction d k
        (section43OrderedPullbackTimeSpatialTensorCLM d (k + 1) χ φ) =
      section43NPointTimeSpatialTensor d k
        (SCV.sliceIntegral φ)
        (section43SpatialHeadMarginal χ) := by
  ext ξ
  change
    (∫ a : SpacetimeDim d,
      section43OrderedPullbackTimeSpatialTensorCLM d (k + 1) χ φ
        (fun i μ => a μ + diffVarSection d k ξ i μ)) =
      _
  calc
    (∫ a : SpacetimeDim d,
        section43OrderedPullbackTimeSpatialTensorCLM d (k + 1) χ φ
          (fun i μ => a μ + diffVarSection d k ξ i μ)) =
      ∫ p : ℝ × (Fin d → ℝ),
        section43OrderedPullbackTimeSpatialTensorCLM d (k + 1) χ φ
          (fun i μ =>
            (Fin.cons p.1 p.2 : SpacetimeDim d) μ +
              diffVarSection d k ξ i μ)
          ∂((volume : Measure ℝ).prod
            (volume : Measure (Fin d → ℝ))) := by
        simpa [MeasureTheory.volume_pi] using
          (integral_finSucc_cons_eq
            (f := fun a : SpacetimeDim d =>
              section43OrderedPullbackTimeSpatialTensorCLM
                d (k + 1) χ φ
                (fun i μ => a μ + diffVarSection d k ξ i μ))).symm
    _ =
      ∫ p : ℝ × (Fin d → ℝ),
        φ (Fin.cons p.1 (section43QTime (d := d) (n := k) ξ)) *
          χ (section43SpatialPrependBasepoint p.2
            (section43QSpatial (d := d) (n := k) ξ))
          ∂((volume : Measure ℝ).prod
            (volume : Measure (Fin d → ℝ))) := by
        apply integral_congr_ae
        filter_upwards with p
        simp [section43OrderedPullbackTimeSpatialTensorCLM_apply,
          section43NPointTimeSpatialTensor_apply]
    _ =
      (∫ t : ℝ,
          φ (Fin.cons t (section43QTime (d := d) (n := k) ξ))) *
        ∫ x₀ : Fin d → ℝ,
          χ (section43SpatialPrependBasepoint x₀
            (section43QSpatial (d := d) (n := k) ξ)) := by
        simpa using
          (integral_prod_mul
            (μ := (volume : Measure ℝ))
            (ν := (volume : Measure (Fin d → ℝ)))
            (fun t : ℝ =>
              φ (Fin.cons t
                (section43QTime (d := d) (n := k) ξ)))
            (fun x₀ : Fin d → ℝ =>
              χ (section43SpatialPrependBasepoint x₀
                (section43QSpatial (d := d) (n := k) ξ))))
    _ =
      SCV.sliceIntegral φ
          (section43QTime (d := d) (n := k) ξ) *
        section43SpatialHeadMarginal χ
          (section43QSpatial (d := d) (n := k) ξ) := by
        simp [SCV.sliceIntegral_apply, SCV.sliceIntegralRaw]
    _ =
      section43NPointTimeSpatialTensor d k
        (SCV.sliceIntegral φ)
        (section43SpatialHeadMarginal χ) ξ := by
        rw [section43NPointTimeSpatialTensor_apply]

end OSIIChapterV
end OSReconstruction
