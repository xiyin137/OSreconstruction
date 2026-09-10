import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTransform
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43SpectralSupport
import OSReconstruction.Wightman.Reconstruction.WickRotation.BHWReducedExtension
import OSReconstruction.GeneralResults.FinProductIntegral
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Group.Prod

noncomputable section

open scoped Topology FourierTransform
open Set MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- The real difference-coordinate map as a measurable equivalence, with the
direction used for absolute-to-difference coordinate changes. -/
noncomputable def section43DiffCoordRealMeasurableEquiv
    (d n : ℕ) [NeZero d] :
    NPointDomain d n ≃ᵐ NPointDomain d n :=
  (section43DiffCoordRealCLE d n).toHomeomorph.toMeasurableEquiv

/-- The inverse real difference-coordinate map preserves Lebesgue measure. -/
theorem section43DiffCoordRealCLE_symm_measurePreserving
    (d n : ℕ) [NeZero d] :
    MeasurePreserving
      (section43DiffCoordRealMeasurableEquiv d n).symm
      (volume : Measure (NPointDomain d n))
      (volume : Measure (NPointDomain d n)) := by
  simpa [section43DiffCoordRealMeasurableEquiv, section43DiffCoordRealCLE] using
    (BHW.realDiffCoordCLE_symm_measurePreserving n d)

/-- The real difference-coordinate map preserves Lebesgue measure. -/
theorem section43DiffCoordRealCLE_measurePreserving
    (d n : ℕ) [NeZero d] :
    MeasurePreserving
      (section43DiffCoordRealMeasurableEquiv d n)
      (volume : Measure (NPointDomain d n))
      (volume : Measure (NPointDomain d n)) := by
  simpa using (section43DiffCoordRealCLE_symm_measurePreserving d n).symm

/-- Split `Fin (d + 1)` into its time coordinate and spatial coordinates. -/
def section43FinSuccTimeSpatialEquiv (d : ℕ) :
    Fin (d + 1) ≃ PUnit.{1} ⊕ Fin d where
  toFun μ :=
    if h : μ = 0 then Sum.inl PUnit.unit
    else Sum.inr ⟨μ.val - 1, by
      have hμ : μ.val < d + 1 := μ.isLt
      have hpos : 0 < μ.val := by
        exact Nat.pos_of_ne_zero (by
          intro hzero
          apply h
          exact Fin.ext hzero)
      omega⟩
  invFun s :=
    match s with
    | Sum.inl _ => 0
    | Sum.inr μ => Fin.succ μ
  left_inv := by
    intro μ
    by_cases h : μ = 0
    · simp [h]
    · simp [h]
      apply Fin.ext
      have hpos : 0 < μ.val := by
        exact Nat.pos_of_ne_zero (by
          intro hzero
          apply h
          exact Fin.ext hzero)
      simp
      omega
  right_inv := by
    intro s
    cases s with
    | inl u =>
        cases u
        simp
    | inr μ =>
        simp [Fin.succ_ne_zero]

@[simp] theorem section43FinSuccTimeSpatialEquiv_zero (d : ℕ) :
    section43FinSuccTimeSpatialEquiv d (0 : Fin (d + 1)) =
      Sum.inl PUnit.unit := by
  simp [section43FinSuccTimeSpatialEquiv]

@[simp] theorem section43FinSuccTimeSpatialEquiv_succ (d : ℕ) (μ : Fin d) :
    section43FinSuccTimeSpatialEquiv d (Fin.succ μ) = Sum.inr μ := by
  simp [section43FinSuccTimeSpatialEquiv, Fin.succ_ne_zero]

/-- Split a spacetime index into a time-coordinate index or a spatial-coordinate
index. -/
def section43TimeSpatialIndexEquiv (d n : ℕ) :
    Fin n × Fin (d + 1) ≃ Fin n ⊕ (Fin n × Fin d) :=
  (((Equiv.refl (Fin n)).prodCongr (section43FinSuccTimeSpatialEquiv d)).trans
      (Equiv.prodSumDistrib (Fin n) PUnit.{1} (Fin d))).trans
    (Equiv.sumCongr (Equiv.prodPUnit (Fin n)) (Equiv.refl (Fin n × Fin d)))

@[simp] theorem section43TimeSpatialIndexEquiv_time
    (d n : ℕ) (i : Fin n) :
    section43TimeSpatialIndexEquiv d n (i, (0 : Fin (d + 1))) =
      Sum.inl i := by
  simp [section43TimeSpatialIndexEquiv]

@[simp] theorem section43TimeSpatialIndexEquiv_spatial
    (d n : ℕ) (i : Fin n) (μ : Fin d) :
    section43TimeSpatialIndexEquiv d n (i, Fin.succ μ) =
      Sum.inr (i, μ) := by
  simp [section43TimeSpatialIndexEquiv]

@[simp] theorem section43TimeSpatialIndexEquiv_symm_time
    (d n : ℕ) (i : Fin n) :
    (section43TimeSpatialIndexEquiv d n).symm (Sum.inl i) =
      (i, (0 : Fin (d + 1))) := by
  rw [Equiv.symm_apply_eq]
  exact section43TimeSpatialIndexEquiv_time d n i

@[simp] theorem section43TimeSpatialIndexEquiv_symm_spatial
    (d n : ℕ) (i : Fin n) (μ : Fin d) :
    (section43TimeSpatialIndexEquiv d n).symm (Sum.inr (i, μ)) =
      (i, Fin.succ μ) := by
  rw [Equiv.symm_apply_eq]
  exact section43TimeSpatialIndexEquiv_spatial d n i μ

private theorem section43_volume_map_curry_symm (α β : Type*)
    [Fintype α] [Fintype β] :
    (volume : Measure (α → β → ℝ)).map
      (MeasurableEquiv.curry α β ℝ).symm =
    (volume : Measure (α × β → ℝ)) := by
  symm
  apply MeasureTheory.Measure.pi_eq
  intro s hs
  rw [MeasureTheory.Measure.map_apply
    (MeasurableEquiv.curry α β ℝ).symm.measurable
    (MeasurableSet.univ_pi hs)]
  have h_preimage : (MeasurableEquiv.curry α β ℝ).symm ⁻¹'
      (Set.univ.pi s) = Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_univ_pi, MeasurableEquiv.coe_curry_symm,
      Function.uncurry]
    exact ⟨fun h i j => h (i, j), fun h ⟨i, j⟩ => h i j⟩
  rw [h_preimage, MeasureTheory.volume_pi_pi]
  simp_rw [MeasureTheory.volume_pi_pi]
  rw [← Finset.prod_product', ← Finset.univ_product_univ]

/-- Function-space version of the time/spatial split for `NPointDomain`. -/
noncomputable def section43TimeSpatialFunctionMeasurableEquiv
    (d n : ℕ) :
    NPointDomain d n ≃ᵐ
      (Fin n → ℝ) × (Fin n × Fin d → ℝ) :=
  ((MeasurableEquiv.curry (Fin n) (Fin (d + 1)) ℝ).symm.trans
      (MeasurableEquiv.piCongrLeft (fun _ => ℝ)
        (section43TimeSpatialIndexEquiv d n))).trans
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Fin n ⊕ (Fin n × Fin d) => ℝ))

@[simp] theorem section43TimeSpatialFunctionMeasurableEquiv_apply_fst
    (d n : ℕ) (x : NPointDomain d n) :
    (section43TimeSpatialFunctionMeasurableEquiv d n x).1 =
      fun i : Fin n => x i 0 := by
  ext i
  change
    (Equiv.piCongrLeft (fun _ => ℝ) (section43TimeSpatialIndexEquiv d n)
      (Function.uncurry x) (Sum.inl i)) = x i 0
  rw [Equiv.piCongrLeft_apply_eq_cast]
  simp

@[simp] theorem section43TimeSpatialFunctionMeasurableEquiv_apply_snd
    (d n : ℕ) (x : NPointDomain d n) :
    (section43TimeSpatialFunctionMeasurableEquiv d n x).2 =
      fun p : Fin n × Fin d => x p.1 (Fin.succ p.2) := by
  ext p
  rcases p with ⟨i, μ⟩
  change
    (Equiv.piCongrLeft (fun _ => ℝ) (section43TimeSpatialIndexEquiv d n)
      (Function.uncurry x) (Sum.inr (i, μ))) = x i (Fin.succ μ)
  rw [Equiv.piCongrLeft_apply_eq_cast]
  simp

/-- The function-space time/spatial split preserves product Lebesgue measure. -/
theorem section43TimeSpatialFunctionMeasurableEquiv_measurePreserving
    (d n : ℕ) :
    MeasurePreserving
      (section43TimeSpatialFunctionMeasurableEquiv d n)
      (volume : Measure (NPointDomain d n))
      (volume : Measure ((Fin n → ℝ) × (Fin n × Fin d → ℝ))) := by
  unfold section43TimeSpatialFunctionMeasurableEquiv
  have h_uncurry :
      MeasurePreserving
        (MeasurableEquiv.curry (Fin n) (Fin (d + 1)) ℝ).symm
        (volume : Measure (NPointDomain d n))
        (volume : Measure (Fin n × Fin (d + 1) → ℝ)) := by
    refine ⟨(MeasurableEquiv.curry (Fin n) (Fin (d + 1)) ℝ).symm.measurable, ?_⟩
    exact section43_volume_map_curry_symm (Fin n) (Fin (d + 1))
  exact
    (h_uncurry.trans
      (MeasureTheory.volume_measurePreserving_piCongrLeft
        (fun _ => ℝ) (section43TimeSpatialIndexEquiv d n))).trans
      (MeasureTheory.volume_measurePreserving_sumPiEquivProdPi
        (fun _ : Fin n ⊕ (Fin n × Fin d) => ℝ))

/-- The canonical measurable equivalence between finite Euclidean coordinates
and the corresponding function space, with the direction used by
`nPointTimeSpatialCLE`. -/
noncomputable def section43EuclideanSpaceMeasurableEquiv
    (ι : Type*) [Fintype ι] :
    EuclideanSpace ℝ ι ≃ᵐ (ι → ℝ) :=
  (EuclideanSpace.equiv (ι := ι) (𝕜 := ℝ)).toHomeomorph.toMeasurableEquiv

/-- The canonical Euclidean coordinate equivalence preserves Lebesgue measure. -/
theorem section43EuclideanSpaceMeasurableEquiv_measurePreserving
    (ι : Type*) [Fintype ι] :
    MeasurePreserving
      (section43EuclideanSpaceMeasurableEquiv ι)
      (volume : Measure (EuclideanSpace ℝ ι))
      (volume : Measure (ι → ℝ)) := by
  simpa [section43EuclideanSpaceMeasurableEquiv, EuclideanSpace.equiv] using
    (PiLp.volume_preserving_ofLp ι)

/-- The measurable time/spatial split with the spatial block in the
`EuclideanSpace` surface used by `partialFourierSpatial_fun`. -/
noncomputable def section43NPointTimeSpatialMeasurableEquiv
    (d n : ℕ) [NeZero d] :
    NPointDomain d n ≃ᵐ
      (Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d) :=
  (section43TimeSpatialFunctionMeasurableEquiv d n).trans
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl (Fin n → ℝ))
      (section43EuclideanSpaceMeasurableEquiv (Fin n × Fin d)).symm)

@[simp] theorem section43NPointTimeSpatialMeasurableEquiv_apply
    (d n : ℕ) [NeZero d] (x : NPointDomain d n) :
    section43NPointTimeSpatialMeasurableEquiv d n x =
      nPointTimeSpatialCLE (d := d) n x := by
  ext i
  · change (section43TimeSpatialFunctionMeasurableEquiv d n x).1 i = x i 0
    simp
  · change
      (((section43EuclideanSpaceMeasurableEquiv (Fin n × Fin d)).symm
          ((section43TimeSpatialFunctionMeasurableEquiv d n x).2)).ofLp i) =
        x i.1 (Fin.succ i.2)
    simp [section43EuclideanSpaceMeasurableEquiv]

/-- The time/spatial split preserves product Lebesgue measure. -/
theorem section43NPointTimeSpatialCLE_measurePreserving
    (d n : ℕ) [NeZero d] :
    MeasurePreserving
      (section43NPointTimeSpatialMeasurableEquiv d n)
      (volume : Measure (NPointDomain d n))
      (volume : Measure
        ((Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d))) := by
  unfold section43NPointTimeSpatialMeasurableEquiv
  exact
    (section43TimeSpatialFunctionMeasurableEquiv_measurePreserving d n).trans
      ((MeasurePreserving.id (volume : Measure (Fin n → ℝ))).prod
        (section43EuclideanSpaceMeasurableEquiv_measurePreserving (Fin n × Fin d)).symm)

@[simp] theorem section43NPointTimeSpatialMeasurableEquiv_symm_apply_time
    (d n : ℕ) [NeZero d]
    (p : (Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d))
    (k : Fin n) :
    ((section43NPointTimeSpatialMeasurableEquiv d n).symm p) k 0 =
      p.1 k := by
  have h :=
    congrArg Prod.fst
      ((section43NPointTimeSpatialMeasurableEquiv d n).apply_symm_apply p)
  change (section43TimeSpatialFunctionMeasurableEquiv d n
    ((section43NPointTimeSpatialMeasurableEquiv d n).symm p)).1 = p.1 at h
  exact congrFun h k

@[simp] theorem section43NPointTimeSpatialMeasurableEquiv_symm_apply_spatial
    (d n : ℕ) [NeZero d]
    (p : (Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d))
    (i : Fin n × Fin d) :
    ((section43NPointTimeSpatialMeasurableEquiv d n).symm p) i.1
        (Fin.succ i.2) =
      (EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ) p.2) i := by
  have h :=
    congrArg Prod.snd
      ((section43NPointTimeSpatialMeasurableEquiv d n).apply_symm_apply p)
  change ((section43EuclideanSpaceMeasurableEquiv (Fin n × Fin d)).symm
    (section43TimeSpatialFunctionMeasurableEquiv d n
      ((section43NPointTimeSpatialMeasurableEquiv d n).symm p)).2) = p.2 at h
  have h2 := congrArg (section43EuclideanSpaceMeasurableEquiv (Fin n × Fin d)) h
  simp [section43EuclideanSpaceMeasurableEquiv] at h2
  have hcoord :=
    congrArg
      (fun v : EuclideanSpace ℝ (Fin n × Fin d) =>
        (EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ) v) i)
      h2
  simpa [section43EuclideanSpaceMeasurableEquiv] using hcoord

/-- Applying the unscaled cumulative-tail map to the inverse scaled
Section-4.3 cumulative-tail coordinates removes exactly the spatial Fourier
normalization. -/
theorem section43RawCumulativeTail_of_cumulativeTailMomentum_symm
    (d n : ℕ) [NeZero d] (q : NPointDomain d n) :
    section43RawCumulativeTailMomentumCLE d n
      ((section43CumulativeTailMomentumCLE d n).symm q) =
    (section43SpatialFourierScaleCLE d n).symm q := by
  rw [section43CumulativeTailMomentumCLE]
  simp

/-- Coordinatewise form of the difference-coordinate/cumulative-tail pairing.
This is the local one-coordinate version used to split the Wick-rotated phase
into time and spatial pieces. -/
theorem section43DiffCoord_pairing_coord_eq_rawCumulativeTail
    (d n : ℕ) [NeZero d]
    (δ : NPointDomain d n)
    (ξ : Fin (n * (d + 1)) → ℝ)
    (μ : Fin (d + 1)) :
    (∑ k : Fin n,
        (section43DiffCoordRealCLE d n).symm δ k μ *
          ξ (finProdFinEquiv (k, μ))) =
    ∑ j : Fin n,
      δ j μ * section43RawCumulativeTailMomentumCLE d n ξ j μ := by
  classical
  calc
    (∑ k : Fin n,
        (section43DiffCoordRealCLE d n).symm δ k μ *
          ξ (finProdFinEquiv (k, μ)))
        = ∑ k : Fin n,
            (∑ l : Fin (k.val + 1), δ ⟨l.val, by omega⟩ μ) *
              ξ (finProdFinEquiv (k, μ)) := by
          simp only [section43DiffCoordRealCLE_symm_apply]
    _ = ∑ j : Fin n,
          δ j μ * ∑ k : Fin n,
            if j.val ≤ k.val then ξ (finProdFinEquiv (k, μ)) else 0 := by
          exact section43_fin_prefix_mul_eq_sum_tail_public
            (fun j : Fin n => δ j μ)
            (fun k : Fin n => ξ (finProdFinEquiv (k, μ)))
    _ = ∑ j : Fin n,
          δ j μ * section43RawCumulativeTailMomentumCLE d n ξ j μ := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          simp [section43RawCumulativeTailMomentumCLE_apply]

private theorem section43WickRotatePairing_timePart_after_diffCoord_symm
    (d n : ℕ) [NeZero d]
    (q δ : NPointDomain d n) :
    Complex.I *
      (∑ k : Fin n,
        wickRotatePoint (((section43DiffCoordRealCLE d n).symm δ) k) 0 *
          (((section43CumulativeTailMomentumCLE d n).symm q
            (finProdFinEquiv (k, (0 : Fin (d + 1)))) : ℝ) : ℂ)) =
    -(∑ j : Fin n, (δ j 0 : ℂ) *
      (section43QTime (d := d) (n := n) q j : ℂ)) := by
  classical
  let ξ : Fin (n * (d + 1)) → ℝ :=
    (section43CumulativeTailMomentumCLE d n).symm q
  let y : NPointDomain d n := (section43DiffCoordRealCLE d n).symm δ
  have hreal :
      (∑ k : Fin n,
        y k 0 * ξ (finProdFinEquiv (k, (0 : Fin (d + 1))))) =
      ∑ j : Fin n, δ j 0 * q j 0 := by
    have h := section43DiffCoord_pairing_coord_eq_rawCumulativeTail
      d n δ ξ (0 : Fin (d + 1))
    rw [section43RawCumulativeTail_of_cumulativeTailMomentum_symm] at h
    simpa [ξ, y] using h
  have hcomplex :
      (∑ k : Fin n,
        (y k 0 : ℂ) *
          (ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) : ℂ)) =
      ∑ j : Fin n, (δ j 0 : ℂ) * (q j 0 : ℂ) := by
    exact_mod_cast hreal
  calc
    Complex.I *
      (∑ k : Fin n,
        wickRotatePoint (((section43DiffCoordRealCLE d n).symm δ) k) 0 *
          (((section43CumulativeTailMomentumCLE d n).symm q
            (finProdFinEquiv (k, (0 : Fin (d + 1)))) : ℝ) : ℂ))
        = Complex.I * (∑ k : Fin n,
            (Complex.I * (y k 0 : ℂ)) *
              (ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) : ℂ)) := by
          simp [y, ξ, wickRotatePoint]
    _ = Complex.I * (Complex.I *
            (∑ k : Fin n,
              (y k 0 : ℂ) *
                (ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) : ℂ))) := by
          congr 1
          calc
            (∑ k : Fin n,
              (Complex.I * (y k 0 : ℂ)) *
                (ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) : ℂ))
                = ∑ k : Fin n,
                    Complex.I *
                      ((y k 0 : ℂ) *
                        (ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) : ℂ)) := by
                  refine Finset.sum_congr rfl ?_
                  intro k _hk
                  ring
            _ = Complex.I *
                (∑ k : Fin n,
                  (y k 0 : ℂ) *
                    (ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) : ℂ)) := by
                  rw [Finset.mul_sum]
    _ = - (∑ k : Fin n,
            (y k 0 : ℂ) *
              (ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) : ℂ)) := by
          rw [← mul_assoc, Complex.I_mul_I]
          simp
    _ = -(∑ j : Fin n, (δ j 0 : ℂ) *
          (section43QTime (d := d) (n := n) q j : ℂ)) := by
          rw [hcomplex]
          simp [section43QTime, nPointTimeSpatialCLE]

private theorem section43WickRotatePairing_spatialPart_after_diffCoord_symm
    (d n : ℕ) [NeZero d]
    (q δ : NPointDomain d n) :
    Complex.I *
      (∑ k : Fin n, ∑ μ : Fin d,
        wickRotatePoint (((section43DiffCoordRealCLE d n).symm δ) k)
          (Fin.succ μ) *
          (((section43CumulativeTailMomentumCLE d n).symm q
            (finProdFinEquiv (k, Fin.succ μ)) : ℝ) : ℂ)) =
    -(2 * Real.pi : ℂ) * Complex.I *
      ∑ p : Fin n × Fin d,
        (δ p.1 (Fin.succ p.2) : ℂ) *
          ((EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ)
            (section43QSpatial (d := d) (n := n) q)) p : ℂ) := by
  classical
  let ξ : Fin (n * (d + 1)) → ℝ :=
    (section43CumulativeTailMomentumCLE d n).symm q
  let y : NPointDomain d n := (section43DiffCoordRealCLE d n).symm δ
  have hreal_mu (μ : Fin d) :
      (∑ k : Fin n,
        y k (Fin.succ μ) * ξ (finProdFinEquiv (k, Fin.succ μ))) =
      ∑ j : Fin n,
        δ j (Fin.succ μ) * (-(2 * Real.pi) * q j (Fin.succ μ)) := by
    have h := section43DiffCoord_pairing_coord_eq_rawCumulativeTail
      d n δ ξ (Fin.succ μ)
    rw [section43RawCumulativeTail_of_cumulativeTailMomentum_symm] at h
    simpa [ξ, y] using h
  have hreal :
      (∑ k : Fin n, ∑ μ : Fin d,
        y k (Fin.succ μ) * ξ (finProdFinEquiv (k, Fin.succ μ))) =
      -(2 * Real.pi) *
        ∑ p : Fin n × Fin d, δ p.1 (Fin.succ p.2) *
          q p.1 (Fin.succ p.2) := by
    calc
      (∑ k : Fin n, ∑ μ : Fin d,
        y k (Fin.succ μ) * ξ (finProdFinEquiv (k, Fin.succ μ)))
          = ∑ μ : Fin d, ∑ k : Fin n,
              y k (Fin.succ μ) * ξ (finProdFinEquiv (k, Fin.succ μ)) := by
            rw [Finset.sum_comm]
      _ = ∑ μ : Fin d, ∑ j : Fin n,
              δ j (Fin.succ μ) * (-(2 * Real.pi) * q j (Fin.succ μ)) := by
            refine Finset.sum_congr rfl ?_
            intro μ _hμ
            exact hreal_mu μ
      _ = ∑ j : Fin n, ∑ μ : Fin d,
              δ j (Fin.succ μ) * (-(2 * Real.pi) * q j (Fin.succ μ)) := by
            rw [Finset.sum_comm]
      _ = ∑ p : Fin n × Fin d,
              δ p.1 (Fin.succ p.2) *
                (-(2 * Real.pi) * q p.1 (Fin.succ p.2)) := by
            simpa using
              (Finset.sum_product (s := (Finset.univ : Finset (Fin n)))
                (t := (Finset.univ : Finset (Fin d)))
                (f := fun p : Fin n × Fin d =>
                  δ p.1 (Fin.succ p.2) *
                    (-(2 * Real.pi) * q p.1 (Fin.succ p.2)))).symm
      _ = -(2 * Real.pi) *
            ∑ p : Fin n × Fin d,
              δ p.1 (Fin.succ p.2) * q p.1 (Fin.succ p.2) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro p _hp
            ring
  have hcomplex :
      (∑ k : Fin n, ∑ μ : Fin d,
        (y k (Fin.succ μ) : ℂ) *
          (ξ (finProdFinEquiv (k, Fin.succ μ)) : ℂ)) =
      -(2 * Real.pi : ℂ) *
        ∑ p : Fin n × Fin d,
          (δ p.1 (Fin.succ p.2) : ℂ) *
            (q p.1 (Fin.succ p.2) : ℂ) := by
    exact_mod_cast hreal
  have hqsp :
      (∑ p : Fin n × Fin d,
          (δ p.1 (Fin.succ p.2) : ℂ) *
            (q p.1 (Fin.succ p.2) : ℂ)) =
      ∑ p : Fin n × Fin d,
        (δ p.1 (Fin.succ p.2) : ℂ) *
          ((EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ)
            (section43QSpatial (d := d) (n := n) q)) p : ℂ) := by
    refine Finset.sum_congr rfl ?_
    intro p _hp
    rw [section43QSpatial_apply]
  calc
    Complex.I *
      (∑ k : Fin n, ∑ μ : Fin d,
        wickRotatePoint (((section43DiffCoordRealCLE d n).symm δ) k)
          (Fin.succ μ) *
          (((section43CumulativeTailMomentumCLE d n).symm q
            (finProdFinEquiv (k, Fin.succ μ)) : ℝ) : ℂ))
        = Complex.I *
          (∑ k : Fin n, ∑ μ : Fin d,
            (y k (Fin.succ μ) : ℂ) *
              (ξ (finProdFinEquiv (k, Fin.succ μ)) : ℂ)) := by
          simp [y, ξ, wickRotatePoint]
    _ = Complex.I * (-(2 * Real.pi : ℂ) *
          ∑ p : Fin n × Fin d,
            (δ p.1 (Fin.succ p.2) : ℂ) *
              (q p.1 (Fin.succ p.2) : ℂ)) := by
          rw [hcomplex]
    _ = -(2 * Real.pi : ℂ) * Complex.I *
      ∑ p : Fin n × Fin d,
        (δ p.1 (Fin.succ p.2) : ℂ) *
          ((EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ)
            (section43QSpatial (d := d) (n := n) q)) p : ℂ) := by
          rw [← hqsp]
          ring

/-- The Wick-rotated absolute-coordinate phase equals the
Fourier-Laplace phase after difference coordinates and the Section 4.3
cumulative-tail momentum normalization. -/
theorem section43WickRotatePhase_after_diffCoord_symm_eq_fourierLaplacePhase
    (d n : ℕ) [NeZero d]
    (q : NPointDomain d n)
    (δ : NPointDomain d n) :
    Complex.I *
        ∑ i : Fin (n * (d + 1)),
          flattenCLEquiv n (d + 1)
            (fun k => wickRotatePoint
              (((section43DiffCoordRealCLE d n).symm δ) k)) i *
          (((section43CumulativeTailMomentumCLE d n).symm q i : ℝ) : ℂ)
      =
    -(∑ k : Fin n,
        (δ k 0 : ℂ) *
          (section43QTime (d := d) (n := n) q k : ℂ)) -
      (2 * Real.pi : ℂ) * Complex.I *
        ∑ p : Fin n × Fin d,
          (δ p.1 (Fin.succ p.2) : ℂ) *
            ((EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ)
              (section43QSpatial (d := d) (n := n) q)) p : ℂ) := by
  classical
  let ξ : Fin (n * (d + 1)) → ℝ :=
    (section43CumulativeTailMomentumCLE d n).symm q
  let y : NPointDomain d n := (section43DiffCoordRealCLE d n).symm δ
  have hsplit :
      (∑ i : Fin (n * (d + 1)),
          flattenCLEquiv n (d + 1)
            (fun k => wickRotatePoint (y k)) i * (ξ i : ℂ)) =
      (∑ k : Fin n,
        wickRotatePoint (y k) 0 *
          (ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) : ℂ)) +
      (∑ k : Fin n, ∑ μ : Fin d,
        wickRotatePoint (y k) (Fin.succ μ) *
          (ξ (finProdFinEquiv (k, Fin.succ μ)) : ℂ)) := by
    calc
      (∑ i : Fin (n * (d + 1)),
          flattenCLEquiv n (d + 1)
            (fun k => wickRotatePoint (y k)) i * (ξ i : ℂ))
          = ∑ p : Fin n × Fin (d + 1),
              flattenCLEquiv n (d + 1)
                (fun k => wickRotatePoint (y k)) (finProdFinEquiv p) *
                (ξ (finProdFinEquiv p) : ℂ) := by
            simpa using
              (finProdFinEquiv.sum_comp
                (fun i : Fin (n * (d + 1)) =>
                  flattenCLEquiv n (d + 1)
                    (fun k => wickRotatePoint (y k)) i * (ξ i : ℂ))).symm
      _ = ∑ k : Fin n, ∑ μ : Fin (d + 1),
              wickRotatePoint (y k) μ *
                (ξ (finProdFinEquiv (k, μ)) : ℂ) := by
            simpa [flattenCLEquiv_apply] using
              (Finset.sum_product (s := (Finset.univ : Finset (Fin n)))
                (t := (Finset.univ : Finset (Fin (d + 1))))
                (f := fun p : Fin n × Fin (d + 1) =>
                  wickRotatePoint (y p.1) p.2 *
                    (ξ (finProdFinEquiv p) : ℂ)))
      _ = ∑ k : Fin n,
            (wickRotatePoint (y k) 0 *
                (ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) : ℂ) +
             ∑ μ : Fin d,
              wickRotatePoint (y k) (Fin.succ μ) *
                (ξ (finProdFinEquiv (k, Fin.succ μ)) : ℂ)) := by
            refine Finset.sum_congr rfl ?_
            intro k _hk
            rw [Fin.sum_univ_succ]
      _ = (∑ k : Fin n,
            wickRotatePoint (y k) 0 *
              (ξ (finProdFinEquiv (k, (0 : Fin (d + 1)))) : ℂ)) +
          (∑ k : Fin n, ∑ μ : Fin d,
            wickRotatePoint (y k) (Fin.succ μ) *
              (ξ (finProdFinEquiv (k, Fin.succ μ)) : ℂ)) := by
            rw [Finset.sum_add_distrib]
  rw [show (fun k => wickRotatePoint
      (((section43DiffCoordRealCLE d n).symm δ) k)) =
      (fun k => wickRotatePoint (y k)) by rfl]
  change Complex.I *
      (∑ i : Fin (n * (d + 1)),
          flattenCLEquiv n (d + 1)
            (fun k => wickRotatePoint (y k)) i * (ξ i : ℂ)) = _
  rw [hsplit, mul_add]
  rw [section43WickRotatePairing_timePart_after_diffCoord_symm
    (d := d) (n := n) q δ]
  rw [section43WickRotatePairing_spatialPart_after_diffCoord_symm
    (d := d) (n := n) q δ]
  ring

private theorem section43FourierLaplacePhase_norm_exp_le_one_of_nonneg
    (d n : ℕ) [NeZero d]
    (q δ : NPointDomain d n)
    (hq : q ∈ section43PositiveEnergyRegion d n)
    (hδ : ∀ k : Fin n, 0 ≤ δ k 0) :
    ‖Complex.exp
      (-(∑ k : Fin n,
          (δ k 0 : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ)) -
        (2 * Real.pi : ℂ) * Complex.I *
          ∑ p : Fin n × Fin d,
            (δ p.1 (Fin.succ p.2) : ℂ) *
              ((EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ)
                (section43QSpatial (d := d) (n := n) q)) p : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  apply Real.exp_le_one_iff.mpr
  have hsum_nonneg :
      0 ≤ ∑ k : Fin n,
        δ k 0 * section43QTime (d := d) (n := n) q k := by
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hδ k) (by
      simpa [section43QTime, nPointTimeSpatialCLE] using hq k)
  have hre :
      (-(∑ k : Fin n,
          (δ k 0 : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ)) -
        (2 * Real.pi : ℂ) * Complex.I *
          ∑ p : Fin n × Fin d,
            (δ p.1 (Fin.succ p.2) : ℂ) *
              ((EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ)
                (section43QSpatial (d := d) (n := n) q)) p : ℂ)).re =
        -(∑ k : Fin n,
          δ k 0 * section43QTime (d := d) (n := n) q k) := by
    simp
  rw [hre]
  exact neg_nonpos.mpr hsum_nonneg

private theorem section43SpatialFourierPhase_eq_fourierChar
    (d n : ℕ) [NeZero d]
    (η ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    Complex.exp
      (-(2 * Real.pi : ℂ) * Complex.I *
        ∑ p : Fin n × Fin d,
          ((EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ) η) p : ℂ) *
            ((EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ) ξ) p : ℂ)) =
      ((𝐞 (-(inner ℝ η ξ)) : Circle) : ℂ) := by
  rw [Real.fourierChar_apply]
  have hinner : inner ℝ η ξ =
      ∑ p : Fin n × Fin d,
        (EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ) ξ) p *
          (EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ) η) p := by
    rw [PiLp.inner_apply]
    rfl
  rw [hinner]
  congr 1
  simp [Finset.mul_sum, mul_assoc, mul_comm]

private theorem section43SchwartzNPoint_integrable
    (d n : ℕ) [NeZero d] (φ : SchwartzNPoint d n) :
    Integrable φ (volume : Measure (NPointDomain d n)) := by
  let flatφ : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (flattenCLEquivReal n (d + 1)).symm φ
  have hflat_int :
      Integrable flatφ (volume : Measure (Fin (n * (d + 1)) → ℝ)) := by
    exact flatφ.integrable
  have hcomp : Integrable (flatφ ∘ flattenMeasurableEquiv n (d + 1))
      (volume : Measure (NPointDomain d n)) := by
    exact
      (flattenMeasurableEquiv_measurePreserving n (d + 1)).integrable_comp_of_integrable
        hflat_int
  have hEq : flatφ ∘ flattenMeasurableEquiv n (d + 1) = φ := by
    funext x
    have harg :
        (flattenCLEquivReal n (d + 1)).symm
          ((flattenMeasurableEquiv n (d + 1)) x) = x := by
      ext k μ
      rw [flattenCLEquivReal_symm_apply]
      simp [flattenMeasurableEquiv_apply]
    simp [flatφ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, harg]
  simpa [hEq] using hcomp

/-- The absolute Wick-rotated phase integral is integrable on the
positive-energy spectral region.  The proof changes to difference coordinates,
uses the phase identity above, and bounds the exponential by `1` on the
positive-time support of the OS I difference-coordinate pullback. -/
theorem integrable_section43WickRotatePhaseIntegral_of_mem_positiveEnergy
    (d n : ℕ) [NeZero d]
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (q : NPointDomain d n)
    (hq : q ∈ section43PositiveEnergyRegion d n) :
    Integrable
      (fun x : NPointDomain d n =>
        Complex.exp
          (Complex.I *
            ∑ i : Fin (n * (d + 1)),
              flattenCLEquiv n (d + 1)
                (fun k => wickRotatePoint (x k)) i *
              (((section43CumulativeTailMomentumCLE d n).symm q i : ℝ) : ℂ)) *
        f.1 x) := by
  classical
  let e := section43DiffCoordRealMeasurableEquiv d n
  let φ : SchwartzNPoint d n := section43DiffPullbackCLM d n f
  let H : NPointDomain d n → ℂ := fun δ =>
    Complex.exp
      (-(∑ k : Fin n,
          (δ k 0 : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ)) -
        (2 * Real.pi : ℂ) * Complex.I *
          ∑ p : Fin n × Fin d,
            (δ p.1 (Fin.succ p.2) : ℂ) *
              ((EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ)
                (section43QSpatial (d := d) (n := n) q)) p : ℂ)) *
      φ δ
  have hH_cont : Continuous H := by
    fun_prop
  have hbound : ∀ᵐ δ : NPointDomain d n ∂(volume : Measure (NPointDomain d n)),
      ‖H δ‖ ≤ ‖φ δ‖ := by
    refine Filter.Eventually.of_forall ?_
    intro δ
    by_cases hzero : φ δ = 0
    · simp [H, hzero]
    · have hsupport :
          δ ∈ tsupport ((φ : SchwartzNPoint d n) : NPointDomain d n → ℂ) := by
        exact subset_tsupport _ (Function.mem_support.mpr hzero)
      have hpos :=
        tsupport_section43DiffPullback_subset_positiveOrthant d n f hsupport
      have hδ_nonneg : ∀ k : Fin n, 0 ≤ δ k 0 := fun k => hpos k
      have hexp_le := section43FourierLaplacePhase_norm_exp_le_one_of_nonneg
        d n q δ hq hδ_nonneg
      calc
        ‖H δ‖ =
            ‖Complex.exp
              (-(∑ k : Fin n,
                  (δ k 0 : ℂ) *
                    (section43QTime (d := d) (n := n) q k : ℂ)) -
                (2 * Real.pi : ℂ) * Complex.I *
                  ∑ p : Fin n × Fin d,
                    (δ p.1 (Fin.succ p.2) : ℂ) *
                      ((EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ)
                        (section43QSpatial (d := d) (n := n) q)) p : ℂ)) *
              φ δ‖ := by rfl
        _ = ‖Complex.exp
              (-(∑ k : Fin n,
                  (δ k 0 : ℂ) *
                    (section43QTime (d := d) (n := n) q k : ℂ)) -
                (2 * Real.pi : ℂ) * Complex.I *
                  ∑ p : Fin n × Fin d,
                    (δ p.1 (Fin.succ p.2) : ℂ) *
                      ((EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ)
                        (section43QSpatial (d := d) (n := n) q)) p : ℂ))‖ *
              ‖φ δ‖ := by
            rw [norm_mul]
        _ ≤ 1 * ‖φ δ‖ :=
            mul_le_mul_of_nonneg_right hexp_le (norm_nonneg _)
        _ = ‖φ δ‖ := one_mul _
  have hH_int : Integrable H (volume : Measure (NPointDomain d n)) := by
    exact
      (section43SchwartzNPoint_integrable d n φ).mono
        hH_cont.aestronglyMeasurable hbound
  have hcomp :=
    (section43DiffCoordRealCLE_measurePreserving d n).integrable_comp_of_integrable hH_int
  refine hcomp.congr ?_
  filter_upwards with x
  simp only [Function.comp_apply]
  have hφx : φ ((section43DiffCoordRealMeasurableEquiv d n) x) = f.1 x := by
    simp [φ, section43DiffCoordRealMeasurableEquiv, section43DiffPullbackCLM_apply]
  have hphase := section43WickRotatePhase_after_diffCoord_symm_eq_fourierLaplacePhase
    (d := d) (n := n) q ((section43DiffCoordRealCLE d n) x)
  simp at hphase
  change H ((section43DiffCoordRealMeasurableEquiv d n) x) = _
  simp only [H]
  rw [hφx]
  have hphase' :
      (-(∑ k : Fin n,
          (((section43DiffCoordRealMeasurableEquiv d n) x) k 0 : ℂ) *
            (section43QTime (d := d) (n := n) q k : ℂ)) -
        (2 * Real.pi : ℂ) * Complex.I *
          ∑ p : Fin n × Fin d,
            (((section43DiffCoordRealMeasurableEquiv d n) x) p.1
              (Fin.succ p.2) : ℂ) *
              ((EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ)
                (section43QSpatial (d := d) (n := n) q)) p : ℂ)) =
      Complex.I *
        ∑ i : Fin (n * (d + 1)),
          flattenCLEquiv n (d + 1) (fun k => wickRotatePoint (x k)) i *
            (((section43CumulativeTailMomentumCLE d n).symm q i : ℝ) : ℂ) := by
    simpa [section43DiffCoordRealMeasurableEquiv] using hphase.symm
  rw [hphase']

/-- Evaluation compatibility between the measurable time/spatial split and the
existing Schwartz-space split. -/
private theorem section43NPointTimeSpatialSchwartzCLE_symm_eval
    (d n : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n)
    (p : (Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d)) :
    φ ((section43NPointTimeSpatialMeasurableEquiv d n).symm p) =
      nPointTimeSpatialSchwartzCLE (d := d) (n := n) φ p := by
  have h_eq : (section43NPointTimeSpatialMeasurableEquiv d n).symm p =
      (nPointTimeSpatialCLE (d := d) n).symm p := by
    ext k μ
    refine Fin.cases ?_ ?_ μ
    · simp [nPointTimeSpatialCLE]
    · intro j
      simpa [nPointTimeSpatialCLE, EuclideanSpace.equiv] using
        section43NPointTimeSpatialMeasurableEquiv_symm_apply_spatial d n p (k, j)
  simp [nPointTimeSpatialSchwartzCLE,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, h_eq]

/-- The OS I `(4.20)` Fourier-Laplace integral is exactly the
absolute-coordinate Wick-rotated phase integral after the Section 4.3
cumulative-tail momentum normalization. -/
theorem section43FourierLaplaceIntegral_eq_wickRotatePhaseIntegral_of_mem_positiveEnergy
    (d n : ℕ) [NeZero d]
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (q : NPointDomain d n)
    (hq : q ∈ section43PositiveEnergyRegion d n) :
    section43FourierLaplaceIntegral d n f q =
      ∫ x : NPointDomain d n,
        Complex.exp
          (Complex.I *
            ∑ i : Fin (n * (d + 1)),
              flattenCLEquiv n (d + 1)
                (fun k => wickRotatePoint (x k)) i *
              (((section43CumulativeTailMomentumCLE d n).symm q i : ℝ) : ℂ)) *
        f.1 x := by
  classical
  let G : NPointDomain d n → ℂ := fun x =>
    Complex.exp
      (Complex.I *
        ∑ i : Fin (n * (d + 1)),
          flattenCLEquiv n (d + 1)
            (fun k => wickRotatePoint (x k)) i *
          (((section43CumulativeTailMomentumCLE d n).symm q i : ℝ) : ℂ)) *
    f.1 x
  let φ : SchwartzNPoint d n := section43DiffPullbackCLM d n f
  let K : NPointDomain d n → ℂ := fun δ =>
    Complex.exp
      (-(∑ k : Fin n,
          (δ k 0 : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ)) -
        (2 * Real.pi : ℂ) * Complex.I *
          ∑ p : Fin n × Fin d,
            (δ p.1 (Fin.succ p.2) : ℂ) *
              ((EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ)
                (section43QSpatial (d := d) (n := n) q)) p : ℂ)) *
      φ δ
  have hG_int : Integrable G (volume : Measure (NPointDomain d n)) := by
    simpa [G] using
      integrable_section43WickRotatePhaseIntegral_of_mem_positiveEnergy
        (d := d) (n := n) f q hq
  have hK_int : Integrable K (volume : Measure (NPointDomain d n)) := by
    have hcomp :=
      (section43DiffCoordRealCLE_symm_measurePreserving d n).integrable_comp_of_integrable
        hG_int
    refine hcomp.congr ?_
    filter_upwards with δ
    simp only [Function.comp_apply]
    have hφδ : f.1 ((section43DiffCoordRealMeasurableEquiv d n).symm δ) =
        φ δ := by
      simp [φ, section43DiffCoordRealMeasurableEquiv, section43DiffPullbackCLM_apply]
    have hphase := section43WickRotatePhase_after_diffCoord_symm_eq_fourierLaplacePhase
      (d := d) (n := n) q δ
    have hphase' :
        Complex.I *
            ∑ i : Fin (n * (d + 1)),
              flattenCLEquiv n (d + 1)
                (fun k => wickRotatePoint
                  (((section43DiffCoordRealMeasurableEquiv d n).symm δ) k)) i *
              (((section43CumulativeTailMomentumCLE d n).symm q i : ℝ) : ℂ)
          =
        -(∑ k : Fin n,
            (δ k 0 : ℂ) *
              (section43QTime (d := d) (n := n) q k : ℂ)) -
          (2 * Real.pi : ℂ) * Complex.I *
            ∑ p : Fin n × Fin d,
              (δ p.1 (Fin.succ p.2) : ℂ) *
                ((EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ)
                  (section43QSpatial (d := d) (n := n) q)) p : ℂ) := by
      simpa [section43DiffCoordRealMeasurableEquiv] using hphase
    change G ((section43DiffCoordRealMeasurableEquiv d n).symm δ) = K δ
    simp only [G, K]
    rw [hφδ]
    rw [hphase']
  let eTS := section43NPointTimeSpatialMeasurableEquiv d n
  have hK_split_int :
      Integrable (fun p : (Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d) =>
        K (eTS.symm p)) := by
    exact
      (section43NPointTimeSpatialCLE_measurePreserving d n).symm.integrable_comp_of_integrable
        hK_int
  have h_abs_to_diff :
      (∫ x : NPointDomain d n, G x) = ∫ δ : NPointDomain d n, K δ := by
    calc
      (∫ x : NPointDomain d n, G x) =
          ∫ δ : NPointDomain d n,
            G ((section43DiffCoordRealMeasurableEquiv d n).symm δ) := by
            exact
              ((section43DiffCoordRealCLE_symm_measurePreserving d n).integral_comp'
                (g := G)).symm
      _ = ∫ δ : NPointDomain d n, K δ := by
            apply integral_congr_ae
            filter_upwards with δ
            have hφδ : f.1 ((section43DiffCoordRealMeasurableEquiv d n).symm δ) =
                φ δ := by
              simp [φ, section43DiffCoordRealMeasurableEquiv,
                section43DiffPullbackCLM_apply]
            have hphase :=
              section43WickRotatePhase_after_diffCoord_symm_eq_fourierLaplacePhase
                (d := d) (n := n) q δ
            have hphase' :
                Complex.I *
                    ∑ i : Fin (n * (d + 1)),
                      flattenCLEquiv n (d + 1)
                        (fun k => wickRotatePoint
                          (((section43DiffCoordRealMeasurableEquiv d n).symm δ) k)) i *
                      (((section43CumulativeTailMomentumCLE d n).symm q i : ℝ) : ℂ)
                  =
                -(∑ k : Fin n,
                    (δ k 0 : ℂ) *
                      (section43QTime (d := d) (n := n) q k : ℂ)) -
                  (2 * Real.pi : ℂ) * Complex.I *
                    ∑ p : Fin n × Fin d,
                      (δ p.1 (Fin.succ p.2) : ℂ) *
                        ((EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ)
                          (section43QSpatial (d := d) (n := n) q)) p : ℂ) := by
              simpa [section43DiffCoordRealMeasurableEquiv] using hphase
            change G ((section43DiffCoordRealMeasurableEquiv d n).symm δ) = K δ
            simp only [G, K]
            rw [hφδ]
            rw [hphase']
  have h_diff_to_split :
      (∫ δ : NPointDomain d n, K δ) =
        ∫ p : (Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d),
          K (eTS.symm p) := by
    exact
      ((section43NPointTimeSpatialCLE_measurePreserving d n).symm.integral_comp'
        (g := K)).symm
  have h_prod :
      (∫ p : (Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d),
          K (eTS.symm p)) =
      ∫ τ : Fin n → ℝ, ∫ η : EuclideanSpace ℝ (Fin n × Fin d),
        K (eTS.symm (τ, η)) := by
    exact integral_prod
      (fun p : (Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d) =>
        K (eTS.symm p)) hK_split_int
  have h_inner :
      (∫ τ : Fin n → ℝ, ∫ η : EuclideanSpace ℝ (Fin n × Fin d),
          K (eTS.symm (τ, η))) =
      ∫ τ : Fin n → ℝ,
        Complex.exp
            (-(∑ k : Fin n,
              (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ))) *
          (∫ η : EuclideanSpace ℝ (Fin n × Fin d),
            𝐞 (-(inner ℝ η (section43QSpatial (d := d) (n := n) q))) •
              nPointTimeSpatialSchwartzCLE (d := d) (n := n) φ (τ, η)) := by
    apply integral_congr_ae
    filter_upwards with τ
    let c : ℂ := Complex.exp
      (-(∑ k : Fin n,
        (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ)))
    let L : EuclideanSpace ℝ (Fin n × Fin d) → ℂ := fun η =>
      𝐞 (-(inner ℝ η (section43QSpatial (d := d) (n := n) q))) •
        nPointTimeSpatialSchwartzCLE (d := d) (n := n) φ (τ, η)
    trans ∫ η : EuclideanSpace ℝ (Fin n × Fin d), c * L η
    · apply integral_congr_ae
      filter_upwards with η
      have hsplitφ := section43NPointTimeSpatialSchwartzCLE_symm_eval d n φ (τ, η)
      change K ((section43NPointTimeSpatialMeasurableEquiv d n).symm (τ, η)) =
        c * L η
      simp only [K, c, L]
      rw [hsplitφ]
      simp only [section43NPointTimeSpatialMeasurableEquiv_symm_apply_time,
        section43NPointTimeSpatialMeasurableEquiv_symm_apply_spatial]
      rw [sub_eq_add_neg, Complex.exp_add]
      have hchar :
          Complex.exp
            (-(2 * ↑Real.pi * Complex.I *
              ∑ p : Fin n × Fin d,
                ((EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ) η) p : ℂ) *
                  ((EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ)
                    (section43QSpatial (d := d) (n := n) q)) p : ℂ))) =
          ((𝐞 (-(inner ℝ η (section43QSpatial (d := d) (n := n) q))) :
              Circle) : ℂ) := by
        convert section43SpatialFourierPhase_eq_fourierChar
          (d := d) (n := n) η (section43QSpatial (d := d) (n := n) q) using 2
        ring
      rw [hchar]
      simp [Circle.smul_def]
      ring
    · simpa [c, L] using
        (MeasureTheory.integral_const_mul
          (μ := (volume : Measure (EuclideanSpace ℝ (Fin n × Fin d)))) c L)
  calc
    section43FourierLaplaceIntegral d n f q =
        ∫ τ : Fin n → ℝ,
          Complex.exp
              (-(∑ k : Fin n,
                (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ))) *
            (∫ η : EuclideanSpace ℝ (Fin n × Fin d),
              𝐞 (-(inner ℝ η (section43QSpatial (d := d) (n := n) q))) •
                nPointTimeSpatialSchwartzCLE (d := d) (n := n) φ (τ, η)) := by
          simpa [φ] using
            section43FourierLaplaceIntegral_eq_time_spatial_integral d n f q
    _ = ∫ τ : Fin n → ℝ, ∫ η : EuclideanSpace ℝ (Fin n × Fin d),
          K (eTS.symm (τ, η)) := h_inner.symm
    _ = ∫ p : (Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d),
          K (eTS.symm p) := h_prod.symm
    _ = ∫ δ : NPointDomain d n, K δ := h_diff_to_split.symm
    _ = ∫ x : NPointDomain d n, G x := h_abs_to_diff.symm
    _ = ∫ x : NPointDomain d n,
        Complex.exp
          (Complex.I *
            ∑ i : Fin (n * (d + 1)),
              flattenCLEquiv n (d + 1)
                (fun k => wickRotatePoint (x k)) i *
              (((section43CumulativeTailMomentumCLE d n).symm q i : ℝ) : ℂ)) *
        f.1 x := by rfl

end OSReconstruction
