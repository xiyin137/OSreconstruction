/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43Codomain
import OSReconstruction.SCV.PartialFourierSpatial
import OSReconstruction.SCV.FourierSupportCone
import OSReconstruction.SCV.PaleyWienerSchwartz
import OSReconstruction.ComplexLieGroups.DifferenceCoordinatesReduced
import OSReconstruction.Wightman.Reconstruction.ForwardTubeDistributions
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Fin.Rev

noncomputable section

open scoped Topology FourierTransform LineDeriv
open Set MeasureTheory

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- The real difference-coordinate map used in OS I `(4.19)`.

This is only a local name for the existing BHW real difference-coordinate
equivalence, specialized to the `NPointDomain` abbreviation. -/
noncomputable abbrev section43DiffCoordRealCLE (d n : ℕ) :
    NPointDomain d n ≃L[ℝ] NPointDomain d n :=
  BHW.realDiffCoordCLE n d

@[simp] theorem section43DiffCoordRealCLE_apply (d n : ℕ)
    (x : NPointDomain d n) (k : Fin n) (μ : Fin (d + 1)) :
    section43DiffCoordRealCLE d n x k μ =
      if _hk : k.val = 0 then x k μ
      else x k μ - x ⟨k.val - 1, by omega⟩ μ := by
  simp [section43DiffCoordRealCLE]

@[simp] theorem section43DiffCoordRealCLE_symm_apply (d n : ℕ)
    (ξ : NPointDomain d n) (k : Fin n) (μ : Fin (d + 1)) :
    (section43DiffCoordRealCLE d n).symm ξ k μ =
      ∑ j : Fin (k.val + 1), ξ ⟨j.val, by omega⟩ μ := by
  simp [section43DiffCoordRealCLE]

/-- Pull a positive-time Euclidean test function back to difference coordinates.

This is the `f ↦ f⁺` step in OS I `(4.19)`. -/
noncomputable def section43DiffPullbackCLM (d n : ℕ) [NeZero d] :
    euclideanPositiveTimeSubmodule (d := d) n →L[ℂ] SchwartzNPoint d n :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (section43DiffCoordRealCLE d n).symm).comp
    (euclideanPositiveTimeSubmodule (d := d) n).subtypeL

@[simp] theorem section43DiffPullbackCLM_apply (d n : ℕ) [NeZero d]
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (ξ : NPointDomain d n) :
    section43DiffPullbackCLM d n f ξ =
      f.1 ((section43DiffCoordRealCLE d n).symm ξ) := by
  simp [section43DiffPullbackCLM, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

/-- Ordered positive-time support becomes nonnegative support in difference
time coordinates. -/
theorem tsupport_section43DiffPullback_subset_positiveOrthant (d n : ℕ) [NeZero d]
    (f : euclideanPositiveTimeSubmodule (d := d) n) :
    tsupport
      ((section43DiffPullbackCLM d n f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ)
      ⊆ section43PositiveEnergyRegion d n := by
  intro ξ hξ k
  let y : NPointDomain d n := (section43DiffCoordRealCLE d n).symm ξ
  have hpre : y ∈ tsupport ((f.1 : SchwartzNPoint d n) : NPointDomain d n → ℂ) := by
    exact tsupport_comp_subset_preimage (f.1 : NPointDomain d n → ℂ)
      (section43DiffCoordRealCLE d n).symm.continuous hξ
  have hord : y ∈ OrderedPositiveTimeRegion d n := f.2 hpre
  have hcoord :
      ξ k 0 =
        (if hk : k.val = 0 then y k 0 else y k 0 - y ⟨k.val - 1, by omega⟩ 0) := by
    have happly :=
      congr_fun (congr_fun ((section43DiffCoordRealCLE d n).apply_symm_apply ξ) k) 0
    rw [section43DiffCoordRealCLE_apply] at happly
    exact happly.symm
  rw [hcoord]
  by_cases hk : k.val = 0
  · simp [hk, (hord k).1.le]
  · simp [hk]
    have hprev_lt : (⟨k.val - 1, by omega⟩ : Fin n) < k := by
      exact Fin.mk_lt_mk.mpr (by omega)
    exact (((hord ⟨k.val - 1, by omega⟩).2 k hprev_lt).le)

private theorem section43_inOpenForwardCone_timeAxis (d : ℕ) [NeZero d]
    {a : ℝ} (ha : 0 < a) :
    InOpenForwardCone d
      (fun μ : Fin (d + 1) => if μ = (0 : Fin (d + 1)) then a else 0) := by
  refine ⟨by simp [ha], ?_⟩
  rw [MinkowskiSpace.minkowskiNormSq_decomp]
  simp only [MinkowskiSpace.spatialNormSq, ↓reduceIte, Fin.succ_ne_zero]
  simp
  nlinarith [sq_pos_of_pos ha]

private theorem section43DiffCoordRealCLE_symm_mem_forwardConeAbs
    (d n : ℕ) [NeZero d]
    {δ : NPointDomain d n}
    (hδ : ∀ k : Fin n, InOpenForwardCone d (δ k)) :
    (section43DiffCoordRealCLE d n).symm δ ∈ ForwardConeAbs d n := by
  intro k
  let y : NPointDomain d n := (section43DiffCoordRealCLE d n).symm δ
  have hcoord :
      (fun μ : Fin (d + 1) =>
          y k μ -
            (let prev : Fin (d + 1) → ℝ :=
              if h : k.val = 0 then 0 else y ⟨k.val - 1, by omega⟩
            prev μ)) =
        δ k := by
    ext μ
    have happly :=
      congr_fun (congr_fun ((section43DiffCoordRealCLE d n).apply_symm_apply δ) k) μ
    rw [section43DiffCoordRealCLE_apply] at happly
    by_cases hk : k.val = 0
    · simp [hk] at happly ⊢
      exact happly
    · simp [hk] at happly ⊢
      exact happly
  change InOpenForwardCone d
    (fun μ : Fin (d + 1) =>
      y k μ -
        (let prev : Fin (d + 1) → ℝ :=
          if h : k.val = 0 then 0 else y ⟨k.val - 1, by omega⟩
        prev μ))
  rw [hcoord]
  exact hδ k

private def section43TimeAxisDifference (d n : ℕ) [NeZero d]
    (j : Fin n) (R : ℝ) : NPointDomain d n :=
  fun k μ => if μ = 0 then if k = j then R else 1 else 0

private theorem section43TimeAxisDifference_mem_forwardConeAbs
    (d n : ℕ) [NeZero d]
    (j : Fin n) {R : ℝ} (hR : 0 < R) :
    (section43DiffCoordRealCLE d n).symm
        (section43TimeAxisDifference d n j R) ∈ ForwardConeAbs d n := by
  apply section43DiffCoordRealCLE_symm_mem_forwardConeAbs
  intro k
  apply section43_inOpenForwardCone_timeAxis
  by_cases hk : k = j
  · simp [hk, hR]
  · simp [hk]

/-- Time coordinates after the standard time/spatial splitting. -/
def section43QTime (d n : ℕ) [NeZero d] (q : NPointDomain d n) : Fin n → ℝ :=
  (nPointTimeSpatialCLE (d := d) n q).1

/-- Spatial coordinates after the standard time/spatial splitting. -/
def section43QSpatial (d n : ℕ) [NeZero d] (q : NPointDomain d n) :
    EuclideanSpace ℝ (Fin n × Fin d) :=
  (nPointTimeSpatialCLE (d := d) n q).2

@[simp] theorem section43QSpatial_apply (d n : ℕ) [NeZero d]
    (q : NPointDomain d n) (p : Fin n × Fin d) :
    (EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ)
      (section43QSpatial (d := d) (n := n) q)) p =
      q p.1 (Fin.succ p.2) := by
  simp [section43QSpatial, nPointTimeSpatialCLE]

/-- Reverse the order of the point block.  This turns the existing prefix-sum
difference-coordinate inverse into a tail-sum map. -/
noncomputable def section43PointReverseCLE (d n : ℕ) [NeZero d] :
    NPointDomain d n ≃L[ℝ] NPointDomain d n :=
  (LinearEquiv.funCongrLeft ℝ (Fin (d + 1) → ℝ) Fin.revPerm).toContinuousLinearEquiv

@[simp] theorem section43PointReverseCLE_symm_apply (d n : ℕ) [NeZero d]
    (x : NPointDomain d n) (k : Fin n) :
    (section43PointReverseCLE d n).symm x k = x (Fin.rev k) := by
  rfl

private theorem section43_fin_rev_prefix_sum_eq_tail_sum
    {n : ℕ} {A : Type*} [AddCommMonoid A]
    (f : Fin n → A) (j : Fin n) :
    (∑ l : Fin ((Fin.rev j).val + 1),
        f (Fin.rev ⟨l.val, by omega⟩)) =
      ∑ k : Fin n, if j ≤ k then f k else 0 := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij
    (fun l (_hl : l ∈ (Finset.univ : Finset (Fin ((Fin.rev j).val + 1)))) =>
      Fin.rev (⟨l.val, by omega⟩ : Fin n)) ?hmem ?hinj ?hsurj ?hval
  · intro l _hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply Fin.le_rev_iff.mpr
    exact Fin.mk_le_mk.mpr (Nat.lt_succ_iff.mp l.isLt)
  · intro a _ha b _hb h
    have h' := congrArg Fin.rev h
    simp only [Fin.rev_rev] at h'
    apply Fin.ext
    simpa using congrArg Fin.val h'
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    let a : Fin ((Fin.rev j).val + 1) :=
      ⟨(Fin.rev b).val, Nat.lt_succ_of_le (Fin.mk_le_mk.mp (Fin.rev_le_rev.mpr hb))⟩
    refine ⟨a, Finset.mem_univ _, ?_⟩
    change (⟨a.val, by omega⟩ : Fin n).rev = b
    have hcast : (⟨a.val, by omega⟩ : Fin n) = Fin.rev b := by
      apply Fin.ext
      rfl
    rw [hcast]
    exact Fin.rev_rev b
  · intro _l _hl
    rfl

private theorem section43_fin_prefix_sum_eq_lower_sum
    {n : ℕ} {A : Type*} [AddCommMonoid A]
    (f : Fin n → A) (k : Fin n) :
    (∑ l : Fin (k.val + 1), f ⟨l.val, by omega⟩) =
      ∑ j : Fin n, if j.val ≤ k.val then f j else 0 := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij
    (fun l (_hl : l ∈ (Finset.univ : Finset (Fin (k.val + 1)))) =>
      (⟨l.val, by omega⟩ : Fin n)) ?hmem ?hinj ?hsurj ?hval
  · intro l _hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Nat.lt_succ_iff.mp l.isLt
  · intro a _ha b _hb h
    have hval := congrArg Fin.val h
    apply Fin.ext
    exact hval
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    let a : Fin (k.val + 1) := ⟨b.val, Nat.lt_succ_iff.mpr hb⟩
    refine ⟨a, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    rfl
  · intro _l _hl
    rfl

private theorem section43_fin_prefix_mul_eq_sum_tail
    {n : ℕ} (a b : Fin n → ℝ) :
    (∑ k : Fin n, (∑ l : Fin (k.val + 1), a ⟨l.val, by omega⟩) * b k) =
      ∑ j : Fin n, a j * ∑ k : Fin n, if j.val ≤ k.val then b k else 0 := by
  classical
  calc
    (∑ k : Fin n, (∑ l : Fin (k.val + 1), a ⟨l.val, by omega⟩) * b k)
        = ∑ k : Fin n, (∑ j : Fin n, if j.val ≤ k.val then a j else 0) * b k := by
          simp only [section43_fin_prefix_sum_eq_lower_sum]
    _ = ∑ k : Fin n, ∑ j : Fin n, (if j.val ≤ k.val then a j else 0) * b k := by
          simp [Finset.sum_mul]
    _ = ∑ j : Fin n, ∑ k : Fin n, (if j.val ≤ k.val then a j else 0) * b k := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin n, a j * ∑ k : Fin n, if j.val ≤ k.val then b k else 0 := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro k _hk
          by_cases h : j.val ≤ k.val
          · simp [h]
          · simp [h]

/-- Unscaled cumulative tail momenta.  In coordinates this is
`q_j = ∑_{k ≥ j} ξ_k`, before the spatial Fourier normalization is applied. -/
noncomputable def section43RawCumulativeTailMomentumCLE (d n : ℕ) [NeZero d] :
    (Fin (n * (d + 1)) → ℝ) ≃L[ℝ] NPointDomain d n :=
  (((_root_.flattenCLEquivReal n (d + 1)).symm).trans
    (section43PointReverseCLE d n)).trans
    (((section43DiffCoordRealCLE d n).symm).trans
      (section43PointReverseCLE d n))

@[simp] theorem section43RawCumulativeTailMomentumCLE_apply
    (d n : ℕ) [NeZero d]
    (ξ : Fin (n * (d + 1)) → ℝ) (j : Fin n) (μ : Fin (d + 1)) :
    section43RawCumulativeTailMomentumCLE d n ξ j μ =
      ∑ k : Fin n,
        if j.val ≤ k.val then ξ (finProdFinEquiv (k, μ)) else 0 := by
  change (∑ l : Fin ((Fin.rev j).val + 1),
      ξ (finProdFinEquiv (Fin.rev ⟨l.val, by omega⟩, μ))) =
    ∑ k : Fin n, if j.val ≤ k.val then ξ (finProdFinEquiv (k, μ)) else 0
  simpa only [Fin.le_iff_val_le_val] using
    section43_fin_rev_prefix_sum_eq_tail_sum
      (fun k : Fin n => ξ (finProdFinEquiv (k, μ))) j

@[simp] theorem section43RawCumulativeTailMomentumCLE_symm_apply
    (d n : ℕ) [NeZero d]
    (q : NPointDomain d n) (k : Fin n) (μ : Fin (d + 1)) :
    (section43RawCumulativeTailMomentumCLE d n).symm q
        (finProdFinEquiv (k, μ)) =
      q k μ - if h : k.val + 1 < n then q ⟨k.val + 1, h⟩ μ else 0 := by
  rw [section43RawCumulativeTailMomentumCLE]
  simp only [ContinuousLinearEquiv.symm_trans_apply, ContinuousLinearEquiv.symm_symm,
    _root_.flattenCLEquivReal_apply, Equiv.symm_apply_apply]
  rw [section43PointReverseCLE_symm_apply]
  rw [section43DiffCoordRealCLE_apply]
  by_cases hlast : (Fin.rev k).val = 0
  · have hnot : ¬ k.val + 1 < n := by
      have hlast' : n - (k.val + 1) = 0 := by
        simpa [Fin.val_rev] using hlast
      omega
    have hlast' : n - (k.val + 1) = 0 := by
      simpa [Fin.val_rev] using hlast
    simp [section43PointReverseCLE_symm_apply, hlast', hnot]
  · have hsucc : k.val + 1 < n := by
      have hlast' : ¬ n - (k.val + 1) = 0 := by
        simpa [Fin.val_rev] using hlast
      omega
    have hlast' : ¬ n - (k.val + 1) = 0 := by
      simpa [Fin.val_rev] using hlast
    have hprev_rev :
        ∀ hprev : n - (k.val + 1) - 1 < n,
          Fin.rev (⟨n - (k.val + 1) - 1, hprev⟩ : Fin n) =
            ⟨k.val + 1, hsucc⟩ := by
      intro hprev
      apply Fin.ext
      rw [Fin.val_rev]
      simp only
      omega
    simp [section43PointReverseCLE_symm_apply, hlast', hsucc, hprev_rev]

/-- Diagonal scaling that converts Mathlib's spatial Fourier variables to the
Section 4.3 convention.  Time coordinates are unchanged; spatial coordinates
are multiplied by `-(1 / (2 * π))`. -/
noncomputable def section43SpatialFourierScaleLinearEquiv (d n : ℕ) [NeZero d] :
    NPointDomain d n ≃ₗ[ℝ] NPointDomain d n where
  toFun := fun q j μ =>
    if μ = 0 then q j μ else -(1 / (2 * Real.pi)) * q j μ
  invFun := fun q j μ =>
    if μ = 0 then q j μ else -(2 * Real.pi) * q j μ
  map_add' := by
    intro q r
    ext j μ
    by_cases hμ : μ = 0
    · simp [hμ]
    · simp [hμ]
      ring
  map_smul' := by
    intro a q
    ext j μ
    by_cases hμ : μ = 0
    · simp [hμ]
    · simp [hμ]
      ring
  left_inv := by
    intro q
    ext j μ
    by_cases hμ : μ = 0
    · simp [hμ]
    · simp [hμ]
      field_simp [Real.pi_ne_zero]
  right_inv := by
    intro q
    ext j μ
    by_cases hμ : μ = 0
    · simp [hμ]
    · simp [hμ]
      field_simp [Real.pi_ne_zero]

noncomputable def section43SpatialFourierScaleCLE (d n : ℕ) [NeZero d] :
    NPointDomain d n ≃L[ℝ] NPointDomain d n :=
  (section43SpatialFourierScaleLinearEquiv d n).toContinuousLinearEquiv

@[simp] theorem section43SpatialFourierScaleCLE_apply (d n : ℕ) [NeZero d]
    (q : NPointDomain d n) (j : Fin n) (μ : Fin (d + 1)) :
    section43SpatialFourierScaleCLE d n q j μ =
      if μ = 0 then q j μ else -(1 / (2 * Real.pi)) * q j μ := by
  rfl

@[simp] theorem section43SpatialFourierScaleCLE_symm_apply (d n : ℕ) [NeZero d]
    (q : NPointDomain d n) (j : Fin n) (μ : Fin (d + 1)) :
    (section43SpatialFourierScaleCLE d n).symm q j μ =
      if μ = 0 then q j μ else -(2 * Real.pi) * q j μ := by
  rfl

/-- Corrected cumulative tail momenta for Section 4.3.  Time components are
ordinary cumulative energies; spatial components include the
`-(1 / (2 * π))` Fourier-normalization factor. -/
noncomputable def section43CumulativeTailMomentumCLE (d n : ℕ) [NeZero d] :
    (Fin (n * (d + 1)) → ℝ) ≃L[ℝ] NPointDomain d n :=
  (section43RawCumulativeTailMomentumCLE d n).trans
    (section43SpatialFourierScaleCLE d n)

@[simp] theorem section43CumulativeTailMomentumCLE_apply
    (d n : ℕ) [NeZero d]
    (ξ : Fin (n * (d + 1)) → ℝ) (j : Fin n) (μ : Fin (d + 1)) :
    section43CumulativeTailMomentumCLE d n ξ j μ =
      if μ = 0 then
        ∑ k : Fin n,
          if j.val ≤ k.val then ξ (finProdFinEquiv (k, μ)) else 0
      else
        -(1 / (2 * Real.pi)) *
          ∑ k : Fin n,
            if j.val ≤ k.val then ξ (finProdFinEquiv (k, μ)) else 0 := by
  rw [section43CumulativeTailMomentumCLE]
  simp only [ContinuousLinearEquiv.trans_apply, section43SpatialFourierScaleCLE_apply,
    section43RawCumulativeTailMomentumCLE_apply]

@[simp] theorem section43CumulativeTailMomentumCLE_symm_apply
    (d n : ℕ) [NeZero d]
    (q : NPointDomain d n) (k : Fin n) (μ : Fin (d + 1)) :
    (section43CumulativeTailMomentumCLE d n).symm q
        (finProdFinEquiv (k, μ)) =
      if μ = 0 then
        q k μ - if h : k.val + 1 < n then q ⟨k.val + 1, h⟩ μ else 0
      else
        -(2 * Real.pi) *
          (q k μ - if h : k.val + 1 < n then q ⟨k.val + 1, h⟩ μ else 0) := by
  rw [section43CumulativeTailMomentumCLE]
  change (section43RawCumulativeTailMomentumCLE d n).symm
      ((section43SpatialFourierScaleCLE d n).symm q)
        (finProdFinEquiv (k, μ)) =
      if μ = 0 then
        q k μ - if h : k.val + 1 < n then q ⟨k.val + 1, h⟩ μ else 0
      else
        -(2 * Real.pi) *
          (q k μ - if h : k.val + 1 < n then q ⟨k.val + 1, h⟩ μ else 0)
  rw [section43RawCumulativeTailMomentumCLE_symm_apply]
  simp only [section43SpatialFourierScaleCLE_symm_apply]
  by_cases hμ : μ = 0
  · simp [hμ]
  · by_cases hsucc : k.val + 1 < n
    · simp [hμ, hsucc]
      ring
    · simp [hμ, hsucc]

private theorem section43TimeAxisDifference_pairing_eq_sum_tail
    (d n : ℕ) [NeZero d]
    (ξ : Fin (n * (d + 1)) → ℝ) (j : Fin n) (R : ℝ) :
    (∑ i : Fin (n * (d + 1)),
        flattenCLEquivReal n (d + 1)
          ((section43DiffCoordRealCLE d n).symm
            (section43TimeAxisDifference d n j R)) i * ξ i) =
      R * section43CumulativeTailMomentumCLE d n ξ j 0 +
        ∑ k : Fin n,
          if k = j then 0 else section43CumulativeTailMomentumCLE d n ξ k 0 := by
  classical
  let δ : NPointDomain d n := section43TimeAxisDifference d n j R
  let qξ : NPointDomain d n := section43CumulativeTailMomentumCLE d n ξ
  let ξtime : Fin n → ℝ := fun k => ξ (finProdFinEquiv (k, (0 : Fin (d + 1))))
  have hspatial_zero :
      ∀ (k : Fin n) (μ : Fin (d + 1)), μ ≠ 0 →
        (section43DiffCoordRealCLE d n).symm δ k μ = 0 := by
    intro k μ hμ
    rw [section43DiffCoordRealCLE_symm_apply]
    simp [δ, section43TimeAxisDifference, hμ]
  calc
    (∑ i : Fin (n * (d + 1)),
        flattenCLEquivReal n (d + 1)
          ((section43DiffCoordRealCLE d n).symm
            (section43TimeAxisDifference d n j R)) i * ξ i)
        = ∑ k : Fin n, ∑ μ : Fin (d + 1),
            (section43DiffCoordRealCLE d n).symm δ k μ *
              ξ (finProdFinEquiv (k, μ)) := by
          calc
            (∑ i : Fin (n * (d + 1)),
                flattenCLEquivReal n (d + 1)
                  ((section43DiffCoordRealCLE d n).symm
                    (section43TimeAxisDifference d n j R)) i * ξ i)
                = ∑ p : Fin n × Fin (d + 1),
                    flattenCLEquivReal n (d + 1)
                      ((section43DiffCoordRealCLE d n).symm δ)
                        (finProdFinEquiv p) *
                      ξ (finProdFinEquiv p) := by
                  simpa [δ] using
                    (finProdFinEquiv.sum_comp
                      (fun i : Fin (n * (d + 1)) =>
                        flattenCLEquivReal n (d + 1)
                          ((section43DiffCoordRealCLE d n).symm δ) i * ξ i)).symm
            _ = ∑ k : Fin n, ∑ μ : Fin (d + 1),
                    (section43DiffCoordRealCLE d n).symm δ k μ *
                      ξ (finProdFinEquiv (k, μ)) := by
                  simpa [flattenCLEquivReal_apply] using
                    (Finset.sum_product (s := (Finset.univ : Finset (Fin n)))
                      (t := (Finset.univ : Finset (Fin (d + 1))))
                      (f := fun p : Fin n × Fin (d + 1) =>
                        (section43DiffCoordRealCLE d n).symm δ p.1 p.2 *
                          ξ (finProdFinEquiv p)))
    _ = ∑ k : Fin n,
            (section43DiffCoordRealCLE d n).symm δ k 0 * ξtime k := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          rw [Finset.sum_eq_single (0 : Fin (d + 1))]
          · intro μ _hμ hμ
            simp [hspatial_zero k μ hμ]
          · intro hmem
            exact False.elim (hmem (Finset.mem_univ _))
    _ = ∑ k : Fin n,
            (∑ l : Fin (k.val + 1), δ ⟨l.val, by omega⟩ 0) * ξtime k := by
          simp only [section43DiffCoordRealCLE_symm_apply]
    _ = ∑ k : Fin n,
            δ k 0 * ∑ l : Fin n, if k.val ≤ l.val then ξtime l else 0 := by
          exact section43_fin_prefix_mul_eq_sum_tail (fun k => δ k 0) ξtime
    _ = ∑ k : Fin n, δ k 0 * qξ k 0 := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          simp [qξ, ξtime, section43CumulativeTailMomentumCLE_apply]
    _ = ∑ k : Fin n, (if k = j then R else 1) * qξ k 0 := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          simp [δ, section43TimeAxisDifference]
    _ = R * qξ j 0 + ∑ k : Fin n, if k = j then 0 else qξ k 0 := by
          have hsingle :
              (∑ k : Fin n, if k = j then R * qξ j 0 else 0) = R * qξ j 0 := by
            rw [Finset.sum_eq_single j]
            · simp
            · intro k _hk hkj
              simp [hkj]
            · intro hj
              exact False.elim (hj (Finset.mem_univ _))
          calc
            (∑ k : Fin n, (if k = j then R else 1) * qξ k 0)
                = ∑ k : Fin n,
                    ((if k = j then R * qξ j 0 else 0) +
                      if k = j then 0 else qξ k 0) := by
                  refine Finset.sum_congr rfl ?_
                  intro k _hk
                  by_cases hk : k = j
                  · simp [hk]
                  · simp [hk]
            _ = (∑ k : Fin n, if k = j then R * qξ j 0 else 0) +
                  ∑ k : Fin n, if k = j then 0 else qξ k 0 := by
                  rw [Finset.sum_add_distrib]
            _ = R * qξ j 0 + ∑ k : Fin n, if k = j then 0 else qξ k 0 := by
                  rw [hsingle]

theorem section43CumulativeTailMomentumCLE_mem_positiveEnergy_of_mem_dualCone
    (d n : ℕ) [NeZero d]
    {ξ : Fin (n * (d + 1)) → ℝ}
    (hξ : ξ ∈
      DualConeFlat ((flattenCLEquivReal n (d + 1)) '' ForwardConeAbs d n)) :
    section43CumulativeTailMomentumCLE d n ξ ∈
      section43PositiveEnergyRegion d n := by
  rw [section43PositiveEnergyRegion]
  intro j
  let qξ : NPointDomain d n := section43CumulativeTailMomentumCLE d n ξ
  let qj : ℝ := qξ j 0
  by_contra hnon
  have hqneg : qj < 0 := by
    exact lt_of_not_ge hnon
  let C : ℝ := ∑ k : Fin n, if k = j then 0 else qξ k 0
  let R : ℝ := max 1 ((C + 1) / (-qj) + 1)
  have hR_pos : 0 < R := by
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let yR : NPointDomain d n :=
    (section43DiffCoordRealCLE d n).symm
      (section43TimeAxisDifference d n j R)
  have hyR_abs : yR ∈ ForwardConeAbs d n := by
    exact section43TimeAxisDifference_mem_forwardConeAbs d n j hR_pos
  have hyR_flat :
      flattenCLEquivReal n (d + 1) yR ∈
        (flattenCLEquivReal n (d + 1)) '' ForwardConeAbs d n := by
    exact ⟨yR, hyR_abs, rfl⟩
  have hnonneg :
      0 ≤ ∑ i : Fin (n * (d + 1)),
        flattenCLEquivReal n (d + 1)
          ((section43DiffCoordRealCLE d n).symm
            (section43TimeAxisDifference d n j R)) i * ξ i := by
    simpa [yR] using hξ (flattenCLEquivReal n (d + 1) yR) hyR_flat
  rw [section43TimeAxisDifference_pairing_eq_sum_tail] at hnonneg
  have hnonneg_tail : 0 ≤ R * qj + C := by
    simpa [qξ, qj, C] using hnonneg
  have hpos_neg_qj : 0 < -qj := by
    linarith
  have hR_gt : (C + 1) / (-qj) < R := by
    exact lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
  have hmul0 := mul_lt_mul_of_pos_right hR_gt hpos_neg_qj
  have hdiv_cancel : (C + 1) / (-qj) * (-qj) = C + 1 := by
    have hqj_ne : qj ≠ 0 := by
      linarith
    field_simp [hqj_ne]
  have hmul : C + 1 < R * (-qj) := by
    simpa [hdiv_cancel] using hmul0
  have hneg_tail : R * qj + C < 0 := by
    nlinarith
  exact (not_le_of_gt hneg_tail) hnonneg_tail

noncomputable def section43FrequencyRepresentative (d n : ℕ) [NeZero d] :
    SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (section43CumulativeTailMomentumCLE d n).symm).comp
    ((physicsFourierFlatCLM : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ →L[ℂ]
        SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ).comp
      (flattenSchwartzNPoint (d := d)))

noncomputable def section43FrequencyProjection (d n : ℕ) [NeZero d] :
    SchwartzNPoint d n →L[ℂ] Section43PositiveEnergyComponent (d := d) n :=
  (section43PositiveEnergyQuotientMap (d := d) n).comp
    (section43FrequencyRepresentative d n)

theorem section43_physicsFourierFlatCLM_translateSchwartz_apply
    {m : ℕ}
    (a : Fin m → ℝ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (ξ : Fin m → ℝ) :
    physicsFourierFlatCLM (SCV.translateSchwartz a ψ) ξ =
      Complex.exp (-(Complex.I * ∑ i, (a i : ℂ) * (ξ i : ℂ))) *
        physicsFourierFlatCLM ψ ξ := by
  rw [← physicsFourierFlatCLM_integral, ← physicsFourierFlatCLM_integral]
  let g : (Fin m → ℝ) → ℂ := fun x =>
    Complex.exp (Complex.I * ∑ i, (((x i : ℂ) - (a i : ℂ)) * (ξ i : ℂ))) * ψ x
  have hg_shift :
      (fun x : Fin m → ℝ => g (x + a)) =
        (fun x : Fin m → ℝ =>
          Complex.exp (Complex.I * ∑ i, (x i : ℂ) * (ξ i : ℂ)) *
            SCV.translateSchwartz a ψ x) := by
    funext x
    simp [g, SCV.translateSchwartz_apply]
  calc
    ∫ x : Fin m → ℝ,
        Complex.exp (Complex.I * ∑ i, (x i : ℂ) * (ξ i : ℂ)) *
          SCV.translateSchwartz a ψ x
      = ∫ x : Fin m → ℝ, g (x + a) := by
          simp [hg_shift]
    _ = ∫ x : Fin m → ℝ, g x := by
          simpa [g] using MeasureTheory.integral_add_right_eq_self g a
    _ = ∫ x : Fin m → ℝ,
          Complex.exp (-(Complex.I * ∑ i, (a i : ℂ) * (ξ i : ℂ))) *
            (Complex.exp (Complex.I * ∑ i, (x i : ℂ) * (ξ i : ℂ)) * ψ x) := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with x
          dsimp [g]
          have hsum :
              Complex.I * ∑ i, (((x i : ℂ) - (a i : ℂ)) * (ξ i : ℂ)) =
                -(Complex.I * ∑ i, (a i : ℂ) * (ξ i : ℂ)) +
                  Complex.I * ∑ i, (x i : ℂ) * (ξ i : ℂ) := by
            calc
              Complex.I * ∑ i, (((x i : ℂ) - (a i : ℂ)) * (ξ i : ℂ))
                  = ∑ i, Complex.I *
                      ((((x i : ℂ) - (a i : ℂ)) * (ξ i : ℂ))) := by
                      rw [Finset.mul_sum]
              _ = ∑ i, (Complex.I * ((x i : ℂ) * (ξ i : ℂ)) -
                    Complex.I * ((a i : ℂ) * (ξ i : ℂ))) := by
                      refine Finset.sum_congr rfl ?_
                      intro i _hi
                      ring
              _ = -(Complex.I * ∑ i, (a i : ℂ) * (ξ i : ℂ)) +
                    Complex.I * ∑ i, (x i : ℂ) * (ξ i : ℂ) := by
                      rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
                      ring
          rw [hsum, Complex.exp_add]
          simp [mul_assoc]
    _ = Complex.exp (-(Complex.I * ∑ i, (a i : ℂ) * (ξ i : ℂ))) *
          ∫ x : Fin m → ℝ,
            Complex.exp (Complex.I * ∑ i, (x i : ℂ) * (ξ i : ℂ)) * ψ x := by
          simpa [mul_assoc] using
            (MeasureTheory.integral_const_mul
              (Complex.exp (-(Complex.I * ∑ i, (a i : ℂ) * (ξ i : ℂ))))
              (fun x : Fin m → ℝ =>
                Complex.exp (Complex.I * ∑ i, (x i : ℂ) * (ξ i : ℂ)) * ψ x))

theorem physicsFourierFlatCLM_surjective (m : ℕ) :
    Function.Surjective
      (physicsFourierFlatCLM :
        SchwartzMap (Fin m → ℝ) ℂ → SchwartzMap (Fin m → ℝ) ℂ) := by
  intro K
  let a : ℝˣ := Units.mk0 (-(1 / (2 * Real.pi) : ℝ)) <| by
    apply neg_ne_zero.mpr
    exact one_div_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  let scaleNeg : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ) :=
    ContinuousLinearEquiv.smulLeft a
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (Fin m) ℝ
  let toEuc : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
      SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
  let fromEuc : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ →L[ℂ]
      SchwartzMap (Fin m → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm
  let unscaleK : SchwartzMap (Fin m → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ scaleNeg.symm K
  let A : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ := toEuc unscaleK
  let ψE : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ := FourierTransform.fourierInv A
  let φ : SchwartzMap (Fin m → ℝ) ℂ := fromEuc ψE
  have h_to_from : toEuc φ = ψE := by
    ext y
    simp [toEuc, fromEuc, φ, e]
  have h_fourier : (SchwartzMap.fourierTransformCLM ℂ) (toEuc φ) = A := by
    rw [h_to_from]
    simp [ψE]
  have h_from_to : fromEuc A = unscaleK := by
    ext ξ
    change K (scaleNeg.symm ((EuclideanSpace.equiv (Fin m) ℝ) (WithLp.toLp 2 ξ))) =
      K (scaleNeg.symm ξ)
    have hx : ((EuclideanSpace.equiv (Fin m) ℝ) (WithLp.toLp 2 ξ)) = ξ := by
      ext i
      simp [EuclideanSpace.equiv]
    rw [hx]
  have h_scale :
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ scaleNeg) unscaleK = K := by
    ext ξ
    change K (scaleNeg.symm (scaleNeg ξ)) = K ξ
    rw [ContinuousLinearEquiv.symm_apply_apply]
  refine ⟨φ, ?_⟩
  calc
    physicsFourierFlatCLM φ
        = (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ scaleNeg)
            (fromEuc ((SchwartzMap.fourierTransformCLM ℂ) (toEuc φ))) := by
            rfl
    _ = (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ scaleNeg) (fromEuc A) := by
            rw [h_fourier]
    _ = (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ scaleNeg) unscaleK := by
            rw [h_from_to]
    _ = K := h_scale

/-- Continuous linear right inverse for the physics-convention flat Fourier
transform.  This exposes the constructive inverse hidden in
`physicsFourierFlatCLM_surjective`, so later quotient descents can use a
linear/continuous section rather than arbitrary preimage choice. -/
noncomputable def physicsFourierFlatInvCLM {m : ℕ} :
    SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] SchwartzMap (Fin m → ℝ) ℂ :=
  let a : ℝˣ := Units.mk0 (-(1 / (2 * Real.pi) : ℝ)) <| by
    apply neg_ne_zero.mpr
    exact one_div_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  let scaleNeg : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ) :=
    ContinuousLinearEquiv.smulLeft a
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (Fin m) ℝ
  let toEuc : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
      SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
  let fromEuc : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ →L[ℂ]
      SchwartzMap (Fin m → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm
  fromEuc.comp
    ((FourierTransform.fourierInvCLM ℂ
        (SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ)).comp
      (toEuc.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ scaleNeg.symm)))

/-- The physics-convention flat Fourier transform composed with its explicit
continuous linear right inverse is the identity. -/
theorem physicsFourierFlatCLM_inv_right {m : ℕ}
    (K : SchwartzMap (Fin m → ℝ) ℂ) :
    physicsFourierFlatCLM (physicsFourierFlatInvCLM K) = K := by
  let a : ℝˣ := Units.mk0 (-(1 / (2 * Real.pi) : ℝ)) <| by
    apply neg_ne_zero.mpr
    exact one_div_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  let scaleNeg : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ) :=
    ContinuousLinearEquiv.smulLeft a
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (Fin m) ℝ
  let toEuc : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
      SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
  let fromEuc : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ →L[ℂ]
      SchwartzMap (Fin m → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm
  let unscaleK : SchwartzMap (Fin m → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ scaleNeg.symm K
  let A : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ := toEuc unscaleK
  let ψE : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ :=
    (FourierTransform.fourierInvCLM ℂ
      (SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ)) A
  let φ : SchwartzMap (Fin m → ℝ) ℂ := fromEuc ψE
  have hφ_def : physicsFourierFlatInvCLM K = φ := by
    rfl
  have h_to_from : toEuc φ = ψE := by
    ext y
    simp [toEuc, fromEuc, φ, e]
  have h_fourier : (SchwartzMap.fourierTransformCLM ℂ) (toEuc φ) = A := by
    rw [h_to_from]
    simp [ψE]
  have h_from_to : fromEuc A = unscaleK := by
    ext ξ
    change K (scaleNeg.symm ((EuclideanSpace.equiv (Fin m) ℝ) (WithLp.toLp 2 ξ))) =
      K (scaleNeg.symm ξ)
    have hx : ((EuclideanSpace.equiv (Fin m) ℝ) (WithLp.toLp 2 ξ)) = ξ := by
      ext i
      simp [EuclideanSpace.equiv]
    rw [hx]
  have h_scale :
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ scaleNeg) unscaleK = K := by
    ext ξ
    change K (scaleNeg.symm (scaleNeg ξ)) = K ξ
    rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [hφ_def]
  calc
    physicsFourierFlatCLM φ
        = (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ scaleNeg)
            (fromEuc ((SchwartzMap.fourierTransformCLM ℂ) (toEuc φ))) := by
            rfl
    _ = (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ scaleNeg) (fromEuc A) := by
            rw [h_fourier]
    _ = (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ scaleNeg) unscaleK := by
            rw [h_from_to]
    _ = K := h_scale

/-- The explicit continuous inverse also cancels the physics-convention flat
Fourier transform on the left. -/
theorem physicsFourierFlatInvCLM_left {m : ℕ}
    (φ : SchwartzMap (Fin m → ℝ) ℂ) :
    physicsFourierFlatInvCLM (physicsFourierFlatCLM φ) = φ := by
  let a : ℝˣ := Units.mk0 (-(1 / (2 * Real.pi) : ℝ)) <| by
    apply neg_ne_zero.mpr
    exact one_div_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  let scaleNeg : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ) :=
    ContinuousLinearEquiv.smulLeft a
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (Fin m) ℝ
  let toEuc : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
      SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
  let fromEuc : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ →L[ℂ]
      SchwartzMap (Fin m → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm
  let ft : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ →L[ℂ]
      SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ :=
    SchwartzMap.fourierTransformCLM ℂ
  let ftInv : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ →L[ℂ]
      SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ :=
    FourierTransform.fourierInvCLM ℂ
      (SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ)
  have hphysics :
      physicsFourierFlatCLM φ =
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ scaleNeg)
          (fromEuc (ft (toEuc φ))) := by
    rfl
  have hunscale :
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ scaleNeg.symm
          (physicsFourierFlatCLM φ) =
        fromEuc (ft (toEuc φ)) := by
    rw [hphysics]
    ext ξ
    change
      (fromEuc (ft (toEuc φ))) (scaleNeg (scaleNeg.symm ξ)) =
        (fromEuc (ft (toEuc φ))) ξ
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hto_from (K : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ) :
      toEuc (fromEuc K) = K := by
    ext x
    simp [toEuc, fromEuc, e]
  have hfrom_to : fromEuc (toEuc φ) = φ := by
    ext x
    change φ (e (e.symm x)) = φ x
    rw [ContinuousLinearEquiv.apply_symm_apply]
  calc
    physicsFourierFlatInvCLM (physicsFourierFlatCLM φ) =
        fromEuc
          (ftInv
            (toEuc
              (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ scaleNeg.symm
                (physicsFourierFlatCLM φ)))) := by
          rfl
    _ = fromEuc (ftInv (toEuc (fromEuc (ft (toEuc φ))))) := by
          rw [hunscale]
    _ = fromEuc (ftInv (ft (toEuc φ))) := by
          rw [hto_from]
    _ = fromEuc (toEuc φ) := by
          simp [ftInv, ft]
    _ = φ := hfrom_to

/-- The deterministic Section 4.3 frequency representative map is onto. -/
theorem section43FrequencyRepresentative_surjective
    (d n : ℕ) [NeZero d] :
    Function.Surjective
      (section43FrequencyRepresentative d n :
        SchwartzNPoint d n → SchwartzNPoint d n) := by
  intro Φ
  let Kflat : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (section43CumulativeTailMomentumCLE d n) Φ
  obtain ⟨φflat, hφflat⟩ :=
    physicsFourierFlatCLM_surjective (n * (d + 1)) Kflat
  refine ⟨unflattenSchwartzNPoint (d := d) φflat, ?_⟩
  have hflat :
      flattenSchwartzNPoint (d := d)
          (unflattenSchwartzNPoint (d := d) φflat) = φflat := by
    ext ξ
    simp [flattenSchwartzNPoint_apply, unflattenSchwartzNPoint_apply]
  calc
    section43FrequencyRepresentative d n
        (unflattenSchwartzNPoint (d := d) φflat)
        =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (section43CumulativeTailMomentumCLE d n).symm
        (physicsFourierFlatCLM φflat) := by
          simp [section43FrequencyRepresentative, hflat]
    _ =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (section43CumulativeTailMomentumCLE d n).symm Kflat := by
          rw [hφflat]
    _ = Φ := by
          ext q
          simp [Kflat, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

/-- Continuous linear right inverse for the deterministic Section 4.3 frequency
representative.  This is the quotient-safe replacement for choosing preimages
from `section43FrequencyRepresentative_surjective`. -/
noncomputable def section43FrequencyRepresentativeInv (d n : ℕ) [NeZero d] :
    SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n :=
  (unflattenSchwartzNPoint (d := d)).comp
    (physicsFourierFlatInvCLM.comp
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (section43CumulativeTailMomentumCLE d n)))

/-- The deterministic frequency representative composed with its explicit
continuous linear right inverse is the identity. -/
theorem section43FrequencyRepresentativeInv_right
    (d n : ℕ) [NeZero d]
    (Φ : SchwartzNPoint d n) :
    section43FrequencyRepresentative d n
      (section43FrequencyRepresentativeInv d n Φ) = Φ := by
  let Kflat : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (section43CumulativeTailMomentumCLE d n) Φ
  have hflat :
      flattenSchwartzNPoint (d := d)
          (section43FrequencyRepresentativeInv d n Φ) =
        physicsFourierFlatInvCLM Kflat := by
    ext ξ
    simp [section43FrequencyRepresentativeInv, Kflat,
      flattenSchwartzNPoint_apply, unflattenSchwartzNPoint_apply]
  calc
    section43FrequencyRepresentative d n
        (section43FrequencyRepresentativeInv d n Φ)
        = SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (section43CumulativeTailMomentumCLE d n).symm
            (physicsFourierFlatCLM (physicsFourierFlatInvCLM Kflat)) := by
          simp [section43FrequencyRepresentative, hflat]
    _ = SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (section43CumulativeTailMomentumCLE d n).symm Kflat := by
          rw [physicsFourierFlatCLM_inv_right]
    _ = Φ := by
          ext q
          simp [Kflat, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

def section43TotalMomentumFlat
    (d N : ℕ) [NeZero d]
    (ξ : Fin (N * (d + 1)) → ℝ) : Fin (d + 1) → ℝ :=
  fun μ => ∑ k : Fin N, ξ (finProdFinEquiv (k, μ))

noncomputable def section43TotalMomentumComponentCLM
    (d N : ℕ) [NeZero d]
    (μ : Fin (d + 1)) :
    (Fin (N * (d + 1)) → ℝ) →L[ℝ] ℝ :=
  ∑ k : Fin N,
    ContinuousLinearMap.proj (R := ℝ) (ι := Fin (N * (d + 1)))
      (φ := fun _ => ℝ) (finProdFinEquiv (k, μ))

@[simp] theorem section43TotalMomentumComponentCLM_apply
    (d N : ℕ) [NeZero d]
    (μ : Fin (d + 1))
    (ξ : Fin (N * (d + 1)) → ℝ) :
    section43TotalMomentumComponentCLM d N μ ξ =
      section43TotalMomentumFlat d N ξ μ := by
  simp [section43TotalMomentumComponentCLM, section43TotalMomentumFlat]

noncomputable def section43TotalMomentumPairingCLM
    (d N : ℕ) [NeZero d]
    (a : Fin (d + 1) → ℝ) :
    (Fin (N * (d + 1)) → ℝ) →L[ℝ] ℝ :=
  ∑ μ : Fin (d + 1), a μ • section43TotalMomentumComponentCLM d N μ

@[simp] theorem section43TotalMomentumPairingCLM_apply
    (d N : ℕ) [NeZero d]
    (a : Fin (d + 1) → ℝ)
    (ξ : Fin (N * (d + 1)) → ℝ) :
    section43TotalMomentumPairingCLM d N a ξ =
      ∑ μ : Fin (d + 1), a μ * section43TotalMomentumFlat d N ξ μ := by
  simp [section43TotalMomentumPairingCLM]

def section43TotalMomentumZeroFlat
    (d N : ℕ) [NeZero d] :
    Set (Fin (N * (d + 1)) → ℝ) :=
  {ξ | section43TotalMomentumFlat d N ξ = 0}

def section43WightmanSpectralRegion
    (d N : ℕ) [NeZero d] :
    Set (Fin (N * (d + 1)) → ℝ) :=
  DualConeFlat ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N) ∩
    section43TotalMomentumZeroFlat d N

def section43DiagonalTranslationFlat
    (d N : ℕ) [NeZero d]
    (a : Fin (d + 1) → ℝ) : Fin (N * (d + 1)) → ℝ :=
  fun i =>
    let p := finProdFinEquiv.symm i
    a p.2

theorem section43DiagonalTranslationFlat_pair_eq_totalMomentum
    (d N : ℕ) [NeZero d]
    (a : Fin (d + 1) → ℝ)
    (ξ : Fin (N * (d + 1)) → ℝ) :
    (∑ i : Fin (N * (d + 1)),
        section43DiagonalTranslationFlat d N a i * ξ i)
      =
    ∑ μ : Fin (d + 1),
      a μ * section43TotalMomentumFlat d N ξ μ := by
  classical
  calc
    (∑ i : Fin (N * (d + 1)),
        section43DiagonalTranslationFlat d N a i * ξ i)
        = ∑ p : Fin N × Fin (d + 1),
            a p.2 * ξ (finProdFinEquiv p) := by
          simpa [section43DiagonalTranslationFlat] using
            (finProdFinEquiv.sum_comp
              (fun i : Fin (N * (d + 1)) =>
                section43DiagonalTranslationFlat d N a i * ξ i)).symm
    _ = ∑ k : Fin N, ∑ μ : Fin (d + 1),
            a μ * ξ (finProdFinEquiv (k, μ)) := by
          simpa using
            (Finset.sum_product (s := (Finset.univ : Finset (Fin N)))
              (t := (Finset.univ : Finset (Fin (d + 1))))
              (f := fun p : Fin N × Fin (d + 1) =>
                a p.2 * ξ (finProdFinEquiv p)))
    _ = ∑ μ : Fin (d + 1), ∑ k : Fin N,
            a μ * ξ (finProdFinEquiv (k, μ)) := by
          rw [Finset.sum_comm]
    _ = ∑ μ : Fin (d + 1),
          a μ * section43TotalMomentumFlat d N ξ μ := by
          simp [section43TotalMomentumFlat, Finset.mul_sum]

theorem section43DiagonalTranslationFlat_complex_pair_eq_totalMomentum
    (d N : ℕ) [NeZero d]
    (a : Fin (d + 1) → ℝ)
    (ξ : Fin (N * (d + 1)) → ℝ) :
    (∑ i : Fin (N * (d + 1)),
        (section43DiagonalTranslationFlat d N a i : ℂ) * (ξ i : ℂ))
      =
    ∑ μ : Fin (d + 1),
      (a μ : ℂ) * (section43TotalMomentumFlat d N ξ μ : ℂ) := by
  have h := congrArg (fun r : ℝ => (r : ℂ))
    (section43DiagonalTranslationFlat_pair_eq_totalMomentum d N a ξ)
  simpa using h

theorem physicsFourierFlatCLM_diagonalTranslate_apply
    (d N : ℕ) [NeZero d]
    (a : Fin (d + 1) → ℝ)
    (φflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ)
    (ξ : Fin (N * (d + 1)) → ℝ) :
    physicsFourierFlatCLM
        (SCV.translateSchwartz (section43DiagonalTranslationFlat d N a) φflat) ξ
      =
    Complex.exp
        (-(Complex.I *
          ∑ μ : Fin (d + 1),
            (a μ : ℂ) * (section43TotalMomentumFlat d N ξ μ : ℂ))) *
      physicsFourierFlatCLM φflat ξ := by
  rw [section43_physicsFourierFlatCLM_translateSchwartz_apply]
  rw [section43DiagonalTranslationFlat_complex_pair_eq_totalMomentum]

theorem section43_realOscillatoryPhase_hasTemperateGrowth (lam : ℝ) :
    (fun τ : ℝ =>
      Complex.exp (-(Complex.I * (lam : ℂ) * (τ : ℂ)))).HasTemperateGrowth := by
  let c : ℂ := -(Complex.I * (lam : ℂ))
  suffices htemp : (fun τ : ℝ => Complex.exp (c * (τ : ℂ))).HasTemperateGrowth by
    convert htemp using 1
    ext τ
    simp [c, mul_assoc]
  refine ⟨?_, ?_⟩
  · have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun τ : ℝ => c * (τ : ℂ)) := by
      simpa using (contDiff_const.mul Complex.ofRealCLM.contDiff)
    exact Complex.contDiff_exp.comp hlin
  · intro n
    refine ⟨0, ‖c ^ n‖, fun τ => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hiter := congr_fun (SCV.iteratedDeriv_cexp_const_mul_real n c) τ
    rw [hiter]
    have hre : (c * (τ : ℂ)).re = 0 := by
      simp [c, Complex.mul_re]
    calc
      ‖c ^ n * Complex.exp (c * (τ : ℂ))‖ = ‖c ^ n‖ := by
        rw [norm_mul, Complex.norm_exp, hre, Real.exp_zero, mul_one]
      _ ≤ ‖c ^ n‖ * (1 + ‖τ‖) ^ 0 := by simp

theorem section43TotalMomentumPhase_hasTemperateGrowth
    (d N : ℕ) [NeZero d]
    (a : Fin (d + 1) → ℝ) :
    (fun ξ : Fin (N * (d + 1)) → ℝ =>
      Complex.exp
        (-(Complex.I *
          ∑ μ : Fin (d + 1),
            (a μ : ℂ) * (section43TotalMomentumFlat d N ξ μ : ℂ)))).HasTemperateGrowth := by
  let L : (Fin (N * (d + 1)) → ℝ) →L[ℝ] ℝ :=
    section43TotalMomentumPairingCLM d N a
  have hL : Function.HasTemperateGrowth L := by
    exact L.hasTemperateGrowth
  have hphase := (section43_realOscillatoryPhase_hasTemperateGrowth 1).comp hL
  convert hphase using 1
  ext ξ
  simp [L]

noncomputable def section43TotalMomentumPhaseCLM
    (d N : ℕ) [NeZero d]
    (a : Fin (d + 1) → ℝ) :
    SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ →L[ℂ]
      SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ :=
  SchwartzMap.smulLeftCLM ℂ
    (fun ξ : Fin (N * (d + 1)) → ℝ =>
      Complex.exp
        (-(Complex.I *
          ∑ μ : Fin (d + 1),
            (a μ : ℂ) * (section43TotalMomentumFlat d N ξ μ : ℂ))))

@[simp] theorem section43TotalMomentumPhaseCLM_apply
    (d N : ℕ) [NeZero d]
    (a : Fin (d + 1) → ℝ)
    (K : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ)
    (ξ : Fin (N * (d + 1)) → ℝ) :
    section43TotalMomentumPhaseCLM d N a K ξ =
      Complex.exp
        (-(Complex.I *
          ∑ μ : Fin (d + 1),
            (a μ : ℂ) * (section43TotalMomentumFlat d N ξ μ : ℂ))) * K ξ := by
  rw [section43TotalMomentumPhaseCLM]
  exact SchwartzMap.smulLeftCLM_apply_apply
    (section43TotalMomentumPhase_hasTemperateGrowth d N a) K ξ

theorem physicsFourierFlatCLM_diagonalTranslate_eq_phaseCLM
    (d N : ℕ) [NeZero d]
    (a : Fin (d + 1) → ℝ)
    (φflat : SchwartzMap (Fin (N * (d + 1)) → ℝ) ℂ) :
    physicsFourierFlatCLM
        (SCV.translateSchwartz (section43DiagonalTranslationFlat d N a) φflat)
      =
    section43TotalMomentumPhaseCLM d N a (physicsFourierFlatCLM φflat) := by
  ext ξ
  rw [physicsFourierFlatCLM_diagonalTranslate_apply]
  rw [section43TotalMomentumPhaseCLM_apply]

theorem flatComplexPairing_hasTemperateGrowth {m : ℕ}
    (v : Fin m → ℝ) :
    (fun ξ : Fin m → ℝ =>
      ∑ i : Fin m, (v i : ℂ) * (ξ i : ℂ)).HasTemperateGrowth := by
  let L : (Fin m → ℝ) →L[ℝ] ℝ :=
    ∑ i : Fin m,
      v i • ContinuousLinearMap.proj (R := ℝ) (ι := Fin m)
        (φ := fun _ => ℝ) i
  have hL : Function.HasTemperateGrowth L := L.hasTemperateGrowth
  have hC := Complex.ofRealCLM.toContinuousLinearMap.hasTemperateGrowth.comp hL
  convert hC using 1
  ext ξ
  simp [L]

theorem physicsFourierFlatCLM_lineDeriv_eq_pairingMultiplier {m : ℕ}
    (v : Fin m → ℝ)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) :
    physicsFourierFlatCLM (∂_{v} φ)
      =
    (-Complex.I) •
      SchwartzMap.smulLeftCLM ℂ
        (fun ξ : Fin m → ℝ =>
          ∑ i : Fin m, (v i : ℂ) * (ξ i : ℂ))
        (physicsFourierFlatCLM φ) := by
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (Fin m) ℝ
  have hderiv :
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e) (∂_{v} φ) =
        ∂_{e.symm v} ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e) φ) := by
    symm
    simpa only [e.apply_symm_apply] using
      (SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv (𝕜 := ℂ)
        (m := e.symm v) (g := e) (f := φ))
  have hpair :
      (fun ξ : Fin m → ℝ =>
        ∑ i : Fin m, (v i : ℂ) * (ξ i : ℂ)).HasTemperateGrowth :=
    flatComplexPairing_hasTemperateGrowth v
  have hinner :
      (fun x : EuclideanSpace ℝ (Fin m) =>
        inner ℝ x (e.symm v)).HasTemperateGrowth := by
    have hL : Function.HasTemperateGrowth ((innerSL ℝ) (e.symm v)) := by
      exact ((innerSL ℝ) (e.symm v)).hasTemperateGrowth
    simpa [real_inner_comm] using hL
  ext ξ
  rw [physicsFourierFlatCLM_apply]
  rw [SchwartzMap.smul_apply]
  rw [SchwartzMap.smulLeftCLM_apply_apply hpair]
  rw [physicsFourierFlatCLM_apply]
  unfold inverseFourierFlatCLM
  simp only [ContinuousLinearMap.comp_apply]
  rw [hderiv]
  rw [SchwartzMap.fourierTransformCLM_apply]
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
  rw [SchwartzMap.smul_apply]
  rw [SchwartzMap.smulLeftCLM_apply_apply hinner]
  have hinner_eval :
      inner ℝ ((EuclideanSpace.equiv (Fin m) ℝ).symm
          (-(1 / (2 * Real.pi)) • ξ)) (e.symm v) =
        (-(1 / (2 * Real.pi))) * ∑ i : Fin m, ξ i * v i := by
    rw [PiLp.inner_apply]
    simp [e, EuclideanSpace.equiv, inner, Finset.mul_sum,
      mul_assoc, mul_comm]
  rw [hinner_eval]
  simp only [e]
  let Z : ℂ :=
    (𝓕 ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (EuclideanSpace.equiv (Fin m) ℝ)) φ))
      ((EuclideanSpace.equiv (Fin m) ℝ).symm (-(1 / (2 * Real.pi)) • ξ))
  change (2 * (Real.pi : ℂ) * Complex.I) •
      (((-(1 / (2 * Real.pi)) * ∑ i : Fin m, ξ i * v i) : ℝ) • Z) =
    ((-Complex.I) • ((∑ i : Fin m, (v i : ℂ) * (ξ i : ℂ)) • Z))
  simp [smul_eq_mul, Complex.real_smul, Complex.ofReal_sum, Finset.mul_sum,
    mul_assoc, mul_comm]
  have hscaled :
      (∑ x : Fin m,
          (v x : ℂ) * ((ξ x : ℂ) * ((Real.pi : ℂ)⁻¹ * 2⁻¹))) =
        (∑ i : Fin m, (v i : ℂ) * (ξ i : ℂ)) *
          ((Real.pi : ℂ)⁻¹ * 2⁻¹) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    ring
  rw [hscaled]
  have hπc : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  field_simp [hπc]

/-- The distinguished difference coordinate at the boundary between the left
block and the shifted right tail. -/
def section43TailGapIndex {n m : ℕ} (hm : 0 < m) : Fin (n + m) :=
  ⟨n, Nat.lt_add_of_pos_right hm⟩

/-- The same distinguished tail-gap coordinate, written in the `(N + 1)` degree
form required by `section43TimeSplitMeasurableEquiv`, where
`N = n + m - 1`. -/
def section43TailGapSplitIndex {n m : ℕ} (hm : 0 < m) : Fin (n + m - 1 + 1) :=
  ⟨n, by omega⟩

@[simp] theorem section43TailGapIndex_val {n m : ℕ} (hm : 0 < m) :
    (section43TailGapIndex (n := n) (m := m) hm).val = n := rfl

@[simp] theorem section43TailGapSplitIndex_val {n m : ℕ} (hm : 0 < m) :
    (section43TailGapSplitIndex (n := n) (m := m) hm).val = n := rfl

/-- Background index corresponding to an un-reversed left-block coordinate
after the tail-gap coordinate has been removed. -/
def section43TailBgLeftIndex {n m : ℕ} (hm : 0 < m) (i : Fin n) :
    Fin (n + m - 1) :=
  ⟨i.val, by omega⟩

/-- Background index corresponding to a right-block internal coordinate after
the tail-gap coordinate has been removed. -/
def section43TailBgRightIndex {n m : ℕ} (hm : 0 < m) (j : Fin (m - 1)) :
    Fin (n + m - 1) :=
  ⟨n + j.val, by omega⟩

/-- Background index corresponding to the Borchers-reversed left block after
the tail-gap coordinate has been removed. -/
def section43TailBgLeftRevIndex {n m : ℕ} (hm : 0 < m) (i : Fin n) :
    Fin (n + m - 1) :=
  section43TailBgLeftIndex (n := n) (m := m) hm (Fin.rev i)

@[simp] theorem section43TailBgLeftIndex_val {n m : ℕ} (hm : 0 < m)
    (i : Fin n) :
    (section43TailBgLeftIndex (n := n) (m := m) hm i).val = i.val := rfl

@[simp] theorem section43TailBgRightIndex_val {n m : ℕ} (hm : 0 < m)
    (j : Fin (m - 1)) :
    (section43TailBgRightIndex (n := n) (m := m) hm j).val = n + j.val := rfl

@[simp] theorem section43TailBgLeftRevIndex_val {n m : ℕ} (hm : 0 < m)
    (i : Fin n) :
    (section43TailBgLeftRevIndex (n := n) (m := m) hm i).val = (Fin.rev i).val := rfl

/-- The left block of a full Section-4.3 positive-energy point. -/
def section43LeftBlock (d n m : ℕ) [NeZero d]
    (q : NPointDomain d (n + m)) : NPointDomain d n :=
  fun i => q (Fin.castAdd m i)

/-- The Borchers-reversed left block of a full Section-4.3 positive-energy
point. -/
def section43LeftRevBlock (d n m : ℕ) [NeZero d]
    (q : NPointDomain d (n + m)) : NPointDomain d n :=
  fun i => q (Fin.castAdd m (Fin.rev i))

/-- The right tail block of a full Section-4.3 positive-energy point,
including the boundary/tail-gap coordinate as its first coordinate. -/
def section43RightTailBlock (d n m : ℕ) [NeZero d]
    (q : NPointDomain d (n + m)) : NPointDomain d m :=
  fun j => q (Fin.natAdd n j)

@[simp] theorem section43LeftBlock_apply (d n m : ℕ) [NeZero d]
    (q : NPointDomain d (n + m)) (i : Fin n) :
    section43LeftBlock d n m q i = q (Fin.castAdd m i) := rfl

@[simp] theorem section43LeftRevBlock_apply (d n m : ℕ) [NeZero d]
    (q : NPointDomain d (n + m)) (i : Fin n) :
    section43LeftRevBlock d n m q i = q (Fin.castAdd m (Fin.rev i)) := rfl

@[simp] theorem section43RightTailBlock_apply (d n m : ℕ) [NeZero d]
    (q : NPointDomain d (n + m)) (j : Fin m) :
    section43RightTailBlock d n m q j = q (Fin.natAdd n j) := rfl

/-- Positive-energy support passes to the right tail block. -/
theorem section43RightTailBlock_mem_positiveEnergy
    (d n m : ℕ) [NeZero d]
    {q : NPointDomain d (n + m)}
    (hq : q ∈ section43PositiveEnergyRegion d (n + m)) :
    section43RightTailBlock d n m q ∈ section43PositiveEnergyRegion d m := by
  intro j
  simpa [section43PositiveEnergyRegion, section43RightTailBlock] using
    hq (Fin.natAdd n j)

/-- Time coordinates of the left block are the corresponding full time
coordinates before the tail. -/
theorem section43QTime_leftBlock
    (d n m : ℕ) [NeZero d]
    (q : NPointDomain d (n + m)) (i : Fin n) :
    section43QTime (d := d) (n := n) (section43LeftBlock d n m q) i =
      section43QTime (d := d) (n := n + m) q (Fin.castAdd m i) := by
  simp [section43QTime, nPointTimeSpatialCLE, section43LeftBlock]

/-- Time coordinates of the right tail block are the corresponding full time
coordinates starting at the tail. -/
theorem section43QTime_rightTailBlock
    (d n m : ℕ) [NeZero d]
    (q : NPointDomain d (n + m)) (j : Fin m) :
    section43QTime (d := d) (n := m) (section43RightTailBlock d n m q) j =
      section43QTime (d := d) (n := n + m) q (Fin.natAdd n j) := by
  simp [section43QTime, nPointTimeSpatialCLE, section43RightTailBlock]

/-- Spatial coordinates of the left block are the corresponding full spatial
coordinates before the tail. -/
theorem section43QSpatial_leftBlock_apply
    (d n m : ℕ) [NeZero d]
    (q : NPointDomain d (n + m)) (p : Fin n × Fin d) :
    (EuclideanSpace.equiv (ι := Fin n × Fin d) (𝕜 := ℝ)
      (section43QSpatial (d := d) (n := n) (section43LeftBlock d n m q))) p =
    (EuclideanSpace.equiv (ι := Fin (n + m) × Fin d) (𝕜 := ℝ)
      (section43QSpatial (d := d) (n := n + m) q)) (Fin.castAdd m p.1, p.2) := by
  simp [section43QSpatial, nPointTimeSpatialCLE, section43LeftBlock]

/-- Spatial coordinates of the right tail block are the corresponding full
spatial coordinates starting at the tail. -/
theorem section43QSpatial_rightTailBlock_apply
    (d n m : ℕ) [NeZero d]
    (q : NPointDomain d (n + m)) (p : Fin m × Fin d) :
    (EuclideanSpace.equiv (ι := Fin m × Fin d) (𝕜 := ℝ)
      (section43QSpatial (d := d) (n := m) (section43RightTailBlock d n m q))) p =
    (EuclideanSpace.equiv (ι := Fin (n + m) × Fin d) (𝕜 := ℝ)
      (section43QSpatial (d := d) (n := n + m) q)) (Fin.natAdd n p.1, p.2) := by
  simp [section43QSpatial, nPointTimeSpatialCLE, section43RightTailBlock]

/-- Split the time-coordinate block into one distinguished coordinate and the
remaining background coordinates. -/
noncomputable def section43TimeSplitCLE {n : ℕ} (r : Fin n) :
    (Fin n → ℝ) ≃L[ℝ] ℝ × ({i : Fin n // i ≠ r} → ℝ) := by
  let e : (Fin n → ℝ) ≃ₗ[ℝ] ℝ × ({i : Fin n // i ≠ r} → ℝ) :=
    { toFun := fun τ => (τ r, fun i => τ i.1)
      invFun := fun p i => if hi : i = r then p.1 else p.2 ⟨i, hi⟩
      map_add' := by
        intro τ σ
        ext i <;> simp
      map_smul' := by
        intro a τ
        ext i <;> simp
      left_inv := by
        intro τ
        funext i
        by_cases hi : i = r
        · simp [hi]
        · simp [hi]
      right_inv := by
        intro p
        ext i
        · simp
        · simp [i.2] }
  exact e.toContinuousLinearEquiv

@[simp] theorem section43TimeSplitCLE_apply {n : ℕ} (r : Fin n)
    (τ : Fin n → ℝ) :
    section43TimeSplitCLE r τ =
      (τ r, fun i : {i : Fin n // i ≠ r} => τ i.1) := rfl

/-- The scalar OS I `(4.20)` Fourier-Laplace integral built from the
difference-coordinate pullback.  The spatial Fourier sign and normalization
are inherited from `partialFourierSpatial_fun`. -/
noncomputable def section43FourierLaplaceIntegral (d n : ℕ) [NeZero d]
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (q : NPointDomain d n) : ℂ :=
  ∫ τ : Fin n → ℝ,
    Complex.exp
        (-(∑ k : Fin n,
          (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ))) *
      partialFourierSpatial_fun
        (d := d) (n := n) (section43DiffPullbackCLM d n f)
        (τ, section43QSpatial (d := d) (n := n) q)

@[simp] theorem nPointTimeSpatialSchwartzCLE_section43DiffPullbackCLM_apply
    (d n : ℕ) [NeZero d]
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (τ : Fin n → ℝ) (η : EuclideanSpace ℝ (Fin n × Fin d)) :
    nPointTimeSpatialSchwartzCLE (d := d) (n := n)
        (section43DiffPullbackCLM d n f) (τ, η) =
      f.1 ((section43DiffCoordRealCLE d n).symm
        ((nPointTimeSpatialCLE (d := d) n).symm (τ, η))) := by
  simp [nPointTimeSpatialSchwartzCLE, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

/-- Fully expanded OS I `(4.20)` form: time Laplace transform outside, spatial
Fourier integral inside. -/
theorem section43FourierLaplaceIntegral_eq_time_spatial_integral
    (d n : ℕ) [NeZero d]
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (q : NPointDomain d n) :
    section43FourierLaplaceIntegral d n f q =
      ∫ τ : Fin n → ℝ,
        Complex.exp
            (-(∑ k : Fin n,
              (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ))) *
          (∫ η : EuclideanSpace ℝ (Fin n × Fin d),
            𝐞 (-(inner ℝ η (section43QSpatial (d := d) (n := n) q))) •
              nPointTimeSpatialSchwartzCLE (d := d) (n := n)
                (section43DiffPullbackCLM d n f) (τ, η)) := by
  rw [section43FourierLaplaceIntegral]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with τ
  rw [partialFourierSpatial_fun_eq_integral]

/-- On the nonnegative time orthant, positive-energy external time variables
make the OS I `(4.20)` time-Laplace exponential bounded by `1`. -/
theorem norm_exp_neg_section43_timePair_le_one
    (d n : ℕ) [NeZero d]
    (q : NPointDomain d n) (τ : Fin n → ℝ)
    (hq : q ∈ section43PositiveEnergyRegion d n)
    (hτ : ∀ i : Fin n, 0 ≤ τ i) :
    ‖Complex.exp
      (-(∑ k : Fin n,
        (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ)))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  apply Real.exp_le_one_iff.mpr
  have hsum_nonneg :
      0 ≤ ∑ k : Fin n, τ k * section43QTime (d := d) (n := n) q k := by
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hτ k) (by
      simpa [section43QTime, nPointTimeSpatialCLE] using hq k)
  have hre :
      (-(∑ k : Fin n,
        (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ))).re =
        -(∑ k : Fin n, τ k * section43QTime (d := d) (n := n) q k) := by
    simp
  rw [hre]
  exact neg_nonpos.mpr hsum_nonneg

/-- Fixed-spatial-frequency time slices of the partial spatial Fourier
transform have polynomial decay in the full time-block norm. -/
theorem exists_normPow_bound_partialFourierSpatial_timeSlice
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ τ : Fin n → ℝ,
        ‖τ‖ ^ K *
          ‖partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ ≤ C := by
  rcases exists_norm_bound_partialFourierSpatial_fun (d := d) (n := n) f with
    ⟨C0, hC0_nonneg, hC0⟩
  by_cases hK : K = 0
  · subst K
    refine ⟨C0, hC0_nonneg, ?_⟩
    intro τ
    simpa using hC0 (τ, ξ)
  classical
  choose Ccoord hCcoord_nonneg hCcoord using
    fun i : Fin n =>
      exists_timeCoordPow_norm_bound_partialFourierSpatial_fun
        (d := d) (n := n) f i K
  let Csum : ℝ := C0 + ∑ i : Fin n, Ccoord i
  refine ⟨Csum, add_nonneg hC0_nonneg (Finset.sum_nonneg fun i _ => hCcoord_nonneg i), ?_⟩
  intro τ
  by_cases hτnorm : ‖τ‖ = 0
  · have hpow : ‖τ‖ ^ K = 0 := by
      rw [hτnorm]
      exact zero_pow hK
    exact le_trans (by simp [hpow]) (add_nonneg hC0_nonneg
      (Finset.sum_nonneg fun i _ => hCcoord_nonneg i))
  · have huniv_nonempty : (Finset.univ : Finset (Fin n)).Nonempty := by
      by_contra hne
      have hempty : (Finset.univ : Finset (Fin n)) = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hne
      have hnorm_zero : ‖τ‖ = 0 := by
        rw [Pi.norm_def]
        simp [hempty]
      exact hτnorm hnorm_zero
    obtain ⟨i, _hi, hi_sup⟩ :=
      Finset.exists_mem_eq_sup (s := (Finset.univ : Finset (Fin n))) huniv_nonempty
        (fun j : Fin n => ‖τ j‖₊)
    have hnorm_eq : ‖τ‖ = ‖τ i‖ := by
      rw [Pi.norm_def]
      exact congrArg (fun x : NNReal => (x : ℝ)) hi_sup
    have hcoord := hCcoord i (τ, ξ)
    have hrewrite :
        ‖τ‖ ^ K *
            ‖partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ =
          ‖((((τ i : ℝ) : ℂ)) ^ K) *
            partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ := by
      rw [norm_mul, norm_pow, Complex.norm_real, hnorm_eq]
    calc
      ‖τ‖ ^ K *
          ‖partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ =
          ‖((((τ i : ℝ) : ℂ)) ^ K) *
            partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)‖ := hrewrite
      _ ≤ Ccoord i := hcoord
      _ ≤ Csum := by
        have hi_le_sum : Ccoord i ≤ ∑ j : Fin n, Ccoord j :=
          Finset.single_le_sum (fun j _ => hCcoord_nonneg j) (Finset.mem_univ i)
        exact hi_le_sum.trans (by simp [Csum, hC0_nonneg])

/-- For fixed spatial frequency, the partial spatial Fourier transform is
integrable in all time variables. -/
theorem integrable_partialFourierSpatial_timeSlice
    (d n : ℕ) [NeZero d]
    (f : SchwartzNPoint d n)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    Integrable
      (fun τ : Fin n → ℝ =>
        partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)) := by
  let F : (Fin n → ℝ) → ℂ := fun τ =>
    partialFourierSpatial_fun (d := d) (n := n) f (τ, ξ)
  have hF_meas : AEStronglyMeasurable F (volume : Measure (Fin n → ℝ)) :=
    (contDiff_partialFourierSpatial_fun_time (d := d) (n := n) f ξ).continuous.aestronglyMeasurable
  rcases exists_norm_bound_partialFourierSpatial_fun (d := d) (n := n) f with
    ⟨C0, _hC0_nonneg, hC0⟩
  rcases exists_normPow_bound_partialFourierSpatial_timeSlice
      (d := d) (n := n) f ξ
      ((volume : Measure (Fin n → ℝ)).integrablePower) with
    ⟨C1, _hC1_nonneg, hC1⟩
  have hnorm_int :
      Integrable
        (fun τ : Fin n → ℝ => ‖τ‖ ^ 0 * ‖F τ‖)
        (volume : Measure (Fin n → ℝ)) := by
    exact integrable_of_le_of_pow_mul_le
      (μ := (volume : Measure (Fin n → ℝ)))
      (f := F)
      (C₁ := C0)
      (C₂ := C1)
      (k := 0)
      (fun τ => hC0 (τ, ξ))
      (by simpa [F, Nat.zero_add] using hC1)
      hF_meas
  exact hnorm_int.mono' hF_meas (Filter.Eventually.of_forall fun τ => by simp [F])

/-- An ambient Schwartz representative realizes the explicit OS I Section 4.3
Fourier-Laplace transform when, on the positive-energy half-space, it agrees
with the `(4.19)-(4.20)` scalar integral built from the difference-coordinate
pullback.

This predicate is deliberately stronger than the current
`os1TransportComponent` quotient-inclusion surface: it contains the actual
Fourier-Laplace formula, so it cannot be discharged by
`simp [os1TransportComponent_apply]`. -/
def section43FourierLaplaceRepresentative (d n : ℕ) [NeZero d]
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (Φ : SchwartzNPoint d n) : Prop :=
  ∀ q : NPointDomain d n, q ∈ section43PositiveEnergyRegion d n →
    Φ q = section43FourierLaplaceIntegral d n f q

theorem section43FourierLaplaceRepresentative_apply
    (d n : ℕ) [NeZero d]
    {f : euclideanPositiveTimeSubmodule (d := d) n}
    {Φ : SchwartzNPoint d n}
    (hΦ : section43FourierLaplaceRepresentative d n f Φ)
    {q : NPointDomain d n}
    (hq : q ∈ section43PositiveEnergyRegion d n) :
    Φ q = section43FourierLaplaceIntegral d n f q :=
  hΦ q hq

/-- Transfer a Section 4.3 Fourier-Laplace representative through the
positive-energy quotient to the deterministic frequency representative of an
ambient Wightman test. -/
theorem section43FrequencyRepresentative_is_fourierLaplaceRepresentative_of_quotient_eq
    (d n : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n)
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (Φ : SchwartzNPoint d n)
    (hΦ_rep : section43FourierLaplaceRepresentative d n f Φ)
    (hφ_proj :
      section43FrequencyProjection (d := d) n φ =
        section43PositiveEnergyQuotientMap (d := d) n Φ) :
    section43FourierLaplaceRepresentative d n f
      (section43FrequencyRepresentative (d := d) n φ) := by
  intro q hq
  have hquot :
      section43PositiveEnergyQuotientMap (d := d) n
          (section43FrequencyRepresentative (d := d) n φ) =
        section43PositiveEnergyQuotientMap (d := d) n Φ := by
    simpa [section43FrequencyProjection] using hφ_proj
  have hEqOn :=
    eqOn_region_of_section43PositiveEnergyQuotientMap_eq
      (d := d) (n := n) hquot
  exact (hEqOn hq).trans (hΦ_rep q hq)

end OSReconstruction
