import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSourceCurrent
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSchwingerSourceCurrent
import OSReconstruction.SCV.EuclideanWeylOpen

/-!
# OS-II A0 Local Schwinger Distributions

This file contains the first local-distribution bridge for the
Osterwalder-Schrader II `(A0)` route.  The Schwinger functional is only defined
on the OS-I zero-diagonal test space, so before applying local regularity or
representation machinery one must cut tests off away from the coincidence
locus.  The cutoff-localized functional below is a genuine continuous linear
functional on all Schwartz tests, and it agrees with the original Schwinger
value on smaller tests where the cutoff is identically one.
-/

noncomputable section

open Complex Topology MeasureTheory
open Set
open scoped Classical NNReal BigOperators

namespace OSReconstruction

variable {d n : ℕ}

/-- Multiplication by a cutoff whose support avoids the coincidence locus sends
every Schwartz test to the zero-diagonal OS-I test space. -/
theorem osiiA0LocalCutoff_mul_mem_zeroDiagonal
    (χ : SchwartzNPoint d n)
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d n → ℂ)) (CoincidenceLocus d n))
    (φ : SchwartzNPoint d n) :
    VanishesToInfiniteOrderOnCoincidence
      (SchwartzMap.smulLeftCLM ℂ (χ : NPointDomain d n → ℂ) φ) := by
  apply VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint
  refine Set.disjoint_left.2 ?_
  intro x hx hcoin
  have hxχ : x ∈ tsupport (χ : NPointDomain d n → ℂ) :=
    (SchwartzMap.tsupport_smulLeftCLM_subset
      (F := ℂ) (g := (χ : NPointDomain d n → ℂ)) (f := φ) hx).2
  exact Set.disjoint_left.mp hχ_disj hxχ hcoin

/-- The localized zero-diagonal source-current map.  This is the honest local
replacement for a nonexistent global map from all Schwartz tests to
`ZeroDiagonalSchwartz`. -/
noncomputable def osiiA0LocalCutoffZeroCLM
    (χ : SchwartzNPoint d n)
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d n → ℂ)) (CoincidenceLocus d n)) :
    SchwartzNPoint d n →L[ℂ] ZeroDiagonalSchwartz d n :=
  (SchwartzMap.smulLeftCLM ℂ (χ : NPointDomain d n → ℂ)).codRestrict
    (zeroDiagonalSubmodule d n)
    (fun φ => by
      change VanishesToInfiniteOrderOnCoincidence _
      exact osiiA0LocalCutoff_mul_mem_zeroDiagonal χ hχ_disj φ)

@[simp] theorem osiiA0LocalCutoffZeroCLM_coe
    (χ : SchwartzNPoint d n)
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d n → ℂ)) (CoincidenceLocus d n))
    (φ : SchwartzNPoint d n) :
    (osiiA0LocalCutoffZeroCLM χ hχ_disj φ).1 =
      SchwartzMap.smulLeftCLM ℂ (χ : NPointDomain d n → ℂ) φ := rfl

/-- If the cutoff is one on the topological support of the test, the localized
zero-diagonal current is exactly the original test. -/
theorem osiiA0LocalCutoffZeroCLM_apply_eq_of_one_on_tsupport
    (χ : SchwartzNPoint d n)
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d n → ℂ)) (CoincidenceLocus d n))
    (φ : SchwartzNPoint d n)
    (hχ_one : ∀ x ∈ tsupport (φ : NPointDomain d n → ℂ), χ x = 1) :
    (osiiA0LocalCutoffZeroCLM χ hχ_disj φ).1 = φ := by
  ext x
  by_cases hx : x ∈ tsupport (φ : NPointDomain d n → ℂ)
  · rw [osiiA0LocalCutoffZeroCLM_coe]
    rw [SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth]
    simp [smul_eq_mul, hχ_one x hx]
  · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [osiiA0LocalCutoffZeroCLM_coe]
    rw [SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth]
    simp [smul_eq_mul, hφx]

/-- The localized zero-diagonal current depends only on the cutoff values on
the topological support of the test.  This is the cutoff-independence step
needed before local `(A0)` Schwinger representatives can be glued. -/
theorem osiiA0LocalCutoffZeroCLM_apply_eq_of_eq_on_tsupport
    (χ₁ χ₂ : SchwartzNPoint d n)
    (hχ₁_disj :
      Disjoint (tsupport (χ₁ : NPointDomain d n → ℂ)) (CoincidenceLocus d n))
    (hχ₂_disj :
      Disjoint (tsupport (χ₂ : NPointDomain d n → ℂ)) (CoincidenceLocus d n))
    (φ : SchwartzNPoint d n)
    (hχ_eq : ∀ x ∈ tsupport (φ : NPointDomain d n → ℂ), χ₁ x = χ₂ x) :
    (osiiA0LocalCutoffZeroCLM χ₁ hχ₁_disj φ).1 =
      (osiiA0LocalCutoffZeroCLM χ₂ hχ₂_disj φ).1 := by
  ext x
  by_cases hx : x ∈ tsupport (φ : NPointDomain d n → ℂ)
  · rw [osiiA0LocalCutoffZeroCLM_coe, osiiA0LocalCutoffZeroCLM_coe]
    rw [SchwartzMap.smulLeftCLM_apply_apply χ₁.hasTemperateGrowth]
    rw [SchwartzMap.smulLeftCLM_apply_apply χ₂.hasTemperateGrowth]
    simp [smul_eq_mul, hχ_eq x hx]
  · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [osiiA0LocalCutoffZeroCLM_coe, osiiA0LocalCutoffZeroCLM_coe]
    rw [SchwartzMap.smulLeftCLM_apply_apply χ₁.hasTemperateGrowth]
    rw [SchwartzMap.smulLeftCLM_apply_apply χ₂.hasTemperateGrowth]
    simp [smul_eq_mul, hφx]

/-- The local full-Schwartz Schwinger distribution obtained by cutting off
away from the coincidence locus and then applying the OS-I Schwinger
functional. -/
noncomputable def osiiA0LocalCutoffSchwingerCLM
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzNPoint d n)
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d n → ℂ)) (CoincidenceLocus d n)) :
    SchwartzNPoint d n →L[ℂ] ℂ :=
  (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS n).comp
    (osiiA0LocalCutoffZeroCLM χ hχ_disj)

/-- Fixed-left OS-conjugated tensoring as a continuous linear map in the right
Schwartz argument. -/
noncomputable def osConjTensorProductRightCLM
    [NeZero d] {n m : ℕ} (f : SchwartzNPoint d n) :
    SchwartzNPoint d m →L[ℂ] SchwartzNPoint d (n + m) :=
  { toLinearMap :=
      { toFun := fun g => f.osConjTensorProduct g
        map_add' := by
          intro g h
          simp [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_add_right]
        map_smul' := by
          intro c g
          simp [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_smul_right] }
    cont := by
      simpa [SchwartzNPoint.osConjTensorProduct] using
        (SchwartzMap.tensorProduct_continuous_right (E := SpacetimeDim d) f.osConj :
          Continuous fun g : SchwartzNPoint d m => f.osConj.tensorProduct g) }

@[simp] theorem osConjTensorProductRightCLM_apply
    [NeZero d] {n m : ℕ} (f : SchwartzNPoint d n) (g : SchwartzNPoint d m) :
    osConjTensorProductRightCLM (d := d) (n := n) (m := m) f g =
      f.osConjTensorProduct g := rfl

/-- Local cutoff zero-current selection for a source current kernel.

If the right source-current CLM selects a coordinate-height time shift and the
cutoff is identically one on the selected two-block shell, then the localized
zero-diagonal current is exactly that shifted shell.  This is the concrete
kernel identity later used in the axis-pair side-cone handoff. -/
theorem osiiA0LocalCutoffZeroCLM_sourceCurrent_kernel_eq_of_one_on_tsupport
    [NeZero d] {n r m : ℕ}
    (χ : SchwartzNPoint d (n + r))
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d (n + r) → ℂ))
        (CoincidenceLocus d (n + r)))
    (fLeft f : SchwartzNPoint d n)
    (hf_left : fLeft = f)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (R : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] SchwartzNPoint d r)
    (τ : Fin m → ℝ)
    (q : Fin m)
    (hτq : 0 < τ q)
    (hright :
      R (section43TimeImagAxisProductKernel τ) =
        timeShiftSchwartzNPoint (d := d) (τ q) g)
    (hχ_one :
      ∀ x ∈ tsupport
        ((f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (τ q) g)) :
          NPointDomain d (n + r) → ℂ),
        χ x = 1) :
    let Z : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
        ZeroDiagonalSchwartz d (n + r) :=
      (osiiA0LocalCutoffZeroCLM χ hχ_disj).comp
        ((osConjTensorProductRightCLM (d := d) (n := n) (m := r) fLeft).comp R)
    Z (section43TimeImagAxisProductKernel τ) =
      ⟨f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (τ q) g),
        VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_timeShift_coord_of_pos
          (d := d) q f hf_ord g hg_ord τ hτq⟩ := by
  intro Z
  apply SetCoe.ext
  dsimp [Z]
  rw [hright, hf_left]
  exact
    osiiA0LocalCutoffZeroCLM_apply_eq_of_one_on_tsupport
      χ hχ_disj
      (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) (τ q) g))
      hχ_one

/-- The time-shell distribution induced by a fixed local A0 cutoff, fixed left
source, and fixed right spatial source. -/
noncomputable def osiiA0LocalCutoffTimeShellCLM
    [NeZero d] {n m : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzNPoint d (n + m))
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d (n + m) → ℂ))
        (CoincidenceLocus d (n + m)))
    (fLeft : SchwartzNPoint d n)
    (κ : Section43SpatialCompactSource d m) :
    SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ :=
  (osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj).comp
    ((osConjTensorProductRightCLM (d := d) (n := n) (m := m) fLeft).comp
      (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1))

@[simp] theorem osiiA0LocalCutoffTimeShellCLM_apply
    [NeZero d] {n m : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzNPoint d (n + m))
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d (n + m) → ℂ))
        (CoincidenceLocus d (n + m)))
    (fLeft : SchwartzNPoint d n)
    (κ : Section43SpatialCompactSource d m)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) :
    osiiA0LocalCutoffTimeShellCLM
        (d := d) OS χ hχ_disj fLeft κ φ =
      osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
        (fLeft.osConjTensorProduct
          (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1 φ)) := rfl

/-- A cutoff time-shell functional descends to the finite positive-time
quotient once the cutoff itself is supported over the positive right-time
cylinder.

This is the quotient-descent half of the OS-II `(5.7)`--`(5.8)` dense-boundary
handoff: equality in the time quotient is only equality on the closed positive
orthant, so the cutoff support must force the source current to be read there. -/
theorem osiiA0LocalCutoffTimeShellCLM_eq_of_timePositiveQuotient_eq
    [NeZero d] {n m : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzNPoint d (n + m))
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d (n + m) → ℂ))
        (CoincidenceLocus d (n + m)))
    (hχ_time :
      tsupport (χ : NPointDomain d (n + m) → ℂ) ⊆
        { x : NPointDomain d (n + m) |
          section43QTime (d := d) (n := m)
            (section43DiffCoordRealCLE d m (splitLast n m x)) ∈
              section43TimePositiveRegion m })
    (fLeft : SchwartzNPoint d n)
    (κ : Section43SpatialCompactSource d m)
    {φ ψ : SchwartzMap (Fin m → ℝ) ℂ}
    (hφψ :
      section43TimePositiveQuotientMap m φ =
        section43TimePositiveQuotientMap m ψ) :
    osiiA0LocalCutoffTimeShellCLM OS χ hχ_disj fLeft κ φ =
      osiiA0LocalCutoffTimeShellCLM OS χ hχ_disj fLeft κ ψ := by
  change
    (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS (n + m))
        (osiiA0LocalCutoffZeroCLM χ hχ_disj
          (fLeft.osConjTensorProduct
            (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1 φ))) =
      (OsterwalderSchraderAxioms.schwingerCLM (d := d) OS (n + m))
        (osiiA0LocalCutoffZeroCLM χ hχ_disj
          (fLeft.osConjTensorProduct
            (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1 ψ)))
  congr 1
  apply SetCoe.ext
  ext x
  rw [osiiA0LocalCutoffZeroCLM_coe, osiiA0LocalCutoffZeroCLM_coe]
  rw [SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth]
  rw [SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth]
  by_cases hxχ : x ∈ tsupport (χ : NPointDomain d (n + m) → ℂ)
  · have htime :
        section43QTime (d := d) (n := m)
            (section43DiffCoordRealCLE d m (splitLast n m x)) ∈
          section43TimePositiveRegion m :=
      hχ_time hxχ
    have hφψ_point :
        φ (section43QTime (d := d) (n := m)
            (section43DiffCoordRealCLE d m (splitLast n m x))) =
          ψ (section43QTime (d := d) (n := m)
            (section43DiffCoordRealCLE d m (splitLast n m x))) :=
      eqOn_region_of_section43TimePositiveQuotientMap_eq hφψ htime
    simp [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_apply,
      section43OrderedPullbackTimeSpatialTensorCLM_apply,
      section43NPointTimeSpatialTensor_apply, hφψ_point]
  · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hxχ
    simp [hχx]

/-- Same-distribution handoff for the actual local A0 cutoff time-shell CLM.

If a branch-side time-shell CLM descends to the positive-time quotient and
agrees with the local A0 cutoff time-shell CLM on compact one-sided Laplace
product representatives, then it is the same CLM.  The target descent is
discharged from the strict-positive support of the cutoff; the branch descent
and product-source equality are the genuine OS-II `(5.2)` inputs. -/
theorem osiiA0LocalCutoffTimeShellCLM_eq_of_compactLaplace_product_sources
    [NeZero d] {n m : ℕ} [Nonempty (Fin m)]
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzNPoint d (n + m))
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d (n + m) → ℂ))
        (CoincidenceLocus d (n + m)))
    (hχ_time :
      tsupport (χ : NPointDomain d (n + m) → ℂ) ⊆
        { x : NPointDomain d (n + m) |
          section43QTime (d := d) (n := m)
            (section43DiffCoordRealCLE d m (splitLast n m x)) ∈
              section43TimeStrictPositiveRegion m })
    (fLeft : SchwartzNPoint d n)
    (κ : Section43SpatialCompactSource d m)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hT_desc :
      ∀ φ ψ : SchwartzMap (Fin m → ℝ) ℂ,
        section43TimePositiveQuotientMap m φ =
          section43TimePositiveQuotientMap m ψ →
        T φ = T ψ)
    (h_on_products :
      ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
        T (section43TimeProductTensor
          (fun i : Fin m =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) =
        osiiA0LocalCutoffTimeShellCLM OS χ hχ_disj fLeft κ
          (section43TimeProductTensor
            (fun i : Fin m =>
              section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))) :
    T = osiiA0LocalCutoffTimeShellCLM OS χ hχ_disj fLeft κ := by
  refine
    section43_timeSchwartz_clm_eq_of_compactLaplace_product_sources
      (n := m) T (osiiA0LocalCutoffTimeShellCLM OS χ hχ_disj fLeft κ)
      hT_desc ?_ h_on_products
  intro φ ψ hφψ
  have hχ_time_pos :
      tsupport (χ : NPointDomain d (n + m) → ℂ) ⊆
        { x : NPointDomain d (n + m) |
          section43QTime (d := d) (n := m)
            (section43DiffCoordRealCLE d m (splitLast n m x)) ∈
              section43TimePositiveRegion m } := by
    intro x hx
    have hx_strict := hχ_time hx
    intro i
    exact le_of_lt (hx_strict i)
  exact
    osiiA0LocalCutoffTimeShellCLM_eq_of_timePositiveQuotient_eq
      OS χ hχ_disj hχ_time_pos fLeft κ hφψ

/-- On a smaller test where the cutoff is one, the local full-Schwartz
distribution recovers the original Schwinger functional value. -/
theorem osiiA0LocalCutoffSchwingerCLM_apply_eq_of_one_on_tsupport
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (χ : SchwartzNPoint d n)
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d n → ℂ)) (CoincidenceLocus d n))
    (φ : SchwartzNPoint d n)
    (hφ_zero : VanishesToInfiniteOrderOnCoincidence φ)
    (hχ_one : ∀ x ∈ tsupport (φ : NPointDomain d n → ℂ), χ x = 1) :
    osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj φ =
      OS.S n ⟨φ, hφ_zero⟩ := by
  have hz :
      osiiA0LocalCutoffZeroCLM χ hχ_disj φ =
        (⟨φ, hφ_zero⟩ : ZeroDiagonalSchwartz d n) := by
    apply SetCoe.ext
    exact osiiA0LocalCutoffZeroCLM_apply_eq_of_one_on_tsupport
      χ hχ_disj φ hχ_one
  change OS.S n (osiiA0LocalCutoffZeroCLM χ hχ_disj φ) =
    OS.S n ⟨φ, hφ_zero⟩
  rw [hz]

/-- The local full-Schwartz Schwinger distribution is independent of the
auxiliary cutoff on tests whose support sees the same cutoff values. -/
theorem osiiA0LocalCutoffSchwingerCLM_apply_eq_of_eq_on_tsupport
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (χ₁ χ₂ : SchwartzNPoint d n)
    (hχ₁_disj :
      Disjoint (tsupport (χ₁ : NPointDomain d n → ℂ)) (CoincidenceLocus d n))
    (hχ₂_disj :
      Disjoint (tsupport (χ₂ : NPointDomain d n → ℂ)) (CoincidenceLocus d n))
    (φ : SchwartzNPoint d n)
    (hχ_eq : ∀ x ∈ tsupport (φ : NPointDomain d n → ℂ), χ₁ x = χ₂ x) :
    osiiA0LocalCutoffSchwingerCLM OS χ₁ hχ₁_disj φ =
      osiiA0LocalCutoffSchwingerCLM OS χ₂ hχ₂_disj φ := by
  have hz :
      osiiA0LocalCutoffZeroCLM χ₁ hχ₁_disj φ =
        osiiA0LocalCutoffZeroCLM χ₂ hχ₂_disj φ := by
    apply SetCoe.ext
    exact osiiA0LocalCutoffZeroCLM_apply_eq_of_eq_on_tsupport
      χ₁ χ₂ hχ₁_disj hχ₂_disj φ hχ_eq
  change OS.S n (osiiA0LocalCutoffZeroCLM χ₁ hχ₁_disj φ) =
    OS.S n (osiiA0LocalCutoffZeroCLM χ₂ hχ₂_disj φ)
  rw [hz]

/-- Local representative transport between equal cutoffs on a carrier.

If two auxiliary cutoffs agree throughout the carrier of a local A0
representative, then a kernel representing the first localized Schwinger
distribution also represents the second one on that carrier.  This is the
cutoff-independence form needed when Lemma 5.1 branches are moved between
overlapping local cutoff windows. -/
theorem osiiA0LocalCutoffSchwingerCLM_representsDistributionOn_of_cutoff_eqOn
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (χ₁ χ₂ : SchwartzNPoint d n)
    (hχ₁_disj :
      Disjoint (tsupport (χ₁ : NPointDomain d n → ℂ)) (CoincidenceLocus d n))
    (hχ₂_disj :
      Disjoint (tsupport (χ₂ : NPointDomain d n → ℂ)) (CoincidenceLocus d n))
    (H : NPointDomain d n → ℂ)
    (U : Set (NPointDomain d n))
    (hχ_eq : Set.EqOn
      (χ₁ : NPointDomain d n → ℂ) (χ₂ : NPointDomain d n → ℂ) U)
    (hRep :
      SCV.RepresentsDistributionOn
        (osiiA0LocalCutoffSchwingerCLM OS χ₁ hχ₁_disj) H U) :
    SCV.RepresentsDistributionOn
      (osiiA0LocalCutoffSchwingerCLM OS χ₂ hχ₂_disj) H U := by
  intro φ hφU
  have hcut :
      osiiA0LocalCutoffSchwingerCLM OS χ₂ hχ₂_disj φ =
        osiiA0LocalCutoffSchwingerCLM OS χ₁ hχ₁_disj φ := by
    exact
      (osiiA0LocalCutoffSchwingerCLM_apply_eq_of_eq_on_tsupport
        OS χ₂ χ₁ hχ₂_disj hχ₁_disj φ
        (fun x hx => (hχ_eq (hφU.2 hx)).symm))
  calc
    osiiA0LocalCutoffSchwingerCLM OS χ₂ hχ₂_disj φ
        = osiiA0LocalCutoffSchwingerCLM OS χ₁ hχ₁_disj φ := hcut
    _ = ∫ x : NPointDomain d n, H x * φ x := hRep φ hφU

/-- In particular, two cutoffs which are both one on the test support give the
same local Schwinger distribution value. -/
theorem osiiA0LocalCutoffSchwingerCLM_apply_eq_of_both_one_on_tsupport
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (χ₁ χ₂ : SchwartzNPoint d n)
    (hχ₁_disj :
      Disjoint (tsupport (χ₁ : NPointDomain d n → ℂ)) (CoincidenceLocus d n))
    (hχ₂_disj :
      Disjoint (tsupport (χ₂ : NPointDomain d n → ℂ)) (CoincidenceLocus d n))
    (φ : SchwartzNPoint d n)
    (hχ₁_one : ∀ x ∈ tsupport (φ : NPointDomain d n → ℂ), χ₁ x = 1)
    (hχ₂_one : ∀ x ∈ tsupport (φ : NPointDomain d n → ℂ), χ₂ x = 1) :
    osiiA0LocalCutoffSchwingerCLM OS χ₁ hχ₁_disj φ =
      osiiA0LocalCutoffSchwingerCLM OS χ₂ hχ₂_disj φ := by
  exact osiiA0LocalCutoffSchwingerCLM_apply_eq_of_eq_on_tsupport
    OS χ₁ χ₂ hχ₁_disj hχ₂_disj φ
    (fun x hx => by rw [hχ₁_one x hx, hχ₂_one x hx])

/-- A compact subset of an open `NPointDomain` set admits a Schwartz cutoff
equal to one on the compact set and whose topological support lies in the open
set.  This is the cutoff-selection step for local `(A0)` distributions. -/
theorem osiiA0_exists_schwartzNPoint_cutoff_eq_one_on_compact_subset_open
    {K U : Set (NPointDomain d n)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : SchwartzNPoint d n,
      (∀ x ∈ K, χ x = 1) ∧
      tsupport (χ : NPointDomain d n → ℂ) ⊆ U := by
  classical
  let e : NPointDomain d n ≃L[ℝ] (Fin (n * (d + 1)) → ℝ) :=
    flattenCLEquivReal n (d + 1)
  let Kflat : Set (Fin (n * (d + 1)) → ℝ) := e '' K
  let Uflat : Set (Fin (n * (d + 1)) → ℝ) := e '' U
  have hKflat : IsCompact Kflat := hK.image e.continuous
  have hUflat : IsOpen Uflat := by
    simpa [Uflat] using e.toHomeomorph.isOpenMap U hU
  have hKUflat : Kflat ⊆ Uflat := by
    intro y hy
    rcases hy with ⟨x, hxK, rfl⟩
    exact ⟨x, hKU hxK, rfl⟩
  obtain ⟨χflat, hχflat_one, hχflat_sub⟩ :=
    SCV.exists_schwartz_cutoff_eq_one_on_compact_subset_open
      (m := n * (d + 1)) hKflat hUflat hKUflat
  let χ : SchwartzNPoint d n :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e χflat
  refine ⟨χ, ?_, ?_⟩
  · intro x hxK
    change χflat (e x) = 1
    exact hχflat_one (e x) ⟨x, hxK, rfl⟩
  · have hχ_tsupport :
        tsupport (χ : NPointDomain d n → ℂ) =
          e.toHomeomorph ⁻¹'
            tsupport (χflat : (Fin (n * (d + 1)) → ℝ) → ℂ) := by
      simpa [χ, e, SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
        (tsupport_comp_eq_preimage
          (g := (χflat : (Fin (n * (d + 1)) → ℝ) → ℂ)) e.toHomeomorph)
    intro x hx
    have hex : e x ∈ Uflat := hχflat_sub (by
      simpa [hχ_tsupport] using hx)
    rcases hex with ⟨y, hyU, hy_eq⟩
    have hyx : y = x := e.injective hy_eq
    simpa [hyx] using hyU

/-- For every compactly supported test whose topological support avoids the
coincidence locus, the OS Schwinger functional has a local full-Schwartz
continuous-linear representative obtained by a cutoff. -/
theorem exists_osiiA0LocalCutoffSchwingerCLM_for_compact_disjoint_test
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (φ : SchwartzNPoint d n)
    (hφ_comp : HasCompactSupport (φ : NPointDomain d n → ℂ))
    (hφ_disj :
      Disjoint (tsupport (φ : NPointDomain d n → ℂ)) (CoincidenceLocus d n)) :
    ∃ (χ : SchwartzNPoint d n)
      (hχ_disj :
        Disjoint (tsupport (χ : NPointDomain d n → ℂ)) (CoincidenceLocus d n)),
      (∀ x ∈ tsupport (φ : NPointDomain d n → ℂ), χ x = 1) ∧
      osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj φ =
        OS.S n ⟨φ,
          VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint φ hφ_disj⟩ := by
  let U : Set (NPointDomain d n) := (CoincidenceLocus d n)ᶜ
  have hU_open : IsOpen U := by
    simpa [U] using (isClosed_CoincidenceLocus (d := d) (n := n)).isOpen_compl
  have hφ_sub : tsupport (φ : NPointDomain d n → ℂ) ⊆ U := by
    intro x hx hcoin
    exact Set.disjoint_left.mp hφ_disj hx hcoin
  obtain ⟨χ, hχ_one, hχ_sub⟩ :=
    osiiA0_exists_schwartzNPoint_cutoff_eq_one_on_compact_subset_open
      (d := d) (n := n) (K := tsupport (φ : NPointDomain d n → ℂ)) (U := U)
      hφ_comp.isCompact hU_open hφ_sub
  have hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d n → ℂ)) (CoincidenceLocus d n) := by
    refine Set.disjoint_left.2 ?_
    intro x hx hcoin
    exact hχ_sub hx hcoin
  refine ⟨χ, hχ_disj, hχ_one, ?_⟩
  exact
    osiiA0LocalCutoffSchwingerCLM_apply_eq_of_one_on_tsupport
      OS χ hχ_disj φ
      (VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint φ hφ_disj)
      hχ_one

/-- The ordered pullback of a compact Section 4.3 time/spatial product source
has compact support.  This is the support-control input needed to apply a
local `(A0)` cutoff distribution to concrete product currents without
importing the downstream boundary-value carrier. -/
theorem osiiA0_hasCompactSupport_section43OrderedPullbackTimeSpatialTensorCLM
    [NeZero d]
    (g : Section43CompactStrictPositiveTimeSource n)
    (κ : Section43SpatialCompactSource d n) :
    HasCompactSupport
      (((section43OrderedPullbackTimeSpatialTensorCLM d n κ.1 g.f :
        SchwartzNPoint d n) : NPointDomain d n → ℂ)) := by
  let e : NPointDomain d n ≃L[ℝ] NPointDomain d n :=
    section43DiffCoordRealCLE d n
  let ψ : SchwartzNPoint d n :=
    section43NPointTimeSpatialTensor d n g.f κ.1
  have hψ_comp : IsCompact (tsupport (ψ : NPointDomain d n → ℂ)) := by
    simpa [ψ, HasCompactSupport] using
      (section43TimeSpatialProductSource d n g κ).compact
  have htsupport :
      tsupport
          (((section43OrderedPullbackTimeSpatialTensorCLM d n κ.1 g.f :
            SchwartzNPoint d n) : NPointDomain d n → ℂ)) =
        e.toHomeomorph ⁻¹' tsupport (ψ : NPointDomain d n → ℂ) := by
    change
      tsupport
          (((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e ψ :
            SchwartzNPoint d n) : NPointDomain d n → ℂ)) =
        e.toHomeomorph ⁻¹' tsupport (ψ : NPointDomain d n → ℂ)
    simpa [SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
      (tsupport_comp_eq_preimage
        (g := (ψ : NPointDomain d n → ℂ)) e.toHomeomorph)
  have hpreimage :
      e.toHomeomorph ⁻¹' tsupport (ψ : NPointDomain d n → ℂ) =
        e.toHomeomorph.symm '' tsupport (ψ : NPointDomain d n → ℂ) := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, by simp [e]⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [e] using hy
  have hcompact_preimage :
      IsCompact (e.toHomeomorph ⁻¹' tsupport (ψ : NPointDomain d n → ℂ)) := by
    rw [hpreimage]
    exact hψ_comp.image e.toHomeomorph.symm.continuous
  change IsCompact
    (tsupport
      (((section43OrderedPullbackTimeSpatialTensorCLM d n κ.1 g.f :
        SchwartzNPoint d n) : NPointDomain d n → ℂ)))
  rw [htsupport]
  exact hcompact_preimage

/-- The ordered pullback of a compact time test and compact spatial source has
compact support, without assuming the time support is positive. -/
theorem osiiA0_hasCompactSupport_section43OrderedPullbackTimeSpatialTensorCLM_of_compact
    [NeZero d]
    (φ : SchwartzMap (Fin n → ℝ) ℂ)
    (hφ_comp : HasCompactSupport (φ : (Fin n → ℝ) → ℂ))
    (κ : Section43SpatialCompactSource d n) :
    HasCompactSupport
      (((section43OrderedPullbackTimeSpatialTensorCLM d n κ.1 φ :
        SchwartzNPoint d n) : NPointDomain d n → ℂ)) := by
  let e : NPointDomain d n ≃L[ℝ] NPointDomain d n :=
    section43DiffCoordRealCLE d n
  let ψ : SchwartzNPoint d n :=
    section43NPointTimeSpatialTensor d n φ κ.1
  have hψ_comp : IsCompact (tsupport (ψ : NPointDomain d n → ℂ)) := by
    simpa [ψ, HasCompactSupport] using
      hasCompactSupport_section43NPointTimeSpatialTensor
        d n φ κ.1 hφ_comp κ.2
  have htsupport :
      tsupport
          (((section43OrderedPullbackTimeSpatialTensorCLM d n κ.1 φ :
            SchwartzNPoint d n) : NPointDomain d n → ℂ)) =
        e.toHomeomorph ⁻¹' tsupport (ψ : NPointDomain d n → ℂ) := by
    change
      tsupport
          (((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e ψ :
            SchwartzNPoint d n) : NPointDomain d n → ℂ)) =
        e.toHomeomorph ⁻¹' tsupport (ψ : NPointDomain d n → ℂ)
    simpa [SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
      (tsupport_comp_eq_preimage
        (g := (ψ : NPointDomain d n → ℂ)) e.toHomeomorph)
  have hpreimage :
      e.toHomeomorph ⁻¹' tsupport (ψ : NPointDomain d n → ℂ) =
        e.toHomeomorph.symm '' tsupport (ψ : NPointDomain d n → ℂ) := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, by simp [e]⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [e] using hy
  have hcompact_preimage :
      IsCompact (e.toHomeomorph ⁻¹' tsupport (ψ : NPointDomain d n → ℂ)) := by
    rw [hpreimage]
    exact hψ_comp.image e.toHomeomorph.symm.continuous
  change IsCompact
    (tsupport
      (((section43OrderedPullbackTimeSpatialTensorCLM d n κ.1 φ :
        SchwartzNPoint d n) : NPointDomain d n → ℂ)))
  rw [htsupport]
  exact hcompact_preimage

/-- Product-time specialization of compact support for the ordered-pullback
source current. -/
theorem osiiA0_hasCompactSupport_section43OrderedPullbackTimeSpatialTensorCLM_product
    [NeZero d]
    (gs : Fin n → Section43CompactPositiveTimeSource1D)
    (κ : Section43SpatialCompactSource d n) :
    HasCompactSupport
      (((section43OrderedPullbackTimeSpatialTensorCLM d n κ.1
        (section43TimeProductSource gs).f : SchwartzNPoint d n) :
        NPointDomain d n → ℂ)) := by
  exact
    osiiA0_hasCompactSupport_section43OrderedPullbackTimeSpatialTensorCLM
      (d := d) (n := n) (section43TimeProductSource gs) κ

/-- Product-source specialization of the local `(A0)` cutoff distribution:
compact strict-positive Section 4.3 time sources and compact spatial sources
give a full-Schwartz local Schwinger representative which evaluates to the
original OS Schwinger scalar on the ordered-pullback product current. -/
theorem exists_osiiA0LocalCutoffSchwingerCLM_for_section43ProductSource
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (gs : Fin n → Section43CompactPositiveTimeSource1D)
    (κ : Section43SpatialCompactSource d n) :
    ∃ (χ : SchwartzNPoint d n)
      (hχ_disj :
        Disjoint (tsupport (χ : NPointDomain d n → ℂ)) (CoincidenceLocus d n)),
      (∀ x ∈ tsupport
          (((section43OrderedPullbackTimeSpatialTensorCLM d n κ.1
            (section43TimeProductSource gs).f : SchwartzNPoint d n) :
              NPointDomain d n → ℂ)), χ x = 1) ∧
      osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
          (section43OrderedPullbackTimeSpatialTensorCLM d n κ.1
            (section43TimeProductSource gs).f) =
        OS.S n
          ⟨section43OrderedPullbackTimeSpatialTensorCLM d n κ.1
              (section43TimeProductSource gs).f,
            section43OrderedPullbackTimeSpatialTensorCLM_mem_zeroDiagonal_of_tsupport_strictPositive
              d n κ.1 (section43TimeProductSource gs).f
              (section43TimeProductSource gs).positive⟩ := by
  let φ : SchwartzNPoint d n :=
    section43OrderedPullbackTimeSpatialTensorCLM d n κ.1
      (section43TimeProductSource gs).f
  have hφ_comp : HasCompactSupport (φ : NPointDomain d n → ℂ) := by
    simpa [φ] using
      osiiA0_hasCompactSupport_section43OrderedPullbackTimeSpatialTensorCLM_product
        (d := d) (n := n) gs κ
  have hφ_ord :
      tsupport (φ : NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n := by
    simpa [φ] using
      section43OrderedPullbackTimeSpatialTensorCLM_tsupport_subset_orderedPositive_of_tsupport_strictPositive
        d n κ.1 (section43TimeProductSource gs).f
        (section43TimeProductSource gs).positive
  have hφ_disj :
      Disjoint (tsupport (φ : NPointDomain d n → ℂ)) (CoincidenceLocus d n) := by
    refine Set.disjoint_left.2 ?_
    intro x hx hcoin
    exact (not_mem_CoincidenceLocus_of_mem_OrderedPositiveTimeRegion
      (hφ_ord hx)) hcoin
  rcases
    exists_osiiA0LocalCutoffSchwingerCLM_for_compact_disjoint_test
      (d := d) (n := n) OS φ hφ_comp hφ_disj with
    ⟨χ, hχ_disj, hχ_one, hχ_apply⟩
  refine ⟨χ, hχ_disj, ?_, ?_⟩
  · simpa [φ] using hχ_one
  · have hzero :
        (⟨φ, VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint
            φ hφ_disj⟩ : ZeroDiagonalSchwartz d n) =
          ⟨φ,
            section43OrderedPullbackTimeSpatialTensorCLM_mem_zeroDiagonal_of_tsupport_strictPositive
              d n κ.1 (section43TimeProductSource gs).f
              (section43TimeProductSource gs).positive⟩ := by
      apply Subtype.ext
      rfl
    calc
      osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
          (section43OrderedPullbackTimeSpatialTensorCLM d n κ.1
            (section43TimeProductSource gs).f)
          = osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj φ := by
              rfl
      _ = OS.S n
            ⟨φ, VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint
              φ hφ_disj⟩ := hχ_apply
      _ = OS.S n
            ⟨φ,
              section43OrderedPullbackTimeSpatialTensorCLM_mem_zeroDiagonal_of_tsupport_strictPositive
                d n κ.1 (section43TimeProductSource gs).f
                (section43TimeProductSource gs).positive⟩ := by
              rw [hzero]
      _ = OS.S n
          ⟨section43OrderedPullbackTimeSpatialTensorCLM d n κ.1
              (section43TimeProductSource gs).f,
            section43OrderedPullbackTimeSpatialTensorCLM_mem_zeroDiagonal_of_tsupport_strictPositive
              d n κ.1 (section43TimeProductSource gs).f
              (section43TimeProductSource gs).positive⟩ := by
          rfl

private def osiiA0_timeReflectionNHomeomorph {d n : ℕ} [NeZero d] :
    NPointDomain d n ≃ₜ NPointDomain d n where
  toFun := timeReflectionN d
  invFun := timeReflectionN d
  left_inv x := by
    funext i
    exact timeReflection_timeReflection d (x i)
  right_inv x := by
    funext i
    exact timeReflection_timeReflection d (x i)
  continuous_toFun := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro μ
    by_cases hμ : μ = 0
    · subst hμ
      simpa [timeReflectionN, timeReflection] using
        ((((continuous_apply 0 : Continuous fun y : SpacetimeDim d => y 0).comp
            (continuous_apply i : Continuous fun x : NPointDomain d n => x i))).neg :
          Continuous fun x : NPointDomain d n => -x i 0)
    · simpa [timeReflectionN, timeReflection, hμ] using
        ((continuous_apply μ : Continuous fun y : SpacetimeDim d => y μ).comp
          (continuous_apply i : Continuous fun x : NPointDomain d n => x i) :
          Continuous fun x : NPointDomain d n => x i μ)
  continuous_invFun := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro μ
    by_cases hμ : μ = 0
    · subst hμ
      simpa [timeReflectionN, timeReflection] using
        ((((continuous_apply 0 : Continuous fun y : SpacetimeDim d => y 0).comp
            (continuous_apply i : Continuous fun x : NPointDomain d n => x i))).neg :
          Continuous fun x : NPointDomain d n => -x i 0)
    · simpa [timeReflectionN, timeReflection, hμ] using
        ((continuous_apply μ : Continuous fun y : SpacetimeDim d => y μ).comp
          (continuous_apply i : Continuous fun x : NPointDomain d n => x i) :
          Continuous fun x : NPointDomain d n => x i μ)

theorem osiiA0_osConj_hasCompactSupport
    [NeZero d]
    {n : ℕ} (f : SchwartzNPoint d n)
    (hf_comp : HasCompactSupport (f : NPointDomain d n → ℂ)) :
    HasCompactSupport
      (((f.osConj : SchwartzNPoint d n) : NPointDomain d n → ℂ)) := by
  have hreflect :
      HasCompactSupport (fun x : NPointDomain d n =>
        (f : NPointDomain d n → ℂ) (timeReflectionN d x)) := by
    simpa using
      hf_comp.comp_homeomorph
        (osiiA0_timeReflectionNHomeomorph (d := d) (n := n))
  simpa [SchwartzNPoint.osConj_apply] using
    hreflect.comp_left (g := starRingEnd ℂ) (map_zero _)

private theorem osiiA0_prod_mul_hasCompactSupport
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [R1Space X] [R1Space Y]
    {f : X → ℂ} {g : Y → ℂ}
    (hf_comp : HasCompactSupport f) (hg_comp : HasCompactSupport g) :
    HasCompactSupport (fun p : X × Y => f p.1 * g p.2) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (hf_comp.isCompact.prod hg_comp.isCompact) ?_
  intro p hp
  change p.1 ∈ tsupport f ∧ p.2 ∈ tsupport g
  have hmul : f p.1 * g p.2 ≠ 0 := by
    simpa [Function.mem_support] using hp
  constructor
  · have hf_ne : f p.1 ≠ 0 := by
      intro hf_zero
      exact hmul (by simp [hf_zero])
    exact subset_tsupport f (by simpa [Function.mem_support] using hf_ne)
  · have hg_ne : g p.2 ≠ 0 := by
      intro hg_zero
      exact hmul (by simp [hg_zero])
    exact subset_tsupport g (by simpa [Function.mem_support] using hg_ne)

private def osiiA0_nPointAppendLinearEquiv (d n m : ℕ) :
    (NPointDomain d n × NPointDomain d m) ≃ₗ[ℝ] NPointDomain d (n + m) :=
  { Fin.appendEquiv n m with
    map_add' := by
      intro x y
      apply (Fin.appendEquiv n m).symm.injective
      ext i μ <;> simp [Fin.appendEquiv]
    map_smul' := by
      intro c x
      apply (Fin.appendEquiv n m).symm.injective
      ext i μ <;> simp [Fin.appendEquiv] }

private noncomputable def osiiA0_nPointAppendCLE (d n m : ℕ) :
    (NPointDomain d n × NPointDomain d m) ≃L[ℝ] NPointDomain d (n + m) :=
  (osiiA0_nPointAppendLinearEquiv d n m).toContinuousLinearEquiv

@[simp] private theorem osiiA0_nPointAppendCLE_apply_head
    (d n m : ℕ) (p : NPointDomain d n × NPointDomain d m) (i : Fin n) :
    osiiA0_nPointAppendCLE d n m p (Fin.castAdd m i) = p.1 i := by
  simp [osiiA0_nPointAppendCLE, osiiA0_nPointAppendLinearEquiv]

@[simp] private theorem osiiA0_nPointAppendCLE_apply_tail
    (d n m : ℕ) (p : NPointDomain d n × NPointDomain d m) (i : Fin m) :
    osiiA0_nPointAppendCLE d n m p (Fin.natAdd n i) = p.2 i := by
  simp [osiiA0_nPointAppendCLE, osiiA0_nPointAppendLinearEquiv]

private theorem osiiA0_nPointAppendCLE_symm_fst
    (d n m : ℕ) (x : NPointDomain d (n + m)) :
    ((osiiA0_nPointAppendCLE d n m).symm x).1 = splitFirst n m x := by
  ext i μ
  let e := osiiA0_nPointAppendCLE d n m
  have h := congrFun (ContinuousLinearEquiv.apply_symm_apply e x) (Fin.castAdd m i)
  have hμ := congrFun h μ
  simpa [e, splitFirst] using hμ

private theorem osiiA0_nPointAppendCLE_symm_snd
    (d n m : ℕ) (x : NPointDomain d (n + m)) :
    ((osiiA0_nPointAppendCLE d n m).symm x).2 = splitLast n m x := by
  ext i μ
  let e := osiiA0_nPointAppendCLE d n m
  have h := congrFun (ContinuousLinearEquiv.apply_symm_apply e x) (Fin.natAdd n i)
  have hμ := congrFun h μ
  simpa [e, splitLast] using hμ

/-- Compact support is preserved by the OS-conjugated tensor product when both
ordered source blocks are compactly supported. -/
theorem osiiA0_hasCompactSupport_osConjTensorProduct
    [NeZero d]
    {n m : ℕ} (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (hf_comp : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hg_comp : HasCompactSupport (g : NPointDomain d m → ℂ)) :
    HasCompactSupport
      (((f.osConjTensorProduct g : SchwartzNPoint d (n + m)) :
        NPointDomain d (n + m) → ℂ)) := by
  let H : NPointDomain d n × NPointDomain d m → ℂ := fun p =>
    ((f.osConj : SchwartzNPoint d n) : NPointDomain d n → ℂ) p.1 *
      (g : NPointDomain d m → ℂ) p.2
  have hH_comp : HasCompactSupport H :=
    osiiA0_prod_mul_hasCompactSupport
      (osiiA0_osConj_hasCompactSupport (d := d) f hf_comp) hg_comp
  have hcomp :
      HasCompactSupport
        (H ∘ ((osiiA0_nPointAppendCLE d n m).symm.toHomeomorph :
          NPointDomain d (n + m) ≃ₜ
            NPointDomain d n × NPointDomain d m)) :=
    hH_comp.comp_homeomorph (osiiA0_nPointAppendCLE d n m).symm.toHomeomorph
  simpa [H, Function.comp, SchwartzNPoint.osConjTensorProduct,
    SchwartzMap.tensorProduct_apply,
    osiiA0_nPointAppendCLE_symm_fst,
    osiiA0_nPointAppendCLE_symm_snd] using hcomp

private theorem osiiA0_osConj_tsupport_subset_orderedNegative
    [NeZero d]
    {n : ℕ} (f : SchwartzNPoint d n)
    (hf : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n) :
    tsupport ((f.osConj : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      OrderedNegativeTimeRegion d n := by
  intro x hx i
  have hxpre :
      timeReflectionN d x ∈ tsupport (f : NPointDomain d n → ℂ) := by
    exact
      tsupport_comp_subset_preimage
        (f : NPointDomain d n → ℂ)
        (osiiA0_timeReflectionNHomeomorph (d := d) (n := n)).continuous_toFun
        ((tsupport_comp_subset (g := starRingEnd ℂ) (map_zero _)
          (fun y : NPointDomain d n => f (timeReflectionN d y))) hx)
  have hpos := hf hxpre
  constructor
  · have : 0 < timeReflectionN d x i 0 := (hpos i).1
    simpa [timeReflectionN, timeReflection] using this
  · intro j hij
    have : timeReflectionN d x i 0 < timeReflectionN d x j 0 := (hpos i).2 j hij
    simpa [timeReflectionN, timeReflection] using this

private theorem osiiA0_nPointAppendCLE_not_mem_coincidence_of_neg_pos
    [NeZero d]
    {n m : ℕ} (p : NPointDomain d n × NPointDomain d m)
    (hneg : p.1 ∈ OrderedNegativeTimeRegion d n)
    (hpos : p.2 ∈ OrderedPositiveTimeRegion d m) :
    osiiA0_nPointAppendCLE d n m p ∉ CoincidenceLocus d (n + m) := by
  intro hcoin
  rcases hcoin with ⟨i, j, hij, hijEq⟩
  by_cases hi : i.1 < n
  · by_cases hj : j.1 < n
    · let i' : Fin n := ⟨i.1, hi⟩
      let j' : Fin n := ⟨j.1, hj⟩
      have hi_cast : Fin.castAdd m i' = i := by
        ext
        simp [i']
      have hj_cast : Fin.castAdd m j' = j := by
        ext
        simp [j']
      have hij' : i' ≠ j' := by
        intro hij'
        apply hij
        simpa [hi_cast, hj_cast] using congrArg (fun t : Fin n => Fin.castAdd m t) hij'
      have hEq : p.1 i' = p.1 j' := by
        ext μ
        have hμ := congrArg (fun y : SpacetimeDim d => y μ) hijEq
        change osiiA0_nPointAppendCLE d n m p i μ =
          osiiA0_nPointAppendCLE d n m p j μ at hμ
        rw [← hi_cast, ← hj_cast] at hμ
        simpa using hμ
      exact
        (not_mem_CoincidenceLocus_of_mem_OrderedNegativeTimeRegion hneg)
          ⟨i', j', hij', hEq⟩
    · let i' : Fin n := ⟨i.1, hi⟩
      let j' : Fin m := ⟨j.1 - n, by omega⟩
      have hi_cast : Fin.castAdd m i' = i := by
        ext
        simp [i']
      have hj_cast : Fin.natAdd n j' = j := by
        ext
        simp [j']
        omega
      have hEq0 : p.1 i' 0 = p.2 j' 0 := by
        have h0 := congrArg (fun y : SpacetimeDim d => y 0) hijEq
        change osiiA0_nPointAppendCLE d n m p i 0 =
          osiiA0_nPointAppendCLE d n m p j 0 at h0
        rw [← hi_cast, ← hj_cast] at h0
        simpa using h0
      have hlt : p.1 i' 0 < 0 := (hneg i').1
      have hgt : 0 < p.2 j' 0 := (hpos j').1
      linarith
  · by_cases hj : j.1 < n
    · let i' : Fin m := ⟨i.1 - n, by omega⟩
      let j' : Fin n := ⟨j.1, hj⟩
      have hi_cast : Fin.natAdd n i' = i := by
        ext
        simp [i']
        omega
      have hj_cast : Fin.castAdd m j' = j := by
        ext
        simp [j']
      have hEq0 : p.2 i' 0 = p.1 j' 0 := by
        have h0 := congrArg (fun y : SpacetimeDim d => y 0) hijEq
        change osiiA0_nPointAppendCLE d n m p i 0 =
          osiiA0_nPointAppendCLE d n m p j 0 at h0
        rw [← hi_cast, ← hj_cast] at h0
        simpa using h0
      have hgt : 0 < p.2 i' 0 := (hpos i').1
      have hlt : p.1 j' 0 < 0 := (hneg j').1
      linarith
    · let i' : Fin m := ⟨i.1 - n, by omega⟩
      let j' : Fin m := ⟨j.1 - n, by omega⟩
      have hi_cast : Fin.natAdd n i' = i := by
        ext
        simp [i']
        omega
      have hj_cast : Fin.natAdd n j' = j := by
        ext
        simp [j']
        omega
      have hij' : i' ≠ j' := by
        intro hij'
        apply hij
        simpa [hi_cast, hj_cast] using congrArg (fun t : Fin m => Fin.natAdd n t) hij'
      have hEq : p.2 i' = p.2 j' := by
        ext μ
        have hμ := congrArg (fun y : SpacetimeDim d => y μ) hijEq
        change osiiA0_nPointAppendCLE d n m p i μ =
          osiiA0_nPointAppendCLE d n m p j μ at hμ
        rw [← hi_cast, ← hj_cast] at hμ
        simpa using hμ
      exact
        (not_mem_CoincidenceLocus_of_mem_OrderedPositiveTimeRegion hpos)
          ⟨i', j', hij', hEq⟩

/-- Ordered positive-time support of the two source blocks keeps the
OS-conjugated tensor product away from the coincidence locus. -/
theorem osiiA0_osConjTensorProduct_tsupport_disjoint_coincidence_of_ordered
    [NeZero d]
    {n m : ℕ} (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (hf : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (hg : tsupport (g : NPointDomain d m → ℂ) ⊆
      OrderedPositiveTimeRegion d m) :
    Disjoint
      (tsupport (((f.osConjTensorProduct g : SchwartzNPoint d (n + m)) :
        NPointDomain d (n + m) → ℂ)))
      (CoincidenceLocus d (n + m)) := by
  let A : Set (NPointDomain d (n + m)) :=
    { x | splitFirst n m x ∈ OrderedNegativeTimeRegion d n }
  let B : Set (NPointDomain d (n + m)) :=
    { x | splitLast n m x ∈ OrderedPositiveTimeRegion d m }
  have hosConj :
      tsupport ((f.osConj : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        OrderedNegativeTimeRegion d n := by
    exact osiiA0_osConj_tsupport_subset_orderedNegative (d := d) f hf
  have hA :
      tsupport (fun x : NPointDomain d (n + m) => f.osConj (splitFirst n m x)) ⊆ A := by
    intro x hx
    exact hosConj <|
      tsupport_comp_subset_preimage
        ((f.osConj : SchwartzNPoint d n) : NPointDomain d n → ℂ)
        (splitFirst_continuousLinear n m) hx
  have hB :
      tsupport (fun x : NPointDomain d (n + m) => g (splitLast n m x)) ⊆ B := by
    intro x hx
    exact hg <|
      tsupport_comp_subset_preimage
        (g : NPointDomain d m → ℂ)
        (splitLast_continuousLinear n m) hx
  have hsupport :
      tsupport (((f.osConjTensorProduct g : SchwartzNPoint d (n + m)) :
          NPointDomain d (n + m) → ℂ)) ⊆ A ∩ B := by
    intro x hx
    have hxprod :
        x ∈ tsupport (fun y : NPointDomain d (n + m) =>
          f.osConj (splitFirst n m y) * g (splitLast n m y)) := by
      simpa [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_apply] using hx
    refine ⟨hA ((tsupport_mul_subset_left (f := fun y : NPointDomain d (n + m) =>
      f.osConj (splitFirst n m y)) (g := fun y : NPointDomain d (n + m) =>
      g (splitLast n m y))) hxprod), ?_⟩
    exact hB ((tsupport_mul_subset_right (f := fun y : NPointDomain d (n + m) =>
      f.osConj (splitFirst n m y)) (g := fun y : NPointDomain d (n + m) =>
      g (splitLast n m y))) hxprod)
  have hdisj : Disjoint (A ∩ B) (CoincidenceLocus d (n + m)) := by
    refine Set.disjoint_left.mpr ?_
    intro x hxAB hxcoin
    rcases hxAB with ⟨hxA, hxB⟩
    rcases hxcoin with ⟨i, j, hij, hijEq⟩
    by_cases hi : i.1 < n
    · by_cases hj : j.1 < n
      · let i' : Fin n := ⟨i.1, hi⟩
        let j' : Fin n := ⟨j.1, hj⟩
        have hi_cast : Fin.castAdd m i' = i := by
          ext
          simp [i']
        have hj_cast : Fin.castAdd m j' = j := by
          ext
          simp [j']
        have hEq0 : splitFirst n m x i' 0 = splitFirst n m x j' 0 := by
          simpa [splitFirst, hi_cast, hj_cast] using
            congrArg (fun y : SpacetimeDim d => y 0) hijEq
        have hij' : i' ≠ j' := by
          intro hij'
          apply hij
          simpa [hi_cast, hj_cast] using congrArg (fun t : Fin n => Fin.castAdd m t) hij'
        rcases lt_or_gt_of_ne hij' with hij'_lt | hij'_gt
        · have hlt : splitFirst n m x j' 0 < splitFirst n m x i' 0 := (hxA i').2 j' hij'_lt
          exact (lt_irrefl (splitFirst n m x j' 0)) (hEq0 ▸ hlt)
        · have hlt : splitFirst n m x i' 0 < splitFirst n m x j' 0 := (hxA j').2 i' hij'_gt
          exact (lt_irrefl (splitFirst n m x i' 0)) (hEq0.symm ▸ hlt)
      · let i' : Fin n := ⟨i.1, hi⟩
        let j' : Fin m := ⟨j.1 - n, by omega⟩
        have hi_cast : Fin.castAdd m i' = i := by
          ext
          simp [i']
        have hj_cast : Fin.natAdd n j' = j := by
          ext
          simp [j']
          omega
        have hneg : splitFirst n m x i' 0 < 0 := (hxA i').1
        have hpos : 0 < splitLast n m x j' 0 := (hxB j').1
        have hEq0 : splitFirst n m x i' 0 = splitLast n m x j' 0 := by
          simpa [splitFirst, splitLast, hi_cast, hj_cast] using
            congrArg (fun y : SpacetimeDim d => y 0) hijEq
        linarith
    · by_cases hj : j.1 < n
      · let i' : Fin m := ⟨i.1 - n, by omega⟩
        let j' : Fin n := ⟨j.1, hj⟩
        have hi_cast : Fin.natAdd n i' = i := by
          ext
          simp [i']
          omega
        have hj_cast : Fin.castAdd m j' = j := by
          ext
          simp [j']
        have hpos : 0 < splitLast n m x i' 0 := (hxB i').1
        have hneg : splitFirst n m x j' 0 < 0 := (hxA j').1
        have hEq0 : splitLast n m x i' 0 = splitFirst n m x j' 0 := by
          simpa [splitFirst, splitLast, hi_cast, hj_cast] using
            congrArg (fun y : SpacetimeDim d => y 0) hijEq
        linarith
      · let i' : Fin m := ⟨i.1 - n, by omega⟩
        let j' : Fin m := ⟨j.1 - n, by omega⟩
        have hi_cast : Fin.natAdd n i' = i := by
          ext
          simp [i']
          omega
        have hj_cast : Fin.natAdd n j' = j := by
          ext
          simp [j']
          omega
        have hEq0 : splitLast n m x i' 0 = splitLast n m x j' 0 := by
          simpa [splitLast, hi_cast, hj_cast] using
            congrArg (fun y : SpacetimeDim d => y 0) hijEq
        have hij' : i' ≠ j' := by
          intro hij'
          apply hij
          simpa [hi_cast, hj_cast] using congrArg (fun t : Fin m => Fin.natAdd n t) hij'
        rcases lt_or_gt_of_ne hij' with hij'_lt | hij'_gt
        · have hlt : splitLast n m x i' 0 < splitLast n m x j' 0 := (hxB i').2 j' hij'_lt
          exact (lt_irrefl (splitLast n m x i' 0)) (hEq0 ▸ hlt)
        · have hlt : splitLast n m x j' 0 < splitLast n m x i' 0 := (hxB j').2 i' hij'_gt
          exact (lt_irrefl (splitLast n m x j' 0)) (hEq0.symm ▸ hlt)
  exact hdisj.mono_left hsupport

/-- The ordered pullback transports time-support control through the
difference-coordinate chart.  This is the local support packet needed before a
single A0 cutoff can be chosen on a neighborhood of a positive real point. -/
theorem osiiA0_orderedPullback_tsupport_subset_timeSet
    [NeZero d]
    {n : ℕ}
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (φ : SchwartzMap (Fin n → ℝ) ℂ)
    (U : Set (Fin n → ℝ))
    (hφU : tsupport (φ : (Fin n → ℝ) → ℂ) ⊆ U) :
    tsupport
        (((section43OrderedPullbackTimeSpatialTensorCLM d n χ φ :
          SchwartzNPoint d n) : NPointDomain d n → ℂ)) ⊆
      { y : NPointDomain d n |
        section43QTime (d := d) (n := n)
          (section43DiffCoordRealCLE d n y) ∈ U } := by
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
  exact hφU
    (tsupport_section43NPointTimeSpatialTensor_subset_time_preimage
      d n φ χ hy_pre)

private theorem osiiA0_section43NPointTimeSpatialTensor_tsupport_subset_spatial_preimage
    [NeZero d]
    {n : ℕ}
    (φ : SchwartzMap (Fin n → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ) :
    tsupport
        ((section43NPointTimeSpatialTensor d n φ χ :
          SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
      (section43QSpatial (d := d) (n := n)) ⁻¹'
        tsupport (χ : Section43SpatialSpace d n → ℂ) := by
  intro q hq
  have hfun :
      (((section43NPointTimeSpatialTensor d n φ χ :
          SchwartzNPoint d n) : NPointDomain d n → ℂ)) =
        fun q : NPointDomain d n =>
          φ (section43QTime (d := d) (n := n) q) *
            χ (section43QSpatial (d := d) (n := n) q) := by
    funext q
    simp
  have hprod :
      q ∈ tsupport
        (fun q : NPointDomain d n =>
          φ (section43QTime (d := d) (n := n) q) *
            χ (section43QSpatial (d := d) (n := n) q)) := by
    simpa [hfun] using hq
  have hsp_pullback :
      q ∈ tsupport
        (fun q : NPointDomain d n =>
          χ (section43QSpatial (d := d) (n := n) q)) :=
    (tsupport_mul_subset_right
      (f := fun q : NPointDomain d n =>
        φ (section43QTime (d := d) (n := n) q))
      (g := fun q : NPointDomain d n =>
        χ (section43QSpatial (d := d) (n := n) q))) hprod
  exact
    (tsupport_comp_subset_preimage
      (χ : Section43SpatialSpace d n → ℂ)
      (f := section43QSpatial (d := d) (n := n))
      (by
        simpa [section43QSpatialCLM_apply] using
          (section43QSpatialCLM d n).continuous)) hsp_pullback

/-- The ordered pullback transports simultaneous time and spatial support
control through the difference-coordinate chart. -/
theorem osiiA0_orderedPullback_tsupport_subset_time_spatialSet
    [NeZero d]
    {n : ℕ}
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
    (φ : SchwartzMap (Fin n → ℝ) ℂ)
    (U : Set (Fin n → ℝ))
    (V : Set (Section43SpatialSpace d n))
    (hφU : tsupport (φ : (Fin n → ℝ) → ℂ) ⊆ U)
    (hχV : tsupport (χ : Section43SpatialSpace d n → ℂ) ⊆ V) :
    tsupport
        (((section43OrderedPullbackTimeSpatialTensorCLM d n χ φ :
          SchwartzNPoint d n) : NPointDomain d n → ℂ)) ⊆
      { y : NPointDomain d n |
        section43QTime (d := d) (n := n)
            (section43DiffCoordRealCLE d n y) ∈ U ∧
          section43QSpatial (d := d) (n := n)
            (section43DiffCoordRealCLE d n y) ∈ V } := by
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
  constructor
  · exact hφU
      (tsupport_section43NPointTimeSpatialTensor_subset_time_preimage
        d n φ χ hy_pre)
  · exact hχV
      (osiiA0_section43NPointTimeSpatialTensor_tsupport_subset_spatial_preimage
        (d := d) φ χ hy_pre)

/-- The support of an OS-conjugated tensor product is controlled by the support
of its right block after `splitLast`. -/
theorem osiiA0_osConjTensorProduct_tsupport_subset_right
    [NeZero d]
    {n m : ℕ}
    (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (P : Set (NPointDomain d m))
    (hgP : tsupport (g : NPointDomain d m → ℂ) ⊆ P) :
    tsupport (((f.osConjTensorProduct g : SchwartzNPoint d (n + m)) :
        NPointDomain d (n + m) → ℂ)) ⊆
      { x : NPointDomain d (n + m) | splitLast n m x ∈ P } := by
  intro x hx
  have hxprod :
      x ∈ tsupport (fun y : NPointDomain d (n + m) =>
        f.osConj (splitFirst n m y) * g (splitLast n m y)) := by
    simpa [SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_apply] using hx
  have hxright :
      x ∈ tsupport (fun y : NPointDomain d (n + m) => g (splitLast n m y)) :=
    (tsupport_mul_subset_right
      (f := fun y : NPointDomain d (n + m) =>
        f.osConj (splitFirst n m y))
      (g := fun y : NPointDomain d (n + m) =>
        g (splitLast n m y))) hxprod
  exact hgP
    (tsupport_comp_subset_preimage
      (g : NPointDomain d m → ℂ)
      (splitLast_continuousLinear n m) hxright)

/-- If the right ordered-pullback source is built from a time test supported
in `U`, then the two-block OS-conjugated current is supported over right
difference-times in `U`. -/
theorem osiiA0_osConjTensorProduct_orderedPullback_right_tsupport_subset_timeSet
    [NeZero d]
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (χ : SchwartzMap (Section43SpatialSpace d m) ℂ)
    (φ : SchwartzMap (Fin m → ℝ) ℂ)
    (U : Set (Fin m → ℝ))
    (hφU : tsupport (φ : (Fin m → ℝ) → ℂ) ⊆ U) :
    tsupport
        (((f.osConjTensorProduct
          (section43OrderedPullbackTimeSpatialTensorCLM d m χ φ) :
          SchwartzNPoint d (n + m)) : NPointDomain d (n + m) → ℂ)) ⊆
      { x : NPointDomain d (n + m) |
        section43QTime (d := d) (n := m)
          (section43DiffCoordRealCLE d m (splitLast n m x)) ∈ U } := by
  exact
    osiiA0_osConjTensorProduct_tsupport_subset_right
      (d := d) f
      (section43OrderedPullbackTimeSpatialTensorCLM d m χ φ)
      { y : NPointDomain d m |
        section43QTime (d := d) (n := m)
          (section43DiffCoordRealCLE d m y) ∈ U }
      (osiiA0_orderedPullback_tsupport_subset_timeSet
        (d := d) χ φ U hφU)

/-- If the right time test is supported in `U`, then the full two-block
OS-conjugated current is supported in the corresponding right-time cylinder.

This is the concrete support packet consumed by the OS-II A0 time-shell
transport theorem. -/
theorem osiiA0_osConjTensorProduct_orderedPullback_supportsInOpen_rightTimeCylinder
    [NeZero d]
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (hf_comp : HasCompactSupport (f : NPointDomain d n → ℂ))
    (κ : Section43SpatialCompactSource d m)
    (φ : SchwartzMap (Fin m → ℝ) ℂ)
    (U : Set (Fin m → ℝ))
    (hφU : SCV.SupportsInOpen (φ : (Fin m → ℝ) → ℂ) U) :
    SCV.SupportsInOpen
      (((f.osConjTensorProduct
        (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1 φ) :
        SchwartzNPoint d (n + m)) : NPointDomain d (n + m) → ℂ))
      { x : NPointDomain d (n + m) |
        section43QTime (d := d) (n := m)
          (section43DiffCoordRealCLE d m (splitLast n m x)) ∈ U } := by
  constructor
  · exact
      osiiA0_hasCompactSupport_osConjTensorProduct
        (d := d) f
        (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1 φ)
        hf_comp
        (osiiA0_hasCompactSupport_section43OrderedPullbackTimeSpatialTensorCLM_of_compact
          (d := d) (n := m) φ hφU.1 κ)
  · exact
      osiiA0_osConjTensorProduct_orderedPullback_right_tsupport_subset_timeSet
        (d := d) f κ.1 φ U hφU.2

/-- Uniform fixed-cutoff packet for right time tests supported in one compact
strict-positive neighborhood.

This is the local `(A0)` support geometry needed for OS-II `(5.2)`: once the
left block, right spatial block, and a compact right-time shell `U` are fixed,
one cutoff is valid for every right time Schwartz test supported in `U`. -/
theorem exists_osiiA0LocalCutoffSchwingerCLM_for_uniform_right_time_support
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    {n m : ℕ}
    (f : SchwartzNPoint d n)
    (hf_comp : HasCompactSupport (f : NPointDomain d n → ℂ))
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (κ : Section43SpatialCompactSource d m)
    (U : Set (Fin m → ℝ))
  (hU_comp : IsCompact U)
  (hU_pos : U ⊆ section43TimeStrictPositiveRegion m) :
    ∃ (χ : SchwartzNPoint d (n + m))
      (hχ_disj :
        Disjoint (tsupport (χ : NPointDomain d (n + m) → ℂ))
          (CoincidenceLocus d (n + m))),
      tsupport (χ : NPointDomain d (n + m) → ℂ) ⊆
        { x : NPointDomain d (n + m) |
          section43QTime (d := d) (n := m)
            (section43DiffCoordRealCLE d m (splitLast n m x)) ∈
              section43TimeStrictPositiveRegion m } ∧
        ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
          tsupport (φ : (Fin m → ℝ) → ℂ) ⊆ U →
            (∀ x ∈ tsupport
                (((f.osConjTensorProduct
                    (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1 φ) :
                    SchwartzNPoint d (n + m)) :
                      NPointDomain d (n + m) → ℂ)),
                χ x = 1) ∧
            osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
                (f.osConjTensorProduct
                  (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1 φ)) =
              OS.S (n + m)
                (ZeroDiagonalSchwartz.ofClassical
                  (f.osConjTensorProduct
                    (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1 φ))) := by
  classical
  let eRight :
      NPointDomain d m ≃L[ℝ]
        ((Fin m → ℝ) × Section43SpatialSpace d m) :=
    (section43DiffCoordRealCLE d m).trans (nPointTimeSpatialCLE (d := d) m)
  let Kright : Set (NPointDomain d m) :=
    { y : NPointDomain d m |
      section43QTime (d := d) (n := m)
          (section43DiffCoordRealCLE d m y) ∈ U ∧
        section43QSpatial (d := d) (n := m)
          (section43DiffCoordRealCLE d m y) ∈
            tsupport (κ.1 : Section43SpatialSpace d m → ℂ) }
  have hKright_eq :
      Kright =
        eRight.toHomeomorph.symm ''
          (U ×ˢ tsupport (κ.1 : Section43SpatialSpace d m → ℂ)) := by
    ext y
    constructor
    · intro hy
      refine ⟨eRight y, ?_, ?_⟩
      · simpa [Kright, eRight, section43QTime, section43QSpatial] using hy
      · simp [eRight]
    · rintro ⟨q, hq, rfl⟩
      simpa [Kright, eRight, section43QTime, section43QSpatial] using hq
  have hKright_comp : IsCompact Kright := by
    rw [hKright_eq]
    exact (hU_comp.prod κ.2.isCompact).image eRight.toHomeomorph.symm.continuous
  let Kleft : Set (NPointDomain d n) :=
    tsupport ((f.osConj : SchwartzNPoint d n) : NPointDomain d n → ℂ)
  have hKleft_comp : IsCompact Kleft := by
    exact (osiiA0_osConj_hasCompactSupport (d := d) f hf_comp).isCompact
  let eAppend := osiiA0_nPointAppendCLE d n m
  let K : Set (NPointDomain d (n + m)) :=
    eAppend.toHomeomorph '' (Kleft ×ˢ Kright)
  have hK_comp : IsCompact K := by
    exact (hKleft_comp.prod hKright_comp).image eAppend.toHomeomorph.continuous
  let Uopen : Set (NPointDomain d (n + m)) :=
    (CoincidenceLocus d (n + m))ᶜ ∩
      { x : NPointDomain d (n + m) |
        section43QTime (d := d) (n := m)
          (section43DiffCoordRealCLE d m (splitLast n m x)) ∈
            section43TimeStrictPositiveRegion m }
  have hUopen_open : IsOpen Uopen := by
    have htime_cont :
        Continuous fun y : NPointDomain d m =>
          section43QTime (d := d) (n := m)
            (section43DiffCoordRealCLE d m y) := by
      have hq_cont :
          Continuous (section43QTime (d := d) (n := m)) := by
        simpa [section43QTimeCLM_apply] using
          (section43QTimeCLM d m).continuous
      exact hq_cont.comp (section43DiffCoordRealCLE d m).continuous
    exact
      (isClosed_CoincidenceLocus (d := d) (n := n + m)).isOpen_compl.inter
        ((isOpen_section43TimeStrictPositiveRegion m).preimage
          (htime_cont.comp (splitLast_continuousLinear n m)))
  have hK_sub_Uopen : K ⊆ Uopen := by
    rintro x ⟨p, hp, rfl⟩
    constructor
    · have hpneg : p.1 ∈ OrderedNegativeTimeRegion d n := by
        exact osiiA0_osConj_tsupport_subset_orderedNegative (d := d) f hf_ord hp.1
      have hptime_pos :
          ∀ i : Fin m,
            0 < section43QTime (d := d) (n := m)
              (section43DiffCoordRealCLE d m p.2) i :=
        hU_pos hp.2.1
      have hpδ_pos : ∀ i : Fin m,
          0 < (section43DiffCoordRealCLE d m p.2) i 0 := by
        intro i
        simpa [section43QTime, nPointTimeSpatialCLE] using hptime_pos i
      have hppos' :
          (section43DiffCoordRealCLE d m).symm
              (section43DiffCoordRealCLE d m p.2) ∈
            OrderedPositiveTimeRegion d m :=
        section43DiffCoordRealCLE_symm_mem_orderedPositiveTimeRegion_of_pos_time
          d m (δ := section43DiffCoordRealCLE d m p.2) hpδ_pos
      have hppos : p.2 ∈ OrderedPositiveTimeRegion d m := by
        simpa using hppos'
      exact
        osiiA0_nPointAppendCLE_not_mem_coincidence_of_neg_pos
          (d := d) p hpneg hppos
    · have hsplit : splitLast n m (eAppend p) = p.2 := by
        ext i μ
        simp [eAppend, splitLast]
      simpa [hsplit] using hU_pos hp.2.1
  obtain ⟨χ, hχ_one_K, hχ_sub⟩ :=
    osiiA0_exists_schwartzNPoint_cutoff_eq_one_on_compact_subset_open
      (d := d) (n := n + m) (K := K) (U := Uopen)
      hK_comp hUopen_open hK_sub_Uopen
  have hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d (n + m) → ℂ))
        (CoincidenceLocus d (n + m)) := by
    refine Set.disjoint_left.2 ?_
    intro x hx hcoin
    exact (hχ_sub hx).1 hcoin
  have hχ_time :
      tsupport (χ : NPointDomain d (n + m) → ℂ) ⊆
        { x : NPointDomain d (n + m) |
          section43QTime (d := d) (n := m)
            (section43DiffCoordRealCLE d m (splitLast n m x)) ∈
              section43TimeStrictPositiveRegion m } := by
    intro x hx
    exact (hχ_sub hx).2
  refine ⟨χ, hχ_disj, hχ_time, ?_⟩
  intro φ hφU
  let right : SchwartzNPoint d m :=
    section43OrderedPullbackTimeSpatialTensorCLM d m κ.1 φ
  let F : SchwartzNPoint d (n + m) := f.osConjTensorProduct right
  have hright_subset :
      tsupport (right : NPointDomain d m → ℂ) ⊆ Kright := by
    intro y hy
    have hys :=
      osiiA0_orderedPullback_tsupport_subset_time_spatialSet
        (d := d) κ.1 φ U
        (tsupport (κ.1 : Section43SpatialSpace d m → ℂ)) hφU
        (Subset.refl _) hy
    simpa [right, Kright] using hys
  have hF_sub_K :
      tsupport (F : NPointDomain d (n + m) → ℂ) ⊆ K := by
    intro x hx
    have hxprod :
        x ∈ tsupport (fun y : NPointDomain d (n + m) =>
          f.osConj (splitFirst n m y) * right (splitLast n m y)) := by
      simpa [F, SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_apply] using hx
    have hxleft_fun :
        x ∈ tsupport
          (fun y : NPointDomain d (n + m) => f.osConj (splitFirst n m y)) :=
      (tsupport_mul_subset_left
        (f := fun y : NPointDomain d (n + m) => f.osConj (splitFirst n m y))
        (g := fun y : NPointDomain d (n + m) => right (splitLast n m y))) hxprod
    have hxright_fun :
        x ∈ tsupport
          (fun y : NPointDomain d (n + m) => right (splitLast n m y)) :=
      (tsupport_mul_subset_right
        (f := fun y : NPointDomain d (n + m) => f.osConj (splitFirst n m y))
        (g := fun y : NPointDomain d (n + m) => right (splitLast n m y))) hxprod
    have hxleft : splitFirst n m x ∈ Kleft :=
      tsupport_comp_subset_preimage
        ((f.osConj : SchwartzNPoint d n) : NPointDomain d n → ℂ)
        (splitFirst_continuousLinear n m) hxleft_fun
    have hxright : splitLast n m x ∈ Kright :=
      hright_subset
        (tsupport_comp_subset_preimage
          (right : NPointDomain d m → ℂ)
          (splitLast_continuousLinear n m) hxright_fun)
    refine ⟨(splitFirst n m x, splitLast n m x), ⟨hxleft, hxright⟩, ?_⟩
    have hpair :
        (splitFirst n m x, splitLast n m x) = eAppend.symm x := by
      ext i μ
      · simpa [eAppend] using
          congrFun (congrFun (osiiA0_nPointAppendCLE_symm_fst d n m x) i) μ
      · simpa [eAppend] using
          congrFun (congrFun (osiiA0_nPointAppendCLE_symm_snd d n m x) i) μ
    rw [hpair]
    simp [eAppend]
  have hχ_one_F :
      ∀ x ∈ tsupport (F : NPointDomain d (n + m) → ℂ), χ x = 1 := by
    intro x hx
    exact hχ_one_K x (hF_sub_K hx)
  have hφ_pos :
      tsupport (φ : (Fin m → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion m :=
    hφU.trans hU_pos
  have hright_ord :
      tsupport (right : NPointDomain d m → ℂ) ⊆
        OrderedPositiveTimeRegion d m := by
    simpa [right] using
      section43OrderedPullbackTimeSpatialTensorCLM_tsupport_subset_orderedPositive_of_tsupport_strictPositive
        d m κ.1 φ hφ_pos
  have hvanish : VanishesToInfiniteOrderOnCoincidence F := by
    simpa [F, right] using
      VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
        (d := d) f right hf_ord hright_ord
  refine ⟨?_, ?_⟩
  · simpa [F, right] using hχ_one_F
  · calc
      osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
          (f.osConjTensorProduct
            (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1 φ))
          = osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj F := by
              rfl
      _ = OS.S (n + m) ⟨F, hvanish⟩ := by
              exact
                osiiA0LocalCutoffSchwingerCLM_apply_eq_of_one_on_tsupport
                  OS χ hχ_disj F hvanish hχ_one_F
      _ = OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical F) := by
              rw [ZeroDiagonalSchwartz.ofClassical_of_vanishes (f := F) hvanish]
      _ = OS.S (n + m)
            (ZeroDiagonalSchwartz.ofClassical
              (f.osConjTensorProduct
                (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1 φ))) := by
              rfl

/-- Compact product-source Schwinger pairings from a represented local A0
time-shell distribution.

This is the producer-facing form of the OS-II `(A0)->(P0)` handoff: once the
same cutoff distribution is represented by `S_real` on a right-time shell and
is known to recover the honest Schwinger value for every time test supported in
that shell, the representative has the compact positive product-source
Schwinger pairings consumed by the pointwise delta step. -/
theorem osiiA0LocalCutoffTimeShell_schwinger_pairings_of_representsDistributionOn
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    {n m : ℕ}
    (χ : SchwartzNPoint d (n + m))
    (hχ_disj :
      Disjoint (tsupport (χ : NPointDomain d (n + m) → ℂ))
        (CoincidenceLocus d (n + m)))
    (fLeft : SchwartzNPoint d n)
    (κ : Section43SpatialCompactSource d m)
    (S_real : (Fin m → ℝ) → ℂ)
    (U : Set (Fin m → ℝ))
    (hrep :
      SCV.RepresentsDistributionOn
        (osiiA0LocalCutoffTimeShellCLM
          OS χ hχ_disj fLeft κ)
        S_real U)
    (hχ_schwinger :
      ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
        tsupport (φ : (Fin m → ℝ) → ℂ) ⊆ U →
          osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
              (fLeft.osConjTensorProduct
                (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1 φ)) =
            OS.S (n + m)
              (ZeroDiagonalSchwartz.ofClassical
                (fLeft.osConjTensorProduct
                  (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1 φ)))) :
    ∀ gs : Fin m → Section43CompactPositiveTimeSource1D,
      tsupport ((section43TimeProductSource gs).f : (Fin m → ℝ) → ℂ) ⊆ U →
        (∫ τ : Fin m → ℝ,
            S_real τ * (section43TimeProductSource gs).f τ) =
          OS.S (n + m)
            (ZeroDiagonalSchwartz.ofClassical
              (fLeft.osConjTensorProduct
                (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1
                  (section43TimeProductSource gs).f))) := by
  intro gs hgsU
  calc
    (∫ τ : Fin m → ℝ,
        S_real τ * (section43TimeProductSource gs).f τ)
        =
      osiiA0LocalCutoffTimeShellCLM
        OS χ hχ_disj fLeft κ (section43TimeProductSource gs).f := by
        simpa using
          (hrep (section43TimeProductSource gs).f
            ⟨(section43TimeProductSource gs).compact, hgsU⟩).symm
    _ =
      osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
          (fLeft.osConjTensorProduct
            (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1
              (section43TimeProductSource gs).f)) := by
        rfl
    _ =
      OS.S (n + m)
        (ZeroDiagonalSchwartz.ofClassical
          (fLeft.osConjTensorProduct
            (section43OrderedPullbackTimeSpatialTensorCLM d m κ.1
              (section43TimeProductSource gs).f))) :=
        hχ_schwinger (section43TimeProductSource gs).f hgsU

/-- Fixed-left/right product-source specialization of the local `(A0)` cutoff
distribution at the Schwinger/BVT source-current seam. -/
theorem exists_osiiA0LocalCutoffSchwingerCLM_for_section43TwoBlockProductSource
    [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    {n m : ℕ}
    (gs₁ : Fin n → Section43CompactPositiveTimeSource1D)
    (κ₁ : Section43SpatialCompactSource d n)
    (gs₂ : Fin m → Section43CompactPositiveTimeSource1D)
    (κ₂ : Section43SpatialCompactSource d m) :
    ∃ (χ : SchwartzNPoint d (n + m))
      (hχ_disj :
        Disjoint (tsupport (χ : NPointDomain d (n + m) → ℂ))
          (CoincidenceLocus d (n + m))),
      (∀ x ∈ tsupport
          (((section43OrderedPullbackTimeSpatialTensorCLM d n κ₁.1
              (section43TimeProductSource gs₁).f).osConjTensorProduct
            (section43OrderedPullbackTimeSpatialTensorCLM d m κ₂.1
              (section43TimeProductSource gs₂).f) :
              SchwartzNPoint d (n + m)) : NPointDomain d (n + m) → ℂ),
          χ x = 1) ∧
      osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
          ((section43OrderedPullbackTimeSpatialTensorCLM d n κ₁.1
              (section43TimeProductSource gs₁).f).osConjTensorProduct
            (section43OrderedPullbackTimeSpatialTensorCLM d m κ₂.1
              (section43TimeProductSource gs₂).f)) =
        OS.S (n + m)
          (ZeroDiagonalSchwartz.ofClassical
            ((section43OrderedPullbackTimeSpatialTensorCLM d n κ₁.1
                (section43TimeProductSource gs₁).f).osConjTensorProduct
              (section43OrderedPullbackTimeSpatialTensorCLM d m κ₂.1
                (section43TimeProductSource gs₂).f))) := by
  let left : SchwartzNPoint d n :=
    section43OrderedPullbackTimeSpatialTensorCLM d n κ₁.1
      (section43TimeProductSource gs₁).f
  let right : SchwartzNPoint d m :=
    section43OrderedPullbackTimeSpatialTensorCLM d m κ₂.1
      (section43TimeProductSource gs₂).f
  let F : SchwartzNPoint d (n + m) := left.osConjTensorProduct right
  have hleft_comp : HasCompactSupport (left : NPointDomain d n → ℂ) := by
    simpa [left] using
      osiiA0_hasCompactSupport_section43OrderedPullbackTimeSpatialTensorCLM_product
        (d := d) (n := n) gs₁ κ₁
  have hright_comp : HasCompactSupport (right : NPointDomain d m → ℂ) := by
    simpa [right] using
      osiiA0_hasCompactSupport_section43OrderedPullbackTimeSpatialTensorCLM_product
        (d := d) (n := m) gs₂ κ₂
  have hF_comp : HasCompactSupport (F : NPointDomain d (n + m) → ℂ) := by
    simpa [F] using
      osiiA0_hasCompactSupport_osConjTensorProduct
        (d := d) left right hleft_comp hright_comp
  have hleft_ord :
      tsupport (left : NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n := by
    simpa [left] using
      section43OrderedPullbackTimeSpatialTensorCLM_tsupport_subset_orderedPositive_of_tsupport_strictPositive
        d n κ₁.1 (section43TimeProductSource gs₁).f
        (section43TimeProductSource gs₁).positive
  have hright_ord :
      tsupport (right : NPointDomain d m → ℂ) ⊆
        OrderedPositiveTimeRegion d m := by
    simpa [right] using
      section43OrderedPullbackTimeSpatialTensorCLM_tsupport_subset_orderedPositive_of_tsupport_strictPositive
        d m κ₂.1 (section43TimeProductSource gs₂).f
        (section43TimeProductSource gs₂).positive
  have hF_disj :
      Disjoint (tsupport (F : NPointDomain d (n + m) → ℂ))
        (CoincidenceLocus d (n + m)) := by
    simpa [F] using
      osiiA0_osConjTensorProduct_tsupport_disjoint_coincidence_of_ordered
        (d := d) left right hleft_ord hright_ord
  have hF_vanish : VanishesToInfiniteOrderOnCoincidence F := by
    simpa [F] using
      VanishesToInfiniteOrderOnCoincidence_osConjTensorProduct_of_tsupport_subset_orderedPositiveTimeRegion
        (d := d) left right hleft_ord hright_ord
  rcases
    exists_osiiA0LocalCutoffSchwingerCLM_for_compact_disjoint_test
      (d := d) (n := n + m) OS F hF_comp hF_disj with
    ⟨χ, hχ_disj, hχ_one, hχ_apply⟩
  refine ⟨χ, hχ_disj, ?_, ?_⟩
  · simpa [F, left, right] using hχ_one
  · have hzero :
        (⟨F, VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint
            F hF_disj⟩ : ZeroDiagonalSchwartz d (n + m)) =
          ZeroDiagonalSchwartz.ofClassical F := by
      apply Subtype.ext
      exact
        (ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
          (f := F) hF_vanish).symm
    calc
      osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj
          ((section43OrderedPullbackTimeSpatialTensorCLM d n κ₁.1
              (section43TimeProductSource gs₁).f).osConjTensorProduct
            (section43OrderedPullbackTimeSpatialTensorCLM d m κ₂.1
              (section43TimeProductSource gs₂).f))
          = osiiA0LocalCutoffSchwingerCLM OS χ hχ_disj F := by
              rfl
      _ = OS.S (n + m)
            ⟨F, VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint
              F hF_disj⟩ := hχ_apply
      _ = OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical F) := by
            rw [hzero]
      _ = OS.S (n + m)
          (ZeroDiagonalSchwartz.ofClassical
            ((section43OrderedPullbackTimeSpatialTensorCLM d n κ₁.1
                (section43TimeProductSource gs₁).f).osConjTensorProduct
              (section43OrderedPullbackTimeSpatialTensorCLM d m κ₂.1
                (section43TimeProductSource gs₂).f))) := by
          rfl

end OSReconstruction
