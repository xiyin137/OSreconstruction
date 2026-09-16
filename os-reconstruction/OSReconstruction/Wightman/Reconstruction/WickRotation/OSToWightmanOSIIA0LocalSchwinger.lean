/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSourceCurrent
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSchwingerSourceCurrent
import OSReconstruction.SCV.EuclideanWeylOpen













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
      change Continuous fun x : NPointDomain d n => -x i 0
      exact
        ((continuous_apply 0 : Continuous fun y : SpacetimeDim d => y 0).comp
          (continuous_apply i : Continuous fun x : NPointDomain d n => x i)).neg
    · simp only [timeReflectionN, timeReflection, hμ]
      exact
        (continuous_apply μ : Continuous fun y : SpacetimeDim d => y μ).comp
          (continuous_apply i : Continuous fun x : NPointDomain d n => x i)
  continuous_invFun := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro μ
    by_cases hμ : μ = 0
    · subst hμ
      change Continuous fun x : NPointDomain d n => -x i 0
      exact
        ((continuous_apply 0 : Continuous fun y : SpacetimeDim d => y 0).comp
          (continuous_apply i : Continuous fun x : NPointDomain d n => x i)).neg
    · simp only [timeReflectionN, timeReflection, hμ]
      exact
        (continuous_apply μ : Continuous fun y : SpacetimeDim d => y μ).comp
          (continuous_apply i : Continuous fun x : NPointDomain d n => x i)

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
      change x ∈ tsupport (fun y : NPointDomain d (n + m) =>
        (f.osConj.tensorProduct g) y)
      exact hx
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

end OSReconstruction
