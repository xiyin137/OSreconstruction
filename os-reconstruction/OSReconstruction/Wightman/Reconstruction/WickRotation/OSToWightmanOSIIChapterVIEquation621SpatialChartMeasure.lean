import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVBlockGlobalTimeMeasure
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorGlobalProfile
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIReducedBVTComparison

/-!
# Volume preservation of the reflected spatial chart

The block-global spatial chart acts independently in every spatial scalar
coordinate.  Its scalar action differs from the already volume-preserving
time chart only by a conjugated sign change on the left block.  Consequently
the spatial chart also has unit Jacobian.
-/

noncomputable section

open MeasureTheory
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Reverse the left scalar block without changing its sign.  This is the
spatial counterpart of chronological reverse-and-time-reflect. -/
noncomputable def axisPairReflectReverseLeftSpatialScalarCLE
    (n m : Nat) :
    (Fin (n + m) -> Real) ≃L[Real] (Fin (n + m) -> Real) :=
  (SCV.finAppendCLE n m).symm |>.trans
    ((ContinuousLinearEquiv.prodCongr
      (LinearEquiv.funCongrLeft Real Real Fin.revPerm
        ).toContinuousLinearEquiv
      (ContinuousLinearEquiv.refl Real (Fin m -> Real))).trans
        (SCV.finAppendCLE n m))

@[simp]
theorem axisPairReflectReverseLeftSpatialScalarCLE_apply_left
    (n m : Nat) (x : Fin (n + m) -> Real) (i : Fin n) :
    axisPairReflectReverseLeftSpatialScalarCLE n m x
        (Fin.castAdd m i) =
      x (Fin.castAdd m (Fin.rev i)) := by
  simp [axisPairReflectReverseLeftSpatialScalarCLE,
    LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, splitFirst]

@[simp]
theorem axisPairReflectReverseLeftSpatialScalarCLE_apply_right
    (n m : Nat) (x : Fin (n + m) -> Real) (j : Fin m) :
    axisPairReflectReverseLeftSpatialScalarCLE n m x
        (Fin.natAdd n j) =
      x (Fin.natAdd n j) := by
  simp [axisPairReflectReverseLeftSpatialScalarCLE, splitLast]

/-- Scalar action of the block-global chart on one spatial coordinate. -/
noncomputable def axisPairBlockGlobalSpatialScalarCLE
    (n m : Nat) :
    (Fin (n + m) -> Real) ≃L[Real] (Fin (n + m) -> Real) :=
  (osiiAxisPairBlockwiseTimeDiffCLE n m).symm |>.trans
    ((axisPairReflectReverseLeftSpatialScalarCLE n m).trans
      (section43ScalarDiffCLE (n + m)))

/-- Insert a zero common head before a tuple of reduced global spatial
coordinates.  The explicit formula avoids associativity transports between
`(r + 1) + m` and `(r + m) + 1`. -/
def axisPairBlockGlobalSpatialScalarZeroHead
    {r m : Nat} (x : Fin (r + m) -> Real) :
    Fin ((r + 1) + m) -> Real := fun c =>
  if h : c.val = 0 then 0 else x ⟨c.val - 1, by omega⟩

@[simp]
theorem axisPairBlockGlobalSpatialScalarZeroHead_zero
    {r m : Nat} (x : Fin (r + m) -> Real) :
    axisPairBlockGlobalSpatialScalarZeroHead x 0 = 0 := by
  simp [axisPairBlockGlobalSpatialScalarZeroHead]

@[simp]
theorem axisPairBlockGlobalSpatialScalarZeroHead_succ
    {r m : Nat} (x : Fin (r + m) -> Real) (c : Fin (r + m)) :
    axisPairBlockGlobalSpatialScalarZeroHead x
        ⟨c.val + 1, by omega⟩ = x c := by
  simp [axisPairBlockGlobalSpatialScalarZeroHead]

private theorem section43ScalarDiffCLE_symm_succ_sub_castSucc_spatial
    {r : Nat}
    (delta : Fin (r + 1) -> Real)
    (i : Fin r) :
    (section43ScalarDiffCLE (r + 1)).symm delta i.succ -
        (section43ScalarDiffCLE (r + 1)).symm delta i.castSucc =
      delta i.succ := by
  have h := congrFun
    ((section43ScalarDiffCLE (r + 1)).apply_symm_apply delta) i.succ
  simpa [section43ScalarDiffCLE_apply] using h

/-- After removing its common zero head, the block-global spatial chart is
signed reversal on the left internal gaps and identity on the remaining
bridge-plus-right gaps. -/
theorem axisPairBlockGlobalSpatialScalarCLE_zeroHead_tail
    {r m : Nat}
    (x : Fin (r + m) -> Real)
    (j : Fin (r + m)) :
    axisPairBlockGlobalSpatialScalarCLE (r + 1) m
        (axisPairBlockGlobalSpatialScalarZeroHead x)
        ⟨j.val + 1, by omega⟩ =
      Fin.append
        (fun a : Fin r => -x (Fin.castAdd m (Fin.rev a)))
        (fun b : Fin m => x (Fin.natAdd r b)) j := by
  refine Fin.addCases ?_ ?_ j
  · intro a
    simp only [Fin.val_castAdd, Fin.append_left]
    change
      section43ScalarDiffCLE ((r + 1) + m)
          (axisPairReflectReverseLeftSpatialScalarCLE (r + 1) m
            ((osiiAxisPairBlockwiseTimeDiffCLE (r + 1) m).symm
              (axisPairBlockGlobalSpatialScalarZeroHead x)))
          ⟨a.val + 1, by omega⟩ =
        -x (Fin.castAdd m (Fin.rev a))
    rw [section43ScalarDiffCLE_apply]
    rw [dif_neg (by
      simpa only [Nat.succ_eq_add_one] using Nat.succ_ne_zero a.val)]
    have hcurrent :
        (⟨a.val + 1, by omega⟩ : Fin ((r + 1) + m)) =
          Fin.castAdd m a.succ := by
      ext
      rfl
    have hprevious :
        (⟨a.val + 1 - 1, by omega⟩ : Fin ((r + 1) + m)) =
          Fin.castAdd m a.castSucc := by
      ext
      simp
    simp only [hcurrent, hprevious,
      axisPairReflectReverseLeftSpatialScalarCLE_apply_left,
      osiiAxisPairBlockwiseTimeDiffCLE_symm_apply_left]
    rw [Fin.rev_succ, Fin.rev_castSucc]
    have hdiff :=
      section43ScalarDiffCLE_symm_succ_sub_castSucc_spatial
        (splitFirst (r + 1) m
          (axisPairBlockGlobalSpatialScalarZeroHead x)) (Fin.rev a)
    have hvalue :
        splitFirst (r + 1) m
            (axisPairBlockGlobalSpatialScalarZeroHead x) (Fin.rev a).succ =
          x (Fin.castAdd m (Fin.rev a)) := by
      change axisPairBlockGlobalSpatialScalarZeroHead x
        ⟨(Fin.rev a).val + 1, by omega⟩ = _
      simpa only [Fin.val_castAdd] using
        axisPairBlockGlobalSpatialScalarZeroHead_succ x
          (Fin.castAdd m (Fin.rev a))
    rw [hvalue] at hdiff
    linarith
  · intro q
    simp only [Fin.val_natAdd, Fin.append_right]
    by_cases hq : q.val = 0
    · have hm : 0 < m := by omega
      have hq_eq : q = (⟨0, hm⟩ : Fin m) := Fin.ext hq
      change
        section43ScalarDiffCLE ((r + 1) + m)
            (axisPairReflectReverseLeftSpatialScalarCLE (r + 1) m
              ((osiiAxisPairBlockwiseTimeDiffCLE (r + 1) m).symm
                (axisPairBlockGlobalSpatialScalarZeroHead x)))
            ⟨r + q.val + 1, by omega⟩ =
          x (Fin.natAdd r q)
      rw [section43ScalarDiffCLE_apply]
      have hindex_ne :
          (⟨r + q.val + 1, by omega⟩ : Fin ((r + 1) + m)).val ≠ 0 :=
        Nat.succ_ne_zero (r + q.val)
      rw [dif_neg hindex_ne]
      have hcurrent :
          (⟨r + q.val + 1, by omega⟩ : Fin ((r + 1) + m)) =
            Fin.natAdd (r + 1) q := by
        ext
        simp
        omega
      have hprevious :
          (⟨r + q.val + 1 - 1, by omega⟩ : Fin ((r + 1) + m)) =
            Fin.castAdd m (Fin.last r) := by
        ext
        simp [hq]
      simp only [hcurrent, hprevious,
        axisPairReflectReverseLeftSpatialScalarCLE_apply_right,
        axisPairReflectReverseLeftSpatialScalarCLE_apply_left,
        osiiAxisPairBlockwiseTimeDiffCLE_symm_apply_right,
        osiiAxisPairBlockwiseTimeDiffCLE_symm_apply_left]
      have hright0 :
          (section43ScalarDiffCLE m).symm
              (splitLast (r + 1) m
                (axisPairBlockGlobalSpatialScalarZeroHead x)) q =
            x (Fin.natAdd r q) := by
        rw [hq_eq, section43ScalarDiffCLE_symm_apply]
        simp [splitLast, axisPairBlockGlobalSpatialScalarZeroHead]
      have hleft0 :
          (section43ScalarDiffCLE (r + 1)).symm
              (splitFirst (r + 1) m
                (axisPairBlockGlobalSpatialScalarZeroHead x))
              (Fin.rev (Fin.last r)) = 0 := by
        rw [Fin.rev_last]
        have hinv := congrFun
          ((section43ScalarDiffCLE (r + 1)).apply_symm_apply
            (splitFirst (r + 1) m
              (axisPairBlockGlobalSpatialScalarZeroHead x)))
          (0 : Fin (r + 1))
        rw [section43ScalarDiffCLE_apply] at hinv
        have hinv0 :
            (section43ScalarDiffCLE (r + 1)).symm
                (splitFirst (r + 1) m
                  (axisPairBlockGlobalSpatialScalarZeroHead x)) 0 =
              splitFirst (r + 1) m
                (axisPairBlockGlobalSpatialScalarZeroHead x) 0 := by
          simpa using hinv
        rw [hinv0]
        change axisPairBlockGlobalSpatialScalarZeroHead x 0 = 0
        exact axisPairBlockGlobalSpatialScalarZeroHead_zero x
      rw [hright0, hleft0]
      simp
    · let qprev : Fin m := ⟨q.val - 1, by omega⟩
      change
        section43ScalarDiffCLE ((r + 1) + m)
            (axisPairReflectReverseLeftSpatialScalarCLE (r + 1) m
              ((osiiAxisPairBlockwiseTimeDiffCLE (r + 1) m).symm
                (axisPairBlockGlobalSpatialScalarZeroHead x)))
            ⟨r + q.val + 1, by omega⟩ =
          x (Fin.natAdd r q)
      rw [section43ScalarDiffCLE_apply]
      have hindex_ne :
          (⟨r + q.val + 1, by omega⟩ : Fin ((r + 1) + m)).val ≠ 0 :=
        Nat.succ_ne_zero (r + q.val)
      rw [dif_neg hindex_ne]
      have hcurrent :
          (⟨r + q.val + 1, by omega⟩ : Fin ((r + 1) + m)) =
            Fin.natAdd (r + 1) q := by
        ext
        simp
        omega
      have hprevious :
          (⟨r + q.val + 1 - 1, by omega⟩ : Fin ((r + 1) + m)) =
            Fin.natAdd (r + 1) qprev := by
        ext
        simp [qprev]
        omega
      simp only [hcurrent, hprevious,
        axisPairReflectReverseLeftSpatialScalarCLE_apply_right,
        osiiAxisPairBlockwiseTimeDiffCLE_symm_apply_right]
      have hdiff := congrFun
        ((section43ScalarDiffCLE m).apply_symm_apply
          (splitLast (r + 1) m
            (axisPairBlockGlobalSpatialScalarZeroHead x))) q
      rw [section43ScalarDiffCLE_apply, dif_neg hq] at hdiff
      have hqprev :
          (⟨q.val - 1, by omega⟩ : Fin m) = qprev := rfl
      rw [hqprev] at hdiff
      have hvalue :
          splitLast (r + 1) m
              (axisPairBlockGlobalSpatialScalarZeroHead x) q =
            x (Fin.natAdd r q) := by
        change axisPairBlockGlobalSpatialScalarZeroHead x
          (Fin.natAdd (r + 1) q) = _
        have hindex :
            Fin.natAdd (r + 1) q =
              (⟨(Fin.natAdd r q).val + 1, by omega⟩ :
                Fin ((r + 1) + m)) := by
          apply Fin.ext
          simp
          omega
        rw [hindex]
        exact axisPairBlockGlobalSpatialScalarZeroHead_succ x
          (Fin.natAdd r q)
      rw [hvalue] at hdiff
      exact hdiff

/-- Zero-headed tuple with a positive left block, expressed without first
rewriting `n` as `(n - 1) + 1`. -/
def axisPairBlockGlobalSpatialScalarZeroHeadOfPositive
    (n m : Nat) (x : Fin ((n - 1) + m) -> Real) :
    Fin (n + m) -> Real := fun c =>
  if h : c.val = 0 then 0 else x ⟨c.val - 1, by omega⟩

/-- Positive-left-block form of
`axisPairBlockGlobalSpatialScalarCLE_zeroHead_tail`. -/
theorem axisPairBlockGlobalSpatialScalarCLE_zeroHeadOfPositive_tail
    {n m : Nat} (hn : 0 < n)
    (x : Fin ((n - 1) + m) -> Real)
    (j : Fin ((n - 1) + m)) :
    axisPairBlockGlobalSpatialScalarCLE n m
        (axisPairBlockGlobalSpatialScalarZeroHeadOfPositive n m x)
        ⟨j.val + 1, by omega⟩ =
      Fin.append
        (fun a : Fin (n - 1) => -x (Fin.castAdd m (Fin.rev a)))
        (fun b : Fin m => x (Fin.natAdd (n - 1) b)) j := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hzero :
      axisPairBlockGlobalSpatialScalarZeroHeadOfPositive (r + 1) m x =
        axisPairBlockGlobalSpatialScalarZeroHead x := by
    funext c
    simp [axisPairBlockGlobalSpatialScalarZeroHeadOfPositive,
      axisPairBlockGlobalSpatialScalarZeroHead]
  rw [hzero]
  exact axisPairBlockGlobalSpatialScalarCLE_zeroHead_tail x j

/-- Negate precisely the left block of a scalar tuple. -/
noncomputable def axisPairNegateLeftScalarCLE
    (n m : Nat) :
    (Fin (n + m) -> Real) ≃L[Real] (Fin (n + m) -> Real) :=
  ContinuousLinearEquiv.piCongrRight fun c =>
    if c.val < n then
      ContinuousLinearEquiv.neg Real
    else
      ContinuousLinearEquiv.refl Real Real

@[simp]
theorem axisPairNegateLeftScalarCLE_apply_left
    (n m : Nat) (x : Fin (n + m) -> Real) (i : Fin n) :
    axisPairNegateLeftScalarCLE n m x (Fin.castAdd m i) =
      -x (Fin.castAdd m i) := by
  simp [axisPairNegateLeftScalarCLE, ContinuousLinearEquiv.piCongrRight]

@[simp]
theorem axisPairNegateLeftScalarCLE_apply_right
    (n m : Nat) (x : Fin (n + m) -> Real) (j : Fin m) :
    axisPairNegateLeftScalarCLE n m x (Fin.natAdd n j) =
      x (Fin.natAdd n j) := by
  simp [axisPairNegateLeftScalarCLE, ContinuousLinearEquiv.piCongrRight]

/-- Removing the temporal sign from reverse-and-reflect is left-block
negation after that operation. -/
theorem axisPairReflectReverseLeftSpatialScalarCLE_eq
    (n m : Nat) :
    axisPairReflectReverseLeftSpatialScalarCLE n m =
      (osiiAxisPairReflectReverseLeftTimeCLE n m).trans
        (axisPairNegateLeftScalarCLE n m) := by
  ext x c
  refine Fin.addCases ?_ ?_ c
  · intro i
    simp
  · intro j
    simp

/-- The spatial scalar chart is the time chart followed by a conjugated
left-block sign change in global-difference coordinates. -/
theorem axisPairBlockGlobalSpatialScalarCLE_eq_time_conjugate
    (n m : Nat) :
    axisPairBlockGlobalSpatialScalarCLE n m =
      (osiiAxisPairBlockGlobalTimeCLE n m).trans
        ((section43ScalarDiffCLE (n + m)).symm.trans
          ((axisPairNegateLeftScalarCLE n m).trans
            (section43ScalarDiffCLE (n + m)))) := by
  rw [axisPairBlockGlobalSpatialScalarCLE,
    axisPairReflectReverseLeftSpatialScalarCLE_eq,
    osiiAxisPairBlockGlobalTimeCLE]
  ext x c
  simp

theorem axisPairNegateLeftScalarCLE_measurePreserving
    (n m : Nat) :
    MeasurePreserving
      (axisPairNegateLeftScalarCLE n m).toHomeomorph.toMeasurableEquiv
      (volume : Measure (Fin (n + m) -> Real))
      (volume : Measure (Fin (n + m) -> Real)) := by
  have hcoord : forall c : Fin (n + m),
      MeasurePreserving
        ((if c.val < n then
            ContinuousLinearEquiv.neg Real
          else
            ContinuousLinearEquiv.refl Real Real
          ).toHomeomorph.toMeasurableEquiv)
        (volume : Measure Real) (volume : Measure Real) := by
    intro c
    split_ifs
    · change MeasurePreserving (fun x : Real => -x)
        (volume : Measure Real) (volume : Measure Real)
      exact MeasureTheory.Measure.measurePreserving_neg
        (volume : Measure Real)
    · exact MeasurePreserving.id (volume : Measure Real)
  change MeasurePreserving (fun a i =>
      (if i.val < n then
        ContinuousLinearEquiv.neg Real
      else
        ContinuousLinearEquiv.refl Real Real) (a i))
    (volume : Measure (Fin (n + m) -> Real))
    (volume : Measure (Fin (n + m) -> Real))
  exact MeasureTheory.volume_preserving_pi hcoord

/-- The scalar spatial block-global chart preserves Lebesgue measure. -/
theorem axisPairBlockGlobalSpatialScalarCLE_measurePreserving
    (n m : Nat) :
    MeasurePreserving
      (axisPairBlockGlobalSpatialScalarCLE n m
        ).toHomeomorph.toMeasurableEquiv
      (volume : Measure (Fin (n + m) -> Real))
      (volume : Measure (Fin (n + m) -> Real)) := by
  have htime : MeasurePreserving
      (osiiAxisPairBlockGlobalTimeCLE n m
        ).toHomeomorph.toMeasurableEquiv
      (volume : Measure (Fin (n + m) -> Real))
      (volume : Measure (Fin (n + m) -> Real)) := by
    change MeasurePreserving (fun x => osiiAxisPairBlockGlobalTimeCLE n m x)
      (volume : Measure (Fin (n + m) -> Real))
      (volume : Measure (Fin (n + m) -> Real))
    exact axisPairBlockGlobalTimeME_measurePreserving n m
  have hdiff : MeasurePreserving
      (section43ScalarDiffCLE (n + m)).toHomeomorph.toMeasurableEquiv
      (volume : Measure (Fin (n + m) -> Real))
      (volume : Measure (Fin (n + m) -> Real)) := by
    change MeasurePreserving (fun x => section43ScalarDiffCLE (n + m) x)
      (volume : Measure (Fin (n + m) -> Real))
      (volume : Measure (Fin (n + m) -> Real))
    exact section43ScalarDiffME_measurePreserving (n + m)
  have hconjugate :=
    hdiff.symm.trans
      ((axisPairNegateLeftScalarCLE_measurePreserving n m).trans hdiff)
  rw [axisPairBlockGlobalSpatialScalarCLE_eq_time_conjugate]
  exact htime.trans hconjugate

private theorem blockwiseSpacetimeDiff_symm_spatial
    (d n m : Nat)
    (q : NPointDomain d (n + m))
    (mu : Fin d) :
    (fun c =>
      (osiiAxisPairBlockwiseSpacetimeDiffCLE d n m).symm q c mu.succ) =
      (osiiAxisPairBlockwiseTimeDiffCLE n m).symm
        (fun c => q c mu.succ) := by
  funext c
  refine Fin.addCases ?_ ?_ c
  · intro a
    simp only [
      osiiAxisPairBlockwiseSpacetimeDiffCLE_symm_apply_left,
      osiiAxisPairBlockwiseTimeDiffCLE_symm_apply_left]
    simp [section43ScalarDiffCLE_symm_apply, splitFirst]
  · intro b
    simp only [
      osiiAxisPairBlockwiseSpacetimeDiffCLE_symm_apply_right,
      osiiAxisPairBlockwiseTimeDiffCLE_symm_apply_right]
    simp [section43ScalarDiffCLE_symm_apply, splitLast]

private theorem reflectReverseLeftSpacetime_spatial
    (d n m : Nat)
    (x : NPointDomain d (n + m))
    (mu : Fin d) :
    (fun c =>
      osiiAxisPairReflectReverseLeftSpacetimeCLE d n m x c mu.succ) =
      axisPairReflectReverseLeftSpatialScalarCLE n m
        (fun c => x c mu.succ) := by
  funext c
  refine Fin.addCases ?_ ?_ c
  · intro a
    simp [timeReflection]
  · intro b
    simp

private theorem section43DiffCoordRealCLE_spatial
    (d n : Nat)
    (x : NPointDomain d n)
    (mu : Fin d) :
    (fun c => section43DiffCoordRealCLE d n x c mu.succ) =
      section43ScalarDiffCLE n (fun c => x c mu.succ) := by
  funext c
  simp [section43ScalarDiffCLE_apply]

private theorem blockGlobalSpacetime_spatial_component
    (d n m : Nat)
    (q : NPointDomain d (n + m))
    (mu : Fin d) :
    (fun c =>
      osiiAxisPairBlockGlobalSpacetimeCLE d n m q c mu.succ) =
      axisPairBlockGlobalSpatialScalarCLE n m
        (fun c => q c mu.succ) := by
  change
    (fun c =>
      section43DiffCoordRealCLE d (n + m)
        (osiiAxisPairReflectReverseLeftSpacetimeCLE d n m
          ((osiiAxisPairBlockwiseSpacetimeDiffCLE d n m).symm q))
        c mu.succ) = _
  rw [section43DiffCoordRealCLE_spatial,
    reflectReverseLeftSpacetime_spatial,
    blockwiseSpacetimeDiff_symm_spatial]
  rfl

private theorem volume_map_curry_symm
    (alpha beta : Type*) [Fintype alpha] [Fintype beta] :
    (volume : Measure (alpha -> beta -> Real)).map
        (MeasurableEquiv.curry alpha beta Real).symm =
      (volume : Measure (alpha × beta -> Real)) := by
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply
    (MeasurableEquiv.curry alpha beta Real).symm.measurable
    (MeasurableSet.univ_pi hs)]
  have hpreimage :
      (MeasurableEquiv.curry alpha beta Real).symm ⁻¹'
          (Set.univ.pi s) =
        Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_univ_pi,
      MeasurableEquiv.coe_curry_symm, Function.uncurry]
    exact ⟨fun h i j => h (i, j), fun h ⟨i, j⟩ => h i j⟩
  rw [hpreimage, volume_pi_pi]
  simp_rw [volume_pi_pi]
  rw [← Finset.prod_product', ← Finset.univ_product_univ]

private theorem curry_measurePreserving
    (alpha beta : Type*) [Fintype alpha] [Fintype beta] :
    MeasurePreserving
      (MeasurableEquiv.curry alpha beta Real)
      (volume : Measure (alpha × beta -> Real))
      (volume : Measure (alpha -> beta -> Real)) := by
  have hsymm : MeasurePreserving
      (MeasurableEquiv.curry alpha beta Real).symm
      (volume : Measure (alpha -> beta -> Real))
      (volume : Measure (alpha × beta -> Real)) :=
    ⟨(MeasurableEquiv.curry alpha beta Real).symm.measurable,
      volume_map_curry_symm alpha beta⟩
  exact hsymm.symm

/-- Euclidean spatial coordinates regrouped by scalar spatial direction. -/
noncomputable def section43SpatialCoordinateFibersME
    (d q : Nat) :
    Section43SpatialSpace d q ≃ᵐ (Fin d -> Fin q -> Real) :=
  (section43EuclideanSpaceMeasurableEquiv (Fin q × Fin d)).trans
    ((MeasurableEquiv.piCongrLeft
      (fun _ : Fin d × Fin q => Real)
      (Equiv.prodComm (Fin q) (Fin d))).trans
        (MeasurableEquiv.curry (Fin d) (Fin q) Real))

@[simp]
theorem section43SpatialCoordinateFibersME_apply
    (d q : Nat)
    (eta : Section43SpatialSpace d q)
    (mu : Fin d) (c : Fin q) :
    section43SpatialCoordinateFibersME d q eta mu c =
      section43SpatialParticleCLE d q eta c mu := by
  change
    (Equiv.piCongrLeft (fun _ : Fin d × Fin q => Real)
      (Equiv.prodComm (Fin q) (Fin d))
      (EuclideanSpace.equiv (ι := Fin q × Fin d) (𝕜 := Real) eta))
        (mu, c) =
      (EuclideanSpace.equiv (ι := Fin q × Fin d) (𝕜 := Real) eta)
        (c, mu)
  rw [Equiv.piCongrLeft_apply_eq_cast]
  rfl

theorem section43SpatialCoordinateFibersME_measurePreserving
    (d q : Nat) :
    MeasurePreserving
      (section43SpatialCoordinateFibersME d q)
      (volume : Measure (Section43SpatialSpace d q))
      (volume : Measure (Fin d -> Fin q -> Real)) := by
  exact
    (section43EuclideanSpaceMeasurableEquiv_measurePreserving
      (Fin q × Fin d)).trans
      ((volume_measurePreserving_piCongrLeft
        (fun _ : Fin d × Fin q => Real)
        (Equiv.prodComm (Fin q) (Fin d))).trans
          (curry_measurePreserving (Fin d) (Fin q)))

theorem axisPairBlockGlobalSpatialCLE_coordinate
    (d n m : Nat) [NeZero d]
    (eta : Section43SpatialSpace d (n + m))
    (mu : Fin d) :
    section43SpatialCoordinateFibersME d (n + m)
        (GeneratorHermiteHilbertFieldFamilyData.axisPairBlockGlobalSpatialCLE
          (d := d) n m eta) mu =
      axisPairBlockGlobalSpatialScalarCLE n m
        (section43SpatialCoordinateFibersME d (n + m) eta mu) := by
  funext c
  rw [section43SpatialCoordinateFibersME_apply,
    section43SpatialParticleCLE_apply,
    GeneratorHermiteHilbertFieldFamilyData.axisPairBlockGlobalSpatialCLE_apply,
    section43QSpatial_apply]
  let q : NPointDomain d (n + m) :=
    (nPointTimeSpatialCLE (d := d) (n + m)).symm (0, eta)
  have hq :
      (fun c => q c mu.succ) =
        section43SpatialCoordinateFibersME d (n + m) eta mu := by
    funext a
    rw [section43SpatialCoordinateFibersME_apply,
      section43SpatialParticleCLE_apply]
    have hsnd := congrArg Prod.snd
      ((nPointTimeSpatialCLE (d := d) (n + m)).apply_symm_apply
        (0, eta))
    exact congrArg
      (fun z : Section43SpatialSpace d (n + m) =>
        (EuclideanSpace.equiv
          (ι := Fin (n + m) × Fin d) (𝕜 := Real) z) (a, mu))
      hsnd
  change
    osiiAxisPairBlockGlobalSpacetimeCLE d n m q c mu.succ = _
  calc
    osiiAxisPairBlockGlobalSpacetimeCLE d n m q c mu.succ =
        axisPairBlockGlobalSpatialScalarCLE n m
          (fun a => q a mu.succ) c :=
      congrFun (blockGlobalSpacetime_spatial_component d n m q mu) c
    _ = axisPairBlockGlobalSpatialScalarCLE n m
          (section43SpatialCoordinateFibersME d (n + m) eta mu) c := by
      rw [hq]

/-- The complete block-global spatial chart has unit Jacobian. -/
theorem axisPairBlockGlobalSpatialCLE_measurePreserving
    (d n m : Nat) [NeZero d] :
    MeasurePreserving
      (GeneratorHermiteHilbertFieldFamilyData.axisPairBlockGlobalSpatialCLE
        (d := d) n m
        ).toHomeomorph.toMeasurableEquiv
      (volume : Measure (Section43SpatialSpace d (n + m)))
      (volume : Measure (Section43SpatialSpace d (n + m))) := by
  let coord := section43SpatialCoordinateFibersME d (n + m)
  let scalarCLE :
      (Fin d -> Fin (n + m) -> Real) ≃L[Real]
        (Fin d -> Fin (n + m) -> Real) :=
    ContinuousLinearEquiv.piCongrRight fun _ =>
      axisPairBlockGlobalSpatialScalarCLE n m
  let scalarME := scalarCLE.toHomeomorph.toMeasurableEquiv
  have hcoord :=
    section43SpatialCoordinateFibersME_measurePreserving d (n + m)
  have hscalar : MeasurePreserving scalarME
      (volume : Measure (Fin d -> Fin (n + m) -> Real))
      (volume : Measure (Fin d -> Fin (n + m) -> Real)) := by
    have hpi := volume_preserving_pi fun _ : Fin d =>
      axisPairBlockGlobalSpatialScalarCLE_measurePreserving n m
    have hfun : (scalarME :
        (Fin d -> Fin (n + m) -> Real) ->
          (Fin d -> Fin (n + m) -> Real)) =
        fun a i => axisPairBlockGlobalSpatialScalarCLE n m (a i) := by
      funext a i c
      rfl
    rw [hfun]
    exact hpi
  have hcomp : MeasurePreserving
      (coord.trans (scalarME.trans coord.symm))
      (volume : Measure (Section43SpatialSpace d (n + m)))
      (volume : Measure (Section43SpatialSpace d (n + m))) :=
    hcoord.trans (hscalar.trans hcoord.symm)
  convert hcomp using 1
  funext eta
  apply coord.injective
  funext mu
  simpa [scalarME, scalarCLE, ContinuousLinearEquiv.piCongrRight] using
    axisPairBlockGlobalSpatialCLE_coordinate d n m eta mu

/-- Flat-coordinate form of the block-global spatial chart. -/
noncomputable def axisPairBlockGlobalSpatialFlatCLE
    (d n m : Nat) [NeZero d] :
    (Fin ((n + m) * d) -> Real) ≃L[Real]
      (Fin ((n + m) * d) -> Real) :=
  (section43SpatialFlatCLE d (n + m)).symm |>.trans
    ((GeneratorHermiteHilbertFieldFamilyData.axisPairBlockGlobalSpatialCLE
      (d := d) n m).trans
        (section43SpatialFlatCLE d (n + m)))

@[simp]
theorem axisPairBlockGlobalSpatialFlatCLE_apply
    (d n m : Nat) [NeZero d]
    (x : Fin ((n + m) * d) -> Real)
    (j : Fin ((n + m) * d)) :
    axisPairBlockGlobalSpatialFlatCLE d n m x j =
      axisPairBlockGlobalSpatialScalarCLE n m
        (fun c => x (finProdFinEquiv
          (c, (finProdFinEquiv.symm j).2)))
        (finProdFinEquiv.symm j).1 := by
  rw [axisPairBlockGlobalSpatialFlatCLE,
    ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.trans_apply,
    section43SpatialFlatCLE_apply]
  have h := axisPairBlockGlobalSpatialCLE_coordinate d n m
    ((section43SpatialFlatCLE d (n + m)).symm x)
    (finProdFinEquiv.symm j).2
  have hfiber :
      section43SpatialCoordinateFibersME d (n + m)
          ((section43SpatialFlatCLE d (n + m)).symm x)
          (finProdFinEquiv.symm j).2 =
        fun c => x (finProdFinEquiv
          (c, (finProdFinEquiv.symm j).2)) := by
    funext c
    rw [section43SpatialCoordinateFibersME_apply,
      section43SpatialParticleCLE_apply]
    exact section43SpatialFlatCLE_symm_apply d (n + m) x
      (c, (finProdFinEquiv.symm j).2)
  rw [hfiber] at h
  simpa only [section43SpatialCoordinateFibersME_apply,
    section43SpatialParticleCLE_apply, Prod.eta] using
    congrFun h (finProdFinEquiv.symm j).1

/-- The flat-coordinate spatial chart also preserves Lebesgue measure. -/
theorem axisPairBlockGlobalSpatialFlatCLE_measurePreserving
    (d n m : Nat) [NeZero d] :
    MeasurePreserving
      (axisPairBlockGlobalSpatialFlatCLE d n m
        ).toHomeomorph.toMeasurableEquiv
      (volume : Measure (Fin ((n + m) * d) -> Real))
      (volume : Measure (Fin ((n + m) * d) -> Real)) := by
  have hflat : MeasurePreserving
      (section43SpatialFlatCLE d (n + m)).toHomeomorph.toMeasurableEquiv
      (volume : Measure (Section43SpatialSpace d (n + m)))
      (volume : Measure (Fin ((n + m) * d) -> Real)) := by
    simpa using section43SpatialFlatCLE_measurePreserving d (n + m)
  exact hflat.symm.trans
    ((axisPairBlockGlobalSpatialCLE_measurePreserving d n m).trans hflat)

/-- Reindexing a split's concatenated particles to the common absolute
particle cardinality preserves Euclidean volume. -/
theorem generatorSplitToAbsoluteSpatialCLE_measurePreserving
    {d k : Nat} [NeZero d]
    (i : GeneratorIndex k) :
    MeasurePreserving
      (generatorSplitToAbsoluteSpatialCLE (d := d) i
        ).toHomeomorph.toMeasurableEquiv
      (volume : Measure (Section43SpatialSpace d (i.n + i.m)))
      (volume : Measure (Section43SpatialSpace d (k + 1))) := by
  let sourceCoord := section43SpatialCoordinateFibersME d (i.n + i.m)
  let targetCoord := section43SpatialCoordinateFibersME d (k + 1)
  let castCLE :
      (Fin d -> Fin (i.n + i.m) -> Real) ≃L[Real]
        (Fin d -> Fin (k + 1) -> Real) :=
    ContinuousLinearEquiv.piCongrRight fun _ =>
      ContinuousLinearEquiv.piCongrLeft Real
        (fun _ : Fin (k + 1) => Real)
        (finCongr i.absoluteCard_eq.symm)
  let castME := castCLE.toHomeomorph.toMeasurableEquiv
  have hsource :=
    section43SpatialCoordinateFibersME_measurePreserving d (i.n + i.m)
  have htarget :=
    section43SpatialCoordinateFibersME_measurePreserving d (k + 1)
  have hcast : MeasurePreserving castME
      (volume : Measure (Fin d -> Fin (i.n + i.m) -> Real))
      (volume : Measure (Fin d -> Fin (k + 1) -> Real)) := by
    have h := volume_preserving_pi fun _ : Fin d =>
      volume_measurePreserving_piCongrLeft
        (fun _ : Fin (k + 1) => Real)
        (finCongr i.absoluteCard_eq.symm)
    have hfun : (castME :
        (Fin d -> Fin (i.n + i.m) -> Real) ->
          (Fin d -> Fin (k + 1) -> Real)) =
        fun (x : Fin d -> Fin (i.n + i.m) -> Real) (mu : Fin d) =>
          MeasurableEquiv.piCongrLeft
            (fun _ : Fin (k + 1) => Real)
            (finCongr i.absoluteCard_eq.symm) (x mu) := by
      funext x mu c
      rfl
    rw [hfun]
    exact h
  have hcomp : MeasurePreserving
      (sourceCoord.trans (castME.trans targetCoord.symm))
      (volume : Measure (Section43SpatialSpace d (i.n + i.m)))
      (volume : Measure (Section43SpatialSpace d (k + 1))) :=
    hsource.trans (hcast.trans htarget.symm)
  convert hcomp using 1
  funext eta
  apply targetCoord.injective
  funext mu c
  change section43SpatialParticleCLE d (k + 1)
      (generatorSplitToAbsoluteSpatialCLE i eta) c mu =
    targetCoord (targetCoord.symm (castME (sourceCoord eta))) mu c
  rw [generatorSplitToAbsoluteSpatialCLE_apply,
    targetCoord.apply_symm_apply]
  change section43SpatialParticleCLE d (i.n + i.m) eta
      (Fin.cast i.absoluteCard_eq c) mu =
    castME (sourceCoord eta) mu c
  rfl

/-- The generator chart on the common `k + 1` particle space preserves
Euclidean volume. -/
theorem generatorSplitGlobalSpatialCLE_measurePreserving
    {d k : Nat} [NeZero d]
    (i : GeneratorIndex k) :
    MeasurePreserving
      (GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialCLE
        (d := d) i).toHomeomorph.toMeasurableEquiv
      (volume : Measure (Section43SpatialSpace d (k + 1)))
      (volume : Measure (Section43SpatialSpace d (k + 1))) := by
  have hcast := generatorSplitToAbsoluteSpatialCLE_measurePreserving
    (d := d) i
  rw [GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialCLE]
  exact hcast.symm.trans
    ((axisPairBlockGlobalSpatialCLE_measurePreserving d i.n i.m).trans hcast)

/-- Flat-coordinate form of the common generator spatial chart. -/
noncomputable def generatorSplitGlobalSpatialFlatCLE
    {d k : Nat} [NeZero d]
    (i : GeneratorIndex k) :
    (Fin ((k + 1) * d) -> Real) ≃L[Real]
      (Fin ((k + 1) * d) -> Real) :=
  (section43SpatialFlatCLE d (k + 1)).symm |>.trans
    ((GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialCLE
      (d := d) i).trans (section43SpatialFlatCLE d (k + 1)))

/-- The flat generator chart preserves Lebesgue measure. -/
theorem generatorSplitGlobalSpatialFlatCLE_measurePreserving
    {d k : Nat} [NeZero d]
    (i : GeneratorIndex k) :
    MeasurePreserving
      (generatorSplitGlobalSpatialFlatCLE (d := d) i
        ).toHomeomorph.toMeasurableEquiv
      (volume : Measure (Fin ((k + 1) * d) -> Real))
      (volume : Measure (Fin ((k + 1) * d) -> Real)) := by
  have hflat : MeasurePreserving
      (section43SpatialFlatCLE d (k + 1)).toHomeomorph.toMeasurableEquiv
      (volume : Measure (Section43SpatialSpace d (k + 1)))
      (volume : Measure (Fin ((k + 1) * d) -> Real)) := by
    simpa using section43SpatialFlatCLE_measurePreserving d (k + 1)
  exact hflat.symm.trans
    ((generatorSplitGlobalSpatialCLE_measurePreserving (d := d) i).trans hflat)

end OSIIChapterV
end OSReconstruction
