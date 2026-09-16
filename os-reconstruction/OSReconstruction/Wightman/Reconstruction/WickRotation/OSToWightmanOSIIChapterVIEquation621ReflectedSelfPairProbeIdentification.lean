/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621ProductSpatialSelfPairApproxIdentity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621GeneratorSpatialSplit










noncomputable section

open Complex
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity

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

/-- In one spatial scalar coordinate, the reflected equal-block chart sends
two copies of `(x0, x)` to `(-reverse x, 0, x)` after its common head is
removed. -/
theorem axisPairBlockGlobalSpatialScalarCLE_duplicated_tail
    {r : Nat}
    (x0 : Real)
    (x : Fin r -> Real)
    (j : Fin (r + (r + 1))) :
    axisPairBlockGlobalSpatialScalarCLE (r + 1) (r + 1)
        (Fin.append (Fin.cons x0 x) (Fin.cons x0 x))
        ⟨j.val + 1, by omega⟩ =
      Fin.append (fun i : Fin r => -x (Fin.rev i)) (Fin.cons 0 x) j := by
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp only [Fin.val_castAdd, Fin.append_left]
    change
      section43ScalarDiffCLE ((r + 1) + (r + 1))
          (axisPairReflectReverseLeftSpatialScalarCLE (r + 1) (r + 1)
            ((osiiAxisPairBlockwiseTimeDiffCLE (r + 1) (r + 1)).symm
              (Fin.append (Fin.cons x0 x) (Fin.cons x0 x))))
          ⟨i.val + 1, by omega⟩ = -x (Fin.rev i)
    rw [section43ScalarDiffCLE_apply]
    rw [dif_neg (by
      simpa only [Nat.succ_eq_add_one] using Nat.succ_ne_zero i.val)]
    have hcurrent :
        (⟨i.val + 1, by omega⟩ :
            Fin ((r + 1) + (r + 1))) =
          Fin.castAdd (r + 1) i.succ := by
      ext
      rfl
    have hprevious :
        (⟨i.val + 1 - 1, by omega⟩ :
            Fin ((r + 1) + (r + 1))) =
          Fin.castAdd (r + 1) i.castSucc := by
      ext
      simp
    simp only [hcurrent, hprevious,
      axisPairReflectReverseLeftSpatialScalarCLE_apply_left,
      osiiAxisPairBlockwiseTimeDiffCLE_symm_apply_left]
    rw [Fin.rev_succ, Fin.rev_castSucc]
    have hdiff :=
      section43ScalarDiffCLE_symm_succ_sub_castSucc_spatial
        (splitFirst (r + 1) (r + 1)
          (Fin.append (Fin.cons x0 x) (Fin.cons x0 x)))
        (Fin.rev i)
    have hvalue :
        splitFirst (r + 1) (r + 1)
            (Fin.append (Fin.cons x0 x) (Fin.cons x0 x))
            (Fin.rev i).succ = x (Fin.rev i) := by
      simp
    rw [hvalue] at hdiff
    linarith
  · intro q
    refine Fin.cases ?_ (fun i => ?_) q
    · simp only [Fin.val_natAdd, Fin.append_right, Fin.cons_zero]
      change
        section43ScalarDiffCLE ((r + 1) + (r + 1))
            (axisPairReflectReverseLeftSpatialScalarCLE (r + 1) (r + 1)
              ((osiiAxisPairBlockwiseTimeDiffCLE (r + 1) (r + 1)).symm
                (Fin.append (Fin.cons x0 x) (Fin.cons x0 x))))
            ⟨r + 1, by omega⟩ = 0
      rw [section43ScalarDiffCLE_apply]
      rw [dif_neg (by
        simpa only [Nat.succ_eq_add_one] using Nat.succ_ne_zero r)]
      have hcurrent :
          (⟨r + 1, by omega⟩ :
              Fin ((r + 1) + (r + 1))) =
            Fin.natAdd (r + 1) (0 : Fin (r + 1)) := by
        ext
        simp
      have hprevious :
          (⟨r + 1 - 1, by omega⟩ :
              Fin ((r + 1) + (r + 1))) =
            Fin.castAdd (r + 1) (Fin.last r) := by
        ext
        simp
      simp only [hcurrent, hprevious,
        axisPairReflectReverseLeftSpatialScalarCLE_apply_right,
        axisPairReflectReverseLeftSpatialScalarCLE_apply_left,
        osiiAxisPairBlockwiseTimeDiffCLE_symm_apply_right,
        osiiAxisPairBlockwiseTimeDiffCLE_symm_apply_left]
      have hright0 :
          (section43ScalarDiffCLE (r + 1)).symm
              (splitLast (r + 1) (r + 1)
                (Fin.append (Fin.cons x0 x) (Fin.cons x0 x))) 0 = x0 := by
        rw [section43ScalarDiffCLE_symm_apply]
        rw [Finset.sum_fin_eq_sum_range]
        simp
      have hleft0 :
          (section43ScalarDiffCLE (r + 1)).symm
              (splitFirst (r + 1) (r + 1)
                (Fin.append (Fin.cons x0 x) (Fin.cons x0 x)))
              (Fin.rev (Fin.last r)) = x0 := by
        rw [Fin.rev_last, section43ScalarDiffCLE_symm_apply]
        rw [Finset.sum_fin_eq_sum_range]
        simp
      simpa only [hright0, hleft0, sub_self]
    · simp only [Fin.val_natAdd, Fin.append_right, Fin.cons_succ]
      change
        section43ScalarDiffCLE ((r + 1) + (r + 1))
            (axisPairReflectReverseLeftSpatialScalarCLE (r + 1) (r + 1)
              ((osiiAxisPairBlockwiseTimeDiffCLE (r + 1) (r + 1)).symm
                (Fin.append (Fin.cons x0 x) (Fin.cons x0 x))))
            ⟨r + i.val + 2, by omega⟩ = x i
      rw [section43ScalarDiffCLE_apply]
      rw [dif_neg (by
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using
          Nat.succ_ne_zero (r + i.val + 1))]
      have hcurrent :
          (⟨r + i.val + 2, by omega⟩ :
              Fin ((r + 1) + (r + 1))) =
            Fin.natAdd (r + 1) i.succ := by
        ext
        simp
        omega
      have hprevious :
          (⟨r + i.val + 2 - 1, by omega⟩ :
              Fin ((r + 1) + (r + 1))) =
            Fin.natAdd (r + 1) i.castSucc := by
        ext
        simp
        omega
      simp only [hcurrent, hprevious,
        axisPairReflectReverseLeftSpatialScalarCLE_apply_right,
        osiiAxisPairBlockwiseTimeDiffCLE_symm_apply_right]
      have hdiff :=
        section43ScalarDiffCLE_symm_succ_sub_castSucc_spatial
          (splitLast (r + 1) (r + 1)
            (Fin.append (Fin.cons x0 x) (Fin.cons x0 x))) i
      have hvalue :
          splitLast (r + 1) (r + 1)
              (Fin.append (Fin.cons x0 x) (Fin.cons x0 x)) i.succ = x i := by
        simp
      rw [hvalue] at hdiff
      exact hdiff

/-- The reduced center obtained by applying the reflected block-global chart
to two copies of one absolute block center and then forgetting the common
spatial basepoint. -/
def reflectedSelfPairMarginalSpatialPoint
    (d r : Nat) [NeZero d]
    (y : Fin ((r + 1) * d) -> Real) :
    Fin ((r + (r + 1)) * d) -> Real :=
  splitLast d ((r + (r + 1)) * d)
    (reflectedSelfPairHeadTailSpatialCLE d r
      (reflectedSelfPairDuplicatedSpatialCenter d r y))

/-- The internal spatial tail of one block center.  Its head is omitted
because the reflected marginal integrates the common absolute basepoint. -/
def reflectedSelfPairBlockTailSpatialPoint
    (d r : Nat)
    (y : Fin ((r + 1) * d) -> Real) :
    Fin (r * d) -> Real :=
  fun j =>
    let p := finProdFinEquiv.symm j
    y (finProdFinEquiv (p.1.succ, p.2))

/-- The transformed duplicated center is the canonical reflected self-pair
of the block's internal tail.  In particular, the result is independent of
the common absolute spatial head. -/
theorem reflectedSelfPairMarginalSpatialPoint_eq
    {d r : Nat} [NeZero d]
    (y : Fin ((r + 1) * d) -> Real) :
    reflectedSelfPairMarginalSpatialPoint d r y =
      osiiEquation629ReflectedSelfPairSpatialPoint d r
        (reflectedSelfPairBlockTailSpatialPoint d r y) := by
  funext j
  generalize hp : finProdFinEquiv.symm j = p
  rcases p with ⟨c, mu⟩
  have hj : j = finProdFinEquiv (c, mu) := by
    rw [← hp]
    exact (finProdFinEquiv.apply_symm_apply j).symm
  rw [hj]
  change
    (reflectedSelfPairHeadTailSpatialCLE d r
      (reflectedSelfPairDuplicatedSpatialCenter d r y))
        (Fin.natAdd d (finProdFinEquiv (c, mu))) = _
  simp only [reflectedSelfPairHeadTailSpatialCLE,
    ContinuousLinearEquiv.trans_apply]
  let h : ((r + 1) + (r + 1)) * d =
      d + (r + (r + 1)) * d := by ring
  change
    axisPairBlockGlobalSpatialFlatCLE d (r + 1) (r + 1)
        ((reflectedSelfPairHeadTailCastCLE d r).symm
          (reflectedSelfPairDuplicatedSpatialCenter d r y))
        ((finCongr h).symm
          (Fin.natAdd d (finProdFinEquiv (c, mu)))) = _
  have hindex :
      (finCongr h).symm
          (Fin.natAdd d (finProdFinEquiv (c, mu))) =
        finProdFinEquiv
          (⟨c.val + 1, by omega⟩, mu) := by
    apply Fin.ext
    simp [finProdFinEquiv]
    ring
  rw [hindex]
  rw [axisPairBlockGlobalSpatialFlatCLE_apply]
  simp only [Equiv.symm_apply_apply]
  have hinput :
      (fun q : Fin ((r + 1) + (r + 1)) =>
        (reflectedSelfPairHeadTailCastCLE d r).symm
            (reflectedSelfPairDuplicatedSpatialCenter d r y)
            (finProdFinEquiv (q, mu))) =
        Fin.append
          (Fin.cons (y (finProdFinEquiv (0, mu)))
            (fun i : Fin r => y (finProdFinEquiv (i.succ, mu))))
          (Fin.cons (y (finProdFinEquiv (0, mu)))
            (fun i : Fin r => y (finProdFinEquiv (i.succ, mu)))) := by
    funext q
    change reflectedSelfPairDuplicatedSpatialCenter d r y
        ((finCongr h) (finProdFinEquiv (q, mu))) = _
    refine Fin.addCases ?_ ?_ q
    · intro a
      refine Fin.cases ?_ (fun i => ?_) a <;>
        simp [reflectedSelfPairDuplicatedSpatialCenter,
          reflectedSelfPairFactorIndex]
    · intro b
      rw [reflectedSelfPairDuplicatedSpatialCenter,
        reflectedSelfPairFactorIndex_right d r h b mu,
        Fin.append_right]
      refine Fin.cases ?_ (fun i => ?_) b <;> simp
  rw [hinput]
  have hscalar := axisPairBlockGlobalSpatialScalarCLE_duplicated_tail
    (y (finProdFinEquiv (0, mu)))
    (fun i : Fin r => y (finProdFinEquiv (i.succ, mu))) c
  rw [hscalar]
  simp only [reflectedSelfPairBlockTailSpatialPoint,
    osiiEquation629ReflectedSelfPairSpatialPoint,
    osiiEquation629ReflectedSelfPairSpatialBlocks,
    flattenCLEquivReal_apply, Equiv.symm_apply_apply]
  refine Fin.addCases ?_ ?_ c
  · intro i
    simp
  · intro q
    refine Fin.cases ?_ (fun i => ?_) q <;> simp

/-- Scalar reindexing of the coherent absolute product family to the left
generator block. -/
def generatorLeftBlockSpatialScalarIndex
    {k : Nat}
    (d : Nat) (i : GeneratorIndex k)
    (j : Fin (((i.n - 1) + 1) * d)) : Fin ((k + 1) * d) :=
  let p := finProdFinEquiv.symm j
  finProdFinEquiv
    (i.leftAbsoluteIndex
      (Fin.cast (Nat.sub_add_cancel i.hn) p.1), p.2)

/-- Scalar reindexing of the coherent absolute product family to the right
generator block. -/
def generatorRightBlockSpatialScalarIndex
    {k : Nat}
    (d : Nat) (i : GeneratorIndex k)
    (j : Fin (((i.m - 1) + 1) * d)) : Fin ((k + 1) * d) :=
  let p := finProdFinEquiv.symm j
  finProdFinEquiv
    (i.rightAbsoluteIndex
      (Fin.cast (Nat.sub_add_cancel i.hm) p.1), p.2)

/-- The left block's factorwise approximate identity, inherited from the
single absolute target family. -/
noncomputable def generatorLeftBlockProductApproxIdentity
    {d k : Nat}
    (I : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (i : GeneratorIndex k) :
    Section43ProductTimeApproximateIdentity (((i.n - 1) + 1) * d) :=
  I.reindex (generatorLeftBlockSpatialScalarIndex d i)

/-- The right block's factorwise approximate identity, inherited from the
single absolute target family. -/
noncomputable def generatorRightBlockProductApproxIdentity
    {d k : Nat}
    (I : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (i : GeneratorIndex k) :
    Section43ProductTimeApproximateIdentity (((i.m - 1) + 1) * d) :=
  I.reindex (generatorRightBlockSpatialScalarIndex d i)

/-- Center of the left block product in its native head-plus-tail
coordinates. -/
def generatorLeftBlockSpatialPoint
    {k : Nat}
    (d : Nat) (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real) :
    Fin (((i.n - 1) + 1) * d) -> Real :=
  fun j => prependZeroSpatialPoint d k x
    (generatorLeftBlockSpatialScalarIndex d i j)

/-- Center of the right block product in its native head-plus-tail
coordinates.  Its head is the target bridge coordinate. -/
def generatorRightBlockSpatialPoint
    {k : Nat}
    (d : Nat) (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real) :
    Fin (((i.m - 1) + 1) * d) -> Real :=
  fun j => prependZeroSpatialPoint d k x
    (generatorRightBlockSpatialScalarIndex d i j)

theorem generatorLeftBlock_translatedSpatialParticleFactor
    {d k : Nat}
    (I : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real)
    (N : Nat) (a : Fin ((i.n - 1) + 1)) :
    (I.generatorLeftBlockProductApproxIdentity i
      ).translatedSpatialParticleFactor
        (generatorLeftBlockSpatialPoint d i x) N a =
      I.translatedSpatialParticleFactor
        (prependZeroSpatialPoint d k x) N
        (i.leftAbsoluteIndex
          (Fin.cast (Nat.sub_add_cancel i.hn) a)) := by
  ext z
  simp [generatorLeftBlockProductApproxIdentity,
    generatorLeftBlockSpatialPoint,
    generatorLeftBlockSpatialScalarIndex,
    translatedSpatialParticleFactor, spatialParticleFactor,
    Section43ProductTimeApproximateIdentity.reindex,
    section43TimeProductSource, section43TimeProductTensor,
    SchwartzMap.productTensor_apply]
  apply Finset.prod_congr rfl
  intro mu _hmu
  have hp := finProdFinEquiv.symm_apply_apply (a, mu)
  have hfst := congrArg Prod.fst hp
  have hsnd := congrArg Prod.snd hp
  have hdiv : (finProdFinEquiv (a, mu)).divNat = a := hfst
  have hmod : (finProdFinEquiv (a, mu)).modNat = mu := hsnd
  rw [hdiv, hmod]
  congr 1
  simp [spatialParticlePoint, generatorLeftBlockSpatialPoint,
    generatorLeftBlockSpatialScalarIndex]

theorem generatorRightBlock_translatedSpatialParticleFactor
    {d k : Nat}
    (I : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real)
    (N : Nat) (b : Fin ((i.m - 1) + 1)) :
    (I.generatorRightBlockProductApproxIdentity i
      ).translatedSpatialParticleFactor
        (generatorRightBlockSpatialPoint d i x) N b =
      I.translatedSpatialParticleFactor
        (prependZeroSpatialPoint d k x) N
        (i.rightAbsoluteIndex
          (Fin.cast (Nat.sub_add_cancel i.hm) b)) := by
  ext z
  simp [generatorRightBlockProductApproxIdentity,
    generatorRightBlockSpatialPoint,
    generatorRightBlockSpatialScalarIndex,
    translatedSpatialParticleFactor, spatialParticleFactor,
    Section43ProductTimeApproximateIdentity.reindex,
    section43TimeProductSource, section43TimeProductTensor,
    SchwartzMap.productTensor_apply]
  apply Finset.prod_congr rfl
  intro mu _hmu
  have hp := finProdFinEquiv.symm_apply_apply (b, mu)
  have hfst := congrArg Prod.fst hp
  have hsnd := congrArg Prod.snd hp
  have hdiv : (finProdFinEquiv (b, mu)).divNat = b := hfst
  have hmod : (finProdFinEquiv (b, mu)).modNat = mu := hsnd
  rw [hdiv, hmod]
  congr 1
  simp [spatialParticlePoint, generatorRightBlockSpatialPoint,
    generatorRightBlockSpatialScalarIndex]

theorem generatorLeftBlock_section43Probe_eq_spatialProduct
    {d k : Nat}
    (I : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real)
    (N : Nat) :
    (I.generatorLeftBlockProductApproxIdentity i
      ).toEquation621SpatialApproxIdentity.section43Probe
        (generatorLeftBlockSpatialPoint d i x) N =
      section43SpatialProductCMM d ((i.n - 1) + 1) fun a =>
        I.translatedSpatialParticleFactor
          (prependZeroSpatialPoint d k x) N
          (i.leftAbsoluteIndex
            (Fin.cast (Nat.sub_add_cancel i.hn) a)) := by
  rw [(I.generatorLeftBlockProductApproxIdentity i
    ).section43Probe_eq_spatialProduct]
  congr 1
  funext a
  exact I.generatorLeftBlock_translatedSpatialParticleFactor i x N a

theorem generatorRightBlock_section43Probe_eq_spatialProduct
    {d k : Nat}
    (I : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real)
    (N : Nat) :
    (I.generatorRightBlockProductApproxIdentity i
      ).toEquation621SpatialApproxIdentity.section43Probe
        (generatorRightBlockSpatialPoint d i x) N =
      section43SpatialProductCMM d ((i.m - 1) + 1) fun b =>
        I.translatedSpatialParticleFactor
          (prependZeroSpatialPoint d k x) N
          (i.rightAbsoluteIndex
            (Fin.cast (Nat.sub_add_cancel i.hm) b)) := by
  rw [(I.generatorRightBlockProductApproxIdentity i
    ).section43Probe_eq_spatialProduct]
  congr 1
  funext b
  exact I.generatorRightBlock_translatedSpatialParticleFactor i x N b

theorem generatorLeftBlockSpatialPoint_tail
    {d k : Nat}
    (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real) :
    reflectedSelfPairBlockTailSpatialPoint d (i.n - 1)
        (generatorLeftBlockSpatialPoint d i x) =
      i.leftSpatialCoordinates d x := by
  funext j
  simp [reflectedSelfPairBlockTailSpatialPoint,
    generatorLeftBlockSpatialPoint,
    generatorLeftBlockSpatialScalarIndex,
    prependZeroSpatialPoint,
    GeneratorIndex.leftSpatialCoordinates]
  have hidx :
      i.leftAbsoluteIndex
          (Fin.cast (Nat.sub_add_cancel i.hn) j.divNat.succ) =
        (i.leftGlobalIndex (Fin.rev j.divNat)).succ := by
    apply Fin.ext
    simp [GeneratorIndex.leftGlobalIndex_rev_val]
  rw [hidx]
  rfl

theorem generatorRightBlockSpatialPoint_tail
    {d k : Nat}
    (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real) :
    reflectedSelfPairBlockTailSpatialPoint d (i.m - 1)
        (generatorRightBlockSpatialPoint d i x) =
      i.rightSpatialCoordinates d x := by
  funext j
  simp [reflectedSelfPairBlockTailSpatialPoint,
    generatorRightBlockSpatialPoint,
    generatorRightBlockSpatialScalarIndex,
    prependZeroSpatialPoint,
    GeneratorIndex.rightSpatialCoordinates,
    GeneratorIndex.rightGlobalIndex]
  have hidx :
      i.rightAbsoluteIndex
          (Fin.cast (Nat.sub_add_cancel i.hm) j.divNat.succ) =
        (i.rightGlobalIndex j.divNat).succ := by
    apply Fin.ext
    simp [GeneratorIndex.rightGlobalIndex]
    omega
  rw [hidx]
  simp [GeneratorIndex.rightGlobalIndex]

/-- The transformed left block center is the canonical left reflected
self-pair point used by the equation-`(6.29)` spatial split. -/
theorem generatorLeftBlockSpatialPoint_reflectedSelfPair
    {d k : Nat} [NeZero d]
    (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real) :
    reflectedSelfPairMarginalSpatialPoint d (i.n - 1)
        (generatorLeftBlockSpatialPoint d i x) =
      i.leftReflectedSelfPairSpatialPoint d x := by
  rw [reflectedSelfPairMarginalSpatialPoint_eq,
    generatorLeftBlockSpatialPoint_tail]
  rfl

/-- The transformed right block center is the canonical right reflected
self-pair point used by the equation-`(6.29)` spatial split. -/
theorem generatorRightBlockSpatialPoint_reflectedSelfPair
    {d k : Nat} [NeZero d]
    (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real) :
    reflectedSelfPairMarginalSpatialPoint d (i.m - 1)
        (generatorRightBlockSpatialPoint d i x) =
      i.rightReflectedSelfPairSpatialPoint d x := by
  rw [reflectedSelfPairMarginalSpatialPoint_eq,
    generatorRightBlockSpatialPoint_tail]
  rfl

/-- Exact left diagonal probe identity for a generator split. -/
theorem generatorLeftBlockMarginal_section43Probe_eq
    {d k : Nat} [NeZero d]
    (I : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real)
    (N : Nat) :
    (I.generatorLeftBlockProductApproxIdentity i
      ).reflectedSelfPairMarginalSpatialApproxIdentity.section43Probe
        (i.leftReflectedSelfPairSpatialPoint d x) N =
      osiiMixedSpatialHeadMarginal
        ((I.generatorLeftBlockProductApproxIdentity i
          ).toEquation621SpatialApproxIdentity.section43Probe
            (generatorLeftBlockSpatialPoint d i x) N)
        ((I.generatorLeftBlockProductApproxIdentity i
          ).toEquation621SpatialApproxIdentity.section43Probe
            (generatorLeftBlockSpatialPoint d i x) N) := by
  rw [← generatorLeftBlockSpatialPoint_reflectedSelfPair]
  rw [reflectedSelfPairMarginalSpatialPoint]
  rw [reflectedSelfPairMarginalSpatialApproxIdentity_section43Probe_eq_mixed]
  rw [(I.generatorLeftBlockProductApproxIdentity i
    ).section43Probe_eq_spatialProduct]

/-- Exact right diagonal probe identity for a generator split. -/
theorem generatorRightBlockMarginal_section43Probe_eq
    {d k : Nat} [NeZero d]
    (I : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real)
    (N : Nat) :
    (I.generatorRightBlockProductApproxIdentity i
      ).reflectedSelfPairMarginalSpatialApproxIdentity.section43Probe
        (i.rightReflectedSelfPairSpatialPoint d x) N =
      osiiMixedSpatialHeadMarginal
        ((I.generatorRightBlockProductApproxIdentity i
          ).toEquation621SpatialApproxIdentity.section43Probe
            (generatorRightBlockSpatialPoint d i x) N)
        ((I.generatorRightBlockProductApproxIdentity i
          ).toEquation621SpatialApproxIdentity.section43Probe
            (generatorRightBlockSpatialPoint d i x) N) := by
  rw [← generatorRightBlockSpatialPoint_reflectedSelfPair]
  rw [reflectedSelfPairMarginalSpatialPoint]
  rw [reflectedSelfPairMarginalSpatialApproxIdentity_section43Probe_eq_mixed]
  rw [(I.generatorRightBlockProductApproxIdentity i
    ).section43Probe_eq_spatialProduct]

/-- The marginal reflected self-pair probe is exactly the mixed spatial
marginal of the one-block translated product with itself.  This is the
spatial evaluation identity required by the diagonal reflected-Gram limit. -/
theorem reflectedSelfPairMarginal_section43Probe_eq_mixedSpatialHeadMarginal
    {d r : Nat} [NeZero d]
    (I : Section43ProductTimeApproximateIdentity ((r + 1) * d))
    (y : Fin ((r + 1) * d) -> Real)
    (N : Nat) :
    I.reflectedSelfPairMarginalSpatialApproxIdentity.section43Probe
        (reflectedSelfPairMarginalSpatialPoint d r y) N =
      osiiMixedSpatialHeadMarginal
        (I.toEquation621SpatialApproxIdentity.section43Probe y N)
        (I.toEquation621SpatialApproxIdentity.section43Probe y N) := by
  rw [reflectedSelfPairMarginalSpatialPoint,
    I.reflectedSelfPairMarginalSpatialApproxIdentity_section43Probe_eq]
  rw [← reflectedSelfPair_marginal_flat_eq]
  rw [ContinuousLinearEquiv.symm_apply_apply]
  unfold osiiMixedSpatialHeadMarginal
  rw [I.reflectedSelfPairSeparateSpatialTest_translatedTest_eq_product]
  rw [← I.section43TwoBlockSpatialProduct_self_eq_duplicated]
  rw [I.section43Probe_eq_spatialProduct]

end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
