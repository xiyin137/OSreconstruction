/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621HeadMarginalApproxIdentity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621SpatialChartMeasure
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedProductTargetStageRow











noncomputable section

open Complex MeasureTheory
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity

theorem equation621TargetHeadTailArity
    (d k : Nat) :
    (k + 1) * d = d + k * d := by
  ring

/-- Reindex the coherent full product from flat `(k + 1)`-particle
coordinates to one `d`-dimensional head followed by `k * d` reduced
coordinates. -/
def equation621TargetHeadTailFactorIndex
    (d k : Nat)
    (j : Fin (d + k * d)) : Fin ((k + 1) * d) :=
  (finCongr (equation621TargetHeadTailArity d k)).symm j

/-- The coherent full approximate identity in head-plus-tail coordinates. -/
noncomputable def equation621TargetFullApproxIdentity
    {d k : Nat}
    (P : Section43ProductTimeApproximateIdentity ((k + 1) * d)) :
    Section43ProductTimeApproximateIdentity (d + k * d) :=
  P.reindex (equation621TargetHeadTailFactorIndex d k)

/-- Equality transport from a generator's native concatenated block
coordinates to the common `(k + 1)`-particle flat coordinates. -/
noncomputable def generatorSplitSpatialFlatCastCLE
    {d k : Nat}
    (i : GeneratorIndex k) :
    (Fin ((i.n + i.m) * d) -> Real) ≃L[Real]
      (Fin ((k + 1) * d) -> Real) :=
  ContinuousLinearEquiv.piCongrLeft Real
    (fun _ : Fin ((k + 1) * d) => Real)
    (finCongr (congrArg (fun q => q * d) i.absoluteCard_eq.symm))

/-- The common flat generator chart is the native block chart conjugated by
the split-cardinality transport. -/
theorem generatorSplitGlobalSpatialFlatCLE_eq_cast
    {d k : Nat} [NeZero d]
    (i : GeneratorIndex k) :
    generatorSplitGlobalSpatialFlatCLE (d := d) i =
      (generatorSplitSpatialFlatCastCLE (d := d) i).symm.trans
        ((axisPairBlockGlobalSpatialFlatCLE d i.n i.m).trans
          (generatorSplitSpatialFlatCastCLE (d := d) i)) := by
  ext x j
  rfl

/-- Equality transport from common flat particle coordinates to the
head-plus-reduced-tail presentation. -/
noncomputable def equation621TargetHeadTailCastCLE
    (d k : Nat) :
    (Fin ((k + 1) * d) -> Real) ≃L[Real]
      (Fin (d + k * d) -> Real) :=
  OSReconstruction.OSIIChapterV.section43SpatialHeadTailCast d k

theorem equation621TargetHeadTailCastCLE_measurePreserving
    (d k : Nat) :
    MeasurePreserving
      (equation621TargetHeadTailCastCLE d k
        ).toHomeomorph.toMeasurableEquiv
      (volume : Measure (Fin ((k + 1) * d) -> Real))
      (volume : Measure (Fin (d + k * d) -> Real)) := by
  simpa [equation621TargetHeadTailCastCLE] using
    (volume_measurePreserving_piCongrLeft
      (fun _ : Fin (d + k * d) => Real)
      (finCongr (equation621TargetHeadTailArity d k)))

/-- The split-global chart expressed as one spatial head plus the reduced
target tail. -/
noncomputable def equation621TargetHeadTailSpatialCLE
    {d k : Nat} [NeZero d]
    (i : GeneratorIndex k) :
    (Fin (d + k * d) -> Real) ≃L[Real]
      (Fin (d + k * d) -> Real) :=
  (equation621TargetHeadTailCastCLE d k).symm |>.trans
    ((generatorSplitGlobalSpatialFlatCLE (d := d) i).trans
      (equation621TargetHeadTailCastCLE d k))

theorem equation621TargetHeadTailSpatialCLE_measurePreserving
    {d k : Nat} [NeZero d]
    (i : GeneratorIndex k) :
    MeasurePreserving
      (equation621TargetHeadTailSpatialCLE (d := d) i
        ).toHomeomorph.toMeasurableEquiv
      (volume : Measure (Fin (d + k * d) -> Real))
      (volume : Measure (Fin (d + k * d) -> Real)) := by
  have hcast := equation621TargetHeadTailCastCLE_measurePreserving d k
  exact hcast.symm.trans
    ((generatorSplitGlobalSpatialFlatCLE_measurePreserving
      (d := d) i).trans hcast)

/-- The normalized shrinking target probe in the represented generator's
split-adapted reduced spatial coordinates. -/
noncomputable def equation621SplitTargetSpatialApproxIdentity
    {d k : Nat} [NeZero d]
    (P : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (i : GeneratorIndex k) :
    OSIIEquation621SpatialApproxIdentityData (k * d) :=
  (P.equation621TargetFullApproxIdentity.toEquation621SpatialApproxIdentity
    ).headMarginalPullback
      (equation621TargetHeadTailSpatialCLE (d := d) i)
      (equation621TargetHeadTailSpatialCLE_measurePreserving
        (d := d) i).symm

/-- Regard a head-plus-tail flat test as a full common spatial test. -/
noncomputable def equation621TargetCommonSpatialTest
    (d k : Nat)
    (G : SchwartzMap (Fin (d + k * d) -> Real) Complex) :
    SchwartzMap (Section43SpatialSpace d (k + 1)) Complex :=
  (section43SpatialFlatSchwartzCLE d (k + 1)).symm
    (SchwartzMap.compCLMOfContinuousLinearEquiv Complex
      (equation621TargetHeadTailCastCLE d k) G)

/-- Flattening commutes with the split-global spatial pullback after
conjugating the chart to flat coordinates. -/
theorem section43SpatialFlat_generatorSplitGlobalSpatialPullback
    {d k : Nat} [NeZero d]
    (i : GeneratorIndex k)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) Complex) :
    section43SpatialFlatSchwartzCLE d (k + 1)
        (GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPullbackCLM
          (d := d) i F) =
      SchwartzMap.compCLMOfContinuousLinearEquiv Complex
        (generatorSplitGlobalSpatialFlatCLE (d := d) i).symm
        (section43SpatialFlatSchwartzCLE d (k + 1) F) := by
  ext x
  simp [GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPullbackCLM,
    GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialCLE,
    generatorSplitGlobalSpatialFlatCLE,
    generatorSplitToAbsoluteSpatialCLE,
    section43SpatialFlatSchwartzCLE,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

private theorem equation621_integrateHeadBlock_eq_scv
    {head tail : Nat}
    (F : SchwartzMap (Fin (head + tail) -> Real) Complex) :
    integrateHeadBlock (m := head) (n := tail) F =
      SCV.integrateHeadBlock (m := head) (n := tail) F := by
  rw [← headBlockIntegralCLM_apply]
  induction head with
  | zero => rfl
  | succ head ih =>
      simp only [integrateHeadBlock, headBlockIntegralCLM,
        ContinuousLinearMap.comp_apply, SCV.sliceIntegralCLM_apply]
      exact ih (SCV.sliceIntegral (SCV.reindexSchwartzFin
        (Nat.succ_add head tail) F))

/-- Pulling a full common test to the split chart and taking its spatial head
marginal is ordinary head integration after flat pullback by the explicit
head-tail chart. -/
theorem equation621Target_marginal_flat_eq
    {d k : Nat} [NeZero d]
    (i : GeneratorIndex k)
    (G : SchwartzMap (Fin (d + k * d) -> Real) Complex) :
    section43SpatialFlatSchwartzCLE d k
        (section43SpatialHeadMarginal
          (GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPullbackCLM
            (d := d) i
            (equation621TargetCommonSpatialTest d k G))) =
      integrateHeadBlock
        (SchwartzMap.compCLMOfContinuousLinearEquiv Complex
          (equation621TargetHeadTailSpatialCLE (d := d) i).symm G) := by
  rw [equation621_integrateHeadBlock_eq_scv]
  rw [section43SpatialHeadMarginal]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  rw [section43SpatialFlat_generatorSplitGlobalSpatialPullback]
  ext x
  simp [equation621TargetCommonSpatialTest,
    equation621TargetHeadTailSpatialCLE,
    equation621TargetHeadTailCastCLE,
    OSReconstruction.OSIIChapterV.section43SpatialHeadTailCast,
    generatorSplitGlobalSpatialFlatCLE,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

/-- The common absolute-product center, presented as one spatial head and
the reduced tail. -/
def equation621TargetHeadTailCenter
    (d k : Nat)
    (x : Fin (k * d) -> Real) :
    Fin (d + k * d) -> Real :=
  equation621TargetHeadTailCastCLE d k
    (prependZeroSpatialPoint d k x)

/-- The center seen by the represented target stage after the split-global
chart and integration of the common spatial head. -/
def equation621SplitTargetSpatialPoint
    {d k : Nat} [NeZero d]
    (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real) :
    Fin (k * d) -> Real :=
  splitLast d (k * d)
    (equation621TargetHeadTailSpatialCLE (d := d) i
      (equation621TargetHeadTailCenter d k x))

/-- The reduced generator coordinates split into the left internal gaps and
the bridge-plus-right block. -/
theorem equation621ReducedSplitCard
    {k : Nat} (i : GeneratorIndex k) :
    (i.n - 1) + i.m = k := by
  have hn := i.hn
  have hm := i.hm
  have hnm := i.hnm
  omega

/-- On one spatial coordinate, the represented target chart reverses and
negates the left internal gaps and fixes the bridge-plus-right block. -/
noncomputable def equation621SplitTargetScalarCLE
    {k : Nat} (i : GeneratorIndex k) :
    (Fin k -> Real) ≃L[Real] (Fin k -> Real) :=
  let castCLE :
      (Fin ((i.n - 1) + i.m) -> Real) ≃L[Real] (Fin k -> Real) :=
    ContinuousLinearEquiv.piCongrLeft Real
      (fun _ : Fin k => Real)
      (finCongr (equation621ReducedSplitCard i))
  castCLE.symm.trans
    (((axisPairReflectReverseLeftSpatialScalarCLE (i.n - 1) i.m).trans
      (axisPairNegateLeftScalarCLE (i.n - 1) i.m)).trans castCLE)

/-- Exchange the gap and spatial-coordinate indices in a finite real
coordinate family. -/
private noncomputable def equation621SwapSpatialFibersCLE
    (k d : Nat) :
    (Fin k -> Fin d -> Real) ≃L[Real] (Fin d -> Fin k -> Real) :=
  ({
    toFun := fun x mu c => x c mu
    invFun := fun x c mu => x mu c
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
  } : (Fin k -> Fin d -> Real) ≃ₗ[Real] (Fin d -> Fin k -> Real)
    ).toContinuousLinearEquiv

/-- Flat reduced spatial form of the split-target coordinate change. -/
noncomputable def equation621SplitTargetSpatialCLE
    (d : Nat) {k : Nat} (i : GeneratorIndex k) :
    (Fin (k * d) -> Real) ≃L[Real] (Fin (k * d) -> Real) :=
  (flattenCLEquivReal k d).symm |>.trans
    ((equation621SwapSpatialFibersCLE k d).trans
      ((ContinuousLinearEquiv.piCongrRight fun _ : Fin d =>
          equation621SplitTargetScalarCLE i).trans
        ((equation621SwapSpatialFibersCLE k d).symm.trans
          (flattenCLEquivReal k d))))

@[simp]
theorem equation621SplitTargetScalarCLE_apply_left
    {k : Nat} (i : GeneratorIndex k)
    (x : Fin k -> Real) (a : Fin (i.n - 1)) :
    equation621SplitTargetScalarCLE i x
        (Fin.cast (equation621ReducedSplitCard i) (Fin.castAdd i.m a)) =
      -x (Fin.cast (equation621ReducedSplitCard i)
        (Fin.castAdd i.m (Fin.rev a))) := by
  simp [equation621SplitTargetScalarCLE]

@[simp]
theorem equation621SplitTargetScalarCLE_apply_right
    {k : Nat} (i : GeneratorIndex k)
    (x : Fin k -> Real) (b : Fin i.m) :
    equation621SplitTargetScalarCLE i x
        (Fin.cast (equation621ReducedSplitCard i)
          (Fin.natAdd (i.n - 1) b)) =
      x (Fin.cast (equation621ReducedSplitCard i)
        (Fin.natAdd (i.n - 1) b)) := by
  simp [equation621SplitTargetScalarCLE]

/-- Native block-chart form of the split-target scalar equivalence. -/
theorem axisPairBlockGlobalSpatialScalarCLE_zeroHead_eq_splitTarget
    {k : Nat} (i : GeneratorIndex k)
    (x : Fin k -> Real) (j : Fin ((i.n - 1) + i.m)) :
    axisPairBlockGlobalSpatialScalarCLE i.n i.m
        (axisPairBlockGlobalSpatialScalarZeroHeadOfPositive i.n i.m
          (fun q => x (Fin.cast (equation621ReducedSplitCard i) q)))
        ⟨j.val + 1, by have := i.hn; omega⟩ =
      equation621SplitTargetScalarCLE i x
        (Fin.cast (equation621ReducedSplitCard i) j) := by
  rw [axisPairBlockGlobalSpatialScalarCLE_zeroHeadOfPositive_tail i.hn]
  refine Fin.addCases ?_ ?_ j
  · intro a
    simp
  · intro b
    simp

@[simp]
theorem equation621SplitTargetSpatialCLE_apply
    (d : Nat) {k : Nat} (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real) (j : Fin (k * d)) :
    equation621SplitTargetSpatialCLE d i x j =
      equation621SplitTargetScalarCLE i
        (fun c => x (finProdFinEquiv (c, (finProdFinEquiv.symm j).2)))
        (finProdFinEquiv.symm j).1 := by
  rfl

/-- The geometric center produced by the split-global chart is exactly the
explicit signed-reversal spatial equivalence. -/
theorem equation621SplitTargetSpatialPoint_eq_cle
    {d k : Nat} [NeZero d]
    (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real) :
    equation621SplitTargetSpatialPoint i x =
      equation621SplitTargetSpatialCLE d i x := by
  funext j
  generalize hp : finProdFinEquiv.symm j = p
  rcases p with ⟨c, mu⟩
  have hj : j = finProdFinEquiv (c, mu) := by
    rw [← hp]
    exact (finProdFinEquiv.apply_symm_apply j).symm
  rw [hj]
  rw [equation621SplitTargetSpatialCLE_apply]
  simp only [Equiv.symm_apply_apply]
  change
    equation621TargetHeadTailSpatialCLE (d := d) i
        (equation621TargetHeadTailCenter d k x)
        (Fin.natAdd d (finProdFinEquiv (c, mu))) = _
  simp only [equation621TargetHeadTailSpatialCLE,
    equation621TargetHeadTailCenter,
    equation621TargetHeadTailCastCLE,
    ContinuousLinearEquiv.trans_apply]
  have hindex :
      (finCongr (equation621TargetHeadTailArity d k)).symm
          (Fin.natAdd d (finProdFinEquiv (c, mu))) =
        finProdFinEquiv (c.succ, mu) := by
    apply Fin.ext
    simp [finProdFinEquiv]
    ring
  rw [ContinuousLinearEquiv.symm_apply_apply]
  change
    generatorSplitGlobalSpatialFlatCLE (d := d) i
        (prependZeroSpatialPoint d k x)
        ((finCongr (equation621TargetHeadTailArity d k)).symm
          (Fin.natAdd d (finProdFinEquiv (c, mu)))) = _
  rw [hindex]
  rw [generatorSplitGlobalSpatialFlatCLE_eq_cast]
  simp only [ContinuousLinearEquiv.trans_apply]
  let cNative : Fin (i.n + i.m) :=
    Fin.cast i.absoluteCard_eq c.succ
  change
    axisPairBlockGlobalSpatialFlatCLE d i.n i.m
        ((generatorSplitSpatialFlatCastCLE (d := d) i).symm
          (prependZeroSpatialPoint d k x))
        (finProdFinEquiv (cNative, mu)) = _
  rw [axisPairBlockGlobalSpatialFlatCLE_apply]
  simp only [Equiv.symm_apply_apply]
  let reducedFiber : Fin ((i.n - 1) + i.m) -> Real := fun q =>
    x (finProdFinEquiv
      (Fin.cast (equation621ReducedSplitCard i) q, mu))
  have hinput :
      (fun q : Fin (i.n + i.m) =>
        (generatorSplitSpatialFlatCastCLE (d := d) i).symm
          (prependZeroSpatialPoint d k x)
          (finProdFinEquiv (q, mu))) =
        axisPairBlockGlobalSpatialScalarZeroHeadOfPositive
          i.n i.m reducedFiber := by
    funext q
    simp only [generatorSplitSpatialFlatCastCLE]
    by_cases hq : q.val = 0
    · simp [axisPairBlockGlobalSpatialScalarZeroHeadOfPositive,
        prependZeroSpatialPoint, finProdFinEquiv, hq,
        Nat.mod_eq_of_lt mu.isLt]
      change
        @Fin.cases k (fun _ => Real) 0
            (fun c => x (finProdFinEquiv (c, mu)))
            (finProdFinEquiv ((0 : Fin (k + 1)), mu)).divNat = 0
      have hpair := finProdFinEquiv.symm_apply_apply
        ((0 : Fin (k + 1)), mu)
      have hdiv :
          (finProdFinEquiv ((0 : Fin (k + 1)), mu)).divNat =
            (0 : Fin (k + 1)) := congrArg Prod.fst hpair
      rw [hdiv]
      rfl
    · simp [axisPairBlockGlobalSpatialScalarZeroHeadOfPositive,
        prependZeroSpatialPoint, reducedFiber, finProdFinEquiv, hq,
        Nat.mod_eq_of_lt mu.isLt]
      let qCommon : Fin (k + 1) := Fin.cast i.absoluteCard_eq.symm q
      have hqCommon : qCommon.val ≠ 0 := by
        simpa [qCommon] using hq
      let qTail : Fin k := ⟨qCommon.val - 1, by
        have := qCommon.isLt
        omega⟩
      have hqSucc : qCommon = qTail.succ := by
        apply Fin.ext
        dsimp [qTail]
        omega
      change
        @Fin.cases k (fun _ => Real) 0
            (fun c => x (finProdFinEquiv (c, mu)))
            (finProdFinEquiv (qCommon, mu)).divNat =
          x (finProdFinEquiv (qTail, mu))
      have hpair := finProdFinEquiv.symm_apply_apply (qCommon, mu)
      have hdiv :
          (finProdFinEquiv (qCommon, mu)).divNat = qCommon :=
        congrArg Prod.fst hpair
      rw [hdiv]
      rw [hqSucc]
      rfl
  rw [hinput]
  let cReducedNative : Fin ((i.n - 1) + i.m) :=
    Fin.cast (equation621ReducedSplitCard i).symm c
  have hcNative :
      cNative = ⟨cReducedNative.val + 1, by
        dsimp [cReducedNative]
        have := c.isLt
        have := i.absoluteCard_eq
        omega⟩ := by
    apply Fin.ext
    rfl
  rw [hcNative]
  simpa [reducedFiber, cReducedNative] using
    (axisPairBlockGlobalSpatialScalarCLE_zeroHead_eq_splitTarget
      i (fun q => x (finProdFinEquiv (q, mu))) cReducedNative)

@[simp]
theorem equation621SplitTargetSpatialPoint_apply_left
    {d k : Nat} [NeZero d]
    (i : GeneratorIndex k) (x : Fin (k * d) -> Real)
    (a : Fin (i.n - 1)) (mu : Fin d) :
    equation621SplitTargetSpatialPoint i x
        (finProdFinEquiv
          (Fin.cast (equation621ReducedSplitCard i) (Fin.castAdd i.m a), mu)) =
      -x (finProdFinEquiv
        (Fin.cast (equation621ReducedSplitCard i)
          (Fin.castAdd i.m (Fin.rev a)), mu)) := by
  rw [equation621SplitTargetSpatialPoint_eq_cle]
  simp

@[simp]
theorem equation621SplitTargetSpatialPoint_apply_right
    {d k : Nat} [NeZero d]
    (i : GeneratorIndex k) (x : Fin (k * d) -> Real)
    (b : Fin i.m) (mu : Fin d) :
    equation621SplitTargetSpatialPoint i x
        (finProdFinEquiv
          (Fin.cast (equation621ReducedSplitCard i)
            (Fin.natAdd (i.n - 1) b), mu)) =
      x (finProdFinEquiv
        (Fin.cast (equation621ReducedSplitCard i)
          (Fin.natAdd (i.n - 1) b), mu)) := by
  rw [equation621SplitTargetSpatialPoint_eq_cle]
  simp

/-- The split-target coordinate change is a contraction in the finite
coordinate sup norm. -/
theorem norm_equation621SplitTargetSpatialPoint_le
    {d k : Nat} [NeZero d]
    (i : GeneratorIndex k) (x : Fin (k * d) -> Real) :
    ‖equation621SplitTargetSpatialPoint i x‖ ≤ ‖x‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg x)]
  intro j
  generalize hp : finProdFinEquiv.symm j = p
  rcases p with ⟨c, mu⟩
  have hj : j = finProdFinEquiv (c, mu) := by
    rw [← hp]
    exact (finProdFinEquiv.apply_symm_apply j).symm
  rw [hj]
  let cNative : Fin ((i.n - 1) + i.m) :=
    Fin.cast (equation621ReducedSplitCard i).symm c
  have hc : Fin.cast (equation621ReducedSplitCard i) cNative = c := by
    simp [cNative]
  rw [← hc]
  refine Fin.addCases ?_ ?_ cNative
  · intro a
    simp only [equation621SplitTargetSpatialPoint_apply_left, norm_neg]
    exact norm_le_pi_norm x
      (finProdFinEquiv
        (Fin.cast (equation621ReducedSplitCard i)
          (Fin.castAdd i.m (Fin.rev a)), mu))
  · intro b
    simp only [equation621SplitTargetSpatialPoint_apply_right]
    exact norm_le_pi_norm x
      (finProdFinEquiv
        (Fin.cast (equation621ReducedSplitCard i)
          (Fin.natAdd (i.n - 1) b), mu))

/-- Signed reversal on the left and identity on the right make the
split-target coordinate change an involution. -/
theorem equation621SplitTargetSpatialPoint_involutive
    {d k : Nat} [NeZero d]
    (i : GeneratorIndex k) (x : Fin (k * d) -> Real) :
    equation621SplitTargetSpatialPoint i
        (equation621SplitTargetSpatialPoint i x) = x := by
  funext j
  generalize hp : finProdFinEquiv.symm j = p
  rcases p with ⟨c, mu⟩
  have hj : j = finProdFinEquiv (c, mu) := by
    rw [← hp]
    exact (finProdFinEquiv.apply_symm_apply j).symm
  rw [hj]
  let cNative : Fin ((i.n - 1) + i.m) :=
    Fin.cast (equation621ReducedSplitCard i).symm c
  have hc : Fin.cast (equation621ReducedSplitCard i) cNative = c := by
    simp [cNative]
  rw [← hc]
  refine Fin.addCases ?_ ?_ cNative
  · intro a
    simp
  · intro b
    simp

/-- A translated coherent product in head-tail coordinates is the literal
full absolute-product target test after transport back to Section-4.3
coordinates. -/
theorem equation621TargetCommonSpatialTest_translated_eq
    {d k : Nat} [NeZero d]
    (P : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (x : Fin (k * d) -> Real)
    (N : Nat) :
    equation621TargetCommonSpatialTest d k
        (P.equation621TargetFullApproxIdentity.toEquation621SpatialApproxIdentity.translatedTest
          (equation621TargetHeadTailCenter d k x) N) =
      AnchoredPacketTimeShellFamilyData.RootedA0BlockContinuousTranslationData.absoluteProductTargetFullSpatialTest
        P x N := by
  rw [AnchoredPacketTimeShellFamilyData.RootedA0BlockContinuousTranslationData.absoluteProductTargetFullSpatialTest,
    P.absoluteProduct_basepointLift_targetProbe_eq_product,
    ← P.section43Probe_eq_spatialProduct]
  apply (section43SpatialFlatSchwartzCLE d (k + 1)).injective
  ext y
  let sigma : Fin ((k + 1) * d) ≃ Fin (d + k * d) :=
    finCongr (equation621TargetHeadTailArity d k)
  let F : Fin ((k + 1) * d) -> Complex := fun j =>
    (P.factors N j).f ((y + -prependZeroSpatialPoint d k x) j)
  have hprod : (∏ j, F j) = ∏ l, F (sigma.symm l) :=
    Fintype.prod_equiv sigma F (fun l => F (sigma.symm l))
      (fun _ => rfl)
  simpa [F, sigma, equation621TargetCommonSpatialTest,
    equation621TargetHeadTailCenter,
    equation621TargetFullApproxIdentity,
    equation621TargetHeadTailFactorIndex,
    equation621TargetHeadTailCastCLE,
    OSIIEquation621SpatialApproxIdentityData.section43Probe,
    OSIIEquation621SpatialApproxIdentityData.translatedTest,
    toEquation621SpatialApproxIdentity,
    Section43ProductTimeApproximateIdentity.reindex,
    Section43ProductTimeApproximateIdentity.test_apply,
    section43TimeProductSource,
    section43TimeProductTensor,
    SchwartzMap.productTensor_apply,
    SCV.translateSchwartz_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using hprod.symm

/-- The split-adapted target approximate identity evaluates to the exact
reduced spatial test used by the represented rooted generator stage. -/
theorem equation621SplitTargetSpatialApproxIdentity_section43Probe_eq
    {d k : Nat} [NeZero d] [NeZero k]
    (P : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real)
    (N : Nat) :
    (P.equation621SplitTargetSpatialApproxIdentity i).section43Probe
        (equation621SplitTargetSpatialPoint i x) N =
      AnchoredPacketTimeShellFamilyData.RootedA0BlockContinuousTranslationData.absoluteProductTargetReducedSpatialTest
        P i x N := by
  apply (section43SpatialFlatSchwartzCLE d k).injective
  simp only [OSIIEquation621SpatialApproxIdentityData.section43Probe,
    ContinuousLinearEquiv.apply_symm_apply]
  rw [AnchoredPacketTimeShellFamilyData.RootedA0BlockContinuousTranslationData.absoluteProductTargetReducedSpatialTest,
    AnchoredPacketTimeShellFamilyData.RootedA0BlockContinuousTranslationData.absoluteProductTargetHermiteSpatialTest,
    ← equation621TargetCommonSpatialTest_translated_eq P x N]
  rw [equation621Target_marginal_flat_eq]
  rw [OSIIEquation621SpatialApproxIdentityData.headMarginalPullback_translatedTest]
  rfl

end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
