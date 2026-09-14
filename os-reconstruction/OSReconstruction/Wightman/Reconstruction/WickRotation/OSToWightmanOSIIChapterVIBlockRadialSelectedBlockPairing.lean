/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialSelectedBlockPositiveSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPartialKernelRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReducedSchwinger
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVCompactTimeSource














noncomputable section

open Matrix MeasureTheory
open scoped Classical

namespace OSReconstruction

/-- Reverse the reflected left absolute-point block and leave the right block
fixed.  The left and right blocks have respectively `n + 1` and `m + 1`
absolute points. -/
def osiiStep4SelectedBlockLeftReversePerm
    (n m : Nat) : Equiv.Perm (Fin ((n + 1) + (m + 1))) :=
  (finSumFinEquiv (m := n + 1) (n := m + 1)).symm.trans
    ((Equiv.sumCongr Fin.revPerm (Equiv.refl (Fin (m + 1)))).trans
      (finSumFinEquiv (m := n + 1) (n := m + 1)))

@[simp] theorem osiiStep4SelectedBlockLeftReversePerm_castAdd
    (n m : Nat) (i : Fin (n + 1)) :
    osiiStep4SelectedBlockLeftReversePerm n m
        (Fin.castAdd (m + 1) i) =
      Fin.castAdd (m + 1) (Fin.rev i) := by
  simp [osiiStep4SelectedBlockLeftReversePerm]

@[simp] theorem osiiStep4SelectedBlockLeftReversePerm_natAdd
    (n m : Nat) (j : Fin (m + 1)) :
    osiiStep4SelectedBlockLeftReversePerm n m
        (Fin.natAdd (n + 1) j) =
      Fin.natAdd (n + 1) j := by
  simp [osiiStep4SelectedBlockLeftReversePerm]

/-- The `i`th block strictly before the selected block, in its original
order. -/
def osiiStep4BeforeBlockIndex
    (n m : Nat) (i : Fin n) : Fin (n + 1 + m) :=
  Fin.cast (Nat.add_assoc n 1 m).symm
    (Fin.castAdd (1 + m) i)

@[simp] theorem osiiStep4BeforeBlockIndex_val
    (n m : Nat) (i : Fin n) :
    (osiiStep4BeforeBlockIndex n m i).val = i.val := by
  rfl

theorem osiiStep4ReversedBeforeBlockIndex_eq_before_rev
    (n m : Nat) (i : Fin n) :
    osiiStep4ReversedBeforeBlockIndex n m i =
      osiiStep4BeforeBlockIndex n m (Fin.rev i) := by
  rfl

/-- One original-order block factor in the centered partial-convolution
kernel. -/
def osiiStep4SelectedBlockKernelFactor
    (d n m : Nat) (rho : Real)
    (center y y' : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (xi : NPointDomain d (n + 1 + m))
    (i : Fin (n + 1 + m)) : Real :=
  osiiStep4ComplexBlockPartialConvolutionKernel (d + 1) rho
    (osiiStep4ComplexOfRealImag
      (xi i - fun mu => center (finProdFinEquiv (i, mu)))
      (fun mu => y (finProdFinEquiv (i, mu))))
    (fun mu => y' (finProdFinEquiv (i, mu)))

/-- The selected-block real density after all nonselected one-block kernels
have been left outside the shared endpoint integral. -/
def osiiStep4SelectedBlockConvolutionDensity
    (d n m : Nat) (rho : Real)
    (center y y' : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (xi : NPointDomain d (n + 1 + m))
    (x' : SpacetimeDim d) : Real :=
  (Finset.univ.prod fun i : Fin n =>
      osiiStep4SelectedBlockKernelFactor d n m rho center y y' xi
        (osiiStep4BeforeBlockIndex n m i)) *
    osiiStep4ComplexBlockPartialConvolutionIntegrand (d + 1) rho
      (osiiStep4ComplexOfRealImag
        (xi (osiiStep4SelectedBlockIndex n m) -
          fun mu => center (finProdFinEquiv
            (osiiStep4SelectedBlockIndex n m, mu)))
        (fun mu => y (finProdFinEquiv
          (osiiStep4SelectedBlockIndex n m, mu))))
      (fun mu => y' (finProdFinEquiv
        (osiiStep4SelectedBlockIndex n m, mu))) x' *
    (Finset.univ.prod fun j : Fin m =>
      osiiStep4SelectedBlockKernelFactor d n m rho center y y' xi
        (osiiStep4AfterBlockIndex n m j))

/-- Centering commutes with an orthogonal real action in the one-block
partial kernel. -/
theorem osiiStep4ComplexBlockPartialConvolutionKernel_centered_realMatrix_invariant
    {q : Nat}
    (R : Matrix (Fin q) (Fin q) Real)
    (hR : R.transpose * R = 1)
    (rho : Real) (x center y y' : Fin q -> Real) :
    osiiStep4ComplexBlockPartialConvolutionKernel q rho
        (osiiStep4ComplexOfRealImag
          (R.mulVec x - R.mulVec center) (R.mulVec y))
        (R.mulVec y') =
      osiiStep4ComplexBlockPartialConvolutionKernel q rho
        (osiiStep4ComplexOfRealImag (x - center) y) y' := by
  rw [← Matrix.mulVec_sub]
  rw [← osiiStep4RealMatrixComplexAction_ofRealImag]
  exact osiiStep4ComplexBlockPartialConvolutionKernel_realMatrix_invariant
    R hR rho (osiiStep4ComplexOfRealImag (x - center) y) y'

theorem osiiStep4_prod_beforeBlockIndex_eq_Iio
    (n m : Nat) (F : Fin (n + 1 + m) -> Real) :
    (Finset.univ.prod fun i : Fin n =>
      F (osiiStep4BeforeBlockIndex n m i)) =
      (Finset.Iio (osiiStep4SelectedBlockIndex n m)).prod F := by
  refine Finset.prod_bij
    (fun i (_hi : i ∈ (Finset.univ : Finset (Fin n))) =>
      osiiStep4BeforeBlockIndex n m i) ?_ ?_ ?_ ?_
  · intro i _hi
    rw [Finset.mem_Iio]
    change i.val < n
    exact i.isLt
  · intro i _hi j _hj hij
    apply Fin.ext
    simpa using congrArg Fin.val hij
  · intro b hb
    have hbval : b.val < n := by
      have hlt := Finset.mem_Iio.mp hb
      simpa [osiiStep4SelectedBlockIndex] using hlt
    let i : Fin n := ⟨b.val, hbval⟩
    refine ⟨i, Finset.mem_univ i, ?_⟩
    apply Fin.ext
    rfl
  · intro i _hi
    rfl

theorem osiiStep4_prod_afterBlockIndex_eq_Ioi
    (n m : Nat) (F : Fin (n + 1 + m) -> Real) :
    (Finset.univ.prod fun j : Fin m =>
      F (osiiStep4AfterBlockIndex n m j)) =
      (Finset.Ioi (osiiStep4SelectedBlockIndex n m)).prod F := by
  refine Finset.prod_bij
    (fun j (_hj : j ∈ (Finset.univ : Finset (Fin m))) =>
      osiiStep4AfterBlockIndex n m j) ?_ ?_ ?_ ?_
  · intro j _hj
    rw [Finset.mem_Ioi]
    change n < n + 1 + j.val
    omega
  · intro i _hi j _hj hij
    apply Fin.ext
    have hval := congrArg Fin.val hij
    simp [osiiStep4AfterBlockIndex] at hval
    omega
  · intro b hb
    have hbgt : n < b.val := by
      have hlt := Finset.mem_Ioi.mp hb
      simpa [osiiStep4SelectedBlockIndex] using hlt
    let j : Fin m := ⟨b.val - (n + 1), by omega⟩
    refine ⟨j, Finset.mem_univ j, ?_⟩
    apply Fin.ext
    simp [j, osiiStep4AfterBlockIndex]
    omega
  · intro j _hj
    rfl

/-- Pointwise selected-block expansion of the complete centered reduced
source, expressed with the original-order blocks on either side. -/
theorem osiiStep4CenteredPartialConvolutionKernelFullSource_apply_eq_integral_selectedDensity
    (d n m : Nat) {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (xi : NPointDomain d (n + 1 + m)) :
    osiiStep4CenteredPartialConvolutionKernelFullSource
        d (n + 1 + m) hrho center y y' xi =
      ((∫ x' : SpacetimeDim d,
        osiiStep4SelectedBlockConvolutionDensity
          d n m rho center y y' xi x' : Real) : Complex) := by
  change
    osiiStep4CenteredPartialConvolutionKernelComplexSchwartz
        (d + 1) (n + 1 + m) hrho center y y'
          (flattenCLEquivReal (n + 1 + m) (d + 1) xi) = _
  rw [osiiStep4CenteredPartialConvolutionKernelComplexSchwartz_apply_eq_integral_orderedSelectedBlock
    (d + 1) (n + 1 + m) hrho center y y'
      (flattenCLEquivReal (n + 1 + m) (d + 1) xi)
      (osiiStep4SelectedBlockIndex n m)]
  congr 1
  apply integral_congr_ae
  filter_upwards with x'
  simp only [flattenCLEquivReal_apply, Equiv.symm_apply_apply]
  let F : Fin (n + 1 + m) -> Real := fun i =>
    osiiStep4ComplexBlockPartialConvolutionKernel (d + 1) rho
      (osiiStep4ComplexOfRealImag
        (fun mu => xi i mu - center (finProdFinEquiv (i, mu)))
        (fun mu => y (finProdFinEquiv (i, mu))))
      (fun mu => y' (finProdFinEquiv (i, mu)))
  let C : Real :=
    osiiStep4ComplexBlockPartialConvolutionIntegrand (d + 1) rho
      (osiiStep4ComplexOfRealImag
        (xi (osiiStep4SelectedBlockIndex n m) -
          fun mu => center (finProdFinEquiv
            (osiiStep4SelectedBlockIndex n m, mu)))
        (fun mu => y (finProdFinEquiv
          (osiiStep4SelectedBlockIndex n m, mu))))
      (fun mu => y' (finProdFinEquiv
        (osiiStep4SelectedBlockIndex n m, mu))) x'
  change
    (Finset.Iio (osiiStep4SelectedBlockIndex n m)).prod F * C *
        (Finset.Ioi (osiiStep4SelectedBlockIndex n m)).prod F =
      (Finset.univ.prod fun i : Fin n =>
          F (osiiStep4BeforeBlockIndex n m i)) * C *
        (Finset.univ.prod fun j : Fin m =>
          F (osiiStep4AfterBlockIndex n m j))
  rw [osiiStep4_prod_beforeBlockIndex_eq_Iio,
    osiiStep4_prod_afterBlockIndex_eq_Ioi]

/-- The positive-time left configuration recovered from a chronologically
ordered absolute configuration: reverse the left block and then undo its OS
time reflection. -/
def osiiStep4SelectedBlockChronologicalLeftConfig
    (d n m : Nat)
    (x : NPointDomain d ((n + 1) + (m + 1))) :
    NPointDomain d (n + 1) :=
  timeReflectionN d
    (splitFirst (n + 1) (m + 1)
      (fun i => x (osiiStep4SelectedBlockLeftReversePerm n m i)))

/-- The positive-time right configuration recovered from a chronologically
ordered absolute configuration. -/
def osiiStep4SelectedBlockChronologicalRightConfig
    (d n m : Nat)
    (x : NPointDomain d ((n + 1) + (m + 1))) :
    NPointDomain d (m + 1) :=
  splitLast (n + 1) (m + 1)
    (fun i => x (osiiStep4SelectedBlockLeftReversePerm n m i))

@[simp] theorem osiiStep4SelectedBlockChronologicalLeftConfig_apply
    (d n m : Nat)
    (x : NPointDomain d ((n + 1) + (m + 1)))
    (i : Fin (n + 1)) :
    osiiStep4SelectedBlockChronologicalLeftConfig d n m x i =
      timeReflection d (x (Fin.castAdd (m + 1) (Fin.rev i))) := by
  simp [osiiStep4SelectedBlockChronologicalLeftConfig,
    timeReflectionN, splitFirst]

@[simp] theorem osiiStep4SelectedBlockChronologicalRightConfig_apply
    (d n m : Nat)
    (x : NPointDomain d ((n + 1) + (m + 1)))
    (j : Fin (m + 1)) :
    osiiStep4SelectedBlockChronologicalRightConfig d n m x j =
      x (Fin.natAdd (n + 1) j) := by
  simp [osiiStep4SelectedBlockChronologicalRightConfig, splitLast]

theorem osiiStep4EuclideanParityMatrix_mulVec_timeReflection
    (d : Nat) (x : SpacetimeDim d) :
    (osiiStep4EuclideanParityMatrix d).mulVec (timeReflection d x) = -x := by
  ext mu
  by_cases hmu : mu = 0
  · subst mu
    simp [timeReflection]
  · simp [timeReflection, hmu]

/-- The first point of the recovered left source is the reflection of the
last point in the chronological left block. -/
theorem osiiStep4SelectedBlockChronologicalLeftConfig_zero
    (d n m : Nat)
    (x : NPointDomain d ((n + 1) + (m + 1))) :
    osiiStep4SelectedBlockChronologicalLeftConfig d n m x 0 =
      timeReflection d
        (x (Fin.castAdd (m + 1) (Fin.last n))) := by
  simp

/-- The first point of the recovered right source is the first point after
the chronological left block. -/
theorem osiiStep4SelectedBlockChronologicalRightConfig_zero
    (d n m : Nat)
    (x : NPointDomain d ((n + 1) + (m + 1))) :
    osiiStep4SelectedBlockChronologicalRightConfig d n m x 0 =
      x (Fin.natAdd (n + 1) (0 : Fin (m + 1))) := by
  simp

/-- The bridge between the two recovered endpoint points is the selected
consecutive difference in the chronological configuration. -/
theorem osiiStep4SelectedBlockChronologicalEndpoint_sum
    (d n m : Nat)
    (x : NPointDomain d ((n + 1) + (m + 1))) :
    (osiiStep4EuclideanParityMatrix d).mulVec
          (osiiStep4SelectedBlockChronologicalLeftConfig d n m x 0) +
        osiiStep4SelectedBlockChronologicalRightConfig d n m x 0 =
      BHW.reducedDiffMapReal ((n + 1) + (m + 1)) d x
        (osiiStep4SelectedBlockIndex n m) := by
  rw [osiiStep4SelectedBlockChronologicalLeftConfig_zero,
    osiiStep4SelectedBlockChronologicalRightConfig_zero,
    osiiStep4EuclideanParityMatrix_mulVec_timeReflection]
  ext mu
  rw [BHW.reducedDiffMapReal_apply]
  have hsucc :
      (⟨(osiiStep4SelectedBlockIndex n m).val + 1,
          by omega⟩ : Fin ((n + 1) + (m + 1))) =
        Fin.natAdd (n + 1) (0 : Fin (m + 1)) := by
    apply Fin.ext
    simp [osiiStep4SelectedBlockIndex]
  have hcast :
      (⟨(osiiStep4SelectedBlockIndex n m).val,
          by omega⟩ : Fin ((n + 1) + (m + 1))) =
        Fin.castAdd (m + 1) (Fin.last n) := by
    apply Fin.ext
    simp [osiiStep4SelectedBlockIndex]
  rw [hsucc, hcast]
  simp only [Pi.add_apply, Pi.neg_apply]
  ring

/-- A recovered left difference is parity applied to the corresponding
chronological difference before the selected block, read in reverse order. -/
theorem osiiStep4SelectedBlockChronologicalLeft_reducedDiff
    (d n m : Nat)
    (x : NPointDomain d ((n + 1) + (m + 1)))
    (i : Fin n) :
    BHW.reducedDiffMapReal (n + 1) d
        (osiiStep4SelectedBlockChronologicalLeftConfig d n m x) i =
      (osiiStep4EuclideanParityMatrix d).mulVec
        (BHW.reducedDiffMapReal ((n + 1) + (m + 1)) d x
          (osiiStep4ReversedBeforeBlockIndex n m i)) := by
  have hrevSucc :
      Fin.castAdd (m + 1) (Fin.rev i.succ) =
        (osiiStep4ReversedBeforeBlockIndex n m i).castSucc := by
    apply Fin.ext
    simp [osiiStep4ReversedBeforeBlockIndex]
  have hrevCastSucc :
      Fin.castAdd (m + 1) (Fin.rev i.castSucc) =
        (osiiStep4ReversedBeforeBlockIndex n m i).succ := by
    apply Fin.ext
    simp [osiiStep4ReversedBeforeBlockIndex]
    omega
  ext mu
  rw [BHW.reducedDiffMapReal_apply,
    osiiStep4EuclideanParityMatrix_mulVec_apply,
    BHW.reducedDiffMapReal_apply]
  change
    osiiStep4SelectedBlockChronologicalLeftConfig d n m x i.succ mu -
        osiiStep4SelectedBlockChronologicalLeftConfig d n m x i.castSucc mu =
      if mu = 0 then
        x (osiiStep4ReversedBeforeBlockIndex n m i).succ mu -
          x (osiiStep4ReversedBeforeBlockIndex n m i).castSucc mu
      else
        -(x (osiiStep4ReversedBeforeBlockIndex n m i).succ mu -
          x (osiiStep4ReversedBeforeBlockIndex n m i).castSucc mu)
  rw [osiiStep4SelectedBlockChronologicalLeftConfig_apply,
    osiiStep4SelectedBlockChronologicalLeftConfig_apply,
    hrevSucc, hrevCastSucc]
  by_cases hmu : mu = 0
  · subst mu
    simp [timeReflection]
    ring
  · simp [timeReflection, hmu]

/-- A recovered right difference is the corresponding chronological
difference after the selected block. -/
theorem osiiStep4SelectedBlockChronologicalRight_reducedDiff
    (d n m : Nat)
    (x : NPointDomain d ((n + 1) + (m + 1)))
    (j : Fin m) :
    BHW.reducedDiffMapReal (m + 1) d
        (osiiStep4SelectedBlockChronologicalRightConfig d n m x) j =
      BHW.reducedDiffMapReal ((n + 1) + (m + 1)) d x
        (osiiStep4AfterBlockIndex n m j) := by
  have hsucc :
      Fin.natAdd (n + 1) j.succ =
        (osiiStep4AfterBlockIndex n m j).succ := by
    apply Fin.ext
    simp [osiiStep4AfterBlockIndex]
    omega
  have hcast :
      Fin.natAdd (n + 1) j.castSucc =
        (osiiStep4AfterBlockIndex n m j).castSucc := by
    apply Fin.ext
    simp [osiiStep4AfterBlockIndex]
  ext mu
  rw [BHW.reducedDiffMapReal_apply, BHW.reducedDiffMapReal_apply]
  rw [osiiStep4SelectedBlockChronologicalRightConfig_apply,
    osiiStep4SelectedBlockChronologicalRightConfig_apply]
  have hjSucc :
      (⟨j.val + 1, by omega⟩ : Fin (m + 1)) = j.succ := by
    apply Fin.ext
    rfl
  have hjCast :
      (⟨j.val, by omega⟩ : Fin (m + 1)) = j.castSucc := by
    apply Fin.ext
    rfl
  have hrSucc :
      (⟨(osiiStep4AfterBlockIndex n m j).val + 1,
          by omega⟩ : Fin ((n + 1) + (m + 1))) =
        (osiiStep4AfterBlockIndex n m j).succ := by
    apply Fin.ext
    rfl
  have hrCast :
      (⟨(osiiStep4AfterBlockIndex n m j).val,
          by omega⟩ : Fin ((n + 1) + (m + 1))) =
        (osiiStep4AfterBlockIndex n m j).castSucc := by
    apply Fin.ext
    rfl
  rw [hjSucc, hjCast, hrSucc, hrCast, hsucc, hcast]

/-- The reduced partial-kernel factor of the recovered left source is the
product of the original blocks before the selected block.  Orthogonal parity
covariance removes the parity action, and commutativity removes the reversal. -/
theorem osiiStep4SelectedBlockLeftPartialSource_apply_eq_prod
    (d n m : Nat) [NeZero d] {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (x : NPointDomain d ((n + 1) + (m + 1))) :
    osiiStep4CenteredPartialConvolutionKernelFullSource d n hrho
        (osiiStep4ParityReversedBeforeRealBlocks d n m center)
        (osiiStep4ParityReversedBeforeRealBlocks d n m y)
        (osiiStep4ParityReversedBeforeRealBlocks d n m y')
        (BHW.reducedDiffMapReal (n + 1) d
          (osiiStep4SelectedBlockChronologicalLeftConfig d n m x)) =
      Finset.univ.prod fun i : Fin n =>
        (osiiStep4SelectedBlockKernelFactor d n m rho center y y'
          (BHW.reducedDiffMapReal ((n + 1) + (m + 1)) d x)
          (osiiStep4BeforeBlockIndex n m i) : Complex) := by
  let xi : NPointDomain d (n + 1 + m) :=
    BHW.reducedDiffMapReal ((n + 1) + (m + 1)) d x
  calc
    osiiStep4CenteredPartialConvolutionKernelFullSource d n hrho
          (osiiStep4ParityReversedBeforeRealBlocks d n m center)
          (osiiStep4ParityReversedBeforeRealBlocks d n m y)
          (osiiStep4ParityReversedBeforeRealBlocks d n m y')
          (BHW.reducedDiffMapReal (n + 1) d
            (osiiStep4SelectedBlockChronologicalLeftConfig d n m x)) =
        Finset.univ.prod fun i : Fin n =>
          (osiiStep4SelectedBlockKernelFactor d n m rho center y y' xi
            (osiiStep4ReversedBeforeBlockIndex n m i) : Complex) := by
      change
        osiiStep4CenteredPartialConvolutionKernelComplexSchwartz
            (d + 1) n hrho
            (osiiStep4ParityReversedBeforeRealBlocks d n m center)
            (osiiStep4ParityReversedBeforeRealBlocks d n m y)
            (osiiStep4ParityReversedBeforeRealBlocks d n m y')
            (flattenCLEquivReal n (d + 1)
              (BHW.reducedDiffMapReal (n + 1) d
                (osiiStep4SelectedBlockChronologicalLeftConfig d n m x))) = _
      rw [osiiStep4CenteredPartialConvolutionKernelComplexSchwartz_apply_eq_prod]
      apply Finset.prod_congr rfl
      intro i _hi
      have hxi :
          (fun mu =>
            flattenCLEquivReal n (d + 1)
                (BHW.reducedDiffMapReal (n + 1) d
                  (osiiStep4SelectedBlockChronologicalLeftConfig d n m x))
              (finProdFinEquiv (i, mu))) =
            (osiiStep4EuclideanParityMatrix d).mulVec
              (xi (osiiStep4ReversedBeforeBlockIndex n m i)) := by
        ext mu
        simpa [xi] using congrFun
          (osiiStep4SelectedBlockChronologicalLeft_reducedDiff d n m x i) mu
      let c : SpacetimeDim d := fun mu =>
        center (finProdFinEquiv
          (osiiStep4ReversedBeforeBlockIndex n m i, mu))
      let eta : SpacetimeDim d := fun mu =>
        y (finProdFinEquiv
          (osiiStep4ReversedBeforeBlockIndex n m i, mu))
      let eta' : SpacetimeDim d := fun mu =>
        y' (finProdFinEquiv
          (osiiStep4ReversedBeforeBlockIndex n m i, mu))
      have hc :
          (fun mu =>
            osiiStep4ParityReversedBeforeRealBlocks d n m center
              (finProdFinEquiv (i, mu))) =
            (osiiStep4EuclideanParityMatrix d).mulVec c := by
        ext mu
        simp [c]
      have hreal :
          (fun mu =>
            flattenCLEquivReal n (d + 1)
                (BHW.reducedDiffMapReal (n + 1) d
                  (osiiStep4SelectedBlockChronologicalLeftConfig d n m x))
              (finProdFinEquiv (i, mu)) -
            osiiStep4ParityReversedBeforeRealBlocks d n m center
              (finProdFinEquiv (i, mu))) =
            (osiiStep4EuclideanParityMatrix d).mulVec
                (xi (osiiStep4ReversedBeforeBlockIndex n m i)) -
              (osiiStep4EuclideanParityMatrix d).mulVec c := by
        change
          (fun mu =>
            flattenCLEquivReal n (d + 1)
                (BHW.reducedDiffMapReal (n + 1) d
                  (osiiStep4SelectedBlockChronologicalLeftConfig d n m x))
              (finProdFinEquiv (i, mu))) -
            (fun mu =>
              osiiStep4ParityReversedBeforeRealBlocks d n m center
                (finProdFinEquiv (i, mu))) = _
        rw [hxi, hc]
      have heta :
          (fun mu =>
            osiiStep4ParityReversedBeforeRealBlocks d n m y
              (finProdFinEquiv (i, mu))) =
            (osiiStep4EuclideanParityMatrix d).mulVec eta := by
        ext mu
        simp [eta]
      have heta' :
          (fun mu =>
            osiiStep4ParityReversedBeforeRealBlocks d n m y'
              (finProdFinEquiv (i, mu))) =
            (osiiStep4EuclideanParityMatrix d).mulVec eta' := by
        ext mu
        simp [eta']
      rw [hreal, heta, heta']
      norm_cast
      change
        osiiStep4ComplexBlockPartialConvolutionKernel (d + 1) rho
            (osiiStep4ComplexOfRealImag
              ((osiiStep4EuclideanParityMatrix d).mulVec
                  (xi (osiiStep4ReversedBeforeBlockIndex n m i)) -
                (osiiStep4EuclideanParityMatrix d).mulVec c)
              ((osiiStep4EuclideanParityMatrix d).mulVec eta))
            ((osiiStep4EuclideanParityMatrix d).mulVec eta') =
          osiiStep4ComplexBlockPartialConvolutionKernel (d + 1) rho
            (osiiStep4ComplexOfRealImag
              (xi (osiiStep4ReversedBeforeBlockIndex n m i) - c) eta) eta'
      exact
        osiiStep4ComplexBlockPartialConvolutionKernel_centered_realMatrix_invariant
          (osiiStep4EuclideanParityMatrix d)
          (osiiStep4EuclideanParityMatrix_orthogonal d) rho
          (xi (osiiStep4ReversedBeforeBlockIndex n m i)) c eta eta'
    _ = Finset.univ.prod fun i : Fin n =>
          (osiiStep4SelectedBlockKernelFactor d n m rho center y y' xi
            (osiiStep4BeforeBlockIndex n m i) : Complex) := by
      exact Fintype.prod_equiv Fin.revPerm
        (fun i : Fin n =>
          (osiiStep4SelectedBlockKernelFactor d n m rho center y y' xi
            (osiiStep4ReversedBeforeBlockIndex n m i) : Complex))
        (fun i : Fin n =>
          (osiiStep4SelectedBlockKernelFactor d n m rho center y y' xi
            (osiiStep4BeforeBlockIndex n m i) : Complex))
        (fun i => by
          change
            (osiiStep4SelectedBlockKernelFactor d n m rho center y y' xi
              (osiiStep4ReversedBeforeBlockIndex n m i) : Complex) =
            osiiStep4SelectedBlockKernelFactor d n m rho center y y' xi
              (osiiStep4BeforeBlockIndex n m (Fin.rev i))
          rw [osiiStep4ReversedBeforeBlockIndex_eq_before_rev])

/-- The reduced partial-kernel factor of the recovered right source is the
product of the original blocks after the selected block. -/
theorem osiiStep4SelectedBlockRightPartialSource_apply_eq_prod
    (d n m : Nat) [NeZero d] {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (x : NPointDomain d ((n + 1) + (m + 1))) :
    osiiStep4CenteredPartialConvolutionKernelFullSource d m hrho
        (osiiStep4AfterRealBlocks n m (d + 1) center)
        (osiiStep4AfterRealBlocks n m (d + 1) y)
        (osiiStep4AfterRealBlocks n m (d + 1) y')
        (BHW.reducedDiffMapReal (m + 1) d
          (osiiStep4SelectedBlockChronologicalRightConfig d n m x)) =
      Finset.univ.prod fun j : Fin m =>
        (osiiStep4SelectedBlockKernelFactor d n m rho center y y'
          (BHW.reducedDiffMapReal ((n + 1) + (m + 1)) d x)
          (osiiStep4AfterBlockIndex n m j) : Complex) := by
  let xi : NPointDomain d (n + 1 + m) :=
    BHW.reducedDiffMapReal ((n + 1) + (m + 1)) d x
  change
    osiiStep4CenteredPartialConvolutionKernelComplexSchwartz
        (d + 1) m hrho
        (osiiStep4AfterRealBlocks n m (d + 1) center)
        (osiiStep4AfterRealBlocks n m (d + 1) y)
        (osiiStep4AfterRealBlocks n m (d + 1) y')
        (flattenCLEquivReal m (d + 1)
          (BHW.reducedDiffMapReal (m + 1) d
            (osiiStep4SelectedBlockChronologicalRightConfig d n m x))) = _
  rw [osiiStep4CenteredPartialConvolutionKernelComplexSchwartz_apply_eq_prod]
  apply Finset.prod_congr rfl
  intro j _hj
  have hxi :
      (fun mu =>
        flattenCLEquivReal m (d + 1)
            (BHW.reducedDiffMapReal (m + 1) d
              (osiiStep4SelectedBlockChronologicalRightConfig d n m x))
          (finProdFinEquiv (j, mu))) =
        xi (osiiStep4AfterBlockIndex n m j) := by
    ext mu
    simpa [xi] using congrFun
      (osiiStep4SelectedBlockChronologicalRight_reducedDiff d n m x j) mu
  have hc :
      (fun mu => osiiStep4AfterRealBlocks n m (d + 1) center
        (finProdFinEquiv (j, mu))) =
        fun mu => center (finProdFinEquiv
          (osiiStep4AfterBlockIndex n m j, mu)) := by
    ext mu
    simp
  have heta :
      (fun mu => osiiStep4AfterRealBlocks n m (d + 1) y
        (finProdFinEquiv (j, mu))) =
        fun mu => y (finProdFinEquiv
          (osiiStep4AfterBlockIndex n m j, mu)) := by
    ext mu
    simp
  have heta' :
      (fun mu => osiiStep4AfterRealBlocks n m (d + 1) y'
        (finProdFinEquiv (j, mu))) =
        fun mu => y' (finProdFinEquiv
          (osiiStep4AfterBlockIndex n m j, mu)) := by
    ext mu
    simp
  have hreal :
      (fun mu =>
        flattenCLEquivReal m (d + 1)
            (BHW.reducedDiffMapReal (m + 1) d
              (osiiStep4SelectedBlockChronologicalRightConfig d n m x))
          (finProdFinEquiv (j, mu)) -
        osiiStep4AfterRealBlocks n m (d + 1) center
          (finProdFinEquiv (j, mu))) =
        xi (osiiStep4AfterBlockIndex n m j) -
          (fun mu => center (finProdFinEquiv
            (osiiStep4AfterBlockIndex n m j, mu))) := by
    change
      (fun mu =>
        flattenCLEquivReal m (d + 1)
            (BHW.reducedDiffMapReal (m + 1) d
              (osiiStep4SelectedBlockChronologicalRightConfig d n m x))
          (finProdFinEquiv (j, mu))) -
        (fun mu => osiiStep4AfterRealBlocks n m (d + 1) center
          (finProdFinEquiv (j, mu))) = _
    rw [hxi, hc]
  rw [hreal, heta, heta']
  rfl

/-- On a chronological absolute configuration, the two endpoint radial
factors are exactly the selected-block convolution factor. -/
theorem osiiStep4SelectedBlockChronologicalEndpointRadialProduct_eq
    (d n m : Nat)
    (rho : Real)
    (center y y' : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (x : NPointDomain d ((n + 1) + (m + 1))) :
    osiiStep4ComplexBlockRadialG (d + 1) rho
        (osiiStep4ComplexOfRealImag
          (osiiStep4SelectedBlockChronologicalLeftConfig d n m x 0 -
            osiiStep4SelectedBlockLeftEndpointCenter d n m center)
          (osiiStep4SelectedBlockLeftEndpointImag d n m y y')) *
      osiiStep4ComplexBlockRadialG (d + 1) rho
        (osiiStep4ComplexOfRealImag
          (osiiStep4SelectedBlockChronologicalRightConfig d n m x 0 -
            osiiStep4SelectedBlockRightEndpointCenter d n m center)
          (osiiStep4SelectedBlockRightEndpointImag d n m y')) =
    osiiStep4ComplexBlockPartialConvolutionIntegrand (d + 1) rho
      (osiiStep4ComplexOfRealImag
        (BHW.reducedDiffMapReal ((n + 1) + (m + 1)) d x
            (osiiStep4SelectedBlockIndex n m) -
          osiiStep4SelectedRealBlock n m (d + 1) center)
        (osiiStep4SelectedRealBlock n m (d + 1) y))
      (osiiStep4SelectedRealBlock n m (d + 1) y')
      (osiiStep4SelectedBlockChronologicalRightConfig d n m x 0 -
        osiiStep4SelectedBlockRightEndpointCenter d n m center) := by
  rw [osiiStep4SelectedBlockEndpointRadialProduct_eq_integrand]
  rw [osiiStep4SelectedBlockChronologicalEndpoint_sum]

/-- Chronologically reorder an OS reflected tensor product by reversing its
left absolute-point block. -/
noncomputable def osiiStep4SelectedBlockChronologicalOSSource
    (d n m : Nat) [NeZero d]
    (f : SchwartzNPoint d (n + 1))
    (g : SchwartzNPoint d (m + 1)) :
    SchwartzNPoint d ((n + 1) + (m + 1)) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv Complex
    ((LinearEquiv.funCongrLeft Real (SpacetimeDim d)
      (osiiStep4SelectedBlockLeftReversePerm n m)).toContinuousLinearEquiv)
    (f.osConjTensorProduct g)

@[simp] theorem osiiStep4SelectedBlockChronologicalOSSource_apply
    (d n m : Nat) [NeZero d]
    (f : SchwartzNPoint d (n + 1))
    (g : SchwartzNPoint d (m + 1))
    (x : NPointDomain d ((n + 1) + (m + 1))) :
    osiiStep4SelectedBlockChronologicalOSSource d n m f g x =
      star (f (osiiStep4SelectedBlockChronologicalLeftConfig d n m x)) *
        g (osiiStep4SelectedBlockChronologicalRightConfig d n m x) := by
  simp [osiiStep4SelectedBlockChronologicalOSSource,
    SchwartzNPoint.osConjTensorProduct, SchwartzMap.tensorProduct_apply,
    SchwartzNPoint.osConj_apply,
    osiiStep4SelectedBlockChronologicalLeftConfig,
    osiiStep4SelectedBlockChronologicalRightConfig]

/-- Reconstruct the chronological absolute configuration from the two
positive-time source configurations. -/
def osiiStep4SelectedBlockChronologicalConfigOfPair
    (d n m : Nat)
    (p : NPointDomain d (n + 1) × NPointDomain d (m + 1)) :
    NPointDomain d ((n + 1) + (m + 1)) :=
  fun i =>
    Fin.append (timeReflectionN d p.1) p.2
      (osiiStep4SelectedBlockLeftReversePerm n m i)

@[simp] theorem osiiStep4SelectedBlockChronologicalConfigOfPair_castAdd
    (d n m : Nat)
    (p : NPointDomain d (n + 1) × NPointDomain d (m + 1))
    (i : Fin (n + 1)) :
    osiiStep4SelectedBlockChronologicalConfigOfPair d n m p
        (Fin.castAdd (m + 1) i) =
      timeReflection d (p.1 (Fin.rev i)) := by
  simp [osiiStep4SelectedBlockChronologicalConfigOfPair, timeReflectionN]

@[simp] theorem osiiStep4SelectedBlockChronologicalConfigOfPair_natAdd
    (d n m : Nat)
    (p : NPointDomain d (n + 1) × NPointDomain d (m + 1))
    (j : Fin (m + 1)) :
    osiiStep4SelectedBlockChronologicalConfigOfPair d n m p
        (Fin.natAdd (n + 1) j) = p.2 j := by
  simp [osiiStep4SelectedBlockChronologicalConfigOfPair]

private theorem osiiStep4_continuous_timeReflectionN
    (d k : Nat) :
    Continuous (timeReflectionN d : NPointDomain d k -> NPointDomain d k) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro mu
  by_cases hmu : mu = 0
  · subst mu
    simpa [timeReflectionN, timeReflection] using
      ((((continuous_apply 0 : Continuous fun y : SpacetimeDim d => y 0).comp
        (continuous_apply i : Continuous fun x : NPointDomain d k => x i))).neg)
  · simpa [timeReflectionN, timeReflection, hmu] using
      ((continuous_apply mu : Continuous fun y : SpacetimeDim d => y mu).comp
        (continuous_apply i : Continuous fun x : NPointDomain d k => x i))

private theorem osiiStep4_continuous_append_reflected_pair
    (d n m : Nat) :
    Continuous (fun p : NPointDomain d (n + 1) × NPointDomain d (m + 1) =>
      Fin.append (timeReflectionN d p.1) p.2) := by
  let leftMap := fun p : NPointDomain d (n + 1) × NPointDomain d (m + 1) =>
    timeReflectionN d p.1
  let rightMap := fun p : NPointDomain d (n + 1) × NPointDomain d (m + 1) => p.2
  have hleft : Continuous leftMap :=
    (osiiStep4_continuous_timeReflectionN d (n + 1)).comp continuous_fst
  have hright : Continuous rightMap := continuous_snd
  apply continuous_pi
  intro i
  by_cases hi : i.val < n + 1
  · let ii : Fin (n + 1) := ⟨i.val, hi⟩
    have hi_eq : i = Fin.castAdd (m + 1) ii := by
      apply Fin.ext
      rfl
    rw [hi_eq]
    simpa [leftMap] using
      (continuous_apply ii).comp hleft
  · let jj : Fin (m + 1) := ⟨i.val - (n + 1), by omega⟩
    have hi_eq : i = Fin.natAdd (n + 1) jj := by
      apply Fin.ext
      simp [jj, Fin.natAdd]
      omega
    rw [hi_eq]
    simpa [rightMap] using
      (continuous_apply jj).comp hright

theorem osiiStep4SelectedBlockChronologicalConfigOfPair_continuous
    (d n m : Nat) :
    Continuous (osiiStep4SelectedBlockChronologicalConfigOfPair d n m) := by
  let appendMap := fun p : NPointDomain d (n + 1) × NPointDomain d (m + 1) =>
    Fin.append (timeReflectionN d p.1) p.2
  have happ : Continuous appendMap :=
    osiiStep4_continuous_append_reflected_pair d n m
  apply continuous_pi
  intro i
  simpa [osiiStep4SelectedBlockChronologicalConfigOfPair, appendMap] using
    (continuous_apply (osiiStep4SelectedBlockLeftReversePerm n m i)).comp happ

/-- Undoing the chronological permutation sends support back into the raw OS
reflected tensor-product support. -/
theorem osiiStep4SelectedBlockChronologicalOSSource_raw_mem_tsupport
    (d n m : Nat) [NeZero d]
    (f : SchwartzNPoint d (n + 1))
    (g : SchwartzNPoint d (m + 1))
    {x : NPointDomain d ((n + 1) + (m + 1))}
    (hx : x ∈ tsupport
      ((osiiStep4SelectedBlockChronologicalOSSource d n m f g :
        SchwartzNPoint d ((n + 1) + (m + 1))) :
          NPointDomain d ((n + 1) + (m + 1)) -> Complex)) :
    (fun i => x (osiiStep4SelectedBlockLeftReversePerm n m i)) ∈
      tsupport
        (((f.osConjTensorProduct g :
          SchwartzNPoint d ((n + 1) + (m + 1))) :
            NPointDomain d ((n + 1) + (m + 1)) -> Complex)) := by
  let e :=
    (LinearEquiv.funCongrLeft Real (SpacetimeDim d)
      (osiiStep4SelectedBlockLeftReversePerm n m)).toContinuousLinearEquiv
  have hts := tsupport_comp_eq_preimage
    (g := (((f.osConjTensorProduct g :
      SchwartzNPoint d ((n + 1) + (m + 1))) :
        NPointDomain d ((n + 1) + (m + 1)) -> Complex)))
    e.toHomeomorph
  have hx' : x ∈ e.toHomeomorph ⁻¹'
      tsupport
        (((f.osConjTensorProduct g :
          SchwartzNPoint d ((n + 1) + (m + 1))) :
            NPointDomain d ((n + 1) + (m + 1)) -> Complex)) := by
    rw [← hts]
    simpa [osiiStep4SelectedBlockChronologicalOSSource, e,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using hx
  simpa [e] using hx'

theorem osiiStep4SelectedBlockChronologicalLeftConfig_mem_tsupport
    (d n m : Nat) [NeZero d]
    (f : SchwartzNPoint d (n + 1))
    (g : SchwartzNPoint d (m + 1))
    {x : NPointDomain d ((n + 1) + (m + 1))}
    (hx : x ∈ tsupport
      ((osiiStep4SelectedBlockChronologicalOSSource d n m f g :
        SchwartzNPoint d ((n + 1) + (m + 1))) :
          NPointDomain d ((n + 1) + (m + 1)) -> Complex)) :
    osiiStep4SelectedBlockChronologicalLeftConfig d n m x ∈
      tsupport (f : NPointDomain d (n + 1) -> Complex) := by
  exact OSIIChapterV.osConjTensorProduct_tsupport_reflectedLeft_mem f g
    (osiiStep4SelectedBlockChronologicalOSSource_raw_mem_tsupport
      d n m f g hx)

theorem osiiStep4SelectedBlockChronologicalRightConfig_mem_tsupport
    (d n m : Nat) [NeZero d]
    (f : SchwartzNPoint d (n + 1))
    (g : SchwartzNPoint d (m + 1))
    {x : NPointDomain d ((n + 1) + (m + 1))}
    (hx : x ∈ tsupport
      ((osiiStep4SelectedBlockChronologicalOSSource d n m f g :
        SchwartzNPoint d ((n + 1) + (m + 1))) :
          NPointDomain d ((n + 1) + (m + 1)) -> Complex)) :
    osiiStep4SelectedBlockChronologicalRightConfig d n m x ∈
      tsupport (g : NPointDomain d (m + 1) -> Complex) := by
  exact OSIIChapterV.osConjTensorProduct_tsupport_right_mem f g
    (osiiStep4SelectedBlockChronologicalOSSource_raw_mem_tsupport
      d n m f g hx)

theorem osiiStep4SelectedBlockChronologicalConfigOfPair_left_right
    (d n m : Nat) [NeZero d]
    (x : NPointDomain d ((n + 1) + (m + 1))) :
    osiiStep4SelectedBlockChronologicalConfigOfPair d n m
        (osiiStep4SelectedBlockChronologicalLeftConfig d n m x,
          osiiStep4SelectedBlockChronologicalRightConfig d n m x) = x := by
  ext i mu
  by_cases hi : i.val < n + 1
  · let ii : Fin (n + 1) := ⟨i.val, hi⟩
    have hi_eq : i = Fin.castAdd (m + 1) ii := by
      apply Fin.ext
      rfl
    rw [hi_eq]
    simp [osiiStep4SelectedBlockChronologicalLeftConfig_apply,
      Fin.rev_rev, timeReflection_timeReflection]
  · let jj : Fin (m + 1) := ⟨i.val - (n + 1), by omega⟩
    have hi_eq : i = Fin.natAdd (n + 1) jj := by
      apply Fin.ext
      simp [jj, Fin.natAdd]
      omega
    rw [hi_eq]
    simp

/-- Compact support of both factors gives compact support of their
chronologically reordered OS tensor product. -/
theorem osiiStep4SelectedBlockChronologicalOSSource_hasCompactSupport
    (d n m : Nat) [NeZero d]
    (f : SchwartzNPoint d (n + 1))
    (g : SchwartzNPoint d (m + 1))
    (hf : HasCompactSupport (f : NPointDomain d (n + 1) -> Complex))
    (hg : HasCompactSupport (g : NPointDomain d (m + 1) -> Complex)) :
    HasCompactSupport
      ((osiiStep4SelectedBlockChronologicalOSSource d n m f g :
        SchwartzNPoint d ((n + 1) + (m + 1))) :
          NPointDomain d ((n + 1) + (m + 1)) -> Complex) := by
  let K : Set (NPointDomain d ((n + 1) + (m + 1))) :=
    osiiStep4SelectedBlockChronologicalConfigOfPair d n m ''
      (tsupport (f : NPointDomain d (n + 1) -> Complex) ×ˢ
        tsupport (g : NPointDomain d (m + 1) -> Complex))
  have hK : IsCompact K :=
    (hf.isCompact.prod hg.isCompact).image
      (osiiStep4SelectedBlockChronologicalConfigOfPair_continuous d n m)
  refine HasCompactSupport.of_support_subset_isCompact hK ?_
  intro x hx
  have hxt : x ∈ tsupport
      ((osiiStep4SelectedBlockChronologicalOSSource d n m f g :
        SchwartzNPoint d ((n + 1) + (m + 1))) :
          NPointDomain d ((n + 1) + (m + 1)) -> Complex) :=
    subset_tsupport _ hx
  let xL := osiiStep4SelectedBlockChronologicalLeftConfig d n m x
  let xR := osiiStep4SelectedBlockChronologicalRightConfig d n m x
  have hxL : xL ∈ tsupport (f : NPointDomain d (n + 1) -> Complex) :=
    osiiStep4SelectedBlockChronologicalLeftConfig_mem_tsupport d n m f g hxt
  have hxR : xR ∈ tsupport (g : NPointDomain d (m + 1) -> Complex) :=
    osiiStep4SelectedBlockChronologicalRightConfig_mem_tsupport d n m f g hxt
  refine ⟨(xL, xR), ⟨hxL, hxR⟩, ?_⟩
  exact osiiStep4SelectedBlockChronologicalConfigOfPair_left_right d n m x

theorem
    osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernel_hasCompactSupport
    (d k : Nat) [NeZero d] {rho : Real} (hrho : 0 < rho)
    (endpointCenter endpointImag : SpacetimeDim d)
    (center y y' : Fin (k * (d + 1)) -> Real) :
    HasCompactSupport
      ((osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource
        d k hrho endpointCenter endpointImag center y y' :
          SchwartzNPoint d (k + 1)) : NPointDomain d (k + 1) -> Complex) := by
  have hendpoint : HasCompactSupport
      ((osiiStep4CenteredComplexBlockRadialGRealSchwartz
        (d + 1) hrho endpointCenter endpointImag :
          SchwartzMap (SpacetimeDim d) Complex) : SpacetimeDim d -> Complex) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall endpointCenter (rho / 8)) ?_
    intro x hx
    exact
      osiiStep4CenteredComplexBlockRadialGRealSchwartz_tsupport_subset_closedBall
        (d + 1) hrho endpointCenter endpointImag (subset_tsupport _ hx)
  exact reducedTestLift_hasCompactSupport
    (osiiStep4CenteredComplexBlockRadialGRealSchwartz
      (d + 1) hrho endpointCenter endpointImag)
    (osiiStep4CenteredPartialConvolutionKernelFullSource
      d k hrho center y y')
    hendpoint
    (osiiStep4CenteredPartialConvolutionKernelFullSource_hasCompactSupport
      d k hrho center y y')

/-- A compactly supported source whose support has strictly positive
consecutive time gaps has compact strict-positive reduced-time support. -/
theorem osiiStep4_hasCompactStrictPositiveReducedTimeSupport_of_gap_pos
    (d k : Nat) [NeZero d]
    (f : SchwartzNPoint d (k + 1))
    (hcompact : HasCompactSupport
      (f : NPointDomain d (k + 1) -> Complex))
    (hgap : forall x,
      x ∈ tsupport (f : NPointDomain d (k + 1) -> Complex) ->
      forall i : Fin k,
        0 < BHW.reducedDiffMapReal (k + 1) d x i 0) :
    OSIIChapterV.HasCompactStrictPositiveReducedTimeSupport f := by
  let K : Set (Fin k -> Real) :=
    OSIIChapterV.reducedTimeProjectionCLM d k ''
      tsupport (f : NPointDomain d (k + 1) -> Complex)
  refine ⟨K,
    hcompact.isCompact.image
      (OSIIChapterV.reducedTimeProjectionCLM d k).continuous, ?_, ?_⟩
  · rintro tau ⟨x, hx, rfl⟩
    intro i
    simpa [OSIIChapterV.reducedTimeProjectionCLM_apply,
      section43QTime] using hgap x hx i
  · intro x hx
    exact ⟨x, hx, rfl⟩

/-- The chronological representative of the reflected tensor product of the
explicit selected-block positive-time sources. -/
noncomputable def osiiStep4SelectedBlockChronologicalPositiveSource
    (d n m : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (hcenter : forall i : Fin (n + 1 + m),
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    SchwartzNPoint d ((n + 1) + (m + 1)) :=
  osiiStep4SelectedBlockChronologicalOSSource d n m
    (osiiStep4SelectedBlockLeftPositiveTimeSource
      d n m hrho center y y' hcenter).1
    (osiiStep4SelectedBlockRightPositiveTimeSource
      d n m hrho center y y' hcenter).1

/-- The chronological reflected tensor-product source is pointwise the
selected-block density, with the shared integration variable supplied by the
first right endpoint. -/
theorem osiiStep4SelectedBlockChronologicalPositiveSource_apply_eq_density
    (d n m : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (hcenter : forall i : Fin (n + 1 + m),
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (x : NPointDomain d ((n + 1) + (m + 1))) :
    osiiStep4SelectedBlockChronologicalPositiveSource
        d n m hrho center y y' hcenter x =
      (osiiStep4SelectedBlockConvolutionDensity d n m rho center y y'
        (BHW.reducedDiffMapReal ((n + 1) + (m + 1)) d x)
        (osiiStep4SelectedBlockChronologicalRightConfig d n m x 0 -
          osiiStep4SelectedBlockRightEndpointCenter d n m center) : Complex) := by
  rw [osiiStep4SelectedBlockChronologicalPositiveSource,
    osiiStep4SelectedBlockChronologicalOSSource_apply]
  change
    star
        (osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource
          d n hrho
          (osiiStep4SelectedBlockLeftEndpointCenter d n m center)
          (osiiStep4SelectedBlockLeftEndpointImag d n m y y')
          (osiiStep4ParityReversedBeforeRealBlocks d n m center)
          (osiiStep4ParityReversedBeforeRealBlocks d n m y)
          (osiiStep4ParityReversedBeforeRealBlocks d n m y')
          (osiiStep4SelectedBlockChronologicalLeftConfig d n m x)) *
      osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource
        d m hrho
        (osiiStep4SelectedBlockRightEndpointCenter d n m center)
        (osiiStep4SelectedBlockRightEndpointImag d n m y')
        (osiiStep4AfterRealBlocks n m (d + 1) center)
        (osiiStep4AfterRealBlocks n m (d + 1) y)
        (osiiStep4AfterRealBlocks n m (d + 1) y')
        (osiiStep4SelectedBlockChronologicalRightConfig d n m x) = _
  rw [osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource_apply,
    osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource_apply]
  rw [osiiStep4SelectedBlockLeftPartialSource_apply_eq_prod,
    osiiStep4SelectedBlockRightPartialSource_apply_eq_prod]
  have hbefore :
      (Finset.univ.prod fun i : Fin n =>
        (osiiStep4SelectedBlockKernelFactor d n m rho center y y'
          (BHW.reducedDiffMapReal ((n + 1) + (m + 1)) d x)
          (osiiStep4BeforeBlockIndex n m i) : Complex)) =
        ((Finset.univ.prod fun i : Fin n =>
          osiiStep4SelectedBlockKernelFactor d n m rho center y y'
            (BHW.reducedDiffMapReal ((n + 1) + (m + 1)) d x)
            (osiiStep4BeforeBlockIndex n m i)) : Real) := by
    push_cast
    rfl
  have hafter :
      (Finset.univ.prod fun j : Fin m =>
        (osiiStep4SelectedBlockKernelFactor d n m rho center y y'
          (BHW.reducedDiffMapReal ((n + 1) + (m + 1)) d x)
          (osiiStep4AfterBlockIndex n m j) : Complex)) =
        ((Finset.univ.prod fun j : Fin m =>
          osiiStep4SelectedBlockKernelFactor d n m rho center y y'
            (BHW.reducedDiffMapReal ((n + 1) + (m + 1)) d x)
            (osiiStep4AfterBlockIndex n m j)) : Real) := by
    push_cast
    rfl
  rw [hbefore, hafter, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  let A : Real :=
    osiiStep4ComplexBlockRadialG (d + 1) rho
        (osiiStep4ComplexOfRealImag
          (osiiStep4SelectedBlockChronologicalLeftConfig d n m x 0 -
            osiiStep4SelectedBlockLeftEndpointCenter d n m center)
          (osiiStep4SelectedBlockLeftEndpointImag d n m y y')) *
      (Finset.univ.prod fun i : Fin n =>
        osiiStep4SelectedBlockKernelFactor d n m rho center y y'
          (BHW.reducedDiffMapReal ((n + 1) + (m + 1)) d x)
          (osiiStep4BeforeBlockIndex n m i))
  let B : Real :=
    osiiStep4ComplexBlockRadialG (d + 1) rho
        (osiiStep4ComplexOfRealImag
          (osiiStep4SelectedBlockChronologicalRightConfig d n m x 0 -
            osiiStep4SelectedBlockRightEndpointCenter d n m center)
          (osiiStep4SelectedBlockRightEndpointImag d n m y')) *
      (Finset.univ.prod fun j : Fin m =>
        osiiStep4SelectedBlockKernelFactor d n m rho center y y'
          (BHW.reducedDiffMapReal ((n + 1) + (m + 1)) d x)
          (osiiStep4AfterBlockIndex n m j))
  change star (A : Complex) * (B : Complex) = _
  have hstar : star (A : Complex) = (A : Complex) := by
    exact Complex.conj_ofReal A
  rw [hstar]
  norm_cast
  dsimp only [A, B]
  rw [osiiStep4SelectedBlockConvolutionDensity]
  have hendpoint :=
    osiiStep4SelectedBlockChronologicalEndpointRadialProduct_eq
      d n m rho center y y' x
  let gL : Real :=
    osiiStep4ComplexBlockRadialG (d + 1) rho
      (osiiStep4ComplexOfRealImag
        (osiiStep4SelectedBlockChronologicalLeftConfig d n m x 0 -
          osiiStep4SelectedBlockLeftEndpointCenter d n m center)
        (osiiStep4SelectedBlockLeftEndpointImag d n m y y'))
  let gR : Real :=
    osiiStep4ComplexBlockRadialG (d + 1) rho
      (osiiStep4ComplexOfRealImag
        (osiiStep4SelectedBlockChronologicalRightConfig d n m x 0 -
          osiiStep4SelectedBlockRightEndpointCenter d n m center)
        (osiiStep4SelectedBlockRightEndpointImag d n m y'))
  let cSel : Real :=
    osiiStep4ComplexBlockPartialConvolutionIntegrand (d + 1) rho
      (osiiStep4ComplexOfRealImag
        (BHW.reducedDiffMapReal ((n + 1) + (m + 1)) d x
            (osiiStep4SelectedBlockIndex n m) -
          osiiStep4SelectedRealBlock n m (d + 1) center)
        (osiiStep4SelectedRealBlock n m (d + 1) y))
      (osiiStep4SelectedRealBlock n m (d + 1) y')
      (osiiStep4SelectedBlockChronologicalRightConfig d n m x 0 -
        osiiStep4SelectedBlockRightEndpointCenter d n m center)
  let pBefore : Real := Finset.univ.prod fun i : Fin n =>
    osiiStep4SelectedBlockKernelFactor d n m rho center y y'
      (BHW.reducedDiffMapReal ((n + 1) + (m + 1)) d x)
      (osiiStep4BeforeBlockIndex n m i)
  let pAfter : Real := Finset.univ.prod fun j : Fin m =>
    osiiStep4SelectedBlockKernelFactor d n m rho center y y'
      (BHW.reducedDiffMapReal ((n + 1) + (m + 1)) d x)
      (osiiStep4AfterBlockIndex n m j)
  change (gL * pBefore) * (gR * pAfter) = pBefore * cSel * pAfter
  have hcSel : cSel = gL * gR := hendpoint.symm
  rw [hcSel]
  ring

/-- On a basepoint fiber, the first right endpoint differs from the common
basepoint by a fixed vector. -/
theorem osiiStep4SelectedBlockChronologicalRightConfig_fiber_zero_sub
    (d n m : Nat)
    (center : Fin ((n + 1 + m) * (d + 1)) -> Real)
    (a : SpacetimeDim d) (xi : NPointDomain d (n + 1 + m)) :
    osiiStep4SelectedBlockChronologicalRightConfig d n m
          (fun k mu =>
            a mu + diffVarSection d (n + 1 + m) xi k mu) 0 -
        osiiStep4SelectedBlockRightEndpointCenter d n m center =
      a +
        (diffVarSection d (n + 1 + m) xi
            (Fin.natAdd (n + 1) (0 : Fin (m + 1))) -
          osiiStep4SelectedBlockRightEndpointCenter d n m center) := by
  rw [osiiStep4SelectedBlockChronologicalRightConfig_zero]
  ext mu
  simp
  ring

end OSReconstruction
