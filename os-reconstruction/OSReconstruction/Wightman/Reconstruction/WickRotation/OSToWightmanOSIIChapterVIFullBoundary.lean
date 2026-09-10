/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIMixedBoundary
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSourceCurrent
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedTransport




















noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction

private noncomputable def schwartzPartialEvalRightZeroCLM
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F] :
    SchwartzMap (E × F) Complex →L[Complex] SchwartzMap E Complex := by
  let g : E -> E × F := fun x => (x, 0)
  have hg : g.HasTemperateGrowth := by
    simpa [g] using
      (ContinuousLinearMap.inl Real E F).hasTemperateGrowth
  have hg_upper : exists (n : Nat) (C : Real),
      forall x, norm x <= C * (1 + norm (g x)) ^ n := by
    refine ⟨1, 1, ?_⟩
    intro x
    simp [g, Prod.norm_def]
  exact SchwartzMap.compCLM (𝕜 := Complex) (g := g) hg hg_upper

private noncomputable def schwartzPartialEvalLeftZeroCLM
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F] :
    SchwartzMap (E × F) Complex →L[Complex] SchwartzMap F Complex := by
  let g : F -> E × F := fun y => (0, y)
  have hg : g.HasTemperateGrowth := by
    simpa [g] using
      (ContinuousLinearMap.inr Real E F).hasTemperateGrowth
  have hg_upper : exists (n : Nat) (C : Real),
      forall y, norm y <= C * (1 + norm (g y)) ^ n := by
    refine ⟨1, 1, ?_⟩
    intro y
    simp [g, Prod.norm_def]
  exact SchwartzMap.compCLM (𝕜 := Complex) (g := g) hg hg_upper

/-- Positive-dimensional form of the existing complex Schwartz nuclear
extension theorem.  Splitting the dimension as a successor avoids dependent
casts through `(N - 1) + 1 = N`. -/
private theorem schwartz_nuclear_extension_fin
    (N n : Nat) (hN : 0 < N)
    (Phi : ContinuousMultilinearMap Complex
      (fun _ : Fin n => SchwartzMap (Fin N -> Real) Complex) Complex) :
    ∃! W : SchwartzMap (Fin n -> Fin N -> Real) Complex →L[Complex] Complex,
      forall fs : Fin n -> SchwartzMap (Fin N -> Real) Complex,
        W (SchwartzMap.productTensor fs) = Phi fs := by
  cases N with
  | zero => omega
  | succ N =>
      simpa using schwartz_nuclear_extension N n Phi

/-- Swap the two spatial blocks while leaving the two time blocks fixed. -/
private noncomputable def blockCrossSwapCLE (n m : Nat) :
    (Fin 2 -> Fin (n + m) -> Real) ≃L[Real]
      (Fin 2 -> Fin (n + m) -> Real) := by
  let swap : (Fin 2 -> Fin (n + m) -> Real) ->
      Fin 2 -> Fin (n + m) -> Real :=
    fun x i j => if j.val < n then x i j else x i.rev j
  let e : (Fin 2 -> Fin (n + m) -> Real) ≃ₗ[Real]
      (Fin 2 -> Fin (n + m) -> Real) :=
    { toFun := swap
      invFun := swap
      map_add' := by
        intro x y
        ext i j
        simp only [swap, Pi.add_apply]
        split <;> rfl
      map_smul' := by
        intro c x
        ext i j
        simp only [swap, Pi.smul_apply, smul_eq_mul]
        split <;> rfl
      left_inv := by
        intro x
        ext i j
        by_cases hj : j.val < n <;> simp [swap, hj]
      right_inv := by
        intro x
        ext i j
        by_cases hj : j.val < n <;> simp [swap, hj] }
  exact e.toContinuousLinearEquiv

@[simp] private theorem blockCrossSwapCLE_apply
    (n m : Nat) (x : Fin 2 -> Fin (n + m) -> Real)
    (i : Fin 2) (j : Fin (n + m)) :
    blockCrossSwapCLE n m x i j =
      if j.val < n then x i j else x i.rev j := rfl

private theorem blockCrossSwapCLE_zero_splitFirst
    (n m : Nat) (x : Fin 2 -> Fin (n + m) -> Real) :
    splitFirst n m (blockCrossSwapCLE n m x 0) = splitFirst n m (x 0) := by
  ext i
  simp [splitFirst]

private theorem blockCrossSwapCLE_zero_splitLast
    (n m : Nat) (x : Fin 2 -> Fin (n + m) -> Real) :
    splitLast n m (blockCrossSwapCLE n m x 0) = splitLast n m (x 1) := by
  ext i
  simp [splitLast]

private theorem blockCrossSwapCLE_one_splitFirst
    (n m : Nat) (x : Fin 2 -> Fin (n + m) -> Real) :
    splitFirst n m (blockCrossSwapCLE n m x 1) = splitFirst n m (x 1) := by
  ext i
  simp [splitFirst]

private theorem blockCrossSwapCLE_one_splitLast
    (n m : Nat) (x : Fin 2 -> Fin (n + m) -> Real) :
    splitLast n m (blockCrossSwapCLE n m x 1) = splitLast n m (x 0) := by
  ext i
  simp [splitLast]

private noncomputable def flatTimeSliceCLM (d k : Nat) :
    SchwartzMap (Fin (k + k * d) -> Real) Complex →L[Complex]
      SchwartzMap (Fin k -> Real) Complex :=
  schwartzPartialEvalRightZeroCLM.comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv Complex
      (section43TimeSpatialFlatCLE d k))

@[simp] private theorem flatTimeSliceCLM_apply
    (d k : Nat) (F : SchwartzMap (Fin (k + k * d) -> Real) Complex)
    (t : Fin k -> Real) :
    flatTimeSliceCLM d k F t =
      F (section43TimeSpatialFlatCLE d k (t, 0)) := rfl

private noncomputable def flatSpatialSliceCLM (d k : Nat) :
    SchwartzMap (Fin (k + k * d) -> Real) Complex →L[Complex]
      SchwartzMap (Section43SpatialSpace d k) Complex :=
  schwartzPartialEvalLeftZeroCLM.comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv Complex
      (section43TimeSpatialFlatCLE d k))

@[simp] private theorem flatSpatialSliceCLM_apply
    (d k : Nat) (F : SchwartzMap (Fin (k + k * d) -> Real) Complex)
    (x : Section43SpatialSpace d k) :
    flatSpatialSliceCLM d k F x =
      F (section43TimeSpatialFlatCLE d k (0, x)) := rfl

private noncomputable def blockBump (n m : Nat) :
    SchwartzMap (Fin (n + m) -> Real) Complex :=
  SchwartzMap.tensorProduct
    (unitBallBumpSchwartzPi n)
    (unitBallBumpSchwartzPi m)

/-- Embed one mixed block into two stabilized blocks, then cross the spatial
coordinates. -/
private noncomputable def blockCrossEmbeddingCLM (n m : Nat) :
    SchwartzMap (Fin (n + m) -> Real) Complex →L[Complex]
      SchwartzMap (Fin 2 -> Fin (n + m) -> Real) Complex :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv Complex
      (blockCrossSwapCLE n m)).comp
    (SchwartzMap.prependFieldCLMLeft
      (SchwartzMap.compCLMOfContinuousLinearEquiv Complex
        (ContinuousLinearEquiv.funUnique (Fin 1) Real
          (Fin (n + m) -> Real))
        (blockBump n m)))

private theorem blockCrossEmbeddingCLM_apply
    (n m : Nat) (F : SchwartzMap (Fin (n + m) -> Real) Complex)
    (x : Fin 2 -> Fin (n + m) -> Real) :
    blockCrossEmbeddingCLM n m F x =
      F (blockCrossSwapCLE n m x 0) *
        blockBump n m (blockCrossSwapCLE n m x 1) := by
  rfl

private theorem blockCrossEmbeddingCLM_tensorProduct
    (n m : Nat)
    (phi : SchwartzMap (Fin n -> Real) Complex)
    (chi : SchwartzMap (Fin m -> Real) Complex) :
    blockCrossEmbeddingCLM n m (SchwartzMap.tensorProduct phi chi) =
      SchwartzMap.productTensor (fun i : Fin 2 =>
        Fin.cases
          (SchwartzMap.tensorProduct phi (unitBallBumpSchwartzPi m))
          (fun _ => SchwartzMap.tensorProduct
            (unitBallBumpSchwartzPi n) chi) i) := by
  ext x
  rw [blockCrossEmbeddingCLM_apply, SchwartzMap.productTensor_apply]
  rw [Fin.prod_univ_two]
  change
    (SchwartzMap.tensorProduct phi chi) (blockCrossSwapCLE n m x 0) *
        blockBump n m (blockCrossSwapCLE n m x 1) =
      (SchwartzMap.tensorProduct phi (unitBallBumpSchwartzPi m)) (x 0) *
        (SchwartzMap.tensorProduct (unitBallBumpSchwartzPi n) chi) (x 1)
  rw [blockBump]
  simp only [SchwartzMap.tensorProduct_apply]
  rw [blockCrossSwapCLE_zero_splitFirst,
    blockCrossSwapCLE_zero_splitLast,
    blockCrossSwapCLE_one_splitFirst,
    blockCrossSwapCLE_one_splitLast]
  ring

private theorem flatTimeSliceCLM_tensorProduct_bump
    (d k : Nat) (phi : SchwartzMap (Fin k -> Real) Complex) :
    flatTimeSliceCLM d k
        (SchwartzMap.tensorProduct phi (unitBallBumpSchwartzPi (k * d))) =
      phi := by
  ext t
  rw [flatTimeSliceCLM_apply, SchwartzMap.tensorProduct_apply,
    section43TimeSpatialFlatCLE_splitFirst,
    section43TimeSpatialFlatCLE_splitLast]
  have hbump :
      unitBallBumpSchwartzPi (k * d) (0 : Fin (k * d) -> Real) = 1 := by
    apply unitBallBumpSchwartzPi_one_of_mem_closedBall
    simp
  simp [hbump]

private theorem flatSpatialSliceCLM_bump_tensorProduct
    (d k : Nat)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    flatSpatialSliceCLM d k
        (SchwartzMap.tensorProduct (unitBallBumpSchwartzPi k)
          (section43SpatialFlatSchwartzCLE d k chi)) = chi := by
  ext x
  rw [flatSpatialSliceCLM_apply, SchwartzMap.tensorProduct_apply,
    section43TimeSpatialFlatCLE_splitFirst,
    section43TimeSpatialFlatCLE_splitLast]
  have hbump : unitBallBumpSchwartzPi k (0 : Fin k -> Real) = 1 := by
    apply unitBallBumpSchwartzPi_one_of_mem_closedBall
    simp
  simp [hbump, section43SpatialFlatSchwartzCLE]

namespace OSIIFullTimeStageVladimirovGrowthData

variable {d k : Nat} [NeZero d]
variable {A : OSIITimeContinuationStage d k}

private noncomputable def flatTimeSpatialBilinearMap
    (B : SchwartzMap (Fin k -> Real) Complex →ₗ[Complex]
      SchwartzMap (Section43SpatialSpace d k) Complex →ₗ[Complex] Complex) :
    SchwartzMap (Fin (k + k * d) -> Real) Complex →ₗ[Complex]
      SchwartzMap (Fin (k + k * d) -> Real) Complex →ₗ[Complex] Complex where
  toFun F :=
    (B (flatTimeSliceCLM d k F)).comp
      (flatSpatialSliceCLM d k).toLinearMap
  map_add' F H := by
    ext K
    simp
  map_smul' c F := by
    ext K
    simp

@[simp] private theorem flatTimeSpatialBilinearMap_apply
    (B : SchwartzMap (Fin k -> Real) Complex →ₗ[Complex]
      SchwartzMap (Section43SpatialSpace d k) Complex →ₗ[Complex] Complex)
    (F H : SchwartzMap (Fin (k + k * d) -> Real) Complex) :
    flatTimeSpatialBilinearMap (d := d) (k := k) B F H =
      B
        (flatTimeSliceCLM d k F) (flatSpatialSliceCLM d k H) := rfl

private theorem continuous_flatTimeSpatialBilinearMap
    (B : SchwartzMap (Fin k -> Real) Complex →ₗ[Complex]
      SchwartzMap (Section43SpatialSpace d k) Complex →ₗ[Complex] Complex)
    (hB : Continuous (fun p :
      SchwartzMap (Fin k -> Real) Complex ×
        SchwartzMap (Section43SpatialSpace d k) Complex =>
      B p.1 p.2)) :
    Continuous (fun p :
      SchwartzMap (Fin (k + k * d) -> Real) Complex ×
        SchwartzMap (Fin (k + k * d) -> Real) Complex =>
      flatTimeSpatialBilinearMap (d := d) (k := k) B p.1 p.2) := by
  exact hB.comp
    (((flatTimeSliceCLM d k).continuous.comp continuous_fst).prodMk
      ((flatSpatialSliceCLM d k).continuous.comp continuous_snd))

set_option maxHeartbeats 800000 in
private noncomputable def flatTimeSpatialCMM
    (B : SchwartzMap (Fin k -> Real) Complex →ₗ[Complex]
      SchwartzMap (Section43SpatialSpace d k) Complex →ₗ[Complex] Complex)
    (hB : Continuous (fun p :
      SchwartzMap (Fin k -> Real) Complex ×
        SchwartzMap (Section43SpatialSpace d k) Complex =>
      B p.1 p.2)) :
    ContinuousMultilinearMap Complex
      (fun _ : Fin 2 =>
        SchwartzMap (Fin (k + k * d) -> Real) Complex) Complex where
  toMultilinearMap :=
    { toFun := fun fs =>
        flatTimeSpatialBilinearMap (d := d) (k := k) B (fs 0) (fs 1)
      map_update_add' := by
        intro hdec fs i F H
        have hdec_eq : hdec = instDecidableEqFin 2 := Subsingleton.elim _ _
        subst hdec_eq
        fin_cases i
        · simpa [Function.update] using
            congrArg
              (fun L : SchwartzMap (Fin (k + k * d) -> Real) Complex
                  →ₗ[Complex] Complex => L (fs 1))
              ((flatTimeSpatialBilinearMap (d := d) (k := k) B).map_add F H)
        · simpa [Function.update] using
            (flatTimeSpatialBilinearMap (d := d) (k := k) B (fs 0)).map_add F H
      map_update_smul' := by
        intro hdec fs i c F
        have hdec_eq : hdec = instDecidableEqFin 2 := Subsingleton.elim _ _
        subst hdec_eq
        fin_cases i
        · simpa [Function.update] using
            congrArg
              (fun L : SchwartzMap (Fin (k + k * d) -> Real) Complex
                  →ₗ[Complex] Complex => L (fs 1))
              ((flatTimeSpatialBilinearMap (d := d) (k := k) B).map_smul c F)
        · simpa [Function.update] using
            (flatTimeSpatialBilinearMap (d := d) (k := k) B (fs 0)).map_smul c F }
  cont := by
    let evalPair :
        (Fin 2 -> SchwartzMap (Fin (k + k * d) -> Real) Complex) ->
          SchwartzMap (Fin (k + k * d) -> Real) Complex ×
            SchwartzMap (Fin (k + k * d) -> Real) Complex :=
      fun fs => (fs 0, fs 1)
    have hevalPair : Continuous evalPair :=
      (continuous_apply 0).prodMk (continuous_apply 1)
    simpa [evalPair] using
      (continuous_flatTimeSpatialBilinearMap
        (d := d) (k := k) B hB).comp hevalPair

@[simp] private theorem flatTimeSpatialCMM_apply
    (B : SchwartzMap (Fin k -> Real) Complex →ₗ[Complex]
      SchwartzMap (Section43SpatialSpace d k) Complex →ₗ[Complex] Complex)
    (hB : Continuous (fun p :
      SchwartzMap (Fin k -> Real) Complex ×
        SchwartzMap (Section43SpatialSpace d k) Complex =>
      B p.1 p.2))
    (fs : Fin 2 -> SchwartzMap (Fin (k + k * d) -> Real) Complex) :
    flatTimeSpatialCMM (d := d) (k := k) B hB fs =
      flatTimeSpatialBilinearMap (d := d) (k := k) B (fs 0) (fs 1) := rfl

/-- Any jointly continuous time--spatial bilinear pairing extends to the
Schwartz space on the flattened mixed block. -/
theorem exists_flatTimeSpatialDistribution_of_continuousBilinearMap
    (B : SchwartzMap (Fin k -> Real) Complex →ₗ[Complex]
      SchwartzMap (Section43SpatialSpace d k) Complex →ₗ[Complex] Complex)
    (hB : Continuous (fun p :
      SchwartzMap (Fin k -> Real) Complex ×
        SchwartzMap (Section43SpatialSpace d k) Complex =>
      B p.1 p.2))
    [NeZero k] :
    exists W : SchwartzMap (Fin (k + k * d) -> Real) Complex →L[Complex] Complex,
      forall (phi : SchwartzMap (Fin k -> Real) Complex)
        (chi : SchwartzMap (Section43SpatialSpace d k) Complex),
        W (SchwartzMap.tensorProduct phi
          (section43SpatialFlatSchwartzCLE d k chi)) =
            B phi chi := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hdim_pos : 0 < k + k * d := by omega
  have hnuclear := schwartz_nuclear_extension_fin
    (k + k * d) 2 hdim_pos
      (flatTimeSpatialCMM (d := d) (k := k) B hB)
  obtain ⟨Wnuclear, hWnuclear, _⟩ := hnuclear
  refine ⟨Wnuclear.comp (blockCrossEmbeddingCLM k (k * d)), ?_⟩
  intro phi chi
  rw [ContinuousLinearMap.comp_apply,
    blockCrossEmbeddingCLM_tensorProduct, hWnuclear,
    flatTimeSpatialCMM_apply, flatTimeSpatialBilinearMap_apply]
  change
    B
        (flatTimeSliceCLM d k
          (SchwartzMap.tensorProduct phi
            (unitBallBumpSchwartzPi (k * d))))
        (flatSpatialSliceCLM d k
          (SchwartzMap.tensorProduct (unitBallBumpSchwartzPi k)
            (section43SpatialFlatSchwartzCLE d k chi))) =
      B phi chi
  rw [flatTimeSliceCLM_tensorProduct_bump,
    flatSpatialSliceCLM_bump_tensorProduct]

/-- The jointly continuous Chapter VI boundary pairing extends to the
Schwartz space on the flattened mixed block. -/
theorem exists_flatMixedBoundary
    (G : OSIIFullTimeStageVladimirovGrowthData A) [NeZero k] :
    exists W : SchwartzMap (Fin (k + k * d) -> Real) Complex →L[Complex] Complex,
      forall (phi : SchwartzMap (Fin k -> Real) Complex)
        (chi : SchwartzMap (Section43SpatialSpace d k) Complex),
        W (SchwartzMap.tensorProduct phi
          (section43SpatialFlatSchwartzCLE d k chi)) =
            G.mixedBoundaryBilinearMap phi chi :=
  exists_flatTimeSpatialDistribution_of_continuousBilinearMap
    G.mixedBoundaryBilinearMap G.continuous_mixedBoundaryBilinearMap

private noncomputable def timeSpatialToMixedFlatCLM (d k : Nat) [NeZero d] :
    SchwartzMap (Section43TimeSpatialSpace d k) Complex →L[Complex]
      SchwartzMap (Fin (k + k * d) -> Real) Complex :=
  SchwartzMap.compCLMOfContinuousLinearEquiv Complex
    (section43TimeSpatialFlatCLE d k).symm

@[simp] private theorem timeSpatialToMixedFlatCLM_timeSpatialTensor
    (d k : Nat) [NeZero d]
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    timeSpatialToMixedFlatCLM d k
        (section43TimeSpatialTensor d k phi chi) =
      SchwartzMap.tensorProduct phi
        (section43SpatialFlatSchwartzCLE d k chi) := by
  ext x
  simp [timeSpatialToMixedFlatCLM, section43TimeSpatialTensor,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

/-- Any jointly continuous time--spatial bilinear pairing extends to one
tempered distribution on the unflattened Section 4.3 mixed Schwartz space. -/
theorem exists_timeSpatialDistribution_of_continuousBilinearMap
    (B : SchwartzMap (Fin k -> Real) Complex →ₗ[Complex]
      SchwartzMap (Section43SpatialSpace d k) Complex →ₗ[Complex] Complex)
    (hB : Continuous (fun p :
      SchwartzMap (Fin k -> Real) Complex ×
        SchwartzMap (Section43SpatialSpace d k) Complex =>
      B p.1 p.2))
    [NeZero k] :
    exists W : SchwartzMap (Section43TimeSpatialSpace d k) Complex
        →L[Complex] Complex,
      forall (phi : SchwartzMap (Fin k -> Real) Complex)
        (chi : SchwartzMap (Section43SpatialSpace d k) Complex),
        W (section43TimeSpatialTensor d k phi chi) = B phi chi := by
  obtain ⟨Wflat, hWflat⟩ :=
    exists_flatTimeSpatialDistribution_of_continuousBilinearMap B hB
  refine ⟨Wflat.comp (timeSpatialToMixedFlatCLM d k), ?_⟩
  intro phi chi
  rw [ContinuousLinearMap.comp_apply,
    timeSpatialToMixedFlatCLM_timeSpatialTensor, hWflat]

/-- Section 4.3 time--spatial tensors determine a continuous functional on
the complete mixed Schwartz space. -/
theorem section43TimeSpatial_clm_eq_of_eq_on_timeSpatialTensor
    (W U : SchwartzMap (Section43TimeSpatialSpace d k) Complex
      →L[Complex] Complex)
    (h : forall (phi : SchwartzMap (Fin k -> Real) Complex)
      (chi : SchwartzMap (Section43SpatialSpace d k) Complex),
        W (section43TimeSpatialTensor d k phi chi) =
          U (section43TimeSpatialTensor d k phi chi)) :
    W = U := by
  let S : Set (SchwartzMap (Section43TimeSpatialSpace d k) Complex) :=
    {F | exists phi : SchwartzMap (Fin k -> Real) Complex,
      exists chi : SchwartzMap (Section43SpatialSpace d k) Complex,
        F = section43TimeSpatialTensor d k phi chi}
  have hDense :
      Dense (((Submodule.span Complex S : Submodule Complex
        (SchwartzMap (Section43TimeSpatialSpace d k) Complex)) :
          Set (SchwartzMap (Section43TimeSpatialSpace d k) Complex))) := by
    simpa [S] using dense_section43TimeSpatialTensor_span d k
  have hSpan : forall F : SchwartzMap (Section43TimeSpatialSpace d k) Complex,
      F ∈ Submodule.span Complex S -> W F = U F := by
    intro F hF
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hF
    · intro V hV
      rcases hV with ⟨phi, chi, rfl⟩
      exact h phi chi
    · simp
    · intro V Z _ _ hV hZ
      simpa using congrArg₂ (fun a b : Complex => a + b) hV hZ
    · intro c V _ hV
      simpa using congrArg (fun z : Complex => c * z) hV
  apply ContinuousLinearMap.ext
  intro F
  have hclosed :
      IsClosed {V : SchwartzMap (Section43TimeSpatialSpace d k) Complex |
        W V = U V} :=
    isClosed_eq W.continuous U.continuous
  have hclosure :
      closure (((Submodule.span Complex S : Submodule Complex
        (SchwartzMap (Section43TimeSpatialSpace d k) Complex)) :
          Set (SchwartzMap (Section43TimeSpatialSpace d k) Complex))) ⊆
        {V : SchwartzMap (Section43TimeSpatialSpace d k) Complex |
          W V = U V} :=
    hclosed.closure_subset_iff.mpr hSpan
  exact hclosure (hDense.closure_eq ▸ Set.mem_univ F)

private noncomputable def nPointToMixedFlatCLM (d k : Nat) [NeZero d] :
    SchwartzNPoint d k →L[Complex]
      SchwartzMap (Fin (k + k * d) -> Real) Complex :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv Complex
      (section43TimeSpatialFlatCLE d k).symm).comp
    (nPointTimeSpatialSchwartzCLE (d := d) (n := k)).toContinuousLinearMap

@[simp] private theorem nPointToMixedFlatCLM_timeSpatialTensor
    (d k : Nat) [NeZero d]
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    nPointToMixedFlatCLM d k
        (section43NPointTimeSpatialTensor d k phi chi) =
      SchwartzMap.tensorProduct phi
        (section43SpatialFlatSchwartzCLE d k chi) := by
  ext x
  simp [nPointToMixedFlatCLM, section43NPointTimeSpatialTensor,
    section43TimeSpatialTensor,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

/-- The mixed boundary pairing extends to a tempered distribution in the
full difference-coordinate Schwartz space. -/
theorem exists_mixedBoundaryDistribution
    (G : OSIIFullTimeStageVladimirovGrowthData A) [NeZero k] :
    exists W : SchwartzNPoint d k →L[Complex] Complex,
      forall (phi : SchwartzMap (Fin k -> Real) Complex)
        (chi : SchwartzMap (Section43SpatialSpace d k) Complex),
        W (section43NPointTimeSpatialTensor d k phi chi) =
          G.mixedBoundaryBilinearMap phi chi := by
  obtain ⟨Wflat, hWflat⟩ := G.exists_flatMixedBoundary
  refine ⟨Wflat.comp (nPointToMixedFlatCLM d k), ?_⟩
  intro phi chi
  rw [ContinuousLinearMap.comp_apply,
    nPointToMixedFlatCLM_timeSpatialTensor, hWflat]

/-- The mixed boundary pairing in the ordered spacetime coordinates used by
the Chapter VI handoff. -/
theorem exists_orderedMixedBoundaryDistribution
    (G : OSIIFullTimeStageVladimirovGrowthData A) [NeZero k] :
    exists W : SchwartzNPoint d k →L[Complex] Complex,
      forall (phi : SchwartzMap (Fin k -> Real) Complex)
        (chi : SchwartzMap (Section43SpatialSpace d k) Complex),
        W (section43OrderedPullbackTimeSpatialTensorCLM d k chi phi) =
          G.mixedBoundaryBilinearMap phi chi := by
  obtain ⟨Wmixed, hWmixed⟩ := G.exists_mixedBoundaryDistribution
  refine ⟨OSIIChapterV.orderedTransportDistribution Wmixed, ?_⟩
  intro phi chi
  rw [OSIIChapterV.orderedTransportDistribution_orderedPullbackTimeSpatialTensor,
    section43TimeSpatialTensorCLM_apply, hWmixed]

/-- A selected ordered-coordinate tempered distribution extending the mixed
boundary pairing. -/
noncomputable def orderedMixedBoundary
    (G : OSIIFullTimeStageVladimirovGrowthData A) [NeZero k] :
    SchwartzNPoint d k →L[Complex] Complex :=
  Classical.choose G.exists_orderedMixedBoundaryDistribution

@[simp] theorem orderedMixedBoundary_apply
    (G : OSIIFullTimeStageVladimirovGrowthData A) [NeZero k]
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    G.orderedMixedBoundary
        (section43OrderedPullbackTimeSpatialTensorCLM d k chi phi) =
      G.mixedBoundaryBilinearMap phi chi :=
  Classical.choose_spec G.exists_orderedMixedBoundaryDistribution phi chi

/-- Package the Chapter VI growth theorem as a full tempered Minkowski
boundary.  Spectral support remains a separate downstream obligation. -/
noncomputable def toTemperedBoundaryData
    (G : OSIIFullTimeStageVladimirovGrowthData A) [NeZero k] :
    OSIIFullTimeStageTemperedBoundaryData A where
  fullCarrier := G.fullCarrier
  orderedBoundary := G.orderedMixedBoundary
  slice_integrable := by
    intro eta heta epsilon hepsilon phi chi
    exact G.integrable_positiveSlicePairing
      eta heta epsilon hepsilon phi chi
  boundaryValue := by
    intro eta heta phi chi
    simpa only [orderedMixedBoundary_apply, mixedBoundaryBilinearMap_apply] using
      G.timeBoundary_boundaryValue chi eta heta phi

@[simp] theorem toTemperedBoundaryData_orderedBoundary
    (G : OSIIFullTimeStageVladimirovGrowthData A) [NeZero k] :
    G.toTemperedBoundaryData.orderedBoundary = G.orderedMixedBoundary := rfl

/-- On every Section 4.3 tensor, the canonical reduced Chapter VI boundary is
the fixed-spatial-probe time boundary. -/
@[simp] theorem toTemperedBoundaryData_reducedBoundary_timeSpatialTensor
    (G : OSIIFullTimeStageVladimirovGrowthData A) [NeZero k]
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    G.toTemperedBoundaryData.reducedBoundary
        (section43NPointTimeSpatialTensor d k phi chi) =
      G.timeBoundary chi phi := by
  rw [← section43TimeSpatialTensorCLM_apply]
  rw [← OSIIChapterV.orderedTransportDistribution_orderedPullbackTimeSpatialTensor]
  rw [OSIIFullTimeStageTemperedBoundaryData.orderedTransportDistribution_reducedBoundary]
  rw [toTemperedBoundaryData_orderedBoundary, orderedMixedBoundary_apply,
    mixedBoundaryBilinearMap_apply]

end OSIIFullTimeStageVladimirovGrowthData

end OSReconstruction
