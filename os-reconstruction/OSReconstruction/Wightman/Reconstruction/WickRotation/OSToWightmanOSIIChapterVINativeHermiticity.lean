import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINativeSourcePairing
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceOrderedDensity
import OSReconstruction.Wightman.Reconstruction.DenseCLM

/-!
# Hermiticity from the coupled source pairing

Nonempty left and right blocks determine every distribution of point arity
at least two. Their coupled source identity and compact-source density give
Hermiticity before the right-vacuum pairing or Wightman positivity is used.
The zero- and one-point distributions are treated separately.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace OSReconstruction

private theorem borchersConj_conjTensorProduct_cast
    {d n m : Nat} (f : SchwartzNPoint d n) (g : SchwartzNPoint d m)
    (x : NPointDomain d (n + m)) :
    (f.conjTensorProduct g).borchersConj x =
      (g.conjTensorProduct f) (fun i => x (Fin.cast (Nat.add_comm m n) i)) := by
  simp only [SchwartzMap.borchersConj_apply, SchwartzMap.conjTensorProduct_apply,
    map_mul, starRingEnd_self_apply]
  rw [mul_comm]
  congr 1
  · congr 1
    congr 1
    ext k
    simp only [splitFirst, splitLast]
    congr 1
    apply Fin.ext
    simp only [Fin.val_natAdd, Fin.val_rev, Fin.val_castAdd, Fin.val_cast]
    omega
  · congr 1
    ext k
    simp only [splitFirst, splitLast]
    congr 1
    apply Fin.ext
    simp only [Fin.val_natAdd, Fin.val_rev, Fin.val_castAdd, Fin.val_cast]
    omega

private def borchersAdjointFunctional {d n : Nat}
    (W : SchwartzNPoint d n →L[Complex] Complex) :
    SchwartzNPoint d n →L[Complex] Complex where
  toFun f := starRingEnd Complex (W f.borchersConj)
  map_add' f g := by simp
  map_smul' c f := by simp [SchwartzMap.borchersConj_smul]
  cont := continuous_star.comp (W.continuous.comp borchersConj_continuous_closure)

/-- Nonempty tensor pairings determine Hermiticity in every point degree
at least two. No vacuum pairing or positivity premise enters this step. -/
theorem hermitian_of_nonemptyConjTensorPairing
    {d : Nat} (W : (n : Nat) -> SchwartzNPoint d n →L[Complex] Complex)
    (hpair : ∀ (n m : Nat) (phi : SchwartzNPoint d (n + 1))
        (psi : SchwartzNPoint d (m + 1)),
      W ((n + 1) + (m + 1)) (phi.conjTensorProduct psi) =
        starRingEnd Complex (W ((m + 1) + (n + 1)) (psi.conjTensorProduct phi)))
    (k : Nat) (f : SchwartzNPoint d (k + 2)) :
    W (k + 2) f.borchersConj = starRingEnd Complex (W (k + 2) f) := by
  have hblock (phi : SchwartzNPoint d (k + 1)) (psi : SchwartzNPoint d 1) :
      W (k + 2) (phi.conjTensorProduct psi).borchersConj =
        starRingEnd Complex (W (k + 2) (phi.conjTensorProduct psi)) := by
    calc
      _ = W (1 + (k + 1)) (psi.conjTensorProduct phi) :=
        W_eq_of_cast (fun n f => W n f) (k + 2) (1 + (k + 1))
          (Nat.add_comm (k + 1) 1) _ _
          (fun x => borchersConj_conjTensorProduct_cast phi psi x)
      _ = _ := hpair 0 k psi phi
  have heq : borchersAdjointFunctional (W (k + 2)) = W (k + 2) := by
    apply clm_eq_of_eq_on_productTensor d (k + 2)
    intro fs
    let phi := (SchwartzMap.productTensor (fun i : Fin (k + 1) => fs i.castSucc)).borchersConj
    let psi := onePointToFin1CLM d (fs (Fin.last (k + 1)))
    have htensor : phi.conjTensorProduct psi = SchwartzMap.productTensor fs := by
      ext x
      simp only [phi, psi, SchwartzMap.conjTensorProduct,
        SchwartzMap.borchersConj_borchersConj, SchwartzMap.tensorProduct_apply,
        SchwartzMap.productTensor_apply, onePointToFin1CLM_apply]
      conv_rhs => rw [Fin.prod_univ_castSucc]
      rfl
    change starRingEnd Complex (W (k + 2) (SchwartzMap.productTensor fs).borchersConj) = _
    rw [← htensor, hblock]
    simp
  have h := congrArg (fun L : SchwartzNPoint d (k + 2) →L[Complex] Complex => L f) heq
  simpa [borchersAdjointFunctional] using congrArg (starRingEnd Complex) h

private theorem integral_osConj {d n : Nat} [NeZero d] (f : SchwartzNPoint d n) :
    (∫ x, f.osConj x) = starRingEnd Complex (∫ x, f x) := by
  have hinv : Function.Involutive (timeReflectionN (d := d) (n := n)) := by
    intro x
    funext i
    exact timeReflection_timeReflection d (x i)
  have hmp := timeReflectionN_measurePreserving (d := d) (n := n)
  calc
    (∫ x, f.osConj x) = starRingEnd Complex (∫ x, f (timeReflectionN d x)) :=
      _root_.integral_conj
    _ = _ := congrArg (starRingEnd Complex)
      (hmp.integral_comp (hmp.measurable.measurableEmbedding hinv.injective) (fun x => f x))

private theorem integral_borchersConj {d n : Nat} [NeZero d] (f : SchwartzNPoint d n) :
    (∫ x, f.borchersConj x) = starRingEnd Complex (∫ x, f x) := by
  have hinv : Function.Involutive (fun x : NPointDomain d n => fun i => x (Fin.rev i)) := by
    intro x
    ext i
    simp
  have hmp := reverseNPoint_measurePreserving (d := d) (n := n)
  calc
    (∫ x, f.borchersConj x) =
        starRingEnd Complex (∫ x : NPointDomain d n, f (fun i => x (Fin.rev i))) :=
      _root_.integral_conj
    _ = _ := congrArg (starRingEnd Complex)
      (hmp.integral_comp (hmp.measurable.measurableEmbedding hinv.injective) (fun x => f x))

private theorem onePointScalar_real_of_recovery
    {d : Nat} [NeZero d] (OS : OsterwalderSchraderAxioms d) (c : Complex)
    (hrecovery : ∀ f : ZeroDiagonalSchwartz d 1, OS.S 1 f = c * ∫ x, f.1 x) :
    starRingEnd Complex c = c := by
  let f : SchwartzNPoint d 1 := onePointToFin1CLM d (BHW.normalizedCutoffOfBump d).toSchwartz
  have hI : (∫ x : NPointDomain d 1, f x) = 1 := by
    have h := MeasurePreserving.integral_comp'
      (volume_preserving_funUnique (Fin 1) (SpacetimeDim d))
      (fun x => (BHW.normalizedCutoffOfBump d).toSchwartz x)
    exact (show (∫ x : NPointDomain d 1, f x) =
      ∫ x : SpacetimeDim d, (BHW.normalizedCutoffOfBump d).toSchwartz x from
        by simpa [f, onePointToFin1CLM_apply, ContinuousLinearEquiv.coe_funUnique] using h).trans
          (BHW.normalizedCutoffOfBump d).integral_eq_one
  have hIR : (∫ x, f.osConj x) = 1 := by rw [integral_osConj, hI]; simp
  have hreal := OS.E0_reality 1
    ⟨f, VanishesToInfiniteOrderOnCoincidence.one f⟩
    ⟨f.osConj, VanishesToInfiniteOrderOnCoincidence.one f.osConj⟩
    (fun x => SchwartzNPoint.osConj_apply f x)
  simpa only [hrecovery, hI, hIR, mul_one] using hreal

namespace OSIIChapterV.InitialGeneratedLogarithmicStageLevelData

variable {d : Nat} [NeZero d] {OS : OsterwalderSchraderAxioms d}

theorem strictGeneratedFullBoundary_conjTensorPairing_hermitian_pos
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (n m : Nat)
    (phi : SchwartzNPoint d (n + 1)) (psi : SchwartzNPoint d (m + 1)) :
    initial.strictGeneratedFullBoundary lgc ((n + 1) + (m + 1)) (phi.conjTensorProduct psi) =
      starRingEnd Complex (initial.strictGeneratedFullBoundary lgc ((m + 1) + (n + 1))
        (psi.conjTensorProduct phi)) := by
  have hclosed : IsClosed {p : SchwartzNPoint d (n + 1) × SchwartzNPoint d (m + 1) |
      initial.strictGeneratedFullBoundary lgc ((n + 1) + (m + 1)) (p.1.conjTensorProduct p.2) =
        starRingEnd Complex (initial.strictGeneratedFullBoundary lgc ((m + 1) + (n + 1))
          (p.2.conjTensorProduct p.1))} :=
    isClosed_eq
      ((initial.strictGeneratedFullBoundary lgc _).continuous.comp
        conjTensorProduct_continuous_closure)
      (continuous_star.comp ((initial.strictGeneratedFullBoundary lgc _).continuous.comp
        (conjTensorProduct_continuous_closure.comp continuous_swap)))
  refine ((dense_section43FourierLaplace_compact_ordered_frequency_preimage d (n + 1)).prod
    (dense_section43FourierLaplace_compact_ordered_frequency_preimage d (m + 1))).induction
      (P := fun p =>
        initial.strictGeneratedFullBoundary lgc ((n + 1) + (m + 1)) (p.1.conjTensorProduct p.2) =
          starRingEnd Complex (initial.strictGeneratedFullBoundary lgc ((m + 1) + (n + 1))
            (p.2.conjTensorProduct p.1)))
      ?_ hclosed (phi, psi)
  rintro ⟨phi, psi⟩ ⟨⟨f, hf⟩, ⟨g, hg⟩⟩
  change section43FourierLaplaceTransformComponent d (n + 1) f.f f.ordered f.compact =
    section43FrequencyProjection d (n + 1) phi at hf
  change section43FourierLaplaceTransformComponent d (m + 1) g.f g.ordered g.compact =
    section43FrequencyProjection d (m + 1) psi at hg
  change initial.strictGeneratedFullBoundary lgc _ (phi.conjTensorProduct psi) =
    starRingEnd Complex (initial.strictGeneratedFullBoundary lgc _ (psi.conjTensorProduct phi))
  rw [initial.strictGeneratedFullBoundary_sourcePairing_succRight_of_transformComponent
      lgc (n + 1) m phi psi ⟨f.f, f.ordered⟩ ⟨g.f, g.ordered⟩ f.compact g.compact hf.symm hg.symm,
    initial.strictGeneratedFullBoundary_sourcePairing_succRight_of_transformComponent
      lgc (m + 1) n psi phi ⟨g.f, g.ordered⟩ ⟨f.f, f.ordered⟩ g.compact f.compact hg.symm hf.symm]
  have h := PositiveTimeBorchersSequence.osInner_hermitian OS
    (PositiveTimeBorchersSequence.single (n + 1) f.f f.ordered)
    (PositiveTimeBorchersSequence.single (m + 1) g.f g.ordered)
  simpa only [PositiveTimeBorchersSequence.osInner,
    PositiveTimeBorchersSequence.single_toBorchersSequence,
    OSInnerProduct_single_single d OS.S OS.E0_linear] using h

/-- The native one-point distribution retains its independent scalar. -/
theorem strictGeneratedFullBoundary_one_eq_kernel_integral
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (f : SchwartzNPoint d 1) :
    initial.strictGeneratedFullBoundary lgc 1 f =
      (initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc 0).kernel 0 * ∫ x, f x := by
  let H := initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc 0
  have hkernel (z : Fin 1 -> Fin (d + 1) -> Complex) :
      initial.strictGeneratedWickKernel lgc 1 z = H.kernel 0 := by
    change H.wickPairKernel z = _
    rw [H.wickPairKernel_eq_of_reduced_mem (by
      change ∀ j : Fin 0, _
      exact fun j => Fin.elim0 j)]
    exact congrArg H.kernel (Subsingleton.elim _ _)
  have hlim := initial.strictGeneratedWickKernel_boundaryValue lgc 1 f
    (canonicalForwardConeDirection (d := d) 1) (canonicalForwardConeDirection_mem 1)
  simp_rw [hkernel, integral_const_mul] at hlim
  exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm

private theorem strictGeneratedFullBoundary_one_hermitian
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (f : SchwartzNPoint d 1) :
    initial.strictGeneratedFullBoundary lgc 1 f.borchersConj =
      starRingEnd Complex (initial.strictGeneratedFullBoundary lgc 1 f) := by
  let H := initial.toStrictGeneratedForwardTubeBoundaryDataOfOSII lgc 0
  have hsource (g : ZeroDiagonalSchwartz d 1) : OS.S 1 g = H.kernel 0 * ∫ x, g.1 x := by
    rw [initial.strictGeneratedEuclideanKernel_reproducesZeroDiagonal lgc 1 g]
    change (∫ x : NPointDomain d 1, H.euclideanDensity x * g.1 x) = _
    simp_rw [H.euclideanDensity_zeroGap_eq
      (initial.toStrictGeneratedFullTimeContinuationStage_hasCanonicalReducedCompactStageEdges lgc 0)
      (initial.toStrictGeneratedForwardTubeTimeSliceRealizationDataOfOSII lgc 0)]
    exact integral_const_mul _ _
  have hreal := onePointScalar_real_of_recovery OS (H.kernel 0) hsource
  rw [initial.strictGeneratedFullBoundary_one_eq_kernel_integral lgc,
    initial.strictGeneratedFullBoundary_one_eq_kernel_integral lgc,
    integral_borchersConj, map_mul, hreal]

/-- Literal full-Schwartz Hermiticity of the original-OS boundary family.
The proof uses nonempty source pairings, not the right-vacuum case or positivity. -/
theorem strictGeneratedFullBoundary_hermitian
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (n : Nat) (f g : SchwartzNPoint d n)
    (hfg : ∀ x, g x = starRingEnd Complex (f (fun i => x (Fin.rev i)))) :
    initial.strictGeneratedFullBoundary lgc n g =
      starRingEnd Complex (initial.strictGeneratedFullBoundary lgc n f) := by
  have hg : g = f.borchersConj := by ext x; exact hfg x
  rw [hg]
  cases n with
  | zero =>
      change f.borchersConj 0 = starRingEnd Complex (f 0)
      rw [SchwartzMap.borchersConj_apply]
      exact congrArg (fun x => starRingEnd Complex (f x)) (Subsingleton.elim _ _)
  | succ k =>
      cases k with
      | zero => exact initial.strictGeneratedFullBoundary_one_hermitian lgc f
      | succ k =>
          exact hermitian_of_nonemptyConjTensorPairing (initial.strictGeneratedFullBoundary lgc)
            (initial.strictGeneratedFullBoundary_conjTensorPairing_hermitian_pos lgc) k f

end OSIIChapterV.InitialGeneratedLogarithmicStageLevelData
end OSReconstruction
