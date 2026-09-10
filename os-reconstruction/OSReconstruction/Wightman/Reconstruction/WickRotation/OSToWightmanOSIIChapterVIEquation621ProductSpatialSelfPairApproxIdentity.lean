/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621HeadMarginalApproxIdentity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621ProductSpatialApproxIdentity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621SpatialChartMeasure
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINormalizedEnvelopeWeightedSourceSpatialGrowth











noncomputable section

open MeasureTheory
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity

theorem reflectedSelfPairHeadTailArity
    (d r : Nat) :
    ((r + 1) + (r + 1)) * d = d + (r + (r + 1)) * d := by
  ring

/-- Reindex the two copies of an `(r + 1)`-particle block back to the same
one-copy scalar factors.  The domain is already arranged as one head block of
size `d` followed by the `r + (r + 1)` reduced spatial gaps. -/
def reflectedSelfPairFactorIndex
    (d r : Nat)
    (j : Fin (d + (r + (r + 1)) * d)) : Fin ((r + 1) * d) :=
  let h := reflectedSelfPairHeadTailArity d r
  let p := finProdFinEquiv.symm ((finCongr h).symm j)
  finProdFinEquiv
    (Fin.addCases (fun c : Fin (r + 1) => c)
      (fun c : Fin (r + 1) => c) p.1, p.2)

@[simp]
theorem reflectedSelfPairFactorIndex_left
    (d r : Nat)
    (h : ((r + 1) + (r + 1)) * d = d + (r + (r + 1)) * d)
    (c : Fin (r + 1)) (mu : Fin d) :
    reflectedSelfPairFactorIndex d r
        ((finCongr h) (finProdFinEquiv (Fin.castAdd (r + 1) c, mu))) =
      finProdFinEquiv (c, mu) := by
  simp [reflectedSelfPairFactorIndex]

@[simp]
theorem reflectedSelfPairFactorIndex_right
    (d r : Nat)
    (h : ((r + 1) + (r + 1)) * d = d + (r + (r + 1)) * d)
    (c : Fin (r + 1)) (mu : Fin d) :
    reflectedSelfPairFactorIndex d r
        ((finCongr h) (finProdFinEquiv (Fin.natAdd (r + 1) c, mu))) =
      finProdFinEquiv (c, mu) := by
  simp [reflectedSelfPairFactorIndex]
  apply Fin.ext
  have hc : ¬c.val + (r + 1) ≤ r := by omega
  simp [Fin.addCases, hc]

/-- The duplicated factor family in head-plus-reduced-tail coordinates. -/
noncomputable def reflectedSelfPairFullApproxIdentity
    {d r : Nat}
    (I : Section43ProductTimeApproximateIdentity ((r + 1) * d)) :
    Section43ProductTimeApproximateIdentity
      (d + (r + (r + 1)) * d) :=
  I.reindex (reflectedSelfPairFactorIndex d r)

/-- Equality transport between the native two-block flat coordinates and the
head-plus-reduced-tail coordinates used by block integration. -/
noncomputable def reflectedSelfPairHeadTailCastCLE
    (d r : Nat) :
    (Fin (((r + 1) + (r + 1)) * d) -> Real) ≃L[Real]
      (Fin (d + (r + (r + 1)) * d) -> Real) :=
  ContinuousLinearEquiv.piCongrLeft Real
    (fun _ : Fin (d + (r + (r + 1)) * d) => Real)
    (finCongr (reflectedSelfPairHeadTailArity d r))

/-- The reflected block-global chart in head-plus-reduced-tail coordinates. -/
noncomputable def reflectedSelfPairHeadTailSpatialCLE
    (d r : Nat) [NeZero d] :
    (Fin (d + (r + (r + 1)) * d) -> Real) ≃L[Real]
      (Fin (d + (r + (r + 1)) * d) -> Real) :=
  (reflectedSelfPairHeadTailCastCLE d r).symm |>.trans
    ((axisPairBlockGlobalSpatialFlatCLE d (r + 1) (r + 1)).trans
      (reflectedSelfPairHeadTailCastCLE d r))

theorem reflectedSelfPairHeadTailCastCLE_measurePreserving
    (d r : Nat) :
    MeasurePreserving
      (reflectedSelfPairHeadTailCastCLE d r
        ).toHomeomorph.toMeasurableEquiv
      (volume : Measure
        (Fin (((r + 1) + (r + 1)) * d) -> Real))
      (volume : Measure
        (Fin (d + (r + (r + 1)) * d) -> Real)) := by
  simpa [reflectedSelfPairHeadTailCastCLE] using
    (volume_measurePreserving_piCongrLeft
      (fun _ : Fin (d + (r + (r + 1)) * d) => Real)
      (finCongr (by ring :
        ((r + 1) + (r + 1)) * d = d + (r + (r + 1)) * d)))

/-- The reflected head-tail chart has unit Jacobian. -/
theorem reflectedSelfPairHeadTailSpatialCLE_measurePreserving
    (d r : Nat) [NeZero d] :
    MeasurePreserving
      (reflectedSelfPairHeadTailSpatialCLE d r
        ).toHomeomorph.toMeasurableEquiv
      (volume : Measure
        (Fin (d + (r + (r + 1)) * d) -> Real))
      (volume : Measure
        (Fin (d + (r + (r + 1)) * d) -> Real)) := by
  have hcast := reflectedSelfPairHeadTailCastCLE_measurePreserving d r
  exact hcast.symm.trans
    ((axisPairBlockGlobalSpatialFlatCLE_measurePreserving
      d (r + 1) (r + 1)).trans hcast)

/-- The normalized shrinking reduced spatial probe for the reflected
self-pair of one source block. -/
noncomputable def reflectedSelfPairMarginalSpatialApproxIdentity
    {d r : Nat} [NeZero d]
    (I : Section43ProductTimeApproximateIdentity ((r + 1) * d)) :
    OSIIEquation621SpatialApproxIdentityData
      ((r + (r + 1)) * d) :=
  (I.reflectedSelfPairFullApproxIdentity.toEquation621SpatialApproxIdentity
    ).headMarginalPullback
      (reflectedSelfPairHeadTailSpatialCLE d r)
      (reflectedSelfPairHeadTailSpatialCLE_measurePreserving d r).symm

/-- Regard a head-plus-reduced-tail flat test as a test in the native
separate two-block spatial coordinates. -/
noncomputable def reflectedSelfPairSeparateSpatialTest
    (d r : Nat) [NeZero d]
    (G : SchwartzMap (Fin (d + (r + (r + 1)) * d) -> Real) Complex) :
    SchwartzMap
      (Section43SpatialSpace d ((r + 1) + (r + 1))) Complex :=
  (section43SpatialFlatSchwartzCLE d ((r + 1) + (r + 1))).symm
    (SchwartzMap.compCLMOfContinuousLinearEquiv Complex
      (reflectedSelfPairHeadTailCastCLE d r) G)

private theorem integrateHeadBlock_eq_scv
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

/-- Prepending the spatial head in the canonical reduced arity and then
transporting back to the native equal-block arity is exactly the flat
head-tail reindexing used by the reflected chart. -/
theorem reflectedSelfPairSpatialTupleTransport_prependBasepoint
    (d r : Nat) [NeZero d]
    (x0 : Fin d -> Real)
    (x : Fin ((r + (r + 1)) * d) -> Real) :
    section43SpatialTupleTransport d (by omega)
        (section43SpatialPrependBasepoint x0
          ((section43SpatialFlatCLE d (r + (r + 1))).symm x)) =
      (section43SpatialFlatCLE d ((r + 1) + (r + 1))).symm
        ((reflectedSelfPairHeadTailCastCLE d r).symm
          (Fin.append x0 x)) := by
  let h : (r + (r + 1)) + 1 = (r + 1) + (r + 1) := by omega
  change section43SpatialTupleTransport d h _ = _
  apply (section43SpatialParticleCLE d ((r + 1) + (r + 1))).injective
  funext i mu
  rw [section43SpatialParticleCLE_tupleTransport]
  change
    section43SpatialParticleCLE d ((r + (r + 1)) + 1)
        (section43SpatialPrependBasepoint x0
          ((section43SpatialFlatCLE d (r + (r + 1))).symm x))
        (Fin.cast h.symm i) mu =
      ((reflectedSelfPairHeadTailCastCLE d r).symm
        (Fin.append x0 x)) (finProdFinEquiv (i, mu))
  let c : Fin ((r + (r + 1)) + 1) := Fin.cast h.symm i
  have hi : i = Fin.cast h c := by simp [c]
  rw [hi]
  change
    section43SpatialParticleCLE d ((r + (r + 1)) + 1)
        (section43SpatialPrependBasepoint x0
          ((section43SpatialFlatCLE d (r + (r + 1))).symm x)) c mu =
      ((reflectedSelfPairHeadTailCastCLE d r).symm
        (Fin.append x0 x)) (finProdFinEquiv (Fin.cast h c, mu))
  refine Fin.cases ?_ ?_ c
  · rw [section43SpatialParticleCLE_apply,
      section43SpatialPrependBasepoint_zero]
    nth_rewrite 1 [← Fin.append_left x0 x mu]
    congr 1
  · intro j
    rw [section43SpatialParticleCLE_apply,
      section43SpatialPrependBasepoint_succ,
      section43SpatialFlatCLE_symm_apply]
    nth_rewrite 1 [← Fin.append_right x0 x
      (finProdFinEquiv (j, mu))]
    congr 1
    apply Fin.ext
    simp [finProdFinEquiv]
    ring

/-- Coordinate-only marginal identity.  Pulling a native separate-block test
through the reflected spatial chart and integrating its absolute head is the
same operation as flat pullback by `reflectedSelfPairHeadTailSpatialCLE`
followed by ordinary head-block integration. -/
theorem reflectedSelfPair_marginal_flat_eq
    (d r : Nat) [NeZero d]
    (G : SchwartzMap (Fin (d + (r + (r + 1)) * d) -> Real) Complex) :
    section43SpatialFlatSchwartzCLE d (r + (r + 1))
        (section43SpatialHeadMarginal
          (section43SpatialSchwartzTransport d (by omega)
            (GeneratorHermiteHilbertFieldFamilyData.axisPairGlobalSpatialPullbackCLM
              (d := d) (r + 1) (r + 1)
              (reflectedSelfPairSeparateSpatialTest d r G)))) =
      integrateHeadBlock
        (SchwartzMap.compCLMOfContinuousLinearEquiv Complex
          (reflectedSelfPairHeadTailSpatialCLE d r).symm G) := by
  rw [integrateHeadBlock_eq_scv]
  ext x
  rw [section43SpatialFlatSchwartzCLE_apply,
    section43SpatialHeadMarginal_apply,
    SCV.integrateHeadBlock_apply_finAppend]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x0
  let h : (r + 1) + (r + 1) = (r + (r + 1)) + 1 := by omega
  change section43SpatialSchwartzTransport d h _
      (section43SpatialPrependBasepoint x0
        ((section43SpatialFlatCLE d (r + (r + 1))).symm x)) = _
  nth_rewrite 1 [← section43SpatialTupleTransport_symm d h
    (section43SpatialPrependBasepoint x0
      ((section43SpatialFlatCLE d (r + (r + 1))).symm x))]
  rw [section43SpatialSchwartzTransport_apply]
  rw [reflectedSelfPairSpatialTupleTransport_prependBasepoint]
  simp [
    GeneratorHermiteHilbertFieldFamilyData.axisPairGlobalSpatialPullbackCLM,
    reflectedSelfPairSeparateSpatialTest,
    reflectedSelfPairHeadTailSpatialCLE,
    axisPairBlockGlobalSpatialFlatCLE,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

/-- Duplicate one absolute block center into the two separate copies used by
the reflected self-pair source, in head-plus-reduced-tail flat coordinates. -/
def reflectedSelfPairDuplicatedSpatialCenter
    (d r : Nat)
    (y : Fin ((r + 1) * d) -> Real) :
    Fin (d + (r + (r + 1)) * d) -> Real :=
  fun j => y (reflectedSelfPairFactorIndex d r j)

/-- The same translated one-particle factor on both copies of a source block. -/
noncomputable def reflectedSelfPairDuplicatedSpatialFactor
    {d r : Nat}
    (I : Section43ProductTimeApproximateIdentity ((r + 1) * d))
    (y : Fin ((r + 1) * d) -> Real)
    (N : Nat) (c : Fin ((r + 1) + (r + 1))) :
    SchwartzMap (Fin d -> Real) Complex :=
  Fin.addCases
    (I.translatedSpatialParticleFactor y N)
    (I.translatedSpatialParticleFactor y N) c

@[simp]
theorem reflectedSelfPairDuplicatedSpatialFactor_left
    {d r : Nat}
    (I : Section43ProductTimeApproximateIdentity ((r + 1) * d))
    (y : Fin ((r + 1) * d) -> Real)
    (N : Nat) (c : Fin (r + 1)) :
    I.reflectedSelfPairDuplicatedSpatialFactor y N
        (Fin.castAdd (r + 1) c) =
      I.translatedSpatialParticleFactor y N c := by
  rw [reflectedSelfPairDuplicatedSpatialFactor, Fin.addCases_left]

@[simp]
theorem reflectedSelfPairDuplicatedSpatialFactor_right
    {d r : Nat}
    (I : Section43ProductTimeApproximateIdentity ((r + 1) * d))
    (y : Fin ((r + 1) * d) -> Real)
    (N : Nat) (c : Fin (r + 1)) :
    I.reflectedSelfPairDuplicatedSpatialFactor y N
        (Fin.natAdd (r + 1) c) =
      I.translatedSpatialParticleFactor y N c := by
  rw [reflectedSelfPairDuplicatedSpatialFactor, Fin.addCases_right]

/-- Every translated spatial particle factor is real-valued and hence fixed
by complex conjugation. -/
@[simp]
theorem translatedSpatialParticleFactor_conj
    {d r : Nat}
    (I : Section43ProductTimeApproximateIdentity ((r + 1) * d))
    (y : Fin ((r + 1) * d) -> Real)
    (N : Nat) (c : Fin (r + 1)) :
    (I.translatedSpatialParticleFactor y N c).conj =
      I.translatedSpatialParticleFactor y N c := by
  ext z
  simp only [translatedSpatialParticleFactor, spatialParticleFactor,
    SCV.translateSchwartz_apply, section43TimeProductSource,
    section43TimeProductTensor, SchwartzMap.productTensor_apply,
    SchwartzMap.conj_apply, map_prod]
  apply Finset.prod_congr rfl
  intro mu _hmu
  apply Complex.ext
  · simp
  · have hreal :
        ((I.factors N (finProdFinEquiv (c, mu))).f
          ((z + -spatialParticlePoint y c) mu)).im = 0 :=
      I.factor_real N (finProdFinEquiv (c, mu))
        ((z + -spatialParticlePoint y c) mu)
    change
      -((I.factors N (finProdFinEquiv (c, mu))).f
          ((z + -spatialParticlePoint y c) mu)).im =
        ((I.factors N (finProdFinEquiv (c, mu))).f
          ((z + -spatialParticlePoint y c) mu)).im
    rw [hreal]
    simp

/-- The self-pair of one real translated particle product is the duplicated
particle product on the native separate two-block coordinates. -/
theorem section43TwoBlockSpatialProduct_self_eq_duplicated
    {d r : Nat} [NeZero d]
    (I : Section43ProductTimeApproximateIdentity ((r + 1) * d))
    (y : Fin ((r + 1) * d) -> Real)
    (N : Nat) :
    section43TwoBlockSpatialProduct
        (section43SpatialProductCMM d (r + 1)
          (I.translatedSpatialParticleFactor y N))
        (section43SpatialProductCMM d (r + 1)
          (I.translatedSpatialParticleFactor y N)) =
      section43SpatialProductCMM d ((r + 1) + (r + 1))
        (I.reflectedSelfPairDuplicatedSpatialFactor y N) := by
  simpa only [reflectedSelfPairDuplicatedSpatialFactor_left,
    reflectedSelfPairDuplicatedSpatialFactor_right,
    translatedSpatialParticleFactor_conj] using
    section43TwoBlockSpatialProduct_particleProducts_eq
      d (r + 1) (r + 1)
      (I.reflectedSelfPairDuplicatedSpatialFactor y N)

/-- The translated duplicated flat probe, transported back to native
separate-block coordinates, is exactly the duplicated particle product. -/
theorem reflectedSelfPairSeparateSpatialTest_translatedTest_eq_product
    {d r : Nat} [NeZero d]
    (I : Section43ProductTimeApproximateIdentity ((r + 1) * d))
    (y : Fin ((r + 1) * d) -> Real)
    (N : Nat) :
    reflectedSelfPairSeparateSpatialTest d r
        ((I.reflectedSelfPairFullApproxIdentity.toEquation621SpatialApproxIdentity
          ).translatedTest
          (reflectedSelfPairDuplicatedSpatialCenter d r y) N) =
      section43SpatialProductCMM d ((r + 1) + (r + 1))
        (I.reflectedSelfPairDuplicatedSpatialFactor y N) := by
  ext eta
  simp only [reflectedSelfPairSeparateSpatialTest,
    section43SpatialFlatSchwartzCLE_symm_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply,
    OSIIEquation621SpatialApproxIdentityData.translatedTest,
    SCV.translateSchwartz_apply,
    toEquation621SpatialApproxIdentity,
    reflectedSelfPairFullApproxIdentity,
    Section43ProductTimeApproximateIdentity.test_apply,
    section43TimeProductSource, section43TimeProductTensor,
    SchwartzMap.productTensor_apply,
    section43SpatialProductCMM_apply,
    section43SpatialSchwartzParticleCLE_symm_apply]
  let h : ((r + 1) + (r + 1)) * d =
      d + (r + (r + 1)) * d := by ring
  nth_rewrite 1 [← Equiv.prod_comp (finCongr h)]
  nth_rewrite 1 [← Equiv.prod_comp finProdFinEquiv]
  simp only [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro c _hc
  refine Fin.addCases ?_ ?_ c
  · intro c
    simp only [reflectedSelfPairDuplicatedSpatialFactor,
      Fin.addCases_left, translatedSpatialParticleFactor,
      spatialParticleFactor, SCV.translateSchwartz_apply,
      section43TimeProductSource, section43TimeProductTensor,
      SchwartzMap.productTensor_apply]
    apply Finset.prod_congr rfl
    intro mu _hmu
    have hidx :
        reflectedSelfPairFactorIndex d r
            (Fin.cast h
              (finProdFinEquiv (Fin.castAdd (r + 1) c, mu))) =
          finProdFinEquiv (c, mu) := by
      exact reflectedSelfPairFactorIndex_left d r h c mu
    simp only [Section43ProductTimeApproximateIdentity.reindex,
      reflectedSelfPairFactorIndex_left]
    simp [reflectedSelfPairHeadTailCastCLE,
      reflectedSelfPairDuplicatedSpatialCenter,
      spatialParticlePoint, section43SpatialFlatCLE_apply,
      section43SpatialParticleCLE_apply]
    rw [hidx]
  · intro c
    simp only [reflectedSelfPairDuplicatedSpatialFactor,
      Fin.addCases_right, translatedSpatialParticleFactor,
      spatialParticleFactor, SCV.translateSchwartz_apply,
      section43TimeProductSource, section43TimeProductTensor,
      SchwartzMap.productTensor_apply]
    apply Finset.prod_congr rfl
    intro mu _hmu
    have hc : c.addNat (r + 1) = Fin.natAdd (r + 1) c := by
      apply Fin.ext
      simp
    have hidx :
        reflectedSelfPairFactorIndex d r
            (Fin.cast h
              (finProdFinEquiv (c.addNat (r + 1), mu))) =
          finProdFinEquiv (c, mu) := by
      rw [hc]
      exact reflectedSelfPairFactorIndex_right d r h c mu
    simp only [Section43ProductTimeApproximateIdentity.reindex,
      reflectedSelfPairFactorIndex_right]
    simp [reflectedSelfPairHeadTailCastCLE,
      reflectedSelfPairDuplicatedSpatialCenter,
      spatialParticlePoint, section43SpatialFlatCLE_apply,
      section43SpatialParticleCLE_apply]
    rw [hidx]

/-- Evaluation form of the reflected self-pair marginal probe.  A translated
full duplicated probe is first pulled through the reflected block-global
chart; integrating its absolute spatial basepoint gives the translated
reduced probe at the tail of the transformed center. -/
theorem reflectedSelfPairMarginalSpatialApproxIdentity_section43Probe_eq
    {d r : Nat} [NeZero d]
    (I : Section43ProductTimeApproximateIdentity ((r + 1) * d))
    (a : Fin (d + (r + (r + 1)) * d) -> Real)
    (N : Nat) :
    I.reflectedSelfPairMarginalSpatialApproxIdentity.section43Probe
        (splitLast d ((r + (r + 1)) * d)
          (reflectedSelfPairHeadTailSpatialCLE d r a)) N =
      (section43SpatialFlatSchwartzCLE d (r + (r + 1))).symm
        (integrateHeadBlock
          (SchwartzMap.compCLMOfContinuousLinearEquiv Complex
            (reflectedSelfPairHeadTailSpatialCLE d r).symm
            (OSIIEquation621SpatialApproxIdentityData.translatedTest
              I.reflectedSelfPairFullApproxIdentity.toEquation621SpatialApproxIdentity
              a N))) := by
  rw [OSIIEquation621SpatialApproxIdentityData.section43Probe]
  congr 1
  symm
  exact
    OSIIEquation621SpatialApproxIdentityData.headMarginalPullback_translatedTest
      I.reflectedSelfPairFullApproxIdentity.toEquation621SpatialApproxIdentity
      (reflectedSelfPairHeadTailSpatialCLE d r)
      (reflectedSelfPairHeadTailSpatialCLE_measurePreserving d r).symm a N

/-- The genuine reflected marginal probe is exactly the mixed spatial Gram
probe formed from one translated product approximate identity. -/
theorem reflectedSelfPairMarginalSpatialApproxIdentity_section43Probe_eq_mixed
    {d r : Nat} [NeZero d]
    (I : Section43ProductTimeApproximateIdentity ((r + 1) * d))
    (y : Fin ((r + 1) * d) -> Real)
    (N : Nat) :
    I.reflectedSelfPairMarginalSpatialApproxIdentity.section43Probe
        (splitLast d ((r + (r + 1)) * d)
          (reflectedSelfPairHeadTailSpatialCLE d r
            (reflectedSelfPairDuplicatedSpatialCenter d r y))) N =
      osiiMixedSpatialHeadMarginal
        (section43SpatialProductCMM d (r + 1)
          (I.translatedSpatialParticleFactor y N))
        (section43SpatialProductCMM d (r + 1)
          (I.translatedSpatialParticleFactor y N)) := by
  rw [reflectedSelfPairMarginalSpatialApproxIdentity_section43Probe_eq]
  apply (section43SpatialFlatSchwartzCLE d (r + (r + 1))).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [← reflectedSelfPair_marginal_flat_eq d r]
  unfold osiiMixedSpatialHeadMarginal
  rw [reflectedSelfPairSeparateSpatialTest_translatedTest_eq_product]
  rw [← section43TwoBlockSpatialProduct_self_eq_duplicated]

end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
