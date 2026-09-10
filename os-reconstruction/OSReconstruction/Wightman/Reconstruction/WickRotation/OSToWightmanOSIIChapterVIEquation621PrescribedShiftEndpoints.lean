import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621PrescribedShiftRows
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRawGeneratedNormalizedWeightedL1RankLocalEndpointShellFirstRecovery

/-!
# Prescribed-shift one-particle source rows

The empty chronological parameter needs no new analytic continuation. The
actual OS semigroup moves its packet anchor by half the requested shift, and
the existing positive-real packet limit gives the damped lower distribution.
-/

noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

open Section43ProductTimeApproximateIdentity

variable {d : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

/-- A one-particle packet absorbs the exact half shift in its sole source
time. No growth hypothesis or packet-scale restriction is used. -/
theorem oneParticlePacket_halfShift
    (I : Section43ProductTimeApproximateIdentity 1)
    (tau : Fin 1 -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion 1)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (chi : SchwartzMap (Section43SpatialSpace d 1) Complex) (N : Nat) :
    osiiOriginalOSHilbertComplex OS ((epsilon / 2 : Real) : Complex)
        (osiiPositiveTimeSingleVectorCLM OS 1
          (I.translatedPositiveTimeSpatialSource tau htau chi N)) =
      osiiPositiveTimeSingleVectorCLM OS 1
        (I.translatedPositiveTimeSpatialSource
          (equation621ShiftedSourceCenter epsilon tau)
          (equation621ShiftedSourceCenter_positive hepsilon.le htau) chi N) := by
  let shifted := equation621ShiftedSourceCenter epsilon tau
  have hpositive : shifted ∈ section43TimeStrictPositiveRegion 1 :=
    equation621ShiftedSourceCenter_positive hepsilon.le htau
  rw [osiiOriginalOSHilbertComplex_ofReal_single_eq_shift OS _ _
    (half_pos hepsilon)]
  refine (osiiOriginalOSHilbertShift_single_eq OS
    (I.translatedPositiveTimeSpatialSource tau htau chi N)
    ⟨epsilon / 2, half_pos hepsilon⟩).trans ?_
  apply congrArg (osiiPositiveTimeSingleVectorCLM OS 1)
  apply Subtype.ext
  have hinternal : chronologicalPacketInternalRecentering tau shifted =
      (0 : Fin 0 -> Real) := Subsingleton.elim _ _
  have hfirst : chronologicalPacketFirstTimeRecentering tau shifted =
      epsilon / 2 := by
    simp [chronologicalPacketFirstTimeRecentering, shifted]
  simpa only [osiiOriginalOSPositiveTimeShiftSource, hinternal, hfirst,
    map_zero, translateSchwartzConfiguration_zero] using
    timeShift_chronologicalTranslate_translatedPositiveTimeSpatialSource
      I tau shifted htau hpositive chi N

/-- The raw one-particle packet sequence has the actual damped predecessor
limit at every prescribed positive shift, independently of its starting tail. -/
theorem tendsto_oneParticlePacket_dampedDiagonal
    {L : SimultaneousTimeContinuationStageLevel d}
    (H : L.HasCanonicalReducedCompactEdges OS)
    (I : Section43ProductTimeApproximateIdentity 1)
    (tau : Fin 1 -> Real)
    (htau : tau ∈ section43TimeStrictPositiveRegion 1)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (chi : SchwartzMap (Section43SpatialSpace d 1) Complex)
    (tail : Nat) :
    let vector := fun N => osiiPositiveTimeSingleVectorCLM OS 1
      (I.translatedPositiveTimeSpatialSource tau htau chi (N + tail))
    Tendsto (fun N => @inner Complex (OSHilbertSpace OS) _ (vector N)
        (osiiOriginalOSHilbertComplex OS (epsilon : Complex) (vector N)))
      atTop (nhds ((L.stage 1).distribution
        (equation621DampedReflectedStagePoint epsilon
          (reflectedChronologicalGapMap 0 (tau, tau)) 0)
        (osiiMixedSpatialHeadMarginal chi chi))) := by
  dsimp only
  let shifted := equation621ShiftedSourceCenter epsilon tau
  have hpositive : shifted ∈ section43TimeStrictPositiveRegion 1 :=
    equation621ShiftedSourceCenter_positive hepsilon.le htau
  let D : OneParticleTranslatedMixedDeltaPredecessorData L OS I shifted hpositive :=
    Classical.choice
      (SimultaneousTimeContinuationStageLevel.exists_oneParticleTranslatedMixedDeltaPredecessorData H)
  let vector := fun N => osiiPositiveTimeSingleVectorCLM OS 1
    (I.translatedPositiveTimeSpatialSource shifted hpositive chi N)
  have hraw : Tendsto (fun N => @inner Complex (OSHilbertSpace OS) _
        (vector N) (vector N)) atTop
      (nhds ((L.stage 1).distribution
        (equation621ReflectedMovingSlicePoint (0 : Fin (0 + 0) -> Complex)
          (osiiMixedBlockGlobalReducedTime 0 (Fin.append shifted shifted)))
        (osiiMixedSpatialHeadMarginal chi chi))) := by
    apply (tendsto_add_atTop_iff_nat D.tailStart).1
    simpa [vector, OneParticleTranslatedMixedDeltaPredecessorData.field] using
      D.tendsto_inner_field_add_to_distribution_at_anchor chi 0
  have htime : equation621ReflectedMovingSlicePoint
      (0 : Fin (0 + 0) -> Complex)
      (osiiMixedBlockGlobalReducedTime 0 (Fin.append shifted shifted)) =
        equation621DampedReflectedStagePoint epsilon
          (reflectedChronologicalGapMap 0 (tau, tau)) 0 := by
    rw [osiiMixedBlockGlobalReducedTime_append_eq_reflectedChronologicalGapMap]
    have hunshift : osiiVI2Unshift 0 epsilon (0 : Fin 0 -> Complex) = 0 :=
      Subsingleton.elim _ _
    rw [equation621DampedReflectedStagePoint, hunshift,
      ← reflectedCauchyShiftedStagePoint_equation621ShiftedSourceCenter]
    have hcenter : reflectedCauchyCenter (0 : Fin 0 -> Complex) = 0 := by
      funext j
      exact Fin.elim0 j
    simpa only [hcenter] using
      equation621ReflectedMovingSlicePoint_reflectedCauchyCenter
        (reflectedChronologicalGapMap 0 (shifted, shifted))
        (0 : Fin 0 -> Complex)
  rw [htime] at hraw
  have htail := hraw.comp (tendsto_add_atTop_nat tail)
  apply (tendsto_congr' (Filter.Eventually.of_forall fun N => ?_)).2 htail
  rw [← osiiOriginalOSHilbertComplex_inner_halfShift_self OS hepsilon,
    oneParticlePacket_halfShift I tau htau hepsilon chi (N + tail)]
  rfl

namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData
namespace RootedA0BlockContinuousTranslationData

variable {k : Nat} [NeZero k]
variable {I : Section43ProductTimeApproximateIdentity k}
variable {anchor : Fin k -> Real}
variable {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
variable {R : TripleConvolutionRootData I}

theorem leftArbitrarySpatialGeneratorField_zero_eq_rootedSource
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k) (scale : Nat)
    (chi : SchwartzMap (Section43SpatialSpace d ((i.n - 1) + 1)) Complex) :
    H.leftArbitrarySpatialGeneratorField i scale chi 0 =
      osiiPositiveTimeSingleVectorCLM OS ((i.n - 1) + 1)
        (A.rootedLeftBlockSpatialSource R i
          (scale + H.commonTailStart i) chi) := by
  simpa only [leftArbitrarySpatialGeneratorField,
    rootedLeftBlockTranslatedSpatialSource_zero,
    leftCofinalIndex_add_tailStart] using
    (H.left i).zero_eq (H.leftCofinalIndex i scale) chi

theorem rightArbitrarySpatialGeneratorField_zero_eq_rootedSource
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k) (scale : Nat)
    (chi : SchwartzMap (Section43SpatialSpace d ((i.m - 1) + 1)) Complex) :
    H.rightArbitrarySpatialGeneratorField i scale chi 0 =
      osiiPositiveTimeSingleVectorCLM OS ((i.m - 1) + 1)
        (A.rootedRightBlockSpatialSource R i
          (scale + H.commonTailStart i) chi) := by
  simpa only [rightArbitrarySpatialGeneratorField,
    rootedRightBlockTranslatedSpatialSource_zero,
    rightCofinalIndex_add_tailStart] using
    (H.right i).zero_eq (H.rightCofinalIndex i scale) chi

/-- The actual left one-particle field has the prescribed-shift lower row in
any canonical predecessor stage. The opposite block can also be one particle. -/
theorem tendsto_leftOneParticle_dampedDiagonal
    (H : RootedA0BlockContinuousTranslationData OS A R)
    {L : SimultaneousTimeContinuationStageLevel d}
    (hL : L.HasCanonicalReducedCompactEdges OS)
    (m : Nat) (hm : 1 <= m) (hindex : k = 1 + m - 1)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (chi : SchwartzMap (Section43SpatialSpace d 1) Complex) :
    let i : GeneratorIndex k := ⟨1, m, le_rfl, hm, hindex⟩
    let field := fun N => H.leftArbitrarySpatialGeneratorField i N chi 0
    Tendsto (fun N => @inner Complex (OSHilbertSpace OS) _ (field N)
        (osiiOriginalOSHilbertComplex OS (epsilon : Complex) (field N)))
      atTop (nhds ((L.stage 1).distribution
        (equation621DampedReflectedStagePoint epsilon
          (reflectedChronologicalGapMap 0
            (A.rootedLeftBlockAnchor i, A.rootedLeftBlockAnchor i)) 0)
        (osiiMixedSpatialHeadMarginal chi chi))) := by
  dsimp only
  let i : GeneratorIndex k := ⟨1, m, le_rfl, hm, hindex⟩
  simpa only [leftArbitrarySpatialGeneratorField_zero_eq_rootedSource,
    rootedLeftBlockSpatialSource] using
    tendsto_oneParticlePacket_dampedDiagonal hL
      (A.rootedLeftBlockApproximateIdentity R i)
      (A.rootedLeftBlockAnchor i) (A.rootedLeftBlockAnchor_positive i)
      hepsilon chi (H.commonTailStart i)

/-- Right-hand companion, including the two-point corner. -/
theorem tendsto_rightOneParticle_dampedDiagonal
    (H : RootedA0BlockContinuousTranslationData OS A R)
    {L : SimultaneousTimeContinuationStageLevel d}
    (hL : L.HasCanonicalReducedCompactEdges OS)
    (n : Nat) (hn : 1 <= n) (hindex : k = n + 1 - 1)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (chi : SchwartzMap (Section43SpatialSpace d 1) Complex) :
    let i : GeneratorIndex k := ⟨n, 1, hn, le_rfl, hindex⟩
    let field := fun N => H.rightArbitrarySpatialGeneratorField i N chi 0
    Tendsto (fun N => @inner Complex (OSHilbertSpace OS) _ (field N)
        (osiiOriginalOSHilbertComplex OS (epsilon : Complex) (field N)))
      atTop (nhds ((L.stage 1).distribution
        (equation621DampedReflectedStagePoint epsilon
          (reflectedChronologicalGapMap 0
            (A.rootedRightBlockAnchor i, A.rootedRightBlockAnchor i)) 0)
        (osiiMixedSpatialHeadMarginal chi chi))) := by
  dsimp only
  let i : GeneratorIndex k := ⟨n, 1, hn, le_rfl, hindex⟩
  simpa only [rightArbitrarySpatialGeneratorField_zero_eq_rootedSource,
    rootedRightBlockSpatialSource] using
    tendsto_oneParticlePacket_dampedDiagonal hL
      (A.rootedRightBlockApproximateIdentity R i)
      (A.rootedRightBlockAnchor i) (A.rootedRightBlockAnchor_positive i)
      hepsilon chi (H.commonTailStart i)

/-- The same sharp middle-root estimate applies to every generator split,
including either one-particle endpoint and the two-point corner. -/
theorem norm_generatorSemigroupCandidate_middleRoot_shift_le
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k) (scale : Nat)
    (left : (Fin (i.n - 1) -> Complex) -> OSHilbertSpace OS)
    (right : (Fin (i.m - 1) -> Complex) -> OSHilbertSpace OS)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (z : OSIITimeGapSpace k)
    (hbridge : epsilon < (z i.bridgeGlobalIndex).re) :
    let x := left (equation621TargetLeftParameter i z)
    let y := right (equation621TargetRightParameter i z)
    ‖generatorSemigroupCandidate OS lgc i left
        (fun w => H.semigroupBridgeRootOperator lgc i scale (right w))
        (generatorChronologicalParameterComplexCLE i z)‖ <=
      Real.sqrt
        (‖@inner Complex (OSHilbertSpace OS) _ x
            (osiiOriginalOSHilbertComplex OS (epsilon : Complex) x)‖ *
          ‖@inner Complex (OSHilbertSpace OS) _ y
            (osiiOriginalOSHilbertComplex OS (epsilon : Complex) y)‖) := by
  dsimp only
  have hremaining : 0 < (z i.bridgeGlobalIndex - (epsilon : Complex)).re := by
    simpa using sub_pos.mpr hbridge
  have hbridgeEq :
      (generatorChronologicalParameterComplexCLE i z) i.bridgeGlobalIndex =
        z i.bridgeGlobalIndex := generatorChronological_split_fst i z
  rw [generatorSemigroupCandidate_apply]
  change ‖@inner Complex (OSHilbertSpace OS) _
      (left (equation621TargetLeftParameter i z))
      (osiiOriginalOSHilbertComplex OS
        ((generatorChronologicalParameterComplexCLE i z) i.bridgeGlobalIndex)
        (H.semigroupBridgeRootOperatorOfOS i scale
          (right (equation621TargetRightParameter i z))))‖ <= _
  rw [hbridgeEq]
  simpa only [sub_add_cancel] using
    H.norm_inner_semigroupBridgeRootOperatorOfOS_shift_le
      i scale hepsilon hremaining
      (left (equation621TargetLeftParameter i z))
      (right (equation621TargetRightParameter i z))

end RootedA0BlockContinuousTranslationData
end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity

end OSIIChapterV
end OSReconstruction
