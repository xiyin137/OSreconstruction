import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIReflectedTwoScaleSemigroupAdapter
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621SourceIntegralSegment
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621VacuumTailSourceRank
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621ReflectedDiagonalProbeLimit
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621ReflectedSourceAnchorCutoff

/-!
# Prescribed-shift sources for the normalized VI.2 successor

The normalization shift is independent of the small source cutoff. A full
shift moves each state head by half that amount and every internal gap by
the full amount. The existing compact-center atlas realizes this operation
at one unchanged analytic rank.
-/

noncomputable section

open Complex Filter Set Topology
open scoped Classical Pointwise

namespace OSReconstruction
namespace OSIIChapterV

open Section43ProductTimeApproximateIdentity

/-- The lower point sampled by a damped field at its current parameter.
Relative to the undamped reflected point, only the bridge gains `epsilon`. -/
def equation621DampedReflectedStagePoint
    {m : Nat} (epsilon : Real)
    (tau : Fin (m + (m + 1)) -> Real) (z : Fin m -> Complex) :
    OSIITimeGapSpace (m + (m + 1)) :=
  osiiVI2Shift (m + (m + 1)) epsilon
    (reflectedCauchyShiftedStagePoint tau (osiiVI2Unshift m epsilon z))

theorem equation621DampedReflectedStagePoint_eq_bridgeShift
    {m : Nat} (epsilon : Real)
    (tau : Fin (m + (m + 1)) -> Real) (z : Fin m -> Complex) :
    equation621DampedReflectedStagePoint epsilon tau z =
      reflectedCauchyShiftedStagePoint
        (reflectedCauchyBridgeUnshiftTime (-epsilon) tau) z := by
  ext j
  refine Fin.addCases (fun i => ?_) (fun r => ?_) j
  · simp [equation621DampedReflectedStagePoint, osiiVI2Shift, osiiVI2Unshift]
    ring
  · refine Fin.cases ?_ (fun i => ?_) r
    · simp [equation621DampedReflectedStagePoint, osiiVI2Shift]
    · simp [equation621DampedReflectedStagePoint, osiiVI2Shift, osiiVI2Unshift]
      ring

/-- Damping adds one copy of the prescribed shift to the reflected sum. -/
theorem sum_equation621DampedReflectedStagePoint
    {m : Nat} (epsilon : Real)
    (tau : Fin (m + (m + 1)) -> Real) (z : Fin m -> Complex) :
    (∑ j, equation621DampedReflectedStagePoint epsilon tau z j) =
      (∑ j, reflectedCauchyShiftedStagePoint tau z j) + (epsilon : Complex) := by
  rw [equation621DampedReflectedStagePoint_eq_bridgeShift,
    sum_reflectedCauchyShiftedStagePoint, sum_reflectedCauchyShiftedStagePoint]
  have htime : (∑ j, reflectedCauchyBridgeUnshiftTime (-epsilon) tau j) =
      (∑ j, tau j) + epsilon := by
    simp only [Fin.sum_univ_add, Fin.sum_univ_succ,
      reflectedCauchyBridgeUnshiftTime_left, reflectedCauchyBridgeUnshiftTime_bridge,
      reflectedCauchyBridgeUnshiftTime_right]
    ring
  have htimeC := congrArg (fun x : Real => (x : Complex)) htime
  push_cast at htimeC
  rw [htimeC]
  ring

theorem equation621DampedReflectedSourceNumerator
    {m : Nat} (epsilon : Real)
    (left right : Fin (m + 1) -> Real) (z : Fin m -> Complex) :
    1 + ∑ j, equation621DampedReflectedStagePoint epsilon
        (reflectedChronologicalGapMap m (left, right)) z j =
      ((1 + 2 * ∑ i, (z i).re + ∑ j, left j + ∑ j, right j + epsilon : Real) :
        Complex) := by
  rw [sum_equation621DampedReflectedStagePoint, ← add_assoc,
    equation621ReflectedChronologicalSourceNumerator]
  push_cast
  ring

theorem rankedMixedTail_mem_openZeroConvexKernel
    {m depth rank : Nat} {U : Set (Fin m -> Complex)}
    (hU : IsOpen U) (hzero : (0 : Fin m -> Complex) ∈ U)
    (hcover : osiiMixedTailArgumentCarrier
      (osiiStrictGeneratedMixedLogarithmicBaseAtRank (m + 1) depth rank) ⊆ U)
    {z : Fin m -> Complex}
    (hz : z ∈ osiiMixedTailArgumentCarrier
      (osiiStrictGeneratedMixedLogarithmicBaseAtRank (m + 1) depth rank)) :
    z ∈ openZeroConvexKernel U := by
  have hsegment : segment Real (0 : Fin m -> Complex) z ⊆ U := by
    intro w hw
    rw [segment_eq_image_lineMap] at hw
    obtain ⟨r, hr, rfl⟩ := hw
    by_cases hr0 : r = 0
    · subst r
      rw [AffineMap.lineMap_apply_zero]
      exact hzero
    · apply hcover
      simpa only [AffineMap.lineMap_apply_module, smul_zero, zero_add] using
        real_smul_mem_osiiMixedTailArgumentCarrier_of_pos hz
          (lt_of_le_of_ne hr.1 (Ne.symm hr0))
  exact mem_openZeroConvexKernel_of_segment_subset hU hsegment

/-- The whole positive-shift interpolation uses the original mixed rank. -/
theorem rankedMixedTail_shiftSegment_subset_openZeroConvexKernel
    {m depth rank : Nat} {U : Set (Fin m -> Complex)}
    (hU : IsOpen U) (hzero : (0 : Fin m -> Complex) ∈ U)
    (hcover : osiiMixedTailArgumentCarrier
      (osiiStrictGeneratedMixedLogarithmicBaseAtRank (m + 1) depth rank) ⊆ U)
    {z : Fin m -> Complex}
    (hz : z ∈ osiiMixedTailArgumentCarrier
      (osiiStrictGeneratedMixedLogarithmicBaseAtRank (m + 1) depth rank))
    {epsilon : Real} (hepsilon : 0 <= epsilon) :
    segment Real (osiiVI2Shift m epsilon z) z ⊆
      openZeroConvexKernel U := by
  intro w hw
  rw [segment_symm, segment_eq_image_lineMap Real z
    (osiiVI2Shift m epsilon z)] at hw
  obtain ⟨r, hr, rfl⟩ := hw
  have heq : AffineMap.lineMap z (osiiVI2Shift m epsilon z) r =
      osiiVI2Shift m (r * epsilon) z := by
    ext j
    simp only [AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply,
      osiiVI2Shift, Complex.real_smul]
    push_cast
    ring
  rw [heq]
  exact rankedMixedTail_mem_openZeroConvexKernel hU hzero hcover
    (StrictGeneratedScalarDepthPointedData.osiiVI2Shift_mem_mixedTailArgumentCarrier
      hz (mul_nonneg hr.1 hepsilon))

/-- One compact source carrier can retain an old carrier and the entire
internal recentering path, independently of both packet scales. -/
def equation621PrescribedShiftCenters
    {m : Nat} (old : Set (Fin (m + 1) -> Real))
    (anchor : Fin (m + 1) -> Real) (epsilon : Real) :
    Set (Fin (m + 1) -> Real) :=
  old ∪ segment Real anchor
      (chronologicalPacketInternalCenter anchor
        (equation621ShiftedSourceCenter epsilon anchor)) ∪
    {equation621ShiftedSourceCenter epsilon anchor}

theorem exists_equation621PrescribedShiftCarrier
    {m : Nat} (I : Section43ProductTimeApproximateIdentity (m + 1))
    {old : Set (Fin (m + 1) -> Real)}
    (holdCompact : IsCompact old)
    (holdPositive : old ⊆ section43TimeStrictPositiveRegion (m + 1))
    {anchor : Fin (m + 1) -> Real}
    (hanchor : anchor ∈ section43TimeStrictPositiveRegion (m + 1))
    {epsilon : Real} (hepsilon : 0 <= epsilon) :
    Nonempty (I.CompactCenterFamilyTimeCarrierData
      (equation621PrescribedShiftCenters old anchor epsilon)) := by
  let shifted := equation621ShiftedSourceCenter epsilon anchor
  let hybrid := chronologicalPacketInternalCenter anchor shifted
  have hshifted : shifted ∈ section43TimeStrictPositiveRegion (m + 1) :=
    equation621ShiftedSourceCenter_positive hepsilon hanchor
  have hhybrid : hybrid ∈ section43TimeStrictPositiveRegion (m + 1) :=
    chronologicalPacketInternalCenter_mem_strictPositive hanchor hshifted
  have hsegmentCompact : IsCompact (segment Real anchor hybrid) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  apply I.exists_compactCenterFamilyTimeCarrierData
  · exact (holdCompact.union hsegmentCompact).union isCompact_singleton
  · intro tau htau
    rcases htau with (htau | htau) | htau
    · exact holdPositive htau
    · exact mem_strictPositive_of_mem_packetCenter_segment hanchor hhybrid htau
    · simpa only [Set.mem_singleton_iff.mp htau] using hshifted

variable {d q : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

/-- The existing reflected-source record, with its index retaining the actual
packet scale at one selected center. -/
noncomputable def compactCenterReflectedGramSpatialSourceData
    {C0 : Type*} [CanonicalGeneratorStageLevelProvider OS C0]
    {S0 : C0} {depth : Nat}
    {I : Section43ProductTimeApproximateIdentity ((q + 1) + 1)}
    {centers : Set (Fin ((q + 1) + 1) -> Real)}
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S0 depth)
    (C : I.CompactCenterFamilyTimeCarrierData centers)
    (center : Fin ((q + 1) + 1) -> Real)
    (hcenter : center ∈ centers)
    (hpositive : center ∈ section43TimeStrictPositiveRegion ((q + 1) + 1)) :
    ReflectedGramSpatialSourceData (OS := OS) S0 q where
  carrier := C.carrier
  carrier_compact := C.carrier_compact
  carrier_positive := C.carrier_positive
  reflectedGram := P.forCarrier q C.carrier C.carrier_compact C.carrier_positive
  sourceCLM := fun scale => C.sourceCLM center hcenter hpositive scale

set_option maxHeartbeats 2000000 in
/-- The complete VI.2 shift is an exact identity of the continued packet
fields, not an assumed estimate on their norms. -/
theorem compactCenterReflectedGram_completeShift_field_eq
    {C0 : Type*} [CanonicalGeneratorStageLevelProvider OS C0]
    {S0 : C0} {depth rank : Nat}
    {I : Section43ProductTimeApproximateIdentity ((q + 1) + 1)}
    {centers : Set (Fin ((q + 1) + 1) -> Real)}
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S0 depth rank)
    (C : I.CompactCenterFamilyTimeCarrierData centers)
    (anchor : Fin ((q + 1) + 1) -> Real)
    (hanchor : anchor ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hsegment : segment Real anchor
      (chronologicalPacketInternalCenter anchor
        (equation621ShiftedSourceCenter epsilon anchor)) ⊆ centers)
    (hshifted : equation621ShiftedSourceCenter epsilon anchor ∈ centers)
    (lgc : OSLinearGrowthCondition d OS)
    (scale : Nat)
    (chi : SchwartzMap (Section43SpatialSpace d ((q + 1) + 1)) Complex)
    (z : Fin (q + 1) -> Complex)
    (hz : z ∈ osiiMixedTailArgumentCarrier
      (osiiStrictGeneratedMixedLogarithmicBaseAtRank
        ((q + 1) + 1) depth rank)) :
    let shifted := equation621ShiftedSourceCenter epsilon anchor
    let hpositive := equation621ShiftedSourceCenter_positive hepsilon.le hanchor
    let A := (P.forCarrier q C.carrier C.carrier_compact C.carrier_positive).atlas
    let field := A.gram.anchoredAtlasField A.sourceStage.stage A.sourceStage.germ
    field (C.sourceCLM shifted hshifted hpositive scale chi) z =
      osiiOriginalOSHilbertComplex OS ((epsilon / 2 : Real) : Complex)
        (field (C.sourceCLM anchor
          (hsegment (left_mem_segment Real _ _)) hanchor scale chi)
          (osiiVI2Shift (q + 1) epsilon z)) := by
  dsimp only
  let shifted := equation621ShiftedSourceCenter epsilon anchor
  have hpositive : shifted ∈
      section43TimeStrictPositiveRegion ((q + 1) + 1) :=
    equation621ShiftedSourceCenter_positive hepsilon.le hanchor
  let hybrid := chronologicalPacketInternalCenter anchor shifted
  have hhybrid : hybrid ∈
      section43TimeStrictPositiveRegion ((q + 1) + 1) :=
    chronologicalPacketInternalCenter_mem_strictPositive hanchor hpositive
  have hanchorCenters := hsegment (left_mem_segment Real anchor hybrid)
  have hhybridCenters := hsegment (right_mem_segment Real anchor hybrid)
  let source := compactCenterReflectedGramSpatialSourceData
    P.toAtlasFamily C shifted hshifted hpositive
  let A := source.reflectedGram.atlas
  let field := A.gram.anchoredAtlasField A.sourceStage.stage A.sourceStage.germ
  have hcover : osiiMixedTailArgumentCarrier
      (osiiStrictGeneratedMixedLogarithmicBaseAtRank
        ((q + 1) + 1) depth rank) ⊆ A.spatialLinearDomain :=
    (P.forCarrier q C.carrier C.carrier_compact C.carrier_positive
      ).coversStrictGeneratedAtRank
  have hradial := rankedMixedTail_mem_openZeroConvexKernel
    A.spatialLinearDomain_open source.zero_mem_spatialLinearDomain hcover hz
  have hrec : (fun j =>
      (chronologicalPacketInternalRecentering anchor hybrid j : Complex)) =
        (fun _ : Fin (q + 1) => (epsilon : Complex)) := by
    funext j
    simp [chronologicalPacketInternalRecentering, hybrid, shifted]
  let baseAt : forall tau, tau ∈ segment Real anchor hybrid ->
      UniformCompactTimeSource d ((q + 1) + 1) source.carrier :=
    fun tau htau => C.sourceCLM tau (hsegment htau)
      (mem_strictPositive_of_mem_packetCenter_segment hanchor hhybrid htau)
      scale chi
  have hinternal := anchoredAtlasField_internalRecenter_eq_of_radial_segment
    source I anchor hybrid hanchor hhybrid (by simp [hybrid]) scale chi
    baseAt (by intro tau htau hpos; rfl) lgc z (by
      rw [hrec]
      exact rankedMixedTail_shiftSegment_subset_openZeroConvexKernel
        A.spatialLinearDomain_open source.zero_mem_spatialLinearDomain
        hcover hz hepsilon.le)
  have hhead := anchoredAtlasField_headShift_eq_complex
    source I hybrid shifted hhybrid hpositive (half_pos hepsilon)
    (by simp [hybrid, shifted])
    (by intro j; simp [hybrid])
    (C.sourceCLM hybrid hhybridCenters hhybrid scale chi)
    (C.sourceCLM shifted hshifted hpositive scale chi)
    scale chi rfl rfl lgc z hradial
  apply hhead.trans
  apply congrArg (osiiOriginalOSHilbertComplex OS
    ((epsilon / 2 : Real) : Complex))
  have hshift : z + (fun _ : Fin (q + 1) => (epsilon : Complex)) =
      osiiVI2Shift (q + 1) epsilon z := by
    rfl
  simpa only [baseAt, hrec, hshift, source,
    compactCenterReflectedGramSpatialSourceData,
    StageWideStrictGeneratedMixedReflectedGramRankData.toAtlasFamily] using hinternal

set_option maxHeartbeats 2000000 in
/-- The damped Gram scalar is the literal reflected product of the completely
shifted sources. The two tests and packet scales are independent. -/
theorem compactCenterReflectedGram_completeShift_inner_eq_scalar
    {C0 : Type*} [CanonicalGeneratorStageLevelProvider OS C0]
    {S0 : C0} {depth rank : Nat}
    {I : Section43ProductTimeApproximateIdentity ((q + 1) + 1)}
    {centers : Set (Fin ((q + 1) + 1) -> Real)}
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S0 depth rank)
    (C : I.CompactCenterFamilyTimeCarrierData centers)
    (anchor : Fin ((q + 1) + 1) -> Real)
    (hanchor : anchor ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hsegment : segment Real anchor
      (chronologicalPacketInternalCenter anchor
        (equation621ShiftedSourceCenter epsilon anchor)) ⊆ centers)
    (hshifted : equation621ShiftedSourceCenter epsilon anchor ∈ centers)
    (lgc : OSLinearGrowthCondition d OS)
    (leftScale rightScale : Nat)
    (left right : SchwartzMap (Section43SpatialSpace d ((q + 1) + 1)) Complex)
    (z : Fin (q + 1) -> Complex)
    (hz : z ∈ osiiMixedTailArgumentCarrier
      (osiiStrictGeneratedMixedLogarithmicBaseAtRank
        ((q + 1) + 1) depth rank)) :
    let shifted := equation621ShiftedSourceCenter epsilon anchor
    let hpositive := equation621ShiftedSourceCenter_positive hepsilon.le hanchor
    let ha := hsegment (left_mem_segment Real _ _)
    let A := (P.forCarrier q C.carrier C.carrier_compact C.carrier_positive).atlas
    let field := A.gram.anchoredAtlasField A.sourceStage.stage A.sourceStage.germ
    @inner Complex (OSHilbertSpace OS) _
        (field (C.sourceCLM anchor ha hanchor leftScale left)
          (osiiVI2Shift (q + 1) epsilon z))
        (osiiOriginalOSHilbertComplex OS (epsilon : Complex)
          (field (C.sourceCLM anchor ha hanchor rightScale right)
            (osiiVI2Shift (q + 1) epsilon z))) =
      reflectedMovingSliceScalar A.sourceStage.stage A.sourceStage.germ.η
        (diffVarReduction d ((q + 1) + ((q + 1) + 1))
          (mixedReflectedChronologicalSource
            (I.translatedPositiveTimeSpatialSource shifted hpositive left leftScale).1
            (I.translatedPositiveTimeSpatialSource shifted hpositive right rightScale).1))
        (reflectedCauchyCenter z) := by
  dsimp only
  let shifted := equation621ShiftedSourceCenter epsilon anchor
  have hpositive : shifted ∈
      section43TimeStrictPositiveRegion ((q + 1) + 1) :=
    equation621ShiftedSourceCenter_positive hepsilon.le hanchor
  let source := compactCenterReflectedGramSpatialSourceData
    P.toAtlasFamily C shifted hshifted hpositive
  let A := source.reflectedGram.atlas
  let field := A.gram.anchoredAtlasField A.sourceStage.stage A.sourceStage.germ
  let ha := hsegment (left_mem_segment Real _ _)
  let leftBase := C.sourceCLM anchor ha hanchor leftScale left
  let rightBase := C.sourceCLM anchor ha hanchor rightScale right
  let shiftedLeft := C.sourceCLM shifted hshifted hpositive leftScale left
  let shiftedRight := C.sourceCLM shifted hshifted hpositive rightScale right
  have hleft : field shiftedLeft z =
      osiiOriginalOSHilbertComplex OS ((epsilon / 2 : Real) : Complex)
        (field leftBase (osiiVI2Shift (q + 1) epsilon z)) :=
    compactCenterReflectedGram_completeShift_field_eq
      P C anchor hanchor hepsilon hsegment hshifted lgc leftScale left z hz
  have hright : field shiftedRight z =
      osiiOriginalOSHilbertComplex OS ((epsilon / 2 : Real) : Complex)
        (field rightBase (osiiVI2Shift (q + 1) epsilon z)) :=
    compactCenterReflectedGram_completeShift_field_eq
      P C anchor hanchor hepsilon hsegment hshifted lgc rightScale right z hz
  have hcovered : z ∈ A.gram.anchoredAtlasCoveredDomain
      A.sourceStage.stage A.sourceStage.germ :=
    ((P.forCarrier q C.carrier C.carrier_compact C.carrier_positive
      ).coversStrictGeneratedAtRank hz).1
  have hgram := A.gram.anchoredAtlas_scalar_reflectedCauchyCenter_eq_inner
    A.sourceStage.stage A.sourceStage.germ shiftedLeft shiftedRight z hcovered
  rw [A.gram.cauchy_scalar shiftedLeft shiftedRight] at hgram
  exact (osiiOriginalOSHilbertComplex_inner_halfShift_self OS hepsilon
    (field leftBase (osiiVI2Shift (q + 1) epsilon z))
    (field rightBase (osiiVI2Shift (q + 1) epsilon z))).symm.trans
      ((congrArg₂ (fun x y : OSHilbertSpace OS =>
          @inner Complex (OSHilbertSpace OS) _ x y)
        hleft.symm hright.symm).trans hgram.symm)

set_option maxHeartbeats 2000000 in
/-- Coherent packet limits identify the prescribed-shift Gram form with the
actual stage distribution. The cutoff plateau is derived from the source
family, and no uniform bound on absolute Hermite-mode energies is used. -/
theorem tendsto_compactCenterReflectedGram_completeShift_inner
    {C0 : Type*} [CanonicalGeneratorStageLevelProvider OS C0]
    {S0 : C0} {depth rank : Nat}
    {I : Section43ProductTimeApproximateIdentity ((q + 1) + 1)}
    {centers : Set (Fin ((q + 1) + 1) -> Real)}
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S0 depth rank)
    (C : I.CompactCenterFamilyTimeCarrierData centers)
    (anchor : Fin ((q + 1) + 1) -> Real)
    (hanchor : anchor ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hsegment : segment Real anchor
      (chronologicalPacketInternalCenter anchor
        (equation621ShiftedSourceCenter epsilon anchor)) ⊆ centers)
    (hshifted : equation621ShiftedSourceCenter epsilon anchor ∈ centers)
    (lgc : OSLinearGrowthCondition d OS)
    (left right : SchwartzMap (Section43SpatialSpace d ((q + 1) + 1)) Complex)
    (z : Fin (q + 1) -> Complex)
    (hz : z ∈ osiiMixedTailArgumentCarrier
      (osiiStrictGeneratedMixedLogarithmicBaseAtRank
        ((q + 1) + 1) depth rank))
    (leftTail rightTail : Nat) :
    let ha := hsegment (left_mem_segment Real _ _)
    let A := (P.forCarrier q C.carrier C.carrier_compact C.carrier_positive).atlas
    let field := A.gram.anchoredAtlasField A.sourceStage.stage A.sourceStage.germ
    Tendsto (fun N => @inner Complex (OSHilbertSpace OS) _
        (field (C.sourceCLM anchor ha hanchor (N + leftTail) left)
          (osiiVI2Shift (q + 1) epsilon z))
        (osiiOriginalOSHilbertComplex OS (epsilon : Complex)
          (field (C.sourceCLM anchor ha hanchor (N + rightTail) right)
            (osiiVI2Shift (q + 1) epsilon z)))) atTop
      (nhds ((CanonicalGeneratorStageLevelProvider.stage (OS := OS) S0
          ((q + 1) + ((q + 1) + 1))).distribution
        (osiiVI2Shift ((q + 1) + ((q + 1) + 1)) epsilon
          (reflectedCauchyShiftedStagePoint
            (reflectedChronologicalGapMap (q + 1) (anchor, anchor)) z))
        (osiiMixedSpatialHeadMarginal left right))) := by
  dsimp only
  let shifted := equation621ShiftedSourceCenter epsilon anchor
  have hpositive : shifted ∈
      section43TimeStrictPositiveRegion ((q + 1) + 1) :=
    equation621ShiftedSourceCenter_positive hepsilon.le hanchor
  let source := compactCenterReflectedGramSpatialSourceData
    P.toAtlasFamily C shifted hshifted hpositive
  let A := source.reflectedGram.atlas
  have hzA : z ∈ A.spatialLinearDomain :=
    (P.forCarrier q C.carrier C.carrier_compact C.carrier_positive
      ).coversStrictGeneratedAtRank hz
  have hcutoff := source.cutoff_eq_one_at_translatedSourceAnchor
    I shifted hpositive (by intro scale chi; rfl)
  have hlimit :=
    tendsto_reflectedMovingSliceScalar_tailDiagonal_to_distribution_of_cutoff_eq_one
      A.sourceStage.stage A.sourceStage.germ.η I I shifted shifted
      hpositive hpositive left right (reflectedCauchyCenter z) hzA.2.2
      (osiiMixedBlockGlobalReducedTime (q + 1) (Fin.append shifted shifted))
      rfl hcutoff leftTail rightTail
  have hpoint : equation621ReflectedMovingSlicePoint
      (reflectedCauchyCenter z)
      (osiiMixedBlockGlobalReducedTime (q + 1) (Fin.append shifted shifted)) =
        osiiVI2Shift ((q + 1) + ((q + 1) + 1)) epsilon
          (reflectedCauchyShiftedStagePoint
            (reflectedChronologicalGapMap (q + 1) (anchor, anchor)) z) := by
    rw [equation621ReflectedMovingSlicePoint_reflectedCauchyCenter,
      osiiMixedBlockGlobalReducedTime_append_eq_reflectedChronologicalGapMap]
    exact reflectedCauchyShiftedStagePoint_equation621ShiftedSourceCenter
      epsilon anchor anchor z
  rw [hpoint] at hlimit
  have hstage : A.sourceStage.stage =
      CanonicalGeneratorStageLevelProvider.stage (OS := OS) S0
        ((q + 1) + ((q + 1) + 1)) :=
    source.sourceStage_eq_currentReflectedStage
  rw [← hstage]
  apply (tendsto_congr' (Filter.Eventually.of_forall fun N =>
    compactCenterReflectedGram_completeShift_inner_eq_scalar
      P C anchor hanchor hepsilon hsegment hshifted lgc
      (N + leftTail) (N + rightTail) left right z hz)).2
  exact hlimit

set_option maxHeartbeats 3000000 in
/-- A stored source atlas has the same prescribed-shift packet limit as the
actual predecessor stage, even when their stage providers differ. The larger
compact carrier and all shifted source representatives are constructed here. -/
theorem ReflectedGramSpatialSourceData.tendsto_prescribedShift_inner
    {Csource Crank : Type*}
    [CanonicalGeneratorStageLevelProvider OS Csource]
    [CanonicalGeneratorStageLevelProvider OS Crank]
    {Ssource : Csource} {Srank : Crank} {depth rank : Nat}
    (source : ReflectedGramSpatialSourceData (OS := OS) Ssource q)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) Srank depth rank)
    (I : Section43ProductTimeApproximateIdentity ((q + 1) + 1))
    (anchor : Fin ((q + 1) + 1) -> Real)
    (hanchor : anchor ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hsource : forall scale chi,
      UniformCompactTimeSource.source (source.sourceCLM scale chi) =
        I.translatedPositiveTimeSpatialSource anchor hanchor chi scale)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (lgc : OSLinearGrowthCondition d OS)
    (left right : SchwartzMap (Section43SpatialSpace d ((q + 1) + 1)) Complex)
    (z : Fin (q + 1) -> Complex)
    (hz : z ∈ osiiMixedTailArgumentCarrier
      (osiiStrictGeneratedMixedLogarithmicBaseAtRank
        ((q + 1) + 1) depth rank))
    (hsourceDomain : osiiVI2Shift (q + 1) epsilon z ∈
      openZeroConvexKernel source.reflectedGram.atlas.spatialLinearDomain)
    (leftTail rightTail : Nat) :
    let A := source.reflectedGram.atlas
    let field := A.gram.anchoredAtlasField A.sourceStage.stage A.sourceStage.germ
    Tendsto (fun N => @inner Complex (OSHilbertSpace OS) _
        (field (source.sourceCLM (N + leftTail) left)
          (osiiVI2Shift (q + 1) epsilon z))
        (osiiOriginalOSHilbertComplex OS (epsilon : Complex)
          (field (source.sourceCLM (N + rightTail) right)
            (osiiVI2Shift (q + 1) epsilon z)))) atTop
      (nhds ((CanonicalGeneratorStageLevelProvider.stage (OS := OS) Srank
          ((q + 1) + ((q + 1) + 1))).distribution
        (osiiVI2Shift ((q + 1) + ((q + 1) + 1)) epsilon
          (reflectedCauchyShiftedStagePoint
            (reflectedChronologicalGapMap (q + 1) (anchor, anchor)) z))
        (osiiMixedSpatialHeadMarginal left right))) := by
  dsimp only
  let centers := equation621PrescribedShiftCenters source.carrier anchor epsilon
  let C : I.CompactCenterFamilyTimeCarrierData centers :=
    Classical.choice (exists_equation621PrescribedShiftCarrier I
      source.carrier_compact source.carrier_positive hanchor hepsilon.le)
  have hsegment : segment Real anchor
      (chronologicalPacketInternalCenter anchor
        (equation621ShiftedSourceCenter epsilon anchor)) ⊆ centers :=
    fun _ h => Or.inl (Or.inr h)
  have hshifted : equation621ShiftedSourceCenter epsilon anchor ∈ centers :=
    Or.inr rfl
  have ha : anchor ∈ centers := hsegment (left_mem_segment Real _ _)
  have hcarrier : source.carrier ⊆ C.carrier := by
    intro tau htau
    exact C.centers_subset_carrier (Or.inl (Or.inl htau))
  let A := source.reflectedGram.atlas
  let B := (P.forCarrier q C.carrier C.carrier_compact C.carrier_positive).atlas
  let fieldA := A.gram.anchoredAtlasField A.sourceStage.stage A.sourceStage.germ
  let fieldB := B.gram.anchoredAtlasField B.sourceStage.stage B.sourceStage.germ
  let w := osiiVI2Shift (q + 1) epsilon z
  have hzeroB : (0 : Fin (q + 1) -> Complex) ∈ B.spatialLinearDomain :=
    B.initialGramPolydisc_subset_spatialLinearDomain
      (SCV.center_mem_polydisc fun _ => B.gram.gramRadius_pos)
  have hwB : w ∈ openZeroConvexKernel B.spatialLinearDomain :=
    rankedMixedTail_mem_openZeroConvexKernel B.spatialLinearDomain_open hzeroB
      (P.forCarrier q C.carrier C.carrier_compact C.carrier_positive
        ).coversStrictGeneratedAtRank
      (StrictGeneratedScalarDepthPointedData.osiiVI2Shift_mem_mixedTailArgumentCarrier
        hz hepsilon.le)
  have hwCommon : w ∈ openZeroConvexKernel
      (A.spatialLinearDomain ∩ B.spatialLinearDomain) := by
    rw [openZeroConvexKernel_inter]
    exact ⟨hsourceDomain, hwB⟩
  have hfield (scale : Nat)
      (chi : SchwartzMap (Section43SpatialSpace d ((q + 1) + 1)) Complex) :
      fieldB (C.sourceCLM anchor ha hanchor scale chi) w =
        fieldA (source.sourceCLM scale chi) w := by
    have hbase : uniformCompactTimeSourceMonoCLM hcarrier
        (source.sourceCLM scale chi) =
          C.sourceCLM anchor ha hanchor scale chi := by
      apply Subtype.ext
      exact hsource scale chi
    have h :=
      _root_.OSReconstruction.FixedAxisSplitUniformRankFieldData.ofCarrier_field_eq_reflectedGram_source_acrossProviders_on_openZeroConvexKernel_inter_domain
        source P C.carrier_compact C.carrier_positive hcarrier
        (source.sourceCLM scale chi) w hwCommon
    exact (congrArg (fun base => fieldB base w) hbase).symm.trans h
  have hlimit := tendsto_compactCenterReflectedGram_completeShift_inner
    P C anchor hanchor hepsilon hsegment hshifted lgc left right z hz
    leftTail rightTail
  apply (tendsto_congr' (Filter.Eventually.of_forall fun N => ?_)).2 hlimit
  exact congrArg₂ (fun x y : OSHilbertSpace OS =>
      @inner Complex (OSHilbertSpace OS) _ x y)
    (hfield (N + leftTail) left).symm
    (congrArg (osiiOriginalOSHilbertComplex OS (epsilon : Complex))
      (hfield (N + rightTail) right).symm)

/-- The same source limit in the current field parameter, with the reflected
spatial marginal kept as the actual coherent product probe. -/
theorem ReflectedGramSpatialSourceData.tendsto_dampedDiagonal_marginalSpatialProbe
    {Csource Crank : Type*}
    [CanonicalGeneratorStageLevelProvider OS Csource]
    [CanonicalGeneratorStageLevelProvider OS Crank]
    {Ssource : Csource} {Srank : Crank} {depth rank : Nat}
    (source : ReflectedGramSpatialSourceData (OS := OS) Ssource q)
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) Srank depth rank)
    (I : Section43ProductTimeApproximateIdentity ((q + 1) + 1))
    (anchor : Fin ((q + 1) + 1) -> Real)
    (hanchor : anchor ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hsource : forall scale chi,
      UniformCompactTimeSource.source (source.sourceCLM scale chi) =
        I.translatedPositiveTimeSpatialSource anchor hanchor chi scale)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (lgc : OSLinearGrowthCondition d OS)
    (spatialApprox : Section43ProductTimeApproximateIdentity
      (((q + 1) + 1) * d))
    (spatialCenter : Fin (((q + 1) + 1) * d) -> Real)
    (probeScale : Nat) (z : Fin (q + 1) -> Complex)
    (hz : osiiVI2Unshift (q + 1) epsilon z ∈ osiiMixedTailArgumentCarrier
      (osiiStrictGeneratedMixedLogarithmicBaseAtRank
        ((q + 1) + 1) depth rank))
    (hsourceDomain : z ∈
      openZeroConvexKernel source.reflectedGram.atlas.spatialLinearDomain)
    (leftTail rightTail : Nat) :
    let A := source.reflectedGram.atlas
    let field := A.gram.anchoredAtlasField A.sourceStage.stage A.sourceStage.germ
    let test := spatialApprox.toEquation621SpatialApproxIdentity.section43Probe
      spatialCenter probeScale
    Tendsto (fun N => @inner Complex (OSHilbertSpace OS) _
        (field (source.sourceCLM (N + leftTail) test) z)
        (osiiOriginalOSHilbertComplex OS (epsilon : Complex)
          (field (source.sourceCLM (N + rightTail) test) z))) atTop
      (nhds ((CanonicalGeneratorStageLevelProvider.stage (OS := OS) Srank
          ((q + 1) + ((q + 1) + 1))).distribution
        (equation621DampedReflectedStagePoint epsilon
          (reflectedChronologicalGapMap (q + 1) (anchor, anchor)) z)
        (spatialApprox.reflectedSelfPairMarginalSpatialApproxIdentity.section43Probe
          (reflectedSelfPairMarginalSpatialPoint d (q + 1) spatialCenter)
          probeScale))) := by
  dsimp only
  rw [spatialApprox.reflectedSelfPairMarginal_section43Probe_eq_mixedSpatialHeadMarginal]
  simpa only [osiiVI2Shift_unshift, equation621DampedReflectedStagePoint]
    using source.tendsto_prescribedShift_inner P I anchor hanchor hsource
      hepsilon lgc
      (spatialApprox.toEquation621SpatialApproxIdentity.section43Probe
        spatialCenter probeScale)
      (spatialApprox.toEquation621SpatialApproxIdentity.section43Probe
        spatialCenter probeScale)
      (osiiVI2Unshift (q + 1) epsilon z) hz
      (by simpa using hsourceDomain) leftTail rightTail

end OSIIChapterV
end OSReconstruction
