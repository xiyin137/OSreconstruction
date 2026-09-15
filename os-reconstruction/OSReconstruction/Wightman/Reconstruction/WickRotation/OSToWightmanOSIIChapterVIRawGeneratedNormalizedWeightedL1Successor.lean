import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621PrescribedShiftAllSplits
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRawGeneratedWeightedL1GeneratorSeeds
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRawGeneratedNormalizedWeightedL1UnitHubAllDepthHandoff

/-!
# The complete-normalized raw VI.2 successor

Choose the rooted anchor before the prescribed positive shift. Its reflected
source unshifts then return to the same raw predecessor. The actual all-split
estimate and scalar coefficient convexification retain one coefficient and
exactly one outer-depth increment.
-/

noncomputable section

open Complex Set Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

open StrictGeneratedScalarDepthPointedData
open StrictGeneratedScalarDepthPointedData.RecursiveSectorAdaptiveZeroBetaSelectedVI2GramChartPackageData
open Section43ProductTimeApproximateIdentity
open Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData

private theorem equation621RootedLeftCenter_shift_unshift
    {k : Nat} (i : GeneratorIndex k) (anchor : Fin k -> Real)
    (epsilon : Real) (z : OSIITimeGapSpace k) :
    osiiVI2Unshift (i.n - 1) epsilon
        (equation621RootedLeftCenter i anchor (osiiVI2Shift k epsilon z)) =
      equation621RootedLeftCenter i anchor z := by
  ext j
  simp [osiiVI2Unshift, osiiVI2Shift, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm]

private theorem equation621RootedRightCenter_shift_unshift
    {k : Nat} (i : GeneratorIndex k) (anchor : Fin k -> Real)
    (epsilon : Real) (z : OSIITimeGapSpace k) :
    osiiVI2Unshift (i.m - 1) epsilon
        (equation621RootedRightCenter i anchor (osiiVI2Shift k epsilon z)) =
      equation621RootedRightCenter i anchor z := by
  ext j
  simp [osiiVI2Unshift, osiiVI2Shift, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm]

private def prescribedShiftAnchorData
    {k : Nat} {hub : Fin k -> Real} {z : OSIITimeGapSpace k}
    (C : TargetHubHalfAnchorData hub z)
    {epsilon : Real} (hepsilon : 0 <= epsilon) :
    TargetHubHalfAnchorData hub (osiiVI2Shift k epsilon z) where
  anchor := C.anchor
  anchor_positive := C.anchor_positive
  anchor_le_half_hub := C.anchor_le_half_hub
  anchor_le_half_target := by
    intro j
    change C.anchor j <= ((z j).re + epsilon) / 2
    linarith [C.anchor_le_half_target j]
  anchor_lt_hub := C.anchor_lt_hub
  anchor_lt_target := by
    intro j
    change C.anchor j < (z j).re + epsilon
    linarith [C.anchor_lt_target j]

variable {d : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

namespace StrictGeneratedScalarRankPointedInductionData

set_option maxHeartbeats 4000000 in
/-- A strictly contracted raw generator has the complete-normalized bound
at every prescribed positive shift, on the actual scalar rank successor. -/
theorem normalizedRawGeneratorPointBound_of_argumentBound
    {initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS}
    {lgc : OSLinearGrowthCondition d OS}
    {depth rank q t beta : Nat}
    (B : RawStrictGeneratedVI2NormalizedWeightedL1DepthBoundData
      initial lgc t beta depth)
    (R : StrictGeneratedScalarRankPointedInductionData OS depth rank)
    {x : Fin (q + 1) -> Real}
    (G : RawGeneratorRankSuccessorSeedData rank (q + 1) depth x)
    {rho : Real} (hrho_nonneg : 0 <= rho) (hrho_lt_one : rho < 1)
    (zeta : OSIITimeGapSpace (q + 1))
    (hzeta : zeta ∈ osiiTimeRightHalfPlane (q + 1))
    (hargument : forall j,
      |osiiTimeArgumentVector zeta j| <= rho * |x j|)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (spatialApprox : Section43ProductTimeApproximateIdentity
      (((q + 1) + 1) * d)) :
    OSIIEquation621WeightedL1PointBoundData
      ((((R.next lgc).pointed.stageLevel.stage (q + 1)
        ).vi2Equation621TotalNormalizedStage t epsilon).distribution zeta)
      ((q + 1) * t) B.alpha beta (depth + 1) := by
  let shifted := osiiVI2Shift (q + 1) epsilon zeta
  have hshifted : shifted ∈ osiiTimeRightHalfPlane (q + 1) := by
    intro j
    change 0 < (zeta j).re + epsilon
    exact add_pos (hzeta j) hepsilon
  have hshrink : forall j,
      |osiiTimeArgumentVector shifted j| <= |x j| := by
    intro j
    calc
      |osiiTimeArgumentVector shifted j| <=
          |osiiTimeArgumentVector zeta j| :=
        abs_arg_add_ofReal_le (hzeta j) hepsilon.le
      _ <= rho * |x j| := hargument j
      _ <= |x j| := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hrho_lt_one.le (abs_nonneg (x j))
  obtain ⟨P⟩ := nonempty_rawGeneratorCoordinatewiseShrinkData
    G.generator G.left G.left_rank G.left_raw G.theta G.theta_bound
    G.right G.right_rank G.right_raw (osiiTimeArgumentVector shifted)
      (by simpa [G.point_eq] using hshrink)
  let a : RootedStrictGeneratedTargetHubChartAtRank
      (q + 1) depth rank := {
    generator := G.generator
    left := P.centered.left
    left_rank := P.centered.left_rank
    theta := P.centered.theta
    angle_bound := P.centered.angle_bound
    right := P.centered.right
    right_rank := P.centered.right_rank
    target := shifted
    target_mem := ⟨hshifted, Set.mem_singleton_iff.mpr
      P.centered.point_eq.symm⟩ }
  let radial : Real := (rho + 1) / 2
  have hradial_pos : 0 < radial := by dsimp [radial]; linarith
  have hradial_lt_one : radial < 1 := by dsimp [radial]; linarith
  have hrho_radial : rho < radial := by dsimp [radial]; linarith
  let C := targetHubNormalizedRadialSlackAnchorData
    (R.pointed.hub q) (R.pointed.hub_positive q) zeta hzeta
    rho radial hrho_nonneg hradial_pos hrho_radial
  let H := Classical.choice
    (nonempty_positiveHubFloorData
      (R.pointed.hub q) (R.pointed.hub_positive q))
  obtain ⟨cap, hcap, _hcap_eq, hsource⟩ :=
    TargetHubNormalizedRadialSlackAnchorData.exists_equation621RawSourceCenters_of_argumentBound
      hradial_pos hradial_lt_one G.generator G.left G.left_rank G.left_raw
      G.theta G.theta_bound G.right G.right_rank G.right_raw hzeta
      (by simpa [G.point_eq] using hargument) C H
  have hcenters := hsource 0 (le_refl 0) hcap.le
  have hunshiftZero (m : Nat) (z : OSIITimeGapSpace m) :
      osiiVI2Unshift m 0 z = z := by
    ext j
    simp [osiiVI2Unshift]
  let C0 := prescribedShiftAnchorData C.anchorData hepsilon.le
  let Q := selectedAnchorLocalRootedReflectedGramRadialProducer
    R.pointed depth R.sourceReflectedGramRankData.toAtlasFamily lgc
      C0.anchor C0.anchor_positive
  obtain ⟨D⟩ :=
    nonempty_rootedRankSuccessorTargetHubAdaptedReflectedGramData_atRank
      R.pointed depth rank R.sourceReflectedGramRankData Q.packet Q.roots
      Q.holomorphic.toContinuousTranslationData a.generator
      (R.pointed.hub q) C0.anchor_le_hub a.target
      a.left a.left_rank a.right a.right_rank a.theta a.target_mem
  obtain ⟨E⟩ :=
    nonempty_rootedTargetHubPointedDirectExtensionData_of_rootedDataAtRank
      R.pointed depth rank R.sourceReflectedGramRankData lgc a.generator
      (R.pointed.hub q) (R.pointed.pointedAtlas q) a.target C0 Q D.current
  have hleft : osiiVI2Unshift (a.generator.n - 1) epsilon
      (equation621TargetLeftParameter a.generator
        (a.target - osiiPositiveRealTimeEmbed C0.anchor)) ∈
      osiiMixedTailArgumentCarrier
        (osiiRawStrictGeneratedMixedLogarithmicBase
          ((a.generator.n - 1) + 1) depth) := by
    change osiiVI2Unshift (G.generator.n - 1) epsilon
      (equation621RootedLeftCenter G.generator C.anchorData.anchor
        (osiiVI2Shift (q + 1) epsilon zeta)) ∈ _
    rw [equation621RootedLeftCenter_shift_unshift]
    simpa only [hunshiftZero, a] using hcenters.1
  have hright : osiiVI2Unshift (a.generator.m - 1) epsilon
      (equation621TargetRightParameter a.generator
        (a.target - osiiPositiveRealTimeEmbed C0.anchor)) ∈
      osiiMixedTailArgumentCarrier
        (osiiRawStrictGeneratedMixedLogarithmicBase
          ((a.generator.m - 1) + 1) depth) := by
    change osiiVI2Unshift (G.generator.m - 1) epsilon
      (equation621RootedRightCenter G.generator C.anchorData.anchor
        (osiiVI2Shift (q + 1) epsilon zeta)) ∈ _
    rw [equation621RootedRightCenter_shift_unshift]
    simpa only [hunshiftZero, a] using hcenters.2
  have hbridge : epsilon <
      ((a.target - osiiPositiveRealTimeEmbed C0.anchor)
        a.generator.bridgeGlobalIndex).re := by
    change epsilon <
      (zeta G.generator.bridgeGlobalIndex).re + epsilon -
        C.anchorData.anchor G.generator.bridgeGlobalIndex
    linarith [C.anchorData.anchor_lt_target G.generator.bridgeGlobalIndex]
  refine { alpha_nonneg := B.alpha_nonneg, norm_distribution_le := ?_ }
  intro chi
  have hlocal := norm_equation621Normalized_le_of_distribution_le_denormalization
    E.current.extension.toTimeContinuationStage hepsilon hshifted chi
      (osiiVI2ArityDepthMajorant B.alpha beta (q + 1) (depth + 1) *
        osiiSpatialPolynomialWeightedL1 ((q + 1) * t)
          (section43SpatialFlatSchwartzCLE d (q + 1) chi))
      (norm_current_allSplits_le_of_rawPredecessor_prescribedShift
        E B spatialApprox a.target E.current.target_mem_carrier hepsilon
        C0.centeredTarget_mem_rightHalfPlane hbridge hleft hright chi)
  have hnext := norm_normalizedRankSuccessor_le_of_rootedExtension
    R lgc a E.current epsilon chi _ hlocal
  rw [OSIITimeContinuationStage.vi2Equation621TotalNormalizedStage_eq_of_pos
    _ (by omega : 0 < q + 1)]
  simpa only [a, shifted, osiiVI2Unshift_shift] using hnext

end StrictGeneratedScalarRankPointedInductionData

namespace RawStrictGeneratedVI2NormalizedWeightedL1DepthBoundData

set_option maxHeartbeats 4000000 in
/-- The prescribed-shift generator estimate agrees with the completed next
outer-depth stage at the same physical point. -/
theorem generatorPointBound_of_argumentBound
    {initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS}
    {lgc : OSLinearGrowthCondition d OS}
    {depth rank q t beta : Nat}
    (B : RawStrictGeneratedVI2NormalizedWeightedL1DepthBoundData
      initial lgc t beta depth)
    {x : Fin (q + 1) -> Real}
    (G : RawGeneratorRankSuccessorSeedData rank (q + 1) depth x)
    {rho : Real} (hrho_nonneg : 0 <= rho) (hrho_lt_one : rho < 1)
    (zeta : OSIITimeGapSpace (q + 1))
    (hzeta : zeta ∈ osiiTimeRightHalfPlane (q + 1))
    (hargument : forall j,
      |osiiTimeArgumentVector zeta j| <= rho * |x j|)
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (spatialApprox : Section43ProductTimeApproximateIdentity
      (((q + 1) + 1) * d)) :
    OSIIEquation621WeightedL1PointBoundData
      ((((initial.toStrictGeneratedTimeContinuationLadder lgc (q + 1)).stage
        (depth + 1)).vi2Equation621TotalNormalizedStage
          t epsilon).distribution zeta)
      ((q + 1) * t) B.alpha beta (depth + 1) := by
  let D0 := initial.toStrictGeneratedScalarDepthZeroPointedData
  let R := (D0.depthInduction lgc depth).recursiveSectorRankInduction lgc rank
  have hbound := R.normalizedRawGeneratorPointBound_of_argumentBound
    B G hrho_nonneg hrho_lt_one zeta hzeta hargument hepsilon spatialApprox
  have hargumentRank : osiiTimeArgumentVector zeta ∈
      osiiStrictGeneratedLogarithmicBaseAtRank
        (q + 1) (depth + 1) (rank + 1) := by
    apply OSIIStrictGeneratedLogarithmicArgumentAtRank.scalar_hyperrectangle
      G.toIsGeneratorRankSuccessorSeed.toRankSuccessorSeed.toRankSucc
    intro j
    exact (hargument j).trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hrho_lt_one.le (abs_nonneg (x j)))
  have hshiftedRank := osiiVI2Shift_mem_timeArgumentCarrier_of_coordinatewiseSolid
    (strictGeneratedScalarBaseAtRank_isCoordinatewiseSolid
      (q + 1) (depth + 1) (rank + 1)) hepsilon.le
    ⟨hzeta, hargumentRank⟩
  have hnext := (R.next lgc).targetRankCarrier_subset (q + 1) hshiftedRank
  have hcanonical : osiiVI2Shift (q + 1) epsilon zeta ∈
      ((CanonicalGeneratorStageLevelProvider.toSimultaneousTimeContinuationStageLevel
        (OS := OS)
        (((D0.depthInduction lgc depth).recursiveSectorRankInduction
          lgc (rank + 1)).pointed)).stage (q + 1)).carrier := by
    change osiiVI2Shift (q + 1) epsilon zeta ∈
      ((((D0.depthInduction lgc depth).recursiveSectorRankInduction
        lgc (rank + 1)).pointed).stageLevel.stage (q + 1)).carrier
    exact hnext
  have hnextDepth := D0.recursiveSectorRankInduction_distribution_eq_nextDepth
    lgc depth (rank + 1) (q + 1) hcanonical
  have hraw :
      (((initial.toStrictGeneratedTimeContinuationLadder lgc (q + 1)).stage
        (depth + 1)).distribution (osiiVI2Shift (q + 1) epsilon zeta)) =
      ((R.next lgc).pointed.stageLevel.stage (q + 1)).distribution
        (osiiVI2Shift (q + 1) epsilon zeta) := by
    change (((((D0.depthInduction lgc depth).recursiveSectorRankInduction
      lgc (rank + 1)).pointed).stageLevel.stage (q + 1)).distribution
        (osiiVI2Shift (q + 1) epsilon zeta)) = _ at hnextDepth
    simpa [R, D0,
      StrictGeneratedScalarDepthPointedData.recursiveSectorRankInduction,
      InitialGeneratedLogarithmicStageLevelData.toStrictGeneratedTimeContinuationLadder,
      StrictGeneratedScalarDepthPointedData.toTimeContinuationLadder,
      timeContinuationLadderOfAngleSectorCover] using hnextDepth.symm
  apply hbound.congr
  ext chi
  simp only [OSIITimeContinuationStage.vi2Equation621TotalNormalizedStage_eq_of_pos
      _ (by omega : 0 < q + 1),
    OSIITimeContinuationStage.vi2Equation621NormalizedStage_distribution_apply,
    hraw]

/-- Every arm of a finite raw-generator coefficient cross has the same
complete-normalized successor bound, for the prescribed shift itself. -/
theorem generatorFlatWindowPointBound
    {initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS}
    {lgc : OSLinearGrowthCondition d OS}
    {depth rank q t beta n : Nat} [NeZero n]
    (B : RawStrictGeneratedVI2NormalizedWeightedL1DepthBoundData
      initial lgc t beta depth)
    (spatialApprox : Section43ProductTimeApproximateIdentity
      (((q + 1) + 1) * d))
    (seed : Fin n -> Fin (q + 1) -> Real)
    (hseedRaw : forall active,
      Nonempty (RawGeneratorRankSuccessorSeedData
        rank (q + 1) depth (seed active)))
    {radius rho : Real} (hrho : rho < 1)
    (r : Fin n -> Complex)
    (hr : r ∈ osiiStrictScalarSeedCoefficientFlatWindow (Fin n) radius rho)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    OSIIEquation621WeightedL1PointBoundData
      ((((initial.toStrictGeneratedTimeContinuationLadder lgc (q + 1)).stage
        (depth + 1)).vi2Equation621TotalNormalizedStage t epsilon).distribution
          (osiiLogExp (osiiStrictScalarSeedCoefficientMap seed r)))
      ((q + 1) * t) B.alpha beta (depth + 1) := by
  obtain ⟨active, hactive, hzero⟩ := hr.2
  let G := Classical.choice (hseedRaw active)
  have himaginary := osiiStrictScalarSeedCoefficientMap_im_isGeneratorRankSuccessorSeed
    seed r active ⟨hactive, hzero⟩ hrho G.toIsGeneratorRankSuccessorSeed
  have hstrip := himaginary.toRankSuccessorSeed.toRankSucc.toStrictGenerated
    |>.coordinate_abs_lt_pi_div_two
  apply B.generatorPointBound_of_argumentBound G
    ((abs_nonneg _).trans hactive) hrho
    (osiiLogExp (osiiStrictScalarSeedCoefficientMap seed r))
    (osiiLogExp_mem_rightHalfPlane hstrip) ?_ hepsilon spatialApprox
  intro j
  rw [osiiTimeArgumentVector_logExp hstrip,
    osiiStrictScalarSeedCoefficientMap_im_eq_active seed r active hzero]
  change |(r active).im * seed active j| <= rho * |seed active j|
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right hactive (abs_nonneg _)

end RawStrictGeneratedVI2NormalizedWeightedL1DepthBoundData

private theorem normalizedDepth_logarithmicRankTube_subset
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) (t depth rank : Nat)
    {epsilon : Real} (hepsilon : 0 <= epsilon) (arity : Nat) :
    osiiLogarithmicTube
        (osiiStrictGeneratedLogarithmicBaseAtRank arity depth rank) ⊆
      (logarithmicPullbackStage
        (((initial.toStrictGeneratedTimeContinuationLadder lgc arity).stage depth
          ).vi2Equation621TotalNormalizedStage t epsilon)).carrier := by
  let D0 := initial.toStrictGeneratedScalarDepthZeroPointedData
  have h := logarithmicRankTube_subset_vi2Equation621TotalNormalizedPullback
    (D0.depthInduction lgc depth).pointed.stageLevel t depth rank hepsilon
    (fun arity w hw =>
      (D0.depthInduction lgc depth).strictGeneratedCarrier_subset arity
        ⟨hw.1, hw.2.toStrictGenerated⟩) arity
  simpa [D0,
    InitialGeneratedLogarithmicStageLevelData.toStrictGeneratedTimeContinuationLadder,
    StrictGeneratedScalarDepthPointedData.toTimeContinuationLadder,
    timeContinuationLadderOfAngleSectorCover] using h

private theorem normalizedRawNextDepth_flatCoefficientTube_subset
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS)
    {depth rank q t n : Nat} [NeZero n]
    (seed : Fin n -> Fin (q + 1) -> Real)
    (hseedRaw : forall active,
      Nonempty (RawGeneratorRankSuccessorSeedData
        rank (q + 1) depth (seed active)))
    {epsilon : Real} (hepsilon : 0 <= epsilon) :
    SCV.horizontalTube (fintypeFlatImaginaryUnion (Fin n) 1) ⊆
      osiiStrictScalarSeedCoefficientCarrier
        (((initial.toStrictGeneratedTimeContinuationLadder lgc (q + 1)).stage
          (depth + 1)).vi2Equation621TotalNormalizedStage t epsilon) seed := by
  intro r hr
  have hseed := osiiStrictScalarSeedCoefficientMap_mem_rankSuccessorSeedTube_of_mem_flat
    (fun active => (Classical.choice (hseedRaw active)
      ).toIsGeneratorRankSuccessorSeed.toRankSuccessorSeed) hr
  apply normalizedDepth_logarithmicRankTube_subset
    initial lgc t (depth + 1) (rank + 1) hepsilon (q + 1)
  rw [osiiLogarithmicTube, physicalLogarithmicBase_strictGeneratedAtRank_eq]
  exact hseed.1.toRankSucc

namespace RawStrictGeneratedVI2NormalizedWeightedL1DepthBoundData

set_option maxHeartbeats 4000000 in
/-- A raw generator presentation gives a bounded logarithmic coefficient
chart for the actual normalized next-depth stage. -/
theorem nonempty_nextDepthLogarithmicChart
    {initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS}
    {lgc : OSLinearGrowthCondition d OS}
    {depth rank q t beta : Nat}
    (B : RawStrictGeneratedVI2NormalizedWeightedL1DepthBoundData
      initial lgc t beta depth)
    (spatialApprox : Section43ProductTimeApproximateIdentity
      (((q + 1) + 1) * d))
    (z : Fin (q + 1) -> Complex)
    (S : RawRankedGeneratorSectionPresentationData
      rank (q + 1) depth (fun j => (z j).im))
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    Nonempty (WeightedL1ZeroPointedAmbientChartData
      (((initial.toStrictGeneratedTimeContinuationLadder lgc (q + 1)).stage
        (depth + 1)).vi2Equation621TotalNormalizedStage t epsilon)
      z ((q + 1) * t) B.alpha beta (depth + 1)) := by
  letI : NeZero S.seedCount := ⟨Nat.ne_of_gt S.seedCount_pos⟩
  let total : Real := ∑ i, S.weight i
  let rho : Real := (total + 1) / 2
  have htotal_nonneg : 0 <= total :=
    Finset.sum_nonneg fun i _ => S.weight_nonneg i
  have htotal_rho : total < rho := by
    dsimp [rho, total]
    linarith [S.weight_sum_lt_one]
  have hrho_pos : 0 < rho := by dsimp [rho]; linarith
  have hrho_lt_one : rho < 1 := by
    dsimp [rho, total]
    linarith [S.weight_sum_lt_one]
  obtain ⟨r0, htarget, hr0_budget, hregular⟩ :
      exists r0 : Fin S.seedCount -> Complex,
        osiiStrictScalarSeedCoefficientCLM S.seed r0 = z ∧
        (∑ i, |(r0 i).im|) <= total ∧
        (r0 = 0 ∨ osiiStrictScalarSeedCoefficientMap S.seed r0 ≠ 0) := by
    by_cases hz : z = 0
    · refine ⟨0, ?_, ?_, Or.inl rfl⟩
      · exact (osiiStrictScalarSeedCoefficientCLM S.seed).map_zero.trans hz.symm
      · simpa using htotal_nonneg
    obtain ⟨v, hv⟩ := exists_real_strictScalarSeedCoefficient_preimage
      S.seed S.coefficient_surjective (fun j => (z j).re)
    let r0 : Fin S.seedCount -> Complex :=
      fun i => (v i : Complex) + (S.weight i : Complex) * I
    have htarget : osiiStrictScalarSeedCoefficientCLM S.seed r0 = z := by
      rw [osiiStrictScalarSeedCoefficientCLM_apply]
      funext j
      apply Complex.ext
      · have hj := congrArg Complex.re (congrFun hv j)
        simpa [osiiStrictScalarSeedCoefficientMap, r0] using hj
      · have hj := congrFun S.combination_eq j
        simpa [osiiStrictScalarSeedCoefficientMap, r0,
          Finset.sum_apply, Pi.smul_apply] using hj
    refine ⟨r0, htarget, ?_, Or.inr ?_⟩
    · apply le_of_eq
      dsimp [r0, total]
      apply Finset.sum_congr rfl
      intro i _hi
      simpa using abs_of_nonneg (S.weight_nonneg i)
    · intro hzero
      apply hz
      rw [← htarget]
      simpa [osiiStrictScalarSeedCoefficientCLM_apply] using hzero
  obtain ⟨compactification, hsegment⟩ :=
    exists_stripCompactificationParameters_segment_subset_germDomain
      r0 htotal_nonneg hr0_budget htotal_rho
  let M : StrictScalarSeedCoefficientMZBoundData
      (((initial.toStrictGeneratedTimeContinuationLadder lgc (q + 1)).stage
        (depth + 1)).vi2Equation621TotalNormalizedStage t epsilon)
      compactification S.seed :=
    Classical.choice (StrictScalarSeedCoefficientMZBoundData.nonempty
      (normalizedRawNextDepth_flatCoefficientTube_subset
        initial lgc S.seed S.seed_raw hepsilon.le) hrho_pos hrho_lt_one)
  let T : StrictCoefficientTargetSectionData S.seed r0 :=
    Classical.choice (nonempty_strictCoefficientTargetSectionData
      S.seed r0 S.coefficient_surjective hregular)
  let C : StrictCoefficientTargetConvexChartData compactification r0 :=
    Classical.choice
      (nonempty_strictCoefficientTargetConvexChartData_of_segment_subset hsegment)
  exact ⟨T.toWeightedL1ZeroPointedAmbientChartDataOfFlatWindow
    C M B.alpha_nonneg
    (fun r hr => B.generatorFlatWindowPointBound spatialApprox S.seed
      S.seed_raw hrho_lt_one r hr hepsilon) htarget⟩

set_option maxHeartbeats 4000000 in
/-- Scalar convexification closes every raw successor point at every
positive shift, without changing the predecessor coefficient. -/
theorem nextDepthPointBound
    {initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS}
    {lgc : OSLinearGrowthCondition d OS}
    {depth q t beta : Nat}
    (B : RawStrictGeneratedVI2NormalizedWeightedL1DepthBoundData
      initial lgc t beta depth)
    (spatialApprox : Section43ProductTimeApproximateIdentity
      (((q + 1) + 1) * d))
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (zeta : OSIITimeGapSpace (q + 1))
    (hzeta : zeta ∈ osiiTimeArgumentCarrier
      (osiiRawStrictGeneratedLogarithmicBase (q + 1) (depth + 1))) :
    OSIIEquation621WeightedL1PointBoundData
      ((((initial.toStrictGeneratedTimeContinuationLadder lgc (q + 1)).stage
        (depth + 1)).vi2Equation621TotalNormalizedStage
          t epsilon).distribution zeta)
      ((q + 1) * t) B.alpha beta (depth + 1) := by
  have hraw : OSIIRawStrictGeneratedLogarithmicArgument
      .scalar (q + 1) (depth + 1)
        (fun j => (osiiPrincipalLog zeta j).im) := by
    have hargEq : (fun j => (osiiPrincipalLog zeta j).im) =
        osiiTimeArgumentVector zeta := by
      funext j
      simp [osiiPrincipalLog, osiiTimeArgumentVector, Complex.log_im]
    rw [hargEq]
    simpa only [osiiRawStrictGeneratedLogarithmicBase, Set.mem_setOf_eq]
      using hzeta.2
  obtain ⟨rank, ⟨S⟩⟩ := exists_rankedSectionPresentation hraw
  obtain ⟨Q⟩ := B.nonempty_nextDepthLogarithmicChart
    spatialApprox (osiiPrincipalLog zeta) S hepsilon
  have hzTube : osiiPrincipalLog zeta ∈ osiiLogarithmicTube
      (osiiStrictGeneratedLogarithmicBaseAtRank
        (q + 1) (depth + 1) (rank + 1)) := by
    rw [osiiLogarithmicTube, physicalLogarithmicBase_strictGeneratedAtRank_eq]
    exact S.toRankSucc
  have hsegment :=
    (convex_logarithmicTube_strictGeneratedAtRank
      (q + 1) (depth + 1) (rank + 1)).segment_subset
        (zero_mem_logarithmicTube_strictGeneratedAtRank
          (q + 1) (depth + 1) (rank + 1)) hzTube
  have hphysical := hsegment.trans
    (normalizedDepth_logarithmicRankTube_subset
      initial lgc t (depth + 1) (rank + 1) hepsilon.le (q + 1))
  simpa only [osiiLogExp_principalLog hzeta.1] using
    Q.targetBoundInPhysical hphysical

/-- The genuine complete-normalized VI.2 outer-depth successor. -/
noncomputable def succ
    {initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS}
    {lgc : OSLinearGrowthCondition d OS}
    {t beta depth : Nat}
    (B : RawStrictGeneratedVI2NormalizedWeightedL1DepthBoundData
      initial lgc t beta depth)
    (spatialApprox : forall q,
      Section43ProductTimeApproximateIdentity (((q + 1) + 1) * d)) :
    RawStrictGeneratedVI2NormalizedWeightedL1DepthBoundData
      initial lgc t beta (depth + 1) where
  alpha := B.alpha
  alpha_nonneg := B.alpha_nonneg
  pointBound := by
    intro arity _ epsilon hepsilon zeta hzeta
    cases arity with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q =>
      exact B.nextDepthPointBound (spatialApprox q) hepsilon zeta hzeta

@[simp] theorem succ_alpha
    {initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS}
    {lgc : OSLinearGrowthCondition d OS}
    {t beta depth : Nat}
    (B : RawStrictGeneratedVI2NormalizedWeightedL1DepthBoundData
      initial lgc t beta depth)
    (spatialApprox : forall q,
      Section43ProductTimeApproximateIdentity (((q + 1) + 1) * d)) :
    (B.succ spatialApprox).alpha = B.alpha := rfl

end RawStrictGeneratedVI2NormalizedWeightedL1DepthBoundData

/-- The corrected all-arity VI.1 seed now has its coefficient-preserving
VI.2 successor, with all spatial approximate identities selected internally. -/
noncomputable def canonicalRawNormalizedDepthSuccessorData
    (initial : InitialGeneratedLogarithmicStageLevelData (d := d) OS)
    (lgc : OSLinearGrowthCondition d OS) :
    CanonicalRawNormalizedDepthSuccessorData initial lgc where
  next _ B := B.succ (fun q =>
    fixedTripleConvolutionApproximateIdentity (((q + 1) + 1) * d))
  next_alpha _ _ := rfl

end OSIIChapterV
end OSReconstruction
