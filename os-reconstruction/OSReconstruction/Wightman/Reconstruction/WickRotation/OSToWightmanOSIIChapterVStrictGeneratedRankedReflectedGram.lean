/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedClosureRank
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVAnchoredGeneratedCarrierCoverage
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageWideReflectedGramRealization
















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- The reflected scalar diagonal of a strict rank-`rank` mixed point is a
strict scalar point at the same rank. -/
theorem reflectedMixedDiagonal_strictGeneratedAtRank
    {m N rank : Nat}
    {z : Fin m -> Complex}
    (hz :
      reflectedMixedArgument z ∈
        osiiStrictGeneratedMixedLogarithmicBaseAtRank
          (m + 1) N rank) :
    OSIIStrictGeneratedLogarithmicArgumentAtRank
      rank .scalar (m + (m + 1)) N
      (reflectedMixedDiagonal z) := by
  have hdiag :=
    OSIIStrictGeneratedLogarithmicArgumentAtRank.mixed_diagonal_mem_scalar
      (n := m + 1) (by omega) hz
  have hreindexed :=
    OSIIStrictGeneratedLogarithmicArgumentAtRank.reindex
      (by omega :
        2 * (m + 1) - 1 = m + (m + 1))
      hdiag
  exact hreindexed

/-- Every reflected Cauchy point over a strict-positive time parameter stays
in the same ranked scalar argument carrier as the original mixed point. -/
theorem
    reflectedCauchyShiftedStagePoint_mem_argumentCarrier_of_strictGeneratedAtRank
    {m N rank : Nat}
    {tau : Fin (m + (m + 1)) -> Real}
    (htau : tau ∈ section43TimeStrictPositiveRegion (m + (m + 1)))
    {z : Fin m -> Complex}
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          (m + 1) N rank)) :
    reflectedCauchyShiftedStagePoint tau z ∈
      osiiTimeArgumentCarrier
        (osiiStrictGeneratedLogarithmicBaseAtRank
          (m + (m + 1)) N rank) := by
  refine
    ⟨reflectedCauchyShiftedStagePoint_mem_rightHalfPlane
        htau hz.1,
      ?_⟩
  apply
    OSIIStrictGeneratedLogarithmicArgumentAtRank.scalar_hyperrectangle
      (reflectedMixedDiagonal_strictGeneratedAtRank
        (by simpa [reflectedMixedArgument] using hz.2))
  exact
    abs_argumentVector_reflectedCauchyShiftedStagePoint_le
      htau hz.1

/-- Every reflected Cauchy point over the radial segment from zero to a
strict ranked mixed point stays in the matching ranked scalar carrier. -/
theorem
    reflectedCauchyShiftedStagePoint_mem_argumentCarrier_of_segment_strictGeneratedAtRank
    {m N rank : Nat}
    {tau : Fin (m + (m + 1)) -> Real}
    (htau : tau ∈ section43TimeStrictPositiveRegion (m + (m + 1)))
    {z center : Fin m -> Complex}
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          (m + 1) N rank))
    (hcenter : center ∈ segment Real (0 : Fin m -> Complex) z) :
    reflectedCauchyShiftedStagePoint tau center ∈
      osiiTimeArgumentCarrier
        (osiiStrictGeneratedLogarithmicBaseAtRank
          (m + (m + 1)) N rank) := by
  rw [segment_eq_image_lineMap] at hcenter
  obtain ⟨r, hr, rfl⟩ := hcenter
  by_cases hr0 : r = 0
  · subst r
    rw [AffineMap.lineMap_apply_zero]
    have hcenter_zero :
        reflectedCauchyCenter (0 : Fin m -> Complex) =
          (0 : Fin (m + m) -> Complex) := by
      funext j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp
      · rw [reflectedCauchyCenter_right]
        rfl
    have hpoint :
        reflectedCauchyShiftedStagePoint tau
            (0 : Fin m -> Complex) =
          osiiPositiveRealTimeEmbed tau := by
      rw [reflectedCauchyShiftedStagePoint, hcenter_zero,
        map_zero, neg_zero, zero_add]
    rw [hpoint]
    refine
      ⟨(osiiPositiveRealTimeEmbed_mem_rightHalfPlane_iff tau).2 htau,
        ?_⟩
    have harg :
        osiiTimeArgumentVector (osiiPositiveRealTimeEmbed tau) =
          (0 : Fin (m + (m + 1)) -> Real) := by
      funext j
      rw [osiiTimeArgumentVector, osiiPositiveRealTimeEmbed,
        Complex.arg_ofReal_of_nonneg (htau j).le]
      rfl
    rw [harg]
    exact
      OSIIStrictGeneratedLogarithmicArgumentAtRank.scalar_zero_mem
        rank (m + (m + 1)) N
  · apply
      reflectedCauchyShiftedStagePoint_mem_argumentCarrier_of_strictGeneratedAtRank
        htau
    simpa [AffineMap.lineMap_apply_module] using
      real_smul_mem_osiiMixedTailArgumentCarrier_of_pos
        hz (lt_of_le_of_ne hr.1 (Ne.symm hr0))

/-- A strict rank-`rank` scalar realization contains the reflected Cauchy
endpoint of every strict rank-`rank` mixed point. -/
theorem reflectedCauchyCenter_mem_reflectedMovingSliceCarrier_of_strictGeneratedAtRank
    {d m N rank : Nat} [NeZero d]
    (A : OSIITimeContinuationStage d (m + (m + 1)))
    (eta : SchwartzMap (Fin (m + (m + 1)) -> Real) Complex)
    (heta_support :
      tsupport
          (eta : (Fin (m + (m + 1)) -> Real) -> Complex) ⊆
        section43TimeStrictPositiveRegion (m + (m + 1)))
    (hscalar :
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            (m + (m + 1)) N rank) ⊆
        A.carrier)
    {z : Fin m -> Complex}
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          (m + 1) N rank)) :
    reflectedCauchyCenter z ∈
      reflectedMovingSliceCarrier A eta := by
  intro tau htau
  change reflectedCauchyShiftedStagePoint tau z ∈ A.carrier
  exact
    hscalar
      (reflectedCauchyShiftedStagePoint_mem_argumentCarrier_of_strictGeneratedAtRank
        (heta_support htau) hz)

/-- A strict rank scalar realization also contains the radial basepoint of
the reflected moving slice. -/
theorem zero_mem_reflectedMovingSliceCarrier_of_strictGeneratedAtRank
    {d m N rank : Nat} [NeZero d]
    (A : OSIITimeContinuationStage d (m + (m + 1)))
    (eta : SchwartzMap (Fin (m + (m + 1)) -> Real) Complex)
    (heta_support :
      tsupport
          (eta : (Fin (m + (m + 1)) -> Real) -> Complex) ⊆
        section43TimeStrictPositiveRegion (m + (m + 1)))
    (hscalar :
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            (m + (m + 1)) N rank) ⊆
        A.carrier) :
    (0 : Fin (m + m) -> Complex) ∈
      reflectedMovingSliceCarrier A eta := by
  apply
    zero_mem_reflectedMovingSliceCarrier A eta
      (section43TimeStrictPositiveRegion (m + (m + 1)))
      heta_support
  intro tau htau
  apply hscalar
  refine
    ⟨(osiiPositiveRealTimeEmbed_mem_rightHalfPlane_iff tau).2 htau,
      ?_⟩
  have harg :
      osiiTimeArgumentVector (osiiPositiveRealTimeEmbed tau) =
        (0 : Fin (m + (m + 1)) -> Real) := by
    funext j
    rw [osiiTimeArgumentVector, osiiPositiveRealTimeEmbed,
      Complex.arg_ofReal_of_nonneg (htau j).le]
    rfl
  rw [harg]
  exact
    OSIIStrictGeneratedLogarithmicArgumentAtRank.scalar_zero_mem
      rank (m + (m + 1)) N

/-- Strict rank scalar realization controls the complete reflected radial
segment needed by finite Cauchy continuation. -/
theorem reflected_segment_subset_reflectedMovingSliceCarrier_of_strictGeneratedAtRank
    {d m N rank : Nat} [NeZero d]
    (A : OSIITimeContinuationStage d (m + (m + 1)))
    (eta : SchwartzMap (Fin (m + (m + 1)) -> Real) Complex)
    (heta_support :
      tsupport
          (eta : (Fin (m + (m + 1)) -> Real) -> Complex) ⊆
        section43TimeStrictPositiveRegion (m + (m + 1)))
    (hscalar :
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            (m + (m + 1)) N rank) ⊆
        A.carrier)
    {z : Fin m -> Complex}
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          (m + 1) N rank)) :
    ∀ center ∈ segment ℝ (0 : Fin m -> Complex) z,
      reflectedCauchyCenter center ∈
        reflectedMovingSliceCarrier A eta := by
  intro center hcenter
  intro tau htau
  change reflectedCauchyShiftedStagePoint tau center ∈ A.carrier
  exact
    hscalar
      (reflectedCauchyShiftedStagePoint_mem_argumentCarrier_of_segment_strictGeneratedAtRank
        (heta_support htau) hz hcenter)

/-- Every zero-anchor point over a strict-positive time parameter stays in
the same ranked scalar argument carrier as the original mixed point. -/
theorem
    zeroAnchorShiftedStagePoint_mem_argumentCarrier_of_strictGeneratedAtRank
    {m N rank : Nat}
    {tau : Fin (m + (m + 1)) -> Real}
    (htau : tau ∈ section43TimeStrictPositiveRegion (m + (m + 1)))
    {z : Fin m -> Complex}
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          (m + 1) N rank)) :
    zeroAnchorShiftedStagePoint tau z ∈
      osiiTimeArgumentCarrier
        (osiiStrictGeneratedLogarithmicBaseAtRank
          (m + (m + 1)) N rank) := by
  refine
    ⟨zeroAnchorShiftedStagePoint_mem_rightHalfPlane
        htau hz.1,
      ?_⟩
  apply
    OSIIStrictGeneratedLogarithmicArgumentAtRank.scalar_hyperrectangle
      (reflectedMixedDiagonal_strictGeneratedAtRank
        (by simpa [reflectedMixedArgument] using hz.2))
  exact
    abs_argumentVector_zeroAnchorShiftedStagePoint_le
      htau hz.1

/-- The zero-anchor scalar pairing of a strict rank mixed point remains in
the same strict rank scalar moving-slice carrier. -/
theorem zeroAnchorPair_mem_reflectedMovingSliceCarrier_of_strictGeneratedAtRank
    {d m N rank : Nat} [NeZero d]
    (A : OSIITimeContinuationStage d (m + (m + 1)))
    (eta : SchwartzMap (Fin (m + (m + 1)) -> Real) Complex)
    (heta_support :
      tsupport
          (eta : (Fin (m + (m + 1)) -> Real) -> Complex) ⊆
        section43TimeStrictPositiveRegion (m + (m + 1)))
    (hscalar :
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            (m + (m + 1)) N rank) ⊆
        A.carrier)
    {z : Fin m -> Complex}
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          (m + 1) N rank)) :
    reflectedAnchorPair (0 : Fin m -> Complex) z ∈
      reflectedMovingSliceCarrier A eta := by
  intro tau htau
  change zeroAnchorShiftedStagePoint tau z ∈ A.carrier
  exact
    hscalar
      (zeroAnchorShiftedStagePoint_mem_argumentCarrier_of_strictGeneratedAtRank
        (heta_support htau) hz)

/-- The complete radial segment of zero-anchor pairings remains in the
strict rank scalar moving-slice carrier. -/
theorem zeroAnchorPair_segment_subset_reflectedMovingSliceCarrier_of_strictGeneratedAtRank
    {d m N rank : Nat} [NeZero d]
    (A : OSIITimeContinuationStage d (m + (m + 1)))
    (eta : SchwartzMap (Fin (m + (m + 1)) -> Real) Complex)
    (heta_support :
      tsupport
          (eta : (Fin (m + (m + 1)) -> Real) -> Complex) ⊆
        section43TimeStrictPositiveRegion (m + (m + 1)))
    (hscalar :
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            (m + (m + 1)) N rank) ⊆
        A.carrier)
    {z : Fin m -> Complex}
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          (m + 1) N rank)) :
    ∀ center ∈ segment ℝ (0 : Fin m -> Complex) z,
      reflectedAnchorPair (0 : Fin m -> Complex) center ∈
        reflectedMovingSliceCarrier A eta := by
  intro center hcenter
  rw [segment_eq_image_lineMap] at hcenter
  obtain ⟨t, ht, rfl⟩ := hcenter
  by_cases ht0 : t = 0
  · subst t
    have hzero :
        reflectedAnchorPair
            (0 : Fin m -> Complex) (0 : Fin m -> Complex) =
          (0 : Fin (m + m) -> Complex) := by
      funext j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp [reflectedAnchorPair]
      · rw [reflectedAnchorPair, Fin.append_right]
        rfl
    rw [AffineMap.lineMap_apply_zero, hzero]
    exact
      zero_mem_reflectedMovingSliceCarrier_of_strictGeneratedAtRank
        A eta heta_support hscalar
  · apply
      zeroAnchorPair_mem_reflectedMovingSliceCarrier_of_strictGeneratedAtRank
        A eta heta_support hscalar
    simpa [AffineMap.lineMap_apply_module] using
      real_smul_mem_osiiMixedTailArgumentCarrier_of_pos
        hz (lt_of_le_of_ne ht.1 (Ne.symm ht0))

/-- An anchored reflected-Gram seed with a strict rank scalar domain reaches
every strict mixed point in the same rank. -/
theorem exists_anchored_chain_reaching_strictGeneratedMixedCarrierAtRank
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [CompleteSpace H]
    {iota : Type*} {k N rank : Nat}
    {scalar :
      iota -> iota ->
        (Fin ((k + 1) + (k + 1)) -> Complex) -> Complex}
    {anchorField : iota -> H}
    (P : SourceIndexedReflectedGramHilbertFieldData
      H iota (k + 1) scalar)
    (A0 : SourceIndexedAnchoredReflectedGramHilbertFieldData
      scalar (0 : Fin (k + 1) -> Complex) anchorField P)
    {d : Nat} [NeZero d]
    (A : OSIITimeContinuationStage d
      ((k + 1) + ((k + 1) + 1)))
    (eta : SchwartzMap
      (Fin ((k + 1) + ((k + 1) + 1)) -> Real) Complex)
    (heta_support :
      tsupport
          (eta :
            (Fin ((k + 1) + ((k + 1) + 1)) -> Real) -> Complex) ⊆
        section43TimeStrictPositiveRegion
          ((k + 1) + ((k + 1) + 1)))
    (hscalar :
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            ((k + 1) + ((k + 1) + 1)) N rank) ⊆
        A.carrier)
    (hscalarDomain :
      P.scalarDomain = reflectedMovingSliceCarrier A eta)
    (hzero : (0 : Fin (k + 1) -> Complex) ∈ P.domain)
    {z : Fin (k + 1) -> Complex}
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((k + 1) + 1) N rank)) :
    exists steps : Nat,
      exists C : SourceIndexedReflectedGramContinuationChain
          H iota k scalar P steps,
        exists _Aterminal :
            SourceIndexedAnchoredReflectedGramHilbertFieldData
              scalar (0 : Fin (k + 1) -> Complex)
              anchorField C.terminal,
          z ∈ C.terminal.domain := by
  apply
    SourceIndexedAnchoredReflectedGramContinuationChain.exists_chain_reaching_of_segment_subsets_scalarDomain
      A0 hzero
  · intro center hcenter
    rw [hscalarDomain]
    exact
      reflected_segment_subset_reflectedMovingSliceCarrier_of_strictGeneratedAtRank
        A eta heta_support hscalar hz center hcenter
  · intro center hcenter
    rw [hscalarDomain]
    exact
      zeroAnchorPair_segment_subset_reflectedMovingSliceCarrier_of_strictGeneratedAtRank
        A eta heta_support hscalar hz center hcenter

/-- Strict rank anchored-chain reachability gives coverage by the maximal
source-indexed anchored atlas. -/
theorem strictGeneratedMixedCarrierAtRank_subset_anchoredAtlasCoveredDomain
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [CompleteSpace H]
    {iota : Type*} {k N rank : Nat}
    {scalar :
      iota -> iota ->
        (Fin ((k + 1) + (k + 1)) -> Complex) -> Complex}
    {anchorField : iota -> H}
    (P : SourceIndexedReflectedGramHilbertFieldData
      H iota (k + 1) scalar)
    (A0 : SourceIndexedAnchoredReflectedGramHilbertFieldData
      scalar (0 : Fin (k + 1) -> Complex) anchorField P)
    {d : Nat} [NeZero d]
    (A : OSIITimeContinuationStage d
      ((k + 1) + ((k + 1) + 1)))
    (eta : SchwartzMap
      (Fin ((k + 1) + ((k + 1) + 1)) -> Real) Complex)
    (heta_support :
      tsupport
          (eta :
            (Fin ((k + 1) + ((k + 1) + 1)) -> Real) -> Complex) ⊆
        section43TimeStrictPositiveRegion
          ((k + 1) + ((k + 1) + 1)))
    (hscalar :
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            ((k + 1) + ((k + 1) + 1)) N rank) ⊆
        A.carrier)
    (hscalarDomain :
      P.scalarDomain = reflectedMovingSliceCarrier A eta)
    (hzero : (0 : Fin (k + 1) -> Complex) ∈ P.domain) :
    osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((k + 1) + 1) N rank) ⊆
      SourceIndexedAnchoredReflectedGramChart.coveredDomain
        (H := H) (ι := iota) (m := k + 1)
        (scalar := scalar)
        (anchorPoint := (0 : Fin (k + 1) -> Complex))
        (anchorField := anchorField) := by
  apply
    SourceIndexedAnchoredReflectedGramChart.subset_coveredDomain_of_exists_chart
  intro z hz
  obtain ⟨steps, C, Aterminal, hzC⟩ :=
    exists_anchored_chain_reaching_strictGeneratedMixedCarrierAtRank
      P A0 A eta heta_support hscalar hscalarDomain hzero hz
  exact
    ⟨{ gram := C.terminal, anchored := Aterminal }, hzC⟩

namespace UniformCompactTimeMixedHilbertGramFamilyData

variable {d q N rank : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}
variable {K : Set (Fin ((q + 1) + 1) -> Real)}

/-- The production maximal anchored atlas covers every strict generated
mixed point in one analytic-rank stratum. -/
theorem strictGeneratedMixedCarrierAtRank_subset_anchoredAtlasCoveredDomain
    (stage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (germ : UniformCompactTimeMixedReflectedSourceFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a))
    (G : UniformCompactTimeMixedHilbertGramFamilyData OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ)
    (hscalar :
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            ((q + 1) + ((q + 1) + 1)) N rank) ⊆
        stage.carrier) :
    osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) N rank) ⊆
      G.anchoredAtlasCoveredDomain stage germ := by
  let P :=
    G.toInitialSourceIndexedReflectedGramHilbertFieldData
      OS
      (fun a : AnchoredSourceIndex d q K =>
        UniformCompactTimeSource.source (K := K) a)
      stage germ
  let A0 :=
    G.toInitialSourceIndexedAnchoredReflectedGramHilbertFieldData
      stage germ
  exact
    OSIIChapterV.strictGeneratedMixedCarrierAtRank_subset_anchoredAtlasCoveredDomain
      P A0 stage germ.η germ.η_support hscalar rfl
      (SCV.center_mem_polydisc fun _ => G.gramRadius_pos)

end UniformCompactTimeMixedHilbertGramFamilyData

namespace UniversalCompactCarrierAnchoredAtlasData

variable {d q N rank : Nat} [NeZero d]
variable
  {L : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {K : Set (Fin ((q + 1) + 1) -> Real)}

/-- A universal compact-carrier atlas built from a strict rank scalar stage
covers the corresponding strict rank mixed carrier in its source-linear
domain. -/
theorem strictGeneratedMixedCarrierAtRank_subset_spatialLinearDomain
    (D : UniversalCompactCarrierAnchoredAtlasData L OS K)
    (hscalar :
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            ((q + 1) + ((q + 1) + 1)) N rank) ⊆
        D.sourceStage.stage.carrier) :
    osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) N rank) ⊆
      D.spatialLinearDomain := by
  intro z hz
  exact
    ⟨D.gram.strictGeneratedMixedCarrierAtRank_subset_anchoredAtlasCoveredDomain
        D.sourceStage.stage D.sourceStage.germ hscalar hz,
      zeroAnchorPair_mem_reflectedMovingSliceCarrier_of_strictGeneratedAtRank
        D.sourceStage.stage D.sourceStage.germ.η
        D.sourceStage.germ.η_support hscalar hz,
      reflectedCauchyCenter_mem_reflectedMovingSliceCarrier_of_strictGeneratedAtRank
        D.sourceStage.stage D.sourceStage.germ.η
        D.sourceStage.germ.η_support hscalar hz⟩

end UniversalCompactCarrierAnchoredAtlasData

variable {d : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}

/-- One source-indexed reflected-Gram realization of a strict generated
mixed rank stratum. -/
structure StrictGeneratedMixedReflectedGramAtlasRankData
    {C : Type*}
    [CanonicalGeneratorStageLevelProvider OS C]
    (S : C)
    (depth rank q : Nat)
    (K : Set (Fin ((q + 1) + 1) -> Real)) where
  atlas :
    UniversalCompactCarrierAnchoredAtlasData
      (q := q)
        (CanonicalGeneratorStageLevelProvider.toSimultaneousTimeContinuationStageLevel
          (OS := OS) S)
        OS K
  coversStrictGeneratedAtRank :
    osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) depth rank) ⊆
      atlas.spatialLinearDomain

namespace StrictGeneratedMixedReflectedGramAtlasRankData

/-- A compact strict-positive source carrier and a strict rank scalar
realization construct the non-circular reflected-Gram package at that rank. -/
theorem nonempty_of_strictGeneratedAtRank
    {C : Type*}
    [CanonicalGeneratorStageLevelProvider OS C]
    (S : C)
    (depth rank q : Nat)
    (K : Set (Fin ((q + 1) + 1) -> Real))
    (hK_compact : IsCompact K)
    (hK_positive :
      K ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hscalar :
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            ((q + 1) + ((q + 1) + 1)) depth rank) ⊆
        (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S
          ((q + 1) + ((q + 1) + 1))).carrier) :
    Nonempty
      (StrictGeneratedMixedReflectedGramAtlasRankData
        (OS := OS) S depth rank q K) := by
  let L :=
    CanonicalGeneratorStageLevelProvider.toSimultaneousTimeContinuationStageLevel
      (OS := OS) S
  obtain ⟨D⟩ :=
    nonempty_universalCompactCarrierAnchoredAtlasData
      (q := q) L OS
      (CanonicalGeneratorStageLevelProvider.hasCanonicalReducedCompactEdges
        (OS := OS) S)
      K hK_compact hK_positive
  refine ⟨{
    atlas := D
    coversStrictGeneratedAtRank := ?_ }⟩
  apply
    D.strictGeneratedMixedCarrierAtRank_subset_spatialLinearDomain
  rw [D.sourceStage_eq]
  exact hscalar

end StrictGeneratedMixedReflectedGramAtlasRankData

/-- The reflected-Gram `(A_{N,r}) -> (P_{N,r})` payload at every positive
mixed tail arity and compact strict-positive source carrier. -/
structure StageWideStrictGeneratedMixedReflectedGramRankData
    {C : Type*}
    [CanonicalGeneratorStageLevelProvider OS C]
    (S : C)
    (depth rank : Nat) where
  scalarStrictGeneratedAtRank :
    forall arity,
      osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            arity depth rank) ⊆
        (CanonicalGeneratorStageLevelProvider.stage
          (OS := OS) S arity).carrier
  forCarrier :
    forall (q : Nat)
      (K : Set (Fin ((q + 1) + 1) -> Real)),
      IsCompact K ->
      K ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1) ->
      StrictGeneratedMixedReflectedGramAtlasRankData
        (OS := OS) S depth rank q K

namespace StageWideStrictGeneratedMixedReflectedGramRankData

/-- Forget only the strict-rank coverage proof, retaining the common
carrier-parametric analytic atlas family used by rooted generator
continuation. -/
noncomputable def toAtlasFamily
    {C : Type*}
    [CanonicalGeneratorStageLevelProvider OS C]
    {S : C}
    {depth rank : Nat}
    (P : StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank) :
    StageWideReflectedGramAtlasFamilyData (OS := OS) S depth where
  forCarrier q K hK_compact hK_positive :=
    { atlas :=
        (P.forCarrier q K hK_compact hK_positive).atlas }

/-- A simultaneous strict rank scalar realization constructs the
source-indexed reflected-Gram package at the same rank. -/
noncomputable def ofStrictGeneratedAtRank
    {C : Type*}
    [CanonicalGeneratorStageLevelProvider OS C]
    (S : C)
    (depth rank : Nat)
    (hscalar :
      forall arity,
        osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBaseAtRank
              arity depth rank) ⊆
          (CanonicalGeneratorStageLevelProvider.stage
            (OS := OS) S arity).carrier) :
    StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) S depth rank where
  scalarStrictGeneratedAtRank := hscalar
  forCarrier q K hK_compact hK_positive :=
    Classical.choice
      (StrictGeneratedMixedReflectedGramAtlasRankData.nonempty_of_strictGeneratedAtRank
        S depth rank q K hK_compact hK_positive
        (hscalar ((q + 1) + ((q + 1) + 1))))

end StageWideStrictGeneratedMixedReflectedGramRankData

end OSIIChapterV
end OSReconstruction
