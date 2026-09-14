/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVINormalizedEnvelopeWeightedSourceSpatialGrowth
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedVacuumTail










noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

open Section43ProductTimeApproximateIdentity
open Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData

namespace VI2NormalizedReflectedOrbitCoverageData

end VI2NormalizedReflectedOrbitCoverageData

/-- Local normalized-envelope coverage for one reflected moving source.

The route-facing continuation only needs an open zero-based domain containing
the reflected centers that a selected rooted chart evaluates.  Keeping that
domain in the certificate avoids silently upgrading a compact chart-local
problem to coverage of the complete natural moving-slice kernel. -/
structure VI2NormalizedReflectedLocalOrbitCoverageData
    {d q t : Nat} [NeZero d]
    {OS : OsterwalderSchraderAxioms d}
    {C0 : Type*} [CanonicalGeneratorStageLevelProvider OS C0]
    {S0 : C0}
    {epsilon : Real}
    {bound : forall arity,
      SchwartzMap (Section43SpatialSpace d arity) Complex -> Real}
    (Denv : VI2NormalizedEnvelopeFamilyData
      (CanonicalGeneratorStageLevelProvider.toSimultaneousTimeContinuationStageLevel
        (OS := OS) S0) t epsilon bound)
    (target : forall arity, Set (Fin arity -> Complex))
    (sourceStage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (eta : SchwartzMap
      (Fin ((q + 1) + ((q + 1) + 1)) -> Real) Complex) : Type where
  envelopeCoverage : VI2NormalizedEnvelopeCoverageData Denv target
  domain : Set (Fin ((q + 1) + (q + 1)) -> Complex)
  domain_open : IsOpen domain
  domain_starConvex : StarConvex Real 0 domain
  zero_mem : (0 : Fin ((q + 1) + (q + 1)) -> Complex) ∈ domain
  domain_subset : domain ⊆ reflectedMovingSliceCarrier sourceStage eta
  ae_logLift : forall
    (w : Fin ((q + 1) + (q + 1)) -> Complex),
    w ∈ domain ->
    ∀ᵐ sigma : Fin ((q + 1) + ((q + 1) + 1)) -> Real,
      sigma ∈ tsupport
          ((SCV.translateSchwartz
            (fun _ : Fin ((q + 1) + ((q + 1) + 1)) => epsilon)
            eta :
              SchwartzMap
                (Fin ((q + 1) + ((q + 1) + 1)) -> Real) Complex) :
            (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex) ->
        ∃ z ∈ target ((q + 1) + ((q + 1) + 1)),
          osiiLogExp z =
            -(reflectedReducedTimeDisplacementCLM (q + 1) w) +
              osiiPositiveRealTimeEmbed sigma

namespace VI2NormalizedReflectedLocalOrbitCoverageData

/-- A retained compact logarithmic target package gives local normalized
orbit coverage as soon as its target is included in the envelope target
family.

This is the finite-union adapter used by selected rooted charts: each
nontrivial reflected source constructs its own compact log target first, and
the final chart target only has to contain those finitely many pieces. -/
noncomputable def ofCompactLogTarget
    {d q t : Nat} [NeZero d]
    {OS : OsterwalderSchraderAxioms d}
    {C0 : Type*} [CanonicalGeneratorStageLevelProvider OS C0]
    {S0 : C0}
    {epsilon : Real}
    {bound : forall arity,
      SchwartzMap (Section43SpatialSpace d arity) Complex -> Real}
    {Denv : VI2NormalizedEnvelopeFamilyData
      (CanonicalGeneratorStageLevelProvider.toSimultaneousTimeContinuationStageLevel
        (OS := OS) S0) t epsilon bound}
    {target : forall arity, Set (Fin arity -> Complex)}
    (Cenv : VI2NormalizedEnvelopeCoverageData Denv target)
    (sourceStage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (eta : SchwartzMap
      (Fin ((q + 1) + ((q + 1) + 1)) -> Real) Complex)
    (base : Set
      (Fin ((q + 1) + ((q + 1) + 1)) -> Real))
    (K : Set (Fin ((q + 1) + (q + 1)) -> Complex))
    (G : CompactLogTargetReflectedOrbitData
      sourceStage eta epsilon base K)
    (hlogTarget_subset :
      G.logTarget ⊆ target ((q + 1) + ((q + 1) + 1))) :
    {O : VI2NormalizedReflectedLocalOrbitCoverageData Denv target
        sourceStage eta //
      K ⊆ O.domain} := by
  refine
    ⟨{ envelopeCoverage := Cenv
       domain := G.domain
       domain_open := G.domain_open
       domain_starConvex := G.domain_starConvex
       zero_mem := G.zero_mem
       domain_subset := G.domain_subset
       ae_logLift := ?_ },
      G.centers_mem⟩
  intro w hw
  apply Filter.Eventually.of_forall
  intro sigma hsigma
  obtain ⟨z, hz, hexp⟩ := G.logLift w hw sigma hsigma
  exact ⟨z, hlogTarget_subset hz, hexp⟩

/-- Build a continuation-ready local reflected-orbit certificate from a
compact radial family of centers whose translated cutoff orbits stay in one
open logarithmic tube, retaining the fact that every chosen center lies in
the resulting domain.  The recorded domain is the open zero-convex
thickening supplied by the moving-slice compactness lemma. -/
noncomputable def ofCompactRadialHullWithCenters
    {d q t : Nat} [NeZero d]
    {OS : OsterwalderSchraderAxioms d}
    {C0 : Type*} [CanonicalGeneratorStageLevelProvider OS C0]
    {S0 : C0}
    {epsilon : Real}
    {bound : forall arity,
      SchwartzMap (Section43SpatialSpace d arity) Complex -> Real}
    {Denv : VI2NormalizedEnvelopeFamilyData
      (CanonicalGeneratorStageLevelProvider.toSimultaneousTimeContinuationStageLevel
        (OS := OS) S0) t epsilon bound}
    {target : forall arity, Set (Fin arity -> Complex)}
    (Cenv : VI2NormalizedEnvelopeCoverageData Denv target)
    (sourceStage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (eta : SchwartzMap
      (Fin ((q + 1) + ((q + 1) + 1)) -> Real) Complex)
    (heta_compact :
      HasCompactSupport
        (eta :
          (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex))
    (base : Set
      (Fin ((q + 1) + ((q + 1) + 1)) -> Real))
    (hbase_open : IsOpen base)
    (htube_target :
      osiiLogarithmicTube base ⊆
        target ((q + 1) + ((q + 1) + 1)))
    (K : Set (Fin ((q + 1) + (q + 1)) -> Complex))
    (hK_compact : IsCompact K)
    (hK_nonempty : K.Nonempty)
    (hraw_segment : forall center, center ∈ K ->
      segment Real
          (0 : Fin ((q + 1) + (q + 1)) -> Complex) center ⊆
        reflectedMovingSliceCarrier sourceStage eta)
    (horbit_segment : forall center, center ∈ K ->
      forall w,
        w ∈ segment Real
          (0 : Fin ((q + 1) + (q + 1)) -> Complex) center ->
      forall sigma,
        sigma ∈ tsupport
          ((SCV.translateSchwartz
              (fun _ : Fin ((q + 1) + ((q + 1) + 1)) => epsilon)
              eta :
            SchwartzMap
              (Fin ((q + 1) + ((q + 1) + 1)) -> Real) Complex) :
            (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex) ->
        -(reflectedReducedTimeDisplacementCLM (q + 1) w) +
            osiiPositiveRealTimeEmbed sigma ∈
          osiiTimeArgumentCarrier base) :
    {O : VI2NormalizedReflectedLocalOrbitCoverageData Denv target
        sourceStage eta //
      K ⊆ O.domain} := by
  let hexists :=
    exists_openZeroConvex_reflectedOrbitDomain_of_compact_radialHull
      sourceStage eta heta_compact epsilon base hbase_open K hK_compact
      hK_nonempty hraw_segment horbit_segment
  let domain := Classical.choose hexists
  have hdomain := Classical.choose_spec hexists
  have hdomain_open : IsOpen domain := hdomain.1
  have hdomain_starConvex : StarConvex Real 0 domain := hdomain.2.1
  have hzero :
      (0 : Fin ((q + 1) + (q + 1)) -> Complex) ∈ domain :=
    hdomain.2.2.1
  have hdomain_subset :
      domain ⊆ reflectedMovingSliceCarrier sourceStage eta :=
    hdomain.2.2.2.1
  have hlogLift := hdomain.2.2.2.2.2
  refine ⟨{
      envelopeCoverage := Cenv
      domain := domain
      domain_open := hdomain_open
      domain_starConvex := hdomain_starConvex
      zero_mem := hzero
      domain_subset := hdomain_subset
      ae_logLift := by
        intro w hw
        apply Filter.Eventually.of_forall
        intro sigma hsigma
        obtain ⟨z, hz, hexp⟩ := hlogLift w hw sigma hsigma
        exact ⟨z, htube_target hz, hexp⟩ },
    hdomain.2.2.2.2.1⟩

/-- A compact family of strict next-rank mixed tails supplies the geometric
premises of `ofCompactRadialHullWithCenters`, retaining the reflected-center
inclusion needed by selected rooted charts.  Positive translated cutoff
support keeps every reflected radial orbit in the same ranked scalar
argument carrier. -/
private theorem continuous_reflectedCauchyCenter'
    {q : Nat} :
    Continuous
      (reflectedCauchyCenter :
        (Fin (q + 1) -> Complex) ->
          Fin ((q + 1) + (q + 1)) -> Complex) := by
  apply continuous_pi
  intro j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simpa [reflectedCauchyCenter] using
      (continuous_star.comp
        (continuous_apply i :
          Continuous (fun z : Fin (q + 1) -> Complex => z i)))
  · convert
      (continuous_apply i :
        Continuous (fun z : Fin (q + 1) -> Complex => z i)) using 1
    funext z
    simpa using reflectedCauchyCenter_right z i

noncomputable def ofRankSuccessorMixedCompactRadialHullWithCenters
    {d q t : Nat} [NeZero d]
    {OS : OsterwalderSchraderAxioms d}
    {C0 : Type*} [CanonicalGeneratorStageLevelProvider OS C0]
    {S0 : C0}
    {epsilon : Real}
    {bound : forall arity,
      SchwartzMap (Section43SpatialSpace d arity) Complex -> Real}
    {Denv : VI2NormalizedEnvelopeFamilyData
      (CanonicalGeneratorStageLevelProvider.toSimultaneousTimeContinuationStageLevel
        (OS := OS) S0) t epsilon bound}
    {target : forall arity, Set (Fin arity -> Complex)}
    (Cenv : VI2NormalizedEnvelopeCoverageData Denv target)
    (sourceStage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (eta : SchwartzMap
      (Fin ((q + 1) + ((q + 1) + 1)) -> Real) Complex)
    (heta_compact :
      HasCompactSupport
        (eta :
          (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex))
    (depth rank : Nat)
    (htube_target :
      osiiLogarithmicTube
          (osiiStrictGeneratedLogarithmicBaseAtRank
            ((q + 1) + ((q + 1) + 1))
            (depth + 1) (rank + 1)) ⊆
        target ((q + 1) + ((q + 1) + 1)))
    (Z : Set (Fin (q + 1) -> Complex))
    (hZ_compact : IsCompact Z)
    (hZ_nonempty : Z.Nonempty)
    (hZ_ranked :
      Z ⊆
        osiiMixedTailArgumentCarrier
          (osiiStrictGeneratedMixedLogarithmicBaseAtRank
            ((q + 1) + 1) (depth + 1) (rank + 1)))
    (htranslated_support :
      tsupport
          ((SCV.translateSchwartz
              (fun _ : Fin ((q + 1) + ((q + 1) + 1)) => epsilon)
              eta :
            SchwartzMap
              (Fin ((q + 1) + ((q + 1) + 1)) -> Real) Complex) :
            (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex) ⊆
        section43TimeStrictPositiveRegion
          ((q + 1) + ((q + 1) + 1)))
    (hraw_segment : forall z, z ∈ Z ->
      segment Real
          (0 : Fin ((q + 1) + (q + 1)) -> Complex)
          (reflectedCauchyCenter z) ⊆
        reflectedMovingSliceCarrier sourceStage eta) :
    {O : VI2NormalizedReflectedLocalOrbitCoverageData Denv target
        sourceStage eta //
      forall z, z ∈ Z -> reflectedCauchyCenter z ∈ O.domain} := by
  let K : Set (Fin ((q + 1) + (q + 1)) -> Complex) :=
    reflectedCauchyCenter '' Z
  have hcenter_continuous :
      Continuous
        (reflectedCauchyCenter :
          (Fin (q + 1) -> Complex) ->
            Fin ((q + 1) + (q + 1)) -> Complex) := by
    exact continuous_reflectedCauchyCenter'
  have hK_compact : IsCompact K := by
    dsimp [K]
    exact hZ_compact.image hcenter_continuous
  have hK_nonempty : K.Nonempty := by
    exact hZ_nonempty.image reflectedCauchyCenter
  have hrawK : forall center, center ∈ K ->
      segment Real
          (0 : Fin ((q + 1) + (q + 1)) -> Complex) center ⊆
        reflectedMovingSliceCarrier sourceStage eta := by
    intro center hcenter
    obtain ⟨z, hz, rfl⟩ := hcenter
    exact hraw_segment z hz
  have horbitK : forall center, center ∈ K ->
      forall w,
        w ∈ segment Real
          (0 : Fin ((q + 1) + (q + 1)) -> Complex) center ->
      forall sigma,
        sigma ∈ tsupport
          ((SCV.translateSchwartz
              (fun _ : Fin ((q + 1) + ((q + 1) + 1)) => epsilon)
              eta :
            SchwartzMap
              (Fin ((q + 1) + ((q + 1) + 1)) -> Real) Complex) :
            (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex) ->
        -(reflectedReducedTimeDisplacementCLM (q + 1) w) +
            osiiPositiveRealTimeEmbed sigma ∈
          osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBaseAtRank
              ((q + 1) + ((q + 1) + 1))
              (depth + 1) (rank + 1)) := by
    intro center hcenter w hw sigma hsigma
    obtain ⟨z, hz, rfl⟩ := hcenter
    rw [segment_eq_image_lineMap] at hw
    obtain ⟨r, hr, rfl⟩ := hw
    rw [← reflectedCauchyCenter_lineMap_zero z r]
    change
      reflectedCauchyShiftedStagePoint sigma
          (AffineMap.lineMap (k := Real)
            (0 : Fin (q + 1) -> Complex) z r) ∈
        osiiTimeArgumentCarrier
          (osiiStrictGeneratedLogarithmicBaseAtRank
            ((q + 1) + ((q + 1) + 1))
            (depth + 1) (rank + 1))
    apply
      reflectedCauchyShiftedStagePoint_mem_argumentCarrier_of_segment_strictGeneratedAtRank
        (htranslated_support hsigma) (hZ_ranked hz)
    rw [segment_eq_image_lineMap]
    exact ⟨r, hr, rfl⟩
  let O :=
    ofCompactRadialHullWithCenters Cenv sourceStage eta heta_compact
      (osiiStrictGeneratedLogarithmicBaseAtRank
        ((q + 1) + ((q + 1) + 1))
        (depth + 1) (rank + 1))
      (isOpen_rankSuccessorScalarBase
        rank ((q + 1) + ((q + 1) + 1)) depth)
      htube_target K hK_compact hK_nonempty hrawK horbitK
  refine ⟨O.1, ?_⟩
  intro z hz
  exact O.2 ⟨z, hz, rfl⟩

/-- A ranked target tail controls the complete radial hull of its centered
hub-to-target segment.

The centered segment itself is not required to lie in the mixed tail
carrier.  Instead, every radial point is rewritten as a target-and-hub box
point before applying the ranked reflected-Cauchy estimate.  This is the
correct local-domain constructor for target-hub rooted charts. -/
noncomputable def ofRankSuccessorTargetHubSegmentWithCenters
    {d q t : Nat} [NeZero d]
    {OS : OsterwalderSchraderAxioms d}
    {C0 : Type*} [CanonicalGeneratorStageLevelProvider OS C0]
    {S0 : C0}
    {epsilon : Real}
    {bound : forall arity,
      SchwartzMap (Section43SpatialSpace d arity) Complex -> Real}
    {Denv : VI2NormalizedEnvelopeFamilyData
      (CanonicalGeneratorStageLevelProvider.toSimultaneousTimeContinuationStageLevel
        (OS := OS) S0) t epsilon bound}
    {target : forall arity, Set (Fin arity -> Complex)}
    (Cenv : VI2NormalizedEnvelopeCoverageData Denv target)
    (sourceStage : OSIITimeContinuationStage d
      ((q + 1) + ((q + 1) + 1)))
    (eta : SchwartzMap
      (Fin ((q + 1) + ((q + 1) + 1)) -> Real) Complex)
    (heta_compact :
      HasCompactSupport
        (eta :
          (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex))
    (depth rank : Nat)
    (htube_target :
      osiiLogarithmicTube
          (osiiStrictGeneratedLogarithmicBaseAtRank
            ((q + 1) + ((q + 1) + 1))
            (depth + 1) (rank + 1)) ⊆
        target ((q + 1) + ((q + 1) + 1)))
    (anchor hub : Fin ((q + 1) + 1) -> Real)
    (hanchor :
      anchor ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hhub : forall i, anchor i <= hub i)
    (z : Fin (q + 1) -> Complex)
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiStrictGeneratedMixedLogarithmicBaseAtRank
          ((q + 1) + 1) (depth + 1) (rank + 1)))
    (htranslated_dominates :
      forall sigma,
        sigma ∈ tsupport
          ((SCV.translateSchwartz
              (fun _ : Fin ((q + 1) + ((q + 1) + 1)) => epsilon)
              eta :
            SchwartzMap
              (Fin ((q + 1) + ((q + 1) + 1)) -> Real) Complex) :
            (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex) ->
        ReflectedTimeDominatesTailAnchor anchor sigma)
    (hraw_segment : forall point,
      point ∈ segment Real
          (tailAnchorCenteredHubPoint anchor hub)
          (tailAnchorCenteredPoint anchor z) ->
      segment Real
          (0 : Fin ((q + 1) + (q + 1)) -> Complex)
          (reflectedCauchyCenter point) ⊆
        reflectedMovingSliceCarrier sourceStage eta) :
    {O : VI2NormalizedReflectedLocalOrbitCoverageData Denv target
        sourceStage eta //
      forall point,
        point ∈ segment Real
          (tailAnchorCenteredHubPoint anchor hub)
          (tailAnchorCenteredPoint anchor z) ->
        reflectedCauchyCenter point ∈ O.domain} := by
  let Z : Set (Fin (q + 1) -> Complex) :=
    segment Real
      (tailAnchorCenteredHubPoint anchor hub)
      (tailAnchorCenteredPoint anchor z)
  have hZ_compact : IsCompact Z := by
    change IsCompact
      (segment Real
        (tailAnchorCenteredHubPoint anchor hub)
        (tailAnchorCenteredPoint anchor z))
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hZ_nonempty : Z.Nonempty := by
    exact
      ⟨tailAnchorCenteredHubPoint anchor hub,
        left_mem_segment Real _ _⟩
  let K : Set (Fin ((q + 1) + (q + 1)) -> Complex) :=
    reflectedCauchyCenter '' Z
  have hcenter_continuous :
      Continuous
        (reflectedCauchyCenter :
          (Fin (q + 1) -> Complex) ->
            Fin ((q + 1) + (q + 1)) -> Complex) := by
    exact continuous_reflectedCauchyCenter'
  have hK_compact : IsCompact K := by
    dsimp [K]
    exact hZ_compact.image hcenter_continuous
  have hK_nonempty : K.Nonempty :=
    hZ_nonempty.image reflectedCauchyCenter
  have hrawK : forall center, center ∈ K ->
      segment Real
          (0 : Fin ((q + 1) + (q + 1)) -> Complex) center ⊆
        reflectedMovingSliceCarrier sourceStage eta := by
    rintro _center ⟨point, hpoint, rfl⟩
    exact hraw_segment point hpoint
  have horbitK : forall center, center ∈ K ->
      forall w,
        w ∈ segment Real
          (0 : Fin ((q + 1) + (q + 1)) -> Complex) center ->
      forall sigma,
        sigma ∈ tsupport
          ((SCV.translateSchwartz
              (fun _ : Fin ((q + 1) + ((q + 1) + 1)) => epsilon)
              eta :
            SchwartzMap
              (Fin ((q + 1) + ((q + 1) + 1)) -> Real) Complex) :
            (Fin ((q + 1) + ((q + 1) + 1)) -> Real) -> Complex) ->
        -(reflectedReducedTimeDisplacementCLM (q + 1) w) +
            osiiPositiveRealTimeEmbed sigma ∈
          osiiTimeArgumentCarrier
            (osiiStrictGeneratedLogarithmicBaseAtRank
              ((q + 1) + ((q + 1) + 1))
              (depth + 1) (rank + 1)) := by
    rintro _center ⟨point, hpoint, rfl⟩ w hw sigma hsigma
    rw [segment_eq_image_lineMap] at hw
    obtain ⟨r, hr, rfl⟩ := hw
    rw [← reflectedCauchyCenter_lineMap_zero point r]
    change reflectedCauchyShiftedStagePoint sigma
        (AffineMap.lineMap (k := Real)
          (0 : Fin (q + 1) -> Complex) point r) ∈
      osiiTimeArgumentCarrier
        (osiiStrictGeneratedLogarithmicBaseAtRank
          ((q + 1) + ((q + 1) + 1))
          (depth + 1) (rank + 1))
    simpa [AffineMap.lineMap_apply_module] using
      reflectedCauchyShiftedStagePoint_targetHubSegment_mem_argumentCarrier_of_strictGeneratedAtRank
        hanchor hhub (htranslated_dominates sigma hsigma)
        hz hpoint hr
  let O :=
    ofCompactRadialHullWithCenters Cenv sourceStage eta heta_compact
      (osiiStrictGeneratedLogarithmicBaseAtRank
        ((q + 1) + ((q + 1) + 1))
        (depth + 1) (rank + 1))
      (isOpen_rankSuccessorScalarBase
        rank ((q + 1) + ((q + 1) + 1)) depth)
      htube_target K hK_compact hK_nonempty hrawK horbitK
  refine ⟨O.1, ?_⟩
  intro point hpoint
  exact O.2 ⟨point, hpoint, rfl⟩

end VI2NormalizedReflectedLocalOrbitCoverageData

namespace VI2NormalizedReflectedOrbitCoverageData

end VI2NormalizedReflectedOrbitCoverageData

namespace ReflectedGramSpatialSourceData

end ReflectedGramSpatialSourceData

namespace VI2NormalizedTargetSeminormBoundData

end VI2NormalizedTargetSeminormBoundData

namespace VI2NormalizedEnvelopeCoverageData

end VI2NormalizedEnvelopeCoverageData

namespace RootedAllSplitWeightedSourceEndpointBoundData

end RootedAllSplitWeightedSourceEndpointBoundData

namespace RootedAllSplitWeightedSourceInitialRestrictionData

end RootedAllSplitWeightedSourceInitialRestrictionData

namespace RootedAllSplitWeightedSourceReflectedOrbitCoverageData

end RootedAllSplitWeightedSourceReflectedOrbitCoverageData

namespace RootedAllSplitWeightedSourceEnvelopeNumericalBoundData

variable
  {d k depth t : Nat} [NeZero d] [NeZero k]
  {OS : OsterwalderSchraderAxioms d}
  {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
  {S : C}
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k -> Real}
  {P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
  {R : TripleConvolutionRootData I}
  {T : RootedA0BlockContinuousTranslationData OS A R}
  {test : SchwartzMap (Section43SpatialSpace d k) Complex}
  {epsilon : Real}
  {bound : forall arity,
    SchwartzMap (Section43SpatialSpace d arity) Complex -> Real}
  {Denv : VI2NormalizedEnvelopeFamilyData
    (CanonicalGeneratorStageLevelProvider.toSimultaneousTimeContinuationStageLevel
      (OS := OS) S) t epsilon bound}
  {Henv : VI2NormalizedEnvelopeSeminormBoundData Denv}
  {B : Real}
  {Q : RootedAllSplitWeightedSourceInitialRestrictionData
    P A R T test B}

end RootedAllSplitWeightedSourceEnvelopeNumericalBoundData

namespace RootedAllSplitWeightedSourceEnvelopeBoundData

variable
  {d k depth t : Nat} [NeZero d] [NeZero k]
  {OS : OsterwalderSchraderAxioms d}
  {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
  {S : C}
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k -> Real}
  {P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
  {R : TripleConvolutionRootData I}
  {T : RootedA0BlockContinuousTranslationData OS A R}
  {test : SchwartzMap (Section43SpatialSpace d k) Complex}
  {epsilon : Real}
  {bound : forall arity,
    SchwartzMap (Section43SpatialSpace d arity) Complex -> Real}
  {Denv : VI2NormalizedEnvelopeFamilyData
    (CanonicalGeneratorStageLevelProvider.toSimultaneousTimeContinuationStageLevel
      (OS := OS) S) t epsilon bound}
  {Henv : VI2NormalizedEnvelopeSeminormBoundData Denv}
  {B : Real}

end RootedAllSplitWeightedSourceEnvelopeBoundData

end OSIIChapterV
end OSReconstruction
