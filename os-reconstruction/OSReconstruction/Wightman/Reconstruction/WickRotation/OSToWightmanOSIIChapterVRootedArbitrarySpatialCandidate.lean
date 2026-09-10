/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketRootedHolomorphicSmearing
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketRootedTwoScaleFamily
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorRadialDomain

















noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical Topology

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData
namespace RootedA0BlockContinuousTranslationData

variable {d k : Nat} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k -> Real}
  {OS : OsterwalderSchraderAxioms d}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
  {R : TripleConvolutionRootData I}

/-- Arbitrary-test form of
`axisPairTwoBlockTimeSpatialSource_schwinger_eq_absoluteHermite`.
If an absolute spatial test pulls back to one left/right product, its split
Schwinger functional is exactly the source-native two-block pairing. -/
theorem axisPairTwoBlockTimeSpatialSource_schwinger_eq_absoluteSpatial_of_pullback
    (i : GeneratorIndex k)
    (etaLeft : SchwartzMap (Fin i.n -> Real) Complex)
    (hetaLeft : tsupport (etaLeft : (Fin i.n -> Real) -> Complex) ⊆
      section43TimeStrictPositiveRegion i.n)
    (leftTest : SchwartzMap (Section43SpatialSpace d i.n) Complex)
    (etaRight : SchwartzMap (Fin i.m -> Real) Complex)
    (hetaRight : tsupport (etaRight : (Fin i.m -> Real) -> Complex) ⊆
      section43TimeStrictPositiveRegion i.m)
    (rightTest : SchwartzMap (Section43SpatialSpace d i.m) Complex)
    (s t : Real)
    (ht : 0 < t)
    (hspan : ∀ delta ∈ tsupport
      (etaLeft : (Fin i.n -> Real) -> Complex),
      (section43ScalarDiffCLE i.n).symm delta
          (Fin.rev ⟨0, i.hn⟩) < s)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) Complex)
    (hF : generatorSplitSpatialPullbackCLM (d := d) i F =
      section43TwoBlockSpatialProduct leftTest rightTest) :
    OS.S (i.n + i.m)
        (ZeroDiagonalSchwartz.ofClassical
          (axisPairTwoBlockTimeSpatialSource i.n i.m
            etaLeft leftTest etaRight rightTest t)) =
      generatorSplitAbsoluteSpatialSchwingerCLM
        OS i etaLeft hetaLeft etaRight hetaRight s t ht.le hspan F := by
  have hschwinger :=
    axisPairTwoBlockTimeSpatialSource_schwinger_eq_global
      OS i.n i.m etaLeft hetaLeft leftTest
        etaRight hetaRight rightTest s t ht
  have hsource :
      axisPairGlobalTimeSpatialSource i.n i.m s t
          (axisPairBlockTimeSpatialTensor i.n i.m
            etaLeft leftTest etaRight rightTest) =
        axisPairGlobalAbsoluteSpatialSourceCLM i.n i.m
          etaLeft etaRight s t
          (generatorSplitSpatialPullbackCLM (d := d) i F) := by
    rw [axisPairGlobalAbsoluteSpatialSourceCLM_apply, hF,
      axisPairSeparateTimeSpatialTensor_twoBlockSpatialProduct]
  let Z :=
    axisPairGlobalAbsoluteSpatialSourceZeroCLM
      (d := d) i.n i.m i.hn i.hm
      etaLeft hetaLeft etaRight hetaRight s t ht.le hspan
  have hvanish :
      VanishesToInfiniteOrderOnCoincidence
        (axisPairGlobalTimeSpatialSource i.n i.m s t
          (axisPairBlockTimeSpatialTensor i.n i.m
            etaLeft leftTest etaRight rightTest)) := by
    rw [hsource]
    exact (Z (generatorSplitSpatialPullbackCLM (d := d) i F)).2
  have hzero :
      ZeroDiagonalSchwartz.ofClassical
          (axisPairGlobalTimeSpatialSource i.n i.m s t
            (axisPairBlockTimeSpatialTensor i.n i.m
              etaLeft leftTest etaRight rightTest)) =
        Z (generatorSplitSpatialPullbackCLM (d := d) i F) := by
    apply Subtype.ext
    rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes _ hvanish]
    exact hsource
  rw [hschwinger, hzero]
  rfl

/-- The synchronized rooted left field evaluated on one arbitrary spatial
block test. -/
noncomputable def leftArbitrarySpatialGeneratorField
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : Nat)
    (chi : SchwartzMap
      (Section43SpatialSpace d ((i.n - 1) + 1)) Complex) :
    (Fin (i.n - 1) -> Complex) -> OSHilbertSpace OS :=
  fun z =>
    (D.left i).field (D.leftCofinalIndex i timeScale) z chi

/-- The synchronized rooted right field evaluated on one arbitrary spatial
block test. -/
noncomputable def rightArbitrarySpatialGeneratorField
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : Nat)
    (chi : SchwartzMap
      (Section43SpatialSpace d ((i.m - 1) + 1)) Complex) :
    (Fin (i.m - 1) -> Complex) -> OSHilbertSpace OS :=
  fun z =>
    (D.right i).field (D.rightCofinalIndex i timeScale) z chi

/-- The unsmeared semigroup pairing of two arbitrary rooted spatial block
tests at one synchronized packet scale. -/
noncomputable def arbitrarySpatialGeneratorCandidate
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (timeScale : Nat)
    (leftTest : SchwartzMap
      (Section43SpatialSpace d ((i.n - 1) + 1)) Complex)
    (rightTest : SchwartzMap
      (Section43SpatialSpace d ((i.m - 1) + 1)) Complex) :
    OSIITimeGapSpace k -> Complex :=
  generatorSemigroupCandidate OS lgc i
    (D.leftArbitrarySpatialGeneratorField i timeScale leftTest)
    (D.rightArbitrarySpatialGeneratorField i timeScale rightTest)

/-- The arbitrary right spatial field after applying the same synchronized
middle-root operator used by every rooted Hermite mode. -/
noncomputable def rootSmearedRightArbitrarySpatialGeneratorField
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (timeScale : Nat)
    (chi : SchwartzMap
      (Section43SpatialSpace d ((i.m - 1) + 1)) Complex) :
    (Fin (i.m - 1) -> Complex) -> OSHilbertSpace OS :=
  fun z =>
    D.semigroupBridgeRootOperator lgc i timeScale
      (D.rightArbitrarySpatialGeneratorField i timeScale chi z)

/-- The root-smeared semigroup candidate associated with one rank-one pair
of arbitrary spatial block tests. -/
noncomputable def rootSmearedArbitrarySpatialGeneratorCandidate
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (timeScale : Nat)
    (leftTest : SchwartzMap
      (Section43SpatialSpace d ((i.n - 1) + 1)) Complex)
    (rightTest : SchwartzMap
      (Section43SpatialSpace d ((i.m - 1) + 1)) Complex) :
    OSIITimeGapSpace k -> Complex :=
  generatorSemigroupCandidate OS lgc i
    (D.leftArbitrarySpatialGeneratorField i timeScale leftTest)
    (D.rootSmearedRightArbitrarySpatialGeneratorField
      lgc i timeScale rightTest)

/-- A fixed arbitrary left spatial block test has one chronological
neighborhood on which its translated-source formula is valid at every
packet scale.  Uniformity follows from the retained all-scale compact time
carrier, not from any spatial-test seminorm estimate. -/
theorem
    eventually_rootedLeftBlockTranslatedSpatialSource_coe_eq_timeProfile_uniform_scale_test
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (chi : SchwartzMap
      (Section43SpatialSpace d ((i.n - 1) + 1)) Complex) :
    ∀ᶠ x : Fin (i.n - 1) -> Real in nhds 0,
      forall timeScale : Nat,
        (A.rootedLeftBlockTranslatedSpatialSource R i
          (timeScale + D.commonTailStart i) x chi).1 =
          section43OrderedPullbackTimeSpatialTensorCLM
            d ((i.n - 1) + 1) chi
            (SCV.translateSchwartz
              (fun j => -Fin.cases 0 x j)
              ((A.rootedLeftBlockApproximateIdentity R i).translatedSource
                (A.rootedLeftBlockAnchor i)
                (A.rootedLeftBlockAnchor_positive i)
                (timeScale + D.commonTailStart i)).f) := by
  have hf :
      HasUniformCompactStrictPositiveDifferenceTimeSupport
        (fun timeScale : Nat =>
          (A.rootedLeftBlockSpatialSource R i
            (timeScale + D.commonTailStart i) chi).1) := by
    obtain ⟨K, hK_compact, hK_positive, hK⟩ :=
      rootedLeftBlockSpatialSource_uniformCompactSupport_all_scales A R i
    refine ⟨K, hK_compact, hK_positive, ?_⟩
    intro timeScale q hq
    exact hK (timeScale + D.commonTailStart i, chi) q hq
  filter_upwards
    [eventually_localPositiveTimeParameterTranslate_family_chronological_coe_eq
      (fun timeScale : Nat =>
        A.rootedLeftBlockSpatialSource R i
          (timeScale + D.commonTailStart i) chi)
      hf] with x hx
  intro timeScale
  change
    (localPositiveTimeParameterTranslate
      (A.rootedLeftBlockSpatialSource R i
        (timeScale + D.commonTailStart i) chi)
      (fun a : Fin (i.n - 1) =>
        chronologicalTimeSourceDirection (d := d) a) x).1 = _
  rw [hx timeScale]
  change
    translateSchwartzConfiguration
        (sourceParameterDisplacementCLM
          (fun a : Fin (i.n - 1) =>
            chronologicalTimeSourceDirection (d := d) a) x)
        (section43OrderedPullbackTimeSpatialTensorCLM
          d ((i.n - 1) + 1) chi
          ((A.rootedLeftBlockApproximateIdentity R i).translatedSource
            (A.rootedLeftBlockAnchor i)
            (A.rootedLeftBlockAnchor_positive i)
            (timeScale + D.commonTailStart i)).f) = _
  exact
    translate_chronologicalSource_orderedPullbackTimeSpatialTensor
      (d := d) (k := i.n - 1) x chi
      ((A.rootedLeftBlockApproximateIdentity R i).translatedSource
        (A.rootedLeftBlockAnchor i)
        (A.rootedLeftBlockAnchor_positive i)
        (timeScale + D.commonTailStart i)).f

/-- Right-block form of
`eventually_rootedLeftBlockTranslatedSpatialSource_coe_eq_timeProfile_uniform_scale_test`.
-/
theorem
    eventually_rootedRightBlockTranslatedSpatialSource_coe_eq_timeProfile_uniform_scale_test
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (chi : SchwartzMap
      (Section43SpatialSpace d ((i.m - 1) + 1)) Complex) :
    ∀ᶠ x : Fin (i.m - 1) -> Real in nhds 0,
      forall timeScale : Nat,
        (A.rootedRightBlockTranslatedSpatialSource R i
          (timeScale + D.commonTailStart i) x chi).1 =
          section43OrderedPullbackTimeSpatialTensorCLM
            d ((i.m - 1) + 1) chi
            (SCV.translateSchwartz
              (fun j => -Fin.cases 0 x j)
              ((A.rootedRightBlockApproximateIdentity R i).translatedSource
                (A.rootedRightBlockAnchor i)
                (A.rootedRightBlockAnchor_positive i)
                (timeScale + D.commonTailStart i)).f) := by
  have hf :
      HasUniformCompactStrictPositiveDifferenceTimeSupport
        (fun timeScale : Nat =>
          (A.rootedRightBlockSpatialSource R i
            (timeScale + D.commonTailStart i) chi).1) := by
    obtain ⟨K, hK_compact, hK_positive, hK⟩ :=
      rootedRightBlockSpatialSource_uniformCompactSupport_all_scales A R i
    refine ⟨K, hK_compact, hK_positive, ?_⟩
    intro timeScale q hq
    exact hK (timeScale + D.commonTailStart i, chi) q hq
  filter_upwards
    [eventually_localPositiveTimeParameterTranslate_family_chronological_coe_eq
      (fun timeScale : Nat =>
        A.rootedRightBlockSpatialSource R i
          (timeScale + D.commonTailStart i) chi)
      hf] with x hx
  intro timeScale
  change
    (localPositiveTimeParameterTranslate
      (A.rootedRightBlockSpatialSource R i
        (timeScale + D.commonTailStart i) chi)
      (fun a : Fin (i.m - 1) =>
        chronologicalTimeSourceDirection (d := d) a) x).1 = _
  rw [hx timeScale]
  change
    translateSchwartzConfiguration
        (sourceParameterDisplacementCLM
          (fun a : Fin (i.m - 1) =>
            chronologicalTimeSourceDirection (d := d) a) x)
        (section43OrderedPullbackTimeSpatialTensorCLM
          d ((i.m - 1) + 1) chi
          ((A.rootedRightBlockApproximateIdentity R i).translatedSource
            (A.rootedRightBlockAnchor i)
            (A.rootedRightBlockAnchor_positive i)
            (timeScale + D.commonTailStart i)).f) = _
  exact
    translate_chronologicalSource_orderedPullbackTimeSpatialTensor
      (d := d) (k := i.m - 1) x chi
      ((A.rootedRightBlockApproximateIdentity R i).translatedSource
        (A.rootedRightBlockAnchor i)
        (A.rootedRightBlockAnchor_positive i)
        (timeScale + D.commonTailStart i)).f

/-- On the positive real edge, the arbitrary unsmeared candidate is exactly
the Schwinger pairing of the two translated rooted block sources. -/
theorem arbitrarySpatialGeneratorCandidate_positiveReal_eq_schwinger
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (timeScale : Nat)
    (leftTest : SchwartzMap
      (Section43SpatialSpace d ((i.n - 1) + 1)) Complex)
    (rightTest : SchwartzMap
      (Section43SpatialSpace d ((i.m - 1) + 1)) Complex)
    (tau : Fin k -> Real)
    (hbridge : 0 < tau i.bridgeGlobalIndex)
    (hleft : i.leftRealCoordinates tau ∈ (D.left i).realRegion)
    (hright : i.rightRealCoordinates tau ∈ (D.right i).realRegion) :
    D.arbitrarySpatialGeneratorCandidate
        lgc i timeScale leftTest rightTest
        (osiiPositiveRealTimeEmbed tau) =
      OS.S (((i.n - 1) + 1) + ((i.m - 1) + 1))
        (ZeroDiagonalSchwartz.ofClassical
          ((A.rootedLeftBlockTranslatedSpatialSource R i
              (timeScale + D.commonTailStart i)
              (i.leftRealCoordinates tau) leftTest).1.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d)
              (tau i.bridgeGlobalIndex)
              (A.rootedRightBlockTranslatedSpatialSource R i
                (timeScale + D.commonTailStart i)
                (i.rightRealCoordinates tau) rightTest).1))) := by
  rw [arbitrarySpatialGeneratorCandidate,
    generatorSemigroupCandidate_apply]
  have hleftField :
      D.leftArbitrarySpatialGeneratorField i timeScale leftTest
          (fun a =>
            -star
              (osiiPositiveRealTimeEmbed tau
                (i.leftGlobalIndex a))) =
        osiiPositiveTimeSingleVectorCLM OS ((i.n - 1) + 1)
          (A.rootedLeftBlockTranslatedSpatialSource R i
            (timeScale + D.commonTailStart i)
            (i.leftRealCoordinates tau) leftTest) := by
    simpa [leftArbitrarySpatialGeneratorField,
      GeneratorIndex.leftRealCoordinates,
      osiiPositiveRealTimeEmbed] using
      (D.left i).realEdge
        (D.leftCofinalIndex i timeScale) leftTest
        (i.leftRealCoordinates tau) hleft
  have hrightField :
      D.rightArbitrarySpatialGeneratorField i timeScale rightTest
          (fun b =>
            osiiPositiveRealTimeEmbed tau
              (i.rightGlobalIndex b)) =
        osiiPositiveTimeSingleVectorCLM OS ((i.m - 1) + 1)
          (A.rootedRightBlockTranslatedSpatialSource R i
            (timeScale + D.commonTailStart i)
            (i.rightRealCoordinates tau) rightTest) := by
    simpa [rightArbitrarySpatialGeneratorField,
      GeneratorIndex.rightRealCoordinates,
      osiiPositiveRealTimeEmbed] using
      (D.right i).realEdge
        (D.rightCofinalIndex i timeScale) rightTest
        (i.rightRealCoordinates tau) hright
  rw [hleftField, hrightField]
  exact
    osiiPositiveTimeSingleSemigroupPairing_ofReal_eq_schwinger_all
      OS ((i.n - 1) + 1) ((i.m - 1) + 1)
      (tau i.bridgeGlobalIndex) hbridge
      (A.rootedLeftBlockTranslatedSpatialSource R i
        (timeScale + D.commonTailStart i)
        (i.leftRealCoordinates tau) leftTest)
      (A.rootedRightBlockTranslatedSpatialSource R i
        (timeScale + D.commonTailStart i)
        (i.rightRealCoordinates tau) rightTest)

/-- Root smearing remains inside the semigroup-candidate API for arbitrary
spatial tests.  On a positive real bridge it is the normalized integral of
the unsmeared candidate with only that bridge coordinate translated. -/
theorem rootSmearedArbitrarySpatialGeneratorCandidate_positiveReal_eq_integral
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (timeScale : Nat)
    (leftTest : SchwartzMap
      (Section43SpatialSpace d ((i.n - 1) + 1)) Complex)
    (rightTest : SchwartzMap
      (Section43SpatialSpace d ((i.m - 1) + 1)) Complex)
    (tau : Fin k -> Real)
    (hbridge : 0 < tau i.bridgeGlobalIndex) :
    D.rootSmearedArbitrarySpatialGeneratorCandidate
        lgc i timeScale leftTest rightTest
        (osiiPositiveRealTimeEmbed tau) =
      ∫ t : Real,
        D.semigroupBridgeRootWeight i timeScale t *
          D.arbitrarySpatialGeneratorCandidate
            lgc i timeScale leftTest rightTest
            (osiiPositiveRealTimeEmbed
              (generatorBridgeVariation i tau
                (tau i.bridgeGlobalIndex + t))) := by
  let u : OSHilbertSpace OS :=
    D.leftArbitrarySpatialGeneratorField i timeScale leftTest
      (fun a =>
        -star
          (osiiPositiveRealTimeEmbed tau
            (i.leftGlobalIndex a)))
  let v : OSHilbertSpace OS :=
    D.rightArbitrarySpatialGeneratorField i timeScale rightTest
      (fun b =>
        osiiPositiveRealTimeEmbed tau
          (i.rightGlobalIndex b))
  have hvector :
      Integrable
        (fun t : Real =>
          D.semigroupBridgeRootWeight i timeScale t •
            osTimeShiftHilbertComplex OS lgc
              (((tau i.bridgeGlobalIndex + t : Real)) : Complex) v) := by
    exact
      D.integrable_semigroupBridgeRootWeight_smul_timeShift_add
        lgc i timeScale (tau i.bridgeGlobalIndex) hbridge v
  rw [rootSmearedArbitrarySpatialGeneratorCandidate,
    generatorSemigroupCandidate_apply]
  change
    @inner Complex (OSHilbertSpace OS) _ u
        (osTimeShiftHilbertComplex OS lgc
          ((tau i.bridgeGlobalIndex : Real) : Complex)
          (D.semigroupBridgeRootOperator lgc i timeScale v)) =
      _
  rw [D.osTimeShiftHilbertComplex_semigroupBridgeRootOperator
    lgc i timeScale (tau i.bridgeGlobalIndex) hbridge v]
  calc
    @inner Complex (OSHilbertSpace OS) _ u
        (∫ t : Real,
          D.semigroupBridgeRootWeight i timeScale t •
            osTimeShiftHilbertComplex OS lgc
              (((tau i.bridgeGlobalIndex + t : Real)) : Complex) v)
        =
      ∫ t : Real,
        @inner Complex (OSHilbertSpace OS) _ u
          (D.semigroupBridgeRootWeight i timeScale t •
            osTimeShiftHilbertComplex OS lgc
              (((tau i.bridgeGlobalIndex + t : Real)) : Complex) v) := by
            exact (integral_inner hvector u).symm
    _ =
      ∫ t : Real,
        D.semigroupBridgeRootWeight i timeScale t *
          D.arbitrarySpatialGeneratorCandidate
            lgc i timeScale leftTest rightTest
            (osiiPositiveRealTimeEmbed
              (generatorBridgeVariation i tau
                (tau i.bridgeGlobalIndex + t))) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun t => by
              simp only [inner_smul_right]
              congr 1
              rw [arbitrarySpatialGeneratorCandidate,
                generatorSemigroupCandidate_apply]
              simp only [osiiPositiveRealTimeEmbed,
                generatorBridgeVariation_left,
                generatorBridgeVariation_bridge,
                generatorBridgeVariation_right,
                u, v]

/-- On one real neighborhood, uniformly in packet scale, the full
root-smeared Hermite sum is the affine root-smearing limit based at the
current positive bridge.  This follows by identifying the same finite shells
and using uniqueness of their two limits. -/
theorem
    eventually_rootSmearedSpatialHermiteGeneratorSum_positiveReal_eq_affineRootSmearingLimit_uniform_scale
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k) :
    ∀ᶠ xi : Fin k -> Real in nhds 0,
      forall timeScale : Nat,
      forall hprofiles :
        D.RootedTranslatedTimeProfilesPositive i timeScale xi,
      forall hbridge : 0 < xi i.bridgeGlobalIndex,
      i.leftRealCoordinates xi ∈ (D.left i).realRegion ->
      i.rightRealCoordinates xi ∈ (D.right i).realRegion ->
      forall F : SchwartzMap
        (Section43SpatialSpace d (k + 1)) Complex,
        D.rootSmearedSpatialHermiteGeneratorSum
            lgc i timeScale (osiiPositiveRealTimeEmbed xi) F =
          D.spatialHermiteGeneratorAffineRootSmearingLimit
            i timeScale xi hprofiles (xi i.bridgeGlobalIndex)
            hbridge.le F := by
  filter_upwards
    [D.eventually_tendsto_spatialHermiteGeneratorFiniteShellAffineRootSmearing_uniform_scale
      lgc i] with xi hlimit
  intro timeScale hprofiles hbridge hleft hright F
  let w : OSIITimeGapSpace k := osiiPositiveRealTimeEmbed xi
  have hw : w ∈ generatorSemigroupDomain i
      (D.left i).domain (D.right i).domain := by
    exact positiveRealTimeEmbed_mem_generatorSemigroupDomain
      i xi hbridge
      ((D.left i).realRegion_to_domain
        (i.leftRealCoordinates xi) hleft)
      ((D.right i).realRegion_to_domain
        (i.rightRealCoordinates xi) hright)
  have hsum :
      Tendsto
        (fun shell =>
          D.rootSmearedSpatialHermiteGeneratorFiniteShell
            lgc i timeScale shell w F)
        atTop
        (nhds (D.rootSmearedSpatialHermiteGeneratorSum
          lgc i timeScale w F)) := by
    exact
      (D.tendstoUniformlyOn_rootSmearedSpatialHermiteGeneratorFiniteShell_on_compact
        lgc i timeScale F {w} isCompact_singleton
        (by simpa [Set.singleton_subset_iff] using hw)).tendsto_at
          (Set.mem_singleton w)
  have haffine :
      Tendsto
        (fun shell =>
          D.rootSmearedSpatialHermiteGeneratorFiniteShell
            lgc i timeScale shell w F)
        atTop
        (nhds (D.spatialHermiteGeneratorAffineRootSmearingLimit
          i timeScale xi hprofiles (xi i.bridgeGlobalIndex)
          hbridge.le F)) := by
    rw [show
        (fun shell =>
          D.rootSmearedSpatialHermiteGeneratorFiniteShell
            lgc i timeScale shell w F) =
          (fun shell =>
            D.spatialHermiteGeneratorFiniteShellAffineRootSmearing
              lgc i timeScale shell xi
              (xi i.bridgeGlobalIndex) F) by
        funext shell
        exact
          D.rootSmearedSpatialHermiteGeneratorFiniteShell_positiveReal_eq_affineRootSmearing
            lgc i timeScale shell xi hbridge F]
    exact hlimit timeScale hprofiles hleft hright
      (xi i.bridgeGlobalIndex) hbridge.le F
  exact tendsto_nhds_unique hsum haffine

/-- A pointwise real-edge identification of the unsmeared arbitrary-test
candidate with the split absolute-spatial Schwinger functional passes through
the synchronized middle-root integral. -/
theorem rootSmearedArbitrarySpatialGeneratorCandidate_eq_affineRootSmearingLimit_of_unsmeared
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (timeScale : Nat)
    (leftTest : SchwartzMap
      (Section43SpatialSpace d ((i.n - 1) + 1)) Complex)
    (rightTest : SchwartzMap
      (Section43SpatialSpace d ((i.m - 1) + 1)) Complex)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) Complex)
    (xi : Fin k -> Real)
    (hprofiles : D.RootedTranslatedTimeProfilesPositive i timeScale xi)
    (hbridge : 0 < xi i.bridgeGlobalIndex)
    (hunsmeared : forall (t : Real) (ht : 0 < t),
      D.arbitrarySpatialGeneratorCandidate
          lgc i timeScale leftTest rightTest
          (osiiPositiveRealTimeEmbed
            (generatorBridgeVariation i xi
              (xi i.bridgeGlobalIndex + t))) =
        generatorSplitAbsoluteSpatialSchwingerCLM
          OS i
          (D.rootedLeftTranslatedTimeProfile i timeScale xi)
          hprofiles.1
          (D.rootedRightTranslatedTimeProfile i timeScale xi)
          hprofiles.2
          (D.rootedLeftTranslatedCommonShift i timeScale xi)
          (xi i.bridgeGlobalIndex + t)
          (add_nonneg hbridge.le ht.le)
          (D.rootedLeftTranslatedCommonShift_span i timeScale xi)
          (GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
            (d := d) i F)) :
    D.rootSmearedArbitrarySpatialGeneratorCandidate
        lgc i timeScale leftTest rightTest
        (osiiPositiveRealTimeEmbed xi) =
      D.spatialHermiteGeneratorAffineRootSmearingLimit
        i timeScale xi hprofiles (xi i.bridgeGlobalIndex)
        hbridge.le F := by
  rw [D.rootSmearedArbitrarySpatialGeneratorCandidate_positiveReal_eq_integral
    lgc i timeScale leftTest rightTest xi hbridge]
  unfold spatialHermiteGeneratorAffineRootSmearingLimit
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    by_cases ht : 0 < t
    · change
        D.semigroupBridgeRootWeight i timeScale t *
            D.arbitrarySpatialGeneratorCandidate
              lgc i timeScale leftTest rightTest
              (osiiPositiveRealTimeEmbed
                (generatorBridgeVariation i xi
                  (xi i.bridgeGlobalIndex + t))) =
          D.semigroupBridgeRootWeight i timeScale t *
            (if ht' : 0 < t then
              generatorSplitAbsoluteSpatialSchwingerCLM
                OS i
                (D.rootedLeftTranslatedTimeProfile i timeScale xi)
                hprofiles.1
                (D.rootedRightTranslatedTimeProfile i timeScale xi)
                hprofiles.2
                (D.rootedLeftTranslatedCommonShift i timeScale xi)
                (xi i.bridgeGlobalIndex + t)
                (add_nonneg hbridge.le ht'.le)
                (D.rootedLeftTranslatedCommonShift_span i timeScale xi)
                (GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
                  (d := d) i F)
            else 0)
      rw [dif_pos ht, hunsmeared t ht]
    · obtain ⟨J, _hJ_compact, hJ_positive, hsupport⟩ :=
        D.exists_semigroupBridgeRootWeight_uniformCompactPositiveSupport i
      have hzero : D.semigroupBridgeRootWeight i timeScale t = 0 := by
        by_contra hne
        have ht_support :
            t ∈ tsupport
              (D.semigroupBridgeRootWeight i timeScale : Real -> Complex) :=
          subset_tsupport _
            (by simpa [Function.mem_support] using hne)
        exact ht (hJ_positive (hsupport timeScale ht_support))
      simp [ht, hzero]

/-- Holomorphy of the retained rooted fields promotes the arbitrary
root-smeared product candidate to a holomorphic scalar function on the usual
generator domain. -/
theorem differentiableOn_rootSmearedArbitrarySpatialGeneratorCandidate
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (timeScale : Nat)
    (leftTest : SchwartzMap
      (Section43SpatialSpace d ((i.n - 1) + 1)) Complex)
    (rightTest : SchwartzMap
      (Section43SpatialSpace d ((i.m - 1) + 1)) Complex) :
    DifferentiableOn Complex
      (H.toContinuousTranslationData.rootSmearedArbitrarySpatialGeneratorCandidate
        lgc i timeScale leftTest rightTest)
      (generatorSemigroupDomain i
        (H.left i).domain (H.right i).domain) := by
  let D := H.toContinuousTranslationData
  have hleft :
      DifferentiableOn Complex
        (D.leftArbitrarySpatialGeneratorField i timeScale leftTest)
        (H.left i).domain := by
    simpa [D, leftArbitrarySpatialGeneratorField] using
      (H.left i).field_holomorphic
        (D.leftCofinalIndex i timeScale) leftTest
  have hright :
      DifferentiableOn Complex
        (D.rightArbitrarySpatialGeneratorField i timeScale rightTest)
        (H.right i).domain := by
    simpa [D, rightArbitrarySpatialGeneratorField] using
      (H.right i).field_holomorphic
        (D.rightCofinalIndex i timeScale) rightTest
  have hrightSmeared :
      DifferentiableOn Complex
        (D.rootSmearedRightArbitrarySpatialGeneratorField
          lgc i timeScale rightTest)
        (H.right i).domain := by
    exact
      (D.semigroupBridgeRootOperator lgc i timeScale
        ).differentiable.differentiableOn.comp hright
          (fun _ _ => Set.mem_univ _)
  exact
    differentiableOn_generatorSemigroupCandidate
      OS lgc i (H.left i).domain_open (H.right i).domain_open
      hleft hrightSmeared

/-- Equality of the arbitrary rank-one candidate and the full rooted Hermite
sum on one nonempty open real patch propagates through the whole connected
generator domain.  This is the exact analytic-continuation step needed by the
equation-`(6.29)` target row. -/
theorem rootSmearedArbitrarySpatialGeneratorCandidate_eq_hermiteSum_of_realEdge
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (timeScale : Nat)
    (leftTest : SchwartzMap
      (Section43SpatialSpace d ((i.n - 1) + 1)) Complex)
    (rightTest : SchwartzMap
      (Section43SpatialSpace d ((i.m - 1) + 1)) Complex)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) Complex)
    (V : Set (Fin k -> Real))
    (hV_open : IsOpen V)
    (hV_nonempty : V.Nonempty)
    (hV_domain : forall x, x ∈ V ->
      SCV.realToComplex x ∈ generatorSemigroupDomain i
        (H.left i).domain (H.right i).domain)
    (hreal : forall x, x ∈ V ->
      H.toContinuousTranslationData.rootSmearedArbitrarySpatialGeneratorCandidate
          lgc i timeScale leftTest rightTest (SCV.realToComplex x) =
        H.toContinuousTranslationData.rootSmearedSpatialHermiteGeneratorSum
          lgc i timeScale (SCV.realToComplex x) F)
    (z : OSIITimeGapSpace k)
    (hz : z ∈ generatorSemigroupDomain i
      (H.left i).domain (H.right i).domain) :
    H.toContinuousTranslationData.rootSmearedArbitrarySpatialGeneratorCandidate
        lgc i timeScale leftTest rightTest z =
      H.toContinuousTranslationData.rootSmearedSpatialHermiteGeneratorSum
        lgc i timeScale z F := by
  let D := H.toContinuousTranslationData
  let U := generatorSemigroupDomain i
    (H.left i).domain (H.right i).domain
  let f : OSIITimeGapSpace k -> Complex := fun w =>
    D.rootSmearedArbitrarySpatialGeneratorCandidate
        lgc i timeScale leftTest rightTest w -
      D.rootSmearedSpatialHermiteGeneratorSum
        lgc i timeScale w F
  have hU_open : IsOpen U :=
    isOpen_generatorSemigroupDomain i
      (H.left i).domain_open (H.right i).domain_open
  have hU_convex : Convex Real U :=
    convex_generatorSemigroupDomain i
      (convex_conjugateFieldDomain (H.left i).domain_convex)
      (H.right i).domain_convex
  have hU_nonempty : U.Nonempty := by
    obtain ⟨x, hx⟩ := hV_nonempty
    exact ⟨SCV.realToComplex x, hV_domain x hx⟩
  have hU_connected : IsConnected U :=
    hU_convex.isConnected hU_nonempty
  have hf : DifferentiableOn Complex f U := by
    exact
      (differentiableOn_rootSmearedArbitrarySpatialGeneratorCandidate H
        lgc i timeScale leftTest rightTest).sub
      (H.differentiableOn_rootSmearedSpatialHermiteGeneratorSum
        lgc i timeScale F)
  have hf_zero : forall x, x ∈ V -> f (SCV.realToComplex x) = 0 := by
    intro x hx
    exact sub_eq_zero.mpr (hreal x hx)
  exact sub_eq_zero.mp
    (SCV.identity_theorem_totally_real
      hU_open hU_connected hf hV_open hV_nonempty hV_domain hf_zero z hz)

end RootedA0BlockContinuousTranslationData
end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
