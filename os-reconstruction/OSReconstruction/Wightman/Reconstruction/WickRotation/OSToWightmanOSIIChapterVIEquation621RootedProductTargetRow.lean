/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRootedArbitrarySpatialCandidate
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621ProductSpatialApproxIdentity
import OSReconstruction.SCV.DistributionalRepresentationUniqueness
















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

private theorem cast_cast_symm
    {ι : Sort*}
    {α : ι -> Sort*}
    {a b : ι}
    (h : a = b)
    (x : α b) :
    cast (congrArg α h) (cast (congrArg α h.symm) x) = x := by
  subst b
  rfl

private theorem reindex_axisPairTwoBlockTimeSpatialSource_cast
    {n n' m m' : Nat}
    (hn : n = n')
    (hm : m = m')
    (eta1 : SchwartzMap (Fin n -> Real) Complex)
    (chi1 : SchwartzMap (Section43SpatialSpace d n) Complex)
    (eta2 : SchwartzMap (Fin m -> Real) Complex)
    (chi2 : SchwartzMap (Section43SpatialSpace d m) Complex)
    (t : Real) :
    reindexSchwartz
        (d := d)
        (finCongr (congrArg₂ (fun a b => a + b) hn hm))
        (axisPairTwoBlockTimeSpatialSource n m eta1 chi1 eta2 chi2 t) =
      axisPairTwoBlockTimeSpatialSource n' m'
        (cast
          (congrArg (fun q => SchwartzMap (Fin q -> Real) Complex) hn)
          eta1)
        (cast
          (congrArg
            (fun q => SchwartzMap (Section43SpatialSpace d q) Complex)
            hn)
          chi1)
        (cast
          (congrArg (fun q => SchwartzMap (Fin q -> Real) Complex) hm)
          eta2)
        (cast
          (congrArg
            (fun q => SchwartzMap (Section43SpatialSpace d q) Complex)
            hm)
          chi2)
        t := by
  subst n'
  subst m'
  rfl

/-- Express a positive-arity block test in the predecessor-plus-head
cardinality used by the rooted Hilbert fields. -/
noncomputable def positiveBlockSpatialTest
    {n : Nat} (hn : 0 < n)
    (chi : SchwartzMap (Section43SpatialSpace d n) Complex) :
    SchwartzMap (Section43SpatialSpace d ((n - 1) + 1)) Complex :=
  cast
    (congrArg
      (fun q => SchwartzMap (Section43SpatialSpace d q) Complex)
      (Nat.sub_add_cancel hn).symm)
    chi

@[simp] theorem cast_positiveBlockSpatialTest
    {n : Nat} (hn : 0 < n)
    (chi : SchwartzMap (Section43SpatialSpace d n) Complex) :
    cast
        (congrArg
          (fun q => SchwartzMap (Section43SpatialSpace d q) Complex)
          (Nat.sub_add_cancel hn))
        (positiveBlockSpatialTest (d := d) hn chi) =
      chi := by
  exact cast_cast_symm
    (α := fun q => SchwartzMap (Section43SpatialSpace d q) Complex)
    (Nat.sub_add_cancel hn) chi

/-- Once the two rooted block sources have their canonical time-profile
forms, the arbitrary-test semigroup candidate is the native reflected
two-block Schwinger source. -/
theorem arbitrarySpatialGeneratorCandidate_positiveReal_eq_timeProfiles_of_source_eq
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (timeScale : Nat)
    (leftTest : SchwartzMap
      (Section43SpatialSpace d ((i.n - 1) + 1)) Complex)
    (rightTest : SchwartzMap
      (Section43SpatialSpace d ((i.m - 1) + 1)) Complex)
    (leftTestFull : SchwartzMap (Section43SpatialSpace d i.n) Complex)
    (rightTestFull : SchwartzMap (Section43SpatialSpace d i.m) Complex)
    (hleftTest : cast
        (congrArg
          (fun q => SchwartzMap (Section43SpatialSpace d q) Complex)
          (Nat.sub_add_cancel i.hn)) leftTest = leftTestFull)
    (hrightTest : cast
        (congrArg
          (fun q => SchwartzMap (Section43SpatialSpace d q) Complex)
          (Nat.sub_add_cancel i.hm)) rightTest = rightTestFull)
    (tau : Fin k -> Real)
    (hleftSource :
      (A.rootedLeftBlockTranslatedSpatialSource R i
        (timeScale + D.commonTailStart i)
        (i.leftRealCoordinates tau) leftTest).1 =
        section43OrderedPullbackTimeSpatialTensorCLM
          d ((i.n - 1) + 1) leftTest
          (SCV.translateSchwartz
            (fun j => -Fin.cases 0 (i.leftRealCoordinates tau) j)
            ((A.rootedLeftBlockApproximateIdentity R i).translatedSource
              (A.rootedLeftBlockAnchor i)
              (A.rootedLeftBlockAnchor_positive i)
              (timeScale + D.commonTailStart i)).f))
    (hrightSource :
      (A.rootedRightBlockTranslatedSpatialSource R i
        (timeScale + D.commonTailStart i)
        (i.rightRealCoordinates tau) rightTest).1 =
        section43OrderedPullbackTimeSpatialTensorCLM
          d ((i.m - 1) + 1) rightTest
          (SCV.translateSchwartz
            (fun j => -Fin.cases 0 (i.rightRealCoordinates tau) j)
            ((A.rootedRightBlockApproximateIdentity R i).translatedSource
              (A.rootedRightBlockAnchor i)
              (A.rootedRightBlockAnchor_positive i)
              (timeScale + D.commonTailStart i)).f))
    (hbridge : 0 < tau i.bridgeGlobalIndex)
    (hleft : i.leftRealCoordinates tau ∈ (D.left i).realRegion)
    (hright : i.rightRealCoordinates tau ∈ (D.right i).realRegion) :
    D.arbitrarySpatialGeneratorCandidate
        lgc i timeScale leftTest rightTest
        (osiiPositiveRealTimeEmbed tau) =
      OS.S (i.n + i.m)
        (ZeroDiagonalSchwartz.ofClassical
          (axisPairTwoBlockTimeSpatialSource i.n i.m
            (D.rootedLeftTranslatedTimeProfile i timeScale tau)
            leftTestFull
            (D.rootedRightTranslatedTimeProfile i timeScale tau)
            rightTestFull
            (tau i.bridgeGlobalIndex))) := by
  rw [D.arbitrarySpatialGeneratorCandidate_positiveReal_eq_schwinger
    lgc i timeScale leftTest rightTest tau hbridge hleft hright,
    hleftSource, hrightSource]
  let hn := Nat.sub_add_cancel i.hn
  let hm := Nat.sub_add_cancel i.hm
  have hleftTime :
      cast
          (congrArg (fun q => SchwartzMap (Fin q -> Real) Complex) hn)
          (SCV.translateSchwartz
            (fun j => -Fin.cases 0 (i.leftRealCoordinates tau) j)
            ((A.rootedLeftBlockApproximateIdentity R i).translatedSource
              (A.rootedLeftBlockAnchor i)
              (A.rootedLeftBlockAnchor_positive i)
              (timeScale + D.commonTailStart i)).f) =
        D.rootedLeftTranslatedTimeProfile i timeScale tau := by
    rw [D.rootedLeftBlock_translatedTimeProfile_f]
    exact (D.rootedLeftTranslatedTimeProfile_eq_cast_prepend
      i timeScale tau).symm
  have hrightTime :
      cast
          (congrArg (fun q => SchwartzMap (Fin q -> Real) Complex) hm)
          (SCV.translateSchwartz
            (fun j => -Fin.cases 0 (i.rightRealCoordinates tau) j)
            ((A.rootedRightBlockApproximateIdentity R i).translatedSource
              (A.rootedRightBlockAnchor i)
              (A.rootedRightBlockAnchor_positive i)
              (timeScale + D.commonTailStart i)).f) =
        D.rootedRightTranslatedTimeProfile i timeScale tau := by
    rw [D.rootedRightBlock_translatedTimeProfile_f]
    exact (D.rootedRightTranslatedTimeProfile_eq_cast_prepend
      i timeScale tau).symm
  have hsource :
      reindexSchwartz
          (d := d)
          (finCongr (congrArg₂ (fun a b => a + b) hn hm))
          (axisPairTwoBlockTimeSpatialSource
            ((i.n - 1) + 1) ((i.m - 1) + 1)
            (SCV.translateSchwartz
              (fun j => -Fin.cases 0 (i.leftRealCoordinates tau) j)
              ((A.rootedLeftBlockApproximateIdentity R i).translatedSource
                (A.rootedLeftBlockAnchor i)
                (A.rootedLeftBlockAnchor_positive i)
                (timeScale + D.commonTailStart i)).f)
            leftTest
            (SCV.translateSchwartz
              (fun j => -Fin.cases 0 (i.rightRealCoordinates tau) j)
              ((A.rootedRightBlockApproximateIdentity R i).translatedSource
                (A.rootedRightBlockAnchor i)
                (A.rootedRightBlockAnchor_positive i)
                (timeScale + D.commonTailStart i)).f)
            rightTest
            (tau i.bridgeGlobalIndex)) =
        axisPairTwoBlockTimeSpatialSource i.n i.m
          (D.rootedLeftTranslatedTimeProfile i timeScale tau) leftTestFull
          (D.rootedRightTranslatedTimeProfile i timeScale tau) rightTestFull
          (tau i.bridgeGlobalIndex) := by
    rw [reindex_axisPairTwoBlockTimeSpatialSource_cast
      (d := d) hn hm, hleftTime, hleftTest, hrightTime, hrightTest]
  exact
    osiiSchwinger_ofClassical_eq_of_reindex_finCongr
      OS (congrArg₂ (fun a b => a + b) hn hm) _ _ hsource

/-- An exact rank-one split of a full spatial test identifies its arbitrary
rooted candidate with the full rooted Hermite sum on one real neighborhood,
uniformly in packet scale. -/
theorem eventually_rootSmearedArbitrarySpatialGeneratorCandidate_eq_hermiteSum_of_split
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (leftTestFull : SchwartzMap (Section43SpatialSpace d i.n) Complex)
    (rightTestFull : SchwartzMap (Section43SpatialSpace d i.m) Complex)
    (targetFull : SchwartzMap (Section43SpatialSpace d (k + 1)) Complex)
    (hsplit : generatorSplitSpatialPullbackCLM (d := d) i targetFull =
      section43TwoBlockSpatialProduct leftTestFull rightTestFull) :
    ∀ᶠ xi : Fin k -> Real in nhds 0,
      forall timeScale : Nat,
      forall hprofiles : D.RootedTranslatedTimeProfilesPositive i timeScale xi,
      forall hbridge : 0 < xi i.bridgeGlobalIndex,
      i.leftRealCoordinates xi ∈ (D.left i).realRegion ->
      i.rightRealCoordinates xi ∈ (D.right i).realRegion ->
        D.rootSmearedArbitrarySpatialGeneratorCandidate
            lgc i timeScale
            (positiveBlockSpatialTest (d := d) i.hn leftTestFull)
            (positiveBlockSpatialTest (d := d) i.hm rightTestFull)
            (osiiPositiveRealTimeEmbed xi) =
          D.rootSmearedSpatialHermiteGeneratorSum
            lgc i timeScale (osiiPositiveRealTimeEmbed xi)
            (GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPullbackCLM
              (d := d) i targetFull) := by
  let leftTest := positiveBlockSpatialTest (d := d) i.hn leftTestFull
  let rightTest := positiveBlockSpatialTest (d := d) i.hm rightTestFull
  filter_upwards
    [(GeneratorHermiteHilbertFieldFamilyData.tendsto_leftRealCoordinates_zero i).eventually
      (D.eventually_rootedLeftBlockTranslatedSpatialSource_coe_eq_timeProfile_uniform_scale_test
        i leftTest),
    (GeneratorHermiteHilbertFieldFamilyData.tendsto_rightRealCoordinates_zero i).eventually
      (D.eventually_rootedRightBlockTranslatedSpatialSource_coe_eq_timeProfile_uniform_scale_test
        i rightTest),
    D.eventually_rootSmearedSpatialHermiteGeneratorSum_positiveReal_eq_affineRootSmearingLimit_uniform_scale
      lgc i]
      with xi hleftSource hrightSource hhermite
  intro timeScale hprofiles hbridge hleft hright
  apply (D.rootSmearedArbitrarySpatialGeneratorCandidate_eq_affineRootSmearingLimit_of_unsmeared
    lgc i timeScale leftTest rightTest
    (GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPullbackCLM
      (d := d) i targetFull)
    xi hprofiles hbridge ?_).trans
  · exact (hhermite timeScale hprofiles hbridge hleft hright _).symm
  · intro t ht
    let tau := generatorBridgeVariation i xi (xi i.bridgeGlobalIndex + t)
    have htauBridge : tau i.bridgeGlobalIndex = xi i.bridgeGlobalIndex + t :=
      generatorBridgeVariation_bridge i xi (xi i.bridgeGlobalIndex + t)
    have hcandidate :=
      D.arbitrarySpatialGeneratorCandidate_positiveReal_eq_timeProfiles_of_source_eq
        lgc i timeScale leftTest rightTest leftTestFull rightTestFull
        (by simpa [leftTest] using
          cast_positiveBlockSpatialTest (d := d) i.hn leftTestFull)
        (by simpa [rightTest] using
          cast_positiveBlockSpatialTest (d := d) i.hm rightTestFull)
        tau
        (by simpa [tau] using hleftSource timeScale)
        (by simpa [tau] using hrightSource timeScale)
        (by rw [htauBridge]; exact add_pos hbridge ht)
        (by simpa [tau] using hleft)
        (by simpa [tau] using hright)
    rw [htauBridge] at hcandidate
    rw [hcandidate]
    have habsolute :=
      axisPairTwoBlockTimeSpatialSource_schwinger_eq_absoluteSpatial_of_pullback
        (OS := OS) i
        (D.rootedLeftTranslatedTimeProfile i timeScale xi) hprofiles.1 leftTestFull
        (D.rootedRightTranslatedTimeProfile i timeScale xi) hprofiles.2 rightTestFull
        (D.rootedLeftTranslatedCommonShift i timeScale xi)
        (xi i.bridgeGlobalIndex + t) (add_pos hbridge ht)
        (D.rootedLeftTranslatedCommonShift_span i timeScale xi)
        targetFull hsplit
    simpa [tau, rootedLeftTranslatedTimeProfile,
      rootedRightTranslatedTimeProfile, rootedLeftTranslatedCommonShift] using habsolute

/-- The real-patch identity propagates to every point of the connected
generator semigroup domain. -/
theorem rootSmearedArbitrarySpatialGeneratorCandidate_eq_hermiteSum_of_split
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (leftTestFull : SchwartzMap (Section43SpatialSpace d i.n) Complex)
    (rightTestFull : SchwartzMap (Section43SpatialSpace d i.m) Complex)
    (targetFull : SchwartzMap (Section43SpatialSpace d (k + 1)) Complex)
    (hsplit : generatorSplitSpatialPullbackCLM (d := d) i targetFull =
      section43TwoBlockSpatialProduct leftTestFull rightTestFull)
    (timeScale : Nat)
    (z : OSIITimeGapSpace k)
    (hz : z ∈ generatorSemigroupDomain i
      (H.left i).domain (H.right i).domain) :
    H.toContinuousTranslationData.rootSmearedArbitrarySpatialGeneratorCandidate
        lgc i timeScale
        (positiveBlockSpatialTest (d := d) i.hn leftTestFull)
        (positiveBlockSpatialTest (d := d) i.hm rightTestFull) z =
      H.toContinuousTranslationData.rootSmearedSpatialHermiteGeneratorSum
        lgc i timeScale z
        (GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPullbackCLM
          (d := d) i targetFull) := by
  let D := H.toContinuousTranslationData
  let leftTest := positiveBlockSpatialTest (d := d) i.hn leftTestFull
  let rightTest := positiveBlockSpatialTest (d := d) i.hm rightTestFull
  have heq :=
    D.eventually_rootSmearedArbitrarySpatialGeneratorCandidate_eq_hermiteSum_of_split
      lgc i leftTestFull rightTestFull targetFull hsplit
  have hprofiles :=
    D.eventually_rootedTranslatedTimeProfilesPositive_uniform_scale i
  have hleft :=
    (GeneratorHermiteHilbertFieldFamilyData.tendsto_leftRealCoordinates_zero i
      ).eventually (D.left i).realRegion_nhds
  have hright :=
    (GeneratorHermiteHilbertFieldFamilyData.tendsto_rightRealCoordinates_zero i
      ).eventually (D.right i).realRegion_nhds
  have hgood :
      {xi : Fin k -> Real |
        D.RootedTranslatedTimeProfilesPositive i timeScale xi ∧
        i.leftRealCoordinates xi ∈ (D.left i).realRegion ∧
        i.rightRealCoordinates xi ∈ (D.right i).realRegion ∧
        (0 < xi i.bridgeGlobalIndex ->
          D.rootSmearedArbitrarySpatialGeneratorCandidate
              lgc i timeScale leftTest rightTest
              (osiiPositiveRealTimeEmbed xi) =
            D.rootSmearedSpatialHermiteGeneratorSum
              lgc i timeScale (osiiPositiveRealTimeEmbed xi)
              (GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPullbackCLM
                (d := d) i targetFull))} ∈ nhds 0 := by
    filter_upwards [hprofiles, hleft, hright, heq]
      with xi hp hl hr heq_xi
    exact ⟨hp timeScale, hl, hr,
      fun hb => heq_xi timeScale (hp timeScale) hb hl hr⟩
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp hgood
  let xi0 : Fin k -> Real :=
    fun j => if j = i.toGap then epsilon / 2 else 0
  have hxi0_norm : ‖xi0‖ < epsilon := by
    rw [pi_norm_lt_iff hepsilon]
    intro j
    by_cases hj : j = i.toGap
    · subst j
      simp only [xi0, if_pos]
      rw [Real.norm_eq_abs, abs_of_pos (half_pos hepsilon)]
      linarith
    · simpa [xi0, hj] using hepsilon
  have hxi0_ball : xi0 ∈ Metric.ball (0 : Fin k -> Real) epsilon := by
    simpa [Metric.mem_ball, dist_zero_right] using hxi0_norm
  let V : Set (Fin k -> Real) :=
    Metric.ball (0 : Fin k -> Real) epsilon ∩
      {xi | 0 < xi i.bridgeGlobalIndex}
  have hV_open : IsOpen V := by
    exact Metric.isOpen_ball.inter
      (isOpen_lt continuous_const
        (continuous_apply i.bridgeGlobalIndex))
  have hxi0_bridge : 0 < xi0 i.bridgeGlobalIndex := by
    rw [GeneratorIndex.bridgeGlobalIndex_eq_toGap]
    simp [xi0, hepsilon]
  have hV_nonempty : V.Nonempty :=
    ⟨xi0, hxi0_ball, hxi0_bridge⟩
  have hV_domain : forall xi, xi ∈ V ->
      SCV.realToComplex xi ∈ generatorSemigroupDomain i
        (H.left i).domain (H.right i).domain := by
    intro xi hxi
    have hprops := hball hxi.1
    simpa [SCV.realToComplex, osiiPositiveRealTimeEmbed] using
      (positiveRealTimeEmbed_mem_generatorSemigroupDomain
        i xi hxi.2
        ((D.left i).realRegion_to_domain
          (i.leftRealCoordinates xi) hprops.2.1)
        ((D.right i).realRegion_to_domain
          (i.rightRealCoordinates xi) hprops.2.2.1))
  have hreal : forall xi, xi ∈ V ->
      D.rootSmearedArbitrarySpatialGeneratorCandidate
          lgc i timeScale leftTest rightTest (SCV.realToComplex xi) =
        D.rootSmearedSpatialHermiteGeneratorSum
          lgc i timeScale (SCV.realToComplex xi)
          (GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPullbackCLM
            (d := d) i targetFull) := by
    intro xi hxi
    have hprops := hball hxi.1
    simpa [SCV.realToComplex, osiiPositiveRealTimeEmbed] using
      hprops.2.2.2 hxi.2
  exact
    rootSmearedArbitrarySpatialGeneratorCandidate_eq_hermiteSum_of_realEdge
      H lgc i timeScale leftTest rightTest
      (GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPullbackCLM
        (d := d) i targetFull)
      V hV_open hV_nonempty hV_domain hreal z hz

/-- The full root-smeared Hermite sum is linear in its absolute spatial test.
This is proved from the finite shells, avoiding a separate summability API for
the defining series. -/
theorem rootSmearedSpatialHermiteGeneratorSum_sub
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (timeScale : Nat)
    (z : OSIITimeGapSpace k)
    (hz : z ∈ generatorSemigroupDomain i
      (H.left i).domain (H.right i).domain)
    (F G : SchwartzMap (Section43SpatialSpace d (k + 1)) Complex) :
    H.toContinuousTranslationData.rootSmearedSpatialHermiteGeneratorSum
        lgc i timeScale z (F - G) =
      H.toContinuousTranslationData.rootSmearedSpatialHermiteGeneratorSum
          lgc i timeScale z F -
        H.toContinuousTranslationData.rootSmearedSpatialHermiteGeneratorSum
          lgc i timeScale z G := by
  let D := H.toContinuousTranslationData
  let K : Set (OSIITimeGapSpace k) := {z}
  have hK_compact : IsCompact K := isCompact_singleton
  have hK_domain : K ⊆ generatorSemigroupDomain i
      (D.left i).domain (D.right i).domain := by
    simpa [K] using hz
  have hF :=
    (D.tendstoUniformlyOn_rootSmearedSpatialHermiteGeneratorFiniteShell_on_compact
      lgc i timeScale F K hK_compact hK_domain).tendsto_at
        (Set.mem_singleton z)
  have hG :=
    (D.tendstoUniformlyOn_rootSmearedSpatialHermiteGeneratorFiniteShell_on_compact
      lgc i timeScale G K hK_compact hK_domain).tendsto_at
        (Set.mem_singleton z)
  have hFG :=
    (D.tendstoUniformlyOn_rootSmearedSpatialHermiteGeneratorFiniteShell_on_compact
      lgc i timeScale (F - G) K hK_compact hK_domain).tendsto_at
        (Set.mem_singleton z)
  have hsub : Tendsto
      (fun shell =>
        D.rootSmearedSpatialHermiteGeneratorFiniteShell
            lgc i timeScale shell z F -
          D.rootSmearedSpatialHermiteGeneratorFiniteShell
            lgc i timeScale shell z G)
      atTop
      (nhds
        (D.rootSmearedSpatialHermiteGeneratorSum lgc i timeScale z F -
          D.rootSmearedSpatialHermiteGeneratorSum lgc i timeScale z G)) :=
    hF.sub hG
  have hsub' : Tendsto
      (fun shell =>
        D.rootSmearedSpatialHermiteGeneratorFiniteShell
          lgc i timeScale shell z (F - G))
      atTop
      (nhds
        (D.rootSmearedSpatialHermiteGeneratorSum lgc i timeScale z F -
          D.rootSmearedSpatialHermiteGeneratorSum lgc i timeScale z G)) := by
    apply hsub.congr'
    filter_upwards with shell
    simp [RootedA0BlockContinuousTranslationData.rootSmearedSpatialHermiteGeneratorFiniteShell_apply,
      map_sub]
  exact tendsto_nhds_unique hFG hsub'

/-- The selected packet-scale limit depends only on the reduced spatial head
marginal.  In particular, changing the normalized absolute basepoint cutoff
does not change the represented reduced stage.

The proof subtracts the two full Hermite families.  Their packet limit has
zero distributional trace on its real patch, hence vanishes there by
distributional uniqueness and throughout the connected generator domain by
totally-real holomorphic uniqueness. -/
theorem rootedPacketScaleLimit_eq_of_headMarginal_eq
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (F G : SchwartzMap (Section43SpatialSpace d (k + 1)) Complex)
    (hhead : section43SpatialHeadMarginal F =
      section43SpatialHeadMarginal G)
    (z : OSIITimeGapSpace k)
    (hz : z ∈ generatorSemigroupDomain i
      (H.left i).domain (H.right i).domain) :
    (rootedPacketScaleLimitData H lgc i F).limit z =
      (rootedPacketScaleLimitData H lgc i G).limit z := by
  let D := H.toContinuousTranslationData
  let U := generatorSemigroupDomain i
    (H.left i).domain (H.right i).domain
  let PF := rootedPacketScaleLimitData H lgc i F
  let PG := rootedPacketScaleLimitData H lgc i G
  let P0 := rootedPacketScaleLimitData H lgc i (F - G)
  have hsubLimit : PF.limit z - PG.limit z = P0.limit z := by
    have hF := PF.locallyUniform.tendsto_at hz
    have hG := PG.locallyUniform.tendsto_at hz
    have h0 := P0.locallyUniform.tendsto_at hz
    have hsub : Tendsto
        (fun timeScale =>
          D.rootSmearedSpatialHermiteGeneratorSum lgc i timeScale z F -
            D.rootSmearedSpatialHermiteGeneratorSum lgc i timeScale z G)
        atTop (nhds (PF.limit z - PG.limit z)) := hF.sub hG
    have hsub' : Tendsto
        (fun timeScale =>
          D.rootSmearedSpatialHermiteGeneratorSum
            lgc i timeScale z (F - G))
        atTop (nhds (PF.limit z - PG.limit z)) := by
      apply hsub.congr'
      filter_upwards with timeScale
      exact (rootSmearedSpatialHermiteGeneratorSum_sub
        H lgc i timeScale z hz F G).symm
    exact tendsto_nhds_unique hsub' h0
  have hU_open : IsOpen U :=
    isOpen_generatorSemigroupDomain i
      (H.left i).domain_open (H.right i).domain_open
  have hU_convex : Convex Real U :=
    convex_generatorSemigroupDomain i
      (convex_conjugateFieldDomain (H.left i).domain_convex)
      (H.right i).domain_convex
  have hU_nonempty : U.Nonempty := ⟨z, hz⟩
  have hU_connected : IsConnected U :=
    hU_convex.isConnected hU_nonempty
  let g : (Fin k -> Real) -> Complex :=
    fun x => P0.limit (SCV.realToComplex x)
  have hg_cont : ContinuousOn g P0.realRegion := by
    exact P0.holomorphic.continuousOn.comp
      (continuous_pi fun j =>
        Complex.continuous_ofReal.comp (continuous_apply j)).continuousOn
      P0.real_mem
  have hg_zero : Set.EqOn g 0 P0.realRegion := by
    apply SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn
      P0.realRegion_open hg_cont continuousOn_const
    intro phi hphi_compact hphi_support
    have hrep := P0.real_representation phi
      ⟨hphi_compact, hphi_support⟩
    have hhead0 : section43SpatialHeadMarginal (F - G) = 0 := by
      calc
        section43SpatialHeadMarginal (F - G) =
            section43SpatialHeadMarginalCLM d k (F - G) :=
          (section43SpatialHeadMarginalCLM_apply d k (F - G)).symm
        _ = section43SpatialHeadMarginalCLM d k F -
              section43SpatialHeadMarginalCLM d k G := map_sub _ F G
        _ = section43SpatialHeadMarginal F -
              section43SpatialHeadMarginal G := by
          rw [section43SpatialHeadMarginalCLM_apply,
            section43SpatialHeadMarginalCLM_apply]
        _ = 0 := by rw [hhead, sub_self]
    have hrep_zero :
        (∫ x : Fin k -> Real,
          P0.limit (osiiPositiveRealTimeEmbed x) * phi x) = 0 := by
      rw [hrep, hhead0]
      have htensor :
          section43NPointTimeSpatialTensor d k
              (generatorChronologicalPullbackTest i anchor phi) 0 = 0 := by
        ext q
        simp [section43NPointTimeSpatialTensor_apply]
      rw [htensor, map_zero]
    calc
      (∫ x : Fin k -> Real, g x * phi x) =
          ∫ x : Fin k -> Real,
            P0.limit (osiiPositiveRealTimeEmbed x) * phi x := by
        rfl
      _ = 0 := hrep_zero
      _ = ∫ x : Fin k -> Real, (0 : Complex) * phi x := by simp
  have hP0_zero : P0.limit z = 0 := by
    exact SCV.identity_theorem_totally_real
      hU_open hU_connected P0.holomorphic
      P0.realRegion_open P0.realRegion_nonempty P0.real_mem
      (fun x hx => hg_zero hx) z hz
  exact sub_eq_zero.mp (hsubLimit.trans hP0_zero)

/-- The full absolute product probe whose reduced tail is the mixed target
probe in equation `(6.21)`. -/
noncomputable def absoluteProductTargetFullSpatialTest
    (P : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (x : Fin (k * d) -> Real)
    (N : Nat) :
    SchwartzMap (Section43SpatialSpace d (k + 1)) Complex :=
  section43SpatialBasepointLiftCLM d k
    (P.absoluteProductSpatialBasepointCutoff N).toSchwartz
    (P.absoluteProductTargetSpatialApproxIdentity.section43Probe x N)

/-- Left reflected block of the coherent absolute-product target probe. -/
noncomputable def absoluteProductTargetLeftSpatialTest
    (P : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real)
    (N : Nat) :
    SchwartzMap (Section43SpatialSpace d i.n) Complex :=
  section43SpatialProductCMM d i.n fun a =>
    (P.translatedSpatialParticleFactor
      (prependZeroSpatialPoint d k x) N (i.leftAbsoluteIndex a)).conj

/-- Right block of the coherent absolute-product target probe. -/
noncomputable def absoluteProductTargetRightSpatialTest
    (P : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real)
    (N : Nat) :
    SchwartzMap (Section43SpatialSpace d i.m) Complex :=
  section43SpatialProductCMM d i.m fun b =>
    P.translatedSpatialParticleFactor
      (prependZeroSpatialPoint d k x) N (i.rightAbsoluteIndex b)

/-- Hermite-chart pullback of the full coherent target probe. -/
noncomputable def absoluteProductTargetHermiteSpatialTest
    (P : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real)
    (N : Nat) :
    SchwartzMap (Section43SpatialSpace d (k + 1)) Complex :=
  GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPullbackCLM
    (d := d) i (absoluteProductTargetFullSpatialTest P x N)

/-- The split chart turns the coherent full target into the exact reflected
left/right block product. -/
theorem generatorSplitSpatialPullback_absoluteProductTargetFullSpatialTest
    (P : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real)
    (N : Nat) :
    generatorSplitSpatialPullbackCLM (d := d) i
        (absoluteProductTargetFullSpatialTest P x N) =
      section43TwoBlockSpatialProduct
        (absoluteProductTargetLeftSpatialTest P i x N)
        (absoluteProductTargetRightSpatialTest P i x N) := by
  simpa [absoluteProductTargetFullSpatialTest,
    absoluteProductTargetLeftSpatialTest,
    absoluteProductTargetRightSpatialTest] using
    P.generatorSplitSpatialPullback_absoluteProduct_targetProbe_eq_twoBlock
      i x N

end RootedA0BlockContinuousTranslationData
end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
