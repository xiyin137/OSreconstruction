import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageWideReflectedGramPacketScaleGlobal
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621RootedProductTargetRow

/-!
# Reflected-Gram packet-scale uniqueness for equation (6.21)

Packet limits formed from arbitrary continuous spatial lifts agree on the
global reflected-Gram branch when the lifted tests have the same reduced
spatial head marginal.  Local packet-limit uniqueness identifies the limits
on the common real seed patch; totally-real holomorphic uniqueness propagates
that equality through the connected global branch.
-/

noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData
namespace RootedA0BlockContinuousTranslationData

variable {d k : Nat} [NeZero d] [NeZero k]
variable {I : Section43ProductTimeApproximateIdentity k}
variable {anchor : Fin k -> Real}
variable {OS : OsterwalderSchraderAxioms d}
variable {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]

/-- Global reflected-Gram packet-scale branch limits depend only on the
reduced spatial head marginal of the lifted test. -/
theorem
    rootedReflectedGramPacketScaleBranchLimitDataOfLift_eq_of_headMarginal_eq
    (S : C)
    (depth : Nat)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (lgc : OSLinearGrowthCondition d OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (liftF liftG :
      SchwartzMap (Section43SpatialSpace d k) Complex →L[Complex]
        SchwartzMap (Section43SpatialSpace d (k + 1)) Complex)
    (chiF chiG : SchwartzMap (Section43SpatialSpace d k) Complex)
    (hhead : section43SpatialHeadMarginal (liftF chiF) =
      section43SpatialHeadMarginal (liftG chiG))
    (z : OSIITimeGapSpace k)
    (hz : z ∈ rootedReflectedGramPacketScaleBranch
      S depth P lgc A R H i) :
    (rootedReflectedGramPacketScaleBranchLimitDataOfLift
        S depth P lgc A R H i liftF chiF).limit z =
      (rootedReflectedGramPacketScaleBranchLimitDataOfLift
        S depth P lgc A R H i liftG chiG).limit z := by
  let BF := rootedReflectedGramPacketScaleBranchLimitDataOfLift
    S depth P lgc A R H i liftF chiF
  let BG := rootedReflectedGramPacketScaleBranchLimitDataOfLift
    S depth P lgc A R H i liftG chiG
  let G := rootedReflectedGramPacketScaleGermData
    S depth P lgc A R H i
  have hseed : ∀ x ∈ G.realSeedRegion,
      BF.limit (SCV.realToComplex x) =
        BG.limit (SCV.realToComplex x) := by
    intro x hx
    rw [BF.seed_eq x hx, BG.seed_eq x hx]
    apply rootedPacketScaleLimit_eq_of_headMarginal_eq
      H lgc i (liftF chiF) (liftG chiG) hhead
    let K := rootedReflectedGramGeneratorCommonComplexModeGermData
      S depth P lgc A R H
    simpa [G, rootedReflectedGramPacketScaleGermData, K] using
      K.ball_subset_second i hx.2
  have hzero :=
    SCV.identity_theorem_totally_real
      (rootedReflectedGramPacketScaleBranch_open
        S depth P lgc A R H i)
      (rootedReflectedGramPacketScaleBranch_connected
        S depth P lgc A R H i)
      (BF.holomorphic.sub BG.holomorphic)
      G.realSeedRegion_open
      G.realSeedRegion_nonempty
      (fun x hx => G.germ_subset_branch hx.2)
      (fun x hx => by simp [hseed x hx])
      z hz
  change BF.limit z = BG.limit z
  exact sub_eq_zero.mp hzero

/-- An arbitrary lifted packet branch agrees with the canonical reduced-test
branch when its spatial head marginal is the canonical test. -/
theorem
    rootedReflectedGramPacketScaleBranchLimitDataOfLift_eq_canonical_of_headMarginal_eq
    (S : C)
    (depth : Nat)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (lgc : OSLinearGrowthCondition d OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (lift : SchwartzMap (Section43SpatialSpace d k) Complex →L[Complex]
      SchwartzMap (Section43SpatialSpace d (k + 1)) Complex)
    (chi chiCanonical : SchwartzMap (Section43SpatialSpace d k) Complex)
    (hhead : section43SpatialHeadMarginal (lift chi) = chiCanonical)
    (z : OSIITimeGapSpace k)
    (hz : z ∈ rootedReflectedGramPacketScaleBranch
      S depth P lgc A R H i) :
    (rootedReflectedGramPacketScaleBranchLimitDataOfLift
        S depth P lgc A R H i lift chi).limit z =
      (rootedReflectedGramPacketScaleBranchLimitData
        S depth P lgc A R H i chiCanonical).limit z := by
  let lift0 := section43SpatialBasepointLiftCLM d k
    (normalizedSpatialBasepointCutoff d).toSchwartz
  let B0 := rootedReflectedGramPacketScaleBranchLimitDataOfLift
    S depth P lgc A R H i lift0 chiCanonical
  let BC := rootedReflectedGramPacketScaleBranchLimitData
    S depth P lgc A R H i chiCanonical
  have hhead0 : section43SpatialHeadMarginal (lift chi) =
      section43SpatialHeadMarginal (lift0 chiCanonical) := by
    rw [hhead]
    exact (section43SpatialHeadMarginal_basepointLift_eq
      (normalizedSpatialBasepointCutoff d) chiCanonical).symm
  have hfirst :=
    rootedReflectedGramPacketScaleBranchLimitDataOfLift_eq_of_headMarginal_eq
      S depth P lgc A R H i lift lift0 chi chiCanonical hhead0 z hz
  have h0 := B0.locallyUniform.tendsto_at hz
  have h0' : Tendsto
      (fun scale =>
        (rootedReflectedGramRootSmearedGlobalFamily
          S depth P lgc A R H).spatialHermiteScalarSum
          lgc (rootedGeneratorSplitSpatialLiftCLM i)
          i scale z chiCanonical)
      atTop (nhds (B0.limit z)) := by
    simpa [B0, lift0, rootedGeneratorSplitSpatialLiftCLM] using h0
  have hcanonical := BC.locallyUniform.tendsto_at hz
  exact hfirst.trans (tendsto_nhds_unique h0' hcanonical)

end RootedA0BlockContinuousTranslationData
end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
