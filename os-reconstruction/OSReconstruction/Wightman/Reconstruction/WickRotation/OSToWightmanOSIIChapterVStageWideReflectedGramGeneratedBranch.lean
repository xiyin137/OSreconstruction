/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageWideReflectedGramTwoScaleFamily
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRootedAnchoredGeneratedBranch
















noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}
  {OS : OsterwalderSchraderAxioms d}
variable {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]

/-- Every reflected-Gram left real-edge point contracts to zero through the
initial Gram polydisc. -/
theorem rootedReflectedGramLeft_real_smul_mem
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (x : Fin (i.n - 1) → ℝ)
    (hx :
      x ∈
        (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
          S depth P A R H).leftRealRegion i)
    (t : ℝ)
    (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    t • SCV.realToComplex x ∈
      (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        S depth P A R H).leftDomain i := by
  rcases i with ⟨n, m, hn, hm, hnm⟩
  by_cases hi : n = 1
  · subst n
    exact Set.mem_univ _
  · cases n with
    | zero => omega
    | succ n =>
      cases n with
      | zero => contradiction
      | succ q =>
        let i : GeneratorIndex k := ⟨q + 2, m, hn, hm, hnm⟩
        let D :=
          rootedLeftNontrivialReflectedGramSpatialSourceData
            S depth P A R i (q := q) rfl
        change
          t • SCV.realToComplex x ∈
            D.reflectedGram.atlas.spatialLinearDomain
        apply
          D.reflectedGram.atlas.initialGramPolydisc_subset_spatialLinearDomain
        have hzero :
            (0 : Fin (q + 1) → ℂ) ∈
              SCV.Polydisc 0
                (fun _ => D.reflectedGram.atlas.gram.gramRadius) :=
          SCV.center_mem_polydisc
            (fun _ => D.reflectedGram.atlas.gram.gramRadius_pos)
        have hxpoly :
            SCV.realToComplex x ∈
              SCV.Polydisc 0
                (fun _ => D.reflectedGram.atlas.gram.gramRadius) :=
          hx.2
        have hcombo :=
          SCV.polydisc_convex hzero hxpoly
            (sub_nonneg.mpr ht1) ht0 (by ring)
        simpa using hcombo

/-- Right-hand form of `rootedReflectedGramLeft_real_smul_mem`. -/
theorem rootedReflectedGramRight_real_smul_mem
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (x : Fin (i.m - 1) → ℝ)
    (hx :
      x ∈
        (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
          S depth P A R H).rightRealRegion i)
    (t : ℝ)
    (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    t • SCV.realToComplex x ∈
      (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        S depth P A R H).rightDomain i := by
  rcases i with ⟨n, m, hn, hm, hnm⟩
  by_cases hi : m = 1
  · subst m
    exact Set.mem_univ _
  · cases m with
    | zero => omega
    | succ m =>
      cases m with
      | zero => contradiction
      | succ q =>
        let i : GeneratorIndex k := ⟨n, q + 2, hn, hm, hnm⟩
        let D :=
          rootedRightNontrivialReflectedGramSpatialSourceData
            S depth P A R i (q := q) rfl
        change
          t • SCV.realToComplex x ∈
            D.reflectedGram.atlas.spatialLinearDomain
        apply
          D.reflectedGram.atlas.initialGramPolydisc_subset_spatialLinearDomain
        have hzero :
            (0 : Fin (q + 1) → ℂ) ∈
              SCV.Polydisc 0
                (fun _ => D.reflectedGram.atlas.gram.gramRadius) :=
          SCV.center_mem_polydisc
            (fun _ => D.reflectedGram.atlas.gram.gramRadius_pos)
        have hxpoly :
            SCV.realToComplex x ∈
              SCV.Polydisc 0
                (fun _ => D.reflectedGram.atlas.gram.gramRadius) :=
          hx.2
        have hcombo :=
          SCV.polydisc_convex hzero hxpoly
            (sub_nonneg.mpr ht1) ht0 (by ring)
        simpa using hcombo

/-- The original-OS common source seed connects to its bridge-only point
through the initial reflected-Gram polydiscs. -/
theorem rootedReflectedGramSeedOfOS_joinedIn_nativeBridgePoint
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k) :
    JoinedIn
      ((rootedReflectedGramRootSmearedGlobalFamilyOfOS
        S depth P A R H).domain i)
      (i.nativeBridgePoint
        ((rootedReflectedGramGeneratorCommonComplexModeGermDataOfOS
          S depth P A R H).center i.bridgeGlobalIndex))
      (osiiPositiveRealTimeEmbed
        (rootedReflectedGramGeneratorCommonComplexModeGermDataOfOS
          S depth P A R H).center) := by
  let E :=
    rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
      S depth P A R H.toContinuousTranslationData
  let Q :=
    rootedReflectedGramGeneratorOpenFieldSourceAgreementData
      S depth P A R H
  let C :=
    rootedReflectedGramGeneratorCommonComplexModeGermDataOfOS
      S depth P A R H
  have hpositive :
      C.center ∈ section43TimeStrictPositiveRegion k :=
    Q.strictPositive_of_mem_commonPositiveRealOfOS
      C.center C.center_mem
  have hleftCenter :
      i.leftRealCoordinates C.center ∈ E.leftRealRegion i :=
    Q.first_leftReal_mem_of_mem_commonPositiveRealOfOS
      i C.center C.center_mem
  have hrightCenter :
      i.rightRealCoordinates C.center ∈ E.rightRealRegion i :=
    Q.first_rightReal_mem_of_mem_commonPositiveRealOfOS
      i C.center C.center_mem
  have hjoin :
      JoinedIn (E.domain i)
        (i.nativeBridgePoint (C.center i.bridgeGlobalIndex))
        (osiiPositiveRealTimeEmbed C.center) := by
    apply E.nativeBridgePoint_joinedIn_positiveReal
      i C.center (hpositive i.bridgeGlobalIndex)
    · intro t ht
      exact
        rootedReflectedGramLeft_real_smul_mem
          S depth P A R H.toContinuousTranslationData
          i (i.leftRealCoordinates C.center) hleftCenter
          t ht.1 ht.2
    · intro t ht
      exact
        rootedReflectedGramRight_real_smul_mem
          S depth P A R H.toContinuousTranslationData
          i (i.rightRealCoordinates C.center) hrightCenter
          t ht.1 ht.2
  change
    JoinedIn (E.domain i)
      (i.nativeBridgePoint (C.center i.bridgeGlobalIndex))
      (osiiPositiveRealTimeEmbed C.center)
  exact hjoin

/-- The common reflected-Gram packet-scale seed is joined to its bridge-only
projection through the initial Gram polydiscs. -/
theorem rootedReflectedGramSeed_joinedIn_nativeBridgePoint
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (lgc : OSLinearGrowthCondition d OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k) :
    JoinedIn
      ((rootedReflectedGramRootSmearedGlobalFamily
        S depth P lgc A R H).domain i)
      (i.nativeBridgePoint
        ((rootedReflectedGramGeneratorCommonComplexModeGermData
          S depth P lgc A R H).center i.bridgeGlobalIndex))
      (osiiPositiveRealTimeEmbed
        (rootedReflectedGramGeneratorCommonComplexModeGermData
          S depth P lgc A R H).center) := by
  let E :=
    rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
      S depth P A R H.toContinuousTranslationData
  let Q :=
    rootedReflectedGramGeneratorOpenFieldSourceAgreementData
      S depth P A R H
  let C :=
    rootedReflectedGramGeneratorCommonComplexModeGermData
      S depth P lgc A R H
  have hpositive :
      C.center ∈ section43TimeStrictPositiveRegion k :=
    Q.strictPositive_of_mem_commonPositiveReal
      lgc C.center C.center_mem
  have hleftCenter :
      i.leftRealCoordinates C.center ∈ E.leftRealRegion i :=
    Q.first_leftReal_mem_of_mem_commonPositiveReal
      lgc i C.center C.center_mem
  have hrightCenter :
      i.rightRealCoordinates C.center ∈ E.rightRealRegion i :=
    Q.first_rightReal_mem_of_mem_commonPositiveReal
      lgc i C.center C.center_mem
  have hjoin :
      JoinedIn (E.domain i)
        (i.nativeBridgePoint (C.center i.bridgeGlobalIndex))
        (osiiPositiveRealTimeEmbed C.center) := by
    apply E.nativeBridgePoint_joinedIn_positiveReal
      i C.center (hpositive i.bridgeGlobalIndex)
    · intro t ht
      exact
        rootedReflectedGramLeft_real_smul_mem
          S depth P A R H.toContinuousTranslationData
          i (i.leftRealCoordinates C.center) hleftCenter
          t ht.1 ht.2
    · intro t ht
      exact
        rootedReflectedGramRight_real_smul_mem
          S depth P A R H.toContinuousTranslationData
          i (i.rightRealCoordinates C.center) hrightCenter
          t ht.1 ht.2
  change
    JoinedIn (E.domain i)
      (i.nativeBridgePoint (C.center i.bridgeGlobalIndex))
      (osiiPositiveRealTimeEmbed C.center)
  exact hjoin

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
