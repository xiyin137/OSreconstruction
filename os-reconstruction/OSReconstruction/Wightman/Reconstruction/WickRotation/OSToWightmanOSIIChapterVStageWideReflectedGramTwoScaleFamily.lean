/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageWideReflectedGramPacketScaleGlobal
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorTwoScaleAssembly










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

/-- The genuine original-OS reflected-Gram two-scale family on its entire
connected source-selected generator branch in split-native coordinates. -/
noncomputable def
    rootedReflectedGramGeneratorNativeTwoScaleApproximationFamilyOfOS
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R) :
    GeneratorSpatialTwoScaleApproximationFamily d k := by
  let B :=
    rootedReflectedGramRootSmearedGlobalFamilyOfOS
      S depth P A R H
  exact {
    domain := fun i =>
      rootedReflectedGramPacketScaleBranchOfOS
        S depth P A R H i
    domain_open := fun i =>
      rootedReflectedGramPacketScaleBranchOfOS_open
        S depth P A R H i
    approximation := fun i timeScale shell z =>
      B.twoScaleApproximationOfOS
        (rootedGeneratorSplitSpatialLiftCLM i)
        i timeScale shell z
    approximation_weaklyHolomorphic := by
      intro i timeScale shell χ
      exact
        (B.twoScaleApproximationOfOS_weaklyHolomorphic
          (rootedGeneratorSplitSpatialLiftCLM i)
          i timeScale shell χ).mono
            (rootedReflectedGramPacketScaleBranchOfOS_subset_domain
              S depth P A R H i)
    scalarLimit := fun i z χ =>
      (rootedReflectedGramPacketScaleBranchLimitDataOfOS
        S depth P A R H i χ).limit z
    locallyUniform := by
      intro i χ
      let Q :=
        rootedReflectedGramPacketScaleBranchLimitDataOfOS
          S depth P A R H i χ
      change TendstoLocallyUniformlyOn
        (fun p : ℕ × ℕ =>
          fun z =>
            B.twoScaleApproximationOfOS
              (rootedGeneratorSplitSpatialLiftCLM i)
              i p.1 p.2 z χ)
        Q.limit atTop
        (rootedReflectedGramPacketScaleBranchOfOS
          S depth P A R H i)
      refine
        tendstoLocallyUniformlyOn_prod_of_first_of_uniform_second
          (F := fun timeScale shell z =>
            B.twoScaleApproximationOfOS
              (rootedGeneratorSplitSpatialLiftCLM i)
              i timeScale shell z χ)
          (G := fun timeScale z =>
            B.spatialHermiteScalarSumOfOS
              (rootedGeneratorSplitSpatialLiftCLM i)
              i timeScale z χ)
          (f := Q.limit)
          (U := rootedReflectedGramPacketScaleBranchOfOS
            S depth P A R H i)
          (rootedReflectedGramPacketScaleBranchOfOS_open
            S depth P A R H i)
          Q.locallyUniform ?_
      intro K hK_domain hK_compact
      exact
        B.tendstoUniformlyOn_twoScaleApproximationOfOS_uniform_scale_on_compact
          (rootedGeneratorSplitSpatialLiftCLM i)
          i χ K hK_compact
          (hK_domain.trans
            (rootedReflectedGramPacketScaleBranchOfOS_subset_domain
              S depth P A R H i))
  }

/-- The genuine original-OS reflected-Gram two-scale family in common
chronological generator coordinates. -/
noncomputable def
    rootedReflectedGramGeneratorTwoScaleApproximationFamilyOfOS
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R) :
    GeneratorSpatialTwoScaleApproximationFamily d k :=
  (rootedReflectedGramGeneratorNativeTwoScaleApproximationFamilyOfOS
    S depth P A R H).precomp
      generatorChronologicalParameterComplexCLE

/-- The reflected-Gram global two-scale family in split-native generator
coordinates. -/
noncomputable def
    rootedReflectedGramGeneratorNativeTwoScaleApproximationFamily
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (lgc : OSLinearGrowthCondition d OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R) :
    GeneratorSpatialTwoScaleApproximationFamily d k := by
  let B :=
    rootedReflectedGramRootSmearedGlobalFamily
      S depth P lgc A R H
  exact {
    domain := fun i =>
      rootedReflectedGramPacketScaleBranch
        S depth P lgc A R H i
    domain_open := fun i =>
      rootedReflectedGramPacketScaleBranch_open
        S depth P lgc A R H i
    approximation := fun i timeScale shell z =>
      B.twoScaleApproximation
        lgc (rootedGeneratorSplitSpatialLiftCLM i)
        i timeScale shell z
    approximation_weaklyHolomorphic := by
      intro i timeScale shell χ
      exact
        (B.twoScaleApproximation_weaklyHolomorphic
          lgc (rootedGeneratorSplitSpatialLiftCLM i)
          i timeScale shell χ).mono
            (rootedReflectedGramPacketScaleBranch_subset_domain
              S depth P lgc A R H i)
    scalarLimit := fun i z χ =>
      (rootedReflectedGramPacketScaleBranchLimitData
        S depth P lgc A R H i χ).limit z
    locallyUniform := by
      intro i χ
      let Q :=
        rootedReflectedGramPacketScaleBranchLimitData
          S depth P lgc A R H i χ
      change TendstoLocallyUniformlyOn
        (fun p : ℕ × ℕ =>
          fun z =>
            B.twoScaleApproximation
              lgc (rootedGeneratorSplitSpatialLiftCLM i)
              i p.1 p.2 z χ)
        Q.limit atTop
        (rootedReflectedGramPacketScaleBranch
          S depth P lgc A R H i)
      refine
        tendstoLocallyUniformlyOn_prod_of_first_of_uniform_second
          (F := fun timeScale shell z =>
            B.twoScaleApproximation
              lgc (rootedGeneratorSplitSpatialLiftCLM i)
              i timeScale shell z χ)
          (G := fun timeScale z =>
            B.spatialHermiteScalarSum
              lgc (rootedGeneratorSplitSpatialLiftCLM i)
              i timeScale z χ)
          (f := Q.limit)
          (U := rootedReflectedGramPacketScaleBranch
            S depth P lgc A R H i)
          (rootedReflectedGramPacketScaleBranch_open
            S depth P lgc A R H i)
          Q.locallyUniform ?_
      intro K hK_domain hK_compact
      exact
        B.tendstoUniformlyOn_twoScaleApproximation_uniform_scale_on_compact
          lgc (rootedGeneratorSplitSpatialLiftCLM i)
          i χ K hK_compact
          (hK_domain.trans
            (rootedReflectedGramPacketScaleBranch_subset_domain
              S depth P lgc A R H i))
  }

/-- The reflected-Gram two-scale family in common chronological
coordinates. -/
noncomputable def
    rootedReflectedGramGeneratorTwoScaleApproximationFamily
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (lgc : OSLinearGrowthCondition d OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R) :
    GeneratorSpatialTwoScaleApproximationFamily d k :=
  (rootedReflectedGramGeneratorNativeTwoScaleApproximationFamily
    S depth P lgc A R H).precomp
      generatorChronologicalParameterComplexCLE

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
