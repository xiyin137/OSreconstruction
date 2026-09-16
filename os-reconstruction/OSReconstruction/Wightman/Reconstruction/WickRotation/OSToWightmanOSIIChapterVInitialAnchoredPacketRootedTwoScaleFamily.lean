/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketRootedPacketScaleNormalFamily
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorTwoScaleAssembly
import OSReconstruction.SCV.SchwartzFiniteSeminormBound











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
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
  {R : TripleConvolutionRootData I}

/-- A chosen original-OS packet-scale Vitali limit, retaining its genuine
distributional Schwinger edge for later split comparison. -/
structure RootedPacketScaleLimitDataOfOS
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) where
  limit : OSIITimeGapSpace k → ℂ
  reducedCurrent : SchwartzNPoint d k →L[ℂ] ℂ
  realRegion : Set (Fin k → ℝ)
  realRegion_open : IsOpen realRegion
  realRegion_nonempty : realRegion.Nonempty
  real_mem :
    ∀ ξ ∈ realRegion,
      osiiPositiveRealTimeEmbed ξ ∈
        generatorSemigroupDomain i
          (H.toContinuousTranslationData.left i).domain
          (H.toContinuousTranslationData.right i).domain
  locallyUniform :
    TendstoLocallyUniformlyOn
      (fun timeScale z =>
        H.toContinuousTranslationData.rootSmearedSpatialHermiteGeneratorSumOfOS
          i timeScale z F)
      limit atTop
      (generatorSemigroupDomain i
        (H.toContinuousTranslationData.left i).domain
        (H.toContinuousTranslationData.right i).domain)
  holomorphic :
    DifferentiableOn ℂ limit
      (generatorSemigroupDomain i
        (H.toContinuousTranslationData.left i).domain
        (H.toContinuousTranslationData.right i).domain)
  real_representation :
    ∀ φ : SchwartzMap (Fin k → ℝ) ℂ,
      SCV.SupportsInOpen
          (φ : (Fin k → ℝ) → ℂ) realRegion →
        ∫ ξ : Fin k → ℝ,
            limit (osiiPositiveRealTimeEmbed ξ) * φ ξ =
          reducedCurrent
            (section43NPointTimeSpatialTensor d k
              (generatorChronologicalPullbackTest i anchor φ)
              (section43SpatialHeadMarginal F))

/-- Compatibility type for the genuine original-OS Vitali limit. -/
abbrev RootedPacketScaleLimitData
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (_lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :=
  RootedPacketScaleLimitDataOfOS H i F

/-- Choose the genuine original-OS rooted packet-scale Vitali limit. -/
noncomputable def rootedPacketScaleLimitDataOfOS
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    RootedPacketScaleLimitDataOfOS H i F := by
  let hexists :=
    H.exists_tendstoLocallyUniformlyOn_rootSmearedSpatialHermiteGeneratorSumOfOS_packetScale
      i F
  let limit := Classical.choose hexists
  let hlimit_exists := Classical.choose_spec hexists
  let L := Classical.choose hlimit_exists
  let hregion_exists := Classical.choose_spec hlimit_exists
  let V := Classical.choose hregion_exists
  have hspec := Classical.choose_spec hregion_exists
  exact {
    limit := limit
    reducedCurrent := L
    realRegion := V
    realRegion_open := hspec.1
    realRegion_nonempty := hspec.2.1
    real_mem := hspec.2.2.1
    locallyUniform := hspec.2.2.2.1
    holomorphic := hspec.2.2.2.2.1
    real_representation := hspec.2.2.2.2.2
  }

/-- Compatibility presentation of the original-OS rooted Vitali limit. -/
noncomputable def rootedPacketScaleLimitData
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (_lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    RootedPacketScaleLimitData H _lgc i F :=
  rootedPacketScaleLimitDataOfOS H i F

/-- The concrete rooted two-scale generator family in split-native
coordinates, built from any canonical rooted block family. The first index
shrinks the anchored packet and the second truncates the block-global spatial
Hermite expansion; neither requires an extra OS growth condition. -/
noncomputable def rootedGeneratorNativeTwoScaleApproximationFamilyOfOS
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    : GeneratorSpatialTwoScaleApproximationFamily d k := by
  let D := H.toContinuousTranslationData
  let lift :
      SchwartzMap (Section43SpatialSpace d k) ℂ →L[ℂ]
        SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ :=
    section43SpatialBasepointLiftCLM d k
      (normalizedSpatialBasepointCutoff d).toSchwartz
  exact {
    domain := fun i =>
      generatorSemigroupDomain i
        (D.left i).domain (D.right i).domain
    domain_open := fun i =>
      isOpen_generatorSemigroupDomain i
        (H.left i).domain_open (H.right i).domain_open
    approximation := fun i timeScale shell z =>
      (D.rootSmearedSpatialHermiteGeneratorFiniteShellOfOS
        i timeScale shell z).comp lift
    approximation_weaklyHolomorphic := by
      intro i timeScale shell χ
      exact
        H.differentiableOn_rootSmearedSpatialHermiteGeneratorFiniteShellOfOS
          i timeScale shell (lift χ)
    scalarLimit := fun i z χ =>
      (rootedPacketScaleLimitDataOfOS H i (lift χ)).limit z
    locallyUniform := by
      intro i χ
      let F := lift χ
      let P := rootedPacketScaleLimitDataOfOS H i F
      change TendstoLocallyUniformlyOn
        (fun p : ℕ × ℕ =>
          fun z =>
            D.rootSmearedSpatialHermiteGeneratorFiniteShellOfOS
              i p.1 p.2 z F)
        P.limit atTop
        (generatorSemigroupDomain i
          (D.left i).domain (D.right i).domain)
      refine
        tendstoLocallyUniformlyOn_prod_of_first_of_uniform_second
          (F := fun timeScale shell z =>
            D.rootSmearedSpatialHermiteGeneratorFiniteShellOfOS
              i timeScale shell z F)
          (G := fun timeScale z =>
            D.rootSmearedSpatialHermiteGeneratorSumOfOS
              i timeScale z F)
          (f := P.limit)
          (U := generatorSemigroupDomain i
            (D.left i).domain (D.right i).domain)
          (isOpen_generatorSemigroupDomain i
            (H.left i).domain_open (H.right i).domain_open)
          P.locallyUniform ?_
      intro K hK_domain hK_compact
      simpa [F, P] using
        D.tendstoUniformlyOn_rootSmearedSpatialHermiteGeneratorFiniteShellOfOS_uniform_scale_on_compact
          i F K hK_compact hK_domain
  }

/-- The rooted two-scale family in common chronological coordinates. Each
split-native chart is precomposed with its chronological sign reflection, so
the positive real point `τ` represents the same physical gap vector for every
generator split, with no additional OS growth premise. -/
noncomputable def rootedGeneratorTwoScaleApproximationFamilyOfOS
    (H : RootedA0BlockHolomorphicTranslationData OS A R) :
    GeneratorSpatialTwoScaleApproximationFamily d k :=
  (rootedGeneratorNativeTwoScaleApproximationFamilyOfOS H).precomp
    generatorChronologicalParameterComplexCLE

/-- Compatibility presentation of the original-OS chronological family. -/
noncomputable def rootedGeneratorTwoScaleApproximationFamily
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (_lgc : OSLinearGrowthCondition d OS) :
    GeneratorSpatialTwoScaleApproximationFamily d k :=
  rootedGeneratorTwoScaleApproximationFamilyOfOS H

/-- The original-OS common-coordinate rooted generator domains are convex. -/
theorem rootedGeneratorTwoScaleApproximationFamilyOfOS_domain_convex
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    :
    ∀ i,
      Convex ℝ
        ((rootedGeneratorTwoScaleApproximationFamilyOfOS H
          ).domain i) := by
  intro i
  let D := H.toContinuousTranslationData
  have hnative :
      Convex ℝ
        (generatorSemigroupDomain i
          (D.left i).domain (D.right i).domain) := by
    apply convex_generatorSemigroupDomain i
    · intro x hx y hy a b ha hb hab
      change star x ∈ (H.left i).domain at hx
      change star y ∈ (H.left i).domain at hy
      change star (a • x + b • y) ∈ (H.left i).domain
      rw [show star (a • x + b • y) =
        a • star x + b • star y by ext j; simp]
      exact (H.left i).domain_convex hx hy ha hb hab
    · exact (H.right i).domain_convex
  change
    Convex ℝ
      (generatorChronologicalParameterComplexCLE i ⁻¹'
        generatorSemigroupDomain i
          (D.left i).domain (D.right i).domain)
  exact
    hnative.linear_preimage
      ((generatorChronologicalParameterComplexCLE i).toContinuousLinearMap
        |>.restrictScalars ℝ).toLinearMap

/-- Compatibility wrapper for original-OS generator-domain convexity. -/
theorem rootedGeneratorTwoScaleApproximationFamily_domain_convex
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (_lgc : OSLinearGrowthCondition d OS) :
    ∀ i,
      Convex ℝ
        ((rootedGeneratorTwoScaleApproximationFamily H _lgc
          ).domain i) :=
  rootedGeneratorTwoScaleApproximationFamilyOfOS_domain_convex H

/-- The original-OS rooted two-scale family on its cofinal diagonal. -/
noncomputable def rootedGeneratorDiagonalApproximationFamilyOfOS
    (H : RootedA0BlockHolomorphicTranslationData OS A R) :
    GeneratorSpatialApproximationFamily d k :=
  (rootedGeneratorTwoScaleApproximationFamilyOfOS H).diagonal

/-- Compatibility presentation of the original-OS diagonal generator. -/
noncomputable def rootedGeneratorDiagonalApproximationFamily
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (_lgc : OSLinearGrowthCondition d OS) :
    GeneratorSpatialApproximationFamily d k :=
  rootedGeneratorDiagonalApproximationFamilyOfOS H

/-- Select the rooted packet shell while keeping its approximate identity and
triple-convolution roots fixed before the anchor.  This coherence is needed
by later recursive estimates whose constants are chosen before the moving
anchor/profile. -/
noncomputable def selectedRootedAnchoredPacketTimeShellFamilyData
    (anchor : Fin k → ℝ)
    (hanchor : anchor ∈ section43TimeStrictPositiveRegion k) :
    RootedAnchoredPacketTimeShellFamilyData (d := d) anchor := by
  let I := fixedTripleConvolutionApproximateIdentity k
  let R := fixedTripleConvolutionRootData k
  let A := Classical.choose
    (exists_anchoredPacketTimeShellFamilyData_zeroTail
      (d := d) I anchor hanchor)
  exact {
    approximateIdentity := I
    roots := R
    packet := A }

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
