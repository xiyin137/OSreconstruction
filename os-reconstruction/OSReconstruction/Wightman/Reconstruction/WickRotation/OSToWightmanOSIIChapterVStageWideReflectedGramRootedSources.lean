/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageWideReflectedGramRealization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRootedAnchoredSpatialSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVTranslatedAnchoredSpatialGrowth
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorOpenFieldRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRootedAnchoredSpatialGrowth
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRootedAnchoredSpatialAgreement




















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction

open OSIIAxisPairSourcewiseFlatCrossData.GaussianCMMFamily

namespace OSIIChapterV

variable {d : ℕ} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}
variable {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]

/-- The carrier-local reflected-Gram source object used by the rooted
analytic construction.

It deliberately contains no logarithmic-domain predicate.  Such coverage is
proved separately by the generated or strict-rank package that selected the
atlas. -/
structure ReflectedGramSpatialSourceData
    (S : C)
    (q : ℕ) where
  carrier : Set (Fin ((q + 1) + 1) → ℝ)
  carrier_compact : IsCompact carrier
  carrier_positive :
    carrier ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1)
  reflectedGram : ReflectedGramAtlasData (OS := OS) S q carrier
  sourceCLM :
    ℕ →
      SchwartzMap
          (Section43SpatialSpace d ((q + 1) + 1)) ℂ →L[ℂ]
        UniformCompactTimeSource d ((q + 1) + 1) carrier

namespace ReflectedGramSpatialSourceData

variable
  {S : C}
  {q : ℕ}

/-- The carrier-local reflected Gram source is represented on the current
simultaneous stage at the exact reflected-pair arity. -/
theorem sourceStage_eq_currentReflectedStage
    (D : ReflectedGramSpatialSourceData (OS := OS) S q) :
    D.reflectedGram.atlas.sourceStage.stage =
      CanonicalGeneratorStageLevelProvider.stage
        (OS := OS) S ((q + 1) + ((q + 1) + 1)) := by
  simpa [
    CanonicalGeneratorStageLevelProvider.stage,
    SimultaneousTimeContinuationStageLevel.reflectedPairStage] using
      D.reflectedGram.atlas.sourceStage_eq

/-- Package a translated product source family as one source-realized open
Hilbert block.  This is the analytic core shared by full generated and
strict-rank coverage. -/
noncomputable def toOpenFieldScaleBlockRealEdgeData
    (D : ReflectedGramSpatialSourceData (OS := OS) S q)
    (I :
      Section43ProductTimeApproximateIdentity ((q + 1) + 1))
    (τ : Fin ((q + 1) + 1) → ℝ)
    (hτ :
      τ ∈ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hsource :
      ∀ scale χ,
        UniformCompactTimeSource.source (D.sourceCLM scale χ) =
          I.translatedPositiveTimeSpatialSource τ hτ χ scale)
    (modeTest :
      ℕ →
        SchwartzMap
          (Section43SpatialSpace d ((q + 1) + 1)) ℂ)
    (βs : ℕ → Fin ((q + 1) + 1) → ℕ)
    (hβ : ∃ C > 0, ∃ p : ℕ, ∀ r a,
      (βs r a : ℝ) ≤ C * (1 + (r : ℝ)) ^ p)
    (hmode :
      ∀ r,
        modeTest r =
          (section43SpatialSchwartzParticleCLE
            d ((q + 1) + 1)).symm
            (SchwartzMap.productTensor fun a =>
              complexifyRealSchwartz
                (GaussianField.DyninMityaginSpace.basis
                  (E := SchwartzMap (Fin d → ℝ) ℝ)
                  (βs r a)))) :
    GeneratorOpenHilbertFieldScaleBlockRealEdgeData
      OS ((q + 1) + 1) (q + 1) where
  domain := D.reflectedGram.atlas.spatialLinearDomain
  domain_open := D.reflectedGram.atlas.spatialLinearDomain_open
  field := fun scale mode z =>
    D.reflectedGram.atlas.gram.anchoredAtlasField
      D.reflectedGram.atlas.sourceStage.stage
      D.reflectedGram.atlas.sourceStage.germ
      (D.sourceCLM scale (modeTest mode)) z
  field_holomorphic := by
    intro scale mode
    exact
      (D.reflectedGram.atlas.generatedSpatialField_holomorphic
        D.sourceCLM scale (modeTest mode)).mono
        (fun _ hz => hz.1)
  field_polyBounded_on_compact := by
    intro C hC_compact hC_domain
    obtain ⟨B, hB, p, hbound⟩ :=
      D.reflectedGram.atlas.translatedSpatialField_encodedHermite_polyBounded_on_compact
          I τ hτ D.sourceCLM hsource
          C hC_compact hC_domain βs hβ
    refine ⟨B, hB, p, ?_⟩
    intro scale z hz mode
    rw [hmode mode]
    exact hbound scale z hz mode
  source := fun scale mode =>
    localPositiveTimeParameterTranslate
      (UniformCompactTimeSource.source
        (D.sourceCLM scale (modeTest mode)))
      (fun r : Fin (q + 1) =>
        chronologicalTimeSourceDirection (d := d) r)
  realRegion :=
    D.reflectedGram.atlas.gram.anchoredAtlasRealRegion
      D.reflectedGram.atlas.sourceStage.stage
      D.reflectedGram.atlas.sourceStage.germ
  realRegion_open :=
    D.reflectedGram.atlas.gram.anchoredAtlasRealRegion_open
      D.reflectedGram.atlas.sourceStage.stage
      D.reflectedGram.atlas.sourceStage.germ
  realRegion_mem_nhds :=
    D.reflectedGram.atlas.gram.anchoredAtlasRealRegion_mem_nhds
      D.reflectedGram.atlas.sourceStage.stage
      D.reflectedGram.atlas.sourceStage.germ
  realToComplex_mem_domain := by
    intro x hx
    apply
      D.reflectedGram.atlas.initialGramPolydisc_subset_spatialLinearDomain
    simpa [SCV.realToComplex] using hx.2
  field_realEdge := by
    intro scale mode
    exact
      D.reflectedGram.atlas.generatedSpatialField_realEdge
        D.sourceCLM scale (modeTest mode)

end ReflectedGramSpatialSourceData

/-- One full spatial source family, on one fixed compact positive-time
carrier, retained together with the exact same-depth reflected-Gram atlas. -/
structure GeneratedMixedReflectedGramSpatialSourceData
    (S : C)
    (depth q : ℕ) where
  carrier : Set (Fin ((q + 1) + 1) → ℝ)
  carrier_compact : IsCompact carrier
  carrier_positive :
    carrier ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1)
  reflectedGram :
    GeneratedMixedReflectedGramAtlasData
      (OS := OS) S depth q carrier
  sourceCLM :
    ℕ →
      SchwartzMap
          (Section43SpatialSpace d ((q + 1) + 1)) ℂ →L[ℂ]
        UniformCompactTimeSource d ((q + 1) + 1) carrier

namespace GeneratedMixedReflectedGramSpatialSourceData

variable
  {S : C}
  {depth q : ℕ}

/-- The retained source-indexed atlas gives a Hilbert vector continuously
linear in the complete spatial Schwartz test at every generated mixed point. -/
noncomputable def generatedFieldCLM
    (D : GeneratedMixedReflectedGramSpatialSourceData
      (OS := OS) S depth q)
    (scale : ℕ)
    (z : Fin (q + 1) → ℂ)
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiGeneratedMixedLogarithmicBase
          ((q + 1) + 1) depth)) :
    SchwartzMap
        (Section43SpatialSpace d ((q + 1) + 1)) ℂ →L[ℂ]
      OSHilbertSpace OS :=
  D.reflectedGram.atlas.spatialFieldCLM
    D.sourceCLM scale z (D.reflectedGram.coversGeneratedMixed hz)

@[simp]
theorem generatedFieldCLM_apply
    (D : GeneratedMixedReflectedGramSpatialSourceData
      (OS := OS) S depth q)
    (scale : ℕ)
    (z : Fin (q + 1) → ℂ)
    (hz :
      z ∈ osiiMixedTailArgumentCarrier
        (osiiGeneratedMixedLogarithmicBase
          ((q + 1) + 1) depth))
    (χ : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) ℂ) :
    D.generatedFieldCLM scale z hz χ =
      D.reflectedGram.atlas.gram.anchoredAtlasField
        D.reflectedGram.atlas.sourceStage.stage
        D.reflectedGram.atlas.sourceStage.germ
        (D.sourceCLM scale χ) z :=
  rfl

end GeneratedMixedReflectedGramSpatialSourceData

namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {k : ℕ} [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}

/-- Instantiate the retained stage-wide reflected-Gram package with the
physical rooted left-block source map for a nontrivial block. -/
noncomputable def rootedLeftNontrivialReflectedGramSpatialSourceData
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    {q : ℕ}
    (hi : i.n = q + 2) :
    ReflectedGramSpatialSourceData (OS := OS) S q := by
  rcases i with ⟨n, m, hn, hm, hnm⟩
  simp only at hi
  subst n
  let i : GeneratorIndex k := ⟨q + 2, m, hn, hm, hnm⟩
  let K := A.rootedLeftBlockSpatialSourceCarrier R i
  let hK_compact := A.rootedLeftBlockSpatialSourceCarrier_compact R i
  let hK_positive := A.rootedLeftBlockSpatialSourceCarrier_positive R i
  exact {
    carrier := K
    carrier_compact := hK_compact
    carrier_positive := hK_positive
    reflectedGram :=
      P.forCarrier q K hK_compact hK_positive
    sourceCLM :=
      A.rootedLeftBlockAnchoredSourceCLM R i }

/-- Right-block form of
`rootedLeftNontrivialReflectedGramSpatialSourceData`. -/
noncomputable def rootedRightNontrivialReflectedGramSpatialSourceData
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    {q : ℕ}
    (hi : i.m = q + 2) :
    ReflectedGramSpatialSourceData (OS := OS) S q := by
  rcases i with ⟨n, m, hn, hm, hnm⟩
  simp only at hi
  subst m
  let i : GeneratorIndex k := ⟨n, q + 2, hn, hm, hnm⟩
  let K := A.rootedRightBlockSpatialSourceCarrier R i
  let hK_compact := A.rootedRightBlockSpatialSourceCarrier_compact R i
  let hK_positive := A.rootedRightBlockSpatialSourceCarrier_positive R i
  exact {
    carrier := K
    carrier_compact := hK_compact
    carrier_positive := hK_positive
    reflectedGram :=
      P.forCarrier q K hK_compact hK_positive
    sourceCLM :=
      A.rootedRightBlockAnchoredSourceCLM R i }

/-- The nontrivial rooted left block as a source-realized open Hilbert field,
constructed from the retained stage-wide reflected-Gram package. -/
noncomputable def
    rootedLeftNontrivialReflectedGramOpenFieldScaleBlockRealEdgeData
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    {q : ℕ}
    (hi : i.n = q + 2) :
    GeneratorOpenHilbertFieldScaleBlockRealEdgeData
      OS i.n (i.n - 1) := by
  rcases i with ⟨n, m, hn, hm, hnm⟩
  simp only at hi
  subst n
  let i : GeneratorIndex k := ⟨q + 2, m, hn, hm, hnm⟩
  let D :=
    rootedLeftNontrivialReflectedGramSpatialSourceData
      S depth P A R i (q := q) rfl
  have hsource :
      ∀ scale χ,
        UniformCompactTimeSource.source (D.sourceCLM scale χ) =
          (A.rootedLeftBlockApproximateIdentity R i
            ).translatedPositiveTimeSpatialSource
              (A.rootedLeftBlockAnchor i)
              (A.rootedLeftBlockAnchor_positive i) χ scale := by
    intro scale χ
    simpa [D,
      rootedLeftNontrivialReflectedGramSpatialSourceData] using
      A.rootedLeftBlockAnchoredSourceCLM_source_translated
        R i scale χ
  have hmode :
      ∀ mode,
        leftSpatialHermiteBlock d i mode =
          (section43SpatialSchwartzParticleCLE
            d ((q + 1) + 1)).symm
            (SchwartzMap.productTensor fun a =>
              complexifyRealSchwartz
                (GaussianField.DyninMityaginSpace.basis
                  (E := SchwartzMap (Fin d → ℝ) ℝ)
                  (GeneratorHermiteHilbertFieldFamilyData.leftHermiteIndices
                    (d := d) i mode a))) := by
    intro mode
    ext η
    simp [
      GeneratorHermiteHilbertFieldFamilyData.leftHermiteIndices,
      leftSpatialHermiteBlock, spatialHermiteFactor,
      realSpatialHermiteFactor, complexifyRealSchwartz, i]
  exact
    D.toOpenFieldScaleBlockRealEdgeData
      (A.rootedLeftBlockApproximateIdentity R i)
      (A.rootedLeftBlockAnchor i)
      (A.rootedLeftBlockAnchor_positive i)
      hsource
      (leftSpatialHermiteBlock d i)
      (GeneratorHermiteHilbertFieldFamilyData.leftHermiteIndices
        (d := d) i)
      (GeneratorHermiteHilbertFieldFamilyData.leftHermiteIndices_polyGrowth
        (d := d) i)
      hmode

/-- Right-block form of
`rootedLeftNontrivialReflectedGramOpenFieldScaleBlockRealEdgeData`. -/
noncomputable def
    rootedRightNontrivialReflectedGramOpenFieldScaleBlockRealEdgeData
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    {q : ℕ}
    (hi : i.m = q + 2) :
    GeneratorOpenHilbertFieldScaleBlockRealEdgeData
      OS i.m (i.m - 1) := by
  rcases i with ⟨n, m, hn, hm, hnm⟩
  simp only at hi
  subst m
  let i : GeneratorIndex k := ⟨n, q + 2, hn, hm, hnm⟩
  let D :=
    rootedRightNontrivialReflectedGramSpatialSourceData
      S depth P A R i (q := q) rfl
  have hsource :
      ∀ scale χ,
        UniformCompactTimeSource.source (D.sourceCLM scale χ) =
          (A.rootedRightBlockApproximateIdentity R i
            ).translatedPositiveTimeSpatialSource
              (A.rootedRightBlockAnchor i)
              (A.rootedRightBlockAnchor_positive i) χ scale := by
    intro scale χ
    simpa [D,
      rootedRightNontrivialReflectedGramSpatialSourceData] using
      A.rootedRightBlockAnchoredSourceCLM_source_translated
        R i scale χ
  have hmode :
      ∀ mode,
        rightSpatialHermiteBlock d i mode =
          (section43SpatialSchwartzParticleCLE
            d ((q + 1) + 1)).symm
            (SchwartzMap.productTensor fun a =>
              complexifyRealSchwartz
                (GaussianField.DyninMityaginSpace.basis
                  (E := SchwartzMap (Fin d → ℝ) ℝ)
                  (GeneratorHermiteHilbertFieldFamilyData.rightHermiteIndices
                    (d := d) i mode a))) := by
    intro mode
    ext η
    simp [
      GeneratorHermiteHilbertFieldFamilyData.rightHermiteIndices,
      rightSpatialHermiteBlock, spatialHermiteFactor,
      realSpatialHermiteFactor, complexifyRealSchwartz, i]
  exact
    D.toOpenFieldScaleBlockRealEdgeData
      (A.rootedRightBlockApproximateIdentity R i)
      (A.rootedRightBlockAnchor i)
      (A.rootedRightBlockAnchor_positive i)
      hsource
      (rightSpatialHermiteBlock d i)
      (GeneratorHermiteHilbertFieldFamilyData.rightHermiteIndices
        (d := d) i)
      (GeneratorHermiteHilbertFieldFamilyData.rightHermiteIndices_polyGrowth
        (d := d) i)
      hmode

/-- Every rooted left block, with the one-particle endpoint retained and each
nontrivial block constructed from the stage-wide reflected-Gram package. -/
noncomputable def
    rootedReflectedGramLeftGeneratorOpenFieldScaleBlockRealEdgeData
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k) :
    GeneratorOpenHilbertFieldScaleBlockRealEdgeData
      OS i.n (i.n - 1) := by
  rcases i with ⟨n, m, hn, hm, hnm⟩
  by_cases hi : n = 1
  · subst n
    let i : GeneratorIndex k := ⟨1, m, hn, hm, hnm⟩
    exact
      rootedAnchoredLeftOneParticleOpenFieldScaleBlockRealEdgeData
        A R H i rfl
  · cases n with
    | zero => omega
    | succ n =>
      cases n with
      | zero => contradiction
      | succ q =>
        let i : GeneratorIndex k := ⟨q + 2, m, hn, hm, hnm⟩
        exact
          rootedScaleShiftOpenFieldBlock
            (rootedLeftNontrivialReflectedGramOpenFieldScaleBlockRealEdgeData
              S depth P A R i (q := q) rfl)
            (H.commonTailStart i)

/-- Right-block form of
`rootedReflectedGramLeftGeneratorOpenFieldScaleBlockRealEdgeData`. -/
noncomputable def
    rootedReflectedGramRightGeneratorOpenFieldScaleBlockRealEdgeData
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k) :
    GeneratorOpenHilbertFieldScaleBlockRealEdgeData
      OS i.m (i.m - 1) := by
  rcases i with ⟨n, m, hn, hm, hnm⟩
  by_cases hi : m = 1
  · subst m
    let i : GeneratorIndex k := ⟨n, 1, hn, hm, hnm⟩
    exact
      rootedAnchoredRightOneParticleOpenFieldScaleBlockRealEdgeData
        A R H i rfl
  · cases m with
    | zero => omega
    | succ m =>
      cases m with
      | zero => contradiction
      | succ q =>
        let i : GeneratorIndex k := ⟨n, q + 2, hn, hm, hnm⟩
        exact
          rootedScaleShiftOpenFieldBlock
            (rootedRightNontrivialReflectedGramOpenFieldScaleBlockRealEdgeData
              S depth P A R i (q := q) rfl)
            (H.commonTailStart i)

/-- The complete all-split rooted field family constructed from one retained
same-depth reflected-Gram package.  Both sides use the same physical packet
scale, including the existing one-particle endpoints. -/
noncomputable def
    rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R) :
    GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k :=
  GeneratorOpenHilbertFieldScaleFamilyRealEdgeData.ofBlocks
    (rootedReflectedGramLeftGeneratorOpenFieldScaleBlockRealEdgeData
      S depth P A R H)
    (rootedReflectedGramRightGeneratorOpenFieldScaleBlockRealEdgeData
      S depth P A R H)

/-- Source provenance for a complete all-split rooted open-field family.

Target-local stage construction may replace the outer reflected-Gram family
by an adapted one before selecting its unsmeared fields.  Retaining this
witness keeps that adapted family, packet, roots, and translation data
available to the later bounded lower-rank induction. -/
structure RootedAllSplitSourceProvenanceData
    (S : C)
    (depth : Nat)
    (E : GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k) where
  atlasFamily : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth
  approximateIdentity : Section43ProductTimeApproximateIdentity k
  anchor : Fin k -> Real
  packet : AnchoredPacketTimeShellFamilyData
    (d := d) approximateIdentity anchor
  roots : TripleConvolutionRootData approximateIdentity
  translation : RootedA0BlockContinuousTranslationData OS packet roots
  family_eq : E =
    rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
      S depth atlasFamily packet roots translation

/-- Every left source in the reflected-Gram all-split family is the physical
rooted translated block at the synchronized packet scale. -/
theorem
    rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData_leftSource_eq
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (scale mode : ℕ)
    (x : Fin (i.n - 1) → ℝ) :
    (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        S depth P A R H).leftSource i scale mode x =
      A.rootedLeftBlockTranslatedSpatialSourceNative R i
        (scale + H.commonTailStart i) mode x := by
  unfold rootedLeftBlockTranslatedSpatialSourceNative
  rcases i with ⟨n, m, hn, hm, hnm⟩
  by_cases hi : n = 1
  · subst n
    rfl
  · cases n with
    | zero => omega
    | succ n =>
      cases n with
      | zero => contradiction
      | succ q =>
        rw [
          ReflectedA0BlockContinuousTranslationData.leftHeadSpatialHermiteBlock_eq_cast_leftSpatialHermiteBlock]
        rfl

/-- Right-hand source normal form for the reflected-Gram family. -/
theorem
    rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData_rightSource_eq
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (scale mode : ℕ)
    (x : Fin (i.m - 1) → ℝ) :
    (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        S depth P A R H).rightSource i scale mode x =
      A.rootedRightBlockTranslatedSpatialSourceNative R i
        (scale + H.commonTailStart i) mode x := by
  unfold rootedRightBlockTranslatedSpatialSourceNative
  rcases i with ⟨n, m, hn, hm, hnm⟩
  by_cases hi : m = 1
  · subst m
    rfl
  · cases m with
    | zero => omega
    | succ m =>
      cases m with
      | zero => contradiction
      | succ q =>
        rw [
          ReflectedA0BlockContinuousTranslationData.rightHeadSpatialHermiteBlock_eq_cast_rightSpatialHermiteBlock]
        rfl

/-- The reflected-Gram global rooted fields and the original local rooted
fields carry identical positive-time sources at every split and scale. -/
noncomputable def
    rootedReflectedGramGeneratorOpenFieldSourceAgreementData
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R) :
    GeneratorOpenHilbertFieldScaleFamilyRealEdgeData.SourceAgreementData
      (rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        S depth P A R H.toContinuousTranslationData)
      (rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        A R H) where
  leftSource_eq := by
    intro i scale mode x
    rw [
      rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData_leftSource_eq,
      rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData_leftSource_eq]
  rightSource_eq := by
    intro i scale mode x
    rw [
      rootedReflectedGramGeneratorOpenHilbertFieldScaleFamilyRealEdgeData_rightSource_eq,
      rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData_rightSource_eq]

/-- The complete reflected-Gram and local rooted families have one common
positive-real source germ under the original OS axioms alone. -/
noncomputable def
    rootedReflectedGramGeneratorCommonPositiveRealModeAgreementDataOfOS
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R) :
    (rootedReflectedGramGeneratorOpenFieldSourceAgreementData
      S depth P A R H).CommonPositiveRealModeAgreementDataOfOS :=
  (rootedReflectedGramGeneratorOpenFieldSourceAgreementData
    S depth P A R H).toCommonPositiveRealModeAgreementDataOfOS

/-- The original-OS reflected-Gram and local rooted generator families
agree on their actual connected complex source germ. -/
noncomputable def
    rootedReflectedGramGeneratorCommonComplexModeGermDataOfOS
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R) :
    GeneratorOpenHilbertFieldScaleFamilyRealEdgeData.SourceAgreementData.CommonComplexModeGermDataOfOS
      (rootedReflectedGramGeneratorCommonPositiveRealModeAgreementDataOfOS
        S depth P A R H) :=
  (rootedReflectedGramGeneratorCommonPositiveRealModeAgreementDataOfOS
    S depth P A R H).toCommonComplexModeGermDataOfOS

/-- Compatibility presentation of the original-OS reflected-Gram common
positive-real source germ. -/
noncomputable def
    rootedReflectedGramGeneratorCommonPositiveRealModeAgreementData
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (lgc : OSLinearGrowthCondition d OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R) :
    (rootedReflectedGramGeneratorOpenFieldSourceAgreementData
      S depth P A R H).CommonPositiveRealModeAgreementData lgc :=
  (rootedReflectedGramGeneratorOpenFieldSourceAgreementData
    S depth P A R H).toCommonPositiveRealModeAgreementData lgc

/-- Compatibility presentation of the reflected-Gram common complex source
germ. -/
noncomputable def
    rootedReflectedGramGeneratorCommonComplexModeGermData
    (S : C)
    (depth : ℕ)
    (P : StageWideReflectedGramAtlasFamilyData (OS := OS) S depth)
    (lgc : OSLinearGrowthCondition d OS)
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R) :
    GeneratorOpenHilbertFieldScaleFamilyRealEdgeData.SourceAgreementData.CommonComplexModeGermData
      (rootedReflectedGramGeneratorCommonPositiveRealModeAgreementData
        S depth P lgc A R H) :=
  (rootedReflectedGramGeneratorCommonPositiveRealModeAgreementData
    S depth P lgc A R H).toCommonComplexModeGermData

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity

end OSIIChapterV
end OSReconstruction
