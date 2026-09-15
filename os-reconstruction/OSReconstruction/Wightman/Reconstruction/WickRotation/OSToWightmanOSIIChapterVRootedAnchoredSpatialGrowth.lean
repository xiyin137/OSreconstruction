/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRootedAnchoredSpatialSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVTranslatedAnchoredSpatialGrowth
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorOpenFieldRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketRootedGeneratorBridge















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

private theorem finFunction_eq_of_dimension_eq_zero
    {r : ℕ}
    (hr : r = 0)
    {α : Type*}
    (f g : Fin r → α) :
    f = g := by
  subst r
  funext j
  exact Fin.elim0 j

/-- Reindex a source-realized open block by one fixed physical packet-scale
shift. -/
noncomputable def rootedScaleShiftOpenFieldBlock
    {n m : ℕ}
    (B : GeneratorOpenHilbertFieldScaleBlockRealEdgeData OS n m)
    (shift : ℕ) :
    GeneratorOpenHilbertFieldScaleBlockRealEdgeData OS n m where
  domain := B.domain
  domain_open := B.domain_open
  field := fun scale => B.field (scale + shift)
  field_holomorphic := fun scale => B.field_holomorphic (scale + shift)
  field_polyBounded_on_compact := by
    intro C hC_compact hC_domain
    obtain ⟨M, hM, p, hbound⟩ :=
      B.field_polyBounded_on_compact C hC_compact hC_domain
    exact
      ⟨M, hM, p,
        fun scale z hz mode =>
          hbound (scale + shift) z hz mode⟩
  source := fun scale => B.source (scale + shift)
  realRegion := B.realRegion
  realRegion_open := B.realRegion_open
  realRegion_mem_nhds := B.realRegion_mem_nhds
  realToComplex_mem_domain := B.realToComplex_mem_domain
  field_realEdge := fun scale => B.field_realEdge (scale + shift)

/-- The global rooted-left anchored field for a block whose particle count is
written explicitly as `q + 2`. -/
noncomputable def
    rootedAnchoredLeftNontrivialOpenFieldScaleBlockRealEdgeData
    (L : SimultaneousTimeContinuationStageLevel d)
    (H : L.HasCanonicalReducedCompactEdges OS)
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
  let D :
      UniversalCompactCarrierAnchoredAtlasData (q := q) L OS
        (A.rootedLeftBlockSpatialSourceCarrier R i) :=
    Classical.choice
      (nonempty_universalCompactCarrierAnchoredAtlasData
        (q := q) L OS H
        (A.rootedLeftBlockSpatialSourceCarrier R i)
        (A.rootedLeftBlockSpatialSourceCarrier_compact R i)
        (A.rootedLeftBlockSpatialSourceCarrier_positive R i))
  exact {
    domain := D.spatialLinearDomain
    domain_open := D.spatialLinearDomain_open
    field := fun scale mode z =>
      D.gram.anchoredAtlasField
        D.sourceStage.stage D.sourceStage.germ
        (A.rootedLeftBlockAnchoredSourceCLM R i scale
          (leftSpatialHermiteBlock d i mode))
        z
    field_holomorphic := by
      intro scale mode
      exact
        (D.generatedSpatialField_holomorphic
          (A.rootedLeftBlockAnchoredSourceCLM R i)
          scale (leftSpatialHermiteBlock d i mode)).mono
          (fun _ hz => hz.1)
    field_polyBounded_on_compact := by
      intro C hC_compact hC_domain
      obtain ⟨B, hB, p, hbound⟩ :=
        D.translatedSpatialField_encodedHermite_polyBounded_on_compact
          (A.rootedLeftBlockApproximateIdentity R i)
          (A.rootedLeftBlockAnchor i)
          (A.rootedLeftBlockAnchor_positive i)
          (A.rootedLeftBlockAnchoredSourceCLM R i)
          (by
            intro scale χ
            exact
              A.rootedLeftBlockAnchoredSourceCLM_source_translated
                R i scale χ)
          C hC_compact hC_domain
          (GeneratorHermiteHilbertFieldFamilyData.leftHermiteIndices
            (d := d) i)
          (GeneratorHermiteHilbertFieldFamilyData.leftHermiteIndices_polyGrowth
            (d := d) i)
      refine ⟨B, hB, p, ?_⟩
      intro scale z hz mode
      have hcomplexify (f : SchwartzMap (Fin d → ℝ) ℝ) :
          OSIIAxisPairSourcewiseFlatCrossData.GaussianCMMFamily.complexifyRealSchwartz f =
            SCV.schwartzOfRealCLM f := rfl
      simpa [
        GeneratorHermiteHilbertFieldFamilyData.leftHermiteIndices,
        leftSpatialHermiteBlock, spatialHermiteFactor,
        realSpatialHermiteFactor,
        hcomplexify,
        i] using
        hbound scale z hz mode
    source := fun scale mode =>
      localPositiveTimeParameterTranslate
        (A.rootedLeftBlockSpatialSource R i scale
          (leftSpatialHermiteBlock d i mode))
        (fun r : Fin (i.n - 1) =>
          chronologicalTimeSourceDirection (d := d) r)
    realRegion :=
      D.gram.anchoredAtlasRealRegion
        D.sourceStage.stage D.sourceStage.germ
    realRegion_open :=
      D.gram.anchoredAtlasRealRegion_open
        D.sourceStage.stage D.sourceStage.germ
    realRegion_mem_nhds :=
      D.gram.anchoredAtlasRealRegion_mem_nhds
        D.sourceStage.stage D.sourceStage.germ
    realToComplex_mem_domain := by
      intro x hx
      apply D.initialGramPolydisc_subset_spatialLinearDomain
      change SCV.realToComplex x ∈ _
      exact hx.2
    field_realEdge := by
      intro scale mode
      simpa only [
        rootedLeftBlockAnchoredSourceCLM_source,
        rootedLeftBlockAnchoredSourceCLM_source_translated] using!
        D.generatedSpatialField_realEdge
          (A.rootedLeftBlockAnchoredSourceCLM R i)
          scale (leftSpatialHermiteBlock d i mode) }

/-- The synchronized rooted-left one-particle endpoint, viewed on its unique
zero-dimensional complex parameter space. -/
noncomputable def
    rootedAnchoredLeftOneParticleOpenFieldScaleBlockRealEdgeData
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (hi : i.n = 1) :
    GeneratorOpenHilbertFieldScaleBlockRealEdgeData
      OS i.n (i.n - 1) := by
  rcases i with ⟨n, m, hn, hm, hnm⟩
  simp only at hi
  subst n
  let i : GeneratorIndex k := ⟨1, m, hn, hm, hnm⟩
  have hzeroDim : i.n - 1 = 0 := by
    simp [i]
  exact {
    domain := Set.univ
    domain_open := isOpen_univ
    field := fun scale mode =>
      D.leftSpatialHermiteGeneratorField i scale mode
    field_holomorphic := by
      intro scale mode
      have hconst :
          D.leftSpatialHermiteGeneratorField i scale mode =
            fun _ =>
              D.leftSpatialHermiteGeneratorField i scale mode 0 := by
        funext z
        congr 1
        exact finFunction_eq_of_dimension_eq_zero hzeroDim z 0
      rw [hconst]
      exact differentiableOn_const _
    field_polyBounded_on_compact := by
      intro _C _hC_compact _hC_domain
      have hzero_domain :
          ({0} : Set (Fin (i.n - 1) → ℂ)) ⊆
            (D.left i).domain := by
        intro z hz
        have hz : z = 0 := Set.mem_singleton_iff.mp hz
        subst z
        exact (D.left i).zero_mem_domain
      obtain ⟨B, hB, p, hbound⟩ :=
        D.exists_leftSpatialHermiteGeneratorField_norm_polynomial_bound_on_complex_compact
          i {0} isCompact_singleton hzero_domain
      exact
        ⟨B, hB, p,
          fun scale z _hz mode => by
            have hz :
                z = 0 :=
              finFunction_eq_of_dimension_eq_zero hzeroDim z 0
            subst z
            exact hbound scale 0 (Set.mem_singleton 0) mode⟩
    source := fun scale mode x =>
      A.rootedLeftBlockTranslatedSpatialSource R i
        (scale + D.commonTailStart i) x
        (ReflectedA0BlockConvergenceData.leftHeadSpatialHermiteBlock
          (d := d) i mode)
    realRegion := Set.univ
    realRegion_open := isOpen_univ
    realRegion_mem_nhds := univ_mem
    realToComplex_mem_domain := fun _ _ => Set.mem_univ _
    field_realEdge := by
      intro scale mode x _hx
      have hx :
          x = 0 :=
        finFunction_eq_of_dimension_eq_zero hzeroDim x 0
      subst x
      have hzero :
          (0 : Fin (i.n - 1) → ℝ) ∈ (D.left i).realRegion :=
        mem_of_mem_nhds (D.left i).realRegion_nhds
      simpa [
        RootedA0BlockContinuousTranslationData.leftSpatialHermiteGeneratorField]
        using!
          (D.left i).realEdge
            (D.leftCofinalIndex i scale)
            (ReflectedA0BlockConvergenceData.leftHeadSpatialHermiteBlock
              (d := d) i mode)
            0 hzero }

/-- The synchronized rooted-right one-particle endpoint. -/
noncomputable def
    rootedAnchoredRightOneParticleOpenFieldScaleBlockRealEdgeData
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (hi : i.m = 1) :
    GeneratorOpenHilbertFieldScaleBlockRealEdgeData
      OS i.m (i.m - 1) := by
  rcases i with ⟨n, m, hn, hm, hnm⟩
  simp only at hi
  subst m
  let i : GeneratorIndex k := ⟨n, 1, hn, hm, hnm⟩
  have hzeroDim : i.m - 1 = 0 := by
    simp [i]
  exact {
    domain := Set.univ
    domain_open := isOpen_univ
    field := fun scale mode =>
      D.rightSpatialHermiteGeneratorField i scale mode
    field_holomorphic := by
      intro scale mode
      have hconst :
          D.rightSpatialHermiteGeneratorField i scale mode =
            fun _ =>
              D.rightSpatialHermiteGeneratorField i scale mode 0 := by
        funext z
        congr 1
        exact finFunction_eq_of_dimension_eq_zero hzeroDim z 0
      rw [hconst]
      exact differentiableOn_const _
    field_polyBounded_on_compact := by
      intro _C _hC_compact _hC_domain
      have hzero_domain :
          ({0} : Set (Fin (i.m - 1) → ℂ)) ⊆
            (D.right i).domain := by
        intro z hz
        have hz : z = 0 := Set.mem_singleton_iff.mp hz
        subst z
        exact (D.right i).zero_mem_domain
      obtain ⟨B, hB, p, hbound⟩ :=
        D.exists_rightSpatialHermiteGeneratorField_norm_polynomial_bound_on_complex_compact
          i {0} isCompact_singleton hzero_domain
      exact
        ⟨B, hB, p,
          fun scale z _hz mode => by
            have hz :
                z = 0 :=
              finFunction_eq_of_dimension_eq_zero hzeroDim z 0
            subst z
            exact hbound scale 0 (Set.mem_singleton 0) mode⟩
    source := fun scale mode x =>
      A.rootedRightBlockTranslatedSpatialSource R i
        (scale + D.commonTailStart i) x
        (ReflectedA0BlockConvergenceData.rightHeadSpatialHermiteBlock
          (d := d) i mode)
    realRegion := Set.univ
    realRegion_open := isOpen_univ
    realRegion_mem_nhds := univ_mem
    realToComplex_mem_domain := fun _ _ => Set.mem_univ _
    field_realEdge := by
      intro scale mode x _hx
      have hx :
          x = 0 :=
        finFunction_eq_of_dimension_eq_zero hzeroDim x 0
      subst x
      have hzero :
          (0 : Fin (i.m - 1) → ℝ) ∈ (D.right i).realRegion :=
        mem_of_mem_nhds (D.right i).realRegion_nhds
      simpa [
        RootedA0BlockContinuousTranslationData.rightSpatialHermiteGeneratorField]
        using!
          (D.right i).realEdge
            (D.rightCofinalIndex i scale)
            (ReflectedA0BlockConvergenceData.rightHeadSpatialHermiteBlock
              (d := d) i mode)
            0 hzero }

/-- The exact rooted-left translated source, transported from the syntactic
arity `(i.n - 1) + 1` to the generator's native arity `i.n`. -/
noncomputable def rootedLeftBlockTranslatedSpatialSourceNative
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (scale mode : ℕ)
    (x : Fin (i.n - 1) → ℝ) :
    euclideanPositiveTimeSubmodule (d := d) i.n :=
  cast
    (congrArg
      (fun n => ↥(euclideanPositiveTimeSubmodule (d := d) n))
      (Nat.sub_add_cancel i.hn))
    (A.rootedLeftBlockTranslatedSpatialSource R i scale x
      (ReflectedA0BlockConvergenceData.leftHeadSpatialHermiteBlock
        (d := d) i mode))

/-- Right-hand native-arity rooted translated source. -/
noncomputable def rootedRightBlockTranslatedSpatialSourceNative
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (scale mode : ℕ)
    (x : Fin (i.m - 1) → ℝ) :
    euclideanPositiveTimeSubmodule (d := d) i.m :=
  cast
    (congrArg
      (fun m => ↥(euclideanPositiveTimeSubmodule (d := d) m))
      (Nat.sub_add_cancel i.hm))
    (A.rootedRightBlockTranslatedSpatialSource R i scale x
      (ReflectedA0BlockConvergenceData.rightHeadSpatialHermiteBlock
        (d := d) i mode))

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
