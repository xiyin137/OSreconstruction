/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRootedAnchoredSpatialGrowth
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketRootedCanonicalFields















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

/-- A centered real ball contained in the real edge of one local rooted
holomorphic field. -/
private structure RootedLocalRealEdgeBall
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n m : ℕ}
    {translatedSource :
      ℕ → (Fin m → ℝ) → SchwartzMap E ℂ →
        euclideanPositiveTimeSubmodule (d := d) n}
    (D :
      LocalReflectedA0HolomorphicTranslationFieldData
        OS n m translatedSource) where
  radius : ℝ
  radius_pos : 0 < radius
  ball_subset :
    Metric.ball (0 : Fin m → ℝ) radius ⊆ D.realRegion

private theorem nonempty_rootedLocalRealEdgeBall
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n m : ℕ}
    {translatedSource :
      ℕ → (Fin m → ℝ) → SchwartzMap E ℂ →
        euclideanPositiveTimeSubmodule (d := d) n}
    (D :
      LocalReflectedA0HolomorphicTranslationFieldData
        OS n m translatedSource) :
    Nonempty (RootedLocalRealEdgeBall D) := by
  rcases Metric.mem_nhds_iff.mp D.realRegion_nhds with
    ⟨r, hr, hball⟩
  exact ⟨⟨r, hr, hball⟩⟩

private noncomputable def rootedLocalRealEdgeBall
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n m : ℕ}
    {translatedSource :
      ℕ → (Fin m → ℝ) → SchwartzMap E ℂ →
        euclideanPositiveTimeSubmodule (d := d) n}
    (D :
      LocalReflectedA0HolomorphicTranslationFieldData
        OS n m translatedSource) :
    RootedLocalRealEdgeBall D :=
  Classical.choice (nonempty_rootedLocalRealEdgeBall D)

/-- The synchronized local rooted-left field in the source-realized
open-field interface. -/
noncomputable def rootedLocalLeftOpenFieldScaleBlockRealEdgeData
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k) :
    GeneratorOpenHilbertFieldScaleBlockRealEdgeData
      OS i.n (i.n - 1) := by
  rcases i with ⟨n, m, hn, hm, hnm⟩
  cases n with
  | zero => omega
  | succ q =>
    let i : GeneratorIndex k := ⟨q + 1, m, hn, hm, hnm⟩
    let D := H.toContinuousTranslationData
    let B := rootedLocalRealEdgeBall (H.left i)
    exact {
      domain := (H.left i).domain
      domain_open := (H.left i).domain_open
      field := fun scale mode =>
        D.leftSpatialHermiteGeneratorField i scale mode
      field_holomorphic := by
        intro scale mode
        unfold RootedA0BlockContinuousTranslationData.leftSpatialHermiteGeneratorField
        exact
          (H.left i).field_holomorphic
            (D.leftCofinalIndex i scale)
            (ReflectedA0BlockConvergenceData.leftHeadSpatialHermiteBlock
              (d := d) i mode)
      field_polyBounded_on_compact := by
        intro K hK_compact hK_domain
        exact
          D.exists_leftSpatialHermiteGeneratorField_norm_polynomial_bound_on_complex_compact
            i K hK_compact hK_domain
      source := fun scale mode x =>
        A.rootedLeftBlockTranslatedSpatialSource R i
          (scale + D.commonTailStart i) x
          (ReflectedA0BlockConvergenceData.leftHeadSpatialHermiteBlock
            (d := d) i mode)
      realRegion := Metric.ball 0 B.radius
      realRegion_open := Metric.isOpen_ball
      realRegion_mem_nhds := Metric.ball_mem_nhds 0 B.radius_pos
      realToComplex_mem_domain := by
        intro x hx
        exact (D.left i).realRegion_to_domain x (B.ball_subset hx)
      field_realEdge := by
        intro scale mode x hx
        simpa [
          i, D,
          RootedA0BlockContinuousTranslationData.leftSpatialHermiteGeneratorField]
          using
            (D.left i).realEdge
              (D.leftCofinalIndex i scale)
              (ReflectedA0BlockConvergenceData.leftHeadSpatialHermiteBlock
                (d := d) i mode)
              x (B.ball_subset hx)
    }

/-- The synchronized local rooted-right field in the same interface. -/
noncomputable def rootedLocalRightOpenFieldScaleBlockRealEdgeData
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k) :
    GeneratorOpenHilbertFieldScaleBlockRealEdgeData
      OS i.m (i.m - 1) := by
  rcases i with ⟨n, m, hn, hm, hnm⟩
  cases m with
  | zero => omega
  | succ q =>
    let i : GeneratorIndex k := ⟨n, q + 1, hn, hm, hnm⟩
    let D := H.toContinuousTranslationData
    let B := rootedLocalRealEdgeBall (H.right i)
    exact {
      domain := (H.right i).domain
      domain_open := (H.right i).domain_open
      field := fun scale mode =>
        D.rightSpatialHermiteGeneratorField i scale mode
      field_holomorphic := by
        intro scale mode
        unfold RootedA0BlockContinuousTranslationData.rightSpatialHermiteGeneratorField
        exact
          (H.right i).field_holomorphic
            (D.rightCofinalIndex i scale)
            (ReflectedA0BlockConvergenceData.rightHeadSpatialHermiteBlock
              (d := d) i mode)
      field_polyBounded_on_compact := by
        intro K hK_compact hK_domain
        exact
          D.exists_rightSpatialHermiteGeneratorField_norm_polynomial_bound_on_complex_compact
            i K hK_compact hK_domain
      source := fun scale mode x =>
        A.rootedRightBlockTranslatedSpatialSource R i
          (scale + D.commonTailStart i) x
          (ReflectedA0BlockConvergenceData.rightHeadSpatialHermiteBlock
            (d := d) i mode)
      realRegion := Metric.ball 0 B.radius
      realRegion_open := Metric.isOpen_ball
      realRegion_mem_nhds := Metric.ball_mem_nhds 0 B.radius_pos
      realToComplex_mem_domain := by
        intro x hx
        exact (D.right i).realRegion_to_domain x (B.ball_subset hx)
      field_realEdge := by
        intro scale mode x hx
        simpa [
          i, D,
          RootedA0BlockContinuousTranslationData.rightSpatialHermiteGeneratorField]
          using
            (D.right i).realEdge
              (D.rightCofinalIndex i scale)
              (ReflectedA0BlockConvergenceData.rightHeadSpatialHermiteBlock
                (d := d) i mode)
              x (B.ball_subset hx)
    }

/-- The all-split local rooted field family, synchronized to one physical
packet scale on both sides of every generator split. -/
noncomputable def
    rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R) :
    GeneratorOpenHilbertFieldScaleFamilyRealEdgeData OS k :=
  GeneratorOpenHilbertFieldScaleFamilyRealEdgeData.ofBlocks
    (rootedLocalLeftOpenFieldScaleBlockRealEdgeData A R H)
    (rootedLocalRightOpenFieldScaleBlockRealEdgeData A R H)

/-- The local adapter retains the original synchronized rooted-left
holomorphy domain. -/
@[simp]
theorem
    rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData_leftDomain
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k) :
    (rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        A R H).leftDomain i =
      (H.toContinuousTranslationData.left i).domain := by
  rcases i with ⟨n, m, hn, hm, hnm⟩
  cases n with
  | zero => omega
  | succ q =>
    rfl

/-- The local adapter retains the original synchronized rooted-right
holomorphy domain. -/
@[simp]
theorem
    rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData_rightDomain
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k) :
    (rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        A R H).rightDomain i =
      (H.toContinuousTranslationData.right i).domain := by
  rcases i with ⟨n, m, hn, hm, hnm⟩
  cases m with
  | zero => omega
  | succ q =>
    rfl

/-- Hence the local open-field generator domain is exactly the original
rooted semigroup domain. -/
@[simp]
theorem rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData_domain
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k) :
    (rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        A R H).domain i =
      generatorSemigroupDomain i
        (H.toContinuousTranslationData.left i).domain
        (H.toContinuousTranslationData.right i).domain := by
  rw [GeneratorOpenHilbertFieldScaleFamilyData.domain,
    rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData_leftDomain,
    rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData_rightDomain]

/-- Every local rooted-left source is the native-arity physical translated
source at the synchronized packet scale. -/
theorem
    rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData_leftSource_eq
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (scale mode : ℕ)
    (x : Fin (i.n - 1) → ℝ) :
    (rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        A R H).leftSource i scale mode x =
      A.rootedLeftBlockTranslatedSpatialSourceNative R i
        (scale + H.toContinuousTranslationData.commonTailStart i)
        mode x := by
  unfold rootedLeftBlockTranslatedSpatialSourceNative
  rcases i with ⟨n, m, hn, hm, hnm⟩
  cases n with
  | zero => omega
  | succ q =>
    rfl

/-- Right-hand local source normal form. -/
theorem
    rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData_rightSource_eq
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (H : RootedA0BlockHolomorphicTranslationData OS A R)
    (i : GeneratorIndex k)
    (scale mode : ℕ)
    (x : Fin (i.m - 1) → ℝ) :
    (rootedLocalGeneratorOpenHilbertFieldScaleFamilyRealEdgeData
        A R H).rightSource i scale mode x =
      A.rootedRightBlockTranslatedSpatialSourceNative R i
        (scale + H.toContinuousTranslationData.commonTailStart i)
        mode x := by
  unfold rootedRightBlockTranslatedSpatialSourceNative
  rcases i with ⟨n, m, hn, hm, hnm⟩
  cases m with
  | zero => omega
  | succ q =>
    rfl

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
