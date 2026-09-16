/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageWideReflectedGramRootedBounds
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapFixedAxisAllSplitUniformTargetRankField
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapFixedAxisAnchoredAtlas
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorChronologicalCoordinates
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVLogarithmicGeneratorDomains
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorBranchGeometry
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReducedTranslation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageRealEdge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReflectedMovingSliceBridge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedRankedRootedSuccessor
import OSReconstruction.SCV.TotallyRealIdentity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapFixedAxisAllSplitRankGenerator
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictGeneratedPointedDepthInduction
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapBoundedTarget
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairProductSourceAdapter
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairProductSourceComparison
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVDifferenceReducedSupport
import OSReconstruction.Wightman.Reconstruction.DenseCLM
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapFixedAxisAllSplitUniformTargetCutoffHullRankField
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVMovingSliceDistribution
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialCoherentTarget
import OSReconstruction.SCV.SchwartzFiniteSeminormBound
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorRadialDomain

noncomputable section

open Complex Set Topology Filter
open scoped Classical Pointwise

namespace OSReconstruction
namespace FixedAxisSplitUniformRankFieldData

open OSIIChapterV

/-- Connected components of open subsets of a normed space are open. -/
theorem isOpen_connectedComponentIn_normedSpace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {U : Set E} (hU : IsOpen U) (x : E) :
    IsOpen (connectedComponentIn U x) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hyU : y ∈ U := connectedComponentIn_subset U x hy
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU y hyU
  have hballComponent : Metric.ball y r ⊆ connectedComponentIn U y :=
    (convex_ball y r).isPreconnected.subset_connectedComponentIn
      (Metric.mem_ball_self hr) hball
  rw [← connectedComponentIn_eq hy] at hballComponent
  exact Filter.mem_of_superset (Metric.ball_mem_nhds y hr) hballComponent

set_option maxHeartbeats 1000000 in
/-- Hilbert-valued holomorphic maps on a connected finite-dimensional domain
agree everywhere when they agree on a nonempty open real slice. -/
theorem hilbert_holomorphic_eq_at_of_eq_on_open_real
    {d : Nat} [NeZero d]
    {m : Nat}
    {OS : OsterwalderSchraderAxioms d}
    (U : Set (Fin m -> Complex))
    (hUOpen : IsOpen U)
    (hUConnected : IsConnected U)
    (f g : (Fin m -> Complex) -> OSHilbertSpace OS)
    (hf : DifferentiableOn Complex f U)
    (hg : DifferentiableOn Complex g U)
    (V : Set (Fin m -> Real))
    (hVOpen : IsOpen V)
    (hVNonempty : V.Nonempty)
    (hVsub : forall x, x ∈ V -> (fun a => (x a : Complex)) ∈ U)
    (hreal : forall x, x ∈ V ->
      f (fun a => (x a : Complex)) = g (fun a => (x a : Complex)))
    (z : Fin m -> Complex)
    (hz : z ∈ U) :
    f z = g z := by
  let v : OSHilbertSpace OS := f z - g z
  have hF : DifferentiableOn Complex
      (fun w => (innerSL Complex v) (f w)) U :=
    (differentiableOn_const (c := innerSL Complex v)).clm_apply hf
  have hG : DifferentiableOn Complex
      (fun w => (innerSL Complex v) (g w)) U :=
    (differentiableOn_const (c := innerSL Complex v)).clm_apply hg
  have hpair :
      (innerSL Complex v) (f z) = (innerSL Complex v) (g z) := by
    apply SCV.holomorphic_eq_of_eq_on_open_real_of_connected_finite
      hUOpen hUConnected hF hG hVOpen hVNonempty hVsub
    intro x hx
    rw [hreal x hx]
    exact hz
  have hpair' :
      @inner Complex (OSHilbertSpace OS) _ v (f z) =
        @inner Complex (OSHilbertSpace OS) _ v (g z) := by
    simpa [innerSL_apply_apply] using hpair
  have hv : @inner Complex (OSHilbertSpace OS) _ v v = 0 := by
    rw [show v = f z - g z by rfl]
    rw [inner_sub_right, hpair', sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hv)

variable {d n depth rank : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}
variable {C : Type*}
variable [OSIIChapterV.CanonicalGeneratorStageLevelProvider OS C]
variable {S : C}
variable {P : OSIIChapterV.StageWideStrictGeneratedMixedReflectedGramRankData
  (OS := OS) S depth rank}

set_option maxHeartbeats 1000000 in
/-- A stored reflected-Gram atlas and a rank atlas on a larger carrier define
the same source field on the common zero-based domain, even when their stage
providers differ.  Both real edges are the same OS Hilbert vector. -/
theorem
    ofCarrier_field_eq_reflectedGram_source_acrossProviders_on_openZeroConvexKernel_inter_domain
    {q : Nat}
    {Csource Crank : Type*}
    [OSIIChapterV.CanonicalGeneratorStageLevelProvider OS Csource]
    [OSIIChapterV.CanonicalGeneratorStageLevelProvider OS Crank]
    {Ssource : Csource} {Srank : Crank}
    (source : OSIIChapterV.ReflectedGramSpatialSourceData
      (OS := OS) Ssource q)
    (P : OSIIChapterV.StageWideStrictGeneratedMixedReflectedGramRankData
      (OS := OS) Srank depth rank)
    {L : Set (Fin ((q + 1) + 1) -> Real)}
    (hL_compact : IsCompact L)
    (hL_positive : L ⊆ section43TimeStrictPositiveRegion ((q + 1) + 1))
    (hKL : source.carrier ⊆ L)
    (base : OSIIChapterV.UniformCompactTimeSource
      d ((q + 1) + 1) source.carrier) :
    let B := (P.forCarrier q L hL_compact hL_positive).atlas
    forall z, z ∈ openZeroConvexKernel
        (source.reflectedGram.atlas.spatialLinearDomain ∩
          B.spatialLinearDomain) ->
      B.gram.anchoredAtlasField B.sourceStage.stage B.sourceStage.germ
          (OSIIChapterV.uniformCompactTimeSourceMonoCLM hKL base) z =
        source.reflectedGram.atlas.gram.anchoredAtlasField
          source.reflectedGram.atlas.sourceStage.stage
          source.reflectedGram.atlas.sourceStage.germ base z := by
  dsimp only
  let A := source.reflectedGram.atlas
  let B := (P.forCarrier q L hL_compact hL_positive).atlas
  let U : Set (Fin (q + 1) -> Complex) :=
    openZeroConvexKernel (A.spatialLinearDomain ∩ B.spatialLinearDomain)
  have hABOpen : IsOpen (A.spatialLinearDomain ∩ B.spatialLinearDomain) :=
    A.spatialLinearDomain_open.inter B.spatialLinearDomain_open
  have hzeroAB : (0 : Fin (q + 1) -> Complex) ∈
      A.spatialLinearDomain ∩ B.spatialLinearDomain :=
    ⟨A.initialGramPolydisc_subset_spatialLinearDomain
        (SCV.center_mem_polydisc (fun _ => A.gram.gramRadius_pos)),
      B.initialGramPolydisc_subset_spatialLinearDomain
        (SCV.center_mem_polydisc (fun _ => B.gram.gramRadius_pos))⟩
  have hzeroU : (0 : Fin (q + 1) -> Complex) ∈ U :=
    zero_mem_openZeroConvexKernel hABOpen hzeroAB
  have hUOpen : IsOpen U := openZeroConvexKernel_open _
  have hUConnected : IsConnected U :=
    ((openZeroConvexKernel_starConvex _).isPathConnected hzeroU).isConnected
  have hAfield : DifferentiableOn Complex
      (fun w => A.gram.anchoredAtlasField
        A.sourceStage.stage A.sourceStage.germ base w) U := by
    apply (A.gram.anchoredAtlasField_holomorphic
      A.sourceStage.stage A.sourceStage.germ base).mono
    intro z hz
    exact (openZeroConvexKernel_subset _ hz).1.1
  have hBfield : DifferentiableOn Complex
      (fun w => B.gram.anchoredAtlasField
        B.sourceStage.stage B.sourceStage.germ
        (OSIIChapterV.uniformCompactTimeSourceMonoCLM hKL base) w) U := by
    apply (B.gram.anchoredAtlasField_holomorphic
      B.sourceStage.stage B.sourceStage.germ
      (OSIIChapterV.uniformCompactTimeSourceMonoCLM hKL base)).mono
    intro z hz
    exact (openZeroConvexKernel_subset _ hz).2.1
  intro z hz
  let v : OSHilbertSpace OS :=
    B.gram.anchoredAtlasField B.sourceStage.stage B.sourceStage.germ
        (OSIIChapterV.uniformCompactTimeSourceMonoCLM hKL base) z -
      A.gram.anchoredAtlasField
        A.sourceStage.stage A.sourceStage.germ base z
  have hF : DifferentiableOn Complex
      (fun w => (innerSL Complex v)
        (B.gram.anchoredAtlasField B.sourceStage.stage B.sourceStage.germ
          (OSIIChapterV.uniformCompactTimeSourceMonoCLM hKL base) w))
      U := by
    exact (differentiableOn_const (c := innerSL Complex v)).clm_apply hBfield
  have hG : DifferentiableOn Complex
      (fun w => (innerSL Complex v)
        (A.gram.anchoredAtlasField
          A.sourceStage.stage A.sourceStage.germ base w)) U := by
    exact (differentiableOn_const (c := innerSL Complex v)).clm_apply hAfield
  let V : Set (Fin (q + 1) -> Real) :=
    {x | (fun a => (x a : Complex)) ∈ U} ∩
      (A.gram.anchoredAtlasRealRegion
          A.sourceStage.stage A.sourceStage.germ ∩
        B.gram.anchoredAtlasRealRegion
          B.sourceStage.stage B.sourceStage.germ)
  have hVOpen : IsOpen V := by
    exact (hUOpen.preimage (by fun_prop)).inter
      ((A.gram.anchoredAtlasRealRegion_open
        A.sourceStage.stage A.sourceStage.germ).inter
        (B.gram.anchoredAtlasRealRegion_open
          B.sourceStage.stage B.sourceStage.germ))
  have hzeroV : (0 : Fin (q + 1) -> Real) ∈ V := by
    constructor
    · change
        (fun a => (((0 : Fin (q + 1) -> Real) a) : Complex)) ∈ U
      convert hzeroU using 1
      ext
      simp
    · exact ⟨mem_of_mem_nhds
          (A.gram.anchoredAtlasRealRegion_mem_nhds
            A.sourceStage.stage A.sourceStage.germ),
        mem_of_mem_nhds
          (B.gram.anchoredAtlasRealRegion_mem_nhds
            B.sourceStage.stage B.sourceStage.germ)⟩
  have hVsub : forall x, x ∈ V ->
      (fun a => (x a : Complex)) ∈ U := by
    intro x hx
    exact hx.1
  have hreal : forall x, x ∈ V ->
      (innerSL Complex v)
          (B.gram.anchoredAtlasField
            B.sourceStage.stage B.sourceStage.germ
            (OSIIChapterV.uniformCompactTimeSourceMonoCLM hKL base)
            (fun a => (x a : Complex))) =
        (innerSL Complex v)
          (A.gram.anchoredAtlasField
            A.sourceStage.stage A.sourceStage.germ base
            (fun a => (x a : Complex))) := by
    intro x hx
    have hvector :
        B.gram.anchoredAtlasField
            B.sourceStage.stage B.sourceStage.germ
            (OSIIChapterV.uniformCompactTimeSourceMonoCLM hKL base)
            (fun a => (x a : Complex)) =
          A.gram.anchoredAtlasField
            A.sourceStage.stage A.sourceStage.germ base
            (fun a => (x a : Complex)) := by
      rw [B.gram.anchoredAtlasField_realEdge
          B.sourceStage.stage B.sourceStage.germ
          (OSIIChapterV.uniformCompactTimeSourceMonoCLM hKL base)
          x hx.2.2,
        A.gram.anchoredAtlasField_realEdge
          A.sourceStage.stage A.sourceStage.germ base x hx.2.1]
      rfl
    rw [hvector]
  have hpair :
      (innerSL Complex v)
          (B.gram.anchoredAtlasField B.sourceStage.stage B.sourceStage.germ
            (OSIIChapterV.uniformCompactTimeSourceMonoCLM hKL base) z) =
        (innerSL Complex v)
          (A.gram.anchoredAtlasField
            A.sourceStage.stage A.sourceStage.germ base z) := by
    exact SCV.holomorphic_eq_of_eq_on_open_real_of_connected_finite
      hUOpen hUConnected hF hG hVOpen ⟨0, hzeroV⟩ hVsub hreal z hz
  have hpair' :
      @inner Complex (OSHilbertSpace OS) _ v
          (B.gram.anchoredAtlasField B.sourceStage.stage B.sourceStage.germ
            (OSIIChapterV.uniformCompactTimeSourceMonoCLM hKL base) z) =
        @inner Complex (OSHilbertSpace OS) _ v
          (A.gram.anchoredAtlasField
            A.sourceStage.stage A.sourceStage.germ base z) := by
    simpa [innerSL_apply_apply] using hpair
  have hv : @inner Complex (OSHilbertSpace OS) _ v v = 0 := by
    rw [show v =
      B.gram.anchoredAtlasField B.sourceStage.stage B.sourceStage.germ
          (OSIIChapterV.uniformCompactTimeSourceMonoCLM hKL base) z -
        A.gram.anchoredAtlasField
          A.sourceStage.stage A.sourceStage.germ base z by rfl]
    rw [inner_sub_right, hpair', sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hv)

end FixedAxisSplitUniformRankFieldData

namespace OSIIChapterV.ReflectedGramSpatialSourceData

variable {d q : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}
variable {C : Type*} [CanonicalGeneratorStageLevelProvider OS C]
variable {S : C}

set_option maxHeartbeats 1000000 in
/-- A stored reflected-Gram source field agrees with any holomorphic
translated field having the same real translated source, on the common
zero-based domain.  This is the choice-independent bridge from the retained
recursive canonical field to the source-native atlas. -/
theorem anchoredAtlasField_eq_holomorphicTranslationField_on_commonKernel
    (source : ReflectedGramSpatialSourceData (OS := OS) S q)
    {translatedSource :
      Nat -> (Fin (q + 1) -> Real) ->
        SchwartzMap (Section43SpatialSpace d ((q + 1) + 1)) Complex ->
          euclideanPositiveTimeSubmodule (d := d) ((q + 1) + 1)}
    (T : LocalReflectedA0HolomorphicTranslationFieldData
      OS ((q + 1) + 1) (q + 1) translatedSource)
    (sourceScale fieldScale : Nat)
    (chi : SchwartzMap
      (Section43SpatialSpace d ((q + 1) + 1)) Complex)
    (hsource : forall x,
      localPositiveTimeParameterTranslate
          (UniformCompactTimeSource.source (source.sourceCLM sourceScale chi))
          (fun r : Fin (q + 1) =>
            chronologicalTimeSourceDirection (d := d) r) x =
        translatedSource fieldScale x chi)
    (z : Fin (q + 1) -> Complex)
    (hz : z ∈ openZeroConvexKernel
      (source.reflectedGram.atlas.spatialLinearDomain ∩ T.domain)) :
    source.reflectedGram.atlas.gram.anchoredAtlasField
        source.reflectedGram.atlas.sourceStage.stage
        source.reflectedGram.atlas.sourceStage.germ
        (source.sourceCLM sourceScale chi) z =
      T.field fieldScale z chi := by
  let A := source.reflectedGram.atlas
  let U : Set (Fin (q + 1) -> Complex) :=
    openZeroConvexKernel (A.spatialLinearDomain ∩ T.domain)
  have hATOpen : IsOpen (A.spatialLinearDomain ∩ T.domain) :=
    A.spatialLinearDomain_open.inter T.domain_open
  have hzeroAT : (0 : Fin (q + 1) -> Complex) ∈
      A.spatialLinearDomain ∩ T.domain :=
    ⟨source.zero_mem_spatialLinearDomain, T.zero_mem_domain⟩
  have hzeroU : (0 : Fin (q + 1) -> Complex) ∈ U :=
    zero_mem_openZeroConvexKernel hATOpen hzeroAT
  have hUOpen : IsOpen U := openZeroConvexKernel_open _
  have hUConnected : IsConnected U :=
    ((openZeroConvexKernel_starConvex _).isPathConnected hzeroU).isConnected
  have hAfield : DifferentiableOn Complex
      (fun w => A.gram.anchoredAtlasField
        A.sourceStage.stage A.sourceStage.germ
        (source.sourceCLM sourceScale chi) w) U := by
    apply (A.gram.anchoredAtlasField_holomorphic
      A.sourceStage.stage A.sourceStage.germ
      (source.sourceCLM sourceScale chi)).mono
    intro w hw
    exact (openZeroConvexKernel_subset _ hw).1.1
  have hTfield : DifferentiableOn Complex
      (fun w => T.field fieldScale w chi) U := by
    apply (T.field_holomorphic fieldScale chi).mono
    intro w hw
    exact (openZeroConvexKernel_subset _ hw).2
  obtain ⟨W, hWsub, hWOpen, hzeroW⟩ := mem_nhds_iff.mp T.realRegion_nhds
  let V : Set (Fin (q + 1) -> Real) :=
    {x | (fun a => (x a : Complex)) ∈ U} ∩
      (A.gram.anchoredAtlasRealRegion
          A.sourceStage.stage A.sourceStage.germ ∩ W)
  have hVOpen : IsOpen V := by
    exact (hUOpen.preimage (by fun_prop)).inter
      ((A.gram.anchoredAtlasRealRegion_open
        A.sourceStage.stage A.sourceStage.germ).inter hWOpen)
  have hzeroV : (0 : Fin (q + 1) -> Real) ∈ V := by
    constructor
    · change
        (fun a => (((0 : Fin (q + 1) -> Real) a) : Complex)) ∈ U
      convert hzeroU using 1
      ext
      simp
    · exact ⟨mem_of_mem_nhds
          (A.gram.anchoredAtlasRealRegion_mem_nhds
            A.sourceStage.stage A.sourceStage.germ), hzeroW⟩
  have hVsub : forall x, x ∈ V ->
      (fun a => (x a : Complex)) ∈ U := by
    intro x hx
    exact hx.1
  let v : OSHilbertSpace OS :=
    A.gram.anchoredAtlasField
        A.sourceStage.stage A.sourceStage.germ
        (source.sourceCLM sourceScale chi) z -
      T.field fieldScale z chi
  have hF : DifferentiableOn Complex
      (fun w => (innerSL Complex v)
        (A.gram.anchoredAtlasField
          A.sourceStage.stage A.sourceStage.germ
          (source.sourceCLM sourceScale chi) w)) U := by
    exact (differentiableOn_const (c := innerSL Complex v)).clm_apply hAfield
  have hG : DifferentiableOn Complex
      (fun w => (innerSL Complex v) (T.field fieldScale w chi)) U := by
    exact (differentiableOn_const (c := innerSL Complex v)).clm_apply hTfield
  have hreal : forall x, x ∈ V ->
      (innerSL Complex v)
          (A.gram.anchoredAtlasField
            A.sourceStage.stage A.sourceStage.germ
            (source.sourceCLM sourceScale chi)
            (fun a => (x a : Complex))) =
        (innerSL Complex v) (T.field fieldScale
          (fun a => (x a : Complex)) chi) := by
    intro x hx
    have hvector :
        A.gram.anchoredAtlasField
            A.sourceStage.stage A.sourceStage.germ
            (source.sourceCLM sourceScale chi)
            (fun a => (x a : Complex)) =
          T.field fieldScale (fun a => (x a : Complex)) chi := by
      rw [A.gram.anchoredAtlasField_realEdge
          A.sourceStage.stage A.sourceStage.germ
          (source.sourceCLM sourceScale chi) x hx.2.1,
        T.realEdge fieldScale chi x (hWsub hx.2.2), hsource x]
    rw [hvector]
  have hpair :
      (innerSL Complex v)
          (A.gram.anchoredAtlasField
            A.sourceStage.stage A.sourceStage.germ
            (source.sourceCLM sourceScale chi) z) =
        (innerSL Complex v) (T.field fieldScale z chi) := by
    exact SCV.holomorphic_eq_of_eq_on_open_real_of_connected_finite
      hUOpen hUConnected hF hG hVOpen ⟨0, hzeroV⟩ hVsub hreal z hz
  have hpair' :
      @inner Complex (OSHilbertSpace OS) _ v
          (A.gram.anchoredAtlasField
            A.sourceStage.stage A.sourceStage.germ
            (source.sourceCLM sourceScale chi) z) =
        @inner Complex (OSHilbertSpace OS) _ v
          (T.field fieldScale z chi) := by
    simpa [innerSL_apply_apply] using hpair
  have hv : @inner Complex (OSHilbertSpace OS) _ v v = 0 := by
    rw [show v =
      A.gram.anchoredAtlasField
          A.sourceStage.stage A.sourceStage.germ
          (source.sourceCLM sourceScale chi) z -
        T.field fieldScale z chi by rfl]
    rw [inner_sub_right, hpair', sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hv)

end OSIIChapterV.ReflectedGramSpatialSourceData

namespace OSIIStep4MultiGapUniformCommonSlopeData
namespace FixedAxisSplitUniformTargetCutoffHullData

open OSIIChapterV
open OSIIChapterV.Section43ProductTimeApproximateIdentity
open OSIIChapterV.Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData

variable {d q depth rank : Nat} [NeZero d]
variable {OS : OsterwalderSchraderAxioms d}
variable {C : Type*}
variable [OSIIChapterV.CanonicalGeneratorStageLevelProvider OS C]
variable {S : C}

namespace SourceRadialDomainData

end SourceRadialDomainData

namespace CompactSourceRadialDomainData

end CompactSourceRadialDomainData

namespace SourceCommonCutoffHullData

end SourceCommonCutoffHullData

namespace CanonicalSourceRadialSingletonSegmentKernelData

end CanonicalSourceRadialSingletonSegmentKernelData

end FixedAxisSplitUniformTargetCutoffHullData
end OSIIStep4MultiGapUniformCommonSlopeData
end OSReconstruction
