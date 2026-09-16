/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPartialKernelE0Source
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialLocalMeanValue
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIRegularizationRadius
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairPhysicalBlockPatch
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReduced
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialProductBasepointSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReducedTestLiftSupport
import OSReconstruction.ComplexLieGroups.AdjacentOverlapWitness
import OSReconstruction.ComplexLieGroups.Connectedness.PermutedTube
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanTubeIdentity
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.IndexSetD1
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValuesBase
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOrderedPositiveTimeTopology
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.EdgeDistribution
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceExtension
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.Adjacency
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValues
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import OSReconstruction.SCV.IdentityTheorem
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.Thickening
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOriented
import OSReconstruction.SCV.EuclideanWeylOpen



















noncomputable section

open Complex MeasureTheory Set
open scoped Classical

namespace OSReconstruction

private theorem tsupport_precomp_subset_realEdge
    {X Y alpha : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Zero alpha]
    {f : Y → alpha} {h : X → Y} (hh : Continuous h) :
    tsupport (fun x => f (h x)) ⊆ h ⁻¹' tsupport f := by
  refine closure_minimal ?_ ((isClosed_tsupport _).preimage hh)
  intro x hx
  exact subset_closure (by simpa [Function.mem_support] using hx)

private theorem normalizedSpatialBasepointCutoff_hasCompactSupport
    (d : Nat) :
    HasCompactSupport
      ((OSIIChapterV.normalizedSpatialBasepointCutoff d).toSchwartz :
        (Fin d → Real) → Complex) := by
  let h :=
    SCV.exists_normalized_schwartz_bump_kernelSupportWithin
      (m := d) 1 (by norm_num)
  have hsupp :
      tsupport ((Classical.choose h : SchwartzMap (Fin d → Real) Complex) :
        (Fin d → Real) → Complex) ⊆ Metric.closedBall 0 1 :=
    (Classical.choose_spec h).2.2.2
  change HasCompactSupport
    ((Classical.choose h : SchwartzMap (Fin d → Real) Complex) :
      (Fin d → Real) → Complex)
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Fin d → Real) 1) ?_
  intro x hx
  exact hsupp (subset_tsupport _ hx)

/-- A normalized spacetime basepoint cutoff whose Euclidean time support is
strictly positive. -/
noncomputable def osiiStep4PositiveTimeBasepointCutoff
    (d : Nat) [NeZero d] : BHW.NormalizedBasepointCutoff d := by
  let chi : SchwartzMap (SpacetimeDim d) Complex :=
    SCV.prependField
      OSIIChapterV.normalizedPositiveTimeBasepointCutoff.f
      (OSIIChapterV.normalizedSpatialBasepointCutoff d).toSchwartz
  refine { toSchwartz := chi, integral_eq_one := ?_ }
  have hslice :
      SCV.sliceIntegral chi =
        (OSIIChapterV.normalizedSpatialBasepointCutoff d).toSchwartz := by
    exact SCV.sliceIntegral_prependField_eq_self
      OSIIChapterV.normalizedPositiveTimeBasepointCutoff.f
      (OSIIChapterV.normalizedSpatialBasepointCutoff d).toSchwartz
      OSIIChapterV.normalizedPositiveTimeBasepointCutoff_integral_eq_one
  have hint := SCV.integral_sliceIntegral chi
  rw [hslice] at hint
  exact
    (show
      (SchwartzMap.integralCLM Complex
        (volume : Measure (SpacetimeDim d))) chi = 1 by
      rw [← hint]
      exact (OSIIChapterV.normalizedSpatialBasepointCutoff d).integral_eq_one)

theorem osiiStep4PositiveTimeBasepointCutoff_time_pos
    (d : Nat) [NeZero d]
    (x : SpacetimeDim d)
    (hx : x ∈ tsupport
      ((osiiStep4PositiveTimeBasepointCutoff d).toSchwartz :
        SpacetimeDim d → Complex)) :
    0 < x 0 := by
  have hprod :
      x ∈ tsupport (fun u : SpacetimeDim d =>
        OSIIChapterV.normalizedPositiveTimeBasepointCutoff.f (u 0) *
          (OSIIChapterV.normalizedSpatialBasepointCutoff d).toSchwartz
            (fun j => u j.succ)) := by
    change x ∈ tsupport (fun u : SpacetimeDim d =>
      OSIIChapterV.normalizedPositiveTimeBasepointCutoff.f (u 0) *
        (OSIIChapterV.normalizedSpatialBasepointCutoff d).toSchwartz
          (fun j => u j.succ)) at hx
    exact hx
  have hheadPre :
      x ∈ tsupport (fun u : SpacetimeDim d =>
        OSIIChapterV.normalizedPositiveTimeBasepointCutoff.f (u 0)) :=
    tsupport_mul_subset_left hprod
  have hhead :
      x 0 ∈ tsupport
        (OSIIChapterV.normalizedPositiveTimeBasepointCutoff.f : Real → Complex) :=
    tsupport_precomp_subset_realEdge
      (f := (OSIIChapterV.normalizedPositiveTimeBasepointCutoff.f : Real → Complex))
      (h := fun u : SpacetimeDim d => u 0)
      (by simpa using
        (continuous_apply (0 : Fin (d + 1)) :
          Continuous (fun u : SpacetimeDim d => u 0))) hheadPre
  exact OSIIChapterV.normalizedPositiveTimeBasepointCutoff.positive hhead

theorem osiiStep4PositiveTimeBasepointCutoff_hasCompactSupport
    (d : Nat) [NeZero d] :
    HasCompactSupport
      ((osiiStep4PositiveTimeBasepointCutoff d).toSchwartz :
        SpacetimeDim d → Complex) := by
  have hcompact :=
    hasCompactSupport_prependField
      OSIIChapterV.normalizedPositiveTimeBasepointCutoff.f
      (OSIIChapterV.normalizedSpatialBasepointCutoff d).toSchwartz
      OSIIChapterV.normalizedPositiveTimeBasepointCutoff.compact
      (normalizedSpatialBasepointCutoff_hasCompactSupport d)
  change HasCompactSupport (fun u : SpacetimeDim d =>
    OSIIChapterV.normalizedPositiveTimeBasepointCutoff.f (u 0) *
      (OSIIChapterV.normalizedSpatialBasepointCutoff d).toSchwartz
        (fun j => u j.succ))
  exact hcompact

/-- The centered reduced block kernel lifted with the positive-time normalized
basepoint cutoff. -/
noncomputable def
    osiiStep4PositiveLiftedCenteredPartialConvolutionKernelFullSource
    (d k : Nat) [NeZero d] {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) → Real) :
    SchwartzNPoint d (k + 1) :=
  BHW.reducedTestLift k d
    (osiiStep4PositiveTimeBasepointCutoff d).toSchwartz
    (osiiStep4CenteredPartialConvolutionKernelFullSource
      d k hrho center y y')

/-- At a fixed real center, the positive-basepoint lift varies continuously
with both imaginary regularizer variables. -/
theorem
    continuous_osiiStep4PositiveLiftedCenteredPartialConvolutionKernelFullSource
    (d k : Nat) [NeZero d] {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) → Real) :
    Continuous
      (fun p :
          (Fin (k * (d + 1)) → Real) ×
            (Fin (k * (d + 1)) → Real) =>
        osiiStep4PositiveLiftedCenteredPartialConvolutionKernelFullSource
          d k hrho center p.1 p.2) := by
  exact
    (BHW.reducedTestLift k d
      (osiiStep4PositiveTimeBasepointCutoff d).toSchwartz).continuous.comp
        (continuous_osiiStep4CenteredPartialConvolutionKernelFullSource
          d k hrho center)

private theorem reducedTestLift_tsupport_basepoint_mem_realEdge
    (d m : Nat)
    (chi : SchwartzMap (SpacetimeDim d) Complex)
    (phi : SchwartzNPoint d m)
    (x : NPointDomain d (m + 1))
    (hx : x ∈ tsupport
      ((BHW.reducedTestLift m d chi phi : SchwartzNPoint d (m + 1)) :
        NPointDomain d (m + 1) → Complex)) :
    x 0 ∈ tsupport (chi : SpacetimeDim d → Complex) := by
  have hprod :
      x ∈ tsupport (fun u : NPointDomain d (m + 1) =>
        chi (u 0) * phi (BHW.reducedDiffMapReal (m + 1) d u)) := by
    change x ∈ tsupport (fun u : NPointDomain d (m + 1) =>
      chi (u 0) * phi (BHW.reducedDiffMapReal (m + 1) d u)) at hx
    exact hx
  have hheadPre :
      x ∈ tsupport (fun u : NPointDomain d (m + 1) => chi (u 0)) :=
    tsupport_mul_subset_left hprod
  exact tsupport_precomp_subset_realEdge
    (f := (chi : SpacetimeDim d → Complex))
    (h := fun u : NPointDomain d (m + 1) => u 0)
    (by simpa using
      (continuous_apply (0 : Fin (m + 1)) :
        Continuous (fun u : NPointDomain d (m + 1) => u 0))) hheadPre

/-- The positive-basepoint lift is carried by the absolute ordered
positive-time sector. -/
theorem
    osiiStep4PositiveLiftedCenteredPartialConvolutionKernel_tsupport_ordered
    (d k : Nat) [NeZero d] {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) → Real)
    (hcenter : ∀ i : Fin k,
      rho / 2 ≤ center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    tsupport
        ((osiiStep4PositiveLiftedCenteredPartialConvolutionKernelFullSource
          d k hrho center y y' : SchwartzNPoint d (k + 1)) :
            NPointDomain d (k + 1) → Complex) ⊆
      OrderedPositiveTimeRegion d (k + 1) := by
  intro x hx
  let phi : SchwartzNPoint d k :=
    osiiStep4CenteredPartialConvolutionKernelFullSource
      d k hrho center y y'
  have hred :
      BHW.reducedDiffMapReal (k + 1) d x ∈
        tsupport (phi : NPointDomain d k → Complex) := by
    exact reducedTestLift_tsupport_subset_reducedDiff_preimage_tsupport
      (osiiStep4PositiveTimeBasepointCutoff d).toSchwartz phi hx
  have hgap : ∀ i : Fin k, 0 < x i.succ 0 - x i.castSucc 0 := by
    intro i
    have hpos :=
      osiiStep4CenteredPartialConvolutionKernelFullSource_reduced_time_pos
        d k hrho center y y' hcenter
          (BHW.reducedDiffMapReal (k + 1) d x) hred i
    rw [BHW.reducedDiffMapReal_apply] at hpos
    exact hpos
  have hmono : StrictMono (fun i : Fin (k + 1) => x i 0) := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    exact sub_pos.mp (hgap i)
  have hbase : 0 < x 0 0 := by
    apply osiiStep4PositiveTimeBasepointCutoff_time_pos d (x 0)
    exact reducedTestLift_tsupport_basepoint_mem_realEdge d k
      (osiiStep4PositiveTimeBasepointCutoff d).toSchwartz phi x hx
  intro i
  constructor
  · exact hbase.trans_le (hmono.monotone (Fin.zero_le i))
  · intro j hij
    exact hmono hij

/-- Any basepoint lift of this reduced kernel has the compact strict-positive
reduced-time support needed for cutoff independence. -/
theorem
    osiiStep4CenteredPartialConvolutionKernel_reducedTestLift_compactPositiveSupport
    (d k : Nat) [NeZero d]
    (chi : SchwartzMap (SpacetimeDim d) Complex)
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) → Real)
    (hcenter : ∀ i : Fin k,
      rho / 2 ≤ center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    OSIIChapterV.HasCompactStrictPositiveReducedTimeSupport
      (BHW.reducedTestLift k d chi
        (osiiStep4CenteredPartialConvolutionKernelFullSource
          d k hrho center y y')) := by
  let phi : SchwartzNPoint d k :=
    osiiStep4CenteredPartialConvolutionKernelFullSource
      d k hrho center y y'
  let K : Set (Fin k → Real) :=
    section43QTimeCLM d k '' tsupport (phi : NPointDomain d k → Complex)
  have hphiCompact :
      IsCompact (tsupport (phi : NPointDomain d k → Complex)) :=
    (osiiStep4CenteredPartialConvolutionKernelFullSource_hasCompactSupport
      d k hrho center y y').isCompact
  refine ⟨K, hphiCompact.image (section43QTimeCLM d k).continuous, ?_, ?_⟩
  · intro tau htau i
    rcases htau with ⟨xi, hxi, rfl⟩
    change 0 < xi i 0
    exact osiiStep4CenteredPartialConvolutionKernelFullSource_reduced_time_pos
      d k hrho center y y' hcenter xi hxi i
  · intro x hx
    have hred :
        BHW.reducedDiffMapReal (k + 1) d x ∈
          tsupport (phi : NPointDomain d k → Complex) := by
      exact reducedTestLift_tsupport_subset_reducedDiff_preimage_tsupport
        chi phi hx
    refine ⟨BHW.reducedDiffMapReal (k + 1) d x, hred, ?_⟩
    simp [OSIIChapterV.reducedTimeProjectionCLM_apply,
      section43QTimeCLM_apply]

/-- The positive-basepoint lifted source as an honest zero-diagonal Euclidean
test. -/
noncomputable def
    osiiStep4PositiveLiftedCenteredPartialConvolutionKernelZeroDiagonal
    (d k : Nat) [NeZero d] {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) → Real)
    (hcenter : ∀ i : Fin k,
      rho / 2 ≤ center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    ZeroDiagonalSchwartz d (k + 1) :=
  ⟨osiiStep4PositiveLiftedCenteredPartialConvolutionKernelFullSource
      d k hrho center y y',
    VanishesToInfiniteOrderOnCoincidence_of_support_subset_orderedPositiveTimeRegion
      (osiiStep4PositiveLiftedCenteredPartialConvolutionKernelFullSource
        d k hrho center y y')
      (osiiStep4PositiveLiftedCenteredPartialConvolutionKernel_tsupport_ordered
        d k hrho center y y' hcenter)⟩

end OSReconstruction
