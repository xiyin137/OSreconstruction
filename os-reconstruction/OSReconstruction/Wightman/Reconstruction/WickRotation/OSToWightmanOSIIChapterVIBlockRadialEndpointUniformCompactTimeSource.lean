/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialDifferenceTimeProjection
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialChronologicalCover
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVUniformCompactTimeAnchoredSeed











noncomputable section

open Complex Metric Set Topology
open scoped Classical

namespace OSReconstruction

variable {d k : Nat} [NeZero d]

/-- Imaginary endpoint and the two reduced radial parameters of an endpoint
source. -/
abbrev OSIIStep4RadialEndpointSourceParameter (d k : Nat) :=
  SpacetimeDim d ×
    ((Fin (k * (d + 1)) -> Real) ×
      (Fin (k * (d + 1)) -> Real))

/-- The fixed-center radial endpoint source as a single parameterized
Schwartz family. -/
noncomputable def osiiStep4RadialEndpointSourceFamily
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (endpointCenter : SpacetimeDim d)
    (center : Fin (k * (d + 1)) -> Real)
    (p : OSIIStep4RadialEndpointSourceParameter d k) :
    SchwartzNPoint d (k + 1) :=
  osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource
    d k hrho endpointCenter p.1 center p.2.1 p.2.2

/-- One compact absolute-coordinate carrier for every radial endpoint source
at fixed real endpoint and reduced centers. -/
noncomputable def osiiStep4RadialEndpointCommonCarrier
    (d k : Nat) [NeZero d]
    (rho : Real)
    (endpointCenter : SpacetimeDim d)
    (center : Fin (k * (d + 1)) -> Real) :
    Set (NPointDomain d (k + 1)) :=
  (fun p : SpacetimeDim d × NPointDomain d k =>
    (BHW.realDiffCoordCLE (k + 1) d).symm
      (BHW.prependBasepointReal d k p.1 p.2)) ''
    (Metric.closedBall endpointCenter (rho / 8) ×ˢ
      osiiStep4CenteredPartialKernelCommonReducedCarrier
        d k rho center)

/-- Shrinking the radial scale shrinks the common absolute endpoint
carrier. -/
theorem osiiStep4RadialEndpointCommonCarrier_mono
    (d k : Nat) [NeZero d]
    {sigma rho : Real} (hscale : sigma <= rho)
    (endpointCenter : SpacetimeDim d)
    (center : Fin (k * (d + 1)) -> Real) :
    osiiStep4RadialEndpointCommonCarrier
        d k sigma endpointCenter center ⊆
      osiiStep4RadialEndpointCommonCarrier
        d k rho endpointCenter center := by
  rintro _ ⟨p, hp, rfl⟩
  refine ⟨p, ⟨?_, ?_⟩, rfl⟩
  · exact Metric.closedBall_subset_closedBall (by linarith) hp.1
  · exact osiiStep4CenteredPartialKernelCommonReducedCarrier_mono
      d k hscale center hp.2

theorem osiiStep4RadialEndpointCommonCarrier_isCompact
    (d k : Nat) [NeZero d]
    (rho : Real)
    (endpointCenter : SpacetimeDim d)
    (center : Fin (k * (d + 1)) -> Real) :
    IsCompact
      (osiiStep4RadialEndpointCommonCarrier
        d k rho endpointCenter center) := by
  exact
    ((isCompact_closedBall endpointCenter (rho / 8)).prod
      (osiiStep4CenteredPartialKernelCommonReducedCarrier_isCompact
        d k rho center)).image
      OSIIChapterV.continuous_reducedTestLiftReconstruction

private theorem reducedTestLift_tsupport_basepoint_mem_endpointCarrier
    (d m : Nat)
    (chi : SchwartzMap (SpacetimeDim d) Complex)
    (phi : SchwartzNPoint d m)
    (x : NPointDomain d (m + 1))
    (hx : x ∈ tsupport
      ((BHW.reducedTestLift m d chi phi : SchwartzNPoint d (m + 1)) :
        NPointDomain d (m + 1) -> Complex)) :
    x 0 ∈ tsupport (chi : SpacetimeDim d -> Complex) := by
  have hprod :
      x ∈ tsupport (fun u : NPointDomain d (m + 1) =>
        chi (u 0) * phi (BHW.reducedDiffMapReal (m + 1) d u)) := by
    have hfun :
        ((BHW.reducedTestLift m d chi phi : SchwartzNPoint d (m + 1)) :
            NPointDomain d (m + 1) -> Complex) =
          fun u => chi (u 0) * phi (BHW.reducedDiffMapReal (m + 1) d u) := by
      funext u
      exact BHW.reducedTestLift_apply m d chi phi u
    rwa [hfun] at hx
  have hheadPre :
      x ∈ tsupport (fun u : NPointDomain d (m + 1) => chi (u 0)) :=
    tsupport_mul_subset_left hprod
  exact tsupport_comp_subset_preimage
    (chi : SpacetimeDim d -> Complex)
    (f := fun u : NPointDomain d (m + 1) => u 0)
    (continuous_apply 0) hheadPre

/-- Every member of the radial endpoint source family is supported in the
same compact absolute carrier. -/
theorem osiiStep4RadialEndpointSourceFamily_tsupport_subset_commonCarrier
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (endpointCenter : SpacetimeDim d)
    (center : Fin (k * (d + 1)) -> Real)
    (p : OSIIStep4RadialEndpointSourceParameter d k) :
    tsupport
        ((osiiStep4RadialEndpointSourceFamily
          d k hrho endpointCenter center p : SchwartzNPoint d (k + 1)) :
            NPointDomain d (k + 1) -> Complex) ⊆
      osiiStep4RadialEndpointCommonCarrier
        d k rho endpointCenter center := by
  intro x hx
  let chi : SchwartzMap (SpacetimeDim d) Complex :=
    osiiStep4CenteredComplexBlockRadialGRealSchwartz
      (d + 1) hrho endpointCenter p.1
  let phi : SchwartzNPoint d k :=
    osiiStep4CenteredPartialConvolutionKernelFullSource
      d k hrho center p.2.1 p.2.2
  have hbase : x 0 ∈ tsupport (chi : SpacetimeDim d -> Complex) := by
    exact reducedTestLift_tsupport_basepoint_mem_endpointCarrier
      d k chi phi x hx
  have hbaseCarrier :
      x 0 ∈ Metric.closedBall endpointCenter (rho / 8) := by
    exact
      osiiStep4CenteredComplexBlockRadialGRealSchwartz_tsupport_subset_closedBall
        (d + 1) hrho endpointCenter p.1 hbase
  have hred :
      BHW.reducedDiffMapReal (k + 1) d x ∈
        tsupport (phi : NPointDomain d k -> Complex) := by
    exact reducedTestLift_tsupport_subset_reducedDiff_preimage_tsupport
      chi phi hx
  have hredCarrier :
      BHW.reducedDiffMapReal (k + 1) d x ∈
        osiiStep4CenteredPartialKernelCommonReducedCarrier
          d k rho center := by
    exact
      osiiStep4CenteredPartialConvolutionKernelFullSource_tsupport_subset_commonReducedCarrier
        d k hrho center p.2.1 p.2.2 hred
  refine ⟨(x 0, BHW.reducedDiffMapReal (k + 1) d x),
    ⟨hbaseCarrier, hredCarrier⟩, ?_⟩
  exact OSIIChapterV.realDiffCoordCLE_symm_prependBasepointReal_self x

/-- The radial endpoint source is compactly supported.  This theorem is a
direct consequence of the common absolute carrier and is kept at the same
endpoint layer as that carrier. -/
theorem
    osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernel_hasCompactSupport
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (endpointCenter endpointImag : SpacetimeDim d)
    (center y y' : Fin (k * (d + 1)) -> Real) :
    HasCompactSupport
      ((osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource
        d k hrho endpointCenter endpointImag center y y' :
          SchwartzNPoint d (k + 1)) :
        NPointDomain d (k + 1) -> Complex) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (osiiStep4RadialEndpointCommonCarrier_isCompact
      d k rho endpointCenter center)
  intro x hx
  apply osiiStep4RadialEndpointSourceFamily_tsupport_subset_commonCarrier
    d k hrho endpointCenter center (endpointImag, (y, y'))
  exact subset_closure hx

/-- The common endpoint carrier remains strictly chronological; the endpoint
carrier itself does not affect the positive-gap argument. -/
theorem osiiStep4RadialEndpointCommonCarrier_ordered
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (endpointCenter : SpacetimeDim d)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    ∀ x ∈ osiiStep4RadialEndpointCommonCarrier
        d k rho endpointCenter center,
      forall i j : Fin (k + 1), i < j -> x i 0 < x j 0 := by
  rintro x ⟨p, hp, rfl⟩
  have hgap : forall i : Fin k,
      0 <
        (BHW.realDiffCoordCLE (k + 1) d).symm
              (BHW.prependBasepointReal d k p.1 p.2) i.succ 0 -
          (BHW.realDiffCoordCLE (k + 1) d).symm
              (BHW.prependBasepointReal d k p.1 p.2) i.castSucc 0 := by
    intro i
    have hpos := osiiStep4CommonReducedCarrier_time_pos
      d k hrho center hcenter p.2 hp.2 i
    have hred :=
      BHW.reducedDiffMapReal_realDiffCoordCLE_symm_prependBasepointReal
        d k p.1 p.2
    have hcoord := congrFun (congrFun hred i) (0 : Fin (d + 1))
    change
      (BHW.realDiffCoordCLE (k + 1) d).symm
            (BHW.prependBasepointReal d k p.1 p.2) i.succ 0 -
        (BHW.realDiffCoordCLE (k + 1) d).symm
            (BHW.prependBasepointReal d k p.1 p.2) i.castSucc 0 =
          p.2 i 0 at hcoord
    linarith
  have hmono : StrictMono
      (fun i : Fin (k + 1) =>
        (BHW.realDiffCoordCLE (k + 1) d).symm
          (BHW.prependBasepointReal d k p.1 p.2) i 0) := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    exact sub_pos.mp (hgap i)
  intro i j hij
  exact hmono hij

private theorem endpointCarrier_time_pos
    (d : Nat) {rho : Real} (hrho : 0 < rho)
    (endpointCenter x : SpacetimeDim d)
    (hEndpointCenter : rho / 4 <= endpointCenter 0)
    (hx : x ∈ Metric.closedBall endpointCenter (rho / 8)) :
    0 < x 0 := by
  have hnorm : norm (x - endpointCenter) <= rho / 8 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  have hcoord : abs (x 0 - endpointCenter 0) <= rho / 8 := by
    calc
      abs (x 0 - endpointCenter 0) = norm ((x - endpointCenter) 0) := by
        simp [Real.norm_eq_abs]
      _ <= norm (x - endpointCenter) := norm_le_pi_norm _ 0
      _ <= rho / 8 := hnorm
  nlinarith [abs_le.mp hcoord |>.1]

/-- Positivity of the endpoint center and of all reduced-gap centers makes
the entire common carrier ordered and positive. -/
theorem osiiStep4RadialEndpointCommonCarrier_orderedPositive
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (endpointCenter : SpacetimeDim d)
    (center : Fin (k * (d + 1)) -> Real)
    (hEndpointCenter : rho / 4 <= endpointCenter 0)
    (hcenter : forall i : Fin k,
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    osiiStep4RadialEndpointCommonCarrier
        d k rho endpointCenter center ⊆
      OrderedPositiveTimeRegion d (k + 1) := by
  intro x hx
  have hordered := osiiStep4RadialEndpointCommonCarrier_ordered
    d k hrho endpointCenter center hcenter x hx
  rcases hx with ⟨p, hp, rfl⟩
  have hbase : 0 < p.1 0 :=
    endpointCarrier_time_pos d hrho endpointCenter p.1
      hEndpointCenter hp.1
  have hzero :
      (BHW.realDiffCoordCLE (k + 1) d).symm
          (BHW.prependBasepointReal d k p.1 p.2) 0 0 = p.1 0 := by
    rw [BHW.realDiffCoordCLE_symm_apply]
    change (∑ j : Fin 1,
      BHW.prependBasepointReal d k p.1 p.2 ⟨j.val, by omega⟩ 0) = p.1 0
    rw [Fin.sum_univ_one]
    simp [BHW.prependBasepointReal]
  intro i
  constructor
  · by_cases hi : i = 0
    · subst i
      change 0 < (BHW.realDiffCoordCLE (k + 1) d).symm
        (BHW.prependBasepointReal d k p.1 p.2) 0 0
      rw [hzero]
      exact hbase
    · have h0i : (0 : Fin (k + 1)) < i := Fin.pos_iff_ne_zero.mpr hi
      have hlt := hordered 0 i h0i
      change
        (BHW.realDiffCoordCLE (k + 1) d).symm
              (BHW.prependBasepointReal d k p.1 p.2) 0 0 <
          (BHW.realDiffCoordCLE (k + 1) d).symm
              (BHW.prependBasepointReal d k p.1 p.2) i 0 at hlt
      rw [hzero] at hlt
      exact hbase.trans hlt
  · intro j hij
    exact hordered i j hij

/-- The difference-time projection of the common absolute endpoint carrier. -/
noncomputable def osiiStep4RadialEndpointTimeCarrier
    (d k : Nat) [NeZero d]
    (rho : Real)
    (endpointCenter : SpacetimeDim d)
    (center : Fin (k * (d + 1)) -> Real) :
    Set (Fin (k + 1) -> Real) :=
  osiiStep4FullDifferenceTimeProjectionCLM d k ''
    osiiStep4RadialEndpointCommonCarrier
      d k rho endpointCenter center

/-- The complete radial endpoint source, retaining its common compact
strict-positive time carrier in the source type. -/
noncomputable def osiiStep4RadialEndpointUniformCompactTimeSource
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (endpointCenter : SpacetimeDim d)
    (center : Fin (k * (d + 1)) -> Real)
    (hEndpointCenter : rho / 4 <= endpointCenter 0)
    (hcenter : forall i : Fin k,
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (p : OSIIStep4RadialEndpointSourceParameter d k) :
    OSIIChapterV.UniformCompactTimeSource d (k + 1)
      (osiiStep4RadialEndpointTimeCarrier
        d k rho endpointCenter center) := by
  let f := osiiStep4RadialEndpointSourceFamily
    d k hrho endpointCenter center p
  have hf_positive :
      tsupport (f : NPointDomain d (k + 1) -> Complex) ⊆
        OrderedPositiveTimeRegion d (k + 1) := by
    exact
      osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernel_tsupport_ordered
        d k hrho endpointCenter p.1 center p.2.1 p.2.2
          hEndpointCenter hcenter
  refine ⟨⟨f, hf_positive⟩, ?_⟩
  intro x hx
  change
    osiiStep4FullDifferenceTimeProjectionCLM d k x ∈
      osiiStep4RadialEndpointTimeCarrier
        d k rho endpointCenter center
  exact ⟨x,
    osiiStep4RadialEndpointSourceFamily_tsupport_subset_commonCarrier
      d k hrho endpointCenter center p hx,
    rfl⟩

@[simp] theorem
    osiiStep4RadialEndpointUniformCompactTimeSource_source_coe
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (endpointCenter : SpacetimeDim d)
    (center : Fin (k * (d + 1)) -> Real)
    (hEndpointCenter : rho / 4 <= endpointCenter 0)
    (hcenter : forall i : Fin k,
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (p : OSIIStep4RadialEndpointSourceParameter d k) :
    (OSIIChapterV.UniformCompactTimeSource.source
      (osiiStep4RadialEndpointUniformCompactTimeSource
        d k hrho endpointCenter center hEndpointCenter hcenter p)).1 =
      osiiStep4RadialEndpointSourceFamily
        d k hrho endpointCenter center p :=
  rfl

end OSReconstruction
