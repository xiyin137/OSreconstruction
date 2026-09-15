/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVChronologicalCompactCover
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReducedTestLiftRepresentative
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPartialKernelRealEdge
















noncomputable section

open Complex Metric Set Topology
open scoped Classical

namespace OSReconstruction

variable {d k : Nat} [NeZero d] [NeZero k]

/-- A finite family of continuous localization operators subordinate to
chronological product carriers.  The sum identity is required only for
sources supported in the retained compact carrier `K`. -/
structure OSIIChronologicalCompactLocalizationData
    (d k : Nat) [NeZero d] [NeZero k]
    (K : Set (NPointDomain d (k + 1))) where
  index : Type
  indexFintype : Fintype index
  piece :
    index →
      SchwartzNPoint d (k + 1) →L[Complex]
        SchwartzNPoint d (k + 1)
  carrier : index → OSIIChronologicalCompactFactors d k
  sum_eq :
    forall f : SchwartzNPoint d (k + 1),
      tsupport (f : NPointDomain d (k + 1) → Complex) ⊆ K →
        f = (@Finset.univ index indexFintype).sum fun a => piece a f
  carrier_fix :
    forall a f,
      SchwartzMap.smulLeftCLM Complex
          (SchwartzMap.productTensor (carrier a).factors)
          (piece a f) =
        piece a f

namespace OSIIChronologicalCompactLocalizationData

end OSIIChronologicalCompactLocalizationData

/-- One compact reduced carrier containing the support of every centered
partial kernel at the fixed center and radius. -/
def osiiStep4CenteredPartialKernelCommonReducedCarrier
    (d k : Nat) (rho : Real)
    (center : Fin (k * (d + 1)) -> Real) :
    Set (NPointDomain d k) :=
  (flattenCLEquivReal k (d + 1)).symm ''
    Metric.closedBall center (rho / 4)

/-- Shrinking the radial scale shrinks the common reduced carrier. -/
theorem osiiStep4CenteredPartialKernelCommonReducedCarrier_mono
    (d k : Nat) {sigma rho : Real} (hscale : sigma <= rho)
    (center : Fin (k * (d + 1)) -> Real) :
    osiiStep4CenteredPartialKernelCommonReducedCarrier d k sigma center ⊆
      osiiStep4CenteredPartialKernelCommonReducedCarrier d k rho center := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨x, ?_, rfl⟩
  exact Metric.closedBall_subset_closedBall (by linarith) hx

theorem osiiStep4CenteredPartialKernelCommonReducedCarrier_isCompact
    (d k : Nat) (rho : Real)
    (center : Fin (k * (d + 1)) -> Real) :
    IsCompact
      (osiiStep4CenteredPartialKernelCommonReducedCarrier
        d k rho center) := by
  exact (isCompact_closedBall center (rho / 4)).image
    (flattenCLEquivReal k (d + 1)).symm.continuous

/-- Every centered reduced partial-kernel source lies in the common reduced
carrier determined only by its fixed center and radius. -/
theorem
    osiiStep4CenteredPartialConvolutionKernelFullSource_tsupport_subset_commonReducedCarrier
    (d k : Nat) {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) -> Real) :
    tsupport
        ((osiiStep4CenteredPartialConvolutionKernelFullSource
          d k hrho center y y' : SchwartzNPoint d k) :
            NPointDomain d k -> Complex) ⊆
      osiiStep4CenteredPartialKernelCommonReducedCarrier d k rho center := by
  intro xi hxi
  have hball :
      osiiStep4NPointFlatCLM d k xi ∈
        Metric.closedBall center (rho / 4) :=
    osiiStep4CenteredPartialConvolutionKernelFullSource_tsupport_flat_mem_closedBall
      d k hrho center y y' xi hxi
  refine ⟨osiiStep4NPointFlatCLM d k xi, hball, ?_⟩
  simpa [osiiStep4NPointFlatCLM] using
    (flattenCLEquivReal k (d + 1)).symm_apply_apply xi

/-- The compact absolute-coordinate carrier obtained from the fixed positive
basepoint cutoff and the common reduced support ball. -/
noncomputable def osiiStep4PositiveLiftedCenteredPartialKernelCommonCarrier
    (d k : Nat) [NeZero d]
    (rho : Real)
    (center : Fin (k * (d + 1)) -> Real) :
    Set (NPointDomain d (k + 1)) :=
  OSIIChapterV.reducedTestLiftFullCarrier
    (osiiStep4PositiveTimeBasepointCutoff d)
    (osiiStep4CenteredPartialKernelCommonReducedCarrier
      d k rho center)

/-- Positive-basepoint lifting preserves radial-scale carrier
monotonicity. -/
theorem osiiStep4PositiveLiftedCenteredPartialKernelCommonCarrier_mono
    (d k : Nat) [NeZero d]
    {sigma rho : Real} (hscale : sigma <= rho)
    (center : Fin (k * (d + 1)) -> Real) :
    osiiStep4PositiveLiftedCenteredPartialKernelCommonCarrier
        d k sigma center ⊆
      osiiStep4PositiveLiftedCenteredPartialKernelCommonCarrier
        d k rho center := by
  rintro _ ⟨p, hp, rfl⟩
  refine ⟨p, ⟨hp.1, ?_⟩, rfl⟩
  exact osiiStep4CenteredPartialKernelCommonReducedCarrier_mono
    d k hscale center hp.2

theorem osiiStep4PositiveLiftedCenteredPartialKernelCommonCarrier_isCompact
    (d k : Nat) [NeZero d]
    (rho : Real)
    (center : Fin (k * (d + 1)) -> Real) :
    IsCompact
      (osiiStep4PositiveLiftedCenteredPartialKernelCommonCarrier
        d k rho center) := by
  exact OSIIChapterV.isCompact_reducedTestLiftFullCarrier
    (osiiStep4PositiveTimeBasepointCutoff d)
    (osiiStep4PositiveTimeBasepointCutoff_hasCompactSupport d)
    (osiiStep4CenteredPartialKernelCommonReducedCarrier d k rho center)
    (osiiStep4CenteredPartialKernelCommonReducedCarrier_isCompact
      d k rho center)

private theorem reducedTestLift_tsupport_basepoint_mem_commonCarrier
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
    exact hx
  have hheadPre :
      x ∈ tsupport (fun u : NPointDomain d (m + 1) => chi (u 0)) :=
    tsupport_mul_subset_left hprod
  exact tsupport_comp_subset_preimage
    (chi : SpacetimeDim d → Complex)
    (f := fun u : NPointDomain d (m + 1) => u 0)
    (continuous_apply 0) hheadPre

/-- A reduced test supported in the observed flat ball lifts into the same
absolute compact carrier used by the centered partial kernels.  The premise
is stated on `Function.support`, exactly as in the support-local distribution
interface; closedness of the ball upgrades it to a topological-support
statement internally. -/
theorem osiiStep4PositiveReducedTestLift_tsupport_subset_commonCarrier
    (d k : Nat) [NeZero d]
    (rho : Real)
    (center : Fin (k * (d + 1)) -> Real)
    (phi : SchwartzNPoint d k)
    (hsupport :
      Function.support (flattenSchwartzNPoint (d := d) phi) ⊆
        Metric.closedBall center (rho / 4)) :
    tsupport
        ((BHW.reducedTestLift k d
          (osiiStep4PositiveTimeBasepointCutoff d).toSchwartz phi :
            SchwartzNPoint d (k + 1)) :
          NPointDomain d (k + 1) → Complex) ⊆
      osiiStep4PositiveLiftedCenteredPartialKernelCommonCarrier
        d k rho center := by
  have hphiSupport :
      Function.support (phi : NPointDomain d k → Complex) ⊆
        osiiStep4CenteredPartialKernelCommonReducedCarrier
          d k rho center := by
    intro xi hxi
    refine ⟨flattenCLEquivReal k (d + 1) xi, ?_, ?_⟩
    · apply hsupport
      rw [Function.mem_support, flattenSchwartzNPoint_apply]
      change phi (fun i mu =>
        flattenCLEquivReal k (d + 1) xi (finProdFinEquiv (i, mu))) ≠ 0
      simpa using hxi
    · exact (flattenCLEquivReal k (d + 1)).symm_apply_apply xi
  have hphi :
      tsupport (phi : NPointDomain d k → Complex) ⊆
        osiiStep4CenteredPartialKernelCommonReducedCarrier
          d k rho center := by
    exact closure_minimal hphiSupport
      (osiiStep4CenteredPartialKernelCommonReducedCarrier_isCompact
        d k rho center).isClosed
  intro x hx
  have hbase :
      x 0 ∈ tsupport
        ((osiiStep4PositiveTimeBasepointCutoff d).toSchwartz :
          SpacetimeDim d → Complex) := by
    exact reducedTestLift_tsupport_basepoint_mem_commonCarrier
      d k (osiiStep4PositiveTimeBasepointCutoff d).toSchwartz phi x hx
  have hred :
      BHW.reducedDiffMapReal (k + 1) d x ∈
        tsupport (phi : NPointDomain d k → Complex) := by
    exact reducedTestLift_tsupport_subset_reducedDiff_preimage_tsupport
      (osiiStep4PositiveTimeBasepointCutoff d).toSchwartz phi hx
  refine ⟨(x 0, BHW.reducedDiffMapReal (k + 1) d x),
    ⟨hbase, hphi hred⟩, ?_⟩
  exact OSIIChapterV.realDiffCoordCLE_symm_prependBasepointReal_self x

/-- Every member of the two-parameter centered source family is supported in
the same compact absolute-coordinate carrier. -/
theorem
    osiiStep4PositiveLiftedCenteredPartialConvolutionKernel_tsupport_subset_commonCarrier
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center y y' : Fin (k * (d + 1)) -> Real) :
    tsupport
        ((osiiStep4PositiveLiftedCenteredPartialConvolutionKernelFullSource
          d k hrho center y y' : SchwartzNPoint d (k + 1)) :
            NPointDomain d (k + 1) → Complex) ⊆
      osiiStep4PositiveLiftedCenteredPartialKernelCommonCarrier
        d k rho center := by
  intro x hx
  let phi : SchwartzNPoint d k :=
    osiiStep4CenteredPartialConvolutionKernelFullSource
      d k hrho center y y'
  have hbase :
      x 0 ∈ tsupport
        ((osiiStep4PositiveTimeBasepointCutoff d).toSchwartz :
          SpacetimeDim d → Complex) := by
    exact reducedTestLift_tsupport_basepoint_mem_commonCarrier
      d k (osiiStep4PositiveTimeBasepointCutoff d).toSchwartz phi x hx
  have hred :
      BHW.reducedDiffMapReal (k + 1) d x ∈
        tsupport (phi : NPointDomain d k → Complex) := by
    exact reducedTestLift_tsupport_subset_reducedDiff_preimage_tsupport
      (osiiStep4PositiveTimeBasepointCutoff d).toSchwartz phi hx
  have hredCarrier :
      BHW.reducedDiffMapReal (k + 1) d x ∈
        osiiStep4CenteredPartialKernelCommonReducedCarrier
          d k rho center := by
    exact
      osiiStep4CenteredPartialConvolutionKernelFullSource_tsupport_subset_commonReducedCarrier
        d k hrho center y y' hred
  refine ⟨(x 0, BHW.reducedDiffMapReal (k + 1) d x),
    ⟨hbase, hredCarrier⟩, ?_⟩
  exact OSIIChapterV.realDiffCoordCLE_symm_prependBasepointReal_self x

theorem osiiStep4CommonReducedCarrier_time_pos
    (d k : Nat)
    {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (xi : NPointDomain d k)
    (hxi : xi ∈ osiiStep4CenteredPartialKernelCommonReducedCarrier
      d k rho center)
    (i : Fin k) :
    0 < xi i 0 := by
  rcases hxi with ⟨u, hu, rfl⟩
  have hnorm : ‖u - center‖ <= rho / 4 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hu
  let idx : Fin (k * (d + 1)) :=
    finProdFinEquiv (i, (0 : Fin (d + 1)))
  have hcoord : |u idx - center idx| <= rho / 4 := by
    calc
      |u idx - center idx| = ‖(u - center) idx‖ := by
        simp [Real.norm_eq_abs]
      _ <= ‖u - center‖ := norm_le_pi_norm _ idx
      _ <= rho / 4 := hnorm
  have hlower := (abs_le.mp hcoord).1
  have hc := hcenter i
  have hpositive : 0 < u idx := by
    dsimp only [idx] at hlower hc
    nlinarith
  simpa [idx] using hpositive

/-- The common compact carrier retains strict chronological order. -/
theorem osiiStep4PositiveLiftedCenteredPartialKernelCommonCarrier_ordered
    (d k : Nat) [NeZero d]
    {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    ∀ x ∈
        osiiStep4PositiveLiftedCenteredPartialKernelCommonCarrier
          d k rho center,
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

end OSReconstruction
