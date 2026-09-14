/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPartialKernelSourceFactorization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPartialKernelE0Source
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIPositiveTimeHilbertSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReducedFiberMarginalSchwartz
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReducedTestLiftSupport



















noncomputable section

open Complex Metric Set
open scoped Classical

namespace OSReconstruction

/-- Restrict the normalized complex block bump to real variables at a fixed
imaginary block. -/
def osiiStep4ComplexBlockRadialGRealSlice
    (q : Nat) (rho : Real)
    (imag x : Fin q -> Real) : Real :=
  osiiStep4ComplexBlockRadialG q rho
    (osiiStep4ComplexOfRealImag x imag)

theorem osiiStep4ComplexBlockRadialGRealSlice_contDiff
    (q : Nat) {rho : Real} (hrho : 0 < rho)
    (imag : Fin q -> Real) :
    ContDiff Real (⊤ : ℕ∞)
      (osiiStep4ComplexBlockRadialGRealSlice q rho imag) := by
  apply (osiiStep4ComplexBlockRadialG_contDiff q hrho).comp
  rw [contDiff_pi]
  intro a
  change ContDiff Real (⊤ : ℕ∞)
    (fun x : Fin q -> Real => (x a : Complex) + (imag a : Complex) * I)
  have hx : ContDiff Real (⊤ : ℕ∞)
      (fun x : Fin q -> Real => (x a : Complex)) :=
    Complex.ofRealCLM.contDiff.comp
      (ContinuousLinearMap.proj
        (R := Real) (ι := Fin q) (φ := fun _ => Real) a).contDiff
  exact hx.add contDiff_const

theorem osiiStep4ComplexBlockRadialGRealSlice_support_subset_closedBall
    (q : Nat) {rho : Real} (hrho : 0 < rho)
    (imag : Fin q -> Real) :
    Function.support
        (osiiStep4ComplexBlockRadialGRealSlice q rho imag) <=
      Metric.closedBall (0 : Fin q -> Real) (rho / 8) := by
  intro x hx
  have hz := osiiStep4ComplexBlockRadialG_support_subset q hrho hx
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro a
  let z : Fin q -> Complex := osiiStep4ComplexOfRealImag x imag
  have hzball :
      norm (osiiStep4ComplexBlockToEuclideanCLE q z) < rho / 8 := by
    simpa [osiiStep4ComplexBlockBall, z] using hz
  rw [Real.norm_eq_abs]
  calc
    abs (x a) = abs (z a).re := by simp [z, osiiStep4ComplexOfRealImag]
    _ <= norm (z a) := Complex.abs_re_le_norm _
    _ <= norm (osiiStep4ComplexBlockToEuclideanCLE q z) := by
      simpa using
        PiLp.norm_apply_le (osiiStep4ComplexBlockToEuclideanCLE q z) a
    _ <= rho / 8 := hzball.le

theorem osiiStep4ComplexBlockRadialGRealSlice_hasCompactSupport
    (q : Nat) {rho : Real} (hrho : 0 < rho)
    (imag : Fin q -> Real) :
    HasCompactSupport
      (osiiStep4ComplexBlockRadialGRealSlice q rho imag) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Fin q -> Real) (rho / 8))
  exact osiiStep4ComplexBlockRadialGRealSlice_support_subset_closedBall
    q hrho imag

/-- The fixed-imaginary one-block radial factor as a complex-valued Schwartz
test on the real block. -/
noncomputable def osiiStep4ComplexBlockRadialGRealSchwartz
    (q : Nat) {rho : Real} (hrho : 0 < rho)
    (imag : Fin q -> Real) :
    SchwartzMap (Fin q -> Real) Complex :=
  SchwartzMap.ofRealCLM
    ((osiiStep4ComplexBlockRadialGRealSlice_hasCompactSupport
        q hrho imag).toSchwartzMap
      (osiiStep4ComplexBlockRadialGRealSlice_contDiff q hrho imag))

@[simp] theorem osiiStep4ComplexBlockRadialGRealSchwartz_apply
    (q : Nat) {rho : Real} (hrho : 0 < rho)
    (imag x : Fin q -> Real) :
    osiiStep4ComplexBlockRadialGRealSchwartz q hrho imag x =
      osiiStep4ComplexBlockRadialG q rho
        (osiiStep4ComplexOfRealImag x imag) := by
  simp [osiiStep4ComplexBlockRadialGRealSchwartz,
    osiiStep4ComplexBlockRadialGRealSlice]

/-- Translate the one-block radial factor to a real endpoint center. -/
noncomputable def osiiStep4CenteredComplexBlockRadialGRealSchwartz
    (q : Nat) {rho : Real} (hrho : 0 < rho)
    (center imag : Fin q -> Real) :
    SchwartzMap (Fin q -> Real) Complex :=
  SCV.translateSchwartz (-center)
    (osiiStep4ComplexBlockRadialGRealSchwartz q hrho imag)

@[simp] theorem osiiStep4CenteredComplexBlockRadialGRealSchwartz_apply
    (q : Nat) {rho : Real} (hrho : 0 < rho)
    (center imag x : Fin q -> Real) :
    osiiStep4CenteredComplexBlockRadialGRealSchwartz
        q hrho center imag x =
      osiiStep4ComplexBlockRadialG q rho
        (osiiStep4ComplexOfRealImag (x - center) imag) := by
  simp [osiiStep4CenteredComplexBlockRadialGRealSchwartz,
    sub_eq_add_neg]

theorem
    osiiStep4CenteredComplexBlockRadialGRealSchwartz_tsupport_subset_closedBall
    (q : Nat) {rho : Real} (hrho : 0 < rho)
    (center imag : Fin q -> Real) :
    tsupport
        ((osiiStep4CenteredComplexBlockRadialGRealSchwartz
          q hrho center imag : SchwartzMap (Fin q -> Real) Complex) :
            (Fin q -> Real) -> Complex) <=
      Metric.closedBall center (rho / 8) := by
  apply closure_minimal
  · intro x hx
    have hshift :
        x - center ∈ Function.support
          (osiiStep4ComplexBlockRadialGRealSlice q rho imag) := by
      simpa [Function.mem_support,
        osiiStep4CenteredComplexBlockRadialGRealSchwartz_apply] using hx
    have hball :=
      osiiStep4ComplexBlockRadialGRealSlice_support_subset_closedBall
        q hrho imag hshift
    simpa [Metric.mem_closedBall, dist_eq_norm] using hball
  · exact isClosed_closedBall

/-- If the endpoint center is sufficiently positive in Euclidean time, the
complete support of the centered radial endpoint factor lies at positive
time. -/
theorem osiiStep4CenteredComplexBlockRadialGRealSchwartz_time_pos
    (d : Nat) {rho : Real} (hrho : 0 < rho)
    (center imag : SpacetimeDim d)
    (hcenter : rho / 4 <= center 0)
    (x : SpacetimeDim d)
    (hx : x ∈ tsupport
      ((osiiStep4CenteredComplexBlockRadialGRealSchwartz
        (d + 1) hrho center imag : SchwartzMap (SpacetimeDim d) Complex) :
          SpacetimeDim d -> Complex)) :
    0 < x 0 := by
  have hball :=
    osiiStep4CenteredComplexBlockRadialGRealSchwartz_tsupport_subset_closedBall
      (d + 1) hrho center imag hx
  have hnorm : norm (x - center) <= rho / 8 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hball
  have hcoord : abs (x 0 - center 0) <= rho / 8 := by
    calc
      abs (x 0 - center 0) = norm ((x - center) 0) := by
        simp [Real.norm_eq_abs]
      _ <= norm (x - center) := norm_le_pi_norm _ 0
      _ <= rho / 8 := hnorm
  nlinarith [abs_le.mp hcoord |>.1]

/-- Combine one centered radial endpoint factor with a centered reduced
partial-kernel source.  The output has one endpoint and `k` successive
difference blocks. -/
noncomputable def
    osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource
    (d k : Nat) [NeZero d] {rho : Real} (hrho : 0 < rho)
    (endpointCenter endpointImag : SpacetimeDim d)
    (center y y' : Fin (k * (d + 1)) -> Real) :
    SchwartzNPoint d (k + 1) :=
  BHW.reducedTestLift k d
    (osiiStep4CenteredComplexBlockRadialGRealSchwartz
      (d + 1) hrho endpointCenter endpointImag)
    (osiiStep4CenteredPartialConvolutionKernelFullSource
      d k hrho center y y')

@[simp] theorem
    osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource_apply
    (d k : Nat) [NeZero d] {rho : Real} (hrho : 0 < rho)
    (endpointCenter endpointImag : SpacetimeDim d)
    (center y y' : Fin (k * (d + 1)) -> Real)
    (x : NPointDomain d (k + 1)) :
    osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource
        d k hrho endpointCenter endpointImag center y y' x =
      osiiStep4ComplexBlockRadialG (d + 1) rho
          (osiiStep4ComplexOfRealImag (x 0 - endpointCenter) endpointImag) *
        osiiStep4CenteredPartialConvolutionKernelFullSource
          d k hrho center y y'
            (BHW.reducedDiffMapReal (k + 1) d x) := by
  simp [osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource]

private theorem tsupport_precomp_subset_positiveSource
    {X Y alpha : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Zero alpha]
    {f : Y -> alpha} {h : X -> Y} (hh : Continuous h) :
    tsupport (fun x => f (h x)) <= h ⁻¹' tsupport f := by
  refine closure_minimal ?_ ((isClosed_tsupport _).preimage hh)
  intro x hx
  exact subset_closure (by simpa [Function.mem_support] using hx)

private theorem reducedTestLift_tsupport_basepoint_mem_positiveSource
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
    simpa [BHW.reducedTestLift_apply] using hx
  have hheadPre :
      x ∈ tsupport (fun u : NPointDomain d (m + 1) => chi (u 0)) :=
    tsupport_mul_subset_left hprod
  exact tsupport_precomp_subset_positiveSource
    (f := (chi : SpacetimeDim d -> Complex))
    (h := fun u : NPointDomain d (m + 1) => u 0)
    (by simpa using
      (continuous_apply (0 : Fin (m + 1)) :
        Continuous (fun u : NPointDomain d (m + 1) => u 0))) hheadPre

/-- Positive endpoint and positive reduced-gap centers put the complete lifted
source in the ordered positive-time region. -/
theorem
    osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernel_tsupport_ordered
    (d k : Nat) [NeZero d] {rho : Real} (hrho : 0 < rho)
    (endpointCenter endpointImag : SpacetimeDim d)
    (center y y' : Fin (k * (d + 1)) -> Real)
    (hEndpointCenter : rho / 4 <= endpointCenter 0)
    (hcenter : forall i : Fin k,
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    tsupport
        ((osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource
          d k hrho endpointCenter endpointImag center y y' :
            SchwartzNPoint d (k + 1)) :
              NPointDomain d (k + 1) -> Complex) <=
      OrderedPositiveTimeRegion d (k + 1) := by
  intro x hx
  let chi : SchwartzMap (SpacetimeDim d) Complex :=
    osiiStep4CenteredComplexBlockRadialGRealSchwartz
      (d + 1) hrho endpointCenter endpointImag
  let phi : SchwartzNPoint d k :=
    osiiStep4CenteredPartialConvolutionKernelFullSource
      d k hrho center y y'
  have hred :
      BHW.reducedDiffMapReal (k + 1) d x ∈
        tsupport (phi : NPointDomain d k -> Complex) := by
    exact reducedTestLift_tsupport_subset_reducedDiff_preimage_tsupport
      chi phi hx
  have hgap : forall i : Fin k, 0 < x i.succ 0 - x i.castSucc 0 := by
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
    apply osiiStep4CenteredComplexBlockRadialGRealSchwartz_time_pos
      d hrho endpointCenter endpointImag hEndpointCenter (x 0)
    exact reducedTestLift_tsupport_basepoint_mem_positiveSource
      d k chi phi x hx
  intro i
  constructor
  · exact hbase.trans_le (hmono.monotone (Fin.zero_le i))
  · intro j hij
    exact hmono hij

/-- The preceding source packaged as an input to the continuous OS Hilbert
vector map. -/
noncomputable def
    osiiStep4RadialEndpointPositiveTimeSource
    (d k : Nat) [NeZero d] {rho : Real} (hrho : 0 < rho)
    (endpointCenter endpointImag : SpacetimeDim d)
    (center y y' : Fin (k * (d + 1)) -> Real)
    (hEndpointCenter : rho / 4 <= endpointCenter 0)
    (hcenter : forall i : Fin k,
      rho / 2 <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    euclideanPositiveTimeSubmodule (d := d) (k + 1) :=
  ⟨osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernelFullSource
      d k hrho endpointCenter endpointImag center y y',
    osiiStep4RadialEndpointLiftedCenteredPartialConvolutionKernel_tsupport_ordered
      d k hrho endpointCenter endpointImag center y y'
        hEndpointCenter hcenter⟩

end OSReconstruction
