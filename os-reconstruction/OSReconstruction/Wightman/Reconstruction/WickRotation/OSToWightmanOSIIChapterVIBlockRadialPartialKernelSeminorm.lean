import OSReconstruction.Mathlib429Compat
import OSReconstruction.SCV.HeadBlockIntegral
import OSReconstruction.SCV.SchwartzFiniteSeminormBound
import OSReconstruction.Wightman.Reconstruction.SchwartzPartialEval
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPartialKernelFullSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialSupremumBound

/-!
# Uniform seminorm bounds for the OS-II block partial kernel

The fixed-imaginary partial kernels used in Chapter VI are not an unrelated
family of Schwartz tests.  Jointly in the real variable and the two imaginary
parameters they are obtained by integrating one compactly supported smooth
function over the auxiliary real convolution variable.  This module packages
that observation as a single joint Schwartz function.

Partial evaluation is continuous in the Schwartz topology.  Consequently, on
the compact reference imaginary box, every finite family of Schwartz
seminorms of the partial kernel has one uniform bound.  Subsequent results in
this module add the explicit dilation and real-center translation powers.
-/

noncomputable section

open Complex MeasureTheory Metric Set
open scoped Classical

namespace OSReconstruction

private theorem osiiStep4_sixteen_pos : (0 : Real) < 16 := by
  norm_num

private abbrev OSIIStep4PartialKernelFlatBase (q k : Nat) :=
  Fin ((k * q) + ((k * q) + (k * q))) → Real

private def osiiStep4PartialKernelFlatX (q k : Nat)
    (u : OSIIStep4PartialKernelFlatBase q k) : Fin (k * q) → Real :=
  splitFirst (k * q) ((k * q) + (k * q)) u

private def osiiStep4PartialKernelFlatY (q k : Nat)
    (u : OSIIStep4PartialKernelFlatBase q k) : Fin (k * q) → Real :=
  splitFirst (k * q) (k * q)
    (splitLast (k * q) ((k * q) + (k * q)) u)

private def osiiStep4PartialKernelFlatY' (q k : Nat)
    (u : OSIIStep4PartialKernelFlatBase q k) : Fin (k * q) → Real :=
  splitLast (k * q) (k * q)
    (splitLast (k * q) ((k * q) + (k * q)) u)

@[simp]
private theorem osiiStep4PartialKernelFlatX_append
    (q k : Nat) (x y y' : Fin (k * q) → Real) :
    osiiStep4PartialKernelFlatX q k (Fin.append x (Fin.append y y')) = x := by
  simp [osiiStep4PartialKernelFlatX]

@[simp]
private theorem osiiStep4PartialKernelFlatY_append
    (q k : Nat) (x y y' : Fin (k * q) → Real) :
    osiiStep4PartialKernelFlatY q k (Fin.append x (Fin.append y y')) = y := by
  simp [osiiStep4PartialKernelFlatY]

@[simp]
private theorem osiiStep4PartialKernelFlatY'_append
    (q k : Nat) (x y y' : Fin (k * q) → Real) :
    osiiStep4PartialKernelFlatY' q k (Fin.append x (Fin.append y y')) = y' := by
  simp [osiiStep4PartialKernelFlatY']

private theorem osiiStep4_finAppendCLE_eq_append
    {m n : Nat} (p : (Fin m → Real) × (Fin n → Real)) :
    SCV.finAppendCLE m n p = Fin.append p.1 p.2 := by
  ext i
  refine Fin.addCases (motive := fun i =>
    SCV.finAppendCLE m n p i = Fin.append p.1 p.2 i) ?_ ?_ i
  · intro j
    simp [Fin.append]
  · intro j
    simp [Fin.append]

/-- The full block density has sup norm at most its block support radius on
its function support. -/
theorem osiiStep4FullBlockRadialG_norm_le_of_mem_support
    (q k : Nat) {rho : Real} (hrho : 0 < rho)
    {z : Fin (k * q) → Complex}
    (hz : z ∈ Function.support (osiiStep4FullBlockRadialG q k rho)) :
    ‖z‖ ≤ rho / 8 := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro a
  obtain ⟨⟨i, mu⟩, rfl⟩ := finProdFinEquiv.surjective a
  have hblock :=
    osiiStep4FullBlockRadialG_support_subset q k hrho hz i
  have hcoord := PiLp.norm_apply_le
    (osiiStep4ComplexBlockToEuclideanCLE q
      ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z i)) mu
  exact hcoord.trans hblock.le

theorem osiiStep4ComplexOfRealImag_real_norm_le
    {m : Nat} (x y : Fin m → Real) :
    ‖x‖ ≤ ‖osiiStep4ComplexOfRealImag x y‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  calc
    ‖x i‖ = |(osiiStep4ComplexOfRealImag x y i).re| := by
      simp [osiiStep4ComplexOfRealImag]
    _ ≤ ‖osiiStep4ComplexOfRealImag x y i‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ‖osiiStep4ComplexOfRealImag x y‖ := norm_le_pi_norm _ _

theorem osiiStep4ComplexOfRealImag_imag_norm_le
    {m : Nat} (x y : Fin m → Real) :
    ‖y‖ ≤ ‖osiiStep4ComplexOfRealImag x y‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  calc
    ‖y i‖ = |(osiiStep4ComplexOfRealImag x y i).im| := by
      simp [osiiStep4ComplexOfRealImag]
    _ ≤ ‖osiiStep4ComplexOfRealImag x y i‖ :=
      Complex.abs_im_le_norm _
    _ ≤ ‖osiiStep4ComplexOfRealImag x y‖ := norm_le_pi_norm _ _

/-- The joint real integrand whose fiber integral is the block partial
convolution kernel.  The flat base stores `(x,y,y')`, in that order. -/
private def osiiStep4PartialConvolutionKernelJointIntegrand
    (q k : Nat) (rho : Real)
    (p : OSIIStep4PartialKernelFlatBase q k × (Fin (k * q) → Real)) :
    Complex :=
  (osiiStep4FullBlockRadialG q k rho
      (osiiStep4ComplexOfRealImag
        (osiiStep4PartialKernelFlatX q k p.1 - p.2)
        (osiiStep4PartialKernelFlatY q k p.1 -
          osiiStep4PartialKernelFlatY' q k p.1)) : Complex) *
    (osiiStep4FullBlockRadialG q k rho
      (osiiStep4ComplexOfRealImag p.2
        (osiiStep4PartialKernelFlatY' q k p.1)) : Complex)

private theorem osiiStep4PartialConvolutionKernelJointIntegrand_contDiff
    (q k : Nat) {rho : Real} (hrho : 0 < rho) :
    ContDiff Real (⊤ : ℕ∞)
      (osiiStep4PartialConvolutionKernelJointIntegrand q k rho) := by
  have hleftArg : ContDiff Real (⊤ : ℕ∞)
      (fun p : OSIIStep4PartialKernelFlatBase q k × (Fin (k * q) → Real) =>
        osiiStep4ComplexOfRealImag
          (osiiStep4PartialKernelFlatX q k p.1 - p.2)
          (osiiStep4PartialKernelFlatY q k p.1 -
            osiiStep4PartialKernelFlatY' q k p.1)) := by
    rw [contDiff_pi]
    intro a
    have hre : ContDiff Real (⊤ : ℕ∞)
        (fun p : OSIIStep4PartialKernelFlatBase q k × (Fin (k * q) → Real) =>
          (osiiStep4PartialKernelFlatX q k p.1 - p.2) a) := by
      dsimp [osiiStep4PartialKernelFlatX, splitFirst]
      fun_prop
    have him : ContDiff Real (⊤ : ℕ∞)
        (fun p : OSIIStep4PartialKernelFlatBase q k × (Fin (k * q) → Real) =>
          (osiiStep4PartialKernelFlatY q k p.1 -
            osiiStep4PartialKernelFlatY' q k p.1) a) := by
      dsimp [osiiStep4PartialKernelFlatY,
        osiiStep4PartialKernelFlatY', splitFirst, splitLast]
      fun_prop
    simpa only [osiiStep4ComplexOfRealImag, Function.comp_apply,
      Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.contDiff.comp hre).add
        ((Complex.ofRealCLM.contDiff.comp him).mul contDiff_const)
  have hrightArg : ContDiff Real (⊤ : ℕ∞)
      (fun p : OSIIStep4PartialKernelFlatBase q k × (Fin (k * q) → Real) =>
        osiiStep4ComplexOfRealImag p.2
          (osiiStep4PartialKernelFlatY' q k p.1)) := by
    rw [contDiff_pi]
    intro a
    have hre : ContDiff Real (⊤ : ℕ∞)
        (fun p : OSIIStep4PartialKernelFlatBase q k × (Fin (k * q) → Real) =>
          p.2 a) := by fun_prop
    have him : ContDiff Real (⊤ : ℕ∞)
        (fun p : OSIIStep4PartialKernelFlatBase q k × (Fin (k * q) → Real) =>
          osiiStep4PartialKernelFlatY' q k p.1 a) := by
      dsimp [osiiStep4PartialKernelFlatY', splitLast]
      fun_prop
    simpa only [osiiStep4ComplexOfRealImag, Function.comp_apply,
      Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.contDiff.comp hre).add
        ((Complex.ofRealCLM.contDiff.comp him).mul contDiff_const)
  have hleft :=
    (osiiStep4FullBlockRadialG_contDiff q k hrho).comp hleftArg
  have hright :=
    (osiiStep4FullBlockRadialG_contDiff q k hrho).comp hrightArg
  exact (Complex.ofRealCLM.contDiff.comp hleft).mul
    (Complex.ofRealCLM.contDiff.comp hright)

private theorem
    osiiStep4PartialConvolutionKernelJointIntegrand_support_subset_closedBall
    (q k : Nat) {rho : Real} (hrho : 0 < rho) :
    Function.support
        (osiiStep4PartialConvolutionKernelJointIntegrand q k rho) ⊆
      Metric.closedBall 0 rho := by
  intro p hp
  let x := osiiStep4PartialKernelFlatX q k p.1
  let y := osiiStep4PartialKernelFlatY q k p.1
  let y' := osiiStep4PartialKernelFlatY' q k p.1
  let z1 := osiiStep4ComplexOfRealImag (x - p.2) (y - y')
  let z2 := osiiStep4ComplexOfRealImag p.2 y'
  have hpne :
      (osiiStep4FullBlockRadialG q k rho z1 : Complex) *
          (osiiStep4FullBlockRadialG q k rho z2 : Complex) ≠ 0 := by
    simpa [osiiStep4PartialConvolutionKernelJointIntegrand, x, y, y', z1, z2,
      Function.mem_support] using hp
  have hz1ne : osiiStep4FullBlockRadialG q k rho z1 ≠ 0 := by
    intro hzero
    apply hpne
    simp [hzero]
  have hz2ne : osiiStep4FullBlockRadialG q k rho z2 ≠ 0 := by
    intro hzero
    apply hpne
    simp [hzero]
  have hz1 : z1 ∈ Function.support (osiiStep4FullBlockRadialG q k rho) :=
    Function.mem_support.mpr hz1ne
  have hz2 : z2 ∈ Function.support (osiiStep4FullBlockRadialG q k rho) :=
    Function.mem_support.mpr hz2ne
  have hz1norm : ‖z1‖ ≤ rho / 8 :=
    osiiStep4FullBlockRadialG_norm_le_of_mem_support q k hrho hz1
  have hz2norm : ‖z2‖ ≤ rho / 8 :=
    osiiStep4FullBlockRadialG_norm_le_of_mem_support q k hrho hz2
  have ht : ‖p.2‖ ≤ rho / 8 :=
    (osiiStep4ComplexOfRealImag_real_norm_le p.2 y').trans hz2norm
  have hy' : ‖y'‖ ≤ rho / 8 :=
    (osiiStep4ComplexOfRealImag_imag_norm_le p.2 y').trans hz2norm
  have hxt : ‖x - p.2‖ ≤ rho / 8 :=
    (osiiStep4ComplexOfRealImag_real_norm_le (x - p.2) (y - y')).trans hz1norm
  have hyy' : ‖y - y'‖ ≤ rho / 8 :=
    (osiiStep4ComplexOfRealImag_imag_norm_le (x - p.2) (y - y')).trans hz1norm
  have hx : ‖x‖ ≤ rho / 4 := by
    calc
      ‖x‖ = ‖(x - p.2) + p.2‖ := by ring_nf
      _ ≤ ‖x - p.2‖ + ‖p.2‖ := norm_add_le _ _
      _ ≤ rho / 8 + rho / 8 := add_le_add hxt ht
      _ = rho / 4 := by ring
  have hy : ‖y‖ ≤ rho / 4 := by
    calc
      ‖y‖ = ‖(y - y') + y'‖ := by ring_nf
      _ ≤ ‖y - y'‖ + ‖y'‖ := norm_add_le _ _
      _ ≤ rho / 8 + rho / 8 := add_le_add hyy' hy'
      _ = rho / 4 := by ring
  have htail :
      ‖splitLast (k * q) ((k * q) + (k * q)) p.1‖ ≤ 3 * rho / 8 := by
    calc
      ‖splitLast (k * q) ((k * q) + (k * q)) p.1‖ ≤
          ‖y‖ + ‖y'‖ :=
        norm_le_splitFirst_add_splitLast (k * q) (k * q)
          (splitLast (k * q) ((k * q) + (k * q)) p.1)
      _ ≤ rho / 4 + rho / 8 := add_le_add hy hy'
      _ = 3 * rho / 8 := by ring
  have hu : ‖p.1‖ ≤ 5 * rho / 8 := by
    calc
      ‖p.1‖ ≤ ‖x‖ +
          ‖splitLast (k * q) ((k * q) + (k * q)) p.1‖ :=
        norm_le_splitFirst_add_splitLast
          (k * q) ((k * q) + (k * q)) p.1
      _ ≤ rho / 4 + 3 * rho / 8 := add_le_add hx htail
      _ = 5 * rho / 8 := by ring
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
  apply max_le
  · exact hu.trans (by nlinarith)
  · exact ht.trans (by nlinarith)

private theorem
    osiiStep4PartialConvolutionKernelJointIntegrand_hasCompactSupport
    (q k : Nat) {rho : Real} (hrho : 0 < rho) :
    HasCompactSupport
      (osiiStep4PartialConvolutionKernelJointIntegrand q k rho) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall
      (0 : OSIIStep4PartialKernelFlatBase q k × (Fin (k * q) → Real)) rho)
  exact
    osiiStep4PartialConvolutionKernelJointIntegrand_support_subset_closedBall
      q k hrho

/-- The compactly supported joint integrand as a Schwartz test. -/
private noncomputable def osiiStep4PartialConvolutionKernelJointIntegrandSchwartz
    (q k : Nat) {rho : Real} (hrho : 0 < rho) :
    SchwartzMap
      (OSIIStep4PartialKernelFlatBase q k × (Fin (k * q) → Real)) Complex :=
  (osiiStep4PartialConvolutionKernelJointIntegrand_hasCompactSupport
      q k hrho).toSchwartzMap
    (osiiStep4PartialConvolutionKernelJointIntegrand_contDiff q k hrho)

@[simp]
private theorem osiiStep4PartialConvolutionKernelJointIntegrandSchwartz_apply
    (q k : Nat) {rho : Real} (hrho : 0 < rho)
    (p : OSIIStep4PartialKernelFlatBase q k × (Fin (k * q) → Real)) :
    osiiStep4PartialConvolutionKernelJointIntegrandSchwartz q k hrho p =
      osiiStep4PartialConvolutionKernelJointIntegrand q k rho p := by
  rfl

/-- The partial kernel jointly in the flattened real and two imaginary
variables. -/
noncomputable def osiiStep4PartialConvolutionKernelJointFlatSchwartz
    (q k : Nat) {rho : Real} (hrho : 0 < rho) :
    SchwartzMap (OSIIStep4PartialKernelFlatBase q k) Complex :=
  SCV.realFiberIntegral
    (osiiStep4PartialConvolutionKernelJointIntegrandSchwartz q k hrho)

@[simp]
theorem osiiStep4PartialConvolutionKernelJointFlatSchwartz_apply_append
    (q k : Nat) {rho : Real} (hrho : 0 < rho)
    (x y y' : Fin (k * q) → Real) :
    osiiStep4PartialConvolutionKernelJointFlatSchwartz q k hrho
        (Fin.append x (Fin.append y y')) =
      osiiStep4PartialConvolutionKernel
        (osiiStep4FullBlockRadialG q k rho)
        (osiiStep4ComplexOfRealImag x y) y' := by
  rw [osiiStep4PartialConvolutionKernelJointFlatSchwartz,
    SCV.realFiberIntegral_apply, osiiStep4PartialConvolutionKernel]
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with t
  simp only [osiiStep4PartialConvolutionKernelJointIntegrandSchwartz_apply,
    osiiStep4PartialConvolutionKernelJointIntegrand,
    osiiStep4PartialKernelFlatX_append,
    osiiStep4PartialKernelFlatY_append,
    osiiStep4PartialKernelFlatY'_append]
  have harg :
      osiiStep4ComplexOfRealImag (x - t) (y - y') =
        osiiStep4ComplexOfRealImag x y -
          osiiStep4ComplexOfRealImag t y' := by
    ext i
    simp [osiiStep4ComplexOfRealImag]
    ring
  rw [harg]
  push_cast
  rfl

/-- Product-coordinate form of the joint partial kernel, with the real
variable first and `(y,y')` in the second factor. -/
noncomputable def osiiStep4PartialConvolutionKernelJointSchwartz
    (q k : Nat) {rho : Real} (hrho : 0 < rho) :
    SchwartzMap
      ((Fin (k * q) → Real) × (Fin ((k * q) + (k * q)) → Real)) Complex :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv Complex
    (SCV.finAppendCLE (k * q) ((k * q) + (k * q))))
      (osiiStep4PartialConvolutionKernelJointFlatSchwartz q k hrho)

@[simp]
theorem osiiStep4PartialConvolutionKernelJointSchwartz_apply
    (q k : Nat) {rho : Real} (hrho : 0 < rho)
    (x y y' : Fin (k * q) → Real) :
    osiiStep4PartialConvolutionKernelJointSchwartz q k hrho
        (x, Fin.append y y') =
      osiiStep4PartialConvolutionKernel
        (osiiStep4FullBlockRadialG q k rho)
        (osiiStep4ComplexOfRealImag x y) y' := by
  rw [osiiStep4PartialConvolutionKernelJointSchwartz]
  change osiiStep4PartialConvolutionKernelJointFlatSchwartz q k hrho
      (SCV.finAppendCLE (k * q) ((k * q) + (k * q))
        (x, Fin.append y y')) = _
  rw [osiiStep4_finAppendCLE_eq_append]
  exact osiiStep4PartialConvolutionKernelJointFlatSchwartz_apply_append
    q k hrho x y y'

/-- Every fixed-imaginary complex partial kernel is the corresponding partial
evaluation of the joint Schwartz kernel. -/
theorem osiiStep4PartialConvolutionKernelComplexSchwartz_eq_partialEval
    (q k : Nat) {rho : Real} (hrho : 0 < rho)
    (y y' : Fin (k * q) → Real) :
    osiiStep4PartialConvolutionKernelComplexSchwartz q k hrho y y' =
      SchwartzMap.partialEval₂
        (osiiStep4PartialConvolutionKernelJointSchwartz q k hrho)
        (Fin.append y y') := by
  ext x
  rw [osiiStep4PartialConvolutionKernelComplexSchwartz_apply]
  exact (osiiStep4PartialConvolutionKernelJointSchwartz_apply
    q k hrho x y y').symm

/-- The fixed-imaginary block partial kernel varies continuously in both
imaginary parameters for the Schwartz topology. -/
theorem continuous_osiiStep4PartialConvolutionKernelComplexSchwartz
    (q k : Nat) {rho : Real} (hrho : 0 < rho) :
    Continuous (fun p : (Fin (k * q) → Real) × (Fin (k * q) → Real) =>
      osiiStep4PartialConvolutionKernelComplexSchwartz
        q k hrho p.1 p.2) := by
  let K := osiiStep4PartialConvolutionKernelJointSchwartz q k hrho
  have hpartial : Continuous (fun v : Fin ((k * q) + (k * q)) → Real =>
      SchwartzMap.partialEval₂ K v) :=
    continuous_partialEval₂ K
  have happend : Continuous
      (fun p : (Fin (k * q) → Real) × (Fin (k * q) → Real) =>
        Fin.append p.1 p.2) := by
    have h := (SCV.finAppendCLE (k * q) (k * q)).continuous
    convert h using 1
    funext p
    exact osiiStep4_finAppendCLE_eq_append p
  rw [show (fun p : (Fin (k * q) → Real) × (Fin (k * q) → Real) =>
      osiiStep4PartialConvolutionKernelComplexSchwartz
        q k hrho p.1 p.2) =
      fun p => SchwartzMap.partialEval₂ K (Fin.append p.1 p.2) by
    funext p
    exact osiiStep4PartialConvolutionKernelComplexSchwartz_eq_partialEval
      q k hrho p.1 p.2]
  exact hpartial.comp happend

/-- At a fixed real center, the complete centered partial-kernel source is
continuous in both imaginary regularizer variables for the Schwartz
topology. -/
theorem continuous_osiiStep4CenteredPartialConvolutionKernelFullSource
    (d k : Nat) {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) → Real) :
    Continuous
      (fun p :
          (Fin (k * (d + 1)) → Real) ×
            (Fin (k * (d + 1)) → Real) =>
        osiiStep4CenteredPartialConvolutionKernelFullSource
          d k hrho center p.1 p.2) := by
  let translate := SCV.translateSchwartzCLM
    (-center : Fin (k * (d + 1)) → Real)
  have hkernel : Continuous
      (fun p :
          (Fin (k * (d + 1)) → Real) ×
            (Fin (k * (d + 1)) → Real) =>
        osiiStep4PartialConvolutionKernelComplexSchwartz
          (d + 1) k hrho p.1 p.2) :=
    continuous_osiiStep4PartialConvolutionKernelComplexSchwartz
      (d + 1) k hrho
  have htranslated : Continuous
      (fun p :
          (Fin (k * (d + 1)) → Real) ×
            (Fin (k * (d + 1)) → Real) =>
        translate
          (osiiStep4PartialConvolutionKernelComplexSchwartz
            (d + 1) k hrho p.1 p.2)) :=
    translate.continuous.comp hkernel
  have hfull :=
    (unflattenSchwartzNPoint (d := d)).continuous.comp htranslated
  refine hfull.congr ?_
  intro p
  rfl

set_option maxHeartbeats 800000 in
/-- At the reference radius, every finite collection of real Schwartz
seminorms of the partial kernel is uniformly bounded over the full closed
imaginary support box. -/
theorem exists_osiiStep4PartialConvolutionKernel_reference_finsetSeminorm_bound
    (q k : Nat) (s : Finset (Nat × Nat)) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ p ∈ osiiStep4PartialConvolutionClosedImaginaryBox q k 16,
        s.sup (schwartzSeminormFamily Real (Fin (k * q) → Real) Complex)
            (osiiStep4PartialConvolutionKernelComplexSchwartz
              q k (rho := 16) osiiStep4_sixteen_pos p.1 p.2) ≤ C := by
  have hF : Continuous (fun p :
      (Fin (k * q) → Real) × (Fin (k * q) → Real) =>
      s.sup (schwartzSeminormFamily Real (Fin (k * q) → Real) Complex)
        (osiiStep4PartialConvolutionKernelComplexSchwartz
          q k (rho := 16) osiiStep4_sixteen_pos p.1 p.2)) := by
    exact (((schwartz_withSeminorms Real (Fin (k * q) → Real) Complex).finset_sups
      ).continuous_seminorm s).comp
        (continuous_osiiStep4PartialConvolutionKernelComplexSchwartz
          q k (rho := 16) osiiStep4_sixteen_pos)
  have hK : IsCompact
      (osiiStep4PartialConvolutionClosedImaginaryBox q k 16) :=
    osiiStep4PartialConvolutionClosedImaginaryBox_isCompact q k 16
  rcases hK.bddAbove_image hF.continuousOn with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro p hp
  have hFC :
      s.sup (schwartzSeminormFamily Real (Fin (k * q) → Real) Complex)
          (osiiStep4PartialConvolutionKernelComplexSchwartz
            q k (rho := 16) osiiStep4_sixteen_pos p.1 p.2) ≤ C :=
    hC ⟨p, hp, rfl⟩
  exact hFC.trans (le_max_left C 0)

set_option backward.isDefEq.respectTransparency false in
/-- Exact dilation bound for a fixed Schwartz seminorm of the partial kernel.
The factor `3 * q * k` is the normalized partial-kernel density power, and
each derivative contributes one further inverse-radius power. -/
theorem osiiStep4PartialConvolutionKernelComplexSchwartz_seminorm_scale
    (q k : Nat) {rho : Real} (hrho : 0 < rho) (hrho_le : rho ≤ 16)
    (p l : Nat) (y y' : Fin (k * q) → Real) :
    SchwartzMap.seminorm Real p l
        (osiiStep4PartialConvolutionKernelComplexSchwartz
          q k hrho y y') ≤
      (16 / rho) ^ (3 * q * k + l) *
        SchwartzMap.seminorm Real p l
          (osiiStep4PartialConvolutionKernelComplexSchwartz
            q k osiiStep4_sixteen_pos
              ((16 / rho) • y) ((16 / rho) • y') ) := by
  let a : Real := 16 / rho
  let K0 : SchwartzMap (Fin (k * q) → Real) Complex :=
    osiiStep4PartialConvolutionKernelComplexSchwartz
      q k osiiStep4_sixteen_pos (a • y) (a • y')
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have ha_one : 1 ≤ a := by
    dsimp [a]
    rw [le_div_iff₀ hrho]
    simpa using hrho_le
  have hfun :
      (⇑(osiiStep4PartialConvolutionKernelComplexSchwartz
          q k hrho y y') : (Fin (k * q) → Real) → Complex) =
        fun x => (a ^ (3 * q * k) : Real) • K0 (a • x) := by
    funext x
    rw [osiiStep4PartialConvolutionKernelComplexSchwartz_apply,
      osiiStep4PartialConvolutionKernelComplexSchwartz_apply]
    rw [osiiStep4PartialConvolutionKernel_fullBlock_scale q k hrho]
    have hcplx := osiiStep4ComplexOfRealImag_smul a x y
    dsimp only [a] at hcplx ⊢
    rw [← hcplx]
    push_cast
    simp [Complex.real_smul]
  refine SchwartzMap.seminorm_le_bound Real p l
    (osiiStep4PartialConvolutionKernelComplexSchwartz q k hrho y y')
    (mul_nonneg (pow_nonneg ha_pos.le _)
      (apply_nonneg (SchwartzMap.seminorm Real p l) K0)) ?_
  intro x
  have hcomp_smooth :
      ContDiff Real l (fun u : Fin (k * q) → Real => K0 (a • u)) :=
    (K0.smooth l).comp (contDiff_const_smul a)
  have hderiv :
      iteratedFDeriv Real l
          (⇑(osiiStep4PartialConvolutionKernelComplexSchwartz
            q k hrho y y')) x =
        (a ^ (3 * q * k) : Real) •
          (a ^ l : Real) •
            iteratedFDeriv Real l (⇑K0) (a • x) := by
    rw [hfun]
    calc
      iteratedFDeriv Real l
          (fun u : Fin (k * q) → Real =>
            (a ^ (3 * q * k) : Real) • K0 (a • u)) x =
        (a ^ (3 * q * k) : Real) •
          iteratedFDeriv Real l
            (fun u : Fin (k * q) → Real => K0 (a • u)) x := by
              exact iteratedFDeriv_const_smul_apply'
                hcomp_smooth.contDiffAt
      _ = (a ^ (3 * q * k) : Real) •
          (a ^ l : Real) •
            iteratedFDeriv Real l (⇑K0) (a • x) := by
        rw [show
          iteratedFDeriv Real l
              (fun u : Fin (k * q) → Real => K0 (a • u)) x =
            (a ^ l : Real) • iteratedFDeriv Real l (⇑K0) (a • x) by
              simpa using congrFun
                (iteratedFDeriv_comp_const_smul a (K0.smooth l)) x]
  have hxnorm : ‖x‖ ≤ ‖a • x‖ := by
    calc
      ‖x‖ = 1 * ‖x‖ := by simp
      _ ≤ a * ‖x‖ :=
        mul_le_mul_of_nonneg_right ha_one (norm_nonneg x)
      _ = ‖a • x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha_pos]
  letI : Norm
      (ContinuousMultilinearMap Real
        (fun _ : Fin l => Fin (k * q) → Real) Complex) :=
    ContinuousMultilinearMap.hasOpNorm
  letI : NormedAddCommGroup
      (ContinuousMultilinearMap Real
        (fun _ : Fin l => Fin (k * q) → Real) Complex) :=
    ContinuousMultilinearMap.normedAddCommGroup
  letI : NormedSpace Real
      (ContinuousMultilinearMap Real
        (fun _ : Fin l => Fin (k * q) → Real) Complex) :=
    ContinuousMultilinearMap.normedSpace
  letI : NormSMulClass Real
      (ContinuousMultilinearMap Real
        (fun _ : Fin l => Fin (k * q) → Real) Complex) :=
    NormedSpace.toNormSMulClass
  rw [hderiv]
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg ha_pos.le (3 * q * k)),
    abs_of_nonneg (pow_nonneg ha_pos.le l)]
  calc
    ‖x‖ ^ p *
        (a ^ (3 * q * k) *
          (a ^ l * ‖iteratedFDeriv Real l (⇑K0) (a • x)‖)) =
      a ^ (3 * q * k + l) *
        (‖x‖ ^ p * ‖iteratedFDeriv Real l (⇑K0) (a • x)‖) := by
          rw [pow_add]
          ring
    _ ≤ a ^ (3 * q * k + l) *
        (‖a • x‖ ^ p *
          ‖iteratedFDeriv Real l (⇑K0) (a • x)‖) := by
      gcongr
    _ ≤ a ^ (3 * q * k + l) *
        SchwartzMap.seminorm Real p l K0 := by
      exact mul_le_mul_of_nonneg_left
        (SchwartzMap.le_seminorm Real p l K0 (a • x))
        (pow_nonneg ha_pos.le _)
    _ = (16 / rho) ^ (3 * q * k + l) *
        SchwartzMap.seminorm Real p l
          (osiiStep4PartialConvolutionKernelComplexSchwartz
            q k osiiStep4_sixteen_pos
              ((16 / rho) • y) ((16 / rho) • y')) := by
      rfl

private theorem
    osiiStep4PartialConvolutionClosedImaginaryBox_scale_to_reference_local
    (q k : Nat) {rho : Real} (hrho : 0 < rho)
    {p : (Fin (k * q) → Real) × (Fin (k * q) → Real)}
    (hp : p ∈ osiiStep4PartialConvolutionClosedImaginaryBox q k rho) :
    ((16 / rho) • p.1, (16 / rho) • p.2) ∈
      osiiStep4PartialConvolutionClosedImaginaryBox q k 16 := by
  rcases hp with ⟨hy, hy'⟩
  constructor
  · rw [Metric.mem_closedBall, dist_zero_right] at hy ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc
      (16 / rho) * ‖p.1‖ ≤ (16 / rho) * (rho / 4) := by
        gcongr
      _ = 16 / 4 := by field_simp
  · rw [Metric.mem_closedBall, dist_zero_right] at hy' ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc
      (16 / rho) * ‖p.2‖ ≤ (16 / rho) * (rho / 8) := by
        gcongr
      _ = 16 / 8 := by field_simp

set_option maxHeartbeats 800000 in
/-- Uniform inverse-radius bound for any finite family of partial-kernel
Schwartz seminorms.  The exponent is chosen from the largest derivative order
in the requested family. -/
theorem exists_osiiStep4PartialConvolutionKernel_finsetSeminorm_scale_bound
    (q k : Nat) (s : Finset (Nat × Nat)) :
    ∃ C : Real, ∃ M : Nat, 0 ≤ C ∧
      ∀ {rho : Real} (hrho : 0 < rho), rho ≤ 16 →
        ∀ p ∈ osiiStep4PartialConvolutionClosedImaginaryBox q k rho,
          s.sup (schwartzSeminormFamily Real
              (Fin (k * q) → Real) Complex)
              (osiiStep4PartialConvolutionKernelComplexSchwartz
                q k hrho p.1 p.2) ≤
            C * (16 / rho) ^ M := by
  let derivativeOrder : Nat := s.sup fun j => j.2
  let M : Nat := 3 * q * k + derivativeOrder
  obtain ⟨C, hC, href⟩ :=
    exists_osiiStep4PartialConvolutionKernel_reference_finsetSeminorm_bound
      q k s
  refine ⟨C, M, hC, ?_⟩
  intro rho hrho hrho_le p hp
  let a : Real := 16 / rho
  have ha_one : 1 ≤ a := by
    dsimp [a]
    rw [le_div_iff₀ hrho]
    simpa using hrho_le
  have hpref : (a • p.1, a • p.2) ∈
      osiiStep4PartialConvolutionClosedImaginaryBox q k 16 := by
    simpa [a] using
      osiiStep4PartialConvolutionClosedImaginaryBox_scale_to_reference_local
        q k hrho hp
  have hrefp := href (a • p.1, a • p.2) hpref
  apply Seminorm.finset_sup_apply_le
  · exact mul_nonneg hC (pow_nonneg (by positivity) _)
  intro j hj
  change SchwartzMap.seminorm Real j.1 j.2
      (osiiStep4PartialConvolutionKernelComplexSchwartz
        q k hrho p.1 p.2) ≤ C * a ^ M
  have hscale :=
    osiiStep4PartialConvolutionKernelComplexSchwartz_seminorm_scale
      q k hrho hrho_le j.1 j.2 p.1 p.2
  have hjderiv : j.2 ≤ derivativeOrder :=
    Finset.le_sup (f := fun z => z.2) hj
  have hexp : 3 * q * k + j.2 ≤ M :=
    Nat.add_le_add_left hjderiv (3 * q * k)
  have hpow : a ^ (3 * q * k + j.2) ≤ a ^ M :=
    pow_le_pow_right₀ ha_one hexp
  have hrefj :
      SchwartzMap.seminorm Real j.1 j.2
          (osiiStep4PartialConvolutionKernelComplexSchwartz
            q k osiiStep4_sixteen_pos (a • p.1) (a • p.2)) ≤ C := by
    exact (Finset.le_sup
      (f := schwartzSeminormFamily Real
        (Fin (k * q) → Real) Complex) hj
      (osiiStep4PartialConvolutionKernelComplexSchwartz
        q k osiiStep4_sixteen_pos (a • p.1) (a • p.2))).trans hrefp
  calc
    SchwartzMap.seminorm Real j.1 j.2
        (osiiStep4PartialConvolutionKernelComplexSchwartz
          q k hrho p.1 p.2) ≤
      a ^ (3 * q * k + j.2) *
        SchwartzMap.seminorm Real j.1 j.2
          (osiiStep4PartialConvolutionKernelComplexSchwartz
            q k osiiStep4_sixteen_pos (a • p.1) (a • p.2)) := by
              simpa [a] using hscale
    _ ≤ a ^ M * C :=
      mul_le_mul hpow hrefj
        (apply_nonneg _ _) (pow_nonneg (by positivity) _)
    _ = C * a ^ M := by ring

/-- Centering the partial kernel costs only the expected polynomial power in
the real center.  The uncentered seminorms of weight orders `p` and `0` are
both needed because the polynomial weight vanishes at the origin. -/
theorem osiiStep4CenteredPartialConvolutionKernelComplexSchwartz_seminorm_le
    (q k : Nat) {rho : Real} (hrho : 0 < rho)
    (p l : Nat) (center y y' : Fin (k * q) → Real) :
    SchwartzMap.seminorm Real p l
        (osiiStep4CenteredPartialConvolutionKernelComplexSchwartz
          q k hrho center y y') ≤
      2 ^ (p - 1) *
        (SchwartzMap.seminorm Real p l
            (osiiStep4PartialConvolutionKernelComplexSchwartz
              q k hrho y y') +
          SchwartzMap.seminorm Real 0 l
            (osiiStep4PartialConvolutionKernelComplexSchwartz
              q k hrho y y')) *
        (1 + ‖center‖) ^ p := by
  let G : SchwartzMap (Fin (k * q) → Real) Complex :=
    osiiStep4PartialConvolutionKernelComplexSchwartz q k hrho y y'
  rw [show
      osiiStep4CenteredPartialConvolutionKernelComplexSchwartz
          q k hrho center y y' =
        SCV.translateSchwartz (-center) G by
      rfl]
  refine SchwartzMap.seminorm_le_bound Real p l
    (SCV.translateSchwartz (-center) G) (by positivity) ?_
  intro x
  have hcoe :
      (⇑(SCV.translateSchwartz (-center) G) :
          (Fin (k * q) → Real) → Complex) =
        fun z => G (z + (-center)) := by
    rfl
  rw [hcoe, iteratedFDeriv_comp_add_right]
  have hnorm_x : ‖x‖ ≤ ‖x + (-center)‖ + ‖center‖ := by
    calc
      ‖x‖ = ‖(x + (-center)) - (-center)‖ := by simp
      _ ≤ ‖x + (-center)‖ + ‖-center‖ := norm_sub_le _ _
      _ = ‖x + (-center)‖ + ‖center‖ := by rw [norm_neg]
  have hp :
      ‖x + (-center)‖ ^ p *
          ‖iteratedFDeriv Real l (⇑G) (x + (-center))‖ ≤
        SchwartzMap.seminorm Real p l G :=
    SchwartzMap.le_seminorm Real p l G (x + (-center))
  have h0 :
      ‖iteratedFDeriv Real l (⇑G) (x + (-center))‖ ≤
        SchwartzMap.seminorm Real 0 l G := by
    simpa using SchwartzMap.le_seminorm Real 0 l G (x + (-center))
  have hbase : 1 ≤ 1 + ‖center‖ := by
    linarith [norm_nonneg center]
  have hconstants :
      SchwartzMap.seminorm Real p l G +
          ‖center‖ ^ p * SchwartzMap.seminorm Real 0 l G ≤
        (1 + ‖center‖) ^ p *
          (SchwartzMap.seminorm Real p l G +
            SchwartzMap.seminorm Real 0 l G) := by
    rw [mul_add]
    apply add_le_add
    · exact le_mul_of_one_le_left
        (apply_nonneg (SchwartzMap.seminorm Real p l) G)
        (one_le_pow₀ hbase)
    · exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg center)
          (le_add_of_nonneg_left zero_le_one) p)
        (apply_nonneg (SchwartzMap.seminorm Real 0 l) G)
  calc
    ‖x‖ ^ p *
        ‖iteratedFDeriv Real l (⇑G) (x + (-center))‖ ≤
      (‖x + (-center)‖ + ‖center‖) ^ p *
        ‖iteratedFDeriv Real l (⇑G) (x + (-center))‖ := by
      gcongr
    _ ≤
      (2 ^ (p - 1) *
          (‖x + (-center)‖ ^ p + ‖center‖ ^ p)) *
        ‖iteratedFDeriv Real l (⇑G) (x + (-center))‖ := by
      gcongr
      exact add_pow_le (norm_nonneg _) (norm_nonneg _) p
    _ =
      2 ^ (p - 1) *
        (‖x + (-center)‖ ^ p *
            ‖iteratedFDeriv Real l (⇑G) (x + (-center))‖ +
          ‖center‖ ^ p *
            ‖iteratedFDeriv Real l (⇑G) (x + (-center))‖) := by
      ring
    _ ≤
      2 ^ (p - 1) *
        (SchwartzMap.seminorm Real p l G +
          ‖center‖ ^ p * SchwartzMap.seminorm Real 0 l G) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add hp
          (mul_le_mul_of_nonneg_left h0
            (pow_nonneg (norm_nonneg center) p)))
        (by positivity)
    _ ≤
      2 ^ (p - 1) *
        ((1 + ‖center‖) ^ p *
          (SchwartzMap.seminorm Real p l G +
            SchwartzMap.seminorm Real 0 l G)) := by
      exact mul_le_mul_of_nonneg_left hconstants (by positivity)
    _ =
      2 ^ (p - 1) *
        (SchwartzMap.seminorm Real p l
            (osiiStep4PartialConvolutionKernelComplexSchwartz
              q k hrho y y') +
          SchwartzMap.seminorm Real 0 l
            (osiiStep4PartialConvolutionKernelComplexSchwartz
              q k hrho y y')) *
        (1 + ‖center‖) ^ p := by
      dsimp only [G]
      ring

set_option maxHeartbeats 800000 in
/-- A finite family of centered partial-kernel seminorms has one simultaneous
inverse-radius exponent and one real-center growth degree. -/
theorem
    exists_osiiStep4CenteredPartialConvolutionKernel_finsetSeminorm_scale_bound
    (q k : Nat) (s : Finset (Nat × Nat)) :
    ∃ C : Real, ∃ M N : Nat, 0 ≤ C ∧
      ∀ {rho : Real} (hrho : 0 < rho), rho ≤ 16 →
        ∀ center : Fin (k * q) → Real,
          ∀ p ∈ osiiStep4PartialConvolutionClosedImaginaryBox q k rho,
            s.sup (schwartzSeminormFamily Real
                (Fin (k * q) → Real) Complex)
                (osiiStep4CenteredPartialConvolutionKernelComplexSchwartz
                  q k hrho center p.1 p.2) ≤
              C * (16 / rho) ^ M * (1 + ‖center‖) ^ N := by
  let s' : Finset (Nat × Nat) :=
    s ∪ s.image (fun j => (0, j.2))
  let N : Nat := s.sup fun j => j.1
  obtain ⟨C0, M, hC0, hscale⟩ :=
    exists_osiiStep4PartialConvolutionKernel_finsetSeminorm_scale_bound
      q k s'
  let C : Real := 2 ^ N * (C0 + C0)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, M, N, hC, ?_⟩
  intro rho hrho hrho_le center p hp
  let a : Real := 16 / rho
  let b : Real := 1 + ‖center‖
  have ha_one : 1 ≤ a := by
    dsimp [a]
    rw [le_div_iff₀ hrho]
    simpa using hrho_le
  have hb_one : 1 ≤ b := by
    dsimp [b]
    linarith [norm_nonneg center]
  have hbase := hscale hrho hrho_le p hp
  apply Seminorm.finset_sup_apply_le
  · exact mul_nonneg
      (mul_nonneg hC (pow_nonneg (by positivity) M))
      (pow_nonneg (by positivity) N)
  intro j hj
  change SchwartzMap.seminorm Real j.1 j.2
      (osiiStep4CenteredPartialConvolutionKernelComplexSchwartz
        q k hrho center p.1 p.2) ≤ C * a ^ M * b ^ N
  have hj_mem : j ∈ s' := by
    exact Finset.mem_union_left _ hj
  have hj0_mem : (0, j.2) ∈ s' := by
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
  have hjbase :
      SchwartzMap.seminorm Real j.1 j.2
          (osiiStep4PartialConvolutionKernelComplexSchwartz
            q k hrho p.1 p.2) ≤ C0 * a ^ M := by
    exact (Seminorm.le_finset_sup_apply
      (p := schwartzSeminormFamily Real
        (Fin (k * q) → Real) Complex) hj_mem).trans
      (by simpa [a] using hbase)
  have hj0base :
      SchwartzMap.seminorm Real 0 j.2
          (osiiStep4PartialConvolutionKernelComplexSchwartz
            q k hrho p.1 p.2) ≤ C0 * a ^ M := by
    exact (Seminorm.le_finset_sup_apply
      (p := schwartzSeminormFamily Real
        (Fin (k * q) → Real) Complex) hj0_mem).trans
      (by simpa [a] using hbase)
  have hjN : j.1 ≤ N :=
    Finset.le_sup (f := fun z => z.1) hj
  have hjpredN : j.1 - 1 ≤ N :=
    (Nat.sub_le j.1 1).trans hjN
  have hpow_two : (2 : Real) ^ (j.1 - 1) ≤ 2 ^ N :=
    pow_le_pow_right₀ (by norm_num) hjpredN
  have hpow_center : b ^ j.1 ≤ b ^ N :=
    pow_le_pow_right₀ hb_one hjN
  calc
    SchwartzMap.seminorm Real j.1 j.2
        (osiiStep4CenteredPartialConvolutionKernelComplexSchwartz
          q k hrho center p.1 p.2) ≤
      2 ^ (j.1 - 1) *
        (SchwartzMap.seminorm Real j.1 j.2
            (osiiStep4PartialConvolutionKernelComplexSchwartz
              q k hrho p.1 p.2) +
          SchwartzMap.seminorm Real 0 j.2
            (osiiStep4PartialConvolutionKernelComplexSchwartz
              q k hrho p.1 p.2)) * b ^ j.1 := by
      simpa [b] using
        osiiStep4CenteredPartialConvolutionKernelComplexSchwartz_seminorm_le
          q k hrho j.1 j.2 center p.1 p.2
    _ ≤ 2 ^ N * ((C0 * a ^ M) + (C0 * a ^ M)) * b ^ N := by
      gcongr
    _ = C * a ^ M * b ^ N := by
      dsimp [C]
      ring

set_option maxHeartbeats 800000 in
/-- The same simultaneous scale and center estimate after transporting the
flat kernel to the canonical full `k`-point spacetime Schwartz space. -/
theorem
    exists_osiiStep4CenteredPartialConvolutionKernelFullSource_finsetSeminorm_scale_bound
    (d k : Nat) (t : Finset (Nat × Nat)) :
    ∃ C : Real, ∃ M N : Nat, 0 ≤ C ∧
      ∀ {rho : Real} (hrho : 0 < rho), rho ≤ 16 →
        ∀ center : Fin (k * (d + 1)) → Real,
          ∀ p ∈ osiiStep4PartialConvolutionClosedImaginaryBox
              (d + 1) k rho,
            t.sup (schwartzSeminormFamily Real
                (NPointDomain d k) Complex)
                (osiiStep4CenteredPartialConvolutionKernelFullSource
                  d k hrho center p.1 p.2) ≤
              C * (16 / rho) ^ M * (1 + ‖center‖) ^ N := by
  let U :
      SchwartzMap (Fin (k * (d + 1)) → Real) Complex →L[Complex]
        SchwartzNPoint d k :=
    unflattenSchwartzNPoint (d := d)
  obtain ⟨s, CU, hCU, hU⟩ :=
    exists_schwartzCLM_finsetRealSeminormBound_between U t
  obtain ⟨Cflat, M, N, hCflat, hflat⟩ :=
    exists_osiiStep4CenteredPartialConvolutionKernel_finsetSeminorm_scale_bound
      (d + 1) k s
  let C : Real := CU * Cflat
  have hC : 0 ≤ C := mul_nonneg hCU hCflat
  refine ⟨C, M, N, hC, ?_⟩
  intro rho hrho hrho_le center p hp
  let phi : SchwartzMap (Fin (k * (d + 1)) → Real) Complex :=
    osiiStep4CenteredPartialConvolutionKernelComplexSchwartz
      (d + 1) k hrho center p.1 p.2
  have htransport := hU phi
  have hsource := hflat hrho hrho_le center p hp
  calc
    t.sup (schwartzSeminormFamily Real (NPointDomain d k) Complex)
        (osiiStep4CenteredPartialConvolutionKernelFullSource
          d k hrho center p.1 p.2) ≤
      CU * s.sup
        (schwartzSeminormFamily Real
          (Fin (k * (d + 1)) → Real) Complex) phi := by
      simpa [U, phi,
        osiiStep4CenteredPartialConvolutionKernelFullSource] using htransport
    _ ≤ CU *
        (Cflat * (16 / rho) ^ M * (1 + ‖center‖) ^ N) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [phi] using hsource) hCU
    _ = C * (16 / rho) ^ M * (1 + ‖center‖) ^ N := by
      dsimp [C]
      ring

end OSReconstruction
