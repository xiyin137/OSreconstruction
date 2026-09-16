/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialMultiGapGrowth














noncomputable section

open Complex Set
open scoped BigOperators Classical

namespace OSReconstruction

/-- Extract one spacetime block from a flattened real block tuple. -/
def osiiStep4MultiGapRealBlock
    (q k : Nat)
    (x : Fin (k * q) -> Real)
    (i : Fin k) : Fin q -> Real :=
  fun mu => x (finProdFinEquiv (i, mu))

/-- Extract one spacetime block from a flattened complex block tuple. -/
def osiiStep4MultiGapComplexBlock
    (q k : Nat)
    (z : Fin (k * q) -> Complex)
    (i : Fin k) : Fin q -> Complex :=
  fun mu => z (finProdFinEquiv (i, mu))

/-- The flattened blockwise axis-pair anchor.  It halves every time
coordinate and leaves every spatial coordinate unchanged. -/
def osiiStep4MultiGapXiHatCenter
    (d k : Nat)
    (center : Fin (k * (d + 1)) -> Real) :
    Fin (k * (d + 1)) -> Real :=
  flattenCLEquivReal k (d + 1) fun i =>
    osiiAxisPairPhysicalChartAnchor
      (osiiStep4MultiGapRealBlock (d + 1) k center i)

@[simp] theorem osiiStep4MultiGapXiHatCenter_finProdFinEquiv
    (d k : Nat)
    (center : Fin (k * (d + 1)) -> Real)
    (i : Fin k) (mu : Fin (d + 1)) :
    osiiStep4MultiGapXiHatCenter d k center
        (finProdFinEquiv (i, mu)) =
      osiiAxisPairPhysicalChartAnchor
        (osiiStep4MultiGapRealBlock (d + 1) k center i) mu := by
  simp [osiiStep4MultiGapXiHatCenter, flattenCLEquivReal_apply]

/-- The original full-radius lower bound is exactly what the half-time
axis-pair anchor needs for the radial source condition. -/
theorem osiiStep4MultiGapXiHatCenter_time_lower
    (d k : Nat)
    {rho : Real}
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      rho <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    forall i : Fin k,
      rho / 2 <= osiiStep4MultiGapXiHatCenter d k center
        (finProdFinEquiv (i, (0 : Fin (d + 1)))) := by
  intro i
  simp [osiiAxisPairPhysicalChartAnchor,
    osiiStep4MultiGapRealBlock]
  linarith [hcenter i]

/-- Purely imaginary perturbation of one flattened target block. -/
def osiiStep4MultiGapImaginaryBlock
    (d k : Nat)
    (y : Fin (k * (d + 1)) -> Real)
    (i : Fin k) : Fin (d + 1) -> Complex :=
  osiiStep4ComplexOfRealImag 0
    (osiiStep4MultiGapRealBlock (d + 1) k y i)

/-- Axis-pair coefficients that move the blockwise anchor to the requested
complex target. -/
def osiiStep4MultiGapTargetCoeff
    (d k : Nat) [NeZero d]
    (T : Real)
    (center y : Fin (k * (d + 1)) -> Real) :
    Fin k -> osiiAxisPairIndex d -> Complex :=
  fun i =>
    osiiAxisPairCoeffMap T
      (osiiStep4MultiGapRealBlock (d + 1) k center i)
      (osiiStep4MultiGapImaginaryBlock d k y i)

/-- Principal logarithmic coordinates of the target coefficients. -/
def osiiStep4MultiGapTargetLog
    (d k : Nat) [NeZero d]
    (T : Real)
    (center y : Fin (k * (d + 1)) -> Real) :
    Fin k -> osiiAxisPairIndex d -> Complex :=
  fun i a => Complex.log (osiiStep4MultiGapTargetCoeff d k T center y i a)

/-- Axis-pair coefficients for a genuinely complex displacement from the
real target center.  Unlike `osiiStep4MultiGapTargetCoeff`, this map keeps the
real and imaginary parts together, so it is holomorphic in the complete
flattened displacement. -/
def osiiStep4MultiGapComplexTargetCoeff
    (d k : Nat) [NeZero d]
    (T : Real)
    (center : Fin (k * (d + 1)) -> Real)
    (z : Fin (k * (d + 1)) -> Complex) :
    Fin k -> osiiAxisPairIndex d -> Complex :=
  fun i =>
    osiiAxisPairCoeffMap T
      (osiiStep4MultiGapRealBlock (d + 1) k center i)
      (osiiStep4MultiGapComplexBlock (d + 1) k z i)

/-- Principal logarithmic coordinates of a complete complex displacement. -/
def osiiStep4MultiGapComplexTargetLog
    (d k : Nat) [NeZero d]
    (T : Real)
    (center : Fin (k * (d + 1)) -> Real)
    (z : Fin (k * (d + 1)) -> Complex) :
    Fin k -> osiiAxisPairIndex d -> Complex :=
  fun i a =>
    Complex.log (osiiStep4MultiGapComplexTargetCoeff d k T center z i a)

/-- Complete complex displacements on which every axis-pair coefficient
stays in the open right half-plane. -/
def osiiStep4MultiGapComplexTargetRightHalfPlane
    (d k : Nat) [NeZero d]
    (T : Real)
    (center : Fin (k * (d + 1)) -> Real) :
    Set (Fin (k * (d + 1)) -> Complex) :=
  {z | forall i a,
    0 < (osiiStep4MultiGapComplexTargetCoeff d k T center z i a).re}

/-- Every coordinate of the complete complex coefficient map is entire. -/
theorem differentiable_osiiStep4MultiGapComplexTargetCoeff_apply
    (d k : Nat) [NeZero d]
    (T : Real)
    (center : Fin (k * (d + 1)) -> Real)
    (i : Fin k) (a : osiiAxisPairIndex d) :
    Differentiable Complex
      (fun z : Fin (k * (d + 1)) -> Complex =>
        osiiStep4MultiGapComplexTargetCoeff d k T center z i a) := by
  rcases a with ⟨a, b⟩
  cases b <;>
    simp [osiiStep4MultiGapComplexTargetCoeff,
      osiiStep4MultiGapComplexBlock, osiiAxisPairCoeffMap,
      osiiAxisPairCoeff] <;>
    fun_prop

/-- The complete complex logarithmic target map is holomorphic wherever its
coefficients remain in the right half-plane. -/
theorem differentiableOn_osiiStep4MultiGapComplexTargetLog
    (d k : Nat) [NeZero d]
    (T : Real)
    (center : Fin (k * (d + 1)) -> Real) :
    DifferentiableOn Complex
      (osiiStep4MultiGapComplexTargetLog d k T center)
      (osiiStep4MultiGapComplexTargetRightHalfPlane d k T center) := by
  rw [differentiableOn_pi]
  intro i
  rw [differentiableOn_pi]
  intro a z hz
  have hslit :
      osiiStep4MultiGapComplexTargetCoeff d k T center z i a ∈
        Complex.slitPlane := by
    simp only [Complex.slitPlane, Set.mem_setOf_eq]
    left
    exact hz i a
  have hcoeff :=
    differentiable_osiiStep4MultiGapComplexTargetCoeff_apply
      d k T center i a
  simpa [osiiStep4MultiGapComplexTargetLog, Function.comp_def] using
    ((Complex.differentiableAt_log hslit).comp z
      hcoeff.differentiableAt).differentiableWithinAt

/-- On a real displacement with positive coefficients, the complete target
logarithm is the real logarithmic embedding of those coefficients. -/
theorem osiiStep4MultiGapComplexTargetLog_realToComplex_eq_realEmbed
    (d k : Nat) [NeZero d]
    (T : Real)
    (center x : Fin (k * (d + 1)) -> Real)
    (hx : SCV.realToComplex x ∈
      osiiStep4MultiGapComplexTargetRightHalfPlane d k T center) :
    osiiStep4MultiGapComplexTargetLog d k T center
        (SCV.realToComplex x) =
      osiiAxisPairSimultaneousLogRealEmbed
        (fun i a => Real.log
          (osiiStep4MultiGapComplexTargetCoeff d k T center
            (SCV.realToComplex x) i a).re) := by
  funext i
  have hblock :
      osiiStep4MultiGapComplexBlock (d + 1) k
          (SCV.realToComplex x) i =
        fun mu =>
          (osiiStep4MultiGapRealBlock (d + 1) k x i mu : Complex) := by
    funext mu
    simp [osiiStep4MultiGapComplexBlock, osiiStep4MultiGapRealBlock,
      SCV.realToComplex]
  rw [show
    osiiStep4MultiGapComplexTargetLog d k T center
        (SCV.realToComplex x) i =
      osiiAxisPairLogCoeffMap T
        (osiiStep4MultiGapRealBlock (d + 1) k center i)
        (osiiStep4MultiGapComplexBlock (d + 1) k
          (SCV.realToComplex x) i) by rfl]
  rw [hblock]
  simpa [osiiAxisPairSimultaneousLogRealEmbed,
    osiiStep4MultiGapComplexTargetCoeff, hblock] using
    (osiiAxisPairLogCoeffMap_real_eq_embed
      (d := d) T
      (osiiStep4MultiGapRealBlock (d + 1) k center i)
      (osiiStep4MultiGapRealBlock (d + 1) k x i)
      (fun a => hx i a))

/-- One complex interpolation parameter for the target displacement.  Real
parameter values give real axis-pair coefficients; the value `I` gives the
requested imaginary displacement. -/
def osiiStep4MultiGapTargetCoeffLine
    (d k : Nat) [NeZero d]
    (T : Real)
    (center y : Fin (k * (d + 1)) -> Real)
    (z : Complex) :
    Fin k -> osiiAxisPairIndex d -> Complex :=
  fun i =>
    osiiAxisPairCoeffMap T
      (osiiStep4MultiGapRealBlock (d + 1) k center i)
      (fun mu => z *
        (osiiStep4MultiGapRealBlock (d + 1) k y i mu : Complex))

/-- Principal logarithms along the one-parameter target interpolation. -/
def osiiStep4MultiGapTargetLogLine
    (d k : Nat) [NeZero d]
    (T : Real)
    (center y : Fin (k * (d + 1)) -> Real)
    (z : Complex) :
    Fin k -> osiiAxisPairIndex d -> Complex :=
  fun i a =>
    Complex.log
      (osiiStep4MultiGapTargetCoeffLine d k T center y z i a)

/-- Scalar parameters for which every interpolated axis-pair coefficient is
in the open right half-plane. -/
def osiiStep4MultiGapTargetCoeffLineRightHalfPlane
    (d k : Nat) [NeZero d]
    (T : Real)
    (center y : Fin (k * (d + 1)) -> Real) : Set Complex :=
  {z | forall i a,
    0 < (osiiStep4MultiGapTargetCoeffLine d k T center y z i a).re}

theorem osiiStep4MultiGapTargetCoeffLine_I_mul_real
    (d k : Nat) [NeZero d]
    (T : Real)
    (center y : Fin (k * (d + 1)) -> Real)
    (v : Real) :
    osiiStep4MultiGapTargetCoeffLine d k T center y
        (I * (v : Complex)) =
      osiiStep4MultiGapTargetCoeff d k T center (v • y) := by
  funext i a
  simp only [osiiStep4MultiGapTargetCoeffLine,
    osiiStep4MultiGapTargetCoeff,
    osiiStep4MultiGapImaginaryBlock]
  congr 2
  funext mu
  simp [osiiStep4ComplexOfRealImag,
    osiiStep4MultiGapRealBlock]
  ring

theorem osiiStep4MultiGapTargetCoeffLine_ofReal_im
    (d k : Nat) [NeZero d]
    (T : Real)
    (center y : Fin (k * (d + 1)) -> Real)
    (t : Real) (i : Fin k) (a : osiiAxisPairIndex d) :
    (osiiStep4MultiGapTargetCoeffLine d k T center y
      (t : Complex) i a).im = 0 := by
  have hrealDiv (r s : Real) :
      (((r : Complex) / (s : Complex)).im) = 0 := by
    rw [Complex.div_ofReal_im]
    simp
  have hbase := hrealDiv
    (osiiStep4MultiGapRealBlock (d + 1) k center i 0)
    (4 * (d : Real) * T)
  have htime := hrealDiv
    (t * osiiStep4MultiGapRealBlock (d + 1) k y i 0)
    (2 * (d : Real) * T)
  push_cast at hbase htime
  rcases a with ⟨j, b⟩
  cases b <;>
    simp [osiiStep4MultiGapTargetCoeffLine,
      osiiAxisPairCoeffMap, osiiAxisPairCoeff,
      hbase, htime]

theorem osiiStep4MultiGapTargetLogLine_ofReal_eq_realEmbed
    (d k : Nat) [NeZero d]
    (T : Real)
    (center y : Fin (k * (d + 1)) -> Real)
    (t : Real)
    (ht : (t : Complex) ∈
      osiiStep4MultiGapTargetCoeffLineRightHalfPlane
        d k T center y) :
    osiiStep4MultiGapTargetLogLine d k T center y (t : Complex) =
      osiiAxisPairSimultaneousLogRealEmbed
        (fun i a => Real.log
          (osiiStep4MultiGapTargetCoeffLine
            d k T center y (t : Complex) i a).re) := by
  funext i a
  let q := osiiStep4MultiGapTargetCoeffLine
    d k T center y (t : Complex) i a
  have hq_im : q.im = 0 :=
    osiiStep4MultiGapTargetCoeffLine_ofReal_im
      d k T center y t i a
  have hq : q = (q.re : Complex) := by
    apply Complex.ext
    · simp
    · simpa [hq_im]
  rw [show osiiStep4MultiGapTargetLogLine
      d k T center y (t : Complex) i a = Complex.log q by rfl,
    hq]
  exact (Complex.ofReal_log (le_of_lt (ht i a))).symm

/-- Complexification of the axis-pair coefficient translation, flattened
over all chronological gaps. -/
def osiiStep4AxisPairCoeffGapTranslationFlat
    (d : Nat) [NeZero d]
    (T : Real) {k : Nat}
    (w : Fin k -> osiiAxisPairIndex d -> Complex) :
    Fin (k * (d + 1)) -> Complex :=
  fun p =>
    let q := finProdFinEquiv.symm p
    ∑ a : osiiAxisPairIndex d,
      w q.1 a * (osiiAxisPairDir (d := d) T a q.2 : Complex)

@[simp] theorem osiiStep4AxisPairCoeffGapTranslationFlat_finProdFinEquiv
    (d : Nat) [NeZero d]
    (T : Real) {k : Nat}
    (w : Fin k -> osiiAxisPairIndex d -> Complex)
    (i : Fin k) (mu : Fin (d + 1)) :
    osiiStep4AxisPairCoeffGapTranslationFlat d T w
        (finProdFinEquiv (i, mu)) =
      ∑ a : osiiAxisPairIndex d,
        w i a * (osiiAxisPairDir (d := d) T a mu : Complex) := by
  simp [osiiStep4AxisPairCoeffGapTranslationFlat]

@[simp] theorem osiiStep4MultiGapXiHatCenter_realToComplex_finProdFinEquiv
    (d k : Nat)
    (center : Fin (k * (d + 1)) -> Real)
    (i : Fin k) (mu : Fin (d + 1)) :
    SCV.realToComplex (osiiStep4MultiGapXiHatCenter d k center)
        (finProdFinEquiv (i, mu)) =
      osiiAxisPairXiHat
        (osiiStep4MultiGapRealBlock (d + 1) k center i) mu := by
  refine Fin.cases ?_ ?_ mu
  · simp [SCV.realToComplex, osiiAxisPairPhysicalChartAnchor,
      osiiAxisPairXiHat, osiiStep4MultiGapRealBlock]
  · intro j
    simp [SCV.realToComplex, osiiAxisPairPhysicalChartAnchor,
      osiiAxisPairXiHat, osiiStep4MultiGapRealBlock]

/-- The complete complex coefficient map reconstructs `center + z` from the
blockwise axis-pair anchor. -/
theorem osiiStep4MultiGapXiHat_add_complexTargetCoeffTranslation
    (d k : Nat) [NeZero d]
    (T : Real) (hT : T ≠ 0)
    (center : Fin (k * (d + 1)) -> Real)
    (z : Fin (k * (d + 1)) -> Complex) :
    SCV.realToComplex (osiiStep4MultiGapXiHatCenter d k center) +
        osiiStep4AxisPairCoeffGapTranslationFlat d T
          (osiiStep4MultiGapComplexTargetCoeff d k T center z) =
      SCV.realToComplex center + z := by
  funext p
  obtain ⟨⟨i, mu⟩, rfl⟩ := finProdFinEquiv.surjective p
  rw [Pi.add_apply,
    osiiStep4MultiGapXiHatCenter_realToComplex_finProdFinEquiv,
    osiiStep4AxisPairCoeffGapTranslationFlat_finProdFinEquiv]
  simpa [osiiStep4MultiGapComplexTargetCoeff,
    osiiStep4MultiGapComplexBlock, osiiStep4MultiGapRealBlock,
    osiiAxisPairCoeffMap,
    SCV.realToComplex] using
      osiiAxisPairCoeff_linear_identity (d := d) T hT
        (osiiStep4MultiGapRealBlock (d + 1) k center i)
        (osiiStep4MultiGapComplexBlock (d + 1) k z i) mu

/-- On the real edge, the logarithmic target coefficients reconstruct the
real physical displacement `center + x`. -/
theorem osiiStep4MultiGapXiHat_add_complexTargetRealLogTranslation
    (d k : Nat) [NeZero d]
    (T : Real) (hT : T ≠ 0)
    (center x : Fin (k * (d + 1)) -> Real)
    (hx : SCV.realToComplex x ∈
      osiiStep4MultiGapComplexTargetRightHalfPlane d k T center) :
    osiiStep4MultiGapXiHatCenter d k center +
        osiiStep4AxisPairGapTranslationFlat d T
          (fun i a => Real.log
            (osiiStep4MultiGapComplexTargetCoeff d k T center
              (SCV.realToComplex x) i a).re) =
      center + x := by
  ext p
  obtain ⟨⟨i, mu⟩, rfl⟩ := finProdFinEquiv.surjective p
  have hrec := congrArg
    (fun w : Fin (k * (d + 1)) -> Complex =>
      (w (finProdFinEquiv (i, mu))).re)
    (osiiStep4MultiGapXiHat_add_complexTargetCoeffTranslation
      d k T hT center (SCV.realToComplex x))
  rw [Pi.add_apply,
    osiiStep4AxisPairGapTranslationFlat_finProdFinEquiv]
  simp only [osiiAxisPairChronologicalGapTranslation,
    osiiAxisPairPositiveCoefficients, Pi.add_apply, Pi.smul_apply]
  rw [Finset.sum_apply]
  have hexp : forall a : osiiAxisPairIndex d,
      Real.exp (Real.log
        (osiiStep4MultiGapComplexTargetCoeff d k T center
          (SCV.realToComplex x) i a).re) =
        (osiiStep4MultiGapComplexTargetCoeff d k T center
          (SCV.realToComplex x) i a).re := by
    intro a
    exact Real.exp_log (hx i a)
  simp only [hexp]
  simpa [osiiStep4AxisPairCoeffGapTranslationFlat,
    osiiStep4MultiGapXiHatCenter, osiiStep4MultiGapRealBlock,
    SCV.realToComplex] using hrec

theorem osiiStep4MultiGapTargetCoeff_re
    (d k : Nat) [NeZero d]
    (T : Real)
    (center y : Fin (k * (d + 1)) -> Real)
    (i : Fin k) (a : osiiAxisPairIndex d) :
    (osiiStep4MultiGapTargetCoeff d k T center y i a).re =
      center (finProdFinEquiv (i, (0 : Fin (d + 1)))) /
        (4 * (d : Real) * T) := by
  have hbase :
      (((center (finProdFinEquiv (i, (0 : Fin (d + 1)))) : Complex) /
          (((4 * (d : Real) * T : Real) : Complex))).re) =
        center (finProdFinEquiv (i, (0 : Fin (d + 1)))) /
          (4 * (d : Real) * T) := by
    simpa using Complex.div_ofReal_re
      (center (finProdFinEquiv (i, (0 : Fin (d + 1)))) : Complex)
      (4 * (d : Real) * T)
  have hpure (r s : Real) :
      ((((r : Complex) * I) / (s : Complex)).re) = 0 := by
    rw [Complex.div_ofReal_re]
    simp
  have hpureTime := hpure
    (y (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (2 * (d : Real) * T)
  push_cast at hbase hpureTime
  rcases a with ⟨j, b⟩
  cases b <;>
    simp [osiiStep4MultiGapTargetCoeff,
      osiiStep4MultiGapImaginaryBlock,
      osiiStep4MultiGapRealBlock,
      osiiAxisPairCoeffMap, osiiAxisPairCoeff,
      osiiStep4ComplexOfRealImag,
      hbase, hpureTime]

theorem osiiStep4MultiGapTargetCoeffLine_I_mul_real_re
    (d k : Nat) [NeZero d]
    (T : Real)
    (center y : Fin (k * (d + 1)) -> Real)
    (v : Real) (i : Fin k) (a : osiiAxisPairIndex d) :
    (osiiStep4MultiGapTargetCoeffLine d k T center y
      (I * (v : Complex)) i a).re =
        center (finProdFinEquiv (i, (0 : Fin (d + 1)))) /
          (4 * (d : Real) * T) := by
  rw [osiiStep4MultiGapTargetCoeffLine_I_mul_real]
  exact osiiStep4MultiGapTargetCoeff_re
    d k T center (v • y) i a

theorem osiiStep4MultiGapTargetCoeff_re_pos
    (d k : Nat) [NeZero d]
    (T : Real) (hT : 0 < T)
    (center y : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      0 < center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (i : Fin k) (a : osiiAxisPairIndex d) :
    0 < (osiiStep4MultiGapTargetCoeff d k T center y i a).re := by
  rw [osiiStep4MultiGapTargetCoeff_re]
  have hd : 0 < (d : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  exact div_pos (hcenter i) (mul_pos (mul_pos (by norm_num) hd) hT)

theorem osiiStep4MultiGapTargetCoeffLine_I_mul_real_mem_rightHalfPlane
    (d k : Nat) [NeZero d]
    (T : Real) (hT : 0 < T)
    (center y : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      0 < center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (v : Real) :
    I * (v : Complex) ∈
      osiiStep4MultiGapTargetCoeffLineRightHalfPlane
        d k T center y := by
  intro i a
  rw [osiiStep4MultiGapTargetCoeffLine_I_mul_real_re]
  have hd : 0 < (d : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  exact div_pos (hcenter i) (mul_pos (mul_pos (by norm_num) hd) hT)

/-- At zero imaginary displacement, the physical target logarithm lies on
the real multi-gap edge.  Positivity selects the principal real logarithm;
there is no residual branch choice. -/
theorem osiiStep4MultiGapTargetLog_zero_eq_realEmbed
    (d k : Nat) [NeZero d]
    (T : Real) (hT : 0 < T)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      0 < center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    osiiStep4MultiGapTargetLog d k T center 0 =
      osiiAxisPairSimultaneousLogRealEmbed
        (fun i a => Real.log
          (osiiStep4MultiGapTargetCoeff d k T center 0 i a).re) := by
  have hcoeff (z : Complex) :
      osiiStep4MultiGapTargetCoeffLine d k T center 0 z =
        osiiStep4MultiGapTargetCoeff d k T center 0 := by
    funext i a
    simp only [osiiStep4MultiGapTargetCoeffLine,
      osiiStep4MultiGapTargetCoeff,
      osiiStep4MultiGapImaginaryBlock]
    congr 2
    funext mu
    simp [osiiStep4ComplexOfRealImag,
      osiiStep4MultiGapRealBlock]
  have hzero :
      (0 : Complex) ∈
        osiiStep4MultiGapTargetCoeffLineRightHalfPlane
          d k T center 0 := by
    simpa using
      osiiStep4MultiGapTargetCoeffLine_I_mul_real_mem_rightHalfPlane
        d k T hT center 0 hcenter 0
  calc
    osiiStep4MultiGapTargetLog d k T center 0 =
        osiiStep4MultiGapTargetLogLine d k T center 0 0 := by
      funext i a
      simp only [osiiStep4MultiGapTargetLog,
        osiiStep4MultiGapTargetLogLine]
      rw [hcoeff]
    _ = osiiAxisPairSimultaneousLogRealEmbed
          (fun i a => Real.log
            (osiiStep4MultiGapTargetCoeffLine
              d k T center 0 0 i a).re) :=
      osiiStep4MultiGapTargetLogLine_ofReal_eq_realEmbed
        d k T center 0 0 hzero
    _ = osiiAxisPairSimultaneousLogRealEmbed
          (fun i a => Real.log
            (osiiStep4MultiGapTargetCoeff d k T center 0 i a).re) := by
      rw [hcoeff]

theorem osiiStep4MultiGapTargetCoeff_ne_zero
    (d k : Nat) [NeZero d]
    (T : Real) (hT : 0 < T)
    (center y : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      0 < center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (i : Fin k) (a : osiiAxisPairIndex d) :
    osiiStep4MultiGapTargetCoeff d k T center y i a ≠ 0 := by
  intro hzero
  have hpos :=
    osiiStep4MultiGapTargetCoeff_re_pos
      d k T hT center y hcenter i a
  rw [hzero] at hpos
  simp at hpos

@[simp] theorem osiiStep4MultiGapTargetLog_exp
    (d k : Nat) [NeZero d]
    (T : Real) (hT : 0 < T)
    (center y : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      0 < center (finProdFinEquiv (i, (0 : Fin (d + 1)))))
    (i : Fin k) (a : osiiAxisPairIndex d) :
    Complex.exp (osiiStep4MultiGapTargetLog d k T center y i a) =
      osiiStep4MultiGapTargetCoeff d k T center y i a := by
  exact Complex.exp_log
    (osiiStep4MultiGapTargetCoeff_ne_zero
      d k T hT center y hcenter i a)

/-- Exact first-stage domain test for the target logarithmic tuple. -/
theorem osiiStep4MultiGapTargetLog_mem_logDomain_iff
    (d k : Nat) [NeZero d]
    (T : Real)
    (center y : Fin (k * (d + 1)) -> Real) :
    osiiStep4MultiGapTargetLog d k T center y ∈
        osiiAxisPairMultiGapLogDomain d k <->
      (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
        |Complex.arg
          (osiiStep4MultiGapTargetCoeff d k T center y i a)|) <
        Real.pi / 2 := by
  simp [osiiAxisPairMultiGapLogDomain,
    osiiStep4MultiGapTargetLog, Complex.log_im]

theorem osiiStep4MultiGapTargetLog_mem_logDomain_of_argumentBudget
    (d k : Nat) [NeZero d]
    (T : Real)
    (center y : Fin (k * (d + 1)) -> Real)
    (hbudget :
      (∑ i : Fin k, ∑ a : osiiAxisPairIndex d,
        |Complex.arg
          (osiiStep4MultiGapTargetCoeff d k T center y i a)|) <
        Real.pi / 2) :
    osiiStep4MultiGapTargetLog d k T center y ∈
      osiiAxisPairMultiGapLogDomain d k :=
  (osiiStep4MultiGapTargetLog_mem_logDomain_iff
    d k T center y).2 hbudget

end OSReconstruction
