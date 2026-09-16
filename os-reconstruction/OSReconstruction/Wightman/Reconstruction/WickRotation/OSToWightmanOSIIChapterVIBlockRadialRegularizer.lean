/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIPartialConvolutionKernel























noncomputable section

open MeasureTheory Metric Set
open scoped Classical

namespace OSReconstruction

/-- The canonical real-linear identification of a complex coordinate block
with its Euclidean `L2` realization. -/
def osiiStep4ComplexBlockToEuclideanCLE (q : ℕ) :
    (Fin q → ℂ) ≃L[ℝ] EuclideanSpace ℂ (Fin q) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin q => ℂ)).symm

@[simp]
theorem osiiStep4ComplexBlockToEuclideanCLE_apply
    (q : ℕ) (z : Fin q → ℂ) (i : Fin q) :
    osiiStep4ComplexBlockToEuclideanCLE q z i = z i := by
  rfl

/-- Taking real parts coordinatewise cannot increase the Euclidean block
norm. -/
theorem osiiStep4ComplexBlockRealPart_norm_le
    (q : ℕ) (z : Fin q → ℂ) :
    ‖osiiStep4ComplexBlockToEuclideanCLE q
        (fun mu => ((z mu).re : ℂ))‖ ≤
      ‖osiiStep4ComplexBlockToEuclideanCLE q z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro mu _
  have h := Complex.abs_re_le_norm (z mu)
  simp only [osiiStep4ComplexBlockToEuclideanCLE_apply,
    Complex.norm_real, Real.norm_eq_abs]
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 h

/-- The explicit unnormalized radial bump on one whole complex spacetime
block. -/
def osiiStep4ComplexBlockRadialRaw
    (q : ℕ) (rho : ℝ) (z : Fin q → ℂ) : ℝ :=
  (ContDiffBumpBase.ofInnerProductSpace
      (EuclideanSpace ℂ (Fin q))).toFun 2
    (((16 / rho : ℝ) : ℂ) • osiiStep4ComplexBlockToEuclideanCLE q z)

theorem osiiStep4ComplexBlockRadialRaw_apply
    (q : ℕ) (rho : ℝ) (z : Fin q → ℂ) :
    osiiStep4ComplexBlockRadialRaw q rho z =
      Real.smoothTransition
        (2 - ‖((16 / rho : ℝ) : ℂ) •
          osiiStep4ComplexBlockToEuclideanCLE q z‖) := by
  simp only [osiiStep4ComplexBlockRadialRaw,
    ContDiffBumpBase.ofInnerProductSpace]
  congr 1
  ring

/-- The unnormalized block bump at scale `rho` is the pullback of the
reference bump at scale `16` by real dilation. -/
theorem osiiStep4ComplexBlockRadialRaw_scale
    (q : ℕ) {rho : ℝ} (_hrho : 0 < rho)
    (z : Fin q → ℂ) :
    osiiStep4ComplexBlockRadialRaw q rho z =
      osiiStep4ComplexBlockRadialRaw q 16 ((16 / rho) • z) := by
  change
    (ContDiffBumpBase.ofInnerProductSpace
      (EuclideanSpace ℂ (Fin q))).toFun 2
        (((16 / rho : ℝ) : ℂ) •
          osiiStep4ComplexBlockToEuclideanCLE q z) =
      (ContDiffBumpBase.ofInnerProductSpace
        (EuclideanSpace ℂ (Fin q))).toFun 2
          (((16 / 16 : ℝ) : ℂ) •
            osiiStep4ComplexBlockToEuclideanCLE q ((16 / rho) • z))
  congr 1
  ext i
  simp [osiiStep4ComplexBlockToEuclideanCLE_apply]

theorem osiiStep4ComplexBlockRadialRaw_nonneg
    (q : ℕ) (rho : ℝ) (z : Fin q → ℂ) :
    0 ≤ osiiStep4ComplexBlockRadialRaw q rho z := by
  exact
    (ContDiffBumpBase.ofInnerProductSpace
      (EuclideanSpace ℂ (Fin q))).mem_Icc 2
        (((16 / rho : ℝ) : ℂ) •
          osiiStep4ComplexBlockToEuclideanCLE q z) |>.1

theorem osiiStep4ComplexBlockRadialRaw_contDiff
    (q : ℕ) {rho : ℝ} (_hrho : 0 < rho) :
    ContDiff ℝ (⊤ : ℕ∞) (osiiStep4ComplexBlockRadialRaw q rho) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  have hbase :
      ContDiffAt ℝ (⊤ : ℕ∞)
        (Function.uncurry
          (ContDiffBumpBase.ofInnerProductSpace
            (EuclideanSpace ℂ (Fin q))).toFun)
        ((2 : ℝ),
          ((16 / rho : ℝ) : ℂ) •
            osiiStep4ComplexBlockToEuclideanCLE q z) :=
    (ContDiffBumpBase.ofInnerProductSpace
      (EuclideanSpace ℂ (Fin q))).smooth.contDiffAt
        (prod_mem_nhds (Ioi_mem_nhds (by norm_num)) Filter.univ_mem)
  have hpair :
      ContDiffAt ℝ (⊤ : ℕ∞)
        (fun w : Fin q → ℂ =>
          ((2 : ℝ),
            ((16 / rho : ℝ) : ℂ) •
              osiiStep4ComplexBlockToEuclideanCLE q w)) z := by
    fun_prop
  change ContDiffAt ℝ (⊤ : ℕ∞)
    (fun w : Fin q → ℂ =>
      (ContDiffBumpBase.ofInnerProductSpace
        (EuclideanSpace ℂ (Fin q))).toFun 2
          (((16 / rho : ℝ) : ℂ) •
            osiiStep4ComplexBlockToEuclideanCLE q w)) z
  simpa only [Function.comp_def, Function.uncurry_apply_pair] using
    hbase.comp z hpair

/-- The block-Euclidean support ball, expressed on ordinary complex
coordinates. -/
def osiiStep4ComplexBlockBall
    (q : ℕ) (rho : ℝ) : Set (Fin q → ℂ) :=
  {z | ‖osiiStep4ComplexBlockToEuclideanCLE q z‖ < rho / 8}

theorem osiiStep4ComplexBlockRadialRaw_support_subset
    (q : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    Function.support (osiiStep4ComplexBlockRadialRaw q rho) ⊆
      osiiStep4ComplexBlockBall q rho := by
  intro z hz
  have hscaled :
      ((16 / rho : ℝ) : ℂ) •
          osiiStep4ComplexBlockToEuclideanCLE q z ∈
        Function.support
          ((ContDiffBumpBase.ofInnerProductSpace
            (EuclideanSpace ℂ (Fin q))).toFun 2) := by
    simpa [osiiStep4ComplexBlockRadialRaw, Function.mem_support] using hz
  rw [(ContDiffBumpBase.ofInnerProductSpace
    (EuclideanSpace ℂ (Fin q))).support 2 (by norm_num)] at hscaled
  rw [Metric.mem_ball, dist_zero_right] at hscaled
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 16 / rho)] at hscaled
  rw [osiiStep4ComplexBlockBall, Set.mem_setOf_eq]
  have hscale : 0 < 16 / rho := by positivity
  have hzlt :
      ‖osiiStep4ComplexBlockToEuclideanCLE q z‖ < 2 / (16 / rho) := by
    apply (lt_div_iff₀ hscale).2
    simpa [mul_comm] using hscaled
  have hcalc : 2 / (16 / rho) = rho / 8 := by
    field_simp
    norm_num
  rwa [hcalc] at hzlt

theorem osiiStep4ComplexBlockRadialRaw_hasCompactSupport
    (q : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    HasCompactSupport (osiiStep4ComplexBlockRadialRaw q rho) := by
  let e := osiiStep4ComplexBlockToEuclideanCLE q
  let K : Set (Fin q → ℂ) :=
    e.symm '' Metric.closedBall
      (0 : EuclideanSpace ℂ (Fin q)) (rho / 8)
  have hK : IsCompact K :=
    (isCompact_closedBall
      (0 : EuclideanSpace ℂ (Fin q)) (rho / 8)).image e.symm.continuous
  refine HasCompactSupport.of_support_subset_isCompact hK ?_
  intro z hz
  have hzball := osiiStep4ComplexBlockRadialRaw_support_subset q hrho hz
  refine ⟨e z, ?_, by simp [e]⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hzball.le

theorem osiiStep4ComplexBlockRadialRaw_integral_pos
    (q : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    0 < ∫ z : Fin q → ℂ, osiiStep4ComplexBlockRadialRaw q rho z := by
  apply
    (osiiStep4ComplexBlockRadialRaw_contDiff q hrho).continuous
      |>.integral_pos_of_hasCompactSupport_nonneg_nonzero
        (osiiStep4ComplexBlockRadialRaw_hasCompactSupport q hrho)
        (osiiStep4ComplexBlockRadialRaw_nonneg q rho)
        (x := 0)
  have hzero : osiiStep4ComplexBlockRadialRaw q rho 0 = 1 := by
    apply (ContDiffBumpBase.ofInnerProductSpace
      (EuclideanSpace ℂ (Fin q))).eq_one 2 (by norm_num)
    simp [osiiStep4ComplexBlockToEuclideanCLE]
  rw [hzero]
  exact one_ne_zero

/-- The real Jacobian of one complex `q`-block dilation has exponent `2q`. -/
theorem osiiStep4ComplexBlockRadialRaw_integral_scale
    (q : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    ∫ z : Fin q → ℂ, osiiStep4ComplexBlockRadialRaw q rho z =
      ((16 / rho) ^ (2 * q))⁻¹ *
        ∫ z : Fin q → ℂ,
          osiiStep4ComplexBlockRadialRaw q 16 z := by
  let a : ℝ := 16 / rho
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hfun :
      (fun z : Fin q → ℂ => osiiStep4ComplexBlockRadialRaw q rho z) =
        fun z => osiiStep4ComplexBlockRadialRaw q 16 (a • z) := by
    funext z
    simpa [a] using osiiStep4ComplexBlockRadialRaw_scale q hrho z
  rw [hfun]
  have hscale := Measure.integral_comp_smul_of_nonneg
    (volume : Measure (Fin q → ℂ))
    (fun z : Fin q → ℂ => osiiStep4ComplexBlockRadialRaw q 16 z)
    a (hR := ha.le)
  simpa [Module.finrank_pi_fintype, Complex.finrank_real_complex, a,
    mul_comm] using hscale

/-- The normalized radial density on one whole complex block. -/
def osiiStep4ComplexBlockRadialG
    (q : ℕ) (rho : ℝ) : (Fin q → ℂ) → ℝ := fun z =>
  osiiStep4ComplexBlockRadialRaw q rho z /
    ∫ w : Fin q → ℂ, osiiStep4ComplexBlockRadialRaw q rho w

theorem osiiStep4ComplexBlockRadialG_integral_one
    (q : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    ∫ z : Fin q → ℂ, osiiStep4ComplexBlockRadialG q rho z = 1 := by
  change
    (∫ z : Fin q → ℂ,
      osiiStep4ComplexBlockRadialRaw q rho z /
        ∫ w : Fin q → ℂ,
          osiiStep4ComplexBlockRadialRaw q rho w) = 1
  rw [integral_div,
    div_self (osiiStep4ComplexBlockRadialRaw_integral_pos q hrho).ne']

/-- Exact normalized dilation law for one complex spacetime block. -/
theorem osiiStep4ComplexBlockRadialG_scale
    (q : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (z : Fin q → ℂ) :
    osiiStep4ComplexBlockRadialG q rho z =
      (16 / rho) ^ (2 * q) *
        osiiStep4ComplexBlockRadialG q 16 ((16 / rho) • z) := by
  have ha : 16 / rho ≠ 0 := by positivity
  have hI :
      ∫ w : Fin q → ℂ, osiiStep4ComplexBlockRadialRaw q 16 w ≠ 0 :=
    (osiiStep4ComplexBlockRadialRaw_integral_pos q (by norm_num)).ne'
  simp only [osiiStep4ComplexBlockRadialG]
  rw [osiiStep4ComplexBlockRadialRaw_scale q hrho z,
    osiiStep4ComplexBlockRadialRaw_integral_scale q hrho]
  field_simp

theorem osiiStep4ComplexBlockRadialG_contDiff
    (q : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    ContDiff ℝ (⊤ : ℕ∞) (osiiStep4ComplexBlockRadialG q rho) :=
  (osiiStep4ComplexBlockRadialRaw_contDiff q hrho).div_const _

theorem osiiStep4ComplexBlockRadialG_support_subset
    (q : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    Function.support (osiiStep4ComplexBlockRadialG q rho) ⊆
      osiiStep4ComplexBlockBall q rho := by
  intro z hz
  apply osiiStep4ComplexBlockRadialRaw_support_subset q hrho
  simpa [osiiStep4ComplexBlockRadialG, Function.mem_support,
    (osiiStep4ComplexBlockRadialRaw_integral_pos q hrho).ne'] using hz

theorem osiiStep4ComplexBlockRadialG_hasCompactSupport
    (q : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    HasCompactSupport (osiiStep4ComplexBlockRadialG q rho) := by
  let e := osiiStep4ComplexBlockToEuclideanCLE q
  let K : Set (Fin q → ℂ) :=
    e.symm '' Metric.closedBall
      (0 : EuclideanSpace ℂ (Fin q)) (rho / 8)
  have hK : IsCompact K :=
    (isCompact_closedBall
      (0 : EuclideanSpace ℂ (Fin q)) (rho / 8)).image e.symm.continuous
  refine HasCompactSupport.of_support_subset_isCompact hK ?_
  intro z hz
  have hzball := osiiStep4ComplexBlockRadialG_support_subset q hrho hz
  refine ⟨e z, ?_, by simp [e]⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hzball.le

theorem osiiStep4ComplexBlockRadialG_eq_of_euclideanNorm_eq
    (q : ℕ) (rho : ℝ) (z w : Fin q → ℂ)
    (h : ‖osiiStep4ComplexBlockToEuclideanCLE q z‖ =
      ‖osiiStep4ComplexBlockToEuclideanCLE q w‖) :
    osiiStep4ComplexBlockRadialG q rho z =
      osiiStep4ComplexBlockRadialG q rho w := by
  simp only [osiiStep4ComplexBlockRadialG,
    osiiStep4ComplexBlockRadialRaw_apply]
  congr 2
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  rw [h]

theorem osiiStep4ComplexBlockRadialG_smul_of_norm_one
    (q : ℕ) (rho : ℝ) (u : ℂ) (hu : ‖u‖ = 1)
    (z : Fin q → ℂ) :
    osiiStep4ComplexBlockRadialG q rho (u • z) =
      osiiStep4ComplexBlockRadialG q rho z := by
  apply osiiStep4ComplexBlockRadialG_eq_of_euclideanNorm_eq
  have heq :
      osiiStep4ComplexBlockToEuclideanCLE q (u • z) =
        u • osiiStep4ComplexBlockToEuclideanCLE q z := by
    rfl
  rw [heq, norm_smul, hu, one_mul]



/-- Flatten complex spacetime blocks into the canonical product-coordinate
order. -/
def osiiStep4ComplexBlockFlattenMeasurableEquiv (k q : ℕ) :
    (Fin k → Fin q → ℂ) ≃ᵐ (Fin (k * q) → ℂ) :=
  (MeasurableEquiv.curry (Fin k) (Fin q) ℂ).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ => ℂ) finProdFinEquiv)

@[simp]
theorem osiiStep4ComplexBlockFlattenMeasurableEquiv_apply
    (k q : ℕ) (z : Fin k → Fin q → ℂ) (a : Fin (k * q)) :
    osiiStep4ComplexBlockFlattenMeasurableEquiv k q z a =
      z (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2 := by
  simp [osiiStep4ComplexBlockFlattenMeasurableEquiv,
    MeasurableEquiv.trans_apply, MeasurableEquiv.coe_curry_symm,
    MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Function.uncurry]

@[simp]
theorem osiiStep4ComplexBlockFlattenMeasurableEquiv_symm_apply
    (k q : ℕ) (z : Fin (k * q) → ℂ) (i : Fin k) (mu : Fin q) :
    (osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z i mu =
      z (finProdFinEquiv (i, mu)) := by
  rfl

theorem osiiStep4ComplexBlockFlattenMeasurableEquiv_differentiable
    (k q : ℕ) :
    Differentiable ℂ (osiiStep4ComplexBlockFlattenMeasurableEquiv k q) := by
  rw [differentiable_pi]
  intro a
  simpa only [osiiStep4ComplexBlockFlattenMeasurableEquiv_apply,
    Function.comp_def] using
    ((differentiable_apply (finProdFinEquiv.symm a).2 :
        Differentiable ℂ
          (fun z : Fin q → ℂ => z (finProdFinEquiv.symm a).2)).comp
      (differentiable_apply (finProdFinEquiv.symm a).1 :
        Differentiable ℂ
          (fun z : Fin k → Fin q → ℂ => z (finProdFinEquiv.symm a).1)))

theorem osiiStep4ComplexBlockFlattenMeasurableEquiv_symm_differentiable
    (k q : ℕ) :
    Differentiable ℂ
      (osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm := by
  rw [differentiable_pi]
  intro i
  rw [differentiable_pi]
  intro mu
  simpa only [osiiStep4ComplexBlockFlattenMeasurableEquiv_symm_apply] using
    (differentiable_apply (finProdFinEquiv (i, mu)) :
      Differentiable ℂ
        (fun z : Fin (k * q) → ℂ => z (finProdFinEquiv (i, mu))))

private theorem osiiStep4_volume_map_complex_curry_symm (k q : ℕ) :
    (volume : Measure (Fin k → Fin q → ℂ)).map
      (MeasurableEquiv.curry (Fin k) (Fin q) ℂ).symm =
        (volume : Measure (Fin k × Fin q → ℂ)) := by
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply
    (MeasurableEquiv.curry (Fin k) (Fin q) ℂ).symm.measurable
    (MeasurableSet.univ_pi hs)]
  have hpreimage :
      (MeasurableEquiv.curry (Fin k) (Fin q) ℂ).symm ⁻¹'
          (Set.univ.pi s) =
        Set.univ.pi
          (fun i => Set.univ.pi (fun mu => s (i, mu))) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_univ_pi,
      MeasurableEquiv.coe_curry_symm, Function.uncurry]
    exact ⟨fun h i mu => h (i, mu), fun h ⟨i, mu⟩ => h i mu⟩
  rw [hpreimage, volume_pi_pi]
  simp_rw [volume_pi_pi]
  rw [← Finset.prod_product', ← Finset.univ_product_univ]

theorem osiiStep4ComplexBlockFlattenMeasurableEquiv_measurePreserving
    (k q : ℕ) :
    MeasurePreserving (osiiStep4ComplexBlockFlattenMeasurableEquiv k q)
      (volume : Measure (Fin k → Fin q → ℂ))
      (volume : Measure (Fin (k * q) → ℂ)) := by
  exact
    (MeasurePreserving.mk
      (MeasurableEquiv.curry (Fin k) (Fin q) ℂ).symm.measurable
      (osiiStep4_volume_map_complex_curry_symm k q)).trans
    (volume_measurePreserving_piCongrLeft
      (fun _ : Fin (k * q) => ℂ) finProdFinEquiv)

/-- Product of the block-radial densities, expressed in flattened complex
coordinates. -/
def osiiStep4FullBlockRadialG
    (q k : ℕ) (rho : ℝ) : (Fin (k * q) → ℂ) → ℝ := fun z =>
  ∏ i : Fin k,
    osiiStep4ComplexBlockRadialG q rho
      ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z i)

/-- Exact normalized dilation law for the product of `k` complex
spacetime-block densities. -/
theorem osiiStep4FullBlockRadialG_scale
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (z : Fin (k * q) → ℂ) :
    osiiStep4FullBlockRadialG q k rho z =
      (16 / rho) ^ (2 * q * k) *
        osiiStep4FullBlockRadialG q k 16 ((16 / rho) • z) := by
  rw [osiiStep4FullBlockRadialG, osiiStep4FullBlockRadialG]
  simp_rw [osiiStep4ComplexBlockRadialG_scale q hrho]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [show ((16 / rho) ^ (2 * q)) ^ k =
      (16 / rho) ^ (2 * q * k) by rw [← pow_mul]]
  congr 1

/-- The product support: every complex spacetime block lies in its own
Euclidean ball of radius `rho / 8`. -/
def osiiStep4FullBlockRadialSupport
    (q k : ℕ) (rho : ℝ) : Set (Fin (k * q) → ℂ) :=
  {z | ∀ i : Fin k,
    (osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z i ∈
      osiiStep4ComplexBlockBall q rho}

theorem osiiStep4FullBlockRadialG_support_subset
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    Function.support (osiiStep4FullBlockRadialG q k rho) ⊆
      osiiStep4FullBlockRadialSupport q k rho := by
  intro z hz i
  apply osiiStep4ComplexBlockRadialG_support_subset q hrho
  apply Function.mem_support.mpr
  intro hi
  apply hz
  rw [osiiStep4FullBlockRadialG]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi

theorem osiiStep4FullBlockRadialG_continuous
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    Continuous (osiiStep4FullBlockRadialG q k rho) := by
  change Continuous (fun z : Fin (k * q) → ℂ =>
    ∏ i : Fin k,
      osiiStep4ComplexBlockRadialG q rho
        ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z i))
  apply continuous_finset_prod Finset.univ
  intro i _hi
  have hblock : Continuous
      (fun z : Fin (k * q) → ℂ =>
        (osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z i) := by
    apply continuous_pi
    intro mu
    simpa using
      (continuous_apply (finProdFinEquiv (i, mu)) :
        Continuous (fun z : Fin (k * q) → ℂ =>
          z (finProdFinEquiv (i, mu))))
  exact (osiiStep4ComplexBlockRadialG_contDiff q hrho).continuous.comp
    hblock

/-- The flattened product density is smooth as a real function on the full
complex coordinate space. -/
theorem osiiStep4FullBlockRadialG_contDiff
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    ContDiff ℝ (⊤ : ℕ∞) (osiiStep4FullBlockRadialG q k rho) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin (k * q) → ℂ =>
    ∏ i : Fin k,
      osiiStep4ComplexBlockRadialG q rho
        ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z i))
  apply contDiff_prod
  intro i _hi
  apply (osiiStep4ComplexBlockRadialG_contDiff q hrho).comp
  rw [contDiff_pi]
  intro mu
  change ContDiff ℝ (⊤ : ℕ∞)
    (ContinuousLinearMap.proj
      (R := ℝ)
      (ι := Fin (k * q))
      (φ := fun _ => ℂ)
      (finProdFinEquiv (i, mu)))
  exact (ContinuousLinearMap.proj
    (R := ℝ)
    (ι := Fin (k * q))
    (φ := fun _ => ℂ)
    (finProdFinEquiv (i, mu))).contDiff

theorem osiiStep4FullBlockRadialG_hasCompactSupport
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    HasCompactSupport (osiiStep4FullBlockRadialG q k rho) := by
  let eBlock := osiiStep4ComplexBlockToEuclideanCLE q
  let B : Set (Fin q → ℂ) :=
    eBlock.symm '' Metric.closedBall
      (0 : EuclideanSpace ℂ (Fin q)) (rho / 8)
  have hB : IsCompact B :=
    (isCompact_closedBall
      (0 : EuclideanSpace ℂ (Fin q)) (rho / 8)).image
        eBlock.symm.continuous
  let e := osiiStep4ComplexBlockFlattenMeasurableEquiv k q
  let KNested : Set (Fin k → Fin q → ℂ) :=
    Set.univ.pi fun _ : Fin k => B
  have hKNested : IsCompact KNested :=
    isCompact_univ_pi fun _ : Fin k => hB
  have hecont : Continuous (e : (Fin k → Fin q → ℂ) →
      (Fin (k * q) → ℂ)) := by
    apply continuous_pi
    intro a
    let i : Fin k := (finProdFinEquiv.symm a).1
    let mu : Fin q := (finProdFinEquiv.symm a).2
    have hcoord : Continuous (fun z : Fin k → Fin q → ℂ => z i mu) :=
      (continuous_apply mu).comp (continuous_apply i)
    simpa [e, i, mu,
      osiiStep4ComplexBlockFlattenMeasurableEquiv_apply] using hcoord
  let K : Set (Fin (k * q) → ℂ) := e '' KNested
  have hK : IsCompact K := hKNested.image hecont
  refine HasCompactSupport.of_support_subset_isCompact hK ?_
  intro z hz
  have hzsupport :=
    osiiStep4FullBlockRadialG_support_subset q k hrho hz
  refine ⟨e.symm z, ?_, by simp [e]⟩
  change (e.symm z) ∈ Set.univ.pi (fun _ : Fin k => B)
  rw [Set.mem_univ_pi]
  intro i
  have hiball := hzsupport i
  refine ⟨eBlock ((e.symm z) i), ?_, by simp [eBlock]⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hiball.le

theorem osiiStep4FullBlockRadialG_weighted_integrable
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (F : (Fin (k * q) → ℂ) → ℂ) (hF : Continuous F) :
    Integrable
      (fun z : Fin (k * q) → ℂ =>
        (osiiStep4FullBlockRadialG q k rho z : ℂ) * F z)
      (volume : Measure (Fin (k * q) → ℂ)) := by
  have hcont : Continuous
      (fun z : Fin (k * q) → ℂ =>
        (osiiStep4FullBlockRadialG q k rho z : ℂ) * F z) :=
    (Complex.continuous_ofReal.comp
      (osiiStep4FullBlockRadialG_continuous q k hrho)).mul hF
  have hGcompact : HasCompactSupport
      (fun z : Fin (k * q) → ℂ =>
        (osiiStep4FullBlockRadialG q k rho z : ℂ)) := by
    simpa [Function.comp_def] using
      (osiiStep4FullBlockRadialG_hasCompactSupport q k hrho).comp_left
        Complex.ofReal_zero
  have hcompact : HasCompactSupport
      (fun z : Fin (k * q) → ℂ =>
        (osiiStep4FullBlockRadialG q k rho z : ℂ) * F z) :=
    hGcompact.mul_right
  exact hcont.integrable_of_hasCompactSupport hcompact

/-- The concrete block-radial density satisfies the convolution-slice
integrability premise of the neutral partial-kernel theorem. -/
theorem osiiStep4FullBlockRadialG_convolution_integrable
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (z : Fin (k * q) → ℂ) :
    Integrable
      (fun z' : Fin (k * q) → ℂ =>
        osiiStep4FullBlockRadialG q k rho (z - z') *
          osiiStep4FullBlockRadialG q k rho z')
      (volume : Measure (Fin (k * q) → ℂ)) := by
  have hcont : Continuous
      (fun z' : Fin (k * q) → ℂ =>
        osiiStep4FullBlockRadialG q k rho (z - z') *
          osiiStep4FullBlockRadialG q k rho z') :=
    ((osiiStep4FullBlockRadialG_continuous q k hrho).comp
      (continuous_const.sub continuous_id)).mul
        (osiiStep4FullBlockRadialG_continuous q k hrho)
  have hcompact : HasCompactSupport
      (fun z' : Fin (k * q) → ℂ =>
        osiiStep4FullBlockRadialG q k rho (z - z') *
          osiiStep4FullBlockRadialG q k rho z') :=
    (osiiStep4FullBlockRadialG_hasCompactSupport q k hrho).mul_left
  exact hcont.integrable_of_hasCompactSupport hcompact

end OSReconstruction
