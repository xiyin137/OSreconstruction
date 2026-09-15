/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Mathlib.Analysis.Complex.Tietze
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPartialConvolution

















noncomputable section

open Complex MeasureTheory Metric Set
open scoped Classical

namespace OSReconstruction

/-- A nonzero partial kernel lies in the doubled complex block support. -/
theorem osiiStep4PartialConvolutionKernel_nonzero_block_lt
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (z : Fin (k * q) → ℂ) (y' : Fin (k * q) → ℝ)
    (hz : osiiStep4PartialConvolutionKernel
      (osiiStep4FullBlockRadialG q k rho) z y' ≠ 0)
    (i : Fin k) :
    ‖osiiStep4ComplexBlockToEuclideanCLE q
      ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z i)‖ <
        rho / 4 := by
  obtain ⟨x', hx'⟩ : ∃ x' : Fin (k * q) → ℝ,
      osiiStep4FullBlockRadialG q k rho
          (z - osiiStep4ComplexOfRealImag x' y') *
        osiiStep4FullBlockRadialG q k rho
          (osiiStep4ComplexOfRealImag x' y') ≠ 0 := by
    by_contra h
    apply hz
    rw [osiiStep4PartialConvolutionKernel]
    apply integral_eq_zero_of_ae
    filter_upwards with x'
    by_contra hx'
    exact h ⟨x', hx'⟩
  have hleft := osiiStep4FullBlockRadialG_support_subset q k hrho
    (Function.mem_support.mpr (mul_ne_zero_iff.mp hx').1)
  have hright := osiiStep4FullBlockRadialG_support_subset q k hrho
    (Function.mem_support.mpr (mul_ne_zero_iff.mp hx').2)
  let z' := osiiStep4ComplexOfRealImag x' y'
  have hblock :
      (osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z i =
        (osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm (z - z') i +
          (osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z' i := by
    ext mu
    simp [z']
  rw [hblock, map_add]
  calc
    ‖osiiStep4ComplexBlockToEuclideanCLE q
          ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm
            (z - z') i) +
        osiiStep4ComplexBlockToEuclideanCLE q
          ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z' i)‖ ≤
        ‖osiiStep4ComplexBlockToEuclideanCLE q
          ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm
            (z - z') i)‖ +
        ‖osiiStep4ComplexBlockToEuclideanCLE q
          ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z' i)‖ :=
      norm_add_le _ _
    _ < rho / 8 + rho / 8 := by
      apply add_lt_add
      · simpa [osiiStep4FullBlockRadialSupport,
          osiiStep4ComplexBlockBall, z'] using hleft i
      · simpa [osiiStep4FullBlockRadialSupport,
          osiiStep4ComplexBlockBall, z'] using hright i
    _ = rho / 4 := by ring

/-- The open block polydisc corresponding to the closed support API. -/
def osiiStep4FullBlockRadialOpenSupport
    (q k : ℕ) (rho : ℝ) : Set (Fin (k * q) → ℂ) :=
  {z | ∀ i : Fin k,
    ‖osiiStep4ComplexBlockToEuclideanCLE q
      ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z i)‖ <
        rho / 8}

theorem isClosed_osiiStep4FullBlockRadialClosedSupport
    (q k : ℕ) (rho : ℝ) :
    IsClosed (osiiStep4FullBlockRadialClosedSupport q k rho) := by
  rw [show osiiStep4FullBlockRadialClosedSupport q k rho = ⋂ i : Fin k,
      {z : Fin (k * q) → ℂ |
        ‖osiiStep4ComplexBlockToEuclideanCLE q
          ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z i)‖ ≤
            rho / 8} by
    ext z
    simp [osiiStep4FullBlockRadialClosedSupport]]
  apply isClosed_iInter
  intro i
  exact isClosed_le
    (continuous_norm.comp
      ((osiiStep4ComplexBlockToEuclideanCLE q).continuous.comp
        (continuous_pi fun mu => by
          simpa using
            (continuous_apply (finProdFinEquiv (i, mu)) :
              Continuous (fun z : Fin (k * q) → ℂ =>
                z (finProdFinEquiv (i, mu))))))) continuous_const

/-- A locally holomorphic function admits a global continuous extension that
agrees at the center and on every nonzero partial-kernel contribution.  The
extension therefore has the same partial transforms and satisfies the global
block-radial mean-value identity. -/
theorem
    exists_osiiStep4FullBlockRadialG_local_continuous_extension
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (F : (Fin (k * q) → ℂ) → ℂ) (c : Fin (k * q) → ℂ)
    (U : Set (Fin (k * q) → ℂ))
    (hF : DifferentiableOn ℂ F U)
    (hsupport : ∀ z ∈ osiiStep4FullBlockRadialClosedSupport q k (3 * rho),
      c + z ∈ U) :
    ∃ G : (Fin (k * q) → ℂ) → ℂ,
      Continuous G ∧
      G c = F c ∧
      G c =
        (∫ y' : Fin (k * q) → ℝ, ∫ y : Fin (k * q) → ℝ,
          osiiStep4PartialConvolutionTransform
            (osiiStep4FullBlockRadialG q k rho) G c y y') ∧
      ∀ y y' : Fin (k * q) → ℝ,
        osiiStep4PartialConvolutionTransform
            (osiiStep4FullBlockRadialG q k rho) G c y y' =
          osiiStep4PartialConvolutionTransform
            (osiiStep4FullBlockRadialG q k rho) F c y y' := by
  let K : Set (Fin (k * q) → ℂ) :=
    (fun w => w - c) ⁻¹'
      osiiStep4FullBlockRadialClosedSupport q k (3 * rho)
  let V : Set (Fin (k * q) → ℂ) :=
    (fun w => w - c) ⁻¹'
      osiiStep4FullBlockRadialOpenSupport q k (3 * rho)
  have hK_closed : IsClosed K :=
    (isClosed_osiiStep4FullBlockRadialClosedSupport q k (3 * rho)).preimage
      (continuous_id.sub continuous_const)
  have hK_U : K ⊆ U := by
    intro w hw
    have := hsupport (w - c) hw
    simpa using this
  let FK : C(K, ℂ) :=
    ⟨fun w => F w,
      continuousOn_iff_continuous_restrict.mp
        (hF.continuousOn.mono hK_U)⟩
  obtain ⟨G, hG⟩ := FK.exists_restrict_eq hK_closed
  have hG_eq (w : Fin (k * q) → ℂ) (hw : w ∈ K) : G w = F w := by
    have h := DFunLike.congr_fun hG ⟨w, hw⟩
    exact h
  have hV_K : V ⊆ K := by
    intro w hw i
    exact (hw i).le
  have hG_diff : DifferentiableOn ℂ G V := by
    apply (hF.mono (hV_K.trans hK_U)).congr
    intro w hw
    exact hG_eq w (hV_K hw)
  have hsupport_two : ∀ z ∈
      osiiStep4FullBlockRadialClosedSupport q k (2 * rho),
      c + z ∈ V := by
    intro z hz i
    change ‖osiiStep4ComplexBlockToEuclideanCLE q
      ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm
        ((c + z) - c) i)‖ < 3 * rho / 8
    simpa only [add_sub_cancel_left] using
      (lt_of_le_of_lt (hz i)
        (by nlinarith [hrho] : 2 * rho / 8 < 3 * rho / 8))
  have hmeanG :=
    osiiStep4FullBlockRadialG_partialConvolution_meanValue_of_differentiableOn
      q k hrho G c G.continuous V hG_diff hsupport_two
  have hcK : c ∈ K := by
    intro i
    change ‖osiiStep4ComplexBlockToEuclideanCLE q
      ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm
        (c - c) i)‖ ≤ 3 * rho / 8
    have hzero :
        (osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm
            (0 : Fin (k * q) → ℂ) i = 0 := by
      ext mu
      rfl
    rw [sub_self, hzero, map_zero, norm_zero]
    positivity
  have htransform (y y' : Fin (k * q) → ℝ) :
      osiiStep4PartialConvolutionTransform
          (osiiStep4FullBlockRadialG q k rho) G c y y' =
        osiiStep4PartialConvolutionTransform
          (osiiStep4FullBlockRadialG q k rho) F c y y' := by
    rw [osiiStep4PartialConvolutionTransform,
      osiiStep4PartialConvolutionTransform]
    apply integral_congr_ae
    filter_upwards with x
    let z := osiiStep4ComplexOfRealImag x y
    let kernel := osiiStep4PartialConvolutionKernel
      (osiiStep4FullBlockRadialG q k rho) z y'
    by_cases hkernel : kernel = 0
    · simp [kernel, z, hkernel]
    · have hzblock :=
        osiiStep4PartialConvolutionKernel_nonzero_block_lt
          q k hrho z y' hkernel
      have hczK : c + z ∈ K := by
        intro i
        change ‖osiiStep4ComplexBlockToEuclideanCLE q
          ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm
            ((c + z) - c) i)‖ ≤ 3 * rho / 8
        simpa only [add_sub_cancel_left] using
          (hzblock i).le.trans
            (by nlinarith [hrho] : rho / 4 ≤ 3 * rho / 8)
      rw [hG_eq (c + z) hczK]
  exact ⟨G, G.continuous, hG_eq c hcK, hmeanG, htransform⟩

/-- Exact `(6.6)` for a function holomorphic only on a translated local
domain containing the three-radius block polydisc.  No values or continuity
outside that domain enter the resulting transform. -/
theorem
    osiiStep4FullBlockRadialG_partialConvolution_meanValue_local
    (q k : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (F : (Fin (k * q) → ℂ) → ℂ) (c : Fin (k * q) → ℂ)
    (U : Set (Fin (k * q) → ℂ))
    (hF : DifferentiableOn ℂ F U)
    (hsupport : ∀ z ∈ osiiStep4FullBlockRadialClosedSupport q k (3 * rho),
      c + z ∈ U) :
    F c =
      ∫ y' : Fin (k * q) → ℝ, ∫ y : Fin (k * q) → ℝ,
        osiiStep4PartialConvolutionTransform
          (osiiStep4FullBlockRadialG q k rho) F c y y' := by
  obtain ⟨G, _hG_cont, hGc, hmean, htransform⟩ :=
    exists_osiiStep4FullBlockRadialG_local_continuous_extension
      q k hrho F c U hF hsupport
  calc
    F c = G c := hGc.symm
    _ = ∫ y' : Fin (k * q) → ℝ, ∫ y : Fin (k * q) → ℝ,
          osiiStep4PartialConvolutionTransform
            (osiiStep4FullBlockRadialG q k rho) G c y y' := hmean
    _ = ∫ y' : Fin (k * q) → ℝ, ∫ y : Fin (k * q) → ℝ,
          osiiStep4PartialConvolutionTransform
            (osiiStep4FullBlockRadialG q k rho) F c y y' := by
      apply integral_congr_ae
      filter_upwards with y'
      apply integral_congr_ae
      filter_upwards with y
      exact htransform y y'

end OSReconstruction
