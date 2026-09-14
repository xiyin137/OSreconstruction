/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.EuclideanWeylProbe

/-!
# Euclidean Weyl Pairing Infrastructure

This file starts the scalar distribution-pairing stage for the Euclidean Weyl
route.  It keeps the integrals Banach-valued by first passing through the
finite coordinate-probe space from `EuclideanWeylProbe`.
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set Filter intervalIntegral FourierTransform
open scoped LineDeriv Convolution

namespace SCV

/-! ### Probe-family integrability -/

/-- Fourier transform is injective on the Euclidean Schwartz space. -/
theorem euclideanSchwartz_fourier_injective
    {ι : Type*} [Fintype ι] :
    Function.Injective
      (fun f : SchwartzMap (EuclideanSpace ℝ ι) ℂ => 𝓕 f) := by
  intro a b h
  have h' := congrArg
    (fun f : SchwartzMap (EuclideanSpace ℝ ι) ℂ => 𝓕⁻ f) h
  simpa [FourierTransform.fourierInv_fourier_eq] using h'

/-- Iterated directional derivatives commute with reflected Euclidean
translation. -/
theorem iteratedLineDerivOp_euclideanReflectedTranslate
    {ι : Type*} [Fintype ι] {n : ℕ}
    (u : Fin n → EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι)
    (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    (∂^{u} (euclideanReflectedTranslate x ρ) :
        SchwartzMap (EuclideanSpace ℝ ι) ℂ) =
      euclideanReflectedTranslate x
        (∂^{u} ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) := by
  induction n with
  | zero =>
      simp [LineDeriv.iteratedLineDerivOp_fin_zero]
  | succ n ih =>
      rw [LineDeriv.iteratedLineDerivOp_succ_left]
      rw [ih (Fin.tail u)]
      rw [lineDerivOp_euclideanReflectedTranslate]
      rw [LineDeriv.iteratedLineDerivOp_succ_left]

/-- Directional derivatives in the output variable commute with Euclidean
Schwartz convolution in the right argument. -/
theorem lineDerivOp_euclideanConvolutionTest_right
    {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℝ ι)
    (φ ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    (∂_{v} (euclideanConvolutionTest φ ρ) :
        SchwartzMap (EuclideanSpace ℝ ι) ℂ) =
      euclideanConvolutionTest φ
        (∂_{v} ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) := by
  apply_fun (fun f : SchwartzMap (EuclideanSpace ℝ ι) ℂ => 𝓕 f) using
    (euclideanSchwartz_fourier_injective (ι := ι))
  change 𝓕 (∂_{v} (euclideanConvolutionTest φ ρ) :
      SchwartzMap (EuclideanSpace ℝ ι) ℂ) =
    𝓕 (euclideanConvolutionTest φ
      (∂_{v} ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ))
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  unfold euclideanConvolutionTest
  rw [SchwartzMap.fourier_convolution]
  rw [SchwartzMap.fourier_convolution]
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  ext ξ
  have hinner :
      (fun x : EuclideanSpace ℝ ι => inner ℝ x v).HasTemperateGrowth :=
    ((innerSL ℝ).flip v).hasTemperateGrowth
  simp [SchwartzMap.pairing_apply_apply,
    SchwartzMap.smulLeftCLM_apply_apply hinner]
  exact RCLike.real_smul_eq_coe_mul (K := ℂ) (inner ℝ ξ v)
    ((𝓕 φ) ξ * (𝓕 ρ) ξ)

/-- Iterated directional derivatives in the output variable commute with
Euclidean Schwartz convolution in the right argument. -/
theorem iteratedLineDerivOp_euclideanConvolutionTest_right
    {ι : Type*} [Fintype ι] {n : ℕ}
    (u : Fin n → EuclideanSpace ℝ ι)
    (φ ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    (∂^{u} (euclideanConvolutionTest φ ρ) :
        SchwartzMap (EuclideanSpace ℝ ι) ℂ) =
      euclideanConvolutionTest φ
        (∂^{u} ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) := by
  induction n with
  | zero =>
      simp [LineDeriv.iteratedLineDerivOp_fin_zero]
  | succ n ih =>
      rw [LineDeriv.iteratedLineDerivOp_succ_left]
      rw [ih (Fin.tail u)]
      rw [lineDerivOp_euclideanConvolutionTest_right]
      rw [LineDeriv.iteratedLineDerivOp_succ_left]

/-- Directional derivatives in the output variable also commute with Euclidean
Schwartz convolution in the left argument.  This is the derivative placement
needed for approximate-identity estimates. -/
theorem lineDerivOp_euclideanConvolutionTest_left
    {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℝ ι)
    (φ ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    (∂_{v} (euclideanConvolutionTest φ ρ) :
        SchwartzMap (EuclideanSpace ℝ ι) ℂ) =
      euclideanConvolutionTest
        (∂_{v} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) ρ := by
  apply_fun (fun f : SchwartzMap (EuclideanSpace ℝ ι) ℂ => 𝓕 f) using
    (euclideanSchwartz_fourier_injective (ι := ι))
  change 𝓕 (∂_{v} (euclideanConvolutionTest φ ρ) :
      SchwartzMap (EuclideanSpace ℝ ι) ℂ) =
    𝓕 (euclideanConvolutionTest
      (∂_{v} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) ρ)
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  unfold euclideanConvolutionTest
  rw [SchwartzMap.fourier_convolution]
  rw [SchwartzMap.fourier_convolution]
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  ext ξ
  have hinner :
      (fun x : EuclideanSpace ℝ ι => inner ℝ x v).HasTemperateGrowth :=
    ((innerSL ℝ).flip v).hasTemperateGrowth
  simp [SchwartzMap.pairing_apply_apply,
    SchwartzMap.smulLeftCLM_apply_apply hinner]

/-- Iterated directional derivatives in the output variable commute with
Euclidean Schwartz convolution in the left argument. -/
theorem iteratedLineDerivOp_euclideanConvolutionTest_left
    {ι : Type*} [Fintype ι] {n : ℕ}
    (u : Fin n → EuclideanSpace ℝ ι)
    (φ ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    (∂^{u} (euclideanConvolutionTest φ ρ) :
        SchwartzMap (EuclideanSpace ℝ ι) ℂ) =
      euclideanConvolutionTest
        (∂^{u} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) ρ := by
  induction n with
  | zero =>
      simp [LineDeriv.iteratedLineDerivOp_fin_zero]
  | succ n ih =>
      rw [LineDeriv.iteratedLineDerivOp_succ_left]
      rw [ih (Fin.tail u)]
      rw [lineDerivOp_euclideanConvolutionTest_left]
      rw [LineDeriv.iteratedLineDerivOp_succ_left]

/-- Reflected translation by a compactly supported Euclidean Schwartz kernel is
continuous as a Schwartz-space-valued function of the center. -/
theorem continuous_euclideanReflectedTranslate_of_isCompactSupport
    {ι : Type*} [Fintype ι]
    (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (hρ_compact : HasCompactSupport (ρ : EuclideanSpace ℝ ι → ℂ)) :
    Continuous
      (fun x : EuclideanSpace ℝ ι => euclideanReflectedTranslate x ρ) := by
  refine continuous_iff_continuousAt.2 ?_
  intro x0
  have htranslate :=
    tendsto_euclideanTranslateSchwartz_nhds_of_isCompactSupport ρ hρ_compact (-x0)
  simpa [euclideanReflectedTranslate] using htranslate.comp (continuous_neg.tendsto x0)

/-- The finite Banach probe integrand used to turn the scalar pairing identity
into an ordinary Bochner-integral statement. -/
noncomputable def euclideanPairingProbeFamily
    {ι : Type*} [Fintype ι]
    (s : Finset (ℕ × ℕ))
    (φ ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (x : EuclideanSpace ℝ ι) :
    EuclideanProbeSpace (ι := ι) s :=
  euclideanProbeCLM s (φ x • euclideanReflectedTranslate x ρ)

/-- Pointwise form of one finite probe-family component. -/
theorem euclideanPairingProbeFamily_apply
    {ι : Type*} [Fintype ι]
    (s : Finset (ℕ × ℕ))
    (φ ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (x : EuclideanSpace ℝ ι)
    (p : ↑s.attach) (u : Fin p.1.1.2 → ι)
    (y : EuclideanSpace ℝ ι) :
    euclideanPairingProbeFamily s φ ρ x p u y =
      φ x * (euclideanPolynomialWeight p.1.1.1 y *
        euclideanReflectedTranslate x
          (∂^{euclideanCoordinateDirs u} ρ :
            SchwartzMap (EuclideanSpace ℝ ι) ℂ) y) := by
  have hderiv :
      (∂^{euclideanCoordinateDirs u} (φ x • euclideanReflectedTranslate x ρ) :
          SchwartzMap (EuclideanSpace ℝ ι) ℂ) =
        φ x •
          (∂^{euclideanCoordinateDirs u} (euclideanReflectedTranslate x ρ) :
            SchwartzMap (EuclideanSpace ℝ ι) ℂ) := by
    rw [← euclideanIteratedCoordinateLineDerivCLM_apply,
      ← euclideanIteratedCoordinateLineDerivCLM_apply]
    exact (euclideanIteratedCoordinateLineDerivCLM p.1.1.2 u).map_smul
      (φ x) (euclideanReflectedTranslate x ρ)
  rw [euclideanPairingProbeFamily, euclideanProbeCLM_apply, hderiv,
    iteratedLineDerivOp_euclideanReflectedTranslate]
  simp [smul_eq_mul, mul_left_comm]

/-- The finite Banach probe integrand is continuous when the reflected kernel
is compactly supported. -/
theorem continuous_euclideanPairingProbeFamily
    {ι : Type*} [Fintype ι]
    (s : Finset (ℕ × ℕ))
    (φ ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (hρ_compact : HasCompactSupport (ρ : EuclideanSpace ℝ ι → ℂ)) :
    Continuous (euclideanPairingProbeFamily s φ ρ) := by
  have hscalar : Continuous fun x : EuclideanSpace ℝ ι => φ x := φ.continuous
  have hreflect := continuous_euclideanReflectedTranslate_of_isCompactSupport ρ hρ_compact
  exact (euclideanProbeCLM s).continuous.comp
    (hscalar.smul hreflect)

/-- Compact support of the scalar test `φ` gives compact support of the whole
finite Banach probe integrand. -/
theorem hasCompactSupport_euclideanPairingProbeFamily
    {ι : Type*} [Fintype ι]
    (s : Finset (ℕ × ℕ))
    (φ ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (hφ_compact : HasCompactSupport (φ : EuclideanSpace ℝ ι → ℂ)) :
    HasCompactSupport (euclideanPairingProbeFamily s φ ρ) := by
  refine hφ_compact.mono' ?_
  intro x hx
  by_contra hxφ
  have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hxφ
  have hzero : euclideanPairingProbeFamily s φ ρ x = 0 := by
    simp [euclideanPairingProbeFamily, hφx]
  exact hx hzero

/-- The finite Banach probe integrand is Bochner integrable under the compact
support hypotheses used by the Euclidean Weyl regularization route. -/
theorem integrable_euclideanPairingProbeFamily
    {ι : Type*} [Fintype ι]
    (s : Finset (ℕ × ℕ))
    (φ ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (hφ_compact : HasCompactSupport (φ : EuclideanSpace ℝ ι → ℂ))
    (hρ_compact : HasCompactSupport (ρ : EuclideanSpace ℝ ι → ℂ)) :
    Integrable (euclideanPairingProbeFamily s φ ρ) := by
  exact (continuous_euclideanPairingProbeFamily s φ ρ hρ_compact).integrable_of_hasCompactSupport
    (hasCompactSupport_euclideanPairingProbeFamily s φ ρ hφ_compact)

/-- Evaluate the Bochner integral of the finite probe family componentwise. -/
theorem integral_euclideanPairingProbeFamily_apply
    {ι : Type*} [Fintype ι]
    (s : Finset (ℕ × ℕ))
    (φ ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (hφ_compact : HasCompactSupport (φ : EuclideanSpace ℝ ι → ℂ))
    (hρ_compact : HasCompactSupport (ρ : EuclideanSpace ℝ ι → ℂ))
    (p : ↑s.attach) (u : Fin p.1.1.2 → ι)
    (y : EuclideanSpace ℝ ι) :
    (∫ x : EuclideanSpace ℝ ι, euclideanPairingProbeFamily s φ ρ x) p u y =
      ∫ x : EuclideanSpace ℝ ι, euclideanPairingProbeFamily s φ ρ x p u y := by
  let Lp : EuclideanProbeSpace (ι := ι) s →L[ℂ]
      ((Fin p.1.1.2 → ι) →
        BoundedContinuousFunction (EuclideanSpace ℝ ι) ℂ) :=
    ContinuousLinearMap.proj
      (R := ℂ)
      (φ := fun p : ↑s.attach =>
        (Fin p.1.1.2 → ι) →
          BoundedContinuousFunction (EuclideanSpace ℝ ι) ℂ)
      p
  let Lu : ((Fin p.1.1.2 → ι) →
        BoundedContinuousFunction (EuclideanSpace ℝ ι) ℂ) →L[ℂ]
      BoundedContinuousFunction (EuclideanSpace ℝ ι) ℂ :=
    ContinuousLinearMap.proj
      (R := ℂ)
      (φ := fun _ : Fin p.1.1.2 → ι =>
        BoundedContinuousFunction (EuclideanSpace ℝ ι) ℂ)
      u
  let Ly :
      BoundedContinuousFunction (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ :=
    BoundedContinuousFunction.evalCLM ℂ y
  let L : EuclideanProbeSpace (ι := ι) s →L[ℂ] ℂ :=
    Ly.comp (Lu.comp Lp)
  change L (∫ x : EuclideanSpace ℝ ι, euclideanPairingProbeFamily s φ ρ x) =
    ∫ x : EuclideanSpace ℝ ι, L (euclideanPairingProbeFamily s φ ρ x)
  exact
    ((ContinuousLinearMap.integral_comp_comm L
      (integrable_euclideanPairingProbeFamily s φ ρ hφ_compact hρ_compact)).symm)

/-- Componentwise integral identity for the finite probe family. -/
theorem integral_euclideanPairingProbeFamily_component_eq_probe_convolution
    {ι : Type*} [Fintype ι]
    (s : Finset (ℕ × ℕ))
    (φ ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (p : ↑s.attach) (u : Fin p.1.1.2 → ι)
    (y : EuclideanSpace ℝ ι) :
    ∫ x : EuclideanSpace ℝ ι, euclideanPairingProbeFamily s φ ρ x p u y =
      euclideanProbeCLM s (euclideanConvolutionTest φ ρ) p u y := by
  rw [euclideanProbeCLM_apply]
  rw [iteratedLineDerivOp_euclideanConvolutionTest_right]
  rw [euclideanConvolutionTest_apply_reflectedTranslate]
  calc
    ∫ x : EuclideanSpace ℝ ι, euclideanPairingProbeFamily s φ ρ x p u y
        = ∫ x : EuclideanSpace ℝ ι,
            euclideanPolynomialWeight p.1.1.1 y *
              (euclideanReflectedTranslate x
                (∂^{euclideanCoordinateDirs u} ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) y *
                  φ x) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          rw [euclideanPairingProbeFamily_apply]
          ring
    _ = euclideanPolynomialWeight p.1.1.1 y *
          ∫ x : EuclideanSpace ℝ ι,
            euclideanReflectedTranslate x
              (∂^{euclideanCoordinateDirs u} ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) y *
                φ x := by
          exact
            MeasureTheory.integral_const_mul
              (μ := MeasureTheory.volume)
              (euclideanPolynomialWeight p.1.1.1 y)
              (fun x : EuclideanSpace ℝ ι =>
                euclideanReflectedTranslate x
                  (∂^{euclideanCoordinateDirs u} ρ :
                    SchwartzMap (EuclideanSpace ℝ ι) ℂ) y * φ x)

/-- The Bochner integral of the finite probe family is the probe of the
Euclidean convolution test. -/
theorem integral_euclideanPairingProbeFamily_eq_probe_convolution
    {ι : Type*} [Fintype ι]
    (s : Finset (ℕ × ℕ))
    (φ ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (hφ_compact : HasCompactSupport (φ : EuclideanSpace ℝ ι → ℂ))
    (hρ_compact : HasCompactSupport (ρ : EuclideanSpace ℝ ι → ℂ)) :
    ∫ x : EuclideanSpace ℝ ι, euclideanPairingProbeFamily s φ ρ x =
      euclideanProbeCLM s (euclideanConvolutionTest φ ρ) := by
  ext p u y
  rw [integral_euclideanPairingProbeFamily_apply s φ ρ hφ_compact hρ_compact p u y]
  exact integral_euclideanPairingProbeFamily_component_eq_probe_convolution s φ ρ p u y

/-- Scalar distribution-pairing identity for compactly supported regularizing
kernels.  This is the finite-probe replacement for the unavailable
`SchwartzMap`-valued Bochner integral. -/
theorem regularizedDistribution_integral_pairing
    {ι : Type*} [Fintype ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (hρ_compact : HasCompactSupport (ρ : EuclideanSpace ℝ ι → ℂ))
    (hφ_compact : HasCompactSupport (φ : EuclideanSpace ℝ ι → ℂ)) :
    ∫ x : EuclideanSpace ℝ ι,
        T (euclideanReflectedTranslate x ρ) * φ x =
      T (euclideanConvolutionTest φ ρ) := by
  obtain ⟨s, G, hTG⟩ := euclideanSchwartzFunctional_exists_probe_factorization T
  have hT_apply :
      ∀ f : SchwartzMap (EuclideanSpace ℝ ι) ℂ,
        T f = G (euclideanProbeCLM s f) := by
    intro f
    exact congrArg (fun L => L f) hTG
  calc
    ∫ x : EuclideanSpace ℝ ι,
        T (euclideanReflectedTranslate x ρ) * φ x
        = ∫ x : EuclideanSpace ℝ ι,
            T (φ x • euclideanReflectedTranslate x ρ) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          rw [map_smul]
          simp [smul_eq_mul, mul_comm]
    _ = ∫ x : EuclideanSpace ℝ ι,
          G (euclideanPairingProbeFamily s φ ρ x) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          rw [hT_apply]
          rfl
    _ = G (∫ x : EuclideanSpace ℝ ι, euclideanPairingProbeFamily s φ ρ x) := by
          exact G.integral_comp_comm
            (integrable_euclideanPairingProbeFamily s φ ρ hφ_compact hρ_compact)
    _ = G (euclideanProbeCLM s (euclideanConvolutionTest φ ρ)) := by
          rw [integral_euclideanPairingProbeFamily_eq_probe_convolution
            s φ ρ hφ_compact hρ_compact]
    _ = T (euclideanConvolutionTest φ ρ) := by
          rw [hT_apply]

end SCV
