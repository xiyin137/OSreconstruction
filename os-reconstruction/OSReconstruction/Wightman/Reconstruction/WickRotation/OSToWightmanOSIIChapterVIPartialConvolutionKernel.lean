/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Pi
































noncomputable section

open MeasureTheory

namespace OSReconstruction

/-- Reassemble a complex configuration from real and imaginary parts. -/
def osiiStep4ComplexOfRealImag {m : ℕ}
    (x y : Fin m → ℝ) : Fin m → ℂ :=
  fun i => (x i : ℂ) + (y i : ℂ) * Complex.I

@[simp]
theorem osiiStep4ComplexOfRealImag_re {m : ℕ}
    (x y : Fin m → ℝ) (i : Fin m) :
    (osiiStep4ComplexOfRealImag x y i).re = x i := by
  simp [osiiStep4ComplexOfRealImag]

@[simp]
theorem osiiStep4ComplexOfRealImag_im {m : ℕ}
    (x y : Fin m → ℝ) (i : Fin m) :
    (osiiStep4ComplexOfRealImag x y i).im = y i := by
  simp [osiiStep4ComplexOfRealImag]

/-- Split a finite complex configuration into its real and imaginary parts. -/
def osiiStep4ComplexRealImagMeasurableEquiv (m : ℕ) :
    (Fin m → ℂ) ≃ᵐ ((Fin m → ℝ) × (Fin m → ℝ)) :=
  (MeasurableEquiv.piCongrRight
      (fun _ : Fin m => Complex.measurableEquivRealProd)).trans
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin m))

@[simp]
theorem osiiStep4ComplexRealImagMeasurableEquiv_symm_apply
    (m : ℕ) (p : (Fin m → ℝ) × (Fin m → ℝ)) :
    (osiiStep4ComplexRealImagMeasurableEquiv m).symm p =
      osiiStep4ComplexOfRealImag p.1 p.2 := by
  change (fun i => Complex.measurableEquivRealProd.symm (p.1 i, p.2 i)) = _
  funext i
  apply Complex.ext <;> simp [osiiStep4ComplexOfRealImag]

/-- The real/imaginary splitting preserves finite-dimensional Lebesgue
volume. -/
theorem osiiStep4ComplexRealImagMeasurableEquiv_measurePreserving (m : ℕ) :
    MeasurePreserving (osiiStep4ComplexRealImagMeasurableEquiv m)
      (volume : Measure (Fin m → ℂ))
      ((volume : Measure (Fin m → ℝ)).prod
        (volume : Measure (Fin m → ℝ))) := by
  exact
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin m)).comp
      (volume_preserving_pi
        (fun _ : Fin m => Complex.volume_preserving_equiv_real_prod))

/-- The same real/imaginary splitting with the imaginary integral outermost. -/
theorem osiiStep4_integral_complex_eq_integral_imag_real
    {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin m → ℂ) → E)
    (hf : Integrable f (volume : Measure (Fin m → ℂ))) :
    ∫ z, f z =
      ∫ y : Fin m → ℝ, ∫ x : Fin m → ℝ,
        f (osiiStep4ComplexOfRealImag x y) := by
  let e := osiiStep4ComplexRealImagMeasurableEquiv m
  have he : MeasurePreserving e
      (volume : Measure (Fin m → ℂ))
      ((volume : Measure (Fin m → ℝ)).prod
        (volume : Measure (Fin m → ℝ))) :=
    osiiStep4ComplexRealImagMeasurableEquiv_measurePreserving m
  have hf' : Integrable (fun p => f (e.symm p))
      ((volume : Measure (Fin m → ℝ)).prod
        (volume : Measure (Fin m → ℝ))) := by
    simpa [Function.comp_def] using he.symm.integrable_comp_of_integrable hf
  calc
    ∫ z, f z = ∫ p, f (e.symm p) := by
      simpa only [Measure.volume_eq_prod, Function.comp_def] using
        (he.symm.integral_comp' f).symm
    _ = ∫ y : Fin m → ℝ, ∫ x : Fin m → ℝ, f (e.symm (x, y)) := by
      exact integral_prod_symm _ hf'
    _ = ∫ y : Fin m → ℝ, ∫ x : Fin m → ℝ,
        f (osiiStep4ComplexOfRealImag x y) := by
      simp [e]

/-- The full complex convolution density `k(z) = ∫ g(z-z')g(z') dz'`. -/
def osiiStep4ComplexConvolutionDensity {m : ℕ}
    (g : (Fin m → ℂ) → ℝ) (z : Fin m → ℂ) : ℝ :=
  ∫ z' : Fin m → ℂ, g (z - z') * g z'

/-- The OS-II partial convolution kernel.  Only the real coordinates of
`z' = x' + i y'` are integrated; the auxiliary imaginary coordinate `y'`
remains a parameter. -/
def osiiStep4PartialConvolutionKernel {m : ℕ}
    (g : (Fin m → ℂ) → ℝ)
    (z : Fin m → ℂ) (y' : Fin m → ℝ) : ℝ :=
  ∫ x' : Fin m → ℝ,
    g (z - osiiStep4ComplexOfRealImag x' y') *
      g (osiiStep4ComplexOfRealImag x' y')

/-- Real/imaginary disintegration of the full complex convolution.  This is
the kernel identity immediately preceding OS-II `(6.5)`. -/
theorem osiiStep4ComplexConvolutionDensity_eq_integral_partial
    {m : ℕ} (g : (Fin m → ℂ) → ℝ) (z : Fin m → ℂ)
    (hconv : Integrable
      (fun z' : Fin m → ℂ => g (z - z') * g z')
      (volume : Measure (Fin m → ℂ))) :
    osiiStep4ComplexConvolutionDensity g z =
      ∫ y' : Fin m → ℝ,
        osiiStep4PartialConvolutionKernel g z y' := by
  simpa [osiiStep4ComplexConvolutionDensity,
    osiiStep4PartialConvolutionKernel] using
    osiiStep4_integral_complex_eq_integral_imag_real
      (fun z' : Fin m → ℂ => g (z - z') * g z') hconv

/-- The paper's regularized transform at the imaginary displacement `i y`.
The second imaginary variable `y'` is retained because it enters the partial
convolution kernel. -/
def osiiStep4PartialConvolutionTransform {m : ℕ}
    (g : (Fin m → ℂ) → ℝ)
    (F : (Fin m → ℂ) → ℂ)
    (c : Fin m → ℂ) (y y' : Fin m → ℝ) : ℂ :=
  ∫ x : Fin m → ℝ,
    F (c + osiiStep4ComplexOfRealImag x y) *
      (osiiStep4PartialConvolutionKernel g
        (osiiStep4ComplexOfRealImag x y) y' : ℂ)

/-- Exact Fubini identity behind OS-II `(6.6)`.  It rewrites convolution by
the full complex kernel as the double imaginary average of the partial
real-coordinate transform. -/
theorem osiiStep4_weightedComplexConvolution_eq_integral_partialTransform
    {m : ℕ}
    (g : (Fin m → ℂ) → ℝ)
    (F : (Fin m → ℂ) → ℂ)
    (c : Fin m → ℂ)
    (hconv : ∀ z : Fin m → ℂ,
      Integrable (fun z' : Fin m → ℂ => g (z - z') * g z')
        (volume : Measure (Fin m → ℂ)))
    (hweighted : Integrable
      (fun p : (Fin m → ℂ) × (Fin m → ℝ) =>
        F (c + p.1) *
          (osiiStep4PartialConvolutionKernel g p.1 p.2 : ℂ))
      ((volume : Measure (Fin m → ℂ)).prod
        (volume : Measure (Fin m → ℝ)))) :
    (∫ z : Fin m → ℂ,
        F (c + z) * (osiiStep4ComplexConvolutionDensity g z : ℂ)) =
      ∫ y' : Fin m → ℝ, ∫ y : Fin m → ℝ,
        osiiStep4PartialConvolutionTransform g F c y y' := by
  calc
    (∫ z : Fin m → ℂ,
        F (c + z) * (osiiStep4ComplexConvolutionDensity g z : ℂ)) =
        ∫ z : Fin m → ℂ, ∫ y' : Fin m → ℝ,
          F (c + z) *
            (osiiStep4PartialConvolutionKernel g z y' : ℂ) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [osiiStep4ComplexConvolutionDensity_eq_integral_partial g z (hconv z)]
      rw [← integral_complex_ofReal]
      exact (integral_const_mul
        (μ := (volume : Measure (Fin m → ℝ)))
        (F (c + z))
        (fun y' : Fin m → ℝ =>
          (osiiStep4PartialConvolutionKernel g z y' : ℂ))).symm
    _ = ∫ y' : Fin m → ℝ, ∫ z : Fin m → ℂ,
          F (c + z) *
            (osiiStep4PartialConvolutionKernel g z y' : ℂ) := by
      exact integral_integral_swap hweighted
    _ = ∫ y' : Fin m → ℝ, ∫ y : Fin m → ℝ,
          osiiStep4PartialConvolutionTransform g F c y y' := by
      apply integral_congr_ae
      filter_upwards [hweighted.prod_left_ae] with y' hy'
      simpa [osiiStep4PartialConvolutionTransform] using
        osiiStep4_integral_complex_eq_integral_imag_real
          (fun z : Fin m → ℂ =>
            F (c + z) *
              (osiiStep4PartialConvolutionKernel g z y' : ℂ)) hy'

/-- Mean-value corollary in the exact shape of OS-II `(6.6)`.  The analytic
mean-value property of the chosen full kernel remains an explicit premise. -/
theorem osiiStep4_partialConvolution_meanValue
    {m : ℕ}
    (g : (Fin m → ℂ) → ℝ)
    (F : (Fin m → ℂ) → ℂ)
    (c : Fin m → ℂ)
    (hconv : ∀ z : Fin m → ℂ,
      Integrable (fun z' : Fin m → ℂ => g (z - z') * g z')
        (volume : Measure (Fin m → ℂ)))
    (hweighted : Integrable
      (fun p : (Fin m → ℂ) × (Fin m → ℝ) =>
        F (c + p.1) *
          (osiiStep4PartialConvolutionKernel g p.1 p.2 : ℂ))
      ((volume : Measure (Fin m → ℂ)).prod
        (volume : Measure (Fin m → ℝ))))
    (hmean :
      (∫ z : Fin m → ℂ,
          F (c + z) * (osiiStep4ComplexConvolutionDensity g z : ℂ)) =
        F c) :
    F c =
      ∫ y' : Fin m → ℝ, ∫ y : Fin m → ℝ,
        osiiStep4PartialConvolutionTransform g F c y y' := by
  exact hmean.symm.trans
    (osiiStep4_weightedComplexConvolution_eq_integral_partialTransform
      g F c hconv hweighted)

end OSReconstruction
