/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPartialKernelFactorization














noncomputable section

open MeasureTheory
open scoped Classical

namespace OSReconstruction

/-- Apply a real matrix simultaneously to the real and imaginary parts of a
complex spacetime block. -/
def osiiStep4RealMatrixComplexAction {q : Nat}
    (R : Matrix (Fin q) (Fin q) Real)
    (z : Fin q -> Complex) : Fin q -> Complex :=
  osiiStep4ComplexOfRealImag
    (R.mulVec fun mu => (z mu).re)
    (R.mulVec fun mu => (z mu).im)

@[simp] theorem osiiStep4RealMatrixComplexAction_re {q : Nat}
    (R : Matrix (Fin q) (Fin q) Real)
    (z : Fin q -> Complex) (mu : Fin q) :
    (osiiStep4RealMatrixComplexAction R z mu).re =
      R.mulVec (fun nu => (z nu).re) mu := by
  simp [osiiStep4RealMatrixComplexAction]

@[simp] theorem osiiStep4RealMatrixComplexAction_im {q : Nat}
    (R : Matrix (Fin q) (Fin q) Real)
    (z : Fin q -> Complex) (mu : Fin q) :
    (osiiStep4RealMatrixComplexAction R z mu).im =
      R.mulVec (fun nu => (z nu).im) mu := by
  simp [osiiStep4RealMatrixComplexAction]

theorem osiiStep4RealMatrixComplexAction_ofRealImag {q : Nat}
    (R : Matrix (Fin q) (Fin q) Real)
    (x y : Fin q -> Real) :
    osiiStep4RealMatrixComplexAction R
        (osiiStep4ComplexOfRealImag x y) =
      osiiStep4ComplexOfRealImag (R.mulVec x) (R.mulVec y) := by
  apply funext
  intro mu
  apply Complex.ext
  · simp only [osiiStep4RealMatrixComplexAction_re,
      osiiStep4ComplexOfRealImag_re]
  · simp only [osiiStep4RealMatrixComplexAction_im,
      osiiStep4ComplexOfRealImag_im]

theorem osiiStep4RealMatrixComplexAction_sub {q : Nat}
    (R : Matrix (Fin q) (Fin q) Real)
    (z w : Fin q -> Complex) :
    osiiStep4RealMatrixComplexAction R (z - w) =
      osiiStep4RealMatrixComplexAction R z -
        osiiStep4RealMatrixComplexAction R w := by
  ext mu
  apply Complex.ext
  · simp only [osiiStep4RealMatrixComplexAction_re, Pi.sub_apply,
      Complex.sub_re]
    exact congrFun
      (Matrix.mulVec_sub R (fun nu => (z nu).re) (fun nu => (w nu).re)) mu
  · simp only [osiiStep4RealMatrixComplexAction_im, Pi.sub_apply,
      Complex.sub_im]
    exact congrFun
      (Matrix.mulVec_sub R (fun nu => (z nu).im) (fun nu => (w nu).im)) mu

/-- A real orthogonal matrix preserves the sum of coordinate squares. -/
theorem osiiStep4_sum_sq_matrix_mulVec {q : Nat}
    (R : Matrix (Fin q) (Fin q) Real)
    (hR : R.transpose * R = 1)
    (x : Fin q -> Real) :
    (Finset.univ.sum fun mu => (R.mulVec x mu) ^ 2) =
      Finset.univ.sum fun mu => (x mu) ^ 2 := by
  have hvec : Matrix.vecMul (R.mulVec x) R = x := by
    rw [← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hR]
    simp
  calc
    (Finset.univ.sum fun mu => (R.mulVec x mu) ^ 2) =
        dotProduct (R.mulVec x) (R.mulVec x) := by
      simp [dotProduct, pow_two]
    _ = dotProduct (Matrix.vecMul (R.mulVec x) R) x := by
      rw [Matrix.dotProduct_mulVec]
    _ = dotProduct x x := by rw [hvec]
    _ = Finset.univ.sum fun mu => (x mu) ^ 2 := by
      simp [dotProduct, pow_two]

/-- Rotating both real components of a complex block preserves its Euclidean
norm. -/
theorem osiiStep4RealMatrixComplexAction_euclideanNorm {q : Nat}
    (R : Matrix (Fin q) (Fin q) Real)
    (hR : R.transpose * R = 1)
    (z : Fin q -> Complex) :
    ‖osiiStep4ComplexBlockToEuclideanCLE q
        (osiiStep4RealMatrixComplexAction R z)‖ =
      ‖osiiStep4ComplexBlockToEuclideanCLE q z‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [osiiStep4ComplexBlockToEuclideanCLE_apply, Complex.sq_norm,
    Complex.normSq_apply, osiiStep4RealMatrixComplexAction_re,
    osiiStep4RealMatrixComplexAction_im]
  have hre := osiiStep4_sum_sq_matrix_mulVec R hR
    (fun nu => (z nu).re)
  have him := osiiStep4_sum_sq_matrix_mulVec R hR
    (fun nu => (z nu).im)
  simp only [pow_two] at hre him
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hre, him]

/-- The one-block radial density is invariant under a real orthogonal
transformation of the spacetime coordinates. -/
theorem osiiStep4ComplexBlockRadialG_realMatrix_invariant {q : Nat}
    (R : Matrix (Fin q) (Fin q) Real)
    (hR : R.transpose * R = 1)
    (rho : Real) (z : Fin q -> Complex) :
    osiiStep4ComplexBlockRadialG q rho
        (osiiStep4RealMatrixComplexAction R z) =
      osiiStep4ComplexBlockRadialG q rho z := by
  apply osiiStep4ComplexBlockRadialG_eq_of_euclideanNorm_eq
  exact osiiStep4RealMatrixComplexAction_euclideanNorm R hR z

/-- An orthogonal real matrix as a measurable equivalence, with transpose as
inverse. -/
noncomputable def osiiStep4RealOrthogonalMeasurableEquiv {q : Nat}
    (R : Matrix (Fin q) (Fin q) Real)
    (hR : R.transpose * R = 1) :
    (Fin q -> Real) ≃ᵐ (Fin q -> Real) := by
  have hR' : R * R.transpose = 1 := mul_eq_one_comm.mpr hR
  exact
    { toEquiv :=
        { toFun := fun x => R.mulVec x
          invFun := fun x => R.transpose.mulVec x
          left_inv := fun x => by
            change R.transpose.mulVec (R.mulVec x) = x
            rw [Matrix.mulVec_mulVec, hR]
            simp
          right_inv := fun x => by
            change R.mulVec (R.transpose.mulVec x) = x
            rw [Matrix.mulVec_mulVec, hR']
            simp }
      measurable_toFun := by
        simpa [Matrix.toLin'_apply] using
          (LinearMap.continuous_of_finiteDimensional
            (Matrix.toLin' R)).measurable
      measurable_invFun := by
        simpa [Matrix.toLin'_apply] using
          (LinearMap.continuous_of_finiteDimensional
            (Matrix.toLin' R.transpose)).measurable }

theorem osiiStep4RealOrthogonalMeasurableEquiv_measurePreserving {q : Nat}
    (R : Matrix (Fin q) (Fin q) Real)
    (hR : R.transpose * R = 1) :
    MeasurePreserving (osiiStep4RealOrthogonalMeasurableEquiv R hR)
      volume volume := by
  have hdet : R.det ≠ 0 := by
    intro h
    have hdetR := congrArg Matrix.det hR
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, h, mul_zero]
      at hdetR
    exact zero_ne_one hdetR
  have habs : |R.det| = 1 := by
    have hsq : R.det * R.det = 1 := by
      have hdetR := congrArg Matrix.det hR
      rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hdetR
    rcases mul_self_eq_one_iff.mp hsq with h | h <;> simp [h]
  change MeasurePreserving (fun x : Fin q -> Real => R.mulVec x)
    volume volume
  rw [show (fun x : Fin q -> Real => R.mulVec x) = Matrix.toLin' R by
    ext x
    simp [Matrix.toLin'_apply]]
  constructor
  · exact (LinearMap.continuous_of_finiteDimensional _).measurable
  · rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hdet]
    simp [abs_inv, habs]

/-- The one-block partial kernel is invariant when its complex argument and
auxiliary imaginary vector are rotated together. -/
theorem osiiStep4ComplexBlockPartialConvolutionKernel_realMatrix_invariant
    {q : Nat}
    (R : Matrix (Fin q) (Fin q) Real)
    (hR : R.transpose * R = 1)
    (rho : Real) (z : Fin q -> Complex) (y' : Fin q -> Real) :
    osiiStep4ComplexBlockPartialConvolutionKernel q rho
        (osiiStep4RealMatrixComplexAction R z) (R.mulVec y') =
      osiiStep4ComplexBlockPartialConvolutionKernel q rho z y' := by
  rw [osiiStep4ComplexBlockPartialConvolutionKernel,
    osiiStep4PartialConvolutionKernel]
  let f : (Fin q -> Real) -> Real := fun x =>
    osiiStep4ComplexBlockRadialG q rho
        (osiiStep4RealMatrixComplexAction R z -
          osiiStep4ComplexOfRealImag x (R.mulVec y')) *
      osiiStep4ComplexBlockRadialG q rho
        (osiiStep4ComplexOfRealImag x (R.mulVec y'))
  let e := osiiStep4RealOrthogonalMeasurableEquiv R hR
  have he : MeasurePreserving e volume volume :=
    osiiStep4RealOrthogonalMeasurableEquiv_measurePreserving R hR
  calc
    (∫ x : Fin q -> Real,
        osiiStep4ComplexBlockRadialG q rho
            (osiiStep4RealMatrixComplexAction R z -
              osiiStep4ComplexOfRealImag x (R.mulVec y')) *
          osiiStep4ComplexBlockRadialG q rho
            (osiiStep4ComplexOfRealImag x (R.mulVec y'))) =
        ∫ x : Fin q -> Real, f x := by rfl
    _ = ∫ x : Fin q -> Real, f (e x) :=
      (he.integral_comp' f).symm
    _ = ∫ x : Fin q -> Real,
        osiiStep4ComplexBlockRadialG q rho
            (z - osiiStep4ComplexOfRealImag x y') *
          osiiStep4ComplexBlockRadialG q rho
            (osiiStep4ComplexOfRealImag x y') := by
      apply integral_congr_ae
      filter_upwards with x
      change f (R.mulVec x) = _
      dsimp only [f]
      rw [show osiiStep4ComplexOfRealImag (R.mulVec x) (R.mulVec y') =
          osiiStep4RealMatrixComplexAction R
            (osiiStep4ComplexOfRealImag x y') by
        exact (osiiStep4RealMatrixComplexAction_ofRealImag R x y').symm]
      rw [← osiiStep4RealMatrixComplexAction_sub]
      rw [osiiStep4ComplexBlockRadialG_realMatrix_invariant R hR,
        osiiStep4ComplexBlockRadialG_realMatrix_invariant R hR]



end OSReconstruction
