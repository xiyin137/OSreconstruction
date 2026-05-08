import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedFullFrame

/-!
# Derivative of the full-frame oriented hypersurface equation

This file proves the first derivative facts needed by the full-frame
local-image route.  The regularity theorem below uses the actual Frechet
derivative of the hypersurface equation and the determinant-coordinate
direction; the full Jacobi trace formula identifying the derivative with the
linearized trace expression remains a separate tangent-space target.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

variable {d : ℕ}

/-- The full-frame oriented hypersurface equation is smooth. -/
theorem contDiff_sourceFullFrameOrientedEquation
    (d : ℕ) :
    ContDiff ℂ ⊤ (sourceFullFrameOrientedEquation d) := by
  unfold sourceFullFrameOrientedEquation
  have hdet :
      ContDiff ℂ ⊤
        (fun H : SourceFullFrameOrientedCoord d =>
          ∑ σ : Equiv.Perm (Fin (d + 1)),
            (↑σ.sign : ℂ) * ∏ i : Fin (d + 1), H.1 (σ i) i) := by
    apply ContDiff.sum
    intro σ _
    apply contDiff_const.mul
    apply contDiff_prod
    intro i _
    fun_prop
  have heq :
      (fun H : SourceFullFrameOrientedCoord d =>
          (Matrix.of H.1).det) =
        fun H =>
          ∑ σ : Equiv.Perm (Fin (d + 1)),
            (↑σ.sign : ℂ) * ∏ i : Fin (d + 1), H.1 (σ i) i := by
    ext H
    exact (Matrix.of H.1).det_apply'
  have hdet' :
      ContDiff ℂ ⊤
        (fun H : SourceFullFrameOrientedCoord d =>
          (Matrix.of H.1).det) := by
    simpa [heq] using hdet
  exact hdet'.sub (contDiff_const.mul (contDiff_snd.pow 2))

/-- The full-frame oriented hypersurface equation is differentiable. -/
theorem differentiable_sourceFullFrameOrientedEquation
    (d : ℕ) :
    Differentiable ℂ (sourceFullFrameOrientedEquation d) :=
  (contDiff_sourceFullFrameOrientedEquation d).differentiable (by simp)

/-- The actual Frechet derivative of the oriented equation exists at `H0`. -/
theorem sourceFullFrameOrientedEquation_hasFDerivAt
    (d : ℕ) (H0 : SourceFullFrameOrientedGramData d) :
    HasFDerivAt
      (sourceFullFrameOrientedEquation d)
      (fderiv ℂ (sourceFullFrameOrientedEquation d) H0.toCoord)
      H0.toCoord :=
  (differentiable_sourceFullFrameOrientedEquation d).differentiableAt.hasFDerivAt

/-- Along the determinant-coordinate line the full-frame oriented equation has
the expected one-variable derivative. -/
theorem sourceFullFrameOrientedEquation_hasDerivAt_detLine
    (d : ℕ) (H0 : SourceFullFrameOrientedGramData d) :
    HasDerivAt
      (fun t : ℂ =>
        sourceFullFrameOrientedEquation d
          (H0.toCoord + t • sourceFullFrameDetDirection d))
      (-((2 : ℂ) * minkowskiMetricDet d * H0.det)) 0 := by
  have hlin : HasDerivAt (fun t : ℂ => H0.det + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_add H0.det
  have hsq :
      HasDerivAt (fun t : ℂ => (H0.det + t) ^ 2)
        ((2 : ℂ) * H0.det) 0 := by
    simpa using hlin.pow 2
  have hterm :
      HasDerivAt
        (fun t : ℂ => minkowskiMetricDet d * (H0.det + t) ^ 2)
        (minkowskiMetricDet d * ((2 : ℂ) * H0.det)) 0 :=
    hsq.const_mul (minkowskiMetricDet d)
  have hconst :
      HasDerivAt (fun _ : ℂ => (Matrix.of H0.gram).det) 0 0 :=
    hasDerivAt_const (0 : ℂ) ((Matrix.of H0.gram).det)
  have hsub := hconst.sub hterm
  simpa [sourceFullFrameOrientedEquation, sourceFullFrameDetDirection,
    SourceFullFrameOrientedGramData.toCoord, mul_comm, mul_left_comm,
    mul_assoc] using hsub

/-- The actual Frechet derivative of the oriented equation on the pure
determinant-coordinate direction. -/
theorem sourceFullFrameOrientedEquation_fderiv_detDirection
    (d : ℕ) (H0 : SourceFullFrameOrientedGramData d) :
    (fderiv ℂ (sourceFullFrameOrientedEquation d) H0.toCoord)
        (sourceFullFrameDetDirection d) =
      -((2 : ℂ) * minkowskiMetricDet d * H0.det) := by
  have hf :
      DifferentiableAt ℂ
        (sourceFullFrameOrientedEquation d) H0.toCoord :=
    (differentiable_sourceFullFrameOrientedEquation d).differentiableAt
  have hline :
      HasDerivAt
        (fun t : ℂ => H0.toCoord + t • sourceFullFrameDetDirection d)
        (sourceFullFrameDetDirection d) 0 := by
    simpa using
      ((hasDerivAt_id (0 : ℂ)).smul_const
        (sourceFullFrameDetDirection d)).const_add H0.toCoord
  have hcomp := hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  exact hcomp.unique
    (sourceFullFrameOrientedEquation_hasDerivAt_detLine d H0)

/-- Nonzero oriented determinant makes the actual Frechet derivative nonzero
in the determinant-coordinate direction. -/
theorem sourceFullFrameOrientedEquation_fderiv_detDirection_ne_zero
    (d : ℕ) {H0 : SourceFullFrameOrientedGramData d}
    (hH0 : H0.det ≠ 0) :
    (fderiv ℂ (sourceFullFrameOrientedEquation d) H0.toCoord)
        (sourceFullFrameDetDirection d) ≠ 0 := by
  rw [sourceFullFrameOrientedEquation_fderiv_detDirection]
  exact
    neg_ne_zero.mpr
      (mul_ne_zero
        (mul_ne_zero (by norm_num) (minkowskiMetricDet_ne_zero d)) hH0)

/-- Nonzero oriented determinant makes the actual Frechet derivative onto
`ℂ`. -/
theorem sourceFullFrameOrientedEquation_fderiv_surjective_of_det_ne_zero
    (d : ℕ) {H0 : SourceFullFrameOrientedGramData d}
    (hH0 : H0.det ≠ 0) :
    Function.Surjective
      (fderiv ℂ (sourceFullFrameOrientedEquation d) H0.toCoord) := by
  intro c
  let a : ℂ :=
    (fderiv ℂ (sourceFullFrameOrientedEquation d) H0.toCoord)
      (sourceFullFrameDetDirection d)
  have ha : a ≠ 0 :=
    sourceFullFrameOrientedEquation_fderiv_detDirection_ne_zero
      (d := d) hH0
  refine ⟨(c / a) • sourceFullFrameDetDirection d, ?_⟩
  calc
    (fderiv ℂ (sourceFullFrameOrientedEquation d) H0.toCoord)
        ((c / a) • sourceFullFrameDetDirection d)
        = (c / a) * a := by
          simp [a]
    _ = c := by
          field_simp [ha]

/-- Nonzero oriented determinant makes the actual Frechet derivative onto `ℂ`
even after restricting to symmetric coordinates. -/
theorem
    sourceFullFrameOrientedEquation_fderiv_surjectiveOnSymmetric_of_det_ne_zero
    (d : ℕ) {H0 : SourceFullFrameOrientedGramData d}
    (hH0 : H0.det ≠ 0) :
    Function.Surjective
      (fun Y : sourceFullFrameSymmetricCoordSubmodule d =>
        (fderiv ℂ (sourceFullFrameOrientedEquation d) H0.toCoord)
          (Y : SourceFullFrameOrientedCoord d)) := by
  intro c
  let a : ℂ :=
    (fderiv ℂ (sourceFullFrameOrientedEquation d) H0.toCoord)
      (sourceFullFrameDetDirection d)
  have ha : a ≠ 0 :=
    sourceFullFrameOrientedEquation_fderiv_detDirection_ne_zero
      (d := d) hH0
  refine ⟨(c / a) • sourceFullFrameSymmetricDetDirection d, ?_⟩
  calc
    (fderiv ℂ (sourceFullFrameOrientedEquation d) H0.toCoord)
        (((c / a) • sourceFullFrameSymmetricDetDirection d :
            sourceFullFrameSymmetricCoordSubmodule d) :
          SourceFullFrameOrientedCoord d)
        = (c / a) * a := by
          simp [a, sourceFullFrameSymmetricDetDirection]
    _ = c := by
          field_simp [ha]

/-- Data saying a scalar equation cuts out a regular zero locus at `x0`. -/
structure RegularZeroLocusAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (x0 : E) where
  deriv : E →L[ℂ] ℂ
  value_zero : f x0 = 0
  has_deriv : HasFDerivAt f deriv x0
  deriv_surj : Function.Surjective deriv

/-- Data saying a scalar equation cuts out a regular zero locus inside a
linear submodule at `x0`. -/
structure RegularZeroLocusInSubmoduleAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S : Submodule ℂ E) (f : E → ℂ) (x0 : E) where
  x0_mem : x0 ∈ S
  deriv : E →L[ℂ] ℂ
  value_zero : f x0 = 0
  has_deriv : HasFDerivAt f deriv x0
  deriv_surj_on : Function.Surjective (fun x : S => deriv (x : E))

/-- The full-frame oriented hypersurface is regular at every invertible
full-frame invariant. -/
noncomputable def sourceFullFrameOrientedHypersurface_regularAt
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det) :
    RegularZeroLocusAt
      (sourceFullFrameOrientedEquation d)
      (sourceFullFrameOrientedGramCoord d M0) where
  deriv :=
    fderiv ℂ (sourceFullFrameOrientedEquation d)
      (sourceFullFrameOrientedGramCoord d M0)
  value_zero :=
    (sourceFullFrameOrientedGramCoord_mem_hypersurface d M0).2
  has_deriv :=
    (differentiable_sourceFullFrameOrientedEquation d).differentiableAt.hasFDerivAt
  deriv_surj := by
    simpa [sourceFullFrameOrientedGramCoord]
      using
        sourceFullFrameOrientedEquation_fderiv_surjective_of_det_ne_zero
          (d := d) (H0 := sourceFullFrameOrientedGram d M0) hM0.ne_zero

/-- The full-frame oriented hypersurface is regular inside symmetric
coordinates at every invertible full-frame invariant. -/
noncomputable def sourceFullFrameOrientedHypersurface_regularInSymmetricAt
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det) :
    RegularZeroLocusInSubmoduleAt
      (sourceFullFrameSymmetricCoordSubmodule d)
      (sourceFullFrameOrientedEquation d)
      (sourceFullFrameOrientedGramCoord d M0) where
  x0_mem :=
    (sourceFullFrameOrientedGramCoord_mem_hypersurface d M0).1
  deriv :=
    fderiv ℂ (sourceFullFrameOrientedEquation d)
      (sourceFullFrameOrientedGramCoord d M0)
  value_zero :=
    (sourceFullFrameOrientedGramCoord_mem_hypersurface d M0).2
  has_deriv :=
    (differentiable_sourceFullFrameOrientedEquation d).differentiableAt.hasFDerivAt
  deriv_surj_on := by
    simpa [sourceFullFrameOrientedGramCoord]
      using
        sourceFullFrameOrientedEquation_fderiv_surjectiveOnSymmetric_of_det_ne_zero
          (d := d) (H0 := sourceFullFrameOrientedGram d M0) hM0.ne_zero

end BHW
