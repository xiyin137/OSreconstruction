import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedStandardSOInvariantSubalgebra
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedInvariantCoordinateStandardEval
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# One containment in the standard `SO` relation-kernel theorem

This file proves the formal direction of the standard-dot SFT kernel statement:
the explicitly displayed symmetry, rank-minor, alternation, and Cauchy-Binet
relations lie in the kernel of the actual invariant-coordinate map.

The reverse containment is the genuine second fundamental theorem and is not
proved here.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Evaluating the tuple-coordinate polynomial underlying the actual
standard-dot invariant-coordinate map is the same as evaluating the
presentation coordinates directly at the tuple. -/
theorem standardSOInvariantCoordinateMap_aeval
    (D n : ℕ)
    (z : Fin n → Fin D → ℂ)
    (p : standardSOInvariantCoordinateRing D n) :
    MvPolynomial.aeval (fun im : Fin n × Fin D => z im.1 im.2)
        ((standardSOInvariantCoordinateMap D n p : standardSOInvariantSubalgebra D n) :
          standardTupleCoordinateRing D n) =
      standardSOCoordinateEval D n z p := by
  have hhom :
      ((MvPolynomial.aeval (fun im : Fin n × Fin D => z im.1 im.2)).comp
          (Subalgebra.val (standardSOInvariantSubalgebra D n))).comp
          (standardSOInvariantCoordinateMap D n) =
        standardSOCoordinateEval D n z := by
    ext x
    cases x with
    | inl ij =>
        simp [standardSOCoordinateEval, standardPairingInvariantElement,
          standardPairingCoordinatePolynomial, sourceComplexDotGram]
    | inr ι =>
        simp [standardSOCoordinateEval, standardVolumeInvariantElement,
          standardVolumeCoordinatePolynomial]
        rw [RingHom.map_det]
        congr
        ext a μ
        simp
  exact AlgHom.congr_fun hhom p

/-- Every explicit standard-dot relation lies in the kernel of the actual
invariant-coordinate map.  The reverse inclusion is the genuine SFT theorem. -/
theorem standardSOAlgebraicRelationIdeal_le_invariantCoordinateMap_ker
    (D n : ℕ) :
    standardSOAlgebraicRelationIdeal D n ≤
      RingHom.ker (standardSOInvariantCoordinateMap D n) := by
  intro p hp
  change standardSOInvariantCoordinateMap D n p = 0
  apply Subtype.ext
  change ((standardSOInvariantCoordinateMap D n p : standardSOInvariantSubalgebra D n) :
      standardTupleCoordinateRing D n) = 0
  apply MvPolynomial.funext
  intro x
  let z : Fin n → Fin D → ℂ := fun i μ => x (i, μ)
  have hEval := standardSOInvariantCoordinateMap_aeval D n z p
  have hRel := standardSOAlgebraicRelationIdeal_eval_eq_zero z hp
  simpa [z] using hEval.trans hRel

end BHW
