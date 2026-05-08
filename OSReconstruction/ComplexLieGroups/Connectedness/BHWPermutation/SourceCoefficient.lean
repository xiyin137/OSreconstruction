import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexTangent

/-!
# Source coefficient maps for the Hall-Wightman Gram packet

This file records the finite-dimensional coefficient algebra used in the
Hall-Wightman same-source-Gram branch analysis.  The constructions are purely
linear algebraic: a coefficient vector evaluates to a source spacetime vector,
and the scalar Gram matrix records all pairings of that vector with the source
tuple.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial
open scoped Matrix.Norms.Operator

namespace BHW

/-- Evaluate a coefficient vector against a complex source tuple. -/
def sourceCoefficientEval
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin (d + 1) → ℂ) where
  toFun := fun a => ∑ i : Fin n, a i • z i
  map_add' := by
    intro a b
    ext μ
    simp [Pi.add_apply, Finset.sum_add_distrib, add_mul]
  map_smul' := by
    intro c a
    ext μ
    simp [Pi.smul_apply, Finset.mul_sum, mul_assoc]

/-- Left multiplication by a scalar source Gram matrix on coefficient
vectors. -/
def sourceCoefficientGramMap
    (n : ℕ)
    (G : Fin n → Fin n → ℂ) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun := fun a j => ∑ i : Fin n, a i * G i j
  map_add' := by
    intro a b
    ext j
    simp [Pi.add_apply, Finset.sum_add_distrib, add_mul]
  map_smul' := by
    intro c a
    ext j
    simp [Pi.smul_apply, Finset.mul_sum, mul_assoc]

/-- The scalar Gram kernel of a source Gram matrix. -/
def sourceCoefficientGramKernel
    (n : ℕ)
    (G : Fin n → Fin n → ℂ) :
    Submodule ℂ (Fin n → ℂ) :=
  LinearMap.ker (sourceCoefficientGramMap n G)

/-- The Gram map records pairings of a coefficient-evaluated vector with each
source vector. -/
theorem sourceCoefficientGramMap_apply_sourceMinkowskiGram
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (a : Fin n → ℂ)
    (j : Fin n) :
    sourceCoefficientGramMap n (sourceMinkowskiGram d n z) a j =
      sourceComplexMinkowskiInner d (sourceCoefficientEval d n z a) (z j) := by
  simpa [sourceCoefficientGramMap, sourceCoefficientEval,
    sourceMinkowskiGram_apply_eq_complexInner] using
    (sourceComplexMinkowskiInner_sum_smul_left d n a z (z j)).symm

/-- A single coefficient vector evaluates to the corresponding source row. -/
theorem sourceCoefficientEval_single
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (i : Fin n) :
    sourceCoefficientEval d n z ((Pi.single i 1 : Fin n → ℂ)) = z i := by
  ext μ
  simp only [sourceCoefficientEval, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- Vanishing of the scalar Gram map is the same as orthogonality against all
coefficient-evaluated source vectors. -/
theorem sourceCoefficientGramMap_eq_zero_iff_eval_pair_eval_eq_zero
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (a : Fin n → ℂ) :
    sourceCoefficientGramMap n (sourceMinkowskiGram d n z) a = 0 ↔
      ∀ b : Fin n → ℂ,
        sourceComplexMinkowskiInner d
          (sourceCoefficientEval d n z a)
          (sourceCoefficientEval d n z b) = 0 := by
  constructor
  · intro h b
    calc
      sourceComplexMinkowskiInner d
          (sourceCoefficientEval d n z a)
          (sourceCoefficientEval d n z b)
          = ∑ j : Fin n, b j *
              sourceComplexMinkowskiInner d
                (sourceCoefficientEval d n z a) (z j) := by
            simpa [sourceCoefficientEval] using
              sourceComplexMinkowskiInner_sum_smul_right d n
                (sourceCoefficientEval d n z a) b z
      _ = 0 := by
            apply Finset.sum_eq_zero
            intro j _
            have hj :
                sourceComplexMinkowskiInner d
                  (sourceCoefficientEval d n z a) (z j) = 0 := by
              simpa [sourceCoefficientGramMap_apply_sourceMinkowskiGram]
                using congrFun h j
            simp [hj]
  · intro h
    ext j
    rw [sourceCoefficientGramMap_apply_sourceMinkowskiGram]
    simpa [sourceCoefficientEval_single] using h (Pi.single j 1)

/-- Pairing two coefficient-evaluated source vectors depends only on the
source Gram matrix. -/
theorem sourceCoefficientEval_pair_eq_sum_gram
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (a b : Fin n → ℂ) :
    sourceComplexMinkowskiInner d
        (sourceCoefficientEval d n z a)
        (sourceCoefficientEval d n z b) =
      ∑ j : Fin n, b j *
        sourceCoefficientGramMap n (sourceMinkowskiGram d n z) a j := by
  calc
    sourceComplexMinkowskiInner d
        (sourceCoefficientEval d n z a)
        (sourceCoefficientEval d n z b)
        = ∑ j : Fin n, b j *
            sourceComplexMinkowskiInner d
              (sourceCoefficientEval d n z a) (z j) := by
          simpa [sourceCoefficientEval] using
            sourceComplexMinkowskiInner_sum_smul_right d n
              (sourceCoefficientEval d n z a) b z
    _ = ∑ j : Fin n, b j *
          sourceCoefficientGramMap n (sourceMinkowskiGram d n z) a j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [sourceCoefficientGramMap_apply_sourceMinkowskiGram]

/-- The coefficient Gram map is the linear map of the transposed Gram
matrix. -/
theorem sourceCoefficientGramMap_eq_toLin_transpose
    (n : ℕ)
    (G : Fin n → Fin n → ℂ) :
    sourceCoefficientGramMap n G =
      Matrix.toLin' Gᵀ := by
  ext a j
  simp [sourceCoefficientGramMap, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct, Matrix.transpose, mul_comm]

/-- The kernel of coefficient evaluation is contained in the scalar Gram
kernel of the source Gram matrix. -/
theorem sourceCoefficientEval_ker_le_gramKernel
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    LinearMap.ker (sourceCoefficientEval d n z) ≤
      sourceCoefficientGramKernel n (sourceMinkowskiGram d n z) := by
  intro a ha
  change sourceCoefficientGramMap n (sourceMinkowskiGram d n z) a = 0
  ext j
  rw [sourceCoefficientGramMap_apply_sourceMinkowskiGram]
  rw [show sourceCoefficientEval d n z a = 0 from ha]
  simp [sourceComplexMinkowskiInner]

end BHW
