import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedFullFrameDerivative

/-!
# Orbit kernel for the full-frame oriented differential

This file proves the algebraic kernel half of the full-frame local-image
packet: the kernel of the linearized full-frame oriented invariant is exactly
the infinitesimal determinant-one Lorentz orbit tangent.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

/-- Trace identity for the linearized full-frame oriented invariant. -/
theorem sourceFullFrameOrientedDifferential_trace_identity
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    Matrix.trace
        ((Matrix.of (sourceFullFrameGram d M0))⁻¹ *
          Matrix.of (sourceFullFrameOrientedDifferential d M0 X).1) =
      (2 : ℂ) * Matrix.trace (M0⁻¹ * X) := by
  have hMt : IsUnit M0.transpose.det := by
    simpa [Matrix.det_transpose] using hM0
  have hGramInv :
      (Matrix.of (sourceFullFrameGram d M0))⁻¹ =
        (M0.transpose)⁻¹ * ComplexLorentzGroup.ηℂ (d := d) * M0⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [sourceFullFrameGram_eq_mul_eta_transpose]
    calc
      ((M0.transpose)⁻¹ * ComplexLorentzGroup.ηℂ (d := d) * M0⁻¹) *
          (M0 * ComplexLorentzGroup.ηℂ (d := d) * M0.transpose)
          = (M0.transpose)⁻¹ *
              (ComplexLorentzGroup.ηℂ (d := d) *
                (M0⁻¹ * M0) * ComplexLorentzGroup.ηℂ (d := d)) *
              M0.transpose := by
            noncomm_ring
      _ = (M0.transpose)⁻¹ * M0.transpose := by
            rw [Matrix.nonsing_inv_mul M0 hM0]
            simp [ComplexLorentzGroup.ηℂ_sq]
      _ = 1 := by
            exact Matrix.nonsing_inv_mul M0.transpose hMt
  have hdiffMatrix :
      Matrix.of (sourceFullFrameOrientedDifferential d M0 X).1 =
        X * ComplexLorentzGroup.ηℂ (d := d) * M0.transpose +
          M0 * ComplexLorentzGroup.ηℂ (d := d) * X.transpose := by
    ext a b
    rfl
  have hfirst :
      Matrix.trace
        (((M0.transpose)⁻¹ * ComplexLorentzGroup.ηℂ (d := d) * M0⁻¹) *
          (X * ComplexLorentzGroup.ηℂ (d := d) * M0.transpose)) =
        Matrix.trace (M0⁻¹ * X) := by
    have hMtinv : M0.transpose * (M0.transpose)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv M0.transpose hMt
    calc
      Matrix.trace
          (((M0.transpose)⁻¹ * ComplexLorentzGroup.ηℂ (d := d) * M0⁻¹) *
            (X * ComplexLorentzGroup.ηℂ (d := d) * M0.transpose))
        = Matrix.trace
            (((M0.transpose)⁻¹ * ComplexLorentzGroup.ηℂ (d := d)) *
              ((M0⁻¹ * X) *
                (ComplexLorentzGroup.ηℂ (d := d) * M0.transpose))) := by
            congr 1
            noncomm_ring
      _ = Matrix.trace
            (((M0⁻¹ * X) *
                (ComplexLorentzGroup.ηℂ (d := d) * M0.transpose)) *
              ((M0.transpose)⁻¹ * ComplexLorentzGroup.ηℂ (d := d))) := by
            rw [Matrix.trace_mul_comm]
      _ = Matrix.trace (M0⁻¹ * X) := by
            congr 1
            calc
              ((M0⁻¹ * X) *
                  (ComplexLorentzGroup.ηℂ (d := d) * M0.transpose)) *
                  ((M0.transpose)⁻¹ * ComplexLorentzGroup.ηℂ (d := d))
                  = (M0⁻¹ * X) *
                      (ComplexLorentzGroup.ηℂ (d := d) *
                        (M0.transpose * (M0.transpose)⁻¹) *
                        ComplexLorentzGroup.ηℂ (d := d)) := by
                      noncomm_ring
              _ = M0⁻¹ * X := by
                      rw [hMtinv]
                      simp [ComplexLorentzGroup.ηℂ_sq]
  have hsecond :
      Matrix.trace
        (((M0.transpose)⁻¹ * ComplexLorentzGroup.ηℂ (d := d) * M0⁻¹) *
          (M0 * ComplexLorentzGroup.ηℂ (d := d) * X.transpose)) =
        Matrix.trace (M0⁻¹ * X) := by
    have hMinv : M0⁻¹ * M0 = 1 := Matrix.nonsing_inv_mul M0 hM0
    calc
      Matrix.trace
          (((M0.transpose)⁻¹ * ComplexLorentzGroup.ηℂ (d := d) * M0⁻¹) *
            (M0 * ComplexLorentzGroup.ηℂ (d := d) * X.transpose))
        = Matrix.trace ((M0.transpose)⁻¹ * X.transpose) := by
            congr 1
            calc
              ((M0.transpose)⁻¹ * ComplexLorentzGroup.ηℂ (d := d) * M0⁻¹) *
                  (M0 * ComplexLorentzGroup.ηℂ (d := d) * X.transpose)
                  = (M0.transpose)⁻¹ *
                      (ComplexLorentzGroup.ηℂ (d := d) * (M0⁻¹ * M0) *
                        ComplexLorentzGroup.ηℂ (d := d)) * X.transpose := by
                      noncomm_ring
              _ = (M0.transpose)⁻¹ * X.transpose := by
                      rw [hMinv]
                      simp [ComplexLorentzGroup.ηℂ_sq]
      _ = Matrix.trace (X.transpose * (M0.transpose)⁻¹) := by
            rw [Matrix.trace_mul_comm]
      _ = Matrix.trace ((M0⁻¹ * X).transpose) := by
            congr 1
            rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
      _ = Matrix.trace (M0⁻¹ * X) := by
            rw [Matrix.trace_transpose]
  calc
    Matrix.trace
        ((Matrix.of (sourceFullFrameGram d M0))⁻¹ *
          Matrix.of (sourceFullFrameOrientedDifferential d M0 X).1)
        = Matrix.trace
            (((M0.transpose)⁻¹ * ComplexLorentzGroup.ηℂ (d := d) * M0⁻¹) *
              (X * ComplexLorentzGroup.ηℂ (d := d) * M0.transpose +
                M0 * ComplexLorentzGroup.ηℂ (d := d) * X.transpose)) := by
          rw [hGramInv, hdiffMatrix]
    _ = Matrix.trace
          (((M0.transpose)⁻¹ * ComplexLorentzGroup.ηℂ (d := d) * M0⁻¹) *
            (X * ComplexLorentzGroup.ηℂ (d := d) * M0.transpose)) +
        Matrix.trace
          (((M0.transpose)⁻¹ * ComplexLorentzGroup.ηℂ (d := d) * M0⁻¹) *
            (M0 * ComplexLorentzGroup.ηℂ (d := d) * X.transpose)) := by
          rw [Matrix.mul_add, Matrix.trace_add]
    _ = Matrix.trace (M0⁻¹ * X) + Matrix.trace (M0⁻¹ * X) := by
          rw [hfirst, hsecond]
    _ = (2 : ℂ) * Matrix.trace (M0⁻¹ * X) := by
          ring

/-- The kernel of the linearized full-frame oriented invariant is the tangent
space to the determinant-one complex Lorentz orbit. -/
theorem sourceFullFrameOrientedDifferential_kernel_eq_orbitTangent
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det) :
    LinearMap.ker (sourceFullFrameOrientedDifferentialCLM d M0).toLinearMap =
      sourceFullFrameOrbitTangent d M0 := by
  ext X
  constructor
  · intro hX
    have hDiff : sourceFullFrameOrientedDifferential d M0 X = 0 := by
      simpa [sourceFullFrameOrientedDifferentialCLM,
        sourceFullFrameOrientedDifferentialLinear] using hX
    let B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := M0⁻¹ * X
    have hMt : IsUnit M0.transpose.det := by
      simpa [Matrix.det_transpose] using hM0
    have hX_eq : X = M0 * B := by
      dsimp [B]
      simpa [Matrix.mul_assoc] using
        (Matrix.mul_nonsing_inv_cancel_left M0 X hM0).symm
    have hGramMatrix :
        X * ComplexLorentzGroup.ηℂ (d := d) * M0.transpose +
          M0 * ComplexLorentzGroup.ηℂ (d := d) * X.transpose = 0 := by
      ext a b
      have hfst := congrArg Prod.fst hDiff
      simpa [sourceFullFrameOrientedDifferential] using
        congrFun (congrFun hfst a) b
    have hGram :
        B * ComplexLorentzGroup.ηℂ (d := d) +
          ComplexLorentzGroup.ηℂ (d := d) * B.transpose = 0 := by
      have hconj := congrArg
        (fun C : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ =>
          M0⁻¹ * C * (M0.transpose)⁻¹) hGramMatrix
      have hMinv : M0⁻¹ * M0 = 1 := Matrix.nonsing_inv_mul M0 hM0
      have hMtinv : M0.transpose * (M0.transpose)⁻¹ = 1 :=
        Matrix.mul_nonsing_inv M0.transpose hMt
      have hleft :
          M0⁻¹ *
              (X * ComplexLorentzGroup.ηℂ (d := d) * M0.transpose +
                M0 * ComplexLorentzGroup.ηℂ (d := d) * X.transpose) *
            (M0.transpose)⁻¹ =
          B * ComplexLorentzGroup.ηℂ (d := d) +
            ComplexLorentzGroup.ηℂ (d := d) * B.transpose := by
        rw [hX_eq]
        calc
          M0⁻¹ *
              ((M0 * B) * ComplexLorentzGroup.ηℂ (d := d) *
                  M0.transpose +
                M0 * ComplexLorentzGroup.ηℂ (d := d) *
                  (M0 * B).transpose) *
              (M0.transpose)⁻¹
              = (M0⁻¹ * M0) *
                  ((B * ComplexLorentzGroup.ηℂ (d := d) +
                    ComplexLorentzGroup.ηℂ (d := d) * B.transpose) *
                    (M0.transpose * (M0.transpose)⁻¹)) := by
                rw [Matrix.transpose_mul]
                noncomm_ring
          _ = B * ComplexLorentzGroup.ηℂ (d := d) +
                ComplexLorentzGroup.ηℂ (d := d) * B.transpose := by
                rw [hMinv, hMtinv]
                simp
      simpa [hleft] using hconj
    have hTrace : Matrix.trace B = 0 := by
      have hdet : (sourceFullFrameOrientedDifferential d M0 X).2 = 0 := by
        simpa using congrArg Prod.snd hDiff
      have htraceArg : M0⁻¹ * (M0 * B) = B := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul M0 hM0,
          Matrix.one_mul]
      have hprod : M0.det * Matrix.trace B = 0 := by
        simpa [sourceFullFrameOrientedDifferential, hX_eq, htraceArg]
          using hdet
      exact mul_eq_zero.mp hprod |>.resolve_left hM0.ne_zero
    let A : specialComplexLorentzLieAlgebra d :=
      ⟨B.transpose, by
        constructor
        · simpa [B] using hGram
        · simpa [Matrix.trace_transpose] using hTrace⟩
    refine ⟨A, ?_⟩
    simp [infinitesimalRightSpecialLorentzAction, A, hX_eq]
  · rintro ⟨A, rfl⟩
    change
      sourceFullFrameOrientedDifferential d M0
        (M0 * (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).transpose) = 0
    have htraceArg :
        M0⁻¹ *
            (M0 * (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).transpose) =
          (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).transpose := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul M0 hM0,
        Matrix.one_mul]
    have hGramMatrix :
        (M0 * (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).transpose) *
            ComplexLorentzGroup.ηℂ (d := d) * M0.transpose +
          M0 * ComplexLorentzGroup.ηℂ (d := d) *
            (M0 *
              (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).transpose).transpose =
          0 := by
      calc
        (M0 * (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).transpose) *
            ComplexLorentzGroup.ηℂ (d := d) * M0.transpose +
          M0 * ComplexLorentzGroup.ηℂ (d := d) *
            (M0 *
              (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).transpose).transpose
            = M0 *
                (((A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).transpose *
                    ComplexLorentzGroup.ηℂ (d := d) +
                  ComplexLorentzGroup.ηℂ (d := d) *
                    (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)) *
                  M0.transpose) := by
              rw [Matrix.transpose_mul]
              noncomm_ring
        _ = 0 := by
              rw [A.property.1]
              simp
    apply Prod.ext
    · ext a b
      simpa [sourceFullFrameOrientedDifferential] using
        congrArg
          (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ => M a b)
          hGramMatrix
    · have hdet :
          M0.det *
              Matrix.trace
                ((A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ).transpose) =
            0 := by
        simp [Matrix.trace_transpose, A.property.2]
      simpa [sourceFullFrameOrientedDifferential, htraceArg] using hdet

/-- The range of the linearized full-frame oriented invariant lies in the
linearized tangent space to the oriented hypersurface. -/
theorem sourceFullFrameOrientedDifferential_range_subset_tangent
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det) :
  LinearMap.range (sourceFullFrameOrientedDifferentialCLM d M0).toLinearMap ≤
      sourceFullFrameOrientedTangentSpace d (sourceFullFrameOrientedGram d M0) := by
  rintro Y ⟨X, rfl⟩
  change sourceFullFrameOrientedDifferential d M0 X ∈
    sourceFullFrameOrientedTangentSpace d (sourceFullFrameOrientedGram d M0)
  rw [mem_sourceFullFrameOrientedTangentSpace_iff_symmetric_and_deriv_eq_zero]
  constructor
  · intro a b
    let A :=
      X * ComplexLorentzGroup.ηℂ (d := d) * M0.transpose +
        M0 * ComplexLorentzGroup.ηℂ (d := d) * X.transpose
    have hA : A.transpose = A := by
      dsimp [A]
      rw [Matrix.transpose_add]
      simp [Matrix.transpose_mul, ComplexLorentzGroup.ηℂ_transpose,
        Matrix.mul_assoc, add_comm]
    change A a b = A b a
    calc
      A a b = A.transpose b a := rfl
      _ = A b a := by rw [hA]
  · have htrace :=
      sourceFullFrameOrientedDifferential_trace_identity (d := d) hM0 X
    have htrace' :
        ((Matrix.of (sourceFullFrameGram d M0))⁻¹ *
            Matrix.of
              (fun a b : Fin (d + 1) =>
                (X * (ComplexLorentzGroup.ηℂ (d := d) * M0.transpose)) a b +
                  (M0 * (ComplexLorentzGroup.ηℂ (d := d) * X.transpose)) a b)).trace =
          (2 : ℂ) * (M0⁻¹ * X).trace := by
      simpa [sourceFullFrameOrientedDifferential, Matrix.mul_assoc] using htrace
    have hdet := sourceFullFrameGram_det_eq d M0
    change
      sourceFullFrameOrientedEquationDerivLinear d
        (sourceFullFrameOrientedGram d M0)
        (sourceFullFrameOrientedDifferential d M0 X) = 0
    simp [sourceFullFrameOrientedEquationDerivLinear,
      sourceFullFrameOrientedDifferential, sourceFullFrameOrientedGram,
      hdet, pow_two, mul_comm, mul_left_comm, mul_assoc]
    rw [htrace']
    ring

/-- Gram component of the explicit preimage used for full-frame tangent
surjectivity. -/
theorem sourceFullFrameOrientedDifferential_constructedGram
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    {Y : SourceFullFrameOrientedCoord d}
    (hYsym : ∀ a b : Fin (d + 1), Y.1 a b = Y.1 b a) :
    let G : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := Matrix.of Y.1
    let B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
      (2 : ℂ)⁻¹ • (M0⁻¹ * G * (M0.transpose)⁻¹ *
        ComplexLorentzGroup.ηℂ (d := d))
    Matrix.of (sourceFullFrameOrientedDifferential d M0 (M0 * B)).1 = G := by
  intro G B
  have hMt : IsUnit M0.transpose.det := by
    simpa [Matrix.det_transpose] using hM0
  have hGsym : G.transpose = G := by
    ext a b
    exact hYsym b a
  let P : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    M0 * (M0⁻¹ * G * (M0.transpose)⁻¹) * M0.transpose
  have hterm1 :
      (M0 * B) * ComplexLorentzGroup.ηℂ (d := d) * M0.transpose =
        (2 : ℂ)⁻¹ • P := by
    dsimp [B, P]
    have hraw :
        M0 * (M0⁻¹ * G * (M0.transpose)⁻¹ *
            ComplexLorentzGroup.ηℂ (d := d)) *
          ComplexLorentzGroup.ηℂ (d := d) * M0.transpose =
        M0 * (M0⁻¹ * G * (M0.transpose)⁻¹) * M0.transpose := by
      calc
        M0 * (M0⁻¹ * G * (M0.transpose)⁻¹ *
            ComplexLorentzGroup.ηℂ (d := d)) *
          ComplexLorentzGroup.ηℂ (d := d) * M0.transpose
            = M0 * (M0⁻¹ * G * (M0.transpose)⁻¹) *
                (ComplexLorentzGroup.ηℂ (d := d) *
                  ComplexLorentzGroup.ηℂ (d := d)) * M0.transpose := by
                noncomm_ring
        _ = M0 * (M0⁻¹ * G * (M0.transpose)⁻¹) * M0.transpose := by
                simp [ComplexLorentzGroup.ηℂ_sq]
    calc
      (M0 * ((2 : ℂ)⁻¹ • (M0⁻¹ * G * (M0.transpose)⁻¹ *
          ComplexLorentzGroup.ηℂ (d := d)))) *
          ComplexLorentzGroup.ηℂ (d := d) * M0.transpose
        = (2 : ℂ)⁻¹ •
            (M0 * (M0⁻¹ * G * (M0.transpose)⁻¹ *
              ComplexLorentzGroup.ηℂ (d := d)) *
                ComplexLorentzGroup.ηℂ (d := d) * M0.transpose) := by
            ext a b
            simp [smul_eq_mul]
      _ = (2 : ℂ)⁻¹ •
          (M0 * (M0⁻¹ * G * (M0.transpose)⁻¹) * M0.transpose) := by
            rw [hraw]
  have hterm2 :
      M0 * ComplexLorentzGroup.ηℂ (d := d) * (M0 * B).transpose =
        (2 : ℂ)⁻¹ • P := by
    dsimp [B, P]
    have hassoc :
        M0 * ComplexLorentzGroup.ηℂ (d := d) *
            (ComplexLorentzGroup.ηℂ (d := d) *
              (M0⁻¹ * (G * (M0.transpose)⁻¹)) * M0.transpose) =
          M0 * ComplexLorentzGroup.ηℂ (d := d) *
            (ComplexLorentzGroup.ηℂ (d := d) * M0⁻¹ * G *
              (M0.transpose)⁻¹) * M0.transpose := by
      noncomm_ring
    have hraw :
        M0 * ComplexLorentzGroup.ηℂ (d := d) *
            (ComplexLorentzGroup.ηℂ (d := d) * M0⁻¹ * G *
              (M0.transpose)⁻¹) * M0.transpose =
        M0 * (M0⁻¹ * G * (M0.transpose)⁻¹) * M0.transpose := by
      calc
        M0 * ComplexLorentzGroup.ηℂ (d := d) *
            (ComplexLorentzGroup.ηℂ (d := d) * M0⁻¹ * G *
              (M0.transpose)⁻¹) * M0.transpose
            = M0 * (ComplexLorentzGroup.ηℂ (d := d) *
                ComplexLorentzGroup.ηℂ (d := d)) *
                M0⁻¹ * G * (M0.transpose)⁻¹ * M0.transpose := by
                noncomm_ring
        _ = M0 * M0⁻¹ * G * (M0.transpose)⁻¹ * M0.transpose := by
                simp [ComplexLorentzGroup.ηℂ_sq]
        _ = M0 * (M0⁻¹ * G * (M0.transpose)⁻¹) * M0.transpose := by
                noncomm_ring
    calc
      M0 * ComplexLorentzGroup.ηℂ (d := d) *
          (M0 * ((2 : ℂ)⁻¹ • (M0⁻¹ * G * (M0.transpose)⁻¹ *
            ComplexLorentzGroup.ηℂ (d := d)))).transpose
        = (2 : ℂ)⁻¹ •
            (M0 * ComplexLorentzGroup.ηℂ (d := d) *
              (ComplexLorentzGroup.ηℂ (d := d) * M0⁻¹ * G *
                (M0.transpose)⁻¹) * M0.transpose) := by
            ext a b
            simp [Matrix.transpose_mul, Matrix.transpose_smul,
              ComplexLorentzGroup.ηℂ_transpose, hGsym,
              Matrix.transpose_nonsing_inv, smul_eq_mul, hassoc]
      _ = (2 : ℂ)⁻¹ •
          (M0 * (M0⁻¹ * G * (M0.transpose)⁻¹) * M0.transpose) := by
            rw [hraw]
  have hP : P = G := by
    dsimp [P]
    calc
      M0 * (M0⁻¹ * G * (M0.transpose)⁻¹) * M0.transpose
          = (M0 * M0⁻¹) * G * ((M0.transpose)⁻¹ * M0.transpose) := by
              noncomm_ring
      _ = G := by
              rw [Matrix.mul_nonsing_inv M0 hM0,
                Matrix.nonsing_inv_mul M0.transpose hMt]
              simp
  have hmat :
      (M0 * B) * ComplexLorentzGroup.ηℂ (d := d) * M0.transpose +
          M0 * ComplexLorentzGroup.ηℂ (d := d) * (M0 * B).transpose = G := by
    calc
      (M0 * B) * ComplexLorentzGroup.ηℂ (d := d) * M0.transpose +
          M0 * ComplexLorentzGroup.ηℂ (d := d) * (M0 * B).transpose
          = (2 : ℂ)⁻¹ • P + (2 : ℂ)⁻¹ • P := by
              rw [hterm1, hterm2]
      _ = P := by
              rw [← add_smul]
              norm_num
      _ = G := hP
  ext a b
  change ((M0 * B) * ComplexLorentzGroup.ηℂ (d := d) * M0.transpose +
    M0 * ComplexLorentzGroup.ηℂ (d := d) * (M0 * B).transpose) a b = G a b
  rw [hmat]

/-- Determinant component of the explicit preimage used for full-frame tangent
surjectivity. -/
theorem sourceFullFrameOrientedDifferential_constructedDet
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    {Y : SourceFullFrameOrientedCoord d}
    (hY : Y ∈ sourceFullFrameOrientedTangentSpace d
      (sourceFullFrameOrientedGram d M0)) :
    let G : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := Matrix.of Y.1
    let B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
      (2 : ℂ)⁻¹ • (M0⁻¹ * G * (M0.transpose)⁻¹ *
        ComplexLorentzGroup.ηℂ (d := d))
    Matrix.of (sourceFullFrameOrientedDifferential d M0 (M0 * B)).1 = G →
    (sourceFullFrameOrientedDifferential d M0 (M0 * B)).2 = Y.2 := by
  intro G B hgram
  have htraceArg : M0⁻¹ * (M0 * B) = B := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul M0 hM0,
      Matrix.one_mul]
  have htraceID :=
    sourceFullFrameOrientedDifferential_trace_identity (d := d) hM0 (M0 * B)
  have htrace :
      Matrix.trace ((Matrix.of (sourceFullFrameGram d M0))⁻¹ * G) =
        (2 : ℂ) * Matrix.trace B := by
    simpa [hgram, htraceArg] using htraceID
  have hYlin :
      (Matrix.of (sourceFullFrameGram d M0)).det *
          Matrix.trace ((Matrix.of (sourceFullFrameGram d M0))⁻¹ * G) =
        (2 : ℂ) * minkowskiMetricDet d * M0.det * Y.2 := by
    simpa [sourceFullFrameOrientedGram, G] using hY.2
  have hdetGram := sourceFullFrameGram_det_eq d M0
  have hscalar : M0.det * Matrix.trace B = Y.2 := by
    have hlinB :
        (minkowskiMetricDet d * M0.det ^ 2) *
            ((2 : ℂ) * Matrix.trace B) =
          (2 : ℂ) * minkowskiMetricDet d * M0.det * Y.2 := by
      simpa [hdetGram, htrace] using hYlin
    field_simp [hM0.ne_zero, (by norm_num : (2 : ℂ) ≠ 0),
      minkowskiMetricDet_ne_zero d] at hlinB ⊢
    ring_nf at hlinB ⊢
    exact hlinB
  simpa [sourceFullFrameOrientedDifferential, htraceArg] using hscalar

/-- The linearized full-frame oriented invariant maps onto the tangent space of
the oriented hypersurface at an invertible full frame. -/
theorem sourceFullFrameOrientedDifferential_range_eq_tangent
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det) :
  LinearMap.range (sourceFullFrameOrientedDifferentialCLM d M0).toLinearMap =
      sourceFullFrameOrientedTangentSpace d (sourceFullFrameOrientedGram d M0) := by
  apply le_antisymm
  · exact sourceFullFrameOrientedDifferential_range_subset_tangent (d := d) hM0
  · intro Y hY
    let G : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := Matrix.of Y.1
    let B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
      (2 : ℂ)⁻¹ • (M0⁻¹ * G * (M0.transpose)⁻¹ *
        ComplexLorentzGroup.ηℂ (d := d))
    refine ⟨M0 * B, ?_⟩
    change sourceFullFrameOrientedDifferential d M0 (M0 * B) = Y
    have hgram :
        Matrix.of (sourceFullFrameOrientedDifferential d M0 (M0 * B)).1 = G :=
      sourceFullFrameOrientedDifferential_constructedGram
        (d := d) hM0 (Y := Y) hY.1
    have hdet :
        (sourceFullFrameOrientedDifferential d M0 (M0 * B)).2 = Y.2 :=
      sourceFullFrameOrientedDifferential_constructedDet
        (d := d) hM0 (Y := Y) hY hgram
    apply Prod.ext
    · ext a b
      exact congrArg (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ => M a b)
        hgram
    · exact hdet

/-- Choose a full-frame gauge slice complementary to the determinant-one
complex Lorentz orbit tangent. -/
noncomputable def sourceFullFrameGaugeSlice_exists
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det) :
    SourceFullFrameGaugeSliceData d M0 := by
  let L : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ →ₗ[ℂ]
      SourceFullFrameOrientedCoord d :=
    (sourceFullFrameOrientedDifferentialCLM d M0).toLinearMap
  let K := sourceFullFrameOrbitTangent d M0
  have hker : LinearMap.ker L = K := by
    dsimp [L, K]
    exact sourceFullFrameOrientedDifferential_kernel_eq_orbitTangent (d := d) hM0
  have hrange : LinearMap.range L =
      sourceFullFrameOrientedTangentSpace d (sourceFullFrameOrientedGram d M0) := by
    dsimp [L]
    exact sourceFullFrameOrientedDifferential_range_eq_tangent (d := d) hM0
  let S : Submodule ℂ (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :=
    Classical.choose (Submodule.exists_isCompl K)
  have hS : IsCompl S K :=
    (Classical.choose_spec (Submodule.exists_isCompl K)).symm
  let T := sourceFullFrameOrientedTangentSpace d (sourceFullFrameOrientedGram d M0)
  let LS : S →ₗ[ℂ] T :=
    { toFun := fun X =>
        ⟨L (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ), by
          show L (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) ∈
            sourceFullFrameOrientedTangentSpace d (sourceFullFrameOrientedGram d M0)
          rw [← hrange]
          exact ⟨(X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ), rfl⟩⟩
      map_add' := by
        intro X Y
        apply Subtype.ext
        simp [L]
      map_smul' := by
        intro c X
        apply Subtype.ext
        simp [L] }
  have hLS_inj : Function.Injective LS := by
    intro X Y hXY
    apply Subtype.ext
    have hval := congrArg Subtype.val hXY
    have hdiffK :
        (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) -
            (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) ∈ K := by
      rw [← hker, LinearMap.mem_ker]
      simpa [LS, map_sub] using sub_eq_zero.mpr hval
    have hdiffS :
        (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) -
            (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) ∈ S :=
      S.sub_mem X.property Y.property
    have hzero :
        (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) -
            (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) = 0 :=
      submodule_mem_isCompl_inter_eq_zero hS hdiffS hdiffK
    exact sub_eq_zero.mp hzero
  have hLS_surj : Function.Surjective LS := by
    intro Y
    have hYrange :
        (Y : SourceFullFrameOrientedCoord d) ∈ LinearMap.range L := by
      rw [hrange]
      exact Y.property
    rcases hYrange with ⟨X, hX⟩
    rcases submodule_decompose_of_isCompl hS X with ⟨Xs, Xk, hdecomp⟩
    refine ⟨Xs, Subtype.ext ?_⟩
    have hXk_ker :
        (Xk : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) ∈ LinearMap.ker L := by
      rw [hker]
      exact Xk.property
    calc
      L (Xs : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
          = L X := by
            have h := congrArg L hdecomp
            simpa [map_add, LinearMap.mem_ker.mp hXk_ker] using h
      _ = Y := hX
  let e : S ≃ₗ[ℂ] T := LinearEquiv.ofBijective LS ⟨hLS_inj, hLS_surj⟩
  refine
    { slice := S
      isCompl := hS
      differential_iso := e
      differential_iso_eq := ?_ }
  intro X
  rfl

/-- The linear equivalence carried by a full-frame gauge slice. -/
noncomputable def sourceFullFrameSlice_differential_linearEquiv
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (S : SourceFullFrameGaugeSliceData d M0) :
    S.slice ≃ₗ[ℂ]
      sourceFullFrameOrientedTangentSpace d (sourceFullFrameOrientedGram d M0) :=
  S.differential_iso

/-- The full-frame oriented differential restricted to a gauge slice has range
equal to the oriented tangent space. -/
theorem sourceFullFrameSlice_restricted_range_eq_tangent
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (S : SourceFullFrameGaugeSliceData d M0) :
    LinearMap.range
        ((sourceFullFrameOrientedDifferentialCLM d M0).toLinearMap.comp
          S.slice.subtype) =
      sourceFullFrameOrientedTangentSpace d (sourceFullFrameOrientedGram d M0) := by
  ext Y
  constructor
  · rintro ⟨X, rfl⟩
    show sourceFullFrameOrientedDifferential d M0
        (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) ∈
      sourceFullFrameOrientedTangentSpace d (sourceFullFrameOrientedGram d M0)
    rw [← S.differential_iso_eq X]
    exact (S.differential_iso X).property
  · intro hY
    let YT : sourceFullFrameOrientedTangentSpace d (sourceFullFrameOrientedGram d M0) :=
      ⟨Y, hY⟩
    refine ⟨S.differential_iso.symm YT, ?_⟩
    have h := S.differential_iso_eq (S.differential_iso.symm YT)
    change sourceFullFrameOrientedDifferential d M0
        ((S.differential_iso.symm YT : S.slice) :
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) = Y
    rw [← h]
    exact congrArg Subtype.val
      (LinearEquiv.apply_symm_apply S.differential_iso YT)

/-- The full-frame gauge-slice map is holomorphic as a finite-dimensional
polynomial map. -/
theorem contDiff_sourceFullFrameGaugeSliceMap
    (d : ℕ)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0) :
    ContDiff ℂ ⊤ (sourceFullFrameGaugeSliceMap d M0 S) := by
  unfold sourceFullFrameGaugeSliceMap
  have htranslate :
      ContDiff ℂ ⊤
        (fun X : S.slice =>
          M0 + (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)) := by
    exact contDiff_const.add S.slice.subtypeL.contDiff
  exact (contDiff_sourceFullFrameOrientedGramCoord d).comp htranslate

end BHW
