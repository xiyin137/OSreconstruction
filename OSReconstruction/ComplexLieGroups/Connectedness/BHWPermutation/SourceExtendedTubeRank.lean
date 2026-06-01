import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOriented
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceRank

/-!
# Rank support for extended-tube source Gram matrices

This file contains the small cone/rank facts used by the Hall-Wightman
Lemma-3 adapted-representative route.  The key point is that an ordinary
forward-tube source tuple has a nonzero diagonal scalar product, hence
positive scalar Gram rank; the extended-tube case then follows from complex
Lorentz invariance of the source Gram matrix.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial
open scoped Matrix.Norms.Operator

namespace BHW

/-- A finite matrix with rank zero is the zero matrix. -/
theorem matrix_eq_zero_of_rank_eq_zero_source
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (hA : A.rank = 0) :
    A = 0 := by
  have hfin : Module.finrank ℂ (LinearMap.range A.mulVecLin) = 0 := by
    simpa [Matrix.rank] using hA
  have hrange : LinearMap.range A.mulVecLin = ⊥ := by
    rw [← Submodule.finrank_eq_zero]
    exact hfin
  have hmul : A.mulVecLin = 0 := by
    apply LinearMap.ext
    intro v
    ext i
    have hv : A.mulVecLin v ∈ LinearMap.range A.mulVecLin :=
      LinearMap.mem_range_self A.mulVecLin v
    rw [hrange] at hv
    have hz : A.mulVecLin v = 0 := by
      simpa using hv
    exact congr_fun hz i
  ext i j
  have hz : A.mulVecLin (Pi.single j (1 : ℂ)) i = 0 := by
    have hfun := congr_fun (LinearMap.congr_fun hmul (Pi.single j (1 : ℂ))) i
    simpa using hfun
  simpa [Matrix.mulVecLin, Matrix.mulVec, dotProduct, Pi.single_apply,
    Finset.sum_eq_single j] using hz

/-- A nonzero entry forces positive matrix rank. -/
theorem matrix_rank_pos_of_nonzero_entry
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) {i : m} {j : n}
    (hij : A i j ≠ 0) :
    0 < A.rank := by
  by_contra hnot
  have hA0 : A.rank = 0 := Nat.eq_zero_of_not_pos hnot
  have hzero := matrix_eq_zero_of_rank_eq_zero_source A hA0
  have hentry : A i j = 0 := by
    rw [hzero]
    rfl
  exact hij hentry

/-- Real and imaginary parts of the complex bilinear self-pairing. -/
theorem sourceComplexMinkowskiInner_self_re_im
    (d : ℕ) (v : Fin (d + 1) → ℂ) :
    (sourceComplexMinkowskiInner d v v).re =
        MinkowskiSpace.minkowskiInner d
          (fun μ => (v μ).re) (fun μ => (v μ).re) -
        MinkowskiSpace.minkowskiInner d
          (fun μ => (v μ).im) (fun μ => (v μ).im) ∧
      (sourceComplexMinkowskiInner d v v).im =
        2 * MinkowskiSpace.minkowskiInner d
          (fun μ => (v μ).re) (fun μ => (v μ).im) := by
  constructor
  · rw [sourceComplexMinkowskiInner, Complex.re_sum]
    simp [MinkowskiSpace.minkowskiInner, Complex.mul_re, Complex.mul_im]
  · rw [sourceComplexMinkowskiInner, Complex.im_sum]
    simp [MinkowskiSpace.minkowskiInner, Complex.mul_re, Complex.mul_im]
    calc
      ∑ x,
          (MinkowskiSpace.metricSignature d x * (v x).re * (v x).im +
            MinkowskiSpace.metricSignature d x * (v x).im * (v x).re)
          = ∑ x,
              2 * (MinkowskiSpace.metricSignature d x *
                (v x).re * (v x).im) := by
            apply Finset.sum_congr rfl
            intro x _
            ring
      _ = 2 * ∑ x,
              MinkowskiSpace.metricSignature d x * (v x).re * (v x).im := by
            rw [Finset.mul_sum]

/-- A complex vector whose imaginary part lies in the open forward cone has
nonzero complex Minkowski self-pairing. -/
theorem openForwardCone_imag_complexSelfInner_ne_zero
    [NeZero d] (_hd : 2 ≤ d)
    {v : Fin (d + 1) → ℂ}
    (hv_im : InOpenForwardCone d (fun μ => (v μ).im)) :
    sourceComplexMinkowskiInner d v v ≠ 0 := by
  intro hzero
  let x : MinkowskiSpace d := fun μ => (v μ).re
  let η : MinkowskiSpace d := fun μ => (v μ).im
  have hparts := sourceComplexMinkowskiInner_self_re_im d v
  have hre0 : (sourceComplexMinkowskiInner d v v).re = 0 := by
    simp [hzero]
  have him0 : (sourceComplexMinkowskiInner d v v).im = 0 := by
    simp [hzero]
  have horth : MinkowskiSpace.minkowskiInner d x η = 0 := by
    have h2 : 2 * MinkowskiSpace.minkowskiInner d x η = 0 := by
      rw [← hparts.2]
      exact him0
    nlinarith
  have hxx_eq :
      MinkowskiSpace.minkowskiInner d x x =
        MinkowskiSpace.minkowskiInner d η η := by
    have hdiff :
        MinkowskiSpace.minkowskiInner d x x -
          MinkowskiSpace.minkowskiInner d η η = 0 := by
      rw [← hparts.1]
      exact hre0
    linarith
  have hη_timelike : MinkowskiSpace.IsTimelike d η := by
    simpa [η, MinkowskiSpace.IsTimelike, MinkowskiSpace.minkowskiNormSq,
      MinkowskiSpace.minkowskiInner, InOpenForwardCone,
      MinkowskiSpace.metricSignature, LorentzLieGroup.minkowskiSignature, sq]
      using hv_im.2
  have hη_future : MinkowskiSpace.IsFutureDirected d η := by
    simpa [η, MinkowskiSpace.IsFutureDirected, MinkowskiSpace.timeComponent]
      using hv_im.1
  have hxx_nonneg :
      0 ≤ MinkowskiSpace.minkowskiInner d x x := by
    have h :=
      MinkowskiSpace.minkowskiInner_orthogonal_to_timelike_nonneg
        (d := d) x η hη_timelike hη_future horth
    simpa [MinkowskiSpace.minkowskiNormSq] using h
  have hη_inner_neg : MinkowskiSpace.minkowskiInner d η η < 0 := by
    simpa [MinkowskiSpace.IsTimelike, MinkowskiSpace.minkowskiNormSq]
      using hη_timelike
  linarith

/-- A forward-tube source tuple has positive scalar Gram rank. -/
theorem sourceGramMatrixRank_pos_of_forwardTube
    [NeZero d] (hd : 2 ≤ d)
    {n : ℕ} [NeZero n]
    {w : Fin n → Fin (d + 1) → ℂ}
    (hw : w ∈ ForwardTube d n) :
    0 < sourceGramMatrixRank n (sourceMinkowskiGram d n w) := by
  let i0 : Fin n := 0
  have hcone :
      InOpenForwardCone d (fun μ => (w i0 μ).im) := by
    simpa [ForwardTube, i0] using hw i0
  have hdiag :
      sourceMinkowskiGram d n w i0 i0 ≠ 0 := by
    simpa [sourceMinkowskiGram_apply_eq_complexInner] using
      openForwardCone_imag_complexSelfInner_ne_zero
        (d := d) hd (v := w i0) hcone
  have hrank :=
    matrix_rank_pos_of_nonzero_entry
      (A := Matrix.of fun i j : Fin n => sourceMinkowskiGram d n w i j)
      (i := i0) (j := i0) hdiag
  simpa [sourceGramMatrixRank] using hrank

/-- An extended-tube source tuple has positive scalar Gram rank. -/
theorem sourceGramMatrixRank_pos_of_mem_extendedTube
    [NeZero d] (hd : 2 ≤ d)
    {n : ℕ} [NeZero n]
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (hz0 : z0 ∈ ExtendedTube d n) :
    0 < sourceGramMatrixRank n (sourceMinkowskiGram d n z0) := by
  rcases Set.mem_iUnion.mp hz0 with ⟨Λ, w, hw, hz0_eq⟩
  have hforward :
      0 < sourceGramMatrixRank n (sourceMinkowskiGram d n w) :=
    sourceGramMatrixRank_pos_of_forwardTube (d := d) hd hw
  have hgram :
      sourceMinkowskiGram d n z0 = sourceMinkowskiGram d n w := by
    rw [hz0_eq, sourceMinkowskiGram_complexLorentzAction]
  simpa [hgram] using hforward

end BHW
