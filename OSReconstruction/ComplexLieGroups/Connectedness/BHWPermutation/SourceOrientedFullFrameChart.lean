import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedFullFrameTransport
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexTangent
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedLocalChart

/-!
# Chart coordinates for the selected full-frame max-rank patch

This file starts the finite-dimensional chart layer that consumes the checked
full-frame implicit-kernel lift.  The first ingredients are deliberately small:
the complement index type, mixed-row coordinates, and the selected
determinant-nonzero ambient domain.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

/-- Source labels not selected by a fixed full-frame embedding. -/
def sourceComplementIndex
    {n D : ℕ}
    (ι : Fin D ↪ Fin n) : Type :=
  {j : Fin n // j ∉ Set.range ι}

instance sourceComplementIndex_fintype
    {n D : ℕ}
    (ι : Fin D ↪ Fin n) :
    Fintype (sourceComplementIndex ι) := by
  classical
  unfold sourceComplementIndex
  infer_instance

/-- Recover the selected-frame coordinate of a source label known to be in the
selected range. -/
noncomputable def sourceSelectedIndexOfMem
    {n D : ℕ}
    (ι : Fin D ↪ Fin n)
    {j : Fin n}
    (hj : j ∈ Set.range ι) : Fin D :=
  Classical.choose hj

theorem sourceSelectedIndexOfMem_spec
    {n D : ℕ}
    (ι : Fin D ↪ Fin n)
    {j : Fin n}
    (hj : j ∈ Set.range ι) :
    ι (sourceSelectedIndexOfMem ι hj) = j :=
  Classical.choose_spec hj

/-- The mixed Gram rows against the selected full frame. -/
def sourceSelectedMixedRows
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (G : SourceOrientedGramData d n) :
    sourceComplementIndex ι → Fin (d + 1) → ℂ :=
  fun k a => G.gram k.1 (ι a)

@[simp]
theorem sourceSelectedMixedRows_apply
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (G : SourceOrientedGramData d n)
    (k : sourceComplementIndex ι)
    (a : Fin (d + 1)) :
    sourceSelectedMixedRows d n ι G k a = G.gram k.1 (ι a) :=
  rfl

/-- The mixed-row coordinate projection is continuous. -/
theorem continuous_sourceSelectedMixedRows
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n) :
    Continuous (sourceSelectedMixedRows d n ι) := by
  unfold sourceSelectedMixedRows
  apply continuous_pi
  intro k
  apply continuous_pi
  intro a
  exact
    (continuous_apply (ι a)).comp
      ((continuous_apply k.1).comp
        (continuous_sourceOrientedGramData_gram (d := d) (n := n)))

/-- The selected Gram block of oriented source data. -/
def sourceSelectedFrameGramMatrix
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (G : SourceOrientedGramData d n) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  fun a b => G.gram (ι a) (ι b)

@[simp]
theorem sourceSelectedFrameGramMatrix_apply
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (G : SourceOrientedGramData d n)
    (a b : Fin (d + 1)) :
    sourceSelectedFrameGramMatrix d n ι G a b = G.gram (ι a) (ι b) :=
  rfl

/-- Coefficients of an oriented source label relative to the selected Gram
block.  Selected labels get identity rows; unselected labels get the mixed row
times the inverse selected Gram block. -/
noncomputable def sourceSelectedFrameCoeff
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (G : SourceOrientedGramData d n) :
    Fin n → Fin (d + 1) → ℂ :=
  fun j b =>
    if hj : j ∈ Set.range ι then
      if b = sourceSelectedIndexOfMem ι hj then 1 else 0
    else
      let k : sourceComplementIndex ι := ⟨j, hj⟩
      let A := sourceSelectedFrameGramMatrix d n ι G
      ∑ a : Fin (d + 1), sourceSelectedMixedRows d n ι G k a * A⁻¹ a b

/-- Selected labels have identity coefficient rows relative to the selected
frame. -/
theorem sourceSelectedFrameCoeff_selected
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (G : SourceOrientedGramData d n)
    (a b : Fin (d + 1)) :
    sourceSelectedFrameCoeff d n ι G (ι a) b =
      if b = a then 1 else 0 := by
  have hmem : ι a ∈ Set.range ι := ⟨a, rfl⟩
  have hidx : sourceSelectedIndexOfMem ι hmem = a := by
    apply ι.injective
    exact sourceSelectedIndexOfMem_spec ι hmem
  simp [sourceSelectedFrameCoeff, hmem, hidx]

/-- The coefficient Gram expression determined by a selected frame. -/
noncomputable def sourceCoeffGramFromSelected
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (G : SourceOrientedGramData d n)
    (i j : Fin n) : ℂ :=
  ∑ a : Fin (d + 1), ∑ b : Fin (d + 1),
    sourceSelectedFrameCoeff d n ι G i a *
      sourceSelectedFrameGramMatrix d n ι G a b *
      sourceSelectedFrameCoeff d n ι G j b

/-- Selected-selected entries of the coefficient Gram are the selected Gram
block itself. -/
theorem sourceCoeffGramFromSelected_selectedSelected
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (G : SourceOrientedGramData d n)
    (a b : Fin (d + 1)) :
    sourceCoeffGramFromSelected d n ι G (ι a) (ι b) =
      G.gram (ι a) (ι b) := by
  simp [sourceCoeffGramFromSelected, sourceSelectedFrameCoeff_selected]

/-- With invertible selected Gram block, the coefficient Gram recovers mixed
entries with the unselected label on the left. -/
theorem sourceCoeffGramFromSelected_unselectedSelected
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (G : SourceOrientedGramData d n)
    (hA_unit : IsUnit (sourceSelectedFrameGramMatrix d n ι G).det)
    (k : sourceComplementIndex ι)
    (a : Fin (d + 1)) :
    sourceCoeffGramFromSelected d n ι G k.1 (ι a) =
      G.gram k.1 (ι a) := by
  let A := sourceSelectedFrameGramMatrix d n ι G
  let row : Matrix (Fin 1) (Fin (d + 1)) ℂ := fun _ b => G.gram k.1 (ι b)
  have hcancel : row * A⁻¹ * A = row :=
    Matrix.nonsing_inv_mul_cancel_right (A := A) row hA_unit
  have happ := congrFun (congrFun hcancel (0 : Fin 1)) a
  have happ' :
      (∑ b : Fin (d + 1),
          (∑ c : Fin (d + 1), row (0 : Fin 1) c * A⁻¹ c b) * A b a) =
        row (0 : Fin 1) a := by
    simpa only [Matrix.mul_apply] using happ
  have hidx (hmem : ι a ∈ Set.range ι) :
      sourceSelectedIndexOfMem ι hmem = a := by
    apply ι.injective
    exact sourceSelectedIndexOfMem_spec ι hmem
  calc
    sourceCoeffGramFromSelected d n ι G k.1 (ι a) =
        ∑ b : Fin (d + 1),
          (∑ c : Fin (d + 1), row (0 : Fin 1) c * A⁻¹ c b) * A b a := by
      simp [sourceCoeffGramFromSelected, sourceSelectedFrameCoeff,
        sourceSelectedMixedRows, A, row, k.2, hidx]
    _ = G.gram k.1 (ι a) := by
      simpa [row] using happ'

/-- The coefficient Gram is symmetric when the selected Gram block is
symmetric. -/
theorem sourceCoeffGramFromSelected_symm_of_selectedGram_symm
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (G : SourceOrientedGramData d n)
    (hA_symm :
      ∀ a b : Fin (d + 1),
        sourceSelectedFrameGramMatrix d n ι G a b =
          sourceSelectedFrameGramMatrix d n ι G b a)
    (i j : Fin n) :
    sourceCoeffGramFromSelected d n ι G i j =
      sourceCoeffGramFromSelected d n ι G j i := by
  simp only [sourceCoeffGramFromSelected]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  rw [hA_symm a b]
  ring

/-- A nonzero selected determinant on the oriented source variety makes the
selected Gram block invertible. -/
theorem sourceSelectedFrameGramMatrix_det_isUnit_of_variety_det_ne_zero
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n)
    (hdet : G.det ι ≠ 0) :
    IsUnit (sourceSelectedFrameGramMatrix d n ι G).det := by
  rcases hG with ⟨z, rfl⟩
  let M := sourceFullFrameMatrix d n ι z
  have hMdet : IsUnit M.det := by
    exact isUnit_iff_ne_zero.mpr hdet
  have hunit := sourceFullFrameGram_det_isUnit_of_frame_det_isUnit d hMdet
  have hA :
      sourceSelectedFrameGramMatrix d n ι
          (sourceOrientedMinkowskiInvariant d n z) =
        Matrix.of (sourceFullFrameGram d M) := by
    ext a b
    simp [sourceSelectedFrameGramMatrix, sourceOrientedMinkowskiInvariant,
      SourceOrientedGramData.gram, M, sourceFullFrameGram_sourceFullFrameMatrix]
  simpa [hA] using hunit

/-- Gram coordinates on the oriented source variety are symmetric. -/
theorem sourceOrientedGramVariety_gram_symm
    (d n : ℕ)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n)
    (i j : Fin n) :
    G.gram i j = G.gram j i := by
  rcases hG with ⟨z, rfl⟩
  simpa [sourceOrientedMinkowskiInvariant, SourceOrientedGramData.gram] using
    sourceMinkowskiGram_symm d n z i j

/-- The selected Gram block of a source-variety point is symmetric. -/
theorem sourceSelectedFrameGramMatrix_symm_of_variety
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n)
    (a b : Fin (d + 1)) :
    sourceSelectedFrameGramMatrix d n ι G a b =
      sourceSelectedFrameGramMatrix d n ι G b a := by
  simpa [sourceSelectedFrameGramMatrix] using
    sourceOrientedGramVariety_gram_symm d n hG (ι a) (ι b)

/-- On the oriented source variety, the coefficient Gram also recovers mixed
entries with the selected label on the left. -/
theorem sourceCoeffGramFromSelected_selectedUnselected_of_variety
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n)
    (hdet : G.det ι ≠ 0)
    (k : sourceComplementIndex ι)
    (a : Fin (d + 1)) :
    sourceCoeffGramFromSelected d n ι G (ι a) k.1 =
      G.gram (ι a) k.1 := by
  have hAunit :=
    sourceSelectedFrameGramMatrix_det_isUnit_of_variety_det_ne_zero
      d n ι hG hdet
  have hcg_symm :
      sourceCoeffGramFromSelected d n ι G (ι a) k.1 =
        sourceCoeffGramFromSelected d n ι G k.1 (ι a) :=
    sourceCoeffGramFromSelected_symm_of_selectedGram_symm
      d n ι G
      (sourceSelectedFrameGramMatrix_symm_of_variety d n ι hG) (ι a) k.1
  have hleft :=
    sourceCoeffGramFromSelected_unselectedSelected d n ι G hAunit k a
  have hGsymm := sourceOrientedGramVariety_gram_symm d n hG k.1 (ι a)
  calc
    sourceCoeffGramFromSelected d n ι G (ι a) k.1 =
        sourceCoeffGramFromSelected d n ι G k.1 (ι a) := hcg_symm
    _ = G.gram k.1 (ι a) := hleft
    _ = G.gram (ι a) k.1 := hGsymm

/-- If a realizing tuple expands through the selected-frame coefficient rows,
then the coefficient Gram expression is the realized source Gram. -/
theorem sourceCoeffGramFromSelected_eq_gram_of_invariant_vector_expansion
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {G : SourceOrientedGramData d n}
    {z : Fin n → Fin (d + 1) → ℂ}
    (hGz : G = sourceOrientedMinkowskiInvariant d n z)
    (hexpand :
      ∀ j : Fin n,
        z j =
          ∑ a : Fin (d + 1),
            sourceSelectedFrameCoeff d n ι G j a •
              sourceFullFrameMatrix d n ι z a)
    (i j : Fin n) :
    G.gram i j = sourceCoeffGramFromSelected d n ι G i j := by
  subst G
  let M := sourceFullFrameMatrix d n ι z
  let coeff :=
    sourceSelectedFrameCoeff d n ι
      (sourceOrientedMinkowskiInvariant d n z)
  have hi : z i = ∑ a : Fin (d + 1), coeff i a • M a := by
    simpa [coeff, M] using hexpand i
  have hj : z j = ∑ b : Fin (d + 1), coeff j b • M b := by
    simpa [coeff, M] using hexpand j
  calc
    (sourceOrientedMinkowskiInvariant d n z).gram i j =
        sourceComplexMinkowskiInner d (z i) (z j) := by
      rfl
    _ = sourceComplexMinkowskiInner d
          (∑ a : Fin (d + 1), coeff i a • M a)
          (∑ b : Fin (d + 1), coeff j b • M b) := by
      rw [hi, hj]
    _ = ∑ a : Fin (d + 1),
          coeff i a *
            sourceComplexMinkowskiInner d (M a)
              (∑ b : Fin (d + 1), coeff j b • M b) := by
      rw [sourceComplexMinkowskiInner_sum_smul_left]
    _ = ∑ a : Fin (d + 1),
          coeff i a *
            (∑ b : Fin (d + 1),
              coeff j b * sourceComplexMinkowskiInner d (M a) (M b)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [sourceComplexMinkowskiInner_sum_smul_right]
    _ = sourceCoeffGramFromSelected d n ι
          (sourceOrientedMinkowskiInvariant d n z) i j := by
      unfold sourceCoeffGramFromSelected
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      have hinnerAB :
          sourceComplexMinkowskiInner d (M a) (M b) =
            sourceSelectedFrameGramMatrix d n ι
              (sourceOrientedMinkowskiInvariant d n z) a b := by
        rfl
      rw [hinnerAB]
      simp [coeff]
      ring

/-- Nonzero selected full-frame determinant makes the selected source rows
span the whole source spacetime. -/
theorem sourceFullFrameMatrix_rows_span_top_of_det_ne_zero
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hdet : (sourceFullFrameMatrix d n ι z).det ≠ 0) :
    Submodule.span ℂ
        (Set.range (fun a : Fin (d + 1) =>
          sourceFullFrameMatrix d n ι z a)) = ⊤ := by
  have hli :
      LinearIndependent ℂ
        (fun a : Fin (d + 1) => sourceFullFrameMatrix d n ι z a) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet
  have hcard :
      Fintype.card (Fin (d + 1)) =
        Module.finrank ℂ (Fin (d + 1) → ℂ) := by
    simp
  exact hli.span_eq_top_of_card_eq_finrank' hcard

/-- For an actual source tuple with nonzero selected determinant, every source
row expands in the selected full frame with the selected-frame coefficients. -/
theorem sourceSelectedFrameCoeff_vector_expansion_of_invariant
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hdet : (sourceOrientedMinkowskiInvariant d n z).det ι ≠ 0)
    (j : Fin n) :
    z j =
      ∑ a : Fin (d + 1),
        sourceSelectedFrameCoeff d n ι (sourceOrientedMinkowskiInvariant d n z) j a •
          sourceFullFrameMatrix d n ι z a := by
  let G := sourceOrientedMinkowskiInvariant d n z
  let M := sourceFullFrameMatrix d n ι z
  let coeff := sourceSelectedFrameCoeff d n ι G
  by_cases hj : j ∈ Set.range ι
  · let a := sourceSelectedIndexOfMem ι hj
    have hja : ι a = j := sourceSelectedIndexOfMem_spec ι hj
    have hcoeff : coeff j = fun b => if b = a then (1 : ℂ) else 0 := by
      funext b
      simp [coeff, sourceSelectedFrameCoeff, hj, a]
    have hsum :
        (∑ b : Fin (d + 1), (if b = a then (1 : ℂ) else 0) • M b) =
          M a := by
      simp
    calc
      z j = M a := by
        rw [← hja]
        rfl
      _ = ∑ b : Fin (d + 1), coeff j b • M b := by
        rw [hcoeff, hsum]
  · let k : sourceComplementIndex ι := ⟨j, hj⟩
    have hGvar : G ∈ sourceOrientedGramVariety d n := by
      exact ⟨z, rfl⟩
    have hAunit : IsUnit (sourceSelectedFrameGramMatrix d n ι G).det :=
      sourceSelectedFrameGramMatrix_det_isUnit_of_variety_det_ne_zero
        d n ι hGvar (by simpa [G] using hdet)
    have hMdet : M.det ≠ 0 := by
      simpa [G, M, sourceOrientedMinkowskiInvariant,
        SourceOrientedGramData.det, sourceFullFrameDet] using hdet
    have hspan :
        Submodule.span ℂ (Set.range (fun a : Fin (d + 1) => M a)) = ⊤ := by
      simpa [M] using
        sourceFullFrameMatrix_rows_span_top_of_det_ne_zero d n ι z hMdet
    have hzero :
        z j - (∑ a : Fin (d + 1), coeff j a • M a) = 0 := by
      apply sourceComplexMinkowskiInner_eq_zero_of_orthogonal_spanning_family
        d (d + 1) hspan
      intro b
      let A := sourceSelectedFrameGramMatrix d n ι G
      let row : Matrix (Fin 1) (Fin (d + 1)) ℂ := fun _ a => G.gram j (ι a)
      have hcancel : row * A⁻¹ * A = row :=
        Matrix.nonsing_inv_mul_cancel_right (A := A) row hAunit
      have happ := congrFun (congrFun hcancel (0 : Fin 1)) b
      have happ' :
          (∑ a : Fin (d + 1),
              (∑ c : Fin (d + 1), row (0 : Fin 1) c * A⁻¹ c a) * A a b) =
            row (0 : Fin 1) b := by
        simpa only [Matrix.mul_apply] using happ
      have hpair_sum :
          sourceComplexMinkowskiInner d (∑ a : Fin (d + 1), coeff j a • M a)
              (M b) =
            sourceComplexMinkowskiInner d (z j) (M b) := by
        calc
          sourceComplexMinkowskiInner d (∑ a : Fin (d + 1), coeff j a • M a)
              (M b) =
              ∑ a : Fin (d + 1),
                coeff j a * sourceComplexMinkowskiInner d (M a) (M b) := by
            rw [sourceComplexMinkowskiInner_sum_smul_left]
          _ = ∑ a : Fin (d + 1),
                (∑ c : Fin (d + 1), row (0 : Fin 1) c * A⁻¹ c a) * A a b := by
            apply Finset.sum_congr rfl
            intro a _
            have hcoeff :
                coeff j a =
                  ∑ c : Fin (d + 1), row (0 : Fin 1) c * A⁻¹ c a := by
              simp [coeff, sourceSelectedFrameCoeff, hj, A, row, G,
                sourceSelectedMixedRows]
            have hinner :
                sourceComplexMinkowskiInner d (M a) (M b) = A a b := by
              rfl
            rw [hcoeff, hinner]
          _ = row (0 : Fin 1) b := happ'
          _ = sourceComplexMinkowskiInner d (z j) (M b) := by
            have hMb : M b = z (ι b) := by
              ext μ
              rfl
            rw [hMb]
            simp [row, G, sourceOrientedMinkowskiInvariant,
              SourceOrientedGramData.gram, sourceMinkowskiGram_apply_eq_complexInner]
      calc
        sourceComplexMinkowskiInner d
            (z j - (∑ a : Fin (d + 1), coeff j a • M a)) (M b) =
            sourceComplexMinkowskiInner d (z j) (M b) -
              sourceComplexMinkowskiInner d
                (∑ a : Fin (d + 1), coeff j a • M a) (M b) := by
          rw [sourceComplexMinkowskiInner_sub_left]
        _ = 0 := by
          rw [hpair_sum]
          simp
    exact sub_eq_zero.mp hzero

/-- On the oriented source variety with nonzero selected determinant, every
Gram entry is recovered from the selected-frame coefficient Gram expression. -/
theorem sourceOrientedVariety_schurGram_eq_of_selectedDet_ne_zero
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n)
    (hdet : G.det ι ≠ 0) :
    ∀ i j : Fin n,
      G.gram i j = sourceCoeffGramFromSelected d n ι G i j := by
  rcases hG with ⟨z, rfl⟩
  intro i j
  exact
    sourceCoeffGramFromSelected_eq_gram_of_invariant_vector_expansion
      d n ι rfl
      (sourceSelectedFrameCoeff_vector_expansion_of_invariant d n ι z hdet)
      i j

/-- For a realized source tuple, every selected full-frame matrix is the
coefficient matrix times the base selected full frame. -/
theorem sourceSelectedFrameCoeff_matrix_eq_frame_of_invariant
    (d n : ℕ)
    (ι κ : Fin (d + 1) ↪ Fin n)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hdet : (sourceOrientedMinkowskiInvariant d n z).det ι ≠ 0) :
    sourceFullFrameMatrix d n κ z =
      Matrix.of
        (fun a b =>
          sourceSelectedFrameCoeff d n ι
            (sourceOrientedMinkowskiInvariant d n z) (κ a) b) *
        sourceFullFrameMatrix d n ι z := by
  ext a μ
  have hvec :=
    congrFun
      (sourceSelectedFrameCoeff_vector_expansion_of_invariant
        d n ι z hdet (κ a)) μ
  simpa [sourceFullFrameMatrix, Matrix.mul_apply, Pi.smul_apply,
    smul_eq_mul] using hvec

/-- On the oriented source variety with nonzero selected determinant, all
determinant coordinates are recovered from the selected-frame coefficients. -/
theorem sourceOrientedVariety_det_eq_coeff_det_selected
    (d n : ℕ)
    (ι κ : Fin (d + 1) ↪ Fin n)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n)
    (hdet : G.det ι ≠ 0) :
    (Matrix.of
        (fun a b => sourceSelectedFrameCoeff d n ι G (κ a) b)).det *
      G.det ι =
    G.det κ := by
  rcases hG with ⟨z, rfl⟩
  let C : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    Matrix.of
      (fun a b =>
        sourceSelectedFrameCoeff d n ι
          (sourceOrientedMinkowskiInvariant d n z) (κ a) b)
  let Mι := sourceFullFrameMatrix d n ι z
  let Mκ := sourceFullFrameMatrix d n κ z
  have hmat : Mκ = C * Mι := by
    simpa [C, Mι, Mκ] using
      sourceSelectedFrameCoeff_matrix_eq_frame_of_invariant d n ι κ z hdet
  calc
    C.det * (sourceOrientedMinkowskiInvariant d n z).det ι =
        C.det * Mι.det := by
      rfl
    _ = (C * Mι).det := by
      rw [Matrix.det_mul]
    _ = Mκ.det := by
      rw [← hmat]
    _ = (sourceOrientedMinkowskiInvariant d n z).det κ := by
      rfl

/-- Ambient oriented source coordinates whose selected full-frame determinant
is nonzero. -/
def sourceFullFrameSelectedDetNonzeroDomain
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n) :
    Set (SourceOrientedGramData d n) :=
  {G | G.det ι ≠ 0}

@[simp]
theorem mem_sourceFullFrameSelectedDetNonzeroDomain
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {G : SourceOrientedGramData d n} :
    G ∈ sourceFullFrameSelectedDetNonzeroDomain d n ι ↔ G.det ι ≠ 0 :=
  Iff.rfl

/-- The selected determinant-nonzero ambient domain is open. -/
theorem sourceFullFrameSelectedDetNonzeroDomain_open
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n) :
    IsOpen (sourceFullFrameSelectedDetNonzeroDomain d n ι) := by
  exact
    isOpen_ne_fun
      ((continuous_apply ι).comp
        (continuous_sourceOrientedGramData_det (d := d) (n := n)))
      continuous_const

/-- A source-variety point with a nonzero selected full-frame determinant is
in the maximal oriented-rank stratum. -/
theorem sourceOrientedMaxRankAt_of_selectedDet_ne_zero
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n)
    (hdet : G.det ι ≠ 0) :
    SourceOrientedMaxRankAt d n G := by
  classical
  have hn : d + 1 ≤ n := by
    simpa using Fintype.card_le_of_embedding ι
  have hmin : min (d + 1) n = d + 1 := min_eq_left hn
  have hAunit :
      IsUnit (sourceSelectedFrameGramMatrix d n ι G).det :=
    sourceSelectedFrameGramMatrix_det_isUnit_of_variety_det_ne_zero
      d n ι hG hdet
  let restrictSelectedCols : (Fin n → ℂ) →ₗ[ℂ] (Fin (d + 1) → ℂ) :=
    { toFun := fun row a => row (ι a)
      map_add' := by
        intro row₁ row₂
        ext a
        rfl
      map_smul' := by
        intro c row
        ext a
        rfl }
  have hselectedRows :
      LinearIndependent ℂ (fun a : Fin (d + 1) =>
        sourceSelectedFrameGramMatrix d n ι G a) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hAunit.ne_zero
  have hfullRows :
      LinearIndependent ℂ (fun a : Fin (d + 1) =>
        (G.gram (ι a) : Fin n → ℂ)) := by
    apply LinearIndependent.of_comp restrictSelectedCols
    simpa [restrictSelectedCols, sourceSelectedFrameGramMatrix,
      Function.comp_def] using hselectedRows
  let Msel : Matrix (Fin (d + 1)) (Fin n) ℂ :=
    fun a j => G.gram (ι a) j
  have hMsel_rank : Msel.rank = d + 1 := by
    have hrank := hfullRows.rank_matrix
    simpa [Msel] using hrank
  have hrank_le_full : Msel.rank ≤ Matrix.rank G.gram := by
    simpa [Msel] using
      (Matrix.rank_submatrix_le
        (f := fun a : Fin (d + 1) => ι a)
        (e := Equiv.refl (Fin n))
        (A := G.gram))
  have hlower : min (d + 1) n ≤ sourceGramMatrixRank n G.gram := by
    simpa [sourceGramMatrixRank, hmin, hMsel_rank] using hrank_le_full
  rcases hG with ⟨z, rfl⟩
  have hupper :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z) ≤
        min (d + 1) n :=
    sourceGramMatrixRank_le_spacetime_source_min d n z
  exact le_antisymm hupper hlower

/-- Symmetrize the Gram block of a full-frame oriented coordinate, keeping the
oriented determinant coordinate unchanged.  This gives a total ambient
coordinate landing in the symmetric submodule; on the source variety it agrees
with the actual selected symmetric coordinate. -/
def sourceFullFrameSymmetrizeCoord
    (d : ℕ)
    (H : SourceFullFrameOrientedCoord d) :
    sourceFullFrameSymmetricCoordSubmodule d :=
  ⟨((fun a b : Fin (d + 1) => (H.1 a b + H.1 b a) / (2 : ℂ)), H.2),
    by
      intro a b
      change (H.1 a b + H.1 b a) / (2 : ℂ) =
        (H.1 b a + H.1 a b) / (2 : ℂ)
      rw [add_comm]⟩

@[simp]
theorem sourceFullFrameSymmetrizeCoord_coe
    (d : ℕ)
    (H : SourceFullFrameOrientedCoord d) :
    (sourceFullFrameSymmetrizeCoord d H : SourceFullFrameOrientedCoord d) =
      ((fun a b : Fin (d + 1) => (H.1 a b + H.1 b a) / (2 : ℂ)), H.2) :=
  rfl

/-- Symmetrization is the identity on already symmetric full-frame
coordinates. -/
theorem sourceFullFrameSymmetrizeCoord_eq_of_mem_symmetric
    (d : ℕ)
    {H : SourceFullFrameOrientedCoord d}
    (hH : H ∈ sourceFullFrameSymmetricCoordSubmodule d) :
    (sourceFullFrameSymmetrizeCoord d H : SourceFullFrameOrientedCoord d) =
      H := by
  apply Prod.ext
  · funext a b
    change (H.1 a b + H.1 b a) / (2 : ℂ) = H.1 a b
    rw [hH a b]
    ring
  · rfl

/-- The ambient symmetrization map is continuous. -/
theorem continuous_sourceFullFrameSymmetrizeCoord
    (d : ℕ) :
    Continuous (sourceFullFrameSymmetrizeCoord d) := by
  refine Continuous.subtype_mk ?_ ?_
  · change Continuous
      (fun H : SourceFullFrameOrientedCoord d =>
        ((fun a b : Fin (d + 1) => (H.1 a b + H.1 b a) / (2 : ℂ)), H.2))
    have hgram :
        Continuous
          (fun H : SourceFullFrameOrientedCoord d =>
            fun a b : Fin (d + 1) =>
              (H.1 a b + H.1 b a) / (2 : ℂ)) := by
      apply continuous_pi
      intro a
      apply continuous_pi
      intro b
      have hab : Continuous
          (fun H : SourceFullFrameOrientedCoord d => H.1 a b) :=
        (continuous_apply b).comp ((continuous_apply a).comp continuous_fst)
      have hba : Continuous
          (fun H : SourceFullFrameOrientedCoord d => H.1 b a) :=
        (continuous_apply a).comp ((continuous_apply b).comp continuous_fst)
      exact (hab.add hba).div_const (2 : ℂ)
    exact hgram.prodMk continuous_snd

/-- Total ambient selected symmetric coordinate obtained by symmetrizing the
selected full-frame block. -/
def sourceFullFrameSelectedSymmetricCoordAmbient
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (G : SourceOrientedGramData d n) :
    sourceFullFrameSymmetricCoordSubmodule d :=
  sourceFullFrameSymmetrizeCoord d
    (sourceFullFrameOrientedCoordOfSource d n ι G)

/-- The ambient selected symmetric coordinate is continuous. -/
theorem continuous_sourceFullFrameSelectedSymmetricCoordAmbient
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n) :
    Continuous (sourceFullFrameSelectedSymmetricCoordAmbient d n ι) :=
  (continuous_sourceFullFrameSymmetrizeCoord d).comp
    (continuous_sourceFullFrameOrientedCoordOfSource d n ι)

/-- A source-variety point supplies a symmetric selected full-frame coordinate. -/
def sourceFullFrameSelectedSymmetricCoordOfSource
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n) :
    sourceFullFrameSymmetricCoordSubmodule d :=
  ⟨sourceFullFrameOrientedCoordOfSource d n ι G,
    sourceFullFrameOrientedGramVarietyCoord_subset_symmetric d
      (sourceFullFrameOrientedCoordOfSource_mem_varietyCoord_of_mem_variety d n ι hG)⟩

@[simp]
theorem sourceFullFrameSelectedSymmetricCoordOfSource_coe
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n) :
    (sourceFullFrameSelectedSymmetricCoordOfSource d n ι hG :
      SourceFullFrameOrientedCoord d) =
      sourceFullFrameOrientedCoordOfSource d n ι G :=
  rfl

theorem sourceFullFrameSelectedSymmetricCoordOfSource_mem_varietyCoord
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n) :
    sourceFullFrameSelectedSymmetricCoordOfSource d n ι hG ∈
      sourceFullFrameSymmetricVarietyCoord d := by
  simpa [sourceFullFrameSymmetricVarietyCoord,
    sourceFullFrameSelectedSymmetricCoordOfSource] using
    sourceFullFrameOrientedCoordOfSource_mem_varietyCoord_of_mem_variety d n ι hG

theorem sourceFullFrameSelectedSymmetricCoordOfSource_mem_detNonzeroCoord
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n)
    (hdet : G ∈ sourceFullFrameSelectedDetNonzeroDomain d n ι) :
    sourceFullFrameSelectedSymmetricCoordOfSource d n ι hG ∈
      sourceFullFrameSymmetricDetNonzeroCoord d := by
  simpa [sourceFullFrameSymmetricDetNonzeroCoord,
    sourceFullFrameSelectedSymmetricCoordOfSource,
    sourceFullFrameSelectedDetNonzeroDomain] using hdet

/-- On the source variety, the total ambient selected symmetric coordinate is
the proof-carrying selected symmetric coordinate. -/
theorem sourceFullFrameSelectedSymmetricCoordAmbient_eq_of_mem_variety
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n) :
    sourceFullFrameSelectedSymmetricCoordAmbient d n ι G =
      sourceFullFrameSelectedSymmetricCoordOfSource d n ι hG := by
  apply Subtype.ext
  have hsym :
      sourceFullFrameOrientedCoordOfSource d n ι G ∈
        sourceFullFrameSymmetricCoordSubmodule d :=
    sourceFullFrameOrientedGramVarietyCoord_subset_symmetric d
      (sourceFullFrameOrientedCoordOfSource_mem_varietyCoord_of_mem_variety
        d n ι hG)
  simpa [sourceFullFrameSelectedSymmetricCoordAmbient,
    sourceFullFrameSelectedSymmetricCoordOfSource] using
    sourceFullFrameSymmetrizeCoord_eq_of_mem_symmetric d hsym

/-- If the chosen base frame represents the selected full-frame coordinate of
`G0`, then the ambient selected symmetric coordinate at `G0` is the symmetric
implicit-chart base point. -/
theorem sourceFullFrameSelectedSymmetricCoordAmbient_eq_base_of_oriented_eq
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    {G0 : SourceOrientedGramData d n}
    (hG0 : G0 ∈ sourceOrientedGramVariety d n)
    (hM0_oriented :
      sourceFullFrameOrientedGramCoord d M0 =
        sourceFullFrameOrientedCoordOfSource d n ι G0) :
    sourceFullFrameSelectedSymmetricCoordAmbient d n ι G0 =
      sourceFullFrameSymmetricBase d M0 := by
  apply Subtype.ext
  rw [sourceFullFrameSelectedSymmetricCoordAmbient_eq_of_mem_variety d n ι hG0]
  simpa [sourceFullFrameSelectedSymmetricCoordOfSource,
    sourceFullFrameSymmetricBase] using hM0_oriented.symm

/-- At a represented base point, the ambient selected symmetric coordinate
lies in the symmetric implicit-chart source. -/
theorem sourceFullFrameSelectedSymmetricCoordAmbient_mem_implicitSource_at_base
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    {G0 : SourceOrientedGramData d n}
    (hG0 : G0 ∈ sourceOrientedGramVariety d n)
    (hM0_oriented :
      sourceFullFrameOrientedGramCoord d M0 =
        sourceFullFrameOrientedCoordOfSource d n ι G0) :
    sourceFullFrameSelectedSymmetricCoordAmbient d n ι G0 ∈
      (sourceFullFrameSymmetricEquation_implicitChart d M0 hM0).source := by
  rw [sourceFullFrameSelectedSymmetricCoordAmbient_eq_base_of_oriented_eq
    d n ι hG0 hM0_oriented]
  exact sourceFullFrameSymmetricBase_mem_implicitChart_source d hM0

/-- The first constructor shrink: the ambient selected symmetric coordinate
lands in the symmetric implicit-chart source for all sufficiently near ambient
oriented Gram data. -/
theorem sourceFullFrameSelectedSymmetricCoordAmbient_eventually_mem_implicitSource
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    {G0 : SourceOrientedGramData d n}
    (hG0 : G0 ∈ sourceOrientedGramVariety d n)
    (hM0_oriented :
      sourceFullFrameOrientedGramCoord d M0 =
        sourceFullFrameOrientedCoordOfSource d n ι G0) :
    {G : SourceOrientedGramData d n |
      sourceFullFrameSelectedSymmetricCoordAmbient d n ι G ∈
        (sourceFullFrameSymmetricEquation_implicitChart d M0 hM0).source} ∈
      𝓝 G0 := by
  have hbase :
      sourceFullFrameSelectedSymmetricCoordAmbient d n ι G0 =
        sourceFullFrameSymmetricBase d M0 :=
    sourceFullFrameSelectedSymmetricCoordAmbient_eq_base_of_oriented_eq
      d n ι hG0 hM0_oriented
  have hsource :
      (sourceFullFrameSymmetricEquation_implicitChart d M0 hM0).source ∈
        𝓝 (sourceFullFrameSelectedSymmetricCoordAmbient d n ι G0) := by
    simpa [hbase] using
      sourceFullFrameSymmetricEquation_implicitChart_source_mem_nhds_base
        d hM0
  have hcont :
      ContinuousAt (sourceFullFrameSelectedSymmetricCoordAmbient d n ι) G0 :=
    (continuous_sourceFullFrameSelectedSymmetricCoordAmbient d n ι).continuousAt
  exact hcont.preimage_mem_nhds hsource

/-- The selected full-frame coordinate of a source-variety point, expressed as
the second coordinate of the symmetric implicit chart at the base frame. -/
noncomputable def sourceFullFrameSelectedKernelCoord
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n) :
    (sourceFullFrameSymmetricEquationDerivCLM d
      (sourceFullFrameOrientedGramCoord d M0)).ker :=
  ((sourceFullFrameSymmetricEquation_implicitChart d M0 hM0)
    (sourceFullFrameSelectedSymmetricCoordOfSource d n ι hG)).2

@[simp]
theorem sourceFullFrameSelectedKernelCoord_eq_implicitChart_snd
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n) :
    sourceFullFrameSelectedKernelCoord d n ι hM0 hG =
      ((sourceFullFrameSymmetricEquation_implicitChart d M0 hM0)
        (sourceFullFrameSelectedSymmetricCoordOfSource d n ι hG)).2 :=
  rfl

/-- Total ambient selected kernel coordinate.  On the source variety this
agrees with `sourceFullFrameSelectedKernelCoord`, but it is defined for every
ambient oriented Gram datum, which is needed for the ambient chart map. -/
noncomputable def sourceFullFrameSelectedKernelCoordAmbient
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (G : SourceOrientedGramData d n) :
    (sourceFullFrameSymmetricEquationDerivCLM d
      (sourceFullFrameOrientedGramCoord d M0)).ker :=
  ((sourceFullFrameSymmetricEquation_implicitChart d M0 hM0)
    (sourceFullFrameSelectedSymmetricCoordAmbient d n ι G)).2

/-- The ambient selected kernel coordinate restricts to the source-variety
selected kernel coordinate. -/
theorem sourceFullFrameSelectedKernelCoordAmbient_eq_of_mem_variety
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n) :
    sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G =
      sourceFullFrameSelectedKernelCoord d n ι hM0 hG := by
  rw [sourceFullFrameSelectedKernelCoordAmbient,
    sourceFullFrameSelectedKernelCoord,
    sourceFullFrameSelectedSymmetricCoordAmbient_eq_of_mem_variety d n ι hG]

theorem sourceFullFrameSelectedKernelCoord_eq_kernelProjection
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n) :
    sourceFullFrameSelectedKernelCoord d n ι hM0 hG =
      sourceFullFrameSymmetricEquationKernelProjection d M0
        (sourceFullFrameSelectedSymmetricCoordOfSource d n ι hG -
          sourceFullFrameSymmetricBase d M0) := by
  unfold sourceFullFrameSelectedKernelCoord
  exact
    sourceFullFrameSymmetricEquation_implicitChart_snd d M0 hM0
      (sourceFullFrameSelectedSymmetricCoordOfSource d n ι hG)

theorem sourceFullFrameSelectedKernelCoord_eq_zero_of_selected_eq_base
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n)
    (hbase :
      sourceFullFrameSelectedSymmetricCoordOfSource d n ι hG =
        sourceFullFrameSymmetricBase d M0) :
    sourceFullFrameSelectedKernelCoord d n ι hM0 hG = 0 := by
  rw [sourceFullFrameSelectedKernelCoord_eq_kernelProjection, hbase, sub_self]
  exact map_zero (sourceFullFrameSymmetricEquationKernelProjection d M0)

/-- At a represented base point, the ambient selected kernel coordinate is
zero. -/
theorem sourceFullFrameSelectedKernelCoordAmbient_eq_zero_at_base
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    {G0 : SourceOrientedGramData d n}
    (hG0 : G0 ∈ sourceOrientedGramVariety d n)
    (hM0_oriented :
      sourceFullFrameOrientedGramCoord d M0 =
        sourceFullFrameOrientedCoordOfSource d n ι G0) :
    sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G0 = 0 := by
  have hbaseAmbient :=
    sourceFullFrameSelectedSymmetricCoordAmbient_eq_base_of_oriented_eq
      d n ι hG0 hM0_oriented
  have hbase :
      sourceFullFrameSelectedSymmetricCoordOfSource d n ι hG0 =
        sourceFullFrameSymmetricBase d M0 := by
    rw [← sourceFullFrameSelectedSymmetricCoordAmbient_eq_of_mem_variety
      d n ι hG0]
    exact hbaseAmbient
  rw [sourceFullFrameSelectedKernelCoordAmbient_eq_of_mem_variety
    d n ι hM0 hG0]
  exact sourceFullFrameSelectedKernelCoord_eq_zero_of_selected_eq_base
    d n ι hM0 hG0 hbase

/-- The ambient selected kernel coordinate is continuous at a represented base
point.  This uses continuity of the symmetric implicit chart at its source
base point and the total ambient symmetrized selected coordinate. -/
theorem continuousAt_sourceFullFrameSelectedKernelCoordAmbient_at_base
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    {G0 : SourceOrientedGramData d n}
    (hG0 : G0 ∈ sourceOrientedGramVariety d n)
    (hM0_oriented :
      sourceFullFrameOrientedGramCoord d M0 =
        sourceFullFrameOrientedCoordOfSource d n ι G0) :
    ContinuousAt
      (sourceFullFrameSelectedKernelCoordAmbient d n ι hM0) G0 := by
  let e := sourceFullFrameSymmetricEquation_implicitChart d M0 hM0
  have hbase :
      sourceFullFrameSelectedSymmetricCoordAmbient d n ι G0 =
        sourceFullFrameSymmetricBase d M0 :=
    sourceFullFrameSelectedSymmetricCoordAmbient_eq_base_of_oriented_eq
      d n ι hG0 hM0_oriented
  have he :
      ContinuousAt e (sourceFullFrameSelectedSymmetricCoordAmbient d n ι G0) := by
    simpa [e, hbase] using
      e.continuousAt (sourceFullFrameSymmetricBase_mem_implicitChart_source d hM0)
  have hselected :
      ContinuousAt (sourceFullFrameSelectedSymmetricCoordAmbient d n ι) G0 :=
    (continuous_sourceFullFrameSelectedSymmetricCoordAmbient d n ι).continuousAt
  have hcomp :
      ContinuousAt
        (fun G : SourceOrientedGramData d n =>
          e (sourceFullFrameSelectedSymmetricCoordAmbient d n ι G)) G0 :=
    he.comp hselected
  exact continuous_snd.continuousAt.comp hcomp

/-- The second constructor shrink: the ambient selected kernel coordinate lies
in the gauge-slice kernel-chart target for all sufficiently near ambient
oriented Gram data. -/
theorem sourceFullFrameSelectedKernelCoordAmbient_eventually_mem_kernelTarget
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0)
    {G0 : SourceOrientedGramData d n}
    (hG0 : G0 ∈ sourceOrientedGramVariety d n)
    (hM0_oriented :
      sourceFullFrameOrientedGramCoord d M0 =
        sourceFullFrameOrientedCoordOfSource d n ι G0) :
    {G : SourceOrientedGramData d n |
      sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G ∈
        (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
          d hM0 S).target} ∈
      𝓝 G0 := by
  have hzero :
      sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G0 = 0 :=
    sourceFullFrameSelectedKernelCoordAmbient_eq_zero_at_base
      d n ι hM0 hG0 hM0_oriented
  have htarget :
      (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
          d hM0 S).target ∈
        𝓝 (sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G0) := by
    simpa [hzero] using
      sourceFullFrameGaugeSliceImplicitKernel_chartTarget_mem_nhds_zero
        d hM0 S
  exact
    (continuousAt_sourceFullFrameSelectedKernelCoordAmbient_at_base
      d n ι hM0 hG0 hM0_oriented).preimage_mem_nhds htarget

/-- The third constructor shrink: the gauge-slice lift of the ambient selected
kernel coordinate lies in the symmetric implicit-chart source for all
sufficiently near ambient oriented Gram data. -/
theorem sourceFullFrameSelectedKernelCoordAmbient_eventually_gaugeSlice_mem_implicitSource
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0)
    {G0 : SourceOrientedGramData d n}
    (hG0 : G0 ∈ sourceOrientedGramVariety d n)
    (hM0_oriented :
      sourceFullFrameOrientedGramCoord d M0 =
        sourceFullFrameOrientedCoordOfSource d n ι G0) :
    {G : SourceOrientedGramData d n |
      sourceFullFrameGaugeSliceMapSymmetric d M0 S
          ((sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
            d hM0 S).symm
            (sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G)) ∈
        (sourceFullFrameSymmetricEquation_implicitChart d M0 hM0).source} ∈
      𝓝 G0 := by
  have hzero :
      sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G0 = 0 :=
    sourceFullFrameSelectedKernelCoordAmbient_eq_zero_at_base
      d n ι hM0 hG0 hM0_oriented
  have hsource :
      {K : (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d M0)).ker |
        sourceFullFrameGaugeSliceMapSymmetric d M0 S
          ((sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).symm K) ∈
          (sourceFullFrameSymmetricEquation_implicitChart d M0 hM0).source} ∈
        𝓝 (sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G0) := by
    simpa [hzero] using
      sourceFullFrameGaugeSliceImplicitKernel_symm_implicitSource_mem_nhds_zero
        d hM0 S
  exact
    (continuousAt_sourceFullFrameSelectedKernelCoordAmbient_at_base
      d n ι hM0 hG0 hM0_oriented).preimage_mem_nhds hsource

/-- An open ambient neighborhood around a represented full-frame max-rank base
point on which all source/target shrink conditions for the candidate chart
hold. -/
structure SourceFullFrameMaxRankChartAmbientShrink
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0)
    (G0 : SourceOrientedGramData d n) where
  Ωamb : Set (SourceOrientedGramData d n)
  Ωamb_open : IsOpen Ωamb
  center_mem : G0 ∈ Ωamb
  selectedSymmetric_mem_implicitSource :
    ∀ {G : SourceOrientedGramData d n}, G ∈ Ωamb →
      sourceFullFrameSelectedSymmetricCoordAmbient d n ι G ∈
        (sourceFullFrameSymmetricEquation_implicitChart d M0 hM0).source
  selectedKernel_mem_target :
    ∀ {G : SourceOrientedGramData d n}, G ∈ Ωamb →
      sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G ∈
        (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
          d hM0 S).target
  gaugeSlice_mem_implicitSource :
    ∀ {G : SourceOrientedGramData d n}, G ∈ Ωamb →
      sourceFullFrameGaugeSliceMapSymmetric d M0 S
          ((sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
            d hM0 S).symm
            (sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G)) ∈
        (sourceFullFrameSymmetricEquation_implicitChart d M0 hM0).source
  selectedDetNonzero :
    Ωamb ⊆ sourceFullFrameSelectedDetNonzeroDomain d n ι

/-- Produce the ambient open shrink by intersecting the three checked
source/target neighborhoods with the selected determinant-nonzero sheet. -/
noncomputable def sourceFullFrameMaxRankChart_ambientShrink
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0)
    {G0 : SourceOrientedGramData d n}
    (hG0 : G0 ∈ sourceOrientedGramVariety d n)
    (hM0_oriented :
      sourceFullFrameOrientedGramCoord d M0 =
        sourceFullFrameOrientedCoordOfSource d n ι G0) :
    SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0 := by
  classical
  let Aselected : Set (SourceOrientedGramData d n) :=
    {G |
      sourceFullFrameSelectedSymmetricCoordAmbient d n ι G ∈
        (sourceFullFrameSymmetricEquation_implicitChart d M0 hM0).source}
  let Akernel : Set (SourceOrientedGramData d n) :=
    {G |
      sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G ∈
        (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
          d hM0 S).target}
  let Agauge : Set (SourceOrientedGramData d n) :=
    {G |
      sourceFullFrameGaugeSliceMapSymmetric d M0 S
          ((sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
            d hM0 S).symm
            (sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G)) ∈
        (sourceFullFrameSymmetricEquation_implicitChart d M0 hM0).source}
  let D : Set (SourceOrientedGramData d n) :=
    sourceFullFrameSelectedDetNonzeroDomain d n ι
  have hselected : Aselected ∈ 𝓝 G0 := by
    simpa [Aselected] using
      sourceFullFrameSelectedSymmetricCoordAmbient_eventually_mem_implicitSource
        d n ι hM0 hG0 hM0_oriented
  have hkernel : Akernel ∈ 𝓝 G0 := by
    simpa [Akernel] using
      sourceFullFrameSelectedKernelCoordAmbient_eventually_mem_kernelTarget
        d n ι hM0 S hG0 hM0_oriented
  have hgauge : Agauge ∈ 𝓝 G0 := by
    simpa [Agauge] using
      sourceFullFrameSelectedKernelCoordAmbient_eventually_gaugeSlice_mem_implicitSource
        d n ι hM0 S hG0 hM0_oriented
  have hG0det : G0.det ι ≠ 0 := by
    have hdet_eq : G0.det ι = M0.det := by
      simpa [sourceFullFrameOrientedCoordOfSource] using
        (congrArg Prod.snd hM0_oriented).symm
    rw [hdet_eq]
    exact hM0.ne_zero
  have hdet : D ∈ 𝓝 G0 := by
    exact (sourceFullFrameSelectedDetNonzeroDomain_open d n ι).mem_nhds hG0det
  let A : Set (SourceOrientedGramData d n) :=
    Aselected ∩ (Akernel ∩ (Agauge ∩ D))
  have hA : A ∈ 𝓝 G0 := by
    exact inter_mem hselected (inter_mem hkernel (inter_mem hgauge hdet))
  let Ωamb : Set (SourceOrientedGramData d n) :=
    Classical.choose (mem_nhds_iff.mp hA)
  have hΩamb_spec :
      Ωamb ⊆ A ∧ IsOpen Ωamb ∧ G0 ∈ Ωamb :=
    Classical.choose_spec (mem_nhds_iff.mp hA)
  have hΩamb_sub : Ωamb ⊆ A := hΩamb_spec.1
  have hΩamb_open : IsOpen Ωamb := hΩamb_spec.2.1
  have hcenter : G0 ∈ Ωamb := hΩamb_spec.2.2
  exact
    { Ωamb := Ωamb
      Ωamb_open := hΩamb_open
      center_mem := hcenter
      selectedSymmetric_mem_implicitSource := by
        intro G hG
        exact (hΩamb_sub hG).1
      selectedKernel_mem_target := by
        intro G hG
        exact (hΩamb_sub hG).2.1
      gaugeSlice_mem_implicitSource := by
        intro G hG
        exact (hΩamb_sub hG).2.2.1
      selectedDetNonzero := by
        intro G hG
        exact (hΩamb_sub hG).2.2.2 }

namespace SourceFullFrameMaxRankChartAmbientShrink

/-- The relative source-variety domain obtained from the ambient shrink. -/
def relDomain
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    {hM0 : IsUnit M0.det}
    {S : SourceFullFrameGaugeSliceData d M0}
    {G0 : SourceOrientedGramData d n}
    (T : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0) :
    Set (SourceOrientedGramData d n) :=
  T.Ωamb ∩ sourceOrientedGramVariety d n

/-- The relative domain of an ambient shrink is relatively open in the source
oriented variety. -/
theorem relDomain_relOpen
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    {hM0 : IsUnit M0.det}
    {S : SourceFullFrameGaugeSliceData d M0}
    {G0 : SourceOrientedGramData d n}
    (T : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0) :
    IsRelOpenInSourceOrientedGramVariety d n T.relDomain :=
  ⟨T.Ωamb, T.Ωamb_open, rfl⟩

/-- The base point belongs to the relative domain whenever it belongs to the
source oriented variety. -/
theorem center_mem_relDomain
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    {hM0 : IsUnit M0.det}
    {S : SourceFullFrameGaugeSliceData d M0}
    {G0 : SourceOrientedGramData d n}
    (T : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0)
    (hG0 : G0 ∈ sourceOrientedGramVariety d n) :
    G0 ∈ T.relDomain :=
  ⟨T.center_mem, hG0⟩

theorem mem_Ωamb_of_mem_relDomain
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    {hM0 : IsUnit M0.det}
    {S : SourceFullFrameGaugeSliceData d M0}
    {G0 G : SourceOrientedGramData d n}
    (T : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0)
    (hG : G ∈ T.relDomain) :
    G ∈ T.Ωamb :=
  hG.1

theorem mem_variety_of_mem_relDomain
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    {hM0 : IsUnit M0.det}
    {S : SourceFullFrameGaugeSliceData d M0}
    {G0 G : SourceOrientedGramData d n}
    (T : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0)
    (hG : G ∈ T.relDomain) :
    G ∈ sourceOrientedGramVariety d n :=
  hG.2

theorem selectedDet_ne_zero_of_mem_relDomain
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    {hM0 : IsUnit M0.det}
    {S : SourceFullFrameGaugeSliceData d M0}
    {G0 G : SourceOrientedGramData d n}
    (T : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0)
    (hG : G ∈ T.relDomain) :
    G.det ι ≠ 0 :=
  T.selectedDetNonzero hG.1

/-- The relative domain of an ambient full-frame shrink lies in the
maximal-rank stratum. -/
theorem maxRank_of_mem_relDomain
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    {hM0 : IsUnit M0.det}
    {S : SourceFullFrameGaugeSliceData d M0}
    {G0 G : SourceOrientedGramData d n}
    (T : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0)
    (hG : G ∈ T.relDomain) :
    SourceOrientedMaxRankAt d n G :=
  sourceOrientedMaxRankAt_of_selectedDet_ne_zero d n ι
    (T.mem_variety_of_mem_relDomain hG)
    (T.selectedDet_ne_zero_of_mem_relDomain hG)

end SourceFullFrameMaxRankChartAmbientShrink

/-- The selected full-frame coordinate of a source-variety point has implicit
chart coordinates `(0, selectedKernelCoord)`. -/
theorem sourceFullFrameSelectedImplicitChart_eq_zero_kernelCoord
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n) :
    (sourceFullFrameSymmetricEquation_implicitChart d M0 hM0)
        (sourceFullFrameSelectedSymmetricCoordOfSource d n ι hG) =
      (0, sourceFullFrameSelectedKernelCoord d n ι hM0 hG) := by
  have hzero :
      sourceFullFrameSymmetricEquation d
          (sourceFullFrameSelectedSymmetricCoordOfSource d n ι hG) = 0 := by
    have hvar :=
      sourceFullFrameSelectedSymmetricCoordOfSource_mem_varietyCoord
        d n ι hG
    have hhyp :
        ((sourceFullFrameSelectedSymmetricCoordOfSource d n ι hG :
            sourceFullFrameSymmetricCoordSubmodule d) :
          SourceFullFrameOrientedCoord d) ∈
          sourceFullFrameOrientedHypersurfaceCoord d :=
      sourceFullFrameOrientedGramVarietyCoord_subset_hypersurface d hvar
    simpa [sourceFullFrameSymmetricEquation] using hhyp.2
  rw [sourceFullFrameSymmetricEquation_implicitChart_eq_zero_kernelProjection
    d M0 hM0 _ hzero]
  rw [sourceFullFrameSelectedKernelCoord_eq_kernelProjection]

/-- The gauge-slice symmetric coordinate has implicit chart coordinates
`(0, implicitKernelMap X)`. -/
theorem sourceFullFrameGaugeSliceMapSymmetric_implicitChart_eq_zero_kernelMap
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0)
    (X : S.slice) :
    (sourceFullFrameSymmetricEquation_implicitChart d M0 hM0)
        (sourceFullFrameGaugeSliceMapSymmetric d M0 S X) =
      (0, sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S X) := by
  apply Prod.ext
  · have hzero :
        sourceFullFrameSymmetricEquation d
            (sourceFullFrameGaugeSliceMapSymmetric d M0 S X) = 0 := by
      have hhyp :=
        sourceFullFrameGaugeSliceMapSymmetric_mem_hypersurface d M0 S X
      simpa [sourceFullFrameSymmetricHypersurfaceCoord] using hhyp
    rw [sourceFullFrameSymmetricEquation_implicitChart_fst, hzero]
  · rfl

/-- If the selected source coordinate and a gauge-slice coordinate are both in
the symmetric implicit-chart source and have the same kernel coordinate, then
they are the same symmetric full-frame coordinate. -/
theorem sourceFullFrameSelectedSymmetricCoordOfSource_eq_gaugeSliceMapSymmetric_of_kernel_eq
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n)
    (X : S.slice)
    (hG_source :
      sourceFullFrameSelectedSymmetricCoordOfSource d n ι hG ∈
        (sourceFullFrameSymmetricEquation_implicitChart d M0 hM0).source)
    (hX_source :
      sourceFullFrameGaugeSliceMapSymmetric d M0 S X ∈
        (sourceFullFrameSymmetricEquation_implicitChart d M0 hM0).source)
    (hkernel :
      sourceFullFrameSelectedKernelCoord d n ι hM0 hG =
        sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S X) :
    sourceFullFrameSelectedSymmetricCoordOfSource d n ι hG =
      sourceFullFrameGaugeSliceMapSymmetric d M0 S X := by
  let e := sourceFullFrameSymmetricEquation_implicitChart d M0 hM0
  apply e.injOn hG_source hX_source
  calc
    e (sourceFullFrameSelectedSymmetricCoordOfSource d n ι hG) =
        (0, sourceFullFrameSelectedKernelCoord d n ι hM0 hG) := by
      simpa [e] using
        sourceFullFrameSelectedImplicitChart_eq_zero_kernelCoord
          d n ι hM0 hG
    _ = (0, sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S X) := by
      rw [hkernel]
    _ = e (sourceFullFrameGaugeSliceMapSymmetric d M0 S X) := by
      simpa [e] using
        (sourceFullFrameGaugeSliceMapSymmetric_implicitChart_eq_zero_kernelMap
          d hM0 S X).symm

/-- Oriented-coordinate form of
`sourceFullFrameSelectedSymmetricCoordOfSource_eq_gaugeSliceMapSymmetric_of_kernel_eq`. -/
theorem sourceFullFrameOrientedCoordOfSource_eq_gaugeSliceMap_of_kernel_eq
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n)
    (X : S.slice)
    (hG_source :
      sourceFullFrameSelectedSymmetricCoordOfSource d n ι hG ∈
        (sourceFullFrameSymmetricEquation_implicitChart d M0 hM0).source)
    (hX_source :
      sourceFullFrameGaugeSliceMapSymmetric d M0 S X ∈
        (sourceFullFrameSymmetricEquation_implicitChart d M0 hM0).source)
    (hkernel :
      sourceFullFrameSelectedKernelCoord d n ι hM0 hG =
        sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S X) :
    sourceFullFrameOrientedCoordOfSource d n ι G =
      sourceFullFrameGaugeSliceMap d M0 S X := by
  have hsym :=
    sourceFullFrameSelectedSymmetricCoordOfSource_eq_gaugeSliceMapSymmetric_of_kernel_eq
      d n ι hM0 S hG X hG_source hX_source hkernel
  have hcoe := congrArg
    (fun H : sourceFullFrameSymmetricCoordSubmodule d =>
      (H : SourceFullFrameOrientedCoord d)) hsym
  simpa [sourceFullFrameSelectedSymmetricCoordOfSource,
    sourceFullFrameGaugeSliceMapSymmetric] using hcoe

/-- Reconstruct the selected full-frame matrix from a gauge-slice coordinate. -/
noncomputable def sourceFullFrameGauge_reconstructFrame
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0)
    (y : S.slice × (sourceComplementIndex ι → Fin (d + 1) → ℂ)) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  M0 + (y.1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)

/-- The reconstructed selected-frame matrix is continuous in model
coordinates. -/
theorem continuous_sourceFullFrameGauge_reconstructFrame
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0) :
    Continuous (sourceFullFrameGauge_reconstructFrame d n ι M0 S) := by
  have hfst :
      Continuous
        (fun y : S.slice × (sourceComplementIndex ι → Fin (d + 1) → ℂ) =>
          (y.1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)) :=
    continuous_subtype_val.comp continuous_fst
  simpa [sourceFullFrameGauge_reconstructFrame] using
    continuous_const.add hfst

/-- The reconstructed selected-frame matrix is differentiable in model
coordinates. -/
theorem differentiable_sourceFullFrameGauge_reconstructFrame
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0) :
    Differentiable ℂ (sourceFullFrameGauge_reconstructFrame d n ι M0 S) := by
  have hfst :
      Differentiable ℂ
        (fun y : S.slice × (sourceComplementIndex ι → Fin (d + 1) → ℂ) =>
          (y.1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)) := by
    exact
      S.slice.subtypeL.differentiable.comp
        (ContinuousLinearMap.fst ℂ S.slice
          (sourceComplementIndex ι → Fin (d + 1) → ℂ)).differentiable
  simpa [sourceFullFrameGauge_reconstructFrame] using
    (show Differentiable ℂ
        (fun y : S.slice × (sourceComplementIndex ι → Fin (d + 1) → ℂ) =>
          M0 + (y.1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)) from
      hfst.const_add M0)

/-- Model coordinates whose reconstructed selected frame remains invertible. -/
def sourceFullFrameGaugeModelDetNonzero
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0) :
    Set (S.slice × (sourceComplementIndex ι → Fin (d + 1) → ℂ)) :=
  {y | (sourceFullFrameGauge_reconstructFrame d n ι M0 S y).det ≠ 0}

@[simp]
theorem mem_sourceFullFrameGaugeModelDetNonzero
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    {S : SourceFullFrameGaugeSliceData d M0}
    {y : S.slice × (sourceComplementIndex ι → Fin (d + 1) → ℂ)} :
    y ∈ sourceFullFrameGaugeModelDetNonzero d n ι M0 S ↔
      (sourceFullFrameGauge_reconstructFrame d n ι M0 S y).det ≠ 0 :=
  Iff.rfl

/-- The reconstructed selected-frame determinant-nonzero model locus is open. -/
theorem sourceFullFrameGaugeModelDetNonzero_open
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0) :
    IsOpen (sourceFullFrameGaugeModelDetNonzero d n ι M0 S) := by
  exact
    isOpen_ne_fun
      ((continuous_sourceFullFrameGauge_reconstructFrame d n ι M0 S).matrix_det)
      continuous_const

/-- The inverse kernel chart sends the zero kernel coordinate to the zero
gauge-slice coordinate. -/
theorem sourceFullFrameGaugeSliceImplicitKernel_symm_zero
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).symm
      (0 :
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d M0)).ker) = (0 : S.slice) := by
  have h :=
    sourceFullFrameGaugeSliceImplicitKernelMap_left_inv_on_chartSource d hM0 S
      (sourceFullFrameGaugeSliceImplicitKernel_zero_mem_chartSource d hM0 S)
  simpa using h

/-- Reconstruct all source vectors from a selected-frame gauge coordinate and
free mixed rows. -/
noncomputable def sourceFullFrameGauge_reconstructVector
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0)
    (y : S.slice × (sourceComplementIndex ι → Fin (d + 1) → ℂ)) :
    Fin n → Fin (d + 1) → ℂ :=
  fun j μ =>
    if hj : j ∈ Set.range ι then
      sourceFullFrameGauge_reconstructFrame d n ι M0 S y
        (sourceSelectedIndexOfMem ι hj) μ
    else
      let k : sourceComplementIndex ι := ⟨j, hj⟩
      let M := sourceFullFrameGauge_reconstructFrame d n ι M0 S y
      let A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
        Matrix.of (sourceFullFrameGram d M)
      ∑ b : Fin (d + 1),
        (∑ a : Fin (d + 1), y.2 k a * A⁻¹ a b) * M b μ

/-- Coefficients of each reconstructed source vector relative to the selected
reconstructed full frame. -/
noncomputable def sourceFullFrameGauge_reconstructCoeff
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0)
    (y : S.slice × (sourceComplementIndex ι → Fin (d + 1) → ℂ)) :
    Fin n → Fin (d + 1) → ℂ :=
  fun j b =>
    if hj : j ∈ Set.range ι then
      if b = sourceSelectedIndexOfMem ι hj then 1 else 0
    else
      let k : sourceComplementIndex ι := ⟨j, hj⟩
      let M := sourceFullFrameGauge_reconstructFrame d n ι M0 S y
      let A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
        Matrix.of (sourceFullFrameGram d M)
      ∑ a : Fin (d + 1), y.2 k a * A⁻¹ a b

@[simp]
theorem sourceFullFrameGauge_reconstructFrame_apply
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0)
    (y : S.slice × (sourceComplementIndex ι → Fin (d + 1) → ℂ))
    (a μ : Fin (d + 1)) :
    sourceFullFrameGauge_reconstructFrame d n ι M0 S y a μ =
      (M0 + (y.1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)) a μ :=
  rfl

/-- The selected rows of the reconstructed vector are exactly the reconstructed
selected full frame. -/
theorem sourceFullFrameGauge_reconstructVector_selected
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0)
    (y : S.slice × (sourceComplementIndex ι → Fin (d + 1) → ℂ)) :
    sourceFullFrameMatrix d n ι
        (sourceFullFrameGauge_reconstructVector d n ι M0 S y) =
      sourceFullFrameGauge_reconstructFrame d n ι M0 S y := by
  ext a μ
  have hmem : ι a ∈ Set.range ι := ⟨a, rfl⟩
  have hidx : sourceSelectedIndexOfMem ι hmem = a := by
    apply ι.injective
    exact sourceSelectedIndexOfMem_spec ι hmem
  simp [sourceFullFrameMatrix, sourceFullFrameGauge_reconstructVector,
    hmem, hidx]

/-- The free mixed rows are recovered as the Minkowski pairings with the
selected reconstructed frame. -/
theorem sourceFullFrameGauge_reconstructVector_mixedGram
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0)
    (y : S.slice × (sourceComplementIndex ι → Fin (d + 1) → ℂ))
    (hA_unit :
      IsUnit
        (Matrix.of
          (sourceFullFrameGram d
            (sourceFullFrameGauge_reconstructFrame d n ι M0 S y))).det)
    (k : sourceComplementIndex ι)
    (a : Fin (d + 1)) :
    sourceComplexMinkowskiInner d
        (sourceFullFrameGauge_reconstructVector d n ι M0 S y k.1)
        (sourceFullFrameGauge_reconstructVector d n ι M0 S y (ι a)) =
      y.2 k a := by
  let M := sourceFullFrameGauge_reconstructFrame d n ι M0 S y
  let z := sourceFullFrameGauge_reconstructVector d n ι M0 S y
  let A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    Matrix.of (sourceFullFrameGram d M)
  let coeff : Fin (d + 1) → ℂ :=
    fun b => ∑ c : Fin (d + 1), y.2 k c * A⁻¹ c b
  have hk_not : k.1 ∉ Set.range ι := k.2
  have hz_k :
      z k.1 = fun μ => ∑ b : Fin (d + 1), coeff b * M b μ := by
    ext μ
    simp [z, sourceFullFrameGauge_reconstructVector, hk_not, coeff, M, A]
  have hz_sel : z (ι a) = M a := by
    have hsel := sourceFullFrameGauge_reconstructVector_selected d n ι M0 S y
    ext μ
    exact congrFun (congrFun hsel a) μ
  have hinner :
      sourceComplexMinkowskiInner d
          (fun μ => ∑ b : Fin (d + 1), coeff b * M b μ) (M a) =
        ∑ b : Fin (d + 1), coeff b * A b a := by
    have hsum :
        (fun μ => ∑ b : Fin (d + 1), coeff b * M b μ) =
          ∑ b : Fin (d + 1), coeff b • M b := by
      ext μ
      simp [Pi.smul_apply, smul_eq_mul]
    rw [hsum]
    rw [sourceComplexMinkowskiInner_sum_smul_left]
    apply Finset.sum_congr rfl
    intro b _
    simp [A, sourceFullFrameGram, sourceComplexMinkowskiInner]
  have hrow : ∑ b : Fin (d + 1), coeff b * A b a = y.2 k a := by
    let row : Matrix (Fin 1) (Fin (d + 1)) ℂ := fun _ b => y.2 k b
    have hcancel : row * A⁻¹ * A = row :=
      Matrix.nonsing_inv_mul_cancel_right (A := A) row hA_unit
    have happ := congrFun (congrFun hcancel (0 : Fin 1)) a
    have happ' :
        (∑ b : Fin (d + 1),
            (∑ c : Fin (d + 1), row (0 : Fin 1) c * A⁻¹ c b) * A b a) =
          row (0 : Fin 1) a := by
      simpa only [Matrix.mul_apply] using happ
    simpa only [coeff, row] using happ'
  calc
    sourceComplexMinkowskiInner d (z k.1) (z (ι a)) =
        sourceComplexMinkowskiInner d
          (fun μ => ∑ b : Fin (d + 1), coeff b * M b μ) (M a) := by
      rw [hz_k, hz_sel]
    _ = ∑ b : Fin (d + 1), coeff b * A b a := hinner
    _ = y.2 k a := hrow

/-- Selected-selected reconstructed source Gram entries are the selected
full-frame Gram entries. -/
theorem sourceFullFrameGauge_reconstructVector_selectedSelectedGram
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0)
    (y : S.slice × (sourceComplementIndex ι → Fin (d + 1) → ℂ))
    (a b : Fin (d + 1)) :
    sourceMinkowskiGram d n
        (sourceFullFrameGauge_reconstructVector d n ι M0 S y) (ι a) (ι b) =
      sourceFullFrameGram d
        (sourceFullFrameGauge_reconstructFrame d n ι M0 S y) a b := by
  rw [sourceMinkowskiGram_apply_eq_complexInner]
  have hsel := sourceFullFrameGauge_reconstructVector_selected d n ι M0 S y
  have ha :
      sourceFullFrameGauge_reconstructVector d n ι M0 S y (ι a) =
        sourceFullFrameGauge_reconstructFrame d n ι M0 S y a := by
    ext μ
    exact congrFun (congrFun hsel a) μ
  have hb :
      sourceFullFrameGauge_reconstructVector d n ι M0 S y (ι b) =
        sourceFullFrameGauge_reconstructFrame d n ι M0 S y b := by
    ext μ
    exact congrFun (congrFun hsel b) μ
  rw [ha, hb]
  rfl

/-- Mixed reconstructed source Gram entries with the unselected label on the
left are the free mixed row. -/
theorem sourceFullFrameGauge_reconstructVector_mixedSourceGram_left
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0)
    (y : S.slice × (sourceComplementIndex ι → Fin (d + 1) → ℂ))
    (hA_unit :
      IsUnit
        (Matrix.of
          (sourceFullFrameGram d
            (sourceFullFrameGauge_reconstructFrame d n ι M0 S y))).det)
    (k : sourceComplementIndex ι)
    (a : Fin (d + 1)) :
    sourceMinkowskiGram d n
        (sourceFullFrameGauge_reconstructVector d n ι M0 S y) k.1 (ι a) =
      y.2 k a := by
  rw [sourceMinkowskiGram_apply_eq_complexInner]
  exact
    sourceFullFrameGauge_reconstructVector_mixedGram
      d n ι M0 S y hA_unit k a

/-- Mixed reconstructed source Gram entries with the selected label on the
left are the free mixed row. -/
theorem sourceFullFrameGauge_reconstructVector_mixedSourceGram_right
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0)
    (y : S.slice × (sourceComplementIndex ι → Fin (d + 1) → ℂ))
    (hA_unit :
      IsUnit
        (Matrix.of
          (sourceFullFrameGram d
            (sourceFullFrameGauge_reconstructFrame d n ι M0 S y))).det)
    (k : sourceComplementIndex ι)
    (a : Fin (d + 1)) :
    sourceMinkowskiGram d n
        (sourceFullFrameGauge_reconstructVector d n ι M0 S y) (ι a) k.1 =
      y.2 k a := by
  rw [sourceMinkowskiGram_apply_eq_complexInner]
  rw [sourceComplexMinkowskiInner_comm]
  exact
    sourceFullFrameGauge_reconstructVector_mixedGram
      d n ι M0 S y hA_unit k a

/-- Selected labels have the corresponding identity coefficient row. -/
theorem sourceFullFrameGauge_reconstructCoeff_selected
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0)
    (y : S.slice × (sourceComplementIndex ι → Fin (d + 1) → ℂ))
    (a b : Fin (d + 1)) :
    sourceFullFrameGauge_reconstructCoeff d n ι M0 S y (ι a) b =
      if b = a then 1 else 0 := by
  have hmem : ι a ∈ Set.range ι := ⟨a, rfl⟩
  have hidx : sourceSelectedIndexOfMem ι hmem = a := by
    apply ι.injective
    exact sourceSelectedIndexOfMem_spec ι hmem
  simp [sourceFullFrameGauge_reconstructCoeff, hmem, hidx]

/-- Every reconstructed vector is the coefficient row times the selected
reconstructed frame. -/
theorem sourceFullFrameGauge_reconstructVector_eq_sum_coeff_frame
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0)
    (y : S.slice × (sourceComplementIndex ι → Fin (d + 1) → ℂ))
    (j : Fin n) :
    sourceFullFrameGauge_reconstructVector d n ι M0 S y j =
      ∑ b : Fin (d + 1),
        sourceFullFrameGauge_reconstructCoeff d n ι M0 S y j b •
          sourceFullFrameGauge_reconstructFrame d n ι M0 S y b := by
  let M := sourceFullFrameGauge_reconstructFrame d n ι M0 S y
  let z := sourceFullFrameGauge_reconstructVector d n ι M0 S y
  let coeff := sourceFullFrameGauge_reconstructCoeff d n ι M0 S y
  by_cases hj : j ∈ Set.range ι
  · let a := sourceSelectedIndexOfMem ι hj
    have hz : z j = M a := by
      ext μ
      simp [z, M, sourceFullFrameGauge_reconstructVector, hj, a]
    have hcoeff : coeff j = fun b => if b = a then 1 else 0 := by
      funext b
      simp [coeff, sourceFullFrameGauge_reconstructCoeff, hj, a]
    have hsum :
        (∑ b : Fin (d + 1), (if b = a then (1 : ℂ) else 0) • M b) =
          M a := by
      simp
    calc
      sourceFullFrameGauge_reconstructVector d n ι M0 S y j = M a := hz
      _ = ∑ b : Fin (d + 1), coeff j b • M b := by
        rw [hcoeff, hsum]
  · ext μ
    simp [sourceFullFrameGauge_reconstructVector,
      sourceFullFrameGauge_reconstructCoeff, hj, Pi.smul_apply, smul_eq_mul]

/-- The reconstructed Gram of two source vectors is the coefficient Gram
against the selected reconstructed full-frame Gram matrix. -/
theorem sourceFullFrameGauge_reconstructVector_gram_eq_coeff_gram
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0)
    (y : S.slice × (sourceComplementIndex ι → Fin (d + 1) → ℂ))
    (i j : Fin n) :
    sourceComplexMinkowskiInner d
        (sourceFullFrameGauge_reconstructVector d n ι M0 S y i)
        (sourceFullFrameGauge_reconstructVector d n ι M0 S y j) =
      ∑ a : Fin (d + 1), ∑ b : Fin (d + 1),
        sourceFullFrameGauge_reconstructCoeff d n ι M0 S y i a *
          sourceFullFrameGauge_reconstructCoeff d n ι M0 S y j b *
          Matrix.of
            (sourceFullFrameGram d
              (sourceFullFrameGauge_reconstructFrame d n ι M0 S y)) a b := by
  let M := sourceFullFrameGauge_reconstructFrame d n ι M0 S y
  let z := sourceFullFrameGauge_reconstructVector d n ι M0 S y
  let coeff := sourceFullFrameGauge_reconstructCoeff d n ι M0 S y
  let A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    Matrix.of (sourceFullFrameGram d M)
  have hi : z i = ∑ a : Fin (d + 1), coeff i a • M a :=
    sourceFullFrameGauge_reconstructVector_eq_sum_coeff_frame d n ι M0 S y i
  have hj : z j = ∑ b : Fin (d + 1), coeff j b • M b :=
    sourceFullFrameGauge_reconstructVector_eq_sum_coeff_frame d n ι M0 S y j
  calc
    sourceComplexMinkowskiInner d (z i) (z j) =
        sourceComplexMinkowskiInner d
          (∑ a : Fin (d + 1), coeff i a • M a)
          (∑ b : Fin (d + 1), coeff j b • M b) := by
      rw [hi, hj]
    _ = ∑ a : Fin (d + 1),
          coeff i a *
            sourceComplexMinkowskiInner d (M a)
              (∑ b : Fin (d + 1), coeff j b • M b) := by
      rw [sourceComplexMinkowskiInner_sum_smul_left]
    _ = ∑ a : Fin (d + 1),
          coeff i a *
            (∑ b : Fin (d + 1),
              coeff j b * sourceComplexMinkowskiInner d (M a) (M b)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [sourceComplexMinkowskiInner_sum_smul_right]
    _ = ∑ a : Fin (d + 1), ∑ b : Fin (d + 1),
          coeff i a * coeff j b * A a b := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      simp [A, sourceFullFrameGram, sourceComplexMinkowskiInner, mul_assoc]

/-- A selected full-frame matrix of the reconstructed source tuple is the
coefficient matrix times the reconstructed frame. -/
theorem sourceFullFrameGauge_reconstructMatrix_eq_coeff_mul
    (d n : ℕ)
    (ι κ : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0)
    (y : S.slice × (sourceComplementIndex ι → Fin (d + 1) → ℂ)) :
    sourceFullFrameMatrix d n κ
        (sourceFullFrameGauge_reconstructVector d n ι M0 S y) =
      Matrix.of
        (fun a b =>
          sourceFullFrameGauge_reconstructCoeff d n ι M0 S y (κ a) b) *
        sourceFullFrameGauge_reconstructFrame d n ι M0 S y := by
  ext a μ
  have hvec :=
    congrFun
      (sourceFullFrameGauge_reconstructVector_eq_sum_coeff_frame
        d n ι M0 S y (κ a)) μ
  simpa [sourceFullFrameMatrix, Matrix.mul_apply, Pi.smul_apply,
    smul_eq_mul] using hvec

/-- Determinants of reconstructed selected frames factor through the
coefficient matrix. -/
theorem sourceFullFrameGauge_reconstructDet_eq_coeff_det_mul
    (d n : ℕ)
    (ι κ : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0)
    (y : S.slice × (sourceComplementIndex ι → Fin (d + 1) → ℂ)) :
    sourceFullFrameDet d n κ
        (sourceFullFrameGauge_reconstructVector d n ι M0 S y) =
      (Matrix.of
        (fun a b =>
          sourceFullFrameGauge_reconstructCoeff d n ι M0 S y (κ a) b)).det *
        (sourceFullFrameGauge_reconstructFrame d n ι M0 S y).det := by
  rw [sourceFullFrameDet]
  rw [sourceFullFrameGauge_reconstructMatrix_eq_coeff_mul]
  rw [Matrix.det_mul]

/-- If the reconstructed frame and mixed rows are taken from a realized source
tuple, the explicit reconstruction recovers that tuple. -/
theorem sourceFullFrameGauge_reconstructVector_eq_of_frame_eq_mixedRows_eq
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0)
    (y : S.slice × (sourceComplementIndex ι → Fin (d + 1) → ℂ))
    (z : Fin n → Fin (d + 1) → ℂ)
    (hframe :
      sourceFullFrameGauge_reconstructFrame d n ι M0 S y =
        sourceFullFrameMatrix d n ι z)
    (hmixed :
      y.2 =
        sourceSelectedMixedRows d n ι (sourceOrientedMinkowskiInvariant d n z))
    (hdet : (sourceOrientedMinkowskiInvariant d n z).det ι ≠ 0) :
    sourceFullFrameGauge_reconstructVector d n ι M0 S y = z := by
  let G := sourceOrientedMinkowskiInvariant d n z
  let M := sourceFullFrameMatrix d n ι z
  ext j μ
  by_cases hj : j ∈ Set.range ι
  · let a := sourceSelectedIndexOfMem ι hj
    have hja : ι a = j := sourceSelectedIndexOfMem_spec ι hj
    have hrec :
        sourceFullFrameGauge_reconstructVector d n ι M0 S y j =
          sourceFullFrameGauge_reconstructFrame d n ι M0 S y a := by
      ext ν
      simp [sourceFullFrameGauge_reconstructVector, hj, a]
    calc
      sourceFullFrameGauge_reconstructVector d n ι M0 S y j μ =
          sourceFullFrameGauge_reconstructFrame d n ι M0 S y a μ := by
        exact congrFun hrec μ
      _ = M a μ := by
        rw [hframe]
      _ = z j μ := by
        rw [← hja]
        rfl
  · have htarget :=
      congrFun
        (sourceSelectedFrameCoeff_vector_expansion_of_invariant
          d n ι z hdet j) μ
    have hAeq :
        Matrix.of
            (sourceFullFrameGram d
              (sourceFullFrameGauge_reconstructFrame d n ι M0 S y)) =
          sourceSelectedFrameGramMatrix d n ι G := by
      rw [hframe]
      ext a b
      simp [G, sourceSelectedFrameGramMatrix, sourceOrientedMinkowskiInvariant,
        SourceOrientedGramData.gram, sourceFullFrameGram_sourceFullFrameMatrix]
    have hAinv :
        (Matrix.of (fun a b => sourceMinkowskiGram d n z (ι a) (ι b)))⁻¹ =
          (sourceSelectedFrameGramMatrix d n ι G)⁻¹ := by
      congr 1
    have hcoeff :
        sourceFullFrameGauge_reconstructCoeff d n ι M0 S y j =
          sourceSelectedFrameCoeff d n ι G j := by
      funext a
      simp [sourceFullFrameGauge_reconstructCoeff, sourceSelectedFrameCoeff,
        sourceSelectedMixedRows, hj, G, hframe, hmixed,
        sourceOrientedMinkowskiInvariant, SourceOrientedGramData.gram,
        sourceFullFrameGram_sourceFullFrameMatrix]
      rw [hAinv]
      simp [G, sourceOrientedMinkowskiInvariant]
    calc
      sourceFullFrameGauge_reconstructVector d n ι M0 S y j μ =
          (∑ a : Fin (d + 1),
            sourceFullFrameGauge_reconstructCoeff d n ι M0 S y j a •
              sourceFullFrameGauge_reconstructFrame d n ι M0 S y a) μ := by
        exact
          congrFun
            (sourceFullFrameGauge_reconstructVector_eq_sum_coeff_frame
              d n ι M0 S y j) μ
      _ = (∑ a : Fin (d + 1),
            sourceSelectedFrameCoeff d n ι G j a • M a) μ := by
        apply congrArg (fun v : Fin (d + 1) → ℂ => v μ)
        apply Finset.sum_congr rfl
        intro a _
        rw [hcoeff, hframe]
      _ = z j μ := by
        simpa [G, M] using htarget.symm

/-- Invariant form of the explicit reconstruction recovery theorem. -/
theorem sourceFullFrameGauge_reconstructInvariant_eq_of_frame_eq_mixedRows_eq
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0)
    (y : S.slice × (sourceComplementIndex ι → Fin (d + 1) → ℂ))
    (z : Fin n → Fin (d + 1) → ℂ)
    (hframe :
      sourceFullFrameGauge_reconstructFrame d n ι M0 S y =
        sourceFullFrameMatrix d n ι z)
    (hmixed :
      y.2 =
        sourceSelectedMixedRows d n ι (sourceOrientedMinkowskiInvariant d n z))
    (hdet : (sourceOrientedMinkowskiInvariant d n z).det ι ≠ 0) :
    sourceOrientedMinkowskiInvariant d n
        (sourceFullFrameGauge_reconstructVector d n ι M0 S y) =
      sourceOrientedMinkowskiInvariant d n z := by
  rw [sourceFullFrameGauge_reconstructVector_eq_of_frame_eq_mixedRows_eq
    d n ι M0 S y z hframe hmixed hdet]

/-- Model coordinates for the selected full-frame max-rank chart: a gauge-slice
parameter for the selected frame, plus the free mixed Gram rows. -/
abbrev sourceFullFrameMaxRankChartModel
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0) :=
  S.slice × (sourceComplementIndex ι → Fin (d + 1) → ℂ)

/-- The explicit inverse map attached to full-frame max-rank chart coordinates. -/
noncomputable def sourceFullFrameGauge_reconstructInvariant
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0)
    (y : sourceFullFrameMaxRankChartModel d n ι M0 S) :
    SourceOrientedGramData d n :=
  sourceOrientedMinkowskiInvariant d n
    (sourceFullFrameGauge_reconstructVector d n ι M0 S y)

@[simp]
theorem sourceFullFrameGauge_reconstructInvariant_eq
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0)
    (y : sourceFullFrameMaxRankChartModel d n ι M0 S) :
    sourceFullFrameGauge_reconstructInvariant d n ι M0 S y =
      sourceOrientedMinkowskiInvariant d n
        (sourceFullFrameGauge_reconstructVector d n ι M0 S y) :=
  rfl

/-- Reconstructed invariants are, tautologically, points of the oriented source
Gram variety. -/
theorem sourceFullFrameGauge_reconstructInvariant_mem_variety
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0)
    (y : sourceFullFrameMaxRankChartModel d n ι M0 S) :
    sourceFullFrameGauge_reconstructInvariant d n ι M0 S y ∈
      sourceOrientedGramVariety d n :=
  ⟨sourceFullFrameGauge_reconstructVector d n ι M0 S y, rfl⟩

/-- The determinant of a finite complex square matrix is differentiable. -/
@[fun_prop]
theorem differentiable_matrix_det
    {D : Type} [Fintype D] [DecidableEq D] :
    Differentiable ℂ (fun A : Matrix D D ℂ => A.det) := by
  intro A
  exact (matrix_det_hasFDerivAt_expansion A).differentiableAt

/-- The adjugate entries are determinants of matrices whose entries depend
linearly on the original matrix, hence form a differentiable matrix-valued
map. -/
@[fun_prop]
theorem differentiable_matrix_adjugate
    {D : Type} [Fintype D] [DecidableEq D] :
    Differentiable ℂ (fun A : Matrix D D ℂ => A.adjugate) := by
  change Differentiable ℂ (fun A : Matrix D D ℂ => fun i j => A.adjugate i j)
  exact
    differentiable_pi.mpr
      (fun i =>
        differentiable_pi.mpr
          (fun j => by
            have hupdate :
                Differentiable ℂ
                  (fun A : Matrix D D ℂ => A.updateRow j (Pi.single i 1)) := by
              change
                Differentiable ℂ
                  (fun A : Matrix D D ℂ =>
                    fun r c => A.updateRow j (Pi.single i 1) r c)
              exact
                differentiable_pi.mpr
                  (fun r =>
                    differentiable_pi.mpr
                      (fun c => by
                        by_cases hr : r = j
                        · subst r
                          simp [Matrix.updateRow_self]
                        · let evalRow :
                              Matrix D D ℂ →L[ℂ] (D → ℂ) :=
                            ContinuousLinearMap.proj (R := ℂ)
                              (φ := fun _ : D => D → ℂ) r
                          let evalEntry : (D → ℂ) →L[ℂ] ℂ :=
                            ContinuousLinearMap.proj (R := ℂ)
                              (φ := fun _ : D => ℂ) c
                          let eval : Matrix D D ℂ →L[ℂ] ℂ :=
                            evalEntry.comp evalRow
                          simpa [eval, evalRow, evalEntry, Matrix.updateRow_ne hr] using
                            eval.differentiable))
            simpa [Matrix.adjugate_apply] using
              (differentiable_matrix_det (D := D)).comp hupdate))

/-- Matrix inverse is differentiable on the determinant-nonzero locus. -/
theorem differentiableOn_matrix_inv_of_det_ne_zero
    {D : Type} [Fintype D] [DecidableEq D] :
    DifferentiableOn ℂ (fun A : Matrix D D ℂ => A⁻¹)
      {A : Matrix D D ℂ | A.det ≠ 0} := by
  intro A hA
  change
    DifferentiableWithinAt ℂ
      (fun A : Matrix D D ℂ => Ring.inverse A.det • A.adjugate)
      {A : Matrix D D ℂ | A.det ≠ 0} A
  have hdet : DifferentiableAt ℂ (fun A : Matrix D D ℂ => A.det) A :=
    (matrix_det_hasFDerivAt_expansion A).differentiableAt
  have hinv :
      DifferentiableWithinAt ℂ
        (fun A : Matrix D D ℂ => Ring.inverse A.det)
        {A : Matrix D D ℂ | A.det ≠ 0} A := by
    simpa [Ring.inverse_eq_inv] using (hdet.inv hA).differentiableWithinAt
  have hadj : DifferentiableAt ℂ (fun A : Matrix D D ℂ => A.adjugate) A :=
    (differentiable_matrix_adjugate (D := D)).differentiableAt
  exact hinv.smul hadj.differentiableWithinAt

/- The explicit reconstructed source-vector map is differentiable on the model
determinant-nonzero locus. -/
set_option maxHeartbeats 800000 in
theorem differentiableOn_sourceFullFrameGauge_reconstructVector_on_modelDetNonzero
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0) :
    DifferentiableOn ℂ (sourceFullFrameGauge_reconstructVector d n ι M0 S)
      (sourceFullFrameGaugeModelDetNonzero d n ι M0 S) := by
  intro y hy
  exact
    differentiableWithinAt_pi.mpr
      (fun j =>
        differentiableWithinAt_pi.mpr
          (fun μ => by
            unfold sourceFullFrameGauge_reconstructVector sourceFullFrameGaugeModelDetNonzero
            by_cases hj : j ∈ Set.range ι
            · simp [hj]
              let evalRow :
                  Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ →L[ℂ]
                    (Fin (d + 1) → ℂ) :=
                ContinuousLinearMap.proj (R := ℂ)
                  (φ := fun _ : Fin (d + 1) => Fin (d + 1) → ℂ)
                  (sourceSelectedIndexOfMem ι hj)
              let evalEntry : (Fin (d + 1) → ℂ) →L[ℂ] ℂ :=
                ContinuousLinearMap.proj (R := ℂ)
                  (φ := fun _ : Fin (d + 1) => ℂ) μ
              let eval :
                  Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ →L[ℂ] ℂ :=
                evalEntry.comp evalRow
              have hfst :
                  Differentiable ℂ
                    (fun y :
                        S.slice × (sourceComplementIndex ι → Fin (d + 1) → ℂ) =>
                      (y.1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)) := by
                exact
                  S.slice.subtypeL.differentiable.comp
                    (ContinuousLinearMap.fst ℂ S.slice
                      (sourceComplementIndex ι → Fin (d + 1) → ℂ)).differentiable
              change
                DifferentiableWithinAt ℂ
                  (fun y =>
                    eval
                      (y.1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ))
                  (sourceFullFrameGaugeModelDetNonzero d n ι M0 S) y
              exact
                eval.differentiableAt.comp_differentiableWithinAt y
                  hfst.differentiableAt.differentiableWithinAt
            · simp [hj]
              let k : sourceComplementIndex ι := ⟨j, hj⟩
              let Amap :
                  sourceFullFrameMaxRankChartModel d n ι M0 S →
                    Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
                fun y =>
                  Matrix.of
                    (sourceFullFrameGram d
                      (sourceFullFrameGauge_reconstructFrame d n ι M0 S y))
              have hA : Differentiable ℂ Amap := by
                change
                  Differentiable ℂ
                    (fun y : sourceFullFrameMaxRankChartModel d n ι M0 S =>
                      fun a b =>
                        sourceFullFrameGram d
                          (sourceFullFrameGauge_reconstructFrame d n ι M0 S y) a b)
                have hM :
                    Differentiable ℂ
                      (sourceFullFrameGauge_reconstructFrame d n ι M0 S) :=
                  differentiable_sourceFullFrameGauge_reconstructFrame d n ι M0 S
                have hMEntry :
                    ∀ a μ : Fin (d + 1),
                      Differentiable ℂ
                        (fun y : sourceFullFrameMaxRankChartModel d n ι M0 S =>
                          sourceFullFrameGauge_reconstructFrame d n ι M0 S y a μ) := by
                  intro a μ
                  let evalRow :
                      Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ →L[ℂ]
                        (Fin (d + 1) → ℂ) :=
                    ContinuousLinearMap.proj (R := ℂ)
                      (φ := fun _ : Fin (d + 1) => Fin (d + 1) → ℂ) a
                  let evalEntry : (Fin (d + 1) → ℂ) →L[ℂ] ℂ :=
                    ContinuousLinearMap.proj (R := ℂ)
                      (φ := fun _ : Fin (d + 1) => ℂ) μ
                  let eval :
                      Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ →L[ℂ] ℂ :=
                    evalEntry.comp evalRow
                  change
                    Differentiable ℂ
                      (fun y : sourceFullFrameMaxRankChartModel d n ι M0 S =>
                        eval (sourceFullFrameGauge_reconstructFrame d n ι M0 S y))
                  exact eval.differentiable.comp hM
                exact
                  differentiable_pi.mpr
                    (fun a =>
                      differentiable_pi.mpr
                        (fun b => by
                          unfold sourceFullFrameGram
                          refine Differentiable.fun_sum ?_
                          intro μ _hμ
                          exact
                            ((differentiable_const
                                (c := (MinkowskiSpace.metricSignature d μ : ℂ))).mul
                              (hMEntry a μ)).mul (hMEntry b μ)))
              have hmaps :
                  Set.MapsTo Amap
                    (sourceFullFrameGaugeModelDetNonzero d n ι M0 S)
                    {A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ |
                      A.det ≠ 0} := by
                intro y hy
                exact
                  (sourceFullFrameGram_det_isUnit_of_frame_det_isUnit d
                    (isUnit_iff_ne_zero.mpr hy)).ne_zero
              have hAinv :
                  DifferentiableOn ℂ (fun y => (Amap y)⁻¹)
                    (sourceFullFrameGaugeModelDetNonzero d n ι M0 S) :=
                (differentiableOn_matrix_inv_of_det_ne_zero
                  (D := Fin (d + 1))).comp hA.differentiableOn hmaps
              have hM :
                  Differentiable ℂ
                    (sourceFullFrameGauge_reconstructFrame d n ι M0 S) :=
                differentiable_sourceFullFrameGauge_reconstructFrame d n ι M0 S
              have hAinvEntry :
                  ∀ a b : Fin (d + 1),
                    DifferentiableWithinAt ℂ
                      (fun y : sourceFullFrameMaxRankChartModel d n ι M0 S =>
                        (Amap y)⁻¹ a b)
                      (sourceFullFrameGaugeModelDetNonzero d n ι M0 S) y := by
                intro a b
                let evalRow :
                    Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ →L[ℂ]
                      (Fin (d + 1) → ℂ) :=
                  ContinuousLinearMap.proj (R := ℂ)
                    (φ := fun _ : Fin (d + 1) => Fin (d + 1) → ℂ) a
                let evalEntry : (Fin (d + 1) → ℂ) →L[ℂ] ℂ :=
                  ContinuousLinearMap.proj (R := ℂ)
                    (φ := fun _ : Fin (d + 1) => ℂ) b
                let eval :
                    Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ →L[ℂ] ℂ :=
                  evalEntry.comp evalRow
                change
                  DifferentiableWithinAt ℂ
                    (fun y : sourceFullFrameMaxRankChartModel d n ι M0 S =>
                      eval ((Amap y)⁻¹))
                    (sourceFullFrameGaugeModelDetNonzero d n ι M0 S) y
                exact
                  eval.differentiableAt.comp_differentiableWithinAt y
                    (hAinv y hy)
              have hMEntry :
                  ∀ b : Fin (d + 1),
                    DifferentiableWithinAt ℂ
                      (fun y : sourceFullFrameMaxRankChartModel d n ι M0 S =>
                        sourceFullFrameGauge_reconstructFrame d n ι M0 S y b μ)
                      (sourceFullFrameGaugeModelDetNonzero d n ι M0 S) y := by
                intro b
                let evalRow :
                    Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ →L[ℂ]
                      (Fin (d + 1) → ℂ) :=
                  ContinuousLinearMap.proj (R := ℂ)
                    (φ := fun _ : Fin (d + 1) => Fin (d + 1) → ℂ) b
                let evalEntry : (Fin (d + 1) → ℂ) →L[ℂ] ℂ :=
                  ContinuousLinearMap.proj (R := ℂ)
                    (φ := fun _ : Fin (d + 1) => ℂ) μ
                let eval :
                    Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ →L[ℂ] ℂ :=
                  evalEntry.comp evalRow
                change
                  DifferentiableWithinAt ℂ
                    (fun y : sourceFullFrameMaxRankChartModel d n ι M0 S =>
                      eval (sourceFullFrameGauge_reconstructFrame d n ι M0 S y))
                    (sourceFullFrameGaugeModelDetNonzero d n ι M0 S) y
                exact
                  eval.differentiableAt.comp_differentiableWithinAt y
                    hM.differentiableAt.differentiableWithinAt
              have hY2 :
                  ∀ a : Fin (d + 1),
                    DifferentiableWithinAt ℂ
                      (fun y : sourceFullFrameMaxRankChartModel d n ι M0 S =>
                        y.2 k a)
                      (sourceFullFrameGaugeModelDetNonzero d n ι M0 S) y := by
                intro a
                fun_prop
              change
                DifferentiableWithinAt ℂ
                  (fun y : sourceFullFrameMaxRankChartModel d n ι M0 S =>
                    ∑ b : Fin (d + 1),
                      (∑ a : Fin (d + 1), y.2 k a * (Amap y)⁻¹ a b) *
                        sourceFullFrameGauge_reconstructFrame d n ι M0 S y b μ)
                  (sourceFullFrameGaugeModelDetNonzero d n ι M0 S) y
              refine DifferentiableWithinAt.fun_sum ?_
              intro b _hb
              have hcoeff :
                  DifferentiableWithinAt ℂ
                    (fun y : sourceFullFrameMaxRankChartModel d n ι M0 S =>
                      ∑ a : Fin (d + 1), y.2 k a * (Amap y)⁻¹ a b)
                    (sourceFullFrameGaugeModelDetNonzero d n ι M0 S) y := by
                refine DifferentiableWithinAt.fun_sum ?_
                intro a _ha
                exact (hY2 a).mul (hAinvEntry a b)
              exact hcoeff.mul (hMEntry b)))

/-- The explicit reconstructed oriented invariant is differentiable on the
model determinant-nonzero locus. -/
theorem differentiableOn_sourceFullFrameGauge_reconstructInvariant_on_modelDetNonzero
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0) :
    DifferentiableOn ℂ (sourceFullFrameGauge_reconstructInvariant d n ι M0 S)
      (sourceFullFrameGaugeModelDetNonzero d n ι M0 S) := by
  have hz :=
    differentiableOn_sourceFullFrameGauge_reconstructVector_on_modelDetNonzero
      d n ι M0 S
  unfold sourceFullFrameGauge_reconstructInvariant sourceOrientedMinkowskiInvariant
  have hgram :
      DifferentiableOn ℂ
        (fun y =>
          sourceMinkowskiGram d n
            (sourceFullFrameGauge_reconstructVector d n ι M0 S y))
        (sourceFullFrameGaugeModelDetNonzero d n ι M0 S) := by
    exact
      differentiableOn_pi.mpr
        (fun i =>
          differentiableOn_pi.mpr
            (fun j => by
              have hcoord :
                  Differentiable ℂ
                    (fun z : Fin n → Fin (d + 1) → ℂ =>
                      sourceMinkowskiGram d n z i j) := by
                unfold sourceMinkowskiGram
                fun_prop
              exact hcoord.comp_differentiableOn hz))
  have hdet :
      DifferentiableOn ℂ
        (fun y =>
          fun κ =>
            sourceFullFrameDet d n κ
              (sourceFullFrameGauge_reconstructVector d n ι M0 S y))
        (sourceFullFrameGaugeModelDetNonzero d n ι M0 S) := by
    exact
      differentiableOn_pi.mpr
        (fun κ => by
          have hdetκ :
              Differentiable ℂ
                (fun z : Fin n → Fin (d + 1) → ℂ =>
                  sourceFullFrameDet d n κ z) := by
            have hmat : Differentiable ℂ (sourceFullFrameMatrix d n κ) := by
              unfold sourceFullFrameMatrix
              fun_prop
            simpa [sourceFullFrameDet] using
              (differentiable_matrix_det (D := Fin (d + 1))).comp hmat
          exact hdetκ.comp_differentiableOn hz)
  exact hgram.prodMk hdet

/-- The explicit reconstructed oriented invariant is continuous on the model
determinant-nonzero locus. -/
theorem continuousOn_sourceFullFrameGauge_reconstructInvariant_on_modelDetNonzero
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0) :
    ContinuousOn (sourceFullFrameGauge_reconstructInvariant d n ι M0 S)
      (sourceFullFrameGaugeModelDetNonzero d n ι M0 S) :=
  (differentiableOn_sourceFullFrameGauge_reconstructInvariant_on_modelDetNonzero
    d n ι M0 S).continuousOn

/-- The selected full-frame oriented coordinate of the reconstructed invariant
is exactly the oriented coordinate of the reconstructed selected frame. -/
theorem sourceFullFrameOrientedCoordOfSource_reconstructInvariant_eq
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0)
    (y : sourceFullFrameMaxRankChartModel d n ι M0 S) :
    sourceFullFrameOrientedCoordOfSource d n ι
        (sourceFullFrameGauge_reconstructInvariant d n ι M0 S y) =
      sourceFullFrameOrientedGramCoord d
        (sourceFullFrameGauge_reconstructFrame d n ι M0 S y) := by
  rw [sourceFullFrameGauge_reconstructInvariant_eq]
  rw [sourceFullFrameOrientedCoordOfSource_sourceOrientedMinkowskiInvariant]
  rw [sourceFullFrameGauge_reconstructVector_selected]

/-- The selected kernel coordinate of the reconstructed invariant is the
implicit kernel coordinate of the model slice point. -/
theorem sourceFullFrameSelectedKernelCoord_reconstructInvariant_eq
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0)
    (y : sourceFullFrameMaxRankChartModel d n ι M0 S) :
    sourceFullFrameSelectedKernelCoord d n ι hM0
        (sourceFullFrameGauge_reconstructInvariant_mem_variety d n ι M0 S y) =
      sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S y.1 := by
  let H : SourceOrientedGramData d n :=
    sourceFullFrameGauge_reconstructInvariant d n ι M0 S y
  have hH : H ∈ sourceOrientedGramVariety d n :=
    sourceFullFrameGauge_reconstructInvariant_mem_variety d n ι M0 S y
  have hcoord :
      sourceFullFrameSelectedSymmetricCoordOfSource d n ι hH =
        sourceFullFrameGaugeSliceMapSymmetric d M0 S y.1 := by
    apply Subtype.ext
    simpa [H, sourceFullFrameSelectedSymmetricCoordOfSource,
      sourceFullFrameGaugeSliceMapSymmetric] using
      sourceFullFrameOrientedCoordOfSource_reconstructInvariant_eq
        d n ι M0 S y
  calc
    sourceFullFrameSelectedKernelCoord d n ι hM0 hH =
        ((sourceFullFrameSymmetricEquation_implicitChart d M0 hM0)
          (sourceFullFrameSelectedSymmetricCoordOfSource d n ι hH)).2 := rfl
    _ =
        ((sourceFullFrameSymmetricEquation_implicitChart d M0 hM0)
          (sourceFullFrameGaugeSliceMapSymmetric d M0 S y.1)).2 := by
          rw [hcoord]
    _ = sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S y.1 := by
      rw [sourceFullFrameGaugeSliceMapSymmetric_implicitChart_eq_zero_kernelMap]

/-- Ambient selected-kernel readoff for a reconstructed invariant. -/
theorem sourceFullFrameSelectedKernelCoordAmbient_reconstructInvariant_eq
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0)
    (y : sourceFullFrameMaxRankChartModel d n ι M0 S) :
    sourceFullFrameSelectedKernelCoordAmbient d n ι hM0
        (sourceFullFrameGauge_reconstructInvariant d n ι M0 S y) =
      sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S y.1 := by
  have hH :=
    sourceFullFrameGauge_reconstructInvariant_mem_variety d n ι M0 S y
  rw [sourceFullFrameSelectedKernelCoordAmbient_eq_of_mem_variety
    d n ι hM0 hH]
  exact sourceFullFrameSelectedKernelCoord_reconstructInvariant_eq
    d n ι hM0 S y

/-- If a model coordinate uses the same selected kernel coordinate as a source
variety point, then the reconstructed invariant has the same selected
full-frame oriented coordinate as that source point. -/
theorem sourceFullFrameGauge_reconstructInvariant_selectedCoord_eq_of_kernel_eq
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n)
    (y : sourceFullFrameMaxRankChartModel d n ι M0 S)
    (hG_source :
      sourceFullFrameSelectedSymmetricCoordOfSource d n ι hG ∈
        (sourceFullFrameSymmetricEquation_implicitChart d M0 hM0).source)
    (hX_source :
      sourceFullFrameGaugeSliceMapSymmetric d M0 S y.1 ∈
        (sourceFullFrameSymmetricEquation_implicitChart d M0 hM0).source)
    (hkernel :
      sourceFullFrameSelectedKernelCoord d n ι hM0 hG =
        sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S y.1) :
    sourceFullFrameOrientedCoordOfSource d n ι
        (sourceFullFrameGauge_reconstructInvariant d n ι M0 S y) =
      sourceFullFrameOrientedCoordOfSource d n ι G := by
  calc
    sourceFullFrameOrientedCoordOfSource d n ι
        (sourceFullFrameGauge_reconstructInvariant d n ι M0 S y) =
        sourceFullFrameOrientedGramCoord d
          (sourceFullFrameGauge_reconstructFrame d n ι M0 S y) := by
      exact
        sourceFullFrameOrientedCoordOfSource_reconstructInvariant_eq
          d n ι M0 S y
    _ = sourceFullFrameGaugeSliceMap d M0 S y.1 := by
      rfl
    _ = sourceFullFrameOrientedCoordOfSource d n ι G := by
      exact
        (sourceFullFrameOrientedCoordOfSource_eq_gaugeSliceMap_of_kernel_eq
          d n ι hM0 S hG y.1 hG_source hX_source hkernel).symm

/-- The selected Gram matrix of the reconstructed invariant is the Gram matrix
of the reconstructed selected frame. -/
theorem sourceSelectedFrameGramMatrix_reconstructInvariant_eq
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0)
    (y : sourceFullFrameMaxRankChartModel d n ι M0 S) :
    sourceSelectedFrameGramMatrix d n ι
        (sourceFullFrameGauge_reconstructInvariant d n ι M0 S y) =
      Matrix.of
        (sourceFullFrameGram d
          (sourceFullFrameGauge_reconstructFrame d n ι M0 S y)) := by
  ext a b
  simpa [sourceSelectedFrameGramMatrix, sourceFullFrameGauge_reconstructInvariant,
    sourceOrientedMinkowskiInvariant, SourceOrientedGramData.gram] using
    sourceFullFrameGauge_reconstructVector_selectedSelectedGram
      d n ι M0 S y a b

/-- The selected determinant coordinate of the reconstructed invariant is the
determinant of the reconstructed selected frame. -/
theorem sourceFullFrameGauge_reconstructInvariant_selectedDet
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0)
    (y : sourceFullFrameMaxRankChartModel d n ι M0 S) :
    (sourceFullFrameGauge_reconstructInvariant d n ι M0 S y).det ι =
      (sourceFullFrameGauge_reconstructFrame d n ι M0 S y).det := by
  rw [sourceFullFrameGauge_reconstructInvariant_eq]
  change
    sourceFullFrameDet d n ι
        (sourceFullFrameGauge_reconstructVector d n ι M0 S y) =
      (sourceFullFrameGauge_reconstructFrame d n ι M0 S y).det
  rw [sourceFullFrameDet]
  rw [sourceFullFrameGauge_reconstructVector_selected]

/-- A nonzero reconstructed selected-frame determinant makes the selected Gram
matrix of the reconstructed invariant invertible. -/
theorem sourceSelectedFrameGramMatrix_reconstructInvariant_det_isUnit
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0)
    (y : sourceFullFrameMaxRankChartModel d n ι M0 S)
    (hdet :
      (sourceFullFrameGauge_reconstructFrame d n ι M0 S y).det ≠ 0) :
    IsUnit
      (sourceSelectedFrameGramMatrix d n ι
        (sourceFullFrameGauge_reconstructInvariant d n ι M0 S y)).det := by
  rw [sourceSelectedFrameGramMatrix_reconstructInvariant_eq]
  exact
    sourceFullFrameGram_det_isUnit_of_frame_det_isUnit d
      (isUnit_iff_ne_zero.mpr hdet)

/-- If the reconstructed selected Gram block is invertible, the mixed-row
coordinate of the reconstructed invariant is the free mixed-row coordinate. -/
theorem sourceSelectedMixedRows_reconstructInvariant_eq
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0)
    (y : sourceFullFrameMaxRankChartModel d n ι M0 S)
    (hA_unit :
      IsUnit
        (Matrix.of
          (sourceFullFrameGram d
            (sourceFullFrameGauge_reconstructFrame d n ι M0 S y))).det) :
    sourceSelectedMixedRows d n ι
        (sourceFullFrameGauge_reconstructInvariant d n ι M0 S y) =
      y.2 := by
  funext k a
  rw [sourceSelectedMixedRows_apply]
  simpa [sourceFullFrameGauge_reconstructInvariant,
    sourceOrientedMinkowskiInvariant, SourceOrientedGramData.gram] using
    sourceFullFrameGauge_reconstructVector_mixedSourceGram_left
      d n ι M0 S y hA_unit k a

/-- Determinant-nonzero form of the mixed-row readoff theorem. -/
theorem sourceSelectedMixedRows_reconstructInvariant_eq_of_frame_det_ne_zero
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0)
    (y : sourceFullFrameMaxRankChartModel d n ι M0 S)
    (hdet :
      (sourceFullFrameGauge_reconstructFrame d n ι M0 S y).det ≠ 0) :
    sourceSelectedMixedRows d n ι
        (sourceFullFrameGauge_reconstructInvariant d n ι M0 S y) =
      y.2 := by
  exact
    sourceSelectedMixedRows_reconstructInvariant_eq d n ι M0 S y
      (by
        rw [← sourceSelectedFrameGramMatrix_reconstructInvariant_eq
          d n ι M0 S y]
        exact
          sourceSelectedFrameGramMatrix_reconstructInvariant_det_isUnit
            d n ι M0 S y hdet)

/-- The selected full-frame coordinate and mixed rows determine all
selected-frame coefficients. -/
theorem sourceSelectedFrameCoeff_eq_of_selectedCoord_eq_mixedRows_eq
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {H G : SourceOrientedGramData d n}
    (hsel :
      sourceFullFrameOrientedCoordOfSource d n ι H =
        sourceFullFrameOrientedCoordOfSource d n ι G)
    (hmixed :
      sourceSelectedMixedRows d n ι H =
        sourceSelectedMixedRows d n ι G)
    (j : Fin n) :
    sourceSelectedFrameCoeff d n ι H j =
      sourceSelectedFrameCoeff d n ι G j := by
  funext b
  by_cases hj : j ∈ Set.range ι
  · simp [sourceSelectedFrameCoeff, hj]
  · have hA :
        sourceSelectedFrameGramMatrix d n ι H =
          sourceSelectedFrameGramMatrix d n ι G := by
      simpa [sourceSelectedFrameGramMatrix, sourceFullFrameOrientedCoordOfSource]
        using congrArg Prod.fst hsel
    have hmixed_j :
        sourceSelectedMixedRows d n ι H ⟨j, hj⟩ =
          sourceSelectedMixedRows d n ι G ⟨j, hj⟩ := by
      exact congrFun hmixed ⟨j, hj⟩
    have hrow :
        ∀ a : Fin (d + 1), H.gram j (ι a) = G.gram j (ι a) := by
      intro a
      exact congrFun hmixed_j a
    simp [sourceSelectedFrameCoeff, hj, hA, hrow]

/-- The selected full-frame coordinate and mixed rows determine the coefficient
Gram expression. -/
theorem sourceCoeffGramFromSelected_eq_of_selectedCoord_eq_mixedRows_eq
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {H G : SourceOrientedGramData d n}
    (hsel :
      sourceFullFrameOrientedCoordOfSource d n ι H =
        sourceFullFrameOrientedCoordOfSource d n ι G)
    (hmixed :
      sourceSelectedMixedRows d n ι H =
        sourceSelectedMixedRows d n ι G)
    (i j : Fin n) :
    sourceCoeffGramFromSelected d n ι H i j =
      sourceCoeffGramFromSelected d n ι G i j := by
  have hA :
      sourceSelectedFrameGramMatrix d n ι H =
        sourceSelectedFrameGramMatrix d n ι G := by
    simpa [sourceSelectedFrameGramMatrix, sourceFullFrameOrientedCoordOfSource]
      using congrArg Prod.fst hsel
  have hcoeff :=
    sourceSelectedFrameCoeff_eq_of_selectedCoord_eq_mixedRows_eq
      d n ι hsel hmixed
  have hgram :
      ∀ a b : Fin (d + 1), H.gram (ι a) (ι b) = G.gram (ι a) (ι b) := by
    intro a b
    exact congrFun (congrFun hA a) b
  simp [sourceCoeffGramFromSelected, hcoeff, hgram]

/-- On the determinant-nonzero selected sheet of the oriented source variety,
the selected full-frame coordinate together with the mixed rows determines the
entire oriented Gram datum. -/
theorem sourceOrientedGramData_eq_of_selectedCoord_eq_mixedRows_eq
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {H G : SourceOrientedGramData d n}
    (hH : H ∈ sourceOrientedGramVariety d n)
    (hG : G ∈ sourceOrientedGramVariety d n)
    (hdet : G.det ι ≠ 0)
    (hsel :
      sourceFullFrameOrientedCoordOfSource d n ι H =
        sourceFullFrameOrientedCoordOfSource d n ι G)
    (hmixed :
      sourceSelectedMixedRows d n ι H =
        sourceSelectedMixedRows d n ι G) :
    H = G := by
  have hdet_eq : H.det ι = G.det ι := by
    simpa [sourceFullFrameOrientedCoordOfSource] using congrArg Prod.snd hsel
  have hdetH : H.det ι ≠ 0 := by
    rw [hdet_eq]
    exact hdet
  have hcoeff :=
    sourceSelectedFrameCoeff_eq_of_selectedCoord_eq_mixedRows_eq
      d n ι hsel hmixed
  apply SourceOrientedGramData.ext
  · funext i j
    rw [sourceOrientedVariety_schurGram_eq_of_selectedDet_ne_zero
      d n ι hH hdetH i j]
    rw [sourceOrientedVariety_schurGram_eq_of_selectedDet_ne_zero
      d n ι hG hdet i j]
    exact
      sourceCoeffGramFromSelected_eq_of_selectedCoord_eq_mixedRows_eq
        d n ι hsel hmixed i j
  · funext κ
    have hdetHκ :=
      sourceOrientedVariety_det_eq_coeff_det_selected
        d n ι κ hH hdetH
    have hdetGκ :=
      sourceOrientedVariety_det_eq_coeff_det_selected
        d n ι κ hG hdet
    have hcoeffκ :
        Matrix.of
            (fun a b => sourceSelectedFrameCoeff d n ι H (κ a) b) =
          Matrix.of
            (fun a b => sourceSelectedFrameCoeff d n ι G (κ a) b) := by
      ext a b
      exact congrFun (hcoeff (κ a)) b
    calc
      H.det κ =
          (Matrix.of
            (fun a b => sourceSelectedFrameCoeff d n ι H (κ a) b)).det *
            H.det ι := by
        exact hdetHκ.symm
      _ = (Matrix.of
            (fun a b => sourceSelectedFrameCoeff d n ι G (κ a) b)).det *
            G.det ι := by
        rw [hcoeffκ, hdet_eq]
      _ = G.det κ := hdetGκ

/-- Variant of `sourceOrientedGramData_eq_of_selectedCoord_eq_mixedRows_eq`
for the explicit reconstructed invariant. -/
theorem sourceFullFrameGauge_reconstructInvariant_eq_of_selectedCoord_eq_mixedRows_eq
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0)
    (y : sourceFullFrameMaxRankChartModel d n ι M0 S)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n)
    (hdet : G.det ι ≠ 0)
    (hsel :
      sourceFullFrameOrientedCoordOfSource d n ι
          (sourceFullFrameGauge_reconstructInvariant d n ι M0 S y) =
        sourceFullFrameOrientedCoordOfSource d n ι G)
    (hmixed :
      sourceSelectedMixedRows d n ι
          (sourceFullFrameGauge_reconstructInvariant d n ι M0 S y) =
        sourceSelectedMixedRows d n ι G) :
    sourceFullFrameGauge_reconstructInvariant d n ι M0 S y = G := by
  exact
    sourceOrientedGramData_eq_of_selectedCoord_eq_mixedRows_eq
      d n ι
      (sourceFullFrameGauge_reconstructInvariant_mem_variety d n ι M0 S y)
      hG hdet hsel hmixed

/-- If the selected kernel coordinate matches and the free mixed rows are those
of `G`, then the explicit reconstruction has invariant `G`.  This is the
algebraic core of the future local-product chart `left_inv_on` proof. -/
theorem sourceFullFrameGauge_reconstructInvariant_eq_of_kernel_eq_mixedRows_eq
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n)
    (hdet : G.det ι ≠ 0)
    (y : sourceFullFrameMaxRankChartModel d n ι M0 S)
    (hG_source :
      sourceFullFrameSelectedSymmetricCoordOfSource d n ι hG ∈
        (sourceFullFrameSymmetricEquation_implicitChart d M0 hM0).source)
    (hX_source :
      sourceFullFrameGaugeSliceMapSymmetric d M0 S y.1 ∈
        (sourceFullFrameSymmetricEquation_implicitChart d M0 hM0).source)
    (hkernel :
      sourceFullFrameSelectedKernelCoord d n ι hM0 hG =
        sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S y.1)
    (hmixed :
      y.2 = sourceSelectedMixedRows d n ι G) :
    sourceFullFrameGauge_reconstructInvariant d n ι M0 S y = G := by
  let H := sourceFullFrameGauge_reconstructInvariant d n ι M0 S y
  have hsel :
      sourceFullFrameOrientedCoordOfSource d n ι H =
        sourceFullFrameOrientedCoordOfSource d n ι G := by
    simpa [H] using
      sourceFullFrameGauge_reconstructInvariant_selectedCoord_eq_of_kernel_eq
        d n ι hM0 S hG y hG_source hX_source hkernel
  have hdetH : H.det ι ≠ 0 := by
    have hdet_eq : H.det ι = G.det ι := by
      simpa [sourceFullFrameOrientedCoordOfSource] using congrArg Prod.snd hsel
    rw [hdet_eq]
    exact hdet
  have hframe_det :
      (sourceFullFrameGauge_reconstructFrame d n ι M0 S y).det ≠ 0 := by
    rw [← sourceFullFrameGauge_reconstructInvariant_selectedDet d n ι M0 S y]
    exact hdetH
  have hmixedH :
      sourceSelectedMixedRows d n ι H =
        sourceSelectedMixedRows d n ι G := by
    calc
      sourceSelectedMixedRows d n ι H = y.2 := by
        simpa [H] using
          sourceSelectedMixedRows_reconstructInvariant_eq_of_frame_det_ne_zero
            d n ι M0 S y hframe_det
      _ = sourceSelectedMixedRows d n ι G := hmixed
  exact
    sourceFullFrameGauge_reconstructInvariant_eq_of_selectedCoord_eq_mixedRows_eq
      d n ι M0 S y hG hdet (by simpa [H] using hsel) (by simpa [H] using hmixedH)

namespace SourceFullFrameMaxRankChartAmbientShrink

/-- The explicit chart candidate attached to an ambient shrink. -/
noncomputable def chartCandidate
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0)
    (G : SourceOrientedGramData d n) :
    sourceFullFrameMaxRankChartModel d n ι M0 S :=
  ((sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).symm
      (sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G),
    sourceSelectedMixedRows d n ι G)

@[simp]
theorem chartCandidate_fst
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0)
    (G : SourceOrientedGramData d n) :
    (chartCandidate (d := d) (n := n) (ι := ι) hM0 S G).1 =
      (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).symm
        (sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G) :=
  rfl

@[simp]
theorem chartCandidate_snd
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0)
    (G : SourceOrientedGramData d n) :
    (chartCandidate (d := d) (n := n) (ι := ι) hM0 S G).2 =
      sourceSelectedMixedRows d n ι G :=
  rfl

/-- The ambient selected-kernel coordinate is continuous on an ambient shrink.
The source condition for the symmetric implicit chart is read from the shrink
field. -/
theorem selectedKernelCoordAmbient_continuousOn_Ωamb
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    {hM0 : IsUnit M0.det}
    {S : SourceFullFrameGaugeSliceData d M0}
    {G0 : SourceOrientedGramData d n}
    (T : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0) :
    ContinuousOn (sourceFullFrameSelectedKernelCoordAmbient d n ι hM0)
      T.Ωamb := by
  let e := sourceFullFrameSymmetricEquation_implicitChart d M0 hM0
  have hselected :
      ContinuousOn (sourceFullFrameSelectedSymmetricCoordAmbient d n ι)
        T.Ωamb :=
    (continuous_sourceFullFrameSelectedSymmetricCoordAmbient d n ι).continuousOn
  have he :
      ContinuousOn
        (fun G : SourceOrientedGramData d n =>
          e (sourceFullFrameSelectedSymmetricCoordAmbient d n ι G))
        T.Ωamb :=
    e.continuousOn.comp hselected (by
      intro G hG
      exact T.selectedSymmetric_mem_implicitSource hG)
  have hsnd :
      ContinuousOn
        (fun p :
          ℂ × (sourceFullFrameSymmetricEquationDerivCLM d
              (sourceFullFrameOrientedGramCoord d M0)).ker => p.2)
        Set.univ :=
    continuous_snd.continuousOn
  simpa [sourceFullFrameSelectedKernelCoordAmbient, e] using
    hsnd.comp he (by intro G _; exact Set.mem_univ _)

/-- The explicit chart candidate is continuous on the ambient shrink. -/
theorem chartCandidate_continuousOn_Ωamb
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    {hM0 : IsUnit M0.det}
    {S : SourceFullFrameGaugeSliceData d M0}
    {G0 : SourceOrientedGramData d n}
    (T : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0) :
    ContinuousOn (chartCandidate (d := d) (n := n) (ι := ι) hM0 S)
      T.Ωamb := by
  let e := sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S
  have hK :
      ContinuousOn (sourceFullFrameSelectedKernelCoordAmbient d n ι hM0)
        T.Ωamb :=
    T.selectedKernelCoordAmbient_continuousOn_Ωamb
  have hsymm :
      ContinuousOn
        (fun G : SourceOrientedGramData d n =>
          e.symm (sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G))
        T.Ωamb :=
    e.continuousOn_symm.comp hK (by
      intro G hG
      exact T.selectedKernel_mem_target hG)
  have hmixed :
      ContinuousOn (sourceSelectedMixedRows d n ι) T.Ωamb :=
    (continuous_sourceSelectedMixedRows d n ι).continuousOn
  simpa [chartCandidate, e] using hsymm.prodMk hmixed

/-- Relative-domain continuity of the explicit chart candidate. -/
theorem chartCandidate_continuousOn_relDomain
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    {hM0 : IsUnit M0.det}
    {S : SourceFullFrameGaugeSliceData d M0}
    {G0 : SourceOrientedGramData d n}
    (T : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0) :
    ContinuousOn (chartCandidate (d := d) (n := n) (ι := ι) hM0 S)
      T.relDomain :=
  T.chartCandidate_continuousOn_Ωamb.mono (by
    intro G hG
    exact T.mem_Ωamb_of_mem_relDomain hG)

/-- Reconstructing from a model coordinate and then applying the explicit
chart candidate returns the original model coordinate, provided the slice
coordinate lies in the kernel-chart source and the reconstructed selected
frame is invertible. -/
theorem chartCandidate_reconstructInvariant_eq_of_chartSource_frameDet
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0)
    {y : sourceFullFrameMaxRankChartModel d n ι M0 S}
    (hy_source :
      y.1 ∈
        (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
          d hM0 S).source)
    (hy_det :
      (sourceFullFrameGauge_reconstructFrame d n ι M0 S y).det ≠ 0) :
    chartCandidate (d := d) (n := n) (ι := ι) hM0 S
        (sourceFullFrameGauge_reconstructInvariant d n ι M0 S y) =
      y := by
  apply Prod.ext
  · change
      (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).symm
          (sourceFullFrameSelectedKernelCoordAmbient d n ι hM0
            (sourceFullFrameGauge_reconstructInvariant d n ι M0 S y)) =
        y.1
    rw [sourceFullFrameSelectedKernelCoordAmbient_reconstructInvariant_eq]
    exact
      sourceFullFrameGaugeSliceImplicitKernelMap_left_inv_on_chartSource
        d hM0 S hy_source
  · simpa [chartCandidate] using
      sourceSelectedMixedRows_reconstructInvariant_eq_of_frame_det_ne_zero
        d n ι M0 S y hy_det

/-- On the shrink relative domain, the explicit chart candidate reconstructs
the original oriented source invariant.  This is the constructor-level
left-inverse theorem before bundling into
`SourceOrientedFullFrameMaxRankChartData`. -/
theorem reconstructInvariant_chartCandidate_eq_of_mem_relDomain
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    {hM0 : IsUnit M0.det}
    {S : SourceFullFrameGaugeSliceData d M0}
    {G0 G : SourceOrientedGramData d n}
    (T : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0)
    (hG : G ∈ T.relDomain) :
    sourceFullFrameGauge_reconstructInvariant d n ι M0 S
        (chartCandidate (d := d) (n := n) (ι := ι) hM0 S G) =
      G := by
  let e := sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S
  let y : sourceFullFrameMaxRankChartModel d n ι M0 S :=
    chartCandidate (d := d) (n := n) (ι := ι) hM0 S G
  have hGvar : G ∈ sourceOrientedGramVariety d n :=
    T.mem_variety_of_mem_relDomain hG
  have hdet : G.det ι ≠ 0 :=
    T.selectedDet_ne_zero_of_mem_relDomain hG
  have hG_source :
      sourceFullFrameSelectedSymmetricCoordOfSource d n ι hGvar ∈
        (sourceFullFrameSymmetricEquation_implicitChart d M0 hM0).source := by
    simpa [sourceFullFrameSelectedSymmetricCoordAmbient_eq_of_mem_variety
      d n ι hGvar] using
      T.selectedSymmetric_mem_implicitSource hG.1
  have htarget :
      sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G ∈ e.target :=
    T.selectedKernel_mem_target hG.1
  have hX_source :
      sourceFullFrameGaugeSliceMapSymmetric d M0 S y.1 ∈
        (sourceFullFrameSymmetricEquation_implicitChart d M0 hM0).source := by
    simpa [y, chartCandidate, e] using
      T.gaugeSlice_mem_implicitSource hG.1
  have hkernel :
      sourceFullFrameSelectedKernelCoord d n ι hM0 hGvar =
        sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S y.1 := by
    have hright :
        sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S
            (e.symm (sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G)) =
          sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G := by
      exact
        sourceFullFrameGaugeSliceImplicitKernelMap_right_inv_on_chartTarget
          d hM0 S htarget
    calc
      sourceFullFrameSelectedKernelCoord d n ι hM0 hGvar =
          sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G := by
        exact
          (sourceFullFrameSelectedKernelCoordAmbient_eq_of_mem_variety
            d n ι hM0 hGvar).symm
      _ = sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S y.1 := by
        simpa [y, chartCandidate, e] using hright.symm
  exact
    sourceFullFrameGauge_reconstructInvariant_eq_of_kernel_eq_mixedRows_eq
      d n ι hM0 S hGvar hdet y hG_source hX_source hkernel (by simp [y])

/-- The local-biholomorph packet attached to an ambient shrink, once the
regularity of the explicit reconstruction inverse on the chart image has been
proved.  The inverse identities and chart continuity are supplied by the
checked shrink fields. -/
noncomputable def localBiholomorph
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    {hM0 : IsUnit M0.det}
    {S : SourceFullFrameGaugeSliceData d M0}
    {G0 : SourceOrientedGramData d n}
    (T : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0)
    (hinv_differentiableOn :
      DifferentiableOn ℂ
        (sourceFullFrameGauge_reconstructInvariant d n ι M0 S)
        ((chartCandidate (d := d) (n := n) (ι := ι) hM0 S) ''
          T.relDomain))
    (hinv_continuousOn :
      ContinuousOn
        (sourceFullFrameGauge_reconstructInvariant d n ι M0 S)
        ((chartCandidate (d := d) (n := n) (ι := ι) hM0 S) ''
          T.relDomain)) :
    LocalBiholomorphOnSourceOrientedVariety d n T.relDomain
      (chartCandidate (d := d) (n := n) (ι := ι) hM0 S) where
  inv := sourceFullFrameGauge_reconstructInvariant d n ι M0 S
  left_inv_on := by
    intro G hG
    exact T.reconstructInvariant_chartCandidate_eq_of_mem_relDomain hG
  right_inv_on := by
    rintro y ⟨G, hG, rfl⟩
    rw [T.reconstructInvariant_chartCandidate_eq_of_mem_relDomain hG]
  inv_mem_on := by
    rintro y ⟨G, hG, rfl⟩
    rw [T.reconstructInvariant_chartCandidate_eq_of_mem_relDomain hG]
    exact hG
  chart_continuousOn := T.chartCandidate_continuousOn_relDomain
  inv_differentiableOn := hinv_differentiableOn
  inv_continuousOn := hinv_continuousOn

/-- Pull an open model-coordinate set back through the explicit chart
candidate inside an ambient shrink.  If reconstructing every model point of
`V` lands in the old relative domain, and the model points satisfy the
right-inverse source/determinant hypotheses, then the new relative-domain
chart image is exactly `V`. -/
theorem exists_restrict_modelOpen_image_eq
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    {hM0 : IsUnit M0.det}
    {S : SourceFullFrameGaugeSliceData d M0}
    {G0 : SourceOrientedGramData d n}
    (T : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0)
    {V : Set (sourceFullFrameMaxRankChartModel d n ι M0 S)}
    (hV_open : IsOpen V)
    (hcenterV :
      chartCandidate (d := d) (n := n) (ι := ι) hM0 S G0 ∈ V)
    (hsource :
      ∀ y ∈ V,
        y.1 ∈
          (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
            d hM0 S).source)
    (hdet :
      ∀ y ∈ V,
        (sourceFullFrameGauge_reconstructFrame d n ι M0 S y).det ≠ 0)
    (hreconstruct :
      ∀ y ∈ V,
        sourceFullFrameGauge_reconstructInvariant d n ι M0 S y ∈
          T.relDomain) :
    ∃ T' : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0,
      T'.relDomain ⊆ T.relDomain ∧
        (chartCandidate (d := d) (n := n) (ι := ι) hM0 S) ''
            T'.relDomain = V := by
  classical
  let chart : SourceOrientedGramData d n →
      sourceFullFrameMaxRankChartModel d n ι M0 S :=
    chartCandidate (d := d) (n := n) (ι := ι) hM0 S
  rcases (continuousOn_iff'.mp T.chartCandidate_continuousOn_Ωamb)
      V hV_open with ⟨U, hU_open, hpre_eq⟩
  let Ωamb' : Set (SourceOrientedGramData d n) := U ∩ T.Ωamb
  have hΩamb'_open : IsOpen Ωamb' := hU_open.inter T.Ωamb_open
  have hcenter_pre : G0 ∈ chart ⁻¹' V ∩ T.Ωamb := ⟨hcenterV, T.center_mem⟩
  have hcenter_UΩ : G0 ∈ U ∩ T.Ωamb := by
    have htmp :
        G0 ∈
          (chartCandidate (d := d) (n := n) (ι := ι) hM0 S) ⁻¹' V ∩
            T.Ωamb := by
      simpa [chart] using hcenter_pre
    rw [hpre_eq] at htmp
    exact htmp
  let T' : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0 :=
    { Ωamb := Ωamb'
      Ωamb_open := hΩamb'_open
      center_mem := hcenter_UΩ
      selectedSymmetric_mem_implicitSource := by
        intro G hG
        exact T.selectedSymmetric_mem_implicitSource hG.2
      selectedKernel_mem_target := by
        intro G hG
        exact T.selectedKernel_mem_target hG.2
      gaugeSlice_mem_implicitSource := by
        intro G hG
        exact T.gaugeSlice_mem_implicitSource hG.2
      selectedDetNonzero := by
        intro G hG
        exact T.selectedDetNonzero hG.2 }
  refine ⟨T', ?_, ?_⟩
  · intro G hG
    exact ⟨hG.1.2, hG.2⟩
  · ext y
    constructor
    · rintro ⟨G, hGT', rfl⟩
      have hG_UΩ : G ∈ U ∩ T.Ωamb := hGT'.1
      have hG_pre : G ∈ chart ⁻¹' V ∩ T.Ωamb := by
        have htmp :
            G ∈
              (chartCandidate (d := d) (n := n) (ι := ι) hM0 S) ⁻¹' V ∩
                T.Ωamb := by
          rw [hpre_eq]
          exact hG_UΩ
        simpa [chart] using htmp
      exact hG_pre.1
    · intro hyV
      let H : SourceOrientedGramData d n :=
        sourceFullFrameGauge_reconstructInvariant d n ι M0 S y
      have hH_old : H ∈ T.relDomain := hreconstruct y hyV
      have hchartH : chart H = y := by
        simpa [chart, H] using
          chartCandidate_reconstructInvariant_eq_of_chartSource_frameDet
            (d := d) (n := n) (ι := ι) hM0 S
            (y := y) (hsource y hyV) (hdet y hyV)
      have hH_pre : H ∈ chart ⁻¹' V ∩ T.Ωamb :=
        ⟨by simpa [hchartH] using hyV, hH_old.1⟩
      have hH_UΩ : H ∈ U ∩ T.Ωamb := by
        have htmp :
            H ∈
              (chartCandidate (d := d) (n := n) (ι := ι) hM0 S) ⁻¹' V ∩
                T.Ωamb := by
          simpa [chart] using hH_pre
        rw [hpre_eq] at htmp
        exact htmp
      refine ⟨H, ?_, hchartH⟩
      exact ⟨hH_UΩ, hH_old.2⟩

end SourceFullFrameMaxRankChartAmbientShrink

/-- Full-frame chart data at a selected determinant-nonzero max-rank point.
This packet records exactly the local-product chart fields needed by the
existing max-rank identity-principle API; the hard constructor producing such a
packet is the later local-image theorem. -/
structure SourceOrientedFullFrameMaxRankChartData
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (G0 : SourceOrientedGramData d n) where
  M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ
  M0_det_unit : IsUnit M0.det
  M0_oriented :
    sourceFullFrameOrientedGramCoord d M0 =
      sourceFullFrameOrientedCoordOfSource d n ι G0
  slice : SourceFullFrameGaugeSliceData d M0
  kernelChart :
    OpenPartialHomeomorph slice.slice
      (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d M0)).ker
  kernelChart_eq :
    (kernelChart : slice.slice →
      (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d M0)).ker) =
      sourceFullFrameGaugeSliceImplicitKernelMap d M0_det_unit slice
  Ω : Set (SourceOrientedGramData d n)
  Ω_relOpen : IsRelOpenInSourceOrientedGramVariety d n Ω
  Ωamb : Set (SourceOrientedGramData d n)
  Ωamb_open : IsOpen Ωamb
  Ω_eq_ambient : Ω = Ωamb ∩ sourceOrientedGramVariety d n
  center_mem : G0 ∈ Ω
  center_mem_amb : G0 ∈ Ωamb
  Ω_maxRank : Ω ⊆ {G | SourceOrientedMaxRankAt d n G}
  Ω_selectedDetNonzero : Ω ⊆ sourceFullFrameSelectedDetNonzeroDomain d n ι
  Ω_selectedSymmetric_mem_implicitSource :
    ∀ {G : SourceOrientedGramData d n}, G ∈ Ω →
      sourceFullFrameSelectedSymmetricCoordAmbient d n ι G ∈
        (sourceFullFrameSymmetricEquation_implicitChart d M0 M0_det_unit).source
  Ω_selectedKernel_mem_target :
    ∀ {G : SourceOrientedGramData d n}, G ∈ Ω →
      sourceFullFrameSelectedKernelCoordAmbient d n ι M0_det_unit G ∈
        kernelChart.target
  Ω_gaugeSlice_mem_implicitSource :
    ∀ {G : SourceOrientedGramData d n}, G ∈ Ω →
      sourceFullFrameGaugeSliceMapSymmetric d M0 slice
          (kernelChart.symm
            (sourceFullFrameSelectedKernelCoordAmbient d n ι M0_det_unit G)) ∈
        (sourceFullFrameSymmetricEquation_implicitChart d M0 M0_det_unit).source
  chart :
    SourceOrientedGramData d n →
      sourceFullFrameMaxRankChartModel d n ι M0 slice
  chart_eq_candidate :
    chart =
      fun G =>
        (kernelChart.symm
          (sourceFullFrameSelectedKernelCoordAmbient d n ι M0_det_unit G),
          sourceSelectedMixedRows d n ι G)
  chart_continuousOn_amb : ContinuousOn chart Ωamb
  chart_open : IsOpen (chart '' Ω)
  chart_biholomorphic :
    LocalBiholomorphOnSourceOrientedVariety d n Ω chart
  inv_formula :
    ∀ y ∈ chart '' Ω,
      chart_biholomorphic.inv y =
        sourceFullFrameGauge_reconstructInvariant d n ι M0 slice y

namespace SourceFullFrameMaxRankChartAmbientShrink

/-- Assemble full-frame max-rank chart data from an ambient shrink, after the
remaining model-side openness and inverse-regularity facts have been proved.
All determinant, max-rank, membership, chart-continuity, and inverse-identity
fields are discharged from the checked shrink API. -/
noncomputable def toFullFrameMaxRankChartData
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    {hM0 : IsUnit M0.det}
    {S : SourceFullFrameGaugeSliceData d M0}
    {G0 : SourceOrientedGramData d n}
    (T : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0)
    (hG0 : G0 ∈ sourceOrientedGramVariety d n)
    (hM0_oriented :
      sourceFullFrameOrientedGramCoord d M0 =
        sourceFullFrameOrientedCoordOfSource d n ι G0)
    (hchart_open :
      IsOpen
        ((SourceFullFrameMaxRankChartAmbientShrink.chartCandidate
          (d := d) (n := n) (ι := ι) hM0 S) '' T.relDomain))
    (hinv_differentiableOn :
      DifferentiableOn ℂ
        (sourceFullFrameGauge_reconstructInvariant d n ι M0 S)
        ((SourceFullFrameMaxRankChartAmbientShrink.chartCandidate
          (d := d) (n := n) (ι := ι) hM0 S) '' T.relDomain))
    (hinv_continuousOn :
      ContinuousOn
        (sourceFullFrameGauge_reconstructInvariant d n ι M0 S)
        ((SourceFullFrameMaxRankChartAmbientShrink.chartCandidate
          (d := d) (n := n) (ι := ι) hM0 S) '' T.relDomain)) :
    SourceOrientedFullFrameMaxRankChartData d n ι G0 :=
  { M0 := M0
    M0_det_unit := hM0
    M0_oriented := hM0_oriented
    slice := S
    kernelChart :=
      sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S
    kernelChart_eq :=
      sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph_coe
        d hM0 S
    Ω := T.relDomain
    Ω_relOpen := T.relDomain_relOpen
    Ωamb := T.Ωamb
    Ωamb_open := T.Ωamb_open
    Ω_eq_ambient := rfl
    center_mem := T.center_mem_relDomain hG0
    center_mem_amb := T.center_mem
    Ω_maxRank := by
      intro G hG
      exact T.maxRank_of_mem_relDomain hG
    Ω_selectedDetNonzero := by
      intro G hG
      exact T.selectedDet_ne_zero_of_mem_relDomain hG
    Ω_selectedSymmetric_mem_implicitSource := by
      intro G hG
      exact T.selectedSymmetric_mem_implicitSource hG.1
    Ω_selectedKernel_mem_target := by
      intro G hG
      exact T.selectedKernel_mem_target hG.1
    Ω_gaugeSlice_mem_implicitSource := by
      intro G hG
      exact T.gaugeSlice_mem_implicitSource hG.1
    chart :=
      SourceFullFrameMaxRankChartAmbientShrink.chartCandidate
        (d := d) (n := n) (ι := ι) hM0 S
    chart_eq_candidate := by
      funext G
      rfl
    chart_continuousOn_amb := T.chartCandidate_continuousOn_Ωamb
    chart_open := hchart_open
    chart_biholomorphic :=
      T.localBiholomorph hinv_differentiableOn hinv_continuousOn
    inv_formula := by
      intro y hy
      rfl }

/-- Constructor-facing model-open version of the full-frame chart assembly.
After an ambient shrink is available, it suffices to produce an open model set
`V` around the center whose reconstructed points stay in the old relative
domain, satisfy the model-side right-inverse hypotheses, and on which the
explicit reconstruction map is regular. -/
noncomputable def toFullFrameMaxRankChartData_of_modelOpen
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    {hM0 : IsUnit M0.det}
    {S : SourceFullFrameGaugeSliceData d M0}
    {G0 : SourceOrientedGramData d n}
    (T : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0)
    (hG0 : G0 ∈ sourceOrientedGramVariety d n)
    (hM0_oriented :
      sourceFullFrameOrientedGramCoord d M0 =
        sourceFullFrameOrientedCoordOfSource d n ι G0)
    {V : Set (sourceFullFrameMaxRankChartModel d n ι M0 S)}
    (hV_open : IsOpen V)
    (hcenterV :
      chartCandidate (d := d) (n := n) (ι := ι) hM0 S G0 ∈ V)
    (hsource :
      ∀ y ∈ V,
        y.1 ∈
          (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
            d hM0 S).source)
    (hdet :
      ∀ y ∈ V,
        (sourceFullFrameGauge_reconstructFrame d n ι M0 S y).det ≠ 0)
    (hreconstruct :
      ∀ y ∈ V,
        sourceFullFrameGauge_reconstructInvariant d n ι M0 S y ∈
          T.relDomain)
    (hinv_differentiableOn :
      DifferentiableOn ℂ
        (sourceFullFrameGauge_reconstructInvariant d n ι M0 S) V)
    (hinv_continuousOn :
      ContinuousOn (sourceFullFrameGauge_reconstructInvariant d n ι M0 S) V) :
    SourceOrientedFullFrameMaxRankChartData d n ι G0 := by
  classical
  let hex :=
    T.exists_restrict_modelOpen_image_eq
      hV_open hcenterV hsource hdet hreconstruct
  let T' : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0 :=
    Classical.choose hex
  have hT'_image :
      (chartCandidate (d := d) (n := n) (ι := ι) hM0 S) ''
          T'.relDomain = V :=
    (Classical.choose_spec hex).2
  exact
    T'.toFullFrameMaxRankChartData hG0 hM0_oriented
      (by simpa [hT'_image] using hV_open)
      (by simpa [hT'_image] using hinv_differentiableOn)
      (by simpa [hT'_image] using hinv_continuousOn)

/-- The canonical model-side domain attached to an ambient shrink: the slice
coordinate lies in the kernel-chart source, the reconstructed invariant stays
inside the ambient shrink, and the reconstructed selected frame is invertible. -/
def modelChartDomain
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    {hM0 : IsUnit M0.det}
    {S : SourceFullFrameGaugeSliceData d M0}
    {G0 : SourceOrientedGramData d n}
    (T : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0) :
    Set (sourceFullFrameMaxRankChartModel d n ι M0 S) :=
  {y | y.1 ∈
      (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
        d hM0 S).source} ∩
    ((sourceFullFrameGauge_reconstructInvariant d n ι M0 S) ⁻¹' T.Ωamb ∩
      sourceFullFrameGaugeModelDetNonzero d n ι M0 S)

/-- The canonical model-side chart domain is open. -/
theorem modelChartDomain_open
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    {hM0 : IsUnit M0.det}
    {S : SourceFullFrameGaugeSliceData d M0}
    {G0 : SourceOrientedGramData d n}
    (T : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0) :
    IsOpen T.modelChartDomain := by
  have hsource_open :
      IsOpen
        ({y : sourceFullFrameMaxRankChartModel d n ι M0 S |
          y.1 ∈
            (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
              d hM0 S).source}) :=
    (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
      d hM0 S).open_source.preimage continuous_fst
  have hpre_open :
      IsOpen
        ((sourceFullFrameGauge_reconstructInvariant d n ι M0 S) ⁻¹' T.Ωamb ∩
          sourceFullFrameGaugeModelDetNonzero d n ι M0 S) := by
    have hcont :=
      continuousOn_sourceFullFrameGauge_reconstructInvariant_on_modelDetNonzero
        d n ι M0 S
    rcases (continuousOn_iff'.mp hcont) T.Ωamb T.Ωamb_open with
      ⟨U, hU_open, hpre_eq⟩
    rw [hpre_eq]
    exact hU_open.inter (sourceFullFrameGaugeModelDetNonzero_open d n ι M0 S)
  exact hsource_open.inter hpre_open

/-- At a represented base point, the chart candidate reconstructs the stored
base selected frame. -/
theorem chartCandidate_reconstructFrame_center_eq
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0)
    {G0 : SourceOrientedGramData d n}
    (hG0 : G0 ∈ sourceOrientedGramVariety d n)
    (hM0_oriented :
      sourceFullFrameOrientedGramCoord d M0 =
        sourceFullFrameOrientedCoordOfSource d n ι G0) :
    sourceFullFrameGauge_reconstructFrame d n ι M0 S
        (chartCandidate (d := d) (n := n) (ι := ι) hM0 S G0) =
      M0 := by
  have hzero :
      sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G0 = 0 :=
    sourceFullFrameSelectedKernelCoordAmbient_eq_zero_at_base
      d n ι hM0 hG0 hM0_oriented
  have hsymm :
      (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).symm
        (0 :
          (sourceFullFrameSymmetricEquationDerivCLM d
            (sourceFullFrameOrientedGramCoord d M0)).ker) = (0 : S.slice) :=
    sourceFullFrameGaugeSliceImplicitKernel_symm_zero d hM0 S
  ext a μ
  simp [chartCandidate, sourceFullFrameGauge_reconstructFrame, hzero, hsymm]

/-- The chart candidate at a represented base point belongs to the canonical
model-side chart domain. -/
theorem chartCandidate_center_mem_modelChartDomain
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    {hM0 : IsUnit M0.det}
    {S : SourceFullFrameGaugeSliceData d M0}
    {G0 : SourceOrientedGramData d n}
    (T : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0)
    (hG0 : G0 ∈ sourceOrientedGramVariety d n)
    (hM0_oriented :
      sourceFullFrameOrientedGramCoord d M0 =
        sourceFullFrameOrientedCoordOfSource d n ι G0) :
    chartCandidate (d := d) (n := n) (ι := ι) hM0 S G0 ∈
      T.modelChartDomain := by
  have hzero :
      sourceFullFrameSelectedKernelCoordAmbient d n ι hM0 G0 = 0 :=
    sourceFullFrameSelectedKernelCoordAmbient_eq_zero_at_base
      d n ι hM0 hG0 hM0_oriented
  have hsymm :
      (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).symm
        (0 :
          (sourceFullFrameSymmetricEquationDerivCLM d
            (sourceFullFrameOrientedGramCoord d M0)).ker) = (0 : S.slice) :=
    sourceFullFrameGaugeSliceImplicitKernel_symm_zero d hM0 S
  have hframe :
      sourceFullFrameGauge_reconstructFrame d n ι M0 S
          (chartCandidate (d := d) (n := n) (ι := ι) hM0 S G0) =
        M0 :=
    chartCandidate_reconstructFrame_center_eq
      (d := d) (n := n) (ι := ι) hM0 S hG0 hM0_oriented
  constructor
  · simpa [chartCandidate, hzero, hsymm] using
      sourceFullFrameGaugeSliceImplicitKernel_zero_mem_chartSource d hM0 S
  · constructor
    · have hrec :=
        T.reconstructInvariant_chartCandidate_eq_of_mem_relDomain
          (T.center_mem_relDomain hG0)
      change
        sourceFullFrameGauge_reconstructInvariant d n ι M0 S
            (chartCandidate (d := d) (n := n) (ι := ι) hM0 S G0) ∈
          T.Ωamb
      rw [hrec]
      exact T.center_mem
    · simpa [sourceFullFrameGaugeModelDetNonzero, hframe] using hM0.ne_zero

/-- Canonical assembly of full-frame chart data from an ambient shrink, using
the model domain whose openness and regularity are now proved internally. -/
noncomputable def toFullFrameMaxRankChartData_of_modelChartDomain
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    {hM0 : IsUnit M0.det}
    {S : SourceFullFrameGaugeSliceData d M0}
    {G0 : SourceOrientedGramData d n}
    (T : SourceFullFrameMaxRankChartAmbientShrink d n ι hM0 S G0)
    (hG0 : G0 ∈ sourceOrientedGramVariety d n)
    (hM0_oriented :
      sourceFullFrameOrientedGramCoord d M0 =
        sourceFullFrameOrientedCoordOfSource d n ι G0) :
    SourceOrientedFullFrameMaxRankChartData d n ι G0 :=
  T.toFullFrameMaxRankChartData_of_modelOpen hG0 hM0_oriented
    T.modelChartDomain_open
    (T.chartCandidate_center_mem_modelChartDomain hG0 hM0_oriented)
    (by
      intro y hy
      exact hy.1)
    (by
      intro y hy
      simpa [sourceFullFrameGaugeModelDetNonzero] using hy.2.2)
    (by
      intro y hy
      exact
        ⟨hy.2.1,
          sourceFullFrameGauge_reconstructInvariant_mem_variety d n ι M0 S y⟩)
    ((differentiableOn_sourceFullFrameGauge_reconstructInvariant_on_modelDetNonzero
      d n ι M0 S).mono (by
        intro y hy
        exact hy.2.2))
    ((continuousOn_sourceFullFrameGauge_reconstructInvariant_on_modelDetNonzero
      d n ι M0 S).mono (by
        intro y hy
        exact hy.2.2))

end SourceFullFrameMaxRankChartAmbientShrink

namespace SourceOrientedFullFrameMaxRankChartData

/-- Points in the relative chart domain are still points of the source
oriented Gram variety. -/
theorem mem_variety_of_mem_Ω
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {G0 G : SourceOrientedGramData d n}
    (C : SourceOrientedFullFrameMaxRankChartData d n ι G0)
    (hG : G ∈ C.Ω) :
    G ∈ sourceOrientedGramVariety d n := by
  rw [C.Ω_eq_ambient] at hG
  exact hG.2

/-- Points in the relative chart domain lie in the stored ambient open
neighborhood. -/
theorem mem_Ωamb_of_mem_Ω
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {G0 G : SourceOrientedGramData d n}
    (C : SourceOrientedFullFrameMaxRankChartData d n ι G0)
    (hG : G ∈ C.Ω) :
    G ∈ C.Ωamb := by
  rw [C.Ω_eq_ambient] at hG
  exact hG.1

/-- Points in the selected full-frame chart domain stay on the selected
determinant-nonzero sheet. -/
theorem selectedDet_ne_zero_of_mem_Ω
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {G0 G : SourceOrientedGramData d n}
    (C : SourceOrientedFullFrameMaxRankChartData d n ι G0)
    (hG : G ∈ C.Ω) :
    G.det ι ≠ 0 := by
  exact C.Ω_selectedDetNonzero hG

/-- The total ambient chart formula associated to the stored kernel chart:
first take the ambient selected kernel coordinate, invert it through the kernel
chart, and pair the resulting slice coordinate with the mixed rows.  The final
constructor should install this formula as its `chart` field after shrinking
the domain. -/
noncomputable def chartCandidate
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {G0 : SourceOrientedGramData d n}
    (C : SourceOrientedFullFrameMaxRankChartData d n ι G0)
    (G : SourceOrientedGramData d n) :
    sourceFullFrameMaxRankChartModel d n ι C.M0 C.slice :=
  (C.kernelChart.symm
    (sourceFullFrameSelectedKernelCoordAmbient d n ι C.M0_det_unit G),
    sourceSelectedMixedRows d n ι G)

@[simp]
theorem chartCandidate_fst
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {G0 G : SourceOrientedGramData d n}
    (C : SourceOrientedFullFrameMaxRankChartData d n ι G0) :
    (C.chartCandidate G).1 =
      C.kernelChart.symm
        (sourceFullFrameSelectedKernelCoordAmbient d n ι C.M0_det_unit G) :=
  rfl

@[simp]
theorem chartCandidate_snd
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {G0 G : SourceOrientedGramData d n}
    (C : SourceOrientedFullFrameMaxRankChartData d n ι G0) :
    (C.chartCandidate G).2 = sourceSelectedMixedRows d n ι G :=
  rfl

/-- On the source variety, the ambient chart formula is the expected
source-selected kernel formula. -/
theorem chartCandidate_eq_of_mem_variety
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {G0 G : SourceOrientedGramData d n}
    (C : SourceOrientedFullFrameMaxRankChartData d n ι G0)
    (hG : G ∈ sourceOrientedGramVariety d n) :
    C.chartCandidate G =
      (C.kernelChart.symm
        (sourceFullFrameSelectedKernelCoord d n ι C.M0_det_unit hG),
        sourceSelectedMixedRows d n ι G) := by
  simp [chartCandidate,
    sourceFullFrameSelectedKernelCoordAmbient_eq_of_mem_variety d n ι
      C.M0_det_unit hG]

/-- The stored chart field is the explicit candidate chart formula. -/
theorem chart_eq_chartCandidate
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {G0 : SourceOrientedGramData d n}
    (C : SourceOrientedFullFrameMaxRankChartData d n ι G0) :
    C.chart = C.chartCandidate := by
  funext G
  simpa [chartCandidate] using congrFun C.chart_eq_candidate G

@[simp]
theorem chart_apply_eq_chartCandidate
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {G0 G : SourceOrientedGramData d n}
    (C : SourceOrientedFullFrameMaxRankChartData d n ι G0) :
    C.chart G = C.chartCandidate G := by
  exact congrFun C.chart_eq_chartCandidate G

/-- The stored kernel chart is the local inverse-function chart for the
implicit kernel-coordinate map. -/
@[simp]
theorem kernelChart_apply_eq
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {G0 : SourceOrientedGramData d n}
    (C : SourceOrientedFullFrameMaxRankChartData d n ι G0)
    (X : C.slice.slice) :
    C.kernelChart X =
      sourceFullFrameGaugeSliceImplicitKernelMap d C.M0_det_unit C.slice X := by
  exact congrFun C.kernelChart_eq X

/-- Right-inverse form of the stored kernel chart, written in the explicit
implicit-kernel coordinates used by the reconstruction formula. -/
theorem kernelChart_right_inv_implicitKernel
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {G0 : SourceOrientedGramData d n}
    (C : SourceOrientedFullFrameMaxRankChartData d n ι G0)
    {K : (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d C.M0)).ker}
    (hK : K ∈ C.kernelChart.target) :
    sourceFullFrameGaugeSliceImplicitKernelMap d C.M0_det_unit C.slice
        (C.kernelChart.symm K) = K := by
  have hright := C.kernelChart.right_inv hK
  simpa using hright

/-- Left-inverse form of the stored kernel chart, written in the explicit
implicit-kernel coordinates used by the reconstruction formula. -/
theorem kernelChart_left_inv_implicitKernel
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {G0 : SourceOrientedGramData d n}
    (C : SourceOrientedFullFrameMaxRankChartData d n ι G0)
    {X : C.slice.slice}
    (hX : X ∈ C.kernelChart.source) :
    C.kernelChart.symm
        (sourceFullFrameGaugeSliceImplicitKernelMap d C.M0_det_unit C.slice X) =
      X := by
  have hleft := C.kernelChart.left_inv hX
  simpa using hleft

/-- Once the selected kernel coordinate is in the stored kernel-chart target,
the explicit reconstruction with source mixed rows recovers the original
oriented invariant.  This is the algebraic core used by the forthcoming
`sourceFullFrameMaxRankChart_localImage_kernel_mixed_eq` theorem. -/
theorem reconstructInvariant_eq_of_selectedKernel_target_mixedRows
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {G0 : SourceOrientedGramData d n}
    (C : SourceOrientedFullFrameMaxRankChartData d n ι G0)
    {G : SourceOrientedGramData d n}
    (hG : G ∈ sourceOrientedGramVariety d n)
    (hdet : G.det ι ≠ 0)
    (hsel_source :
      sourceFullFrameSelectedSymmetricCoordOfSource d n ι hG ∈
        (sourceFullFrameSymmetricEquation_implicitChart d C.M0 C.M0_det_unit).source)
    (hK_target :
      sourceFullFrameSelectedKernelCoord d n ι C.M0_det_unit hG ∈
        C.kernelChart.target)
    (hX_source :
      sourceFullFrameGaugeSliceMapSymmetric d C.M0 C.slice
          (C.kernelChart.symm
            (sourceFullFrameSelectedKernelCoord d n ι C.M0_det_unit hG)) ∈
        (sourceFullFrameSymmetricEquation_implicitChart d C.M0 C.M0_det_unit).source) :
    sourceFullFrameGauge_reconstructInvariant d n ι C.M0 C.slice
        (C.kernelChart.symm
          (sourceFullFrameSelectedKernelCoord d n ι C.M0_det_unit hG),
          sourceSelectedMixedRows d n ι G) =
      G := by
  let K := sourceFullFrameSelectedKernelCoord d n ι C.M0_det_unit hG
  let y : sourceFullFrameMaxRankChartModel d n ι C.M0 C.slice :=
    (C.kernelChart.symm K, sourceSelectedMixedRows d n ι G)
  have hkernel :
      sourceFullFrameSelectedKernelCoord d n ι C.M0_det_unit hG =
        sourceFullFrameGaugeSliceImplicitKernelMap d C.M0_det_unit C.slice y.1 := by
    simpa [K, y] using
      (C.kernelChart_right_inv_implicitKernel hK_target).symm
  exact
    sourceFullFrameGauge_reconstructInvariant_eq_of_kernel_eq_mixedRows_eq
      d n ι C.M0_det_unit C.slice hG hdet y
      hsel_source hX_source hkernel (by simp [y])

/-- Domain-specialized form of
`reconstructInvariant_eq_of_selectedKernel_target_mixedRows`: the source
variety and determinant hypotheses are read directly from the stored chart
domain. -/
theorem reconstructInvariant_eq_of_mem_Ω_selectedKernel_target_mixedRows
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {G0 : SourceOrientedGramData d n}
    (C : SourceOrientedFullFrameMaxRankChartData d n ι G0)
    {G : SourceOrientedGramData d n}
    (hGΩ : G ∈ C.Ω)
    (hsel_source :
      sourceFullFrameSelectedSymmetricCoordOfSource d n ι
          (C.mem_variety_of_mem_Ω hGΩ) ∈
        (sourceFullFrameSymmetricEquation_implicitChart d C.M0 C.M0_det_unit).source)
    (hK_target :
      sourceFullFrameSelectedKernelCoord d n ι C.M0_det_unit
          (C.mem_variety_of_mem_Ω hGΩ) ∈
        C.kernelChart.target)
    (hX_source :
      sourceFullFrameGaugeSliceMapSymmetric d C.M0 C.slice
          (C.kernelChart.symm
            (sourceFullFrameSelectedKernelCoord d n ι C.M0_det_unit
              (C.mem_variety_of_mem_Ω hGΩ))) ∈
        (sourceFullFrameSymmetricEquation_implicitChart d C.M0 C.M0_det_unit).source) :
    sourceFullFrameGauge_reconstructInvariant d n ι C.M0 C.slice
        (C.kernelChart.symm
          (sourceFullFrameSelectedKernelCoord d n ι C.M0_det_unit
            (C.mem_variety_of_mem_Ω hGΩ)),
          sourceSelectedMixedRows d n ι G) =
      G := by
  exact
    C.reconstructInvariant_eq_of_selectedKernel_target_mixedRows
      (C.mem_variety_of_mem_Ω hGΩ)
      (C.selectedDet_ne_zero_of_mem_Ω hGΩ)
      hsel_source hK_target hX_source

/-- Left-inverse core for the total chart candidate.  The remaining
constructor work is exactly to shrink the domain so that the three membership
hypotheses below hold. -/
theorem reconstructInvariant_chartCandidate_eq_of_mem_Ω
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {G0 : SourceOrientedGramData d n}
    (C : SourceOrientedFullFrameMaxRankChartData d n ι G0)
    {G : SourceOrientedGramData d n}
    (hGΩ : G ∈ C.Ω)
    (hsel_source :
      sourceFullFrameSelectedSymmetricCoordAmbient d n ι G ∈
        (sourceFullFrameSymmetricEquation_implicitChart d C.M0 C.M0_det_unit).source)
    (hK_target :
      sourceFullFrameSelectedKernelCoordAmbient d n ι C.M0_det_unit G ∈
        C.kernelChart.target)
    (hX_source :
      sourceFullFrameGaugeSliceMapSymmetric d C.M0 C.slice
          (C.chartCandidate G).1 ∈
        (sourceFullFrameSymmetricEquation_implicitChart d C.M0 C.M0_det_unit).source) :
    sourceFullFrameGauge_reconstructInvariant d n ι C.M0 C.slice
        (C.chartCandidate G) =
      G := by
  have hGvar := C.mem_variety_of_mem_Ω hGΩ
  have hsel_source' :
      sourceFullFrameSelectedSymmetricCoordOfSource d n ι hGvar ∈
        (sourceFullFrameSymmetricEquation_implicitChart d C.M0 C.M0_det_unit).source := by
    simpa [sourceFullFrameSelectedSymmetricCoordAmbient_eq_of_mem_variety
      d n ι hGvar] using hsel_source
  have hK_target' :
      sourceFullFrameSelectedKernelCoord d n ι C.M0_det_unit hGvar ∈
        C.kernelChart.target := by
    simpa [sourceFullFrameSelectedKernelCoordAmbient_eq_of_mem_variety
      d n ι C.M0_det_unit hGvar] using hK_target
  have hX_source' :
      sourceFullFrameGaugeSliceMapSymmetric d C.M0 C.slice
          (C.kernelChart.symm
            (sourceFullFrameSelectedKernelCoord d n ι C.M0_det_unit hGvar)) ∈
        (sourceFullFrameSymmetricEquation_implicitChart d C.M0 C.M0_det_unit).source := by
    simpa [chartCandidate,
      sourceFullFrameSelectedKernelCoordAmbient_eq_of_mem_variety
        d n ι C.M0_det_unit hGvar] using hX_source
  simpa [chartCandidate,
    sourceFullFrameSelectedKernelCoordAmbient_eq_of_mem_variety
      d n ι C.M0_det_unit hGvar] using
    C.reconstructInvariant_eq_of_mem_Ω_selectedKernel_target_mixedRows
      hGΩ hsel_source' hK_target' hX_source'

/-- Stored-domain form of the candidate left inverse.  This is the exact
left-inverse proof the constructor will use once `chart = C.chartCandidate` on
the chart domain. -/
theorem reconstructInvariant_chartCandidate_eq_of_mem_Ω_from_fields
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {G0 : SourceOrientedGramData d n}
    (C : SourceOrientedFullFrameMaxRankChartData d n ι G0)
    {G : SourceOrientedGramData d n}
    (hGΩ : G ∈ C.Ω) :
    sourceFullFrameGauge_reconstructInvariant d n ι C.M0 C.slice
        (C.chartCandidate G) =
      G := by
  exact
    C.reconstructInvariant_chartCandidate_eq_of_mem_Ω hGΩ
      (C.Ω_selectedSymmetric_mem_implicitSource hGΩ)
      (C.Ω_selectedKernel_mem_target hGΩ)
      (by simpa [chartCandidate] using
        C.Ω_gaugeSlice_mem_implicitSource hGΩ)

/-- Stored-domain left inverse for the actual stored `chart` field. -/
theorem reconstructInvariant_chart_eq_of_mem_Ω_from_fields
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {G0 : SourceOrientedGramData d n}
    (C : SourceOrientedFullFrameMaxRankChartData d n ι G0)
    {G : SourceOrientedGramData d n}
    (hGΩ : G ∈ C.Ω) :
    sourceFullFrameGauge_reconstructInvariant d n ι C.M0 C.slice
        (C.chart G) =
      G := by
  rw [C.chart_apply_eq_chartCandidate]
  exact C.reconstructInvariant_chartCandidate_eq_of_mem_Ω_from_fields hGΩ

/-- Forget the selected full-frame bookkeeping and expose the standard
max-rank chart packet used by the oriented-source identity-principle layer. -/
noncomputable def to_maxRankChart
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {G0 : SourceOrientedGramData d n}
    (C : SourceOrientedFullFrameMaxRankChartData d n ι G0) :
    SourceOrientedMaxRankChartData d n
      (M := sourceFullFrameMaxRankChartModel d n ι C.M0 C.slice) G0 where
  Ω := C.Ω
  Ω_relOpen := C.Ω_relOpen
  center_mem := C.center_mem
  Ω_maxRank := C.Ω_maxRank
  chart := C.chart
  chart_open := C.chart_open
  chart_biholomorphic := C.chart_biholomorphic

end SourceOrientedFullFrameMaxRankChartData

/-- A source-variety point on a selected determinant-nonzero sheet has the
full-frame chart data attached to that selected frame. -/
noncomputable def sourceOrientedFullFrameMaxRankChartData_of_selectedDetNonzero
    {d n : ℕ}
    (ι : Fin (d + 1) ↪ Fin n)
    {G0 : SourceOrientedGramData d n}
    (hG0 : G0 ∈ sourceOrientedGramVariety d n)
    (hdet : G0.det ι ≠ 0) :
    SourceOrientedFullFrameMaxRankChartData d n ι G0 := by
  let z : Fin n → Fin (d + 1) → ℂ := Classical.choose hG0
  have hz : sourceOrientedMinkowskiInvariant d n z = G0 :=
    Classical.choose_spec hG0
  let M0 := sourceFullFrameMatrix d n ι z
  have hM0 : IsUnit M0.det := by
    have hdet' : (sourceOrientedMinkowskiInvariant d n z).det ι ≠ 0 := by
      simpa [hz] using hdet
    exact
      isUnit_iff_ne_zero.mpr
        (by
          simpa [M0, sourceOrientedMinkowskiInvariant,
            SourceOrientedGramData.det, sourceFullFrameDet] using hdet')
  let S := sourceFullFrameGaugeSlice_exists d hM0
  have hG0' :
      sourceOrientedMinkowskiInvariant d n z ∈ sourceOrientedGramVariety d n :=
    ⟨z, rfl⟩
  have hM0_oriented :
      sourceFullFrameOrientedGramCoord d M0 =
        sourceFullFrameOrientedCoordOfSource d n ι
          (sourceOrientedMinkowskiInvariant d n z) := by
    simpa [M0] using
      (sourceFullFrameOrientedCoordOfSource_sourceOrientedMinkowskiInvariant
        d n ι z).symm
  let T :=
    sourceFullFrameMaxRankChart_ambientShrink
      d n ι hM0 S hG0' hM0_oriented
  have C :
      SourceOrientedFullFrameMaxRankChartData d n ι
        (sourceOrientedMinkowskiInvariant d n z) :=
    T.toFullFrameMaxRankChartData_of_modelChartDomain hG0' hM0_oriented
  simpa [hz] using C

/-- A selected determinant-nonzero source-variety point supplies a finite
coordinate max-rank chart packet for the oriented source variety. -/
noncomputable def sourceOrientedMaxRankChartData_of_selectedDetNonzero
    {d n : ℕ}
    (ι : Fin (d + 1) ↪ Fin n)
    {G0 : SourceOrientedGramData d n}
    (hG0 : G0 ∈ sourceOrientedGramVariety d n)
    (hdet : G0.det ι ≠ 0) :
    Σ m : ℕ, SourceOrientedMaxRankChartData d n (M := Fin m → ℂ) G0 := by
  let Cfull :=
    sourceOrientedFullFrameMaxRankChartData_of_selectedDetNonzero
      (d := d) (n := n) ι hG0 hdet
  let M := sourceFullFrameMaxRankChartModel d n ι Cfull.M0 Cfull.slice
  let C : SourceOrientedMaxRankChartData d n (M := M) G0 :=
    Cfull.to_maxRankChart
  exact ⟨Module.finrank ℂ M, C.to_finrankCoordinateChart⟩

end BHW
