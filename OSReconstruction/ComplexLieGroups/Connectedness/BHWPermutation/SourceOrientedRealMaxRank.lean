import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedReal
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedFullFrameChart

/-!
# Real source full-frame determinant and oriented max rank

This file contains the finite-coordinate bridge used by the oriented real-patch
route: a real source tuple with one nonzero selected full-frame determinant maps
to the max-rank stratum of the oriented source invariant variety.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- Selecting full-frame oriented coordinates from a real source invariant
agrees with complexifying the real selected full-frame matrix. -/
theorem sourceFullFrameOrientedCoordOfSource_sourceRealOrientedMinkowskiInvariant
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (x : Fin n → Fin (d + 1) → ℝ) :
    sourceFullFrameOrientedCoordOfSource d n ι
        (sourceRealOrientedMinkowskiInvariant d n x) =
      sourceFullFrameOrientedGramCoord d
        ((sourceRealFullFrameMatrix d n ι x).map Complex.ofReal) := by
  rw [sourceRealOrientedMinkowskiInvariant]
  rw [sourceFullFrameOrientedCoordOfSource_sourceOrientedMinkowskiInvariant]
  congr 1

/-- Real mixed Gram rows against the selected full frame. -/
def sourceRealSelectedMixedRows
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (x : Fin n → Fin (d + 1) → ℝ) :
    sourceComplementIndex ι → Fin (d + 1) → ℝ :=
  fun k a => sourceRealMinkowskiGram d n x k.1 (ι a)

@[simp]
theorem sourceRealSelectedMixedRows_apply
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (x : Fin n → Fin (d + 1) → ℝ)
    (k : sourceComplementIndex ι)
    (a : Fin (d + 1)) :
    sourceRealSelectedMixedRows d n ι x k a =
      sourceRealMinkowskiGram d n x k.1 (ι a) :=
  rfl

/-- The real mixed-row coordinate projection is continuous. -/
theorem continuous_sourceRealSelectedMixedRows
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n) :
    Continuous (sourceRealSelectedMixedRows d n ι) := by
  unfold sourceRealSelectedMixedRows sourceRealMinkowskiGram
  apply continuous_pi
  intro k
  apply continuous_pi
  intro a
  fun_prop

/-- The real linear map sending a source row to its mixed Gram row against an
invertible selected full frame. -/
def sourceRealFullFrameMixedRowMap
    (d : ℕ)
    (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    (Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin (d + 1) → ℝ) :=
  Matrix.toLin' (M * LorentzLieGroup.minkowskiMatrix d)

/-- For a nondegenerate selected real full frame, the map from an unselected
source row to its mixed Gram row against that frame is a linear equivalence. -/
noncomputable def sourceRealFullFrameMixedRowLinearEquiv
    (d : ℕ)
    (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hM : M.det ≠ 0) :
    (Fin (d + 1) → ℝ) ≃ₗ[ℝ] (Fin (d + 1) → ℝ) := by
  let η := LorentzLieGroup.minkowskiMatrix d
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  have hleft : (η * M⁻¹) * (M * η) = 1 := by
    calc
      (η * M⁻¹) * (M * η) = η * (M⁻¹ * M) * η := by
        noncomm_ring
      _ = η * 1 * η := by
        rw [Matrix.nonsing_inv_mul M hMu]
      _ = 1 := by
        simp [η, LorentzLieGroup.minkowskiMatrix_sq]
  have hright : (M * η) * (η * M⁻¹) = 1 := by
    calc
      (M * η) * (η * M⁻¹) = M * (η * η) * M⁻¹ := by
        noncomm_ring
      _ = M * 1 * M⁻¹ := by
        rw [show η * η = 1 by
          simp [η, LorentzLieGroup.minkowskiMatrix_sq]]
      _ = 1 := by
        simpa using Matrix.mul_nonsing_inv M hMu
  exact
    { toLinearMap := sourceRealFullFrameMixedRowMap d M
      invFun := Matrix.toLin' (η * M⁻¹)
      left_inv := fun v => by
        show
          (Matrix.toLin' (η * M⁻¹)) ((Matrix.toLin' (M * η)) v) = v
        rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hleft,
          Matrix.toLin'_one]
        simp
      right_inv := fun v => by
        show
          (Matrix.toLin' (M * η)) ((Matrix.toLin' (η * M⁻¹)) v) = v
        rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hright,
          Matrix.toLin'_one]
        simp }

/-- The rowwise linear equivalence is exactly the mixed Minkowski pairing
against the selected full frame. -/
theorem sourceRealFullFrameMixedRowLinearEquiv_apply
    (d : ℕ)
    (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hM : M.det ≠ 0)
    (v : Fin (d + 1) → ℝ)
    (a : Fin (d + 1)) :
    sourceRealFullFrameMixedRowLinearEquiv d M hM v a =
      ∑ μ : Fin (d + 1),
        MinkowskiSpace.metricSignature d μ * v μ * M a μ := by
  simp [sourceRealFullFrameMixedRowLinearEquiv,
    sourceRealFullFrameMixedRowMap, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct, LorentzLieGroup.minkowskiMatrix,
    LorentzLieGroup.minkowskiSignature, MinkowskiSpace.metricSignature,
    Matrix.diagonal_apply, mul_comm]

/-- Each unselected real source row maps to its selected mixed Gram row by the
linear equivalence determined by the selected full frame. -/
theorem sourceRealSelectedMixedRows_tail_eq_mixedRowLinearEquiv
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {x : Fin n → Fin (d + 1) → ℝ}
    (hdet : sourceRealFullFrameDet d n ι x ≠ 0)
    (k : sourceComplementIndex ι) :
    sourceRealSelectedMixedRows d n ι x k =
      sourceRealFullFrameMixedRowLinearEquiv d
        (sourceRealFullFrameMatrix d n ι x) hdet (x k.1) := by
  ext a
  rw [sourceRealFullFrameMixedRowLinearEquiv_apply]
  simp [sourceRealSelectedMixedRows, sourceRealMinkowskiGram,
    sourceRealFullFrameMatrix, mul_comm, mul_assoc]

/-- Apply the selected-frame mixed-row map to every complement row. -/
def sourceRealFullFrameTailMixedRowsMap
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    (sourceComplementIndex ι → Fin (d + 1) → ℝ) →ₗ[ℝ]
      (sourceComplementIndex ι → Fin (d + 1) → ℝ) where
  toFun T := fun k => sourceRealFullFrameMixedRowMap d M (T k)
  map_add' := by
    intro T U
    ext k a
    simp
  map_smul' := by
    intro c T
    ext k a
    simp

/-- The full tail block maps linearly and invertibly to the selected mixed-row
block when the selected frame is nondegenerate. -/
noncomputable def sourceRealFullFrameTailMixedRowsLinearEquiv
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hM : M.det ≠ 0) :
    (sourceComplementIndex ι → Fin (d + 1) → ℝ) ≃ₗ[ℝ]
      (sourceComplementIndex ι → Fin (d + 1) → ℝ) where
  toLinearMap := sourceRealFullFrameTailMixedRowsMap d n ι M
  invFun T := fun k => (sourceRealFullFrameMixedRowLinearEquiv d M hM).symm (T k)
  left_inv := by
    intro T
    ext k a
    exact
      congrFun
        ((sourceRealFullFrameMixedRowLinearEquiv d M hM).left_inv (T k)) a
  right_inv := by
    intro T
    ext k a
    exact
      congrFun
        ((sourceRealFullFrameMixedRowLinearEquiv d M hM).right_inv (T k)) a

/-- The tail-block linear equivalence is applied rowwise. -/
theorem sourceRealFullFrameTailMixedRowsLinearEquiv_apply
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hM : M.det ≠ 0)
    (T : sourceComplementIndex ι → Fin (d + 1) → ℝ)
    (k : sourceComplementIndex ι) :
    sourceRealFullFrameTailMixedRowsLinearEquiv d n ι M hM T k =
      sourceRealFullFrameMixedRowLinearEquiv d M hM (T k) :=
  rfl

/-- The selected mixed-row block of a real source tuple is the tail-block
linear equivalence applied to the unselected source rows. -/
theorem sourceRealSelectedMixedRows_eq_tailMixedRowsLinearEquiv
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {x : Fin n → Fin (d + 1) → ℝ}
    (hdet : sourceRealFullFrameDet d n ι x ≠ 0) :
    sourceRealSelectedMixedRows d n ι x =
      sourceRealFullFrameTailMixedRowsLinearEquiv d n ι
        (sourceRealFullFrameMatrix d n ι x) hdet (fun k => x k.1) := by
  ext k a
  exact congrFun
    (sourceRealSelectedMixedRows_tail_eq_mixedRowLinearEquiv d n ι hdet k) a

/-- Split a real source tuple into its selected full-frame matrix and the
remaining unselected rows. -/
noncomputable def sourceRealFullFrameSplitEquiv
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n) :
    (Fin n → Fin (d + 1) → ℝ) ≃
      (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
        (sourceComplementIndex ι → Fin (d + 1) → ℝ)) where
  toFun x :=
    (sourceRealFullFrameMatrix d n ι x, fun k => x k.1)
  invFun p :=
    fun j μ =>
      if hj : j ∈ Set.range ι then
        p.1 (sourceSelectedIndexOfMem ι hj) μ
      else
        p.2 ⟨j, hj⟩ μ
  left_inv := by
    intro x
    ext j μ
    by_cases hj : j ∈ Set.range ι
    · have hidx := sourceSelectedIndexOfMem_spec ι hj
      simp [sourceRealFullFrameMatrix, hj, hidx]
    · simp [hj]
  right_inv := by
    intro p
    rcases p with ⟨M, T⟩
    apply Prod.ext
    · ext a μ
      have hmem : ι a ∈ Set.range ι := ⟨a, rfl⟩
      have hidx : sourceSelectedIndexOfMem ι hmem = a := by
        apply ι.injective
        exact sourceSelectedIndexOfMem_spec ι hmem
      simp [sourceRealFullFrameMatrix, hmem, hidx]
    · ext k μ
      simp [k.2]

/-- The selected-frame/complement-row split is a finite-dimensional
homeomorphism. -/
noncomputable def sourceRealFullFrameSplitHomeomorph
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n) :
    (Fin n → Fin (d + 1) → ℝ) ≃ₜ
      (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
        (sourceComplementIndex ι → Fin (d + 1) → ℝ)) where
  toEquiv := sourceRealFullFrameSplitEquiv d n ι
  continuous_toFun := by
    apply Continuous.prodMk
    · exact continuous_sourceRealFullFrameMatrix d n ι
    · apply continuous_pi
      intro k
      apply continuous_pi
      intro μ
      exact (continuous_apply μ).comp (continuous_apply k.1)
  continuous_invFun := by
    apply continuous_pi
    intro j
    apply continuous_pi
    intro μ
    by_cases hj : ∃ y, ι y = j
    · let hmem : j ∈ Set.range ι := hj
      have hrow :
          Continuous
            (fun p : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
                (sourceComplementIndex ι → Fin (d + 1) → ℝ) =>
              p.1 (sourceSelectedIndexOfMem ι hmem)) :=
        (continuous_apply (sourceSelectedIndexOfMem ι hmem)).comp
          continuous_fst
      simpa [sourceRealFullFrameSplitEquiv, Set.mem_range, hj, hmem] using
        (continuous_apply μ).comp hrow
    · have hmem : j ∉ Set.range ι := by
        simpa [Set.mem_range] using hj
      have hrow :
          Continuous
            (fun p : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
                (sourceComplementIndex ι → Fin (d + 1) → ℝ) =>
              p.2 (⟨j, hmem⟩ : sourceComplementIndex ι)) :=
        (continuous_apply (⟨j, hmem⟩ : sourceComplementIndex ι)).comp
          continuous_snd
      simpa [sourceRealFullFrameSplitEquiv, Set.mem_range, hj, hmem] using
        (continuous_apply μ).comp hrow

/-- The split homeomorphism exposes exactly the selected frame and complement
rows. -/
theorem sourceRealFullFrameSplitHomeomorph_apply
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (x : Fin n → Fin (d + 1) → ℝ) :
    sourceRealFullFrameSplitHomeomorph d n ι x =
      (sourceRealFullFrameMatrix d n ι x, fun k => x k.1) :=
  rfl

/-- The inverse split recovers selected rows from the frame matrix. -/
theorem sourceRealFullFrameSplitHomeomorph_symm_apply_selected
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (p : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
      (sourceComplementIndex ι → Fin (d + 1) → ℝ))
    (a μ : Fin (d + 1)) :
    (sourceRealFullFrameSplitHomeomorph d n ι).symm p (ι a) μ =
      p.1 a μ := by
  have hmem : ι a ∈ Set.range ι := ⟨a, rfl⟩
  have hidx : sourceSelectedIndexOfMem ι hmem = a := by
    apply ι.injective
    exact sourceSelectedIndexOfMem_spec ι hmem
  simp [sourceRealFullFrameSplitHomeomorph, sourceRealFullFrameSplitEquiv,
    hidx]

/-- The inverse split recovers complement rows from the complement component. -/
theorem sourceRealFullFrameSplitHomeomorph_symm_apply_complement
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (p : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
      (sourceComplementIndex ι → Fin (d + 1) → ℝ))
    (k : sourceComplementIndex ι)
    (μ : Fin (d + 1)) :
    (sourceRealFullFrameSplitHomeomorph d n ι).symm p k.1 μ =
      p.2 k μ := by
  have hnot : ¬ ∃ x, ι x = (k.1 : Fin n) := by
    simpa [Set.mem_range] using k.2
  simp [sourceRealFullFrameSplitHomeomorph, sourceRealFullFrameSplitEquiv,
    Set.mem_range, hnot]

/-- Selecting mixed-row coordinates from a real source invariant agrees with
complexifying the real selected mixed rows. -/
theorem sourceSelectedMixedRows_sourceRealOrientedMinkowskiInvariant
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (x : Fin n → Fin (d + 1) → ℝ) :
    sourceSelectedMixedRows d n ι
        (sourceRealOrientedMinkowskiInvariant d n x) =
      fun k a => (sourceRealSelectedMixedRows d n ι x k a : ℂ) := by
  ext k a
  rw [sourceSelectedMixedRows_apply]
  rw [sourceRealOrientedMinkowskiInvariant_gram]
  rfl

/-- A real source tuple with a nonzero selected full-frame determinant has
maximal oriented source rank after applying the real oriented invariant. -/
theorem sourceOrientedMaxRankAt_sourceReal_fullFrameDet_ne_zero
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {x : Fin n → Fin (d + 1) → ℝ}
    (hdet : sourceRealFullFrameDet d n ι x ≠ 0) :
    SourceOrientedMaxRankAt d n
      (sourceRealOrientedMinkowskiInvariant d n x) := by
  apply sourceOrientedMaxRankAt_of_selectedDet_ne_zero d n ι
  · exact sourceRealOrientedMinkowskiInvariant_mem_variety d n x
  · rw [sourceRealOrientedMinkowskiInvariant_det]
    exact_mod_cast hdet

end BHW
