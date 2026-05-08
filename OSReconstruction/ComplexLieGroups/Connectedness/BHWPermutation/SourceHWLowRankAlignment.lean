import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceHWSelectedProjection
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceHWTubeCoefficient
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceHWSingularLimit

/-!
# Hall-Wightman low-rank selected-span alignment data

This file records the finite-dimensional data surfaces immediately below the
low-rank singular normal form.  The producer of these structures is still the
hard Hall-Wightman geometry; the checked theorem here packages the residual
subspaces once the selected-span alignment fields are available.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

/-- The range of the source coefficient-evaluation map is exactly the span of
the source tuple. -/
theorem sourceCoefficientEval_range_eq_span
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    LinearMap.range (sourceCoefficientEval d n z) =
      Submodule.span ℂ (Set.range z) := by
  apply le_antisymm
  · rintro v ⟨a, rfl⟩
    simp only [sourceCoefficientEval, LinearMap.coe_mk, AddHom.coe_mk]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ (a i) (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    exact ⟨Pi.single i 1, sourceCoefficientEval_single d n z i⟩

/-- A nonzero selected principal Gram minor says that the selected tuple has
full scalar Gram rank equal to the number of selected vectors. -/
theorem sourceGramMatrixRank_selectedTuple_eq_of_principal_minor_ne
    (d n r : ℕ)
    {z : Fin n → Fin (d + 1) → ℂ}
    {I : Fin r → Fin n}
    (hminor :
      sourceMatrixMinor n r I I (sourceMinkowskiGram d n z) ≠ 0) :
    sourceGramMatrixRank r
      (sourceMinkowskiGram d r fun a : Fin r => z (I a)) = r := by
  let A : Matrix (Fin r) (Fin r) ℂ :=
    fun a b => sourceMinkowskiGram d n z (I a) (I b)
  have hdetA : A.det ≠ 0 := by
    simpa [A, sourceMatrixMinor] using hminor
  have hli : LinearIndependent ℂ fun a : Fin r => A.row a :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdetA
  have hspan :
      Module.finrank ℂ (Submodule.span ℂ (Set.range fun a : Fin r => A.row a)) =
        r := by
    simpa using finrank_span_eq_card (R := ℂ)
      (b := fun a : Fin r => A.row a) hli
  have hrank_rows :
      A.rank =
        Module.finrank ℂ
          (Submodule.span ℂ (Set.range fun a : Fin r => A.row a)) := by
    rw [Matrix.rank_eq_finrank_span_row]
  calc
    sourceGramMatrixRank r
        (sourceMinkowskiGram d r fun a : Fin r => z (I a)) = A.rank := by
          rfl
    _ = r := hrank_rows.trans hspan

/-- Linear algebra inside the low-rank branch: after choosing a nonzero
principal scalar block, the equal Gram data determine the same selected
coefficients and residual radical pairings. -/
structure HWLowRankSelectedSpanFrame
    (d n r : ℕ)
    (z w : Fin n → Fin (d + 1) → ℂ)
    (I : Fin r → Fin n) where
  I_injective : Function.Injective I
  principal_minor_ne :
    sourceMatrixMinor n r I I (sourceMinkowskiGram d n z) ≠ 0
  selected_gram_eq :
    ∀ a b,
      sourceMinkowskiGram d n z (I a) (I b) =
        sourceMinkowskiGram d n w (I a) (I b)
  coeff : Fin n → Fin r → ℂ
  left_residual_orth :
    ∀ i a,
      sourceComplexMinkowskiInner d
        (z i - ∑ b : Fin r, coeff i b • z (I b))
        (z (I a)) = 0
  right_residual_orth :
    ∀ i a,
      sourceComplexMinkowskiInner d
        (w i - ∑ b : Fin r, coeff i b • w (I b))
        (w (I a)) = 0
  residual_pairing_eq :
    ∀ i j,
      sourceComplexMinkowskiInner d
        (z i - ∑ b : Fin r, coeff i b • z (I b))
        (z j - ∑ b : Fin r, coeff j b • z (I b)) =
      sourceComplexMinkowskiInner d
        (w i - ∑ b : Fin r, coeff i b • w (I b))
        (w j - ∑ b : Fin r, coeff j b • w (I b))
  left_residual_pair_zero :
    ∀ i j,
      sourceComplexMinkowskiInner d
        (z i - ∑ b : Fin r, coeff i b • z (I b))
        (z j - ∑ b : Fin r, coeff j b • z (I b)) = 0
  right_residual_pair_zero :
    ∀ i j,
      sourceComplexMinkowskiInner d
        (w i - ∑ b : Fin r, coeff i b • w (I b))
        (w j - ∑ b : Fin r, coeff j b • w (I b)) = 0

/-- A selected-span frame together with the rank and selected principal
indices used to build it. -/
structure HWLowRankSelectedSpanFrameData
    (d n : ℕ)
    (z w : Fin n → Fin (d + 1) → ℂ) where
  r : ℕ
  I : Fin r → Fin n
  rank_eq : r = sourceGramMatrixRank n (sourceMinkowskiGram d n z)
  frame : HWLowRankSelectedSpanFrame d n r z w I

/-- Data obtained after the selected nondegenerate spans have been matched by
a determinant-one complex Lorentz transformation.  The common selected span is
the target span; only after applying `Λsel` to the left endpoint do the two
residual families live in the same orthogonal complement. -/
structure HWLowRankSelectedSpanAlignment
    (d n r : ℕ)
    (z w : Fin n → Fin (d + 1) → ℂ)
    (I : Fin r → Fin n)
    (S : HWLowRankSelectedSpanFrame d n r z w I) where
  M : Submodule ℂ (Fin (d + 1) → ℂ)
  Λsel : ComplexLorentzGroup d
  ξ : Fin n → Fin (d + 1) → ℂ
  leftResidual : Fin n → Fin (d + 1) → ℂ
  rightResidual : Fin n → Fin (d + 1) → ℂ
  M_eq : M = Submodule.span ℂ (Set.range fun a : Fin r => w (I a))
  M_nondeg : ComplexMinkowskiNondegenerateSubspace d M
  selected_mem : ∀ a, w (I a) ∈ M
  Λsel_selected :
    ∀ a, complexLorentzVectorAction Λsel (z (I a)) = w (I a)
  ξ_eq : ∀ i, ξ i = ∑ b : Fin r, S.coeff i b • w (I b)
  ξ_mem : ∀ i, ξ i ∈ M
  leftResidual_eq :
    ∀ i, leftResidual i = complexLorentzVectorAction Λsel (z i) - ξ i
  rightResidual_eq : ∀ i, rightResidual i = w i - ξ i
  left_decomp :
    ∀ i, complexLorentzVectorAction Λsel (z i) = ξ i + leftResidual i
  right_decomp : ∀ i, w i = ξ i + rightResidual i
  left_residual_orth_M :
    ∀ i (m : M),
      sourceComplexMinkowskiInner d (leftResidual i)
        (m : Fin (d + 1) → ℂ) = 0
  right_residual_orth_M :
    ∀ i (m : M),
      sourceComplexMinkowskiInner d (rightResidual i)
        (m : Fin (d + 1) → ℂ) = 0
  left_residual_pair_zero :
    ∀ i j,
      sourceComplexMinkowskiInner d (leftResidual i) (leftResidual j) = 0
  right_residual_pair_zero :
    ∀ i j,
      sourceComplexMinkowskiInner d (rightResidual i) (rightResidual j) = 0

/-- Same source Gram data produce the selected-span frame packet at the
scalar Gram rank.  The residual-pairing equality is obtained after both
residual pairings are proved to vanish by the selected Schur-complement zero
theorem. -/
def hw_lowRank_selectedSpanFrame_of_sameSourceGram
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w) :
    HWLowRankSelectedSpanFrameData d n z w := by
  classical
  let G : Fin n → Fin n → ℂ := sourceMinkowskiGram d n z
  let r : ℕ := sourceGramMatrixRank n G
  have hGsym : G ∈ sourceSymmetricMatrixSpace n := by
    intro i j
    exact sourceMinkowskiGram_symm d n z i j
  have hrank : (Matrix.of fun i j : Fin n => G i j).rank = r := by
    have hM : (Matrix.of fun i j : Fin n => G i j) = G := by
      ext i j
      rfl
    rw [hM]
    simp [sourceGramMatrixRank, r]
  let hExists :=
    exists_sourcePrincipalMinor_ne_zero_of_sourceSymmetricRank hGsym hrank
  let I : Fin r → Fin n := Classical.choose hExists
  have hI : Function.Injective I := (Classical.choose_spec hExists).1
  have hminor : sourceMatrixMinor n r I I G ≠ 0 :=
    (Classical.choose_spec hExists).2
  let coeff : Fin n → Fin r → ℂ :=
    hw_selectedSpanCoeff n r I G
  have hminorW :
      sourceMatrixMinor n r I I (sourceMinkowskiGram d n w) ≠ 0 := by
    simpa [G, hgram] using hminor
  have hrankZ :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z) = r := by
    rfl
  have hrankW :
      sourceGramMatrixRank n (sourceMinkowskiGram d n w) = r := by
    simpa [G, r] using congrArg (sourceGramMatrixRank n) hgram.symm
  have hleft_pair_zero :
      ∀ i j,
        sourceComplexMinkowskiInner d
          (z i - ∑ b : Fin r, coeff i b • z (I b))
          (z j - ∑ b : Fin r, coeff j b • z (I b)) = 0 := by
    intro i j
    simpa [coeff, G, hwLemma3_selectedResidual, hwLemma3_selectedProjection]
      using
        hwLemma3_selectedResidual_inner_residual_eq_zero
          d n r I z hrankZ hminor i j
  have hright_pair_zero :
      ∀ i j,
        sourceComplexMinkowskiInner d
          (w i - ∑ b : Fin r, coeff i b • w (I b))
          (w j - ∑ b : Fin r, coeff j b • w (I b)) = 0 := by
    intro i j
    simpa [coeff, G, hgram, hwLemma3_selectedResidual,
      hwLemma3_selectedProjection]
      using
        hwLemma3_selectedResidual_inner_residual_eq_zero
          d n r I w hrankW hminorW i j
  exact
    { r := r
      I := I
      rank_eq := rfl
      frame :=
        { I_injective := hI
          principal_minor_ne := by
            simpa [G] using hminor
          selected_gram_eq := by
            intro a b
            exact congrFun (congrFun hgram (I a)) (I b)
          coeff := coeff
          left_residual_orth := by
            intro i a
            simpa [coeff, G, hwLemma3_selectedResidual,
              hwLemma3_selectedProjection]
              using hwLemma3_selectedResidual_inner_head d n r I z hminor i a
          right_residual_orth := by
            intro i a
            simpa [coeff, G, hgram, hwLemma3_selectedResidual,
              hwLemma3_selectedProjection]
              using hwLemma3_selectedResidual_inner_head d n r I w hminorW i a
          residual_pairing_eq := by
            intro i j
            exact (hleft_pair_zero i j).trans (hright_pair_zero i j).symm
          left_residual_pair_zero := hleft_pair_zero
          right_residual_pair_zero := hright_pair_zero } }

/-- The selected nondegenerate spans in a proper low-rank branch can be aligned
by a determinant-one complex Lorentz transformation. -/
theorem hw_lowRank_selectedSpanFrame_detOneOrbit
    (d n r : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    {I : Fin r → Fin n}
    (S : HWLowRankSelectedSpanFrame d n r z w I)
    (hproper : r < d + 1) :
    ∃ Λ : ComplexLorentzGroup d,
      ∀ a : Fin r, complexLorentzVectorAction Λ (z (I a)) = w (I a) := by
  let zI : Fin r → Fin (d + 1) → ℂ := fun a => z (I a)
  let wI : Fin r → Fin (d + 1) → ℂ := fun a => w (I a)
  have hgramI : sourceMinkowskiGram d r zI = sourceMinkowskiGram d r wI := by
    ext a b
    exact S.selected_gram_eq a b
  have hrankI :
      sourceGramMatrixRank r (sourceMinkowskiGram d r zI) = r := by
    simpa [zI] using
      sourceGramMatrixRank_selectedTuple_eq_of_principal_minor_ne
        d n r (z := z) (I := I) S.principal_minor_ne
  have hzOrbit : HWSourceGramOrbitRankAt d r zI := by
    simp [HWSourceGramOrbitRankAt, HWSourceGramOrbitRank, hrankI]
  let H : HWHighRankSpanIsometryData d r zI wI :=
    hw_highRank_spanIsometryData_of_sameSourceGram d r hzOrbit hgramI
  have hSO : HWSameSourceGramSOOrientationCompatible d r zI wI := by
    left
    simpa [HWSameSourceGramSOOrientationCompatible, hrankI] using hproper
  rcases complexMinkowski_wittExtension_detOne_of_sourceSpan d r H hSO with
  ⟨Λ, hΛ⟩
  exact ⟨Λ, hΛ⟩

/-- Align the selected nondegenerate spans and place both residual families in
the orthogonal complement of the common selected span. -/
noncomputable def hw_lowRank_selectedSpanAlignment_of_selectedSpanFrame
    (d n r : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    {I : Fin r → Fin n}
    (S : HWLowRankSelectedSpanFrame d n r z w I)
    (hproper : r < d + 1) :
    HWLowRankSelectedSpanAlignment d n r z w I S := by
  classical
  let zI : Fin r → Fin (d + 1) → ℂ := fun a => z (I a)
  let wI : Fin r → Fin (d + 1) → ℂ := fun a => w (I a)
  let orbit := hw_lowRank_selectedSpanFrame_detOneOrbit d n r S hproper
  let Λ : ComplexLorentzGroup d := Classical.choose orbit
  have hΛ :
      ∀ a : Fin r, complexLorentzVectorAction Λ (z (I a)) = w (I a) :=
    Classical.choose_spec orbit
  let M : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range wI)
  let ξ : Fin n → Fin (d + 1) → ℂ :=
    fun i => ∑ b : Fin r, S.coeff i b • w (I b)
  let leftResidual : Fin n → Fin (d + 1) → ℂ :=
    fun i => complexLorentzVectorAction Λ (z i) - ξ i
  let rightResidual : Fin n → Fin (d + 1) → ℂ :=
    fun i => w i - ξ i
  have hgramI : sourceMinkowskiGram d r zI = sourceMinkowskiGram d r wI := by
    ext a b
    exact S.selected_gram_eq a b
  have hrankI :
      sourceGramMatrixRank r (sourceMinkowskiGram d r zI) = r := by
    simpa [zI] using
      sourceGramMatrixRank_selectedTuple_eq_of_principal_minor_ne
        d n r (z := z) (I := I) S.principal_minor_ne
  have hwOrbit : HWSourceGramOrbitRankAt d r wI := by
    have hzOrbit : HWSourceGramOrbitRankAt d r zI := by
      simp [HWSourceGramOrbitRankAt, HWSourceGramOrbitRank, hrankI]
    simpa [HWSourceGramOrbitRankAt, HWSourceGramOrbitRank, hgramI] using
      (hwSourceGramOrbitRankAt_of_sourceGram_eq
        (d := d) (n := r) (z := zI) (w := wI) hgramI).1 hzOrbit
  have hM_nondeg : ComplexMinkowskiNondegenerateSubspace d M := by
    have hRange :
        LinearMap.range (sourceCoefficientEval d r wI) =
          Submodule.span ℂ (Set.range wI) :=
      sourceCoefficientEval_range_eq_span d r wI
    simpa [M, hRange] using
      hw_highRank_eval_range_nondegenerate (d := d) (n := r)
        (z := wI) hwOrbit
  have hleft_action_residual :
      ∀ i,
        leftResidual i =
          complexLorentzVectorAction Λ
            (z i - ∑ b : Fin r, S.coeff i b • z (I b)) := by
    intro i
    have hsub :
        complexLorentzVectorAction Λ
            (z i - ∑ b : Fin r, S.coeff i b • z (I b)) =
          complexLorentzVectorAction Λ (z i) -
            complexLorentzVectorAction Λ
              (∑ b : Fin r, S.coeff i b • z (I b)) := by
      ext μ
      simp [complexLorentzVectorAction, mul_sub, Finset.sum_sub_distrib]
    have hsum :
        complexLorentzVectorAction Λ
            (∑ b : Fin r, S.coeff i b • z (I b)) =
          ∑ b : Fin r, S.coeff i b • w (I b) := by
      calc
        complexLorentzVectorAction Λ
            (∑ b : Fin r, S.coeff i b • z (I b)) =
            ∑ b : Fin r,
              complexLorentzVectorAction Λ (S.coeff i b • z (I b)) := by
              rw [show
                (∑ b : Fin r,
                  complexLorentzVectorAction Λ (S.coeff i b • z (I b))) =
                    (fun μ => ∑ b : Fin r,
                      complexLorentzVectorAction Λ
                        (S.coeff i b • z (I b)) μ) by
                  exact Finset.sum_fn Finset.univ
                    (fun b : Fin r =>
                      complexLorentzVectorAction Λ (S.coeff i b • z (I b)))]
              rw [Finset.sum_fn]
              exact complexLorentzVectorAction_sum Λ
                (fun b : Fin r => S.coeff i b • z (I b))
        _ = ∑ b : Fin r,
              S.coeff i b • complexLorentzVectorAction Λ (z (I b)) := by
              apply Finset.sum_congr rfl
              intro b _
              simpa [Pi.smul_apply] using
                complexLorentzVectorAction_smul Λ (S.coeff i b) (z (I b))
        _ = ∑ b : Fin r, S.coeff i b • w (I b) := by
              apply Finset.sum_congr rfl
              intro b _
              rw [hΛ b]
    rw [hsub, hsum]
  have hleft_gen :
      ∀ i a,
        sourceComplexMinkowskiInner d (leftResidual i) (w (I a)) = 0 := by
    intro i a
    calc
      sourceComplexMinkowskiInner d (leftResidual i) (w (I a)) =
          sourceComplexMinkowskiInner d
            (complexLorentzVectorAction Λ
              (z i - ∑ b : Fin r, S.coeff i b • z (I b)))
            (complexLorentzVectorAction Λ (z (I a))) := by
              rw [hleft_action_residual i, hΛ a]
      _ =
          sourceComplexMinkowskiInner d
            (z i - ∑ b : Fin r, S.coeff i b • z (I b))
            (z (I a)) :=
              sourceComplexMinkowskiInner_complexLorentzVectorAction Λ
                (z i - ∑ b : Fin r, S.coeff i b • z (I b)) (z (I a))
      _ = 0 := S.left_residual_orth i a
  have hright_gen :
      ∀ i a,
        sourceComplexMinkowskiInner d (rightResidual i) (w (I a)) = 0 := by
    intro i a
    simpa [rightResidual, ξ] using S.right_residual_orth i a
  have hleft_pair :
      ∀ i j,
        sourceComplexMinkowskiInner d (leftResidual i) (leftResidual j) = 0 := by
    intro i j
    calc
      sourceComplexMinkowskiInner d (leftResidual i) (leftResidual j) =
          sourceComplexMinkowskiInner d
            (complexLorentzVectorAction Λ
              (z i - ∑ b : Fin r, S.coeff i b • z (I b)))
            (complexLorentzVectorAction Λ
              (z j - ∑ b : Fin r, S.coeff j b • z (I b))) := by
              rw [hleft_action_residual i, hleft_action_residual j]
      _ =
          sourceComplexMinkowskiInner d
            (z i - ∑ b : Fin r, S.coeff i b • z (I b))
            (z j - ∑ b : Fin r, S.coeff j b • z (I b)) :=
              sourceComplexMinkowskiInner_complexLorentzVectorAction Λ
                (z i - ∑ b : Fin r, S.coeff i b • z (I b))
                (z j - ∑ b : Fin r, S.coeff j b • z (I b))
      _ = 0 := S.left_residual_pair_zero i j
  have hright_pair :
      ∀ i j,
        sourceComplexMinkowskiInner d (rightResidual i) (rightResidual j) = 0 := by
    intro i j
    simpa [rightResidual, ξ] using S.right_residual_pair_zero i j
  refine
    { M := M
      Λsel := Λ
      ξ := ξ
      leftResidual := leftResidual
      rightResidual := rightResidual
      M_eq := rfl
      M_nondeg := hM_nondeg
      selected_mem := ?_
      Λsel_selected := hΛ
      ξ_eq := by intro i; rfl
      ξ_mem := ?_
      leftResidual_eq := by intro i; rfl
      rightResidual_eq := by intro i; rfl
      left_decomp := ?_
      right_decomp := ?_
      left_residual_orth_M := ?_
      right_residual_orth_M := ?_
      left_residual_pair_zero := hleft_pair
      right_residual_pair_zero := hright_pair }
  · intro a
    exact Submodule.subset_span ⟨a, rfl⟩
  · intro i
    exact Submodule.sum_mem _ fun b _ =>
      Submodule.smul_mem _ (S.coeff i b) (Submodule.subset_span ⟨b, rfl⟩)
  · intro i
    simp [leftResidual]
  · intro i
    simp [rightResidual, ξ]
  · intro i m
    refine Submodule.span_induction ?leftBase ?leftZero ?leftAdd ?leftSmul m.2
    · rintro x ⟨a, rfl⟩
      exact hleft_gen i a
    · simp [sourceComplexMinkowskiInner]
    · intro x y _ _ hx hy
      rw [sourceComplexMinkowskiInner_add_right, hx, hy, add_zero]
    · intro c x _ hx
      rw [sourceComplexMinkowskiInner_smul_right, hx, mul_zero]
  · intro i m
    refine Submodule.span_induction ?rightBase ?rightZero ?rightAdd ?rightSmul m.2
    · rintro x ⟨a, rfl⟩
      exact hright_gen i a
    · simp [sourceComplexMinkowskiInner]
    · intro x y _ _ hx hy
      rw [sourceComplexMinkowskiInner_add_right, hx, hy, add_zero]
    · intro c x _ hx
      rw [sourceComplexMinkowskiInner_smul_right, hx, mul_zero]

/-- Once the selected spans are aligned, the left and right residual families
span totally isotropic subspaces in the orthogonal complement of the common
selected span. -/
theorem hw_lowRank_residualSubspaces_after_selectedAlignment
    {d n r : ℕ}
    {z w : Fin n → Fin (d + 1) → ℂ}
    {I : Fin r → Fin n}
    {S : HWLowRankSelectedSpanFrame d n r z w I}
    (A : HWLowRankSelectedSpanAlignment d n r z w I S) :
    ∃ (Rleft Rright : Submodule ℂ (Fin (d + 1) → ℂ)),
      Rleft = Submodule.span ℂ (Set.range A.leftResidual) ∧
      Rright = Submodule.span ℂ (Set.range A.rightResidual) ∧
      (∀ x : Rleft, ∀ m : A.M,
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (m : Fin (d + 1) → ℂ) = 0) ∧
      (∀ x : Rright, ∀ m : A.M,
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (m : Fin (d + 1) → ℂ) = 0) ∧
      ComplexMinkowskiTotallyIsotropicSubspace d Rleft ∧
      ComplexMinkowskiTotallyIsotropicSubspace d Rright := by
  refine
    ⟨Submodule.span ℂ (Set.range A.leftResidual),
      Submodule.span ℂ (Set.range A.rightResidual), rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro x m
    exact
      span_frame_orthogonal_to_subspace
        (d := d) (s := n) (M := A.M) (q := A.leftResidual)
        A.left_residual_orth_M x.2 m
  · intro x m
    exact
      span_frame_orthogonal_to_subspace
        (d := d) (s := n) (M := A.M) (q := A.rightResidual)
        A.right_residual_orth_M x.2 m
  · exact
      complexMinkowskiTotallyIsotropic_span_range
        d n A.leftResidual A.left_residual_pair_zero
  · exact
      complexMinkowskiTotallyIsotropic_span_range
        d n A.rightResidual A.right_residual_pair_zero

end BHW
