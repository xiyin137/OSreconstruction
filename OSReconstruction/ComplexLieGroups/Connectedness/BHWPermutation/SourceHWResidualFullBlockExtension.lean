import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceHWResidualFrameExtension

/-!
# Full-block bridge for residual hyperbolic extensions

The proper residual hyperbolic block branch uses a determinant repair in the
orthogonal complement of the target block.  When the completed block is the
whole ambient complex Minkowski space, that repair is unavailable.  This file
keeps the full-block branch honest: if the top-to-top block equivalence is
already known to have determinant `1`, the existing ambient determinant-one
packaging lemma supplies the residual Lorentz correction.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

/-- A block equivalence between two subspaces that are both the full ambient
space, viewed as an ambient linear equivalence. -/
noncomputable def fullBlockAmbientEquivOfTopBlock
    {d : ℕ}
    {K L : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hKtop : K = ⊤) (hLtop : L = ⊤)
    (Tblock : K ≃ₗ[ℂ] L) :
    (Fin (d + 1) → ℂ) ≃ₗ[ℂ] (Fin (d + 1) → ℂ) :=
  (Submodule.topEquiv (R := ℂ) (M := Fin (d + 1) → ℂ)).symm.trans
    ((LinearEquiv.ofEq (R := ℂ) (M := Fin (d + 1) → ℂ)
      ⊤ K hKtop.symm).trans
      (Tblock.trans
        ((LinearEquiv.ofEq (R := ℂ) (M := Fin (d + 1) → ℂ)
          L ⊤ hLtop).trans
          (Submodule.topEquiv (R := ℂ) (M := Fin (d + 1) → ℂ)))))

/-- The ambient equivalence associated to a full-block equivalence acts by the
original block equivalence. -/
theorem fullBlockAmbientEquivOfTopBlock_apply
    {d : ℕ}
    {K L : Submodule ℂ (Fin (d + 1) → ℂ)}
    (hKtop : K = ⊤) (hLtop : L = ⊤)
    (Tblock : K ≃ₗ[ℂ] L)
    (x : Fin (d + 1) → ℂ) :
    fullBlockAmbientEquivOfTopBlock hKtop hLtop Tblock x =
      (Tblock ⟨x, by rw [hKtop]; trivial⟩ :
        Fin (d + 1) → ℂ) := by
  simp [fullBlockAmbientEquivOfTopBlock]
  exact Subtype.ext rfl

/-- Full-block residual hyperbolic extension bridge.

This is the mechanical full-block companion to the proper-block constructor
`complexMinkowski_selectedResidualHyperbolicExtension_of_blockExtensionData`.
The determinant-one fact is an explicit hypothesis; the later
source-oriented/volume-family argument must provide it. -/
theorem complexMinkowski_selectedResidualHyperbolicExtension_of_fullBlockData
    {d s : ℕ}
    {M Rleft K L : Submodule ℂ (Fin (d + 1) → ℂ)}
    {q : Fin s → Fin (d + 1) → ℂ}
    (hKtop : K = ⊤) (hLtop : L = ⊤)
    (Tblock : K ≃ₗ[ℂ] L)
    (hT :
      ∀ x y : K,
        sourceComplexMinkowskiInner d
          (Tblock x : Fin (d + 1) → ℂ)
          (Tblock y : Fin (d + 1) → ℂ) =
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (y : Fin (d + 1) → ℂ))
    (hdet :
      LinearMap.det
        (fullBlockAmbientEquivOfTopBlock hKtop hLtop Tblock).toLinearMap =
          1)
    (hK_M : M ≤ K)
    (hK_left : Rleft ≤ K)
    (hT_M :
      ∀ m : M,
        (Tblock ⟨(m : Fin (d + 1) → ℂ), hK_M m.2⟩ :
          Fin (d + 1) → ℂ) =
        (m : Fin (d + 1) → ℂ))
    (hT_left_span :
      ∀ x : Rleft,
        (Tblock ⟨(x : Fin (d + 1) → ℂ), hK_left x.2⟩ :
          Fin (d + 1) → ℂ) ∈
        Submodule.span ℂ (Set.range q)) :
    ∃ Λfix : ComplexLorentzGroup d,
      (∀ m : M,
        complexLorentzVectorAction Λfix
          (m : Fin (d + 1) → ℂ) =
        (m : Fin (d + 1) → ℂ)) ∧
      ∀ x : Rleft,
        complexLorentzVectorAction Λfix
          (x : Fin (d + 1) → ℂ) ∈
        Submodule.span ℂ (Set.range q) := by
  let E := fullBlockAmbientEquivOfTopBlock hKtop hLtop Tblock
  have hE_apply :
      ∀ x : Fin (d + 1) → ℂ,
        E x =
          (Tblock ⟨x, by rw [hKtop]; trivial⟩ :
            Fin (d + 1) → ℂ) := by
    intro x
    exact fullBlockAmbientEquivOfTopBlock_apply hKtop hLtop Tblock x
  apply
    complexMinkowski_selectedResidualHyperbolicExtension_of_ambientLinearEquiv
      (d := d) (M := M) (Rleft := Rleft) (q := q)
      E
  · intro x y
    rw [hE_apply x, hE_apply y]
    exact hT _ _
  · exact hdet
  · intro m
    calc
      E (m : Fin (d + 1) → ℂ) =
          (Tblock ⟨(m : Fin (d + 1) → ℂ), by rw [hKtop]; trivial⟩ :
            Fin (d + 1) → ℂ) := hE_apply _
      _ =
          (Tblock ⟨(m : Fin (d + 1) → ℂ), hK_M m.2⟩ :
            Fin (d + 1) → ℂ) := by
            congr 1
      _ = (m : Fin (d + 1) → ℂ) := hT_M m
  · intro x
    have hx :
        (⟨(x : Fin (d + 1) → ℂ), by rw [hKtop]; trivial⟩ : K) =
          ⟨(x : Fin (d + 1) → ℂ), hK_left x.2⟩ := by
      exact Subtype.ext rfl
    rw [hE_apply (x : Fin (d + 1) → ℂ)]
    simpa [hx] using hT_left_span x

/-- Full-block residual hyperbolic extension from an explicitly oriented
completed full-rank tuple.

This is the honest full-block consumer: instead of hiding the determinant-one
condition as a raw hypothesis, it asks for a full-rank tuple of completed-frame
vectors whose oriented source invariant is preserved by the ambient
top-to-top block equivalence. -/
theorem complexMinkowski_selectedResidualHyperbolicExtension_of_fullBlockOrientedTuple
    {d s m : ℕ}
    {M Rleft K L : Submodule ℂ (Fin (d + 1) → ℂ)}
    {q : Fin s → Fin (d + 1) → ℂ}
    (hKtop : K = ⊤) (hLtop : L = ⊤)
    (Tblock : K ≃ₗ[ℂ] L)
    (hT :
      ∀ x y : K,
        sourceComplexMinkowskiInner d
          (Tblock x : Fin (d + 1) → ℂ)
          (Tblock y : Fin (d + 1) → ℂ) =
        sourceComplexMinkowskiInner d
          (x : Fin (d + 1) → ℂ)
          (y : Fin (d + 1) → ℂ))
    {z w : Fin m → Fin (d + 1) → ℂ}
    (hfull :
      sourceGramMatrixRank m (sourceMinkowskiGram d m z) = d + 1)
    (horiented :
      sourceOrientedMinkowskiInvariant d m z =
        sourceOrientedMinkowskiInvariant d m w)
    (hT_tuple :
      ∀ i,
        fullBlockAmbientEquivOfTopBlock hKtop hLtop Tblock (z i) = w i)
    (hK_M : M ≤ K)
    (hK_left : Rleft ≤ K)
    (hT_M :
      ∀ m : M,
        (Tblock ⟨(m : Fin (d + 1) → ℂ), hK_M m.2⟩ :
          Fin (d + 1) → ℂ) =
        (m : Fin (d + 1) → ℂ))
    (hT_left_span :
      ∀ x : Rleft,
        (Tblock ⟨(x : Fin (d + 1) → ℂ), hK_left x.2⟩ :
          Fin (d + 1) → ℂ) ∈
        Submodule.span ℂ (Set.range q)) :
    ∃ Λfix : ComplexLorentzGroup d,
      (∀ m : M,
        complexLorentzVectorAction Λfix
          (m : Fin (d + 1) → ℂ) =
        (m : Fin (d + 1) → ℂ)) ∧
      ∀ x : Rleft,
        complexLorentzVectorAction Λfix
          (x : Fin (d + 1) → ℂ) ∈
        Submodule.span ℂ (Set.range q) := by
  let E := fullBlockAmbientEquivOfTopBlock hKtop hLtop Tblock
  have hE_apply :
      ∀ x : Fin (d + 1) → ℂ,
        E x =
          (Tblock ⟨x, by rw [hKtop]; trivial⟩ :
            Fin (d + 1) → ℂ) := by
    intro x
    exact fullBlockAmbientEquivOfTopBlock_apply hKtop hLtop Tblock x
  have hE_preserves :
      ∀ x y,
        sourceComplexMinkowskiInner d (E x) (E y) =
          sourceComplexMinkowskiInner d x y := by
    intro x y
    rw [hE_apply x, hE_apply y]
    exact hT _ _
  have hdet : LinearMap.det E.toLinearMap = 1 :=
    linearEquiv_det_one_of_same_sourceOrientedInvariant_fullRank
      d m hfull horiented E hE_preserves hT_tuple
  exact
    complexMinkowski_selectedResidualHyperbolicExtension_of_fullBlockData
      (d := d) (s := s) (M := M) (Rleft := Rleft)
      (K := K) (L := L) (q := q)
      hKtop hLtop Tblock hT hdet hK_M hK_left hT_M hT_left_span

end BHW
