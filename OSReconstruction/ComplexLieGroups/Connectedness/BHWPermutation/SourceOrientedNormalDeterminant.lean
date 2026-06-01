import Mathlib.Data.Fintype.Sort
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedNormalParameter

/-!
# Determinant support for source-oriented normal parameters

This companion file keeps determinant-specific finite linear algebra separate
from the head/tail normal-parameter bookkeeping.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open exteriorPower

namespace BHW

/-- The canonical equivalence between the head/tail sum index and the ambient
source-coordinate index. -/
def sourceHeadTailSumEquiv
    (d r : ℕ)
    (hrD : r < d + 1) :
    (Fin r ⊕ Fin (d + 1 - r)) ≃ Fin (d + 1) :=
  finSumFinEquiv.trans
    (finCongr (Nat.add_sub_of_le (Nat.le_of_lt hrD)))

@[simp]
theorem sourceHeadTailSumEquiv_inl
    (d r : ℕ)
    (hrD : r < d + 1)
    (a : Fin r) :
    sourceHeadTailSumEquiv d r hrD (Sum.inl a) =
      finSourceHead (Nat.le_of_lt hrD) a := by
  apply Fin.ext
  simp [sourceHeadTailSumEquiv, finSourceHead]

@[simp]
theorem sourceHeadTailSumEquiv_inr
    (d r : ℕ)
    (hrD : r < d + 1)
    (u : Fin (d + 1 - r)) :
    sourceHeadTailSumEquiv d r hrD (Sum.inr u) =
      finSourceTail (Nat.le_of_lt hrD) u := by
  apply Fin.ext
  simp [sourceHeadTailSumEquiv, finSourceTail]

@[simp]
theorem sourceOrientedNormalHeadVector_headCoord
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (a b : Fin r) :
    sourceOrientedNormalHeadVector d n r hrD hrn p a
        (finSourceHead (Nat.le_of_lt hrD) b) = p.head a b := by
  rw [sourceOrientedNormalHeadVector]
  rw [Finset.sum_eq_single b]
  · rw [hwLemma3CanonicalSource_head_head
      (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)]
    simp
  · intro c _hc hcb
    rw [hwLemma3CanonicalSource_head_head
      (d := d) (n := n) (r := r) (hrD := hrD) (hrn := hrn)]
    simp [hcb]
  · intro hb
    simp at hb

@[simp]
theorem sourceOrientedNormalHeadVector_tailCoord
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (a : Fin r)
    (u : Fin (d + 1 - r)) :
    sourceOrientedNormalHeadVector d n r hrD hrn p a
        (finSourceTail (Nat.le_of_lt hrD) u) = 0 := by
  rw [sourceOrientedNormalHeadVector]
  simp

/-- Shifted residual-tail oriented coordinates: the shifted Gram matrix and all
top residual-tail determinants. -/
structure SourceShiftedTailOrientedData
    (d r : ℕ)
    (hrD : r < d + 1)
    (m : ℕ) where
  gram : Matrix (Fin m) (Fin m) ℂ
  det : (Fin (d + 1 - r) ↪ Fin m) → ℂ

/-- The shifted-tail oriented invariant of a residual-tail source tuple. -/
def sourceShiftedTailOrientedInvariant
    (d r : ℕ)
    (hrD : r < d + 1)
    (m : ℕ)
    (q : Fin m → Fin (d + 1 - r) → ℂ) :
    SourceShiftedTailOrientedData d r hrD m where
  gram := sourceShiftedTailGram d r hrD m q
  det := fun lam => Matrix.det (fun u μ : Fin (d + 1 - r) => q (lam u) μ)

@[simp]
theorem sourceShiftedTailOrientedInvariant_gram
    (d r : ℕ)
    (hrD : r < d + 1)
    (m : ℕ)
    (q : Fin m → Fin (d + 1 - r) → ℂ) :
    (sourceShiftedTailOrientedInvariant d r hrD m q).gram =
      sourceShiftedTailGram d r hrD m q := by
  rfl

@[simp]
theorem sourceShiftedTailOrientedInvariant_det
    (d r : ℕ)
    (hrD : r < d + 1)
    (m : ℕ)
    (q : Fin m → Fin (d + 1 - r) → ℂ)
    (lam : Fin (d + 1 - r) ↪ Fin m) :
    (sourceShiftedTailOrientedInvariant d r hrD m q).det lam =
      Matrix.det (fun u μ : Fin (d + 1 - r) => q (lam u) μ) := by
  rfl

theorem sourceFullFrameMatrix_normalParameter_headTail_blocks
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (lam : Fin (d + 1 - r) ↪ Fin (n - r)) :
    Matrix.reindex
        (sourceHeadTailSumEquiv d r hrD).symm
        (sourceHeadTailSumEquiv d r hrD).symm
        (sourceFullFrameMatrix d n
          (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam)
          (sourceOrientedNormalParameterVector d n r hrD hrn p)) =
      Matrix.fromBlocks
        p.head
        (0 : Matrix (Fin r) (Fin (d + 1 - r)) ℂ)
        ((p.mixed.submatrix lam id) * p.head)
        (fun u μ => p.tail (lam u) μ) := by
  ext row col
  cases row with
  | inl a =>
      cases col with
      | inl b =>
          simp [sourceFullFrameMatrix, sourceOrientedNormalParameterVector_head]
      | inr μ =>
          simp [sourceFullFrameMatrix, sourceOrientedNormalParameterVector_head]
  | inr u =>
      cases col with
      | inl b =>
          simp [sourceFullFrameMatrix, sourceOrientedNormalParameterVector_tail,
            Matrix.mul_apply]
      | inr μ =>
          simp [sourceFullFrameMatrix, sourceOrientedNormalParameterVector_tail]

theorem sourceFullFrameDet_normalParameter_headTail_raw
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (lam : Fin (d + 1 - r) ↪ Fin (n - r)) :
    sourceFullFrameDet d n
        (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam)
        (sourceOrientedNormalParameterVector d n r hrD hrn p) =
      p.head.det *
        Matrix.det (fun u μ : Fin (d + 1 - r) => p.tail (lam u) μ) := by
  have hblocks :=
    sourceFullFrameMatrix_normalParameter_headTail_blocks d n r hrD hrn p lam
  have hdet := congrArg Matrix.det hblocks
  rw [Matrix.det_reindex_self] at hdet
  simpa [sourceFullFrameDet] using hdet

theorem sourceFullFrameDet_normalParameter_headTail
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (lam : Fin (d + 1 - r) ↪ Fin (n - r)) :
    sourceFullFrameDet d n
        (sourceFullFrameEmbeddingOfHeadTail d n r hrD hrn lam)
        (sourceOrientedNormalParameterVector d n r hrD hrn p) =
      p.head.det *
        (sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail).det lam := by
  simpa using
    sourceFullFrameDet_normalParameter_headTail_raw d n r hrD hrn p lam

/-- Matrix formed by adjoining an `(r + D) × r` block to an
`(r + D) × D` block.  The first `r` columns come from `M`; the remaining
`D` columns come from `Q`. -/
def matrixBlockColumns
    (r D : ℕ)
    (M : Matrix (Fin (r + D)) (Fin r) ℂ)
    (Q : Matrix (Fin (r + D)) (Fin D) ℂ) :
    Matrix (Fin (r + D)) (Fin (r + D)) ℂ :=
  fun i j =>
    if h : j.val < r then
      M i ⟨j.val, h⟩
    else
      Q i ⟨j.val - r, by omega⟩

@[simp]
theorem matrixBlockColumns_inl
    (r D : ℕ)
    (M : Matrix (Fin (r + D)) (Fin r) ℂ)
    (Q : Matrix (Fin (r + D)) (Fin D) ℂ)
    (i : Fin (r + D))
    (a : Fin r) :
    matrixBlockColumns r D M Q i
        ((finSumFinEquiv : Fin r ⊕ Fin D ≃ Fin (r + D)) (Sum.inl a)) =
      M i a := by
  simp [matrixBlockColumns]

@[simp]
theorem matrixBlockColumns_inr
    (r D : ℕ)
    (M : Matrix (Fin (r + D)) (Fin r) ℂ)
    (Q : Matrix (Fin (r + D)) (Fin D) ℂ)
    (i : Fin (r + D))
    (u : Fin D) :
    matrixBlockColumns r D M Q i
        ((finSumFinEquiv : Fin r ⊕ Fin D ≃ Fin (r + D)) (Sum.inr u)) =
      Q i u := by
  simp [matrixBlockColumns]

theorem matrixBlockColumns_reindex_finSum
    (r D : ℕ)
    (M : Matrix (Fin (r + D)) (Fin r) ℂ)
    (Q : Matrix (Fin (r + D)) (Fin D) ℂ) :
    Matrix.reindex
        (finSumFinEquiv : Fin r ⊕ Fin D ≃ Fin (r + D)).symm
        (finSumFinEquiv : Fin r ⊕ Fin D ≃ Fin (r + D)).symm
        (matrixBlockColumns r D M Q) =
      Matrix.fromBlocks
        (fun a b => M ((finSumFinEquiv :
          Fin r ⊕ Fin D ≃ Fin (r + D)) (Sum.inl a)) b)
        (fun a u => Q ((finSumFinEquiv :
          Fin r ⊕ Fin D ≃ Fin (r + D)) (Sum.inl a)) u)
        (fun v b => M ((finSumFinEquiv :
          Fin r ⊕ Fin D ≃ Fin (r + D)) (Sum.inr v)) b)
        (fun v u => Q ((finSumFinEquiv :
          Fin r ⊕ Fin D ≃ Fin (r + D)) (Sum.inr v)) u) := by
  ext row col
  cases row <;> cases col <;>
    simp [Matrix.reindex_apply, matrixBlockColumns]

/-- The exterior product of all columns of a block-column matrix is the
product of the exterior products of the two column blocks. -/
theorem matrixBlockColumns_iMulti_eq_mul
    (r D : ℕ)
    (M : Matrix (Fin (r + D)) (Fin r) ℂ)
    (Q : Matrix (Fin (r + D)) (Fin D) ℂ) :
    ExteriorAlgebra.ιMulti ℂ (r + D)
        (fun j : Fin (r + D) => fun i : Fin (r + D) =>
          matrixBlockColumns r D M Q i j) =
      ExteriorAlgebra.ιMulti ℂ r
          (fun a : Fin r => fun i : Fin (r + D) => M i a) *
        ExteriorAlgebra.ιMulti ℂ D
          (fun u : Fin D => fun i : Fin (r + D) => Q i u) := by
  rw [ExteriorAlgebra.ιMulti_mul_ιMulti]
  congr
  funext j
  refine Fin.addCases (motive := fun j =>
    (fun i : Fin (r + D) => matrixBlockColumns r D M Q i j) =
      Fin.append (fun a : Fin r => fun i : Fin (r + D) => M i a)
        (fun u : Fin D => fun i : Fin (r + D) => Q i u) j) ?_ ?_ j
  · intro a
    funext i
    rw [Fin.append_left]
    simp [matrixBlockColumns]
  · intro u
    funext i
    rw [Fin.append_right]
    simp [matrixBlockColumns]

/-- Exterior-power coefficient form of the ordered-minor determinant.  For a
matrix whose columns are vectors in `Fin N → ℂ`, the coordinate of their
exterior product at an ordered `k`-subset is the determinant of the
corresponding row minor. -/
theorem exteriorPower_repr_iMulti_matrixColumns
    (N k : ℕ)
    (A : Matrix (Fin N) (Fin k) ℂ)
    (s : Set.powersetCard (Fin N) k) :
    (((Pi.basisFun ℂ (Fin N)).exteriorPower k).repr
        (exteriorPower.ιMulti ℂ k
          (fun j : Fin k => fun i : Fin N => A i j))) s =
      Matrix.det
        (fun i j : Fin k => A (Set.powersetCard.ofFinEmbEquiv.symm s i) j) := by
  rw [exteriorPower.basis_repr_apply]
  simp [exteriorPower.ιMultiDual_apply_ιMulti]
  rw [← Matrix.det_transpose
    (M := fun i j : Fin k =>
      A (Set.powersetCard.ofFinEmbEquiv.symm s i) j)]
  rfl

/-- For a homogeneous exterior-power element, its coordinate in the full
exterior-algebra basis at an ordered `N`-subset agrees with its coordinate in
the degree-`N` exterior-power basis. -/
theorem exteriorAlgebra_repr_of_mem
    (N : ℕ)
    (x : ⋀[ℂ]^N (Fin N → ℂ))
    (s : Set.powersetCard (Fin N) N) :
    ((Pi.basisFun ℂ (Fin N)).ExteriorAlgebra.repr
        (x : ExteriorAlgebra ℂ (Fin N → ℂ))) s.val =
      ((Pi.basisFun ℂ (Fin N)).exteriorPower N).repr x s := by
  change (((DirectSum.Decomposition.isInternal
      (fun n => ⋀[ℂ]^n (Fin N → ℂ))).collectedBasis
        (fun n => (Pi.basisFun ℂ (Fin N)).exteriorPower n)).reindex
          Set.powersetCard.prodEquiv).repr
        (x : ExteriorAlgebra ℂ (Fin N → ℂ)) s.val = _
  simp [Module.Basis.reindex]
  have hidx :
      (⟨(s.val).card, Set.powersetCard.ofCard (s := s.val) rfl⟩ :
        Sigma fun n => Set.powersetCard (Fin N) n) =
        ⟨N, s⟩ := by
    rw [Sigma.mk.inj_iff]
    constructor
    · exact s.prop
    · rw [Subtype.heq_iff_coe_eq]
      · rfl
      · intro t
        rw [s.prop]
  rw [hidx]
  exact
    DirectSum.IsInternal.collectedBasis_repr_of_mem
      (DirectSum.Decomposition.isInternal
        (fun n => ⋀[ℂ]^n (Fin N → ℂ)))
      (fun n => (Pi.basisFun ℂ (Fin N)).exteriorPower n)
      (x.property :
        (x : ExteriorAlgebra ℂ (Fin N → ℂ)) ∈ ⋀[ℂ]^N (Fin N → ℂ))
      (a := s)

@[simp]
theorem powersetCard_univ_orderEmb_id
    (N : ℕ)
    (S : Set.powersetCard (Fin N) N)
    (hS : (S : Finset (Fin N)) = Finset.univ)
    (i : Fin N) :
    Set.powersetCard.ofFinEmbEquiv.symm S i = i := by
  have horder :
      Set.powersetCard.ofFinEmbEquiv.symm S =
        (OrderIso.refl (Fin N)).toOrderEmbedding := by
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
    exact (Finset.orderEmbOfFin_unique' S.prop
      (f := (OrderIso.refl (Fin N)).toOrderEmbedding) (by
        intro x
        rw [hS]
        simp)).symm
  exact congrFun (congrArg DFunLike.coe horder) i

/-- Top-degree exterior-algebra coordinate form of the determinant. -/
theorem exteriorAlgebra_top_repr_iMulti_matrixColumns
    (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    ((Pi.basisFun ℂ (Fin N)).ExteriorAlgebra.repr
        (ExteriorAlgebra.ιMulti ℂ N
          (fun j : Fin N => fun i : Fin N => A i j))) Finset.univ =
      Matrix.det A := by
  let S : Set.powersetCard (Fin N) N :=
    Set.powersetCard.ofCard (s := (Finset.univ : Finset (Fin N))) (by simp)
  have hS : (S : Finset (Fin N)) = Finset.univ := rfl
  have hrepr := exteriorAlgebra_repr_of_mem N
    (exteriorPower.ιMulti ℂ N
      (fun j : Fin N => fun i : Fin N => A i j)) S
  have hminor := exteriorPower_repr_iMulti_matrixColumns N N A S
  rw [hminor] at hrepr
  rw [hS] at hrepr
  have hmat :
      (fun i j : Fin N =>
        A (Set.powersetCard.ofFinEmbEquiv.symm S i) j) = A := by
    ext i j
    rw [powersetCard_univ_orderEmb_id N S hS i]
  rw [hmat] at hrepr
  exact hrepr

/-- Expansion of an exterior product of matrix columns in the full exterior
algebra basis. -/
theorem exteriorAlgebra_iMulti_matrixColumns_eq_sum_minors
    (N k : ℕ)
    (A : Matrix (Fin N) (Fin k) ℂ) :
    ExteriorAlgebra.ιMulti ℂ k
        (fun j : Fin k => fun i : Fin N => A i j) =
      ∑ s : Set.powersetCard (Fin N) k,
        Matrix.det
            (fun i j : Fin k =>
              A (Set.powersetCard.ofFinEmbEquiv.symm s i) j) •
          (Pi.basisFun ℂ (Fin N)).ExteriorAlgebra s.val := by
  let x : ⋀[ℂ]^k (Fin N → ℂ) :=
    exteriorPower.ιMulti ℂ k
      (fun j : Fin k => fun i : Fin N => A i j)
  change (x : ExteriorAlgebra ℂ (Fin N → ℂ)) = _
  have hsum := ((Pi.basisFun ℂ (Fin N)).exteriorPower k).sum_repr x
  have hcoe := congrArg
    (fun y : ⋀[ℂ]^k (Fin N → ℂ) =>
      (y : ExteriorAlgebra ℂ (Fin N → ℂ))) hsum
  change ((↑(∑ i,
        ((Module.Basis.exteriorPower k (Pi.basisFun ℂ (Fin N))).repr x) i •
          (Module.Basis.exteriorPower k
            (Pi.basisFun ℂ (Fin N))) i) :
      ExteriorAlgebra ℂ (Fin N → ℂ)) = ↑x) at hcoe
  rw [← hcoe]
  rw [Submodule.coe_sum]
  simp_rw [Submodule.coe_smul_of_tower]
  apply Finset.sum_congr rfl
  intro s _hs
  rw [exteriorPower_repr_iMulti_matrixColumns]
  congr 1
  exact (ExteriorAlgebra.basis_eq_coe_basis (Pi.basisFun ℂ (Fin N)) s).symm

@[simp]
theorem matrixRowSubset_compl_card
    (r D : ℕ)
    (s : Finset (Fin (r + D)))
    (hs : s.card = r) :
    sᶜ.card = D := by
  rw [Finset.card_compl, hs, Fintype.card_fin]
  omega

/-- The canonical increasing enumeration of a chosen `r`-row subset. -/
def matrixRowSubsetHeadRows
    (r D : ℕ)
    (s : Finset (Fin (r + D)))
    (hs : s.card = r) :
    Fin r ↪ Fin (r + D) :=
  (s.orderEmbOfFin hs).toEmbedding

/-- The canonical increasing enumeration of the complement of a chosen
`r`-row subset. -/
def matrixRowSubsetTailRows
    (r D : ℕ)
    (s : Finset (Fin (r + D)))
    (hs : s.card = r) :
    Fin D ↪ Fin (r + D) :=
  (sᶜ.orderEmbOfFin (matrixRowSubset_compl_card r D s hs)).toEmbedding

/-- The canonical row equivalence that puts a chosen row subset first and its
complement second, preserving the internal order on each part. -/
noncomputable def matrixRowSubsetSumEquiv
    (r D : ℕ)
    (s : Finset (Fin (r + D)))
    (hs : s.card = r) :
    Fin r ⊕ Fin D ≃ Fin (r + D) :=
  finSumEquivOfFinset (s := s) hs
    (matrixRowSubset_compl_card r D s hs)

@[simp]
theorem matrixRowSubsetSumEquiv_inl
    (r D : ℕ)
    (s : Finset (Fin (r + D)))
    (hs : s.card = r)
    (a : Fin r) :
    matrixRowSubsetSumEquiv r D s hs (Sum.inl a) =
      matrixRowSubsetHeadRows r D s hs a := by
  simp [matrixRowSubsetSumEquiv, matrixRowSubsetHeadRows]

@[simp]
theorem matrixRowSubsetSumEquiv_inr
    (r D : ℕ)
    (s : Finset (Fin (r + D)))
    (hs : s.card = r)
    (u : Fin D) :
    matrixRowSubsetSumEquiv r D s hs (Sum.inr u) =
      matrixRowSubsetTailRows r D s hs u := by
  simp [matrixRowSubsetSumEquiv, matrixRowSubsetTailRows]

/-- The row-shuffle sign in the finite Laplace expansion along the first
`r` columns and the last `D` columns. -/
noncomputable def matrixRowSubsetLaplaceSign
    (r D : ℕ)
    (s : Finset (Fin (r + D)))
    (hs : s.card = r) : ℂ :=
  let S : Set.powersetCard (Fin (r + D)) r :=
    ⟨s, by simpa [Set.powersetCard.mem_iff] using hs⟩
  let T : Set.powersetCard (Fin (r + D)) D :=
    Set.powersetCard.compl (α := Fin (r + D)) (n := r) (m := D)
      (by simp [Nat.add_comm]) S
  let hdisj : Disjoint S.val T.val := by
    change Disjoint S.val S.valᶜ
    exact disjoint_compl_right
  (((Set.powersetCard.permOfDisjoint hdisj).sign : ℤ) : ℂ)

/-- The summand attached to one ordered row subset in the finite Laplace
expansion of a block-column determinant. -/
noncomputable def matrixBlockColumnLaplaceTerm
    (r D : ℕ)
    (M : Matrix (Fin (r + D)) (Fin r) ℂ)
    (Q : Matrix (Fin (r + D)) (Fin D) ℂ)
    (S : Set.powersetCard (Fin (r + D)) r) : ℂ :=
  matrixRowSubsetLaplaceSign r D S.val S.prop *
    Matrix.det
      (fun a b => M (matrixRowSubsetHeadRows r D S.val S.prop a) b) *
    Matrix.det
      (fun a b => Q (matrixRowSubsetTailRows r D S.val S.prop a) b)

/-- The finite row-subset Laplace sum for a block-column determinant. -/
noncomputable def matrixBlockColumnLaplaceSum
    (r D : ℕ)
    (M : Matrix (Fin (r + D)) (Fin r) ℂ)
    (Q : Matrix (Fin (r + D)) (Fin D) ℂ) : ℂ :=
  ∑ S : Set.powersetCard (Fin (r + D)) r,
    matrixBlockColumnLaplaceTerm r D M Q S

/-- Coefficient of a fixed head-row exterior basis vector times the tail-column
exterior product.  Only the complementary tail rows survive in top degree. -/
theorem exteriorAlgebra_basis_mul_iMulti_compl_repr
    (r D : ℕ)
    (Q : Matrix (Fin (r + D)) (Fin D) ℂ)
    (S : Set.powersetCard (Fin (r + D)) r) :
    ((Pi.basisFun ℂ (Fin (r + D))).ExteriorAlgebra.repr
      ((Pi.basisFun ℂ (Fin (r + D))).ExteriorAlgebra S.val *
        ExteriorAlgebra.ιMulti ℂ D
          (fun u : Fin D => fun i : Fin (r + D) => Q i u))) Finset.univ =
      matrixRowSubsetLaplaceSign r D S.val S.prop *
        Matrix.det
          (fun a b : Fin D =>
            Q (matrixRowSubsetTailRows r D S.val S.prop a) b) := by
  let T : Set.powersetCard (Fin (r + D)) D :=
    Set.powersetCard.compl (α := Fin (r + D)) (n := r) (m := D)
      (by simp [Nat.add_comm]) S
  have hdisj : Disjoint S.val T.val := by
    change Disjoint S.val S.valᶜ
    exact disjoint_compl_right
  have hQ := exteriorAlgebra_iMulti_matrixColumns_eq_sum_minors (r + D) D Q
  rw [hQ]
  rw [Finset.mul_sum]
  simp_rw [mul_smul_comm]
  rw [map_sum]
  simp_rw [map_smul]
  rw [Finset.sum_eq_single T]
  · have hmul := ExteriorAlgebra.basis_mul_of_disjoint
      (Pi.basisFun ℂ (Fin (r + D))) (s := S) (t := T) hdisj
    rw [hmul]
    have hsign :
        (((Set.powersetCard.permOfDisjoint hdisj).sign : ℤ) : ℂ) =
          matrixRowSubsetLaplaceSign r D S.val S.prop := by
      simp [matrixRowSubsetLaplaceSign, T]
    rw [← hsign]
    have htop :
        (Set.powersetCard.disjUnion hdisj).val =
          (Finset.univ : Finset (Fin (r + D))) := by
      ext x
      simp [T]
    have hcoord :
        ((Pi.basisFun ℂ (Fin (r + D))).ExteriorAlgebra.repr
          ((Set.powersetCard.permOfDisjoint hdisj).sign •
            (Pi.basisFun ℂ (Fin (r + D))).ExteriorAlgebra
              (Set.powersetCard.disjUnion hdisj).val)) Finset.univ =
          (((Set.powersetCard.permOfDisjoint hdisj).sign : ℤ) : ℂ) := by
      rw [← htop]
      change
        ((Pi.basisFun ℂ (Fin (r + D))).ExteriorAlgebra.repr
          ((((Set.powersetCard.permOfDisjoint hdisj).sign : ℤ) : ℂ) •
            (Pi.basisFun ℂ (Fin (r + D))).ExteriorAlgebra
              (Set.powersetCard.disjUnion hdisj).val))
          (Set.powersetCard.disjUnion hdisj).val =
          (((Set.powersetCard.permOfDisjoint hdisj).sign : ℤ) : ℂ)
      simp
    rw [Finsupp.smul_apply, hcoord]
    have htailRows :
        (fun i j : Fin D => Q (Set.powersetCard.ofFinEmbEquiv.symm T i) j) =
          (fun a b : Fin D =>
            Q (matrixRowSubsetTailRows r D S.val S.prop a) b) := by
      ext a b
      simp [T, matrixRowSubsetTailRows,
        Set.powersetCard.ofFinEmbEquiv_symm_apply]
    rw [htailRows]
    exact mul_comm _ _
  · intro U _hU hUT
    by_cases hSU : Disjoint S.val U.val
    · have hUeq : U = T := by
        apply Set.powersetCard.eq_iff_subset.mpr
        intro x hx
        change x ∈ S.valᶜ
        rw [Finset.mem_compl]
        intro hxS
        exact Finset.disjoint_left.mp hSU hxS hx
      exact (hUT hUeq).elim
    · have hmul := ExteriorAlgebra.basis_mul_of_not_disjoint
        (Pi.basisFun ℂ (Fin (r + D))) (s := S) (t := U) hSU
      rw [hmul]
      simp
  · intro hT
    exact (hT (Finset.mem_univ T)).elim

/-- Finite Laplace expansion of a determinant whose first `r` columns are `M`
and last `D` columns are `Q`, grouped by the chosen rows of the first block. -/
theorem matrix_det_blockColumn_laplace
    (r D : ℕ)
    (M : Matrix (Fin (r + D)) (Fin r) ℂ)
    (Q : Matrix (Fin (r + D)) (Fin D) ℂ) :
    (matrixBlockColumns r D M Q).det =
      matrixBlockColumnLaplaceSum r D M Q := by
  rw [← exteriorAlgebra_top_repr_iMulti_matrixColumns
    (r + D) (matrixBlockColumns r D M Q)]
  rw [matrixBlockColumns_iMulti_eq_mul]
  have hM := exteriorAlgebra_iMulti_matrixColumns_eq_sum_minors (r + D) r M
  rw [hM]
  rw [Finset.sum_mul]
  simp_rw [smul_mul_assoc]
  rw [map_sum]
  simp_rw [map_smul]
  simp_rw [Finsupp.finset_sum_apply]
  simp_rw [Finsupp.smul_apply]
  unfold matrixBlockColumnLaplaceSum matrixBlockColumnLaplaceTerm
  change
    (∑ S : Set.powersetCard (Fin (r + D)) r,
      (Matrix.det
          (fun i j : Fin r =>
            M (Set.powersetCard.ofFinEmbEquiv.symm S i) j)) •
        (((Pi.basisFun ℂ (Fin (r + D))).ExteriorAlgebra.repr
          ((Pi.basisFun ℂ (Fin (r + D))).ExteriorAlgebra S.val *
            ExteriorAlgebra.ιMulti ℂ D
              (fun u : Fin D => fun i : Fin (r + D) => Q i u))) Finset.univ)) =
      ∑ S : Set.powersetCard (Fin (r + D)) r,
        (matrixRowSubsetLaplaceSign r D S.val S.prop *
            Matrix.det
              (fun a b : Fin r =>
                M (matrixRowSubsetHeadRows r D S.val S.prop a) b)) *
          Matrix.det
            (fun a b : Fin D =>
              Q (matrixRowSubsetTailRows r D S.val S.prop a) b)
  apply Finset.sum_congr rfl
  intro S _hS
  rw [exteriorAlgebra_basis_mul_iMulti_compl_repr]
  have hheadRows :
      (fun i j : Fin r => M (Set.powersetCard.ofFinEmbEquiv.symm S i) j) =
        (fun a b : Fin r =>
          M (matrixRowSubsetHeadRows r D S.val S.prop a) b) := by
    ext a b
    simp [matrixRowSubsetHeadRows,
      Set.powersetCard.ofFinEmbEquiv_symm_apply]
  rw [hheadRows]
  simp [smul_eq_mul, mul_left_comm, mul_assoc]

/-- Head-column coefficients for an arbitrary ordered full frame in the
rank-deficient Schur normal form.  Selected head labels contribute standard
basis rows; tail labels contribute their stored mixed rows. -/
def sourceNormalFullFrameCoeff
    (d n r : ℕ)
    (hrn : r ≤ n)
    (L : Matrix (Fin (n - r)) (Fin r) ℂ)
    (ι : Fin (d + 1) ↪ Fin n) :
    Matrix (Fin (d + 1)) (Fin r) ℂ :=
  fun k a =>
    if hhead : ∃ b : Fin r, ι k = finSourceHead hrn b then
      if Classical.choose hhead = a then 1 else 0
    else
      let htail : ∃ u : Fin (n - r), ι k = finSourceTail hrn u :=
        (finSourceHead_tail_cases hrn (ι k)).resolve_left hhead
      L (Classical.choose htail) a

/-- The head-coordinate block of an arbitrary ordered full frame after applying
the chosen head factor. -/
def sourceNormalFullFrameHeadBlock
    (d n r : ℕ)
    (hrn : r ≤ n)
    (H : Matrix (Fin r) (Fin r) ℂ)
    (L : Matrix (Fin (n - r)) (Fin r) ℂ)
    (ι : Fin (d + 1) ↪ Fin n) :
    Matrix (Fin (d + 1)) (Fin r) ℂ :=
  sourceNormalFullFrameCoeff d n r hrn L ι * H

@[simp]
theorem sourceNormalFullFrameCoeff_head
    (d n r : ℕ)
    (hrn : r ≤ n)
    (L : Matrix (Fin (n - r)) (Fin r) ℂ)
    (ι : Fin (d + 1) ↪ Fin n)
    (k : Fin (d + 1))
    (b a : Fin r)
    (hk : ι k = finSourceHead hrn b) :
    sourceNormalFullFrameCoeff d n r hrn L ι k a =
      if b = a then 1 else 0 := by
  unfold sourceNormalFullFrameCoeff
  have hhead : ∃ b : Fin r, ι k = finSourceHead hrn b := ⟨b, hk⟩
  rw [dif_pos hhead]
  have hchoose : Classical.choose hhead = b := by
    apply finSourceHead_injective hrn
    rw [← Classical.choose_spec hhead, hk]
  simp [hchoose]

@[simp]
theorem sourceNormalFullFrameCoeff_tail
    (d n r : ℕ)
    (hrn : r ≤ n)
    (L : Matrix (Fin (n - r)) (Fin r) ℂ)
    (ι : Fin (d + 1) ↪ Fin n)
    (k : Fin (d + 1))
    (u : Fin (n - r))
    (a : Fin r)
    (hk : ι k = finSourceTail hrn u) :
    sourceNormalFullFrameCoeff d n r hrn L ι k a = L u a := by
  unfold sourceNormalFullFrameCoeff
  have hnothead :
      ¬ ∃ b : Fin r, ι k = finSourceHead hrn b := by
    rintro ⟨b, hb⟩
    exact finSourceHead_ne_finSourceTail hrn b u (hb.symm.trans hk)
  rw [dif_neg hnothead]
  have htail :
      ∃ u : Fin (n - r), ι k = finSourceTail hrn u :=
    (finSourceHead_tail_cases hrn (ι k)).resolve_left hnothead
  have hchoose : Classical.choose htail = u := by
    apply finSourceTail_injective hrn
    rw [← Classical.choose_spec htail, hk]
  simp [hchoose]

@[simp]
theorem sourceNormalFullFrameHeadBlock_head
    (d n r : ℕ)
    (hrn : r ≤ n)
    (H : Matrix (Fin r) (Fin r) ℂ)
    (L : Matrix (Fin (n - r)) (Fin r) ℂ)
    (ι : Fin (d + 1) ↪ Fin n)
    (k : Fin (d + 1))
    (b a : Fin r)
    (hk : ι k = finSourceHead hrn b) :
    sourceNormalFullFrameHeadBlock d n r hrn H L ι k a = H b a := by
  have hcoeff :
      ∀ j : Fin r,
        sourceNormalFullFrameCoeff d n r hrn L ι k j =
          if b = j then 1 else 0 := by
    intro j
    exact sourceNormalFullFrameCoeff_head d n r hrn L ι k b j hk
  simp [sourceNormalFullFrameHeadBlock, Matrix.mul_apply, hcoeff]

@[simp]
theorem sourceNormalFullFrameHeadBlock_tail
    (d n r : ℕ)
    (hrn : r ≤ n)
    (H : Matrix (Fin r) (Fin r) ℂ)
    (L : Matrix (Fin (n - r)) (Fin r) ℂ)
    (ι : Fin (d + 1) ↪ Fin n)
    (k : Fin (d + 1))
    (u : Fin (n - r))
    (a : Fin r)
    (hk : ι k = finSourceTail hrn u) :
    sourceNormalFullFrameHeadBlock d n r hrn H L ι k a =
      (L * H) u a := by
  have hcoeff :
      ∀ j : Fin r,
        sourceNormalFullFrameCoeff d n r hrn L ι k j = L u j := by
    intro j
    exact sourceNormalFullFrameCoeff_tail d n r hrn L ι k u j hk
  simp [sourceNormalFullFrameHeadBlock, Matrix.mul_apply, hcoeff]

/-- The residual-tail coordinate block for an arbitrary ordered full frame.
Rows selected from tail source labels contribute the corresponding shifted-tail
coordinate row; rows selected from head labels contribute zero. -/
def sourceNormalFullFrameTailBlock
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (q : Fin (n - r) → Fin (d + 1 - r) → ℂ)
    (ι : Fin (d + 1) ↪ Fin n) :
    Matrix (Fin (d + 1)) (Fin (d + 1 - r)) ℂ :=
  let _ := hrD
  fun k μ =>
    if htail :
        ∃ u : Fin (n - r), ι k = finSourceTail hrn u then
      q (Classical.choose htail) μ
    else
      0

@[simp]
theorem sourceNormalFullFrameTailBlock_head
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (q : Fin (n - r) → Fin (d + 1 - r) → ℂ)
    (ι : Fin (d + 1) ↪ Fin n)
    (k : Fin (d + 1))
    (b : Fin r)
    (μ : Fin (d + 1 - r))
    (hk : ι k = finSourceHead hrn b) :
    sourceNormalFullFrameTailBlock d n r hrD hrn q ι k μ = 0 := by
  simp [sourceNormalFullFrameTailBlock, hk,
    finSourceHead_ne_finSourceTail]

@[simp]
theorem sourceNormalFullFrameTailBlock_tail
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (q : Fin (n - r) → Fin (d + 1 - r) → ℂ)
    (ι : Fin (d + 1) ↪ Fin n)
    (k : Fin (d + 1))
    (u : Fin (n - r))
    (μ : Fin (d + 1 - r))
    (hk : ι k = finSourceTail hrn u) :
    sourceNormalFullFrameTailBlock d n r hrD hrn q ι k μ = q u μ := by
  unfold sourceNormalFullFrameTailBlock
  have htail :
      ∃ u : Fin (n - r), ι k = finSourceTail hrn u := ⟨u, hk⟩
  rw [dif_pos htail]
  have hchoose : Classical.choose htail = u := by
    apply finSourceTail_injective hrn
    rw [← Classical.choose_spec htail, hk]
  simp [hchoose]

theorem sourceOrientedNormalParameterVector_headCoord_eq_headBlock
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (ι : Fin (d + 1) ↪ Fin n)
    (k : Fin (d + 1))
    (a : Fin r) :
    sourceOrientedNormalParameterVector d n r hrD hrn p (ι k)
        (finSourceHead (Nat.le_of_lt hrD) a) =
      sourceNormalFullFrameHeadBlock d n r hrn p.head p.mixed ι k a := by
  rcases finSourceHead_tail_cases hrn (ι k) with ⟨b, hb⟩ | ⟨u, hu⟩
  · rw [hb, sourceOrientedNormalParameterVector_head,
      sourceOrientedNormalHeadVector_headCoord,
      sourceNormalFullFrameHeadBlock_head d n r hrn p.head p.mixed ι k b a hb]
  · rw [hu, sourceOrientedNormalParameterVector_tail,
      sourceNormalFullFrameHeadBlock_tail d n r hrn p.head p.mixed ι k u a hu]
    simp [Matrix.mul_apply]

theorem sourceOrientedNormalParameterVector_tailCoord_eq_tailBlock
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (ι : Fin (d + 1) ↪ Fin n)
    (k : Fin (d + 1))
    (μ : Fin (d + 1 - r)) :
    sourceOrientedNormalParameterVector d n r hrD hrn p (ι k)
        (finSourceTail (Nat.le_of_lt hrD) μ) =
      sourceNormalFullFrameTailBlock d n r hrD hrn p.tail ι k μ := by
  rcases finSourceHead_tail_cases hrn (ι k) with ⟨b, hb⟩ | ⟨u, hu⟩
  · rw [hb, sourceOrientedNormalParameterVector_head,
      sourceOrientedNormalHeadVector_tailCoord,
      sourceNormalFullFrameTailBlock_head d n r hrD hrn p.tail ι k b μ hb]
  · rw [hu, sourceOrientedNormalParameterVector_tail,
      sourceNormalFullFrameTailBlock_tail d n r hrD hrn p.tail ι k u μ hu]
    simp

theorem sourceFullFrameMatrix_normalParameter_eq_blockColumns
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (ι : Fin (d + 1) ↪ Fin n) :
    Matrix.reindex
        (finCongr (Nat.add_sub_of_le (Nat.le_of_lt hrD)).symm)
        (finCongr (Nat.add_sub_of_le (Nat.le_of_lt hrD)).symm)
        (sourceFullFrameMatrix d n ι
          (sourceOrientedNormalParameterVector d n r hrD hrn p)) =
      matrixBlockColumns r (d + 1 - r)
        (fun k a =>
          sourceNormalFullFrameHeadBlock d n r hrn p.head p.mixed ι
            (Fin.cast (Nat.add_sub_of_le (Nat.le_of_lt hrD)) k) a)
        (fun k μ =>
          sourceNormalFullFrameTailBlock d n r hrD hrn p.tail ι
            (Fin.cast (Nat.add_sub_of_le (Nat.le_of_lt hrD)) k) μ) := by
  ext k j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  by_cases hcol : j.val < r
  · have hj :
        Fin.cast (Nat.add_sub_of_le (Nat.le_of_lt hrD)) j =
          finSourceHead (Nat.le_of_lt hrD) ⟨j.val, hcol⟩ := by
      apply Fin.ext
      simp [finSourceHead]
    simp [matrixBlockColumns, sourceFullFrameMatrix, hcol, hj,
      sourceOrientedNormalParameterVector_headCoord_eq_headBlock]
  · have hj :
        Fin.cast (Nat.add_sub_of_le (Nat.le_of_lt hrD)) j =
          finSourceTail (Nat.le_of_lt hrD) ⟨j.val - r, by omega⟩ := by
      apply Fin.ext
      simp [finSourceTail]
      omega
    simp [matrixBlockColumns, sourceFullFrameMatrix, hcol, hj,
      sourceOrientedNormalParameterVector_tailCoord_eq_tailBlock]

/-- Residual-tail determinant attached to a chosen set of rows of an arbitrary
ordered full frame.  It is zero unless all chosen rows are tail source labels. -/
def sourceNormalFullFrameTailRowsDet
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (T : SourceShiftedTailOrientedData d r hrD (n - r))
    (ι : Fin (d + 1) ↪ Fin n)
    (rows : Fin (d + 1 - r) ↪ Fin (d + 1)) : ℂ :=
  if htail :
      ∀ μ : Fin (d + 1 - r),
        ∃ u : Fin (n - r), ι (rows μ) = finSourceTail hrn u then
    T.det
      { toFun := fun μ => Classical.choose (htail μ)
        inj' := by
          intro μ ν hμν
          apply rows.injective
          apply ι.injective
          calc
            ι (rows μ) = finSourceTail hrn (Classical.choose (htail μ)) :=
              Classical.choose_spec (htail μ)
            _ = finSourceTail hrn (Classical.choose (htail ν)) := by
              simpa using congrArg (finSourceTail hrn) hμν
            _ = ι (rows ν) := (Classical.choose_spec (htail ν)).symm }
  else
    0

theorem sourceNormalFullFrameTailRowsDet_eq_det_tailBlock
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (q : Fin (n - r) → Fin (d + 1 - r) → ℂ)
    (ι : Fin (d + 1) ↪ Fin n)
    (rows : Fin (d + 1 - r) ↪ Fin (d + 1)) :
    Matrix.det
        (fun μ ν =>
          sourceNormalFullFrameTailBlock d n r hrD hrn q ι (rows μ) ν) =
      sourceNormalFullFrameTailRowsDet d n r hrD hrn
        (sourceShiftedTailOrientedInvariant d r hrD (n - r) q) ι rows := by
  unfold sourceNormalFullFrameTailRowsDet sourceNormalFullFrameTailBlock
    sourceShiftedTailOrientedInvariant
  by_cases htail :
      ∀ μ : Fin (d + 1 - r),
        ∃ u : Fin (n - r), ι (rows μ) = finSourceTail hrn u
  · simp [htail]
  · have hrow :
        ∃ μ : Fin (d + 1 - r),
          ¬ ∃ u : Fin (n - r), ι (rows μ) = finSourceTail hrn u := by
      simpa [not_forall] using htail
    rcases hrow with ⟨μ0, hμ0⟩
    rw [Matrix.det_eq_zero_of_row_eq_zero μ0]
    · simp [htail]
    · intro ν
      simp [hμ0]

/-- The Schur/Laplace determinant formula for an arbitrary ordered full frame,
expressed using the chosen head factor, mixed Schur coefficients, and
shifted-tail oriented determinant coordinates. -/
def sourceNormalFullFrameDetFromSchur
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (H : Matrix (Fin r) (Fin r) ℂ)
    (L : Matrix (Fin (n - r)) (Fin r) ℂ)
    (T : SourceShiftedTailOrientedData d r hrD (n - r))
    (ι : Fin (d + 1) ↪ Fin n) : ℂ :=
  ∑ S : Set.powersetCard (Fin (r + (d + 1 - r))) r,
    matrixRowSubsetLaplaceSign r (d + 1 - r) S.val S.prop *
      Matrix.det
        (fun a b =>
          sourceNormalFullFrameHeadBlock d n r hrn H L ι
            (Fin.cast (Nat.add_sub_of_le (Nat.le_of_lt hrD))
              (matrixRowSubsetHeadRows r (d + 1 - r) S.val S.prop a)) b) *
      sourceNormalFullFrameTailRowsDet d n r hrD hrn T ι
        { toFun := fun μ =>
            Fin.cast (Nat.add_sub_of_le (Nat.le_of_lt hrD))
              (matrixRowSubsetTailRows r (d + 1 - r) S.val S.prop μ)
          inj' := by
            intro μ ν hμν
            exact (matrixRowSubsetTailRows r (d + 1 - r) S.val S.prop).injective
              (Fin.cast_injective
                (Nat.add_sub_of_le (Nat.le_of_lt hrD)) hμν) }

theorem sourceFullFrameDet_normalParameter_eq_schurFormula_of_laplace
    (hlaplace :
      ∀ (r D : ℕ)
        (M : Matrix (Fin (r + D)) (Fin r) ℂ)
        (Q : Matrix (Fin (r + D)) (Fin D) ℂ),
        (matrixBlockColumns r D M Q).det =
          matrixBlockColumnLaplaceSum r D M Q)
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (ι : Fin (d + 1) ↪ Fin n) :
    sourceFullFrameDet d n ι
        (sourceOrientedNormalParameterVector d n r hrD hrn p) =
      sourceNormalFullFrameDetFromSchur d n r hrD hrn
        p.head p.mixed
        (sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail)
        ι := by
  let M : Matrix (Fin (r + (d + 1 - r))) (Fin r) ℂ :=
    fun k a =>
      sourceNormalFullFrameHeadBlock d n r hrn p.head p.mixed ι
        (Fin.cast (Nat.add_sub_of_le (Nat.le_of_lt hrD)) k) a
  let Q : Matrix (Fin (r + (d + 1 - r))) (Fin (d + 1 - r)) ℂ :=
    fun k μ =>
      sourceNormalFullFrameTailBlock d n r hrD hrn p.tail ι
        (Fin.cast (Nat.add_sub_of_le (Nat.le_of_lt hrD)) k) μ
  have hmat :
      Matrix.reindex
          (finCongr (Nat.add_sub_of_le (Nat.le_of_lt hrD)).symm)
          (finCongr (Nat.add_sub_of_le (Nat.le_of_lt hrD)).symm)
          (sourceFullFrameMatrix d n ι
            (sourceOrientedNormalParameterVector d n r hrD hrn p)) =
        matrixBlockColumns r (d + 1 - r) M Q := by
    simpa [M, Q] using
      sourceFullFrameMatrix_normalParameter_eq_blockColumns d n r hrD hrn p ι
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_reindex_self] at hdet
  rw [sourceFullFrameDet, hdet, hlaplace r (d + 1 - r) M Q]
  unfold matrixBlockColumnLaplaceSum sourceNormalFullFrameDetFromSchur
  apply Finset.sum_congr rfl
  intro S _hS
  unfold matrixBlockColumnLaplaceTerm
  simp only [M, Q]
  congr 2
  exact sourceNormalFullFrameTailRowsDet_eq_det_tailBlock d n r hrD hrn
    p.tail ι
    { toFun := fun μ =>
        Fin.cast (Nat.add_sub_of_le (Nat.le_of_lt hrD))
          (matrixRowSubsetTailRows r (d + 1 - r) S.val S.prop μ)
      inj' := by
        intro μ ν hμν
        exact (matrixRowSubsetTailRows r (d + 1 - r) S.val S.prop).injective
          (Fin.cast_injective
            (Nat.add_sub_of_le (Nat.le_of_lt hrD)) hμν) }

theorem sourceFullFrameDet_normalParameter_eq_schurFormula
    (d n r : ℕ)
    (hrD : r < d + 1)
    (hrn : r ≤ n)
    (p : SourceOrientedRankDeficientNormalParameter d n r hrD hrn)
    (ι : Fin (d + 1) ↪ Fin n) :
    sourceFullFrameDet d n ι
        (sourceOrientedNormalParameterVector d n r hrD hrn p) =
      sourceNormalFullFrameDetFromSchur d n r hrD hrn
        p.head p.mixed
        (sourceShiftedTailOrientedInvariant d r hrD (n - r) p.tail)
        ι :=
  sourceFullFrameDet_normalParameter_eq_schurFormula_of_laplace
    matrix_det_blockColumn_laplace d n r hrD hrn p ι

end BHW
