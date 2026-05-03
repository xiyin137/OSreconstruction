import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexConeTransport
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexSchurPatch
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Principal Schur graph charts for source scalar-product matrices

This file is the graph side of the principal Schur patch.  The algebraic rank
splitting lives in `SourceComplexSchurPatch`; here we build the actual graph
map

`(A, B, S) ↦ [[A, B], [Bᵀ, S + Bᵀ A⁻¹ B]]`

and prove that, on an invertible symmetric principal block, rank conditions on
the graph are exactly rank conditions on the Schur-complement coordinate `S`.
This is the finite-dimensional Hall-Wightman product chart used at singular
source-complex Gram points.
-/

noncomputable section

open scoped BigOperators
open scoped Topology
open Matrix

namespace BHW

/-- A finite matrix of rank zero is the zero matrix. -/
theorem matrix_eq_zero_of_rank_eq_zero
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (hA : A.rank = 0) : A = 0 := by
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

/-- Principal symmetric Schur graph, transported from `r ⊕ q` back to
`Fin n` by a chosen coordinate equivalence. -/
noncomputable def sourcePrincipalSchurGraph
    (n : ℕ) {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (e : Fin n ≃ r ⊕ q)
    (A : Matrix r r ℂ) (B : Matrix r q ℂ) (S : Matrix q q ℂ) :
    Fin n → Fin n → ℂ :=
  fun i j =>
    (Matrix.fromBlocks A B Bᵀ (S + Bᵀ * A⁻¹ * B))
      (e i) (e j)

theorem sourcePrincipalSchurGraph_toBlocks₁₁
    (n : ℕ) {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (e : Fin n ≃ r ⊕ q)
    (A : Matrix r r ℂ) (B : Matrix r q ℂ) (S : Matrix q q ℂ) :
    ((Matrix.of fun i j : Fin n =>
      sourcePrincipalSchurGraph n e A B S i j).reindex e e).toBlocks₁₁ = A := by
  ext i j
  simp [sourcePrincipalSchurGraph, Matrix.reindex, Matrix.toBlocks₁₁,
    Matrix.fromBlocks]

theorem sourcePrincipalSchurGraph_toBlocks₁₂
    (n : ℕ) {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (e : Fin n ≃ r ⊕ q)
    (A : Matrix r r ℂ) (B : Matrix r q ℂ) (S : Matrix q q ℂ) :
    ((Matrix.of fun i j : Fin n =>
      sourcePrincipalSchurGraph n e A B S i j).reindex e e).toBlocks₁₂ = B := by
  ext i j
  simp [sourcePrincipalSchurGraph, Matrix.reindex, Matrix.toBlocks₁₂,
    Matrix.fromBlocks]

theorem sourcePrincipalSchurGraph_toBlocks₂₁
    (n : ℕ) {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (e : Fin n ≃ r ⊕ q)
    (A : Matrix r r ℂ) (B : Matrix r q ℂ) (S : Matrix q q ℂ) :
    ((Matrix.of fun i j : Fin n =>
      sourcePrincipalSchurGraph n e A B S i j).reindex e e).toBlocks₂₁ = Bᵀ := by
  ext i j
  simp [sourcePrincipalSchurGraph, Matrix.reindex, Matrix.toBlocks₂₁,
    Matrix.fromBlocks]

theorem sourcePrincipalSchurGraph_toBlocks₂₂
    (n : ℕ) {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (e : Fin n ≃ r ⊕ q)
    (A : Matrix r r ℂ) (B : Matrix r q ℂ) (S : Matrix q q ℂ) :
    ((Matrix.of fun i j : Fin n =>
      sourcePrincipalSchurGraph n e A B S i j).reindex e e).toBlocks₂₂ =
        S + Bᵀ * A⁻¹ * B := by
  ext i j
  simp [sourcePrincipalSchurGraph, Matrix.reindex, Matrix.toBlocks₂₂,
    Matrix.fromBlocks]

/-- The Schur-complement coordinate of the graph is exactly `S`. -/
theorem sourcePrincipalSchurGraph_schurComplement
    (n : ℕ) {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (e : Fin n ≃ r ⊕ q)
    (A : Matrix r r ℂ) (B : Matrix r q ℂ) (S : Matrix q q ℂ) :
    ((Matrix.of fun i j : Fin n =>
      sourcePrincipalSchurGraph n e A B S i j).reindex e e).toBlocks₂₂ -
        ((Matrix.of fun i j : Fin n =>
          sourcePrincipalSchurGraph n e A B S i j).reindex e e).toBlocks₂₁ *
          ((Matrix.of fun i j : Fin n =>
            sourcePrincipalSchurGraph n e A B S i j).reindex e e).toBlocks₁₁⁻¹ *
          ((Matrix.of fun i j : Fin n =>
            sourcePrincipalSchurGraph n e A B S i j).reindex e e).toBlocks₁₂ = S := by
  rw [sourcePrincipalSchurGraph_toBlocks₂₂,
    sourcePrincipalSchurGraph_toBlocks₂₁,
    sourcePrincipalSchurGraph_toBlocks₁₁,
    sourcePrincipalSchurGraph_toBlocks₁₂]
  abel

/-- On a symmetric determinant patch, the principal block, rectangular block,
and Schur complement are inverse coordinates to the principal Schur graph. -/
theorem sourcePrincipalSchurGraph_coordinates_eq_of_symmetric
    (n : ℕ) {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (e : Fin n ≃ r ⊕ q)
    {Z : Matrix (Fin n) (Fin n) ℂ}
    (hZsym : Zᵀ = Z) :
    (Matrix.of fun i j : Fin n =>
      sourcePrincipalSchurGraph n e
        ((Z.reindex e e).toBlocks₁₁)
        ((Z.reindex e e).toBlocks₁₂)
        (reindexedRectSchurComplement Z e e) i j) = Z := by
  let M : Matrix (r ⊕ q) (r ⊕ q) ℂ := Z.reindex e e
  have hM_sym : Mᵀ = M := by
    ext x y
    simpa [M, Matrix.transpose, Matrix.reindex] using
      congr_fun (congr_fun hZsym (e.symm x)) (e.symm y)
  have hD : M.toBlocks₂₁ = M.toBlocks₁₂ᵀ := by
    ext a b
    have h := congr_fun (congr_fun hM_sym (Sum.inl b)) (Sum.inr a)
    simpa [Matrix.transpose, Matrix.toBlocks₂₁, Matrix.toBlocks₁₂] using h
  have hC :
      reindexedRectSchurComplement Z e e +
          M.toBlocks₁₂ᵀ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂ =
        M.toBlocks₂₂ := by
    change
      M.toBlocks₂₂ - M.toBlocks₂₁ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂ +
          M.toBlocks₁₂ᵀ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂ =
        M.toBlocks₂₂
    rw [hD]
    abel
  have hgraph_reindex :
      ((Matrix.of fun i j : Fin n =>
        sourcePrincipalSchurGraph n e
          ((Z.reindex e e).toBlocks₁₁)
          ((Z.reindex e e).toBlocks₁₂)
          (reindexedRectSchurComplement Z e e) i j).reindex e e) = M := by
    ext x y
    cases x with
    | inl a =>
        cases y with
        | inl b =>
            simp [sourcePrincipalSchurGraph, M, Matrix.reindex, Matrix.fromBlocks,
              Matrix.toBlocks₁₁]
        | inr b =>
            simp [sourcePrincipalSchurGraph, M, Matrix.reindex, Matrix.fromBlocks,
              Matrix.toBlocks₁₂]
    | inr a =>
        cases y with
        | inl b =>
            have h := congr_fun (congr_fun hD a) b
            simpa [sourcePrincipalSchurGraph, M, Matrix.reindex, Matrix.fromBlocks,
              Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.transpose] using h.symm
        | inr b =>
            have h := congr_fun (congr_fun hC a) b
            simpa [sourcePrincipalSchurGraph, M, Matrix.reindex, Matrix.fromBlocks,
              Matrix.toBlocks₂₂, Matrix.toBlocks₁₂] using h
  ext i j
  have h := congr_fun (congr_fun hgraph_reindex (e i)) (e j)
  simpa [M, Matrix.reindex] using h

/-- The principal block of a symmetric reindexed matrix is symmetric. -/
theorem principalBlock_transpose_eq_of_symmetric
    (n : ℕ) {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (e : Fin n ≃ r ⊕ q)
    {Z : Matrix (Fin n) (Fin n) ℂ}
    (hZsym : Zᵀ = Z) :
    ((Z.reindex e e).toBlocks₁₁)ᵀ =
      (Z.reindex e e).toBlocks₁₁ := by
  ext i j
  simpa [Matrix.transpose, Matrix.reindex, Matrix.toBlocks₁₁] using
    congr_fun (congr_fun hZsym (e.symm (Sum.inl i))) (e.symm (Sum.inl j))

/-- The Schur-complement coordinate of a symmetric reindexed matrix is
symmetric. -/
theorem reindexedRectSchurComplement_transpose_eq_of_symmetric
    (n : ℕ) {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (e : Fin n ≃ r ⊕ q)
    {Z : Matrix (Fin n) (Fin n) ℂ}
    (hZsym : Zᵀ = Z) :
    (reindexedRectSchurComplement Z e e)ᵀ =
      reindexedRectSchurComplement Z e e := by
  let M : Matrix (r ⊕ q) (r ⊕ q) ℂ := Z.reindex e e
  have hM_sym : Mᵀ = M := by
    ext x y
    simpa [M, Matrix.transpose, Matrix.reindex] using
      congr_fun (congr_fun hZsym (e.symm x)) (e.symm y)
  have hA_sym : M.toBlocks₁₁ᵀ = M.toBlocks₁₁ := by
    ext a b
    have h := congr_fun (congr_fun hM_sym (Sum.inl a)) (Sum.inl b)
    simpa [Matrix.transpose, Matrix.toBlocks₁₁] using h
  have hD : M.toBlocks₂₁ = M.toBlocks₁₂ᵀ := by
    ext a b
    have h := congr_fun (congr_fun hM_sym (Sum.inl b)) (Sum.inr a)
    simpa [Matrix.transpose, Matrix.toBlocks₂₁, Matrix.toBlocks₁₂] using h
  have hC_sym : M.toBlocks₂₂ᵀ = M.toBlocks₂₂ := by
    ext a b
    have h := congr_fun (congr_fun hM_sym (Sum.inr a)) (Sum.inr b)
    simpa [Matrix.transpose, Matrix.toBlocks₂₂] using h
  have hInv : M.toBlocks₁₁⁻¹ᵀ = M.toBlocks₁₁⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hA_sym]
  have hterm :
      (M.toBlocks₂₁ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂)ᵀ =
        M.toBlocks₂₁ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂ := by
    rw [hD]
    simp [Matrix.transpose_mul, hInv, Matrix.mul_assoc]
  change
    (M.toBlocks₂₂ - M.toBlocks₂₁ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂)ᵀ =
      M.toBlocks₂₂ - M.toBlocks₂₁ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂
  rw [Matrix.transpose_sub, hC_sym, hterm]

theorem sourcePrincipalSchurGraph_mem_symmetric
    (n : ℕ) {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (e : Fin n ≃ r ⊕ q)
    {A : Matrix r r ℂ} {S : Matrix q q ℂ} (B : Matrix r q ℂ)
    (hA_sym : Aᵀ = A) (hS_sym : Sᵀ = S) :
    sourcePrincipalSchurGraph n e A B S ∈
      sourceSymmetricMatrixSpace n := by
  have hA_entry : ∀ i j, A i j = A j i := by
    intro i j
    simpa [Matrix.transpose] using congr_fun (congr_fun hA_sym j) i
  have hS_entry : ∀ i j, S i j = S j i := by
    intro i j
    simpa [Matrix.transpose] using congr_fun (congr_fun hS_sym j) i
  have hBsym : (Bᵀ * A⁻¹ * B)ᵀ = Bᵀ * A⁻¹ * B := by
    have hInv : (A⁻¹)ᵀ = A⁻¹ := by
      rw [Matrix.transpose_nonsing_inv, hA_sym]
    simp [Matrix.transpose_mul, Matrix.mul_assoc, hInv]
  have hB_entry :
      ∀ i j, (Bᵀ * A⁻¹ * B) i j = (Bᵀ * A⁻¹ * B) j i := by
    intro i j
    simpa [Matrix.transpose] using congr_fun (congr_fun hBsym j) i
  intro i j
  simp only [sourcePrincipalSchurGraph]
  cases e i <;> cases e j <;>
    simp [Matrix.fromBlocks, hA_entry, hS_entry, hB_entry]

theorem sourcePrincipalSchurGraph_mem_rankLE_iff
    (n D : ℕ) {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (e : Fin n ≃ r ⊕ q)
    {A : Matrix r r ℂ} (hA_unit : IsUnit A.det)
    (hA_sym : Aᵀ = A)
    {B : Matrix r q ℂ} {S : Matrix q q ℂ}
    (hS_sym : Sᵀ = S) (hrD : Fintype.card r ≤ D) :
    sourcePrincipalSchurGraph n e A B S ∈
        sourceSymmetricRankLEVariety n D ↔
      S.rank ≤ D - Fintype.card r := by
  let G : Fin n → Fin n → ℂ := sourcePrincipalSchurGraph n e A B S
  have hblock :
      IsUnit (((Matrix.of fun i j : Fin n => G i j).reindex e e).toBlocks₁₁.det) := by
    rw [show ((Matrix.of fun i j : Fin n => G i j).reindex e e).toBlocks₁₁ = A by
      simpa [G] using sourcePrincipalSchurGraph_toBlocks₁₁ n e A B S]
    exact hA_unit
  have hschur :
      ((Matrix.of fun i j : Fin n => G i j).reindex e e).toBlocks₂₂ -
          ((Matrix.of fun i j : Fin n => G i j).reindex e e).toBlocks₂₁ *
            ((Matrix.of fun i j : Fin n => G i j).reindex e e).toBlocks₁₁⁻¹ *
            ((Matrix.of fun i j : Fin n => G i j).reindex e e).toBlocks₁₂ = S := by
    simpa [G] using sourcePrincipalSchurGraph_schurComplement n e A B S
  rw [sourceSymmetricRankLEVariety_iff_principal_schur_rank_le
    n D e (Z := G) hblock hrD]
  constructor
  · intro h
    rw [hschur] at h
    exact h.2
  · intro h
    refine ⟨sourcePrincipalSchurGraph_mem_symmetric n e B hA_sym hS_sym, ?_⟩
    rw [hschur]
    exact h

theorem sourcePrincipalSchurGraph_mem_rankExact_iff
    (n D : ℕ) {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (e : Fin n ≃ r ⊕ q)
    {A : Matrix r r ℂ} (hA_unit : IsUnit A.det)
    (hA_sym : Aᵀ = A)
    {B : Matrix r q ℂ} {S : Matrix q q ℂ}
    (hS_sym : Sᵀ = S) (hrD : Fintype.card r ≤ D) :
    sourcePrincipalSchurGraph n e A B S ∈
        sourceSymmetricRankExactStratum n D ↔
      S.rank = D - Fintype.card r := by
  let G : Fin n → Fin n → ℂ := sourcePrincipalSchurGraph n e A B S
  have hblock :
      IsUnit (((Matrix.of fun i j : Fin n => G i j).reindex e e).toBlocks₁₁.det) := by
    rw [show ((Matrix.of fun i j : Fin n => G i j).reindex e e).toBlocks₁₁ = A by
      simpa [G] using sourcePrincipalSchurGraph_toBlocks₁₁ n e A B S]
    exact hA_unit
  have hschur :
      ((Matrix.of fun i j : Fin n => G i j).reindex e e).toBlocks₂₂ -
          ((Matrix.of fun i j : Fin n => G i j).reindex e e).toBlocks₂₁ *
            ((Matrix.of fun i j : Fin n => G i j).reindex e e).toBlocks₁₁⁻¹ *
            ((Matrix.of fun i j : Fin n => G i j).reindex e e).toBlocks₁₂ = S := by
    simpa [G] using sourcePrincipalSchurGraph_schurComplement n e A B S
  rw [sourceSymmetricRankExactStratum_iff_principal_schur_rank_eq
    n D e (Z := G) hblock hrD]
  constructor
  · intro h
    rw [hschur] at h
    exact h.2
  · intro h
    refine ⟨sourcePrincipalSchurGraph_mem_symmetric n e B hA_sym hS_sym, ?_⟩
    rw [hschur]
    exact h

/-- Matrix inversion is continuous on the determinant-unit locus.  This is the
topological input for continuity of the Schur graph on a principal patch. -/
theorem continuousOn_matrix_inv_of_isUnit_det
    {q : Type*} [Fintype q] [DecidableEq q] :
    ContinuousOn (fun A : Matrix q q ℂ => A⁻¹)
      {A : Matrix q q ℂ | IsUnit A.det} := by
  intro A hA
  have hcont : ContinuousAt (fun z : ℂ => Ring.inverse z) A.det := by
    simpa [Ring.inverse_eq_inv] using
      (ContinuousInv₀.continuousAt_inv₀ hA.ne_zero : ContinuousAt Inv.inv A.det)
  exact (continuousAt_matrix_inv A hcont).continuousWithinAt

/-- Coordinate form of determinant-unit inverse continuity for the product
coordinates used by the Schur graph. -/
theorem continuousOn_sourceSchurProduct_invEntry_of_isUnit_det
    {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q] (i j : r) :
    ContinuousOn
      (fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ => p.1⁻¹ i j)
      {p | IsUnit p.1.det} := by
  intro p hp
  have hInvA : ContinuousWithinAt (fun A : Matrix r r ℂ => A⁻¹)
      {A : Matrix r r ℂ | IsUnit A.det} p.1 :=
    continuousOn_matrix_inv_of_isUnit_det p.1 hp
  have hfst : ContinuousWithinAt
      (fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ => p.1)
      {p | IsUnit p.1.det} p := by
    exact continuous_fst.continuousAt.continuousWithinAt
  have hcomp : ContinuousWithinAt
      ((fun A : Matrix r r ℂ => A⁻¹) ∘
        (fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ => p.1))
      {p | IsUnit p.1.det} p :=
    hInvA.comp hfst (by intro z hz; exact hz)
  have hi : ContinuousWithinAt (fun M : Matrix r r ℂ => M i)
      Set.univ (((fun A : Matrix r r ℂ => A⁻¹) ∘
        (fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ => p.1)) p) :=
    (continuous_apply i).continuousAt.continuousWithinAt
  have hrow : ContinuousWithinAt
      ((fun M : Matrix r r ℂ => M i) ∘
        ((fun A : Matrix r r ℂ => A⁻¹) ∘
          (fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ => p.1)))
      {p | IsUnit p.1.det} p :=
    hi.comp hcomp (by intro z hz; trivial)
  have hj : ContinuousWithinAt (fun row : r → ℂ => row j)
      Set.univ ((((fun M : Matrix r r ℂ => M i) ∘
        ((fun A : Matrix r r ℂ => A⁻¹) ∘
          (fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ => p.1))) p)) :=
    (continuous_apply j).continuousAt.continuousWithinAt
  have hentry : ContinuousWithinAt
      ((fun row : r → ℂ => row j) ∘
        ((fun M : Matrix r r ℂ => M i) ∘
          ((fun A : Matrix r r ℂ => A⁻¹) ∘
            (fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ => p.1))))
      {p | IsUnit p.1.det} p :=
    hj.comp hrow (by intro z hz; trivial)
  simpa [Function.comp_def] using hentry

/-- The principal Schur graph is continuous on the determinant-unit principal
block patch.  The proof is intentionally coordinatewise to avoid expanding the
whole matrix expression at once. -/
theorem continuousOn_sourcePrincipalSchurGraph
    (n : ℕ) {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (e : Fin n ≃ r ⊕ q) :
    ContinuousOn
      (fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ =>
        sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2)
      {p | IsUnit p.1.det} := by
  rw [continuousOn_pi]
  intro i
  rw [continuousOn_pi]
  intro j
  unfold sourcePrincipalSchurGraph
  cases e i <;> cases e j
  · simp [Matrix.fromBlocks]
    fun_prop
  · simp [Matrix.fromBlocks]
    fun_prop
  · simp [Matrix.fromBlocks]
    fun_prop
  · rename_i a b
    simp [Matrix.fromBlocks]
    have hinner_term : ∀ x y : r, ContinuousOn
        (fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ =>
          p.2.1 y a * p.1⁻¹ y x)
        {p | IsUnit p.1.det} := by
      intro x y
      have h1 : ContinuousOn
          (fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ => p.2.1 y a)
          {p | IsUnit p.1.det} := by fun_prop
      have h2 : ContinuousOn
          (fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ => p.1⁻¹ y x)
          {p | IsUnit p.1.det} :=
        continuousOn_sourceSchurProduct_invEntry_of_isUnit_det y x
      exact h1.mul h2
    have hinner : ∀ x : r, ContinuousOn
        (fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ =>
          ∑ y : r, p.2.1 y a * p.1⁻¹ y x)
        {p | IsUnit p.1.det} := by
      intro x
      simpa using
        (continuousOn_finset_sum (Finset.univ : Finset r)
          (fun y _ => hinner_term x y))
    have hterm : ∀ x : r, ContinuousOn
        (fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ =>
          (∑ y : r, p.2.1 y a * p.1⁻¹ y x) * p.2.1 x b)
        {p | IsUnit p.1.det} := by
      intro x
      have hB : ContinuousOn
          (fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ => p.2.1 x b)
          {p | IsUnit p.1.det} := by fun_prop
      exact (hinner x).mul hB
    have hsum : ContinuousOn
        (fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ =>
          ∑ x : r, (∑ y : r, p.2.1 y a * p.1⁻¹ y x) * p.2.1 x b)
        {p | IsUnit p.1.det} := by
      simpa using
        (continuousOn_finset_sum (Finset.univ : Finset r)
          (fun x _ => hterm x))
    have hS : ContinuousOn
        (fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ => p.2.2 a b)
        {p | IsUnit p.1.det} := by fun_prop
    have hadd := hS.add hsum
    simpa [Matrix.mul_apply] using hadd

/-- Continuity of the principal Schur graph gives product neighborhoods whose
graph image lies in a prescribed open ambient neighborhood.  The `A`
neighborhood is chosen inside the determinant-unit locus. -/
theorem exists_sourcePrincipalSchurGraph_product_subset_open
    (n : ℕ) {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (e : Fin n ≃ r ⊕ q)
    {A0 : Matrix r r ℂ} {B0 : Matrix r q ℂ} {S0 : Matrix q q ℂ}
    (hA0_unit : IsUnit A0.det)
    {N0 : Set (Fin n → Fin n → ℂ)}
    (hN0_open : IsOpen N0)
    (hG0N0 : sourcePrincipalSchurGraph n e A0 B0 S0 ∈ N0) :
    ∃ Aset : Set (Matrix r r ℂ),
    ∃ Bset : Set (Matrix r q ℂ),
    ∃ Sset : Set (Matrix q q ℂ),
      IsOpen Aset ∧ A0 ∈ Aset ∧
      IsOpen Bset ∧ B0 ∈ Bset ∧
      IsOpen Sset ∧ S0 ∈ Sset ∧
      (∀ A ∈ Aset, IsUnit A.det) ∧
      ((fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ =>
          sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2) ''
        {p | p.1 ∈ Aset ∧ p.2.1 ∈ Bset ∧ p.2.2 ∈ Sset}) ⊆ N0 := by
  let F : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ →
      Fin n → Fin n → ℂ :=
    fun p => sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2
  let p0 : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ := (A0, B0, S0)
  let unitPatch : Set (Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ) :=
    {p | IsUnit p.1.det}
  have hunit_open : IsOpen unitPatch := by
    have hdet : Continuous
        (fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ => p.1.det) := by
      have hdet_matrix : Continuous (fun A : Matrix r r ℂ => A.det) := by
        fun_prop
      exact hdet_matrix.comp continuous_fst
    simpa [unitPatch, isUnit_iff_ne_zero] using
      (isOpen_ne_fun hdet continuous_const)
  have hW_open : IsOpen (unitPatch ∩ F ⁻¹' N0) := by
    exact
      (continuousOn_sourcePrincipalSchurGraph n e).isOpen_inter_preimage
        hunit_open hN0_open
  have hp0W : p0 ∈ unitPatch ∩ F ⁻¹' N0 := by
    exact ⟨hA0_unit, hG0N0⟩
  have hW_nhds : unitPatch ∩ F ⁻¹' N0 ∈ 𝓝 p0 :=
    hW_open.mem_nhds hp0W
  rcases (mem_nhds_prod_iff'.mp hW_nhds) with
    ⟨Aset, BSset, hAset_open, hA0A, hBSset_open, hBS0, hprod_sub⟩
  have hBS_nhds : BSset ∈ 𝓝 (B0, S0) :=
    hBSset_open.mem_nhds hBS0
  rcases (mem_nhds_prod_iff'.mp hBS_nhds) with
    ⟨Bset, Sset, hBset_open, hB0B, hSset_open, hS0S, hBS_sub⟩
  refine ⟨Aset, Bset, Sset,
    hAset_open, hA0A, hBset_open, hB0B, hSset_open, hS0S, ?_, ?_⟩
  · intro A hA
    have hp : (A, (B0, S0)) ∈ Aset ×ˢ BSset := ⟨hA, hBS0⟩
    exact (hprod_sub hp).1
  · rintro G ⟨p, hp, rfl⟩
    have hpBS : (p.2.1, p.2.2) ∈ BSset :=
      hBS_sub ⟨hp.2.1, hp.2.2⟩
    exact (hprod_sub ⟨hp.1, hpBS⟩).2

/-- Connectedness of the rank-exact Schur-graph parameter image.  The
rank-exact condition is imposed on the Schur-complement coordinate; the next
lemma records that the corresponding graph points are rank-exact in the source
matrix. -/
theorem isConnected_sourcePrincipalSchurGraph_rankExact_image
    (n D : ℕ) {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (e : Fin n ≃ r ⊕ q)
    {Aset : Set (Matrix r r ℂ)}
    {Bset : Set (Matrix r q ℂ)}
    {Sset : Set (Matrix q q ℂ)}
    (hA_conn : IsConnected Aset)
    (hB_conn : IsConnected Bset)
    (hS_conn :
      IsConnected
        (Sset ∩ {S : Matrix q q ℂ |
          Sᵀ = S ∧ S.rank = D - Fintype.card r}))
    (hA_unit : ∀ A ∈ Aset, IsUnit A.det) :
    IsConnected
      ((fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ =>
          sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2) ''
        {p | p.1 ∈ Aset ∧ p.2.1 ∈ Bset ∧
          p.2.2 ∈ Sset ∩ {S : Matrix q q ℂ |
            Sᵀ = S ∧ S.rank = D - Fintype.card r}}) := by
  have hparam : IsConnected
      {p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ |
        p.1 ∈ Aset ∧ p.2.1 ∈ Bset ∧
          p.2.2 ∈ Sset ∩ {S : Matrix q q ℂ |
            Sᵀ = S ∧ S.rank = D - Fintype.card r}} := by
    have hprod : IsConnected
        (Aset ×ˢ (Bset ×ˢ
          (Sset ∩ {S : Matrix q q ℂ |
            Sᵀ = S ∧ S.rank = D - Fintype.card r}))) :=
      hA_conn.prod (hB_conn.prod hS_conn)
    simpa [Set.prod] using hprod
  exact hparam.image _
    ((continuousOn_sourcePrincipalSchurGraph n e).mono (by
      intro p hp
      exact hA_unit p.1 hp.1))

/-- The rank-exact Schur-graph parameter image is contained in the source
rank-exact symmetric stratum. -/
theorem sourcePrincipalSchurGraph_rankExact_image_subset
    (n D : ℕ) {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (e : Fin n ≃ r ⊕ q)
    {Aset : Set (Matrix r r ℂ)}
    {Bset : Set (Matrix r q ℂ)}
    {Sset : Set (Matrix q q ℂ)}
    (hA_unit : ∀ A ∈ Aset, IsUnit A.det)
    (hA_sym : ∀ A ∈ Aset, Aᵀ = A)
    (hrD : Fintype.card r ≤ D) :
    ((fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ =>
        sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2) ''
      {p | p.1 ∈ Aset ∧ p.2.1 ∈ Bset ∧
        p.2.2 ∈ Sset ∩ {S : Matrix q q ℂ |
          Sᵀ = S ∧ S.rank = D - Fintype.card r}}) ⊆
      sourceSymmetricRankExactStratum n D := by
  rintro G ⟨p, hp, rfl⟩
  have hAunit : IsUnit p.1.det := hA_unit p.1 hp.1
  have hAsym : p.1ᵀ = p.1 := hA_sym p.1 hp.1
  have hSsym : p.2.2ᵀ = p.2.2 := hp.2.2.2.1
  have hSrank : p.2.2.rank = D - Fintype.card r := hp.2.2.2.2
  exact
    (sourcePrincipalSchurGraph_mem_rankExact_iff
      n D e hAunit hAsym hSsym hrD).mpr hSrank

/-- On a Schur coordinate patch whose graph is contained in an ambient
neighborhood `N0`, the rank-exact part of the patch is exactly the graph image
of the rank-exact Schur-complement parameter set. -/
theorem sourcePrincipalSchurGraph_rankExact_image_eq_coordinatePatch
    (n D : ℕ) {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (e : Fin n ≃ r ⊕ q)
    {N0 : Set (Fin n → Fin n → ℂ)}
    {Aset : Set (Matrix r r ℂ)}
    {Bset : Set (Matrix r q ℂ)}
    {Sset : Set (Matrix q q ℂ)}
    (hA_unit : ∀ A ∈ Aset, IsUnit A.det)
    (hA_sym : ∀ A ∈ Aset, Aᵀ = A)
    (hrD : Fintype.card r ≤ D)
    (hgraph_N0 :
      ((fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ =>
          sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2) ''
        {p | p.1 ∈ Aset ∧ p.2.1 ∈ Bset ∧
          p.2.2 ∈ Sset ∩ {S : Matrix q q ℂ |
            Sᵀ = S ∧ S.rank = D - Fintype.card r}}) ⊆ N0) :
    ({Z : Fin n → Fin n → ℂ |
        Z ∈ N0 ∧
        IsUnit
          ((((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₁).det) ∧
        (((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₁) ∈
          Aset ∧
        (((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₂) ∈
          Bset ∧
        reindexedRectSchurComplement (Matrix.of fun i j : Fin n => Z i j) e e ∈
          Sset} ∩ sourceSymmetricRankExactStratum n D) =
      ((fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ =>
          sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2) ''
        {p | p.1 ∈ Aset ∧ p.2.1 ∈ Bset ∧
          p.2.2 ∈ Sset ∩ {S : Matrix q q ℂ |
            Sᵀ = S ∧ S.rank = D - Fintype.card r}}) := by
  ext Z
  constructor
  · intro hZ
    rcases hZ with ⟨hpatch, hZrank⟩
    rcases hpatch with ⟨_hZN0, hUnit, hA, hB, hS⟩
    let M : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => Z i j
    have hM_sym : Mᵀ = M := by
      ext i j
      simpa [M, Matrix.transpose] using hZrank.1 j i
    have hSsym :
        (reindexedRectSchurComplement M e e)ᵀ =
          reindexedRectSchurComplement M e e :=
      reindexedRectSchurComplement_transpose_eq_of_symmetric n e hM_sym
    have hSrank :
        (reindexedRectSchurComplement M e e).rank =
          D - Fintype.card r := by
      have h :=
        (sourceSymmetricRankExactStratum_iff_principal_schur_rank_eq
          n D e hUnit hrD).mp hZrank
      simpa [M] using h.2
    refine ⟨(((M.reindex e e).toBlocks₁₁),
        ((M.reindex e e).toBlocks₁₂),
        reindexedRectSchurComplement M e e), ?_, ?_⟩
    · exact ⟨by simpa [M] using hA, by simpa [M] using hB,
        ⟨by simpa [M] using hS, hSsym, hSrank⟩⟩
    · funext i j
      have hcoord :=
        congr_fun
          (congr_fun
            (sourcePrincipalSchurGraph_coordinates_eq_of_symmetric
              n e hM_sym) i) j
      simpa [M] using hcoord
  · intro hZ
    rcases hZ with ⟨p, hp, rfl⟩
    constructor
    · refine ⟨hgraph_N0 ⟨p, hp, rfl⟩, ?_, ?_, ?_, ?_⟩
      · rw [sourcePrincipalSchurGraph_toBlocks₁₁ n e p.1 p.2.1 p.2.2]
        exact hA_unit p.1 hp.1
      · rw [sourcePrincipalSchurGraph_toBlocks₁₁ n e p.1 p.2.1 p.2.2]
        exact hp.1
      · rw [sourcePrincipalSchurGraph_toBlocks₁₂ n e p.1 p.2.1 p.2.2]
        exact hp.2.1
      · change
          ((Matrix.of fun i j : Fin n =>
              sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2 i j).reindex e e).toBlocks₂₂ -
            ((Matrix.of fun i j : Fin n =>
              sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2 i j).reindex e e).toBlocks₂₁ *
              ((Matrix.of fun i j : Fin n =>
                sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2 i j).reindex e e).toBlocks₁₁⁻¹ *
              ((Matrix.of fun i j : Fin n =>
                sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2 i j).reindex e e).toBlocks₁₂ ∈
            Sset
        rw [sourcePrincipalSchurGraph_schurComplement n e p.1 p.2.1 p.2.2]
        exact hp.2.2.1
    · exact
        (sourcePrincipalSchurGraph_mem_rankExact_iff
          n D e (hA_unit p.1 hp.1) (hA_sym p.1 hp.1)
          hp.2.2.2.1 hrD).mpr hp.2.2.2.2

/-- Variant of the Schur coordinate-patch equality with an open `A` coordinate
set on the left and the corresponding symmetric `A` factor on the graph
parameters.  This is the form used by the local-basis theorem: openness uses
the ambient `Aset`, while connectedness uses `Aset ∩ {A | Aᵀ = A}`. -/
theorem sourcePrincipalSchurGraph_rankExact_image_eq_openCoordinatePatch
    (n D : ℕ) {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (e : Fin n ≃ r ⊕ q)
    {N0 : Set (Fin n → Fin n → ℂ)}
    {Aset : Set (Matrix r r ℂ)}
    {Bset : Set (Matrix r q ℂ)}
    {Sset : Set (Matrix q q ℂ)}
    (hA_unit : ∀ A ∈ Aset, IsUnit A.det)
    (hrD : Fintype.card r ≤ D)
    (hgraph_N0 :
      ((fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ =>
          sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2) ''
        {p | p.1 ∈ Aset ∩ {A : Matrix r r ℂ | Aᵀ = A} ∧
          p.2.1 ∈ Bset ∧
          p.2.2 ∈ Sset ∩ {S : Matrix q q ℂ |
            Sᵀ = S ∧ S.rank = D - Fintype.card r}}) ⊆ N0) :
    ({Z : Fin n → Fin n → ℂ |
        Z ∈ N0 ∧
        IsUnit
          ((((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₁).det) ∧
        (((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₁) ∈
          Aset ∧
        (((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₂) ∈
          Bset ∧
        reindexedRectSchurComplement (Matrix.of fun i j : Fin n => Z i j) e e ∈
          Sset} ∩ sourceSymmetricRankExactStratum n D) =
      ((fun p : Matrix r r ℂ × Matrix r q ℂ × Matrix q q ℂ =>
          sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2) ''
        {p | p.1 ∈ Aset ∩ {A : Matrix r r ℂ | Aᵀ = A} ∧
          p.2.1 ∈ Bset ∧
          p.2.2 ∈ Sset ∩ {S : Matrix q q ℂ |
            Sᵀ = S ∧ S.rank = D - Fintype.card r}}) := by
  let Aexact : Set (Matrix r r ℂ) :=
    Aset ∩ {A : Matrix r r ℂ | Aᵀ = A}
  have hleft_eq :
      ({Z : Fin n → Fin n → ℂ |
          Z ∈ N0 ∧
          IsUnit
            ((((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₁).det) ∧
          (((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₁) ∈
            Aset ∧
          (((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₂) ∈
            Bset ∧
          reindexedRectSchurComplement (Matrix.of fun i j : Fin n => Z i j) e e ∈
            Sset} ∩ sourceSymmetricRankExactStratum n D) =
        ({Z : Fin n → Fin n → ℂ |
          Z ∈ N0 ∧
          IsUnit
            ((((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₁).det) ∧
          (((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₁) ∈
            Aexact ∧
          (((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₂) ∈
            Bset ∧
          reindexedRectSchurComplement (Matrix.of fun i j : Fin n => Z i j) e e ∈
            Sset} ∩ sourceSymmetricRankExactStratum n D) := by
    ext Z
    constructor
    · rintro ⟨hpatch, hZrank⟩
      rcases hpatch with ⟨hZN0, hUnit, hA, hB, hS⟩
      let M : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => Z i j
      have hM_sym : Mᵀ = M := by
        ext i j
        simpa [M, Matrix.transpose] using hZrank.1 j i
      have hA_sym :
          ((M.reindex e e).toBlocks₁₁)ᵀ =
            (M.reindex e e).toBlocks₁₁ :=
        principalBlock_transpose_eq_of_symmetric n e hM_sym
      exact
        ⟨⟨hZN0, hUnit, ⟨by simpa [M] using hA, hA_sym⟩,
          hB, hS⟩, hZrank⟩
    · rintro ⟨hpatch, hZrank⟩
      rcases hpatch with ⟨hZN0, hUnit, hA, hB, hS⟩
      exact ⟨⟨hZN0, hUnit, hA.1, hB, hS⟩, hZrank⟩
  have hcoord :=
    sourcePrincipalSchurGraph_rankExact_image_eq_coordinatePatch
      (n := n) (D := D) (e := e) (N0 := N0)
      (Aset := Aexact) (Bset := Bset) (Sset := Sset)
      (by
        intro A hA
        exact hA_unit A hA.1)
      (by
        intro A hA
        exact hA.2)
      hrD
      (by simpa [Aexact] using hgraph_N0)
  rw [hleft_eq]
  simpa [Aexact] using hcoord

/-- The determinant-unit locus for finite complex matrices is open. -/
theorem isOpen_matrix_det_isUnit
    {r : Type*} [Fintype r] [DecidableEq r] :
    IsOpen ({A : Matrix r r ℂ | IsUnit A.det}) := by
  have hdet : Continuous (fun A : Matrix r r ℂ => A.det) := by fun_prop
  simpa [isUnit_iff_ne_zero] using
    (isOpen_ne_fun hdet continuous_const)

section FrobeniusTopology

open scoped Matrix.Norms.Frobenius

/-- Every determinant-unit matrix has a small ball contained in the
determinant-unit locus. -/
theorem exists_pos_ball_subset_isUnit_det
    {r : Type*} [Fintype r] [DecidableEq r]
    {A0 : Matrix r r ℂ} (hA0 : IsUnit A0.det) :
    ∃ ε : ℝ, 0 < ε ∧
      Metric.ball A0 ε ⊆ {A : Matrix r r ℂ | IsUnit A.det} := by
  have hnhds : ({A : Matrix r r ℂ | IsUnit A.det}) ∈ 𝓝 A0 :=
    isOpen_matrix_det_isUnit.mem_nhds hA0
  rw [Metric.mem_nhds_iff] at hnhds
  rcases hnhds with ⟨ε, hε, hsub⟩
  exact ⟨ε, hε, hsub⟩

/-- A small ball in the affine space of symmetric matrices is connected. -/
theorem isConnected_symmetric_matrix_ball
    {r : Type*} [Fintype r] [DecidableEq r]
    {A0 : Matrix r r ℂ} (hA0sym : A0ᵀ = A0)
    {ε : ℝ} (hε : 0 < ε) :
    IsConnected (Metric.ball A0 ε ∩ {A : Matrix r r ℂ | Aᵀ = A}) := by
  have hsymConvex : Convex ℝ ({A : Matrix r r ℂ | Aᵀ = A}) := by
    intro A hA B hB a b ha hb hab
    ext i j
    have hAij : A j i = A i j := by
      simpa [Matrix.transpose] using congr_fun (congr_fun hA i) j
    have hBij : B j i = B i j := by
      simpa [Matrix.transpose] using congr_fun (congr_fun hB i) j
    simp [Matrix.transpose, hAij, hBij]
  have hconv : Convex ℝ
      (Metric.ball A0 ε ∩ {A : Matrix r r ℂ | Aᵀ = A}) :=
    (convex_ball A0 ε).inter hsymConvex
  have hne : (Metric.ball A0 ε ∩
      {A : Matrix r r ℂ | Aᵀ = A}).Nonempty :=
    ⟨A0, Metric.mem_ball_self hε, hA0sym⟩
  exact hconv.isConnected hne

/-- An ordinary matrix ball is connected. -/
theorem isConnected_matrix_ball
    {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (B0 : Matrix r q ℂ) {ε : ℝ} (hε : 0 < ε) :
    IsConnected (Metric.ball B0 ε) := by
  exact (convex_ball B0 ε).isConnected ⟨B0, Metric.mem_ball_self hε⟩

end FrobeniusTopology

/-- Coordinate evaluation on a matrix is continuous. -/
theorem continuous_matrix_entry
    {ι κ : Type*} (i : ι) (j : κ) :
    Continuous (fun Z : Matrix ι κ ℂ => Z i j) :=
  (continuous_apply j).comp (continuous_apply i)

/-- Coordinate evaluation on a matrix is continuous on every set. -/
theorem continuousOn_matrix_entry
    {ι κ : Type*} (i : ι) (j : κ)
    (s : Set (Matrix ι κ ℂ)) :
    ContinuousOn (fun Z : Matrix ι κ ℂ => Z i j) s := by
  intro Z hZ
  have hrow : ContinuousWithinAt (fun Z : Matrix ι κ ℂ => Z i) s Z :=
    (continuous_apply i).continuousAt.continuousWithinAt
  have hcol : ContinuousWithinAt (fun row : κ → ℂ => row j)
      Set.univ (Z i) :=
    (continuous_apply j).continuousAt.continuousWithinAt
  have hentry : ContinuousWithinAt
      ((fun row : κ → ℂ => row j) ∘
        (fun Z : Matrix ι κ ℂ => Z i)) s Z :=
    ContinuousWithinAt.comp
      (f := fun Z : Matrix ι κ ℂ => Z i)
      (g := fun row : κ → ℂ => row j)
      hcol hrow (by intro W hW; trivial)
  simpa [Function.comp_def] using hentry

/-- Coordinate continuity of the inverse of the principal block in a Schur
patch. -/
theorem continuousOn_principalBlock_invEntry
    (n : ℕ) {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (e : Fin n ≃ r ⊕ q) (i j : r) :
    ContinuousOn
      (fun Z : Matrix (Fin n) (Fin n) ℂ =>
        ((Z.reindex e e).toBlocks₁₁)⁻¹ i j)
      {Z | IsUnit ((Z.reindex e e).toBlocks₁₁.det)} := by
  intro Z hZ
  have hInvA : ContinuousWithinAt (fun A : Matrix r r ℂ => A⁻¹)
      {A : Matrix r r ℂ | IsUnit A.det} ((Z.reindex e e).toBlocks₁₁) :=
    continuousOn_matrix_inv_of_isUnit_det ((Z.reindex e e).toBlocks₁₁) hZ
  have hblock : ContinuousWithinAt
      (fun Z : Matrix (Fin n) (Fin n) ℂ => (Z.reindex e e).toBlocks₁₁)
      {Z | IsUnit ((Z.reindex e e).toBlocks₁₁.det)} Z := by
    change ContinuousWithinAt
      (fun Z : Matrix (Fin n) (Fin n) ℂ =>
        fun i j => (Z.reindex e e).toBlocks₁₁ i j)
      {Z | IsUnit ((Z.reindex e e).toBlocks₁₁.det)} Z
    rw [continuousWithinAt_pi]
    intro i
    rw [continuousWithinAt_pi]
    intro j
    simpa [Matrix.reindex, Matrix.toBlocks₁₁, isUnit_iff_ne_zero] using
      continuousOn_matrix_entry
        (e.symm (Sum.inl i)) (e.symm (Sum.inl j))
        {Z | IsUnit ((Z.reindex e e).toBlocks₁₁.det)} Z hZ
  have hcomp : ContinuousWithinAt
      ((fun A : Matrix r r ℂ => A⁻¹) ∘
        (fun Z : Matrix (Fin n) (Fin n) ℂ => (Z.reindex e e).toBlocks₁₁))
      {Z | IsUnit ((Z.reindex e e).toBlocks₁₁.det)} Z :=
    ContinuousWithinAt.comp
      (f := fun Z : Matrix (Fin n) (Fin n) ℂ => (Z.reindex e e).toBlocks₁₁)
      (g := fun A : Matrix r r ℂ => A⁻¹)
      hInvA hblock (by intro W hW; exact hW)
  have hi : ContinuousWithinAt (fun M : Matrix r r ℂ => M i)
      Set.univ (((fun A : Matrix r r ℂ => A⁻¹) ∘
        (fun Z : Matrix (Fin n) (Fin n) ℂ => (Z.reindex e e).toBlocks₁₁)) Z) :=
    (continuous_apply i).continuousAt.continuousWithinAt
  have hrow : ContinuousWithinAt
      ((fun M : Matrix r r ℂ => M i) ∘
        ((fun A : Matrix r r ℂ => A⁻¹) ∘
          (fun Z : Matrix (Fin n) (Fin n) ℂ => (Z.reindex e e).toBlocks₁₁)))
      {Z | IsUnit ((Z.reindex e e).toBlocks₁₁.det)} Z :=
    hi.comp hcomp (by intro W hW; trivial)
  have hj : ContinuousWithinAt (fun row : r → ℂ => row j)
      Set.univ ((((fun M : Matrix r r ℂ => M i) ∘
        ((fun A : Matrix r r ℂ => A⁻¹) ∘
          (fun Z : Matrix (Fin n) (Fin n) ℂ => (Z.reindex e e).toBlocks₁₁))) Z)) :=
    (continuous_apply j).continuousAt.continuousWithinAt
  have hentry : ContinuousWithinAt
      ((fun row : r → ℂ => row j) ∘
        ((fun M : Matrix r r ℂ => M i) ∘
          ((fun A : Matrix r r ℂ => A⁻¹) ∘
            (fun Z : Matrix (Fin n) (Fin n) ℂ => (Z.reindex e e).toBlocks₁₁))))
      {Z | IsUnit ((Z.reindex e e).toBlocks₁₁.det)} Z :=
    hj.comp hrow (by intro W hW; trivial)
  simpa [Function.comp_def] using hentry

/-- The Schur-complement coordinate is continuous on the determinant-unit
principal patch. -/
theorem continuousOn_reindexedPrincipalSchurComplement
    (n : ℕ) {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (e : Fin n ≃ r ⊕ q) :
    ContinuousOn
      (fun Z : Matrix (Fin n) (Fin n) ℂ =>
        reindexedRectSchurComplement Z e e)
      {Z | IsUnit ((Z.reindex e e).toBlocks₁₁.det)} := by
  change ContinuousOn
    (fun Z : Matrix (Fin n) (Fin n) ℂ =>
      fun a b => reindexedRectSchurComplement Z e e a b)
    {Z | IsUnit ((Z.reindex e e).toBlocks₁₁.det)}
  rw [continuousOn_pi]
  intro a
  rw [continuousOn_pi]
  intro b
  unfold reindexedRectSchurComplement
  simp [Matrix.mul_apply]
  have hinner_term : ∀ x y : r, ContinuousOn
      (fun Z : Matrix (Fin n) (Fin n) ℂ =>
        (Z.reindex e e).toBlocks₂₁ a y *
          ((Z.reindex e e).toBlocks₁₁)⁻¹ y x)
      {Z | IsUnit ((Z.reindex e e).toBlocks₁₁.det)} := by
    intro x y
    have h1 : ContinuousOn
        (fun Z : Matrix (Fin n) (Fin n) ℂ => (Z.reindex e e).toBlocks₂₁ a y)
        {Z | IsUnit ((Z.reindex e e).toBlocks₁₁.det)} := by
      simpa [Matrix.reindex, Matrix.toBlocks₂₁] using
        (continuousOn_matrix_entry
          (e.symm (Sum.inr a)) (e.symm (Sum.inl y))
          {Z : Matrix (Fin n) (Fin n) ℂ |
            IsUnit ((Z.reindex e e).toBlocks₁₁.det)})
    have h2 : ContinuousOn
        (fun Z : Matrix (Fin n) (Fin n) ℂ =>
          ((Z.reindex e e).toBlocks₁₁)⁻¹ y x)
        {Z | IsUnit ((Z.reindex e e).toBlocks₁₁.det)} :=
      continuousOn_principalBlock_invEntry n e y x
    exact h1.mul h2
  have hinner : ∀ x : r, ContinuousOn
      (fun Z : Matrix (Fin n) (Fin n) ℂ =>
        ∑ y : r,
          (Z.reindex e e).toBlocks₂₁ a y *
            ((Z.reindex e e).toBlocks₁₁)⁻¹ y x)
      {Z | IsUnit ((Z.reindex e e).toBlocks₁₁.det)} := by
    intro x
    simpa using
      (continuousOn_finset_sum (Finset.univ : Finset r)
        (fun y _ => hinner_term x y))
  have hterm : ∀ x : r, ContinuousOn
      (fun Z : Matrix (Fin n) (Fin n) ℂ =>
        (∑ y : r,
          (Z.reindex e e).toBlocks₂₁ a y *
            ((Z.reindex e e).toBlocks₁₁)⁻¹ y x) *
          (Z.reindex e e).toBlocks₁₂ x b)
      {Z | IsUnit ((Z.reindex e e).toBlocks₁₁.det)} := by
    intro x
    have hB : ContinuousOn
        (fun Z : Matrix (Fin n) (Fin n) ℂ => (Z.reindex e e).toBlocks₁₂ x b)
        {Z | IsUnit ((Z.reindex e e).toBlocks₁₁.det)} := by
      simpa [Matrix.reindex, Matrix.toBlocks₁₂] using
        (continuousOn_matrix_entry
          (e.symm (Sum.inl x)) (e.symm (Sum.inr b))
          {Z : Matrix (Fin n) (Fin n) ℂ |
            IsUnit ((Z.reindex e e).toBlocks₁₁.det)})
    exact (hinner x).mul hB
  have hsum : ContinuousOn
      (fun Z : Matrix (Fin n) (Fin n) ℂ =>
        ∑ x : r,
          (∑ y : r,
            (Z.reindex e e).toBlocks₂₁ a y *
              ((Z.reindex e e).toBlocks₁₁)⁻¹ y x) *
            (Z.reindex e e).toBlocks₁₂ x b)
      {Z | IsUnit ((Z.reindex e e).toBlocks₁₁.det)} := by
    simpa using
      (continuousOn_finset_sum (Finset.univ : Finset r)
        (fun x _ => hterm x))
  have hC : ContinuousOn
      (fun Z : Matrix (Fin n) (Fin n) ℂ => (Z.reindex e e).toBlocks₂₂ a b)
      {Z | IsUnit ((Z.reindex e e).toBlocks₁₁.det)} := by
    simpa [Matrix.reindex, Matrix.toBlocks₂₂] using
      (continuousOn_matrix_entry
        (e.symm (Sum.inr a)) (e.symm (Sum.inr b))
        {Z : Matrix (Fin n) (Fin n) ℂ |
          IsUnit ((Z.reindex e e).toBlocks₁₁.det)})
  have hsub := hC.sub hsum
  simpa [Matrix.mul_apply] using hsub

/-- The determinant-unit Schur coordinate patch cut out by open conditions on
`Z`, `A`, `B`, and the Schur complement is open. -/
theorem isOpen_sourcePrincipalSchurCoordinatePatch
    (n : ℕ) {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (e : Fin n ≃ r ⊕ q)
    {N0 : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hN0_open : IsOpen N0)
    {Aset : Set (Matrix r r ℂ)}
    (hAset_open : IsOpen Aset)
    {Bset : Set (Matrix r q ℂ)}
    (hBset_open : IsOpen Bset)
    {Sset : Set (Matrix q q ℂ)}
    (hSset_open : IsOpen Sset) :
    IsOpen
      {Z : Matrix (Fin n) (Fin n) ℂ |
        Z ∈ N0 ∧
        IsUnit ((Z.reindex e e).toBlocks₁₁.det) ∧
        (Z.reindex e e).toBlocks₁₁ ∈ Aset ∧
        (Z.reindex e e).toBlocks₁₂ ∈ Bset ∧
        reindexedRectSchurComplement Z e e ∈ Sset} := by
  let unitPatch : Set (Matrix (Fin n) (Fin n) ℂ) :=
    {Z | IsUnit ((Z.reindex e e).toBlocks₁₁.det)}
  have hblock11 : Continuous
      (fun Z : Matrix (Fin n) (Fin n) ℂ =>
        (Z.reindex e e).toBlocks₁₁) := by
    change Continuous
      (fun Z : Matrix (Fin n) (Fin n) ℂ =>
        fun i j => (Z.reindex e e).toBlocks₁₁ i j)
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simpa [Matrix.reindex, Matrix.toBlocks₁₁] using
      continuous_matrix_entry (e.symm (Sum.inl i)) (e.symm (Sum.inl j))
  have hblock12 : Continuous
      (fun Z : Matrix (Fin n) (Fin n) ℂ =>
        (Z.reindex e e).toBlocks₁₂) := by
    change Continuous
      (fun Z : Matrix (Fin n) (Fin n) ℂ =>
        fun i j => (Z.reindex e e).toBlocks₁₂ i j)
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simpa [Matrix.reindex, Matrix.toBlocks₁₂] using
      continuous_matrix_entry (e.symm (Sum.inl i)) (e.symm (Sum.inr j))
  have hunit_open : IsOpen unitPatch := by
    have hdet : Continuous
        (fun Z : Matrix (Fin n) (Fin n) ℂ =>
          ((Z.reindex e e).toBlocks₁₁.det)) := by
      have hdet_matrix : Continuous (fun A : Matrix r r ℂ => A.det) := by
        fun_prop
      exact hdet_matrix.comp hblock11
    simpa [unitPatch, isUnit_iff_ne_zero] using
      (isOpen_ne_fun hdet continuous_const)
  have hApre_open : IsOpen
      ((fun Z : Matrix (Fin n) (Fin n) ℂ =>
        (Z.reindex e e).toBlocks₁₁) ⁻¹' Aset) := by
    exact hAset_open.preimage hblock11
  have hBpre_open : IsOpen
      ((fun Z : Matrix (Fin n) (Fin n) ℂ =>
        (Z.reindex e e).toBlocks₁₂) ⁻¹' Bset) := by
    exact hBset_open.preimage hblock12
  have hSpre_open : IsOpen
      (unitPatch ∩
        (fun Z : Matrix (Fin n) (Fin n) ℂ =>
          reindexedRectSchurComplement Z e e) ⁻¹' Sset) := by
    exact
      (continuousOn_reindexedPrincipalSchurComplement n e).isOpen_inter_preimage
        hunit_open hSset_open
  have hopen :
      IsOpen
        (N0 ∩
          ((fun Z : Matrix (Fin n) (Fin n) ℂ =>
            (Z.reindex e e).toBlocks₁₁) ⁻¹' Aset) ∩
          ((fun Z : Matrix (Fin n) (Fin n) ℂ =>
            (Z.reindex e e).toBlocks₁₂) ⁻¹' Bset) ∩
          (unitPatch ∩
            (fun Z : Matrix (Fin n) (Fin n) ℂ =>
              reindexedRectSchurComplement Z e e) ⁻¹' Sset)) :=
    (((hN0_open.inter hApre_open).inter hBpre_open).inter hSpre_open)
  convert hopen using 1
  ext Z
  simp [unitPatch, and_assoc, and_left_comm, and_comm]

section FrobeniusLocalBasis

open scoped Matrix.Norms.Frobenius

/-- Singular lower-rank points of the source complex Gram variety have
relatively open neighborhoods whose rank-`d+1` part is connected.  This is the
Schur-product branch of the local Hall-Wightman source-variety connectedness
theorem. -/
theorem sourceComplexGramVariety_local_rankExact_connected_basis_singular
    (d n : ℕ)
    (hD : d + 1 < n)
    {Z0 : Fin n → Fin n → ℂ}
    (hZ0 : Z0 ∈ sourceComplexGramVariety d n)
    (hZ0_sing :
      (Matrix.of fun i j : Fin n => Z0 i j).rank < d + 1)
    {N0 : Set (Fin n → Fin n → ℂ)}
    (hN0_open : IsOpen N0)
    (hZ0N0 : Z0 ∈ N0) :
    ∃ V : Set (Fin n → Fin n → ℂ),
      Z0 ∈ V ∧
      IsRelOpenInSourceComplexGramVariety d n V ∧
      V ⊆ N0 ∩ sourceComplexGramVariety d n ∧
      IsConnected (V ∩ sourceSymmetricRankExactStratum n (d + 1)) := by
  let D : ℕ := d + 1
  let M0 : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => Z0 i j
  let k : ℕ := M0.rank
  have hZ0_rank_le : Z0 ∈ sourceSymmetricMatrixSpace n ∧
      M0.rank ≤ d + 1 := by
    have h := hZ0
    rw [sourceComplexGramVariety_eq_rank_le] at h
    simpa [M0] using h
  have hZ0sym : Z0 ∈ sourceSymmetricMatrixSpace n := hZ0_rank_le.1
  have hkD : k ≤ D := by
    simpa [D, k] using hZ0_rank_le.2
  have hksing : k < D := by
    simpa [D, k, M0] using hZ0_sing
  rcases exists_sourcePrincipalMinor_ne_zero_of_sourceSymmetricRank
      (n := n) (r := k) (Z := Z0) hZ0sym (by simp [k, M0]) with
    ⟨I, hI, hminor⟩
  let q := selectedIndexComplement I
  let e : Fin n ≃ Fin k ⊕ q := selectedIndexSumEquiv I hI
  let A0 : Matrix (Fin k) (Fin k) ℂ := (M0.reindex e e).toBlocks₁₁
  let B0 : Matrix (Fin k) q ℂ := (M0.reindex e e).toBlocks₁₂
  let S0 : Matrix q q ℂ := reindexedRectSchurComplement M0 e e
  have hA0_unit : IsUnit A0.det := by
    simpa [A0, M0, e] using
      isUnit_selectedIndexSumEquiv_toBlocks₁₁_det
        (I := I) (J := I) hI hI hminor
  have hM0sym : M0ᵀ = M0 := by
    ext i j
    simpa [M0, Matrix.transpose] using hZ0sym j i
  have hA0_sym : A0ᵀ = A0 := by
    simpa [A0] using principalBlock_transpose_eq_of_symmetric n e hM0sym
  have hS0_rank_zero : S0.rank = 0 := by
    have hsplit :=
      rank_reindexed_principal_eq_card_add_rank_schur
        (Z := M0) (e := e) hA0_unit
    have hsplit' : k = k + S0.rank := by
      simpa [k, S0, A0] using hsplit
    omega
  have hS0_zero : S0 = 0 :=
    matrix_eq_zero_of_rank_eq_zero S0 hS0_rank_zero
  have hZ0_graph :
      sourcePrincipalSchurGraph n e A0 B0 0 = Z0 := by
    have hcoord :=
      sourcePrincipalSchurGraph_coordinates_eq_of_symmetric n e hM0sym
    funext i j
    have hij := congr_fun (congr_fun hcoord i) j
    simpa [M0, A0, B0, S0, hS0_zero] using hij
  rcases exists_sourcePrincipalSchurGraph_product_subset_open
      (n := n) (e := e) (A0 := A0) (B0 := B0) (S0 := 0)
      hA0_unit hN0_open (by simpa [hZ0_graph] using hZ0N0) with
    ⟨UA, UB, US, hUA_open, hA0_UA, hUB_open, hB0_UB, hUS_open, h0_US,
      hUA_unit, hgraph_U⟩
  rcases Metric.mem_nhds_iff.mp (hUA_open.mem_nhds hA0_UA) with
    ⟨εA, hεA, hAball_sub_UA⟩
  rcases Metric.mem_nhds_iff.mp (hUB_open.mem_nhds hB0_UB) with
    ⟨εB, hεB, hBball_sub_UB⟩
  have hcard_sum : n = k + Fintype.card q := by
    have hcard := Fintype.card_congr e
    simpa [q] using hcard
  have hDk_le_q : D - k ≤ Fintype.card q := by
    omega
  rcases matrixSymmetricRankExactCone_small_connected
      (q := q) (r := D - k) hDk_le_q hUS_open h0_US with
    ⟨C, h0C, hC_open, hC_sub_US, hC_rank_conn⟩
  let Aball : Set (Matrix (Fin k) (Fin k) ℂ) := Metric.ball A0 εA
  let Bball : Set (Matrix (Fin k) q ℂ) := Metric.ball B0 εB
  let Aexact : Set (Matrix (Fin k) (Fin k) ℂ) :=
    Aball ∩ {A | Aᵀ = A}
  have hAexact_conn : IsConnected Aexact := by
    simpa [Aexact, Aball] using
      isConnected_symmetric_matrix_ball hA0_sym hεA
  have hBball_conn : IsConnected Bball := by
    simpa [Bball] using isConnected_matrix_ball B0 hεB
  have hC_rank_conn' :
      IsConnected (C ∩ {S : Matrix q q ℂ |
        Sᵀ = S ∧ S.rank = D - Fintype.card (Fin k)}) := by
    simpa using hC_rank_conn
  have hgraph_rank_conn :
      IsConnected
        ((fun p : Matrix (Fin k) (Fin k) ℂ × Matrix (Fin k) q ℂ ×
            Matrix q q ℂ =>
            sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2) ''
          {p | p.1 ∈ Aexact ∧ p.2.1 ∈ Bball ∧
            p.2.2 ∈ C ∩ {S : Matrix q q ℂ |
              Sᵀ = S ∧ S.rank = D - k}}) := by
    simpa using
      isConnected_sourcePrincipalSchurGraph_rankExact_image
        n D e hAexact_conn hBball_conn hC_rank_conn'
        (by
          intro A hA
          exact hUA_unit A (hAball_sub_UA hA.1))
  let V0 : Set (Fin n → Fin n → ℂ) :=
    {Z |
      Z ∈ N0 ∧
      IsUnit
        ((((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₁).det) ∧
      (((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₁) ∈
        Aball ∧
      (((Matrix.of fun i j : Fin n => Z i j).reindex e e).toBlocks₁₂) ∈
        Bball ∧
      reindexedRectSchurComplement
        (Matrix.of fun i j : Fin n => Z i j) e e ∈ C}
  let V : Set (Fin n → Fin n → ℂ) :=
    V0 ∩ sourceComplexGramVariety d n
  have hV0_open : IsOpen V0 := by
    simpa [V0, Aball, Bball] using
      isOpen_sourcePrincipalSchurCoordinatePatch
        (n := n) (e := e) (N0 := N0)
        hN0_open Metric.isOpen_ball Metric.isOpen_ball hC_open
  have hV_rel : IsRelOpenInSourceComplexGramVariety d n V := by
    exact ⟨V0, hV0_open, rfl⟩
  have hZ0V : Z0 ∈ V := by
    refine ⟨?_, hZ0⟩
    refine ⟨hZ0N0, ?_, ?_, ?_, ?_⟩
    · simpa [M0, A0] using hA0_unit
    · simpa [M0, A0, Aball] using
        (Metric.mem_ball_self (x := A0) hεA)
    · simpa [M0, B0, Bball] using
        (Metric.mem_ball_self (x := B0) hεB)
    · have hS0C : S0 ∈ C := by
        simpa [hS0_zero] using h0C
      simpa [M0, S0] using hS0C
  have hV_sub : V ⊆ N0 ∩ sourceComplexGramVariety d n := by
    intro Z hZ
    exact ⟨hZ.1.1, hZ.2⟩
  have hgraph_N0 :
      ((fun p : Matrix (Fin k) (Fin k) ℂ × Matrix (Fin k) q ℂ ×
          Matrix q q ℂ =>
          sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2) ''
        {p | p.1 ∈ Aball ∩ {A : Matrix (Fin k) (Fin k) ℂ | Aᵀ = A} ∧
          p.2.1 ∈ Bball ∧
          p.2.2 ∈ C ∩ {S : Matrix q q ℂ |
            Sᵀ = S ∧ S.rank = D - Fintype.card (Fin k)}}) ⊆ N0 := by
    rintro G ⟨p, hp, rfl⟩
    apply hgraph_U
    refine ⟨p, ?_, rfl⟩
    exact
      ⟨hAball_sub_UA hp.1.1,
        hBball_sub_UB hp.2.1,
        hC_sub_US hp.2.2.1⟩
  have hpatch_eq_D :
      V ∩ sourceSymmetricRankExactStratum n D =
        ((fun p : Matrix (Fin k) (Fin k) ℂ × Matrix (Fin k) q ℂ ×
            Matrix q q ℂ =>
            sourcePrincipalSchurGraph n e p.1 p.2.1 p.2.2) ''
          {p | p.1 ∈ Aexact ∧ p.2.1 ∈ Bball ∧
            p.2.2 ∈ C ∩ {S : Matrix q q ℂ |
              Sᵀ = S ∧ S.rank = D - k}}) := by
    have hrank_sub_var :
        sourceSymmetricRankExactStratum n D ⊆
          sourceComplexGramVariety d n := by
      simpa [D] using
        sourceSymmetricRankExactStratum_subset_sourceComplexGramVariety
          d n (d + 1) le_rfl
    have hV_inter :
        V ∩ sourceSymmetricRankExactStratum n D =
          V0 ∩ sourceSymmetricRankExactStratum n D := by
      ext Z
      constructor
      · intro hZ
        exact ⟨hZ.1.1, hZ.2⟩
      · intro hZ
        exact ⟨⟨hZ.1, hrank_sub_var hZ.2⟩, hZ.2⟩
    have hcoord :=
      sourcePrincipalSchurGraph_rankExact_image_eq_openCoordinatePatch
        (n := n) (D := D) (e := e) (N0 := N0)
        (Aset := Aball) (Bset := Bball) (Sset := C)
        (by
          intro A hA
          exact hUA_unit A (hAball_sub_UA hA))
        (by simpa [D] using hkD)
        (by simpa [Aexact] using hgraph_N0)
    rw [hV_inter]
    simpa [V0, Aball, Bball, Aexact] using hcoord
  have hV_rank_conn :
      IsConnected (V ∩ sourceSymmetricRankExactStratum n (d + 1)) := by
    simpa [D] using (by
      rw [hpatch_eq_D]
      exact hgraph_rank_conn)
  exact ⟨V, hZ0V, hV_rel, hV_sub, hV_rank_conn⟩

end FrobeniusLocalBasis

end BHW
