import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexChart
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexTangent
import OSReconstruction.SCV.IdentityTheorem

/-!
# Global source-variety identity support

This file starts the finite-dimensional scalar-product geometry needed for the
global Hall-Wightman identity principle on the source complex Gram variety.
The first checked step is the complex-linear reduction of the Minkowski
bilinear form to the ordinary complex symmetric dot form.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial Module
open scoped Matrix.Norms.Operator

namespace BHW

/-- Ordinary complex symmetric dot-product Gram map in `D` coordinates. -/
def sourceComplexDotGram
    (D n : ℕ)
    (z : Fin n → Fin D → ℂ) :
    Fin n → Fin n → ℂ :=
  fun i j => ∑ μ : Fin D, z i μ * z j μ

/-- Symmetric complex `n × n` matrices, represented in source Gram
coordinates. -/
def sourceSymmetricMatrixSpace
    (n : ℕ) :
    Set (Fin n → Fin n → ℂ) :=
  {Z | ∀ i j, Z i j = Z j i}

/-- Coordinate minor of a source Gram matrix. -/
def sourceMatrixMinor
    (n k : ℕ)
    (I J : Fin k → Fin n)
    (Z : Fin n → Fin n → ℂ) : ℂ :=
  Matrix.det (fun a b : Fin k => Z (I a) (J b))

/-- Coordinate minors are continuous functions of the source Gram matrix
coordinates. -/
theorem continuous_sourceMatrixMinor
    (n k : ℕ)
    (I J : Fin k → Fin n) :
    Continuous (sourceMatrixMinor n k I J) := by
  change Continuous fun Z : Fin n → Fin n → ℂ =>
    Matrix.det (fun a b : Fin k => Z (I a) (J b))
  exact
    (continuous_matrix fun a b =>
      continuous_apply_apply (I a) (J b)).matrix_det

/-- Symmetric determinantal rank-`≤ D` variety in source Gram coordinates.
When `D ≥ n`, this is the whole symmetric matrix space. -/
def sourceSymmetricRankLEVariety
    (n D : ℕ) :
    Set (Fin n → Fin n → ℂ) :=
  if D < n then
    {Z | Z ∈ sourceSymmetricMatrixSpace n ∧
      ∀ I J : Fin (D + 1) → Fin n,
        sourceMatrixMinor n (D + 1) I J Z = 0}
  else
    sourceSymmetricMatrixSpace n

/-- Symmetric source matrices form a closed coordinate subspace. -/
theorem isClosed_sourceSymmetricMatrixSpace
    (n : ℕ) :
    IsClosed (sourceSymmetricMatrixSpace n) := by
  rw [sourceSymmetricMatrixSpace]
  simpa [Set.setOf_forall] using
    (isClosed_iInter fun i =>
      isClosed_iInter fun j =>
        isClosed_eq
          (show Continuous (fun Z : Fin n → Fin n → ℂ => Z i j) from
            continuous_apply_apply i j)
          (show Continuous (fun Z : Fin n → Fin n → ℂ => Z j i) from
            continuous_apply_apply j i))

/-- The symmetric determinantal rank-`≤ D` source variety is closed. -/
theorem isClosed_sourceSymmetricRankLEVariety
    (n D : ℕ) :
    IsClosed (sourceSymmetricRankLEVariety n D) := by
  unfold sourceSymmetricRankLEVariety
  by_cases hD : D < n
  · rw [if_pos hD]
    have hminor :
        IsClosed {Z : Fin n → Fin n → ℂ |
          ∀ I J : Fin (D + 1) → Fin n,
            sourceMatrixMinor n (D + 1) I J Z = 0} := by
      simpa [Set.setOf_forall] using
        (isClosed_iInter fun I =>
          isClosed_iInter fun J =>
            isClosed_eq
              (continuous_sourceMatrixMinor n (D + 1) I J)
              continuous_const)
    exact (isClosed_sourceSymmetricMatrixSpace n).inter hminor
  · rw [if_neg hD]
    exact isClosed_sourceSymmetricMatrixSpace n

/-- Ordinary complex dot-Gram matrices are symmetric. -/
theorem sourceComplexDotGram_symm
    (D n : ℕ)
    (z : Fin n → Fin D → ℂ)
    (i j : Fin n) :
    sourceComplexDotGram D n z i j =
      sourceComplexDotGram D n z j i := by
  simp [sourceComplexDotGram, mul_comm]

/-- The ordinary complex dot-Gram range lies in the symmetric matrix space. -/
theorem sourceComplexDotGram_mem_sourceSymmetricMatrixSpace
    (D n : ℕ)
    (z : Fin n → Fin D → ℂ) :
    sourceComplexDotGram D n z ∈ sourceSymmetricMatrixSpace n := by
  intro i j
  exact sourceComplexDotGram_symm D n z i j

/-- Every `(D + 1) × (D + 1)` minor of a `D`-dimensional complex dot-Gram
matrix vanishes. -/
theorem sourceComplexDotGram_minor_eq_zero
    (D n : ℕ)
    (z : Fin n → Fin D → ℂ)
    (I J : Fin (D + 1) → Fin n) :
    sourceMatrixMinor n (D + 1) I J (sourceComplexDotGram D n z) = 0 := by
  let M : Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ :=
    fun a b => sourceComplexDotGram D n z (I a) (J b)
  rw [sourceMatrixMinor]
  change Matrix.det M = 0
  apply Matrix.det_eq_zero_of_not_linearIndependent_rows
  intro hlin
  let rowVec : Fin D → (Fin (D + 1) → ℂ) :=
    fun μ b => z (J b) μ
  have hrow_mem :
      ∀ a : Fin (D + 1),
        M a ∈ Submodule.span ℂ (Set.range rowVec) := by
    intro a
    have hrow_eq :
        M a = ∑ μ : Fin D, z (I a) μ • rowVec μ := by
      ext b
      simp [M, rowVec, sourceComplexDotGram, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
    rw [hrow_eq]
    exact Submodule.sum_mem _ fun μ _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨μ, rfl⟩)
  have hspan_le :
      Submodule.span ℂ (Set.range fun a : Fin (D + 1) => M a) ≤
        Submodule.span ℂ (Set.range rowVec) := by
    exact Submodule.span_le.mpr (by
      rintro v ⟨a, rfl⟩
      exact hrow_mem a)
  have hcard_le :
      Fintype.card (Fin (D + 1)) ≤
        Module.finrank ℂ
          (Submodule.span ℂ (Set.range fun a : Fin (D + 1) => M a)) := by
    exact linearIndependent_iff_card_le_finrank_span.mp hlin
  have hfin_le :
      Module.finrank ℂ
          (Submodule.span ℂ (Set.range fun a : Fin (D + 1) => M a)) ≤
        D := by
    calc
      Module.finrank ℂ
          (Submodule.span ℂ (Set.range fun a : Fin (D + 1) => M a))
          ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range rowVec)) :=
            Submodule.finrank_mono hspan_le
      _ ≤ Fintype.card (Fin D) := by
            simpa using finrank_range_le_card (R := ℂ) rowVec
      _ = D := Fintype.card_fin D
  have hD_succ : D + 1 ≤ D := by
    simpa using hcard_le.trans hfin_le
  exact Nat.not_succ_le_self D hD_succ

/-- The ordinary complex dot-Gram range lies in the symmetric rank-`≤ D`
determinantal variety. -/
theorem sourceComplexDotGram_mem_sourceSymmetricRankLEVariety
    (D n : ℕ)
    (z : Fin n → Fin D → ℂ) :
    sourceComplexDotGram D n z ∈ sourceSymmetricRankLEVariety n D := by
  unfold sourceSymmetricRankLEVariety
  by_cases hD : D < n
  · simp [hD, sourceComplexDotGram_mem_sourceSymmetricMatrixSpace,
      sourceComplexDotGram_minor_eq_zero]
  · simp [hD, sourceComplexDotGram_mem_sourceSymmetricMatrixSpace]

/-- Coordinate scale turning the mostly-plus complex Minkowski form into the
ordinary complex dot form.  The time coordinate is multiplied by `I`; spatial
coordinates are unchanged. -/
def complexMinkowskiDotScale
    (d : ℕ) (μ : Fin (d + 1)) : ℂ :=
  if μ = 0 then Complex.I else 1

/-- Inverse coordinate scale for `complexMinkowskiDotScale`. -/
def complexMinkowskiDotInvScale
    (d : ℕ) (μ : Fin (d + 1)) : ℂ :=
  if μ = 0 then -Complex.I else 1

theorem complexMinkowskiDotInvScale_mul_scale
    (d : ℕ) (μ : Fin (d + 1)) :
    complexMinkowskiDotInvScale d μ * complexMinkowskiDotScale d μ = 1 := by
  by_cases hμ : μ = 0 <;>
    simp [complexMinkowskiDotScale, complexMinkowskiDotInvScale, hμ]

theorem complexMinkowskiDotScale_sq
    (d : ℕ) (μ : Fin (d + 1)) :
    complexMinkowskiDotScale d μ * complexMinkowskiDotScale d μ =
      (MinkowskiSpace.metricSignature d μ : ℂ) := by
  by_cases hμ : μ = 0 <;>
    simp [complexMinkowskiDotScale, MinkowskiSpace.metricSignature, hμ]

/-- Complex-linear coordinate equivalence reducing the source Minkowski
bilinear form to the ordinary complex symmetric dot form. -/
def complexMinkowskiToDotLinearEquiv
    (d : ℕ) :
    (Fin (d + 1) → ℂ) ≃ₗ[ℂ] (Fin (d + 1) → ℂ) where
  toFun := fun u μ => complexMinkowskiDotScale d μ * u μ
  invFun := fun u μ => complexMinkowskiDotInvScale d μ * u μ
  map_add' := by
    intro u v
    ext μ
    simp [Pi.add_apply]
    ring
  map_smul' := by
    intro c u
    ext μ
    simp [Pi.smul_apply, smul_eq_mul]
    ring
  left_inv := by
    intro u
    ext μ
    simp
    calc
      complexMinkowskiDotInvScale d μ *
          (complexMinkowskiDotScale d μ * u μ)
          = (complexMinkowskiDotInvScale d μ *
              complexMinkowskiDotScale d μ) * u μ := by
            ring
      _ = u μ := by
            rw [complexMinkowskiDotInvScale_mul_scale]
            ring
  right_inv := by
    intro u
    ext μ
    simp
    calc
      complexMinkowskiDotScale d μ *
          (complexMinkowskiDotInvScale d μ * u μ)
          = (complexMinkowskiDotInvScale d μ *
              complexMinkowskiDotScale d μ) * u μ := by
            ring
      _ = u μ := by
            rw [complexMinkowskiDotInvScale_mul_scale]
            ring

@[simp]
theorem complexMinkowskiToDotLinearEquiv_apply
    (d : ℕ) (u : Fin (d + 1) → ℂ) (μ : Fin (d + 1)) :
    complexMinkowskiToDotLinearEquiv d u μ =
      complexMinkowskiDotScale d μ * u μ :=
  rfl

/-- The complex Minkowski pairing becomes the ordinary complex dot pairing after
the checked coordinate scale. -/
theorem sourceComplexMinkowskiInner_eq_dot_after_equiv
    (d : ℕ) (u v : Fin (d + 1) → ℂ) :
    sourceComplexMinkowskiInner d u v =
      ∑ μ : Fin (d + 1),
        complexMinkowskiToDotLinearEquiv d u μ *
          complexMinkowskiToDotLinearEquiv d v μ := by
  unfold sourceComplexMinkowskiInner complexMinkowskiToDotLinearEquiv
  apply Finset.sum_congr rfl
  intro μ _
  simp
  rw [← complexMinkowskiDotScale_sq d μ]
  ring

/-- The source complex Gram map is the ordinary symmetric dot Gram map after
the same coordinate scale on each source vector. -/
theorem sourceMinkowskiGram_eq_dotGram_after_equiv
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceMinkowskiGram d n z =
      sourceComplexDotGram (d + 1) n
        (fun i => complexMinkowskiToDotLinearEquiv d (z i)) := by
  ext i j
  simp [sourceComplexDotGram]
  exact sourceComplexMinkowskiInner_eq_dot_after_equiv d (z i) (z j)

/-- The source complex Gram variety is exactly the ordinary complex symmetric
dot-Gram range in dimension `d + 1`. -/
theorem sourceComplexGramVariety_eq_dotGram_range
    (d n : ℕ) :
    sourceComplexGramVariety d n =
      Set.range (sourceComplexDotGram (d + 1) n) := by
  ext Z
  constructor
  · rintro ⟨z, rfl⟩
    exact
      ⟨fun i => complexMinkowskiToDotLinearEquiv d (z i),
        (sourceMinkowskiGram_eq_dotGram_after_equiv d n z).symm⟩
  · rintro ⟨a, rfl⟩
    refine
      ⟨fun i => (complexMinkowskiToDotLinearEquiv d).symm (a i), ?_⟩
    rw [sourceMinkowskiGram_eq_dotGram_after_equiv]
    have hrow :
        (fun i =>
          complexMinkowskiToDotLinearEquiv d
            ((complexMinkowskiToDotLinearEquiv d).symm (a i))) = a := by
      ext i μ
      exact
        congrFun
          ((complexMinkowskiToDotLinearEquiv d).apply_symm_apply (a i)) μ
    rw [hrow]

/-- The source complex Gram variety lies in the symmetric matrix space. -/
theorem sourceComplexGramVariety_subset_sourceSymmetricMatrixSpace
    (d n : ℕ) :
    sourceComplexGramVariety d n ⊆ sourceSymmetricMatrixSpace n := by
  intro Z hZ
  rw [sourceComplexGramVariety_eq_dotGram_range] at hZ
  rcases hZ with ⟨z, rfl⟩
  exact sourceComplexDotGram_mem_sourceSymmetricMatrixSpace (d + 1) n z

/-- Forward algebraic inclusion: every source complex Gram matrix satisfies the
determinantal equations for symmetric rank `≤ d + 1`. -/
theorem sourceComplexGramVariety_subset_sourceSymmetricRankLEVariety
    (d n : ℕ) :
    sourceComplexGramVariety d n ⊆
      sourceSymmetricRankLEVariety n (d + 1) := by
  intro Z hZ
  rw [sourceComplexGramVariety_eq_dotGram_range] at hZ
  rcases hZ with ⟨z, rfl⟩
  exact sourceComplexDotGram_mem_sourceSymmetricRankLEVariety (d + 1) n z

/-- A chosen complex square root, used for the diagonal stage of the symmetric
factorization theorem. -/
noncomputable def complexSquareRootChoice (c : ℂ) : ℂ :=
  (IsAlgClosed.exists_eq_mul_self c).choose

theorem complexSquareRootChoice_mul_self (c : ℂ) :
    complexSquareRootChoice c * complexSquareRootChoice c = c := by
  exact (IsAlgClosed.exists_eq_mul_self c).choose_spec.symm

/-- Every complex diagonal matrix is an ordinary complex dot-Gram matrix in the
same dimension. -/
theorem sourceComplexDiagonal_factorization_self
    (n : ℕ) (w : Fin n → ℂ) :
    ∃ A : Fin n → Fin n → ℂ,
      (fun i j => if i = j then w i else 0) =
        sourceComplexDotGram n n A := by
  let A : Fin n → Fin n → ℂ :=
    fun i a => if a = i then complexSquareRootChoice (w i) else 0
  refine ⟨A, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst j
    simp [sourceComplexDotGram, A, complexSquareRootChoice_mul_self]
  · have hzero : ∀ a : Fin n, A i a * A j a = 0 := by
      intro a
      by_cases haj : a = j
      · have hai : a ≠ i := by
          intro hai
          exact hij (hai ▸ haj)
        have hAi : A i a = 0 := by
          simp [A, hai]
        rw [hAi, zero_mul]
      · have hAj : A j a = 0 := by
          simp [A, haj]
        rw [hAj, mul_zero]
    simp [sourceComplexDotGram, hij, hzero]

/-- Expansion of a bilinear form in an orthogonal basis. -/
theorem bilinform_orthogonal_basis_expansion
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm K V)
    (b : Basis ι K V)
    (hortho : B.IsOrthoᵢ b)
    (x y : V) :
    B x y =
      ∑ a : ι, b.repr x a * b.repr y a * B (b a) (b a) := by
  have hcoord :=
    Matrix.toBilin_apply (b := b) (LinearMap.BilinForm.toMatrix b B) x y
  rw [Matrix.toBilin_toMatrix] at hcoord
  rw [hcoord]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · simp [LinearMap.BilinForm.toMatrix_apply]
    ring_nf
  · intro j hj hji
    have ho : B (b i) (b j) = 0 := hortho (Ne.symm hji)
    simp [LinearMap.BilinForm.toMatrix_apply, ho]
  · intro hi_not
    exact (hi_not hi).elim

/-- A symmetric source matrix gives a symmetric bilinear form under
`Matrix.toBilin'`. -/
theorem sourceMatrix_toBilin_isSymm
    (n : ℕ)
    {Z : Fin n → Fin n → ℂ}
    (hZsym : Z ∈ sourceSymmetricMatrixSpace n) :
    (Matrix.toBilin' (Matrix.of fun i j : Fin n => Z i j)).IsSymm := by
  rw [LinearMap.BilinForm.isSymm_iff_basis (Pi.basisFun ℂ (Fin n))]
  intro i j
  simp [hZsym i j]

/-- Orthogonal-basis coordinate expansion of a complex symmetric source
matrix. -/
theorem sourceSymmetricMatrix_exists_orthogonal_coordinate_expansion
    (n : ℕ)
    {Z : Fin n → Fin n → ℂ}
    (hZsym : Z ∈ sourceSymmetricMatrixSpace n) :
    ∃ b : Basis (Fin (Module.finrank ℂ (Fin n → ℂ))) ℂ (Fin n → ℂ),
      (Matrix.toBilin' (Matrix.of fun i j : Fin n => Z i j)).IsOrthoᵢ b ∧
        ∀ i j : Fin n,
          Z i j =
            ∑ a : Fin (Module.finrank ℂ (Fin n → ℂ)),
              b.repr (Pi.single i 1) a * b.repr (Pi.single j 1) a *
                (Matrix.toBilin' (Matrix.of fun i j : Fin n => Z i j))
                  (b a) (b a) := by
  let M : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j : Fin n => Z i j
  let B : LinearMap.BilinForm ℂ (Fin n → ℂ) := Matrix.toBilin' M
  have hsymB : LinearMap.IsSymm B :=
    LinearMap.BilinForm.isSymm_iff.1 (sourceMatrix_toBilin_isSymm n hZsym)
  rcases LinearMap.BilinForm.exists_orthogonal_basis (B := B) hsymB with
    ⟨b, hb⟩
  refine ⟨b, hb, ?_⟩
  intro i j
  have h :=
    bilinform_orthogonal_basis_expansion B b hb (Pi.single i 1) (Pi.single j 1)
  change Z i j =
    ∑ a : Fin (Module.finrank ℂ (Fin n → ℂ)),
      b.repr (Pi.single i 1) a * b.repr (Pi.single j 1) a *
        B (b a) (b a)
  rw [← h]
  change Z i j = Matrix.toBilin' M (Pi.single i 1) (Pi.single j 1)
  rw [Matrix.toBilin'_single]
  rfl

/-- Every complex symmetric source matrix is an ordinary complex dot-Gram
matrix in `Module.finrank ℂ (Fin n → ℂ)` coordinates.  The rank-bounded
factorization still has to compress this representation to the rank. -/
theorem sourceSymmetricMatrix_factorization_finrank
    (n : ℕ)
    {Z : Fin n → Fin n → ℂ}
    (hZsym : Z ∈ sourceSymmetricMatrixSpace n) :
    ∃ A : Fin n → Fin (Module.finrank ℂ (Fin n → ℂ)) → ℂ,
      Z = sourceComplexDotGram (Module.finrank ℂ (Fin n → ℂ)) n A := by
  let B : LinearMap.BilinForm ℂ (Fin n → ℂ) :=
    Matrix.toBilin' (Matrix.of fun i j : Fin n => Z i j)
  rcases sourceSymmetricMatrix_exists_orthogonal_coordinate_expansion n hZsym with
    ⟨b, hb, hentry⟩
  let A : Fin n → Fin (Module.finrank ℂ (Fin n → ℂ)) → ℂ :=
    fun i a => complexSquareRootChoice (B (b a) (b a)) *
      b.repr (Pi.single i 1) a
  refine ⟨A, ?_⟩
  ext i j
  rw [hentry i j]
  simp [sourceComplexDotGram, A]
  apply Finset.sum_congr rfl
  intro a ha
  let lam : ℂ := B (b a) (b a)
  change
    b.repr (Pi.single i 1) a * b.repr (Pi.single j 1) a * lam =
      complexSquareRootChoice lam * b.repr (Pi.single i 1) a *
        (complexSquareRootChoice lam * b.repr (Pi.single j 1) a)
  calc
    b.repr (Pi.single i 1) a * b.repr (Pi.single j 1) a * lam
        = b.repr (Pi.single i 1) a * b.repr (Pi.single j 1) a *
            (complexSquareRootChoice lam * complexSquareRootChoice lam) := by
          rw [complexSquareRootChoice_mul_self]
    _ = complexSquareRootChoice lam * b.repr (Pi.single i 1) a *
          (complexSquareRootChoice lam * b.repr (Pi.single j 1) a) := by
          ring

/-- Every complex symmetric source matrix is an ordinary complex dot-Gram
matrix in `n` coordinates. -/
theorem sourceSymmetricMatrix_factorization_self
    (n : ℕ)
    {Z : Fin n → Fin n → ℂ}
    (hZsym : Z ∈ sourceSymmetricMatrixSpace n) :
    ∃ A : Fin n → Fin n → ℂ,
      Z = sourceComplexDotGram n n A := by
  have hfin : Module.finrank ℂ (Fin n → ℂ) = n := by
    simp
  have h := sourceSymmetricMatrix_factorization_finrank n hZsym
  rw [hfin] at h
  exact h

/-- Reindex a product sum along an embedding, using zero extension away from
the image. -/
theorem sum_mul_indicator_embedding
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (e : α ↪ β) (U V : α → ℂ) :
    (∑ b : β,
      (if h : b ∈ Set.range e then U (Classical.choose h) else 0) *
      (if h : b ∈ Set.range e then V (Classical.choose h) else 0)) =
      ∑ a : α, U a * V a := by
  let F : β → ℂ := fun b =>
    (if h : b ∈ Set.range e then U (Classical.choose h) else 0) *
      (if h : b ∈ Set.range e then V (Classical.choose h) else 0)
  have hfilter :
      (Finset.univ.filter (fun b : β => b ∈ Set.range e)) =
        Finset.univ.map e := by
    ext b
    simp [Set.mem_range]
  calc
    (∑ b : β,
      (if h : b ∈ Set.range e then U (Classical.choose h) else 0) *
        (if h : b ∈ Set.range e then V (Classical.choose h) else 0))
        = ∑ b : β, F b := rfl
    _ = ∑ b ∈ Finset.univ.filter (fun b : β => b ∈ Set.range e), F b := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro b hb
          by_cases hbmem : b ∈ Set.range e
          · have hbmem' : ∃ a : α, e a = b := by
              simpa [Set.mem_range] using hbmem
            simp [F, Set.mem_range, hbmem']
          · have hbmem' : ¬ ∃ a : α, e a = b := by
              simpa [Set.mem_range] using hbmem
            simp [F, Set.mem_range, hbmem']
    _ = ∑ b ∈ Finset.univ.map e, F b := by
          rw [hfilter]
    _ = ∑ a : α, U a * V a := by
          rw [Finset.sum_map]
          apply Finset.sum_congr rfl
          intro a ha
          simp [F, Set.mem_range]

/-- Rank-bounded complex symmetric factorization: every complex symmetric
`n × n` source matrix of matrix rank at most `D` is a dot-Gram matrix in
`D` coordinates. -/
theorem complex_symmetric_matrix_factorization_of_rank_le
    (n D : ℕ)
    {Z : Fin n → Fin n → ℂ}
    (hZsym : Z ∈ sourceSymmetricMatrixSpace n)
    (hrank : (Matrix.of fun i j : Fin n => Z i j).rank ≤ D) :
    ∃ A : Fin n → Fin D → ℂ,
      Z = sourceComplexDotGram D n A := by
  let M : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j : Fin n => Z i j
  let B : LinearMap.BilinForm ℂ (Fin n → ℂ) := Matrix.toBilin' M
  have hsymB : LinearMap.IsSymm B :=
    LinearMap.BilinForm.isSymm_iff.1 (sourceMatrix_toBilin_isSymm n hZsym)
  rcases LinearMap.BilinForm.exists_orthogonal_basis (B := B) hsymB with
    ⟨b0, hb0⟩
  have hfin : Module.finrank ℂ (Fin n → ℂ) = n := by
    simp
  let eFin : Fin n ≃ Fin (Module.finrank ℂ (Fin n → ℂ)) := finCongr hfin.symm
  let b : Basis (Fin n) ℂ (Fin n → ℂ) := b0.reindex eFin.symm
  have hb : B.IsOrthoᵢ b := by
    intro i j hij
    have hne : eFin i ≠ eFin j :=
      fun h => hij (eFin.injective h)
    simpa [b] using hb0 hne
  let lam : Fin n → ℂ := fun a => B (b a) (b a)
  let c : Basis (Fin n) ℂ (Fin n → ℂ) := Pi.basisFun ℂ (Fin n)
  have hdiag : LinearMap.BilinForm.toMatrix b B = Matrix.diagonal lam := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [LinearMap.BilinForm.toMatrix_apply, Matrix.diagonal, lam]
    · have ho : B (b i) (b j) = 0 := hb hij
      simp [LinearMap.BilinForm.toMatrix_apply, Matrix.diagonal, lam, hij, ho]
  have hstd : LinearMap.BilinForm.toMatrix c B = M := by
    change
      LinearMap.BilinForm.toMatrix (Pi.basisFun ℂ (Fin n))
        (Matrix.toBilin' M) = M
    rw [LinearMap.BilinForm.toMatrix_basisFun,
      LinearMap.BilinForm.toMatrix'_toBilin']
  let P : Matrix (Fin n) (Fin n) ℂ := b.toMatrix c
  have hcongr : Pᵀ * Matrix.diagonal lam * P = M := by
    change (b.toMatrix c)ᵀ * Matrix.diagonal lam * b.toMatrix c = M
    rw [← hstd, ← hdiag]
    exact LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (b := b) (c := c) B
  have hPunit : IsUnit P.det := by
    letI := Module.Basis.invertibleToMatrix b c
    exact Matrix.isUnit_det_of_invertible P
  have hPtunit : IsUnit Pᵀ.det := Matrix.isUnit_det_transpose P hPunit
  have hrankeq : M.rank = (Matrix.diagonal lam).rank := by
    calc
      M.rank = (Pᵀ * Matrix.diagonal lam * P).rank := by
        rw [hcongr]
      _ = (Pᵀ * Matrix.diagonal lam).rank := by
        rw [Matrix.rank_mul_eq_left_of_isUnit_det P
          (Pᵀ * Matrix.diagonal lam) hPunit]
      _ = (Matrix.diagonal lam).rank := by
        rw [Matrix.rank_mul_eq_right_of_isUnit_det Pᵀ
          (Matrix.diagonal lam) hPtunit]
  have hcard : Fintype.card {a : Fin n // lam a ≠ 0} ≤ D := by
    rw [← Matrix.rank_diagonal lam, ← hrankeq]
    exact hrank
  let nz := {a : Fin n // lam a ≠ 0}
  have hnzEmb : Nonempty (nz ↪ Fin D) := by
    rw [Function.Embedding.nonempty_iff_card_le, Fintype.card_fin]
    exact hcard
  let emb : nz ↪ Fin D := Classical.choice hnzEmb
  let s : Fin n → ℂ := fun a => complexSquareRootChoice (lam a)
  let A : Fin n → Fin D → ℂ := fun i β =>
    if hβ : β ∈ Set.range emb then
      s (Classical.choose hβ).val *
        b.repr (Pi.single i 1) (Classical.choose hβ).val
    else 0
  refine ⟨A, ?_⟩
  ext i j
  have hentry : Z i j =
      ∑ a : Fin n,
        b.repr (Pi.single i 1) a * b.repr (Pi.single j 1) a * lam a := by
    have h :=
      bilinform_orthogonal_basis_expansion B b hb (Pi.single i 1) (Pi.single j 1)
    change Z i j =
      ∑ a : Fin n,
        b.repr (Pi.single i 1) a * b.repr (Pi.single j 1) a *
          B (b a) (b a)
    rw [← h]
    change Z i j = Matrix.toBilin' M (Pi.single i 1) (Pi.single j 1)
    rw [Matrix.toBilin'_single]
    rfl
  rw [hentry]
  rw [sourceComplexDotGram]
  change
    (∑ a : Fin n,
      b.repr (Pi.single i 1) a * b.repr (Pi.single j 1) a * lam a) =
        ∑ β : Fin D, A i β * A j β
  have hdrop :
      (∑ a : Fin n,
        b.repr (Pi.single i 1) a * b.repr (Pi.single j 1) a * lam a) =
        ∑ a : nz,
          b.repr (Pi.single i 1) a.val *
            b.repr (Pi.single j 1) a.val * lam a.val := by
    let F : Fin n → ℂ := fun a =>
      b.repr (Pi.single i 1) a * b.repr (Pi.single j 1) a * lam a
    calc
      (∑ a : Fin n,
        b.repr (Pi.single i 1) a * b.repr (Pi.single j 1) a * lam a)
          = ∑ a : Fin n, if lam a ≠ 0 then F a else 0 := by
            apply Finset.sum_congr rfl
            intro a ha
            by_cases hla : lam a ≠ 0
            · simp [F, hla]
            · have hzero : lam a = 0 := not_ne_iff.mp hla
              simp [F, hzero]
      _ = ∑ a ∈ Finset.univ.filter (fun a : Fin n => lam a ≠ 0), F a := by
            rw [Finset.sum_filter]
      _ = ∑ a : nz, F a.val := by
            simpa using (Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
              (p := fun a : Fin n => lam a ≠ 0) (f := F)).symm
      _ = ∑ a : nz,
            b.repr (Pi.single i 1) a.val *
              b.repr (Pi.single j 1) a.val * lam a.val := rfl
  rw [hdrop]
  let U : nz → ℂ := fun a => s a.val * b.repr (Pi.single i 1) a.val
  let V : nz → ℂ := fun a => s a.val * b.repr (Pi.single j 1) a.val
  have hsquares :
      (∑ a : nz,
        b.repr (Pi.single i 1) a.val *
          b.repr (Pi.single j 1) a.val * lam a.val) =
        ∑ a : nz, U a * V a := by
    apply Finset.sum_congr rfl
    intro a ha
    simp [U, V, s]
    calc
      b.repr (Pi.single i 1) a.val *
          b.repr (Pi.single j 1) a.val * lam a.val
          = b.repr (Pi.single i 1) a.val *
              b.repr (Pi.single j 1) a.val *
              (complexSquareRootChoice (lam a.val) *
                complexSquareRootChoice (lam a.val)) := by
            rw [complexSquareRootChoice_mul_self]
      _ = complexSquareRootChoice (lam a.val) *
            b.repr (Pi.single i 1) a.val *
            (complexSquareRootChoice (lam a.val) *
              b.repr (Pi.single j 1) a.val) := by
            ring
  rw [hsquares]
  have hsum := sum_mul_indicator_embedding emb U V
  rw [← hsum]

/-- Rank-defined reverse inclusion into the source complex Gram variety.  The
remaining determinantal-variety bridge is to derive the rank hypothesis from
vanishing `(D + 1) × (D + 1)` minors. -/
theorem sourceComplexGramVariety_mem_of_symmetric_rank_le
    (d n : ℕ)
    {Z : Fin n → Fin n → ℂ}
    (hZsym : Z ∈ sourceSymmetricMatrixSpace n)
    (hrank : (Matrix.of fun i j : Fin n => Z i j).rank ≤ d + 1) :
    Z ∈ sourceComplexGramVariety d n := by
  rcases complex_symmetric_matrix_factorization_of_rank_le n (d + 1)
      hZsym hrank with
    ⟨A, hA⟩
  rw [sourceComplexGramVariety_eq_dotGram_range]
  exact ⟨A, hA.symm⟩

/-- If a matrix has rank at least `k`, some `k` rows are linearly
independent. -/
theorem exists_linearIndependent_rows_of_rank_ge
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) {k : ℕ}
    (hk : k ≤ A.rank) :
    ∃ I : Fin k → m,
      LinearIndependent ℂ (fun a : Fin k => A.row (I a)) := by
  rcases exists_linearIndependent' ℂ A.row with
    ⟨κ, a, ha_inj, hspan, hli⟩
  haveI : Finite κ := Finite.of_injective a ha_inj
  letI : Fintype κ := Fintype.ofFinite κ
  have hcard_rank : Fintype.card κ = A.rank := by
    have hcard_span :
        Fintype.card κ =
          Module.finrank ℂ (Submodule.span ℂ (Set.range (A.row ∘ a))) := by
      simpa [Set.finrank] using
        (linearIndependent_iff_card_eq_finrank_span.mp hli)
    calc
      Fintype.card κ
          = Module.finrank ℂ (Submodule.span ℂ (Set.range (A.row ∘ a))) :=
            hcard_span
      _ = Module.finrank ℂ (Submodule.span ℂ (Set.range A.row)) := by
            rw [hspan]
      _ = A.rank := by
            rw [A.rank_eq_finrank_span_row]
  have hkcard : Fintype.card (Fin k) ≤ Fintype.card κ := by
    simpa [hcard_rank] using hk
  have hEmb : Nonempty (Fin k ↪ κ) := by
    rw [Function.Embedding.nonempty_iff_card_le]
    exact hkcard
  let e : Fin k ↪ κ := Classical.choice hEmb
  refine ⟨fun i => a (e i), ?_⟩
  simpa [Function.comp_def] using hli.comp (fun i : Fin k => e i) e.injective

/-- If a matrix has rank at least `k`, it has a nonzero `k × k` minor. -/
theorem exists_nondegenerate_square_submatrix_of_rank_ge
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) {k : ℕ}
    (hk : k ≤ A.rank) :
    ∃ I : Fin k → m, ∃ J : Fin k → n,
      (Matrix.det (fun a b : Fin k => A (I a) (J b))) ≠ 0 := by
  rcases exists_linearIndependent_rows_of_rank_ge A hk with
    ⟨I, hIlin⟩
  let R : Matrix (Fin k) n ℂ := fun a j => A (I a) j
  have hRrank : R.rank = k := by
    have hrows : LinearIndependent ℂ R.row := by
      simpa [R, Matrix.row] using hIlin
    simpa using hrows.rank_matrix (M := R)
  have hkT : k ≤ Rᵀ.rank := by
    rw [Matrix.rank_transpose, hRrank]
  rcases exists_linearIndependent_rows_of_rank_ge Rᵀ hkT with
    ⟨J, hJlin⟩
  let S : Matrix (Fin k) (Fin k) ℂ := fun a b => A (I a) (J b)
  have hcols : LinearIndependent ℂ S.col := by
    simpa [S, R, Matrix.row, Matrix.col] using hJlin
  have hunit : IsUnit S := Matrix.linearIndependent_cols_iff_isUnit.1 hcols
  have hdetunit : IsUnit S.det := Matrix.isUnit_iff_isUnit_det S |>.mp hunit
  refine ⟨I, J, ?_⟩
  simpa [S] using hdetunit.ne_zero

/-- Vanishing of all `(D + 1) × (D + 1)` coordinate minors forces matrix
rank at most `D`. -/
theorem sourceMatrix_rank_le_of_minors_eq_zero
    (n D : ℕ)
    {Z : Fin n → Fin n → ℂ}
    (hminors : ∀ I J : Fin (D + 1) → Fin n,
      sourceMatrixMinor n (D + 1) I J Z = 0) :
    (Matrix.of fun i j : Fin n => Z i j).rank ≤ D := by
  let M : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j : Fin n => Z i j
  by_contra hle
  have hlt : D < M.rank := Nat.lt_of_not_ge hle
  have hsucc : D + 1 ≤ M.rank := Nat.succ_le_of_lt hlt
  rcases exists_nondegenerate_square_submatrix_of_rank_ge M hsucc with
    ⟨I, J, hdet⟩
  have hzero := hminors I J
  rw [sourceMatrixMinor] at hzero
  exact hdet (by simpa [M] using hzero)

/-- A nonzero finite square submatrix minor forces the ambient matrix rank to
be at least the cardinality of the square index type. -/
theorem matrix_rank_ge_card_of_nondegenerate_square_submatrix
    {m n κ : Type*} [Fintype m] [Fintype n] [Fintype κ]
    [DecidableEq m] [DecidableEq n] [DecidableEq κ]
    (A : Matrix m n ℂ)
    {I : κ → m} {J : κ → n}
    (hdet : Matrix.det (fun a b : κ => A (I a) (J b)) ≠ 0) :
    Fintype.card κ ≤ A.rank := by
  let S : Matrix κ κ ℂ := fun a b => A (I a) (J b)
  let R : Matrix κ n ℂ := fun a j => A (I a) j
  have hSrank : S.rank = Fintype.card κ := by
    have hrows : LinearIndependent ℂ S.row :=
      Matrix.linearIndependent_rows_of_det_ne_zero (A := S) (by
        simpa [S] using hdet)
    simpa using hrows.rank_matrix (M := S)
  have hS_le_R : S.rank ≤ R.rank := by
    have hraw :
        ((Rᵀ).submatrix J (Equiv.refl κ)).rank ≤ Rᵀ.rank :=
      Matrix.rank_submatrix_le (A := Rᵀ) J (Equiv.refl κ)
    have hsub : (Rᵀ).submatrix J (Equiv.refl κ) = Sᵀ := by
      ext a b
      rfl
    rw [hsub] at hraw
    simpa [Matrix.rank_transpose] using hraw
  have hR_le_A : R.rank ≤ A.rank := by
    simpa [R, Matrix.submatrix] using
      Matrix.rank_submatrix_le (A := A) I (Equiv.refl n)
  calc
    Fintype.card κ = S.rank := hSrank.symm
    _ ≤ R.rank := hS_le_R
    _ ≤ A.rank := hR_le_A

/-- A nonzero square submatrix minor forces the ambient matrix rank to be at
least the minor size. -/
theorem matrix_rank_ge_of_nondegenerate_square_submatrix
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) {k : ℕ}
    {I : Fin k → m} {J : Fin k → n}
    (hdet : Matrix.det (fun a b : Fin k => A (I a) (J b)) ≠ 0) :
    k ≤ A.rank := by
  let S : Matrix (Fin k) (Fin k) ℂ := fun a b => A (I a) (J b)
  let R : Matrix (Fin k) n ℂ := fun a j => A (I a) j
  have hSrank : S.rank = k := by
    have hrows : LinearIndependent ℂ S.row :=
      Matrix.linearIndependent_rows_of_det_ne_zero (A := S) (by simpa [S] using hdet)
    simpa using hrows.rank_matrix (M := S)
  have hS_le_R : S.rank ≤ R.rank := by
    have hraw :
        ((Rᵀ).submatrix J (Equiv.refl (Fin k))).rank ≤ Rᵀ.rank :=
      Matrix.rank_submatrix_le (A := Rᵀ) J (Equiv.refl (Fin k))
    have hsub : (Rᵀ).submatrix J (Equiv.refl (Fin k)) = Sᵀ := by
      ext a b
      rfl
    rw [hsub] at hraw
    simpa [Matrix.rank_transpose] using hraw
  have hR_le_A : R.rank ≤ A.rank := by
    simpa [R, Matrix.submatrix] using
      Matrix.rank_submatrix_le (A := A) I (Equiv.refl n)
  calc
    k = S.rank := hSrank.symm
    _ ≤ R.rank := hS_le_R
    _ ≤ A.rank := hR_le_A

/-- Matrix rank at most `D` forces all `(D + 1) × (D + 1)` coordinate minors to
vanish. -/
theorem sourceMatrix_minors_eq_zero_of_rank_le
    (n D : ℕ)
    {Z : Fin n → Fin n → ℂ}
    (hrank : (Matrix.of fun i j : Fin n => Z i j).rank ≤ D) :
    ∀ I J : Fin (D + 1) → Fin n,
      sourceMatrixMinor n (D + 1) I J Z = 0 := by
  intro I J
  by_contra hne
  let M : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j : Fin n => Z i j
  have hge : D + 1 ≤ M.rank :=
    matrix_rank_ge_of_nondegenerate_square_submatrix
      (A := M) (I := I) (J := J) (by
        simpa [sourceMatrixMinor, M] using hne)
  have hbad : D + 1 ≤ D := hge.trans hrank
  exact Nat.not_succ_le_self D hbad

/-- Rank-defined form of the symmetric determinantal variety. -/
theorem sourceSymmetricRankLEVariety_eq_rank_le
    (n D : ℕ) :
    sourceSymmetricRankLEVariety n D =
      {Z | Z ∈ sourceSymmetricMatrixSpace n ∧
        (Matrix.of fun i j : Fin n => Z i j).rank ≤ D} := by
  ext Z
  unfold sourceSymmetricRankLEVariety
  by_cases hD : D < n
  · rw [if_pos hD]
    constructor
    · intro h
      exact ⟨h.1, sourceMatrix_rank_le_of_minors_eq_zero n D h.2⟩
    · intro h
      exact ⟨h.1, sourceMatrix_minors_eq_zero_of_rank_le n D h.2⟩
  · have hnle : n ≤ D := Nat.le_of_not_gt hD
    rw [if_neg hD]
    constructor
    · intro hsym
      exact ⟨hsym,
        (Matrix.rank_le_width
          (Matrix.of fun i j : Fin n => Z i j : Matrix (Fin n) (Fin n) ℂ)).trans hnle⟩
    · intro h
      exact h.1

/-- Rank-exact symmetric stratum in source Gram coordinates. -/
def sourceSymmetricRankExactStratum
    (n r : ℕ) :
    Set (Fin n → Fin n → ℂ) :=
  {Z | Z ∈ sourceSymmetricMatrixSpace n ∧
    (Matrix.of fun i j : Fin n => Z i j).rank = r}

/-- A rank-exact stratum with `r ≤ D` lies in the rank-`≤ D` symmetric
determinantal variety. -/
theorem sourceSymmetricRankExactStratum_subset_rankLE
    (n r D : ℕ) (hrD : r ≤ D) :
    sourceSymmetricRankExactStratum n r ⊆
      sourceSymmetricRankLEVariety n D := by
  intro Z hZ
  rw [sourceSymmetricRankLEVariety_eq_rank_le]
  exact ⟨hZ.1, hZ.2.le.trans hrD⟩

/-- For positive rank, the rank-exact stratum is the difference between the
rank-`≤ r` and rank-`≤ r - 1` symmetric determinantal varieties. -/
theorem sourceSymmetricRankExactStratum_eq_rankLE_diff
    (n r : ℕ) (hr : 0 < r) :
    sourceSymmetricRankExactStratum n r =
      sourceSymmetricRankLEVariety n r \
        sourceSymmetricRankLEVariety n (r - 1) := by
  ext Z
  rw [sourceSymmetricRankLEVariety_eq_rank_le,
    sourceSymmetricRankLEVariety_eq_rank_le]
  constructor
  · intro hZ
    refine ⟨⟨hZ.1, hZ.2.le⟩, ?_⟩
    intro hlow
    have hbad :
        (Matrix.of fun i j : Fin n => Z i j).rank ≤ r - 1 := hlow.2
    rw [hZ.2] at hbad
    omega
  · intro hZ
    rcases hZ with ⟨hle, hnot_low⟩
    have hnot_rank_le_pred :
        ¬ (Matrix.of fun i j : Fin n => Z i j).rank ≤ r - 1 := by
      intro hrank
      exact hnot_low ⟨hle.1, hrank⟩
    have hrank_eq :
        (Matrix.of fun i j : Fin n => Z i j).rank = r := by
      refine le_antisymm hle.2 ?_
      by_contra hnot
      have hrank_pred :
          (Matrix.of fun i j : Fin n => Z i j).rank ≤ r - 1 := by
        omega
      exact hnot_rank_le_pred hrank_pred
    exact ⟨hle.1, hrank_eq⟩

/-- The source complex Gram variety is the symmetric determinantal variety of
rank at most `d + 1`. -/
theorem sourceComplexGramVariety_eq_sourceSymmetricRankLEVariety
    (d n : ℕ) :
    sourceComplexGramVariety d n =
      sourceSymmetricRankLEVariety n (d + 1) := by
  ext Z
  constructor
  · intro hZ
    exact sourceComplexGramVariety_subset_sourceSymmetricRankLEVariety d n hZ
  · intro hZ
    unfold sourceSymmetricRankLEVariety at hZ
    by_cases hD : d + 1 < n
    · simp [hD] at hZ
      rcases hZ with ⟨hZsym, hminors⟩
      have hrank :
          (Matrix.of fun i j : Fin n => Z i j).rank ≤ d + 1 :=
        sourceMatrix_rank_le_of_minors_eq_zero n (d + 1) hminors
      exact sourceComplexGramVariety_mem_of_symmetric_rank_le d n hZsym hrank
    · have hZsym : Z ∈ sourceSymmetricMatrixSpace n := by
        simpa [hD] using hZ
      have hnle : n ≤ d + 1 := Nat.le_of_not_gt hD
      have hrank :
          (Matrix.of fun i j : Fin n => Z i j).rank ≤ d + 1 := by
        exact (Matrix.rank_le_width
          (Matrix.of fun i j : Fin n => Z i j : Matrix (Fin n) (Fin n) ℂ)).trans hnle
      exact sourceComplexGramVariety_mem_of_symmetric_rank_le d n hZsym hrank

/-- Rank-defined characterization of the source complex Gram variety. -/
theorem sourceComplexGramVariety_eq_rank_le
    (d n : ℕ) :
    sourceComplexGramVariety d n =
      {Z | Z ∈ sourceSymmetricMatrixSpace n ∧
        (Matrix.of fun i j : Fin n => Z i j).rank ≤ d + 1} := by
  rw [sourceComplexGramVariety_eq_sourceSymmetricRankLEVariety,
    sourceSymmetricRankLEVariety_eq_rank_le]

/-- In the easy arity range `n <= d + 1`, the source complex Gram variety is
the full symmetric matrix space. -/
theorem sourceComplexGramVariety_eq_sourceSymmetricMatrixSpace_of_le
    (d n : ℕ)
    (hn : n ≤ d + 1) :
    sourceComplexGramVariety d n = sourceSymmetricMatrixSpace n := by
  rw [sourceComplexGramVariety_eq_rank_le]
  ext Z
  constructor
  · intro hZ
    exact hZ.1
  · intro hZsym
    refine ⟨hZsym, ?_⟩
    exact (Matrix.rank_le_width
      (Matrix.of fun i j : Fin n => Z i j : Matrix (Fin n) (Fin n) ℂ)).trans hn

/-- Full symmetric-coordinate inverse continuous linear map for the easy-arity
branch.  It uses the selected symmetric-coordinate chart with all rows selected
and `I = id`. -/
noncomputable def sourceFullSymCoordMapCLM
    (n : ℕ) :
    (Fin (Fintype.card
      (sourceSelectedSymCoordKey n n (fun i : Fin n => i))) → ℂ) →L[ℂ]
      (Fin n → Fin n → ℂ) :=
  (sourceSelectedComplexSymCoordSubspace n n
    (fun i : Fin n => i)).subtypeL.comp
    ((sourceSelectedComplexSymCoordFinEquiv n n
      (Function.injective_id)).symm.toContinuousLinearMap)

/-- Full symmetric-coordinate inverse map for the easy-arity branch. -/
noncomputable def sourceFullSymCoordMap
    (n : ℕ) :
    (Fin (Fintype.card
      (sourceSelectedSymCoordKey n n (fun i : Fin n => i))) → ℂ) →
      (Fin n → Fin n → ℂ) :=
  sourceFullSymCoordMapCLM n

/-- The full symmetric-coordinate inverse map lands in the symmetric affine
matrix space. -/
theorem sourceFullSymCoordMap_mem_sourceSymmetricMatrixSpace
    (n : ℕ)
    (q : Fin (Fintype.card
      (sourceSelectedSymCoordKey n n (fun i : Fin n => i))) → ℂ) :
    sourceFullSymCoordMap n q ∈ sourceSymmetricMatrixSpace n := by
  intro i j
  change
    (((sourceSelectedComplexSymCoordFinEquiv n n
          (Function.injective_id)).symm q :
          sourceSelectedComplexSymCoordSubspace n n
            (fun i : Fin n => i)) :
        Fin n → Fin n → ℂ) i j =
      (((sourceSelectedComplexSymCoordFinEquiv n n
          (Function.injective_id)).symm q :
          sourceSelectedComplexSymCoordSubspace n n
            (fun i : Fin n => i)) :
        Fin n → Fin n → ℂ) j i
  exact
    ((sourceSelectedComplexSymCoordFinEquiv n n
      (Function.injective_id)).symm q).property i j

/-- The full symmetric-coordinate inverse map is continuous. -/
theorem continuous_sourceFullSymCoordMap
    (n : ℕ) :
    Continuous (sourceFullSymCoordMap n) := by
  exact (sourceFullSymCoordMapCLM n).continuous

/-- The full symmetric-coordinate inverse map is complex differentiable. -/
theorem differentiable_sourceFullSymCoordMap
    (n : ℕ) :
    Differentiable ℂ (sourceFullSymCoordMap n) := by
  exact (sourceFullSymCoordMapCLM n).differentiable

/-- Reconstructing a symmetric matrix from its full symmetric coordinates gives
the original matrix. -/
theorem sourceFullSymCoordMap_of_mem_sourceSymmetricMatrixSpace
    (n : ℕ)
    (Z : Fin n → Fin n → ℂ)
    (hZ : Z ∈ sourceSymmetricMatrixSpace n) :
    sourceFullSymCoordMap n
        ((sourceSelectedComplexSymCoordFinEquiv n n
          (Function.injective_id))
          (⟨Z, by
            intro a b
            exact hZ a b⟩ :
            sourceSelectedComplexSymCoordSubspace n n
              (fun i : Fin n => i))) = Z := by
  change
    (((sourceSelectedComplexSymCoordFinEquiv n n
        (Function.injective_id)).symm
        ((sourceSelectedComplexSymCoordFinEquiv n n
          (Function.injective_id))
          (⟨Z, by
            intro a b
            exact hZ a b⟩ :
            sourceSelectedComplexSymCoordSubspace n n
              (fun i : Fin n => i))) :
        sourceSelectedComplexSymCoordSubspace n n
          (fun i : Fin n => i)) :
      Fin n → Fin n → ℂ) = Z
  rw [ContinuousLinearEquiv.symm_apply_apply]

/-- Full symmetric coordinates are injective. -/
theorem sourceFullSymCoordMap_injective
    (n : ℕ) :
    Function.Injective (sourceFullSymCoordMap n) := by
  intro q r hqr
  have hsub :
      (sourceSelectedComplexSymCoordFinEquiv n n
        (Function.injective_id)).symm q =
        (sourceSelectedComplexSymCoordFinEquiv n n
          (Function.injective_id)).symm r := by
    apply Subtype.ext
    exact hqr
  exact
    (sourceSelectedComplexSymCoordFinEquiv n n
      (Function.injective_id)).symm.injective hsub

/-- The full symmetric-coordinate inverse map parametrizes exactly the full
symmetric affine matrix space. -/
theorem sourceSymmetricMatrixSpace_eq_range_sourceFullSymCoordMap
    (n : ℕ) :
    sourceSymmetricMatrixSpace n = Set.range (sourceFullSymCoordMap n) := by
  ext Z
  constructor
  · intro hZ
    let A : sourceSelectedComplexSymCoordSubspace n n
        (fun i : Fin n => i) :=
      ⟨Z, by
        intro a b
        exact hZ a b⟩
    refine
      ⟨(sourceSelectedComplexSymCoordFinEquiv n n
        (Function.injective_id)) A, ?_⟩
    change
      (((sourceSelectedComplexSymCoordFinEquiv n n
          (Function.injective_id)).symm
          ((sourceSelectedComplexSymCoordFinEquiv n n
            (Function.injective_id)) A) :
          sourceSelectedComplexSymCoordSubspace n n
            (fun i : Fin n => i)) :
        Fin n → Fin n → ℂ) = Z
    rw [ContinuousLinearEquiv.symm_apply_apply]
  · rintro ⟨q, rfl⟩
    exact sourceFullSymCoordMap_mem_sourceSymmetricMatrixSpace n q

/-- In the easy-arity branch, relatively open source-variety domains pull back
to honest open domains in full symmetric coordinates. -/
theorem isOpen_sourceFullSymCoordMap_preimage_of_relOpen_of_le
    (d n : ℕ)
    (hn : n ≤ d + 1)
    {U : Set (Fin n → Fin n → ℂ)}
    (hU_rel : IsRelOpenInSourceComplexGramVariety d n U) :
    IsOpen ((sourceFullSymCoordMap n) ⁻¹' U) := by
  rcases hU_rel with ⟨U0, hU0_open, hU_eq⟩
  rw [hU_eq, sourceComplexGramVariety_eq_sourceSymmetricMatrixSpace_of_le d n hn]
  have hset :
      (sourceFullSymCoordMap n) ⁻¹'
          (U0 ∩ sourceSymmetricMatrixSpace n) =
        (sourceFullSymCoordMap n) ⁻¹' U0 := by
    ext q
    constructor
    · intro hq
      exact hq.1
    · intro hq
      exact ⟨hq, sourceFullSymCoordMap_mem_sourceSymmetricMatrixSpace n q⟩
  rw [hset]
  exact hU0_open.preimage (continuous_sourceFullSymCoordMap n)

/-- In the easy-arity branch, connected relatively open source-variety domains
pull back to connected full symmetric coordinate domains. -/
theorem isConnected_sourceFullSymCoordMap_preimage_of_relOpen_of_le
    (d n : ℕ)
    (hn : n ≤ d + 1)
    {U : Set (Fin n → Fin n → ℂ)}
    (hU_rel : IsRelOpenInSourceComplexGramVariety d n U)
    (hU_conn : IsConnected U) :
    IsConnected ((sourceFullSymCoordMap n) ⁻¹' U) := by
  rcases hU_rel with ⟨U0, _hU0_open, hU_eq⟩
  have hU_subset_sym : U ⊆ sourceSymmetricMatrixSpace n := by
    intro Z hZU
    rw [hU_eq,
      sourceComplexGramVariety_eq_sourceSymmetricMatrixSpace_of_le d n hn]
      at hZU
    exact hZU.2
  let X :=
    Fin (Fintype.card
      (sourceSelectedSymCoordKey n n (fun i : Fin n => i))) → ℂ
  let F : U → X := fun ZU =>
    (sourceSelectedComplexSymCoordFinEquiv n n
      (Function.injective_id))
      (⟨(ZU : Fin n → Fin n → ℂ), hU_subset_sym ZU.property⟩ :
        sourceSelectedComplexSymCoordSubspace n n
          (fun i : Fin n => i))
  have hF_cont : Continuous F := by
    dsimp [F]
    exact
      (sourceSelectedComplexSymCoordFinEquiv n n
        (Function.injective_id)).continuous.comp
        (Continuous.subtype_mk continuous_subtype_val
          (fun ZU => hU_subset_sym ZU.property))
  haveI : ConnectedSpace U := isConnected_iff_connectedSpace.mp hU_conn
  have hconn_image : IsConnected (F '' (Set.univ : Set U)) := by
    exact isConnected_univ.image F hF_cont.continuousOn
  have himage :
      F '' (Set.univ : Set U) =
        (sourceFullSymCoordMap n) ⁻¹' U := by
    ext q
    constructor
    · rintro ⟨ZU, _hZUuniv, rfl⟩
      change sourceFullSymCoordMap n (F ZU) ∈ U
      have hsym :
          (ZU : Fin n → Fin n → ℂ) ∈ sourceSymmetricMatrixSpace n :=
        hU_subset_sym ZU.property
      rw [show sourceFullSymCoordMap n (F ZU) =
          (ZU : Fin n → Fin n → ℂ) from by
        dsimp [F]
        exact
          sourceFullSymCoordMap_of_mem_sourceSymmetricMatrixSpace n
            (ZU : Fin n → Fin n → ℂ) hsym]
      exact ZU.property
    · intro hqU
      refine ⟨⟨sourceFullSymCoordMap n q, hqU⟩, trivial, ?_⟩
      apply sourceFullSymCoordMap_injective n
      have hsym :
          sourceFullSymCoordMap n q ∈ sourceSymmetricMatrixSpace n :=
        sourceFullSymCoordMap_mem_sourceSymmetricMatrixSpace n q
      rw [show sourceFullSymCoordMap n
          (F ⟨sourceFullSymCoordMap n q, hqU⟩) =
          sourceFullSymCoordMap n q from by
        dsimp [F]
        exact
          sourceFullSymCoordMap_of_mem_sourceSymmetricMatrixSpace n
            (sourceFullSymCoordMap n q) hsym]
  rwa [himage] at hconn_image

/-- Easy-arity source-variety identity principle.  When `n <= d + 1`, the
source complex Gram variety is the full symmetric affine matrix space, so the
global identity theorem reduces to the ordinary finite-dimensional SCV identity
theorem in full symmetric coordinates. -/
theorem sourceComplexGramVariety_identity_principle_easy
    (d n : ℕ)
    (hn : n ≤ d + 1)
    {U W : Set (Fin n → Fin n → ℂ)}
    {H : (Fin n → Fin n → ℂ) → ℂ}
    (hU_rel : IsRelOpenInSourceComplexGramVariety d n U)
    (hU_conn : IsConnected U)
    (hW_rel : IsRelOpenInSourceComplexGramVariety d n W)
    (hW_ne : W.Nonempty)
    (hW_sub : W ⊆ U)
    (hH : SourceVarietyHolomorphicOn d n H U)
    (hW_zero : Set.EqOn H 0 W) :
    Set.EqOn H 0 U := by
  let X :=
    Fin (Fintype.card
      (sourceSelectedSymCoordKey n n (fun i : Fin n => i))) → ℂ
  let Γ : X → (Fin n → Fin n → ℂ) := sourceFullSymCoordMap n
  let Uhat : Set X := Γ ⁻¹' U
  let What : Set X := Γ ⁻¹' W
  have hUhat_open : IsOpen Uhat := by
    simpa [Γ, Uhat] using
      isOpen_sourceFullSymCoordMap_preimage_of_relOpen_of_le
        d n hn hU_rel
  have hWhat_open : IsOpen What := by
    simpa [Γ, What] using
      isOpen_sourceFullSymCoordMap_preimage_of_relOpen_of_le
        d n hn hW_rel
  have hUhat_conn : IsConnected Uhat := by
    simpa [Γ, Uhat] using
      isConnected_sourceFullSymCoordMap_preimage_of_relOpen_of_le
        d n hn hU_rel hU_conn
  have hW_subset_sym : W ⊆ sourceSymmetricMatrixSpace n := by
    intro Z hZW
    rcases hW_rel with ⟨W0, _hW0_open, hW_eq⟩
    rw [hW_eq,
      sourceComplexGramVariety_eq_sourceSymmetricMatrixSpace_of_le d n hn]
      at hZW
    exact hZW.2
  have hWhat_ne : What.Nonempty := by
    rcases hW_ne with ⟨Z, hZW⟩
    let q : X :=
      (sourceSelectedComplexSymCoordFinEquiv n n
        (Function.injective_id))
        (⟨Z, by
          intro a b
          exact hW_subset_sym hZW a b⟩ :
          sourceSelectedComplexSymCoordSubspace n n
            (fun i : Fin n => i))
    refine ⟨q, ?_⟩
    change Γ q ∈ W
    rw [show Γ q = Z from by
      dsimp [Γ, q]
      exact sourceFullSymCoordMap_of_mem_sourceSymmetricMatrixSpace n Z
        (hW_subset_sym hZW)]
    exact hZW
  have hWhat_sub_Uhat : What ⊆ Uhat := by
    intro q hqW
    exact hW_sub hqW
  have hcomp_diff : DifferentiableOn ℂ (fun q : X => H (Γ q)) Uhat := by
    intro q hqU
    have hΓqU : Γ q ∈ U := hqU
    rcases hH (Γ q) hΓqU with
      ⟨U0, hU0_open, hΓqU0, hHdiffU0, _hU0_sub⟩
    have hHat : DifferentiableAt ℂ H (Γ q) :=
      (hHdiffU0 (Γ q) hΓqU0).differentiableAt
        (hU0_open.mem_nhds hΓqU0)
    exact
      (hHat.comp q
        ((differentiable_sourceFullSymCoordMap n).differentiableAt)
        ).differentiableWithinAt
  rcases hWhat_ne with ⟨q0, hq0W⟩
  have hq0U : q0 ∈ Uhat := hWhat_sub_Uhat hq0W
  have hagree :
      (fun q : X => H (Γ q)) =ᶠ[nhds q0] (fun _ : X => 0) := by
    filter_upwards [hWhat_open.mem_nhds hq0W] with q hqW
    exact hW_zero hqW
  have hzero_coord :
      Set.EqOn (fun q : X => H (Γ q)) (fun _ : X => 0) Uhat := by
    exact identity_theorem_SCV hUhat_open hUhat_conn hcomp_diff
      (differentiableOn_const (c := (0 : ℂ))) hq0U hagree
  have hU_subset_sym : U ⊆ sourceSymmetricMatrixSpace n := by
    intro Z hZU
    rcases hU_rel with ⟨U0, _hU0_open, hU_eq⟩
    rw [hU_eq,
      sourceComplexGramVariety_eq_sourceSymmetricMatrixSpace_of_le d n hn]
      at hZU
    exact hZU.2
  intro Z hZU
  let q : X :=
    (sourceSelectedComplexSymCoordFinEquiv n n
      (Function.injective_id))
      (⟨Z, by
        intro a b
        exact hU_subset_sym hZU a b⟩ :
        sourceSelectedComplexSymCoordSubspace n n
          (fun i : Fin n => i))
  have hΓq : Γ q = Z := by
    dsimp [Γ, q]
    exact sourceFullSymCoordMap_of_mem_sourceSymmetricMatrixSpace n Z
      (hU_subset_sym hZU)
  have hqU : q ∈ Uhat := by
    change Γ q ∈ U
    rw [hΓq]
    exact hZU
  have hzero := hzero_coord hqU
  simpa [hΓq] using hzero

/-- The source complex Gram variety is closed in the ambient source Gram
coordinate space. -/
theorem isClosed_sourceComplexGramVariety
    (d n : ℕ) :
    IsClosed (sourceComplexGramVariety d n) := by
  rw [sourceComplexGramVariety_eq_sourceSymmetricRankLEVariety]
  exact isClosed_sourceSymmetricRankLEVariety n (d + 1)

/-- The regular rank-`d+1` stratum is the complement of the lower-rank
singular locus inside the source complex Gram variety. -/
theorem sourceComplexGramVariety_diff_lowerRank_eq_rankExact
    (d n : ℕ) :
    sourceComplexGramVariety d n \
        sourceSymmetricRankLEVariety n d =
      sourceSymmetricRankExactStratum n (d + 1) := by
  rw [sourceComplexGramVariety_eq_sourceSymmetricRankLEVariety]
  rw [sourceSymmetricRankExactStratum_eq_rankLE_diff n (d + 1)
    (Nat.succ_pos d)]
  have hd : d + 1 - 1 = d := by omega
  rw [hd]

/-- The regular rank-`d+1` stratum is relatively open in the source complex
Gram variety. -/
theorem sourceSymmetricRankExactStratum_relOpenIn_sourceComplexGramVariety
    (d n : ℕ) :
    IsRelOpenInSourceComplexGramVariety d n
      (sourceSymmetricRankExactStratum n (d + 1)) := by
  refine ⟨(sourceSymmetricRankLEVariety n d)ᶜ,
    (isClosed_sourceSymmetricRankLEVariety n d).isOpen_compl, ?_⟩
  calc
    sourceSymmetricRankExactStratum n (d + 1)
        = sourceComplexGramVariety d n \
            sourceSymmetricRankLEVariety n d :=
          (sourceComplexGramVariety_diff_lowerRank_eq_rankExact d n).symm
    _ = (sourceSymmetricRankLEVariety n d)ᶜ ∩
          sourceComplexGramVariety d n := by
        ext Z
        simp [Set.diff_eq, and_comm]

/-- On a block patch with invertible principal block, rank at most the
principal-block size forces every Schur-complement entry to vanish. -/
theorem schur_complement_entry_eq_zero_of_rank_le
    {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (A : Matrix r r ℂ) (B : Matrix r q ℂ) (C : Matrix q q ℂ)
    (hA : IsUnit A.det)
    (hrank : (Matrix.fromBlocks A B Bᵀ C).rank ≤ Fintype.card r)
    (u v : q) :
    (C - Bᵀ * A⁻¹ * B) u v = 0 := by
  by_contra hne
  let rowSel : r ⊕ Unit → r ⊕ q := Sum.elim Sum.inl (fun _ => Sum.inr u)
  let colSel : r ⊕ Unit → r ⊕ q := Sum.elim Sum.inl (fun _ => Sum.inr v)
  let S : Matrix (r ⊕ Unit) (r ⊕ Unit) ℂ :=
    (Matrix.fromBlocks A B Bᵀ C).submatrix rowSel colSel
  have hS_eq :
      S = Matrix.fromBlocks A (fun i _ => B i v)
        (fun _ j => Bᵀ u j) (fun _ _ : Unit => C u v) := by
    ext x y
    cases x <;> cases y <;> rfl
  have hdetS :
      S.det =
        A.det * ((C - Bᵀ * A⁻¹ * B) u v) := by
    classical
    cases ((Matrix.isUnit_iff_isUnit_det A).mpr hA).nonempty_invertible
    rw [hS_eq]
    rw [Matrix.det_fromBlocks₁₁]
    simp [Matrix.det_unique, Matrix.mul_apply]
  have hdetS_ne : S.det ≠ 0 := by
    rw [hdetS]
    exact mul_ne_zero hA.ne_zero hne
  have hge :
      Fintype.card (r ⊕ Unit) ≤
        (Matrix.fromBlocks A B Bᵀ C).rank :=
    matrix_rank_ge_card_of_nondegenerate_square_submatrix
      (A := Matrix.fromBlocks A B Bᵀ C)
      (I := rowSel) (J := colSel)
      (by simpa [S] using hdetS_ne)
  have hcard : Fintype.card (r ⊕ Unit) = Fintype.card r + 1 := by
    simp
  omega

/-- A block matrix with only the upper-left block possibly nonzero has rank at
most the size of that block. -/
theorem rank_fromBlocks_zero₂₂_le_card_left
    {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (A : Matrix r r ℂ) :
    (Matrix.fromBlocks A (0 : Matrix r q ℂ) (0 : Matrix q r ℂ)
      (0 : Matrix q q ℂ)).rank ≤ Fintype.card r := by
  let M : Matrix (r ⊕ q) (r ⊕ q) ℂ :=
    Matrix.fromBlocks A (0 : Matrix r q ℂ) (0 : Matrix q r ℂ)
      (0 : Matrix q q ℂ)
  let rowVec : r → (r ⊕ q → ℂ) := fun i => M.row (Sum.inl i)
  have hrow_mem :
      ∀ x : r ⊕ q,
        M.row x ∈ Submodule.span ℂ (Set.range rowVec) := by
    intro x
    cases x with
    | inl i =>
        exact Submodule.subset_span ⟨i, rfl⟩
    | inr j =>
        have hzero : M.row (Sum.inr j) = 0 := by
          ext y
          cases y <;> rfl
        rw [hzero]
        exact Submodule.zero_mem _
  have hspan_le :
      Submodule.span ℂ (Set.range fun x : r ⊕ q => M.row x) ≤
        Submodule.span ℂ (Set.range rowVec) := by
    exact Submodule.span_le.mpr (by
      rintro v ⟨x, rfl⟩
      exact hrow_mem x)
  rw [Matrix.rank_eq_finrank_span_row]
  calc
    Module.finrank ℂ
        (Submodule.span ℂ (Set.range fun x : r ⊕ q => M.row x))
        ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range rowVec)) :=
          Submodule.finrank_mono hspan_le
    _ ≤ Fintype.card r := by
          simpa using finrank_range_le_card (R := ℂ) rowVec

/-- On a block patch with invertible principal block, Schur-complement zero
forces rank at most the principal-block size. -/
theorem rank_fromBlocks_le_of_schur_complement_eq_zero
    {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    (A : Matrix r r ℂ) (B : Matrix r q ℂ) (C : Matrix q q ℂ)
    (hA : IsUnit A.det)
    (hschur : C - Bᵀ * A⁻¹ * B = 0) :
    (Matrix.fromBlocks A B Bᵀ C).rank ≤ Fintype.card r := by
  classical
  cases ((Matrix.isUnit_iff_isUnit_det A).mpr hA).nonempty_invertible
  have hschur' : C - Bᵀ * ⅟A * B = 0 := by
    simpa [Matrix.invOf_eq_nonsing_inv] using hschur
  rw [Matrix.fromBlocks_eq_of_invertible₁₁ (A := A) (B := B) (C := Bᵀ) (D := C)]
  calc
    (Matrix.fromBlocks 1 0 (Bᵀ * ⅟A) 1 *
          Matrix.fromBlocks A 0 0 (C - Bᵀ * ⅟A * B) *
          Matrix.fromBlocks 1 (⅟A * B) 0 1).rank
        ≤ (Matrix.fromBlocks 1 0 (Bᵀ * ⅟A) 1 *
          Matrix.fromBlocks A 0 0 (C - Bᵀ * ⅟A * B)).rank :=
          Matrix.rank_mul_le_left _ _
    _ ≤ (Matrix.fromBlocks A 0 0 (C - Bᵀ * ⅟A * B)).rank :=
          Matrix.rank_mul_le_right _ _
    _ = (Matrix.fromBlocks A (0 : Matrix r q ℂ) (0 : Matrix q r ℂ)
          (0 : Matrix q q ℂ)).rank := by
          rw [hschur']
    _ ≤ Fintype.card r :=
          rank_fromBlocks_zero₂₂_le_card_left A

/-- For a symmetric block matrix, the lower-left block is the transpose of the
upper-right block. -/
theorem toBlocks₂₁_eq_transpose_toBlocks₁₂_of_symm
    {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] [DecidableEq q]
    {M : Matrix (r ⊕ q) (r ⊕ q) ℂ}
    (hM : ∀ i j, M i j = M j i) :
    M.toBlocks₂₁ = M.toBlocks₁₂ᵀ := by
  ext u i
  exact hM (Sum.inr u) (Sum.inl i)

/-- Reindexed Schur-complement obstruction: on any coordinate patch equivalent
to `r ⊕ q`, symmetry, an invertible principal block, and rank at most `card r`
force every Schur-complement entry to vanish. -/
theorem schur_complement_entry_eq_zero_of_rank_le_reindex
    {ι r q : Type*} [Fintype ι] [Fintype r] [Fintype q]
    [DecidableEq ι] [DecidableEq r] [DecidableEq q]
    (Z : Matrix ι ι ℂ)
    (e : ι ≃ r ⊕ q)
    (hZsym : ∀ i j, Z i j = Z j i)
    (hA : IsUnit ((Z.reindex e e).toBlocks₁₁.det))
    (hrank : Z.rank ≤ Fintype.card r)
    (u v : q) :
    ((Z.reindex e e).toBlocks₂₂ -
        (Z.reindex e e).toBlocks₁₂ᵀ *
          (Z.reindex e e).toBlocks₁₁⁻¹ *
          (Z.reindex e e).toBlocks₁₂) u v = 0 := by
  let M : Matrix (r ⊕ q) (r ⊕ q) ℂ := Z.reindex e e
  let A : Matrix r r ℂ := M.toBlocks₁₁
  let B : Matrix r q ℂ := M.toBlocks₁₂
  let C : Matrix q q ℂ := M.toBlocks₂₂
  have hMsym : ∀ i j, M i j = M j i := by
    intro i j
    simpa [M, Matrix.reindex_apply] using hZsym (e.symm i) (e.symm j)
  have h21 : M.toBlocks₂₁ = Bᵀ := by
    simpa [B] using toBlocks₂₁_eq_transpose_toBlocks₁₂_of_symm hMsym
  have hblock_eq : Matrix.fromBlocks A B Bᵀ C = M := by
    rw [← Matrix.fromBlocks_toBlocks M]
    simp [A, B, C, h21]
  have hrankBlock :
      (Matrix.fromBlocks A B Bᵀ C).rank ≤ Fintype.card r := by
    rw [hblock_eq]
    have hrankM : M.rank = Z.rank := by
      simp [M]
    rw [hrankM]
    exact hrank
  simpa [M, A, B, C] using
    schur_complement_entry_eq_zero_of_rank_le
      (A := A) (B := B) (C := C) hA hrankBlock u v

/-- Reindexed Schur-complement graph-to-rank theorem: on any coordinate patch
equivalent to `r ⊕ q`, symmetry, an invertible principal block, and vanishing
Schur complement force rank at most `card r`. -/
theorem rank_le_of_reindexed_schur_complement_eq_zero
    {ι r q : Type*} [Fintype ι] [Fintype r] [Fintype q]
    [DecidableEq ι] [DecidableEq r] [DecidableEq q]
    (Z : Matrix ι ι ℂ)
    (e : ι ≃ r ⊕ q)
    (hZsym : ∀ i j, Z i j = Z j i)
    (hA : IsUnit ((Z.reindex e e).toBlocks₁₁.det))
    (hschur :
      (Z.reindex e e).toBlocks₂₂ -
          (Z.reindex e e).toBlocks₁₂ᵀ *
            (Z.reindex e e).toBlocks₁₁⁻¹ *
            (Z.reindex e e).toBlocks₁₂ = 0) :
    Z.rank ≤ Fintype.card r := by
  let M : Matrix (r ⊕ q) (r ⊕ q) ℂ := Z.reindex e e
  let A : Matrix r r ℂ := M.toBlocks₁₁
  let B : Matrix r q ℂ := M.toBlocks₁₂
  let C : Matrix q q ℂ := M.toBlocks₂₂
  have hMsym : ∀ i j, M i j = M j i := by
    intro i j
    simpa [M, Matrix.reindex_apply] using hZsym (e.symm i) (e.symm j)
  have h21 : M.toBlocks₂₁ = Bᵀ := by
    simpa [B] using toBlocks₂₁_eq_transpose_toBlocks₁₂_of_symm hMsym
  have hblock_eq : Matrix.fromBlocks A B Bᵀ C = M := by
    rw [← Matrix.fromBlocks_toBlocks M]
    simp [A, B, C, h21]
  have hschur' : C - Bᵀ * A⁻¹ * B = 0 := by
    simpa [M, A, B, C] using hschur
  have hrankM : M.rank ≤ Fintype.card r := by
    rw [← hblock_eq]
    exact rank_fromBlocks_le_of_schur_complement_eq_zero
      (A := A) (B := B) (C := C) hA hschur'
  have hrankM_eq : M.rank = Z.rank := by
    simp [M]
  rw [hrankM_eq] at hrankM
  exact hrankM

/-- Any symmetric rank-exact stratum of rank at most `d + 1` lies in the source
complex Gram variety. -/
theorem sourceSymmetricRankExactStratum_subset_sourceComplexGramVariety
    (d n r : ℕ) (hr : r ≤ d + 1) :
    sourceSymmetricRankExactStratum n r ⊆
      sourceComplexGramVariety d n := by
  intro Z hZ
  rw [sourceComplexGramVariety_eq_rank_le]
  exact ⟨hZ.1, hZ.2.le.trans hr⟩

end BHW
