import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexSchurPatch
import OSReconstruction.ComplexLieGroups.MatrixLieGroup
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Cone support for source symmetric rank strata

This file records the cone algebra, Stiefel-space path-connectedness, and
small-cone contraction used by the local Hall-Wightman source-variety
connectedness proof.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial Module
open scoped Matrix.Norms.Operator

namespace BHW

/-- Nonzero scalar multiplication does not change matrix rank. -/
theorem matrix_rank_smul_of_ne_zero
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (c : ℂ) (hc : c ≠ 0) (A : Matrix m n ℂ) :
    (c • A).rank = A.rank := by
  have hdet : IsUnit ((c • (1 : Matrix m m ℂ)).det) := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ hc)
  have hmul : (c • (1 : Matrix m m ℂ)) * A = c • A := by
    rw [Matrix.smul_mul, Matrix.one_mul]
  rw [← hmul]
  exact Matrix.rank_mul_eq_right_of_isUnit_det
    (c • (1 : Matrix m m ℂ)) A hdet

/-- Rank-exact symmetric strata are cones under nonzero complex scalar
multiplication. -/
theorem sourceSymmetricRankExactStratum_smul_mem
    {n r : ℕ} {Z : Fin n → Fin n → ℂ}
    (hZ : Z ∈ sourceSymmetricRankExactStratum n r)
    {c : ℂ} (hc : c ≠ 0) :
    (c • Z) ∈ sourceSymmetricRankExactStratum n r := by
  refine ⟨?_, ?_⟩
  · intro i j
    simp [Pi.smul_apply, hZ.1 i j]
  · let M : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j : Fin n => Z i j
    have hM :
        (Matrix.of fun i j : Fin n => (c • Z) i j) = c • M := by
      ext i j
      simp [M]
    rw [hM]
    simpa [M] using
      (matrix_rank_smul_of_ne_zero
        (m := Fin n) (n := Fin n) c hc M).trans hZ.2

/-- Scaling source configurations scales their ordinary complex dot-Gram matrix
by the square of the scalar. -/
theorem sourceComplexDotGram_smul
    (D n : ℕ) (a : ℂ) (z : Fin n → Fin D → ℂ) :
    sourceComplexDotGram D n (a • z) =
      (a * a) • sourceComplexDotGram D n z := by
  ext i j
  simp [sourceComplexDotGram, Pi.smul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro μ _hμ
  ring

/-- Scaling a source configuration by the chosen square root scales its
ordinary complex dot-Gram matrix by the original scalar. -/
theorem sourceComplexDotGram_smul_sqrt
    (D n : ℕ) (c : ℂ) (z : Fin n → Fin D → ℂ) :
    sourceComplexDotGram D n ((complexSquareRootChoice c) • z) =
      c • sourceComplexDotGram D n z := by
  rw [sourceComplexDotGram_smul]
  rw [complexSquareRootChoice_mul_self]

/-- The ordinary complex dot-Gram map is continuous. -/
theorem continuous_sourceComplexDotGram
    (D n : ℕ) :
    Continuous (sourceComplexDotGram D n) := by
  unfold sourceComplexDotGram
  exact continuous_pi fun i => continuous_pi fun j =>
    continuous_finset_sum _ fun μ _ =>
      (continuous_apply_apply i μ).mul (continuous_apply_apply j μ)

/-- Full-rank complex source configurations for the ordinary dot-Gram
parametrization. -/
def sourceFullRankConfigurations
    (m r : ℕ) :
    Set (Fin m → Fin r → ℂ) :=
  {A | (Matrix.of fun (i : Fin m) (a : Fin r) => A i a).rank = r}

/-- The coordinate frame associated to an injective selection of `r` rows. -/
def selectedFullRankFrame
    {m r : ℕ} (I : Fin r → Fin m) :
    Fin m → Fin r → ℂ :=
  fun i a => if i = I a then 1 else 0

/-- The standard full-rank coordinate frame. -/
def standardFullRankConfiguration
    (m r : ℕ) (hr : r ≤ m) :
    Fin m → Fin r → ℂ :=
  selectedFullRankFrame (fun a : Fin r => Fin.castLE hr a)

/-- An injectively selected coordinate frame is a full-rank configuration. -/
theorem selectedFullRankFrame_mem_sourceFullRankConfigurations
    {m r : ℕ} {I : Fin r → Fin m} (hI : Function.Injective I) :
    selectedFullRankFrame I ∈ sourceFullRankConfigurations m r := by
  let P : Matrix (Fin m) (Fin r) ℂ :=
    Matrix.of fun i a => selectedFullRankFrame I i a
  have hle : P.rank ≤ r := by
    simpa using Matrix.rank_le_width P
  have hminor : Matrix.det (fun a b : Fin r => P (I a) b) ≠ 0 := by
    have hmat :
        (fun a b : Fin r => P (I a) b) =
          (1 : Matrix (Fin r) (Fin r) ℂ) := by
      ext a b
      by_cases hab : a = b
      · subst hab
        simp [P, selectedFullRankFrame]
      · have hne : I a ≠ I b := fun h => hab (hI h)
        simp [P, selectedFullRankFrame, hne, hab]
    rw [hmat, Matrix.det_one]
    exact one_ne_zero
  have hge : r ≤ P.rank :=
    matrix_rank_ge_of_nondegenerate_square_submatrix
      (A := P) (I := I) (J := id) (by simpa using hminor)
  simpa [sourceFullRankConfigurations, P] using le_antisymm hle hge

/-- The standard coordinate frame is a full-rank configuration. -/
theorem standardFullRankConfiguration_mem_sourceFullRankConfigurations
    {m r : ℕ} (hr : r ≤ m) :
    standardFullRankConfiguration m r hr ∈ sourceFullRankConfigurations m r := by
  apply selectedFullRankFrame_mem_sourceFullRankConfigurations
  intro a b h
  exact Fin.castLE_injective hr h

/-- Left multiplication by an invertible square matrix preserves full-rank
source configurations. -/
theorem sourceFullRankConfigurations_left_mul_isUnit_mem
    {m r : ℕ} {G : Matrix (Fin m) (Fin m) ℂ}
    (hG : IsUnit G.det)
    {A : Fin m → Fin r → ℂ}
    (hA : A ∈ sourceFullRankConfigurations m r) :
    (fun i a =>
      (G * (Matrix.of fun (j : Fin m) (b : Fin r) => A j b)) i a) ∈
      sourceFullRankConfigurations m r := by
  let P : Matrix (Fin m) (Fin r) ℂ :=
    Matrix.of fun (j : Fin m) (b : Fin r) => A j b
  have hrank : (G * P).rank = r := by
    rw [Matrix.rank_mul_eq_right_of_isUnit_det G P hG]
    simpa [sourceFullRankConfigurations, P] using hA
  simpa [sourceFullRankConfigurations, P] using hrank

/-- Right multiplication by an invertible square matrix preserves full-rank
source configurations. -/
theorem sourceFullRankConfigurations_right_mul_isUnit_mem
    {m r : ℕ} {R : Matrix (Fin r) (Fin r) ℂ}
    (hR : IsUnit R.det)
    {A : Fin m → Fin r → ℂ}
    (hA : A ∈ sourceFullRankConfigurations m r) :
    (fun i a =>
      ((Matrix.of fun (j : Fin m) (b : Fin r) => A j b) * R) i a) ∈
      sourceFullRankConfigurations m r := by
  let P : Matrix (Fin m) (Fin r) ℂ :=
    Matrix.of fun (j : Fin m) (b : Fin r) => A j b
  have hrank : (P * R).rank = r := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det R P hR]
    simpa [sourceFullRankConfigurations, P] using hA
  simpa [sourceFullRankConfigurations, P] using hrank

/-- Left multiplication by a matrix in `GL_m(ℂ)` joins a full-rank source
configuration to its translate inside the full-rank configuration space. -/
theorem sourceFullRankConfigurations_joined_left_mul_GL
    {m r : ℕ} {A : Fin m → Fin r → ℂ}
    (hA : A ∈ sourceFullRankConfigurations m r)
    (G : GL (Fin m) ℂ) :
    JoinedIn (sourceFullRankConfigurations m r) A
      (fun i a =>
        ((G : Matrix (Fin m) (Fin m) ℂ) *
          (Matrix.of fun (j : Fin m) (b : Fin r) => A j b)) i a) := by
  let P : Matrix (Fin m) (Fin r) ℂ :=
    Matrix.of fun (j : Fin m) (b : Fin r) => A j b
  let f : GL (Fin m) ℂ → Fin m → Fin r → ℂ :=
    fun R i a => ((R : Matrix (Fin m) (Fin m) ℂ) * P) i a
  have hf : Continuous f := by
    fun_prop
  have hjoin :
      JoinedIn (Set.univ : Set (GL (Fin m) ℂ)) (1 : GL (Fin m) ℂ) G :=
    (MatrixLieGroup.GL_isPathConnected m).joinedIn
      _ (Set.mem_univ _) _ (Set.mem_univ _)
  have himage :
      JoinedIn (f '' (Set.univ : Set (GL (Fin m) ℂ))) (f 1) (f G) :=
    hjoin.map hf
  have hsub :
      f '' (Set.univ : Set (GL (Fin m) ℂ)) ⊆
        sourceFullRankConfigurations m r := by
    rintro B ⟨R, _hR, rfl⟩
    exact
      sourceFullRankConfigurations_left_mul_isUnit_mem
        (Matrix.isUnits_det_units R) hA
  have hf1 : f 1 = A := by
    ext i a
    simp [f, P]
  have htarget :
      f G =
        fun i a =>
          ((G : Matrix (Fin m) (Fin m) ℂ) *
            (Matrix.of fun (j : Fin m) (b : Fin r) => A j b)) i a := rfl
  simpa [hf1, htarget] using himage.mono hsub

/-- Right multiplication by a matrix in `GL_r(ℂ)` joins a full-rank source
configuration to its translate inside the full-rank configuration space. -/
theorem sourceFullRankConfigurations_joined_right_mul_GL
    {m r : ℕ} {A : Fin m → Fin r → ℂ}
    (hA : A ∈ sourceFullRankConfigurations m r)
    (G : GL (Fin r) ℂ) :
    JoinedIn (sourceFullRankConfigurations m r) A
      (fun i a =>
        ((Matrix.of fun (j : Fin m) (b : Fin r) => A j b) *
          (G : Matrix (Fin r) (Fin r) ℂ)) i a) := by
  let P : Matrix (Fin m) (Fin r) ℂ :=
    Matrix.of fun (j : Fin m) (b : Fin r) => A j b
  let f : GL (Fin r) ℂ → Fin m → Fin r → ℂ :=
    fun R i a => (P * (R : Matrix (Fin r) (Fin r) ℂ)) i a
  have hf : Continuous f := by
    fun_prop
  have hjoin :
      JoinedIn (Set.univ : Set (GL (Fin r) ℂ)) (1 : GL (Fin r) ℂ) G :=
    (MatrixLieGroup.GL_isPathConnected r).joinedIn
      _ (Set.mem_univ _) _ (Set.mem_univ _)
  have himage :
      JoinedIn (f '' (Set.univ : Set (GL (Fin r) ℂ))) (f 1) (f G) :=
    hjoin.map hf
  have hsub :
      f '' (Set.univ : Set (GL (Fin r) ℂ)) ⊆
        sourceFullRankConfigurations m r := by
    rintro B ⟨R, _hR, rfl⟩
    exact
      sourceFullRankConfigurations_right_mul_isUnit_mem
        (Matrix.isUnits_det_units R) hA
  have hf1 : f 1 = A := by
    ext i a
    simp [f, P]
  have htarget :
      f G =
        fun i a =>
          ((Matrix.of fun (j : Fin m) (b : Fin r) => A j b) *
            (G : Matrix (Fin r) (Fin r) ℂ)) i a := rfl
  simpa [hf1, htarget] using himage.mono hsub

/-- A full-rank source configuration has a nonzero square row minor using all
`r` source columns. -/
theorem exists_sourceFullRankConfiguration_selected_minor_ne_zero
    {m r : ℕ} {A : Fin m → Fin r → ℂ}
    (hA : A ∈ sourceFullRankConfigurations m r) :
    ∃ I : Fin r → Fin m, Function.Injective I ∧
      Matrix.det (fun a b : Fin r => A (I a) b) ≠ 0 := by
  let P : Matrix (Fin m) (Fin r) ℂ := Matrix.of fun i a => A i a
  have hP_rank : P.rank = r := by
    simpa [sourceFullRankConfigurations, P] using hA
  have hge : r ≤ P.rank := by
    rw [hP_rank]
  rcases exists_nondegenerate_square_submatrix_of_rank_ge P hge with
    ⟨I, J, hdetIJ⟩
  have hIinj : Function.Injective I := by
    intro a b hab
    by_contra hne
    have hzero :
        Matrix.det (fun x y : Fin r => P (I x) (J y)) = 0 :=
      Matrix.det_zero_of_row_eq hne (by
        ext y
        simp [hab])
    exact hdetIJ hzero
  have hJinj : Function.Injective J := by
    intro a b hab
    by_contra hne
    have hzero :
        Matrix.det (fun x y : Fin r => P (I x) (J y)) = 0 :=
      Matrix.det_zero_of_column_eq hne (by
        intro x
        simp [hab])
    exact hdetIJ hzero
  let σ : Equiv.Perm (Fin r) :=
    Equiv.ofBijective J
      ((Fintype.bijective_iff_injective_and_card J).mpr ⟨hJinj, by simp⟩)
  let PI : Matrix (Fin r) (Fin r) ℂ := fun a b => A (I a) b
  have hdet_perm_ne : (PI.submatrix id σ).det ≠ 0 := by
    simpa [PI, P, σ] using hdetIJ
  have hPI_ne : PI.det ≠ 0 := by
    have hperm := Matrix.det_permute' σ PI
    rw [hperm] at hdet_perm_ne
    intro hzero
    exact hdet_perm_ne (by simp [hzero])
  exact ⟨I, hIinj, by simpa [PI] using hPI_ne⟩

/-- In a selected-minor chart, a full-rank source configuration is joined to
the associated coordinate frame.  The path first normalizes the selected
`r × r` block through `GL_r(ℂ)`, then linearly kills the remaining rows while
the selected block stays equal to the identity. -/
theorem sourceFullRankConfigurations_joined_selectedFrame
    {m r : ℕ} {A : Fin m → Fin r → ℂ}
    (hA : A ∈ sourceFullRankConfigurations m r)
    {I : Fin r → Fin m}
    (hIminor : Matrix.det (fun a b : Fin r => A (I a) b) ≠ 0) :
    JoinedIn (sourceFullRankConfigurations m r)
      A (selectedFullRankFrame I) := by
  let P : Matrix (Fin m) (Fin r) ℂ :=
    Matrix.of fun (i : Fin m) (a : Fin r) => A i a
  let B : Matrix (Fin r) (Fin r) ℂ := fun a b => A (I a) b
  let G : GL (Fin r) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero B hIminor
  have hIinj : Function.Injective I := by
    intro a b hEq
    by_contra hne
    have hzero : Matrix.det B = 0 :=
      Matrix.det_zero_of_row_eq hne (by
        ext x
        simp [B, hEq])
    exact hIminor (by simpa [B] using hzero)
  let A₁ : Fin m → Fin r → ℂ :=
    fun i a => (P * ((G⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) i a
  have hjoin₁ : JoinedIn (sourceFullRankConfigurations m r) A A₁ := by
    simpa [A₁, P] using
      sourceFullRankConfigurations_joined_right_mul_GL
        (m := m) (r := r) (A := A) hA G⁻¹
  have hA₁_selected :
      ∀ a b : Fin r, A₁ (I a) b = selectedFullRankFrame I (I a) b := by
    intro a b
    have hmul :
        B * ((G⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = 1 := by
      calc
        B * ((G⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)
            = ((G : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
                ((G⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by
              simp [G]
        _ = ((G * G⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := rfl
        _ = 1 := by simp
    have hentry := congrFun (congrFun hmul a) b
    have hAentry :
        A₁ (I a) b =
          (B * ((G⁻¹ : GL (Fin r) ℂ) :
            Matrix (Fin r) (Fin r) ℂ)) a b := by
      simp [A₁, P, B, Matrix.mul_apply]
    rw [hAentry, hentry]
    by_cases hab : a = b
    · subst hab
      simp [selectedFullRankFrame]
    · have hne : I a ≠ I b := by
        intro hEq
        exact hab (hIinj hEq)
      simp [selectedFullRankFrame, hne, hab]
  have hjoin₂ :
      JoinedIn (sourceFullRankConfigurations m r) A₁ (selectedFullRankFrame I) := by
    let f : ℝ → Fin m → Fin r → ℂ :=
      fun t i a =>
        (1 - (t : ℂ)) * A₁ i a + (t : ℂ) * selectedFullRankFrame I i a
    refine JoinedIn.ofLine (f := f) ?_ ?_ ?_ ?_
    · fun_prop
    · ext i a
      simp [f]
    · ext i a
      simp [f]
    · rintro X ⟨t, ht, rfl⟩
      let Q : Matrix (Fin m) (Fin r) ℂ := Matrix.of fun i a => f t i a
      have hle : Q.rank ≤ r := by
        simpa using Matrix.rank_le_width Q
      have hminor : Matrix.det (fun a b : Fin r => Q (I a) b) ≠ 0 := by
        have hmat :
            (fun a b : Fin r => Q (I a) b) =
              (1 : Matrix (Fin r) (Fin r) ℂ) := by
          ext a b
          have hframe :
              selectedFullRankFrame I (I a) b =
                (1 : Matrix (Fin r) (Fin r) ℂ) a b := by
            by_cases hab : a = b
            · subst hab
              simp [selectedFullRankFrame]
            · have hne : I a ≠ I b := fun hEq => hab (hIinj hEq)
              simp [selectedFullRankFrame, hne, hab]
          simp [Q, f, hA₁_selected a b, hframe]
          ring
        rw [hmat, Matrix.det_one]
        exact one_ne_zero
      have hge : r ≤ Q.rank :=
        matrix_rank_ge_of_nondegenerate_square_submatrix
          (A := Q) (I := I) (J := id) (by simpa using hminor)
      simpa [sourceFullRankConfigurations, Q] using le_antisymm hle hge
  exact hjoin₁.trans hjoin₂

/-- Any selected coordinate frame is joined to the standard coordinate frame.
The proof extends the selected-row injection to a permutation of `Fin m`; the
corresponding permutation matrix lies in `GL_m(ℂ)` and carries the standard
frame to the selected one. -/
theorem selectedFullRankFrame_joined_standard
    {m r : ℕ} (hr : r ≤ m)
    {I : Fin r → Fin m} (hI : Function.Injective I) :
    JoinedIn (sourceFullRankConfigurations m r)
      (selectedFullRankFrame I)
      (standardFullRankConfiguration m r hr) := by
  let x : Fin r ↪ Fin m := ⟨fun a => Fin.castLE hr a, Fin.castLE_injective hr⟩
  let y : Fin r ↪ Fin m := ⟨I, hI⟩
  have htrans := Equiv.Perm.isMultiplyPretransitive (Fin m) r
  rw [MulAction.isMultiplyPretransitive_iff] at htrans
  rcases htrans x y with ⟨σ, hσxy⟩
  have hσ : ∀ a : Fin r, σ (Fin.castLE hr a) = I a := by
    intro a
    have happ := congrFun (congrArg Function.Embedding.toFun hσxy) a
    simpa [x, y] using happ
  let G : GL (Fin m) ℂ :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero ((σ⁻¹).permMatrix ℂ) (by
      rw [Matrix.det_permutation]
      exact_mod_cast (Equiv.Perm.sign (σ⁻¹)).ne_zero)
  have hstd :
      standardFullRankConfiguration m r hr ∈
        sourceFullRankConfigurations m r :=
    standardFullRankConfiguration_mem_sourceFullRankConfigurations hr
  have hjoin :=
    sourceFullRankConfigurations_joined_left_mul_GL
      (m := m) (r := r) (A := standardFullRankConfiguration m r hr) hstd G
  have htarget :
      (fun i a =>
        ((G : Matrix (Fin m) (Fin m) ℂ) *
          (Matrix.of fun (j : Fin m) (b : Fin r) =>
            standardFullRankConfiguration m r hr j b)) i a) =
        selectedFullRankFrame I := by
    ext i a
    simp [G, Matrix.mul_apply, standardFullRankConfiguration,
      selectedFullRankFrame]
    by_cases hleft : (σ⁻¹) i = Fin.castLE hr a
    · have hright : i = I a := by
        rw [← hσ a]
        simpa using congrArg σ hleft
      have hinvIa : (σ⁻¹) (I a) = Fin.castLE hr a := by
        rw [← hσ a]
        simp
      have hinvIa' : (Equiv.symm σ) (I a) = Fin.castLE hr a := by
        simpa using hinvIa
      simp [hright, hinvIa']
    · have hright : i ≠ I a := by
        intro hi
        apply hleft
        rw [hi, ← hσ a]
        simp
      have hnot : ¬(Equiv.symm σ) i = Fin.castLE hr a := hleft
      simp [hnot, hright]
  have hjoin' :
      JoinedIn (sourceFullRankConfigurations m r)
        (standardFullRankConfiguration m r hr) (selectedFullRankFrame I) := by
    simpa [htarget] using hjoin
  exact hjoin'.symm

/-- The Stiefel space of full-rank complex source configurations is
path-connected. -/
theorem sourceFullRankConfigurations_isPathConnected
    (m r : ℕ) (hr : r ≤ m) :
    IsPathConnected (sourceFullRankConfigurations m r) := by
  rw [isPathConnected_iff]
  constructor
  · exact ⟨standardFullRankConfiguration m r hr,
      standardFullRankConfiguration_mem_sourceFullRankConfigurations hr⟩
  · intro A hA B hB
    rcases exists_sourceFullRankConfiguration_selected_minor_ne_zero hA with
      ⟨IA, hIA, hAminor⟩
    rcases exists_sourceFullRankConfiguration_selected_minor_ne_zero hB with
      ⟨IB, hIB, hBminor⟩
    have hAstd :
        JoinedIn (sourceFullRankConfigurations m r) A
          (standardFullRankConfiguration m r hr) :=
      (sourceFullRankConfigurations_joined_selectedFrame hA hAminor).trans
        (selectedFullRankFrame_joined_standard hr hIA)
    have hBstd :
        JoinedIn (sourceFullRankConfigurations m r) B
          (standardFullRankConfiguration m r hr) :=
      (sourceFullRankConfigurations_joined_selectedFrame hB hBminor).trans
        (selectedFullRankFrame_joined_standard hr hIB)
    exact hAstd.trans hBstd.symm

/-- A full-rank source configuration maps to the exact symmetric rank stratum
under the ordinary complex dot-Gram map. -/
theorem sourceComplexDotGram_mem_rankExact_of_fullRank
    {m r : ℕ} {A : Fin m → Fin r → ℂ}
    (hA : A ∈ sourceFullRankConfigurations m r) :
    sourceComplexDotGram r m A ∈
      sourceSymmetricRankExactStratum m r := by
  refine ⟨sourceComplexDotGram_mem_sourceSymmetricMatrixSpace r m A, ?_⟩
  let P : Matrix (Fin m) (Fin r) ℂ := Matrix.of fun i a => A i a
  let M : Matrix (Fin m) (Fin m) ℂ :=
    Matrix.of fun i j : Fin m => sourceComplexDotGram r m A i j
  have hM_eq : M = P * Pᵀ := by
    ext i j
    simp [M, P, sourceComplexDotGram, Matrix.mul_apply]
  have hP_rank : P.rank = r := by
    simpa [sourceFullRankConfigurations, P] using hA
  have hle : M.rank ≤ r := by
    have hmul_le : (P * Pᵀ).rank ≤ P.rank :=
      Matrix.rank_mul_le_left P Pᵀ
    rw [hM_eq]
    exact hmul_le.trans_eq hP_rank
  have hP_rank_ge : r ≤ P.rank := by
    rw [hP_rank]
  rcases exists_nondegenerate_square_submatrix_of_rank_ge P hP_rank_ge with
    ⟨I, J, hdetIJ⟩
  let PI : Matrix (Fin r) (Fin r) ℂ := fun a b => A (I a) b
  have hJinj : Function.Injective J := by
    intro a b hab
    by_contra hne
    have hzero : Matrix.det (fun x y : Fin r => P (I x) (J y)) = 0 :=
      Matrix.det_zero_of_column_eq hne (by
        intro x
        simp [hab])
    exact hdetIJ (by simpa using hzero)
  let σ : Equiv.Perm (Fin r) :=
    Equiv.ofBijective J
      ((Fintype.bijective_iff_injective_and_card J).mpr ⟨hJinj, by simp⟩)
  have hdet_perm_ne : (PI.submatrix id σ).det ≠ 0 := by
    simpa [PI, P, σ] using hdetIJ
  have hPI_det_ne : PI.det ≠ 0 := by
    have hperm := Matrix.det_permute' σ PI
    rw [hperm] at hdet_perm_ne
    intro hzero
    exact hdet_perm_ne (by simp [hzero])
  have hminor_ne :
      sourceMatrixMinor m r I I (sourceComplexDotGram r m A) ≠ 0 := by
    have hminor_eq :
        sourceMatrixMinor m r I I (sourceComplexDotGram r m A) =
          (PI * PIᵀ).det := by
      have hmatrix :
          (fun a b : Fin r => sourceComplexDotGram r m A (I a) (I b)) =
            PI * PIᵀ := by
        ext a b
        simp [sourceComplexDotGram, PI, Matrix.mul_apply]
      rw [sourceMatrixMinor, hmatrix]
    rw [hminor_eq, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero hPI_det_ne hPI_det_ne
  have hge : r ≤ M.rank := by
    exact matrix_rank_ge_of_nondegenerate_square_submatrix
      (A := M) (I := I) (J := I) (by
        simpa [sourceMatrixMinor, M] using hminor_ne)
  exact le_antisymm hle hge

/-- Every exact-rank symmetric source matrix has a full-rank ordinary
dot-Gram representative in exactly that rank. -/
theorem exists_fullRank_sourceComplexDotGram_of_rankExact
    {m r : ℕ} {Z : Fin m → Fin m → ℂ}
    (hZ : Z ∈ sourceSymmetricRankExactStratum m r) :
    ∃ A : Fin m → Fin r → ℂ,
      A ∈ sourceFullRankConfigurations m r ∧
        sourceComplexDotGram r m A = Z := by
  rcases complex_symmetric_matrix_factorization_of_rank_le m r hZ.1
      (by rw [hZ.2]) with
    ⟨A, hAeq⟩
  refine ⟨A, ?_, hAeq.symm⟩
  let P : Matrix (Fin m) (Fin r) ℂ := Matrix.of fun i a => A i a
  let M : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i j : Fin m => Z i j
  have hM_eq : M = P * Pᵀ := by
    ext i j
    change Z i j = (P * Pᵀ) i j
    rw [hAeq]
    simp [P, sourceComplexDotGram, Matrix.mul_apply]
  have hM_rank : M.rank = r := by
    simpa [M] using hZ.2
  have hle : P.rank ≤ r := by
    simpa using Matrix.rank_le_width P
  have hge : r ≤ P.rank := by
    have hmul_le : (P * Pᵀ).rank ≤ P.rank :=
      Matrix.rank_mul_le_left P Pᵀ
    have hmul_rank : (P * Pᵀ).rank = r := by
      rw [← hM_eq]
      exact hM_rank
    exact hmul_rank.ge.trans hmul_le
  exact le_antisymm hle hge

/-- The exact symmetric rank stratum is the dot-Gram image of the full-rank
configuration space of the same rank. -/
theorem sourceSymmetricRankExactStratum_eq_sourceComplexDotGram_image_fullRank
    (m r : ℕ) :
    sourceSymmetricRankExactStratum m r =
      sourceComplexDotGram r m '' sourceFullRankConfigurations m r := by
  ext Z
  constructor
  · intro hZ
    rcases exists_fullRank_sourceComplexDotGram_of_rankExact hZ with
      ⟨A, hA, hAZ⟩
    exact ⟨A, hA, hAZ⟩
  · rintro ⟨A, hA, rfl⟩
    exact sourceComplexDotGram_mem_rankExact_of_fullRank hA

/-- Once the full-rank source-configuration space is path-connected, the
exact symmetric rank stratum is path-connected by the dot-Gram map. -/
theorem sourceSymmetricRankExactStratum_isPathConnected_of_fullRank
    (m r : ℕ)
    (hfull : IsPathConnected (sourceFullRankConfigurations m r)) :
    IsPathConnected (sourceSymmetricRankExactStratum m r) := by
  rw [sourceSymmetricRankExactStratum_eq_sourceComplexDotGram_image_fullRank]
  exact hfull.image (continuous_sourceComplexDotGram r m)

/-- The exact symmetric rank stratum is path-connected whenever the requested
rank is at most the ambient size. -/
theorem sourceSymmetricRankExactStratum_isPathConnected
    (m r : ℕ) (hr : r ≤ m) :
    IsPathConnected (sourceSymmetricRankExactStratum m r) :=
  sourceSymmetricRankExactStratum_isPathConnected_of_fullRank m r
    (sourceFullRankConfigurations_isPathConnected m r hr)

/-- Positive real radial scaling joins a point of the exact symmetric rank
stratum to its scaled copy while staying in the same stratum. -/
theorem sourceSymmetricRankExactStratum_joined_radial_smul
    {m r : ℕ} {Z : Fin m → Fin m → ℂ}
    (hZ : Z ∈ sourceSymmetricRankExactStratum m r)
    {ρ : ℝ} (hρ : 0 < ρ) :
    JoinedIn (sourceSymmetricRankExactStratum m r)
      Z ((ρ : ℂ) • Z) := by
  let f : ℝ → Fin m → Fin m → ℂ :=
    fun t => (((1 - t) + t * ρ : ℝ) : ℂ) • Z
  refine JoinedIn.ofLine (f := f) ?_ ?_ ?_ ?_
  · fun_prop
  · ext i j
    simp [f]
  · ext i j
    simp [f]
  · rintro X ⟨t, ht, rfl⟩
    change t ∈ Set.Icc (0 : ℝ) 1 at ht
    have hcoeff_pos : 0 < (1 - t) + t * ρ := by
      rcases eq_or_lt_of_le ht.1 with ht0 | htpos
      · subst ht0
        simp
      · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr ht.2) (mul_pos htpos hρ)
    exact
      sourceSymmetricRankExactStratum_smul_mem hZ
        (by exact_mod_cast hcoeff_pos.ne')

/-- If `0 < ρ ≤ 1`, the positive radial path from `Z` to `ρ • Z` stays inside
any centered ball that already contains `Z`, as well as inside the exact rank
stratum. -/
theorem sourceSymmetricRankExactStratum_joined_ball_radial_smul
    {m r : ℕ} {ε ρ : ℝ} (hρ : 0 < ρ) (hρle : ρ ≤ 1)
    {Z : Fin m → Fin m → ℂ}
    (hZball : Z ∈ Metric.ball (0 : Fin m → Fin m → ℂ) ε)
    (hZ : Z ∈ sourceSymmetricRankExactStratum m r) :
    JoinedIn
      (Metric.ball (0 : Fin m → Fin m → ℂ) ε ∩
        sourceSymmetricRankExactStratum m r)
      Z ((ρ : ℂ) • Z) := by
  let f : ℝ → Fin m → Fin m → ℂ :=
    fun t => (((1 - t) + t * ρ : ℝ) : ℂ) • Z
  have hZnorm : ‖Z‖ < ε := by
    simpa [Metric.mem_ball, dist_eq_norm] using hZball
  refine JoinedIn.ofLine (f := f) ?_ ?_ ?_ ?_
  · fun_prop
  · ext i j
    simp [f]
  · ext i j
    simp [f]
  · rintro X ⟨t, ht, rfl⟩
    change t ∈ Set.Icc (0 : ℝ) 1 at ht
    have hcoeff_pos : 0 < (1 - t) + t * ρ := by
      rcases eq_or_lt_of_le ht.1 with ht0 | htpos
      · subst ht0
        simp
      · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr ht.2) (mul_pos htpos hρ)
    have hcoeff_nonneg : 0 ≤ (1 - t) + t * ρ := hcoeff_pos.le
    have hcoeff_le_one : (1 - t) + t * ρ ≤ 1 := by
      have hmul : t * ρ ≤ t * 1 := mul_le_mul_of_nonneg_left hρle ht.1
      linarith
    constructor
    · have hnorm :
          ‖(((1 - t) + t * ρ : ℝ) : ℂ) • Z‖ < ε := by
        rw [norm_smul, Complex.norm_of_nonneg hcoeff_nonneg]
        exact
          (mul_le_of_le_one_left (norm_nonneg Z) hcoeff_le_one).trans_lt
            hZnorm
      simpa [Metric.mem_ball, dist_eq_norm, f] using hnorm
    · exact
        sourceSymmetricRankExactStratum_smul_mem hZ
          (by exact_mod_cast hcoeff_pos.ne')

/-- A continuous path in a normed group has a positive norm bound. -/
theorem exists_pos_norm_bound_of_path
    {E : Type*} [NormedAddCommGroup E]
    {X Y : E} (γ : Path X Y) :
    ∃ M : ℝ, 0 < M ∧ ∀ t : unitInterval, ‖γ t‖ ≤ M := by
  have hcompact : IsCompact (Set.range γ) := isCompact_range γ.continuous
  rcases hcompact.isBounded.exists_pos_norm_le with ⟨M, hMpos, hM⟩
  exact ⟨M, hMpos, fun t => hM (γ t) ⟨t, rfl⟩⟩

/-- If a path in the exact symmetric rank stratum is uniformly bounded, a small
positive radial rescaling of the path lies in a prescribed centered ball. -/
theorem sourceSymmetricRankExactStratum_joined_ball_scaled_path
    {m r : ℕ} {ε ρ M : ℝ} (hρ : 0 < ρ)
    {X Y : Fin m → Fin m → ℂ} (γ : Path X Y)
    (hγ : ∀ t : unitInterval, γ t ∈ sourceSymmetricRankExactStratum m r)
    (hbound : ∀ t : unitInterval, ‖γ t‖ ≤ M)
    (hρM : ρ * M < ε) :
    JoinedIn
      (Metric.ball (0 : Fin m → Fin m → ℂ) ε ∩
        sourceSymmetricRankExactStratum m r)
      ((ρ : ℂ) • X) ((ρ : ℂ) • Y) := by
  let f : (Fin m → Fin m → ℂ) → (Fin m → Fin m → ℂ) :=
    fun Z => ((ρ : ℂ) • Z)
  have hf : Continuous f := by
    fun_prop
  refine ⟨γ.map hf, ?_⟩
  intro t
  constructor
  · have hnorm : ‖((ρ : ℂ) • γ t)‖ < ε := by
      rw [norm_smul, Complex.norm_of_nonneg hρ.le]
      exact (mul_le_mul_of_nonneg_left (hbound t) hρ.le).trans_lt hρM
    simpa [Metric.mem_ball, dist_eq_norm, f] using hnorm
  · exact
      sourceSymmetricRankExactStratum_smul_mem (hγ t)
        (by exact_mod_cast hρ.ne')

/-- Every centered ball meets the exact symmetric rank stratum in a
path-connected set, provided the requested rank is at most the ambient size. -/
theorem sourceSymmetricRankExactStratum_ball_isPathConnected
    (m r : ℕ) (hr : r ≤ m) {ε : ℝ} (hε : 0 < ε) :
    IsPathConnected
      (Metric.ball (0 : Fin m → Fin m → ℂ) ε ∩
        sourceSymmetricRankExactStratum m r) := by
  rw [isPathConnected_iff]
  constructor
  · rcases (sourceSymmetricRankExactStratum_isPathConnected m r hr).nonempty with
      ⟨Z, hZ⟩
    rcases exists_pos_mul_lt hε ‖Z‖ with ⟨ρ, hρ, hsmall⟩
    refine ⟨((ρ : ℂ) • Z), ?_, ?_⟩
    · have hnorm : ‖((ρ : ℂ) • Z)‖ < ε := by
        rw [norm_smul, Complex.norm_of_nonneg hρ.le]
        simpa [mul_comm] using hsmall
      simpa [Metric.mem_ball, dist_eq_norm] using hnorm
    · exact sourceSymmetricRankExactStratum_smul_mem hZ (by exact_mod_cast hρ.ne')
  · intro X hX Y hY
    have hXY : JoinedIn (sourceSymmetricRankExactStratum m r) X Y :=
      (sourceSymmetricRankExactStratum_isPathConnected m r hr).joinedIn
        X hX.2 Y hY.2
    let γ : Path X Y := hXY.somePath
    have hγ : ∀ t : unitInterval, γ t ∈ sourceSymmetricRankExactStratum m r :=
      hXY.somePath_mem
    rcases exists_pos_norm_bound_of_path γ with ⟨M, hMpos, hbound⟩
    rcases exists_pos_mul_lt hε M with ⟨δ, hδpos, hδsmall⟩
    let ρ : ℝ := min δ 1
    have hρ : 0 < ρ := lt_min hδpos zero_lt_one
    have hρle : ρ ≤ 1 := min_le_right δ 1
    have hρδ : ρ ≤ δ := min_le_left δ 1
    have hρM : ρ * M < ε := by
      rw [mul_comm ρ M]
      exact (mul_le_mul_of_nonneg_left hρδ hMpos.le).trans_lt hδsmall
    have hXrad :
        JoinedIn
          (Metric.ball (0 : Fin m → Fin m → ℂ) ε ∩
            sourceSymmetricRankExactStratum m r)
          X ((ρ : ℂ) • X) :=
      sourceSymmetricRankExactStratum_joined_ball_radial_smul
        hρ hρle hX.1 hX.2
    have hmid :
        JoinedIn
          (Metric.ball (0 : Fin m → Fin m → ℂ) ε ∩
            sourceSymmetricRankExactStratum m r)
          ((ρ : ℂ) • X) ((ρ : ℂ) • Y) :=
      sourceSymmetricRankExactStratum_joined_ball_scaled_path
        hρ γ hγ hbound hρM
    have hYrad :
        JoinedIn
          (Metric.ball (0 : Fin m → Fin m → ℂ) ε ∩
            sourceSymmetricRankExactStratum m r)
          Y ((ρ : ℂ) • Y) :=
      sourceSymmetricRankExactStratum_joined_ball_radial_smul
        hρ hρle hY.1 hY.2
    exact (hXrad.trans hmid).trans hYrad.symm

/-- Every neighborhood of zero contains a centered open cone piece whose
intersection with the exact symmetric rank stratum is connected.  This is the
finite-dimensional cone input for the singular Schur chart in the source
Hall-Wightman connectedness argument. -/
theorem sourceSymmetricRankExactCone_small_connected
    (m r : ℕ) (hr : r ≤ m)
    {N : Set (Fin m → Fin m → ℂ)}
    (hN_open : IsOpen N)
    (h0N : (0 : Fin m → Fin m → ℂ) ∈ N) :
    ∃ C : Set (Fin m → Fin m → ℂ),
      (0 : Fin m → Fin m → ℂ) ∈ C ∧
      IsOpen C ∧ C ⊆ N ∧
      IsConnected (C ∩ sourceSymmetricRankExactStratum m r) := by
  have hN_nhds : N ∈ 𝓝 (0 : Fin m → Fin m → ℂ) := hN_open.mem_nhds h0N
  rw [Metric.mem_nhds_iff] at hN_nhds
  rcases hN_nhds with ⟨ε, hε, hεsub⟩
  refine ⟨Metric.ball (0 : Fin m → Fin m → ℂ) ε, ?_, Metric.isOpen_ball, hεsub, ?_⟩
  · simpa [Metric.mem_ball]
  · exact (sourceSymmetricRankExactStratum_ball_isPathConnected m r hr hε).isConnected

end BHW
