import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedSchurResidual
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexSchurPatch
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceRank

/-!
# Euclidean tail model for source-oriented Schur residuals

This file contains the finite coordinate bridge between the shifted residual
tail metric inherited from the ambient Minkowski source coordinates and the
Euclidean tail model used by the small-tail realization induction.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

private theorem matrix_eq_zero_of_rank_eq_zero_tail
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

/-- Euclidean tail oriented coordinates: ordinary dot-product Gram coordinates
and all top tail determinants. -/
structure SourceTailOrientedData
    (D m : ℕ) where
  gram : Matrix (Fin m) (Fin m) ℂ
  det : (Fin D ↪ Fin m) → ℂ

@[ext]
theorem SourceTailOrientedData.ext
    {D m : ℕ}
    {T U : SourceTailOrientedData D m}
    (hgram : T.gram = U.gram)
    (hdet : T.det = U.det) :
    T = U := by
  cases T
  cases U
  simp at hgram hdet ⊢
  exact ⟨hgram, hdet⟩

@[ext]
theorem SourceShiftedTailOrientedData.ext
    {d r m : ℕ}
    {hrD : r < d + 1}
    {T U : SourceShiftedTailOrientedData d r hrD m}
    (hgram : T.gram = U.gram)
    (hdet : T.det = U.det) :
    T = U := by
  cases T
  cases U
  simp at hgram hdet ⊢
  exact ⟨hgram, hdet⟩

/-- Euclidean tail oriented invariant of a tail tuple. -/
def sourceTailOrientedInvariant
    (D m : ℕ)
    (q : Fin m → Fin D → ℂ) :
    SourceTailOrientedData D m where
  gram := fun u v => ∑ μ : Fin D, q u μ * q v μ
  det := fun lam => Matrix.det (fun a μ : Fin D => q (lam a) μ)

@[simp]
theorem sourceTailOrientedInvariant_gram
    (D m : ℕ)
    (q : Fin m → Fin D → ℂ) :
    (sourceTailOrientedInvariant D m q).gram =
      fun u v => ∑ μ : Fin D, q u μ * q v μ := by
  rfl

@[simp]
theorem sourceTailOrientedInvariant_det
    (D m : ℕ)
    (q : Fin m → Fin D → ℂ)
    (lam : Fin D ↪ Fin m) :
    (sourceTailOrientedInvariant D m q).det lam =
      Matrix.det (fun a μ : Fin D => q (lam a) μ) := by
  rfl

/-- The Euclidean tail oriented variety. -/
def sourceTailOrientedVariety
    (D m : ℕ) :
    Set (SourceTailOrientedData D m) :=
  Set.range (sourceTailOrientedInvariant D m)

/-- For Euclidean tail data coming from a tuple, the determinant of a selected
Gram block is the square of the corresponding selected tail determinant. -/
theorem sourceTailOrientedInvariant_selectedGram_det
    (D m : ℕ)
    (q : Fin m → Fin D → ℂ)
    (ι : Fin D ↪ Fin m) :
    Matrix.det (fun a b : Fin D =>
        (sourceTailOrientedInvariant D m q).gram (ι a) (ι b)) =
      (sourceTailOrientedInvariant D m q).det ι *
        (sourceTailOrientedInvariant D m q).det ι := by
  let M : Matrix (Fin D) (Fin D) ℂ := fun a μ => q (ι a) μ
  have hgram :
      (fun a b : Fin D =>
        (sourceTailOrientedInvariant D m q).gram (ι a) (ι b)) =
        M * Mᵀ := by
    ext a b
    simp [sourceTailOrientedInvariant, M, Matrix.mul_apply,
      Matrix.transpose_apply]
  calc
    Matrix.det (fun a b : Fin D =>
        (sourceTailOrientedInvariant D m q).gram (ι a) (ι b))
        = Matrix.det (M * Mᵀ) := by rw [hgram]
    _ = Matrix.det M * Matrix.det M := by
        rw [Matrix.det_mul, Matrix.det_transpose]
    _ = (sourceTailOrientedInvariant D m q).det ι *
        (sourceTailOrientedInvariant D m q).det ι := by
          rfl

/-- For a realized Euclidean tail tuple, every mixed selected Gram determinant
is the product of the two corresponding oriented determinant coordinates. -/
theorem sourceTailOrientedInvariant_mixedGram_det
    (D m : ℕ)
    (q : Fin m → Fin D → ℂ)
    (ι κ : Fin D ↪ Fin m) :
    Matrix.det (fun a b : Fin D =>
        (sourceTailOrientedInvariant D m q).gram (ι a) (κ b)) =
      (sourceTailOrientedInvariant D m q).det ι *
        (sourceTailOrientedInvariant D m q).det κ := by
  let Mι : Matrix (Fin D) (Fin D) ℂ := fun a μ => q (ι a) μ
  let Mκ : Matrix (Fin D) (Fin D) ℂ := fun a μ => q (κ a) μ
  have hgram :
      (fun a b : Fin D =>
        (sourceTailOrientedInvariant D m q).gram (ι a) (κ b)) =
        Mι * Mκᵀ := by
    ext a b
    simp [sourceTailOrientedInvariant, Mι, Mκ, Matrix.mul_apply,
      Matrix.transpose_apply]
  calc
    Matrix.det (fun a b : Fin D =>
        (sourceTailOrientedInvariant D m q).gram (ι a) (κ b))
        = Matrix.det (Mι * Mκᵀ) := by rw [hgram]
    _ = Matrix.det Mι * Matrix.det Mκ := by
        rw [Matrix.det_mul, Matrix.det_transpose]
    _ = (sourceTailOrientedInvariant D m q).det ι *
        (sourceTailOrientedInvariant D m q).det κ := by
          rfl

/-- Every Euclidean tail-variety point satisfies the selected Gram determinant
square relation with its oriented determinant coordinate. -/
theorem sourceTailOrientedVariety_selectedGram_det
    (D m : ℕ)
    {T : SourceTailOrientedData D m}
    (hTvar : T ∈ sourceTailOrientedVariety D m)
    (ι : Fin D ↪ Fin m) :
    Matrix.det (fun a b : Fin D => T.gram (ι a) (ι b)) =
      T.det ι * T.det ι := by
  rcases hTvar with ⟨q, rfl⟩
  exact sourceTailOrientedInvariant_selectedGram_det D m q ι

/-- Every Euclidean tail-variety point satisfies the mixed selected Gram
determinant identity. -/
theorem sourceTailOrientedVariety_mixedGram_det
    (D m : ℕ)
    {T : SourceTailOrientedData D m}
    (hTvar : T ∈ sourceTailOrientedVariety D m)
    (ι κ : Fin D ↪ Fin m) :
    Matrix.det (fun a b : Fin D => T.gram (ι a) (κ b)) =
      T.det ι * T.det κ := by
  rcases hTvar with ⟨q, rfl⟩
  exact sourceTailOrientedInvariant_mixedGram_det D m q ι κ

/-- Multiplying one Euclidean coordinate by `-1` preserves all Gram coordinates
and flips all oriented full-frame determinants. -/
theorem sourceTailOrientedInvariant_reflection
    (D m : ℕ)
    (hD : 0 < D)
    (q : Fin m → Fin D → ℂ) :
    let i0 : Fin D := ⟨0, hD⟩
    let sign : Fin D → ℂ := fun μ => if μ = i0 then -1 else 1
    sourceTailOrientedInvariant D m (fun u μ => sign μ * q u μ) =
      { gram := (sourceTailOrientedInvariant D m q).gram
        det := fun ι => - (sourceTailOrientedInvariant D m q).det ι } := by
  intro i0 sign
  have hsign_sq : ∀ μ, sign μ * sign μ = 1 := by
    intro μ
    by_cases hμ : μ = i0
    · simp [sign, hμ]
    · simp [sign, hμ]
  apply SourceTailOrientedData.ext
  · ext u v
    simp [sourceTailOrientedInvariant]
    apply Finset.sum_congr rfl
    intro μ _
    calc
      sign μ * q u μ * (sign μ * q v μ)
          = (sign μ * sign μ) * q u μ * q v μ := by ring
      _ = q u μ * q v μ := by rw [hsign_sq μ]; ring
  · funext ι
    let M : Matrix (Fin D) (Fin D) ℂ := fun a μ => q (ι a) μ
    let R : Matrix (Fin D) (Fin D) ℂ := Matrix.diagonal sign
    have hmat :
        (fun a μ : Fin D => sign μ * q (ι a) μ) = M * R := by
      ext a μ
      simp [M, R, Matrix.mul_diagonal, mul_comm]
    have hRdet : R.det = -1 := by
      rw [Matrix.det_diagonal]
      have hprod :
          (∏ μ : Fin D, sign μ) = -1 := by
        rw [Finset.prod_eq_single i0]
        · simp [sign]
        · intro μ _ hμ
          simp [sign, hμ]
        · intro hi0
          exact False.elim (hi0 (Finset.mem_univ i0))
      exact hprod
    calc
      Matrix.det (fun a μ : Fin D => sign μ * q (ι a) μ)
          = Matrix.det (M * R) := by rw [hmat]
      _ = Matrix.det M * Matrix.det R := Matrix.det_mul M R
      _ = -Matrix.det M := by rw [hRdet]; ring

/-- The determinant-flipping coordinate reflection preserves coordinate norms. -/
theorem sourceTail_reflection_norm
    (D m : ℕ)
    (hD : 0 < D)
    (q : Fin m → Fin D → ℂ) :
    let i0 : Fin D := ⟨0, hD⟩
    let sign : Fin D → ℂ := fun μ => if μ = i0 then -1 else 1
    ∀ u μ, ‖sign μ * q u μ‖ = ‖q u μ‖ := by
  intro i0 sign u μ
  by_cases hμ : μ = i0
  · simp [sign, hμ]
  · simp [sign, hμ]

/-- If two Euclidean tail data have the same Gram coordinates and agree on one
nonzero selected determinant, then all determinant coordinates agree by the
mixed-minor identity. -/
theorem sourceTailOrientedInvariant_eq_of_gram_eq_selectedDet
    (D m : ℕ)
    {T : SourceTailOrientedData D m}
    (hTvar : T ∈ sourceTailOrientedVariety D m)
    (ι : Fin D ↪ Fin m)
    (q : Fin m → Fin D → ℂ)
    (hgram : (sourceTailOrientedInvariant D m q).gram = T.gram)
    (hdetι : (sourceTailOrientedInvariant D m q).det ι = T.det ι)
    (hdet_ne : T.det ι ≠ 0) :
    sourceTailOrientedInvariant D m q = T := by
  apply SourceTailOrientedData.ext
  · exact hgram
  · funext κ
    have hq := sourceTailOrientedInvariant_mixedGram_det D m q ι κ
    have hT := sourceTailOrientedVariety_mixedGram_det D m hTvar ι κ
    have hleft :
        Matrix.det (fun a b : Fin D =>
            (sourceTailOrientedInvariant D m q).gram (ι a) (κ b)) =
          Matrix.det (fun a b : Fin D => T.gram (ι a) (κ b)) := by
      congr
      ext a b
      rw [hgram]
    have hprod :
        (sourceTailOrientedInvariant D m q).det ι *
            (sourceTailOrientedInvariant D m q).det κ =
          T.det ι * T.det κ := by
      rw [← hq, hleft, hT]
    rw [hdetι] at hprod
    exact mul_left_cancel₀ hdet_ne hprod

/-- A same-Gram factor of a full-rank Euclidean tail point can be oriented by
at most one coordinate reflection, preserving all coordinate norms. -/
theorem sourceTailOrientedInvariant_or_reflection_eq_of_gram_eq
    (D m : ℕ)
    (hD : 0 < D)
    {T : SourceTailOrientedData D m}
    (hTvar : T ∈ sourceTailOrientedVariety D m)
    (ι : Fin D ↪ Fin m)
    (hdet_ne : T.det ι ≠ 0)
    (q : Fin m → Fin D → ℂ)
    (hgram : (sourceTailOrientedInvariant D m q).gram = T.gram) :
    ∃ q' : Fin m → Fin D → ℂ,
      (∀ u μ, ‖q' u μ‖ = ‖q u μ‖) ∧
      sourceTailOrientedInvariant D m q' = T := by
  have hqsel := sourceTailOrientedInvariant_selectedGram_det D m q ι
  have hTsel := sourceTailOrientedVariety_selectedGram_det D m hTvar ι
  have hleft :
      Matrix.det (fun a b : Fin D =>
          (sourceTailOrientedInvariant D m q).gram (ι a) (ι b)) =
        Matrix.det (fun a b : Fin D => T.gram (ι a) (ι b)) := by
    congr
    ext a b
    rw [hgram]
  have hsq :
      (sourceTailOrientedInvariant D m q).det ι *
          (sourceTailOrientedInvariant D m q).det ι =
        T.det ι * T.det ι := by
    rw [← hqsel, hleft, hTsel]
  rcases mul_self_eq_mul_self_iff.mp hsq with hsame | hneg
  · refine ⟨q, ?_, ?_⟩
    · intro u μ
      rfl
    · exact
        sourceTailOrientedInvariant_eq_of_gram_eq_selectedDet
          D m hTvar ι q hgram hsame hdet_ne
  · let i0 : Fin D := ⟨0, hD⟩
    let sign : Fin D → ℂ := fun μ => if μ = i0 then -1 else 1
    let q' : Fin m → Fin D → ℂ := fun u μ => sign μ * q u μ
    have href :
        sourceTailOrientedInvariant D m q' =
          { gram := (sourceTailOrientedInvariant D m q).gram
            det := fun ι => - (sourceTailOrientedInvariant D m q).det ι } := by
      simpa [q', i0, sign] using
        sourceTailOrientedInvariant_reflection D m hD q
    have hgram' :
        (sourceTailOrientedInvariant D m q').gram = T.gram := by
      have h := congrArg SourceTailOrientedData.gram href
      exact h.trans hgram
    have hdetι' :
        (sourceTailOrientedInvariant D m q').det ι = T.det ι := by
      have h := congrFun (congrArg SourceTailOrientedData.det href) ι
      calc
        (sourceTailOrientedInvariant D m q').det ι
            = - (sourceTailOrientedInvariant D m q).det ι := by
              simpa using h
        _ = T.det ι := by
              rw [hneg]
              ring
    refine ⟨q', ?_, ?_⟩
    · intro u μ
      simpa [q', i0, sign] using
        sourceTail_reflection_norm D m hD q u μ
    · exact
        sourceTailOrientedInvariant_eq_of_gram_eq_selectedDet
          D m hTvar ι q' hgram' hdetι' hdet_ne

/-- On the Euclidean tail variety in positive tail dimension, zero Gram
coordinates force all top determinant coordinates to vanish. -/
theorem sourceTailOrientedVariety_det_eq_zero_of_gram_eq_zero
    (D m : ℕ)
    (hD : 0 < D)
    {T : SourceTailOrientedData D m}
    (hT : T ∈ sourceTailOrientedVariety D m)
    (hgram : T.gram = 0) :
    T.det = 0 := by
  rcases hT with ⟨q, rfl⟩
  funext ι
  have hsquare := sourceTailOrientedInvariant_selectedGram_det D m q ι
  have hsel_zero :
      (fun a b : Fin D =>
        (sourceTailOrientedInvariant D m q).gram (ι a) (ι b)) = 0 := by
    ext a b
    exact congrFun (congrFun hgram (ι a)) (ι b)
  have hzero :
      (sourceTailOrientedInvariant D m q).det ι *
          (sourceTailOrientedInvariant D m q).det ι = 0 := by
    rw [← hsquare, hsel_zero]
    exact Matrix.det_zero (Fin.pos_iff_nonempty.mp hD)
  exact mul_self_eq_zero.mp hzero

/-- Zero-Gram Euclidean tail data are realized by the zero tail tuple. -/
theorem sourceTailOrientedSmallRealization_zeroGram
    (D m : ℕ)
    (hD : 0 < D)
    (T : SourceTailOrientedData D m)
    (hTvar : T ∈ sourceTailOrientedVariety D m)
    (hgram_zero : T.gram = 0) :
    T.det = 0 ∧
      sourceTailOrientedInvariant D m (fun _ _ => 0) = T := by
  have hdet :=
    sourceTailOrientedVariety_det_eq_zero_of_gram_eq_zero
      D m hD hTvar hgram_zero
  refine ⟨hdet, ?_⟩
  apply SourceTailOrientedData.ext
  · ext u v
    rw [hgram_zero]
    simp [sourceTailOrientedInvariant]
  · funext ι
    rw [hdet]
    simp [sourceTailOrientedInvariant]
    exact Matrix.det_zero (Fin.pos_iff_nonempty.mp hD)

/-- Estimate wrapper for the zero-rank Euclidean tail case. -/
theorem sourceTailOrientedSmallRealization_zeroRank_bound
    (D m : ℕ)
    (hD : 0 < D)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧
      ∀ T : SourceTailOrientedData D m,
        T ∈ sourceTailOrientedVariety D m →
        sourceGramMatrixRank m T.gram = 0 →
        (∀ u v, ‖T.gram u v‖ < η) →
        (∀ ι, ‖T.det ι‖ < η) →
        ∃ q : Fin m → Fin D → ℂ,
          (∀ u μ, ‖q u μ‖ < ε) ∧
          sourceTailOrientedInvariant D m q = T := by
  refine ⟨1, by norm_num, ?_⟩
  intro T hTvar hrank _hgramSmall _hdetSmall
  have hgram_zero : T.gram = 0 := by
    exact
      matrix_eq_zero_of_rank_eq_zero_tail T.gram
        (by simpa [sourceGramMatrixRank] using hrank)
  rcases sourceTailOrientedSmallRealization_zeroGram
      D m hD T hTvar hgram_zero with
    ⟨_hdet, hzero_realizes⟩
  refine ⟨fun _ _ => 0, ?_, hzero_realizes⟩
  intro u μ
  simpa using hε

/-- Source-label permutation action on Euclidean tail oriented data. -/
def sourceTailPermuteOrientedData
    (D m : ℕ)
    (σ : Equiv.Perm (Fin m))
    (T : SourceTailOrientedData D m) :
    SourceTailOrientedData D m where
  gram := fun u v => T.gram (σ u) (σ v)
  det := fun lam => T.det (lam.trans σ.toEmbedding)

/-- Permuting the tail tuple permutes Euclidean tail oriented data. -/
theorem sourceTailOrientedInvariant_perm
    (D m : ℕ)
    (σ : Equiv.Perm (Fin m))
    (q : Fin m → Fin D → ℂ) :
    sourceTailOrientedInvariant D m (fun u => q (σ u)) =
      sourceTailPermuteOrientedData D m σ
        (sourceTailOrientedInvariant D m q) := by
  apply SourceTailOrientedData.ext
  · ext u v
    rfl
  · funext lam
    rfl

theorem sourceTailPermuteOrientedData_symm_apply
    (D m : ℕ)
    (σ : Equiv.Perm (Fin m))
    (T : SourceTailOrientedData D m) :
    sourceTailPermuteOrientedData D m σ.symm
        (sourceTailPermuteOrientedData D m σ T) = T := by
  apply SourceTailOrientedData.ext
  · ext u v
    simp [sourceTailPermuteOrientedData]
  · funext lam
    have hcomp : (lam.trans σ.symm.toEmbedding).trans σ.toEmbedding = lam := by
      ext a
      simp [Function.Embedding.trans]
    simp [sourceTailPermuteOrientedData, hcomp]

/-- Source-label permutations preserve membership in the Euclidean tail
oriented variety. -/
theorem sourceTailOrientedVariety_perm_iff
    (D m : ℕ)
    (σ : Equiv.Perm (Fin m))
    (T : SourceTailOrientedData D m) :
    sourceTailPermuteOrientedData D m σ T ∈
        sourceTailOrientedVariety D m ↔
      T ∈ sourceTailOrientedVariety D m := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨fun u => q (σ.symm u), ?_⟩
    apply SourceTailOrientedData.ext
    · ext u v
      have hgram :=
        congrFun
          (congrFun (congrArg SourceTailOrientedData.gram hq) (σ.symm u))
          (σ.symm v)
      simpa [sourceTailPermuteOrientedData] using hgram
    · funext lam
      have hdet :=
        congrFun (congrArg SourceTailOrientedData.det hq)
          (lam.trans σ.symm.toEmbedding)
      have hcomp : (lam.trans σ.symm.toEmbedding).trans σ.toEmbedding = lam := by
        ext a
        simp [Function.Embedding.trans]
      simpa [sourceTailPermuteOrientedData, sourceTailOrientedInvariant,
        hcomp] using hdet
  · rintro ⟨q, rfl⟩
    exact ⟨fun u => q (σ u), sourceTailOrientedInvariant_perm D m σ q⟩

/-- A Euclidean tail point on the oriented variety whose Gram matrix has rank
`r` admits an invertible principal `r × r` Gram block. -/
theorem sourceTail_exists_principalMinor_of_rank
    (D m r : ℕ)
    (T : SourceTailOrientedData D m)
    (hTvar : T ∈ sourceTailOrientedVariety D m)
    (hr : sourceGramMatrixRank m T.gram = r) :
    ∃ ι : Fin r ↪ Fin m,
      IsUnit (Matrix.det (fun a b : Fin r => T.gram (ι a) (ι b))) := by
  rcases hTvar with ⟨q, rfl⟩
  have hsym :
      (sourceTailOrientedInvariant D m q).gram ∈
        sourceSymmetricMatrixSpace m := by
    intro u v
    simp [sourceTailOrientedInvariant, mul_comm]
  have hrank :
      (Matrix.of fun i j : Fin m =>
        (sourceTailOrientedInvariant D m q).gram i j).rank = r := by
    simpa [sourceGramMatrixRank] using hr
  rcases exists_sourcePrincipalMinor_ne_zero_of_sourceSymmetricRank
      (n := m) (r := r) hsym hrank with
    ⟨I, hI, hdet⟩
  refine ⟨⟨I, hI⟩, ?_⟩
  have hdet' :
      Matrix.det (fun a b : Fin r =>
          (sourceTailOrientedInvariant D m q).gram (I a) (I b)) ≠ 0 := by
    simpa [sourceMatrixMinor] using hdet
  exact isUnit_iff_ne_zero.mpr hdet'

/-- Full-frame Euclidean orientation repair: if a symmetric square Gram block
has determinant `δ^2`, then it has a square dot-factor whose determinant is
exactly `δ`.  The only orientation adjustment is right multiplication by a
one-coordinate reflection. -/
theorem sourceTailFullFrame_factorWithDet
    (D : ℕ)
    (hD : 0 < D)
    (A : Matrix (Fin D) (Fin D) ℂ)
    (hAsym : (fun i j : Fin D => A i j) ∈ sourceSymmetricMatrixSpace D)
    (δ : ℂ)
    (hdet : A.det = δ * δ) :
    ∃ M : Matrix (Fin D) (Fin D) ℂ,
      M * Mᵀ = A ∧ M.det = δ := by
  let Z : Fin D → Fin D → ℂ := fun i j => A i j
  have hrank : (Matrix.of fun i j : Fin D => Z i j).rank ≤ D := by
    simpa [Z] using Matrix.rank_le_width A
  rcases complex_symmetric_matrix_factorization_of_rank_le D D hAsym hrank with
    ⟨q, hq⟩
  let M : Matrix (Fin D) (Fin D) ℂ := fun i μ => q i μ
  have hM : M * Mᵀ = A := by
    ext i j
    have hij := congrFun (congrFun hq i) j
    rw [hij]
    simp [M, sourceComplexDotGram, Matrix.mul_apply]
  have hMdet_sq : M.det * M.det = δ * δ := by
    calc
      M.det * M.det = (M * Mᵀ).det := by
        rw [Matrix.det_mul, Matrix.det_transpose]
      _ = A.det := by rw [hM]
      _ = δ * δ := hdet
  rcases (mul_self_eq_mul_self_iff.mp hMdet_sq) with hMdet | hMdet
  · exact ⟨M, hM, hMdet⟩
  · let i0 : Fin D := ⟨0, hD⟩
    let sign : Fin D → ℂ := fun μ => if μ = i0 then -1 else 1
    let R : Matrix (Fin D) (Fin D) ℂ := Matrix.diagonal sign
    have hsign_sq : ∀ μ, sign μ * sign μ = 1 := by
      intro μ
      by_cases hμ : μ = i0
      · simp [sign, hμ]
      · simp [sign, hμ]
    have hRR : R * Rᵀ = 1 := by
      ext μ ν
      by_cases hμν : μ = ν
      · subst hμν
        simp [R, Matrix.mul_apply, Matrix.diagonal, hsign_sq]
      · simp [R, Matrix.mul_apply, Matrix.diagonal, hμν]
    have hRdet : R.det = -1 := by
      rw [Matrix.det_diagonal]
      have hprod :
          (∏ μ : Fin D, sign μ) = -1 := by
        rw [Finset.prod_eq_single i0]
        · simp [sign]
        · intro μ _ hμ
          simp [sign, hμ]
        · intro hi0
          exact False.elim (hi0 (Finset.mem_univ i0))
      exact hprod
    refine ⟨M * R, ?_, ?_⟩
    · calc
        (M * R) * (M * R)ᵀ
            = (M * R) * (Rᵀ * Mᵀ) := by
              rw [Matrix.transpose_mul]
        _ = M * (R * Rᵀ) * Mᵀ := by
              rw [Matrix.mul_assoc M R (Rᵀ * Mᵀ),
                ← Matrix.mul_assoc R Rᵀ Mᵀ,
                ← Matrix.mul_assoc M (R * Rᵀ) Mᵀ]
        _ = M * Mᵀ := by simp [hRR]
        _ = A := hM
    · calc
        (M * R).det = M.det * R.det := Matrix.det_mul M R
        _ = (-δ) * (-1) := by rw [hMdet, hRdet]
        _ = δ := by ring

/-- Any selected injection can be moved to the canonical head labels by a
permutation of the finite source-label set. -/
theorem sourceTail_permute_to_head
    (m r : ℕ)
    (hrm : r ≤ m)
    (ι : Fin r ↪ Fin m) :
    ∃ σ : Equiv.Perm (Fin m),
      ∀ a : Fin r, σ (finSourceHead hrm a) = ι a := by
  classical
  let headEmb : Fin r ↪ Fin m :=
    ⟨finSourceHead hrm, finSourceHead_injective hrm⟩
  let e : Set.range headEmb ≃ Set.range ι :=
    headEmb.toEquivRange.symm.trans ι.toEquivRange
  refine ⟨e.extendSubtype, ?_⟩
  intro a
  have hmem : finSourceHead hrm a ∈ Set.range headEmb := by
    exact Set.mem_range_self a
  calc
    e.extendSubtype (finSourceHead hrm a)
        = e ⟨finSourceHead hrm a, hmem⟩ := by
            exact Equiv.extendSubtype_apply_of_mem e (finSourceHead hrm a) hmem
    _ = ι a := by
        change
          ((headEmb.toEquivRange.symm.trans ι.toEquivRange)
            ⟨headEmb a, Set.mem_range_self a⟩).1 = ι a
        change
          (ι.toEquivRange
            (headEmb.toEquivRange.symm
              ⟨headEmb a, Set.mem_range_self a⟩)).1 = ι a
        rw [Function.Embedding.toEquivRange_symm_apply_self]
        rfl

/-- A small realization of permuted Euclidean tail data transports back to a
small realization of the original ordered data by undoing the source-label
permutation. -/
theorem sourceTailSmallRealization_transport_perm
    (D m : ℕ)
    (σ : Equiv.Perm (Fin m))
    {ε : ℝ}
    {T : SourceTailOrientedData D m}
    {qσ : Fin m → Fin D → ℂ}
    (hsmall : ∀ u μ, ‖qσ u μ‖ < ε)
    (hrealizes :
      sourceTailOrientedInvariant D m qσ =
        sourceTailPermuteOrientedData D m σ T) :
    ∃ q : Fin m → Fin D → ℂ,
      (∀ u μ, ‖q u μ‖ < ε) ∧
      sourceTailOrientedInvariant D m q = T := by
  refine ⟨fun u => qσ (σ.symm u), ?_, ?_⟩
  · intro u μ
    exact hsmall (σ.symm u) μ
  · calc
      sourceTailOrientedInvariant D m (fun u => qσ (σ.symm u))
          = sourceTailPermuteOrientedData D m σ.symm
              (sourceTailOrientedInvariant D m qσ) := by
            exact sourceTailOrientedInvariant_perm D m σ.symm qσ
      _ = sourceTailPermuteOrientedData D m σ.symm
              (sourceTailPermuteOrientedData D m σ T) := by
            rw [hrealizes]
      _ = T := sourceTailPermuteOrientedData_symm_apply D m σ T

/-- Stored diagonal normalization from the shifted tail metric to the Euclidean
tail dot product. -/
structure SourceShiftedTailMetricNormalization
    (d r : ℕ)
    (hrD : r < d + 1) where
  scale : Fin (d + 1 - r) → ℂ
  scale_ne_zero : ∀ μ, scale μ ≠ 0
  scale_sq :
    ∀ μ,
      scale μ * scale μ =
        (MinkowskiSpace.metricSignature d
          (finSourceTail (Nat.le_of_lt hrD) μ) : ℂ)
  detScale : ℂ
  detScale_eq : detScale = ∏ μ, scale μ
  detScale_ne_zero : detScale ≠ 0

/-- Canonical shifted-tail metric normalization. -/
def sourceShiftedTailMetricNormalization
    (d r : ℕ)
    (hrD : r < d + 1) :
    SourceShiftedTailMetricNormalization d r hrD where
  scale := sourceTailMetricScale d r hrD
  scale_ne_zero := sourceTailMetricScale_ne_zero d r hrD
  scale_sq := sourceTailMetricScale_mul_self d r hrD
  detScale := sourceTailMetricDetScale d r hrD
  detScale_eq := rfl
  detScale_ne_zero := sourceTailMetricDetScale_ne_zero d r hrD

/-- Convert shifted-tail oriented data to Euclidean tail data by the diagonal
normalization.  Gram coordinates are unchanged; full determinant coordinates
are multiplied by the product of the coordinate scales. -/
def sourceShiftedTailDataToEuclidean
    (d r m : ℕ)
    (hrD : r < d + 1)
    (N : SourceShiftedTailMetricNormalization d r hrD)
    (T : SourceShiftedTailOrientedData d r hrD m) :
    SourceTailOrientedData (d + 1 - r) m where
  gram := T.gram
  det := fun lam => N.detScale * T.det lam

theorem sourceVectorMinkowskiInner_sourceTailEmbed_tail
    (d r : ℕ)
    (hrD : r < d + 1)
    (q p : Fin (d + 1 - r) → ℂ) :
    sourceVectorMinkowskiInner d
        (sourceTailEmbed d r hrD q)
        (sourceTailEmbed d r hrD p) =
      ∑ μ : Fin (d + 1 - r),
        (MinkowskiSpace.metricSignature d
          (finSourceTail (Nat.le_of_lt hrD) μ) : ℂ) * q μ * p μ := by
  rw [sourceVectorMinkowskiInner]
  rw [← Equiv.sum_comp (sourceHeadTailSumEquiv d r hrD)
    (fun μ : Fin (d + 1) =>
      (MinkowskiSpace.metricSignature d μ : ℂ) *
        sourceTailEmbed d r hrD q μ * sourceTailEmbed d r hrD p μ)]
  simp [sourceHeadTailSumEquiv_inl, sourceHeadTailSumEquiv_inr]

/-- Scaling a shifted-tail tuple by the normalization scalars gives the
Euclidean tail datum associated to the shifted-tail oriented invariant. -/
theorem sourceShiftedTailInvariant_toEuclidean
    (d r m : ℕ)
    (hrD : r < d + 1)
    (N : SourceShiftedTailMetricNormalization d r hrD)
    (q : Fin m → Fin (d + 1 - r) → ℂ) :
    sourceTailOrientedInvariant (d + 1 - r) m
        (fun u μ => N.scale μ * q u μ) =
      sourceShiftedTailDataToEuclidean d r m hrD N
        (sourceShiftedTailOrientedInvariant d r hrD m q) := by
  apply SourceTailOrientedData.ext
  · ext u v
    simp [sourceTailOrientedInvariant, sourceShiftedTailDataToEuclidean,
      sourceShiftedTailOrientedInvariant, sourceShiftedTailGram,
      sourceVectorMinkowskiInner_sourceTailEmbed_tail]
    apply Finset.sum_congr rfl
    intro μ _
    calc
      N.scale μ * q u μ * (N.scale μ * q v μ)
          = (N.scale μ * N.scale μ) * q u μ * q v μ := by ring
      _ = (MinkowskiSpace.metricSignature d
            (finSourceTail (Nat.le_of_lt hrD) μ) : ℂ) * q u μ * q v μ := by
          rw [N.scale_sq μ]
  · funext lam
    let M : Matrix (Fin (d + 1 - r)) (Fin (d + 1 - r)) ℂ :=
      fun a μ => q (lam a) μ
    have hmat :
        (fun a μ : Fin (d + 1 - r) => N.scale μ * q (lam a) μ) =
          M * Matrix.diagonal N.scale := by
      ext a μ
      simp [M, Matrix.mul_apply, Matrix.diagonal, mul_comm]
    calc
      Matrix.det (fun a μ : Fin (d + 1 - r) => N.scale μ * q (lam a) μ)
          = Matrix.det (M * Matrix.diagonal N.scale) := by rw [hmat]
      _ = N.detScale * Matrix.det M := by
          rw [Matrix.det_mul, Matrix.det_diagonal, N.detScale_eq]
          ring
      _ = N.detScale *
            Matrix.det (fun a μ : Fin (d + 1 - r) => q (lam a) μ) := by
          rfl

/-- The diagonal normalization is injective on shifted-tail oriented data. -/
theorem sourceShiftedTailDataToEuclidean_injective
    (d r m : ℕ)
    (hrD : r < d + 1)
    (N : SourceShiftedTailMetricNormalization d r hrD) :
    Function.Injective
      (sourceShiftedTailDataToEuclidean d r m hrD N) := by
  intro T U hTU
  apply SourceShiftedTailOrientedData.ext
  · exact congrArg SourceTailOrientedData.gram hTU
  · funext lam
    have hdet := congrFun (congrArg SourceTailOrientedData.det hTU) lam
    exact mul_left_cancel₀ N.detScale_ne_zero hdet

/-- Shifted-tail variety membership is equivalent to Euclidean tail variety
membership after diagonal normalization. -/
theorem sourceShiftedTailVariety_toEuclidean_iff
    (d r m : ℕ)
    (hrD : r < d + 1)
    (N : SourceShiftedTailMetricNormalization d r hrD)
    (T : SourceShiftedTailOrientedData d r hrD m) :
    sourceShiftedTailDataToEuclidean d r m hrD N T ∈
        sourceTailOrientedVariety (d + 1 - r) m ↔
      T ∈ sourceShiftedTailOrientedVariety d r hrD m := by
  constructor
  · rintro ⟨qE, hqE⟩
    let q : Fin m → Fin (d + 1 - r) → ℂ :=
      fun u μ => (N.scale μ)⁻¹ * qE u μ
    refine ⟨q, ?_⟩
    apply sourceShiftedTailDataToEuclidean_injective d r m hrD N
    calc
      sourceShiftedTailDataToEuclidean d r m hrD N
          (sourceShiftedTailOrientedInvariant d r hrD m q)
          = sourceTailOrientedInvariant (d + 1 - r) m
              (fun u μ => N.scale μ * q u μ) := by
            exact (sourceShiftedTailInvariant_toEuclidean d r m hrD N q).symm
      _ = sourceTailOrientedInvariant (d + 1 - r) m qE := by
            congr
            ext u μ
            simp [q, N.scale_ne_zero μ]
      _ = sourceShiftedTailDataToEuclidean d r m hrD N T := hqE
  · rintro ⟨q, rfl⟩
    exact ⟨fun u μ => N.scale μ * q u μ,
      sourceShiftedTailInvariant_toEuclidean d r m hrD N q⟩

/-- A Euclidean realization of the normalized shifted-tail data descends to a
shifted-tail realization after scaling the coordinates back. -/
theorem sourceShiftedTailInvariant_eq_of_toEuclidean_eq
    (d r m : ℕ)
    (hrD : r < d + 1)
    (N : SourceShiftedTailMetricNormalization d r hrD)
    (q : Fin m → Fin (d + 1 - r) → ℂ)
    (T : SourceShiftedTailOrientedData d r hrD m)
    (hE :
      sourceTailOrientedInvariant (d + 1 - r) m
          (fun u μ => N.scale μ * q u μ) =
        sourceShiftedTailDataToEuclidean d r m hrD N T) :
    sourceShiftedTailOrientedInvariant d r hrD m q = T := by
  apply sourceShiftedTailDataToEuclidean_injective d r m hrD N
  rw [← hE]
  exact (sourceShiftedTailInvariant_toEuclidean d r m hrD N q).symm

/-- Estimate-compatible Euclidean small-realization packet for the tail model.
It stores both directions needed by the rank-deficient Schur chart: small data
are realized by small vectors, and small vectors have small invariant data. -/
structure SourceTailOrientedCompatibleSmallRealization
    (D m : ℕ) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  eta : ℝ
  eta_pos : 0 < eta
  realize :
    ∀ T : SourceTailOrientedData D m,
      T ∈ sourceTailOrientedVariety D m →
      (∀ u v, ‖T.gram u v‖ < eta) →
      (∀ ι, ‖T.det ι‖ < eta) →
      ∃ q : Fin m → Fin D → ℂ,
        (∀ u μ, ‖q u μ‖ < epsilon) ∧
        sourceTailOrientedInvariant D m q = T
  self_image_small :
    ∀ q : Fin m → Fin D → ℂ,
      (∀ u μ, ‖q u μ‖ < epsilon) →
      (∀ u v, ‖(sourceTailOrientedInvariant D m q).gram u v‖ < eta) ∧
      (∀ ι, ‖(sourceTailOrientedInvariant D m q).det ι‖ < eta)

/-- Estimate-compatible shifted-tail small-realization packet.  This is the
shifted-signature analogue consumed by the source-oriented Schur chart. -/
structure SourceShiftedTailCompatibleSmallRealization
    (d r : ℕ)
    (hrD : r < d + 1)
    (m : ℕ) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  eta : ℝ
  eta_pos : 0 < eta
  realize :
    ∀ T : SourceShiftedTailOrientedData d r hrD m,
      T ∈ sourceShiftedTailOrientedVariety d r hrD m →
      (∀ u v, ‖T.gram u v‖ < eta) →
      (∀ ι, ‖T.det ι‖ < eta) →
      ∃ q : Fin m → Fin (d + 1 - r) → ℂ,
        (∀ u μ, ‖q u μ‖ < epsilon) ∧
        sourceShiftedTailOrientedInvariant d r hrD m q = T
  self_image_small :
    ∀ q : Fin m → Fin (d + 1 - r) → ℂ,
      (∀ u μ, ‖q u μ‖ < epsilon) →
      (∀ u v,
        ‖(sourceShiftedTailOrientedInvariant d r hrD m q).gram u v‖ < eta) ∧
      (∀ ι,
        ‖(sourceShiftedTailOrientedInvariant d r hrD m q).det ι‖ < eta)

/-- The shifted-tail compatible small-realization packet follows mechanically
from the Euclidean one by diagonal normalization. -/
def sourceShiftedTailCompatibleSmallRealization_of_euclidean
    (d r m : ℕ)
    (hrD : r < d + 1)
    (E : SourceTailOrientedCompatibleSmallRealization (d + 1 - r) m) :
    SourceShiftedTailCompatibleSmallRealization d r hrD m := by
  classical
  let N := sourceShiftedTailMetricNormalization d r hrD
  have hscale_norm : ∀ μ : Fin (d + 1 - r), ‖N.scale μ‖ = 1 := by
    intro μ
    simp [N, sourceShiftedTailMetricNormalization, sourceTailMetricScale_norm]
  have hdet_norm : ‖N.detScale‖ = 1 := by
    simp [N, sourceShiftedTailMetricNormalization, sourceTailMetricDetScale_norm]
  refine
    { epsilon := E.epsilon
      epsilon_pos := E.epsilon_pos
      eta := E.eta
      eta_pos := E.eta_pos
      realize := ?_
      self_image_small := ?_ }
  · intro T hTvar hTgram hTdet
    have hTEvar :
        sourceShiftedTailDataToEuclidean d r m hrD N T ∈
          sourceTailOrientedVariety (d + 1 - r) m := by
      exact (sourceShiftedTailVariety_toEuclidean_iff d r m hrD N T).2 hTvar
    have hTEgram :
        ∀ u v, ‖(sourceShiftedTailDataToEuclidean d r m hrD N T).gram u v‖ <
          E.eta := by
      intro u v
      exact hTgram u v
    have hTEdet :
        ∀ ι, ‖(sourceShiftedTailDataToEuclidean d r m hrD N T).det ι‖ <
          E.eta := by
      intro ι
      calc
        ‖(sourceShiftedTailDataToEuclidean d r m hrD N T).det ι‖
            = ‖N.detScale * T.det ι‖ := rfl
        _ = ‖T.det ι‖ := by simp [hdet_norm]
        _ < E.eta := hTdet ι
    rcases E.realize
        (sourceShiftedTailDataToEuclidean d r m hrD N T)
        hTEvar hTEgram hTEdet with
      ⟨qE, hqE_small, hqE_realizes⟩
    let q : Fin m → Fin (d + 1 - r) → ℂ :=
      fun u μ => (N.scale μ)⁻¹ * qE u μ
    refine ⟨q, ?_, ?_⟩
    · intro u μ
      calc
        ‖q u μ‖ = ‖qE u μ‖ := by
          simp [q, norm_inv, hscale_norm μ]
        _ < E.epsilon := hqE_small u μ
    · apply sourceShiftedTailInvariant_eq_of_toEuclidean_eq d r m hrD N q T
      calc
        sourceTailOrientedInvariant (d + 1 - r) m
            (fun u μ => N.scale μ * q u μ)
            = sourceTailOrientedInvariant (d + 1 - r) m qE := by
              congr
              ext u μ
              simp [q, N.scale_ne_zero μ]
        _ = sourceShiftedTailDataToEuclidean d r m hrD N T := hqE_realizes
  · intro q hq_small
    have hqE_small :
        ∀ u μ, ‖N.scale μ * q u μ‖ < E.epsilon := by
      intro u μ
      calc
        ‖N.scale μ * q u μ‖ = ‖q u μ‖ := by
          simp [hscale_norm μ]
        _ < E.epsilon := hq_small u μ
    rcases E.self_image_small (fun u μ => N.scale μ * q u μ) hqE_small with
      ⟨hgramE, hdetE⟩
    constructor
    · intro u v
      have h := hgramE u v
      simpa [sourceShiftedTailInvariant_toEuclidean, sourceShiftedTailDataToEuclidean]
        using h
    · intro ι
      have h := hdetE ι
      have h' :
          ‖N.detScale *
              (sourceShiftedTailOrientedInvariant d r hrD m q).det ι‖ <
            E.eta := by
        simpa [sourceShiftedTailInvariant_toEuclidean,
          sourceShiftedTailDataToEuclidean] using h
      calc
        ‖(sourceShiftedTailOrientedInvariant d r hrD m q).det ι‖
            = ‖N.detScale *
                (sourceShiftedTailOrientedInvariant d r hrD m q).det ι‖ := by
              simp [hdet_norm]
        _ < E.eta := h'

end BHW
