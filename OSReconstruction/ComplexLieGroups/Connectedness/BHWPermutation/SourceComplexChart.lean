import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexTangent

/-!
# Complex selected source Gram chart support

This companion file contains the complex selected-coordinate chart substrate
needed after the maximal-totally-real tangent packet.  It keeps the selected
Gram coordinates in the symmetric-coordinate codomain, matching the real
`SourceRegularRank.lean` chart interface.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial
open scoped Matrix.Norms.Operator

namespace BHW

/-- The complex source Gram map is smooth because each coordinate is a finite
sum of quadratic coordinate monomials. -/
theorem contDiff_sourceMinkowskiGram
    (d n : ℕ) :
    ContDiff ℂ ⊤ (sourceMinkowskiGram d n) := by
  rw [contDiff_pi]
  intro i
  rw [contDiff_pi]
  intro j
  unfold sourceMinkowskiGram
  apply ContDiff.sum
  intro μ _
  exact ((contDiff_const.mul (contDiff_apply_apply ℂ ℂ i μ)).mul
    (contDiff_apply_apply ℂ ℂ j μ))

/-- The complex source Gram map has Frechet derivative
`sourceComplexGramDifferential`. -/
theorem sourceMinkowskiGram_hasFDerivAt
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    HasFDerivAt (sourceMinkowskiGram d n)
      (LinearMap.toContinuousLinearMap (sourceComplexGramDifferential d n z)) z := by
  let rowProj : Fin n →
      ((Fin n → Fin (d + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ)) :=
    fun i =>
      ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin n => Fin (d + 1) → ℂ) i
  let coordProj : Fin (d + 1) →
      ((Fin (d + 1) → ℂ) →L[ℂ] ℂ) :=
    fun μ =>
      ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin (d + 1) => ℂ) μ
  let coord : Fin n → Fin (d + 1) →
      ((Fin n → Fin (d + 1) → ℂ) →L[ℂ] ℂ) :=
    fun i μ => (coordProj μ).comp (rowProj i)
  let L : (Fin n → Fin (d + 1) → ℂ) →L[ℂ]
      (Fin n → Fin n → ℂ) :=
    LinearMap.toContinuousLinearMap (sourceComplexGramDifferential d n z)
  change HasFDerivAt (sourceMinkowskiGram d n) L z
  have hL : L =
      ContinuousLinearMap.pi
        (fun i : Fin n =>
          (ContinuousLinearMap.proj (R := ℂ)
            (φ := fun _ : Fin n => Fin n → ℂ) i).comp L) := by
    ext y i j
    rfl
  rw [hL]
  rw [hasFDerivAt_pi]
  intro i
  let Li : (Fin n → Fin (d + 1) → ℂ) →L[ℂ] (Fin n → ℂ) :=
    (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin n => Fin n → ℂ) i).comp L
  change HasFDerivAt
    (fun y : Fin n → Fin (d + 1) → ℂ =>
      sourceMinkowskiGram d n y i) Li z
  have hLi : Li =
      ContinuousLinearMap.pi
        (fun j : Fin n =>
          (ContinuousLinearMap.proj (R := ℂ)
            (φ := fun _ : Fin n => ℂ) j).comp Li) := by
    ext y j
    rfl
  rw [hLi]
  rw [hasFDerivAt_pi]
  intro j
  let component : (Fin n → Fin (d + 1) → ℂ) →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin n => ℂ) j).comp Li
  change HasFDerivAt
    (fun y : Fin n → Fin (d + 1) → ℂ =>
      sourceMinkowskiGram d n y i j) component z
  have hsum : HasFDerivAt
      (fun y : Fin n → Fin (d + 1) → ℂ =>
        ∑ μ : Fin (d + 1),
          (MinkowskiSpace.metricSignature d μ : ℂ) * y i μ * y j μ)
      (∑ μ : Fin (d + 1),
        (MinkowskiSpace.metricSignature d μ : ℂ) •
          (ContinuousLinearMap.smulRight (coord i μ) (z j μ) +
            ContinuousLinearMap.smulRight (coord j μ) (z i μ))) z := by
    apply HasFDerivAt.fun_sum
    intro μ _
    have hi :
        HasFDerivAt
          (fun y : Fin n → Fin (d + 1) → ℂ => y i μ)
          (coord i μ) z := by
      simpa [coord, rowProj, coordProj] using
        (coord i μ).hasFDerivAt (x := z)
    have hj :
        HasFDerivAt
          (fun y : Fin n → Fin (d + 1) → ℂ => y j μ)
          (coord j μ) z := by
      simpa [coord, rowProj, coordProj] using
        (coord j μ).hasFDerivAt (x := z)
    convert (hi.mul hj).const_mul (MinkowskiSpace.metricSignature d μ : ℂ) using 1
    · ext y
      simp
      ring_nf
    · ext h
      simp [coord, rowProj, coordProj, ContinuousLinearMap.smulRight]
      ring_nf
  convert hsum using 1
  ext h
  change (sourceComplexGramDifferential d n z h) i j =
    (∑ μ : Fin (d + 1),
      (MinkowskiSpace.metricSignature d μ : ℂ) •
        (ContinuousLinearMap.smulRight (coord i μ) (z j μ) +
          ContinuousLinearMap.smulRight (coord j μ) (z i μ))) h
  simp [coord, rowProj, coordProj, sourceComplexGramDifferential,
    Finset.sum_apply, ContinuousLinearMap.smulRight]
  apply Finset.sum_congr rfl
  intro μ _
  change
    (MinkowskiSpace.metricSignature d μ : ℂ) *
        (h i μ * z j μ + z i μ * h j μ) =
      (MinkowskiSpace.metricSignature d μ : ℂ) * (h i μ * z j μ) +
        (MinkowskiSpace.metricSignature d μ : ℂ) * (h j μ * z i μ)
  ring

/-- Complex coordinate target for selected Gram variations.  It keeps all
pairings `δG i (I a)` and imposes exactly the symmetry constraints on the
selected block. -/
def sourceSelectedComplexSymCoordSubspace
    (n m : ℕ) (I : Fin m → Fin n) :
    Submodule ℂ (Fin n → Fin m → ℂ) where
  carrier := {A | ∀ a b : Fin m, A (I a) b = A (I b) a}
  zero_mem' := by
    intro a b
    rfl
  add_mem' := by
    intro A B hA hB a b
    change A (I a) b + B (I a) b = A (I b) a + B (I b) a
    rw [hA a b, hB a b]
  smul_mem' := by
    intro c A hA a b
    change c • A (I a) b = c • A (I b) a
    rw [hA a b]

theorem mem_sourceSelectedComplexSymCoordSubspace
    {n m : ℕ} {I : Fin m → Fin n}
    {A : Fin n → Fin m → ℂ} :
    A ∈ sourceSelectedComplexSymCoordSubspace n m I ↔
      ∀ a b : Fin m, A (I a) b = A (I b) a :=
  Iff.rfl

/-- The selected-coordinate projection of the complex Gram differential satisfies
the selected-block symmetry relations. -/
theorem sourceSelectedComplexGramCoord_differential_mem
    (d n : ℕ)
    (z h : Fin n → Fin (d + 1) → ℂ)
    {m : ℕ} (I : Fin m → Fin n) :
    sourceSelectedComplexGramCoord n m I
        ((sourceComplexGramDifferential d n z) h) ∈
      sourceSelectedComplexSymCoordSubspace n m I := by
  intro a b
  exact sourceComplexGramDifferential_symm d n z h (I a) (I b)

/-- The selected complex Gram differential with codomain restricted to the
selected symmetric-coordinate subspace. -/
def sourceSelectedComplexGramDifferentialToSym
    (d n m : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (I : Fin m → Fin n) :
    (Fin n → Fin (d + 1) → ℂ) →ₗ[ℂ]
      sourceSelectedComplexSymCoordSubspace n m I where
  toFun := fun h =>
    ⟨sourceSelectedComplexGramCoord n m I
        ((sourceComplexGramDifferential d n z) h),
      sourceSelectedComplexGramCoord_differential_mem d n z h I⟩
  map_add' := by
    intro h₁ h₂
    ext i a
    simp [sourceSelectedComplexGramCoord_apply]
  map_smul' := by
    intro c h
    ext i a
    simp [sourceSelectedComplexGramCoord_apply]

@[simp]
theorem sourceSelectedComplexGramDifferentialToSym_apply
    (d n m : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (I : Fin m → Fin n)
    (h : Fin n → Fin (d + 1) → ℂ)
    (i : Fin n) (a : Fin m) :
    (sourceSelectedComplexGramDifferentialToSym d n m z I h :
        Fin n → Fin m → ℂ) i a =
      sourceComplexGramDifferential d n z h i (I a) :=
  rfl

/-- Selected complex Gram coordinates, with codomain restricted to the symmetric
selected-coordinate subspace. -/
def sourceSelectedComplexGramMap
    (d n m : ℕ)
    (I : Fin m → Fin n) :
    (Fin n → Fin (d + 1) → ℂ) →
      sourceSelectedComplexSymCoordSubspace n m I :=
  fun z =>
    ⟨sourceSelectedComplexGramCoord n m I (sourceMinkowskiGram d n z), by
      intro a b
      simp [sourceSelectedComplexGramCoord_apply,
        sourceMinkowskiGram_symm d n z (I a) (I b)]⟩

@[simp]
theorem sourceSelectedComplexGramMap_apply
    (d n m : ℕ)
    (I : Fin m → Fin n)
    (z : Fin n → Fin (d + 1) → ℂ)
    (i : Fin n) (a : Fin m) :
    (sourceSelectedComplexGramMap d n m I z : Fin n → Fin m → ℂ) i a =
      sourceMinkowskiGram d n z i (I a) :=
  rfl

/-- The selected complex Gram coordinate map has strict derivative given by the
codomain-restricted selected complex Gram differential. -/
theorem sourceSelectedComplexGramMap_hasStrictFDerivAt
    (d n m : ℕ)
    (I : Fin m → Fin n)
    (z : Fin n → Fin (d + 1) → ℂ) :
    HasStrictFDerivAt
      (sourceSelectedComplexGramMap d n m I)
      (LinearMap.toContinuousLinearMap
        (sourceSelectedComplexGramDifferentialToSym d n m z I)) z := by
  have hfull : HasStrictFDerivAt
      (fun y : Fin n → Fin (d + 1) → ℂ =>
        sourceSelectedComplexGramCoord n m I (sourceMinkowskiGram d n y))
      (LinearMap.toContinuousLinearMap
        ((sourceSelectedComplexGramCoord n m I).comp
          (sourceComplexGramDifferential d n z))) z := by
    have hfullG : HasStrictFDerivAt (sourceMinkowskiGram d n)
        (LinearMap.toContinuousLinearMap (sourceComplexGramDifferential d n z)) z := by
      have hcd : ContDiffAt ℂ ⊤ (sourceMinkowskiGram d n) z :=
        (contDiff_sourceMinkowskiGram d n).contDiffAt
      have hstrict := hcd.hasStrictFDerivAt (by simp)
      have hfderiv := (sourceMinkowskiGram_hasFDerivAt d n z).fderiv
      rwa [hfderiv] at hstrict
    exact
      (LinearMap.toContinuousLinearMap
        (sourceSelectedComplexGramCoord n m I)).hasStrictFDerivAt.comp z hfullG
  apply HasStrictFDerivAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_norm_left
  have hfullNorm := (Asymptotics.isLittleO_norm_left).2 hfull.isLittleO
  simpa [sourceSelectedComplexGramMap, sourceSelectedComplexGramDifferentialToSym,
    sourceSelectedComplexGramCoord_apply] using hfullNorm

/-- A nonzero real source minor makes the selected complex Gram differential
onto the symmetric selected-coordinate codomain at the real-embedded point. -/
theorem sourceSelectedComplexGramDifferentialToSym_surjective_of_sourceRegularMinor_ne_zero
    (d n : ℕ)
    {x : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceRegularMinor d n I J x ≠ 0) :
    Function.Surjective
      (sourceSelectedComplexGramDifferentialToSym d n
        (min n (d + 1)) (realEmbed x) I) := by
  let m := min n (d + 1)
  intro A
  rcases
      sourceSelectedComplexGramDifferential_surjective_of_sourceRegularMinor_ne_zero
        d n hI hJ hminor (A := (A : Fin n → Fin m → ℂ)) A.property with
    ⟨k, hk⟩
  refine ⟨k, ?_⟩
  ext i a
  exact congrFun (congrFun hk i) a

/-- The selected complex Gram coordinate map has the local product chart
supplied by the finite-dimensional implicit-function theorem at a real
nonzero-minor point. -/
theorem sourceSelectedComplexGramMap_implicit_chart_of_nonzero_minor
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceRegularMinor d n I J x0 ≠ 0) :
    ∃ e : OpenPartialHomeomorph
        (Fin n → Fin (d + 1) → ℂ)
        (sourceSelectedComplexSymCoordSubspace n (min n (d + 1)) I ×
          LinearMap.ker
            (sourceSelectedComplexGramDifferentialToSym d n
              (min n (d + 1)) (realEmbed x0) I)),
      realEmbed x0 ∈ e.source ∧
      e (realEmbed x0) =
        (sourceSelectedComplexGramMap d n (min n (d + 1)) I (realEmbed x0), 0) ∧
      ∀ z ∈ e.source,
        (e z).1 = sourceSelectedComplexGramMap d n (min n (d + 1)) I z := by
  let m := min n (d + 1)
  let f := sourceSelectedComplexGramMap d n m I
  let f' : (Fin n → Fin (d + 1) → ℂ) →L[ℂ]
      sourceSelectedComplexSymCoordSubspace n m I :=
    LinearMap.toContinuousLinearMap
      (sourceSelectedComplexGramDifferentialToSym d n m (realEmbed x0) I)
  have hstrict : HasStrictFDerivAt f f' (realEmbed x0) := by
    simpa [f, f'] using
      sourceSelectedComplexGramMap_hasStrictFDerivAt d n m I (realEmbed x0)
  have hsurj : f'.range = ⊤ := by
    exact LinearMap.range_eq_top.mpr
      (sourceSelectedComplexGramDifferentialToSym_surjective_of_sourceRegularMinor_ne_zero
        d n hI hJ hminor)
  let e := hstrict.implicitToOpenPartialHomeomorph f f' hsurj
  refine ⟨e, ?_, ?_, ?_⟩
  · exact hstrict.mem_implicitToOpenPartialHomeomorph_source hsurj
  · simpa [e, f, f'] using hstrict.implicitToOpenPartialHomeomorph_self hsurj
  · intro z hz
    simpa [e, f, f'] using
      hstrict.implicitToOpenPartialHomeomorph_fst hsurj z

/-- Complex maximal coordinate minor of a source configuration. -/
def sourceComplexRegularMinor
    (d n : ℕ)
    (I : Fin (min n (d + 1)) → Fin n)
    (J : Fin (min n (d + 1)) → Fin (d + 1))
    (z : Fin n → Fin (d + 1) → ℂ) : ℂ :=
  Matrix.det (fun a b => z (I a) (J b))

/-- Complex coordinate minors vary continuously with the complex source
configuration. -/
theorem continuous_sourceComplexRegularMinor
    (d n : ℕ)
    (I : Fin (min n (d + 1)) → Fin n)
    (J : Fin (min n (d + 1)) → Fin (d + 1)) :
    Continuous (sourceComplexRegularMinor d n I J) := by
  unfold sourceComplexRegularMinor
  exact (continuous_matrix fun a b =>
    (continuous_apply (J b)).comp (continuous_apply (I a))).matrix_det

/-- Complexifying a real source configuration complexifies its coordinate
minor. -/
theorem sourceComplexRegularMinor_realEmbed
    (d n : ℕ)
    (I : Fin (min n (d + 1)) → Fin n)
    (J : Fin (min n (d + 1)) → Fin (d + 1))
    (x : Fin n → Fin (d + 1) → ℝ) :
    sourceComplexRegularMinor d n I J (realEmbed x) =
      (sourceRegularMinor d n I J x : ℂ) := by
  let M : Matrix (Fin (min n (d + 1))) (Fin (min n (d + 1))) ℝ :=
    Matrix.of fun a b => x (I a) (J b)
  have hmatrix : Complex.ofRealHom.mapMatrix M =
      (Matrix.of fun a b : Fin (min n (d + 1)) =>
        realEmbed (d := d) (n := n) x (I a) (J b)) := by
    ext a b
    rfl
  unfold sourceComplexRegularMinor sourceRegularMinor
  change (Matrix.of fun a b : Fin (min n (d + 1)) =>
      realEmbed (d := d) (n := n) x (I a) (J b)).det =
    ((Matrix.of fun a b : Fin (min n (d + 1)) => x (I a) (J b)).det : ℂ)
  rw [← hmatrix]
  exact (RingHom.map_det Complex.ofRealHom M).symm

/-- A linearly independent family of complex coordinate vectors has a nonzero
square coordinate minor. -/
theorem exists_nonzero_complex_coordinate_minor_of_linearIndependent
    {m D : ℕ}
    {v : Fin m → Fin D → ℂ}
    (hli : LinearIndependent ℂ v) :
    ∃ J : Fin m → Fin D,
      Function.Injective J ∧
      Matrix.det (fun a b => v a (J b)) ≠ 0 := by
  let A : Matrix (Fin m) (Fin D) ℂ := fun a j => v a j
  have hrowspan :
      Module.finrank ℂ (Submodule.span ℂ (Set.range A.row)) = m := by
    have hspan := finrank_span_eq_card (R := ℂ) (b := v) hli
    simpa [A, Matrix.row, Fintype.card_fin] using hspan
  have hcolrank :
      Module.finrank ℂ (Submodule.span ℂ (Set.range A.col)) = m := by
    have hrank_rows := Matrix.rank_eq_finrank_span_row (R := ℂ) A
    have hrank_cols := Matrix.rank_eq_finrank_span_cols (R := ℂ) A
    calc
      Module.finrank ℂ (Submodule.span ℂ (Set.range A.col)) = A.rank := by
        exact hrank_cols.symm
      _ = Module.finrank ℂ (Submodule.span ℂ (Set.range A.row)) := by
        exact hrank_rows
      _ = m := hrowspan
  obtain ⟨c, hc_mem, _hc_span, hc_li⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq (K := ℂ) (s := Set.range A.col)
  let e : Fin m ≃
      Fin (Module.finrank ℂ (Submodule.span ℂ (Set.range A.col))) :=
    finCongr hcolrank.symm
  let J : Fin m → Fin D := fun b => Classical.choose (hc_mem (e b))
  have hJcol : ∀ b : Fin m, A.col (J b) = c (e b) := by
    intro b
    exact Classical.choose_spec (hc_mem (e b))
  have hcols : LinearIndependent ℂ (fun b : Fin m => A.col (J b)) := by
    have hc' : LinearIndependent ℂ (fun b : Fin m => c (e b)) :=
      hc_li.comp e e.injective
    convert hc' using 1
    ext b a
    exact congr_fun (hJcol b) a
  have hJinj : Function.Injective J := by
    intro b₁ b₂ h
    apply hcols.injective
    ext a
    simp [A, Matrix.col, h]
  let B : Matrix (Fin m) (Fin m) ℂ := fun a b => v a (J b)
  have hcolsB : LinearIndependent ℂ B.col := by
    simpa [A, Matrix.col] using hcols
  have hunit : IsUnit B :=
    (Matrix.linearIndependent_cols_iff_isUnit).1 hcolsB
  have hunitdet : IsUnit B.det := B.isUnit_iff_isUnit_det.mp hunit
  exact ⟨J, hJinj, by simpa [B] using hunitdet.ne_zero⟩

/-- A nonzero maximal complex coordinate minor witnesses regularity of the
source configuration. -/
theorem sourceComplexGramRegularAt_of_exists_nonzero_minor
    (d n : ℕ)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hminor :
      ∃ I : Fin (min n (d + 1)) → Fin n,
        Function.Injective I ∧
        ∃ J : Fin (min n (d + 1)) → Fin (d + 1),
          Function.Injective J ∧
          sourceComplexRegularMinor d n I J z ≠ 0) :
    SourceComplexGramRegularAt d n z := by
  rcases hminor with ⟨I, _hI, J, _hJ, hdet⟩
  let restrictJ : (Fin (d + 1) → ℂ) →ₗ[ℂ]
      (Fin (min n (d + 1)) → ℂ) := {
    toFun := fun v b => v (J b)
    map_add' := by
      intro v w
      ext b
      simp
    map_smul' := by
      intro c v
      ext b
      simp }
  have hrows : LinearIndependent ℂ
      (fun a : Fin (min n (d + 1)) =>
        fun b : Fin (min n (d + 1)) => z (I a) (J b)) := by
    exact Matrix.linearIndependent_rows_of_det_ne_zero hdet
  have hzI : LinearIndependent ℂ
      (fun a : Fin (min n (d + 1)) => z (I a)) := by
    apply LinearIndependent.of_comp restrictJ
    simpa [Function.comp_def, restrictJ] using hrows
  unfold SourceComplexGramRegularAt
  let S : Submodule ℂ (Fin (d + 1) → ℂ) :=
    sourceComplexConfigurationSpan d n z
  have hzIS : LinearIndependent ℂ
      (fun a : Fin (min n (d + 1)) =>
        (⟨z (I a), by
          change z (I a) ∈ Submodule.span ℂ (Set.range z)
          exact Submodule.subset_span ⟨I a, rfl⟩⟩ : S)) := by
    apply LinearIndependent.of_comp S.subtype
    simpa [Function.comp_def, S] using hzI
  have hlower : min n (d + 1) ≤ Module.finrank ℂ S := by
    simpa using hzIS.fintype_card_le_finrank
  have hupper_n : Module.finrank ℂ S ≤ n := by
    simpa [S, sourceComplexConfigurationSpan] using
      (finrank_range_le_card (R := ℂ) (b := z))
  have hupper_d : Module.finrank ℂ S ≤ d + 1 := by
    have h := Submodule.finrank_le S
    simpa [Module.finrank_fin_fun] using h
  have hupper : Module.finrank ℂ S ≤ min n (d + 1) :=
    le_min hupper_n hupper_d
  exact le_antisymm hupper hlower

/-- Regularity of a complex source configuration supplies a nonzero maximal
coordinate minor. -/
theorem exists_nonzero_minor_of_sourceComplexGramRegularAt
    (d n : ℕ)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hreg : SourceComplexGramRegularAt d n z) :
    ∃ I : Fin (min n (d + 1)) → Fin n,
      Function.Injective I ∧
      ∃ J : Fin (min n (d + 1)) → Fin (d + 1),
        Function.Injective J ∧
        sourceComplexRegularMinor d n I J z ≠ 0 := by
  have hfin : Module.finrank ℂ (Submodule.span ℂ (Set.range z)) =
      min n (d + 1) := by
    simpa [SourceComplexGramRegularAt, sourceComplexConfigurationSpan] using hreg
  obtain ⟨v, hv_mem, _hv_span, hv_li⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq (K := ℂ) (s := Set.range z)
  let e : Fin (min n (d + 1)) ≃
      Fin (Module.finrank ℂ (Submodule.span ℂ (Set.range z))) :=
    finCongr hfin.symm
  let w : Fin (min n (d + 1)) → Fin (d + 1) → ℂ :=
    fun a => v (e a)
  have hw_li : LinearIndependent ℂ w := hv_li.comp e e.injective
  let I : Fin (min n (d + 1)) → Fin n :=
    fun a => Classical.choose (hv_mem (e a))
  have hIrow : ∀ a : Fin (min n (d + 1)), z (I a) = w a := by
    intro a
    exact Classical.choose_spec (hv_mem (e a))
  have hzI_li :
      LinearIndependent ℂ
        (fun a : Fin (min n (d + 1)) => z (I a)) := by
    convert hw_li using 1
    ext a μ
    exact congr_fun (hIrow a) μ
  have hIinj : Function.Injective I := by
    intro a b h
    apply hzI_li.injective
    ext μ
    simp [h]
  obtain ⟨J, hJinj, hdet⟩ :=
    exists_nonzero_complex_coordinate_minor_of_linearIndependent
      (v := fun a => z (I a)) hzI_li
  exact ⟨I, hIinj, J, hJinj, by simpa [sourceComplexRegularMinor] using hdet⟩

/-- Maximal complex source span is equivalent to the existence of a nonzero
maximal coordinate minor. -/
theorem sourceComplexGramRegularAt_iff_exists_nonzero_minor
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ) :
    SourceComplexGramRegularAt d n z ↔
      ∃ I : Fin (min n (d + 1)) → Fin n,
        Function.Injective I ∧
        ∃ J : Fin (min n (d + 1)) → Fin (d + 1),
          Function.Injective J ∧
          sourceComplexRegularMinor d n I J z ≠ 0 :=
  ⟨exists_nonzero_minor_of_sourceComplexGramRegularAt d n,
    sourceComplexGramRegularAt_of_exists_nonzero_minor d n⟩

/-- The complex regular source configurations form an open subset of complex
source configuration space. -/
theorem isOpen_sourceComplexGramRegularAt
    (d n : ℕ) :
    IsOpen {z : Fin n → Fin (d + 1) → ℂ |
      SourceComplexGramRegularAt d n z} := by
  rw [show {z : Fin n → Fin (d + 1) → ℂ |
        SourceComplexGramRegularAt d n z} =
      ⋃ I : Fin (min n (d + 1)) → Fin n,
        ⋃ _hI : Function.Injective I,
          ⋃ J : Fin (min n (d + 1)) → Fin (d + 1),
            ⋃ _hJ : Function.Injective J,
              {z : Fin n → Fin (d + 1) → ℂ |
                sourceComplexRegularMinor d n I J z ≠ 0} by
    ext z
    simp [sourceComplexGramRegularAt_iff_exists_nonzero_minor]]
  apply isOpen_iUnion
  intro I
  apply isOpen_iUnion
  intro _hI
  apply isOpen_iUnion
  intro J
  apply isOpen_iUnion
  intro _hJ
  exact isOpen_ne_fun (continuous_sourceComplexRegularMinor d n I J)
    continuous_const

/-- A nonzero complex selected minor makes the corresponding selected source
rows complex-linearly independent. -/
theorem linearIndependent_complex_sourceRows_of_sourceComplexRegularMinor_ne_zero
    (d n : ℕ)
    {z : Fin n → Fin (d + 1) → ℂ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hminor : sourceComplexRegularMinor d n I J z ≠ 0) :
    LinearIndependent ℂ (fun a : Fin (min n (d + 1)) => z (I a)) := by
  let m := min n (d + 1)
  let restrictJ : (Fin (d + 1) → ℂ) →ₗ[ℂ]
      (Fin m → ℂ) := {
    toFun := fun v b => v (J b)
    map_add' := by
      intro v w
      ext b
      simp
    map_smul' := by
      intro c v
      ext b
      simp }
  have hrows : LinearIndependent ℂ
      (fun a : Fin m => fun b : Fin m => z (I a) (J b)) := by
    exact Matrix.linearIndependent_rows_of_det_ne_zero hminor
  apply LinearIndependent.of_comp restrictJ
  simpa [Function.comp_def, restrictJ, m] using hrows

/-- Coordinate expansion in the standard complex source basis. -/
theorem sourceComplexStdBasis_sum
    (d : ℕ) (v : Fin (d + 1) → ℂ) :
    (∑ μ : Fin (d + 1), v μ • sourceComplexStdBasisVector d μ) = v := by
  simpa [sourceComplexStdBasisVector, Pi.basisFun_apply, Pi.basisFun_repr] using
    ((Pi.basisFun ℂ (Fin (d + 1))).sum_repr v)

/-- The complex Minkowski-dual vector representing a complex linear
functional. -/
def sourceComplexMinkowskiDualVectorOfLinearFunctional
    (d : ℕ)
    (ell : (Fin (d + 1) → ℂ) →ₗ[ℂ] ℂ) :
    Fin (d + 1) → ℂ :=
  fun μ => (MinkowskiSpace.metricSignature d μ : ℂ) *
    ell (sourceComplexStdBasisVector d μ)

/-- Every complex linear functional on finite-dimensional source Minkowski
space is represented by pairing with its complex Minkowski-dual vector. -/
theorem sourceComplexMinkowskiInner_dualVectorOfLinearFunctional
    (d : ℕ)
    (ell : (Fin (d + 1) → ℂ) →ₗ[ℂ] ℂ)
    (v : Fin (d + 1) → ℂ) :
    sourceComplexMinkowskiInner d
      (sourceComplexMinkowskiDualVectorOfLinearFunctional d ell) v =
        ell v := by
  unfold sourceComplexMinkowskiInner
    sourceComplexMinkowskiDualVectorOfLinearFunctional
  calc
    (∑ μ : Fin (d + 1),
        (MinkowskiSpace.metricSignature d μ : ℂ) *
          ((MinkowskiSpace.metricSignature d μ : ℂ) *
            ell (sourceComplexStdBasisVector d μ)) * v μ)
        = ∑ μ : Fin (d + 1),
            ell (sourceComplexStdBasisVector d μ) * v μ := by
          apply Finset.sum_congr rfl
          intro μ _
          calc
            (MinkowskiSpace.metricSignature d μ : ℂ) *
                ((MinkowskiSpace.metricSignature d μ : ℂ) *
                  ell (sourceComplexStdBasisVector d μ)) * v μ
                =
              ((MinkowskiSpace.metricSignature d μ : ℂ) *
                  (MinkowskiSpace.metricSignature d μ : ℂ)) *
                ell (sourceComplexStdBasisVector d μ) * v μ := by
                  ring
            _ = ell (sourceComplexStdBasisVector d μ) * v μ := by
                  by_cases hμ : μ = 0
                  · simp [MinkowskiSpace.metricSignature, hμ]
                  · simp [MinkowskiSpace.metricSignature, hμ]
    _ = ell (∑ μ : Fin (d + 1), v μ • sourceComplexStdBasisVector d μ) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro μ _
          rw [map_smul]
          simp [smul_eq_mul, mul_comm]
    _ = ell v := by
          rw [sourceComplexStdBasis_sum d v]

/-- A complex-linearly independent source family admits complex Minkowski-dual
vectors with Kronecker pairings. -/
theorem exists_sourceComplexMinkowski_dual_family_of_linearIndependent
    (d m : ℕ)
    {e : Fin m → Fin (d + 1) → ℂ}
    (hli : LinearIndependent ℂ e) :
    ∃ u : Fin m → Fin (d + 1) → ℂ,
      ∀ a b : Fin m,
        sourceComplexMinkowskiInner d (u a) (e b) =
          if a = b then 1 else 0 := by
  let W : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ (Set.range e)
  choose ell hell using
    fun a : Fin m =>
      LinearMap.exists_extend
        ((Finsupp.lapply a).comp hli.repr :
          W →ₗ[ℂ] ℂ)
  refine ⟨fun a => sourceComplexMinkowskiDualVectorOfLinearFunctional d (ell a), ?_⟩
  intro a b
  rw [sourceComplexMinkowskiInner_dualVectorOfLinearFunctional]
  have hell_apply :
      ell a (e b) =
        ((Finsupp.lapply a).comp hli.repr)
          (⟨e b, by
            change e b ∈ Submodule.span ℂ (Set.range e)
            exact Submodule.subset_span ⟨b, rfl⟩⟩ : W) := by
    simpa [LinearMap.comp_apply] using
      congrArg
        (fun L : W →ₗ[ℂ] ℂ =>
          L (⟨e b, by
            change e b ∈ Submodule.span ℂ (Set.range e)
            exact Submodule.subset_span ⟨b, rfl⟩⟩ : W)) (hell a)
  rw [hell_apply, LinearMap.comp_apply, Finsupp.lapply_apply]
  have hrepreq :
      hli.repr
          (⟨e b, by
            change e b ∈ Submodule.span ℂ (Set.range e)
            exact Submodule.subset_span ⟨b, rfl⟩⟩ : W) =
        Finsupp.single b (1 : ℂ) := by
    exact hli.repr_eq_single b
      (⟨e b, by
        change e b ∈ Submodule.span ℂ (Set.range e)
        exact Submodule.subset_span ⟨b, rfl⟩⟩ : W) rfl
  rw [hrepreq]
  by_cases h : a = b
  · subst h
    simp
  · simp [h]

/-- Selected source rows from a nonzero complex regular minor admit complex
Minkowski-dual vectors with Kronecker pairings. -/
theorem exists_sourceComplexMinkowski_dual_sourceRows_of_sourceComplexRegularMinor_ne_zero
    (d n : ℕ)
    {z : Fin n → Fin (d + 1) → ℂ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hminor : sourceComplexRegularMinor d n I J z ≠ 0) :
    ∃ u : Fin (min n (d + 1)) → Fin (d + 1) → ℂ,
      ∀ a b : Fin (min n (d + 1)),
        sourceComplexMinkowskiInner d (u a) (z (I b)) =
          if a = b then 1 else 0 :=
  exists_sourceComplexMinkowski_dual_family_of_linearIndependent
    d (min n (d + 1))
    (linearIndependent_complex_sourceRows_of_sourceComplexRegularMinor_ne_zero
      d n hminor)

/-- Pairing a complex linear combination of Minkowski-dual vectors against a
selected source row recovers the corresponding coefficient. -/
theorem sourceComplexMinkowskiInner_sum_smul_dual_left
    (d m : ℕ)
    {u e : Fin m → Fin (d + 1) → ℂ}
    (hdual :
      ∀ a b : Fin m,
        sourceComplexMinkowskiInner d (u a) (e b) =
          if a = b then 1 else 0)
    (coeff : Fin m → ℂ) (a : Fin m) :
    sourceComplexMinkowskiInner d
      (∑ b : Fin m, coeff b • u b) (e a) = coeff a := by
  let L : (Fin (d + 1) → ℂ) →ₗ[ℂ] ℂ := {
    toFun := fun v => sourceComplexMinkowskiInner d v (e a)
    map_add' := by
      intro v w
      exact sourceComplexMinkowskiInner_add_left d v w (e a)
    map_smul' := by
      intro c v
      exact sourceComplexMinkowskiInner_smul_left d c v (e a) }
  calc
    sourceComplexMinkowskiInner d
        (∑ b : Fin m, coeff b • u b) (e a)
        = ∑ b : Fin m,
            sourceComplexMinkowskiInner d (coeff b • u b) (e a) := by
          change L (∑ b : Fin m, coeff b • u b) =
            ∑ b : Fin m, L (coeff b • u b)
          rw [map_sum]
    _ = ∑ b : Fin m, coeff b * (if b = a then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro b _
          change L (coeff b • u b) = coeff b * (if b = a then 1 else 0)
          rw [L.map_smul]
          change coeff b • sourceComplexMinkowskiInner d (u b) (e a) =
            coeff b * (if b = a then 1 else 0)
          rw [hdual b a]
          simp [smul_eq_mul]
    _ = coeff a := by
          simp

/-- The selected-coordinate projection of the complex Gram differential has
exactly the symmetric selected-coordinate subspace as its range on any
nonzero complex selected-minor chart. -/
theorem sourceSelectedComplexGramCoord_comp_differential_range_eq_of_sourceComplexRegularMinor_ne_zero
    (d n : ℕ)
    {z : Fin n → Fin (d + 1) → ℂ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (_hJ : Function.Injective J)
    (hminor : sourceComplexRegularMinor d n I J z ≠ 0) :
    LinearMap.range
      ((sourceSelectedComplexGramCoord n (min n (d + 1)) I).comp
        (sourceComplexGramDifferential d n z)) =
      sourceSelectedComplexSymCoordSubspace n (min n (d + 1)) I := by
  let m := min n (d + 1)
  apply le_antisymm
  · rintro A ⟨h, rfl⟩
    exact sourceSelectedComplexGramCoord_differential_mem d n z h I
  · intro A hA
    rcases exists_sourceComplexMinkowski_dual_sourceRows_of_sourceComplexRegularMinor_ne_zero
        d n hminor with
      ⟨u, hdual⟩
    let selectedVar : Fin m → Fin (d + 1) → ℂ := fun a =>
      (1 / 2 : ℂ) •
        ∑ b : Fin m, A (I a) b • u b
    let residualVar : Fin n → Fin (d + 1) → ℂ := fun r =>
      ∑ a : Fin m,
        (A r a - sourceComplexMinkowskiInner d (z r) (selectedVar a)) • u a
    let h : Fin n → Fin (d + 1) → ℂ := fun r =>
      if hr : r ∈ Set.range I then
        selectedVar ((Equiv.ofInjective I hI).symm ⟨r, hr⟩)
      else residualVar r
    have hsym :
        ∀ a b : Fin m, A (I a) b = A (I b) a :=
      (mem_sourceSelectedComplexSymCoordSubspace).1 hA
    have h_at_selected : ∀ a : Fin m, h (I a) = selectedVar a := by
      intro a
      change (if hr : I a ∈ Set.range I then
          selectedVar ((Equiv.ofInjective I hI).symm ⟨I a, hr⟩)
        else residualVar (I a)) = selectedVar a
      rw [dif_pos ⟨a, rfl⟩]
      rw [Equiv.ofInjective_symm_apply hI a]
    have h_at_unselected :
        ∀ r : Fin n, r ∉ Set.range I → h r = residualVar r := by
      intro r hr
      change (if hr' : r ∈ Set.range I then
          selectedVar ((Equiv.ofInjective I hI).symm ⟨r, hr'⟩)
        else residualVar r) = residualVar r
      rw [dif_neg hr]
    have hselected_pair :
        ∀ a b : Fin m,
          sourceComplexMinkowskiInner d (selectedVar a) (z (I b)) =
            (1 / 2 : ℂ) * A (I a) b := by
      intro a b
      unfold selectedVar
      rw [sourceComplexMinkowskiInner_smul_left]
      rw [sourceComplexMinkowskiInner_sum_smul_dual_left d m hdual]
    have hresidual_pair :
        ∀ r : Fin n, ∀ a : Fin m,
          sourceComplexMinkowskiInner d (residualVar r) (z (I a)) =
            A r a - sourceComplexMinkowskiInner d (z r) (selectedVar a) := by
      intro r a
      unfold residualVar
      rw [sourceComplexMinkowskiInner_sum_smul_dual_left d m hdual]
    have h_selected :
        ∀ a b : Fin m,
          sourceComplexGramDifferential d n z h (I a) (I b) =
            A (I a) b := by
      intro a b
      rw [sourceComplexGramDifferential_apply_eq_complexInner]
      rw [h_at_selected a, h_at_selected b]
      rw [hselected_pair a b]
      rw [sourceComplexMinkowskiInner_comm d (z (I a)) (selectedVar b),
        hselected_pair b a]
      have hsymAB : A (I b) a = A (I a) b := hsym b a
      rw [hsymAB]
      ring
    have h_unselected :
        ∀ r : Fin n, r ∉ Set.range I →
          ∀ a : Fin m,
            sourceComplexGramDifferential d n z h r (I a) = A r a := by
      intro r hr a
      rw [sourceComplexGramDifferential_apply_eq_complexInner]
      rw [h_at_unselected r hr, h_at_selected a]
      rw [hresidual_pair r a]
      ring
    refine ⟨h, ?_⟩
    ext r a
    simp [sourceSelectedComplexGramCoord_apply]
    by_cases hr : r ∈ Set.range I
    · let c : Fin m := (Equiv.ofInjective I hI).symm ⟨r, hr⟩
      have hc : I c = r := by
        exact Equiv.apply_ofInjective_symm hI ⟨r, hr⟩
      calc
        sourceComplexGramDifferential d n z h r (I a)
            = sourceComplexGramDifferential d n z h (I c) (I a) := by
              rw [hc]
        _ = A (I c) a := h_selected c a
        _ = A r a := by rw [hc]
    · exact h_unselected r hr a

/-- The codomain-restricted selected complex Gram differential is surjective
onto the selected symmetric-coordinate subspace on any nonzero complex
selected-minor chart. -/
theorem sourceSelectedComplexGramDifferentialToSym_surjective_of_sourceComplexRegularMinor_ne_zero
    (d n : ℕ)
    {z : Fin n → Fin (d + 1) → ℂ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceComplexRegularMinor d n I J z ≠ 0) :
    Function.Surjective
      (sourceSelectedComplexGramDifferentialToSym d n
        (min n (d + 1)) z I) := by
  let m := min n (d + 1)
  intro A
  let L := sourceComplexGramDifferential d n z
  let P := sourceSelectedComplexGramCoord n m I
  have hA :
      (A : Fin n → Fin m → ℂ) ∈ LinearMap.range (P.comp L) := by
    rw [sourceSelectedComplexGramCoord_comp_differential_range_eq_of_sourceComplexRegularMinor_ne_zero
      d n hI hJ hminor]
    exact A.property
  rcases hA with ⟨h, hh⟩
  refine ⟨h, ?_⟩
  ext i a
  exact congrFun (congrFun hh i) a

/-- The selected complex Gram coordinate map has the local product chart
supplied by the finite-dimensional implicit-function theorem at any complex
nonzero-minor point. -/
theorem sourceSelectedComplexGramMap_implicit_chart_of_complex_nonzero_minor
    (d n : ℕ)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceComplexRegularMinor d n I J z0 ≠ 0) :
    ∃ e : OpenPartialHomeomorph
        (Fin n → Fin (d + 1) → ℂ)
        (sourceSelectedComplexSymCoordSubspace n (min n (d + 1)) I ×
          LinearMap.ker
            (sourceSelectedComplexGramDifferentialToSym d n
              (min n (d + 1)) z0 I)),
      z0 ∈ e.source ∧
      e z0 =
        (sourceSelectedComplexGramMap d n (min n (d + 1)) I z0, 0) ∧
      ∀ z ∈ e.source,
        (e z).1 = sourceSelectedComplexGramMap d n (min n (d + 1)) I z := by
  let m := min n (d + 1)
  let f := sourceSelectedComplexGramMap d n m I
  let f' : (Fin n → Fin (d + 1) → ℂ) →L[ℂ]
      sourceSelectedComplexSymCoordSubspace n m I :=
    LinearMap.toContinuousLinearMap
      (sourceSelectedComplexGramDifferentialToSym d n m z0 I)
  have hstrict : HasStrictFDerivAt f f' z0 := by
    simpa [f, f'] using
      sourceSelectedComplexGramMap_hasStrictFDerivAt d n m I z0
  have hsurj : f'.range = ⊤ := by
    exact LinearMap.range_eq_top.mpr
      (sourceSelectedComplexGramDifferentialToSym_surjective_of_sourceComplexRegularMinor_ne_zero
        d n hI hJ hminor)
  let e := hstrict.implicitToOpenPartialHomeomorph f f' hsurj
  refine ⟨e, ?_, ?_, ?_⟩
  · exact hstrict.mem_implicitToOpenPartialHomeomorph_source hsurj
  · simpa [e, f, f'] using hstrict.implicitToOpenPartialHomeomorph_self hsurj
  · intro z hz
    simpa [e, f, f'] using
      hstrict.implicitToOpenPartialHomeomorph_fst hsurj z

/-- A nonzero complex maximal source coordinate minor selects rows whose span is
the whole complex source configuration span. -/
theorem span_sourceComplexRows_eq_sourceComplexConfigurationSpan_of_sourceComplexRegularMinor_ne_zero
    (d n : ℕ)
    {z : Fin n → Fin (d + 1) → ℂ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hminor : sourceComplexRegularMinor d n I J z ≠ 0) :
    Submodule.span ℂ
        (Set.range (fun a : Fin (min n (d + 1)) => z (I a))) =
      sourceComplexConfigurationSpan d n z := by
  let T : Submodule ℂ (Fin (d + 1) → ℂ) :=
    Submodule.span ℂ
      (Set.range (fun a : Fin (min n (d + 1)) => z (I a)))
  let S : Submodule ℂ (Fin (d + 1) → ℂ) := sourceComplexConfigurationSpan d n z
  have hzI : LinearIndependent ℂ
      (fun a : Fin (min n (d + 1)) => z (I a)) :=
    linearIndependent_complex_sourceRows_of_sourceComplexRegularMinor_ne_zero
      d n hminor
  have hTS : T ≤ S := by
    have hrange : Set.range
        (fun a : Fin (min n (d + 1)) => z (I a)) ⊆ Set.range z := by
      rintro _ ⟨a, rfl⟩
      exact ⟨I a, rfl⟩
    simpa [T, S, sourceComplexConfigurationSpan] using
      (Submodule.span_mono (R := ℂ) hrange)
  have hTfin : Module.finrank ℂ T = min n (d + 1) := by
    have hspan := finrank_span_eq_card (R := ℂ)
      (b := fun a : Fin (min n (d + 1)) => z (I a)) hzI
    simpa [T, Fintype.card_fin] using hspan
  have hSfin : Module.finrank ℂ S = min n (d + 1) := by
    have hzIS : LinearIndependent ℂ
        (fun a : Fin (min n (d + 1)) =>
          (⟨z (I a), by
            change z (I a) ∈ Submodule.span ℂ (Set.range z)
            exact Submodule.subset_span ⟨I a, rfl⟩⟩ : S)) := by
      apply LinearIndependent.of_comp S.subtype
      simpa [Function.comp_def, S] using hzI
    have hlower : min n (d + 1) ≤ Module.finrank ℂ S := by
      simpa using hzIS.fintype_card_le_finrank
    have hupper_n : Module.finrank ℂ S ≤ n := by
      simpa [S, sourceComplexConfigurationSpan] using
        (finrank_range_le_card (R := ℂ) (b := z))
    have hupper_d : Module.finrank ℂ S ≤ d + 1 := by
      have h := Submodule.finrank_le S
      simpa [Module.finrank_fin_fun] using h
    have hupper : Module.finrank ℂ S ≤ min n (d + 1) :=
      le_min hupper_n hupper_d
    exact le_antisymm hupper hlower
  exact Submodule.eq_of_le_of_finrank_eq hTS (by rw [hTfin, hSfin])

/-- In the full-spacetime case, a nonzero complex selected minor makes the
selected rows span the whole complex source spacetime. -/
theorem sourceSelectedComplexRows_span_top_of_sourceComplexRegularMinor_ne_zero
    (d n : ℕ)
    {z : Fin n → Fin (d + 1) → ℂ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hminor : sourceComplexRegularMinor d n I J z ≠ 0)
    (hD : d + 1 ≤ n) :
    Submodule.span ℂ
        (Set.range (fun a : Fin (min n (d + 1)) => z (I a))) = ⊤ := by
  have hli :=
    linearIndependent_complex_sourceRows_of_sourceComplexRegularMinor_ne_zero
      d n hminor
  have hcard :
      Fintype.card (Fin (min n (d + 1))) =
        Module.finrank ℂ (Fin (d + 1) → ℂ) := by
    simp [Nat.min_eq_right hD]
  exact hli.span_eq_top_of_card_eq_finrank' hcard

/-- Coefficients expressing every complex source row in the selected-row span
supplied by a nonzero complex regular minor. -/
theorem sourceComplexRows_coefficients_of_sourceComplexRegularMinor_ne_zero
    (d n : ℕ)
    {z : Fin n → Fin (d + 1) → ℂ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hminor : sourceComplexRegularMinor d n I J z ≠ 0) :
    ∃ c : Fin n → Fin (min n (d + 1)) → ℂ,
      ∀ r : Fin n,
        z r = ∑ a : Fin (min n (d + 1)), c r a • z (I a) := by
  let m := min n (d + 1)
  have hspan :=
    span_sourceComplexRows_eq_sourceComplexConfigurationSpan_of_sourceComplexRegularMinor_ne_zero
      d n hminor
  have hexists : ∀ r : Fin n,
      ∃ c : Fin m → ℂ,
        ∑ a : Fin m, c a • z (I a) = z r := by
    intro r
    have hzmem : z r ∈
        Submodule.span ℂ (Set.range (fun a : Fin m => z (I a))) := by
      rw [hspan]
      change z r ∈ Submodule.span ℂ (Set.range z)
      exact Submodule.subset_span ⟨r, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun (R := ℂ)
      (v := fun a : Fin m => z (I a))).1 hzmem
  choose c hc using hexists
  exact ⟨c, fun r => (hc r).symm⟩

/-- If the selected rows of the right-hand complex source point span spacetime,
then selected coordinates equal to those of a left nonzero-minor point determine
the full complex source Gram matrix. -/
theorem sourceSelectedComplexGramCoord_eq_fullGram_eq_of_leftMinor_rightSpanTop
    (d n : ℕ)
    {x y : Fin n → Fin (d + 1) → ℂ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hminor_x : sourceComplexRegularMinor d n I J x ≠ 0)
    (hspan_y :
      Submodule.span ℂ
        (Set.range (fun a : Fin (min n (d + 1)) => y (I a))) = ⊤)
    (hsel :
      sourceSelectedComplexGramCoord n (min n (d + 1)) I
          (sourceMinkowskiGram d n x) =
        sourceSelectedComplexGramCoord n (min n (d + 1)) I
          (sourceMinkowskiGram d n y)) :
    sourceMinkowskiGram d n x = sourceMinkowskiGram d n y := by
  ext r s
  let m := min n (d + 1)
  rcases sourceComplexRows_coefficients_of_sourceComplexRegularMinor_ne_zero
      d n hminor_x with
    ⟨c, hc⟩
  let yApprox : Fin n → Fin (d + 1) → ℂ := fun q =>
    ∑ a : Fin m, c q a • y (I a)
  have hy_eq : ∀ q : Fin n, y q = yApprox q := by
    intro q
    have hzero : y q - yApprox q = 0 := by
      apply sourceComplexMinkowskiInner_eq_zero_of_orthogonal_spanning_family
        d m hspan_y
      intro b
      rw [sourceComplexMinkowskiInner_sub_left]
      have hsel_qb := congrFun (congrFun hsel q) b
      change sourceMinkowskiGram d n x q (I b) =
        sourceMinkowskiGram d n y q (I b) at hsel_qb
      have hx_expand :
          sourceComplexMinkowskiInner d (x q) (x (I b)) =
            ∑ a : Fin m,
              c q a *
                sourceComplexMinkowskiInner d (x (I a)) (x (I b)) := by
        rw [hc q]
        rw [sourceComplexMinkowskiInner_sum_smul_left]
      have hyApprox_expand :
          sourceComplexMinkowskiInner d (yApprox q) (y (I b)) =
            ∑ a : Fin m,
              c q a *
                sourceComplexMinkowskiInner d (y (I a)) (y (I b)) := by
        unfold yApprox
        rw [sourceComplexMinkowskiInner_sum_smul_left]
      have hblock : ∀ a : Fin m,
          sourceComplexMinkowskiInner d (y (I a)) (y (I b)) =
            sourceComplexMinkowskiInner d (x (I a)) (x (I b)) := by
        intro a
        have h := congrFun (congrFun hsel (I a)) b
        change sourceMinkowskiGram d n x (I a) (I b) =
          sourceMinkowskiGram d n y (I a) (I b) at h
        simpa [sourceMinkowskiGram_apply_eq_complexInner] using h.symm
      have hyApprox_eq_x :
          sourceComplexMinkowskiInner d (yApprox q) (y (I b)) =
            sourceComplexMinkowskiInner d (x q) (x (I b)) := by
        rw [hyApprox_expand, hx_expand]
        apply Finset.sum_congr rfl
        intro a _
        rw [hblock a]
      have hy_eq_x :
          sourceComplexMinkowskiInner d (y q) (y (I b)) =
            sourceComplexMinkowskiInner d (x q) (x (I b)) := by
        simpa [sourceMinkowskiGram_apply_eq_complexInner] using hsel_qb.symm
      rw [hy_eq_x, hyApprox_eq_x]
      simp
    exact sub_eq_zero.mp hzero
  have hx_expand_rs :
      sourceMinkowskiGram d n x r s =
        ∑ a : Fin m,
          c s a * sourceMinkowskiGram d n x r (I a) := by
    rw [sourceMinkowskiGram_apply_eq_complexInner]
    rw [hc s]
    rw [sourceComplexMinkowskiInner_sum_smul_right]
    rfl
  have hy_expand_rs :
      sourceMinkowskiGram d n y r s =
        ∑ a : Fin m,
          c s a * sourceMinkowskiGram d n y r (I a) := by
    rw [sourceMinkowskiGram_apply_eq_complexInner]
    rw [hy_eq s]
    unfold yApprox
    rw [sourceComplexMinkowskiInner_sum_smul_right]
    rfl
  calc
    sourceMinkowskiGram d n x r s
        = ∑ a : Fin m,
            c s a * sourceMinkowskiGram d n x r (I a) := hx_expand_rs
    _ = ∑ a : Fin m,
            c s a * sourceMinkowskiGram d n y r (I a) := by
          apply Finset.sum_congr rfl
          intro a _
          have h := congrFun (congrFun hsel r) a
          simpa [sourceSelectedComplexGramCoord_apply] using
            congrArg (fun z => c s a * z) h
    _ = sourceMinkowskiGram d n y r s := hy_expand_rs.symm

/-- On a fixed nonzero complex selected-minor chart, the selected complex Gram
coordinates determine the full complex source Gram matrix. -/
theorem sourceSelectedComplexGramCoord_eq_fullGram_eq_of_sourceComplexRegularMinor_ne_zero
    (d n : ℕ)
    {x y : Fin n → Fin (d + 1) → ℂ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hminor_x : sourceComplexRegularMinor d n I J x ≠ 0)
    (hminor_y : sourceComplexRegularMinor d n I J y ≠ 0)
    (hsel :
      sourceSelectedComplexGramCoord n (min n (d + 1)) I
          (sourceMinkowskiGram d n x) =
        sourceSelectedComplexGramCoord n (min n (d + 1)) I
          (sourceMinkowskiGram d n y)) :
    sourceMinkowskiGram d n x = sourceMinkowskiGram d n y := by
  by_cases hn : n ≤ d + 1
  · ext r s
    have hsurj := sourceSelectedIndex_surjective_of_le d n hI hn
    rcases hsurj s with ⟨a, rfl⟩
    have h := congrFun (congrFun hsel r) a
    simpa [sourceSelectedComplexGramCoord_apply] using h
  · have hD : d + 1 ≤ n := by omega
    have hspan_y :
        Submodule.span ℂ
          (Set.range (fun a : Fin (min n (d + 1)) => y (I a))) = ⊤ :=
      sourceSelectedComplexRows_span_top_of_sourceComplexRegularMinor_ne_zero
        d n hminor_y hD
    exact
      sourceSelectedComplexGramCoord_eq_fullGram_eq_of_leftMinor_rightSpanTop
        d n hminor_x hspan_y hsel

/-- In the selected-coordinate complex implicit chart, the full complex source
Gram map is constant on local vertical fibers after shrinking to the same
nonzero complex-minor chart. -/
theorem sourceComplexGramMap_constant_on_selectedVerticalFibers
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceRegularMinor d n I J x0 ≠ 0) :
    ∃ e : OpenPartialHomeomorph
        (Fin n → Fin (d + 1) → ℂ)
        (sourceSelectedComplexSymCoordSubspace n (min n (d + 1)) I ×
          LinearMap.ker
            (sourceSelectedComplexGramDifferentialToSym d n
              (min n (d + 1)) (realEmbed x0) I)),
      realEmbed x0 ∈ e.source ∧
      ∃ U : Set (Fin n → Fin (d + 1) → ℂ),
        IsOpen U ∧ realEmbed x0 ∈ U ∧ U ⊆ e.source ∧
        (∀ z ∈ U, sourceComplexRegularMinor d n I J z ≠ 0) ∧
        ∀ y ∈ U, ∀ z ∈ U,
          (e y).1 = (e z).1 →
          sourceMinkowskiGram d n y = sourceMinkowskiGram d n z := by
  rcases sourceSelectedComplexGramMap_implicit_chart_of_nonzero_minor
      d n hI hJ hminor with
    ⟨e, hx0e, _hebase, hefst⟩
  have hminorC :
      sourceComplexRegularMinor d n I J (realEmbed x0) ≠ 0 := by
    rw [sourceComplexRegularMinor_realEmbed]
    exact (Complex.ofReal_ne_zero).2 hminor
  let U : Set (Fin n → Fin (d + 1) → ℂ) :=
    e.source ∩ {z | sourceComplexRegularMinor d n I J z ≠ 0}
  refine ⟨e, hx0e, U, ?_, ?_, ?_, ?_, ?_⟩
  · exact e.open_source.inter
      (isOpen_ne_fun (continuous_sourceComplexRegularMinor d n I J)
        continuous_const)
  · exact ⟨hx0e, hminorC⟩
  · intro z hz
    exact hz.1
  · intro z hz
    exact hz.2
  · intro y hy z hz hyz
    have hselSubtype :
        sourceSelectedComplexGramMap d n (min n (d + 1)) I y =
          sourceSelectedComplexGramMap d n (min n (d + 1)) I z := by
      rw [← hefst y hy.1, ← hefst z hz.1, hyz]
    have hsel :
        sourceSelectedComplexGramCoord n (min n (d + 1)) I
            (sourceMinkowskiGram d n y) =
          sourceSelectedComplexGramCoord n (min n (d + 1)) I
            (sourceMinkowskiGram d n z) := by
      exact congrArg Subtype.val hselSubtype
    exact
      sourceSelectedComplexGramCoord_eq_fullGram_eq_of_sourceComplexRegularMinor_ne_zero
        d n hI hy.2 hz.2 hsel

/-- In the full-spacetime case, equality of selected complex Gram coordinates
with a regular selected-minor point transfers full span to the arbitrary
right-hand selected rows. -/
theorem sourceSelectedComplexRows_span_top_of_selectedComplexGramCoord_eq_regular
    (d n : ℕ)
    {x y : Fin n → Fin (d + 1) → ℂ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hminor_x : sourceComplexRegularMinor d n I J x ≠ 0)
    (hsel :
      sourceSelectedComplexGramCoord n (min n (d + 1)) I
          (sourceMinkowskiGram d n x) =
        sourceSelectedComplexGramCoord n (min n (d + 1)) I
          (sourceMinkowskiGram d n y))
    (hD : d + 1 ≤ n) :
    Submodule.span ℂ
      (Set.range (fun a : Fin (min n (d + 1)) => y (I a))) = ⊤ := by
  let m := min n (d + 1)
  have hspan_x : Submodule.span ℂ
      (Set.range (fun a : Fin m => x (I a))) = ⊤ := by
    simpa [m] using
      sourceSelectedComplexRows_span_top_of_sourceComplexRegularMinor_ne_zero
        d n hminor_x hD
  have hli_x : LinearIndependent ℂ (fun a : Fin m => x (I a)) := by
    simpa [m] using
      linearIndependent_complex_sourceRows_of_sourceComplexRegularMinor_ne_zero
        d n hminor_x
  have hli_y : LinearIndependent ℂ (fun a : Fin m => y (I a)) := by
    rw [Fintype.linearIndependent_iff]
    intro coeff hsum a
    have hxcombo_zero :
        (∑ c : Fin m, coeff c • x (I c)) = 0 := by
      apply sourceComplexMinkowskiInner_eq_zero_of_orthogonal_spanning_family
        d m hspan_x
      intro b
      have hyorth :
          sourceComplexMinkowskiInner d
            (∑ c : Fin m, coeff c • y (I c)) (y (I b)) = 0 := by
        rw [hsum]
        unfold sourceComplexMinkowskiInner
        simp
      calc
        sourceComplexMinkowskiInner d
            (∑ c : Fin m, coeff c • x (I c)) (x (I b))
            = ∑ c : Fin m,
                coeff c *
                  sourceComplexMinkowskiInner d (x (I c)) (x (I b)) := by
              rw [sourceComplexMinkowskiInner_sum_smul_left]
        _ = ∑ c : Fin m,
                coeff c *
                  sourceComplexMinkowskiInner d (y (I c)) (y (I b)) := by
              apply Finset.sum_congr rfl
              intro c _
              have h := congrFun (congrFun hsel (I c)) b
              change sourceMinkowskiGram d n x (I c) (I b) =
                sourceMinkowskiGram d n y (I c) (I b) at h
              simpa [sourceMinkowskiGram_apply_eq_complexInner] using
                congrArg (fun z => coeff c * z) h
        _ = sourceComplexMinkowskiInner d
            (∑ c : Fin m, coeff c • y (I c)) (y (I b)) := by
              rw [sourceComplexMinkowskiInner_sum_smul_left]
        _ = 0 := hyorth
    exact (Fintype.linearIndependent_iff.mp hli_x coeff hxcombo_zero) a
  have hcard :
      Fintype.card (Fin m) =
        Module.finrank ℂ (Fin (d + 1) → ℂ) := by
    simp [m, Nat.min_eq_right hD]
  exact hli_y.span_eq_top_of_card_eq_finrank' hcard

/-- Selected coordinates of one regular complex selected-minor source point
determine any Gram matrix in the complex source Gram variety. -/
theorem sourceSelectedComplexGramCoord_eq_fullGram_eq_of_sourceComplexRegularMinor_ne_zero_of_mem_variety
    (d n : ℕ)
    {x : Fin n → Fin (d + 1) → ℂ}
    {G : Fin n → Fin n → ℂ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hminor_x : sourceComplexRegularMinor d n I J x ≠ 0)
    (hG : G ∈ sourceComplexGramVariety d n)
    (hsel :
      sourceSelectedComplexGramCoord n (min n (d + 1)) I
          (sourceMinkowskiGram d n x) =
        sourceSelectedComplexGramCoord n (min n (d + 1)) I G) :
    sourceMinkowskiGram d n x = G := by
  rcases hG with ⟨y, rfl⟩
  by_cases hn : n ≤ d + 1
  · ext r s
    have hsurj := sourceSelectedIndex_surjective_of_le d n hI hn
    rcases hsurj s with ⟨a, rfl⟩
    have h := congrFun (congrFun hsel r) a
    simpa [sourceSelectedComplexGramCoord_apply] using h
  · have hD : d + 1 ≤ n := by omega
    have hspan_y :
        Submodule.span ℂ
          (Set.range (fun a : Fin (min n (d + 1)) => y (I a))) = ⊤ :=
      sourceSelectedComplexRows_span_top_of_selectedComplexGramCoord_eq_regular
        d n hminor_x hsel hD
    exact
      sourceSelectedComplexGramCoord_eq_fullGram_eq_of_leftMinor_rightSpanTop
        d n hminor_x hspan_y hsel

/-- Inside any open complex source neighborhood of a complex regular point,
the complex source Gram map sends a smaller complex regular source patch to a
relatively open neighborhood in the complex source Gram variety. -/
theorem sourceComplexGramMap_localRelOpenImage_in_open_of_complexRegular
    (d n : ℕ)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (hreg : SourceComplexGramRegularAt d n z0)
    {V : Set (Fin n → Fin (d + 1) → ℂ)}
    (hV_open : IsOpen V)
    (hz0V : z0 ∈ V) :
    ∃ U : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen U ∧ z0 ∈ U ∧ U ⊆ V ∧
      ∃ O : Set (Fin n → Fin n → ℂ),
        sourceMinkowskiGram d n z0 ∈ O ∧
        IsRelOpenInSourceComplexGramVariety d n O ∧
        O ⊆ sourceMinkowskiGram d n '' U ∧
        ∀ G ∈ O, ∃ z ∈ U,
          sourceMinkowskiGram d n z = G := by
  rcases exists_nonzero_minor_of_sourceComplexGramRegularAt d n hreg with
    ⟨I, hI, J, hJ, hminor⟩
  rcases sourceSelectedComplexGramMap_implicit_chart_of_complex_nonzero_minor
      d n hI hJ hminor with
    ⟨e, hz0e, _hebase, hefst⟩
  let U : Set (Fin n → Fin (d + 1) → ℂ) :=
    (e.source ∩ {z | sourceComplexRegularMinor d n I J z ≠ 0}) ∩ V
  have hUopen : IsOpen U := by
    exact (e.open_source.inter
      (isOpen_ne_fun (continuous_sourceComplexRegularMinor d n I J)
        continuous_const)).inter hV_open
  have hz0U : z0 ∈ U := ⟨⟨hz0e, hminor⟩, hz0V⟩
  have hUsub : U ⊆ e.source := fun _ hz => hz.1.1
  have hUV : U ⊆ V := fun _ hz => hz.2
  have hUminor :
      ∀ z ∈ U, sourceComplexRegularMinor d n I J z ≠ 0 :=
    fun _ hz => hz.1.2
  let m := min n (d + 1)
  let S := sourceSelectedComplexSymCoordSubspace n m I
  let K := LinearMap.ker
    (sourceSelectedComplexGramDifferentialToSym d n m z0 I)
  let T : Set (S × K) := e '' U
  let R : Set S := Prod.fst '' T
  have hTopen : IsOpen T := by
    exact e.isOpen_image_of_subset_source hUopen hUsub
  have hRopen : IsOpen R := by
    exact isOpenMap_fst T hTopen
  rcases isOpen_induced_iff.mp hRopen with
    ⟨R0, hR0open, hR0pre⟩
  let E0 : Set (Fin n → Fin n → ℂ) :=
    {G | sourceSelectedComplexGramCoord n m I G ∈ R0}
  let O : Set (Fin n → Fin n → ℂ) :=
    E0 ∩ sourceComplexGramVariety d n
  have hPcont : Continuous (sourceSelectedComplexGramCoord n m I) :=
    LinearMap.continuous_of_finiteDimensional
      (sourceSelectedComplexGramCoord n m I)
  have hE0open : IsOpen E0 := by
    exact hR0open.preimage hPcont
  have hbaseR :
      sourceSelectedComplexGramMap d n m I z0 ∈ R := by
    refine ⟨e z0, ?_, ?_⟩
    · exact ⟨z0, hz0U, rfl⟩
    · exact hefst z0 hz0e
  have hbaseR0 :
      (sourceSelectedComplexGramMap d n m I z0 :
          Fin n → Fin m → ℂ) ∈ R0 := by
    have hpre :
        sourceSelectedComplexGramMap d n m I z0 ∈
          Subtype.val ⁻¹' R0 := by
      rw [hR0pre]
      exact hbaseR
    exact hpre
  have hbaseO :
      sourceMinkowskiGram d n z0 ∈ O := by
    refine ⟨?_, ?_⟩
    · exact hbaseR0
    · exact ⟨z0, rfl⟩
  have hOcomplex :
      ∀ G ∈ O, ∃ z ∈ U,
        sourceComplexRegularMinor d n I J z ≠ 0 ∧
          sourceMinkowskiGram d n z = G := by
    intro G hGO
    rcases hGO with ⟨hGE0, hGvar⟩
    have hGsym : ∀ i j : Fin n, G i j = G j i := by
      rcases hGvar with ⟨z, rfl⟩
      intro i j
      exact sourceMinkowskiGram_symm d n z i j
    let A : S :=
      ⟨sourceSelectedComplexGramCoord n m I G, by
        intro a b
        change G (I a) (I b) = G (I b) (I a)
        exact hGsym (I a) (I b)⟩
    have hAR : A ∈ R := by
      have hpre : A ∈ Subtype.val ⁻¹' R0 := hGE0
      rw [hR0pre] at hpre
      exact hpre
    rcases hAR with ⟨p, hpT, hpA⟩
    rcases hpT with ⟨u, huU, rfl⟩
    have hselSubtype :
        sourceSelectedComplexGramMap d n m I u = A := by
      exact (hefst u (hUsub huU)).symm.trans hpA
    have hsel :
        sourceSelectedComplexGramCoord n m I
            (sourceMinkowskiGram d n u) =
          sourceSelectedComplexGramCoord n m I G := by
      exact congrArg Subtype.val hselSubtype
    have hGram :
        sourceMinkowskiGram d n u = G :=
      sourceSelectedComplexGramCoord_eq_fullGram_eq_of_sourceComplexRegularMinor_ne_zero_of_mem_variety
        d n hI (hUminor u huU) hGvar hsel
    exact ⟨u, huU, hUminor u huU, hGram⟩
  have hOsubset :
      O ⊆ sourceMinkowskiGram d n '' U := by
    intro G hG
    rcases hOcomplex G hG with ⟨u, huU, _hminoru, hGram⟩
    exact ⟨u, huU, hGram⟩
  refine ⟨U, hUopen, hz0U, hUV, O, hbaseO, ?_, hOsubset, ?_⟩
  · exact ⟨E0, hE0open, rfl⟩
  · intro G hG
    rcases hOcomplex G hG with ⟨u, huU, _hminoru, hGram⟩
    exact ⟨u, huU, hGram⟩

/-- Inside any open complex source neighborhood of a real regular point, the
complex source Gram map sends a smaller complex regular source patch to a
relatively open neighborhood in the complex source Gram variety. -/
theorem sourceComplexGramMap_localRelOpenImage_in_open_of_realRegular
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (hreg : SourceGramRegularAt d n x0)
    {V : Set (Fin n → Fin (d + 1) → ℂ)}
    (hV_open : IsOpen V)
    (hx0V : realEmbed x0 ∈ V) :
    ∃ U : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen U ∧ realEmbed x0 ∈ U ∧ U ⊆ V ∧
      ∃ O : Set (Fin n → Fin n → ℂ),
        sourceMinkowskiGram d n (realEmbed x0) ∈ O ∧
        IsRelOpenInSourceComplexGramVariety d n O ∧
        O ⊆ sourceMinkowskiGram d n '' U ∧
        ∀ G ∈ O, ∃ z ∈ U,
          sourceMinkowskiGram d n z = G := by
  rcases exists_nonzero_minor_of_sourceGramRegularAt d n hreg with
    ⟨I, hI, J, hJ, hminor⟩
  rcases sourceSelectedComplexGramMap_implicit_chart_of_nonzero_minor
      d n hI hJ hminor with
    ⟨e, hx0e, _hebase, hefst⟩
  have hminorC :
      sourceComplexRegularMinor d n I J (realEmbed x0) ≠ 0 := by
    rw [sourceComplexRegularMinor_realEmbed]
    exact (Complex.ofReal_ne_zero).2 hminor
  let U : Set (Fin n → Fin (d + 1) → ℂ) :=
    (e.source ∩ {z | sourceComplexRegularMinor d n I J z ≠ 0}) ∩ V
  have hUopen : IsOpen U := by
    exact (e.open_source.inter
      (isOpen_ne_fun (continuous_sourceComplexRegularMinor d n I J)
        continuous_const)).inter hV_open
  have hx0U : realEmbed x0 ∈ U := ⟨⟨hx0e, hminorC⟩, hx0V⟩
  have hUsub : U ⊆ e.source := fun _ hz => hz.1.1
  have hUV : U ⊆ V := fun _ hz => hz.2
  have hUminor :
      ∀ z ∈ U, sourceComplexRegularMinor d n I J z ≠ 0 :=
    fun _ hz => hz.1.2
  let m := min n (d + 1)
  let S := sourceSelectedComplexSymCoordSubspace n m I
  let K := LinearMap.ker
    (sourceSelectedComplexGramDifferentialToSym d n m (realEmbed x0) I)
  let T : Set (S × K) := e '' U
  let R : Set S := Prod.fst '' T
  have hTopen : IsOpen T := by
    exact e.isOpen_image_of_subset_source hUopen hUsub
  have hRopen : IsOpen R := by
    exact isOpenMap_fst T hTopen
  rcases isOpen_induced_iff.mp hRopen with
    ⟨R0, hR0open, hR0pre⟩
  let E0 : Set (Fin n → Fin n → ℂ) :=
    {G | sourceSelectedComplexGramCoord n m I G ∈ R0}
  let O : Set (Fin n → Fin n → ℂ) :=
    E0 ∩ sourceComplexGramVariety d n
  have hPcont : Continuous (sourceSelectedComplexGramCoord n m I) :=
    LinearMap.continuous_of_finiteDimensional
      (sourceSelectedComplexGramCoord n m I)
  have hE0open : IsOpen E0 := by
    exact hR0open.preimage hPcont
  have hbaseR :
      sourceSelectedComplexGramMap d n m I (realEmbed x0) ∈ R := by
    refine ⟨e (realEmbed x0), ?_, ?_⟩
    · exact ⟨realEmbed x0, hx0U, rfl⟩
    · exact hefst (realEmbed x0) hx0e
  have hbaseR0 :
      (sourceSelectedComplexGramMap d n m I (realEmbed x0) :
          Fin n → Fin m → ℂ) ∈ R0 := by
    have hpre :
        sourceSelectedComplexGramMap d n m I (realEmbed x0) ∈
          Subtype.val ⁻¹' R0 := by
      rw [hR0pre]
      exact hbaseR
    exact hpre
  have hbaseO :
      sourceMinkowskiGram d n (realEmbed x0) ∈ O := by
    refine ⟨?_, ?_⟩
    · exact hbaseR0
    · exact ⟨realEmbed x0, rfl⟩
  have hOcomplex :
      ∀ G ∈ O, ∃ z ∈ U,
        sourceComplexRegularMinor d n I J z ≠ 0 ∧
          sourceMinkowskiGram d n z = G := by
    intro G hGO
    rcases hGO with ⟨hGE0, hGvar⟩
    have hGsym : ∀ i j : Fin n, G i j = G j i := by
      rcases hGvar with ⟨z, rfl⟩
      intro i j
      exact sourceMinkowskiGram_symm d n z i j
    let A : S :=
      ⟨sourceSelectedComplexGramCoord n m I G, by
        intro a b
        change G (I a) (I b) = G (I b) (I a)
        exact hGsym (I a) (I b)⟩
    have hAR : A ∈ R := by
      have hpre : A ∈ Subtype.val ⁻¹' R0 := hGE0
      rw [hR0pre] at hpre
      exact hpre
    rcases hAR with ⟨p, hpT, hpA⟩
    rcases hpT with ⟨u, huU, rfl⟩
    have hselSubtype :
        sourceSelectedComplexGramMap d n m I u = A := by
      exact (hefst u (hUsub huU)).symm.trans hpA
    have hsel :
        sourceSelectedComplexGramCoord n m I
            (sourceMinkowskiGram d n u) =
          sourceSelectedComplexGramCoord n m I G := by
      exact congrArg Subtype.val hselSubtype
    have hGram :
        sourceMinkowskiGram d n u = G :=
      sourceSelectedComplexGramCoord_eq_fullGram_eq_of_sourceComplexRegularMinor_ne_zero_of_mem_variety
        d n hI (hUminor u huU) hGvar hsel
    exact ⟨u, huU, hUminor u huU, hGram⟩
  have hOsubset :
      O ⊆ sourceMinkowskiGram d n '' U := by
    intro G hG
    rcases hOcomplex G hG with ⟨u, huU, _hminoru, hGram⟩
    exact ⟨u, huU, hGram⟩
  refine ⟨U, hUopen, hx0U, hUV, O, hbaseO, ?_, hOsubset, ?_⟩
  · exact ⟨E0, hE0open, rfl⟩
  · intro G hG
    rcases hOcomplex G hG with ⟨u, huU, hminoru, hGram⟩
    exact ⟨u, huU, hGram⟩

/-- Coordinate keys for the selected symmetric-coordinate subspace.  We keep
all coordinates whose row is not selected, and on selected rows keep only the
lower-triangular part of the selected block. -/
def sourceSelectedSymCoordKey
    (n m : ℕ) (I : Fin m → Fin n) : Type :=
  {q : Fin n × Fin m //
    ∀ c : Fin m, q.1 = I c → q.2.val ≤ c.val}

instance sourceSelectedSymCoordKey.fintype
    (n m : ℕ) (I : Fin m → Fin n) :
    Fintype (sourceSelectedSymCoordKey n m I) := by
  classical
  let p : Fin n × Fin m → Prop :=
    fun q => ∀ c : Fin m, q.1 = I c → q.2.val ≤ c.val
  change Fintype {q : Fin n × Fin m // p q}
  infer_instance

/-- Evaluation of selected complex symmetric coordinates on the kept coordinate
keys. -/
noncomputable def sourceSelectedComplexSymCoordKeyEvalCLM
    (n m : ℕ) (I : Fin m → Fin n) :
    sourceSelectedComplexSymCoordSubspace n m I →L[ℂ]
      (sourceSelectedSymCoordKey n m I → ℂ) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun A q => (A : Fin n → Fin m → ℂ) q.val.1 q.val.2
    map_add' := by
      intro A B
      ext q
      rfl
    map_smul' := by
      intro c A
      ext q
      rfl }

/-- Evaluation of selected real symmetric coordinates on the kept coordinate
keys. -/
noncomputable def sourceSelectedRealSymCoordKeyEvalCLM
    (n m : ℕ) (I : Fin m → Fin n) :
    sourceSelectedSymCoordSubspace n m I →L[ℝ]
      (sourceSelectedSymCoordKey n m I → ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun A q => (A : Fin n → Fin m → ℝ) q.val.1 q.val.2
    map_add' := by
      intro A B
      ext q
      rfl
    map_smul' := by
      intro c A
      ext q
      rfl }

/-- Componentwise complexification from the real selected symmetric-coordinate
subspace to the complex selected symmetric-coordinate subspace. -/
def sourceSelectedSymCoordRealComplexify
    (n m : ℕ) (I : Fin m → Fin n) :
    sourceSelectedSymCoordSubspace n m I →ₗ[ℝ]
      sourceSelectedComplexSymCoordSubspace n m I where
  toFun := fun A =>
    ⟨fun i a => ((A : Fin n → Fin m → ℝ) i a : ℂ), by
      intro a b
      change ((A : Fin n → Fin m → ℝ) (I a) b : ℂ) =
        ((A : Fin n → Fin m → ℝ) (I b) a : ℂ)
      exact_mod_cast A.property a b⟩
  map_add' := by
    intro A B
    ext i a
    simp
  map_smul' := by
    intro c A
    ext i a
    change (((c • A : sourceSelectedSymCoordSubspace n m I) :
          Fin n → Fin m → ℝ) i a : ℂ) =
      c • (((A : Fin n → Fin m → ℝ) i a : ℂ))
    simp [smul_eq_mul]

@[simp]
theorem sourceSelectedSymCoordRealComplexify_apply
    (n m : ℕ) (I : Fin m → Fin n)
    (A : sourceSelectedSymCoordSubspace n m I)
    (i : Fin n) (a : Fin m) :
    (sourceSelectedSymCoordRealComplexify n m I A :
        Fin n → Fin m → ℂ) i a =
      ((A : Fin n → Fin m → ℝ) i a : ℂ) :=
  rfl

/-- The kept-coordinate evaluation maps commute with componentwise
complexification. -/
theorem sourceSelectedComplexSymCoordKeyEvalCLM_real_slice
    (n m : ℕ) (I : Fin m → Fin n)
    (A : sourceSelectedSymCoordSubspace n m I) :
    sourceSelectedComplexSymCoordKeyEvalCLM n m I
      (sourceSelectedSymCoordRealComplexify n m I A) =
      fun q => ((sourceSelectedRealSymCoordKeyEvalCLM n m I A q : ℝ) : ℂ) := by
  ext q
  rfl

/-- Reconstruct the full selected-coordinate array from kept coordinate keys,
using selected-block symmetry for the omitted upper-triangular coordinates. -/
private noncomputable def sourceSelectedSymCoordKeyReconstructScalar
    (n m : ℕ) {I : Fin m → Fin n}
    (hI : Function.Injective I)
    (𝕜 : Type*) [Zero 𝕜]
    (f : sourceSelectedSymCoordKey n m I → 𝕜) :
    Fin n → Fin m → 𝕜 :=
  fun i a =>
    if hi : i ∈ Set.range I then
      let c := (Equiv.ofInjective I hI).symm ⟨i, hi⟩
      if hle : a.val ≤ c.val then
        f ⟨(i, a), by
          intro c' hic'
          have hc_image : I c = i := by
            exact congrArg Subtype.val
              ((Equiv.ofInjective I hI).apply_symm_apply ⟨i, hi⟩)
          have hc' : c' = c := by
            apply hI
            calc
              I c' = i := hic'.symm
              _ = I c := hc_image.symm
          simpa [hc'] using hle⟩
      else
        f ⟨(I a, c), by
          intro b hb
          have hba : b = a := by
            exact (hI hb.symm)
          have hlt : c.val < a.val := Nat.lt_of_not_ge hle
          simpa [hba] using le_of_lt hlt⟩
    else
      f ⟨(i, a), by
        intro c hic
        exact False.elim (hi ⟨c, hic.symm⟩)⟩

private theorem sourceSelectedSymCoordKeyReconstructScalar_selected_apply
    (n m : ℕ) {I : Fin m → Fin n}
    (hI : Function.Injective I)
    (𝕜 : Type*) [Zero 𝕜]
    (f : sourceSelectedSymCoordKey n m I → 𝕜)
    (a b : Fin m) :
    sourceSelectedSymCoordKeyReconstructScalar n m hI 𝕜 f (I a) b =
      if hle : b.val ≤ a.val then
        f ⟨(I a, b), by
          intro c hc
          have hca : c = a := (hI hc.symm)
          simpa [hca] using hle⟩
      else
        f ⟨(I b, a), by
          intro c hc
          have hcb : c = b := (hI hc.symm)
          have hlt : a.val < b.val := Nat.lt_of_not_ge hle
          simpa [hcb] using le_of_lt hlt⟩ := by
  unfold sourceSelectedSymCoordKeyReconstructScalar
  have hrow : I a ∈ Set.range I := ⟨a, rfl⟩
  have hsymm : (Equiv.ofInjective I hI).symm ⟨I a, hrow⟩ = a := by
    apply hI
    exact congrArg Subtype.val
      ((Equiv.ofInjective I hI).apply_symm_apply ⟨I a, hrow⟩)
  simp [hrow, hsymm]

private theorem sourceSelectedSymCoordKeyReconstructScalar_symm
    (n m : ℕ) {I : Fin m → Fin n}
    (hI : Function.Injective I)
    (𝕜 : Type*) [Zero 𝕜]
    (f : sourceSelectedSymCoordKey n m I → 𝕜)
    (a b : Fin m) :
    sourceSelectedSymCoordKeyReconstructScalar n m hI 𝕜 f (I a) b =
      sourceSelectedSymCoordKeyReconstructScalar n m hI 𝕜 f (I b) a := by
  rcases lt_trichotomy a.val b.val with hlt | heq | hgt
  · have hnot : ¬ b.val ≤ a.val := Nat.not_le_of_gt hlt
    have hle : a.val ≤ b.val := le_of_lt hlt
    rw [sourceSelectedSymCoordKeyReconstructScalar_selected_apply,
      sourceSelectedSymCoordKeyReconstructScalar_selected_apply]
    simp [hnot, hle]
  · have hab : a = b := Fin.ext heq
    subst b
    rfl
  · have hle : b.val ≤ a.val := le_of_lt hgt
    have hnot : ¬ a.val ≤ b.val := Nat.not_le_of_gt hgt
    rw [sourceSelectedSymCoordKeyReconstructScalar_selected_apply,
      sourceSelectedSymCoordKeyReconstructScalar_selected_apply]
    simp [hnot, hle]

private theorem sourceSelectedSymCoordKeyReconstruct_mem_complex
    (n m : ℕ) {I : Fin m → Fin n}
    (hI : Function.Injective I)
    (f : sourceSelectedSymCoordKey n m I → ℂ) :
    sourceSelectedSymCoordKeyReconstructScalar n m hI ℂ f ∈
      sourceSelectedComplexSymCoordSubspace n m I := by
  intro a b
  exact sourceSelectedSymCoordKeyReconstructScalar_symm n m hI ℂ f a b

private theorem sourceSelectedSymCoordKeyReconstruct_mem_real
    (n m : ℕ) {I : Fin m → Fin n}
    (hI : Function.Injective I)
    (f : sourceSelectedSymCoordKey n m I → ℝ) :
    sourceSelectedSymCoordKeyReconstructScalar n m hI ℝ f ∈
      sourceSelectedSymCoordSubspace n m I := by
  intro a b
  exact sourceSelectedSymCoordKeyReconstructScalar_symm n m hI ℝ f a b

private noncomputable def sourceSelectedComplexSymCoordKeyReconstructCLM
    (n m : ℕ) {I : Fin m → Fin n}
    (hI : Function.Injective I) :
    (sourceSelectedSymCoordKey n m I → ℂ) →L[ℂ]
      sourceSelectedComplexSymCoordSubspace n m I :=
  LinearMap.toContinuousLinearMap {
    toFun := fun f =>
      ⟨sourceSelectedSymCoordKeyReconstructScalar n m hI ℂ f,
        sourceSelectedSymCoordKeyReconstruct_mem_complex n m hI f⟩
    map_add' := by
      intro f g
      ext i a
      change sourceSelectedSymCoordKeyReconstructScalar n m hI ℂ (f + g) i a =
        sourceSelectedSymCoordKeyReconstructScalar n m hI ℂ f i a +
          sourceSelectedSymCoordKeyReconstructScalar n m hI ℂ g i a
      unfold sourceSelectedSymCoordKeyReconstructScalar
      by_cases hmem : i ∈ Set.range I
      · by_cases hle :
          a.val ≤ ((Equiv.ofInjective I hI).symm ⟨i, hmem⟩).val
        · simp [hmem, hle]
        · simp [hmem, hle]
      · simp [hmem]
    map_smul' := by
      intro c f
      ext i a
      change sourceSelectedSymCoordKeyReconstructScalar n m hI ℂ (c • f) i a =
        c • sourceSelectedSymCoordKeyReconstructScalar n m hI ℂ f i a
      unfold sourceSelectedSymCoordKeyReconstructScalar
      split_ifs <;> simp }

private noncomputable def sourceSelectedRealSymCoordKeyReconstructCLM
    (n m : ℕ) {I : Fin m → Fin n}
    (hI : Function.Injective I) :
    (sourceSelectedSymCoordKey n m I → ℝ) →L[ℝ]
      sourceSelectedSymCoordSubspace n m I :=
  LinearMap.toContinuousLinearMap {
    toFun := fun f =>
      ⟨sourceSelectedSymCoordKeyReconstructScalar n m hI ℝ f,
        sourceSelectedSymCoordKeyReconstruct_mem_real n m hI f⟩
    map_add' := by
      intro f g
      ext i a
      change sourceSelectedSymCoordKeyReconstructScalar n m hI ℝ (f + g) i a =
        sourceSelectedSymCoordKeyReconstructScalar n m hI ℝ f i a +
          sourceSelectedSymCoordKeyReconstructScalar n m hI ℝ g i a
      unfold sourceSelectedSymCoordKeyReconstructScalar
      by_cases hmem : i ∈ Set.range I
      · by_cases hle :
          a.val ≤ ((Equiv.ofInjective I hI).symm ⟨i, hmem⟩).val
        · simp [hmem, hle]
        · simp [hmem, hle]
      · simp [hmem]
    map_smul' := by
      intro c f
      ext i a
      change sourceSelectedSymCoordKeyReconstructScalar n m hI ℝ (c • f) i a =
        c • sourceSelectedSymCoordKeyReconstructScalar n m hI ℝ f i a
      unfold sourceSelectedSymCoordKeyReconstructScalar
      split_ifs <;> simp }

private theorem sourceSelectedComplexSymCoordKeyEval_reconstruct
    (n m : ℕ) {I : Fin m → Fin n}
    (hI : Function.Injective I)
    (f : sourceSelectedSymCoordKey n m I → ℂ) :
    sourceSelectedComplexSymCoordKeyEvalCLM n m I
        (sourceSelectedComplexSymCoordKeyReconstructCLM n m hI f) = f := by
  ext q
  rcases q with ⟨⟨i, a⟩, hq⟩
  change sourceSelectedSymCoordKeyReconstructScalar n m hI ℂ f i a =
    f ⟨(i, a), hq⟩
  unfold sourceSelectedSymCoordKeyReconstructScalar
  by_cases hi : i ∈ Set.range I
  · let c := (Equiv.ofInjective I hI).symm ⟨i, hi⟩
    have hc_image : I c = i := by
      exact congrArg Subtype.val
        ((Equiv.ofInjective I hI).apply_symm_apply ⟨i, hi⟩)
    have hle : a.val ≤ c.val := hq c hc_image.symm
    simp [hi, c, hle]
  · simp [hi]

private theorem sourceSelectedRealSymCoordKeyEval_reconstruct
    (n m : ℕ) {I : Fin m → Fin n}
    (hI : Function.Injective I)
    (f : sourceSelectedSymCoordKey n m I → ℝ) :
    sourceSelectedRealSymCoordKeyEvalCLM n m I
        (sourceSelectedRealSymCoordKeyReconstructCLM n m hI f) = f := by
  ext q
  rcases q with ⟨⟨i, a⟩, hq⟩
  change sourceSelectedSymCoordKeyReconstructScalar n m hI ℝ f i a =
    f ⟨(i, a), hq⟩
  unfold sourceSelectedSymCoordKeyReconstructScalar
  by_cases hi : i ∈ Set.range I
  · let c := (Equiv.ofInjective I hI).symm ⟨i, hi⟩
    have hc_image : I c = i := by
      exact congrArg Subtype.val
        ((Equiv.ofInjective I hI).apply_symm_apply ⟨i, hi⟩)
    have hle : a.val ≤ c.val := hq c hc_image.symm
    simp [hi, c, hle]
  · simp [hi]

private theorem sourceSelectedComplexSymCoordKeyReconstruct_eval
    (n m : ℕ) {I : Fin m → Fin n}
    (hI : Function.Injective I)
    (A : sourceSelectedComplexSymCoordSubspace n m I) :
    sourceSelectedComplexSymCoordKeyReconstructCLM n m hI
        (sourceSelectedComplexSymCoordKeyEvalCLM n m I A) = A := by
  ext i a
  change sourceSelectedSymCoordKeyReconstructScalar n m hI ℂ
      (sourceSelectedComplexSymCoordKeyEvalCLM n m I A) i a =
    (A : Fin n → Fin m → ℂ) i a
  unfold sourceSelectedSymCoordKeyReconstructScalar
  by_cases hi : i ∈ Set.range I
  · let c := (Equiv.ofInjective I hI).symm ⟨i, hi⟩
    have hc_image : I c = i := by
      exact congrArg Subtype.val
        ((Equiv.ofInjective I hI).apply_symm_apply ⟨i, hi⟩)
    by_cases hle : a.val ≤ c.val
    · simp [hi, c, hle]
      change (A : Fin n → Fin m → ℂ) i a =
        (A : Fin n → Fin m → ℂ) i a
      rfl
    · simp [hi, c, hle]
      change (A : Fin n → Fin m → ℂ) (I a) c =
        (A : Fin n → Fin m → ℂ) i a
      rw [← hc_image]
      exact (A.property c a).symm
  · simp [hi]
    change (A : Fin n → Fin m → ℂ) i a =
      (A : Fin n → Fin m → ℂ) i a
    rfl

private theorem sourceSelectedRealSymCoordKeyReconstruct_eval
    (n m : ℕ) {I : Fin m → Fin n}
    (hI : Function.Injective I)
    (A : sourceSelectedSymCoordSubspace n m I) :
    sourceSelectedRealSymCoordKeyReconstructCLM n m hI
        (sourceSelectedRealSymCoordKeyEvalCLM n m I A) = A := by
  ext i a
  change sourceSelectedSymCoordKeyReconstructScalar n m hI ℝ
      (sourceSelectedRealSymCoordKeyEvalCLM n m I A) i a =
    (A : Fin n → Fin m → ℝ) i a
  unfold sourceSelectedSymCoordKeyReconstructScalar
  by_cases hi : i ∈ Set.range I
  · let c := (Equiv.ofInjective I hI).symm ⟨i, hi⟩
    have hc_image : I c = i := by
      exact congrArg Subtype.val
        ((Equiv.ofInjective I hI).apply_symm_apply ⟨i, hi⟩)
    by_cases hle : a.val ≤ c.val
    · simp [hi, c, hle]
      change (A : Fin n → Fin m → ℝ) i a =
        (A : Fin n → Fin m → ℝ) i a
      rfl
    · simp [hi, c, hle]
      change (A : Fin n → Fin m → ℝ) (I a) c =
        (A : Fin n → Fin m → ℝ) i a
      rw [← hc_image]
      exact (A.property c a).symm
  · simp [hi]
    change (A : Fin n → Fin m → ℝ) i a =
      (A : Fin n → Fin m → ℝ) i a
    rfl

/-- Continuous linear coordinates on the complex selected symmetric-coordinate
subspace, indexed by the kept coordinate keys. -/
noncomputable def sourceSelectedComplexSymCoordKeyEquiv
    (n m : ℕ) {I : Fin m → Fin n}
    (hI : Function.Injective I) :
    sourceSelectedComplexSymCoordSubspace n m I ≃L[ℂ]
      (sourceSelectedSymCoordKey n m I → ℂ) :=
  ContinuousLinearEquiv.equivOfInverse
    (sourceSelectedComplexSymCoordKeyEvalCLM n m I)
    (sourceSelectedComplexSymCoordKeyReconstructCLM n m hI)
    (by
      intro A
      exact sourceSelectedComplexSymCoordKeyReconstruct_eval n m hI A)
    (by
      intro f
      exact sourceSelectedComplexSymCoordKeyEval_reconstruct n m hI f)

/-- Continuous linear coordinates on the real selected symmetric-coordinate
subspace, indexed by the kept coordinate keys. -/
noncomputable def sourceSelectedRealSymCoordKeyEquiv
    (n m : ℕ) {I : Fin m → Fin n}
    (hI : Function.Injective I) :
    sourceSelectedSymCoordSubspace n m I ≃L[ℝ]
      (sourceSelectedSymCoordKey n m I → ℝ) :=
  ContinuousLinearEquiv.equivOfInverse
    (sourceSelectedRealSymCoordKeyEvalCLM n m I)
    (sourceSelectedRealSymCoordKeyReconstructCLM n m hI)
    (by
      intro A
      exact sourceSelectedRealSymCoordKeyReconstruct_eval n m hI A)
    (by
      intro f
      exact sourceSelectedRealSymCoordKeyEval_reconstruct n m hI f)

/-- The selected-key coordinates commute with the real slice. -/
theorem sourceSelectedComplexSymCoordKeyEquiv_real_slice
    (n m : ℕ) {I : Fin m → Fin n}
    (hI : Function.Injective I)
    (A : sourceSelectedSymCoordSubspace n m I) :
    sourceSelectedComplexSymCoordKeyEquiv n m hI
      (sourceSelectedSymCoordRealComplexify n m I A) =
      fun q => ((sourceSelectedRealSymCoordKeyEquiv n m hI A q : ℝ) : ℂ) := by
  exact sourceSelectedComplexSymCoordKeyEvalCLM_real_slice n m I A

/-- Flat `Fin N` complex coordinates on the selected symmetric-coordinate
subspace. -/
noncomputable def sourceSelectedComplexSymCoordFinEquiv
    (n m : ℕ) {I : Fin m → Fin n}
    (hI : Function.Injective I) :
    sourceSelectedComplexSymCoordSubspace n m I ≃L[ℂ]
      (Fin (Fintype.card (sourceSelectedSymCoordKey n m I)) → ℂ) :=
  (sourceSelectedComplexSymCoordKeyEquiv n m hI).trans
    (ContinuousLinearEquiv.piCongrLeft ℂ
      (fun _ : Fin (Fintype.card (sourceSelectedSymCoordKey n m I)) => ℂ)
      (Fintype.equivFin (sourceSelectedSymCoordKey n m I)))

/-- Flat `Fin N` real coordinates on the selected symmetric-coordinate
subspace. -/
noncomputable def sourceSelectedRealSymCoordFinEquiv
    (n m : ℕ) {I : Fin m → Fin n}
    (hI : Function.Injective I) :
    sourceSelectedSymCoordSubspace n m I ≃L[ℝ]
      (Fin (Fintype.card (sourceSelectedSymCoordKey n m I)) → ℝ) :=
  (sourceSelectedRealSymCoordKeyEquiv n m hI).trans
    (ContinuousLinearEquiv.piCongrLeft ℝ
      (fun _ : Fin (Fintype.card (sourceSelectedSymCoordKey n m I)) => ℝ)
      (Fintype.equivFin (sourceSelectedSymCoordKey n m I)))

/-- The flat selected-symmetric coordinates commute with the real slice. -/
theorem sourceSelectedComplexSymCoordFinEquiv_real_slice
    (n m : ℕ) {I : Fin m → Fin n}
    (hI : Function.Injective I)
    (A : sourceSelectedSymCoordSubspace n m I) :
    sourceSelectedComplexSymCoordFinEquiv n m hI
      (sourceSelectedSymCoordRealComplexify n m I A) =
      SCV.realToComplex
        (sourceSelectedRealSymCoordFinEquiv n m hI A) := by
  ext k
  simp [sourceSelectedComplexSymCoordFinEquiv,
    sourceSelectedRealSymCoordFinEquiv,
    sourceSelectedComplexSymCoordKeyEquiv_real_slice,
    ContinuousLinearEquiv.piCongrLeft,
    Equiv.piCongrLeft_apply_eq_cast,
    SCV.realToComplex]

/-- The selected complex Gram coordinate map is smooth on an injective
selected-row chart. -/
theorem contDiff_sourceSelectedComplexGramMap_of_injective
    (d n m : ℕ)
    {I : Fin m → Fin n}
    (hI : Function.Injective I) :
    ContDiff ℂ ⊤ (sourceSelectedComplexGramMap d n m I) := by
  let Ekey := sourceSelectedComplexSymCoordKeyEquiv n m hI
  have hkey :
      ContDiff ℂ ⊤
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          Ekey (sourceSelectedComplexGramMap d n m I z)) := by
    rw [contDiff_pi]
    intro q
    have hcoord : ContDiff ℂ ⊤
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          sourceMinkowskiGram d n z q.val.1 (I q.val.2)) := by
      exact (contDiff_apply_apply ℂ ℂ q.val.1 (I q.val.2)).comp
        (contDiff_sourceMinkowskiGram d n)
    simpa [Ekey, sourceSelectedComplexSymCoordKeyEquiv,
      sourceSelectedComplexSymCoordKeyEvalCLM] using hcoord
  have hdecomp :
      sourceSelectedComplexGramMap d n m I =
        (fun A => Ekey.symm A) ∘
          (fun z : Fin n → Fin (d + 1) → ℂ =>
            Ekey (sourceSelectedComplexGramMap d n m I z)) := by
    funext z
    simp [Ekey]
  rw [hdecomp]
  exact Ekey.symm.contDiff.comp hkey

/-- The fixed projection onto the base kernel used by the selected complex
implicit product chart. -/
noncomputable def sourceSelectedComplexGramKernelProjection
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (I : Fin (min n (d + 1)) → Fin n) :
    (Fin n → Fin (d + 1) → ℂ) →L[ℂ]
      LinearMap.ker
        (sourceSelectedComplexGramDifferentialToSym d n
          (min n (d + 1)) (realEmbed x0) I) :=
  let m := min n (d + 1)
  let L : (Fin n → Fin (d + 1) → ℂ) →L[ℂ]
      sourceSelectedComplexSymCoordSubspace n m I :=
    LinearMap.toContinuousLinearMap
      (sourceSelectedComplexGramDifferentialToSym d n m (realEmbed x0) I)
  Classical.choose L.ker_closedComplemented_of_finiteDimensional_range

/-- The base-kernel projection fixes the base kernel pointwise. -/
theorem sourceSelectedComplexGramKernelProjection_apply_ker
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (I : Fin (min n (d + 1)) → Fin n)
    (v :
      LinearMap.ker
        (sourceSelectedComplexGramDifferentialToSym d n
          (min n (d + 1)) (realEmbed x0) I)) :
    sourceSelectedComplexGramKernelProjection d n I v = v := by
  let m := min n (d + 1)
  let L : (Fin n → Fin (d + 1) → ℂ) →L[ℂ]
      sourceSelectedComplexSymCoordSubspace n m I :=
    LinearMap.toContinuousLinearMap
      (sourceSelectedComplexGramDifferentialToSym d n m (realEmbed x0) I)
  exact Classical.choose_spec
    L.ker_closedComplemented_of_finiteDimensional_range v

/-- Product chart map for the selected complex Gram map, using the fixed
projection onto the base kernel as transverse coordinate. -/
noncomputable def sourceSelectedComplexGramProdMap
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (I : Fin (min n (d + 1)) → Fin n) :
    (Fin n → Fin (d + 1) → ℂ) →
      sourceSelectedComplexSymCoordSubspace n (min n (d + 1)) I ×
        LinearMap.ker
          (sourceSelectedComplexGramDifferentialToSym d n
            (min n (d + 1)) (realEmbed x0) I) :=
  fun z =>
    (sourceSelectedComplexGramMap d n (min n (d + 1)) I z,
      sourceSelectedComplexGramKernelProjection d n I (z - realEmbed x0))

/-- The selected complex product chart map is smooth. -/
theorem contDiff_sourceSelectedComplexGramProdMap
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    (hI : Function.Injective I) :
    ContDiff ℂ ⊤ (sourceSelectedComplexGramProdMap d n I (x0 := x0)) := by
  unfold sourceSelectedComplexGramProdMap
  refine (contDiff_sourceSelectedComplexGramMap_of_injective d n
    (min n (d + 1)) hI).prodMk ?_
  fun_prop

/-- Frechet derivative of the selected complex product chart map. -/
theorem sourceSelectedComplexGramProdMap_hasFDerivAt
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (I : Fin (min n (d + 1)) → Fin n)
    (z : Fin n → Fin (d + 1) → ℂ) :
    HasFDerivAt (sourceSelectedComplexGramProdMap d n I (x0 := x0))
      ((LinearMap.toContinuousLinearMap
          (sourceSelectedComplexGramDifferentialToSym d n
            (min n (d + 1)) z I)).prod
        (sourceSelectedComplexGramKernelProjection d n I)) z := by
  unfold sourceSelectedComplexGramProdMap
  refine
    (sourceSelectedComplexGramMap_hasStrictFDerivAt d n
      (min n (d + 1)) I z).hasFDerivAt.prodMk ?_
  exact (sourceSelectedComplexGramKernelProjection d n I).hasFDerivAt.comp z
    ((hasFDerivAt_id z).sub_const (realEmbed x0))

/-- Formula for the Frechet derivative of the selected complex product chart
map. -/
theorem sourceSelectedComplexGramProdMap_fderiv
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (I : Fin (min n (d + 1)) → Fin n)
    (z : Fin n → Fin (d + 1) → ℂ) :
    fderiv ℂ (sourceSelectedComplexGramProdMap d n I (x0 := x0)) z =
      (LinearMap.toContinuousLinearMap
          (sourceSelectedComplexGramDifferentialToSym d n
            (min n (d + 1)) z I)).prod
        (sourceSelectedComplexGramKernelProjection d n I) :=
  (sourceSelectedComplexGramProdMap_hasFDerivAt d n I z).fderiv

/-- At the base real point, the selected complex product chart derivative is
invertible. -/
theorem sourceSelectedComplexGramProdMap_base_fderiv_isInvertible
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceRegularMinor d n I J x0 ≠ 0) :
    (fderiv ℂ (sourceSelectedComplexGramProdMap d n I (x0 := x0))
      (realEmbed x0)).IsInvertible := by
  let m := min n (d + 1)
  let L : (Fin n → Fin (d + 1) → ℂ) →L[ℂ]
      sourceSelectedComplexSymCoordSubspace n m I :=
    LinearMap.toContinuousLinearMap
      (sourceSelectedComplexGramDifferentialToSym d n m (realEmbed x0) I)
  let P :
      (Fin n → Fin (d + 1) → ℂ) →L[ℂ]
        LinearMap.ker
          (sourceSelectedComplexGramDifferentialToSym d n m (realEmbed x0) I) :=
    sourceSelectedComplexGramKernelProjection d n I
  have hsurj : L.range = ⊤ := by
    exact LinearMap.range_eq_top.mpr
      (sourceSelectedComplexGramDifferentialToSym_surjective_of_sourceRegularMinor_ne_zero
        d n hI hJ hminor)
  have hproj :
      ∀ v : L.ker, P v = v := by
    intro v
    exact sourceSelectedComplexGramKernelProjection_apply_ker d n I v
  have hPrange : P.range = ⊤ := LinearMap.range_eq_of_proj hproj
  have hcompl : IsCompl L.ker P.ker := LinearMap.isCompl_of_proj hproj
  rw [sourceSelectedComplexGramProdMap_fderiv]
  let eLin :=
    LinearMap.equivProdOfSurjectiveOfIsCompl
      (L : (Fin n → Fin (d + 1) → ℂ) →ₗ[ℂ]
        sourceSelectedComplexSymCoordSubspace n m I)
      (P : (Fin n → Fin (d + 1) → ℂ) →ₗ[ℂ]
        LinearMap.ker
          (sourceSelectedComplexGramDifferentialToSym d n m (realEmbed x0) I))
      hsurj hPrange hcompl
  refine ⟨eLin.toContinuousLinearEquiv, ?_⟩
  ext v <;> rfl

/-- After shrinking the source neighborhood of the base real point, the
selected complex product chart derivative remains invertible. -/
theorem sourceSelectedComplexGramProdMap_local_invertible_nhds
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceRegularMinor d n I J x0 ≠ 0)
    {V : Set (Fin n → Fin (d + 1) → ℂ)}
    (hV_open : IsOpen V)
    (hx0V : realEmbed x0 ∈ V) :
    ∃ W : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen W ∧ realEmbed x0 ∈ W ∧ W ⊆ V ∧
      ∀ z ∈ W,
        (fderiv ℂ (sourceSelectedComplexGramProdMap d n I (x0 := x0)) z).IsInvertible := by
  let Espace := Fin n → Fin (d + 1) → ℂ
  let ProdTarget :=
    sourceSelectedComplexSymCoordSubspace n (min n (d + 1)) I ×
      LinearMap.ker
        (sourceSelectedComplexGramDifferentialToSym d n
          (min n (d + 1)) (realEmbed x0) I)
  let InvSet :
      Set (Espace →L[ℂ] ProdTarget) :=
    Set.range ((↑) : (Espace ≃L[ℂ] ProdTarget) → Espace →L[ℂ] ProdTarget)
  have hInvOpen : IsOpen InvSet := by
    dsimp [InvSet]
    exact ContinuousLinearEquiv.isOpen
      (𝕜 := ℂ)
      (E := Espace)
      (F := ProdTarget)
  have hderivCont :
      Continuous
        (fun z : Fin n → Fin (d + 1) → ℂ =>
          fderiv ℂ (sourceSelectedComplexGramProdMap d n I (x0 := x0)) z) := by
    exact (contDiff_sourceSelectedComplexGramProdMap d n hI
      (x0 := x0)).continuous_fderiv (by simp)
  let W : Set (Fin n → Fin (d + 1) → ℂ) :=
    V ∩ {z |
      fderiv ℂ (sourceSelectedComplexGramProdMap d n I (x0 := x0)) z ∈ InvSet}
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · exact hV_open.inter (hInvOpen.preimage hderivCont)
  · refine ⟨hx0V, ?_⟩
    exact sourceSelectedComplexGramProdMap_base_fderiv_isInvertible
      d n hI hJ hminor
  · intro z hz
    exact hz.1
  · intro z hz
    exact hz.2

end BHW
