import Mathlib.LinearAlgebra.Basis.Defs
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedFullFrameChart
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedLocalBasis
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexDensity

/-!
# Full-frame max-rank chart producer

This file converts the full-frame chart construction into the max-rank chart
producer expected by the oriented local-basis layer in the hard range
`d + 1 <= n`.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace

namespace BHW

/-- The selected nonzero full frame of a source tuple as a basis of complex
spacetime. -/
noncomputable def sourceFullFrameBasis
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hι : sourceFullFrameDet d n ι z ≠ 0) :
    Module.Basis (Fin (d + 1)) ℂ (Fin (d + 1) → ℂ) :=
  let M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    sourceFullFrameMatrix d n ι z
  let hMdet : IsUnit M.transpose.det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr (by simpa [M, sourceFullFrameDet] using hι)
  letI hM : Invertible M.transpose :=
    Matrix.invertibleOfIsUnitDet M.transpose hMdet
  (Pi.basisFun ℂ (Fin (d + 1))).map
    (Matrix.toLinearEquiv' M.transpose hM)

/-- The selected full-frame basis evaluates to the selected source vectors. -/
theorem sourceFullFrameBasis_apply
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hι : sourceFullFrameDet d n ι z ≠ 0)
    (a : Fin (d + 1)) :
    sourceFullFrameBasis d n ι z hι a = z (ι a) := by
  ext μ
  unfold sourceFullFrameBasis
  rw [Module.Basis.map_apply, Pi.basisFun_apply]
  change
    ((((sourceFullFrameMatrix d n ι z).transpose.toLinearEquiv' _) :
        Module.End ℂ (Fin (d + 1) → ℂ)) (Pi.single a 1)) μ =
      z (ι a) μ
  rw [Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply]
  simp [sourceFullFrameMatrix]

/-- In the hard range `d + 1 <= n`, scalar max rank of an actual source
configuration forces maximal complex source span. -/
theorem sourceComplexGramRegularAt_of_HWSourceGramMaxRankAt
    (d n : ℕ)
    (hn : d + 1 ≤ n)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hmax : HWSourceGramMaxRankAt d n z) :
    SourceComplexGramRegularAt d n z := by
  let S : Submodule ℂ (Fin (d + 1) → ℂ) :=
    sourceComplexConfigurationSpan d n z
  have hrank_ge :
      d + 1 ≤
        (Matrix.of fun i j : Fin n => sourceMinkowskiGram d n z i j).rank := by
    simpa [HWSourceGramMaxRankAt, HWSourceGramMaxRank, sourceGramMatrixRank,
      Nat.min_eq_left hn] using hmax
  have hrank_le :
      (Matrix.of fun i j : Fin n => sourceMinkowskiGram d n z i j).rank ≤
        Module.finrank ℂ S := by
    simpa [S] using
      sourceMinkowskiGram_rank_le_sourceComplexConfigurationSpan_finrank d n z
  have hge : d + 1 ≤ Module.finrank ℂ S :=
    le_trans hrank_ge hrank_le
  have hle : Module.finrank ℂ S ≤ d + 1 := by
    have h := Submodule.finrank_le S
    simpa [S, sourceComplexConfigurationSpan, Module.finrank_fin_fun] using h
  unfold SourceComplexGramRegularAt
  rw [Nat.min_eq_right hn]
  exact le_antisymm hle hge

/-- In the hard range, maximal complex source span supplies a selected
full-frame source determinant which is nonzero. -/
theorem exists_sourceFullFrameDet_ne_zero_of_sourceComplexGramRegularAt
    (d n : ℕ)
    (hn : d + 1 ≤ n)
    {z : Fin n → Fin (d + 1) → ℂ}
    (hreg : SourceComplexGramRegularAt d n z) :
    ∃ ι : Fin (d + 1) ↪ Fin n, sourceFullFrameDet d n ι z ≠ 0 := by
  rcases exists_nonzero_minor_of_sourceComplexGramRegularAt d n hreg with
    ⟨I, hI, _J, _hJ, hminor⟩
  let e : Fin (d + 1) ≃ Fin (min n (d + 1)) :=
    finCongr (Nat.min_eq_right hn).symm
  let ι : Fin (d + 1) ↪ Fin n :=
    { toFun := fun a => I (e a)
      inj' := by
        intro a b hab
        exact e.injective (hI hab) }
  let M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    sourceFullFrameMatrix d n ι z
  have hli_min :
      LinearIndependent ℂ (fun a : Fin (min n (d + 1)) => z (I a)) :=
    linearIndependent_complex_sourceRows_of_sourceComplexRegularMinor_ne_zero
      d n hminor
  have hli :
      LinearIndependent ℂ (fun a : Fin (d + 1) => z (ι a)) := by
    simpa [ι, Function.comp_def] using hli_min.comp e e.injective
  have hrows : LinearIndependent ℂ M.row := by
    simpa [M, sourceFullFrameMatrix, Matrix.row] using hli
  have hMunit : IsUnit M :=
    (Matrix.linearIndependent_rows_iff_isUnit).1 hrows
  have hdet : M.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det M).1 hMunit).ne_zero
  exact ⟨ι, by simpa [M, sourceFullFrameDet] using hdet⟩

/-- Same ordinary source Gram preserves nonvanishing of a selected full-frame
determinant. -/
theorem sourceFullFrameDet_ne_zero_of_sameGram_fullFrame
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w)
    (ι : Fin (d + 1) ↪ Fin n)
    (hι : sourceFullFrameDet d n ι z ≠ 0) :
    sourceFullFrameDet d n ι w ≠ 0 := by
  let Mz : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    sourceFullFrameMatrix d n ι z
  let Mw : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
    sourceFullFrameMatrix d n ι w
  have hsel :
      sourceFullFrameGram d Mz =
        sourceFullFrameGram d Mw := by
    ext a b
    simpa [Mz, Mw, sourceFullFrameGram_sourceFullFrameMatrix] using
      congrFun (congrFun hgram (ι a)) (ι b)
  intro hwzero
  have hdet_eq :
      (Matrix.of (sourceFullFrameGram d Mz)).det =
        (Matrix.of (sourceFullFrameGram d Mw)).det := by
    simpa using
      congrArg (fun G : Fin (d + 1) → Fin (d + 1) → ℂ =>
        (Matrix.of G).det) hsel
  have hzdet : Mz.det ≠ 0 := by
    simpa [Mz, sourceFullFrameDet] using hι
  have hwdet : Mw.det = 0 := by
    simpa [Mw, sourceFullFrameDet] using hwzero
  have hdet_eq' :
      minkowskiMetricDet d * Mz.det ^ 2 =
        minkowskiMetricDet d * Mw.det ^ 2 := by
    calc
      minkowskiMetricDet d * Mz.det ^ 2 =
          (Matrix.of (sourceFullFrameGram d Mz)).det :=
        (sourceFullFrameGram_det_eq d Mz).symm
      _ = (Matrix.of (sourceFullFrameGram d Mw)).det := hdet_eq
      _ = minkowskiMetricDet d * Mw.det ^ 2 :=
        sourceFullFrameGram_det_eq d Mw
  have hright : minkowskiMetricDet d * Mw.det ^ 2 = 0 := by
    rw [hwdet]
    simp
  exact (mul_ne_zero (minkowskiMetricDet_ne_zero d)
    (pow_ne_zero 2 hzdet)) (hdet_eq'.trans hright)

/-- The selected full-frame map carrying the chosen full frame of `z` to the
corresponding full frame of `w`. -/
noncomputable def sourceFullFrameMap
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w)
    (ι : Fin (d + 1) ↪ Fin n)
    (hι : sourceFullFrameDet d n ι z ≠ 0) :
    (Fin (d + 1) → ℂ) ≃ₗ[ℂ] (Fin (d + 1) → ℂ) :=
  let hιw := sourceFullFrameDet_ne_zero_of_sameGram_fullFrame
    d n hgram ι hι
  (sourceFullFrameBasis d n ι z hι).equiv
    (sourceFullFrameBasis d n ι w hιw)
    (Equiv.refl (Fin (d + 1)))

/-- The selected full-frame map sends selected source vectors of `z` to the
corresponding selected source vectors of `w`. -/
theorem sourceFullFrameMap_apply_selected
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w)
    (ι : Fin (d + 1) ↪ Fin n)
    (hι : sourceFullFrameDet d n ι z ≠ 0)
    (a : Fin (d + 1)) :
    sourceFullFrameMap d n hgram ι hι (z (ι a)) = w (ι a) := by
  let hιw := sourceFullFrameDet_ne_zero_of_sameGram_fullFrame
    d n hgram ι hι
  calc
    sourceFullFrameMap d n hgram ι hι (z (ι a)) =
        sourceFullFrameMap d n hgram ι hι
          ((sourceFullFrameBasis d n ι z hι) a) := by
          rw [sourceFullFrameBasis_apply]
    _ = (sourceFullFrameBasis d n ι w hιw) a := by
          rw [sourceFullFrameMap]
          simp
    _ = w (ι a) := sourceFullFrameBasis_apply d n ι w hιw a

/-- The complex Minkowski pairing as a bilinear form. -/
def sourceComplexMinkowskiBilinForm
    (d : ℕ) : LinearMap.BilinForm ℂ (Fin (d + 1) → ℂ) where
  toFun u :=
    { toFun := fun v => sourceComplexMinkowskiInner d u v
      map_add' := by
        intro v w
        exact sourceComplexMinkowskiInner_add_right d u v w
      map_smul' := by
        intro c v
        exact sourceComplexMinkowskiInner_smul_right d c u v }
  map_add' := by
    intro u v
    apply LinearMap.ext
    intro w
    exact sourceComplexMinkowskiInner_add_left d u v w
  map_smul' := by
    intro c u
    apply LinearMap.ext
    intro v
    exact sourceComplexMinkowskiInner_smul_left d c u v

@[simp]
theorem sourceComplexMinkowskiBilinForm_apply
    (d : ℕ) (u v : Fin (d + 1) → ℂ) :
    sourceComplexMinkowskiBilinForm d u v =
      sourceComplexMinkowskiInner d u v :=
  rfl

/-- The complex Minkowski bilinear form is symmetric. -/
theorem sourceComplexMinkowskiBilinForm_isSymm
    (d : ℕ) :
    (sourceComplexMinkowskiBilinForm d).IsSymm := by
  constructor
  intro u v
  simpa using sourceComplexMinkowskiInner_comm d u v

/-- Package a determinant-one linear equivalence preserving the complex
Minkowski pairing as a proper complex Lorentz transformation. -/
noncomputable def complexLorentzGroupOfLinearEquivPreservesInner
    (d : ℕ)
    (E : (Fin (d + 1) → ℂ) ≃ₗ[ℂ] (Fin (d + 1) → ℂ))
    (hpres :
      ∀ x y,
        sourceComplexMinkowskiInner d (E x) (E y) =
          sourceComplexMinkowskiInner d x y)
    (hdet : LinearMap.det E.toLinearMap = 1) :
    ComplexLorentzGroup d where
  val := LinearMap.toMatrix' E.toLinearMap
  metric_preserving := by
    intro μ ν
    have h := hpres (Pi.single μ (1 : ℂ)) (Pi.single ν (1 : ℂ))
    by_cases hμν : μ = ν
    · subst ν
      simpa [sourceComplexMinkowskiInner, LinearMap.toMatrix'_apply,
        Pi.single_apply, MinkowskiSpace.metricSignature, minkowskiSignature,
        mul_comm, mul_left_comm, mul_assoc] using h
    · have hνμ : ν ≠ μ := fun h => hμν h.symm
      simpa [sourceComplexMinkowskiInner, LinearMap.toMatrix'_apply,
        Pi.single_apply, MinkowskiSpace.metricSignature, minkowskiSignature,
        hμν, hνμ, mul_comm, mul_left_comm, mul_assoc] using h
  proper := by
    rw [LinearMap.det_toMatrix']
    exact hdet

/-- The packaged Lorentz transformation acts by the original linear
equivalence. -/
theorem complexLorentzVectorAction_ofLinearEquivPreservesInner
    (d : ℕ)
    (E : (Fin (d + 1) → ℂ) ≃ₗ[ℂ] (Fin (d + 1) → ℂ))
    (hpres :
      ∀ x y,
        sourceComplexMinkowskiInner d (E x) (E y) =
          sourceComplexMinkowskiInner d x y)
    (hdet : LinearMap.det E.toLinearMap = 1)
    (v : Fin (d + 1) → ℂ) :
    complexLorentzVectorAction
        (complexLorentzGroupOfLinearEquivPreservesInner d E hpres hdet) v =
      E v := by
  ext μ
  have h := congrFun (LinearMap.toMatrix'_mulVec E.toLinearMap v) μ
  simpa [complexLorentzVectorAction,
    complexLorentzGroupOfLinearEquivPreservesInner, Matrix.mulVec, dotProduct,
    mul_comm, mul_left_comm, mul_assoc] using h

/-- A bilinear form is determined by its values on a basis, after transporting
the basis through a linear equivalence. -/
theorem bilinForm_eq_of_basis_values
    {ι U : Type*}
    [Fintype ι] [DecidableEq ι]
    [AddCommGroup U] [Module ℂ U]
    (B : LinearMap.BilinForm ℂ U)
    (b : Module.Basis ι ℂ U)
    {L : U ≃ₗ[ℂ] U}
    (hbasis : ∀ a b', B (L (b a)) (L (b b')) = B (b a) (b b')) :
    ∀ x y, B (L x) (L y) = B x y := by
  intro x y
  calc
    B (L x) (L y) =
        ((b.map L).repr (L x)).sum fun i xi =>
          ((b.map L).repr (L y)).sum fun j yj =>
            xi • yj • B ((b.map L) i) ((b.map L) j) := by
          exact (LinearMap.sum_repr_mul_repr_mul
            (b.map L) (b.map L) (B := B) (L x) (L y)).symm
    _ = (b.repr x).sum fun i xi =>
          (b.repr y).sum fun j yj =>
            xi • yj • B (b i) (b j) := by
          simp [hbasis]
    _ = B x y :=
          LinearMap.sum_repr_mul_repr_mul b b (B := B) x y

/-- A bilinear pairing against a fixed vector vanishes everywhere if it
vanishes on a basis. -/
theorem basis_pairing_zero_ext
    {ι U : Type*}
    [AddCommGroup U] [Module ℂ U]
    (B : LinearMap.BilinForm ℂ U)
    (b : Module.Basis ι ℂ U)
    {u : U}
    (h : ∀ a, B (b a) u = 0) :
    ∀ v, B v u = 0 := by
  let f : U →ₗ[ℂ] ℂ :=
    { toFun := fun v => B v u
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro c x
        simp }
  have hf : f = 0 := by
    apply b.ext
    intro i
    simp [f, h i]
  intro v
  simpa [f] using congrFun (congrArg DFunLike.coe hf) v

/-- The selected full-frame map preserves the complex Minkowski pairing. -/
theorem sourceFullFrameMap_preserves_inner
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w)
    (ι : Fin (d + 1) ↪ Fin n)
    (hι : sourceFullFrameDet d n ι z ≠ 0) :
    ∀ x y,
      sourceComplexMinkowskiInner d
        (sourceFullFrameMap d n hgram ι hι x)
        (sourceFullFrameMap d n hgram ι hι y) =
      sourceComplexMinkowskiInner d x y := by
  let bZ := sourceFullFrameBasis d n ι z hι
  let E := sourceFullFrameMap d n hgram ι hι
  have hbasis :
      ∀ a b,
        sourceComplexMinkowskiBilinForm d (E (bZ a)) (E (bZ b)) =
          sourceComplexMinkowskiBilinForm d (bZ a) (bZ b) := by
    intro a b
    have hpair :
        sourceComplexMinkowskiInner d (w (ι a)) (w (ι b)) =
          sourceComplexMinkowskiInner d (z (ι a)) (z (ι b)) := by
      simpa [sourceMinkowskiGram_apply_eq_complexInner] using
        (congrFun (congrFun hgram (ι a)) (ι b)).symm
    simpa [E, bZ, sourceFullFrameMap_apply_selected,
      sourceFullFrameBasis_apply] using hpair
  exact bilinForm_eq_of_basis_values
    (sourceComplexMinkowskiBilinForm d) bZ hbasis

/-- The selected full-frame map carries every source vector with the same Gram
matrix to the corresponding source vector. -/
theorem sourceFullFrameMap_apply_all
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w)
    (ι : Fin (d + 1) ↪ Fin n)
    (hι : sourceFullFrameDet d n ι z ≠ 0)
    (i : Fin n) :
    sourceFullFrameMap d n hgram ι hι (z i) = w i := by
  let E := sourceFullFrameMap d n hgram ι hι
  have hpres := sourceFullFrameMap_preserves_inner d n hgram ι hι
  let hιw := sourceFullFrameDet_ne_zero_of_sameGram_fullFrame
    d n hgram ι hι
  let bW := sourceFullFrameBasis d n ι w hιw
  have hdiff_zero : E (z i) - w i = 0 := by
    apply sourceComplexMinkowskiInner_left_nonDegenerate d
    intro v
    let L : (Fin (d + 1) → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun u => sourceComplexMinkowskiInner d (E (z i) - w i) u
        map_add' := by
          intro u v
          exact sourceComplexMinkowskiInner_add_right d (E (z i) - w i) u v
        map_smul' := by
          intro c u
          exact sourceComplexMinkowskiInner_smul_right d c (E (z i) - w i) u }
    change L v = 0
    have hL : L = 0 := by
      apply bW.ext
      intro a
      have hpair :
          sourceComplexMinkowskiInner d (E (z i)) (w (ι a)) =
            sourceComplexMinkowskiInner d (w i) (w (ι a)) := by
        calc
          sourceComplexMinkowskiInner d (E (z i)) (w (ι a)) =
              sourceComplexMinkowskiInner d (E (z i)) (E (z (ι a))) := by
                rw [sourceFullFrameMap_apply_selected d n hgram ι hι a]
          _ = sourceComplexMinkowskiInner d (z i) (z (ι a)) :=
                hpres (z i) (z (ι a))
          _ = sourceComplexMinkowskiInner d (w i) (w (ι a)) := by
                simpa [sourceMinkowskiGram_apply_eq_complexInner] using
                  congrFun (congrFun hgram i) (ι a)
      change sourceComplexMinkowskiInner d (E (z i) - w i) (bW a) = 0
      rw [sourceFullFrameBasis_apply]
      rw [sourceComplexMinkowskiInner_sub_left]
      exact sub_eq_zero.mpr hpair
    rw [hL]
    rfl
  exact sub_eq_zero.mp hdiff_zero

/-- Applying a linear equivalence to every source vector multiplies a selected
full-frame matrix on the right by the transpose of its coordinate matrix. -/
theorem sourceFullFrameMatrix_linearEquivAction
    (d n : ℕ)
    (L : (Fin (d + 1) → ℂ) ≃ₗ[ℂ] (Fin (d + 1) → ℂ))
    (ι : Fin (d + 1) ↪ Fin n)
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceFullFrameMatrix d n ι (fun i => L (z i)) =
      sourceFullFrameMatrix d n ι z *
        (LinearMap.toMatrix
          (Pi.basisFun ℂ (Fin (d + 1)))
          (Pi.basisFun ℂ (Fin (d + 1))) L.toLinearMap).transpose := by
  ext a μ
  have h :=
    congrFun (LinearMap.toMatrix'_mulVec L.toLinearMap (z (ι a))) μ
  simpa [sourceFullFrameMatrix, LinearMap.toMatrix_eq_toMatrix',
    Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    mul_comm, mul_left_comm, mul_assoc] using h.symm

/-- Applying a linear equivalence to every source vector scales a selected
full-frame determinant by the determinant of the linear equivalence. -/
theorem sourceFullFrameDet_linearEquivAction
    (d n : ℕ)
    (L : (Fin (d + 1) → ℂ) ≃ₗ[ℂ] (Fin (d + 1) → ℂ))
    (ι : Fin (d + 1) ↪ Fin n)
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceFullFrameDet d n ι (fun i => L (z i)) =
      sourceFullFrameDet d n ι z * LinearMap.det L.toLinearMap := by
  rw [sourceFullFrameDet, sourceFullFrameMatrix_linearEquivAction,
    sourceFullFrameDet, Matrix.det_mul, Matrix.det_transpose,
    LinearMap.det_toMatrix]

/-- The determinant of the selected same-Gram full-frame map is the quotient of
the corresponding selected full-frame determinants. -/
theorem det_sourceFullFrameMap_eq_ratio
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w)
    (ι : Fin (d + 1) ↪ Fin n)
    (hι : sourceFullFrameDet d n ι z ≠ 0) :
    LinearMap.det (sourceFullFrameMap d n hgram ι hι).toLinearMap =
      sourceFullFrameDet d n ι w / sourceFullFrameDet d n ι z := by
  let E := sourceFullFrameMap d n hgram ι hι
  have hact := sourceFullFrameDet_linearEquivAction d n E ι z
  have hall : (fun i => E (z i)) = w := by
    funext i
    exact sourceFullFrameMap_apply_all d n hgram ι hι i
  rw [hall] at hact
  change LinearMap.det E.toLinearMap =
    sourceFullFrameDet d n ι w / sourceFullFrameDet d n ι z
  rw [hact]
  field_simp [hι]

/-- The same-Gram full-frame map is independent of the selected nonzero full
frame, as a linear map. -/
theorem sourceFullFrameMap_toLinearMap_eq_of_sameGram_fullFrame
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w)
    (ι κ : Fin (d + 1) ↪ Fin n)
    (hι : sourceFullFrameDet d n ι z ≠ 0)
    (hκ : sourceFullFrameDet d n κ z ≠ 0) :
    (sourceFullFrameMap d n hgram ι hι).toLinearMap =
      (sourceFullFrameMap d n hgram κ hκ).toLinearMap := by
  let Eι := sourceFullFrameMap d n hgram ι hι
  let Eκ := sourceFullFrameMap d n hgram κ hκ
  let bι := sourceFullFrameBasis d n ι z hι
  apply bι.ext
  intro a
  change Eι (bι a) = Eκ (bι a)
  calc
    Eι (bι a) = Eι (z (ι a)) := by rw [sourceFullFrameBasis_apply]
    _ = w (ι a) := sourceFullFrameMap_apply_all d n hgram ι hι (ι a)
    _ = Eκ (z (ι a)) := (sourceFullFrameMap_apply_all d n hgram κ hκ (ι a)).symm
    _ = Eκ (bι a) := by rw [sourceFullFrameBasis_apply]

/-- Independence of the full-frame determinant ratio in the full scalar-rank
case. -/
theorem sourceFullFrameDet_ratio_eq_of_sameSourceGram_fullRank
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (_hfull :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z) = d + 1)
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w)
    (ι κ : Fin (d + 1) ↪ Fin n)
    (hι : sourceFullFrameDet d n ι z ≠ 0)
    (hκ : sourceFullFrameDet d n κ z ≠ 0) :
    sourceFullFrameDet d n ι w / sourceFullFrameDet d n ι z =
      sourceFullFrameDet d n κ w / sourceFullFrameDet d n κ z := by
  have hdetι := det_sourceFullFrameMap_eq_ratio d n hgram ι hι
  have hdetκ := det_sourceFullFrameMap_eq_ratio d n hgram κ hκ
  have hmaps :=
    sourceFullFrameMap_toLinearMap_eq_of_sameGram_fullFrame
      d n hgram ι κ hι hκ
  have hdet_eq :
      LinearMap.det (sourceFullFrameMap d n hgram ι hι).toLinearMap =
        LinearMap.det (sourceFullFrameMap d n hgram κ hκ).toLinearMap := by
    rw [hmaps]
  exact hdetι.symm.trans (hdet_eq.trans hdetκ)

/-- Determinant of the unique ambient same-Gram frame map in the full scalar
rank case.  Outside the full-rank/nonzero-frame case the value is a harmless
default; downstream orientation predicates use it only after a nonzero full
frame is available. -/
noncomputable def HWFullRankSameGramFrameMapDet
    (d n : ℕ)
    (z w : Fin n → Fin (d + 1) → ℂ) : ℂ :=
  if h : ∃ ι : Fin (d + 1) ↪ Fin n, sourceFullFrameDet d n ι z ≠ 0 then
    let ι := Classical.choose h
    sourceFullFrameDet d n ι w / sourceFullFrameDet d n ι z
  else
    1

/-- The chosen determinant in `HWFullRankSameGramFrameMapDet` agrees with any
nonzero selected full-frame determinant ratio under the full-rank same-Gram
hypotheses. -/
theorem hwFullRankSameGramFrameMapDet_eq_det_ratio_of_fullFrame
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hfull :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z) = d + 1)
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w)
    (ι : Fin (d + 1) ↪ Fin n)
    (hι : sourceFullFrameDet d n ι z ≠ 0) :
    HWFullRankSameGramFrameMapDet d n z w =
      sourceFullFrameDet d n ι w / sourceFullFrameDet d n ι z := by
  unfold HWFullRankSameGramFrameMapDet
  have hnonempty :
      ∃ κ : Fin (d + 1) ↪ Fin n, sourceFullFrameDet d n κ z ≠ 0 :=
    ⟨ι, hι⟩
  rw [dif_pos hnonempty]
  let κ := Classical.choose hnonempty
  have hκ : sourceFullFrameDet d n κ z ≠ 0 :=
    Classical.choose_spec hnonempty
  exact sourceFullFrameDet_ratio_eq_of_sameSourceGram_fullRank
    d n hfull hgram κ ι hκ hι

/-- Orientation compatibility for determinant-`1` same-Gram extension: below
full ambient rank a complementary determinant correction is available; in full
ambient rank the unique full-frame same-Gram determinant must be `1`. -/
def HWSameSourceGramSOOrientationCompatible
    (d n : ℕ)
    (z w : Fin n → Fin (d + 1) → ℂ) : Prop :=
  sourceGramMatrixRank n (sourceMinkowskiGram d n z) < d + 1 ∨
    HWFullRankSameGramFrameMapDet d n z w = 1

/-- Full scalar Gram rank supplies a nonzero ordered full-frame determinant. -/
theorem exists_sourceFullFrameDet_ne_zero_of_sourceGramRank_eq_spacetime
    (d n : ℕ)
    (z : Fin n → Fin (d + 1) → ℂ)
    (hfull :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z) = d + 1) :
    ∃ ι : Fin (d + 1) ↪ Fin n, sourceFullFrameDet d n ι z ≠ 0 := by
  have hrank_le_n :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z) ≤ n :=
    by
      simpa [sourceGramMatrixRank] using
        (Matrix.rank_le_width
          (A := Matrix.of fun i j : Fin n => sourceMinkowskiGram d n z i j))
  have hn : d + 1 ≤ n := by
    simpa [hfull] using hrank_le_n
  have hmax : HWSourceGramMaxRankAt d n z := by
    simp [HWSourceGramMaxRankAt, HWSourceGramMaxRank, hfull,
      Nat.min_eq_left hn]
  have hreg : SourceComplexGramRegularAt d n z :=
    sourceComplexGramRegularAt_of_HWSourceGramMaxRankAt d n hn hmax
  exact exists_sourceFullFrameDet_ne_zero_of_sourceComplexGramRegularAt
    d n hn hreg

/-- Equality of oriented source invariants supplies the determinant
compatibility required for the determinant-`1` same-Gram extension branch. -/
theorem sourceOriented_soCompatible_of_sameInvariant
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w)
    (horiented :
      sourceOrientedMinkowskiInvariant d n z =
        sourceOrientedMinkowskiInvariant d n w) :
    HWSameSourceGramSOOrientationCompatible d n z w := by
  by_cases hlt :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z) < d + 1
  · exact Or.inl hlt
  · have hle :
        sourceGramMatrixRank n (sourceMinkowskiGram d n z) ≤ d + 1 :=
      le_trans (sourceGramMatrixRank_le_spacetime_source_min d n z)
        (min_le_left (d + 1) n)
    have hfull :
        sourceGramMatrixRank n (sourceMinkowskiGram d n z) = d + 1 :=
      le_antisymm hle (Nat.le_of_not_lt hlt)
    rcases exists_sourceFullFrameDet_ne_zero_of_sourceGramRank_eq_spacetime
        d n z hfull with
      ⟨ι, hι⟩
    right
    calc
      HWFullRankSameGramFrameMapDet d n z w =
          sourceFullFrameDet d n ι w / sourceFullFrameDet d n ι z :=
            hwFullRankSameGramFrameMapDet_eq_det_ratio_of_fullFrame
              d n hfull hgram ι hι
      _ = sourceFullFrameDet d n ι z / sourceFullFrameDet d n ι z := by
            rw [← same_sourceOrientedInvariant_fullFrameDet
              (d := d) (n := n) horiented ι]
      _ = 1 := div_self hι

/-- If the selected same-Gram full-frame map has determinant one, it is
realized by a proper complex Lorentz transformation on all source vectors. -/
theorem sourceFullFrameMap_complexLorentzVectorAction_of_det_one
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w)
    (ι : Fin (d + 1) ↪ Fin n)
    (hι : sourceFullFrameDet d n ι z ≠ 0)
    (hdet : LinearMap.det (sourceFullFrameMap d n hgram ι hι).toLinearMap = 1) :
    ∃ Λ : ComplexLorentzGroup d,
      ∀ i, complexLorentzVectorAction Λ (z i) = w i := by
  let E := sourceFullFrameMap d n hgram ι hι
  have hpres : ∀ x y,
      sourceComplexMinkowskiInner d (E x) (E y) =
        sourceComplexMinkowskiInner d x y :=
    sourceFullFrameMap_preserves_inner d n hgram ι hι
  let Λ := complexLorentzGroupOfLinearEquivPreservesInner d E hpres hdet
  refine ⟨Λ, ?_⟩
  intro i
  calc
    complexLorentzVectorAction Λ (z i) = E (z i) := by
      exact complexLorentzVectorAction_ofLinearEquivPreservesInner
        d E hpres hdet (z i)
    _ = w i := sourceFullFrameMap_apply_all d n hgram ι hι i

/-- Tuple-level version of
`sourceFullFrameMap_complexLorentzVectorAction_of_det_one`. -/
theorem sourceFullFrameMap_complexLorentzOrbit_of_det_one
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w)
    (ι : Fin (d + 1) ↪ Fin n)
    (hι : sourceFullFrameDet d n ι z ≠ 0)
    (hdet : LinearMap.det (sourceFullFrameMap d n hgram ι hι).toLinearMap = 1) :
    ∃ Λ : ComplexLorentzGroup d, w = complexLorentzAction Λ z := by
  rcases sourceFullFrameMap_complexLorentzVectorAction_of_det_one
      d n hgram ι hι hdet with
    ⟨Λ, hΛ⟩
  refine ⟨Λ, ?_⟩
  funext i
  exact (hΛ i).symm

/-- Full ambient-rank oriented same-invariant configurations lie in the same
proper complex Lorentz orbit. -/
theorem sourceOriented_fullRank_detOneOrbit_of_sameInvariant
    (d n : ℕ)
    {z w : Fin n → Fin (d + 1) → ℂ}
    (hfull :
      sourceGramMatrixRank n (sourceMinkowskiGram d n z) = d + 1)
    (hgram : sourceMinkowskiGram d n z = sourceMinkowskiGram d n w)
    (horiented :
      sourceOrientedMinkowskiInvariant d n z =
        sourceOrientedMinkowskiInvariant d n w) :
    ∃ Λ : ComplexLorentzGroup d, w = complexLorentzAction Λ z := by
  rcases exists_sourceFullFrameDet_ne_zero_of_sourceGramRank_eq_spacetime
      d n z hfull with
    ⟨ι, hι⟩
  have hratio :
      sourceFullFrameDet d n ι w / sourceFullFrameDet d n ι z = 1 := by
    rw [← same_sourceOrientedInvariant_fullFrameDet
      (d := d) (n := n) horiented ι]
    exact div_self hι
  have hdet :
      LinearMap.det (sourceFullFrameMap d n hgram ι hι).toLinearMap = 1 := by
    rw [det_sourceFullFrameMap_eq_ratio d n hgram ι hι, hratio]
  exact sourceFullFrameMap_complexLorentzOrbit_of_det_one d n hgram ι hι hdet

/-- In the hard range, every oriented max-rank source-variety point lies on
some selected full-frame determinant-nonzero sheet. -/
theorem exists_selectedDetNonzero_of_sourceOrientedMaxRankAt
    {d n : ℕ}
    (hn : d + 1 ≤ n)
    {G0 : SourceOrientedGramData d n}
    (hG0 : G0 ∈ sourceOrientedGramVariety d n)
    (hmax : SourceOrientedMaxRankAt d n G0) :
    ∃ ι : Fin (d + 1) ↪ Fin n, G0.det ι ≠ 0 := by
  let z : Fin n → Fin (d + 1) → ℂ := Classical.choose hG0
  have hz : sourceOrientedMinkowskiInvariant d n z = G0 :=
    Classical.choose_spec hG0
  have hmax_z :
      SourceOrientedMaxRankAt d n (sourceOrientedMinkowskiInvariant d n z) := by
    simpa [hz] using hmax
  have hHW : HWSourceGramMaxRankAt d n z :=
    (sourceOrientedMaxRankAt_invariant_iff_hwSourceGramMaxRankAt d n z).1 hmax_z
  have hreg : SourceComplexGramRegularAt d n z :=
    sourceComplexGramRegularAt_of_HWSourceGramMaxRankAt d n hn hHW
  rcases exists_sourceFullFrameDet_ne_zero_of_sourceComplexGramRegularAt
      d n hn hreg with
    ⟨ι, hdetz⟩
  refine ⟨ι, ?_⟩
  have hdetz' : (sourceOrientedMinkowskiInvariant d n z).det ι ≠ 0 := by
    simpa [sourceOrientedMinkowskiInvariant, SourceOrientedGramData.det] using hdetz
  simpa [hz] using hdetz'

/-- In the hard range, oriented max rank supplies the finite-coordinate
max-rank chart packet expected by the local connected-basis layer. -/
noncomputable def sourceOrientedMaxRankChartData_of_maxRankAt_fullFrame
    {d n : ℕ}
    (hn : d + 1 ≤ n)
    {G0 : SourceOrientedGramData d n}
    (hG0 : G0 ∈ sourceOrientedGramVariety d n)
    (hmax : SourceOrientedMaxRankAt d n G0) :
    Σ m : ℕ, SourceOrientedMaxRankChartData d n (M := Fin m → ℂ) G0 := by
  let hex := exists_selectedDetNonzero_of_sourceOrientedMaxRankAt hn hG0 hmax
  let ι : Fin (d + 1) ↪ Fin n := Classical.choose hex
  have hdet : G0.det ι ≠ 0 := Classical.choose_spec hex
  exact sourceOrientedMaxRankChartData_of_selectedDetNonzero ι hG0 hdet

/-- Hard-range local connected-basis adapter: the full-frame producer closes
the max-rank chart input, leaving only the exceptional-rank local-image
producer. -/
theorem sourceOrientedGramVariety_local_connectedRelOpen_basis_of_fullFrameMaxRank_and_localImage
    {d n : ℕ}
    (hn : d + 1 ≤ n)
    (rankDeficientLocalImageAt :
      ∀ {G0 : SourceOrientedGramData d n},
        G0 ∈ sourceOrientedGramVariety d n →
        SourceOrientedExceptionalRank d n G0 →
        ∀ {N0 : Set (SourceOrientedGramData d n)},
          IsOpen N0 → G0 ∈ N0 →
          Σ P : Type, Σ _ : TopologicalSpace P,
            SourceOrientedRankDeficientVarietyLocalImageData
              (d := d) (n := n) (P := P) G0 N0)
    {G0 : SourceOrientedGramData d n}
    (hG0 : G0 ∈ sourceOrientedGramVariety d n)
    {N0 : Set (SourceOrientedGramData d n)}
    (hN0_open : IsOpen N0)
    (hG0N0 : G0 ∈ N0) :
    ∃ V : Set (SourceOrientedGramData d n),
      G0 ∈ V ∧
      IsRelOpenInSourceOrientedGramVariety d n V ∧
      IsConnected V ∧
      V ⊆ N0 ∩ sourceOrientedGramVariety d n := by
  exact
    sourceOrientedGramVariety_local_connectedRelOpen_basis_of_chart_and_localImage_producers
      (d := d) (n := n)
      (fun {G} hG hmax =>
        sourceOrientedMaxRankChartData_of_maxRankAt_fullFrame hn hG hmax)
      rankDeficientLocalImageAt hG0 hN0_open hG0N0

/-- Hard-range connected-component adapter using the full-frame max-rank
producer and the supplied exceptional-rank local-image producer. -/
theorem sourceOrientedGramVariety_connectedComponentIn_relOpen_of_fullFrameMaxRank_and_localImage
    {d n : ℕ}
    (hn : d + 1 ≤ n)
    (rankDeficientLocalImageAt :
      ∀ {G0 : SourceOrientedGramData d n},
        G0 ∈ sourceOrientedGramVariety d n →
        SourceOrientedExceptionalRank d n G0 →
        ∀ {N0 : Set (SourceOrientedGramData d n)},
          IsOpen N0 → G0 ∈ N0 →
          Σ P : Type, Σ _ : TopologicalSpace P,
            SourceOrientedRankDeficientVarietyLocalImageData
              (d := d) (n := n) (P := P) G0 N0)
    {D : Set (SourceOrientedGramData d n)}
    (hD_rel : IsRelOpenInSourceOrientedGramVariety d n D)
    {G0 : SourceOrientedGramData d n}
    (hG0D : G0 ∈ D) :
    IsRelOpenInSourceOrientedGramVariety d n
      (connectedComponentIn D G0) := by
  exact
    sourceOrientedGramVariety_connectedComponentIn_relOpen_of_chart_and_localImage_producers
      (d := d) (n := n)
      (fun {G} hG hmax =>
        sourceOrientedMaxRankChartData_of_maxRankAt_fullFrame hn hG hmax)
      rankDeficientLocalImageAt hD_rel hG0D

/-- Hard-range compact-path tube adapter using the full-frame max-rank
producer and the supplied exceptional-rank local-image producer. -/
theorem sourceOrientedGramVariety_connectedRelOpenTube_around_compactPath_of_fullFrameMaxRank_and_localImage
    {d n : ℕ}
    (hn : d + 1 ≤ n)
    (rankDeficientLocalImageAt :
      ∀ {G0 : SourceOrientedGramData d n},
        G0 ∈ sourceOrientedGramVariety d n →
        SourceOrientedExceptionalRank d n G0 →
        ∀ {N0 : Set (SourceOrientedGramData d n)},
          IsOpen N0 → G0 ∈ N0 →
          Σ P : Type, Σ _ : TopologicalSpace P,
            SourceOrientedRankDeficientVarietyLocalImageData
              (d := d) (n := n) (P := P) G0 N0)
    {D : Set (SourceOrientedGramData d n)}
    (hD_rel : IsRelOpenInSourceOrientedGramVariety d n D)
    {γ : unitInterval → SourceOrientedGramData d n}
    (hγ_cont : Continuous γ)
    (hγD : ∀ t, γ t ∈ D)
    {W0 : Set (SourceOrientedGramData d n)}
    (hW0_rel : IsRelOpenInSourceOrientedGramVariety d n W0)
    (hW0_conn : IsConnected W0)
    (hW0_nonempty : W0.Nonempty)
    (hW0D : W0 ⊆ D)
    (hstart : γ (0 : unitInterval) ∈ W0) :
    ∃ Wtube : Set (SourceOrientedGramData d n),
      IsRelOpenInSourceOrientedGramVariety d n Wtube ∧
      IsConnected Wtube ∧
      W0 ⊆ Wtube ∧
      Wtube ⊆ D ∧
      (∀ t, γ t ∈ Wtube) := by
  exact
    sourceOrientedGramVariety_connectedRelOpenTube_around_compactPath_of_chart_and_localImage_producers
      (d := d) (n := n)
      (fun {G} hG hmax =>
        sourceOrientedMaxRankChartData_of_maxRankAt_fullFrame hn hG hmax)
      rankDeficientLocalImageAt hD_rel hγ_cont hγD hW0_rel hW0_conn
      hW0_nonempty hW0D hstart

end BHW
