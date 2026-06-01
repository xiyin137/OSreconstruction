import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedRealUniqueness
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedFullFrameExplicitSlice

/-!
# Real-compatible full-frame chart data

This file contains the mechanical packaging layer for the hard full-frame real
chart theorem.  The remaining analytic input is the construction of the
real-compatible slice and real/complex implicit chart data; once that data is
available, the conversion to `SourceOrientedLocalRealChartData` is formal.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

/-- Complexifying a real selected full-frame matrix complexifies its
determinant. -/
theorem sourceRealFullFrameMatrix_map_ofReal_det
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (x : Fin n → Fin (d + 1) → ℝ) :
    ((sourceRealFullFrameMatrix d n ι x).map Complex.ofReal).det =
      (sourceRealFullFrameDet d n ι x : ℂ) := by
  rw [sourceRealFullFrameDet]
  exact
    (RingHom.map_det Complex.ofRealHom
      (sourceRealFullFrameMatrix d n ι x)
    ).symm

/-- A nonzero real selected full-frame determinant remains a unit after
complexifying the selected full-frame matrix. -/
theorem sourceRealFullFrameMatrix_map_ofReal_det_isUnit
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    {x : Fin n → Fin (d + 1) → ℝ}
    (hdet : sourceRealFullFrameDet d n ι x ≠ 0) :
    IsUnit ((sourceRealFullFrameMatrix d n ι x).map Complex.ofReal).det := by
  rw [sourceRealFullFrameMatrix_map_ofReal_det]
  exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hdet)

set_option synthInstance.maxHeartbeats 120000 in
set_option maxHeartbeats 300000 in
/-- The determinant-coordinate direction is transverse to the symmetric
full-frame equation at a complexified real full-frame base. -/
theorem sourceFullFrameRealCompatibleSymmetricDetDirection_ne_zero
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det) :
    sourceFullFrameSymmetricEquationDerivCLM d
      (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))
      (sourceFullFrameSymmetricDetDirection d) ≠ 0 := by
  simpa [sourceFullFrameSymmetricEquationDerivCLM,
    sourceFullFrameOrientedGramCoord] using
      sourceFullFrameOrientedEquation_fderiv_detDirection_ne_zero
        (d := d) (H0 := sourceFullFrameOrientedGram d (M0R.map Complex.ofReal))
        (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R).ne_zero

set_option synthInstance.maxHeartbeats 100000 in
/-- The determinant-direction derivative scalar at a complexified real
full-frame base is itself the complexification of the corresponding real
scalar. -/
theorem sourceFullFrameRealCompatibleSymmetricDetDirection_scalar
    (d : ℕ)
    (M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    sourceFullFrameSymmetricEquationDerivCLM d
      (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))
      (sourceFullFrameSymmetricDetDirection d) =
      -((2 : ℂ) * minkowskiMetricDet d * ((M0R.det : ℝ) : ℂ)) := by
  have h := sourceFullFrameOrientedEquation_fderiv_detDirection
    (d := d) (H0 := sourceFullFrameOrientedGram d (M0R.map Complex.ofReal))
  simpa [sourceFullFrameSymmetricEquationDerivCLM,
    sourceFullFrameOrientedGramCoord, sourceFullFrameSymmetricDetDirection,
    sourceFullFrameDetDirection, sourceFullFrameOrientedGram,
    sourceFullFrame_matrix_map_ofReal_det] using h

/-- The determinant-direction derivative scalar has zero imaginary part at a
complexified real full-frame base. -/
theorem sourceFullFrameRealCompatibleSymmetricDetDirection_scalar_im
    (d : ℕ)
    (M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    Complex.im (sourceFullFrameSymmetricEquationDerivCLM d
      (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))
      (sourceFullFrameSymmetricDetDirection d)) = 0 := by
  rw [sourceFullFrameRealCompatibleSymmetricDetDirection_scalar]
  rw [minkowskiMetricDet_eq_ofReal_minkowskiMatrix_det]
  simp

set_option synthInstance.maxHeartbeats 120000 in
set_option maxHeartbeats 400000 in
/-- Explicit kernel projection for the symmetric full-frame equation at a
complexified real base, using the determinant-coordinate direction as the
chosen transverse complement.  Unlike the arbitrary closed-complement
projection used in the generic complex chart, this projection is algebraic and
is the one intended for the real-compatible chart route. -/
noncomputable def sourceFullFrameRealCompatibleKernelProjection
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det) :
    sourceFullFrameSymmetricCoordSubmodule d →L[ℂ]
      (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker := by
  let L := sourceFullFrameSymmetricEquationDerivCLM d
      (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))
  let u := sourceFullFrameSymmetricDetDirection d
  let a : ℂ := L u
  have ha : a ≠ 0 := by
    simpa [L, u, a] using
      sourceFullFrameRealCompatibleSymmetricDetDirection_ne_zero d hM0R
  let P : sourceFullFrameSymmetricCoordSubmodule d →L[ℂ]
      sourceFullFrameSymmetricCoordSubmodule d :=
    ContinuousLinearMap.id ℂ (sourceFullFrameSymmetricCoordSubmodule d) -
      (1 / a) • (ContinuousLinearMap.smulRight L u)
  refine P.codRestrict L.ker ?_
  intro H
  change L (P H) = 0
  simp [P, ContinuousLinearMap.smulRight_apply]
  rw [show L u = a by rfl]
  field_simp [ha]
  ring

set_option synthInstance.maxHeartbeats 120000 in
@[simp]
theorem sourceFullFrameRealCompatibleKernelProjection_apply_ker
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (K : (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker) :
    sourceFullFrameRealCompatibleKernelProjection d hM0R K = K := by
  let L := sourceFullFrameSymmetricEquationDerivCLM d
      (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))
  have hK : L (K : sourceFullFrameSymmetricCoordSubmodule d) = 0 := K.property
  apply Subtype.ext
  change ((sourceFullFrameRealCompatibleKernelProjection d hM0R) K :
      sourceFullFrameSymmetricCoordSubmodule d) = K
  simp [sourceFullFrameRealCompatibleKernelProjection, L,
    ContinuousLinearMap.smulRight_apply, hK]

/-- The explicit real-compatible kernel-coordinate map on the named full-frame
gauge slice.  It uses the determinant-direction projection above instead of
the arbitrary closed-complement projection in the generic complex implicit
chart. -/
noncomputable def sourceFullFrameRealCompatibleExplicitKernelMap
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det) :
    (sourceFullFrameExplicitGaugeSliceData d
      (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)).slice →
      (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker :=
  fun X =>
    sourceFullFrameRealCompatibleKernelProjection d hM0R
      (sourceFullFrameGaugeSliceMapSymmetric d (M0R.map Complex.ofReal)
        (sourceFullFrameExplicitGaugeSliceData d
          (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)) X -
        sourceFullFrameSymmetricBase d (M0R.map Complex.ofReal))

set_option synthInstance.maxHeartbeats 100000 in
@[simp]
theorem sourceFullFrameRealCompatibleExplicitKernelMap_zero
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det) :
    sourceFullFrameRealCompatibleExplicitKernelMap d hM0R 0 = 0 := by
  simp [sourceFullFrameRealCompatibleExplicitKernelMap]

/-- Finite-coordinate equivalence from the real-form explicit slice coordinates
to the implicit-kernel target.  This is the complex-linear normalization used
by the real-compatible implicit chart: explicit slice coordinates are first
sent to the named complex gauge slice, then through the checked derivative of
the implicit-kernel map. -/
noncomputable def sourceFullFrameRealSliceKernelCoordEquiv
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    (Fin F.realModelDim → ℂ) ≃L[ℂ]
      (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker :=
  F.complexCoordEquiv.trans
    (sourceFullFrameGaugeSliceKernelDerivContinuousLinearEquiv d
      (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)
      (sourceFullFrameExplicitGaugeSliceData d
        (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)))

/-- The complex implicit-kernel map written in the finite coordinates supplied
by the real-form explicit slice.  Its derivative at the origin is the identity;
the real-compatible producer will apply the real inverse-function theorem to
the real form of this map. -/
noncomputable def sourceFullFrameRealSliceNormalizedImplicitKernelMap
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    (Fin F.realModelDim → ℂ) → (Fin F.realModelDim → ℂ) :=
  fun q =>
    (sourceFullFrameRealSliceKernelCoordEquiv d hM0R F).symm
      (sourceFullFrameGaugeSliceImplicitKernelMap d
        (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R)
        (sourceFullFrameExplicitGaugeSliceData d
          (sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R))
        (F.complexCoordEquiv q))

set_option synthInstance.maxHeartbeats 100000 in
@[simp]
theorem sourceFullFrameRealSliceNormalizedImplicitKernelMap_zero
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    sourceFullFrameRealSliceNormalizedImplicitKernelMap d hM0R F 0 = 0 := by
  simp [sourceFullFrameRealSliceNormalizedImplicitKernelMap,
    sourceFullFrameRealSliceKernelCoordEquiv]

set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 400000 in
/-- The normalized complex implicit-kernel map has identity strict derivative
at the origin.  This is the finite-coordinate theorem that the real-compatible
producer must real-form and feed to the real inverse-function theorem. -/
theorem sourceFullFrameRealSliceNormalizedImplicitKernelMap_hasStrictFDerivAt
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    HasStrictFDerivAt
      (sourceFullFrameRealSliceNormalizedImplicitKernelMap d hM0R F)
      (1 : (Fin F.realModelDim → ℂ) →L[ℂ] (Fin F.realModelDim → ℂ)) 0 := by
  let hM0C := sourceFullFrame_matrix_map_ofReal_det_isUnit d hM0R
  let S := sourceFullFrameExplicitGaugeSliceData d hM0C
  let K := (sourceFullFrameSymmetricEquationDerivCLM d
    (sourceFullFrameOrientedGramCoord d (M0R.map Complex.ofReal))).ker
  let E := sourceFullFrameRealSliceKernelCoordEquiv d hM0R F
  let Es : K →L[ℂ] (Fin F.realModelDim → ℂ) := E.symm
  let f := sourceFullFrameGaugeSliceImplicitKernelMap d hM0C S
  let c : (Fin F.realModelDim → ℂ) →L[ℂ] S.slice := F.complexCoordEquiv
  let e : S.slice ≃L[ℂ] K :=
    sourceFullFrameGaugeSliceKernelDerivContinuousLinearEquiv d hM0C S
  have hf : HasStrictFDerivAt f (e : S.slice →L[ℂ] K) 0 := by
    simpa [f, e, S, hM0C] using
      sourceFullFrameGaugeSliceImplicitKernelMap_hasStrictFDerivAt d hM0C S
  have hc : HasStrictFDerivAt (fun q : Fin F.realModelDim → ℂ => c q) c
      (0 : Fin F.realModelDim → ℂ) :=
    c.hasStrictFDerivAt
  have hc0 : c (0 : Fin F.realModelDim → ℂ) = 0 := by
    simp [c]
  have hf0 : HasStrictFDerivAt f (e : S.slice →L[ℂ] K)
      (c (0 : Fin F.realModelDim → ℂ)) := by
    simpa [hc0] using hf
  have hfc : HasStrictFDerivAt (fun q : Fin F.realModelDim → ℂ => f (c q))
      ((e : S.slice →L[ℂ] K).comp c) (0 : Fin F.realModelDim → ℂ) := by
    simpa using
      (HasStrictFDerivAt.comp (𝕜 := ℂ) (x := (0 : Fin F.realModelDim → ℂ))
        (g := f) (f := fun q : Fin F.realModelDim → ℂ => c q) hf0 hc)
  have hsymm : HasStrictFDerivAt
      (Es : K → (Fin F.realModelDim → ℂ)) Es
      (0 : K) :=
    ContinuousLinearMap.hasStrictFDerivAt Es (x := (0 : K))
  have hf_zero : f 0 = 0 := by
    simp [f, S]
  have hf_c0 : f (c (0 : Fin F.realModelDim → ℂ)) = 0 := by
    rw [hc0]
    exact hf_zero
  have hsymm0 : HasStrictFDerivAt
      (Es : K → (Fin F.realModelDim → ℂ)) Es
      (f (c (0 : Fin F.realModelDim → ℂ))) := by
    rw [hf_c0]
    exact hsymm
  have hcomp : HasStrictFDerivAt
      (fun q : Fin F.realModelDim → ℂ => E.symm (f (c q)))
      (Es.comp
        ((e : S.slice →L[ℂ] K).comp c)) (0 : Fin F.realModelDim → ℂ) := by
    simpa using
      (HasStrictFDerivAt.comp (𝕜 := ℂ) (x := (0 : Fin F.realModelDim → ℂ))
        (g := (Es : K → (Fin F.realModelDim → ℂ)))
        (f := fun q : Fin F.realModelDim → ℂ => f (c q)) hsymm0 hfc)
  have hfun :
      (fun q : Fin F.realModelDim → ℂ => E.symm (f (c q))) =
        sourceFullFrameRealSliceNormalizedImplicitKernelMap d hM0R F := by
    funext q
    rfl
  have hderiv :
      (Es.comp
        ((e : S.slice →L[ℂ] K).comp c)) =
        (1 : (Fin F.realModelDim → ℂ) →L[ℂ] (Fin F.realModelDim → ℂ)) := by
    apply ContinuousLinearMap.ext
    intro q
    change Es (e (c q)) = q
    rw [show Es (e (c q)) =
        F.complexCoordEquiv.symm (e.symm (e (F.complexCoordEquiv q))) by
      rfl]
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact ContinuousLinearEquiv.symm_apply_apply F.complexCoordEquiv q
  simpa [hfun, hderiv] using hcomp

set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 400000 in
/-- The local inverse-function chart for the normalized finite-coordinate
implicit-kernel map.  The derivative theorem above makes this an honest local
chart at the origin with identity linear part. -/
noncomputable def sourceFullFrameRealSliceNormalizedImplicitKernelOpenPartialHomeomorph
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    OpenPartialHomeomorph (Fin F.realModelDim → ℂ) (Fin F.realModelDim → ℂ) := by
  let f := sourceFullFrameRealSliceNormalizedImplicitKernelMap d hM0R F
  let e : (Fin F.realModelDim → ℂ) ≃L[ℂ] (Fin F.realModelDim → ℂ) :=
    ContinuousLinearEquiv.refl ℂ (Fin F.realModelDim → ℂ)
  have hderiv : HasStrictFDerivAt f
      (e : (Fin F.realModelDim → ℂ) →L[ℂ] (Fin F.realModelDim → ℂ)) 0 := by
    simpa [f, e] using
      sourceFullFrameRealSliceNormalizedImplicitKernelMap_hasStrictFDerivAt
        d hM0R F
  exact
    @HasStrictFDerivAt.toOpenPartialHomeomorph ℂ _
      (Fin F.realModelDim → ℂ) _ _ (Fin F.realModelDim → ℂ) _ _
      f e 0 inferInstance hderiv

@[simp]
theorem sourceFullFrameRealSliceNormalizedImplicitKernelOpenPartialHomeomorph_coe
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    (sourceFullFrameRealSliceNormalizedImplicitKernelOpenPartialHomeomorph
      d hM0R F : (Fin F.realModelDim → ℂ) → (Fin F.realModelDim → ℂ)) =
      sourceFullFrameRealSliceNormalizedImplicitKernelMap d hM0R F := by
  rfl

set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 400000 in
/-- The normalized finite-coordinate implicit-kernel chart contains the origin
in its source. -/
theorem sourceFullFrameRealSliceNormalizedImplicitKernel_zero_mem_chartSource
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    (0 : Fin F.realModelDim → ℂ) ∈
      (sourceFullFrameRealSliceNormalizedImplicitKernelOpenPartialHomeomorph
        d hM0R F).source := by
  let f := sourceFullFrameRealSliceNormalizedImplicitKernelMap d hM0R F
  let e : (Fin F.realModelDim → ℂ) ≃L[ℂ] (Fin F.realModelDim → ℂ) :=
    ContinuousLinearEquiv.refl ℂ (Fin F.realModelDim → ℂ)
  have hderiv : HasStrictFDerivAt f
      (e : (Fin F.realModelDim → ℂ) →L[ℂ] (Fin F.realModelDim → ℂ)) 0 := by
    simpa [f, e] using
      sourceFullFrameRealSliceNormalizedImplicitKernelMap_hasStrictFDerivAt
        d hM0R F
  unfold sourceFullFrameRealSliceNormalizedImplicitKernelOpenPartialHomeomorph
  simp only [HasStrictFDerivAt.toOpenPartialHomeomorph,
    ApproximatesLinearOn.toOpenPartialHomeomorph_source]
  exact (Classical.choose_spec hderiv.approximates_deriv_on_open_nhds).1

/-- The normalized finite-coordinate implicit-kernel chart contains the origin
in its target. -/
theorem sourceFullFrameRealSliceNormalizedImplicitKernel_zero_mem_chartTarget
    (d : ℕ)
    {M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hM0R : IsUnit M0R.det)
    (F : SourceFullFrameRealSliceFiniteCoordData d M0R hM0R) :
    (0 : Fin F.realModelDim → ℂ) ∈
      (sourceFullFrameRealSliceNormalizedImplicitKernelOpenPartialHomeomorph
        d hM0R F).target := by
  have hsource :=
    sourceFullFrameRealSliceNormalizedImplicitKernel_zero_mem_chartSource
      d hM0R F
  have htarget :=
    (sourceFullFrameRealSliceNormalizedImplicitKernelOpenPartialHomeomorph
      d hM0R F).map_source hsource
  simpa using htarget

/-- An open partial homeomorphism from a frame space to product coordinates
makes the first product coordinate, crossed with an unchanged tail coordinate,
locally open on its source.  This is the pure-topology bridge used by the
selected-frame product chart in the real full-frame producer. -/
theorem isOpen_product_first_id_image_of_openPartialHomeomorph
    {Frame K O Tail : Type*}
    [TopologicalSpace Frame] [TopologicalSpace K] [TopologicalSpace O]
    [TopologicalSpace Tail]
    (e : OpenPartialHomeomorph Frame (K × O))
    {V : Set (Frame × Tail)}
    (hV_open : IsOpen V)
    (hV_sub : V ⊆ {p : Frame × Tail | p.1 ∈ e.source}) :
    IsOpen ((fun p : Frame × Tail => ((e p.1).1, p.2)) '' V) := by
  let eprod := e.prod (OpenPartialHomeomorph.refl Tail)
  have hV_sub' : V ⊆ eprod.source := by
    intro p hp
    change p.1 ∈ e.source ∧
      p.2 ∈ (OpenPartialHomeomorph.refl Tail).source
    exact ⟨hV_sub hp, by simp⟩
  have h_img : IsOpen (eprod '' V) :=
    eprod.isOpen_image_of_subset_source hV_open hV_sub'
  have hproj : IsOpenMap (fun q : (K × O) × Tail => (q.1.1, q.2)) := by
    simpa using
      (isOpenMap_fst (X := K) (Y := O)).prodMap
        (IsOpenMap.id : IsOpenMap (id : Tail → Tail))
  have hEq :
      ((fun p : Frame × Tail => ((e p.1).1, p.2)) '' V) =
        (fun q : (K × O) × Tail => (q.1.1, q.2)) '' (eprod '' V) := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(e p.1, p.2), ⟨p, hp, by simp [eprod]⟩, rfl⟩
    · rintro ⟨q, ⟨p, hp, hpq⟩, hqy⟩
      refine ⟨p, hp, ?_⟩
      subst hpq
      subst hqy
      simp [eprod]
  rw [hEq]
  exact hproj _ h_img

/-- A real gauge-slice packet whose complexification is the complex full-frame
gauge slice used by the existing full-frame max-rank chart. -/
structure SourceFullFrameRealGaugeSliceData
    (d : ℕ)
    (M0R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (_hM0R : M0R.det ≠ 0) where
  M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := M0R.map Complex.ofReal
  M0_det_unit : IsUnit M0.det
  complexSlice : SourceFullFrameGaugeSliceData d M0
  realModelDim : ℕ
  realModelToComplexSlice :
    (Fin realModelDim → ℂ) ≃L[ℂ] complexSlice.slice
  realKernelCoord :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ → Fin realModelDim → ℝ
  complexKernelCoord :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ → complexSlice.slice
  complexKernelCoord_real_eq :
    ∀ M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ,
      complexKernelCoord (M.map Complex.ofReal) =
        realModelToComplexSlice (SCV.realToComplex (realKernelCoord M))
  frameDomain : Set (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
  frameDomain_open : IsOpen frameDomain
  center_mem_frameDomain : M0R ∈ frameDomain
  frameDomain_det_nonzero : frameDomain ⊆ {M | M.det ≠ 0}
  realKernelCoord_continuousOn : ContinuousOn realKernelCoord frameDomain

/-- The real kernel coordinate together with the selected mixed-row coordinates
of a source tuple.  This is the raw real coordinate map before applying the
finite coordinate equivalence in `SourceFullFrameRealCompatibleImplicitChartData`. -/
def sourceFullFrameRealKernelMixedCoord
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    (S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet)
    (x : Fin n → Fin (d + 1) → ℝ) :
    (Fin S.realModelDim → ℝ) ×
      (sourceComplementIndex ι → Fin (d + 1) → ℝ) :=
  (S.realKernelCoord (sourceRealFullFrameMatrix d n ι x),
    sourceRealSelectedMixedRows d n ι x)

/-- The mixed Gram rows computed from split real source coordinates: pair each
complement row with each selected-frame row. -/
def sourceFullFrameRealSplitMixedRows
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    (p :
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
        (sourceComplementIndex ι → Fin (d + 1) → ℝ)) :
    sourceComplementIndex ι → Fin (d + 1) → ℝ :=
  fun k a => MinkowskiSpace.minkowskiInner d (p.2 k) (p.1 a)

/-- Matrix inversion is continuous on the real determinant-nonzero locus. -/
theorem continuousOn_matrix_inv_of_det_ne_zero_real
    {q : Type*} [Fintype q] [DecidableEq q] :
    ContinuousOn (fun A : Matrix q q ℝ => A⁻¹)
      {A : Matrix q q ℝ | A.det ≠ 0} := by
  intro A hA
  have hcont : ContinuousAt (fun z : ℝ => Ring.inverse z) A.det := by
    simpa [Ring.inverse_eq_inv] using
      (ContinuousInv₀.continuousAt_inv₀ hA : ContinuousAt Inv.inv A.det)
  exact (continuousAt_matrix_inv A hcont).continuousWithinAt

/-- The inverse matrix is continuous when the determinant-nonzero condition is
part of the domain. -/
theorem continuous_subtype_matrix_inv_of_det_ne_zero_real
    {q : Type*} [Fintype q] [DecidableEq q] :
    Continuous
      (fun A : {A : Matrix q q ℝ // A.det ≠ 0} =>
        (A : Matrix q q ℝ)⁻¹) := by
  rw [continuous_iff_continuousAt]
  intro A
  have hcont : ContinuousAt (fun z : ℝ => Ring.inverse z) (A : Matrix q q ℝ).det := by
    simpa [Ring.inverse_eq_inv] using
      (ContinuousInv₀.continuousAt_inv₀ A.property :
        ContinuousAt Inv.inv (A : Matrix q q ℝ).det)
  exact
    (continuousAt_matrix_inv (A : Matrix q q ℝ) hcont).comp
      continuous_subtype_val.continuousAt

/-- Explicit inverse to the split mixed-row map on determinant-nonzero frames. -/
noncomputable def sourceFullFrameRealSplitMixedRowsInv
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    (p :
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
        (sourceComplementIndex ι → Fin (d + 1) → ℝ)) :
    sourceComplementIndex ι → Fin (d + 1) → ℝ :=
  fun k =>
    Matrix.toLin'
      (LorentzLieGroup.minkowskiMatrix d * p.1⁻¹) (p.2 k)

/-- The explicit inverse is the inverse of the checked rowwise mixed-row
linear equivalence. -/
theorem sourceFullFrameRealSplitMixedRowsInv_eq_tailMixedRowsLinearEquiv_symm
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    (p :
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
        (sourceComplementIndex ι → Fin (d + 1) → ℝ))
    (hp : p.1.det ≠ 0) :
    sourceFullFrameRealSplitMixedRowsInv p =
      (sourceRealFullFrameTailMixedRowsLinearEquiv d n ι p.1 hp).symm p.2 := by
  rfl

/-- On determinant-nonzero selected frames, the split mixed-row component is
the checked rowwise linear equivalence from complement rows to mixed Gram
rows. -/
theorem sourceFullFrameRealSplitMixedRows_eq_tailMixedRowsLinearEquiv
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    (p :
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
        (sourceComplementIndex ι → Fin (d + 1) → ℝ))
    (hp : p.1.det ≠ 0) :
    sourceFullFrameRealSplitMixedRows p =
      sourceRealFullFrameTailMixedRowsLinearEquiv d n ι p.1 hp p.2 := by
  ext k a
  rw [sourceRealFullFrameTailMixedRowsLinearEquiv_apply]
  rw [sourceRealFullFrameMixedRowLinearEquiv_apply]
  simp [sourceFullFrameRealSplitMixedRows,
    MinkowskiSpace.minkowskiInner, mul_comm]

/-- Split coordinates with determinant-nonzero selected-frame component. -/
abbrev sourceFullFrameRealSplitDetNonzero
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n) :=
  {p :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
      (sourceComplementIndex ι → Fin (d + 1) → ℝ) // p.1.det ≠ 0}

/-- On the determinant-nonzero split domain, replacing complement rows by
mixed rows is a homeomorphism. -/
noncomputable def sourceFullFrameRealSplitMixedRowsHomeomorph
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n) :
    sourceFullFrameRealSplitDetNonzero d n ι ≃ₜ
      sourceFullFrameRealSplitDetNonzero d n ι where
  toFun p :=
    ⟨(p.1.1, sourceFullFrameRealSplitMixedRows p.1), p.property⟩
  invFun p :=
    ⟨(p.1.1, sourceFullFrameRealSplitMixedRowsInv p.1), p.property⟩
  left_inv := by
    intro p
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change
        sourceFullFrameRealSplitMixedRowsInv
          (p.1.1, sourceFullFrameRealSplitMixedRows p.1) = p.1.2
      rw [sourceFullFrameRealSplitMixedRowsInv_eq_tailMixedRowsLinearEquiv_symm
        (p.1.1, sourceFullFrameRealSplitMixedRows p.1) p.property]
      rw [sourceFullFrameRealSplitMixedRows_eq_tailMixedRowsLinearEquiv p.1 p.property]
      exact
        (sourceRealFullFrameTailMixedRowsLinearEquiv d n ι p.1.1
          p.property).symm_apply_apply p.1.2
  right_inv := by
    intro p
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change
        sourceFullFrameRealSplitMixedRows
          (p.1.1, sourceFullFrameRealSplitMixedRowsInv p.1) = p.1.2
      rw [sourceFullFrameRealSplitMixedRows_eq_tailMixedRowsLinearEquiv
        (p.1.1, sourceFullFrameRealSplitMixedRowsInv p.1) p.property]
      rw [sourceFullFrameRealSplitMixedRowsInv_eq_tailMixedRowsLinearEquiv_symm
        p.1 p.property]
      exact
        (sourceRealFullFrameTailMixedRowsLinearEquiv d n ι p.1.1
          p.property).apply_symm_apply p.1.2
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact continuous_fst.comp continuous_subtype_val
    · unfold sourceFullFrameRealSplitMixedRows
      apply continuous_pi
      intro k
      apply continuous_pi
      intro a
      simp [MinkowskiSpace.minkowskiInner]
      fun_prop
  continuous_invFun := by
    have hInv :
        Continuous
          (fun p : sourceFullFrameRealSplitDetNonzero d n ι =>
            (p.1.1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)⁻¹) := by
      exact
        continuous_subtype_matrix_inv_of_det_ne_zero_real.comp
          (Continuous.subtype_mk
            (continuous_fst.comp continuous_subtype_val)
            (fun p => p.property))
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact continuous_fst.comp continuous_subtype_val
    · unfold sourceFullFrameRealSplitMixedRowsInv
      apply continuous_pi
      intro k
      apply continuous_pi
      intro a
      simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
      fun_prop

/-- The split-space form of the real kernel/mixed coordinate: apply the real
kernel coordinate to the selected-frame factor and compute mixed Gram rows
from the selected frame and complement rows. -/
def sourceFullFrameRealSplitKernelMixedCoord
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    (S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet)
    (p :
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
        (sourceComplementIndex ι → Fin (d + 1) → ℝ)) :
    (Fin S.realModelDim → ℝ) ×
      (sourceComplementIndex ι → Fin (d + 1) → ℝ) :=
  (S.realKernelCoord p.1, sourceFullFrameRealSplitMixedRows p)

/-- After the determinant-nonzero mixed-row homeomorphism, the split
kernel/mixed coordinate is just the product of the selected-frame kernel
coordinate with the identity on mixed rows. -/
def sourceFullFrameRealSplitProductKernelCoord
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    (S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet)
    (p :
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
        (sourceComplementIndex ι → Fin (d + 1) → ℝ)) :
    (Fin S.realModelDim → ℝ) ×
      (sourceComplementIndex ι → Fin (d + 1) → ℝ) :=
  (S.realKernelCoord p.1, p.2)

/-- If the selected-frame kernel coordinate is open, then its product with the
identity mixed-row coordinate is open.  The final producer uses this topology
fact on a shrunken local frame chart. -/
theorem isOpenMap_sourceFullFrameRealSplitProductKernelCoord_of_realKernelCoord
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    (S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet)
    (hS_open : IsOpenMap S.realKernelCoord) :
    IsOpenMap (sourceFullFrameRealSplitProductKernelCoord S) := by
  simpa [sourceFullFrameRealSplitProductKernelCoord, Prod.map_map] using
    hS_open.prodMap (IsOpenMap.id :
      IsOpenMap (id :
        (sourceComplementIndex ι → Fin (d + 1) → ℝ) →
          sourceComplementIndex ι → Fin (d + 1) → ℝ))

/-- The determinant-nonzero split-coordinate locus is open. -/
theorem isOpen_sourceFullFrameRealSplitDetNonzero
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n} :
    IsOpen
      {p :
        Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
          (sourceComplementIndex ι → Fin (d + 1) → ℝ) |
        p.1.det ≠ 0} := by
  exact
    isOpen_ne_fun
      ((continuous_fst :
        Continuous
          (fun p :
            Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
              (sourceComplementIndex ι → Fin (d + 1) → ℝ) => p.1)
        ).matrix_det)
      continuous_const

/-- Passing an ambient-open set through the determinant-nonzero mixed-row
homeomorphism and then forgetting the subtype gives an ambient-open set. -/
theorem isOpen_sourceFullFrameRealSplitMixedRowsHomeomorph_val_image
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {V : Set
      (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
        (sourceComplementIndex ι → Fin (d + 1) → ℝ))}
    (hV_open : IsOpen V) :
    IsOpen
      ((Subtype.val :
        sourceFullFrameRealSplitDetNonzero d n ι →
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
            (sourceComplementIndex ι → Fin (d + 1) → ℝ)) ''
        ((sourceFullFrameRealSplitMixedRowsHomeomorph d n ι) ''
          {p : sourceFullFrameRealSplitDetNonzero d n ι |
            p.1 ∈ V})) := by
  have hpre :
      IsOpen
        {p : sourceFullFrameRealSplitDetNonzero d n ι |
          p.1 ∈ V} := by
    exact hV_open.preimage continuous_subtype_val
  have hH :
      IsOpen
        ((sourceFullFrameRealSplitMixedRowsHomeomorph d n ι) ''
          {p : sourceFullFrameRealSplitDetNonzero d n ι |
            p.1 ∈ V}) := by
    exact (sourceFullFrameRealSplitMixedRowsHomeomorph d n ι).isOpenMap _ hpre
  exact
    (isOpen_sourceFullFrameRealSplitDetNonzero (d := d) (n := n) (ι := ι)
      ).isOpenMap_subtype_val _ hH

/-- If the selected-frame kernel coordinate is globally open, the transformed
product-coordinate image required by the local bridge is open.  The final
producer will replace the global hypothesis with the corresponding local
selected-frame product chart on the chosen `W`. -/
theorem sourceFullFrameRealSplitProductKernelCoord_open_after_homeomorph_on_W_of_realKernelCoord_openMap
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    (S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet)
    {W : Set
      (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
        (sourceComplementIndex ι → Fin (d + 1) → ℝ))}
    (hS_open : IsOpenMap S.realKernelCoord) :
    ∀ {V : Set
      (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
        (sourceComplementIndex ι → Fin (d + 1) → ℝ))},
      IsOpen V →
      V ⊆ W →
      IsOpen
        (sourceFullFrameRealSplitProductKernelCoord S ''
          ((Subtype.val :
            sourceFullFrameRealSplitDetNonzero d n ι →
              Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
                (sourceComplementIndex ι → Fin (d + 1) → ℝ)) ''
            ((sourceFullFrameRealSplitMixedRowsHomeomorph d n ι) ''
              {p : sourceFullFrameRealSplitDetNonzero d n ι |
                p.1 ∈ V}))) := by
  intro V hV_open _hV_sub
  exact
    (isOpenMap_sourceFullFrameRealSplitProductKernelCoord_of_realKernelCoord
      S hS_open)
      _
      (isOpen_sourceFullFrameRealSplitMixedRowsHomeomorph_val_image
        (d := d) (n := n) (ι := ι) hV_open)

/-- On determinant-nonzero selected frames, the split kernel/mixed coordinate
is the selected-frame kernel coordinate together with the checked rowwise
linear equivalence from complement rows to mixed rows. -/
theorem sourceFullFrameRealSplitKernelMixedCoord_eq_tailMixedRowsLinearEquiv
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    (S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet)
    (p :
      Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
        (sourceComplementIndex ι → Fin (d + 1) → ℝ))
    (hp : p.1.det ≠ 0) :
    sourceFullFrameRealSplitKernelMixedCoord S p =
      (S.realKernelCoord p.1,
        sourceRealFullFrameTailMixedRowsLinearEquiv d n ι p.1 hp p.2) := by
  rw [sourceFullFrameRealSplitKernelMixedCoord,
    sourceFullFrameRealSplitMixedRows_eq_tailMixedRowsLinearEquiv p hp]

/-- The split kernel/mixed coordinate factors through the checked
determinant-nonzero mixed-row homeomorphism and the product coordinate. -/
theorem sourceFullFrameRealSplitKernelMixedCoord_eq_productKernelCoord_homeomorph
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    (S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet)
    (p : sourceFullFrameRealSplitDetNonzero d n ι) :
    sourceFullFrameRealSplitKernelMixedCoord S (p : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
        (sourceComplementIndex ι → Fin (d + 1) → ℝ)) =
      sourceFullFrameRealSplitProductKernelCoord S
        ((sourceFullFrameRealSplitMixedRowsHomeomorph d n ι p) :
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
            (sourceComplementIndex ι → Fin (d + 1) → ℝ)) := by
  rfl

/-- The image of the split kernel/mixed coordinate over a determinant-nonzero
set is the image of the product coordinate after applying the checked
mixed-row homeomorphism on the determinant-nonzero subtype. -/
theorem sourceFullFrameRealSplitKernelMixedCoord_image_eq_product_homeomorph_image
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    (S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet)
    {V : Set
      (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
        (sourceComplementIndex ι → Fin (d + 1) → ℝ))}
    (hV_det : V ⊆ {p | p.1.det ≠ 0}) :
    sourceFullFrameRealSplitKernelMixedCoord S '' V =
      sourceFullFrameRealSplitProductKernelCoord S ''
        ((Subtype.val :
          sourceFullFrameRealSplitDetNonzero d n ι →
            Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
              (sourceComplementIndex ι → Fin (d + 1) → ℝ)) ''
          ((sourceFullFrameRealSplitMixedRowsHomeomorph d n ι) ''
            {p : sourceFullFrameRealSplitDetNonzero d n ι |
              p.1 ∈ V})) := by
  ext y
  constructor
  · rintro ⟨p, hpV, rfl⟩
    let q : sourceFullFrameRealSplitDetNonzero d n ι :=
      ⟨p, hV_det hpV⟩
    refine
      ⟨((sourceFullFrameRealSplitMixedRowsHomeomorph d n ι q) :
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
            (sourceComplementIndex ι → Fin (d + 1) → ℝ)), ?_, ?_⟩
    · exact
        ⟨sourceFullFrameRealSplitMixedRowsHomeomorph d n ι q,
          ⟨q, hpV, rfl⟩, rfl⟩
    · rw [← sourceFullFrameRealSplitKernelMixedCoord_eq_productKernelCoord_homeomorph
        S q]
  · rintro ⟨p, ⟨q, ⟨r, hrV, rfl⟩, rfl⟩, rfl⟩
    refine ⟨(r : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
      (sourceComplementIndex ι → Fin (d + 1) → ℝ)), hrV, ?_⟩
    rw [sourceFullFrameRealSplitKernelMixedCoord_eq_productKernelCoord_homeomorph
      S r]

/-- Once the selected-frame/product coordinate is known to have open images
after the checked mixed-row homeomorphism, the original split kernel/mixed
coordinate has the same open-image property. -/
theorem isOpen_sourceFullFrameRealSplitKernelMixedCoord_image_of_product_homeomorph_image_open
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    (S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet)
    {V : Set
      (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
        (sourceComplementIndex ι → Fin (d + 1) → ℝ))}
    (hV_det : V ⊆ {p | p.1.det ≠ 0})
    (hopen :
      IsOpen
        (sourceFullFrameRealSplitProductKernelCoord S ''
          ((Subtype.val :
            sourceFullFrameRealSplitDetNonzero d n ι →
              Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
                (sourceComplementIndex ι → Fin (d + 1) → ℝ)) ''
            ((sourceFullFrameRealSplitMixedRowsHomeomorph d n ι) ''
              {p : sourceFullFrameRealSplitDetNonzero d n ι |
                p.1 ∈ V})))) :
    IsOpen (sourceFullFrameRealSplitKernelMixedCoord S '' V) := by
  rwa [sourceFullFrameRealSplitKernelMixedCoord_image_eq_product_homeomorph_image
    S hV_det]

/-- Local-open form of the previous bridge on a chosen split neighborhood
`W`.  The remaining mathematical input is exactly the local openness of the
selected-frame/product coordinate after the checked mixed-row homeomorphism. -/
theorem sourceFullFrameRealSplitKernelMixedCoord_open_on_W_of_product_homeomorph_open
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    (S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet)
    {W : Set
      (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
        (sourceComplementIndex ι → Fin (d + 1) → ℝ))}
    (hW_det : W ⊆ {p | p.1.det ≠ 0})
    (hProduct_open :
      ∀ {V : Set
        (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
          (sourceComplementIndex ι → Fin (d + 1) → ℝ))},
        IsOpen V →
        V ⊆ W →
        IsOpen
          (sourceFullFrameRealSplitProductKernelCoord S ''
            ((Subtype.val :
              sourceFullFrameRealSplitDetNonzero d n ι →
                Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
                  (sourceComplementIndex ι → Fin (d + 1) → ℝ)) ''
              ((sourceFullFrameRealSplitMixedRowsHomeomorph d n ι) ''
                {p : sourceFullFrameRealSplitDetNonzero d n ι |
                  p.1 ∈ V})))) :
    ∀ {V : Set
      (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
        (sourceComplementIndex ι → Fin (d + 1) → ℝ))},
      IsOpen V →
      V ⊆ W →
      IsOpen (sourceFullFrameRealSplitKernelMixedCoord S '' V) := by
  intro V hV_open hV_sub
  apply
    isOpen_sourceFullFrameRealSplitKernelMixedCoord_image_of_product_homeomorph_image_open
      S
  · intro p hpV
    exact hW_det (hV_sub hpV)
  · exact hProduct_open hV_open hV_sub

/-- Selected-frame local product-open data on the split source coordinates.

The hard real full-frame producer must construct this packet from the real
IFT selected-frame chart.  Once it is available, the determinant-nonzero
mixed-row homeomorphism and source-split bridges below consume it
mechanically. -/
structure SourceFullFrameRealSelectedFrameProductOpenData
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    (S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet) where
  W :
    Set
      (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
        (sourceComplementIndex ι → Fin (d + 1) → ℝ))
  W_open : IsOpen W
  center_mem : sourceRealFullFrameSplitHomeomorph d n ι x0 ∈ W
  W_det : W ⊆ {p | p.1.det ≠ 0}
  frame_mem_domain : ∀ p ∈ W, p.1 ∈ S.frameDomain
  product_open_after_homeomorph :
    ∀ {V : Set
      (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
        (sourceComplementIndex ι → Fin (d + 1) → ℝ))},
      IsOpen V →
      V ⊆ W →
      IsOpen
        (sourceFullFrameRealSplitProductKernelCoord S ''
          ((Subtype.val :
            sourceFullFrameRealSplitDetNonzero d n ι →
              Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
                (sourceComplementIndex ι → Fin (d + 1) → ℝ)) ''
            ((sourceFullFrameRealSplitMixedRowsHomeomorph d n ι) ''
              {p : sourceFullFrameRealSplitDetNonzero d n ι |
                p.1 ∈ V})))

namespace SourceFullFrameRealSelectedFrameProductOpenData

/-- The selected-frame product-open packet immediately gives the split
kernel/mixed open-image theorem required by the source-coordinate bridge. -/
theorem split_kernel_mixed_open_on_W
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    {S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet}
    (D : SourceFullFrameRealSelectedFrameProductOpenData S) :
    ∀ {V : Set
      (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
        (sourceComplementIndex ι → Fin (d + 1) → ℝ))},
      IsOpen V →
      V ⊆ D.W →
      IsOpen (sourceFullFrameRealSplitKernelMixedCoord S '' V) :=
  sourceFullFrameRealSplitKernelMixedCoord_open_on_W_of_product_homeomorph_open
    S D.W_det D.product_open_after_homeomorph

/-- The inverse split source patch attached to selected-frame product-open data
is open. -/
theorem source_patch_open
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    {S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet}
    (D : SourceFullFrameRealSelectedFrameProductOpenData S) :
    IsOpen ((sourceRealFullFrameSplitHomeomorph d n ι).symm '' D.W) :=
  (sourceRealFullFrameSplitHomeomorph d n ι).symm.isOpenMap D.W D.W_open

/-- The inverse split source patch contains the base tuple. -/
theorem center_mem_source_patch
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    {S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet}
    (D : SourceFullFrameRealSelectedFrameProductOpenData S) :
    x0 ∈ (sourceRealFullFrameSplitHomeomorph d n ι).symm '' D.W := by
  refine ⟨sourceRealFullFrameSplitHomeomorph d n ι x0, D.center_mem, ?_⟩
  simp

/-- Source points in the inverse split patch have selected frames in the local
frame domain recorded by the real gauge-slice packet. -/
theorem source_patch_frame_mem_domain
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    {S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet}
    (D : SourceFullFrameRealSelectedFrameProductOpenData S)
    {x : Fin n → Fin (d + 1) → ℝ}
    (hx : x ∈ (sourceRealFullFrameSplitHomeomorph d n ι).symm '' D.W) :
    sourceRealFullFrameMatrix d n ι x ∈ S.frameDomain := by
  rcases hx with ⟨p, hpW, rfl⟩
  have hp_eq :
      sourceRealFullFrameSplitHomeomorph d n ι
          ((sourceRealFullFrameSplitHomeomorph d n ι).symm p) = p := by
    simp
  have hframe :
      sourceRealFullFrameMatrix d n ι
          ((sourceRealFullFrameSplitHomeomorph d n ι).symm p) = p.1 :=
    congrArg Prod.fst hp_eq
  simpa [hframe] using D.frame_mem_domain p hpW

end SourceFullFrameRealSelectedFrameProductOpenData

/-- A selected-frame local product chart whose first coordinate is the real
kernel coordinate.  Producing this structure from the real submersion theorem
is the remaining non-mechanical selected-frame step. -/
structure SourceFullFrameRealSelectedFrameProductChartData
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    (S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet)
    (O : Type*) [TopologicalSpace O] where
  frameChart :
    OpenPartialHomeomorph
      (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
      ((Fin S.realModelDim → ℝ) × O)
  center_mem_source :
    sourceRealFullFrameMatrix d n ι x0 ∈ frameChart.source
  source_det : frameChart.source ⊆ {M | M.det ≠ 0}
  source_frameDomain : frameChart.source ⊆ S.frameDomain
  first_eq_realKernelCoord :
    ∀ M ∈ frameChart.source, (frameChart M).1 = S.realKernelCoord M

namespace SourceFullFrameRealSelectedFrameProductChartData

/-- A selected-frame local product chart produces the product-open packet
consumed by the real full-frame implicit chart constructor. -/
noncomputable def toOpenData
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    {S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet}
    {O : Type*} [TopologicalSpace O]
    (D : SourceFullFrameRealSelectedFrameProductChartData S O) :
    SourceFullFrameRealSelectedFrameProductOpenData S where
  W := {p |
    p.1 ∈ D.frameChart.source}
  W_open := D.frameChart.open_source.preimage continuous_fst
  center_mem := by
    simpa [sourceRealFullFrameSplitHomeomorph_apply] using D.center_mem_source
  W_det := by
    intro p hp
    exact D.source_det hp
  frame_mem_domain := by
    intro p hp
    exact D.source_frameDomain hp
  product_open_after_homeomorph := by
    intro V hV_open hV_sub
    let Vh : Set
      (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
        (sourceComplementIndex ι → Fin (d + 1) → ℝ)) :=
      ((Subtype.val :
        sourceFullFrameRealSplitDetNonzero d n ι →
          Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
            (sourceComplementIndex ι → Fin (d + 1) → ℝ)) ''
        ((sourceFullFrameRealSplitMixedRowsHomeomorph d n ι) ''
          {p : sourceFullFrameRealSplitDetNonzero d n ι | p.1 ∈ V}))
    have hVh_open : IsOpen Vh := by
      exact isOpen_sourceFullFrameRealSplitMixedRowsHomeomorph_val_image
        (d := d) (n := n) (ι := ι) hV_open
    have hVh_sub : Vh ⊆ {p | p.1 ∈ D.frameChart.source} := by
      rintro p ⟨q, ⟨r, hrV, rfl⟩, rfl⟩
      have hrW : r.1 ∈ {p | p.1 ∈ D.frameChart.source} := hV_sub hrV
      simpa [sourceFullFrameRealSplitMixedRowsHomeomorph] using hrW
    have htop :=
      isOpen_product_first_id_image_of_openPartialHomeomorph
        D.frameChart hVh_open hVh_sub
    have hEq :
        sourceFullFrameRealSplitProductKernelCoord S '' Vh =
          (fun p :
            Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
              (sourceComplementIndex ι → Fin (d + 1) → ℝ) =>
            ((D.frameChart p.1).1, p.2)) '' Vh := by
      ext y
      constructor
      · rintro ⟨p, hp, rfl⟩
        refine ⟨p, hp, ?_⟩
        simp [sourceFullFrameRealSplitProductKernelCoord,
          D.first_eq_realKernelCoord p.1 (hVh_sub hp)]
      · rintro ⟨p, hp, rfl⟩
        refine ⟨p, hp, ?_⟩
        simp [sourceFullFrameRealSplitProductKernelCoord,
          D.first_eq_realKernelCoord p.1 (hVh_sub hp)]
    rwa [hEq]

end SourceFullFrameRealSelectedFrameProductChartData

/-- The source-space kernel/mixed coordinate factors through the checked
selected-frame/complement-row split homeomorphism. -/
theorem sourceFullFrameRealKernelMixedCoord_eq_split
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    (S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet)
    (x : Fin n → Fin (d + 1) → ℝ) :
    sourceFullFrameRealKernelMixedCoord S x =
      sourceFullFrameRealSplitKernelMixedCoord S
        (sourceRealFullFrameSplitHomeomorph d n ι x) := by
  apply Prod.ext
  · simp [sourceFullFrameRealKernelMixedCoord,
      sourceFullFrameRealSplitKernelMixedCoord,
      sourceRealFullFrameSplitHomeomorph_apply]
  · ext k a
    simp [sourceFullFrameRealKernelMixedCoord,
      sourceFullFrameRealSplitKernelMixedCoord,
      sourceFullFrameRealSplitMixedRows,
      sourceRealFullFrameSplitHomeomorph_apply,
      sourceRealSelectedMixedRows, sourceRealMinkowskiGram,
      sourceRealFullFrameMatrix, MinkowskiSpace.minkowskiInner]

/-- The source-coordinate image is exactly the split-coordinate image under the
selected-frame/complement-row split. -/
theorem sourceFullFrameRealKernelMixedCoord_image_eq_split
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    (S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet)
    (U : Set (Fin n → Fin (d + 1) → ℝ)) :
    sourceFullFrameRealKernelMixedCoord S '' U =
      sourceFullFrameRealSplitKernelMixedCoord S ''
        (sourceRealFullFrameSplitHomeomorph d n ι '' U) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact
      ⟨sourceRealFullFrameSplitHomeomorph d n ι x,
        ⟨x, hx, rfl⟩, by
          rw [← sourceFullFrameRealKernelMixedCoord_eq_split S x]⟩
  · rintro ⟨p, ⟨x, hx, rfl⟩, rfl⟩
    exact
      ⟨x, hx, by
        rw [sourceFullFrameRealKernelMixedCoord_eq_split S x]⟩

/-- It is enough to prove openness after passing to the checked
selected-frame/complement-row split. -/
theorem isOpen_sourceFullFrameRealKernelMixedCoord_image_of_split_image_open
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    (S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet)
    {U : Set (Fin n → Fin (d + 1) → ℝ)}
    (hU :
      IsOpen
        (sourceFullFrameRealSplitKernelMixedCoord S ''
          (sourceRealFullFrameSplitHomeomorph d n ι '' U))) :
    IsOpen (sourceFullFrameRealKernelMixedCoord S '' U) := by
  rwa [sourceFullFrameRealKernelMixedCoord_image_eq_split]

/-- For a source patch obtained as the inverse split image of a split
neighborhood `W`, the open-image problem reduces to local openness of the
split kernel/mixed coordinate on `W`. -/
theorem isOpen_sourceFullFrameRealKernelMixedCoord_image_of_split_local_open
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    (S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet)
    {W : Set
      (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
        (sourceComplementIndex ι → Fin (d + 1) → ℝ))}
    (hW_open_image :
      ∀ {V : Set
        (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
          (sourceComplementIndex ι → Fin (d + 1) → ℝ))},
        IsOpen V →
        V ⊆ W →
        IsOpen (sourceFullFrameRealSplitKernelMixedCoord S '' V))
    {U : Set (Fin n → Fin (d + 1) → ℝ)}
    (hU_open : IsOpen U)
    (hU_sub :
      U ⊆ (sourceRealFullFrameSplitHomeomorph d n ι).symm '' W) :
    IsOpen (sourceFullFrameRealKernelMixedCoord S '' U) := by
  apply isOpen_sourceFullFrameRealKernelMixedCoord_image_of_split_image_open S
  apply hW_open_image
  · exact (sourceRealFullFrameSplitHomeomorph d n ι).isOpenMap U hU_open
  · intro p hp
    rcases hp with ⟨x, hx, rfl⟩
    rcases hU_sub hx with ⟨p', hpW, hp'⟩
    have hp_eq : sourceRealFullFrameSplitHomeomorph d n ι x = p' := by
      rw [← hp']
      simp
    simpa [hp_eq] using hpW

/-- The kernel-plus-mixed real coordinate map is continuous on any real source
patch whose selected frame remains in the real gauge-slice frame domain. -/
theorem continuousOn_sourceFullFrameRealKernelMixedCoord
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    (S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet)
    {E0 : Set (Fin n → Fin (d + 1) → ℝ)}
    (hE0_frame :
      ∀ x ∈ E0, sourceRealFullFrameMatrix d n ι x ∈ S.frameDomain) :
    ContinuousOn (sourceFullFrameRealKernelMixedCoord S) E0 := by
  exact
    (S.realKernelCoord_continuousOn.comp
      (continuous_sourceRealFullFrameMatrix d n ι).continuousOn
      hE0_frame).prodMk
      (continuous_sourceRealSelectedMixedRows d n ι).continuousOn

/-- Composing the raw kernel/mixed coordinate map with a finite real coordinate
equivalence gives a continuous real coordinate map on the chosen source
patch. -/
theorem continuousOn_sourceFullFrameRealCoord_of_kernelMixedCoord
    {d n m : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    (S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet)
    (coordEquivR :
      (Fin m → ℝ) ≃ₗ[ℝ]
        ((Fin S.realModelDim → ℝ) ×
          (sourceComplementIndex ι → Fin (d + 1) → ℝ)))
    {E0 : Set (Fin n → Fin (d + 1) → ℝ)}
    (hE0_frame :
      ∀ x ∈ E0, sourceRealFullFrameMatrix d n ι x ∈ S.frameDomain) :
    ContinuousOn
      (fun x : Fin n → Fin (d + 1) → ℝ =>
        coordEquivR.symm (sourceFullFrameRealKernelMixedCoord S x)) E0 := by
  exact
    (LinearMap.continuous_of_finiteDimensional
      coordEquivR.symm.toLinearMap).comp_continuousOn
      (continuousOn_sourceFullFrameRealKernelMixedCoord S hE0_frame)

/-- If the raw kernel/mixed coordinate image is open, then applying the inverse
finite real coordinate equivalence preserves openness. -/
theorem isOpen_sourceFullFrameRealCoord_image_of_kernelMixedCoord_image_open
    {d n m : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    (S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet)
    (coordEquivR :
      (Fin m → ℝ) ≃ₗ[ℝ]
        ((Fin S.realModelDim → ℝ) ×
          (sourceComplementIndex ι → Fin (d + 1) → ℝ)))
    {U : Set (Fin n → Fin (d + 1) → ℝ)}
    (hU :
      IsOpen (sourceFullFrameRealKernelMixedCoord S '' U)) :
    IsOpen
      ((fun x : Fin n → Fin (d + 1) → ℝ =>
        coordEquivR.symm (sourceFullFrameRealKernelMixedCoord S x)) '' U) := by
  rw [← Set.image_image]
  exact coordEquivR.symm.toContinuousLinearEquiv.toHomeomorph.isOpenMap
    (sourceFullFrameRealKernelMixedCoord S '' U) hU

/-- If the split kernel/mixed coordinate is locally open on the chosen split
neighborhood, then the finite real coordinate map has open image on the
corresponding inverse split source patch. -/
theorem isOpen_sourceFullFrameRealCoord_image_of_split_local_open
    {d n m : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    (S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet)
    (coordEquivR :
      (Fin m → ℝ) ≃ₗ[ℝ]
        ((Fin S.realModelDim → ℝ) ×
          (sourceComplementIndex ι → Fin (d + 1) → ℝ)))
    {W : Set
      (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
        (sourceComplementIndex ι → Fin (d + 1) → ℝ))}
    (hW_open_image :
      ∀ {V : Set
        (Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ ×
          (sourceComplementIndex ι → Fin (d + 1) → ℝ))},
        IsOpen V →
        V ⊆ W →
        IsOpen (sourceFullFrameRealSplitKernelMixedCoord S '' V))
    {U : Set (Fin n → Fin (d + 1) → ℝ)}
    (hU_open : IsOpen U)
    (hU_sub :
      U ⊆ (sourceRealFullFrameSplitHomeomorph d n ι).symm '' W) :
    IsOpen
      ((fun x : Fin n → Fin (d + 1) → ℝ =>
        coordEquivR.symm (sourceFullFrameRealKernelMixedCoord S x)) '' U) :=
  isOpen_sourceFullFrameRealCoord_image_of_kernelMixedCoord_image_open
    S coordEquivR
    (isOpen_sourceFullFrameRealKernelMixedCoord_image_of_split_local_open
      S hW_open_image hU_open hU_sub)

namespace SourceFullFrameRealSelectedFrameProductOpenData

/-- The selected-frame product-open packet gives the final finite real
coordinate open-image theorem on any source patch inside its inverse split
patch. -/
theorem realCoord_image_open_on_source_subset
    {d n m : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    {S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet}
    (D : SourceFullFrameRealSelectedFrameProductOpenData S)
    (coordEquivR :
      (Fin m → ℝ) ≃ₗ[ℝ]
        ((Fin S.realModelDim → ℝ) ×
          (sourceComplementIndex ι → Fin (d + 1) → ℝ)))
    {U : Set (Fin n → Fin (d + 1) → ℝ)}
    (hU_open : IsOpen U)
    (hU_sub :
      U ⊆ (sourceRealFullFrameSplitHomeomorph d n ι).symm '' D.W) :
    IsOpen
      ((fun x : Fin n → Fin (d + 1) → ℝ =>
        coordEquivR.symm (sourceFullFrameRealKernelMixedCoord S x)) '' U) :=
  isOpen_sourceFullFrameRealCoord_image_of_split_local_open
    S coordEquivR D.split_kernel_mixed_open_on_W hU_open hU_sub

/-- On the inverse split source patch, the canonical finite real coordinate
obtained from the kernel/mixed coordinate is continuous. -/
theorem realCoord_continuousOn_source_patch
    {d n m : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    {S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet}
    (D : SourceFullFrameRealSelectedFrameProductOpenData S)
    (coordEquivR :
      (Fin m → ℝ) ≃ₗ[ℝ]
        ((Fin S.realModelDim → ℝ) ×
          (sourceComplementIndex ι → Fin (d + 1) → ℝ))) :
    ContinuousOn
      (fun x : Fin n → Fin (d + 1) → ℝ =>
        coordEquivR.symm (sourceFullFrameRealKernelMixedCoord S x))
      ((sourceRealFullFrameSplitHomeomorph d n ι).symm '' D.W) :=
  continuousOn_sourceFullFrameRealCoord_of_kernelMixedCoord
    S coordEquivR (fun _x hx => D.source_patch_frame_mem_domain hx)

/-- The canonical finite real coordinate recovers the kernel/mixed coordinate
after applying the coordinate equivalence. -/
theorem realCoord_eq_kernel_mixed_on_source_patch
    {d n m : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    {S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet}
    (D : SourceFullFrameRealSelectedFrameProductOpenData S)
    (coordEquivR :
      (Fin m → ℝ) ≃ₗ[ℝ]
        ((Fin S.realModelDim → ℝ) ×
          (sourceComplementIndex ι → Fin (d + 1) → ℝ)))
    (x : Fin n → Fin (d + 1) → ℝ)
    (_hx : x ∈ (sourceRealFullFrameSplitHomeomorph d n ι).symm '' D.W) :
    coordEquivR
        (coordEquivR.symm (sourceFullFrameRealKernelMixedCoord S x)) =
      (S.realKernelCoord (sourceRealFullFrameMatrix d n ι x),
        sourceRealSelectedMixedRows d n ι x) := by
  simp [sourceFullFrameRealKernelMixedCoord]

/-- The canonical finite real coordinate has open image on the whole inverse
split source patch attached to the packet. -/
theorem realCoord_image_open_source_patch
    {d n m : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    {S :
      SourceFullFrameRealGaugeSliceData d
        (sourceRealFullFrameMatrix d n ι x0) hdet}
    (D : SourceFullFrameRealSelectedFrameProductOpenData S)
    (coordEquivR :
      (Fin m → ℝ) ≃ₗ[ℝ]
        ((Fin S.realModelDim → ℝ) ×
          (sourceComplementIndex ι → Fin (d + 1) → ℝ))) :
    IsOpen
      ((fun x : Fin n → Fin (d + 1) → ℝ =>
        coordEquivR.symm (sourceFullFrameRealKernelMixedCoord S x)) ''
          ((sourceRealFullFrameSplitHomeomorph d n ι).symm '' D.W)) :=
  D.realCoord_image_open_on_source_subset coordEquivR D.source_patch_open
    (fun _x hx => hx)

end SourceFullFrameRealSelectedFrameProductOpenData

/-- Full-frame real/complex chart data before it is collapsed to the generic
`SourceOrientedLocalRealChartData` interface. -/
structure SourceFullFrameRealCompatibleImplicitChartData
    (d n : ℕ)
    (ι : Fin (d + 1) ↪ Fin n)
    (x0 : Fin n → Fin (d + 1) → ℝ)
    (hdet : sourceRealFullFrameDet d n ι x0 ≠ 0) where
  slice :
    SourceFullFrameRealGaugeSliceData d
      (sourceRealFullFrameMatrix d n ι x0) hdet
  m : ℕ
  C :
    SourceOrientedMaxRankChartData d n
      (M := Fin m → ℂ)
      (sourceRealOrientedMinkowskiInvariant d n x0)
  coordEquivR :
    (Fin m → ℝ) ≃ₗ[ℝ]
      ((Fin slice.realModelDim → ℝ) ×
        (sourceComplementIndex ι → Fin (d + 1) → ℝ))
  coordEquivC :
    (Fin m → ℂ) ≃ₗ[ℂ]
      ((Fin slice.realModelDim → ℂ) ×
        (sourceComplementIndex ι → Fin (d + 1) → ℂ))
  coordEquiv_realToComplex :
    ∀ u : Fin m → ℝ,
      coordEquivC (SCV.realToComplex u) =
        (SCV.realToComplex (coordEquivR u).1,
          fun k a => ((coordEquivR u).2 k a : ℂ))
  E0 : Set (Fin n → Fin (d + 1) → ℝ)
  E0_open : IsOpen E0
  center_mem : x0 ∈ E0
  invariant_mem_chart :
    ∀ x ∈ E0, sourceRealOrientedMinkowskiInvariant d n x ∈ C.Ω
  frame_mem_domain :
    ∀ x ∈ E0,
      sourceRealFullFrameMatrix d n ι x ∈ slice.frameDomain
  realCoord : (Fin n → Fin (d + 1) → ℝ) → Fin m → ℝ
  realCoord_eq_kernel_mixed :
    ∀ x ∈ E0,
      coordEquivR (realCoord x) =
        (slice.realKernelCoord (sourceRealFullFrameMatrix d n ι x),
          sourceRealSelectedMixedRows d n ι x)
  chart_eq_kernel_mixed :
    ∀ x ∈ E0,
      coordEquivC (C.chart (sourceRealOrientedMinkowskiInvariant d n x)) =
        (slice.realModelToComplexSlice.symm
          (slice.complexKernelCoord
            ((sourceRealFullFrameMatrix d n ι x).map Complex.ofReal)),
          sourceSelectedMixedRows d n ι
            (sourceRealOrientedMinkowskiInvariant d n x))
  realCoord_continuousOn : ContinuousOn realCoord E0
  realCoord_image_open :
    ∀ {S : Set (Fin n → Fin (d + 1) → ℝ)},
      IsOpen S → S ⊆ E0 → IsOpen (realCoord '' S)

namespace SourceFullFrameRealCompatibleImplicitChartData

/-- The kernel/mixed real-compatibility equations imply the generic
`chart_real_eq` field required by the totally-real identity consumer. -/
theorem chart_real_eq
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    (R : SourceFullFrameRealCompatibleImplicitChartData d n ι x0 hdet)
    (x : Fin n → Fin (d + 1) → ℝ)
    (hx : x ∈ R.E0) :
    R.C.chart (sourceRealOrientedMinkowskiInvariant d n x) =
      SCV.realToComplex (R.realCoord x) := by
  apply R.coordEquivC.injective
  rw [R.chart_eq_kernel_mixed x hx, R.coordEquiv_realToComplex]
  rw [R.realCoord_eq_kernel_mixed x hx]
  apply Prod.ext
  · rw [R.slice.complexKernelCoord_real_eq]
    simp
  · exact sourceSelectedMixedRows_sourceRealOrientedMinkowskiInvariant d n ι x

/-- Collapse real-compatible full-frame chart data to the generic local real
chart data used by the oriented uniqueness theorem. -/
noncomputable def to_localRealChartData
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    (R : SourceFullFrameRealCompatibleImplicitChartData d n ι x0 hdet) :
    SourceOrientedLocalRealChartData d n x0 where
  m := R.m
  C := R.C
  E0 := R.E0
  E0_open := R.E0_open
  center_mem := R.center_mem
  invariant_mem_chart := R.invariant_mem_chart
  realCoord := R.realCoord
  realCoord_continuousOn := R.realCoord_continuousOn
  realCoord_image_open := R.realCoord_image_open
  chart_real_eq := R.chart_real_eq

end SourceFullFrameRealCompatibleImplicitChartData

/-- Once the hard real-compatible implicit chart data is available, the
pointwise full-frame local real chart theorem is immediate. -/
theorem sourceOrientedLocalRealChartData_of_fullFrameRealCompatibleImplicitChartData
    {d n : ℕ}
    {ι : Fin (d + 1) ↪ Fin n}
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {hdet : sourceRealFullFrameDet d n ι x0 ≠ 0}
    (R :
      Nonempty
        (SourceFullFrameRealCompatibleImplicitChartData d n ι x0 hdet)) :
    Nonempty (SourceOrientedLocalRealChartData d n x0) := by
  rcases R with ⟨R⟩
  exact ⟨R.to_localRealChartData⟩

/-- Pointwise producer for the remaining hard real-compatible full-frame chart
theorem. -/
def SourceFullFrameRealCompatibleImplicitChartProducer
    (d n : ℕ) : Prop :=
  ∀ (ι : Fin (d + 1) ↪ Fin n)
    {x0 : Fin n → Fin (d + 1) → ℝ},
    (hdet : sourceRealFullFrameDet d n ι x0 ≠ 0) →
      Nonempty (SourceFullFrameRealCompatibleImplicitChartData d n ι x0 hdet)

/-- A pointwise real-compatible full-frame chart producer supplies the public
local real chart theorem on every determinant-nonzero sheet. -/
theorem sourceOrientedLocalRealChartData_of_fullFrameDet_ne_zero_of_realCompatibleImplicitChartProducer
    {d n : ℕ}
    (P : SourceFullFrameRealCompatibleImplicitChartProducer d n)
    (ι : Fin (d + 1) ↪ Fin n)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    (hdet : sourceRealFullFrameDet d n ι x0 ≠ 0) :
    Nonempty (SourceOrientedLocalRealChartData d n x0) :=
  sourceOrientedLocalRealChartData_of_fullFrameRealCompatibleImplicitChartData
    (P ι hdet)

/-- A source-open determinant-nonzero Jost patch is an oriented real
environment once the pointwise real-compatible full-frame chart producer is
available. -/
theorem sourceOrientedRealEnvironment_of_realCompatibleImplicitChartProducer
    {d n : ℕ}
    (P : SourceFullFrameRealCompatibleImplicitChartProducer d n)
    (ι : Fin (d + 1) ↪ Fin n)
    {E : Set (Fin n → Fin (d + 1) → ℝ)}
    (hE_open : IsOpen E)
    (hE_nonempty : E.Nonempty)
    (hE_jost : E ⊆ JostSet d n)
    (hdet :
      ∀ x ∈ E, sourceRealFullFrameDet d n ι x ≠ 0) :
    IsHWOrientedRealEnvironment d n E :=
  sourceOrientedRealEnvironment_of_fullFrameDetNonzero_localCharts
    d n ι hE_open hE_nonempty hE_jost hdet
    (fun {_x} hx =>
      sourceOrientedLocalRealChartData_of_fullFrameRealCompatibleImplicitChartData
        (P ι hx))

/-- The checked OS45 determinant-regular subpatch becomes an oriented real
environment from the pointwise real-compatible full-frame chart producer. -/
theorem os45Figure24_checkedRealPatch_fullFrameOrientedEnvironmentSubpatch_of_realCompatibleImplicitChartProducer
    {d : ℕ} [NeZero d]
    (hd : 2 ≤ d)
    (n : ℕ)
    (hn : d + 1 ≤ n)
    (π : Equiv.Perm (Fin n))
    (i : Fin n) (hi : i.val + 1 < n)
    (E0 : Set (Fin n → Fin (d + 1) → ℝ))
    (hE0 : IsOS45Figure24CheckedRealPatch (d := d) n π i hi E0)
    (P : SourceFullFrameRealCompatibleImplicitChartProducer d n) :
    ∃ E : Set (Fin n → Fin (d + 1) → ℝ),
      E ⊆ E0 ∧
      IsOpen E ∧
      E.Nonempty ∧
      IsHWOrientedRealEnvironment d n
        {y | ∃ x ∈ E, y = fun k => x (π k)} :=
  os45Figure24_checkedRealPatch_fullFrameOrientedEnvironmentSubpatch_of_localCharts
    hd n hn π i hi E0 hE0
    (fun ι {_y} hy =>
      sourceOrientedLocalRealChartData_of_fullFrameRealCompatibleImplicitChartData
        (P ι hy))

/-- From the real-compatible full-frame chart producer, a checked OS45 real
patch contains a source-oriented distributional uniqueness subpatch. -/
theorem os45Figure24_checkedRealPatch_sourceOrientedDistributionalUniquenessSubpatch_of_realCompatibleImplicitChartProducer
    {d : ℕ} [NeZero d]
    (hd : 2 ≤ d)
    (n : ℕ)
    (hn : d + 1 ≤ n)
    (π : Equiv.Perm (Fin n))
    (i : Fin n) (hi : i.val + 1 < n)
    (E0 : Set (Fin n → Fin (d + 1) → ℝ))
    (hE0 : IsOS45Figure24CheckedRealPatch (d := d) n π i hi E0)
    (P : SourceFullFrameRealCompatibleImplicitChartProducer d n) :
    ∃ E : Set (Fin n → Fin (d + 1) → ℝ),
      E ⊆ E0 ∧
      IsOpen E ∧
      E.Nonempty ∧
      sourceOrientedDistributionalUniquenessPatch d n
        {y | ∃ x ∈ E, y = fun k => x (π k)} := by
  rcases
      os45Figure24_checkedRealPatch_fullFrameOrientedEnvironmentSubpatch_of_realCompatibleImplicitChartProducer
        hd n hn π i hi E0 hE0 P with
    ⟨E, hE_sub, hE_open, hE_ne, hEnv⟩
  exact
    ⟨E, hE_sub, hE_open, hE_ne,
      sourceOrientedDistributionalUniquenessPatch_of_HWRealEnvironment
        hd hn hEnv⟩

end BHW
