import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexZeroSection

/-!
# Complex-base selected source Gram zero-section support

This companion file duplicates the checked selected zero-section construction
at an arbitrary complex regular base point `z0`.  The older
`SourceComplexZeroSection` file is based at `realEmbed x0`; theorem 2's
small-arity holomorphic section needs the same chart at an actual
extended-tube point.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial
open scoped Matrix.Norms.Operator

namespace BHW

/-- Projection onto the kernel of the selected complex Gram differential at an
arbitrary complex base point. -/
noncomputable def sourceSelectedComplexGramKernelProjectionAt
    (d n : ℕ)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (I : Fin (min n (d + 1)) → Fin n) :
    (Fin n → Fin (d + 1) → ℂ) →L[ℂ]
      LinearMap.ker
        (sourceSelectedComplexGramDifferentialToSym d n
          (min n (d + 1)) z0 I) := by
  let m := min n (d + 1)
  let L : (Fin n → Fin (d + 1) → ℂ) →L[ℂ]
      sourceSelectedComplexSymCoordSubspace n m I :=
    LinearMap.toContinuousLinearMap
      (sourceSelectedComplexGramDifferentialToSym d n m z0 I)
  exact Classical.choose L.ker_closedComplemented_of_finiteDimensional_range

/-- The complex-base kernel projection is the identity on the selected kernel. -/
theorem sourceSelectedComplexGramKernelProjectionAt_apply_ker
    (d n : ℕ)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (I : Fin (min n (d + 1)) → Fin n)
    (v :
      LinearMap.ker
        (sourceSelectedComplexGramDifferentialToSym d n
          (min n (d + 1)) z0 I)) :
    sourceSelectedComplexGramKernelProjectionAt d n (z0 := z0) I v = v := by
  let m := min n (d + 1)
  let L : (Fin n → Fin (d + 1) → ℂ) →L[ℂ]
      sourceSelectedComplexSymCoordSubspace n m I :=
    LinearMap.toContinuousLinearMap
      (sourceSelectedComplexGramDifferentialToSym d n m z0 I)
  exact Classical.choose_spec
    L.ker_closedComplemented_of_finiteDimensional_range v

/-- Product chart map for the selected complex Gram map at a complex base
point, using the fixed projection to the base kernel as transverse
coordinate. -/
noncomputable def sourceSelectedComplexGramProdMapAt
    (d n : ℕ)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (I : Fin (min n (d + 1)) → Fin n) :
    (Fin n → Fin (d + 1) → ℂ) →
      sourceSelectedComplexSymCoordSubspace n (min n (d + 1)) I ×
        LinearMap.ker
          (sourceSelectedComplexGramDifferentialToSym d n
            (min n (d + 1)) z0 I) :=
  fun z =>
    (sourceSelectedComplexGramMap d n (min n (d + 1)) I z,
      sourceSelectedComplexGramKernelProjectionAt d n (z0 := z0) I (z - z0))

/-- The complex-base selected product chart map is smooth. -/
theorem contDiff_sourceSelectedComplexGramProdMapAt
    (d n : ℕ)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    {I : Fin (min n (d + 1)) → Fin n}
    (hI : Function.Injective I) :
    ContDiff ℂ ⊤ (sourceSelectedComplexGramProdMapAt d n (z0 := z0) I) := by
  unfold sourceSelectedComplexGramProdMapAt
  refine (contDiff_sourceSelectedComplexGramMap_of_injective d n
    (min n (d + 1)) hI).prodMk ?_
  fun_prop

/-- Frechet derivative of the complex-base selected product chart map. -/
theorem sourceSelectedComplexGramProdMapAt_hasFDerivAt
    (d n : ℕ)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (I : Fin (min n (d + 1)) → Fin n)
    (z : Fin n → Fin (d + 1) → ℂ) :
    HasFDerivAt (sourceSelectedComplexGramProdMapAt d n (z0 := z0) I)
      ((LinearMap.toContinuousLinearMap
          (sourceSelectedComplexGramDifferentialToSym d n
            (min n (d + 1)) z I)).prod
        (sourceSelectedComplexGramKernelProjectionAt d n (z0 := z0) I)) z := by
  unfold sourceSelectedComplexGramProdMapAt
  refine
    (sourceSelectedComplexGramMap_hasStrictFDerivAt d n
      (min n (d + 1)) I z).hasFDerivAt.prodMk ?_
  exact (sourceSelectedComplexGramKernelProjectionAt d n (z0 := z0) I).hasFDerivAt.comp z
    ((hasFDerivAt_id z).sub_const z0)

/-- Formula for the Frechet derivative of the complex-base selected product
chart map. -/
theorem sourceSelectedComplexGramProdMapAt_fderiv
    (d n : ℕ)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    (I : Fin (min n (d + 1)) → Fin n)
    (z : Fin n → Fin (d + 1) → ℂ) :
    fderiv ℂ (sourceSelectedComplexGramProdMapAt d n (z0 := z0) I) z =
      (LinearMap.toContinuousLinearMap
          (sourceSelectedComplexGramDifferentialToSym d n
            (min n (d + 1)) z I)).prod
        (sourceSelectedComplexGramKernelProjectionAt d n (z0 := z0) I) :=
  (sourceSelectedComplexGramProdMapAt_hasFDerivAt d n I z).fderiv

/-- At the complex base point, the selected product chart derivative is
invertible. -/
theorem sourceSelectedComplexGramProdMapAt_base_fderiv_isInvertible
    (d n : ℕ)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceComplexRegularMinor d n I J z0 ≠ 0) :
    (fderiv ℂ (sourceSelectedComplexGramProdMapAt d n (z0 := z0) I)
      z0).IsInvertible := by
  let m := min n (d + 1)
  let L : (Fin n → Fin (d + 1) → ℂ) →L[ℂ]
      sourceSelectedComplexSymCoordSubspace n m I :=
    LinearMap.toContinuousLinearMap
      (sourceSelectedComplexGramDifferentialToSym d n m z0 I)
  let P :
      (Fin n → Fin (d + 1) → ℂ) →L[ℂ]
        LinearMap.ker
          (sourceSelectedComplexGramDifferentialToSym d n m z0 I) :=
    sourceSelectedComplexGramKernelProjectionAt d n (z0 := z0) I
  have hsurj : L.range = ⊤ := by
    exact LinearMap.range_eq_top.mpr
      (sourceSelectedComplexGramDifferentialToSym_surjective_of_sourceComplexRegularMinor_ne_zero
        d n hI hJ hminor)
  have hproj :
      ∀ v : L.ker, P v = v := by
    intro v
    exact sourceSelectedComplexGramKernelProjectionAt_apply_ker d n (z0 := z0) I v
  have hPrange : P.range = ⊤ := LinearMap.range_eq_of_proj hproj
  have hcompl : IsCompl L.ker P.ker := LinearMap.isCompl_of_proj hproj
  rw [sourceSelectedComplexGramProdMapAt_fderiv]
  let eLin :=
    LinearMap.equivProdOfSurjectiveOfIsCompl
      (L : (Fin n → Fin (d + 1) → ℂ) →ₗ[ℂ]
        sourceSelectedComplexSymCoordSubspace n m I)
      (P : (Fin n → Fin (d + 1) → ℂ) →ₗ[ℂ]
        LinearMap.ker
          (sourceSelectedComplexGramDifferentialToSym d n m z0 I))
      hsurj hPrange hcompl
  refine ⟨eLin.toContinuousLinearEquiv, ?_⟩
  ext v <;> rfl

/-- After shrinking the source neighborhood of the complex base point, the
selected product chart derivative remains invertible. -/
theorem sourceSelectedComplexGramProdMapAt_local_invertible_nhds
    (d n : ℕ)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceComplexRegularMinor d n I J z0 ≠ 0)
    {V : Set (Fin n → Fin (d + 1) → ℂ)}
    (hV_open : IsOpen V)
    (hz0V : z0 ∈ V) :
    ∃ W : Set (Fin n → Fin (d + 1) → ℂ),
      IsOpen W ∧ z0 ∈ W ∧ W ⊆ V ∧
      ∀ z ∈ W,
        (fderiv ℂ (sourceSelectedComplexGramProdMapAt d n (z0 := z0) I) z).IsInvertible := by
  let Espace := Fin n → Fin (d + 1) → ℂ
  let ProdTarget :=
    sourceSelectedComplexSymCoordSubspace n (min n (d + 1)) I ×
      LinearMap.ker
        (sourceSelectedComplexGramDifferentialToSym d n
          (min n (d + 1)) z0 I)
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
          fderiv ℂ (sourceSelectedComplexGramProdMapAt d n (z0 := z0) I) z) := by
    exact (contDiff_sourceSelectedComplexGramProdMapAt d n hI
      (z0 := z0)).continuous_fderiv (by simp)
  let W : Set (Fin n → Fin (d + 1) → ℂ) :=
    V ∩ {z |
      fderiv ℂ (sourceSelectedComplexGramProdMapAt d n (z0 := z0) I) z ∈ InvSet}
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · exact hV_open.inter (hInvOpen.preimage hderivCont)
  · refine ⟨hz0V, ?_⟩
    exact sourceSelectedComplexGramProdMapAt_base_fderiv_isInvertible
      d n hI hJ hminor
  · intro z hz
    exact hz.1
  · intro z hz
    exact hz.2

/-- The canonical selected complex implicit chart at a complex nonzero-minor
source point. -/
noncomputable def sourceSelectedComplexGramImplicitChartAt
    (d n : ℕ)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceComplexRegularMinor d n I J z0 ≠ 0) :
    OpenPartialHomeomorph
      (Fin n → Fin (d + 1) → ℂ)
      (sourceSelectedComplexSymCoordSubspace n (min n (d + 1)) I ×
        LinearMap.ker
          (sourceSelectedComplexGramDifferentialToSym d n
            (min n (d + 1)) z0 I)) := by
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
  exact hstrict.implicitToOpenPartialHomeomorph f f' hsurj

/-- The complex-base implicit chart is the selected Gram/product map. -/
theorem sourceSelectedComplexGramImplicitChartAt_apply
    (d n : ℕ)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceComplexRegularMinor d n I J z0 ≠ 0)
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceSelectedComplexGramImplicitChartAt d n hI hJ hminor z =
      sourceSelectedComplexGramProdMapAt d n (z0 := z0) I z := by
  unfold sourceSelectedComplexGramImplicitChartAt sourceSelectedComplexGramProdMapAt
  dsimp only
  rfl

/-- The complex base point lies in the source of the canonical selected
complex implicit chart. -/
theorem sourceSelectedComplexGramImplicitChartAt_mem_source
    (d n : ℕ)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceComplexRegularMinor d n I J z0 ≠ 0) :
    z0 ∈
      (sourceSelectedComplexGramImplicitChartAt d n hI hJ hminor).source := by
  unfold sourceSelectedComplexGramImplicitChartAt
  dsimp only
  exact HasStrictFDerivAt.mem_implicitToOpenPartialHomeomorph_source _ _

/-- The canonical selected complex implicit chart sends the complex base point
to the base selected Gram coordinate and zero vertical coordinate. -/
theorem sourceSelectedComplexGramImplicitChartAt_self
    (d n : ℕ)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceComplexRegularMinor d n I J z0 ≠ 0) :
    sourceSelectedComplexGramImplicitChartAt d n hI hJ hminor z0 =
      (sourceSelectedComplexGramMap d n (min n (d + 1)) I z0, 0) := by
  rw [sourceSelectedComplexGramImplicitChartAt_apply]
  simp [sourceSelectedComplexGramProdMapAt]

/-- The flat selected-coordinate zero-kernel target map for the complex-base
implicit chart. -/
noncomputable def sourceSelectedComplexZeroKernelTargetCLMAt
    (d n : ℕ)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    {I : Fin (min n (d + 1)) → Fin n}
    (hI : Function.Injective I) :
    (Fin (Fintype.card
        (sourceSelectedSymCoordKey n (min n (d + 1)) I)) → ℂ) →L[ℂ]
      sourceSelectedComplexSymCoordSubspace n (min n (d + 1)) I ×
        LinearMap.ker
          (sourceSelectedComplexGramDifferentialToSym d n
            (min n (d + 1)) z0 I) :=
  ((sourceSelectedComplexSymCoordFinEquiv n (min n (d + 1)) hI).symm :
      (Fin (Fintype.card
        (sourceSelectedSymCoordKey n (min n (d + 1)) I)) → ℂ) →L[ℂ]
        sourceSelectedComplexSymCoordSubspace n (min n (d + 1)) I).prod 0

@[simp]
theorem sourceSelectedComplexZeroKernelTargetCLMAt_apply
    (d n : ℕ)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    {I : Fin (min n (d + 1)) → Fin n}
    (hI : Function.Injective I)
    (q : Fin (Fintype.card
        (sourceSelectedSymCoordKey n (min n (d + 1)) I)) → ℂ) :
    sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q =
      ((sourceSelectedComplexSymCoordFinEquiv n (min n (d + 1)) hI).symm q,
        0) :=
  rfl

/-- The zero-kernel section of the complex-base selected implicit chart is
complex differentiable on every coordinate set whose points remain in the
chart target and whose inverse source points lie in the local derivative
invertibility region. -/
theorem sourceSelectedComplexGramZeroSectionAt_differentiableOn
    (d n : ℕ)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceComplexRegularMinor d n I J z0 ≠ 0)
    {D : Set
      (Fin (Fintype.card
        (sourceSelectedSymCoordKey n (min n (d + 1)) I)) → ℂ)}
    (hD_target :
      ∀ q ∈ D,
        sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q ∈
          (sourceSelectedComplexGramImplicitChartAt d n hI hJ hminor).target)
    (hD_invertible :
      ∀ q ∈ D,
        (fderiv ℂ (sourceSelectedComplexGramProdMapAt d n (z0 := z0) I)
          ((sourceSelectedComplexGramImplicitChartAt d n hI hJ hminor).symm
            (sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q))).IsInvertible) :
    DifferentiableOn ℂ
      (fun q =>
        (sourceSelectedComplexGramImplicitChartAt d n hI hJ hminor).symm
          (sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q))
      D := by
  intro q hq
  let e := sourceSelectedComplexGramImplicitChartAt d n hI hJ hminor
  let y := sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q
  have hy : y ∈ e.target := hD_target q hq
  rcases hD_invertible q hq with ⟨A, hA⟩
  have hprod_has :
      HasFDerivAt (sourceSelectedComplexGramProdMapAt d n (z0 := z0) I)
        (A : (Fin n → Fin (d + 1) → ℂ) →L[ℂ]
          (sourceSelectedComplexSymCoordSubspace n (min n (d + 1)) I ×
            LinearMap.ker
              (sourceSelectedComplexGramDifferentialToSym d n
                (min n (d + 1)) z0 I)))
        (e.symm y) := by
    rw [hA, sourceSelectedComplexGramProdMapAt_fderiv]
    exact sourceSelectedComplexGramProdMapAt_hasFDerivAt d n I (e.symm y)
  have he_has :
      HasFDerivAt e
        (A : (Fin n → Fin (d + 1) → ℂ) →L[ℂ]
          (sourceSelectedComplexSymCoordSubspace n (min n (d + 1)) I ×
            LinearMap.ker
              (sourceSelectedComplexGramDifferentialToSym d n
                (min n (d + 1)) z0 I)))
        (e.symm y) := by
    simpa [e, sourceSelectedComplexGramImplicitChartAt_apply] using hprod_has
  have he_cont :
      ContDiffAt ℂ ⊤ e (e.symm y) := by
    have hprod_cont :
        ContDiffAt ℂ ⊤
          (sourceSelectedComplexGramProdMapAt d n (z0 := z0) I) (e.symm y) :=
      (contDiff_sourceSelectedComplexGramProdMapAt d n hI
        (z0 := z0)).contDiffAt
    simpa [e, sourceSelectedComplexGramImplicitChartAt_apply] using hprod_cont
  have hsymm : ContDiffAt ℂ ⊤ e.symm y :=
    e.contDiffAt_symm hy he_has he_cont
  have hzero :
      ContDiffWithinAt ℂ ⊤
        (sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI) D q :=
    (sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI).contDiff.contDiffAt
      |>.contDiffWithinAt
  have hcomp :
      ContDiffWithinAt ℂ ⊤
        (fun q =>
          e.symm
            (sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q))
        D q :=
    hsymm.comp_contDiffWithinAt q hzero
  simpa [e] using hcomp.differentiableWithinAt (by simp)

/-- The complex-base zero-kernel section has the prescribed selected Gram
coordinates. -/
theorem sourceSelectedComplexGramZeroSectionAt_selectedGram
    (d n : ℕ)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceComplexRegularMinor d n I J z0 ≠ 0)
    (q : Fin (Fintype.card
        (sourceSelectedSymCoordKey n (min n (d + 1)) I)) → ℂ)
    (htarget :
      sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q ∈
        (sourceSelectedComplexGramImplicitChartAt d n hI hJ hminor).target) :
    sourceSelectedComplexGramMap d n (min n (d + 1)) I
        ((sourceSelectedComplexGramImplicitChartAt d n hI hJ hminor).symm
          (sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q)) =
      (sourceSelectedComplexSymCoordFinEquiv n (min n (d + 1)) hI).symm q := by
  let m := min n (d + 1)
  let e := sourceSelectedComplexGramImplicitChartAt d n hI hJ hminor
  let y := sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q
  have hright : e (e.symm y) = y := e.right_inv htarget
  have hfst := congrArg Prod.fst hright
  simpa [e, y, m, sourceSelectedComplexGramImplicitChartAt_apply,
    sourceSelectedComplexGramProdMapAt] using hfst

/-- At the base selected coordinate, the complex-base zero-kernel section is
the base source point. -/
theorem sourceSelectedComplexGramZeroSectionAt_base
    (d n : ℕ)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceComplexRegularMinor d n I J z0 ≠ 0) :
    (sourceSelectedComplexGramImplicitChartAt d n hI hJ hminor).symm
        (sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI
          ((sourceSelectedComplexSymCoordFinEquiv n (min n (d + 1)) hI)
            (sourceSelectedComplexGramMap d n (min n (d + 1)) I z0))) =
      z0 := by
  let m := min n (d + 1)
  let e := sourceSelectedComplexGramImplicitChartAt d n hI hJ hminor
  let q0 :=
    (sourceSelectedComplexSymCoordFinEquiv n m hI)
      (sourceSelectedComplexGramMap d n m I z0)
  have hz0e : z0 ∈ e.source :=
    sourceSelectedComplexGramImplicitChartAt_mem_source d n hI hJ hminor
  have htarget :
      sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q0 =
        e z0 := by
    rw [sourceSelectedComplexGramImplicitChartAt_self]
    simp [q0, m]
  rw [show (sourceSelectedComplexSymCoordFinEquiv n (min n (d + 1)) hI)
        (sourceSelectedComplexGramMap d n (min n (d + 1)) I z0) = q0 by rfl]
  rw [htarget]
  exact e.left_inv hz0e

/-- Complex-base coordinate-ball shrink for the zero-section chart: after
shrinking flat selected coordinates around the base coordinate, the
zero-section stays in the chart target, the prescribed source neighborhood,
the nonzero selected-minor patch, and the derivative-invertible source patch. -/
theorem exists_sourceSelectedComplexGramZeroSectionAt_good_ball
    (d n : ℕ)
    {z0 : Fin n → Fin (d + 1) → ℂ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceComplexRegularMinor d n I J z0 ≠ 0)
    {V : Set (Fin n → Fin (d + 1) → ℂ)}
    (hV_open : IsOpen V)
    (hz0V : z0 ∈ V) :
    ∃ D : Set
      (Fin (Fintype.card
        (sourceSelectedSymCoordKey n (min n (d + 1)) I)) → ℂ),
      IsOpen D ∧ IsConnected D ∧
      ((sourceSelectedComplexSymCoordFinEquiv n (min n (d + 1)) hI)
        (sourceSelectedComplexGramMap d n (min n (d + 1)) I z0)) ∈ D ∧
      (∀ q ∈ D,
        sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q ∈
          (sourceSelectedComplexGramImplicitChartAt d n hI hJ hminor).target) ∧
      (∀ q ∈ D,
        (sourceSelectedComplexGramImplicitChartAt d n hI hJ hminor).symm
          (sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q) ∈ V) ∧
      (∀ q ∈ D,
        sourceComplexRegularMinor d n I J
          ((sourceSelectedComplexGramImplicitChartAt d n hI hJ hminor).symm
            (sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q)) ≠ 0) ∧
      (∀ q ∈ D,
        (fderiv ℂ (sourceSelectedComplexGramProdMapAt d n (z0 := z0) I)
          ((sourceSelectedComplexGramImplicitChartAt d n hI hJ hminor).symm
            (sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q))).IsInvertible) := by
  let m := min n (d + 1)
  let e := sourceSelectedComplexGramImplicitChartAt d n hI hJ hminor
  let q0 :=
    (sourceSelectedComplexSymCoordFinEquiv n m hI)
      (sourceSelectedComplexGramMap d n m I z0)
  let y0 := sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q0
  let Vminor : Set (Fin n → Fin (d + 1) → ℂ) :=
    V ∩ {z | sourceComplexRegularMinor d n I J z ≠ 0}
  have hVminor_open : IsOpen Vminor := by
    exact hV_open.inter
      (isOpen_ne_fun (continuous_sourceComplexRegularMinor d n I J)
        continuous_const)
  have hz0Vminor : z0 ∈ Vminor := ⟨hz0V, hminor⟩
  rcases sourceSelectedComplexGramProdMapAt_local_invertible_nhds
      d n hI hJ hminor hVminor_open hz0Vminor with
    ⟨W, hW_open, hz0W, hWVminor, hWinv⟩
  have hz0e : z0 ∈ e.source :=
    sourceSelectedComplexGramImplicitChartAt_mem_source d n hI hJ hminor
  have hy0_eq : y0 = e z0 := by
    rw [sourceSelectedComplexGramImplicitChartAt_self]
    simp [q0, y0, m]
  have hy0_target : y0 ∈ e.target := by
    rw [hy0_eq]
    exact e.map_source hz0e
  have hzero_target_nhds :
      {q |
        sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q ∈
          e.target} ∈ 𝓝 q0 := by
    exact
      (sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI).continuous
        |>.continuousAt
        |>.preimage_mem_nhds (e.open_target.mem_nhds hy0_target)
  have hsection_cont :
      ContinuousAt
        (fun q =>
          e.symm (sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q))
        q0 := by
    have hsymm0 :
        ContinuousAt e.symm
          (sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q0) := by
      simpa [y0] using e.continuousAt_symm hy0_target
    exact hsymm0.comp
      (sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI).continuous.continuousAt
  have hsection_W_nhds :
      {q |
        e.symm (sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q) ∈
          W} ∈ 𝓝 q0 := by
    have hbase :
        e.symm y0 ∈ W := by
      rw [hy0_eq]
      rw [e.left_inv hz0e]
      exact hz0W
    exact hsection_cont.preimage_mem_nhds (hW_open.mem_nhds hbase)
  have hgood_nhds :
      ({q |
        sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q ∈
          e.target} ∩
        {q |
          e.symm
              (sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q) ∈
            W}) ∈ 𝓝 q0 :=
    inter_mem hzero_target_nhds hsection_W_nhds
  rcases Metric.mem_nhds_iff.mp hgood_nhds with ⟨ε, hεpos, hεsub⟩
  let D : Set
      (Fin (Fintype.card (sourceSelectedSymCoordKey n m I)) → ℂ) :=
    Metric.ball q0 ε
  refine ⟨D, Metric.isOpen_ball, Metric.isConnected_ball hεpos,
    Metric.mem_ball_self hεpos, ?_, ?_, ?_, ?_⟩
  · intro q hq
    exact (hεsub hq).1
  · intro q hq
    exact (hWVminor (hεsub hq).2).1
  · intro q hq
    exact (hWVminor (hεsub hq).2).2
  · intro q hq
    exact hWinv
      ((sourceSelectedComplexGramImplicitChartAt d n hI hJ hminor).symm
        (sourceSelectedComplexZeroKernelTargetCLMAt d n (z0 := z0) hI q))
      (hεsub hq).2

end BHW
