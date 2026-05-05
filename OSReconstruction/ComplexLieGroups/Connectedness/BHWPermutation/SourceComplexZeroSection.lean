import Mathlib.Analysis.Normed.Module.Connected
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceComplexChart

/-!
# Complex selected source Gram zero-section support

This companion file keeps the analytic inverse-chart/zero-section frontier out
of the already checked selected chart algebra file.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace Polynomial
open scoped Matrix.Norms.Operator

namespace BHW

/-- The canonical selected complex implicit chart at a real nonzero-minor
source point.  Its underlying map is the selected Gram map together with the
fixed projection to the base kernel. -/
noncomputable def sourceSelectedComplexGramImplicitChart
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceRegularMinor d n I J x0 ≠ 0) :
    OpenPartialHomeomorph
      (Fin n → Fin (d + 1) → ℂ)
      (sourceSelectedComplexSymCoordSubspace n (min n (d + 1)) I ×
        LinearMap.ker
          (sourceSelectedComplexGramDifferentialToSym d n
            (min n (d + 1)) (realEmbed x0) I)) := by
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
  exact hstrict.implicitToOpenPartialHomeomorph f f' hsurj

/-- The canonical selected complex implicit chart is exactly the product map
used in the zero-section differentiability proof. -/
theorem sourceSelectedComplexGramImplicitChart_apply
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceRegularMinor d n I J x0 ≠ 0)
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceSelectedComplexGramImplicitChart d n hI hJ hminor z =
      sourceSelectedComplexGramProdMap d n I (x0 := x0) z := by
  unfold sourceSelectedComplexGramImplicitChart sourceSelectedComplexGramProdMap
  dsimp only
  rfl

/-- The base real point lies in the source of the canonical selected complex
implicit chart. -/
theorem sourceSelectedComplexGramImplicitChart_mem_source
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceRegularMinor d n I J x0 ≠ 0) :
    realEmbed x0 ∈
      (sourceSelectedComplexGramImplicitChart d n hI hJ hminor).source := by
  unfold sourceSelectedComplexGramImplicitChart
  dsimp only
  exact HasStrictFDerivAt.mem_implicitToOpenPartialHomeomorph_source _ _

/-- The canonical selected complex implicit chart sends the base real point to
the base selected Gram coordinate and zero vertical coordinate. -/
theorem sourceSelectedComplexGramImplicitChart_self
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceRegularMinor d n I J x0 ≠ 0) :
    sourceSelectedComplexGramImplicitChart d n hI hJ hminor (realEmbed x0) =
      (sourceSelectedComplexGramMap d n (min n (d + 1)) I (realEmbed x0), 0) := by
  rw [sourceSelectedComplexGramImplicitChart_apply]
  simp [sourceSelectedComplexGramProdMap]

/-- The flat selected-coordinate zero-kernel target map
`q ↦ ((selected-coordinate equivalence)⁻¹ q, 0)` for the canonical complex
implicit chart. -/
noncomputable def sourceSelectedComplexZeroKernelTargetCLM
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    (hI : Function.Injective I) :
    (Fin (Fintype.card
        (sourceSelectedSymCoordKey n (min n (d + 1)) I)) → ℂ) →L[ℂ]
      sourceSelectedComplexSymCoordSubspace n (min n (d + 1)) I ×
        LinearMap.ker
          (sourceSelectedComplexGramDifferentialToSym d n
            (min n (d + 1)) (realEmbed x0) I) :=
  ((sourceSelectedComplexSymCoordFinEquiv n (min n (d + 1)) hI).symm :
      (Fin (Fintype.card
        (sourceSelectedSymCoordKey n (min n (d + 1)) I)) → ℂ) →L[ℂ]
        sourceSelectedComplexSymCoordSubspace n (min n (d + 1)) I).prod 0

@[simp]
theorem sourceSelectedComplexZeroKernelTargetCLM_apply
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    (hI : Function.Injective I)
    (q : Fin (Fintype.card
        (sourceSelectedSymCoordKey n (min n (d + 1)) I)) → ℂ) :
    sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q =
      ((sourceSelectedComplexSymCoordFinEquiv n (min n (d + 1)) hI).symm q,
        0) :=
  rfl

/-- The zero-kernel section of the canonical selected complex implicit chart is
complex differentiable on every coordinate set whose points remain in the
chart target and whose inverse source points lie in the local derivative
invertibility region. -/
theorem sourceSelectedComplexGramZeroSection_differentiableOn
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceRegularMinor d n I J x0 ≠ 0)
    {D : Set
      (Fin (Fintype.card
        (sourceSelectedSymCoordKey n (min n (d + 1)) I)) → ℂ)}
    (hD_target :
      ∀ q ∈ D,
        sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q ∈
          (sourceSelectedComplexGramImplicitChart d n hI hJ hminor).target)
    (hD_invertible :
      ∀ q ∈ D,
        (fderiv ℂ (sourceSelectedComplexGramProdMap d n I (x0 := x0))
          ((sourceSelectedComplexGramImplicitChart d n hI hJ hminor).symm
            (sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q))).IsInvertible) :
    DifferentiableOn ℂ
      (fun q =>
        (sourceSelectedComplexGramImplicitChart d n hI hJ hminor).symm
          (sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q))
      D := by
  intro q hq
  let e := sourceSelectedComplexGramImplicitChart d n hI hJ hminor
  let y := sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q
  have hy : y ∈ e.target := hD_target q hq
  rcases hD_invertible q hq with ⟨A, hA⟩
  have hprod_has :
      HasFDerivAt (sourceSelectedComplexGramProdMap d n I (x0 := x0))
        (A : (Fin n → Fin (d + 1) → ℂ) →L[ℂ]
          (sourceSelectedComplexSymCoordSubspace n (min n (d + 1)) I ×
            LinearMap.ker
              (sourceSelectedComplexGramDifferentialToSym d n
                (min n (d + 1)) (realEmbed x0) I)))
        (e.symm y) := by
    rw [hA, sourceSelectedComplexGramProdMap_fderiv]
    exact sourceSelectedComplexGramProdMap_hasFDerivAt d n I (e.symm y)
  have he_has :
      HasFDerivAt e
        (A : (Fin n → Fin (d + 1) → ℂ) →L[ℂ]
          (sourceSelectedComplexSymCoordSubspace n (min n (d + 1)) I ×
            LinearMap.ker
              (sourceSelectedComplexGramDifferentialToSym d n
                (min n (d + 1)) (realEmbed x0) I)))
        (e.symm y) := by
    simpa [e, sourceSelectedComplexGramImplicitChart_apply] using hprod_has
  have he_cont :
      ContDiffAt ℂ ⊤ e (e.symm y) := by
    have hprod_cont :
        ContDiffAt ℂ ⊤
          (sourceSelectedComplexGramProdMap d n I (x0 := x0)) (e.symm y) :=
      (contDiff_sourceSelectedComplexGramProdMap d n hI (x0 := x0)).contDiffAt
    simpa [e, sourceSelectedComplexGramImplicitChart_apply] using hprod_cont
  have hsymm : ContDiffAt ℂ ⊤ e.symm y :=
    e.contDiffAt_symm hy he_has he_cont
  have hzero :
      ContDiffWithinAt ℂ ⊤
        (sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI) D q :=
    (sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI).contDiff.contDiffAt
      |>.contDiffWithinAt
  have hcomp :
      ContDiffWithinAt ℂ ⊤
        (fun q =>
          e.symm
            (sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q))
        D q :=
    hsymm.comp_contDiffWithinAt q hzero
  simpa [e] using hcomp.differentiableWithinAt (by simp)

/-- The complex zero-kernel section has the prescribed selected Gram
coordinates. -/
theorem sourceSelectedComplexGramZeroSection_selectedGram
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceRegularMinor d n I J x0 ≠ 0)
    (q : Fin (Fintype.card
        (sourceSelectedSymCoordKey n (min n (d + 1)) I)) → ℂ)
    (htarget :
      sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q ∈
        (sourceSelectedComplexGramImplicitChart d n hI hJ hminor).target) :
    sourceSelectedComplexGramMap d n (min n (d + 1)) I
        ((sourceSelectedComplexGramImplicitChart d n hI hJ hminor).symm
          (sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q)) =
      (sourceSelectedComplexSymCoordFinEquiv n (min n (d + 1)) hI).symm q := by
  let m := min n (d + 1)
  let e := sourceSelectedComplexGramImplicitChart d n hI hJ hminor
  let y := sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q
  have hright : e (e.symm y) = y := e.right_inv htarget
  have hfst := congrArg Prod.fst hright
  simpa [e, y, m, sourceSelectedComplexGramImplicitChart_apply,
    sourceSelectedComplexGramProdMap] using hfst

/-- At the base selected coordinate, the complex zero-kernel section is the
base real source point. -/
theorem sourceSelectedComplexGramZeroSection_base
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceRegularMinor d n I J x0 ≠ 0) :
    (sourceSelectedComplexGramImplicitChart d n hI hJ hminor).symm
        (sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI
          ((sourceSelectedComplexSymCoordFinEquiv n (min n (d + 1)) hI)
            (sourceSelectedComplexGramMap d n (min n (d + 1)) I
              (realEmbed x0)))) =
      realEmbed x0 := by
  let m := min n (d + 1)
  let e := sourceSelectedComplexGramImplicitChart d n hI hJ hminor
  let q0 :=
    (sourceSelectedComplexSymCoordFinEquiv n m hI)
      (sourceSelectedComplexGramMap d n m I (realEmbed x0))
  have hx0e : realEmbed x0 ∈ e.source :=
    sourceSelectedComplexGramImplicitChart_mem_source d n hI hJ hminor
  have htarget :
      sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q0 =
        e (realEmbed x0) := by
    rw [sourceSelectedComplexGramImplicitChart_self]
    simp [q0, m]
  rw [show (sourceSelectedComplexSymCoordFinEquiv n (min n (d + 1)) hI)
        (sourceSelectedComplexGramMap d n (min n (d + 1)) I
          (realEmbed x0)) = q0 by rfl]
  rw [htarget]
  exact e.left_inv hx0e

/-- Flat selected coordinates of a full complex Gram matrix, retaining the same
kept lower-triangular selected keys as
`sourceSelectedComplexSymCoordFinEquiv`. -/
noncomputable def sourceSelectedComplexGramFlatCoordCLM
    (n m : ℕ)
    (I : Fin m → Fin n) :
    (Fin n → Fin n → ℂ) →L[ℂ]
      (Fin (Fintype.card (sourceSelectedSymCoordKey n m I)) → ℂ) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun G k =>
      let q := (Fintype.equivFin (sourceSelectedSymCoordKey n m I)).symm k
      G q.val.1 (I q.val.2)
    map_add' := by
      intro G H
      ext k
      rfl
    map_smul' := by
      intro c G
      ext k
      rfl }

@[simp]
theorem sourceSelectedComplexGramFlatCoordCLM_apply
    (n m : ℕ)
    (I : Fin m → Fin n)
    (G : Fin n → Fin n → ℂ)
    (k : Fin (Fintype.card (sourceSelectedSymCoordKey n m I))) :
    sourceSelectedComplexGramFlatCoordCLM n m I G k =
      G ((Fintype.equivFin (sourceSelectedSymCoordKey n m I)).symm k).val.1
        (I ((Fintype.equivFin (sourceSelectedSymCoordKey n m I)).symm k).val.2) :=
  rfl

/-- The flat selected coordinates of a source Gram matrix agree with the flat
selected coordinates of its selected symmetric-coordinate subspace point. -/
theorem sourceSelectedComplexGramFlatCoordCLM_source
    (d n m : ℕ)
    {I : Fin m → Fin n}
    (hI : Function.Injective I)
    (z : Fin n → Fin (d + 1) → ℂ) :
    sourceSelectedComplexGramFlatCoordCLM n m I (sourceMinkowskiGram d n z) =
      sourceSelectedComplexSymCoordFinEquiv n m hI
        (sourceSelectedComplexGramMap d n m I z) := by
  ext k
  simp [sourceSelectedComplexGramFlatCoordCLM,
    sourceSelectedComplexSymCoordFinEquiv,
    sourceSelectedComplexSymCoordKeyEquiv,
    ContinuousLinearEquiv.piCongrLeft,
    Equiv.piCongrLeft_apply_eq_cast]
  rfl

/-- On the complex source Gram variety, equality of flat selected coordinates
is equality of the selected symmetric-coordinate subspace point. -/
theorem sourceSelectedComplexGramCoord_eq_of_flatCoord_eq
    (d n m : ℕ)
    {I : Fin m → Fin n}
    (hI : Function.Injective I)
    {G : Fin n → Fin n → ℂ}
    (hG : G ∈ sourceComplexGramVariety d n)
    {q : Fin (Fintype.card (sourceSelectedSymCoordKey n m I)) → ℂ}
    (hflat : sourceSelectedComplexGramFlatCoordCLM n m I G = q) :
    (⟨sourceSelectedComplexGramCoord n m I G, by
      rcases hG with ⟨z, rfl⟩
      intro a b
      simp [sourceSelectedComplexGramCoord_apply,
        sourceMinkowskiGram_symm d n z (I a) (I b)]⟩ :
        sourceSelectedComplexSymCoordSubspace n m I) =
      (sourceSelectedComplexSymCoordFinEquiv n m hI).symm q := by
  apply (sourceSelectedComplexSymCoordFinEquiv n m hI).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  calc
    sourceSelectedComplexSymCoordFinEquiv n m hI
        (⟨sourceSelectedComplexGramCoord n m I G, by
          rcases hG with ⟨z, rfl⟩
          intro a b
          simp [sourceSelectedComplexGramCoord_apply,
            sourceMinkowskiGram_symm d n z (I a) (I b)]⟩ :
          sourceSelectedComplexSymCoordSubspace n m I)
        = sourceSelectedComplexGramFlatCoordCLM n m I G := by
            ext k
            simp [sourceSelectedComplexGramFlatCoordCLM,
              sourceSelectedComplexSymCoordFinEquiv,
              sourceSelectedComplexSymCoordKeyEquiv,
              ContinuousLinearEquiv.piCongrLeft,
              Equiv.piCongrLeft_apply_eq_cast]
            rfl
    _ = q := hflat

/-- The zero-section image is exactly the part of the complex Gram variety
whose flat selected coordinates lie in the coordinate set. -/
theorem sourceSelectedComplexGramZeroSection_image_eq_flatCoord_preimage
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceRegularMinor d n I J x0 ≠ 0)
    {D : Set
      (Fin (Fintype.card
        (sourceSelectedSymCoordKey n (min n (d + 1)) I)) → ℂ)}
    (hD_target :
      ∀ q ∈ D,
        sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q ∈
          (sourceSelectedComplexGramImplicitChart d n hI hJ hminor).target)
    (hD_minor :
      ∀ q ∈ D,
        sourceComplexRegularMinor d n I J
          ((sourceSelectedComplexGramImplicitChart d n hI hJ hminor).symm
            (sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q)) ≠ 0) :
    ((fun q =>
        sourceMinkowskiGram d n
          ((sourceSelectedComplexGramImplicitChart d n hI hJ hminor).symm
            (sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q))) '' D) =
      {G |
        sourceSelectedComplexGramFlatCoordCLM n (min n (d + 1)) I G ∈ D} ∩
        sourceComplexGramVariety d n := by
  let m := min n (d + 1)
  let e := sourceSelectedComplexGramImplicitChart d n hI hJ hminor
  let Z :=
    fun q : Fin (Fintype.card (sourceSelectedSymCoordKey n m I)) → ℂ =>
      e.symm (sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q)
  ext G
  constructor
  · rintro ⟨q, hqD, rfl⟩
    have hsel :
        sourceSelectedComplexGramMap d n m I (Z q) =
          (sourceSelectedComplexSymCoordFinEquiv n m hI).symm q := by
      simpa [Z, e, m] using
        sourceSelectedComplexGramZeroSection_selectedGram d n hI hJ hminor q
          (hD_target q hqD)
    constructor
    · have hflat :
          sourceSelectedComplexGramFlatCoordCLM n m I
              (sourceMinkowskiGram d n (Z q)) =
            q := by
        calc
          sourceSelectedComplexGramFlatCoordCLM n m I
              (sourceMinkowskiGram d n (Z q))
              = sourceSelectedComplexSymCoordFinEquiv n m hI
                  (sourceSelectedComplexGramMap d n m I (Z q)) := by
                    exact sourceSelectedComplexGramFlatCoordCLM_source d n m hI (Z q)
          _ = q := by
                rw [hsel, ContinuousLinearEquiv.apply_symm_apply]
      change sourceSelectedComplexGramFlatCoordCLM n m I
          (sourceMinkowskiGram d n (Z q)) ∈ D
      rw [hflat]
      exact hqD
    · exact ⟨Z q, rfl⟩
  · rintro ⟨hflatD, hGvar⟩
    let q := sourceSelectedComplexGramFlatCoordCLM n m I G
    have hqD : q ∈ D := hflatD
    let zq := Z q
    have hsectionSel :
        sourceSelectedComplexGramMap d n m I zq =
          (sourceSelectedComplexSymCoordFinEquiv n m hI).symm q := by
      simpa [zq, Z, e, m] using
        sourceSelectedComplexGramZeroSection_selectedGram d n hI hJ hminor q
          (hD_target q hqD)
    have hGselSubtype :
        (⟨sourceSelectedComplexGramCoord n m I G, by
          rcases hGvar with ⟨z, rfl⟩
          intro a b
          simp [sourceSelectedComplexGramCoord_apply,
            sourceMinkowskiGram_symm d n z (I a) (I b)]⟩ :
            sourceSelectedComplexSymCoordSubspace n m I) =
          (sourceSelectedComplexSymCoordFinEquiv n m hI).symm q := by
      exact sourceSelectedComplexGramCoord_eq_of_flatCoord_eq d n m hI hGvar rfl
    have hsel :
        sourceSelectedComplexGramCoord n m I (sourceMinkowskiGram d n zq) =
          sourceSelectedComplexGramCoord n m I G := by
      have hleft := congrArg Subtype.val hsectionSel
      have hright := congrArg Subtype.val hGselSubtype
      exact hleft.trans hright.symm
    have hfull :
        sourceMinkowskiGram d n zq = G :=
      sourceSelectedComplexGramCoord_eq_fullGram_eq_of_sourceComplexRegularMinor_ne_zero_of_mem_variety
        d n hI (hD_minor q hqD) hGvar hsel
    exact ⟨q, hqD, hfull⟩

/-- The zero-section image over an open flat selected-coordinate set is
relatively open in the complex source Gram variety, provided the section stays
inside the chart target and the nonzero selected-minor patch. -/
theorem sourceSelectedComplexGramZeroSection_image_relOpen
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceRegularMinor d n I J x0 ≠ 0)
    {D : Set
      (Fin (Fintype.card
        (sourceSelectedSymCoordKey n (min n (d + 1)) I)) → ℂ)}
    (hD_open : IsOpen D)
    (hD_target :
      ∀ q ∈ D,
        sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q ∈
          (sourceSelectedComplexGramImplicitChart d n hI hJ hminor).target)
    (hD_minor :
      ∀ q ∈ D,
        sourceComplexRegularMinor d n I J
          ((sourceSelectedComplexGramImplicitChart d n hI hJ hminor).symm
            (sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q)) ≠ 0) :
    IsRelOpenInSourceComplexGramVariety d n
      ((fun q =>
        sourceMinkowskiGram d n
          ((sourceSelectedComplexGramImplicitChart d n hI hJ hminor).symm
            (sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q))) '' D) := by
  let m := min n (d + 1)
  let E0 : Set (Fin n → Fin n → ℂ) :=
    {G | sourceSelectedComplexGramFlatCoordCLM n m I G ∈ D}
  have hE0_open : IsOpen E0 := by
    exact hD_open.preimage (sourceSelectedComplexGramFlatCoordCLM n m I).continuous
  refine ⟨E0, hE0_open, ?_⟩
  simpa [E0, m] using
    sourceSelectedComplexGramZeroSection_image_eq_flatCoord_preimage
      d n hI hJ hminor hD_target hD_minor

/-- The Gram-valued complex zero-section chart map is complex differentiable on
coordinate sets satisfying the target and derivative-invertibility hypotheses. -/
theorem sourceSelectedComplexGramZeroSection_gram_differentiableOn
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceRegularMinor d n I J x0 ≠ 0)
    {D : Set
      (Fin (Fintype.card
        (sourceSelectedSymCoordKey n (min n (d + 1)) I)) → ℂ)}
    (hD_target :
      ∀ q ∈ D,
        sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q ∈
          (sourceSelectedComplexGramImplicitChart d n hI hJ hminor).target)
    (hD_invertible :
      ∀ q ∈ D,
        (fderiv ℂ (sourceSelectedComplexGramProdMap d n I (x0 := x0))
          ((sourceSelectedComplexGramImplicitChart d n hI hJ hminor).symm
            (sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q))).IsInvertible) :
    DifferentiableOn ℂ
      (fun q =>
        sourceMinkowskiGram d n
          ((sourceSelectedComplexGramImplicitChart d n hI hJ hminor).symm
            (sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q)))
      D := by
  have hsec :
      DifferentiableOn ℂ
        (fun q =>
          (sourceSelectedComplexGramImplicitChart d n hI hJ hminor).symm
            (sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q))
        D :=
    sourceSelectedComplexGramZeroSection_differentiableOn d n hI hJ hminor
      hD_target hD_invertible
  have hgram : Differentiable ℂ (sourceMinkowskiGram d n) :=
    (contDiff_sourceMinkowskiGram d n).differentiable (by simp)
  simpa [Function.comp_def] using
    hgram.comp_differentiableOn hsec

/-- Complex-side coordinate-ball shrink for the zero-section chart: after
shrinking flat selected coordinates around the base coordinate, the
zero-section stays in the canonical chart target, the prescribed source
neighborhood, the nonzero selected-minor patch, and the derivative-invertible
source patch. -/
theorem exists_sourceSelectedComplexGramZeroSection_good_ball
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
    ∃ D : Set
      (Fin (Fintype.card
        (sourceSelectedSymCoordKey n (min n (d + 1)) I)) → ℂ),
      IsOpen D ∧ IsConnected D ∧
      ((sourceSelectedComplexSymCoordFinEquiv n (min n (d + 1)) hI)
        (sourceSelectedComplexGramMap d n (min n (d + 1)) I
          (realEmbed x0))) ∈ D ∧
      (∀ q ∈ D,
        sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q ∈
          (sourceSelectedComplexGramImplicitChart d n hI hJ hminor).target) ∧
      (∀ q ∈ D,
        (sourceSelectedComplexGramImplicitChart d n hI hJ hminor).symm
          (sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q) ∈ V) ∧
      (∀ q ∈ D,
        sourceComplexRegularMinor d n I J
          ((sourceSelectedComplexGramImplicitChart d n hI hJ hminor).symm
            (sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q)) ≠ 0) ∧
      (∀ q ∈ D,
        (fderiv ℂ (sourceSelectedComplexGramProdMap d n I (x0 := x0))
          ((sourceSelectedComplexGramImplicitChart d n hI hJ hminor).symm
            (sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q))).IsInvertible) := by
  let m := min n (d + 1)
  let e := sourceSelectedComplexGramImplicitChart d n hI hJ hminor
  let q0 :=
    (sourceSelectedComplexSymCoordFinEquiv n m hI)
      (sourceSelectedComplexGramMap d n m I (realEmbed x0))
  let y0 := sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q0
  let Vminor : Set (Fin n → Fin (d + 1) → ℂ) :=
    V ∩ {z | sourceComplexRegularMinor d n I J z ≠ 0}
  have hminorC : sourceComplexRegularMinor d n I J (realEmbed x0) ≠ 0 := by
    rw [sourceComplexRegularMinor_realEmbed]
    exact (Complex.ofReal_ne_zero).2 hminor
  have hVminor_open : IsOpen Vminor := by
    exact hV_open.inter
      (isOpen_ne_fun (continuous_sourceComplexRegularMinor d n I J)
        continuous_const)
  have hx0Vminor : realEmbed x0 ∈ Vminor := ⟨hx0V, hminorC⟩
  rcases sourceSelectedComplexGramProdMap_local_invertible_nhds
      d n hI hJ hminor hVminor_open hx0Vminor with
    ⟨W, hW_open, hx0W, hWVminor, hWinv⟩
  have hx0e : realEmbed x0 ∈ e.source :=
    sourceSelectedComplexGramImplicitChart_mem_source d n hI hJ hminor
  have hy0_eq : y0 = e (realEmbed x0) := by
    rw [sourceSelectedComplexGramImplicitChart_self]
    simp [q0, y0, m]
  have hy0_target : y0 ∈ e.target := by
    rw [hy0_eq]
    exact e.map_source hx0e
  have hzero_target_nhds :
      {q |
        sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q ∈
          e.target} ∈ 𝓝 q0 := by
    exact
      (sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI).continuous
        |>.continuousAt
        |>.preimage_mem_nhds (e.open_target.mem_nhds hy0_target)
  have hsection_cont :
      ContinuousAt
        (fun q =>
          e.symm (sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q))
        q0 := by
    have hsymm0 :
        ContinuousAt e.symm
          (sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q0) := by
      simpa [y0] using e.continuousAt_symm hy0_target
    exact hsymm0.comp
      (sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI).continuous.continuousAt
  have hsection_W_nhds :
      {q |
        e.symm (sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q) ∈
          W} ∈ 𝓝 q0 := by
    have hbase :
        e.symm y0 ∈ W := by
      rw [hy0_eq]
      rw [e.left_inv hx0e]
      exact hx0W
    exact hsection_cont.preimage_mem_nhds (hW_open.mem_nhds hbase)
  have hgood_nhds :
      ({q |
        sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q ∈
          e.target} ∩
        {q |
          e.symm
              (sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q) ∈
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
      ((sourceSelectedComplexGramImplicitChart d n hI hJ hminor).symm
        (sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI q))
      (hεsub hq).2

/-- The inverse flat selected-coordinate equivalences commute with the real
slice. -/
theorem sourceSelectedComplexSymCoordFinEquiv_symm_real_slice
    (n m : ℕ)
    {I : Fin m → Fin n}
    (hI : Function.Injective I)
    (q : Fin (Fintype.card (sourceSelectedSymCoordKey n m I)) → ℝ) :
    (sourceSelectedComplexSymCoordFinEquiv n m hI).symm (SCV.realToComplex q) =
      sourceSelectedSymCoordRealComplexify n m I
        ((sourceSelectedRealSymCoordFinEquiv n m hI).symm q) := by
  apply (sourceSelectedComplexSymCoordFinEquiv n m hI).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [sourceSelectedComplexSymCoordFinEquiv_real_slice]
  rw [ContinuousLinearEquiv.apply_symm_apply]

/-- The canonical selected real implicit chart at a real nonzero-minor source
point. -/
noncomputable def sourceSelectedRealGramImplicitChart
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceRegularMinor d n I J x0 ≠ 0) :
    OpenPartialHomeomorph
      (Fin n → Fin (d + 1) → ℝ)
      (sourceSelectedSymCoordSubspace n (min n (d + 1)) I ×
        LinearMap.ker
          (sourceSelectedGramDifferentialToSym d n
            (min n (d + 1)) x0 I)) := by
  let m := min n (d + 1)
  let f := sourceSelectedRealGramMap d n m I
  let f' : (Fin n → Fin (d + 1) → ℝ) →L[ℝ]
      sourceSelectedSymCoordSubspace n m I :=
    LinearMap.toContinuousLinearMap
      (sourceSelectedGramDifferentialToSym d n m x0 I)
  have hstrict : HasStrictFDerivAt f f' x0 := by
    simpa [f, f'] using
      sourceSelectedRealGramMap_hasStrictFDerivAt d n m I x0
  have hsurj : f'.range = ⊤ := by
    exact LinearMap.range_eq_top.mpr
      (sourceSelectedGramDifferentialToSym_surjective_of_sourceRegularMinor_ne_zero
        d n hI hJ hminor)
  exact hstrict.implicitToOpenPartialHomeomorph f f' hsurj

/-- The base real point lies in the source of the canonical selected real
implicit chart. -/
theorem sourceSelectedRealGramImplicitChart_mem_source
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceRegularMinor d n I J x0 ≠ 0) :
    x0 ∈
      (sourceSelectedRealGramImplicitChart d n hI hJ hminor).source := by
  unfold sourceSelectedRealGramImplicitChart
  dsimp only
  exact HasStrictFDerivAt.mem_implicitToOpenPartialHomeomorph_source _ _

/-- The canonical selected real implicit chart sends the base point to the
base selected Gram coordinate and zero vertical coordinate. -/
theorem sourceSelectedRealGramImplicitChart_self
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceRegularMinor d n I J x0 ≠ 0) :
    sourceSelectedRealGramImplicitChart d n hI hJ hminor x0 =
      (sourceSelectedRealGramMap d n (min n (d + 1)) I x0, 0) := by
  unfold sourceSelectedRealGramImplicitChart
  dsimp only
  exact HasStrictFDerivAt.implicitToOpenPartialHomeomorph_self _ _

/-- The first component of the canonical selected real implicit chart is the
selected real Gram coordinate map. -/
theorem sourceSelectedRealGramImplicitChart_fst
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceRegularMinor d n I J x0 ≠ 0)
    (x : Fin n → Fin (d + 1) → ℝ) :
    (sourceSelectedRealGramImplicitChart d n hI hJ hminor x).1 =
      sourceSelectedRealGramMap d n (min n (d + 1)) I x := by
  unfold sourceSelectedRealGramImplicitChart
  dsimp only
  exact HasStrictFDerivAt.implicitToOpenPartialHomeomorph_fst _ _ x

/-- The flat selected-coordinate zero-kernel target map for the canonical real
implicit chart. -/
noncomputable def sourceSelectedRealZeroKernelTargetCLM
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    (hI : Function.Injective I) :
    (Fin (Fintype.card
        (sourceSelectedSymCoordKey n (min n (d + 1)) I)) → ℝ) →L[ℝ]
      sourceSelectedSymCoordSubspace n (min n (d + 1)) I ×
        LinearMap.ker
          (sourceSelectedGramDifferentialToSym d n
            (min n (d + 1)) x0 I) :=
  ((sourceSelectedRealSymCoordFinEquiv n (min n (d + 1)) hI).symm :
      (Fin (Fintype.card
        (sourceSelectedSymCoordKey n (min n (d + 1)) I)) → ℝ) →L[ℝ]
        sourceSelectedSymCoordSubspace n (min n (d + 1)) I).prod 0

@[simp]
theorem sourceSelectedRealZeroKernelTargetCLM_apply
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    (hI : Function.Injective I)
    (q : Fin (Fintype.card
        (sourceSelectedSymCoordKey n (min n (d + 1)) I)) → ℝ) :
    sourceSelectedRealZeroKernelTargetCLM d n (x0 := x0) hI q =
      ((sourceSelectedRealSymCoordFinEquiv n (min n (d + 1)) hI).symm q,
        0) :=
  rfl

/-- The real zero-kernel section has the prescribed selected Gram
coordinates. -/
theorem sourceSelectedRealGramZeroSection_selectedGram
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceRegularMinor d n I J x0 ≠ 0)
    (q : Fin (Fintype.card
        (sourceSelectedSymCoordKey n (min n (d + 1)) I)) → ℝ)
    (htarget :
      sourceSelectedRealZeroKernelTargetCLM d n (x0 := x0) hI q ∈
        (sourceSelectedRealGramImplicitChart d n hI hJ hminor).target) :
    sourceSelectedRealGramMap d n (min n (d + 1)) I
        ((sourceSelectedRealGramImplicitChart d n hI hJ hminor).symm
          (sourceSelectedRealZeroKernelTargetCLM d n (x0 := x0) hI q)) =
      (sourceSelectedRealSymCoordFinEquiv n (min n (d + 1)) hI).symm q := by
  let m := min n (d + 1)
  let e := sourceSelectedRealGramImplicitChart d n hI hJ hminor
  let y := sourceSelectedRealZeroKernelTargetCLM d n (x0 := x0) hI q
  have hright : e (e.symm y) = y := e.right_inv htarget
  have hfst := congrArg Prod.fst hright
  simpa [e, y, m, sourceSelectedRealGramImplicitChart_fst] using hfst

/-- At the base selected coordinate, the real zero-kernel section is the base
source point. -/
theorem sourceSelectedRealGramZeroSection_base
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceRegularMinor d n I J x0 ≠ 0) :
    (sourceSelectedRealGramImplicitChart d n hI hJ hminor).symm
        (sourceSelectedRealZeroKernelTargetCLM d n (x0 := x0) hI
          ((sourceSelectedRealSymCoordFinEquiv n (min n (d + 1)) hI)
            (sourceSelectedRealGramMap d n (min n (d + 1)) I x0))) =
      x0 := by
  let m := min n (d + 1)
  let e := sourceSelectedRealGramImplicitChart d n hI hJ hminor
  let q0 :=
    (sourceSelectedRealSymCoordFinEquiv n m hI)
      (sourceSelectedRealGramMap d n m I x0)
  have hx0e : x0 ∈ e.source :=
    sourceSelectedRealGramImplicitChart_mem_source d n hI hJ hminor
  have htarget :
      sourceSelectedRealZeroKernelTargetCLM d n (x0 := x0) hI q0 =
        e x0 := by
    rw [sourceSelectedRealGramImplicitChart_self]
    simp [q0, m]
  rw [show (sourceSelectedRealSymCoordFinEquiv n (min n (d + 1)) hI)
        (sourceSelectedRealGramMap d n (min n (d + 1)) I x0) = q0 by rfl]
  rw [htarget]
  exact e.left_inv hx0e

/-- The real zero-kernel section is continuous on every coordinate set whose
targets lie in the canonical real chart target. -/
theorem sourceSelectedRealGramZeroSection_continuousOn
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceRegularMinor d n I J x0 ≠ 0)
    {Vre : Set
      (Fin (Fintype.card
        (sourceSelectedSymCoordKey n (min n (d + 1)) I)) → ℝ)}
    (hV_target :
      ∀ q ∈ Vre,
        sourceSelectedRealZeroKernelTargetCLM d n (x0 := x0) hI q ∈
          (sourceSelectedRealGramImplicitChart d n hI hJ hminor).target) :
    ContinuousOn
      (fun q =>
        (sourceSelectedRealGramImplicitChart d n hI hJ hminor).symm
          (sourceSelectedRealZeroKernelTargetCLM d n (x0 := x0) hI q))
      Vre := by
  intro q hq
  let e := sourceSelectedRealGramImplicitChart d n hI hJ hminor
  have hzero :
      ContinuousWithinAt
        (sourceSelectedRealZeroKernelTargetCLM d n (x0 := x0) hI) Vre q :=
    (sourceSelectedRealZeroKernelTargetCLM d n (x0 := x0) hI).continuous.continuousAt
      |>.continuousWithinAt
  have hsymm :
      ContinuousAt e.symm
        (sourceSelectedRealZeroKernelTargetCLM d n (x0 := x0) hI q) :=
    e.continuousAt_symm (hV_target q hq)
  exact hsymm.comp_continuousWithinAt hzero

/-- On real flat selected coordinates, the complex zero-section Gram matrix is
the complexification of the real zero-section Gram matrix. -/
theorem sourceSelectedComplexGramZeroSection_real_slice_gram
    (d n : ℕ)
    {x0 : Fin n → Fin (d + 1) → ℝ}
    {I : Fin (min n (d + 1)) → Fin n}
    {J : Fin (min n (d + 1)) → Fin (d + 1)}
    (hI : Function.Injective I)
    (hJ : Function.Injective J)
    (hminor : sourceRegularMinor d n I J x0 ≠ 0)
    (q : Fin (Fintype.card
        (sourceSelectedSymCoordKey n (min n (d + 1)) I)) → ℝ)
    (hCtarget :
      sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI
          (SCV.realToComplex q) ∈
        (sourceSelectedComplexGramImplicitChart d n hI hJ hminor).target)
    (hRtarget :
      sourceSelectedRealZeroKernelTargetCLM d n (x0 := x0) hI q ∈
        (sourceSelectedRealGramImplicitChart d n hI hJ hminor).target)
    (hRminor :
      sourceRegularMinor d n I J
          ((sourceSelectedRealGramImplicitChart d n hI hJ hminor).symm
            (sourceSelectedRealZeroKernelTargetCLM d n (x0 := x0) hI q)) ≠ 0) :
    sourceMinkowskiGram d n
        ((sourceSelectedComplexGramImplicitChart d n hI hJ hminor).symm
          (sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI
            (SCV.realToComplex q))) =
      sourceRealGramComplexify n
        (sourceRealMinkowskiGram d n
          ((sourceSelectedRealGramImplicitChart d n hI hJ hminor).symm
            (sourceSelectedRealZeroKernelTargetCLM d n (x0 := x0) hI q))) := by
  let m := min n (d + 1)
  let eC := sourceSelectedComplexGramImplicitChart d n hI hJ hminor
  let eR := sourceSelectedRealGramImplicitChart d n hI hJ hminor
  let yC :=
    sourceSelectedComplexZeroKernelTargetCLM d n (x0 := x0) hI
      (SCV.realToComplex q)
  let yR := sourceSelectedRealZeroKernelTargetCLM d n (x0 := x0) hI q
  let zC := eC.symm yC
  let xR := eR.symm yR
  have hCright : eC zC = yC := eC.right_inv hCtarget
  have hRright : eR xR = yR := eR.right_inv hRtarget
  have hCsel :
      sourceSelectedComplexGramMap d n m I zC =
        (sourceSelectedComplexSymCoordFinEquiv n m hI).symm
          (SCV.realToComplex q) := by
    have h := congrArg Prod.fst hCright
    simpa [eC, yC, zC, m, sourceSelectedComplexGramImplicitChart_apply,
      sourceSelectedComplexGramProdMap] using h
  have hRsel :
      sourceSelectedRealGramMap d n m I xR =
        (sourceSelectedRealSymCoordFinEquiv n m hI).symm q := by
    have h := congrArg Prod.fst hRright
    simpa [eR, yR, xR, m, sourceSelectedRealGramImplicitChart_fst] using h
  have hsel :
      sourceSelectedComplexGramCoord n m I
          (sourceMinkowskiGram d n (realEmbed xR)) =
        sourceSelectedComplexGramCoord n m I
          (sourceMinkowskiGram d n zC) := by
    ext r a
    have hC := congrArg
      (fun A : sourceSelectedComplexSymCoordSubspace n m I =>
        (A : Fin n → Fin m → ℂ) r a) hCsel
    have hR := congrArg
      (fun A : sourceSelectedSymCoordSubspace n m I =>
        (A : Fin n → Fin m → ℝ) r a) hRsel
    have hslice :=
      congrArg
        (fun A : sourceSelectedComplexSymCoordSubspace n m I =>
          (A : Fin n → Fin m → ℂ) r a)
        (sourceSelectedComplexSymCoordFinEquiv_symm_real_slice n m hI q)
    simp [sourceSelectedComplexGramMap_apply,
      sourceSelectedRealGramMap_apply,
      sourceSelectedComplexGramCoord_apply,
      sourceSelectedSymCoordRealComplexify_apply] at hC hR hslice ⊢
    rw [sourceMinkowskiGram_realEmbed]
    change ((sourceRealMinkowskiGram d n xR r (I a) : ℂ) =
      sourceMinkowskiGram d n zC r (I a))
    rw [hR, ← hslice, ← hC]
  have hminorC :
      sourceComplexRegularMinor d n I J (realEmbed xR) ≠ 0 := by
    rw [sourceComplexRegularMinor_realEmbed]
    exact (Complex.ofReal_ne_zero).2 hRminor
  have hvar : sourceMinkowskiGram d n zC ∈ sourceComplexGramVariety d n :=
    ⟨zC, rfl⟩
  have hfull :
      sourceMinkowskiGram d n (realEmbed xR) =
        sourceMinkowskiGram d n zC :=
    sourceSelectedComplexGramCoord_eq_fullGram_eq_of_sourceComplexRegularMinor_ne_zero_of_mem_variety
      d n hI hminorC hvar hsel
  rw [sourceMinkowskiGram_realEmbed] at hfull
  exact hfull.symm

end BHW
