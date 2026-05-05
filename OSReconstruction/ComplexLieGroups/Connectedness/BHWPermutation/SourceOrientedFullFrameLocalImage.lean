import Mathlib.Analysis.Calculus.Implicit
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedFullFrameJacobi

/-!
# Local image support for full-frame oriented coordinates

This file starts the finite-dimensional local-image layer for the full-frame
gauge route.  It first turns the oriented hypersurface equation, restricted to
the symmetric coordinate submodule, into the exact input expected by Mathlib's
implicit-function theorem.
-/

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter NormedSpace
open scoped Matrix.Norms.Operator

namespace BHW

local instance sourceFullFrameSymmetricCoordSubmodule_isUniformAddGroup
    (d : ℕ) :
    IsUniformAddGroup (sourceFullFrameSymmetricCoordSubmodule d) :=
  (sourceFullFrameSymmetricCoordSubmodule d).toAddSubgroup.isUniformAddGroup

instance sourceFullFrameSymmetricCoordSubmodule_completeSpace
    (d : ℕ) :
    CompleteSpace (sourceFullFrameSymmetricCoordSubmodule d) :=
  FiniteDimensional.complete ℂ (sourceFullFrameSymmetricCoordSubmodule d)

local instance sourceFullFrameGaugeSliceData_slice_isUniformAddGroup
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (S : SourceFullFrameGaugeSliceData d M0) :
    IsUniformAddGroup S.slice :=
  S.slice.toAddSubgroup.isUniformAddGroup

instance sourceFullFrameGaugeSliceData_slice_completeSpace
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (S : SourceFullFrameGaugeSliceData d M0) :
    CompleteSpace S.slice :=
  FiniteDimensional.complete ℂ S.slice

/-- Restrict the codomain of a strictly differentiable map to a linear
subspace, provided both the map and its derivative land in that subspace. -/
theorem hasStrictFDerivAt_submodule_codRestrict
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (S : Submodule 𝕜 F)
    {f : E → F} {f' : E →L[𝕜] F} {x : E}
    (hf : HasStrictFDerivAt f f' x)
    (hmem : ∀ y, f y ∈ S)
    (hderiv : ∀ y, f' y ∈ S) :
    HasStrictFDerivAt (fun y => ⟨f y, hmem y⟩ : E → S)
      (f'.codRestrict S hderiv) x := by
  refine HasStrictFDerivAt.of_isLittleO ?_
  have hfo := hf.isLittleO
  rw [Asymptotics.isLittleO_iff] at hfo ⊢
  intro c hc
  filter_upwards [hfo hc] with p hp
  simpa using hp

/-- The oriented hypersurface equation restricted to symmetric full-frame
coordinates. -/
def sourceFullFrameSymmetricEquation (d : ℕ) :
    sourceFullFrameSymmetricCoordSubmodule d → ℂ :=
  fun H => sourceFullFrameOrientedEquation d (H : SourceFullFrameOrientedCoord d)

/-- The actual Frechet derivative of the symmetric restricted equation. -/
noncomputable def sourceFullFrameSymmetricEquationDerivCLM
    (d : ℕ) (H0 : SourceFullFrameOrientedCoord d) :
    sourceFullFrameSymmetricCoordSubmodule d →L[ℂ] ℂ :=
  (fderiv ℂ (sourceFullFrameOrientedEquation d) H0).comp
    (sourceFullFrameSymmetricCoordSubmodule d).subtypeL

/-- The symmetric-coordinate base point associated to an invertible full
frame. -/
def sourceFullFrameSymmetricBase
    (d : ℕ)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    sourceFullFrameSymmetricCoordSubmodule d :=
  ⟨sourceFullFrameOrientedGramCoord d M0,
    sourceFullFrameOrientedGramCoord_mem_symmetric d M0⟩

/-- Frechet derivative of the symmetric restricted equation. -/
theorem sourceFullFrameSymmetricEquation_hasFDerivAt
    (d : ℕ) (H0 : sourceFullFrameSymmetricCoordSubmodule d) :
    HasFDerivAt
      (sourceFullFrameSymmetricEquation d)
      (sourceFullFrameSymmetricEquationDerivCLM d
        (H0 : SourceFullFrameOrientedCoord d)) H0 := by
  unfold sourceFullFrameSymmetricEquation sourceFullFrameSymmetricEquationDerivCLM
  exact
    ((differentiable_sourceFullFrameOrientedEquation d).differentiableAt.hasFDerivAt.comp
      (x := H0)
      (sourceFullFrameSymmetricCoordSubmodule d).subtypeL.hasFDerivAt)

/-- Strict derivative form of the symmetric restricted equation, suitable for
Mathlib's implicit-function theorem. -/
theorem sourceFullFrameSymmetricEquation_hasStrictFDerivAt
    (d : ℕ) (H0 : sourceFullFrameSymmetricCoordSubmodule d) :
    HasStrictFDerivAt
      (sourceFullFrameSymmetricEquation d)
      (sourceFullFrameSymmetricEquationDerivCLM d
        (H0 : SourceFullFrameOrientedCoord d)) H0 := by
  have hcd : ContDiffAt ℂ ⊤ (sourceFullFrameSymmetricEquation d) H0 := by
    unfold sourceFullFrameSymmetricEquation
    exact (contDiff_sourceFullFrameOrientedEquation d).contDiffAt.comp H0
      (sourceFullFrameSymmetricCoordSubmodule d).subtypeL.contDiff.contDiffAt
  have hstrict := hcd.hasStrictFDerivAt (by simp)
  have hfderiv := (sourceFullFrameSymmetricEquation_hasFDerivAt d H0).fderiv
  exact hstrict.congr_fderiv hfderiv

/-- Nonzero determinant coordinate makes the derivative of the symmetric
restricted equation onto `ℂ`. -/
theorem sourceFullFrameSymmetricEquationDerivCLM_range_eq_top_of_det_ne_zero
    (d : ℕ) {H0 : SourceFullFrameOrientedCoord d}
    (hH0 : H0.2 ≠ 0) :
    LinearMap.range
        (sourceFullFrameSymmetricEquationDerivCLM d H0).toLinearMap = ⊤ := by
  apply LinearMap.range_eq_top.mpr
  intro c
  rcases sourceFullFrameOrientedEquation_fderiv_surjectiveOnSymmetric_of_det_ne_zero
      (d := d) (H0 := SourceFullFrameOrientedGramData.ofCoord H0) hH0 c with
    ⟨Y, hY⟩
  exact ⟨Y, by simpa [sourceFullFrameSymmetricEquationDerivCLM] using hY⟩

/-- The implicit-function-theorem chart for the symmetric full-frame
hypersurface at an invertible full frame.  Its first coordinate is the
oriented equation, and its second coordinate lies in the kernel of the actual
restricted derivative. -/
noncomputable def sourceFullFrameSymmetricEquation_implicitChart
    (d : ℕ)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hM0 : IsUnit M0.det) :
    OpenPartialHomeomorph
      (sourceFullFrameSymmetricCoordSubmodule d)
      (ℂ × (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d M0)).ker) := by
  let H0S := sourceFullFrameSymmetricBase d M0
  let f := sourceFullFrameSymmetricEquation d
  let f' := sourceFullFrameSymmetricEquationDerivCLM d
      (sourceFullFrameOrientedGramCoord d M0)
  have hstrict : HasStrictFDerivAt f f' H0S := by
    simpa [f, f', H0S, sourceFullFrameSymmetricBase] using
      sourceFullFrameSymmetricEquation_hasStrictFDerivAt d H0S
  have hrange : f'.range = ⊤ := by
    simpa [f'] using
      sourceFullFrameSymmetricEquationDerivCLM_range_eq_top_of_det_ne_zero
        (d := d) (H0 := sourceFullFrameOrientedGramCoord d M0) hM0.ne_zero
  have hcompleteCheck : CompleteSpace (sourceFullFrameSymmetricCoordSubmodule d) := by
    infer_instance
  exact
    @HasStrictFDerivAt.implicitToOpenPartialHomeomorph ℂ _ inferInstance
      (sourceFullFrameSymmetricCoordSubmodule d) _ _ hcompleteCheck
      ℂ _ _ inferInstance f f' H0S hstrict hrange

set_option synthInstance.maxHeartbeats 100000 in
theorem sourceFullFrameSymmetricBase_mem_implicitChart_source
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det) :
    sourceFullFrameSymmetricBase d M0 ∈
      (sourceFullFrameSymmetricEquation_implicitChart d M0 hM0).source := by
  haveI : CompleteSpace (sourceFullFrameSymmetricCoordSubmodule d) :=
    sourceFullFrameSymmetricCoordSubmodule_completeSpace d
  let H0S := sourceFullFrameSymmetricBase d M0
  let f := sourceFullFrameSymmetricEquation d
  let f' := sourceFullFrameSymmetricEquationDerivCLM d
      (sourceFullFrameOrientedGramCoord d M0)
  have hstrict : HasStrictFDerivAt f f' H0S := by
    simpa [f, f', H0S, sourceFullFrameSymmetricBase] using
      sourceFullFrameSymmetricEquation_hasStrictFDerivAt d H0S
  have hrange : f'.range = ⊤ := by
    simpa [f'] using
      sourceFullFrameSymmetricEquationDerivCLM_range_eq_top_of_det_ne_zero
        (d := d) (H0 := sourceFullFrameOrientedGramCoord d M0) hM0.ne_zero
  have hmem :=
    @HasStrictFDerivAt.mem_implicitToOpenPartialHomeomorph_source
      ℂ _ _ (sourceFullFrameSymmetricCoordSubmodule d) _ _
      (sourceFullFrameSymmetricCoordSubmodule_completeSpace d) ℂ _ _ _
      f f' H0S hstrict hrange
  simpa [sourceFullFrameSymmetricEquation_implicitChart, H0S, f, f'] using hmem

theorem sourceFullFrameSymmetricEquation_implicitChart_source_mem_nhds_base
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det) :
    (sourceFullFrameSymmetricEquation_implicitChart d M0 hM0).source ∈
      𝓝 (sourceFullFrameSymmetricBase d M0) :=
  (sourceFullFrameSymmetricEquation_implicitChart d M0 hM0).open_source.mem_nhds
    (sourceFullFrameSymmetricBase_mem_implicitChart_source d hM0)

/-- The derivative of the gauge-slice map, with codomain restricted to
symmetric full-frame coordinates. -/
noncomputable def sourceFullFrameGaugeSliceSymmetricDerivCLM
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    S.slice →L[ℂ] sourceFullFrameSymmetricCoordSubmodule d :=
  ((sourceFullFrameOrientedDifferentialCLM d M0).comp S.slice.subtypeL).codRestrict
    (sourceFullFrameSymmetricCoordSubmodule d)
    (fun X => by
      have ht : sourceFullFrameOrientedDifferential d M0
          (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) ∈
          sourceFullFrameOrientedTangentSpace d (sourceFullFrameOrientedGram d M0) := by
        rw [← sourceFullFrameOrientedDifferential_range_eq_tangent (d := d) hM0]
        exact ⟨(X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ), rfl⟩
      exact ht.1)

/-- The derivative of the gauge-slice map, with codomain restricted further to
the kernel of the symmetric restricted hypersurface equation. -/
noncomputable def sourceFullFrameGaugeSliceKernelDerivCLM
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    S.slice →L[ℂ]
      (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d M0)).ker :=
  (sourceFullFrameGaugeSliceSymmetricDerivCLM d hM0 S).codRestrict
    (sourceFullFrameSymmetricEquationDerivCLM d
      (sourceFullFrameOrientedGramCoord d M0)).ker
    (fun X => by
      rw [LinearMap.mem_ker]
      change (fderiv ℂ (sourceFullFrameOrientedEquation d)
          (sourceFullFrameOrientedGramCoord d M0))
        (sourceFullFrameOrientedDifferential d M0
          (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)) = 0
      have ht : sourceFullFrameOrientedDifferential d M0
          (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) ∈
          sourceFullFrameOrientedTangentSpace d (sourceFullFrameOrientedGram d M0) := by
        rw [← sourceFullFrameOrientedDifferential_range_eq_tangent (d := d) hM0]
        exact ⟨(X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ), rfl⟩
      exact ((mem_sourceFullFrameOrientedTangentSpace_iff_symmetric_and_fderiv_eq_zero
        (d := d) hM0).1 ht).2)

/-- The gauge-slice map with codomain restricted to symmetric full-frame
coordinates. -/
def sourceFullFrameGaugeSliceMapSymmetric
    (d : ℕ)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0) :
    S.slice → sourceFullFrameSymmetricCoordSubmodule d :=
  fun X =>
    ⟨sourceFullFrameGaugeSliceMap d M0 S X,
      (sourceFullFrameGaugeSliceMap_mem_hypersurface d M0 S X).1⟩

@[simp]
theorem sourceFullFrameGaugeSliceMapSymmetric_zero
    (d : ℕ)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (S : SourceFullFrameGaugeSliceData d M0) :
    sourceFullFrameGaugeSliceMapSymmetric d M0 S 0 =
      sourceFullFrameSymmetricBase d M0 := by
  apply Subtype.ext
  simp [sourceFullFrameGaugeSliceMapSymmetric, sourceFullFrameSymmetricBase]

/-- The symmetric-codomain gauge-slice map has the expected strict
derivative at the slice origin. -/
theorem sourceFullFrameGaugeSliceMapSymmetric_hasStrictFDerivAt
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    HasStrictFDerivAt
      (sourceFullFrameGaugeSliceMapSymmetric d M0 S)
      (sourceFullFrameGaugeSliceSymmetricDerivCLM d hM0 S) 0 := by
  let L := (sourceFullFrameOrientedDifferentialCLM d M0).comp S.slice.subtypeL
  have hderiv : ∀ X : S.slice, L X ∈ sourceFullFrameSymmetricCoordSubmodule d := by
    intro X
    have ht : sourceFullFrameOrientedDifferential d M0
        (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) ∈
        sourceFullFrameOrientedTangentSpace d (sourceFullFrameOrientedGram d M0) := by
      rw [← sourceFullFrameOrientedDifferential_range_eq_tangent (d := d) hM0]
      exact ⟨(X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ), rfl⟩
    simpa [L, sourceFullFrameOrientedDifferentialCLM,
      sourceFullFrameOrientedDifferentialLinear] using ht.1
  have h :=
    hasStrictFDerivAt_submodule_codRestrict
      (sourceFullFrameSymmetricCoordSubmodule d)
      (sourceFullFrameGaugeSliceMap_hasStrictFDerivAt (d := d) hM0 S)
      (fun X => (sourceFullFrameGaugeSliceMap_mem_hypersurface d M0 S X).1)
      hderiv
  simpa [sourceFullFrameGaugeSliceMapSymmetric,
    sourceFullFrameGaugeSliceSymmetricDerivCLM, L] using h

/-- The kernel-restricted derivative of the gauge slice is injective. -/
theorem sourceFullFrameGaugeSliceKernelDerivCLM_ker_eq_bot
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    LinearMap.ker
        (sourceFullFrameGaugeSliceKernelDerivCLM d hM0 S).toLinearMap = ⊥ := by
  ext X
  constructor
  · intro hX
    have hdiff :
        sourceFullFrameOrientedDifferential d M0
          (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) = 0 := by
      have hval := congrArg
        (fun K :
          (sourceFullFrameSymmetricEquationDerivCLM d
            (sourceFullFrameOrientedGramCoord d M0)).ker =>
          ((K : sourceFullFrameSymmetricCoordSubmodule d) :
            SourceFullFrameOrientedCoord d))
        (LinearMap.mem_ker.mp hX)
      simpa [sourceFullFrameGaugeSliceKernelDerivCLM,
        sourceFullFrameGaugeSliceSymmetricDerivCLM,
        sourceFullFrameOrientedDifferentialCLM,
        sourceFullFrameOrientedDifferentialLinear] using hval
    have hker : X ∈ LinearMap.ker
        (fderiv ℂ (sourceFullFrameGaugeSliceMap d M0 S) 0).toLinearMap := by
      rw [LinearMap.mem_ker]
      rw [sourceFullFrameGaugeSliceMap_fderiv_eq (d := d) hM0 S]
      simpa [sourceFullFrameOrientedDifferentialCLM,
        sourceFullFrameOrientedDifferentialLinear] using hdiff
    have hbot : X ∈ (⊥ : Submodule ℂ S.slice) := by
      rwa [← sourceFullFrameGaugeSliceMap_fderiv_kernel_eq_bot (d := d) hM0 S]
    exact hbot
  · intro hX
    rw [Submodule.mem_bot] at hX
    subst X
    simp

/-- The kernel-restricted derivative of the gauge slice is surjective onto
the kernel of the symmetric hypersurface equation. -/
theorem sourceFullFrameGaugeSliceKernelDerivCLM_range_eq_top
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    LinearMap.range
        (sourceFullFrameGaugeSliceKernelDerivCLM d hM0 S).toLinearMap = ⊤ := by
  apply LinearMap.range_eq_top.mpr
  intro K
  have hYsym :
      ((K : sourceFullFrameSymmetricCoordSubmodule d) :
          SourceFullFrameOrientedCoord d) ∈
        sourceFullFrameSymmetricCoordSubmodule d :=
    (K : sourceFullFrameSymmetricCoordSubmodule d).property
  have hYderiv :
      (fderiv ℂ (sourceFullFrameOrientedEquation d)
          (sourceFullFrameOrientedGramCoord d M0))
        ((K : sourceFullFrameSymmetricCoordSubmodule d) :
          SourceFullFrameOrientedCoord d) = 0 := by
    change sourceFullFrameSymmetricEquationDerivCLM d
      (sourceFullFrameOrientedGramCoord d M0)
      (K : sourceFullFrameSymmetricCoordSubmodule d) = 0
    exact K.property
  have hYtangent :
      ((K : sourceFullFrameSymmetricCoordSubmodule d) :
          SourceFullFrameOrientedCoord d) ∈
        sourceFullFrameOrientedTangentSpace d
          (sourceFullFrameOrientedGram d M0) :=
    (mem_sourceFullFrameOrientedTangentSpace_iff_symmetric_and_fderiv_eq_zero
      (d := d) hM0).2 ⟨hYsym, hYderiv⟩
  have hInRange :
      ((K : sourceFullFrameSymmetricCoordSubmodule d) :
          SourceFullFrameOrientedCoord d) ∈
        LinearMap.range
          (fderiv ℂ (sourceFullFrameGaugeSliceMap d M0 S) 0).toLinearMap := by
    rw [sourceFullFrameGaugeSliceMap_fderiv_range_eq_tangent (d := d) hM0 S]
    exact hYtangent
  rcases hInRange with ⟨X, hX⟩
  refine ⟨X, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have hX' :
      sourceFullFrameOrientedDifferential d M0
        (X : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) =
        ((K : sourceFullFrameSymmetricCoordSubmodule d) :
          SourceFullFrameOrientedCoord d) := by
    rw [sourceFullFrameGaugeSliceMap_fderiv_eq (d := d) hM0 S] at hX
    simpa [sourceFullFrameOrientedDifferentialCLM,
      sourceFullFrameOrientedDifferentialLinear] using hX
  simpa [sourceFullFrameGaugeSliceKernelDerivCLM,
    sourceFullFrameGaugeSliceSymmetricDerivCLM,
    sourceFullFrameOrientedDifferentialCLM,
    sourceFullFrameOrientedDifferentialLinear] using hX'

set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 800000 in
/-- Linear equivalence form of the gauge-slice derivative into the implicit
hypersurface kernel. -/
noncomputable def sourceFullFrameGaugeSliceKernelDerivLinearEquiv
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    S.slice ≃ₗ[ℂ]
      (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d M0)).ker := by
  let L := sourceFullFrameGaugeSliceKernelDerivCLM d hM0 S
  have hker : LinearMap.ker (L : S.slice →ₗ[ℂ]
      (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d M0)).ker) = ⊥ :=
    sourceFullFrameGaugeSliceKernelDerivCLM_ker_eq_bot d hM0 S
  have hrange : LinearMap.range (L : S.slice →ₗ[ℂ]
      (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d M0)).ker) = ⊤ :=
    sourceFullFrameGaugeSliceKernelDerivCLM_range_eq_top d hM0 S
  have hinj : Function.Injective (L : S.slice →
      (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d M0)).ker) := by
    intro X Y hXY
    have hdiff : X - Y ∈ LinearMap.ker (L : S.slice →ₗ[ℂ]
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d M0)).ker) := by
      rw [LinearMap.mem_ker]
      simpa [map_sub] using sub_eq_zero.mpr hXY
    have hbot : X - Y ∈ (⊥ : Submodule ℂ S.slice) := by
      simpa [hker] using hdiff
    have hzero : X - Y = 0 := by
      simpa using hbot
    exact sub_eq_zero.mp hzero
  have hsurj : Function.Surjective (L : S.slice →
      (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d M0)).ker) := by
    intro K
    have hK : K ∈ LinearMap.range (L : S.slice →ₗ[ℂ]
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d M0)).ker) := by
      rw [hrange]
      trivial
    rcases hK with ⟨X, hX⟩
    exact ⟨X, hX⟩
  exact
    LinearEquiv.ofBijective (L : S.slice →ₗ[ℂ]
      (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d M0)).ker)
      ⟨hinj, hsurj⟩

set_option synthInstance.maxHeartbeats 100000 in
/-- The kernel projection used by Mathlib's finite-dimensional implicit
chart for the symmetric full-frame equation. -/
noncomputable def sourceFullFrameSymmetricEquationKernelProjection
    (d : ℕ)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    sourceFullFrameSymmetricCoordSubmodule d →L[ℂ]
      (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d M0)).ker :=
  Classical.choose
    ((sourceFullFrameSymmetricEquationDerivCLM d
      (sourceFullFrameOrientedGramCoord d M0)).ker_closedComplemented_of_finiteDimensional_range)

set_option synthInstance.maxHeartbeats 100000 in
@[simp]
theorem sourceFullFrameSymmetricEquationKernelProjection_apply_ker
    (d : ℕ)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (K : (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d M0)).ker) :
    sourceFullFrameSymmetricEquationKernelProjection d M0 K = K := by
  exact Classical.choose_spec
    ((sourceFullFrameSymmetricEquationDerivCLM d
      (sourceFullFrameOrientedGramCoord d M0)).ker_closedComplemented_of_finiteDimensional_range) K

set_option synthInstance.maxHeartbeats 100000 in
/-- The first coordinate of the symmetric implicit chart is the nonlinear
full-frame hypersurface equation. -/
theorem sourceFullFrameSymmetricEquation_implicitChart_fst
    (d : ℕ)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hM0 : IsUnit M0.det)
    (H : sourceFullFrameSymmetricCoordSubmodule d) :
    ((sourceFullFrameSymmetricEquation_implicitChart d M0 hM0) H).1 =
      sourceFullFrameSymmetricEquation d H := by
  rfl

set_option synthInstance.maxHeartbeats 100000 in
/-- The second coordinate of the symmetric implicit chart is the kernel
projection of the displacement from the base point. -/
theorem sourceFullFrameSymmetricEquation_implicitChart_snd
    (d : ℕ)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hM0 : IsUnit M0.det)
    (H : sourceFullFrameSymmetricCoordSubmodule d) :
    ((sourceFullFrameSymmetricEquation_implicitChart d M0 hM0) H).2 =
      sourceFullFrameSymmetricEquationKernelProjection d M0
        (H - sourceFullFrameSymmetricBase d M0) := by
  haveI : CompleteSpace (sourceFullFrameSymmetricCoordSubmodule d) :=
    sourceFullFrameSymmetricCoordSubmodule_completeSpace d
  let H0S := sourceFullFrameSymmetricBase d M0
  let f := sourceFullFrameSymmetricEquation d
  let f' := sourceFullFrameSymmetricEquationDerivCLM d
      (sourceFullFrameOrientedGramCoord d M0)
  have hstrict : HasStrictFDerivAt f f' H0S := by
    simpa [f, f', H0S, sourceFullFrameSymmetricBase] using
      sourceFullFrameSymmetricEquation_hasStrictFDerivAt d H0S
  have hrange : f'.range = ⊤ := by
    simpa [f'] using
      sourceFullFrameSymmetricEquationDerivCLM_range_eq_top_of_det_ne_zero
        (d := d) (H0 := sourceFullFrameOrientedGramCoord d M0) hM0.ne_zero
  have happ :=
    @HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented_apply ℂ
      _ (sourceFullFrameSymmetricCoordSubmodule d) _ _
      (sourceFullFrameSymmetricCoordSubmodule_completeSpace d)
      ℂ _ _ inferInstance f f' H0S hstrict hrange
      (f'.ker_closedComplemented_of_finiteDimensional_range) H
  have hsnd := congrArg Prod.snd happ
  simpa [sourceFullFrameSymmetricEquation_implicitChart,
    HasStrictFDerivAt.implicitToOpenPartialHomeomorph,
    sourceFullFrameSymmetricEquationKernelProjection, H0S, f, f'] using hsnd

theorem sourceFullFrameSymmetricEquation_implicitChart_eq_zero_kernelProjection
    (d : ℕ)
    (M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hM0 : IsUnit M0.det)
    (H : sourceFullFrameSymmetricCoordSubmodule d)
    (hH : sourceFullFrameSymmetricEquation d H = 0) :
    (sourceFullFrameSymmetricEquation_implicitChart d M0 hM0) H =
      (0,
        sourceFullFrameSymmetricEquationKernelProjection d M0
          (H - sourceFullFrameSymmetricBase d M0)) := by
  exact
    Prod.ext
      (by rw [sourceFullFrameSymmetricEquation_implicitChart_fst, hH])
      (by rw [sourceFullFrameSymmetricEquation_implicitChart_snd])

/-- The nonlinear kernel-coordinate map obtained by putting the gauge-slice
map through the symmetric implicit chart. -/
noncomputable def sourceFullFrameGaugeSliceImplicitKernelMap
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    S.slice →
      (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d M0)).ker :=
  fun X =>
    ((sourceFullFrameSymmetricEquation_implicitChart d M0 hM0)
      (sourceFullFrameGaugeSliceMapSymmetric d M0 S X)).2

@[simp]
theorem sourceFullFrameGaugeSliceImplicitKernelMap_zero
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S 0 = 0 := by
  haveI : CompleteSpace (sourceFullFrameSymmetricCoordSubmodule d) :=
    sourceFullFrameSymmetricCoordSubmodule_completeSpace d
  let H0S := sourceFullFrameSymmetricBase d M0
  let f := sourceFullFrameSymmetricEquation d
  let f' := sourceFullFrameSymmetricEquationDerivCLM d
      (sourceFullFrameOrientedGramCoord d M0)
  have hstrict : HasStrictFDerivAt f f' H0S := by
    simpa [f, f', H0S, sourceFullFrameSymmetricBase] using
      sourceFullFrameSymmetricEquation_hasStrictFDerivAt d H0S
  have hrange : f'.range = ⊤ := by
    simpa [f'] using
      sourceFullFrameSymmetricEquationDerivCLM_range_eq_top_of_det_ne_zero
        (d := d) (H0 := sourceFullFrameOrientedGramCoord d M0) hM0.ne_zero
  have hself :
      (sourceFullFrameSymmetricEquation_implicitChart d M0 hM0) H0S =
        (f H0S, (0 : f'.ker)) := by
    exact
      @HasStrictFDerivAt.implicitToOpenPartialHomeomorph_self ℂ
        _ _ (sourceFullFrameSymmetricCoordSubmodule d) _ _
        (sourceFullFrameSymmetricCoordSubmodule_completeSpace d)
        ℂ _ _ _ f f' H0S hstrict hrange
  have hmap0 :
      sourceFullFrameGaugeSliceMapSymmetric d M0 S 0 = H0S := by
    simp [H0S]
  unfold sourceFullFrameGaugeSliceImplicitKernelMap
  rw [hmap0, hself]

set_option synthInstance.maxHeartbeats 100000 in
/-- Strict derivative of the nonlinear implicit-kernel coordinate map. -/
theorem sourceFullFrameGaugeSliceImplicitKernelMap_hasStrictFDerivAt
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    HasStrictFDerivAt
      (sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S)
      (sourceFullFrameGaugeSliceKernelDerivCLM d hM0 S) 0 := by
  let P := sourceFullFrameSymmetricEquationKernelProjection d M0
  let H0S := sourceFullFrameSymmetricBase d M0
  let Fsym := sourceFullFrameGaugeSliceMapSymmetric d M0 S
  have hF : HasStrictFDerivAt Fsym
      (sourceFullFrameGaugeSliceSymmetricDerivCLM d hM0 S) 0 := by
    simpa [Fsym] using
      sourceFullFrameGaugeSliceMapSymmetric_hasStrictFDerivAt d hM0 S
  have hsub : HasStrictFDerivAt (fun X : S.slice => Fsym X - H0S)
      (sourceFullFrameGaugeSliceSymmetricDerivCLM d hM0 S) 0 := by
    exact hF.sub_const H0S
  let P' : sourceFullFrameSymmetricCoordSubmodule d →L[ℂ]
      (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d M0)).ker :=
    sourceFullFrameSymmetricEquationKernelProjection d M0
  have hP : HasStrictFDerivAt
      (P' : sourceFullFrameSymmetricCoordSubmodule d →
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d M0)).ker)
      P' (Fsym 0 - H0S) :=
    @ContinuousLinearMap.hasStrictFDerivAt ℂ _
      (sourceFullFrameSymmetricCoordSubmodule d) _ _ _
      ((sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d M0)).ker) _ _ _
      P' (Fsym 0 - H0S)
  have hcomp : HasStrictFDerivAt
      (fun X : S.slice =>
        sourceFullFrameSymmetricEquationKernelProjection d M0 (Fsym X - H0S))
      ((sourceFullFrameSymmetricEquationKernelProjection d M0).comp
        (sourceFullFrameGaugeSliceSymmetricDerivCLM d hM0 S)) 0 :=
    by
      simpa [P'] using
        (HasStrictFDerivAt.comp (𝕜 := ℂ) (x := (0 : S.slice))
          (g := (sourceFullFrameSymmetricEquationKernelProjection d M0 :
            sourceFullFrameSymmetricCoordSubmodule d →
              (sourceFullFrameSymmetricEquationDerivCLM d
                (sourceFullFrameOrientedGramCoord d M0)).ker))
          (f := fun X : S.slice => Fsym X - H0S)
          hP hsub)
  have hclm : (sourceFullFrameSymmetricEquationKernelProjection d M0).comp
      (sourceFullFrameGaugeSliceSymmetricDerivCLM d hM0 S) =
      sourceFullFrameGaugeSliceKernelDerivCLM d hM0 S := by
    apply ContinuousLinearMap.ext
    intro X
    have hp := sourceFullFrameSymmetricEquationKernelProjection_apply_ker d M0
      (sourceFullFrameGaugeSliceKernelDerivCLM d hM0 S X)
    simpa [sourceFullFrameGaugeSliceKernelDerivCLM] using hp
  have hcomp' : HasStrictFDerivAt
      (fun X : S.slice =>
        sourceFullFrameSymmetricEquationKernelProjection d M0 (Fsym X - H0S))
      (sourceFullFrameGaugeSliceKernelDerivCLM d hM0 S) 0 :=
    hcomp.congr_fderiv hclm
  refine hcomp'.congr_of_eventuallyEq ?_
  filter_upwards with X
  simp [sourceFullFrameGaugeSliceImplicitKernelMap, Fsym, H0S,
    sourceFullFrameSymmetricEquation_implicitChart_snd]

set_option synthInstance.maxHeartbeats 120000 in
/-- Continuous-linear equivalence form of the implicit-kernel derivative. -/
noncomputable def sourceFullFrameGaugeSliceKernelDerivContinuousLinearEquiv
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    S.slice ≃L[ℂ]
      (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d M0)).ker :=
  { sourceFullFrameGaugeSliceKernelDerivLinearEquiv d hM0 S with
    continuous_toFun := (sourceFullFrameGaugeSliceKernelDerivCLM d hM0 S).continuous
    continuous_invFun := by
      let K := (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d M0)).ker
      let e0 := sourceFullFrameGaugeSliceKernelDerivLinearEquiv d hM0 S
      let invL : @LinearMap ℂ ℂ _ _ (RingHom.id ℂ) K S.slice
          (AddCommGroup.toAddCommMonoid) (AddCommGroup.toAddCommMonoid)
          inferInstance inferInstance :=
        { toFun := fun K => e0.symm K
          map_add' := by
            intro K₁ K₂
            exact e0.symm.map_add K₁ K₂
          map_smul' := by
            intro c K
            exact e0.symm.map_smul c K }
      exact invL.continuous_of_finiteDimensional }

set_option synthInstance.maxHeartbeats 120000 in
@[simp]
theorem sourceFullFrameGaugeSliceKernelDerivContinuousLinearEquiv_coe
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    (sourceFullFrameGaugeSliceKernelDerivContinuousLinearEquiv d hM0 S :
      S.slice →L[ℂ]
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d M0)).ker) =
      sourceFullFrameGaugeSliceKernelDerivCLM d hM0 S := by
  ext X <;> simp [sourceFullFrameGaugeSliceKernelDerivContinuousLinearEquiv,
    sourceFullFrameGaugeSliceKernelDerivLinearEquiv]

set_option synthInstance.maxHeartbeats 120000 in
/-- Local inverse-function chart for the implicit kernel-coordinate map. -/
noncomputable def sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    OpenPartialHomeomorph S.slice
      (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d M0)).ker := by
  haveI : CompleteSpace S.slice :=
    sourceFullFrameGaugeSliceData_slice_completeSpace d S
  let K := (sourceFullFrameSymmetricEquationDerivCLM d
    (sourceFullFrameOrientedGramCoord d M0)).ker
  let f := sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S
  let e := sourceFullFrameGaugeSliceKernelDerivContinuousLinearEquiv d hM0 S
  have hderiv : HasStrictFDerivAt f (e : S.slice →L[ℂ] K) 0 := by
    rw [sourceFullFrameGaugeSliceKernelDerivContinuousLinearEquiv_coe]
    exact sourceFullFrameGaugeSliceImplicitKernelMap_hasStrictFDerivAt d hM0 S
  exact
    @HasStrictFDerivAt.toOpenPartialHomeomorph ℂ _ S.slice _ _ K _ _
      f e 0 (sourceFullFrameGaugeSliceData_slice_completeSpace d S) hderiv

set_option synthInstance.maxHeartbeats 120000 in
@[simp]
theorem sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph_coe
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S :
      S.slice →
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d M0)).ker) =
      sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S := by
  rfl

set_option synthInstance.maxHeartbeats 120000 in
theorem sourceFullFrameGaugeSliceImplicitKernel_zero_mem_chartSource
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    (0 : S.slice) ∈
      (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).source := by
  haveI : CompleteSpace S.slice :=
    sourceFullFrameGaugeSliceData_slice_completeSpace d S
  let f := sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S
  let e := sourceFullFrameGaugeSliceKernelDerivContinuousLinearEquiv d hM0 S
  have hderiv : HasStrictFDerivAt f
      (e : S.slice →L[ℂ]
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d M0)).ker) 0 := by
    rw [sourceFullFrameGaugeSliceKernelDerivContinuousLinearEquiv_coe]
    exact sourceFullFrameGaugeSliceImplicitKernelMap_hasStrictFDerivAt d hM0 S
  unfold sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph
  simp only [HasStrictFDerivAt.toOpenPartialHomeomorph,
    ApproximatesLinearOn.toOpenPartialHomeomorph_source]
  exact (Classical.choose_spec hderiv.approximates_deriv_on_open_nhds).1

set_option synthInstance.maxHeartbeats 120000 in
theorem sourceFullFrameGaugeSliceImplicitKernel_zero_mem_chartTarget
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    (0 :
      (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d M0)).ker) ∈
      (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).target := by
  have hsource :=
    sourceFullFrameGaugeSliceImplicitKernel_zero_mem_chartSource d hM0 S
  have htarget :=
    (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).map_source
      hsource
  simpa [sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph_coe] using htarget

set_option synthInstance.maxHeartbeats 120000 in
theorem sourceFullFrameGaugeSliceImplicitKernel_chartSource_mem_nhds_zero
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).source ∈
      𝓝 (0 : S.slice) :=
  (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).open_source.mem_nhds
    (sourceFullFrameGaugeSliceImplicitKernel_zero_mem_chartSource d hM0 S)

set_option synthInstance.maxHeartbeats 120000 in
theorem sourceFullFrameGaugeSliceImplicitKernel_chartTarget_mem_nhds_zero
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).target ∈
      𝓝 (0 :
        (sourceFullFrameSymmetricEquationDerivCLM d
          (sourceFullFrameOrientedGramCoord d M0)).ker) :=
  (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).open_target.mem_nhds
    (sourceFullFrameGaugeSliceImplicitKernel_zero_mem_chartTarget d hM0 S)

set_option synthInstance.maxHeartbeats 120000 in
theorem sourceFullFrameGaugeSliceImplicitKernelMap_surjOn_chartTarget
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0) :
    Set.SurjOn
      (sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S)
      (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).source
      (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).target := by
  simpa [sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph_coe] using
    (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).surjOn

set_option synthInstance.maxHeartbeats 120000 in
theorem sourceFullFrameGaugeSliceImplicitKernelMap_right_inv_on_chartTarget
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0)
    {K : (sourceFullFrameSymmetricEquationDerivCLM d
        (sourceFullFrameOrientedGramCoord d M0)).ker}
    (hK :
      K ∈
        (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).target) :
    sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S
      ((sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).symm K) = K := by
  simpa [sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph_coe] using
    (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).right_inv hK

set_option synthInstance.maxHeartbeats 120000 in
theorem sourceFullFrameGaugeSliceImplicitKernelMap_left_inv_on_chartSource
    (d : ℕ)
    {M0 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hM0 : IsUnit M0.det)
    (S : SourceFullFrameGaugeSliceData d M0)
    {X : S.slice}
    (hX :
      X ∈
        (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).source) :
    (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).symm
      (sourceFullFrameGaugeSliceImplicitKernelMap d hM0 S X) = X := by
  simpa [sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph_coe] using
    (sourceFullFrameGaugeSliceImplicitKernelOpenPartialHomeomorph d hM0 S).left_inv hX

end BHW
