/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Init
import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.Core
import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.OrbitSetN1Geometry
import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.OrbitSetN1Preconnected
import OSReconstruction.ComplexLieGroups.Connectedness.ComplexInvariance.Extend
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.Adjacency
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.IndexSetD1
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceExtension
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOriented
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.LinearAlgebra.Reflection
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import OSReconstruction.SCV.IdentityTheorem
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.SourceOrientedContinuation
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.MvPolynomial.Basic
import OSReconstruction.ComplexLieGroups.SOConnected
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.Sort
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Topology.LocallyConstant.Basic
import OSReconstruction.SCV.TotallyRealIdentity
import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.PermutationFlow
import OSReconstruction.SCV.TubeDomainExtension
import OSReconstruction.Wightman.Spacetime.Metric
import OSReconstruction.Wightman.Groups.Lorentz



































noncomputable section

set_option linter.unusedSectionVars false

open Complex Topology Matrix

variable {d : ℕ} [NeZero d]



/-- The metric signature in `LorentzLieGroup` equals the one in `MinkowskiSpace`.
    Both are `fun i => if i = 0 then -1 else 1`. -/
theorem minkowskiSignature_eq_metricSignature :
    LorentzLieGroup.minkowskiSignature d = MinkowskiSpace.metricSignature d := rfl

/-- The Minkowski matrix in `LorentzLieGroup` equals the one in `MinkowskiSpace`. -/
theorem lorentzLieGroup_minkowskiMatrix_eq :
    LorentzLieGroup.minkowskiMatrix d = minkowskiMatrix d :=
  congr_arg Matrix.diagonal minkowskiSignature_eq_metricSignature



/-- The two `IsLorentzMatrix` predicates are equivalent. -/
theorem isLorentzMatrix_iff (Λ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    LorentzLieGroup.IsLorentzMatrix d Λ ↔ IsLorentzMatrix d Λ := by
  unfold LorentzLieGroup.IsLorentzMatrix IsLorentzMatrix
  rw [lorentzLieGroup_minkowskiMatrix_eq]



/-- Equivalence between the ambient full Lorentz groups from `LorentzLieGroup`
    and `Wightman/Groups/Lorentz`.
    The underlying matrices are identical. -/
def lorentzGroupEquiv : LorentzLieGroup.FullLorentzGroup d ≃ FullLorentzGroup d where
  toFun Λ := ⟨Λ.val, (isLorentzMatrix_iff Λ.val).mp Λ.prop⟩
  invFun Λ := ⟨Λ.val, (isLorentzMatrix_iff Λ.val).mpr Λ.prop⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The equivalence preserves the underlying matrix. -/
@[simp]
 theorem lorentzGroupEquiv_val (Λ : LorentzLieGroup.FullLorentzGroup d) :
    (lorentzGroupEquiv Λ).val = Λ.val := rfl

/-- The inverse equivalence preserves the underlying matrix. -/
@[simp]
theorem lorentzGroupEquiv_symm_val (Λ : FullLorentzGroup d) :
    (lorentzGroupEquiv.symm Λ).val = Λ.val := rfl



/-- `IsProperLorentz` from `LorentzLieGroup` corresponds to `IsProper` from Wightman. -/
theorem isProperLorentz_iff_isProper (Λ : LorentzLieGroup.FullLorentzGroup d) :
    LorentzLieGroup.IsProperLorentz d Λ ↔
    FullLorentzGroup.IsProper (lorentzGroupEquiv Λ) := by
  simp [LorentzLieGroup.IsProperLorentz, FullLorentzGroup.IsProper]

/-- `IsOrthochronous` from LorentzLieGroup corresponds to `IsOrthochronous` from Wightman. -/
theorem isOrthochronous_iff (Λ : LorentzLieGroup.FullLorentzGroup d) :
    LorentzLieGroup.IsOrthochronous d Λ ↔
    FullLorentzGroup.IsOrthochronous (lorentzGroupEquiv Λ) := by
  simp [LorentzLieGroup.IsOrthochronous, FullLorentzGroup.IsOrthochronous]



/-- Convert from the default connected `LorentzGroup` on the `LorentzLieGroup`
    side to the default connected `LorentzGroup` in the Wightman layer. -/
def lorentzGroupToWightman
    (Λ : LorentzLieGroup.LorentzGroup d) :
    LorentzGroup d :=
  ⟨Λ.val.val,
    (isLorentzMatrix_iff Λ.val.val).mp Λ.val.prop,
    (isProperLorentz_iff_isProper Λ.val).mp Λ.prop.1,
    (isOrthochronous_iff Λ.val).mp Λ.prop.2⟩

/-- Convert from the new default connected `LorentzGroup` (Wightman) to
    the default connected `LorentzGroup` on the `LorentzLieGroup` side. -/
def wightmanToLorentzGroup
    (Λ : LorentzGroup d) :
    LorentzLieGroup.LorentzGroup d :=
  ⟨lorentzGroupEquiv.symm Λ.toFull,
    (isProperLorentz_iff_isProper _).mpr (by
      rw [Equiv.apply_symm_apply]
      exact LorentzGroup.det_eq_one Λ),
    (isOrthochronous_iff _).mpr (by
      rw [Equiv.apply_symm_apply]
      exact LorentzGroup.zero_zero_ge_one Λ)⟩

/-- The underlying matrix is preserved by the conversion. -/
@[simp]
theorem lorentzGroupToWightman_val_val
    (Λ : LorentzLieGroup.LorentzGroup d) :
    (lorentzGroupToWightman Λ).val = Λ.val.val := rfl



/-- The `InOpenForwardCone` from `BHW` (using `minkowskiSignature` and `x^2`)
    is equivalent to the Wightman version (using `metricSignature` and `x * x`). -/
theorem inOpenForwardCone_iff (η : Fin (d + 1) → ℝ) :
    BHW.InOpenForwardCone d η ↔
    (η 0 > 0 ∧ MinkowskiSpace.minkowskiNormSq d η < 0) := by
  unfold BHW.InOpenForwardCone MinkowskiSpace.minkowskiNormSq MinkowskiSpace.minkowskiInner
  constructor <;> intro ⟨h1, h2⟩ <;> exact ⟨h1, by
    convert h2 using 1; apply Finset.sum_congr rfl; intro i _
    rw [minkowskiSignature_eq_metricSignature]; ring⟩




















































end
