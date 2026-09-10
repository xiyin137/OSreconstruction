/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.Algebra.Module.Basic
import Init
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
























noncomputable section

open scoped InnerProduct ComplexConjugate

-- Disable unused section variable warnings; CompleteSpace is needed for most theorems
-- but not all, and restructuring would be more complex than beneficial
set_option linter.unusedSectionVars false

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]



/-- An unbounded linear operator on a Hilbert space H.
    It consists of a dense subspace (domain) and a linear map on that subspace. -/
structure UnboundedOperator (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The domain of the operator -/
  domain : Submodule ℂ H
  /-- The operator is a linear map on its domain -/
  toFun : domain → H
  /-- The operator is linear -/
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  /-- The operator respects scalar multiplication -/
  map_smul' : ∀ (c : ℂ) x, toFun (c • x) = c • toFun x

namespace UnboundedOperator

variable (T : UnboundedOperator H)

instance : CoeFun (UnboundedOperator H) (fun T => T.domain → H) := ⟨UnboundedOperator.toFun⟩



end UnboundedOperator



namespace UnboundedOperator

variable (T : UnboundedOperator H)

end UnboundedOperator



namespace UnboundedOperator

variable (T : UnboundedOperator H)

end UnboundedOperator
