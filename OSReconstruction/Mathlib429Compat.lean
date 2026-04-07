/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Algebra

/-!
# Mathlib v4.29 Compatibility Patches

Lean 4.29 defaults to `backward.isDefEq.respectTransparency = true`, which breaks
typeclass synthesis for `NormSMulClass ℝ ℂ`, `ContinuousSMul ℝ ℂ`, etc.
The `NormedSpace ℝ ℂ` instance (via `InnerProductSpace ℝ ℂ`) carries a `SMul`
that doesn't unify at the stricter transparency level.

Fix: provide global instances with `set_option backward.isDefEq.respectTransparency false`.
See: leanprover-community/mathlib4#37600
-/

set_option backward.isDefEq.respectTransparency false in
noncomputable instance : NormSMulClass ℝ ℂ := inferInstance

set_option backward.isDefEq.respectTransparency false in
noncomputable instance : IsBoundedSMul ℝ ℂ := inferInstance

set_option backward.isDefEq.respectTransparency false in
noncomputable instance : IsScalarTower ℝ ℂ ℂ := inferInstance

set_option backward.isDefEq.respectTransparency false in
noncomputable instance : SMulCommClass ℂ ℝ ℂ := inferInstance

set_option backward.isDefEq.respectTransparency false in
noncomputable instance : SMulCommClass ℝ ℂ ℂ := inferInstance

set_option backward.isDefEq.respectTransparency false in
noncomputable instance : SMulCommClass ℝ ℝ ℂ := inferInstance
