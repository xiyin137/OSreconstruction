/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Algebra













set_option backward.isDefEq.respectTransparency false in
noncomputable instance : NormSMulClass ℝ ℂ := inferInstance

set_option backward.isDefEq.respectTransparency false in
noncomputable instance : IsBoundedSMul ℝ ℂ := inferInstance

set_option backward.isDefEq.respectTransparency false in
noncomputable instance : SMulCommClass ℂ ℝ ℂ := inferInstance

set_option backward.isDefEq.respectTransparency false in
noncomputable instance : SMulCommClass ℝ ℂ ℂ := inferInstance

set_option backward.isDefEq.respectTransparency false in
noncomputable instance : SMulCommClass ℝ ℝ ℂ := inferInstance
