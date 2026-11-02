/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.MetricSpace.Algebra

@[expose] public section

/-!
# Mathlib 4.29 compatibility (retired)

This module used to re-declare `NormSMulClass ℝ ℂ`, `IsBoundedSMul ℝ ℂ` and three
`SMulCommClass` instances via `inferInstance`, as a workaround for Mathlib 4.29's
`backward.isDefEq.respectTransparency`. Those instances are redundant with Mathlib and,
under the module system, shadow Mathlib's inside proof terms, which makes the registry
Challenge (Mathlib only) and Solution (Mathlib plus this package) elaborate the same
definitions to different terms. The module is kept, empty, so importers need no change.
-/
