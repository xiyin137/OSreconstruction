/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.AnalyticContinuation
import OSReconstruction.ComplexLieGroups.BHWCore

/-!
# W11 Counterexample: `wickRotation_not_in_PET_null` is false for n ≥ d+2

## What this file formalizes

This file contains the **algebraic core** of the obstruction: the specific
points `x₁=(1,0)`, `x₂=(-1,0)` in `d=1` (and analogous n=3 triangle), the key
identities `z₂ = -z₁` and `(½)x₁ + (½)x₂ = 0`, and the no-valid-ordering
contradiction `¬(a > 0 ∧ -2a > 0)` for any real `a`.

The full non-membership theorem
`(fun k => wickRotatePoint (w11_counterexample_config k)) ∉ PermutedExtendedTube 1 2`
is argued informally in the module docstring below but is **not yet itself a
Lean theorem in this file** — closing the loop requires unfolding the
`PermutedExtendedTube` `iUnion` over (π, Λ) and combining the algebraic facts
below with the `InOpenForwardCone` definitional conditions. The algebraic
obstruction is fully Lean-formalized; the final unfolding is currently prose.

## The issue

The `ForwardTube` definition (WightmanAxioms.lean) requires for k=0 that
`Im(z₀) ∈ V⁺` (the absolute imaginary part, not a difference). This "basepoint
condition" is stronger than the standard physics definition, which uses only
difference variables ξ_k = z_{k+1} - z_k.

The PET inherits this condition: `PermutedExtendedTube d n` is defined via
`PermutedForwardTube`, which is defined via `ForwardTube`, which has the
basepoint condition for every permutation.

## The counterexample (d=1, n=2)

Points x₁ = (1, 0), x₂ = (-1, 0) are pairwise distinct.
Wick rotation: z₁ = (i, 0), z₂ = (-i, 0). Note z₂ = -z₁.

For ANY complex Lorentz Λ ∈ SO(1,1;ℂ) and EITHER permutation π:

Case π = id:
  w₀ = Λ⁻¹ · z₁ must have Im(w₀) ∈ V⁺ → Im(Λ⁻¹ · z₁)₀ > 0
  w₁ - w₀ = Λ⁻¹ · (z₂ - z₁) = Λ⁻¹ · (-2z₁) must have Im in V⁺
  → Im(Λ⁻¹ · z₁)₀ < 0.   CONTRADICTION.

Case π = swap:
  w₀ = Λ⁻¹ · z₂ = -Λ⁻¹ · z₁ must have Im(w₀) ∈ V⁺ → Im(Λ⁻¹ · z₁)₀ < 0
  w₁ - w₀ = Λ⁻¹ · (z₁ - z₂) = 2Λ⁻¹ · z₁ must have Im in V⁺
  → Im(Λ⁻¹ · z₁)₀ > 0.   CONTRADICTION.

So (z₁, z₂) ∉ PermutedExtendedTube 1 2, even though x₁ ≠ x₂.

## Measure of the bad set

For d=1, n=2: the failure set includes all (x₁, x₂) with x₁ = -c·x₂ for
c > 0, which is codimension 1 in ℝ⁴ — hence measure zero.

For d=1, n=3: the failure set includes all (x₁, x₂, x₃) with 0 in the
convex hull of {x₁, x₂, x₃}. In ℝ², the convex hull of 3 generic points
is a triangle, and the origin being inside is an OPEN condition — hence
POSITIVE MEASURE.

More generally, for n ≥ d+2, the convex hull of n generic points in ℝ^{d+1}
has nonempty interior, and {x : 0 ∈ conv{x₀,...,x_{n-1}}} has positive measure.

## Why the counterexample works

For any complex Lorentz Λ, the imaginary part of Λ·z_k (where z_k = wickRotatePoint(x_k))
is a linear function of x_k:

  Im(Λ · z_k)_μ = Re(Λ_{μ0}) · τ_k + Σ_{j≥1} Im(Λ_{μj}) · x_{k,j}

For the k=0 basepoint condition, we need this vector to be in V⁺ for x_{π(0)}.
In particular, the time component must be positive:
  u · x_{π(0)} > 0  where u = (Re(Λ_{00}), Im(Λ_{01}), ..., Im(Λ_{0d})).

By varying Λ over SO(1,d;ℂ), the direction u can be any point on S^d.
So the basepoint condition requires: ∃ u ∈ S^d, ∀ k, u · x_k > 0.
This is: all x_k lie in some common open half-space of ℝ^{d+1}.
Equivalently: 0 ∉ conv{x₀, ..., x_{n-1}}.

## Fix

The standard physics ForwardTube uses n-1 difference conditions only (no basepoint).
With the standard definition, wickRotation_not_in_PET_null IS true:
non-coincident Euclidean configs always land in the standard PET.

Options:
(a) Remove the k=0 basepoint condition from ForwardTube.
(b) Reformulate the theorem for the standard PET and prove a bridge lemma.
(c) Add hypothesis n ≤ d+1 (insufficient for general use).
-/

noncomputable section

open Complex BHWCore BHW

/-- The two counterexample points in d=1: x₁ = (1, 0), x₂ = (-1, 0). -/
def w11_counterexample_config : Fin 2 → Fin 2 → ℝ :=
  fun k => if k = 0 then ![1, 0] else ![-1, 0]

/-- The points are distinct. -/
theorem w11_counterexample_distinct :
    w11_counterexample_config 0 ≠ w11_counterexample_config 1 := by
  intro hEq
  have : (w11_counterexample_config 0) 0 = (w11_counterexample_config 1) 0 := congrFun hEq 0
  simp [w11_counterexample_config, Matrix.cons_val_zero] at this
  norm_num at this

/-- z₁ 0 = -(z₀ 0): the Wick-rotated time components are opposite.
    Since Λ is linear, Λ·z₂ = -Λ·z₁, making the k=0 and k=1 forward tube
    conditions contradictory. -/
theorem w11_counterexample_wick_time :
    @wickRotatePoint 1 (w11_counterexample_config 1) 0 =
    -(@wickRotatePoint 1 (w11_counterexample_config 0) 0) := by
  simp [wickRotatePoint, w11_counterexample_config, Matrix.cons_val_zero]

/-- z₁ 1 = -(z₀ 1) = 0: the spatial components are both zero. -/
theorem w11_counterexample_wick_spatial :
    @wickRotatePoint 1 (w11_counterexample_config 1) 1 =
    -(@wickRotatePoint 1 (w11_counterexample_config 0) 1) := by
  simp [wickRotatePoint, w11_counterexample_config,
        show (1 : Fin 2) ≠ 0 from by decide,
        Matrix.cons_val_one, Matrix.head_cons]

/-- The key algebraic fact: for any a : ℝ (representing Im(Λ·z₁)₀),
    we cannot simultaneously have a > 0 and -2a > 0 (π = id case),
    nor -a > 0 and 2a > 0 (π = swap case).
    This blocks both permutations for the forward tube condition. -/
theorem w11_no_valid_ordering (a : ℝ) :
    ¬(a > 0 ∧ -2 * a > 0) ∧ ¬(-a > 0 ∧ 2 * a > 0) := by
  constructor <;> intro ⟨h1, h2⟩ <;> nlinarith

/-!
## The general obstruction

The following theorem shows that 0 ∈ conv{x₁, x₂} for our counterexample,
which is the general criterion for the basepoint obstruction.
-/

/-- The origin is in the convex hull of x₁=(1,0) and x₂=(-1,0):
    (1/2)·(1,0) + (1/2)·(-1,0) = (0,0). -/
theorem w11_origin_in_convex_hull :
    let x₁ : Fin 2 → ℝ := ![1, 0]
    let x₂ : Fin 2 → ℝ := ![-1, 0]
    (1/2 : ℝ) • x₁ + (1/2 : ℝ) • x₂ = 0 := by
  ext i
  fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  <;> ring

/-!
## d=1, n=3 positive-measure counterexample

x₁ = (1, 2), x₂ = (-2, 1), x₃ = (1, -2).
Barycentric coords: λ₁ = 1/4, λ₂ = 1/3, λ₃ = 5/12, all positive, sum to 1.
-/

/-- The origin is in the convex hull of 3 points in ℝ²:
    (1/4)·x₁ + (1/3)·x₂ + (5/12)·x₃ = 0. -/
theorem w11_origin_in_triangle :
    let x₁ : Fin 2 → ℝ := ![1, 2]
    let x₂ : Fin 2 → ℝ := ![-2, 1]
    let x₃ : Fin 2 → ℝ := ![1, -2]
    (1/4 : ℝ) • x₁ + (1/3 : ℝ) • x₂ + (5/12 : ℝ) • x₃ = 0 := by
  ext i
  fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  <;> ring

/-- The barycentric coordinates are all positive and sum to 1. -/
theorem w11_barycentric_valid :
    (1/4 : ℝ) > 0 ∧ (1/3 : ℝ) > 0 ∧ (5/12 : ℝ) > 0 ∧
    (1/4 : ℝ) + 1/3 + 5/12 = 1 := by
  norm_num

end
