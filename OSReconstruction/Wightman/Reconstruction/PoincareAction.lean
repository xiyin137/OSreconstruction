/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import OSReconstruction.Wightman.WightmanAxioms

/-!
# Poincaré Action on Schwartz Test Functions

This file defines the action of the Poincaré group on Schwartz test functions:
  (g · f)(x) = f(g⁻¹ · x)

The Schwartz class is preserved because:
- Poincaré transformations are affine maps (linear + translation)
- Composition with an invertible affine map preserves smoothness
- Composition with an invertible affine map preserves polynomial decay
  (since ‖g⁻¹ · x‖ ∼ ‖x‖ for invertible linear maps)

## Main definitions
- `poincareActSchwartz`: The Poincaré action on Schwartz functions
- `poincareActSchwartz_spec`: (g · f)(x) = f(g⁻¹ · x)
-/

open scoped Matrix

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ### Smoothness and decay for affine reparametrization -/

/-- Composition of a Schwartz function with an affine map is smooth.
    This follows because affine maps are smooth (ContDiff ℝ ⊤) and
    the composition of smooth functions is smooth. -/
private theorem affineComp_smooth (g : PoincareGroup d) (f : SchwartzSpacetime d) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : SpacetimeDim d => f (PoincareGroup.act g x)) :=
  f.smooth'.comp (ContDiff.add
    ((Matrix.mulVecLin g.lorentz.val).toContinuousLinearMap).contDiff contDiff_const)

/-- The Poincaré action has temperate growth (affine maps are temperate). -/
private theorem poincareAct_hasTemperateGrowth (g : PoincareGroup d) :
    Function.HasTemperateGrowth (PoincareGroup.act g) := by
  have hL : Function.HasTemperateGrowth
      ((Matrix.mulVecLin g.lorentz.val).toContinuousLinearMap : SpacetimeDim d → SpacetimeDim d) :=
    ContinuousLinearMap.hasTemperateGrowth _
  convert (hL.add (Function.HasTemperateGrowth.const g.translation)) using 1

/-- The inverse Lorentz matrix recovers the original vector. -/
private theorem lorentz_inv_mulVec (g : PoincareGroup d) (x : SpacetimeDim d) :
    Matrix.mulVec g.lorentz⁻¹.val (Matrix.mulVec g.lorentz.val x) = x := by
  have : g.lorentz⁻¹.val * g.lorentz.val = 1 := by
    exact_mod_cast congr_arg Subtype.val (inv_mul_cancel (g.lorentz))
  rw [Matrix.mulVec_mulVec, this, Matrix.one_mulVec]

/-- Upper bound: ‖x‖ ≤ C * (1 + ‖g·x‖)^k for Poincaré actions (from invertibility). -/
private theorem poincareAct_upperBound (g : PoincareGroup d) :
    ∃ (k : ℕ) (C : ℝ), ∀ (x : SpacetimeDim d),
      ‖x‖ ≤ C * (1 + ‖PoincareGroup.act g x‖) ^ k := by
  set Λ_inv := (Matrix.mulVecLin g.lorentz⁻¹.val).toContinuousLinearMap
  refine ⟨1, ‖Λ_inv‖ * (1 + ‖g.translation‖), fun x => ?_⟩
  simp only [pow_one]
  have h1 : ‖x‖ ≤ ‖Λ_inv‖ * ‖g.lorentz.val.mulVec x‖ := by
    calc ‖x‖ = ‖g.lorentz⁻¹.val.mulVec (g.lorentz.val.mulVec x)‖ := by rw [lorentz_inv_mulVec]
      _ ≤ ‖Λ_inv‖ * ‖g.lorentz.val.mulVec x‖ := Λ_inv.le_opNorm _
  have h2 : ‖g.lorentz.val.mulVec x‖ ≤ ‖PoincareGroup.act g x‖ + ‖g.translation‖ := by
    rw [show g.lorentz.val.mulVec x = PoincareGroup.act g x - g.translation from by
      simp [PoincareGroup.act_def]]
    exact norm_sub_le _ _
  have h3 : ‖PoincareGroup.act g x‖ + ‖g.translation‖ ≤
      (1 + ‖g.translation‖) * (1 + ‖PoincareGroup.act g x‖) := by
    nlinarith [norm_nonneg (PoincareGroup.act g x), norm_nonneg g.translation]
  linarith [mul_le_mul_of_nonneg_left (le_trans h2 h3) (norm_nonneg Λ_inv)]

/-- Composition of a Schwartz function with a Poincaré action has polynomial decay.
    Uses `SchwartzMap.compCLM` which handles temperate growth compositions. -/
private theorem affineComp_decay (g : PoincareGroup d) (f : SchwartzSpacetime d)
    (k n : ℕ) :
    ∃ C, ∀ (x : SpacetimeDim d),
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => f (PoincareGroup.act g x)) x‖ ≤ C := by
  convert (SchwartzMap.compCLM ℂ (poincareAct_hasTemperateGrowth g)
    (poincareAct_upperBound g) f).decay' k n using 2

/-! ### The Poincaré action on Schwartz test functions -/

/-- The Poincaré action on a Schwartz test function:
    (g · f)(x) = f(g⁻¹ · x)

    This is well-defined because composition with an invertible affine map
    preserves the Schwartz class. -/
def poincareActSchwartz (g : PoincareGroup d) (f : SchwartzSpacetime d) :
    SchwartzSpacetime d where
  toFun x := f (PoincareGroup.act g⁻¹ x)
  smooth' := affineComp_smooth g⁻¹ f
  decay' k n := affineComp_decay g⁻¹ f k n

/-- The Poincaré action satisfies the pointwise spec:
    (g · f)(x) = f(g⁻¹ · x). -/
@[simp]
theorem poincareActSchwartz_apply (g : PoincareGroup d) (f : SchwartzSpacetime d)
    (x : SpacetimeDim d) :
    (poincareActSchwartz g f) x = f (PoincareGroup.act g⁻¹ x) := rfl

/-- The Poincaré action spec in terms of `.toFun` (matching WightmanQFT.poincareAction_spec). -/
theorem poincareActSchwartz_toFun (g : PoincareGroup d) (f : SchwartzSpacetime d)
    (x : SpacetimeDim d) :
    (poincareActSchwartz g f).toFun x = f.toFun (PoincareGroup.act g⁻¹ x) := rfl

/-! ### Group action properties -/

/-- The identity acts trivially: 1 · f = f. -/
theorem poincareActSchwartz_one (f : SchwartzSpacetime d) :
    poincareActSchwartz 1 f = f := by
  ext x
  simp [poincareActSchwartz_apply, PoincareGroup.act_one]

/-- The action is compatible with group multiplication: (g₁g₂) · f = g₁ · (g₂ · f). -/
theorem poincareActSchwartz_mul (g₁ g₂ : PoincareGroup d) (f : SchwartzSpacetime d) :
    poincareActSchwartz (g₁ * g₂) f = poincareActSchwartz g₁ (poincareActSchwartz g₂ f) := by
  ext x
  simp [poincareActSchwartz_apply, ← PoincareGroup.act_mul, mul_inv_rev]

end
