/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Groups.Lorentz

/-!
# The Full and Connected Poincaré Groups

This file defines both the full Poincaré group `ISO(1,d)` and its connected
proper-orthochronous subgroup `ISO⁺(1,d)` as semidirect products of translations
and Lorentz transformations.

## Main Definitions

* `FullPoincareGroup d` - The full Poincaré group ISO(1,d) = ℝ^{d+1} ⋊ O(1,d)
* `PoincareGroup d` - The connected Poincaré group ISO⁺(1,d) = ℝ^{d+1} ⋊ SO⁺(1,d)
* `PoincareGroup.act` - The action on spacetime: x ↦ Λx + a

## Mathematical Background

The full Poincaré group is the group of isometries of Minkowski spacetime. It consists of:
- Spacetime translations (ℝ^{d+1})
- Lorentz transformations (O(1,d))

The group multiplication is:
  (a₁, Λ₁) · (a₂, Λ₂) = (a₁ + Λ₁a₂, Λ₁Λ₂)

This is a semidirect product ℝ^{d+1} ⋊ O(1,d) where O(1,d) acts on ℝ^{d+1} by
matrix multiplication.

The default physics-facing `PoincareGroup d` in this file is the connected
proper-orthochronous subgroup ℝ^{d+1} ⋊ SO⁺(1,d). The full disconnected group
is kept explicitly as `FullPoincareGroup d`.

## References

* Weinberg, "The Quantum Theory of Fields", Vol. I, Chapter 2
* Streater-Wightman, "PCT, Spin and Statistics, and All That"
-/

noncomputable section

open Matrix BigOperators

set_option linter.unusedSectionVars false

variable (d : ℕ) [NeZero d]

/-! ### The Poincaré Group -/

/-- The full Poincaré group ISO(1,d) as pairs (translation, Lorentz transformation).
    An element (a, Λ) acts on spacetime as x ↦ Λx + a.

    The group multiplication is defined as:
      (a₁, Λ₁) · (a₂, Λ₂) = (a₁ + Λ₁a₂, Λ₁Λ₂)

    This realizes the semidirect product structure ℝ^{d+1} ⋊ O(1,d). -/
structure FullPoincareGroup (d : ℕ) [NeZero d] where
  /-- The translation component a ∈ ℝ^{d+1} -/
  translation : MinkowskiSpace d
  /-- The Lorentz transformation component Λ ∈ O(1,d) -/
  lorentz : FullLorentzGroup d

namespace FullPoincareGroup

local notation "PoincareGroup" => FullPoincareGroup
local notation "LorentzGroup" => FullLorentzGroup

variable {d : ℕ} [NeZero d]

@[ext]
theorem ext {g₁ g₂ : PoincareGroup d}
    (h_trans : g₁.translation = g₂.translation)
    (h_lor : g₁.lorentz = g₂.lorentz) : g₁ = g₂ := by
  cases g₁; cases g₂
  simp only at h_trans h_lor
  simp [h_trans, h_lor]

/-- Multiplication in the Poincaré group: (a₁, Λ₁) · (a₂, Λ₂) = (a₁ + Λ₁a₂, Λ₁Λ₂) -/
instance : Mul (PoincareGroup d) where
  mul g₁ g₂ := {
    translation := g₁.translation + mulVec g₁.lorentz.val g₂.translation
    lorentz := g₁.lorentz * g₂.lorentz
  }

@[simp] theorem mul_translation (g₁ g₂ : PoincareGroup d) :
    (g₁ * g₂).translation = g₁.translation + mulVec g₁.lorentz.val g₂.translation := rfl

@[simp] theorem mul_lorentz (g₁ g₂ : PoincareGroup d) :
    (g₁ * g₂).lorentz = g₁.lorentz * g₂.lorentz := rfl

/-- The identity element: (0, I) -/
instance : One (PoincareGroup d) where
  one := { translation := 0, lorentz := 1 }

@[simp] theorem one_translation : (1 : PoincareGroup d).translation = 0 := rfl

@[simp] theorem one_lorentz : (1 : PoincareGroup d).lorentz = 1 := rfl

@[simp] theorem one_lorentz_val : (1 : LorentzGroup d).val = 1 := rfl

@[simp] theorem mul_lorentz_val (Λ₁ Λ₂ : LorentzGroup d) :
    (Λ₁ * Λ₂).val = Λ₁.val * Λ₂.val := rfl

/-- The inverse: (a, Λ)⁻¹ = (-Λ⁻¹a, Λ⁻¹) -/
instance : Inv (PoincareGroup d) where
  inv g := {
    translation := -mulVec g.lorentz⁻¹.val g.translation
    lorentz := g.lorentz⁻¹
  }

@[simp] theorem inv_translation (g : PoincareGroup d) :
    g⁻¹.translation = -mulVec g.lorentz⁻¹.val g.translation := rfl

@[simp] theorem inv_lorentz (g : PoincareGroup d) :
    g⁻¹.lorentz = g.lorentz⁻¹ := rfl

/-- The Poincaré group forms a group under the semidirect product multiplication.

    The group axioms follow from:
    - Associativity: (a₁ + Λ₁a₂) + Λ₁Λ₂a₃ = a₁ + Λ₁(a₂ + Λ₂a₃) using mulVec_add and mulVec_mulVec
    - Left identity: 0 + I·a = a using one_mulVec
    - Right identity: a + Λ·0 = a using mulVec_zero
    - Left inverse: -Λ⁻¹a + Λ⁻¹Λa = 0 using inv_mul_cancel for Lorentz -/
instance : Group (PoincareGroup d) where
  mul_assoc a b c := by
    apply ext
    · -- Translation: (a₁ + Λ₁a₂) + Λ₁Λ₂a₃ = a₁ + Λ₁(a₂ + Λ₂a₃)
      simp only [mul_translation, mul_lorentz, mul_lorentz_val]
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
      abel
    · exact mul_assoc _ _ _
  one_mul a := by
    apply ext
    · simp only [mul_translation, one_translation, one_lorentz, one_lorentz_val,
        Matrix.one_mulVec, zero_add]
    · exact one_mul _
  mul_one a := by
    apply ext
    · simp only [mul_translation, one_translation, Matrix.mulVec_zero, add_zero]
    · exact mul_one _
  inv_mul_cancel a := by
    apply ext
    · -- -Λ⁻¹a + Λ⁻¹a = 0 (note: the second term uses inv_lorentz to simplify)
      simp only [mul_translation, inv_translation, inv_lorentz, one_translation]
      -- Goal: -mulVec a.lorentz⁻¹.val a.translation + mulVec a.lorentz⁻¹.val a.translation = 0
      exact neg_add_cancel _
    · exact inv_mul_cancel _

/-- Action of the Poincaré group on spacetime: x ↦ Λx + a -/
def act (g : PoincareGroup d) (x : MinkowskiSpace d) : MinkowskiSpace d :=
  mulVec g.lorentz.val x + g.translation

theorem act_def (g : PoincareGroup d) (x : MinkowskiSpace d) :
    g.act x = mulVec g.lorentz.val x + g.translation := rfl

/-- The action is compatible with group multiplication -/
theorem act_mul (g₁ g₂ : PoincareGroup d) (x : MinkowskiSpace d) :
    (g₁ * g₂).act x = g₁.act (g₂.act x) := by
  simp only [act, mul_translation, mul_lorentz, mul_lorentz_val]
  -- LHS: mulVec (g₁.lorentz.val * g₂.lorentz.val) x + (g₁.translation + mulVec g₁.lorentz.val g₂.translation)
  -- RHS: mulVec g₁.lorentz.val (mulVec g₂.lorentz.val x + g₂.translation) + g₁.translation
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
  -- Now both sides are equal up to associativity/commutativity of addition
  abel

/-- The identity acts trivially -/
@[simp]
theorem act_one (x : MinkowskiSpace d) : (1 : PoincareGroup d).act x = x := by
  simp only [act, one_translation, one_lorentz, one_lorentz_val, Matrix.one_mulVec, add_zero]

/-! ### Special Elements -/

/-- Pure translation: (a, 1) -/
def translation' (a : MinkowskiSpace d) : PoincareGroup d :=
  { translation := a, lorentz := 1 }

/-- Pure Lorentz transformation: (0, Λ) -/
def lorentz' (Λ : LorentzGroup d) : PoincareGroup d :=
  { translation := 0, lorentz := Λ }

@[simp]
theorem translation'_translation (a : MinkowskiSpace d) :
    (translation' a).translation = a := rfl

@[simp]
theorem translation'_lorentz (a : MinkowskiSpace d) :
    (translation' a).lorentz = 1 := rfl

@[simp]
theorem lorentz'_translation (Λ : LorentzGroup d) :
    (lorentz' Λ).translation = 0 := rfl

@[simp]
theorem lorentz'_lorentz (Λ : LorentzGroup d) :
    (lorentz' Λ).lorentz = Λ := rfl

@[simp]
theorem pureTranslation_act (a : MinkowskiSpace d) (x : MinkowskiSpace d) :
    (translation' a).act x = x + a := by
  simp only [act, translation'_translation, translation'_lorentz, one_lorentz_val,
    Matrix.one_mulVec]

@[simp]
theorem pureLorentz_act (Λ : LorentzGroup d) (x : MinkowskiSpace d) :
    (lorentz' Λ).act x = mulVec Λ.val x := by
  unfold act lorentz'
  simp only [add_zero]

end FullPoincareGroup

/-- The connected Poincaré group ISO⁺(1,d) as pairs of a translation and a
proper-orthochronous Lorentz transformation. -/
structure PoincareGroup (d : ℕ) [NeZero d] where
  /-- The translation component a ∈ ℝ^{d+1} -/
  translation : MinkowskiSpace d
  /-- The connected Lorentz component Λ ∈ SO⁺(1,d) -/
  lorentz : LorentzGroup d

namespace PoincareGroup

variable {d : ℕ} [NeZero d]

@[ext]
theorem ext {g₁ g₂ : PoincareGroup d}
    (h_trans : g₁.translation = g₂.translation)
    (h_lor : g₁.lorentz = g₂.lorentz) : g₁ = g₂ := by
  cases g₁; cases g₂
  simp only at h_trans h_lor
  simp [h_trans, h_lor]

/-- Forget the connectedness condition and view a connected Poincaré element
as an element of the full Poincaré group. -/
def toFull (g : PoincareGroup d) : FullPoincareGroup d :=
  { translation := g.translation, lorentz := g.lorentz.toFull }

instance : Coe (PoincareGroup d) (FullPoincareGroup d) := ⟨toFull⟩

instance : Mul (PoincareGroup d) where
  mul g₁ g₂ := {
    translation := g₁.translation + mulVec g₁.lorentz.val g₂.translation
    lorentz := g₁.lorentz * g₂.lorentz
  }

@[simp] theorem mul_translation (g₁ g₂ : PoincareGroup d) :
    (g₁ * g₂).translation = g₁.translation + mulVec g₁.lorentz.val g₂.translation := rfl

@[simp] theorem mul_lorentz (g₁ g₂ : PoincareGroup d) :
    (g₁ * g₂).lorentz = g₁.lorentz * g₂.lorentz := rfl

instance : One (PoincareGroup d) where
  one := { translation := 0, lorentz := 1 }

@[simp] theorem one_translation : (1 : PoincareGroup d).translation = 0 := rfl

@[simp] theorem one_lorentz : (1 : PoincareGroup d).lorentz = 1 := rfl

@[simp] theorem one_lorentz_val : (1 : LorentzGroup d).val = 1 := rfl

@[simp] theorem mul_lorentz_val (Λ₁ Λ₂ : LorentzGroup d) :
    (Λ₁ * Λ₂).val = Λ₁.val * Λ₂.val := rfl

instance : Inv (PoincareGroup d) where
  inv g := {
    translation := -mulVec g.lorentz⁻¹.val g.translation
    lorentz := g.lorentz⁻¹
  }

@[simp] theorem inv_translation (g : PoincareGroup d) :
    g⁻¹.translation = -mulVec g.lorentz⁻¹.val g.translation := rfl

@[simp] theorem inv_lorentz (g : PoincareGroup d) :
    g⁻¹.lorentz = g.lorentz⁻¹ := rfl

instance : Group (PoincareGroup d) where
  mul_assoc a b c := by
    apply ext
    · simp only [mul_translation, mul_lorentz, mul_lorentz_val]
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
      abel
    · exact mul_assoc _ _ _
  one_mul a := by
    apply ext
    · simp only [mul_translation, one_translation, one_lorentz, one_lorentz_val,
        Matrix.one_mulVec, zero_add]
    · exact one_mul _
  mul_one a := by
    apply ext
    · simp only [mul_translation, one_translation, Matrix.mulVec_zero, add_zero]
    · exact mul_one _
  inv_mul_cancel a := by
    apply ext
    · simp only [mul_translation, inv_translation, inv_lorentz, one_translation]
      exact neg_add_cancel _
    · exact inv_mul_cancel _

/-- Action of the connected Poincaré group on spacetime: x ↦ Λx + a -/
def act (g : PoincareGroup d) (x : MinkowskiSpace d) : MinkowskiSpace d :=
  mulVec g.lorentz.val x + g.translation

theorem act_def (g : PoincareGroup d) (x : MinkowskiSpace d) :
    g.act x = mulVec g.lorentz.val x + g.translation := rfl

theorem act_mul (g₁ g₂ : PoincareGroup d) (x : MinkowskiSpace d) :
    (g₁ * g₂).act x = g₁.act (g₂.act x) := by
  simp only [act, mul_translation, mul_lorentz, mul_lorentz_val]
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
  abel

@[simp]
theorem act_one (x : MinkowskiSpace d) : (1 : PoincareGroup d).act x = x := by
  simp only [act, one_translation, one_lorentz, one_lorentz_val, Matrix.one_mulVec, add_zero]

/-- Pure translation: `(a, 1)` in the connected Poincaré group. -/
def translation' (a : MinkowskiSpace d) : PoincareGroup d :=
  { translation := a, lorentz := 1 }

/-- Pure connected Lorentz transformation: `(0, Λ)`. -/
def lorentz' (Λ : LorentzGroup d) : PoincareGroup d :=
  { translation := 0, lorentz := Λ }

@[simp] theorem translation'_translation (a : MinkowskiSpace d) :
    (translation' a).translation = a := rfl

@[simp] theorem translation'_lorentz (a : MinkowskiSpace d) :
    (translation' a).lorentz = 1 := rfl

@[simp] theorem lorentz'_translation (Λ : LorentzGroup d) :
    (lorentz' Λ).translation = 0 := rfl

@[simp] theorem lorentz'_lorentz (Λ : LorentzGroup d) :
    (lorentz' Λ).lorentz = Λ := rfl

@[simp] theorem pureTranslation_act (a : MinkowskiSpace d) (x : MinkowskiSpace d) :
    (translation' a).act x = x + a := by
  simp only [act, translation'_translation, translation'_lorentz, one_lorentz_val,
    Matrix.one_mulVec]

@[simp] theorem pureLorentz_act (Λ : LorentzGroup d) (x : MinkowskiSpace d) :
    (lorentz' Λ).act x = mulVec Λ.val x := by
  unfold act lorentz'
  simp only [add_zero]

end PoincareGroup

/-! ### Notation -/

/-- Standard notation for the 3+1 dimensional full Poincaré group -/
abbrev FullPoincare4 := FullPoincareGroup 3

/-- Standard notation for the 3+1 dimensional connected Poincaré group -/
abbrev Poincare4 := PoincareGroup 3

end
