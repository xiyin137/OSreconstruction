/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Partial evaluation of Schwartz maps

This file contains the pure finite-dimensional Schwartz-space fact that
partially evaluating a Schwartz map on a product is again Schwartz.  It is the
QFT-free part of the old reconstruction partial-evaluation source, extracted
for the SCV quotient-descent route.
-/

noncomputable section

open SchwartzMap ContinuousLinearMap

namespace SCV

variable {E₁ E₂ F : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E₁] [NormedSpace ℝ E₂] in
private theorem norm_x_le_norm_prod (x : E₁) (y : E₂) :
    ‖x‖ ≤ ‖(x, y)‖ :=
  le_max_left _ _

/-- The iterated derivative of a partial evaluation is the full product
iterated derivative precomposed with the first-factor inclusion. -/
theorem iteratedFDeriv_partialEval_eq_compContinuousLinearMap_inl
    (f : SchwartzMap (E₁ × E₂) F) (y : E₂) (l : ℕ) (x : E₁) :
    iteratedFDeriv ℝ l (fun x' => f (x', y)) x =
      (iteratedFDeriv ℝ l (⇑f) (x, y)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inl ℝ E₁ E₂) := by
  have htranslate : ∀ x',
      iteratedFDeriv ℝ l (fun z : E₁ × E₂ => f (z + (0, y))) (x', (0 : E₂)) =
        iteratedFDeriv ℝ l (⇑f) (x' + 0, (0 : E₂) + y) := by
    intro x'
    rw [iteratedFDeriv_comp_add_right' l (0, y)]
    simp [Prod.add_def]
  have hcomp : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun z : E₁ × E₂ => f (z + ((0 : E₁), y))) :=
    f.smooth'.comp ((contDiff_id.add contDiff_const).of_le le_top)
  have hinl_comp := ContinuousLinearMap.iteratedFDeriv_comp_right
    (ContinuousLinearMap.inl ℝ E₁ E₂) hcomp x (by exact_mod_cast le_top (a := (l : ℕ∞)))
  have hlhs :
      (fun x' => f (x', y)) =
        (fun z : E₁ × E₂ => f (z + (0, y))) ∘
          (ContinuousLinearMap.inl ℝ E₁ E₂) := by
    ext x'
    simp [ContinuousLinearMap.inl_apply]
  rw [hlhs, hinl_comp]
  exact congrArg
    (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin l => E₁ × E₂) F =>
      A.compContinuousLinearMap (fun _ => ContinuousLinearMap.inl ℝ E₁ E₂))
    (by simpa [ContinuousLinearMap.inl_apply] using htranslate x)

/-- The iterated derivatives of a partial evaluation are norm-controlled by the
corresponding full product derivatives. -/
theorem norm_iteratedFDeriv_partialEval_le
    (f : SchwartzMap (E₁ × E₂) F) (y : E₂) (l : ℕ) (x : E₁) :
    ‖iteratedFDeriv ℝ l (fun x' => f (x', y)) x‖ ≤
      ‖iteratedFDeriv ℝ l (⇑f) (x, y)‖ := by
  rw [iteratedFDeriv_partialEval_eq_compContinuousLinearMap_inl]
  calc
    ‖(iteratedFDeriv ℝ l (⇑f) (x, y)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inl ℝ E₁ E₂)‖
      ≤ ‖iteratedFDeriv ℝ l (⇑f) (x, y)‖ *
          ∏ _ : Fin l, ‖ContinuousLinearMap.inl ℝ E₁ E₂‖ := by
        exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ l (⇑f) (x, y)‖ * 1 := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
        intro _ _
        exact ContinuousLinearMap.norm_inl_le_one ℝ E₁ E₂
    _ = ‖iteratedFDeriv ℝ l (⇑f) (x, y)‖ := by
        simp

/-- The iterated derivative of a first-variable partial evaluation is the full
product iterated derivative precomposed with the second-factor inclusion. -/
theorem iteratedFDeriv_partialEval₁_eq_compContinuousLinearMap_inr
    (f : SchwartzMap (E₁ × E₂) F) (x : E₁) (l : ℕ) (y : E₂) :
    iteratedFDeriv ℝ l (fun y' => f (x, y')) y =
      (iteratedFDeriv ℝ l (⇑f) (x, y)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ E₁ E₂) := by
  have htranslate : ∀ y',
      iteratedFDeriv ℝ l (fun z : E₁ × E₂ => f (z + (x, 0))) ((0 : E₁), y') =
        iteratedFDeriv ℝ l (⇑f) ((0 : E₁) + x, y' + 0) := by
    intro y'
    rw [iteratedFDeriv_comp_add_right' l (x, 0)]
    simp [Prod.add_def]
  have hcomp : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun z : E₁ × E₂ => f (z + (x, (0 : E₂)))) :=
    f.smooth'.comp ((contDiff_id.add contDiff_const).of_le le_top)
  have hinr_comp := ContinuousLinearMap.iteratedFDeriv_comp_right
    (ContinuousLinearMap.inr ℝ E₁ E₂) hcomp y (by exact_mod_cast le_top (a := (l : ℕ∞)))
  have hlhs :
      (fun y' => f (x, y')) =
        (fun z : E₁ × E₂ => f (z + (x, (0 : E₂)))) ∘
          (ContinuousLinearMap.inr ℝ E₁ E₂) := by
    ext y'
    simp [ContinuousLinearMap.inr_apply]
  rw [hlhs, hinr_comp]
  exact congrArg
    (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin l => E₁ × E₂) F =>
      A.compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ E₁ E₂))
    (by simpa [ContinuousLinearMap.inr_apply] using htranslate y)

/-- The iterated derivatives of a first-variable partial evaluation are
norm-controlled by the corresponding full product derivatives. -/
theorem norm_iteratedFDeriv_partialEval₁_le
    (f : SchwartzMap (E₁ × E₂) F) (x : E₁) (l : ℕ) (y : E₂) :
    ‖iteratedFDeriv ℝ l (fun y' => f (x, y')) y‖ ≤
      ‖iteratedFDeriv ℝ l (⇑f) (x, y)‖ := by
  rw [iteratedFDeriv_partialEval₁_eq_compContinuousLinearMap_inr]
  calc
    ‖(iteratedFDeriv ℝ l (⇑f) (x, y)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ E₁ E₂)‖
      ≤ ‖iteratedFDeriv ℝ l (⇑f) (x, y)‖ *
          ∏ _ : Fin l, ‖ContinuousLinearMap.inr ℝ E₁ E₂‖ := by
        exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ l (⇑f) (x, y)‖ * 1 := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
        intro _ _
        exact ContinuousLinearMap.norm_inr_le_one ℝ E₁ E₂
    _ = ‖iteratedFDeriv ℝ l (⇑f) (x, y)‖ := by
        simp

/-- Partial evaluation of a Schwartz map in the second variable. -/
def schwartzPartialEval₂ (f : SchwartzMap (E₁ × E₂) F) (y : E₂) :
    SchwartzMap E₁ F where
  toFun x := f (x, y)
  smooth' := f.smooth'.comp (contDiff_prodMk_left y)
  decay' k l := by
    obtain ⟨C, hC⟩ := f.decay' k l
    refine ⟨C, ?_⟩
    intro x
    calc
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun x' => f.toFun (x', y)) x‖
        ≤ ‖x‖ ^ k * ‖iteratedFDeriv ℝ l f.toFun (x, y)‖ := by
            apply mul_le_mul_of_nonneg_left
              (norm_iteratedFDeriv_partialEval_le f y l x)
            positivity
      _ ≤ ‖(x, y)‖ ^ k * ‖iteratedFDeriv ℝ l f.toFun (x, y)‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            gcongr
            exact norm_x_le_norm_prod x y
      _ ≤ C := hC (x, y)

@[simp]
theorem schwartzPartialEval₂_apply
    (f : SchwartzMap (E₁ × E₂) F) (y : E₂) (x : E₁) :
    schwartzPartialEval₂ f y x = f (x, y) :=
  rfl

end SCV
