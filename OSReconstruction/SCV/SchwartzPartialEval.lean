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

omit [NormedSpace ℝ E₁] [NormedSpace ℝ E₂] in
private theorem norm_y_le_norm_prod (x : E₁) (y : E₂) :
    ‖y‖ ≤ ‖(x, y)‖ :=
  le_max_right _ _

/-- Pointwise evaluation of `iteratedFDeriv` on a Schwartz difference. -/
private theorem iteratedFDeriv_sub_schwartz
    (f g : SchwartzMap E₁ F) (n : ℕ) (x : E₁) :
    iteratedFDeriv ℝ n (⇑(f - g)) x =
      iteratedFDeriv ℝ n (⇑f) x - iteratedFDeriv ℝ n (⇑g) x := by
  have hf : ContDiff ℝ n (⇑f) := f.smooth n
  have hg : ContDiff ℝ n (⇑g) := g.smooth n
  have hfg : (⇑(f - g) : E₁ → F) = (⇑f) + fun x => -(⇑g x) := by
    ext y
    simp [sub_eq_add_neg]
  rw [hfg, iteratedFDeriv_add hf hg.neg]
  simp only [Pi.add_apply, sub_eq_add_neg]
  congr 1
  have : (fun x => -(⇑g x)) = -⇑g := rfl
  rw [this, iteratedFDeriv_neg, Pi.neg_apply]

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

/-- Partial evaluation of a Schwartz map in the first variable. -/
def schwartzPartialEval₁ (f : SchwartzMap (E₁ × E₂) F) (x : E₁) :
    SchwartzMap E₂ F where
  toFun y := f (x, y)
  smooth' := f.smooth'.comp (contDiff_prodMk_right x)
  decay' k l := by
    obtain ⟨C, hC⟩ := f.decay' k l
    refine ⟨C, ?_⟩
    intro y
    calc
      ‖y‖ ^ k * ‖iteratedFDeriv ℝ l (fun y' => f.toFun (x, y')) y‖
        ≤ ‖y‖ ^ k * ‖iteratedFDeriv ℝ l f.toFun (x, y)‖ := by
            apply mul_le_mul_of_nonneg_left
              (norm_iteratedFDeriv_partialEval₁_le f x l y)
            positivity
      _ ≤ ‖(x, y)‖ ^ k * ‖iteratedFDeriv ℝ l f.toFun (x, y)‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            gcongr
            exact norm_y_le_norm_prod x y
      _ ≤ C := hC (x, y)

@[simp]
theorem schwartzPartialEval₁_apply
    (f : SchwartzMap (E₁ × E₂) F) (x : E₁) (y : E₂) :
    schwartzPartialEval₁ f x y = f (x, y) :=
  rfl

/-- The Schwartz tails of `schwartzPartialEval₁ f x` are uniformly small in the
parameter `x` once `‖y‖` is sufficiently large. -/
theorem schwartzPartialEval₁_tail_small
    (f : SchwartzMap (E₁ × E₂) F) (k l : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : E₁, ∀ y : E₂, R < ‖y‖ →
      ‖y‖ ^ k * ‖iteratedFDeriv ℝ l (fun y' => f (x, y')) y‖ < ε := by
  obtain ⟨C, hC⟩ := f.decay' (k + 2) l
  have hC_nn : 0 ≤ C := le_trans (mul_nonneg (pow_nonneg (norm_nonneg _) _)
    (norm_nonneg _)) (hC 0)
  refine ⟨Real.sqrt (C / ε) + 1, by positivity, fun x y hy => ?_⟩
  have hy_pos : 0 < ‖y‖ := by
    linarith [Real.sqrt_nonneg (C / ε)]
  calc
    ‖y‖ ^ k * ‖iteratedFDeriv ℝ l (fun y' => f (x, y')) y‖
      ≤ ‖(x, y)‖ ^ k * ‖iteratedFDeriv ℝ l (⇑f) (x, y)‖ := by
          gcongr
          · exact le_max_right _ _
          · exact norm_iteratedFDeriv_partialEval₁_le f x l y
    _ ≤ C / ‖y‖ ^ 2 := by
          rw [le_div_iff₀ (pow_pos hy_pos 2)]
          calc
            ‖(x, y)‖ ^ k * ‖iteratedFDeriv ℝ l (⇑f) (x, y)‖ * ‖y‖ ^ 2
              ≤ ‖(x, y)‖ ^ k * ‖iteratedFDeriv ℝ l (⇑f) (x, y)‖ *
                  ‖(x, y)‖ ^ 2 := by
                  gcongr
                  exact le_max_right _ _
            _ = ‖(x, y)‖ ^ (k + 2) * ‖iteratedFDeriv ℝ l (⇑f) (x, y)‖ := by
                  ring
            _ ≤ C := hC (x, y)
    _ < ε := by
          rw [div_lt_iff₀ (pow_pos hy_pos 2)]
          have hR_sq : C / ε < ‖y‖ ^ 2 := by
            calc
              C / ε ≤ (Real.sqrt (C / ε)) ^ 2 := by
                rw [Real.sq_sqrt (div_nonneg hC_nn hε.le)]
              _ < (Real.sqrt (C / ε) + 1) ^ 2 := by
                nlinarith [Real.sqrt_nonneg (C / ε)]
              _ ≤ ‖y‖ ^ 2 := by
                apply sq_le_sq'
                · linarith [Real.sqrt_nonneg (C / ε), norm_nonneg y]
                · exact hy.le
          linarith [(div_lt_iff₀ hε).mp hR_sq]

/-- Fréchet derivative in the first product variable of the partially evaluated
`l`-th iterated derivative. -/
theorem hasFDerivAt_iteratedFDeriv_partialEval₁_param
    (f : SchwartzMap (E₁ × E₂) F) (l : ℕ) (x : E₁) (y : E₂) :
    HasFDerivAt
      (fun x' => iteratedFDeriv ℝ l (fun y' => f (x', y')) y)
      ((ContinuousMultilinearMap.compContinuousLinearMapL (F := _)
          (fun _ => ContinuousLinearMap.inr ℝ E₁ E₂)).comp
        ((fderiv ℝ (iteratedFDeriv ℝ l (⇑f)) (x, y)).comp
          (ContinuousLinearMap.inl ℝ E₁ E₂)))
      x := by
  let A :
      ContinuousMultilinearMap ℝ (fun _ : Fin l => E₁ × E₂) F →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin l => E₂) F :=
    ContinuousMultilinearMap.compContinuousLinearMapL (F := _)
      (fun _ => ContinuousLinearMap.inr ℝ E₁ E₂)
  let H :
      E₁ → ContinuousMultilinearMap ℝ (fun _ : Fin l => E₁ × E₂) F :=
    fun x' => iteratedFDeriv ℝ l (⇑f) (x', y)
  have hH :
      HasFDerivAt H
        ((fderiv ℝ (iteratedFDeriv ℝ l (⇑f)) (x, y)).comp
          (ContinuousLinearMap.inl ℝ E₁ E₂))
        x := by
    have hfull :
        HasFDerivAt (iteratedFDeriv ℝ l (⇑f))
          (fderiv ℝ (iteratedFDeriv ℝ l (⇑f)) (x, y)) (x, y) := by
      exact
        (f.smooth (l + 1)).differentiable_iteratedFDeriv
          (by exact_mod_cast Nat.lt_succ_self l) (x, y) |>.hasFDerivAt
    simpa [H] using hfull.comp x (hasFDerivAt_prodMk_left x y)
  have hEq :
      (fun x' => iteratedFDeriv ℝ l (fun y' => f (x', y')) y) = A ∘ H := by
    funext x'
    simp [A, H, iteratedFDeriv_partialEval₁_eq_compContinuousLinearMap_inr]
  rw [hEq]
  exact A.hasFDerivAt.comp x hH

/-- The derivative in the first product variable is controlled by the next
Schwartz iterated derivative of `f`. -/
theorem norm_fderiv_iteratedFDeriv_partialEval₁_param_le
    (f : SchwartzMap (E₁ × E₂) F) (l : ℕ) (x : E₁) (y : E₂) :
    ‖fderiv ℝ (fun x' => iteratedFDeriv ℝ l (fun y' => f (x', y')) y) x‖ ≤
      ‖iteratedFDeriv ℝ (l + 1) (⇑f) (x, y)‖ := by
  let A :
      ContinuousMultilinearMap ℝ (fun _ : Fin l => E₁ × E₂) F →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin l => E₂) F :=
    ContinuousMultilinearMap.compContinuousLinearMapL (F := _)
      (fun _ => ContinuousLinearMap.inr ℝ E₁ E₂)
  calc
    ‖fderiv ℝ (fun x' => iteratedFDeriv ℝ l (fun y' => f (x', y')) y) x‖
      = ‖A.comp
          ((fderiv ℝ (iteratedFDeriv ℝ l (⇑f)) (x, y)).comp
            (ContinuousLinearMap.inl ℝ E₁ E₂))‖ := by
          rw [show
              fderiv ℝ (fun x' => iteratedFDeriv ℝ l (fun y' => f (x', y')) y) x =
                A.comp
                  ((fderiv ℝ (iteratedFDeriv ℝ l (⇑f)) (x, y)).comp
                    (ContinuousLinearMap.inl ℝ E₁ E₂)) by
              simpa [A] using
                (hasFDerivAt_iteratedFDeriv_partialEval₁_param f l x y).fderiv]
    _ ≤ ‖A‖ *
          ‖(fderiv ℝ (iteratedFDeriv ℝ l (⇑f)) (x, y)).comp
            (ContinuousLinearMap.inl ℝ E₁ E₂)‖ := by
          exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 *
          ‖(fderiv ℝ (iteratedFDeriv ℝ l (⇑f)) (x, y)).comp
            (ContinuousLinearMap.inl ℝ E₁ E₂)‖ := by
          have hA :
              ‖A‖ ≤ ∏ _ : Fin l, ‖ContinuousLinearMap.inr ℝ E₁ E₂‖ := by
            simpa [A] using
              (ContinuousMultilinearMap.norm_compContinuousLinearMapL_le
                (𝕜 := ℝ) (ι := Fin l)
                (E := fun _ : Fin l => E₂)
                (E₁ := fun _ : Fin l => E₁ × E₂)
                (G := _)
                (fun _ => ContinuousLinearMap.inr ℝ E₁ E₂))
          have hone_prod : ∏ _ : Fin l, ‖ContinuousLinearMap.inr ℝ E₁ E₂‖ ≤ (1 : ℝ) := by
            apply Finset.prod_le_one
            · intro i hi
              exact norm_nonneg _
            · intro i hi
              exact ContinuousLinearMap.norm_inr_le_one ℝ E₁ E₂
          have hA1 : ‖A‖ ≤ (1 : ℝ) := hA.trans hone_prod
          nlinarith [hA1, norm_nonneg
            ((fderiv ℝ (iteratedFDeriv ℝ l (⇑f)) (x, y)).comp
              (ContinuousLinearMap.inl ℝ E₁ E₂))]
    _ = ‖(fderiv ℝ (iteratedFDeriv ℝ l (⇑f)) (x, y)).comp
          (ContinuousLinearMap.inl ℝ E₁ E₂)‖ := by simp
    _ ≤ ‖fderiv ℝ (iteratedFDeriv ℝ l (⇑f)) (x, y)‖ *
          ‖ContinuousLinearMap.inl ℝ E₁ E₂‖ := by
          exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ (iteratedFDeriv ℝ l (⇑f)) (x, y)‖ * 1 := by
          have hinl : ‖ContinuousLinearMap.inl ℝ E₁ E₂‖ ≤ (1 : ℝ) :=
            ContinuousLinearMap.norm_inl_le_one ℝ E₁ E₂
          nlinarith [hinl, norm_nonneg
            (fderiv ℝ (iteratedFDeriv ℝ l (⇑f)) (x, y))]
    _ = ‖fderiv ℝ (iteratedFDeriv ℝ l (⇑f)) (x, y)‖ := by simp
    _ = ‖iteratedFDeriv ℝ (l + 1) (⇑f) (x, y)‖ := by
          exact norm_fderiv_iteratedFDeriv

/-- First-variable partial evaluation is continuous in the Schwartz topology. -/
theorem continuous_schwartzPartialEval₁
    (f : SchwartzMap (E₁ × E₂) F) :
    Continuous (fun x => schwartzPartialEval₁ f x) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  change Filter.Tendsto (fun x => schwartzPartialEval₁ f x)
    (nhds x₀) (nhds (schwartzPartialEval₁ f x₀))
  rw [(schwartz_withSeminorms ℝ E₂ F).tendsto_nhds _ _]
  intro p ε hε
  rcases p with ⟨k, l⟩
  have hε8 : 0 < ε / 8 := by positivity
  obtain ⟨R, hRpos, htail⟩ := schwartzPartialEval₁_tail_small f k l (ε / 8) hε8
  obtain ⟨C, hC⟩ := f.decay' 0 (l + 1)
  have hC_nonneg : 0 ≤ C := by
    have hC0 : ‖iteratedFDeriv ℝ (l + 1) (⇑f) (x₀, 0)‖ ≤ C := by
      simpa using hC (x₀, 0)
    exact le_trans (norm_nonneg _) hC0
  let A : ℝ := (max R 1) ^ k * C
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  let δ : ℝ := ε / (4 * (A + 1))
  have hδ_pos : 0 < δ := by
    dsimp [δ, A]
    positivity
  filter_upwards [Metric.ball_mem_nhds x₀ hδ_pos] with x hx
  have hx_lt : ‖x - x₀‖ < δ := by
    simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using hx
  rw [schwartzSeminormFamily_apply]
  have hsemi :
      SchwartzMap.seminorm ℝ k l
        (schwartzPartialEval₁ f x - schwartzPartialEval₁ f x₀) ≤ ε / 2 := by
    refine SchwartzMap.seminorm_le_bound ℝ k l
      (schwartzPartialEval₁ f x - schwartzPartialEval₁ f x₀) (by positivity) ?_
    intro y
    by_cases hy : R < ‖y‖
    · have hx_tail :
          ‖y‖ ^ k * ‖iteratedFDeriv ℝ l (fun y' => f (x, y')) y‖ < ε / 8 :=
        htail x y hy
      have hx₀_tail :
          ‖y‖ ^ k * ‖iteratedFDeriv ℝ l (fun y' => f (x₀, y')) y‖ < ε / 8 :=
        htail x₀ y hy
      have hpoint :
          ‖y‖ ^ k *
              ‖iteratedFDeriv ℝ l
                  (⇑(schwartzPartialEval₁ f x - schwartzPartialEval₁ f x₀)) y‖ ≤
            ε / 4 := by
        have hpoint_lt :
            ‖y‖ ^ k *
                ‖iteratedFDeriv ℝ l
                    (⇑(schwartzPartialEval₁ f x - schwartzPartialEval₁ f x₀)) y‖ <
              ε / 4 := by
          calc
          ‖y‖ ^ k *
              ‖iteratedFDeriv ℝ l
                  (⇑(schwartzPartialEval₁ f x - schwartzPartialEval₁ f x₀)) y‖
            = ‖y‖ ^ k *
                ‖iteratedFDeriv ℝ l (fun y' => f (x, y')) y -
                  iteratedFDeriv ℝ l (fun y' => f (x₀, y')) y‖ := by
                  rw [iteratedFDeriv_sub_schwartz]
                  change
                    ‖y‖ ^ k *
                        ‖iteratedFDeriv ℝ l (fun y' => f (x, y')) y -
                          iteratedFDeriv ℝ l (fun y' => f (x₀, y')) y‖ =
                      ‖y‖ ^ k *
                        ‖iteratedFDeriv ℝ l (fun y' => f (x, y')) y -
                          iteratedFDeriv ℝ l (fun y' => f (x₀, y')) y‖
                  rfl
          _ ≤ ‖y‖ ^ k * ‖iteratedFDeriv ℝ l (fun y' => f (x, y')) y‖ +
                ‖y‖ ^ k * ‖iteratedFDeriv ℝ l (fun y' => f (x₀, y')) y‖ := by
                have hk_nonneg : 0 ≤ ‖y‖ ^ k := by positivity
                calc
                  ‖y‖ ^ k *
                      ‖iteratedFDeriv ℝ l (fun y' => f (x, y')) y -
                        iteratedFDeriv ℝ l (fun y' => f (x₀, y')) y‖
                    ≤ ‖y‖ ^ k *
                        (‖iteratedFDeriv ℝ l (fun y' => f (x, y')) y‖ +
                          ‖iteratedFDeriv ℝ l (fun y' => f (x₀, y')) y‖) := by
                            exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) hk_nonneg
                  _ = ‖y‖ ^ k * ‖iteratedFDeriv ℝ l (fun y' => f (x, y')) y‖ +
                        ‖y‖ ^ k * ‖iteratedFDeriv ℝ l (fun y' => f (x₀, y')) y‖ := by
                            ring
          _ < ε / 8 + ε / 8 := add_lt_add hx_tail hx₀_tail
          _ = ε / 4 := by ring
        exact hpoint_lt.le
      exact hpoint.trans (by linarith)
    · have hyR : ‖y‖ ≤ R := le_of_not_gt hy
      have hbound_diff :
          ‖iteratedFDeriv ℝ l (fun y' => f (x, y')) y -
              iteratedFDeriv ℝ l (fun y' => f (x₀, y')) y‖ ≤
            C * ‖x - x₀‖ := by
        let g :
            E₁ → ContinuousMultilinearMap ℝ (fun _ : Fin l => E₂) F :=
          fun x' => iteratedFDeriv ℝ l (fun y' => f (x', y')) y
        have hdiff :
            ∀ z : E₁, DifferentiableAt ℝ g z := by
          intro z
          exact (hasFDerivAt_iteratedFDeriv_partialEval₁_param f l z y).differentiableAt
        have hbound :
            ∀ z : E₁, ‖fderiv ℝ g z‖ ≤ C := by
          intro z
          calc
            ‖fderiv ℝ g z‖
              ≤ ‖iteratedFDeriv ℝ (l + 1) (⇑f) (z, y)‖ := by
                  simpa [g] using norm_fderiv_iteratedFDeriv_partialEval₁_param_le f l z y
            _ ≤ C := by
                  simpa using hC (z, y)
        simpa [g] using
          (Convex.norm_image_sub_le_of_norm_fderiv_le
            (s := (Set.univ : Set E₁))
            (f := g)
            (x := x₀) (y := x)
            (fun z _ => hdiff z)
            (fun z _ => hbound z)
            convex_univ (by simp) (by simp))
      have hnormy :
          ‖y‖ ^ k ≤ (max R 1) ^ k := by
        have hymax : ‖y‖ ≤ max R 1 := hyR.trans (le_max_left _ _)
        gcongr
      have hpoint :
          ‖y‖ ^ k *
              ‖iteratedFDeriv ℝ l
                  (⇑(schwartzPartialEval₁ f x - schwartzPartialEval₁ f x₀)) y‖ ≤
            ε / 4 := by
        calc
          ‖y‖ ^ k *
              ‖iteratedFDeriv ℝ l
                  (⇑(schwartzPartialEval₁ f x - schwartzPartialEval₁ f x₀)) y‖
            = ‖y‖ ^ k *
                ‖iteratedFDeriv ℝ l (fun y' => f (x, y')) y -
                  iteratedFDeriv ℝ l (fun y' => f (x₀, y')) y‖ := by
                  rw [iteratedFDeriv_sub_schwartz]
                  change
                    ‖y‖ ^ k *
                        ‖iteratedFDeriv ℝ l (fun y' => f (x, y')) y -
                          iteratedFDeriv ℝ l (fun y' => f (x₀, y')) y‖ =
                      ‖y‖ ^ k *
                        ‖iteratedFDeriv ℝ l (fun y' => f (x, y')) y -
                          iteratedFDeriv ℝ l (fun y' => f (x₀, y')) y‖
                  rfl
          _ ≤ ‖y‖ ^ k * (C * ‖x - x₀‖) := by
                exact mul_le_mul_of_nonneg_left hbound_diff (by positivity)
          _ ≤ (max R 1) ^ k * (C * ‖x - x₀‖) := by
                exact mul_le_mul_of_nonneg_right hnormy (by positivity)
          _ = A * ‖x - x₀‖ := by
                simp [A, mul_assoc, mul_left_comm, mul_comm]
          _ ≤ A * δ := by
                exact mul_le_mul_of_nonneg_left hx_lt.le hA_nonneg
          _ ≤ ε / 4 := by
                dsimp [δ]
                have hA1_pos : 0 < A + 1 := by linarith
                have hA_frac : A / (A + 1) ≤ (1 : ℝ) := by
                  exact (div_le_iff₀ hA1_pos).2 (by nlinarith)
                have hcalc :
                    A * (ε / (4 * (A + 1))) = (ε / 4) * (A / (A + 1)) := by
                  field_simp [hA1_pos.ne']
                rw [hcalc]
                have hε4_nonneg : 0 ≤ ε / 4 := by linarith
                simpa using mul_le_mul_of_nonneg_left hA_frac hε4_nonneg
      exact hpoint.trans (by linarith)
  exact lt_of_le_of_lt hsemi (by linarith)

end SCV
