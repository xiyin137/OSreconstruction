import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import OSReconstruction.Wightman.Reconstruction.Core

noncomputable section

open SchwartzMap ContinuousLinearMap

namespace OSReconstruction

variable {E₁ E₂ F : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E₁] [NormedSpace ℝ E₂] in
private theorem norm_x_le_norm_prod (x : E₁) (y : E₂) :
    ‖x‖ ≤ ‖(x, y)‖ :=
  le_max_left _ _

/-- Pointwise evaluation of `iteratedFDeriv` on a Schwartz difference. -/
private theorem iteratedFDeriv_sub_schwartz (f g : SchwartzMap E₁ F) (n : ℕ) (x : E₁) :
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

/-- The iterated derivative of the partial evaluation `x ↦ f (x, y)` is bounded
by the corresponding iterated derivative of `f` at `(x, y)`. -/
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
  have hcomp : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun z : E₁ × E₂ => f (z + ((0 : E₁), y))) :=
    f.smooth'.comp ((contDiff_id.add contDiff_const).of_le le_top)
  have hinl_comp := ContinuousLinearMap.iteratedFDeriv_comp_right
    (ContinuousLinearMap.inl ℝ E₁ E₂) hcomp x (by exact_mod_cast le_top (a := (l : ℕ∞)))
  have hlhs :
      (fun x' => f (x', y)) =
        (fun z : E₁ × E₂ => f (z + (0, y))) ∘ (ContinuousLinearMap.inl ℝ E₁ E₂) := by
    ext x'
    simp [ContinuousLinearMap.inl_apply]
  rw [hlhs, hinl_comp]
  exact congrArg
    (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin l => E₁ × E₂) F =>
      A.compContinuousLinearMap (fun _ => ContinuousLinearMap.inl ℝ E₁ E₂))
    (by simpa [ContinuousLinearMap.inl_apply] using htranslate x)

/-- The iterated derivative of the partial evaluation `x ↦ f (x, y)` is bounded
by the corresponding iterated derivative of `f` at `(x, y)`. -/
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

/-- Partial evaluation of a Schwartz function in the second variable is again
a Schwartz function. -/
def SchwartzMap.partialEval₂ (f : SchwartzMap (E₁ × E₂) F) (y : E₂) :
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

/-- The Schwartz tails of `partialEval₂ f y` are uniformly small in the parameter `y`
once `‖x‖` is sufficiently large. -/
theorem partialEval₂_tail_small
    (f : SchwartzMap (E₁ × E₂) F) (k l : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ y : E₂, ∀ x : E₁, R < ‖x‖ →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun x' => f (x', y)) x‖ < ε := by
  obtain ⟨C, hC⟩ := f.decay' (k + 2) l
  have hC_nn : 0 ≤ C := le_trans (mul_nonneg (pow_nonneg (norm_nonneg _) _)
    (norm_nonneg _)) (hC 0)
  refine ⟨Real.sqrt (C / ε) + 1, by positivity, fun y x hx => ?_⟩
  have hx_pos : 0 < ‖x‖ := by
    linarith [Real.sqrt_nonneg (C / ε)]
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun x' => f (x', y)) x‖
      ≤ ‖(x, y)‖ ^ k * ‖iteratedFDeriv ℝ l (⇑f) (x, y)‖ := by
          gcongr
          · exact le_max_left _ _
          · exact norm_iteratedFDeriv_partialEval_le f y l x
    _ ≤ C / ‖x‖ ^ 2 := by
          rw [le_div_iff₀ (pow_pos hx_pos 2)]
          calc
            ‖(x, y)‖ ^ k * ‖iteratedFDeriv ℝ l (⇑f) (x, y)‖ * ‖x‖ ^ 2
              ≤ ‖(x, y)‖ ^ k * ‖iteratedFDeriv ℝ l (⇑f) (x, y)‖ * ‖(x, y)‖ ^ 2 := by
                  gcongr
                  exact le_max_left _ _
            _ = ‖(x, y)‖ ^ (k + 2) * ‖iteratedFDeriv ℝ l (⇑f) (x, y)‖ := by ring
            _ ≤ C := hC (x, y)
    _ < ε := by
          rw [div_lt_iff₀ (pow_pos hx_pos 2)]
          have hR_sq : C / ε < ‖x‖ ^ 2 := by
            calc
              C / ε ≤ (Real.sqrt (C / ε)) ^ 2 := by
                rw [Real.sq_sqrt (div_nonneg hC_nn hε.le)]
              _ < (Real.sqrt (C / ε) + 1) ^ 2 := by
                nlinarith [Real.sqrt_nonneg (C / ε)]
              _ ≤ ‖x‖ ^ 2 := by
                apply sq_le_sq'
                · linarith [Real.sqrt_nonneg (C / ε), norm_nonneg x]
                · exact hx.le
          linarith [(div_lt_iff₀ hε).mp hR_sq]

/-- Fréchet derivative in the parameter `y` of the partially evaluated
`l`-th iterated derivative. -/
theorem hasFDerivAt_iteratedFDeriv_partialEval₂
    (f : SchwartzMap (E₁ × E₂) F) (l : ℕ) (x : E₁) (y : E₂) :
    HasFDerivAt
      (fun y' => iteratedFDeriv ℝ l (fun x' => f (x', y')) x)
      ((ContinuousMultilinearMap.compContinuousLinearMapL (F := _)
          (fun _ => ContinuousLinearMap.inl ℝ E₁ E₂)).comp
        ((fderiv ℝ (iteratedFDeriv ℝ l (⇑f)) (x, y)).comp
          (ContinuousLinearMap.inr ℝ E₁ E₂)))
      y := by
  let A :
      ContinuousMultilinearMap ℝ (fun _ : Fin l => E₁ × E₂) F →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin l => E₁) F :=
    ContinuousMultilinearMap.compContinuousLinearMapL (F := _)
      (fun _ => ContinuousLinearMap.inl ℝ E₁ E₂)
  let H :
      E₂ → ContinuousMultilinearMap ℝ (fun _ : Fin l => E₁ × E₂) F :=
    fun y' => iteratedFDeriv ℝ l (⇑f) (x, y')
  have hH :
      HasFDerivAt H
        ((fderiv ℝ (iteratedFDeriv ℝ l (⇑f)) (x, y)).comp
          (ContinuousLinearMap.inr ℝ E₁ E₂))
        y := by
    have hfull :
        HasFDerivAt (iteratedFDeriv ℝ l (⇑f))
          (fderiv ℝ (iteratedFDeriv ℝ l (⇑f)) (x, y)) (x, y) := by
      exact
        (f.smooth (l + 1)).differentiable_iteratedFDeriv
          (by exact_mod_cast Nat.lt_succ_self l) (x, y) |>.hasFDerivAt
    simpa [H] using hfull.comp y (hasFDerivAt_prodMk_right x y)
  have hEq :
      (fun y' => iteratedFDeriv ℝ l (fun x' => f (x', y')) x) = A ∘ H := by
    funext y'
    simp [A, H, iteratedFDeriv_partialEval_eq_compContinuousLinearMap_inl]
  rw [hEq]
  exact A.hasFDerivAt.comp y hH

/-- The derivative in the parameter `y` is controlled by the next Schwartz
iterated derivative of `f`. -/
theorem norm_fderiv_iteratedFDeriv_partialEval₂_le
    (f : SchwartzMap (E₁ × E₂) F) (l : ℕ) (x : E₁) (y : E₂) :
    ‖fderiv ℝ (fun y' => iteratedFDeriv ℝ l (fun x' => f (x', y')) x) y‖ ≤
      ‖iteratedFDeriv ℝ (l + 1) (⇑f) (x, y)‖ := by
  let A :
      ContinuousMultilinearMap ℝ (fun _ : Fin l => E₁ × E₂) F →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin l => E₁) F :=
    ContinuousMultilinearMap.compContinuousLinearMapL (F := _)
      (fun _ => ContinuousLinearMap.inl ℝ E₁ E₂)
  calc
    ‖fderiv ℝ (fun y' => iteratedFDeriv ℝ l (fun x' => f (x', y')) x) y‖
      = ‖A.comp
          ((fderiv ℝ (iteratedFDeriv ℝ l (⇑f)) (x, y)).comp
            (ContinuousLinearMap.inr ℝ E₁ E₂))‖ := by
          rw [show
              fderiv ℝ (fun y' => iteratedFDeriv ℝ l (fun x' => f (x', y')) x) y =
                A.comp
                  ((fderiv ℝ (iteratedFDeriv ℝ l (⇑f)) (x, y)).comp
                    (ContinuousLinearMap.inr ℝ E₁ E₂)) by
              simpa [A] using (hasFDerivAt_iteratedFDeriv_partialEval₂ f l x y).fderiv]
    _ ≤ ‖A‖ *
          ‖(fderiv ℝ (iteratedFDeriv ℝ l (⇑f)) (x, y)).comp
            (ContinuousLinearMap.inr ℝ E₁ E₂)‖ := by
          exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 *
          ‖(fderiv ℝ (iteratedFDeriv ℝ l (⇑f)) (x, y)).comp
            (ContinuousLinearMap.inr ℝ E₁ E₂)‖ := by
          have hA :
              ‖A‖ ≤ ∏ _ : Fin l, ‖ContinuousLinearMap.inl ℝ E₁ E₂‖ := by
            simpa [A] using
              (ContinuousMultilinearMap.norm_compContinuousLinearMapL_le
                (𝕜 := ℝ) (ι := Fin l)
                (E := fun _ : Fin l => E₁)
                (E₁ := fun _ : Fin l => E₁ × E₂)
                (G := _)
                (fun _ => ContinuousLinearMap.inl ℝ E₁ E₂))
          have hone_prod : ∏ _ : Fin l, ‖ContinuousLinearMap.inl ℝ E₁ E₂‖ ≤ (1 : ℝ) := by
            apply Finset.prod_le_one
            · intro i hi
              exact norm_nonneg _
            · intro i hi
              exact ContinuousLinearMap.norm_inl_le_one ℝ E₁ E₂
          have hA1 : ‖A‖ ≤ (1 : ℝ) := hA.trans hone_prod
          nlinarith [hA1, norm_nonneg
            ((fderiv ℝ (iteratedFDeriv ℝ l (⇑f)) (x, y)).comp
              (ContinuousLinearMap.inr ℝ E₁ E₂))]
    _ = ‖(fderiv ℝ (iteratedFDeriv ℝ l (⇑f)) (x, y)).comp
          (ContinuousLinearMap.inr ℝ E₁ E₂)‖ := by simp
    _ ≤ ‖fderiv ℝ (iteratedFDeriv ℝ l (⇑f)) (x, y)‖ *
          ‖ContinuousLinearMap.inr ℝ E₁ E₂‖ := by
          exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ (iteratedFDeriv ℝ l (⇑f)) (x, y)‖ * 1 := by
          have hinr : ‖ContinuousLinearMap.inr ℝ E₁ E₂‖ ≤ (1 : ℝ) :=
            ContinuousLinearMap.norm_inr_le_one ℝ E₁ E₂
          nlinarith [hinr, norm_nonneg
            (fderiv ℝ (iteratedFDeriv ℝ l (⇑f)) (x, y))]
    _ = ‖fderiv ℝ (iteratedFDeriv ℝ l (⇑f)) (x, y)‖ := by simp
    _ = ‖iteratedFDeriv ℝ (l + 1) (⇑f) (x, y)‖ := by
          exact norm_fderiv_iteratedFDeriv

/-- Partial evaluation is continuous in the second variable for the Schwartz
topology. -/
theorem continuous_partialEval₂
    (f : SchwartzMap (E₁ × E₂) F) :
    Continuous (fun y => SchwartzMap.partialEval₂ f y) := by
  rw [continuous_iff_continuousAt]
  intro y₀
  change Filter.Tendsto (fun y => SchwartzMap.partialEval₂ f y)
    (nhds y₀) (nhds (SchwartzMap.partialEval₂ f y₀))
  rw [(schwartz_withSeminorms ℝ E₁ F).tendsto_nhds _ _]
  intro p ε hε
  rcases p with ⟨k, l⟩
  have hε8 : 0 < ε / 8 := by positivity
  obtain ⟨R, hRpos, htail⟩ := partialEval₂_tail_small f k l (ε / 8) hε8
  obtain ⟨C, hC⟩ := f.decay' 0 (l + 1)
  have hC_nonneg : 0 ≤ C := by
    have hC0 : ‖iteratedFDeriv ℝ (l + 1) (⇑f) (0, y₀)‖ ≤ C := by
      simpa using hC (0, y₀)
    exact le_trans (norm_nonneg _) hC0
  let A : ℝ := (max R 1) ^ k * C
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  let δ : ℝ := ε / (4 * (A + 1))
  have hδ_pos : 0 < δ := by
    dsimp [δ, A]
    positivity
  filter_upwards [Metric.ball_mem_nhds y₀ hδ_pos] with y hy
  have hy_lt : ‖y - y₀‖ < δ := by
    simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using hy
  rw [schwartzSeminormFamily_apply]
  have hsemi :
      SchwartzMap.seminorm ℝ k l
        (SchwartzMap.partialEval₂ f y - SchwartzMap.partialEval₂ f y₀) ≤ ε / 2 := by
    refine SchwartzMap.seminorm_le_bound ℝ k l
      (SchwartzMap.partialEval₂ f y - SchwartzMap.partialEval₂ f y₀) (by positivity) ?_
    intro x
    by_cases hx : R < ‖x‖
    · have hy_tail :
          ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun x' => f (x', y)) x‖ < ε / 8 :=
        htail y x hx
      have hy₀_tail :
          ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun x' => f (x', y₀)) x‖ < ε / 8 :=
        htail y₀ x hx
      have h_eval_y : (⇑(SchwartzMap.partialEval₂ f y) : E₁ → F) = fun x' => f (x', y) := rfl
      have h_eval_y₀ :
          (⇑(SchwartzMap.partialEval₂ f y₀) : E₁ → F) = fun x' => f (x', y₀) := rfl
      have hpoint :
          ‖x‖ ^ k *
              ‖iteratedFDeriv ℝ l
                  (⇑(SchwartzMap.partialEval₂ f y - SchwartzMap.partialEval₂ f y₀)) x‖ ≤
            ε / 4 := by
        have hpoint_lt :
            ‖x‖ ^ k *
                ‖iteratedFDeriv ℝ l
                    (⇑(SchwartzMap.partialEval₂ f y - SchwartzMap.partialEval₂ f y₀)) x‖ <
              ε / 4 := by
          calc
          ‖x‖ ^ k *
              ‖iteratedFDeriv ℝ l
                  (⇑(SchwartzMap.partialEval₂ f y - SchwartzMap.partialEval₂ f y₀)) x‖
            = ‖x‖ ^ k *
                ‖iteratedFDeriv ℝ l (fun x' => f (x', y)) x -
                  iteratedFDeriv ℝ l (fun x' => f (x', y₀)) x‖ := by
                  rw [iteratedFDeriv_sub_schwartz]
                  change
                    ‖x‖ ^ k *
                        ‖iteratedFDeriv ℝ l (fun x' => f (x', y)) x -
                          iteratedFDeriv ℝ l (fun x' => f (x', y₀)) x‖ =
                      ‖x‖ ^ k *
                        ‖iteratedFDeriv ℝ l (fun x' => f (x', y)) x -
                          iteratedFDeriv ℝ l (fun x' => f (x', y₀)) x‖
                  rfl
          _ ≤ ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun x' => f (x', y)) x‖ +
                ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun x' => f (x', y₀)) x‖ := by
                have hk_nonneg : 0 ≤ ‖x‖ ^ k := by positivity
                calc
                  ‖x‖ ^ k *
                      ‖iteratedFDeriv ℝ l (fun x' => f (x', y)) x -
                        iteratedFDeriv ℝ l (fun x' => f (x', y₀)) x‖
                    ≤ ‖x‖ ^ k *
                        (‖iteratedFDeriv ℝ l (fun x' => f (x', y)) x‖ +
                          ‖iteratedFDeriv ℝ l (fun x' => f (x', y₀)) x‖) := by
                            exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) hk_nonneg
                  _ = ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun x' => f (x', y)) x‖ +
                        ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun x' => f (x', y₀)) x‖ := by
                            ring
          _ < ε / 8 + ε / 8 := add_lt_add hy_tail hy₀_tail
          _ = ε / 4 := by ring
        exact hpoint_lt.le
      exact hpoint.trans (by linarith)
    · have hxR : ‖x‖ ≤ R := le_of_not_gt hx
      have hbound_diff :
          ‖iteratedFDeriv ℝ l (fun x' => f (x', y)) x -
              iteratedFDeriv ℝ l (fun x' => f (x', y₀)) x‖ ≤
            C * ‖y - y₀‖ := by
        let g :
            E₂ → ContinuousMultilinearMap ℝ (fun _ : Fin l => E₁) F :=
          fun y' => iteratedFDeriv ℝ l (fun x' => f (x', y')) x
        have hdiff :
            ∀ z : E₂, DifferentiableAt ℝ g z := by
          intro z
          exact (hasFDerivAt_iteratedFDeriv_partialEval₂ f l x z).differentiableAt
        have hbound :
            ∀ z : E₂, ‖fderiv ℝ g z‖ ≤ C := by
          intro z
          calc
            ‖fderiv ℝ g z‖
              ≤ ‖iteratedFDeriv ℝ (l + 1) (⇑f) (x, z)‖ := by
                  simpa [g] using norm_fderiv_iteratedFDeriv_partialEval₂_le f l x z
            _ ≤ C := by
                  simpa using hC (x, z)
        simpa [g] using
          (Convex.norm_image_sub_le_of_norm_fderiv_le
            (s := (Set.univ : Set E₂))
            (f := g)
            (x := y₀) (y := y)
            (fun z _ => hdiff z)
            (fun z _ => hbound z)
            convex_univ (by simp) (by simp))
      have hnormx :
          ‖x‖ ^ k ≤ (max R 1) ^ k := by
        have hxmax : ‖x‖ ≤ max R 1 := hxR.trans (le_max_left _ _)
        gcongr
      have h_eval_y : (⇑(SchwartzMap.partialEval₂ f y) : E₁ → F) = fun x' => f (x', y) := rfl
      have h_eval_y₀ :
          (⇑(SchwartzMap.partialEval₂ f y₀) : E₁ → F) = fun x' => f (x', y₀) := rfl
      have hpoint :
          ‖x‖ ^ k *
              ‖iteratedFDeriv ℝ l
                  (⇑(SchwartzMap.partialEval₂ f y - SchwartzMap.partialEval₂ f y₀)) x‖ ≤
            ε / 4 := by
        calc
          ‖x‖ ^ k *
              ‖iteratedFDeriv ℝ l
                  (⇑(SchwartzMap.partialEval₂ f y - SchwartzMap.partialEval₂ f y₀)) x‖
            = ‖x‖ ^ k *
                ‖iteratedFDeriv ℝ l (fun x' => f (x', y)) x -
                  iteratedFDeriv ℝ l (fun x' => f (x', y₀)) x‖ := by
                  rw [iteratedFDeriv_sub_schwartz]
                  change
                    ‖x‖ ^ k *
                        ‖iteratedFDeriv ℝ l (fun x' => f (x', y)) x -
                          iteratedFDeriv ℝ l (fun x' => f (x', y₀)) x‖ =
                      ‖x‖ ^ k *
                        ‖iteratedFDeriv ℝ l (fun x' => f (x', y)) x -
                          iteratedFDeriv ℝ l (fun x' => f (x', y₀)) x‖
                  rfl
          _ ≤ ‖x‖ ^ k * (C * ‖y - y₀‖) := by
                exact mul_le_mul_of_nonneg_left hbound_diff (by positivity)
          _ ≤ (max R 1) ^ k * (C * ‖y - y₀‖) := by
                exact mul_le_mul_of_nonneg_right hnormx (by positivity)
          _ = A * ‖y - y₀‖ := by
                simp [A, mul_assoc, mul_left_comm, mul_comm]
          _ ≤ A * δ := by
                exact mul_le_mul_of_nonneg_left hy_lt.le hA_nonneg
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

/-! ### Spacetime reindexing for partial evaluation -/

variable (d : ℕ)

/-- Split spacetime coordinates into time and spatial parts. -/
private def spacetimeSplitCLM :
    SpacetimeDim d →L[ℝ] ℝ × (Fin d → ℝ) where
  toFun x := (x 0, fun i => x i.succ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by
    continuity

/-- Join time and spatial parts into a spacetime vector. -/
private def spacetimeJoinCLM :
    (ℝ × (Fin d → ℝ)) →L[ℝ] SpacetimeDim d where
  toFun p := Fin.cons p.1 p.2
  map_add' _ _ := by
    ext μ
    refine Fin.cases ?_ ?_ μ
    · rfl
    · intro i
      rfl
  map_smul' _ _ := by
    ext μ
    refine Fin.cases ?_ ?_ μ
    · rfl
    · intro i
      rfl
  cont := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ ?_ i
    · exact continuous_fst
    · intro j
      exact (continuous_apply j).comp continuous_snd

/-- Continuous linear equivalence between spacetime coordinates and
`(time, spatial)` coordinates. -/
private def spacetimeSplitCLE :
    SpacetimeDim d ≃L[ℝ] ℝ × (Fin d → ℝ) :=
  ContinuousLinearEquiv.equivOfInverse
    (spacetimeSplitCLM d) (spacetimeJoinCLM d)
    (by
      intro x
      ext μ
      refine Fin.cases ?_ ?_ μ
      · rfl
      · intro i
        rfl)
    (by
      intro p
      ext <;> rfl)

/-- Reindex a spacetime Schwartz function as a Schwartz function in
`(time, spatial)` coordinates. -/
def spacetimeToTimeSpatialCLM :
    SchwartzSpacetime d →L[ℂ] SchwartzMap (ℝ × (Fin d → ℝ)) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (spacetimeSplitCLE d).symm

@[simp] theorem spacetimeToTimeSpatialCLM_apply
    (f : SchwartzSpacetime d) (t : ℝ) (y : Fin d → ℝ) :
    spacetimeToTimeSpatialCLM d f (t, y) = f (Fin.cons t y) := by
  simp [spacetimeToTimeSpatialCLM, spacetimeSplitCLE, spacetimeJoinCLM]

@[simp] theorem partialEval₂_spacetimeToTimeSpatialCLM_apply
    (f : SchwartzSpacetime d) (y : Fin d → ℝ) (t : ℝ) :
    SchwartzMap.partialEval₂ (spacetimeToTimeSpatialCLM d f) y t = f (Fin.cons t y) := by
  rfl

end OSReconstruction
