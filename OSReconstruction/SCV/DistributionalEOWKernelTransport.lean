/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.DistributionalEOWKernel
import OSReconstruction.SCV.HeadBlockDescent

/-!
# Transport Lemmas for the Local Distributional EOW Kernel Substrate

This file contains small QFT-free chart transport lemmas used to connect the
mixed complex/real fiber integral with ordinary head-block integration.  It is
kept separate from `DistributionalEOWKernel.lean` so the checked substrate file
does not keep growing.
-/

noncomputable section

open Complex MeasureTheory

namespace SCV

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pullback along a continuous linear equivalence is injective on Schwartz
functions. -/
theorem compCLMOfContinuousLinearEquiv_injective
    (e : E ≃L[ℝ] F) :
    Function.Injective
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e :
        SchwartzMap F ℂ →L[ℂ] SchwartzMap E ℂ) := by
  intro f g hfg
  ext y
  have hy := congrArg (fun H : SchwartzMap E ℂ => H (e.symm y)) hfg
  simpa [SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using hy

@[simp]
theorem compCLMOfContinuousLinearEquiv_symm_left_inv
    (e : E ≃L[ℝ] F) (f : SchwartzMap E ℂ) :
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e)
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm) f) = f := by
  ext x
  simp [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

@[simp]
theorem compCLMOfContinuousLinearEquiv_symm_right_inv
    (e : E ≃L[ℝ] F) (f : SchwartzMap F ℂ) :
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm)
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e) f) = f := by
  ext x
  simp [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

/-- The fiber-first mixed chart is exactly finite append of the real fiber and
the flattened complex coordinates. -/
theorem mixedChartFiberFirstCLE_apply_finAppend {m : ℕ}
    (z : ComplexChartSpace m) (t : Fin m → ℝ) :
    mixedChartFiberFirstCLE m (z, t) =
      Fin.append t (complexChartRealFlattenCLE m z) := by
  ext k
  refine Fin.addCases (motive := fun k =>
    mixedChartFiberFirstCLE m (z, t) k =
      Fin.append t (complexChartRealFlattenCLE m z) k) ?_ ?_ k
  · intro i
    simp
  · intro i
    let p := finProdFinEquiv.symm i
    have hi : i = finProdFinEquiv p := by
      simpa [p] using (finProdFinEquiv.apply_symm_apply i).symm
    rw [hi]
    rcases p with ⟨j, r⟩
    fin_cases r <;> simp

@[simp]
theorem mixedChartFiberFirstCLE_symm_finAppend {m : ℕ}
    (z : ComplexChartSpace m) (t : Fin m → ℝ) :
    (mixedChartFiberFirstCLE m).symm
      (Fin.append t (complexChartRealFlattenCLE m z)) = (z, t) := by
  apply (mixedChartFiberFirstCLE m).injective
  simp [mixedChartFiberFirstCLE_apply_finAppend]

/-- In the flat-to-mixed direction, ordinary head-block translation is exactly
mixed real-fiber translation. -/
theorem mixedChartFiberFirstCLE_translate_inv {m : ℕ} (a : Fin m → ℝ) :
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (mixedChartFiberFirstCLE m)).comp
      (translateSchwartzCLM (headBlockShift m (m * 2) a)) =
    (complexRealFiberTranslateSchwartzCLM a).comp
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (mixedChartFiberFirstCLE m)) := by
  ext H p
  rcases p with ⟨z, t⟩
  have hcoord :
      mixedChartFiberFirstCLE m (z, t) + headBlockShift m (m * 2) a =
        mixedChartFiberFirstCLE m (z, t + a) := by
    ext k
    refine Fin.addCases (motive := fun k =>
      (mixedChartFiberFirstCLE m (z, t) + headBlockShift m (m * 2) a) k =
        mixedChartFiberFirstCLE m (z, t + a) k) ?_ ?_ k
    · intro i
      simp
    · intro i
      let p := finProdFinEquiv.symm i
      have hi : i = finProdFinEquiv p := by
        simpa [p] using (finProdFinEquiv.apply_symm_apply i).symm
      rw [hi]
      rcases p with ⟨j, r⟩
      fin_cases r <;> simp
  simp [ContinuousLinearMap.comp_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    translateSchwartzCLM_apply, hcoord]

/-- The complex-real fiber integral is exactly ordinary head-block integration
after transporting the mixed chart to real fiber-first coordinates. -/
theorem complexRealFiberIntegral_eq_transport_integrateHeadBlock {m : ℕ}
    (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ) :
    complexRealFiberIntegral F =
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (complexChartRealFlattenCLE m))
        (integrateHeadBlock (m := m) (n := m * 2)
          ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (mixedChartFiberFirstCLE m).symm) F)) := by
  ext z
  simp [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    integrateHeadBlock_apply_finAppend,
    mixedChartFiberFirstCLE_symm_finAppend]

/-- The lifted Schwartz functional on the flat fiber-first chart. -/
private noncomputable def liftToFlatChart {m : ℕ}
    (T : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ) :
    SchwartzMap (Fin (m + m * 2) → ℝ) ℂ →L[ℂ] ℂ :=
  T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (mixedChartFiberFirstCLE m))

/-- The flat-chart representative of a mixed-chart Schwartz function. -/
private noncomputable def liftMixedToFlat {m : ℕ}
    (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ) :
    SchwartzMap (Fin (m + m * 2) → ℝ) ℂ :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (mixedChartFiberFirstCLE m).symm) F

private theorem liftToFlatChart_apply_liftMixedToFlat {m : ℕ}
    (T : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ)
    (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ) :
    liftToFlatChart T (liftMixedToFlat F) = T F := by
  show T ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (mixedChartFiberFirstCLE m))
        ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (mixedChartFiberFirstCLE m).symm) F)) = T F
  rw [compCLMOfContinuousLinearEquiv_symm_left_inv]

private theorem liftToFlatChart_headBlockTranslationInvariant {m : ℕ}
    (T : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ)
    (hT : IsComplexRealFiberTranslationInvariant T) :
    IsHeadBlockTranslationInvariantSchwartzCLM (m := m) (n := m * 2)
      (liftToFlatChart T) := by
  intro a
  have hbridge := mixedChartFiberFirstCLE_translate_inv (m := m) a
  show (T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (mixedChartFiberFirstCLE m))).comp
        (translateSchwartzCLM (headBlockShift m (m * 2) a)) =
      T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (mixedChartFiberFirstCLE m))
  calc
    (T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (mixedChartFiberFirstCLE m))).comp
          (translateSchwartzCLM (headBlockShift m (m * 2) a))
        = T.comp ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (mixedChartFiberFirstCLE m)).comp
            (translateSchwartzCLM (headBlockShift m (m * 2) a))) := by
            rw [ContinuousLinearMap.comp_assoc]
    _ = T.comp ((complexRealFiberTranslateSchwartzCLM a).comp
          (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (mixedChartFiberFirstCLE m))) := by
            rw [hbridge]
    _ = (T.comp (complexRealFiberTranslateSchwartzCLM a)).comp
          (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (mixedChartFiberFirstCLE m)) := by
            rw [← ContinuousLinearMap.comp_assoc]
    _ = T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (mixedChartFiberFirstCLE m)) := by
            rw [hT a]

private theorem integrateHeadBlock_liftMixedToFlat_eq_of_complexRealFiberIntegral_eq
    {m : ℕ}
    (F G : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ)
    (hFG : complexRealFiberIntegral F = complexRealFiberIntegral G) :
    integrateHeadBlock (m := m) (n := m * 2) (liftMixedToFlat F) =
      integrateHeadBlock (m := m) (n := m * 2) (liftMixedToFlat G) := by
  have hF :
      complexRealFiberIntegral F =
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (complexChartRealFlattenCLE m))
          (integrateHeadBlock (m := m) (n := m * 2) (liftMixedToFlat F)) := by
    show complexRealFiberIntegral F =
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (complexChartRealFlattenCLE m))
        (integrateHeadBlock (m := m) (n := m * 2)
          ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (mixedChartFiberFirstCLE m).symm) F))
    exact complexRealFiberIntegral_eq_transport_integrateHeadBlock F
  have hG :
      complexRealFiberIntegral G =
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (complexChartRealFlattenCLE m))
          (integrateHeadBlock (m := m) (n := m * 2) (liftMixedToFlat G)) := by
    show complexRealFiberIntegral G =
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (complexChartRealFlattenCLE m))
        (integrateHeadBlock (m := m) (n := m * 2)
          ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (mixedChartFiberFirstCLE m).symm) G))
    exact complexRealFiberIntegral_eq_transport_integrateHeadBlock G
  have hcombined :
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (complexChartRealFlattenCLE m))
        (integrateHeadBlock (m := m) (n := m * 2) (liftMixedToFlat F)) =
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (complexChartRealFlattenCLE m))
        (integrateHeadBlock (m := m) (n := m * 2) (liftMixedToFlat G)) := by
    rw [← hF, ← hG]
    exact hFG
  exact compCLMOfContinuousLinearEquiv_injective
    (complexChartRealFlattenCLE m) hcombined

/-- A fiber-translation-invariant Schwartz functional on the mixed chart
depends only on the complex-real fiber integral. -/
theorem map_eq_of_complexRealFiberIntegral_eq_of_fiberTranslationInvariant
    {m : ℕ}
    (T : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ)
    (hT : IsComplexRealFiberTranslationInvariant T)
    (F G : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ)
    (hFG : complexRealFiberIntegral F = complexRealFiberIntegral G) :
    T F = T G := by
  have h_descent :=
    map_eq_of_integrateHeadBlock_eq_of_headBlockTranslationInvariant_SCV
      (m := m) (n := m * 2)
      (T := liftToFlatChart T)
      (liftToFlatChart_headBlockTranslationInvariant T hT)
      (F := liftMixedToFlat F) (G := liftMixedToFlat G)
      (integrateHeadBlock_liftMixedToFlat_eq_of_complexRealFiberIntegral_eq
        F G hFG)
  rw [liftToFlatChart_apply_liftMixedToFlat,
    liftToFlatChart_apply_liftMixedToFlat] at h_descent
  exact h_descent

end SCV
