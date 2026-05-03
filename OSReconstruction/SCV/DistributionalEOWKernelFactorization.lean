/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.DistributionalEOWKernelTransport

/-!
# Mixed Fiber Factorization for Distributional EOW Kernels

This file contains the next QFT-free consumer of the mixed fiber quotient
theorem.  A fiber-translation-invariant mixed Schwartz functional descends
through `complexRealFiberIntegral`; after fixing a normalized real-fiber cutoff
`η`, the descended functional is realized by tensoring a complex-chart test
with `η`.
-/

noncomputable section

open Complex MeasureTheory

namespace SCV

/-- Product norm is controlled by the sum of the coordinate norms. -/
private theorem norm_prod_le_fst_add_snd
    {E₁ E₂ : Type*} [SeminormedAddCommGroup E₁] [SeminormedAddCommGroup E₂]
    (x : E₁ × E₂) :
    ‖x‖ ≤ ‖x.1‖ + ‖x.2‖ := by
  rw [Prod.norm_def]
  exact max_le (le_add_of_nonneg_right (norm_nonneg _))
    (le_add_of_nonneg_left (norm_nonneg _))

/-- Fixed-right mixed tensor product as a continuous linear map in the complex
chart argument. -/
def schwartzTensorProduct₂CLMRight {m : ℕ}
    (η : SchwartzMap (Fin m → ℝ) ℂ) :
    SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ]
      SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ := by
  refine SchwartzMap.mkCLM (𝕜 := ℂ)
    (fun φ p => φ p.1 * η p.2)
    (fun φ ψ p => by simp [add_mul])
    (fun c φ p => by simp [mul_assoc])
    (fun φ => φ.smooth'.fst'.mul η.smooth'.snd') ?_
  rintro ⟨k, l⟩
  let s : Finset (ℕ × ℕ) :=
    (Finset.range (l + 1)).image (fun i => ((k, i) : ℕ × ℕ)) ∪
      (Finset.range (l + 1)).image (fun i => ((0, i) : ℕ × ℕ))
  let C : ℝ :=
    (2 : ℝ) ^ k * ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
      (SchwartzMap.seminorm ℂ 0 (l - i) η +
        SchwartzMap.seminorm ℂ k (l - i) η)
  refine ⟨s, C, by positivity, fun φ x => ?_⟩
  have hφs := φ.smooth'.comp
    (ContinuousLinearMap.fst ℝ (ComplexChartSpace m) (Fin m → ℝ)).contDiff
  have hηs := η.smooth'.comp
    (ContinuousLinearMap.snd ℝ (ComplexChartSpace m) (Fin m → ℝ)).contDiff
  have hcf : ∀ j (x : ComplexChartSpace m × (Fin m → ℝ)),
      ‖iteratedFDeriv ℝ j (φ.toFun ∘ Prod.fst) x‖ ≤
        ‖iteratedFDeriv ℝ j φ.toFun x.1‖ := by
    intro j x
    rw [show φ.toFun ∘ Prod.fst =
        φ.toFun ∘ ⇑(ContinuousLinearMap.fst ℝ (ComplexChartSpace m) (Fin m → ℝ)) from rfl,
      (ContinuousLinearMap.fst ℝ (ComplexChartSpace m) (Fin m → ℝ)).iteratedFDeriv_comp_right
        φ.smooth' x (by exact_mod_cast le_top)]
    exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _)
        (Finset.prod_le_one (fun _ _ => norm_nonneg _)
          (fun _ _ =>
            ContinuousLinearMap.norm_fst_le ℝ (ComplexChartSpace m) (Fin m → ℝ))))
  have hcg : ∀ j (x : ComplexChartSpace m × (Fin m → ℝ)),
      ‖iteratedFDeriv ℝ j (η.toFun ∘ Prod.snd) x‖ ≤
        ‖iteratedFDeriv ℝ j η.toFun x.2‖ := by
    intro j x
    rw [show η.toFun ∘ Prod.snd =
        η.toFun ∘ ⇑(ContinuousLinearMap.snd ℝ (ComplexChartSpace m) (Fin m → ℝ)) from rfl,
      (ContinuousLinearMap.snd ℝ (ComplexChartSpace m) (Fin m → ℝ)).iteratedFDeriv_comp_right
        η.smooth' x (by exact_mod_cast le_top)]
    exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _)
        (Finset.prod_le_one (fun _ _ => norm_nonneg _)
          (fun _ _ =>
            ContinuousLinearMap.norm_snd_le ℝ (ComplexChartSpace m) (Fin m → ℝ))))
  have hLeib := norm_iteratedFDeriv_mul_le (n := l) hφs hηs x
    (WithTop.coe_le_coe.mpr (le_top (a := (l : ℕ∞))))
  have add_pow_le : (‖x.1‖ + ‖x.2‖) ^ k ≤
      (2 : ℝ) ^ k * (‖x.1‖ ^ k + ‖x.2‖ ^ k) := by
    have hmax : (max ‖x.1‖ ‖x.2‖) ^ k ≤ ‖x.1‖ ^ k + ‖x.2‖ ^ k := by
      rcases max_cases ‖x.1‖ ‖x.2‖ with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]; exact le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _)
      · rw [h]; exact le_add_of_nonneg_left (pow_nonneg (norm_nonneg _) _)
    have h_add_le_2max : ‖x.1‖ + ‖x.2‖ ≤ 2 * max ‖x.1‖ ‖x.2‖ := by
      linarith [le_max_left ‖x.1‖ ‖x.2‖, le_max_right ‖x.1‖ ‖x.2‖]
    calc
      (‖x.1‖ + ‖x.2‖) ^ k ≤ (2 * max ‖x.1‖ ‖x.2‖) ^ k :=
        pow_le_pow_left₀ (add_nonneg (norm_nonneg _) (norm_nonneg _)) h_add_le_2max _
      _ = (2 : ℝ) ^ k * (max ‖x.1‖ ‖x.2‖) ^ k := mul_pow (2 : ℝ) _ k
      _ ≤ (2 : ℝ) ^ k * (‖x.1‖ ^ k + ‖x.2‖ ^ k) :=
        mul_le_mul_of_nonneg_left hmax (pow_nonneg (by norm_num) _)
  have h_pow : ‖x‖ ^ k ≤ (2 : ℝ) ^ k * (‖x.1‖ ^ k + ‖x.2‖ ^ k) :=
    (pow_le_pow_left₀ (norm_nonneg _) (norm_prod_le_fst_add_snd x) _).trans add_pow_le
  have h_term : ∀ i ∈ Finset.range (l + 1),
      ‖x‖ ^ k * (↑(l.choose i) * ‖iteratedFDeriv ℝ i φ.toFun x.1‖ *
        ‖iteratedFDeriv ℝ (l - i) η.toFun x.2‖) ≤
      (2 : ℝ) ^ k * (↑(l.choose i) *
        (SchwartzMap.seminorm ℂ k i φ * SchwartzMap.seminorm ℂ 0 (l - i) η +
         SchwartzMap.seminorm ℂ 0 i φ * SchwartzMap.seminorm ℂ k (l - i) η)) := by
    intro i _
    set a := ‖x.1‖
    set b := ‖x.2‖
    set F := ‖iteratedFDeriv ℝ i φ.toFun x.1‖
    set G := ‖iteratedFDeriv ℝ (l - i) η.toFun x.2‖
    have ha_nn : 0 ≤ a := norm_nonneg _
    have hb_nn : 0 ≤ b := norm_nonneg _
    have hF_nn : 0 ≤ F := norm_nonneg _
    have hG_nn : 0 ≤ G := norm_nonneg _
    have hφ1 : a ^ k * F ≤ SchwartzMap.seminorm ℂ k i φ :=
      SchwartzMap.le_seminorm ℂ k i φ x.1
    have hη1 : G ≤ SchwartzMap.seminorm ℂ 0 (l - i) η := by
      have h := SchwartzMap.le_seminorm ℂ 0 (l - i) η x.2
      simp only [pow_zero, one_mul] at h
      exact h
    have hφ2 : F ≤ SchwartzMap.seminorm ℂ 0 i φ := by
      have h := SchwartzMap.le_seminorm ℂ 0 i φ x.1
      simp only [pow_zero, one_mul] at h
      exact h
    have hη2 : b ^ k * G ≤ SchwartzMap.seminorm ℂ k (l - i) η :=
      SchwartzMap.le_seminorm ℂ k (l - i) η x.2
    have hprod1 : a ^ k * F * G ≤
        SchwartzMap.seminorm ℂ k i φ * SchwartzMap.seminorm ℂ 0 (l - i) η :=
      mul_le_mul hφ1 hη1 hG_nn
        (le_trans (mul_nonneg (pow_nonneg ha_nn _) hF_nn) hφ1)
    have hprod2 : b ^ k * F * G ≤
        SchwartzMap.seminorm ℂ 0 i φ * SchwartzMap.seminorm ℂ k (l - i) η := by
      calc
        b ^ k * F * G = F * (b ^ k * G) := by ring
        _ ≤ SchwartzMap.seminorm ℂ 0 i φ * SchwartzMap.seminorm ℂ k (l - i) η :=
          mul_le_mul hφ2 hη2 (mul_nonneg (pow_nonneg hb_nn _) hG_nn)
            (le_trans hF_nn hφ2)
    have hchoose_nn : (0 : ℝ) ≤ ↑(l.choose i) := Nat.cast_nonneg _
    calc
      ‖x‖ ^ k * (↑(l.choose i) * F * G)
          ≤ ((2 : ℝ) ^ k * (a ^ k + b ^ k)) * (↑(l.choose i) * F * G) :=
        mul_le_mul_of_nonneg_right h_pow
          (mul_nonneg (mul_nonneg hchoose_nn hF_nn) hG_nn)
      _ = (2 : ℝ) ^ k * (↑(l.choose i) * (a ^ k * F * G + b ^ k * F * G)) := by
        ring
      _ ≤ (2 : ℝ) ^ k * (↑(l.choose i) *
          (SchwartzMap.seminorm ℂ k i φ * SchwartzMap.seminorm ℂ 0 (l - i) η +
           SchwartzMap.seminorm ℂ 0 i φ * SchwartzMap.seminorm ℂ k (l - i) η)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
        exact mul_le_mul_of_nonneg_left (add_le_add hprod1 hprod2) hchoose_nn
  have hraw :
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun y => φ y.1 * η y.2) x‖ ≤
      (2 : ℝ) ^ k * ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
        (SchwartzMap.seminorm ℂ k i φ * SchwartzMap.seminorm ℂ 0 (l - i) η +
         SchwartzMap.seminorm ℂ 0 i φ * SchwartzMap.seminorm ℂ k (l - i) η) := by
    calc
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun y => φ y.1 * η y.2) x‖
          ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (l + 1),
            ↑(l.choose i) * ‖iteratedFDeriv ℝ i (φ.toFun ∘ Prod.fst) x‖ *
            ‖iteratedFDeriv ℝ (l - i) (η.toFun ∘ Prod.snd) x‖ := by
        gcongr
        exact hLeib
      _ ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (l + 1),
            ↑(l.choose i) * ‖iteratedFDeriv ℝ i φ.toFun x.1‖ *
            ‖iteratedFDeriv ℝ (l - i) η.toFun x.2‖ := by
        gcongr with i hi
        · exact (hcf i x).trans le_rfl
        · exact (hcg (l - i) x).trans le_rfl
      _ = ∑ i ∈ Finset.range (l + 1),
            ‖x‖ ^ k * (↑(l.choose i) * ‖iteratedFDeriv ℝ i φ.toFun x.1‖ *
            ‖iteratedFDeriv ℝ (l - i) η.toFun x.2‖) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.range (l + 1),
          (2 : ℝ) ^ k * (↑(l.choose i) *
            (SchwartzMap.seminorm ℂ k i φ * SchwartzMap.seminorm ℂ 0 (l - i) η +
             SchwartzMap.seminorm ℂ 0 i φ * SchwartzMap.seminorm ℂ k (l - i) η)) :=
        Finset.sum_le_sum h_term
      _ = _ := by rw [← Finset.mul_sum]
  let S : ℝ := (s.sup (schwartzSeminormFamily ℂ (ComplexChartSpace m) ℂ)) φ
  have hsum :
      ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
        (SchwartzMap.seminorm ℂ k i φ * SchwartzMap.seminorm ℂ 0 (l - i) η +
         SchwartzMap.seminorm ℂ 0 i φ * SchwartzMap.seminorm ℂ k (l - i) η) ≤
      ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
        ((SchwartzMap.seminorm ℂ 0 (l - i) η +
          SchwartzMap.seminorm ℂ k (l - i) η) * S) := by
    apply Finset.sum_le_sum
    intro i hi
    have hchoose_nonneg : (0 : ℝ) ≤ ↑(l.choose i) := Nat.cast_nonneg _
    have hη0_nonneg : 0 ≤ SchwartzMap.seminorm ℂ 0 (l - i) η := apply_nonneg _ _
    have hηk_nonneg : 0 ≤ SchwartzMap.seminorm ℂ k (l - i) η := apply_nonneg _ _
    have hφk_le : SchwartzMap.seminorm ℂ k i φ ≤ S := by
      have hmem : ((k, i) : ℕ × ℕ) ∈ s :=
        Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      exact (show
        (schwartzSeminormFamily ℂ (ComplexChartSpace m) ℂ ((k, i) : ℕ × ℕ)) φ ≤
          (s.sup (schwartzSeminormFamily ℂ (ComplexChartSpace m) ℂ)) φ from
        (Finset.le_sup (f := schwartzSeminormFamily ℂ (ComplexChartSpace m) ℂ) hmem) φ)
    have hφ0_le : SchwartzMap.seminorm ℂ 0 i φ ≤ S := by
      have hmem : ((0, i) : ℕ × ℕ) ∈ s :=
        Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      exact (show
        (schwartzSeminormFamily ℂ (ComplexChartSpace m) ℂ ((0, i) : ℕ × ℕ)) φ ≤
          (s.sup (schwartzSeminormFamily ℂ (ComplexChartSpace m) ℂ)) φ from
        (Finset.le_sup (f := schwartzSeminormFamily ℂ (ComplexChartSpace m) ℂ) hmem) φ)
    calc
      ↑(l.choose i) *
          (SchwartzMap.seminorm ℂ k i φ * SchwartzMap.seminorm ℂ 0 (l - i) η +
           SchwartzMap.seminorm ℂ 0 i φ * SchwartzMap.seminorm ℂ k (l - i) η)
          ≤ ↑(l.choose i) *
            (S * SchwartzMap.seminorm ℂ 0 (l - i) η +
             S * SchwartzMap.seminorm ℂ k (l - i) η) := by
        gcongr
      _ = ↑(l.choose i) *
          ((SchwartzMap.seminorm ℂ 0 (l - i) η +
            SchwartzMap.seminorm ℂ k (l - i) η) * S) := by
        ring
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun y => φ y.1 * η y.2) x‖
        ≤ (2 : ℝ) ^ k * ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
          (SchwartzMap.seminorm ℂ k i φ * SchwartzMap.seminorm ℂ 0 (l - i) η +
           SchwartzMap.seminorm ℂ 0 i φ * SchwartzMap.seminorm ℂ k (l - i) η) := hraw
    _ ≤ (2 : ℝ) ^ k * ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
          ((SchwartzMap.seminorm ℂ 0 (l - i) η +
            SchwartzMap.seminorm ℂ k (l - i) η) * S) :=
      mul_le_mul_of_nonneg_left hsum (pow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ k *
        ((∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
          (SchwartzMap.seminorm ℂ 0 (l - i) η +
            SchwartzMap.seminorm ℂ k (l - i) η)) * S) := by
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = C * S := by
      simp [C, mul_assoc]

@[simp]
theorem schwartzTensorProduct₂CLMRight_apply {m : ℕ}
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (z : ComplexChartSpace m) (t : Fin m → ℝ) :
    schwartzTensorProduct₂CLMRight η φ (z, t) = φ z * η t := rfl

theorem schwartzTensorProduct₂CLMRight_eq {m : ℕ}
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
    schwartzTensorProduct₂CLMRight η φ =
      schwartzTensorProduct₂ φ η := by
  ext p
  rfl

/-- The explicit quotient functional obtained from a mixed functional by
testing against a fixed real-fiber cutoff. -/
def complexRealFiberTranslationDescentCLM {m : ℕ}
    (T : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ)
    (η : SchwartzMap (Fin m → ℝ) ℂ) :
    SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ] ℂ :=
  T.comp (schwartzTensorProduct₂CLMRight η)

@[simp]
theorem complexRealFiberTranslationDescentCLM_apply {m : ℕ}
    (T : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ)
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
    complexRealFiberTranslationDescentCLM T η φ =
      T (schwartzTensorProduct₂CLMRight η φ) := rfl

/-- A fiber-translation-invariant mixed Schwartz functional factors through
`complexRealFiberIntegral`; a normalized real-fiber cutoff gives the explicit
descended continuous linear functional. -/
theorem map_eq_complexRealFiberTranslationDescentCLM_of_fiberTranslationInvariant {m : ℕ}
    (T : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ)
    (hT : IsComplexRealFiberTranslationInvariant T)
    (η : SchwartzMap (Fin m → ℝ) ℂ)
    (hη : ∫ t : Fin m → ℝ, η t = 1)
    (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ) :
    T F =
      complexRealFiberTranslationDescentCLM T η
        (complexRealFiberIntegral F) := by
  let G := schwartzTensorProduct₂ (complexRealFiberIntegral F) η
  have hFG : complexRealFiberIntegral F = complexRealFiberIntegral G := by
    change complexRealFiberIntegral F =
      complexRealFiberIntegral (schwartzTensorProduct₂ (complexRealFiberIntegral F) η)
    rw [complexRealFiberIntegral_schwartzTensorProduct₂, hη, one_smul]
  have hquot :
      T F = T G :=
    map_eq_of_complexRealFiberIntegral_eq_of_fiberTranslationInvariant T hT F G hFG
  calc
    T F = T G := hquot
    _ = complexRealFiberTranslationDescentCLM T η
        (complexRealFiberIntegral F) := by
      simp [complexRealFiberTranslationDescentCLM, G, schwartzTensorProduct₂CLMRight_eq]

end SCV
