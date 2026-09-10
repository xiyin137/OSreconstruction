/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# External Products of Schwartz Functions

This file exposes the elementary but important construction
`(x, y) ↦ φ x * ψ y` as a Schwartz function on a Cartesian product.  It is
kept QFT-free and is used by the theorem-2 product-density route to build flat
two-block product tests.
-/

noncomputable section

open Complex

namespace SCV

/-- Product norm is controlled by the sum of the coordinate norms. -/
private theorem norm_prod_le_fst_add_snd
    {E₁ E₂ : Type*} [SeminormedAddCommGroup E₁] [SeminormedAddCommGroup E₂]
    (x : E₁ × E₂) :
    ‖x‖ ≤ ‖x.1‖ + ‖x.2‖ := by
  rw [Prod.norm_def]
  exact max_le (le_add_of_nonneg_right (norm_nonneg _))
    (le_add_of_nonneg_left (norm_nonneg _))

/-- The external product of two complex-valued Schwartz functions. -/
def schwartzExternalProduct
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    (φ : SchwartzMap E₁ ℂ) (ψ : SchwartzMap E₂ ℂ) :
    SchwartzMap (E₁ × E₂) ℂ where
  toFun := fun p => φ p.1 * ψ p.2
  smooth' := by
    exact φ.smooth'.fst'.mul ψ.smooth'.snd'
  decay' := by
    intro p l
    refine ⟨2 ^ p * ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
      (SchwartzMap.seminorm ℂ p i φ * SchwartzMap.seminorm ℂ 0 (l - i) ψ +
       SchwartzMap.seminorm ℂ 0 i φ * SchwartzMap.seminorm ℂ p (l - i) ψ), fun x => ?_⟩
    have hφs := φ.smooth'.comp (ContinuousLinearMap.fst ℝ E₁ E₂).contDiff
    have hψs := ψ.smooth'.comp (ContinuousLinearMap.snd ℝ E₁ E₂).contDiff
    have hcf : ∀ j (x : E₁ × E₂),
        ‖iteratedFDeriv ℝ j (φ.toFun ∘ Prod.fst) x‖ ≤
          ‖iteratedFDeriv ℝ j φ.toFun x.1‖ := by
      intro j x
      rw [show φ.toFun ∘ Prod.fst =
          φ.toFun ∘ ⇑(ContinuousLinearMap.fst ℝ E₁ E₂) from rfl,
        (ContinuousLinearMap.fst ℝ E₁ E₂).iteratedFDeriv_comp_right φ.smooth' x
          (by exact_mod_cast le_top)]
      exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _)
          (Finset.prod_le_one (fun _ _ => norm_nonneg _)
            (fun _ _ => ContinuousLinearMap.norm_fst_le ℝ E₁ E₂)))
    have hcg : ∀ j (x : E₁ × E₂),
        ‖iteratedFDeriv ℝ j (ψ.toFun ∘ Prod.snd) x‖ ≤
          ‖iteratedFDeriv ℝ j ψ.toFun x.2‖ := by
      intro j x
      rw [show ψ.toFun ∘ Prod.snd =
          ψ.toFun ∘ ⇑(ContinuousLinearMap.snd ℝ E₁ E₂) from rfl,
        (ContinuousLinearMap.snd ℝ E₁ E₂).iteratedFDeriv_comp_right ψ.smooth' x
          (by exact_mod_cast le_top)]
      exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _)
          (Finset.prod_le_one (fun _ _ => norm_nonneg _)
            (fun _ _ => ContinuousLinearMap.norm_snd_le ℝ E₁ E₂)))
    have hLeib := norm_iteratedFDeriv_mul_le (n := l) hφs hψs x
      (WithTop.coe_le_coe.mpr (le_top (a := (l : ℕ∞))))
    have add_pow_le : (‖x.1‖ + ‖x.2‖) ^ p ≤
        2 ^ p * (‖x.1‖ ^ p + ‖x.2‖ ^ p) := by
      have hmax : (max ‖x.1‖ ‖x.2‖) ^ p ≤ ‖x.1‖ ^ p + ‖x.2‖ ^ p := by
        rcases max_cases ‖x.1‖ ‖x.2‖ with ⟨h, _⟩ | ⟨h, _⟩
        · rw [h]; exact le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _)
        · rw [h]; exact le_add_of_nonneg_left (pow_nonneg (norm_nonneg _) _)
      have h_add_le_2max : ‖x.1‖ + ‖x.2‖ ≤ 2 * max ‖x.1‖ ‖x.2‖ := by
        linarith [le_max_left ‖x.1‖ ‖x.2‖, le_max_right ‖x.1‖ ‖x.2‖]
      calc
        (‖x.1‖ + ‖x.2‖) ^ p ≤ (2 * max ‖x.1‖ ‖x.2‖) ^ p :=
          pow_le_pow_left₀ (add_nonneg (norm_nonneg _) (norm_nonneg _)) h_add_le_2max _
        _ = (2 : ℝ) ^ p * (max ‖x.1‖ ‖x.2‖) ^ p := mul_pow (2 : ℝ) _ p
        _ ≤ 2 ^ p * (‖x.1‖ ^ p + ‖x.2‖ ^ p) :=
          mul_le_mul_of_nonneg_left hmax (pow_nonneg (by norm_num) _)
    have h_pow : ‖x‖ ^ p ≤ 2 ^ p * (‖x.1‖ ^ p + ‖x.2‖ ^ p) :=
      (pow_le_pow_left₀ (norm_nonneg _) (norm_prod_le_fst_add_snd x) _).trans add_pow_le
    have h_term : ∀ i ∈ Finset.range (l + 1),
        ‖x‖ ^ p * (↑(l.choose i) * ‖iteratedFDeriv ℝ i φ.toFun x.1‖ *
          ‖iteratedFDeriv ℝ (l - i) ψ.toFun x.2‖) ≤
        2 ^ p * (↑(l.choose i) *
          (SchwartzMap.seminorm ℂ p i φ * SchwartzMap.seminorm ℂ 0 (l - i) ψ +
           SchwartzMap.seminorm ℂ 0 i φ * SchwartzMap.seminorm ℂ p (l - i) ψ)) := by
      intro i _
      set a := ‖x.1‖
      set b := ‖x.2‖
      set F := ‖iteratedFDeriv ℝ i φ.toFun x.1‖
      set G := ‖iteratedFDeriv ℝ (l - i) ψ.toFun x.2‖
      have ha_nn : 0 ≤ a := norm_nonneg _
      have hb_nn : 0 ≤ b := norm_nonneg _
      have hF_nn : 0 ≤ F := norm_nonneg _
      have hG_nn : 0 ≤ G := norm_nonneg _
      have hf1 : a ^ p * F ≤ SchwartzMap.seminorm ℂ p i φ :=
        SchwartzMap.le_seminorm ℂ p i φ x.1
      have hg1 : G ≤ SchwartzMap.seminorm ℂ 0 (l - i) ψ := by
        have h := SchwartzMap.le_seminorm ℂ 0 (l - i) ψ x.2
        simp only [pow_zero, one_mul] at h
        exact h
      have hf2 : F ≤ SchwartzMap.seminorm ℂ 0 i φ := by
        have h := SchwartzMap.le_seminorm ℂ 0 i φ x.1
        simp only [pow_zero, one_mul] at h
        exact h
      have hg2 : b ^ p * G ≤ SchwartzMap.seminorm ℂ p (l - i) ψ :=
        SchwartzMap.le_seminorm ℂ p (l - i) ψ x.2
      have hprod1 : a ^ p * F * G ≤
          SchwartzMap.seminorm ℂ p i φ * SchwartzMap.seminorm ℂ 0 (l - i) ψ :=
        mul_le_mul hf1 hg1 hG_nn
          (le_trans (mul_nonneg (pow_nonneg ha_nn _) hF_nn) hf1)
      have hprod2 : b ^ p * F * G ≤
          SchwartzMap.seminorm ℂ 0 i φ * SchwartzMap.seminorm ℂ p (l - i) ψ := by
        calc
          b ^ p * F * G = F * (b ^ p * G) := by ring
          _ ≤ SchwartzMap.seminorm ℂ 0 i φ * SchwartzMap.seminorm ℂ p (l - i) ψ :=
            mul_le_mul hf2 hg2 (mul_nonneg (pow_nonneg hb_nn _) hG_nn)
              (le_trans hF_nn hf2)
      have hchoose_nn : (0 : ℝ) ≤ ↑(l.choose i) := Nat.cast_nonneg _
      calc
        ‖x‖ ^ p * (↑(l.choose i) * F * G)
            ≤ (2 ^ p * (a ^ p + b ^ p)) * (↑(l.choose i) * F * G) :=
          mul_le_mul_of_nonneg_right h_pow
            (mul_nonneg (mul_nonneg hchoose_nn hF_nn) hG_nn)
        _ = 2 ^ p * (↑(l.choose i) * (a ^ p * F * G + b ^ p * F * G)) := by ring
        _ ≤ 2 ^ p * (↑(l.choose i) *
            (SchwartzMap.seminorm ℂ p i φ * SchwartzMap.seminorm ℂ 0 (l - i) ψ +
             SchwartzMap.seminorm ℂ 0 i φ * SchwartzMap.seminorm ℂ p (l - i) ψ)) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
          exact mul_le_mul_of_nonneg_left (add_le_add hprod1 hprod2) hchoose_nn
    calc
      ‖x‖ ^ p * ‖iteratedFDeriv ℝ l
          (fun y : E₁ × E₂ => φ y.1 * ψ y.2) x‖
          ≤ ‖x‖ ^ p * ∑ i ∈ Finset.range (l + 1),
            ↑(l.choose i) * ‖iteratedFDeriv ℝ i (φ.toFun ∘ Prod.fst) x‖ *
            ‖iteratedFDeriv ℝ (l - i) (ψ.toFun ∘ Prod.snd) x‖ := by
        gcongr
        exact hLeib
      _ ≤ ‖x‖ ^ p * ∑ i ∈ Finset.range (l + 1),
            ↑(l.choose i) * ‖iteratedFDeriv ℝ i φ.toFun x.1‖ *
            ‖iteratedFDeriv ℝ (l - i) ψ.toFun x.2‖ := by
        gcongr with i hi
        · exact (hcf i x).trans le_rfl
        · exact (hcg (l - i) x).trans le_rfl
      _ = ∑ i ∈ Finset.range (l + 1),
            ‖x‖ ^ p * (↑(l.choose i) * ‖iteratedFDeriv ℝ i φ.toFun x.1‖ *
            ‖iteratedFDeriv ℝ (l - i) ψ.toFun x.2‖) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.range (l + 1),
          2 ^ p * (↑(l.choose i) *
            (SchwartzMap.seminorm ℂ p i φ * SchwartzMap.seminorm ℂ 0 (l - i) ψ +
             SchwartzMap.seminorm ℂ 0 i φ * SchwartzMap.seminorm ℂ p (l - i) ψ)) :=
        Finset.sum_le_sum h_term
      _ = _ := by rw [← Finset.mul_sum]

@[simp]
theorem schwartzExternalProduct_apply
    {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    (φ : SchwartzMap E₁ ℂ) (ψ : SchwartzMap E₂ ℂ)
    (x : E₁) (y : E₂) :
    schwartzExternalProduct φ ψ (x, y) = φ x * ψ y := by
  rfl

end SCV
