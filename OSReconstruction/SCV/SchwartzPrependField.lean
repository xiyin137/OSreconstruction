/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import OSReconstruction.Mathlib429Compat
import OSReconstruction.SCV.DistributionalEOWKernel

/-!
# Fixed-head prepend products for real-coordinate Schwartz spaces

This file extracts the QFT-free product-coordinate infrastructure needed by
the theorem-2 head-block descent route.  It deliberately uses `SCV.*` names:
the older Wightman tensor source already defines global `tailCLM` and
`SchwartzMap.prependField`, and SCV must not import or collide with that file.
-/

noncomputable section

open scoped SchwartzMap
open Complex

namespace SCV

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- The tail projection as a continuous linear map:
`x ↦ (x₁,...,xₙ)` from `Fin (n+1) → ℝ`. -/
noncomputable def tailCLM (n : ℕ) :
    (Fin (n + 1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.proj (R := ℝ) (ι := Fin (n + 1)) (φ := fun _ => ℝ) i.succ

@[simp]
theorem tailCLM_apply (n : ℕ) (x : Fin (n + 1) → ℝ) :
    tailCLM n x = fun i => x i.succ := rfl

/-- The tail projection has operator norm at most one. -/
theorem tailCLM_opNorm_le (n : ℕ) :
    ‖tailCLM n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [tailCLM_apply, one_mul]
    simp only [Pi.norm_def]
    exact_mod_cast Finset.sup_le fun b _ =>
      Finset.le_sup (f := fun j => ‖x j‖₊) (Finset.mem_univ (Fin.succ b))

/-- The pi norm of `x : Fin (n+1) → ℝ` is bounded by head norm plus tail norm. -/
theorem norm_le_head_add_tail (n : ℕ) (x : Fin (n + 1) → ℝ) :
    ‖x‖ ≤ ‖x 0‖ + ‖fun i : Fin n => x i.succ‖ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  refine Fin.cases ?_ (fun i => ?_)
  · exact le_add_of_nonneg_right (norm_nonneg _)
  · exact (norm_le_pi_norm (fun i : Fin n => x i.succ) i).trans
      (le_add_of_nonneg_left (norm_nonneg _))

/-- Prepend a one-dimensional real-coordinate Schwartz test to a tail test:
`(prependField f g)(x₀,x₁,...,xₙ) = f x₀ * g(x₁,...,xₙ)`. -/
def prependField {n : ℕ}
    (f : 𝓢(ℝ, ℂ)) (g : 𝓢(Fin n → ℝ, ℂ)) :
    𝓢(Fin (n + 1) → ℝ, ℂ) where
  toFun := fun x => f (x 0) * g (fun i => x i.succ)
  smooth' := by
    apply ContDiff.mul
    · exact f.smooth'.comp
        (ContinuousLinearMap.proj (R := ℝ) (ι := Fin (n + 1)) (φ := fun _ => ℝ) 0).contDiff
    · exact g.smooth'.comp (tailCLM n).contDiff
  decay' := by
    intro p l
    let headCLM :=
      ContinuousLinearMap.proj (R := ℝ) (ι := Fin (n + 1)) (φ := fun _ => ℝ) 0
    have hfs := f.smooth'.comp headCLM.contDiff
    have hgs := g.smooth'.comp (tailCLM n).contDiff
    have headCLM_norm_le : ‖headCLM‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one
        (fun x => by rw [one_mul]; exact norm_le_pi_norm x 0)
    have hcf : ∀ j (x : Fin (n + 1) → ℝ),
        ‖iteratedFDeriv ℝ j (f.toFun ∘ fun x => x 0) x‖ ≤
        ‖iteratedFDeriv ℝ j f.toFun (x 0)‖ := by
      intro j x
      rw [show (f.toFun ∘ fun x => x 0) = f.toFun ∘ ⇑headCLM from rfl,
        headCLM.iteratedFDeriv_comp_right f.smooth' x (by exact_mod_cast le_top)]
      exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _)
          (Finset.prod_le_one (fun _ _ => norm_nonneg _)
            (fun _ _ => headCLM_norm_le)))
    have hcg : ∀ j (x : Fin (n + 1) → ℝ),
        ‖iteratedFDeriv ℝ j (g.toFun ∘ fun x => fun i => x i.succ) x‖ ≤
        ‖iteratedFDeriv ℝ j g.toFun (fun i => x i.succ)‖ := by
      intro j x
      rw [show (g.toFun ∘ fun x => fun i => x i.succ) =
            g.toFun ∘ ⇑(tailCLM n) from rfl,
        (tailCLM n).iteratedFDeriv_comp_right g.smooth' x (by exact_mod_cast le_top)]
      exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _)
          (Finset.prod_le_one (fun _ _ => norm_nonneg _)
            (fun _ _ => tailCLM_opNorm_le n)))
    choose Cf hCf using fun p j => f.decay' p j
    choose Cg hCg using fun p j => g.decay' p j
    refine ⟨(2 : ℝ) ^ p * ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
      (Cf p i * Cg 0 (l - i) + Cf 0 i * Cg p (l - i)), fun x => ?_⟩
    have hLeib := norm_iteratedFDeriv_mul_le (n := l) hfs hgs x
      (WithTop.coe_le_coe.mpr (le_top (a := (l : ℕ∞))))
    have hnorm_split := norm_le_head_add_tail n x
    have h_add_le_2max : ‖x 0‖ + ‖fun i : Fin n => x i.succ‖ ≤
        2 * max ‖x 0‖ ‖fun i : Fin n => x i.succ‖ := by
      linarith [le_max_left ‖x 0‖ ‖fun i : Fin n => x i.succ‖,
                le_max_right ‖x 0‖ ‖fun i : Fin n => x i.succ‖]
    have add_pow_le : (‖x 0‖ + ‖fun i : Fin n => x i.succ‖) ^ p ≤
        (2 : ℝ) ^ p * (‖x 0‖ ^ p + ‖fun i : Fin n => x i.succ‖ ^ p) := by
      have hmax : (max ‖x 0‖ ‖fun i : Fin n => x i.succ‖) ^ p ≤
          ‖x 0‖ ^ p + ‖fun i : Fin n => x i.succ‖ ^ p := by
        rcases max_cases ‖x 0‖ ‖fun i : Fin n => x i.succ‖ with ⟨h, _⟩ | ⟨h, _⟩
        · rw [h]; exact le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _)
        · rw [h]; exact le_add_of_nonneg_left (pow_nonneg (norm_nonneg _) _)
      calc _ ≤ (2 * max ‖x 0‖ ‖fun i : Fin n => x i.succ‖) ^ p :=
            pow_le_pow_left₀ (add_nonneg (norm_nonneg _) (norm_nonneg _)) h_add_le_2max _
        _ = (2 : ℝ) ^ p * (max ‖x 0‖ ‖fun i : Fin n => x i.succ‖) ^ p :=
            mul_pow (2 : ℝ) _ p
        _ ≤ (2 : ℝ) ^ p * (‖x 0‖ ^ p + ‖fun i : Fin n => x i.succ‖ ^ p) :=
            mul_le_mul_of_nonneg_left hmax (pow_nonneg (by norm_num) _)
    have h_pow : ‖x‖ ^ p ≤ (2 : ℝ) ^ p *
        (‖x 0‖ ^ p + ‖fun i : Fin n => x i.succ‖ ^ p) :=
      (pow_le_pow_left₀ (norm_nonneg _) hnorm_split _).trans add_pow_le
    have h_term : ∀ i ∈ Finset.range (l + 1),
        ‖x‖ ^ p * (↑(l.choose i) * ‖iteratedFDeriv ℝ i f.toFun (x 0)‖ *
        ‖iteratedFDeriv ℝ (l - i) g.toFun (fun j => x j.succ)‖) ≤
        (2 : ℝ) ^ p * (↑(l.choose i) *
          (Cf p i * Cg 0 (l - i) + Cf 0 i * Cg p (l - i))) := by
      intro i _
      set a := ‖x 0‖ with ha_def
      set b := ‖fun j : Fin n => x j.succ‖ with hb_def
      set F := ‖iteratedFDeriv ℝ i f.toFun (x 0)‖ with hF_def
      set G := ‖iteratedFDeriv ℝ (l - i) g.toFun (fun j => x j.succ)‖ with hG_def
      have ha_nn : 0 ≤ a := norm_nonneg _
      have hb_nn : 0 ≤ b := norm_nonneg _
      have hF_nn : 0 ≤ F := norm_nonneg _
      have hG_nn : 0 ≤ G := norm_nonneg _
      have hf1 : a ^ p * F ≤ Cf p i := hCf p i (x 0)
      have hg1 : G ≤ Cg 0 (l - i) := by
        have := hCg 0 (l - i) (fun j => x j.succ)
        simp at this
        linarith
      have hf2 : F ≤ Cf 0 i := by
        have := hCf 0 i (x 0)
        simp at this
        linarith
      have hg2 : b ^ p * G ≤ Cg p (l - i) := hCg p (l - i) (fun j => x j.succ)
      have hprod1 : a ^ p * F * G ≤ Cf p i * Cg 0 (l - i) :=
        mul_le_mul hf1 hg1 hG_nn (le_trans (mul_nonneg (pow_nonneg ha_nn _) hF_nn) hf1)
      have hprod2 : b ^ p * F * G ≤ Cf 0 i * Cg p (l - i) := by
        calc b ^ p * F * G = F * (b ^ p * G) := by ring
          _ ≤ Cf 0 i * Cg p (l - i) :=
            mul_le_mul hf2 hg2 (mul_nonneg (pow_nonneg hb_nn _) hG_nn)
              (le_trans hF_nn hf2)
      have hchoose_nn : (0 : ℝ) ≤ ↑(l.choose i) := Nat.cast_nonneg _
      calc ‖x‖ ^ p * (↑(l.choose i) * F * G)
          ≤ ((2 : ℝ) ^ p * (a ^ p + b ^ p)) * (↑(l.choose i) * F * G) :=
            mul_le_mul_of_nonneg_right h_pow
              (mul_nonneg (mul_nonneg hchoose_nn hF_nn) hG_nn)
        _ = (2 : ℝ) ^ p * (↑(l.choose i) * (a ^ p * F * G + b ^ p * F * G)) := by
            ring
        _ ≤ (2 : ℝ) ^ p *
            (↑(l.choose i) * (Cf p i * Cg 0 (l - i) + Cf 0 i * Cg p (l - i))) := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
            exact mul_le_mul_of_nonneg_left (add_le_add hprod1 hprod2) hchoose_nn
    calc ‖x‖ ^ p * ‖iteratedFDeriv ℝ l
          (fun y => f (y 0) * g (fun i => y i.succ)) x‖
        ≤ ‖x‖ ^ p * ∑ i ∈ Finset.range (l + 1),
          ↑(l.choose i) * ‖iteratedFDeriv ℝ i (f.toFun ∘ fun y => y 0) x‖ *
          ‖iteratedFDeriv ℝ (l - i) (g.toFun ∘ fun y => fun j => y j.succ) x‖ := by
          gcongr
          exact hLeib
      _ ≤ ‖x‖ ^ p * ∑ i ∈ Finset.range (l + 1),
          ↑(l.choose i) * ‖iteratedFDeriv ℝ i f.toFun (x 0)‖ *
          ‖iteratedFDeriv ℝ (l - i) g.toFun (fun j => x j.succ)‖ := by
          gcongr with i hi
          · exact (hcf i x).trans le_rfl
          · exact (hcg (l - i) x).trans le_rfl
      _ = ∑ i ∈ Finset.range (l + 1),
          ‖x‖ ^ p * (↑(l.choose i) * ‖iteratedFDeriv ℝ i f.toFun (x 0)‖ *
          ‖iteratedFDeriv ℝ (l - i) g.toFun (fun j => x j.succ)‖) := by
          rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.range (l + 1),
          (2 : ℝ) ^ p * (↑(l.choose i) *
            (Cf p i * Cg 0 (l - i) + Cf 0 i * Cg p (l - i))) := by
          exact Finset.sum_le_sum h_term
      _ = _ := by rw [← Finset.mul_sum]

@[simp]
theorem prependField_apply {n : ℕ}
    (f : 𝓢(ℝ, ℂ)) (g : 𝓢(Fin n → ℝ, ℂ)) (x : Fin (n + 1) → ℝ) :
    prependField f g x = f (x 0) * g (fun i => x i.succ) := rfl

theorem prependField_add_right {n : ℕ}
    (f : 𝓢(ℝ, ℂ)) (g₁ g₂ : 𝓢(Fin n → ℝ, ℂ)) :
    prependField f (g₁ + g₂) = prependField f g₁ + prependField f g₂ := by
  ext x
  simp [mul_add]

theorem prependField_sub_right {n : ℕ}
    (f : 𝓢(ℝ, ℂ)) (g₁ g₂ : 𝓢(Fin n → ℝ, ℂ)) :
    prependField f (g₁ - g₂) = prependField f g₁ - prependField f g₂ := by
  ext x
  simp [mul_sub]

theorem prependField_smul_right {n : ℕ}
    (f : 𝓢(ℝ, ℂ)) (c : ℂ) (g : 𝓢(Fin n → ℝ, ℂ)) :
    prependField f (c • g) = c • prependField f g := by
  ext x
  simp [mul_left_comm]

/-- Fixed-head prepend product seminorm estimate. -/
theorem prependField_seminorm_le {n : ℕ}
    (f : 𝓢(ℝ, ℂ)) (g : 𝓢(Fin n → ℝ, ℂ)) (p l : ℕ) :
    SchwartzMap.seminorm ℝ p l (prependField f g) ≤
      (2 : ℝ) ^ p * ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
        (SchwartzMap.seminorm ℝ p i f * SchwartzMap.seminorm ℝ 0 (l - i) g +
         SchwartzMap.seminorm ℝ 0 i f * SchwartzMap.seminorm ℝ p (l - i) g) := by
  apply SchwartzMap.seminorm_le_bound ℝ p l _ (by positivity)
  intro x
  let headCLM :=
    ContinuousLinearMap.proj (R := ℝ) (ι := Fin (n + 1)) (φ := fun _ => ℝ) 0
  have hfs := f.smooth'.comp headCLM.contDiff
  have hgs := g.smooth'.comp (tailCLM n).contDiff
  have headCLM_norm_le : ‖headCLM‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      (fun x => by rw [one_mul]; exact norm_le_pi_norm x 0)
  have hcf : ∀ j (x : Fin (n + 1) → ℝ),
      ‖iteratedFDeriv ℝ j (f.toFun ∘ fun x => x 0) x‖ ≤
      ‖iteratedFDeriv ℝ j f.toFun (x 0)‖ := by
    intro j x
    rw [show (f.toFun ∘ fun x => x 0) = f.toFun ∘ ⇑headCLM from rfl,
      headCLM.iteratedFDeriv_comp_right f.smooth' x (by exact_mod_cast le_top)]
    exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _)
        (Finset.prod_le_one (fun _ _ => norm_nonneg _)
          (fun _ _ => headCLM_norm_le)))
  have hcg : ∀ j (x : Fin (n + 1) → ℝ),
      ‖iteratedFDeriv ℝ j (g.toFun ∘ fun x => fun i => x i.succ) x‖ ≤
      ‖iteratedFDeriv ℝ j g.toFun (fun i => x i.succ)‖ := by
    intro j x
    rw [show (g.toFun ∘ fun x => fun i => x i.succ) =
          g.toFun ∘ ⇑(tailCLM n) from rfl,
      (tailCLM n).iteratedFDeriv_comp_right g.smooth' x (by exact_mod_cast le_top)]
    exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _)
        (Finset.prod_le_one (fun _ _ => norm_nonneg _)
          (fun _ _ => tailCLM_opNorm_le n)))
  have hLeib := norm_iteratedFDeriv_mul_le (n := l) hfs hgs x
    (WithTop.coe_le_coe.mpr (le_top (a := (l : ℕ∞))))
  have hnorm_split := norm_le_head_add_tail n x
  have h_add_le_2max : ‖x 0‖ + ‖fun i : Fin n => x i.succ‖ ≤
      2 * max ‖x 0‖ ‖fun i : Fin n => x i.succ‖ := by
    linarith [le_max_left ‖x 0‖ ‖fun i : Fin n => x i.succ‖,
              le_max_right ‖x 0‖ ‖fun i : Fin n => x i.succ‖]
  have add_pow_le : (‖x 0‖ + ‖fun i : Fin n => x i.succ‖) ^ p ≤
      (2 : ℝ) ^ p * (‖x 0‖ ^ p + ‖fun i : Fin n => x i.succ‖ ^ p) := by
    have hmax : (max ‖x 0‖ ‖fun i : Fin n => x i.succ‖) ^ p ≤
        ‖x 0‖ ^ p + ‖fun i : Fin n => x i.succ‖ ^ p := by
      rcases max_cases ‖x 0‖ ‖fun i : Fin n => x i.succ‖ with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]; exact le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _)
      · rw [h]; exact le_add_of_nonneg_left (pow_nonneg (norm_nonneg _) _)
    calc _ ≤ (2 * max ‖x 0‖ ‖fun i : Fin n => x i.succ‖) ^ p :=
          pow_le_pow_left₀ (add_nonneg (norm_nonneg _) (norm_nonneg _)) h_add_le_2max _
      _ = (2 : ℝ) ^ p * (max ‖x 0‖ ‖fun i : Fin n => x i.succ‖) ^ p :=
          mul_pow (2 : ℝ) _ p
      _ ≤ (2 : ℝ) ^ p * (‖x 0‖ ^ p + ‖fun i : Fin n => x i.succ‖ ^ p) :=
          mul_le_mul_of_nonneg_left hmax (pow_nonneg (by norm_num) _)
  have h_pow : ‖x‖ ^ p ≤ (2 : ℝ) ^ p *
      (‖x 0‖ ^ p + ‖fun i : Fin n => x i.succ‖ ^ p) :=
    (pow_le_pow_left₀ (norm_nonneg _) hnorm_split _).trans add_pow_le
  have h_term : ∀ i ∈ Finset.range (l + 1),
      ‖x‖ ^ p * (↑(l.choose i) * ‖iteratedFDeriv ℝ i f.toFun (x 0)‖ *
      ‖iteratedFDeriv ℝ (l - i) g.toFun (fun j => x j.succ)‖) ≤
      (2 : ℝ) ^ p * (↑(l.choose i) *
        (SchwartzMap.seminorm ℝ p i f * SchwartzMap.seminorm ℝ 0 (l - i) g +
         SchwartzMap.seminorm ℝ 0 i f * SchwartzMap.seminorm ℝ p (l - i) g)) := by
    intro i _
    set a := ‖x 0‖
    set b := ‖fun j : Fin n => x j.succ‖
    set F := ‖iteratedFDeriv ℝ i f.toFun (x 0)‖
    set G := ‖iteratedFDeriv ℝ (l - i) g.toFun (fun j => x j.succ)‖
    have ha_nn : 0 ≤ a := norm_nonneg _
    have hb_nn : 0 ≤ b := norm_nonneg _
    have hF_nn : 0 ≤ F := norm_nonneg _
    have hG_nn : 0 ≤ G := norm_nonneg _
    have hf1 : a ^ p * F ≤ SchwartzMap.seminorm ℝ p i f :=
      SchwartzMap.le_seminorm ℝ p i f (x 0)
    have hg1 : G ≤ SchwartzMap.seminorm ℝ 0 (l - i) g := by
      have h := SchwartzMap.le_seminorm ℝ 0 (l - i) g (fun j => x j.succ)
      simp only [pow_zero, one_mul] at h
      exact h
    have hf2 : F ≤ SchwartzMap.seminorm ℝ 0 i f := by
      have h := SchwartzMap.le_seminorm ℝ 0 i f (x 0)
      simp only [pow_zero, one_mul] at h
      exact h
    have hg2 : b ^ p * G ≤ SchwartzMap.seminorm ℝ p (l - i) g :=
      SchwartzMap.le_seminorm ℝ p (l - i) g (fun j => x j.succ)
    have hprod1 : a ^ p * F * G ≤
        SchwartzMap.seminorm ℝ p i f * SchwartzMap.seminorm ℝ 0 (l - i) g :=
      mul_le_mul hf1 hg1 hG_nn (le_trans (mul_nonneg (pow_nonneg ha_nn _) hF_nn) hf1)
    have hprod2 : b ^ p * F * G ≤
        SchwartzMap.seminorm ℝ 0 i f * SchwartzMap.seminorm ℝ p (l - i) g := by
      calc b ^ p * F * G = F * (b ^ p * G) := by ring
        _ ≤ SchwartzMap.seminorm ℝ 0 i f * SchwartzMap.seminorm ℝ p (l - i) g :=
          mul_le_mul hf2 hg2 (mul_nonneg (pow_nonneg hb_nn _) hG_nn)
            (le_trans hF_nn hf2)
    have hchoose_nn : (0 : ℝ) ≤ ↑(l.choose i) := Nat.cast_nonneg _
    calc ‖x‖ ^ p * (↑(l.choose i) * F * G)
        ≤ ((2 : ℝ) ^ p * (a ^ p + b ^ p)) * (↑(l.choose i) * F * G) :=
          mul_le_mul_of_nonneg_right h_pow
            (mul_nonneg (mul_nonneg hchoose_nn hF_nn) hG_nn)
      _ = (2 : ℝ) ^ p * (↑(l.choose i) * (a ^ p * F * G + b ^ p * F * G)) := by
          ring
      _ ≤ (2 : ℝ) ^ p * (↑(l.choose i) *
          (SchwartzMap.seminorm ℝ p i f * SchwartzMap.seminorm ℝ 0 (l - i) g +
           SchwartzMap.seminorm ℝ 0 i f * SchwartzMap.seminorm ℝ p (l - i) g)) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
          exact mul_le_mul_of_nonneg_left (add_le_add hprod1 hprod2) hchoose_nn
  calc ‖x‖ ^ p * ‖iteratedFDeriv ℝ l
        (fun y => f (y 0) * g (fun i => y i.succ)) x‖
      ≤ ‖x‖ ^ p * ∑ i ∈ Finset.range (l + 1),
        ↑(l.choose i) * ‖iteratedFDeriv ℝ i (f.toFun ∘ fun y => y 0) x‖ *
        ‖iteratedFDeriv ℝ (l - i) (g.toFun ∘ fun y => fun j => y j.succ) x‖ := by
        gcongr
        exact hLeib
    _ ≤ ‖x‖ ^ p * ∑ i ∈ Finset.range (l + 1),
        ↑(l.choose i) * ‖iteratedFDeriv ℝ i f.toFun (x 0)‖ *
        ‖iteratedFDeriv ℝ (l - i) g.toFun (fun j => x j.succ)‖ := by
        gcongr with i hi
        · exact (hcf i x).trans le_rfl
        · exact (hcg (l - i) x).trans le_rfl
    _ = ∑ i ∈ Finset.range (l + 1),
        ‖x‖ ^ p * (↑(l.choose i) * ‖iteratedFDeriv ℝ i f.toFun (x 0)‖ *
        ‖iteratedFDeriv ℝ (l - i) g.toFun (fun j => x j.succ)‖) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.range (l + 1),
        (2 : ℝ) ^ p * (↑(l.choose i) *
          (SchwartzMap.seminorm ℝ p i f * SchwartzMap.seminorm ℝ 0 (l - i) g +
           SchwartzMap.seminorm ℝ 0 i f * SchwartzMap.seminorm ℝ p (l - i) g)) :=
        Finset.sum_le_sum h_term
    _ = _ := by rw [← Finset.mul_sum]

private noncomputable def prependFieldLinearMapRight {n : ℕ}
    (f : 𝓢(ℝ, ℂ)) :
    𝓢(Fin n → ℝ, ℂ) →ₗ[ℝ] 𝓢(Fin (n + 1) → ℝ, ℂ) where
  toFun := fun g => prependField f g
  map_add' := fun g₁ g₂ => prependField_add_right f g₁ g₂
  map_smul' := fun c g => by
    simpa using prependField_smul_right (n := n) f (c : ℂ) g

/-- Fixed-head prepend is bounded between the Schwartz seminorm families. -/
theorem prependField_isBounded_right {n : ℕ} (f : 𝓢(ℝ, ℂ)) :
    Seminorm.IsBounded
      (schwartzSeminormFamily ℝ (Fin n → ℝ) ℂ)
      (schwartzSeminormFamily ℝ (Fin (n + 1) → ℝ) ℂ)
      (prependFieldLinearMapRight (n := n) f) := by
  refine Seminorm.IsBounded.of_real ?_
  rintro ⟨p, l⟩
  let s : Finset (ℕ × ℕ) :=
    (Finset.range (l + 1)).image (fun i => ((0, l - i) : ℕ × ℕ)) ∪
      (Finset.range (l + 1)).image (fun i => ((p, l - i) : ℕ × ℕ))
  let C : ℝ :=
    (2 : ℝ) ^ p * ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
      (SchwartzMap.seminorm ℝ p i f + SchwartzMap.seminorm ℝ 0 i f)
  refine ⟨s, C, fun g => ?_⟩
  change SchwartzMap.seminorm ℝ p l (prependField f g) ≤
    C * (s.sup (schwartzSeminormFamily ℝ (Fin n → ℝ) ℂ)) g
  have hsem := prependField_seminorm_le (n := n) f g p l
  refine hsem.trans ?_
  let S : ℝ := s.sup (schwartzSeminormFamily ℝ (Fin n → ℝ) ℂ) g
  have hS_nonneg : 0 ≤ S := by
    exact apply_nonneg _ _
  have hsum :
      ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
        (SchwartzMap.seminorm ℝ p i f * SchwartzMap.seminorm ℝ 0 (l - i) g +
         SchwartzMap.seminorm ℝ 0 i f * SchwartzMap.seminorm ℝ p (l - i) g) ≤
      ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
        ((SchwartzMap.seminorm ℝ p i f + SchwartzMap.seminorm ℝ 0 i f) * S) := by
    apply Finset.sum_le_sum
    intro i hi
    have hchoose_nonneg : (0 : ℝ) ≤ ↑(l.choose i) := Nat.cast_nonneg _
    have hfpi_nonneg : 0 ≤ SchwartzMap.seminorm ℝ p i f := apply_nonneg _ _
    have hf0i_nonneg : 0 ≤ SchwartzMap.seminorm ℝ 0 i f := apply_nonneg _ _
    have hg0_le : SchwartzMap.seminorm ℝ 0 (l - i) g ≤ S := by
      have hmem : ((0, l - i) : ℕ × ℕ) ∈ s := by
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      exact (show
        (schwartzSeminormFamily ℝ (Fin n → ℝ) ℂ ((0, l - i) : ℕ × ℕ)) g ≤
          (s.sup (schwartzSeminormFamily ℝ (Fin n → ℝ) ℂ)) g from
        (Finset.le_sup (f := schwartzSeminormFamily ℝ (Fin n → ℝ) ℂ) hmem) g)
    have hgp_le : SchwartzMap.seminorm ℝ p (l - i) g ≤ S := by
      have hmem : ((p, l - i) : ℕ × ℕ) ∈ s := by
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      exact (show
        (schwartzSeminormFamily ℝ (Fin n → ℝ) ℂ ((p, l - i) : ℕ × ℕ)) g ≤
          (s.sup (schwartzSeminormFamily ℝ (Fin n → ℝ) ℂ)) g from
        (Finset.le_sup (f := schwartzSeminormFamily ℝ (Fin n → ℝ) ℂ) hmem) g)
    calc ↑(l.choose i) *
          (SchwartzMap.seminorm ℝ p i f * SchwartzMap.seminorm ℝ 0 (l - i) g +
           SchwartzMap.seminorm ℝ 0 i f * SchwartzMap.seminorm ℝ p (l - i) g)
        ≤ ↑(l.choose i) *
          (SchwartzMap.seminorm ℝ p i f * S +
           SchwartzMap.seminorm ℝ 0 i f * S) := by
          gcongr
      _ = ↑(l.choose i) *
          ((SchwartzMap.seminorm ℝ p i f + SchwartzMap.seminorm ℝ 0 i f) * S) := by
          ring
  calc
    (2 : ℝ) ^ p * ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
        (SchwartzMap.seminorm ℝ p i f * SchwartzMap.seminorm ℝ 0 (l - i) g +
         SchwartzMap.seminorm ℝ 0 i f * SchwartzMap.seminorm ℝ p (l - i) g)
        ≤ (2 : ℝ) ^ p * ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
            ((SchwartzMap.seminorm ℝ p i f + SchwartzMap.seminorm ℝ 0 i f) * S) := by
          exact mul_le_mul_of_nonneg_left hsum (pow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ p *
        ((∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
          (SchwartzMap.seminorm ℝ p i f + SchwartzMap.seminorm ℝ 0 i f)) * S) := by
        congr 1
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
    _ = C * S := by
        simp [C, mul_assoc]

/-- Fixed-head prepend is continuous in the tail argument. -/
theorem prependField_continuous_right {n : ℕ} (f : 𝓢(ℝ, ℂ)) :
    Continuous (fun g : 𝓢(Fin n → ℝ, ℂ) => prependField f g) := by
  have hcont : Continuous (prependFieldLinearMapRight (n := n) f) :=
    WithSeminorms.continuous_of_isBounded
      (schwartz_withSeminorms ℝ (Fin n → ℝ) ℂ)
      (schwartz_withSeminorms ℝ (Fin (n + 1) → ℝ) ℂ)
      (prependFieldLinearMapRight (n := n) f)
      (prependField_isBounded_right (n := n) f)
  simpa [prependFieldLinearMapRight] using hcont

/-- Fixed-head prepend as a complex continuous linear map in the tail argument. -/
def prependFieldCLMRight {n : ℕ} (f : 𝓢(ℝ, ℂ)) :
    𝓢(Fin n → ℝ, ℂ) →L[ℂ] 𝓢(Fin (n + 1) → ℝ, ℂ) where
  toLinearMap :=
    { toFun := fun g => prependField f g
      map_add' := fun g₁ g₂ => prependField_add_right f g₁ g₂
      map_smul' := fun c g => prependField_smul_right f c g }
  cont := prependField_continuous_right f

@[simp]
theorem prependFieldCLMRight_apply {n : ℕ}
    (f : 𝓢(ℝ, ℂ)) (g : 𝓢(Fin n → ℝ, ℂ)) :
    prependFieldCLMRight f g = prependField f g := rfl

end SCV
