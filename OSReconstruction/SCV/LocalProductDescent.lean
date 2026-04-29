/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.DistributionalEOWKernelFactorization
import OSReconstruction.SCV.DistributionalEOWSupport

/-!
# Local Product-Kernel Descent

This file starts the scalarized local descent package used after local EOW
product-kernel covariance has been proved.  The package deliberately begins
with small continuous-linear primitives rather than a global quotient theorem:
local covariance will only be consumed under explicit support hypotheses.
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

/-- The real embedding as a public continuous real-linear map. -/
def realEmbedContinuousLinearMap (m : ℕ) :
    (Fin m → ℝ) →L[ℝ] ComplexChartSpace m :=
  ContinuousLinearMap.pi fun i =>
    Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)

@[simp]
theorem realEmbedContinuousLinearMap_apply {m : ℕ} (a : Fin m → ℝ) :
    realEmbedContinuousLinearMap m a = realEmbed a := by
  ext i
  simp [realEmbedContinuousLinearMap, realEmbed]

/-- Fixed-left mixed tensor product as a continuous linear map in the real
kernel argument. -/
def schwartzTensorProduct₂CLMLeft {m : ℕ}
    (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
    SchwartzMap (Fin m → ℝ) ℂ →L[ℂ]
      SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ := by
  refine SchwartzMap.mkCLM (𝕜 := ℂ)
    (fun ψ p => φ p.1 * ψ p.2)
    (fun ψ η p => by simp [mul_add])
    (fun c ψ p => by simp [smul_eq_mul, mul_left_comm])
    (fun ψ => φ.smooth'.fst'.mul ψ.smooth'.snd') ?_
  rintro ⟨k, l⟩
  let s : Finset (ℕ × ℕ) :=
    (Finset.range (l + 1)).image (fun i => ((0, l - i) : ℕ × ℕ)) ∪
      (Finset.range (l + 1)).image (fun i => ((k, l - i) : ℕ × ℕ))
  let C : ℝ :=
    (2 : ℝ) ^ k * ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
      (SchwartzMap.seminorm ℂ k i φ +
        SchwartzMap.seminorm ℂ 0 i φ)
  refine ⟨s, C, by positivity, fun ψ x => ?_⟩
  have hφs := φ.smooth'.comp
    (ContinuousLinearMap.fst ℝ (ComplexChartSpace m) (Fin m → ℝ)).contDiff
  have hψs := ψ.smooth'.comp
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
      ‖iteratedFDeriv ℝ j (ψ.toFun ∘ Prod.snd) x‖ ≤
        ‖iteratedFDeriv ℝ j ψ.toFun x.2‖ := by
    intro j x
    rw [show ψ.toFun ∘ Prod.snd =
        ψ.toFun ∘ ⇑(ContinuousLinearMap.snd ℝ (ComplexChartSpace m) (Fin m → ℝ)) from rfl,
      (ContinuousLinearMap.snd ℝ (ComplexChartSpace m) (Fin m → ℝ)).iteratedFDeriv_comp_right
        ψ.smooth' x (by exact_mod_cast le_top)]
    exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _)
        (Finset.prod_le_one (fun _ _ => norm_nonneg _)
          (fun _ _ =>
            ContinuousLinearMap.norm_snd_le ℝ (ComplexChartSpace m) (Fin m → ℝ))))
  have hLeib := norm_iteratedFDeriv_mul_le (n := l) hφs hψs x
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
        ‖iteratedFDeriv ℝ (l - i) ψ.toFun x.2‖) ≤
      (2 : ℝ) ^ k * (↑(l.choose i) *
        ((SchwartzMap.seminorm ℂ k i φ + SchwartzMap.seminorm ℂ 0 i φ) *
          (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) ψ)) := by
    intro i hi
    let S : ℝ := (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) ψ
    set a := ‖x.1‖
    set b := ‖x.2‖
    set F := ‖iteratedFDeriv ℝ i φ.toFun x.1‖
    set G := ‖iteratedFDeriv ℝ (l - i) ψ.toFun x.2‖
    have ha_nn : 0 ≤ a := norm_nonneg _
    have hb_nn : 0 ≤ b := norm_nonneg _
    have hF_nn : 0 ≤ F := norm_nonneg _
    have hG_nn : 0 ≤ G := norm_nonneg _
    have hφ1 : a ^ k * F ≤ SchwartzMap.seminorm ℂ k i φ :=
      SchwartzMap.le_seminorm ℂ k i φ x.1
    have hψ1 : G ≤ S := by
      have hψ0 : G ≤ SchwartzMap.seminorm ℂ 0 (l - i) ψ := by
        have h := SchwartzMap.le_seminorm ℂ 0 (l - i) ψ x.2
        simp only [pow_zero, one_mul] at h
        exact h
      have hmem : ((0, l - i) : ℕ × ℕ) ∈ s :=
        Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      exact hψ0.trans
        ((Finset.le_sup
          (f := schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ) hmem) ψ)
    have hφ2 : F ≤ SchwartzMap.seminorm ℂ 0 i φ := by
      have h := SchwartzMap.le_seminorm ℂ 0 i φ x.1
      simp only [pow_zero, one_mul] at h
      exact h
    have hψ2 : b ^ k * G ≤ S := by
      have hψk : b ^ k * G ≤ SchwartzMap.seminorm ℂ k (l - i) ψ :=
        SchwartzMap.le_seminorm ℂ k (l - i) ψ x.2
      have hmem : ((k, l - i) : ℕ × ℕ) ∈ s :=
        Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      exact hψk.trans
        ((Finset.le_sup
          (f := schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ) hmem) ψ)
    have hprod1 : a ^ k * F * G ≤
        SchwartzMap.seminorm ℂ k i φ * S :=
      mul_le_mul hφ1 hψ1 hG_nn
        (le_trans (mul_nonneg (pow_nonneg ha_nn _) hF_nn) hφ1)
    have hprod2 : b ^ k * F * G ≤
        SchwartzMap.seminorm ℂ 0 i φ * S := by
      calc
        b ^ k * F * G = F * (b ^ k * G) := by ring
        _ ≤ SchwartzMap.seminorm ℂ 0 i φ * S :=
          mul_le_mul hφ2 hψ2 (mul_nonneg (pow_nonneg hb_nn _) hG_nn)
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
          ((SchwartzMap.seminorm ℂ k i φ + SchwartzMap.seminorm ℂ 0 i φ) * S)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
        apply mul_le_mul_of_nonneg_left _ hchoose_nn
        calc
          a ^ k * F * G + b ^ k * F * G ≤
              SchwartzMap.seminorm ℂ k i φ * S +
                SchwartzMap.seminorm ℂ 0 i φ * S :=
            add_le_add hprod1 hprod2
          _ = (SchwartzMap.seminorm ℂ k i φ +
                SchwartzMap.seminorm ℂ 0 i φ) * S := by
            ring
  have hraw :
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun y => φ y.1 * ψ y.2) x‖ ≤
      (2 : ℝ) ^ k * ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
        ((SchwartzMap.seminorm ℂ k i φ + SchwartzMap.seminorm ℂ 0 i φ) *
          (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) ψ) := by
    calc
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun y => φ y.1 * ψ y.2) x‖
          ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (l + 1),
            ↑(l.choose i) * ‖iteratedFDeriv ℝ i (φ.toFun ∘ Prod.fst) x‖ *
            ‖iteratedFDeriv ℝ (l - i) (ψ.toFun ∘ Prod.snd) x‖ := by
        gcongr
        exact hLeib
      _ ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (l + 1),
            ↑(l.choose i) * ‖iteratedFDeriv ℝ i φ.toFun x.1‖ *
            ‖iteratedFDeriv ℝ (l - i) ψ.toFun x.2‖ := by
        gcongr with i hi
        · exact (hcf i x).trans le_rfl
        · exact (hcg (l - i) x).trans le_rfl
      _ = ∑ i ∈ Finset.range (l + 1),
            ‖x‖ ^ k * (↑(l.choose i) * ‖iteratedFDeriv ℝ i φ.toFun x.1‖ *
            ‖iteratedFDeriv ℝ (l - i) ψ.toFun x.2‖) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.range (l + 1),
          (2 : ℝ) ^ k * (↑(l.choose i) *
            ((SchwartzMap.seminorm ℂ k i φ + SchwartzMap.seminorm ℂ 0 i φ) *
              (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) ψ)) :=
        Finset.sum_le_sum h_term
      _ = _ := by rw [← Finset.mul_sum]
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun y => φ y.1 * ψ y.2) x‖
        ≤ (2 : ℝ) ^ k * ∑ i ∈ Finset.range (l + 1), ↑(l.choose i) *
          ((SchwartzMap.seminorm ℂ k i φ + SchwartzMap.seminorm ℂ 0 i φ) *
            (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) ψ) := hraw
    _ = C * (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) ψ := by
      simp [C, mul_assoc, Finset.sum_mul]

@[simp]
theorem schwartzTensorProduct₂CLMLeft_apply {m : ℕ}
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (z : ComplexChartSpace m) (t : Fin m → ℝ) :
    schwartzTensorProduct₂CLMLeft φ ψ (z, t) = φ z * ψ t := rfl

theorem schwartzTensorProduct₂CLMLeft_eq {m : ℕ}
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ) :
    schwartzTensorProduct₂CLMLeft φ ψ =
      schwartzTensorProduct₂ φ ψ := by
  ext p
  rfl

/-- Partial evaluation of a triple mixed Schwartz test at a fixed last real
parameter, as a continuous linear map in the ambient triple test. -/
def schwartzPartialEval₂CLM {m : ℕ} (a : Fin m → ℝ) :
    SchwartzMap
      ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) ℂ →L[ℂ]
        SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ := by
  let B := ComplexChartSpace m × (Fin m → ℝ)
  let P := Fin m → ℝ
  let g : B → B × P := fun b => (b, a)
  have hg : g.HasTemperateGrowth := by
    have hconst : Function.HasTemperateGrowth
        (fun _ : B => ((0, a) : B × P)) :=
      Function.HasTemperateGrowth.const _
    have hlin : Function.HasTemperateGrowth
        (⇑(ContinuousLinearMap.inl ℝ B P)) :=
      (ContinuousLinearMap.inl ℝ B P).hasTemperateGrowth
    convert hlin.add hconst using 1
    ext b <;> simp [g, B, P, ContinuousLinearMap.inl_apply, Prod.add_def]
  have hg_upper : ∃ (k : ℕ) (C : ℝ), ∀ b, ‖b‖ ≤ C * (1 + ‖g b‖) ^ k := by
    refine ⟨1, 1, ?_⟩
    intro b
    have hb : ‖b‖ ≤ ‖g b‖ := by
      simp [g, Prod.norm_def]
    have hnonneg : 0 ≤ ‖g b‖ := norm_nonneg _
    nlinarith
  exact SchwartzMap.compCLM (𝕜 := ℂ) (g := g) hg hg_upper

@[simp]
theorem schwartzPartialEval₂CLM_apply {m : ℕ}
    (a : Fin m → ℝ)
    (A : SchwartzMap
      ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) ℂ)
    (z : ComplexChartSpace m) (t : Fin m → ℝ) :
    schwartzPartialEval₂CLM a A (z, t) = A ((z, t), a) := rfl

/-- The fixed-last-variable partial evaluations vary continuously in the last
real parameter. -/
theorem continuous_schwartzPartialEval₂CLM {m : ℕ}
    (A : SchwartzMap
      ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) ℂ) :
    Continuous fun a : Fin m → ℝ => schwartzPartialEval₂CLM a A := by
  let B := ComplexChartSpace m × (Fin m → ℝ)
  let P := Fin m → ℝ
  let Acomm : SchwartzMap (P × B) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (ContinuousLinearEquiv.prodComm ℝ P B)) A
  have hcont : Continuous fun a : P => schwartzPartialEval₁ Acomm a :=
    continuous_schwartzPartialEval₁ Acomm
  have hfun :
      (fun a : P => schwartzPartialEval₂CLM a A) =
        fun a : P => schwartzPartialEval₁ Acomm a := by
    funext a
    ext b
    rcases b with ⟨z, t⟩
    rfl
  simpa [B, P, hfun]

end SCV
