/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.DistributionalEOWKernelFactorization
import OSReconstruction.SCV.DistributionalEOWSupport
import OSReconstruction.SCV.SchwartzExternalProduct

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

/-- Singleton seminorm decay for fixed-last-variable partial evaluation.

The two source seminorms control the origin and the radial tail in the fixed
parameter. -/
private theorem schwartzPartialEval₂CLM_seminorm_decay_one_bound {m : ℕ}
    (k l : ℕ) :
    let μ : Measure (Fin m → ℝ) := volume
    let N := μ.integrablePower
    let s : Finset (ℕ × ℕ) := {((k, l) : ℕ × ℕ), (k + N, l)}
    let C : ℝ := (2 : ℝ) ^ N * 2
    0 ≤ C ∧
      ∀ (A : SchwartzMap
          ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) ℂ)
        (a : Fin m → ℝ),
        SchwartzMap.seminorm ℂ k l (schwartzPartialEval₂CLM a A) ≤
          C * (1 + ‖a‖) ^ (-(N : ℝ)) *
            s.sup (schwartzSeminormFamily ℂ
              ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) ℂ) A := by
  let B := ComplexChartSpace m × (Fin m → ℝ)
  let P := Fin m → ℝ
  let μ : Measure P := volume
  let N := μ.integrablePower
  let s : Finset (ℕ × ℕ) := {((k, l) : ℕ × ℕ), (k + N, l)}
  let C : ℝ := (2 : ℝ) ^ N * 2
  change 0 ≤ C ∧
      ∀ (A : SchwartzMap (B × P) ℂ) (a : P),
        SchwartzMap.seminorm ℂ k l (schwartzPartialEval₂CLM a A) ≤
          C * (1 + ‖a‖) ^ (-(N : ℝ)) *
            s.sup (schwartzSeminormFamily ℂ (B × P) ℂ) A
  refine ⟨by positivity, ?_⟩
  intro A a
  let S : ℝ := s.sup (schwartzSeminormFamily ℂ (B × P) ℂ) A
  let r : ℝ := (1 + ‖a‖) ^ (-(N : ℝ))
  have hS_nonneg : 0 ≤ S := apply_nonneg _ _
  have hr_nonneg : 0 ≤ r := by positivity
  have hC₁_le : SchwartzMap.seminorm ℂ k l A ≤ S := by
    have hmem : ((k, l) : ℕ × ℕ) ∈ s := by simp [s]
    exact (show
      (schwartzSeminormFamily ℂ (B × P) ℂ ((k, l) : ℕ × ℕ)) A ≤ S from
        (Finset.le_sup (f := schwartzSeminormFamily ℂ (B × P) ℂ) hmem) A)
  have hC₂_le : SchwartzMap.seminorm ℂ (k + N) l A ≤ S := by
    have hmem : ((k + N, l) : ℕ × ℕ) ∈ s := by simp [s]
    exact (show
      (schwartzSeminormFamily ℂ (B × P) ℂ ((k + N, l) : ℕ × ℕ)) A ≤ S from
        (Finset.le_sup (f := schwartzSeminormFamily ℂ (B × P) ℂ) hmem) A)
  apply SchwartzMap.seminorm_le_bound ℂ k l _ (mul_nonneg (mul_nonneg (by positivity) hr_nonneg) hS_nonneg)
  intro b
  let D : ℝ :=
    ‖iteratedFDeriv ℝ l (fun x => (schwartzPartialEval₂CLM a A) x) b‖
  let E : ℝ := ‖iteratedFDeriv ℝ l (⇑A) (b, a)‖
  have hD_nonneg : 0 ≤ D := norm_nonneg _
  have hE_nonneg : 0 ≤ E := norm_nonneg _
  have hderiv : D ≤ E := by
    simpa [D, E, schwartzPartialEval₂CLM_apply] using
      norm_iteratedFDeriv_partialEval_le (f := A) (y := a) (l := l) (x := b)
  have hb_norm : ‖b‖ ≤ ‖(b, a)‖ := by
    rw [Prod.norm_def]
    exact le_max_left ‖b‖ ‖a‖
  have ha_norm : ‖a‖ ≤ ‖(b, a)‖ := by
    rw [Prod.norm_def]
    exact le_max_right ‖b‖ ‖a‖
  have h₁ : ‖b‖ ^ k * D ≤ SchwartzMap.seminorm ℂ k l A := by
    calc
      ‖b‖ ^ k * D ≤ ‖b‖ ^ k * E :=
        mul_le_mul_of_nonneg_left hderiv (pow_nonneg (norm_nonneg _) _)
      _ ≤ ‖(b, a)‖ ^ k * E := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) hb_norm _) hE_nonneg
      _ ≤ SchwartzMap.seminorm ℂ k l A :=
        SchwartzMap.le_seminorm ℂ k l A (b, a)
  have hpow_prod : ‖a‖ ^ N * ‖b‖ ^ k ≤ ‖(b, a)‖ ^ (k + N) := by
    have ha_pow : ‖a‖ ^ N ≤ ‖(b, a)‖ ^ N :=
      pow_le_pow_left₀ (norm_nonneg _) ha_norm _
    have hb_pow : ‖b‖ ^ k ≤ ‖(b, a)‖ ^ k :=
      pow_le_pow_left₀ (norm_nonneg _) hb_norm _
    calc
      ‖a‖ ^ N * ‖b‖ ^ k ≤ ‖(b, a)‖ ^ N * ‖(b, a)‖ ^ k :=
        mul_le_mul ha_pow hb_pow (pow_nonneg (norm_nonneg _) _)
          (pow_nonneg (norm_nonneg _) _)
      _ = ‖(b, a)‖ ^ (N + k) := by rw [pow_add]
      _ = ‖(b, a)‖ ^ (k + N) := by rw [add_comm]
  have h₂ : ‖a‖ ^ N * (‖b‖ ^ k * D) ≤
      SchwartzMap.seminorm ℂ (k + N) l A := by
    calc
      ‖a‖ ^ N * (‖b‖ ^ k * D) =
          (‖a‖ ^ N * ‖b‖ ^ k) * D := by ring
      _ ≤ ‖(b, a)‖ ^ (k + N) * E :=
        mul_le_mul hpow_prod hderiv hD_nonneg
          (pow_nonneg (norm_nonneg _) _)
      _ ≤ SchwartzMap.seminorm ℂ (k + N) l A :=
        SchwartzMap.le_seminorm ℂ (k + N) l A (b, a)
  have hmain := pow_mul_le_of_le_of_pow_mul_le (k := 0) (l := N)
    (x := ‖a‖) (f := ‖b‖ ^ k * D)
    (C₁ := SchwartzMap.seminorm ℂ k l A)
    (C₂ := SchwartzMap.seminorm ℂ (k + N) l A)
    (norm_nonneg _) (mul_nonneg (pow_nonneg (norm_nonneg _) _) hD_nonneg)
    h₁ (by simpa using h₂)
  have hsum_le : SchwartzMap.seminorm ℂ k l A +
      SchwartzMap.seminorm ℂ (k + N) l A ≤ 2 * S := by
    linarith
  calc
    ‖b‖ ^ k *
        ‖iteratedFDeriv ℝ l (fun x => (schwartzPartialEval₂CLM a A) x) b‖
        = ‖b‖ ^ k * D := rfl
    _ ≤ (2 : ℝ) ^ N *
          (SchwartzMap.seminorm ℂ k l A +
            SchwartzMap.seminorm ℂ (k + N) l A) * r := by
      simpa [r] using hmain
    _ ≤ (2 : ℝ) ^ N * (2 * S) * r := by
      gcongr
    _ = C * r * S := by
      ring

/-- Singleton finite-seminorm decay for fixed-last-variable partial
evaluation. -/
theorem schwartzPartialEval₂CLM_seminorm_decay_one {m : ℕ} (k l : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : SchwartzMap
          ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) ℂ)
        (a : Fin m → ℝ),
        SchwartzMap.seminorm ℂ k l (schwartzPartialEval₂CLM a A) ≤
          C * (1 + ‖a‖) ^
              (-((volume : Measure (Fin m → ℝ)).integrablePower : ℝ)) *
            s.sup (schwartzSeminormFamily ℂ
              ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) ℂ) A := by
  let μ : Measure (Fin m → ℝ) := volume
  let N := μ.integrablePower
  let s : Finset (ℕ × ℕ) := {((k, l) : ℕ × ℕ), (k + N, l)}
  let C : ℝ := (2 : ℝ) ^ N * 2
  refine ⟨s, C, ?_, ?_⟩
  · exact (schwartzPartialEval₂CLM_seminorm_decay_one_bound (m := m) k l).1
  · intro A a
    simpa [μ, N, s, C] using
      (schwartzPartialEval₂CLM_seminorm_decay_one_bound (m := m) k l).2 A a

/-- Finite-family seminorm decay for fixed-last-variable partial evaluation. -/
theorem schwartzPartialEval₂CLM_finsetSeminorm_decay {m : ℕ}
    (s0 : Finset (ℕ × ℕ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : SchwartzMap
          ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) ℂ)
        (a : Fin m → ℝ),
        s0.sup (schwartzSeminormFamily ℂ
            (ComplexChartSpace m × (Fin m → ℝ)) ℂ)
            (schwartzPartialEval₂CLM a A) ≤
          C * (1 + ‖a‖) ^
              (-((volume : Measure (Fin m → ℝ)).integrablePower : ℝ)) *
            s.sup (schwartzSeminormFamily ℂ
              ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) ℂ) A := by
  let μ : Measure (Fin m → ℝ) := volume
  let N := μ.integrablePower
  let source : ℕ × ℕ → Finset (ℕ × ℕ) :=
    fun i => {i, (i.1 + N, i.2)}
  let s : Finset (ℕ × ℕ) := s0.biUnion source
  let C0 : ℝ := (2 : ℝ) ^ N * 2
  let C : ℝ := ∑ i ∈ s0, C0
  refine ⟨s, C, ?_, ?_⟩
  · exact Finset.sum_nonneg fun _ _ => by positivity
  intro A a
  let S : ℝ := s.sup (schwartzSeminormFamily ℂ
    ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) ℂ) A
  let r : ℝ := (1 + ‖a‖) ^ (-(N : ℝ))
  have hS_nonneg : 0 ≤ S := apply_nonneg _ _
  have hr_nonneg : 0 ≤ r := by positivity
  have htarget_nonneg : 0 ≤ C * r * S :=
    mul_nonneg (mul_nonneg (Finset.sum_nonneg fun _ _ => by positivity) hr_nonneg) hS_nonneg
  apply Seminorm.finset_sup_apply_le
  · simpa [μ, N, s, C, S, r, mul_assoc] using htarget_nonneg
  intro i hi
  rcases i with ⟨k, l⟩
  let sOne : Finset (ℕ × ℕ) := source (k, l)
  let SOne : ℝ := sOne.sup (schwartzSeminormFamily ℂ
    ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) ℂ) A
  have hOne := (schwartzPartialEval₂CLM_seminorm_decay_one_bound (m := m) k l).2 A a
  have hSOne_le : SOne ≤ S := by
    apply Seminorm.finset_sup_apply_le
    · exact hS_nonneg
    intro j hj
    exact (Seminorm.le_finset_sup_apply
      (p := schwartzSeminormFamily ℂ
        ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) ℂ)
      (s := s) (x := A)
      (by
        exact Finset.mem_biUnion.mpr ⟨(k, l), hi, hj⟩))
  have hC0_nonneg : 0 ≤ C0 := by positivity
  have hC0_le_C : C0 ≤ C := by
    simpa [C] using Finset.single_le_sum (fun _ _ => hC0_nonneg) hi
  calc
    (schwartzSeminormFamily ℂ (ComplexChartSpace m × (Fin m → ℝ)) ℂ (k, l))
        (schwartzPartialEval₂CLM a A)
        ≤ C0 * r * SOne := by
      simpa [μ, N, C0, sOne, SOne, source, r] using hOne
    _ ≤ C0 * r * S := by
      gcongr
    _ ≤ C * r * S := by
      gcongr

/-- Raw real-fiber integral over the last real parameter with mixed base. -/
def mixedRealFiberIntegralRaw {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (A : SchwartzMap
      ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) V)
    (b : ComplexChartSpace m × (Fin m → ℝ)) : V :=
  ∫ a : Fin m → ℝ, A (b, a)

@[simp]
theorem mixedRealFiberIntegralRaw_apply {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (A : SchwartzMap
      ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) V)
    (b : ComplexChartSpace m × (Fin m → ℝ)) :
    mixedRealFiberIntegralRaw A b = ∫ a : Fin m → ℝ, A (b, a) := by
  rfl

/-- Every fixed mixed-base fiber of a triple Schwartz map is Bochner
integrable over the last real parameter. -/
theorem integrable_mixedRealFiber {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (A : SchwartzMap
      ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) V)
    (b : ComplexChartSpace m × (Fin m → ℝ)) :
    Integrable (fun a : Fin m → ℝ => A (b, a)) := by
  let B := ComplexChartSpace m × (Fin m → ℝ)
  let P := Fin m → ℝ
  let μ : Measure P := volume
  have hmeas : AEStronglyMeasurable (fun a : P => A (b, a)) μ := by
    have hcont_pair : Continuous fun a : P => (b, a) := by
      exact continuous_const.prodMk continuous_id
    exact (A.continuous.comp hcont_pair).aestronglyMeasurable
  have hnorm : Integrable (fun a : P => ‖a‖ ^ 0 * ‖A (b, a)‖) μ := by
    refine integrable_of_le_of_pow_mul_le
      (μ := μ) (f := fun a : P => A (b, a))
      (C₁ := SchwartzMap.seminorm ℝ 0 0 A)
      (C₂ := SchwartzMap.seminorm ℝ (0 + μ.integrablePower) 0 A) (k := 0)
      ?hf ?hpow hmeas
    · intro a
      have h := SchwartzMap.le_seminorm ℝ 0 0 A (b, a)
      simpa using h
    · intro a
      have ha_norm : ‖a‖ ≤ ‖(b, a)‖ := by
        rw [Prod.norm_def]
        exact le_max_right ‖b‖ ‖a‖
      have hpow_le :
          ‖a‖ ^ (0 + μ.integrablePower) ≤
            ‖(b, a)‖ ^ (0 + μ.integrablePower) :=
        pow_le_pow_left₀ (norm_nonneg _) ha_norm _
      have h := SchwartzMap.le_seminorm ℝ (0 + μ.integrablePower) 0 A (b, a)
      have h' :
          ‖(b, a)‖ ^ (0 + μ.integrablePower) * ‖A (b, a)‖ ≤
            SchwartzMap.seminorm ℝ (0 + μ.integrablePower) 0 A := by
        simpa using h
      exact (mul_le_mul_of_nonneg_right hpow_le (norm_nonneg _)).trans h'
  rw [← integrable_norm_iff hmeas]
  simpa using hnorm

/-- The mixed-base derivative field of a triple Schwartz map. -/
def mixedBaseFDerivSchwartz {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (A : SchwartzMap
      ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) V) :
    SchwartzMap
      ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ))
      ((ComplexChartSpace m × (Fin m → ℝ)) →L[ℝ] V) := by
  let B := ComplexChartSpace m × (Fin m → ℝ)
  let P := Fin m → ℝ
  exact
    (SchwartzMap.postcompCLM
      ((ContinuousLinearMap.inl ℝ B P).precomp V))
      (SchwartzMap.fderivCLM ℝ (B × P) V A)

@[simp]
theorem mixedBaseFDerivSchwartz_apply {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (A : SchwartzMap
      ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) V)
    (b : ComplexChartSpace m × (Fin m → ℝ)) (a : Fin m → ℝ) :
    mixedBaseFDerivSchwartz A (b, a) =
      (fderiv ℝ
        (A : ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) → V)
        (b, a)).comp
        (ContinuousLinearMap.inl ℝ
          (ComplexChartSpace m × (Fin m → ℝ)) (Fin m → ℝ)) := by
  simp [mixedBaseFDerivSchwartz]

/-- Zeroth-order weighted decay of the raw mixed real-fiber integral. -/
theorem exists_norm_pow_mul_mixedRealFiberIntegralRaw_le {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (A : SchwartzMap
      ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) V)
    (k : ℕ) :
    ∃ C, ∀ b : ComplexChartSpace m × (Fin m → ℝ),
      ‖b‖ ^ k * ‖mixedRealFiberIntegralRaw A b‖ ≤ C := by
  let B := ComplexChartSpace m × (Fin m → ℝ)
  let P := Fin m → ℝ
  let μ : Measure P := volume
  let C₁ : ℝ := SchwartzMap.seminorm ℝ k 0 A
  let C₂ : ℝ := SchwartzMap.seminorm ℝ (k + μ.integrablePower) 0 A
  refine ⟨2 ^ μ.integrablePower *
      (∫ a : P, (1 + ‖a‖) ^ (-(μ.integrablePower : ℝ))) * (C₁ + C₂), ?_⟩
  intro b
  let c : ℝ := ‖b‖ ^ k
  have hc_nonneg : 0 ≤ c := pow_nonneg (norm_nonneg _) _
  have hbound :
      ∫ a : P, ‖a‖ ^ 0 * ‖c • A (b, a)‖ ∂μ ≤
        2 ^ μ.integrablePower *
          (∫ a : P, (1 + ‖a‖) ^ (-(μ.integrablePower : ℝ))) * (C₁ + C₂) := by
    refine integral_pow_mul_le_of_le_of_pow_mul_le (μ := μ) (k := 0)
      (f := fun a : P => c • A (b, a)) (C₁ := C₁) (C₂ := C₂) ?hf ?hpow
    · intro a
      have hb_norm : ‖b‖ ≤ ‖(b, a)‖ := by
        rw [Prod.norm_def]
        exact le_max_left ‖b‖ ‖a‖
      have hbpow : ‖b‖ ^ k ≤ ‖(b, a)‖ ^ k :=
        pow_le_pow_left₀ (norm_nonneg _) hb_norm _
      have h := SchwartzMap.le_seminorm ℝ k 0 A (b, a)
      have h' : ‖(b, a)‖ ^ k * ‖A (b, a)‖ ≤ C₁ := by
        simpa [C₁] using h
      calc
        ‖c • A (b, a)‖ = c * ‖A (b, a)‖ := by
          simp [c, norm_smul]
        _ = ‖b‖ ^ k * ‖A (b, a)‖ := rfl
        _ ≤ ‖(b, a)‖ ^ k * ‖A (b, a)‖ := by
          exact mul_le_mul_of_nonneg_right hbpow (norm_nonneg _)
        _ ≤ C₁ := h'
    · intro a
      have hb_norm : ‖b‖ ≤ ‖(b, a)‖ := by
        rw [Prod.norm_def]
        exact le_max_left ‖b‖ ‖a‖
      have ha_norm : ‖a‖ ≤ ‖(b, a)‖ := by
        rw [Prod.norm_def]
        exact le_max_right ‖b‖ ‖a‖
      have hprod : ‖a‖ ^ (0 + μ.integrablePower) * c ≤
          ‖(b, a)‖ ^ (k + μ.integrablePower) := by
        have ha_pow :
            ‖a‖ ^ μ.integrablePower ≤ ‖(b, a)‖ ^ μ.integrablePower :=
          pow_le_pow_left₀ (norm_nonneg _) ha_norm _
        have hb_pow : ‖b‖ ^ k ≤ ‖(b, a)‖ ^ k :=
          pow_le_pow_left₀ (norm_nonneg _) hb_norm _
        calc
          ‖a‖ ^ (0 + μ.integrablePower) * c =
              ‖a‖ ^ μ.integrablePower * ‖b‖ ^ k := by
            simp [c]
          _ ≤ ‖(b, a)‖ ^ μ.integrablePower * ‖(b, a)‖ ^ k :=
            mul_le_mul ha_pow hb_pow (pow_nonneg (norm_nonneg _) _)
              (pow_nonneg (norm_nonneg _) _)
          _ = ‖(b, a)‖ ^ (μ.integrablePower + k) := by
            rw [pow_add]
          _ = ‖(b, a)‖ ^ (k + μ.integrablePower) := by
            rw [add_comm]
      have h := SchwartzMap.le_seminorm ℝ (k + μ.integrablePower) 0 A (b, a)
      have h' : ‖(b, a)‖ ^ (k + μ.integrablePower) * ‖A (b, a)‖ ≤ C₂ := by
        simpa [C₂] using h
      calc
        ‖a‖ ^ (0 + μ.integrablePower) * ‖c • A (b, a)‖
            = (‖a‖ ^ (0 + μ.integrablePower) * c) * ‖A (b, a)‖ := by
              simp [c, norm_smul, mul_assoc]
        _ ≤ ‖(b, a)‖ ^ (k + μ.integrablePower) * ‖A (b, a)‖ :=
          mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
        _ ≤ C₂ := h'
  have hnorm_int :
      ‖mixedRealFiberIntegralRaw A b‖ ≤ ∫ a : P, ‖A (b, a)‖ := by
    simpa [mixedRealFiberIntegralRaw, μ] using
      (norm_integral_le_integral_norm (μ := μ) (f := fun a : P => A (b, a)))
  calc
    ‖b‖ ^ k * ‖mixedRealFiberIntegralRaw A b‖
        ≤ ‖b‖ ^ k * ∫ a : P, ‖A (b, a)‖ := by
          gcongr
    _ = ∫ a : P, ‖b‖ ^ k * ‖A (b, a)‖ := by
          rw [← integral_const_mul]
    _ = ∫ a : P, ‖a‖ ^ 0 * ‖c • A (b, a)‖ ∂μ := by
          apply integral_congr_ae
          filter_upwards with a
          simp [c, norm_smul]
    _ ≤ 2 ^ μ.integrablePower *
          (∫ a : P, (1 + ‖a‖) ^ (-(μ.integrablePower : ℝ))) * (C₁ + C₂) := hbound

/-- A single integrable last-parameter bound for the mixed-base derivative
field, uniform in the mixed base point. -/
lemma exists_integrable_bound_mixedBaseFDerivSchwartz {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (A : SchwartzMap
      ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) V) :
    ∃ bound : (Fin m → ℝ) → ℝ,
      Integrable bound ∧
      ∀ b a, ‖mixedBaseFDerivSchwartz A (b, a)‖ ≤ bound a := by
  let B := ComplexChartSpace m × (Fin m → ℝ)
  let P := Fin m → ℝ
  let μ : Measure P := volume
  let G : SchwartzMap (B × P) (B →L[ℝ] V) :=
    mixedBaseFDerivSchwartz A
  let C₁ : ℝ := SchwartzMap.seminorm ℝ 0 0 G
  let C₂ : ℝ := SchwartzMap.seminorm ℝ (0 + μ.integrablePower) 0 G
  refine ⟨fun a => 2 ^ μ.integrablePower * (C₁ + C₂) *
      (1 + ‖a‖) ^ (-(μ.integrablePower : ℝ)), ?_, ?_⟩
  · simpa [mul_assoc, mul_comm, mul_left_comm] using
      (Measure.integrable_pow_neg_integrablePower μ).const_mul
        (2 ^ μ.integrablePower * (C₁ + C₂))
  · intro b a
    have h1 : ‖G (b, a)‖ ≤ C₁ := by
      have h := SchwartzMap.le_seminorm ℝ 0 0 G (b, a)
      simpa [G, C₁] using h
    have ha_norm : ‖a‖ ≤ ‖(b, a)‖ := by
      rw [Prod.norm_def]
      exact le_max_right ‖b‖ ‖a‖
    have hpow_le :
        ‖a‖ ^ (0 + μ.integrablePower) ≤ ‖(b, a)‖ ^ (0 + μ.integrablePower) :=
      pow_le_pow_left₀ (norm_nonneg _) ha_norm _
    have h2 : ‖a‖ ^ (0 + μ.integrablePower) * ‖G (b, a)‖ ≤ C₂ := by
      have h := SchwartzMap.le_seminorm ℝ (0 + μ.integrablePower) 0 G (b, a)
      have h' : ‖(b, a)‖ ^ (0 + μ.integrablePower) * ‖G (b, a)‖ ≤ C₂ := by
        simpa [G, C₂] using h
      exact (mul_le_mul_of_nonneg_right hpow_le (norm_nonneg _)).trans h'
    have hmain := pow_mul_le_of_le_of_pow_mul_le (k := 0) (l := μ.integrablePower)
      (x := ‖a‖) (f := ‖G (b, a)‖) (C₁ := C₁) (C₂ := C₂)
      (norm_nonneg _) (norm_nonneg _) h1 h2
    simpa [G, mul_assoc, mul_comm, mul_left_comm] using hmain

/-- Differentiation under the mixed real-fiber integral. -/
theorem hasFDerivAt_mixedRealFiberIntegralRaw {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (A : SchwartzMap
      ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) V)
    (b : ComplexChartSpace m × (Fin m → ℝ)) :
    HasFDerivAt (mixedRealFiberIntegralRaw A)
      (mixedRealFiberIntegralRaw (mixedBaseFDerivSchwartz A) b) b := by
  let B := ComplexChartSpace m × (Fin m → ℝ)
  let P := Fin m → ℝ
  obtain ⟨bound, hbound_int, hbound⟩ := exists_integrable_bound_mixedBaseFDerivSchwartz A
  have hs : (Set.univ : Set B) ∈ nhds b := Filter.univ_mem
  have hA_meas :
      ∀ᶠ b' in nhds b,
        AEStronglyMeasurable (fun a : P => A (b', a))
          (MeasureTheory.volume : MeasureTheory.Measure P) := by
    exact Filter.Eventually.of_forall fun b' =>
      (integrable_mixedRealFiber A b').aestronglyMeasurable
  have hA_int :
      Integrable (fun a : P => A (b, a))
        (MeasureTheory.volume : MeasureTheory.Measure P) :=
    integrable_mixedRealFiber A b
  have hA'_meas :
      AEStronglyMeasurable (fun a : P => mixedBaseFDerivSchwartz A (b, a))
        (MeasureTheory.volume : MeasureTheory.Measure P) :=
    (integrable_mixedRealFiber (mixedBaseFDerivSchwartz A) b).aestronglyMeasurable
  have h_bound :
      ∀ᵐ a ∂(MeasureTheory.volume : MeasureTheory.Measure P),
        ∀ b' ∈ (Set.univ : Set B),
          ‖mixedBaseFDerivSchwartz A (b', a)‖ ≤ bound a := by
    exact Filter.Eventually.of_forall fun a b' _ => hbound b' a
  have h_diff :
      ∀ᵐ a ∂(MeasureTheory.volume : MeasureTheory.Measure P),
        ∀ b' ∈ (Set.univ : Set B),
          HasFDerivAt (fun b'' : B => A (b'', a))
            (mixedBaseFDerivSchwartz A (b', a)) b' := by
    refine Filter.Eventually.of_forall ?_
    intro a b' _
    let inl : B →L[ℝ] B × P :=
      ContinuousLinearMap.inl ℝ B P
    have hinner : HasFDerivAt (fun b'' : B => (b'', a)) inl b' := by
      have hlin : HasFDerivAt (fun b'' : B => inl b'') inl b' :=
        inl.hasFDerivAt
      have hconst : (fun b'' : B => (b'', a)) =
          fun b'' => inl b'' + (0, a) := by
        funext b''
        ext <;> simp [inl]
      rw [hconst]
      exact hlin.add_const (0, a)
    have hAderiv :
        HasFDerivAt (A : B × P → V)
          (fderiv ℝ (A : B × P → V) (b', a)) (b', a) :=
      A.differentiableAt.hasFDerivAt
    simpa [inl] using hAderiv.comp b' hinner
  simpa [mixedRealFiberIntegralRaw] using
    (hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := (MeasureTheory.volume : MeasureTheory.Measure P))
      (s := (Set.univ : Set B))
      (x₀ := b)
      (F := fun b' a => A (b', a))
      (F' := fun b' a => mixedBaseFDerivSchwartz A (b', a))
      hs hA_meas hA_int hA'_meas h_bound hbound_int h_diff)

/-- The Fréchet derivative of the mixed raw fiber integral is the mixed fiber
integral of the mixed-base derivative field. -/
theorem fderiv_mixedRealFiberIntegralRaw_eq {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (A : SchwartzMap
      ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) V) :
    fderiv ℝ (mixedRealFiberIntegralRaw A) =
      mixedRealFiberIntegralRaw (mixedBaseFDerivSchwartz A) := by
  funext b
  exact (hasFDerivAt_mixedRealFiberIntegralRaw A b).fderiv

/-- Continuity of the mixed raw fiber integral. -/
theorem continuous_mixedRealFiberIntegralRaw {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (A : SchwartzMap
      ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) V) :
    Continuous (mixedRealFiberIntegralRaw A) :=
  continuous_iff_continuousAt.2 fun b =>
    (hasFDerivAt_mixedRealFiberIntegralRaw A b).continuousAt

theorem contDiff_nat_mixedRealFiberIntegralRaw {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (r : ℕ)
    (A : SchwartzMap
      ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) V) :
    ContDiff ℝ r (mixedRealFiberIntegralRaw A) := by
  induction r generalizing V A with
  | zero =>
      exact contDiff_zero.2 (continuous_mixedRealFiberIntegralRaw A)
  | succ r ihr =>
      exact (contDiff_succ_iff_hasFDerivAt (𝕜 := ℝ) (n := r)
        (f := mixedRealFiberIntegralRaw A)).2 <| by
        refine ⟨mixedRealFiberIntegralRaw (mixedBaseFDerivSchwartz A), ?_, ?_⟩
        · exact ihr (A := mixedBaseFDerivSchwartz A)
        · intro b
          exact hasFDerivAt_mixedRealFiberIntegralRaw A b

/-- Smoothness of the mixed raw fiber integral. -/
theorem contDiff_mixedRealFiberIntegralRaw {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (A : SchwartzMap
      ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) V) :
    ContDiff ℝ (⊤ : ℕ∞) (mixedRealFiberIntegralRaw A) := by
  rw [contDiff_infty]
  intro r
  exact contDiff_nat_mixedRealFiberIntegralRaw r A

/-- Schwartz decay of all mixed-base derivatives of the raw fiber integral. -/
theorem decay_mixedRealFiberIntegralRaw {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (A : SchwartzMap
      ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) V)
    (k r : ℕ) :
    ∃ C, ∀ b : ComplexChartSpace m × (Fin m → ℝ),
      ‖b‖ ^ k * ‖iteratedFDeriv ℝ r (mixedRealFiberIntegralRaw A) b‖ ≤ C := by
  induction r generalizing V A with
  | zero =>
      obtain ⟨C, hC⟩ := exists_norm_pow_mul_mixedRealFiberIntegralRaw_le A k
      refine ⟨C, fun b => ?_⟩
      simpa [norm_iteratedFDeriv_zero] using hC b
  | succ r ihr =>
      obtain ⟨C, hC⟩ := ihr (A := mixedBaseFDerivSchwartz A)
      refine ⟨C, fun b => ?_⟩
      calc
        ‖b‖ ^ k * ‖iteratedFDeriv ℝ (r + 1) (mixedRealFiberIntegralRaw A) b‖
            = ‖b‖ ^ k *
                ‖iteratedFDeriv ℝ r (fderiv ℝ (mixedRealFiberIntegralRaw A)) b‖ := by
              rw [norm_iteratedFDeriv_fderiv]
        _ = ‖b‖ ^ k *
              ‖iteratedFDeriv ℝ r
                (mixedRealFiberIntegralRaw (mixedBaseFDerivSchwartz A)) b‖ := by
              rw [fderiv_mixedRealFiberIntegralRaw_eq]
        _ ≤ C := hC b

/-- Uniform zeroth-derivative seminorm bound for the mixed real-fiber
integral. -/
theorem exists_seminorm_bound_mixedRealFiberIntegralRaw_zero {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
    [SMulCommClass ℝ ℂ V] [CompleteSpace V]
    (k : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : SchwartzMap
          ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) V)
        (b : ComplexChartSpace m × (Fin m → ℝ)),
        ‖b‖ ^ k * ‖mixedRealFiberIntegralRaw A b‖ ≤
          C * s.sup (schwartzSeminormFamily ℂ
            ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) V) A := by
  let B := ComplexChartSpace m × (Fin m → ℝ)
  let P := Fin m → ℝ
  let μ : Measure P := volume
  let s : Finset (ℕ × ℕ) := {(k, 0), (k + μ.integrablePower, 0)}
  let Aconst : ℝ :=
    2 ^ μ.integrablePower *
      ∫ a : P, (1 + ‖a‖) ^ (-(μ.integrablePower : ℝ))
  refine ⟨s, 2 * Aconst, ?_, ?_⟩
  · dsimp [Aconst]
    positivity
  · intro F b
    let C₁ : ℝ := SchwartzMap.seminorm ℂ k 0 F
    let C₂ : ℝ := SchwartzMap.seminorm ℂ (k + μ.integrablePower) 0 F
    let S : ℝ := s.sup (schwartzSeminormFamily ℂ (B × P) V) F
    have hC₁_le : C₁ ≤ S := by
      have hmem : ((k, 0) : ℕ × ℕ) ∈ s := by simp [s]
      exact (show (schwartzSeminormFamily ℂ (B × P) V ((k, 0) : ℕ × ℕ)) F ≤ S from
        (Finset.le_sup (f := schwartzSeminormFamily ℂ (B × P) V) hmem) F)
    have hC₂_le : C₂ ≤ S := by
      have hmem : ((k + μ.integrablePower, 0) : ℕ × ℕ) ∈ s := by simp [s]
      exact (show
        (schwartzSeminormFamily ℂ (B × P) V
          ((k + μ.integrablePower, 0) : ℕ × ℕ)) F ≤ S from
        (Finset.le_sup (f := schwartzSeminormFamily ℂ (B × P) V) hmem) F)
    have hbound :
        ∫ a : P, ‖a‖ ^ 0 * ‖(‖b‖ ^ k : ℝ) • F (b, a)‖ ∂μ ≤
          Aconst * (C₁ + C₂) := by
      refine integral_pow_mul_le_of_le_of_pow_mul_le (μ := μ) (k := 0)
        (f := fun a : P => (‖b‖ ^ k : ℝ) • F (b, a))
        (C₁ := C₁) (C₂ := C₂) ?hf ?hpow
      · intro a
        have hb_norm : ‖b‖ ≤ ‖(b, a)‖ := by
          rw [Prod.norm_def]
          exact le_max_left ‖b‖ ‖a‖
        have hbpow : ‖b‖ ^ k ≤ ‖(b, a)‖ ^ k :=
          pow_le_pow_left₀ (norm_nonneg _) hb_norm _
        have h := SchwartzMap.le_seminorm ℂ k 0 F (b, a)
        have h' : ‖(b, a)‖ ^ k * ‖F (b, a)‖ ≤ C₁ := by
          simpa [C₁] using h
        calc
          ‖(‖b‖ ^ k : ℝ) • F (b, a)‖ =
              ‖b‖ ^ k * ‖F (b, a)‖ := by
            rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg b) k)]
          _ ≤ ‖(b, a)‖ ^ k * ‖F (b, a)‖ :=
            mul_le_mul_of_nonneg_right hbpow (norm_nonneg _)
          _ ≤ C₁ := h'
      · intro a
        have hb_norm : ‖b‖ ≤ ‖(b, a)‖ := by
          rw [Prod.norm_def]
          exact le_max_left ‖b‖ ‖a‖
        have ha_norm : ‖a‖ ≤ ‖(b, a)‖ := by
          rw [Prod.norm_def]
          exact le_max_right ‖b‖ ‖a‖
        have hprod : ‖a‖ ^ (0 + μ.integrablePower) * ‖b‖ ^ k ≤
            ‖(b, a)‖ ^ (k + μ.integrablePower) := by
          have ha_pow :
              ‖a‖ ^ μ.integrablePower ≤ ‖(b, a)‖ ^ μ.integrablePower :=
            pow_le_pow_left₀ (norm_nonneg _) ha_norm _
          have hb_pow : ‖b‖ ^ k ≤ ‖(b, a)‖ ^ k :=
            pow_le_pow_left₀ (norm_nonneg _) hb_norm _
          calc
            ‖a‖ ^ (0 + μ.integrablePower) * ‖b‖ ^ k =
                ‖a‖ ^ μ.integrablePower * ‖b‖ ^ k := by simp
            _ ≤ ‖(b, a)‖ ^ μ.integrablePower * ‖(b, a)‖ ^ k :=
              mul_le_mul ha_pow hb_pow (pow_nonneg (norm_nonneg _) _)
                (pow_nonneg (norm_nonneg _) _)
            _ = ‖(b, a)‖ ^ (μ.integrablePower + k) := by rw [pow_add]
            _ = ‖(b, a)‖ ^ (k + μ.integrablePower) := by rw [add_comm]
        have h := SchwartzMap.le_seminorm ℂ (k + μ.integrablePower) 0 F (b, a)
        have h' : ‖(b, a)‖ ^ (k + μ.integrablePower) * ‖F (b, a)‖ ≤ C₂ := by
          simpa [C₂] using h
        calc
          ‖a‖ ^ (0 + μ.integrablePower) *
              ‖(‖b‖ ^ k : ℝ) • F (b, a)‖
              = (‖a‖ ^ (0 + μ.integrablePower) * ‖b‖ ^ k) *
                  ‖F (b, a)‖ := by
                rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg b) k)]
                ring
          _ ≤ ‖(b, a)‖ ^ (k + μ.integrablePower) * ‖F (b, a)‖ :=
            mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
          _ ≤ C₂ := h'
    have hnorm_int :
        ‖mixedRealFiberIntegralRaw F b‖ ≤ ∫ a : P, ‖F (b, a)‖ := by
      simpa [mixedRealFiberIntegralRaw, μ] using
        (norm_integral_le_integral_norm (μ := μ) (f := fun a : P => F (b, a)))
    calc
      ‖b‖ ^ k * ‖mixedRealFiberIntegralRaw F b‖
          ≤ ‖b‖ ^ k * ∫ a : P, ‖F (b, a)‖ := by
            gcongr
      _ = ∫ a : P, ‖b‖ ^ k * ‖F (b, a)‖ := by
            rw [← integral_const_mul]
      _ = ∫ a : P, ‖a‖ ^ 0 *
              ‖(‖b‖ ^ k : ℝ) • F (b, a)‖ ∂μ := by
            apply integral_congr_ae
            filter_upwards with a
            rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg b) k)]
            simp
      _ ≤ Aconst * (C₁ + C₂) := hbound
      _ ≤ Aconst * (2 * S) := by
            gcongr
            linarith
      _ = 2 * Aconst * S := by ring

/-- Precomposition with the mixed-base inclusion on real-linear maps, viewed as
a complex-linear continuous map because the scalar action is on the codomain. -/
def mixedBasePrecompCLM {m : ℕ}
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
    [SMulCommClass ℝ ℂ V] :
    (((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) →L[ℝ] V) →L[ℂ]
      ((ComplexChartSpace m × (Fin m → ℝ)) →L[ℝ] V) := by
  let B := ComplexChartSpace m × (Fin m → ℝ)
  let P := Fin m → ℝ
  let inl : B →L[ℝ] B × P := ContinuousLinearMap.inl ℝ B P
  let Llin : ((B × P) →L[ℝ] V) →ₗ[ℂ] (B →L[ℝ] V) :=
    { toFun := fun T => T.comp inl
      map_add' := by
        intro T U
        apply ContinuousLinearMap.ext
        intro b
        rfl
      map_smul' := by
        intro c T
        apply ContinuousLinearMap.ext
        intro b
        rfl }
  exact Llin.mkContinuous 1 (by
    intro T
    have hcomp : ‖T.comp inl‖ ≤ ‖T‖ * ‖inl‖ := T.opNorm_comp_le inl
    have hinl : ‖inl‖ ≤ (1 : ℝ) := by
      simpa [inl] using ContinuousLinearMap.norm_inl_le_one ℝ B P
    calc
      ‖Llin T‖ = ‖T.comp inl‖ := rfl
      _ ≤ ‖T‖ * ‖inl‖ := hcomp
      _ ≤ 1 * ‖T‖ := by
        rw [one_mul]
        exact mul_le_of_le_one_right (norm_nonneg T) hinl
      _ = 1 * ‖T‖ := rfl)

@[simp]
theorem mixedBasePrecompCLM_apply {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
    [SMulCommClass ℝ ℂ V]
    (T : (((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) →L[ℝ] V)) :
    mixedBasePrecompCLM (m := m) V T =
      T.comp (ContinuousLinearMap.inl ℝ
        (ComplexChartSpace m × (Fin m → ℝ)) (Fin m → ℝ)) := by
  rfl

/-- The mixed-base derivative field as a continuous complex-linear map on the
triple Schwartz space. -/
def mixedBaseFDerivSchwartzCLM {m : ℕ}
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
    [SMulCommClass ℝ ℂ V] [CompleteSpace V] :
    SchwartzMap
      ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) V →L[ℂ]
      SchwartzMap
        ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ))
        ((ComplexChartSpace m × (Fin m → ℝ)) →L[ℝ] V) :=
  (SchwartzMap.postcompCLM (mixedBasePrecompCLM (m := m) V)).comp
    (SchwartzMap.fderivCLM ℂ
      ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) V)

@[simp]
theorem mixedBaseFDerivSchwartzCLM_apply {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
    [SMulCommClass ℝ ℂ V] [CompleteSpace V]
    (A : SchwartzMap
      ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) V) :
    mixedBaseFDerivSchwartzCLM V A = mixedBaseFDerivSchwartz A := by
  ext p v <;>
    simp [mixedBaseFDerivSchwartzCLM, mixedBasePrecompCLM, mixedBaseFDerivSchwartz]

/-- Finite-supremum Schwartz seminorms of the mixed-base derivative field are
controlled by finitely many Schwartz seminorms of the original triple test. -/
theorem exists_seminorm_bound_mixedBaseFDerivSchwartz {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
    [SMulCommClass ℝ ℂ V] [CompleteSpace V]
    (s0 : Finset (ℕ × ℕ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ A : SchwartzMap
          ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) V,
        s0.sup (schwartzSeminormFamily ℂ
          ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ))
          ((ComplexChartSpace m × (Fin m → ℝ)) →L[ℝ] V))
          (mixedBaseFDerivSchwartz A) ≤
        C * s.sup (schwartzSeminormFamily ℂ
          ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) V) A := by
  let D := (ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)
  let B := ComplexChartSpace m × (Fin m → ℝ)
  let L := mixedBaseFDerivSchwartzCLM (m := m) V
  let p := schwartzSeminormFamily ℂ D V
  let q := schwartzSeminormFamily ℂ D (B →L[ℝ] V)
  have hbounded : Seminorm.IsBounded p q L.toLinearMap := by
    intro i
    let qi : Seminorm ℂ (SchwartzMap D V) := (q i).comp L.toLinearMap
    have hqi_cont : Continuous qi := by
      exact ((schwartz_withSeminorms ℂ D (B →L[ℝ] V)).continuous_seminorm i).comp
        L.continuous
    obtain ⟨s, C, _hCne, hbound⟩ :=
      Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ D V) qi hqi_cont
    exact ⟨s, C, hbound⟩
  obtain ⟨Cnn, s, hsup⟩ := Seminorm.isBounded_sup hbounded s0
  refine ⟨s, (Cnn : ℝ), Cnn.2, ?_⟩
  intro A
  have h := Seminorm.le_def.mp hsup A
  simpa [L, p, q] using h

/-- Uniform finite-seminorm bound for every mixed-base derivative of the real
fiber integral. -/
theorem exists_seminorm_bound_mixedRealFiberIntegralRaw_deriv {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
    [SMulCommClass ℝ ℂ V] [CompleteSpace V]
    (k n : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : SchwartzMap
          ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) V)
        (b : ComplexChartSpace m × (Fin m → ℝ)),
        ‖b‖ ^ k *
          ‖iteratedFDeriv ℝ n (mixedRealFiberIntegralRaw A) b‖ ≤
        C * s.sup (schwartzSeminormFamily ℂ
          ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) V) A := by
  induction n generalizing V with
  | zero =>
      obtain ⟨s, C, hC, hbound⟩ :=
        exists_seminorm_bound_mixedRealFiberIntegralRaw_zero (m := m) (V := V) k
      refine ⟨s, C, hC, ?_⟩
      intro A b
      simpa [norm_iteratedFDeriv_zero] using hbound A b
  | succ n ih =>
      obtain ⟨s0, C0, hC0, hIH⟩ :=
        ih (V := (ComplexChartSpace m × (Fin m → ℝ)) →L[ℝ] V)
      obtain ⟨s, C1, hC1, hbase⟩ :=
        exists_seminorm_bound_mixedBaseFDerivSchwartz (m := m) (V := V) s0
      refine ⟨s, C0 * C1, mul_nonneg hC0 hC1, ?_⟩
      intro A b
      calc
        ‖b‖ ^ k *
            ‖iteratedFDeriv ℝ (n + 1) (mixedRealFiberIntegralRaw A) b‖
            = ‖b‖ ^ k *
                ‖iteratedFDeriv ℝ n
                  (fderiv ℝ (mixedRealFiberIntegralRaw A)) b‖ := by
              rw [norm_iteratedFDeriv_fderiv]
        _ = ‖b‖ ^ k *
              ‖iteratedFDeriv ℝ n
                (mixedRealFiberIntegralRaw (mixedBaseFDerivSchwartz A)) b‖ := by
              rw [fderiv_mixedRealFiberIntegralRaw_eq]
        _ ≤ C0 * s0.sup (schwartzSeminormFamily ℂ
              ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ))
              ((ComplexChartSpace m × (Fin m → ℝ)) →L[ℝ] V))
              (mixedBaseFDerivSchwartz A) :=
            hIH (mixedBaseFDerivSchwartz A) b
        _ ≤ C0 * (C1 * s.sup (schwartzSeminormFamily ℂ
              ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) V) A) := by
            gcongr
            exact hbase A
        _ = (C0 * C1) * s.sup (schwartzSeminormFamily ℂ
              ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) V) A := by
            ring

/-- Mixed real-fiber integration over the last real parameter as a continuous
complex-linear map of Schwartz spaces. -/
noncomputable def mixedRealFiberIntegralCLM {m : ℕ} :
    SchwartzMap
      ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) ℂ →L[ℂ]
      SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ :=
  SchwartzMap.mkCLM (𝕜 := ℂ) (𝕜' := ℂ)
    (fun A b => ∫ a : Fin m → ℝ, A (b, a))
    (fun A B b => by
      simpa using
        (integral_add (integrable_mixedRealFiber A b) (integrable_mixedRealFiber B b)))
    (fun c A b => by
      simpa using
        (integral_const_mul (μ := (volume : Measure (Fin m → ℝ))) c
          (fun a : Fin m → ℝ => A (b, a))))
    (fun A => contDiff_mixedRealFiberIntegralRaw A)
    (fun kn => by
      rcases kn with ⟨k, n⟩
      simpa using
        (exists_seminorm_bound_mixedRealFiberIntegralRaw_deriv (m := m) (V := ℂ) k n))

@[simp]
theorem mixedRealFiberIntegralCLM_apply {m : ℕ}
    (A : SchwartzMap
      ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) ℂ)
    (z : ComplexChartSpace m) (t : Fin m → ℝ) :
    mixedRealFiberIntegralCLM A (z, t) =
      ∫ a : Fin m → ℝ, A ((z, t), a) := by
  rfl

/-- Split tensors for the mixed base/fiber decomposition used in scalarization. -/
def mixedBaseFiberTensor {m : ℕ}
    (G : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ)
    (ξ : SchwartzMap (Fin m → ℝ) ℂ) :
    SchwartzMap
      ((ComplexChartSpace m × (Fin m → ℝ)) × (Fin m → ℝ)) ℂ :=
  schwartzExternalProduct G ξ

@[simp]
theorem mixedBaseFiberTensor_apply {m : ℕ}
    (G : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ)
    (ξ : SchwartzMap (Fin m → ℝ) ℂ)
    (b : ComplexChartSpace m × (Fin m → ℝ)) (a : Fin m → ℝ) :
    mixedBaseFiberTensor G ξ (b, a) = G b * ξ a := by
  rfl

@[simp]
theorem schwartzPartialEval₂CLM_mixedBaseFiberTensor {m : ℕ}
    (a : Fin m → ℝ)
    (G : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ)
    (ξ : SchwartzMap (Fin m → ℝ) ℂ) :
    schwartzPartialEval₂CLM a (mixedBaseFiberTensor G ξ) =
      ξ a • G := by
  ext b
  rcases b with ⟨z, t⟩
  simp [mixedBaseFiberTensor, smul_eq_mul, mul_comm]

@[simp]
theorem mixedRealFiberIntegralCLM_mixedBaseFiberTensor {m : ℕ}
    (G : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ)
    (ξ : SchwartzMap (Fin m → ℝ) ℂ) :
    mixedRealFiberIntegralCLM (mixedBaseFiberTensor G ξ) =
      (∫ a : Fin m → ℝ, ξ a) • G := by
  ext b
  rcases b with ⟨z, t⟩
  rw [mixedRealFiberIntegralCLM_apply]
  simp only [mixedBaseFiberTensor_apply]
  calc
    ∫ a : Fin m → ℝ, G (z, t) * ξ a =
        G (z, t) * ∫ a : Fin m → ℝ, ξ a := by
      simpa [smul_eq_mul] using
        (integral_const_mul (μ := (volume : Measure (Fin m → ℝ)))
          (G (z, t)) (fun a : Fin m → ℝ => ξ a))
    _ = ((∫ a : Fin m → ℝ, ξ a) • G) (z, t) := by
      simp [smul_eq_mul, mul_comm]

end SCV
