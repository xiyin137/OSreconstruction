/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.DistributionalUniqueness
import OSReconstruction.SCV.SchwartzPartialEval
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Kernel Substrate for Local Distributional Edge-of-the-Wedge

This file contains the QFT-free Schwartz-space infrastructure needed for the
Streater-Wightman/Jost distributional edge-of-the-wedge regularization route.
It deliberately introduces only honest definitions and checked elementary
adapters; the kernel theorem, descent, and distributional-holomorphic
regularity statements are deferred until their proofs are implemented.
-/

noncomputable section

open Complex MeasureTheory

namespace SCV

variable {m : ℕ}

/-- The complex coordinate chart used in local SCV edge-of-the-wedge arguments. -/
abbrev ComplexChartSpace (m : ℕ) := Fin m → ℂ

/-- A Schwartz test function whose topological support lies in an open set. -/
def SupportsInOpen
    {E : Type*} [TopologicalSpace E]
    (φ : E → ℂ) (U : Set E) : Prop :=
  HasCompactSupport φ ∧ tsupport φ ⊆ U

/-- A real-kernel support predicate for fixed-radius regularization kernels. -/
def KernelSupportWithin {m : ℕ}
    (ψ : SchwartzMap (Fin m → ℝ) ℂ) (r : ℝ) : Prop :=
  tsupport (ψ : (Fin m → ℝ) → ℂ) ⊆ Metric.closedBall 0 r

/-- Kernel support is monotone in the support radius. -/
theorem KernelSupportWithin.mono {m : ℕ}
    {ψ : SchwartzMap (Fin m → ℝ) ℂ} {r R : ℝ}
    (hψ : KernelSupportWithin ψ r) (hrR : r ≤ R) :
    KernelSupportWithin ψ R := by
  intro x hx
  exact Metric.closedBall_subset_closedBall hrR (hψ hx)

/-- The real coordinate direction in the complex chart. -/
def complexRealDir {m : ℕ} (j : Fin m) : ComplexChartSpace m :=
  fun k => if k = j then 1 else 0

/-- The imaginary coordinate direction in the complex chart. -/
def complexImagDir {m : ℕ} (j : Fin m) : ComplexChartSpace m :=
  fun k => if k = j then Complex.I else 0

/-- Directional derivative on complex-chart Schwartz functions, viewing the
complex chart as a real finite-dimensional normed vector space. -/
def directionalDerivSchwartzCLM {m : ℕ} (v : ComplexChartSpace m) :
    SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ]
      SchwartzMap (ComplexChartSpace m) ℂ :=
  LineDeriv.lineDerivOpCLM ℂ (SchwartzMap (ComplexChartSpace m) ℂ) v

/-- The test-function Cauchy-Riemann operator `∂/∂\bar z_j` on Schwartz space. -/
def dbarSchwartzCLM {m : ℕ} (j : Fin m) :
    SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ]
      SchwartzMap (ComplexChartSpace m) ℂ :=
  (1 / 2 : ℂ) •
    (directionalDerivSchwartzCLM (complexRealDir j) +
      Complex.I • directionalDerivSchwartzCLM (complexImagDir j))

/-- Distributional holomorphy on a complex domain, expressed by vanishing of
all `∂/∂\bar z_j` test derivatives supported in the domain. -/
def IsDistributionalHolomorphicOn {m : ℕ}
    (T : SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ] ℂ)
    (U : Set (ComplexChartSpace m)) : Prop :=
  ∀ j : Fin m,
    ∀ φ : SchwartzMap (ComplexChartSpace m) ℂ,
      SupportsInOpen (φ : ComplexChartSpace m → ℂ) U →
        T (dbarSchwartzCLM j φ) = 0

/-- A holomorphic function represents a complex-chart distribution on tests
supported in `U` when integration against the function agrees with the
distribution on those tests. -/
def RepresentsDistributionOnComplexDomain {m : ℕ}
    (T : SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ] ℂ)
    (H : ComplexChartSpace m → ℂ)
    (U : Set (ComplexChartSpace m)) : Prop :=
  ∀ φ : SchwartzMap (ComplexChartSpace m) ℂ,
    SupportsInOpen (φ : ComplexChartSpace m → ℂ) U →
      T φ = ∫ z : ComplexChartSpace m, H z * φ z

/-- Real translation of complex-chart Schwartz tests as a continuous linear map:
`φ ↦ (z ↦ φ (z + realEmbed a))`. -/
def complexTranslateSchwartzCLM {m : ℕ} (a : Fin m → ℝ) :
    SchwartzMap (ComplexChartSpace m) ℂ →L[ℂ]
      SchwartzMap (ComplexChartSpace m) ℂ := by
  let g : ComplexChartSpace m → ComplexChartSpace m := fun z => z + realEmbed a
  have hg : g.HasTemperateGrowth := by
    fun_prop
  have hg_upper :
      ∃ (k : ℕ) (C : ℝ), ∀ z, ‖z‖ ≤ C * (1 + ‖g z‖) ^ k := by
    refine ⟨1, 1 + ‖realEmbed a‖, ?_⟩
    intro z
    have htri : ‖z‖ ≤ ‖g z‖ + ‖realEmbed a‖ := by
      calc
        ‖z‖ = ‖(z + realEmbed a) - realEmbed a‖ := by
          simp
        _ ≤ ‖g z‖ + ‖realEmbed a‖ := by
          simpa [g] using norm_sub_le (z + realEmbed a) (realEmbed a)
    have hfac : ‖g z‖ + ‖realEmbed a‖ ≤ (1 + ‖realEmbed a‖) * (1 + ‖g z‖) := by
      nlinarith [norm_nonneg (g z), norm_nonneg (realEmbed a)]
    simpa using le_trans htri hfac
  exact SchwartzMap.compCLM (𝕜 := ℂ) (g := g) hg hg_upper

/-- Real translation of complex-chart Schwartz tests:
`(complexTranslateSchwartz a φ) z = φ (z + realEmbed a)`. -/
def complexTranslateSchwartz {m : ℕ}
    (a : Fin m → ℝ)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
    SchwartzMap (ComplexChartSpace m) ℂ :=
  complexTranslateSchwartzCLM a φ

@[simp]
theorem complexTranslateSchwartz_apply {m : ℕ}
    (a : Fin m → ℝ)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (z : ComplexChartSpace m) :
    complexTranslateSchwartz a φ z = φ (z + realEmbed a) := by
  rfl

@[simp]
theorem complexTranslateSchwartzCLM_apply {m : ℕ}
    (a : Fin m → ℝ)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
    complexTranslateSchwartzCLM a φ = complexTranslateSchwartz a φ := rfl

/-- Product norm is controlled by the sum of the coordinate norms. -/
private theorem norm_prod_le_fst_add_snd
    {E₁ E₂ : Type*} [SeminormedAddCommGroup E₁] [SeminormedAddCommGroup E₂]
    (x : E₁ × E₂) :
    ‖x‖ ≤ ‖x.1‖ + ‖x.2‖ := by
  rw [Prod.norm_def]
  exact max_le (le_add_of_nonneg_right (norm_nonneg _))
    (le_add_of_nonneg_left (norm_nonneg _))

/-- The external product of two Schwartz functions on a Cartesian product.

This is kept private in the theorem-2 kernel substrate so the public surface
stays the mixed `ComplexChartSpace m × (Fin m → ℝ)` tensor product needed by
the Streater-Wightman argument. -/
private def schwartzTensorProductRaw
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

/-- The two-space Schwartz tensor product needed by the local distributional
edge-of-the-wedge kernel theorem. -/
def schwartzTensorProduct₂ {m : ℕ}
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ) :
    SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ :=
  schwartzTensorProductRaw φ ψ

@[simp]
theorem schwartzTensorProduct₂_apply {m : ℕ}
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (z : ComplexChartSpace m) (t : Fin m → ℝ) :
    schwartzTensorProduct₂ φ ψ (z, t) = φ z * ψ t := by
  rfl

/-- Partial evaluation of a mixed chart/fiber Schwartz test at a fixed chart
point, as a continuous linear map in the ambient Schwartz test. -/
def schwartzPartialEval₁CLM {m : ℕ} (z : ComplexChartSpace m) :
    SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ]
      SchwartzMap (Fin m → ℝ) ℂ := by
  let g : (Fin m → ℝ) → ComplexChartSpace m × (Fin m → ℝ) := fun t => (z, t)
  have hg : g.HasTemperateGrowth := by
    have hconst : Function.HasTemperateGrowth
        (fun _ : Fin m → ℝ => ((z, 0) : ComplexChartSpace m × (Fin m → ℝ))) :=
      Function.HasTemperateGrowth.const _
    have hlin : Function.HasTemperateGrowth
        (⇑(ContinuousLinearMap.inr ℝ (ComplexChartSpace m) (Fin m → ℝ))) :=
      (ContinuousLinearMap.inr ℝ (ComplexChartSpace m) (Fin m → ℝ)).hasTemperateGrowth
    convert hconst.add hlin using 1
    ext t <;> simp [g, ContinuousLinearMap.inr_apply, Prod.add_def]
  have hg_upper : ∃ (k : ℕ) (C : ℝ), ∀ t, ‖t‖ ≤ C * (1 + ‖g t‖) ^ k := by
    refine ⟨1, 1, ?_⟩
    intro t
    have ht : ‖t‖ ≤ ‖g t‖ := by
      simp [g, Prod.norm_def]
    have hnonneg : 0 ≤ ‖g t‖ := norm_nonneg _
    nlinarith
  exact SchwartzMap.compCLM (𝕜 := ℂ) (g := g) hg hg_upper

@[simp]
theorem schwartzPartialEval₁CLM_apply {m : ℕ} (z : ComplexChartSpace m)
    (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ)
    (t : Fin m → ℝ) :
    schwartzPartialEval₁CLM z F t = F (z, t) := by
  rfl

@[simp]
theorem schwartzPartialEval₁CLM_tensorProduct₂ {m : ℕ} (z : ComplexChartSpace m)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ) :
    schwartzPartialEval₁CLM z (schwartzTensorProduct₂ φ ψ) =
      φ z • ψ := by
  ext t
  simp [schwartzTensorProduct₂_apply]

/-- Partial evaluation at a fixed chart point is bounded by the corresponding
mixed Schwartz seminorm with the same weight and derivative order. -/
theorem schwartzPartialEval₁CLM_seminorm_le {m : ℕ} (z : ComplexChartSpace m)
    (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ)
    (k l : ℕ) :
    SchwartzMap.seminorm ℂ k l (schwartzPartialEval₁CLM z F) ≤
      SchwartzMap.seminorm ℂ k l F := by
  apply SchwartzMap.seminorm_le_bound ℂ k l _ (apply_nonneg _ _)
  intro t
  calc
    ‖t‖ ^ k * ‖iteratedFDeriv ℝ l (fun x => (schwartzPartialEval₁CLM z F) x) t‖
        ≤ ‖t‖ ^ k * ‖iteratedFDeriv ℝ l (⇑F) (z, t)‖ := by
          apply mul_le_mul_of_nonneg_left
          · simpa [schwartzPartialEval₁CLM_apply]
              using norm_iteratedFDeriv_partialEval₁_le (f := F) z l t
          · positivity
    _ ≤ ‖(z, t)‖ ^ k * ‖iteratedFDeriv ℝ l (⇑F) (z, t)‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          gcongr
          simp [Prod.norm_def]
    _ ≤ SchwartzMap.seminorm ℂ k l F :=
          SchwartzMap.le_seminorm ℂ k l F (z, t)

/-- Uniform finite-seminorm control for partial evaluation on a compact chart
window.  The proof is pointwise in the chart variable, so the compact radius is
kept only to match the downstream local-EOW API. -/
theorem schwartzPartialEval₁CLM_compactSeminormBound {m : ℕ}
    (R : ℝ) (_hR : 0 ≤ R) (s : Finset (ℕ × ℕ)) :
    ∃ s' : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ Metric.closedBall (0 : ComplexChartSpace m) R,
      ∀ F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ,
        s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)
            (schwartzPartialEval₁CLM z F) ≤
          C * s'.sup
            (schwartzSeminormFamily ℂ
              (ComplexChartSpace m × (Fin m → ℝ)) ℂ) F := by
  refine ⟨s, 1, zero_le_one, ?_⟩
  intro z _ F
  rw [one_mul]
  apply Seminorm.finset_sup_apply_le
  · exact apply_nonneg _ _
  · intro a ha
    rcases a with ⟨k, l⟩
    exact (schwartzPartialEval₁CLM_seminorm_le (z := z) (F := F) k l).trans
      ((Seminorm.le_finset_sup_apply
        (p := schwartzSeminormFamily ℂ (ComplexChartSpace m × (Fin m → ℝ)) ℂ)
        (s := s) (x := F) ha))

/-- Partial evaluation at a varying chart point is continuous in the Schwartz
topology of the real-kernel variable. -/
theorem continuous_schwartzPartialEval₁CLM {m : ℕ}
    (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ) :
    Continuous (fun z : ComplexChartSpace m => schwartzPartialEval₁CLM z F) := by
  have hcont :
      Continuous (fun z : ComplexChartSpace m => schwartzPartialEval₁ F z) :=
    continuous_schwartzPartialEval₁ F
  have heq :
      (fun z : ComplexChartSpace m => schwartzPartialEval₁CLM z F) =
        fun z : ComplexChartSpace m => schwartzPartialEval₁ F z := by
    funext z
    ext t
    simp [schwartzPartialEval₁CLM_apply, schwartzPartialEval₁_apply]
  simpa [heq] using hcont

/-- A continuous linear endomorphism of kernel Schwartz space transports any
finite family of output Schwartz seminorms to a finite family of input
seminorms. -/
theorem SchwartzMap.exists_schwartzCLM_finsetSeminormBound {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] SchwartzMap (Fin m → ℝ) ℂ)
    (s0 : Finset (ℕ × ℕ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
        s0.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ) (T ψ) ≤
          C * s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ) ψ := by
  let D := Fin m → ℝ
  let p := schwartzSeminormFamily ℂ D ℂ
  have hbounded : Seminorm.IsBounded p p T.toLinearMap := by
    intro i
    let qi : Seminorm ℂ (SchwartzMap D ℂ) := (p i).comp T.toLinearMap
    have hqi_cont : Continuous qi := by
      exact ((schwartz_withSeminorms ℂ D ℂ).continuous_seminorm i).comp T.continuous
    obtain ⟨s, C, _hCne, hbound⟩ :=
      Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ D ℂ) qi hqi_cont
    exact ⟨s, C, hbound⟩
  obtain ⟨Cnn, s, hsup⟩ := Seminorm.isBounded_sup hbounded s0
  refine ⟨s, (Cnn : ℝ), Cnn.2, ?_⟩
  intro ψ
  have h := Seminorm.le_def.mp hsup ψ
  simpa [D, p] using h

/-- The real embedding as a continuous real-linear map. -/
private def realEmbedCLM {m : ℕ} : (Fin m → ℝ) →L[ℝ] ComplexChartSpace m :=
  ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)

private theorem realEmbedCLM_apply {m : ℕ} (t : Fin m → ℝ) :
    realEmbedCLM t = realEmbed t := by
  ext i
  simp [realEmbedCLM, realEmbed]

/-- The product-space shear that turns the external tensor product into the
real-direction convolution test. -/
private def realConvolutionShearLinearEquiv (m : ℕ) :
    (ComplexChartSpace m × (Fin m → ℝ)) ≃ₗ[ℝ]
      (ComplexChartSpace m × (Fin m → ℝ)) where
  toFun := fun p => (p.1 - realEmbedCLM p.2, p.2)
  invFun := fun p => (p.1 + realEmbedCLM p.2, p.2)
  map_add' := by
    intro x y
    ext : 1
    · simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
    · rfl
  map_smul' := by
    intro c x
    ext : 1
    · simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_sub]
      rfl
    · rfl
  left_inv := by
    intro p
    ext : 1
    · simp [sub_eq_add_neg, add_assoc]
    · rfl
  right_inv := by
    intro p
    ext : 1
    · simp [sub_eq_add_neg, add_assoc]
    · rfl

/-- Real-direction shear:
`(z,t) ↦ (z - realEmbed t, t)`. -/
def realConvolutionShearCLE (m : ℕ) :
    (ComplexChartSpace m × (Fin m → ℝ)) ≃L[ℝ]
      (ComplexChartSpace m × (Fin m → ℝ)) :=
  (realConvolutionShearLinearEquiv m).toContinuousLinearEquiv

@[simp]
theorem realConvolutionShearCLE_apply {m : ℕ}
    (z : ComplexChartSpace m) (t : Fin m → ℝ) :
    realConvolutionShearCLE m (z, t) = (z - realEmbed t, t) := by
  ext i <;> simp [realConvolutionShearCLE, realConvolutionShearLinearEquiv,
    realEmbedCLM_apply]

@[simp]
theorem realConvolutionShearCLE_symm_apply {m : ℕ}
    (z : ComplexChartSpace m) (t : Fin m → ℝ) :
    (realConvolutionShearCLE m).symm (z, t) = (z + realEmbed t, t) := by
  ext i <;> simp [realConvolutionShearCLE, realConvolutionShearLinearEquiv,
    realEmbedCLM_apply]

/-- Raw fiber integral over the real direction in the local EOW chart. -/
def complexRealFiberIntegralRaw {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) V)
    (z : ComplexChartSpace m) : V :=
  ∫ t : Fin m → ℝ, F (z, t)

@[simp]
theorem complexRealFiberIntegralRaw_apply {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) V)
    (z : ComplexChartSpace m) :
    complexRealFiberIntegralRaw F z = ∫ t : Fin m → ℝ, F (z, t) := by
  rfl

/-- Every fixed complex-chart fiber of a product-space Schwartz map is
Bochner integrable over the real direction. -/
theorem integrable_complexRealFiber {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) V)
    (z : ComplexChartSpace m) :
    Integrable (fun t : Fin m → ℝ => F (z, t)) := by
  let μ : Measure (Fin m → ℝ) := volume
  have hmeas : AEStronglyMeasurable (fun t : Fin m → ℝ => F (z, t)) μ := by
    have hcont_pair : Continuous fun t : Fin m → ℝ => (z, t) := by
      exact continuous_const.prodMk continuous_id
    exact (F.continuous.comp hcont_pair).aestronglyMeasurable
  have hnorm : Integrable (fun t : Fin m → ℝ => ‖t‖ ^ 0 * ‖F (z, t)‖) μ := by
    refine integrable_of_le_of_pow_mul_le
      (μ := μ) (f := fun t : Fin m → ℝ => F (z, t))
      (C₁ := SchwartzMap.seminorm ℝ 0 0 F)
      (C₂ := SchwartzMap.seminorm ℝ (0 + μ.integrablePower) 0 F) (k := 0)
      ?hf ?hpow hmeas
    · intro t
      have h := SchwartzMap.le_seminorm ℝ 0 0 F (z, t)
      simpa using h
    · intro t
      have ht_norm : ‖t‖ ≤ ‖(z, t)‖ := by
        rw [Prod.norm_def]
        exact le_max_right ‖z‖ ‖t‖
      have hpow_le :
          ‖t‖ ^ (0 + μ.integrablePower) ≤ ‖(z, t)‖ ^ (0 + μ.integrablePower) :=
        pow_le_pow_left₀ (norm_nonneg _) ht_norm _
      have h := SchwartzMap.le_seminorm ℝ (0 + μ.integrablePower) 0 F (z, t)
      have h' :
          ‖(z, t)‖ ^ (0 + μ.integrablePower) * ‖F (z, t)‖ ≤
            SchwartzMap.seminorm ℝ (0 + μ.integrablePower) 0 F := by
        simpa using h
      exact (mul_le_mul_of_nonneg_right hpow_le (norm_nonneg _)).trans h'
  rw [← integrable_norm_iff hmeas]
  simpa using hnorm

/-- The base-variable derivative field of a product-space Schwartz map. -/
def baseFDerivSchwartz {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) V) :
    SchwartzMap
      (ComplexChartSpace m × (Fin m → ℝ))
      (ComplexChartSpace m →L[ℝ] V) :=
  (SchwartzMap.postcompCLM
    ((ContinuousLinearMap.inl ℝ
      (ComplexChartSpace m) (Fin m → ℝ)).precomp V))
    (SchwartzMap.fderivCLM ℝ
      (ComplexChartSpace m × (Fin m → ℝ)) V F)

@[simp]
theorem baseFDerivSchwartz_apply {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) V)
    (z : ComplexChartSpace m) (t : Fin m → ℝ) :
    baseFDerivSchwartz F (z, t) =
      (fderiv ℝ (F : (ComplexChartSpace m × (Fin m → ℝ)) → V) (z, t)).comp
        (ContinuousLinearMap.inl ℝ (ComplexChartSpace m) (Fin m → ℝ)) := by
  simp [baseFDerivSchwartz]

/-- Zeroth-order weighted decay of the raw real-direction fiber integral. -/
theorem exists_norm_pow_mul_complexRealFiberIntegralRaw_le {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) V) (k : ℕ) :
    ∃ C, ∀ z : ComplexChartSpace m,
      ‖z‖ ^ k * ‖complexRealFiberIntegralRaw F z‖ ≤ C := by
  let μ : Measure (Fin m → ℝ) := volume
  let C₁ : ℝ := SchwartzMap.seminorm ℝ k 0 F
  let C₂ : ℝ := SchwartzMap.seminorm ℝ (k + μ.integrablePower) 0 F
  refine ⟨2 ^ μ.integrablePower *
      (∫ t : Fin m → ℝ, (1 + ‖t‖) ^ (-(μ.integrablePower : ℝ))) * (C₁ + C₂), ?_⟩
  intro z
  let c : ℝ := ‖z‖ ^ k
  have hc_nonneg : 0 ≤ c := pow_nonneg (norm_nonneg _) _
  have hbound :
      ∫ t : Fin m → ℝ, ‖t‖ ^ 0 * ‖c • F (z, t)‖ ∂μ ≤
        2 ^ μ.integrablePower *
          (∫ t : Fin m → ℝ, (1 + ‖t‖) ^ (-(μ.integrablePower : ℝ))) * (C₁ + C₂) := by
    refine integral_pow_mul_le_of_le_of_pow_mul_le (μ := μ) (k := 0)
      (f := fun t : Fin m → ℝ => c • F (z, t)) (C₁ := C₁) (C₂ := C₂) ?hf ?hpow
    · intro t
      have hz_norm : ‖z‖ ≤ ‖(z, t)‖ := by
        rw [Prod.norm_def]
        exact le_max_left ‖z‖ ‖t‖
      have hzpow : ‖z‖ ^ k ≤ ‖(z, t)‖ ^ k :=
        pow_le_pow_left₀ (norm_nonneg _) hz_norm _
      have h := SchwartzMap.le_seminorm ℝ k 0 F (z, t)
      have h' : ‖(z, t)‖ ^ k * ‖F (z, t)‖ ≤ C₁ := by
        simpa [C₁] using h
      calc
        ‖c • F (z, t)‖ = c * ‖F (z, t)‖ := by
          simp [c, norm_smul]
        _ = ‖z‖ ^ k * ‖F (z, t)‖ := rfl
        _ ≤ ‖(z, t)‖ ^ k * ‖F (z, t)‖ := by
          exact mul_le_mul_of_nonneg_right hzpow (norm_nonneg _)
        _ ≤ C₁ := h'
    · intro t
      have hz_norm : ‖z‖ ≤ ‖(z, t)‖ := by
        rw [Prod.norm_def]
        exact le_max_left ‖z‖ ‖t‖
      have ht_norm : ‖t‖ ≤ ‖(z, t)‖ := by
        rw [Prod.norm_def]
        exact le_max_right ‖z‖ ‖t‖
      have hprod : ‖t‖ ^ (0 + μ.integrablePower) * c ≤
          ‖(z, t)‖ ^ (k + μ.integrablePower) := by
        have ht_pow : ‖t‖ ^ μ.integrablePower ≤ ‖(z, t)‖ ^ μ.integrablePower :=
          pow_le_pow_left₀ (norm_nonneg _) ht_norm _
        have hz_pow : ‖z‖ ^ k ≤ ‖(z, t)‖ ^ k :=
          pow_le_pow_left₀ (norm_nonneg _) hz_norm _
        calc
          ‖t‖ ^ (0 + μ.integrablePower) * c = ‖t‖ ^ μ.integrablePower * ‖z‖ ^ k := by
            simp [c]
          _ ≤ ‖(z, t)‖ ^ μ.integrablePower * ‖(z, t)‖ ^ k :=
            mul_le_mul ht_pow hz_pow (pow_nonneg (norm_nonneg _) _) (pow_nonneg (norm_nonneg _) _)
          _ = ‖(z, t)‖ ^ (k + μ.integrablePower) := by
            rw [← pow_add]
            ring_nf
      have h := SchwartzMap.le_seminorm ℝ (k + μ.integrablePower) 0 F (z, t)
      have h' : ‖(z, t)‖ ^ (k + μ.integrablePower) * ‖F (z, t)‖ ≤ C₂ := by
        simpa [C₂] using h
      calc
        ‖t‖ ^ (0 + μ.integrablePower) * ‖c • F (z, t)‖
            = (‖t‖ ^ (0 + μ.integrablePower) * c) * ‖F (z, t)‖ := by
              simp [c, norm_smul, mul_assoc]
        _ ≤ ‖(z, t)‖ ^ (k + μ.integrablePower) * ‖F (z, t)‖ :=
          mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
        _ ≤ C₂ := h'
  have hnorm_int : ‖complexRealFiberIntegralRaw F z‖ ≤ ∫ t : Fin m → ℝ, ‖F (z, t)‖ := by
    simpa [complexRealFiberIntegralRaw, μ] using
      (norm_integral_le_integral_norm (μ := μ) (f := fun t : Fin m → ℝ => F (z, t)))
  calc
    ‖z‖ ^ k * ‖complexRealFiberIntegralRaw F z‖
        ≤ ‖z‖ ^ k * ∫ t : Fin m → ℝ, ‖F (z, t)‖ := by
          gcongr
    _ = ∫ t : Fin m → ℝ, ‖z‖ ^ k * ‖F (z, t)‖ := by
          rw [← integral_const_mul]
    _ = ∫ t : Fin m → ℝ, ‖t‖ ^ 0 * ‖c • F (z, t)‖ ∂μ := by
          apply integral_congr_ae
          filter_upwards with t
          simp [c, norm_smul]
    _ ≤ 2 ^ μ.integrablePower *
          (∫ t : Fin m → ℝ, (1 + ‖t‖) ^ (-(μ.integrablePower : ℝ))) * (C₁ + C₂) := hbound

/-- A single integrable real-direction bound for the base derivative field,
uniform in the complex-chart base point. -/
lemma exists_integrable_bound_baseFDerivSchwartz {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) V) :
    ∃ bound : (Fin m → ℝ) → ℝ,
      Integrable bound ∧
      ∀ z t, ‖baseFDerivSchwartz F (z, t)‖ ≤ bound t := by
  let μ : Measure (Fin m → ℝ) := volume
  let G : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) (ComplexChartSpace m →L[ℝ] V) :=
    baseFDerivSchwartz F
  let C₁ : ℝ := SchwartzMap.seminorm ℝ 0 0 G
  let C₂ : ℝ := SchwartzMap.seminorm ℝ (0 + μ.integrablePower) 0 G
  refine ⟨fun t => 2 ^ μ.integrablePower * (C₁ + C₂) *
      (1 + ‖t‖) ^ (-(μ.integrablePower : ℝ)), ?_, ?_⟩
  · simpa [mul_assoc, mul_comm, mul_left_comm] using
      (Measure.integrable_pow_neg_integrablePower μ).const_mul
        (2 ^ μ.integrablePower * (C₁ + C₂))
  · intro z t
    have h1 : ‖G (z, t)‖ ≤ C₁ := by
      have h := SchwartzMap.le_seminorm ℝ 0 0 G (z, t)
      simpa [G, C₁] using h
    have ht_norm : ‖t‖ ≤ ‖(z, t)‖ := by
      rw [Prod.norm_def]
      exact le_max_right ‖z‖ ‖t‖
    have hpow_le :
        ‖t‖ ^ (0 + μ.integrablePower) ≤ ‖(z, t)‖ ^ (0 + μ.integrablePower) :=
      pow_le_pow_left₀ (norm_nonneg _) ht_norm _
    have h2 : ‖t‖ ^ (0 + μ.integrablePower) * ‖G (z, t)‖ ≤ C₂ := by
      have h := SchwartzMap.le_seminorm ℝ (0 + μ.integrablePower) 0 G (z, t)
      have h' : ‖(z, t)‖ ^ (0 + μ.integrablePower) * ‖G (z, t)‖ ≤ C₂ := by
        simpa [G, C₂] using h
      exact (mul_le_mul_of_nonneg_right hpow_le (norm_nonneg _)).trans h'
    have hmain := pow_mul_le_of_le_of_pow_mul_le (k := 0) (l := μ.integrablePower)
      (x := ‖t‖) (f := ‖G (z, t)‖) (C₁ := C₁) (C₂ := C₂)
      (norm_nonneg _) (norm_nonneg _) h1 h2
    simpa [G, mul_assoc, mul_comm, mul_left_comm] using hmain

/-- Differentiation under the real-direction fiber integral. -/
theorem hasFDerivAt_complexRealFiberIntegralRaw {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) V)
    (z : ComplexChartSpace m) :
    HasFDerivAt (complexRealFiberIntegralRaw F)
      (complexRealFiberIntegralRaw (baseFDerivSchwartz F) z) z := by
  obtain ⟨bound, hbound_int, hbound⟩ := exists_integrable_bound_baseFDerivSchwartz F
  have hs : (Set.univ : Set (ComplexChartSpace m)) ∈ nhds z := Filter.univ_mem
  have hF_meas :
      ∀ᶠ z' in nhds z,
        AEStronglyMeasurable (fun t : Fin m → ℝ => F (z', t))
          (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)) := by
    exact Filter.Eventually.of_forall fun z' =>
      (integrable_complexRealFiber F z').aestronglyMeasurable
  have hF_int :
      Integrable (fun t : Fin m → ℝ => F (z, t))
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)) :=
    integrable_complexRealFiber F z
  have hF'_meas :
      AEStronglyMeasurable (fun t : Fin m → ℝ => baseFDerivSchwartz F (z, t))
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)) :=
    (integrable_complexRealFiber (baseFDerivSchwartz F) z).aestronglyMeasurable
  have h_bound :
      ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)),
        ∀ z' ∈ (Set.univ : Set (ComplexChartSpace m)),
          ‖baseFDerivSchwartz F (z', t)‖ ≤ bound t := by
    exact Filter.Eventually.of_forall fun t z' _ => hbound z' t
  have h_diff :
      ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)),
        ∀ z' ∈ (Set.univ : Set (ComplexChartSpace m)),
          HasFDerivAt (fun z'' : ComplexChartSpace m => F (z'', t))
            (baseFDerivSchwartz F (z', t)) z' := by
    refine Filter.Eventually.of_forall ?_
    intro t z' _
    let inl : ComplexChartSpace m →L[ℝ]
        (ComplexChartSpace m × (Fin m → ℝ)) :=
      ContinuousLinearMap.inl ℝ (ComplexChartSpace m) (Fin m → ℝ)
    have hinner : HasFDerivAt (fun z'' : ComplexChartSpace m => (z'', t)) inl z' := by
      have hlin : HasFDerivAt (fun z'' : ComplexChartSpace m => inl z'') inl z' :=
        inl.hasFDerivAt
      have hconst :
          (fun z'' : ComplexChartSpace m => (z'', t)) = fun z'' => inl z'' + (0, t) := by
        funext z''
        ext i <;> simp [inl]
      rw [hconst]
      exact hlin.add_const (0, t)
    have hFderiv :
        HasFDerivAt (F : (ComplexChartSpace m × (Fin m → ℝ)) → V)
          (fderiv ℝ (F : (ComplexChartSpace m × (Fin m → ℝ)) → V) (z', t)) (z', t) :=
      F.differentiableAt.hasFDerivAt
    simpa [inl] using hFderiv.comp z' hinner
  simpa [complexRealFiberIntegralRaw] using
    (hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)))
      (s := (Set.univ : Set (ComplexChartSpace m)))
      (x₀ := z)
      (F := fun z' t => F (z', t))
      (F' := fun z' t => baseFDerivSchwartz F (z', t))
      hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff)

/-- The Fréchet derivative of the raw fiber integral is the fiber integral of
the base-derivative field. -/
theorem fderiv_complexRealFiberIntegralRaw_eq {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) V) :
    fderiv ℝ (complexRealFiberIntegralRaw F) =
      complexRealFiberIntegralRaw (baseFDerivSchwartz F) := by
  funext z
  exact (hasFDerivAt_complexRealFiberIntegralRaw F z).fderiv

/-- Continuity of the raw fiber integral. -/
theorem continuous_complexRealFiberIntegralRaw {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) V) :
    Continuous (complexRealFiberIntegralRaw F) :=
  continuous_iff_continuousAt.2 fun z =>
    (hasFDerivAt_complexRealFiberIntegralRaw F z).continuousAt

/-- Finite-order smoothness of the raw fiber integral. -/
theorem contDiff_nat_complexRealFiberIntegralRaw {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (n : ℕ) (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) V) :
    ContDiff ℝ n (complexRealFiberIntegralRaw F) := by
  induction n generalizing V F with
  | zero =>
      exact contDiff_zero.2 (continuous_complexRealFiberIntegralRaw F)
  | succ n ihn =>
      exact (contDiff_succ_iff_hasFDerivAt (𝕜 := ℝ) (n := n)
        (f := complexRealFiberIntegralRaw F)).2 <| by
        refine ⟨complexRealFiberIntegralRaw (baseFDerivSchwartz F), ?_, ?_⟩
        · exact ihn (F := baseFDerivSchwartz F)
        · intro z
          exact hasFDerivAt_complexRealFiberIntegralRaw F z

/-- Smoothness of the raw fiber integral. -/
theorem contDiff_complexRealFiberIntegralRaw {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) V) :
    ContDiff ℝ (⊤ : ℕ∞) (complexRealFiberIntegralRaw F) := by
  rw [contDiff_infty]
  intro n
  exact contDiff_nat_complexRealFiberIntegralRaw n F

/-- Schwartz decay of every derivative of the raw fiber integral. -/
theorem decay_complexRealFiberIntegralRaw {m : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) V) (k n : ℕ) :
    ∃ C, ∀ z : ComplexChartSpace m,
      ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (complexRealFiberIntegralRaw F) z‖ ≤ C := by
  induction n generalizing V F with
  | zero =>
      obtain ⟨C, hC⟩ := exists_norm_pow_mul_complexRealFiberIntegralRaw_le F k
      refine ⟨C, fun z => ?_⟩
      simpa [norm_iteratedFDeriv_zero] using hC z
  | succ n ihn =>
      obtain ⟨C, hC⟩ := ihn (F := baseFDerivSchwartz F)
      refine ⟨C, fun z => ?_⟩
      calc
        ‖z‖ ^ k * ‖iteratedFDeriv ℝ (n + 1) (complexRealFiberIntegralRaw F) z‖
            = ‖z‖ ^ k *
                ‖iteratedFDeriv ℝ n (fderiv ℝ (complexRealFiberIntegralRaw F)) z‖ := by
              rw [norm_iteratedFDeriv_fderiv]
        _ = ‖z‖ ^ k *
              ‖iteratedFDeriv ℝ n
                (complexRealFiberIntegralRaw (baseFDerivSchwartz F)) z‖ := by
              rw [fderiv_complexRealFiberIntegralRaw_eq]
        _ ≤ C := hC z

/-- Fiber integration over the real direction as a Schwartz map in the complex
chart variable. -/
def complexRealFiberIntegral {m : ℕ}
    (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ) :
    SchwartzMap (ComplexChartSpace m) ℂ where
  toFun := complexRealFiberIntegralRaw F
  smooth' := contDiff_complexRealFiberIntegralRaw F
  decay' := decay_complexRealFiberIntegralRaw F

@[simp]
theorem complexRealFiberIntegral_apply {m : ℕ}
    (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ)
    (z : ComplexChartSpace m) :
    complexRealFiberIntegral F z = ∫ t : Fin m → ℝ, F (z, t) := by
  rfl

/-- The real-direction convolution test
`z ↦ ∫ t, φ (z - realEmbed t) * ψ t`. -/
def realConvolutionTest {m : ℕ}
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ) :
    SchwartzMap (ComplexChartSpace m) ℂ :=
  complexRealFiberIntegral
    ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (realConvolutionShearCLE m))
      (schwartzTensorProduct₂ φ ψ))

@[simp]
theorem realConvolutionTest_apply {m : ℕ}
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ)
    (z : ComplexChartSpace m) :
    realConvolutionTest φ ψ z = ∫ t : Fin m → ℝ, φ (z - realEmbed t) * ψ t := by
  simp [realConvolutionTest]

/-- Translating the complex-chart factor in `realConvolutionTest` is the same
as translating the real-kernel factor.  This is the sign-sensitive algebraic
identity consumed by the translation-covariant product-kernel descent. -/
theorem realConvolutionTest_complexTranslate_eq_translateSchwartz {m : ℕ}
    (a : Fin m → ℝ)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ) :
    realConvolutionTest (complexTranslateSchwartz a φ) ψ =
      realConvolutionTest φ (translateSchwartz a ψ) := by
  ext z
  simp [realConvolutionTest_apply]
  rw [← integral_add_right_eq_self a (μ := (volume : Measure (Fin m → ℝ)))
    (f := fun t : Fin m → ℝ => φ (z - realEmbed t + realEmbed a) * ψ t)]
  apply integral_congr_ae
  filter_upwards with t
  congr 2
  ext j
  simp [realEmbed, sub_eq_add_neg, add_comm, add_left_comm]

/-- Translation in the real fiber of the mixed complex/real chart:
`F(z,t) ↦ F(z,t+a)`. -/
def complexRealFiberTranslateSchwartzCLM {m : ℕ} (a : Fin m → ℝ) :
    SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ]
      SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ :=
  SchwartzMap.compSubConstCLM ℂ ((0 : ComplexChartSpace m), -a)

@[simp]
theorem complexRealFiberTranslateSchwartzCLM_apply {m : ℕ}
    (a : Fin m → ℝ)
    (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ)
    (z : ComplexChartSpace m) (t : Fin m → ℝ) :
    complexRealFiberTranslateSchwartzCLM a F (z, t) = F (z, t + a) := by
  simp [complexRealFiberTranslateSchwartzCLM]

/-- Head-block shift in ordinary real coordinates: the first `m` coordinates are
`a`, and the final `n` coordinates are zero. -/
def headBlockShift (m n : ℕ) (a : Fin m → ℝ) : Fin (m + n) → ℝ :=
  Fin.append a 0

@[simp]
theorem headBlockShift_apply_head {m n : ℕ} (a : Fin m → ℝ) (i : Fin m) :
    headBlockShift m n a (Fin.castAdd n i) = a i := by
  simp [headBlockShift]

@[simp]
theorem headBlockShift_apply_tail {m n : ℕ} (a : Fin m → ℝ) (i : Fin n) :
    headBlockShift m n a (Fin.natAdd m i) = 0 := by
  simp [headBlockShift]

private def realBlockUncurryLinearEquiv (n d : ℕ) (𝕜 : Type*) [CommSemiring 𝕜] :
    (Fin n → Fin d → 𝕜) ≃ₗ[𝕜] (Fin n × Fin d → 𝕜) :=
  { (Equiv.curry (Fin n) (Fin d) 𝕜).symm with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

private def realBlockFlattenLinearEquiv (n d : ℕ) (𝕜 : Type*) [CommSemiring 𝕜] :
    (Fin n → Fin d → 𝕜) ≃ₗ[𝕜] (Fin (n * d) → 𝕜) :=
  (realBlockUncurryLinearEquiv n d 𝕜).trans
    (LinearEquiv.funCongrLeft 𝕜 𝕜 finProdFinEquiv.symm)

/-- Flatten an `n` by `d` real block into the `finProdFinEquiv` coordinate order. -/
def realBlockFlattenCLE (n d : ℕ) :
    (Fin n → Fin d → ℝ) ≃L[ℝ] (Fin (n * d) → ℝ) :=
  (realBlockFlattenLinearEquiv n d ℝ).toContinuousLinearEquiv

@[simp]
theorem realBlockFlattenCLE_apply (n d : ℕ)
    (f : Fin n → Fin d → ℝ) (k : Fin (n * d)) :
    realBlockFlattenCLE n d f k =
      f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 := rfl

@[simp]
theorem realBlockFlattenCLE_symm_apply (n d : ℕ)
    (w : Fin (n * d) → ℝ) (i : Fin n) (j : Fin d) :
    (realBlockFlattenCLE n d).symm w i j = w (finProdFinEquiv (i, j)) := rfl

/-- Real-linear identification of one complex coordinate with `(re, im)`. -/
def complexToFinTwoCLE : ℂ ≃L[ℝ] (Fin 2 → ℝ) :=
  Complex.equivRealProdCLM.trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm

@[simp]
theorem complexToFinTwoCLE_apply_zero (z : ℂ) :
    complexToFinTwoCLE z 0 = z.re := by
  simp [complexToFinTwoCLE]

@[simp]
theorem complexToFinTwoCLE_apply_one (z : ℂ) :
    complexToFinTwoCLE z 1 = z.im := by
  simp [complexToFinTwoCLE]

/-- Coordinatewise real/imaginary chart of a complex chart. -/
def complexChartRealBlockCLE (m : ℕ) :
    ComplexChartSpace m ≃L[ℝ] (Fin m → Fin 2 → ℝ) :=
  ContinuousLinearEquiv.piCongrRight fun _ : Fin m => complexToFinTwoCLE

/-- Flatten a complex chart into real/imaginary coordinates in `(i, re/im)` order. -/
def complexChartRealFlattenCLE (m : ℕ) :
    ComplexChartSpace m ≃L[ℝ] (Fin (m * 2) → ℝ) :=
  (complexChartRealBlockCLE m).trans (realBlockFlattenCLE m 2)

@[simp]
theorem complexChartRealFlattenCLE_apply_re {m : ℕ}
    (z : ComplexChartSpace m) (i : Fin m) :
    complexChartRealFlattenCLE m z (finProdFinEquiv (i, (0 : Fin 2))) = (z i).re := by
  simp [complexChartRealFlattenCLE, complexChartRealBlockCLE]

@[simp]
theorem complexChartRealFlattenCLE_apply_im {m : ℕ}
    (z : ComplexChartSpace m) (i : Fin m) :
    complexChartRealFlattenCLE m z (finProdFinEquiv (i, (1 : Fin 2))) = (z i).im := by
  simp [complexChartRealFlattenCLE, complexChartRealBlockCLE]

private def finAppendLinearEquiv (m n : ℕ) :
    ((Fin m → ℝ) × (Fin n → ℝ)) ≃ₗ[ℝ] (Fin (m + n) → ℝ) :=
  { Fin.appendEquiv m n with
    map_add' := by
      intro x y
      apply (Fin.appendEquiv m n).symm.injective
      ext i <;> simp [Fin.appendEquiv]
    map_smul' := by
      intro c x
      apply (Fin.appendEquiv m n).symm.injective
      ext i <;> simp [Fin.appendEquiv] }

/-- Continuous real-linear append equivalence for finite coordinate blocks. -/
def finAppendCLE (m n : ℕ) :
    ((Fin m → ℝ) × (Fin n → ℝ)) ≃L[ℝ] (Fin (m + n) → ℝ) :=
  (finAppendLinearEquiv m n).toContinuousLinearEquiv

@[simp]
theorem finAppendCLE_apply_head {m n : ℕ}
    (p : (Fin m → ℝ) × (Fin n → ℝ)) (i : Fin m) :
    finAppendCLE m n p (Fin.castAdd n i) = p.1 i := by
  simp [finAppendCLE, finAppendLinearEquiv]

@[simp]
theorem finAppendCLE_apply_tail {m n : ℕ}
    (p : (Fin m → ℝ) × (Fin n → ℝ)) (i : Fin n) :
    finAppendCLE m n p (Fin.natAdd m i) = p.2 i := by
  simp [finAppendCLE, finAppendLinearEquiv]

/-- Mixed chart transport with the real fiber in the head block. -/
def mixedChartFiberFirstCLE (m : ℕ) :
    (ComplexChartSpace m × (Fin m → ℝ)) ≃L[ℝ] (Fin (m + m * 2) → ℝ) :=
  (ContinuousLinearEquiv.prodComm ℝ (ComplexChartSpace m) (Fin m → ℝ)).trans
    ((ContinuousLinearEquiv.prodCongr
      (ContinuousLinearEquiv.refl ℝ (Fin m → ℝ))
      (complexChartRealFlattenCLE m)).trans (finAppendCLE m (m * 2)))

@[simp]
theorem mixedChartFiberFirstCLE_apply_head {m : ℕ}
    (z : ComplexChartSpace m) (t : Fin m → ℝ) (i : Fin m) :
    mixedChartFiberFirstCLE m (z, t) (Fin.castAdd (m * 2) i) = t i := by
  simp [mixedChartFiberFirstCLE]

@[simp]
theorem mixedChartFiberFirstCLE_apply_tail_re {m : ℕ}
    (z : ComplexChartSpace m) (t : Fin m → ℝ) (i : Fin m) :
    mixedChartFiberFirstCLE m (z, t)
      (Fin.natAdd m (finProdFinEquiv (i, (0 : Fin 2)))) = (z i).re := by
  simp [mixedChartFiberFirstCLE]

@[simp]
theorem mixedChartFiberFirstCLE_apply_tail_im {m : ℕ}
    (z : ComplexChartSpace m) (t : Fin m → ℝ) (i : Fin m) :
    mixedChartFiberFirstCLE m (z, t)
      (Fin.natAdd m (finProdFinEquiv (i, (1 : Fin 2)))) = (z i).im := by
  simp [mixedChartFiberFirstCLE]

@[simp]
theorem mixedChartFiberFirstCLE_symm_headBlockShift {m : ℕ} (a : Fin m → ℝ) :
    (mixedChartFiberFirstCLE m).symm (headBlockShift m (m * 2) a) = (0, a) := by
  ext i
  · simp [mixedChartFiberFirstCLE, headBlockShift, complexChartRealFlattenCLE,
      complexChartRealBlockCLE, complexToFinTwoCLE, finAppendCLE, finAppendLinearEquiv,
      ContinuousLinearEquiv.prodCongr_symm]
  · simp [mixedChartFiberFirstCLE, headBlockShift, complexChartRealFlattenCLE,
      complexChartRealBlockCLE, complexToFinTwoCLE, finAppendCLE, finAppendLinearEquiv,
      ContinuousLinearEquiv.prodCongr_symm]

/-- Under the fiber-first chart, mixed real-fiber translation is ordinary
head-block translation in real coordinates. -/
theorem mixedChartFiberFirstCLE_translate {m : ℕ} (a : Fin m → ℝ) :
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedChartFiberFirstCLE m).symm).comp
      (complexRealFiberTranslateSchwartzCLM a) =
    (translateSchwartzCLM (headBlockShift m (m * 2) a)).comp
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedChartFiberFirstCLE m).symm) := by
  ext F x
  set y := (mixedChartFiberFirstCLE m).symm x with hy
  have hshift := mixedChartFiberFirstCLE_symm_headBlockShift (m := m) a
  have hlin :
      (mixedChartFiberFirstCLE m).symm (x + headBlockShift m (m * 2) a) =
        y + (0, a) := by
    calc
      (mixedChartFiberFirstCLE m).symm (x + headBlockShift m (m * 2) a)
          = (mixedChartFiberFirstCLE m).symm x +
              (mixedChartFiberFirstCLE m).symm (headBlockShift m (m * 2) a) := by
            simp
      _ = y + (0, a) := by simp [hy, hshift]
  rcases y with ⟨z, t⟩
  simp [ContinuousLinearMap.comp_apply, translateSchwartzCLM_apply, hlin]
  rw [← hy]
  simp

/-- Fiber integration is invariant under real-fiber translation. -/
theorem complexRealFiberIntegral_fiberTranslate {m : ℕ}
    (a : Fin m → ℝ)
    (F : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ) :
    complexRealFiberIntegral (complexRealFiberTranslateSchwartzCLM a F) =
      complexRealFiberIntegral F := by
  ext z
  simp [complexRealFiberIntegral_apply]
  simpa using
    (MeasureTheory.integral_add_right_eq_self
      (μ := (volume : Measure (Fin m → ℝ)))
      (fun t : Fin m → ℝ => F (z, t)) a)

/-- The real-fiber integral of a product test is the complex-chart factor
scaled by the real-kernel mass. -/
theorem complexRealFiberIntegral_schwartzTensorProduct₂ {m : ℕ}
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ) :
    complexRealFiberIntegral (schwartzTensorProduct₂ φ ψ) =
      (∫ t : Fin m → ℝ, ψ t) • φ := by
  ext z
  simp [complexRealFiberIntegral_apply]
  calc
    ∫ t : Fin m → ℝ, φ z * ψ t = φ z * ∫ t : Fin m → ℝ, ψ t := by
      simpa [smul_eq_mul] using
        (integral_const_mul
          (μ := (volume : Measure (Fin m → ℝ)))
          (r := φ z) (f := fun t : Fin m → ℝ => ψ t))
    _ = (∫ t : Fin m → ℝ, ψ t) * φ z := by ring

/-- Composition law for real translations of real-fiber Schwartz tests. -/
theorem translateSchwartz_translateSchwartz {m : ℕ}
    (a b : Fin m → ℝ) (ψ : SchwartzMap (Fin m → ℝ) ℂ) :
    translateSchwartz a (translateSchwartz b ψ) =
      translateSchwartz (a + b) ψ := by
  ext t
  simp [translateSchwartz_apply, add_assoc]

/-- Composition law for real translations of complex-chart Schwartz tests. -/
theorem complexTranslateSchwartz_complexTranslateSchwartz {m : ℕ}
    (a b : Fin m → ℝ)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ) :
    complexTranslateSchwartz a (complexTranslateSchwartz b φ) =
      complexTranslateSchwartz (a + b) φ := by
  ext z
  have hreal : realEmbed a + realEmbed b = realEmbed (a + b) := by
    ext i
    simp [realEmbed]
  simp [complexTranslateSchwartz_apply, add_assoc, hreal]

/-- Global real-translation covariance for product kernels.  This is the pure
SCV form used by the descent theorem before local support cutoffs are applied. -/
def ProductKernelRealTranslationCovariantGlobal {m : ℕ}
    (K : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ) :
    Prop :=
  ∀ (a : Fin m → ℝ)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ),
      K (schwartzTensorProduct₂ (complexTranslateSchwartz a φ) ψ) =
        K (schwartzTensorProduct₂ φ (translateSchwartz a ψ))

/-- Local real-translation covariance for product kernels on the support
window used by the regularized EOW envelope.  The global descent theorem is
proved first; this local predicate is consumed only after the fixed cutoff
extends the local covariance to a global kernel. -/
def ProductKernelRealTranslationCovariantLocal {m : ℕ}
    (K : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ)
    (Ucore : Set (ComplexChartSpace m)) (r : ℝ) : Prop :=
  ∀ (a : Fin m → ℝ)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ),
      SupportsInOpen (φ : ComplexChartSpace m → ℂ) Ucore →
      SupportsInOpen
        (complexTranslateSchwartz a φ : ComplexChartSpace m → ℂ) Ucore →
      KernelSupportWithin ψ r →
      KernelSupportWithin (translateSchwartz a ψ) r →
        K (schwartzTensorProduct₂ (complexTranslateSchwartz a φ) ψ) =
          K (schwartzTensorProduct₂ φ (translateSchwartz a ψ))

/-- The sheared functional used to convert product-kernel covariance into
translation invariance along the real fiber. -/
def shearedProductKernelFunctional {m : ℕ}
    (K : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ) :
    SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ :=
  K.comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (realConvolutionShearCLE m).symm)

/-- Fiber translation of a sheared product test is another sheared product
test, with the sign fixed by the shear convention. -/
theorem complexRealFiberTranslate_shearedTensor_eq {m : ℕ}
    (a : Fin m → ℝ)
    (φ : SchwartzMap (ComplexChartSpace m) ℂ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ) :
    complexRealFiberTranslateSchwartzCLM a
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (realConvolutionShearCLE m))
        (schwartzTensorProduct₂ φ ψ)) =
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (realConvolutionShearCLE m))
        (schwartzTensorProduct₂ (complexTranslateSchwartz (-a) φ)
          (translateSchwartz a ψ)) := by
  ext p
  rcases p with ⟨z, t⟩
  have hz : z - realEmbed (a + t) = z - realEmbed t + realEmbed (-a) := by
    ext i
    simp [realEmbed, sub_eq_add_neg, add_comm, add_left_comm]
  simp [hz, add_comm]

/-- Real-fiber translation invariance of a mixed-chart Schwartz functional. -/
def IsComplexRealFiberTranslationInvariant {m : ℕ}
    (T : SchwartzMap (ComplexChartSpace m × (Fin m → ℝ)) ℂ →L[ℂ] ℂ) :
    Prop :=
  ∀ a : Fin m → ℝ, T.comp (complexRealFiberTranslateSchwartzCLM a) = T

end SCV
