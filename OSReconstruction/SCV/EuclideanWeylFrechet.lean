/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.EuclideanWeyl
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

/-!
# Euclidean Weyl Frechet Derivative Infrastructure

This file contains the Frechet-derivative packaging for the Euclidean moving
kernel layer.  The remaining hard estimate is the direction-uniform Schwartz
remainder for translations; the declarations here fix the honest derivative
candidate consumed by that estimate.
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set Filter
open scoped LineDeriv

namespace SCV

/-- The directional derivative of a fixed Schwartz function, as a continuous
real-linear map of the Euclidean direction. -/
noncomputable def euclideanLineDerivDirectionCLM
    {ι : Type*} [Fintype ι]
    (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    EuclideanSpace ℝ ι →L[ℝ] SchwartzMap (EuclideanSpace ℝ ι) ℂ := by
  let L : EuclideanSpace ℝ ι →ₗ[ℝ] SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
    { toFun := fun v => (∂_{v} ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
      map_add' := by
        intro v w
        simpa using (LineDeriv.lineDerivOp_left_add v w ρ)
      map_smul' := by
        intro c v
        simpa using (LineDeriv.lineDerivOp_left_smul c v ρ) }
  exact ⟨L, L.continuous_of_finiteDimensional⟩

@[simp]
theorem euclideanLineDerivDirectionCLM_apply
    {ι : Type*} [Fintype ι]
    (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (v : EuclideanSpace ℝ ι) :
    euclideanLineDerivDirectionCLM ρ v =
      (∂_{v} ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) := by
  simp [euclideanLineDerivDirectionCLM]

/-- The second directional derivative of a fixed Schwartz function, as a
continuous real-bilinear map of the two Euclidean directions. -/
noncomputable def euclideanSecondLineDerivDirectionCLM
    {ι : Type*} [Fintype ι]
    (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    EuclideanSpace ℝ ι →L[ℝ]
      EuclideanSpace ℝ ι →L[ℝ] SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
  (LineDeriv.bilinearLineDerivTwo ℝ φ).toContinuousBilinearMap

@[simp]
theorem euclideanSecondLineDerivDirectionCLM_apply
    {ι : Type*} [Fintype ι]
    (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (v w : EuclideanSpace ℝ ι) :
    euclideanSecondLineDerivDirectionCLM φ v w =
      (∂_{v} (∂_{w} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
        SchwartzMap (EuclideanSpace ℝ ι) ℂ) := by
  rfl

private theorem seminorm_finset_sum_le {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p : Seminorm ℝ V) {α : Type*} (s : Finset α) (g : α → V) :
    p (∑ i ∈ s, g i) ≤ ∑ i ∈ s, p (g i) := by
  induction s using Finset.cons_induction with
  | empty => simp [map_zero]
  | cons a s _ ih =>
      rw [Finset.sum_cons, Finset.sum_cons]
      calc
        p (g a + ∑ i ∈ s, g i) ≤ p (g a) + p (∑ i ∈ s, g i) :=
          map_add_le_add p _ _
        _ ≤ p (g a) + ∑ i ∈ s, p (g i) := by linarith

private theorem iteratedFDeriv_sub_euclidean_schwartz
    {ι : Type*} [Fintype ι]
    (f g : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (n : ℕ) (x : EuclideanSpace ℝ ι) :
    iteratedFDeriv ℝ n (⇑(f - g)) x =
      iteratedFDeriv ℝ n (⇑f) x - iteratedFDeriv ℝ n (⇑g) x := by
  have hf : ContDiff ℝ n (⇑f) := f.smooth n
  have hg : ContDiff ℝ n (⇑g) := g.smooth n
  have hfg :
      (⇑(f - g) : EuclideanSpace ℝ ι → ℂ) =
        (⇑f) + fun x => -(⇑g x) := by
    ext y
    simp [sub_eq_add_neg]
  have hneg : (fun x => -(⇑g x)) = -⇑g := rfl
  rw [hfg, iteratedFDeriv_add_apply hf.contDiffAt hg.neg.contDiffAt,
    hneg, iteratedFDeriv_neg_apply]
  simp [sub_eq_add_neg]

private theorem euclidean_coord_norm_le_norm
    {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℝ ι) (i : ι) : ‖v i‖ ≤ ‖v‖ := by
  have hsq_i : ‖v i‖ ^ 2 ≤ ∑ j : ι, ‖v j‖ ^ 2 := by
    exact Finset.single_le_sum
      (fun j _ => sq_nonneg (‖v j‖)) (Finset.mem_univ i)
  have hsq : ‖v i‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    simpa [EuclideanSpace.norm_sq_eq] using hsq_i
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

private theorem secondLineDeriv_diagonal_expand
    {ι : Type*} [Fintype ι]
    (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (v : EuclideanSpace ℝ ι) :
    (LineDeriv.bilinearLineDerivTwo ℝ φ) v v =
      ∑ i : ι, ∑ j : ι,
        (v i * v j) •
          (LineDeriv.bilinearLineDerivTwo ℝ φ)
            (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ j) := by
  let B : EuclideanSpace ℝ ι →ₗ[ℝ]
      EuclideanSpace ℝ ι →ₗ[ℝ] SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
    LineDeriv.bilinearLineDerivTwo ℝ φ
  let e : ι → EuclideanSpace ℝ ι := fun i => EuclideanSpace.basisFun ι ℝ i
  have hv : v = ∑ i : ι, v i • e i := by
    simpa [e, EuclideanSpace.basisFun_repr] using
      ((EuclideanSpace.basisFun ι ℝ).sum_repr v).symm
  calc
    B v v = B (∑ i : ι, v i • e i) v := by rw [← hv]
    _ = ∑ i : ι, B (v i • e i) v := by simp [map_sum]
    _ = ∑ i : ι, v i • B (e i) v := by simp
    _ = ∑ i : ι, v i • B (e i) (∑ j : ι, v j • e j) := by rw [← hv]
    _ = ∑ i : ι, v i • (∑ j : ι, B (e i) (v j • e j)) := by
      simp [map_sum]
    _ = ∑ i : ι, v i • (∑ j : ι, v j • B (e i) (e j)) := by simp
    _ = ∑ i : ι, ∑ j : ι, (v i * v j) • B (e i) (e j) := by
      simp [Finset.smul_sum, smul_smul]

/-- Every fixed Schwartz seminorm of the second line derivative is uniformly
bounded for unit Euclidean directions. -/
theorem exists_seminorm_secondLineDeriv_unit_bound
    {ι : Type*} [Fintype ι]
    (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ v : EuclideanSpace ℝ ι, ‖v‖ ≤ 1 →
        SchwartzMap.seminorm ℝ k n
          (∂_{v} (∂_{v} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)) ≤ C := by
  let B : EuclideanSpace ℝ ι →ₗ[ℝ]
      EuclideanSpace ℝ ι →ₗ[ℝ] SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
    LineDeriv.bilinearLineDerivTwo ℝ φ
  let e : ι → EuclideanSpace ℝ ι := fun i => EuclideanSpace.basisFun ι ℝ i
  let p : Seminorm ℝ (SchwartzMap (EuclideanSpace ℝ ι) ℂ) :=
    SchwartzMap.seminorm ℝ k n
  let C : ℝ := ∑ i : ι, ∑ j : ι, p (B (e i) (e j))
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => apply_nonneg p _
  refine ⟨C, hC_nonneg, ?_⟩
  intro v hv_unit
  have hdiag := secondLineDeriv_diagonal_expand (φ := φ) v
  have hcoord : ∀ i : ι, ‖v i‖ ≤ 1 := by
    intro i
    exact (euclidean_coord_norm_le_norm v i).trans hv_unit
  have hterm : ∀ i j : ι,
      p ((v i * v j) • B (e i) (e j)) ≤ p (B (e i) (e j)) := by
    intro i j
    rw [map_smul_eq_mul]
    have habs : ‖v i * v j‖ ≤ 1 := by
      calc
        ‖v i * v j‖ = ‖v i‖ * ‖v j‖ := norm_mul _ _
        _ ≤ 1 * 1 := by
          exact mul_le_mul (hcoord i) (hcoord j) (norm_nonneg _) zero_le_one
        _ = 1 := by norm_num
    calc
      ‖v i * v j‖ * p (B (e i) (e j)) ≤ 1 * p (B (e i) (e j)) := by
        exact mul_le_mul_of_nonneg_right habs (apply_nonneg p _)
      _ = p (B (e i) (e j)) := one_mul _
  calc
    SchwartzMap.seminorm ℝ k n
        (∂_{v} (∂_{v} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)) = p (B v v) := by rfl
    _ = p (∑ i : ι, ∑ j : ι, (v i * v j) • B (e i) (e j)) := by
      rw [hdiag]
    _ ≤ ∑ i : ι, p (∑ j : ι, (v i * v j) • B (e i) (e j)) := by
      simpa using seminorm_finset_sum_le p Finset.univ
        (fun i : ι => ∑ j : ι, (v i * v j) • B (e i) (e j))
    _ ≤ ∑ i : ι, ∑ j : ι, p ((v i * v j) • B (e i) (e j)) := by
      exact Finset.sum_le_sum fun i _ => by
        simpa using seminorm_finset_sum_le p Finset.univ
          (fun j : ι => (v i * v j) • B (e i) (e j))
    _ ≤ ∑ i : ι, ∑ j : ι, p (B (e i) (e j)) := by
      exact Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => hterm i j
    _ = C := rfl

/-- Unit-direction second line derivatives remain uniformly bounded after
unit Euclidean translations. -/
theorem exists_seminorm_translate_secondLineDeriv_unit_bound
    {ι : Type*} [Fintype ι]
    (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ v : EuclideanSpace ℝ ι, ‖v‖ ≤ 1 →
      ∀ a : EuclideanSpace ℝ ι, ‖a‖ ≤ 1 →
        SchwartzMap.seminorm ℝ k n
          (euclideanTranslateSchwartzCLM a
            (∂_{v} (∂_{v} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
              SchwartzMap (EuclideanSpace ℝ ι) ℂ)) ≤ C := by
  obtain ⟨Ck, hCk_nonneg, hCk⟩ :=
    exists_seminorm_secondLineDeriv_unit_bound φ k n
  obtain ⟨C0, hC0_nonneg, hC0⟩ :=
    exists_seminorm_secondLineDeriv_unit_bound φ 0 n
  let C : ℝ := 2 ^ (k - 1) * (Ck + C0)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      (add_nonneg hCk_nonneg hC0_nonneg)
  refine ⟨C, hC_nonneg, ?_⟩
  intro v hv_unit a ha_unit
  let h : SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
    (∂_{v} (∂_{v} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
      SchwartzMap (EuclideanSpace ℝ ι) ℂ)
  have hk_bound : SchwartzMap.seminorm ℝ k n h ≤ Ck := hCk v hv_unit
  have h0_bound : SchwartzMap.seminorm ℝ 0 n h ≤ C0 := hC0 v hv_unit
  refine SchwartzMap.seminorm_le_bound ℝ k n
      (euclideanTranslateSchwartzCLM a h) hC_nonneg ?_
  intro x
  have htrans :
      iteratedFDeriv ℝ n (⇑(euclideanTranslateSchwartzCLM a h)) x =
        iteratedFDeriv ℝ n (h : EuclideanSpace ℝ ι → ℂ) (x + a) := by
    simpa using
      (iteratedFDeriv_comp_add_right
        (f := (h : EuclideanSpace ℝ ι → ℂ)) n a x)
  rw [htrans]
  have hk_point :
      ‖x + a‖ ^ k *
          ‖iteratedFDeriv ℝ n (h : EuclideanSpace ℝ ι → ℂ) (x + a)‖ ≤ Ck := by
    exact le_trans (SchwartzMap.le_seminorm ℝ k n h (x + a)) hk_bound
  have h0_point :
      ‖iteratedFDeriv ℝ n (h : EuclideanSpace ℝ ι → ℂ) (x + a)‖ ≤ C0 := by
    have hle := le_trans (SchwartzMap.le_seminorm ℝ 0 n h (x + a)) h0_bound
    simpa using hle
  have hnorm_x : ‖x‖ ≤ ‖x + a‖ + ‖a‖ := by
    calc
      ‖x‖ = ‖(x + a) - a‖ := by simp
      _ ≤ ‖x + a‖ + ‖a‖ := norm_sub_le _ _
  have ha_pow : ‖a‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg a) ha_unit
  have ha_term :
      ‖a‖ ^ k *
          ‖iteratedFDeriv ℝ n (h : EuclideanSpace ℝ ι → ℂ) (x + a)‖ ≤ C0 := by
    calc
      ‖a‖ ^ k *
          ‖iteratedFDeriv ℝ n (h : EuclideanSpace ℝ ι → ℂ) (x + a)‖
          ≤ 1 * ‖iteratedFDeriv ℝ n (h : EuclideanSpace ℝ ι → ℂ) (x + a)‖ := by
            gcongr
      _ = ‖iteratedFDeriv ℝ n (h : EuclideanSpace ℝ ι → ℂ) (x + a)‖ :=
        one_mul _
      _ ≤ C0 := h0_point
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (h : EuclideanSpace ℝ ι → ℂ) (x + a)‖
        ≤ (‖x + a‖ + ‖a‖) ^ k *
            ‖iteratedFDeriv ℝ n (h : EuclideanSpace ℝ ι → ℂ) (x + a)‖ := by
          gcongr
    _ ≤ (2 ^ (k - 1) * (‖x + a‖ ^ k + ‖a‖ ^ k)) *
            ‖iteratedFDeriv ℝ n (h : EuclideanSpace ℝ ι → ℂ) (x + a)‖ := by
          gcongr
          exact add_pow_le (norm_nonneg _) (norm_nonneg _) k
    _ = 2 ^ (k - 1) *
          (‖x + a‖ ^ k *
              ‖iteratedFDeriv ℝ n (h : EuclideanSpace ℝ ι → ℂ) (x + a)‖ +
            ‖a‖ ^ k *
              ‖iteratedFDeriv ℝ n (h : EuclideanSpace ℝ ι → ℂ) (x + a)‖) := by
          ring
    _ ≤ 2 ^ (k - 1) * (Ck + C0) := by
          exact mul_le_mul_of_nonneg_left
            (add_le_add hk_point ha_term) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
    _ = C := rfl

/-- The translate of the first line derivative differs from the first line
derivative by `O(|t|)`, uniformly for unit Euclidean directions. -/
theorem exists_seminorm_translate_lineDeriv_sub_le_linear_uniform_unit
    {ι : Type*} [Fintype ι]
    (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ v : EuclideanSpace ℝ ι, ‖v‖ ≤ 1 →
      ∀ t : ℝ, |t| ≤ 1 →
        SchwartzMap.seminorm ℝ k n
          (euclideanTranslateSchwartzCLM (t • v)
            (∂_{v} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) -
            ∂_{v} φ) ≤ C * |t| := by
  obtain ⟨C, hC_nonneg, hC⟩ :=
    exists_seminorm_translate_secondLineDeriv_unit_bound φ k n
  refine ⟨C, hC_nonneg, ?_⟩
  intro v hv_unit t ht_abs
  let g : SchwartzMap (EuclideanSpace ℝ ι) ℂ := ∂_{v} φ
  let h2 : SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
    (∂_{v} (∂_{v} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
      SchwartzMap (EuclideanSpace ℝ ι) ℂ)
  refine SchwartzMap.seminorm_le_bound ℝ k n
      (euclideanTranslateSchwartzCLM (t • v) g - g)
      (mul_nonneg hC_nonneg (abs_nonneg t)) ?_
  intro x
  let H : EuclideanSpace ℝ ι →
      ContinuousMultilinearMap ℝ (fun _ : Fin n => EuclideanSpace ℝ ι) ℂ :=
    iteratedFDeriv ℝ n (g : EuclideanSpace ℝ ι → ℂ)
  let hxFun : ℝ →
      ContinuousMultilinearMap ℝ (fun _ : Fin n => EuclideanSpace ℝ ι) ℂ :=
    fun s => ‖x‖ ^ k • H (x + s • (t • v))
  have hH_diff : Differentiable ℝ H := by
    simpa [H] using
      (g.smooth (n + 1)).differentiable_iteratedFDeriv (by
        exact_mod_cast Nat.lt_succ_self n)
  have hxFun_hasDeriv :
      ∀ s : ℝ,
        HasDerivAt hxFun
          (‖x‖ ^ k • (fderiv ℝ H (x + s • (t • v)) (t • v))) s := by
    intro s
    have hgamma :
        HasDerivAt (fun r : ℝ => x + r • (t • v)) (t • v) s := by
      let L : ℝ →L[ℝ] ℝ := 1
      let Lsmul : ℝ →L[ℝ] EuclideanSpace ℝ ι :=
        ContinuousLinearMap.smulRight L (t • v)
      simpa [L, Lsmul, ContinuousLinearMap.smulRight_apply, one_smul,
        add_comm, add_left_comm, add_assoc] using (Lsmul.hasDerivAt).const_add x
    have hcomp :
        HasDerivAt (fun r : ℝ => H (x + r • (t • v)))
          ((fderiv ℝ H (x + s • (t • v))) (t • v)) s := by
      exact (hH_diff (x + s • (t • v))).hasFDerivAt.comp_hasDerivAt s hgamma
    simpa [hxFun] using hcomp.const_smul (‖x‖ ^ k)
  have hxFun_bound :
      ∀ s ∈ Set.Ico (0 : ℝ) 1,
        ‖‖x‖ ^ k • (fderiv ℝ H (x + s • (t • v)) (t • v))‖ ≤ C * |t| := by
    intro s hs
    have hs_abs : |s| ≤ 1 := by
      have hs0 : 0 ≤ s := hs.1
      have hs1 : s ≤ 1 := le_of_lt hs.2
      rw [abs_of_nonneg hs0]
      exact hs1
    have ha_norm : ‖s • (t • v)‖ ≤ 1 := by
      calc
        ‖s • (t • v)‖ = |s| * (|t| * ‖v‖) := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ 1 * (1 * 1) := by
          gcongr
        _ = 1 := by norm_num
    have hseminorm := hC v hv_unit (s • (t • v)) ha_norm
    have hpoint :
        ‖x‖ ^ k *
            ‖iteratedFDeriv ℝ n (h2 : EuclideanSpace ℝ ι → ℂ)
              (x + s • (t • v))‖ ≤ C := by
      have hle := le_trans
        (SchwartzMap.le_seminorm ℝ k n
          (euclideanTranslateSchwartzCLM (s • (t • v)) h2) x)
        hseminorm
      have htrans :
          iteratedFDeriv ℝ n
              (⇑(euclideanTranslateSchwartzCLM (s • (t • v)) h2)) x =
            iteratedFDeriv ℝ n (h2 : EuclideanSpace ℝ ι → ℂ)
              (x + s • (t • v)) := by
        simpa using
          (iteratedFDeriv_comp_add_right
            (f := (h2 : EuclideanSpace ℝ ι → ℂ)) n (s • (t • v)) x)
      simpa [htrans] using hle
    have hfderiv_eq :
        fderiv ℝ H (x + s • (t • v)) (t • v) =
          t • iteratedFDeriv ℝ n (h2 : EuclideanSpace ℝ ι → ℂ)
            (x + s • (t • v)) := by
      dsimp [H, g, h2]
      rw [fderiv_iteratedFDeriv_eq_iteratedFDeriv_euclideanLineDeriv]
      rw [LineDeriv.lineDerivOp_left_smul]
      simpa [Pi.smul_apply] using
        (iteratedFDeriv_const_smul_apply'
          (𝕜 := ℝ) (a := t)
          (f := (((∂_{v} (∂_{v} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
            SchwartzMap (EuclideanSpace ℝ ι) ℂ)) : EuclideanSpace ℝ ι → ℂ))
          (x := x + s • (t • v))
          (((∂_{v} (∂_{v} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
            SchwartzMap (EuclideanSpace ℝ ι) ℂ)).smooth n).contDiffAt)
    have hxpow_nonneg : 0 ≤ ‖x‖ ^ k := by positivity
    calc
      ‖‖x‖ ^ k • (fderiv ℝ H (x + s • (t • v)) (t • v))‖
          = ‖x‖ ^ k * ‖fderiv ℝ H (x + s • (t • v)) (t • v)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hxpow_nonneg]
      _ = ‖x‖ ^ k *
            ‖t • iteratedFDeriv ℝ n (h2 : EuclideanSpace ℝ ι → ℂ)
              (x + s • (t • v))‖ := by rw [hfderiv_eq]
      _ = |t| * (‖x‖ ^ k *
            ‖iteratedFDeriv ℝ n (h2 : EuclideanSpace ℝ ι → ℂ)
              (x + s • (t • v))‖) := by
            rw [norm_smul, Real.norm_eq_abs]
            ring
      _ ≤ |t| * C := by
            gcongr
      _ = C * |t| := by ring
  have hmv :=
    norm_image_sub_le_of_norm_deriv_le_segment_01'
      (f := hxFun)
      (f' := fun s => ‖x‖ ^ k • (fderiv ℝ H (x + s • (t • v)) (t • v)))
      (fun s _hs => (hxFun_hasDeriv s).hasDerivWithinAt)
      hxFun_bound
  have hiter_eq :
      iteratedFDeriv ℝ n
        (⇑(euclideanTranslateSchwartzCLM (t • v) g - g)) x =
        H (x + t • v) - H x := by
    have htrans :
        iteratedFDeriv ℝ n
          (⇑(euclideanTranslateSchwartzCLM (t • v) g)) x =
          H (x + t • v) := by
      simpa [H] using
        (iteratedFDeriv_comp_add_right
          (f := (g : EuclideanSpace ℝ ι → ℂ)) n (t • v) x)
    rw [iteratedFDeriv_sub_euclidean_schwartz]
    rw [htrans]
  have hxFun_diff :
      hxFun 1 - hxFun 0 = ‖x‖ ^ k • (H (x + t • v) - H x) := by
    simp [hxFun, smul_sub]
  calc
    ‖x‖ ^ k *
        ‖iteratedFDeriv ℝ n
          (⇑(euclideanTranslateSchwartzCLM (t • v) g - g)) x‖
        = ‖hxFun 1 - hxFun 0‖ := by
            rw [hxFun_diff, hiter_eq, norm_smul, Real.norm_eq_abs]
            have hxpow_nonneg : 0 ≤ ‖x‖ ^ k := by positivity
            simp [abs_of_nonneg hxpow_nonneg]
    _ ≤ C * |t| := by simpa [sub_eq_add_neg] using hmv

/-- Uniform version of the Euclidean translation difference-quotient estimate
for all unit Euclidean directions. -/
theorem exists_seminorm_diffQuotient_euclideanTranslateSchwartz_sub_lineDeriv_le_uniform_unit
    {ι : Type*} [Fintype ι]
    (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ v : EuclideanSpace ℝ ι, ‖v‖ ≤ 1 →
      ∀ t : ℝ, t ≠ 0 → |t| ≤ 1 →
        SchwartzMap.seminorm ℝ k n
          (t⁻¹ • (euclideanTranslateSchwartzCLM (t • v) φ - φ) - ∂_{v} φ) ≤
            C * |t| := by
  obtain ⟨C, hC_nonneg, hC⟩ :=
    exists_seminorm_translate_lineDeriv_sub_le_linear_uniform_unit φ k n
  refine ⟨C, hC_nonneg, ?_⟩
  intro v hv_unit t ht_ne ht_abs
  refine SchwartzMap.seminorm_le_bound ℝ k n
      (t⁻¹ • (euclideanTranslateSchwartzCLM (t • v) φ - φ) - ∂_{v} φ)
      (mul_nonneg hC_nonneg (abs_nonneg t)) ?_
  intro x
  have hpoint :=
    euclideanDiffQuotient_weighted_pointwise_bound
      (φ := φ) (v := v) (k := k) (n := n)
      (C := C) hC_nonneg (fun τ hτ => hC v hv_unit τ hτ) ht_ne ht_abs x
  have hformula :=
    euclideanDiffQuotient_iteratedFDeriv_pointwise
      (φ := φ) (v := v) (n := n) ht_ne x
  calc
    ‖x‖ ^ k *
        ‖iteratedFDeriv ℝ n
          (↑(t⁻¹ • (euclideanTranslateSchwartzCLM (t • v) φ - φ) - ∂_{v} φ) :
            EuclideanSpace ℝ ι → ℂ) x‖
        =
        ‖x‖ ^ k *
          ‖t⁻¹ •
              (iteratedFDeriv ℝ n (φ : EuclideanSpace ℝ ι → ℂ) (x + t • v) -
                iteratedFDeriv ℝ n (φ : EuclideanSpace ℝ ι → ℂ) x) -
            iteratedFDeriv ℝ n
              (((∂_{v} φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
                EuclideanSpace ℝ ι → ℂ)) x‖ := by
          rw [hformula]
    _ ≤ C * |t| := hpoint

/-- Quadratic Schwartz-seminorm remainder for Euclidean translations, uniformly
near the origin in all directions. -/
theorem exists_seminorm_euclideanTranslateSchwartz_sub_lineDeriv_le_quadratic_norm
    {ι : Type*} [Fintype ι]
    (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ h : EuclideanSpace ℝ ι, ‖h‖ ≤ 1 →
        SchwartzMap.seminorm ℝ k n
          (euclideanTranslateSchwartzCLM h φ - φ -
            euclideanLineDerivDirectionCLM φ h) ≤ C * ‖h‖ ^ 2 := by
  obtain ⟨C, hC_nonneg, hC⟩ :=
    exists_seminorm_diffQuotient_euclideanTranslateSchwartz_sub_lineDeriv_le_uniform_unit φ k n
  refine ⟨C, hC_nonneg, ?_⟩
  intro h hh_unit
  by_cases hh_zero : h = 0
  · subst h
    simp [euclideanLineDerivDirectionCLM]
  · have hnorm_pos : 0 < ‖h‖ := norm_pos_iff.mpr hh_zero
    let t : ℝ := ‖h‖
    let v : EuclideanSpace ℝ ι := ‖h‖⁻¹ • h
    have ht_pos : 0 < t := hnorm_pos
    have ht_ne : t ≠ 0 := ne_of_gt ht_pos
    have ht_abs : |t| ≤ 1 := by
      dsimp [t]
      rwa [abs_of_nonneg (norm_nonneg h)]
    have htv : t • v = h := by
      dsimp [t, v]
      rw [smul_smul]
      rw [mul_inv_cancel₀ hnorm_pos.ne']
      simp
    have hv_norm : ‖v‖ = 1 := by
      dsimp [v]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm_pos),
        inv_mul_cancel₀ hnorm_pos.ne']
    have hquot := hC v (le_of_eq hv_norm) t ht_ne ht_abs
    let D : SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
      t⁻¹ • (euclideanTranslateSchwartzCLM (t • v) φ - φ) - ∂_{v} φ
    have hmain_eq :
        euclideanTranslateSchwartzCLM h φ - φ - euclideanLineDerivDirectionCLM φ h =
          t • D := by
      rw [← htv]
      dsimp [D]
      rw [euclideanLineDerivDirectionCLM_apply, LineDeriv.lineDerivOp_left_smul]
      simp [smul_sub, smul_smul, ht_ne]
    calc
      SchwartzMap.seminorm ℝ k n
          (euclideanTranslateSchwartzCLM h φ - φ - euclideanLineDerivDirectionCLM φ h)
          = SchwartzMap.seminorm ℝ k n (t • D) := by rw [hmain_eq]
      _ = |t| * SchwartzMap.seminorm ℝ k n D := by
          rw [map_smul_eq_mul, Real.norm_eq_abs]
      _ ≤ |t| * (C * |t|) := by
          gcongr
      _ = C * ‖h‖ ^ 2 := by
          dsimp [t]
          rw [abs_of_nonneg (norm_nonneg h)]
          ring

/-- Euclidean translation has the expected Frechet remainder in the Schwartz
topology. -/
theorem tendsto_frechetRemainder_euclideanTranslateSchwartz_zero
    {ι : Type*} [Fintype ι]
    (φ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    Filter.Tendsto
      (fun h : EuclideanSpace ℝ ι =>
        ‖h‖⁻¹ •
          (euclideanTranslateSchwartzCLM h φ - φ - euclideanLineDerivDirectionCLM φ h))
      (nhdsWithin (0 : EuclideanSpace ℝ ι) ({0}ᶜ)) (𝓝 0) := by
  rw [(schwartz_withSeminorms ℝ (EuclideanSpace ℝ ι) ℂ).tendsto_nhds _ _]
  intro p ε hε
  obtain ⟨C, hC_nonneg, hC⟩ :=
    exists_seminorm_euclideanTranslateSchwartz_sub_lineDeriv_le_quadratic_norm
      φ p.1 p.2
  let δ : ℝ := min 1 (ε / (C + 1))
  have hδ_pos : 0 < δ := by
    have hC1 : 0 < C + 1 := by linarith
    have hquot : 0 < ε / (C + 1) := by positivity
    exact lt_min zero_lt_one hquot
  have hball :
      Metric.ball (0 : EuclideanSpace ℝ ι) δ ∩
          ({0}ᶜ : Set (EuclideanSpace ℝ ι)) ∈
        nhdsWithin (0 : EuclideanSpace ℝ ι)
          ({0}ᶜ : Set (EuclideanSpace ℝ ι)) := by
    simpa [Set.inter_comm] using
      (inter_mem_nhdsWithin ({0}ᶜ : Set (EuclideanSpace ℝ ι))
        (Metric.ball_mem_nhds (0 : EuclideanSpace ℝ ι) hδ_pos))
  refine Filter.mem_of_superset hball ?_
  intro h hh
  rcases hh with ⟨hh_ball, hh_punctured⟩
  have hh_norm_lt : ‖h‖ < δ := by
    simpa [dist_eq_norm] using hh_ball
  have hh_unit : ‖h‖ ≤ 1 := by
    exact le_trans (le_of_lt hh_norm_lt) (min_le_left _ _)
  have hh_ne : h ≠ 0 := by
    simpa using hh_punctured
  have hnorm_pos : 0 < ‖h‖ := norm_pos_iff.mpr hh_ne
  have hbound_quad := hC h hh_unit
  have hbound_linear :
      SchwartzMap.seminorm ℝ p.1 p.2
        (‖h‖⁻¹ •
          (euclideanTranslateSchwartzCLM h φ - φ - euclideanLineDerivDirectionCLM φ h)) ≤
        C * ‖h‖ := by
    calc
      SchwartzMap.seminorm ℝ p.1 p.2
          (‖h‖⁻¹ •
            (euclideanTranslateSchwartzCLM h φ - φ - euclideanLineDerivDirectionCLM φ h))
          = |‖h‖⁻¹| * SchwartzMap.seminorm ℝ p.1 p.2
              (euclideanTranslateSchwartzCLM h φ - φ - euclideanLineDerivDirectionCLM φ h) := by
              rw [map_smul_eq_mul, Real.norm_eq_abs]
      _ = ‖h‖⁻¹ * SchwartzMap.seminorm ℝ p.1 p.2
              (euclideanTranslateSchwartzCLM h φ - φ - euclideanLineDerivDirectionCLM φ h) := by
              rw [abs_of_nonneg (inv_nonneg.mpr (norm_nonneg h))]
      _ ≤ ‖h‖⁻¹ * (C * ‖h‖ ^ 2) := by
              exact mul_le_mul_of_nonneg_left hbound_quad
                (inv_nonneg.mpr (norm_nonneg h))
      _ = C * ‖h‖ := by
              field_simp [hnorm_pos.ne']
  have hδ_eps : C * ‖h‖ < ε := by
    have hC1 : 0 < C + 1 := by linarith
    have hC_le : C ≤ C + 1 := by linarith
    have hh_eps : ‖h‖ < ε / (C + 1) := lt_of_lt_of_le hh_norm_lt (min_le_right _ _)
    calc
      C * ‖h‖ ≤ (C + 1) * ‖h‖ := by
        gcongr
      _ < (C + 1) * (ε / (C + 1)) := by
        gcongr
      _ = ε := by
        field_simp [ne_of_gt hC1]
  simpa using lt_of_le_of_lt hbound_linear hδ_eps

/-- Candidate Frechet derivative of the reflected regularized distribution
`x ↦ T (euclideanReflectedTranslate x ρ)`. -/
noncomputable def regularizedDistributionFDeriv
    {ι : Type*} [Fintype ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι →L[ℝ] ℂ :=
  -(((T.restrictScalars ℝ).comp
      ((euclideanTranslateSchwartzCLM (-x)).restrictScalars ℝ)).comp
      (euclideanLineDerivDirectionCLM ρ))

@[simp]
theorem regularizedDistributionFDeriv_apply
    {ι : Type*} [Fintype ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (x v : EuclideanSpace ℝ ι) :
    regularizedDistributionFDeriv T ρ x v =
      -T (euclideanReflectedTranslate x
        (∂_{v} ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)) := by
  simp [regularizedDistributionFDeriv, euclideanReflectedTranslate]

/-- The checked line derivative agrees with the new Frechet-derivative
candidate on each direction. -/
theorem hasDerivAt_regularizedDistribution_along_fderiv_apply
    {ι : Type*} [Fintype ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (x v : EuclideanSpace ℝ ι) :
    HasDerivAt
      (fun t : ℝ => T (euclideanReflectedTranslate (x + t • v) ρ))
      (regularizedDistributionFDeriv T ρ x v)
      0 := by
  simpa using hasDerivAt_regularizedDistribution_along T ρ x v

private theorem regularizedDistribution_remainder_eq
    {ι : Type*} [Fintype ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (x h : EuclideanSpace ℝ ι) :
    let L : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℝ] ℂ :=
      (T.restrictScalars ℝ).comp
        ((euclideanTranslateSchwartzCLM (-x)).restrictScalars ℝ)
    let R : EuclideanSpace ℝ ι → SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
      fun h => ‖-h‖⁻¹ •
        (euclideanTranslateSchwartzCLM (-h) ρ - ρ - euclideanLineDerivDirectionCLM ρ (-h))
    L (R h) = ‖h‖⁻¹ •
      (T (euclideanReflectedTranslate (x + h) ρ) -
        T (euclideanReflectedTranslate x ρ) - regularizedDistributionFDeriv T ρ x h) := by
  simp [regularizedDistributionFDeriv, euclideanReflectedTranslate,
    euclideanLineDerivDirectionCLM_apply, euclideanTranslateSchwartzCLM_comp,
    norm_neg, map_add, sub_eq_add_neg, add_comm]
  ring

private theorem regularizedDistribution_remainder_norm_eq
    {ι : Type*} [Fintype ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (x h : EuclideanSpace ℝ ι) :
    let L : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℝ] ℂ :=
      (T.restrictScalars ℝ).comp
        ((euclideanTranslateSchwartzCLM (-x)).restrictScalars ℝ)
    let R : EuclideanSpace ℝ ι → SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
      fun h => ‖-h‖⁻¹ •
        (euclideanTranslateSchwartzCLM (-h) ρ - ρ - euclideanLineDerivDirectionCLM ρ (-h))
    ‖L (R h)‖ =
      ‖h‖⁻¹ * ‖T (euclideanReflectedTranslate (x + h) ρ) -
        T (euclideanReflectedTranslate x ρ) - regularizedDistributionFDeriv T ρ x h‖ := by
  dsimp only
  rw [regularizedDistribution_remainder_eq T ρ x h]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg h))]

private theorem regularizedDistribution_remainder_norm_tendsto_zero
    {ι : Type*} [Fintype ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (x : EuclideanSpace ℝ ι) :
    let L : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℝ] ℂ :=
      (T.restrictScalars ℝ).comp
        ((euclideanTranslateSchwartzCLM (-x)).restrictScalars ℝ)
    let R : EuclideanSpace ℝ ι → SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
      fun h => ‖-h‖⁻¹ •
        (euclideanTranslateSchwartzCLM (-h) ρ - ρ - euclideanLineDerivDirectionCLM ρ (-h))
    let G : EuclideanSpace ℝ ι → ℝ := fun h => ‖L (R h)‖
    Tendsto G (𝓝 (0 : EuclideanSpace ℝ ι)) (𝓝 0) := by
  let L : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℝ] ℂ :=
    (T.restrictScalars ℝ).comp
      ((euclideanTranslateSchwartzCLM (-x)).restrictScalars ℝ)
  let R : EuclideanSpace ℝ ι → SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
    fun h => ‖-h‖⁻¹ •
      (euclideanTranslateSchwartzCLM (-h) ρ - ρ - euclideanLineDerivDirectionCLM ρ (-h))
  let G : EuclideanSpace ℝ ι → ℝ := fun h => ‖L (R h)‖
  have hneg_nhds : Tendsto (fun h : EuclideanSpace ℝ ι => -h)
      (𝓝[≠] (0 : EuclideanSpace ℝ ι)) (𝓝 (0 : EuclideanSpace ℝ ι)) := by
    exact tendsto_nhdsWithin_of_tendsto_nhds (by simpa using
      (continuous_neg.tendsto (0 : EuclideanSpace ℝ ι)))
  have hneg_mem : ∀ᶠ h : EuclideanSpace ℝ ι in 𝓝[≠] (0 : EuclideanSpace ℝ ι),
      -h ∈ ({0}ᶜ : Set (EuclideanSpace ℝ ι)) := by
    filter_upwards [eventually_mem_nhdsWithin] with h hh
    simpa using (neg_ne_zero.mpr hh)
  have hneg : Tendsto (fun h : EuclideanSpace ℝ ι => -h)
      (𝓝[≠] (0 : EuclideanSpace ℝ ι))
      (𝓝[≠] (0 : EuclideanSpace ℝ ι)) := by
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (fun h : EuclideanSpace ℝ ι => -h) hneg_nhds hneg_mem
  have hbase :=
    (tendsto_frechetRemainder_euclideanTranslateSchwartz_zero ρ).comp hneg
  have hL_punct : Tendsto (fun h : EuclideanSpace ℝ ι => L (R h))
      (𝓝[≠] (0 : EuclideanSpace ℝ ι)) (𝓝 0) := by
    have hraw := L.continuous.continuousAt.tendsto.comp hbase
    simpa [R, Function.comp_def, norm_neg] using hraw
  have hnorm_punct : Tendsto G (𝓝[≠] (0 : EuclideanSpace ℝ ι)) (𝓝 0) := by
    simpa [G] using hL_punct.norm
  have hG0 : G 0 = 0 := by
    simp [G, R, L]
  have hnorm_pure : Tendsto G (pure (0 : EuclideanSpace ℝ ι)) (𝓝 0) := by
    simpa [hG0] using (tendsto_pure_nhds G (0 : EuclideanSpace ℝ ι))
  rw [← nhdsNE_sup_pure (0 : EuclideanSpace ℝ ι)]
  exact hnorm_punct.sup hnorm_pure

private theorem regularizedDistribution_remainder_norm_eq_sub
    {ι : Type*} [Fintype ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (x y : EuclideanSpace ℝ ι) :
    (let L : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℝ] ℂ :=
      (T.restrictScalars ℝ).comp
        ((euclideanTranslateSchwartzCLM (-x)).restrictScalars ℝ)
    let R : EuclideanSpace ℝ ι → SchwartzMap (EuclideanSpace ℝ ι) ℂ :=
      fun h => ‖-h‖⁻¹ •
        (euclideanTranslateSchwartzCLM (-h) ρ - ρ - euclideanLineDerivDirectionCLM ρ (-h))
    let G : EuclideanSpace ℝ ι → ℝ := fun h => ‖L (R h)‖
    G (y - x)) =
      ‖y - x‖⁻¹ * ‖T (euclideanReflectedTranslate y ρ) -
        T (euclideanReflectedTranslate x ρ) -
        regularizedDistributionFDeriv T ρ x (y - x)‖ := by
  dsimp only
  rw [regularizedDistribution_remainder_norm_eq T ρ x (y - x)]
  congr 2
  congr 1
  · congr 1
    abel_nf

private theorem regularizedDistribution_remainder_norm_tendsto_at
    {ι : Type*} [Fintype ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (x : EuclideanSpace ℝ ι) :
    Tendsto
      (fun y : EuclideanSpace ℝ ι =>
        ‖y - x‖⁻¹ * ‖T (euclideanReflectedTranslate y ρ) -
          T (euclideanReflectedTranslate x ρ) -
          regularizedDistributionFDeriv T ρ x (y - x)‖)
      (𝓝 x) (𝓝 0) := by
  have hshift : Tendsto (fun y : EuclideanSpace ℝ ι => y - x) (𝓝 x)
      (𝓝 (0 : EuclideanSpace ℝ ι)) := by
    simpa using (tendsto_id.sub tendsto_const_nhds :
      Tendsto (fun y : EuclideanSpace ℝ ι => y - x) (𝓝 x)
        (𝓝 (x - x)))
  have htarget := (regularizedDistribution_remainder_norm_tendsto_zero T ρ x).comp hshift
  refine htarget.congr' ?_
  exact Filter.Eventually.of_forall
    (fun y : EuclideanSpace ℝ ι => regularizedDistribution_remainder_norm_eq_sub T ρ x y)

/-- The reflected regularized distribution is Frechet differentiable in the
Euclidean center variable. -/
theorem hasFDerivAt_regularizedDistribution
    {ι : Type*} [Fintype ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ)
    (x : EuclideanSpace ℝ ι) :
    HasFDerivAt
      (fun x => T (euclideanReflectedTranslate x ρ))
      (regularizedDistributionFDeriv T ρ x) x := by
  rw [hasFDerivAt_iff_tendsto]
  exact regularizedDistribution_remainder_norm_tendsto_at T ρ x

private theorem contDiff_regularizedDistribution_nat
    {ι : Type*} [Fintype ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    ∀ r : ℕ, ContDiff ℝ (r : ℕ∞) (fun x : EuclideanSpace ℝ ι =>
      T (euclideanReflectedTranslate x ρ))
  | 0 => by
      have hd : Differentiable ℝ (fun x : EuclideanSpace ℝ ι =>
          T (euclideanReflectedTranslate x ρ)) := fun x =>
        (hasFDerivAt_regularizedDistribution T ρ x).differentiableAt
      exact (contDiff_zero (𝕜 := ℝ) (f := fun x : EuclideanSpace ℝ ι =>
        T (euclideanReflectedTranslate x ρ))).2 hd.continuous
  | r + 1 => by
      refine (contDiff_succ_iff_hasFDerivAt (𝕜 := ℝ)
        (E := EuclideanSpace ℝ ι) (F := ℂ)
        (f := fun x : EuclideanSpace ℝ ι => T (euclideanReflectedTranslate x ρ))
        (n := r)).2 ?_
      refine ⟨regularizedDistributionFDeriv T ρ, ?_, ?_⟩
      · rw [contDiff_clm_apply_iff]
        intro v
        have hbase := contDiff_regularizedDistribution_nat T
          (∂_{v} ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) r
        simpa [regularizedDistributionFDeriv_apply] using hbase.neg
      · intro x
        exact hasFDerivAt_regularizedDistribution T ρ x

/-- The reflected regularized distribution is smooth in the Euclidean center
variable. -/
theorem contDiff_regularizedDistribution
    {ι : Type*} [Fintype ι]
    (T : SchwartzMap (EuclideanSpace ℝ ι) ℂ →L[ℂ] ℂ)
    (ρ : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ ι =>
      T (euclideanReflectedTranslate x ρ)) := by
  rw [contDiff_iff_forall_nat_le]
  intro m _hm
  exact contDiff_regularizedDistribution_nat T ρ m

end SCV
