/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael R. Douglas, ModularPhysics Contributors
-/
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.Algebra.Module.FiniteDimension
import OSReconstruction.GeneralResults.DiffUnderIntegralSchwartz
import OSReconstruction.GeneralResults.FinProductIntegral
import OSReconstruction.SCV.SchwartzComplete
import OSReconstruction.SCV.SchwartzPrependField

/-!
# Fubini Exchange for Schwartz-Valued Integrals

A continuous linear functional on Schwartz space commutes with
parameter integrals of Schwartz-valued families.

## Main result

`schwartz_clm_fubini_exchange`: For T : S(ℝᵐ) →L[ℂ] ℂ and a
continuous family g : ℝᵐ → S(ℝᵐ) with polynomial seminorm growth,
there exists a Schwartz function Φ such that
  Φ(ξ) = ∫ g(x)(ξ) f(x) dx  and  T(Φ) = ∫ T(g(x)) f(x) dx.

## Mathematical content

This combines two facts:
1. The Schwartz-valued integral Φ = ∫ g(x) f(x) dx is well-defined
   as a Schwartz function (polynomial growth of seminorms × rapid
   decay of f gives convergent Schwartz-valued integral).
2. T is continuous linear, so T(∫ ...) = ∫ T(...) (CLM exchange).

Both follow from the nuclearity/Fréchet structure of Schwartz space.

## References

- Hörmander, "The Analysis of Linear PDOs I", Ch. 5
- Reed-Simon I, §V.3
- Vladimirov, "Methods of Generalized Functions", §25
-/

open MeasureTheory
noncomputable section

variable {m : ℕ}

-- Main CLM-integral exchange theorem is proved below after the bounded-set and
-- exhaustion infrastructure.

lemma integrable_schwartz_fubini_pointwise {m : ℕ}
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (ξ : Fin m → ℝ) :
    Integrable (fun x => g x ξ * f x) := by
  obtain ⟨C, N, hC, hCbound⟩ := hg_bound 0 0
  refine integrable_polyGrowth_mul_schwartz
    (g := fun x => g x ξ)
    (hg_meas := ?_)
    (C := C) (N := N) hC ?_ f
  · have hev :
        Continuous fun ψ : SchwartzMap (Fin m → ℝ) ℂ => ψ ξ := by
      simpa using
        (((BoundedContinuousFunction.evalCLM ℂ ξ).comp
          (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin m → ℝ) ℂ)).continuous)
    exact (hev.comp hg_cont).aestronglyMeasurable
  · intro x
    exact (SchwartzMap.norm_le_seminorm ℝ (g x) ξ).trans (hCbound x)

lemma clm_norm_le_finite_schwartz_seminorms {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
        ‖T ψ‖ ≤
          C * (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)) ψ := by
  let Treal : SchwartzMap (Fin m → ℝ) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun f => T f
      map_add' := fun f h => T.map_add f h
      map_smul' := by
        intro r f
        change T ((r : ℂ) • f) = (r : ℂ) • T f
        exact T.map_smul (r : ℂ) f }
  let q : Seminorm ℝ (SchwartzMap (Fin m → ℝ) ℂ) :=
    (normSeminorm ℝ ℂ).comp Treal
  have hq_cont : Continuous ⇑q := by
    dsimp [q, Treal]
    exact continuous_norm.comp T.continuous
  obtain ⟨s, C₀, hC₀, hbound⟩ :=
    Seminorm.bound_of_continuous
      (schwartz_withSeminorms ℝ (Fin m → ℝ) ℂ) q hq_cont
  refine ⟨s, C₀, ?_, fun ψ => ?_⟩
  · exact_mod_cast (pos_iff_ne_zero.mpr hC₀)
  · have h := hbound ψ
    simp only [q, Treal, Seminorm.comp_apply, coe_normSeminorm,
      LinearMap.coe_mk, AddHom.coe_mk, Seminorm.smul_apply, NNReal.smul_def,
      smul_eq_mul] at h
    exact h

lemma clm_norm_le_finite_schwartz_seminorms_complex {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
        ‖T ψ‖ ≤
          C * (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) ψ := by
  let q : Seminorm ℂ (SchwartzMap (Fin m → ℝ) ℂ) :=
    (normSeminorm ℂ ℂ).comp T.toLinearMap
  have hq_cont : Continuous ⇑q := by
    dsimp [q]
    exact continuous_norm.comp T.continuous
  obtain ⟨s, C₀, hC₀, hbound⟩ :=
    Seminorm.bound_of_continuous
      (schwartz_withSeminorms ℂ (Fin m → ℝ) ℂ) q hq_cont
  refine ⟨s, C₀, ?_, fun ψ => ?_⟩
  · exact_mod_cast (pos_iff_ne_zero.mpr hC₀)
  · have h := hbound ψ
    simp only [q, Seminorm.comp_apply, coe_normSeminorm,
      Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul] at h
    exact h

lemma clm_polyGrowth_of_seminorm_polyGrowth {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, ‖T (g x)‖ ≤ C * (1 + ‖x‖) ^ N := by
  let Treal : SchwartzMap (Fin m → ℝ) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun f => T f
      map_add' := fun f h => T.map_add f h
      map_smul' := by
        intro r f
        change T ((r : ℂ) • f) = (r : ℂ) • T f
        exact T.map_smul (r : ℂ) f }
  let q : Seminorm ℝ (SchwartzMap (Fin m → ℝ) ℂ) :=
    (normSeminorm ℝ ℂ).comp Treal
  have hq_cont : Continuous ⇑q := by
    dsimp [q, Treal]
    exact continuous_norm.comp T.continuous
  obtain ⟨s, C₀, _, hbound⟩ :=
    Seminorm.bound_of_continuous
      (schwartz_withSeminorms ℝ (Fin m → ℝ) ℂ) q hq_cont
  let Ds : ℕ × ℕ → ℝ := fun i => (hg_bound i.1 i.2).choose
  let Ns : ℕ × ℕ → ℕ := fun i => (hg_bound i.1 i.2).choose_spec.choose
  have hDs_pos : ∀ i, 0 < Ds i :=
    fun i => (hg_bound i.1 i.2).choose_spec.choose_spec.1
  have hDs_nonneg : ∀ i, 0 ≤ Ds i := fun i => (hDs_pos i).le
  have hDs_bound : ∀ (i : ℕ × ℕ) x,
      SchwartzMap.seminorm ℝ i.1 i.2 (g x) ≤
        Ds i * (1 + ‖x‖) ^ Ns i := by
    intro i x
    exact (hg_bound i.1 i.2).choose_spec.choose_spec.2 x
  let Nmax : ℕ := s.sup Ns
  let Cbase : ℝ := (C₀ : ℝ) * ∑ i ∈ s, Ds i
  have hCbase_nonneg : 0 ≤ Cbase :=
    mul_nonneg C₀.prop (Finset.sum_nonneg (fun i _ => hDs_nonneg i))
  refine ⟨Cbase + 1, Nmax, by linarith, fun x => ?_⟩
  have hq_eq : q (g x) = ‖T (g x)‖ := rfl
  rw [← hq_eq]
  have h1 : q (g x) ≤
      (C₀ : ℝ) *
        (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)) (g x) := by
    have h := hbound (g x)
    simp only [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul] at h
    linarith
  have h2 : (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)) (g x) ≤
      ∑ i ∈ s, Ds i * (1 + ‖x‖) ^ Ns i := by
    apply Seminorm.finset_sup_apply_le
      (Finset.sum_nonneg (fun i _ =>
        mul_nonneg (hDs_nonneg i) (pow_nonneg (by linarith [norm_nonneg x]) _)))
    intro ⟨p, qidx⟩ hi
    simp only [SchwartzMap.schwartzSeminormFamily_apply]
    exact (hDs_bound (p, qidx) x).trans
      (Finset.single_le_sum
        (fun i _ => mul_nonneg (hDs_nonneg i)
          (pow_nonneg (by linarith [norm_nonneg x]) _)) hi)
  have h3 : ∑ i ∈ s, Ds i * (1 + ‖x‖) ^ Ns i ≤
      (∑ i ∈ s, Ds i) * (1 + ‖x‖) ^ Nmax := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (hDs_nonneg i)
    exact pow_le_pow_right₀ (by linarith [norm_nonneg x])
      (Finset.le_sup (f := Ns) hi)
  calc
    q (g x)
        ≤ (C₀ : ℝ) * (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)) (g x) := h1
    _ ≤ (C₀ : ℝ) * ∑ i ∈ s, Ds i * (1 + ‖x‖) ^ Ns i :=
        mul_le_mul_of_nonneg_left h2 C₀.prop
    _ ≤ (C₀ : ℝ) * ((∑ i ∈ s, Ds i) * (1 + ‖x‖) ^ Nmax) :=
        mul_le_mul_of_nonneg_left h3 C₀.prop
    _ = Cbase * (1 + ‖x‖) ^ Nmax := by ring
    _ ≤ (Cbase + 1) * (1 + ‖x‖) ^ Nmax := by
        exact mul_le_mul_of_nonneg_right (by linarith)
          (pow_nonneg (by linarith [norm_nonneg x]) _)

lemma integrable_schwartz_fubini_clm_pairing {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    Integrable (fun x => T (g x) * f x) := by
  obtain ⟨C, N, hC, hCbound⟩ :=
    clm_polyGrowth_of_seminorm_polyGrowth T g hg_bound
  refine integrable_polyGrowth_mul_schwartz
    (g := fun x => T (g x))
    (hg_meas := ?_)
    (C := C) (N := N) hC hCbound f
  exact (T.continuous.comp hg_cont).aestronglyMeasurable

lemma integrableOn_schwartz_fubini_pointwise {m : ℕ}
    (K : Set (Fin m → ℝ))
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (ξ : Fin m → ℝ) :
    IntegrableOn (fun x => g x ξ * f x) K volume := by
  exact (integrable_schwartz_fubini_pointwise g f hg_cont hg_bound ξ).integrableOn

lemma integrableOn_schwartz_fubini_clm_pairing {m : ℕ}
    (K : Set (Fin m → ℝ))
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    IntegrableOn (fun x => T (g x) * f x) K volume := by
  exact (integrable_schwartz_fubini_clm_pairing T g f hg_cont hg_bound).integrableOn

def boundedParamIntegralScalar {m : ℕ}
    (K : Set (Fin m → ℝ))
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ) :
    (Fin m → ℝ) → ℂ :=
  fun ξ => ∫ x in K, g x ξ * f x

def boundedParamIntegralDeriv {m : ℕ}
    (K : Set (Fin m → ℝ))
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (n : ℕ) :
    (Fin m → ℝ) →
      ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ :=
  fun ξ =>
    ∫ x in K, f x • iteratedFDeriv ℝ n
      (fun η : Fin m → ℝ => g x η) ξ

lemma integrable_polyGrowth_mul_schwartz_norm {m : ℕ}
    (a : (Fin m → ℝ) → ℝ)
    (ha_meas : AEStronglyMeasurable a volume)
    (ha_nonneg : ∀ x, 0 ≤ a x)
    (C : ℝ) (N : ℕ) (hC : 0 < C)
    (ha_growth : ∀ x, a x ≤ C * (1 + ‖x‖) ^ N)
    (φ : SchwartzMap (Fin m → ℝ) ℂ) :
    Integrable (fun x => a x * ‖φ x‖) := by
  have hcomplex :
      Integrable (fun x => ((a x : ℂ) * φ x)) :=
    integrable_polyGrowth_mul_schwartz
      (g := fun x => (a x : ℂ))
      (hg_meas :=
        (Complex.measurable_ofReal.comp_aemeasurable ha_meas.aemeasurable).aestronglyMeasurable)
      (C := C) (N := N) hC ?_ φ
  · refine hcomplex.norm.congr ?_
    exact Filter.Eventually.of_forall fun x => by
      simp [abs_of_nonneg (ha_nonneg x)]
  · intro x
    simpa [RCLike.norm_ofReal, abs_of_nonneg (ha_nonneg x)] using ha_growth x

lemma integrable_schwartz_fubini_seminorm_weight {m : ℕ}
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (k n : ℕ) :
    Integrable fun x =>
      SchwartzMap.seminorm ℝ k n (g x) * ‖f x‖ := by
  obtain ⟨C, N, hC, hCbound⟩ := hg_bound k n
  exact integrable_polyGrowth_mul_schwartz_norm
    (a := fun x => SchwartzMap.seminorm ℝ k n (g x))
    (ha_meas :=
      (((schwartz_withSeminorms ℝ (Fin m → ℝ) ℂ).continuous_seminorm (k, n)).comp
        hg_cont).aestronglyMeasurable)
    (ha_nonneg := fun x => apply_nonneg _ _)
    (C := C) (N := N) hC
    hCbound f

lemma integrable_schwartz_fubini_finset_sum_seminorm_weight {m : ℕ}
    (s : Finset (ℕ × ℕ))
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    Integrable fun x =>
      (∑ i ∈ s, SchwartzMap.seminorm ℝ i.1 i.2 (g x)) * ‖f x‖ := by
  have hsum :
      Integrable
        (fun x => ∑ i ∈ s,
          SchwartzMap.seminorm ℝ i.1 i.2 (g x) * ‖f x‖) := by
    exact MeasureTheory.integrable_finset_sum s fun i _hi =>
      integrable_schwartz_fubini_seminorm_weight
        g f hg_cont hg_bound i.1 i.2
  convert hsum using 1
  ext x
  rw [Finset.sum_mul]

lemma schwartz_seminorm_complex_eq_real {m : ℕ}
    (k n : ℕ) (ψ : SchwartzMap (Fin m → ℝ) ℂ) :
    SchwartzMap.seminorm ℂ k n ψ = SchwartzMap.seminorm ℝ k n ψ := rfl

lemma schwartz_seminorm_real_complex_smul {m : ℕ}
    (k n : ℕ) (c : ℂ) (ψ : SchwartzMap (Fin m → ℝ) ℂ) :
    SchwartzMap.seminorm ℝ k n (c • ψ) =
      ‖c‖ * SchwartzMap.seminorm ℝ k n ψ := by
  rw [← schwartz_seminorm_complex_eq_real k n (c • ψ)]
  rw [map_smul_eq_mul]
  rw [schwartz_seminorm_complex_eq_real k n ψ]

lemma continuous_finset_sup_schwartzSeminormFamily {m : ℕ}
    (s : Finset (ℕ × ℕ)) :
    Continuous fun ψ : SchwartzMap (Fin m → ℝ) ℂ =>
      (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)) ψ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        (continuous_const : Continuous fun _ : SchwartzMap (Fin m → ℝ) ℂ => (0 : ℝ))
  | insert i s hi ih =>
      have hi_cont :
          Continuous fun ψ : SchwartzMap (Fin m → ℝ) ℂ =>
            (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ i) ψ :=
        (schwartz_withSeminorms ℝ (Fin m → ℝ) ℂ).continuous_seminorm i
      have hmax :
          Continuous fun ψ : SchwartzMap (Fin m → ℝ) ℂ =>
            max ((schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ i) ψ)
              ((s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)) ψ) :=
        hi_cont.max ih
      simpa [Finset.sup_insert, hi, Seminorm.sup_apply] using hmax

lemma integrable_schwartz_fubini_finset_sum_seminorm_weight_complex {m : ℕ}
    (s : Finset (ℕ × ℕ))
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    Integrable fun x =>
      (∑ i ∈ s, SchwartzMap.seminorm ℂ i.1 i.2 (g x)) * ‖f x‖ := by
  simpa using
    integrable_schwartz_fubini_finset_sum_seminorm_weight
      s g f hg_cont hg_bound

lemma clm_weighted_kernel_norm_le_finset_sum {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (s : Finset (ℕ × ℕ)) (C : ℝ) (hC_nonneg : 0 ≤ C)
    (hT : ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
      ‖T ψ‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) ψ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (x : Fin m → ℝ) :
    ‖T (f x • g x)‖ ≤
      C * ((∑ i ∈ s, SchwartzMap.seminorm ℂ i.1 i.2 (g x)) * ‖f x‖) := by
  have hsup_le :
      (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) (f x • g x) ≤
        ∑ i ∈ s, SchwartzMap.seminorm ℂ i.1 i.2 (f x • g x) := by
    calc
      (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) (f x • g x)
          ≤ (∑ i ∈ s, schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ i)
              (f x • g x) :=
            Seminorm.finset_sup_le_sum
              (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ) s
              (f x • g x)
      _ = ∑ i ∈ s, (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ i)
              (f x • g x) := by
            classical
            let p := schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ
            let y := f x • g x
            have hsum_apply :
                ∀ t : Finset (ℕ × ℕ), (∑ i ∈ t, p i) y = ∑ i ∈ t, (p i) y := by
              intro t
              induction t using Finset.induction_on with
              | empty =>
                  simp
              | insert a t ha ih =>
                  simp [Finset.sum_insert, ha, ih]
            exact hsum_apply s
      _ = ∑ i ∈ s, SchwartzMap.seminorm ℂ i.1 i.2 (f x • g x) := by
            apply Finset.sum_congr rfl
            intro i _hi
            cases i
            rfl
  have hsum_smul :
      (∑ i ∈ s, SchwartzMap.seminorm ℂ i.1 i.2 (f x • g x)) =
        ∑ i ∈ s, ‖f x‖ * SchwartzMap.seminorm ℂ i.1 i.2 (g x) := by
    apply Finset.sum_congr rfl
    intro i _hi
    exact map_smul_eq_mul (SchwartzMap.seminorm ℂ i.1 i.2) (f x) (g x)
  calc
    ‖T (f x • g x)‖
        ≤ C * (s.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) (f x • g x) :=
          hT (f x • g x)
    _ ≤ C * (∑ i ∈ s, SchwartzMap.seminorm ℂ i.1 i.2 (f x • g x)) :=
          mul_le_mul_of_nonneg_left hsup_le hC_nonneg
    _ = C * (∑ i ∈ s, ‖f x‖ * SchwartzMap.seminorm ℂ i.1 i.2 (g x)) := by
          rw [hsum_smul]
    _ = C * ((∑ i ∈ s, SchwartzMap.seminorm ℂ i.1 i.2 (g x)) * ‖f x‖) := by
          rw [← Finset.mul_sum]
          ring

lemma clm_norm_le_combined_real_finset_sup {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (sT u : Finset (ℕ × ℕ)) (C : ℝ) (hC_nonneg : 0 ≤ C)
    (hsT_sub : sT ⊆ u)
    (hT : ∀ ψ : SchwartzMap (Fin m → ℝ) ℂ,
      ‖T ψ‖ ≤ C * (sT.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) ψ)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ) :
    ‖T ψ‖ ≤ C * (u.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)) ψ := by
  have hsup :
      (sT.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) ψ ≤
        (u.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)) ψ := by
    apply Seminorm.finset_sup_apply_le (apply_nonneg _ _)
    intro i hi
    obtain ⟨k, n⟩ := i
    have hle :
        SchwartzMap.seminorm ℝ k n ψ ≤
          (u.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)) ψ :=
      (Finset.le_sup
        (f := schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)
        (hsT_sub hi)) ψ
    simpa [SchwartzMap.schwartzSeminormFamily_apply,
      schwartz_seminorm_complex_eq_real] using hle
  exact (hT ψ).trans (mul_le_mul_of_nonneg_left hsup hC_nonneg)

lemma integrable_schwartz_fubini_clm_weighted_kernel {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    Integrable fun x => T (f x • g x) := by
  obtain ⟨s, C, hC_pos, hT⟩ :=
    clm_norm_le_finite_schwartz_seminorms_complex T
  refine Integrable.mono'
    ((integrable_schwartz_fubini_finset_sum_seminorm_weight_complex
      s g f hg_cont hg_bound).const_mul C)
    ((T.continuous.comp (f.continuous.smul hg_cont)).aestronglyMeasurable)
    ?_
  exact Filter.Eventually.of_forall fun x =>
    clm_weighted_kernel_norm_le_finset_sum
      T s C hC_pos.le hT g f x

lemma integrableOn_schwartz_fubini_clm_weighted_kernel {m : ℕ}
    (K : Set (Fin m → ℝ))
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    IntegrableOn (fun x => T (f x • g x)) K volume := by
  exact (integrable_schwartz_fubini_clm_weighted_kernel
    T g f hg_cont hg_bound).integrableOn

lemma clm_finset_weighted_sum_exchange {m : ℕ} {ι : Type*}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (s : Finset ι)
    (c : ι → ℂ)
    (ψ : ι → SchwartzMap (Fin m → ℝ) ℂ) :
    T (∑ i ∈ s, c i • ψ i) = ∑ i ∈ s, c i * T (ψ i) := by
  classical
  calc
    T (∑ i ∈ s, c i • ψ i)
        = ∑ i ∈ s, T (c i • ψ i) := by
          rw [map_sum]
    _ = ∑ i ∈ s, c i * T (ψ i) := by
          apply Finset.sum_congr rfl
          intro i _hi
          simp [T.map_smul]

lemma clm_weighted_kernel_apply {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (x : Fin m → ℝ) :
    T (f x • g x) = T (g x) * f x := by
  calc
    T (f x • g x) = f x * T (g x) := by
      simpa using T.map_smul (f x) (g x)
    _ = T (g x) * f x := by ring

lemma integral_clm_weighted_kernel_eq_pairing {m : ℕ}
    (K : Set (Fin m → ℝ))
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ) :
    ∫ x in K, T (f x • g x) = ∫ x in K, T (g x) * f x := by
  exact integral_congr_ae <|
    Filter.Eventually.of_forall fun x =>
      clm_weighted_kernel_apply T g f x

lemma clm_exchange_of_tendsto_approximants {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (Φ : SchwartzMap (Fin m → ℝ) ℂ)
    (Φn : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (I : ℕ → ℂ)
    (J : ℂ)
    (hΦn : Filter.Tendsto Φn Filter.atTop (nhds Φ))
    (hI : Filter.Tendsto I Filter.atTop (nhds J))
    (hstep : ∀ n, T (Φn n) = I n) :
    T Φ = J := by
  have hTΦ :
      Filter.Tendsto (fun n => T (Φn n)) Filter.atTop (nhds (T Φ)) :=
    T.continuous.continuousAt.tendsto.comp hΦn
  have hTΦ' : Filter.Tendsto I Filter.atTop (nhds (T Φ)) := by
    convert hTΦ using 1
    ext n
    exact (hstep n).symm
  exact tendsto_nhds_unique hTΦ' hI

lemma tendsto_schwartz_atTop_iff_seminorm {m : ℕ}
    {u : ℕ → SchwartzMap (Fin m → ℝ) ℂ}
    {Φ : SchwartzMap (Fin m → ℝ) ℂ} :
    Filter.Tendsto u Filter.atTop (nhds Φ) ↔
      ∀ k n ε, 0 < ε →
        ∃ N, ∀ N' ≥ N,
          SchwartzMap.seminorm ℝ k n (u N' - Φ) < ε := by
  rw [(schwartz_withSeminorms ℝ (Fin m → ℝ) ℂ).tendsto_nhds_atTop u Φ]
  constructor
  · intro h k n ε hε
    simpa [SchwartzMap.schwartzSeminormFamily_apply] using h (k, n) ε hε
  · intro h i ε hε
    obtain ⟨k, n⟩ := i
    simpa [SchwartzMap.schwartzSeminormFamily_apply] using h k n ε hε

lemma tendsto_schwartz_atTop_of_tendsto_seminorm {m : ℕ}
    {u : ℕ → SchwartzMap (Fin m → ℝ) ℂ}
    {Φ : SchwartzMap (Fin m → ℝ) ℂ}
    (h : ∀ k n,
      Filter.Tendsto
        (fun N => SchwartzMap.seminorm ℝ k n (u N - Φ))
        Filter.atTop (nhds 0)) :
    Filter.Tendsto u Filter.atTop (nhds Φ) := by
  rw [tendsto_schwartz_atTop_iff_seminorm]
  intro k n ε hε
  have hev := (Metric.tendsto_nhds.mp (h k n)) ε hε
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨N, fun N' hN' => ?_⟩
  have hdist := hN N' hN'
  simpa [Real.dist_eq, abs_of_nonneg (apply_nonneg _ _)] using hdist

def boundedKernel {m : ℕ}
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ) :
    (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ :=
  fun x => f x • g x

lemma finset_sup_schwartzSeminorm_boundedKernel_le_sum {m : ℕ}
    (s : Finset (ℕ × ℕ))
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (x : Fin m → ℝ) :
    (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ))
        (boundedKernel g f x) ≤
      (∑ i ∈ s, SchwartzMap.seminorm ℝ i.1 i.2 (g x)) * ‖f x‖ := by
  classical
  have hsup_le :
      (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ))
          (boundedKernel g f x) ≤
        ∑ i ∈ s, SchwartzMap.seminorm ℝ i.1 i.2 (boundedKernel g f x) := by
    calc
      (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ))
          (boundedKernel g f x)
          ≤ (∑ i ∈ s, schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ i)
              (boundedKernel g f x) :=
            Seminorm.finset_sup_le_sum
              (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ) s
              (boundedKernel g f x)
      _ = ∑ i ∈ s, (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ i)
              (boundedKernel g f x) := by
            let p := schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ
            let y := boundedKernel g f x
            have hsum_apply :
                ∀ t : Finset (ℕ × ℕ), (∑ i ∈ t, p i) y = ∑ i ∈ t, (p i) y := by
              intro t
              induction t using Finset.induction_on with
              | empty =>
                  simp
              | insert a t ha ih =>
                  simp [Finset.sum_insert, ha, ih]
            exact hsum_apply s
      _ = ∑ i ∈ s, SchwartzMap.seminorm ℝ i.1 i.2 (boundedKernel g f x) := by
            apply Finset.sum_congr rfl
            intro i _hi
            cases i
            rfl
  have hsum_smul :
      (∑ i ∈ s, SchwartzMap.seminorm ℝ i.1 i.2 (boundedKernel g f x)) =
        ∑ i ∈ s, ‖f x‖ * SchwartzMap.seminorm ℝ i.1 i.2 (g x) := by
    apply Finset.sum_congr rfl
    intro i _hi
    exact schwartz_seminorm_real_complex_smul i.1 i.2 (f x) (g x)
  calc
    (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ))
        (boundedKernel g f x)
        ≤ ∑ i ∈ s, SchwartzMap.seminorm ℝ i.1 i.2 (boundedKernel g f x) := hsup_le
    _ = ∑ i ∈ s, ‖f x‖ * SchwartzMap.seminorm ℝ i.1 i.2 (g x) := hsum_smul
    _ = (∑ i ∈ s, SchwartzMap.seminorm ℝ i.1 i.2 (g x)) * ‖f x‖ := by
          rw [← Finset.mul_sum]
          ring

lemma integrable_schwartz_fubini_finset_sup_boundedKernel {m : ℕ}
    (s : Finset (ℕ × ℕ))
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    Integrable fun x =>
      (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ))
        (boundedKernel g f x) := by
  refine Integrable.mono'
    (integrable_schwartz_fubini_finset_sum_seminorm_weight
      s g f hg_cont hg_bound)
    ?_ ?_
  · exact
      (continuous_finset_sup_schwartzSeminormFamily s).comp
        (f.continuous.smul hg_cont)
      |>.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      have hnonneg :
          0 ≤ (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ))
            (boundedKernel g f x) :=
        apply_nonneg _ _
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using
        finset_sup_schwartzSeminorm_boundedKernel_le_sum s g f x

lemma exists_finite_schwartzKernel_seminorm_cover {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_bdd : Bornology.IsBounded K)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (s : Finset (ℕ × ℕ)) (η : ℝ) (hη : 0 < η) :
    ∃ t : Finset (Fin m → ℝ),
      K ⊆ ⋃ y ∈ t,
        {x | (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ))
          (boundedKernel g f y - boundedKernel g f x) < η} := by
  let F : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ := boundedKernel g f
  let p : Seminorm ℝ (SchwartzMap (Fin m → ℝ) ℂ) :=
    s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)
  let U : (Fin m → ℝ) → Set (Fin m → ℝ) :=
    fun y => {x | p (F y - F x) < η}
  have hF_cont : Continuous F := f.continuous.smul hg_cont
  have hU_open : ∀ y, IsOpen (U y) := by
    intro y
    have hcont : Continuous fun x => p (F y - F x) :=
      (continuous_finset_sup_schwartzSeminormFamily s).comp
        (continuous_const.sub hF_cont)
    exact isOpen_lt hcont continuous_const
  have hcover_closure : closure K ⊆ ⋃ y, U y := by
    intro x _hx
    refine Set.mem_iUnion.mpr ⟨x, ?_⟩
    simp [U, F, p, hη]
  obtain ⟨t, ht⟩ :=
    hK_bdd.isCompact_closure.elim_finite_subcover U hU_open hcover_closure
  refine ⟨t, ?_⟩
  exact (subset_closure.trans ht)

lemma exists_finite_partition_schwartzKernel_seminorm_approx {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (s : Finset (ℕ × ℕ)) (η : ℝ) (hη : 0 < η) :
    ∃ (ι : Type) (_ : Fintype ι) (A : ι → Set (Fin m → ℝ))
      (ψ : ι → SchwartzMap (Fin m → ℝ) ℂ),
      (∀ i, MeasurableSet (A i)) ∧
      Set.univ.PairwiseDisjoint A ∧
      K ⊆ ⋃ i, A i ∧
      (∀ i, A i ⊆ K) ∧
      (∀ i x, x ∈ A i →
        (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ))
          (ψ i - boundedKernel g f x) < η) := by
  classical
  obtain ⟨t, ht_cover⟩ :=
    exists_finite_schwartzKernel_seminorm_cover
      K hK_bdd g f hg_cont s η hη
  let center : Fin t.card → Fin m → ℝ :=
    fun i => ((Finset.equivFin t).symm i).1
  let F : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ := boundedKernel g f
  let p : Seminorm ℝ (SchwartzMap (Fin m → ℝ) ℂ) :=
    s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)
  let V : Fin t.card → Set (Fin m → ℝ) :=
    fun i => {x | p (F (center i) - F x) < η}
  let Vnat : ℕ → Set (Fin m → ℝ) :=
    fun n => if h : n < t.card then V ⟨n, h⟩ else ∅
  let A : Fin t.card → Set (Fin m → ℝ) :=
    fun i => K ∩ disjointed Vnat i.1
  let ψ : Fin t.card → SchwartzMap (Fin m → ℝ) ℂ :=
    fun i => F (center i)
  have hF_cont : Continuous F := f.continuous.smul hg_cont
  have hV_open : ∀ i, IsOpen (V i) := by
    intro i
    have hcont : Continuous fun x => p (F (center i) - F x) :=
      (continuous_finset_sup_schwartzSeminormFamily s).comp
        (continuous_const.sub hF_cont)
    exact isOpen_lt hcont continuous_const
  have hV_meas : ∀ i, MeasurableSet (V i) :=
    fun i => (hV_open i).measurableSet
  have hVnat_meas : ∀ n, MeasurableSet (Vnat n) := by
    intro n
    by_cases hn : n < t.card
    · simpa [Vnat, hn] using hV_meas ⟨n, hn⟩
    · simp [Vnat, hn]
  refine ⟨Fin t.card, inferInstance, A, ψ, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hK_meas.inter (MeasurableSet.disjointed hVnat_meas i.1)
  · intro i _hi j _hj hij
    have hne : (i : ℕ) ≠ j := by
      intro h
      exact hij (Fin.ext h)
    exact (disjoint_disjointed Vnat hne).mono
      Set.inter_subset_right Set.inter_subset_right
  · intro x hxK
    have hxV : x ∈ ⋃ i : Fin t.card, V i := by
      have hxcover := ht_cover hxK
      rcases Set.mem_iUnion.mp hxcover with ⟨y, hycover⟩
      rcases Set.mem_iUnion.mp hycover with ⟨hyt, hxU⟩
      refine Set.mem_iUnion.mpr ⟨Finset.equivFin t ⟨y, hyt⟩, ?_⟩
      simpa [V, F, p, center] using hxU
    have hxVnat : x ∈ ⋃ n : ℕ, Vnat n := by
      rcases Set.mem_iUnion.mp hxV with ⟨i, hxi⟩
      exact Set.mem_iUnion.mpr ⟨i.1, by simpa [Vnat, i.2] using hxi⟩
    have hxDnat : x ∈ ⋃ n : ℕ, disjointed Vnat n := by
      simpa [iUnion_disjointed] using hxVnat
    rcases Set.mem_iUnion.mp hxDnat with ⟨n, hxn⟩
    have hxVn : x ∈ Vnat n := disjointed_subset Vnat n hxn
    have hn : n < t.card := by
      by_contra hn
      simp [Vnat, hn] at hxVn
    exact Set.mem_iUnion.mpr ⟨⟨n, hn⟩, ⟨hxK, hxn⟩⟩
  · intro i x hx
    exact hx.1
  · intro i x hx
    have hxV : x ∈ Vnat i.1 := disjointed_subset Vnat i.1 hx.2
    simpa [ψ, Vnat, V, F, p, i.2] using hxV

noncomputable def finitePartitionKernel {m : ℕ} {ι : Type*} [Fintype ι]
    (A : ι → Set (Fin m → ℝ))
    (ψ : ι → SchwartzMap (Fin m → ℝ) ℂ) :
    (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ :=
  fun x => ∑ i, (A i).indicator (fun _ => (1 : ℂ)) x • ψ i

lemma finitePartitionKernel_apply_of_mem {m : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {A : ι → Set (Fin m → ℝ)}
    {ψ : ι → SchwartzMap (Fin m → ℝ) ℂ}
    (hA_disj : Set.univ.PairwiseDisjoint A)
    {i : ι} {x : Fin m → ℝ} (hx : x ∈ A i) :
    finitePartitionKernel A ψ x = ψ i := by
  classical
  unfold finitePartitionKernel
  rw [Finset.sum_eq_single i]
  · simp [Set.indicator_of_mem hx]
  · intro j _hj hji
    have hdis : Disjoint (A j) (A i) :=
      hA_disj (Set.mem_univ j) (Set.mem_univ i) hji
    have hxj : x ∉ A j := hdis.notMem_of_mem_right hx
    simp [Set.indicator_of_notMem hxj]
  · intro hi
    simp at hi

lemma finitePartitionKernel_error_lt_of_mem {m : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {K : Set (Fin m → ℝ)}
    {A : ι → Set (Fin m → ℝ)}
    {ψ : ι → SchwartzMap (Fin m → ℝ) ℂ}
    (hA_disj : Set.univ.PairwiseDisjoint A)
    (hA_cover : K ⊆ ⋃ i, A i)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (s : Finset (ℕ × ℕ)) {η : ℝ}
    (hcell : ∀ i x, x ∈ A i →
      (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ))
        (ψ i - boundedKernel g f x) < η)
    {x : Fin m → ℝ} (hxK : x ∈ K) :
    (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ))
      (finitePartitionKernel A ψ x - boundedKernel g f x) < η := by
  classical
  rcases Set.mem_iUnion.mp (hA_cover hxK) with ⟨i, hxi⟩
  rw [finitePartitionKernel_apply_of_mem hA_disj hxi]
  exact hcell i x hxi

lemma finitePartition_iUnion_eq {m : ℕ} {ι : Type*} [Fintype ι]
    {K : Set (Fin m → ℝ)} {A : ι → Set (Fin m → ℝ)}
    (hA_cover : K ⊆ ⋃ i, A i)
    (hA_sub : ∀ i, A i ⊆ K) :
    (⋃ i, A i) = K := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
    exact hA_sub i hxi
  · intro hx
    exact hA_cover hx

lemma setIntegral_finitePartition_eq_sum_of_integrableOn_cells {m : ℕ} {ι : Type*}
    [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set (Fin m → ℝ)} {A : ι → Set (Fin m → ℝ)}
    (hA_meas : ∀ i, MeasurableSet (A i))
    (hA_disj : Set.univ.PairwiseDisjoint A)
    (hA_cover : K ⊆ ⋃ i, A i)
    (hA_sub : ∀ i, A i ⊆ K)
    {H : (Fin m → ℝ) → E}
    (hH : ∀ i, IntegrableOn H (A i) volume) :
    ∫ x in K, H x = ∑ i, ∫ x in A i, H x := by
  have hUnion : (⋃ i, A i) = K :=
    finitePartition_iUnion_eq hA_cover hA_sub
  rw [← hUnion]
  exact MeasureTheory.integral_iUnion_fintype
    hA_meas
    (fun i j hij => hA_disj (Set.mem_univ i) (Set.mem_univ j) hij)
    hH

lemma setIntegral_finitePartition_eq_sum {m : ℕ} {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set (Fin m → ℝ)} {A : ι → Set (Fin m → ℝ)}
    (hA_meas : ∀ i, MeasurableSet (A i))
    (hA_disj : Set.univ.PairwiseDisjoint A)
    (hA_cover : K ⊆ ⋃ i, A i)
    (hA_sub : ∀ i, A i ⊆ K)
    {H : (Fin m → ℝ) → E}
    (hH : IntegrableOn H K volume) :
    ∫ x in K, H x = ∑ i, ∫ x in A i, H x := by
  have hUnion : (⋃ i, A i) = K :=
    finitePartition_iUnion_eq hA_cover hA_sub
  rw [← hUnion]
  exact MeasureTheory.integral_iUnion_fintype
    hA_meas
    (fun i j hij => hA_disj (Set.mem_univ i) (Set.mem_univ j) hij)
    (fun i => hH.mono_set (hA_sub i))

lemma setIntegral_const_complex {m : ℕ}
    (A : Set (Fin m → ℝ)) (c : ℂ) :
    ∫ _x in A, c = ((volume A).toReal : ℂ) * c := by
  rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def]
  exact Complex.real_smul

lemma measure_lt_top_of_subset_isBounded {m : ℕ}
    {K A : Set (Fin m → ℝ)}
    (hK_bdd : Bornology.IsBounded K) (hA_sub : A ⊆ K) :
    volume A < ⊤ :=
  lt_of_le_of_lt (MeasureTheory.measure_mono hA_sub) hK_bdd.measure_lt_top

lemma integrableOn_const_of_subset_isBounded {m : ℕ}
    {K A : Set (Fin m → ℝ)}
    (hK_bdd : Bornology.IsBounded K) (hA_sub : A ⊆ K) (c : ℂ) :
    IntegrableOn (fun _x : Fin m → ℝ => c) A volume :=
  MeasureTheory.integrableOn_const
    (hs := (measure_lt_top_of_subset_isBounded hK_bdd hA_sub).ne)

lemma integrableOn_const_of_subset_isBounded' {m : ℕ}
    {E : Type*} [NormedAddCommGroup E]
    {K A : Set (Fin m → ℝ)}
    (hK_bdd : Bornology.IsBounded K) (hA_sub : A ⊆ K) (c : E) :
    IntegrableOn (fun _x : Fin m → ℝ => c) A volume :=
  MeasureTheory.integrableOn_const
    (hs := (measure_lt_top_of_subset_isBounded hK_bdd hA_sub).ne)

lemma integral_clm_finitePartitionKernel {m : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {K : Set (Fin m → ℝ)} {A : ι → Set (Fin m → ℝ)}
    (hK_bdd : Bornology.IsBounded K)
    (hA_meas : ∀ i, MeasurableSet (A i))
    (hA_disj : Set.univ.PairwiseDisjoint A)
    (hA_cover : K ⊆ ⋃ i, A i)
    (hA_sub : ∀ i, A i ⊆ K)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (ψ : ι → SchwartzMap (Fin m → ℝ) ℂ) :
    ∫ x in K, T (finitePartitionKernel A ψ x) =
      ∑ i, ((volume (A i)).toReal : ℂ) * T (ψ i) := by
  classical
  have hcell_int :
      ∀ i, IntegrableOn
        (fun x => T (finitePartitionKernel A ψ x)) (A i) volume := by
    intro i
    refine (integrableOn_const_of_subset_isBounded hK_bdd (hA_sub i) (T (ψ i))).congr_fun_ae ?_
    exact (MeasureTheory.ae_restrict_iff' (hA_meas i)).2 <|
      Filter.Eventually.of_forall fun x hx =>
        by simpa [finitePartitionKernel_apply_of_mem hA_disj hx]
  calc
    ∫ x in K, T (finitePartitionKernel A ψ x)
        = ∑ i, ∫ x in A i, T (finitePartitionKernel A ψ x) :=
          setIntegral_finitePartition_eq_sum_of_integrableOn_cells
            hA_meas hA_disj hA_cover hA_sub hcell_int
    _ = ∑ i, ∫ _x in A i, T (ψ i) := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact MeasureTheory.setIntegral_congr_ae (hA_meas i) <|
            Filter.Eventually.of_forall fun x hx =>
              by simpa [finitePartitionKernel_apply_of_mem hA_disj hx]
    _ = ∑ i, ((volume (A i)).toReal : ℂ) * T (ψ i) := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact setIntegral_const_complex (A i) (T (ψ i))

lemma integrableOn_clm_finitePartitionKernel {m : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {K : Set (Fin m → ℝ)} {A : ι → Set (Fin m → ℝ)}
    (hK_bdd : Bornology.IsBounded K)
    (hA_meas : ∀ i, MeasurableSet (A i))
    (hA_disj : Set.univ.PairwiseDisjoint A)
    (hA_cover : K ⊆ ⋃ i, A i)
    (hA_sub : ∀ i, A i ⊆ K)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (ψ : ι → SchwartzMap (Fin m → ℝ) ℂ) :
    IntegrableOn (fun x => T (finitePartitionKernel A ψ x)) K volume := by
  classical
  have hcell_int :
      ∀ i, IntegrableOn
        (fun x => T (finitePartitionKernel A ψ x)) (A i) volume := by
    intro i
    refine (integrableOn_const_of_subset_isBounded hK_bdd (hA_sub i) (T (ψ i))).congr_fun_ae ?_
    exact (MeasureTheory.ae_restrict_iff' (hA_meas i)).2 <|
      Filter.Eventually.of_forall fun x hx =>
        by simpa [finitePartitionKernel_apply_of_mem hA_disj hx]
  have hUnion : (⋃ i, A i) = K :=
    finitePartition_iUnion_eq hA_cover hA_sub
  have hbi :
      IntegrableOn (fun x => T (finitePartitionKernel A ψ x))
        (⋃ i ∈ (Finset.univ : Finset ι), A i) volume := by
    exact (MeasureTheory.integrableOn_finset_iUnion
      (s := (Finset.univ : Finset ι)) (t := A)).2
      (fun i _hi => hcell_int i)
  simpa [hUnion] using hbi

lemma integral_eval_finitePartitionKernel {m : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {K : Set (Fin m → ℝ)} {A : ι → Set (Fin m → ℝ)}
    (hK_bdd : Bornology.IsBounded K)
    (hA_meas : ∀ i, MeasurableSet (A i))
    (hA_disj : Set.univ.PairwiseDisjoint A)
    (hA_cover : K ⊆ ⋃ i, A i)
    (hA_sub : ∀ i, A i ⊆ K)
    (ψ : ι → SchwartzMap (Fin m → ℝ) ℂ)
    (ξ : Fin m → ℝ) :
    ∫ x in K, finitePartitionKernel A ψ x ξ =
      ∑ i, ((volume (A i)).toReal : ℂ) * ψ i ξ := by
  classical
  have hcell_int :
      ∀ i, IntegrableOn
        (fun x => finitePartitionKernel A ψ x ξ) (A i) volume := by
    intro i
    refine (integrableOn_const_of_subset_isBounded hK_bdd (hA_sub i) (ψ i ξ)).congr_fun_ae ?_
    exact (MeasureTheory.ae_restrict_iff' (hA_meas i)).2 <|
      Filter.Eventually.of_forall fun x hx =>
        by simpa [finitePartitionKernel_apply_of_mem hA_disj hx]
  calc
    ∫ x in K, finitePartitionKernel A ψ x ξ
        = ∑ i, ∫ x in A i, finitePartitionKernel A ψ x ξ :=
          setIntegral_finitePartition_eq_sum_of_integrableOn_cells
            hA_meas hA_disj hA_cover hA_sub hcell_int
    _ = ∑ i, ∫ _x in A i, ψ i ξ := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact MeasureTheory.setIntegral_congr_ae (hA_meas i) <|
            Filter.Eventually.of_forall fun x hx =>
              by simpa [finitePartitionKernel_apply_of_mem hA_disj hx]
    _ = ∑ i, ((volume (A i)).toReal : ℂ) * ψ i ξ := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact setIntegral_const_complex (A i) (ψ i ξ)

lemma integral_iteratedFDeriv_finitePartitionKernel {m : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {K : Set (Fin m → ℝ)} {A : ι → Set (Fin m → ℝ)}
    (hK_bdd : Bornology.IsBounded K)
    (hA_meas : ∀ i, MeasurableSet (A i))
    (hA_disj : Set.univ.PairwiseDisjoint A)
    (hA_cover : K ⊆ ⋃ i, A i)
    (hA_sub : ∀ i, A i ⊆ K)
    (ψ : ι → SchwartzMap (Fin m → ℝ) ℂ)
    (n : ℕ) (ξ : Fin m → ℝ) :
    ∫ x in K,
        iteratedFDeriv ℝ n
          (fun ζ : Fin m → ℝ => finitePartitionKernel A ψ x ζ) ξ
      =
      ∑ i, (volume (A i)).toReal •
        iteratedFDeriv ℝ n (fun ζ : Fin m → ℝ => ψ i ζ) ξ := by
  classical
  have hcell_int :
      ∀ i, IntegrableOn
        (fun x =>
          iteratedFDeriv ℝ n
            (fun ζ : Fin m → ℝ => finitePartitionKernel A ψ x ζ) ξ)
        (A i) volume := by
    intro i
    refine (integrableOn_const_of_subset_isBounded'
      hK_bdd (hA_sub i)
      (iteratedFDeriv ℝ n (fun ζ : Fin m → ℝ => ψ i ζ) ξ)).congr_fun_ae ?_
    exact (MeasureTheory.ae_restrict_iff' (hA_meas i)).2 <|
      Filter.Eventually.of_forall fun x hx => by
        simp [finitePartitionKernel_apply_of_mem hA_disj hx]
  calc
    ∫ x in K,
        iteratedFDeriv ℝ n
          (fun ζ : Fin m → ℝ => finitePartitionKernel A ψ x ζ) ξ
        =
      ∑ i, ∫ x in A i,
        iteratedFDeriv ℝ n
          (fun ζ : Fin m → ℝ => finitePartitionKernel A ψ x ζ) ξ :=
        setIntegral_finitePartition_eq_sum_of_integrableOn_cells
          hA_meas hA_disj hA_cover hA_sub hcell_int
    _ = ∑ i, ∫ _x in A i,
        iteratedFDeriv ℝ n (fun ζ : Fin m → ℝ => ψ i ζ) ξ := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact MeasureTheory.setIntegral_congr_ae (hA_meas i) <|
            Filter.Eventually.of_forall fun x hx => by
              simp [finitePartitionKernel_apply_of_mem hA_disj hx]
    _ = ∑ i, (volume (A i)).toReal •
        iteratedFDeriv ℝ n (fun ζ : Fin m → ℝ => ψ i ζ) ξ := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def]

lemma finitePartitionApproximant_iteratedFDeriv_eq_integral {m : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {K : Set (Fin m → ℝ)} {A : ι → Set (Fin m → ℝ)}
    (hK_bdd : Bornology.IsBounded K)
    (hA_meas : ∀ i, MeasurableSet (A i))
    (hA_disj : Set.univ.PairwiseDisjoint A)
    (hA_cover : K ⊆ ⋃ i, A i)
    (hA_sub : ∀ i, A i ⊆ K)
    (ψ : ι → SchwartzMap (Fin m → ℝ) ℂ)
    (n : ℕ) (ξ : Fin m → ℝ) :
    iteratedFDeriv ℝ n
        (fun ζ : Fin m → ℝ =>
          (∑ i, ((volume (A i)).toReal : ℂ) • ψ i) ζ) ξ
      =
      ∫ x in K,
        iteratedFDeriv ℝ n
          (fun ζ : Fin m → ℝ => finitePartitionKernel A ψ x ζ) ξ := by
  classical
  rw [integral_iteratedFDeriv_finitePartitionKernel
    hK_bdd hA_meas hA_disj hA_cover hA_sub ψ n ξ]
  calc
    iteratedFDeriv ℝ n
        (fun ζ : Fin m → ℝ =>
          (∑ i, ((volume (A i)).toReal : ℂ) • ψ i) ζ) ξ
        =
      iteratedFDeriv ℝ n
        (fun ζ : Fin m → ℝ =>
          ∑ i, (((volume (A i)).toReal : ℂ) • ψ i) ζ) ξ := by
        congr 1
        funext ζ
        rw [SchwartzMap.sum_apply]
    _ =
      ∑ i,
        iteratedFDeriv ℝ n
          (fun ζ : Fin m → ℝ =>
            (((volume (A i)).toReal : ℂ) • ψ i) ζ) ξ := by
        exact iteratedFDeriv_fun_sum_apply (𝕜 := ℝ)
          (u := (Finset.univ : Finset ι))
          (f := fun i ζ =>
            (((volume (A i)).toReal : ℂ) • ψ i) ζ)
          (by
            intro i _hi
            simpa [SchwartzMap.smul_apply] using
              ((ψ i).contDiffAt n (x := ξ)).const_smul
                (((volume (A i)).toReal : ℂ)))
    _ =
      ∑ i, (volume (A i)).toReal •
        iteratedFDeriv ℝ n (fun ζ : Fin m → ℝ => ψ i ζ) ξ := by
        apply Finset.sum_congr rfl
        intro i _hi
        have hsmul :
            iteratedFDeriv ℝ n
              (fun ζ : Fin m → ℝ =>
                (((volume (A i)).toReal : ℂ) • ψ i) ζ) ξ =
            ((volume (A i)).toReal : ℂ) •
              iteratedFDeriv ℝ n (fun ζ : Fin m → ℝ => ψ i ζ) ξ := by
          simpa [SchwartzMap.smul_apply] using
            (iteratedFDeriv_const_smul_apply (𝕜 := ℝ)
              (a := ((volume (A i)).toReal : ℂ))
              ((ψ i).contDiffAt n (x := ξ)))
        exact hsmul.trans
          ((RCLike.real_smul_eq_coe_smul (K := ℂ)
            (volume (A i)).toReal
            (iteratedFDeriv ℝ n (fun ζ : Fin m → ℝ => ψ i ζ) ξ)).symm)

lemma integrableOn_iteratedFDeriv_finitePartitionKernel {m : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {K : Set (Fin m → ℝ)} {A : ι → Set (Fin m → ℝ)}
    (hK_bdd : Bornology.IsBounded K)
    (hA_meas : ∀ i, MeasurableSet (A i))
    (hA_disj : Set.univ.PairwiseDisjoint A)
    (hA_cover : K ⊆ ⋃ i, A i)
    (hA_sub : ∀ i, A i ⊆ K)
    (ψ : ι → SchwartzMap (Fin m → ℝ) ℂ)
    (n : ℕ) (ξ : Fin m → ℝ) :
    IntegrableOn
      (fun x =>
        iteratedFDeriv ℝ n
          (fun ζ : Fin m → ℝ => finitePartitionKernel A ψ x ζ) ξ)
      K volume := by
  classical
  have hcell_int :
      ∀ i, IntegrableOn
        (fun x =>
          iteratedFDeriv ℝ n
            (fun ζ : Fin m → ℝ => finitePartitionKernel A ψ x ζ) ξ)
        (A i) volume := by
    intro i
    refine (integrableOn_const_of_subset_isBounded'
      hK_bdd (hA_sub i)
      (iteratedFDeriv ℝ n (fun ζ : Fin m → ℝ => ψ i ζ) ξ)).congr_fun_ae ?_
    exact (MeasureTheory.ae_restrict_iff' (hA_meas i)).2 <|
      Filter.Eventually.of_forall fun x hx => by
        simp [finitePartitionKernel_apply_of_mem hA_disj hx]
  have hUnion : (⋃ i, A i) = K :=
    finitePartition_iUnion_eq hA_cover hA_sub
  have hbi :
      IntegrableOn
        (fun x =>
          iteratedFDeriv ℝ n
            (fun ζ : Fin m → ℝ => finitePartitionKernel A ψ x ζ) ξ)
        (⋃ i ∈ (Finset.univ : Finset ι), A i) volume := by
    exact (MeasureTheory.integrableOn_finset_iUnion
      (s := (Finset.univ : Finset ι)) (t := A)).2
      (fun i _hi => hcell_int i)
  simpa [hUnion] using hbi

lemma boundedKernel_iteratedFDeriv_eq {m : ℕ}
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (n : ℕ) (x ξ : Fin m → ℝ) :
    iteratedFDeriv ℝ n
        (fun ζ : Fin m → ℝ => boundedKernel g f x ζ) ξ =
      f x • iteratedFDeriv ℝ n (fun ζ : Fin m → ℝ => g x ζ) ξ := by
  simpa [boundedKernel, SchwartzMap.smul_apply] using
    (iteratedFDeriv_const_smul_apply (𝕜 := ℝ)
      (a := f x) ((g x).contDiffAt n (x := ξ)))

lemma finitePartitionApproximant_apply_eq_integral {m : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {K : Set (Fin m → ℝ)} {A : ι → Set (Fin m → ℝ)}
    (hK_bdd : Bornology.IsBounded K)
    (hA_meas : ∀ i, MeasurableSet (A i))
    (hA_disj : Set.univ.PairwiseDisjoint A)
    (hA_cover : K ⊆ ⋃ i, A i)
    (hA_sub : ∀ i, A i ⊆ K)
    (ψ : ι → SchwartzMap (Fin m → ℝ) ℂ)
    (ξ : Fin m → ℝ) :
    (∑ i, ((volume (A i)).toReal : ℂ) • ψ i) ξ =
      ∫ x in K, finitePartitionKernel A ψ x ξ := by
  rw [integral_eval_finitePartitionKernel
    hK_bdd hA_meas hA_disj hA_cover hA_sub ψ ξ]
  rw [SchwartzMap.sum_apply]
  simp only [SchwartzMap.smul_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  exact Complex.real_smul

lemma clm_finitePartitionKernel_error_norm_le {m : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {K : Set (Fin m → ℝ)} {A : ι → Set (Fin m → ℝ)}
    (hK_bdd : Bornology.IsBounded K)
    (hA_meas : ∀ i, MeasurableSet (A i))
    (hA_disj : Set.univ.PairwiseDisjoint A)
    (hA_cover : K ⊆ ⋃ i, A i)
    (hA_sub : ∀ i, A i ⊆ K)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (ψ : ι → SchwartzMap (Fin m → ℝ) ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    ‖(∫ x in K, T (finitePartitionKernel A ψ x)) -
        ∫ x in K, T (boundedKernel g f x)‖
      ≤ ∫ x in K,
          ‖T (finitePartitionKernel A ψ x - boundedKernel g f x)‖ := by
  have hpiece_int :
      IntegrableOn (fun x => T (finitePartitionKernel A ψ x)) K volume :=
    integrableOn_clm_finitePartitionKernel
      hK_bdd hA_meas hA_disj hA_cover hA_sub T ψ
  have hkernel_int :
      IntegrableOn (fun x => T (boundedKernel g f x)) K volume := by
    simpa [boundedKernel] using
      integrableOn_schwartz_fubini_clm_weighted_kernel
        K T g f hg_cont hg_bound
  have hpiece_int' := hpiece_int.integrable
  have hkernel_int' := hkernel_int.integrable
  calc
    ‖(∫ x in K, T (finitePartitionKernel A ψ x)) -
        ∫ x in K, T (boundedKernel g f x)‖
        = ‖∫ x in K,
            T (finitePartitionKernel A ψ x) - T (boundedKernel g f x)‖ := by
          rw [MeasureTheory.integral_sub hpiece_int' hkernel_int']
    _ = ‖∫ x in K,
            T (finitePartitionKernel A ψ x - boundedKernel g f x)‖ := by
          congr 1
          exact MeasureTheory.integral_congr_ae <|
            Filter.Eventually.of_forall fun x => by
              simp [map_sub]
    _ ≤ ∫ x in K,
          ‖T (finitePartitionKernel A ψ x - boundedKernel g f x)‖ :=
        MeasureTheory.norm_integral_le_integral_norm
          (fun x => T (finitePartitionKernel A ψ x - boundedKernel g f x))

lemma clm_finitePartitionKernel_error_norm_lt_of_uniform {m : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {K : Set (Fin m → ℝ)} {A : ι → Set (Fin m → ℝ)}
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (hA_meas : ∀ i, MeasurableSet (A i))
    (hA_disj : Set.univ.PairwiseDisjoint A)
    (hA_cover : K ⊆ ⋃ i, A i)
    (hA_sub : ∀ i, A i ⊆ K)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (ψ : ι → SchwartzMap (Fin m → ℝ) ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (sT u : Finset (ℕ × ℕ)) (C η ε : ℝ)
    (hC_pos : 0 < C)
    (hsT_sub : sT ⊆ u)
    (hT : ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
      ‖T φ‖ ≤ C * (sT.sup (schwartzSeminormFamily ℂ (Fin m → ℝ) ℂ)) φ)
    (hpoint : ∀ x ∈ K,
      (u.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ))
        (finitePartitionKernel A ψ x - boundedKernel g f x) < η)
    (hsmall : (volume K).toReal * (C * η) < ε) :
    ‖(∫ x in K, T (finitePartitionKernel A ψ x)) -
        ∫ x in K, T (boundedKernel g f x)‖ < ε := by
  have hbase :=
    clm_finitePartitionKernel_error_norm_le
      hK_bdd hA_meas hA_disj hA_cover hA_sub
      T ψ g f hg_cont hg_bound
  have hpiece_int :
      IntegrableOn (fun x => T (finitePartitionKernel A ψ x)) K volume :=
    integrableOn_clm_finitePartitionKernel
      hK_bdd hA_meas hA_disj hA_cover hA_sub T ψ
  have hkernel_int :
      IntegrableOn (fun x => T (boundedKernel g f x)) K volume := by
    simpa [boundedKernel] using
      integrableOn_schwartz_fubini_clm_weighted_kernel
        K T g f hg_cont hg_bound
  have hdiff_int :
      Integrable
        (fun x => T (finitePartitionKernel A ψ x - boundedKernel g f x))
        (volume.restrict K) := by
    refine (hpiece_int.sub hkernel_int).integrable.congr ?_
    exact Filter.Eventually.of_forall fun x => by
      simp [map_sub]
  have hnorm_int :
      Integrable
        (fun x => ‖T (finitePartitionKernel A ψ x - boundedKernel g f x)‖)
        (volume.restrict K) :=
    hdiff_int.norm
  haveI : IsFiniteMeasure (volume.restrict K) := by
    rw [MeasureTheory.isFiniteMeasure_restrict]
    exact ne_of_lt hK_bdd.measure_lt_top
  have hconst_int :
      Integrable (fun _x : Fin m → ℝ => C * η) (volume.restrict K) :=
    MeasureTheory.integrable_const (C * η)
  have hpoint_ae :
      ∀ᵐ x ∂volume.restrict K,
        ‖T (finitePartitionKernel A ψ x - boundedKernel g f x)‖ ≤ C * η := by
    exact (MeasureTheory.ae_restrict_iff' hK_meas).2 <|
      Filter.Eventually.of_forall fun x hxK => by
        have hT_point :=
          clm_norm_le_combined_real_finset_sup
            T sT u C hC_pos.le hsT_sub hT
            (finitePartitionKernel A ψ x - boundedKernel g f x)
        exact hT_point.trans
          (mul_le_mul_of_nonneg_left (le_of_lt (hpoint x hxK)) hC_pos.le)
  have hintegral_le :
      (∫ x in K,
          ‖T (finitePartitionKernel A ψ x - boundedKernel g f x)‖)
        ≤ ∫ _x in K, C * η :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      hconst_int
      hpoint_ae
  have hconst_eval :
      (∫ _x in K, C * η) = (volume K).toReal * (C * η) := by
    rw [MeasureTheory.integral_const, MeasureTheory.measureReal_restrict_apply_univ]
    simp [MeasureTheory.measureReal_def, smul_eq_mul]
  exact lt_of_le_of_lt (hbase.trans hintegral_le) (by simpa [hconst_eval] using hsmall)

lemma isFiniteMeasure_restrict_of_isBounded {m : ℕ}
    (K : Set (Fin m → ℝ)) (hK_bdd : Bornology.IsBounded K) :
    IsFiniteMeasure (volume.restrict K) := by
  rw [isFiniteMeasure_restrict]
  exact (ne_of_lt hK_bdd.measure_lt_top)

theorem bounded_parameter_integral_schwartz_clm_exchange_of_approximants {m : ℕ}
    (K : Set (Fin m → ℝ))
    (_hK_meas : MeasurableSet K)
    (_hK_bdd : Bornology.IsBounded K)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (_g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (_f : SchwartzMap (Fin m → ℝ) ℂ)
    (_hg_cont : Continuous _g)
    (_hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (_g x) ≤ C * (1 + ‖x‖) ^ N)
    (ΦK : SchwartzMap (Fin m → ℝ) ℂ)
    (hΦK : ∀ ξ, ΦK ξ = boundedParamIntegralScalar K _g _f ξ)
    (Φn : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (In : ℕ → ℂ)
    (hΦn : ∀ k n,
      Filter.Tendsto
        (fun N => SchwartzMap.seminorm ℝ k n (Φn N - ΦK))
        Filter.atTop (nhds 0))
    (hIn :
      Filter.Tendsto In Filter.atTop
        (nhds (∫ x in K, T (_f x • _g x))))
    (hstep : ∀ N, T (Φn N) = In N) :
    ∃ ΦK : SchwartzMap (Fin m → ℝ) ℂ,
      (∀ ξ, ΦK ξ = boundedParamIntegralScalar K _g _f ξ) ∧
      T ΦK = ∫ x in K, T (_g x) * _f x := by
  refine ⟨ΦK, hΦK, ?_⟩
  have hΦn_top : Filter.Tendsto Φn Filter.atTop (nhds ΦK) :=
    tendsto_schwartz_atTop_of_tendsto_seminorm hΦn
  have hT_eq_weighted :
      T ΦK = ∫ x in K, T (_f x • _g x) :=
    clm_exchange_of_tendsto_approximants
      T ΦK Φn In (∫ x in K, T (_f x • _g x))
      hΦn_top hIn hstep
  calc
    T ΦK = ∫ x in K, T (_f x • _g x) := hT_eq_weighted
    _ = ∫ x in K, T (_g x) * _f x :=
        integral_clm_weighted_kernel_eq_pairing K T _g _f

lemma continuous_schwartz_iteratedFDeriv_eval {m : ℕ}
    (n : ℕ) (ξ : Fin m → ℝ) :
    Continuous fun ψ : SchwartzMap (Fin m → ℝ) ℂ =>
      iteratedFDeriv ℝ n (fun η : Fin m → ℝ => ψ η) ξ := by
  let A :
      SchwartzMap (Fin m → ℝ) ℂ →ₗ[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ :=
    { toFun := fun ψ => iteratedFDeriv ℝ n (fun η : Fin m → ℝ => ψ η) ξ
      map_add' := by
        intro ψ φ
        ext v
        simpa [SchwartzMap.add_apply] using
          congrArg (fun L =>
            (L : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ) v)
            (iteratedFDeriv_add_apply
              (ψ.contDiffAt n) (φ.contDiffAt n) (x := ξ))
      map_smul' := by
        intro c ψ
        ext v
        simpa [SchwartzMap.smul_apply] using
          congrArg (fun L =>
            (L : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ) v)
            (iteratedFDeriv_const_smul_apply
              (a := c) (ψ.contDiffAt n) (x := ξ)) }
  have hA_cont : Continuous A := by
    refine WithSeminorms.continuous_normedSpace_rng
      (F := ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ)
      (schwartz_withSeminorms ℝ (Fin m → ℝ) ℂ) A ?_
    refine ⟨{(0, n)}, 1, ?_⟩
    intro ψ
    simp only [Seminorm.comp_apply, coe_normSeminorm, one_smul,
      Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply]
    exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ ψ n ξ
  simpa [A] using hA_cont

lemma norm_boundedParamIntegralDeriv_kernel_le {m : ℕ}
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (n : ℕ) (x ξ : Fin m → ℝ) :
    ‖f x • iteratedFDeriv ℝ n (fun η : Fin m → ℝ => g x η) ξ‖ ≤
      SchwartzMap.seminorm ℝ 0 n (g x) * ‖f x‖ := by
  calc
    ‖f x • iteratedFDeriv ℝ n (fun η : Fin m → ℝ => g x η) ξ‖
        = ‖f x‖ * ‖iteratedFDeriv ℝ n (fun η : Fin m → ℝ => g x η) ξ‖ := by
          rw [norm_smul]
    _ ≤ ‖f x‖ * SchwartzMap.seminorm ℝ 0 n (g x) := by
          exact mul_le_mul_of_nonneg_left
            (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ (g x) n ξ)
            (norm_nonneg _)
    _ = SchwartzMap.seminorm ℝ 0 n (g x) * ‖f x‖ := by
          ring

lemma integrableOn_boundedParamIntegral_iterated_deriv_kernel {m : ℕ}
    (K : Set (Fin m → ℝ))
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (n : ℕ) (ξ : Fin m → ℝ) :
    IntegrableOn
      (fun x => f x • iteratedFDeriv ℝ n
        (fun η : Fin m → ℝ => g x η) ξ)
      K volume := by
  refine Integrable.integrableOn ?_
  refine Integrable.mono'
    (integrable_schwartz_fubini_seminorm_weight g f hg_cont hg_bound 0 n) ?_ ?_
  · exact f.continuous.aestronglyMeasurable.smul
      ((continuous_schwartz_iteratedFDeriv_eval n ξ).comp hg_cont).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x =>
      norm_boundedParamIntegralDeriv_kernel_le g f n x ξ

lemma integral_continuousMultilinearCurryLeft {m n : ℕ}
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (φ : α →
      ContinuousMultilinearMap ℝ
        (fun _ : Fin (n + 1) => Fin m → ℝ) ℂ)
    (hφ : Integrable φ μ) :
    (∫ a,
      (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n + 1) => Fin m → ℝ) ℂ).toLinearIsometry.toContinuousLinearMap
        (φ a) ∂μ)
      =
    (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n + 1) => Fin m → ℝ) ℂ).toLinearIsometry.toContinuousLinearMap
      (∫ a, φ a ∂μ) := by
  letI :
      NormedAddCommGroup
        ((Fin m → ℝ) →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let e :=
    continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (n + 1) => Fin m → ℝ) ℂ
  have hcurried : Integrable (fun a => e (φ a)) μ :=
    hφ.congr'
      (e.continuous.comp_aestronglyMeasurable hφ.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun a => by simp [e])
  ext v tail
  change ((∫ a, e (φ a) ∂μ) v) tail = ((e (∫ a, φ a ∂μ)) v) tail
  have hcurried_v : Integrable (fun a => (e (φ a)) v) μ :=
    hcurried.apply_continuousLinearMap v
  rw [ContinuousLinearMap.integral_apply hcurried v]
  rw [ContinuousMultilinearMap.integral_apply hcurried_v tail]
  change (∫ x, φ x (Fin.cons v tail) ∂μ) =
    (∫ a, φ a ∂μ) (Fin.cons v tail)
  rw [ContinuousMultilinearMap.integral_apply hφ (Fin.cons v tail)]

lemma boundedParamIntegralDeriv_hasFDerivAt {m : ℕ}
    (K : Set (Fin m → ℝ))
    (_hK_meas : MeasurableSet K)
    (_hK_bdd : Bornology.IsBounded K)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (n : ℕ) (ξ : Fin m → ℝ) :
    HasFDerivAt
      (boundedParamIntegralDeriv K g f n)
      (∫ x in K,
        (continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (n + 1) => Fin m → ℝ) ℂ).toLinearIsometry.toContinuousLinearMap
          (f x • iteratedFDeriv ℝ (n + 1)
            (fun ζ : Fin m → ℝ => g x ζ) ξ))
      ξ := by
  let curryL :=
    (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (n + 1) => Fin m → ℝ) ℂ).toLinearIsometry.toContinuousLinearMap
  let F :
      (Fin m → ℝ) → (Fin m → ℝ) →
        ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ :=
    fun η x => f x • iteratedFDeriv ℝ n
      (fun ζ : Fin m → ℝ => g x ζ) η
  let F' :
      (Fin m → ℝ) → (Fin m → ℝ) →
        (Fin m → ℝ) →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ :=
    fun η x => curryL (f x • iteratedFDeriv ℝ (n + 1)
      (fun ζ : Fin m → ℝ => g x ζ) η)
  let bound : (Fin m → ℝ) → ℝ :=
    fun x => SchwartzMap.seminorm ℝ 0 (n + 1) (g x) * ‖f x‖
  have hF :
      HasFDerivAt (fun η => ∫ x, F η x ∂volume.restrict K)
        (∫ x, F' ξ x ∂volume.restrict K) ξ := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := volume.restrict K)
      (F := F) (F' := F') (bound := bound)
      (s := Set.univ) (x₀ := ξ) (by simp) ?_ ?_ ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun η =>
        f.continuous.aestronglyMeasurable.smul
          (((continuous_schwartz_iteratedFDeriv_eval n η).comp
            hg_cont).aestronglyMeasurable)
          |>.restrict
    · exact
        (integrableOn_boundedParamIntegral_iterated_deriv_kernel
          K g f hg_cont hg_bound n ξ).integrable
    · have hkernel :
          AEStronglyMeasurable
            (fun x => f x • iteratedFDeriv ℝ (n + 1)
              (fun ζ : Fin m → ℝ => g x ζ) ξ)
            (volume.restrict K) :=
        (integrableOn_boundedParamIntegral_iterated_deriv_kernel
          K g f hg_cont hg_bound (n + 1) ξ).integrable.aestronglyMeasurable
      exact curryL.continuous.comp_aestronglyMeasurable hkernel
    · exact Filter.Eventually.of_forall fun x η _ => by
        simpa [F', bound, curryL] using
          norm_boundedParamIntegralDeriv_kernel_le g f (n + 1) x η
    · exact
        (integrable_schwartz_fubini_seminorm_weight
          g f hg_cont hg_bound 0 (n + 1)).restrict
    · exact Filter.Eventually.of_forall fun x η _ => by
        have hbase :
            HasFDerivAt
              (fun η => iteratedFDeriv ℝ n
                (fun ζ : Fin m → ℝ => g x ζ) η)
              (fderiv ℝ
                (iteratedFDeriv ℝ n
                  (fun ζ : Fin m → ℝ => g x ζ)) η)
              η :=
          ((g x).smooth (n + 1)).differentiable_iteratedFDeriv
            (by exact_mod_cast Nat.lt_succ_self n) η |>.hasFDerivAt
        simpa [F, F', curryL, fderiv_iteratedFDeriv, Function.comp_def] using
          hbase.const_smul (f x)
  simpa [boundedParamIntegralDeriv, F, F', curryL] using hF

lemma boundedParamIntegralDeriv_hasFDerivAt_curry {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (n : ℕ) (ξ : Fin m → ℝ) :
    HasFDerivAt
      (boundedParamIntegralDeriv K g f n)
      ((continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (n + 1) => Fin m → ℝ) ℂ).toLinearIsometry.toContinuousLinearMap
        (boundedParamIntegralDeriv K g f (n + 1) ξ))
      ξ := by
  have hraw :=
    boundedParamIntegralDeriv_hasFDerivAt
      K hK_meas hK_bdd g f hg_cont hg_bound n ξ
  have hkernel_int :
      Integrable
        (fun x => f x • iteratedFDeriv ℝ (n + 1)
          (fun ζ : Fin m → ℝ => g x ζ) ξ)
        (volume.restrict K) :=
    (integrableOn_boundedParamIntegral_iterated_deriv_kernel
      K g f hg_cont hg_bound (n + 1) ξ).integrable
  let e :=
    continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (n + 1) => Fin m → ℝ) ℂ
  have hderiv_eq :
      (∫ x in K,
        e (f x • iteratedFDeriv ℝ (n + 1)
          (fun ζ : Fin m → ℝ => g x ζ) ξ)) =
        e (boundedParamIntegralDeriv K g f (n + 1) ξ) := by
    simpa [boundedParamIntegralDeriv, e] using
      integral_continuousMultilinearCurryLeft
        (μ := volume.restrict K)
        (φ := fun x => f x • iteratedFDeriv ℝ (n + 1)
          (fun ζ : Fin m → ℝ => g x ζ) ξ)
        hkernel_int
  simpa [e, hderiv_eq] using hraw

lemma boundedParamIntegralScalar_iteratedFDeriv_eq {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    ∀ n ξ,
      iteratedFDeriv ℝ n (boundedParamIntegralScalar K g f) ξ =
        boundedParamIntegralDeriv K g f n ξ := by
  intro n
  induction n with
  | zero =>
      intro ξ
      ext v
      have hkernel_int :
          Integrable
            (fun x => f x • iteratedFDeriv ℝ 0
              (fun η : Fin m → ℝ => g x η) ξ)
            (volume.restrict K) :=
        (integrableOn_boundedParamIntegral_iterated_deriv_kernel
          K g f hg_cont hg_bound 0 ξ).integrable
      simp only [iteratedFDeriv_zero_apply]
      change boundedParamIntegralScalar K g f ξ =
        (boundedParamIntegralDeriv K g f 0 ξ) v
      simp only [boundedParamIntegralScalar, boundedParamIntegralDeriv]
      rw [ContinuousMultilinearMap.integral_apply hkernel_int v]
      simp [iteratedFDeriv_zero_apply, mul_comm]
  | succ n ih =>
      intro ξ
      have hfun :
          iteratedFDeriv ℝ n (boundedParamIntegralScalar K g f) =
            fun η : Fin m → ℝ => boundedParamIntegralDeriv K g f n η := by
        funext η
        exact ih η
      have hfd :
          fderiv ℝ
            (iteratedFDeriv ℝ n (boundedParamIntegralScalar K g f)) ξ =
            ((continuousMultilinearCurryLeftEquiv ℝ
                (fun _ : Fin (n + 1) => Fin m → ℝ) ℂ).toLinearIsometry.toContinuousLinearMap
              (boundedParamIntegralDeriv K g f (n + 1) ξ)) := by
        have hderiv :=
          boundedParamIntegralDeriv_hasFDerivAt_curry
            K hK_meas hK_bdd g f hg_cont hg_bound n ξ
        rw [hfun]
        exact hderiv.fderiv
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hfd]
      simp

lemma boundedParamIntegralScalar_contDiff {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    ContDiff ℝ (⊤ : ℕ∞) (boundedParamIntegralScalar K g f) := by
  refine contDiff_of_differentiable_iteratedFDeriv ?_
  intro n _hn
  have hfun :
      iteratedFDeriv ℝ n (boundedParamIntegralScalar K g f) =
        fun η : Fin m → ℝ => boundedParamIntegralDeriv K g f n η := by
    funext η
    exact boundedParamIntegralScalar_iteratedFDeriv_eq
      K hK_meas hK_bdd g f hg_cont hg_bound n η
  rw [hfun]
  intro ξ
  exact (boundedParamIntegralDeriv_hasFDerivAt_curry
    K hK_meas hK_bdd g f hg_cont hg_bound n ξ).differentiableAt

lemma boundedParamIntegralScalar_decay_bound {m : ℕ}
    (K : Set (Fin m → ℝ))
    (_hK_meas : MeasurableSet K)
    (_hK_bdd : Bornology.IsBounded K)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (k n : ℕ) (ξ : Fin m → ℝ) :
    ‖ξ‖ ^ k *
        ‖∫ x in K, f x • iteratedFDeriv ℝ n
          (fun η : Fin m → ℝ => g x η) ξ‖
      ≤ ∫ x in K, SchwartzMap.seminorm ℝ k n (g x) * ‖f x‖ := by
  let kernel : (Fin m → ℝ) →
      ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ :=
    fun x => f x • iteratedFDeriv ℝ n
      (fun η : Fin m → ℝ => g x η) ξ
  let bound : (Fin m → ℝ) → ℝ :=
    fun x => SchwartzMap.seminorm ℝ k n (g x) * ‖f x‖
  have hkernel_int : Integrable kernel (volume.restrict K) :=
    (integrableOn_boundedParamIntegral_iterated_deriv_kernel
      K g f hg_cont hg_bound n ξ).integrable
  have hleft_int :
      Integrable (fun x => ‖ξ‖ ^ k * ‖kernel x‖) (volume.restrict K) :=
    hkernel_int.norm.const_mul _
  have hbound_int : Integrable bound (volume.restrict K) :=
    (integrable_schwartz_fubini_seminorm_weight g f hg_cont hg_bound k n).restrict
  have hpoint : ∀ x, ‖ξ‖ ^ k * ‖kernel x‖ ≤ bound x := by
    intro x
    have hderiv :
        ‖ξ‖ ^ k *
            ‖iteratedFDeriv ℝ n (fun η : Fin m → ℝ => g x η) ξ‖
          ≤ SchwartzMap.seminorm ℝ k n (g x) :=
      SchwartzMap.le_seminorm ℝ k n (g x) ξ
    calc
      ‖ξ‖ ^ k * ‖kernel x‖
          = ‖ξ‖ ^ k *
              (‖f x‖ *
                ‖iteratedFDeriv ℝ n (fun η : Fin m → ℝ => g x η) ξ‖) := by
            simp [kernel, norm_smul]
      _ = ‖f x‖ *
            (‖ξ‖ ^ k *
              ‖iteratedFDeriv ℝ n (fun η : Fin m → ℝ => g x η) ξ‖) := by
            ring
      _ ≤ ‖f x‖ * SchwartzMap.seminorm ℝ k n (g x) :=
            mul_le_mul_of_nonneg_left hderiv (norm_nonneg _)
      _ = bound x := by
            simp [bound, mul_comm]
  calc
    ‖ξ‖ ^ k * ‖∫ x in K, kernel x‖
        ≤ ‖ξ‖ ^ k * ∫ x in K, ‖kernel x‖ :=
          mul_le_mul_of_nonneg_left
            (norm_integral_le_integral_norm (μ := volume.restrict K) kernel)
            (pow_nonneg (norm_nonneg ξ) k)
    _ = ∫ x in K, ‖ξ‖ ^ k * ‖kernel x‖ := by
          exact (MeasureTheory.integral_const_mul (μ := volume.restrict K)
            (‖ξ‖ ^ k) (fun x => ‖kernel x‖)).symm
    _ ≤ ∫ x in K, bound x :=
          MeasureTheory.integral_mono hleft_int hbound_int hpoint
    _ = ∫ x in K, SchwartzMap.seminorm ℝ k n (g x) * ‖f x‖ := rfl

theorem bounded_parameter_integral_scalar_is_schwartz {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    ∃ ΦK : SchwartzMap (Fin m → ℝ) ℂ,
      ∀ ξ, ΦK ξ = boundedParamIntegralScalar K g f ξ := by
  let Φfun : (Fin m → ℝ) → ℂ := boundedParamIntegralScalar K g f
  refine ⟨
    { toFun := Φfun
      smooth' := ?_
      decay' := ?_ }, ?_⟩
  · exact boundedParamIntegralScalar_contDiff
      K hK_meas hK_bdd g f hg_cont hg_bound
  · intro k n
    refine ⟨∫ x in K, SchwartzMap.seminorm ℝ k n (g x) * ‖f x‖, fun ξ => ?_⟩
    have hiter :=
      boundedParamIntegralScalar_iteratedFDeriv_eq
        K hK_meas hK_bdd g f hg_cont hg_bound n ξ
    rw [hiter]
    exact boundedParamIntegralScalar_decay_bound
      K hK_meas hK_bdd g f hg_cont hg_bound k n ξ
  · intro ξ
    rfl

lemma finitePartition_error_iteratedFDeriv_eq_integral {m : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {K : Set (Fin m → ℝ)} {A : ι → Set (Fin m → ℝ)}
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (hA_meas : ∀ i, MeasurableSet (A i))
    (hA_disj : Set.univ.PairwiseDisjoint A)
    (hA_cover : K ⊆ ⋃ i, A i)
    (hA_sub : ∀ i, A i ⊆ K)
    (ψ : ι → SchwartzMap (Fin m → ℝ) ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (ΦK : SchwartzMap (Fin m → ℝ) ℂ)
    (hΦK : ∀ ξ, ΦK ξ = boundedParamIntegralScalar K g f ξ)
    (n : ℕ) (ξ : Fin m → ℝ) :
    iteratedFDeriv ℝ n
        (fun ζ : Fin m → ℝ =>
          ((∑ i, ((volume (A i)).toReal : ℂ) • ψ i) - ΦK) ζ) ξ
      =
      ∫ x in K,
        iteratedFDeriv ℝ n
          (fun ζ : Fin m → ℝ =>
            (finitePartitionKernel A ψ x - boundedKernel g f x) ζ) ξ := by
  classical
  let Φ : SchwartzMap (Fin m → ℝ) ℂ :=
    ∑ i, ((volume (A i)).toReal : ℂ) • ψ i
  have hΦ_deriv :
      iteratedFDeriv ℝ n (fun ζ : Fin m → ℝ => Φ ζ) ξ =
        ∫ x in K,
          iteratedFDeriv ℝ n
            (fun ζ : Fin m → ℝ => finitePartitionKernel A ψ x ζ) ξ := by
    simpa [Φ] using
      finitePartitionApproximant_iteratedFDeriv_eq_integral
        hK_bdd hA_meas hA_disj hA_cover hA_sub ψ n ξ
  have hΦK_fun :
      (fun ζ : Fin m → ℝ => ΦK ζ) = boundedParamIntegralScalar K g f :=
    funext hΦK
  have hΦK_deriv :
      iteratedFDeriv ℝ n (fun ζ : Fin m → ℝ => ΦK ζ) ξ =
        ∫ x in K,
          iteratedFDeriv ℝ n
            (fun ζ : Fin m → ℝ => boundedKernel g f x ζ) ξ := by
    calc
      iteratedFDeriv ℝ n (fun ζ : Fin m → ℝ => ΦK ζ) ξ
          =
        iteratedFDeriv ℝ n (boundedParamIntegralScalar K g f) ξ := by
          rw [hΦK_fun]
      _ = boundedParamIntegralDeriv K g f n ξ :=
          boundedParamIntegralScalar_iteratedFDeriv_eq
            K hK_meas hK_bdd g f hg_cont hg_bound n ξ
      _ = ∫ x in K,
            f x • iteratedFDeriv ℝ n (fun ζ : Fin m → ℝ => g x ζ) ξ := rfl
      _ = ∫ x in K,
            iteratedFDeriv ℝ n
              (fun ζ : Fin m → ℝ => boundedKernel g f x ζ) ξ := by
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall fun x =>
            (boundedKernel_iteratedFDeriv_eq g f n x ξ).symm
  have hpiece_int :
      Integrable
        (fun x =>
          iteratedFDeriv ℝ n
            (fun ζ : Fin m → ℝ => finitePartitionKernel A ψ x ζ) ξ)
        (volume.restrict K) :=
    (integrableOn_iteratedFDeriv_finitePartitionKernel
      hK_bdd hA_meas hA_disj hA_cover hA_sub ψ n ξ).integrable
  have hkernel_int :
      Integrable
        (fun x =>
          iteratedFDeriv ℝ n
            (fun ζ : Fin m → ℝ => boundedKernel g f x ζ) ξ)
        (volume.restrict K) := by
    refine
      (integrableOn_boundedParamIntegral_iterated_deriv_kernel
        K g f hg_cont hg_bound n ξ).integrable.congr ?_
    exact Filter.Eventually.of_forall fun x =>
      (boundedKernel_iteratedFDeriv_eq g f n x ξ).symm
  have hsub_left :
      iteratedFDeriv ℝ n
          (fun ζ : Fin m → ℝ => (Φ - ΦK) ζ) ξ =
        iteratedFDeriv ℝ n (fun ζ : Fin m → ℝ => Φ ζ) ξ -
          iteratedFDeriv ℝ n (fun ζ : Fin m → ℝ => ΦK ζ) ξ := by
    simpa [SchwartzMap.sub_apply, Pi.sub_apply] using
      (iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := n)
        (f := fun ζ : Fin m → ℝ => Φ ζ)
        (g := fun ζ : Fin m → ℝ => ΦK ζ)
        (Φ.contDiffAt n (x := ξ)) (ΦK.contDiffAt n (x := ξ)))
  calc
    iteratedFDeriv ℝ n
        (fun ζ : Fin m → ℝ =>
          ((∑ i, ((volume (A i)).toReal : ℂ) • ψ i) - ΦK) ζ) ξ
        =
      iteratedFDeriv ℝ n (fun ζ : Fin m → ℝ => Φ ζ) ξ -
        iteratedFDeriv ℝ n (fun ζ : Fin m → ℝ => ΦK ζ) ξ := by
        simpa [Φ] using hsub_left
    _ =
      (∫ x in K,
        iteratedFDeriv ℝ n
          (fun ζ : Fin m → ℝ => finitePartitionKernel A ψ x ζ) ξ) -
        ∫ x in K,
          iteratedFDeriv ℝ n
            (fun ζ : Fin m → ℝ => boundedKernel g f x ζ) ξ := by
        rw [hΦ_deriv, hΦK_deriv]
    _ =
      ∫ x in K,
        (iteratedFDeriv ℝ n
          (fun ζ : Fin m → ℝ => finitePartitionKernel A ψ x ζ) ξ -
          iteratedFDeriv ℝ n
            (fun ζ : Fin m → ℝ => boundedKernel g f x ζ) ξ) := by
        rw [MeasureTheory.integral_sub hpiece_int hkernel_int]
    _ =
      ∫ x in K,
        iteratedFDeriv ℝ n
          (fun ζ : Fin m → ℝ =>
            (finitePartitionKernel A ψ x - boundedKernel g f x) ζ) ξ := by
        apply MeasureTheory.integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          have hsub_point :=
            iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := n)
              (f := fun ζ : Fin m → ℝ => finitePartitionKernel A ψ x ζ)
              (g := fun ζ : Fin m → ℝ => boundedKernel g f x ζ)
              ((finitePartitionKernel A ψ x).contDiffAt n (x := ξ))
              ((boundedKernel g f x).contDiffAt n (x := ξ))
          simpa [SchwartzMap.sub_apply, Pi.sub_apply] using hsub_point.symm

lemma finitePartition_error_schwartzSeminorm_lt_of_uniform {m : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {K : Set (Fin m → ℝ)} {A : ι → Set (Fin m → ℝ)}
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (hA_meas : ∀ i, MeasurableSet (A i))
    (hA_disj : Set.univ.PairwiseDisjoint A)
    (hA_cover : K ⊆ ⋃ i, A i)
    (hA_sub : ∀ i, A i ⊆ K)
    (ψ : ι → SchwartzMap (Fin m → ℝ) ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (ΦK : SchwartzMap (Fin m → ℝ) ℂ)
    (hΦK : ∀ ξ, ΦK ξ = boundedParamIntegralScalar K g f ξ)
    (k n : ℕ) (η ε : ℝ) (hη_nonneg : 0 ≤ η)
    (hpoint : ∀ x ∈ K,
      SchwartzMap.seminorm ℝ k n
        (finitePartitionKernel A ψ x - boundedKernel g f x) < η)
    (hsmall : (volume K).toReal * η < ε) :
    SchwartzMap.seminorm ℝ k n
        ((∑ i, ((volume (A i)).toReal : ℂ) • ψ i) - ΦK) < ε := by
  classical
  let Φ : SchwartzMap (Fin m → ℝ) ℂ :=
    ∑ i, ((volume (A i)).toReal : ℂ) • ψ i
  let M : ℝ := ∫ _x in K, η
  haveI : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict_of_isBounded K hK_bdd
  have hconst_int : Integrable (fun _x : Fin m → ℝ => η) (volume.restrict K) :=
    MeasureTheory.integrable_const η
  have hM_nonneg : 0 ≤ M := by
    exact MeasureTheory.integral_nonneg (μ := volume.restrict K) fun _x => hη_nonneg
  have hM_eq : M = (volume K).toReal * η := by
    dsimp [M]
    rw [MeasureTheory.integral_const, MeasureTheory.measureReal_restrict_apply_univ]
    simp [MeasureTheory.measureReal_def, smul_eq_mul]
  have hseminorm_le :
      SchwartzMap.seminorm ℝ k n (Φ - ΦK) ≤ M := by
    refine SchwartzMap.seminorm_le_bound ℝ k n (Φ - ΦK) hM_nonneg ?_
    intro ξ
    have hderiv :
        iteratedFDeriv ℝ n (fun ζ : Fin m → ℝ => (Φ - ΦK) ζ) ξ =
          ∫ x in K,
            iteratedFDeriv ℝ n
              (fun ζ : Fin m → ℝ =>
                (finitePartitionKernel A ψ x - boundedKernel g f x) ζ) ξ := by
      simpa [Φ] using
        finitePartition_error_iteratedFDeriv_eq_integral
          hK_meas hK_bdd hA_meas hA_disj hA_cover hA_sub
          ψ g f hg_cont hg_bound ΦK hΦK n ξ
    let D : (Fin m → ℝ) →
        ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin m → ℝ) ℂ :=
      fun x =>
        iteratedFDeriv ℝ n
          (fun ζ : Fin m → ℝ =>
            (finitePartitionKernel A ψ x - boundedKernel g f x) ζ) ξ
    have hmono :
        (∫ x in K, ‖ξ‖ ^ k * ‖D x‖) ≤ ∫ _x in K, η := by
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _x => mul_nonneg
          (pow_nonneg (norm_nonneg ξ) k) (norm_nonneg _))
        hconst_int ?_
      exact (MeasureTheory.ae_restrict_iff' hK_meas).2 <|
        Filter.Eventually.of_forall fun x hxK => by
          have hle :
              ‖ξ‖ ^ k * ‖D x‖ ≤
                SchwartzMap.seminorm ℝ k n
                  (finitePartitionKernel A ψ x - boundedKernel g f x) :=
            SchwartzMap.le_seminorm ℝ k n
              (finitePartitionKernel A ψ x - boundedKernel g f x) ξ
          exact hle.trans (le_of_lt (hpoint x hxK))
    calc
      ‖ξ‖ ^ k *
          ‖iteratedFDeriv ℝ n (fun ζ : Fin m → ℝ => (Φ - ΦK) ζ) ξ‖
          =
        ‖ξ‖ ^ k * ‖∫ x in K, D x‖ := by
          rw [hderiv]
      _ ≤ ‖ξ‖ ^ k * ∫ x in K, ‖D x‖ :=
          mul_le_mul_of_nonneg_left
            (MeasureTheory.norm_integral_le_integral_norm
              (μ := volume.restrict K) D)
            (pow_nonneg (norm_nonneg ξ) k)
      _ = ∫ x in K, ‖ξ‖ ^ k * ‖D x‖ := by
          exact (MeasureTheory.integral_const_mul (μ := volume.restrict K)
            (‖ξ‖ ^ k) (fun x => ‖D x‖)).symm
      _ ≤ ∫ _x in K, η := hmono
      _ = M := rfl
  exact lt_of_le_of_lt (by simpa [Φ] using hseminorm_le)
    (by simpa [hM_eq] using hsmall)

lemma finitePartition_error_finsetSup_lt_of_uniform {m : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {K : Set (Fin m → ℝ)} {A : ι → Set (Fin m → ℝ)}
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (hA_meas : ∀ i, MeasurableSet (A i))
    (hA_disj : Set.univ.PairwiseDisjoint A)
    (hA_cover : K ⊆ ⋃ i, A i)
    (hA_sub : ∀ i, A i ⊆ K)
    (ψ : ι → SchwartzMap (Fin m → ℝ) ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (ΦK : SchwartzMap (Fin m → ℝ) ℂ)
    (hΦK : ∀ ξ, ΦK ξ = boundedParamIntegralScalar K g f ξ)
    (s : Finset (ℕ × ℕ)) (η ε : ℝ)
    (hη_nonneg : 0 ≤ η) (hε : 0 < ε)
    (hpoint : ∀ x ∈ K,
      (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ))
        (finitePartitionKernel A ψ x - boundedKernel g f x) < η)
    (hsmall : (volume K).toReal * η < ε) :
    (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ))
        ((∑ i, ((volume (A i)).toReal : ℂ) • ψ i) - ΦK) < ε := by
  classical
  refine Seminorm.finset_sup_apply_lt hε ?_
  rintro ⟨k, n⟩ hkn
  exact finitePartition_error_schwartzSeminorm_lt_of_uniform
    hK_meas hK_bdd hA_meas hA_disj hA_cover hA_sub
    ψ g f hg_cont hg_bound ΦK hΦK k n η ε hη_nonneg
    (fun x hxK => by
      have hle :
          SchwartzMap.seminorm ℝ k n
              (finitePartitionKernel A ψ x - boundedKernel g f x) ≤
            (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ))
              (finitePartitionKernel A ψ x - boundedKernel g f x) := by
        simpa [SchwartzMap.schwartzSeminormFamily_apply] using
          (Seminorm.le_finset_sup_apply
            (p := schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)
            (s := s)
            (x := finitePartitionKernel A ψ x - boundedKernel g f x)
            hkn)
      exact hle.trans_lt (hpoint x hxK))
    hsmall

lemma exists_finite_seminorm_kernel_approx {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (ΦK : SchwartzMap (Fin m → ℝ) ℂ)
    (hΦK : ∀ ξ, ΦK ξ = boundedParamIntegralScalar K g f ξ)
    (s : Finset (ℕ × ℕ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (Φ : SchwartzMap (Fin m → ℝ) ℂ) (I : ℂ),
      (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)) (Φ - ΦK) < ε ∧
      ‖I - ∫ x in K, T (f x • g x)‖ < ε ∧
      T Φ = I := by
  classical
  obtain ⟨sT, C, hC_pos, hT⟩ :=
    clm_norm_le_finite_schwartz_seminorms_complex T
  let u : Finset (ℕ × ℕ) := s ∪ sT
  let μK : ℝ := (volume K).toReal
  let η : ℝ := ε / (2 * (μK + 1) * (C + 1))
  have hμK_nonneg : 0 ≤ μK := ENNReal.toReal_nonneg
  have hden_pos : 0 < 2 * (μK + 1) * (C + 1) := by
    nlinarith [hμK_nonneg, hC_pos]
  have hη_pos : 0 < η := by
    exact div_pos hε hden_pos
  have hη_nonneg : 0 ≤ η := hη_pos.le
  have hbase_mul :
      (μK + 1) * (C + 1) * η = ε / 2 := by
    dsimp [η]
    field_simp [hden_pos.ne']
  have hsmall_seminorm : (volume K).toReal * η < ε := by
    have hμ_le : μK ≤ (μK + 1) * (C + 1) := by
      nlinarith [hμK_nonneg, hC_pos]
    calc
      (volume K).toReal * η = μK * η := rfl
      _ ≤ ((μK + 1) * (C + 1)) * η :=
          mul_le_mul_of_nonneg_right hμ_le hη_nonneg
      _ = ε / 2 := hbase_mul
      _ < ε := by linarith
  have hsmall_scalar : (volume K).toReal * (C * η) < ε := by
    have hμC_le : μK * C ≤ (μK + 1) * (C + 1) := by
      nlinarith [hμK_nonneg, hC_pos]
    calc
      (volume K).toReal * (C * η) = (μK * C) * η := by ring
      _ ≤ ((μK + 1) * (C + 1)) * η :=
          mul_le_mul_of_nonneg_right hμC_le hη_nonneg
      _ = ε / 2 := hbase_mul
      _ < ε := by linarith
  obtain ⟨ι, hι, A, ψ, hA_meas, hA_disj, hA_cover, hA_sub, hcell⟩ :=
    exists_finite_partition_schwartzKernel_seminorm_approx
      K hK_meas hK_bdd g f hg_cont u η hη_pos
  letI : Fintype ι := hι
  letI : DecidableEq ι := Classical.decEq ι
  let c : ι → ℂ := fun i => ((volume (A i)).toReal : ℂ)
  let Φ : SchwartzMap (Fin m → ℝ) ℂ := ∑ i, c i • ψ i
  let I : ℂ := ∑ i, c i * T (ψ i)
  have hs_sub : s ⊆ u := by
    intro i hi
    simp [u, hi]
  have hsT_sub : sT ⊆ u := by
    intro i hi
    simp [u, hi]
  have hpoint_u :
      ∀ x ∈ K,
        (u.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ))
          (finitePartitionKernel A ψ x - boundedKernel g f x) < η :=
    fun x hxK =>
      finitePartitionKernel_error_lt_of_mem
        hA_disj hA_cover g f u hcell hxK
  have hpoint_s :
      ∀ x ∈ K,
        (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ))
          (finitePartitionKernel A ψ x - boundedKernel g f x) < η := by
    intro x hxK
    have hle :
        (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ))
            (finitePartitionKernel A ψ x - boundedKernel g f x) ≤
          (u.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ))
            (finitePartitionKernel A ψ x - boundedKernel g f x) := by
      refine Seminorm.finset_sup_apply_le (apply_nonneg _ _) ?_
      intro i hi
      exact
        Seminorm.le_finset_sup_apply
          (p := schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)
          (s := u)
          (x := finitePartitionKernel A ψ x - boundedKernel g f x)
          (hs_sub hi)
    exact hle.trans_lt (hpoint_u x hxK)
  have hseminorm :
      (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)) (Φ - ΦK) < ε := by
    simpa [Φ, c] using
      finitePartition_error_finsetSup_lt_of_uniform
        hK_meas hK_bdd hA_meas hA_disj hA_cover hA_sub
        ψ g f hg_cont hg_bound ΦK hΦK
        s η ε hη_nonneg hε hpoint_s hsmall_seminorm
  have hscalar_piece :
      ‖(∫ x in K, T (finitePartitionKernel A ψ x)) -
          ∫ x in K, T (boundedKernel g f x)‖ < ε :=
    clm_finitePartitionKernel_error_norm_lt_of_uniform
      hK_meas hK_bdd hA_meas hA_disj hA_cover hA_sub
      T ψ g f hg_cont hg_bound sT u C η ε
      hC_pos hsT_sub hT hpoint_u hsmall_scalar
  have hI_piece :
      I = ∫ x in K, T (finitePartitionKernel A ψ x) := by
    dsimp [I, c]
    exact (integral_clm_finitePartitionKernel
      hK_bdd hA_meas hA_disj hA_cover hA_sub T ψ).symm
  have hscalar :
      ‖I - ∫ x in K, T (f x • g x)‖ < ε := by
    simpa [hI_piece, boundedKernel] using hscalar_piece
  have hstep : T Φ = I := by
    simpa [Φ, I, c] using
      clm_finset_weighted_sum_exchange
        T (Finset.univ : Finset ι) c ψ
  exact ⟨Φ, I, hseminorm, hscalar, hstep⟩

def schwartzSeminormIndexBox (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (N + 1)).product (Finset.range (N + 1))

lemma mem_schwartzSeminormIndexBox {k n N : ℕ}
    (hk : k ≤ N) (hn : n ≤ N) :
    (k, n) ∈ schwartzSeminormIndexBox N := by
  simp [schwartzSeminormIndexBox, hk, hn]

lemma schwartzSeminorm_le_finset_sup {m : ℕ}
    (s : Finset (ℕ × ℕ)) {k n : ℕ} (hmem : (k, n) ∈ s)
    (ψ : SchwartzMap (Fin m → ℝ) ℂ) :
    SchwartzMap.seminorm ℝ k n ψ ≤
      (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)) ψ := by
  exact (Finset.le_sup
    (f := schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)
    hmem) ψ

theorem exists_bounded_kernel_approximants_of_finite_seminorm_approx {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (hfinite :
      ∀ (ΦK : SchwartzMap (Fin m → ℝ) ℂ),
        (∀ ξ, ΦK ξ = boundedParamIntegralScalar K g f ξ) →
        ∀ (s : Finset (ℕ × ℕ)) (ε : ℝ), 0 < ε →
          ∃ (Φ : SchwartzMap (Fin m → ℝ) ℂ) (I : ℂ),
            (s.sup (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)) (Φ - ΦK) < ε ∧
            ‖I - ∫ x in K, T (f x • g x)‖ < ε ∧
            T Φ = I) :
    ∃ (Φn : ℕ → SchwartzMap (Fin m → ℝ) ℂ) (In : ℕ → ℂ),
      (∀ k n,
        Filter.Tendsto
          (fun N => SchwartzMap.seminorm ℝ k n
            (Φn N -
              Classical.choose
                (bounded_parameter_integral_scalar_is_schwartz
                  K hK_meas hK_bdd g f hg_cont hg_bound)))
          Filter.atTop (nhds 0)) ∧
      Filter.Tendsto In Filter.atTop
        (nhds (∫ x in K, T (f x • g x))) ∧
      ∀ N, T (Φn N) = In N := by
  classical
  let ΦK : SchwartzMap (Fin m → ℝ) ℂ :=
    Classical.choose
      (bounded_parameter_integral_scalar_is_schwartz
        K hK_meas hK_bdd g f hg_cont hg_bound)
  have hΦK : ∀ ξ, ΦK ξ = boundedParamIntegralScalar K g f ξ :=
    Classical.choose_spec
      (bounded_parameter_integral_scalar_is_schwartz
        K hK_meas hK_bdd g f hg_cont hg_bound)
  let εN : ℕ → ℝ := fun N => (N + 1 : ℝ)⁻¹
  have hεN_pos : ∀ N, 0 < εN N := by
    intro N
    exact inv_pos.mpr (by positivity)
  let approx : ∀ N,
      ∃ (Φ : SchwartzMap (Fin m → ℝ) ℂ) (I : ℂ),
        ((schwartzSeminormIndexBox N).sup
          (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)) (Φ - ΦK) < εN N ∧
        ‖I - ∫ x in K, T (f x • g x)‖ < εN N ∧
        T Φ = I := fun N =>
    hfinite ΦK hΦK (schwartzSeminormIndexBox N) (εN N) (hεN_pos N)
  let Φn : ℕ → SchwartzMap (Fin m → ℝ) ℂ :=
    fun N => Classical.choose (approx N)
  let In : ℕ → ℂ :=
    fun N => Classical.choose (Classical.choose_spec (approx N))
  have hΦn_bound : ∀ N,
      ((schwartzSeminormIndexBox N).sup
        (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)) (Φn N - ΦK) < εN N := by
    intro N
    exact (Classical.choose_spec (Classical.choose_spec (approx N))).1
  have hIn_bound : ∀ N,
      ‖In N - ∫ x in K, T (f x • g x)‖ < εN N := by
    intro N
    exact (Classical.choose_spec (Classical.choose_spec (approx N))).2.1
  have hstep : ∀ N, T (Φn N) = In N := by
    intro N
    exact (Classical.choose_spec (Classical.choose_spec (approx N))).2.2
  refine ⟨Φn, In, ?_, ?_, hstep⟩
  · intro k n
    rw [Metric.tendsto_nhds]
    intro δ hδ
    obtain ⟨Nδ, hNδ⟩ := exists_nat_one_div_lt hδ
    refine Filter.eventually_atTop.2 ⟨max (max k n) Nδ, ?_⟩
    intro N hN
    have hkN : k ≤ N :=
      le_trans (le_max_left k n)
        (le_trans (le_max_left (max k n) Nδ) hN)
    have hnN : n ≤ N :=
      le_trans (le_max_right k n)
        (le_trans (le_max_left (max k n) Nδ) hN)
    have hNδN : Nδ ≤ N :=
      le_trans (le_max_right (max k n) Nδ) hN
    have hsingle_le :
        SchwartzMap.seminorm ℝ k n (Φn N - ΦK) ≤
          ((schwartzSeminormIndexBox N).sup
            (schwartzSeminormFamily ℝ (Fin m → ℝ) ℂ)) (Φn N - ΦK) :=
      schwartzSeminorm_le_finset_sup
        (s := schwartzSeminormIndexBox N)
        (mem_schwartzSeminormIndexBox hkN hnN)
        (Φn N - ΦK)
    have hε_le : εN N ≤ εN Nδ := by
      dsimp [εN]
      exact (inv_le_inv₀
        (by positivity : (0 : ℝ) < N + 1)
        (by positivity : (0 : ℝ) < Nδ + 1)).2
        (by exact_mod_cast Nat.succ_le_succ hNδN)
    have hNδ_small : εN Nδ < δ := by
      simpa [εN, one_div] using hNδ
    have hsmall :
        SchwartzMap.seminorm ℝ k n (Φn N - ΦK) < δ :=
      lt_of_le_of_lt hsingle_le
        (lt_of_lt_of_le (hΦn_bound N)
          (le_trans hε_le (le_of_lt hNδ_small)))
    simpa [Real.dist_eq, abs_of_nonneg (apply_nonneg _ _)] using hsmall
  · rw [Metric.tendsto_nhds]
    intro δ hδ
    obtain ⟨Nδ, hNδ⟩ := exists_nat_one_div_lt hδ
    refine Filter.eventually_atTop.2 ⟨Nδ, ?_⟩
    intro N hN
    have hε_le : εN N ≤ εN Nδ := by
      dsimp [εN]
      exact (inv_le_inv₀
        (by positivity : (0 : ℝ) < N + 1)
        (by positivity : (0 : ℝ) < Nδ + 1)).2
        (by exact_mod_cast Nat.succ_le_succ hN)
    have hNδ_small : εN Nδ < δ := by
      simpa [εN, one_div] using hNδ
    have hsmall : ‖In N - ∫ x in K, T (f x • g x)‖ < δ :=
      lt_of_lt_of_le (hIn_bound N) (le_trans hε_le (le_of_lt hNδ_small))
    simpa [dist_eq_norm] using hsmall

theorem exists_bounded_kernel_approximants {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    ∃ (Φn : ℕ → SchwartzMap (Fin m → ℝ) ℂ) (In : ℕ → ℂ),
      (∀ k n,
        Filter.Tendsto
          (fun N => SchwartzMap.seminorm ℝ k n
            (Φn N -
              Classical.choose
                (bounded_parameter_integral_scalar_is_schwartz
                  K hK_meas hK_bdd g f hg_cont hg_bound)))
          Filter.atTop (nhds 0)) ∧
      Filter.Tendsto In Filter.atTop
        (nhds (∫ x in K, T (f x • g x))) ∧
      ∀ N, T (Φn N) = In N := by
  exact
    exists_bounded_kernel_approximants_of_finite_seminorm_approx
      K hK_meas hK_bdd T g f hg_cont hg_bound
      (fun ΦK hΦK s ε hε =>
        exists_finite_seminorm_kernel_approx
          K hK_meas hK_bdd T g f hg_cont hg_bound
          ΦK hΦK s ε hε)

theorem bounded_parameter_integral_schwartz_clm_exchange_of_choose_approximants {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (Φn : ℕ → SchwartzMap (Fin m → ℝ) ℂ)
    (In : ℕ → ℂ)
    (hΦn : ∀ k n,
      Filter.Tendsto
        (fun N => SchwartzMap.seminorm ℝ k n
          (Φn N -
            Classical.choose
              (bounded_parameter_integral_scalar_is_schwartz
                K hK_meas hK_bdd g f hg_cont hg_bound)))
        Filter.atTop (nhds 0))
    (hIn :
      Filter.Tendsto In Filter.atTop
        (nhds (∫ x in K, T (f x • g x))))
    (hstep : ∀ N, T (Φn N) = In N) :
    ∃ ΦK : SchwartzMap (Fin m → ℝ) ℂ,
      (∀ ξ, ΦK ξ = boundedParamIntegralScalar K g f ξ) ∧
      T ΦK = ∫ x in K, T (g x) * f x := by
  let ΦK : SchwartzMap (Fin m → ℝ) ℂ :=
    Classical.choose
      (bounded_parameter_integral_scalar_is_schwartz
        K hK_meas hK_bdd g f hg_cont hg_bound)
  have hΦK : ∀ ξ, ΦK ξ = boundedParamIntegralScalar K g f ξ :=
    Classical.choose_spec
      (bounded_parameter_integral_scalar_is_schwartz
        K hK_meas hK_bdd g f hg_cont hg_bound)
  exact
    bounded_parameter_integral_schwartz_clm_exchange_of_approximants
      K hK_meas hK_bdd T g f hg_cont hg_bound
      ΦK hΦK Φn In hΦn hIn hstep

theorem bounded_parameter_integral_schwartz_clm_exchange_of_exists_approximants {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (happrox :
      ∃ (Φn : ℕ → SchwartzMap (Fin m → ℝ) ℂ) (In : ℕ → ℂ),
        (∀ k n,
          Filter.Tendsto
            (fun N => SchwartzMap.seminorm ℝ k n
              (Φn N -
                Classical.choose
                  (bounded_parameter_integral_scalar_is_schwartz
                    K hK_meas hK_bdd g f hg_cont hg_bound)))
            Filter.atTop (nhds 0)) ∧
        Filter.Tendsto In Filter.atTop
          (nhds (∫ x in K, T (f x • g x))) ∧
        ∀ N, T (Φn N) = In N) :
    ∃ ΦK : SchwartzMap (Fin m → ℝ) ℂ,
      (∀ ξ, ΦK ξ = boundedParamIntegralScalar K g f ξ) ∧
      T ΦK = ∫ x in K, T (g x) * f x := by
  rcases happrox with ⟨Φn, In, hΦn, hIn, hstep⟩
  exact
    bounded_parameter_integral_schwartz_clm_exchange_of_choose_approximants
      K hK_meas hK_bdd T g f hg_cont hg_bound
      Φn In hΦn hIn hstep

theorem bounded_parameter_integral_schwartz_clm_exchange {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    ∃ ΦK : SchwartzMap (Fin m → ℝ) ℂ,
      (∀ ξ, ΦK ξ = boundedParamIntegralScalar K g f ξ) ∧
      T ΦK = ∫ x in K, T (g x) * f x := by
  exact
    bounded_parameter_integral_schwartz_clm_exchange_of_exists_approximants
      K hK_meas hK_bdd T g f hg_cont hg_bound
      (exists_bounded_kernel_approximants
        K hK_meas hK_bdd T g f hg_cont hg_bound)

lemma bounded_parameter_integral_schwartzSeminorm_le {m : ℕ}
    (K : Set (Fin m → ℝ))
    (hK_meas : MeasurableSet K)
    (hK_bdd : Bornology.IsBounded K)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (ΦK : SchwartzMap (Fin m → ℝ) ℂ)
    (hΦK : ∀ ξ, ΦK ξ = boundedParamIntegralScalar K g f ξ)
    (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n ΦK ≤
      ∫ x in K, SchwartzMap.seminorm ℝ k n (g x) * ‖f x‖ := by
  have hbound_nonneg :
      0 ≤ ∫ x in K, SchwartzMap.seminorm ℝ k n (g x) * ‖f x‖ :=
    MeasureTheory.integral_nonneg (μ := volume.restrict K) fun x =>
      mul_nonneg (apply_nonneg _ _) (norm_nonneg _)
  refine SchwartzMap.seminorm_le_bound ℝ k n ΦK hbound_nonneg ?_
  intro ξ
  have hΦK_fun :
      (fun ζ : Fin m → ℝ => ΦK ζ) = boundedParamIntegralScalar K g f :=
    funext hΦK
  have hiter :
      iteratedFDeriv ℝ n (fun ζ : Fin m → ℝ => ΦK ζ) ξ =
        boundedParamIntegralDeriv K g f n ξ := by
    calc
      iteratedFDeriv ℝ n (fun ζ : Fin m → ℝ => ΦK ζ) ξ
          =
        iteratedFDeriv ℝ n (boundedParamIntegralScalar K g f) ξ := by
          rw [hΦK_fun]
      _ = boundedParamIntegralDeriv K g f n ξ :=
          boundedParamIntegralScalar_iteratedFDeriv_eq
            K hK_meas hK_bdd g f hg_cont hg_bound n ξ
  rw [hiter]
  exact boundedParamIntegralScalar_decay_bound
    K hK_meas hK_bdd g f hg_cont hg_bound k n ξ

def fubiniCube (m R : ℕ) : Set (Fin m → ℝ) :=
  {x | ∀ i, ‖x i‖ ≤ (R : ℝ)}

lemma isClosed_fubiniCube (m R : ℕ) :
    IsClosed (fubiniCube m R) := by
  unfold fubiniCube
  simpa [Set.setOf_forall] using
    (isClosed_iInter fun i =>
      isClosed_le ((continuous_apply i : Continuous fun x : Fin m → ℝ => x i).norm)
        (continuous_const : Continuous fun _ : Fin m → ℝ => (R : ℝ)))

lemma measurableSet_fubiniCube (m R : ℕ) :
    MeasurableSet (fubiniCube m R) :=
  (isClosed_fubiniCube m R).measurableSet

lemma fubiniCube_mono (m : ℕ) {R S : ℕ} (hRS : R ≤ S) :
    fubiniCube m R ⊆ fubiniCube m S := by
  intro x hx i
  exact (hx i).trans (by exact_mod_cast hRS)

lemma fubiniCube_subset_closedBall (m R : ℕ) :
    fubiniCube m R ⊆ Metric.closedBall (0 : Fin m → ℝ) (R : ℝ) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (pi_norm_le_iff_of_nonneg (by exact_mod_cast Nat.zero_le R)).2 hx

lemma isBounded_fubiniCube (m R : ℕ) :
    Bornology.IsBounded (fubiniCube m R) :=
  (Metric.isBounded_iff_subset_closedBall (0 : Fin m → ℝ)).2
    ⟨R, fubiniCube_subset_closedBall m R⟩

lemma iUnion_fubiniCube_eq_univ (m : ℕ) :
    (⋃ R : ℕ, fubiniCube m R) = Set.univ := by
  ext x
  constructor
  · intro _; trivial
  · intro _
    obtain ⟨R, hR⟩ := exists_nat_ge ‖x‖
    refine Set.mem_iUnion.mpr ⟨R, ?_⟩
    intro i
    exact (norm_le_pi_norm x i).trans hR

lemma integrableOn_iUnion_fubiniCube_of_integrable {m : ℕ}
    {F : (Fin m → ℝ) → ℂ} (hF : Integrable F) :
    IntegrableOn F (⋃ R : ℕ, fubiniCube m R) volume := by
  simpa [iUnion_fubiniCube_eq_univ m] using hF

lemma integrableOn_iUnion_fubiniCube_of_integrable_real {m : ℕ}
    {F : (Fin m → ℝ) → ℝ} (hF : Integrable F) :
    IntegrableOn F (⋃ R : ℕ, fubiniCube m R) volume := by
  simpa [iUnion_fubiniCube_eq_univ m] using hF

lemma tendsto_integral_fubiniCube_of_integrable {m : ℕ}
    {F : (Fin m → ℝ) → ℂ} (hF : Integrable F) :
    Filter.Tendsto
      (fun R : ℕ => ∫ x in fubiniCube m R, F x)
      Filter.atTop
      (nhds (∫ x, F x)) := by
  have hmono : Monotone (fun R : ℕ => fubiniCube m R) := by
    intro R S hRS
    exact fubiniCube_mono m hRS
  have hconv :=
    MeasureTheory.tendsto_setIntegral_of_monotone
      (f := F)
      (μ := volume)
      (s := fun R : ℕ => fubiniCube m R)
      (hsm := fun R => measurableSet_fubiniCube m R)
      hmono
      (integrableOn_iUnion_fubiniCube_of_integrable (m := m) hF)
  have hlim :
      (∫ x in ⋃ R : ℕ, fubiniCube m R, F x) = ∫ x, F x := by
    rw [iUnion_fubiniCube_eq_univ m]
    rw [MeasureTheory.setIntegral_univ]
  simpa [hlim] using hconv

lemma tendsto_integral_fubiniCube_of_integrable_real {m : ℕ}
    {F : (Fin m → ℝ) → ℝ} (hF : Integrable F) :
    Filter.Tendsto
      (fun R : ℕ => ∫ x in fubiniCube m R, F x)
      Filter.atTop
      (nhds (∫ x, F x)) := by
  have hmono : Monotone (fun R : ℕ => fubiniCube m R) := by
    intro R S hRS
    exact fubiniCube_mono m hRS
  have hconv :=
    MeasureTheory.tendsto_setIntegral_of_monotone
      (f := F)
      (μ := volume)
      (s := fun R : ℕ => fubiniCube m R)
      (hsm := fun R => measurableSet_fubiniCube m R)
      hmono
      (integrableOn_iUnion_fubiniCube_of_integrable_real (m := m) hF)
  have hlim :
      (∫ x in ⋃ R : ℕ, fubiniCube m R, F x) = ∫ x, F x := by
    rw [iUnion_fubiniCube_eq_univ m]
    rw [MeasureTheory.setIntegral_univ]
  simpa [hlim] using hconv

def fubiniAnnulus (m R S : ℕ) : Set (Fin m → ℝ) :=
  fubiniCube m S \ fubiniCube m R

lemma measurableSet_fubiniAnnulus (m R S : ℕ) :
    MeasurableSet (fubiniAnnulus m R S) :=
  (measurableSet_fubiniCube m S).diff (measurableSet_fubiniCube m R)

lemma isBounded_fubiniAnnulus (m R S : ℕ) :
    Bornology.IsBounded (fubiniAnnulus m R S) :=
  (isBounded_fubiniCube m S).subset (by intro x hx; exact hx.1)

noncomputable def fubiniTruncation {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (R : ℕ) : SchwartzMap (Fin m → ℝ) ℂ :=
  Classical.choose
    (bounded_parameter_integral_schwartz_clm_exchange
      (fubiniCube m R) (measurableSet_fubiniCube m R) (isBounded_fubiniCube m R)
      T g f hg_cont hg_bound)

lemma fubiniTruncation_apply {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (R : ℕ) (ξ : Fin m → ℝ) :
    fubiniTruncation T g f hg_cont hg_bound R ξ =
      ∫ x in fubiniCube m R, g x ξ * f x := by
  have hspec :=
    Classical.choose_spec
      (bounded_parameter_integral_schwartz_clm_exchange
        (fubiniCube m R) (measurableSet_fubiniCube m R) (isBounded_fubiniCube m R)
        T g f hg_cont hg_bound)
  simpa [fubiniTruncation, boundedParamIntegralScalar] using hspec.1 ξ

lemma fubiniTruncation_clm {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (R : ℕ) :
    T (fubiniTruncation T g f hg_cont hg_bound R) =
      ∫ x in fubiniCube m R, T (g x) * f x := by
  have hspec :=
    Classical.choose_spec
      (bounded_parameter_integral_schwartz_clm_exchange
        (fubiniCube m R) (measurableSet_fubiniCube m R) (isBounded_fubiniCube m R)
        T g f hg_cont hg_bound)
  simpa [fubiniTruncation] using hspec.2

noncomputable def fubiniAnnulusIntegral {m : ℕ}
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (R S : ℕ) : SchwartzMap (Fin m → ℝ) ℂ :=
  Classical.choose
    (bounded_parameter_integral_scalar_is_schwartz
      (fubiniAnnulus m R S) (measurableSet_fubiniAnnulus m R S)
      (isBounded_fubiniAnnulus m R S) g f hg_cont hg_bound)

lemma fubiniAnnulusIntegral_apply {m : ℕ}
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    (R S : ℕ) (ξ : Fin m → ℝ) :
    fubiniAnnulusIntegral g f hg_cont hg_bound R S ξ =
      ∫ x in fubiniAnnulus m R S, g x ξ * f x := by
  have hspec :=
    Classical.choose_spec
      (bounded_parameter_integral_scalar_is_schwartz
        (fubiniAnnulus m R S) (measurableSet_fubiniAnnulus m R S)
        (isBounded_fubiniAnnulus m R S) g f hg_cont hg_bound)
  simpa [fubiniAnnulusIntegral, boundedParamIntegralScalar] using hspec ξ

lemma fubiniTruncation_sub_eq_annulus {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    {R S : ℕ} (hRS : R ≤ S) :
    fubiniTruncation T g f hg_cont hg_bound S -
      fubiniTruncation T g f hg_cont hg_bound R =
    fubiniAnnulusIntegral g f hg_cont hg_bound R S := by
  ext ξ
  let F : (Fin m → ℝ) → ℂ := fun x => g x ξ * f x
  have hF_int :
      IntegrableOn F (fubiniCube m S) volume :=
    integrableOn_schwartz_fubini_pointwise
      (fubiniCube m S) g f hg_cont hg_bound ξ
  have hdiff :
      ∫ x in fubiniAnnulus m R S, F x ∂volume =
        (∫ x in fubiniCube m S, F x ∂volume) -
          (∫ x in fubiniCube m R, F x ∂volume) := by
    simpa [fubiniAnnulus] using
      (MeasureTheory.setIntegral_diff
        (μ := volume)
        (f := F)
        (measurableSet_fubiniCube m R) hF_int (fubiniCube_mono m hRS))
  calc
    (fubiniTruncation T g f hg_cont hg_bound S -
        fubiniTruncation T g f hg_cont hg_bound R) ξ
        =
      (∫ x in fubiniCube m S, F x) -
        (∫ x in fubiniCube m R, F x) := by
        simp [SchwartzMap.sub_apply, F,
          fubiniTruncation_apply T g f hg_cont hg_bound]
    _ = ∫ x in fubiniAnnulus m R S, F x := by
        simpa using hdiff.symm
    _ = fubiniAnnulusIntegral g f hg_cont hg_bound R S ξ := by
        rw [fubiniAnnulusIntegral_apply]

lemma fubiniTruncation_sub_seminorm_le_annulus {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    {R S : ℕ} (hRS : R ≤ S) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n
        (fubiniTruncation T g f hg_cont hg_bound S -
          fubiniTruncation T g f hg_cont hg_bound R)
      ≤ ∫ x in fubiniAnnulus m R S,
          SchwartzMap.seminorm ℝ k n (g x) * ‖f x‖ := by
  rw [fubiniTruncation_sub_eq_annulus T g f hg_cont hg_bound hRS]
  exact
    bounded_parameter_integral_schwartzSeminorm_le
      (fubiniAnnulus m R S) (measurableSet_fubiniAnnulus m R S)
      (isBounded_fubiniAnnulus m R S) g f hg_cont hg_bound
      (fubiniAnnulusIntegral g f hg_cont hg_bound R S)
      (fubiniAnnulusIntegral_apply g f hg_cont hg_bound R S) k n

lemma fubiniTruncation_sub_seminorm_le_compl {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N)
    {R S : ℕ} (hRS : R ≤ S) (k n : ℕ) :
    SchwartzMap.seminorm ℝ k n
        (fubiniTruncation T g f hg_cont hg_bound S -
          fubiniTruncation T g f hg_cont hg_bound R)
      ≤ ∫ x in (fubiniCube m R)ᶜ,
          SchwartzMap.seminorm ℝ k n (g x) * ‖f x‖ := by
  let W : (Fin m → ℝ) → ℝ :=
    fun x => SchwartzMap.seminorm ℝ k n (g x) * ‖f x‖
  have hW_int : Integrable W :=
    integrable_schwartz_fubini_seminorm_weight g f hg_cont hg_bound k n
  have hann_subset : fubiniAnnulus m R S ⊆ (fubiniCube m R)ᶜ := by
    intro x hx
    exact hx.2
  have hmono :
      ∫ x in fubiniAnnulus m R S, W x ≤
        ∫ x in (fubiniCube m R)ᶜ, W x :=
    MeasureTheory.setIntegral_mono_set
      (hW_int.integrableOn)
      (Filter.Eventually.of_forall fun x =>
        mul_nonneg (apply_nonneg _ _) (norm_nonneg _))
      (Filter.Eventually.of_forall fun x hx => hann_subset hx)
  exact (fubiniTruncation_sub_seminorm_le_annulus
    T g f hg_cont hg_bound hRS k n).trans hmono

lemma tendsto_integral_compl_fubiniCube_of_integrable {m : ℕ}
    {F : (Fin m → ℝ) → ℝ} (hF : Integrable F) :
    Filter.Tendsto
      (fun R : ℕ => ∫ x in (fubiniCube m R)ᶜ, F x)
      Filter.atTop
      (nhds 0) := by
  have hcube :
      Filter.Tendsto
        (fun R : ℕ => ∫ x in fubiniCube m R, F x)
        Filter.atTop
        (nhds (∫ x, F x)) :=
    tendsto_integral_fubiniCube_of_integrable_real (m := m) hF
  have hrepr :
      (fun R : ℕ => ∫ x in (fubiniCube m R)ᶜ, F x) =
        fun R : ℕ => (∫ x, F x) - (∫ x in fubiniCube m R, F x) := by
    funext R
    have hdiff :
        ∫ x in Set.univ \ fubiniCube m R, F x ∂volume =
          (∫ x in (Set.univ : Set (Fin m → ℝ)), F x ∂volume) -
            (∫ x in fubiniCube m R, F x ∂volume) :=
      MeasureTheory.setIntegral_diff
        (μ := volume)
        (f := F)
        (measurableSet_fubiniCube m R) hF.integrableOn (Set.subset_univ _)
    simpa [Set.compl_eq_univ_diff, MeasureTheory.setIntegral_univ] using hdiff
  rw [hrepr]
  have hlim :=
    (tendsto_const_nhds (x := ∫ x, F x)).sub hcube
  simpa using hlim

lemma cauchySeq_schwartz_of_seminorm {m : ℕ}
    {u : ℕ → SchwartzMap (Fin m → ℝ) ℂ}
    (h : ∀ k n ε, 0 < ε →
      ∃ N, ∀ R ≥ N, ∀ S ≥ N,
        SchwartzMap.seminorm ℝ k n (u R - u S) < ε) :
    CauchySeq u := by
  rw [cauchySeq_iff_tendsto, uniformity_eq_comap_nhds_zero, Filter.tendsto_comap_iff]
  set_option backward.isDefEq.respectTransparency false in
  rw [(schwartz_withSeminorms ℝ (Fin m → ℝ) ℂ).tendsto_nhds _ 0]
  intro i ε hε
  obtain ⟨k, n⟩ := i
  obtain ⟨N, hN⟩ := h k n ε hε
  rw [Filter.eventually_atTop_prod_self]
  refine ⟨N, fun R S hR hS => ?_⟩
  simpa [SchwartzMap.schwartzSeminormFamily_apply, sub_zero] using hN S hS R hR

lemma cauchySeq_fubiniTruncation {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ x, SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    CauchySeq (fubiniTruncation T g f hg_cont hg_bound) := by
  refine cauchySeq_schwartz_of_seminorm ?_
  intro k n ε hε
  let W : (Fin m → ℝ) → ℝ :=
    fun x => SchwartzMap.seminorm ℝ k n (g x) * ‖f x‖
  have hW_int : Integrable W :=
    integrable_schwartz_fubini_seminorm_weight g f hg_cont hg_bound k n
  have htail :=
    tendsto_integral_compl_fubiniCube_of_integrable (m := m) hW_int
  have hev := (Metric.tendsto_nhds.mp htail) ε hε
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨N, fun R hR S hS => ?_⟩
  have htail_lt : ∀ Q ≥ N, (∫ x in (fubiniCube m Q)ᶜ, W x) < ε := by
    intro Q hQ
    have hdist := hN Q hQ
    have hnonneg :
        0 ≤ ∫ x in (fubiniCube m Q)ᶜ, W x :=
      MeasureTheory.integral_nonneg (μ := volume.restrict (fubiniCube m Q)ᶜ) fun x =>
        mul_nonneg (apply_nonneg _ _) (norm_nonneg _)
    simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hdist
  by_cases hRS : R ≤ S
  · have hle :=
      fubiniTruncation_sub_seminorm_le_compl
        T g f hg_cont hg_bound hRS k n
    have hle' :
        SchwartzMap.seminorm ℝ k n
            (fubiniTruncation T g f hg_cont hg_bound R -
              fubiniTruncation T g f hg_cont hg_bound S)
          ≤ ∫ x in (fubiniCube m R)ᶜ, W x := by
      have hneg :
          fubiniTruncation T g f hg_cont hg_bound R -
              fubiniTruncation T g f hg_cont hg_bound S =
            - (fubiniTruncation T g f hg_cont hg_bound S -
              fubiniTruncation T g f hg_cont hg_bound R) := by
        abel
      rw [hneg, map_neg_eq_map]
      exact hle
    exact lt_of_le_of_lt hle' (htail_lt R hR)
  · have hSR : S ≤ R := le_of_not_ge hRS
    have hle :=
      fubiniTruncation_sub_seminorm_le_compl
        T g f hg_cont hg_bound hSR k n
    exact lt_of_le_of_lt hle (htail_lt S hS)

theorem schwartz_clm_fubini_exchange_aux {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ (x : Fin m → ℝ),
        SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    ∃ (Φ : SchwartzMap (Fin m → ℝ) ℂ),
      (∀ ξ : Fin m → ℝ, Φ ξ = ∫ x : Fin m → ℝ, g x ξ * f x) ∧
      (T Φ = ∫ x : Fin m → ℝ, T (g x) * f x) := by
  let ΦR : ℕ → SchwartzMap (Fin m → ℝ) ℂ :=
    fubiniTruncation T g f hg_cont hg_bound
  have hΦR_cauchy : CauchySeq ΦR := by
    simpa [ΦR] using cauchySeq_fubiniTruncation T g f hg_cont hg_bound
  obtain ⟨Φ, hΦ_lim⟩ := cauchySeq_tendsto_of_complete hΦR_cauchy
  refine ⟨Φ, ?_, ?_⟩
  · intro ξ
    have hev :
        Continuous fun ψ : SchwartzMap (Fin m → ℝ) ℂ => ψ ξ := by
      simpa using
        (((BoundedContinuousFunction.evalCLM ℂ ξ).comp
          (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin m → ℝ) ℂ)).continuous)
    have hleft :
        Filter.Tendsto (fun R : ℕ => ΦR R ξ) Filter.atTop (nhds (Φ ξ)) :=
      hev.continuousAt.tendsto.comp hΦ_lim
    have hleft_integral :
        Filter.Tendsto
          (fun R : ℕ => ∫ x in fubiniCube m R, g x ξ * f x)
          Filter.atTop (nhds (Φ ξ)) :=
      hleft.congr' <|
        Filter.Eventually.of_forall fun R => by
          simpa [ΦR] using
            fubiniTruncation_apply T g f hg_cont hg_bound R ξ
    have hright :
        Filter.Tendsto
          (fun R : ℕ => ∫ x in fubiniCube m R, g x ξ * f x)
          Filter.atTop
          (nhds (∫ x : Fin m → ℝ, g x ξ * f x)) :=
      tendsto_integral_fubiniCube_of_integrable
        (m := m) (integrable_schwartz_fubini_pointwise g f hg_cont hg_bound ξ)
    exact tendsto_nhds_unique hleft_integral hright
  · have hleft :
        Filter.Tendsto
          (fun R : ℕ => T (ΦR R))
          Filter.atTop
          (nhds (T Φ)) :=
      T.continuous.continuousAt.tendsto.comp hΦ_lim
    have hleft_integral :
        Filter.Tendsto
          (fun R : ℕ => ∫ x in fubiniCube m R, T (g x) * f x)
          Filter.atTop
          (nhds (T Φ)) :=
      hleft.congr' <|
        Filter.Eventually.of_forall fun R => by
          simpa [ΦR] using
            fubiniTruncation_clm T g f hg_cont hg_bound R
    have hright :
        Filter.Tendsto
          (fun R : ℕ => ∫ x in fubiniCube m R, T (g x) * f x)
          Filter.atTop
          (nhds (∫ x : Fin m → ℝ, T (g x) * f x)) :=
      tendsto_integral_fubiniCube_of_integrable
        (m := m) (integrable_schwartz_fubini_clm_pairing T g f hg_cont hg_bound)
    exact tendsto_nhds_unique hleft_integral hright

theorem schwartz_clm_fubini_exchange {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hg_cont : Continuous g)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ (x : Fin m → ℝ),
        SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    ∃ (Φ : SchwartzMap (Fin m → ℝ) ℂ),
      (∀ ξ : Fin m → ℝ, Φ ξ = ∫ x : Fin m → ℝ, g x ξ * f x) ∧
      (T Φ = ∫ x : Fin m → ℝ, T (g x) * f x) :=
  schwartz_clm_fubini_exchange_aux T g f hg_cont hg_bound

private def clmOfContinuousIsLinear
    {V : Type*} [AddCommMonoid V] [Module ℂ V] [TopologicalSpace V]
    (w : V → ℂ) (hw_cont : Continuous w) (hw_lin : IsLinearMap ℂ w) :
    V →L[ℂ] ℂ where
  toLinearMap :=
    { toFun := w
      map_add' := fun x y => hw_lin.map_add x y
      map_smul' := fun c x => hw_lin.map_smul c x }
  cont := hw_cont

private noncomputable def finiteDimCoordCLE
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

private abbrev castFinCLE {a b : ℕ} (h : a = b) :
    (Fin a → ℝ) ≃L[ℝ] (Fin b → ℝ) :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin b => ℝ) (finCongr h)

@[simp] private lemma castFinCLE_apply {a b : ℕ} (h : a = b)
    (x : Fin a → ℝ) (i : Fin b) :
    castFinCLE h x i = x ((finCongr h).symm i) := rfl

@[simp] private lemma castFinCLE_symm_apply {a b : ℕ} (h : a = b)
    (x : Fin b → ℝ) (i : Fin a) :
    (castFinCLE h).symm x i = x ((finCongr h) i) := rfl

private noncomputable def toCoordSchwartz
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    SchwartzMap E ℂ →L[ℂ] SchwartzMap (Fin (Module.finrank ℝ E) → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (finiteDimCoordCLE E).symm

private noncomputable def fromCoordSchwartz
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    SchwartzMap (Fin (Module.finrank ℝ E) → ℝ) ℂ →L[ℂ] SchwartzMap E ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (finiteDimCoordCLE E)

@[simp] private lemma toCoordSchwartz_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : SchwartzMap E ℂ) (x : Fin (Module.finrank ℝ E) → ℝ) :
    toCoordSchwartz E f x = f ((finiteDimCoordCLE E).symm x) := rfl

@[simp] private lemma fromCoordSchwartz_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : SchwartzMap (Fin (Module.finrank ℝ E) → ℝ) ℂ) (x : E) :
    fromCoordSchwartz E f x = f ((finiteDimCoordCLE E) x) := rfl

private lemma seminorm_clm_family_poly_bound
    {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (L : SchwartzMap A ℂ →L[ℂ] SchwartzMap B ℂ)
    (F : ℝ → SchwartzMap A ℂ)
    (hF_poly : ∀ (k j : ℕ), ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ t : ℝ,
        SchwartzMap.seminorm ℝ k j (F t) ≤ C * (1 + ‖t‖) ^ N) :
    ∀ (k j : ℕ), ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ t : ℝ,
        SchwartzMap.seminorm ℝ k j (L (F t)) ≤ C * (1 + ‖t‖) ^ N := by
  intro k j
  let Lreal : SchwartzMap A ℂ →ₗ[ℝ] SchwartzMap B ℂ :=
    { toFun := fun f => L f
      map_add' := fun f g => L.map_add f g
      map_smul' := by
        intro r f
        change L ((r : ℂ) • f) = (r : ℂ) • L f
        exact L.map_smul (r : ℂ) f }
  let qkj : Seminorm ℝ (SchwartzMap A ℂ) :=
    (schwartzSeminormFamily ℝ B ℂ (k, j)).comp Lreal
  have hqkj_cont : Continuous ⇑qkj :=
    ((schwartz_withSeminorms ℝ B ℂ).continuous_seminorm (k, j)).comp L.continuous
  obtain ⟨s, C₀, _, hbound⟩ :=
    Seminorm.bound_of_continuous
      (schwartz_withSeminorms ℝ A ℂ) qkj hqkj_cont
  let Ds : ℕ × ℕ → ℝ := fun i => (hF_poly i.1 i.2).choose
  let Ns : ℕ × ℕ → ℕ := fun i => (hF_poly i.1 i.2).choose_spec.choose
  have hDs_pos : ∀ i, 0 < Ds i :=
    fun i => (hF_poly i.1 i.2).choose_spec.choose_spec.1
  have hDs_nonneg : ∀ i, 0 ≤ Ds i := fun i => (hDs_pos i).le
  have hDs_bound : ∀ (i : ℕ × ℕ) t,
      SchwartzMap.seminorm ℝ i.1 i.2 (F t) ≤
        Ds i * (1 + ‖t‖) ^ Ns i := by
    intro i t
    exact (hF_poly i.1 i.2).choose_spec.choose_spec.2 t
  let Nmax : ℕ := s.sup Ns
  let Cbase : ℝ := (C₀ : ℝ) * ∑ i ∈ s, Ds i
  have hCbase_nonneg : 0 ≤ Cbase :=
    mul_nonneg C₀.prop (Finset.sum_nonneg (fun i _ => hDs_nonneg i))
  refine ⟨Cbase + 1, Nmax, by linarith, fun t => ?_⟩
  have hq_eq :
      qkj (F t) = SchwartzMap.seminorm ℝ k j (L (F t)) := rfl
  rw [← hq_eq]
  have h1 : qkj (F t) ≤
      (C₀ : ℝ) *
        (s.sup (schwartzSeminormFamily ℝ A ℂ)) (F t) := by
    have h := hbound (F t)
    simp only [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul] at h
    linarith
  have h2 : (s.sup (schwartzSeminormFamily ℝ A ℂ)) (F t) ≤
      ∑ i ∈ s, Ds i * (1 + ‖t‖) ^ Ns i := by
    apply Seminorm.finset_sup_apply_le
      (Finset.sum_nonneg (fun i _ =>
        mul_nonneg (hDs_nonneg i) (pow_nonneg (by linarith [norm_nonneg t]) _)))
    intro ⟨p, q⟩ hi
    simp only [SchwartzMap.schwartzSeminormFamily_apply]
    exact (hDs_bound (p, q) t).trans
      (Finset.single_le_sum
        (fun i _ => mul_nonneg (hDs_nonneg i)
          (pow_nonneg (by linarith [norm_nonneg t]) _)) hi)
  have h3 : ∑ i ∈ s, Ds i * (1 + ‖t‖) ^ Ns i ≤
      (∑ i ∈ s, Ds i) * (1 + ‖t‖) ^ Nmax := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (hDs_nonneg i)
    exact pow_le_pow_right₀ (by linarith [norm_nonneg t])
      (Finset.le_sup (f := Ns) hi)
  calc
    qkj (F t)
        ≤ (C₀ : ℝ) * (s.sup (schwartzSeminormFamily ℝ A ℂ)) (F t) := h1
    _ ≤ (C₀ : ℝ) * ∑ i ∈ s, Ds i * (1 + ‖t‖) ^ Ns i :=
        mul_le_mul_of_nonneg_left h2 C₀.prop
    _ ≤ (C₀ : ℝ) * ((∑ i ∈ s, Ds i) * (1 + ‖t‖) ^ Nmax) :=
        mul_le_mul_of_nonneg_left h3 C₀.prop
    _ = Cbase * (1 + ‖t‖) ^ Nmax := by ring
    _ ≤ (Cbase + 1) * (1 + ‖t‖) ^ Nmax := by
        exact mul_le_mul_of_nonneg_right (by linarith)
          (pow_nonneg (by linarith [norm_nonneg t]) _)

private noncomputable def normedUnitBumpSchwartzReal : SchwartzMap ℝ ℂ := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let f : ℝ → ℂ := fun x => ((b.normed MeasureTheory.volume x : ℝ) : ℂ)
  have hf_smooth : ContDiff ℝ (⊤ : ENat) f := by
    exact (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff_normed
  have hf_compact : HasCompactSupport f :=
    b.hasCompactSupport_normed.comp_left Complex.ofReal_zero
  exact hf_compact.toSchwartzMap hf_smooth

private lemma integral_normedUnitBumpSchwartzReal :
    ∫ x : ℝ, normedUnitBumpSchwartzReal x = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  have happly :
      (fun x : ℝ => normedUnitBumpSchwartzReal x) =
        fun x : ℝ => ((b.normed MeasureTheory.volume x : ℝ) : ℂ) := by
    funext x
    have hf_smooth : ContDiff ℝ (⊤ : ENat)
        (fun y : ℝ => ((b.normed MeasureTheory.volume y : ℝ) : ℂ)) := by
      exact (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff_normed
    have hf_compact :
        HasCompactSupport (fun y : ℝ => ((b.normed MeasureTheory.volume y : ℝ) : ℂ)) :=
      b.hasCompactSupport_normed.comp_left Complex.ofReal_zero
    simpa [normedUnitBumpSchwartzReal, b] using
      (HasCompactSupport.toSchwartzMap_toFun hf_compact hf_smooth x)
  rw [happly, integral_complex_ofReal]
  exact congrArg (fun r : ℝ => (r : ℂ)) (b.integral_normed (μ := MeasureTheory.volume))

private theorem integral_finSucc_cons_eq_complex
    {m : ℕ} (f : (Fin (m + 1) → ℝ) → ℂ) :
    (∫ z : ℝ × (Fin m → ℝ), f (Fin.cons z.1 z.2)
        ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          (MeasureTheory.Measure.pi fun _ : Fin m =>
            (MeasureTheory.volume : MeasureTheory.Measure ℝ)))) =
      (∫ x : Fin (m + 1) → ℝ, f x
        ∂(MeasureTheory.Measure.pi fun _ : Fin (m + 1) =>
          (MeasureTheory.volume : MeasureTheory.Measure ℝ))) := by
  have h :=
    ((MeasureTheory.measurePreserving_piFinSuccAbove
        (fun _ => (MeasureTheory.volume : MeasureTheory.Measure ℝ)) 0).symm).integral_comp'
      (g := f)
  simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, cast_eq, Fin.cons_zero] using h

private noncomputable def normedUnitBumpSchwartzFin : ∀ n : ℕ,
    SchwartzMap (Fin n → ℝ) ℂ
  | 0 => by
      let f : (Fin 0 → ℝ) → ℂ := fun _ => 1
      have hf_smooth : ContDiff ℝ (⊤ : ENat) f := by
        simpa [f] using
          (contDiff_const : ContDiff ℝ (⊤ : ENat) (fun _ : Fin 0 → ℝ => (1 : ℂ)))
      have hf_compact : HasCompactSupport f := by
        simpa [HasCompactSupport, tsupport, Function.support, f] using
          (show IsCompact (Set.univ : Set (Fin 0 → ℝ)) from isCompact_univ)
      exact hf_compact.toSchwartzMap hf_smooth
  | n + 1 => SCV.prependField normedUnitBumpSchwartzReal (normedUnitBumpSchwartzFin n)

private lemma integral_normedUnitBumpSchwartzFin :
    ∀ n : ℕ, ∫ x : Fin n → ℝ, normedUnitBumpSchwartzFin n x = 1
  | 0 => by
      have happly :
          (fun x : Fin 0 → ℝ => normedUnitBumpSchwartzFin 0 x) =
            fun _ : Fin 0 → ℝ => (1 : ℂ) := by
        funext x
        simp [normedUnitBumpSchwartzFin]
      rw [happly]
      have hvol :
          (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ)) =
            MeasureTheory.Measure.dirac default := by
        simpa using
          (MeasureTheory.Measure.volume_pi_eq_dirac
            (ι := Fin 0) (α := fun _ => ℝ) (x := default))
      simpa [hvol] using
        (MeasureTheory.integral_dirac (a := default) (f := fun _ : Fin 0 → ℝ => (1 : ℂ)))
  | n + 1 => by
      calc
        ∫ x : Fin (n + 1) → ℝ, normedUnitBumpSchwartzFin (n + 1) x
            =
          ∫ z : ℝ × (Fin n → ℝ), normedUnitBumpSchwartzFin (n + 1) (Fin.cons z.1 z.2) := by
              simpa using
                (integral_finSucc_cons_eq_complex
                  (f := fun x : Fin (n + 1) → ℝ => normedUnitBumpSchwartzFin (n + 1) x)).symm
        _ = ∫ z : ℝ × (Fin n → ℝ),
              normedUnitBumpSchwartzReal z.1 * normedUnitBumpSchwartzFin n z.2 := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with z
              simp [normedUnitBumpSchwartzFin, SCV.prependField_apply]
        _ = (∫ x : ℝ, normedUnitBumpSchwartzReal x) *
              (∫ y : Fin n → ℝ, normedUnitBumpSchwartzFin n y) := by
              simpa using
                (MeasureTheory.integral_prod_mul
                  (f := fun x : ℝ => normedUnitBumpSchwartzReal x)
                  (g := fun y : Fin n → ℝ => normedUnitBumpSchwartzFin n y))
        _ = 1 := by
              rw [integral_normedUnitBumpSchwartzReal, integral_normedUnitBumpSchwartzFin n]
              ring

private lemma padded_integral_collapse_point
    {n : ℕ}
    (H : ℝ → ℂ)
    (φ : SchwartzMap ℝ ℂ)
    (ρ : SchwartzMap (Fin n → ℝ) ℂ)
    (hρ : ∫ u : Fin n → ℝ, ρ u = 1) :
    (∫ x : Fin (n + 1) → ℝ,
        H (x 0) * ((φ : ℝ → ℂ) (x 0) * ρ (fun i : Fin n => x i.succ))) =
      ∫ t : ℝ, H t * (φ : ℝ → ℂ) t := by
  calc
    ∫ x : Fin (n + 1) → ℝ,
        H (x 0) * ((φ : ℝ → ℂ) (x 0) * ρ (fun i : Fin n => x i.succ))
        =
      ∫ z : ℝ × (Fin n → ℝ),
        H z.1 * ((φ : ℝ → ℂ) z.1 * ρ z.2) := by
        simpa using
          (integral_finSucc_cons_eq_complex
            (m := n)
            (f := fun x : Fin (n + 1) → ℝ =>
              H (x 0) * ((φ : ℝ → ℂ) (x 0) * ρ (fun i : Fin n => x i.succ)))).symm
    _ = ∫ z : ℝ × (Fin n → ℝ),
        (H z.1 * (φ : ℝ → ℂ) z.1) * ρ z.2 := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with z
        ring
    _ = (∫ t : ℝ, H t * (φ : ℝ → ℂ) t) *
        (∫ u : Fin n → ℝ, ρ u) := by
        simpa using
          (MeasureTheory.integral_prod_mul
            (μ := MeasureTheory.volume)
            (ν := MeasureTheory.volume)
            (f := fun t : ℝ => H t * (φ : ℝ → ℂ) t)
            (g := fun u : Fin n → ℝ => ρ u))
    _ = ∫ t : ℝ, H t * (φ : ℝ → ℂ) t := by
        rw [hρ, mul_one]

/-- **Finite-dimensional real-parameter CLM exchange.**

This is the finite-dimensional mixed-domain form needed by the GNS
spectral-condition argument.  The parameter space is one-dimensional (`ℝ`),
while the Schwartz functions live on a finite-dimensional real normed space
`E`; in the current downstream uses, `E` is an `NPointSpacetime` finite product
of real coordinates.

Given a continuous ℂ-linear functional `w` on `SchwartzMap E ℂ`, a continuous
Schwartz-valued family `G : ℝ → SchwartzMap E ℂ` with polynomial seminorm
growth in the real parameter, and a one-variable Schwartz test function `φ`,
the pointwise integral

`Θ ξ = ∫ t, φ t * G t ξ`

defines a Schwartz function on `E`, and `w` commutes with this integral.

This theorem is intentionally narrower than the previous arbitrary-domain
surface: finite dimensionality and positive real dimension are the exact setting
required by the current GNS uses, and this is the setting in which the result
reduces to the existing same-domain axiom `schwartz_clm_fubini_exchange`.

Lean-facing reduction plan from `schwartz_clm_fubini_exchange`:

1. Choose a continuous linear equivalence `E ≃L[ℝ] (Fin N → ℝ)` and transport
   `w` and `G t` to Schwartz functions on `Fin N → ℝ`.
2. Split `Fin N → ℝ` as `ℝ × (Fin (N - 1) → ℝ)`.
3. Choose a fixed Schwartz bump `ρ` on the tail coordinates with
   `∫ u, ρ u = 1`.
4. Apply `schwartz_clm_fubini_exchange` in dimension `N` to the padded data
   `x ↦ G (x₀)` and `x ↦ φ x₀ * ρ x_tail`.
5. Use finite-product Fubini and the normalization of `ρ` to collapse the
   `Fin N → ℝ` integral back to the real-parameter integral above.
6. Transport the resulting Schwartz function back along the chosen coordinate
   equivalence.

The remaining formal work is this coordinate-transport/padding/Fubini package;
the mathematical content is the same Schwartz-valued integral exchange as the
existing axiom, but with different finite-dimensional parameter and target
domains. -/
theorem schwartz_clm_fubini_exchange_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (w : SchwartzMap E ℂ → ℂ) (hw_cont : Continuous w) (hw_lin : IsLinearMap ℂ w)
    (G : ℝ → SchwartzMap E ℂ) (hG_cont : Continuous G)
    (hG_poly : ∀ (k j : ℕ), ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ t : ℝ,
        SchwartzMap.seminorm ℝ k j (G t) ≤ C * (1 + ‖t‖) ^ N)
    (hEpos : 0 < Module.finrank ℝ E)
    (φ : SchwartzMap ℝ ℂ) :
    ∃ Θ : SchwartzMap E ℂ,
      (∀ ξ : E, Θ ξ = ∫ t : ℝ, (φ : ℝ → ℂ) t * G t ξ) ∧
      w Θ = ∫ t : ℝ, w (G t) * (φ : ℝ → ℂ) t := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hEpos)
  have hn' : Module.finrank ℝ E = n + 1 := by
    simpa using hn
  let Lto : SchwartzMap E ℂ →L[ℂ] SchwartzMap (Fin (n + 1) → ℝ) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (castFinCLE hn').symm).comp
      (toCoordSchwartz E)
  let Lfrom : SchwartzMap (Fin (n + 1) → ℝ) ℂ →L[ℂ] SchwartzMap E ℂ :=
    (fromCoordSchwartz E).comp
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (castFinCLE hn'))
  let wCLM : SchwartzMap E ℂ →L[ℂ] ℂ :=
    clmOfContinuousIsLinear w hw_cont hw_lin
  let T : SchwartzMap (Fin (n + 1) → ℝ) ℂ →L[ℂ] ℂ := wCLM.comp Lfrom
  let ρ : SchwartzMap (Fin n → ℝ) ℂ := normedUnitBumpSchwartzFin n
  let fpad : SchwartzMap (Fin (n + 1) → ℝ) ℂ := SCV.prependField φ ρ
  let Gcoord : ℝ → SchwartzMap (Fin (n + 1) → ℝ) ℂ := fun t => Lto (G t)
  let g : (Fin (n + 1) → ℝ) → SchwartzMap (Fin (n + 1) → ℝ) ℂ :=
    fun x => Gcoord (x 0)
  have hGcoord_cont : Continuous Gcoord := Lto.continuous.comp hG_cont
  have hg_cont : Continuous g := hGcoord_cont.comp (continuous_apply 0)
  have hGcoord_poly :
      ∀ (k j : ℕ), ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ t : ℝ,
        SchwartzMap.seminorm ℝ k j (Gcoord t) ≤ C * (1 + ‖t‖) ^ N := by
    simpa [Gcoord] using seminorm_clm_family_poly_bound Lto G hG_poly
  have hg_bound :
      ∀ (k j : ℕ), ∃ (C : ℝ) (N : ℕ), 0 < C ∧
        ∀ x : Fin (n + 1) → ℝ,
          SchwartzMap.seminorm ℝ k j (g x) ≤ C * (1 + ‖x‖) ^ N := by
    intro k j
    obtain ⟨C, N, hC, hCbound⟩ := hGcoord_poly k j
    refine ⟨C, N, hC, fun x => ?_⟩
    have hx : ‖x 0‖ ≤ ‖x‖ := norm_le_pi_norm x 0
    have hpow : (1 + ‖x 0‖) ^ N ≤ (1 + ‖x‖) ^ N :=
      pow_le_pow_left₀ (by linarith [norm_nonneg (x 0)])
        (by linarith) N
    exact (hCbound (x 0)).trans (mul_le_mul_of_nonneg_left hpow hC.le)
  obtain ⟨Φ, hΦ_point, hΦ_T⟩ :=
    schwartz_clm_fubini_exchange (m := n + 1) T g fpad hg_cont hg_bound
  refine ⟨Lfrom Φ, ?_, ?_⟩
  · intro ξ
    let ξc : Fin (n + 1) → ℝ := by
      exact castFinCLE hn' ((finiteDimCoordCLE E) ξ)
    have hLfrom_apply : Lfrom Φ ξ = Φ ξc := by
      simp [Lfrom, ξc, fromCoordSchwartz]
    calc
      Lfrom Φ ξ = Φ ξc := hLfrom_apply
      _ = ∫ x : Fin (n + 1) → ℝ, g x ξc * fpad x := hΦ_point ξc
      _ = ∫ x : Fin (n + 1) → ℝ,
          G (x 0) ξ * ((φ : ℝ → ℂ) (x 0) * ρ (fun i : Fin n => x i.succ)) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          simp [g, Gcoord, Lto, fpad, ρ, ξc, toCoordSchwartz, SCV.prependField_apply]
      _ = ∫ t : ℝ, G t ξ * (φ : ℝ → ℂ) t := by
          exact padded_integral_collapse_point
            (H := fun t : ℝ => G t ξ) φ ρ
            (integral_normedUnitBumpSchwartzFin n)
      _ = ∫ t : ℝ, (φ : ℝ → ℂ) t * G t ξ := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with t
          ring
  · have h_from_to : ∀ F : SchwartzMap E ℂ, Lfrom (Lto F) = F := by
      intro F
      ext ξ
      simp [Lfrom, Lto, fromCoordSchwartz, toCoordSchwartz]
    calc
      w (Lfrom Φ)
          = ∫ x : Fin (n + 1) → ℝ, T (g x) * fpad x := by
          simpa [T, wCLM] using hΦ_T
      _ = ∫ x : Fin (n + 1) → ℝ,
          w (G (x 0)) * ((φ : ℝ → ℂ) (x 0) * ρ (fun i : Fin n => x i.succ)) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          simp [T, wCLM, clmOfContinuousIsLinear, g, Gcoord, fpad, ρ, h_from_to,
            SCV.prependField_apply]
      _ = ∫ t : ℝ, w (G t) * (φ : ℝ → ℂ) t := by
          exact padded_integral_collapse_point
            (H := fun t : ℝ => w (G t)) φ ρ
            (integral_normedUnitBumpSchwartzFin n)

end
