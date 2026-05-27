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

-- **Axiom: CLM-integral exchange for Schwartz-valued families.**
--
-- Given:
-- - T : continuous linear functional on Schwartz space
-- - g : continuous Schwartz-valued family with polynomial seminorm growth
-- - f : Schwartz test function
--
-- Conclusion: there exists a Schwartz function Φ (the Schwartz-valued integral)
-- such that Φ(ξ) = ∫ g(x)(ξ) f(x) dx pointwise, and T(Φ) = ∫ T(g(x)) f(x) dx.
--
-- The axiom constructs Φ rather than taking it as input, to avoid redundancy
-- and ensure coherence. The continuity hypothesis on g (in Schwartz topology)
-- ensures the Bochner integral is well-defined.
axiom schwartz_clm_fubini_exchange {m : ℕ}
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (g : (Fin m → ℝ) → SchwartzMap (Fin m → ℝ) ℂ)
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    -- Continuity of the Schwartz-valued family (ensures Bochner integrability)
    (hg_cont : Continuous g)
    -- Uniform seminorm bound (polynomial growth in x)
    (hg_bound : ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ (x : Fin m → ℝ),
        SchwartzMap.seminorm ℝ k n (g x) ≤ C * (1 + ‖x‖) ^ N) :
    ∃ (Φ : SchwartzMap (Fin m → ℝ) ℂ),
      (∀ ξ : Fin m → ℝ, Φ ξ = ∫ x : Fin m → ℝ, g x ξ * f x) ∧
      (T Φ = ∫ x : Fin m → ℝ, T (g x) * f x)

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
