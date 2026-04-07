import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import OSReconstruction.Mathlib429Compat

/-!
# 1D Poincare Lemma for Schwartz Space

Given `f ∈ S(ℝ, ℂ)` with `∫ f = 0`, construct `g ∈ S(ℝ, ℂ)` with `g' = f`.

This is the one-dimensional base case for the zero-mean decomposition theorem
on Schwartz space that appears in the two-point Schwinger translation-reduction
lane.
-/

noncomputable section

open MeasureTheory Filter Topology Set SchwartzMap

namespace OSReconstruction
namespace Poincare1D

lemma schwartz_intervalIntegrable (f : SchwartzMap ℝ ℂ) (a b : ℝ) :
    IntervalIntegrable (⇑f) volume a b :=
  f.integrable.intervalIntegrable

lemma schwartz_stronglyMeasurableAtFilter (f : SchwartzMap ℝ ℂ) (l : Filter ℝ) :
    StronglyMeasurableAtFilter (⇑f) l volume := by
  exact f.continuous.measurable.stronglyMeasurable.stronglyMeasurableAtFilter

lemma schwartz_continuousAt (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    ContinuousAt (⇑f) x :=
  f.continuous.continuousAt

def antiderivRaw (f : SchwartzMap ℝ ℂ) (x : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..x, (f : ℝ → ℂ) t

def antiderivConst (f : SchwartzMap ℝ ℂ) : ℂ :=
  ∫ t in Iic (0 : ℝ), (f : ℝ → ℂ) t

def antideriv (f : SchwartzMap ℝ ℂ) (x : ℝ) : ℂ :=
  antiderivRaw f x + antiderivConst f

theorem hasDerivAt_antiderivRaw (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    HasDerivAt (antiderivRaw f) (f x) x := by
  exact intervalIntegral.integral_hasDerivAt_right
    (schwartz_intervalIntegrable f 0 x)
    (schwartz_stronglyMeasurableAtFilter f (nhds x))
    (schwartz_continuousAt f x)

theorem hasDerivAt_antideriv (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    HasDerivAt (antideriv f) (f x) x := by
  have h := hasDerivAt_antiderivRaw f x
  have h2 := h.add (hasDerivAt_const x (antiderivConst f))
  simpa [antideriv] using h2

theorem deriv_antideriv (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    deriv (antideriv f) x = f x :=
  (hasDerivAt_antideriv f x).deriv

theorem differentiable_antideriv (f : SchwartzMap ℝ ℂ) :
    Differentiable ℝ (antideriv f) :=
  fun x => (hasDerivAt_antideriv f x).differentiableAt

theorem antideriv_eq_integral_Iic (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    antideriv f x = ∫ t in Iic x, (f : ℝ → ℂ) t := by
  have h_Iic_x : Tendsto (fun r => ∫ t in r..x, (f : ℝ → ℂ) t) atBot
      (nhds (∫ t in Iic x, (f : ℝ → ℂ) t)) :=
    intervalIntegral_tendsto_integral_Iic x f.integrable.integrableOn tendsto_id
  have h_Iic_0 : Tendsto (fun r => ∫ t in r..(0 : ℝ), (f : ℝ → ℂ) t) atBot
      (nhds (∫ t in Iic (0 : ℝ), (f : ℝ → ℂ) t)) :=
    intervalIntegral_tendsto_integral_Iic 0 f.integrable.integrableOn tendsto_id
  have h_split : ∀ r : ℝ, ∫ t in r..x, (f : ℝ → ℂ) t =
      (∫ t in r..(0 : ℝ), (f : ℝ → ℂ) t) + (∫ t in (0 : ℝ)..x, (f : ℝ → ℂ) t) :=
    fun r => (intervalIntegral.integral_add_adjacent_intervals
      (schwartz_intervalIntegrable f r 0) (schwartz_intervalIntegrable f 0 x)).symm
  have h_lim : Tendsto (fun r => (∫ t in r..(0 : ℝ), (f : ℝ → ℂ) t) +
      (∫ t in (0 : ℝ)..x, (f : ℝ → ℂ) t)) atBot
      (nhds ((∫ t in Iic (0 : ℝ), (f : ℝ → ℂ) t) +
        (∫ t in (0 : ℝ)..x, (f : ℝ → ℂ) t))) :=
    h_Iic_0.add tendsto_const_nhds
  have h_eq_lim : Tendsto (fun r => ∫ t in r..x, (f : ℝ → ℂ) t) atBot
      (nhds ((∫ t in Iic (0 : ℝ), (f : ℝ → ℂ) t) +
        (∫ t in (0 : ℝ)..x, (f : ℝ → ℂ) t))) :=
    Filter.Tendsto.congr (fun r => (h_split r).symm) h_lim
  have h_unique := tendsto_nhds_unique h_Iic_x h_eq_lim
  simp only [antideriv, antiderivRaw, antiderivConst]
  rw [h_unique, add_comm]

theorem antideriv_eq_neg_integral_Ioi (f : SchwartzMap ℝ ℂ)
    (hf : ∫ t, (f : ℝ → ℂ) t = 0) (x : ℝ) :
    antideriv f x = -(∫ t in Ioi x, (f : ℝ → ℂ) t) := by
  rw [antideriv_eq_integral_Iic f x]
  have hsum := intervalIntegral.integral_Iic_add_Ioi
    (f.integrable.integrableOn : IntegrableOn (⇑f) (Iic x))
    (f.integrable.integrableOn : IntegrableOn (⇑f) (Ioi x))
  rw [hf] at hsum
  exact eq_neg_of_add_eq_zero_left hsum

theorem contDiff_antideriv (f : SchwartzMap ℝ ℂ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (antideriv f) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨differentiable_antideriv f, ?_⟩
  have hderiv : deriv (antideriv f) = ⇑f := by
    ext x
    exact deriv_antideriv f x
  rw [hderiv]
  exact f.smooth'

theorem iteratedDeriv_antideriv_succ (f : SchwartzMap ℝ ℂ) (n : ℕ) (x : ℝ) :
    iteratedDeriv (n + 1) (antideriv f) x = iteratedDeriv n (⇑f) x := by
  rw [iteratedDeriv_succ']
  have hderiv : deriv (antideriv f) = ⇑f := by
    ext y
    exact deriv_antideriv f y
  rw [hderiv]

lemma schwartz_decay_iteratedDeriv (f : SchwartzMap ℝ ℂ) (k n : ℕ) :
    ∃ C, ∀ x : ℝ, ‖x‖ ^ k * ‖iteratedDeriv n (⇑f) x‖ ≤ C := by
  obtain ⟨C, _, hC⟩ := f.decay k n
  exact ⟨C, fun x => by
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hC x⟩

theorem schwartz_poly_integrable_Ioi (f : SchwartzMap ℝ ℂ) (k : ℕ) (x : ℝ) :
    IntegrableOn (fun t => (‖t‖ ^ k : ℝ) • (f : ℝ → ℂ) t) (Ioi x) volume := by
  rw [IntegrableOn, ← integrable_norm_iff
    ((continuous_norm.pow k |>.smul f.continuous).aestronglyMeasurable)]
  simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _),
    mul_comm, mul_left_comm, mul_assoc] using
    (f.integrable_pow_mul volume k).integrableOn

theorem tendsto_integral_Ioi_atTop (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun x => ∫ t in Ioi x, (f : ℝ → ℂ) t) atTop (𝓝 0) := by
  have htail :=
    MeasureTheory.tendsto_setIntegral_of_antitone
      (μ := volume) (f := (f : ℝ → ℂ))
      (s := fun x : ℝ => Ioi x)
      (fun x => measurableSet_Ioi)
      (fun a b hab => by
        intro y hy
        exact lt_of_le_of_lt hab hy)
      ⟨0, f.integrable.integrableOn⟩
  have hempty : (⋂ x : ℝ, Ioi x) = (∅ : Set ℝ) := by
    ext y
    constructor
    · intro hy
      have hy' : ∀ i : ℝ, i < y := by
        simpa [Set.mem_iInter] using hy
      exact (lt_irrefl y) (hy' y)
    · intro hy
      simp at hy
  simpa [hempty] using htail

theorem antideriv_weighted_decay_pos (f : SchwartzMap ℝ ℂ)
    (hf : ∫ t, (f : ℝ → ℂ) t = 0) (k : ℕ) :
    ∃ C, ∀ x : ℝ, 0 ≤ x ->
      ‖x‖ ^ k * ‖antideriv f x‖ ≤ C := by
  refine ⟨∫ t, ‖t‖ ^ k * ‖(f : ℝ → ℂ) t‖, ?_⟩
  intro x hx
  have hf_norm_int : IntegrableOn (fun t => ‖(f : ℝ → ℂ) t‖) (Ioi x) volume := by
    exact f.integrable.norm.integrableOn
  have hleft_int : IntegrableOn (fun t => ‖x‖ ^ k * ‖(f : ℝ → ℂ) t‖) (Ioi x) volume := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hf_norm_int.const_mul (‖x‖ ^ k)
  have hright_int : IntegrableOn (fun t => ‖t‖ ^ k * ‖(f : ℝ → ℂ) t‖) (Ioi x) volume := by
    exact (f.integrable_pow_mul volume k).integrableOn
  calc
    ‖x‖ ^ k * ‖antideriv f x‖
        = ‖x‖ ^ k * ‖∫ t in Ioi x, (f : ℝ → ℂ) t‖ := by
            rw [antideriv_eq_neg_integral_Ioi f hf x, norm_neg]
    _ ≤ ‖x‖ ^ k * ∫ t in Ioi x, ‖(f : ℝ → ℂ) t‖ := by
          gcongr
          simpa using
            (norm_integral_le_integral_norm (μ := volume.restrict (Ioi x))
              (f := (f : ℝ → ℂ)))
    _ = ∫ t in Ioi x, ‖x‖ ^ k * ‖(f : ℝ → ℂ) t‖ := by
          rw [← integral_const_mul]
    _ ≤ ∫ t in Ioi x, ‖t‖ ^ k * ‖(f : ℝ → ℂ) t‖ := by
          refine setIntegral_mono_on hleft_int hright_int measurableSet_Ioi ?_
          intro t ht
          have hxt : x ≤ t := le_of_lt ht
          have ht0 : 0 ≤ t := le_trans hx hxt
          have hpow : ‖x‖ ^ k ≤ ‖t‖ ^ k := by
            rw [Real.norm_of_nonneg hx, Real.norm_of_nonneg ht0]
            exact pow_le_pow_left₀ hx hxt k
          exact mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ ≤ ∫ t, ‖t‖ ^ k * ‖(f : ℝ → ℂ) t‖ := by
          exact setIntegral_le_integral
            (hfi := f.integrable_pow_mul volume k)
            (hf := Eventually.of_forall fun t =>
              mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))

theorem antideriv_weighted_decay_neg (f : SchwartzMap ℝ ℂ)
    (hf : ∫ t, (f : ℝ → ℂ) t = 0) (k : ℕ) :
    ∃ C, ∀ x : ℝ, x ≤ 0 ->
      ‖x‖ ^ k * ‖antideriv f x‖ ≤ C := by
  refine ⟨∫ t, ‖t‖ ^ k * ‖(f : ℝ → ℂ) t‖, ?_⟩
  intro x hx
  have hf_norm_int : IntegrableOn (fun t => ‖(f : ℝ → ℂ) t‖) (Iic x) volume := by
    exact f.integrable.norm.integrableOn
  have hleft_int : IntegrableOn (fun t => ‖x‖ ^ k * ‖(f : ℝ → ℂ) t‖) (Iic x) volume := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hf_norm_int.const_mul (‖x‖ ^ k)
  have hright_int : IntegrableOn (fun t => ‖t‖ ^ k * ‖(f : ℝ → ℂ) t‖) (Iic x) volume := by
    exact (f.integrable_pow_mul volume k).integrableOn
  calc
    ‖x‖ ^ k * ‖antideriv f x‖
        = ‖x‖ ^ k * ‖∫ t in Iic x, (f : ℝ -> ℂ) t‖ := by
            rw [antideriv_eq_integral_Iic f x]
    _ ≤ ‖x‖ ^ k * ∫ t in Iic x, ‖(f : ℝ → ℂ) t‖ := by
          gcongr
          simpa using
            (norm_integral_le_integral_norm (μ := volume.restrict (Iic x))
              (f := (f : ℝ → ℂ)))
    _ = ∫ t in Iic x, ‖x‖ ^ k * ‖(f : ℝ → ℂ) t‖ := by
          rw [← integral_const_mul]
    _ ≤ ∫ t in Iic x, ‖t‖ ^ k * ‖(f : ℝ → ℂ) t‖ := by
          refine setIntegral_mono_on hleft_int hright_int measurableSet_Iic ?_
          intro t ht
          have ht0 : t ≤ 0 := le_trans ht hx
          have hnorm : ‖x‖ ≤ ‖t‖ := by
            rw [Real.norm_of_nonpos hx, Real.norm_of_nonpos ht0]
            exact neg_le_neg ht
          have hpow : ‖x‖ ^ k ≤ ‖t‖ ^ k := by
            exact pow_le_pow_left₀ (norm_nonneg _) hnorm k
          exact mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ ≤ ∫ t, ‖t‖ ^ k * ‖(f : ℝ → ℂ) t‖ := by
          exact setIntegral_le_integral
            (hfi := f.integrable_pow_mul volume k)
            (hf := Eventually.of_forall fun t =>
              mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))

theorem antideriv_weighted_decay (f : SchwartzMap ℝ ℂ)
    (hf : ∫ t, (f : ℝ → ℂ) t = 0) (k : ℕ) :
    ∃ C, ∀ x : ℝ, ‖x‖ ^ k * ‖antideriv f x‖ ≤ C := by
  obtain ⟨C₁, hC₁⟩ := antideriv_weighted_decay_pos f hf k
  obtain ⟨C₂, hC₂⟩ := antideriv_weighted_decay_neg f hf k
  exact ⟨max C₁ C₂, fun x => by
    by_cases hx : 0 ≤ x
    · exact le_trans (hC₁ x hx) (le_max_left _ _)
    · exact le_trans (hC₂ x (le_of_not_ge hx)) (le_max_right _ _)⟩

theorem antideriv_decay (f : SchwartzMap ℝ ℂ)
    (hf : ∫ t, (f : ℝ → ℂ) t = 0) (k n : ℕ) :
    ∃ C, ∀ x : ℝ, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (antideriv f) x‖ ≤ C := by
  cases n with
  | zero =>
    obtain ⟨C, hC⟩ := antideriv_weighted_decay f hf k
    refine ⟨C, fun x => ?_⟩
    rw [norm_iteratedFDeriv_zero]
    exact hC x
  | succ n =>
    obtain ⟨C, _, hC⟩ := f.decay k n
    refine ⟨C, fun x => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
        iteratedDeriv_antideriv_succ f n x,
        ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hC x

noncomputable def schwartzAntideriv (f : SchwartzMap ℝ ℂ)
    (hf : ∫ t, (f : ℝ → ℂ) t = 0) : SchwartzMap ℝ ℂ :=
  SchwartzMap.mk (antideriv f) (contDiff_antideriv f) (antideriv_decay f hf)

theorem derivCLM_schwartzAntideriv (f : SchwartzMap ℝ ℂ)
    (hf : ∫ t, (f : ℝ → ℂ) t = 0) :
    SchwartzMap.derivCLM ℂ ℂ (schwartzAntideriv f hf) = f := by
  ext x
  simp only [SchwartzMap.derivCLM_apply]
  show deriv (fun x => (schwartzAntideriv f hf : ℝ → ℂ) x) x = f x
  have : ⇑(schwartzAntideriv f hf) = antideriv f := by
    ext y
    rfl
  rw [this]
  exact deriv_antideriv f x

theorem poincare_lemma_1d (f : SchwartzMap ℝ ℂ)
    (hf : ∫ t, (f : ℝ → ℂ) t = 0) :
    ∃ g : SchwartzMap ℝ ℂ, f = SchwartzMap.derivCLM ℂ ℂ g := by
  exact ⟨schwartzAntideriv f hf, (derivCLM_schwartzAntideriv f hf).symm⟩

end Poincare1D
end OSReconstruction
