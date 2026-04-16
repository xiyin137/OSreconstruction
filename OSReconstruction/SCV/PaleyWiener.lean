/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.TubeDomainExtension
import OSReconstruction.SCV.TubeDistributions
import OSReconstruction.SCV.FourierLaplaceCore
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Paley-Wiener-Schwartz Theorem

This file develops the Paley-Wiener-Schwartz theorem and its consequences for
holomorphic extension of distributions with one-sided Fourier support.

## Main results

* `paley_wiener_half_line` -- If T in S'(R) has supp(FT) in [0,infinity), then
  z -> T(e^{-iz.}) extends holomorphically to the upper half-plane.

* `paley_wiener_one_step` -- Slice-wise one-variable extension family:
  for each fixed parameter slice with one-sided Fourier support in one variable,
  produce the upper-half-plane extension in that variable.

Multidimensional cone/converse Paley-Wiener statements are intentionally deferred
from this file. The current `Fin m → ℝ` setup uses the wrong ambient Fourier
domain for an honest `fourierTransformCLM` formalization; the full cone theorem
should be rebuilt later over `EuclideanSpace ℝ (Fin m)`.

## Mathematical Background

The classical Paley-Wiener theorem (for L^2) states that a function f in L^2(R) has
Fourier transform supported in [0,infinity) if and only if f extends holomorphically
to the upper half-plane with L^2 bounds on horizontal lines.

The Schwartz generalization replaces L^2 with tempered distributions S'(R^m) and
replaces L^2 bounds with polynomial growth. The key result: if T in S'(R^m) and
supp(FT) in C* (the dual cone of an open convex cone C in R^m), then the
Fourier-Laplace transform

    F(z) = <FT, e^{iz . .}>

is holomorphic on the tube domain T(C) = R^m + iC, with at most polynomial growth
as Im(z) approaches the boundary of C.

The converse also holds: any holomorphic function on T(C) with polynomial growth
is the Fourier-Laplace transform of a tempered distribution with Fourier support in C*.

## Application

The key consumer is `inductive_analytic_continuation` (OS II, Theorem 4.1) in
WickRotation.lean. At each induction step, one fixes all variables except one
spacetime component, obtains a function of one real variable with polynomial growth
(from E0') whose Fourier transform has one-sided support (from positivity of the
Hamiltonian / reflection positivity), and applies Paley-Wiener to extend
holomorphically to the upper half-plane in that variable.

## References

* Reed-Simon II, Theorem IX.16 (Paley-Wiener for L^2)
* Hormander, "The Analysis of Linear Partial Differential Operators I", Theorem 7.4.3
* Vladimirov, "Methods of the Theory of Generalized Functions", Section 25-26
* Streater-Wightman, "PCT, Spin and Statistics", Theorem 2-6
-/

noncomputable section

open Complex MeasureTheory Topology Metric Set Filter
open scoped FourierTransform ComplexInnerProductSpace BoundedContinuousFunction

namespace SCV

/-! ### Fourier support for tempered distributions

In this file, only the one-dimensional Fourier-support notion is formalized.

For higher-dimensional Paley-Wiener theory, the correct ambient domain is
`EuclideanSpace ℝ (Fin m)`, because Mathlib's Fourier transform on Schwartz
space is organized over the inner-product-space model. The rest of this file,
and the tube-domain infrastructure around it, still use `Fin m → ℝ`, so the
honest multidimensional Fourier-support notion is deferred rather than being
encoded by a surrogate definition.
-/

/-- A tempered distribution T (a continuous linear functional on Schwartz space)
    has **one-sided Fourier support** (in the half-line [0, infinity)) if
    the Fourier transform T̂ of T vanishes on Schwartz functions supported
    in (-infinity, 0).

    Formally: T has Fourier support in [0, ∞) iff for every φ ∈ 𝓢(ℝ,ℂ)
    with supp(φ) ⊂ (-∞, 0), we have T̂(φ) = T(ℱ[φ]) = 0, where ℱ is
    the Schwartz-space Fourier transform.

    This is expressed via Fourier duality: (T̂)(φ) = T(F[φ]) where
    F = SchwartzMap.fourierTransformCLM ℂ is the Fourier transform operator
    on 𝓢(ℝ,ℂ).

    Note: This correctly captures Fourier support (not distributional support).
    A distribution T with supp(T) ⊂ [0,∞) does NOT necessarily have Fourier
    support in [0,∞) — these are distinct conditions. The Paley-Wiener theorem
    requires Fourier support, not distributional support.

    This is the key hypothesis for the Paley-Wiener theorem.

    Ref: Hörmander, "Analysis of PDE I", Definition 7.1.1;
    Vladimirov, "Generalized Functions", §8. -/
def HasOneSidedFourierSupport (T : SchwartzMap ℝ ℂ → ℂ) : Prop :=
  ∀ (φ : SchwartzMap ℝ ℂ),
    (∀ x ∈ Function.support (φ : ℝ → ℂ), x < 0) →
    T (SchwartzMap.fourierTransformCLM ℂ φ) = 0

/-- If a tempered distribution has one-sided Fourier support, then after pairing
    against its Fourier transform it depends only on the restriction of the
    Schwartz kernel to `[0, ∞)`. Any change on the negative half-line is invisible. -/
theorem fourier_pairing_eq_of_eqOn_nonneg
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (hT_supp : HasOneSidedFourierSupport T)
    {φ ψ : SchwartzMap ℝ ℂ}
    (h_eq : Set.EqOn φ ψ (Set.Ici 0)) :
    T (SchwartzMap.fourierTransformCLM ℂ φ) =
      T (SchwartzMap.fourierTransformCLM ℂ ψ) := by
  have hsupp :
      ∀ x ∈ Function.support ((φ - ψ : SchwartzMap ℝ ℂ) : ℝ → ℂ), x < 0 := by
    intro x hx
    by_cases hx_nonneg : 0 ≤ x
    · have hzero : (φ - ψ : SchwartzMap ℝ ℂ) x = 0 := by
        simp [h_eq hx_nonneg]
      exact (hx hzero).elim
    · linarith
  have hzero :
      T (SchwartzMap.fourierTransformCLM ℂ (φ - ψ : SchwartzMap ℝ ℂ)) = 0 :=
    hT_supp (φ - ψ) hsupp
  exact sub_eq_zero.mp (by
    simpa [map_sub] using hzero)

/-- One-sided Fourier-support pairings vanish on Fourier-transformed Schwartz
tests that are identically zero on `[0, ∞)`. This is the zero-specialization of
`fourier_pairing_eq_of_eqOn_nonneg` and is the small dual lemma used when a
Stage-5 slice difference is known to vanish on the positive half-line. -/
theorem fourier_pairing_vanishes_of_eqOn_nonneg
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (hT_supp : HasOneSidedFourierSupport T)
    {φ : SchwartzMap ℝ ℂ}
    (h_zero : Set.EqOn φ 0 (Set.Ici 0)) :
    T (SchwartzMap.fourierTransformCLM ℂ φ) = 0 := by
  simpa using
    (fourier_pairing_eq_of_eqOn_nonneg (T := T) hT_supp (φ := φ) (ψ := 0) h_zero)

/-- Cauchy-rectangle core for the upper-half-plane contour-shift argument:
the bottom horizontal integral on `[-R, R]` can be rewritten as the top edge
plus the two vertical sides. This isolates the complex-analytic content; later
vanishing theorems only need to send those three boundary terms to `0` as
`R → ∞`. -/
theorem intervalIntegral_eq_top_sub_right_add_left_of_holomorphic_UHP
    (g : ℂ → ℂ)
    (hg_holo : DifferentiableOn ℂ g {z : ℂ | 0 ≤ z.im})
    {R : ℝ} (hR : 0 ≤ R) :
    ∫ x : ℝ in -R..R, g x =
      -(Complex.I * ∫ y : ℝ in 0..R, g (↑R + ↑y * I)) +
        ((∫ x : ℝ in -R..R, g (↑x + ↑R * I)) +
          Complex.I * ∫ y : ℝ in 0..R, g (↑y * I + -↑R)) := by
  have hrect_holo :
      DifferentiableOn ℂ g ((Set.uIcc (-R) R) ×ℂ (Set.uIcc 0 R)) := by
    refine hg_holo.mono ?_
    intro z hz
    show 0 ≤ z.im
    simpa [hR] using (Complex.mem_reProdIm.mp hz).2.1
  let A : ℂ := ∫ x : ℝ in -R..R, g x
  let B : ℂ := ∫ x : ℝ in -R..R, g (↑x + ↑R * I)
  let C : ℂ := Complex.I • ∫ y : ℝ in 0..R, g (↑R + ↑y * I)
  let D : ℂ := Complex.I • ∫ y : ℝ in 0..R, g (-↑R + ↑y * I)
  have hrect :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      g (-R) (R + R * Complex.I) (by
        simpa [Complex.add_re, Complex.add_im] using hrect_holo)
  have hzero : A - (B - C + D) = 0 := by
    simpa [A, B, C, D, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
      smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hrect
  have hswap :
      (∫ x : ℝ in -R..R, g (↑R * I + ↑x)) =
        ∫ x : ℝ in -R..R, g (↑x + ↑R * I) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with x
    intro _
    rw [add_comm]
  have hmain := (sub_eq_zero.mp hzero)
  abel_nf at hmain
  simpa [A, B, C, D, hswap, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
    smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hmain

/-- If `g` is holomorphic on the closed upper half-plane and its top horizontal
and vertical-edge integrals vanish as the Cauchy rectangle grows, then the real
line integral of `g` is `0`. This is the contour-shift supplier used by the
current Stage-5 reverse-Paley-Wiener route. -/
theorem integral_zero_of_holomorphic_UHP_exponentialDecay
    (g : ℂ → ℂ)
    (hg_holo : DifferentiableOn ℂ g {z : ℂ | 0 ≤ z.im})
    (hg_integrable : MeasureTheory.Integrable (fun x : ℝ => g x))
    (hg_top_integrable : ∀ R : ℝ, 0 ≤ R →
      MeasureTheory.Integrable (fun x : ℝ => g (↑x + ↑R * I)))
    (hg_decay_top : ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∫ x : ℝ, ‖g (↑x + ↑R * I)‖ ≤ ε)
    (hg_decay_sides : ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      (∫ y in Set.Icc (0 : ℝ) R, ‖g (↑R + ↑y * I)‖) +
        (∫ y in Set.Icc (0 : ℝ) R, ‖g (-↑R + ↑y * I)‖) ≤ ε) :
    ∫ x : ℝ, g x = 0 := by
  have hleft :
      Filter.Tendsto (fun R : ℝ => ∫ x : ℝ in -R..0, g x)
        Filter.atTop (nhds (∫ x : ℝ in Set.Iic 0, g x)) := by
    have hneg_atBot : Filter.Tendsto (fun R : ℝ => -R) Filter.atTop Filter.atBot := by
      simpa using
        (Filter.Tendsto.neg_mul_atTop
          (f := fun _ : ℝ => (-1 : ℝ))
          (g := fun R : ℝ => R)
          (C := (-1 : ℝ))
          (by norm_num)
          tendsto_const_nhds
          Filter.tendsto_id)
    simpa using
      (MeasureTheory.intervalIntegral_tendsto_integral_Iic
        (f := fun x : ℝ => g x) 0 hg_integrable.integrableOn hneg_atBot)
  have hright :
      Filter.Tendsto (fun R : ℝ => ∫ x : ℝ in (0 : ℝ)..R, g x)
        Filter.atTop (nhds (∫ x : ℝ in Set.Ioi 0, g x)) := by
    simpa using
      (MeasureTheory.intervalIntegral_tendsto_integral_Ioi
        (f := fun x : ℝ => g x) 0 hg_integrable.integrableOn Filter.tendsto_id)
  have htrunc :
      Filter.Tendsto (fun R : ℝ => ∫ x : ℝ in -R..R, g x)
        Filter.atTop
        (nhds ((∫ x : ℝ in Set.Iic 0, g x) + ∫ x : ℝ in Set.Ioi 0, g x)) := by
    refine Filter.Tendsto.congr' ?_ (hleft.add hright)
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with R hR
    have hneg : IntervalIntegrable (fun x : ℝ => g x) MeasureTheory.volume (-R) 0 :=
      hg_integrable.intervalIntegrable
    have hpos : IntervalIntegrable (fun x : ℝ => g x) MeasureTheory.volume 0 R :=
      hg_integrable.intervalIntegrable
    exact intervalIntegral.integral_add_adjacent_intervals hneg hpos
  have htrunc_full :
      Filter.Tendsto (fun R : ℝ => ∫ x : ℝ in -R..R, g x)
        Filter.atTop (nhds (∫ x : ℝ, g x)) := by
    have hsplit :
        (∫ x : ℝ in Set.Iic 0, g x) + (∫ x : ℝ in Set.Ioi 0, g x) =
          ∫ x : ℝ, g x := by
      convert
        (MeasureTheory.setIntegral_union (Set.Iic_disjoint_Ioi <| Eq.le rfl)
          measurableSet_Ioi hg_integrable.integrableOn hg_integrable.integrableOn).symm
      rw [Set.Iic_union_Ioi, MeasureTheory.Measure.restrict_univ]
    simpa [hsplit] using htrunc
  have hzero :
      Filter.Tendsto (fun R : ℝ => ∫ x : ℝ in -R..R, g x)
        Filter.atTop (nhds (0 : ℂ)) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine Metric.tendsto_nhds.mpr ?_
    intro ε hε
    obtain ⟨R₁, hR₁_pos, hR₁⟩ := hg_decay_top (ε / 3) (by positivity)
    obtain ⟨R₂, hR₂_pos, hR₂⟩ := hg_decay_sides (ε / 3) (by positivity)
    refine Filter.mem_atTop_sets.2 ?_
    refine ⟨max R₁ R₂, ?_⟩
    intro R hR
    have hR₁_le : R₁ ≤ R := le_trans (le_max_left _ _) hR
    have hR₂_le : R₂ ≤ R := le_trans (le_max_right _ _) hR
    have hR_nonneg : 0 ≤ R := le_trans (le_of_lt hR₁_pos) hR₁_le
    have hrect :=
      intervalIntegral_eq_top_sub_right_add_left_of_holomorphic_UHP g hg_holo hR_nonneg
    have htop :
        ‖∫ x : ℝ in -R..R, g (↑x + ↑R * I)‖ ≤ ε / 3 := by
      calc
        ‖∫ x : ℝ in -R..R, g (↑x + ↑R * I)‖
            ≤ ∫ x : ℝ in -R..R, ‖g (↑x + ↑R * I)‖ := by
              exact intervalIntegral.norm_integral_le_integral_norm (by linarith)
        _ = ∫ x : ℝ in Set.Ioc (-R) R, ‖g (↑x + ↑R * I)‖ := by
              rw [intervalIntegral.integral_of_le (by linarith)]
        _ ≤ ∫ x : ℝ, ‖g (↑x + ↑R * I)‖ := by
              exact MeasureTheory.setIntegral_le_integral
                ((hg_top_integrable R hR_nonneg).norm)
                (Filter.Eventually.of_forall fun _ => by positivity)
        _ ≤ ε / 3 := hR₁ R hR₁_le
    have hright_bound :
        ‖Complex.I * ∫ y : ℝ in (0 : ℝ)..R, g (↑R + ↑y * I)‖
          ≤ ∫ y in Set.Icc (0 : ℝ) R, ‖g (↑R + ↑y * I)‖ := by
      rw [norm_mul, Complex.norm_I, one_mul]
      calc
        ‖∫ y : ℝ in (0 : ℝ)..R, g (↑R + ↑y * I)‖
            ≤ ∫ y : ℝ in (0 : ℝ)..R, ‖g (↑R + ↑y * I)‖ := by
              exact intervalIntegral.norm_integral_le_integral_norm hR_nonneg
        _ = ∫ y in Set.Icc (0 : ℝ) R, ‖g (↑R + ↑y * I)‖ := by
              rw [intervalIntegral.integral_of_le hR_nonneg, MeasureTheory.integral_Icc_eq_integral_Ioc]
    have hleft_bound :
        ‖Complex.I * ∫ y : ℝ in (0 : ℝ)..R, g (↑y * I + -↑R)‖
          ≤ ∫ y in Set.Icc (0 : ℝ) R, ‖g (-↑R + ↑y * I)‖ := by
      rw [norm_mul, Complex.norm_I, one_mul]
      calc
        ‖∫ y : ℝ in (0 : ℝ)..R, g (↑y * I + -↑R)‖
            ≤ ∫ y : ℝ in (0 : ℝ)..R, ‖g (↑y * I + -↑R)‖ := by
              exact intervalIntegral.norm_integral_le_integral_norm hR_nonneg
        _ = ∫ y in Set.Icc (0 : ℝ) R, ‖g (↑y * I + -↑R)‖ := by
              rw [intervalIntegral.integral_of_le hR_nonneg, MeasureTheory.integral_Icc_eq_integral_Ioc]
        _ = ∫ y in Set.Icc (0 : ℝ) R, ‖g (-↑R + ↑y * I)‖ := by
              refine MeasureTheory.integral_congr_ae ?_
              filter_upwards with y
              simp [add_comm]
    let A : ℝ := ∫ y in Set.Icc (0 : ℝ) R, ‖g (↑R + ↑y * I)‖
    let B : ℝ := ∫ y in Set.Icc (0 : ℝ) R, ‖g (-↑R + ↑y * I)‖
    have hAB : A + B ≤ ε / 3 := by
      dsimp [A, B]
      exact hR₂ R hR₂_le
    have hsides :
        ‖Complex.I * ∫ y : ℝ in (0 : ℝ)..R, g (↑R + ↑y * I)‖ +
            ‖Complex.I * ∫ y : ℝ in (0 : ℝ)..R, g (↑y * I + -↑R)‖
          ≤ ε / 3 := by
      calc
        ‖Complex.I * ∫ y : ℝ in (0 : ℝ)..R, g (↑R + ↑y * I)‖ +
            ‖Complex.I * ∫ y : ℝ in (0 : ℝ)..R, g (↑y * I + -↑R)‖
          ≤ A + B := by
                exact add_le_add hright_bound hleft_bound
        _ ≤ ε / 3 := hAB
    have hnorm :
        ‖∫ x : ℝ in -R..R, g x‖ < ε := by
      rw [hrect]
      calc
        ‖-(Complex.I * ∫ y : ℝ in (0 : ℝ)..R, g (↑R + ↑y * I)) +
            ((∫ x : ℝ in -R..R, g (↑x + ↑R * I)) +
              Complex.I * ∫ y : ℝ in (0 : ℝ)..R, g (↑y * I + -↑R))‖
          ≤ ‖Complex.I * ∫ y : ℝ in (0 : ℝ)..R, g (↑R + ↑y * I)‖ +
              (‖∫ x : ℝ in -R..R, g (↑x + ↑R * I)‖ +
                ‖Complex.I * ∫ y : ℝ in (0 : ℝ)..R, g (↑y * I + -↑R)‖) := by
                  calc
                    ‖-(Complex.I * ∫ y : ℝ in (0 : ℝ)..R, g (↑R + ↑y * I)) +
                        ((∫ x : ℝ in -R..R, g (↑x + ↑R * I)) +
                          Complex.I * ∫ y : ℝ in (0 : ℝ)..R, g (↑y * I + -↑R))‖
                      ≤ ‖-(Complex.I * ∫ y : ℝ in (0 : ℝ)..R, g (↑R + ↑y * I))‖ +
                          ‖(∫ x : ℝ in -R..R, g (↑x + ↑R * I)) +
                            Complex.I * ∫ y : ℝ in (0 : ℝ)..R, g (↑y * I + -↑R)‖ := by
                              exact norm_add_le _ _
                    _ ≤ ‖Complex.I * ∫ y : ℝ in (0 : ℝ)..R, g (↑R + ↑y * I)‖ +
                          (‖∫ x : ℝ in -R..R, g (↑x + ↑R * I)‖ +
                            ‖Complex.I * ∫ y : ℝ in (0 : ℝ)..R, g (↑y * I + -↑R)‖) := by
                              gcongr
                              · simp
                              · exact norm_add_le _ _
        _ ≤ ε / 3 + ε / 3 := by nlinarith [htop, hsides]
        _ < ε := by linarith
    simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hnorm
  exact tendsto_nhds_unique htrunc_full hzero

/-- Honest reverse-Paley-Wiener reduction theorem: if a scalar functional `T`
is the boundary value of an upper-half-plane trace `F`, and if that trace
already annihilates Fourier transforms of negative-support Schwartz tests on
every positive horizontal line, then `T` has one-sided Fourier support.

This is the exact theorem surface needed by the current OS-route Stage-5
spectral argument. It deliberately does not claim that upper-half-plane
holomorphicity plus linewise polynomial growth alone already imply one-sided
Fourier support; the real missing content is the paired contour-shift
vanishing hypothesis `hzero`. -/
theorem hasOneSidedFourierSupport_of_boundaryValue_of_paired_zero
    (F : ℂ → ℂ)
    (T : SchwartzMap ℝ ℂ → ℂ)
    (hT_bv : ∀ φ : SchwartzMap ℝ ℂ,
      Filter.Tendsto (fun η : ℝ => ∫ x : ℝ, F (↑x + ↑η * I) * φ x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (T φ)))
    (hzero :
      ∀ (φ : SchwartzMap ℝ ℂ),
        (∀ x ∈ Function.support (φ : ℝ → ℂ), x < 0) →
        ∀ η : ℝ, 0 < η →
          ∫ x : ℝ, F (↑x + ↑η * I) *
            (SchwartzMap.fourierTransformCLM ℂ φ) x = 0) :
    HasOneSidedFourierSupport T := by
  intro φ hφ_neg_supp
  have hT_val := hT_bv (SchwartzMap.fourierTransformCLM ℂ φ)
  have htrace : (fun η : ℝ => ∫ x : ℝ,
      F (↑x + ↑η * I) * (SchwartzMap.fourierTransformCLM ℂ φ) x)
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)] fun _ => (0 : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact hzero φ hφ_neg_supp η hη
  have hzero_limit : Filter.Tendsto (fun η : ℝ => ∫ x : ℝ,
      F (↑x + ↑η * I) * (SchwartzMap.fourierTransformCLM ℂ φ) x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    Filter.Tendsto.congr' htrace.symm tendsto_const_nhds
  exact tendsto_nhds_unique hT_val hzero_limit

/-! ### Upper half-plane -/

/-- The upper half-plane { z in C : Im(z) > 0 }. -/
def upperHalfPlane : Set ℂ := { z : ℂ | z.im > 0 }

/-- A function on the real line with polynomial growth. -/
def HasPolynomialGrowthOnLine (f : ℝ → ℂ) : Prop :=
  ∃ (C_bound : ℝ) (N : ℕ), 0 < C_bound ∧
    ∀ x : ℝ, ‖f x‖ ≤ C_bound * (1 + |x|) ^ N

/-- The upper half-plane is open. -/
theorem upperHalfPlane_isOpen : IsOpen upperHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_im

private theorem im_mem_upperHalfPlane_of_mem_ball
    {z z₀ : ℂ} (hz₀ : z₀ ∈ upperHalfPlane)
    (hz : z ∈ Metric.ball z₀ (z₀.im / 2)) :
    0 < z.im := by
  have hz_norm : ‖z - z₀‖ < z₀.im / 2 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have h_im_lower : -(‖z - z₀‖) ≤ (z - z₀).im := by
    have habs : |(z - z₀).im| ≤ ‖z - z₀‖ := Complex.abs_im_le_norm (z - z₀)
    exact (abs_le.mp habs).1
  have hdelta : -(z₀.im / 2) < (z - z₀).im := by
    linarith
  have hz_eq : z.im = z₀.im + (z - z₀).im := by
    have : z = z₀ + (z - z₀) := by ring
    exact congrArg Complex.im this
  have hz₀_im : 0 < z₀.im := hz₀
  linarith

private theorem fourierKernel_hasDerivAt
    (ξ : ℝ) (z : ℂ) :
    HasDerivAt
      (fun w : ℂ => Complex.exp (-2 * Real.pi * Complex.I * w * (ξ : ℂ)))
      (((-2 * Real.pi * Complex.I * (ξ : ℂ)) *
          Complex.exp (-2 * Real.pi * Complex.I * z * (ξ : ℂ)))) z := by
  have hlin :
      HasDerivAt
        (fun w : ℂ => -2 * Real.pi * Complex.I * w * (ξ : ℂ))
        (-2 * Real.pi * Complex.I * (ξ : ℂ)) z := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (((hasDerivAt_id z).const_mul (-2 * Real.pi * Complex.I)).mul_const (ξ : ℂ))
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (Complex.hasDerivAt_exp (-2 * Real.pi * Complex.I * z * (ξ : ℂ))).comp z hlin

private theorem fourierKernelDeriv_norm_le_weighted
    (φ : SchwartzMap ℝ ℂ)
    (hφ : ∀ x ∈ Function.support (φ : ℝ → ℂ), x < 0)
    {z z₀ : ℂ} (hz₀ : z₀ ∈ upperHalfPlane)
    (hz : z ∈ Metric.ball z₀ (z₀.im / 2))
    (ξ : ℝ) :
    ‖(((-2 * Real.pi * Complex.I * (ξ : ℂ)) *
          Complex.exp (-2 * Real.pi * Complex.I * z * (ξ : ℂ))) * φ ξ)‖
      ≤ (2 * Real.pi) * (‖ξ‖ * ‖φ ξ‖) := by
  by_cases hξ : (φ : ℝ → ℂ) ξ = 0
  · simp [hξ]
  · have hξ_neg : ξ < 0 := hφ ξ hξ
    have hz_im : 0 < z.im := im_mem_upperHalfPlane_of_mem_ball hz₀ hz
    have hre : (-2 * Real.pi * Complex.I * z * (ξ : ℂ)).re = 2 * Real.pi * z.im * ξ := by
      simp [Complex.mul_re, Complex.mul_im, mul_left_comm, mul_comm, sub_eq_add_neg]
    have hexp : Real.exp (2 * Real.pi * z.im * ξ) ≤ 1 := by
      have hmul_nonneg : 0 ≤ 2 * Real.pi * z.im := by positivity
      have hle : 2 * Real.pi * z.im * ξ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hmul_nonneg hξ_neg.le
      exact Real.exp_le_one_iff.mpr hle
    rw [norm_mul, norm_mul, Complex.norm_exp, hre]
    calc
      ‖-2 * ↑Real.pi * Complex.I * ↑ξ‖ * Real.exp (2 * Real.pi * z.im * ξ) * ‖φ ξ‖
          ≤ ‖-2 * ↑Real.pi * Complex.I * ↑ξ‖ * 1 * ‖φ ξ‖ := by
            gcongr
      _ = (2 * Real.pi * ‖ξ‖) * ‖φ ξ‖ := by
            rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_real, Complex.norm_I]
            simp [Real.norm_eq_abs, abs_of_nonneg Real.pi_pos.le, abs_of_nonpos hξ_neg.le,
              mul_assoc, mul_left_comm, mul_comm]
      _ = (2 * Real.pi) * (‖ξ‖ * ‖φ ξ‖) := by ring

/-- If a Schwartz test is supported in the negative half-line, then its Fourier
transform kernel admits a holomorphic extension to the upper half-plane. This
is the first honest analytic ingredient for the reverse Paley-Wiener /
one-sided-spectral-support route. -/
theorem fourierTransform_negSupport_holomorphic_UHP
    (φ : SchwartzMap ℝ ℂ)
    (hφ : ∀ x ∈ Function.support (φ : ℝ → ℂ), x < 0) :
    DifferentiableOn ℂ
      (fun z : ℂ => ∫ ξ : ℝ, Complex.exp (-2 * Real.pi * I * z * ξ) * φ ξ)
      upperHalfPlane := by
  intro z₀ hz₀
  let F : ℂ → ℝ → ℂ :=
    fun z ξ => Complex.exp (-2 * Real.pi * Complex.I * z * (ξ : ℂ)) * φ ξ
  let F' : ℂ → ℝ → ℂ :=
    fun z ξ =>
      (((-2 * Real.pi * Complex.I * (ξ : ℂ)) *
          Complex.exp (-2 * Real.pi * Complex.I * z * (ξ : ℂ))) * φ ξ)
  let bound : ℝ → ℝ := fun ξ => (2 * Real.pi) * (‖ξ‖ * ‖φ ξ‖)
  have hz₀_im : 0 < z₀.im := hz₀
  have hs_ball : Metric.ball z₀ (z₀.im / 2) ∈ nhds z₀ := Metric.ball_mem_nhds z₀ (half_pos hz₀_im)
  have hinner_cont : ∀ z : ℂ, Continuous (fun ξ : ℝ => -2 * Real.pi * Complex.I * z * (ξ : ℂ)) := by
    intro z
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Complex.continuous_ofReal.const_mul ((-2 * Real.pi * Complex.I * z) : ℂ))
  have hkernel_meas : ∀ z : ℂ, MeasureTheory.AEStronglyMeasurable (F z) := by
    intro z
    exact ((Complex.continuous_exp.comp (hinner_cont z)).mul φ.continuous).aestronglyMeasurable
  have hkernelDeriv_meas : MeasureTheory.AEStronglyMeasurable (F' z₀) := by
    have hlin_cont : Continuous (fun ξ : ℝ => -2 * Real.pi * Complex.I * (ξ : ℂ)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Complex.continuous_ofReal.const_mul ((-2 * Real.pi * Complex.I) : ℂ))
    exact ((hlin_cont.mul (Complex.continuous_exp.comp (hinner_cont z₀))).mul
      φ.continuous).aestronglyMeasurable
  have hF_int : MeasureTheory.Integrable (F z₀) := by
    refine MeasureTheory.Integrable.mono'
      ((SchwartzMap.integrable (μ := MeasureTheory.volume) φ).norm)
      (hkernel_meas z₀)
      ?_
    filter_upwards with ξ
    rcases eq_or_ne ((φ : ℝ → ℂ) ξ) 0 with hξ | hξ
    · simp [F, hξ]
    · have hξ_neg : ξ < 0 := hφ ξ hξ
      calc
        ‖F z₀ ξ‖
            = Real.exp (2 * Real.pi * z₀.im * ξ) * ‖φ ξ‖ := by
                simp [F, Complex.norm_exp, mul_comm, mul_left_comm]
        _ ≤ 1 * ‖φ ξ‖ := by
              have hexp : Real.exp (2 * Real.pi * z₀.im * ξ) ≤ 1 := by
                have hle : 2 * Real.pi * z₀.im * ξ ≤ 0 := by
                  have hnonneg : 0 ≤ 2 * Real.pi * z₀.im := by positivity
                  exact mul_nonpos_of_nonneg_of_nonpos hnonneg hξ_neg.le
                exact Real.exp_le_one_iff.mpr hle
              gcongr
        _ = ‖φ ξ‖ := by ring
  have hderiv_ev :
      ∀ᵐ ξ : ℝ ∂MeasureTheory.volume,
        ∀ z ∈ Metric.ball z₀ (z₀.im / 2),
          HasDerivAt (fun z => F z ξ) (F' z ξ) z := by
    filter_upwards with ξ z hz
    simpa [F, F', mul_assoc, mul_left_comm, mul_comm] using
      ((fourierKernel_hasDerivAt ξ z).mul_const (φ ξ))
  have hbound_int : MeasureTheory.Integrable bound := by
    convert ((SchwartzMap.integrable_pow_mul MeasureTheory.volume φ 1).const_mul (2 * Real.pi)) using 1
    ext ξ
    simp [bound, pow_one, mul_assoc, mul_left_comm, mul_comm]
  have h :
      HasDerivAt (fun z => ∫ ξ, F z ξ) (∫ ξ, F' z₀ ξ) z₀ := by
    exact
      (hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (F := F) (F' := F') (x₀ := z₀) (s := Metric.ball z₀ (z₀.im / 2))
        (bound := bound)
        hs_ball
        (Filter.Eventually.of_forall hkernel_meas)
        hF_int
        hkernelDeriv_meas
        (Filter.Eventually.of_forall fun ξ z hz =>
          fourierKernelDeriv_norm_le_weighted φ hφ hz₀ hz ξ)
        hbound_int
        hderiv_ev).2
  exact h.differentiableAt.differentiableWithinAt

/-- If a Schwartz test is supported in `(-∞, -δ]`, then its Fourier-transform
kernel on the upper half-plane decays at least like `e^{-2πδ Im z}`.

This is the gap-away-from-zero ingredient used in the current Stage-5 contour
argument: once the test support stays strictly left of the origin, the
upper-half-plane Fourier transform gains genuine exponential decay in the
vertical direction. -/
theorem norm_fourierTransform_gapNegSupport_UHP_le
    (φ : SchwartzMap ℝ ℂ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hφ : ∀ x ∈ Function.support (φ : ℝ → ℂ), x ≤ -δ)
    (z : ℂ) (hz : z ∈ upperHalfPlane) :
    ‖∫ ξ : ℝ, Complex.exp (-2 * Real.pi * I * z * ξ) * φ ξ‖ ≤
      Real.exp (-2 * Real.pi * z.im * δ) * ∫ ξ : ℝ, ‖φ ξ‖ := by
  let F : ℝ → ℂ :=
    fun ξ => Complex.exp (-2 * Real.pi * I * z * ξ) * φ ξ
  have hF_int : MeasureTheory.Integrable F := by
    refine MeasureTheory.Integrable.mono'
      ((SchwartzMap.integrable (μ := MeasureTheory.volume) φ).norm)
      (((Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.const_mul ((-2 * Real.pi * Complex.I * z) : ℂ)))).mul
          φ.continuous).aestronglyMeasurable)
      ?_
    filter_upwards with ξ
    rcases eq_or_ne ((φ : ℝ → ℂ) ξ) 0 with hξ | hξ
    · simp [F, hξ]
    · have hξ_left : ξ ≤ -δ := hφ ξ hξ
      have hξ_nonpos : ξ ≤ 0 := by linarith
      calc
        ‖F ξ‖
            = Real.exp (2 * Real.pi * z.im * ξ) * ‖φ ξ‖ := by
                simp [F, Complex.norm_exp, mul_comm, mul_left_comm]
        _ ≤ 1 * ‖φ ξ‖ := by
              have hz_im : 0 < z.im := hz
              have hle : 2 * Real.pi * z.im * ξ ≤ 0 := by
                have hfac_nonneg : 0 ≤ 2 * Real.pi * z.im := by positivity
                exact mul_nonpos_of_nonneg_of_nonpos hfac_nonneg hξ_nonpos
              exact mul_le_mul_of_nonneg_right
                (by exact Real.exp_le_one_iff.mpr hle) (norm_nonneg _)
        _ = ‖φ ξ‖ := by ring
  calc
    ‖∫ ξ : ℝ, F ξ‖ ≤ ∫ ξ : ℝ, ‖F ξ‖ := by
          exact MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ ξ : ℝ, Real.exp (-2 * Real.pi * z.im * δ) * ‖φ ξ‖ := by
          refine MeasureTheory.integral_mono_ae ?_ ?_ ?_
          · exact hF_int.norm
          · exact ((SchwartzMap.integrable (μ := MeasureTheory.volume) φ).norm).const_mul _
          · filter_upwards with ξ
            rcases eq_or_ne ((φ : ℝ → ℂ) ξ) 0 with hξ | hξ
            · simp [F, hξ]
            · have hξ_left : ξ ≤ -δ := hφ ξ hξ
              calc
                ‖Complex.exp (-2 * Real.pi * I * z * ξ) * φ ξ‖
                    = Real.exp (2 * Real.pi * z.im * ξ) * ‖φ ξ‖ := by
                        simp [Complex.norm_exp, mul_comm, mul_left_comm]
                _ ≤ Real.exp (-2 * Real.pi * z.im * δ) * ‖φ ξ‖ := by
                      have hfac_nonneg : 0 ≤ 2 * Real.pi * z.im := by
                        have hz_im : 0 < z.im := hz
                        positivity
                      have hmul := mul_le_mul_of_nonneg_left hξ_left hfac_nonneg
                      have hle : 2 * Real.pi * z.im * ξ ≤ -2 * Real.pi * z.im * δ := by
                        simpa [mul_assoc, mul_left_comm, mul_comm, left_distrib, right_distrib] using hmul
                      exact mul_le_mul_of_nonneg_right
                        (Real.exp_le_exp.mpr hle) (norm_nonneg _)
    _ = Real.exp (-2 * Real.pi * z.im * δ) * ∫ ξ : ℝ, ‖φ ξ‖ := by
          rw [MeasureTheory.integral_const_mul]


/-! ### Finite Schwartz-seminorm control of tempered functionals -/

/-- A continuous linear functional on Schwartz space is controlled by finitely many
    Schwartz seminorms.

    This is the standard tempered-distribution boundedness statement specialized to
    `𝓢(ℝ, ℂ)`: continuity for the Schwartz topology is equivalent to domination by a
    finite supremum of Schwartz seminorms. It is the functional-analytic input needed
    to turn the abstract continuity hypothesis in `paley_wiener_half_line` into the
    concrete seminorm estimates used to control the Fourier-Laplace pairing. -/
theorem schwartz_functional_bound
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : NNReal, C ≠ 0 ∧
      ∀ φ : SchwartzMap ℝ ℂ,
        ‖T φ‖ ≤ (C • s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) φ := by
  let q : Seminorm ℂ (SchwartzMap ℝ ℂ) := (normSeminorm ℂ ℂ).comp T.toLinearMap
  have hq_cont : Continuous q := by
    change Continuous (fun φ : SchwartzMap ℝ ℂ => ‖T φ‖)
    simpa [q, Seminorm.comp_apply, coe_normSeminorm] using
      continuous_norm.comp T.continuous
  obtain ⟨s, C, hC, hbound⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℂ ℝ ℂ) q hq_cont
  refine ⟨s, C, hC, ?_⟩
  intro φ
  simpa [q, Seminorm.comp_apply, coe_normSeminorm] using hbound φ

private def polyWeight (k : ℕ) (x : ℝ) : ℂ := ((1 + x^2) ^ k : ℝ)

private theorem polyWeight_hasTemperateGrowth (k : ℕ) :
    (polyWeight k).HasTemperateGrowth := by
  unfold polyWeight
  fun_prop

private def iteratedDerivCLM : ℕ → SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ
  | 0 => ContinuousLinearMap.id ℂ _
  | n + 1 => (SchwartzMap.derivCLM ℂ ℂ).comp (iteratedDerivCLM n)

private theorem iteratedDerivCLM_apply
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    iteratedDerivCLM n f x = iteratedDeriv n f x := by
  induction n generalizing f x with
  | zero => simp [iteratedDerivCLM]
  | succ n ih =>
      have hg : ⇑(iteratedDerivCLM n f) = fun y : ℝ => iteratedDeriv n f y := by
        ext y
        exact ih f y
      rw [iteratedDerivCLM, ContinuousLinearMap.comp_apply, SchwartzMap.derivCLM_apply]
      rw [hg, ← iteratedDeriv_succ]

private def weightedDerivToBCFCLM (k n : ℕ) : SchwartzMap ℝ ℂ →L[ℂ] ℝ →ᵇ ℂ :=
  (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ).comp <|
    (SchwartzMap.smulLeftCLM ℂ (polyWeight k)).comp <|
      iteratedDerivCLM n

private theorem weightedDerivToBCFCLM_apply
    (k n : ℕ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    weightedDerivToBCFCLM k n f x = polyWeight k x * iteratedDeriv n f x := by
  rw [weightedDerivToBCFCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    SchwartzMap.smulLeftCLM_apply_apply (polyWeight_hasTemperateGrowth k),
    iteratedDerivCLM_apply]
  simp [polyWeight]

private theorem abs_pow_le_polyWeight (k : ℕ) (x : ℝ) :
    |x| ^ k ≤ ‖polyWeight k x‖ := by
  rw [polyWeight, Complex.norm_real]
  have h1 : |x| ≤ 1 + x^2 := by
    have hx2_nonneg : 0 ≤ x^2 := sq_nonneg x
    nlinarith [sq_abs x]
  calc
    |x| ^ k ≤ (1 + x^2) ^ k := by
      exact pow_le_pow_left₀ (abs_nonneg x) h1 k
    _ = ‖((1 + x ^ 2) ^ k : ℝ)‖ := by
      rw [Real.norm_of_nonneg]
      positivity

private def probeCLM (s : Finset (ℕ × ℕ)) :
    SchwartzMap ℝ ℂ →L[ℂ] ((p : ↑s.attach) → (ℝ →ᵇ ℂ)) :=
  ContinuousLinearMap.pi fun p : ↑s.attach => weightedDerivToBCFCLM p.1.1.1 p.1.1.2

private theorem schwartzSeminorm_le_probe_component_norm
    (k n : ℕ) (f : SchwartzMap ℝ ℂ) :
    SchwartzMap.seminorm ℝ k n f ≤ ‖weightedDerivToBCFCLM k n f‖ := by
  refine SchwartzMap.seminorm_le_bound' (𝕜 := ℝ) k n f (norm_nonneg _) ?_
  intro x
  have h1 : |x| ^ k * ‖iteratedDeriv n f x‖ ≤ ‖polyWeight k x‖ * ‖iteratedDeriv n f x‖ := by
    exact mul_le_mul_of_nonneg_right (abs_pow_le_polyWeight k x) (norm_nonneg _)
  calc
    |x| ^ k * ‖iteratedDeriv n f x‖
      ≤ ‖polyWeight k x‖ * ‖iteratedDeriv n f x‖ := h1
    _ = ‖polyWeight k x * iteratedDeriv n f x‖ := by rw [norm_mul]
    _ = ‖weightedDerivToBCFCLM k n f x‖ := by rw [weightedDerivToBCFCLM_apply]
    _ ≤ ‖weightedDerivToBCFCLM k n f‖ := by
      simpa using (BoundedContinuousFunction.norm_coe_le_norm (weightedDerivToBCFCLM k n f) x)

private theorem schwartzSeminorm_le_probe_norm
    (s : Finset (ℕ × ℕ)) (p : ↑s.attach) (f : SchwartzMap ℝ ℂ) :
    SchwartzMap.seminorm ℝ p.1.1.1 p.1.1.2 f ≤
      ‖(probeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ)))‖ := by
  calc
    SchwartzMap.seminorm ℝ p.1.1.1 p.1.1.2 f ≤ ‖weightedDerivToBCFCLM p.1.1.1 p.1.1.2 f‖ :=
      schwartzSeminorm_le_probe_component_norm p.1.1.1 p.1.1.2 f
    _ ≤ ‖(probeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ)))‖ := by
      simpa using (norm_le_pi_norm (probeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ))) p)

private theorem weightedDerivToBCFCLM_norm_le
    (k n : ℕ) (f : SchwartzMap ℝ ℂ) :
    ‖weightedDerivToBCFCLM k n f‖ ≤
      (2 : ℝ) ^ k *
        (SchwartzMap.seminorm ℝ 0 n f + SchwartzMap.seminorm ℝ (2 * k) n f) := by
  rw [show ‖weightedDerivToBCFCLM k n f‖ = dist (weightedDerivToBCFCLM k n f) 0 by rfl]
  refine (BoundedContinuousFunction.dist_le ?_).2 ?_
  · positivity
  · intro ξ
    have hsemi0 := SchwartzMap.le_seminorm' (𝕜 := ℝ) (k := 0) (n := n) f ξ
    have hsemi2 := SchwartzMap.le_seminorm' (𝕜 := ℝ) (k := 2 * k) (n := n) f ξ
    simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, dist_eq_norm, sub_zero,
      weightedDerivToBCFCLM_apply]
    by_cases hξ : |ξ| ≤ 1
    · have hpoly : ‖polyWeight k ξ‖ ≤ (2 : ℝ) ^ k := by
        rw [polyWeight, Complex.norm_real, Real.norm_of_nonneg]
        · have hξsq : ξ ^ 2 ≤ 1 := by
            have hsqabs : |ξ| ^ 2 ≤ (1 : ℝ) ^ 2 := by
              gcongr
            simpa [sq_abs] using hsqabs
          calc
            (1 + ξ ^ 2) ^ k ≤ (1 + 1) ^ k := by
              gcongr
            _ = (2 : ℝ) ^ k := by ring
        · positivity
      calc
        ‖polyWeight k ξ * iteratedDeriv n f ξ‖
            ≤ (2 : ℝ) ^ k * ‖iteratedDeriv n f ξ‖ := by
              rw [norm_mul]
              gcongr
        _ ≤ (2 : ℝ) ^ k * SchwartzMap.seminorm ℝ 0 n f := by
              exact mul_le_mul_of_nonneg_left (by simpa using hsemi0) (pow_nonneg (by positivity) _)
        _ ≤ (2 : ℝ) ^ k *
              (SchwartzMap.seminorm ℝ 0 n f + SchwartzMap.seminorm ℝ (2 * k) n f) := by
              gcongr
              exact le_add_of_nonneg_right (apply_nonneg _ _)
    · have hξgt : 1 < |ξ| := lt_of_not_ge hξ
      have habs_nonneg : 0 ≤ |ξ| := abs_nonneg ξ
      have hone : 1 ≤ |ξ| ^ 2 := by
        have : 1 ≤ |ξ| := le_of_lt hξgt
        nlinarith
      have hpoly : ‖polyWeight k ξ‖ ≤ (2 : ℝ) ^ k * |ξ| ^ (2 * k) := by
        rw [polyWeight, Complex.norm_real, Real.norm_of_nonneg]
        · have hξsq : ξ ^ 2 = |ξ| ^ 2 := by rw [sq_abs]
          calc
            (1 + ξ ^ 2) ^ k = (1 + |ξ| ^ 2) ^ k := by rw [hξsq]
            _ ≤ (2 * |ξ| ^ 2) ^ k := by
                  gcongr
                  linarith
            _ = (2 : ℝ) ^ k * |ξ| ^ (2 * k) := by
                  rw [mul_pow]
                  ring_nf
        · positivity
      calc
        ‖polyWeight k ξ * iteratedDeriv n f ξ‖
            ≤ ((2 : ℝ) ^ k * |ξ| ^ (2 * k)) * ‖iteratedDeriv n f ξ‖ := by
              rw [norm_mul]
              gcongr
        _ = (2 : ℝ) ^ k * (|ξ| ^ (2 * k) * ‖iteratedDeriv n f ξ‖) := by ring
        _ ≤ (2 : ℝ) ^ k * SchwartzMap.seminorm ℝ (2 * k) n f := by
              exact mul_le_mul_of_nonneg_left (by simpa using hsemi2) (pow_nonneg (by positivity) _)
        _ ≤ (2 : ℝ) ^ k *
              (SchwartzMap.seminorm ℝ 0 n f + SchwartzMap.seminorm ℝ (2 * k) n f) := by
              gcongr
              exact le_add_of_nonneg_left (apply_nonneg _ _)

private theorem schwartzPsiZ_horizontal_diff_eq
    (x η h : ℝ) (hη : 0 < η)
    (hh_im : ‖(h : ℂ)‖ ≤ η / 2) (hh1 : ‖(h : ℂ)‖ ≤ 1) :
    schwartzPsiZ (((x + h : ℝ) : ℂ) + η * I) (by simpa using hη) -
      schwartzPsiZ ((x : ℂ) + η * I) (by simpa using hη) -
      (h : ℂ) •
        (SchwartzMap.smulLeftCLM ℂ (fun ξ : ℝ => I * (ξ : ℂ)))
          (schwartzPsiZ ((x : ℂ) + η * I) (by simpa using hη)) =
    (h : ℂ) •
      schwartzPsiZExpTaylorLinearRemainderQuot
        ((x : ℂ) + η * I) (by simpa using hη) (h : ℂ) (by simpa using hh_im) hh1 := by
  have hzadd : ((x : ℂ) + η * I) + (h : ℂ) = (((x + h : ℝ) : ℂ) + η * I) := by
    norm_num
    ring
  have htemp : (fun ξ : ℝ => I * (ξ : ℂ)).HasTemperateGrowth := by
    fun_prop
  ext ξ
  simpa [hzadd, schwartzPsiZ_apply, schwartzPsiZExpTaylorLinearRemainderQuot_apply,
    SchwartzMap.smulLeftCLM_apply_apply htemp, smul_eq_mul] using
    (psiZ_sub_sub_deriv_eq_smul_remainder ((x : ℂ) + η * I) (h : ℂ) ξ)

private theorem tendsto_weightedDerivToBCFCLM_schwartzPsiZ_horizontal_diff_zero
    (η x : ℝ) (hη : 0 < η) (k n : ℕ) :
    Tendsto
      (fun h : ℝ =>
        ‖weightedDerivToBCFCLM k n
          (schwartzPsiZ (((x + h : ℝ) : ℂ) + η * I) (by simpa using hη) -
            schwartzPsiZ ((x : ℂ) + η * I) (by simpa using hη))‖)
      (nhds 0) (nhds 0) := by
  let z : ℂ := (x : ℂ) + η * I
  have hz : 0 < z.im := by simpa [z] using hη
  let D : ℝ := ‖weightedDerivToBCFCLM k n
    ((SchwartzMap.smulLeftCLM ℂ (fun ξ : ℝ => I * (ξ : ℂ)))
      (schwartzPsiZ z hz))‖
  obtain ⟨C0, hC0_nonneg, hC0⟩ :=
    schwartzPsiZExpTaylorLinearRemainderQuot_seminorm_le z hz 0 n
  obtain ⟨C2, hC2_nonneg, hC2⟩ :=
    schwartzPsiZExpTaylorLinearRemainderQuot_seminorm_le z hz (2 * k) n
  let C : ℝ := (2 : ℝ) ^ k * (C0 + C2)
  refine Metric.tendsto_nhds.mpr ?_
  intro ε hε
  have hD_nonneg : 0 ≤ D := norm_nonneg _
  let δ : ℝ := min 1 (min (η / 2) (ε / (2 * (D + C + 1))))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    refine lt_min (by norm_num) ?_
    refine lt_min ?_ ?_
    · positivity
    · have hden_pos : 0 < 2 * (D + C + 1) := by positivity
      exact div_pos hε hden_pos
  filter_upwards [Metric.ball_mem_nhds 0 hδ_pos] with h hh
  have hhδ : ‖(h : ℂ)‖ < δ := by
    simpa [Real.norm_eq_abs, Real.dist_eq, sub_eq_add_neg, abs_sub_comm] using hh
  have hh1 : ‖(h : ℂ)‖ ≤ 1 := by
    exact le_trans (le_of_lt hhδ) (by dsimp [δ]; exact min_le_left _ _)
  have hh_im : ‖(h : ℂ)‖ ≤ η / 2 := by
    exact le_trans (le_of_lt hhδ) (by dsimp [δ]; exact le_trans (min_le_right _ _) (min_le_left _ _))
  have hh_im' : ‖(h : ℂ)‖ ≤ z.im / 2 := by simpa [z] using hh_im
  have hdecomp := schwartzPsiZ_horizontal_diff_eq x η h hη hh_im hh1
  have hsplit :
      weightedDerivToBCFCLM k n
        (schwartzPsiZ (((x + h : ℝ) : ℂ) + η * I) (by simpa using hη) -
          schwartzPsiZ ((x : ℂ) + η * I) (by simpa using hη)) =
        h • weightedDerivToBCFCLM k n
          (schwartzPsiZExpTaylorLinearRemainderQuot z hz (h : ℂ) hh_im' hh1) +
        h • weightedDerivToBCFCLM k n
          ((SchwartzMap.smulLeftCLM ℂ (fun ξ : ℝ => I * (ξ : ℂ)))
            (schwartzPsiZ z hz)) := by
    have htmp :
        weightedDerivToBCFCLM k n
            (schwartzPsiZ (((x + h : ℝ) : ℂ) + η * I) (by simpa using hη) -
              schwartzPsiZ ((x : ℂ) + η * I) (by simpa using hη)) -
          h • weightedDerivToBCFCLM k n
            ((SchwartzMap.smulLeftCLM ℂ (fun ξ : ℝ => I * (ξ : ℂ)))
              (schwartzPsiZ z hz)) =
          h • weightedDerivToBCFCLM k n
            (schwartzPsiZExpTaylorLinearRemainderQuot z hz (h : ℂ) hh_im' hh1) := by
      simpa [hdecomp, map_sub, map_smul] using
        congrArg (weightedDerivToBCFCLM k n) hdecomp
    have htmp2 := eq_add_of_sub_eq htmp
    simpa [add_comm, add_left_comm, add_assoc] using htmp2
  have hrem :
      ‖weightedDerivToBCFCLM k n
          (schwartzPsiZExpTaylorLinearRemainderQuot z hz (h : ℂ) hh_im' hh1)‖ ≤
        C * ‖(h : ℂ)‖ := by
    calc
      ‖weightedDerivToBCFCLM k n
          (schwartzPsiZExpTaylorLinearRemainderQuot z hz (h : ℂ) hh_im' hh1)‖
          ≤ (2 : ℝ) ^ k *
              (SchwartzMap.seminorm ℝ 0 n
                  (schwartzPsiZExpTaylorLinearRemainderQuot z hz (h : ℂ) hh_im' hh1) +
                SchwartzMap.seminorm ℝ (2 * k) n
                  (schwartzPsiZExpTaylorLinearRemainderQuot z hz (h : ℂ) hh_im' hh1)) := by
              exact weightedDerivToBCFCLM_norm_le k n _
      _ ≤ (2 : ℝ) ^ k * (C0 * ‖(h : ℂ)‖ + C2 * ‖(h : ℂ)‖) := by
            gcongr
            · exact hC0 (h : ℂ) hh_im' hh1
            · exact hC2 (h : ℂ) hh_im' hh1
      _ = C * ‖(h : ℂ)‖ := by
            dsimp [C]
            ring
  have hmain :
      ‖weightedDerivToBCFCLM k n
          (schwartzPsiZ (((x + h : ℝ) : ℂ) + η * I) (by simpa using hη) -
            schwartzPsiZ ((x : ℂ) + η * I) (by simpa using hη))‖
        ≤ ‖(h : ℂ)‖ * (C * ‖(h : ℂ)‖) + ‖(h : ℂ)‖ * D := by
    calc
      ‖weightedDerivToBCFCLM k n
          (schwartzPsiZ (((x + h : ℝ) : ℂ) + η * I) (by simpa using hη) -
            schwartzPsiZ ((x : ℂ) + η * I) (by simpa using hη))‖
          = ‖h • weightedDerivToBCFCLM k n
              (schwartzPsiZExpTaylorLinearRemainderQuot z hz (h : ℂ) hh_im' hh1) +
            h • weightedDerivToBCFCLM k n
              ((SchwartzMap.smulLeftCLM ℂ (fun ξ : ℝ => I * (ξ : ℂ)))
                (schwartzPsiZ z hz))‖ := by
              rw [hsplit]
      _ ≤ ‖h • weightedDerivToBCFCLM k n
              (schwartzPsiZExpTaylorLinearRemainderQuot z hz (h : ℂ) hh_im' hh1)‖ +
            ‖h • weightedDerivToBCFCLM k n
              ((SchwartzMap.smulLeftCLM ℂ (fun ξ : ℝ => I * (ξ : ℂ)))
                (schwartzPsiZ z hz))‖ := norm_add_le _ _
      _ = ‖(h : ℂ)‖ *
            ‖weightedDerivToBCFCLM k n
              (schwartzPsiZExpTaylorLinearRemainderQuot z hz (h : ℂ) hh_im' hh1)‖ +
          ‖(h : ℂ)‖ * D := by
            set_option backward.isDefEq.respectTransparency false in
            simp only [D, norm_smul, Complex.norm_real]
      _ ≤ ‖(h : ℂ)‖ * (C * ‖(h : ℂ)‖) + ‖(h : ℂ)‖ * D := by
            gcongr
  have hδ_small : δ ≤ ε / (2 * (D + C + 1)) := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hsmall :
      ‖(h : ℂ)‖ * (C * ‖(h : ℂ)‖) + ‖(h : ℂ)‖ * D < ε := by
    have hδfrac : δ * (D + C + 1) < ε := by
      have hden_pos : 0 < 2 * (D + C + 1) := by positivity
      have htmp : δ * (2 * (D + C + 1)) ≤ ε := by
        exact (le_div_iff₀ hden_pos).mp hδ_small
      have hlt : δ * (D + C + 1) ≤ ε / 2 := by
        nlinarith
      linarith
    have hnorm_le : ‖(h : ℂ)‖ * (C * ‖(h : ℂ)‖) + ‖(h : ℂ)‖ * D ≤ δ * (D + C + 1) := by
      have hh_abs : ‖(h : ℂ)‖ ≤ δ := le_of_lt hhδ
      have hsq : ‖(h : ℂ)‖ * ‖(h : ℂ)‖ ≤ δ := by
        have : ‖(h : ℂ)‖ * ‖(h : ℂ)‖ ≤ δ * 1 := by
          refine mul_le_mul hh_abs hh1 ?_ ?_
          · exact norm_nonneg _
          · positivity
        simpa using this
      calc
        ‖(h : ℂ)‖ * (C * ‖(h : ℂ)‖) + ‖(h : ℂ)‖ * D
            = C * (‖(h : ℂ)‖ * ‖(h : ℂ)‖) + D * ‖(h : ℂ)‖ := by ring
        _ ≤ C * δ + D * δ := by
              gcongr
        _ ≤ δ * (D + C + 1) := by ring_nf; nlinarith [hδ_pos, hC0_nonneg, hC2_nonneg, hD_nonneg]
    exact lt_of_le_of_lt hnorm_le hδfrac
  simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using lt_of_le_of_lt hmain hsmall

private def horizontalSchwartzPsi (η : ℝ) (hη : 0 < η) (x : ℝ) : SchwartzMap ℝ ℂ :=
  schwartzPsiZ ((x : ℂ) + η * I) (by simpa using hη)

private def scaledHorizontalSchwartzPsi (η : ℝ) (hη : 0 < η) (x : ℝ) : SchwartzMap ℝ ℂ :=
  horizontalSchwartzPsi (2 * Real.pi * η) (by positivity) (2 * Real.pi * x)

private theorem tendsto_weightedDerivToBCFCLM_horizontalSchwartzPsi_diff_zero
    (η x : ℝ) (hη : 0 < η) (k n : ℕ) :
    Tendsto
      (fun h : ℝ =>
        ‖weightedDerivToBCFCLM k n
          (horizontalSchwartzPsi η hη (x + h) - horizontalSchwartzPsi η hη x)‖)
      (nhds 0) (nhds 0) := by
  simpa [horizontalSchwartzPsi] using
    tendsto_weightedDerivToBCFCLM_schwartzPsiZ_horizontal_diff_zero η x hη k n

set_option maxHeartbeats 800000 in
private theorem continuous_weightedDerivToBCFCLM_schwartzPsiZ_horizontal
    (η : ℝ) (hη : 0 < η) (k n : ℕ) :
    Continuous (fun x : ℝ =>
      weightedDerivToBCFCLM k n (horizontalSchwartzPsi η hη x)) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [Metric.continuousAt_iff]
  intro ε hε
  have htendsto :=
    tendsto_weightedDerivToBCFCLM_horizontalSchwartzPsi_diff_zero η x hη k n
  have ht : ∀ᶠ h in 𝓝 (0 : ℝ),
      dist
        ‖weightedDerivToBCFCLM k n
          (horizontalSchwartzPsi η hη (x + h) - horizontalSchwartzPsi η hη x)‖
        0 < ε :=
    (Metric.tendsto_nhds.1 htendsto) ε hε
  rcases Metric.mem_nhds_iff.1 ht with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro y hy
  have hy' : y - x ∈ ball (0 : ℝ) δ := by
    simpa [Real.dist_eq, sub_eq_add_neg] using hy
  have hmain := hδ hy'
  simpa [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hmain

private theorem weightedDerivToBCFCLM_schwartzPsiZ_horizontal_growth
    (η : ℝ) (hη : 0 < η) (k n : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ,
      ‖weightedDerivToBCFCLM k n
          (horizontalSchwartzPsi η hη x)‖ ≤ D * (1 + |x|) ^ n := by
  obtain ⟨D0, hD0_nonneg, hD0⟩ := schwartzPsiZ_seminorm_horizontal_bound η hη 0 n
  obtain ⟨D2, hD2_nonneg, hD2⟩ := schwartzPsiZ_seminorm_horizontal_bound η hη (2 * k) n
  refine ⟨(2 : ℝ) ^ k * (D0 + D2), by positivity, ?_⟩
  intro x
  calc
    ‖weightedDerivToBCFCLM k n
        (horizontalSchwartzPsi η hη x)‖
        ≤ (2 : ℝ) ^ k *
            (SchwartzMap.seminorm ℝ 0 n
                (horizontalSchwartzPsi η hη x) +
              SchwartzMap.seminorm ℝ (2 * k) n
                (horizontalSchwartzPsi η hη x)) := by
            exact weightedDerivToBCFCLM_norm_le k n _
    _ ≤ (2 : ℝ) ^ k * (D0 * (1 + |x|) ^ n + D2 * (1 + |x|) ^ n) := by
          gcongr
          · exact hD0 x
          · exact hD2 x
    _ = ((2 : ℝ) ^ k * (D0 + D2)) * (1 + |x|) ^ n := by ring

private theorem one_add_abs_two_pi_mul_rpow_le (n : ℕ) (x : ℝ) :
    (1 + |2 * Real.pi * x|) ^ n ≤ (2 * Real.pi) ^ n * (1 + |x|) ^ n := by
  have hbase : 1 + |2 * Real.pi * x| ≤ (2 * Real.pi) * (1 + |x|) := by
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < 2 * Real.pi by positivity)]
    nlinarith [Real.pi_gt_three, abs_nonneg x]
  calc
    (1 + |2 * Real.pi * x|) ^ n ≤ ((2 * Real.pi) * (1 + |x|)) ^ n := by
      exact pow_le_pow_left₀ (by positivity) hbase n
    _ = (2 * Real.pi) ^ n * (1 + |x|) ^ n := by rw [mul_pow]

private theorem continuous_weightedDerivToBCFCLM_scaledHorizontal
    (η : ℝ) (hη : 0 < η) (k n : ℕ) :
    Continuous (fun x : ℝ =>
      weightedDerivToBCFCLM k n (scaledHorizontalSchwartzPsi η hη x)) := by
  simpa [scaledHorizontalSchwartzPsi] using
    (continuous_weightedDerivToBCFCLM_schwartzPsiZ_horizontal
      (2 * Real.pi * η) (by positivity) k n).comp
      (continuous_const.mul continuous_id)

private theorem weightedDerivToBCFCLM_scaledHorizontal_growth
    (η : ℝ) (hη : 0 < η) (k n : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ,
      ‖weightedDerivToBCFCLM k n
          (scaledHorizontalSchwartzPsi η hη x)‖ ≤ D * (1 + |x|) ^ n := by
  obtain ⟨D0, hD0_nonneg, hD0⟩ :=
    weightedDerivToBCFCLM_schwartzPsiZ_horizontal_growth (2 * Real.pi * η) (by positivity) k n
  refine ⟨D0 * (2 * Real.pi) ^ n, by positivity, ?_⟩
  intro x
  calc
    ‖weightedDerivToBCFCLM k n (scaledHorizontalSchwartzPsi η hη x)‖
        = ‖weightedDerivToBCFCLM k n
            (horizontalSchwartzPsi (2 * Real.pi * η) (by positivity) (2 * Real.pi * x))‖ := rfl
    _ ≤ D0 * (1 + |2 * Real.pi * x|) ^ n := hD0 (2 * Real.pi * x)
    _ ≤ D0 * ((2 * Real.pi) ^ n * (1 + |x|) ^ n) := by
          gcongr
          exact one_add_abs_two_pi_mul_rpow_le n x
    _ = (D0 * (2 * Real.pi) ^ n) * (1 + |x|) ^ n := by ring

/-- Continuity in the Schwartz topology of the scaled horizontal `ψ_Z` family. -/
private theorem continuous_scaledHorizontalSchwartzPsi
    (η : ℝ) (hη : 0 < η) :
    Continuous (fun x : ℝ => scaledHorizontalSchwartzPsi η hη x) := by
  rw [continuous_iff_continuousAt]
  intro x
  change Tendsto (fun y : ℝ => scaledHorizontalSchwartzPsi η hη y) (nhds x)
    (nhds (scaledHorizontalSchwartzPsi η hη x))
  rw [(schwartz_withSeminorms ℂ ℝ ℂ).tendsto_nhds _ _]
  intro p ε hε
  have hcont :
      ContinuousAt
        (fun y : ℝ =>
          weightedDerivToBCFCLM p.1 p.2 (scaledHorizontalSchwartzPsi η hη y)) x :=
    (continuous_weightedDerivToBCFCLM_scaledHorizontal η hη p.1 p.2).continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδ_pos, hδ⟩ := hcont ε hε
  refine Filter.mem_of_superset (Metric.ball_mem_nhds x hδ_pos) ?_
  intro y hy
  have hdist := hδ hy
  have hnorm :
      ‖weightedDerivToBCFCLM p.1 p.2
          (scaledHorizontalSchwartzPsi η hη y - scaledHorizontalSchwartzPsi η hη x)‖ < ε := by
    simpa [dist_eq_norm, map_sub] using hdist
  exact lt_of_le_of_lt
    (schwartzSeminorm_le_probe_component_norm p.1 p.2
      (scaledHorizontalSchwartzPsi η hη y - scaledHorizontalSchwartzPsi η hη x))
    hnorm

/-- Public `2π`-scaled horizontal `ψ_Z` continuity package used by the
OS-route horizontal Fubini step. -/
theorem continuous_schwartzPsiZ_twoPi_horizontal
    {η : ℝ} (hη : 0 < η) :
    Continuous
      (fun x : ℝ =>
        schwartzPsiZ
          ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + η * Complex.I)))
          (by
            have hscaled : 0 < (2 * Real.pi) *
                (((x : ℂ) + η * Complex.I).im) :=
              mul_pos Real.two_pi_pos (by simpa using hη)
            simpa [Complex.mul_im] using hscaled)) := by
  have hfun :
      (fun x : ℝ =>
        schwartzPsiZ
          ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + η * Complex.I)))
          (by
            have hscaled : 0 < (2 * Real.pi) *
                (((x : ℂ) + η * Complex.I).im) :=
              mul_pos Real.two_pi_pos (by simpa using hη)
            simpa [Complex.mul_im] using hscaled)) =
      (fun x : ℝ => scaledHorizontalSchwartzPsi η hη x) := by
    funext x
    ext ξ
    simp [scaledHorizontalSchwartzPsi, horizontalSchwartzPsi, schwartzPsiZ_apply]
    ring_nf
  rw [hfun]
  exact continuous_scaledHorizontalSchwartzPsi η hη

private theorem funUnique_abs_le_norm
    (x1 : Fin 1 → ℝ) :
    |(ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ) x1| ≤ ‖x1‖ := by
  simpa [Real.norm_eq_abs] using (norm_le_pi_norm (f := x1) (i := (0 : Fin 1)))

/-- `Fin 1` reindexed Fourier-transform horizontal `ψ_Z` family continuity. -/
theorem continuous_fin1_reindexed_fourierTransform_schwartzPsiZ_horizontal
    {ε : ℝ} (hε : 0 < ε) :
    Continuous
      (fun x1 : Fin 1 → ℝ =>
        let e1 : (Fin 1 → ℝ) ≃L[ℝ] ℝ :=
          ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ
        let toFin1 : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap (Fin 1 → ℝ) ℂ :=
          SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e1
        toFin1
          ((SchwartzMap.fourierTransformCLM ℂ)
            (schwartzPsiZ
              ((((2 * Real.pi : ℝ) : ℂ) * ((e1 x1 : ℂ) + ε * Complex.I)))
              (by
                have hscaled : 0 < (2 * Real.pi) *
                    (((e1 x1 : ℂ) + ε * Complex.I).im) :=
                  mul_pos Real.two_pi_pos (by simpa using hε)
                simpa [Complex.mul_im] using hscaled)))) := by
  let e1 : (Fin 1 → ℝ) ≃L[ℝ] ℝ :=
    ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ
  let toFin1 : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap (Fin 1 → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e1
  let L : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap (Fin 1 → ℝ) ℂ :=
    toFin1.comp (SchwartzMap.fourierTransformCLM ℂ)
  have hcont :
      Continuous (fun x1 : Fin 1 → ℝ =>
        L
          (schwartzPsiZ
            ((((2 * Real.pi : ℝ) : ℂ) * ((e1 x1 : ℂ) + ε * Complex.I)))
            (by
              have hscaled : 0 < (2 * Real.pi) *
                  (((e1 x1 : ℂ) + ε * Complex.I).im) :=
                mul_pos Real.two_pi_pos (by simpa using hε)
              simpa [Complex.mul_im] using hscaled))) :=
    L.continuous.comp
      ((continuous_schwartzPsiZ_twoPi_horizontal hε).comp e1.continuous)
  simpa [L, toFin1, e1] using hcont

/-- Polynomial seminorm growth of the `Fin 1` reindexed Fourier-transform
horizontal `ψ_Z` family. -/
theorem seminorm_fin1_reindexed_fourierTransform_schwartzPsiZ_horizontal_growth
    {ε : ℝ} (hε : 0 < ε) :
    ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
      ∀ (x1 : Fin 1 → ℝ),
        SchwartzMap.seminorm ℝ k n
          (let e1 : (Fin 1 → ℝ) ≃L[ℝ] ℝ :=
            ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ
           let toFin1 : SchwartzMap ℝ ℂ →L[ℂ]
                SchwartzMap (Fin 1 → ℝ) ℂ :=
            SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e1
           toFin1
            ((SchwartzMap.fourierTransformCLM ℂ)
              (schwartzPsiZ
                ((((2 * Real.pi : ℝ) : ℂ) * ((e1 x1 : ℂ) + ε * Complex.I)))
                (by
                  have hscaled : 0 < (2 * Real.pi) *
                      (((e1 x1 : ℂ) + ε * Complex.I).im) :=
                    mul_pos Real.two_pi_pos (by simpa using hε)
                  simpa [Complex.mul_im] using hscaled)))) ≤
          C * (1 + ‖x1‖) ^ N := by
  classical
  intro k n
  let e1 : (Fin 1 → ℝ) ≃L[ℝ] ℝ :=
    ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ
  let toFin1 : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap (Fin 1 → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e1
  let L : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap (Fin 1 → ℝ) ℂ :=
    toFin1.comp (SchwartzMap.fourierTransformCLM ℂ)
  let q : Seminorm ℂ (SchwartzMap ℝ ℂ) :=
    (schwartzSeminormFamily ℂ (Fin 1 → ℝ) ℂ (k, n)).comp L.toLinearMap
  have hq_cont : Continuous q := by
    change Continuous (fun φ : SchwartzMap ℝ ℂ =>
      schwartzSeminormFamily ℂ (Fin 1 → ℝ) ℂ (k, n) (L φ))
    exact
      ((schwartz_withSeminorms ℂ (Fin 1 → ℝ) ℂ).continuous_seminorm
        (k, n)).comp L.continuous
  obtain ⟨s, D, hD_ne, hq_bound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ ℝ ℂ) q hq_cont
  have hD_pos : 0 < (D : ℝ) := by
    exact lt_of_le_of_ne D.2 (by exact_mod_cast hD_ne.symm)
  have hB :
      ∀ p : ℕ × ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ x1 : Fin 1 → ℝ,
        schwartzSeminormFamily ℂ ℝ ℂ p
          (schwartzPsiZ
            ((((2 * Real.pi : ℝ) : ℂ) * ((e1 x1 : ℂ) + ε * Complex.I)))
            (by
              have hscaled : 0 < (2 * Real.pi) *
                  (((e1 x1 : ℂ) + ε * Complex.I).im) :=
                mul_pos Real.two_pi_pos (by simpa using hε)
              simpa [Complex.mul_im] using hscaled)) ≤
            B * (1 + ‖x1‖) ^ p.2 := by
    intro p
    obtain ⟨B0, hB0_nonneg, hB0_bound⟩ :=
      schwartzPsiZ_seminorm_horizontal_bound (2 * Real.pi * ε) (by positivity) p.1 p.2
    refine ⟨B0 * (2 * Real.pi) ^ p.2, by positivity, ?_⟩
    intro x1
    have hscale :
        1 + |2 * Real.pi * e1 x1| ≤ (2 * Real.pi) * (1 + ‖x1‖) := by
      rw [abs_mul, abs_of_pos (show (0 : ℝ) < 2 * Real.pi by positivity)]
      have hfun := funUnique_abs_le_norm x1
      nlinarith [Real.pi_gt_three, hfun, norm_nonneg x1]
    have hpow :
        (1 + |2 * Real.pi * e1 x1|) ^ p.2 ≤
          ((2 * Real.pi) * (1 + ‖x1‖)) ^ p.2 := by
      exact pow_le_pow_left₀ (by positivity) hscale p.2
    calc
      schwartzSeminormFamily ℂ ℝ ℂ p
          (schwartzPsiZ
            ((((2 * Real.pi : ℝ) : ℂ) * ((e1 x1 : ℂ) + ε * Complex.I)))
            (by
              have hscaled : 0 < (2 * Real.pi) *
                  (((e1 x1 : ℂ) + ε * Complex.I).im) :=
                mul_pos Real.two_pi_pos (by simpa using hε)
              simpa [Complex.mul_im] using hscaled))
          =
        schwartzSeminormFamily ℂ ℝ ℂ p
          (horizontalSchwartzPsi (2 * Real.pi * ε) (by positivity) (2 * Real.pi * e1 x1)) := by
            congr 1
            ext ξ
            simp [horizontalSchwartzPsi, schwartzPsiZ_apply]
            ring_nf
      _ ≤ B0 * (1 + |2 * Real.pi * e1 x1|) ^ p.2 :=
            by simpa [horizontalSchwartzPsi] using hB0_bound (2 * Real.pi * e1 x1)
      _ ≤ B0 * (((2 * Real.pi) * (1 + ‖x1‖)) ^ p.2) := by
            gcongr
      _ = (B0 * (2 * Real.pi) ^ p.2) * (1 + ‖x1‖) ^ p.2 := by
            rw [mul_pow]
            ring
  choose B hB_nonneg hB_bound using hB
  let N : ℕ := s.sup Prod.snd
  let Bsum : ℝ := ∑ p ∈ s, B p
  let C : ℝ := (D : ℝ) * Bsum + 1
  have hBsum_nonneg : 0 ≤ Bsum := by
    dsimp [Bsum]
    refine Finset.sum_nonneg ?_
    intro p hp
    exact hB_nonneg p
  refine ⟨C, N, by
    dsimp [C]
    nlinarith [show 0 < (D : ℝ) from hD_pos], ?_⟩
  intro x1
  let ψx : SchwartzMap ℝ ℂ :=
    schwartzPsiZ
      ((((2 * Real.pi : ℝ) : ℂ) * ((e1 x1 : ℂ) + ε * Complex.I)))
      (by
        have hscaled : 0 < (2 * Real.pi) *
            (((e1 x1 : ℂ) + ε * Complex.I).im) :=
          mul_pos Real.two_pi_pos (by simpa using hε)
        simpa [Complex.mul_im] using hscaled)
  let u : ℝ := 1 + ‖x1‖
  have hu_nonneg : 0 ≤ u := by
    dsimp [u]
    positivity
  have hu_ge_one : 1 ≤ u := by
    dsimp [u]
    have hx : 0 ≤ ‖x1‖ := norm_nonneg x1
    linarith
  have hsum_apply :
      ∀ s' : Finset (ℕ × ℕ),
        (∑ p ∈ s', schwartzSeminormFamily ℂ ℝ ℂ p) ψx =
          ∑ p ∈ s', schwartzSeminormFamily ℂ ℝ ℂ p ψx := by
    intro s'
    induction s' using Finset.induction with
    | empty =>
        simp
    | insert a s' ha ih =>
        simp [Finset.sum_insert, ha, ih]
  have hsum_bound :
      (∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p) ψx ≤ Bsum * u ^ N := by
    calc
      (∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p) ψx
          = ∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p ψx := by
              simpa using hsum_apply s
      _ ≤ ∑ p ∈ s, B p * u ^ N := by
            refine Finset.sum_le_sum ?_
            intro p hp
            have hpN : p.2 ≤ N := Finset.le_sup hp
            calc
              schwartzSeminormFamily ℂ ℝ ℂ p ψx
                  ≤ B p * u ^ p.2 := hB_bound p x1
              _ ≤ B p * u ^ N := by
                    refine mul_le_mul_of_nonneg_left ?_ (hB_nonneg p)
                    exact pow_le_pow_right₀ hu_ge_one hpN
      _ = Bsum * u ^ N := by
            simp [Bsum, Finset.sum_mul]
  have hL_bound : SchwartzMap.seminorm ℝ k n (L ψx) ≤ (D : ℝ) * (Bsum * u ^ N) := by
    calc
      SchwartzMap.seminorm ℝ k n (L ψx) = q ψx := by
        rfl
      _ ≤ (D • s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) ψx := hq_bound ψx
      _ = (D : ℝ) * (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) ψx := by
            rfl
      _ ≤ (D : ℝ) * ((∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p) ψx) := by
            gcongr
            exact Seminorm.le_def.mp
              (Seminorm.finset_sup_le_sum (schwartzSeminormFamily ℂ ℝ ℂ) s) ψx
      _ ≤ (D : ℝ) * (Bsum * u ^ N) := by
            gcongr
  calc
    SchwartzMap.seminorm ℝ k n
      (let e1 : (Fin 1 → ℝ) ≃L[ℝ] ℝ :=
        ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ
       let toFin1 : SchwartzMap ℝ ℂ →L[ℂ]
            SchwartzMap (Fin 1 → ℝ) ℂ :=
        SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e1
       toFin1
        ((SchwartzMap.fourierTransformCLM ℂ)
          (schwartzPsiZ
            ((((2 * Real.pi : ℝ) : ℂ) * ((e1 x1 : ℂ) + ε * Complex.I)))
            (by
              have hscaled : 0 < (2 * Real.pi) *
                  (((e1 x1 : ℂ) + ε * Complex.I).im) :=
                mul_pos Real.two_pi_pos (by simpa using hε)
              simpa [Complex.mul_im] using hscaled))))
        = SchwartzMap.seminorm ℝ k n (L ψx) := by
            simp [L, toFin1, e1, ψx]
    _ ≤ (D : ℝ) * (Bsum * u ^ N) := hL_bound
    _ ≤ C * u ^ N := by
          have hCu : (D : ℝ) * (Bsum * u ^ N) ≤ ((D : ℝ) * Bsum + 1) * u ^ N := by
            have hu_pow_ge_one : 1 ≤ u ^ N := by
              exact pow_le_pow_right₀ hu_ge_one (Nat.zero_le _)
            nlinarith [hBsum_nonneg, show 0 < (D : ℝ) from hD_pos]
          simpa [C, u, mul_assoc, mul_left_comm, mul_comm] using hCu

private theorem integrable_one_add_abs_rpow_mul_norm
    (φ : SchwartzMap ℝ ℂ) (n : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|) ^ n * ‖φ x‖) := by
  have h_norm_int : Integrable (fun x : ℝ => ‖φ x‖) :=
    (φ.integrable).norm
  have h_pow_int : Integrable (fun x : ℝ => |x| ^ n * ‖φ x‖) :=
    φ.integrable_pow_mul volume n
  have h_sum : Integrable (fun x : ℝ => (2 : ℝ) ^ n * (‖φ x‖ + |x| ^ n * ‖φ x‖)) :=
    (h_norm_int.add h_pow_int).const_mul _
  have h_bound : ∀ x : ℝ,
      ‖(1 + |x|) ^ n * ‖φ x‖‖ ≤ (2 : ℝ) ^ n * (‖φ x‖ + |x| ^ n * ‖φ x‖) := by
    intro x
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (by positivity : 0 ≤ 1 + |x|) n) (norm_nonneg _))]
    have hpow : (1 + |x|) ^ n ≤ (2 : ℝ) ^ n * (1 + |x| ^ n) := by
      calc
        (1 + |x|) ^ n ≤ (2 * max 1 |x|) ^ n := by
          apply pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |x|)
          calc
            1 + |x| ≤ max 1 |x| + max 1 |x| :=
              add_le_add (le_max_left 1 |x|) (le_max_right 1 |x|)
            _ = 2 * max 1 |x| := by ring
        _ = (2 : ℝ) ^ n * (max 1 |x|) ^ n := by rw [mul_pow]
        _ ≤ (2 : ℝ) ^ n * (1 + |x| ^ n) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            by_cases hx : (1 : ℝ) ≤ |x|
            · simp [max_eq_right hx]
            · push_neg at hx
              simp [max_eq_left hx.le]
    calc
      (1 + |x|) ^ n * ‖φ x‖ ≤ (2 : ℝ) ^ n * (1 + |x| ^ n) * ‖φ x‖ := by
        exact mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ = (2 : ℝ) ^ n * (‖φ x‖ + |x| ^ n * ‖φ x‖) := by ring
  exact h_sum.mono'
    ((((continuous_const.add (continuous_abs.comp continuous_id)).pow n).mul
      φ.continuous.norm).aestronglyMeasurable)
    (Filter.Eventually.of_forall h_bound)

/-- A continuous line function with polynomial growth pairs integrably against a
Schwartz test. This is the basic analytic bound later used for the Stage-5
contour pairings: once the line factor is only polynomially large, Schwartz
decay makes the real-line pairing honest. -/
theorem integrable_mul_of_continuous_polynomialGrowthOnLine
    (f : ℝ → ℂ)
    (hf_cont : Continuous f)
    (hf_growth : HasPolynomialGrowthOnLine f)
    (φ : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => f x * φ x) := by
  rcases hf_growth with ⟨C, N, hC_pos, hbound⟩
  refine Integrable.mono'
    ((integrable_one_add_abs_rpow_mul_norm φ N).const_mul C)
    (hf_cont.mul φ.continuous).aestronglyMeasurable
    ?_
  filter_upwards with x
  calc
    ‖f x * φ x‖ = ‖f x‖ * ‖φ x‖ := norm_mul _ _
    _ ≤ (C * (1 + |x|) ^ N) * ‖φ x‖ := by
          gcongr
          exact hbound x
    _ = C * ((1 + |x|) ^ N * ‖φ x‖) := by ring

/-- Fourier-transform specialization of
`integrable_mul_of_continuous_polynomialGrowthOnLine`: a polynomial-growth line
function pairs integrably with the Fourier transform of any Schwartz test. This
is the exact real-line integrability form used by the current Stage-5
`hzero`/boundary-value contour route. -/
theorem integrable_mul_fourierTransform_of_continuous_polynomialGrowthOnLine
    (f : ℝ → ℂ)
    (hf_cont : Continuous f)
    (hf_growth : HasPolynomialGrowthOnLine f)
    (φ : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => f x * (SchwartzMap.fourierTransformCLM ℂ φ) x) := by
  exact integrable_mul_of_continuous_polynomialGrowthOnLine
    f hf_cont hf_growth ((SchwartzMap.fourierTransformCLM ℂ) φ)

private def stepAProbeFamily
    (s : Finset (ℕ × ℕ)) (η : ℝ) (hη : 0 < η) (φ : SchwartzMap ℝ ℂ) :
    ℝ → ((p : ↑s.attach) → (ℝ →ᵇ ℂ)) :=
  fun x => probeCLM s (φ x • scaledHorizontalSchwartzPsi η hη x)

private theorem continuous_stepAProbeFamily_component
    (s : Finset (ℕ × ℕ)) (η : ℝ) (hη : 0 < η) (φ : SchwartzMap ℝ ℂ)
    (p : ↑s.attach) :
    Continuous (fun x : ℝ => stepAProbeFamily s η hη φ x p) := by
  have hφ : Continuous fun x : ℝ => φ x := φ.continuous
  have hψ : Continuous fun x : ℝ =>
      weightedDerivToBCFCLM p.1.1.1 p.1.1.2
        (scaledHorizontalSchwartzPsi η hη x) :=
    continuous_weightedDerivToBCFCLM_scaledHorizontal η hη p.1.1.1 p.1.1.2
  simpa [stepAProbeFamily, probeCLM, map_smul] using hφ.smul hψ

private theorem integrable_stepAProbeFamily_component
    (s : Finset (ℕ × ℕ)) (η : ℝ) (hη : 0 < η) (φ : SchwartzMap ℝ ℂ)
    (p : ↑s.attach) :
    Integrable (fun x : ℝ => stepAProbeFamily s η hη φ x p) := by
  obtain ⟨D, hD_nonneg, hD⟩ :=
    weightedDerivToBCFCLM_scaledHorizontal_growth η hη p.1.1.1 p.1.1.2
  refine Integrable.mono' (((integrable_one_add_abs_rpow_mul_norm φ p.1.1.2).const_mul D))
    (continuous_stepAProbeFamily_component s η hη φ p).aestronglyMeasurable ?_
  filter_upwards with x
  calc
    ‖stepAProbeFamily s η hη φ x p‖
        = ‖φ x‖ *
          ‖weightedDerivToBCFCLM p.1.1.1 p.1.1.2
              (scaledHorizontalSchwartzPsi η hη x)‖ := by
              simp [stepAProbeFamily, probeCLM, norm_smul]
    _ ≤ ‖φ x‖ * (D * (1 + |x|) ^ p.1.1.2) := by
          gcongr
          exact hD x
    _ = D * ((1 + |x|) ^ p.1.1.2 * ‖φ x‖) := by ring

private theorem integrable_stepAProbeFamily
    (s : Finset (ℕ × ℕ)) (η : ℝ) (hη : 0 < η) (φ : SchwartzMap ℝ ℂ) :
    Integrable (stepAProbeFamily s η hη φ) := by
  exact Integrable.of_eval fun p => integrable_stepAProbeFamily_component s η hη φ p

private theorem schwartzFunctional_bound_by_probeNorm
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : NNReal, C ≠ 0 ∧
      ∀ f : SchwartzMap ℝ ℂ,
        ‖T f‖ ≤ (C : ℝ) * ‖(probeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ)))‖ := by
  classical
  obtain ⟨s, C0, hC0, hbound⟩ := schwartz_functional_bound T
  refine ⟨s, C0 * (s.card + 1), by
    refine mul_ne_zero hC0 ?_
    exact_mod_cast Nat.succ_ne_zero s.card, ?_⟩
  intro f
  have hsup_sum :
      (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f ≤
        (∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p) f := by
    exact Seminorm.le_def.mp (Seminorm.finset_sup_le_sum (schwartzSeminormFamily ℂ ℝ ℂ) s) f
  have hsum_apply_all :
      ∀ s' : Finset (ℕ × ℕ),
        (∑ p ∈ s', schwartzSeminormFamily ℂ ℝ ℂ p) f =
          ∑ p ∈ s', schwartzSeminormFamily ℂ ℝ ℂ p f := by
    intro s'
    induction s' using Finset.induction with
    | empty =>
        simp
    | insert a s' ha ih =>
        simp [Finset.sum_insert, ha, ih]
  have hsum_apply :
      (∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p) f =
        ∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p f := hsum_apply_all s
  have hsum_probe :
      ∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p f ≤
        s.card * ‖(probeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ)))‖ := by
    calc
      ∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p f
          ≤ ∑ _p ∈ s, ‖(probeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ)))‖ := by
              refine Finset.sum_le_sum ?_
              intro a ha
              let p : ↑s.attach := ⟨⟨a, ha⟩, by simp⟩
              simpa [schwartzSeminormFamily, p] using schwartzSeminorm_le_probe_norm s p f
      _ = s.card * ‖(probeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ)))‖ := by
            simp
  calc
    ‖T f‖ ≤ (C0 • s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := hbound f
    _ = (C0 : ℝ) * (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by rfl
    _ ≤ (C0 : ℝ) * ((∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p) f) := by
      exact mul_le_mul_of_nonneg_left hsup_sum C0.coe_nonneg
    _ = (C0 : ℝ) * (∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p f) := by rw [hsum_apply]
    _ ≤ (C0 : ℝ) * (s.card * ‖(probeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ)))‖) := by
      exact mul_le_mul_of_nonneg_left hsum_probe C0.coe_nonneg
    _ ≤ (C0 : ℝ) * ((s.card + 1 : ℝ) * ‖(probeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ)))‖) := by
      have hcard : (s.card : ℝ) ≤ s.card + 1 := by exact_mod_cast Nat.le_succ s.card
      have hnorm := norm_nonneg (probeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ)))
      have hcardnorm :
          (s.card : ℝ) * ‖(probeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ)))‖ ≤
            (s.card + 1 : ℝ) * ‖(probeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ)))‖ := by
        exact mul_le_mul_of_nonneg_right hcard hnorm
      exact mul_le_mul_of_nonneg_left hcardnorm C0.coe_nonneg
    _ = ((C0 * (s.card + 1) : NNReal) : ℝ) * ‖(probeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ)))‖ := by
      rw [NNReal.coe_mul]
      norm_num
      ring

private noncomputable def rangeLiftLinear
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (s : Finset (ℕ × ℕ))
    (hker : LinearMap.ker (probeCLM s).toLinearMap ≤ LinearMap.ker T.toLinearMap) :
    LinearMap.range (probeCLM s).toLinearMap →ₗ[ℂ] ℂ :=
  ((LinearMap.ker (probeCLM s).toLinearMap).liftQ T.toLinearMap hker).comp
    ((probeCLM s).toLinearMap.quotKerEquivRange.symm.toLinearMap)

private theorem rangeLiftLinear_apply
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (s : Finset (ℕ × ℕ))
    (hker : LinearMap.ker (probeCLM s).toLinearMap ≤ LinearMap.ker T.toLinearMap)
    (f : SchwartzMap ℝ ℂ) :
    rangeLiftLinear T s hker ⟨probeCLM s f, LinearMap.mem_range_self _ f⟩ = T f := by
  change
    ((LinearMap.ker (probeCLM s).toLinearMap).liftQ T.toLinearMap hker)
        (((probeCLM s).toLinearMap.quotKerEquivRange.symm)
          ⟨probeCLM s f, LinearMap.mem_range_self _ f⟩) = T f
  have hsymm :
      ((probeCLM s).toLinearMap.quotKerEquivRange.symm)
          ⟨probeCLM s f, LinearMap.mem_range_self _ f⟩ =
        (LinearMap.ker (probeCLM s).toLinearMap).mkQ f := by
    simpa using
      (LinearMap.quotKerEquivRange_symm_apply_image ((probeCLM s).toLinearMap) f
        (LinearMap.mem_range_self _ f))
  rw [hsymm]
  simp

private theorem rangeLiftLinear_bound
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (s : Finset (ℕ × ℕ))
    (C : NNReal)
    (hbound : ∀ f : SchwartzMap ℝ ℂ,
      ‖T f‖ ≤ (C : ℝ) * ‖(probeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ)))‖)
    (hker : LinearMap.ker (probeCLM s).toLinearMap ≤ LinearMap.ker T.toLinearMap) :
    ∀ y, ‖rangeLiftLinear T s hker y‖ ≤ (C : ℝ) * ‖y‖ := by
  intro y
  rcases y with ⟨y, hy⟩
  rcases hy with ⟨f, rfl⟩
  simpa [rangeLiftLinear_apply] using hbound f

/-- Any continuous Schwartz functional factors through finitely many weighted-derivative
probes landing in a Banach space. This is the replacement for the unavailable
Bochner integral on `SchwartzMap ℝ ℂ`: Step A of `paley_wiener_half_line` can instead
be performed after passing through this finite probe space and using ordinary Banach-valued
integration there. -/
private theorem exists_probe_factorization
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ) :
    ∃ s : Finset (ℕ × ℕ), ∃ G : ((p : ↑s.attach) → (ℝ →ᵇ ℂ)) →L[ℂ] ℂ,
      T = G.comp (probeCLM s) := by
  classical
  obtain ⟨s, C, hC, hbound⟩ := schwartzFunctional_bound_by_probeNorm T
  have hker : LinearMap.ker (probeCLM s).toLinearMap ≤ LinearMap.ker T.toLinearMap := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    apply norm_eq_zero.mp
    apply le_antisymm
    · calc
        ‖T f‖ ≤ (C : ℝ) * ‖(probeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ)))‖ := hbound f
        _ = 0 := by
          have hfnorm : ‖(probeCLM s f : (↑s.attach → (ℝ →ᵇ ℂ)))‖ = 0 := by
            simpa using congrArg norm hf
          rw [hfnorm, mul_zero]
    · exact norm_nonneg _
  let FrangeLin :
      LinearMap.range (probeCLM s).toLinearMap →ₗ[ℂ] ℂ :=
    rangeLiftLinear T s hker
  let Frange :
      StrongDual ℂ (LinearMap.range (probeCLM s).toLinearMap) :=
    FrangeLin.mkContinuous (C : ℝ) (rangeLiftLinear_bound T s C hbound hker)
  obtain ⟨G, hGext, _⟩ := exists_extension_norm_eq (LinearMap.range (probeCLM s).toLinearMap) Frange
  refine ⟨s, G, ?_⟩
  ext f
  have hmem : probeCLM s f ∈ LinearMap.range (probeCLM s).toLinearMap :=
    LinearMap.mem_range_self _ f
  change T f = G (probeCLM s f)
  calc
    T f = FrangeLin ⟨probeCLM s f, hmem⟩ := by
      exact (rangeLiftLinear_apply T s hker f).symm
    _ = Frange ⟨probeCLM s f, hmem⟩ := by
      rfl
    _ = G (probeCLM s f) := by
      symm
      exact hGext ⟨probeCLM s f, hmem⟩

/-- A continuous linear functional on Schwartz space grows at most polynomially on the
    horizontal-line test family `x ↦ ψ_{x+iη}`. -/
theorem schwartz_functional_horizontal_growth
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (η : ℝ) (hη : 0 < η) :
    HasPolynomialGrowthOnLine
      (fun x => T (schwartzPsiZ ((x : ℂ) + η * I) (by simpa using hη))) := by
  classical
  obtain ⟨s, C, hC, hbound⟩ := schwartz_functional_bound T
  have hD :
      ∀ p : ℕ × ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ,
        SchwartzMap.seminorm ℝ p.1 p.2
          (schwartzPsiZ ((x : ℂ) + η * I) (by simpa using hη)) ≤
            D * (1 + |x|) ^ p.2 := by
    intro p
    obtain ⟨D, hD_nonneg, hD_bound⟩ := schwartzPsiZ_seminorm_horizontal_bound η hη p.1 p.2
    exact ⟨D, hD_nonneg, hD_bound⟩
  choose D hD_nonneg hD_bound using hD
  let N : ℕ := s.sup Prod.snd
  let Dsum : ℝ := ∑ p ∈ s, D p
  let Cbound : ℝ := (C : ℝ) * Dsum + 1
  have hDsum_nonneg : 0 ≤ Dsum := by
    dsimp [Dsum]
    refine Finset.sum_nonneg ?_
    intro p hp
    exact hD_nonneg p
  have hC_coe_ne : (C : ℝ) ≠ 0 := by
    exact_mod_cast hC
  have hC_pos : 0 < (C : ℝ) := by
    exact lt_of_le_of_ne C.2 hC_coe_ne.symm
  refine ⟨Cbound, N, by
    dsimp [Cbound]
    nlinarith, ?_⟩
  intro x
  let ψx : SchwartzMap ℝ ℂ := schwartzPsiZ ((x : ℂ) + η * I) (by simpa using hη)
  let u : ℝ := 1 + |x|
  have hu_nonneg : 0 ≤ u := by
    have hx : 0 ≤ |x| := abs_nonneg x
    linarith
  have hu_ge_one : 1 ≤ u := by
    have hx : 0 ≤ |x| := abs_nonneg x
    linarith
  have hsup_sum :
      (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) ψx ≤
        (∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p) ψx := by
    exact Seminorm.le_def.mp (Seminorm.finset_sup_le_sum (schwartzSeminormFamily ℂ ℝ ℂ) s) ψx
  have hsum_apply :
      ∀ s' : Finset (ℕ × ℕ),
        (∑ p ∈ s', schwartzSeminormFamily ℂ ℝ ℂ p) ψx =
          ∑ p ∈ s', schwartzSeminormFamily ℂ ℝ ℂ p ψx := by
    intro s'
    induction s' using Finset.induction with
    | empty =>
        simp
    | insert a s' ha ih =>
        simp [Finset.sum_insert, ha, ih]
  have hsum_bound :
      (∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p) ψx ≤ Dsum * u ^ N := by
    calc
      (∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p) ψx
          = ∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p ψx := by
              simpa using hsum_apply s
      _ 
          ≤ ∑ p ∈ s, D p * u ^ N := by
              refine Finset.sum_le_sum ?_
              intro p hp
              have hpN : p.2 ≤ N := Finset.le_sup hp
              calc
                schwartzSeminormFamily ℂ ℝ ℂ p ψx
                    ≤ D p * u ^ p.2 := hD_bound p x
                _ ≤ D p * u ^ N := by
                      refine mul_le_mul_of_nonneg_left ?_ (hD_nonneg p)
                      exact pow_le_pow_right₀ hu_ge_one hpN
      _ = Dsum * u ^ N := by
            simp [Dsum, Finset.sum_mul]
  have hT_bound : ‖T ψx‖ ≤ (C : ℝ) * (Dsum * u ^ N) := by
    calc
      ‖T ψx‖ ≤ (C • s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) ψx := hbound ψx
      _ = (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) ψx := by
            rfl
      _ ≤ (C : ℝ) * ((∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p) ψx) := by
            gcongr
      _ ≤ (C : ℝ) * (Dsum * u ^ N) := by
            gcongr
  calc
    ‖T ψx‖ ≤ (C : ℝ) * (Dsum * u ^ N) := hT_bound
    _ ≤ Cbound * u ^ N := by
          have hu_pow_nonneg : 0 ≤ u ^ N := pow_nonneg hu_nonneg _
          have hCu : (C : ℝ) * (Dsum * u ^ N) ≤ ((C : ℝ) * Dsum + 1) * u ^ N := by
            have hu_pow_ge_one : 1 ≤ u ^ N := by
              exact pow_le_pow_right₀ hu_ge_one (Nat.zero_le _)
            nlinarith
          simpa [Cbound, u, mul_assoc, mul_left_comm, mul_comm] using hCu

/-- Along a fixed horizontal line in the upper half-plane, the candidate
    Fourier-Laplace extension `z ↦ T(ℱ[ψ_z])` has polynomial growth. -/
theorem fourierLaplaceExt_horizontal_growth
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (η : ℝ) (hη : 0 < η) :
    HasPolynomialGrowthOnLine
      (fun x => fourierLaplaceExt T ((x : ℂ) + η * I) (by simpa using hη)) := by
  let S : SchwartzMap ℝ ℂ →L[ℂ] ℂ := T.comp (SchwartzMap.fourierTransformCLM ℂ)
  simpa [S, fourierLaplaceExt_eq] using
    schwartz_functional_horizontal_growth
      (T := S) η hη

/-- Along a fixed horizontal line, the candidate complex derivative kernel
    `T(ℱ[(I ξ) ψ_{x+iη}])` also has polynomial growth.

    This is the growth estimate needed for the derivative side of the
    Fourier-Laplace pairing once holomorphicity is proved at the Schwartz-topology
    level. -/
theorem fourierLaplaceExt_derivCandidate_horizontal_growth
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (η : ℝ) (hη : 0 < η) :
    HasPolynomialGrowthOnLine
      (fun x =>
        T ((SchwartzMap.fourierTransformCLM ℂ)
          ((SchwartzMap.smulLeftCLM ℂ (fun ξ : ℝ => I * (ξ : ℂ)))
            (schwartzPsiZ ((x : ℂ) + η * I) (by simpa using hη))))) := by
  let L : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
    (SchwartzMap.fourierTransformCLM ℂ).comp
      (SchwartzMap.smulLeftCLM ℂ (fun ξ : ℝ => I * (ξ : ℂ)))
  let S : SchwartzMap ℝ ℂ →L[ℂ] ℂ := T.comp L
  simpa [L, S] using schwartz_functional_horizontal_growth (T := S) η hη

/-- Applying `T ∘ ℱ` to the local remainder kernel preserves the uniform
    `O(‖h‖)` bound coming from the Schwartz seminorm estimates. -/
theorem fourierLaplaceExt_remainder_bound
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (z : ℂ) (hz : 0 < z.im) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (h : ℂ) (hh_im : ‖h‖ ≤ z.im / 2) (hh1 : ‖h‖ ≤ 1),
      ‖(T.comp (SchwartzMap.fourierTransformCLM ℂ))
          (schwartzPsiZExpTaylorLinearRemainderQuot z hz h hh_im hh1)‖ ≤
        K * ‖h‖ := by
  let S : SchwartzMap ℝ ℂ →L[ℂ] ℂ := T.comp (SchwartzMap.fourierTransformCLM ℂ)
  obtain ⟨s, C, hC, hbound⟩ := schwartz_functional_bound S
  have hD :
      ∀ p : ℕ × ℕ, ∃ D : ℝ, 0 ≤ D ∧
        ∀ (h : ℂ) (hh_im : ‖h‖ ≤ z.im / 2) (hh1 : ‖h‖ ≤ 1),
          SchwartzMap.seminorm ℝ p.1 p.2
            (schwartzPsiZExpTaylorLinearRemainderQuot z hz h hh_im hh1) ≤
              D * ‖h‖ := by
    intro p
    simpa using
      schwartzPsiZExpTaylorLinearRemainderQuot_seminorm_le z hz p.1 p.2
  choose D hD_nonneg hD_bound using hD
  let Dsum : ℝ := ∑ p ∈ s, D p
  let K : ℝ := (C : ℝ) * Dsum
  have hDsum_nonneg : 0 ≤ Dsum := by
    dsimp [Dsum]
    refine Finset.sum_nonneg ?_
    intro p hp
    exact hD_nonneg p
  have hC_pos : 0 < (C : ℝ) := by
    have hC_coe_ne : (C : ℝ) ≠ 0 := by
      exact_mod_cast hC
    exact lt_of_le_of_ne C.2 hC_coe_ne.symm
  refine ⟨K, mul_nonneg hC_pos.le hDsum_nonneg, ?_⟩
  intro h hh_im hh1
  let ψh : SchwartzMap ℝ ℂ :=
    schwartzPsiZExpTaylorLinearRemainderQuot z hz h hh_im hh1
  have hsup_sum :
      (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) ψh ≤
        (∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p) ψh := by
    exact Seminorm.le_def.mp
      (Seminorm.finset_sup_le_sum (schwartzSeminormFamily ℂ ℝ ℂ) s) ψh
  have hsum_apply :
      ∀ s' : Finset (ℕ × ℕ),
        (∑ p ∈ s', schwartzSeminormFamily ℂ ℝ ℂ p) ψh =
          ∑ p ∈ s', schwartzSeminormFamily ℂ ℝ ℂ p ψh := by
    intro s'
    induction s' using Finset.induction with
    | empty =>
        simp
    | insert a s' ha ih =>
        simp [Finset.sum_insert, ha, ih]
  have hsum_bound :
      (∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p) ψh ≤ Dsum * ‖h‖ := by
    calc
      (∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p) ψh
          = ∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p ψh := by
              simpa using hsum_apply s
      _ ≤ ∑ p ∈ s, D p * ‖h‖ := by
            refine Finset.sum_le_sum ?_
            intro p hp
            exact hD_bound p h hh_im hh1
      _ = Dsum * ‖h‖ := by
            simp [Dsum, Finset.sum_mul]
  calc
    ‖S ψh‖ ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) ψh := by
      simpa using hbound ψh
    _ ≤ (C : ℝ) * ((∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p) ψh) := by
          gcongr
    _ ≤ (C : ℝ) * (Dsum * ‖h‖) := by
          gcongr
    _ = K * ‖h‖ := by
          simp [K, Dsum, mul_assoc, mul_left_comm, mul_comm]

/-- The candidate Fourier-Laplace extension is holomorphic on the upper half-plane.

    This packages the scalar derivative argument: the kernel remainder is
    rewritten using `psiZ_sub_sub_deriv_eq_smul_remainder`, then the uniform
    `O(‖h‖)` bound from `fourierLaplaceExt_remainder_bound` upgrades it to an
    `O(‖h‖²)` scalar remainder. -/
theorem fourierLaplaceExt_hasDerivAt
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (z : ℂ) (hz : 0 < z.im) :
    HasDerivAt
      (fun w : ℂ =>
        if hw : 0 < w.im then
          fourierLaplaceExt T w hw
        else
          0)
      (T ((SchwartzMap.fourierTransformCLM ℂ)
        ((SchwartzMap.smulLeftCLM ℂ (fun ξ : ℝ => I * (ξ : ℂ)))
          (schwartzPsiZ z hz))))
      z := by
  let F : ℂ → ℂ := fun w =>
    if hw : 0 < w.im then
      fourierLaplaceExt T w hw
    else
      0
  let S : SchwartzMap ℝ ℂ →L[ℂ] ℂ := T.comp (SchwartzMap.fourierTransformCLM ℂ)
  let Dψ : SchwartzMap ℝ ℂ :=
    (SchwartzMap.smulLeftCLM ℂ (fun ξ : ℝ => I * (ξ : ℂ))) (schwartzPsiZ z hz)
  let D : ℂ := S Dψ
  obtain ⟨K, hK_nonneg, hKbound⟩ := fourierLaplaceExt_remainder_bound T z hz
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hsmall :
      ∀ᶠ h : ℂ in 𝓝 0, ‖h‖ ≤ z.im / 2 ∧ ‖h‖ ≤ 1 ∧ 0 < (z + h).im := by
    let r : ℝ := min (z.im / 2) 1
    have hr : 0 < r := by
      dsimp [r]
      positivity
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with h hh
    have hnorm_lt : ‖h‖ < r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hh
    have hh_im : ‖h‖ ≤ z.im / 2 := by
      exact le_trans hnorm_lt.le (min_le_left _ _)
    have hh1 : ‖h‖ ≤ 1 := by
      exact le_trans hnorm_lt.le (min_le_right _ _)
    have him_le : |h.im| ≤ ‖h‖ := by
      simpa using Complex.abs_im_le_norm h
    have him_lower : -‖h‖ ≤ h.im := by
      rw [abs_le] at him_le
      linarith
    have hzph : 0 < (z + h).im := by
      have hh_lt : ‖h‖ < z.im / 2 := lt_of_lt_of_le hnorm_lt (min_le_left _ _)
      simpa [Complex.add_im] using (show 0 < z.im + h.im by nlinarith [hz, hh_lt, him_lower])
    exact ⟨hh_im, hh1, hzph⟩
  have hbound :
      ∀ᶠ h : ℂ in 𝓝 0,
        ‖F (z + h) - F z - h * D‖ ≤ K * ‖h ^ 2‖ := by
    filter_upwards [hsmall] with h hh
    rcases hh with ⟨hh_im, hh1, hzph⟩
    let R : SchwartzMap ℝ ℂ := schwartzPsiZExpTaylorLinearRemainderQuot z hz h hh_im hh1
    have htemp : (fun ξ : ℝ => I * (ξ : ℂ)).HasTemperateGrowth := by
      fun_prop
    have hkernel :
        schwartzPsiZ (z + h) hzph - schwartzPsiZ z hz - h • Dψ = h • R := by
      ext ξ
      simpa [Dψ, R, schwartzPsiZ_apply, schwartzPsiZExpTaylorLinearRemainderQuot_apply,
        SchwartzMap.smulLeftCLM_apply_apply htemp, smul_eq_mul] using
        psiZ_sub_sub_deriv_eq_smul_remainder z h ξ
    have hEq :
        F (z + h) - F z - h * D = h * S R := by
      have hzph' : 0 < z.im + h.im := by
        simpa [Complex.add_im] using hzph
      have hF_add : F (z + h) = fourierLaplaceExt T (z + h) hzph := by
        simp [F, Complex.add_im, hzph']
      have hF_zero : F z = fourierLaplaceExt T z hz := by
        simp [F, hz]
      calc
        F (z + h) - F z - h * D
            = fourierLaplaceExt T (z + h) hzph - fourierLaplaceExt T z hz - h * D := by
                rw [hF_add, hF_zero]
        _ = S (schwartzPsiZ (z + h) hzph) - S (schwartzPsiZ z hz) - h * D := by
              simp [S, D, fourierLaplaceExt_eq]
        _ = S (schwartzPsiZ (z + h) hzph - schwartzPsiZ z hz - h • Dψ) := by
              simp [S, D, Dψ, map_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        _ = S (h • R) := by rw [hkernel]
        _ = h * S R := by
              simp [S]
    have hnorm_bound :
        ‖F (z + h) - F z - h * D‖ ≤ K * ‖h ^ 2‖ := by
      calc
        ‖F (z + h) - F z - h * D‖ = ‖h * S R‖ := by rw [hEq]
        _ = ‖h‖ * ‖S R‖ := by rw [norm_mul]
        _ ≤ ‖h‖ * (K * ‖h‖) := by
              exact mul_le_mul_of_nonneg_left (hKbound h hh_im hh1) (norm_nonneg h)
        _ = K * ‖h ^ 2‖ := by
              rw [norm_pow]
              ring
    exact hnorm_bound
  exact (Asymptotics.IsBigO.of_bound K hbound).trans_isLittleO
    (by simpa using (Asymptotics.isLittleO_pow_pow (𝕜 := ℂ) (m := 1) (n := 2) one_lt_two))

/-- The candidate Fourier-Laplace extension is differentiable on the upper half-plane. -/
theorem fourierLaplaceExt_differentiableOn
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ) :
    DifferentiableOn ℂ
      (fun w : ℂ =>
        if hw : 0 < w.im then
          fourierLaplaceExt T w hw
        else
          0)
      upperHalfPlane := by
  intro z hz
  exact (fourierLaplaceExt_hasDerivAt T z hz).differentiableAt.differentiableWithinAt

/-! ### Boundary-value damping estimates -/

private def expDampingFactor (η : ℝ) : ℝ → ℂ :=
  fun ξ => Complex.exp (-(η : ℂ) * ξ) - 1

private theorem expDampingFactor_exp_contDiff (η : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t : ℝ => Complex.exp (-(η : ℂ) * t)) := by
  let c : ℂ := -(η : ℂ)
  simpa [c, mul_comm] using
    (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff :
      ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t : ℝ => c * t)))

private theorem expDampingFactor_contDiff (η : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (expDampingFactor η) := by
  unfold expDampingFactor
  simpa using (expDampingFactor_exp_contDiff η).sub contDiff_const

private theorem norm_expDampingFactor_le_two_mul_eta_on_Icc
    {η ξ : ℝ} (hη_pos : 0 < η) (hη_le : η ≤ 1) (hξ : ξ ∈ Set.Icc (-1 : ℝ) 0) :
    ‖expDampingFactor η ξ‖ ≤ 2 * η := by
  rcases hξ with ⟨hξ_lo, hξ_hi⟩
  have hξη : |η * ξ| ≤ 1 := by
    calc
      |η * ξ| = |η| * |ξ| := by rw [abs_mul]
      _ ≤ η * |ξ| := by rw [abs_of_pos hη_pos]
      _ ≤ η * 1 := by
            gcongr
            have hξ_abs_le_one : |ξ| ≤ 1 := by
              rw [abs_le]
              constructor <;> linarith
            exact hξ_abs_le_one
      _ ≤ 1 := by simpa using hη_le
  have hnorm :
      ‖Complex.exp (-(η : ℂ) * ξ) - 1‖ ≤ 2 * ‖((-(η * ξ : ℝ)) : ℂ)‖ := by
    have hx : ‖((-(η * ξ : ℝ)) : ℂ)‖ ≤ 1 := by
      simpa [Real.norm_eq_abs] using hξη
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Complex.norm_exp_sub_one_le (x := ((-(η * ξ : ℝ)) : ℂ)) hx)
  calc
    ‖expDampingFactor η ξ‖ ≤ 2 * ‖((-(η * ξ : ℝ)) : ℂ)‖ := hnorm
    _ = 2 * |η * ξ| := by simp [Real.norm_eq_abs]
    _ ≤ 2 * η := by
          gcongr
          calc
            |η * ξ| = |η| * |ξ| := by rw [abs_mul]
            _ ≤ η * 1 := by
                  rw [abs_of_pos hη_pos]
                  gcongr
                  have hξ_abs_le_one : |ξ| ≤ 1 := by
                    rw [abs_le]
                    constructor <;> linarith
                  exact hξ_abs_le_one
            _ = η := by ring

private theorem iteratedDeriv_expDampingFactor_succ_eq (m : ℕ) (η : ℝ) (ξ : ℝ) :
    iteratedDeriv (m + 1) (expDampingFactor η) ξ =
      (-(η : ℂ)) ^ (m + 1) * Complex.exp (-(η : ℂ) * ξ) := by
  have hExpAt : ContDiffAt ℝ (m + 1) (fun t : ℝ => Complex.exp (-(η : ℂ) * t)) ξ := by
    exact (expDampingFactor_exp_contDiff η).contDiffAt.of_le (by exact mod_cast le_top)
  have hConstAt : ContDiffAt ℝ (m + 1) (fun _ : ℝ => (1 : ℂ)) ξ := by
    simpa using
      (contDiff_const.contDiffAt.of_le
        (by exact mod_cast le_top : (((m + 1 : ℕ) : WithTop ℕ∞) ≤ _)))
  have hsub := iteratedDeriv_sub (x := ξ) (n := m + 1) hExpAt hConstAt
  change iteratedDeriv (m + 1)
      ((fun t : ℝ => Complex.exp (-(η : ℂ) * t)) - fun _ : ℝ => (1 : ℂ)) ξ = _
  calc
    iteratedDeriv (m + 1)
        ((fun t : ℝ => Complex.exp (-(η : ℂ) * t)) - fun _ : ℝ => (1 : ℂ)) ξ
        = iteratedDeriv (m + 1) (fun t : ℝ => Complex.exp (-(η : ℂ) * t)) ξ -
            iteratedDeriv (m + 1) (fun _ : ℝ => (1 : ℂ)) ξ := by
              simpa using hsub
    _ = (-(η : ℂ)) ^ (m + 1) * Complex.exp (-(η : ℂ) * ξ) - 0 := by
          rw [iteratedDeriv_cexp_const_mul_real]
          simp [iteratedDeriv_const]
    _ = _ := by simp

private theorem norm_iteratedDeriv_expDampingFactor_succ_le_eta_of_nonneg
    (m : ℕ) {η ξ : ℝ} (hη_pos : 0 < η) (hη_le : η ≤ 1) (hξ_nonneg : 0 ≤ ξ) :
    ‖iteratedDeriv (m + 1) (expDampingFactor η) ξ‖ ≤ η := by
  rw [iteratedDeriv_expDampingFactor_succ_eq m η ξ, norm_mul, norm_pow]
  have hpow : η ^ (m + 1) ≤ η := by
    have hηpow : η ^ m ≤ 1 := pow_le_one₀ hη_pos.le hη_le
    calc
      η ^ (m + 1) = η ^ m * η := by rw [pow_succ', mul_comm]
      _ ≤ 1 * η := by
            gcongr
      _ = η := by ring
  have hexp : ‖Complex.exp (-(η : ℂ) * ξ)‖ ≤ 1 := by
    have hcast : Complex.exp (-(η : ℂ) * ξ) = (Real.exp (-(η * ξ)) : ℂ) := by
      simp [mul_comm]
    rw [hcast, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hneg : -(η * ξ) ≤ 0 := by nlinarith
    simpa using Real.exp_le_one_iff.mpr hneg
  have hnormη : ‖-(η : ℂ)‖ = η := by
    simp [Real.norm_eq_abs, abs_of_nonneg hη_pos.le]
  rw [hnormη]
  calc
    η ^ (m + 1) * ‖Complex.exp (-(η : ℂ) * ξ)‖ ≤ η ^ (m + 1) * 1 := by
      gcongr
    _ = η ^ (m + 1) := by ring
    _ ≤ η := hpow

private theorem norm_iteratedDeriv_expDampingFactor_le_eta_of_pos
    {j : ℕ} (hj : 0 < j) {η ξ : ℝ} (hη_pos : 0 < η) (hη_le : η ≤ 1) (hξ_nonneg : 0 ≤ ξ) :
    ‖iteratedDeriv j (expDampingFactor η) ξ‖ ≤ η := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj) with ⟨m, rfl⟩
  exact norm_iteratedDeriv_expDampingFactor_succ_le_eta_of_nonneg m hη_pos hη_le hξ_nonneg

private theorem norm_iteratedDeriv_expDampingFactor_le_const_mul_eta_on_Icc
    (j : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (η : ℝ), 0 < η → η ≤ 1 → ∀ ξ ∈ Set.Icc (-1 : ℝ) 0,
      ‖iteratedDeriv j (expDampingFactor η) ξ‖ ≤ D * η := by
  cases j with
  | zero =>
      refine ⟨2, by positivity, ?_⟩
      intro η hη_pos hη_le ξ hξ
      simpa [iteratedDeriv_zero] using norm_expDampingFactor_le_two_mul_eta_on_Icc hη_pos hη_le hξ
  | succ m =>
      refine ⟨Real.exp 1, (Real.exp_pos 1).le, ?_⟩
      intro η hη_pos hη_le ξ hξ
      rcases hξ with ⟨hξ_lo, hξ_hi⟩
      rw [iteratedDeriv_expDampingFactor_succ_eq m η ξ, norm_mul, norm_pow]
      have hpow : η ^ (m + 1) ≤ η := by
        have hηpow : η ^ m ≤ 1 := pow_le_one₀ hη_pos.le hη_le
        calc
          η ^ (m + 1) = η ^ m * η := by rw [pow_succ', mul_comm]
          _ ≤ 1 * η := by
                gcongr
          _ = η := by ring
      have hexp : ‖Complex.exp (-(η : ℂ) * ξ)‖ ≤ Real.exp 1 := by
        have hcast : Complex.exp (-(η : ℂ) * ξ) = (Real.exp (-(η * ξ)) : ℂ) := by
          simp [mul_comm]
        rw [hcast, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
        have hupper : -(η * ξ) ≤ 1 := by
          nlinarith
        exact Real.exp_le_exp.mpr hupper
      have hnormη : ‖-(η : ℂ)‖ = η := by
        simp [Real.norm_eq_abs, abs_of_nonneg hη_pos.le]
      rw [hnormη]
      calc
        η ^ (m + 1) * ‖Complex.exp (-(η : ℂ) * ξ)‖ ≤ η ^ (m + 1) * Real.exp 1 := by
          gcongr
        _ ≤ η * Real.exp 1 := by
          gcongr
        _ = Real.exp 1 * η := by ring

private theorem norm_expDampingFactor_le_eta_mul_abs_of_nonneg
    {η ξ : ℝ} (hη_nonneg : 0 ≤ η) (hξ_nonneg : 0 ≤ ξ) :
    ‖expDampingFactor η ξ‖ ≤ η * ξ := by
  have hcast : Complex.exp (-(η : ℂ) * ξ) = (Real.exp (-(η * ξ)) : ℂ) := by
    simp [mul_comm]
  have hle_one : Real.exp (-(η * ξ)) ≤ 1 := by
    have hneg : -(η * ξ) ≤ 0 := by nlinarith
    simpa using Real.exp_le_one_iff.mpr hneg
  have habs : |Real.exp (-(η * ξ)) - 1| = 1 - Real.exp (-(η * ξ)) := by
    have hnonpos : Real.exp (-(η * ξ)) - 1 ≤ 0 := sub_nonpos.mpr hle_one
    rw [abs_of_nonpos hnonpos]
    ring
  have haux : 1 - Real.exp (-(η * ξ)) ≤ η * ξ := by
    have := Real.one_sub_le_exp_neg (η * ξ)
    linarith
  calc
    ‖expDampingFactor η ξ‖ = |Real.exp (-(η * ξ)) - 1| := by
      rw [expDampingFactor, hcast, ← Complex.ofReal_one, ← Complex.ofReal_sub]
      simpa [Real.norm_eq_abs] using (Complex.norm_real (Real.exp (-(η * ξ)) - 1))
    _ = 1 - Real.exp (-(η * ξ)) := habs
    _ ≤ η * ξ := haux

private theorem expDamping_mul_iterated_bound_on_Icc
    (ψ : SchwartzMap ℝ ℂ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ ξ ∈ Set.Icc (-1 : ℝ) 0,
      ‖iteratedDeriv n (fun t : ℝ => expDampingFactor η t * ψ t) ξ‖ ≤ C * η := by
  let K : Set ℝ := Set.Icc (-1 : ℝ) 0
  have hK_compact : IsCompact K := isCompact_Icc
  have hB :
      ∀ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ ξ ∈ K, ‖iteratedDeriv j ψ ξ‖ ≤ B := by
    intro j
    obtain ⟨B, hB⟩ := hK_compact.exists_bound_of_continuousOn
      (((ψ.smooth ⊤).continuous_iteratedDeriv j (by exact mod_cast le_top)).norm.continuousOn)
    refine ⟨B, ?_, ?_⟩
    · have hB0' := hB 0 (by
          change (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 0
          constructor <;> norm_num)
      have hB0 : ‖iteratedDeriv j ψ 0‖ ≤ B := by
        simpa using hB0'
      nlinarith [norm_nonneg (iteratedDeriv j ψ 0), hB0]
    · intro ξ hξ
      simpa using hB ξ hξ
  choose B hB_nonneg hB_bound using hB
  have hD :
      ∀ j : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ ξ ∈ K,
        ‖iteratedDeriv j (expDampingFactor η) ξ‖ ≤ D * η := by
    intro j
    simpa [K] using norm_iteratedDeriv_expDampingFactor_le_const_mul_eta_on_Icc j
  choose D hD_nonneg hD_bound using hD
  let C : ℝ := ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℝ) * D i * B (n - i))
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    refine Finset.sum_nonneg ?_
    intro i hi
    exact mul_nonneg
      (mul_nonneg (by exact_mod_cast Nat.zero_le (n.choose i)) (hD_nonneg i))
      (hB_nonneg (n - i))
  · intro η hη_pos hη_le ξ hξ
    have hη_smooth : ContDiffAt ℝ n (expDampingFactor η) ξ :=
      (expDampingFactor_contDiff η).contDiffAt.of_le (by exact mod_cast le_top)
    have hψ_smooth : ContDiffAt ℝ n ψ ξ :=
      (ψ.smooth ⊤).contDiffAt.of_le (by exact mod_cast le_top)
    have hmul :
        iteratedDeriv n (fun t : ℝ => expDampingFactor η t * ψ t) ξ =
          ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℂ) * iteratedDeriv i (expDampingFactor η) ξ *
              iteratedDeriv (n - i) ψ ξ := by
      simpa using iteratedDeriv_mul (x := ξ) hη_smooth hψ_smooth
    calc
      ‖iteratedDeriv n (fun t : ℝ => expDampingFactor η t * ψ t) ξ‖
          = ‖∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℂ) * iteratedDeriv i (expDampingFactor η) ξ *
                iteratedDeriv (n - i) ψ ξ‖ := by
                rw [hmul]
      _ ≤ ∑ i ∈ Finset.range (n + 1),
            ‖(n.choose i : ℂ) * iteratedDeriv i (expDampingFactor η) ξ *
              iteratedDeriv (n - i) ψ ξ‖ := by
              exact norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (n + 1),
            (((n.choose i : ℝ) * D i * B (n - i)) * η) := by
              refine Finset.sum_le_sum ?_
              intro i hi
              have hDi : ‖iteratedDeriv i (expDampingFactor η) ξ‖ ≤ D i * η :=
                hD_bound i η hη_pos hη_le ξ hξ
              have hBi : ‖iteratedDeriv (n - i) ψ ξ‖ ≤ B (n - i) :=
                hB_bound (n - i) ξ hξ
              have hchoose_nonneg : 0 ≤ (n.choose i : ℝ) := by
                exact_mod_cast Nat.zero_le (n.choose i)
              calc
                ‖(n.choose i : ℂ) * iteratedDeriv i (expDampingFactor η) ξ *
                    iteratedDeriv (n - i) ψ ξ‖
                    = (n.choose i : ℝ) * ‖iteratedDeriv i (expDampingFactor η) ξ‖ *
                        ‖iteratedDeriv (n - i) ψ ξ‖ := by
                          simp [mul_assoc]
                _ ≤ (n.choose i : ℝ) * (D i * η) * ‖iteratedDeriv (n - i) ψ ξ‖ := by
                      gcongr
                _ ≤ (n.choose i : ℝ) * (D i * η) * B (n - i) := by
                      have hDiη_nonneg : 0 ≤ D i * η := mul_nonneg (hD_nonneg i) hη_pos.le
                      have hleft_nonneg : 0 ≤ (n.choose i : ℝ) * (D i * η) :=
                        mul_nonneg hchoose_nonneg hDiη_nonneg
                      exact mul_le_mul_of_nonneg_left hBi hleft_nonneg
                _ = (((n.choose i : ℝ) * D i * B (n - i)) * η) := by ring
      _ = C * η := by
            dsimp [C]
            rw [← Finset.sum_mul]

private theorem expDamping_mul_iterated_weighted_bound_on_Ici
    (ψ : SchwartzMap ℝ ℂ) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ ξ : ℝ, 0 ≤ ξ →
      |ξ| ^ k * ‖iteratedDeriv n (fun t : ℝ => expDampingFactor η t * ψ t) ξ‖ ≤ C * η := by
  let A : ℕ → ℝ := fun i =>
    if i = 0 then SchwartzMap.seminorm ℝ (k + 1) n ψ
    else (n.choose i : ℝ) * SchwartzMap.seminorm ℝ k (n - i) ψ
  let C : ℝ := ∑ i ∈ Finset.range (n + 1), A i
  refine ⟨C, ?_, ?_⟩
  · dsimp [C, A]
    refine Finset.sum_nonneg ?_
    intro i hi
    by_cases hi0 : i = 0
    · simp [hi0]
    · have hchoose_nonneg : 0 ≤ (n.choose i : ℝ) := by
          exact_mod_cast Nat.zero_le (n.choose i)
      have hsemi_nonneg : 0 ≤ SchwartzMap.seminorm ℝ k (n - i) ψ := by
          positivity
      simpa [A, hi0] using mul_nonneg hchoose_nonneg hsemi_nonneg
  · intro η hη_pos hη_le ξ hξ_nonneg
    have hη_smooth : ContDiffAt ℝ n (expDampingFactor η) ξ :=
      (expDampingFactor_contDiff η).contDiffAt.of_le (by exact mod_cast le_top)
    have hψ_smooth : ContDiffAt ℝ n ψ ξ :=
      (ψ.smooth ⊤).contDiffAt.of_le (by exact mod_cast le_top)
    have hmul :
        iteratedDeriv n (fun t : ℝ => expDampingFactor η t * ψ t) ξ =
          ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℂ) * iteratedDeriv i (expDampingFactor η) ξ *
              iteratedDeriv (n - i) ψ ξ := by
      simpa using iteratedDeriv_mul (x := ξ) hη_smooth hψ_smooth
    have hξ_abs : |ξ| = ξ := abs_of_nonneg hξ_nonneg
    calc
      |ξ| ^ k * ‖iteratedDeriv n (fun t : ℝ => expDampingFactor η t * ψ t) ξ‖
          = ξ ^ k * ‖∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℂ) * iteratedDeriv i (expDampingFactor η) ξ *
                iteratedDeriv (n - i) ψ ξ‖ := by
                  rw [hmul, hξ_abs]
      _ ≤ ξ ^ k * ∑ i ∈ Finset.range (n + 1),
            ‖(n.choose i : ℂ) * iteratedDeriv i (expDampingFactor η) ξ *
              iteratedDeriv (n - i) ψ ξ‖ := by
              gcongr
              exact norm_sum_le _ _
      _ = ∑ i ∈ Finset.range (n + 1),
            ξ ^ k * ‖(n.choose i : ℂ) * iteratedDeriv i (expDampingFactor η) ξ *
              iteratedDeriv (n - i) ψ ξ‖ := by
              rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.range (n + 1), (A i) * η := by
            refine Finset.sum_le_sum ?_
            intro i hi
            by_cases hi0 : i = 0
            · subst hi0
              calc
                ξ ^ k * ‖(n.choose 0 : ℂ) * iteratedDeriv 0 (expDampingFactor η) ξ *
                    iteratedDeriv n ψ ξ‖
                    = ξ ^ k * (‖expDampingFactor η ξ‖ * ‖iteratedDeriv n ψ ξ‖) := by
                        simp
                _ ≤ ξ ^ k * ((η * ξ) * ‖iteratedDeriv n ψ ξ‖) := by
                      gcongr
                      exact norm_expDampingFactor_le_eta_mul_abs_of_nonneg hη_pos.le hξ_nonneg
                _ = η * (ξ ^ (k + 1) * ‖iteratedDeriv n ψ ξ‖) := by ring
                _ ≤ η * SchwartzMap.seminorm ℝ (k + 1) n ψ := by
                      gcongr
                      simpa [hξ_abs] using
                        (SchwartzMap.le_seminorm' (𝕜 := ℝ) (k := k + 1) (n := n) ψ ξ)
                _ = A 0 * η := by simp [A, mul_comm]
            · have hi_pos : 0 < i := Nat.pos_iff_ne_zero.mpr hi0
              calc
                ξ ^ k * ‖(n.choose i : ℂ) * iteratedDeriv i (expDampingFactor η) ξ *
                    iteratedDeriv (n - i) ψ ξ‖
                    = (n.choose i : ℝ) *
                        ‖iteratedDeriv i (expDampingFactor η) ξ‖ *
                        (ξ ^ k * ‖iteratedDeriv (n - i) ψ ξ‖) := by
                          simp [mul_assoc, mul_left_comm]
                _ ≤ (n.choose i : ℝ) * η * SchwartzMap.seminorm ℝ k (n - i) ψ := by
                      gcongr
                      · exact norm_iteratedDeriv_expDampingFactor_le_eta_of_pos hi_pos hη_pos hη_le hξ_nonneg
                      · simpa [hξ_abs] using
                          (SchwartzMap.le_seminorm' (𝕜 := ℝ) (k := k) (n := n - i) ψ ξ)
                _ = A i * η := by
                      simp [A, hi0, mul_assoc, mul_comm]
      _ = C * η := by
            dsimp [C]
            rw [← Finset.sum_mul]

/-- Global general-`n` pointwise `O(η)` estimate for the damped cutoff kernel. -/
private theorem expDamping_mul_leftTailCutoff_iterated_pointwise_bound
    (ψ : SchwartzMap ℝ ℂ)
    (hψ_left : ∀ ξ ≤ -1, ψ ξ = 0)
    (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ ξ : ℝ,
      |ξ| ^ k * ‖iteratedDeriv n (fun t : ℝ => expDampingFactor η t * ψ t) ξ‖ ≤ C * η := by
  obtain ⟨Cmid, hCmid_nonneg, hmid⟩ := expDamping_mul_iterated_bound_on_Icc ψ n
  obtain ⟨Cpos, hCpos_nonneg, hpos⟩ := expDamping_mul_iterated_weighted_bound_on_Ici ψ k n
  let C : ℝ := Cmid + Cpos
  refine ⟨C, add_nonneg hCmid_nonneg hCpos_nonneg, ?_⟩
  intro η hη_pos hη_le ξ
  by_cases hneg : ξ < -1
  · let f : ℝ → ℂ := fun t => expDampingFactor η t * ψ t
    have hEqNeg : Set.EqOn f (fun _ : ℝ => (0 : ℂ)) (Set.Iio (-1 : ℝ)) := by
      intro t ht
      simp [f, hψ_left t (le_of_lt ht)]
    have hIterEqNeg := Set.EqOn.iteratedDeriv_of_isOpen hEqNeg isOpen_Iio n
    have hzero : iteratedDeriv n f ξ = 0 := by
      simpa using hIterEqNeg hneg
    calc
      |ξ| ^ k * ‖iteratedDeriv n (fun t : ℝ => expDampingFactor η t * ψ t) ξ‖ = 0 := by
        simp [f, hzero]
      _ ≤ C * η := by
            have hC_nonneg : 0 ≤ C := add_nonneg hCmid_nonneg hCpos_nonneg
            exact mul_nonneg hC_nonneg hη_pos.le
  · by_cases hξ_nonneg : 0 ≤ ξ
    · have hmain := hpos η hη_pos hη_le ξ hξ_nonneg
      have hCpos_le : Cpos * η ≤ C * η := by
        dsimp [C]
        nlinarith [hCmid_nonneg, hη_pos]
      exact le_trans hmain hCpos_le
    · have hξ_mem : ξ ∈ Set.Icc (-1 : ℝ) 0 := by
        constructor <;> linarith
      have hξ_abs_le : |ξ| ^ k ≤ 1 := by
        have hξ_abs_le_one : |ξ| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith
        exact pow_le_one₀ (abs_nonneg ξ) hξ_abs_le_one
      have hnorm_nonneg :
          0 ≤ ‖iteratedDeriv n (fun t : ℝ => expDampingFactor η t * ψ t) ξ‖ := by
        positivity
      calc
        |ξ| ^ k * ‖iteratedDeriv n (fun t : ℝ => expDampingFactor η t * ψ t) ξ‖
            ≤ 1 * ‖iteratedDeriv n (fun t : ℝ => expDampingFactor η t * ψ t) ξ‖ := by
              gcongr
        _ = ‖iteratedDeriv n (fun t : ℝ => expDampingFactor η t * ψ t) ξ‖ := by ring
        _ ≤ Cmid * η := hmid η hη_pos hη_le ξ hξ_mem
        _ ≤ C * η := by
              dsimp [C]
              nlinarith [hCpos_nonneg, hη_pos]

private def cutoffSchwartz (ψ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun ξ : ℝ => (smoothCutoff ξ : ℂ)) ψ

private theorem cutoffSchwartz_left
    (ψ : SchwartzMap ℝ ℂ) :
    ∀ ξ ≤ -1, cutoffSchwartz ψ ξ = 0 := by
  intro ξ hξ
  rw [cutoffSchwartz,
    SchwartzMap.smulLeftCLM_apply_apply smoothCutoff_complex_hasTemperateGrowth]
  change ((smoothCutoff ξ : ℂ) * ψ ξ) = 0
  rw [smoothCutoff_zero_of_le_neg_one hξ]
  simp

private theorem cutoffSchwartz_eqOn_nonneg
    (ψ : SchwartzMap ℝ ℂ) :
    Set.EqOn (cutoffSchwartz ψ) ψ (Set.Ici 0) := by
  intro ξ hξ
  have hξ_nonneg : 0 ≤ ξ := by simpa using hξ
  rw [cutoffSchwartz,
    SchwartzMap.smulLeftCLM_apply_apply smoothCutoff_complex_hasTemperateGrowth]
  change ((smoothCutoff ξ : ℂ) * ψ ξ) = ψ ξ
  rw [smoothCutoff_one_of_nonneg hξ_nonneg]
  simp

private def expDampingMulLeftTailCutoffSchwartz
    (η : ℝ) (hη_pos : 0 < η) (hη_le : η ≤ 1)
    (ψ : SchwartzMap ℝ ℂ) (hψ_left : ∀ ξ ≤ -1, ψ ξ = 0) : SchwartzMap ℝ ℂ where
  toFun := fun ξ => expDampingFactor η ξ * ψ ξ
  smooth' := (expDampingFactor_contDiff η).mul (ψ.smooth _)
  decay' k n := by
    obtain ⟨C, hC_nonneg, hC⟩ :=
      expDamping_mul_leftTailCutoff_iterated_pointwise_bound ψ hψ_left k n
    refine ⟨C * η, fun ξ => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hC η hη_pos hη_le ξ

private theorem seminorm_expDampingMulLeftTailCutoffSchwartz_le
    (ψ : SchwartzMap ℝ ℂ) (hψ_left : ∀ ξ ≤ -1, ψ ξ = 0)
    (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, ∀ hη_pos : 0 < η, ∀ hη_le : η ≤ 1,
      SchwartzMap.seminorm ℝ k n
        (expDampingMulLeftTailCutoffSchwartz η hη_pos hη_le ψ hψ_left) ≤ C * η := by
  obtain ⟨C, hC_nonneg, hC⟩ :=
    expDamping_mul_leftTailCutoff_iterated_pointwise_bound ψ hψ_left k n
  refine ⟨C, hC_nonneg, ?_⟩
  intro η hη_pos hη_le
  refine SchwartzMap.seminorm_le_bound' (𝕜 := ℝ) k n
    (expDampingMulLeftTailCutoffSchwartz η hη_pos hη_le ψ hψ_left)
    (mul_nonneg hC_nonneg hη_pos.le) ?_
  intro ξ
  simpa [expDampingMulLeftTailCutoffSchwartz] using hC η hη_pos hη_le ξ

private theorem seminorm_expDampingCutoffSchwartz_le
    (ψ : SchwartzMap ℝ ℂ) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, ∀ hη_pos : 0 < η, ∀ hη_le : η ≤ 1,
      SchwartzMap.seminorm ℝ k n
        (expDampingMulLeftTailCutoffSchwartz η hη_pos hη_le
          (cutoffSchwartz ψ) (cutoffSchwartz_left ψ)) ≤ C * η := by
  simpa using
    seminorm_expDampingMulLeftTailCutoffSchwartz_le
      (ψ := cutoffSchwartz ψ) (hψ_left := cutoffSchwartz_left ψ) k n

private theorem finset_sum_schwartzSeminorm_apply
    (s : Finset (ℕ × ℕ)) (φ : SchwartzMap ℝ ℂ) :
    (∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p) φ =
      ∑ p ∈ s, (schwartzSeminormFamily ℂ ℝ ℂ p) φ := by
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      simp [ha, Seminorm.add_apply, ih]

private theorem clm_bound_of_seminorm_O_eta
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (f : ∀ η : ℝ, 0 < η → η ≤ 1 → SchwartzMap ℝ ℂ)
    (hsemi : ∀ p : ℕ × ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ η : ℝ, ∀ hη_pos : 0 < η, ∀ hη_le : η ≤ 1,
      SchwartzMap.seminorm ℝ p.1 p.2 (f η hη_pos hη_le) ≤ D * η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, ∀ hη_pos : 0 < η, ∀ hη_le : η ≤ 1,
      ‖T (f η hη_pos hη_le)‖ ≤ C * η := by
  classical
  obtain ⟨s, C0, hC0_ne, hbound⟩ := schwartz_functional_bound T
  choose D hD_nonneg hD_bound using hsemi
  let C : ℝ := (C0 : ℝ) * ∑ p ∈ s, D p
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    refine mul_nonneg C0.coe_nonneg ?_
    exact Finset.sum_nonneg (by
      intro p hp
      exact hD_nonneg p)
  · intro η hη_pos hη_le
    have hsup :
        (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (f η hη_pos hη_le) ≤
          ∑ p ∈ s, D p * η := by
      have hsupSeminorm :
          s.sup (schwartzSeminormFamily ℂ ℝ ℂ) ≤
            ∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p :=
        Seminorm.finset_sup_le_sum _ _
      calc
        (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (f η hη_pos hη_le)
            ≤ (∑ p ∈ s, schwartzSeminormFamily ℂ ℝ ℂ p) (f η hη_pos hη_le) :=
              Seminorm.le_def.mp hsupSeminorm _
        _ = ∑ p ∈ s, (schwartzSeminormFamily ℂ ℝ ℂ p) (f η hη_pos hη_le) := by
              simpa using finset_sum_schwartzSeminorm_apply s (f η hη_pos hη_le)
        _ = ∑ p ∈ s, SchwartzMap.seminorm ℝ p.1 p.2 (f η hη_pos hη_le) := by
              unfold schwartzSeminormFamily
              rfl
        _ ≤ ∑ p ∈ s, D p * η := by
              refine Finset.sum_le_sum ?_
              intro p hp
              exact hD_bound p η hη_pos hη_le
    calc
      ‖T (f η hη_pos hη_le)‖ ≤ (C0 • s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (f η hη_pos hη_le) :=
        hbound (f η hη_pos hη_le)
      _ = (C0 : ℝ) * (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (f η hη_pos hη_le) := by
            rfl
      _ ≤ (C0 : ℝ) * ∑ p ∈ s, D p * η := by
            exact mul_le_mul_of_nonneg_left hsup C0.coe_nonneg
      _ = (C0 : ℝ) * ((∑ p ∈ s, D p) * η) := by
            rw [← Finset.sum_mul]
      _ = C * η := by
            dsimp [C]
            ring

private theorem clm_bound_of_expDampingCutoff_O_eta
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (ψ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, ∀ hη_pos : 0 < η, ∀ hη_le : η ≤ 1,
      ‖T (expDampingMulLeftTailCutoffSchwartz η hη_pos hη_le
        (cutoffSchwartz ψ) (cutoffSchwartz_left ψ))‖ ≤ C * η := by
  refine clm_bound_of_seminorm_O_eta T
    (f := fun η hη_pos hη_le =>
      expDampingMulLeftTailCutoffSchwartz η hη_pos hη_le
        (cutoffSchwartz ψ) (cutoffSchwartz_left ψ)) ?_
  intro p
  simpa using seminorm_expDampingCutoffSchwartz_le (ψ := ψ) p.1 p.2

private theorem clm_bound_of_fourier_expDampingCutoff_O_eta
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (ψ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, ∀ hη_pos : 0 < η, ∀ hη_le : η ≤ 1,
      ‖T (SchwartzMap.fourierTransformCLM ℂ
        (expDampingMulLeftTailCutoffSchwartz η hη_pos hη_le
          (cutoffSchwartz ψ) (cutoffSchwartz_left ψ)))‖ ≤ C * η := by
  simpa [ContinuousLinearMap.comp_apply] using
    clm_bound_of_expDampingCutoff_O_eta
      (T := T.comp (SchwartzMap.fourierTransformCLM ℂ)) ψ

private theorem tendsto_fourier_expDampingCutoff_zero
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (ψ : SchwartzMap ℝ ℂ) :
    Tendsto
      (fun η : ℝ =>
        if hη_pos : 0 < η then
          if hη_le : η ≤ 1 then
            T (SchwartzMap.fourierTransformCLM ℂ
              (expDampingMulLeftTailCutoffSchwartz η hη_pos hη_le
                (cutoffSchwartz ψ) (cutoffSchwartz_left ψ)))
          else 0
        else 0)
      (nhdsWithin 0 (Ioi 0))
      (nhds 0) := by
  obtain ⟨C, hC_nonneg, hC_bound⟩ := clm_bound_of_fourier_expDampingCutoff_O_eta (T := T) ψ
  have hη_le_mem : {η : ℝ | η ≤ 1} ∈ nhdsWithin 0 (Ioi 0) := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨Iio (1 : ℝ), Iio_mem_nhds (by norm_num), ?_⟩
    intro η hη
    exact le_of_lt (show η < 1 from hη.1)
  have hbound :
      ∀ᶠ η : ℝ in nhdsWithin 0 (Ioi 0),
        ‖if hη_pos : 0 < η then
            if hη_le : η ≤ 1 then
              T (SchwartzMap.fourierTransformCLM ℂ
                (expDampingMulLeftTailCutoffSchwartz η hη_pos hη_le
                  (cutoffSchwartz ψ) (cutoffSchwartz_left ψ)))
            else 0
          else 0‖ ≤ C * η := by
    filter_upwards [self_mem_nhdsWithin, hη_le_mem] with η hη_pos hη_le
    have hη_pos' : 0 < η := hη_pos
    rw [dif_pos hη_pos', dif_pos hη_le]
    exact hC_bound η hη_pos' hη_le
  have hCη :
      Tendsto (fun η : ℝ => C * η) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul
        (tendsto_id.mono_left nhdsWithin_le_nhds) :
          Tendsto (fun η : ℝ => C * η) (nhdsWithin 0 (Ioi 0)) (nhds (C * 0)))
  exact squeeze_zero_norm' hbound hCη

private theorem fourier_pairing_cutoffSchwartz_eq
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (hT_supp : HasOneSidedFourierSupport T)
    (ψ : SchwartzMap ℝ ℂ) :
    T (SchwartzMap.fourierTransformCLM ℂ (cutoffSchwartz ψ)) =
      T (SchwartzMap.fourierTransformCLM ℂ ψ) :=
  fourier_pairing_eq_of_eqOn_nonneg T hT_supp (cutoffSchwartz_eqOn_nonneg ψ)

set_option backward.isDefEq.respectTransparency false in
private theorem fourierInv_eq_cexp_integral
    (φ : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    FourierTransform.fourierInv φ ξ =
      ∫ x : ℝ, Complex.exp (2 * Real.pi * Complex.I * ξ * x) * φ x := by
  have hcoe :
      FourierTransform.fourierInv φ ξ =
        FourierTransform.fourierInv (φ : ℝ → ℂ) ξ := by
    simpa using
      congrArg (fun g => g ξ) (SchwartzMap.fourierInv_coe (f := φ))
  rw [hcoe, Real.fourierInv_eq' (f := (φ : ℝ → ℂ)) (w := ξ)]
  congr 1; ext v
  have hinner : ∀ a b : ℝ, @inner ℝ ℝ _ a b = b * a := by
    intro a b; simp [inner, mul_comm]
  simp only [smul_eq_mul, hinner, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

set_option backward.isDefEq.respectTransparency false in
private theorem psiZ_pairing_formula
    (φ : SchwartzMap ℝ ℂ) (η ξ : ℝ) :
    ∫ x : ℝ, psiZ ((2 * Real.pi : ℂ) * (x + η * Complex.I)) ξ * φ x =
      smoothCutoff ξ * Complex.exp (-(2 * Real.pi * η : ℂ) * ξ) *
        FourierTransform.fourierInv φ ξ := by
  rw [fourierInv_eq_cexp_integral (φ := φ) (ξ := ξ)]
  have hexp :
      ∀ x : ℝ,
        Complex.exp (Complex.I * ((2 * Real.pi : ℂ) * (x + η * Complex.I)) * ξ) =
          Complex.exp (-(2 * Real.pi * η : ℂ) * ξ) *
            Complex.exp (2 * Real.pi * Complex.I * ξ * x) := by
    intro x
    have harg :
        Complex.I * ((2 * Real.pi : ℂ) * (x + η * Complex.I)) * ξ =
          (-(2 * Real.pi * η : ℂ) * ξ) + (2 * Real.pi * Complex.I * ξ * x) := by
      calc
        Complex.I * ((2 * Real.pi : ℂ) * (x + η * Complex.I)) * ξ
            = 2 * Real.pi * Complex.I * ξ * x +
                2 * Real.pi * Complex.I * (Complex.I * ((η : ℂ) * ξ)) := by ring
        _ = 2 * Real.pi * Complex.I * ξ * x +
              2 * Real.pi * (Complex.I * Complex.I) * ((η : ℂ) * ξ) := by ring
        _ = 2 * Real.pi * Complex.I * ξ * x - (2 * Real.pi * η : ℂ) * ξ := by
              simp [Complex.I_mul_I, sub_eq_add_neg, mul_left_comm, mul_comm]
              ring
        _ = (-(2 * Real.pi * η : ℂ) * ξ) + (2 * Real.pi * Complex.I * ξ * x) := by ring
    rw [harg, Complex.exp_add]
  have hrewrite :
      (∫ x : ℝ, psiZ ((2 * Real.pi : ℂ) * (x + η * Complex.I)) ξ * φ x) =
        ∫ x : ℝ,
          (smoothCutoff ξ : ℂ) *
            (Complex.exp (-(2 * Real.pi * η : ℂ) * ξ) *
              Complex.exp (2 * Real.pi * Complex.I * ξ * x)) * φ x := by
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [psiZ_eq, hexp x]
  rw [hrewrite]
  have hfactor :
      (∫ x : ℝ,
          (smoothCutoff ξ : ℂ) *
            (Complex.exp (-(2 * Real.pi * η : ℂ) * ξ) *
              Complex.exp (2 * Real.pi * Complex.I * ξ * x)) * φ x) =
        ∫ x : ℝ,
          Complex.exp (-(2 * Real.pi * η : ℂ) * ξ) *
            ((smoothCutoff ξ : ℂ) * (Complex.exp (2 * Real.pi * Complex.I * ξ * x) * φ x)) := by
    refine integral_congr_ae ?_
    filter_upwards with x
    ring
  rw [hfactor]
  conv_lhs =>
    rw [@integral_const_mul ℝ _ MeasureTheory.volume ℂ _
      (Complex.exp (-(2 * Real.pi * η : ℂ) * ξ))
      (fun (x : ℝ) => (smoothCutoff ξ : ℂ) * (Complex.exp (2 * Real.pi * Complex.I * ξ * x) * φ x))]
  conv_lhs =>
    rw [@integral_const_mul ℝ _ MeasureTheory.volume ℂ _
      (smoothCutoff ξ : ℂ)
      (fun (x : ℝ) => Complex.exp (2 * Real.pi * Complex.I * ξ * x) * φ x)]
  ring

/-- Public `2π`-normalized `ψ_z` pairing formula used by the OS-route
time-shift expansion. -/
theorem psiZ_twoPi_pairing_formula
    (φ : SchwartzMap ℝ ℂ) (η ξ : ℝ) :
    ∫ x : ℝ,
      psiZ ((2 * Real.pi : ℂ) * (x + η * Complex.I)) ξ * φ x =
        smoothCutoff ξ * Complex.exp (-(2 * Real.pi * η : ℂ) * ξ) *
          FourierTransform.fourierInv φ ξ :=
  psiZ_pairing_formula φ η ξ

private def stepAScalarDerivIntegrand
    (η : ℝ) (hη : 0 < η) (φ : SchwartzMap ℝ ℂ) (n : ℕ) (ξ x : ℝ) : ℂ :=
  iteratedDeriv n (scaledHorizontalSchwartzPsi η hη x) ξ * φ x

private theorem continuous_stepAScalarDerivIntegrand
    (η : ℝ) (hη : 0 < η) (φ : SchwartzMap ℝ ℂ) (n : ℕ) (ξ : ℝ) :
    Continuous (fun x : ℝ => stepAScalarDerivIntegrand η hη φ n ξ x) := by
  have hbcf : Continuous (fun x : ℝ =>
      weightedDerivToBCFCLM 0 n (scaledHorizontalSchwartzPsi η hη x)) :=
    continuous_weightedDerivToBCFCLM_scaledHorizontal η hη 0 n
  have hpsi0 : Continuous (fun x : ℝ =>
      (weightedDerivToBCFCLM 0 n (scaledHorizontalSchwartzPsi η hη x)) ξ) :=
    (BoundedContinuousFunction.evalCLM ℂ ξ).continuous.comp hbcf
  have hEq :
      (fun x : ℝ => (weightedDerivToBCFCLM 0 n (scaledHorizontalSchwartzPsi η hη x)) ξ) =
        fun x : ℝ => iteratedDeriv n (scaledHorizontalSchwartzPsi η hη x) ξ := by
    funext x
    simp [weightedDerivToBCFCLM_apply, polyWeight]
  have hpsi : Continuous (fun x : ℝ =>
      iteratedDeriv n (scaledHorizontalSchwartzPsi η hη x) ξ) := by
    simpa [hEq] using hpsi0
  simpa [stepAScalarDerivIntegrand] using hpsi.mul φ.continuous

private theorem integrable_stepAScalarDerivIntegrand
    (η : ℝ) (hη : 0 < η) (φ : SchwartzMap ℝ ℂ) (n : ℕ) (ξ : ℝ) :
    Integrable (fun x : ℝ => stepAScalarDerivIntegrand η hη φ n ξ x) := by
  obtain ⟨D, hD_nonneg, hD⟩ :=
    weightedDerivToBCFCLM_scaledHorizontal_growth η hη 0 n
  have hbound :
      ∀ x : ℝ,
        ‖stepAScalarDerivIntegrand η hη φ n ξ x‖ ≤
          D * ((1 + |x|) ^ n * ‖φ x‖) := by
    intro x
    have hpoint :
        ‖iteratedDeriv n (scaledHorizontalSchwartzPsi η hη x) ξ‖ ≤
          ‖weightedDerivToBCFCLM 0 n (scaledHorizontalSchwartzPsi η hη x)‖ := by
      simpa [weightedDerivToBCFCLM_apply, polyWeight] using
        (weightedDerivToBCFCLM 0 n (scaledHorizontalSchwartzPsi η hη x)).norm_coe_le_norm ξ
    calc
      ‖stepAScalarDerivIntegrand η hη φ n ξ x‖
          = ‖iteratedDeriv n (scaledHorizontalSchwartzPsi η hη x) ξ‖ * ‖φ x‖ := by
              simp [stepAScalarDerivIntegrand]
      _ ≤ (D * (1 + |x|) ^ n) * ‖φ x‖ := by
            gcongr
            exact hpoint.trans (hD x)
      _ = D * ((1 + |x|) ^ n * ‖φ x‖) := by ring
  exact Integrable.mono'
    ((integrable_one_add_abs_rpow_mul_norm φ n).const_mul D)
    ((continuous_stepAScalarDerivIntegrand η hη φ n ξ).aestronglyMeasurable)
    (Filter.Eventually.of_forall hbound)

  private theorem hasDerivAt_stepAScalarDerivIntegrand
    (η : ℝ) (hη : 0 < η) (φ : SchwartzMap ℝ ℂ) (n : ℕ) (x ξ : ℝ) :
    HasDerivAt
      (fun t : ℝ => stepAScalarDerivIntegrand η hη φ n t x)
      (stepAScalarDerivIntegrand η hη φ (n + 1) ξ x) ξ := by
  have hcont : ContDiff ℝ (n + 1) (scaledHorizontalSchwartzPsi η hη x) :=
    (scaledHorizontalSchwartzPsi η hη x).smooth _
  have hpsi :
      HasDerivAt
        (fun t : ℝ => iteratedDeriv n (scaledHorizontalSchwartzPsi η hη x) t)
        (iteratedDeriv (n + 1) (scaledHorizontalSchwartzPsi η hη x) ξ) ξ := by
    simpa [iteratedDeriv_succ] using
      ((hcont.differentiable_iteratedDeriv' n ξ).hasDerivAt)
  simpa [stepAScalarDerivIntegrand] using hpsi.mul_const (φ x)

private def stepAScalarDerivIntegral
    (η : ℝ) (hη : 0 < η) (φ : SchwartzMap ℝ ℂ) (n : ℕ) (ξ : ℝ) : ℂ :=
  ∫ x : ℝ, stepAScalarDerivIntegrand η hη φ n ξ x

private theorem hasDerivAt_stepAScalarDerivIntegral
    (η : ℝ) (hη : 0 < η) (φ : SchwartzMap ℝ ℂ) (n : ℕ) (ξ : ℝ) :
    HasDerivAt
      (stepAScalarDerivIntegral η hη φ n)
      (stepAScalarDerivIntegral η hη φ (n + 1) ξ) ξ := by
  let s : Set ℝ := Metric.ball ξ 1
  have hs : s ∈ 𝓝 ξ := Metric.ball_mem_nhds ξ zero_lt_one
  have hF_meas :
      ∀ᶠ y in 𝓝 ξ, AEStronglyMeasurable
        (fun x : ℝ => stepAScalarDerivIntegrand η hη φ n y x) volume := by
    filter_upwards with y
    exact (continuous_stepAScalarDerivIntegrand η hη φ n y).aestronglyMeasurable
  have hF_int :
      Integrable (fun x : ℝ => stepAScalarDerivIntegrand η hη φ n ξ x) :=
    integrable_stepAScalarDerivIntegrand η hη φ n ξ
  have hF'_meas :
      AEStronglyMeasurable
        (fun x : ℝ => stepAScalarDerivIntegrand η hη φ (n + 1) ξ x) volume :=
    (continuous_stepAScalarDerivIntegrand η hη φ (n + 1) ξ).aestronglyMeasurable
  obtain ⟨D, hD_nonneg, hD⟩ :=
    weightedDerivToBCFCLM_scaledHorizontal_growth η hη 0 (n + 1)
  let bound : ℝ → ℝ := fun x => D * ((1 + |x|) ^ (n + 1) * ‖φ x‖)
  have h_bound :
      ∀ᵐ x : ℝ ∂volume, ∀ y ∈ s,
        ‖stepAScalarDerivIntegrand η hη φ (n + 1) y x‖ ≤ bound x := by
    filter_upwards with x y hy
    have hpoint :
        ‖iteratedDeriv (n + 1) (scaledHorizontalSchwartzPsi η hη x) y‖ ≤
          ‖weightedDerivToBCFCLM 0 (n + 1) (scaledHorizontalSchwartzPsi η hη x)‖ := by
      simpa [weightedDerivToBCFCLM_apply, polyWeight] using
        (weightedDerivToBCFCLM 0 (n + 1) (scaledHorizontalSchwartzPsi η hη x)).norm_coe_le_norm y
    calc
      ‖stepAScalarDerivIntegrand η hη φ (n + 1) y x‖
          = ‖iteratedDeriv (n + 1) (scaledHorizontalSchwartzPsi η hη x) y‖ * ‖φ x‖ := by
              simp [stepAScalarDerivIntegrand]
      _ ≤ (D * (1 + |x|) ^ (n + 1)) * ‖φ x‖ := by
            gcongr
            exact hpoint.trans (hD x)
      _ = bound x := by
            simp [bound]
            ring
  have bound_integrable : Integrable bound := by
    simpa [bound, mul_assoc, mul_left_comm, mul_comm] using
      (integrable_one_add_abs_rpow_mul_norm φ (n + 1)).const_mul D
  have h_diff :
      ∀ᵐ x : ℝ ∂volume, ∀ y ∈ s,
        HasDerivAt
          (fun t : ℝ => stepAScalarDerivIntegrand η hη φ n t x)
          (stepAScalarDerivIntegrand η hη φ (n + 1) y x) y := by
    filter_upwards with x y hy
    exact hasDerivAt_stepAScalarDerivIntegrand η hη φ n x y
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int
    hF'_meas h_bound bound_integrable h_diff).2

private theorem hasDerivAt_iteratedDeriv_stepAScalarIntegral
    (η : ℝ) (hη : 0 < η) (φ : SchwartzMap ℝ ℂ) (n : ℕ) (ξ : ℝ) :
    HasDerivAt
      (iteratedDeriv n (stepAScalarDerivIntegral η hη φ 0))
      (stepAScalarDerivIntegral η hη φ (n + 1) ξ) ξ := by
  induction n generalizing ξ with
  | zero =>
      simpa [stepAScalarDerivIntegral] using
        hasDerivAt_stepAScalarDerivIntegral η hη φ 0 ξ
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have hEq :
          deriv (iteratedDeriv n (stepAScalarDerivIntegral η hη φ 0)) =ᶠ[𝓝 ξ]
            fun y => stepAScalarDerivIntegral η hη φ (n + 1) y := by
        filter_upwards [Filter.Eventually.of_forall fun y => (ih y).deriv] with y hy using hy
      rw [EventuallyEq.hasDerivAt_iff hEq]
      simpa using hasDerivAt_stepAScalarDerivIntegral η hη φ (n + 1) ξ

private theorem iteratedDeriv_stepAScalarIntegral_eq
    (η : ℝ) (hη : 0 < η) (φ : SchwartzMap ℝ ℂ) (n : ℕ) (ξ : ℝ) :
    iteratedDeriv n (stepAScalarDerivIntegral η hη φ 0) ξ =
      stepAScalarDerivIntegral η hη φ n ξ := by
  induction n generalizing ξ with
  | zero =>
      rfl
  | succ n ih =>
      rw [iteratedDeriv_succ]
      simpa using (hasDerivAt_iteratedDeriv_stepAScalarIntegral η hη φ n ξ).deriv

private def stepAKernel
    (η : ℝ) (hη_pos : 0 < η) (hη_le : η ≤ 1)
    (ψ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  cutoffSchwartz ψ +
    expDampingMulLeftTailCutoffSchwartz η hη_pos hη_le
      (cutoffSchwartz ψ) (cutoffSchwartz_left ψ)

private theorem stepAKernel_eq
    (η : ℝ) (hη_pos : 0 < η) (hη_le : η ≤ 1)
    (ψ : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    stepAKernel η hη_pos hη_le ψ ξ =
      smoothCutoff ξ * Complex.exp (-(η : ℂ) * ξ) * ψ ξ := by
  rw [stepAKernel]
  change cutoffSchwartz ψ ξ + expDampingFactor η ξ * cutoffSchwartz ψ ξ =
    smoothCutoff ξ * Complex.exp (-(η : ℂ) * ξ) * ψ ξ
  rw [cutoffSchwartz,
    SchwartzMap.smulLeftCLM_apply_apply smoothCutoff_complex_hasTemperateGrowth]
  simp [expDampingFactor]
  ring

private theorem stepAScalarDerivIntegral_eq_iteratedDeriv_stepAKernel
    (η : ℝ) (hη_pos : 0 < η) (hη_le : 2 * Real.pi * η ≤ 1)
    (φ : SchwartzMap ℝ ℂ) (n : ℕ) (ξ : ℝ) :
    stepAScalarDerivIntegral η hη_pos φ n ξ =
      iteratedDeriv n
        (stepAKernel (2 * Real.pi * η) (by positivity) hη_le (FourierTransform.fourierInv φ)) ξ := by
  calc
    stepAScalarDerivIntegral η hη_pos φ n ξ
        = iteratedDeriv n (stepAScalarDerivIntegral η hη_pos φ 0) ξ := by
            symm
            exact iteratedDeriv_stepAScalarIntegral_eq η hη_pos φ n ξ
    _ = iteratedDeriv n (fun t : ℝ =>
          stepAKernel (2 * Real.pi * η) (by positivity) hη_le (FourierTransform.fourierInv φ) t) ξ := by
            congr 1
            funext t
            rw [stepAScalarDerivIntegral]
            simp [stepAScalarDerivIntegrand]
            have hpair := psiZ_pairing_formula (φ := φ) (η := η) (ξ := t)
            simpa [scaledHorizontalSchwartzPsi, horizontalSchwartzPsi, schwartzPsiZ_apply,
              stepAKernel_eq, mul_add, mul_assoc, add_comm, add_left_comm, add_assoc] using hpair

set_option backward.isDefEq.respectTransparency false in
private theorem integral_stepAProbeFamily_eq_probe_stepAKernel
    (s : Finset (ℕ × ℕ)) (η : ℝ) (hη_pos : 0 < η) (hη_le : 2 * Real.pi * η ≤ 1)
    (φ : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, stepAProbeFamily s η hη_pos φ x) =
      probeCLM s
        (stepAKernel (2 * Real.pi * η) (by positivity) hη_le (FourierTransform.fourierInv φ)) := by
  ext p ξ
  let k : ℕ := p.1.1.1
  let n : ℕ := p.1.1.2
  have h_eval_p :
      (∫ x : ℝ, stepAProbeFamily s η hη_pos φ x) p =
        ∫ x : ℝ, stepAProbeFamily s η hη_pos φ x p := by
    simpa using
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ↥s.attach => ℝ →ᵇ ℂ) p).integral_comp_comm
        (integrable_stepAProbeFamily s η hη_pos φ)).symm
  have h_eval_ξ :
      (∫ x : ℝ, stepAProbeFamily s η hη_pos φ x p) ξ =
        ∫ x : ℝ, stepAProbeFamily s η hη_pos φ x p ξ := by
    simpa using
      ((BoundedContinuousFunction.evalCLM ℂ ξ).integral_comp_comm
        (integrable_stepAProbeFamily_component s η hη_pos φ p)).symm
  rw [h_eval_p, h_eval_ξ]
  calc
    ∫ x : ℝ, stepAProbeFamily s η hη_pos φ x p ξ
        = ∫ x : ℝ, polyWeight k ξ * stepAScalarDerivIntegrand η hη_pos φ n ξ x := by
            congr with x
            simp [stepAProbeFamily, probeCLM, k, n, stepAScalarDerivIntegrand,
              weightedDerivToBCFCLM_apply, mul_comm, mul_left_comm]
    _ = polyWeight k ξ * stepAScalarDerivIntegral η hη_pos φ n ξ := by
          rw [stepAScalarDerivIntegral]
          conv_lhs => rw [@integral_const_mul ℝ _ MeasureTheory.volume ℂ _ (polyWeight k ξ)
            (fun x => stepAScalarDerivIntegrand η hη_pos φ n ξ x)]
    _ = polyWeight k ξ *
          iteratedDeriv n
            (stepAKernel (2 * Real.pi * η) (by positivity) hη_le (FourierTransform.fourierInv φ)) ξ := by
            rw [stepAScalarDerivIntegral_eq_iteratedDeriv_stepAKernel η hη_pos hη_le φ n ξ]
    _ = probeCLM s
          (stepAKernel (2 * Real.pi * η) (by positivity) hη_le (FourierTransform.fourierInv φ)) p ξ := by
          simp [probeCLM, k, n, weightedDerivToBCFCLM_apply]

/-! ### The Paley-Wiener-Schwartz theorem: 1D case -/

/-- **Paley-Wiener theorem for the half-line (1D).**

    If `T ∈ S'(ℝ)` is given as a continuous complex-linear functional on
    Schwartz space with
    Fourier support in [0, infinity) (meaning: T(phi) = 0 whenever
    supp(phi) subset (-infinity, 0)), then the Fourier-Laplace transform
    z -> T(e^{-iz .}) extends holomorphically to the upper half-plane Im(z) > 0.

    More precisely, there exists a holomorphic function F on the upper half-plane
    such that for each Schwartz function phi, the smeared integral
    integral_R F(x + i*eta) * phi(x) dx converges to T(phi) as eta -> 0+.

    The proof (not yet formalized) proceeds by:
    1. Write T(phi) = (FT)(F^{-1}(phi)) by Parseval for distributions
    2. Since supp(FT) subset [0, infinity), the pairing localizes to xi >= 0
    3. For Im(z) > 0, the factor e^{-Im(z)*xi} provides exponential decay for xi >= 0
    4. This makes z -> T(e^{-iz .}) well-defined and holomorphic (differentiate under
       the distribution pairing)

    The Fourier-Laplace Schwartz family `ψ_z`, the candidate extension
    `z ↦ T(ℱ[ψ_z])`, its differentiability on the upper half-plane, the
    horizontal-line seminorm growth of `ψ_{x+iη}`, the finite-seminorm control
    of `T`, the polynomial horizontal-line growth of both
    `z ↦ T(ℱ[ψ_z])` and its candidate derivative kernel
    `z ↦ T(ℱ[(I ξ) ψ_z])`, and the `O(η)` convergence of the cutoff-damped
    Fourier-side boundary family are now formalized in `SCV.FourierLaplaceCore`,
    `schwartz_functional_bound`, `fourierLaplaceExt_differentiableOn`,
    `fourierLaplaceExt_horizontal_growth`,
    `fourierLaplaceExt_derivCandidate_horizontal_growth`,
    `fourierInv_scaled_eq_cexp_integral`,
    `psiZ_pairing_formula`,
    `tendsto_fourier_expDampingCutoff_zero`, and
    `fourier_pairing_cutoffSchwartz_eq`.
    The remaining blocker is to lift the scalar pairing identity
    `psiZ_pairing_formula` through the tempered functional `T`, i.e. to prove
    the `T`-paired boundary-value identity without a Banach-valued Bochner
    integral on Schwartz space.

    Ref: Reed-Simon II, Theorem IX.16; Hormander, Theorem 7.4.3 -/
theorem paley_wiener_half_line
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (hT_supp : HasOneSidedFourierSupport T) :
    ∃ (F : ℂ → ℂ),
      DifferentiableOn ℂ F upperHalfPlane ∧
      -- F has polynomial growth on approach to the real axis
      (∀ (η : ℝ), 0 < η →
        HasPolynomialGrowthOnLine (fun x => F (x + η * I))) ∧
      -- Distributional boundary value: smeared integrals converge to T
      (∀ (φ : SchwartzMap ℝ ℂ),
        Tendsto (fun η : ℝ => ∫ x : ℝ, F (↑x + ↑η * I) * φ x)
          (nhdsWithin 0 (Ioi 0))
          (nhds (T φ))) := by
  let a : ℝ := 2 * Real.pi
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  let Fcore : ℂ → ℂ := fun w => if hw : 0 < w.im then fourierLaplaceExt T w hw else 0
  let F : ℂ → ℂ := fun w => Fcore ((a : ℂ) * w)
  refine ⟨F, ?_, ?_, ?_⟩
  · -- Part 1: holomorphicity on the upper half-plane
    have hmap : MapsTo (fun w : ℂ => (a : ℂ) * w) upperHalfPlane upperHalfPlane := by
      intro z hz
      dsimp [upperHalfPlane] at hz ⊢
      simpa [Complex.mul_im, a, mul_assoc] using mul_pos ha_pos hz
    have hmul :
        DifferentiableOn ℂ (fun w : ℂ => (a : ℂ) * w) upperHalfPlane := by
      intro z hz
      simpa using
        (((differentiableAt_id : DifferentiableAt ℂ (fun y : ℂ => y) z).const_mul
          (a : ℂ)).differentiableWithinAt)
    simpa [F] using
      (fourierLaplaceExt_differentiableOn T).comp
        hmul
        hmap
  · -- Part 2: polynomial growth on each horizontal line Im(z) = η
    intro η hη
    obtain ⟨C, N, hC, hbound⟩ := fourierLaplaceExt_horizontal_growth T (a * η) (mul_pos ha_pos hη)
    refine ⟨C * a ^ N, N, by positivity, fun x => ?_⟩
    have him : 0 < (((a : ℂ) * ((x : ℂ) + η * I)).im) := by
      simpa [Complex.mul_im, a, mul_assoc] using mul_pos ha_pos hη
    calc
      ‖F ((x : ℂ) + η * I)‖
          = ‖fourierLaplaceExt T ((a : ℂ) * ((x : ℂ) + η * I)) him‖ := by
              change ‖(if h : 0 < (((a : ℂ) * ((x : ℂ) + η * I)).im) then
                fourierLaplaceExt T ((a : ℂ) * ((x : ℂ) + η * I)) h else 0)‖ = _
              rw [dif_pos him]
      _ ≤ C * (1 + |a * x|) ^ N := by
            simpa [a, mul_add, mul_assoc, add_comm, add_left_comm, add_assoc] using hbound (a * x)
      _ ≤ C * (a ^ N * (1 + |x|) ^ N) := by
            gcongr
            simpa [a] using one_add_abs_two_pi_mul_rpow_le N x
      _ = (C * a ^ N) * (1 + |x|) ^ N := by ring
  · -- Part 3: distributional BV convergence
    intro φ
    let ψ : SchwartzMap ℝ ℂ := FourierTransform.fourierInv φ
    let S : SchwartzMap ℝ ℂ →L[ℂ] ℂ := T.comp (SchwartzMap.fourierTransformCLM ℂ)
    obtain ⟨s, G, hS_factor⟩ := exists_probe_factorization S
    have hS_apply (f : SchwartzMap ℝ ℂ) : S f = G (probeCLM s f) := by
      exact congrArg (fun H => H f) hS_factor
    have hStepB :
        Tendsto
          (fun η : ℝ =>
            if hη_pos : 0 < η then
              if hη_le : η ≤ 1 then
                T (SchwartzMap.fourierTransformCLM ℂ
                  (expDampingMulLeftTailCutoffSchwartz η hη_pos hη_le
                    (cutoffSchwartz ψ) (cutoffSchwartz_left ψ)))
              else 0
            else 0)
          (nhdsWithin 0 (Ioi 0))
          (nhds 0) :=
      tendsto_fourier_expDampingCutoff_zero (T := T) ψ
    have hStepC :
        T (SchwartzMap.fourierTransformCLM ℂ (cutoffSchwartz ψ)) =
          T (SchwartzMap.fourierTransformCLM ℂ ψ) :=
      fourier_pairing_cutoffSchwartz_eq (T := T) hT_supp ψ
    have hStepD : T (SchwartzMap.fourierTransformCLM ℂ ψ) = T φ := by
      dsimp [ψ]
      exact congrArg T (FourierTransform.fourier_fourierInv_eq φ)
    let C0 : ℂ := S (cutoffSchwartz ψ)
    let R : ℝ → ℂ := fun η =>
      if hη_pos : 0 < a * η then
        if hη_le : a * η ≤ 1 then
          S (expDampingMulLeftTailCutoffSchwartz (a * η) hη_pos hη_le
            (cutoffSchwartz ψ) (cutoffSchwartz_left ψ))
        else
          0
      else
        0
    have hscale_tendsto :
        Tendsto (fun η : ℝ => a * η) (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 (Ioi 0)) := by
      refine tendsto_nhdsWithin_iff.mpr ?_
      constructor
      · have hcontWithin : ContinuousWithinAt (fun η : ℝ => a * η) (Ioi 0) 0 := by
          exact (continuous_const.mul continuous_id).continuousAt.continuousWithinAt
        simpa using hcontWithin.tendsto
      · filter_upwards [self_mem_nhdsWithin] with η hη
        simpa [a] using mul_pos ha_pos hη
    have hR : Tendsto R (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      simpa [R, S, a] using hStepB.comp hscale_tendsto
    have hsmall_ev : ∀ᶠ η in nhdsWithin 0 (Ioi 0), a * η ≤ 1 := by
      refine mem_nhdsWithin_of_mem_nhds ?_
      refine Filter.mem_of_superset (Iio_mem_nhds (show (0 : ℝ) < 1 / a by positivity)) ?_
      intro η hη
      have hlt_mul : a * η < a * (1 / a) := mul_lt_mul_of_pos_left hη ha_pos
      have ha_ne : a ≠ 0 := ne_of_gt ha_pos
      have hlt : a * η < 1 := by
        calc
          a * η < a * (1 / a) := hlt_mul
          _ = 1 := by field_simp [ha_ne]
      exact le_of_lt hlt
    have hIntegral_eq :
        ∀ (η : ℝ) (hη : 0 < η) (hη_le : a * η ≤ 1),
          ∫ x : ℝ, F (↑x + ↑η * I) * φ x =
            S (stepAKernel (a * η) (mul_pos ha_pos hη) hη_le ψ) := by
      intro η hη hη_le
      have hpoint :
          ∀ x : ℝ,
            F (↑x + ↑η * I) * φ x = G (stepAProbeFamily s η hη φ x) := by
        intro x
        have him : 0 < (((a : ℂ) * ((x : ℂ) + η * I)).im) := by
          simpa [Complex.mul_im, a, mul_assoc] using mul_pos ha_pos hη
        have hSval :
            S (scaledHorizontalSchwartzPsi η hη x) =
              fourierLaplaceExt T ((a : ℂ) * ((x : ℂ) + η * I)) him := by
          dsimp [S]
          rw [fourierLaplaceExt_eq]
          congr 1
          ext t
          simp [scaledHorizontalSchwartzPsi, horizontalSchwartzPsi, a, mul_add, mul_assoc]
        calc
          F (↑x + ↑η * I) * φ x
              = fourierLaplaceExt T ((a : ℂ) * ((x : ℂ) + η * I)) him * φ x := by
                  change
                    ((if h : 0 < (((a : ℂ) * ((x : ℂ) + η * I)).im) then
                      fourierLaplaceExt T ((a : ℂ) * ((x : ℂ) + η * I)) h else 0) * φ x) = _
                  rw [dif_pos him]
          _ = S (scaledHorizontalSchwartzPsi η hη x) * φ x := by rw [← hSval]
          _ = φ x * S (scaledHorizontalSchwartzPsi η hη x) := by ring
          _ = φ x * G (probeCLM s (scaledHorizontalSchwartzPsi η hη x)) := by
                rw [← hS_apply (scaledHorizontalSchwartzPsi η hη x)]
          _ = G (stepAProbeFamily s η hη φ x) := by
                simp [stepAProbeFamily, map_smul, smul_eq_mul]
      calc
        ∫ x : ℝ, F (↑x + ↑η * I) * φ x
            = ∫ x : ℝ, G (stepAProbeFamily s η hη φ x) := by
                refine integral_congr_ae ?_
                filter_upwards with x
                exact hpoint x
        _ = G (∫ x : ℝ, stepAProbeFamily s η hη φ x) := by
              simpa using G.integral_comp_comm (integrable_stepAProbeFamily s η hη φ)
        _ = G (probeCLM s (stepAKernel (a * η) (mul_pos ha_pos hη) hη_le ψ)) := by
              rw [integral_stepAProbeFamily_eq_probe_stepAKernel s η hη hη_le φ]
        _ = S (stepAKernel (a * η) (mul_pos ha_pos hη) hη_le ψ) := by
              rw [hS_apply]
    have hEventually_eq :
        (fun η : ℝ => ∫ x : ℝ, F (↑x + ↑η * I) * φ x) =ᶠ[nhdsWithin 0 (Ioi 0)]
          fun η => C0 + R η := by
      filter_upwards [self_mem_nhdsWithin, hsmall_ev] with η hη hη_le
      have hηpos : 0 < η := by
        simpa using hη
      have hmain := hIntegral_eq η hηpos hη_le
      calc
        ∫ x : ℝ, F (↑x + ↑η * I) * φ x
            = S (stepAKernel (a * η) (mul_pos ha_pos hηpos) hη_le ψ) := hmain
        _ = C0 + R η := by
              simp [C0, R, S, stepAKernel, hη_le, mul_pos ha_pos hηpos]
    have hlimit_C0 : Tendsto (fun η : ℝ => C0 + R η) (nhdsWithin 0 (Ioi 0)) (nhds C0) := by
      simpa [add_comm, add_left_comm, add_assoc] using (tendsto_const_nhds.add hR)
    have hC0_eq : C0 = T φ := by
      dsimp [C0, S]
      simpa using hStepC.trans hStepD
    have hlimit :
        Tendsto (fun η : ℝ => ∫ x : ℝ, F (↑x + ↑η * I) * φ x)
          (nhdsWithin 0 (Ioi 0)) (nhds C0) :=
      (tendsto_congr' hEventually_eq).2 hlimit_C0
    simpa [hC0_eq] using hlimit

theorem paley_wiener_half_line_explicit
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (hT_supp : HasOneSidedFourierSupport T) :
    let F : ℂ → ℂ := fun w =>
      if hw : 0 < w.im then
        fourierLaplaceExt T ((((2 * Real.pi : ℝ) : ℂ) * w))
          (by
            have hscaled : 0 < (2 * Real.pi) * w.im := mul_pos Real.two_pi_pos hw
            simpa [Complex.mul_im] using hscaled)
      else 0
    DifferentiableOn ℂ F upperHalfPlane ∧
      (∀ η : ℝ, 0 < η →
        HasPolynomialGrowthOnLine (fun x => F (↑x + ↑η * I))) ∧
      (∀ φ : SchwartzMap ℝ ℂ,
        Tendsto (fun η : ℝ => ∫ x : ℝ, F (↑x + ↑η * I) * φ x)
          (nhdsWithin 0 (Ioi 0))
          (nhds (T φ))) := by
  let a : ℝ := 2 * Real.pi
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  let Fcore : ℂ → ℂ := fun w => if hw : 0 < w.im then fourierLaplaceExt T w hw else 0
  let F : ℂ → ℂ := fun w => Fcore ((a : ℂ) * w)
  have hEq :
      F =
        (fun w : ℂ =>
          if hw : 0 < w.im then
            fourierLaplaceExt T ((((2 * Real.pi : ℝ) : ℂ) * w))
              (by
                have hscaled : 0 < (2 * Real.pi) * w.im := mul_pos Real.two_pi_pos hw
                simpa [Complex.mul_im] using hscaled)
          else 0) := by
    funext w
    by_cases hw : 0 < w.im
    · have hscaled : 0 < (((a : ℂ) * w).im) := by
        simpa [Complex.mul_im, a, mul_assoc] using mul_pos ha_pos hw
      unfold F Fcore
      rw [dif_pos hscaled, dif_pos hw]
    · have hnotscaled : ¬ 0 < (((a : ℂ) * w).im) := by
        intro hscaled
        have hscaled' : 0 < a * w.im := by
          simpa [Complex.mul_im, a, mul_assoc] using hscaled
        exact hw <| by nlinarith [ha_pos, hscaled']
      unfold F Fcore
      rw [dif_neg hnotscaled, dif_neg hw]
  have hmain :
      DifferentiableOn ℂ F upperHalfPlane ∧
      (∀ η : ℝ, 0 < η →
        HasPolynomialGrowthOnLine (fun x => F (↑x + ↑η * I))) ∧
      (∀ φ : SchwartzMap ℝ ℂ,
        Tendsto (fun η : ℝ => ∫ x : ℝ, F (↑x + ↑η * I) * φ x)
          (nhdsWithin 0 (Ioi 0))
          (nhds (T φ))) := by
    constructor
    · have hmap : MapsTo (fun w : ℂ => (a : ℂ) * w) upperHalfPlane upperHalfPlane := by
        intro z hz
        dsimp [upperHalfPlane] at hz ⊢
        simpa [Complex.mul_im, a, mul_assoc] using mul_pos ha_pos hz
      have hmul :
          DifferentiableOn ℂ (fun w : ℂ => (a : ℂ) * w) upperHalfPlane := by
        intro z hz
        simpa using
          (((differentiableAt_id : DifferentiableAt ℂ (fun y : ℂ => y) z).const_mul
            (a : ℂ)).differentiableWithinAt)
      simpa [F] using
        (fourierLaplaceExt_differentiableOn T).comp
          hmul
          hmap
    · constructor
      · intro η hη
        obtain ⟨C, N, hC, hbound⟩ :=
          fourierLaplaceExt_horizontal_growth T (a * η) (mul_pos ha_pos hη)
        refine ⟨C * a ^ N, N, by positivity, fun x => ?_⟩
        have him : 0 < (((a : ℂ) * ((x : ℂ) + η * I)).im) := by
          simpa [Complex.mul_im, a, mul_assoc] using mul_pos ha_pos hη
        calc
          ‖F ((x : ℂ) + η * I)‖
              = ‖fourierLaplaceExt T ((a : ℂ) * ((x : ℂ) + η * I)) him‖ := by
                  change ‖(if h : 0 < (((a : ℂ) * ((x : ℂ) + η * I)).im) then
                    fourierLaplaceExt T ((a : ℂ) * ((x : ℂ) + η * I)) h else 0)‖ = _
                  rw [dif_pos him]
          _ ≤ C * (1 + |a * x|) ^ N := by
                simpa [a, mul_add, mul_assoc, add_comm, add_left_comm, add_assoc] using
                  hbound (a * x)
          _ ≤ C * (a ^ N * (1 + |x|) ^ N) := by
                gcongr
                simpa [a] using one_add_abs_two_pi_mul_rpow_le N x
          _ = (C * a ^ N) * (1 + |x|) ^ N := by ring
      · intro φ
        let ψ : SchwartzMap ℝ ℂ := FourierTransform.fourierInv φ
        let S : SchwartzMap ℝ ℂ →L[ℂ] ℂ := T.comp (SchwartzMap.fourierTransformCLM ℂ)
        obtain ⟨s, G, hS_factor⟩ := exists_probe_factorization S
        have hS_apply (f : SchwartzMap ℝ ℂ) : S f = G (probeCLM s f) := by
          exact congrArg (fun H => H f) hS_factor
        have hStepB :
            Tendsto
              (fun η : ℝ =>
                if hη_pos : 0 < η then
                  if hη_le : η ≤ 1 then
                    T (SchwartzMap.fourierTransformCLM ℂ
                      (expDampingMulLeftTailCutoffSchwartz η hη_pos hη_le
                        (cutoffSchwartz ψ) (cutoffSchwartz_left ψ)))
                  else 0
                else 0)
              (nhdsWithin 0 (Ioi 0))
              (nhds 0) :=
          tendsto_fourier_expDampingCutoff_zero (T := T) ψ
        have hStepC :
            T (SchwartzMap.fourierTransformCLM ℂ (cutoffSchwartz ψ)) =
              T (SchwartzMap.fourierTransformCLM ℂ ψ) :=
          fourier_pairing_cutoffSchwartz_eq (T := T) hT_supp ψ
        have hStepD : T (SchwartzMap.fourierTransformCLM ℂ ψ) = T φ := by
          dsimp [ψ]
          exact congrArg T (FourierTransform.fourier_fourierInv_eq φ)
        let C0 : ℂ := S (cutoffSchwartz ψ)
        let R : ℝ → ℂ := fun η =>
          if hη_pos : 0 < a * η then
            if hη_le : a * η ≤ 1 then
              S (expDampingMulLeftTailCutoffSchwartz (a * η) hη_pos hη_le
                (cutoffSchwartz ψ) (cutoffSchwartz_left ψ))
            else
              0
          else
            0
        have hscale_tendsto :
            Tendsto (fun η : ℝ => a * η) (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 (Ioi 0)) := by
          refine tendsto_nhdsWithin_iff.mpr ?_
          constructor
          · have hcontWithin : ContinuousWithinAt (fun η : ℝ => a * η) (Ioi 0) 0 := by
              exact (continuous_const.mul continuous_id).continuousAt.continuousWithinAt
            simpa using hcontWithin.tendsto
          · filter_upwards [self_mem_nhdsWithin] with η hη
            simpa [a] using mul_pos ha_pos hη
        have hR : Tendsto R (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
          simpa [R, S, a] using hStepB.comp hscale_tendsto
        have hsmall_ev : ∀ᶠ η in nhdsWithin 0 (Ioi 0), a * η ≤ 1 := by
          refine mem_nhdsWithin_of_mem_nhds ?_
          refine Filter.mem_of_superset (Iio_mem_nhds (show (0 : ℝ) < 1 / a by positivity)) ?_
          intro η hη
          have hlt_mul : a * η < a * (1 / a) := mul_lt_mul_of_pos_left hη ha_pos
          have ha_ne : a ≠ 0 := ne_of_gt ha_pos
          have hlt : a * η < 1 := by
            calc
              a * η < a * (1 / a) := hlt_mul
              _ = 1 := by field_simp [ha_ne]
          exact le_of_lt hlt
        have hIntegral_eq :
            ∀ (η : ℝ) (hη : 0 < η) (hη_le : a * η ≤ 1),
              ∫ x : ℝ, F (↑x + ↑η * I) * φ x =
                S (stepAKernel (a * η) (mul_pos ha_pos hη) hη_le ψ) := by
          intro η hη hη_le
          have hpoint :
              ∀ x : ℝ,
                F (↑x + ↑η * I) * φ x = G (stepAProbeFamily s η hη φ x) := by
            intro x
            have him : 0 < (((a : ℂ) * ((x : ℂ) + η * I)).im) := by
              simpa [Complex.mul_im, a, mul_assoc] using mul_pos ha_pos hη
            have hSval :
                S (scaledHorizontalSchwartzPsi η hη x) =
                  fourierLaplaceExt T ((a : ℂ) * ((x : ℂ) + η * I)) him := by
              dsimp [S]
              rw [fourierLaplaceExt_eq]
              congr 1
              ext t
              simp [scaledHorizontalSchwartzPsi, horizontalSchwartzPsi, a, mul_add, mul_assoc]
            calc
              F (↑x + ↑η * I) * φ x
                  = fourierLaplaceExt T ((a : ℂ) * ((x : ℂ) + η * I)) him * φ x := by
                      change
                        ((if h : 0 < (((a : ℂ) * ((x : ℂ) + η * I)).im) then
                          fourierLaplaceExt T ((a : ℂ) * ((x : ℂ) + η * I)) h else 0) * φ x) = _
                      rw [dif_pos him]
              _ = S (scaledHorizontalSchwartzPsi η hη x) * φ x := by rw [← hSval]
              _ = φ x * S (scaledHorizontalSchwartzPsi η hη x) := by ring
              _ = φ x * G (probeCLM s (scaledHorizontalSchwartzPsi η hη x)) := by
                    rw [← hS_apply (scaledHorizontalSchwartzPsi η hη x)]
              _ = G (stepAProbeFamily s η hη φ x) := by
                    simp [stepAProbeFamily, map_smul, smul_eq_mul]
          calc
            ∫ x : ℝ, F (↑x + ↑η * I) * φ x
                = ∫ x : ℝ, G (stepAProbeFamily s η hη φ x) := by
                    refine integral_congr_ae ?_
                    filter_upwards with x
                    exact hpoint x
            _ = G (∫ x : ℝ, stepAProbeFamily s η hη φ x) := by
                  simpa using G.integral_comp_comm (integrable_stepAProbeFamily s η hη φ)
            _ = G (probeCLM s (stepAKernel (a * η) (mul_pos ha_pos hη) hη_le ψ)) := by
                  rw [integral_stepAProbeFamily_eq_probe_stepAKernel s η hη hη_le φ]
            _ = S (stepAKernel (a * η) (mul_pos ha_pos hη) hη_le ψ) := by
                  rw [hS_apply]
        have hEventually_eq :
            (fun η : ℝ => ∫ x : ℝ, F (↑x + ↑η * I) * φ x) =ᶠ[nhdsWithin 0 (Ioi 0)]
              fun η => C0 + R η := by
          filter_upwards [self_mem_nhdsWithin, hsmall_ev] with η hη hη_le
          have hηpos : 0 < η := by
            simpa using hη
          have hmain := hIntegral_eq η hηpos hη_le
          calc
            ∫ x : ℝ, F (↑x + ↑η * I) * φ x
                = S (stepAKernel (a * η) (mul_pos ha_pos hηpos) hη_le ψ) := hmain
            _ = C0 + R η := by
                  simp [C0, R, S, stepAKernel, hη_le, mul_pos ha_pos hηpos]
        have hlimit_C0 : Tendsto (fun η : ℝ => C0 + R η) (nhdsWithin 0 (Ioi 0)) (nhds C0) := by
          simpa [add_comm, add_left_comm, add_assoc] using (tendsto_const_nhds.add hR)
        have hC0_eq : C0 = T φ := by
          dsimp [C0, S]
          simpa using hStepC.trans hStepD
        have hlimit :
            Tendsto (fun η : ℝ => ∫ x : ℝ, F (↑x + ↑η * I) * φ x)
              (nhdsWithin 0 (Ioi 0)) (nhds C0) :=
          (tendsto_congr' hEventually_eq).2 hlimit_C0
        simpa [hC0_eq] using hlimit
  dsimp
  simpa [hEq] using hmain

/-! ### Multidimensional status -/

/-
The genuine multidimensional cone/converse Paley-Wiener theorems are
intentionally deferred from this file.

The next honest step is to refactor the ambient domain to
`EuclideanSpace ℝ (Fin m)`, so that the multivariate Fourier-support notion is
stated against the same inner-product-space model used by Mathlib's Schwartz
Fourier transform. Until that happens, the multivariate cone/converse theorems
should remain deferred rather than being stated on `Fin m → ℝ`.
-/

/-! ### One-step extension: the actual current slice theorem -/

/-- **Simplified one-step extension for the inductive continuation (1D).**

    A cleaner version specialized to one complex variable: a continuous function
    on the real line with polynomial growth whose associated tempered distribution
    has Fourier support in `[0, infinity)` extends holomorphically to the upper
    half-plane.

    The conclusion is stated in the correct distributional form: `F_ext` has the
    continuous function `f` as its **distributional boundary value**, not as a
    pointwise boundary trace on `ℝ`. Pointwise equality `F_ext x = f x` on the
    real axis is not the right Paley-Wiener conclusion in this generality.

    This formulation directly matches what `inductive_analytic_continuation`
    needs when all but one variable are fixed: extend holomorphicity in one
    coordinate from a real boundary distribution to the upper half-plane.

    Sorry blocked by: `paley_wiener_half_line` (which it essentially restates
    for the special case where the tempered distribution is given by integrating
    against the continuous polynomially-growing function `f`).

    Ref: OS II, Theorem 4.1; Reed-Simon II, Theorem IX.16 -/
theorem paley_wiener_one_step_simple
    (f : ℝ → ℂ) (hf_cont : Continuous f)
    -- Polynomial growth
    (hf_growth : HasPolynomialGrowthOnLine f)
    -- One-sided Fourier support of the tempered distribution T_f(φ) = ∫ f(t) φ(t) dt.
    (h_spectral : HasOneSidedFourierSupport
      (fun φ : SchwartzMap ℝ ℂ => ∫ t : ℝ, f t * φ t)) :
    ∃ (F_ext : ℂ → ℂ),
      DifferentiableOn ℂ F_ext upperHalfPlane ∧
      -- Polynomial growth on horizontal lines
      (∀ η : ℝ, 0 < η →
        HasPolynomialGrowthOnLine (fun x => F_ext (↑x + ↑η * I))) ∧
      -- Distributional boundary value recovers the function-induced tempered distribution.
      (∀ (φ : SchwartzMap ℝ ℂ),
        Tendsto (fun η : ℝ => ∫ x : ℝ, F_ext (↑x + ↑η * I) * φ x)
          (nhdsWithin 0 (Ioi 0))
          (nhds (∫ t : ℝ, f t * φ t))) := by
  rcases hf_growth with ⟨C_bound, N, hC_bound_pos, h_growth_bound⟩
  let M : ℕ := N + 2
  let sem : SchwartzMap ℝ ℂ → ℝ :=
    fun φ => (Finset.Iic (M, 0)).sup (schwartzSeminormFamily ℂ ℝ ℂ) φ
  have h_decay_int : MeasureTheory.Integrable
      (fun t : ℝ => (1 + ‖t‖) ^ (-(2 : ℝ))) MeasureTheory.volume :=
    by
      have : (Module.finrank ℝ ℝ : ℝ) < (2 : ℝ) := by norm_num
      simpa using integrable_one_add_norm this
  have h_decay_int_nat : MeasureTheory.Integrable
      (fun t : ℝ => ((1 + ‖t‖) ^ 2)⁻¹) MeasureTheory.volume := by
    simpa [Real.rpow_neg (by positivity : 0 ≤ (1 + ‖(0 : ℝ)‖)), Real.rpow_natCast] using
      h_decay_int
  have hsem_bound : ∀ (φ : SchwartzMap ℝ ℂ) (t : ℝ),
      (1 + ‖t‖) ^ M * ‖φ t‖ ≤ 2 ^ M * sem φ := by
    intro φ t
    simpa [sem, M, norm_iteratedFDeriv_zero] using
      (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
        (m := (M, 0)) (k := M) (n := 0) (le_rfl) (le_rfl) φ t)
  have h_pointwise_bound : ∀ (φ : SchwartzMap ℝ ℂ) (t : ℝ),
      ‖f t * φ t‖ ≤ C_bound * 2 ^ M * sem φ * ((1 + ‖t‖) ^ 2)⁻¹ := by
    intro φ t
    have h_growth_t : ‖f t‖ ≤ C_bound * (1 + ‖t‖) ^ N := by
      simpa using h_growth_bound t
    have h_pow_pos : 0 < (1 + ‖t‖) ^ 2 := by positivity
    have h_decay_step : (1 + ‖t‖) ^ N * ‖φ t‖ ≤
        2 ^ M * sem φ * ((1 + ‖t‖) ^ 2)⁻¹ := by
      rw [le_mul_inv_iff₀ h_pow_pos]
      calc
        (1 + ‖t‖) ^ N * ‖φ t‖ * (1 + ‖t‖) ^ 2
            = (1 + ‖t‖) ^ M * ‖φ t‖ := by
                rw [show M = N + 2 by simp [M], pow_add]
                ring
        _ ≤ 2 ^ M * sem φ := hsem_bound φ t
    have h_decay_mul :
        C_bound * (1 + ‖t‖) ^ N * ‖φ t‖ ≤
          C_bound * (2 ^ M * sem φ * ((1 + ‖t‖) ^ 2)⁻¹) := by
      simpa [mul_assoc] using
        (mul_le_mul_of_nonneg_left h_decay_step (le_of_lt hC_bound_pos))
    calc
      ‖f t * φ t‖ = ‖f t‖ * ‖φ t‖ := norm_mul _ _
      _ ≤ C_bound * (1 + ‖t‖) ^ N * ‖φ t‖ :=
        mul_le_mul_of_nonneg_right h_growth_t (norm_nonneg _)
      _ ≤ C_bound * (2 ^ M * sem φ * ((1 + ‖t‖) ^ 2)⁻¹) := h_decay_mul
      _ = C_bound * 2 ^ M * sem φ * ((1 + ‖t‖) ^ 2)⁻¹ := by ring
  have h_integrable : ∀ φ : SchwartzMap ℝ ℂ,
      MeasureTheory.Integrable (fun t : ℝ => f t * φ t) MeasureTheory.volume := by
    intro φ
    have h_majorant_int : MeasureTheory.Integrable
        (fun t : ℝ => C_bound * 2 ^ M * sem φ * ((1 + ‖t‖) ^ 2)⁻¹)
        MeasureTheory.volume :=
      h_decay_int_nat.const_mul (C_bound * 2 ^ M * sem φ)
    refine h_majorant_int.mono' ((hf_cont.mul φ.continuous).aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall (h_pointwise_bound φ)
  let I₂ : ℝ := ∫ t : ℝ, ((1 + ‖t‖) ^ 2)⁻¹
  let T : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
    SchwartzMap.mkCLMtoNormedSpace (𝕜 := ℂ)
      (fun φ : SchwartzMap ℝ ℂ => ∫ t : ℝ, f t * φ t)
      (fun φ ψ => by
        simpa [mul_add] using
          (MeasureTheory.integral_add
            (f := fun t : ℝ => f t * φ t)
            (g := fun t : ℝ => f t * ψ t)
            (h_integrable φ) (h_integrable ψ)))
      (fun a φ => by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (MeasureTheory.integral_smul a (fun t : ℝ => f t * φ t)))
      (by
        have hI₂_nonneg : 0 ≤ I₂ := by
          unfold I₂
          exact MeasureTheory.integral_nonneg fun _ => by positivity
        refine ⟨Finset.Iic (M, 0), C_bound * 2 ^ M * I₂, ?_, ?_⟩
        · exact mul_nonneg (mul_nonneg (le_of_lt hC_bound_pos) (by positivity)) hI₂_nonneg
        · intro φ
          calc
            ‖∫ t : ℝ, f t * φ t‖ ≤ ∫ t : ℝ, ‖f t * φ t‖ :=
              MeasureTheory.norm_integral_le_integral_norm _
            _ ≤ ∫ t : ℝ, C_bound * 2 ^ M * sem φ * ((1 + ‖t‖) ^ 2)⁻¹ :=
              MeasureTheory.integral_mono_ae (h_integrable φ).norm
                (h_decay_int_nat.const_mul (C_bound * 2 ^ M * sem φ))
                (Filter.Eventually.of_forall (h_pointwise_bound φ))
            _ = C_bound * 2 ^ M * I₂ * sem φ := by
              rw [show (∫ t : ℝ, C_bound * 2 ^ M * sem φ * ((1 + ‖t‖) ^ 2)⁻¹) =
                  (C_bound * 2 ^ M * sem φ) * I₂ by
                    simp [I₂, MeasureTheory.integral_const_mul]]
              ring
            _ = (C_bound * 2 ^ M * I₂) * (Finset.Iic (M, 0)).sup
                (schwartzSeminormFamily ℂ ℝ ℂ) φ := by
              simp [sem, mul_assoc])
  obtain ⟨F_ext, hF_holo, hF_growth, hF_bv⟩ :=
    paley_wiener_half_line T (by simpa [T] using h_spectral)
  refine ⟨F_ext, hF_holo, hF_growth, ?_⟩
  intro φ
  simpa [T] using hF_bv φ

/-- **Slice-wise one-step Paley-Wiener extension family.**

For each fixed parameter slice `z'` whose imaginary part lies in `C`, if the
real-line slice `t ↦ F(update z' r t)` is continuous, has polynomial growth,
and its function-induced tempered distribution has one-sided Fourier support,
then there is a corresponding upper-half-plane extension in the `r`-th variable.

This is the actual theorem provided by the current infrastructure. Turning this
slice-wise family into a jointly holomorphic extension in all variables still
requires separate-to-joint holomorphicity plus parameter-regularity inputs, and
belongs upstream of `OSToWightman`, not inside this file. -/
theorem paley_wiener_one_step {m : ℕ}
    (C : Set (Fin m → ℝ))
    (F : (Fin m → ℂ) → ℂ)
    (r : Fin m)
    (h_slice_cont : ∀ (z' : Fin m → ℂ), (fun i => (z' i).im) ∈ C →
      Continuous (fun t : ℝ => F (Function.update z' r ↑t)))
    (h_spectral : ∀ (z' : Fin m → ℂ), (fun i => (z' i).im) ∈ C →
      HasOneSidedFourierSupport
        (fun φ : SchwartzMap ℝ ℂ => ∫ t : ℝ, F (Function.update z' r ↑t) * φ t))
    (h_growth : ∀ (z' : Fin m → ℂ), (fun i => (z' i).im) ∈ C →
      HasPolynomialGrowthOnLine (fun t => F (Function.update z' r ↑t))) :
    ∃ E : {z' : Fin m → ℂ // (fun i => (z' i).im) ∈ C} → ℂ → ℂ,
      ∀ zc,
        DifferentiableOn ℂ (E zc) upperHalfPlane ∧
        (∀ η : ℝ, 0 < η →
          HasPolynomialGrowthOnLine (fun x => E zc (↑x + ↑η * I))) ∧
        (∀ φ : SchwartzMap ℝ ℂ,
          Tendsto (fun η : ℝ => ∫ x : ℝ, E zc (↑x + ↑η * I) * φ x)
            (nhdsWithin 0 (Ioi 0))
            (nhds (∫ t : ℝ, F (Function.update zc.1 r ↑t) * φ t))) := by
  classical
  let E : {z' : Fin m → ℂ // (fun i => (z' i).im) ∈ C} → ℂ → ℂ := fun zc =>
    Classical.choose <|
      paley_wiener_one_step_simple
        (f := fun t : ℝ => F (Function.update zc.1 r ↑t))
        (h_slice_cont zc.1 zc.2)
        (h_growth zc.1 zc.2)
        (h_spectral zc.1 zc.2)
  refine ⟨E, ?_⟩
  intro zc
  exact Classical.choose_spec <|
    paley_wiener_one_step_simple
      (f := fun t : ℝ => F (Function.update zc.1 r ↑t))
      (h_slice_cont zc.1 zc.2)
      (h_growth zc.1 zc.2)
      (h_spectral zc.1 zc.2)

end SCV
