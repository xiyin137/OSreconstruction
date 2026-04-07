/-
Copyright (c) 2025 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Fourier-Laplace Core Infrastructure

This file develops the key ingredient for the Paley-Wiener theorem:
the family of Schwartz functions ψ_z(ξ) = χ(ξ) · exp(i·z·ξ) for z ∈ UHP,
where χ is a smooth cutoff function supported on [-1,∞) and equal to 1 on [0,∞).

## Main results

* `smoothCutoff` -- the smooth step function χ, defined using `Real.smoothTransition`
* `psiZ` -- the pointwise function ξ ↦ χ(ξ) · exp(i·z·ξ)
* `hasDerivAt_psiZ` -- pointwise complex derivative of `z ↦ ψ_z(ξ)`
* `psiZ_contDiff` -- smoothness of ψ_z (ContDiff ℝ ↑⊤)
* `psiZ_schwartz_decay` -- Schwartz decay of ψ_z
* `schwartzPsiZ` -- ψ_z as a SchwartzMap for Im(z) > 0
* `schwartzPsiZ_seminorm_horizontal_bound` -- polynomial seminorm growth of
  `ψ_{x+iη}` along horizontal lines
* `fourierLaplaceExt` -- the Fourier-Laplace extension F(z) = T(FT[ψ_z])

## Smoothness convention

`SchwartzMap` requires `ContDiff ℝ (↑⊤) f` where `↑⊤ = ↑(⊤ : ℕ∞) : WithTop ENat`.
This differs from `⊤ : WithTop ENat` (the omega-analytic level).
All smoothness results here use `ContDiff ℝ (↑(⊤ : ℕ∞))`.

## Proof strategy for paley_wiener_half_line

The Fourier-Laplace extension F(z) = T(FT[ψ_z]) for T ∈ S'(ℝ) with
Fourier support in [0,∞) is holomorphic on UHP. The key steps:

1. ψ_z ∈ S(ℝ) for Im(z) > 0 (main content of this file)
2. z ↦ T(FT[ψ_z]) is holomorphic (convergence of difference quotients in S)
3. BV convergence: ∫ F(x+iη)φ(x)dx → T(φ) as η→0+
   (uses HasOneSidedFourierSupport + Fourier inversion)

## References

* Hörmander, "The Analysis of Linear Partial Differential Operators I", §7.4
* Vladimirov, "Methods of the Theory of Generalized Functions", §25-26
* Reed-Simon II, Theorem IX.16
-/

noncomputable section

open Complex MeasureTheory Topology Set Filter Real SchwartzMap

namespace SCV

/-! ### The smooth cutoff function -/

/-- The smooth cutoff function χ : ℝ → ℝ, equal to 0 on (-∞,-1] and 1 on [0,∞).
    Defined using Mathlib's `Real.smoothTransition` (shifted by 1).

    χ(ξ) = smoothTransition(ξ + 1)

    Properties:
    - χ is C∞
    - 0 ≤ χ(ξ) ≤ 1 for all ξ
    - χ(ξ) = 0 for ξ ≤ -1
    - χ(ξ) = 1 for ξ ≥ 0 -/
def smoothCutoff : ℝ → ℝ := fun ξ => Real.smoothTransition (ξ + 1)

@[simp] theorem smoothCutoff_eq (ξ : ℝ) : smoothCutoff ξ = Real.smoothTransition (ξ + 1) := rfl

theorem smoothCutoff_nonneg (ξ : ℝ) : 0 ≤ smoothCutoff ξ :=
  Real.smoothTransition.nonneg _

theorem smoothCutoff_le_one (ξ : ℝ) : smoothCutoff ξ ≤ 1 :=
  Real.smoothTransition.le_one _

theorem smoothCutoff_zero_of_le_neg_one {ξ : ℝ} (h : ξ ≤ -1) : smoothCutoff ξ = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith

theorem smoothCutoff_one_of_nonneg {ξ : ℝ} (h : 0 ≤ ξ) : smoothCutoff ξ = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith

/-- χ is C∞ (ContDiff ℝ ↑⊤, matching SchwartzMap's smoothness requirement). -/
theorem smoothCutoff_contDiff : ContDiff ℝ (↑(⊤ : ℕ∞)) smoothCutoff :=
  Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)

private lemma smoothCutoff_complex_contDiff :
    ContDiff ℝ ↑(⊤ : ℕ∞) (fun ξ : ℝ => (smoothCutoff ξ : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp smoothCutoff_contDiff

/-- The complex-valued smooth cutoff `ξ ↦ (χ(ξ) : ℂ)` has tempered growth.
    This is used to multiply Schwartz functions by χ via `SchwartzMap.smulLeftCLM`.

    For n=0: `|χ(ξ)| ≤ 1` (bounded by smoothTransition range).
    For n≥1: `iteratedDeriv n χ` is supported in `[-1,0]` (smooth function constant on
    `(-∞,-1)` and `(0,∞)`), hence compactly supported and bounded. -/
theorem smoothCutoff_complex_hasTemperateGrowth :
    Function.HasTemperateGrowth (fun ξ : ℝ => (smoothCutoff ξ : ℂ)) := by
  constructor
  · exact smoothCutoff_complex_contDiff
  · intro n
    use 0
    rcases n with _ | n
    · -- n = 0: |χ(ξ)| ≤ 1
      use 1
      intro ξ
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_zero]
      simp only [mul_one, pow_zero]
      rw [Complex.norm_real, show smoothCutoff ξ = (ξ + 1).smoothTransition from rfl,
          Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    · -- n+1 ≥ 1: derivative supported in (-1,0), hence compact support → bounded
      -- On (0,∞): smoothCutoff = 1 (constant), so derivatives vanish there
      -- On (-∞,-1): smoothCutoff = 0 (constant), so derivatives vanish there
      have hEqPos : Set.EqOn (fun ξ : ℝ => (smoothCutoff ξ : ℂ)) (fun _ => 1) (Set.Ioi 0) := by
        intro ξ hξ
        simp only [Set.mem_Ioi] at hξ
        show (smoothCutoff ξ : ℂ) = 1
        exact_mod_cast smoothCutoff_one_of_nonneg (le_of_lt hξ)
      have hEqNeg : Set.EqOn (fun ξ : ℝ => (smoothCutoff ξ : ℂ)) (fun _ => 0) (Set.Iio (-1)) := by
        intro ξ hξ
        simp only [Set.mem_Iio] at hξ
        show (smoothCutoff ξ : ℂ) = 0
        exact_mod_cast smoothCutoff_zero_of_le_neg_one (le_of_lt hξ)
      have hDerivPos : Set.EqOn (iteratedDeriv (n + 1) (fun ξ : ℝ => (smoothCutoff ξ : ℂ)))
          (fun _ => 0) (Set.Ioi 0) :=
        hEqPos.iteratedDeriv_of_isOpen isOpen_Ioi (n + 1) |>.trans
          (by intro x _; simp [iteratedDeriv_const])
      have hDerivNeg : Set.EqOn (iteratedDeriv (n + 1) (fun ξ : ℝ => (smoothCutoff ξ : ℂ)))
          (fun _ => 0) (Set.Iio (-1)) :=
        hEqNeg.iteratedDeriv_of_isOpen isOpen_Iio (n + 1) |>.trans
          (by intro x _; simp)
      -- The derivative is supported in [-1,0] (compact)
      have hsupp : Function.support (iteratedDeriv (n + 1) (fun ξ : ℝ => (smoothCutoff ξ : ℂ))) ⊆
          Set.Icc (-1) 0 := by
        intro ξ hξ
        simp only [Function.mem_support] at hξ
        rw [Set.mem_Icc]
        constructor
        · by_contra h
          push_neg at h
          exact hξ (hDerivNeg (Set.mem_Iio.mpr h))
        · by_contra h
          push_neg at h
          exact hξ (hDerivPos (Set.mem_Ioi.mpr h))
      -- Continuous and compactly supported → bounded
      have hcont : Continuous (iteratedDeriv (n + 1) (fun ξ : ℝ => (smoothCutoff ξ : ℂ))) := by
        exact smoothCutoff_complex_contDiff.continuous_iteratedDeriv (n + 1)
          (by exact_mod_cast le_top)
      have hcs : HasCompactSupport (iteratedDeriv (n + 1) (fun ξ : ℝ => (smoothCutoff ξ : ℂ))) :=
        HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
      obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hcont
      use C
      intro ξ
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      simp only [mul_one, pow_zero]
      exact hC ξ

/-- χ is smooth for any order n : ℕ∞. -/
theorem smoothCutoff_contDiff_n (n : ℕ∞) : ContDiff ℝ (↑n) smoothCutoff :=
  Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)

/-! ### The Schwartz family ψ_z for Im(z) > 0 -/

/-- The pointwise function ψ_z(ξ) = χ(ξ) · exp(i·z·ξ) for z ∈ ℂ, ξ ∈ ℝ.

    For Im(z) > 0:
    - |ψ_z(ξ)| ≤ 1 on [-1,0]
    - |ψ_z(ξ)| = e^{-Im(z)ξ} for ξ ≥ 0  (Gaussian decay)
    - ψ_z(ξ) = 0 for ξ ≤ -1

    This function lies in the Schwartz space S(ℝ,ℂ) for Im(z) > 0. -/
def psiZ (z : ℂ) : ℝ → ℂ := fun ξ => smoothCutoff ξ * Complex.exp (I * z * ξ)

theorem psiZ_eq (z : ℂ) (ξ : ℝ) : psiZ z ξ = smoothCutoff ξ * Complex.exp (I * z * ξ) := rfl

/-- ψ_z vanishes for ξ ≤ -1. -/
theorem psiZ_zero_of_le_neg_one {z : ℂ} {ξ : ℝ} (h : ξ ≤ -1) : psiZ z ξ = 0 := by
  simp only [psiZ_eq, smoothCutoff_zero_of_le_neg_one h, Complex.ofReal_zero, zero_mul]

/-- ψ_z equals exp(i·z·ξ) for ξ ≥ 0. -/
theorem psiZ_eq_exp_of_nonneg {z : ℂ} {ξ : ℝ} (h : 0 ≤ ξ) :
    psiZ z ξ = Complex.exp (I * z * ξ) := by
  simp only [psiZ_eq, smoothCutoff_one_of_nonneg h, Complex.ofReal_one, one_mul]

/-- |ψ_z(ξ)| = e^{-Im(z)·ξ} for ξ ≥ 0. -/
theorem psiZ_norm_of_nonneg {z : ℂ} {ξ : ℝ} (h : 0 ≤ ξ) :
    ‖psiZ z ξ‖ = Real.exp (-(z.im * ξ)) := by
  rw [psiZ_eq_exp_of_nonneg h, Complex.norm_exp]
  simp [Complex.mul_re, Complex.I_re, Complex.I_im, mul_comm]

/-- For fixed `ξ`, the kernel `z ↦ ψ_z(ξ)` is entire with derivative
    `I * ξ * ψ_z(ξ)`. This is the pointwise complex-analytic input for the
    Fourier-Laplace extension; the remaining holomorphicity work is to show the
    difference quotient converges in the Schwartz topology after pairing with a
    tempered functional. -/
theorem hasDerivAt_psiZ (ξ : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => psiZ w ξ) (I * ξ * psiZ z ξ) z := by
  have hlin : HasDerivAt (fun w : ℂ => (I * (ξ : ℂ)) * w) (I * (ξ : ℂ)) z := by
    simpa using (hasDerivAt_const_mul (I * (ξ : ℂ)) :
      HasDerivAt (fun w : ℂ => (I * (ξ : ℂ)) * w) (I * (ξ : ℂ)) z)
  have hexp : HasDerivAt (fun w : ℂ => Complex.exp ((I * (ξ : ℂ)) * w))
      (Complex.exp ((I * (ξ : ℂ)) * z) * (I * (ξ : ℂ))) z := by
    simpa [Function.comp] using (Complex.hasDerivAt_exp ((I * (ξ : ℂ)) * z)).comp z hlin
  simpa [psiZ, mul_assoc, mul_left_comm, mul_comm] using
    (hexp.const_mul (smoothCutoff ξ : ℂ))

/-- ψ_z is C∞ (ContDiff ℝ ↑⊤). -/
theorem psiZ_contDiff (z : ℂ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (psiZ z) := by
  unfold psiZ
  apply ContDiff.mul
  · -- (smoothCutoff ξ : ℂ) is smooth via the bounded linear map ofRealCLM
    exact Complex.ofRealCLM.contDiff.comp smoothCutoff_contDiff
  · -- exp(I * z * ↑ξ) is smooth: compose exp with the linear map ξ ↦ I * z * ↑ξ
    have : (fun ξ : ℝ => Complex.exp (I * z * ↑ξ)) =
        Complex.exp ∘ (fun ξ : ℝ => I * z * ↑ξ) := rfl
    rw [this]
    apply ContDiff.comp Complex.contDiff_exp
    exact contDiff_const.mul Complex.ofRealCLM.contDiff

/-! ### Schwartz decay estimates for ψ_z -/

/-- Exponential decay dominates polynomial growth on `[0, ∞)`: for `η > 0` and `k ∈ ℕ`,
    the function `ξ ↦ ξ^k * exp (-η ξ)` is uniformly bounded on the nonnegative half-line. -/
theorem pow_mul_exp_neg_le_const {η : ℝ} (hη : 0 < η) (k : ℕ) :
    ∃ C > 0, ∀ ξ : ℝ, 0 ≤ ξ → ξ ^ k * Real.exp (-(η * ξ)) ≤ C := by
  let f : ℝ → ℝ := fun ξ => ξ ^ k * Real.exp (-(η * ξ))
  have hcont : Continuous f := by
    continuity
  have htail :
      ∀ᶠ ξ in atTop, 0 ≤ ξ ∧ f ξ < 1 := by
    have htendsto :
        Tendsto (fun ξ : ℝ => ξ ^ (k : ℝ) * Real.exp (-(η * ξ))) atTop (𝓝 0) := by
      simpa [neg_mul, mul_assoc] using
        tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) η hη
    filter_upwards [eventually_ge_atTop (0 : ℝ), htendsto.eventually (Iio_mem_nhds zero_lt_one)] with
      ξ hξ hξlt
    exact ⟨hξ, by simpa [f, Real.rpow_natCast] using hξlt⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 htail
  obtain ⟨C0, hC0⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc (0 : ℝ) N) hcont.continuousOn
  refine ⟨max C0 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro ξ hξ
  by_cases hsmall : ξ ≤ N
  · have hmem : ξ ∈ Set.Icc (0 : ℝ) N := ⟨hξ, hsmall⟩
    have hf_nonneg : 0 ≤ f ξ := by
      exact mul_nonneg (pow_nonneg hξ _) (Real.exp_pos _).le
    have habs : |ξ| = ξ := abs_of_nonneg hξ
    simpa [f, Real.norm_eq_abs, abs_of_nonneg hf_nonneg, habs] using
      (hC0 ξ hmem).trans (le_max_left _ _)
  · exact (hN ξ (le_of_not_ge hsmall)).2.le.trans (le_max_right _ _)

/-- The Schwartz decay condition for ψ_z: for Im(z) > 0, for all k n : ℕ
    there exists C such that |ξ|^k · ‖iteratedFDeriv ℝ n (ψ_z) ξ‖ ≤ C. -/
theorem psiZ_schwartz_decay (z : ℂ) (hz : 0 < z.im) :
    ∀ (k n : ℕ), ∃ C : ℝ, ∀ ξ : ℝ, ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (psiZ z) ξ‖ ≤ C := by
  intro k n
  let g : ℝ → ℝ := fun ξ => ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (psiZ z) ξ‖
  have hcont_iter : Continuous fun ξ => iteratedFDeriv ℝ n (psiZ z) ξ :=
    ContDiff.continuous_iteratedFDeriv (m := n) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))
      (by
        exact_mod_cast (show (n : ℕ∞) ≤ (⊤ : ℕ∞) by exact le_top))
      (psiZ_contDiff z)
  have hcont_g : Continuous g := by
    exact (continuous_norm.pow k).mul hcont_iter.norm
  obtain ⟨Ccomp, hCcomp⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc (-1 : ℝ) 1) hcont_g.continuousOn
  have hCcomp' :
      ∀ ξ ∈ Set.Icc (-1 : ℝ) 1, g ξ ≤ Ccomp := by
    intro ξ hξ
    simpa [g, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg ξ) _) (norm_nonneg _))] using
      hCcomp ξ hξ
  obtain ⟨Ctail, hCtail_pos, hCtail⟩ := pow_mul_exp_neg_le_const hz k
  have hiter_exp :
      ∀ m : ℕ,
        iteratedDeriv m (fun ξ : ℝ => Complex.exp ((ξ : ℂ) * (I * z))) =
          fun ξ : ℝ => (I * z) ^ m * Complex.exp ((ξ : ℂ) * (I * z)) := by
    intro m
    induction m with
    | zero =>
        ext ξ
        simp
    | succ m ih =>
        rw [iteratedDeriv_succ, ih]
        ext ξ
        have hexp_deriv : HasDerivAt (fun ξ : ℝ => Complex.exp ((ξ : ℂ) * (I * z)))
            ((I * z) * Complex.exp ((ξ : ℂ) * (I * z))) ξ := by
          refine (?_ : HasDerivAt (fun y : ℂ => Complex.exp (y * (I * z))) _ (ξ : ℂ)).comp_ofReal
          simpa [mul_comm] using
            (Complex.hasDerivAt_exp ((ξ : ℂ) * (I * z))).comp (ξ : ℂ)
              (hasDerivAt_mul_const (I * z))
        rw [(hexp_deriv.const_mul _).deriv]
        simp [pow_succ', mul_assoc, mul_left_comm, mul_comm]
  have hEqNeg : Set.EqOn (psiZ z) (fun _ : ℝ => (0 : ℂ)) (Set.Iio (-1 : ℝ)) := by
    intro ξ hξ
    exact psiZ_zero_of_le_neg_one (le_of_lt hξ)
  have hIterEqNeg := Set.EqOn.iteratedDeriv_of_isOpen hEqNeg isOpen_Iio n
  have hEqPos :
      Set.EqOn (psiZ z) (fun ξ : ℝ => Complex.exp ((ξ : ℂ) * (I * z))) (Set.Ioi (0 : ℝ)) := by
    intro ξ hξ
    rw [psiZ_eq_exp_of_nonneg (show 0 ≤ ξ by exact le_of_lt hξ)]
    congr 1
    ring
  have hIterEqPos := Set.EqOn.iteratedDeriv_of_isOpen hEqPos isOpen_Ioi n
  refine ⟨max Ccomp (‖I * z‖ ^ n * Ctail), ?_⟩
  intro ξ
  by_cases hneg : ξ < -1
  · have hzero :
        iteratedDeriv n (psiZ z) ξ = 0 := by
      simpa using hIterEqNeg hneg
    dsimp [g]
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hzero]
    have hnonneg_tail : 0 ≤ ‖I * z‖ ^ n * Ctail := by
      positivity
    exact le_trans (by simp) (le_trans hnonneg_tail (le_max_right _ _))
  · by_cases hpos : 1 < ξ
    · have hξ_nonneg : 0 ≤ ξ := by linarith
      have hiter :
          iteratedDeriv n (psiZ z) ξ = (I * z) ^ n * Complex.exp ((ξ : ℂ) * (I * z)) := by
        rw [hIterEqPos (show ξ ∈ Set.Ioi (0 : ℝ) by exact lt_trans zero_lt_one hpos)]
        simpa using congrFun (hiter_exp n) ξ
      have hexp_norm :
          ‖Complex.exp ((ξ : ℂ) * (I * z))‖ = Real.exp (-(z.im * ξ)) := by
        have hnorm := psiZ_norm_of_nonneg (z := z) (ξ := ξ) hξ_nonneg
        rw [psiZ_eq_exp_of_nonneg (z := z) (ξ := ξ) hξ_nonneg] at hnorm
        convert hnorm using 1
        ring_nf
      dsimp [g]
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hiter]
      calc
        ‖ξ‖ ^ k * ‖(I * z) ^ n * Complex.exp ((ξ : ℂ) * (I * z))‖
            = ξ ^ k * (‖I * z‖ ^ n * Real.exp (-(z.im * ξ))) := by
                rw [Real.norm_of_nonneg hξ_nonneg, norm_mul, norm_pow, hexp_norm]
        _ = ‖I * z‖ ^ n * (ξ ^ k * Real.exp (-(z.im * ξ))) := by ring
        _ ≤ ‖I * z‖ ^ n * Ctail := by
              gcongr
              exact hCtail ξ hξ_nonneg
        _ ≤ max Ccomp (‖I * z‖ ^ n * Ctail) := le_max_right _ _
    · have hmid : ξ ∈ Set.Icc (-1 : ℝ) 1 := by
        constructor <;> linarith
      exact (hCcomp' ξ hmid).trans (le_max_left _ _)

/-- Iterated derivatives of the real-parameter exponential family
    `ξ ↦ exp((ξ : ℂ) * (I * z))`. -/
theorem iteratedDeriv_cexp_real_mul (n : ℕ) (z : ℂ) :
    iteratedDeriv n (fun ξ : ℝ => Complex.exp ((ξ : ℂ) * (I * z))) =
      fun ξ : ℝ => (I * z) ^ n * Complex.exp ((ξ : ℂ) * (I * z)) := by
  induction n with
  | zero =>
      ext ξ
      simp
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      ext ξ
      have hexp_deriv : HasDerivAt (fun ξ : ℝ => Complex.exp ((ξ : ℂ) * (I * z)))
          ((I * z) * Complex.exp ((ξ : ℂ) * (I * z))) ξ := by
        refine (?_ : HasDerivAt (fun y : ℂ => Complex.exp (y * (I * z))) _ (ξ : ℂ)).comp_ofReal
        simpa [mul_comm] using
          (Complex.hasDerivAt_exp ((ξ : ℂ) * (I * z))).comp (ξ : ℂ)
            (hasDerivAt_mul_const (I * z))
      rw [(hexp_deriv.const_mul _).deriv]
      simp [pow_succ', mul_assoc, mul_left_comm, mul_comm]

/-- Iterated derivatives of the real-parameter exponential family
    `ξ ↦ exp(c * ξ)`. -/
theorem iteratedDeriv_cexp_const_mul_real (n : ℕ) (c : ℂ) :
    iteratedDeriv n (fun ξ : ℝ => Complex.exp (c * ξ)) =
      fun ξ : ℝ => c ^ n * Complex.exp (c * ξ) := by
  induction n with
  | zero =>
      ext ξ
      simp
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      ext ξ
      have hexp_deriv : HasDerivAt (fun ξ : ℝ => Complex.exp (c * ξ))
          (c * Complex.exp (c * ξ)) ξ := by
        refine (?_ : HasDerivAt (fun y : ℂ => Complex.exp (c * y)) _ (ξ : ℂ)).comp_ofReal
        simpa [mul_comm] using
          (Complex.hasDerivAt_exp (c * (ξ : ℂ))).comp (ξ : ℂ) (hasDerivAt_const_mul c)
      rw [(hexp_deriv.const_mul _).deriv]
      simp [pow_succ', mul_assoc, mul_left_comm, mul_comm]

/-- The divided first-order Taylor remainder
    `ξ ↦ (exp(I h ξ) - 1 - I h ξ) / h`. This is the scalar factor appearing in the
    complex difference quotient of `ψ_z`. -/
private def expTaylorLinearRemainderQuot (h : ℂ) : ℝ → ℂ :=
  fun ξ => (Complex.exp (I * h * ξ) - 1 - I * h * ξ) / h

private theorem iteratedDeriv_expTaylorLinearRemainderQuot_zero
    (h : ℂ) (ξ : ℝ) :
    iteratedDeriv 0 (expTaylorLinearRemainderQuot h) ξ =
      (Complex.exp (I * h * ξ) - 1 - I * h * ξ) / h := by
  simp [expTaylorLinearRemainderQuot]

private theorem iteratedDeriv_expTaylorLinearRemainderQuot_one
    (h : ℂ) (ξ : ℝ) :
    iteratedDeriv 1 (expTaylorLinearRemainderQuot h) ξ =
      I * (Complex.exp (I * h * ξ) - 1) := by
  let c : ℂ := I * h
  rw [iteratedDeriv_succ]
  simp [iteratedDeriv_zero]
  unfold expTaylorLinearRemainderQuot
  -- Compute the derivative via HasDerivAt
  have hlin : HasDerivAt (fun ξ : ℝ => c * ξ) c ξ := by
    refine (?_ : HasDerivAt (fun y : ℂ => c * y) c (ξ : ℂ)).comp_ofReal
    simpa using (hasDerivAt_const_mul c : HasDerivAt (fun y : ℂ => c * y) c (ξ : ℂ))
  have hExp : HasDerivAt (fun ξ : ℝ => Complex.exp (c * ξ))
      (c * Complex.exp (c * ξ)) ξ := by
    simpa [c, mul_assoc, mul_left_comm, mul_comm] using
      (Complex.hasDerivAt_exp (c * (ξ : ℂ))).comp ξ hlin
  have hfull : HasDerivAt (fun ξ : ℝ => (Complex.exp (c * ξ) - 1 - c * ξ) / h)
      ((c * Complex.exp (c * ξ) - c) / h) ξ := by
    exact ((hExp.sub_const 1).sub hlin).div_const h
  rw [hfull.deriv]
  by_cases hh : h = 0
  · subst hh
    simp [c]
  · field_simp [hh]
    simp [c, mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg]

private theorem iteratedDeriv_expTaylorLinearRemainderQuot_succ_succ
    (m : ℕ) (h : ℂ) (ξ : ℝ) :
    iteratedDeriv (m + 2) (expTaylorLinearRemainderQuot h) ξ =
      ((I * h) ^ (m + 2) / h) * Complex.exp (I * h * ξ) := by
  let c : ℂ := I * h
  have hderiv1 :
      deriv (expTaylorLinearRemainderQuot h) =
        fun ξ : ℝ => I * (Complex.exp (c * ξ) - 1) := by
    funext x
    simpa [c] using iteratedDeriv_expTaylorLinearRemainderQuot_one h x
  have hExpDeriv :
      ∀ x : ℝ, deriv (fun ξ : ℝ => Complex.exp (c * ξ) - 1) x =
        c * Complex.exp (c * x) := by
    intro x
    have hlin : HasDerivAt (fun ξ : ℝ => c * ξ) c x := by
      refine (?_ : HasDerivAt (fun y : ℂ => c * y) c (x : ℂ)).comp_ofReal
      simpa using (hasDerivAt_const_mul c : HasDerivAt (fun y : ℂ => c * y) c (x : ℂ))
    have hExp : HasDerivAt (fun ξ : ℝ => Complex.exp (c * ξ))
        (c * Complex.exp (c * x)) x := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Complex.hasDerivAt_exp (c * (x : ℂ))).comp x hlin
    simpa using (hExp.sub_const (1 : ℂ)).deriv
  have hderiv2 :
      deriv (fun ξ : ℝ => I * (Complex.exp (c * ξ) - 1)) =
        fun ξ : ℝ => (I * c) * Complex.exp (c * ξ) := by
    funext x
    have : HasDerivAt (fun ξ : ℝ => Complex.exp (c * ξ) - 1)
        (c * Complex.exp (c * x)) x := by
      have hlin : HasDerivAt (fun ξ : ℝ => c * ξ) c x := by
        refine (?_ : HasDerivAt (fun y : ℂ => c * y) c (x : ℂ)).comp_ofReal
        simpa using (hasDerivAt_const_mul c : HasDerivAt (fun y : ℂ => c * y) c (x : ℂ))
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        ((Complex.hasDerivAt_exp (c * (x : ℂ))).comp x hlin).sub_const 1
    rw [(this.const_mul I).deriv]
    simp [mul_assoc]
  rw [iteratedDeriv_succ', iteratedDeriv_succ']
  rw [hderiv1, hderiv2]
  calc
    iteratedDeriv m (fun ξ : ℝ => (I * c) * Complex.exp (c * ξ)) ξ
        = (I * c) * iteratedDeriv m (fun ξ : ℝ => Complex.exp (c * ξ)) ξ := by
            have := iteratedDeriv_const_mul_field (𝕜 := ℝ) (n := m) (I * c)
              (fun ξ : ℝ => Complex.exp (c * ξ)) (x := ξ)
            exact this
    _ = (I * c) * (c ^ m * Complex.exp (c * ξ)) := by
          rw [iteratedDeriv_cexp_const_mul_real]
    _ = ((I * h) ^ (m + 2) / h) * Complex.exp (I * h * ξ) := by
          by_cases hh : h = 0
          · subst hh
            simp [c]
          · have hscalar : (I * c) * c ^ m = ((I * h) ^ (m + 2)) / h := by
                have hh' : h ≠ 0 := hh
                field_simp [c, hh']
                ring
            calc
              (I * c) * (c ^ m * Complex.exp (c * ξ))
                  = ((I * c) * c ^ m) * Complex.exp (c * ξ) := by ring
              _ = (((I * h) ^ (m + 2)) / h) * Complex.exp (c * ξ) := by rw [hscalar]
              _ = (((I * h) ^ (m + 2)) / h) * Complex.exp (I * h * ξ) := by simp [c]

private theorem expTaylorLinearRemainderQuot_contDiff (h : ℂ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (expTaylorLinearRemainderQuot h) := by
  let c : ℂ := I * h
  have hexp : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun ξ : ℝ => Complex.exp ((ξ : ℂ) * c)) := by
    simpa using
      (Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.mul contDiff_const))
  have hlin : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun ξ : ℝ => (ξ : ℂ) * c) := by
    simpa using (Complex.ofRealCLM.contDiff.mul contDiff_const)
  unfold expTaylorLinearRemainderQuot
  simpa [c, div_eq_mul_inv, sub_eq_add_neg, add_assoc, mul_assoc, mul_left_comm, mul_comm] using
    (contDiff_const.mul ((hexp.sub contDiff_const).sub hlin))

private theorem norm_expTaylorLinearRemainderQuot_zero_le
    (h : ℂ) (ξ : ℝ) :
    ‖iteratedDeriv 0 (expTaylorLinearRemainderQuot h) ξ‖ ≤
      ‖h‖ * |ξ| ^ 2 * Real.exp (‖h‖ * |ξ|) := by
  rw [iteratedDeriv_expTaylorLinearRemainderQuot_zero]
  by_cases hh : h = 0
  · subst hh
    simp
  · have hmain := Complex.norm_exp_sub_sum_le_norm_mul_exp (I * h * ξ) 2
    have hnorm : ‖I * h * ξ‖ = ‖h‖ * |ξ| := by
      simp [mul_assoc, Real.norm_eq_abs]
    have hh0 : ‖h‖ ≠ 0 := by simpa [norm_eq_zero] using hh
    have hsum :
        ∑ m ∈ Finset.range 2, (I * h * ξ) ^ m / (m.factorial : ℂ) = I * h * ξ + 1 := by
      simp [Finset.sum_range_succ, add_comm]
    have hmain' :
        ‖Complex.exp (I * h * ξ) - 1 - I * h * ξ‖ ≤
          ‖I * h * ξ‖ ^ 2 * Real.exp ‖I * h * ξ‖ := by
      simpa [hsum, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmain
    calc
      ‖(Complex.exp (I * h * ξ) - 1 - I * h * ξ) / h‖
          = ‖Complex.exp (I * h * ξ) - 1 - I * h * ξ‖ / ‖h‖ := by rw [norm_div]
      _ ≤ (‖I * h * ξ‖ ^ 2 * Real.exp ‖I * h * ξ‖) / ‖h‖ := by
            gcongr
      _ = ‖h‖ * |ξ| ^ 2 * Real.exp (‖h‖ * |ξ|) := by
            rw [hnorm]
            field_simp [hh0]

private theorem norm_expTaylorLinearRemainderQuot_one_le
    (h : ℂ) (ξ : ℝ) :
    ‖iteratedDeriv 1 (expTaylorLinearRemainderQuot h) ξ‖ ≤
      ‖h‖ * |ξ| * Real.exp (‖h‖ * |ξ|) := by
  rw [iteratedDeriv_expTaylorLinearRemainderQuot_one]
  have hmain := Complex.norm_exp_sub_sum_le_norm_mul_exp (I * h * ξ) 1
  have hnorm : ‖I * h * ξ‖ = ‖h‖ * |ξ| := by
    simp [mul_assoc, Real.norm_eq_abs]
  calc
    ‖I * (Complex.exp (I * h * ξ) - 1)‖
        = ‖Complex.exp (I * h * ξ) - 1‖ := by simp
    _ ≤ ‖I * h * ξ‖ * Real.exp ‖I * h * ξ‖ := by
          simpa using hmain
    _ = ‖h‖ * |ξ| * Real.exp (‖h‖ * |ξ|) := by rw [hnorm]

private theorem norm_expTaylorLinearRemainderQuot_succ_succ_le
    (m : ℕ) (h : ℂ) (hh1 : ‖h‖ ≤ 1) (ξ : ℝ) :
    ‖iteratedDeriv (m + 2) (expTaylorLinearRemainderQuot h) ξ‖ ≤
      ‖h‖ * Real.exp (‖h‖ * |ξ|) := by
  rw [iteratedDeriv_expTaylorLinearRemainderQuot_succ_succ]
  by_cases hh : h = 0
  · subst hh
    simp
  · have hh0 : ‖h‖ ≠ 0 := by simpa [norm_eq_zero] using hh
    have hcoeff :
        ‖((I * h) ^ (m + 2) / h)‖ ≤ ‖h‖ := by
      have hpow_le : ‖h‖ ^ (m + 1) ≤ ‖h‖ := by
        cases m with
        | zero =>
            simp
        | succ m =>
            calc
              ‖h‖ ^ (Nat.succ (Nat.succ m)) = ‖h‖ ^ (Nat.succ m) * ‖h‖ := by
                rw [pow_succ]
              _ ≤ 1 * ‖h‖ := by
                gcongr
                exact pow_le_one₀ (norm_nonneg _) hh1
              _ = ‖h‖ := by ring
      calc
        ‖((I * h) ^ (m + 2) / h)‖
            = ‖h‖ ^ (m + 1) := by
                rw [norm_div, norm_pow, norm_mul, Complex.norm_I, one_mul]
                field_simp [hh0]
                ring
        _ ≤ ‖h‖ := hpow_le
    have hexp :
        ‖Complex.exp (I * h * ξ)‖ ≤ Real.exp (‖h‖ * |ξ|) := by
      calc
        ‖Complex.exp (I * h * ξ)‖ ≤ Real.exp ‖I * h * ξ‖ := Complex.norm_exp_le_exp_norm _
        _ = Real.exp (‖h‖ * |ξ|) := by
              congr 1
              simp [mul_assoc, Real.norm_eq_abs]
    calc
      ‖((I * h) ^ (m + 2) / h) * Complex.exp (I * h * ξ)‖
          = ‖((I * h) ^ (m + 2) / h)‖ * ‖Complex.exp (I * h * ξ)‖ := by rw [norm_mul]
      _ ≤ ‖h‖ * Real.exp (‖h‖ * |ξ|) := by gcongr

private theorem norm_expTaylorLinearRemainderQuot_tail_le
    (j : ℕ) (h : ℂ) (hh1 : ‖h‖ ≤ 1) (ξ : ℝ) (hξ1 : 1 ≤ ξ) :
    ‖iteratedDeriv j (expTaylorLinearRemainderQuot h) ξ‖ ≤
      ‖h‖ * ξ ^ 2 * Real.exp (‖h‖ * ξ) := by
  have hξ_nonneg : 0 ≤ ξ := le_trans (by norm_num) hξ1
  obtain rfl | rfl | m := j
  · calc
      ‖iteratedDeriv 0 (expTaylorLinearRemainderQuot h) ξ‖
          ≤ ‖h‖ * |ξ| ^ 2 * Real.exp (‖h‖ * |ξ|) := norm_expTaylorLinearRemainderQuot_zero_le h ξ
      _ = ‖h‖ * ξ ^ 2 * Real.exp (‖h‖ * ξ) := by simp [abs_of_nonneg hξ_nonneg]
  · calc
      ‖iteratedDeriv 1 (expTaylorLinearRemainderQuot h) ξ‖
          ≤ ‖h‖ * |ξ| * Real.exp (‖h‖ * |ξ|) := norm_expTaylorLinearRemainderQuot_one_le h ξ
      _ = ‖h‖ * ξ * Real.exp (‖h‖ * ξ) := by simp [abs_of_nonneg hξ_nonneg]
      _ ≤ ‖h‖ * ξ ^ 2 * Real.exp (‖h‖ * ξ) := by
            have hmul :
                ξ * Real.exp (‖h‖ * ξ) ≤ ξ ^ 2 * Real.exp (‖h‖ * ξ) := by
              refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
              nlinarith [hξ1]
            have := mul_le_mul_of_nonneg_left hmul (norm_nonneg h)
            simpa [mul_assoc, mul_left_comm, mul_comm] using this
  · calc
      ‖iteratedDeriv (Nat.succ (Nat.succ m)) (expTaylorLinearRemainderQuot h) ξ‖
          ≤ ‖h‖ * Real.exp (‖h‖ * |ξ|) := norm_expTaylorLinearRemainderQuot_succ_succ_le m h hh1 ξ
      _ = ‖h‖ * Real.exp (‖h‖ * ξ) := by simp [abs_of_nonneg hξ_nonneg]
      _ ≤ ‖h‖ * ξ ^ 2 * Real.exp (‖h‖ * ξ) := by
            have hmul :
                Real.exp (‖h‖ * ξ) ≤ ξ ^ 2 * Real.exp (‖h‖ * ξ) := by
              simpa [one_mul] using
                (mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ ξ ^ 2 by nlinarith [hξ1])
                  (Real.exp_pos _).le)
            have := mul_le_mul_of_nonneg_left hmul (norm_nonneg h)
            simpa [mul_assoc, mul_left_comm, mul_comm] using this

private theorem norm_expTaylorLinearRemainderQuot_mid_le
    (j : ℕ) (h : ℂ) (hh1 : ‖h‖ ≤ 1) (ξ : ℝ) (hξ : ξ ∈ Set.Icc (-1 : ℝ) 1) :
    ‖iteratedDeriv j (expTaylorLinearRemainderQuot h) ξ‖ ≤
      Real.exp 1 * ‖h‖ := by
  have hξ_abs_le : |ξ| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [hξ.1, hξ.2]
  have hexp_le : Real.exp (‖h‖ * |ξ|) ≤ Real.exp 1 := by
    apply Real.exp_le_exp.mpr
    nlinarith [norm_nonneg h, hξ_abs_le, hh1]
  obtain rfl | rfl | m := j
  · calc
      ‖iteratedDeriv 0 (expTaylorLinearRemainderQuot h) ξ‖
          ≤ ‖h‖ * |ξ| ^ 2 * Real.exp (‖h‖ * |ξ|) := norm_expTaylorLinearRemainderQuot_zero_le h ξ
      _ ≤ ‖h‖ * (1 : ℝ) * Real.exp 1 := by
            gcongr
            exact pow_le_one₀ (abs_nonneg ξ) hξ_abs_le
      _ = Real.exp 1 * ‖h‖ := by ring
  · calc
      ‖iteratedDeriv 1 (expTaylorLinearRemainderQuot h) ξ‖
          ≤ ‖h‖ * |ξ| * Real.exp (‖h‖ * |ξ|) := norm_expTaylorLinearRemainderQuot_one_le h ξ
      _ ≤ ‖h‖ * (1 : ℝ) * Real.exp 1 := by
            gcongr
      _ = Real.exp 1 * ‖h‖ := by ring
  · calc
      ‖iteratedDeriv (Nat.succ (Nat.succ m)) (expTaylorLinearRemainderQuot h) ξ‖
          ≤ ‖h‖ * Real.exp (‖h‖ * |ξ|) := norm_expTaylorLinearRemainderQuot_succ_succ_le m h hh1 ξ
      _ ≤ ‖h‖ * Real.exp 1 := by gcongr
      _ = Real.exp 1 * ‖h‖ := by ring

/-- The kernel difference `ψ_{z+h} - ψ_z - h (I ξ ψ_z)` factors through the
    local remainder kernel. This is the exact algebraic identity used later in
    the scalar Fourier-Laplace derivative proof. -/
theorem psiZ_sub_sub_deriv_eq_smul_remainder
    (z h : ℂ) (ξ : ℝ) :
    psiZ (z + h) ξ - psiZ z ξ - h * (I * ξ * psiZ z ξ) =
      h * (psiZ z ξ * expTaylorLinearRemainderQuot h ξ) := by
  by_cases hh : h = 0
  · subst hh
    simp [expTaylorLinearRemainderQuot]
  · have hshift :
      psiZ (z + h) ξ = psiZ z ξ * Complex.exp (I * h * ξ) := by
      unfold psiZ
      rw [show I * (z + h) * ξ = I * z * ξ + I * h * ξ by ring]
      rw [Complex.exp_add]
      ring
    rw [hshift]
    unfold expTaylorLinearRemainderQuot
    field_simp [hh]

/-- For `Im(z) > 0`, the kernel remainder
    `ξ ↦ ψ_z(ξ) * (exp(I h ξ) - 1 - I h ξ) / h`
    is Schwartz for all sufficiently small `h`, with every Schwartz seminorm
    bounded uniformly by `O(‖h‖)`.

    This is the local analytic estimate needed for the difference quotient of
    `z ↦ ψ_z` in the Schwartz topology: after dividing by `h` and subtracting
    the candidate derivative `ξ ↦ I ξ ψ_z(ξ)`, the remainder is exactly of
    this form and tends to zero linearly in `‖h‖`, with a constant depending
    only on `z`, `k`, and `n`. -/
theorem psiZ_expTaylorLinearRemainderQuot_decay
    (z : ℂ) (hz : 0 < z.im) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℂ, ‖h‖ ≤ z.im / 2 → ‖h‖ ≤ 1 → ∀ ξ : ℝ,
      |ξ| ^ k *
          ‖iteratedDeriv n (fun t : ℝ => psiZ z t * expTaylorLinearRemainderQuot h t) ξ‖ ≤
        C * ‖h‖ := by
  have hA :
      ∀ i : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ ξ : ℝ, ‖iteratedDeriv i (psiZ z) ξ‖ ≤ A := by
    intro i
    obtain ⟨A, hA⟩ := psiZ_schwartz_decay z hz 0 i
    refine ⟨max A 0, le_max_right _ _, ?_⟩
    intro ξ
    have hAξ : ‖iteratedDeriv i (psiZ z) ξ‖ ≤ A := by
      simpa [pow_zero, one_mul, Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hA ξ
    exact hAξ.trans (le_max_left _ _)
  choose A hA_nonneg hA_bound using hA
  obtain ⟨Ctail, hCtail_pos, hCtail⟩ :=
    pow_mul_exp_neg_le_const (show 0 < z.im / 2 by positivity) (k + 2)
  let Cmid : ℝ :=
    ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℝ) * A i * Real.exp 1)
  let CtailAll : ℝ :=
    ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℝ) * ‖I * z‖ ^ i * Ctail)
  let C : ℝ := Cmid + CtailAll
  have hCmid_nonneg : 0 ≤ Cmid := by
    dsimp [Cmid]
    refine Finset.sum_nonneg ?_
    intro i hi
    exact mul_nonneg
      (mul_nonneg (by exact_mod_cast Nat.zero_le (n.choose i)) (hA_nonneg i))
      (Real.exp_pos 1).le
  have hCtailAll_nonneg : 0 ≤ CtailAll := by
    dsimp [CtailAll]
    refine Finset.sum_nonneg ?_
    intro i hi
    exact mul_nonneg
      (mul_nonneg (by exact_mod_cast Nat.zero_le (n.choose i)) (pow_nonneg (norm_nonneg _) _))
      hCtail_pos.le
  refine ⟨C, add_nonneg hCmid_nonneg hCtailAll_nonneg, ?_⟩
  intro h hh_im hh1
  let f : ℝ → ℂ := fun t => psiZ z t * expTaylorLinearRemainderQuot h t
  intro ξ
  by_cases hneg : ξ < -1
  · have hEqNeg :
        Set.EqOn f (fun _ : ℝ => (0 : ℂ)) (Set.Iio (-1 : ℝ)) := by
        intro t ht
        simp [f, psiZ_zero_of_le_neg_one (le_of_lt ht)]
    have hIterEqNeg := Set.EqOn.iteratedDeriv_of_isOpen hEqNeg isOpen_Iio n
    have hzero : iteratedDeriv n f ξ = 0 := by
      simpa using hIterEqNeg hneg
    calc
      |ξ| ^ k * ‖iteratedDeriv n f ξ‖ = 0 := by simp [hzero]
      _ ≤ C * ‖h‖ := by
            exact mul_nonneg (add_nonneg hCmid_nonneg hCtailAll_nonneg) (norm_nonneg h)
  · by_cases hlarge : 1 < ξ
    · let e : ℝ → ℂ := fun t => Complex.exp (I * z * t)
      let r : ℝ → ℂ := expTaylorLinearRemainderQuot h
      have hEqPos : Set.EqOn f (fun t : ℝ => e t * r t) (Set.Ioi (0 : ℝ)) := by
        intro t ht
        simp [f, e, r, psiZ_eq_exp_of_nonneg (le_of_lt ht)]
      have hIterEqPos := Set.EqOn.iteratedDeriv_of_isOpen hEqPos isOpen_Ioi n
      have hξ_nonneg : 0 ≤ ξ := by linarith
      have hξ_abs : |ξ| = ξ := abs_of_nonneg hξ_nonneg
      have hmul :
          iteratedDeriv n (fun t : ℝ => e t * r t) ξ =
            ∑ i ∈ Finset.range (n + 1),
              n.choose i * iteratedDeriv i e ξ * iteratedDeriv (n - i) r ξ := by
        have he_contDiff : ContDiff ℝ (↑(⊤ : ℕ∞)) e := by
          simpa [e] using
            (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff))
        have he_at : ContDiffAt ℝ n e ξ :=
          he_contDiff.contDiffAt.of_le
            (show (n : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by
              exact mod_cast le_top)
        have hr_at : ContDiffAt ℝ n r ξ :=
          (expTaylorLinearRemainderQuot_contDiff h).contDiffAt.of_le
            (show (n : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by
              exact mod_cast le_top)
        simpa [e, r] using iteratedDeriv_mul (x := ξ) he_at hr_at
      have htail_term :
          ∀ i ∈ Finset.range (n + 1),
            |ξ| ^ k *
                ‖n.choose i * iteratedDeriv i e ξ * iteratedDeriv (n - i) r ξ‖ ≤
              ((n.choose i : ℝ) * ‖I * z‖ ^ i * Ctail) * ‖h‖ := by
        intro i hi
        have hExpDeriv :
            ‖iteratedDeriv i e ξ‖ = ‖I * z‖ ^ i * Real.exp (-(z.im * ξ)) := by
          rw [show e = (fun t : ℝ => Complex.exp (I * z * t)) by rfl,
            iteratedDeriv_cexp_const_mul_real i (I * z)]
          rw [norm_mul, norm_pow, Complex.norm_exp]
          congr 2
          have hre : Complex.re (I * z * ξ) = -(z.im * ξ) := by
            simp [Complex.mul_re, Complex.I_re, Complex.I_im]
          exact hre
        have hRem :
            ‖iteratedDeriv (n - i) r ξ‖ ≤ ‖h‖ * ξ ^ 2 * Real.exp (‖h‖ * ξ) :=
          norm_expTaylorLinearRemainderQuot_tail_le (j := n - i) h hh1 ξ (by linarith)
        have hexp_comb :
            Real.exp (-(z.im * ξ)) * Real.exp (‖h‖ * ξ) ≤
              Real.exp (-((z.im / 2) * ξ)) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          nlinarith
        calc
          |ξ| ^ k * ‖n.choose i * iteratedDeriv i e ξ * iteratedDeriv (n - i) r ξ‖
              = ξ ^ k *
                  ((n.choose i : ℝ) * ‖iteratedDeriv i e ξ‖ *
                    ‖iteratedDeriv (n - i) r ξ‖) := by
                    simp [hξ_abs, mul_assoc]
          _ ≤ ξ ^ k *
                ((n.choose i : ℝ) *
                  (‖I * z‖ ^ i * Real.exp (-(z.im * ξ))) *
                  (‖h‖ * ξ ^ 2 * Real.exp (‖h‖ * ξ))) := by
                    rw [hExpDeriv]
                    gcongr
          _ = ((n.choose i : ℝ) * ‖I * z‖ ^ i) *
                (ξ ^ (k + 2) *
                  (Real.exp (-(z.im * ξ)) * Real.exp (‖h‖ * ξ))) * ‖h‖ := by
                    ring_nf
          _ ≤ ((n.choose i : ℝ) * ‖I * z‖ ^ i) *
                (ξ ^ (k + 2) * Real.exp (-((z.im / 2) * ξ))) * ‖h‖ := by
                    gcongr
          _ ≤ ((n.choose i : ℝ) * ‖I * z‖ ^ i) * Ctail * ‖h‖ := by
                    gcongr
                    exact hCtail ξ hξ_nonneg
          _ = ((n.choose i : ℝ) * ‖I * z‖ ^ i * Ctail) * ‖h‖ := by
                    ring
      calc
        |ξ| ^ k * ‖iteratedDeriv n f ξ‖
            = ξ ^ k * ‖iteratedDeriv n (fun t : ℝ => e t * r t) ξ‖ := by
                rw [hξ_abs, hIterEqPos (show ξ ∈ Set.Ioi (0 : ℝ) by
                  exact lt_trans zero_lt_one hlarge)]
        _ = ξ ^ k *
              ‖∑ i ∈ Finset.range (n + 1),
                  n.choose i * iteratedDeriv i e ξ * iteratedDeriv (n - i) r ξ‖ := by
                rw [hmul]
        _ ≤ ξ ^ k *
              ∑ i ∈ Finset.range (n + 1),
                ‖n.choose i * iteratedDeriv i e ξ * iteratedDeriv (n - i) r ξ‖ := by
                have hξk_nonneg : 0 ≤ ξ ^ k := pow_nonneg hξ_nonneg _
                gcongr
                exact norm_sum_le _ _
        _ = ∑ i ∈ Finset.range (n + 1),
              ξ ^ k *
                ‖n.choose i * iteratedDeriv i e ξ * iteratedDeriv (n - i) r ξ‖ := by
                rw [Finset.mul_sum]
        _ = ∑ i ∈ Finset.range (n + 1),
              |ξ| ^ k *
                ‖n.choose i * iteratedDeriv i e ξ * iteratedDeriv (n - i) r ξ‖ := by
                simp [hξ_abs]
        _ ≤ ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℝ) * ‖I * z‖ ^ i * Ctail) * ‖h‖ := by
              refine Finset.sum_le_sum ?_
              intro i hi
              exact htail_term i hi
        _ = CtailAll * ‖h‖ := by
              dsimp [CtailAll]
              rw [Finset.sum_mul]
        _ ≤ C * ‖h‖ := by
              have hle : CtailAll ≤ C := by
                dsimp [C]
                linarith
              exact mul_le_mul_of_nonneg_right hle (norm_nonneg h)
    · have hξ_mem : ξ ∈ Set.Icc (-1 : ℝ) 1 := by
        constructor <;> linarith
      have hξ_abs_le : |ξ| ≤ 1 := by
        rw [abs_le]
        constructor <;> nlinarith [hξ_mem.1, hξ_mem.2]
      have hξ_pow_le : |ξ| ^ k ≤ 1 := by
        exact pow_le_one₀ (abs_nonneg ξ) hξ_abs_le
      have hmul :
          iteratedDeriv n f ξ =
            ∑ i ∈ Finset.range (n + 1),
              n.choose i * iteratedDeriv i (psiZ z) ξ *
                iteratedDeriv (n - i) (expTaylorLinearRemainderQuot h) ξ := by
        have hpsi_at : ContDiffAt ℝ n (psiZ z) ξ :=
          (psiZ_contDiff z).contDiffAt.of_le
            (show (n : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by
              exact mod_cast le_top)
        have hr_at : ContDiffAt ℝ n (expTaylorLinearRemainderQuot h) ξ :=
          (expTaylorLinearRemainderQuot_contDiff h).contDiffAt.of_le
            (show (n : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by
              exact mod_cast le_top)
        simpa [f] using iteratedDeriv_mul (x := ξ) hpsi_at hr_at
      calc
        |ξ| ^ k * ‖iteratedDeriv n f ξ‖
            ≤ ‖iteratedDeriv n f ξ‖ := by
                nlinarith [norm_nonneg (iteratedDeriv n f ξ), hξ_pow_le]
        _ = ‖∑ i ∈ Finset.range (n + 1),
              n.choose i * iteratedDeriv i (psiZ z) ξ *
                iteratedDeriv (n - i) (expTaylorLinearRemainderQuot h) ξ‖ := by
              rw [hmul]
        _ ≤ ∑ i ∈ Finset.range (n + 1),
              ‖n.choose i * iteratedDeriv i (psiZ z) ξ *
                iteratedDeriv (n - i) (expTaylorLinearRemainderQuot h) ξ‖ := by
              exact norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.range (n + 1),
              ((n.choose i : ℝ) * A i * Real.exp 1) * ‖h‖ := by
              refine Finset.sum_le_sum ?_
              intro i hi
              have hAi : ‖iteratedDeriv i (psiZ z) ξ‖ ≤ A i := hA_bound i ξ
              have hRi :
                  ‖iteratedDeriv (n - i) (expTaylorLinearRemainderQuot h) ξ‖ ≤
                    Real.exp 1 * ‖h‖ :=
                norm_expTaylorLinearRemainderQuot_mid_le (j := n - i) h hh1 ξ hξ_mem
              calc
                ‖n.choose i * iteratedDeriv i (psiZ z) ξ *
                    iteratedDeriv (n - i) (expTaylorLinearRemainderQuot h) ξ‖
                    = (n.choose i : ℝ) * ‖iteratedDeriv i (psiZ z) ξ‖ *
                        ‖iteratedDeriv (n - i) (expTaylorLinearRemainderQuot h) ξ‖ := by
                          simp [mul_assoc]
                _ ≤ (n.choose i : ℝ) * A i * (Real.exp 1 * ‖h‖) := by
                      have hchoose_nonneg : 0 ≤ (n.choose i : ℝ) := by
                        exact_mod_cast Nat.zero_le (n.choose i)
                      calc
                        (n.choose i : ℝ) * ‖iteratedDeriv i (psiZ z) ξ‖ *
                            ‖iteratedDeriv (n - i) (expTaylorLinearRemainderQuot h) ξ‖
                            = (n.choose i : ℝ) *
                                (‖iteratedDeriv i (psiZ z) ξ‖ *
                                  ‖iteratedDeriv (n - i) (expTaylorLinearRemainderQuot h) ξ‖) := by
                                    ring
                        _ ≤ (n.choose i : ℝ) * (A i * (Real.exp 1 * ‖h‖)) := by
                              refine mul_le_mul_of_nonneg_left ?_ hchoose_nonneg
                              exact mul_le_mul hAi hRi (norm_nonneg _) (hA_nonneg i)
                        _ = (n.choose i : ℝ) * A i * (Real.exp 1 * ‖h‖) := by
                              ring
                _ = ((n.choose i : ℝ) * A i * Real.exp 1) * ‖h‖ := by
                      ring
        _ = Cmid * ‖h‖ := by
              dsimp [Cmid]
              rw [Finset.sum_mul]
        _ ≤ C * ‖h‖ := by
              have hle : Cmid ≤ C := by
                dsimp [C]
                linarith
              exact mul_le_mul_of_nonneg_right hle (norm_nonneg h)

/-- The local remainder kernel in the complex difference quotient of `ψ_z`,
    packaged as a Schwartz function under the smallness assumptions on `h`. -/
noncomputable def schwartzPsiZExpTaylorLinearRemainderQuot
    (z : ℂ) (hz : 0 < z.im) (h : ℂ)
    (hh_im : ‖h‖ ≤ z.im / 2) (hh1 : ‖h‖ ≤ 1) : SchwartzMap ℝ ℂ :=
  ⟨fun t : ℝ => psiZ z t * expTaylorLinearRemainderQuot h t,
    (psiZ_contDiff z).mul (expTaylorLinearRemainderQuot_contDiff h),
    by
      intro k n
      obtain ⟨C, _, hC⟩ := psiZ_expTaylorLinearRemainderQuot_decay z hz k n
      refine ⟨max (C * ‖h‖) 0, ?_⟩
      intro ξ
      simpa [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] using
        (hC h hh_im hh1 ξ).trans (le_max_left _ _)⟩

@[simp] theorem schwartzPsiZExpTaylorLinearRemainderQuot_apply
    (z : ℂ) (hz : 0 < z.im) (h : ℂ)
    (hh_im : ‖h‖ ≤ z.im / 2) (hh1 : ‖h‖ ≤ 1) (ξ : ℝ) :
    schwartzPsiZExpTaylorLinearRemainderQuot z hz h hh_im hh1 ξ =
      psiZ z ξ * expTaylorLinearRemainderQuot h ξ := rfl

/-- Every Schwartz seminorm of the local remainder kernel is `O(‖h‖)`. -/
theorem schwartzPsiZExpTaylorLinearRemainderQuot_seminorm_le
    (z : ℂ) (hz : 0 < z.im) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℂ) (hh_im : ‖h‖ ≤ z.im / 2) (hh1 : ‖h‖ ≤ 1),
      SchwartzMap.seminorm ℝ k n
        (schwartzPsiZExpTaylorLinearRemainderQuot z hz h hh_im hh1) ≤
          C * ‖h‖ := by
  obtain ⟨C, hC_nonneg, hC⟩ := psiZ_expTaylorLinearRemainderQuot_decay z hz k n
  refine ⟨C, hC_nonneg, ?_⟩
  intro h hh_im hh1
  refine SchwartzMap.seminorm_le_bound' (𝕜 := ℝ) k n
    (schwartzPsiZExpTaylorLinearRemainderQuot z hz h hh_im hh1)
    (mul_nonneg hC_nonneg (norm_nonneg h)) ?_
  intro ξ
  simpa [schwartzPsiZExpTaylorLinearRemainderQuot] using hC h hh_im hh1 ξ

/-- ψ_z as a SchwartzMap for Im(z) > 0. -/
noncomputable def schwartzPsiZ (z : ℂ) (hz : 0 < z.im) : SchwartzMap ℝ ℂ :=
  ⟨psiZ z, psiZ_contDiff z, psiZ_schwartz_decay z hz⟩

@[simp] theorem schwartzPsiZ_apply (z : ℂ) (hz : 0 < z.im) (ξ : ℝ) :
    schwartzPsiZ z hz ξ = psiZ z ξ := rfl

/-- Along a fixed horizontal line in the upper half-plane, each Schwartz seminorm of `ψ_z`
    grows at most polynomially in the real part of `z`. -/
theorem schwartzPsiZ_seminorm_horizontal_bound
    (η : ℝ) (hη : 0 < η) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      SchwartzMap.seminorm ℝ k n
        (schwartzPsiZ ((x : ℂ) + η * I) (by simpa using hη)) ≤
          C * (1 + |x|) ^ n := by
  classical
  let χ : ℝ → ℂ := fun ξ => smoothCutoff ξ
  have hχ_contDiff : ContDiff ℝ (↑(⊤ : ℕ∞)) χ := by
    simpa [χ] using (Complex.ofRealCLM.contDiff.comp smoothCutoff_contDiff)
  have hB :
      ∀ i : ℕ, ∃ B : ℝ, 0 ≤ B ∧
        ∀ ξ ∈ Set.Icc (-1 : ℝ) 1, ‖iteratedDeriv i χ ξ‖ ≤ B := by
    intro i
    obtain ⟨B, hB⟩ :=
      isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc (-1 : ℝ) 1)
        ((hχ_contDiff.continuous_iteratedDeriv i
          (show (i : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by
            exact mod_cast le_top)).norm.continuousOn)
    refine ⟨B, ?_, ?_⟩
    · have h0 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by simp
      exact le_trans (norm_nonneg _) (by simpa using hB 0 h0)
    · intro ξ hξ
      simpa using hB ξ hξ
  choose B hB_nonneg hB_bound using hB
  obtain ⟨Ctail, hCtail_pos, hCtail⟩ := pow_mul_exp_neg_le_const hη k
  let Cmid : ℝ :=
    ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * B i * (η + 2) ^ n * Real.exp η
  let CtailAll : ℝ := (η + 2) ^ n * Ctail
  let C : ℝ := max Cmid CtailAll
  have hC_nonneg : 0 ≤ C := by
    have hCmid_nonneg : 0 ≤ Cmid := by
      refine Finset.sum_nonneg ?_
      intro i hi
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by exact_mod_cast Nat.cast_nonneg (n.choose i)) (hB_nonneg i))
          (pow_nonneg (by linarith : 0 ≤ η + 2) _))
        (Real.exp_pos η).le
    exact le_trans hCmid_nonneg (le_max_left _ _)
  refine ⟨C, hC_nonneg, ?_⟩
  intro x
  let z : ℂ := (x : ℂ) + η * I
  let u : ℝ := 1 + |x|
  have hu_nonneg : 0 ≤ u := by
    have hx : 0 ≤ |x| := abs_nonneg x
    linarith
  have hz : 0 < z.im := by
    simpa [z] using hη
  have hz_norm_le : ‖I * z‖ ≤ (η + 1) * u := by
    calc
      ‖I * z‖ = ‖z‖ := by simp
      _ ≤ ‖(x : ℂ)‖ + ‖η * I‖ := norm_add_le _ _
      _ = |x| + η := by simp [Real.norm_eq_abs, abs_of_pos hη]
      _ ≤ (η + 1) * u := by
        nlinarith [abs_nonneg x, hη]
  have hz_pow_le :
      ∀ m : ℕ, m ≤ n → ‖I * z‖ ^ m ≤ (η + 2) ^ n * u ^ n := by
    intro m hm
    have h1 : 1 + ‖I * z‖ ≤ (η + 2) * u := by
      have haux : 1 + ‖I * z‖ ≤ 1 + (η + 1) * u := by linarith [hz_norm_le]
      have haux' : 1 + (η + 1) * u ≤ (η + 2) * u := by
        have hu_ge_one : 1 ≤ u := by
          have hx : 0 ≤ |x| := abs_nonneg x
          linarith
        linarith
      exact le_trans haux haux'
    calc
      ‖I * z‖ ^ m ≤ (1 + ‖I * z‖) ^ m := by
        exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
      _ ≤ (1 + ‖I * z‖) ^ n := by
        have hbase : 1 ≤ 1 + ‖I * z‖ := by
          have hnorm : 0 ≤ ‖I * z‖ := norm_nonneg _
          linarith
        exact pow_le_pow_right₀ hbase hm
      _ ≤ ((η + 2) * u) ^ n := by
        exact pow_le_pow_left₀ (by positivity) h1 _
      _ = (η + 2) ^ n * u ^ n := by
        rw [mul_pow]
  refine SchwartzMap.seminorm_le_bound' (𝕜 := ℝ) k n (schwartzPsiZ z hz)
    (mul_nonneg hC_nonneg (pow_nonneg hu_nonneg _)) ?_
  intro ξ
  by_cases hneg : ξ < -1
  · have hEqNeg : Set.EqOn (psiZ z) (fun _ : ℝ => (0 : ℂ)) (Set.Iio (-1 : ℝ)) := by
      intro t ht
      exact psiZ_zero_of_le_neg_one (le_of_lt ht)
    have hIterEqNeg := Set.EqOn.iteratedDeriv_of_isOpen hEqNeg isOpen_Iio n
    have hzero : iteratedDeriv n (psiZ z) ξ = 0 := by
      simpa using hIterEqNeg hneg
    calc
      |ξ| ^ k * ‖iteratedDeriv n (psiZ z) ξ‖ = 0 := by simp [hzero]
      _ ≤ C * u ^ n := by
        exact mul_nonneg hC_nonneg (pow_nonneg hu_nonneg _)
  · by_cases hlarge : 1 < ξ
    · have hξ_nonneg : 0 ≤ ξ := by linarith
      have hEqPos :
          Set.EqOn (psiZ z) (fun t : ℝ => Complex.exp (I * z * t)) (Set.Ioi (0 : ℝ)) := by
        intro t ht
        rw [psiZ_eq_exp_of_nonneg (show 0 ≤ t by exact le_of_lt ht)]
      have hIterEqPos := Set.EqOn.iteratedDeriv_of_isOpen hEqPos isOpen_Ioi n
      have hiter :
          iteratedDeriv n (psiZ z) ξ =
            (I * z) ^ n * Complex.exp (I * z * ξ) := by
        rw [hIterEqPos (show ξ ∈ Set.Ioi (0 : ℝ) by exact lt_trans zero_lt_one hlarge)]
        simpa using congrFun (iteratedDeriv_cexp_const_mul_real n (I * z)) ξ
      have hexp_norm :
          ‖Complex.exp (I * z * ξ)‖ = Real.exp (-(η * ξ)) := by
        rw [Complex.norm_exp]
        have hre : Complex.re (I * z * ξ) = -(η * ξ) := by
          simp [z, Complex.mul_re, Complex.I_re, Complex.I_im]
        rw [hre]
      calc
        |ξ| ^ k * ‖iteratedDeriv n (psiZ z) ξ‖
            = ξ ^ k * (‖I * z‖ ^ n * Real.exp (-(η * ξ))) := by
                rw [hiter, abs_of_nonneg hξ_nonneg, norm_mul, norm_pow, hexp_norm]
        _ = ‖I * z‖ ^ n * (ξ ^ k * Real.exp (-(η * ξ))) := by ring
        _ ≤ ‖I * z‖ ^ n * Ctail := by
              gcongr
              exact hCtail ξ hξ_nonneg
        _ ≤ ((η + 2) ^ n * u ^ n) * Ctail := by
              gcongr
              exact hz_pow_le n le_rfl
        _ = CtailAll * u ^ n := by
              simp [CtailAll, mul_left_comm, mul_comm]
        _ ≤ C * u ^ n := by
              gcongr
              exact le_max_right _ _
    · have hξ_mem : ξ ∈ Set.Icc (-1 : ℝ) 1 := by
        constructor <;> linarith
      have hξ_abs_le : |ξ| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith
      have hξ_pow_le : |ξ| ^ k ≤ 1 := by
        exact pow_le_one₀ (abs_nonneg ξ) hξ_abs_le
      let e : ℝ → ℂ := fun t => Complex.exp (I * z * t)
      have he_contDiff : ContDiff ℝ (↑(⊤ : ℕ∞)) e := by
        simpa [e] using
          (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff))
      have hψε : psiZ z = χ * e := by
        funext t
        rfl
      have hmul :
          iteratedDeriv n (psiZ z) ξ =
            ∑ i ∈ Finset.range (n + 1),
              n.choose i * iteratedDeriv i χ ξ * iteratedDeriv (n - i) e ξ := by
        have hχ_at : ContDiffAt ℝ n χ ξ :=
          (hχ_contDiff.contDiffAt.of_le (show (n : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by
            exact mod_cast le_top))
        have he_at : ContDiffAt ℝ n e ξ :=
          (he_contDiff.contDiffAt.of_le (show (n : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by
            exact mod_cast le_top))
        rw [hψε]
        simpa [χ, e] using iteratedDeriv_mul (x := ξ) hχ_at he_at
      have hexp_mid :
          ‖Complex.exp (I * z * ξ)‖ ≤ Real.exp η := by
        rw [Complex.norm_exp]
        have hre : Complex.re (I * z * ξ) = -(η * ξ) := by
          simp [z, Complex.mul_re, Complex.I_re, Complex.I_im]
        rw [hre]
        apply Real.exp_le_exp.mpr
        nlinarith [hη, hξ_mem.1]
      calc
        |ξ| ^ k * ‖iteratedDeriv n (psiZ z) ξ‖
            ≤ ‖iteratedDeriv n (psiZ z) ξ‖ := by
                nlinarith [norm_nonneg (iteratedDeriv n (psiZ z) ξ), hξ_pow_le]
        _ = ‖∑ i ∈ Finset.range (n + 1),
              n.choose i * iteratedDeriv i χ ξ * iteratedDeriv (n - i) e ξ‖ := by
              rw [hmul]
        _ ≤ ∑ i ∈ Finset.range (n + 1),
              ‖n.choose i * iteratedDeriv i χ ξ * iteratedDeriv (n - i) e ξ‖ := by
              exact norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.range (n + 1),
              ((n.choose i : ℝ) * B i * (η + 2) ^ n * Real.exp η) * u ^ n := by
              refine Finset.sum_le_sum ?_
              intro i hi
              have hBi : ‖iteratedDeriv i χ ξ‖ ≤ B i := hB_bound i ξ hξ_mem
              have hpow_i : ‖I * z‖ ^ (n - i) ≤ (η + 2) ^ n * u ^ n :=
                hz_pow_le (n - i) (Nat.sub_le _ _)
              have hExpDeriv :
                  ‖iteratedDeriv (n - i) e ξ‖ ≤ ‖I * z‖ ^ (n - i) * Real.exp η := by
                rw [show e = (fun t : ℝ => Complex.exp (I * z * t)) by rfl,
                  iteratedDeriv_cexp_const_mul_real (n - i) (I * z)]
                calc
                  ‖(I * z) ^ (n - i) * Complex.exp (I * z * ξ)‖
                      = ‖I * z‖ ^ (n - i) * ‖Complex.exp (I * z * ξ)‖ := by
                          rw [norm_mul, norm_pow]
                  _ ≤ ‖I * z‖ ^ (n - i) * Real.exp η := by
                        gcongr
              calc
                ‖n.choose i * iteratedDeriv i χ ξ * iteratedDeriv (n - i) e ξ‖
                    = (n.choose i : ℝ) * ‖iteratedDeriv i χ ξ‖ * ‖iteratedDeriv (n - i) e ξ‖ := by
                        simp [mul_assoc]
                _ ≤ (n.choose i : ℝ) * B i * (‖I * z‖ ^ (n - i) * Real.exp η) := by
                      have hchoose_nonneg : 0 ≤ (n.choose i : ℝ) := by
                        exact_mod_cast Nat.zero_le (n.choose i)
                      calc
                        (n.choose i : ℝ) * ‖iteratedDeriv i χ ξ‖ * ‖iteratedDeriv (n - i) e ξ‖
                            = (n.choose i : ℝ) * (‖iteratedDeriv i χ ξ‖ * ‖iteratedDeriv (n - i) e ξ‖) := by
                                ring
                        _ ≤ (n.choose i : ℝ) * (B i * (‖I * z‖ ^ (n - i) * Real.exp η)) := by
                              refine mul_le_mul_of_nonneg_left ?_ hchoose_nonneg
                              refine mul_le_mul hBi hExpDeriv (norm_nonneg _) ?_
                              exact hB_nonneg i
                        _ = (n.choose i : ℝ) * B i * (‖I * z‖ ^ (n - i) * Real.exp η) := by
                              ring
                _ ≤ (n.choose i : ℝ) * B i * ((η + 2) ^ n * u ^ n * Real.exp η) := by
                      have hchoose_nonneg : 0 ≤ (n.choose i : ℝ) := by
                        exact_mod_cast Nat.zero_le (n.choose i)
                      calc
                        (n.choose i : ℝ) * B i * (‖I * z‖ ^ (n - i) * Real.exp η)
                            = (n.choose i : ℝ) * (B i * (‖I * z‖ ^ (n - i) * Real.exp η)) := by
                                ring
                        _ ≤ (n.choose i : ℝ) * (B i * ((η + 2) ^ n * u ^ n * Real.exp η)) := by
                              refine mul_le_mul_of_nonneg_left ?_ hchoose_nonneg
                              refine mul_le_mul_of_nonneg_left ?_ (hB_nonneg i)
                              exact mul_le_mul_of_nonneg_right hpow_i (Real.exp_pos η).le
                        _ = (n.choose i : ℝ) * B i * ((η + 2) ^ n * u ^ n * Real.exp η) := by
                              ring
                _ = ((n.choose i : ℝ) * B i * (η + 2) ^ n * Real.exp η) * u ^ n := by
                      ring
        _ = Cmid * u ^ n := by
              dsimp [Cmid]
              rw [Finset.sum_mul]
        _ ≤ C * u ^ n := by
              gcongr
              exact le_max_left _ _

/-- A continuous linear endomorphism of Schwartz space preserves polynomial
    horizontal-line seminorm bounds on the family `ψ_{x+iη}`.

    This packages the generic Schwartz-topology estimate needed later for the
    Fourier transform and for multiplication by the linear symbol `ξ ↦ I ξ`
    when constructing the candidate complex derivative of the Fourier-Laplace
    extension. -/
theorem schwartzCLM_seminorm_horizontal_growth
    (L : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ)
    (η : ℝ) (hη : 0 < η) (k n : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ x : ℝ,
      SchwartzMap.seminorm ℝ k n
        (L (schwartzPsiZ ((x : ℂ) + η * I) (by simpa using hη))) ≤
          C * (1 + |x|) ^ N := by
  classical
  let q : Seminorm ℂ (SchwartzMap ℝ ℂ) :=
    (schwartzSeminormFamily ℂ ℝ ℂ (k, n)).comp L.toLinearMap
  have hq_cont : Continuous q := by
    change Continuous (fun φ : SchwartzMap ℝ ℂ =>
      schwartzSeminormFamily ℂ ℝ ℂ (k, n) (L φ))
    exact ((schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm (k, n)).comp L.continuous
  obtain ⟨s, D, hD_ne, hq_bound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ ℝ ℂ) q hq_cont
  have hD_pos : 0 < (D : ℝ) := by
    exact lt_of_le_of_ne D.2 (by exact_mod_cast hD_ne.symm)
  have hB :
      ∀ p : ℕ × ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ,
        schwartzSeminormFamily ℂ ℝ ℂ p
          (schwartzPsiZ ((x : ℂ) + η * I) (by simpa using hη)) ≤
            B * (1 + |x|) ^ p.2 := by
    intro p
    obtain ⟨B, hB_nonneg, hB_bound⟩ := schwartzPsiZ_seminorm_horizontal_bound η hη p.1 p.2
    exact ⟨B, hB_nonneg, hB_bound⟩
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
  intro x
  let ψx : SchwartzMap ℝ ℂ := schwartzPsiZ ((x : ℂ) + η * I) (by simpa using hη)
  let u : ℝ := 1 + |x|
  have hu_nonneg : 0 ≤ u := by
    have hx : 0 ≤ |x| := abs_nonneg x
    linarith
  have hu_ge_one : 1 ≤ u := by
    have hx : 0 ≤ |x| := abs_nonneg x
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
                  ≤ B p * u ^ p.2 := hB_bound p x
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
    SchwartzMap.seminorm ℝ k n (L ψx) ≤ (D : ℝ) * (Bsum * u ^ N) := hL_bound
    _ ≤ C * u ^ N := by
          have hCu : (D : ℝ) * (Bsum * u ^ N) ≤ ((D : ℝ) * Bsum + 1) * u ^ N := by
            have hu_pow_ge_one : 1 ≤ u ^ N := by
              exact pow_le_pow_right₀ hu_ge_one (Nat.zero_le _)
            nlinarith [hBsum_nonneg, show 0 < (D : ℝ) from hD_pos]
          simpa [C, u, mul_assoc, mul_left_comm, mul_comm] using hCu

/-- The derivative symbol `ξ ↦ I ξ` preserves polynomial horizontal-line
    seminorm growth of the family `ψ_{x+iη}` after multiplication on the
    Schwartz side. -/
theorem schwartzPsiZ_derivSymbol_seminorm_horizontal_growth
    (η : ℝ) (hη : 0 < η) (k n : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ x : ℝ,
      SchwartzMap.seminorm ℝ k n
        ((smulLeftCLM ℂ (fun ξ : ℝ => I * (ξ : ℂ)))
          (schwartzPsiZ ((x : ℂ) + η * I) (by simpa using hη))) ≤
            C * (1 + |x|) ^ N := by
  simpa using
    schwartzCLM_seminorm_horizontal_growth
      (L := smulLeftCLM ℂ (fun ξ : ℝ => I * (ξ : ℂ))) η hη k n

/-! ### The Fourier-Laplace extension F(z) = T(FT[ψ_z]) -/

/-- The candidate Fourier-Laplace extension: for a tempered distribution `T`
    given as a continuous complex-linear functional on Schwartz space and with
    one-sided Fourier support, define `F(z) = T(FT[ψ_z])` for `Im(z) > 0`.

    This is well-defined since ψ_z ∈ S(ℝ,ℂ) for Im(z) > 0. -/
noncomputable def fourierLaplaceExt
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ) (z : ℂ) (hz : 0 < z.im) : ℂ :=
  T (SchwartzMap.fourierTransformCLM ℂ (schwartzPsiZ z hz))

/-- F(z) depends only on the value of T and z (not on the proof hz). -/
theorem fourierLaplaceExt_eq (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ) (z : ℂ) (hz : 0 < z.im) :
    fourierLaplaceExt T z hz =
      T (SchwartzMap.fourierTransformCLM ℂ (schwartzPsiZ z hz)) := rfl

end SCV

end
