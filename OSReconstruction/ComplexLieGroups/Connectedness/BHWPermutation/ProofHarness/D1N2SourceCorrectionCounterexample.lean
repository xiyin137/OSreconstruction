import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.PermutationFlowBlockers.Core

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter

namespace BHW

private def d1N2RealSpacelikeCorrectionRuleNonzero
    (f : ℂ → ℂ → ℂ → ℂ → ℂ) : Prop :=
  ∀ q0 q1 p s : ℂ,
    s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
    q0 ≠ 0 →
    q1 ≠ 0 →
    q0.im = 0 →
    q1.im = 0 →
    p.im = 0 →
    s.im = 0 →
    q0.re + q1.re - 2 * p.re > 0 →
    f q0 q1 p s = f q1 q0 p (-s)

/-- Positive-spacelike nonrealizable probe (`d=1,n=2`). -/
lemma d1N2InvariantRealizable_posProbe_not :
    ¬ d1N2InvariantRealizable (9 : ℂ) (1 : ℂ) (3 : ℂ) 0 := by
  intro hreal
  rcases hreal with ⟨z, hz, hquad⟩
  have hQ0 : d1Q0 z = (9 : ℂ) := by
    simp [d1InvariantQuad] at hquad
    exact hquad.1
  have hP : d1P01 z = (3 : ℂ) := by
    simpa [d1InvariantQuad] using congrArg (fun t => t.2.2.1) hquad
  have hS : d1S01 z = (0 : ℂ) := by
    simpa [d1InvariantQuad] using congrArg (fun t => t.2.2.2) hquad
  have hU0V0 : d1U0 z * d1V0 z = (-9 : ℂ) := by
    calc
      d1U0 z * d1V0 z = -d1Q0 z := by
        rw [d1Q0_eq_neg_U0_mul_V0]
        ring
      _ = (-9 : ℂ) := by simp [hQ0]
  have hR : d1R01 z = (-3 : ℂ) := by
    calc
      d1R01 z = (d1S01 z - (2 : ℂ) * d1P01 z) / 2 := d1R01_eq_of_P01_S01 z
      _ = ((0 : ℂ) - (2 : ℂ) * (3 : ℂ)) / 2 := by simp [hS, hP]
      _ = (-3 : ℂ) := by norm_num
  have hU0_ne : d1U0 z ≠ 0 := d1U0_ne_zero_of_forward z hz
  have hV1_eq : d1V1 z = ((1 : ℂ) / 3) * d1V0 z := by
    apply (mul_left_cancel₀ hU0_ne)
    calc
      d1U0 z * d1V1 z = d1R01 z := by simp [d1R01]
      _ = (-3 : ℂ) := hR
      _ = ((1 : ℂ) / 3) * (-9 : ℂ) := by norm_num
      _ = ((1 : ℂ) / 3) * (d1U0 z * d1V0 z) := by rw [hU0V0]
      _ = d1U0 z * (((1 : ℂ) / 3) * d1V0 z) := by ring
  have hDiffPos : 0 < (d1V1 z - d1V0 z).im := by
    rcases (forwardTube_d1_n2_iff z).1 hz with ⟨_hz0cone, hzdiffcone⟩
    have hpmd := (inOpenForwardCone_d1_iff_pm (fun μ => (z 1 μ - z 0 μ).im)).1 hzdiffcone
    have hdiff :
        (fun μ => (z 1 μ - z 0 μ).im) 0 -
          (fun μ => (z 1 μ - z 0 μ).im) 1 =
        (d1V1 z - d1V0 z).im := by
      simp [d1V0, d1V1, Complex.sub_im]
      ring
    exact hdiff ▸ hpmd.2
  have hV0ImPos : 0 < (d1V0 z).im := d1V0_im_pos_of_forward z hz
  have hDiffNeg : (d1V1 z - d1V0 z).im < 0 := by
    rw [hV1_eq]
    have hrewrite :
        ((1 : ℂ) / 3) * d1V0 z - d1V0 z =
          (((1 : ℂ) / 3) - 1) * d1V0 z := by ring
    rw [hrewrite]
    have hcoeff :
        ((((1 : ℂ) / 3 - 1) * d1V0 z).im) = ((-(2 : ℝ) / 3) * (d1V0 z).im) := by
      norm_num [Complex.mul_im]
    rw [hcoeff]
    have hcoef_neg : (-(2 : ℝ) / 3) < 0 := by norm_num
    exact mul_neg_of_neg_of_pos hcoef_neg hV0ImPos
  linarith

private def d1N2CounterexampleF : ℂ → ℂ → ℂ → ℂ → ℂ :=
  fun q0 q1 p s =>
    if q0 = 9 ∧ q1 = 1 ∧ p = 3 ∧ s = 0 then (1 : ℂ) else 0

private lemma d1N2CounterexampleF_source :
    d1N2InvariantKernelSource d1N2CounterexampleF := by
  refine ⟨(fun _ => (0 : ℂ)), ?_, ?_, ?_, ?_, ?_⟩
  · exact (differentiableOn_const (c := (0 : ℂ)) :
      DifferentiableOn ℂ (fun _ : Fin 2 → Fin (1 + 1) → ℂ => (0 : ℂ))
        (ForwardTube 1 2))
  · intro Λ z hz
    simp
  · intro x
    simpa using (continuousWithinAt_const :
      ContinuousWithinAt (fun _ : Fin 2 → Fin (1 + 1) → ℂ => (0 : ℂ))
        (ForwardTube 1 2) (fun k μ => (x k μ : ℂ)))
  · intro i hi x hx
    simp
  · intro z hz
    have hcond_false :
        ¬ (d1Q0 z = 9 ∧ d1Q1 z = 1 ∧ d1P01 z = 3 ∧ d1S01 z = 0) := by
      intro hcond
      have hreal : d1N2InvariantRealizable (9 : ℂ) (1 : ℂ) (3 : ℂ) 0 :=
        ⟨z, hz, by simp [d1InvariantQuad, hcond.1, hcond.2.1, hcond.2.2.1, hcond.2.2.2]⟩
      exact d1N2InvariantRealizable_posProbe_not hreal
    simp [d1N2CounterexampleF, hcond_false]

/-- Even with nonzero `q0,q1`, source data alone does not force the real-slice
spacelike correction rule for arbitrary off-image values of `f`. -/
theorem d1N2InvariantKernelSource_not_sufficient_for_realSpacelikeCorrection_nonzero :
    ∃ f : ℂ → ℂ → ℂ → ℂ → ℂ,
      d1N2InvariantKernelSource f ∧
      ¬ d1N2RealSpacelikeCorrectionRuleNonzero f := by
  refine ⟨d1N2CounterexampleF, d1N2CounterexampleF_source, ?_⟩
  intro hcorr
  have hquad : (0 : ℂ) ^ 2 = 4 * ((3 : ℂ) ^ 2 - (9 : ℂ) * (1 : ℂ)) := by
    norm_num
  have hsp : (9 : ℂ).re + (1 : ℂ).re - 2 * (3 : ℂ).re > 0 := by
    norm_num
  have heq :
      d1N2CounterexampleF 9 1 3 0 = d1N2CounterexampleF 1 9 3 (-0) :=
    hcorr 9 1 3 0 hquad (by norm_num) (by norm_num)
      (by simp) (by simp) (by simp) (by simp) hsp
  have hneq :
      d1N2CounterexampleF 9 1 3 0 ≠ d1N2CounterexampleF 1 9 3 (-0) := by
    norm_num [d1N2CounterexampleF]
  exact hneq heq

/-- The current bridge-correction shape (without an explicit source-to-invariant
identification principle) is not derivable from `d1N2InvariantKernelSource`
alone. -/
theorem d1N2_source_not_sufficient_for_bridgeCorrection_shape :
    ¬ (∀ f : ℂ → ℂ → ℂ → ℂ → ℂ,
      d1N2InvariantKernelSource f →
      ∀ q0 q1 p s : ℂ,
        s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
        q0.im = 0 →
        q1.im = 0 →
        p.im = 0 →
        s.im = 0 →
        q0.re + q1.re - 2 * p.re > 0 →
        f q0 q1 p s = f q1 q0 p (-s)) := by
  intro hbridge
  rcases d1N2InvariantKernelSource_not_sufficient_for_realSpacelikeCorrection_nonzero with
    ⟨f, hsource, hnot⟩
  have hnonzeroRule : d1N2RealSpacelikeCorrectionRuleNonzero f := by
    intro q0 q1 p s hquad hq0ne hq1ne hq0im hq1im hpim hsim hsp
    exact hbridge f hsource q0 q1 p s hquad hq0im hq1im hpim hsim hsp
  exact hnot hnonzeroRule

end BHW
