import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.PermutationFlowBlockers.Core

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter

namespace BHW

variable {d : ℕ}

/-- Deferred invariant-only core (`d=1,n=2`):
for a function of Lorentz invariants, prove swap symmetry on the doubly
witnessed quadric locus from intrinsic analyticity/connectedness plus a real
spacelike correction condition, all in `(q0,q1,p,s)` variables.

Numerical status (heuristic, 2026-03-04): no finite-ansatz falsifier found in
`ProofHarness/d1n2_tail_four_critical_lemma_checks.py` for this core implication
under sampled correction anchors and sampled complex witnessed-domain points.
Latest stress run summary:
- correction anchors: `9000` samples
  (`3000` real-FT z + `3000` phase-locked z + `3000` intrinsic),
- complex witnessed domain: `4000` samples,
- correction-constrained nullspace dimension: `0`,
- worst sampled `|g|` on witnessed domain: `0.0` (threshold `1e-6`). -/
theorem blocker_d1N2InvariantKernelSwapEq_onSectionWitnessPair_invariantFunction_core_deferred
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hAnalytic :
      DifferentiableOn ℂ
        (fun t : ℂ × ℂ × ℂ × ℂ =>
          f t.1 t.2.1 t.2.2.1 t.2.2.2 - f t.2.1 t.1 t.2.2.1 (-t.2.2.2))
        {t : ℂ × ℂ × ℂ × ℂ |
          t.2.2.2 ^ 2 = 4 * (t.2.2.1 ^ 2 - t.1 * t.2.1) ∧
          (∃ v0 : ℂ,
            0 < v0.im ∧
            0 < ((-t.1) / v0).im ∧
            0 < ((t.1 - t.2.2.1 - t.2.2.2 / 2) / v0).im ∧
            0 < (((t.2.2.1 - t.2.2.2 / 2 - t.1) * v0 / t.1).im)) ∧
          (∃ w0 : ℂ,
            0 < w0.im ∧
            0 < ((-t.2.1) / w0).im ∧
            0 < ((t.2.1 - t.2.2.1 + t.2.2.2 / 2) / w0).im ∧
            0 < (((t.2.2.1 + t.2.2.2 / 2 - t.2.1) * w0 / t.2.1).im))})
    (hConnected :
      IsPreconnected
        {t : ℂ × ℂ × ℂ × ℂ |
          t.2.2.2 ^ 2 = 4 * (t.2.2.1 ^ 2 - t.1 * t.2.1) ∧
          (∃ v0 : ℂ,
            0 < v0.im ∧
            0 < ((-t.1) / v0).im ∧
            0 < ((t.1 - t.2.2.1 - t.2.2.2 / 2) / v0).im ∧
            0 < (((t.2.2.1 - t.2.2.2 / 2 - t.1) * v0 / t.1).im)) ∧
          (∃ w0 : ℂ,
            0 < w0.im ∧
            0 < ((-t.2.1) / w0).im ∧
            0 < ((t.2.1 - t.2.2.1 + t.2.2.2 / 2) / w0).im ∧
            0 < (((t.2.2.1 + t.2.2.2 / 2 - t.2.1) * w0 / t.2.1).im))})
    (hCorrection :
      ∀ q0 q1 p s : ℂ,
        s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
        q0.im = 0 →
        q1.im = 0 →
        p.im = 0 →
        s.im = 0 →
        q0.re + q1.re - 2 * p.re > 0 →
        f q0 q1 p s = f q1 q0 p (-s)) :
    ∀ q0 q1 p s : ℂ, s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      (∃ v0 : ℂ,
        0 < v0.im ∧
        0 < ((-q0) / v0).im ∧
        0 < ((q0 - p - s / 2) / v0).im ∧
        0 < (((p - s / 2 - q0) * v0 / q0).im)) →
      (∃ w0 : ℂ,
        0 < w0.im ∧
        0 < ((-q1) / w0).im ∧
        0 < ((q1 - p + s / 2) / w0).im ∧
        0 < (((p + s / 2 - q1) * w0 / q1).im)) →
      f q0 q1 p s = f q1 q0 p (-s) := by
  intro q0 q1 p s hquad hOrigFT hSwapFT
  let _ := hAnalytic
  let _ := hConnected
  let _ := hCorrection
  let _ := hquad
  let _ := hOrigFT
  let _ := hSwapFT
  -- Remaining invariant-route analytic input.
  sorry

/-- Forward-to-invariant witness extraction (`d=1,n=2`):
from a concrete forward-tube configuration `z` with invariant tuple
`(q0,q1,p,s)`, produce an intrinsic original-chart witness `v0` satisfying the
inequalities in invariant variables.

Mathematically, this maps a point of `FT_{1,2}` to the original-side invariant
witness locus used in the invariant-only core theorem. -/
lemma d1N2InvariantOrigWitnessIneq_of_forwardInvariants
    {q0 q1 p s : ℂ} {z : Fin 2 → Fin (1 + 1) → ℂ}
    (hz : z ∈ ForwardTube 1 2)
    (hquadZ : d1InvariantQuad z = (q0, q1, p, s)) :
    ∃ v0 : ℂ,
      0 < v0.im ∧
      0 < ((-q0) / v0).im ∧
      0 < ((q0 - p - s / 2) / v0).im ∧
      0 < (((p - s / 2 - q0) * v0 / q0).im) := by
  have hq0 : d1Q0 z = q0 := by
    simpa [d1InvariantQuad] using congrArg Prod.fst hquadZ
  have hp : d1P01 z = p := by
    simpa [d1InvariantQuad] using congrArg (fun t => t.2.2.1) hquadZ
  have hs : d1S01 z = s := by
    simpa [d1InvariantQuad] using congrArg (fun t => t.2.2.2) hquadZ
  have hV0_ne : d1V0 z ≠ 0 := d1V0_ne_zero_of_forward z hz
  have hU0_ne : d1U0 z ≠ 0 := d1U0_ne_zero_of_forward z hz
  have hq0_ne : q0 ≠ 0 := by
    have hQ0ne : d1Q0 z ≠ 0 := d1Q0_ne_zero_of_mem_forwardTube_d1_n2 z hz
    simpa [hq0] using hQ0ne
  have hUdiff_im_pos : 0 < (d1U1 z - d1U0 z).im := by
    rcases (forwardTube_d1_n2_iff z).1 hz with ⟨_hz0cone, hzdiffcone⟩
    have hpmd := (inOpenForwardCone_d1_iff_pm (fun μ => (z 1 μ - z 0 μ).im)).1 hzdiffcone
    have hsum :
        (fun μ => (z 1 μ - z 0 μ).im) 0 + (fun μ => (z 1 μ - z 0 μ).im) 1 =
          (d1U1 z - d1U0 z).im := by
      simp [d1U0, d1U1, Complex.add_im, Complex.sub_im]
      ring
    exact hsum ▸ hpmd.1
  have hVdiff_im_pos : 0 < (d1V1 z - d1V0 z).im := by
    rcases (forwardTube_d1_n2_iff z).1 hz with ⟨_hz0cone, hzdiffcone⟩
    have hpmd := (inOpenForwardCone_d1_iff_pm (fun μ => (z 1 μ - z 0 μ).im)).1 hzdiffcone
    have hdiff :
        (fun μ => (z 1 μ - z 0 μ).im) 0 - (fun μ => (z 1 μ - z 0 μ).im) 1 =
          (d1V1 z - d1V0 z).im := by
      simp [d1V0, d1V1, Complex.sub_im]
      ring
    exact hdiff ▸ hpmd.2
  refine ⟨d1V0 z, d1V0_im_pos_of_forward z hz, ?_, ?_, ?_⟩
  ·
    have hEq :
        ((-q0) / d1V0 z).im = (d1U0 z).im := by
      calc
        ((-q0) / d1V0 z).im = ((-d1Q0 z) / d1V0 z).im := by simp [hq0]
        _ = ((d1U0 z * d1V0 z) / d1V0 z).im := by
              simp [d1Q0_eq_neg_U0_mul_V0]
        _ = (d1U0 z).im := by
              field_simp [hV0_ne]
    have hpos : 0 < (d1U0 z).im := d1U0_im_pos_of_forward z hz
    exact hEq.symm ▸ hpos
  ·
    have hEq :
        ((q0 - p - s / 2) / d1V0 z).im = (d1U1 z - d1U0 z).im := by
      calc
        ((q0 - p - s / 2) / d1V0 z).im
            = ((d1Q0 z - d1P01 z - d1S01 z / 2) / d1V0 z).im := by
                simp [hq0, hp, hs]
        _ = ((d1Q0 z + (-(d1P01 z) - d1S01 z / 2)) / d1V0 z).im := by ring_nf
        _ = ((d1Q0 z + d1T01 z) / d1V0 z).im := by
              simp [d1_neg_P01_sub_half_S01_eq_T01 z]
        _ = ((-(d1U0 z * d1V0 z) + d1U1 z * d1V0 z) / d1V0 z).im := by
              simp [d1Q0_eq_neg_U0_mul_V0, d1T01]
        _ = (((d1U1 z - d1U0 z) * d1V0 z) / d1V0 z).im := by ring_nf
        _ = (d1U1 z - d1U0 z).im := by
              field_simp [hV0_ne]
    exact hEq.symm ▸ hUdiff_im_pos
  ·
    have hEq :
        (((p - s / 2 - q0) * d1V0 z / q0).im) = (d1V1 z - d1V0 z).im := by
      calc
        (((p - s / 2 - q0) * d1V0 z / q0).im)
            = (((d1P01 z - d1S01 z / 2 - d1Q0 z) * d1V0 z / d1Q0 z).im) := by
                simp [hq0, hp, hs]
        _ = (((-d1R01 z - d1Q0 z) * d1V0 z / d1Q0 z).im) := by
              have hR : d1P01 z - d1S01 z / 2 = -d1R01 z := by
                calc
                  d1P01 z - d1S01 z / 2 = -(-(d1P01 z) + d1S01 z / 2) := by ring
                  _ = -d1R01 z := by rw [d1_neg_P01_add_half_S01_eq_R01 z]
              rw [hR]
        _ = ((((d1U0 z * (d1V0 z - d1V1 z)) * d1V0 z) /
                (-(d1U0 z * d1V0 z))).im) := by
              simp [d1R01, d1Q0_eq_neg_U0_mul_V0]
              ring_nf
        _ = (d1V1 z - d1V0 z).im := by
              have hfrac :
                  ((d1U0 z * (d1V0 z - d1V1 z)) * d1V0 z) /
                    (-(d1U0 z * d1V0 z)) = -(d1V0 z - d1V1 z) := by
                field_simp [hU0_ne, hV0_ne]
              rw [hfrac]
              ring_nf
    exact hEq.symm ▸ hVdiff_im_pos

/-- Invariant-to-forward reconstruction for the original chart (`d=1,n=2`):
if `v0` satisfies the intrinsic original-side witness inequalities for
`(q0,p,s)`, then the explicit section representative
`d1N2SectionOrig q0 q1 p s v0` belongs to `FT_{1,2}`.

This is the converse direction to forward-to-invariant witness extraction on
the original chart. -/
lemma d1N2SectionOrig_mem_forwardTube_of_witnessIneq
    {q0 q1 p s v0 : ℂ}
    (hv0im : 0 < v0.im)
    (hU0im : 0 < ((-q0) / v0).im)
    (hUdiffim : 0 < ((q0 - p - s / 2) / v0).im)
    (hVdiffim : 0 < (((p - s / 2 - q0) * v0 / q0).im)) :
    d1N2SectionOrig q0 q1 p s v0 ∈ ForwardTube 1 2 := by
  let z : Fin 2 → Fin (1 + 1) → ℂ := d1N2SectionOrig q0 q1 p s v0
  have hq0_ne : q0 ≠ 0 := by
    intro hq0
    have hzero : (((p - s / 2 - q0) * v0 / q0).im) = 0 := by
      simp [hq0]
    linarith
  have hz0cone : InOpenForwardCone 1 (fun μ => (z 0 μ).im) := by
    have hz0pm :
        (fun μ => (z 0 μ).im) 0 + (fun μ => (z 0 μ).im) 1 > 0 ∧
          (fun μ => (z 0 μ).im) 0 - (fun μ => (z 0 μ).im) 1 > 0 := by
      refine ⟨?_, ?_⟩
      · have hsum :
          (fun μ => (z 0 μ).im) 0 + (fun μ => (z 0 μ).im) 1 = (d1U0 z).im := by
            simp [d1U0, Complex.add_im]
        have hU0 :
            d1U0 z = (-q0) / v0 := by
          simp [z, d1N2SectionOrig]
        rw [hsum, hU0]
        exact hU0im
      · have hdiff :
          (fun μ => (z 0 μ).im) 0 - (fun μ => (z 0 μ).im) 1 = (d1V0 z).im := by
            simp [d1V0, Complex.sub_im]
        have hV0 : d1V0 z = v0 := by
          simp [z, d1N2SectionOrig]
        rw [hdiff, hV0]
        exact hv0im
    exact (inOpenForwardCone_d1_iff_pm (fun μ => (z 0 μ).im)).2 hz0pm
  have hzdiffcone : InOpenForwardCone 1 (fun μ => (z 1 μ - z 0 μ).im) := by
    have hpm :
        (fun μ => (z 1 μ - z 0 μ).im) 0 + (fun μ => (z 1 μ - z 0 μ).im) 1 > 0 ∧
          (fun μ => (z 1 μ - z 0 μ).im) 0 - (fun μ => (z 1 μ - z 0 μ).im) 1 > 0 := by
      refine ⟨?_, ?_⟩
      · have hsum :
          (fun μ => (z 1 μ - z 0 μ).im) 0 + (fun μ => (z 1 μ - z 0 μ).im) 1 =
            (d1U1 z - d1U0 z).im := by
          simp [d1U0, d1U1, Complex.add_im, Complex.sub_im]
          ring
        have hU :
            d1U1 z - d1U0 z = (q0 - p - s / 2) / v0 := by
          simp [z, d1N2SectionOrig]
          ring
        rw [hsum, hU]
        exact hUdiffim
      · have hdiff :
          (fun μ => (z 1 μ - z 0 μ).im) 0 - (fun μ => (z 1 μ - z 0 μ).im) 1 =
            (d1V1 z - d1V0 z).im := by
          simp [d1V0, d1V1, Complex.sub_im]
          ring
        have hV :
            d1V1 z - d1V0 z = (p - s / 2 - q0) * v0 / q0 := by
          calc
            d1V1 z - d1V0 z = (p - s / 2) * v0 / q0 - v0 := by
              simp [z, d1N2SectionOrig]
              ring
            _ = (p - s / 2 - q0) * v0 / q0 := by
              field_simp [hq0_ne]
        rw [hdiff, hV]
        exact hVdiffim
    exact (inOpenForwardCone_d1_iff_pm (fun μ => (z 1 μ - z 0 μ).im)).2 hpm
  exact (forwardTube_d1_n2_iff z).2 ⟨hz0cone, hzdiffcone⟩

/-- Invariant-to-forward reconstruction for the swapped chart (`d=1,n=2`):
if `w0` satisfies the intrinsic swapped-side witness inequalities for
`(q1,p,s)`, then the explicit swapped section representative
`d1N2SectionSwap q0 q1 p s w0` belongs to `FT_{1,2}`.

Together with the original-chart reconstruction lemma, this identifies the
intrinsic witness inequalities with forward realizability of section charts. -/
lemma d1N2SectionSwap_mem_forwardTube_of_witnessIneq
    {q0 q1 p s w0 : ℂ}
    (hw0im : 0 < w0.im)
    (hU0im : 0 < ((-q1) / w0).im)
    (hUdiffim : 0 < ((q1 - p + s / 2) / w0).im)
    (hVdiffim : 0 < (((p + s / 2 - q1) * w0 / q1).im)) :
    d1N2SectionSwap q0 q1 p s w0 ∈ ForwardTube 1 2 := by
  let z : Fin 2 → Fin (1 + 1) → ℂ := d1N2SectionSwap q0 q1 p s w0
  have hq1_ne : q1 ≠ 0 := by
    intro hq1
    have hzero : (((p + s / 2 - q1) * w0 / q1).im) = 0 := by
      simp [hq1]
    linarith
  have hz0cone : InOpenForwardCone 1 (fun μ => (z 0 μ).im) := by
    have hz0pm :
        (fun μ => (z 0 μ).im) 0 + (fun μ => (z 0 μ).im) 1 > 0 ∧
          (fun μ => (z 0 μ).im) 0 - (fun μ => (z 0 μ).im) 1 > 0 := by
      refine ⟨?_, ?_⟩
      · have hsum :
          (fun μ => (z 0 μ).im) 0 + (fun μ => (z 0 μ).im) 1 = (d1U0 z).im := by
            simp [d1U0, Complex.add_im]
        have hU0 :
            d1U0 z = (-q1) / w0 := by
          simp [z, d1N2SectionSwap]
        rw [hsum, hU0]
        exact hU0im
      · have hdiff :
          (fun μ => (z 0 μ).im) 0 - (fun μ => (z 0 μ).im) 1 = (d1V0 z).im := by
            simp [d1V0, Complex.sub_im]
        have hV0 : d1V0 z = w0 := by
          simp [z, d1N2SectionSwap]
        rw [hdiff, hV0]
        exact hw0im
    exact (inOpenForwardCone_d1_iff_pm (fun μ => (z 0 μ).im)).2 hz0pm
  have hzdiffcone : InOpenForwardCone 1 (fun μ => (z 1 μ - z 0 μ).im) := by
    have hpm :
        (fun μ => (z 1 μ - z 0 μ).im) 0 + (fun μ => (z 1 μ - z 0 μ).im) 1 > 0 ∧
          (fun μ => (z 1 μ - z 0 μ).im) 0 - (fun μ => (z 1 μ - z 0 μ).im) 1 > 0 := by
      refine ⟨?_, ?_⟩
      · have hsum :
          (fun μ => (z 1 μ - z 0 μ).im) 0 + (fun μ => (z 1 μ - z 0 μ).im) 1 =
            (d1U1 z - d1U0 z).im := by
          simp [d1U0, d1U1, Complex.add_im, Complex.sub_im]
          ring
        have hU :
            d1U1 z - d1U0 z = (q1 - p + s / 2) / w0 := by
          simp [z, d1N2SectionSwap]
          ring
        rw [hsum, hU]
        exact hUdiffim
      · have hdiff :
          (fun μ => (z 1 μ - z 0 μ).im) 0 - (fun μ => (z 1 μ - z 0 μ).im) 1 =
            (d1V1 z - d1V0 z).im := by
          simp [d1V0, d1V1, Complex.sub_im]
          ring
        have hV :
            d1V1 z - d1V0 z = (p + s / 2 - q1) * w0 / q1 := by
          calc
            d1V1 z - d1V0 z = (p + s / 2) * w0 / q1 - w0 := by
              simp [z, d1N2SectionSwap]
              ring
            _ = (p + s / 2 - q1) * w0 / q1 := by
              field_simp [hq1_ne]
        rw [hdiff, hV]
        exact hVdiffim
    exact (inOpenForwardCone_d1_iff_pm (fun μ => (z 1 μ - z 0 μ).im)).2 hpm
  exact (forwardTube_d1_n2_iff z).2 ⟨hz0cone, hzdiffcone⟩

/-- Invariant-function wrapper around the intrinsic `d=1,n=2` core theorem:
if the analytic, preconnectedness, and real-spacelike correction inputs hold on
the
invariant witnessed quadric locus, then the forwardizable-kernel difference
vanishes. -/
theorem blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_invariantFunction_core_deferred
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hAnalytic :
      DifferentiableOn ℂ
        (fun t : ℂ × ℂ × ℂ × ℂ =>
          f t.1 t.2.1 t.2.2.1 t.2.2.2 - f t.2.1 t.1 t.2.2.1 (-t.2.2.2))
        {t : ℂ × ℂ × ℂ × ℂ |
          t.2.2.2 ^ 2 = 4 * (t.2.2.1 ^ 2 - t.1 * t.2.1) ∧
          (∃ v0 : ℂ,
            0 < v0.im ∧
            0 < ((-t.1) / v0).im ∧
            0 < ((t.1 - t.2.2.1 - t.2.2.2 / 2) / v0).im ∧
            0 < (((t.2.2.1 - t.2.2.2 / 2 - t.1) * v0 / t.1).im)) ∧
          (∃ w0 : ℂ,
            0 < w0.im ∧
            0 < ((-t.2.1) / w0).im ∧
            0 < ((t.2.1 - t.2.2.1 + t.2.2.2 / 2) / w0).im ∧
            0 < (((t.2.2.1 + t.2.2.2 / 2 - t.2.1) * w0 / t.2.1).im))})
    (hConnected :
      IsPreconnected
        {t : ℂ × ℂ × ℂ × ℂ |
          t.2.2.2 ^ 2 = 4 * (t.2.2.1 ^ 2 - t.1 * t.2.1) ∧
          (∃ v0 : ℂ,
            0 < v0.im ∧
            0 < ((-t.1) / v0).im ∧
            0 < ((t.1 - t.2.2.1 - t.2.2.2 / 2) / v0).im ∧
            0 < (((t.2.2.1 - t.2.2.2 / 2 - t.1) * v0 / t.1).im)) ∧
          (∃ w0 : ℂ,
            0 < w0.im ∧
            0 < ((-t.2.1) / w0).im ∧
            0 < ((t.2.1 - t.2.2.1 + t.2.2.2 / 2) / w0).im ∧
            0 < (((t.2.2.1 + t.2.2.2 / 2 - t.2.1) * w0 / t.2.1).im))})
    (hCorrection :
      ∀ q0 q1 p s : ℂ,
        s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
        q0.im = 0 →
        q1.im = 0 →
        p.im = 0 →
        s.im = 0 →
        q0.re + q1.re - 2 * p.re > 0 →
        f q0 q1 p s = f q1 q0 p (-s)) :
    d1N2InvariantKernelDiffZeroOnForwardizableQuadric f := by
  intro q0 q1 p s hquad hfw
  have hpairReal :
      d1N2InvariantRealizable q0 q1 p s ∧
        d1N2InvariantRealizable q1 q0 p (-s) :=
    d1N2InvariantRealizable_pair_of_forwardizable hfw
  rcases hpairReal.1 with ⟨z, hz, hquadZ⟩
  rcases hpairReal.2 with ⟨y, hy, hquadY⟩
  have hOrigFT :
      ∃ v0 : ℂ,
        0 < v0.im ∧
        0 < ((-q0) / v0).im ∧
        0 < ((q0 - p - s / 2) / v0).im ∧
        0 < (((p - s / 2 - q0) * v0 / q0).im) :=
    d1N2InvariantOrigWitnessIneq_of_forwardInvariants hz hquadZ
  have hSwapFT :
      ∃ w0 : ℂ,
        0 < w0.im ∧
        0 < ((-q1) / w0).im ∧
        0 < ((q1 - p + s / 2) / w0).im ∧
        0 < (((p + s / 2 - q1) * w0 / q1).im) := by
    rcases d1N2InvariantOrigWitnessIneq_of_forwardInvariants
        (q0 := q1) (q1 := q0) (p := p) (s := -s) hy hquadY with
      ⟨w0, hw0im, hw0a, hw0b, hw0c⟩
    refine ⟨w0, hw0im, hw0a, ?_, ?_⟩
    · have hB : q1 - p - (-s) / 2 = q1 - p + s / 2 := by ring
      simpa [hB] using hw0b
    · have hC : p - (-s) / 2 - q1 = p + s / 2 - q1 := by ring
      simpa [hC] using hw0c
  have hEq :
      f q0 q1 p s = f q1 q0 p (-s) :=
    blocker_d1N2InvariantKernelSwapEq_onSectionWitnessPair_invariantFunction_core_deferred
      f
      hAnalytic
      hConnected
      hCorrection
      q0 q1 p s hquad hOrigFT hSwapFT
  exact sub_eq_zero.mpr hEq

/-- Deferred source-to-invariant bridge (analyticity input).

Define the invariant antisymmetric difference
`g(q0,q1,p,s) := f q0 q1 p s - f q1 q0 p (-s)`, and let `D` be the intrinsic
domain cut out by:
1. `s^2 = 4 * (p^2 - q0*q1)`,
2. the original witness inequalities,
3. the swapped witness inequalities.

This theorem asks to derive `DifferentiableOn ℂ g D` from the source package
`d1N2InvariantKernelSource f` (i.e. from a holomorphic source field on
`FT_{1,2}` plus invariant factorization).

Numerical status (heuristic, 2026-03-04): in the finite ansatz harness
`ProofHarness/d1n2_tail_four_critical_lemma_checks.py`, sampled source
constraints leave no nonzero antisymmetric mode, and finite-difference
Wirtinger residual checks report no violation.
Latest stress run summary:
- source constraint samples: `9000`
  (`6000` intrinsic real-spacelike + `3000` z-constructed),
- source-constrained nullspace dimension: `0`,
- finite-difference points checked: `300`,
- max sampled `|∂̄g|`: `0.0` (step `1e-6`). -/
theorem blocker_d1N2InvariantBridgeAnalyticity_fromSource_deferred
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f) :
    DifferentiableOn ℂ
      (fun t : ℂ × ℂ × ℂ × ℂ =>
        f t.1 t.2.1 t.2.2.1 t.2.2.2 - f t.2.1 t.1 t.2.2.1 (-t.2.2.2))
      {t : ℂ × ℂ × ℂ × ℂ |
        t.2.2.2 ^ 2 = 4 * (t.2.2.1 ^ 2 - t.1 * t.2.1) ∧
        (∃ v0 : ℂ,
          0 < v0.im ∧
          0 < ((-t.1) / v0).im ∧
          0 < ((t.1 - t.2.2.1 - t.2.2.2 / 2) / v0).im ∧
          0 < (((t.2.2.1 - t.2.2.2 / 2 - t.1) * v0 / t.1).im)) ∧
        (∃ w0 : ℂ,
          0 < w0.im ∧
          0 < ((-t.2.1) / w0).im ∧
          0 < ((t.2.1 - t.2.2.1 + t.2.2.2 / 2) / w0).im ∧
          0 < (((t.2.2.1 + t.2.2.2 / 2 - t.2.1) * w0 / t.2.1).im))} := by
  let _ := hsource
  sorry

/-- Deferred source-to-invariant bridge (connectedness input).

For the same intrinsic invariant domain `D` (quadric relation + original and
swapped witness inequalities), prove `IsPreconnected D`.

Mathematically, this is the topological propagation domain on which a
holomorphic identity for the swap-difference can extend from an anchored subset
to all of `D`.

Numerical status (heuristic support): sampled `z`-constructed witnessed-domain
point clouds tested in
`ProofHarness/d1n2_tail_four_critical_lemma_checks.py` are consistently
KNN-connected (single dominant component; latest run on 2026-03-04:
`4000/4000` points in one component, `1` component total, `k=10`). -/
theorem blocker_d1N2InvariantBridgePreconnected_fromSource_deferred
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f) :
    IsPreconnected
      {t : ℂ × ℂ × ℂ × ℂ |
        t.2.2.2 ^ 2 = 4 * (t.2.2.1 ^ 2 - t.1 * t.2.1) ∧
        (∃ v0 : ℂ,
          0 < v0.im ∧
          0 < ((-t.1) / v0).im ∧
          0 < ((t.1 - t.2.2.1 - t.2.2.2 / 2) / v0).im ∧
          0 < (((t.2.2.1 - t.2.2.2 / 2 - t.1) * v0 / t.1).im)) ∧
        (∃ w0 : ℂ,
          0 < w0.im ∧
          0 < ((-t.2.1) / w0).im ∧
          0 < ((t.2.1 - t.2.2.1 + t.2.2.2 / 2) / w0).im ∧
          0 < (((t.2.2.1 + t.2.2.2 / 2 - t.2.1) * w0 / t.2.1).im))} := by
  let _ := hsource
  sorry

/-- Source-to-invariant bridge reduction (correction input).

This is the anchor identity for the same swap-difference
`g(q0,q1,p,s) := f q0 q1 p s - f q1 q0 p (-s)`:
on points satisfying
1. the quadric relation,
2. real-slice conditions `q0.im = q1.im = p.im = s.im = 0`,
3. real-spacelike inequality `q0.re + q1.re - 2*p.re > 0`,
prove `g(q0,q1,p,s) = 0`, assuming the explicit boundary-identification input
`hBoundaryId`.

This supplies the real-slice correction datum that feeds the invariant-core
theorem.

Numerical status (heuristic, 2026-03-04): no finite-ansatz falsifier found in
`ProofHarness/d1n2_tail_four_critical_lemma_checks.py` on sampled real-slice
spacelike correction tuples (both intrinsic and z-constructed samplers).
Latest stress run summary:
- correction-anchor samples: `9000`
  (`3000` real-FT z + `3000` phase-locked z + `3000` intrinsic),
- direct z-family correction-hit rate: `30000/30000`,
- worst sampled `|g|` on correction anchors: `0.0` (threshold `1e-6`). -/
theorem blocker_d1N2InvariantBridgeCorrection_fromSource_deferred
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f)
    (hBoundaryId :
      ∀ q0 q1 p s : ℂ,
        s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
        q0.im = 0 →
        q1.im = 0 →
        p.im = 0 →
        s.im = 0 →
        q0.re + q1.re - 2 * p.re > 0 →
        ∃ x : Fin 2 → Fin (1 + 1) → ℝ,
          d1InvariantQuad (realEmbed x) = (q0, q1, p, s) ∧
          f q0 q1 p s = (Classical.choose hsource) (realEmbed x) ∧
          f q1 q0 p (-s) =
            (Classical.choose hsource)
              (fun k μ => (x (Equiv.swap (0 : Fin 2) 1 k) μ : ℂ))) :
    ∀ q0 q1 p s : ℂ,
      s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      q0.im = 0 →
      q1.im = 0 →
      p.im = 0 →
      s.im = 0 →
      q0.re + q1.re - 2 * p.re > 0 →
      f q0 q1 p s = f q1 q0 p (-s) := by
  intro q0 q1 p s hquad hq0im hq1im hpim hsim hsp
  have hF_local :
      ∀ (i : Fin 2) (hi : i.val + 1 < 2),
        ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
          ∑ μ, minkowskiSignature 1 μ *
            (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
          (Classical.choose hsource)
            (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
          (Classical.choose hsource) (fun k μ => (x k μ : ℂ)) :=
    (Classical.choose_spec hsource).2.2.2.1
  rcases hBoundaryId q0 q1 p s hquad hq0im hq1im hpim hsim hsp with
    ⟨x, hxquad, hfq, hfswap⟩
  have hq0x : d1Q0 (realEmbed x) = q0 := by
    simpa [d1InvariantQuad] using congrArg Prod.fst hxquad
  have hq1x : d1Q1 (realEmbed x) = q1 := by
    simpa [d1InvariantQuad] using congrArg (fun t => t.2.1) hxquad
  have hpx : d1P01 (realEmbed x) = p := by
    simpa [d1InvariantQuad] using congrArg (fun t => t.2.2.1) hxquad
  have hq0R : (d1Q0R x : ℂ) = q0 := by
    simpa [d1Q0_realEmbed] using hq0x
  have hq1R : (d1Q1R x : ℂ) = q1 := by
    simpa [d1Q1_realEmbed] using hq1x
  have hpR : (d1P01R x : ℂ) = p := by
    simpa [d1P01_realEmbed] using hpx
  have hq0Rre : d1Q0R x = q0.re := by
    exact congrArg Complex.re hq0R
  have hq1Rre : d1Q1R x = q1.re := by
    exact congrArg Complex.re hq1R
  have hpRre : d1P01R x = p.re := by
    exact congrArg Complex.re hpR
  have hspInv : d1Q0R x + d1Q1R x - 2 * d1P01R x > 0 := by
    linarith [hsp, hq0Rre, hq1Rre, hpRre]
  have hswapEq :
      (Classical.choose hsource)
        (fun k μ => (x (Equiv.swap (0 : Fin 2) 1 k) μ : ℂ)) =
      (Classical.choose hsource) (realEmbed x) :=
    d1_n2_local_comm_of_invariant_ineq (Classical.choose hsource) hF_local x hspInv
  calc
    f q0 q1 p s = (Classical.choose hsource) (realEmbed x) := hfq
    _ = (Classical.choose hsource)
          (fun k μ => (x (Equiv.swap (0 : Fin 2) 1 k) μ : ℂ)) := hswapEq.symm
    _ = f q1 q0 p (-s) := hfswap.symm

/-- Pass-through reduction:
if the three invariant bridge inputs are available, source-level forwardizable
kernel diff-zero follows immediately. -/
theorem d1N2InvariantKernelDiffZeroOnForwardizableQuadric_of_source_and_invariantBridgeInputs
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f)
    (hAnalytic :
      DifferentiableOn ℂ
        (fun t : ℂ × ℂ × ℂ × ℂ =>
          f t.1 t.2.1 t.2.2.1 t.2.2.2 - f t.2.1 t.1 t.2.2.1 (-t.2.2.2))
        {t : ℂ × ℂ × ℂ × ℂ |
          t.2.2.2 ^ 2 = 4 * (t.2.2.1 ^ 2 - t.1 * t.2.1) ∧
          (∃ v0 : ℂ,
            0 < v0.im ∧
            0 < ((-t.1) / v0).im ∧
            0 < ((t.1 - t.2.2.1 - t.2.2.2 / 2) / v0).im ∧
            0 < (((t.2.2.1 - t.2.2.2 / 2 - t.1) * v0 / t.1).im)) ∧
          (∃ w0 : ℂ,
            0 < w0.im ∧
            0 < ((-t.2.1) / w0).im ∧
            0 < ((t.2.1 - t.2.2.1 + t.2.2.2 / 2) / w0).im ∧
            0 < (((t.2.2.1 + t.2.2.2 / 2 - t.2.1) * w0 / t.2.1).im))})
    (hConnected :
      IsPreconnected
        {t : ℂ × ℂ × ℂ × ℂ |
          t.2.2.2 ^ 2 = 4 * (t.2.2.1 ^ 2 - t.1 * t.2.1) ∧
          (∃ v0 : ℂ,
            0 < v0.im ∧
            0 < ((-t.1) / v0).im ∧
            0 < ((t.1 - t.2.2.1 - t.2.2.2 / 2) / v0).im ∧
            0 < (((t.2.2.1 - t.2.2.2 / 2 - t.1) * v0 / t.1).im)) ∧
          (∃ w0 : ℂ,
            0 < w0.im ∧
            0 < ((-t.2.1) / w0).im ∧
            0 < ((t.2.1 - t.2.2.1 + t.2.2.2 / 2) / w0).im ∧
            0 < (((t.2.2.1 + t.2.2.2 / 2 - t.2.1) * w0 / t.2.1).im))})
    (hCorrection :
      ∀ q0 q1 p s : ℂ,
        s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
        q0.im = 0 →
        q1.im = 0 →
        p.im = 0 →
        s.im = 0 →
        q0.re + q1.re - 2 * p.re > 0 →
        f q0 q1 p s = f q1 q0 p (-s)) :
    d1N2InvariantKernelDiffZeroOnForwardizableQuadric f := by
  let _ := hsource
  exact blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_invariantFunction_core_deferred
    f hAnalytic hConnected hCorrection

/-- Source wrapper around the invariant-function reduction:
the remaining blocker is to derive the invariant-function bridge hypotheses from
`d1N2InvariantKernelSource f`:
analyticity + witnessed-locus preconnectedness + real-slice witnessed
spacelike correction (via an explicit boundary-identification bridge provided
as an input hypothesis). -/
theorem blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_invariantOnly_core_deferred
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f)
    (hBoundaryId :
      ∀ q0 q1 p s : ℂ,
        s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
        q0.im = 0 →
        q1.im = 0 →
        p.im = 0 →
        s.im = 0 →
        q0.re + q1.re - 2 * p.re > 0 →
        ∃ x : Fin 2 → Fin (1 + 1) → ℝ,
          d1InvariantQuad (realEmbed x) = (q0, q1, p, s) ∧
          f q0 q1 p s = (Classical.choose hsource) (realEmbed x) ∧
          f q1 q0 p (-s) =
            (Classical.choose hsource)
              (fun k μ => (x (Equiv.swap (0 : Fin 2) 1 k) μ : ℂ))) :
    d1N2InvariantKernelDiffZeroOnForwardizableQuadric f := by
  have hAnalytic :
      DifferentiableOn ℂ
        (fun t : ℂ × ℂ × ℂ × ℂ =>
          f t.1 t.2.1 t.2.2.1 t.2.2.2 - f t.2.1 t.1 t.2.2.1 (-t.2.2.2))
        {t : ℂ × ℂ × ℂ × ℂ |
          t.2.2.2 ^ 2 = 4 * (t.2.2.1 ^ 2 - t.1 * t.2.1) ∧
          (∃ v0 : ℂ,
            0 < v0.im ∧
            0 < ((-t.1) / v0).im ∧
            0 < ((t.1 - t.2.2.1 - t.2.2.2 / 2) / v0).im ∧
            0 < (((t.2.2.1 - t.2.2.2 / 2 - t.1) * v0 / t.1).im)) ∧
          (∃ w0 : ℂ,
            0 < w0.im ∧
            0 < ((-t.2.1) / w0).im ∧
            0 < ((t.2.1 - t.2.2.1 + t.2.2.2 / 2) / w0).im ∧
            0 < (((t.2.2.1 + t.2.2.2 / 2 - t.2.1) * w0 / t.2.1).im))} :=
    blocker_d1N2InvariantBridgeAnalyticity_fromSource_deferred f hsource
  have hConnected :
      IsPreconnected
        {t : ℂ × ℂ × ℂ × ℂ |
          t.2.2.2 ^ 2 = 4 * (t.2.2.1 ^ 2 - t.1 * t.2.1) ∧
          (∃ v0 : ℂ,
            0 < v0.im ∧
            0 < ((-t.1) / v0).im ∧
            0 < ((t.1 - t.2.2.1 - t.2.2.2 / 2) / v0).im ∧
            0 < (((t.2.2.1 - t.2.2.2 / 2 - t.1) * v0 / t.1).im)) ∧
          (∃ w0 : ℂ,
            0 < w0.im ∧
            0 < ((-t.2.1) / w0).im ∧
            0 < ((t.2.1 - t.2.2.1 + t.2.2.2 / 2) / w0).im ∧
            0 < (((t.2.2.1 + t.2.2.2 / 2 - t.2.1) * w0 / t.2.1).im))} :=
    blocker_d1N2InvariantBridgePreconnected_fromSource_deferred f hsource
  have hCorrection :
      ∀ q0 q1 p s : ℂ,
        s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
        q0.im = 0 →
        q1.im = 0 →
        p.im = 0 →
        s.im = 0 →
        q0.re + q1.re - 2 * p.re > 0 →
        f q0 q1 p s = f q1 q0 p (-s) := by
    exact blocker_d1N2InvariantBridgeCorrection_fromSource_deferred f hsource hBoundaryId
  exact d1N2InvariantKernelDiffZeroOnForwardizableQuadric_of_source_and_invariantBridgeInputs
    f hsource hAnalytic hConnected hCorrection

/-- Forward witness equality from the source package, reduced to the invariant
forwardizable-kernel theorem plus the explicit source-to-boundary
identification input at `d=1,n=2` (deferred locally in this proof).

Numerical status (heuristic, 2026-03-04): in
`ProofHarness/d1n2_tail_four_critical_lemma_checks.py` test 5, no finite-ansatz
falsifier was found for the source-to-forwardizable implication on sampled
domains (latest run: source constraint samples `4000`, complex forwardizable
samples `1800`, worst sampled `|g| = 0.0`, threshold `1e-6`). -/
theorem blocker_d1N2ForwardWitnessEq_field_deferred
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 2) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin 2) (hi : i.val + 1 < 2),
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ))) :
    ∀ (z : Fin 2 → Fin (1 + 1) → ℂ) (Γ : ComplexLorentzGroup 1),
      z ∈ ForwardTube 1 2 →
      complexLorentzAction Γ
        (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
      F (complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z := by
  rcases blocker_d1N2InvariantFactorization_core_deferred
      F hF_holo hF_lorentz hF_bv hF_local with ⟨f, hf_onFT⟩
  have hsource : d1N2InvariantKernelSource f :=
    ⟨F, hF_holo, hF_lorentz, hF_bv, hF_local, hf_onFT⟩
  have hBoundaryId :
      ∀ q0 q1 p s : ℂ,
        s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
        q0.im = 0 →
        q1.im = 0 →
        p.im = 0 →
        s.im = 0 →
        q0.re + q1.re - 2 * p.re > 0 →
        ∃ x : Fin 2 → Fin (1 + 1) → ℝ,
          d1InvariantQuad (realEmbed x) = (q0, q1, p, s) ∧
          f q0 q1 p s = (Classical.choose hsource) (realEmbed x) ∧
          f q1 q0 p (-s) =
            (Classical.choose hsource)
              (fun k μ => (x (Equiv.swap (0 : Fin 2) 1 k) μ : ℂ)) := by
    -- Remaining source-to-boundary identification input at `d=1,n=2`.
    -- This does not follow from `d1N2InvariantKernelSource` alone
    -- (see `ProofHarness/D1N2SourceCorrectionCounterexample.lean` for the
    -- formal obstruction on off-image values of `f`).
    sorry
  have hquadDiff :
      d1N2InvariantKernelDiffZeroOnForwardizableQuadric f :=
    blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_invariantOnly_core_deferred
      f hsource hBoundaryId
  have hforward :
      ∀ z, z ∈ ForwardTube 1 2 →
        ∀ Γ : ComplexLorentzGroup 1,
          complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
          F (complexLorentzAction Γ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z :=
    (d1N2ForwardSwapEq_iff_invariantKernelDiffZeroOnForwardizableQuadric
      F f hf_onFT).2 hquadDiff
  intro z Γ hz hΓswapFT
  exact hforward z hz Γ hΓswapFT


/-- Pointwise slice-anchor propagation at fixed `w` (`d=1,n=2`):
if one anchor witness already matches `F w`, then every forwardizing witness
gives the same value. -/
theorem d1N2ForwardEq_of_sliceAnchorAtPoint
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (w : Fin 2 → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (hΓswap :
      complexLorentzAction Γ
        (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) ∈ ForwardTube 1 2)
    (hanchorAt :
      ∃ Λ₀ : ComplexLorentzGroup 1,
        complexLorentzAction Λ₀
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) ∈ ForwardTube 1 2 ∧
        F (complexLorentzAction Λ₀
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w)) = F w) :
    F (complexLorentzAction Γ
      (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w)) = F w := by
  rcases hanchorAt with ⟨Λ₀, hΛ₀swap, hΛ₀eq⟩
  let z₀ : Fin 2 → Fin (1 + 1) → ℂ :=
    complexLorentzAction Λ₀
      (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w)
  have htarget :
      complexLorentzAction (Γ * Λ₀⁻¹) z₀ =
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) := by
    dsimp [z₀]
    simp [complexLorentzAction_mul, complexLorentzAction_inv]
  have hcinv :
      F (complexLorentzAction (Γ * Λ₀⁻¹) z₀) = F z₀ :=
    complex_lorentz_invariance 2 F hF_holo hF_lorentz (Γ * Λ₀⁻¹) z₀
      (by simpa [z₀] using hΛ₀swap)
      (by simpa [htarget] using hΓswap)
  calc
    F (complexLorentzAction Γ
      (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w))
        = F (complexLorentzAction (Γ * Λ₀⁻¹) z₀) := by
            simp [htarget]
    _ = F z₀ := hcinv
    _ = F (complexLorentzAction Λ₀
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w)) := by simp [z₀]
    _ = F w := hΛ₀eq

/-- On prepared neighborhoods (`d=1,n=2`), eventual slice-anchor existence and
eventual fixed-witness forward equality are equivalent. -/
theorem d1N2EventuallySliceAnchor_iff_eventuallyForwardEq_fixedWitness
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (w0 : Fin 2 → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin 2 → Fin (1 + 1) → ℂ))
    (hU_good : ∀ w ∈ U,
      w ∈ permForwardOverlapSet (d := 1) 2 (Equiv.swap (0 : Fin 2) 1) ∧
      complexLorentzAction Γ
        (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) ∈ ForwardTube 1 2) :
    (∀ᶠ w in 𝓝 w0, w ∈ U →
      ∃ Λ₀ : ComplexLorentzGroup 1,
        complexLorentzAction Λ₀
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) ∈ ForwardTube 1 2 ∧
        F (complexLorentzAction Λ₀
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w)) = F w) ↔
    (∀ᶠ w in 𝓝 w0, w ∈ U →
      F (complexLorentzAction Γ
        (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w)) = F w) := by
  constructor
  · intro hanchor
    filter_upwards [hanchor] with w hwAnchor hwU
    have hΓswap :
        complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) ∈ ForwardTube 1 2 :=
      (hU_good w hwU).2
    exact d1N2ForwardEq_of_sliceAnchorAtPoint
      F hF_holo hF_lorentz w Γ hΓswap (hwAnchor hwU)
  · intro hforward
    filter_upwards [hforward] with w hwForward hwU
    refine ⟨Γ, (hU_good w hwU).2, hwForward hwU⟩

/-- Deferred local fixed-witness forward equality core (`d=1,n=2`):
on a prepared neighborhood with fixed witness `Γ`, prove eventual
`F(Γ·(swap·w)) = F(w)`. -/
theorem blocker_d1N2LocalForwardEqNhd_core_deferred
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 2) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin 2) (hi : i.val + 1 < 2),
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (w0 : Fin 2 → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin 2 → Fin (1 + 1) → ℂ))
    (hU_open : IsOpen U)
    (hw0U : w0 ∈ U)
    (hU_good : ∀ w ∈ U,
      w ∈ permForwardOverlapSet (d := 1) 2 (Equiv.swap (0 : Fin 2) 1) ∧
      complexLorentzAction Γ
        (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) ∈ ForwardTube 1 2) :
    ∀ᶠ w in 𝓝 w0, w ∈ U →
      F (complexLorentzAction Γ
        (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w)) = F w := by
  let _ := hU_open
  let _ := hw0U
  exact Filter.Eventually.of_forall (fun w hwU => by
    exact blocker_d1N2ForwardWitnessEq_field_deferred
      F hF_holo hF_lorentz hF_bv hF_local
      w Γ (hU_good w hwU).1.1 (hU_good w hwU).2)

/-- Deferred local prepared-neighborhood anchor extraction (`d=1,n=2`):
on a prepared neighborhood with fixed witness `Γ`, produce eventual slice
anchors carrying `F`-equality. -/
theorem blocker_d1N2LocalSliceAnchorNhd_core_deferred
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 2))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin 2 → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 2 →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 2) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin 2) (hi : i.val + 1 < 2),
      ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (w0 : Fin 2 → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin 2 → Fin (1 + 1) → ℂ))
    (hU_open : IsOpen U)
    (hw0U : w0 ∈ U)
    (hU_good : ∀ w ∈ U,
      w ∈ permForwardOverlapSet (d := 1) 2 (Equiv.swap (0 : Fin 2) 1) ∧
      complexLorentzAction Γ
        (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) ∈ ForwardTube 1 2) :
    ∀ᶠ w in 𝓝 w0, w ∈ U →
      ∃ Λ₀ : ComplexLorentzGroup 1,
        complexLorentzAction Λ₀
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w) ∈ ForwardTube 1 2 ∧
        F (complexLorentzAction Λ₀
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w)) = F w := by
  have hforward :
      ∀ᶠ w in 𝓝 w0, w ∈ U →
        F (complexLorentzAction Γ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) w)) = F w :=
    blocker_d1N2LocalForwardEqNhd_core_deferred
      F hF_holo hF_lorentz hF_bv hF_local w0 Γ U hU_open hw0U hU_good
  exact (d1N2EventuallySliceAnchor_iff_eventuallyForwardEq_fixedWitness
    F hF_holo hF_lorentz w0 Γ U hU_good).2 hforward


/-- Deferred `d=1` local slice-anchor input on prepared neighborhoods in the
nontrivial permutation branch (`¬ n ≤ 1`, `τ ≠ 1`).
The `n = 2` case is reduced to the `d1N2` core; the remaining `n = 3` and
`n ≥ 4` branches stay deferred. -/
theorem blocker_eventually_slice_anchor_on_prepared_nhds_d1_nontrivial
    (n : ℕ)
    (F : (Fin n → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin n → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 n) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (τ : Equiv.Perm (Fin n))
    (w0 : Fin n → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin n → Fin (1 + 1) → ℂ))
    (hU_open : IsOpen U)
    (hw0U : w0 ∈ U)
    (hU_good : ∀ w ∈ U,
      w ∈ permForwardOverlapSet (d := 1) n τ ∧
      complexLorentzAction Γ (permAct (d := 1) τ w) ∈ ForwardTube 1 n)
    (hn2 : ¬ n ≤ 1)
    (hτ : τ ≠ 1) :
    ∀ᶠ w in 𝓝 w0, w ∈ U →
      ∃ Λ₀ : ComplexLorentzGroup 1,
        complexLorentzAction Λ₀ (permAct (d := 1) τ w) ∈ ForwardTube 1 n ∧
        F (complexLorentzAction Λ₀ (permAct (d := 1) τ w)) = F w := by
  by_cases h2 : n = 2
  · subst h2
    have hτswap : τ = Equiv.swap (0 : Fin 2) 1 :=
      fin2_perm_ne_one_eq_swap01 τ hτ
    subst hτswap
    exact blocker_d1N2LocalSliceAnchorNhd_core_deferred
      F hF_holo hF_lorentz hF_bv hF_local w0 Γ U hU_open hw0U hU_good
  · -- Remaining nontrivial local branches (`n = 3` and `4 ≤ n`) stay deferred.
    sorry

/-- Deferred `d=1` local slice-anchor input on prepared neighborhoods for an
arbitrary permutation `τ`: the identity and `n ≤ 1` branches are discharged
directly, and the nontrivial branch is reduced to
`blocker_eventually_slice_anchor_on_prepared_nhds_d1_nontrivial`. -/
theorem blocker_eventually_slice_anchor_on_prepared_nhds_d1
    (n : ℕ)
    (F : (Fin n → Fin (1 + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube 1 n))
    (hF_lorentz : ∀ (Λ : RestrictedLorentzGroup 1)
      (z : Fin n → Fin (1 + 1) → ℂ), z ∈ ForwardTube 1 n →
      F (fun k μ => ∑ ν, (Λ.val.val μ ν : ℂ) * z k ν) = F z)
    (hF_bv : ∀ (x : Fin n → Fin (1 + 1) → ℝ),
      ContinuousWithinAt F (ForwardTube 1 n) (fun k μ => (x k μ : ℂ)))
    (hF_local : ∀ (i : Fin n) (hi : i.val + 1 < n),
      ∀ (x : Fin n → Fin (1 + 1) → ℝ),
        ∑ μ, minkowskiSignature 1 μ *
          (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
        F (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
        F (fun k μ => (x k μ : ℂ)))
    (τ : Equiv.Perm (Fin n))
    (w0 : Fin n → Fin (1 + 1) → ℂ)
    (Γ : ComplexLorentzGroup 1)
    (U : Set (Fin n → Fin (1 + 1) → ℂ))
    (hU_open : IsOpen U)
    (hw0U : w0 ∈ U)
    (hU_good : ∀ w ∈ U,
      w ∈ permForwardOverlapSet (d := 1) n τ ∧
      complexLorentzAction Γ (permAct (d := 1) τ w) ∈ ForwardTube 1 n) :
    ∀ᶠ w in 𝓝 w0, w ∈ U →
      ∃ Λ₀ : ComplexLorentzGroup 1,
        complexLorentzAction Λ₀ (permAct (d := 1) τ w) ∈ ForwardTube 1 n ∧
        F (complexLorentzAction Λ₀ (permAct (d := 1) τ w)) = F w := by
  by_cases hτ : τ = 1
  · subst hτ
    exact Filter.Eventually.of_forall (fun w hwU => by
      refine ⟨(1 : ComplexLorentzGroup 1), ?_, ?_⟩
      · have hwFT : w ∈ ForwardTube 1 n := (hU_good w hwU).1.1
        simpa [permAct, complexLorentzAction_one] using hwFT
      · have hperm : permAct (d := 1) (1 : Equiv.Perm (Fin n)) w = w := by
          ext k μ
          simp [permAct]
        simp [complexLorentzAction_one, hperm])
  · by_cases hn : n ≤ 1
    · have hsub : Subsingleton (Fin n) := by
        refine ⟨?_⟩
        intro a b
        apply Fin.ext
        have ha0 : a.val = 0 := by omega
        have hb0 : b.val = 0 := by omega
        omega
      letI : Subsingleton (Fin n) := hsub
      exact (hτ (Subsingleton.elim τ 1)).elim
    · -- Remaining nontrivial branch (`n ≥ 2`, `τ ≠ 1`) is deferred.
      exact blocker_eventually_slice_anchor_on_prepared_nhds_d1_nontrivial
        n F hF_holo hF_lorentz hF_bv hF_local
        τ w0 Γ U hU_open hw0U hU_good hn hτ

/-- Deferred `d=1` geometric input B (`n ≥ 4` branch): forward-triple witness. -/
theorem blocker_d1_forward_triple_nonempty_nge4
    (n : ℕ)
    (σ : Equiv.Perm (Fin n))
    (i : Fin n)
    (hi : i.val + 1 < n)
    (hσ : σ ≠ (1 : Equiv.Perm (Fin n)))
    (hστ : σ ≠ Equiv.swap i ⟨i.val + 1, hi⟩)
    (hn4 : 4 ≤ n) :
    ({w : Fin n → Fin (1 + 1) → ℂ |
        w ∈ ForwardTube 1 n ∧
        permAct (d := 1) (Equiv.swap i ⟨i.val + 1, hi⟩) w ∈ ExtendedTube 1 n ∧
        permAct (d := 1) σ w ∈ ExtendedTube 1 n
    }).Nonempty := by
  sorry

end BHW
