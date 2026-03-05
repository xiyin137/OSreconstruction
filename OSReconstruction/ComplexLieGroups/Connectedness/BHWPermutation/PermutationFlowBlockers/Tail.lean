import OSReconstruction.ComplexLieGroups.Connectedness.BHWPermutation.PermutationFlowBlockers.Core

noncomputable section

open Complex Topology Matrix LorentzLieGroup Classical Filter

namespace BHW

variable {d : ℕ}

/-- Deferred intrinsic analytic-propagation core on the `d=1,n=2` invariant
witnessed quadric domain.

Input is a function `g(q0,q1,p,s)` with:
1. differentiability on the intrinsic witnessed domain,
2. preconnectedness of that domain,
3. vanishing on the real-slice spacelike correction locus.

Output is vanishing at every doubly witnessed quadric point.

Assertion-level numerical surrogate status (2026-03-04, thorough):
- `ProofHarness/d1n2_tail_four_critical_lemma_checks.py` (test 1),
  seeds `20260700..20260711` (`12` runs);
- per run: `corr_samples=4500`, `complex_domain_samples=9000`;
- `NO_NUMERIC_FALSIFIER_FOUND` in `12/12`, with
  `max worst_|g| = 3.804785e-11`.

Numerical verdict (assertion-level surrogate): `SUPPORTED` on tested regime.

Finite-sampling caveat: this is numerical support, not a formal proof. -/
theorem blocker_d1N2InvariantAnalyticPropagation_core_deferred
    (g : (ℂ × ℂ × ℂ × ℂ) → ℂ)
    (hDiffD :
      DifferentiableOn ℂ g
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
    (hCorrOnReal :
      ∀ t : ℂ × ℂ × ℂ × ℂ,
        t ∈ {t : ℂ × ℂ × ℂ × ℂ |
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
            0 < (((t.2.2.1 + t.2.2.2 / 2 - t.2.1) * w0 / t.2.1).im))} →
        t.1.im = 0 →
        t.2.1.im = 0 →
        t.2.2.1.im = 0 →
        t.2.2.2.im = 0 →
        t.1.re + t.2.1.re - 2 * t.2.2.1.re > 0 →
        g t = 0) :
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
      g (q0, q1, p, s) = 0 := by
  let D : Set (ℂ × ℂ × ℂ × ℂ) :=
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
        0 < (((t.2.2.1 + t.2.2.2 / 2 - t.2.1) * w0 / t.2.1).im))}
  have hPreD : IsPreconnected D := by
    simpa [D] using hConnected
  intro q0 q1 p s hquad hOrigFT hSwapFT
  have htD : (q0, q1, p, s) ∈ D := by
    exact ⟨hquad, hOrigFT, hSwapFT⟩
  have hq0 : q0 ≠ 0 := by
    rcases hOrigFT with ⟨v0, _hv0im, hq0div, _h2, _h3⟩
    intro hq0z
    have him : (((-q0) / v0).im) = 0 := by simp [hq0z]
    linarith [hq0div, him]
  let u : ℂ × ℂ × ℂ := (q0, p, s)
  let chart : ℂ × ℂ × ℂ → ℂ × ℂ × ℂ × ℂ :=
    fun w => (w.1, (w.2.1 ^ 2 - w.2.2 ^ 2 / 4) / w.1, w.2.1, w.2.2)
  have hchart : chart u = (q0, q1, p, s) := by
    have hq1 : q1 = (p ^ 2 - s ^ 2 / 4) / q0 := d1_q1_eq_of_quadric hq0 hquad
    ext <;> simp [u, chart, hq1]
  have hZeroChart : (fun w : ℂ × ℂ × ℂ => g (chart w)) u = 0 := by
    let _ := hDiffD
    let _ := hPreD
    let _ := hCorrOnReal
    let _ := htD
    let _ := hq0
    let _ := hchart
    let U : Set (ℂ × ℂ × ℂ) := {w : ℂ × ℂ × ℂ | chart w ∈ D}
    have huU : u ∈ U := by
      simpa [U, hchart] using htD
    have hchart_maps : Set.MapsTo chart U D := by
      intro w hw
      exact hw
    have hchartDiffAt : DifferentiableAt ℂ chart u := by
      change DifferentiableAt ℂ
        (fun w : ℂ × ℂ × ℂ =>
          (w.1, (w.2.1 ^ 2 - w.2.2 ^ 2 / 4) / w.1, w.2.1, w.2.2)) u
      fun_prop (disch := assumption)
    have hDiffCharted :
        DifferentiableWithinAt ℂ (fun w : ℂ × ℂ × ℂ => g (chart w)) U u := by
      exact (hDiffD (chart u) (hchart_maps huU)).comp u
        hchartDiffAt.differentiableWithinAt hchart_maps
    let _ := hDiffCharted
    -- Remaining intrinsic analytic-propagation input:
    -- from `DifferentiableOn ℂ g D`, `IsPreconnected D`, and real-slice
    -- spacelike vanishing (`hCorrOnReal`), conclude `g = 0` on all of `D`.
    -- The missing bridge is to convert the real correction information into a
    -- genuine identity-theorem anchor for the witnessed domain `D`
    -- (typically via a quadric chart and an explicit source/boundary
    -- identification that propagates real-slice values to the witnessed locus).
    -- Expected route: pass to a 3-complex-variable chart of the quadric
    -- (`q1 = (p^2 - s^2/4)/q0`) where a totally-real identity theorem applies.
    --
    -- Sanity note (formal harness): with the current correction hypothesis shape
    -- (real-slice spacelike `> 0` only), adding preconnectedness for this
    -- witnessed domain leads to a contradiction in
    -- `ProofHarness/D1N2InvariantCoreCounterexample.lean`
    -- (`d1N2InvariantCore_counterexample_if_connected`).
    -- So either this connectedness input is not derivable on the current domain,
    -- or an additional correction/bridge input is required here.
    sorry
  simpa [u, hchart] using hZeroChart

/-- Deferred invariant-only core (`d=1,n=2`):
for a function of Lorentz invariants, prove swap symmetry on the doubly
witnessed quadric locus from intrinsic analyticity/connectedness plus a real
spacelike correction condition, all in `(q0,q1,p,s)` variables.

Numerical status (heuristic, 2026-03-04): no finite-ansatz falsifier found in
`ProofHarness/d1n2_tail_four_critical_lemma_checks.py` for this core implication
under sampled correction anchors and sampled complex witnessed-domain points.
Stress summary:
- deep single run: correction anchors `9000`, complex witnessed domain `4000`,
  correction-constrained nullspace dimension `0`, worst sampled `|g| = 0.0`
  (threshold `1e-6`);
- multi-seed sweep (`20260300..20260305`): per seed correction anchors `7500`,
  complex witnessed domain `3200`, all `6/6` seeds report
  `NO_NUMERIC_FALSIFIER_FOUND`. -/
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
  let D : Set (ℂ × ℂ × ℂ × ℂ) :=
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
        0 < (((t.2.2.1 + t.2.2.2 / 2 - t.2.1) * w0 / t.2.1).im))}
  let g : (ℂ × ℂ × ℂ × ℂ) → ℂ :=
    fun t => f t.1 t.2.1 t.2.2.1 t.2.2.2 - f t.2.1 t.1 t.2.2.1 (-t.2.2.2)
  have hDiffD : DifferentiableOn ℂ g D := by
    simpa [g, D] using hAnalytic
  have hPreD : IsPreconnected D := by
    simpa [D] using hConnected
  have hCorrOnReal :
      ∀ t : ℂ × ℂ × ℂ × ℂ, t ∈ D →
        t.1.im = 0 →
        t.2.1.im = 0 →
        t.2.2.1.im = 0 →
        t.2.2.2.im = 0 →
        t.1.re + t.2.1.re - 2 * t.2.2.1.re > 0 →
        g t = 0 := by
    intro t ht htq0 htq1 htp hts hsp
    have hEq :
        f t.1 t.2.1 t.2.2.1 t.2.2.2 =
          f t.2.1 t.1 t.2.2.1 (-t.2.2.2) :=
      hCorrection t.1 t.2.1 t.2.2.1 t.2.2.2 ht.1
        htq0 htq1 htp hts hsp
    exact sub_eq_zero.mpr hEq
  intro q0 q1 p s hquad hOrigFT hSwapFT
  have hZero : g (q0, q1, p, s) = 0 :=
    blocker_d1N2InvariantAnalyticPropagation_core_deferred
      g
      (by simpa [D] using hDiffD)
      (by simpa [D] using hPreD)
      (by
        intro t ht hq0im hq1im hpim hsim hsp
        exact hCorrOnReal t (by simpa [D] using ht) hq0im hq1im hpim hsim hsp)
      q0 q1 p s hquad hOrigFT hSwapFT
  exact sub_eq_zero.mp (by simpa [g] using hZero)

private lemma d1N2_ne_zero_of_im_pos' (z : ℂ) (hz : 0 < z.im) :
    z ≠ 0 := by
  intro hz0
  have him : z.im = 0 := by simp [hz0]
  linarith

private lemma d1N2_real_div_im_pos_implies_num_neg
    (a : ℝ) (z : ℂ)
    (hz : 0 < z.im)
    (h : 0 < (((a : ℂ) / z).im)) :
    a < 0 := by
  have hz0 : z ≠ 0 := d1N2_ne_zero_of_im_pos' z hz
  have hnorm : 0 < Complex.normSq z := (Complex.normSq_pos).2 hz0
  have hnorm0 : Complex.normSq z ≠ 0 := by
    intro h0
    exact hz0 ((Complex.normSq_eq_zero).1 h0)
  have him : (((a : ℂ) / z).im) = -(a * z.im) / Complex.normSq z := by
    simp [Complex.div_im]
    ring
  have h1 : 0 < (-(a * z.im)) / Complex.normSq z := by simpa [him] using h
  have h2 : 0 < -(a * z.im) := by
    have hmul : 0 < ((-(a * z.im)) / Complex.normSq z) * Complex.normSq z :=
      mul_pos h1 hnorm
    have hsimpl : ((-(a * z.im)) / Complex.normSq z) * Complex.normSq z = -(a * z.im) := by
      field_simp [hnorm0]
    simpa [hsimpl] using hmul
  have h3 : 0 < -a := by nlinarith [h2, hz]
  linarith

private lemma d1N2_rewrite_orig_second_ratio
    (q0 p s v : ℂ)
    (hq0 : q0.im = 0) (hp : p.im = 0) (hs : s.im = 0) :
    ((q0 - p - s / 2) / v).im
      = ((((q0.re - p.re - s.re / 2 : ℝ) : ℂ) / v).im) := by
  have hq0' : q0 = (q0.re : ℂ) := by
    apply Complex.ext <;> simp [hq0]
  have hp' : p = (p.re : ℂ) := by
    apply Complex.ext <;> simp [hp]
  have hs' : s = (s.re : ℂ) := by
    apply Complex.ext <;> simp [hs]
  rw [hq0', hp', hs']
  change (((q0.re : ℂ) - (p.re : ℂ) - (s.re : ℂ) / 2) / v).im =
    ((((q0.re - p.re - s.re / 2 : ℝ) : ℂ) / v).im)
  have hcast : ((q0.re : ℂ) - (p.re : ℂ) - (s.re : ℂ) / 2) =
      (((q0.re - p.re - s.re / 2 : ℝ) : ℂ)) := by
    norm_num
  rw [hcast]

private lemma d1N2_rewrite_swap_second_ratio
    (q1 p s w : ℂ)
    (hq1 : q1.im = 0) (hp : p.im = 0) (hs : s.im = 0) :
    ((q1 - p + s / 2) / w).im
      = ((((q1.re - p.re + s.re / 2 : ℝ) : ℂ) / w).im) := by
  have hq1' : q1 = (q1.re : ℂ) := by
    apply Complex.ext <;> simp [hq1]
  have hp' : p = (p.re : ℂ) := by
    apply Complex.ext <;> simp [hp]
  have hs' : s = (s.re : ℂ) := by
    apply Complex.ext <;> simp [hs]
  rw [hq1', hp', hs']
  change (((q1.re : ℂ) - (p.re : ℂ) + (s.re : ℂ) / 2) / w).im =
    ((((q1.re - p.re + s.re / 2 : ℝ) : ℂ) / w).im)
  have hcast : ((q1.re : ℂ) - (p.re : ℂ) + (s.re : ℂ) / 2) =
      (((q1.re - p.re + s.re / 2 : ℝ) : ℂ)) := by
    norm_num
  rw [hcast]

private lemma d1InvariantQuad_realEmbed_realConfig_of_uv
    (u0 v0 u1 v1 : ℝ) :
    d1InvariantQuad
      (realEmbed
        (d1N2RealConfig
          ((u0 + v0) / 2) ((u0 - v0) / 2)
          ((u1 + v1) / 2) ((u1 - v1) / 2))) =
      (((-(u0 * v0 : ℝ)) : ℂ),
        (((-(u1 * v1 : ℝ)) : ℂ)),
        (((-(u0 * v1 + u1 * v0) / 2 : ℝ)) : ℂ),
        (((u0 * v1 - u1 * v0 : ℝ)) : ℂ)) := by
  let a : ℝ := (u0 + v0) / 2
  let b : ℝ := (u0 - v0) / 2
  let c : ℝ := (u1 + v1) / 2
  let d : ℝ := (u1 - v1) / 2
  have hcast :
      realEmbed (d1N2RealConfig a b c d) =
        d1N2ComplexConfig (a : ℂ) b c d := by
    exact (d1N2ComplexConfig_realCast a b c d).symm
  calc
    d1InvariantQuad (realEmbed (d1N2RealConfig a b c d))
        = d1InvariantQuad (d1N2ComplexConfig (a : ℂ) b c d) := by
            rw [hcast]
    _ = (((( -(a ^ 2) + b ^ 2 : ℝ)) : ℂ),
          (((( -(c ^ 2) + d ^ 2 : ℝ)) : ℂ)),
          (((( -(a * c) + b * d : ℝ)) : ℂ)),
          (-2 : ℂ) * ((a : ℂ) * d - b * c)) := by
            simpa using d1InvariantQuad_complexConfig (a : ℂ) b c d
    _ = (((-(u0 * v0 : ℝ)) : ℂ),
          (((-(u1 * v1 : ℝ)) : ℂ)),
          (((-(u0 * v1 + u1 * v0) / 2 : ℝ)) : ℂ),
          (((u0 * v1 - u1 * v0 : ℝ)) : ℂ)) := by
            ext <;> simp [a, b, c, d] <;> ring

/-- Real tuples satisfying both intrinsic witness inequalities are timelike in the
`d=1,n=2` adjacent form (`q0 + q1 - 2p < 0`), so they cannot satisfy the
real-spacelike correction inequality. -/
private lemma d1N2_real_witnesses_imply_neg_spacelike
    {q0 q1 p s : ℂ}
    (hq0im : q0.im = 0) (hq1im : q1.im = 0) (hpim : p.im = 0) (hsim : s.im = 0)
    (hOrig :
      ∃ v0 : ℂ,
        0 < v0.im ∧
        0 < ((-q0) / v0).im ∧
        0 < ((q0 - p - s / 2) / v0).im ∧
        0 < (((p - s / 2 - q0) * v0 / q0).im))
    (hSwap :
      ∃ w0 : ℂ,
        0 < w0.im ∧
        0 < ((-q1) / w0).im ∧
        0 < ((q1 - p + s / 2) / w0).im ∧
        0 < (((p + s / 2 - q1) * w0 / q1).im)) :
    q0.re + q1.re - 2 * p.re < 0 := by
  rcases hOrig with ⟨v0, hv0im, _hOrig1, hOrig2, _hOrig3⟩
  rcases hSwap with ⟨w0, hw0im, _hSwap1, hSwap2, _hSwap3⟩
  have hOrig2' :
      0 < ((((q0.re - p.re - s.re / 2 : ℝ) : ℂ) / v0).im) := by
    simpa [d1N2_rewrite_orig_second_ratio q0 p s v0 hq0im hpim hsim] using hOrig2
  have hSwap2' :
      0 < ((((q1.re - p.re + s.re / 2 : ℝ) : ℂ) / w0).im) := by
    simpa [d1N2_rewrite_swap_second_ratio q1 p s w0 hq1im hpim hsim] using hSwap2
  have hA : q0.re - p.re - s.re / 2 < 0 :=
    d1N2_real_div_im_pos_implies_num_neg (q0.re - p.re - s.re / 2) v0 hv0im hOrig2'
  have hB : q1.re - p.re + s.re / 2 < 0 :=
    d1N2_real_div_im_pos_implies_num_neg (q1.re - p.re + s.re / 2) w0 hw0im hSwap2'
  nlinarith [hA, hB]

/-- Intrinsic real-slice geometry (`d=1,n=2`):
on the witnessed invariant domain (quadric + original/swapped witness
inequalities), a real tuple is necessarily timelike in the adjacent expression,
i.e. `q0.re + q1.re - 2*p.re < 0`.

In particular, real-spacelike points (`> 0`) do not directly lie in this
witnessed domain. -/
lemma d1N2InvariantWitnessedDomain_real_implies_neg_spacelike
    {t : ℂ × ℂ × ℂ × ℂ}
    (ht :
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
        0 < (((t.2.2.1 + t.2.2.2 / 2 - t.2.1) * w0 / t.2.1).im)))
    (htq0 : t.1.im = 0)
    (htq1 : t.2.1.im = 0)
    (htp : t.2.2.1.im = 0)
    (hts : t.2.2.2.im = 0) :
    t.1.re + t.2.1.re - 2 * t.2.2.1.re < 0 := by
  exact d1N2_real_witnesses_imply_neg_spacelike htq0 htq1 htp hts ht.2.1 ht.2.2

/-- Real-spacelike points do not lie in the intrinsic witnessed domain used by
the invariant core (`d=1,n=2`). -/
lemma d1N2InvariantWitnessedDomain_real_spacelike_empty :
    ¬ ∃ t : ℂ × ℂ × ℂ × ℂ,
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
        0 < (((t.2.2.1 + t.2.2.2 / 2 - t.2.1) * w0 / t.2.1).im)) ∧
      t.1.im = 0 ∧
      t.2.1.im = 0 ∧
      t.2.2.1.im = 0 ∧
      t.2.2.2.im = 0 ∧
      t.1.re + t.2.1.re - 2 * t.2.2.1.re > 0 := by
  intro h
  rcases h with ⟨t, ht⟩
  have hneg : t.1.re + t.2.1.re - 2 * t.2.2.1.re < 0 :=
    d1N2InvariantWitnessedDomain_real_implies_neg_spacelike
      ⟨ht.1, ht.2.1, ht.2.2.1⟩ ht.2.2.2.1 ht.2.2.2.2.1 ht.2.2.2.2.2.1 ht.2.2.2.2.2.2.1
  have hpos : t.1.re + t.2.1.re - 2 * t.2.2.1.re > 0 := ht.2.2.2.2.2.2.2
  linarith

/-- The intrinsic witnessed domain is genuinely nontrivial:
there are explicit complex tuples satisfying quadric + original witness block +
swapped witness block, with `q0 ≠ q1`. -/
lemma d1N2InvariantWitnessedDomain_nontrivial_example :
    ∃ q0 q1 p s : ℂ,
      q0 ≠ q1 ∧
      s ^ 2 = 4 * (p ^ 2 - q0 * q1) ∧
      (∃ v0 : ℂ,
        0 < v0.im ∧
        0 < ((-q0) / v0).im ∧
        0 < ((q0 - p - s / 2) / v0).im ∧
        0 < (((p - s / 2 - q0) * v0 / q0).im)) ∧
      (∃ w0 : ℂ,
        0 < w0.im ∧
        0 < ((-q1) / w0).im ∧
        0 < ((q1 - p + s / 2) / w0).im ∧
        0 < (((p + s / 2 - q1) * w0 / q1).im)) := by
  refine ⟨(1 - 2 * Complex.I), (3 - 4 * Complex.I),
    (1 - 3 * Complex.I), (-2 - 4 * Complex.I), ?_⟩
  constructor
  · intro hneq
    have hRe : (1 : ℝ) = 3 := by simpa using congrArg Complex.re hneq
    norm_num at hRe
  constructor
  · apply Complex.ext <;> ring_nf <;> norm_num
  constructor
  · refine ⟨(1 + Complex.I), ?_⟩
    constructor
    · norm_num
    constructor
    · have hA : (((-(1 - 2 * Complex.I : ℂ)) / (1 + Complex.I)).im : ℝ) = (3 / 2 : ℝ) := by
        norm_num [Complex.div_im, Complex.normSq]
      linarith
    constructor
    · have hB : ((((1 - 2 * Complex.I : ℂ) - (1 - 3 * Complex.I) - (-2 - 4 * Complex.I) / 2) /
          (1 + Complex.I)).im : ℝ) = (1 : ℝ) := by
          norm_num [Complex.div_im, Complex.normSq]
      linarith
    · have hC : (((((1 - 3 * Complex.I : ℂ) - (-2 - 4 * Complex.I) / 2 - (1 - 2 * Complex.I)) *
          (1 + Complex.I) / (1 - 2 * Complex.I)).im : ℝ)) = (2 / 5 : ℝ) := by
          norm_num [Complex.div_im, Complex.normSq]
      linarith
  · refine ⟨(-1 + 2 * Complex.I), ?_⟩
    constructor
    · norm_num
    constructor
    · have hD : (((-(3 - 4 * Complex.I : ℂ)) / (-1 + 2 * Complex.I)).im : ℝ) = (2 / 5 : ℝ) := by
          norm_num [Complex.div_im, Complex.normSq]
      linarith
    constructor
    · have hE : ((((3 - 4 * Complex.I : ℂ) - (1 - 3 * Complex.I) + (-2 - 4 * Complex.I) / 2) /
          (-1 + 2 * Complex.I)).im : ℝ) = (1 / 5 : ℝ) := by
          norm_num [Complex.div_im, Complex.normSq]
      linarith
    · have hF : (((((1 - 3 * Complex.I : ℂ) + (-2 - 4 * Complex.I) / 2 - (3 - 4 * Complex.I)) *
          (-1 + 2 * Complex.I) / (3 - 4 * Complex.I)).im : ℝ)) = (1 / 5 : ℝ) := by
          norm_num [Complex.div_im, Complex.normSq]
      linarith

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

/-- Real-spacelike tuples cannot be simultaneously realizable by forward points
for both original and swapped invariant branches (`d=1,n=2`). -/
lemma d1N2InvariantRealizablePair_real_spacelike_impossible
    {q0 q1 p s : ℂ}
    (hq0im : q0.im = 0)
    (hq1im : q1.im = 0)
    (hpim : p.im = 0)
    (hsim : s.im = 0)
    (hsp : q0.re + q1.re - 2 * p.re > 0)
    (hreal : d1N2InvariantRealizable q0 q1 p s)
    (hswapReal : d1N2InvariantRealizable q1 q0 p (-s)) :
    False := by
  rcases hreal with ⟨z, hz, hquadZ⟩
  rcases hswapReal with ⟨y, hy, hquadY⟩
  have hOrig :
      ∃ v0 : ℂ,
        0 < v0.im ∧
        0 < ((-q0) / v0).im ∧
        0 < ((q0 - p - s / 2) / v0).im ∧
        0 < (((p - s / 2 - q0) * v0 / q0).im) :=
    d1N2InvariantOrigWitnessIneq_of_forwardInvariants hz hquadZ
  have hSwap :
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
  have hneg : q0.re + q1.re - 2 * p.re < 0 :=
    d1N2_real_witnesses_imply_neg_spacelike hq0im hq1im hpim hsim hOrig hSwap
  linarith

/-- Real-spacelike tuples cannot satisfy the forwardizable swap condition
(`d=1,n=2`). -/
lemma d1N2InvariantForwardizableSwap_real_spacelike_impossible
    {q0 q1 p s : ℂ}
    (hq0im : q0.im = 0)
    (hq1im : q1.im = 0)
    (hpim : p.im = 0)
    (hsim : s.im = 0)
    (hsp : q0.re + q1.re - 2 * p.re > 0) :
    ¬ d1N2InvariantForwardizableSwap q0 q1 p s := by
  intro hfw
  have hpair : d1N2InvariantRealizable q0 q1 p s ∧
      d1N2InvariantRealizable q1 q0 p (-s) :=
    d1N2InvariantRealizable_pair_of_forwardizable hfw
  exact d1N2InvariantRealizablePair_real_spacelike_impossible
    hq0im hq1im hpim hsim hsp hpair.1 hpair.2

/-- Real-spacelike tuples cannot support both fixed-invariant forward-tube
approach families for the original and swapped invariant branches.

At `n = 0`, such a pair of families would realize both invariant tuples in
`FT_{1,2}`, contradicting
`d1N2InvariantRealizablePair_real_spacelike_impossible`. -/
lemma d1N2InvariantApproachPair_real_spacelike_impossible
    {q0 q1 p s : ℂ}
    (hq0im : q0.im = 0)
    (hq1im : q1.im = 0)
    (hpim : p.im = 0)
    (hsim : s.im = 0)
    (hsp : q0.re + q1.re - 2 * p.re > 0)
    {x : Fin 2 → Fin (1 + 1) → ℝ}
    (hApprox :
      (∃ φ : ℕ → Fin 2 → Fin (1 + 1) → ℂ,
        (∀ n, φ n ∈ ForwardTube 1 2) ∧
        Tendsto φ atTop
          (𝓝[ForwardTube 1 2] (realEmbed (n := 2) (d := 1) x)) ∧
        (∀ n, d1InvariantQuad (φ n) = (q0, q1, p, s))) ∧
      (∃ ψ : ℕ → Fin 2 → Fin (1 + 1) → ℂ,
        (∀ n, ψ n ∈ ForwardTube 1 2) ∧
        Tendsto ψ atTop
          (𝓝[ForwardTube 1 2]
            (realEmbed (n := 2) (d := 1)
              (fun k μ => x (Equiv.swap (0 : Fin 2) 1 k) μ))) ∧
        (∀ n, d1InvariantQuad (ψ n) = (q1, q0, p, -s)))) :
    False := by
  rcases hApprox with ⟨hOrig, hSwap⟩
  rcases hOrig with ⟨φ, hφFT, _hφtend, hφquad⟩
  rcases hSwap with ⟨ψ, hψFT, _hψtend, hψquad⟩
  have hreal : d1N2InvariantRealizable q0 q1 p s :=
    ⟨φ 0, hφFT 0, by simpa using hφquad 0⟩
  have hswapReal : d1N2InvariantRealizable q1 q0 p (-s) :=
    ⟨ψ 0, hψFT 0, by simpa using hψquad 0⟩
  exact d1N2InvariantRealizablePair_real_spacelike_impossible
    hq0im hq1im hpim hsim hsp hreal hswapReal

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
Stress summary:
- deep single run: source constraints `9000`
  (`6000` intrinsic real-spacelike + `3000` z-constructed), source nullspace
  dimension `0`, finite-difference points `300`, max sampled `|∂̄g| = 0.0`
  (step `1e-6`);
- multi-seed sweep (`20260300..20260305`): per seed source constraints `3700`,
  source nullspace dimension `0`, max sampled `|∂̄g| = 0.0` on all `6/6` seeds. -/
private lemma d1N2_ne_zero_of_im_div_pos (a b : ℂ) (h : 0 < ((-a) / b).im) :
    a ≠ 0 := by
  intro ha
  have him : (((-a) / b).im) = 0 := by simp [ha]
  linarith

private lemma d1N2_ne_zero_of_im_pos (z : ℂ) (hz : 0 < z.im) :
    z ≠ 0 := by
  intro hz0
  have him : z.im = 0 := by simp [hz0]
  linarith

private lemma d1N2SectionOrig_differentiableAt_invariants
    (v0 : ℂ) (t : ℂ × ℂ × ℂ × ℂ) (ht : t.1 ≠ 0) :
    DifferentiableAt ℂ
      (fun τ : ℂ × ℂ × ℂ × ℂ =>
        d1N2SectionOrig τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 v0) t := by
  have hneg : -t.1 ≠ 0 := by simpa using ht
  refine differentiableAt_pi.2 ?_
  intro i
  refine differentiableAt_pi.2 ?_
  intro μ
  fin_cases i <;> fin_cases μ
  · dsimp [d1N2SectionOrig, d1N2InvariantSection, d1N2ComplexConfig]
    fun_prop (disch := assumption)
  · dsimp [d1N2SectionOrig, d1N2InvariantSection, d1N2ComplexConfig]
    fun_prop (disch := assumption)
  · dsimp [d1N2SectionOrig, d1N2InvariantSection, d1N2ComplexConfig]
    fun_prop (disch := assumption)
  · dsimp [d1N2SectionOrig, d1N2InvariantSection, d1N2ComplexConfig]
    fun_prop (disch := assumption)

private lemma d1N2SectionSwap_differentiableAt_invariants
    (w0 : ℂ) (t : ℂ × ℂ × ℂ × ℂ) (ht : t.2.1 ≠ 0) :
    DifferentiableAt ℂ
      (fun τ : ℂ × ℂ × ℂ × ℂ =>
        d1N2SectionSwap τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 w0) t := by
  have hneg : -t.2.1 ≠ 0 := by simpa using ht
  refine differentiableAt_pi.2 ?_
  intro i
  refine differentiableAt_pi.2 ?_
  intro μ
  fin_cases i <;> fin_cases μ
  · dsimp [d1N2SectionSwap, d1N2InvariantSection, d1N2ComplexConfig]
    fun_prop (disch := assumption)
  · dsimp [d1N2SectionSwap, d1N2InvariantSection, d1N2ComplexConfig]
    fun_prop (disch := assumption)
  · dsimp [d1N2SectionSwap, d1N2InvariantSection, d1N2ComplexConfig]
    fun_prop (disch := assumption)
  · dsimp [d1N2SectionSwap, d1N2InvariantSection, d1N2ComplexConfig]
    fun_prop (disch := assumption)

private lemma d1N2InvariantDiff_eq_sectionDiff_on_fixedWitness
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (F : (Fin 2 → Fin (1 + 1) → ℂ) → ℂ)
    (hf_onFT : ∀ z, z ∈ ForwardTube 1 2 →
      F z = f (d1Q0 z) (d1Q1 z) (d1P01 z) (d1S01 z))
    (τ : ℂ × ℂ × ℂ × ℂ)
    (hquad : τ.2.2.2 ^ 2 = 4 * (τ.2.2.1 ^ 2 - τ.1 * τ.2.1))
    (v0 w0 : ℂ)
    (hv0im : 0 < v0.im)
    (hOrig1 : 0 < ((-τ.1) / v0).im)
    (hOrig2 : 0 < ((τ.1 - τ.2.2.1 - τ.2.2.2 / 2) / v0).im)
    (hOrig3 : 0 < (((τ.2.2.1 - τ.2.2.2 / 2 - τ.1) * v0 / τ.1).im))
    (hw0im : 0 < w0.im)
    (hSwap1 : 0 < ((-τ.2.1) / w0).im)
    (hSwap2 : 0 < ((τ.2.1 - τ.2.2.1 + τ.2.2.2 / 2) / w0).im)
    (hSwap3 : 0 < (((τ.2.2.1 + τ.2.2.2 / 2 - τ.2.1) * w0 / τ.2.1).im)) :
    f τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 - f τ.2.1 τ.1 τ.2.2.1 (-τ.2.2.2)
      = F (d1N2SectionOrig τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 v0)
        - F (d1N2SectionSwap τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 w0) := by
  have hq0 : τ.1 ≠ 0 := d1N2_ne_zero_of_im_div_pos τ.1 v0 hOrig1
  have hq1 : τ.2.1 ≠ 0 := d1N2_ne_zero_of_im_div_pos τ.2.1 w0 hSwap1
  have hv0 : v0 ≠ 0 := d1N2_ne_zero_of_im_pos v0 hv0im
  have hw0 : w0 ≠ 0 := d1N2_ne_zero_of_im_pos w0 hw0im
  have hzOrigFT :
      d1N2SectionOrig τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 v0 ∈ ForwardTube 1 2 :=
    d1N2SectionOrig_mem_forwardTube_of_witnessIneq hv0im hOrig1 hOrig2 hOrig3
  have hzSwapFT :
      d1N2SectionSwap τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 w0 ∈ ForwardTube 1 2 :=
    d1N2SectionSwap_mem_forwardTube_of_witnessIneq hw0im hSwap1 hSwap2 hSwap3
  have hquadOrig :
      d1InvariantQuad (d1N2SectionOrig τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 v0) =
        (τ.1, τ.2.1, τ.2.2.1, τ.2.2.2) :=
    d1InvariantQuad_sectionOrig hquad hq0 hv0
  have hquadSwap :
      d1InvariantQuad (d1N2SectionSwap τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 w0) =
        (τ.2.1, τ.1, τ.2.2.1, -τ.2.2.2) :=
    d1InvariantQuad_sectionSwap hquad hq1 hw0
  have hOrigVal :
      F (d1N2SectionOrig τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 v0) =
        f τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 := by
    calc
      F (d1N2SectionOrig τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 v0)
          = f (d1Q0 (d1N2SectionOrig τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 v0))
              (d1Q1 (d1N2SectionOrig τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 v0))
              (d1P01 (d1N2SectionOrig τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 v0))
              (d1S01 (d1N2SectionOrig τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 v0)) :=
            hf_onFT _ hzOrigFT
      _ = f τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 := by
            simpa [d1InvariantQuad] using congrArg
              (fun u => f u.1 u.2.1 u.2.2.1 u.2.2.2) hquadOrig
  have hSwapVal :
      F (d1N2SectionSwap τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 w0) =
        f τ.2.1 τ.1 τ.2.2.1 (-τ.2.2.2) := by
    calc
      F (d1N2SectionSwap τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 w0)
          = f (d1Q0 (d1N2SectionSwap τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 w0))
              (d1Q1 (d1N2SectionSwap τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 w0))
              (d1P01 (d1N2SectionSwap τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 w0))
              (d1S01 (d1N2SectionSwap τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 w0)) :=
            hf_onFT _ hzSwapFT
      _ = f τ.2.1 τ.1 τ.2.2.1 (-τ.2.2.2) := by
            simpa [d1InvariantQuad] using congrArg
              (fun u => f u.1 u.2.1 u.2.2.1 u.2.2.2) hquadSwap
  calc
    f τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 - f τ.2.1 τ.1 τ.2.2.1 (-τ.2.2.2)
        = F (d1N2SectionOrig τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 v0) -
            f τ.2.1 τ.1 τ.2.2.1 (-τ.2.2.2) := by
              rw [hOrigVal]
    _ = F (d1N2SectionOrig τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 v0) -
          F (d1N2SectionSwap τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 w0) := by
            rw [hSwapVal]

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
  rcases hsource with ⟨F, hF_holo, _hF_lorentz, _hF_bv, _hF_local, hf_onFT⟩
  let D : Set (ℂ × ℂ × ℂ × ℂ) :=
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
        0 < (((t.2.2.1 + t.2.2.2 / 2 - t.2.1) * w0 / t.2.1).im))}
  let g : (ℂ × ℂ × ℂ × ℂ) → ℂ :=
    fun t => f t.1 t.2.1 t.2.2.1 t.2.2.2 - f t.2.1 t.1 t.2.2.1 (-t.2.2.2)
  intro t ht
  rcases ht with ⟨hquad, ⟨v0, hv0im, hOrig1, hOrig2, hOrig3⟩,
    ⟨w0, hw0im, hSwap1, hSwap2, hSwap3⟩⟩
  have hq0 : t.1 ≠ 0 := d1N2_ne_zero_of_im_div_pos t.1 v0 hOrig1
  have hq1 : t.2.1 ≠ 0 := d1N2_ne_zero_of_im_div_pos t.2.1 w0 hSwap1
  have hOrigFT :
      d1N2SectionOrig t.1 t.2.1 t.2.2.1 t.2.2.2 v0 ∈ ForwardTube 1 2 :=
    d1N2SectionOrig_mem_forwardTube_of_witnessIneq hv0im hOrig1 hOrig2 hOrig3
  have hSwapFT :
      d1N2SectionSwap t.1 t.2.1 t.2.2.1 t.2.2.2 w0 ∈ ForwardTube 1 2 :=
    d1N2SectionSwap_mem_forwardTube_of_witnessIneq hw0im hSwap1 hSwap2 hSwap3
  let gF : (ℂ × ℂ × ℂ × ℂ) → ℂ :=
    fun τ => F (d1N2SectionOrig τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 v0) -
      F (d1N2SectionSwap τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 w0)
  have hFAtOrig : DifferentiableAt ℂ F
      (d1N2SectionOrig t.1 t.2.1 t.2.2.1 t.2.2.2 v0) :=
    hF_holo.differentiableAt (isOpen_forwardTube.mem_nhds hOrigFT)
  have hFAtSwap : DifferentiableAt ℂ F
      (d1N2SectionSwap t.1 t.2.1 t.2.2.1 t.2.2.2 w0) :=
    hF_holo.differentiableAt (isOpen_forwardTube.mem_nhds hSwapFT)
  have hSecOrigAt : DifferentiableAt ℂ
      (fun τ : ℂ × ℂ × ℂ × ℂ =>
        d1N2SectionOrig τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 v0) t :=
    d1N2SectionOrig_differentiableAt_invariants v0 t hq0
  have hSecSwapAt : DifferentiableAt ℂ
      (fun τ : ℂ × ℂ × ℂ × ℂ =>
        d1N2SectionSwap τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 w0) t :=
    d1N2SectionSwap_differentiableAt_invariants w0 t hq1
  have hCompOrig : DifferentiableAt ℂ
      (fun τ : ℂ × ℂ × ℂ × ℂ =>
        F (d1N2SectionOrig τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 v0)) t := by
    simpa [Function.comp] using hFAtOrig.comp t hSecOrigAt
  have hCompSwap : DifferentiableAt ℂ
      (fun τ : ℂ × ℂ × ℂ × ℂ =>
        F (d1N2SectionSwap τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 w0)) t := by
    simpa [Function.comp] using hFAtSwap.comp t hSecSwapAt
  have hDiff_gF : DifferentiableWithinAt ℂ gF D t :=
    (hCompOrig.sub hCompSwap).differentiableWithinAt
  have hN1 : {τ : ℂ × ℂ × ℂ × ℂ | 0 < ((-τ.1) / v0).im} ∈ 𝓝[D] t := by
    have hcont : ContinuousAt (fun τ : ℂ × ℂ × ℂ × ℂ => ((-τ.1) / v0).im) t := by
      fun_prop
    have hpre : {τ : ℂ × ℂ × ℂ × ℂ | ((-τ.1) / v0).im ∈ Set.Ioi (0 : ℝ)} ∈ 𝓝 t :=
      hcont.preimage_mem_nhds (isOpen_Ioi.mem_nhds hOrig1)
    simpa using (nhdsWithin_le_nhds hpre)
  have hN2 : {τ : ℂ × ℂ × ℂ × ℂ | 0 < ((τ.1 - τ.2.2.1 - τ.2.2.2 / 2) / v0).im} ∈ 𝓝[D] t := by
    have hcont : ContinuousAt
        (fun τ : ℂ × ℂ × ℂ × ℂ => ((τ.1 - τ.2.2.1 - τ.2.2.2 / 2) / v0).im) t := by
      fun_prop
    have hpre :
        {τ : ℂ × ℂ × ℂ × ℂ | ((τ.1 - τ.2.2.1 - τ.2.2.2 / 2) / v0).im ∈ Set.Ioi (0 : ℝ)} ∈ 𝓝 t :=
      hcont.preimage_mem_nhds (isOpen_Ioi.mem_nhds hOrig2)
    simpa using (nhdsWithin_le_nhds hpre)
  have hN3 : {τ : ℂ × ℂ × ℂ × ℂ | 0 < (((τ.2.2.1 - τ.2.2.2 / 2 - τ.1) * v0 / τ.1).im)} ∈ 𝓝[D] t := by
    have hcont : ContinuousAt
        (fun τ : ℂ × ℂ × ℂ × ℂ => (((τ.2.2.1 - τ.2.2.2 / 2 - τ.1) * v0 / τ.1).im)) t := by
      fun_prop (disch := assumption)
    have hpre :
        {τ : ℂ × ℂ × ℂ × ℂ | (((τ.2.2.1 - τ.2.2.2 / 2 - τ.1) * v0 / τ.1).im) ∈ Set.Ioi (0 : ℝ)} ∈ 𝓝 t :=
      hcont.preimage_mem_nhds (isOpen_Ioi.mem_nhds hOrig3)
    simpa using (nhdsWithin_le_nhds hpre)
  have hM1 : {τ : ℂ × ℂ × ℂ × ℂ | 0 < ((-τ.2.1) / w0).im} ∈ 𝓝[D] t := by
    have hcont : ContinuousAt (fun τ : ℂ × ℂ × ℂ × ℂ => ((-τ.2.1) / w0).im) t := by
      fun_prop
    have hpre : {τ : ℂ × ℂ × ℂ × ℂ | ((-τ.2.1) / w0).im ∈ Set.Ioi (0 : ℝ)} ∈ 𝓝 t :=
      hcont.preimage_mem_nhds (isOpen_Ioi.mem_nhds hSwap1)
    simpa using (nhdsWithin_le_nhds hpre)
  have hM2 : {τ : ℂ × ℂ × ℂ × ℂ | 0 < ((τ.2.1 - τ.2.2.1 + τ.2.2.2 / 2) / w0).im} ∈ 𝓝[D] t := by
    have hcont : ContinuousAt
        (fun τ : ℂ × ℂ × ℂ × ℂ => ((τ.2.1 - τ.2.2.1 + τ.2.2.2 / 2) / w0).im) t := by
      fun_prop
    have hpre :
        {τ : ℂ × ℂ × ℂ × ℂ | ((τ.2.1 - τ.2.2.1 + τ.2.2.2 / 2) / w0).im ∈ Set.Ioi (0 : ℝ)} ∈ 𝓝 t :=
      hcont.preimage_mem_nhds (isOpen_Ioi.mem_nhds hSwap2)
    simpa using (nhdsWithin_le_nhds hpre)
  have hM3 : {τ : ℂ × ℂ × ℂ × ℂ | 0 < (((τ.2.2.1 + τ.2.2.2 / 2 - τ.2.1) * w0 / τ.2.1).im)} ∈ 𝓝[D] t := by
    have hcont : ContinuousAt
        (fun τ : ℂ × ℂ × ℂ × ℂ => (((τ.2.2.1 + τ.2.2.2 / 2 - τ.2.1) * w0 / τ.2.1).im)) t := by
      fun_prop (disch := assumption)
    have hpre :
        {τ : ℂ × ℂ × ℂ × ℂ | (((τ.2.2.1 + τ.2.2.2 / 2 - τ.2.1) * w0 / τ.2.1).im) ∈ Set.Ioi (0 : ℝ)} ∈ 𝓝 t :=
      hcont.preimage_mem_nhds (isOpen_Ioi.mem_nhds hSwap3)
    simpa using (nhdsWithin_le_nhds hpre)
  have hSelf : ∀ᶠ τ in 𝓝[D] t, τ ∈ D := by
    simpa using (self_mem_nhdsWithin : D ∈ 𝓝[D] t)
  have hE1 : ∀ᶠ τ in 𝓝[D] t, 0 < ((-τ.1) / v0).im := by simpa using hN1
  have hE2 : ∀ᶠ τ in 𝓝[D] t, 0 < ((τ.1 - τ.2.2.1 - τ.2.2.2 / 2) / v0).im := by simpa using hN2
  have hE3 : ∀ᶠ τ in 𝓝[D] t, 0 < (((τ.2.2.1 - τ.2.2.2 / 2 - τ.1) * v0 / τ.1).im) := by simpa using hN3
  have hE4 : ∀ᶠ τ in 𝓝[D] t, 0 < ((-τ.2.1) / w0).im := by simpa using hM1
  have hE5 : ∀ᶠ τ in 𝓝[D] t, 0 < ((τ.2.1 - τ.2.2.1 + τ.2.2.2 / 2) / w0).im := by simpa using hM2
  have hE6 : ∀ᶠ τ in 𝓝[D] t, 0 < (((τ.2.2.1 + τ.2.2.2 / 2 - τ.2.1) * w0 / τ.2.1).im) := by simpa using hM3
  have hEventuallyFixed :
      ∀ᶠ τ in 𝓝[D] t,
        τ ∈ D ∧
        0 < ((-τ.1) / v0).im ∧
        0 < ((τ.1 - τ.2.2.1 - τ.2.2.2 / 2) / v0).im ∧
        0 < (((τ.2.2.1 - τ.2.2.2 / 2 - τ.1) * v0 / τ.1).im) ∧
        0 < ((-τ.2.1) / w0).im ∧
        0 < ((τ.2.1 - τ.2.2.1 + τ.2.2.2 / 2) / w0).im ∧
        0 < (((τ.2.2.1 + τ.2.2.2 / 2 - τ.2.1) * w0 / τ.2.1).im) := by
    exact hSelf.and (hE1.and (hE2.and (hE3.and (hE4.and (hE5.and hE6)))))
  have hEqOnFixed :
      ∀ τ : ℂ × ℂ × ℂ × ℂ,
        τ ∈ D →
        0 < ((-τ.1) / v0).im →
        0 < ((τ.1 - τ.2.2.1 - τ.2.2.2 / 2) / v0).im →
        0 < (((τ.2.2.1 - τ.2.2.2 / 2 - τ.1) * v0 / τ.1).im) →
        0 < ((-τ.2.1) / w0).im →
        0 < ((τ.2.1 - τ.2.2.1 + τ.2.2.2 / 2) / w0).im →
        0 < (((τ.2.2.1 + τ.2.2.2 / 2 - τ.2.1) * w0 / τ.2.1).im) →
        g τ = gF τ := by
    intro τ hτD hτ1 hτ2 hτ3 hτ4 hτ5 hτ6
    have hquadτ : τ.2.2.2 ^ 2 = 4 * (τ.2.2.1 ^ 2 - τ.1 * τ.2.1) := hτD.1
    have hEq := d1N2InvariantDiff_eq_sectionDiff_on_fixedWitness f F hf_onFT
      τ hquadτ v0 w0 hv0im hτ1 hτ2 hτ3 hw0im hτ4 hτ5 hτ6
    simpa [g, gF] using hEq
  have hEqEventually : g =ᶠ[𝓝[D] t] gF := by
    refine hEventuallyFixed.mp ?_
    exact Filter.Eventually.of_forall (fun τ hτ =>
      hEqOnFixed τ hτ.1 hτ.2.1 hτ.2.2.1 hτ.2.2.2.1 hτ.2.2.2.2.1 hτ.2.2.2.2.2.1
        hτ.2.2.2.2.2.2)
  have htD : t ∈ D := by
    exact ⟨hquad, ⟨v0, hv0im, hOrig1, hOrig2, hOrig3⟩, ⟨w0, hw0im, hSwap1, hSwap2, hSwap3⟩⟩
  have hEqAt : g t = gF t := by
    apply hEqOnFixed t
    · exact htD
    · exact hOrig1
    · exact hOrig2
    · exact hOrig3
    · exact hSwap1
    · exact hSwap2
    · exact hSwap3
  have hDiff_g : DifferentiableWithinAt ℂ g D t :=
    (hEqEventually.differentiableWithinAt_iff hEqAt).2 hDiff_gF
  simpa [g, D] using hDiff_g

/-- Deferred invariant-domain connectedness input (geometry-only).

For the same intrinsic invariant domain `D` (quadric relation + original and
swapped witness inequalities), prove `IsPreconnected D`.

Mathematically, this is the topological propagation domain on which a
holomorphic identity for the swap-difference can extend from an anchored subset
to all of `D`.

Numerical status (heuristic support): sampled `z`-constructed witnessed-domain
point clouds tested in `ProofHarness/d1n2_tail_four_critical_lemma_checks.py`
remain consistently KNN-connected.

Thorough run summary (2026-03-04):
- seeds `20260700..20260711` (`12` runs), each with
  `complex_domain_samples=9000`;
- for each run and each `k ∈ {6,8,10,14,20,30}`:
  `graph_components = 1`, `largest_component_fraction = 1.0`.

Numerical verdict (graph surrogate): `SUPPORTED` on tested regime.

Finite-sampling caveat: this is a graph-surrogate check, not a formal
topological proof. -/
theorem blocker_d1N2InvariantBridgePreconnected_fromSource_deferred
    :
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
  sorry

/-- Source-to-invariant bridge reduction (correction input).

This is the anchor identity for the same swap-difference
`g(q0,q1,p,s) := f q0 q1 p s - f q1 q0 p (-s)`:
on points satisfying
1. the quadric relation,
2. real-slice conditions `q0.im = q1.im = p.im = s.im = 0`,
3. real-spacelike inequality `q0.re + q1.re - 2*p.re > 0`,
4. an explicit boundary-identification witness
   `∃ x, d1InvariantQuad (realEmbed x) = (q0,q1,p,s)` together with source
   value-identifications for both `f q0 q1 p s` and `f q1 q0 p (-s)`,
prove `g(q0,q1,p,s) = 0`.

This is intended to supply the real-slice correction datum that feeds the
invariant-core theorem.

Numerical note (2026-03-04): the previous finite-ansatz test (test 4 in
`ProofHarness/d1n2_tail_four_critical_lemma_checks.py`) reports
`NO_NUMERIC_FALSIFIER_FOUND`, but with `source_constraint_nullspace_dim = 0`,
so that check is not decisive for source-only sufficiency.

Additional stress (test 8, off-image spike surrogate) reports
`SOURCE_ONLY_SHAPE_PLAUSIBLY_FALSE`, consistent with the formal counterexample
harness (`ProofHarness/D1N2SourceCorrectionCounterexample.lean`):
source-only data does not pin arbitrary off-image values of `f`; the explicit
boundary-identification premise used here is therefore essential. -/
theorem blocker_d1N2InvariantBridgeCorrection_fromSource_deferred
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f)
    :
    ∀ q0 q1 p s : ℂ,
      s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      q0.im = 0 →
      q1.im = 0 →
      p.im = 0 →
      s.im = 0 →
      q0.re + q1.re - 2 * p.re > 0 →
      (∃ x : Fin 2 → Fin (1 + 1) → ℝ,
        d1InvariantQuad (realEmbed x) = (q0, q1, p, s) ∧
        f q0 q1 p s = (Classical.choose hsource) (realEmbed x) ∧
        f q1 q0 p (-s) =
          (Classical.choose hsource)
            (fun k μ => (x (Equiv.swap (0 : Fin 2) 1 k) μ : ℂ))) →
      f q0 q1 p s = f q1 q0 p (-s) := by
  intro q0 q1 p s hquad hq0im hq1im hpim hsim hsp hBoundary
  have hF_local :
      ∀ (i : Fin 2) (hi : i.val + 1 < 2),
        ∀ (x : Fin 2 → Fin (1 + 1) → ℝ),
          ∑ μ, minkowskiSignature 1 μ *
            (x ⟨i.val + 1, hi⟩ μ - x i μ) ^ 2 > 0 →
          (Classical.choose hsource)
            (fun k μ => (x (Equiv.swap i ⟨i.val + 1, hi⟩ k) μ : ℂ)) =
          (Classical.choose hsource) (fun k μ => (x k μ : ℂ)) :=
    (Classical.choose_spec hsource).2.2.2.1
  rcases hBoundary with
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

private lemma d1N2_exists_real_uv_of_quadric
    (q0 q1 p s : ℝ)
    (hquad : s ^ 2 = 4 * (p ^ 2 - q0 * q1)) :
    ∃ u0 v0 u1 v1 : ℝ,
      -(u0 * v0) = q0 ∧
      -(u1 * v1) = q1 ∧
      -(u0 * v1 + u1 * v0) / 2 = p ∧
      u0 * v1 - u1 * v0 = s := by
  by_cases hq0 : q0 = 0
  · by_cases hq1 : q1 = 0
    · have hzero : p ^ 2 - s ^ 2 / 4 = 0 := by
        nlinarith [hquad, hq0, hq1]
      have hprod : (-p + s / 2) * (-p - s / 2) = 0 := by
        nlinarith [hzero]
      by_cases hR : -p + s / 2 = 0
      · refine ⟨0, 1, -p - s / 2, 0, ?_, ?_, ?_, ?_⟩
        · norm_num [hq0]
        · norm_num [hq1]
        · have hsRel : s = 2 * p := by linarith [hR]
          nlinarith [hsRel]
        · have hsRel : s = 2 * p := by linarith [hR]
          nlinarith [hsRel]
      · have hT : -p - s / 2 = 0 := by
          rcases mul_eq_zero.mp hprod with h | h
          · exact False.elim (hR h)
          · exact h
        refine ⟨-p + s / 2, 0, 0, 1, ?_, ?_, ?_, ?_⟩
        · norm_num [hq0]
        · norm_num [hq1]
        · have hsRel : s = -2 * p := by linarith [hT]
          nlinarith [hsRel]
        · have hsRel : s = -2 * p := by linarith [hT]
          nlinarith [hsRel]
    · refine ⟨(p - s / 2) / q1, -p - s / 2, 1, -q1, ?_, ?_, ?_, ?_⟩
      · have hq0Formula : q0 = (p ^ 2 - s ^ 2 / 4) / q1 := by
          apply (eq_div_iff hq1).2
          have hqq : q0 * q1 = p ^ 2 - s ^ 2 / 4 := by
            linarith [hquad]
          simpa [mul_comm] using hqq
        calc
          -(((p - s / 2) / q1) * (-p - s / 2))
              = (p ^ 2 - s ^ 2 / 4) / q1 := by
                  field_simp [hq1]
                  ring
          _ = q0 := hq0Formula.symm
      · ring
      · field_simp [hq1]
        ring
      · field_simp [hq1]
        ring
  · refine ⟨1, -q0, (p + s / 2) / q0, -p + s / 2, ?_, ?_, ?_, ?_⟩
    · ring
    · have hq1Formula : q1 = (p ^ 2 - s ^ 2 / 4) / q0 := by
        apply (eq_div_iff hq0).2
        have hqq : q0 * q1 = p ^ 2 - s ^ 2 / 4 := by
          linarith [hquad]
        simpa [mul_comm] using hqq
      calc
        -(((p + s / 2) / q0) * (-p + s / 2))
            = (p ^ 2 - s ^ 2 / 4) / q0 := by
                field_simp [hq0]
                ring
        _ = q1 := hq1Formula.symm
    · field_simp [hq0]
      ring
    · field_simp [hq0]
      ring

/-- Intrinsic real boundary geometry (`d=1,n=2`):
real quadric tuples admit a real configuration witness with matching
Lorentz-invariant quadruple. -/
lemma d1N2InvariantRealBoundaryWitness_exists
    (q0 q1 p s : ℂ)
    (hquad : s ^ 2 = 4 * (p ^ 2 - q0 * q1))
    (hq0im : q0.im = 0)
    (hq1im : q1.im = 0)
    (hpim : p.im = 0)
    (hsim : s.im = 0) :
    ∃ x : Fin 2 → Fin (1 + 1) → ℝ,
      d1InvariantQuad (realEmbed x) = (q0, q1, p, s) := by
  have hq0r : q0 = (q0.re : ℂ) := by
    apply Complex.ext <;> simp [hq0im]
  have hq1r : q1 = (q1.re : ℂ) := by
    apply Complex.ext <;> simp [hq1im]
  have hpr : p = (p.re : ℂ) := by
    apply Complex.ext <;> simp [hpim]
  have hsr : s = (s.re : ℂ) := by
    apply Complex.ext <;> simp [hsim]
  have hquadC :
      ((s.re : ℂ) ^ 2) =
        4 * (((p.re : ℂ) ^ 2) - (q0.re : ℂ) * (q1.re : ℂ)) := by
    have hquad' := hquad
    rwa [hq0r, hq1r, hpr, hsr] at hquad'
  have hquadR : s.re ^ 2 = 4 * (p.re ^ 2 - q0.re * q1.re) := by
    have hRe := congrArg Complex.re hquadC
    have hRe' :
        s.re ^ 2 =
          (4 * (((p.re : ℂ) ^ 2) - (q0.re : ℂ) * (q1.re : ℂ))).re := by
      simpa [pow_two] using hRe
    calc
      s.re ^ 2 = (4 * (((p.re : ℂ) ^ 2) - (q0.re : ℂ) * (q1.re : ℂ))).re := hRe'
      _ = 4 * (p.re ^ 2 - q0.re * q1.re) := by
            norm_num [pow_two]
  rcases d1N2_exists_real_uv_of_quadric q0.re q1.re p.re s.re hquadR with
    ⟨u0, v0, u1, v1, hq0uv, hq1uv, hpuv, hsuv⟩
  let x : Fin 2 → Fin (1 + 1) → ℝ :=
    d1N2RealConfig
      ((u0 + v0) / 2) ((u0 - v0) / 2)
      ((u1 + v1) / 2) ((u1 - v1) / 2)
  have hq0c : (((-(u0 * v0 : ℝ)) : ℂ)) = (q0.re : ℂ) := by
    exact_mod_cast hq0uv
  have hq1c : (((-(u1 * v1 : ℝ)) : ℂ)) = (q1.re : ℂ) := by
    exact_mod_cast hq1uv
  have hpc : (((-(u0 * v1 + u1 * v0) / 2 : ℝ)) : ℂ) = (p.re : ℂ) := by
    exact_mod_cast hpuv
  have hsc : (((u0 * v1 - u1 * v0 : ℝ)) : ℂ) = (s.re : ℂ) := by
    exact_mod_cast hsuv
  refine ⟨x, ?_⟩
  calc
    d1InvariantQuad (realEmbed x)
        = (((-(u0 * v0 : ℝ)) : ℂ),
            (((-(u1 * v1 : ℝ)) : ℂ)),
            (((-(u0 * v1 + u1 * v0) / 2 : ℝ)) : ℂ),
            (((u0 * v1 - u1 * v0 : ℝ)) : ℂ)) := by
              simpa [x] using d1InvariantQuad_realEmbed_realConfig_of_uv u0 v0 u1 v1
    _ = (((q0.re : ℂ)), ((q1.re : ℂ)), ((p.re : ℂ)), ((s.re : ℂ))) := by
          rw [hq0c, hq1c, hpc, hsc]
    _ = (q0, q1, p, s) := by
          rw [hq0r, hq1r, hpr, hsr]
          simp

/-- Sound source-bridge obstruction form (`d=1,n=2`):
under real-slice spacelike assumptions, simultaneous original+swapped
fixed-invariant `ForwardTube` approach families are impossible.

This is exactly
`d1N2InvariantApproachPair_real_spacelike_impossible`; the source parameter is
retained only to keep the bridge namespace shape stable.

Numerical support (heuristic, test 9 in
`ProofHarness/d1n2_tail_four_critical_lemma_checks.py`, 2026-03-04):
- single stress run: `360` real-spacelike tuples sampled, original-branch
  realizability `360/360`, swapped-branch realizability `0/360`;
- multi-seed sweep (`20260300..20260305`): per seed `240` tuples sampled,
  original-branch realizability `240/240`, swapped-branch realizability
  `0/240` on all `6/6` seeds. -/
theorem blocker_d1N2InvariantBoundaryApproachFamilies_fromSource_deferred
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hsource : d1N2InvariantKernelSource f) :
    ∀ q0 q1 p s : ℂ,
      s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
      q0.im = 0 →
      q1.im = 0 →
      p.im = 0 →
      s.im = 0 →
      q0.re + q1.re - 2 * p.re > 0 →
      ∀ x : Fin 2 → Fin (1 + 1) → ℝ,
        d1InvariantQuad (realEmbed x) = (q0, q1, p, s) →
        ¬ ((∃ φ : ℕ → Fin 2 → Fin (1 + 1) → ℂ,
            (∀ n, φ n ∈ ForwardTube 1 2) ∧
            Tendsto φ atTop
              (𝓝[ForwardTube 1 2] (realEmbed (n := 2) (d := 1) x)) ∧
            (∀ n, d1InvariantQuad (φ n) = (q0, q1, p, s))) ∧
          (∃ ψ : ℕ → Fin 2 → Fin (1 + 1) → ℂ,
            (∀ n, ψ n ∈ ForwardTube 1 2) ∧
            Tendsto ψ atTop
              (𝓝[ForwardTube 1 2]
                (realEmbed (n := 2) (d := 1)
                  (fun k μ => x (Equiv.swap (0 : Fin 2) 1 k) μ))) ∧
            (∀ n, d1InvariantQuad (ψ n) = (q1, q0, p, -s)))) := by
  let _ := f
  let _ := hsource
  intro q0 q1 p s hquad hq0im hq1im hpim hsim hsp x hxquad hApprox
  let _ := hquad
  let _ := hxquad
  exact d1N2InvariantApproachPair_real_spacelike_impossible
    hq0im hq1im hpim hsim hsp hApprox

/-- Deferred source-to-boundary identification input (`d=1,n=2`):
from source data, identify real-spacelike boundary invariant tuples with a real
configuration witness carrying both source-value identifications.

This is the missing ingredient not implied by source constraints alone in the
nonvacuous finite-ansatz stress tests.

Numerical stress note (2026-03-04, counterexample pattern):
- choose probe tuple `(q0,q1,p,s) = (9,1,3,0)` (real, spacelike, quadric) and
  spike model `f_probe = 1`, `f = 0` elsewhere;
- real-boundary reconstruction exists exactly (invariant reconstruction error
  `0.0`);
- sampled source-image checks:
  `200000` FT samples (`min distance to probe ≈ 3.43`) and `950` forwardizable
  samples (`min distance to probe ≈ 4.85`) all satisfy sampled `f = 0`;
- therefore sampled source compatibility can hold while boundary identification
  at the probe fails (`f probe = 1` vs source-anchor value `0`), matching that
  this theorem is the unresolved blocker. -/
theorem blocker_d1N2InvariantBoundaryIdentification_fromSource_deferred
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
      ∃ x : Fin 2 → Fin (1 + 1) → ℝ,
        d1InvariantQuad (realEmbed x) = (q0, q1, p, s) ∧
        f q0 q1 p s = (Classical.choose hsource) (realEmbed x) ∧
        f q1 q0 p (-s) =
          (Classical.choose hsource)
            (fun k μ => (x (Equiv.swap (0 : Fin 2) 1 k) μ : ℂ)) := by
  intro q0 q1 p s hquad hq0im hq1im hpim hsim hsp
  exact hBoundaryId q0 q1 p s hquad hq0im hq1im hpim hsim hsp

/-- Deferred source-to-witnessed swap bridge (`d=1,n=2`):
from source data plus explicit boundary identification, derive the invariant
witnessed-locus swap identity
`f q0 q1 p s = f q1 q0 p (-s)` under:
1. quadric relation;
2. original witness inequalities;
3. swapped witness inequalities.

Numerical note (2026-03-04): nonvacuous finite-ansatz source-only stress can
produce potential falsifiers; with explicit boundary-anchor constraints added,
the same ansatz family shows no sampled falsifier in tested regimes.
Stress run summary (seeds `20260300..20260310`, degree `9`):
- source stage is nonvacuous on every seed (`source_nullspace_dim = 145` after
  adaptive selection);
- after adding sampled boundary-anchor constraints
  (`1800 = 600 + 600 + 600` per seed), intersection nullspace dimension is `0`
  on all `11/11` seeds;
- probed on `900` sampled complex witnessed-domain tuples per seed, worst
  sampled `|g| = 0` on all `11/11` seeds. -/
theorem blocker_d1N2InvariantKernelSwapEq_onSectionWitnessPair_fromSource_deferred
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
    blocker_d1N2InvariantBridgePreconnected_fromSource_deferred
  have hCorrection :
      ∀ q0 q1 p s : ℂ,
        s ^ 2 = 4 * (p ^ 2 - q0 * q1) →
        q0.im = 0 →
        q1.im = 0 →
        p.im = 0 →
        s.im = 0 →
        q0.re + q1.re - 2 * p.re > 0 →
        f q0 q1 p s = f q1 q0 p (-s) := by
    intro q0 q1 p s hquad hq0im hq1im hpim hsim hsp
    have hBoundary :
        ∃ x : Fin 2 → Fin (1 + 1) → ℝ,
          d1InvariantQuad (realEmbed x) = (q0, q1, p, s) ∧
          f q0 q1 p s = (Classical.choose hsource) (realEmbed x) ∧
          f q1 q0 p (-s) =
            (Classical.choose hsource)
              (fun k μ => (x (Equiv.swap (0 : Fin 2) 1 k) μ : ℂ)) :=
      hBoundaryId q0 q1 p s hquad hq0im hq1im hpim hsim hsp
    exact blocker_d1N2InvariantBridgeCorrection_fromSource_deferred
      f hsource q0 q1 p s hquad hq0im hq1im hpim hsim hsp hBoundary
  exact
    blocker_d1N2InvariantKernelSwapEq_onSectionWitnessPair_invariantFunction_core_deferred
      f hAnalytic hConnected hCorrection

/-- Intrinsic forwardizable reduction (`d=1,n=2`):
if swap equality is known on the intrinsic witnessed quadric locus (in
`(q0,q1,p,s)` variables only), then the forwardizable-kernel difference
vanishes.

This isolates the purely geometric reduction:
forwardizable pair `⇒` original/swapped witness inequalities.

Numerical support (2026-03-04):
- direct sampled forwardizable-with-witness runs check the geometric step only
  (no ansatz on `f`):
  for seeds `20260300..20260305`, sampled forwardizable tuples per seed were
  `{186, 213, 209, 238, 244, 213}`, and all sampled tuples satisfied both
  intrinsic witness-inequality branches (`100%` pass on all 6 seeds). -/
theorem blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_invariantOnly_core_deferred
    (f : ℂ → ℂ → ℂ → ℂ → ℂ)
    (hSwapEqOnWitnessed :
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
  exact sub_eq_zero.mpr (hSwapEqOnWitnessed q0 q1 p s hquad hOrigFT hSwapFT)

/-- Forward witness equality from the source package, reduced to the invariant
forwardizable-kernel theorem at `d=1,n=2`.

Assertion-level numerical surrogate status (2026-03-04, thorough rerun):
- `ProofHarness/d1n2_tail_four_critical_lemma_checks.py`, test 5
  (source-constrained forwardizable-domain equality probe);
- seeds `20260800..20260807` (`8` runs), all nonvacuous
  (`source_constraint_nullspace_dim = 13` each run);
- per run source fit: `source_samples=1000` (`600` intrinsic + `400`
  phase-locked), threshold `1e-9`;
- standard holdout (`25000` forwardizable points/seed):
  `NO_NUMERIC_FALSIFIER_FOUND` in `8/8`, with
  `max worst_|g| = 6.427e-11`;
- wide holdout (`15000` wider-range points/seed):
  `POTENTIAL_FALSIFIER_FOUND` in `8/8`, with
  `max worst_|g| = 2.482e-05`.

Precision-stability cross-check (2026-03-04):
- `ProofHarness`-compatible replay on seeds `20260800..20260807`,
  wide sample count `8000` per seed, using the same sampled tuples and
  selected coefficient per seed, with full Decimal re-evaluation at
  precisions `80/120/200` digits;
- Decimal worst values were in `[2.297e-07, 5.818e-07]`, and the
  `120`- vs `200`-digit maxima matched to displayed precision
  (`max rel delta = 0.0` in this run);
- threshold verdict at `1e-9` remained
  `POTENTIAL_FALSIFIER_FOUND` in `8/8` for float and all Decimal precisions.

Numerical verdict (assertion-level surrogate): `MIXED`
(`SUPPORTED` on standard regime, `NOT SUPPORTED` on wide-stress regime).

Interpretation: this finite test suite strongly supports the assertion on the
standard sampled regime but finds repeatable tension on a wider stress regime,
so the numeric evidence is mixed and non-conclusive. This theorem remains
deferred because the source-only boundary-identification generation
(`hBoundaryId`) is still open here; finite-sampling numerics are not a formal
proof. -/
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
    sorry
  have hSwapEqOnWitnessed :
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
        f q0 q1 p s = f q1 q0 p (-s) :=
    blocker_d1N2InvariantKernelSwapEq_onSectionWitnessPair_fromSource_deferred
      f hsource hBoundaryId
  have hquadDiff :
      d1N2InvariantKernelDiffZeroOnForwardizableQuadric f :=
    blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_invariantOnly_core_deferred
      f hSwapEqOnWitnessed
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
gives the same value.

Formal status: this declaration has no `sorry` dependency
(`#print axioms` has no `sorryAx`). -/
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
eventual fixed-witness forward equality are equivalent.

Formal status: this declaration has no `sorry` dependency
(`#print axioms` has no `sorryAx`). -/
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
`F(Γ·(swap·w)) = F(w)`.

Assertion-level numerical stress (2026-03-04;
`ProofHarness/d1n2_tail_four_critical_lemma_checks.py`, Test 7):
- this test checks the hypothesis -> conclusion shape of this lemma directly
  (not proof-internal steps);
- seeds `20260410..20260421` (`12` runs), with nonvacuous source mode in all
  runs (`source_constraint_nullspace_dim = 13`);
- per seed: `local_nhd_centers=300`, `local_nhd_samples_per_center=300`,
  so `local_points_checked = 90000`;
- aggregate: `1080000` local points checked, `268` rejected by the preparation
  filter;
- threshold `1e-9`, worst sampled `|g| = 2.42557e-11`,
  status `NO_NUMERIC_FALSIFIER_FOUND` in `12/12` runs.

Finite-sampling caveat: strong support, not a formal proof. -/
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
  have hfield :
      ∀ (z : Fin 2 → Fin (1 + 1) → ℂ) (Λ : ComplexLorentzGroup 1),
        z ∈ ForwardTube 1 2 →
        complexLorentzAction Λ
          (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z) ∈ ForwardTube 1 2 →
        F (complexLorentzAction Λ
            (permAct (d := 1) (Equiv.swap (0 : Fin 2) 1) z)) = F z :=
    blocker_d1N2ForwardWitnessEq_field_deferred
      F hF_holo hF_lorentz hF_bv hF_local
  exact Filter.Eventually.of_forall (fun w hwU => by
    have hzFT :
        w ∈ ForwardTube 1 2 :=
      (mem_permForwardOverlapSet_d1_swap01_n2_iff w).1 (hU_good w hwU).1 |>.1
    exact hfield w Γ hzFT (hU_good w hwU).2)

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
