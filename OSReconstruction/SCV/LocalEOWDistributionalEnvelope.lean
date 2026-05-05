/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.SCV.LocalEOWChartAssembly

/-!
# Local Distributional EOW Envelope

This file starts the final one-chart distributional EOW assembly.  The checked
support layers live in the local EOW chart files; this file keeps the remaining
outer choices small and explicit before calling the fixed-window scale theorem.
-/

noncomputable section

open Complex MeasureTheory Set Filter

namespace SCV

variable {m : ℕ}

/-- Choose inner fixed-window radii for the one-chart distributional assembly.

The fixed continuous-EOW window supplies an original real radius `ρ0`, a
polywedge coordinate-sum radius `r0`, and the side-cone truncation supplies
`δside`.  This lemma chooses smaller radii `ρ`, `r`, and a Rudin radius `δ`
with exactly the inequalities consumed by
`regularizedLocalEOW_chartEnvelope_from_fixedWindowScale`. -/
theorem exists_localEOW_fixedWindow_innerScale
    {ρ0 r0 δside : ℝ}
    (hρ0 : 0 < ρ0) (hr0 : 0 < r0) (hδside : 0 < δside) :
    ∃ ρ r δ : ℝ,
      0 < ρ ∧
      0 < r ∧
      0 < δ ∧
      δ * 10 ≤ ρ ∧
      (Fintype.card (Fin m) : ℝ) * (δ * 10) < r ∧
      4 * ρ ≤ ρ0 ∧
      r ≤ r0 ∧
      r ≤ δside := by
  let c : ℝ := Fintype.card (Fin m)
  let ρ : ℝ := ρ0 / 4
  let r : ℝ := min (r0 / 2) δside
  let δ : ℝ := min (ρ / 20) (r / (20 * (c + 1)))
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hc1_pos : 0 < c + 1 := by
    positivity
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hr_pos : 0 < r := by
    dsimp [r]
    exact lt_min (by positivity) hδside
  have hden_pos : 0 < 20 * (c + 1) := by
    positivity
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min (by positivity) (by positivity)
  refine ⟨ρ, r, δ, hρ_pos, hr_pos, hδ_pos, ?_, ?_, ?_, ?_, ?_⟩
  · have hδ_le : δ ≤ ρ / 20 := by
      dsimp [δ]
      exact min_le_left _ _
    nlinarith [hδ_le, hρ_pos]
  · have hδ_le : δ ≤ r / (20 * (c + 1)) := by
      dsimp [δ]
      exact min_le_right _ _
    have hδ_mul_le : δ * (20 * (c + 1)) ≤ r :=
      (le_div_iff₀ hden_pos).1 hδ_le
    have hcoeff_lt : c * 10 < 20 * (c + 1) := by
      nlinarith [hc_nonneg]
    have hleft_lt :
        c * (δ * 10) < δ * (20 * (c + 1)) := by
      nlinarith [hcoeff_lt, hδ_pos]
    exact lt_of_lt_of_le hleft_lt hδ_mul_le
  · dsimp [ρ]
    nlinarith
  · dsimp [r]
    have hr_le_half : min (r0 / 2) δside ≤ r0 / 2 := min_le_left _ _
    nlinarith [hr_le_half, hr0]
  · dsimp [r]
    exact min_le_right _ _

/-- Choose the polywedge and Rudin radii after the real chart radius has
already been fixed. -/
theorem exists_localEOW_fixedWindow_polyRudinScale
    {ρ r0 δside : ℝ}
    (hρ : 0 < ρ) (hr0 : 0 < r0) (hδside : 0 < δside) :
    ∃ r δ : ℝ,
      0 < r ∧
      0 < δ ∧
      δ * 10 ≤ ρ ∧
      (Fintype.card (Fin m) : ℝ) * (δ * 10) < r ∧
      r ≤ r0 ∧
      r ≤ δside := by
  let c : ℝ := Fintype.card (Fin m)
  let r : ℝ := min (r0 / 2) δside
  let δ : ℝ := min (ρ / 20) (r / (20 * (c + 1)))
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hc1_pos : 0 < c + 1 := by
    positivity
  have hr_pos : 0 < r := by
    dsimp [r]
    exact lt_min (by positivity) hδside
  have hden_pos : 0 < 20 * (c + 1) := by
    positivity
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min (by positivity) (by positivity)
  refine ⟨r, δ, hr_pos, hδ_pos, ?_, ?_, ?_, ?_⟩
  · have hδ_le : δ ≤ ρ / 20 := by
      dsimp [δ]
      exact min_le_left _ _
    nlinarith [hδ_le, hρ]
  · have hδ_le : δ ≤ r / (20 * (c + 1)) := by
      dsimp [δ]
      exact min_le_right _ _
    have hδ_mul_le : δ * (20 * (c + 1)) ≤ r :=
      (le_div_iff₀ hden_pos).1 hδ_le
    have hcoeff_lt : c * 10 < 20 * (c + 1) := by
      nlinarith [hc_nonneg]
    have hleft_lt :
        c * (δ * 10) < δ * (20 * (c + 1)) := by
      nlinarith [hcoeff_lt, hδ_pos]
    exact lt_of_lt_of_le hleft_lt hδ_mul_le
  · dsimp [r]
    have hr_le_half : min (r0 / 2) δside ≤ r0 / 2 := min_le_left _ _
    nlinarith [hr_le_half, hr0]
  · dsimp [r]
    exact min_le_right _ _

set_option maxHeartbeats 800000

/-- One fixed-basis local distributional edge-of-the-wedge envelope.

This is the outer one-chart assembly: it constructs the fixed window, the
truncated side domains, the affine real cutoff, the cutoff-support slice CLMs,
the recovery scale and cutoffs, and then calls
`regularizedLocalEOW_chartEnvelope_from_fixedWindowScale`. -/
theorem chartDistributionalEOW_local_envelope
    (hm : 0 < m)
    (Ωplus Ωminus : Set (ComplexChartSpace m))
    (E C : Set (Fin m → ℝ))
    (hΩplus_open : IsOpen Ωplus)
    (hΩminus_open : IsOpen Ωminus)
    (hE_open : IsOpen E)
    (hC_open : IsOpen C)
    (hC_conv : Convex ℝ C)
    (_hC_ne : C.Nonempty)
    (hC_cone : ∀ t : ℝ, 0 < t → ∀ y ∈ C, t • y ∈ C)
    (hlocal_wedge :
      ∀ K : Set (Fin m → ℝ), IsCompact K → K ⊆ E →
        ∀ Kη : Set (Fin m → ℝ), IsCompact Kη → Kη ⊆ C →
          ∃ r : ℝ, 0 < r ∧
            ∀ x ∈ K, ∀ η ∈ Kη, ∀ ε : ℝ, 0 < ε → ε < r →
              (fun a => (x a : ℂ) +
                (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωplus ∧
              (fun a => (x a : ℂ) -
                (ε : ℂ) * (η a : ℂ) * Complex.I) ∈ Ωminus)
    (ys : Fin m → Fin m → ℝ)
    (hys_mem : ∀ j, ys j ∈ C)
    (hli : LinearIndependent ℝ ys)
    (x0 : Fin m → ℝ) (hx0 : x0 ∈ E)
    (Fplus Fminus : ComplexChartSpace m → ℂ)
    (hFplus : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus : DifferentiableOn ℂ Fminus Ωminus)
    (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ)
    (hplus_bv :
      ∀ Kη : Set (Fin m → ℝ), IsCompact Kη → Kη ⊆ C →
        ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
          HasCompactSupport (φ : (Fin m → ℝ) → ℂ) →
          tsupport (φ : (Fin m → ℝ) → ℂ) ⊆ E →
          TendstoUniformlyOn
            (fun (ε : ℝ) η =>
              ∫ x : Fin m → ℝ,
                Fplus (fun a => (x a : ℂ) +
                  (ε : ℂ) * (η a : ℂ) * Complex.I) * φ x)
            (fun _ : Fin m → ℝ => T φ)
            (nhdsWithin 0 (Set.Ioi 0))
            Kη)
    (hminus_bv :
      ∀ Kη : Set (Fin m → ℝ), IsCompact Kη → Kη ⊆ C →
        ∀ φ : SchwartzMap (Fin m → ℝ) ℂ,
          HasCompactSupport (φ : (Fin m → ℝ) → ℂ) →
          tsupport (φ : (Fin m → ℝ) → ℂ) ⊆ E →
          TendstoUniformlyOn
            (fun (ε : ℝ) η =>
              ∫ x : Fin m → ℝ,
                Fminus (fun a => (x a : ℂ) -
                  (ε : ℂ) * (η a : ℂ) * Complex.I) * φ x)
            (fun _ : Fin m → ℝ => T φ)
            (nhdsWithin 0 (Set.Ioi 0))
            Kη) :
    ∃ (ρ r δ R : ℝ) (Hcoord : ComplexChartSpace m → ℂ),
      0 < ρ ∧ 0 < r ∧ 0 < δ ∧ 0 < R ∧ R ≤ δ / 2 ∧
      (∀ u ∈ Metric.closedBall (0 : Fin m → ℝ) ρ,
        localEOWRealChart x0 ys u ∈ E) ∧
      StrictPositiveImagBall (m := m) R ⊆
        Metric.ball (0 : ComplexChartSpace m) R ∧
      StrictNegativeImagBall (m := m) R ⊆
        Metric.ball (0 : ComplexChartSpace m) R ∧
      (∀ w ∈ StrictPositiveImagBall (m := m) R,
        localEOWChart x0 ys w ∈ Ωplus) ∧
      (∀ w ∈ StrictNegativeImagBall (m := m) R,
        localEOWChart x0 ys w ∈ Ωminus) ∧
      DifferentiableOn ℂ Hcoord (Metric.ball (0 : ComplexChartSpace m) R) ∧
      (∀ w ∈ StrictPositiveImagBall (m := m) R,
        Hcoord w = Fplus (localEOWChart x0 ys w)) ∧
      (∀ w ∈ StrictNegativeImagBall (m := m) R,
        Hcoord w = Fminus (localEOWChart x0 ys w)) := by
  classical
  let D := Fin m → ℝ
  let X := ComplexChartSpace m
  obtain ⟨ρ0, hρ0, r0, hr0, δ0, hδ0, hδ0ρ, hδ0sum,
      hE0, hplus0, hminus0, _hupper0, _hlower0⟩ :=
    exists_localContinuousEOW_fixedBasis_chart_window
      (m := m) hm Ωplus Ωminus E C hE_open hC_conv hlocal_wedge
      x0 hx0 ys hys_mem
  let ρin : ℝ := ρ0 / 4
  have hρin : 0 < ρin := by
    dsimp [ρin]
    positivity
  have hρin4 : 4 * ρin ≤ ρ0 := by
    dsimp [ρin]
    nlinarith
  have hρin_le_ρ0 : ρin ≤ ρ0 := by nlinarith [hρin, hρin4]
  have hE_mem :
      ∀ u ∈ Metric.closedBall (0 : D) ρin,
        localEOWRealChart x0 ys u ∈ E := by
    intro u hu
    exact hE0 u (by
      rw [Metric.mem_closedBall, dist_zero_right] at hu ⊢
      exact le_trans hu hρin_le_ρ0)
  have hplus_bv_real :
      ∀ Kη : Set D, IsCompact Kη → Kη ⊆ C →
        ∀ φ : SchwartzMap D ℂ,
          HasCompactSupport (φ : D → ℂ) →
          tsupport (φ : D → ℂ) ⊆ E →
          TendstoUniformlyOn
            (fun (ε : ℝ) η =>
              ∫ x : D,
                Fplus (fun a => (x a : ℂ) +
                  (ε : ℂ) * (η a : ℂ) * Complex.I) * φ x)
            (fun _ : D => (T.restrictScalars ℝ) φ)
            (nhdsWithin 0 (Set.Ioi 0))
            Kη := by
    intro Kη hKη hKηC φ hφ hφE
    simpa using hplus_bv Kη hKη hKηC φ hφ hφE
  have hminus_bv_real :
      ∀ Kη : Set D, IsCompact Kη → Kη ⊆ C →
        ∀ φ : SchwartzMap D ℂ,
          HasCompactSupport (φ : D → ℂ) →
          tsupport (φ : D → ℂ) ⊆ E →
          TendstoUniformlyOn
            (fun (ε : ℝ) η =>
              ∫ x : D,
                Fminus (fun a => (x a : ℂ) -
                  (ε : ℂ) * (η a : ℂ) * Complex.I) * φ x)
            (fun _ : D => (T.restrictScalars ℝ) φ)
            (nhdsWithin 0 (Set.Ioi 0))
            Kη := by
    intro Kη hKη hKηC φ hφ hφE
    simpa using hminus_bv Kη hKη hKηC φ hφ hφE
  obtain ⟨ε, CplusRaw, CminusRaw, hε, hCplusRaw_eq, hCminusRaw_eq,
      hclosure, _hCplusRaw_open, _hCminusRaw_open, _hsimplex,
      _hCplusRaw_C, _himag_mem, hplus_raw, hminus_raw⟩ :=
    localEOW_basisSideCone_rawBoundaryValue
      (m := m) E C hC_open hC_conv hC_cone ys hys_mem hli
      Fplus Fminus (T.restrictScalars ℝ) hplus_bv_real hminus_bv_real
  subst CplusRaw
  subst CminusRaw
  obtain ⟨χcoord, hχcoord_one, hχcoord_support⟩ :=
    exists_schwartz_cutoff_eq_one_on_closedBall (m := m)
      (r := 3 * ρin) (rLarge := 4 * ρin)
      (by nlinarith [hρin]) (by nlinarith [hρin])
  let χ : SchwartzMap D ℂ :=
    localEOWAffineTestPushforwardCLM x0 ys hli χcoord
  have hχcoord_compact : HasCompactSupport (χcoord : D → ℂ) := by
    rw [HasCompactSupport]
    exact (isCompact_closedBall (x := (0 : D)) (r := 4 * ρin)).of_isClosed_subset
      (isClosed_tsupport _) hχcoord_support
  have hχ_compact : HasCompactSupport (χ : D → ℂ) := by
    dsimp [χ]
    exact HasCompactSupport.localEOWAffineTestPushforwardCLM x0 ys hli
      hχcoord_compact
  have hχ_E : tsupport (χ : D → ℂ) ⊆ E := by
    intro x hx
    rcases tsupport_localEOWAffineTestPushforwardCLM_subset
        x0 ys hli χcoord hx with ⟨u, hu, rfl⟩
    exact hE0 u (by
      have hu4 := hχcoord_support hu
      rw [Metric.mem_closedBall, dist_zero_right] at hu4 ⊢
      exact le_trans hu4 hρin4)
  obtain ⟨rside, CplusLocRaw, CminusLocRaw, hrside, hCplusLoc_eq,
      hCminusLoc_eq, _hCplusLoc_open0, _hCminusLoc_open0,
      hCplusLoc_sub_raw, hCminusLoc_sub_raw, hplus_margin_loc,
      hminus_margin_loc⟩ :=
    exists_localEOW_truncatedSideCones_for_sliceMargin
      (m := m) E C Ωplus Ωminus hlocal_wedge ys hε hclosure
      χ hχ_compact hχ_E
  subst CplusLocRaw
  subst CminusLocRaw
  obtain ⟨δside, hδside, hδside_map⟩ :=
    exists_localEOWRealLinearPart_ball_subset ys hrside
  let ρ : ℝ := ρin
  have hρ : 0 < ρ := by simpa [ρ] using hρin
  have hρ4 : 4 * ρ ≤ ρ0 := by simpa [ρ] using hρin4
  obtain ⟨r, δ', hr, hδ', hδ'ρ, hδ'sum, hr_r0, hr_δside⟩ :=
    exists_localEOW_fixedWindow_polyRudinScale (m := m) hρ hr0 hδside
  have hρ_le_ρ0 : ρ ≤ ρ0 := by nlinarith [hρ, hρ4]
  have hE_memρ :
      ∀ u ∈ Metric.closedBall (0 : D) ρ,
        localEOWRealChart x0 ys u ∈ E := by
    intro u hu
    exact hE0 u (by
      rw [Metric.mem_closedBall, dist_zero_right] at hu ⊢
      exact le_trans hu hρ_le_ρ0)
  have hplusρ :
      ∀ u ∈ Metric.closedBall (0 : D) ρ, ∀ v : D,
        (∀ j, 0 ≤ v j) →
        0 < ∑ j, v j →
        (∑ j, v j) < r →
          localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωplus := by
    intro u hu v hv_nonneg hv_sum_pos hv_sum_lt
    exact hplus0 u (by
      rw [Metric.mem_closedBall, dist_zero_right] at hu ⊢
      exact le_trans hu hρ_le_ρ0) v hv_nonneg hv_sum_pos
      (lt_of_lt_of_le hv_sum_lt hr_r0)
  have hminusρ :
      ∀ u ∈ Metric.closedBall (0 : D) ρ, ∀ v : D,
        (∀ j, v j ≤ 0) →
        0 < ∑ j, -v j →
        (∑ j, -v j) < r →
          localEOWChart x0 ys
            (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Ωminus := by
    intro u hu v hv_nonpos hv_sum_pos hv_sum_lt
    exact hminus0 u (by
      rw [Metric.mem_closedBall, dist_zero_right] at hu ⊢
      exact le_trans hu hρ_le_ρ0) v hv_nonpos hv_sum_pos
      (lt_of_lt_of_le hv_sum_lt hr_r0)
  let CplusLoc : Set D := localEOWSideCone ys ε ∩ Metric.ball 0 rside
  let CminusLoc : Set D := Neg.neg '' CplusLoc
  let Dplus : Set X :=
    Ωplus ∩ TubeDomain CplusLoc ∩
      localEOWAffineRealWindow x0 ys hli (2 * ρ)
  let Dminus : Set X :=
    Ωminus ∩ TubeDomain CminusLoc ∩
      localEOWAffineRealWindow x0 ys hli (2 * ρ)
  have hprepared :=
    localEOWPreparedSideDomains_from_fixedWindow
      (m := m) (ρ := ρ) (rpoly := r) (ε := ε) (rside := rside)
      (δside := δside) hρ hε Ωplus Ωminus hΩplus_open hΩminus_open
      x0 ys hli hr_δside hδside_map hplusρ hminusρ
  dsimp [CplusLoc, CminusLoc, Dplus, Dminus] at hprepared
  rcases hprepared with
    ⟨hDplus_open, hDminus_open, hDplus_Ω, hDminus_Ω,
      hDplus_tube, hDminus_tube, hDplus_window, hDminus_window,
      hplusD, hminusD⟩
  obtain ⟨δsymm, hδsymm, hsymm⟩ :=
    exists_localEOWRealLinearSymm_ball_subset ys hli hρ
  let rψOne : ℝ := δsymm / 4
  let rψLarge : ℝ := δsymm / 2
  have hrψOne : 0 < rψOne := by
    dsimp [rψOne]
    positivity
  have hrψLarge : 0 < rψLarge := by
    dsimp [rψLarge]
    positivity
  have hrψ_one_large_lt : rψOne < rψLarge := by
    dsimp [rψOne, rψLarge]
    nlinarith [hδsymm]
  have hrψ_one_large : rψOne ≤ rψLarge := le_of_lt hrψ_one_large_lt
  have hsmall :
      ∀ t : D, ‖t‖ ≤ rψLarge →
        ‖(localEOWRealLinearCLE ys hli).symm t‖ < ρ := by
    intro t ht
    exact hsymm t (by
      dsimp [rψLarge] at ht
      nlinarith [ht, hδsymm])
  have hplus_bv_loc :
      ∀ φ : SchwartzMap D ℂ,
        HasCompactSupport (φ : D → ℂ) →
        tsupport (φ : D → ℂ) ⊆ E →
          Tendsto (fun y =>
            ∫ x : D,
              Fplus (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) *
                Complex.I) * φ x)
            (nhdsWithin 0 CplusLoc) (nhds ((T.restrictScalars ℝ) φ)) := by
    intro φ hφ_compact hφ_E
    exact (hplus_raw φ hφ_compact hφ_E).mono_left
      (nhdsWithin_mono _ (by
        intro y hy
        exact hCplusLoc_sub_raw (by simpa [CplusLoc] using hy)))
  have hminus_bv_loc :
      ∀ φ : SchwartzMap D ℂ,
        HasCompactSupport (φ : D → ℂ) →
        tsupport (φ : D → ℂ) ⊆ E →
          Tendsto (fun y =>
            ∫ x : D,
              Fminus (fun i => (x i : ℂ) + ((y i : ℝ) : ℂ) *
                Complex.I) * φ x)
            (nhdsWithin 0 CminusLoc) (nhds ((T.restrictScalars ℝ) φ)) := by
    intro φ hφ_compact hφ_E
    exact (hminus_raw φ hφ_compact hφ_E).mono_left
      (nhdsWithin_mono _ (by
        intro y hy
        dsimp [CminusLoc, CplusLoc] at hy
        rcases hy with ⟨yp, hyp, hy_eq⟩
        exact ⟨yp, hCplusLoc_sub_raw hyp, hy_eq⟩))
  have hplus_margin_closed :
      ∀ z ∈ Dplus, ∀ t ∈ Metric.closedBall (0 : D) rψLarge,
        z + realEmbed t ∈ Ωplus := by
    intro z hz t ht
    have hy : (fun i => (z i).im) ∈ CplusLoc := by
      simpa [CplusLoc, TubeDomain] using hDplus_tube hz
    have ht_norm : ‖t‖ ≤ rψLarge := by
      simpa [Metric.mem_closedBall, dist_zero_right] using ht
    have hone :
        χ (fun j => (z j).re + t j) = 1 := by
      dsimp [χ]
      exact localEOWAffineCutoff_one_of_affineRealWindow_add
        x0 ys hli χcoord (by simpa [ρ] using hχcoord_one)
        (hDplus_window hz)
        (hsmall t ht_norm)
    have hx : (fun j => (z j).re + t j) ∈ tsupport (χ : D → ℂ) := by
      exact subset_tsupport _ (by
        simp [Function.mem_support, hone])
    have hΩ := hplus_margin_loc (fun i => (z i).im) (by
        simpa [CplusLoc] using hy) (fun j => (z j).re + t j) hx
    have hz_eq :
        z + realEmbed t =
          (fun i => ((fun j => (z j).re + t j) i : ℂ) +
            (((fun i => (z i).im) i : ℝ) : ℂ) * Complex.I) := by
      let z0 : ComplexChartSpace m := z
      let t0 : Fin m → ℝ := t
      change z0 + realEmbed t0 =
        (fun i => ((fun j => (z0 j).re + t0 j) i : ℂ) +
          (((fun i => (z0 i).im) i : ℝ) : ℂ) * Complex.I)
      ext i
      apply Complex.ext <;> simp [realEmbed, Pi.add_apply]
    rw [hz_eq]
    exact hΩ
  have hminus_margin_closed :
      ∀ z ∈ Dminus, ∀ t ∈ Metric.closedBall (0 : D) rψLarge,
        z + realEmbed t ∈ Ωminus := by
    intro z hz t ht
    have hy_raw :
        (-fun i => (z i).im) ∈ localEOWSideCone ys ε ∧
          ‖fun i => (z i).im‖ < rside := by
      simpa [CminusLoc, CplusLoc, TubeDomain] using hDminus_tube hz
    have hy_img :
        (fun i => (z i).im) ∈
          Neg.neg '' (localEOWSideCone ys ε ∩ Metric.ball 0 rside) := by
      refine ⟨-(fun i => (z i).im), ?_, ?_⟩
      · refine ⟨hy_raw.1, ?_⟩
        rw [Metric.mem_ball, dist_zero_right]
        simpa [norm_neg] using hy_raw.2
      · ext i
        simp
    have ht_norm : ‖t‖ ≤ rψLarge := by
      simpa [Metric.mem_closedBall, dist_zero_right] using ht
    have hone :
        χ (fun j => (z j).re + t j) = 1 := by
      dsimp [χ]
      exact localEOWAffineCutoff_one_of_affineRealWindow_add
        x0 ys hli χcoord (by simpa [ρ] using hχcoord_one)
        (hDminus_window hz)
        (hsmall t ht_norm)
    have hx : (fun j => (z j).re + t j) ∈ tsupport (χ : D → ℂ) := by
      exact subset_tsupport _ (by
        simp [Function.mem_support, hone])
    have hΩ := hminus_margin_loc (fun i => (z i).im) hy_img
      (fun j => (z j).re + t j) hx
    have hz_eq :
        z + realEmbed t =
          (fun i => ((fun j => (z j).re + t j) i : ℂ) +
            (((fun i => (z i).im) i : ℝ) : ℂ) * Complex.I) := by
      let z0 : ComplexChartSpace m := z
      let t0 : Fin m → ℝ := t
      change z0 + realEmbed t0 =
        (fun i => ((fun j => (z0 j).re + t0 j) i : ℂ) +
          (((fun i => (z0 i).im) i : ℝ) : ℂ) * Complex.I)
      ext i
      apply Complex.ext <;> simp [realEmbed, Pi.add_apply]
    rw [hz_eq]
    exact hΩ
  let TcutOrig : SchwartzMap D ℂ →L[ℂ] ℂ :=
    T.comp (SchwartzMap.smulLeftCLM ℂ (χ : D → ℂ))
  obtain ⟨Tplus, Tminus, hplus_eval, hminus_eval,
      hplus_limit, hminus_limit⟩ :=
    localEOWSliceCLMs_from_preparedDomains
      (m := m) (Cplus := CplusLoc) (Cminus := CminusLoc) (E := E)
      (rψ := rψLarge) (ρ := ρ) Ωplus Ωminus Dplus Dminus
      Fplus Fminus T x0 ys hli χcoord hΩplus_open hΩminus_open
      hFplus hFminus hχcoord_compact (by
        simpa [χ] using hχ_E) (by
        simpa [ρ] using hχcoord_one)
      (by
        intro y hy x hx
        exact hplus_margin_loc y (by simpa [CplusLoc] using hy) x
          (by simpa [χ] using hx))
      (by
        intro y hy x hx
        have hy' :
            y ∈ Neg.neg '' (localEOWSideCone ys ε ∩ Metric.ball 0 rside) := by
          dsimp [CminusLoc, CplusLoc] at hy
          exact hy
        exact hminus_margin_loc y hy' x (by simpa [χ] using hx))
      hDplus_tube hDminus_tube hDplus_window hDminus_window
      hsmall hplus_bv_loc hminus_bv_loc
  obtain ⟨σ, hσ, hδscale, hσδside, hσρ, hcardσ, hA4_raw⟩ :=
    exists_oneChartRecoveryScale (m := m) (δ := δ') (δside := δside)
      (ρin := ρ) (rpoly := r) (rψOrig := rψOne)
      (M := 2 * ‖(localEOWRealLinearCLE ys hli).toContinuousLinearMap‖)
      hδ' hδside hρ hr hrψOne (by positivity)
  have hA4_one :
      ‖(localEOWRealLinearCLE ys hli).toContinuousLinearMap‖ *
          (4 * σ) ≤ rψOne := by
    nlinarith [hA4_raw]
  obtain ⟨χU, hχU_one, _hχU_support⟩ :=
    exists_complexChart_schwartz_cutoff_eq_one_on_closedBall (m := m)
      (R := 8 * σ) (Rlarge := 16 * σ)
      (by nlinarith [hσ]) (by nlinarith [hσ])
  obtain ⟨χr, hχr_one, hχr_support⟩ :=
    exists_schwartz_cutoff_eq_one_on_closedBall (m := m)
      (r := 2 * σ) (rLarge := 4 * σ)
      (by nlinarith [hσ]) (by nlinarith [hσ])
  obtain ⟨χψ, hχψ_one, hχψ_support⟩ :=
    exists_schwartz_cutoff_eq_one_on_closedBall (m := m)
      (r := rψOne) (rLarge := rψLarge) hrψOne hrψ_one_large_lt
  let Kreal : Set D :=
    localEOWRealChart x0 ys '' Metric.closedBall (0 : D) ρ
  have hKreal_compact : IsCompact Kreal := by
    dsimp [Kreal]
    exact (isCompact_closedBall (x := (0 : D)) (r := ρ)).image
      (continuous_localEOWRealChart x0 ys)
  have hKreal_mem :
      ∀ u ∈ Metric.closedBall (0 : D) ρ,
        localEOWRealChart x0 ys u ∈ Kreal := by
    intro u hu
    exact ⟨u, hu, rfl⟩
  obtain ⟨K, H, hH_holo_big, Hdist, _hHdist_rep, _hK_rep,
      hH_plus, hH_minus⟩ :=
    regularizedLocalEOW_chartEnvelope_from_fixedWindowScale
      (m := m) (Cplus := CplusLoc) (Cminus := CminusLoc)
      (rψLarge := rψLarge) (rψOne := rψOne)
      (ρ := ρ) (r := r) (δ := δ') (σ := σ)
      hm hδ' hσ hδscale (le_of_lt hσρ) hcardσ
      Ωplus Ωminus Dplus Dminus E Kreal hΩplus_open hΩminus_open
      hDplus_open hDminus_open hE_open hDplus_Ω hDminus_Ω
      Fplus Fminus hFplus hFminus hplus_margin_closed
      hminus_margin_closed hDplus_tube hDminus_tube Tplus Tminus TcutOrig
      hplus_eval hminus_eval (by
        simpa [TcutOrig, χ] using hplus_limit) (by
        simpa [TcutOrig, χ] using hminus_limit)
      x0 ys hli hδ'ρ hδ'sum hE_memρ hKreal_compact hKreal_mem
      hplusD hminusD χU χr χψ hχU_one hχr_one hχr_support
      hχψ_one hχψ_support hA4_one hrψ_one_large
  refine ⟨ρ, r, δ', σ, H, hρ, hr, hδ', hσ, ?_, hE_memρ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith [hδscale, hδ']
  · intro w hw
    exact hw.1
  · intro w hw
    exact hw.1
  · intro w hw
    have hσρ_le : σ ≤ ρ := by nlinarith [hσρ, hσ]
    have hc_nonneg : 0 ≤ (Fintype.card (Fin m) : ℝ) := by positivity
    have hcardσ_small : (Fintype.card (Fin m) : ℝ) * σ < r := by
      nlinarith [hcardσ, hσ, hc_nonneg]
    exact localEOWChart_mem_fixedWindow_of_strictPositiveImagBall
      (m := m) hm Ωplus x0 ys hσρ_le hcardσ_small hplusρ hw
  · intro w hw
    have hσρ_le : σ ≤ ρ := by nlinarith [hσρ, hσ]
    have hc_nonneg : 0 ≤ (Fintype.card (Fin m) : ℝ) := by positivity
    have hcardσ_small : (Fintype.card (Fin m) : ℝ) * σ < r := by
      nlinarith [hcardσ, hσ, hc_nonneg]
    exact localEOWChart_mem_fixedWindow_of_strictNegativeImagBall
      (m := m) hm Ωminus x0 ys hσρ_le hcardσ_small hminusρ hw
  · refine hH_holo_big.mono ?_
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz ⊢
    nlinarith [hz, hσ]
  · intro w hw
    simpa [X] using hH_plus w hw
  · intro w hw
    simpa [X] using hH_minus w hw

end SCV
