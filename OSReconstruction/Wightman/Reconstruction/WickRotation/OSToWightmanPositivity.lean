/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValues
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValueLimits
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSemigroup
import OSReconstruction.Wightman.Reconstruction.WickRotation.EuclideanPositiveTime
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43Codomain
import OSReconstruction.SCV.PaleyWiener
import OSReconstruction.SCV.PartialFourierSpatial
import OSReconstruction.Mathlib429Compat
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Theorem 3 Positivity Infrastructure

This file contains the live production infrastructure for theorem 3
`bvt_W_positive`.

The endorsed route is now:
1. right-half-plane identity theorem,
2. single-component semigroup bridge on `{Re(z) > 0}`,
3. OS I Section 4.3 transport infrastructure,
4. quadratic identity on the transformed image,
5. final closure to arbitrary `BorchersSequence`.

The old same-test-function comparison route is false, even at `t = 0`, so this
file should not try to identify `WightmanInnerProduct (bvt_W ...)` with
`OSInnerProduct OS.S` on the same raw test data. The transport map is
essential.
-/

open scoped Topology Classical NNReal
open BigOperators Finset Complex
open MeasureTheory Filter
open OSReconstruction

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## Part 1: Identity theorem on the right half-plane -/

/-- Two holomorphic functions on {Re(z) > 0} that agree on (0,∞) agree everywhere.
This is the standard identity theorem for connected domains. -/
theorem identity_theorem_right_halfplane
    (f g : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.re})
    (hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.re})
    (hagree : ∀ t : ℝ, 0 < t → f (t : ℂ) = g (t : ℂ)) :
    ∀ z : ℂ, 0 < z.re → f z = g z := by
  have hU_open : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hU_preconn : IsPreconnected {z : ℂ | 0 < z.re} := by
    apply Convex.isPreconnected
    intro z hz w hw a b ha hb hab
    simp only [Set.mem_setOf_eq] at hz hw ⊢
    calc (a • z + b • w).re = a * z.re + b * w.re := by
            simp [Complex.add_re]
      _ > 0 := by
        rcases ha.lt_or_eq with ha' | ha'
        · have : b * w.re ≥ 0 := mul_nonneg hb hw.le
          have : a * z.re > 0 := mul_pos ha' hz
          linarith
        · have hab' : b = 1 := by linarith
          simp [← ha', hab', hw]
  have hf_an : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.re} := hf.analyticOnNhd hU_open
  have hg_an : AnalyticOnNhd ℂ g {z : ℂ | 0 < z.re} := hg.analyticOnNhd hU_open
  have h1_mem : (1 : ℂ) ∈ {z : ℂ | 0 < z.re} := by simp
  have hfg_an : AnalyticAt ℂ (f - g) 1 := (hf_an 1 h1_mem).sub (hg_an 1 h1_mem)
  have hfreq : ∃ᶠ z in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ, (f - g) z = 0 := by
    rw [Filter.Frequently]
    intro hev
    rw [Filter.Eventually] at hev
    rw [(nhdsWithin_basis_open 1 {(1 : ℂ)}ᶜ).mem_iff] at hev
    obtain ⟨u, ⟨h1u, hu_open⟩, hus⟩ := hev
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hu_open 1 h1u
    have hmem : ((1 + ε / 2 : ℝ) : ℂ) ∈ u := by
      apply hball
      rw [Metric.mem_ball, Complex.dist_eq]
      have hsub : ((1 + ε / 2 : ℝ) : ℂ) - 1 = ((ε / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [hsub]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      linarith
    have hne : ((1 + ε / 2 : ℝ) : ℂ) ≠ (1 : ℂ) := by
      intro heq
      have := congr_arg Complex.re heq
      simp at this; linarith [half_pos hε]
    have hzero : (f - g) ((1 + ε / 2 : ℝ) : ℂ) = 0 := by
      simp only [Pi.sub_apply, sub_eq_zero]; exact hagree (1 + ε / 2) (by linarith)
    exact hus ⟨hmem, hne⟩ hzero
  have hev : ∀ᶠ z in nhds (1 : ℂ), (f - g) z = 0 :=
    hfg_an.frequently_zero_iff_eventually_zero.mp hfreq
  have hfg_an_on : AnalyticOnNhd ℂ (f - g) {z : ℂ | 0 < z.re} := hf_an.sub hg_an
  have heqOn : Set.EqOn (f - g) 0 {z : ℂ | 0 < z.re} :=
    hfg_an_on.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU_preconn h1_mem hev
  intro z hz
  have := heqOn hz
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
  exact this

private theorem identity_theorem_upperHalfPlane
    (f g : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f SCV.upperHalfPlane)
    (hg : DifferentiableOn ℂ g SCV.upperHalfPlane)
    (hagree : ∀ η : ℝ, 0 < η → f (η * Complex.I) = g (η * Complex.I)) :
    ∀ z : ℂ, 0 < z.im → f z = g z := by
  let fR : ℂ → ℂ := fun w => f (Complex.I * w)
  let gR : ℂ → ℂ := fun w => g (Complex.I * w)
  have hmap : Set.MapsTo (fun w : ℂ => Complex.I * w)
      {z : ℂ | 0 < z.re} SCV.upperHalfPlane := by
    intro z hz
    simpa [SCV.upperHalfPlane, Complex.mul_im] using hz
  have hmul :
      DifferentiableOn ℂ (fun w : ℂ => Complex.I * w)
        {z : ℂ | 0 < z.re} := by
    intro z hz
    simpa using
      (((differentiableAt_id : DifferentiableAt ℂ (fun y : ℂ => y) z).const_mul
        Complex.I).differentiableWithinAt)
  have hfR : DifferentiableOn ℂ fR {z : ℂ | 0 < z.re} := hf.comp hmul hmap
  have hgR : DifferentiableOn ℂ gR {z : ℂ | 0 < z.re} := hg.comp hmul hmap
  have hagreeR : ∀ t : ℝ, 0 < t → fR (t : ℂ) = gR (t : ℂ) := by
    intro t ht
    simpa [fR, gR, mul_comm] using hagree t ht
  intro z hz
  have hzR : 0 < (-Complex.I * z).re := by
    simpa [Complex.mul_re] using hz
  have hmain :=
    identity_theorem_right_halfplane fR gR hfR hgR hagreeR (-Complex.I * z) hzR
  dsimp [fR, gR] at hmain
  convert hmain using 1 <;> ring_nf <;> simp

/-! ## Part 2: Semigroup bridge for single-component pairs -/

/-- For single-component positive-time Borchers sequences, the two holomorphic
extensions `bvt_singleSplit_xiShiftHolomorphicValue` and
`OSInnerProductTimeShiftHolomorphicValue` agree on the entire right half-plane.

Both are holomorphic on {Re(z) > 0} and both equal OS.S at real t > 0. -/
theorem bvt_xiShift_eq_osInnerProduct_holomorphicValue_single
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (z : ℂ) (hz : 0 < z.re) :
    bvt_singleSplit_xiShiftHolomorphicValue
        (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact z =
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord) z := by
  apply identity_theorem_right_halfplane
  · exact differentiableOn_bvt_singleSplit_xiShiftHolomorphicValue
      (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact
  · exact OSInnerProductTimeShiftHolomorphicValue_differentiableOn
      (d := d) OS lgc
      (PositiveTimeBorchersSequence.single n f hf_ord)
      (PositiveTimeBorchersSequence.single m g hg_ord)
  · intro t ht
    -- LHS at real t > 0: equals OS.S(n+m)(osConj f ⊗ timeShift_t g)
    rw [bvt_singleSplit_xiShiftHolomorphicValue_ofReal_eq_schwinger_timeShift
      (d := d) (OS := OS) (lgc := lgc) hm f hf_ord hf_compact g hg_ord hg_compact t ht]
    -- RHS at real t > 0: equals sum over k of OS.S(k+m)(...)
    rw [OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_right_single
      (d := d) (OS := OS) (lgc := lgc)
      (F := PositiveTimeBorchersSequence.single n f hf_ord)
      (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact) (t := t) ht]
    -- The sum collapses: single n f has bound = n, so only k = n contributes
    simp only [PositiveTimeBorchersSequence.single_toBorchersSequence,
      BorchersSequence.single_bound]
    rw [Finset.sum_range_succ]
    simp only [BorchersSequence.single_funcs_eq]
    have hvanish :
        ∑ k ∈ Finset.range n,
          OS.S (k + m) (ZeroDiagonalSchwartz.ofClassical
            (((BorchersSequence.single n f).funcs k).osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) t g))) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hk_ne : k ≠ n := by
        have := Finset.mem_range.mp hk; omega
      rw [BorchersSequence.single_funcs_ne hk_ne]
      have : (0 : SchwartzNPoint d k).osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) t g) = 0 := by
        simp [SchwartzNPoint.osConjTensorProduct, SchwartzNPoint.osConj_zero,
          SchwartzMap.tensorProduct_zero_left]
      rw [this]
      rw [ZeroDiagonalSchwartz.ofClassical_zero]
      exact (OS.E0_linear (k + m)).map_zero
    rw [hvanish, zero_add]
  · exact hz

/-- Rotated-horizontal-line form of the single-component semigroup bridge:
inside the Route `3b-II` boundary-value pairing, the rotated OS holomorphic
matrix element can be rewritten pointwise as the already-built
`singleSplit_xiShift` holomorphic trace.

This is not the missing Phase C' identity. It only transfers the **OS side** of
the horizontal-line boundary-value integral to the single-split holomorphic
supplier on the same right-half-plane point `-I * (x + η I)`. The remaining
frontier is the boundary-value identification of that trace with the Wightman
time-shift functional. -/
private theorem
    integral_rotated_OSInnerProductTimeShiftHolomorphicValue_eq_singleSplit_xiShiftHolomorphicValue_fourierTransform
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (χ : SchwartzMap ℝ ℂ) {η : ℝ} (hη : 0 < η) :
    (∫ x : ℝ,
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single m g hg_ord)
          (-Complex.I * ((x : ℂ) + η * Complex.I)) *
        (SchwartzMap.fourierTransformCLM ℂ χ) x)
      =
    ∫ x : ℝ,
      bvt_singleSplit_xiShiftHolomorphicValue
          (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact
          (-Complex.I * ((x : ℂ) + η * Complex.I)) *
        (SchwartzMap.fourierTransformCLM ℂ χ) x := by
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with x
  have hz : 0 < (-Complex.I * ((x : ℂ) + η * Complex.I)).re := by
    ring_nf
    simpa using hη
  have hpt :=
    bvt_xiShift_eq_osInnerProduct_holomorphicValue_single
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (f := f) (hf_ord := hf_ord) (hf_compact := hf_compact)
      (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
      (z := -Complex.I * ((x : ℂ) + η * Complex.I)) hz
  exact congrArg (fun z => z * (SchwartzMap.fourierTransformCLM ℂ χ) x) hpt.symm

/-- Distributional boundary value of the rotated `singleSplit_xiShift`
holomorphic trace on the real axis of the upper half-plane.

This is the semigroup-side boundary-value theorem transferred through Package
B. It gives the `singleSplit` trace the same spectral boundary functional as
the rotated OS holomorphic matrix element. The remaining Phase C' work is to
identify this boundary functional with the canonical Wightman time-shift
boundary functional. -/
private theorem
    tendsto_bvt_singleSplit_xiShiftHolomorphicValue_rotated_boundaryValue_fourierTransform
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (χ : SchwartzMap ℝ ℂ) :
    Filter.Tendsto
      (fun η : ℝ =>
        ∫ x : ℝ,
          bvt_singleSplit_xiShiftHolomorphicValue
              (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact
              (-Complex.I * ((x : ℂ) + η * Complex.I)) *
            (SchwartzMap.fourierTransformCLM ℂ χ) x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (selfAdjointSpectralBoundaryValueOffdiag
          (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
          (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
          (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single n f hf_ord⟧)) : OSHilbertSpace OS))
          (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single m g hg_ord⟧)) : OSHilbertSpace OS))
          χ)) := by
  have hOS :=
    tendsto_rotated_OSInnerProductTimeShiftHolomorphicValue_boundaryValue_fourierTransform
      (d := d) OS lgc
      (PositiveTimeBorchersSequence.single n f hf_ord)
      (PositiveTimeBorchersSequence.single m g hg_ord) χ
  have hEq :
      (fun η : ℝ =>
        ∫ x : ℝ,
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single m g hg_ord)
              (-Complex.I * ((x : ℂ) + η * Complex.I)) *
            (SchwartzMap.fourierTransformCLM ℂ χ) x)
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun η : ℝ =>
        ∫ x : ℝ,
          bvt_singleSplit_xiShiftHolomorphicValue
              (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact
              (-Complex.I * ((x : ℂ) + η * Complex.I)) *
            (SchwartzMap.fourierTransformCLM ℂ χ) x) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact
      integral_rotated_OSInnerProductTimeShiftHolomorphicValue_eq_singleSplit_xiShiftHolomorphicValue_fourierTransform
        (d := d) (OS := OS) (lgc := lgc) (hm := hm)
        (f := f) (hf_ord := hf_ord) (hf_compact := hf_compact)
        (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
        (χ := χ) hη
  exact Filter.Tendsto.congr' hEq hOS

/-! ## Part 3: Sorry 3 — Wightman positive-definiteness

CRITICAL ROUTE CORRECTION (Entry #277):

The former Package C (`hschw`) — equating `OS.S(osConj f ⊗ timeShift_t g)` with
`bvt_W(conj f ⊗ timeShift_t g)` — is MATHEMATICALLY FALSE.

Reason: `timeShiftSchwartzNPoint t` is a real time translation. On the OS/Euclidean
side it corresponds to the contraction semigroup `e^{-tH}` (decaying). On the
Wightman/Minkowski side it corresponds to the unitary group `e^{itH}` (oscillating).
The equation `e^{-tH} = e^{itH}` is false for nontrivial H.

The entire production reduction chain through `hschw` consumes a false hypothesis.

The correct route is OS I Section 4.3: construct the transport map
`u : BorchersSequence d → OSHilbertSpace OS` via Fourier-Laplace transform,
and prove `W(f* × f) = ‖u(f)‖²_H ≥ 0` directly. This does NOT go through
any time-shifted Schwinger-vs-Wightman comparison. -/

namespace EuclideanPositiveTimeComponent

variable {n : ℕ}

/-- A positive-time component viewed as the corresponding single positive-time
Borchers sequence. This is the Euclidean-side input object whose image under
the eventual Section 4.3 transport map will be compared against the Wightman
quadratic form. -/
def toPositiveTimeSingle
    (f : EuclideanPositiveTimeComponent d n) :
    PositiveTimeBorchersSequence d :=
  PositiveTimeBorchersSequence.single n f.1 f.2

end EuclideanPositiveTimeComponent

/-! ### Ordered head-gap frozen-time helpers -/

/-- The head time coordinate used when the OS I one-variable time interchange
isolates the first point of a positive-time block. -/
private def headSliceIndex {q : ℕ} (hq : 0 < q) : Fin q :=
  ⟨0, hq⟩

/-- Frozen background times relative to the head coordinate of an ordered
positive-time block. These are nonnegative away from the head, by ordering. -/
private def orderedHeadGapTimes {q : ℕ} (hq : 0 < q)
    (x : NPointDomain d q) : Fin q → ℝ :=
  fun i => x i 0 - x (headSliceIndex hq) 0

set_option linter.unusedSectionVars false in
/-- In an ordered positive-time block, every non-head time is after the head
time, so the head-gap frozen background times are nonnegative. -/
private theorem orderedHeadGapTimes_nonneg_of_orderedPositive
    {q : ℕ} (hq : 0 < q)
    {x : NPointDomain d q}
    (hx : x ∈ OrderedPositiveTimeRegion d q) :
    ∀ i : Fin q, i ≠ headSliceIndex hq →
      0 ≤ orderedHeadGapTimes (d := d) hq x i := by
  intro i hi
  have h0i : headSliceIndex hq < i := by
    rw [Fin.lt_def, headSliceIndex]
    exact Nat.pos_of_ne_zero (by
      intro hzero
      exact hi (Fin.ext hzero))
  have hlt : x (headSliceIndex hq) 0 < x i 0 :=
    (hx (headSliceIndex hq)).2 i h0i
  dsimp [orderedHeadGapTimes]
  linarith

/-! ### One-point positive-time slice support -/

/-- A one-point Euclidean Schwartz test supported in strictly positive time has
every fixed-spatial slice supported in nonnegative time. This is the exact
support input needed by the one-variable Section 4.3 Paley-Wiener supplier. -/
private theorem tsupport_spatialSlice_subset_Ici_of_timePositive
    (f : SchwartzSpacetime d)
    (hf_pos : tsupport (f : SpacetimeDim d → ℂ) ⊆ {x | 0 < x 0})
    (y : Fin d → ℝ) :
    tsupport (fun t : ℝ => f (Fin.cons t y)) ⊆ Set.Ici 0 := by
  intro t ht
  by_contra ht_neg
  have ht_lt : t < 0 := by
    simpa [Set.mem_Ici, not_le] using ht_neg
  have ht_not : t ∉ tsupport (fun s : ℝ => f (Fin.cons s y)) := by
    rw [notMem_tsupport_iff_eventuallyEq]
    have hball : Metric.ball t (-t / 2) ∈ 𝓝 t := by
      apply Metric.ball_mem_nhds
      linarith
    filter_upwards [hball] with s hs
    have hsabs : |s - t| < -t / 2 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hs
    have hs_lt : s < 0 := by
      linarith [(abs_lt.mp hsabs).2, ht_lt]
    have hs_not_mem : (Fin.cons s y : SpacetimeDim d) ∉ tsupport (f : SpacetimeDim d → ℂ) := by
      intro hs_mem
      have hs_pos : 0 < (Fin.cons s y : SpacetimeDim d) 0 := hf_pos hs_mem
      have : 0 < s := by simpa using hs_pos
      linarith
    exact image_eq_zero_of_notMem_tsupport hs_not_mem
  exact ht_not ht

/-! ### n-point ordered-positive slice support for branch `3b` -/

/-- If one chosen time coordinate is negative, the time/spatial reindexing of
an ordered-positive-time Euclidean test vanishes at that point. -/
private theorem nPointTimeSpatialSchwartzCLE_eq_zero_of_neg_time
    {n : ℕ}
    (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (η : EuclideanSpace ℝ (Fin n × Fin d))
    {s : ℝ} (hs : s < 0) :
    OSReconstruction.nPointTimeSpatialSchwartzCLE (d := d) (n := n) f.1
      (Function.update t r s, η) = 0 := by
  have hnot_ord :
      (OSReconstruction.nPointTimeSpatialCLE (d := d) n).symm (Function.update t r s, η) ∉
        OrderedPositiveTimeRegion d n := by
    intro hmem
    have htime : 0 <
        (((OSReconstruction.nPointTimeSpatialCLE (d := d) n).symm
          (Function.update t r s, η)) r 0) := (hmem r).1
    have hEq :
        (((OSReconstruction.nPointTimeSpatialCLE (d := d) n).symm
          (Function.update t r s, η)) r 0) = s := by
      simp [OSReconstruction.nPointTimeSpatialCLE]
    linarith
  have hnot_supp :
      (OSReconstruction.nPointTimeSpatialCLE (d := d) n).symm (Function.update t r s, η) ∉
        tsupport (f.1 : NPointDomain d n → ℂ) := by
    intro hx
    exact hnot_ord (f.2 hx)
  change f.1 ((OSReconstruction.nPointTimeSpatialCLE (d := d) n).symm
    (Function.update t r s, η)) = 0
  simpa using image_eq_zero_of_notMem_tsupport hnot_supp

/-- Negative time in one chosen coordinate forces the branch-`3b` partial
spatial Fourier transform to vanish at that point. -/
private theorem partialFourierSpatial_fun_eq_zero_of_neg_time
    {n : ℕ}
    (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    {s : ℝ} (hs : s < 0) :
    OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f.1
      (Function.update t r s, ξ) = 0 := by
  rw [OSReconstruction.partialFourierSpatial_fun_eq_integral]
  refine MeasureTheory.integral_eq_zero_of_ae ?_
  filter_upwards with η
  simp [nPointTimeSpatialSchwartzCLE_eq_zero_of_neg_time (f := f) (r := r)
    (t := t) (η := η) hs]

/-- Fixing the spatial momentum block and all but one time coordinate, the
branch-`3b` partial spatial Fourier transform of an ordered-positive-time
Euclidean test is supported in `t ≥ 0` in the remaining time variable. This is
the exact support input needed for the one-variable Section 4.3 supplier. -/
private theorem tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
    {n : ℕ}
    (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    tsupport (fun s : ℝ =>
      OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f.1
        (Function.update t r s, ξ)) ⊆ Set.Ici 0 := by
  intro s hs
  by_contra hs_neg
  have hs_lt : s < 0 := by
    simpa [Set.mem_Ici, not_le] using hs_neg
  have hs_not :
      s ∉ tsupport (fun s' : ℝ =>
        OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f.1
          (Function.update t r s', ξ)) := by
    rw [notMem_tsupport_iff_eventuallyEq]
    have hball : Metric.ball s (-s / 2) ∈ 𝓝 s := by
      apply Metric.ball_mem_nhds
      linarith
    filter_upwards [hball] with s' hs'
    have hsabs : |s' - s| < -s / 2 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hs'
    have hs'_lt : s' < 0 := by
      linarith [(abs_lt.mp hsabs).2, hs_lt]
    exact partialFourierSpatial_fun_eq_zero_of_neg_time
      (f := f) r t ξ hs'_lt
  exact hs_not hs

/-- A branch-`3b` one-variable time slice is continuous. -/
private theorem continuous_partialFourierSpatial_timeSlice
    {n : ℕ}
    (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    Continuous (fun s : ℝ =>
      OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f.1
        (Function.update t r s, ξ)) := by
  have hupdate : Continuous (fun s : ℝ => (Function.update t r s, ξ)) := by
    refine Continuous.prodMk ?_ continuous_const
    refine continuous_pi ?_
    intro i
    by_cases hi : i = r
    · subst hi
      simpa using continuous_id
    · simpa [Function.update, hi] using (continuous_const : Continuous fun _ : ℝ => t i)
  exact (OSReconstruction.continuous_partialFourierSpatial_fun (d := d) (n := n) f.1).comp hupdate

/-- A branch-`3b` one-variable time slice has polynomial growth on the real
line. In fact it is uniformly bounded, by the companion-file partial Fourier
estimate. -/
private theorem hasPolynomialGrowthOnLine_partialFourierSpatial_timeSlice
    {n : ℕ}
    (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    SCV.HasPolynomialGrowthOnLine (fun s : ℝ =>
      OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f.1
        (Function.update t r s, ξ)) := by
  rcases OSReconstruction.exists_norm_bound_partialFourierSpatial_fun (d := d) (n := n) f.1 with
    ⟨C, hC, hbound⟩
  refine ⟨C + 1, 0, by positivity, ?_⟩
  intro s
  calc
    ‖OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f.1
        (Function.update t r s, ξ)‖ ≤ C := hbound (Function.update t r s, ξ)
    _ ≤ (C + 1) * (1 + |s|) ^ (0 : ℕ) := by
      simp

/-- Every fixed time-coordinate polynomial weight is uniformly bounded on a
branch-`3b` one-variable time slice. This is the first weighted bound toward
proving that the slice itself is a Schwartz function of the chosen time
variable. -/
private theorem exists_timePow_norm_bound_partialFourierSpatial_timeSlice
    {n : ℕ}
    (f : SchwartzNPoint d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℝ,
        ‖((s : ℂ) ^ k) *
          OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f
            (Function.update t r s, ξ)‖ ≤ C := by
  rcases OSReconstruction.exists_timeCoordPow_norm_bound_partialFourierSpatial_fun
      (d := d) (n := n) f r k with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro s
  simpa using hbound (Function.update t r s, ξ)

/-- The ordinary one-variable derivative of a branch-`3b` time slice is the
same transported Schwartz input that appears in the ambient time-direction
`fderiv` theorem, specialized to the update curve in the chosen coordinate. -/
private theorem deriv_partialFourierSpatial_timeSlice_eq_transport
    {n : ℕ}
    (f : SchwartzNPoint d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (s : ℝ) :
    deriv
      (fun u : ℝ =>
        OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f
          (Function.update t r u, ξ))
      s =
    OSReconstruction.partialFourierSpatial_fun (d := d) (n := n)
      ((OSReconstruction.nPointSpatialTimeSchwartzCLE (d := d) (n := n)).symm
        (LineDeriv.lineDerivOp
          ((0 : EuclideanSpace ℝ (Fin n × Fin d)),
            Pi.single (M := fun _ : Fin n => ℝ) r (1 : ℝ))
          (OSReconstruction.nPointSpatialTimeSchwartzCLE (d := d) (n := n) f)))
      (Function.update t r s, ξ) := by
  have hcomp :
      HasDerivAt
        (fun u : ℝ =>
          OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f
            (Function.update t r u, ξ))
        ((fderiv ℝ
            (fun u : Fin n → ℝ =>
              OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f (u, ξ))
            (Function.update t r s))
          (Pi.single (M := fun _ : Fin n => ℝ) r (1 : ℝ)))
        s := by
    simpa using
      (((OSReconstruction.differentiableAt_partialFourierSpatial_fun_time
          (d := d) (n := n) f ξ (Function.update t r s)).hasFDerivAt).comp s
        (hasDerivAt_update t r s).hasFDerivAt).hasDerivAt
  calc
    deriv
        (fun u : ℝ =>
          OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f
            (Function.update t r u, ξ))
        s
      =
        ((fderiv ℝ
            (fun u : Fin n → ℝ =>
              OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f (u, ξ))
            (Function.update t r s))
          (Pi.single (M := fun _ : Fin n => ℝ) r (1 : ℝ))) := hcomp.deriv
    _ = OSReconstruction.partialFourierSpatial_fun (d := d) (n := n)
          ((OSReconstruction.nPointSpatialTimeSchwartzCLE (d := d) (n := n)).symm
            (LineDeriv.lineDerivOp
              ((0 : EuclideanSpace ℝ (Fin n × Fin d)),
                Pi.single (M := fun _ : Fin n => ℝ) r (1 : ℝ))
              (OSReconstruction.nPointSpatialTimeSchwartzCLE (d := d) (n := n) f)))
          (Function.update t r s, ξ) := by
            simpa using
              OSReconstruction.fderiv_partialFourierSpatial_fun_time_apply_eq_transport
                (d := d) (n := n) f ξ (Function.update t r s)
                (Pi.single (M := fun _ : Fin n => ℝ) r (1 : ℝ))

/-- The first derivative of a branch-`3b` time slice also satisfies every
fixed time-coordinate polynomial bound. This is the first honest `n = 1` step
toward proving the slice is Schwartz in the chosen time variable. -/
private theorem exists_timePow_norm_bound_deriv_partialFourierSpatial_timeSlice
    {n : ℕ}
    (f : SchwartzNPoint d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℝ,
        ‖((s : ℂ) ^ k) *
          deriv
            (fun u : ℝ =>
              OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f
                (Function.update t r u, ξ))
            s‖ ≤ C := by
  let g : SchwartzNPoint d n :=
    ((OSReconstruction.nPointSpatialTimeSchwartzCLE (d := d) (n := n)).symm
      (LineDeriv.lineDerivOp
        ((0 : EuclideanSpace ℝ (Fin n × Fin d)),
          Pi.single (M := fun _ : Fin n => ℝ) r (1 : ℝ))
        (OSReconstruction.nPointSpatialTimeSchwartzCLE (d := d) (n := n) f)))
  rcases OSReconstruction.exists_timeCoordPow_norm_bound_partialFourierSpatial_fun
      (d := d) (n := n) g r k with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro s
  rw [deriv_partialFourierSpatial_timeSlice_eq_transport (f := f) r t ξ s]
  simpa [g] using hbound (Function.update t r s, ξ)

/-- The Schwartz-input transport corresponding to one ordinary derivative of
the branch-`3b` time slice in the chosen coordinate. -/
private noncomputable def timeDerivTransportInput
    {n : ℕ} (r : Fin n) (f : SchwartzNPoint d n) : SchwartzNPoint d n :=
  ((OSReconstruction.nPointSpatialTimeSchwartzCLE (d := d) (n := n)).symm
    (LineDeriv.lineDerivOp
      ((0 : EuclideanSpace ℝ (Fin n × Fin d)),
        Pi.single (M := fun _ : Fin n => ℝ) r (1 : ℝ))
      (OSReconstruction.nPointSpatialTimeSchwartzCLE (d := d) (n := n) f)))

/-- Repeated time differentiation of the branch-`3b` slice corresponds to
repeated application of `timeDerivTransportInput` on the Schwartz input. -/
private noncomputable def iteratedTimeDerivTransport
    {n : ℕ} (r : Fin n) (m : ℕ) (f : SchwartzNPoint d n) : SchwartzNPoint d n :=
  (timeDerivTransportInput (d := d) (n := n) r)^[m] f

/-- The `m`-th iterated ordinary derivative of the branch-`3b` time slice is
again the same slice, but with the input replaced by the recursively
transported Schwartz datum. -/
private theorem iteratedDeriv_partialFourierSpatial_timeSlice_eq_transport
    {n : ℕ}
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    ∀ (m : ℕ) (f : SchwartzNPoint d n) (s : ℝ),
      iteratedDeriv m
        (fun u : ℝ =>
          OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f
            (Function.update t r u, ξ))
        s =
      OSReconstruction.partialFourierSpatial_fun (d := d) (n := n)
        (iteratedTimeDerivTransport (d := d) (n := n) r m f)
        (Function.update t r s, ξ) := by
  intro m
  induction m with
  | zero =>
      intro f s
      simp [iteratedTimeDerivTransport]
  | succ m ih =>
      intro f s
      rw [iteratedDeriv_succ']
      have hArg :
          iteratedDeriv m
            (deriv
              (fun u : ℝ =>
                OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f
                  (Function.update t r u, ξ)))
            s =
          iteratedDeriv m
            (fun u : ℝ =>
              OSReconstruction.partialFourierSpatial_fun (d := d) (n := n)
                (timeDerivTransportInput (d := d) (n := n) r f)
                (Function.update t r u, ξ))
            s := by
        congr 1
        ext u
        simpa [timeDerivTransportInput] using
          deriv_partialFourierSpatial_timeSlice_eq_transport
            (d := d) (n := n) (f := f) r t ξ u
      calc
        iteratedDeriv m
            (deriv
              (fun u : ℝ =>
                OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f
                  (Function.update t r u, ξ)))
            s
          =
            iteratedDeriv m
              (fun u : ℝ =>
                OSReconstruction.partialFourierSpatial_fun (d := d) (n := n)
                  (timeDerivTransportInput (d := d) (n := n) r f)
                  (Function.update t r u, ξ))
              s := hArg
        _ = OSReconstruction.partialFourierSpatial_fun (d := d) (n := n)
              (iteratedTimeDerivTransport (d := d) (n := n) r (m + 1) f)
              (Function.update t r s, ξ) := by
              simpa [iteratedTimeDerivTransport, timeDerivTransportInput,
                Function.iterate_succ_apply] using
                ih (timeDerivTransportInput (d := d) (n := n) r f) s

/-- Every iterated ordinary derivative of the branch-`3b` time slice satisfies
every fixed polynomial time-weight bound. -/
private theorem exists_timePow_norm_bound_iteratedDeriv_partialFourierSpatial_timeSlice
    {n : ℕ}
    (f : SchwartzNPoint d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (k m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℝ,
        ‖((s : ℂ) ^ k) *
          iteratedDeriv m
            (fun u : ℝ =>
              OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f
                (Function.update t r u, ξ))
            s‖ ≤ C := by
  rcases exists_timePow_norm_bound_partialFourierSpatial_timeSlice
      (d := d) (n := n)
      (f := iteratedTimeDerivTransport (d := d) (n := n) r m f)
      r t ξ k with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro s
  rw [iteratedDeriv_partialFourierSpatial_timeSlice_eq_transport
      (d := d) (n := n) r t ξ m f s]
  simpa using hbound s

/-- Every branch-`3b` time slice is differentiable, with derivative given by
the transported Schwartz input from `timeDerivTransportInput`. -/
private theorem differentiable_partialFourierSpatial_timeSlice
    {n : ℕ}
    (f : SchwartzNPoint d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    Differentiable ℝ
      (fun s : ℝ =>
        OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f
          (Function.update t r s, ξ)) := by
  intro s
  have hcomp :
      HasDerivAt
        (fun u : ℝ =>
          OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f
            (Function.update t r u, ξ))
        (OSReconstruction.partialFourierSpatial_fun (d := d) (n := n)
          (timeDerivTransportInput (d := d) (n := n) r f)
          (Function.update t r s, ξ))
        s := by
    have hbase :
        HasDerivAt
          (fun u : ℝ =>
            OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f
              (Function.update t r u, ξ))
          ((fderiv ℝ
              (fun u : Fin n → ℝ =>
              OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f (u, ξ))
              (Function.update t r s))
            (Pi.single (M := fun _ : Fin n => ℝ) r (1 : ℝ)))
        s := by
      simpa using
        (((OSReconstruction.differentiableAt_partialFourierSpatial_fun_time
            (d := d) (n := n) f ξ (Function.update t r s)).hasFDerivAt).comp s
          (hasDerivAt_update t r s).hasFDerivAt).hasDerivAt
    convert hbase using 1
    simpa [timeDerivTransportInput] using
      (OSReconstruction.fderiv_partialFourierSpatial_fun_time_apply_eq_transport
        (d := d) (n := n) f ξ (Function.update t r s)
        (Pi.single (M := fun _ : Fin n => ℝ) r (1 : ℝ))).symm
  exact hcomp.differentiableAt

/-- The branch-`3b` time slice is a Schwartz function of the chosen time
variable. -/
private theorem contDiff_partialFourierSpatial_timeSlice
    {n : ℕ}
    (f : SchwartzNPoint d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun s : ℝ =>
        OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f
          (Function.update t r s, ξ)) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro m hm
  have hEq :
      iteratedDeriv m
        (fun s : ℝ =>
          OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f
            (Function.update t r s, ξ)) =
      fun s : ℝ =>
        OSReconstruction.partialFourierSpatial_fun (d := d) (n := n)
          (iteratedTimeDerivTransport (d := d) (n := n) r m f)
          (Function.update t r s, ξ) := by
    ext s
    simpa using
      iteratedDeriv_partialFourierSpatial_timeSlice_eq_transport
        (d := d) (n := n) r t ξ m f s
  rw [hEq]
  exact differentiable_partialFourierSpatial_timeSlice
    (d := d) (n := n)
    (f := iteratedTimeDerivTransport (d := d) (n := n) r m f) r t ξ

/-- The branch-`3b` time slice, packaged honestly as a Schwartz function in the
chosen time variable. -/
noncomputable def partialFourierSpatial_timeSliceSchwartz
    {n : ℕ}
    (f : SchwartzNPoint d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    SchwartzMap ℝ ℂ where
  toFun := fun s : ℝ =>
    OSReconstruction.partialFourierSpatial_fun (d := d) (n := n) f
      (Function.update t r s, ξ)
  smooth' := contDiff_partialFourierSpatial_timeSlice (d := d) (n := n) f r t ξ
  decay' := by
    intro k m
    rcases exists_timePow_norm_bound_iteratedDeriv_partialFourierSpatial_timeSlice
        (d := d) (n := n) f r t ξ k m with ⟨C, _, hC⟩
    refine ⟨C, ?_⟩
    intro s
    simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hC s

/-! ### One-variable Section 4.3 Fourier-Laplace supplier -/

/-- The one-variable complex Laplace transform used by the Section 4.3
Fourier-Laplace transport. -/
private noncomputable def complexLaplaceTransform
    (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (-s * (t : ℂ)) * f t

private theorem complexCoord_hasTemperateGrowth :
    (fun t : ℝ => (t : ℂ)).HasTemperateGrowth := by
  fun_prop

private theorem complexNegCoordPow_hasTemperateGrowth (N : ℕ) :
    (fun t : ℝ => (-(t : ℂ)) ^ N).HasTemperateGrowth := by
  fun_prop

private theorem complexLaplaceTransform_integrable_of_nonneg_re
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    (s : ℂ) (hs : 0 ≤ s.re) :
    Integrable (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * f t) := by
  apply MeasureTheory.Integrable.mono f.integrable
  · exact ((Complex.continuous_exp.comp
        ((continuous_const : Continuous (fun _ : ℝ => -s)).mul Complex.continuous_ofReal)).mul
        f.continuous).aestronglyMeasurable
  · filter_upwards with t
    simp only [norm_mul, Complex.norm_exp]
    by_cases ht : (f : ℝ → ℂ) t = 0
    · simp [ht]
    · have ht_supp : t ∈ tsupport (f : ℝ → ℂ) := subset_tsupport _ ht
      have ht_nonneg : 0 ≤ t := Set.mem_Ici.mp (hf_supp ht_supp)
      have hre : (-s * (t : ℂ)).re = -(s.re * t) := by
        simp [Complex.mul_re]
      rw [hre]
      have hexp : Real.exp (-(s.re * t)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith)
      exact mul_le_of_le_one_left (norm_nonneg _) hexp

private theorem weightedSchwartz_integrable
    (f : SchwartzMap ℝ ℂ) :
    Integrable (fun t : ℝ => (t : ℂ) * f t) := by
  convert
    ((SchwartzMap.smulLeftCLM (F := ℂ) (g := fun t : ℝ => (t : ℂ)) f).integrable
      (μ := MeasureTheory.volume)) using 1
  ext t
  rw [SchwartzMap.smulLeftCLM_apply_apply (F := ℂ) complexCoord_hasTemperateGrowth]
  simp [smul_eq_mul]

private noncomputable def weightedNegCoordPowSchwartz
    (N : ℕ) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM (F := ℂ) (g := fun t : ℝ => (-(t : ℂ)) ^ N) f

private theorem weightedNegCoordPowSchwartz_apply
    (N : ℕ) (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    weightedNegCoordPowSchwartz N f t = (-(t : ℂ)) ^ N * f t := by
  rw [weightedNegCoordPowSchwartz,
    SchwartzMap.smulLeftCLM_apply_apply (F := ℂ) (complexNegCoordPow_hasTemperateGrowth N)]
  simp [smul_eq_mul]

private theorem weightedNegCoordPowSchwartz_support
    (N : ℕ) (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0) :
    tsupport (weightedNegCoordPowSchwartz N f : ℝ → ℂ) ⊆ Set.Ici 0 := by
  exact (SchwartzMap.tsupport_smulLeftCLM_subset (g := fun t : ℝ => (-(t : ℂ)) ^ N) (f := f)).trans
    (Set.inter_subset_left.trans hf_supp)

private theorem weightedNegCoordPowSchwartz_integrable
    (N : ℕ) (f : SchwartzMap ℝ ℂ) :
    Integrable (fun t : ℝ => (-(t : ℂ)) ^ N * f t) := by
  convert (weightedNegCoordPowSchwartz N f).integrable (μ := MeasureTheory.volume) using 1
  ext t
  rw [weightedNegCoordPowSchwartz_apply]

private theorem re_mem_rightHalfPlane_of_mem_ball
    {s s₀ : ℂ} (hs₀ : 0 < s₀.re)
    (hs : s ∈ Metric.ball s₀ (s₀.re / 2)) :
    0 < s.re := by
  have hs_norm : ‖s - s₀‖ < s₀.re / 2 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hs
  have h_re_lower : -(‖s - s₀‖) ≤ (s - s₀).re := by
    have habs : |(s - s₀).re| ≤ ‖s - s₀‖ := Complex.abs_re_le_norm (s - s₀)
    exact (abs_le.mp habs).1
  have hdelta : -(s₀.re / 2) < (s - s₀).re := by
    linarith
  have hs_eq : s.re = s₀.re + (s - s₀).re := by
    have : s = s₀ + (s - s₀) := by ring
    exact congrArg Complex.re this
  linarith

private theorem complexLaplaceKernel_hasDerivAt
    (t : ℝ) (s : ℂ) :
    HasDerivAt (fun z : ℂ => Complex.exp (-z * (t : ℂ)))
      ((-(t : ℂ)) * Complex.exp (-s * (t : ℂ))) s := by
  have hlin : HasDerivAt (fun z : ℂ => -z * (t : ℂ)) (-(t : ℂ)) s := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id s).neg).mul_const (t : ℂ))
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (Complex.hasDerivAt_exp (-s * (t : ℂ))).comp s hlin

private theorem complexLaplaceKernelDeriv_norm_le_weighted
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    {s s₀ : ℂ} (hs₀ : 0 < s₀.re)
    (hs : s ∈ Metric.ball s₀ (s₀.re / 2))
    (t : ℝ) :
    ‖((-(t : ℂ)) * Complex.exp (-s * (t : ℂ)) * f t)‖ ≤ ‖((t : ℂ) * f t)‖ := by
  by_cases ht : (f : ℝ → ℂ) t = 0
  · simp [ht]
  · have ht_supp : t ∈ tsupport (f : ℝ → ℂ) := subset_tsupport _ ht
    have ht_nonneg : 0 ≤ t := Set.mem_Ici.mp (hf_supp ht_supp)
    have hs_re_nonneg : 0 ≤ s.re := le_of_lt (re_mem_rightHalfPlane_of_mem_ball hs₀ hs)
    have hre : (-s * (t : ℂ)).re = -(s.re * t) := by
      simp [Complex.mul_re]
    rw [norm_mul, norm_mul, Complex.norm_exp, hre]
    have hexp : Real.exp (-(s.re * t)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    calc
      ‖-(t : ℂ)‖ * Real.exp (-(s.re * t)) * ‖f t‖
          ≤ ‖-(t : ℂ)‖ * 1 * ‖f t‖ := by
            gcongr
      _ = ‖(t : ℂ)‖ * ‖f t‖ := by simp
      _ = ‖(t : ℂ) * f t‖ := by rw [norm_mul]

private theorem complexLaplaceTransform_hasDerivAt_rightHalfPlane
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0) :
    ∀ s₀ : ℂ, 0 < s₀.re →
      HasDerivAt (complexLaplaceTransform f)
        (∫ t : ℝ, (-(t : ℂ)) * Complex.exp (-s₀ * (t : ℂ)) * f t) s₀ := by
  intro s₀ hs₀
  let F : ℂ → ℝ → ℂ := fun s t => Complex.exp (-s * (t : ℂ)) * f t
  let F' : ℂ → ℝ → ℂ := fun s t => (-(t : ℂ)) * Complex.exp (-s * (t : ℂ)) * f t
  let bound : ℝ → ℝ := fun t => ‖(t : ℂ) * f t‖
  have hs_ball : Metric.ball s₀ (s₀.re / 2) ∈ nhds s₀ := Metric.ball_mem_nhds s₀ (half_pos hs₀)
  have h :
      HasDerivAt (fun s => ∫ t, F s t) (∫ t, F' s₀ t) s₀ :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (x₀ := s₀) (s := Metric.ball s₀ (s₀.re / 2))
    (bound := bound)
    hs_ball
    (Filter.Eventually.of_forall (fun s =>
      ((Complex.continuous_exp.comp
        ((continuous_const : Continuous (fun _ : ℝ => -s)).mul Complex.continuous_ofReal)).mul
        f.continuous).aestronglyMeasurable))
    (complexLaplaceTransform_integrable_of_nonneg_re f hf_supp s₀ hs₀.le)
    (((Complex.continuous_ofReal.neg.mul
        (Complex.continuous_exp.comp
          ((continuous_const : Continuous (fun _ : ℝ => -s₀)).mul Complex.continuous_ofReal))).mul
        f.continuous).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun t s hs =>
      complexLaplaceKernelDeriv_norm_le_weighted f hf_supp hs₀ hs t))
    ((weightedSchwartz_integrable f).norm)
    (Filter.Eventually.of_forall (fun t s _ => by
      simpa [F, F', mul_assoc, mul_left_comm, mul_comm] using
        ((complexLaplaceKernel_hasDerivAt t s).mul_const (f t))))
    ).2
  change HasDerivAt (fun s => ∫ t : ℝ, Complex.exp (-s * (t : ℂ)) * f t)
    (∫ t : ℝ, (-(t : ℂ)) * Complex.exp (-s₀ * (t : ℂ)) * f t) s₀
  simpa [F, F', mul_assoc, mul_left_comm, mul_comm] using h

private theorem complexLaplaceTransform_real_hasDerivAt
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    {s₀ : ℝ} (hs₀ : 0 < s₀) :
    HasDerivAt (fun s : ℝ => complexLaplaceTransform f (s : ℂ))
      (∫ t : ℝ, (-(t : ℂ)) * Complex.exp (-((s₀ : ℂ)) * (t : ℂ)) * f t) s₀ := by
  simpa using
    (complexLaplaceTransform_hasDerivAt_rightHalfPlane f hf_supp (s₀ : ℂ) (by simpa using hs₀)).comp_ofReal

private theorem complexLaplaceTransform_real_differentiableOn
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0) :
    DifferentiableOn ℝ (fun s : ℝ => complexLaplaceTransform f (s : ℂ)) (Set.Ioi 0) := by
  intro s hs
  exact (complexLaplaceTransform_real_hasDerivAt f hf_supp hs).differentiableAt.differentiableWithinAt

private theorem complexLaplaceTransform_real_hasDerivAt_weighted
    (N : ℕ)
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    {s₀ : ℝ} (hs₀ : 0 < s₀) :
    HasDerivAt
      (fun s : ℝ => complexLaplaceTransform (weightedNegCoordPowSchwartz N f) (s : ℂ))
      (∫ t : ℝ, (-(t : ℂ)) ^ (N + 1) * Complex.exp (-((s₀ : ℂ)) * (t : ℂ)) * f t) s₀ := by
  have hbase :=
    complexLaplaceTransform_real_hasDerivAt
      (weightedNegCoordPowSchwartz N f)
      (weightedNegCoordPowSchwartz_support N f hf_supp)
      hs₀
  convert hbase using 1
  congr with t
  rw [weightedNegCoordPowSchwartz_apply]
  ring_nf

private theorem complexLaplaceTransform_differentiableOn_rightHalfPlane
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0) :
    DifferentiableOn ℂ (complexLaplaceTransform f) {s : ℂ | 0 < s.re} := by
  intro s hs
  exact (complexLaplaceTransform_hasDerivAt_rightHalfPlane f hf_supp s hs).differentiableAt.differentiableWithinAt

private theorem schwartz_eq_zero_of_neg
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    {x : ℝ} (hx : x < 0) :
    f x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hx_mem
  exact not_lt_of_ge (Set.mem_Ici.mp (hf_supp hx_mem)) hx

private theorem schwartz_zero_at_zero_of_support
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0) :
    f 0 = 0 := by
  have hseq : Tendsto (fun n : ℕ => (-(1 / ((n : ℝ) + 1)) : ℝ)) atTop (𝓝 0) := by
    simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1))) atTop (𝓝 0)).neg
  have hcont :
      Tendsto (fun n : ℕ => f (-(1 / ((n : ℝ) + 1)) : ℝ)) atTop (𝓝 (f 0)) :=
    f.continuous.continuousAt.tendsto.comp hseq
  have hzero :
      Tendsto (fun n : ℕ => f (-(1 / ((n : ℝ) + 1)) : ℝ)) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' <| Filter.Eventually.of_forall ?_
    intro n
    symm
    apply schwartz_eq_zero_of_neg f hf_supp
    have hpos : 0 < (1 / ((n : ℝ) + 1)) := by positivity
    linarith
  exact tendsto_nhds_unique hcont hzero

private theorem schwartz_tendsto_zero_nhdsWithin_right_of_support
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0) :
    Tendsto (fun x : ℝ => f x) (𝓝[>] 0) (𝓝 0) := by
  simpa [ContinuousWithinAt, schwartz_zero_at_zero_of_support f hf_supp] using
    (f.continuous.continuousAt.continuousWithinAt : ContinuousWithinAt f (Set.Ioi 0) 0)

private def iteratedDerivSchwartz : ℕ → SchwartzMap ℝ ℂ → SchwartzMap ℝ ℂ
  | 0, f => f
  | n + 1, f => SchwartzMap.derivCLM ℂ ℂ (iteratedDerivSchwartz n f)

private theorem tsupport_iteratedDerivSchwartz_subset
    (n : ℕ) (f : SchwartzMap ℝ ℂ) :
    tsupport ((iteratedDerivSchwartz n f : SchwartzMap ℝ ℂ) : ℝ → ℂ) ⊆
      tsupport (f : ℝ → ℂ) := by
  induction n with
  | zero =>
      simp [iteratedDerivSchwartz]
  | succ n ih =>
      simpa [iteratedDerivSchwartz] using
        ((SchwartzMap.tsupport_derivCLM_subset (𝕜 := ℂ) (F := ℂ) (iteratedDerivSchwartz n f)).trans ih)

private theorem complexLaplaceKernel_norm_le_self
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    {s : ℂ} (hs : 0 ≤ s.re)
    (t : ℝ) :
    ‖Complex.exp (-s * (t : ℂ)) * f t‖ ≤ ‖f t‖ := by
  by_cases ht : (f : ℝ → ℂ) t = 0
  · simp [ht]
  · have ht_supp : t ∈ tsupport (f : ℝ → ℂ) := subset_tsupport _ ht
    have ht_nonneg : 0 ≤ t := Set.mem_Ici.mp (hf_supp ht_supp)
    have hre : (-s * (t : ℂ)).re = -(s.re * t) := by
      simp [Complex.mul_re]
    rw [norm_mul, Complex.norm_exp, hre]
    have hexp : Real.exp (-(s.re * t)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    calc
      Real.exp (-(s.re * t)) * ‖f t‖ ≤ 1 * ‖f t‖ := by
        gcongr
      _ = ‖f t‖ := by simp

private theorem complexLaplaceTransform_real_eq_inv_mul_deriv
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    {s : ℝ} (hs : 0 < s) :
    complexLaplaceTransform f (s : ℂ)
      = (1 / (s : ℂ)) * complexLaplaceTransform (SchwartzMap.derivCLM ℂ ℂ f) (s : ℂ) := by
  have h_exp_integrable :
      IntegrableOn (fun x : ℝ => Complex.exp (-((s : ℂ) * (x : ℂ))) * deriv f x) (Set.Ioi 0) := by
    convert (complexLaplaceTransform_integrable_of_nonneg_re
      (SchwartzMap.derivCLM ℂ ℂ f)
      ((SchwartzMap.tsupport_derivCLM_subset (𝕜 := ℂ) (F := ℂ) f).trans hf_supp)
      (s : ℂ) hs.le).integrableOn using 1
    ext x
    rw [SchwartzMap.derivCLM_apply]
    congr 1
    ring_nf
  have h_deriv_exp_integrable :
      IntegrableOn
        (fun x : ℝ =>
          ((-(s : ℂ)) * Complex.exp (-((s : ℂ) * (x : ℂ)))) * f x) (Set.Ioi 0) := by
    have hint : Integrable (fun x : ℝ => Complex.exp (-((s : ℂ) * (x : ℂ))) * f x) := by
      simpa using complexLaplaceTransform_integrable_of_nonneg_re f hf_supp (s : ℂ) hs.le
    convert (hint.const_mul (-(s : ℂ))).integrableOn using 1
    ext x
    ring
  have h_zero :
      Tendsto (fun x : ℝ => Complex.exp (-((s : ℂ) * (x : ℂ))) * f x) (𝓝[>] 0) (𝓝 0) := by
    have h_exp :
        Tendsto (fun x : ℝ => Complex.exp (-((s : ℂ) * (x : ℂ)))) (𝓝[>] 0) (𝓝 1) := by
      have hcont : Continuous fun x : ℝ => Complex.exp (-((s : ℂ) * (x : ℂ))) := by
        fun_prop
      simpa [ContinuousWithinAt] using
        (hcont.continuousAt.continuousWithinAt :
          ContinuousWithinAt (fun x : ℝ => Complex.exp (-((s : ℂ) * (x : ℂ)))) (Set.Ioi 0) 0)
    have hf_zero' : Tendsto (fun x : ℝ => f x) (𝓝[>] 0) (𝓝 0) :=
      schwartz_tendsto_zero_nhdsWithin_right_of_support f hf_supp
    simpa using h_exp.mul hf_zero'
  have h_infty :
      Tendsto (fun x : ℝ => Complex.exp (-((s : ℂ) * (x : ℂ))) * f x) atTop (𝓝 0) := by
    have hf_top : Tendsto (fun x : ℝ => f x) atTop (𝓝 0) := by
      exact Tendsto.mono_left (SchwartzMap.tendsto_cocompact f) _root_.atTop_le_cocompact
    have hf_top_norm : Tendsto (fun x : ℝ => ‖f x‖) atTop (𝓝 0) := by
      simpa using (Tendsto.norm hf_top)
    have hexp_bdd :
        ∀ᶠ x : ℝ in atTop, ‖Complex.exp (-((s : ℂ) * (x : ℂ))) * f x‖ ≤ ‖f x‖ := by
      filter_upwards [Filter.eventually_ge_atTop 0] with x hx
      by_cases hfx : f x = 0
      · simp [hfx]
      · have hx_supp : x ∈ tsupport (f : ℝ → ℂ) := subset_tsupport _ hfx
        have hx_nonneg : 0 ≤ x := Set.mem_Ici.mp (hf_supp hx_supp)
        have hre : (-((s : ℂ) * (x : ℂ))).re = -(s * x) := by
          simp [Complex.mul_re]
        rw [norm_mul, Complex.norm_exp, hre]
        have hexp : Real.exp (-(s * x)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith)
        simpa using mul_le_of_le_one_left (norm_nonneg (f x)) hexp
    exact squeeze_zero_norm' hexp_bdd hf_top_norm
  have hparts :=
    MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
      (a := 0)
      (u := fun x : ℝ => Complex.exp (-((s : ℂ) * (x : ℂ))))
      (u' := fun x : ℝ => (-(s : ℂ)) * Complex.exp (-((s : ℂ) * (x : ℂ))))
      (v := fun x : ℝ => f x)
      (v' := fun x : ℝ => deriv f x)
      (fun x _ => by
        have hlin : HasDerivAt (fun t : ℝ => -((s : ℂ) * (t : ℂ))) (-(s : ℂ)) x := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            (((Complex.ofRealCLM.hasDerivAt).const_mul (s : ℂ)).neg : HasDerivAt _ _ x)
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (Complex.hasDerivAt_exp (-((s : ℂ) * (x : ℂ)))).comp x hlin)
      (fun x _ => f.hasDerivAt x)
      h_exp_integrable
      h_deriv_exp_integrable
      h_zero
      h_infty
  let G : ℝ → ℂ := fun x => Complex.exp (-((s : ℂ) * (x : ℂ))) * f x
  have hIoi_eq :
      ∫ x : ℝ in Set.Ioi 0, G x
        = complexLaplaceTransform f (s : ℂ) := by
    have hGsupport : tsupport G ⊆ Set.Ici 0 := by
      have hbase :
          tsupport G ⊆ tsupport (fun x : ℝ => f x) := by
        simpa [G] using
          (tsupport_mul_subset_right :
            tsupport (fun x : ℝ => Complex.exp (-((s : ℂ) * (x : ℂ))) * f x) ⊆
              tsupport (fun x : ℝ => f x))
      exact hbase.trans hf_supp
    have hIci :
        ∫ x : ℝ in Set.Ici 0, G x = ∫ x : ℝ in tsupport G, G x := by
      apply MeasureTheory.setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ici hGsupport
      intro x hx
      exact image_eq_zero_of_notMem_tsupport hx.2
    calc
      ∫ x : ℝ in Set.Ioi 0, G x = ∫ x : ℝ in Set.Ici 0, G x := by
        rw [← MeasureTheory.integral_Ici_eq_integral_Ioi]
      _ = ∫ x : ℝ in tsupport G, G x := hIci
      _ = ∫ x : ℝ, G x := MeasureTheory.setIntegral_tsupport (F := G) (ν := MeasureTheory.volume)
      _ = complexLaplaceTransform f (s : ℂ) := by
        simp [G, complexLaplaceTransform]
  let Gd : ℝ → ℂ := fun x => Complex.exp (-((s : ℂ) * (x : ℂ))) * deriv f x
  have hIoi_deriv_eq :
      ∫ x : ℝ in Set.Ioi 0, Gd x
        = complexLaplaceTransform (SchwartzMap.derivCLM ℂ ℂ f) (s : ℂ) := by
    have hGd_support : tsupport Gd ⊆ Set.Ici 0 := by
      simpa [Gd] using
        ((tsupport_mul_subset_right :
          tsupport (fun x : ℝ => Complex.exp (-((s : ℂ) * (x : ℂ))) * deriv f x) ⊆
            tsupport (fun x : ℝ => deriv f x)).trans
          ((SchwartzMap.tsupport_derivCLM_subset (𝕜 := ℂ) (F := ℂ) f).trans hf_supp))
    have hIci :
        ∫ x : ℝ in Set.Ici 0, Gd x = ∫ x : ℝ in tsupport Gd, Gd x := by
      apply MeasureTheory.setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ici hGd_support
      intro x hx
      exact image_eq_zero_of_notMem_tsupport hx.2
    calc
      ∫ x : ℝ in Set.Ioi 0, Gd x = ∫ x : ℝ in Set.Ici 0, Gd x := by
        rw [← MeasureTheory.integral_Ici_eq_integral_Ioi]
      _ = ∫ x : ℝ in tsupport Gd, Gd x := hIci
      _ = ∫ x : ℝ, Gd x := MeasureTheory.setIntegral_tsupport (F := Gd) (ν := MeasureTheory.volume)
      _ = complexLaplaceTransform (SchwartzMap.derivCLM ℂ ℂ f) (s : ℂ) := by
        rw [complexLaplaceTransform]
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with t
        dsimp [Gd]
        congr 1
        ring_nf
  have hs_ne : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hparts' :
      ∫ x : ℝ in Set.Ioi 0, Gd x = (s : ℂ) * ∫ x : ℝ in Set.Ioi 0, G x := by
    calc
      ∫ x : ℝ in Set.Ioi 0, Gd x
          = -∫ x : ℝ in Set.Ioi 0, ((-(s : ℂ)) * Complex.exp (-((s : ℂ) * (x : ℂ)))) * f x := by
              simpa [Gd] using hparts
      _ = -((-(s : ℂ)) * ∫ x : ℝ in Set.Ioi 0, G x) := by
            congr 1
            have hconst :
                ∫ x : ℝ in Set.Ioi 0, ((-(s : ℂ)) * Complex.exp (-((s : ℂ) * (x : ℂ)))) * f x
                  = (-(s : ℂ)) * ∫ x : ℝ in Set.Ioi 0, G x := by
                    simpa [G, mul_assoc] using
                      (MeasureTheory.integral_const_mul
                        (μ := MeasureTheory.volume.restrict (Set.Ioi 0))
                        (-(s : ℂ))
                        (fun x : ℝ => Complex.exp (-((s : ℂ) * (x : ℂ))) * f x))
            exact hconst
      _ = (s : ℂ) * ∫ x : ℝ in Set.Ioi 0, G x := by ring
  calc
    complexLaplaceTransform f (s : ℂ)
        = ∫ x : ℝ in Set.Ioi 0, G x := by
            simp [hIoi_eq]
    _ = (1 / (s : ℂ)) * ∫ x : ℝ in Set.Ioi 0, Gd x := by
          calc
            ∫ x : ℝ in Set.Ioi 0, G x = (1 / (s : ℂ)) * ((s : ℂ) * ∫ x : ℝ in Set.Ioi 0, G x) := by
              field_simp [hs_ne]
            _ = (1 / (s : ℂ)) * ∫ x : ℝ in Set.Ioi 0, Gd x := by rw [hparts']
    _ = (1 / (s : ℂ)) * complexLaplaceTransform (SchwartzMap.derivCLM ℂ ℂ f) (s : ℂ) := by
          rw [hIoi_deriv_eq]

private theorem complexLaplaceTransform_real_eq_inv_pow_mul_iteratedDeriv
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    {s : ℝ} (hs : 0 < s) (N : ℕ) :
    complexLaplaceTransform f (s : ℂ)
      = (1 / (s : ℂ)) ^ N * complexLaplaceTransform (iteratedDerivSchwartz N f) (s : ℂ) := by
  induction N with
  | zero =>
      simp [iteratedDerivSchwartz]
  | succ N ih =>
      have hN_supp :
          tsupport ((iteratedDerivSchwartz N f : SchwartzMap ℝ ℂ) : ℝ → ℂ) ⊆ Set.Ici 0 :=
        (tsupport_iteratedDerivSchwartz_subset N f).trans hf_supp
      calc
        complexLaplaceTransform f (s : ℂ)
            = (1 / (s : ℂ)) ^ N * complexLaplaceTransform (iteratedDerivSchwartz N f) (s : ℂ) := ih
        _ = (1 / (s : ℂ)) ^ N *
              ((1 / (s : ℂ)) *
                complexLaplaceTransform (iteratedDerivSchwartz (N + 1) f) (s : ℂ)) := by
              rw [complexLaplaceTransform_real_eq_inv_mul_deriv (iteratedDerivSchwartz N f) hN_supp hs]
              simp [iteratedDerivSchwartz]
        _ = (1 / (s : ℂ)) ^ (N + 1) *
              complexLaplaceTransform (iteratedDerivSchwartz (N + 1) f) (s : ℂ) := by
              simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]

private theorem complexLaplaceTransform_real_rapid_decay
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 1 ≤ s →
      ‖complexLaplaceTransform f (s : ℂ)‖ ≤ C * s ^ (-(N : ℤ)) := by
  let g : SchwartzMap ℝ ℂ := iteratedDerivSchwartz N f
  have hg_supp : tsupport (g : ℝ → ℂ) ⊆ Set.Ici 0 := by
    exact (tsupport_iteratedDerivSchwartz_subset N f).trans hf_supp
  let C0 : ℝ := ∫ t : ℝ, ‖g t‖
  refine ⟨C0 + 1, by positivity, ?_⟩
  intro s hs1
  have hs : 0 < s := lt_of_lt_of_le zero_lt_one hs1
  have hIntExpNorm :
      Integrable (fun t : ℝ => ‖Complex.exp (-((s : ℂ) * (t : ℂ))) * g t‖) := by
    simpa only [neg_mul] using
      ((complexLaplaceTransform_integrable_of_nonneg_re g hg_supp (s : ℂ) hs.le).norm :
        Integrable (fun t : ℝ => ‖Complex.exp (-((s : ℂ)) * (t : ℂ)) * g t‖))
  have hLg : ‖complexLaplaceTransform g (s : ℂ)‖ ≤ C0 := by
    calc
      ‖complexLaplaceTransform g (s : ℂ)‖
          ≤ ∫ t : ℝ, ‖Complex.exp (-((s : ℂ) * (t : ℂ))) * g t‖ := by
              simpa [complexLaplaceTransform] using
                (MeasureTheory.norm_integral_le_integral_norm
                  (fun t : ℝ => Complex.exp (-((s : ℂ) * (t : ℂ))) * g t))
      _ ≤ ∫ t : ℝ, ‖g t‖ := by
            refine MeasureTheory.integral_mono_ae
              hIntExpNorm
              g.integrable.norm
              (Filter.Eventually.of_forall fun t =>
                by simpa [neg_mul] using complexLaplaceKernel_norm_le_self g hg_supp (s := (s : ℂ)) hs.le t)
      _ = C0 := rfl
  have hpow :
      ‖((1 / (s : ℂ)) ^ N)‖ = s ^ (-(N : ℤ)) := by
    calc
      ‖((1 / (s : ℂ)) ^ N)‖ = ‖(1 / (s : ℂ))‖ ^ N := by rw [norm_pow]
      _ = (s⁻¹) ^ N := by
            simp [one_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hs)]
      _ = s ^ (-(N : ℤ)) := by
            simp [zpow_neg, zpow_natCast, inv_pow]
  calc
    ‖complexLaplaceTransform f (s : ℂ)‖
        = ‖((1 / (s : ℂ)) ^ N) * complexLaplaceTransform g (s : ℂ)‖ := by
            rw [complexLaplaceTransform_real_eq_inv_pow_mul_iteratedDeriv f hf_supp hs N]
    _ = ‖((1 / (s : ℂ)) ^ N)‖ * ‖complexLaplaceTransform g (s : ℂ)‖ := by
          rw [norm_mul]
    _ ≤ ‖((1 / (s : ℂ)) ^ N)‖ * C0 := by
          gcongr
    _ = C0 * s ^ (-(N : ℤ)) := by
          rw [hpow, mul_comm]
    _ ≤ (C0 + 1) * s ^ (-(N : ℤ)) := by
          have hz_nonneg : 0 ≤ s ^ (-(N : ℤ)) := by
            rw [zpow_neg, zpow_natCast]
            positivity
          nlinarith

private theorem complexLaplaceTransform_real_tendsto_at_zero
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0) :
    Tendsto (fun s : ℝ => complexLaplaceTransform f (s : ℂ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ t : ℝ, f t)) := by
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (bound := fun t : ℝ => ‖f t‖)
  · apply Filter.Eventually.of_forall
    intro s
    exact ((Complex.continuous_exp.comp
      ((continuous_const : Continuous (fun _ : ℝ => -(s : ℂ))).mul Complex.continuous_ofReal)).mul
      f.continuous).aestronglyMeasurable
  · have hmem : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin 0 (Set.Ioi 0) :=
      mem_nhdsWithin.mpr ⟨Set.Iio 1, isOpen_Iio, Set.mem_Iio.mpr zero_lt_one,
        fun s hs => Set.mem_Ioo.mpr ⟨hs.2, hs.1⟩⟩
    apply Filter.eventually_of_mem hmem
    intro s hs
    obtain ⟨hs_pos, _hs_lt⟩ := Set.mem_Ioo.mp hs
    apply Filter.Eventually.of_forall
    intro t
    simpa using complexLaplaceKernel_norm_le_self f hf_supp (s := (s : ℂ)) (by simpa using le_of_lt hs_pos) t
  · exact f.integrable.norm
  · apply Filter.Eventually.of_forall
    intro t
    have hcont : Continuous fun s : ℝ => Complex.exp (-((s : ℂ) * (t : ℂ))) * f t := by
      fun_prop
    have htend :
        Tendsto (fun s : ℝ => Complex.exp (-((s : ℂ) * (t : ℂ))) * f t)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (Complex.exp (-((0 : ℂ) * (t : ℂ))) * f t)) :=
      hcont.continuousAt.continuousWithinAt.tendsto
    simpa using htend

private theorem complexLaplaceTransform_weighted_real_tendsto_at_zero
    (N : ℕ)
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0) :
    Tendsto
      (fun s : ℝ => complexLaplaceTransform (weightedNegCoordPowSchwartz N f) (s : ℂ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ t : ℝ, (-(t : ℂ)) ^ N * f t)) := by
  simpa [weightedNegCoordPowSchwartz_apply] using
    (complexLaplaceTransform_real_tendsto_at_zero
      (weightedNegCoordPowSchwartz N f)
      (weightedNegCoordPowSchwartz_support N f hf_supp))

/-- The tempered functional pairing against `𝓕⁻¹ f`. -/
private noncomputable def fourierInvPairingCLM
    (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
  (SchwartzMap.integralCLM ℂ (MeasureTheory.volume : MeasureTheory.Measure ℝ)).comp
    (SchwartzMap.smulLeftCLM ℂ (fun t : ℝ => FourierTransform.fourierInv f t))

@[simp] private theorem fourierInvPairingCLM_apply
    (f φ : SchwartzMap ℝ ℂ) :
    fourierInvPairingCLM f φ =
      ∫ t : ℝ, FourierTransform.fourierInv f t * φ t := by
  rw [fourierInvPairingCLM, ContinuousLinearMap.comp_apply, SchwartzMap.integralCLM_apply]
  rw [SchwartzMap.smulLeftCLM_apply]
  · simp [smul_eq_mul]
  · fun_prop

/-- Positive-support Schwartz input gives one-sided Fourier support for the
inverse-Fourier pairing functional. This is the exact half-line spectral input
for the one-variable Section 4.3 Paley-Wiener step. -/
theorem fourierInvPairing_hasOneSidedFourierSupport
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0) :
    SCV.HasOneSidedFourierSupport (fourierInvPairingCLM f) := by
  intro φ hφ_supp
  rw [fourierInvPairingCLM_apply, SchwartzMap.integral_fourierInv_mul_eq]
  have hzero : ∀ x : ℝ, f x * φ x = 0 := by
    intro x
    by_cases hx : f x = 0
    · simp [hx]
    · have hx_mem : x ∈ tsupport (f : ℝ → ℂ) := subset_tsupport _ hx
      have hx_nonneg : 0 ≤ x := Set.mem_Ici.mp (hf_supp hx_mem)
      by_cases hφx : φ x = 0
      · simp [hφx]
      · have hx_neg : x < 0 := hφ_supp x (Function.mem_support.mpr hφx)
        exact (not_lt_of_ge hx_nonneg hx_neg).elim
  refine MeasureTheory.integral_eq_zero_of_ae ?_
  filter_upwards with x
  simp [hzero x]

/-- One-variable core of the current Stage-5 spectral route: if `f` has
positive-time support and `φ` has negative support, then the inverse-Fourier
pairing induced by `f` annihilates the Fourier transform of any pointwise
product `g * φ`.

This is not a new route or wrapper theorem. It is exactly the support-disjoint
Parseval step needed after the future time-convolution / spatial-factorization
rewrite: once the time-shift functional is rewritten into this one-variable
form, the vanishing is immediate from `integral_fourierInv_mul_eq`. -/
theorem fourierInvPairing_annihilates_FT_of_negSupport_product
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    (g φ : SchwartzMap ℝ ℂ)
    (hφ_supp : ∀ x ∈ Function.support (φ : ℝ → ℂ), x < 0) :
    fourierInvPairingCLM f
      ((SchwartzMap.fourierTransformCLM ℂ)
        ((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => g x)) φ)) = 0 := by
  have hprod_supp :
      ∀ x ∈ Function.support
        (((SchwartzMap.smulLeftCLM ℂ (fun y : ℝ => g y)) φ : SchwartzMap ℝ ℂ) : ℝ → ℂ),
        x < 0 := by
    intro x hx
    apply hφ_supp x
    apply Function.mem_support.mpr
    intro hφx
    apply hx
    rw [SchwartzMap.smulLeftCLM_apply_apply (F := ℂ) g.hasTemperateGrowth, hφx]
    simp
  exact
    (fourierInvPairing_hasOneSidedFourierSupport f hf_supp)
      (((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => g x)) φ)) hprod_supp

/-- Route-specific consumer of
`fourierInvPairing_annihilates_FT_of_negSupport_product`: every branch-`3b`
time slice coming from a positive-time Euclidean input has positive support, so
its inverse-Fourier pairing annihilates Fourier transforms of pointwise
products with a negative-support Schwartz factor.

This is the exact one-variable statement the later Stage-5 factorization will
need after rewriting the time-shift functional slice-by-slice; it keeps the
remaining blocker on the factorization step itself rather than on support
bookkeeping. -/
theorem fourierInvPairingCLM_partialFourierSpatial_timeSlice_annihilates_FT_of_negSupport_product
    {n : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (g χ : SchwartzMap ℝ ℂ)
    (hχ_supp : ∀ x ∈ Function.support (χ : ℝ → ℂ), x < 0) :
    fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          ((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => g x)) χ)) = 0 := by
  refine fourierInvPairing_annihilates_FT_of_negSupport_product
    (f := partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
      (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)
    (g := g) (φ := χ) ?_ hχ_supp
  exact tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
    (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ

/-- Honest one-variable Section 4.3 supplier: from positive-support Schwartz
input, obtain the Paley-Wiener upper-half-plane extension with the correct
distributional boundary value. -/
theorem complexLaplaceTransform_hasPaleyWienerExtension
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0) :
    ∃ F_ext : ℂ → ℂ,
      DifferentiableOn ℂ F_ext SCV.upperHalfPlane ∧
      (∀ η : ℝ, 0 < η →
        SCV.HasPolynomialGrowthOnLine (fun x => F_ext (↑x + ↑η * Complex.I))) ∧
      (∀ φ : SchwartzMap ℝ ℂ,
        Filter.Tendsto (fun η : ℝ => ∫ x : ℝ, F_ext (↑x + ↑η * Complex.I) * φ x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (∫ t : ℝ, FourierTransform.fourierInv f t * φ t))) := by
  simpa [fourierInvPairingCLM_apply] using
    SCV.paley_wiener_half_line
      (fourierInvPairingCLM f)
      (fourierInvPairing_hasOneSidedFourierSupport f hf_supp)

/-- On the positive imaginary axis, the canonical Fourier-Laplace extension of
the inverse-Fourier functional induced by `f` reproduces the raw one-sided
Laplace transform, with the built-in `2π` scaling from `SCV.paley_wiener_half_line`. -/
private theorem fourierLaplaceExt_fourierInvPairing_eq_complexLaplaceTransform
    (f : SchwartzMap ℝ ℂ)
    (hf_supp : tsupport (f : ℝ → ℂ) ⊆ Set.Ici 0)
    {η : ℝ} (hη : 0 < η) :
    SCV.fourierLaplaceExt
        (fourierInvPairingCLM f)
        (((2 * Real.pi * η : ℂ) * Complex.I))
        (by simpa [Complex.mul_im, hη.ne'] using mul_pos Real.two_pi_pos hη)
      = complexLaplaceTransform f ((2 * Real.pi * η : ℂ)) := by
  let ψ : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ (((2 * Real.pi * η : ℂ) * Complex.I))
      (by simpa [Complex.mul_im, hη.ne'] using mul_pos Real.two_pi_pos hη)
  have hψ_inv :
      FourierTransform.fourierInv ((SchwartzMap.fourierTransformCLM ℂ) ψ) = ψ := by
    simpa [ψ] using (FourierTransform.fourierInv_fourier_eq ψ)
  rw [SCV.fourierLaplaceExt_eq, fourierInvPairingCLM_apply, SchwartzMap.integral_fourierInv_mul_eq]
  rw [hψ_inv]
  change ∫ ξ : ℝ, f ξ * ψ ξ = ∫ t : ℝ, Complex.exp (-((2 * Real.pi * η : ℂ)) * (t : ℂ)) * f t
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with ξ
  by_cases hξ : f ξ = 0
  · simp [hξ]
  · have hξ_mem : ξ ∈ tsupport (f : ℝ → ℂ) := subset_tsupport _ hξ
    have hξ_nonneg : 0 ≤ ξ := Set.mem_Ici.mp (hf_supp hξ_mem)
    rw [show ψ ξ =
        SCV.schwartzPsiZ (((2 * Real.pi * η : ℂ) * Complex.I))
          (by simpa [Complex.mul_im, hη.ne'] using mul_pos Real.two_pi_pos hη) ξ by rfl]
    rw [SCV.schwartzPsiZ_apply, SCV.psiZ_eq_exp_of_nonneg hξ_nonneg]
    have hexp :
        Complex.exp (Complex.I * ((((2 * Real.pi * η : ℂ) * Complex.I)) * ξ)) =
          Complex.exp (-((2 * Real.pi * η : ℂ) * ξ)) := by
      congr 1
      ring_nf
      simp
    simpa [mul_assoc, mul_left_comm, mul_comm] using congrArg (fun z => f ξ * z) hexp

/-- Explicit `2π` normalization check for the standard Paley-Wiener kernel on
the positive imaginary axis: when the spectral boundary functional later
evaluates a test at `u / 2π`, the kernel becomes the plain Laplace weight
`e^{-ηu}` on the nonnegative half-axis. -/
private theorem schwartzPsiZ_two_pi_imagAxis_apply_div_two_pi
    {η u : ℝ} (hη : 0 < η) (hu : 0 ≤ u) :
    SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (η * Complex.I)))
        (by simpa [Complex.mul_im, hη.ne'] using mul_pos Real.two_pi_pos hη)
        (u / (2 * Real.pi)) =
      Complex.exp (-((η * u : ℝ) : ℂ)) := by
  rw [SCV.schwartzPsiZ_apply, SCV.psiZ_eq_exp_of_nonneg]
  · congr 1
    have hI :
        Complex.I * (((2 * Real.pi : ℂ) * (η * Complex.I))) =
          -(((2 * Real.pi * η : ℝ) : ℂ)) := by
      calc
        Complex.I * (((2 * Real.pi : ℂ) * (η * Complex.I)))
            = ((2 * Real.pi : ℂ) * (η : ℂ)) * (Complex.I * Complex.I) := by
                ring
        _ = -(((2 * Real.pi * η : ℝ) : ℂ)) := by
              simp [Complex.I_mul_I, mul_comm, mul_left_comm, mul_assoc]
    have hscalar :
        (((2 * Real.pi * η : ℝ) : ℂ)) * (((u / (2 * Real.pi) : ℝ) : ℂ)) =
          ((η * u : ℝ) : ℂ) := by
      exact_mod_cast (show (2 * Real.pi * η) * (u / (2 * Real.pi)) = η * u by
        field_simp [Real.pi_ne_zero])
    calc
      Complex.I * (((2 * Real.pi : ℂ) * (η * Complex.I))) * (((u / (2 * Real.pi) : ℝ) : ℂ))
          = -(((2 * Real.pi * η : ℝ) : ℂ)) * (((u / (2 * Real.pi) : ℝ) : ℂ)) := by
              rw [hI]
      _ = -((((2 * Real.pi * η : ℝ) : ℂ)) * (((u / (2 * Real.pi) : ℝ) : ℂ))) := by
            ring
      _ = -((η * u : ℝ) : ℂ) := by
            rw [hscalar]
  · exact div_nonneg hu Real.two_pi_pos.le

/-- The one-variable Paley-Wiener supplier applied to the actual branch-`3b`
positive-time time slice: on the positive imaginary axis, the canonical
Fourier-Laplace extension of the induced inverse-Fourier pairing reproduces the
raw one-sided Laplace transform of the slice itself. -/
theorem fourierLaplaceExt_partialFourierSpatial_timeSlice_eq_complexLaplaceTransform
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    {η : ℝ} (hη : 0 < η) :
    SCV.fourierLaplaceExt
        (fourierInvPairingCLM
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ))
        (((2 * Real.pi * η : ℂ) * Complex.I))
        (by simpa [Complex.mul_im, hη.ne'] using mul_pos Real.two_pi_pos hη)
      =
    complexLaplaceTransform
      (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
      ((2 * Real.pi * η : ℂ)) := by
  exact fourierLaplaceExt_fourierInvPairing_eq_complexLaplaceTransform
    (f := partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
    (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
      (d := d) (n := n) f r t ξ)
    hη

/-- The one-variable Paley-Wiener theorem, specialized to the actual branch-`3b`
positive-time time slice. This is the exact existential supplier that still
needs to be assembled into the global Section 4.3 transport map. -/
theorem partialFourierSpatial_timeSlice_hasPaleyWienerExtension
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    ∃ F_ext : ℂ → ℂ,
      DifferentiableOn ℂ F_ext SCV.upperHalfPlane ∧
      (∀ η : ℝ, 0 < η →
        SCV.HasPolynomialGrowthOnLine (fun x => F_ext (↑x + ↑η * Complex.I))) ∧
      (∀ φ : SchwartzMap ℝ ℂ,
        Filter.Tendsto (fun η : ℝ => ∫ x : ℝ, F_ext (↑x + ↑η * Complex.I) * φ x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (fourierInvPairingCLM
              (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
              φ))) := by
  simpa [fourierInvPairingCLM_apply] using
    complexLaplaceTransform_hasPaleyWienerExtension
      (f := partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
      (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
        (d := d) (n := n) f r t ξ)

/-- The canonical one-variable Section-4.3 upper-half-plane extension attached
to the actual branch-`3b` positive-time slice. This avoids arbitrary
`Classical.choose` packaging: it is exactly the scaled `SCV.fourierLaplaceExt`
that `paley_wiener_half_line` builds under the hood. -/
noncomputable def partialFourierSpatial_timeSliceCanonicalExtension
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    (w : ℂ) : ℂ :=
  if hw : 0 < w.im then
    SCV.fourierLaplaceExt
      (fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ))
      (((2 * Real.pi : ℂ) * w))
      (by
        have hmul : 0 < (2 * Real.pi) * w.im := mul_pos Real.two_pi_pos hw
        simpa [Complex.mul_im] using hmul)
  else
    0

/-- On the positive imaginary axis, the canonical slice extension reproduces
the raw one-sided Laplace transform of the branch-`3b` time slice. -/
theorem partialFourierSpatial_timeSliceCanonicalExtension_eq_complexLaplaceTransform
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    {η : ℝ} (hη : 0 < η) :
    partialFourierSpatial_timeSliceCanonicalExtension
        (d := d) (n := n) f r t ξ (η * Complex.I)
      =
    complexLaplaceTransform
      (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
      ((2 * Real.pi * η : ℂ)) := by
  have him : 0 < (η * Complex.I).im := by simpa using hη
  simp only [partialFourierSpatial_timeSliceCanonicalExtension, dif_pos him]
  have harg :
      ((2 * Real.pi : ℂ) * (η * Complex.I)) = ((2 * Real.pi * η : ℂ) * Complex.I) := by
    norm_num
    ring
  simpa [harg] using
    (fourierLaplaceExt_partialFourierSpatial_timeSlice_eq_complexLaplaceTransform
      (d := d) (n := n) f r t ξ hη)

/-- The one-variable Paley-Wiener Fourier-Laplace value at `2π i η` is the
same scalar as the Section-4.3 descended pairing against the corresponding
`ψ_Z` kernel. This is the local Lemma-8.4 atom used by the transported
time-interchange packets. -/
private theorem lemma84_oneSidedFunctional_fourierLaplaceExt_eq_descendedPsiZ
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (hT_supp : SCV.HasOneSidedFourierSupport T)
    {η : ℝ} (hη : 0 < η) :
    SCV.fourierLaplaceExt T
        (((2 * Real.pi * η : ℂ) * Complex.I))
        (by
          simpa [Complex.mul_im, hη.ne']
            using mul_pos Real.two_pi_pos hη) =
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        T hT_supp
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ
            (((2 * Real.pi * η : ℂ) * Complex.I))
            (by
              simpa [Complex.mul_im, hη.ne']
                using mul_pos Real.two_pi_pos hη))) := by
  rw [SCV.fourierLaplaceExt_eq]
  symm
  exact
    OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D_apply
      (T := T) (hT_supp := hT_supp)
      (f := SCV.schwartzPsiZ
        (((2 * Real.pi * η : ℂ) * Complex.I))
        (by
          simpa [Complex.mul_im, hη.ne']
            using mul_pos Real.two_pi_pos hη))

/-- On the positive imaginary axis, the canonical one-variable slice extension
is exactly the descended Section-4.3 Fourier pairing evaluated on the quotient
class of the same Paley-Wiener kernel `ψ_{2πiη}`. This is the first explicit
meeting point between the slice Paley-Wiener package and the current
Section-4.3 codomain on the actual `ψ`-family used in Phase C'. -/
private theorem
    partialFourierSpatial_timeSliceCanonicalExtension_imagAxis_eq_fourierPairingDescendsToSection43PositiveEnergy1D_psiZ
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    {η : ℝ} (hη : 0 < η) :
    partialFourierSpatial_timeSliceCanonicalExtension
        (d := d) (n := n) f r t ξ (η * Complex.I) =
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        (fourierInvPairingCLM
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ))
        (fourierInvPairing_hasOneSidedFourierSupport
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
          (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
            (d := d) (n := n) f r t ξ))
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ
            (((2 * Real.pi * η : ℂ) * Complex.I))
            (by
              simpa [Complex.mul_im, hη.ne']
                using mul_pos Real.two_pi_pos hη))) := by
  let T : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
    fourierInvPairingCLM
      (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
  let ψ : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi * η : ℂ) * Complex.I))
      (by
        simpa [Complex.mul_im, hη.ne']
          using mul_pos Real.two_pi_pos hη)
  have him : 0 < (η * Complex.I).im := by
    simpa using hη
  have hApply :
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
          T
          (fourierInvPairing_hasOneSidedFourierSupport
            (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
            (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
              (d := d) (n := n) f r t ξ))
          (section43PositiveEnergyQuotientMap1D ψ) =
        T ((SchwartzMap.fourierTransformCLM ℂ) ψ) := by
    simpa [T, ψ] using
      (OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D_apply
        (T := T)
        (hT_supp := fourierInvPairing_hasOneSidedFourierSupport
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
          (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
            (d := d) (n := n) f r t ξ))
        (f := ψ))
  rw [partialFourierSpatial_timeSliceCanonicalExtension, dif_pos him, SCV.fourierLaplaceExt_eq]
  have harg : ((2 * Real.pi : ℂ) * (η * Complex.I)) =
      (((2 * Real.pi * η : ℝ) : ℂ) * Complex.I) := by
    norm_num
    ring
  simpa [T, ψ, harg] using hApply.symm

private theorem partialFourierSpatial_timeSliceCanonicalExtension_differentiableOn
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    DifferentiableOn ℂ
      (partialFourierSpatial_timeSliceCanonicalExtension
        (d := d) (n := n) f r t ξ)
      SCV.upperHalfPlane := by
  let T :=
    fourierInvPairingCLM
      (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
  let Fcore : ℂ → ℂ := fun w =>
    if hw : 0 < w.im then
      SCV.fourierLaplaceExt T w hw
    else
      0
  let F : ℂ → ℂ := Fcore ∘ fun w => (((2 * Real.pi : ℝ) : ℂ) * w)
  have hF_diff : DifferentiableOn ℂ F SCV.upperHalfPlane := by
    have hmap : Set.MapsTo (fun w : ℂ => (((2 * Real.pi : ℝ) : ℂ) * w))
        SCV.upperHalfPlane SCV.upperHalfPlane := by
      intro z hz
      dsimp [SCV.upperHalfPlane] at hz ⊢
      simpa [Complex.mul_im, mul_assoc] using mul_pos Real.two_pi_pos hz
    have hmul :
        DifferentiableOn ℂ (fun w : ℂ => (((2 * Real.pi : ℝ) : ℂ) * w))
          SCV.upperHalfPlane := by
      intro z hz
      simpa using
        ((((differentiableAt_id : DifferentiableAt ℂ (fun y : ℂ => y) z).const_mul
          (((2 * Real.pi : ℝ) : ℂ))).differentiableWithinAt))
    simpa [F, Fcore] using (SCV.fourierLaplaceExt_differentiableOn T).comp hmul hmap
  have hEq : partialFourierSpatial_timeSliceCanonicalExtension
      (d := d) (n := n) f r t ξ = F := by
    funext w
    by_cases hw : 0 < w.im
    · have hscaled : 0 < ((((2 * Real.pi : ℝ) : ℂ) * w)).im := by
        simpa [Complex.mul_im, mul_assoc] using mul_pos Real.two_pi_pos hw
      show partialFourierSpatial_timeSliceCanonicalExtension
          (d := d) (n := n) f r t ξ w =
        Fcore ((((2 * Real.pi : ℝ) : ℂ) * w))
      change partialFourierSpatial_timeSliceCanonicalExtension
          (d := d) (n := n) f r t ξ w =
        if hw' : 0 < ((((2 * Real.pi : ℝ) : ℂ) * w)).im then
          SCV.fourierLaplaceExt T ((((2 * Real.pi : ℝ) : ℂ) * w)) hw'
        else 0
      rw [partialFourierSpatial_timeSliceCanonicalExtension, dif_pos hw, dif_pos hscaled]
      simp [T]
    · have hnotscaled : ¬ 0 < ((((2 * Real.pi : ℝ) : ℂ) * w)).im := by
        intro hscaled
        have hscaled' : 0 < (2 * Real.pi) * w.im := by
          simpa [Complex.mul_im, mul_assoc] using hscaled
        nlinarith [Real.two_pi_pos, hscaled']
      show partialFourierSpatial_timeSliceCanonicalExtension
          (d := d) (n := n) f r t ξ w =
        Fcore ((((2 * Real.pi : ℝ) : ℂ) * w))
      change partialFourierSpatial_timeSliceCanonicalExtension
          (d := d) (n := n) f r t ξ w =
        if hw' : 0 < ((((2 * Real.pi : ℝ) : ℂ) * w)).im then
          SCV.fourierLaplaceExt T ((((2 * Real.pi : ℝ) : ℂ) * w)) hw'
        else 0
      rw [partialFourierSpatial_timeSliceCanonicalExtension, dif_neg hw, dif_neg hnotscaled]
  rw [hEq]
  exact hF_diff

/-- The actual branch-`3b` time slice, packaged as the one-variable Section 4.3
positive-time test input. -/
private noncomputable def partialFourierSpatial_timeSliceTest
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    ↥(OSReconstruction.euclideanPositiveTimeTest1D) :=
  ⟨partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ,
    tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
      (d := d) (n := n) f r t ξ⟩

/-- The quotient-side descended pairing for the actual branch-`3b` time slice.
This is the first direct bridge from the existing slice-level analytic package
to the new Section 4.3 transport codomain. -/
private theorem fourierPairingDescendsToSection43PositiveEnergy1D_partialFourierSpatial_timeSlice
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n)
    (r : Fin n) (t : Fin n → ℝ)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        (fourierInvPairingCLM
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ))
        (fourierInvPairing_hasOneSidedFourierSupport
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
          (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
            (d := d) (n := n) f r t ξ))
        (OSReconstruction.os1TransportOneVar
          (partialFourierSpatial_timeSliceTest (d := d) (n := n) f r t ξ)) =
      fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ)) := by
  simpa [partialFourierSpatial_timeSliceTest] using
    (OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D_os1TransportOneVar
      (T := fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ))
      (hT_supp := fourierInvPairing_hasOneSidedFourierSupport
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) f.1 r t ξ)
        (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
          (d := d) (n := n) f r t ξ))
      (f := partialFourierSpatial_timeSliceTest (d := d) (n := n) f r t ξ))

/-- If two ambient Schwartz tests agree on the Section 4.3 positive-energy
region, then their partial spatial Fourier transforms agree at every time
vector with nonnegative coordinates. -/
private theorem partialFourierSpatial_fun_eq_of_eqOn_section43PositiveEnergyRegion
    {n : ℕ} {f g : SchwartzNPoint d n}
    (hfg :
      Set.EqOn (f : NPointDomain d n → ℂ) (g : NPointDomain d n → ℂ)
        (section43PositiveEnergyRegion d n))
    (t : Fin n → ℝ)
    (ht : ∀ i : Fin n, 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    partialFourierSpatial_fun (d := d) (n := n) f (t, ξ) =
      partialFourierSpatial_fun (d := d) (n := n) g (t, ξ) := by
  rw [partialFourierSpatial_fun_eq_integral (d := d) (n := n) f (t, ξ)]
  rw [partialFourierSpatial_fun_eq_integral (d := d) (n := n) g (t, ξ)]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with η
  have hregion :
      (nPointTimeSpatialCLE (d := d) n).symm (t, η) ∈
        section43PositiveEnergyRegion d n := by
    intro i
    simpa [nPointTimeSpatialCLE] using ht i
  have hval :
      nPointTimeSpatialSchwartzCLE (d := d) (n := n) f (t, η) =
        nPointTimeSpatialSchwartzCLE (d := d) (n := n) g (t, η) := by
    simpa [nPointTimeSpatialSchwartzCLE, nPointTimeSpatialCLE,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using hfg hregion
  simp [hval]

/-- If an ambient transformed-image representative `φ` and a positive-time
preimage `f` define the same Section 4.3 quotient class, then freezing all but
one time variable with nonnegative background times gives the same one-variable
slice on `[0,∞)`. This is the first honest ambient-representative bridge
needed by the corrected Stage-5 theorem surface. -/
private theorem partialFourierSpatial_timeSlice_eqOn_nonneg_of_repr_eq_transport
    {n : ℕ}
    {φ : SchwartzNPoint d n}
    {f : euclideanPositiveTimeSubmodule (d := d) n}
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (r : Fin n) (t : Fin n → ℝ)
    (ht : ∀ i : Fin n, i ≠ r → 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    Set.EqOn
      ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ r t ξ :
          SchwartzMap ℝ ℂ) : ℝ → ℂ)
      ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ :
            SchwartzMap ℝ ℂ) : ℝ → ℂ)
      (Set.Ici (0 : ℝ)) := by
  have hregion :
      Set.EqOn (φ : NPointDomain d n → ℂ)
        ((f : euclideanPositiveTimeSubmodule (d := d) n) :
          NPointDomain d n → ℂ)
        (section43PositiveEnergyRegion d n) := by
    have hq :
        section43PositiveEnergyQuotientMap (d := d) n φ =
          section43PositiveEnergyQuotientMap (d := d) n f.1 := by
      simpa [os1TransportComponent_apply] using hφf
    exact eqOn_region_of_section43PositiveEnergyQuotientMap_eq
      (d := d) (n := n) (f := φ) (g := f.1) hq
  intro s hs
  have hnonneg : ∀ i : Fin n, 0 ≤ Function.update t r s i := by
    intro i
    by_cases hi : i = r
    · subst hi
      simpa using hs
    · rw [Function.update_of_ne hi]
      exact ht i hi
  simpa [partialFourierSpatial_timeSliceSchwartz] using
    partialFourierSpatial_fun_eq_of_eqOn_section43PositiveEnergyRegion
      (d := d) (n := n) hregion (Function.update t r s) hnonneg ξ

/-- Zero-left branch of the Section-4.3 representative bridge. For `n = 0`,
the positive-energy region condition is vacuous, so quotient equality already
gives pointwise equality of the ambient representative and its positive-time
preimage. -/
private theorem section43_zero_left_repr_eq_transport_pointwise
    {φ : SchwartzNPoint d 0}
    {f : euclideanPositiveTimeSubmodule (d := d) 0}
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) 0 φ =
        os1TransportComponent d 0 f) :
    φ = (EuclideanPositiveTimeComponent.ofSubmodule f).1 := by
  ext x
  have hq :
      section43PositiveEnergyQuotientMap (d := d) 0 φ =
        section43PositiveEnergyQuotientMap (d := d) 0 f.1 := by
    simpa [os1TransportComponent_apply] using hφf
  have hEqOn :
      Set.EqOn (φ : NPointDomain d 0 → ℂ) (f.1 : NPointDomain d 0 → ℂ)
        (section43PositiveEnergyRegion d 0) :=
    eqOn_region_of_section43PositiveEnergyQuotientMap_eq
      (d := d) (n := 0) hq
  exact hEqOn (by intro i; exact Fin.elim0 i)

/-- Therefore the one-variable Section 4.3 quotient class of the ambient slice
is the same as the transport slice class of its positive-time preimage. This is
the direct current-code bridge from an ambient transformed-image representative
to the one-variable quotient theorem used later in the Stage-5 adapter. -/
private theorem section43PositiveEnergyQuotientMap1D_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport
    {n : ℕ}
    {φ : SchwartzNPoint d n}
    {f : euclideanPositiveTimeSubmodule (d := d) n}
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (r : Fin n) (t : Fin n → ℝ)
    (ht : ∀ i : Fin n, i ≠ r → 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    section43PositiveEnergyQuotientMap1D
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ r t ξ) =
      os1TransportOneVar
        (partialFourierSpatial_timeSliceTest (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ) := by
  apply section43PositiveEnergyQuotientMap1D_eq_of_eqOn_nonneg
  exact partialFourierSpatial_timeSlice_eqOn_nonneg_of_repr_eq_transport
    (d := d) (n := n) hφf r t ht ξ

/-- General one-variable descended-pairing form of the same bridge: once an
ambient representative `φ` and a positive-time preimage `f` determine the same
multivariate Section-4.3 class, every one-sided Fourier-support functional sees
the same one-variable quotient class on the corresponding time slice. This is
the real theorem surface needed later when the pairing functional is induced by
the opposite factor's slice rather than by the same slice. -/
private theorem fourierPairingDescendsToSection43PositiveEnergy1D_eq_of_repr_eq_transport
    {n : ℕ}
    {φ : SchwartzNPoint d n}
    {f : euclideanPositiveTimeSubmodule (d := d) n}
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (hT_supp : SCV.HasOneSidedFourierSupport T)
    (r : Fin n) (t : Fin n → ℝ)
    (ht : ∀ i : Fin n, i ≠ r → 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    fourierPairingDescendsToSection43PositiveEnergy1D T hT_supp
        (section43PositiveEnergyQuotientMap1D
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ r t ξ)) =
      fourierPairingDescendsToSection43PositiveEnergy1D T hT_supp
        (os1TransportOneVar
          (partialFourierSpatial_timeSliceTest (d := d) (n := n)
            (EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ)) := by
  rw [section43PositiveEnergyQuotientMap1D_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport
    (d := d) (n := n) hφf r t ht ξ]

/-- Scalar descended-pairing form of the same bridge: if an ambient
transformed-image representative `φ` and a positive-time preimage `f` define
the same multivariate Section 4.3 quotient class, then the one-variable
descended Fourier pairing attached to the positive-time slice of `f` already
recovers the quotient class of the ambient slice of `φ`. This is the exact
current-code scalar ingredient later needed inside the Lemma-4.2 matrix-element
adapter. -/
private theorem fourierPairingDescendsToSection43PositiveEnergy1D_repr_partialFourierSpatial_timeSlice
    {n : ℕ}
    {φ : SchwartzNPoint d n}
    {f : euclideanPositiveTimeSubmodule (d := d) n}
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (r : Fin n) (t : Fin n → ℝ)
    (ht : ∀ i : Fin n, i ≠ r → 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        (fourierInvPairingCLM
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
            (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ))
        (fourierInvPairing_hasOneSidedFourierSupport
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
            (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)
          (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
            (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ))
        (section43PositiveEnergyQuotientMap1D
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ r t ξ)) =
      fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
            (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)) := by
  rw [fourierPairingDescendsToSection43PositiveEnergy1D_eq_of_repr_eq_transport
    (d := d) (n := n) hφf
    (T := fourierInvPairingCLM
      (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
        (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ))
    (hT_supp := fourierInvPairing_hasOneSidedFourierSupport
      (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
        (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)
      (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
        (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ))
    r t ht ξ]
  exact fourierPairingDescendsToSection43PositiveEnergy1D_partialFourierSpatial_timeSlice
    (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ

/-- Wrapper-free scalar form of the same bridge: for the one-variable pairing
functional induced by the positive-time slice of `f`, the Fourier-side pairing
against the ambient slice of `φ` already equals the same pairing against the
actual positive-time slice. This is the scalar theorem-surface that the later
Lemma-4.2 adapter should consume directly, without reintroducing quotient
wrappers in its statement. -/
theorem fourierInvPairingCLM_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport
    {n : ℕ}
    {φ : SchwartzNPoint d n}
    {f : euclideanPositiveTimeSubmodule (d := d) n}
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (r : Fin n) (t : Fin n → ℝ)
    (ht : ∀ i : Fin n, i ≠ r → 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ r t ξ)) =
      fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
            (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)) := by
  have hleft :
      fourierPairingDescendsToSection43PositiveEnergy1D
          (fourierInvPairingCLM
            (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
              (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ))
          (fourierInvPairing_hasOneSidedFourierSupport
            (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
              (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)
            (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
              (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ))
          (section43PositiveEnergyQuotientMap1D
            (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ r t ξ)) =
        fourierInvPairingCLM
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
            (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)
          ((SchwartzMap.fourierTransformCLM ℂ)
            (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ r t ξ)) := by
    simpa using
      (fourierPairingDescendsToSection43PositiveEnergy1D_apply
        (T := fourierInvPairingCLM
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
            (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ))
        (hT_supp := fourierInvPairing_hasOneSidedFourierSupport
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
            (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)
          (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
            (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ))
        (f := partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ r t ξ))
  calc
    fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ r t ξ)) =
      fourierPairingDescendsToSection43PositiveEnergy1D
          (fourierInvPairingCLM
            (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
              (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ))
          (fourierInvPairing_hasOneSidedFourierSupport
            (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
              (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)
            (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
              (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ))
          (section43PositiveEnergyQuotientMap1D
            (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ r t ξ)) := by
        symm
        exact hleft
    _ =
      fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
            (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ)) := by
        exact fourierPairingDescendsToSection43PositiveEnergy1D_repr_partialFourierSpatial_timeSlice
          (d := d) (n := n) hφf r t ht ξ

/-- Direct kernel form of the same slice bridge: under the Section-4.3
quotient-class hypothesis, the ambient-minus-preimage one-variable slice lies
in the kernel of every one-sided Fourier-support pairing. This is the exact
zero statement later needed in the Lemma-4.2 route, without reintroducing
quotient wrappers. -/
theorem oneSidedFourierSupport_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport
    {n : ℕ}
    {φ : SchwartzNPoint d n}
    {f : euclideanPositiveTimeSubmodule (d := d) n}
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (hT_supp : SCV.HasOneSidedFourierSupport T)
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (r : Fin n) (t : Fin n → ℝ)
    (ht : ∀ i : Fin n, i ≠ r → 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    T ((SchwartzMap.fourierTransformCLM ℂ)
      ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ r t ξ) -
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ))) = 0 := by
  refine SCV.fourier_pairing_vanishes_of_eqOn_nonneg
    (T := T) (hT_supp := hT_supp) ?_
  intro s hs
  have hslice :
      (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ r t ξ : ℝ → ℂ) s =
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ : ℝ → ℂ) s :=
    partialFourierSpatial_timeSlice_eqOn_nonneg_of_repr_eq_transport
      (d := d) (n := n) hφf r t ht ξ hs
  simp [hslice]

/-- Concrete scalar specialization of
`oneSidedFourierSupport_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport`:
the one-variable pairing induced by any positive-time slice on the opposite
factor already kills the ambient-minus-preimage slice difference. This is the
exact "each slice pairing vanishes" statement later consumed by the
matrix-element factorization step. -/
theorem fourierInvPairingCLM_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport
    {n m : ℕ}
    {φ : SchwartzNPoint d n}
    {f : euclideanPositiveTimeSubmodule (d := d) n}
    {g : euclideanPositiveTimeSubmodule (d := d) m}
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (rφ : Fin n) (tφ : Fin n → ℝ)
    (htφ : ∀ i : Fin n, i ≠ rφ → 0 ≤ tφ i)
    (ξφ : EuclideanSpace ℝ (Fin n × Fin d))
    (rψ : Fin m) (tψ : Fin m → ℝ)
    (htψ : ∀ i : Fin m, i ≠ rψ → 0 ≤ tψ i)
    (ξψ : EuclideanSpace ℝ (Fin m × Fin d)) :
    fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := m)
          (EuclideanPositiveTimeComponent.ofSubmodule g).1 rψ tψ ξψ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ rφ tφ ξφ) -
            (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
              (EuclideanPositiveTimeComponent.ofSubmodule f).1 rφ tφ ξφ))) = 0 := by
  exact
    oneSidedFourierSupport_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport
      (d := d)
      (T := fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := m)
          (EuclideanPositiveTimeComponent.ofSubmodule g).1 rψ tψ ξψ))
      (hT_supp := fourierInvPairing_hasOneSidedFourierSupport
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := m)
          (EuclideanPositiveTimeComponent.ofSubmodule g).1 rψ tψ ξψ)
        (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
          (d := d) (n := m) (EuclideanPositiveTimeComponent.ofSubmodule g) rψ tψ ξψ))
      hφf rφ tφ htφ ξφ

/-- Fourier-pairing symmetry on Fourier-transformed inputs: the slice pairing
induced by `f` and evaluated on `𝓕 g` is the same scalar as the opposite
pairing induced by `g` and evaluated on `𝓕 f`. This is the algebraic
commutativity step later used to move the Section-4.3 descended pairing from
one side of the Lemma-4.2 shell to the other without introducing any new
analytic content. -/
private theorem fourierInvPairingCLM_fourierTransform_symm
    (f g : SchwartzMap ℝ ℂ) :
    fourierInvPairingCLM f ((SchwartzMap.fourierTransformCLM ℂ) g) =
      fourierInvPairingCLM g ((SchwartzMap.fourierTransformCLM ℂ) f) := by
  rw [fourierInvPairingCLM_apply, fourierInvPairingCLM_apply]
  rw [SchwartzMap.integral_fourierInv_mul_eq, SchwartzMap.integral_fourierInv_mul_eq]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with x
  simp [mul_comm]

/-- Opposite-factor scalar pairing bridge on the corrected Stage-5 surface: if
ambient representatives `φ, ψ` come from positive-time preimages `f, g`, then
the one-variable Fourier pairing induced by the positive-time slice of `g`
against the ambient slice of `φ` already agrees with the opposite pairing
induced by the positive-time slice of `f` against the ambient slice of `ψ`.

This is a genuine current-code ingredient for the later Lemma-4.2 adapter:
both pairing functionals come from positive-time slices, so the descended
pairing theorems apply on each side, and the middle equality is just the
Fourier-pairing symmetry above. -/
theorem fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport
    {n m : ℕ}
    {φ : SchwartzNPoint d n}
    {ψ : SchwartzNPoint d m}
    {f : euclideanPositiveTimeSubmodule (d := d) n}
    {g : euclideanPositiveTimeSubmodule (d := d) m}
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    (rφ : Fin n) (tφ : Fin n → ℝ)
    (htφ : ∀ i : Fin n, i ≠ rφ → 0 ≤ tφ i)
    (ξφ : EuclideanSpace ℝ (Fin n × Fin d))
    (rψ : Fin m) (tψ : Fin m → ℝ)
    (htψ : ∀ i : Fin m, i ≠ rψ → 0 ≤ tψ i)
    (ξψ : EuclideanSpace ℝ (Fin m × Fin d)) :
    fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := m)
          (EuclideanPositiveTimeComponent.ofSubmodule g).1 rψ tψ ξψ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ rφ tφ ξφ)) =
      fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f).1 rφ tφ ξφ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          (partialFourierSpatial_timeSliceSchwartz (d := d) (n := m) ψ rψ tψ ξψ)) := by
  let φSlice :=
    partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ rφ tφ ξφ
  let ψSlice :=
    partialFourierSpatial_timeSliceSchwartz (d := d) (n := m) ψ rψ tψ ξψ
  let fSlice :=
    partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
      (EuclideanPositiveTimeComponent.ofSubmodule f).1 rφ tφ ξφ
  let gSlice :=
    partialFourierSpatial_timeSliceSchwartz (d := d) (n := m)
      (EuclideanPositiveTimeComponent.ofSubmodule g).1 rψ tψ ξψ
  have hleft :
      fourierInvPairingCLM gSlice ((SchwartzMap.fourierTransformCLM ℂ) φSlice) =
        fourierInvPairingCLM gSlice ((SchwartzMap.fourierTransformCLM ℂ) fSlice) := by
    simpa [φSlice, fSlice, gSlice] using
      (fourierPairingDescendsToSection43PositiveEnergy1D_eq_of_repr_eq_transport
        (d := d) (n := n) hφf
        (T := fourierInvPairingCLM gSlice)
        (hT_supp := fourierInvPairing_hasOneSidedFourierSupport gSlice
          (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
            (d := d) (n := m) (EuclideanPositiveTimeComponent.ofSubmodule g)
            rψ tψ ξψ))
        rφ tφ htφ ξφ)
  have hright :
      fourierInvPairingCLM fSlice ((SchwartzMap.fourierTransformCLM ℂ) ψSlice) =
        fourierInvPairingCLM fSlice ((SchwartzMap.fourierTransformCLM ℂ) gSlice) := by
    simpa [ψSlice, fSlice, gSlice] using
      (fourierPairingDescendsToSection43PositiveEnergy1D_eq_of_repr_eq_transport
        (d := d) (n := m) hψg
        (T := fourierInvPairingCLM fSlice)
        (hT_supp := fourierInvPairing_hasOneSidedFourierSupport fSlice
          (tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
            (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule f)
            rφ tφ ξφ))
        rψ tψ htψ ξψ)
  calc
    fourierInvPairingCLM gSlice ((SchwartzMap.fourierTransformCLM ℂ) φSlice) =
      fourierInvPairingCLM gSlice ((SchwartzMap.fourierTransformCLM ℂ) fSlice) := hleft
    _ =
      fourierInvPairingCLM fSlice ((SchwartzMap.fourierTransformCLM ℂ) gSlice) := by
        exact fourierInvPairingCLM_fourierTransform_symm gSlice fSlice
    _ =
      fourierInvPairingCLM fSlice ((SchwartzMap.fourierTransformCLM ℂ) ψSlice) := by
        symm
        exact hright

/-- Opposite-factor kernel form of the same bridge: once ambient
representatives `φ, ψ` come from positive-time preimages `f, g`, the
one-variable pairing induced by the positive-time slice of `f` already kills
the ambient-minus-preimage slice difference on the opposite factor.

This is the scalar zero theorem that the later Stage-5 spatial-Fourier
factorization can consume directly when the surviving slice pairing happens to
land on the opposite side. -/
theorem fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport
    {n m : ℕ}
    {φ : SchwartzNPoint d n}
    {ψ : SchwartzNPoint d m}
    {f : euclideanPositiveTimeSubmodule (d := d) n}
    {g : euclideanPositiveTimeSubmodule (d := d) m}
    (hφf :
      section43PositiveEnergyQuotientMap (d := d) n φ =
        os1TransportComponent d n f)
    (hψg :
      section43PositiveEnergyQuotientMap (d := d) m ψ =
        os1TransportComponent d m g)
    (rφ : Fin n) (tφ : Fin n → ℝ)
    (htφ : ∀ i : Fin n, i ≠ rφ → 0 ≤ tφ i)
    (ξφ : EuclideanSpace ℝ (Fin n × Fin d))
    (rψ : Fin m) (tψ : Fin m → ℝ)
    (htψ : ∀ i : Fin m, i ≠ rψ → 0 ≤ tψ i)
    (ξψ : EuclideanSpace ℝ (Fin m × Fin d)) :
    fourierInvPairingCLM
        (partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f).1 rφ tφ ξφ)
        ((SchwartzMap.fourierTransformCLM ℂ)
          ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := m) ψ rψ tψ ξψ) -
            (partialFourierSpatial_timeSliceSchwartz (d := d) (n := m)
              (EuclideanPositiveTimeComponent.ofSubmodule g).1 rψ tψ ξψ))) = 0 := by
  let φSlice :=
    partialFourierSpatial_timeSliceSchwartz (d := d) (n := n) φ rφ tφ ξφ
  let ψSlice :=
    partialFourierSpatial_timeSliceSchwartz (d := d) (n := m) ψ rψ tψ ξψ
  let fSlice :=
    partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
      (EuclideanPositiveTimeComponent.ofSubmodule f).1 rφ tφ ξφ
  let gSlice :=
    partialFourierSpatial_timeSliceSchwartz (d := d) (n := m)
      (EuclideanPositiveTimeComponent.ofSubmodule g).1 rψ tψ ξψ
  have hleft_zero :
      fourierInvPairingCLM gSlice
          ((SchwartzMap.fourierTransformCLM ℂ) (φSlice - fSlice)) = 0 := by
    simpa [φSlice, fSlice, gSlice] using
      (fourierInvPairingCLM_partialFourierSpatial_timeSlice_sub_eq_zero_of_repr_eq_transport
        (d := d) (n := n) (m := m) (φ := φ) (f := f) (g := g)
        hφf rφ tφ htφ ξφ rψ tψ htψ ξψ)
  have hleft :
      fourierInvPairingCLM gSlice ((SchwartzMap.fourierTransformCLM ℂ) φSlice) =
        fourierInvPairingCLM gSlice ((SchwartzMap.fourierTransformCLM ℂ) fSlice) := by
    exact sub_eq_zero.mp (by simpa [map_sub] using hleft_zero)
  have hopposite :
      fourierInvPairingCLM gSlice ((SchwartzMap.fourierTransformCLM ℂ) φSlice) =
        fourierInvPairingCLM fSlice ((SchwartzMap.fourierTransformCLM ℂ) ψSlice) := by
    simpa [φSlice, ψSlice, fSlice, gSlice] using
      (fourierInvPairingCLM_opposite_partialFourierSpatial_timeSlice_eq_of_repr_eq_transport
        (d := d) (n := n) (m := m) (φ := φ) (ψ := ψ) (f := f) (g := g)
        hφf hψg rφ tφ htφ ξφ rψ tψ htψ ξψ)
  have hsymm :
      fourierInvPairingCLM gSlice ((SchwartzMap.fourierTransformCLM ℂ) fSlice) =
        fourierInvPairingCLM fSlice ((SchwartzMap.fourierTransformCLM ℂ) gSlice) := by
    exact fourierInvPairingCLM_fourierTransform_symm gSlice fSlice
  have hmain :
      fourierInvPairingCLM fSlice ((SchwartzMap.fourierTransformCLM ℂ) ψSlice) =
        fourierInvPairingCLM fSlice ((SchwartzMap.fourierTransformCLM ℂ) gSlice) := by
    calc
      fourierInvPairingCLM fSlice ((SchwartzMap.fourierTransformCLM ℂ) ψSlice) =
        fourierInvPairingCLM gSlice ((SchwartzMap.fourierTransformCLM ℂ) φSlice) := by
          symm
          exact hopposite
      _ =
        fourierInvPairingCLM gSlice ((SchwartzMap.fourierTransformCLM ℂ) fSlice) := hleft
      _ =
        fourierInvPairingCLM fSlice ((SchwartzMap.fourierTransformCLM ℂ) gSlice) := hsymm
  exact sub_eq_zero.mp (by simpa [map_sub] using sub_eq_zero.mpr hmain)

/-- Concrete positive-time `ξ`-shift shell on the actual reconstructed
continuation kernel `bvt_F`: on positive real times, the Euclidean/OS matrix
element for a positive-time pair is exactly the `ξ`-shift integral of `bvt_F`.

This is just the current-code specialization of
`schwinger_simpleTensor_timeShift_eq_xiShift` to the actual kernel used in the
Stage-5 positivity route. It removes one more layer of generic witness
bookkeeping before the remaining Lemma-4.2 boundary-value step. -/
private theorem bvt_F_osConjTensorProduct_timeShift_eq_xiShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (t : ℝ) (ht : 0 < t) :
    OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
      (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))) =
      ∫ y : NPointDomain d (n + m),
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
          (f.osConjTensorProduct g) y := by
  exact schwinger_simpleTensor_timeShift_eq_xiShift
    (d := d) (OS := OS) (hm := hm) (Ψ := bvt_F OS lgc (n + m))
    (hΨ_euclid := bvt_euclidean_restriction (d := d) OS lgc (n + m))
    (f := f) (hf_ord := hf_ord) (g := g) (hg_ord := hg_ord) (t := t) ht

/-- Concrete ambient `ξ`-shift shell on the actual reconstructed continuation
kernel `bvt_F`: moving the positive real right-time shift from the ambient
Wightman-side test tensor to the continuation variable produces the same
`ξ`-shift integral.

Together with `bvt_F_osConjTensorProduct_timeShift_eq_xiShift`, this isolates
the remaining Stage-5 content to the one-variable boundary-value / time-variable
interchange, not further configuration-space shell algebra. -/
private theorem bvt_F_conjTensorProduct_timeShift_eq_xiShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m) (t : ℝ) :
    ∫ x : NPointDomain d (n + m),
      bvt_F OS lgc (n + m) (fun i => wickRotatePoint (x i)) *
        (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) x =
      ∫ y : NPointDomain d (n + m),
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
          (φ.conjTensorProduct ψ) y := by
  simpa using
    (simpleTensor_timeShift_integral_eq_xiShift_conj
      (d := d) (n := n) (m := m) (hm := hm)
      (f := φ) (g := ψ) (t := t) (Ψ := bvt_F OS lgc (n + m)))

/-- Canonical-shell version of `bvt_F_conjTensorProduct_timeShift_eq_xiShift`:
moving the positive real right-time shift from the ambient Wightman-side test
tensor to the continuation variable on the exact boundary-value shell
`x + ε η₀ i` produces the corresponding raw `ξ`-shift shell.

This is the current Step-2 configuration-space rewrite for Lemma 4.2. Unlike
`bvt_F_conjTensorProduct_timeShift_eq_xiShift`, it works directly on the
forward-cone boundary-value shell that appears in `bvt_boundary_values`. -/
private theorem bvt_F_canonical_conjTensorProduct_timeShift_eq_xiShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (t ε : ℝ) :
    ∫ x : NPointDomain d (n + m),
      bvt_F OS lgc (n + m) (fun k μ =>
        ↑(x k μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I) *
        (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) x =
      ∫ y : NPointDomain d (n + m),
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun k μ =>
              ↑(y k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I)
            (t : ℂ)) *
          (φ.conjTensorProduct ψ) y := by
  let j : Fin (n + m) := ⟨n, Nat.lt_add_of_pos_right hm⟩
  let Ψ : (Fin (n + m) → Fin (d + 1) → ℂ) → ℂ := fun z =>
    bvt_F OS lgc (n + m) (fun k μ =>
      (if μ = 0 then (-Complex.I) * z k μ else z k μ) +
        ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I)
  calc
    ∫ x : NPointDomain d (n + m),
        bvt_F OS lgc (n + m) (fun k μ =>
          ↑(x k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I) *
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) x
      =
        ∫ x : NPointDomain d (n + m),
          Ψ (fun i => wickRotatePoint (x i)) *
            (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) x := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with x
          have hshell :
              Ψ (fun i => wickRotatePoint (x i)) =
                bvt_F OS lgc (n + m) (fun k μ =>
                  ↑(x k μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I) := by
            unfold Ψ
            congr 1
            ext k μ
            by_cases hμ : μ = 0
            · subst hμ
              simp [wickRotatePoint]
              calc
                -(Complex.I * (Complex.I * ↑(x k 0))) =
                    -((Complex.I * Complex.I) * ↑(x k 0)) := by ring
                _ = -((-1 : ℂ) * ↑(x k 0)) := by rw [Complex.I_mul_I]
                _ = ↑(x k 0) := by ring
            · simp [wickRotatePoint, hμ]
          rw [hshell]
    _ =
        ∫ y : NPointDomain d (n + m),
          Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (φ.conjTensorProduct ψ) y := by
          exact simpleTensor_timeShift_integral_eq_xiShift_conj
            (d := d) (n := n) (m := m) (hm := hm)
            (f := φ) (g := ψ) (t := t) (Ψ := Ψ)
    _ =
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I)
              (t : ℂ)) *
            (φ.conjTensorProduct ψ) y := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with y
          have hshell :
              Ψ (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                    (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) =
                bvt_F OS lgc (n + m)
                  (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                    (fun k μ =>
                      ↑(y k μ) +
                        ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I)
                    (t : ℂ)) := by
            unfold Ψ
            congr 1
            ext k μ
            by_cases hμ : μ = 0
            · subst hμ
              by_cases hk : n ≤ k.val
              · simp [wickRotatePoint, xiShift, hk]
                calc
                  -(Complex.I * (Complex.I * ↑(y k 0) + ↑t * Complex.I)) +
                      ↑ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k 0) * Complex.I
                      =
                    -(((Complex.I * Complex.I) * ↑(y k 0)) +
                        ((Complex.I * Complex.I) * ↑t)) +
                      ↑ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k 0) * Complex.I := by
                        ring
                  _ =
                    -(((-1 : ℂ) * ↑(y k 0)) + ((-1 : ℂ) * ↑t)) +
                      ↑ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k 0) * Complex.I := by
                        simp [Complex.I_mul_I]
                  _ =
                    ↑(y k 0) +
                      ↑ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k 0) * Complex.I +
                      ↑t := by
                        ring
              · simp [wickRotatePoint, xiShift, hk]
                calc
                  -(Complex.I * (Complex.I * ↑(y k 0))) =
                      -((Complex.I * Complex.I) * ↑(y k 0)) := by ring
                  _ = -((-1 : ℂ) * ↑(y k 0)) := by rw [Complex.I_mul_I]
                  _ = ↑(y k 0) := by ring
            · by_cases hk : n ≤ k.val
              · simp [wickRotatePoint, xiShift, hμ, hk]
              · simp [wickRotatePoint, xiShift, hμ, hk]
          rw [hshell]

/-- The corrected finite-height canonical shell is genuinely in the forward
tube. The real `ξ`-shift contributes no imaginary part, while the fixed
canonical direction contributes the positive forward-cone height. -/
private theorem canonicalXiShift_mem_forwardTube
    {n m : ℕ} (hm : 0 < m)
    {t ε : ℝ} (hε : 0 < ε)
    (y : NPointDomain d (n + m)) :
    xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
      (fun k μ =>
        ↑(y k μ) +
          ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
            Complex.I)
      (t : ℂ) ∈ TubeDomainSetPi (ForwardConeAbs d (n + m)) := by
  change
    (fun k μ =>
      (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
        (fun k μ =>
          ↑(y k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
              Complex.I)
        (t : ℂ) k μ).im) ∈ ForwardConeAbs d (n + m)
  have hη_abs :
      canonicalForwardConeDirection (d := d) (n + m) ∈ ForwardConeAbs d (n + m) :=
    (inForwardCone_iff_mem_forwardConeAbs (d := d) (n := n + m)
      (canonicalForwardConeDirection (d := d) (n + m))).mp
      (canonicalForwardConeDirection_mem (d := d) (n + m))
  have hscaled :
      ε • canonicalForwardConeDirection (d := d) (n + m) ∈ ForwardConeAbs d (n + m) :=
    forwardConeAbs_smul d (n + m) ε hε
      (canonicalForwardConeDirection (d := d) (n + m)) hη_abs
  convert hscaled using 1
  ext k μ
  by_cases hshift : (⟨n, Nat.lt_add_of_pos_right hm⟩ : Fin (n + m)).val ≤ k.val ∧
      μ = (0 : Fin (d + 1))
  · simp [xiShift, hshift]
  · simp [xiShift, hshift]

/-- Continuity of the fixed-radius Paley-Wiener Schwartz family along the
flattened finite-height canonical shell. This is the continuity side condition
for the shell-side `schwartz_clm_fubini_exchange` packet. -/
private theorem continuous_canonicalShellPsiZExtFamily
    {n m : ℕ} (hm : 0 < m)
    {t ε : ℝ} (hε : 0 < ε)
    (hCflat_open :
      IsOpen
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_conv :
      Convex ℝ
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_cone :
      IsCone
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_salient :
      IsSalientCone
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m))) :
    Continuous (fun yflat : Fin ((n + m) * (d + 1)) → ℝ =>
      multiDimPsiZExt
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m))
        hCflat_open hCflat_conv hCflat_cone hCflat_salient
        (flattenCLEquiv (n + m) (d + 1)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun k μ =>
              (((flattenCLEquivReal (n + m) (d + 1)).symm yflat k μ : ℝ) : ℂ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                  Complex.I)
            (t : ℂ)))) := by
  let Cflat : Set (Fin ((n + m) * (d + 1)) → ℝ) :=
    (flattenCLEquivReal (n + m) (d + 1)) '' ForwardConeAbs d (n + m)
  let zMap : (Fin ((n + m) * (d + 1)) → ℝ) → Fin ((n + m) * (d + 1)) → ℂ :=
    fun yflat =>
      flattenCLEquiv (n + m) (d + 1)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            (((flattenCLEquivReal (n + m) (d + 1)).symm yflat k μ : ℝ) : ℂ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ))
  have hz_cont : Continuous zMap := by
    dsimp [zMap]
    apply continuous_pi
    intro a
    by_cases hshift : (⟨n, Nat.lt_add_of_pos_right hm⟩ : Fin (n + m)).val ≤
        (finProdFinEquiv.symm a).1.val ∧ (finProdFinEquiv.symm a).2 = (0 : Fin (d + 1))
    · simp [flattenCLEquiv_apply, xiShift]
      continuity
    · simp [flattenCLEquiv_apply, xiShift]
      continuity
  have hz_mem : ∀ yflat, zMap yflat ∈ SCV.TubeDomain Cflat := by
    intro yflat
    dsimp [zMap, Cflat]
    apply flattenCLEquiv_mem_tubeDomain_image
    exact canonicalXiShift_mem_forwardTube (d := d) hm hε
      ((flattenCLEquivReal (n + m) (d + 1)).symm yflat)
  simpa [Cflat, zMap] using
    continuous_multiDimPsiZExt_comp_of_mem_tube
      Cflat hCflat_open hCflat_conv hCflat_cone hCflat_salient zMap hz_cont hz_mem

/-- Polynomial seminorm growth of the fixed-radius Paley-Wiener Schwartz family
along the flattened finite-height canonical shell. This is the growth side
condition for the shell-side `schwartz_clm_fubini_exchange` packet. -/
private theorem seminorm_canonicalShellPsiZExtFamily_bound
    {n m : ℕ} (hm : 0 < m)
    {t ε : ℝ} (hε : 0 < ε)
    (hCflat_open :
      IsOpen
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_conv :
      Convex ℝ
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_cone :
      IsCone
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_salient :
      IsSalientCone
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m))) :
    ∀ (k l : ℕ), ∃ (C : ℝ) (N : ℕ), 0 < C ∧
      ∀ yflat : Fin ((n + m) * (d + 1)) → ℝ,
        SchwartzMap.seminorm ℝ k l
          (multiDimPsiZExt
            ((flattenCLEquivReal (n + m) (d + 1)) ''
              ForwardConeAbs d (n + m))
            hCflat_open hCflat_conv hCflat_cone hCflat_salient
            (flattenCLEquiv (n + m) (d + 1)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun k μ =>
                  (((flattenCLEquivReal (n + m) (d + 1)).symm yflat k μ : ℝ) : ℂ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I)
                (t : ℂ)))) ≤
          C * (1 + ‖yflat‖) ^ N := by
  intro k l
  let Cflat : Set (Fin ((n + m) * (d + 1)) → ℝ) :=
    (flattenCLEquivReal (n + m) (d + 1)) '' ForwardConeAbs d (n + m)
  let ηShell : Fin ((n + m) * (d + 1)) → ℝ :=
    flattenCLEquivReal (n + m) (d + 1)
      (ε • canonicalForwardConeDirection (d := d) (n + m))
  let zMap : (Fin ((n + m) * (d + 1)) → ℝ) → Fin ((n + m) * (d + 1)) → ℂ :=
    fun yflat =>
      flattenCLEquiv (n + m) (d + 1)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            (((flattenCLEquivReal (n + m) (d + 1)).symm yflat k μ : ℝ) : ℂ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ))
  let xShell : (Fin ((n + m) * (d + 1)) → ℝ) → Fin ((n + m) * (d + 1)) → ℝ :=
    fun yflat a => (zMap yflat a).re
  have hη_abs :
      canonicalForwardConeDirection (d := d) (n + m) ∈ ForwardConeAbs d (n + m) :=
    (inForwardCone_iff_mem_forwardConeAbs (d := d) (n := n + m)
      (canonicalForwardConeDirection (d := d) (n + m))).mp
      (canonicalForwardConeDirection_mem (d := d) (n + m))
  have hη_scaled :
      ε • canonicalForwardConeDirection (d := d) (n + m) ∈ ForwardConeAbs d (n + m) :=
    forwardConeAbs_smul d (n + m) ε hε
      (canonicalForwardConeDirection (d := d) (n + m)) hη_abs
  have hηShell_mem : ηShell ∈ Cflat := by
    exact ⟨ε • canonicalForwardConeDirection (d := d) (n + m), hη_scaled, rfl⟩
  obtain ⟨B, N, hB, hBbound⟩ :=
    multiDimPsiZExt_fixedImaginary_seminorm_bound
      Cflat hCflat_open hCflat_conv hCflat_cone hCflat_salient hηShell_mem k l
  let A : ℝ := 1 + |t|
  have hA_pos : 0 < A := by
    dsimp [A]
    positivity
  have hxShell_norm :
      ∀ yflat : Fin ((n + m) * (d + 1)) → ℝ,
        ‖xShell yflat‖ ≤ A * (1 + ‖yflat‖) := by
    intro yflat
    have hsymm_norm :
        ‖(flattenCLEquivReal (n + m) (d + 1)).symm yflat‖ = ‖yflat‖ := by
      simpa using
        (flattenCLEquivReal_norm_eq (n + m) (d + 1)
          ((flattenCLEquivReal (n + m) (d + 1)).symm yflat)).symm
    have hcoord :
        ∀ a : Fin ((n + m) * (d + 1)),
          |((flattenCLEquivReal (n + m) (d + 1)).symm yflat
              (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2)| ≤ ‖yflat‖ := by
      intro a
      calc
        |((flattenCLEquivReal (n + m) (d + 1)).symm yflat
            (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2)|
            = ‖((flattenCLEquivReal (n + m) (d + 1)).symm yflat
                (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2)‖ := by
                rw [Real.norm_eq_abs]
        _ ≤ ‖(flattenCLEquivReal (n + m) (d + 1)).symm yflat
              (finProdFinEquiv.symm a).1‖ :=
            norm_le_pi_norm _ (finProdFinEquiv.symm a).2
        _ ≤ ‖(flattenCLEquivReal (n + m) (d + 1)).symm yflat‖ :=
            norm_le_pi_norm _ (finProdFinEquiv.symm a).1
        _ = ‖yflat‖ := hsymm_norm
    have hnonneg : 0 ≤ A * (1 + ‖yflat‖) := by positivity
    apply (pi_norm_le_iff_of_nonneg hnonneg).2
    intro a
    by_cases hshift : (⟨n, Nat.lt_add_of_pos_right hm⟩ : Fin (n + m)).val ≤
        (finProdFinEquiv.symm a).1.val ∧ (finProdFinEquiv.symm a).2 = (0 : Fin (d + 1))
    · have hre :
          xShell yflat a =
            (flattenCLEquivReal (n + m) (d + 1)).symm yflat
              (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2 + t := by
        have hshift' : n ≤ a.val / (d + 1) ∧ a.modNat = (0 : Fin (d + 1)) := by
          simpa using hshift
        simp [xShell, zMap, flattenCLEquiv_apply, xiShift, hshift']
      calc
        ‖xShell yflat a‖ = |xShell yflat a| := Real.norm_eq_abs _
        _ = |(flattenCLEquivReal (n + m) (d + 1)).symm yflat
              (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2 + t| := by rw [hre]
        _ ≤ |(flattenCLEquivReal (n + m) (d + 1)).symm yflat
              (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2| + |t| :=
            abs_add_le _ _
        _ ≤ ‖yflat‖ + |t| := by
            gcongr
            exact hcoord a
        _ ≤ A * (1 + ‖yflat‖) := by
            dsimp [A]
            nlinarith [norm_nonneg yflat, abs_nonneg t]
    · have hre :
          xShell yflat a =
            (flattenCLEquivReal (n + m) (d + 1)).symm yflat
              (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2 := by
        have hshift' : ¬ (n ≤ a.val / (d + 1) ∧ a.modNat = (0 : Fin (d + 1))) := by
          simpa using hshift
        simp [xShell, zMap, flattenCLEquiv_apply, xiShift, hshift']
      calc
        ‖xShell yflat a‖ = |xShell yflat a| := Real.norm_eq_abs _
        _ = |(flattenCLEquivReal (n + m) (d + 1)).symm yflat
              (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2| := by rw [hre]
        _ ≤ ‖yflat‖ := hcoord a
        _ ≤ A * (1 + ‖yflat‖) := by
            dsimp [A]
            nlinarith [norm_nonneg yflat, abs_nonneg t]
  let C : ℝ := B * (1 + A) ^ N
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, N, hC_pos, ?_⟩
  intro yflat
  have hz_decomp :
      zMap yflat =
        fun a => ((xShell yflat a : ℝ) : ℂ) + (ηShell a : ℂ) * Complex.I := by
    ext a
    apply Complex.ext
    · simp [xShell]
    · have him : (zMap yflat a).im = ηShell a := by
        by_cases hshift : (⟨n, Nat.lt_add_of_pos_right hm⟩ : Fin (n + m)).val ≤
            (finProdFinEquiv.symm a).1.val ∧
              (finProdFinEquiv.symm a).2 = (0 : Fin (d + 1))
        · have hshift' : n ≤ a.val / (d + 1) ∧ a.modNat = (0 : Fin (d + 1)) := by
            simpa using hshift
          simp [zMap, ηShell, flattenCLEquiv_apply, flattenCLEquivReal_apply, xiShift, hshift']
        · have hshift' : ¬ (n ≤ a.val / (d + 1) ∧ a.modNat = (0 : Fin (d + 1))) := by
            simpa using hshift
          simp [zMap, ηShell, flattenCLEquiv_apply, flattenCLEquivReal_apply, xiShift, hshift']
      simp [him]
  have hbase :
      SchwartzMap.seminorm ℝ k l
        (multiDimPsiZExt Cflat hCflat_open hCflat_conv hCflat_cone hCflat_salient
          (zMap yflat)) ≤
        B * (1 + ‖xShell yflat‖) ^ N := by
    rw [hz_decomp]
    exact hBbound (xShell yflat)
  have hpoly :
      (1 + ‖xShell yflat‖) ^ N ≤ (1 + A) ^ N * (1 + ‖yflat‖) ^ N := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by linarith [norm_nonneg (xShell yflat)])
    calc
      1 + ‖xShell yflat‖ ≤ 1 + A * (1 + ‖yflat‖) := by
        linarith [hxShell_norm yflat]
      _ ≤ (1 + A) * (1 + ‖yflat‖) := by
        have hy_nonneg : 0 ≤ ‖yflat‖ := norm_nonneg yflat
        nlinarith [hA_pos.le, hy_nonneg]
  have hfinal :
      SchwartzMap.seminorm ℝ k l
        (multiDimPsiZExt Cflat hCflat_open hCflat_conv hCflat_cone hCflat_salient
          (zMap yflat)) ≤
        C * (1 + ‖yflat‖) ^ N := by
    calc
      SchwartzMap.seminorm ℝ k l
          (multiDimPsiZExt Cflat hCflat_open hCflat_conv hCflat_cone hCflat_salient
            (zMap yflat))
          ≤ B * (1 + ‖xShell yflat‖) ^ N := hbase
      _ ≤ B * ((1 + A) ^ N * (1 + ‖yflat‖) ^ N) := by
          gcongr
      _ = C * (1 + ‖yflat‖) ^ N := by
          dsimp [C]
          ring
  simpa [Cflat, zMap] using hfinal

/-- Flat Fubini packet for the fixed-radius Paley-Wiener Schwartz family along
the finite-height canonical shell. This packages the `KShell` produced by
`schwartz_clm_fubini_exchange`; boundary-value rewriting is kept for the next
lemma. -/
private theorem canonicalShellPsiZExtFamily_pairing
    {n m : ℕ} (hm : 0 < m)
    {t ε : ℝ} (hε : 0 < ε)
    (hCflat_open :
      IsOpen
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_conv :
      Convex ℝ
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_cone :
      IsCone
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_salient :
      IsSalientCone
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (Tflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (fFlat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ) :
    ∃ KShell : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
      (∀ ξ : Fin ((n + m) * (d + 1)) → ℝ,
        KShell ξ =
          ∫ yflat : Fin ((n + m) * (d + 1)) → ℝ,
            (multiDimPsiZExt
              ((flattenCLEquivReal (n + m) (d + 1)) ''
                ForwardConeAbs d (n + m))
              hCflat_open hCflat_conv hCflat_cone hCflat_salient
              (flattenCLEquiv (n + m) (d + 1)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun k μ =>
                    (((flattenCLEquivReal (n + m) (d + 1)).symm yflat k μ : ℝ) : ℂ) +
                      ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                        Complex.I)
                  (t : ℂ)))) ξ *
              fFlat yflat) ∧
      (∫ yflat : Fin ((n + m) * (d + 1)) → ℝ,
        Tflat
          (multiDimPsiZExt
            ((flattenCLEquivReal (n + m) (d + 1)) ''
              ForwardConeAbs d (n + m))
            hCflat_open hCflat_conv hCflat_cone hCflat_salient
            (flattenCLEquiv (n + m) (d + 1)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun k μ =>
                  (((flattenCLEquivReal (n + m) (d + 1)).symm yflat k μ : ℝ) : ℂ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I)
                (t : ℂ)))) *
          fFlat yflat) =
        Tflat KShell := by
  let Cflat : Set (Fin ((n + m) * (d + 1)) → ℝ) :=
    (flattenCLEquivReal (n + m) (d + 1)) '' ForwardConeAbs d (n + m)
  let gFamily : (Fin ((n + m) * (d + 1)) → ℝ) →
      SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ :=
    fun yflat =>
      multiDimPsiZExt Cflat hCflat_open hCflat_conv hCflat_cone hCflat_salient
        (flattenCLEquiv (n + m) (d + 1)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun k μ =>
              (((flattenCLEquivReal (n + m) (d + 1)).symm yflat k μ : ℝ) : ℂ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                  Complex.I)
            (t : ℂ)))
  have hg_cont : Continuous gFamily := by
    simpa [Cflat, gFamily] using
      continuous_canonicalShellPsiZExtFamily (d := d) hm hε
        hCflat_open hCflat_conv hCflat_cone hCflat_salient
  have hg_bound :
      ∀ (k l : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
        ∀ yflat : Fin ((n + m) * (d + 1)) → ℝ,
          SchwartzMap.seminorm ℝ k l (gFamily yflat) ≤ C * (1 + ‖yflat‖) ^ N := by
    simpa [Cflat, gFamily] using
      seminorm_canonicalShellPsiZExtFamily_bound (d := d) hm hε
        hCflat_open hCflat_conv hCflat_cone hCflat_salient
  obtain ⟨KShell, _hKShell_eval, hKShell_pair⟩ :=
    schwartz_clm_fubini_exchange Tflat gFamily fFlat hg_cont hg_bound
  refine ⟨KShell, ?_, ?_⟩
  · intro ξ
    simpa [Cflat, gFamily] using _hKShell_eval ξ
  · simpa [Cflat, gFamily] using hKShell_pair.symm

/-- Shell-side boundary-value integral as a flattened Paley-Wiener/Fubini
kernel pairing. This combines the `bvt_F` Fourier-Laplace representation with
the flat shell Fubini packet. -/
private theorem exists_shellKernel_pairing_canonicalXiShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    {t ε : ℝ} (hε : 0 < ε)
    (hCflat_open :
      IsOpen
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_conv :
      Convex ℝ
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_cone :
      IsCone
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (hCflat_salient :
      IsSalientCone
        ((flattenCLEquivReal (n + m) (d + 1)) ''
          ForwardConeAbs d (n + m)))
    (Tflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hFL :
      ∀ z : Fin (n + m) → Fin (d + 1) → ℂ,
        z ∈ TubeDomainSetPi (ForwardConeAbs d (n + m)) →
          bvt_F OS lgc (n + m) z =
            fourierLaplaceExtMultiDim
              ((flattenCLEquivReal (n + m) (d + 1)) ''
                ForwardConeAbs d (n + m))
              hCflat_open hCflat_conv hCflat_cone hCflat_salient
              Tflat (flattenCLEquiv (n + m) (d + 1) z)) :
    ∃ KShell : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
      (∀ ξ : Fin ((n + m) * (d + 1)) → ℝ,
        KShell ξ =
          ∫ yflat : Fin ((n + m) * (d + 1)) → ℝ,
            (multiDimPsiZExt
              ((flattenCLEquivReal (n + m) (d + 1)) ''
                ForwardConeAbs d (n + m))
              hCflat_open hCflat_conv hCflat_cone hCflat_salient
              (flattenCLEquiv (n + m) (d + 1)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun k μ =>
                    (((flattenCLEquivReal (n + m) (d + 1)).symm yflat k μ : ℝ) : ℂ) +
                      ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                        Complex.I)
                  (t : ℂ)))) ξ *
              _root_.flattenSchwartzNPoint (d := d) (φ.conjTensorProduct ψ) yflat) ∧
      (∫ y : NPointDomain d (n + m),
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun k μ =>
              ↑(y k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                  Complex.I)
            (t : ℂ)) *
          (φ.conjTensorProduct ψ) y) =
        Tflat KShell := by
  let Cflat : Set (Fin ((n + m) * (d + 1)) → ℝ) :=
    (flattenCLEquivReal (n + m) (d + 1)) '' ForwardConeAbs d (n + m)
  let zShell :
      (Fin ((n + m) * (d + 1)) → ℝ) → Fin (n + m) → Fin (d + 1) → ℂ :=
    fun yflat =>
      xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
        (fun k μ =>
          (((flattenCLEquivReal (n + m) (d + 1)).symm yflat k μ : ℝ) : ℂ) +
            ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
              Complex.I)
        (t : ℂ)
  let gFlat : (Fin ((n + m) * (d + 1)) → ℝ) → ℂ :=
    fun yflat =>
      Tflat
        (multiDimPsiZExt Cflat hCflat_open hCflat_conv hCflat_cone hCflat_salient
          (flattenCLEquiv (n + m) (d + 1) (zShell yflat))) *
        _root_.flattenSchwartzNPoint (d := d) (φ.conjTensorProduct ψ) yflat
  obtain ⟨KShell, hKShell_eval, hKShell⟩ :=
    canonicalShellPsiZExtFamily_pairing (d := d) hm hε
      hCflat_open hCflat_conv hCflat_cone hCflat_salient Tflat
      (_root_.flattenSchwartzNPoint (d := d) (φ.conjTensorProduct ψ))
  refine ⟨KShell, ?_, ?_⟩
  · simpa [Cflat, zShell] using hKShell_eval
  have hflat_cv :
      ∫ yflat : Fin ((n + m) * (d + 1)) → ℝ, gFlat yflat =
        ∫ y : NPointDomain d (n + m),
          gFlat (flattenCLEquivReal (n + m) (d + 1) y) :=
    integral_flatten_change_of_variables (n + m) (d + 1) gFlat
  have htarget_to_flat :
      (∫ y : NPointDomain d (n + m),
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun k μ =>
              ↑(y k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                  Complex.I)
            (t : ℂ)) *
          (φ.conjTensorProduct ψ) y) =
        ∫ y : NPointDomain d (n + m),
          gFlat (flattenCLEquivReal (n + m) (d + 1) y) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    let shellY : Fin (n + m) → Fin (d + 1) → ℂ :=
      xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
        (fun k μ =>
          ↑(y k μ) +
            ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
              Complex.I)
        (t : ℂ)
    have hzShell_flat :
        zShell (flattenCLEquivReal (n + m) (d + 1) y) = shellY := by
      ext k μ
      simp [zShell, shellY]
    have hshell_mem : shellY ∈ TubeDomainSetPi (ForwardConeAbs d (n + m)) := by
      simpa [shellY] using canonicalXiShift_mem_forwardTube (d := d) hm hε y
    have hbvt :
        bvt_F OS lgc (n + m) shellY =
          Tflat
            (multiDimPsiZExt Cflat hCflat_open hCflat_conv hCflat_cone hCflat_salient
              (flattenCLEquiv (n + m) (d + 1) shellY)) := by
      calc
        bvt_F OS lgc (n + m) shellY
            = fourierLaplaceExtMultiDim Cflat hCflat_open hCflat_conv hCflat_cone
                hCflat_salient Tflat (flattenCLEquiv (n + m) (d + 1) shellY) :=
              hFL shellY hshell_mem
        _ = Tflat
              (multiDimPsiZExt Cflat hCflat_open hCflat_conv hCflat_cone hCflat_salient
                (flattenCLEquiv (n + m) (d + 1) shellY)) := by
              rw [fourierLaplaceExtMultiDim_eq_ext]
    simp [gFlat, Cflat, hzShell_flat, hbvt, shellY, _root_.flattenSchwartzNPoint_apply]
  calc
    (∫ y : NPointDomain d (n + m),
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun k μ =>
              ↑(y k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                  Complex.I)
            (t : ℂ)) *
          (φ.conjTensorProduct ψ) y)
        = ∫ y : NPointDomain d (n + m),
            gFlat (flattenCLEquivReal (n + m) (d + 1) y) := htarget_to_flat
    _ = ∫ yflat : Fin ((n + m) * (d + 1)) → ℝ, gFlat yflat := hflat_cv.symm
    _ = Tflat KShell := by
      simpa [gFlat, Cflat, zShell] using hKShell

/-- The chosen boundary-value continuation `bvt_F` inherits the global forward-
tube polynomial-growth package from
`full_analytic_continuation_with_symmetry_growth`. This keeps the current
Stage-5 shell work on the theorem-based OS continuation rather than routing
through any extra placeholder witness. -/
private theorem bvt_F_hasGlobalForwardTubeGrowth
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (k : ℕ) :
    ∃ (C_bd : ℝ) (N : ℕ),
      0 < C_bd ∧
      ∀ z ∈ ForwardTube d k,
        ‖bvt_F OS lgc k z‖ ≤ C_bd * (1 + ‖z‖) ^ N := by
  rcases (full_analytic_continuation_with_acr_symmetry_growth OS lgc k).choose_spec with
    ⟨_hACR, _hFT, _hEuclid, _hPerm, _hTrans, _hNegCanonical, hGrowth⟩
  exact hGrowth

/-- Exact Step-1 Wightman-side boundary-value shell for the current
Lemma-4.2 route: the reconstructed pairing against the right-time-shifted
ambient tensor is the canonical forward-cone boundary value of the matching
`bvt_F` integral shell. This is just `bvt_boundary_values` specialized to the
current theorem surface, but naming it here keeps the remaining blocker honest:
the next missing step is the time-variable interchange on this explicit shell,
not another hidden boundary-value reduction. -/
private theorem tendsto_bvt_F_canonical_conjTensorProduct_timeShift_boundaryValue
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m) (t : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : NPointDomain d (n + m),
          bvt_F OS lgc (n + m) (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I) *
            (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)))) := by
  let η0 := canonicalForwardConeDirection (d := d) (n + m)
  have hη0 : InForwardCone d (n + m) η0 :=
    canonicalForwardConeDirection_mem (d := d) (n + m)
  simpa [η0] using
    (bvt_boundary_values OS lgc (n + m)
      (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) η0 hη0)

/-- Step-1/2 boundary-value form of the current Lemma-4.2 lane: after moving
the right-time shift from the ambient test tensor into the explicit canonical
`ξ`-shift shell, the resulting shell still has boundary value equal to the
reconstructed Wightman pairing against the right-time-shifted ambient tensor.

This is exactly the current-code replacement for the older hidden
"Wightman-side shell rewrite" slogan: the rewrite is now explicit, checked, and
still lands at the same boundary value. -/
private theorem tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift_boundaryValue
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m) (t : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ =>
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I)
              (t : ℂ)) *
            (φ.conjTensorProduct ψ) y)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)))) := by
  have hEq :
      (fun ε : ℝ =>
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I)
              (t : ℂ)) *
            (φ.conjTensorProduct ψ) y)
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε : ℝ =>
        ∫ x : NPointDomain d (n + m),
          bvt_F OS lgc (n + m) (fun k μ =>
            ↑(x k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) * Complex.I) *
            (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) x) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    symm
    exact bvt_F_canonical_conjTensorProduct_timeShift_eq_xiShift
      (d := d) (OS := OS) (lgc := lgc) (hm := hm) (φ := φ) (ψ := ψ) (t := t) (ε := ε)
  exact Filter.Tendsto.congr' hEq.symm <|
    tendsto_bvt_F_canonical_conjTensorProduct_timeShift_boundaryValue
      (d := d) (OS := OS) (lgc := lgc) (φ := φ) (ψ := ψ) (t := t)

/-- Step-3 reduction for the current Lemma-4.2 route: once the canonical
`ξ`-shift shell is shown to converge back to some explicit scalar `L` as
`ε → 0+`, that scalar is forced to be the reconstructed Wightman pairing
against the right-time-shifted ambient tensor.

This keeps the remaining analytic content honest. After the Step-1/2 shell
rewrite above, the next unresolved theorem is precisely the limit identification
for the explicit canonical `ξ`-shift shell, not another hidden boundary-value
argument. -/
private theorem bvt_W_eq_of_tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m) (t : ℝ)
    {L : ℂ}
    (hL :
      Filter.Tendsto
        (fun ε : ℝ =>
          ∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun k μ =>
                  ↑(y k μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I)
                (t : ℂ)) *
              (φ.conjTensorProduct ψ) y)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds L)) :
    L =
      bvt_W OS lgc (n + m)
        (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) := by
  have hW :
      Filter.Tendsto
        (fun ε : ℝ =>
          ∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun k μ =>
                  ↑(y k μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I)
                (t : ℂ)) *
              (φ.conjTensorProduct ψ) y)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (bvt_W OS lgc (n + m)
            (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)))) :=
    tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift_boundaryValue
      (d := d) (OS := OS) (lgc := lgc) (hm := hm) (φ := φ) (ψ := ψ) (t := t)
  exact tendsto_nhds_unique hL hW

/-- On the exact `bvt_F` shell used by the current Lemma-4.2 lane, the
positive-real OS matrix element converges back to the unshifted Euclidean term
as `t → 0+`. This is the current-code specialization of the already-proved
Schwinger-side boundary-value theorem to the explicit `bvt_F` kernel. -/
private theorem tendsto_bvt_F_osConjTensorProduct_timeShift_nhdsWithin_zero
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ)) :
    Filter.Tendsto
      (fun t : ℝ =>
        OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)))) := by
  have htrace :
      (fun t : ℝ =>
        OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun t : ℝ =>
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (f.osConjTensorProduct g) y) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact bvt_F_osConjTensorProduct_timeShift_eq_xiShift
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (f := f) (hf_ord := hf_ord) (g := g) (hg_ord := hg_ord) (t := t) ht
  exact Filter.Tendsto.congr' htrace.symm <|
    bvt_tendsto_singleSplit_xiShift_nhdsWithin_zero_schwinger
      (d := d) (OS := OS) (lgc := lgc) n m hm
      f hf_ord hf_compact g hg_ord hg_compact

/-- Compact-support reduction of the current Stage-5 frontier: if on positive
real times the Euclidean/OS right-time-shift shell already agrees with the
reconstructed Wightman pairing against the corresponding right-time-shifted
ambient test, then the desired kernel equality at `t = 0` follows formally by
taking `t → 0+` on both sides.

This keeps the remaining live content in the exact shape the proof docs now
advertise: the unresolved theorem is the positive-real time-variable
interchange / boundary-value identification, not another shell-limit lemma. -/
private theorem kernel_eq_of_timeShift_eq_on_positiveReals
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (hreal :
      ∀ t : ℝ, 0 < t →
        OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)))
          =
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ))) :
    bvt_W OS lgc (n + m) (φ.conjTensorProduct ψ)
      =
    OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
  have hS :
      Filter.Tendsto
        (fun t : ℝ =>
          OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)))) := by
    exact tendsto_bvt_F_osConjTensorProduct_timeShift_nhdsWithin_zero
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (f := f) (hf_ord := hf_ord) (hf_compact := hf_compact)
      (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
  have hW :
      Filter.Tendsto
        (fun t : ℝ =>
          bvt_W OS lgc (n + m)
            (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (bvt_W OS lgc (n + m) (φ.conjTensorProduct ψ))) := by
    exact tendsto_bvt_W_conjTensorProduct_timeShift_nhdsWithin_zero
      (d := d) (OS := OS) (lgc := lgc)
      (f := φ) (g := ψ) (hg_compact := hψ_compact)
  have hEq :
      (fun t : ℝ =>
        OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct (timeShiftSchwartzNPoint (d := d) t g))))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun t : ℝ =>
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hreal t ht
  have hS_as_W :
      Filter.Tendsto
        (fun t : ℝ =>
          bvt_W OS lgc (n + m)
            (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)))) :=
    Filter.Tendsto.congr' hEq hS
  exact tendsto_nhds_unique hW hS_as_W

/-- Equivalent current-code reduction with the OS side written on the direct
`ξ`-shift shell: if for all positive real `t` the current OS `ξ`-shift shell
already agrees with the reconstructed Wightman pairing against the right-time
shifted ambient test, then the kernel equality at `t = 0` follows.

This is just `kernel_eq_of_timeShift_eq_on_positiveReals` after rewriting the
OS side to the actual `bvt_F` `ξ`-shift shell used by the current Lemma-4.2
lane. It does not pretend the Wightman side has already been rewritten to the
same raw integral surface; that remaining boundary-value/time-interchange step
is still the live Stage-5 content. -/
private theorem kernel_eq_of_osXiShift_eq_bvt_W_timeShift_on_positiveReals
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (hreal :
      ∀ t : ℝ, 0 < t →
        (∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
            (f.osConjTensorProduct g) y) =
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ))) :
    bvt_W OS lgc (n + m) (φ.conjTensorProduct ψ)
      =
    OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
  refine kernel_eq_of_timeShift_eq_on_positiveReals
    (d := d) (OS := OS) (lgc := lgc) (hm := hm)
    (φ := φ) (ψ := ψ) (f := f)
    (hf_ord := hf_ord) (hf_compact := hf_compact)
    (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
    (hψ_compact := hψ_compact) ?_
  intro t ht
  rw [bvt_F_osConjTensorProduct_timeShift_eq_xiShift
    (d := d) (OS := OS) (lgc := lgc) (hm := hm)
    (f := f) (hf_ord := hf_ord) (g := g) (hg_ord := hg_ord) (t := t) ht]
  exact hreal t ht

/-- Honest Stage-5 reduction for the current Lemma-4.2 lane: to prove the
kernel equality at `t = 0`, it is enough to show that for every positive real
`t`, the canonical forward-cone boundary-value shell converges to the explicit
current-code `ξ`-shift shell against the positive-time preimages.

This theorem is the immediate consumer of the new Step-1/2 shell rewrite. It
shrinks the remaining live analytic content to one positive-real shell-limit
statement, without reviving any false same-shell shortcut. -/
private theorem kernel_eq_of_tendsto_bvt_F_canonical_xiShift_to_osXiShift_on_positiveReals
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (hlimit :
      ∀ t : ℝ, 0 < t →
        Filter.Tendsto
          (fun ε : ℝ =>
            ∫ y : NPointDomain d (n + m),
              bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun k μ =>
                    ↑(y k μ) +
                      ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                        Complex.I)
                  (t : ℂ)) *
                (φ.conjTensorProduct ψ) y)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (∫ y : NPointDomain d (n + m),
              bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
                (f.osConjTensorProduct g) y))) :
    bvt_W OS lgc (n + m) (φ.conjTensorProduct ψ) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
  refine kernel_eq_of_osXiShift_eq_bvt_W_timeShift_on_positiveReals
    (d := d) (OS := OS) (lgc := lgc) (hm := hm)
    (φ := φ) (ψ := ψ) (f := f)
    (hf_ord := hf_ord) (hf_compact := hf_compact)
    (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
    (hψ_compact := hψ_compact) ?_
  intro t ht
  exact
    (bvt_W_eq_of_tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (φ := φ) (ψ := ψ) (t := t)
      (hL := hlimit t ht))

/-- Reusable one-variable right-half-plane uniqueness step for the current
Lemma-4.2 route: if a holomorphic scalar `H` agrees on positive real points
both with the explicit preimage-side `singleSplit_xiShift` shell and with the
ambient Wightman time-shift pairing, then the chosen `singleSplit_xiShift`
holomorphic trace already agrees with that ambient Wightman pairing on
positive real times.

This is the exact reusable analytic theorem slot described in the proof docs
as `one_variable_time_interchange_for_wightman_pairing`. The later concrete
Section-4.3 adapter still has to construct such an `H` from the ambient
representative / positive-time preimage hypotheses. -/
private theorem one_variable_time_interchange_for_wightman_pairing
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (H : ℂ → ℂ)
    (hH_holo : DifferentiableOn ℂ H {z : ℂ | 0 < z.re})
    (hH_real_shell :
      ∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          ∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              (f.osConjTensorProduct g) y)
    (hH_real_wightman :
      ∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          bvt_W OS lgc (n + m)
            (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ))) :
    ∀ t : ℝ, 0 < t →
      bvt_singleSplit_xiShiftHolomorphicValue
          (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ) =
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) := by
  have hEqOn :
      Set.EqOn H
        (bvt_singleSplit_xiShiftHolomorphicValue
          (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact)
        {z : ℂ | 0 < z.re} :=
    bvt_singleSplit_xiShiftHolomorphicValue_eqOn_ofReal_eq
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (f := f) (hf_ord := hf_ord) (hf_compact := hf_compact)
      (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
      (H := H) hH_holo hH_real_shell
  intro t ht
  have ht_mem : (t : ℂ) ∈ {z : ℂ | 0 < z.re} := by
    simpa using ht
  calc
    bvt_singleSplit_xiShiftHolomorphicValue
        (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ)
      = H (t : ℂ) := by
          symm
          exact hEqOn ht_mem
    _ =
      bvt_W OS lgc (n + m)
        (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) :=
      hH_real_wightman t ht

/-- Internal-supplier reduction for the current Stage-5 frontier: if the
chosen one-variable `singleSplit_xiShift` holomorphic trace built from the
positive-time preimages `f, g` already agrees on positive real times with the
reconstructed Wightman pairing against the ambient representatives `φ, ψ`,
then the desired kernel equality at `t = 0` follows.

This keeps the public theorem surface on the corrected ambient
representative/preimage data while allowing the existing `singleSplit`
holomorphic trace to be used only as an internal proof supplier. -/
private theorem kernel_eq_of_singleSplit_eq_bvt_W_timeShift_on_positiveReals
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (hreal :
      ∀ t : ℝ, 0 < t →
        bvt_singleSplit_xiShiftHolomorphicValue
            (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ)
          =
            bvt_W OS lgc (n + m)
              (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ))) :
    bvt_W OS lgc (n + m) (φ.conjTensorProduct ψ) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
  have hW :
      Filter.Tendsto
        (fun t : ℝ =>
          bvt_singleSplit_xiShiftHolomorphicValue
            (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (bvt_W OS lgc (n + m)
            (φ.conjTensorProduct ψ))) :=
    tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_of_ofReal_eq_bvt_W_ambient_conjTensorProduct_timeShift
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (f := f) (hf_ord := hf_ord) (hf_compact := hf_compact)
      (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
      (φ := φ) (ψ := ψ) (hψ_compact := hψ_compact) hreal
  have hS :
      Filter.Tendsto
        (fun t : ℝ =>
          bvt_singleSplit_xiShiftHolomorphicValue
            (d := d) OS lgc hm f hf_ord hf_compact g hg_ord hg_compact (t : ℂ))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)))) :=
    tendsto_bvt_singleSplit_xiShiftHolomorphicValue_nhdsWithin_zero_schwinger
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (f := f) (hf_ord := hf_ord) (hf_compact := hf_compact)
      (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
  exact tendsto_nhds_unique hW hS

/-- Honest Stage-5 per-pair kernel reduction after the reusable Section-8
uniqueness step: once a holomorphic witness `H` on the right half-plane is
constructed with the correct positive-real shell values and the correct
positive-real Wightman values, the desired kernel equality at `t = 0` follows
formally.

This packages the existing kernel reduction with
`one_variable_time_interchange_for_wightman_pairing`, so the remaining live
analytic job is now exactly the construction of such an `H` from the ambient
representative / positive-time preimage data. -/
private theorem kernel_eq_of_one_variable_time_interchange_for_wightman_pairing
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (H : ℂ → ℂ)
    (hH_holo : DifferentiableOn ℂ H {z : ℂ | 0 < z.re})
    (hH_real_shell :
      ∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          ∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun i => wickRotatePoint (y i)) ((t : ℂ) * Complex.I)) *
              (f.osConjTensorProduct g) y)
    (hH_real_wightman :
      ∀ t : ℝ, 0 < t →
        H (t : ℂ) =
          bvt_W OS lgc (n + m)
            (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ))) :
    bvt_W OS lgc (n + m) (φ.conjTensorProduct ψ) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
  apply kernel_eq_of_singleSplit_eq_bvt_W_timeShift_on_positiveReals
    (d := d) (OS := OS) (lgc := lgc) (hm := hm)
    (φ := φ) (ψ := ψ) (f := f)
    (hf_ord := hf_ord) (hf_compact := hf_compact)
    (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
    (hψ_compact := hψ_compact)
  exact one_variable_time_interchange_for_wightman_pairing
    (d := d) (OS := OS) (lgc := lgc) (hm := hm)
    (φ := φ) (ψ := ψ) (f := f)
    (hf_ord := hf_ord) (hf_compact := hf_compact)
    (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
    (H := H) hH_holo hH_real_shell hH_real_wightman

/-- Semigroup-side variant of the same reduction: since the chosen
`singleSplit_xiShift` holomorphic trace already agrees with the OS
time-shift holomorphic matrix element on the whole right half-plane, it is
enough to identify that OS holomorphic value with the reconstructed Wightman
pairing on positive real times. -/
private theorem kernel_eq_of_osHolomorphicValue_eq_bvt_W_timeShift_on_positiveReals
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (hreal :
      ∀ t : ℝ, 0 < t →
        OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ)
          =
            bvt_W OS lgc (n + m)
              (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ))) :
    bvt_W OS lgc (n + m) (φ.conjTensorProduct ψ) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
  refine kernel_eq_of_singleSplit_eq_bvt_W_timeShift_on_positiveReals
    (d := d) (OS := OS) (lgc := lgc) (hm := hm)
    (φ := φ) (ψ := ψ) (f := f)
    (hf_ord := hf_ord) (hf_compact := hf_compact)
    (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
    (hψ_compact := hψ_compact) ?_
  intro t ht
  rw [bvt_xiShift_eq_osInnerProduct_holomorphicValue_single
    (d := d) (OS := OS) (lgc := lgc) (hm := hm)
    (f := f) (hf_ord := hf_ord) (hf_compact := hf_compact)
    (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
    (z := (t : ℂ)) (hz := by simpa using ht)]
  exact hreal t ht

/-- Current best Stage-5 reduction: to prove the kernel equality at `t = 0`, it
is enough to show that for every positive real `t`, the explicit canonical
forward-cone `ξ`-shift shell has boundary value equal to the OS holomorphic
matrix element for the positive-time preimages.

This is the exact theorem surface the current branch-`3b` / Section-4.3
machinery is built to attack: the Wightman side stays on the explicit canonical
shell, while the target scalar is the already-built semigroup-side holomorphic
family rather than a raw same-shell comparison. -/
private theorem kernel_eq_of_tendsto_bvt_F_canonical_xiShift_to_osHolomorphicValue_on_positiveReals
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (hlimit :
      ∀ t : ℝ, 0 < t →
        Filter.Tendsto
          (fun ε : ℝ =>
            ∫ y : NPointDomain d (n + m),
              bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun k μ =>
                    ↑(y k μ) +
                      ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                        Complex.I)
                  (t : ℂ)) *
                (φ.conjTensorProduct ψ) y)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ)))) :
    bvt_W OS lgc (n + m) (φ.conjTensorProduct ψ) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
  refine kernel_eq_of_osHolomorphicValue_eq_bvt_W_timeShift_on_positiveReals
    (d := d) (OS := OS) (lgc := lgc) (hm := hm)
    (φ := φ) (ψ := ψ) (f := f)
    (hf_ord := hf_ord) (hf_compact := hf_compact)
    (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
    (hψ_compact := hψ_compact) ?_
  intro t ht
  exact
    (bvt_W_eq_of_tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (φ := φ) (ψ := ψ) (t := t)
      (hL := hlimit t ht))

/-- Upper-half-plane witness variant of the same Stage-5 reduction: if the
canonical forward-cone shell converges for each positive real `t` to the value
of some ambient upper-half-plane witness on the positive imaginary axis, and
those imaginary-axis values are already identified with the semigroup-side
holomorphic matrix element, then the kernel equality at `t = 0` follows.

This records the honest post-Paley-Wiener theorem surface: the ambient witness
coming from `SCV.paley_wiener_half_line` naturally lives on
`SCV.upperHalfPlane`, so the immediate consumer only needs its values at
`(t : ℂ) * I` rather than a prematurely rotated right-half-plane packaging. -/
private theorem kernel_eq_of_tendsto_bvt_F_canonical_xiShift_to_upperHalfPlaneWitness_on_imagAxis
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (H : ℂ → ℂ)
    (hH_imag_os :
      ∀ t : ℝ, 0 < t →
        H ((t : ℂ) * Complex.I) =
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ))
    (hlimit :
      ∀ t : ℝ, 0 < t →
        Filter.Tendsto
          (fun ε : ℝ =>
            ∫ y : NPointDomain d (n + m),
              bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun k μ =>
                    ↑(y k μ) +
                      ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                        Complex.I)
                  (t : ℂ)) *
                (φ.conjTensorProduct ψ) y)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (H ((t : ℂ) * Complex.I)))) :
    bvt_W OS lgc (n + m) (φ.conjTensorProduct ψ) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
  refine kernel_eq_of_tendsto_bvt_F_canonical_xiShift_to_osHolomorphicValue_on_positiveReals
    (d := d) (OS := OS) (lgc := lgc) (hm := hm)
    (φ := φ) (ψ := ψ) (f := f)
    (hf_ord := hf_ord) (hf_compact := hf_compact)
    (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
    (hψ_compact := hψ_compact) ?_
  intro t ht
  simpa [hH_imag_os t ht] using hlimit t ht

/-- Concrete Section-4.3 / Lemma-4.2 adapter on the current honest theorem
surface: if an upper-half-plane witness already matches the semigroup-side
holomorphic matrix element on the positive imaginary axis, and the canonical
forward-cone `ξ`-shift shell converges to those same witness values for every
positive real time, then the reconstructed Wightman matrix element equals the
OS/Schwinger matrix element.

This theorem does not hide the remaining analytic work. Its hypotheses are
exactly the current Stage-5 blocker: the positive-imaginary-axis witness
identification and the shell-specific limit theorem. Once those are proved,
this theorem is the public consumer that delivers the per-pair kernel equality
needed later for Eq. `(4.28)` and positivity. -/
theorem lemma42_matrix_element_time_interchange
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (H : ℂ → ℂ)
    (hH_imag_os :
      ∀ t : ℝ, 0 < t →
        H ((t : ℂ) * Complex.I) =
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ))
    (hlimit :
      ∀ t : ℝ, 0 < t →
        Filter.Tendsto
          (fun ε : ℝ =>
            ∫ y : NPointDomain d (n + m),
              bvt_F OS lgc (n + m)
                (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                  (fun k μ =>
                    ↑(y k μ) +
                      ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                        Complex.I)
                  (t : ℂ)) *
                (φ.conjTensorProduct ψ) y)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (H ((t : ℂ) * Complex.I)))) :
    bvt_W OS lgc (n + m) (φ.conjTensorProduct ψ) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
  exact
    kernel_eq_of_tendsto_bvt_F_canonical_xiShift_to_upperHalfPlaneWitness_on_imagAxis
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (φ := φ) (ψ := ψ) (f := f)
      (hf_ord := hf_ord) (hf_compact := hf_compact)
      (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact)
      (hψ_compact := hψ_compact) (H := H) hH_imag_os hlimit

/-- Route `3b-II` uniqueness assembly: once the real-time Wightman pairing
functional and the semigroup-side spectral boundary-value functional agree on
Fourier transforms of Schwartz tests, the explicit canonical Wightman witness
and the rotated OS holomorphic matrix element agree on the entire upper
half-plane.

This does not hide the remaining mathematics. The only live hypothesis is the
boundary-value identity itself; the rest is now a checked one-variable
distributional uniqueness argument. -/
private theorem
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension_eq_rotated_OS_of_boundaryValue_fourierTransform_eq
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hBV :
      let xF : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
        (⟦PositiveTimeBorchersSequence.single n f hf_ord⟧)) : OSHilbertSpace OS))
      let xG : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
        (⟦PositiveTimeBorchersSequence.single m g hg_ord⟧)) : OSHilbertSpace OS))
      ∀ χ : SchwartzMap ℝ ℂ,
        ∫ t : ℝ,
          bvt_W OS lgc (n + m)
            (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) *
            (SchwartzMap.fourierTransformCLM ℂ χ) t =
          selfAdjointSpectralBoundaryValueOffdiag
            (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
            (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
            xF xG χ) :
    Set.EqOn
      (bvt_W_conjTensorProduct_timeShiftCanonicalExtension
        (d := d) OS lgc f g hg_compact)
      (fun w =>
        OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single m g hg_ord)
          (-Complex.I * w))
      SCV.upperHalfPlane := by
  let xF : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    (⟦PositiveTimeBorchersSequence.single n f hf_ord⟧)) : OSHilbertSpace OS))
  let xG : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    (⟦PositiveTimeBorchersSequence.single m g hg_ord⟧)) : OSHilbertSpace OS))
  have hBV' :
      ∀ χ : SchwartzMap ℝ ℂ,
        ∫ t : ℝ,
          bvt_W OS lgc (n + m)
            (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) *
            (SchwartzMap.fourierTransformCLM ℂ χ) t =
          selfAdjointSpectralBoundaryValueOffdiag
            (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
            (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
            xF xG χ := by
    simpa [xF, xG] using hBV
  let HΔ : ℂ → ℂ := fun w =>
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension
        (d := d) OS lgc f g hg_compact w -
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord)
        (-Complex.I * w)
  let C : Set (Fin 1 → ℝ) := {y | 0 < y 0}
  let G : (Fin 1 → ℂ) → ℂ := fun z => HΔ (z 0)
  let eR : (Fin 1 → ℝ) ≃L[ℝ] ℝ :=
    ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ
  let eM : ℝ ≃ᵐ (Fin 1 → ℝ) := eR.symm.toHomeomorph.toMeasurableEquiv
  have hmp_eM : MeasureTheory.MeasurePreserving eM MeasureTheory.volume MeasureTheory.volume := by
    simpa [eM, eR] using (MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm
  have hHΔ_diff : DifferentiableOn ℂ HΔ SCV.upperHalfPlane := by
    exact
      (bvt_W_conjTensorProduct_timeShiftCanonicalExtension_differentiableOn
        (d := d) (OS := OS) (lgc := lgc) f g hg_compact).sub
      (differentiableOn_rotated_OSInnerProductTimeShiftHolomorphicValue
        (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord))
  have hHΔ_growth :
      ∀ η : ℝ, 0 < η →
        SCV.HasPolynomialGrowthOnLine (fun x => HΔ (↑x + ↑η * Complex.I)) := by
    intro η hη
    obtain ⟨C₁, N₁, hC₁, hbound₁⟩ :=
      hasPolynomialGrowthOnLine_bvt_W_conjTensorProduct_timeShiftCanonicalExtension
        (d := d) (OS := OS) (lgc := lgc) f g hg_compact η hη
    obtain ⟨C₂, N₂, hC₂, hbound₂⟩ :=
      hasPolynomialGrowthOnLine_rotated_OSInnerProductTimeShiftHolomorphicValue
        (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord) η hη
    refine ⟨C₁ + C₂, max N₁ N₂, add_pos hC₁ hC₂, fun x => ?_⟩
    have hbase_ge_one : 1 ≤ 1 + |x| := by
      nlinarith [abs_nonneg x]
    have hpow₁ :
        (1 + |x|) ^ N₁ ≤ (1 + |x|) ^ max N₁ N₂ := by
      exact pow_le_pow_right₀ hbase_ge_one (Nat.le_max_left _ _)
    have hpow₂ :
        (1 + |x|) ^ N₂ ≤ (1 + |x|) ^ max N₁ N₂ := by
      exact pow_le_pow_right₀ hbase_ge_one (Nat.le_max_right _ _)
    calc
      ‖HΔ (↑x + ↑η * Complex.I)‖
          ≤
        ‖bvt_W_conjTensorProduct_timeShiftCanonicalExtension
            (d := d) OS lgc f g hg_compact (↑x + ↑η * Complex.I)‖ +
          ‖OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single m g hg_ord)
              (-Complex.I * (↑x + ↑η * Complex.I))‖ := by
              simp [HΔ]
              exact norm_sub_le _ _
      _ ≤ C₁ * (1 + |x|) ^ N₁ + C₂ * (1 + |x|) ^ N₂ := by
            exact add_le_add (hbound₁ x) (hbound₂ x)
      _ ≤ C₁ * (1 + |x|) ^ max N₁ N₂ + C₂ * (1 + |x|) ^ max N₁ N₂ := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hpow₁ (le_of_lt hC₁))
              (mul_le_mul_of_nonneg_left hpow₂ (le_of_lt hC₂))
      _ = (C₁ + C₂) * (1 + |x|) ^ max N₁ N₂ := by ring
  have hC_open : IsOpen C := by
    simpa [C] using isOpen_lt continuous_const (continuous_apply 0)
  have hC_conv : Convex ℝ C := by
    intro x hx y hy a b ha hb hab
    dsimp [C] at hx hy ⊢
    change 0 < a * x 0 + b * y 0
    have hab_pos : 0 < a ∨ 0 < b := by
      by_cases ha0 : a = 0
      · right
        linarith
      · left
        exact lt_of_le_of_ne ha (Ne.symm ha0)
    cases hab_pos with
    | inl ha_pos =>
        exact add_pos_of_pos_of_nonneg (mul_pos ha_pos hx) (mul_nonneg hb (le_of_lt hy))
    | inr hb_pos =>
        exact add_pos_of_nonneg_of_pos (mul_nonneg ha (le_of_lt hx)) (mul_pos hb_pos hy)
  have hC_ne : C.Nonempty := by
    refine ⟨fun _ => 1, ?_⟩
    simp [C]
  have hC_cone : ∀ (t : ℝ), 0 < t → ∀ y ∈ C, t • y ∈ C := by
    intro t ht y hy
    dsimp [C] at hy ⊢
    simpa [Pi.smul_apply, smul_eq_mul] using mul_pos ht hy
  have hG_diff : DifferentiableOn ℂ G (SCV.TubeDomain C) := by
    have hmap :
        Set.MapsTo (fun z : Fin 1 → ℂ => z 0) (SCV.TubeDomain C) SCV.upperHalfPlane := by
      intro z hz
      simpa [C, SCV.TubeDomain, SCV.upperHalfPlane] using hz
    have hproj_diff :
        DifferentiableOn ℂ (fun z : Fin 1 → ℂ => z 0) (SCV.TubeDomain C) := by
      exact
        ((ContinuousLinearMap.differentiable
          (ContinuousLinearMap.proj (R := ℂ) (ι := Fin 1) (φ := fun _ => ℂ) 0)).differentiableOn)
    simpa [G] using hHΔ_diff.comp hproj_diff hmap
  have hG_int :
      ∀ y ∈ C, ∀ ψ : SchwartzMap (Fin 1 → ℝ) ℂ,
        MeasureTheory.Integrable
          (fun x : Fin 1 → ℝ =>
            G (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) * ψ x) := by
    intro y hy ψ
    let ψ₁ : SchwartzMap ℝ ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eR.symm ψ
    let χ : SchwartzMap ℝ ℂ := FourierTransform.fourierInv ψ₁
    have hy0 : 0 < y 0 := hy
    have hInt_can :
        MeasureTheory.Integrable
          (fun t : ℝ =>
            bvt_W_conjTensorProduct_timeShiftCanonicalExtension
              (d := d) OS lgc f g hg_compact (↑t + ↑(y 0) * Complex.I) *
            (SchwartzMap.fourierTransformCLM ℂ χ) t) := by
      exact
        integrable_mul_fourierTransform_of_bvt_W_conjTensorProduct_timeShiftCanonicalExtension
          (d := d) OS lgc f g hg_compact χ hy0
    have hInt_os :
        MeasureTheory.Integrable
          (fun t : ℝ =>
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n f hf_ord)
                (PositiveTimeBorchersSequence.single m g hg_ord)
                (-Complex.I * ((t : ℂ) + y 0 * Complex.I)) *
            (SchwartzMap.fourierTransformCLM ℂ χ) t) := by
      exact
        integrable_mul_fourierTransform_of_rotated_OSInnerProductTimeShiftHolomorphicValue
          (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single m g hg_ord) χ hy0
    have hInt₁ :
        MeasureTheory.Integrable
          (fun t : ℝ =>
            HΔ (↑t + ↑(y 0) * Complex.I) * (SchwartzMap.fourierTransformCLM ℂ χ) t) := by
      simpa [HΔ, sub_mul] using hInt_can.sub hInt_os
    have hInt₁' :
        MeasureTheory.Integrable
          (fun t : ℝ => HΔ (↑t + ↑(y 0) * Complex.I) * ψ₁ t) := by
      simpa [χ] using hInt₁
    let g₁ : (Fin 1 → ℝ) → ℂ := fun x =>
      G (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) * ψ x
    have hcomp :
        MeasureTheory.Integrable (fun t : ℝ => g₁ (eR.symm t)) := by
      simpa [g₁, G, HΔ, ψ₁, eR] using hInt₁'
    have hiff := hmp_eM.integrable_comp_emb eM.measurableEmbedding (g := g₁)
    exact hiff.1 hcomp
  have hG_bv_zero :
      ∀ (ψ : SchwartzMap (Fin 1 → ℝ) ℂ) (η : Fin 1 → ℝ), η ∈ C →
        Filter.Tendsto
          (fun ε : ℝ =>
            ∫ x : Fin 1 → ℝ,
              G (fun i => (x i : ℂ) + ε * (η i : ℂ) * Complex.I) * ψ x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds 0) := by
    intro ψ η hη
    let ψ₁ : SchwartzMap ℝ ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eR.symm ψ
    let χ : SchwartzMap ℝ ℂ := FourierTransform.fourierInv ψ₁
    have hη0 : 0 < η 0 := hη
    have hbase_can :
        Filter.Tendsto
          (fun s : ℝ =>
            ∫ t : ℝ,
              bvt_W_conjTensorProduct_timeShiftCanonicalExtension
                (d := d) OS lgc f g hg_compact (↑t + ↑s * Complex.I) * ψ₁ t)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (∫ t : ℝ,
              bvt_W OS lgc (n + m)
                (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) * ψ₁ t)) := by
      simpa using
        (tendsto_bvt_W_conjTensorProduct_timeShiftCanonicalExtension_boundaryValue
          (d := d) (OS := OS) (lgc := lgc) hm f g hg_compact ψ₁)
    have hbase_os :
        Filter.Tendsto
          (fun s : ℝ =>
            ∫ t : ℝ,
              OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                  (PositiveTimeBorchersSequence.single n f hf_ord)
                  (PositiveTimeBorchersSequence.single m g hg_ord)
                  (-Complex.I * ((t : ℂ) + s * Complex.I)) * ψ₁ t)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds
            (selfAdjointSpectralBoundaryValueOffdiag
              (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
              (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
              xF xG χ)) := by
      simpa [χ, xF, xG] using
        (tendsto_rotated_OSInnerProductTimeShiftHolomorphicValue_boundaryValue_fourierTransform
          (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single m g hg_ord) χ)
    have hbase :
        Filter.Tendsto
          (fun s : ℝ =>
            ∫ t : ℝ, HΔ (↑t + ↑s * Complex.I) * ψ₁ t)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds 0) := by
      have hsub := hbase_can.sub hbase_os
      have hEq :
          (fun s : ℝ =>
            (∫ t : ℝ,
              bvt_W_conjTensorProduct_timeShiftCanonicalExtension
                (d := d) OS lgc f g hg_compact (↑t + ↑s * Complex.I) * ψ₁ t) -
              ∫ t : ℝ,
                OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                    (PositiveTimeBorchersSequence.single n f hf_ord)
                    (PositiveTimeBorchersSequence.single m g hg_ord)
                    (-Complex.I * ((t : ℂ) + s * Complex.I)) * ψ₁ t) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
          (fun s : ℝ =>
            ∫ t : ℝ, HΔ (↑t + ↑s * Complex.I) * ψ₁ t) := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        have hInt_can_s :
            MeasureTheory.Integrable
              (fun t : ℝ =>
                bvt_W_conjTensorProduct_timeShiftCanonicalExtension
                  (d := d) OS lgc f g hg_compact (↑t + ↑s * Complex.I) * ψ₁ t) := by
          simpa [χ] using
            (integrable_mul_fourierTransform_of_bvt_W_conjTensorProduct_timeShiftCanonicalExtension
              (d := d) OS lgc f g hg_compact χ hs)
        have hInt_os_s :
            MeasureTheory.Integrable
              (fun t : ℝ =>
                OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                    (PositiveTimeBorchersSequence.single n f hf_ord)
                    (PositiveTimeBorchersSequence.single m g hg_ord)
                    (-Complex.I * ((t : ℂ) + s * Complex.I)) * ψ₁ t) := by
          simpa [χ] using
            (integrable_mul_fourierTransform_of_rotated_OSInnerProductTimeShiftHolomorphicValue
              (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single m g hg_ord) χ hs)
        rw [← MeasureTheory.integral_sub hInt_can_s hInt_os_s]
        simp [HΔ, sub_mul]
      have htarget :
          (∫ t : ℝ,
            bvt_W OS lgc (n + m)
              (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) * ψ₁ t) -
            selfAdjointSpectralBoundaryValueOffdiag
              (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
              (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
              xF xG χ = 0 := by
        have hBVχ :
            ∫ t : ℝ,
              bvt_W OS lgc (n + m)
                (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) * ψ₁ t =
              selfAdjointSpectralBoundaryValueOffdiag
                (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
                (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
                xF xG χ := by
          simpa [χ] using hBV' χ
        rw [hBVχ]
        simp
      have hsub0 :
          Filter.Tendsto
            (fun s : ℝ =>
              (∫ t : ℝ,
                bvt_W_conjTensorProduct_timeShiftCanonicalExtension
                  (d := d) OS lgc f g hg_compact (↑t + ↑s * Complex.I) * ψ₁ t) -
                ∫ t : ℝ,
                  OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                      (PositiveTimeBorchersSequence.single n f hf_ord)
                      (PositiveTimeBorchersSequence.single m g hg_ord)
                      (-Complex.I * ((t : ℂ) + s * Complex.I)) * ψ₁ t)
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds 0) := by
        simpa [htarget] using hsub
      exact hsub0.congr' hEq
    have hscale :
        Filter.Tendsto
          (fun ε : ℝ => ε * η 0)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhdsWithin 0 (Set.Ioi 0)) := by
      refine tendsto_nhdsWithin_iff.mpr ?_
      constructor
      · have hcontWithin :
            ContinuousWithinAt (fun ε : ℝ => ε * η 0) (Set.Ioi 0) 0 := by
          exact (continuous_id.mul continuous_const).continuousAt.continuousWithinAt
        simpa using hcontWithin.tendsto
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        simpa using mul_pos hε hη0
    have hscaled :
        Filter.Tendsto
          (fun ε : ℝ =>
            ∫ t : ℝ, HΔ (↑t + ↑(ε * η 0) * Complex.I) * ψ₁ t)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds 0) := hbase.comp hscale
    have hEq :
        (fun ε : ℝ =>
          ∫ x : Fin 1 → ℝ,
            G (fun i => (x i : ℂ) + ε * (η i : ℂ) * Complex.I) * ψ x) =
        (fun ε : ℝ =>
          ∫ t : ℝ,
            HΔ (↑t + ↑(ε * η 0) * Complex.I) * ψ₁ t) := by
      funext ε
      let g₁ : (Fin 1 → ℝ) → ℂ := fun x =>
        G (fun i => (x i : ℂ) + ε * (η i : ℂ) * Complex.I) * ψ x
      have hcov :
          ∫ t : ℝ, g₁ (eM t) = ∫ x : Fin 1 → ℝ, g₁ x := by
        simpa [eM] using (hmp_eM.integral_comp' (g := g₁))
      simpa [g₁, G, HΔ, ψ₁, eR, mul_assoc, mul_left_comm, mul_comm] using hcov.symm
    simpa [hEq] using hscaled
  have hzero := SCV.distributional_uniqueness_tube_of_zero_bv
    hC_open hC_conv hC_ne hC_cone hG_diff hG_int hG_bv_zero
  intro w hw
  have hw_tube : (fun _ => w) ∈ SCV.TubeDomain C := by
    simpa [C, SCV.TubeDomain] using hw
  have hzero_w := hzero (fun _ => w) hw_tube
  exact sub_eq_zero.mp (by simpa [G, HΔ] using hzero_w)

/-- Wightman-side Section-4.3 connection for the actual `ψ_{2πiη}` boundary
pairing: pairing the reconstructed real-time time-shift distribution against
`𝓕ψ_{2πiη}` is exactly the descended one-variable Section-4.3 Fourier pairing
of the canonical Wightman time-shift functional on the quotient class of
`ψ_{2πiη}`.

This is the direct flattened/time-shift functional surface needed before
comparing to the semigroup-side Section-4.3 scalar. -/
private theorem
    integral_bvt_W_conjTensorProduct_timeShift_mul_fourierTransform_psiZ_eq_fourierPairingDescendsToSection43PositiveEnergy1D
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    {η : ℝ} (hη : 0 < η) :
    ∫ t : ℝ,
      bvt_W OS lgc (n + m)
        (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) *
        (SchwartzMap.fourierTransformCLM ℂ
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) * (η * Complex.I)))
            (by
              simpa [Complex.mul_im, hη.ne']
                using mul_pos Real.two_pi_pos hη))) t =
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional
          (d := d) OS lgc f g hg_compact)
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
          (d := d) OS lgc hm f g hg_compact)
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) * (η * Complex.I)))
            (by
              simpa [Complex.mul_im, hη.ne']
                using mul_pos Real.two_pi_pos hη))) := by
  let T : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
    bvt_W_conjTensorProduct_timeShiftTemperedFunctional
      (d := d) OS lgc f g hg_compact
  let ψ : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (η * Complex.I)))
      (by
        simpa [Complex.mul_im, hη.ne']
          using mul_pos Real.two_pi_pos hη)
  have hT_apply :
      T ((SchwartzMap.fourierTransformCLM ℂ) ψ) =
        ∫ t : ℝ,
          bvt_W OS lgc (n + m)
            (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) *
            (SchwartzMap.fourierTransformCLM ℂ ψ) t := by
    simpa [T] using
      (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply
        (d := d) (OS := OS) (lgc := lgc) (f := f) (g := g)
        (hg_compact := hg_compact)
        ((SchwartzMap.fourierTransformCLM ℂ) ψ))
  have hDesc :
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
          T
          (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
            (d := d) OS lgc hm f g hg_compact)
          (section43PositiveEnergyQuotientMap1D ψ) =
        T ((SchwartzMap.fourierTransformCLM ℂ) ψ) := by
    simpa [T, ψ] using
      (OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D_apply
        (T := T)
        (hT_supp :=
          bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
            (d := d) OS lgc hm f g hg_compact)
        (f := ψ))
  calc
    ∫ t : ℝ,
      bvt_W OS lgc (n + m)
        (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) *
        (SchwartzMap.fourierTransformCLM ℂ
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) * (η * Complex.I)))
            (by
              simpa [Complex.mul_im, hη.ne']
                using mul_pos Real.two_pi_pos hη))) t
      = T ((SchwartzMap.fourierTransformCLM ℂ) ψ) := by
          simpa [ψ] using hT_apply.symm
    _ =
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        T
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
          (d := d) OS lgc hm f g hg_compact)
        (section43PositiveEnergyQuotientMap1D ψ) := hDesc.symm

/-- Wightman-side Section-4.3 connection on the actual Phase C' kernel: the
canonical ambient Stage-5 witness at `η i` is the descended one-variable
Section-4.3 Fourier pairing of the canonical Wightman time-shift functional on
the quotient class of `ψ_{2πiη}`.

This is the ambient counterpart of
`partialFourierSpatial_timeSliceCanonicalExtension_imagAxis_eq_fourierPairingDescendsToSection43PositiveEnergy1D_psiZ`:
both canonical witnesses now meet the same one-variable Section-4.3 codomain on
the same Paley-Wiener test family. -/
private theorem
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imagAxis_eq_fourierPairingDescendsToSection43PositiveEnergy1D_psiZ
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (g : SchwartzNPoint d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    {η : ℝ} (hη : 0 < η) :
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension
        (d := d) OS lgc f g hg_compact (η * Complex.I) =
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional
          (d := d) OS lgc f g hg_compact)
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
          (d := d) OS lgc hm f g hg_compact)
        (section43PositiveEnergyQuotientMap1D
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) * (η * Complex.I)))
            (by
              simpa [Complex.mul_im, hη.ne']
                using mul_pos Real.two_pi_pos hη))) := by
  let T : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
    bvt_W_conjTensorProduct_timeShiftTemperedFunctional
      (d := d) OS lgc f g hg_compact
  let ψ : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (η * Complex.I)))
      (by
        simpa [Complex.mul_im, hη.ne']
          using mul_pos Real.two_pi_pos hη)
  have hCanonical :
      bvt_W_conjTensorProduct_timeShiftCanonicalExtension
          (d := d) OS lgc f g hg_compact (η * Complex.I) =
        ∫ t : ℝ,
          bvt_W OS lgc (n + m)
            (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) *
            (SchwartzMap.fourierTransformCLM ℂ ψ) t := by
    simpa [ψ] using
      (bvt_W_conjTensorProduct_timeShiftCanonicalExtension_eq_fourierLaplaceIntegral
        (d := d) (OS := OS) (lgc := lgc) (f := f) (g := g)
        (hg_compact := hg_compact) hη)
  have hIntegral :
      ∫ t : ℝ,
          bvt_W OS lgc (n + m)
            (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) *
            (SchwartzMap.fourierTransformCLM ℂ ψ) t =
        OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
          T
          (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
            (d := d) OS lgc hm f g hg_compact)
          (section43PositiveEnergyQuotientMap1D ψ) := by
    simpa [T, ψ] using
      (integral_bvt_W_conjTensorProduct_timeShift_mul_fourierTransform_psiZ_eq_fourierPairingDescendsToSection43PositiveEnergy1D
        (d := d) (OS := OS) (lgc := lgc) (hm := hm) (f := f) (g := g)
        (hg_compact := hg_compact) hη)
  calc
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension
        (d := d) OS lgc f g hg_compact (η * Complex.I)
      =
        ∫ t : ℝ,
          bvt_W OS lgc (n + m)
            (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) *
            (SchwartzMap.fourierTransformCLM ℂ ψ) t := hCanonical
    _ =
      OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        T
        (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_hasOneSidedFourierSupport
          (d := d) OS lgc hm f g hg_compact)
        (section43PositiveEnergyQuotientMap1D ψ) := hIntegral


/-- Imaginary-axis corollary of the previous uniqueness assembly: once the
canonical Wightman boundary functional and the rotated OS spectral boundary
functional agree on Fourier transforms of Schwartz tests, the desired scalar
identity `canonical(t·I) = OS(t)` follows immediately. -/
private theorem
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imag_eq_osHolomorphicValue_of_boundaryValue_fourierTransform_eq
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hBV :
      let xF : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
        (⟦PositiveTimeBorchersSequence.single n f hf_ord⟧)) : OSHilbertSpace OS))
      let xG : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
        (⟦PositiveTimeBorchersSequence.single m g hg_ord⟧)) : OSHilbertSpace OS))
      ∀ χ : SchwartzMap ℝ ℂ,
        ∫ t : ℝ,
          bvt_W OS lgc (n + m)
            (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) *
            (SchwartzMap.fourierTransformCLM ℂ χ) t =
          selfAdjointSpectralBoundaryValueOffdiag
            (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
            (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
            xF xG χ) :
    ∀ t : ℝ, 0 < t →
      bvt_W_conjTensorProduct_timeShiftCanonicalExtension
        (d := d) OS lgc f g hg_compact ((t : ℂ) * Complex.I) =
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ) := by
  intro t ht
  have hEqOn :=
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension_eq_rotated_OS_of_boundaryValue_fourierTransform_eq
      (d := d) (OS := OS) (lgc := lgc) hm
      (f := f) (hf_ord := hf_ord)
      (g := g) (hg_ord := hg_ord) (hg_compact := hg_compact) hBV
  have ht_mem : ((t : ℂ) * Complex.I) ∈ SCV.upperHalfPlane := by
    simpa [SCV.upperHalfPlane] using ht
  have hEq := hEqOn ht_mem
  have hrot : -Complex.I * ((t : ℂ) * Complex.I) = (t : ℂ) := by
    ring_nf
    simp
  simpa [hrot] using hEq

/-- Route `3b-II` can be reduced one step further: if the explicit canonical
Wightman witness and the rotated OS holomorphic matrix element agree on the
positive imaginary axis, then their full one-variable boundary-value
functionals already agree on Fourier transforms of Schwartz tests.

This is a genuine blocker shrink, not a wrapper. The proof uses the
one-variable identity theorem to upgrade imag-axis equality to equality on the
entire upper half-plane, and then uniqueness of the boundary limit along
positive horizontal lines to identify the two boundary functionals. -/
private theorem
    bvt_W_conjTensorProduct_timeShift_boundaryValue_fourierTransform_eq_of_canonicalExtension_imag_eq_osHolomorphicValue
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hg_compact : HasCompactSupport (g : NPointDomain d m → ℂ))
    (hImag :
      ∀ t : ℝ, 0 < t →
        bvt_W_conjTensorProduct_timeShiftCanonicalExtension
          (d := d) OS lgc f g hg_compact ((t : ℂ) * Complex.I) =
        OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ)) :
    ∀ χ : SchwartzMap ℝ ℂ,
      ∫ t : ℝ,
        bvt_W OS lgc (n + m)
          (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) *
          (SchwartzMap.fourierTransformCLM ℂ χ) t =
      selfAdjointSpectralBoundaryValueOffdiag
        (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
        (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single n f hf_ord⟧)) : OSHilbertSpace OS))
        (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single m g hg_ord⟧)) : OSHilbertSpace OS))
        χ := by
  let xF : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    (⟦PositiveTimeBorchersSequence.single n f hf_ord⟧)) : OSHilbertSpace OS))
  let xG : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    (⟦PositiveTimeBorchersSequence.single m g hg_ord⟧)) : OSHilbertSpace OS))
  have hEqUHP :
      ∀ z : ℂ, 0 < z.im →
        bvt_W_conjTensorProduct_timeShiftCanonicalExtension
          (d := d) OS lgc f g hg_compact z =
        OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single m g hg_ord) (-Complex.I * z) := by
    exact
      identity_theorem_upperHalfPlane
        (f := bvt_W_conjTensorProduct_timeShiftCanonicalExtension
          (d := d) OS lgc f g hg_compact)
        (g := fun w =>
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single m g hg_ord)
            (-Complex.I * w))
        (hf := bvt_W_conjTensorProduct_timeShiftCanonicalExtension_differentiableOn
          (d := d) (OS := OS) (lgc := lgc) f g hg_compact)
        (hg := differentiableOn_rotated_OSInnerProductTimeShiftHolomorphicValue
          (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single m g hg_ord))
        (hagree := fun η hη => by
          have hrot : -Complex.I * ((η : ℂ) * Complex.I) = (η : ℂ) := by
            ring_nf
            simp
          simpa [hrot] using hImag η hη)
  have hEq :
      ∀ ψχ : SchwartzMap ℝ ℂ,
        (fun η : ℝ =>
          ∫ x : ℝ,
            bvt_W_conjTensorProduct_timeShiftCanonicalExtension
              (d := d) OS lgc f g hg_compact (↑x + ↑η * Complex.I) *
              (SchwartzMap.fourierTransformCLM ℂ ψχ) x)
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun η : ℝ =>
          ∫ x : ℝ,
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n f hf_ord)
                (PositiveTimeBorchersSequence.single m g hg_ord)
                (-Complex.I * ((x : ℂ) + η * Complex.I)) *
              (SchwartzMap.fourierTransformCLM ℂ ψχ) x) := by
    intro ψχ
    filter_upwards [self_mem_nhdsWithin] with η hη
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    have hw : 0 < ((x : ℂ) + η * Complex.I).im := by
      simpa using hη
    simpa [mul_assoc] using
      congrArg
        (fun z =>
          z * (SchwartzMap.fourierTransformCLM ℂ ψχ) x)
        (hEqUHP _ hw)
  intro ψχ
  have hCanonical :
      Filter.Tendsto
        (fun η : ℝ =>
          ∫ x : ℝ,
            bvt_W_conjTensorProduct_timeShiftCanonicalExtension
              (d := d) OS lgc f g hg_compact (↑x + ↑η * Complex.I) *
              (SchwartzMap.fourierTransformCLM ℂ ψχ) x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (∫ t : ℝ,
            bvt_W OS lgc (n + m)
              (f.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t g)) *
              (SchwartzMap.fourierTransformCLM ℂ ψχ) t)) := by
    simpa using
      tendsto_bvt_W_conjTensorProduct_timeShiftCanonicalExtension_boundaryValue
        (d := d) (OS := OS) (lgc := lgc) (hm := hm) f g hg_compact
        ((SchwartzMap.fourierTransformCLM ℂ) ψχ)
  have hOS :
      Filter.Tendsto
        (fun η : ℝ =>
          ∫ x : ℝ,
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n f hf_ord)
                (PositiveTimeBorchersSequence.single m g hg_ord)
                (-Complex.I * ((x : ℂ) + η * Complex.I)) *
              (SchwartzMap.fourierTransformCLM ℂ ψχ) x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (selfAdjointSpectralBoundaryValueOffdiag
            (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
            (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
            xF xG ψχ)) := by
    simpa [xF, xG] using
      tendsto_rotated_OSInnerProductTimeShiftHolomorphicValue_boundaryValue_fourierTransform
        (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord) ψχ
  have hCanonical' :
      Filter.Tendsto
        (fun η : ℝ =>
          ∫ x : ℝ,
            bvt_W_conjTensorProduct_timeShiftCanonicalExtension
              (d := d) OS lgc f g hg_compact (↑x + ↑η * Complex.I) *
              (SchwartzMap.fourierTransformCLM ℂ ψχ) x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (selfAdjointSpectralBoundaryValueOffdiag
            (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
            (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
            xF xG ψχ)) := by
    exact Filter.Tendsto.congr' (hEq ψχ).symm hOS
  exact tendsto_nhds_unique hCanonical hCanonical'

/-- Ambient/preimage boundary-value bridge for Phase C': if the canonical
upper-half-plane Wightman witness for ambient representatives `φ, ψ` agrees on
the positive imaginary axis with the semigroup-side OS matrix element built
from Euclidean preimages `f, g`, then the real-time Wightman boundary
functional of `φ, ψ` agrees with the OS spectral boundary functional of
`f, g` on Fourier transforms of Schwartz tests.

The proof is the same one-variable upper-half-plane identity plus uniqueness
of distributional boundary values used in the same-input bridge, but now on
the theorem surface required by the transformed-image positivity route. -/
private theorem
    bvt_W_conjTensorProduct_timeShift_boundaryValue_fourierTransform_eq_of_ambient_canonicalExtension_imag_eq_osHolomorphicValue
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d m)
    (hg_ord : tsupport (g : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (hImag :
      ∀ t : ℝ, 0 < t →
        bvt_W_conjTensorProduct_timeShiftCanonicalExtension
          (d := d) OS lgc φ ψ hψ_compact ((t : ℂ) * Complex.I) =
        OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single m g hg_ord) (t : ℂ)) :
    ∀ χ : SchwartzMap ℝ ℂ,
      ∫ t : ℝ,
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) *
          (SchwartzMap.fourierTransformCLM ℂ χ) t =
      selfAdjointSpectralBoundaryValueOffdiag
        (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
        (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single n f hf_ord⟧)) : OSHilbertSpace OS))
        (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single m g hg_ord⟧)) : OSHilbertSpace OS))
        χ := by
  let xF : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    (⟦PositiveTimeBorchersSequence.single n f hf_ord⟧)) : OSHilbertSpace OS))
  let xG : OSHilbertSpace OS := (((show OSPreHilbertSpace OS from
    (⟦PositiveTimeBorchersSequence.single m g hg_ord⟧)) : OSHilbertSpace OS))
  have hEqUHP :
      ∀ z : ℂ, 0 < z.im →
        bvt_W_conjTensorProduct_timeShiftCanonicalExtension
          (d := d) OS lgc φ ψ hψ_compact z =
        OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single m g hg_ord) (-Complex.I * z) := by
    exact
      identity_theorem_upperHalfPlane
        (f := bvt_W_conjTensorProduct_timeShiftCanonicalExtension
          (d := d) OS lgc φ ψ hψ_compact)
        (g := fun w =>
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single m g hg_ord)
            (-Complex.I * w))
        (hf := bvt_W_conjTensorProduct_timeShiftCanonicalExtension_differentiableOn
          (d := d) (OS := OS) (lgc := lgc) φ ψ hψ_compact)
        (hg := differentiableOn_rotated_OSInnerProductTimeShiftHolomorphicValue
          (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single m g hg_ord))
        (hagree := fun η hη => by
          have hrot : -Complex.I * ((η : ℂ) * Complex.I) = (η : ℂ) := by
            ring_nf
            simp
          simpa [hrot] using hImag η hη)
  have hEq :
      ∀ χ : SchwartzMap ℝ ℂ,
        (fun η : ℝ =>
          ∫ x : ℝ,
            bvt_W_conjTensorProduct_timeShiftCanonicalExtension
              (d := d) OS lgc φ ψ hψ_compact (↑x + ↑η * Complex.I) *
              (SchwartzMap.fourierTransformCLM ℂ χ) x)
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun η : ℝ =>
          ∫ x : ℝ,
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n f hf_ord)
                (PositiveTimeBorchersSequence.single m g hg_ord)
                (-Complex.I * ((x : ℂ) + η * Complex.I)) *
              (SchwartzMap.fourierTransformCLM ℂ χ) x) := by
    intro χ
    filter_upwards [self_mem_nhdsWithin] with η hη
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    have hw : 0 < ((x : ℂ) + η * Complex.I).im := by
      simpa using hη
    simpa [mul_assoc] using
      congrArg
        (fun z =>
          z * (SchwartzMap.fourierTransformCLM ℂ χ) x)
        (hEqUHP _ hw)
  intro χ
  have hCanonical :
      Filter.Tendsto
        (fun η : ℝ =>
          ∫ x : ℝ,
            bvt_W_conjTensorProduct_timeShiftCanonicalExtension
              (d := d) OS lgc φ ψ hψ_compact (↑x + ↑η * Complex.I) *
              (SchwartzMap.fourierTransformCLM ℂ χ) x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (∫ t : ℝ,
            bvt_W OS lgc (n + m)
              (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) *
              (SchwartzMap.fourierTransformCLM ℂ χ) t)) := by
    simpa using
      tendsto_bvt_W_conjTensorProduct_timeShiftCanonicalExtension_boundaryValue
        (d := d) (OS := OS) (lgc := lgc) (hm := hm) φ ψ hψ_compact
        ((SchwartzMap.fourierTransformCLM ℂ) χ)
  have hOS :
      Filter.Tendsto
        (fun η : ℝ =>
          ∫ x : ℝ,
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n f hf_ord)
                (PositiveTimeBorchersSequence.single m g hg_ord)
                (-Complex.I * ((x : ℂ) + η * Complex.I)) *
              (SchwartzMap.fourierTransformCLM ℂ χ) x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (selfAdjointSpectralBoundaryValueOffdiag
            (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
            (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
            xF xG χ)) := by
    simpa [xF, xG] using
      tendsto_rotated_OSInnerProductTimeShiftHolomorphicValue_boundaryValue_fourierTransform
        (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single m g hg_ord) χ
  have hCanonical' :
      Filter.Tendsto
        (fun η : ℝ =>
          ∫ x : ℝ,
            bvt_W_conjTensorProduct_timeShiftCanonicalExtension
              (d := d) OS lgc φ ψ hψ_compact (↑x + ↑η * Complex.I) *
              (SchwartzMap.fourierTransformCLM ℂ χ) x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (selfAdjointSpectralBoundaryValueOffdiag
            (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
            (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
            xF xG χ)) := by
    exact Filter.Tendsto.congr' (hEq χ).symm hOS
  exact tendsto_nhds_unique hCanonical hCanonical'

/-- One-dimensional horizontal Paley-Wiener kernel for the OS-route
shell-to-Laplace comparison. For any one-variable tempered functional `TW`,
the horizontal `x`-integral of `TW` applied to the Fourier-transformed
`ψ_{2π(x+εi)}` family is represented by pairing `TW` against a single
Schwartz test `χHorizontal`.

This is the genuine Fin1 Fubini packet used before applying the full flattened
time-shift theorem `exists_timeShiftKernel_pairing_fourierTest`. -/
private theorem exists_horizontalPaleyKernel_pairing_fourierTransform
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (TW : SchwartzMap ℝ ℂ →L[ℂ] ℂ) :
    let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
      SCV.schwartzPsiZ
        ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
        (by
          have hscaled : 0 < (2 * Real.pi) *
              (((x : ℂ) + ε * Complex.I).im) :=
            mul_pos Real.two_pi_pos (by simpa using hε)
          simpa [Complex.mul_im] using hscaled)
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    ∃ χHorizontal : SchwartzMap ℝ ℂ,
      (∀ τ : ℝ,
        χHorizontal τ =
          ∫ x : ℝ,
            (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) τ *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x) ∧
      TW χHorizontal =
        ∫ x : ℝ,
          TW (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) *
          (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
  classical
  let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
    SCV.schwartzPsiZ
      ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
      (by
        have hscaled : 0 < (2 * Real.pi) *
            (((x : ℂ) + ε * Complex.I).im) :=
          mul_pos Real.two_pi_pos (by simpa using hε)
        simpa [Complex.mul_im] using hscaled)
  let ψZt : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  let e1 : (Fin 1 → ℝ) ≃L[ℝ] ℝ :=
    ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ
  let toFin1 : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap (Fin 1 → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e1
  let fromFin1 : SchwartzMap (Fin 1 → ℝ) ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e1.symm
  let T1 : SchwartzMap (Fin 1 → ℝ) ℂ →L[ℂ] ℂ := TW.comp fromFin1
  let f1 : SchwartzMap (Fin 1 → ℝ) ℂ :=
    toFin1 ((SchwartzMap.fourierTransformCLM ℂ) ψZt)
  let g1 : (Fin 1 → ℝ) → SchwartzMap (Fin 1 → ℝ) ℂ := fun x1 =>
    toFin1 ((SchwartzMap.fourierTransformCLM ℂ) (ψZxε (e1 x1)))
  have hg1_cont : Continuous g1 := by
    simpa [g1, ψZxε, toFin1, e1] using
      (SCV.continuous_fin1_reindexed_fourierTransform_schwartzPsiZ_horizontal hε)
  have hg1_bound :
      ∀ (k n : ℕ), ∃ (C : ℝ) (N : ℕ), C > 0 ∧
        ∀ (x1 : Fin 1 → ℝ),
          SchwartzMap.seminorm ℝ k n (g1 x1) ≤ C * (1 + ‖x1‖) ^ N := by
    simpa [g1, ψZxε, toFin1, e1] using
      (SCV.seminorm_fin1_reindexed_fourierTransform_schwartzPsiZ_horizontal_growth hε)
  obtain ⟨χ1, hχ1_eval, hχ1_pair⟩ :=
    schwartz_clm_fubini_exchange T1 g1 f1 hg1_cont hg1_bound
  let χHorizontal : SchwartzMap ℝ ℂ := fromFin1 χ1
  let eM : ℝ ≃ᵐ (Fin 1 → ℝ) := e1.symm.toHomeomorph.toMeasurableEquiv
  have hmp_eM : MeasureTheory.MeasurePreserving eM MeasureTheory.volume MeasureTheory.volume := by
    simpa [eM, e1] using (MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm
  have hfrom_to :
      ∀ φ : SchwartzMap ℝ ℂ, fromFin1 (toFin1 φ) = φ := by
    intro φ
    ext x
    simp [fromFin1, toFin1, e1, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  refine ⟨χHorizontal, ?_, ?_⟩
  · intro τ
    let G : (Fin 1 → ℝ) → ℂ := fun x1 => g1 x1 (e1.symm τ) * f1 x1
    have hcov :
        ∫ x : ℝ, G (eM x) = ∫ x1 : Fin 1 → ℝ, G x1 := by
      simpa [eM] using (hmp_eM.integral_comp' (g := G))
    calc
      χHorizontal τ
          = χ1 (e1.symm τ) := by
              simp [χHorizontal, fromFin1, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
      _ = ∫ x1 : Fin 1 → ℝ, g1 x1 (e1.symm τ) * f1 x1 :=
            hχ1_eval (e1.symm τ)
      _ = ∫ x : ℝ,
            (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) τ *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
              rw [← hcov]
              apply MeasureTheory.integral_congr_ae
              filter_upwards with x
              simp [G, g1, f1, ψZxε, ψZt, toFin1, eM, e1,
                SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  · let G : (Fin 1 → ℝ) → ℂ := fun x1 => T1 (g1 x1) * f1 x1
    have hcov :
        ∫ x : ℝ, G (eM x) = ∫ x1 : Fin 1 → ℝ, G x1 := by
      simpa [eM] using (hmp_eM.integral_comp' (g := G))
    calc
      TW χHorizontal
          = T1 χ1 := by
              rfl
      _ = ∫ x1 : Fin 1 → ℝ, T1 (g1 x1) * f1 x1 :=
            hχ1_pair
      _ = ∫ x : ℝ,
            TW (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
              rw [← hcov]
              apply MeasureTheory.integral_congr_ae
              filter_upwards with x
              simp [G, T1, g1, f1, ψZxε, ψZt, hfrom_to, toFin1, fromFin1, eM, e1,
                SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

/-- Universal form of the one-dimensional horizontal Paley-Wiener kernel.
The kernel `χHorizontal` is characterized by its pointwise formula, so the
Fubini pairing identity holds for every one-variable continuous linear
functional, not only for the functional used to construct it. -/
private theorem exists_horizontalPaleyKernel_universal_pairing
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
      SCV.schwartzPsiZ
        ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
        (by
          have hscaled : 0 < (2 * Real.pi) *
              (((x : ℂ) + ε * Complex.I).im) :=
            mul_pos Real.two_pi_pos (by simpa using hε)
          simpa [Complex.mul_im] using hscaled)
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    ∃ χHorizontal : SchwartzMap ℝ ℂ,
      (∀ τ : ℝ,
        χHorizontal τ =
          ∫ x : ℝ,
            (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) τ *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x) ∧
      ∀ TW : SchwartzMap ℝ ℂ →L[ℂ] ℂ,
        TW χHorizontal =
          ∫ x : ℝ,
            TW (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
  classical
  let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
    SCV.schwartzPsiZ
      ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
      (by
        have hscaled : 0 < (2 * Real.pi) *
            (((x : ℂ) + ε * Complex.I).im) :=
          mul_pos Real.two_pi_pos (by simpa using hε)
        simpa [Complex.mul_im] using hscaled)
  let ψZt : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  obtain ⟨χHorizontal, hχ_eval, _hχ_pair_zero⟩ :=
    exists_horizontalPaleyKernel_pairing_fourierTransform
      (hε := hε) (ht := ht)
      (0 : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
  refine ⟨χHorizontal, ?_, ?_⟩
  · simpa [ψZxε, ψZt] using hχ_eval
  · intro TW
    obtain ⟨χTW, hχTW_eval, hχTW_pair⟩ :=
      exists_horizontalPaleyKernel_pairing_fourierTransform
        (hε := hε) (ht := ht) TW
    have hχTW_eq : χTW = χHorizontal := by
      ext τ
      calc
        χTW τ
            = ∫ x : ℝ,
                (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) τ *
                (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
                simpa [ψZxε, ψZt] using hχTW_eval τ
        _ = χHorizontal τ := by
                simpa [ψZxε, ψZt] using (hχ_eval τ).symm
    calc
      TW χHorizontal
          = TW χTW := by rw [hχTW_eq]
      _ = ∫ x : ℝ,
            TW (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
            simpa [ψZxε, ψZt] using hχTW_pair

/-- The one-variable oscillatory phase used to probe the horizontal Paley
kernel at a fixed flattened frequency has temperate growth. -/
private theorem horizontalPhase_temperate (lam : ℝ) :
    (fun τ : ℝ =>
      Complex.exp (-(Complex.I * (lam : ℂ) * (τ : ℂ)))).HasTemperateGrowth := by
  let c : ℂ := -(Complex.I * (lam : ℂ))
  suffices htemp : (fun τ : ℝ => Complex.exp (c * (τ : ℂ))).HasTemperateGrowth by
    convert htemp using 1
    ext τ
    simp [c, mul_assoc]
  refine ⟨?_, ?_⟩
  · have hlin : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun τ : ℝ => c * (τ : ℂ)) := by
      simpa using (contDiff_const.mul Complex.ofRealCLM.contDiff)
    exact Complex.contDiff_exp.comp hlin
  · intro n
    refine ⟨0, ‖c ^ n‖, fun τ => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hiter := congr_fun (SCV.iteratedDeriv_cexp_const_mul_real n c) τ
    rw [hiter]
    have hre : (c * (τ : ℂ)).re = 0 := by
      simp [c, Complex.mul_re]
    calc
      ‖c ^ n * Complex.exp (c * (τ : ℂ))‖ = ‖c ^ n‖ := by
        rw [norm_mul, Complex.norm_exp, hre, Real.exp_zero, mul_one]
      _ ≤ ‖c ^ n‖ * (1 + ‖τ‖) ^ 0 := by simp

/-- Fixed-frequency one-variable functional for the horizontal Paley kernel.
It pairs a Schwartz test with the oscillatory phase carrying frequency `lam`,
then multiplies by the frozen full-flat base Fourier factor. -/
private noncomputable def horizontalPhasePairingCLM
    (base : ℂ) (lam : ℝ) :
    SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
  base •
    ((SchwartzMap.integralCLM ℂ
      (MeasureTheory.volume : MeasureTheory.Measure ℝ)).comp
      (SchwartzMap.smulLeftCLM ℂ
        (fun τ : ℝ =>
          Complex.exp (-(Complex.I * (lam : ℂ) * (τ : ℂ))))))

private theorem horizontalPhasePairingCLM_apply
    (base : ℂ) (lam : ℝ) (χ : SchwartzMap ℝ ℂ) :
    horizontalPhasePairingCLM base lam χ =
      base *
        ∫ τ : ℝ,
          Complex.exp (-(Complex.I * (lam : ℂ) * (τ : ℂ))) * χ τ := by
  simp [horizontalPhasePairingCLM, SchwartzMap.integralCLM_apply,
    SchwartzMap.smulLeftCLM_apply_apply (horizontalPhase_temperate lam), smul_eq_mul]

private theorem horizontalPhasePairingCLM_fourierTransform
    (base : ℂ) (lam : ℝ) (χ : SchwartzMap ℝ ℂ) :
    horizontalPhasePairingCLM base lam
        ((SchwartzMap.fourierTransformCLM ℂ) χ) =
      base * χ (-lam / (2 * Real.pi)) := by
  rw [horizontalPhasePairingCLM_apply]
  rw [integral_phase_mul_fourierTransform_eq_eval]

/-- Fixed-frequency evaluation of the horizontal Paley kernel against the
oscillatory phase functional. This is the horizontal half of the finite-height
kernel comparison at a frozen flattened frequency. -/
private theorem exists_horizontalPaleyKernel_phasePairing
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (base : ℂ) (lam : ℝ) :
    let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
      SCV.schwartzPsiZ
        ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
        (by
          have hscaled : 0 < (2 * Real.pi) *
              (((x : ℂ) + ε * Complex.I).im) :=
            mul_pos Real.two_pi_pos (by simpa using hε)
          simpa [Complex.mul_im] using hscaled)
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    ∃ χHorizontal : SchwartzMap ℝ ℂ,
      (∀ τ : ℝ,
        χHorizontal τ =
          ∫ x : ℝ,
            (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) τ *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x) ∧
      horizontalPhasePairingCLM base lam χHorizontal =
        ∫ x : ℝ,
          (base * (ψZxε x) (-lam / (2 * Real.pi))) *
          (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
  classical
  let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
    SCV.schwartzPsiZ
      ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
      (by
        have hscaled : 0 < (2 * Real.pi) *
            (((x : ℂ) + ε * Complex.I).im) :=
          mul_pos Real.two_pi_pos (by simpa using hε)
        simpa [Complex.mul_im] using hscaled)
  let ψZt : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  obtain ⟨χHorizontal, hχ_eval, hχ_pair⟩ :=
    exists_horizontalPaleyKernel_universal_pairing (hε := hε) (ht := ht)
  refine ⟨χHorizontal, ?_, ?_⟩
  · simpa [ψZxε, ψZt] using hχ_eval
  · calc
      horizontalPhasePairingCLM base lam χHorizontal
          = ∫ x : ℝ,
              horizontalPhasePairingCLM base lam
                ((SchwartzMap.fourierTransformCLM ℂ) (ψZxε x)) *
              (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
              simpa [ψZxε, ψZt] using
                hχ_pair (horizontalPhasePairingCLM base lam)
      _ = ∫ x : ℝ,
            (base * (ψZxε x) (-lam / (2 * Real.pi))) *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            rw [horizontalPhasePairingCLM_fourierTransform]

/-- Collapse the remaining one-variable horizontal Paley integral after
freezing the oscillatory frequency. The result keeps the one-sided cutoffs
explicit; they are removed later from the dual-cone inequality `lam ≤ 0`. -/
private theorem horizontalPaley_phase_xIntegral_eq
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (base : ℂ) (lam : ℝ) :
    let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
      SCV.schwartzPsiZ
        ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
        (by
          have hscaled : 0 < (2 * Real.pi) *
              (((x : ℂ) + ε * Complex.I).im) :=
            mul_pos Real.two_pi_pos (by simpa using hε)
          simpa [Complex.mul_im] using hscaled)
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    ∫ x : ℝ,
      (base * (ψZxε x) (-lam / (2 * Real.pi))) *
      (SchwartzMap.fourierTransformCLM ℂ ψZt) x =
    base *
      ((SCV.smoothCutoff (-lam / (2 * Real.pi)) : ℂ) *
        Complex.exp (-(2 * Real.pi * ε : ℂ) * (-lam / (2 * Real.pi))) *
        ψZt (-lam / (2 * Real.pi))) := by
  classical
  let r : ℝ := -lam / (2 * Real.pi)
  let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
    SCV.schwartzPsiZ
      ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
      (by
        have hscaled : 0 < (2 * Real.pi) *
            (((x : ℂ) + ε * Complex.I).im) :=
          mul_pos Real.two_pi_pos (by simpa using hε)
        simpa [Complex.mul_im] using hscaled)
  let ψZt : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  have hψ_inv :
      FourierTransform.fourierInv
          ((SchwartzMap.fourierTransformCLM ℂ) ψZt) = ψZt := by
    simpa [ψZt] using (FourierTransform.fourierInv_fourier_eq ψZt)
  have hpair :
      (∫ x : ℝ,
          (ψZxε x) r *
          (SchwartzMap.fourierTransformCLM ℂ ψZt) x) =
        (SCV.smoothCutoff r : ℂ) *
          Complex.exp (-(2 * Real.pi * ε : ℂ) * r) *
          ψZt r := by
    calc
      (∫ x : ℝ,
          (ψZxε x) r *
          (SchwartzMap.fourierTransformCLM ℂ ψZt) x)
          = ∫ x : ℝ,
              SCV.psiZ ((2 * Real.pi : ℂ) * (x + ε * Complex.I)) r *
              (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with x
              simp [ψZxε]
      _ = (SCV.smoothCutoff r : ℂ) *
            Complex.exp (-(2 * Real.pi * ε : ℂ) * r) *
            FourierTransform.fourierInv
              ((SchwartzMap.fourierTransformCLM ℂ) ψZt) r :=
            SCV.psiZ_twoPi_pairing_formula
              (φ := (SchwartzMap.fourierTransformCLM ℂ ψZt))
              (η := ε) (ξ := r)
      _ = (SCV.smoothCutoff r : ℂ) *
            Complex.exp (-(2 * Real.pi * ε : ℂ) * r) *
            ψZt r := by rw [hψ_inv]
  have hmain :
      (∫ x : ℝ,
        (base * (ψZxε x) r) *
        (SchwartzMap.fourierTransformCLM ℂ ψZt) x) =
      base *
        ((SCV.smoothCutoff r : ℂ) *
          Complex.exp (-(2 * Real.pi * ε : ℂ) * r) *
          ψZt r) := by
    calc
      (∫ x : ℝ,
        (base * (ψZxε x) r) *
        (SchwartzMap.fourierTransformCLM ℂ ψZt) x)
          = ∫ x : ℝ,
              base * ((ψZxε x) r *
                (SchwartzMap.fourierTransformCLM ℂ ψZt) x) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with x
              ring
      _ = base *
            ∫ x : ℝ,
              (ψZxε x) r *
              (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
            simpa using
              (MeasureTheory.integral_const_mul
                (μ := MeasureTheory.volume) base
                (fun x : ℝ =>
                  (ψZxε x) r *
                  (SchwartzMap.fourierTransformCLM ℂ ψZt) x))
      _ = base *
            ((SCV.smoothCutoff r : ℂ) *
              Complex.exp (-(2 * Real.pi * ε : ℂ) * r) *
              ψZt r) := by rw [hpair]
  simpa [r, ψZxε, ψZt] using hmain

/-- Nonnegative-frequency form of `horizontalPaley_phase_xIntegral_eq`.
On the dual cone this applies because the tail time-shift direction pairs
nonpositively with every allowed frequency. -/
private theorem horizontalPaley_phase_xIntegral_eq_of_nonneg
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (base : ℂ) (lam : ℝ)
    (hr : 0 ≤ -lam / (2 * Real.pi)) :
    let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
      SCV.schwartzPsiZ
        ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
        (by
          have hscaled : 0 < (2 * Real.pi) *
              (((x : ℂ) + ε * Complex.I).im) :=
            mul_pos Real.two_pi_pos (by simpa using hε)
          simpa [Complex.mul_im] using hscaled)
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    ∫ x : ℝ,
      (base * (ψZxε x) (-lam / (2 * Real.pi))) *
      (SchwartzMap.fourierTransformCLM ℂ ψZt) x =
    base *
      (Complex.exp (-(2 * Real.pi * ε : ℂ) * (-lam / (2 * Real.pi))) *
       Complex.exp (-(2 * Real.pi * t : ℂ) * (-lam / (2 * Real.pi)))) := by
  classical
  let r : ℝ := -lam / (2 * Real.pi)
  let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
    SCV.schwartzPsiZ
      ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
      (by
        have hscaled : 0 < (2 * Real.pi) *
            (((x : ℂ) + ε * Complex.I).im) :=
          mul_pos Real.two_pi_pos (by simpa using hε)
        simpa [Complex.mul_im] using hscaled)
  let ψZt : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  have hr' : 0 ≤ r := by simpa [r] using hr
  have hcut : (SCV.smoothCutoff r : ℂ) = 1 := by
    exact_mod_cast SCV.smoothCutoff_one_of_nonneg hr'
  have hψt :
      ψZt r = Complex.exp (-(2 * Real.pi * t : ℂ) * (r : ℂ)) := by
    calc
      ψZt r
          = SCV.psiZ ((2 * Real.pi : ℂ) * (t * Complex.I)) r := by
              simp [ψZt]
      _ = Complex.exp
            (Complex.I * ((2 * Real.pi : ℂ) * (t * Complex.I)) * (r : ℂ)) := by
            rw [SCV.psiZ_eq_exp_of_nonneg hr']
      _ = Complex.exp (-(2 * Real.pi * t : ℂ) * (r : ℂ)) := by
            congr 1
            calc
              Complex.I * ((2 * Real.pi : ℂ) * (t * Complex.I)) * (r : ℂ)
                  = (Complex.I * Complex.I) *
                      ((2 * Real.pi * t : ℂ) * (r : ℂ)) := by ring
              _ = -(2 * Real.pi * t : ℂ) * (r : ℂ) := by
                    simp [Complex.I_mul_I]
  have hcollapse :=
    horizontalPaley_phase_xIntegral_eq (hε := hε) (ht := ht)
      (base := base) (lam := lam)
  have hmain :
      (∫ x : ℝ,
        (base * (ψZxε x) r) *
        (SchwartzMap.fourierTransformCLM ℂ ψZt) x) =
      base *
        (Complex.exp (-(2 * Real.pi * ε : ℂ) * (r : ℂ)) *
         Complex.exp (-(2 * Real.pi * t : ℂ) * (r : ℂ))) := by
    calc
      (∫ x : ℝ,
        (base * (ψZxε x) r) *
        (SchwartzMap.fourierTransformCLM ℂ ψZt) x)
          = base *
              ((SCV.smoothCutoff r : ℂ) *
                Complex.exp (-(2 * Real.pi * ε : ℂ) * (r : ℂ)) *
                ψZt r) := by
              simpa [r, ψZxε, ψZt] using hcollapse
      _ = base *
            (Complex.exp (-(2 * Real.pi * ε : ℂ) * (r : ℂ)) *
             Complex.exp (-(2 * Real.pi * t : ℂ) * (r : ℂ))) := by
            rw [hcut, hψt]
            ring
  simpa [r, ψZxε, ψZt] using hmain

/-- The frozen horizontal frequency `r = -lam/(2π)` is nonnegative on the
dual cone. This is exactly the sign input needed to remove the one-sided
Paley-Wiener cutoffs from the horizontal scalar. -/
private theorem horizontalPaley_frequency_nonneg_of_mem_dualCone
    {n m : ℕ}
    {ξ : Fin ((n + m) * (d + 1)) → ℝ}
    (hξ : ξ ∈ DualConeFlat
      ((flattenCLEquivReal (n + m) (d + 1)) '' ForwardConeAbs d (n + m))) :
    0 ≤ -(∑ i,
      (((OSReconstruction.castFinCLE
          (Nat.add_mul n m (d + 1)).symm)
        (OSReconstruction.zeroHeadBlockShift
          (m := n * (d + 1)) (n := m * (d + 1))
          (flatTimeShiftDirection d m))) i) * ξ i) / (2 * Real.pi) := by
  have hlam :=
    zeroHeadBlockShift_flatTimeShiftDirection_pairing_nonpos_of_mem_dualCone
      (d := d) (n := n) (m := m) (ξ := ξ) hξ
  have hden_nonneg : 0 ≤ 2 * Real.pi := Real.two_pi_pos.le
  refine div_nonneg ?_ hden_nonneg
  exact neg_nonneg.mpr (by simpa using hlam)

/-- Pointwise horizontal kernel scalar on the dual cone. This is the full
horizontal-side finite-height computation: the `τ`-kernel formula collapses to
the explicit Paley-Wiener damping scalar at each dual-cone frequency. -/
private theorem horizontalKernel_pointwise_eq_exp_of_mem_dualCone
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (χHorizontal : SchwartzMap ℝ ℂ)
    (KHorizontal : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ)
    (hχ_eval :
      ∀ τ : ℝ,
        χHorizontal τ =
          ∫ x : ℝ,
            (SchwartzMap.fourierTransformCLM ℂ
              (SCV.schwartzPsiZ
                ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
                (by
                  have hscaled : 0 < (2 * Real.pi) *
                      (((x : ℂ) + ε * Complex.I).im) :=
                    mul_pos Real.two_pi_pos (by simpa using hε)
                  simpa [Complex.mul_im] using hscaled))) τ *
            (SchwartzMap.fourierTransformCLM ℂ
              (SCV.schwartzPsiZ
                (((2 * Real.pi : ℂ) * (t * Complex.I)))
                (by
                  simpa [Complex.mul_im, ht.ne']
                    using mul_pos Real.two_pi_pos ht))) x)
    (hK_eval :
      ∀ ξ : Fin ((n + m) * (d + 1)) → ℝ,
        KHorizontal ξ =
          ∫ τ : ℝ,
            timeShiftFlatOrbit (d := d) φ ψ τ ξ * χHorizontal τ)
    {ξ : Fin ((n + m) * (d + 1)) → ℝ}
    (hξ : ξ ∈ DualConeFlat
      ((flattenCLEquivReal (n + m) (d + 1)) '' ForwardConeAbs d (n + m))) :
    let base : ℂ :=
      physicsFourierFlatCLM
        (OSReconstruction.reindexSchwartzFin
          (Nat.add_mul n m (d + 1)).symm
          (((_root_.flattenSchwartzNPoint (d := d) φ.borchersConj).tensorProduct
            (_root_.flattenSchwartzNPoint (d := d) ψ)))) ξ
    let lam : ℝ :=
      ∑ i,
        (((OSReconstruction.castFinCLE
            (Nat.add_mul n m (d + 1)).symm)
          (OSReconstruction.zeroHeadBlockShift
            (m := n * (d + 1)) (n := m * (d + 1))
            (flatTimeShiftDirection d m))) i) * ξ i
    KHorizontal ξ =
      base *
        (Complex.exp (-(2 * Real.pi * ε : ℂ) * (-lam / (2 * Real.pi))) *
         Complex.exp (-(2 * Real.pi * t : ℂ) * (-lam / (2 * Real.pi)))) := by
  classical
  let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
    SCV.schwartzPsiZ
      ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
      (by
        have hscaled : 0 < (2 * Real.pi) *
            (((x : ℂ) + ε * Complex.I).im) :=
          mul_pos Real.two_pi_pos (by simpa using hε)
        simpa [Complex.mul_im] using hscaled)
  let ψZt : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  let base : ℂ :=
    physicsFourierFlatCLM
      (OSReconstruction.reindexSchwartzFin
        (Nat.add_mul n m (d + 1)).symm
        (((_root_.flattenSchwartzNPoint (d := d) φ.borchersConj).tensorProduct
          (_root_.flattenSchwartzNPoint (d := d) ψ)))) ξ
  let lam : ℝ :=
    ∑ i,
      (((OSReconstruction.castFinCLE
          (Nat.add_mul n m (d + 1)).symm)
        (OSReconstruction.zeroHeadBlockShift
          (m := n * (d + 1)) (n := m * (d + 1))
          (flatTimeShiftDirection d m))) i) * ξ i
  have hχ_eval_local :
      ∀ τ : ℝ,
        χHorizontal τ =
          ∫ x : ℝ,
            (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) τ *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
    intro τ
    simpa [ψZxε, ψZt] using hχ_eval τ
  have hK_phase :
      KHorizontal ξ = horizontalPhasePairingCLM base lam χHorizontal := by
    calc
      KHorizontal ξ
          = ∫ τ : ℝ,
              timeShiftFlatOrbit (d := d) φ ψ τ ξ * χHorizontal τ :=
            hK_eval ξ
      _ = ∫ τ : ℝ,
            base *
              (Complex.exp (-(Complex.I * (lam : ℂ) * (τ : ℂ))) *
                χHorizontal τ) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with τ
            rw [timeShiftFlatOrbit_apply_phase]
            dsimp only [base, lam]
            ring
      _ = base *
            ∫ τ : ℝ,
              Complex.exp (-(Complex.I * (lam : ℂ) * (τ : ℂ))) *
                χHorizontal τ := by
            simpa using
              (MeasureTheory.integral_const_mul
                (μ := MeasureTheory.volume) base
                (fun τ : ℝ =>
                  Complex.exp (-(Complex.I * (lam : ℂ) * (τ : ℂ))) *
                    χHorizontal τ))
      _ = horizontalPhasePairingCLM base lam χHorizontal :=
            (horizontalPhasePairingCLM_apply base lam χHorizontal).symm
  obtain ⟨χPhase, hχPhase_eval, hχPhase_pair⟩ :=
    exists_horizontalPaleyKernel_phasePairing
      (hε := hε) (ht := ht) (base := base) (lam := lam)
  have hχPhase_eval_local :
      ∀ τ : ℝ,
        χPhase τ =
          ∫ x : ℝ,
            (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) τ *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
    intro τ
    simpa [ψZxε, ψZt] using hχPhase_eval τ
  have hχ_eq : χHorizontal = χPhase := by
    ext τ
    rw [hχ_eval_local τ, hχPhase_eval_local τ]
  have hr :
      0 ≤ -lam / (2 * Real.pi) := by
    simpa [lam] using
      (horizontalPaley_frequency_nonneg_of_mem_dualCone
        (d := d) (n := n) (m := m) (ξ := ξ) hξ)
  have hfinal :
      KHorizontal ξ =
        base *
          (Complex.exp (-(2 * Real.pi * ε : ℂ) * (-lam / (2 * Real.pi))) *
           Complex.exp (-(2 * Real.pi * t : ℂ) * (-lam / (2 * Real.pi)))) := by
    calc
      KHorizontal ξ
          = horizontalPhasePairingCLM base lam χHorizontal := hK_phase
      _ = horizontalPhasePairingCLM base lam χPhase := by rw [hχ_eq]
      _ = ∫ x : ℝ,
            (base * (ψZxε x) (-lam / (2 * Real.pi))) *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
            simpa [ψZxε, ψZt] using hχPhase_pair
      _ = base *
            (Complex.exp (-(2 * Real.pi * ε : ℂ) * (-lam / (2 * Real.pi))) *
             Complex.exp (-(2 * Real.pi * t : ℂ) * (-lam / (2 * Real.pi)))) := by
            simpa [ψZxε, ψZt] using
              (horizontalPaley_phase_xIntegral_eq_of_nonneg
                (hε := hε) (ht := ht) (base := base) (lam := lam) hr)
  simpa [base, lam] using hfinal

/-- Pointwise normal form for the explicit canonical Wightman witness on a
positive horizontal line: after unfolding `fourierLaplaceExt`, its value at
`x + η i` is the real-time Wightman time-shift tempered functional applied to
the Fourier transform of the Paley-Wiener kernel
`ψ_{2π(x+η i)}`.

This is a proof-local algebraic step toward the shell-to-Laplace comparison:
it exposes the inner Wightman time-shift integral that will later be related
to the explicit canonical `ξ`-shift shell. -/
private theorem
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension_horizontal_eq_fourierLaplaceIntegral
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    {η : ℝ} (hη : 0 < η) (x : ℝ) :
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension
        (d := d) OS lgc φ ψ hψ_compact ((x : ℂ) + η * Complex.I) =
      ∫ τ : ℝ,
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
        (SchwartzMap.fourierTransformCLM ℂ
          (SCV.schwartzPsiZ
            ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + η * Complex.I)))
            (by
              have hscaled : 0 < (2 * Real.pi) *
                  (((x : ℂ) + η * Complex.I).im) :=
                mul_pos Real.two_pi_pos (by simpa using hη)
              simpa [Complex.mul_im] using hscaled))) τ := by
  have hw : 0 < (((x : ℂ) + η * Complex.I).im) := by
    simpa using hη
  rw [bvt_W_conjTensorProduct_timeShiftCanonicalExtension, dif_pos hw]
  rw [SCV.fourierLaplaceExt_eq]
  change
    bvt_W_conjTensorProduct_timeShiftTemperedFunctional
        (d := d) OS lgc φ ψ hψ_compact
      ((SchwartzMap.fourierTransformCLM ℂ)
        (SCV.schwartzPsiZ
          ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + η * Complex.I)))
          (by
            have hscaled : 0 < (2 * Real.pi) *
                (((x : ℂ) + η * Complex.I).im) :=
              mul_pos Real.two_pi_pos (by simpa using hη)
            simpa [Complex.mul_im] using hscaled))) =
      ∫ τ : ℝ,
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
        (SchwartzMap.fourierTransformCLM ℂ
          (SCV.schwartzPsiZ
            ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + η * Complex.I)))
            (by
              have hscaled : 0 < (2 * Real.pi) *
                  (((x : ℂ) + η * Complex.I).im) :=
                mul_pos Real.two_pi_pos (by simpa using hη)
              simpa [Complex.mul_im] using hscaled))) τ
  exact
    bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply
      (d := d) (OS := OS) (lgc := lgc) (f := φ) (g := ψ)
      (hg_compact := hψ_compact)
      ((SchwartzMap.fourierTransformCLM ℂ)
        (SCV.schwartzPsiZ
          ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + η * Complex.I)))
          (by
            have hscaled : 0 < (2 * Real.pi) *
                (((x : ℂ) + η * Complex.I).im) :=
              mul_pos Real.two_pi_pos (by simpa using hη)
            simpa [Complex.mul_im] using hscaled)))

/-- Horizontal full-flat `Tflat` kernel packet. For finite positive height
`ε` and positive imaginary-axis target `t`, the canonical horizontal
Fourier-Laplace scalar is represented by the same full flattened distribution
`Tflat` as a single kernel `KHorizontal`.

The proof first constructs the one-dimensional Paley-Wiener test
`χHorizontal`, then feeds it into
`exists_timeShiftKernel_pairing_fourierTest`. -/
private theorem exists_horizontalKernel_pairing_iteratedFourierLaplace
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (Tflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_bv :
      ∀ φflat : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
        bvt_W OS lgc (n + m) (_root_.unflattenSchwartzNPoint (d := d) φflat) =
          Tflat (physicsFourierFlatCLM φflat)) :
    let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
      SCV.schwartzPsiZ
        ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
        (by
          have hscaled : 0 < (2 * Real.pi) *
              (((x : ℂ) + ε * Complex.I).im) :=
            mul_pos Real.two_pi_pos (by simpa using hε)
          simpa [Complex.mul_im] using hscaled)
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    ∃ χHorizontal : SchwartzMap ℝ ℂ,
      (∀ τ : ℝ,
        χHorizontal τ =
          ∫ x : ℝ,
            (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) τ *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x) ∧
      ∃ KHorizontal : SchwartzMap (Fin ((n + m) * (d + 1)) → ℝ) ℂ,
        (∀ ξ : Fin ((n + m) * (d + 1)) → ℝ,
          KHorizontal ξ =
            ∫ τ : ℝ,
              timeShiftFlatOrbit (d := d) φ ψ τ ξ * χHorizontal τ) ∧
        (∫ x : ℝ,
          bvt_W_conjTensorProduct_timeShiftCanonicalExtension
              (d := d) OS lgc φ ψ hψ_compact ((x : ℂ) + ε * Complex.I) *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x) =
          Tflat KHorizontal := by
  classical
  let ψZxε : ℝ → SchwartzMap ℝ ℂ := fun x =>
    SCV.schwartzPsiZ
      ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
      (by
        have hscaled : 0 < (2 * Real.pi) *
            (((x : ℂ) + ε * Complex.I).im) :=
          mul_pos Real.two_pi_pos (by simpa using hε)
        simpa [Complex.mul_im] using hscaled)
  let ψZt : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  let TW : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
    bvt_W_conjTensorProduct_timeShiftTemperedFunctional
      (d := d) OS lgc φ ψ hψ_compact
  obtain ⟨χHorizontal, hχ_eval, hχ_pairTW⟩ :=
    exists_horizontalPaleyKernel_pairing_fourierTransform
      (hε := hε) (ht := ht) TW
  obtain ⟨KHorizontal, hK_eval, hK_pair⟩ :=
    exists_timeShiftKernel_pairing_fourierTest
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (φ := φ) (ψ := ψ) (χ := χHorizontal)
      (Tflat := Tflat) hTflat_bv
  have hTW_point :
      ∀ x : ℝ,
        TW (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) =
          bvt_W_conjTensorProduct_timeShiftCanonicalExtension
            (d := d) OS lgc φ ψ hψ_compact ((x : ℂ) + ε * Complex.I) := by
    intro x
    calc
      TW (SchwartzMap.fourierTransformCLM ℂ (ψZxε x))
          =
        ∫ τ : ℝ,
          bvt_W OS lgc (n + m)
            (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
          (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) τ := by
            simpa [TW] using
              (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply
                (d := d) (OS := OS) (lgc := lgc)
                (f := φ) (g := ψ) (hg_compact := hψ_compact)
                ((SchwartzMap.fourierTransformCLM ℂ) (ψZxε x)))
      _ =
          bvt_W_conjTensorProduct_timeShiftCanonicalExtension
            (d := d) OS lgc φ ψ hψ_compact ((x : ℂ) + ε * Complex.I) := by
            simpa [ψZxε] using
              (bvt_W_conjTensorProduct_timeShiftCanonicalExtension_horizontal_eq_fourierLaplaceIntegral
                (d := d) (OS := OS) (lgc := lgc)
                (φ := φ) (ψ := ψ) (hψ_compact := hψ_compact) hε x).symm
  have hTWχ_apply :
      TW χHorizontal =
        ∫ τ : ℝ,
          bvt_W OS lgc (n + m)
            (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
          χHorizontal τ := by
    simpa [TW] using
      (bvt_W_conjTensorProduct_timeShiftTemperedFunctional_apply
        (d := d) (OS := OS) (lgc := lgc)
        (f := φ) (g := ψ) (hg_compact := hψ_compact) χHorizontal)
  refine ⟨χHorizontal, ?_, KHorizontal, hK_eval, ?_⟩
  · simpa [ψZxε, ψZt] using hχ_eval
  · calc
      (∫ x : ℝ,
          bvt_W_conjTensorProduct_timeShiftCanonicalExtension
              (d := d) OS lgc φ ψ hψ_compact ((x : ℂ) + ε * Complex.I) *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x)
          =
        ∫ x : ℝ,
          TW (SchwartzMap.fourierTransformCLM ℂ (ψZxε x)) *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            rw [hTW_point x]
      _ = TW χHorizontal := by
            simpa [ψZxε, ψZt] using hχ_pairTW.symm
      _ =
        ∫ τ : ℝ,
          bvt_W OS lgc (n + m)
            (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
          χHorizontal τ := hTWχ_apply
      _ = Tflat KHorizontal := hK_pair

/-- Outer-integral normal form for the canonical horizontal Fourier-Laplace
pairing. For fixed `t > 0`, the horizontal integral of the canonical witness
against `𝓕ψ_{2πit}` can be rewritten as an iterated real-time Wightman
time-shift integral whose inner Paley-Wiener kernel is `ψ_{2π(x+ηi)}`.

This does not perform the Fubini/Fourier-inversion step. It is the exact
normal form that the next shell-to-Laplace proof has to analyze. -/
private theorem
    integral_bvt_W_conjTensorProduct_timeShiftCanonicalExtension_horizontal_eq_iterated_fourierLaplaceIntegral
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    {t η : ℝ} (ht : 0 < t) (hη : 0 < η) :
    (∫ x : ℝ,
      bvt_W_conjTensorProduct_timeShiftCanonicalExtension
          (d := d) OS lgc φ ψ hψ_compact ((x : ℂ) + η * Complex.I) *
        (SchwartzMap.fourierTransformCLM ℂ
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) * (t * Complex.I)))
            (by
              simpa [Complex.mul_im, ht.ne']
                using mul_pos Real.two_pi_pos ht))) x)
      =
    ∫ x : ℝ,
      (∫ τ : ℝ,
        bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
        (SchwartzMap.fourierTransformCLM ℂ
          (SCV.schwartzPsiZ
            ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + η * Complex.I)))
            (by
              have hscaled : 0 < (2 * Real.pi) *
                  (((x : ℂ) + η * Complex.I).im) :=
                mul_pos Real.two_pi_pos (by simpa using hη)
              simpa [Complex.mul_im] using hscaled))) τ) *
        (SchwartzMap.fourierTransformCLM ℂ
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) * (t * Complex.I)))
            (by
              simpa [Complex.mul_im, ht.ne']
                using mul_pos Real.two_pi_pos ht))) x := by
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with x
  have hpt :=
    bvt_W_conjTensorProduct_timeShiftCanonicalExtension_horizontal_eq_fourierLaplaceIntegral
      (d := d) (OS := OS) (lgc := lgc)
      (φ := φ) (ψ := ψ) (hψ_compact := hψ_compact) hη x
  exact
    congrArg
      (fun z =>
        z *
          (SchwartzMap.fourierTransformCLM ℂ
            (SCV.schwartzPsiZ
              (((2 * Real.pi : ℂ) * (t * Complex.I)))
              (by
                simpa [Complex.mul_im, ht.ne']
                  using mul_pos Real.two_pi_pos ht))) x)
      hpt

/-- Pointwise shell-minus-horizontal normal form for the shell-to-Laplace seam.
After the previous lemma rewrites the canonical horizontal witness as an
iterated real-time Wightman integral, the remaining comparison is exactly the
difference between the explicit canonical `bvt_F` `ξ`-shell and that iterated
integral.

This is deliberately not a new end-stage conditional wrapper: it is the local
algebraic rewrite that exposes the next Fubini/Fourier-inversion target. -/
private theorem
    bvt_F_canonical_xiShift_shell_sub_horizontal_eq_shell_sub_iterated_fourierLaplaceIntegral
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    (∫ y : NPointDomain d (n + m),
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun k μ =>
              ↑(y k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                  Complex.I)
            (t : ℂ)) *
          (φ.conjTensorProduct ψ) y) -
      (∫ x : ℝ,
        bvt_W_conjTensorProduct_timeShiftCanonicalExtension
            (d := d) OS lgc φ ψ hψ_compact ((x : ℂ) + ε * Complex.I) *
          (SchwartzMap.fourierTransformCLM ℂ
            (SCV.schwartzPsiZ
              (((2 * Real.pi : ℂ) * (t * Complex.I)))
              (by
                simpa [Complex.mul_im, ht.ne']
                  using mul_pos Real.two_pi_pos ht))) x) =
    (∫ y : NPointDomain d (n + m),
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun k μ =>
              ↑(y k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                  Complex.I)
            (t : ℂ)) *
          (φ.conjTensorProduct ψ) y) -
      (∫ x : ℝ,
        (∫ τ : ℝ,
          bvt_W OS lgc (n + m)
            (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
          (SchwartzMap.fourierTransformCLM ℂ
            (SCV.schwartzPsiZ
              ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
              (by
                have hscaled : 0 < (2 * Real.pi) *
                    (((x : ℂ) + ε * Complex.I).im) :=
                  mul_pos Real.two_pi_pos (by simpa using hε)
                simpa [Complex.mul_im] using hscaled))) τ) *
          (SchwartzMap.fourierTransformCLM ℂ
            (SCV.schwartzPsiZ
              (((2 * Real.pi : ℂ) * (t * Complex.I)))
              (by
                simpa [Complex.mul_im, ht.ne']
                  using mul_pos Real.two_pi_pos ht))) x) := by
  rw [integral_bvt_W_conjTensorProduct_timeShiftCanonicalExtension_horizontal_eq_iterated_fourierLaplaceIntegral
    (d := d) (OS := OS) (lgc := lgc)
    (φ := φ) (ψ := ψ) (hψ_compact := hψ_compact) ht hε]

/-- The shell-minus-horizontal comparison has an unconditional residual limit:
the explicit `bvt_F` `ξ`-shell tends to the real-time shifted Wightman pairing,
while the canonical horizontal Fourier-Laplace integral tends to the canonical
witness value at `t i`. Thus their difference tends to the difference of those
two scalar targets.

This computes the exact scalar obstruction behind the shell-to-Laplace seam. -/
private theorem
    tendsto_bvt_F_canonical_xiShift_shell_sub_horizontal_to_timeShift_sub_canonicalExtension
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    {t : ℝ} (ht : 0 < t) :
    let ψZ : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I)
              (t : ℂ)) *
            (φ.conjTensorProduct ψ) y) -
        (∫ x : ℝ,
          bvt_W_conjTensorProduct_timeShiftCanonicalExtension
            (d := d) OS lgc φ ψ hψ_compact (↑x + ↑ε * Complex.I) *
          (SchwartzMap.fourierTransformCLM ℂ ψZ) x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) -
        bvt_W_conjTensorProduct_timeShiftCanonicalExtension
          (d := d) OS lgc φ ψ hψ_compact ((t : ℂ) * Complex.I))) := by
  let ψZ : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  let shell : ℝ → ℂ := fun ε =>
    ∫ y : NPointDomain d (n + m),
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
        (φ.conjTensorProduct ψ) y
  let horizontal : ℝ → ℂ := fun ε =>
    ∫ x : ℝ,
      bvt_W_conjTensorProduct_timeShiftCanonicalExtension
        (d := d) OS lgc φ ψ hψ_compact (↑x + ↑ε * Complex.I) *
      (SchwartzMap.fourierTransformCLM ℂ ψZ) x
  have hShell :
      Filter.Tendsto shell
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (bvt_W OS lgc (n + m)
            (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)))) := by
    simpa [shell] using
      (tendsto_bvt_F_canonical_xiShift_conjTensorProduct_timeShift_boundaryValue
        (d := d) (OS := OS) (lgc := lgc) (hm := hm)
        (φ := φ) (ψ := ψ) (t := t))
  have hHorizontal :
      Filter.Tendsto horizontal
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (bvt_W_conjTensorProduct_timeShiftCanonicalExtension
            (d := d) OS lgc φ ψ hψ_compact ((t : ℂ) * Complex.I))) := by
    simpa [horizontal, ψZ] using
      (tendsto_bvt_W_conjTensorProduct_timeShiftCanonicalExtension_to_imagAxis
        (d := d) (OS := OS) (lgc := lgc) (hm := hm)
        (f := φ) (g := ψ) (hg_compact := hψ_compact) ht)
  simpa [shell, horizontal, ψZ] using hShell.sub hHorizontal

/-- Eventual guarded normal form for the actual shell-minus-horizontal limit
function. On the punctured positive neighbourhood used by the boundary-value
filter, the horizontal canonical witness can be replaced by the explicit
iterated real-time Fourier-Laplace integral.

The `if hε : 0 < ε` guard only makes the right-hand side a total function of
`ε`; it disappears under `nhdsWithin 0 (Set.Ioi 0)`. -/
private theorem
    bvt_F_canonical_xiShift_shell_sub_horizontal_eventually_eq_shell_sub_iterated_fourierLaplaceIntegral
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    {t : ℝ} (ht : 0 < t) :
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    (fun ε : ℝ =>
      (∫ y : NPointDomain d (n + m),
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun k μ =>
              ↑(y k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                  Complex.I)
            (t : ℂ)) *
          (φ.conjTensorProduct ψ) y) -
      (∫ x : ℝ,
        bvt_W_conjTensorProduct_timeShiftCanonicalExtension
          (d := d) OS lgc φ ψ hψ_compact (↑x + ↑ε * Complex.I) *
        (SchwartzMap.fourierTransformCLM ℂ ψZt) x))
    =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
    (fun ε : ℝ =>
      (∫ y : NPointDomain d (n + m),
        bvt_F OS lgc (n + m)
          (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
            (fun k μ =>
              ↑(y k μ) +
                ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                  Complex.I)
            (t : ℂ)) *
          (φ.conjTensorProduct ψ) y) -
      if hε : 0 < ε then
        ∫ x : ℝ,
          (∫ τ : ℝ,
            bvt_W OS lgc (n + m)
              (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
            (SchwartzMap.fourierTransformCLM ℂ
              (SCV.schwartzPsiZ
                ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
                (by
                  have hscaled : 0 < (2 * Real.pi) *
                      (((x : ℂ) + ε * Complex.I).im) :=
                    mul_pos Real.two_pi_pos (by simpa using hε)
                  simpa [Complex.mul_im] using hscaled))) τ) *
          (SchwartzMap.fourierTransformCLM ℂ ψZt) x
      else
        0) := by
  let ψZt : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : 0 < ε := hε
  rw [dif_pos hεpos]
  simpa [ψZt] using
    bvt_F_canonical_xiShift_shell_sub_horizontal_eq_shell_sub_iterated_fourierLaplaceIntegral
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (φ := φ) (ψ := ψ) (hψ_compact := hψ_compact) ht hεpos

/-- The fully explicit shell-minus-iterated Fourier-Laplace expression has the
same residual limit as shell-minus-horizontal. Thus the concrete Fubini /
Fourier-inversion target is precisely to show this explicit residual tends to
zero, which is equivalent at the limit-target level to the missing scalar
time-interchange identity. -/
private theorem
    tendsto_bvt_F_canonical_xiShift_shell_sub_iterated_to_timeShift_sub_canonicalExtension
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    {t : ℝ} (ht : 0 < t) :
    let ψZt : SchwartzMap ℝ ℂ :=
      SCV.schwartzPsiZ
        (((2 * Real.pi : ℂ) * (t * Complex.I)))
        (by
          simpa [Complex.mul_im, ht.ne']
            using mul_pos Real.two_pi_pos ht)
    Filter.Tendsto
      (fun ε : ℝ =>
        (∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I)
              (t : ℂ)) *
            (φ.conjTensorProduct ψ) y) -
        if hε : 0 < ε then
          ∫ x : ℝ,
            (∫ τ : ℝ,
              bvt_W OS lgc (n + m)
                (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) τ ψ)) *
              (SchwartzMap.fourierTransformCLM ℂ
                (SCV.schwartzPsiZ
                  ((((2 * Real.pi : ℝ) : ℂ) * ((x : ℂ) + ε * Complex.I)))
                  (by
                    have hscaled : 0 < (2 * Real.pi) *
                        (((x : ℂ) + ε * Complex.I).im) :=
                      mul_pos Real.two_pi_pos (by simpa using hε)
                    simpa [Complex.mul_im] using hscaled))) τ) *
            (SchwartzMap.fourierTransformCLM ℂ ψZt) x
        else
          0)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (bvt_W OS lgc (n + m)
          (φ.conjTensorProduct (timeShiftSchwartzNPoint (d := d) t ψ)) -
        bvt_W_conjTensorProduct_timeShiftCanonicalExtension
          (d := d) OS lgc φ ψ hψ_compact ((t : ℂ) * Complex.I))) := by
  let ψZt : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  have hEq :=
    bvt_F_canonical_xiShift_shell_sub_horizontal_eventually_eq_shell_sub_iterated_fourierLaplaceIntegral
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (φ := φ) (ψ := ψ) (hψ_compact := hψ_compact) ht
  have hResidual :=
    tendsto_bvt_F_canonical_xiShift_shell_sub_horizontal_to_timeShift_sub_canonicalExtension
      (d := d) (OS := OS) (lgc := lgc) (hm := hm)
      (φ := φ) (ψ := ψ) (hψ_compact := hψ_compact) ht
  exact Filter.Tendsto.congr' hEq hResidual

/-- Exact shell-to-Laplace reduction for the ambient Phase C' witness.

For a fixed positive time `t`, the explicit canonical Wightman witness already
has a horizontal boundary-value limit against the Paley-Wiener kernel
`ψ_{2πit}`. Therefore, to prove that the concrete `bvt_F` canonical
`ξ`-shift shell converges to the same witness value, it is enough to prove that
the difference between that shell and the corresponding horizontal
Fourier-Laplace integral tends to zero.

This isolates the real remaining analytic comparison without changing the
theorem category: both terms are on the Wightman/ambient representative side
`φ, ψ`; no Schwinger/Wightman same-shell equality is asserted. -/
private theorem
    tendsto_bvt_F_canonical_xiShift_to_ambientCanonicalExtension_imagAxis_of_shell_sub_horizontal_tendsto_zero
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n m : ℕ} (hm : 0 < m)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m)
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d m → ℂ))
    {t : ℝ} (ht : 0 < t)
    (hShellLaplace :
      let ψZ : SchwartzMap ℝ ℂ :=
        SCV.schwartzPsiZ
          (((2 * Real.pi : ℂ) * (t * Complex.I)))
          (by
            simpa [Complex.mul_im, ht.ne']
              using mul_pos Real.two_pi_pos ht)
      Filter.Tendsto
        (fun ε : ℝ =>
          (∫ y : NPointDomain d (n + m),
            bvt_F OS lgc (n + m)
              (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
                (fun k μ =>
                  ↑(y k μ) +
                    ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                      Complex.I)
                (t : ℂ)) *
              (φ.conjTensorProduct ψ) y) -
          (∫ x : ℝ,
            bvt_W_conjTensorProduct_timeShiftCanonicalExtension
              (d := d) OS lgc φ ψ hψ_compact (↑x + ↑ε * Complex.I) *
            (SchwartzMap.fourierTransformCLM ℂ ψZ) x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0)) :
    Filter.Tendsto
      (fun ε : ℝ =>
        ∫ y : NPointDomain d (n + m),
          bvt_F OS lgc (n + m)
            (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
              (fun k μ =>
                ↑(y k μ) +
                  ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                    Complex.I)
              (t : ℂ)) *
            (φ.conjTensorProduct ψ) y)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (bvt_W_conjTensorProduct_timeShiftCanonicalExtension
          (d := d) OS lgc φ ψ hψ_compact ((t : ℂ) * Complex.I))) := by
  let ψZ : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  let shell : ℝ → ℂ := fun ε =>
    ∫ y : NPointDomain d (n + m),
      bvt_F OS lgc (n + m)
        (xiShift ⟨n, Nat.lt_add_of_pos_right hm⟩ 0
          (fun k μ =>
            ↑(y k μ) +
              ε * ↑(canonicalForwardConeDirection (d := d) (n + m) k μ) *
                Complex.I)
          (t : ℂ)) *
        (φ.conjTensorProduct ψ) y
  let horizontal : ℝ → ℂ := fun ε =>
    ∫ x : ℝ,
      bvt_W_conjTensorProduct_timeShiftCanonicalExtension
        (d := d) OS lgc φ ψ hψ_compact (↑x + ↑ε * Complex.I) *
      (SchwartzMap.fourierTransformCLM ℂ ψZ) x
  have hShellLaplace' :
      Filter.Tendsto
        (fun ε : ℝ => shell ε - horizontal ε)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
    simpa [shell, horizontal, ψZ] using hShellLaplace
  have hHorizontal :
      Filter.Tendsto horizontal
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (bvt_W_conjTensorProduct_timeShiftCanonicalExtension
            (d := d) OS lgc φ ψ hψ_compact ((t : ℂ) * Complex.I))) := by
    simpa [horizontal, ψZ] using
      (tendsto_bvt_W_conjTensorProduct_timeShiftCanonicalExtension_to_imagAxis
        (d := d) (OS := OS) (lgc := lgc) (hm := hm)
        (f := φ) (g := ψ) (hg_compact := hψ_compact) ht)
  have hsum :
      Filter.Tendsto
        (fun ε : ℝ => (shell ε - horizontal ε) + horizontal ε)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (0 +
            bvt_W_conjTensorProduct_timeShiftCanonicalExtension
              (d := d) OS lgc φ ψ hψ_compact ((t : ℂ) * Complex.I))) :=
    hShellLaplace'.add hHorizontal
  have hEq :
      (fun ε : ℝ => (shell ε - horizontal ε) + horizontal ε) = shell := by
    funext ε
    simp [shell, horizontal]
  simpa [hEq, shell] using hsum

/-- Equality of multivariate Section 4.3 quotient classes forces equality of
the associated one-variable slice tests on `[0,\infty)`, provided the frozen
background times are nonnegative. -/
private theorem partialFourierSpatial_timeSlice_eqOn_nonneg_of_transport_eq
    {n : ℕ}
    {f g : euclideanPositiveTimeSubmodule (d := d) n}
    (hfg : os1TransportComponent d n f = os1TransportComponent d n g)
    (r : Fin n) (t : Fin n → ℝ)
    (ht : ∀ i : Fin n, i ≠ r → 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    Set.EqOn
      ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ : SchwartzMap ℝ ℂ) : ℝ → ℂ)
      ((partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule g).1 r t ξ : SchwartzMap ℝ ℂ) : ℝ → ℂ)
      (Set.Ici (0 : ℝ)) := by
  have hregion :
      Set.EqOn ((f : euclideanPositiveTimeSubmodule (d := d) n) : NPointDomain d n → ℂ)
        ((g : euclideanPositiveTimeSubmodule (d := d) n) : NPointDomain d n → ℂ)
        (section43PositiveEnergyRegion d n) :=
    eqOn_region_of_section43PositiveEnergyQuotientMap_eq (d := d)
      (n := n) (f := (f : SchwartzNPoint d n)) (g := (g : SchwartzNPoint d n)) hfg
  intro s hs
  have hnonneg : ∀ i : Fin n, 0 ≤ Function.update t r s i := by
    intro i
    by_cases hi : i = r
    · subst hi
      simpa using hs
    · rw [Function.update_of_ne hi]
      exact ht i hi
  simpa [partialFourierSpatial_timeSliceSchwartz] using
    partialFourierSpatial_fun_eq_of_eqOn_section43PositiveEnergyRegion
      (d := d) (n := n) hregion (Function.update t r s) hnonneg ξ

/-- Therefore the one-variable quotient class of the branch-`3b` slice depends
only on the multivariate Section 4.3 quotient class. This is the concrete
slice-level descent step needed before the full iterated pairing theorem. -/
private theorem os1TransportOneVar_partialFourierSpatial_timeSlice_eq_of_transport_eq
    {n : ℕ}
    {f g : euclideanPositiveTimeSubmodule (d := d) n}
    (hfg : os1TransportComponent d n f = os1TransportComponent d n g)
    (r : Fin n) (t : Fin n → ℝ)
    (ht : ∀ i : Fin n, i ≠ r → 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    os1TransportOneVar
      (partialFourierSpatial_timeSliceTest (d := d) (n := n)
        (EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ) =
    os1TransportOneVar
      (partialFourierSpatial_timeSliceTest (d := d) (n := n)
        (EuclideanPositiveTimeComponent.ofSubmodule g) r t ξ) := by
  apply section43PositiveEnergyQuotientMap1D_eq_of_eqOn_nonneg
  exact partialFourierSpatial_timeSlice_eqOn_nonneg_of_transport_eq
    (d := d) (n := n) hfg r t ht ξ

/-- On the current support-restricted source, equality of multivariate
Section-4.3 classes forces equality of the actual one-variable branch-`3b`
slice Schwartz functions. On `[0,∞)` this is the quotient argument above; on
`(-∞,0)` both slices vanish by positive-time support. -/
private theorem partialFourierSpatial_timeSliceSchwartz_eq_of_transport_eq
    {n : ℕ}
    {f g : euclideanPositiveTimeSubmodule (d := d) n}
    (hfg : os1TransportComponent d n f = os1TransportComponent d n g)
    (r : Fin n) (t : Fin n → ℝ)
    (ht : ∀ i : Fin n, i ≠ r → 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d)) :
    partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
        (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ =
      partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
        (EuclideanPositiveTimeComponent.ofSubmodule g).1 r t ξ := by
  ext s
  by_cases hs : 0 ≤ s
  · exact partialFourierSpatial_timeSlice_eqOn_nonneg_of_transport_eq
      (d := d) (n := n) hfg r t ht ξ hs
  · have hf_zero :
      partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
        (EuclideanPositiveTimeComponent.ofSubmodule f).1 r t ξ s = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hsupp
      exact hs <|
        tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
          (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ hsupp
    have hg_zero :
        partialFourierSpatial_timeSliceSchwartz (d := d) (n := n)
          (EuclideanPositiveTimeComponent.ofSubmodule g).1 r t ξ s = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hsupp
      exact hs <|
        tsupport_partialFourierSpatial_timeSlice_subset_Ici_of_orderedPositiveTime
          (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule g) r t ξ hsupp
    simp [hf_zero, hg_zero]

/-- First concrete Stage-5 descended-pairing theorem: on the positive imaginary
axis, the canonical Section-4.3 slice extension depends only on the multivariate
quotient class. This is the honest current-code fragment of the blueprint's
`section43_iteratedSlice_descendedPairing`. -/
theorem section43_iteratedSlice_descendedPairing_imagAxis
    {n : ℕ}
    {f g : euclideanPositiveTimeSubmodule (d := d) n}
    (hfg : os1TransportComponent d n f = os1TransportComponent d n g)
    (r : Fin n) (t : Fin n → ℝ)
    (ht : ∀ i : Fin n, i ≠ r → 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    {η : ℝ} (hη : 0 < η) :
    partialFourierSpatial_timeSliceCanonicalExtension
        (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ
        (η * Complex.I) =
      partialFourierSpatial_timeSliceCanonicalExtension
        (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule g) r t ξ
        (η * Complex.I) := by
  rw [partialFourierSpatial_timeSliceCanonicalExtension_eq_complexLaplaceTransform
    (d := d) (n := n) (f := EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ hη]
  rw [partialFourierSpatial_timeSliceCanonicalExtension_eq_complexLaplaceTransform
    (d := d) (n := n) (f := EuclideanPositiveTimeComponent.ofSubmodule g) r t ξ hη]
  simpa [partialFourierSpatial_timeSliceSchwartz_eq_of_transport_eq
    (d := d) (n := n) hfg r t ht ξ]

/-- Full Stage-5 slice descent: once two multivariate positive-time inputs have
the same Section-4.3 quotient class, the canonical one-variable branch-`3b`
slice extensions agree on the entire upper half-plane. This upgrades the
previous imag-axis fragment by a one-variable identity theorem and does not use
any forbidden many-variable separate-analyticity shortcut. -/
theorem section43_iteratedSlice_descendedPairing
    {n : ℕ}
    {f g : euclideanPositiveTimeSubmodule (d := d) n}
    (hfg : os1TransportComponent d n f = os1TransportComponent d n g)
    (r : Fin n) (t : Fin n → ℝ)
    (ht : ∀ i : Fin n, i ≠ r → 0 ≤ t i)
    (ξ : EuclideanSpace ℝ (Fin n × Fin d))
    {w : ℂ} (hw : 0 < w.im) :
    partialFourierSpatial_timeSliceCanonicalExtension
        (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ w =
      partialFourierSpatial_timeSliceCanonicalExtension
        (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule g) r t ξ w := by
  exact
    identity_theorem_upperHalfPlane
      (f := partialFourierSpatial_timeSliceCanonicalExtension
        (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ)
      (g := partialFourierSpatial_timeSliceCanonicalExtension
        (d := d) (n := n) (EuclideanPositiveTimeComponent.ofSubmodule g) r t ξ)
      (hf := partialFourierSpatial_timeSliceCanonicalExtension_differentiableOn
        (d := d) (n := n) (f := EuclideanPositiveTimeComponent.ofSubmodule f) r t ξ)
      (hg := partialFourierSpatial_timeSliceCanonicalExtension_differentiableOn
        (d := d) (n := n) (f := EuclideanPositiveTimeComponent.ofSubmodule g) r t ξ)
      (hagree := fun η hη =>
        section43_iteratedSlice_descendedPairing_imagAxis
          (d := d) (n := n) hfg r t ht ξ hη)
      w hw

/-- The honest OS Hilbert-space vector determined by a positive-time Euclidean
Borchers sequence. Package I will later define the Minkowski-side transport map
by choosing a Euclidean preimage and landing in this existing vector. -/
noncomputable def positiveTimeBorchersVector
    (OS : OsterwalderSchraderAxioms d)
    (F : PositiveTimeBorchersSequence d) :
    OSHilbertSpace OS :=
  (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))

@[simp] theorem positiveTimeBorchersVector_inner_eq
    (OS : OsterwalderSchraderAxioms d)
    (F G : PositiveTimeBorchersSequence d) :
    @inner ℂ (OSHilbertSpace OS) _ (positiveTimeBorchersVector (d := d) OS F)
      (positiveTimeBorchersVector (d := d) OS G) =
      PositiveTimeBorchersSequence.osInner OS F G := by
  change @inner ℂ (OSHilbertSpace OS) _
      (((show OSPreHilbertSpace OS from (⟦F⟧)) : OSHilbertSpace OS))
      (((show OSPreHilbertSpace OS from (⟦G⟧)) : OSHilbertSpace OS)) =
      PositiveTimeBorchersSequence.osInner OS F G
  rw [UniformSpace.Completion.inner_coe]
  simp [OSPreHilbertSpace.inner_eq]

@[simp] theorem positiveTimeBorchersVector_norm_sq_eq
    (OS : OsterwalderSchraderAxioms d)
    (F : PositiveTimeBorchersSequence d) :
    ‖positiveTimeBorchersVector (d := d) OS F‖ ^ 2 =
      (PositiveTimeBorchersSequence.osInner OS F F).re := by
  have hnorm :
      RCLike.re
        (@inner ℂ (OSHilbertSpace OS) _ (positiveTimeBorchersVector (d := d) OS F)
          (positiveTimeBorchersVector (d := d) OS F)) =
        ‖positiveTimeBorchersVector (d := d) OS F‖ ^ 2 := by
    simpa using
      (inner_self_eq_norm_sq (𝕜 := ℂ) (positiveTimeBorchersVector (d := d) OS F))
  rw [← hnorm, positiveTimeBorchersVector_inner_eq]
  simp

theorem positiveTimeBorchersVector_self_nonneg
    (OS : OsterwalderSchraderAxioms d)
    (F : PositiveTimeBorchersSequence d) :
    0 ≤ ‖positiveTimeBorchersVector (d := d) OS F‖ ^ 2 := by
  rw [positiveTimeBorchersVector_norm_sq_eq]
  exact PositiveTimeBorchersSequence.osInner_nonneg_self OS F

/-- The positive-time Borchers vectors are dense in the completed OS Hilbert
space. This is the honest density input later used in Package I: it comes
for free from the quotient-completion construction and does not rely on any
Schwartz-space density theorem. -/
theorem positiveTimeBorchersVector_dense
    (OS : OsterwalderSchraderAxioms d) :
    Dense (Set.range (positiveTimeBorchersVector (d := d) OS)) := by
  have hrange :
      Set.range (positiveTimeBorchersVector (d := d) OS) =
        Set.range ((↑) : OSPreHilbertSpace OS → OSHilbertSpace OS) := by
    ext x
    constructor
    · rintro ⟨F, rfl⟩
      exact ⟨(⟦F⟧ : OSPreHilbertSpace OS), rfl⟩
    · rintro ⟨xpre, rfl⟩
      induction xpre using Quotient.inductionOn with
      | h F =>
          exact ⟨F, rfl⟩
  rw [hrange]
  exact UniformSpace.Completion.denseRange_coe

private theorem positiveTimeBorchersVector_eq_sum_single_vectors
    (OS : OsterwalderSchraderAxioms d)
    (F : PositiveTimeBorchersSequence d) :
    positiveTimeBorchersVector (d := d) OS F =
      ∑ k ∈ Finset.range (((F : BorchersSequence d).bound) + 1),
        positiveTimeBorchersVector (d := d) OS
          (PositiveTimeBorchersSequence.single k
            (((F : BorchersSequence d).funcs k)) (F.ordered_tsupport k)) := by
  unfold positiveTimeBorchersVector
  suffices h : ∀ (s : Finset ℕ) (G : PositiveTimeBorchersSequence d),
      (∀ k, k ∉ s → ((G : BorchersSequence d).funcs k) = 0) →
      (((show OSPreHilbertSpace OS from (⟦G⟧)) : OSHilbertSpace OS)) =
        ∑ k ∈ s,
          (((show OSPreHilbertSpace OS from
            (⟦PositiveTimeBorchersSequence.single k
              (((G : BorchersSequence d).funcs k)) (G.ordered_tsupport k)⟧)) :
            OSHilbertSpace OS)) from
    h (Finset.range (((F : BorchersSequence d).bound) + 1)) F (fun k hk =>
      (F : BorchersSequence d).bound_spec k (by
        simp only [Finset.mem_range, not_lt] at hk
        omega))
  intro s
  induction s using Finset.cons_induction with
  | empty =>
      intro G hG
      rw [Finset.sum_empty]
      have hpre :
          (⟦G⟧ : OSPreHilbertSpace OS) =
            (⟦(0 : PositiveTimeBorchersSequence d)⟧ : OSPreHilbertSpace OS) := by
        exact OSPreHilbertSpace.mk_eq_of_funcs_eq OS G 0
          (fun k => by simp [hG k (by simp)])
      simpa [UniformSpace.Completion.coe_zero] using
        congrArg (fun x : OSPreHilbertSpace OS => ((x : OSHilbertSpace OS))) hpre
  | cons a s ha ih =>
      intro G hG
      rw [Finset.sum_cons]
      let G' : PositiveTimeBorchersSequence d := {
        toBorchersSequence := {
          funcs := fun k => if k = a then 0 else ((G : BorchersSequence d).funcs k)
          bound := max ((G : BorchersSequence d).bound) a
          bound_spec := fun k hk => by
            show (if k = a then (0 : SchwartzNPoint d k)
              else (G : BorchersSequence d).funcs k) = 0
            split
            · rfl
            · next _hka => exact (G : BorchersSequence d).bound_spec k (by omega)
        }
        ordered_tsupport := fun k => by
          by_cases hka : k = a
          · intro x hx
            simp [hka] at hx
          · simpa [hka] using G.ordered_tsupport k
      }
      have hG'supp : ∀ k, k ∉ s → ((G' : BorchersSequence d).funcs k) = 0 := by
        intro k hk
        by_cases hka : k = a
        · subst hka
          simp [G']
        · simp [G', hka]
          exact hG k (fun hmem => (Finset.mem_cons.mp hmem).elim hka hk)
      have h_split :
          (⟦G⟧ : OSPreHilbertSpace OS) =
            (⟦(G' + PositiveTimeBorchersSequence.single a
              (((G : BorchersSequence d).funcs a)) (G.ordered_tsupport a))⟧ :
              OSPreHilbertSpace OS) := by
        apply OSPreHilbertSpace.mk_eq_of_funcs_eq OS
        intro k
        simp only [PositiveTimeBorchersSequence.add_toBorchersSequence,
          BorchersSequence.add_funcs, G']
        by_cases hka : k = a
        · subst hka
          simp [BorchersSequence.single_funcs_eq]
        · simp [hka, PositiveTimeBorchersSequence.single_toBorchersSequence]
      have hG'eq :
          (((show OSPreHilbertSpace OS from (⟦G'⟧)) : OSHilbertSpace OS)) =
            ∑ k ∈ s,
              (((show OSPreHilbertSpace OS from
                (⟦PositiveTimeBorchersSequence.single k
                  (((G : BorchersSequence d).funcs k)) (G.ordered_tsupport k)⟧)) :
                OSHilbertSpace OS)) := by
        rw [show ∑ k ∈ s,
              (((show OSPreHilbertSpace OS from
                (⟦PositiveTimeBorchersSequence.single k
                  (((G : BorchersSequence d).funcs k)) (G.ordered_tsupport k)⟧)) :
                OSHilbertSpace OS)) =
            ∑ k ∈ s,
              (((show OSPreHilbertSpace OS from
                (⟦PositiveTimeBorchersSequence.single k
                  (((G' : BorchersSequence d).funcs k)) (G'.ordered_tsupport k)⟧)) :
                OSHilbertSpace OS)) from by
          refine Finset.sum_congr rfl ?_
          intro k hk
          have hka : k ≠ a := by
            intro h
            exact ha (by simpa [h] using hk)
          simp [G', hka]]
        exact ih G' hG'supp
      have hcomm :
          (⟦(G' + PositiveTimeBorchersSequence.single a
            (((G : BorchersSequence d).funcs a)) (G.ordered_tsupport a))⟧ :
            OSPreHilbertSpace OS) =
          (⟦(PositiveTimeBorchersSequence.single a
            (((G : BorchersSequence d).funcs a)) (G.ordered_tsupport a) + G')⟧ :
            OSPreHilbertSpace OS) := by
        apply OSPreHilbertSpace.mk_eq_of_funcs_eq OS
        intro k
        simp [BorchersSequence.add_funcs, add_comm]
      rw [h_split, hcomm]
      let xpre : OSPreHilbertSpace OS :=
        ⟦PositiveTimeBorchersSequence.single a
          (((G : BorchersSequence d).funcs a)) (G.ordered_tsupport a)⟧
      let ypre : OSPreHilbertSpace OS := ⟦G'⟧
      change ((xpre + ypre : OSPreHilbertSpace OS) : OSHilbertSpace OS) =
        (xpre : OSHilbertSpace OS) +
          ∑ k ∈ s,
            (((show OSPreHilbertSpace OS from
              (⟦PositiveTimeBorchersSequence.single k
                (((G : BorchersSequence d).funcs k)) (G.ordered_tsupport k)⟧)) :
              OSHilbertSpace OS))
      rw [UniformSpace.Completion.coe_add, hG'eq]

/-- The degree-`n` Section 4.3 quotient-image carrier.

Warning: with the current production definition this is only the range of
`os1TransportComponent`, i.e. positive-time data viewed in the Section-4.3
quotient codomain. Membership in this set is not, by itself, the missing
paper Fourier-Laplace transform and must not be used to prove a Wightman/OS
scalar comparison. The latter still has to pass through an explicit
normal-form/transform theorem. -/
def bvtTransportImage (d n : ℕ) [NeZero d] :
    Set (Section43PositiveEnergyComponent (d := d) n) :=
  Set.range (os1TransportComponent d n)

/-- Additive closure of the transformed image. -/
theorem bvtTransportImage_add
    {n : ℕ} {f g : Section43PositiveEnergyComponent (d := d) n}
    (hf : f ∈ bvtTransportImage (d := d) n)
    (hg : g ∈ bvtTransportImage (d := d) n) :
    f + g ∈ bvtTransportImage (d := d) n := by
  rcases hf with ⟨f₀, rfl⟩
  rcases hg with ⟨g₀, rfl⟩
  exact ⟨f₀ + g₀, by simp [bvtTransportImage]⟩

/-- Scalar closure of the transformed image. -/
theorem bvtTransportImage_smul
    {n : ℕ} {c : ℂ} {f : Section43PositiveEnergyComponent (d := d) n}
    (hf : f ∈ bvtTransportImage (d := d) n) :
    c • f ∈ bvtTransportImage (d := d) n := by
  rcases hf with ⟨f₀, rfl⟩
  exact ⟨c • f₀, by simp [bvtTransportImage]⟩

/-- Finite Borchers data whose every component lies in the Section 4.3
transformed image. This is the honest current-code carrier for the later
on-image transport and Eq. `(4.28)` stages. -/
structure BvtTransportImageSequence (d : ℕ) [NeZero d] where
  toBorchers : BorchersSequence d
  image_mem : ∀ n,
    section43PositiveEnergyQuotientMap (d := d) n (toBorchers.funcs n) ∈
      bvtTransportImage (d := d) n

def positiveTimeBorchersSequence_toBvtTransportImageSequence
    (F : PositiveTimeBorchersSequence d) :
    BvtTransportImageSequence d where
  toBorchers := (F : BorchersSequence d)
  image_mem := fun n => by
    refine ⟨⟨((F : BorchersSequence d).funcs n), F.ordered_tsupport n⟩, ?_⟩
    simp [os1TransportComponent_apply]

instance : Add (BvtTransportImageSequence d) where
  add F G :=
    { toBorchers := F.toBorchers + G.toBorchers
      image_mem := fun n => by
        have hsum :=
            bvtTransportImage_add (d := d)
              (hf := F.image_mem n) (hg := G.image_mem n)
        simpa [BorchersSequence.add_funcs, map_add] using hsum }

instance : SMul ℂ (BvtTransportImageSequence d) where
  smul c F :=
    { toBorchers := c • F.toBorchers
      image_mem := fun n => by
        have hsmul :=
            bvtTransportImage_smul (d := d) (c := c) (hf := F.image_mem n)
        simpa [BorchersSequence.smul_funcs] using hsmul }

@[simp] theorem add_toBorchers
    (F G : BvtTransportImageSequence d) :
    (F + G).toBorchers = F.toBorchers + G.toBorchers := rfl

@[simp] theorem smul_toBorchers
    (c : ℂ) (F : BvtTransportImageSequence d) :
    (c • F).toBorchers = c • F.toBorchers := rfl

noncomputable def euclideanPositiveTimeSingleVector
    (OS : OsterwalderSchraderAxioms d)
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n) :
    OSHilbertSpace OS :=
  positiveTimeBorchersVector (d := d) OS
    (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d) f)

@[simp] theorem euclideanPositiveTimeSingleVector_norm_sq_eq
    (OS : OsterwalderSchraderAxioms d)
    {n : ℕ} (f : EuclideanPositiveTimeComponent d n) :
    ‖euclideanPositiveTimeSingleVector (d := d) OS f‖ ^ 2 =
      (PositiveTimeBorchersSequence.osInner OS
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d) f)
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d) f)).re := by
  simp [euclideanPositiveTimeSingleVector, positiveTimeBorchersVector_norm_sq_eq]

@[simp] theorem euclideanPositiveTimeSingleVector_ofSubmodule_add
    (OS : OsterwalderSchraderAxioms d)
    {n : ℕ} (f g : euclideanPositiveTimeSubmodule (d := d) n) :
    euclideanPositiveTimeSingleVector (d := d) OS
        (EuclideanPositiveTimeComponent.ofSubmodule (f + g)) =
      euclideanPositiveTimeSingleVector (d := d) OS
        (EuclideanPositiveTimeComponent.ofSubmodule f) +
      euclideanPositiveTimeSingleVector (d := d) OS
        (EuclideanPositiveTimeComponent.ofSubmodule g) := by
  have hpre :
      let xfg : OSPreHilbertSpace OS :=
        ⟦EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule (f + g))⟧
      let xf : OSPreHilbertSpace OS :=
        ⟦EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule f)⟧
      let xg : OSPreHilbertSpace OS :=
        ⟦EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule g)⟧
      xfg = xf + xg := by
    dsimp
    change (Quotient.mk (osBorchersSetoid OS)
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule (f + g))) :
          OSPreHilbertSpace OS) =
      (Quotient.mk (osBorchersSetoid OS)
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule f) +
         EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule g)) :
          OSPreHilbertSpace OS)
    apply OSPreHilbertSpace.mk_eq_of_funcs_eq
    intro m
    by_cases hm : m = n
    · subst hm
      simp [EuclideanPositiveTimeComponent.toPositiveTimeSingle,
        EuclideanPositiveTimeComponent.ofSubmodule, BorchersSequence.add_funcs]
    · simp [EuclideanPositiveTimeComponent.toPositiveTimeSingle,
        EuclideanPositiveTimeComponent.ofSubmodule,
        PositiveTimeBorchersSequence.single_toBorchersSequence,
        BorchersSequence.add_funcs, hm]
  simpa [euclideanPositiveTimeSingleVector, positiveTimeBorchersVector,
    UniformSpace.Completion.coe_add] using
    congrArg (fun x : OSPreHilbertSpace OS => ((x : OSHilbertSpace OS))) hpre

@[simp] theorem euclideanPositiveTimeSingleVector_ofSubmodule_smul
    (OS : OsterwalderSchraderAxioms d)
    {n : ℕ} (c : ℂ) (f : euclideanPositiveTimeSubmodule (d := d) n) :
    euclideanPositiveTimeSingleVector (d := d) OS
        (EuclideanPositiveTimeComponent.ofSubmodule (c • f)) =
      c • euclideanPositiveTimeSingleVector (d := d) OS
        (EuclideanPositiveTimeComponent.ofSubmodule f) := by
  have hpre :
      let xcf : OSPreHilbertSpace OS :=
        ⟦EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule (c • f))⟧
      let xf : OSPreHilbertSpace OS :=
        ⟦EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule f)⟧
      xcf = c • xf := by
    dsimp
    change (Quotient.mk (osBorchersSetoid OS)
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule (c • f))) :
          OSPreHilbertSpace OS) =
      (Quotient.mk (osBorchersSetoid OS)
        (c • EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule f)) :
          OSPreHilbertSpace OS)
    apply OSPreHilbertSpace.mk_eq_of_funcs_eq
    intro m
    by_cases hm : m = n
    · subst hm
      simp [EuclideanPositiveTimeComponent.toPositiveTimeSingle,
        EuclideanPositiveTimeComponent.ofSubmodule, BorchersSequence.smul_funcs]
    · simp [EuclideanPositiveTimeComponent.toPositiveTimeSingle,
        EuclideanPositiveTimeComponent.ofSubmodule,
        PositiveTimeBorchersSequence.single_toBorchersSequence,
        BorchersSequence.smul_funcs, hm]
  simpa [euclideanPositiveTimeSingleVector, positiveTimeBorchersVector,
    UniformSpace.Completion.coe_smul] using
    congrArg (fun x : OSPreHilbertSpace OS => ((x : OSHilbertSpace OS))) hpre

@[simp] theorem euclideanPositiveTimeSingleVector_ofSubmodule_zero
    (OS : OsterwalderSchraderAxioms d)
    {n : ℕ} :
    euclideanPositiveTimeSingleVector (d := d) OS
        (EuclideanPositiveTimeComponent.ofSubmodule
          (0 : euclideanPositiveTimeSubmodule (d := d) n)) = 0 := by
  have hpre :
      let x0 : OSPreHilbertSpace OS :=
        ⟦EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule
            (0 : euclideanPositiveTimeSubmodule (d := d) n))⟧
      x0 = 0 := by
    dsimp
    change (Quotient.mk (osBorchersSetoid OS)
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule
            (0 : euclideanPositiveTimeSubmodule (d := d) n))) :
          OSPreHilbertSpace OS) =
      (0 : OSPreHilbertSpace OS)
    apply OSPreHilbertSpace.mk_eq_of_funcs_eq
    intro m
    by_cases hm : m = n
    · subst hm
      simp [EuclideanPositiveTimeComponent.toPositiveTimeSingle,
        EuclideanPositiveTimeComponent.ofSubmodule]
    · simp [EuclideanPositiveTimeComponent.toPositiveTimeSingle,
        EuclideanPositiveTimeComponent.ofSubmodule,
        PositiveTimeBorchersSequence.single_toBorchersSequence, hm]
  simpa [euclideanPositiveTimeSingleVector, positiveTimeBorchersVector,
    UniformSpace.Completion.coe_zero] using
    congrArg (fun x : OSPreHilbertSpace OS => ((x : OSHilbertSpace OS))) hpre

private noncomputable def bvtTransportImagePreimage
    (F : BvtTransportImageSequence d) (n : ℕ) :
    euclideanPositiveTimeSubmodule (d := d) n :=
  Classical.choose (F.image_mem n)

@[simp] private theorem bvtTransportImagePreimage_spec
    (F : BvtTransportImageSequence d) (n : ℕ) :
    os1TransportComponent d n (bvtTransportImagePreimage (d := d) F n) =
      section43PositiveEnergyQuotientMap (d := d) n (F.toBorchers.funcs n) :=
  Classical.choose_spec (F.image_mem n)

/-- The Section 4.3 Hilbert transport on the transformed-image core. It is
defined by choosing a positive-time Euclidean preimage degreewise and summing
the resulting OS Hilbert vectors over the finite Borchers bound. -/
noncomputable def bvt_transport_to_osHilbert_onImage
    (OS : OsterwalderSchraderAxioms d)
    (F : BvtTransportImageSequence d) :
    OSHilbertSpace OS :=
  (Finset.range (F.toBorchers.bound + 1)).sum fun n =>
    euclideanPositiveTimeSingleVector (d := d) OS
      (EuclideanPositiveTimeComponent.ofSubmodule
        (bvtTransportImagePreimage (d := d) F n))

/-- The on-image transport does not depend on which positive-time Euclidean
preimage family is used to represent the transformed-image data. The proof uses
only `os1TransportComponent_injective`, not any density theorem. -/
theorem bvt_transport_to_osHilbert_onImage_wellDefined
    (OS : OsterwalderSchraderAxioms d)
    (F : BvtTransportImageSequence d)
    (g : ∀ n, euclideanPositiveTimeSubmodule (d := d) n)
    (hg : ∀ n,
      os1TransportComponent d n (g n) =
        section43PositiveEnergyQuotientMap (d := d) n (F.toBorchers.funcs n)) :
    bvt_transport_to_osHilbert_onImage OS F =
      (Finset.range (F.toBorchers.bound + 1)).sum fun n =>
        euclideanPositiveTimeSingleVector (d := d) OS
          (EuclideanPositiveTimeComponent.ofSubmodule (g n)) := by
  unfold bvt_transport_to_osHilbert_onImage
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hpre :
      bvtTransportImagePreimage (d := d) F n = g n := by
    apply os1TransportComponent_injective (d := d) (n := n)
    rw [bvtTransportImagePreimage_spec, hg]
  simp [hpre]

theorem bvt_transport_to_osHilbert_onImage_positiveTime
    (OS : OsterwalderSchraderAxioms d)
    (F : PositiveTimeBorchersSequence d) :
    bvt_transport_to_osHilbert_onImage OS
      (positiveTimeBorchersSequence_toBvtTransportImageSequence (d := d) F) =
    positiveTimeBorchersVector (d := d) OS F := by
  let G : BvtTransportImageSequence d :=
    positiveTimeBorchersSequence_toBvtTransportImageSequence (d := d) F
  let g : ∀ n, euclideanPositiveTimeSubmodule (d := d) n :=
    fun n => ⟨((F : BorchersSequence d).funcs n), F.ordered_tsupport n⟩
  have hg : ∀ n,
      os1TransportComponent d n (g n) =
        section43PositiveEnergyQuotientMap (d := d) n (G.toBorchers.funcs n) := by
    intro n
    simp [G, g, positiveTimeBorchersSequence_toBvtTransportImageSequence,
      os1TransportComponent_apply]
  rw [bvt_transport_to_osHilbert_onImage_wellDefined (d := d) (OS := OS)
    (F := G) (g := g) hg]
  simpa [G, g, euclideanPositiveTimeSingleVector, positiveTimeBorchersVector]
    using (positiveTimeBorchersVector_eq_sum_single_vectors (d := d) OS F).symm

/-- The Section 4.3 on-image transport has dense range in the OS Hilbert space:
the positive-time Borchers vectors are dense, and every such vector is the
transport of its componentwise Section 4.3 image. -/
theorem bvt_transport_to_osHilbert_onImage_dense
    (OS : OsterwalderSchraderAxioms d) :
    Dense (Set.range (bvt_transport_to_osHilbert_onImage (d := d) OS)) := by
  refine Dense.mono ?_ (positiveTimeBorchersVector_dense (d := d) OS)
  rintro _ ⟨F, rfl⟩
  exact ⟨positiveTimeBorchersSequence_toBvtTransportImageSequence (d := d) F,
    bvt_transport_to_osHilbert_onImage_positiveTime (d := d) OS F⟩

private theorem bvt_transport_to_osHilbert_onImage_eq_padded_sum
    (OS : OsterwalderSchraderAxioms d)
    (F : BvtTransportImageSequence d) {m : ℕ}
    (hm : F.toBorchers.bound ≤ m) :
    bvt_transport_to_osHilbert_onImage OS F =
      (Finset.range (m + 1)).sum fun n =>
        if h : n ≤ F.toBorchers.bound then
          euclideanPositiveTimeSingleVector (d := d) OS
            (EuclideanPositiveTimeComponent.ofSubmodule
              (bvtTransportImagePreimage (d := d) F n))
        else 0 := by
  let v : ℕ → OSHilbertSpace OS := fun n =>
    euclideanPositiveTimeSingleVector (d := d) OS
      (EuclideanPositiveTimeComponent.ofSubmodule
        (bvtTransportImagePreimage (d := d) F n))
  unfold bvt_transport_to_osHilbert_onImage
  have hprefix :
      (Finset.range (F.toBorchers.bound + 1)).sum
          (fun n => if h : n ≤ F.toBorchers.bound then v n else 0) =
        (Finset.range (F.toBorchers.bound + 1)).sum v := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hle : n ≤ F.toBorchers.bound := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    simp [v, hle]
  have hmdecomp : m + 1 = (F.toBorchers.bound + 1) + (m - F.toBorchers.bound) := by
    omega
  have htail :
      ((Finset.range (m - F.toBorchers.bound)).sum fun k =>
        if h : F.toBorchers.bound + 1 + k ≤ F.toBorchers.bound then
          v (F.toBorchers.bound + 1 + k)
        else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro k hk
    have hnot : ¬ F.toBorchers.bound + 1 + k ≤ F.toBorchers.bound := by
      omega
    simp [v, hnot]
  have hpad :
      (Finset.range (m + 1)).sum
          (fun n => if h : n ≤ F.toBorchers.bound then v n else 0) =
        (Finset.range (F.toBorchers.bound + 1)).sum
          (fun n => if h : n ≤ F.toBorchers.bound then v n else 0) := by
    rw [hmdecomp, Finset.sum_range_add, htail, add_zero]
  calc
    (Finset.range (F.toBorchers.bound + 1)).sum v =
      (Finset.range (F.toBorchers.bound + 1)).sum
        (fun n => if h : n ≤ F.toBorchers.bound then v n else 0) := by
          symm
          exact hprefix
    _ =
      (Finset.range (m + 1)).sum
        (fun n => if h : n ≤ F.toBorchers.bound then v n else 0) := by
          symm
          exact hpad

theorem bvt_transport_to_osHilbert_onImage_add
    (OS : OsterwalderSchraderAxioms d)
    (F G : BvtTransportImageSequence d) :
    bvt_transport_to_osHilbert_onImage OS (F + G) =
      bvt_transport_to_osHilbert_onImage OS F +
      bvt_transport_to_osHilbert_onImage OS G := by
  let m := max F.toBorchers.bound G.toBorchers.bound
  have hfg :
      ∀ n,
        os1TransportComponent d n
            ((if h : n ≤ F.toBorchers.bound then
                bvtTransportImagePreimage (d := d) F n
              else 0) +
              (if h : n ≤ G.toBorchers.bound then
                bvtTransportImagePreimage (d := d) G n
              else 0)) =
          section43PositiveEnergyQuotientMap (d := d) n
            ((F + G).toBorchers.funcs n) := by
    intro n
    have hspecF :
        section43PositiveEnergyQuotientMap (d := d) n
            (bvtTransportImagePreimage (d := d) F n : SchwartzNPoint d n) =
          section43PositiveEnergyQuotientMap (d := d) n (F.toBorchers.funcs n) := by
      simpa [os1TransportComponent_apply] using
        (bvtTransportImagePreimage_spec (d := d) F n)
    have hspecG :
        section43PositiveEnergyQuotientMap (d := d) n
            (bvtTransportImagePreimage (d := d) G n : SchwartzNPoint d n) =
          section43PositiveEnergyQuotientMap (d := d) n (G.toBorchers.funcs n) := by
      simpa [os1TransportComponent_apply] using
        (bvtTransportImagePreimage_spec (d := d) G n)
    by_cases hF : n ≤ F.toBorchers.bound
    · by_cases hG : n ≤ G.toBorchers.bound
      · simp [hF, hG, add_toBorchers, BorchersSequence.add_funcs, map_add,
          hspecF, hspecG]
      · have hGt : G.toBorchers.bound < n := by omega
        simp [hF, hG, G.toBorchers.bound_spec n hGt, add_toBorchers,
          BorchersSequence.add_funcs, map_add, hspecF]
    · have hFt : F.toBorchers.bound < n := by omega
      by_cases hG : n ≤ G.toBorchers.bound
      · simp [hF, hG, F.toBorchers.bound_spec n hFt, add_toBorchers,
          BorchersSequence.add_funcs, map_add, hspecG]
      · have hGt : G.toBorchers.bound < n := by omega
        simp [hF, hG, F.toBorchers.bound_spec n hFt, G.toBorchers.bound_spec n hGt,
          add_toBorchers, BorchersSequence.add_funcs, map_add]
  rw [bvt_transport_to_osHilbert_onImage_wellDefined (d := d) (OS := OS)
    (F := F + G) (g := fun n =>
      (if h : n ≤ F.toBorchers.bound then
        bvtTransportImagePreimage (d := d) F n
      else 0) +
      (if h : n ≤ G.toBorchers.bound then
        bvtTransportImagePreimage (d := d) G n
      else 0)) hfg]
  rw [bvt_transport_to_osHilbert_onImage_eq_padded_sum (d := d) (OS := OS)
    (F := F) (m := m) (by
      dsimp [m]
      exact le_max_left _ _)]
  rw [bvt_transport_to_osHilbert_onImage_eq_padded_sum (d := d) (OS := OS)
    (F := G) (m := m) (by
      dsimp [m]
      exact le_max_right _ _)]
  dsimp [m]
  have hsum :
      (Finset.range (max F.toBorchers.bound G.toBorchers.bound + 1)).sum
          (fun n =>
            euclideanPositiveTimeSingleVector (d := d) OS
              (EuclideanPositiveTimeComponent.ofSubmodule
                ((if h : n ≤ F.toBorchers.bound then
                    bvtTransportImagePreimage (d := d) F n
                  else 0) +
                  if h : n ≤ G.toBorchers.bound then
                    bvtTransportImagePreimage (d := d) G n
                  else 0))) =
        (Finset.range (max F.toBorchers.bound G.toBorchers.bound + 1)).sum
            (fun n =>
              (if h : n ≤ F.toBorchers.bound then
                euclideanPositiveTimeSingleVector (d := d) OS
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) F n))
              else 0) +
              if h : n ≤ G.toBorchers.bound then
                euclideanPositiveTimeSingleVector (d := d) OS
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) G n))
              else 0) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    by_cases hF : n ≤ F.toBorchers.bound
    · by_cases hG : n ≤ G.toBorchers.bound
      · simp [hF, hG, euclideanPositiveTimeSingleVector_ofSubmodule_add]
      · simp [hF, hG, euclideanPositiveTimeSingleVector_ofSubmodule_add,
          euclideanPositiveTimeSingleVector_ofSubmodule_zero]
    · by_cases hG : n ≤ G.toBorchers.bound
      · simp [hF, hG, euclideanPositiveTimeSingleVector_ofSubmodule_add,
          euclideanPositiveTimeSingleVector_ofSubmodule_zero]
      · simp [hF, hG, euclideanPositiveTimeSingleVector_ofSubmodule_add,
          euclideanPositiveTimeSingleVector_ofSubmodule_zero]
  calc
    (Finset.range (max F.toBorchers.bound G.toBorchers.bound + 1)).sum
        (fun n =>
          euclideanPositiveTimeSingleVector (d := d) OS
            (EuclideanPositiveTimeComponent.ofSubmodule
              ((if n ≤ F.toBorchers.bound then
                  bvtTransportImagePreimage (d := d) F n
                else 0) +
                if n ≤ G.toBorchers.bound then
                  bvtTransportImagePreimage (d := d) G n
                else 0))) =
      (Finset.range (max F.toBorchers.bound G.toBorchers.bound + 1)).sum
        (fun n =>
          (if h : n ≤ F.toBorchers.bound then
            euclideanPositiveTimeSingleVector (d := d) OS
              (EuclideanPositiveTimeComponent.ofSubmodule
                (bvtTransportImagePreimage (d := d) F n))
          else 0) +
          if h : n ≤ G.toBorchers.bound then
            euclideanPositiveTimeSingleVector (d := d) OS
              (EuclideanPositiveTimeComponent.ofSubmodule
                (bvtTransportImagePreimage (d := d) G n))
          else 0) := hsum
    _ = _ := by
      rw [Finset.sum_add_distrib]
      rfl

theorem bvt_transport_to_osHilbert_onImage_smul
    (OS : OsterwalderSchraderAxioms d)
    (c : ℂ) (F : BvtTransportImageSequence d) :
    bvt_transport_to_osHilbert_onImage OS (c • F) =
      c • bvt_transport_to_osHilbert_onImage OS F := by
  have hF :
      ∀ n,
        os1TransportComponent d n (c • bvtTransportImagePreimage (d := d) F n) =
          section43PositiveEnergyQuotientMap (d := d) n
            ((c • F).toBorchers.funcs n) := by
    intro n
    rw [map_smul, bvtTransportImagePreimage_spec]
    simp [smul_toBorchers, BorchersSequence.smul_funcs]
  rw [bvt_transport_to_osHilbert_onImage_wellDefined (d := d) (OS := OS)
    (F := c • F) (g := fun n => c • bvtTransportImagePreimage (d := d) F n) hF]
  simp [bvt_transport_to_osHilbert_onImage, Finset.smul_sum,
    euclideanPositiveTimeSingleVector_ofSubmodule_smul]

private theorem inner_bvt_transport_to_osHilbert_onImage_eq_double_sum
    (OS : OsterwalderSchraderAxioms d)
    (F G : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m) (hGm : G.toBorchers.bound ≤ m) :
    @inner ℂ (OSHilbertSpace OS) _
        (bvt_transport_to_osHilbert_onImage OS F)
        (bvt_transport_to_osHilbert_onImage OS G) =
      (Finset.range (m + 1)).sum fun n =>
        (Finset.range (m + 1)).sum fun k =>
          @inner ℂ (OSHilbertSpace OS) _
            (if h : n ≤ F.toBorchers.bound then
              euclideanPositiveTimeSingleVector (d := d) OS
                (EuclideanPositiveTimeComponent.ofSubmodule
                  (bvtTransportImagePreimage (d := d) F n))
            else 0)
            (if h : k ≤ G.toBorchers.bound then
              euclideanPositiveTimeSingleVector (d := d) OS
                (EuclideanPositiveTimeComponent.ofSubmodule
                  (bvtTransportImagePreimage (d := d) G k))
            else 0) := by
  rw [bvt_transport_to_osHilbert_onImage_eq_padded_sum (d := d) (OS := OS)
      (F := F) (m := m) hFm]
  rw [bvt_transport_to_osHilbert_onImage_eq_padded_sum (d := d) (OS := OS)
      (F := G) (m := m) hGm]
  rw [sum_inner]
  refine Finset.sum_congr rfl ?_
  intro n hn
  rw [inner_sum]

private theorem norm_sq_bvt_transport_to_osHilbert_onImage_eq_double_sum
    (OS : OsterwalderSchraderAxioms d)
    (F : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m) :
    ‖bvt_transport_to_osHilbert_onImage OS F‖ ^ 2 =
      ((Finset.range (m + 1)).sum fun n =>
        (Finset.range (m + 1)).sum fun k =>
          @inner ℂ (OSHilbertSpace OS) _
            (if h : n ≤ F.toBorchers.bound then
              euclideanPositiveTimeSingleVector (d := d) OS
                (EuclideanPositiveTimeComponent.ofSubmodule
                  (bvtTransportImagePreimage (d := d) F n))
            else 0)
            (if h : k ≤ F.toBorchers.bound then
              euclideanPositiveTimeSingleVector (d := d) OS
                (EuclideanPositiveTimeComponent.ofSubmodule
                  (bvtTransportImagePreimage (d := d) F k))
            else 0)).re := by
  have hnorm :
      RCLike.re
        (@inner ℂ (OSHilbertSpace OS) _
          (bvt_transport_to_osHilbert_onImage OS F)
          (bvt_transport_to_osHilbert_onImage OS F)) =
        ‖bvt_transport_to_osHilbert_onImage OS F‖ ^ 2 := by
    simpa using
      (inner_self_eq_norm_sq (𝕜 := ℂ) (bvt_transport_to_osHilbert_onImage OS F))
  rw [← hnorm, inner_bvt_transport_to_osHilbert_onImage_eq_double_sum
    (d := d) (OS := OS) (F := F) (G := F) (m := m) hFm hFm]
  have houter :
      RCLike.re
          ((Finset.range (m + 1)).sum fun n =>
            (Finset.range (m + 1)).sum fun k =>
              @inner ℂ (OSHilbertSpace OS) _
                (if h : n ≤ F.toBorchers.bound then
                  euclideanPositiveTimeSingleVector (d := d) OS
                    (EuclideanPositiveTimeComponent.ofSubmodule
                      (bvtTransportImagePreimage (d := d) F n))
                else 0)
                (if h : k ≤ F.toBorchers.bound then
                  euclideanPositiveTimeSingleVector (d := d) OS
                    (EuclideanPositiveTimeComponent.ofSubmodule
                      (bvtTransportImagePreimage (d := d) F k))
                else 0)) =
        (Finset.range (m + 1)).sum fun n =>
          RCLike.re
            ((Finset.range (m + 1)).sum fun k =>
              @inner ℂ (OSHilbertSpace OS) _
                (if h : n ≤ F.toBorchers.bound then
                  euclideanPositiveTimeSingleVector (d := d) OS
                    (EuclideanPositiveTimeComponent.ofSubmodule
                      (bvtTransportImagePreimage (d := d) F n))
                else 0)
                (if h : k ≤ F.toBorchers.bound then
                  euclideanPositiveTimeSingleVector (d := d) OS
                    (EuclideanPositiveTimeComponent.ofSubmodule
                      (bvtTransportImagePreimage (d := d) F k))
                else 0)) := by
    simpa using
      (Complex.re_sum (s := Finset.range (m + 1))
        (f := fun n =>
          (Finset.range (m + 1)).sum fun k =>
            @inner ℂ (OSHilbertSpace OS) _
              (if h : n ≤ F.toBorchers.bound then
                euclideanPositiveTimeSingleVector (d := d) OS
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) F n))
              else 0)
              (if h : k ≤ F.toBorchers.bound then
                euclideanPositiveTimeSingleVector (d := d) OS
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) F k))
              else 0)))
  rw [houter]
  have hinner :
      ∀ n,
        RCLike.re
            ((Finset.range (m + 1)).sum fun k =>
              @inner ℂ (OSHilbertSpace OS) _
                (if h : n ≤ F.toBorchers.bound then
                  euclideanPositiveTimeSingleVector (d := d) OS
                    (EuclideanPositiveTimeComponent.ofSubmodule
                      (bvtTransportImagePreimage (d := d) F n))
                else 0)
                (if h : k ≤ F.toBorchers.bound then
                  euclideanPositiveTimeSingleVector (d := d) OS
                    (EuclideanPositiveTimeComponent.ofSubmodule
                      (bvtTransportImagePreimage (d := d) F k))
                else 0)) =
          (Finset.range (m + 1)).sum fun k =>
            (@inner ℂ (OSHilbertSpace OS) _
              (if h : n ≤ F.toBorchers.bound then
                euclideanPositiveTimeSingleVector (d := d) OS
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) F n))
              else 0)
              (if h : k ≤ F.toBorchers.bound then
                euclideanPositiveTimeSingleVector (d := d) OS
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) F k))
              else 0)).re := by
    intro n
    simpa using
      (Complex.re_sum (s := Finset.range (m + 1))
        (f := fun k =>
          @inner ℂ (OSHilbertSpace OS) _
            (if h : n ≤ F.toBorchers.bound then
              euclideanPositiveTimeSingleVector (d := d) OS
                (EuclideanPositiveTimeComponent.ofSubmodule
                  (bvtTransportImagePreimage (d := d) F n))
            else 0)
            (if h : k ≤ F.toBorchers.bound then
              euclideanPositiveTimeSingleVector (d := d) OS
                (EuclideanPositiveTimeComponent.ofSubmodule
                  (bvtTransportImagePreimage (d := d) F k))
            else 0)))
  simpa [hinner]

private theorem inner_euclideanPositiveTimeSingleVector_ofSubmodule_eq_osInner
    (OS : OsterwalderSchraderAxioms d)
    {n k : ℕ}
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) k) :
    @inner ℂ (OSHilbertSpace OS) _
        (euclideanPositiveTimeSingleVector (d := d) OS
          (EuclideanPositiveTimeComponent.ofSubmodule f))
        (euclideanPositiveTimeSingleVector (d := d) OS
          (EuclideanPositiveTimeComponent.ofSubmodule g)) =
      PositiveTimeBorchersSequence.osInner OS
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule f))
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule g)) := by
  simp [euclideanPositiveTimeSingleVector, positiveTimeBorchersVector_inner_eq]

private theorem inner_bvt_transport_to_osHilbert_onImage_eq_osInner_padded_double_sum
    (OS : OsterwalderSchraderAxioms d)
    (F G : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m) (hGm : G.toBorchers.bound ≤ m) :
    @inner ℂ (OSHilbertSpace OS) _
        (bvt_transport_to_osHilbert_onImage OS F)
        (bvt_transport_to_osHilbert_onImage OS G) =
      (Finset.range (m + 1)).sum fun n =>
        (Finset.range (m + 1)).sum fun k =>
          if h₁ : n ≤ F.toBorchers.bound then
            if h₂ : k ≤ G.toBorchers.bound then
              PositiveTimeBorchersSequence.osInner OS
                (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) F n)))
                (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) G k)))
            else 0
          else 0 := by
  rw [inner_bvt_transport_to_osHilbert_onImage_eq_double_sum
    (d := d) (OS := OS) (F := F) (G := G) (m := m) hFm hGm]
  refine Finset.sum_congr rfl ?_
  intro n hn
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases h₁ : n ≤ F.toBorchers.bound
  · by_cases h₂ : k ≤ G.toBorchers.bound
    · simp [h₁, h₂,
        inner_euclideanPositiveTimeSingleVector_ofSubmodule_eq_osInner]
    · simp [h₁, h₂]
  · simp [h₁]

private theorem norm_sq_bvt_transport_to_osHilbert_onImage_eq_osInner_padded_double_sum
    (OS : OsterwalderSchraderAxioms d)
    (F : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m) :
    ‖bvt_transport_to_osHilbert_onImage OS F‖ ^ 2 =
      ((Finset.range (m + 1)).sum fun n =>
        (Finset.range (m + 1)).sum fun k =>
          if h₁ : n ≤ F.toBorchers.bound then
            if h₂ : k ≤ F.toBorchers.bound then
              PositiveTimeBorchersSequence.osInner OS
                (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) F n)))
                (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) F k)))
            else 0
          else 0).re := by
  rw [norm_sq_bvt_transport_to_osHilbert_onImage_eq_double_sum
    (d := d) (OS := OS) (F := F) (m := m) hFm]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro n hn
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases h₁ : n ≤ F.toBorchers.bound
  · by_cases h₂ : k ≤ F.toBorchers.bound
    · simp [h₁, h₂,
        inner_euclideanPositiveTimeSingleVector_ofSubmodule_eq_osInner]
    · simp [h₁, h₂]
  · simp [h₁]

private theorem bvt_wightmanInner_self_eq_padded_double_sum
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m) :
    WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers F.toBorchers =
      (Finset.range (m + 1)).sum fun n =>
        (Finset.range (m + 1)).sum fun k =>
          if h₁ : n ≤ F.toBorchers.bound then
            if h₂ : k ≤ F.toBorchers.bound then
              bvt_W OS lgc (n + k)
                ((F.toBorchers.funcs n).conjTensorProduct (F.toBorchers.funcs k))
            else 0
          else 0 := by
  have hw :
      WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers F.toBorchers =
        WightmanInnerProductN d (bvt_W OS lgc) F.toBorchers F.toBorchers
          (m + 1) (m + 1) := by
    apply WightmanInnerProduct_eq_extended (d := d) (W := bvt_W OS lgc)
      (hlin := bvt_W_linear (d := d) OS lgc)
    · exact Nat.succ_le_succ hFm
    · exact Nat.succ_le_succ hFm
  rw [hw]
  unfold WightmanInnerProductN
  refine Finset.sum_congr rfl ?_
  intro n hn
  by_cases hN : n ≤ F.toBorchers.bound
  · refine Finset.sum_congr rfl ?_
    intro k hk
    by_cases hK : k ≤ F.toBorchers.bound
    · simp [hN, hK]
    · have hkgt : F.toBorchers.bound < k := by omega
      simp [hN, hK, F.toBorchers.bound_spec k hkgt,
        (bvt_W_linear (d := d) OS lgc (n + k)).map_zero]
  · have hngt : F.toBorchers.bound < n := by omega
    simp [hN]
    apply Finset.sum_eq_zero
    intro k hk
    rw [F.toBorchers.bound_spec n hngt, SchwartzMap.conjTensorProduct_zero_left,
      (bvt_W_linear (d := d) OS lgc (n + k)).map_zero]

private theorem bvt_wightmanInner_self_eq_single_single_padded_double_sum
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m) :
    WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers F.toBorchers =
      (Finset.range (m + 1)).sum fun n =>
        (Finset.range (m + 1)).sum fun k =>
          if h₁ : n ≤ F.toBorchers.bound then
            if h₂ : k ≤ F.toBorchers.bound then
              WightmanInnerProduct d (bvt_W OS lgc)
                (BorchersSequence.single n (F.toBorchers.funcs n))
                (BorchersSequence.single k (F.toBorchers.funcs k))
            else 0
          else 0 := by
  rw [bvt_wightmanInner_self_eq_padded_double_sum
    (d := d) (OS := OS) (lgc := lgc) (F := F) (m := m) hFm]
  refine Finset.sum_congr rfl ?_
  intro n hn
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases h₁ : n ≤ F.toBorchers.bound
  · by_cases h₂ : k ≤ F.toBorchers.bound
    · have hsingle :=
        WightmanInnerProduct_single_single (d := d) (W := bvt_W OS lgc)
          (hlin := bvt_W_linear (d := d) OS lgc) (n := n) (m := k)
          (f := F.toBorchers.funcs n) (g := F.toBorchers.funcs k)
      simpa [h₁, h₂] using hsingle.symm
    · simp [h₁, h₂]
  · simp [h₁]

private theorem bvt_wightmanInner_eq_padded_double_sum
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m) (hGm : G.toBorchers.bound ≤ m) :
    WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers G.toBorchers =
      (Finset.range (m + 1)).sum fun n =>
        (Finset.range (m + 1)).sum fun k =>
          if h₁ : n ≤ F.toBorchers.bound then
            if h₂ : k ≤ G.toBorchers.bound then
              bvt_W OS lgc (n + k)
                ((F.toBorchers.funcs n).conjTensorProduct (G.toBorchers.funcs k))
            else 0
          else 0 := by
  have hw :
      WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers G.toBorchers =
        WightmanInnerProductN d (bvt_W OS lgc) F.toBorchers G.toBorchers
          (m + 1) (m + 1) := by
    apply WightmanInnerProduct_eq_extended (d := d) (W := bvt_W OS lgc)
      (hlin := bvt_W_linear (d := d) OS lgc)
    · exact Nat.succ_le_succ hFm
    · exact Nat.succ_le_succ hGm
  rw [hw]
  unfold WightmanInnerProductN
  refine Finset.sum_congr rfl ?_
  intro n hn
  by_cases hN : n ≤ F.toBorchers.bound
  · refine Finset.sum_congr rfl ?_
    intro k hk
    by_cases hK : k ≤ G.toBorchers.bound
    · simp [hN, hK]
    · have hkgt : G.toBorchers.bound < k := by omega
      simp [hN, hK, G.toBorchers.bound_spec k hkgt,
        (bvt_W_linear (d := d) OS lgc (n + k)).map_zero]
  · have hngt : F.toBorchers.bound < n := by omega
    simp [hN]
    apply Finset.sum_eq_zero
    intro k hk
    rw [F.toBorchers.bound_spec n hngt, SchwartzMap.conjTensorProduct_zero_left,
      (bvt_W_linear (d := d) OS lgc (n + k)).map_zero]

private theorem bvt_wightmanInner_eq_single_single_padded_double_sum
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m) (hGm : G.toBorchers.bound ≤ m) :
    WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers G.toBorchers =
      (Finset.range (m + 1)).sum fun n =>
        (Finset.range (m + 1)).sum fun k =>
          if h₁ : n ≤ F.toBorchers.bound then
            if h₂ : k ≤ G.toBorchers.bound then
              WightmanInnerProduct d (bvt_W OS lgc)
                (BorchersSequence.single n (F.toBorchers.funcs n))
                (BorchersSequence.single k (G.toBorchers.funcs k))
            else 0
          else 0 := by
  rw [bvt_wightmanInner_eq_padded_double_sum
    (d := d) (OS := OS) (lgc := lgc) (F := F) (G := G) (m := m) hFm hGm]
  refine Finset.sum_congr rfl ?_
  intro n hn
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases h₁ : n ≤ F.toBorchers.bound
  · by_cases h₂ : k ≤ G.toBorchers.bound
    · have hsingle :=
        WightmanInnerProduct_single_single (d := d) (W := bvt_W OS lgc)
          (hlin := bvt_W_linear (d := d) OS lgc) (n := n) (m := k)
          (f := F.toBorchers.funcs n) (g := G.toBorchers.funcs k)
      simpa [h₁, h₂] using hsingle.symm
    · simp [h₁, h₂]
  · simp [h₁]

private theorem single_single_wightman_eq_osInner_iff_kernel_eq
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    {n k : ℕ}
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d k)
    (f : euclideanPositiveTimeSubmodule (d := d) n)
    (g : euclideanPositiveTimeSubmodule (d := d) k) :
    WightmanInnerProduct d (bvt_W OS lgc)
        (BorchersSequence.single n φ)
        (BorchersSequence.single k ψ) =
      PositiveTimeBorchersSequence.osInner OS
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule f))
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule g))
      ↔
    bvt_W OS lgc (n + k) (φ.conjTensorProduct ψ) =
      OS.S (n + k)
        (ZeroDiagonalSchwartz.ofClassical
          ((f : SchwartzNPoint d n).osConjTensorProduct
            (g : SchwartzNPoint d k))) := by
  rw [WightmanInnerProduct_single_single (d := d) (W := bvt_W OS lgc)
      (hlin := bvt_W_linear (d := d) OS lgc) (n := n) (m := k)
      (f := φ) (g := ψ)]
  have hos :
      PositiveTimeBorchersSequence.osInner OS
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule f))
        (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
          (EuclideanPositiveTimeComponent.ofSubmodule g)) =
      OS.S (n + k)
        (ZeroDiagonalSchwartz.ofClassical
          ((f : SchwartzNPoint d n).osConjTensorProduct
            (g : SchwartzNPoint d k))) := by
    unfold PositiveTimeBorchersSequence.osInner
    simp [EuclideanPositiveTimeComponent.toPositiveTimeSingle,
      EuclideanPositiveTimeComponent.ofSubmodule, OSInnerProduct_single_single,
      OS.E0_linear]
  rw [hos]

private theorem bvt_wightmanInner_eq_transport_norm_sq_onImage_of_single_single
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m)
    (hss : ∀ n k,
      n ≤ F.toBorchers.bound →
      k ≤ F.toBorchers.bound →
      WightmanInnerProduct d (bvt_W OS lgc)
          (BorchersSequence.single n (F.toBorchers.funcs n))
          (BorchersSequence.single k (F.toBorchers.funcs k)) =
        PositiveTimeBorchersSequence.osInner OS
          (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
            (EuclideanPositiveTimeComponent.ofSubmodule
              (bvtTransportImagePreimage (d := d) F n)))
          (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
            (EuclideanPositiveTimeComponent.ofSubmodule
              (bvtTransportImagePreimage (d := d) F k)))) :
    (WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers F.toBorchers).re =
      ‖bvt_transport_to_osHilbert_onImage OS F‖ ^ 2 := by
  rw [bvt_wightmanInner_self_eq_single_single_padded_double_sum
    (d := d) (OS := OS) (lgc := lgc) (F := F) (m := m) hFm]
  rw [norm_sq_bvt_transport_to_osHilbert_onImage_eq_osInner_padded_double_sum
    (d := d) (OS := OS) (F := F) (m := m) hFm]
  have hsum :
      ((Finset.range (m + 1)).sum fun n =>
        (Finset.range (m + 1)).sum fun k =>
          if h₁ : n ≤ F.toBorchers.bound then
            if h₂ : k ≤ F.toBorchers.bound then
              WightmanInnerProduct d (bvt_W OS lgc)
                (BorchersSequence.single n (F.toBorchers.funcs n))
                (BorchersSequence.single k (F.toBorchers.funcs k))
            else 0
          else 0) =
      ((Finset.range (m + 1)).sum fun n =>
        (Finset.range (m + 1)).sum fun k =>
          if h₁ : n ≤ F.toBorchers.bound then
            if h₂ : k ≤ F.toBorchers.bound then
              PositiveTimeBorchersSequence.osInner OS
                (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) F n)))
                (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
                  (EuclideanPositiveTimeComponent.ofSubmodule
                    (bvtTransportImagePreimage (d := d) F k)))
            else 0
          else 0) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    refine Finset.sum_congr rfl ?_
    intro k hk
    by_cases h₁ : n ≤ F.toBorchers.bound
    · by_cases h₂ : k ≤ F.toBorchers.bound
      · simp [h₁, h₂, hss n k h₁ h₂]
      · simp [h₁, h₂]
    · simp [h₁]
  exact congrArg Complex.re hsum

private theorem bvt_wightmanInner_eq_transport_inner_onImage_of_single_single
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m) (hGm : G.toBorchers.bound ≤ m)
    (hss : ∀ n k,
      n ≤ F.toBorchers.bound →
      k ≤ G.toBorchers.bound →
      WightmanInnerProduct d (bvt_W OS lgc)
          (BorchersSequence.single n (F.toBorchers.funcs n))
          (BorchersSequence.single k (G.toBorchers.funcs k)) =
        PositiveTimeBorchersSequence.osInner OS
          (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
            (EuclideanPositiveTimeComponent.ofSubmodule
              (bvtTransportImagePreimage (d := d) F n)))
          (EuclideanPositiveTimeComponent.toPositiveTimeSingle (d := d)
            (EuclideanPositiveTimeComponent.ofSubmodule
              (bvtTransportImagePreimage (d := d) G k)))) :
    WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers G.toBorchers =
      @inner ℂ (OSHilbertSpace OS) _
        (bvt_transport_to_osHilbert_onImage OS F)
        (bvt_transport_to_osHilbert_onImage OS G) := by
  rw [bvt_wightmanInner_eq_single_single_padded_double_sum
    (d := d) (OS := OS) (lgc := lgc) (F := F) (G := G) (m := m) hFm hGm]
  rw [inner_bvt_transport_to_osHilbert_onImage_eq_osInner_padded_double_sum
    (d := d) (OS := OS) (F := F) (G := G) (m := m) hFm hGm]
  refine Finset.sum_congr rfl ?_
  intro n hn
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases h₁ : n ≤ F.toBorchers.bound
  · by_cases h₂ : k ≤ G.toBorchers.bound
    · simp [h₁, h₂, hss n k h₁ h₂]
    · simp [h₁, h₂]
  · simp [h₁]

theorem bvt_wightmanInner_eq_transport_inner_onImage_of_kernel_eq
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : BvtTransportImageSequence d)
    (hkernel : ∀ n k,
      n ≤ F.toBorchers.bound →
      k ≤ G.toBorchers.bound →
      bvt_W OS lgc (n + k)
        ((F.toBorchers.funcs n).conjTensorProduct (G.toBorchers.funcs k)) =
      OS.S (n + k)
        (ZeroDiagonalSchwartz.ofClassical
          (((bvtTransportImagePreimage (d := d) F n : euclideanPositiveTimeSubmodule (d := d) n) :
              SchwartzNPoint d n).osConjTensorProduct
            ((bvtTransportImagePreimage (d := d) G k : euclideanPositiveTimeSubmodule (d := d) k) :
              SchwartzNPoint d k)))) :
    WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers G.toBorchers =
      @inner ℂ (OSHilbertSpace OS) _
        (bvt_transport_to_osHilbert_onImage OS F)
        (bvt_transport_to_osHilbert_onImage OS G) := by
  let M := max F.toBorchers.bound G.toBorchers.bound
  apply bvt_wightmanInner_eq_transport_inner_onImage_of_single_single
    (d := d) (OS := OS) (lgc := lgc) (F := F) (G := G) (m := M)
  · dsimp [M]
    exact le_max_left _ _
  · dsimp [M]
    exact le_max_right _ _
  intro n k hn hk
  exact
    (single_single_wightman_eq_osInner_iff_kernel_eq
      (d := d) (OS := OS) (lgc := lgc)
      (φ := F.toBorchers.funcs n) (ψ := G.toBorchers.funcs k)
      (f := bvtTransportImagePreimage (d := d) F n)
      (g := bvtTransportImagePreimage (d := d) G k)).2
      (hkernel n k hn hk)

theorem bvt_wightmanInner_eq_transport_norm_sq_onImage_of_kernel_eq
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m)
    (hkernel : ∀ n k,
      n ≤ F.toBorchers.bound →
      k ≤ F.toBorchers.bound →
      bvt_W OS lgc (n + k)
        ((F.toBorchers.funcs n).conjTensorProduct (F.toBorchers.funcs k)) =
      OS.S (n + k)
        (ZeroDiagonalSchwartz.ofClassical
          (((bvtTransportImagePreimage (d := d) F n : euclideanPositiveTimeSubmodule (d := d) n) :
              SchwartzNPoint d n).osConjTensorProduct
            ((bvtTransportImagePreimage (d := d) F k : euclideanPositiveTimeSubmodule (d := d) k) :
              SchwartzNPoint d k)))) :
    (WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers F.toBorchers).re =
      ‖bvt_transport_to_osHilbert_onImage OS F‖ ^ 2 := by
  apply bvt_wightmanInner_eq_transport_norm_sq_onImage_of_single_single
    (d := d) (OS := OS) (lgc := lgc) (F := F) (m := m) hFm
  intro n k hn hk
  exact
    (single_single_wightman_eq_osInner_iff_kernel_eq
      (d := d) (OS := OS) (lgc := lgc)
      (φ := F.toBorchers.funcs n) (ψ := F.toBorchers.funcs k)
      (f := bvtTransportImagePreimage (d := d) F n)
      (g := bvtTransportImagePreimage (d := d) F k)).2
      (hkernel n k hn hk)

/-- Once the Stage-5 matrix-element kernel equality is available on the
transformed-image carrier, positivity on that carrier is immediate: the
reconstructed Wightman quadratic form is already identified with the square
norm of the transported OS Hilbert-space vector. -/
theorem bvt_wightmanInner_self_nonneg_onImage_of_kernel_eq
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BvtTransportImageSequence d) {m : ℕ}
    (hFm : F.toBorchers.bound ≤ m)
    (hkernel : ∀ n k,
      n ≤ F.toBorchers.bound →
      k ≤ F.toBorchers.bound →
      bvt_W OS lgc (n + k)
        ((F.toBorchers.funcs n).conjTensorProduct (F.toBorchers.funcs k)) =
      OS.S (n + k)
        (ZeroDiagonalSchwartz.ofClassical
          (((bvtTransportImagePreimage (d := d) F n : euclideanPositiveTimeSubmodule (d := d) n) :
              SchwartzNPoint d n).osConjTensorProduct
            ((bvtTransportImagePreimage (d := d) F k : euclideanPositiveTimeSubmodule (d := d) k) :
              SchwartzNPoint d k)))) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc) F.toBorchers F.toBorchers).re := by
  rw [bvt_wightmanInner_eq_transport_norm_sq_onImage_of_kernel_eq
    (d := d) (OS := OS) (lgc := lgc) (F := F) (m := m) hFm hkernel]
  exact sq_nonneg ‖bvt_transport_to_osHilbert_onImage OS F‖

/-
Package I transport note:

The old placeholder transport route has been removed. The
current live Package-I frontier is now:
1. establish the transformed-image quadratic identity,
2. then close positivity from the transformed-image core using the already-built
   Hilbert-space density of positive-time vectors.
-/

end
