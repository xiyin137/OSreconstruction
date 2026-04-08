/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Michael Douglas, ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValues
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSemigroup
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

/-- The Euclidean positive-time degree-`n` test space from OS I Section 4.3.

This is the paper's `S_+(ℝ^{4n})`: Schwartz `n`-point test functions whose
topological support lies in the ordered positive-time region. -/
def EuclideanPositiveTimeComponent (d n : ℕ) [NeZero d] :=
  {f : SchwartzNPoint d n //
    tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n}

/-- An equivalent submodule presentation of the Euclidean positive-time domain.

The blueprint allows either the subtype or submodule form, as long as it
represents the same Section-4.3 Euclidean input space. This submodule surface
will be convenient when the transport map is eventually stated as a continuous
linear map. -/
def euclideanPositiveTimeSubmodule (d n : ℕ) [NeZero d] :
    Submodule ℂ (SchwartzNPoint d n) where
  carrier := {f |
    tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n}
  zero_mem' := by
    change tsupport (((0 : SchwartzNPoint d n) : NPointDomain d n → ℂ)) ⊆
      OrderedPositiveTimeRegion d n
    rw [show (((0 : SchwartzNPoint d n) : NPointDomain d n → ℂ)) = 0 by rfl]
    simpa using (empty_subset (OrderedPositiveTimeRegion d n) :
      (∅ : Set (NPointDomain d n)) ⊆ OrderedPositiveTimeRegion d n)
  add_mem' := by
    intro f g hf hg x hx
    have hx' := tsupport_add
      ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ)
      ((g : SchwartzNPoint d n) : NPointDomain d n → ℂ) hx
    exact hx'.elim (hf ·) (hg ·)
  smul_mem' := by
    intro c f hf
    exact (tsupport_smul_subset_right
      (fun _ : NPointDomain d n => c)
      ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ)).trans hf

@[simp] theorem mem_euclideanPositiveTimeSubmodule
    {n : ℕ} (f : SchwartzNPoint d n) :
    f ∈ euclideanPositiveTimeSubmodule (d := d) n ↔
      tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n := Iff.rfl

namespace EuclideanPositiveTimeComponent

variable {n : ℕ}

/-- Package a positive-time submodule element as the corresponding subtype
object. This is the bridge from the current-code submodule model back to the
existing Euclidean-side OS Hilbert-space vectors. -/
def ofSubmodule
    (f : euclideanPositiveTimeSubmodule (d := d) n) :
    EuclideanPositiveTimeComponent d n :=
  ⟨f.1, f.2⟩

/-- A positive-time component viewed as the corresponding single positive-time
Borchers sequence. This is the Euclidean-side input object whose image under
the eventual Section 4.3 transport map will be compared against the Wightman
quadratic form. -/
def toPositiveTimeSingle
    (f : EuclideanPositiveTimeComponent d n) :
    PositiveTimeBorchersSequence d :=
  PositiveTimeBorchersSequence.single n f.1 f.2

end EuclideanPositiveTimeComponent

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
private noncomputable def partialFourierSpatial_timeSliceSchwartz
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
private theorem fourierInvPairing_hasOneSidedFourierSupport
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

/-- Honest one-variable Section 4.3 supplier: from positive-support Schwartz
input, obtain the Paley-Wiener upper-half-plane extension with the correct
distributional boundary value. -/
private theorem complexLaplaceTransform_hasPaleyWienerExtension
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

/-- The one-variable Paley-Wiener supplier applied to the actual branch-`3b`
positive-time time slice: on the positive imaginary axis, the canonical
Fourier-Laplace extension of the induced inverse-Fourier pairing reproduces the
raw one-sided Laplace transform of the slice itself. -/
private theorem fourierLaplaceExt_partialFourierSpatial_timeSlice_eq_complexLaplaceTransform
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
private theorem partialFourierSpatial_timeSlice_hasPaleyWienerExtension
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
private noncomputable def partialFourierSpatial_timeSliceCanonicalExtension
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
private theorem partialFourierSpatial_timeSliceCanonicalExtension_eq_complexLaplaceTransform
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

/-- The current-code realization of the degree-`n` Section 4.3 Fourier-Laplace
transport map.

Current route note:

* the theorem-surface codomain is under migration to the corrected half-space
  Section-4.3 object from the blueprint;
* the current type signature remains a temporary placeholder while branch `3b`
  builds the concrete partial-spatial-Fourier infrastructure;
* do **not** read this placeholder signature as endorsing the withdrawn
  full-Schwartz / Seeley-extension route from Iteration B.
-/
noncomputable def os1TransportComponent
    (d n : ℕ) [NeZero d] :
    euclideanPositiveTimeSubmodule (d := d) n →L[ℂ] SchwartzNPoint d n := by
  sorry

/-- The Section 4.3 transport applied componentwise to a positive-time
Borchers sequence. This is the Minkowski-side test sequence whose
Wightman quadratic form is compared against the OS Hilbert-space inner
product. -/
noncomputable def positiveTimeBorchersTransport
    (d : ℕ) [NeZero d] :
    PositiveTimeBorchersSequence d → BorchersSequence d
  | F =>
      { funcs := fun n =>
          os1TransportComponent (d := d) n
            ⟨((F : BorchersSequence d).funcs n), F.ordered_tsupport n⟩
        bound := (F : BorchersSequence d).bound
        bound_spec := by
          intro n hn
          have hzero : ((F : BorchersSequence d).funcs n) = 0 :=
            (F : BorchersSequence d).bound_spec n hn
          have hsub :
              (⟨((F : BorchersSequence d).funcs n), F.ordered_tsupport n⟩ :
                euclideanPositiveTimeSubmodule (d := d) n) = 0 := by
            apply Subtype.ext
            exact hzero
          simpa [hsub] using
            (os1TransportComponent (d := d) n).map_zero }

/-- The core Section 4.3 sesquilinear bridge: on transported positive-time
inputs, the reconstructed Wightman pairing agrees with the honest OS Hilbert
space inner product. This is the theorem surface needed to expose the
cross-degree terms in `WightmanInnerProduct` and feed the final positivity
closure.

Because `os1TransportComponent` lands in full `SchwartzNPoint d n` via a
non-canonical Seeley extension, the proof of this bridge must be phrased so it
does not depend on the chosen extension. Concretely, only the half-space trace
of the Section 4.3 transform is mathematically meaningful, and any two Schwartz
extensions of that same half-space data differ by a function whose half-space
trace vanishes. The bridge proof must use only Wightman smearings that are
insensitive to that difference. -/
theorem bvt_W_eq_inner_on_positiveTimeTransport
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) :
    WightmanInnerProduct d (bvt_W OS lgc)
      (positiveTimeBorchersTransport (d := d) F)
      (positiveTimeBorchersTransport (d := d) G) =
      @inner ℂ (OSHilbertSpace OS) _
        (positiveTimeBorchersVector (d := d) OS F)
        (positiveTimeBorchersVector (d := d) OS G) := by
  sorry

/-- Positivity already holds on the image of the positive-time Section 4.3
transport, once the sesquilinear bridge is available. This is the first honest
consumer of `bvt_W_eq_inner_on_positiveTimeTransport`. -/
theorem bvt_W_positive_on_positiveTimeTransport_image
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : PositiveTimeBorchersSequence d) :
    0 ≤ (WightmanInnerProduct d (bvt_W OS lgc)
            (positiveTimeBorchersTransport (d := d) F)
            (positiveTimeBorchersTransport (d := d) F)).re := by
  rw [bvt_W_eq_inner_on_positiveTimeTransport (OS := OS) (lgc := lgc) F F]
  have hnorm :
      RCLike.re
        (@inner ℂ (OSHilbertSpace OS) _ (positiveTimeBorchersVector (d := d) OS F)
          (positiveTimeBorchersVector (d := d) OS F)) =
        ‖positiveTimeBorchersVector (d := d) OS F‖ ^ 2 := by
    simpa using
      (inner_self_eq_norm_sq (𝕜 := ℂ) (positiveTimeBorchersVector (d := d) OS F))
  change 0 ≤ RCLike.re
    (@inner ℂ (OSHilbertSpace OS) _ (positiveTimeBorchersVector (d := d) OS F)
      (positiveTimeBorchersVector (d := d) OS F))
  rw [hnorm]
  exact sq_nonneg ‖positiveTimeBorchersVector (d := d) OS F‖

/-- Final theorem-3 blocker after the transport/bridge package is in place:
reduce positivity for arbitrary Borchers data to positivity on the
positive-time transport image by the remaining density and continuity
arguments. -/
theorem bvt_W_positive_density_reduction
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F : BorchersSequence d) :
    (WightmanInnerProduct d (bvt_W OS lgc) F F).re ≥ 0 := by
  sorry

/-- Sorry 3: Wightman positive-definiteness for all BorchersSequence.

The correct proof route (OS I Section 4.3, equations 4.22-4.28):
1. define the Section 4.3 transport map on positive-time Euclidean inputs,
2. show `bvt_W` agrees with the corresponding VEV / Hilbert-space pairing on
   that positive-time transport core,
3. use density of positive-time vectors in `OSHilbertSpace OS` from the
   completion/GNS construction,
4. extend by continuity to arbitrary `BorchersSequence d`.

This requires Fourier-Laplace infrastructure connecting `bvt_F` to the
semigroup spectral measure and the corrected Section 4.3 transport / VEV
identification. The old Schwartz-density theorem surface was withdrawn after
review; see `agents_chat.md` Entries #329-#331. -/
theorem bvt_W_positive_direct
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    ∀ F : BorchersSequence d,
      (WightmanInnerProduct d (bvt_W OS lgc) F F).re ≥ 0 := by
  intro F
  simpa using bvt_W_positive_density_reduction (OS := OS) (lgc := lgc) F

end
