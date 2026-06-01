import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIILemma51
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIILemma51AxisPair
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIParametricFlatTubeBranch

/-!
# OS II Lemma 5.1 Axis-Pair Total Branch Pullback

This companion applies the general-`d` axis-pair Lemma 5.1 coefficient geometry
to the explicit OS-II total log semigroup branch.  It is the arbitrary spatial
dimension analogue of the checked four-coordinate Lemma 5.1 total-branch
pullback.
-/

noncomputable section

open Complex Topology MeasureTheory
open scoped Classical NNReal BigOperators

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Explicit scalar semigroup candidate on the axis-pair logarithmic carrier:
evaluate the one-variable OS semigroup representative at the total complex
positive coefficient `sum_a exp r_a`. -/
def osiiAxisPairTotalLogSemigroupBranch
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) :
    (osiiAxisPairIndex d → ℂ) → ℂ :=
  fun r =>
    OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc F G
      (∑ a : osiiAxisPairIndex d, Complex.exp (r a))

/-- Weighted scalar semigroup candidate on the axis-pair logarithmic carrier.

In the Lemma 5.1 axis-pair chart, coefficients multiply directions whose time
component is `T`, so the physical semigroup time is
`T * sum_a exp r_a`. -/
def osiiAxisPairWeightedTotalLogSemigroupBranch
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) (T : ℝ) :
    (osiiAxisPairIndex d → ℂ) → ℂ :=
  fun r =>
    OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc F G
      ((T : ℂ) * ∑ a : osiiAxisPairIndex d, Complex.exp (r a))

/-- The axis-pair log carrier maps by exponentiation and summation into the
right half-plane. -/
theorem osiiAxisPairLogDomain_sum_exp_mem_rightHalfPlane
    {r : osiiAxisPairIndex d → ℂ}
    (hr : r ∈ osiiAxisPairLogDomain (d := d)) :
    (∑ a : osiiAxisPairIndex d, Complex.exp (r a)) ∈ {z : ℂ | 0 < z.re} := by
  classical
  have hcoord : ∀ a : osiiAxisPairIndex d, |(r a).im| < Real.pi / 2 := by
    intro a
    exact lt_of_le_of_lt
      (Finset.single_le_sum
        (fun p _ => abs_nonneg (r p).im) (Finset.mem_univ a))
      (by simpa [osiiAxisPairLogDomain] using hr)
  have hpos : ∀ a : osiiAxisPairIndex d, 0 < (Complex.exp (r a)).re := by
    intro a
    exact osiiMZ_exp_apply_mem_rightHalfPlane
      (m := Fintype.card (osiiAxisPairIndex d))
      (q := ⟨0, by
        have hcard_pos : 0 < Fintype.card (osiiAxisPairIndex d) := by
          exact Fintype.card_pos_iff.2
            ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩, true)⟩
        simpa using hcard_pos⟩)
      (r := fun _ : Fin (Fintype.card (osiiAxisPairIndex d)) => r a)
      (by simpa [osiiMZCoordinateLogStrip] using hcoord a)
  have hnonempty : (Finset.univ : Finset (osiiAxisPairIndex d)).Nonempty := by
    refine ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩, true), Finset.mem_univ _⟩
  simpa using Finset.sum_pos (fun a _ => hpos a) hnonempty

/-- Positive real weights preserve the right half-plane image of the axis-pair
log carrier. -/
theorem osiiAxisPairLogDomain_weighted_sum_exp_mem_rightHalfPlane
    (T : ℝ) (hT : 0 < T)
    {r : osiiAxisPairIndex d → ℂ}
    (hr : r ∈ osiiAxisPairLogDomain (d := d)) :
    ((T : ℂ) * ∑ a : osiiAxisPairIndex d, Complex.exp (r a)) ∈
      {z : ℂ | 0 < z.re} := by
  have hsum :=
    osiiAxisPairLogDomain_sum_exp_mem_rightHalfPlane (d := d) hr
  simpa [Complex.mul_re] using mul_pos hT hsum

/-- The explicit total semigroup branch is holomorphic on the axis-pair
logarithmic carrier. -/
theorem differentiableOn_osiiAxisPairTotalLogSemigroupBranch
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) :
    DifferentiableOn ℂ
      (osiiAxisPairTotalLogSemigroupBranch (d := d) OS lgc F G)
      (osiiAxisPairLogDomain (d := d)) := by
  classical
  have hsum_diff :
      DifferentiableOn ℂ
        (fun r : osiiAxisPairIndex d → ℂ =>
          ∑ a : osiiAxisPairIndex d, Complex.exp (r a))
        (osiiAxisPairLogDomain (d := d)) := by
    convert
      DifferentiableOn.sum
        (u := (Finset.univ : Finset (osiiAxisPairIndex d))) fun a _ =>
          (Complex.differentiable_exp.comp
            (differentiable_apply a :
              Differentiable ℂ (fun r : osiiAxisPairIndex d → ℂ => r a))).differentiableOn
      using 1
    ext r
    simp
  exact
      (differentiableOn_OSInnerProductTimeShiftHolomorphicValueExpandBoth
        (d := d) OS lgc F G).comp hsum_diff
      (fun r hr => osiiAxisPairLogDomain_sum_exp_mem_rightHalfPlane (d := d) hr)

/-- The weighted total semigroup branch is holomorphic on the axis-pair
logarithmic carrier. -/
theorem differentiableOn_osiiAxisPairWeightedTotalLogSemigroupBranch
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (T : ℝ) (hT : 0 < T) :
    DifferentiableOn ℂ
      (osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc F G T)
      (osiiAxisPairLogDomain (d := d)) := by
  classical
  have hsum_diff :
      DifferentiableOn ℂ
        (fun r : osiiAxisPairIndex d → ℂ =>
          ∑ a : osiiAxisPairIndex d, Complex.exp (r a))
        (osiiAxisPairLogDomain (d := d)) := by
    convert
      DifferentiableOn.sum
        (u := (Finset.univ : Finset (osiiAxisPairIndex d))) fun a _ =>
          (Complex.differentiable_exp.comp
            (differentiable_apply a :
              Differentiable ℂ (fun r : osiiAxisPairIndex d → ℂ => r a))).differentiableOn
      using 1
    ext r
    simp
  have hweighted_diff :
      DifferentiableOn ℂ
        (fun r : osiiAxisPairIndex d → ℂ =>
          (T : ℂ) * ∑ a : osiiAxisPairIndex d, Complex.exp (r a))
        (osiiAxisPairLogDomain (d := d)) := by
    simpa using hsum_diff.const_mul (T : ℂ)
  exact
    (differentiableOn_OSInnerProductTimeShiftHolomorphicValueExpandBoth
      (d := d) OS lgc F G).comp hweighted_diff
      (fun r hr =>
        osiiAxisPairLogDomain_weighted_sum_exp_mem_rightHalfPlane
          (d := d) T hT hr)

/-- Real-edge value of the axis-pair total log semigroup branch.

This is the axis-pair version of the real restriction in OS II `(5.7)`--`(5.8)`:
on real logarithmic coefficients, the Malgrange-Zerner branch is the actual OS
positive-time semigroup scalar with total time `sum_a exp x_a`. -/
theorem osiiAxisPairTotalLogSemigroupBranch_real_edge_eq_total
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (x : osiiAxisPairIndex d → ℝ) :
    osiiAxisPairTotalLogSemigroupBranch (d := d) OS lgc F G (fun a => (x a : ℂ)) =
      OSInnerProduct d OS.S (F : BorchersSequence d)
        (timeShiftBorchers (d := d)
          (∑ a : osiiAxisPairIndex d, Real.exp (x a))
          (G : BorchersSequence d)) := by
  classical
  have hsum_pos : 0 < ∑ a : osiiAxisPairIndex d, Real.exp (x a) := by
    have hnonempty : (Finset.univ : Finset (osiiAxisPairIndex d)).Nonempty := by
      refine ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩, true), Finset.mem_univ _⟩
    exact Finset.sum_pos (fun a _ => Real.exp_pos (x a)) hnonempty
  have hsum :
      (∑ a : osiiAxisPairIndex d, Complex.exp ((x a : ℂ))) =
        ((∑ a : osiiAxisPairIndex d, Real.exp (x a)) : ℂ) := by
    simp
  rw [osiiAxisPairTotalLogSemigroupBranch, hsum]
  simpa using
    OSInnerProductTimeShiftHolomorphicValueExpandBoth_ofReal_eq_of_isCompactSupport
      (d := d) OS lgc F G hG_compact
      (∑ a : osiiAxisPairIndex d, Real.exp (x a)) hsum_pos

/-- Positive-coefficient form of the axis-pair branch real edge.

This is the "going back to the variables `u`" step after OS II `(5.8)`: the
logarithmic branch evaluated at `log u_a` restricts to the same OS semigroup
scalar with total positive time `sum_a u_a`. -/
theorem osiiAxisPairTotalLogSemigroupBranch_log_real_edge_eq_total
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (u : osiiAxisPairIndex d → ℝ) (hu : ∀ a, 0 < u a) :
    osiiAxisPairTotalLogSemigroupBranch (d := d) OS lgc F G
        (fun a => Complex.log ((u a : ℝ) : ℂ)) =
      OSInnerProduct d OS.S (F : BorchersSequence d)
        (timeShiftBorchers (d := d)
          (∑ a : osiiAxisPairIndex d, u a)
          (G : BorchersSequence d)) := by
  classical
  have hlog :
      (fun a : osiiAxisPairIndex d => Complex.log ((u a : ℝ) : ℂ)) =
        fun a : osiiAxisPairIndex d => ((Real.log (u a) : ℝ) : ℂ) := by
    funext a
    exact (Complex.ofReal_log (le_of_lt (hu a))).symm
  rw [hlog]
  have hreal :=
    osiiAxisPairTotalLogSemigroupBranch_real_edge_eq_total
      (d := d) OS lgc F G hG_compact
      (fun a : osiiAxisPairIndex d => Real.log (u a))
  simpa [Real.exp_log, hu] using hreal

/-- Weighted real-edge value of the axis-pair total log semigroup branch.

This is the time-normalized form of OS II `(5.7)`--`(5.8)` for the axis-pair
chart: the semigroup time is the weighted coefficient sum
`T * sum_a exp x_a`. -/
theorem osiiAxisPairWeightedTotalLogSemigroupBranch_real_edge_eq_total
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (T : ℝ) (hT : 0 < T)
    (hG_compact : ∀ n,
      HasCompactSupport (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (x : osiiAxisPairIndex d → ℝ) :
    osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc F G T
        (fun a => (x a : ℂ)) =
      OSInnerProduct d OS.S (F : BorchersSequence d)
        (timeShiftBorchers (d := d)
          (T * ∑ a : osiiAxisPairIndex d, Real.exp (x a))
          (G : BorchersSequence d)) := by
  classical
  have hsum_pos : 0 < ∑ a : osiiAxisPairIndex d, Real.exp (x a) := by
    have hnonempty : (Finset.univ : Finset (osiiAxisPairIndex d)).Nonempty := by
      refine ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩, true), Finset.mem_univ _⟩
    exact Finset.sum_pos (fun a _ => Real.exp_pos (x a)) hnonempty
  have htime_pos : 0 < T * ∑ a : osiiAxisPairIndex d, Real.exp (x a) :=
    mul_pos hT hsum_pos
  have hsum :
      (T : ℂ) * (∑ a : osiiAxisPairIndex d, Complex.exp ((x a : ℂ))) =
        ((T * ∑ a : osiiAxisPairIndex d, Real.exp (x a)) : ℂ) := by
    simp
  rw [osiiAxisPairWeightedTotalLogSemigroupBranch, hsum]
  simpa using
    OSInnerProductTimeShiftHolomorphicValueExpandBoth_ofReal_eq_of_isCompactSupport
      (d := d) OS lgc F G hG_compact
      (T * ∑ a : osiiAxisPairIndex d, Real.exp (x a)) htime_pos

/-- Positive-coefficient form of the weighted axis-pair branch real edge. -/
theorem osiiAxisPairWeightedTotalLogSemigroupBranch_log_real_edge_eq_total
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (T : ℝ) (hT : 0 < T)
    (hG_compact : ∀ n,
      HasCompactSupport (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (u : osiiAxisPairIndex d → ℝ) (hu : ∀ a, 0 < u a) :
    osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc F G T
        (fun a => Complex.log ((u a : ℝ) : ℂ)) =
      OSInnerProduct d OS.S (F : BorchersSequence d)
        (timeShiftBorchers (d := d)
          (T * ∑ a : osiiAxisPairIndex d, u a)
          (G : BorchersSequence d)) := by
  classical
  have hlog :
      (fun a : osiiAxisPairIndex d => Complex.log ((u a : ℝ) : ℂ)) =
        fun a : osiiAxisPairIndex d => ((Real.log (u a) : ℝ) : ℂ) := by
    funext a
    exact (Complex.ofReal_log (le_of_lt (hu a))).symm
  rw [hlog]
  have hreal :=
    osiiAxisPairWeightedTotalLogSemigroupBranch_real_edge_eq_total
      (d := d) OS lgc F G T hT hG_compact
      (fun a : osiiAxisPairIndex d => Real.log (u a))
  simpa [Real.exp_log, hu] using hreal

/-- Concentrated real-edge value of the axis-pair total log branch.

For single left and right positive-time vectors, the real edge is the Schwinger
functional of the OS-conjugated left test tensor the right test shifted by the
total positive coefficient time.  This is the distributional form used in the
OS-II `(5.7)`--`(5.8)` local branch-representation step. -/
theorem osiiAxisPairTotalLogSemigroupBranch_single_real_edge_eq_schwinger_timeShift
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (x : osiiAxisPairIndex d → ℝ) :
    osiiAxisPairTotalLogSemigroupBranch (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single r g hg_ord)
        (fun a => (x a : ℂ)) =
      OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ a : osiiAxisPairIndex d, Real.exp (x a)) g))) := by
  classical
  have hG_compact :
      ∀ s,
        HasCompactSupport (((((PositiveTimeBorchersSequence.single r g hg_ord :
          PositiveTimeBorchersSequence d) : BorchersSequence d).funcs s :
          SchwartzNPoint d s) : NPointDomain d s → ℂ)) := by
    intro s
    by_cases hs : s = r
    · subst hs
      simpa [PositiveTimeBorchersSequence.single_toBorchersSequence] using hg_compact
    · have hzero :
        ((((PositiveTimeBorchersSequence.single r g hg_ord :
          PositiveTimeBorchersSequence d) : BorchersSequence d).funcs s :
          SchwartzNPoint d s) : NPointDomain d s → ℂ) = 0 := by
          simp [PositiveTimeBorchersSequence.single_toBorchersSequence,
            BorchersSequence.single, hs]
      rw [hzero]
      simpa using (HasCompactSupport.zero :
        HasCompactSupport (0 : NPointDomain d s → ℂ))
  calc
    osiiAxisPairTotalLogSemigroupBranch (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single r g hg_ord)
        (fun a => (x a : ℂ)) =
      OSInnerProduct d OS.S
        (PositiveTimeBorchersSequence.single n f hf_ord : BorchersSequence d)
        (timeShiftBorchers (d := d)
          (∑ a : osiiAxisPairIndex d, Real.exp (x a))
          (PositiveTimeBorchersSequence.single r g hg_ord : BorchersSequence d)) := by
        exact
          osiiAxisPairTotalLogSemigroupBranch_real_edge_eq_total
            (d := d) OS lgc
            (F := PositiveTimeBorchersSequence.single n f hf_ord)
            (G := PositiveTimeBorchersSequence.single r g hg_ord)
            hG_compact x
    _ = OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ a : osiiAxisPairIndex d, Real.exp (x a)) g))) := by
        simpa [PositiveTimeBorchersSequence.single_toBorchersSequence] using
          OSInnerProduct_single_right_timeShift
            (d := d) OS f g
            (∑ a : osiiAxisPairIndex d, Real.exp (x a))

/-- Positive-coefficient concentrated real-edge value of the axis-pair branch.

This is the direct single-test form of the OS II `(5.8)` return from logarithmic
variables: `r_a = log u_a` gives the Schwinger functional of the shifted right
test at total time `sum_a u_a`. -/
theorem osiiAxisPairTotalLogSemigroupBranch_single_log_real_edge_eq_schwinger_timeShift
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (u : osiiAxisPairIndex d → ℝ) (hu : ∀ a, 0 < u a) :
    osiiAxisPairTotalLogSemigroupBranch (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single r g hg_ord)
        (fun a => Complex.log ((u a : ℝ) : ℂ)) =
      OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ a : osiiAxisPairIndex d, u a) g))) := by
  classical
  have hlog :
      (fun a : osiiAxisPairIndex d => Complex.log ((u a : ℝ) : ℂ)) =
        fun a : osiiAxisPairIndex d => ((Real.log (u a) : ℝ) : ℂ) := by
    funext a
    exact (Complex.ofReal_log (le_of_lt (hu a))).symm
  rw [hlog]
  have hreal :=
    osiiAxisPairTotalLogSemigroupBranch_single_real_edge_eq_schwinger_timeShift
      (d := d) OS lgc f hf_ord g hg_ord hg_compact
      (fun a : osiiAxisPairIndex d => Real.log (u a))
  simpa [Real.exp_log, hu] using hreal

/-- Concentrated weighted real-edge value of the axis-pair total log branch.

This is the single-test OS-II Lemma 5.1 normalization needed after introducing
directions with time component `T`: the right factor is shifted by
`T * sum_a exp x_a`. -/
theorem osiiAxisPairWeightedTotalLogSemigroupBranch_single_real_edge_eq_schwinger_timeShift
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (x : osiiAxisPairIndex d → ℝ) :
    osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single r g hg_ord) T
        (fun a => (x a : ℂ)) =
      OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (T * ∑ a : osiiAxisPairIndex d, Real.exp (x a)) g))) := by
  classical
  have hG_compact :
      ∀ s,
        HasCompactSupport (((((PositiveTimeBorchersSequence.single r g hg_ord :
          PositiveTimeBorchersSequence d) : BorchersSequence d).funcs s :
          SchwartzNPoint d s) : NPointDomain d s → ℂ)) := by
    intro s
    by_cases hs : s = r
    · subst hs
      simpa [PositiveTimeBorchersSequence.single_toBorchersSequence] using hg_compact
    · have hzero :
        ((((PositiveTimeBorchersSequence.single r g hg_ord :
          PositiveTimeBorchersSequence d) : BorchersSequence d).funcs s :
          SchwartzNPoint d s) : NPointDomain d s → ℂ) = 0 := by
          simp [PositiveTimeBorchersSequence.single_toBorchersSequence,
            BorchersSequence.single, hs]
      rw [hzero]
      simpa using (HasCompactSupport.zero :
        HasCompactSupport (0 : NPointDomain d s → ℂ))
  calc
    osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single r g hg_ord) T
        (fun a => (x a : ℂ)) =
      OSInnerProduct d OS.S
        (PositiveTimeBorchersSequence.single n f hf_ord : BorchersSequence d)
        (timeShiftBorchers (d := d)
          (T * ∑ a : osiiAxisPairIndex d, Real.exp (x a))
          (PositiveTimeBorchersSequence.single r g hg_ord : BorchersSequence d)) := by
        exact
          osiiAxisPairWeightedTotalLogSemigroupBranch_real_edge_eq_total
            (d := d) OS lgc
            (F := PositiveTimeBorchersSequence.single n f hf_ord)
            (G := PositiveTimeBorchersSequence.single r g hg_ord)
            T hT hG_compact x
    _ = OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (T * ∑ a : osiiAxisPairIndex d, Real.exp (x a)) g))) := by
        simpa [PositiveTimeBorchersSequence.single_toBorchersSequence] using
          OSInnerProduct_single_right_timeShift
            (d := d) OS f g
            (T * ∑ a : osiiAxisPairIndex d, Real.exp (x a))

/-- Positive-coefficient concentrated weighted real-edge value of the axis-pair
branch. -/
theorem osiiAxisPairWeightedTotalLogSemigroupBranch_single_log_real_edge_eq_schwinger_timeShift
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (u : osiiAxisPairIndex d → ℝ) (hu : ∀ a, 0 < u a) :
    osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single r g hg_ord) T
        (fun a => Complex.log ((u a : ℝ) : ℂ)) =
      OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (T * ∑ a : osiiAxisPairIndex d, u a) g))) := by
  classical
  have hlog :
      (fun a : osiiAxisPairIndex d => Complex.log ((u a : ℝ) : ℂ)) =
        fun a : osiiAxisPairIndex d => ((Real.log (u a) : ℝ) : ℂ) := by
    funext a
    exact (Complex.ofReal_log (le_of_lt (hu a))).symm
  rw [hlog]
  have hreal :=
    osiiAxisPairWeightedTotalLogSemigroupBranch_single_real_edge_eq_schwinger_timeShift
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT
      (fun a : osiiAxisPairIndex d => Real.log (u a))
  simpa [Real.exp_log, hu] using hreal

/-- Coefficient-map real edge of the weighted axis-pair branch.

For real coordinate perturbations, the positive coefficients from Lemma 5.1
return to the physical time variable by
`T * sum_a coeff_a = ξ^0 / 2 + ζ^0`.  This is the concrete normalization that
connects the MZ logarithmic variables back to the OS Schwinger time shift. -/
theorem osiiAxisPairWeightedTotalLogSemigroupBranch_single_coeffMap_real_edge_eq_schwinger_timeShift
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (ξ ζ : Fin (d + 1) → ℝ)
    (hcoeff_pos :
      ∀ a : osiiAxisPairIndex d,
        0 < (osiiAxisPairCoeffMap T ξ (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a).re) :
    osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single r g hg_ord) T
        (fun a : osiiAxisPairIndex d =>
          Complex.log
            (osiiAxisPairCoeffMap T ξ (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a)) =
      OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (ξ 0 / 2 + ζ 0) g))) := by
  classical
  let u : osiiAxisPairIndex d → ℝ := fun a =>
    (osiiAxisPairCoeffMap T ξ (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a).re
  have hu : ∀ a : osiiAxisPairIndex d, 0 < u a := by
    intro a
    exact hcoeff_pos a
  have hcoeff_real :
      ∀ a : osiiAxisPairIndex d,
        ((u a : ℝ) : ℂ) =
          osiiAxisPairCoeffMap T ξ (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a := by
    intro a
    rcases a with ⟨j, b⟩
    have hbase_im :
        ((ξ 0 : ℂ) / (((4 * (d : ℝ) * T : ℝ) : ℂ))).im = 0 := by
      simpa using (Complex.div_ofReal_im (ξ 0 : ℂ) (4 * (d : ℝ) * T))
    have htime_im :
        ((ζ 0 : ℂ) / (((2 * (d : ℝ) * T : ℝ) : ℂ))).im = 0 := by
      simpa using (Complex.div_ofReal_im (ζ 0 : ℂ) (2 * (d : ℝ) * T))
    have hbase_im' :
        ((ξ 0 : ℂ) / (4 * (d : ℂ) * (T : ℂ))).im = 0 := by
      simpa using hbase_im
    have htime_im' :
        ((ζ 0 : ℂ) / (2 * (d : ℂ) * (T : ℂ))).im = 0 := by
      simpa using htime_im
    apply Complex.ext
    · cases b <;>
        simp [u, osiiAxisPairCoeffMap, osiiAxisPairCoeff]
    · cases b <;>
        simp [u, osiiAxisPairCoeffMap, osiiAxisPairCoeff, hbase_im', htime_im']
  have hlog :
      (fun a : osiiAxisPairIndex d =>
          Complex.log
            (osiiAxisPairCoeffMap T ξ (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a)) =
        fun a : osiiAxisPairIndex d => Complex.log ((u a : ℝ) : ℂ) := by
    funext a
    rw [hcoeff_real a]
  have hsum_time : T * (∑ a : osiiAxisPairIndex d, u a) = ξ 0 / 2 + ζ 0 := by
    have hweighted :=
      osiiAxisPairCoeffMap_weighted_time_sum
        (d := d) T (ne_of_gt hT) ξ
        (fun ν : Fin (d + 1) => (ζ ν : ℂ))
    have hre := congrArg Complex.re hweighted
    have hre' : (∑ a : osiiAxisPairIndex d, T * u a) = ξ 0 / 2 + ζ 0 := by
      simpa [u, mul_comm, mul_left_comm, mul_assoc, Complex.mul_re] using hre
    rw [← Finset.mul_sum] at hre'
    simpa using hre'
  calc
    osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single r g hg_ord) T
        (fun a : osiiAxisPairIndex d =>
          Complex.log
            (osiiAxisPairCoeffMap T ξ (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a)) =
      osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single r g hg_ord) T
        (fun a : osiiAxisPairIndex d => Complex.log ((u a : ℝ) : ℂ)) := by
        rw [hlog]
    _ = OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (T * ∑ a : osiiAxisPairIndex d, u a) g))) := by
        exact
          osiiAxisPairWeightedTotalLogSemigroupBranch_single_log_real_edge_eq_schwinger_timeShift
            (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT u hu
    _ = OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (ξ 0 / 2 + ζ 0) g))) := by
        rw [hsum_time]

/-- OS II Lemma 5.1, axis-pair form, applied to the explicit total log
semigroup branch.

Near any positive physical time coordinate, the general-`d` axis-pair
coefficient chart pulls the total log semigroup representative back to a
holomorphic local polydisc in physical coordinates. -/
theorem osiiAxisPair_totalLogSemigroupBranch_local_polydisc
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    (η : ℝ) (hη : 0 < η)
    (hηsum :
      (Fintype.card (osiiAxisPairIndex d) : ℝ) * Real.arctan η < Real.pi / 2) :
    ∃ ρ : ℝ, 0 < ρ ∧
      DifferentiableOn ℂ
        (fun ζ : Fin (d + 1) → ℂ =>
          osiiAxisPairTotalLogSemigroupBranch (d := d) OS lgc F G
            (fun a : osiiAxisPairIndex d =>
              Complex.log (osiiAxisPairCoeffMap T ξ ζ a)))
        {ζ : Fin (d + 1) → ℂ | ∀ ν : Fin (d + 1), ‖ζ ν‖ < ρ} := by
  exact
    osiiAxisPair_local_polydisc_logDomain_extension_differentiableOn
      (d := d) T hT ξ hξ0 η hη hηsum
      (osiiAxisPairTotalLogSemigroupBranch (d := d) OS lgc F G)
      (differentiableOn_osiiAxisPairTotalLogSemigroupBranch
        (d := d) OS lgc F G)

/-- Aperture-free form of the axis-pair Lemma 5.1 total-branch pullback. -/
theorem osiiAxisPair_totalLogSemigroupBranch_local_polydisc_exists_eta
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0) :
    ∃ η ρ : ℝ, 0 < η ∧ 0 < ρ ∧
      DifferentiableOn ℂ
        (fun ζ : Fin (d + 1) → ℂ =>
          osiiAxisPairTotalLogSemigroupBranch (d := d) OS lgc F G
            (fun a : osiiAxisPairIndex d =>
              Complex.log (osiiAxisPairCoeffMap T ξ ζ a)))
        {ζ : Fin (d + 1) → ℂ | ∀ ν : Fin (d + 1), ‖ζ ν‖ < ρ} := by
  rcases exists_osiiAxisPair_eta_argSum (d := d) with ⟨η, hη, hηsum⟩
  rcases osiiAxisPair_totalLogSemigroupBranch_local_polydisc
      (d := d) OS lgc F G T hT ξ hξ0 η hη hηsum with
    ⟨ρ, hρ, hdiff⟩
  exact ⟨η, ρ, hη, hρ, hdiff⟩

/-- Real-slice continuity form of the axis-pair Lemma 5.1 total branch.

The local MZ output is holomorphic on a complex polydisc; the OS-II `(A0)->(P0)`
time-shell handoff consumes continuity of the induced real-coordinate scalar.
-/
theorem osiiAxisPair_totalLogSemigroupBranch_local_realSlice_continuous
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0) :
    ∃ η ρ : ℝ, 0 < η ∧ 0 < ρ ∧
      ContinuousOn
        (fun ζ : Fin (d + 1) → ℝ =>
          osiiAxisPairTotalLogSemigroupBranch (d := d) OS lgc F G
            (fun a : osiiAxisPairIndex d =>
              Complex.log
                (osiiAxisPairCoeffMap T ξ (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a)))
        {ζ : Fin (d + 1) → ℝ | ∀ ν : Fin (d + 1), ‖(ζ ν : ℂ)‖ < ρ} := by
  rcases osiiAxisPair_totalLogSemigroupBranch_local_polydisc_exists_eta
      (d := d) OS lgc F G T hT ξ hξ0 with
    ⟨η, ρ, hη, hρ, hdiff⟩
  let C : (Fin (d + 1) → ℝ) → (Fin (d + 1) → ℂ) :=
    fun ζ ν => (ζ ν : ℂ)
  have hC_cont : Continuous C := by
    apply continuous_pi
    intro ν
    exact continuous_ofReal.comp (continuous_apply ν)
  have hmaps :
      Set.MapsTo C
        {ζ : Fin (d + 1) → ℝ | ∀ ν : Fin (d + 1), ‖(ζ ν : ℂ)‖ < ρ}
        {ζ : Fin (d + 1) → ℂ | ∀ ν : Fin (d + 1), ‖ζ ν‖ < ρ} := by
    intro ζ hζ ν
    exact hζ ν
  refine ⟨η, ρ, hη, hρ, ?_⟩
  simpa [C] using
    hdiff.continuousOn.comp hC_cont.continuousOn hmaps

/-- OS II Lemma 5.1, axis-pair form, applied to the time-weighted total log
semigroup branch.

This is the normalized local holomorphy surface used when the coefficient
directions have time component `T`. -/
theorem osiiAxisPair_weightedTotalLogSemigroupBranch_local_polydisc
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    (η : ℝ) (hη : 0 < η)
    (hηsum :
      (Fintype.card (osiiAxisPairIndex d) : ℝ) * Real.arctan η < Real.pi / 2) :
    ∃ ρ : ℝ, 0 < ρ ∧
      DifferentiableOn ℂ
        (fun ζ : Fin (d + 1) → ℂ =>
          osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc F G T
            (fun a : osiiAxisPairIndex d =>
              Complex.log (osiiAxisPairCoeffMap T ξ ζ a)))
        {ζ : Fin (d + 1) → ℂ | ∀ ν : Fin (d + 1), ‖ζ ν‖ < ρ} := by
  exact
    osiiAxisPair_local_polydisc_logDomain_extension_differentiableOn
      (d := d) T hT ξ hξ0 η hη hηsum
      (osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc F G T)
      (differentiableOn_osiiAxisPairWeightedTotalLogSemigroupBranch
        (d := d) OS lgc F G T hT)

/-- Aperture-free form of the weighted axis-pair Lemma 5.1 branch pullback. -/
theorem osiiAxisPair_weightedTotalLogSemigroupBranch_local_polydisc_exists_eta
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0) :
    ∃ η ρ : ℝ, 0 < η ∧ 0 < ρ ∧
      DifferentiableOn ℂ
        (fun ζ : Fin (d + 1) → ℂ =>
          osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc F G T
            (fun a : osiiAxisPairIndex d =>
              Complex.log (osiiAxisPairCoeffMap T ξ ζ a)))
        {ζ : Fin (d + 1) → ℂ | ∀ ν : Fin (d + 1), ‖ζ ν‖ < ρ} := by
  rcases exists_osiiAxisPair_eta_argSum (d := d) with ⟨η, hη, hηsum⟩
  rcases osiiAxisPair_weightedTotalLogSemigroupBranch_local_polydisc
      (d := d) OS lgc F G T hT ξ hξ0 η hη hηsum with
    ⟨ρ, hρ, hdiff⟩
  exact ⟨η, ρ, hη, hρ, hdiff⟩

/-- Real-slice continuity form of the weighted axis-pair Lemma 5.1 branch. -/
theorem osiiAxisPair_weightedTotalLogSemigroupBranch_local_realSlice_continuous
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0) :
    ∃ η ρ : ℝ, 0 < η ∧ 0 < ρ ∧
      ContinuousOn
        (fun ζ : Fin (d + 1) → ℝ =>
          osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc F G T
            (fun a : osiiAxisPairIndex d =>
              Complex.log
                (osiiAxisPairCoeffMap T ξ (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a)))
        {ζ : Fin (d + 1) → ℝ | ∀ ν : Fin (d + 1), ‖(ζ ν : ℂ)‖ < ρ} := by
  rcases osiiAxisPair_weightedTotalLogSemigroupBranch_local_polydisc_exists_eta
      (d := d) OS lgc F G T hT ξ hξ0 with
    ⟨η, ρ, hη, hρ, hdiff⟩
  let C : (Fin (d + 1) → ℝ) → (Fin (d + 1) → ℂ) :=
    fun ζ ν => (ζ ν : ℂ)
  have hC_cont : Continuous C := by
    apply continuous_pi
    intro ν
    exact continuous_ofReal.comp (continuous_apply ν)
  have hmaps :
      Set.MapsTo C
        {ζ : Fin (d + 1) → ℝ | ∀ ν : Fin (d + 1), ‖(ζ ν : ℂ)‖ < ρ}
        {ζ : Fin (d + 1) → ℂ | ∀ ν : Fin (d + 1), ‖ζ ν‖ < ρ} := by
    intro ζ hζ ν
    exact hζ ν
  refine ⟨η, ρ, hη, hρ, ?_⟩
  simpa [C] using
    hdiff.continuousOn.comp hC_cont.continuousOn hmaps

/-- Local compact boundedness of the real-slice weighted Lemma 5.1 branch.

This is the Banach-Steinhaus-facing estimate for the OS-II `(5.7)`--`(5.8)`
boundary-value step: after shrinking the real coefficient polydisc to a compact
ball, the actual weighted semigroup/Malgrange-Zerner branch is uniformly
bounded there. -/
theorem osiiAxisPair_weightedTotalLogSemigroupBranch_local_realSlice_bound
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0) :
    ∃ ρ C : ℝ, 0 < ρ ∧
      0 ≤ C ∧
      ∀ ζ : Fin (d + 1) → ℝ,
        ζ ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) ρ →
          ‖osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc F G T
            (fun a : osiiAxisPairIndex d =>
              Complex.log
                (osiiAxisPairCoeffMap T ξ (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a))‖ ≤ C := by
  classical
  rcases osiiAxisPair_weightedTotalLogSemigroupBranch_local_realSlice_continuous
      (d := d) OS lgc F G T hT ξ hξ0 with
    ⟨_η, ρ0, _hη, hρ0, hcont⟩
  let H : (Fin (d + 1) → ℝ) → ℂ :=
    fun ζ =>
      osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc F G T
        (fun a : osiiAxisPairIndex d =>
          Complex.log
            (osiiAxisPairCoeffMap T ξ (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a))
  let ρ : ℝ := ρ0 / 2
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hρ_lt : ρ < ρ0 := by
    dsimp [ρ]
    linarith
  let K : Set (Fin (d + 1) → ℝ) := Metric.closedBall (0 : Fin (d + 1) → ℝ) ρ
  have hK_compact : IsCompact K := by
    simpa [K] using isCompact_closedBall (0 : Fin (d + 1) → ℝ) ρ
  have hK_sub :
      K ⊆ {ζ : Fin (d + 1) → ℝ | ∀ ν : Fin (d + 1), ‖(ζ ν : ℂ)‖ < ρ0} := by
    intro ζ hζ ν
    have hζ_norm : ‖ζ‖ ≤ ρ := by
      simpa [K, Metric.mem_closedBall, dist_eq_norm] using hζ
    have hcoord : ‖ζ ν‖ ≤ ‖ζ‖ := norm_le_pi_norm ζ ν
    have hcoord' : ‖(ζ ν : ℂ)‖ ≤ ρ := by
      simpa using hcoord.trans hζ_norm
    exact lt_of_le_of_lt hcoord' hρ_lt
  obtain ⟨C, hC⟩ :=
    hK_compact.exists_bound_of_continuousOn
      (f := H) (hcont.mono hK_sub)
  refine ⟨ρ, max C 0, hρ, le_max_right C 0, ?_⟩
  intro ζ hζ
  exact (hC ζ (by simpa [K] using hζ)).trans (le_max_left C 0)

/-- Raw OS-II generator boundary value at an actual weighted axis-pair
coefficient point.

This specializes the one-variable semigroup boundary theorem to the real
Lemma 5.1 coefficient chart: after taking logarithms of the positive
axis-pair coefficients, the target is exactly the weighted MZ branch value.
It is the generator-side input before the dense/test-function upgrade to a
local `RepresentsDistributionOn` statement. -/
theorem tendsto_rotated_osiiAxisPairWeightedTotalLogSemigroupBranch_coeffMap_real
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (T : ℝ) (hT : 0 < T)
    (ξ ζ : Fin (d + 1) → ℝ)
    (hcoeff_pos :
      ∀ a : osiiAxisPairIndex d,
        0 < (osiiAxisPairCoeffMap T ξ
          (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a).re)
    (htime : 0 < ξ 0 / 2 + ζ 0) :
    Filter.Tendsto
      (fun η : ℝ =>
        ∫ x : ℝ,
          OSInnerProductTimeShiftHolomorphicValueExpandBoth
              (d := d) OS lgc F G
              (-Complex.I * ((x : ℂ) + η * Complex.I)) *
            (SchwartzMap.fourierTransformCLM ℂ
              (SCV.schwartzPsiZ
                (((2 * Real.pi : ℂ) *
                  (((ξ 0 / 2 + ζ 0 : ℝ) : ℂ) * Complex.I)))
                (by
                  simpa [Complex.mul_im, htime.ne']
                    using mul_pos Real.two_pi_pos htime))) x)
      (𝓝[Set.Ioi 0] (0 : ℝ))
      (𝓝
        (osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc F G T
          (fun a : osiiAxisPairIndex d =>
            Complex.log
              (osiiAxisPairCoeffMap T ξ
                (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a)))) := by
  classical
  let coeff : osiiAxisPairIndex d → ℂ :=
    osiiAxisPairCoeffMap T ξ (fun ν : Fin (d + 1) => (ζ ν : ℂ))
  let t : ℝ := ξ 0 / 2 + ζ 0
  have ht : 0 < t := by
    simpa [t] using htime
  have hlim :=
    tendsto_rotated_OSInnerProductTimeShiftHolomorphicValueExpandBoth_to_imagAxis
      (d := d) OS lgc F G ht
  have htarget :
      OSInnerProductTimeShiftHolomorphicValueExpandBoth
          (d := d) OS lgc F G (t : ℂ) =
        osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc F G T
          (fun a : osiiAxisPairIndex d => Complex.log (coeff a)) := by
    dsimp [osiiAxisPairWeightedTotalLogSemigroupBranch, coeff, t]
    congr 1
    calc
      ((ξ 0 / 2 + ζ 0 : ℝ) : ℂ) =
          (T : ℂ) * ∑ a : osiiAxisPairIndex d,
            osiiAxisPairCoeffMap T ξ
              (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a := by
        symm
        simpa [Complex.ofReal_add] using
          osiiAxisPairCoeffMap_time_mul_sum (d := d) T hT.ne' ξ
            (fun ν : Fin (d + 1) => (ζ ν : ℂ))
      _ =
          (T : ℂ) * ∑ a : osiiAxisPairIndex d,
            Complex.exp
              (Complex.log
                (osiiAxisPairCoeffMap T ξ
                  (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro a _ha
        have hne :
            osiiAxisPairCoeffMap T ξ
                (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a ≠ 0 := by
          intro hzero
          have hre_zero :
              (osiiAxisPairCoeffMap T ξ
                  (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a).re = 0 := by
            simp [hzero]
          linarith [hcoeff_pos a]
        exact (Complex.exp_log hne).symm
  have htarget_complex :
      OSInnerProductTimeShiftHolomorphicValueExpandBoth
          (d := d) OS lgc F G (((ξ 0 : ℂ) / 2) + (ζ 0 : ℂ)) =
        osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc F G T
          (fun a : osiiAxisPairIndex d => Complex.log (coeff a)) := by
    simpa [t, Complex.ofReal_add, Complex.ofReal_div, coeff] using htarget
  rw [← htarget_complex]
  simpa [t, Complex.ofReal_add, Complex.ofReal_div] using hlim

/-- Raw OS-II generator boundary value at an actual weighted axis-pair
coefficient point, in the concentrated Schwinger scalar form.

This is the selector statement needed before the local `(A0)` distributional
upgrade: the positive-side source current used in `(5.7)`--`(5.8)` tends to the
Schwinger value of the OS-conjugated left test tensor the shifted right test. -/
theorem tendsto_rotated_osiiAxisPairWeightedTotalLogSemigroupBranch_single_coeffMap_real
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (ξ ζ : Fin (d + 1) → ℝ)
    (hcoeff_pos :
      ∀ a : osiiAxisPairIndex d,
        0 < (osiiAxisPairCoeffMap T ξ
          (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a).re)
    (htime : 0 < ξ 0 / 2 + ζ 0) :
    Filter.Tendsto
      (fun η : ℝ =>
        ∫ x : ℝ,
          OSInnerProductTimeShiftHolomorphicValueExpandBoth
              (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single r g hg_ord)
              (-Complex.I * ((x : ℂ) + η * Complex.I)) *
            (SchwartzMap.fourierTransformCLM ℂ
              (SCV.schwartzPsiZ
                (((2 * Real.pi : ℂ) *
                  (((ξ 0 / 2 + ζ 0 : ℝ) : ℂ) * Complex.I)))
                (by
                  simpa [Complex.mul_im, htime.ne']
                    using mul_pos Real.two_pi_pos htime))) x)
      (𝓝[Set.Ioi 0] (0 : ℝ))
      (𝓝
        (OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (ξ 0 / 2 + ζ 0) g))))) := by
  have hlim :=
    tendsto_rotated_osiiAxisPairWeightedTotalLogSemigroupBranch_coeffMap_real
      (d := d) OS lgc
      (PositiveTimeBorchersSequence.single n f hf_ord)
      (PositiveTimeBorchersSequence.single r g hg_ord)
      T hT ξ ζ hcoeff_pos htime
  have htarget :
      osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single r g hg_ord) T
          (fun a : osiiAxisPairIndex d =>
            Complex.log
              (osiiAxisPairCoeffMap T ξ
                (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a)) =
        OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (ξ 0 / 2 + ζ 0) g))) := by
    exact
      osiiAxisPairWeightedTotalLogSemigroupBranch_single_coeffMap_real_edge_eq_schwinger_timeShift
        (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ ζ hcoeff_pos
  simpa [htarget] using hlim

/-- Local weighted axis-pair branch packet for single tests.

On one sufficiently small Lemma 5.1 polydisc, the normalized weighted branch is
holomorphic in the complex coordinate perturbation and its real slice is the
physical Schwinger edge with shift `xi^0 / 2 + zeta^0`. -/
theorem osiiAxisPair_weightedTotalLogSemigroupBranch_single_local_polydisc_real_edge
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧
      DifferentiableOn ℂ
        (fun ζ : Fin (d + 1) → ℂ =>
          osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single r g hg_ord) T
            (fun a : osiiAxisPairIndex d =>
              Complex.log (osiiAxisPairCoeffMap T ξ ζ a)))
        {ζ : Fin (d + 1) → ℂ | ∀ ν : Fin (d + 1), ‖ζ ν‖ < ρ} ∧
      ∀ ζ : Fin (d + 1) → ℝ,
        (∀ ν : Fin (d + 1), ‖(ζ ν : ℂ)‖ < ρ) →
          osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single r g hg_ord) T
            (fun a : osiiAxisPairIndex d =>
              Complex.log
                (osiiAxisPairCoeffMap T ξ (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a))
          =
          OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (ξ 0 / 2 + ζ 0) g))) := by
  classical
  rcases osiiAxisPair_weightedTotalLogSemigroupBranch_local_polydisc_exists_eta
      (d := d) OS lgc
      (PositiveTimeBorchersSequence.single n f hf_ord)
      (PositiveTimeBorchersSequence.single r g hg_ord)
      T hT ξ hξ0 with
    ⟨η, ρhol, hη, hρhol, hdiff_hol⟩
  rcases osiiAxisPair_exists_coord_radius_coeff_rightHalfPlane
      (d := d) T hT ξ hξ0 with
    ⟨ρpos, hρpos, hcoeff_pos_of_small⟩
  let ρ : ℝ := min ρhol ρpos
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min hρhol hρpos
  have hρ_le_hol : ρ ≤ ρhol := by
    dsimp [ρ]
    exact min_le_left _ _
  have hρ_le_pos : ρ ≤ ρpos := by
    dsimp [ρ]
    exact min_le_right _ _
  refine ⟨ρ, hρ, ?_, ?_⟩
  · exact hdiff_hol.mono (by
      intro ζ hζ ν
      exact lt_of_lt_of_le (hζ ν) hρ_le_hol)
  · intro ζ hζ
    have hcoeff_pos :
        ∀ a : osiiAxisPairIndex d,
          0 < (osiiAxisPairCoeffMap T ξ (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a).re := by
      exact hcoeff_pos_of_small
        (fun ν : Fin (d + 1) => (ζ ν : ℂ))
        (fun ν => lt_of_lt_of_le (hζ ν) hρ_le_pos)
    exact
      osiiAxisPairWeightedTotalLogSemigroupBranch_single_coeffMap_real_edge_eq_schwinger_timeShift
        (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ ζ hcoeff_pos

/-- Local weighted axis-pair branch packet with the raw positive-side selector.

After shrinking the Lemma 5.1 polydisc once more, the same neighborhood carries
holomorphy, real-edge Schwinger equality, and the raw OS-II generator boundary
limit to that Schwinger value.  This is the local `(5.7)`--`(5.8)` packet before
the dense all-test and EOW representation upgrades. -/
theorem osiiAxisPair_weightedTotalLogSemigroupBranch_single_local_polydisc_real_edge_selector
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧
      DifferentiableOn ℂ
        (fun ζ : Fin (d + 1) → ℂ =>
          osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single r g hg_ord) T
            (fun a : osiiAxisPairIndex d =>
              Complex.log (osiiAxisPairCoeffMap T ξ ζ a)))
        {ζ : Fin (d + 1) → ℂ | ∀ ν : Fin (d + 1), ‖ζ ν‖ < ρ} ∧
      (∀ ζ : Fin (d + 1) → ℝ,
        (∀ ν : Fin (d + 1), ‖(ζ ν : ℂ)‖ < ρ) →
          osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single r g hg_ord) T
            (fun a : osiiAxisPairIndex d =>
              Complex.log
                (osiiAxisPairCoeffMap T ξ (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a))
          =
          OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (ξ 0 / 2 + ζ 0) g)))) ∧
      (∀ ζ : Fin (d + 1) → ℝ,
        (∀ ν : Fin (d + 1), ‖(ζ ν : ℂ)‖ < ρ) →
          ∃ htime : 0 < ξ 0 / 2 + ζ 0,
            Filter.Tendsto
              (fun η : ℝ =>
                ∫ x : ℝ,
                  OSInnerProductTimeShiftHolomorphicValueExpandBoth
                      (d := d) OS lgc
                      (PositiveTimeBorchersSequence.single n f hf_ord)
                      (PositiveTimeBorchersSequence.single r g hg_ord)
                      (-Complex.I * ((x : ℂ) + η * Complex.I)) *
                    (SchwartzMap.fourierTransformCLM ℂ
                      (SCV.schwartzPsiZ
                        (((2 * Real.pi : ℂ) *
                          (((ξ 0 / 2 + ζ 0 : ℝ) : ℂ) * Complex.I)))
                        (by
                          simpa [Complex.mul_im, htime.ne']
                            using mul_pos Real.two_pi_pos htime))) x)
              (𝓝[Set.Ioi 0] (0 : ℝ))
              (𝓝
                (OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
                  (f.osConjTensorProduct
                    (timeShiftSchwartzNPoint (d := d) (ξ 0 / 2 + ζ 0) g)))))) := by
  classical
  rcases osiiAxisPair_weightedTotalLogSemigroupBranch_single_local_polydisc_real_edge
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ hξ0 with
    ⟨ρedge, hρedge, hdiff_edge, hreal_edge⟩
  rcases osiiAxisPair_exists_coord_radius_coeff_rightHalfPlane
      (d := d) T hT ξ hξ0 with
    ⟨ρpos, hρpos, hcoeff_pos_of_small⟩
  let ρ : ℝ := min ρedge (min ρpos (ξ 0 / 4))
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min hρedge (lt_min hρpos (by positivity))
  have hρ_le_edge : ρ ≤ ρedge := by
    dsimp [ρ]
    exact min_le_left _ _
  have hρ_le_pos : ρ ≤ ρpos := by
    dsimp [ρ]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρ_le_time : ρ ≤ ξ 0 / 4 := by
    dsimp [ρ]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨ρ, hρ, ?_, ?_, ?_⟩
  · exact hdiff_edge.mono (by
      intro ζ hζ ν
      exact lt_of_lt_of_le (hζ ν) hρ_le_edge)
  · intro ζ hζ
    exact hreal_edge ζ (fun ν => lt_of_lt_of_le (hζ ν) hρ_le_edge)
  · intro ζ hζ
    have hcoeff_pos :
        ∀ a : osiiAxisPairIndex d,
          0 < (osiiAxisPairCoeffMap T ξ
            (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a).re := by
      exact hcoeff_pos_of_small
        (fun ν : Fin (d + 1) => (ζ ν : ℂ))
        (fun ν => lt_of_lt_of_le (hζ ν) hρ_le_pos)
    have hζ0_abs : |ζ 0| < ξ 0 / 4 := by
      have hζ0_complex : ‖(ζ 0 : ℂ)‖ < ξ 0 / 4 :=
        lt_of_lt_of_le (hζ 0) hρ_le_time
      simpa [Real.norm_eq_abs] using hζ0_complex
    have htime : 0 < ξ 0 / 2 + ζ 0 := by
      have hζ0_gt : -(ξ 0 / 4) < ζ 0 := (abs_lt.mp hζ0_abs).1
      nlinarith [hξ0, hζ0_gt]
    exact ⟨htime,
      tendsto_rotated_osiiAxisPairWeightedTotalLogSemigroupBranch_single_coeffMap_real
        (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ ζ hcoeff_pos htime⟩

/-- Local weighted axis-pair branch packet with the real-slice compact bound.

This is the Banach-Steinhaus-facing strengthening of
`osiiAxisPair_weightedTotalLogSemigroupBranch_single_local_polydisc_real_edge_selector`:
after one common shrink, the same Lemma 5.1 neighborhood carries holomorphy,
real-edge Schwinger identification, raw positive-side selector convergence, and
uniform boundedness on the compact real slice. -/
theorem osiiAxisPair_weightedTotalLogSemigroupBranch_single_local_polydisc_real_edge_selector_bound
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      DifferentiableOn ℂ
        (fun ζ : Fin (d + 1) → ℂ =>
          osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single r g hg_ord) T
            (fun a : osiiAxisPairIndex d =>
              Complex.log (osiiAxisPairCoeffMap T ξ ζ a)))
        {ζ : Fin (d + 1) → ℂ | ∀ ν : Fin (d + 1), ‖ζ ν‖ < ρ} ∧
      (∀ ζ : Fin (d + 1) → ℝ,
        (∀ ν : Fin (d + 1), ‖(ζ ν : ℂ)‖ < ρ) →
          osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single r g hg_ord) T
            (fun a : osiiAxisPairIndex d =>
              Complex.log
                (osiiAxisPairCoeffMap T ξ (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a))
          =
          OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (ξ 0 / 2 + ζ 0) g)))) ∧
      (∀ ζ : Fin (d + 1) → ℝ,
        (∀ ν : Fin (d + 1), ‖(ζ ν : ℂ)‖ < ρ) →
          ∃ htime : 0 < ξ 0 / 2 + ζ 0,
            Filter.Tendsto
              (fun η : ℝ =>
                ∫ x : ℝ,
                  OSInnerProductTimeShiftHolomorphicValueExpandBoth
                      (d := d) OS lgc
                      (PositiveTimeBorchersSequence.single n f hf_ord)
                      (PositiveTimeBorchersSequence.single r g hg_ord)
                      (-Complex.I * ((x : ℂ) + η * Complex.I)) *
                    (SchwartzMap.fourierTransformCLM ℂ
                      (SCV.schwartzPsiZ
                        (((2 * Real.pi : ℂ) *
                          (((ξ 0 / 2 + ζ 0 : ℝ) : ℂ) * Complex.I)))
                        (by
                          simpa [Complex.mul_im, htime.ne']
                            using mul_pos Real.two_pi_pos htime))) x)
              (𝓝[Set.Ioi 0] (0 : ℝ))
              (𝓝
                (OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
                  (f.osConjTensorProduct
                    (timeShiftSchwartzNPoint (d := d) (ξ 0 / 2 + ζ 0) g)))))) ∧
      ∀ ζ : Fin (d + 1) → ℝ,
        ζ ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) ρ →
          ‖osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single r g hg_ord) T
            (fun a : osiiAxisPairIndex d =>
              Complex.log
                (osiiAxisPairCoeffMap T ξ (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a))‖ ≤ C := by
  classical
  rcases
    osiiAxisPair_weightedTotalLogSemigroupBranch_single_local_polydisc_real_edge_selector
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ hξ0 with
    ⟨ρsel, hρsel, hdiff, hreal, hselector⟩
  rcases
    osiiAxisPair_weightedTotalLogSemigroupBranch_local_realSlice_bound
      (d := d) OS lgc
      (PositiveTimeBorchersSequence.single n f hf_ord)
      (PositiveTimeBorchersSequence.single r g hg_ord)
      T hT ξ hξ0 with
    ⟨ρbound, C, hρbound, hC, hbound⟩
  let ρ : ℝ := min ρsel ρbound
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min hρsel hρbound
  have hρ_le_sel : ρ ≤ ρsel := by
    dsimp [ρ]
    exact min_le_left _ _
  have hρ_le_bound : ρ ≤ ρbound := by
    dsimp [ρ]
    exact min_le_right _ _
  refine ⟨ρ, C, hρ, hC, ?_, ?_, ?_, ?_⟩
  · exact hdiff.mono (by
      intro ζ hζ ν
      exact lt_of_lt_of_le (hζ ν) hρ_le_sel)
  · intro ζ hζ
    exact hreal ζ (fun ν => lt_of_lt_of_le (hζ ν) hρ_le_sel)
  · intro ζ hζ
    exact hselector ζ (fun ν => lt_of_lt_of_le (hζ ν) hρ_le_sel)
  · intro ζ hζ
    exact hbound ζ (by
      rw [Metric.mem_closedBall, dist_eq_norm] at hζ ⊢
      exact hζ.trans hρ_le_bound)

/-- Local weighted axis-pair selector with the MZ branch itself as target.

The raw selector theorem above is Schwinger-normalized; the local EOW
boundary-value handoff needs convergence to the explicit side branch.  On the
real edge these are the same by the Lemma 5.1 real-edge identity, so this
theorem packages exactly that target conversion while keeping the holomorphy
and compact real-slice bound on the same local neighborhood. -/
theorem osiiAxisPair_weightedTotalLogSemigroupBranch_single_local_polydisc_branch_selector_bound
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      DifferentiableOn ℂ
        (fun ζ : Fin (d + 1) → ℂ =>
          osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single r g hg_ord) T
            (fun a : osiiAxisPairIndex d =>
              Complex.log (osiiAxisPairCoeffMap T ξ ζ a)))
        {ζ : Fin (d + 1) → ℂ | ∀ ν : Fin (d + 1), ‖ζ ν‖ < ρ} ∧
      (∀ ζ : Fin (d + 1) → ℝ,
        (∀ ν : Fin (d + 1), ‖(ζ ν : ℂ)‖ < ρ) →
          ∃ htime : 0 < ξ 0 / 2 + ζ 0,
            Filter.Tendsto
              (fun η : ℝ =>
                ∫ x : ℝ,
                  OSInnerProductTimeShiftHolomorphicValueExpandBoth
                      (d := d) OS lgc
                      (PositiveTimeBorchersSequence.single n f hf_ord)
                      (PositiveTimeBorchersSequence.single r g hg_ord)
                      (-Complex.I * ((x : ℂ) + η * Complex.I)) *
                    (SchwartzMap.fourierTransformCLM ℂ
                      (SCV.schwartzPsiZ
                        (((2 * Real.pi : ℂ) *
                          (((ξ 0 / 2 + ζ 0 : ℝ) : ℂ) * Complex.I)))
                        (by
                          simpa [Complex.mul_im, htime.ne']
                            using mul_pos Real.two_pi_pos htime))) x)
              (𝓝[Set.Ioi 0] (0 : ℝ))
              (𝓝
                (osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
                  (PositiveTimeBorchersSequence.single n f hf_ord)
                  (PositiveTimeBorchersSequence.single r g hg_ord) T
                  (fun a : osiiAxisPairIndex d =>
                    Complex.log
                      (osiiAxisPairCoeffMap T ξ
                        (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a))))) ∧
      ∀ ζ : Fin (d + 1) → ℝ,
        ζ ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) ρ →
          ‖osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single r g hg_ord) T
            (fun a : osiiAxisPairIndex d =>
              Complex.log
                (osiiAxisPairCoeffMap T ξ (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a))‖ ≤ C := by
  classical
  rcases
    osiiAxisPair_weightedTotalLogSemigroupBranch_single_local_polydisc_real_edge_selector_bound
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ hξ0 with
    ⟨ρ, C, hρ, hC, hdiff, hreal, hselector, hbound⟩
  refine ⟨ρ, C, hρ, hC, hdiff, ?_, hbound⟩
  intro ζ hζ
  rcases hselector ζ hζ with ⟨htime, hlim⟩
  refine ⟨htime, ?_⟩
  have htarget :
      OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (ξ 0 / 2 + ζ 0) g))) =
        osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single r g hg_ord) T
          (fun a : osiiAxisPairIndex d =>
            Complex.log
              (osiiAxisPairCoeffMap T ξ
                (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a)) := by
    exact (hreal ζ hζ).symm
  simpa [htarget] using hlim

/-- Real-edge overlap equality for two weighted axis-pair local MZ branches.

The only datum that survives the return from logarithmic coefficient variables
is the physical time displacement `ξ⁰ / 2 + ζ⁰`; if two local charts have the
same value of that displacement, their real-edge branch values are the same
Schwinger scalar.  This is the concrete real-slice equality fed to the
Malgrange-Zerner identity/gluing step. -/
theorem osiiAxisPairWeightedTotalLogSemigroupBranch_single_coeffMap_real_edge_eq_of_time_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (ξ₁ ξ₂ ζ₁ ζ₂ : Fin (d + 1) → ℝ)
    (hcoeff₁ :
      ∀ a : osiiAxisPairIndex d,
        0 < (osiiAxisPairCoeffMap T ξ₁
          (fun ν : Fin (d + 1) => (ζ₁ ν : ℂ)) a).re)
    (hcoeff₂ :
      ∀ a : osiiAxisPairIndex d,
        0 < (osiiAxisPairCoeffMap T ξ₂
          (fun ν : Fin (d + 1) => (ζ₂ ν : ℂ)) a).re)
    (htime : ξ₁ 0 / 2 + ζ₁ 0 = ξ₂ 0 / 2 + ζ₂ 0) :
    osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single r g hg_ord) T
        (fun a : osiiAxisPairIndex d =>
          Complex.log
            (osiiAxisPairCoeffMap T ξ₁
              (fun ν : Fin (d + 1) => (ζ₁ ν : ℂ)) a)) =
      osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single r g hg_ord) T
        (fun a : osiiAxisPairIndex d =>
          Complex.log
            (osiiAxisPairCoeffMap T ξ₂
              (fun ν : Fin (d + 1) => (ζ₂ ν : ℂ)) a)) := by
  classical
  have h₁ :=
    osiiAxisPairWeightedTotalLogSemigroupBranch_single_coeffMap_real_edge_eq_schwinger_timeShift
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ₁ ζ₁ hcoeff₁
  have h₂ :=
    osiiAxisPairWeightedTotalLogSemigroupBranch_single_coeffMap_real_edge_eq_schwinger_timeShift
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ₂ ζ₂ hcoeff₂
  calc
    osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single r g hg_ord) T
        (fun a : osiiAxisPairIndex d =>
          Complex.log
            (osiiAxisPairCoeffMap T ξ₁
              (fun ν : Fin (d + 1) => (ζ₁ ν : ℂ)) a))
        =
      OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (ξ₁ 0 / 2 + ζ₁ 0) g))) := h₁
    _ =
      OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (ξ₂ 0 / 2 + ζ₂ 0) g))) := by
        rw [htime]
    _ =
      osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single r g hg_ord) T
        (fun a : osiiAxisPairIndex d =>
          Complex.log
            (osiiAxisPairCoeffMap T ξ₂
              (fun ν : Fin (d + 1) => (ζ₂ ν : ℂ)) a)) := h₂.symm

/-- Local-radius form of the real-edge overlap equality.

This is the form used by Malgrange-Zerner gluing: after choosing the Lemma 5.1
coefficient radii at two positive centers, the corresponding real-edge branches
agree at any pair of small real perturbations with the same physical time
displacement. -/
theorem osiiAxisPairWeightedTotalLogSemigroupBranch_single_local_real_edge_eq_of_time_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (ξ₁ ξ₂ : Fin (d + 1) → ℝ)
    (hξ₁0 : 0 < ξ₁ 0) (hξ₂0 : 0 < ξ₂ 0) :
    ∃ ρ₁ ρ₂ : ℝ, 0 < ρ₁ ∧ 0 < ρ₂ ∧
      ∀ ζ₁ ζ₂ : Fin (d + 1) → ℝ,
        (∀ ν : Fin (d + 1), ‖(ζ₁ ν : ℂ)‖ < ρ₁) →
        (∀ ν : Fin (d + 1), ‖(ζ₂ ν : ℂ)‖ < ρ₂) →
        ξ₁ 0 / 2 + ζ₁ 0 = ξ₂ 0 / 2 + ζ₂ 0 →
          osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single r g hg_ord) T
              (fun a : osiiAxisPairIndex d =>
                Complex.log
                  (osiiAxisPairCoeffMap T ξ₁
                    (fun ν : Fin (d + 1) => (ζ₁ ν : ℂ)) a)) =
            osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single r g hg_ord) T
              (fun a : osiiAxisPairIndex d =>
                Complex.log
                  (osiiAxisPairCoeffMap T ξ₂
                    (fun ν : Fin (d + 1) => (ζ₂ ν : ℂ)) a)) := by
  classical
  rcases osiiAxisPair_exists_coord_radius_coeff_rightHalfPlane
      (d := d) T hT ξ₁ hξ₁0 with
    ⟨ρ₁, hρ₁, hcoeff₁⟩
  rcases osiiAxisPair_exists_coord_radius_coeff_rightHalfPlane
      (d := d) T hT ξ₂ hξ₂0 with
    ⟨ρ₂, hρ₂, hcoeff₂⟩
  refine ⟨ρ₁, ρ₂, hρ₁, hρ₂, ?_⟩
  intro ζ₁ ζ₂ hζ₁ hζ₂ htime
  exact
    osiiAxisPairWeightedTotalLogSemigroupBranch_single_coeffMap_real_edge_eq_of_time_eq
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT
      ξ₁ ξ₂ ζ₁ ζ₂ (hcoeff₁ (fun ν => (ζ₁ ν : ℂ)) hζ₁)
      (hcoeff₂ (fun ν => (ζ₂ ν : ℂ)) hζ₂) htime

/-- Pull a common time-shell coordinate back to the local axis-pair
perturbation coordinate at center `ξ`.

The zero component is normalized so that the semigroup time in the weighted
axis-pair branch is the common shell time:
`ξ⁰ / 2 + ζ⁰ = τ⁰`.  This is the coordinate correction needed before applying
Malgrange-Zerner overlap to neighboring local branches. -/
def osiiAxisPairTimeShellPerturbation
    (ξ τ : Fin (d + 1) → ℝ) : Fin (d + 1) → ℝ :=
  Fin.cases (τ 0 - ξ 0 / 2) (fun j => τ (Fin.succ j) - ξ (Fin.succ j))

/-- Complex version of `osiiAxisPairTimeShellPerturbation`, used for
holomorphicity of the time-shell pullback. -/
def osiiAxisPairTimeShellPerturbationC
    (ξ : Fin (d + 1) → ℝ) (τ : Fin (d + 1) → ℂ) :
    Fin (d + 1) → ℂ :=
  Fin.cases (τ 0 - ((ξ 0 / 2 : ℝ) : ℂ))
    (fun j => τ (Fin.succ j) - (ξ (Fin.succ j) : ℂ))

/-- Center associated to a time-shell coordinate.

Choosing center `(2τ⁰, τ^space)` makes the corrected perturbation of `τ`
equal to zero, so compact shell supports are covered by genuine Lemma 5.1
windows with the right semigroup-time normalization. -/
def osiiAxisPairTimeShellCenter
    (τ : Fin (d + 1) → ℝ) : Fin (d + 1) → ℝ :=
  Fin.cases (2 * τ 0) (fun j => τ (Fin.succ j))

/-- Real time-shell window for a fixed axis-pair center. -/
def osiiAxisPairTimeShellWindow
    (ξ : Fin (d + 1) → ℝ) (ρ : ℝ) : Set (Fin (d + 1) → ℝ) :=
  {τ | ∀ ν : Fin (d + 1),
    ‖(osiiAxisPairTimeShellPerturbation (d := d) ξ τ ν : ℂ)‖ < ρ}

/-- Complex time-shell window for a fixed axis-pair center. -/
def osiiAxisPairTimeShellComplexWindow
    (ξ : Fin (d + 1) → ℝ) (ρ : ℝ) : Set (Fin (d + 1) → ℂ) :=
  {τ | ∀ ν : Fin (d + 1),
    ‖osiiAxisPairTimeShellPerturbationC (d := d) ξ τ ν‖ < ρ}

/-- The actual weighted axis-pair MZ branch in corrected time-shell
coordinates. -/
def osiiAxisPairWeightedTimeShellBranch
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (T : ℝ) (ξ : Fin (d + 1) → ℝ) :
    (Fin (d + 1) → ℂ) → ℂ :=
  fun τ =>
    osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
      (PositiveTimeBorchersSequence.single n f hf_ord)
      (PositiveTimeBorchersSequence.single r g hg_ord) T
      (fun a : osiiAxisPairIndex d =>
        Complex.log
          (osiiAxisPairCoeffMap T ξ
            (osiiAxisPairTimeShellPerturbationC (d := d) ξ τ) a))

omit [NeZero d] in
theorem osiiAxisPairTimeShellCenter_time_pos
    {τ : Fin (d + 1) → ℝ} (hτ0 : 0 < τ 0) :
    0 < osiiAxisPairTimeShellCenter (d := d) τ 0 := by
  simp [osiiAxisPairTimeShellCenter, hτ0]

omit [NeZero d] in
theorem osiiAxisPairTimeShellPerturbation_center_self
    (τ : Fin (d + 1) → ℝ) :
    osiiAxisPairTimeShellPerturbation (d := d)
      (osiiAxisPairTimeShellCenter (d := d) τ) τ = 0 := by
  funext ν
  refine Fin.cases ?_ ?_ ν
  · simp [osiiAxisPairTimeShellPerturbation, osiiAxisPairTimeShellCenter]
  · intro j
    simp [osiiAxisPairTimeShellPerturbation, osiiAxisPairTimeShellCenter]

omit [NeZero d] in
theorem isOpen_osiiAxisPairTimeShellWindow
    (ξ : Fin (d + 1) → ℝ) {ρ : ℝ} :
    IsOpen (osiiAxisPairTimeShellWindow (d := d) ξ ρ) := by
  classical
  unfold osiiAxisPairTimeShellWindow
  have hset :
      {τ : Fin (d + 1) → ℝ | ∀ ν : Fin (d + 1),
        ‖(osiiAxisPairTimeShellPerturbation (d := d) ξ τ ν : ℂ)‖ < ρ} =
        ⋂ ν : Fin (d + 1),
          {τ : Fin (d + 1) → ℝ |
            ‖(osiiAxisPairTimeShellPerturbation (d := d) ξ τ ν : ℂ)‖ < ρ} := by
    ext τ
    simp
  rw [hset]
  apply isOpen_iInter_of_finite
  intro ν
  have hcont :
      Continuous (fun τ : Fin (d + 1) → ℝ =>
        ‖(osiiAxisPairTimeShellPerturbation (d := d) ξ τ ν : ℂ)‖) := by
    refine continuous_norm.comp ?_
    refine Fin.cases ?_ ?_ ν
    · simp [osiiAxisPairTimeShellPerturbation]
      fun_prop
    · intro j
      simp [osiiAxisPairTimeShellPerturbation]
      fun_prop
  exact isOpen_lt hcont continuous_const

omit [NeZero d] in
theorem isOpen_osiiAxisPairTimeShellComplexWindow
    (ξ : Fin (d + 1) → ℝ) {ρ : ℝ} :
    IsOpen (osiiAxisPairTimeShellComplexWindow (d := d) ξ ρ) := by
  classical
  unfold osiiAxisPairTimeShellComplexWindow
  have hset :
      {τ : Fin (d + 1) → ℂ | ∀ ν : Fin (d + 1),
        ‖osiiAxisPairTimeShellPerturbationC (d := d) ξ τ ν‖ < ρ} =
        ⋂ ν : Fin (d + 1),
          {τ : Fin (d + 1) → ℂ |
            ‖osiiAxisPairTimeShellPerturbationC (d := d) ξ τ ν‖ < ρ} := by
    ext τ
    simp
  rw [hset]
  apply isOpen_iInter_of_finite
  intro ν
  have hcont :
      Continuous (fun τ : Fin (d + 1) → ℂ =>
        ‖osiiAxisPairTimeShellPerturbationC (d := d) ξ τ ν‖) := by
    refine continuous_norm.comp ?_
    refine Fin.cases ?_ ?_ ν
    · simp [osiiAxisPairTimeShellPerturbationC]
      fun_prop
    · intro j
      simp [osiiAxisPairTimeShellPerturbationC]
      fun_prop
  exact isOpen_lt hcont continuous_const

omit [NeZero d] in
theorem osiiAxisPairTimeShellPerturbationC_realPart
    (ξ : Fin (d + 1) → ℝ) (z : Fin (d + 1) → ℂ)
    (ν : Fin (d + 1)) :
    osiiAxisPairTimeShellPerturbationC (d := d) ξ
        (SCV.realToComplex (fun μ : Fin (d + 1) => (z μ).re)) ν =
      ((osiiAxisPairTimeShellPerturbationC (d := d) ξ z ν).re : ℂ) := by
  refine Fin.cases ?_ ?_ ν
  · simp [osiiAxisPairTimeShellPerturbationC, SCV.realToComplex,
      Complex.ofReal_sub, Complex.ofReal_div]
  · intro j
    simp [osiiAxisPairTimeShellPerturbationC, SCV.realToComplex,
      Complex.ofReal_sub]

/-- The coordinatewise real part of a point in a complex time-shell window stays
inside the same window. -/
theorem osiiAxisPairTimeShellComplexWindow_realPart_mem
    {ξ : Fin (d + 1) → ℝ} {ρ : ℝ} {z : Fin (d + 1) → ℂ}
    (hz : z ∈ osiiAxisPairTimeShellComplexWindow (d := d) ξ ρ) :
    SCV.realToComplex (fun ν : Fin (d + 1) => (z ν).re) ∈
      osiiAxisPairTimeShellComplexWindow (d := d) ξ ρ := by
  intro ν
  rw [osiiAxisPairTimeShellPerturbationC_realPart]
  calc
    ‖(((osiiAxisPairTimeShellPerturbationC (d := d) ξ z ν).re : ℝ) : ℂ)‖
        = |(osiiAxisPairTimeShellPerturbationC (d := d) ξ z ν).re| := by
          simpa using
            (RCLike.norm_ofReal (K := ℂ)
              ((osiiAxisPairTimeShellPerturbationC (d := d) ξ z ν).re))
    _ ≤ ‖osiiAxisPairTimeShellPerturbationC (d := d) ξ z ν‖ :=
        Complex.abs_re_le_norm _
    _ < ρ := hz ν

/-- A nonempty complex overlap of two corrected time-shell windows contains a
real point, obtained by taking coordinatewise real parts. -/
theorem osiiAxisPairTimeShellComplexWindow_inter_realPart_nonempty
    {ξ₁ ξ₂ : Fin (d + 1) → ℝ} {ρ₁ ρ₂ : ℝ}
    {z : Fin (d + 1) → ℂ}
    (hz : z ∈
      osiiAxisPairTimeShellComplexWindow (d := d) ξ₁ ρ₁ ∩
        osiiAxisPairTimeShellComplexWindow (d := d) ξ₂ ρ₂) :
    ∃ x : Fin (d + 1) → ℝ,
      SCV.realToComplex x ∈
        osiiAxisPairTimeShellComplexWindow (d := d) ξ₁ ρ₁ ∩
          osiiAxisPairTimeShellComplexWindow (d := d) ξ₂ ρ₂ := by
  refine ⟨fun ν : Fin (d + 1) => (z ν).re, ?_⟩
  exact ⟨
    osiiAxisPairTimeShellComplexWindow_realPart_mem (d := d) hz.1,
    osiiAxisPairTimeShellComplexWindow_realPart_mem (d := d) hz.2⟩

omit [NeZero d] in
theorem osiiAxisPairTimeShellPerturbation_time
    (ξ τ : Fin (d + 1) → ℝ) :
    ξ 0 / 2 + osiiAxisPairTimeShellPerturbation (d := d) ξ τ 0 = τ 0 := by
  simp [osiiAxisPairTimeShellPerturbation]

omit [NeZero d] in
theorem osiiAxisPairTimeShellPerturbationC_ofReal
    (ξ τ : Fin (d + 1) → ℝ) :
    osiiAxisPairTimeShellPerturbationC (d := d) ξ
        (fun ν : Fin (d + 1) => (τ ν : ℂ)) =
      fun ν : Fin (d + 1) =>
        (osiiAxisPairTimeShellPerturbation (d := d) ξ τ ν : ℂ) := by
  funext ν
  refine Fin.cases ?_ ?_ ν
  · simp [osiiAxisPairTimeShellPerturbationC,
      osiiAxisPairTimeShellPerturbation, Complex.ofReal_sub,
      Complex.ofReal_div]
  · intro j
    simp [osiiAxisPairTimeShellPerturbationC,
      osiiAxisPairTimeShellPerturbation, Complex.ofReal_sub]

/-- Complex time-shell normalization of the corrected perturbation coordinate. -/
theorem osiiAxisPairTimeShellPerturbationC_time
    (ξ : Fin (d + 1) → ℝ) (τ : Fin (d + 1) → ℂ) :
    ((ξ 0 / 2 : ℝ) : ℂ) +
        osiiAxisPairTimeShellPerturbationC (d := d) ξ τ 0 =
      τ 0 := by
  simp [osiiAxisPairTimeShellPerturbationC]

/-- Complex time-shell form of the weighted axis-pair coefficient sum.

This is the finite-height normalization behind the OS-II return from the
logarithmic Lemma 5.1 variables to the physical semigroup time. -/
theorem osiiAxisPairCoeffMap_time_mul_sum_timeShellC
    (T : ℝ) (hT : T ≠ 0)
    (ξ : Fin (d + 1) → ℝ) (τ : Fin (d + 1) → ℂ) :
    ((T : ℂ) * ∑ a : osiiAxisPairIndex d,
        osiiAxisPairCoeffMap T ξ
          (osiiAxisPairTimeShellPerturbationC (d := d) ξ τ) a) =
      τ 0 := by
  calc
    ((T : ℂ) * ∑ a : osiiAxisPairIndex d,
        osiiAxisPairCoeffMap T ξ
          (osiiAxisPairTimeShellPerturbationC (d := d) ξ τ) a)
        =
      ((ξ 0 / 2 : ℝ) : ℂ) +
        osiiAxisPairTimeShellPerturbationC (d := d) ξ τ 0 :=
        osiiAxisPairCoeffMap_time_mul_sum (d := d) T hT ξ
          (osiiAxisPairTimeShellPerturbationC (d := d) ξ τ)
    _ = τ 0 :=
        osiiAxisPairTimeShellPerturbationC_time (d := d) ξ τ

/-- Finite-height value of the weighted axis-pair time-shell branch.

On the actual Lemma 5.1 logarithmic carrier, the principal logarithms exponentiate
back to the axis-pair coefficients.  The weighted coefficient sum is the common
time-shell coordinate `τ 0`, so the MZ log branch is the one-variable OS
semigroup branch evaluated at that finite complex time. -/
theorem osiiAxisPairWeightedTimeShellBranch_eq_semigroup_time
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (T : ℝ) (hT : T ≠ 0)
    (ξ : Fin (d + 1) → ℝ) (τ : Fin (d + 1) → ℂ)
    (hcoeff_ne :
      ∀ a : osiiAxisPairIndex d,
        osiiAxisPairCoeffMap T ξ
          (osiiAxisPairTimeShellPerturbationC (d := d) ξ τ) a ≠ 0) :
    osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
        f hf_ord g hg_ord T ξ τ =
      OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single r g hg_ord)
        (τ 0) := by
  unfold osiiAxisPairWeightedTimeShellBranch
    osiiAxisPairWeightedTotalLogSemigroupBranch
  congr 1
  calc
    ((T : ℂ) * ∑ a : osiiAxisPairIndex d,
        Complex.exp
          (Complex.log
            (osiiAxisPairCoeffMap T ξ
              (osiiAxisPairTimeShellPerturbationC (d := d) ξ τ) a)))
        =
      (T : ℂ) * ∑ a : osiiAxisPairIndex d,
        osiiAxisPairCoeffMap T ξ
          (osiiAxisPairTimeShellPerturbationC (d := d) ξ τ) a := by
        congr 1
        exact Finset.sum_congr rfl
          (fun a _ha => Complex.exp_log (hcoeff_ne a))
    _ = τ 0 :=
        osiiAxisPairCoeffMap_time_mul_sum_timeShellC
          (d := d) T hT ξ τ

/-- Side-kernel form of
`osiiAxisPairWeightedTimeShellBranch_eq_semigroup_time`.

This is the finite-height integrand identity needed by the OS-II `(5.7)`--`(5.8)`
side-boundary argument: at a real point `x` and side height `y`, the corrected
axis-pair MZ branch is the one-variable semigroup branch at
`x⁰ + i y⁰`, once the local coefficient carrier keeps the logarithms nonzero. -/
theorem osiiAxisPairWeightedTimeShellBranch_realImag_eq_semigroup_time
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (T : ℝ) (hT : T ≠ 0)
    (ξ x y : Fin (d + 1) → ℝ)
    (hcoeff_ne :
      ∀ a : osiiAxisPairIndex d,
        osiiAxisPairCoeffMap T ξ
          (osiiAxisPairTimeShellPerturbationC (d := d) ξ
            (fun ν : Fin (d + 1) =>
              (x ν : ℂ) + ((y ν : ℝ) : ℂ) * Complex.I)) a ≠ 0) :
    osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
        f hf_ord g hg_ord T ξ
        (fun ν : Fin (d + 1) =>
          (x ν : ℂ) + ((y ν : ℝ) : ℂ) * Complex.I) =
      OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single r g hg_ord)
        ((x 0 : ℂ) + ((y 0 : ℝ) : ℂ) * Complex.I) := by
  simpa using
    osiiAxisPairWeightedTimeShellBranch_eq_semigroup_time
      (d := d) OS lgc f hf_ord g hg_ord T hT ξ
      (fun ν : Fin (d + 1) =>
        (x ν : ℂ) + ((y ν : ℝ) : ℂ) * Complex.I)
      hcoeff_ne

/-- Time-shell form of the local real-edge overlap equality.

The previous overlap theorem is keyed to `ξ⁰ / 2 + ζ⁰`.  In the fixed-window
local-EOW handoff the two charts are compared at a common shell coordinate
`τ`; this theorem inserts the correct pullback `ζ⁰ = τ⁰ - ξ⁰ / 2` for each
center before applying the real-edge identity. -/
theorem osiiAxisPairWeightedTotalLogSemigroupBranch_single_timeShell_local_real_edge_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (ξ₁ ξ₂ : Fin (d + 1) → ℝ)
    (hξ₁0 : 0 < ξ₁ 0) (hξ₂0 : 0 < ξ₂ 0) :
    ∃ ρ₁ ρ₂ : ℝ, 0 < ρ₁ ∧ 0 < ρ₂ ∧
      ∀ τ : Fin (d + 1) → ℝ,
        (∀ ν : Fin (d + 1),
          ‖(osiiAxisPairTimeShellPerturbation (d := d) ξ₁ τ ν : ℂ)‖ < ρ₁) →
        (∀ ν : Fin (d + 1),
          ‖(osiiAxisPairTimeShellPerturbation (d := d) ξ₂ τ ν : ℂ)‖ < ρ₂) →
          osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single r g hg_ord) T
              (fun a : osiiAxisPairIndex d =>
                Complex.log
                  (osiiAxisPairCoeffMap T ξ₁
                    (fun ν : Fin (d + 1) =>
                      (osiiAxisPairTimeShellPerturbation (d := d) ξ₁ τ ν : ℂ)) a)) =
            osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single r g hg_ord) T
              (fun a : osiiAxisPairIndex d =>
                Complex.log
                  (osiiAxisPairCoeffMap T ξ₂
                    (fun ν : Fin (d + 1) =>
                      (osiiAxisPairTimeShellPerturbation (d := d) ξ₂ τ ν : ℂ)) a)) := by
  classical
  rcases
    osiiAxisPairWeightedTotalLogSemigroupBranch_single_local_real_edge_eq_of_time_eq
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ₁ ξ₂
      hξ₁0 hξ₂0 with
    ⟨ρ₁, ρ₂, hρ₁, hρ₂, heq⟩
  refine ⟨ρ₁, ρ₂, hρ₁, hρ₂, ?_⟩
  intro τ hτ₁ hτ₂
  exact heq
    (osiiAxisPairTimeShellPerturbation (d := d) ξ₁ τ)
    (osiiAxisPairTimeShellPerturbation (d := d) ξ₂ τ)
    hτ₁ hτ₂
    (by
      rw [osiiAxisPairTimeShellPerturbation_time,
        osiiAxisPairTimeShellPerturbation_time])

/-- Local weighted branch selector packet in time-shell coordinates.

This is the fixed-window form of the raw OS-II `(5.7)`--`(5.8)` packet: the
axis-pair branch is pulled back from local perturbation coordinates to a common
time-shell coordinate, preserving holomorphy, the one-sided selector limit, and
the real-slice bound on the same corrected window. -/
theorem osiiAxisPair_weightedTotalLogSemigroupBranch_single_timeShell_local_packet
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      DifferentiableOn ℂ
        (fun τ : Fin (d + 1) → ℂ =>
          osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single r g hg_ord) T
            (fun a : osiiAxisPairIndex d =>
              Complex.log
                (osiiAxisPairCoeffMap T ξ
                  (osiiAxisPairTimeShellPerturbationC (d := d) ξ τ) a)))
        {τ : Fin (d + 1) → ℂ |
          ∀ ν : Fin (d + 1),
            ‖osiiAxisPairTimeShellPerturbationC (d := d) ξ τ ν‖ < ρ} ∧
      (∀ τ : Fin (d + 1) → ℝ,
        (∀ ν : Fin (d + 1),
          ‖(osiiAxisPairTimeShellPerturbation (d := d) ξ τ ν : ℂ)‖ < ρ) →
          osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
            f hf_ord g hg_ord T ξ
            (fun ν : Fin (d + 1) => (τ ν : ℂ)) =
            OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
              (f.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) (τ 0) g)))) ∧
      (∀ τ : Fin (d + 1) → ℝ,
        (∀ ν : Fin (d + 1),
          ‖(osiiAxisPairTimeShellPerturbation (d := d) ξ τ ν : ℂ)‖ < ρ) →
          ∃ htime : 0 < τ 0,
            Filter.Tendsto
              (fun η : ℝ =>
                ∫ x : ℝ,
                  OSInnerProductTimeShiftHolomorphicValueExpandBoth
                      (d := d) OS lgc
                      (PositiveTimeBorchersSequence.single n f hf_ord)
                      (PositiveTimeBorchersSequence.single r g hg_ord)
                      (-Complex.I * ((x : ℂ) + η * Complex.I)) *
                    (SchwartzMap.fourierTransformCLM ℂ
                      (SCV.schwartzPsiZ
                        (((2 * Real.pi : ℂ) *
                          (((τ 0 : ℝ) : ℂ) * Complex.I)))
                        (by
                          simpa [Complex.mul_im, htime.ne']
                            using mul_pos Real.two_pi_pos htime))) x)
              (𝓝[Set.Ioi 0] (0 : ℝ))
              (𝓝
                (osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
                  (PositiveTimeBorchersSequence.single n f hf_ord)
                  (PositiveTimeBorchersSequence.single r g hg_ord) T
                  (fun a : osiiAxisPairIndex d =>
                    Complex.log
                      (osiiAxisPairCoeffMap T ξ
                        (fun ν : Fin (d + 1) =>
                          (osiiAxisPairTimeShellPerturbation
                            (d := d) ξ τ ν : ℂ)) a))))) ∧
      ∀ τ : Fin (d + 1) → ℝ,
        osiiAxisPairTimeShellPerturbation (d := d) ξ τ ∈
          Metric.closedBall (0 : Fin (d + 1) → ℝ) ρ →
          ‖osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single r g hg_ord) T
            (fun a : osiiAxisPairIndex d =>
              Complex.log
                (osiiAxisPairCoeffMap T ξ
                  (fun ν : Fin (d + 1) =>
                    (osiiAxisPairTimeShellPerturbation
                      (d := d) ξ τ ν : ℂ)) a))‖ ≤ C := by
  classical
  rcases
    osiiAxisPair_weightedTotalLogSemigroupBranch_single_local_polydisc_real_edge_selector_bound
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ hξ0 with
    ⟨ρ, C, hρ, hC, hdiff, hreal, hselector, hbound⟩
  refine ⟨ρ, C, hρ, hC, ?_, ?_, ?_, ?_⟩
  · let L : (Fin (d + 1) → ℂ) → Fin (d + 1) → ℂ :=
      osiiAxisPairTimeShellPerturbationC (d := d) ξ
    have hLdiff : DifferentiableOn ℂ L
        {τ : Fin (d + 1) → ℂ | ∀ ν : Fin (d + 1), ‖L τ ν‖ < ρ} := by
      have hLglobal : Differentiable ℂ L := by
        rw [differentiable_pi]
        intro ν
        refine Fin.cases ?_ ?_ ν
        · simp [L, osiiAxisPairTimeShellPerturbationC]
          fun_prop
        · intro j
          simp [L, osiiAxisPairTimeShellPerturbationC]
          fun_prop
      exact hLglobal.differentiableOn
    exact hdiff.comp hLdiff (fun τ hτ => hτ)
  · intro τ hτ
    have hrealζ :=
      hreal (osiiAxisPairTimeShellPerturbation (d := d) ξ τ) hτ
    simpa [osiiAxisPairWeightedTimeShellBranch,
      osiiAxisPairTimeShellPerturbationC_ofReal,
      osiiAxisPairTimeShellPerturbation_time (d := d) ξ τ] using hrealζ
  · intro τ hτ
    rcases hselector (osiiAxisPairTimeShellPerturbation (d := d) ξ τ) hτ with
      ⟨htime, hlim⟩
    refine ⟨by
      simpa [osiiAxisPairTimeShellPerturbation_time (d := d) ξ τ] using htime,
      ?_⟩
    have htarget :
        OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (τ 0) g))) =
          osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single r g hg_ord) T
            (fun a : osiiAxisPairIndex d =>
              Complex.log
                (osiiAxisPairCoeffMap T ξ
                  (fun ν : Fin (d + 1) =>
                    (osiiAxisPairTimeShellPerturbation (d := d) ξ τ ν : ℂ)) a)) := by
      simpa [osiiAxisPairTimeShellPerturbation_time (d := d) ξ τ] using
        (hreal (osiiAxisPairTimeShellPerturbation (d := d) ξ τ) hτ).symm
    simpa [osiiAxisPairTimeShellPerturbation_time (d := d) ξ τ, htarget] using hlim
  · intro τ hτ
    exact hbound (osiiAxisPairTimeShellPerturbation (d := d) ξ τ) hτ

/-- Compact finite packet for the corrected time-shell axis-pair windows.

For a compact strict-positive time-shell support, the correct Lemma 5.1 centers
are `(2τ⁰, τ^space)`.  This theorem finite-subcovers the support by the
time-shell windows from those centers while retaining the actual branch packet
and one finite bound over the selected windows. -/
theorem osiiAxisPair_weightedTotalLogSemigroupBranch_single_compact_timeShell_packet
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (K : Set (Fin (d + 1) → ℝ))
    (hK : IsCompact K)
    (hK_pos : K ⊆ {τ : Fin (d + 1) → ℝ | 0 < τ 0}) :
    ∃ (s : Finset K) (ρ C : K → ℝ) (Ctot : ℝ),
      0 ≤ Ctot ∧
      (∀ c : K,
        0 < ρ c ∧ 0 ≤ C c ∧
        DifferentiableOn ℂ
          (fun τ : Fin (d + 1) → ℂ =>
            osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single r g hg_ord) T
              (fun a : osiiAxisPairIndex d =>
                Complex.log
                  (osiiAxisPairCoeffMap T
                    (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
                    (osiiAxisPairTimeShellPerturbationC (d := d)
                      (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
                      τ) a)))
            {τ : Fin (d + 1) → ℂ |
              ∀ ν : Fin (d + 1),
                ‖osiiAxisPairTimeShellPerturbationC (d := d)
                  (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
                  τ ν‖ < ρ c} ∧
          (∀ τ : Fin (d + 1) → ℝ,
            τ ∈ osiiAxisPairTimeShellWindow (d := d)
                (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
                (ρ c) →
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                f hf_ord g hg_ord T
                (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
                (fun ν : Fin (d + 1) => (τ ν : ℂ)) =
                OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
                  (f.osConjTensorProduct
                    (timeShiftSchwartzNPoint (d := d) (τ 0) g)))) ∧
          (∀ τ : Fin (d + 1) → ℝ,
            τ ∈ osiiAxisPairTimeShellWindow (d := d)
                (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
              (ρ c) →
            ∃ htime : 0 < τ 0,
              Filter.Tendsto
                (fun η : ℝ =>
                  ∫ x : ℝ,
                    OSInnerProductTimeShiftHolomorphicValueExpandBoth
                        (d := d) OS lgc
                        (PositiveTimeBorchersSequence.single n f hf_ord)
                        (PositiveTimeBorchersSequence.single r g hg_ord)
                        (-Complex.I * ((x : ℂ) + η * Complex.I)) *
                      (SchwartzMap.fourierTransformCLM ℂ
                        (SCV.schwartzPsiZ
                          (((2 * Real.pi : ℂ) *
                            (((τ 0 : ℝ) : ℂ) * Complex.I)))
                          (by
                            simpa [Complex.mul_im, htime.ne']
                              using mul_pos Real.two_pi_pos htime))) x)
                (𝓝[Set.Ioi 0] (0 : ℝ))
                (𝓝
                  (osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
                    (PositiveTimeBorchersSequence.single n f hf_ord)
                    (PositiveTimeBorchersSequence.single r g hg_ord) T
                    (fun a : osiiAxisPairIndex d =>
                      Complex.log
                        (osiiAxisPairCoeffMap T
                          (osiiAxisPairTimeShellCenter (d := d)
                            (c : Fin (d + 1) → ℝ))
                          (fun ν : Fin (d + 1) =>
                            (osiiAxisPairTimeShellPerturbation
                              (d := d)
                              (osiiAxisPairTimeShellCenter (d := d)
                                (c : Fin (d + 1) → ℝ))
                              τ ν : ℂ)) a))))) ∧
        (∀ τ : Fin (d + 1) → ℝ,
          osiiAxisPairTimeShellPerturbation (d := d)
              (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
              τ ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) (ρ c) →
            ‖osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single r g hg_ord) T
              (fun a : osiiAxisPairIndex d =>
                Complex.log
                  (osiiAxisPairCoeffMap T
                    (osiiAxisPairTimeShellCenter (d := d)
                      (c : Fin (d + 1) → ℝ))
                    (fun ν : Fin (d + 1) =>
                      (osiiAxisPairTimeShellPerturbation
                        (d := d)
                        (osiiAxisPairTimeShellCenter (d := d)
                          (c : Fin (d + 1) → ℝ))
                        τ ν : ℂ)) a))‖ ≤ C c)) ∧
      (∀ c ∈ s, C c ≤ Ctot) ∧
      (∀ τ : K, ∃ c ∈ s,
        (τ : Fin (d + 1) → ℝ) ∈ osiiAxisPairTimeShellWindow (d := d)
          (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
          (ρ c)) := by
  classical
  have hlocal :
      ∀ c : K, ∃ ρ C : ℝ,
        0 < ρ ∧ 0 ≤ C ∧
        DifferentiableOn ℂ
          (fun τ : Fin (d + 1) → ℂ =>
            osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single r g hg_ord) T
              (fun a : osiiAxisPairIndex d =>
                Complex.log
                  (osiiAxisPairCoeffMap T
                    (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
                    (osiiAxisPairTimeShellPerturbationC (d := d)
                      (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
                      τ) a)))
            {τ : Fin (d + 1) → ℂ |
              ∀ ν : Fin (d + 1),
                ‖osiiAxisPairTimeShellPerturbationC (d := d)
                  (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
                  τ ν‖ < ρ} ∧
          (∀ τ : Fin (d + 1) → ℝ,
            τ ∈ osiiAxisPairTimeShellWindow (d := d)
                (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
                ρ →
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                f hf_ord g hg_ord T
                (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
                (fun ν : Fin (d + 1) => (τ ν : ℂ)) =
                OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
                  (f.osConjTensorProduct
                    (timeShiftSchwartzNPoint (d := d) (τ 0) g)))) ∧
          (∀ τ : Fin (d + 1) → ℝ,
            τ ∈ osiiAxisPairTimeShellWindow (d := d)
                (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
              ρ →
            ∃ htime : 0 < τ 0,
              Filter.Tendsto
                (fun η : ℝ =>
                  ∫ x : ℝ,
                    OSInnerProductTimeShiftHolomorphicValueExpandBoth
                        (d := d) OS lgc
                        (PositiveTimeBorchersSequence.single n f hf_ord)
                        (PositiveTimeBorchersSequence.single r g hg_ord)
                        (-Complex.I * ((x : ℂ) + η * Complex.I)) *
                      (SchwartzMap.fourierTransformCLM ℂ
                        (SCV.schwartzPsiZ
                          (((2 * Real.pi : ℂ) *
                            (((τ 0 : ℝ) : ℂ) * Complex.I)))
                          (by
                            simpa [Complex.mul_im, htime.ne']
                              using mul_pos Real.two_pi_pos htime))) x)
                (𝓝[Set.Ioi 0] (0 : ℝ))
                (𝓝
                  (osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
                    (PositiveTimeBorchersSequence.single n f hf_ord)
                    (PositiveTimeBorchersSequence.single r g hg_ord) T
                    (fun a : osiiAxisPairIndex d =>
                      Complex.log
                        (osiiAxisPairCoeffMap T
                          (osiiAxisPairTimeShellCenter (d := d)
                            (c : Fin (d + 1) → ℝ))
                          (fun ν : Fin (d + 1) =>
                            (osiiAxisPairTimeShellPerturbation
                              (d := d)
                              (osiiAxisPairTimeShellCenter (d := d)
                                (c : Fin (d + 1) → ℝ))
                              τ ν : ℂ)) a))))) ∧
        (∀ τ : Fin (d + 1) → ℝ,
          osiiAxisPairTimeShellPerturbation (d := d)
              (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
              τ ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) ρ →
            ‖osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single r g hg_ord) T
              (fun a : osiiAxisPairIndex d =>
                Complex.log
                  (osiiAxisPairCoeffMap T
                    (osiiAxisPairTimeShellCenter (d := d)
                      (c : Fin (d + 1) → ℝ))
                    (fun ν : Fin (d + 1) =>
                      (osiiAxisPairTimeShellPerturbation
                        (d := d)
                        (osiiAxisPairTimeShellCenter (d := d)
                          (c : Fin (d + 1) → ℝ))
                        τ ν : ℂ)) a))‖ ≤ C) := by
    intro c
    exact
      osiiAxisPair_weightedTotalLogSemigroupBranch_single_timeShell_local_packet
        (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT
        (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
        (osiiAxisPairTimeShellCenter_time_pos (d := d) (hK_pos c.2))
  choose ρ C hpacket using hlocal
  have hρ : ∀ c : K, 0 < ρ c := fun c => (hpacket c).1
  have hcover : K ⊆ ⋃ c : K,
      osiiAxisPairTimeShellWindow (d := d)
        (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
        (ρ c) := by
    intro τ hτ
    refine Set.mem_iUnion.mpr ⟨⟨τ, hτ⟩, ?_⟩
    intro ν
    rw [osiiAxisPairTimeShellPerturbation_center_self]
    simpa using hρ ⟨τ, hτ⟩
  obtain ⟨s, hscover⟩ :=
    hK.elim_finite_subcover
      (fun c : K =>
        osiiAxisPairTimeShellWindow (d := d)
          (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
          (ρ c))
      (fun c => isOpen_osiiAxisPairTimeShellWindow (d := d)
        (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ)))
      hcover
  let Ctot : ℝ := s.sum C
  have hCtot_nonneg : 0 ≤ Ctot := by
    exact Finset.sum_nonneg fun c _hc => (hpacket c).2.1
  have hC_le : ∀ c ∈ s, C c ≤ Ctot := by
    intro c hc
    exact Finset.single_le_sum (fun x _hx => (hpacket x).2.1) hc
  have hfinite_cover :
      ∀ τ : K, ∃ c ∈ s,
        (τ : Fin (d + 1) → ℝ) ∈ osiiAxisPairTimeShellWindow (d := d)
          (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
          (ρ c) := by
    intro τ
    have hmem : (τ : Fin (d + 1) → ℝ) ∈ ⋃ c ∈ s,
        osiiAxisPairTimeShellWindow (d := d)
          (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
          (ρ c) := hscover τ.2
    rcases Set.mem_iUnion.mp hmem with ⟨c, hc_mem⟩
    rcases Set.mem_iUnion.mp hc_mem with ⟨hcs, hτwin⟩
    exact ⟨c, hcs, hτwin⟩
  exact ⟨s, ρ, C, Ctot, hCtot_nonneg, hpacket, hC_le, hfinite_cover⟩

/-- Finite shrinking of selected time-shell windows to satisfy every pairwise
real-edge overlap constraint.

The compact packet supplies one local selector radius per selected center.  MZ
gluing also needs every pair of selected branches to be inside the radii from
the real-edge identity theorem.  This theorem performs the finite shrink once
and records pairwise real-edge equality on the resulting selected windows. -/
theorem osiiAxisPair_timeShell_selected_windows_shrink_pairwise_real_edge_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (K : Set (Fin (d + 1) → ℝ))
    (hK_pos : K ⊆ {τ : Fin (d + 1) → ℝ | 0 < τ 0})
    (s : Finset K) (hs : s.Nonempty)
    (ρ : K → ℝ)
    (hρ : ∀ c ∈ s, 0 < ρ c) :
    ∃ ρ' : K → ℝ,
      (∀ c ∈ s, 0 < ρ' c ∧ ρ' c ≤ ρ c) ∧
      ∀ c ∈ s, ∀ e ∈ s, ∀ τ : Fin (d + 1) → ℝ,
        τ ∈ osiiAxisPairTimeShellWindow (d := d)
          (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
          (ρ' c) →
        τ ∈ osiiAxisPairTimeShellWindow (d := d)
          (osiiAxisPairTimeShellCenter (d := d) (e : Fin (d + 1) → ℝ))
          (ρ' e) →
          osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
              f hf_ord g hg_ord T
              (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
              (fun ν : Fin (d + 1) => (τ ν : ℂ)) =
            osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
              f hf_ord g hg_ord T
              (osiiAxisPairTimeShellCenter (d := d) (e : Fin (d + 1) → ℝ))
              (fun ν : Fin (d + 1) => (τ ν : ℂ)) := by
  classical
  have hoverlap :
      ∀ c e : K, ∃ R₁ R₂ : ℝ, 0 < R₁ ∧ 0 < R₂ ∧
        ∀ τ : Fin (d + 1) → ℝ,
          (∀ ν : Fin (d + 1),
            ‖(osiiAxisPairTimeShellPerturbation (d := d)
              (osiiAxisPairTimeShellCenter (d := d)
                (c : Fin (d + 1) → ℝ)) τ ν : ℂ)‖ < R₁) →
          (∀ ν : Fin (d + 1),
            ‖(osiiAxisPairTimeShellPerturbation (d := d)
              (osiiAxisPairTimeShellCenter (d := d)
                (e : Fin (d + 1) → ℝ)) τ ν : ℂ)‖ < R₂) →
            osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                f hf_ord g hg_ord T
                (osiiAxisPairTimeShellCenter (d := d)
                  (c : Fin (d + 1) → ℝ))
                (fun ν : Fin (d + 1) => (τ ν : ℂ)) =
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                f hf_ord g hg_ord T
                (osiiAxisPairTimeShellCenter (d := d)
                  (e : Fin (d + 1) → ℝ))
                (fun ν : Fin (d + 1) => (τ ν : ℂ)) := by
    intro c e
    rcases
      osiiAxisPairWeightedTotalLogSemigroupBranch_single_timeShell_local_real_edge_eq
        (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT
        (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
        (osiiAxisPairTimeShellCenter (d := d) (e : Fin (d + 1) → ℝ))
        (osiiAxisPairTimeShellCenter_time_pos (d := d) (hK_pos c.2))
        (osiiAxisPairTimeShellCenter_time_pos (d := d) (hK_pos e.2)) with
      ⟨R₁, R₂, hR₁, hR₂, heq⟩
    refine ⟨R₁, R₂, hR₁, hR₂, ?_⟩
    intro τ hτc hτe
    simpa [osiiAxisPairWeightedTimeShellBranch,
      osiiAxisPairTimeShellPerturbationC_ofReal]
      using heq τ hτc hτe
  choose R₁ R₂ hR using hoverlap
  let lower : K → K → ℝ := fun c e => min (R₁ c e) (R₂ e c)
  let ρ' : K → ℝ := fun c => min (ρ c) (s.inf' hs (lower c))
  have hρ'_pos_le : ∀ c ∈ s, 0 < ρ' c ∧ ρ' c ≤ ρ c := by
    intro c hc
    have hlower_pos : 0 < s.inf' hs (lower c) := by
      rw [Finset.lt_inf'_iff hs]
      intro e he
      exact lt_min (hR c e).1 ((hR e c).2.1)
    exact ⟨lt_min (hρ c hc) hlower_pos, min_le_left _ _⟩
  refine ⟨ρ', hρ'_pos_le, ?_⟩
  intro c hc e he τ hτc hτe
  have hρ'c_le_R₁ : ρ' c ≤ R₁ c e := by
    have hle_inf : s.inf' hs (lower c) ≤ lower c e :=
      Finset.inf'_le (s := s) (f := lower c) he
    have hle_lower : lower c e ≤ R₁ c e := min_le_left _ _
    exact (min_le_right (ρ c) (s.inf' hs (lower c))).trans (hle_inf.trans hle_lower)
  have hρ'e_le_R₂ : ρ' e ≤ R₂ c e := by
    have hle_inf : s.inf' hs (lower e) ≤ lower e c :=
      Finset.inf'_le (s := s) (f := lower e) hc
    have hle_lower : lower e c ≤ R₂ c e := min_le_right _ _
    exact (min_le_right (ρ e) (s.inf' hs (lower e))).trans (hle_inf.trans hle_lower)
  have hτc_small :
      ∀ ν : Fin (d + 1),
        ‖(osiiAxisPairTimeShellPerturbation (d := d)
          (osiiAxisPairTimeShellCenter (d := d)
            (c : Fin (d + 1) → ℝ)) τ ν : ℂ)‖ < R₁ c e := by
    intro ν
    exact lt_of_lt_of_le (hτc ν) hρ'c_le_R₁
  have hτe_small :
      ∀ ν : Fin (d + 1),
        ‖(osiiAxisPairTimeShellPerturbation (d := d)
          (osiiAxisPairTimeShellCenter (d := d)
            (e : Fin (d + 1) → ℝ)) τ ν : ℂ)‖ < R₂ c e := by
    intro ν
    exact lt_of_lt_of_le (hτe ν) hρ'e_le_R₂
  exact (hR c e).2.2 τ hτc_small hτe_small

/-- Convexity of the corrected complex time-shell windows.

These are coordinate polydiscs after an affine real-linear change of variables,
so their nonempty overlaps are connected.  This is the geometric side of the
Malgrange-Zerner overlap step. -/
theorem convex_osiiAxisPairTimeShellComplexWindow
    (ξ : Fin (d + 1) → ℝ) (ρ : ℝ) :
    Convex ℝ (osiiAxisPairTimeShellComplexWindow (d := d) ξ ρ) := by
  intro z hz w hw a b ha hb hab
  intro ν
  have hlin :
      osiiAxisPairTimeShellPerturbationC (d := d) ξ (a • z + b • w) ν =
        a • osiiAxisPairTimeShellPerturbationC (d := d) ξ z ν +
          b • osiiAxisPairTimeShellPerturbationC (d := d) ξ w ν := by
    refine Fin.cases ?_ ?_ ν
    · simp [osiiAxisPairTimeShellPerturbationC, Pi.add_apply, Pi.smul_apply,
        sub_eq_add_neg, add_left_comm, add_assoc]
      have habc : (a : ℂ) + (b : ℂ) = 1 := by
        exact_mod_cast hab
      calc
        -(↑(ξ 0) / 2) = -(((a : ℂ) + (b : ℂ)) * (↑(ξ 0) / 2)) := by
          rw [habc, one_mul]
        _ = -(↑a * (↑(ξ 0) / 2)) + -(↑b * (↑(ξ 0) / 2)) := by
          ring
    · intro j
      simp [osiiAxisPairTimeShellPerturbationC, Pi.add_apply, Pi.smul_apply,
        sub_eq_add_neg, add_left_comm, add_assoc]
      have habc : (a : ℂ) + (b : ℂ) = 1 := by
        exact_mod_cast hab
      calc
        -↑(ξ j.succ) = -(((a : ℂ) + (b : ℂ)) * ↑(ξ j.succ)) := by
          rw [habc, one_mul]
        _ = -(↑a * ↑(ξ j.succ)) + -(↑b * ↑(ξ j.succ)) := by
          ring
  rw [hlin]
  have hp :
      osiiAxisPairTimeShellPerturbationC (d := d) ξ z ν ∈
        Metric.ball (0 : ℂ) ρ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz ν
  have hq :
      osiiAxisPairTimeShellPerturbationC (d := d) ξ w ν ∈
        Metric.ball (0 : ℂ) ρ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw ν
  have hcomb := (convex_ball (0 : ℂ) ρ) hp hq ha hb hab
  simpa [Metric.mem_ball, dist_eq_norm] using hcomb

/-- MZ overlap equality for the selected corrected time-shell axis-pair
branches.

The previous theorem gives equality on the real shell slice after finite
shrinking.  Convexity gives connected complex overlaps, and the coordinatewise
real-part lemma supplies a real seed in every nonempty overlap.  The
totally-real identity theorem then upgrades real-edge agreement to equality of
the holomorphic MZ branches on the whole complex overlap. -/
theorem osiiAxisPair_timeShell_selected_windows_shrink_pairwise_mz_eqOn
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (K : Set (Fin (d + 1) → ℝ))
    (hK_pos : K ⊆ {τ : Fin (d + 1) → ℝ | 0 < τ 0})
    (s : Finset K) (hs : s.Nonempty)
    (ρ : K → ℝ)
    (hρ : ∀ c ∈ s, 0 < ρ c)
    (hdiff : ∀ c ∈ s,
      DifferentiableOn ℂ
        (osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
          f hf_ord g hg_ord T
          (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ)))
        (osiiAxisPairTimeShellComplexWindow (d := d)
          (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
          (ρ c))) :
    ∃ ρ' : K → ℝ,
      (∀ c ∈ s, 0 < ρ' c ∧ ρ' c ≤ ρ c) ∧
      ∀ c ∈ s, ∀ e ∈ s,
        Set.EqOn
          (osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
            f hf_ord g hg_ord T
            (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ)))
          (osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
            f hf_ord g hg_ord T
            (osiiAxisPairTimeShellCenter (d := d) (e : Fin (d + 1) → ℝ)))
          (osiiAxisPairTimeShellComplexWindow (d := d)
              (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
              (ρ' c) ∩
            osiiAxisPairTimeShellComplexWindow (d := d)
              (osiiAxisPairTimeShellCenter (d := d) (e : Fin (d + 1) → ℝ))
              (ρ' e)) := by
  classical
  rcases
    osiiAxisPair_timeShell_selected_windows_shrink_pairwise_real_edge_eq
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT K hK_pos s hs ρ hρ with
    ⟨ρ', hρ'_pos_le, hreal_edge⟩
  refine ⟨ρ', hρ'_pos_le, ?_⟩
  intro c hc e he
  let U : Set (Fin (d + 1) → ℂ) :=
    osiiAxisPairTimeShellComplexWindow (d := d)
        (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
        (ρ' c) ∩
      osiiAxisPairTimeShellComplexWindow (d := d)
        (osiiAxisPairTimeShellCenter (d := d) (e : Fin (d + 1) → ℝ))
        (ρ' e)
  intro z hz
  have hU_open : IsOpen U := by
    exact
      (isOpen_osiiAxisPairTimeShellComplexWindow (d := d)
        (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))).inter
      (isOpen_osiiAxisPairTimeShellComplexWindow (d := d)
        (osiiAxisPairTimeShellCenter (d := d) (e : Fin (d + 1) → ℝ)))
  have hU_conn : IsConnected U := by
    exact ⟨⟨z, hz⟩,
      ((convex_osiiAxisPairTimeShellComplexWindow (d := d)
          (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
          (ρ' c)).inter
        (convex_osiiAxisPairTimeShellComplexWindow (d := d)
          (osiiAxisPairTimeShellCenter (d := d) (e : Fin (d + 1) → ℝ))
          (ρ' e))).isPreconnected⟩
  have hsub_c : U ⊆
      osiiAxisPairTimeShellComplexWindow (d := d)
        (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
        (ρ c) := by
    intro τ hτ ν
    exact lt_of_lt_of_le (hτ.1 ν) (hρ'_pos_le c hc).2
  have hsub_e : U ⊆
      osiiAxisPairTimeShellComplexWindow (d := d)
        (osiiAxisPairTimeShellCenter (d := d) (e : Fin (d + 1) → ℝ))
        (ρ e) := by
    intro τ hτ ν
    exact lt_of_lt_of_le (hτ.2 ν) (hρ'_pos_le e he).2
  have hD_c :
      DifferentiableOn ℂ
        (osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
          f hf_ord g hg_ord T
          (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))) U :=
    (hdiff c hc).mono hsub_c
  have hD_e :
      DifferentiableOn ℂ
        (osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
          f hf_ord g hg_ord T
          (osiiAxisPairTimeShellCenter (d := d) (e : Fin (d + 1) → ℝ))) U :=
    (hdiff e he).mono hsub_e
  have hseed :
      ∃ x₀ : Fin (d + 1) → ℝ, SCV.realToComplex x₀ ∈ U :=
    osiiAxisPairTimeShellComplexWindow_inter_realPart_nonempty (d := d) hz
  rcases hseed with ⟨x₀, hx₀⟩
  have hreal :
      ∀ x : Fin (d + 1) → ℝ, SCV.realToComplex x ∈ U →
        osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
            f hf_ord g hg_ord T
            (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
            (SCV.realToComplex x) =
          osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
            f hf_ord g hg_ord T
            (osiiAxisPairTimeShellCenter (d := d) (e : Fin (d + 1) → ℝ))
            (SCV.realToComplex x) := by
    intro x hx
    have hx_c : x ∈
        osiiAxisPairTimeShellWindow (d := d)
          (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
          (ρ' c) := by
      intro ν
      have hν := hx.1 ν
      change
        ‖osiiAxisPairTimeShellPerturbationC (d := d)
          (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
          (fun μ : Fin (d + 1) => (x μ : ℂ)) ν‖ < ρ' c at hν
      rw [osiiAxisPairTimeShellPerturbationC_ofReal] at hν
      simpa [osiiAxisPairTimeShellWindow] using hν
    have hx_e : x ∈
        osiiAxisPairTimeShellWindow (d := d)
          (osiiAxisPairTimeShellCenter (d := d) (e : Fin (d + 1) → ℝ))
          (ρ' e) := by
      intro ν
      have hν := hx.2 ν
      change
        ‖osiiAxisPairTimeShellPerturbationC (d := d)
          (osiiAxisPairTimeShellCenter (d := d) (e : Fin (d + 1) → ℝ))
          (fun μ : Fin (d + 1) => (x μ : ℂ)) ν‖ < ρ' e at hν
      rw [osiiAxisPairTimeShellPerturbationC_ofReal] at hν
      simpa [osiiAxisPairTimeShellWindow] using hν
    simpa [SCV.realToComplex] using hreal_edge c hc e he x hx_c hx_e
  exact
    (osii_mz_overlap_eqOn_of_real_slice_agreement
      hU_open hU_conn
      (osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
        f hf_ord g hg_ord T
        (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ)))
      (osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
        f hf_ord g hg_ord T
        (osiiAxisPairTimeShellCenter (d := d) (e : Fin (d + 1) → ℝ)))
      hD_c hD_e hx₀ hreal) (x := z) hz

/-- MZ overlap equality for selected corrected time-shell branches without
shrinking the covering windows.

Each selected branch is already Schwinger-normalized on the real part of its
own carrier.  Therefore two branches agree at every real point of a complex
overlap by comparison with the same time-shifted Schwinger value.  Convexity of
the carriers and the totally-real identity theorem then give equality on the
whole complex overlap. -/
theorem osiiAxisPair_timeShell_pairwise_mz_eqOn_of_real_edge
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (T : ℝ)
    (K : Set (Fin (d + 1) → ℝ))
    (s : Finset K)
    (ρ : K → ℝ)
    (hdiff : ∀ c ∈ s,
      DifferentiableOn ℂ
        (osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
          f hf_ord g hg_ord T
          (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ)))
        (osiiAxisPairTimeShellComplexWindow (d := d)
          (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
          (ρ c)))
    (hreal : ∀ c ∈ s, ∀ τ : Fin (d + 1) → ℝ,
      τ ∈ osiiAxisPairTimeShellWindow (d := d)
        (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
        (ρ c) →
      osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
          f hf_ord g hg_ord T
          (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
          (fun ν : Fin (d + 1) => (τ ν : ℂ)) =
        OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (τ 0) g)))) :
    ∀ c ∈ s, ∀ e ∈ s,
      Set.EqOn
        (osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
          f hf_ord g hg_ord T
          (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ)))
        (osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
          f hf_ord g hg_ord T
          (osiiAxisPairTimeShellCenter (d := d) (e : Fin (d + 1) → ℝ)))
        (osiiAxisPairTimeShellComplexWindow (d := d)
            (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
            (ρ c) ∩
          osiiAxisPairTimeShellComplexWindow (d := d)
            (osiiAxisPairTimeShellCenter (d := d) (e : Fin (d + 1) → ℝ))
            (ρ e)) := by
  classical
  intro c hc e he
  let U : Set (Fin (d + 1) → ℂ) :=
    osiiAxisPairTimeShellComplexWindow (d := d)
        (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
        (ρ c) ∩
      osiiAxisPairTimeShellComplexWindow (d := d)
        (osiiAxisPairTimeShellCenter (d := d) (e : Fin (d + 1) → ℝ))
        (ρ e)
  intro z hz
  have hU_open : IsOpen U := by
    exact
      (isOpen_osiiAxisPairTimeShellComplexWindow (d := d)
        (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))).inter
      (isOpen_osiiAxisPairTimeShellComplexWindow (d := d)
        (osiiAxisPairTimeShellCenter (d := d) (e : Fin (d + 1) → ℝ)))
  have hU_conn : IsConnected U := by
    exact ⟨⟨z, hz⟩,
      ((convex_osiiAxisPairTimeShellComplexWindow (d := d)
          (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
          (ρ c)).inter
        (convex_osiiAxisPairTimeShellComplexWindow (d := d)
          (osiiAxisPairTimeShellCenter (d := d) (e : Fin (d + 1) → ℝ))
          (ρ e))).isPreconnected⟩
  have hD_c :
      DifferentiableOn ℂ
        (osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
          f hf_ord g hg_ord T
          (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))) U :=
    (hdiff c hc).mono Set.inter_subset_left
  have hD_e :
      DifferentiableOn ℂ
        (osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
          f hf_ord g hg_ord T
          (osiiAxisPairTimeShellCenter (d := d) (e : Fin (d + 1) → ℝ))) U :=
    (hdiff e he).mono Set.inter_subset_right
  have hseed :
      ∃ x₀ : Fin (d + 1) → ℝ, SCV.realToComplex x₀ ∈ U :=
    osiiAxisPairTimeShellComplexWindow_inter_realPart_nonempty (d := d) hz
  rcases hseed with ⟨x₀, hx₀⟩
  have hreal_overlap :
      ∀ x : Fin (d + 1) → ℝ, SCV.realToComplex x ∈ U →
        osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
            f hf_ord g hg_ord T
            (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
            (SCV.realToComplex x) =
          osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
            f hf_ord g hg_ord T
            (osiiAxisPairTimeShellCenter (d := d) (e : Fin (d + 1) → ℝ))
            (SCV.realToComplex x) := by
    intro x hx
    have hx_c : x ∈
        osiiAxisPairTimeShellWindow (d := d)
          (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
          (ρ c) := by
      intro ν
      have hν := hx.1 ν
      change
        ‖osiiAxisPairTimeShellPerturbationC (d := d)
          (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
          (fun μ : Fin (d + 1) => (x μ : ℂ)) ν‖ < ρ c at hν
      rw [osiiAxisPairTimeShellPerturbationC_ofReal] at hν
      simpa [osiiAxisPairTimeShellWindow] using hν
    have hx_e : x ∈
        osiiAxisPairTimeShellWindow (d := d)
          (osiiAxisPairTimeShellCenter (d := d) (e : Fin (d + 1) → ℝ))
          (ρ e) := by
      intro ν
      have hν := hx.2 ν
      change
        ‖osiiAxisPairTimeShellPerturbationC (d := d)
          (osiiAxisPairTimeShellCenter (d := d) (e : Fin (d + 1) → ℝ))
          (fun μ : Fin (d + 1) => (x μ : ℂ)) ν‖ < ρ e at hν
      rw [osiiAxisPairTimeShellPerturbationC_ofReal] at hν
      simpa [osiiAxisPairTimeShellWindow] using hν
    calc
      osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
          f hf_ord g hg_ord T
          (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
          (SCV.realToComplex x)
          = OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
              (f.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) (x 0) g))) := by
            simpa [SCV.realToComplex] using hreal c hc x hx_c
      _ = osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
          f hf_ord g hg_ord T
          (osiiAxisPairTimeShellCenter (d := d) (e : Fin (d + 1) → ℝ))
          (SCV.realToComplex x) := by
            simpa [SCV.realToComplex] using (hreal e he x hx_e).symm
  exact
    (osii_mz_overlap_eqOn_of_real_slice_agreement
      hU_open hU_conn
      (osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
        f hf_ord g hg_ord T
        (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ)))
      (osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
        f hf_ord g hg_ord T
        (osiiAxisPairTimeShellCenter (d := d) (e : Fin (d + 1) → ℝ)))
      hD_c hD_e hx₀ hreal_overlap) (x := z) hz

/-- Compact selected finite-cover packet for the corrected axis-pair
time-shell MZ branches.

This promotes the compact time-shell selector packet to the MZ gluing datum
needed downstream: selected holomorphic branches, real Schwinger edge
normalization on their real carriers, real support coverage, complex support
coverage, and pairwise equality on complex overlaps. -/
theorem osiiAxisPair_weightedTotalLogSemigroupBranch_single_compact_timeShell_mz_cover
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (K : Set (Fin (d + 1) → ℝ))
    (hK : IsCompact K)
    (hK_pos : K ⊆ {τ : Fin (d + 1) → ℝ | 0 < τ 0}) :
    ∃ (s : Finset K) (ρ : K → ℝ),
      (∀ c ∈ s,
        0 < ρ c ∧
          DifferentiableOn ℂ
            (osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
              f hf_ord g hg_ord T
              (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ)))
            (osiiAxisPairTimeShellComplexWindow (d := d)
              (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
              (ρ c)) ∧
          (∀ τ : Fin (d + 1) → ℝ,
            τ ∈ osiiAxisPairTimeShellWindow (d := d)
              (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
              (ρ c) →
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                f hf_ord g hg_ord T
                (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
                (fun ν : Fin (d + 1) => (τ ν : ℂ)) =
                OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
                  (f.osConjTensorProduct
                    (timeShiftSchwartzNPoint (d := d) (τ 0) g))))) ∧
      (∀ τ : K, ∃ c ∈ s,
        (τ : Fin (d + 1) → ℝ) ∈ osiiAxisPairTimeShellWindow (d := d)
          (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
          (ρ c)) ∧
      (∀ τ : K, ∃ c ∈ s,
        SCV.realToComplex (τ : Fin (d + 1) → ℝ) ∈
          osiiAxisPairTimeShellComplexWindow (d := d)
            (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
            (ρ c)) ∧
      ∀ c ∈ s, ∀ e ∈ s,
        Set.EqOn
          (osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
            f hf_ord g hg_ord T
            (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ)))
          (osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
            f hf_ord g hg_ord T
            (osiiAxisPairTimeShellCenter (d := d) (e : Fin (d + 1) → ℝ)))
          (osiiAxisPairTimeShellComplexWindow (d := d)
              (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
              (ρ c) ∩
            osiiAxisPairTimeShellComplexWindow (d := d)
              (osiiAxisPairTimeShellCenter (d := d) (e : Fin (d + 1) → ℝ))
              (ρ e)) := by
  classical
  rcases
    osiiAxisPair_weightedTotalLogSemigroupBranch_single_compact_timeShell_packet
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT K hK hK_pos with
    ⟨s, ρ, C, Ctot, _hCtot, hpacket, _hC_le, hcover⟩
  have hselected :
      ∀ c ∈ s,
        0 < ρ c ∧
          DifferentiableOn ℂ
            (osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
              f hf_ord g hg_ord T
              (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ)))
            (osiiAxisPairTimeShellComplexWindow (d := d)
              (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
              (ρ c)) ∧
          (∀ τ : Fin (d + 1) → ℝ,
            τ ∈ osiiAxisPairTimeShellWindow (d := d)
              (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
              (ρ c) →
              osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                f hf_ord g hg_ord T
                (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
                (fun ν : Fin (d + 1) => (τ ν : ℂ)) =
                OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
                  (f.osConjTensorProduct
                    (timeShiftSchwartzNPoint (d := d) (τ 0) g)))) := by
    intro c hc
    rcases hpacket c with
      ⟨hρc, _hCc, hdiffc, hrealc, _hselectorc, _hboundc⟩
    refine ⟨hρc, ?_, hrealc⟩
    simpa [osiiAxisPairWeightedTimeShellBranch] using hdiffc
  have hcomplex_cover :
      ∀ τ : K, ∃ c ∈ s,
        SCV.realToComplex (τ : Fin (d + 1) → ℝ) ∈
          osiiAxisPairTimeShellComplexWindow (d := d)
            (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
            (ρ c) := by
    intro τ
    rcases hcover τ with ⟨c, hc, hτwin⟩
    refine ⟨c, hc, ?_⟩
    intro ν
    change
      ‖osiiAxisPairTimeShellPerturbationC (d := d)
        (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
        (fun μ : Fin (d + 1) => ((τ : Fin (d + 1) → ℝ) μ : ℂ)) ν‖ < ρ c
    rw [osiiAxisPairTimeShellPerturbationC_ofReal]
    exact hτwin ν
  have hEq :
      ∀ c ∈ s, ∀ e ∈ s,
        Set.EqOn
          (osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
            f hf_ord g hg_ord T
            (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ)))
          (osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
            f hf_ord g hg_ord T
            (osiiAxisPairTimeShellCenter (d := d) (e : Fin (d + 1) → ℝ)))
          (osiiAxisPairTimeShellComplexWindow (d := d)
              (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
              (ρ c) ∩
            osiiAxisPairTimeShellComplexWindow (d := d)
              (osiiAxisPairTimeShellCenter (d := d) (e : Fin (d + 1) → ℝ))
              (ρ e)) :=
    osiiAxisPair_timeShell_pairwise_mz_eqOn_of_real_edge
      (d := d) OS lgc f hf_ord g hg_ord T K s ρ
      (fun c hc => (hselected c hc).2.1)
      (fun c hc τ hτ => (hselected c hc).2.2 τ hτ)
  exact ⟨s, ρ, hselected, hcover, hcomplex_cover, hEq⟩

/-- Compact glued time-shell representative for the corrected axis-pair MZ
family.

The finite cover and pairwise MZ overlap equality assemble to one holomorphic
scalar on a complex neighborhood of the selected compact real support.  On the
real support it is exactly the Schwinger shifted-shell value. -/
theorem osiiAxisPair_weightedTotalLogSemigroupBranch_single_compact_timeShell_glued_schwinger_edge
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (K : Set (Fin (d + 1) → ℝ))
    (hK : IsCompact K)
    (hK_pos : K ⊆ {τ : Fin (d + 1) → ℝ | 0 < τ 0}) :
    ∃ (U : Set (Fin (d + 1) → ℂ))
      (S_time : (Fin (d + 1) → ℂ) → ℂ),
      IsOpen U ∧
        DifferentiableOn ℂ S_time U ∧
        (∀ τ : K, SCV.realToComplex (τ : Fin (d + 1) → ℝ) ∈ U) ∧
        (∀ τ : K,
          S_time (SCV.realToComplex (τ : Fin (d + 1) → ℝ)) =
            OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
              (f.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) ((τ : Fin (d + 1) → ℝ) 0) g)))) := by
  classical
  rcases
    osiiAxisPair_weightedTotalLogSemigroupBranch_single_compact_timeShell_mz_cover
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT K hK hK_pos with
    ⟨s, ρ, hselected, _hreal_cover, hcomplex_cover, hEq⟩
  let I := {c : K // c ∈ s}
  let N : I → Set (Fin (d + 1) → ℂ) := fun c =>
    osiiAxisPairTimeShellComplexWindow (d := d)
      (osiiAxisPairTimeShellCenter (d := d) (c.1 : Fin (d + 1) → ℝ))
      (ρ c.1)
  let D : I → (Fin (d + 1) → ℂ) → ℂ := fun c =>
    osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
      f hf_ord g hg_ord T
      (osiiAxisPairTimeShellCenter (d := d) (c.1 : Fin (d + 1) → ℝ))
  let U : Set (Fin (d + 1) → ℂ) := ⋃ c : I, N c
  let S_time : (Fin (d + 1) → ℂ) → ℂ := SCV.glued_iUnion N D
  have hN_open : ∀ c : I, IsOpen (N c) := by
    intro c
    exact
      isOpen_osiiAxisPairTimeShellComplexWindow (d := d)
        (osiiAxisPairTimeShellCenter (d := d) (c.1 : Fin (d + 1) → ℝ))
  have hD : ∀ c : I, DifferentiableOn ℂ (D c) (N c) := by
    intro c
    exact (hselected c.1 c.2).2.1
  have hEqI : ∀ c e : I, Set.EqOn (D c) (D e) (N c ∩ N e) := by
    intro c e
    exact hEq c.1 c.2 e.1 e.2
  have hU_open : IsOpen U := by
    simpa [U, N] using isOpen_iUnion hN_open
  have hU_cover : U ⊆ ⋃ c : I, N c := by
    intro z hz
    simpa [U] using hz
  have hdiff :
      DifferentiableOn ℂ S_time U := by
    simpa [S_time] using
      SCV.differentiableOn_glued_iUnion
        (U := U) (N := N) (D := D) hU_cover hN_open hD hEqI
  have hcoverU :
      ∀ τ : K, SCV.realToComplex (τ : Fin (d + 1) → ℝ) ∈ U := by
    intro τ
    rcases hcomplex_cover τ with ⟨c, hc, hτc⟩
    exact Set.mem_iUnion.2 ⟨⟨c, hc⟩, by simpa [N] using hτc⟩
  have hedge :
      ∀ τ : K,
        S_time (SCV.realToComplex (τ : Fin (d + 1) → ℝ)) =
          OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) ((τ : Fin (d + 1) → ℝ) 0) g))) := by
    intro τ
    rcases hcomplex_cover τ with ⟨c, hc, hτc_complex⟩
    have hτc_real :
        (τ : Fin (d + 1) → ℝ) ∈
          osiiAxisPairTimeShellWindow (d := d)
            (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
            (ρ c) := by
      intro ν
      have hν := hτc_complex ν
      change
        ‖osiiAxisPairTimeShellPerturbationC (d := d)
          (osiiAxisPairTimeShellCenter (d := d) (c : Fin (d + 1) → ℝ))
          (fun μ : Fin (d + 1) => ((τ : Fin (d + 1) → ℝ) μ : ℂ)) ν‖ < ρ c at hν
      rw [osiiAxisPairTimeShellPerturbationC_ofReal] at hν
      simpa [osiiAxisPairTimeShellWindow] using hν
    calc
      S_time (SCV.realToComplex (τ : Fin (d + 1) → ℝ)) =
          D ⟨c, hc⟩ (SCV.realToComplex (τ : Fin (d + 1) → ℝ)) := by
            exact
              SCV.glued_iUnion_eqOn (N := N) (D := D) hEqI ⟨c, hc⟩
                (by simpa [N] using hτc_complex)
      _ =
          OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) ((τ : Fin (d + 1) → ℝ) 0) g))) := by
            simpa [D, SCV.realToComplex] using
              (hselected c hc).2.2 (τ : Fin (d + 1) → ℝ) hτc_real
  exact ⟨U, S_time, hU_open, hdiff, hcoverU, hedge⟩

/-- Real time-shell form of the compact glued MZ representative.

This is the real-side input shape needed by the OS II `(A0)->(P0)`
delta-smearing bridge: a continuous scalar on an open real neighborhood of the
compact support, equal there to the shifted Schwinger shell. -/
theorem osiiAxisPair_weightedTotalLogSemigroupBranch_single_compact_timeShell_real_representative
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (K : Set (Fin (d + 1) → ℝ))
    (hK : IsCompact K)
    (hK_pos : K ⊆ {τ : Fin (d + 1) → ℝ | 0 < τ 0}) :
    ∃ (Ureal : Set (Fin (d + 1) → ℝ))
      (S_real : (Fin (d + 1) → ℝ) → ℂ),
      IsOpen Ureal ∧
        K ⊆ Ureal ∧
        ContinuousOn S_real Ureal ∧
        (∀ τ ∈ K,
          S_real τ =
            OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
              (f.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) (τ 0) g)))) := by
  classical
  rcases
    osiiAxisPair_weightedTotalLogSemigroupBranch_single_compact_timeShell_glued_schwinger_edge
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT K hK hK_pos with
    ⟨U, S_time, hU_open, hdiff, hcoverU, hedge⟩
  let Ureal : Set (Fin (d + 1) → ℝ) := {τ | SCV.realToComplex τ ∈ U}
  let S_real : (Fin (d + 1) → ℝ) → ℂ := fun τ => S_time (SCV.realToComplex τ)
  have hreal_cont : Continuous (SCV.realToComplex (m := d + 1)) := by
    exact continuous_pi fun ν =>
      by simpa [SCV.realToComplex] using
        (Complex.continuous_ofReal.comp (continuous_apply ν))
  have hUreal_open : IsOpen Ureal := by
    simpa [Ureal] using hU_open.preimage hreal_cont
  have hK_sub : K ⊆ Ureal := by
    intro τ hτ
    exact hcoverU ⟨τ, hτ⟩
  have hS_cont : ContinuousOn S_real Ureal := by
    exact hdiff.continuousOn.comp hreal_cont.continuousOn (fun τ hτ => hτ)
  have hedge_real :
      ∀ τ ∈ K,
        S_real τ =
          OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) (τ 0) g))) := by
    intro τ hτ
    simpa [S_real] using hedge ⟨τ, hτ⟩
  exact ⟨Ureal, S_real, hUreal_open, hK_sub, hS_cont, hedge_real⟩

/-- Compact-source pairing form of the glued real time-shell representative.

If a Schwartz test is supported in the compact real carrier, the glued
representative pairs with it exactly as the shifted Schwinger shell does. -/
theorem osiiAxisPair_weightedTotalLogSemigroupBranch_single_compact_timeShell_real_representative_pairing
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (K : Set (Fin (d + 1) → ℝ))
    (hK : IsCompact K)
    (hK_pos : K ⊆ {τ : Fin (d + 1) → ℝ | 0 < τ 0}) :
    ∃ (Ureal : Set (Fin (d + 1) → ℝ))
      (S_real : (Fin (d + 1) → ℝ) → ℂ),
      IsOpen Ureal ∧
        K ⊆ Ureal ∧
        ContinuousOn S_real Ureal ∧
        (∀ τ ∈ K,
          S_real τ =
            OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
              (f.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) (τ 0) g)))) ∧
        (∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
          tsupport (φ : (Fin (d + 1) → ℝ) → ℂ) ⊆ K →
            (∫ τ : Fin (d + 1) → ℝ, S_real τ * φ τ) =
              ∫ τ : Fin (d + 1) → ℝ,
                OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
                  (f.osConjTensorProduct
                    (timeShiftSchwartzNPoint (d := d) (τ 0) g))) * φ τ) := by
  classical
  rcases
    osiiAxisPair_weightedTotalLogSemigroupBranch_single_compact_timeShell_real_representative
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT K hK hK_pos with
    ⟨Ureal, S_real, hUreal_open, hK_sub, hS_cont, hedge⟩
  refine ⟨Ureal, S_real, hUreal_open, hK_sub, hS_cont, hedge, ?_⟩
  intro φ hφK
  apply integral_congr_ae
  filter_upwards with τ
  by_cases hτ : τ ∈ tsupport (φ : (Fin (d + 1) → ℝ) → ℂ)
  · rw [hedge τ (hφK hτ)]
  · have hzero : φ τ = 0 := image_eq_zero_of_notMem_tsupport hτ
    simp [hzero]

/-- Compact real-slice finite packet for the weighted axis-pair MZ branch.

This is the finite-cover form of the Lemma 5.1/MZ local selector packet over a
compact real support lying in the positive time half-space.  It records, for a
finite family of centers, the actual branch-selector packet and a single finite
real-slice bound on the selected centers. -/
theorem osiiAxisPair_weightedTotalLogSemigroupBranch_single_compact_realSlice_packet
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (K : Set (Fin (d + 1) → ℝ))
    (hK : IsCompact K)
    (hK_pos : K ⊆ {ξ : Fin (d + 1) → ℝ | 0 < ξ 0}) :
    ∃ (s : Finset K) (ρ C : K → ℝ) (Ctot : ℝ),
      0 ≤ Ctot ∧
      (∀ c : K,
        0 < ρ c ∧ 0 ≤ C c ∧
        DifferentiableOn ℂ
          (fun ζ : Fin (d + 1) → ℂ =>
            osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single r g hg_ord) T
              (fun a : osiiAxisPairIndex d =>
                Complex.log (osiiAxisPairCoeffMap T (c : Fin (d + 1) → ℝ) ζ a)))
          {ζ : Fin (d + 1) → ℂ | ∀ ν : Fin (d + 1), ‖ζ ν‖ < ρ c} ∧
        (∀ ζ : Fin (d + 1) → ℝ,
          (∀ ν : Fin (d + 1), ‖(ζ ν : ℂ)‖ < ρ c) →
            ∃ htime : 0 < (c : Fin (d + 1) → ℝ) 0 / 2 + ζ 0,
              Filter.Tendsto
                (fun η : ℝ =>
                  ∫ x : ℝ,
                    OSInnerProductTimeShiftHolomorphicValueExpandBoth
                        (d := d) OS lgc
                        (PositiveTimeBorchersSequence.single n f hf_ord)
                        (PositiveTimeBorchersSequence.single r g hg_ord)
                        (-Complex.I * ((x : ℂ) + η * Complex.I)) *
                      (SchwartzMap.fourierTransformCLM ℂ
                        (SCV.schwartzPsiZ
                          (((2 * Real.pi : ℂ) *
                            ((((c : Fin (d + 1) → ℝ) 0 / 2 + ζ 0 : ℝ) : ℂ) *
                              Complex.I)))
                          (by
                            simpa [Complex.mul_im, htime.ne']
                              using mul_pos Real.two_pi_pos htime))) x)
                (𝓝[Set.Ioi 0] (0 : ℝ))
                (𝓝
                  (osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
                    (PositiveTimeBorchersSequence.single n f hf_ord)
                    (PositiveTimeBorchersSequence.single r g hg_ord) T
                    (fun a : osiiAxisPairIndex d =>
                      Complex.log
                        (osiiAxisPairCoeffMap T (c : Fin (d + 1) → ℝ)
                          (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a))))) ∧
        (∀ ζ : Fin (d + 1) → ℝ,
          ζ ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) (ρ c) →
            ‖osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single r g hg_ord) T
              (fun a : osiiAxisPairIndex d =>
                Complex.log
                  (osiiAxisPairCoeffMap T (c : Fin (d + 1) → ℝ)
                    (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a))‖ ≤ C c)) ∧
      (∀ c ∈ s, C c ≤ Ctot) ∧
      (∀ ξ ∈ K, ∃ c ∈ s, ξ ∈ Metric.ball (c : Fin (d + 1) → ℝ) (ρ c)) ∧
      (∀ ξ ∈ K, ∃ c ∈ s,
        ξ ∈ Metric.ball (c : Fin (d + 1) → ℝ) (ρ c) ∧
          ‖osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single r g hg_ord) T
            (fun a : osiiAxisPairIndex d =>
              Complex.log
                (osiiAxisPairCoeffMap T (c : Fin (d + 1) → ℝ)
                  (fun ν : Fin (d + 1) => ((ξ - (c : Fin (d + 1) → ℝ)) ν : ℂ)) a))‖
            ≤ Ctot) := by
  classical
  have hlocal :
      ∀ c : K, ∃ ρ C : ℝ,
        0 < ρ ∧ 0 ≤ C ∧
        DifferentiableOn ℂ
          (fun ζ : Fin (d + 1) → ℂ =>
            osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single r g hg_ord) T
              (fun a : osiiAxisPairIndex d =>
                Complex.log (osiiAxisPairCoeffMap T (c : Fin (d + 1) → ℝ) ζ a)))
          {ζ : Fin (d + 1) → ℂ | ∀ ν : Fin (d + 1), ‖ζ ν‖ < ρ} ∧
        (∀ ζ : Fin (d + 1) → ℝ,
          (∀ ν : Fin (d + 1), ‖(ζ ν : ℂ)‖ < ρ) →
            ∃ htime : 0 < (c : Fin (d + 1) → ℝ) 0 / 2 + ζ 0,
              Filter.Tendsto
                (fun η : ℝ =>
                  ∫ x : ℝ,
                    OSInnerProductTimeShiftHolomorphicValueExpandBoth
                        (d := d) OS lgc
                        (PositiveTimeBorchersSequence.single n f hf_ord)
                        (PositiveTimeBorchersSequence.single r g hg_ord)
                        (-Complex.I * ((x : ℂ) + η * Complex.I)) *
                      (SchwartzMap.fourierTransformCLM ℂ
                        (SCV.schwartzPsiZ
                          (((2 * Real.pi : ℂ) *
                            ((((c : Fin (d + 1) → ℝ) 0 / 2 + ζ 0 : ℝ) : ℂ) *
                              Complex.I)))
                          (by
                            simpa [Complex.mul_im, htime.ne']
                              using mul_pos Real.two_pi_pos htime))) x)
                (𝓝[Set.Ioi 0] (0 : ℝ))
                (𝓝
                  (osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
                    (PositiveTimeBorchersSequence.single n f hf_ord)
                    (PositiveTimeBorchersSequence.single r g hg_ord) T
                    (fun a : osiiAxisPairIndex d =>
                      Complex.log
                        (osiiAxisPairCoeffMap T (c : Fin (d + 1) → ℝ)
                          (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a))))) ∧
        (∀ ζ : Fin (d + 1) → ℝ,
          ζ ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) ρ →
            ‖osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single r g hg_ord) T
              (fun a : osiiAxisPairIndex d =>
                Complex.log
                  (osiiAxisPairCoeffMap T (c : Fin (d + 1) → ℝ)
                    (fun ν : Fin (d + 1) => (ζ ν : ℂ)) a))‖ ≤ C) := by
    intro c
    exact
      osiiAxisPair_weightedTotalLogSemigroupBranch_single_local_polydisc_branch_selector_bound
        (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT
        (c : Fin (d + 1) → ℝ) (hK_pos c.2)
  choose ρ C hpacket using hlocal
  have hρ : ∀ c : K, 0 < ρ c := fun c => (hpacket c).1
  have hcover : K ⊆ ⋃ c : K, Metric.ball (c : Fin (d + 1) → ℝ) (ρ c) := by
    intro ξ hξ
    exact Set.mem_iUnion.mpr
      ⟨⟨ξ, hξ⟩, Metric.mem_ball_self (hρ ⟨ξ, hξ⟩)⟩
  obtain ⟨s, hscover⟩ :=
    hK.elim_finite_subcover
      (fun c : K => Metric.ball (c : Fin (d + 1) → ℝ) (ρ c))
      (fun _ => Metric.isOpen_ball) hcover
  let Ctot : ℝ := s.sum C
  have hCtot_nonneg : 0 ≤ Ctot := by
    exact Finset.sum_nonneg fun c _hc => (hpacket c).2.1
  have hC_le : ∀ c ∈ s, C c ≤ Ctot := by
    intro c hc
    exact Finset.single_le_sum (fun x _hx => (hpacket x).2.1) hc
  have hfinite_cover :
      ∀ ξ ∈ K, ∃ c ∈ s, ξ ∈ Metric.ball (c : Fin (d + 1) → ℝ) (ρ c) := by
    intro ξ hξ
    have hmem : ξ ∈ ⋃ c ∈ s, Metric.ball (c : Fin (d + 1) → ℝ) (ρ c) :=
      hscover hξ
    rcases Set.mem_iUnion.mp hmem with ⟨c, hc_mem⟩
    rcases Set.mem_iUnion.mp hc_mem with ⟨hcs, hξball⟩
    exact ⟨c, hcs, hξball⟩
  refine ⟨s, ρ, C, Ctot, hCtot_nonneg, hpacket, hC_le, hfinite_cover, ?_⟩
  intro ξ hξ
  rcases hfinite_cover ξ hξ with ⟨c, hcs, hξball⟩
  refine ⟨c, hcs, hξball, ?_⟩
  rcases hpacket c with ⟨_hρc, _hCc, _hdiff, _hselector, hbound⟩
  have hξdist : ‖ξ - (c : Fin (d + 1) → ℝ)‖ < ρ c := by
    simpa [Metric.mem_ball, dist_eq_norm] using hξball
  have hζclosed :
      ξ - (c : Fin (d + 1) → ℝ) ∈
        Metric.closedBall (0 : Fin (d + 1) → ℝ) (ρ c) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa using le_of_lt hξdist
  exact (hbound (ξ - (c : Fin (d + 1) → ℝ)) hζclosed).trans (hC_le c hcs)

/-- Real-edge value of the weighted axis-pair branch at the center of a
Lemma 5.1 coefficient chart.

This removes the auxiliary coefficient-positivity hypothesis from the centered
MZ value: positivity follows from the axis-pair coordinate estimate once the
physical time coordinate is strictly positive. -/
theorem osiiAxisPairWeightedTotalLogSemigroupBranch_single_coeffMap_center_real_edge_eq_schwinger_timeShift
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0) :
    osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single r g hg_ord) T
        (fun a : osiiAxisPairIndex d =>
          Complex.log
            (osiiAxisPairCoeffMap T ξ (fun _ν : Fin (d + 1) => (0 : ℂ)) a)) =
      OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d) (ξ 0 / 2) g))) := by
  classical
  rcases osiiAxisPair_exists_coord_radius_coeff_rightHalfPlane
      (d := d) T hT ξ hξ0 with
    ⟨ρ, hρ, hcoeff_pos_of_small⟩
  have hcoeff_pos :
      ∀ a : osiiAxisPairIndex d,
        0 < (osiiAxisPairCoeffMap T ξ
          (fun _ν : Fin (d + 1) => (0 : ℂ)) a).re := by
    exact hcoeff_pos_of_small
      (fun _ν : Fin (d + 1) => (0 : ℂ))
      (by
        intro ν
        simpa using hρ)
  have hvalue :=
    osiiAxisPairWeightedTotalLogSemigroupBranch_single_coeffMap_real_edge_eq_schwinger_timeShift
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT
      ξ (fun _ν : Fin (d + 1) => (0 : ℝ)) hcoeff_pos
  simpa using hvalue

/-- Raw OS-II generator boundary value at the center of an actual weighted
axis-pair coefficient chart.

This is the pointwise Section 4.3 kernel input at the Lemma 5.1 chart center:
the coefficient positivity required by
`tendsto_rotated_osiiAxisPairWeightedTotalLogSemigroupBranch_single_coeffMap_real`
is discharged by the axis-pair coordinate estimate itself. -/
theorem tendsto_rotated_osiiAxisPairWeightedTotalLogSemigroupBranch_single_coeffMap_center_real
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0) :
    Filter.Tendsto
      (fun η : ℝ =>
        ∫ x : ℝ,
          OSInnerProductTimeShiftHolomorphicValueExpandBoth
              (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single r g hg_ord)
              (-Complex.I * ((x : ℂ) + η * Complex.I)) *
            (SchwartzMap.fourierTransformCLM ℂ
              (SCV.schwartzPsiZ
                (((2 * Real.pi : ℂ) *
                  (((ξ 0 / 2 : ℝ) : ℂ) * Complex.I)))
                (by
                  have htime : 0 < ξ 0 / 2 := by positivity
                  simpa [Complex.mul_im, htime.ne']
                    using mul_pos Real.two_pi_pos htime))) x)
      (𝓝[Set.Ioi 0] (0 : ℝ))
      (𝓝
        (OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (ξ 0 / 2) g))))) := by
  classical
  rcases osiiAxisPair_exists_coord_radius_coeff_rightHalfPlane
      (d := d) T hT ξ hξ0 with
    ⟨ρ, hρ, hcoeff_pos_of_small⟩
  have hcoeff_pos :
      ∀ a : osiiAxisPairIndex d,
        0 < (osiiAxisPairCoeffMap T ξ
          (fun _ν : Fin (d + 1) => (0 : ℂ)) a).re := by
    exact hcoeff_pos_of_small
      (fun _ν : Fin (d + 1) => (0 : ℂ))
      (by
        intro ν
        simpa using hρ)
  have htime : 0 < ξ 0 / 2 + (0 : ℝ) := by positivity
  simpa using
    tendsto_rotated_osiiAxisPairWeightedTotalLogSemigroupBranch_single_coeffMap_real
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT
      ξ (fun _ν : Fin (d + 1) => (0 : ℝ)) hcoeff_pos htime

end OSReconstruction
