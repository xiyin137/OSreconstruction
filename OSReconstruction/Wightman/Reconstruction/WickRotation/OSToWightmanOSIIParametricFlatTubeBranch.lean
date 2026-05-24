import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIDirectionalSemigroup
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIMZFlatTubeEnvelope

/-!
# OS-II Parametric Flat-Tube Branch

This file constructs the scalar flat-tube branch before the full
Malgrange-Zerner extension.  On a one-coordinate flat log tube, the selected
coordinate is continued by the OS semigroup and the remaining coordinates are
held at their real log base.  On overlaps, the only possible ambiguity is the
real edge, where the semigroup algebra identifies all selected branches with
the same total positive-time Schwinger scalar.
-/

noncomputable section

open Complex Topology
open scoped Classical BigOperators

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Real log base associated to a complex log point. -/
def osiiRealLogBase {m : ℕ} (r : Fin m → ℂ) : Fin m → ℝ :=
  fun p => (r p).re

/-- Directional branch with the non-selected real positive-time differences
frozen at the supplied real log base. -/
def osiiMatchingBaseDirectionalLogBranch
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} (F G : PositiveTimeBorchersSequence d)
    (x : Fin m → ℝ) (q : Fin m) :
    (Fin m → ℂ) → ℂ :=
  osiiFrozenDirectionalLogBranch (d := d) OS lgc F G
    (fun p => Real.exp (x p)) (fun p => le_of_lt (Real.exp_pos (x p))) q

/-- The common Schwinger scalar on the real log edge: total positive-time shift
by `sum_p exp x_p`. -/
def osiiTotalPositiveTimeRealEdge
    (OS : OsterwalderSchraderAxioms d)
    {m : ℕ} (F G : PositiveTimeBorchersSequence d)
    (x : Fin m → ℝ) : ℂ :=
  OSInnerProduct d OS.S (F : BorchersSequence d)
    (timeShiftBorchers (d := d)
      (∑ p : Fin m, Real.exp (x p))
      (G : BorchersSequence d))

/-- At the matching real edge, a directional branch recovers the total
positive-time Schwinger scalar. -/
theorem osiiMatchingBaseDirectionalLogBranch_real_edge_eq_total
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (x : Fin m → ℝ) (q : Fin m) :
    osiiMatchingBaseDirectionalLogBranch (d := d) OS lgc F G x q
        (osiiMZLogRealEmbed x) =
      osiiTotalPositiveTimeRealEdge (d := d) OS F G x := by
  simpa [osiiMatchingBaseDirectionalLogBranch, osiiTotalPositiveTimeRealEdge] using
    osii_frozen_directional_log_branch_matching_base_real_edge_eq_total
      (d := d) OS lgc F G hG_compact x q

/-- Two selected-coordinate branches agree on a common flat-tube point.  Away
from the real edge the selected coordinate is unique; on the real edge this is
exactly the checked common-real-edge semigroup identity. -/
theorem osiiMatchingBaseDirectionalLogBranch_eq_on_flat_overlap
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    {r : Fin m → ℂ} {q q' : Fin m}
    (hrq : |(r q).im| < Real.pi / 2 ∧ ∀ p : Fin m, p ≠ q → (r p).im = 0)
    (hrq' : |(r q').im| < Real.pi / 2 ∧ ∀ p : Fin m, p ≠ q' → (r p).im = 0) :
    osiiMatchingBaseDirectionalLogBranch (d := d) OS lgc F G (osiiRealLogBase r) q r =
      osiiMatchingBaseDirectionalLogBranch (d := d) OS lgc F G (osiiRealLogBase r) q' r := by
  by_cases hqq' : q = q'
  · subst hqq'
    rfl
  · have him_zero : ∀ p : Fin m, (r p).im = 0 := by
      intro p
      by_cases hp : p = q
      · exact hrq'.2 p (by
          intro hp'
          exact hqq' (hp.symm.trans hp'))
      · exact hrq.2 p hp
    have hreal : r = osiiMZLogRealEmbed (osiiRealLogBase r) := by
      funext p
      apply Complex.ext
      · simp [osiiRealLogBase, osiiMZLogRealEmbed]
      · simp [osiiMZLogRealEmbed, him_zero p]
    rw [hreal]
    exact
      osii_parametric_directional_log_branch_real_edges_agree
        (d := d) OS lgc F G hG_compact (osiiRealLogBase r) q q'

/-- Scalar branch on the one-coordinate flat log-tube union, obtained by
choosing the active flat coordinate.  The independence theorem above proves
that this agrees with any available flat-coordinate presentation. -/
noncomputable def osiiParametricFlatTubeBranch
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    (F G : PositiveTimeBorchersSequence d)
    (r : Fin m → ℂ) : ℂ :=
  if hr : r ∈ osiiMZFlatLogTubeUnion m (Real.pi / 2) then
    osiiMatchingBaseDirectionalLogBranch (d := d) OS lgc F G (osiiRealLogBase r)
      (Classical.choose hr) r
  else
    0

/-- On any presented one-coordinate flat tube, the scalar flat-tube branch is
the corresponding matching-base directional branch. -/
theorem osiiParametricFlatTubeBranch_eq_directional_of_mem
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    {r : Fin m → ℂ} {q : Fin m}
    (hrq : |(r q).im| < Real.pi / 2 ∧ ∀ p : Fin m, p ≠ q → (r p).im = 0) :
    osiiParametricFlatTubeBranch (d := d) OS lgc F G r =
      osiiMatchingBaseDirectionalLogBranch (d := d) OS lgc F G (osiiRealLogBase r) q r := by
  have hr : r ∈ osiiMZFlatLogTubeUnion m (Real.pi / 2) := ⟨q, hrq⟩
  unfold osiiParametricFlatTubeBranch
  rw [dif_pos hr]
  exact
    osiiMatchingBaseDirectionalLogBranch_eq_on_flat_overlap
      (d := d) OS lgc F G hG_compact
      (Classical.choose_spec hr) hrq

/-- The scalar flat-tube branch has the correct common Schwinger real edge. -/
theorem osiiParametricFlatTubeBranch_real_edge_eq_total
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (x : Fin m → ℝ) :
    osiiParametricFlatTubeBranch (d := d) OS lgc F G (osiiMZLogRealEmbed x) =
      osiiTotalPositiveTimeRealEdge (d := d) OS F G x := by
  let q : Fin m := Classical.choice inferInstance
  have hrq :
      |(osiiMZLogRealEmbed x q).im| < Real.pi / 2 ∧
        ∀ p : Fin m, p ≠ q → (osiiMZLogRealEmbed x p).im = 0 := by
    constructor
    · simp [osiiMZLogRealEmbed]
      positivity
    · intro p _hp
      simp [osiiMZLogRealEmbed]
  calc
    osiiParametricFlatTubeBranch (d := d) OS lgc F G (osiiMZLogRealEmbed x)
        =
          osiiMatchingBaseDirectionalLogBranch (d := d) OS lgc F G
            (osiiRealLogBase (osiiMZLogRealEmbed x)) q
            (osiiMZLogRealEmbed x) :=
          osiiParametricFlatTubeBranch_eq_directional_of_mem
            (d := d) OS lgc F G hG_compact hrq
    _ =
          osiiMatchingBaseDirectionalLogBranch (d := d) OS lgc F G x q
            (osiiMZLogRealEmbed x) := by
          have hxbase : osiiRealLogBase (osiiMZLogRealEmbed x) = x := by
            funext p
            simp [osiiRealLogBase, osiiMZLogRealEmbed]
          rw [hxbase]
    _ =
          osiiTotalPositiveTimeRealEdge (d := d) OS F G x :=
          osiiMatchingBaseDirectionalLogBranch_real_edge_eq_total
            (d := d) OS lgc F G hG_compact x q

theorem osiiLeftTimeSum_congr_of_eq_off_selected
    {m : ℕ} {τ σ : Fin m → ℝ} {q : Fin m}
    (h : ∀ p : Fin m, p ≠ q → τ p = σ p) :
    osiiLeftTimeSum τ q = osiiLeftTimeSum σ q := by
  unfold osiiLeftTimeSum
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.val < q.val
  · have hp_ne : p ≠ q := Fin.ne_of_val_ne hp.ne
    simp [hp, h p hp_ne]
  · simp [hp]

theorem osiiRightTimeSum_congr_of_eq_off_selected
    {m : ℕ} {τ σ : Fin m → ℝ} {q : Fin m}
    (h : ∀ p : Fin m, p ≠ q → τ p = σ p) :
    osiiRightTimeSum τ q = osiiRightTimeSum σ q := by
  unfold osiiRightTimeSum
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : q.val < p.val
  · have hp_ne : p ≠ q := fun hpq => by
      have hval : q.val = p.val := congrArg Fin.val hpq.symm
      omega
    simp [hp, h p hp_ne]
  · simp [hp]

/-- The frozen directional branch only depends on the frozen positive-time
base away from the selected coordinate. -/
theorem osiiFrozenDirectionalLogBranch_congr_of_eq_off_selected
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} (F G : PositiveTimeBorchersSequence d)
    {τ σ : Fin m → ℝ} (hτ : ∀ p, 0 ≤ τ p) (hσ : ∀ p, 0 ≤ σ p)
    {q : Fin m}
    (h : ∀ p : Fin m, p ≠ q → τ p = σ p) :
    osiiFrozenDirectionalLogBranch (d := d) OS lgc F G τ hτ q =
      osiiFrozenDirectionalLogBranch (d := d) OS lgc F G σ hσ q := by
  have hleft := osiiLeftTimeSum_congr_of_eq_off_selected (τ := τ) (σ := σ) (q := q) h
  have hright := osiiRightTimeSum_congr_of_eq_off_selected (τ := τ) (σ := σ) (q := q) h
  funext r
  simp [osiiFrozenDirectionalLogBranch, osiiLeftSplitPositiveBranch,
    osiiRightSplitPositiveBranch, hleft, hright]

theorem osiiRealLogBase_update_real_edge_eq_off_selected
    {m : ℕ} (x : Fin m → ℝ) (q : Fin m) (w : ℂ) :
    ∀ p : Fin m, p ≠ q →
      Real.exp (osiiRealLogBase (Function.update (osiiMZLogRealEmbed x) q w) p) =
        Real.exp (x p) := by
  intro p hp
  simp [osiiRealLogBase, osiiMZLogRealEmbed, Function.update, hp]

/-- Along a fixed coordinate flat tube through a real base point, the
choice-independent scalar branch is the corresponding one-variable frozen
directional semigroup branch. -/
theorem osiiParametricFlatTubeBranch_coordinate_line_eq_fixed_directional
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (x : Fin m → ℝ) (q : Fin m) {w : ℂ}
    (hw : |w.im| < Real.pi / 2) :
    osiiParametricFlatTubeBranch (d := d) OS lgc F G
        (Function.update (osiiMZLogRealEmbed x) q w) =
      osiiMatchingBaseDirectionalLogBranch (d := d) OS lgc F G x q
        (Function.update (osiiMZLogRealEmbed x) q w) := by
  let r : Fin m → ℂ := Function.update (osiiMZLogRealEmbed x) q w
  have hrq : |(r q).im| < Real.pi / 2 ∧ ∀ p : Fin m, p ≠ q → (r p).im = 0 := by
    constructor
    · simpa [r, Function.update] using hw
    · intro p hp
      simp [r, osiiMZLogRealEmbed, hp]
  have hbranch :
      osiiParametricFlatTubeBranch (d := d) OS lgc F G r =
        osiiMatchingBaseDirectionalLogBranch (d := d) OS lgc F G
          (osiiRealLogBase r) q r :=
    osiiParametricFlatTubeBranch_eq_directional_of_mem
      (d := d) OS lgc F G hG_compact hrq
  have hfreeze :
      osiiMatchingBaseDirectionalLogBranch (d := d) OS lgc F G
          (osiiRealLogBase r) q =
        osiiMatchingBaseDirectionalLogBranch (d := d) OS lgc F G x q := by
    exact
      osiiFrozenDirectionalLogBranch_congr_of_eq_off_selected
        (d := d) OS lgc F G
        (fun p => le_of_lt (Real.exp_pos (osiiRealLogBase r p)))
        (fun p => le_of_lt (Real.exp_pos (x p)))
        (osiiRealLogBase_update_real_edge_eq_off_selected x q w)
  calc
    osiiParametricFlatTubeBranch (d := d) OS lgc F G
        (Function.update (osiiMZLogRealEmbed x) q w)
        = osiiParametricFlatTubeBranch (d := d) OS lgc F G r := rfl
    _ = osiiMatchingBaseDirectionalLogBranch (d := d) OS lgc F G
          (osiiRealLogBase r) q r := hbranch
    _ = osiiMatchingBaseDirectionalLogBranch (d := d) OS lgc F G x q r := by
          rw [hfreeze]
    _ = osiiMatchingBaseDirectionalLogBranch (d := d) OS lgc F G x q
          (Function.update (osiiMZLogRealEmbed x) q w) := rfl

/-- Each coordinate-line slice of the scalar flat-tube branch is holomorphic
on the OS-II strip `|Im w| < pi / 2`.  This records the actual one-variable
analytic carrier that feeds the Malgrange-Zerner/Osgood step. -/
theorem differentiableOn_osiiParametricFlatTubeBranch_coordinate_line
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (x : Fin m → ℝ) (q : Fin m) :
    DifferentiableOn ℂ
      (fun w : ℂ =>
        osiiParametricFlatTubeBranch (d := d) OS lgc F G
          (Function.update (osiiMZLogRealEmbed x) q w))
      {w : ℂ | |w.im| < Real.pi / 2} := by
  let τ : Fin m → ℝ := fun p => Real.exp (x p)
  let hτ : ∀ p, 0 ≤ τ p := fun p => le_of_lt (Real.exp_pos (x p))
  let line : ℂ → Fin m → ℂ := fun w => Function.update (osiiMZLogRealEmbed x) q w
  have hupdate_diff : Differentiable ℂ line := by
    rw [differentiable_pi]
    intro p
    by_cases hp : p = q
    · subst hp
      simp [line]
    · simp [line, hp]
  have hmaps :
      Set.MapsTo line {w : ℂ | |w.im| < Real.pi / 2} (osiiMZCoordinateLogStrip m q) := by
    intro w hw
    simpa [line, osiiMZCoordinateLogStrip, Function.update] using hw
  have hfixed :
      DifferentiableOn ℂ
        (fun w : ℂ =>
          osiiMatchingBaseDirectionalLogBranch (d := d) OS lgc F G x q
            (line w))
        {w : ℂ | |w.im| < Real.pi / 2} := by
    simpa [osiiMatchingBaseDirectionalLogBranch, τ, hτ, line] using
      (osii_frozen_directional_log_branch_differentiableOn_coordinateStrip
        (d := d) OS lgc F G τ hτ q).comp
        hupdate_diff.differentiableOn hmaps
  refine hfixed.congr ?_
  intro w hw
  simpa [line] using
    (osiiParametricFlatTubeBranch_coordinate_line_eq_fixed_directional
      (d := d) OS lgc F G hG_compact x q hw)

/-- Explicit scalar semigroup candidate on the full OS-II logarithmic carrier:
evaluate the one-variable OS semigroup representative at the total complex
positive-time difference `sum_p exp r_p`. -/
def osiiTotalLogSemigroupBranch
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} (F G : PositiveTimeBorchersSequence d) :
    (Fin m → ℂ) → ℂ :=
  fun r =>
    OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc F G
      (∑ p : Fin m, Complex.exp (r p))

theorem osiiMZLogDomain_sum_exp_mem_rightHalfPlane
    {m : ℕ} [Nonempty (Fin m)] {r : Fin m → ℂ}
    (hr : r ∈ osiiMZLogDomain m (Real.pi / 2)) :
    (∑ p : Fin m, Complex.exp (r p)) ∈ {z : ℂ | 0 < z.re} := by
  have hcoord : ∀ p : Fin m, |(r p).im| < Real.pi / 2 := by
    intro p
    exact
      osiiMZ_l1LogCarrier_subset_coordinateLogStrip
        (m := m) (alpha := Real.pi / 2) p hr
  have hpos : ∀ p : Fin m, 0 < (Complex.exp (r p)).re := by
    intro p
    exact osiiMZ_exp_apply_mem_rightHalfPlane (m := m) (q := p) (hcoord p)
  have hnonempty : (Finset.univ : Finset (Fin m)).Nonempty :=
    Finset.univ_nonempty
  simpa using Finset.sum_pos (fun p _ => hpos p) hnonempty

/-- The explicit total-time semigroup candidate is holomorphic on the full
OS-II `l1` log carrier. -/
theorem differentiableOn_osiiTotalLogSemigroupBranch_l1
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    (F G : PositiveTimeBorchersSequence d) :
    DifferentiableOn ℂ
      (osiiTotalLogSemigroupBranch (d := d) OS lgc F G)
      (osiiMZLogDomain m (Real.pi / 2)) := by
  have hsum_diff :
      DifferentiableOn ℂ
        (fun r : Fin m → ℂ => ∑ p : Fin m, Complex.exp (r p))
        (osiiMZLogDomain m (Real.pi / 2)) := by
    convert
      DifferentiableOn.sum (u := (Finset.univ : Finset (Fin m))) fun p _ =>
        (Complex.differentiable_exp.comp
          (differentiable_apply p :
            Differentiable ℂ (fun r : Fin m → ℂ => r p))).differentiableOn
      using 1
    ext r
    simp
  exact
    (differentiableOn_OSInnerProductTimeShiftHolomorphicValueExpandBoth
      (d := d) OS lgc F G).comp hsum_diff
      (fun r hr => osiiMZLogDomain_sum_exp_mem_rightHalfPlane (m := m) hr)

/-- On the real log edge, the explicit total-time semigroup candidate recovers
the common positive-time Schwinger scalar. -/
theorem osiiTotalLogSemigroupBranch_real_edge_eq_total
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (x : Fin m → ℝ) :
    osiiTotalLogSemigroupBranch (d := d) OS lgc F G (osiiMZLogRealEmbed x) =
      osiiTotalPositiveTimeRealEdge (d := d) OS F G x := by
  have hpos : 0 < ∑ p : Fin m, Real.exp (x p) := by
    have hnonempty : (Finset.univ : Finset (Fin m)).Nonempty :=
      Finset.univ_nonempty
    exact Finset.sum_pos (fun p _ => Real.exp_pos (x p)) hnonempty
  have hsum :
      (∑ p : Fin m, Complex.exp (osiiMZLogRealEmbed x p)) =
        ((∑ p : Fin m, Real.exp (x p)) : ℂ) := by
    simp [osiiMZLogRealEmbed]
  rw [osiiTotalLogSemigroupBranch, hsum]
  simpa [osiiTotalPositiveTimeRealEdge] using
    OSInnerProductTimeShiftHolomorphicValueExpandBoth_ofReal_eq_of_isCompactSupport
      (d := d) OS lgc F G hG_compact (∑ p : Fin m, Real.exp (x p)) hpos

/-- Concentrated scalarization of the total log representative on the real
log edge: the common real-edge scalar is the Schwinger functional of the
OS-conjugated simple tensor shifted by the total positive time
`sum_p exp x_p`. -/
theorem osiiTotalLogSemigroupBranch_single_real_edge_eq_schwinger_timeShift
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (x : Fin m → ℝ) :
    osiiTotalLogSemigroupBranch (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single r g hg_ord)
        (osiiMZLogRealEmbed x) =
      OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, Real.exp (x p)) g))) := by
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
    osiiTotalLogSemigroupBranch (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single r g hg_ord)
        (osiiMZLogRealEmbed x) =
      osiiTotalPositiveTimeRealEdge (d := d) OS
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single r g hg_ord) x := by
        exact
          osiiTotalLogSemigroupBranch_real_edge_eq_total
            (d := d) OS lgc
            (F := PositiveTimeBorchersSequence.single n f hf_ord)
            (G := PositiveTimeBorchersSequence.single r g hg_ord)
            hG_compact x
    _ = OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
        (f.osConjTensorProduct
          (timeShiftSchwartzNPoint (d := d)
            (∑ p : Fin m, Real.exp (x p)) g))) := by
        simpa [osiiTotalPositiveTimeRealEdge,
          PositiveTimeBorchersSequence.single_toBorchersSequence] using
          OSInnerProduct_single_right_timeShift
            (d := d) OS f g (∑ p : Fin m, Real.exp (x p))

/-- On every one-coordinate flat log tube through a real base point, the
choice-independent flat branch agrees with the explicit total-time semigroup
branch.  The proof is the OS-II semigroup split: both sides are holomorphic on
the one-variable strip and agree on its real edge. -/
theorem osiiParametricFlatTubeBranch_coordinate_line_eq_total_log
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (x : Fin m → ℝ) (q : Fin m) {w : ℂ}
    (hw : |w.im| < Real.pi / 2) :
    osiiParametricFlatTubeBranch (d := d) OS lgc F G
        (Function.update (osiiMZLogRealEmbed x) q w) =
      osiiTotalLogSemigroupBranch (d := d) OS lgc F G
        (Function.update (osiiMZLogRealEmbed x) q w) := by
  let U : Set (Fin 1 → ℂ) := osiiMZLogDomain 1 (Real.pi / 2)
  let τ : Fin m → ℝ := fun p => Real.exp (x p)
  let hτ : ∀ p, 0 ≤ τ p := fun p => le_of_lt (Real.exp_pos (x p))
  let line : (Fin 1 → ℂ) → Fin m → ℂ :=
    fun ζ => Function.update (osiiMZLogRealEmbed x) q (ζ 0)
  let Fline : (Fin 1 → ℂ) → ℂ := fun ζ =>
    osiiMatchingBaseDirectionalLogBranch (d := d) OS lgc F G x q (line ζ)
  let Gline : (Fin 1 → ℂ) → ℂ := fun ζ =>
    osiiTotalLogSemigroupBranch (d := d) OS lgc F G (line ζ)
  have hline_diff : Differentiable ℂ line := by
    rw [differentiable_pi]
    intro p
    by_cases hp : p = q
    · subst hp
      simpa [line] using
        (differentiable_apply (0 : Fin 1) :
          Differentiable ℂ (fun ζ : Fin 1 → ℂ => ζ 0))
    · simp [line, hp]
  have hstrip_of_U : ∀ ζ ∈ U, |(ζ 0).im| < Real.pi / 2 := by
    intro ζ hζ
    simpa [U, osiiMZLogDomain] using hζ
  have hline_maps_coord :
      Set.MapsTo line U (osiiMZCoordinateLogStrip m q) := by
    intro ζ hζ
    simpa [line, osiiMZCoordinateLogStrip, Function.update] using hstrip_of_U ζ hζ
  have hFdiff : DifferentiableOn ℂ Fline U := by
    simpa [Fline, osiiMatchingBaseDirectionalLogBranch, τ, hτ, line] using
      (osii_frozen_directional_log_branch_differentiableOn_coordinateStrip
        (d := d) OS lgc F G τ hτ q).comp
        hline_diff.differentiableOn hline_maps_coord
  have hline_maps_l1 :
      Set.MapsTo line U (osiiMZLogDomain m (Real.pi / 2)) := by
    intro ζ hζ
    have hsum :
        (∑ p : Fin m, |((line ζ) p).im|) = |(ζ 0).im| := by
      calc
        (∑ p : Fin m, |((line ζ) p).im|)
            = |((line ζ) q).im| := by
              refine Finset.sum_eq_single (s := (Finset.univ : Finset (Fin m)))
                (a := q) (f := fun p : Fin m => |((line ζ) p).im|) ?_ ?_
              · intro p _ hp
                simp [line, osiiMZLogRealEmbed, hp]
              · intro hq_not
                exact (hq_not (Finset.mem_univ q)).elim
        _ = |(ζ 0).im| := by
              simp [line]
    simpa [osiiMZLogDomain, hsum] using hstrip_of_U ζ hζ
  have hGdiff : DifferentiableOn ℂ Gline U := by
    simpa [Gline, line] using
      (differentiableOn_osiiTotalLogSemigroupBranch_l1
        (d := d) OS lgc F G).comp
        hline_diff.differentiableOn hline_maps_l1
  have hreal : ∀ y : Fin 1 → ℝ, SCV.realToComplex y ∈ U →
      Fline (SCV.realToComplex y) = Gline (SCV.realToComplex y) := by
    intro y _hy
    let x' : Fin m → ℝ := Function.update x q (y 0)
    have hline_real : line (SCV.realToComplex y) = osiiMZLogRealEmbed x' := by
      funext p
      by_cases hp : p = q
      · subst hp
        simp [line, x', osiiMZLogRealEmbed, SCV.realToComplex]
      · simp [line, x', osiiMZLogRealEmbed, hp]
    have hx'q : x' q = y 0 := by
      simp [x']
    have hFreal :
        Fline (SCV.realToComplex y) =
          OSInnerProduct d OS.S (F : BorchersSequence d)
            (timeShiftBorchers (d := d)
              (∑ p : Fin m, osiiFrozenTimeUpdate τ q (Real.exp (y 0)) p)
              (G : BorchersSequence d)) := by
      have hraw :=
        osii_frozen_directional_log_branch_real_edge_eq
          (d := d) OS lgc F G hG_compact τ hτ q x'
      dsimp [Fline]
      rw [hline_real]
      simpa [Fline, osiiMatchingBaseDirectionalLogBranch, τ,
        osiiFrozenSplitRealEdge, hx'q] using hraw
    have hsum :
        (∑ p : Fin m, Complex.exp (line (SCV.realToComplex y) p)) =
          ((∑ p : Fin m, osiiFrozenTimeUpdate τ q (Real.exp (y 0)) p) : ℂ) := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p = q
      · subst hp
        simp [line, SCV.realToComplex, osiiFrozenTimeUpdate, τ]
      · simp [line, osiiMZLogRealEmbed, osiiFrozenTimeUpdate, τ, hp]
    have hsum_pos :
        0 < ∑ p : Fin m, osiiFrozenTimeUpdate τ q (Real.exp (y 0)) p := by
      have hnonempty : (Finset.univ : Finset (Fin m)).Nonempty :=
        Finset.univ_nonempty
      refine Finset.sum_pos (fun p _ => ?_) hnonempty
      by_cases hp : p = q
      · subst hp
        simp [osiiFrozenTimeUpdate, τ, Real.exp_pos]
      · simp [osiiFrozenTimeUpdate, τ, hp, Real.exp_pos]
    have hGreal :
        Gline (SCV.realToComplex y) =
          OSInnerProduct d OS.S (F : BorchersSequence d)
            (timeShiftBorchers (d := d)
              (∑ p : Fin m, osiiFrozenTimeUpdate τ q (Real.exp (y 0)) p)
              (G : BorchersSequence d)) := by
      dsimp [Gline]
      rw [osiiTotalLogSemigroupBranch, hsum]
      simpa using
        OSInnerProductTimeShiftHolomorphicValueExpandBoth_ofReal_eq_of_isCompactSupport
          (d := d) OS lgc F G hG_compact
          (∑ p : Fin m, osiiFrozenTimeUpdate τ q (Real.exp (y 0)) p) hsum_pos
    exact hFreal.trans hGreal.symm
  have hzero_mem : SCV.realToComplex (0 : Fin 1 → ℝ) ∈ U := by
    simpa [U, SCV.realToComplex, osiiMZLogRealEmbed] using
      osiiMZLogRealEmbed_mem (m := 1) (α := Real.pi / 2) (by positivity)
        (0 : Fin 1 → ℝ)
  have hEqOn :
      Set.EqOn Fline Gline U := by
    intro ζ hζ
    exact
      SCV.holomorphic_eq_of_eq_on_real_of_connected
        (m := 1) (U := U)
        (isOpen_osiiMZLogDomain 1 (Real.pi / 2))
        (isConnected_osiiMZLogDomain 1 (by positivity))
        hFdiff hGdiff hzero_mem hreal ζ hζ
  let ζw : Fin 1 → ℂ := fun _ => w
  have hζw : ζw ∈ U := by
    simpa [ζw, U, osiiMZLogDomain] using hw
  have hflat :=
    osiiParametricFlatTubeBranch_coordinate_line_eq_fixed_directional
      (d := d) OS lgc F G hG_compact x q hw
  calc
    osiiParametricFlatTubeBranch (d := d) OS lgc F G
        (Function.update (osiiMZLogRealEmbed x) q w)
        =
          osiiMatchingBaseDirectionalLogBranch (d := d) OS lgc F G x q
            (Function.update (osiiMZLogRealEmbed x) q w) := hflat
    _ = Fline ζw := by
          simp [Fline, line, ζw]
    _ = Gline ζw := hEqOn hζw
    _ = osiiTotalLogSemigroupBranch (d := d) OS lgc F G
          (Function.update (osiiMZLogRealEmbed x) q w) := by
          simp [Gline, line, ζw]

end OSReconstruction
