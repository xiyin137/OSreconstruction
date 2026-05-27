import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIDirectionalSemigroup
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIMZFlatTubeEnvelope
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTimeProductDensity

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

private instance instLineSchwartzCompatibleSMul :
    LinearMap.CompatibleSMul (SchwartzMap ℝ ℂ) ℂ ℝ ℂ where
  map_smul := by
    intro f r x
    have hx : r • x = (r : ℂ) • x := by
      ext t
      simp
    rw [hx]
    simpa using f.map_smul (r : ℂ) x

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

/-- Along each positive horizontal line in the rotated upper half-plane, the
finite Borchers expansion of the OS semigroup branch has polynomial growth.
The estimate is obtained by summing the checked one-component semigroup
growth bounds over the finite left and right Borchers supports. -/
theorem hasPolynomialGrowthOnLine_rotated_OSInnerProductTimeShiftHolomorphicValueExpandBoth
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (η : ℝ) (hη : 0 < η) :
    SCV.HasPolynomialGrowthOnLine
      (fun x : ℝ =>
        OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc F G
          (-Complex.I * ((x : ℂ) + η * Complex.I))) := by
  classical
  let I : Finset ℕ := Finset.range (((F : BorchersSequence d).bound) + 1)
  let J : Finset ℕ := Finset.range (((G : BorchersSequence d).bound) + 1)
  let Cterm : ℕ → ℕ → ℝ := fun n m =>
    (hasPolynomialGrowthOnLine_rotated_OSInnerProductTimeShiftHolomorphicValue
      (d := d) OS lgc
      (PositiveTimeBorchersSequence.single n (((F : BorchersSequence d).funcs n))
        (F.ordered_tsupport n))
      (PositiveTimeBorchersSequence.single m (((G : BorchersSequence d).funcs m))
        (G.ordered_tsupport m))
      η hη).choose
  let Nterm : ℕ → ℕ → ℕ := fun n m =>
    (hasPolynomialGrowthOnLine_rotated_OSInnerProductTimeShiftHolomorphicValue
      (d := d) OS lgc
      (PositiveTimeBorchersSequence.single n (((F : BorchersSequence d).funcs n))
        (F.ordered_tsupport n))
      (PositiveTimeBorchersSequence.single m (((G : BorchersSequence d).funcs m))
        (G.ordered_tsupport m))
      η hη).choose_spec.choose
  let C : ℝ := ∑ n ∈ I, ∑ m ∈ J, Cterm n m
  let N : ℕ := ∑ n ∈ I, ∑ m ∈ J, Nterm n m
  have hCterm_pos : ∀ n ∈ I, ∀ m ∈ J, 0 < Cterm n m := by
    intro n hn m hm
    exact
      (hasPolynomialGrowthOnLine_rotated_OSInnerProductTimeShiftHolomorphicValue
        (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n (((F : BorchersSequence d).funcs n))
          (F.ordered_tsupport n))
        (PositiveTimeBorchersSequence.single m (((G : BorchersSequence d).funcs m))
          (G.ordered_tsupport m))
        η hη).choose_spec.choose_spec.1
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg fun n hn =>
      Finset.sum_nonneg fun m hm => le_of_lt (hCterm_pos n hn m hm)
  refine ⟨C + 1, N, by linarith, ?_⟩
  intro x
  have hbase_one : 1 ≤ 1 + |x| := by
    linarith [abs_nonneg x]
  have hbase_nonneg : 0 ≤ 1 + |x| := by positivity
  have hterm :
      ∀ n ∈ I, ∀ m ∈ J,
        ‖OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n (((F : BorchersSequence d).funcs n))
              (F.ordered_tsupport n))
            (PositiveTimeBorchersSequence.single m (((G : BorchersSequence d).funcs m))
              (G.ordered_tsupport m))
            (-Complex.I * ((x : ℂ) + η * Complex.I))‖ ≤ Cterm n m * (1 + |x|) ^ N := by
    intro n hn m hm
    have hgrowth :=
      (hasPolynomialGrowthOnLine_rotated_OSInnerProductTimeShiftHolomorphicValue
        (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n (((F : BorchersSequence d).funcs n))
          (F.ordered_tsupport n))
        (PositiveTimeBorchersSequence.single m (((G : BorchersSequence d).funcs m))
          (G.ordered_tsupport m))
        η hη).choose_spec.choose_spec.2
    have hN_inner :
        Nterm n m ≤ ∑ m ∈ J, Nterm n m :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hm
    have hN_outer :
        (∑ m ∈ J, Nterm n m) ≤ N :=
      Finset.single_le_sum
        (s := I) (a := n)
        (f := fun n => ∑ m ∈ J, Nterm n m)
        (fun _ _ => Nat.zero_le _) hn
    have hN_le : Nterm n m ≤ N := le_trans hN_inner hN_outer
    have hpow :
        (1 + |x|) ^ Nterm n m ≤ (1 + |x|) ^ N :=
      pow_le_pow_right₀ hbase_one hN_le
    have hC_nonneg_nm : 0 ≤ Cterm n m := le_of_lt (hCterm_pos n hn m hm)
    calc
      ‖OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n (((F : BorchersSequence d).funcs n))
            (F.ordered_tsupport n))
          (PositiveTimeBorchersSequence.single m (((G : BorchersSequence d).funcs m))
            (G.ordered_tsupport m))
          (-Complex.I * ((x : ℂ) + η * Complex.I))‖
          ≤ Cterm n m * (1 + |x|) ^ Nterm n m := by
            simpa [Cterm, Nterm] using hgrowth x
      _ ≤ Cterm n m * (1 + |x|) ^ N := by
            exact mul_le_mul_of_nonneg_left hpow hC_nonneg_nm
  have hsum_norm :
      ‖∑ n ∈ I, ∑ m ∈ J,
        OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n (((F : BorchersSequence d).funcs n))
            (F.ordered_tsupport n))
          (PositiveTimeBorchersSequence.single m (((G : BorchersSequence d).funcs m))
            (G.ordered_tsupport m))
          (-Complex.I * ((x : ℂ) + η * Complex.I))‖ ≤ C * (1 + |x|) ^ N := by
    calc
      ‖∑ n ∈ I, ∑ m ∈ J,
        OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n (((F : BorchersSequence d).funcs n))
            (F.ordered_tsupport n))
          (PositiveTimeBorchersSequence.single m (((G : BorchersSequence d).funcs m))
            (G.ordered_tsupport m))
          (-Complex.I * ((x : ℂ) + η * Complex.I))‖
          ≤ ∑ n ∈ I, ‖∑ m ∈ J,
        OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n (((F : BorchersSequence d).funcs n))
            (F.ordered_tsupport n))
          (PositiveTimeBorchersSequence.single m (((G : BorchersSequence d).funcs m))
            (G.ordered_tsupport m))
          (-Complex.I * ((x : ℂ) + η * Complex.I))‖ := by
            exact norm_sum_le _ _
      _ ≤ ∑ n ∈ I, ∑ m ∈ J, Cterm n m * (1 + |x|) ^ N := by
            exact Finset.sum_le_sum fun n hn =>
              calc
                ‖∑ m ∈ J,
                  OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                    (PositiveTimeBorchersSequence.single n
                      (((F : BorchersSequence d).funcs n))
                      (F.ordered_tsupport n))
                    (PositiveTimeBorchersSequence.single m
                      (((G : BorchersSequence d).funcs m))
                      (G.ordered_tsupport m))
                    (-Complex.I * ((x : ℂ) + η * Complex.I))‖
                    ≤ ∑ m ∈ J,
                      ‖OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                        (PositiveTimeBorchersSequence.single n
                          (((F : BorchersSequence d).funcs n))
                          (F.ordered_tsupport n))
                        (PositiveTimeBorchersSequence.single m
                          (((G : BorchersSequence d).funcs m))
                          (G.ordered_tsupport m))
                        (-Complex.I * ((x : ℂ) + η * Complex.I))‖ := by
                          exact norm_sum_le _ _
                _ ≤ ∑ m ∈ J, Cterm n m * (1 + |x|) ^ N := by
                          exact Finset.sum_le_sum fun m hm => hterm n hn m hm
      _ = C * (1 + |x|) ^ N := by
            simp [C, Finset.sum_mul]
  calc
    ‖OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc F G
        (-Complex.I * ((x : ℂ) + η * Complex.I))‖
        = ‖∑ n ∈ I, ∑ m ∈ J,
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n (((F : BorchersSequence d).funcs n))
              (F.ordered_tsupport n))
            (PositiveTimeBorchersSequence.single m (((G : BorchersSequence d).funcs m))
              (G.ordered_tsupport m))
            (-Complex.I * ((x : ℂ) + η * Complex.I))‖ := by
          simp [OSInnerProductTimeShiftHolomorphicValueExpandBoth, I, J]
    _ ≤ C * (1 + |x|) ^ N := hsum_norm
    _ ≤ (C + 1) * (1 + |x|) ^ N := by
          exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hbase_nonneg N)

/-- Integrability of the recombined finite Borchers expansion against Fourier
transforms of Schwartz tests along positive horizontal lines. -/
theorem integrable_mul_fourierTransform_of_rotated_OSInnerProductTimeShiftHolomorphicValueExpandBoth
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (χ : SchwartzMap ℝ ℂ)
    {η : ℝ} (hη : 0 < η) :
    MeasureTheory.Integrable
      (fun x : ℝ =>
        OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc F G
            (-Complex.I * ((x : ℂ) + η * Complex.I)) *
          (SchwartzMap.fourierTransformCLM ℂ χ) x) := by
  have hline_cont :
      Continuous
        (fun x : ℝ =>
          OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc F G
            (-Complex.I * ((x : ℂ) + η * Complex.I))) := by
    have hmap_cont : Continuous (fun x : ℝ => -Complex.I * ((x : ℂ) + η * Complex.I)) := by
      fun_prop
    exact
      (differentiableOn_OSInnerProductTimeShiftHolomorphicValueExpandBoth
        (d := d) OS lgc F G).continuousOn.comp_continuous hmap_cont
        (by
          intro x
          simp [Complex.mul_re, hη])
  exact SCV.integrable_mul_fourierTransform_of_continuous_polynomialGrowthOnLine
    (f := fun x : ℝ =>
      OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc F G
        (-Complex.I * ((x : ℂ) + η * Complex.I)))
    hline_cont
    (hasPolynomialGrowthOnLine_rotated_OSInnerProductTimeShiftHolomorphicValueExpandBoth
      (d := d) OS lgc F G η hη)
    χ

/-- A continuous polynomial-growth function on the real line defines a
one-variable tempered distribution.  This is the local functional-analytic
bridge used to turn the positive-height OS-II semigroup branch into the
`Tseq` family required by the Section 4.3 dense-boundary theorem. -/
private theorem exists_lineTemperedCLM_of_continuous_polynomialGrowthOnLine
    (f : ℝ → ℂ)
    (hf_cont : Continuous f)
    (hf_growth : SCV.HasPolynomialGrowthOnLine f) :
    ∃ T : SchwartzMap ℝ ℂ →L[ℂ] ℂ,
      ∀ φ : SchwartzMap ℝ ℂ, T φ = ∫ x : ℝ, f x * φ x := by
  rcases hf_growth with ⟨C_bound, N, hC_bound_pos, h_growth_bound⟩
  let M : ℕ := N + 2
  let sem : SchwartzMap ℝ ℂ → ℝ :=
    fun φ => (Finset.Iic (M, 0)).sup (schwartzSeminormFamily ℂ ℝ ℂ) φ
  have h_decay_int : MeasureTheory.Integrable
      (fun t : ℝ => (1 + ‖t‖) ^ (-(2 : ℝ))) MeasureTheory.volume := by
    have : (Module.finrank ℝ ℝ : ℝ) < (2 : ℝ) := by norm_num
    simpa using integrable_one_add_norm this
  have h_decay_int_nat : MeasureTheory.Integrable
      (fun t : ℝ => ((1 + ‖t‖) ^ 2)⁻¹) MeasureTheory.volume := by
    simpa [Real.rpow_neg (by positivity : 0 ≤ (1 + ‖(0 : ℝ)‖)),
      Real.rpow_natCast] using h_decay_int
  have hsem_bound : ∀ (φ : SchwartzMap ℝ ℂ) (t : ℝ),
      (1 + ‖t‖) ^ M * ‖φ t‖ ≤ 2 ^ M * sem φ := by
    intro φ t
    simpa [sem, M, norm_iteratedFDeriv_zero] using
      (SchwartzMap.one_add_le_sup_seminorm_apply
        (𝕜 := ℂ) (m := (M, 0)) (k := M) (n := 0)
        (le_rfl) (le_rfl) φ t)
  have h_pointwise_bound : ∀ (φ : SchwartzMap ℝ ℂ) (t : ℝ),
      ‖f t * φ t‖ ≤
        C_bound * 2 ^ M * sem φ * ((1 + ‖t‖) ^ 2)⁻¹ := by
    intro φ t
    have h_growth_t : ‖f t‖ ≤ C_bound * (1 + ‖t‖) ^ N :=
      h_growth_bound t
    have h_pow_pos : 0 < (1 + ‖t‖) ^ 2 := by positivity
    have h_decay_step :
        (1 + ‖t‖) ^ N * ‖φ t‖ ≤
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
            _ = (C_bound * 2 ^ M * I₂) *
                (Finset.Iic (M, 0)).sup (schwartzSeminormFamily ℂ ℝ ℂ) φ := by
              simp [sem, mul_assoc])
  refine ⟨T, ?_⟩
  intro φ
  rfl

/-- Positive-height regularized boundary functional for the recombined OS-II
semigroup branch.  It is the polynomial-growth line distribution at height
`η`, composed with the Fourier transform on Schwartz tests. -/
noncomputable def OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (η : ℝ) (hη : 0 < η) :
    SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
  let f : ℝ → ℂ := fun x =>
    OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc F G
      (-Complex.I * ((x : ℂ) + η * Complex.I))
  have hf_cont : Continuous f := by
    have hmap_cont : Continuous (fun x : ℝ => -Complex.I * ((x : ℂ) + η * Complex.I)) := by
      fun_prop
    exact
      (differentiableOn_OSInnerProductTimeShiftHolomorphicValueExpandBoth
        (d := d) OS lgc F G).continuousOn.comp_continuous hmap_cont
        (by
          intro x
          simp [Complex.mul_re, hη])
  have hf_growth : SCV.HasPolynomialGrowthOnLine f :=
    hasPolynomialGrowthOnLine_rotated_OSInnerProductTimeShiftHolomorphicValueExpandBoth
      (d := d) OS lgc F G η hη
  (Classical.choose
    (exists_lineTemperedCLM_of_continuous_polynomialGrowthOnLine f hf_cont hf_growth)).comp
      (SchwartzMap.fourierTransformCLM ℂ)

@[simp] theorem OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_apply
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (χ : SchwartzMap ℝ ℂ)
    {η : ℝ} (hη : 0 < η) :
    OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
        (d := d) OS lgc F G η hη χ =
      ∫ x : ℝ,
        OSInnerProductTimeShiftHolomorphicValueExpandBoth
            (d := d) OS lgc F G
            (-Complex.I * ((x : ℂ) + η * Complex.I)) *
          (SchwartzMap.fourierTransformCLM ℂ χ) x := by
  let f : ℝ → ℂ := fun x =>
    OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc F G
      (-Complex.I * ((x : ℂ) + η * Complex.I))
  have hf_cont : Continuous f := by
    have hmap_cont : Continuous (fun x : ℝ => -Complex.I * ((x : ℂ) + η * Complex.I)) := by
      fun_prop
    exact
      (differentiableOn_OSInnerProductTimeShiftHolomorphicValueExpandBoth
        (d := d) OS lgc F G).continuousOn.comp_continuous hmap_cont
        (by
          intro x
          simp [Complex.mul_re, hη])
  have hf_growth : SCV.HasPolynomialGrowthOnLine f :=
    hasPolynomialGrowthOnLine_rotated_OSInnerProductTimeShiftHolomorphicValueExpandBoth
      (d := d) OS lgc F G η hη
  change
    (Classical.choose
      (exists_lineTemperedCLM_of_continuous_polynomialGrowthOnLine f hf_cont hf_growth))
        ((SchwartzMap.fourierTransformCLM ℂ) χ) =
      ∫ x : ℝ, f x * (SchwartzMap.fourierTransformCLM ℂ χ) x
  exact
    (Classical.choose_spec
      (exists_lineTemperedCLM_of_continuous_polynomialGrowthOnLine f hf_cont hf_growth))
      ((SchwartzMap.fourierTransformCLM ℂ) χ)

/-- Moving the finite Borchers expansion through the regularized
Fourier-paired boundary integral. -/
private theorem integral_rotated_OSInnerProductTimeShiftHolomorphicValueExpandBoth_mul_fourierTransform_eq_sum
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (χ : SchwartzMap ℝ ℂ)
    {η : ℝ} (hη : 0 < η) :
    (∫ x : ℝ,
      OSInnerProductTimeShiftHolomorphicValueExpandBoth
          (d := d) OS lgc F G
          (-Complex.I * ((x : ℂ) + η * Complex.I)) *
        (SchwartzMap.fourierTransformCLM ℂ χ) x) =
      ∑ n ∈ Finset.range (((F : BorchersSequence d).bound) + 1),
        ∑ m ∈ Finset.range (((G : BorchersSequence d).bound) + 1),
          ∫ x : ℝ,
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n
                  (((F : BorchersSequence d).funcs n))
                  (F.ordered_tsupport n))
                (PositiveTimeBorchersSequence.single m
                  (((G : BorchersSequence d).funcs m))
                  (G.ordered_tsupport m))
                (-Complex.I * ((x : ℂ) + η * Complex.I)) *
              (SchwartzMap.fourierTransformCLM ℂ χ) x := by
  classical
  let I : Finset ℕ := Finset.range (((F : BorchersSequence d).bound) + 1)
  let J : Finset ℕ := Finset.range (((G : BorchersSequence d).bound) + 1)
  have hint :
      ∀ n ∈ I, ∀ m ∈ J,
        MeasureTheory.Integrable
          (fun x : ℝ =>
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n
                  (((F : BorchersSequence d).funcs n))
                  (F.ordered_tsupport n))
                (PositiveTimeBorchersSequence.single m
                  (((G : BorchersSequence d).funcs m))
                  (G.ordered_tsupport m))
                (-Complex.I * ((x : ℂ) + η * Complex.I)) *
              (SchwartzMap.fourierTransformCLM ℂ χ) x) := by
    intro n _hn m _hm
    exact
      integrable_mul_fourierTransform_of_rotated_OSInnerProductTimeShiftHolomorphicValue
        (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n
          (((F : BorchersSequence d).funcs n))
          (F.ordered_tsupport n))
        (PositiveTimeBorchersSequence.single m
          (((G : BorchersSequence d).funcs m))
          (G.ordered_tsupport m))
        χ hη
  have hinner :
      ∀ n ∈ I,
        MeasureTheory.Integrable
          (fun x : ℝ =>
            ∑ m ∈ J,
              OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                  (PositiveTimeBorchersSequence.single n
                    (((F : BorchersSequence d).funcs n))
                    (F.ordered_tsupport n))
                  (PositiveTimeBorchersSequence.single m
                    (((G : BorchersSequence d).funcs m))
                    (G.ordered_tsupport m))
                  (-Complex.I * ((x : ℂ) + η * Complex.I)) *
                (SchwartzMap.fourierTransformCLM ℂ χ) x) := by
    intro n hn
    exact MeasureTheory.integrable_finset_sum J (fun m hm => hint n hn m hm)
  calc
    (∫ x : ℝ,
        OSInnerProductTimeShiftHolomorphicValueExpandBoth
            (d := d) OS lgc F G
            (-Complex.I * ((x : ℂ) + η * Complex.I)) *
          (SchwartzMap.fourierTransformCLM ℂ χ) x)
        =
      ∫ x : ℝ,
        ∑ n ∈ I, ∑ m ∈ J,
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n
                (((F : BorchersSequence d).funcs n))
                (F.ordered_tsupport n))
              (PositiveTimeBorchersSequence.single m
                (((G : BorchersSequence d).funcs m))
                (G.ordered_tsupport m))
              (-Complex.I * ((x : ℂ) + η * Complex.I)) *
            (SchwartzMap.fourierTransformCLM ℂ χ) x := by
          congr 1
          funext x
          simp [OSInnerProductTimeShiftHolomorphicValueExpandBoth, I, J,
            Finset.sum_mul]
    _ =
      ∑ n ∈ I,
        ∫ x : ℝ,
          ∑ m ∈ J,
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n
                  (((F : BorchersSequence d).funcs n))
                  (F.ordered_tsupport n))
                (PositiveTimeBorchersSequence.single m
                  (((G : BorchersSequence d).funcs m))
                  (G.ordered_tsupport m))
                (-Complex.I * ((x : ℂ) + η * Complex.I)) *
              (SchwartzMap.fourierTransformCLM ℂ χ) x := by
          rw [MeasureTheory.integral_finset_sum I hinner]
    _ =
      ∑ n ∈ I, ∑ m ∈ J,
        ∫ x : ℝ,
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n
                (((F : BorchersSequence d).funcs n))
                (F.ordered_tsupport n))
              (PositiveTimeBorchersSequence.single m
                (((G : BorchersSequence d).funcs m))
                (G.ordered_tsupport m))
              (-Complex.I * ((x : ℂ) + η * Complex.I)) *
            (SchwartzMap.fourierTransformCLM ℂ χ) x := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [MeasureTheory.integral_finset_sum J (fun m hm => hint n hn m hm)]

/-- Finite-height Paley-kernel value of the recombined OS-II regularized CLM.

The Section 4.3 line current at height `η`, tested on the Paley kernel for a
strict positive time `t`, is exactly the recombined OS semigroup branch at the
positive shifted time `t + η`.  This is the finite-height analogue of the
boundary selector theorem and is the kernel identity needed before the
product-source side-integral conversion. -/
theorem OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_psiZ_eq
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    {t η : ℝ} (ht : 0 < t) (hη : 0 < η) :
    OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
        (d := d) OS lgc F G η hη
        (SCV.schwartzPsiZ
          (((2 * Real.pi : ℂ) * (t * Complex.I)))
          (by simpa [Complex.mul_im, ht.ne'] using
            mul_pos Real.two_pi_pos ht)) =
      OSInnerProductTimeShiftHolomorphicValueExpandBoth
        (d := d) OS lgc F G (((t + η : ℝ) : ℂ)) := by
  classical
  let χ : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by simpa [Complex.mul_im, ht.ne'] using mul_pos Real.two_pi_pos ht)
  rw [OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_apply]
  rw [integral_rotated_OSInnerProductTimeShiftHolomorphicValueExpandBoth_mul_fourierTransform_eq_sum
    (d := d) OS lgc F G χ hη]
  unfold OSInnerProductTimeShiftHolomorphicValueExpandBoth
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  let Fn : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single n (((F : BorchersSequence d).funcs n))
      (F.ordered_tsupport n)
  let Gm : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single m (((G : BorchersSequence d).funcs m))
      (G.ordered_tsupport m)
  have hpoint :
      ∀ s : ℝ,
        OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc Fn Gm
            (-Complex.I * ((s : ℂ) + η * Complex.I)) =
          ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
            (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
            (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
            (((show OSPreHilbertSpace OS from (⟦Fn⟧)) : OSHilbertSpace OS))
            (((show OSPreHilbertSpace OS from (⟦Gm⟧)) : OSHilbertSpace OS))
            (-Complex.I * ((s : ℂ) + η * Complex.I)) := by
    intro s
    exact
      OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag
        (d := d) OS lgc Fn Gm (-Complex.I * ((s : ℂ) + η * Complex.I))
        (by simp [Complex.mul_re, hη])
  calc
    (∫ s : ℝ,
        OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc Fn Gm
            (-Complex.I * ((s : ℂ) + η * Complex.I)) *
          (SchwartzMap.fourierTransformCLM ℂ χ) s)
        =
      ∫ s : ℝ,
        ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
            (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
            (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
            (((show OSPreHilbertSpace OS from (⟦Fn⟧)) : OSHilbertSpace OS))
            (((show OSPreHilbertSpace OS from (⟦Gm⟧)) : OSHilbertSpace OS))
            (-Complex.I * ((s : ℂ) + η * Complex.I)) *
          (SchwartzMap.fourierTransformCLM ℂ χ) s := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with s
            rw [hpoint s]
    _ =
      ContinuousLinearMap.selfAdjointSpectralLaplaceOffdiag
        (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
        (((show OSPreHilbertSpace OS from (⟦Fn⟧)) : OSHilbertSpace OS))
        (((show OSPreHilbertSpace OS from (⟦Gm⟧)) : OSHilbertSpace OS))
        (((t + η : ℝ) : ℂ)) := by
          simpa [χ] using
            integral_rotated_selfAdjointSpectralLaplaceOffdiag_mul_fourierTransform_psiZ
              (A := osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
              (hA := osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
              (hspec := spectrum_osTimeShiftHilbert_subset_Icc (d := d) OS lgc 1 one_pos)
              (x := (((show OSPreHilbertSpace OS from (⟦Fn⟧)) : OSHilbertSpace OS)))
              (y := (((show OSPreHilbertSpace OS from (⟦Gm⟧)) : OSHilbertSpace OS)))
              (t := t) (η := η) ht hη
    _ =
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc Fn Gm
        (((t + η : ℝ) : ℂ)) := by
          symm
          exact
            OSInnerProductTimeShiftHolomorphicValue_eq_selfAdjointSpectralLaplaceOffdiag
              (d := d) OS lgc Fn Gm (((t + η : ℝ) : ℂ))
              (by simp [add_pos ht hη])

/-- For each fixed Schwartz test, the recombined finite Borchers branch gives a
uniformly bounded family of positive-side regularized boundary pairings. -/
theorem exists_bound_integral_rotated_OSInnerProductTimeShiftHolomorphicValueExpandBoth_mul_fourierTransform
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (χ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {η : ℝ}, 0 < η →
      ‖∫ x : ℝ,
        OSInnerProductTimeShiftHolomorphicValueExpandBoth
            (d := d) OS lgc F G
            (-Complex.I * ((x : ℂ) + η * Complex.I)) *
          (SchwartzMap.fourierTransformCLM ℂ χ) x‖ ≤ C := by
  classical
  let I : Finset ℕ := Finset.range (((F : BorchersSequence d).bound) + 1)
  let J : Finset ℕ := Finset.range (((G : BorchersSequence d).bound) + 1)
  let Cterm : ℕ → ℕ → ℝ := fun n m =>
    Classical.choose
      (exists_bound_integral_rotated_OSInnerProductTimeShiftHolomorphicValue_mul_fourierTransform
        (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n
          (((F : BorchersSequence d).funcs n))
          (F.ordered_tsupport n))
        (PositiveTimeBorchersSequence.single m
          (((G : BorchersSequence d).funcs m))
          (G.ordered_tsupport m))
        χ)
  have hCterm_nonneg : ∀ n m, 0 ≤ Cterm n m := by
    intro n m
    exact
      (Classical.choose_spec
        (exists_bound_integral_rotated_OSInnerProductTimeShiftHolomorphicValue_mul_fourierTransform
          (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n
            (((F : BorchersSequence d).funcs n))
            (F.ordered_tsupport n))
          (PositiveTimeBorchersSequence.single m
            (((G : BorchersSequence d).funcs m))
            (G.ordered_tsupport m))
          χ)).1
  have hCterm_bound :
      ∀ n m, ∀ {η : ℝ}, 0 < η →
        ‖∫ x : ℝ,
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n
                (((F : BorchersSequence d).funcs n))
                (F.ordered_tsupport n))
              (PositiveTimeBorchersSequence.single m
                (((G : BorchersSequence d).funcs m))
                (G.ordered_tsupport m))
              (-Complex.I * ((x : ℂ) + η * Complex.I)) *
            (SchwartzMap.fourierTransformCLM ℂ χ) x‖ ≤ Cterm n m := by
    intro n m η hη
    exact
      (Classical.choose_spec
        (exists_bound_integral_rotated_OSInnerProductTimeShiftHolomorphicValue_mul_fourierTransform
          (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n
            (((F : BorchersSequence d).funcs n))
            (F.ordered_tsupport n))
          (PositiveTimeBorchersSequence.single m
            (((G : BorchersSequence d).funcs m))
            (G.ordered_tsupport m))
          χ)).2 hη
  refine ⟨∑ n ∈ I, ∑ m ∈ J, Cterm n m, ?_, ?_⟩
  · exact Finset.sum_nonneg fun n _hn =>
      Finset.sum_nonneg fun m _hm => hCterm_nonneg n m
  · intro η hη
    rw [
      integral_rotated_OSInnerProductTimeShiftHolomorphicValueExpandBoth_mul_fourierTransform_eq_sum
        (d := d) OS lgc F G χ hη]
    calc
      ‖∑ n ∈ I, ∑ m ∈ J,
          ∫ x : ℝ,
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n
                  (((F : BorchersSequence d).funcs n))
                  (F.ordered_tsupport n))
                (PositiveTimeBorchersSequence.single m
                  (((G : BorchersSequence d).funcs m))
                  (G.ordered_tsupport m))
                (-Complex.I * ((x : ℂ) + η * Complex.I)) *
              (SchwartzMap.fourierTransformCLM ℂ χ) x‖
          ≤ ∑ n ∈ I,
              ‖∑ m ∈ J,
                ∫ x : ℝ,
                  OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                      (PositiveTimeBorchersSequence.single n
                        (((F : BorchersSequence d).funcs n))
                        (F.ordered_tsupport n))
                      (PositiveTimeBorchersSequence.single m
                        (((G : BorchersSequence d).funcs m))
                        (G.ordered_tsupport m))
                      (-Complex.I * ((x : ℂ) + η * Complex.I)) *
                    (SchwartzMap.fourierTransformCLM ℂ χ) x‖ := by
            exact norm_sum_le _ _
      _ ≤ ∑ n ∈ I, ∑ m ∈ J,
              ‖∫ x : ℝ,
                OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                    (PositiveTimeBorchersSequence.single n
                      (((F : BorchersSequence d).funcs n))
                      (F.ordered_tsupport n))
                    (PositiveTimeBorchersSequence.single m
                      (((G : BorchersSequence d).funcs m))
                      (G.ordered_tsupport m))
                    (-Complex.I * ((x : ℂ) + η * Complex.I)) *
                  (SchwartzMap.fourierTransformCLM ℂ χ) x‖ := by
            exact Finset.sum_le_sum fun n _hn => norm_sum_le _ _
      _ ≤ ∑ n ∈ I, ∑ m ∈ J, Cterm n m := by
            exact Finset.sum_le_sum fun n _hn =>
              Finset.sum_le_sum fun m _hm => hCterm_bound n m hη

/-- Continuous-linear spectral boundary functional for the finite Borchers
expansion of the rotated OS semigroup branch. -/
noncomputable def OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) :
    SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
  ∑ n ∈ Finset.range (((F : BorchersSequence d).bound) + 1),
    ∑ m ∈ Finset.range (((G : BorchersSequence d).bound) + 1),
      selfAdjointSpectralBoundaryValueOffdiagCLM
        (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
        (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
        (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single n
            (((F : BorchersSequence d).funcs n))
            (F.ordered_tsupport n)⟧)) : OSHilbertSpace OS))
        (((show OSPreHilbertSpace OS from
          (⟦PositiveTimeBorchersSequence.single m
            (((G : BorchersSequence d).funcs m))
            (G.ordered_tsupport m)⟧)) : OSHilbertSpace OS))

@[simp] theorem OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM_apply
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (χ : SchwartzMap ℝ ℂ) :
    OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
        (d := d) OS lgc F G χ =
      ∑ n ∈ Finset.range (((F : BorchersSequence d).bound) + 1),
        ∑ m ∈ Finset.range (((G : BorchersSequence d).bound) + 1),
          selfAdjointSpectralBoundaryValueOffdiag
            (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
            (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
            (((show OSPreHilbertSpace OS from
              (⟦PositiveTimeBorchersSequence.single n
                (((F : BorchersSequence d).funcs n))
                (F.ordered_tsupport n)⟧)) : OSHilbertSpace OS))
            (((show OSPreHilbertSpace OS from
              (⟦PositiveTimeBorchersSequence.single m
                (((G : BorchersSequence d).funcs m))
                (G.ordered_tsupport m)⟧)) : OSHilbertSpace OS))
            χ := by
  simp [OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM]

/-- Pointwise boundedness of the regularized expanded branch after subtracting
its spectral boundary-value distribution. -/
theorem exists_bound_integral_rotated_OSInnerProductTimeShiftHolomorphicValueExpandBoth_boundaryDifference
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (χ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {η : ℝ}, 0 < η →
      ‖(∫ x : ℝ,
        OSInnerProductTimeShiftHolomorphicValueExpandBoth
            (d := d) OS lgc F G
            (-Complex.I * ((x : ℂ) + η * Complex.I)) *
          (SchwartzMap.fourierTransformCLM ℂ χ) x) -
        OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
          (d := d) OS lgc F G χ‖ ≤ C := by
  rcases
    exists_bound_integral_rotated_OSInnerProductTimeShiftHolomorphicValueExpandBoth_mul_fourierTransform
      (d := d) OS lgc F G χ with
    ⟨Craw, hCraw_nonneg, hCraw_bound⟩
  refine
    ⟨Craw +
      ‖OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
          (d := d) OS lgc F G χ‖, ?_, ?_⟩
  · exact add_nonneg hCraw_nonneg (norm_nonneg _)
  · intro η hη
    calc
      ‖(∫ x : ℝ,
          OSInnerProductTimeShiftHolomorphicValueExpandBoth
              (d := d) OS lgc F G
              (-Complex.I * ((x : ℂ) + η * Complex.I)) *
            (SchwartzMap.fourierTransformCLM ℂ χ) x) -
          OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
            (d := d) OS lgc F G χ‖
          ≤
            ‖∫ x : ℝ,
              OSInnerProductTimeShiftHolomorphicValueExpandBoth
                  (d := d) OS lgc F G
                  (-Complex.I * ((x : ℂ) + η * Complex.I)) *
                (SchwartzMap.fourierTransformCLM ℂ χ) x‖ +
            ‖OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
              (d := d) OS lgc F G χ‖ := by
              exact norm_sub_le _ _
      _ ≤ Craw +
            ‖OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
              (d := d) OS lgc F G χ‖ := by
            exact add_le_add (hCraw_bound hη) le_rfl

/-- Pointwise boundedness in the actual complex-linear `Tseq - T` form used by
the dense-boundary adapter. -/
theorem exists_bound_OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_boundaryDifference
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (χ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {η : ℝ}, (hη : 0 < η) →
      ‖(OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
          (d := d) OS lgc F G η hη -
        OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
          (d := d) OS lgc F G) χ‖ ≤ C := by
  rcases
    exists_bound_integral_rotated_OSInnerProductTimeShiftHolomorphicValueExpandBoth_boundaryDifference
      (d := d) OS lgc F G χ with
    ⟨C, hC_nonneg, hC_bound⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro η hη
  simpa [ContinuousLinearMap.sub_apply] using hC_bound hη

/-- Subtype-indexed form of the complex-linear pointwise boundedness, ready for
positive-height nets. -/
theorem exists_bound_OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_boundaryDifference_posSubtype
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (χ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : {η : ℝ // 0 < η},
      ‖(OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
          (d := d) OS lgc F G η.1 η.2 -
        OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
          (d := d) OS lgc F G) χ‖ ≤ C := by
  rcases
    exists_bound_OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_boundaryDifference
      (d := d) OS lgc F G χ with
    ⟨C, hC_nonneg, hC_bound⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro η
  exact hC_bound η.2

/-- Real-linear version of the subtype-indexed pointwise boundedness, matching
the scalar interface of the Section 4.3 Banach-Steinhaus adapter. -/
theorem exists_bound_OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_boundaryDifference_posSubtype_restrictScalars
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (χ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : {η : ℝ // 0 < η},
      ‖((OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
            (d := d) OS lgc F G η.1 η.2).restrictScalars ℝ -
        (OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
            (d := d) OS lgc F G).restrictScalars ℝ) χ‖ ≤ C := by
  rcases
    exists_bound_OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_boundaryDifference_posSubtype
      (d := d) OS lgc F G χ with
    ⟨C, hC_nonneg, hC_bound⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro η
  simpa [ContinuousLinearMap.sub_apply] using hC_bound η

/-- The finite Borchers spectral boundary target descends to the one-variable
positive-time quotient. -/
theorem OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM_eq_of_eqOn_nonneg
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    {χ ψ : SchwartzMap ℝ ℂ}
    (hχψ : Set.EqOn (χ : ℝ → ℂ) ψ (Set.Ici (0 : ℝ))) :
    OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
        (d := d) OS lgc F G χ =
      OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
        (d := d) OS lgc F G ψ := by
  classical
  simp [OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM,
    selfAdjointSpectralBoundaryValueOffdiagCLM_eq_of_eqOn_nonneg
      (A := osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
      (hA := osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
      (hspec := spectrum_osTimeShiftHilbert_subset_Icc (d := d) OS lgc 1 one_pos)
      (hχψ := hχψ)]

/-- The regularized positive-side family for the recombined finite Borchers
semigroup branch descends to the one-variable positive-time quotient. -/
theorem integral_rotated_OSInnerProductTimeShiftHolomorphicValueExpandBoth_mul_fourierTransform_eq_of_eqOn_nonneg
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    {χ ψ : SchwartzMap ℝ ℂ}
    {η : ℝ} (hη : 0 < η)
    (hχψ : Set.EqOn (χ : ℝ → ℂ) ψ (Set.Ici (0 : ℝ))) :
    (∫ x : ℝ,
      OSInnerProductTimeShiftHolomorphicValueExpandBoth
          (d := d) OS lgc F G
          (-Complex.I * ((x : ℂ) + η * Complex.I)) *
        (SchwartzMap.fourierTransformCLM ℂ χ) x) =
      ∫ x : ℝ,
        OSInnerProductTimeShiftHolomorphicValueExpandBoth
            (d := d) OS lgc F G
            (-Complex.I * ((x : ℂ) + η * Complex.I)) *
          (SchwartzMap.fourierTransformCLM ℂ ψ) x := by
  classical
  let I : Finset ℕ := Finset.range (((F : BorchersSequence d).bound) + 1)
  let J : Finset ℕ := Finset.range (((G : BorchersSequence d).bound) + 1)
  have hterm :
      ∀ n ∈ I, ∀ m ∈ J,
        (∫ x : ℝ,
          OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n
                (((F : BorchersSequence d).funcs n))
                (F.ordered_tsupport n))
              (PositiveTimeBorchersSequence.single m
                (((G : BorchersSequence d).funcs m))
                (G.ordered_tsupport m))
              (-Complex.I * ((x : ℂ) + η * Complex.I)) *
            (SchwartzMap.fourierTransformCLM ℂ χ) x) =
          ∫ x : ℝ,
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n
                  (((F : BorchersSequence d).funcs n))
                  (F.ordered_tsupport n))
                (PositiveTimeBorchersSequence.single m
                  (((G : BorchersSequence d).funcs m))
                  (G.ordered_tsupport m))
                (-Complex.I * ((x : ℂ) + η * Complex.I)) *
              (SchwartzMap.fourierTransformCLM ℂ ψ) x := by
    intro n _hn m _hm
    exact
      integral_rotated_OSInnerProductTimeShiftHolomorphicValue_mul_fourierTransform_eq_of_eqOn_nonneg
        (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n
          (((F : BorchersSequence d).funcs n))
          (F.ordered_tsupport n))
        (PositiveTimeBorchersSequence.single m
          (((G : BorchersSequence d).funcs m))
          (G.ordered_tsupport m))
        hη hχψ
  have hexpand :
      ∀ θ : SchwartzMap ℝ ℂ,
        (∫ x : ℝ,
          OSInnerProductTimeShiftHolomorphicValueExpandBoth
              (d := d) OS lgc F G
              (-Complex.I * ((x : ℂ) + η * Complex.I)) *
            (SchwartzMap.fourierTransformCLM ℂ θ) x) =
          ∑ n ∈ I, ∑ m ∈ J,
            ∫ x : ℝ,
              OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                  (PositiveTimeBorchersSequence.single n
                    (((F : BorchersSequence d).funcs n))
                    (F.ordered_tsupport n))
                  (PositiveTimeBorchersSequence.single m
                    (((G : BorchersSequence d).funcs m))
                    (G.ordered_tsupport m))
                  (-Complex.I * ((x : ℂ) + η * Complex.I)) *
                (SchwartzMap.fourierTransformCLM ℂ θ) x := by
    intro θ
    have hint :
        ∀ n ∈ I, ∀ m ∈ J,
          MeasureTheory.Integrable
            (fun x : ℝ =>
              OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                  (PositiveTimeBorchersSequence.single n
                    (((F : BorchersSequence d).funcs n))
                    (F.ordered_tsupport n))
                  (PositiveTimeBorchersSequence.single m
                    (((G : BorchersSequence d).funcs m))
                    (G.ordered_tsupport m))
                  (-Complex.I * ((x : ℂ) + η * Complex.I)) *
                (SchwartzMap.fourierTransformCLM ℂ θ) x) := by
      intro n _hn m _hm
      exact
        integrable_mul_fourierTransform_of_rotated_OSInnerProductTimeShiftHolomorphicValue
          (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n
            (((F : BorchersSequence d).funcs n))
            (F.ordered_tsupport n))
          (PositiveTimeBorchersSequence.single m
            (((G : BorchersSequence d).funcs m))
            (G.ordered_tsupport m))
          θ hη
    have hinner :
        ∀ n ∈ I,
          MeasureTheory.Integrable
            (fun x : ℝ =>
              ∑ m ∈ J,
                OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                    (PositiveTimeBorchersSequence.single n
                      (((F : BorchersSequence d).funcs n))
                      (F.ordered_tsupport n))
                    (PositiveTimeBorchersSequence.single m
                      (((G : BorchersSequence d).funcs m))
                      (G.ordered_tsupport m))
                    (-Complex.I * ((x : ℂ) + η * Complex.I)) *
                  (SchwartzMap.fourierTransformCLM ℂ θ) x) := by
      intro n hn
      exact MeasureTheory.integrable_finset_sum J (fun m hm => hint n hn m hm)
    calc
      (∫ x : ℝ,
          OSInnerProductTimeShiftHolomorphicValueExpandBoth
              (d := d) OS lgc F G
              (-Complex.I * ((x : ℂ) + η * Complex.I)) *
            (SchwartzMap.fourierTransformCLM ℂ θ) x)
          =
        ∫ x : ℝ,
          ∑ n ∈ I, ∑ m ∈ J,
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n
                  (((F : BorchersSequence d).funcs n))
                  (F.ordered_tsupport n))
                (PositiveTimeBorchersSequence.single m
                  (((G : BorchersSequence d).funcs m))
                  (G.ordered_tsupport m))
                (-Complex.I * ((x : ℂ) + η * Complex.I)) *
              (SchwartzMap.fourierTransformCLM ℂ θ) x := by
            congr 1
            funext x
            simp [OSInnerProductTimeShiftHolomorphicValueExpandBoth, I, J,
              Finset.sum_mul]
      _ =
        ∑ n ∈ I,
          ∫ x : ℝ,
            ∑ m ∈ J,
              OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                  (PositiveTimeBorchersSequence.single n
                    (((F : BorchersSequence d).funcs n))
                    (F.ordered_tsupport n))
                  (PositiveTimeBorchersSequence.single m
                    (((G : BorchersSequence d).funcs m))
                    (G.ordered_tsupport m))
                  (-Complex.I * ((x : ℂ) + η * Complex.I)) *
                (SchwartzMap.fourierTransformCLM ℂ θ) x := by
            rw [MeasureTheory.integral_finset_sum I hinner]
      _ =
        ∑ n ∈ I, ∑ m ∈ J,
          ∫ x : ℝ,
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n
                  (((F : BorchersSequence d).funcs n))
                  (F.ordered_tsupport n))
                (PositiveTimeBorchersSequence.single m
                  (((G : BorchersSequence d).funcs m))
                  (G.ordered_tsupport m))
                (-Complex.I * ((x : ℂ) + η * Complex.I)) *
              (SchwartzMap.fourierTransformCLM ℂ θ) x := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [MeasureTheory.integral_finset_sum J (fun m hm => hint n hn m hm)]
  rw [hexpand χ, hexpand ψ]
  exact Finset.sum_congr rfl fun n hn =>
    Finset.sum_congr rfl fun m hm => hterm n hn m hm

/-- The regularized positive-side CLM for the recombined branch descends to the
one-variable positive-time quotient. -/
theorem OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_eq_of_eqOn_nonneg
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    {χ ψ : SchwartzMap ℝ ℂ}
    {η : ℝ} (hη : 0 < η)
    (hχψ : Set.EqOn (χ : ℝ → ℂ) ψ (Set.Ici (0 : ℝ))) :
    OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
        (d := d) OS lgc F G η hη χ =
      OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
        (d := d) OS lgc F G η hη ψ := by
  simpa using
    integral_rotated_OSInnerProductTimeShiftHolomorphicValueExpandBoth_mul_fourierTransform_eq_of_eqOn_nonneg
      (d := d) OS lgc F G hη hχψ

/-- Boundary-value distribution of the recombined finite Borchers semigroup
branch.

The scalar semigroup branch is a finite Borchers expansion.  Applying the
one-component spectral boundary theorem termwise and then moving the finite sum
back inside the integral gives the boundary functional used by the compact
Laplace representative step. -/
theorem tendsto_rotated_OSInnerProductTimeShiftHolomorphicValueExpandBoth_boundaryValue_fourierTransform
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (χ : SchwartzMap ℝ ℂ) :
    Filter.Tendsto
      (fun η : ℝ =>
        ∫ x : ℝ,
          OSInnerProductTimeShiftHolomorphicValueExpandBoth
              (d := d) OS lgc F G
              (-Complex.I * ((x : ℂ) + η * Complex.I)) *
            (SchwartzMap.fourierTransformCLM ℂ χ) x)
      (𝓝[Set.Ioi 0] (0 : ℝ))
      (𝓝
        (∑ n ∈ Finset.range (((F : BorchersSequence d).bound) + 1),
          ∑ m ∈ Finset.range (((G : BorchersSequence d).bound) + 1),
            selfAdjointSpectralBoundaryValueOffdiag
              (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
              (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
              (((show OSPreHilbertSpace OS from
                (⟦PositiveTimeBorchersSequence.single n
                  (((F : BorchersSequence d).funcs n))
                  (F.ordered_tsupport n)⟧)) : OSHilbertSpace OS))
              (((show OSPreHilbertSpace OS from
                (⟦PositiveTimeBorchersSequence.single m
                  (((G : BorchersSequence d).funcs m))
                  (G.ordered_tsupport m)⟧)) : OSHilbertSpace OS))
              χ)) := by
  classical
  let I : Finset ℕ := Finset.range (((F : BorchersSequence d).bound) + 1)
  let J : Finset ℕ := Finset.range (((G : BorchersSequence d).bound) + 1)
  have hterm :
      ∀ n ∈ I, ∀ m ∈ J,
        Filter.Tendsto
          (fun η : ℝ =>
            ∫ x : ℝ,
              OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                  (PositiveTimeBorchersSequence.single n
                    (((F : BorchersSequence d).funcs n))
                    (F.ordered_tsupport n))
                  (PositiveTimeBorchersSequence.single m
                    (((G : BorchersSequence d).funcs m))
                    (G.ordered_tsupport m))
                  (-Complex.I * ((x : ℂ) + η * Complex.I)) *
                (SchwartzMap.fourierTransformCLM ℂ χ) x)
          (𝓝[Set.Ioi 0] (0 : ℝ))
          (𝓝
            (selfAdjointSpectralBoundaryValueOffdiag
              (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
              (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
              (((show OSPreHilbertSpace OS from
                (⟦PositiveTimeBorchersSequence.single n
                  (((F : BorchersSequence d).funcs n))
                  (F.ordered_tsupport n)⟧)) : OSHilbertSpace OS))
              (((show OSPreHilbertSpace OS from
                (⟦PositiveTimeBorchersSequence.single m
                  (((G : BorchersSequence d).funcs m))
                  (G.ordered_tsupport m)⟧)) : OSHilbertSpace OS))
              χ)) := by
    intro n _hn m _hm
    simpa using
      tendsto_rotated_OSInnerProductTimeShiftHolomorphicValue_boundaryValue_fourierTransform
        (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n
          (((F : BorchersSequence d).funcs n))
          (F.ordered_tsupport n))
        (PositiveTimeBorchersSequence.single m
          (((G : BorchersSequence d).funcs m))
          (G.ordered_tsupport m))
        χ
  have hsum :
      Filter.Tendsto
        (fun η : ℝ =>
          ∑ n ∈ I, ∑ m ∈ J,
            ∫ x : ℝ,
              OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                  (PositiveTimeBorchersSequence.single n
                    (((F : BorchersSequence d).funcs n))
                    (F.ordered_tsupport n))
                  (PositiveTimeBorchersSequence.single m
                    (((G : BorchersSequence d).funcs m))
                    (G.ordered_tsupport m))
                  (-Complex.I * ((x : ℂ) + η * Complex.I)) *
                (SchwartzMap.fourierTransformCLM ℂ χ) x)
        (𝓝[Set.Ioi 0] (0 : ℝ))
        (𝓝
          (∑ n ∈ I, ∑ m ∈ J,
            selfAdjointSpectralBoundaryValueOffdiag
              (osTimeShiftHilbert (d := d) OS lgc 1 one_pos)
              (osTimeShiftHilbert_isSelfAdjoint (d := d) OS lgc 1 one_pos)
              (((show OSPreHilbertSpace OS from
                (⟦PositiveTimeBorchersSequence.single n
                  (((F : BorchersSequence d).funcs n))
                  (F.ordered_tsupport n)⟧)) : OSHilbertSpace OS))
              (((show OSPreHilbertSpace OS from
                (⟦PositiveTimeBorchersSequence.single m
                  (((G : BorchersSequence d).funcs m))
                  (G.ordered_tsupport m)⟧)) : OSHilbertSpace OS))
              χ)) :=
    tendsto_finset_sum I fun n hn =>
      tendsto_finset_sum J fun m hm => hterm n hn m hm
  have hEq :
      (fun η : ℝ =>
        ∫ x : ℝ,
          OSInnerProductTimeShiftHolomorphicValueExpandBoth
              (d := d) OS lgc F G
              (-Complex.I * ((x : ℂ) + η * Complex.I)) *
            (SchwartzMap.fourierTransformCLM ℂ χ) x)
        =ᶠ[𝓝[Set.Ioi 0] (0 : ℝ)]
      (fun η : ℝ =>
        ∑ n ∈ I, ∑ m ∈ J,
          ∫ x : ℝ,
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n
                  (((F : BorchersSequence d).funcs n))
                  (F.ordered_tsupport n))
                (PositiveTimeBorchersSequence.single m
                  (((G : BorchersSequence d).funcs m))
                  (G.ordered_tsupport m))
                (-Complex.I * ((x : ℂ) + η * Complex.I)) *
              (SchwartzMap.fourierTransformCLM ℂ χ) x) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    have hη_pos : 0 < η := by simpa using hη
    have hint :
        ∀ n ∈ I, ∀ m ∈ J,
          MeasureTheory.Integrable
            (fun x : ℝ =>
              OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                  (PositiveTimeBorchersSequence.single n
                    (((F : BorchersSequence d).funcs n))
                    (F.ordered_tsupport n))
                  (PositiveTimeBorchersSequence.single m
                    (((G : BorchersSequence d).funcs m))
                    (G.ordered_tsupport m))
                  (-Complex.I * ((x : ℂ) + η * Complex.I)) *
                (SchwartzMap.fourierTransformCLM ℂ χ) x) := by
      intro n _hn m _hm
      exact
        integrable_mul_fourierTransform_of_rotated_OSInnerProductTimeShiftHolomorphicValue
          (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n
            (((F : BorchersSequence d).funcs n))
            (F.ordered_tsupport n))
          (PositiveTimeBorchersSequence.single m
            (((G : BorchersSequence d).funcs m))
            (G.ordered_tsupport m))
          χ hη_pos
    have hinner :
        ∀ n ∈ I,
          MeasureTheory.Integrable
            (fun x : ℝ =>
              ∑ m ∈ J,
                OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                    (PositiveTimeBorchersSequence.single n
                      (((F : BorchersSequence d).funcs n))
                      (F.ordered_tsupport n))
                    (PositiveTimeBorchersSequence.single m
                      (((G : BorchersSequence d).funcs m))
                      (G.ordered_tsupport m))
                    (-Complex.I * ((x : ℂ) + η * Complex.I)) *
                  (SchwartzMap.fourierTransformCLM ℂ χ) x) := by
      intro n hn
      exact MeasureTheory.integrable_finset_sum J (fun m hm => hint n hn m hm)
    calc
      (∫ x : ℝ,
          OSInnerProductTimeShiftHolomorphicValueExpandBoth
              (d := d) OS lgc F G
              (-Complex.I * ((x : ℂ) + η * Complex.I)) *
            (SchwartzMap.fourierTransformCLM ℂ χ) x)
          =
        ∫ x : ℝ,
          ∑ n ∈ I, ∑ m ∈ J,
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n
                  (((F : BorchersSequence d).funcs n))
                  (F.ordered_tsupport n))
                (PositiveTimeBorchersSequence.single m
                  (((G : BorchersSequence d).funcs m))
                  (G.ordered_tsupport m))
                (-Complex.I * ((x : ℂ) + η * Complex.I)) *
              (SchwartzMap.fourierTransformCLM ℂ χ) x := by
            congr 1
            funext x
            simp [OSInnerProductTimeShiftHolomorphicValueExpandBoth, I, J,
              Finset.sum_mul]
      _ =
        ∑ n ∈ I,
          ∫ x : ℝ,
            ∑ m ∈ J,
              OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                  (PositiveTimeBorchersSequence.single n
                    (((F : BorchersSequence d).funcs n))
                    (F.ordered_tsupport n))
                  (PositiveTimeBorchersSequence.single m
                    (((G : BorchersSequence d).funcs m))
                    (G.ordered_tsupport m))
                  (-Complex.I * ((x : ℂ) + η * Complex.I)) *
                (SchwartzMap.fourierTransformCLM ℂ χ) x := by
            rw [MeasureTheory.integral_finset_sum I hinner]
      _ =
        ∑ n ∈ I, ∑ m ∈ J,
          ∫ x : ℝ,
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n
                  (((F : BorchersSequence d).funcs n))
                  (F.ordered_tsupport n))
                (PositiveTimeBorchersSequence.single m
                  (((G : BorchersSequence d).funcs m))
                  (G.ordered_tsupport m))
                (-Complex.I * ((x : ℂ) + η * Complex.I)) *
              (SchwartzMap.fourierTransformCLM ℂ χ) x := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [MeasureTheory.integral_finset_sum J (fun m hm => hint n hn m hm)]
  simpa [I, J] using Filter.Tendsto.congr' hEq.symm hsum

/-- One-sided dense-boundary convergence for the recombined OS-II total-time
regularized CLM.

This is the Section 4.3 Banach-Steinhaus handoff for OS II `(5.7)`--`(5.8)`:
the positive-height family descends to the one-sided quotient, converges on
compact one-sided Laplace representatives by the spectral boundary theorem,
and is pointwise bounded by the semigroup estimate above. -/
theorem tendsto_OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_boundaryValue_oneSided
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) :
    ∀ χ : SchwartzMap ℝ ℂ,
      Filter.Tendsto
        (fun η : {η : ℝ // 0 < η} =>
          ((OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
              (d := d) OS lgc F G η.1 η.2).restrictScalars ℝ) χ)
        (Filter.comap (fun η : {η : ℝ // 0 < η} => η.1)
          (𝓝[Set.Ioi 0] (0 : ℝ)))
        (𝓝
          (((OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
              (d := d) OS lgc F G).restrictScalars ℝ) χ)) := by
  let lpos : Filter {η : ℝ // 0 < η} :=
    Filter.comap (fun η : {η : ℝ // 0 < η} => η.1)
      (𝓝[Set.Ioi 0] (0 : ℝ))
  have hlpos_neBot : Filter.NeBot lpos := by
    have hbase : Filter.NeBot (𝓝[Set.Ioi 0] (0 : ℝ)) := by infer_instance
    have hrange :
        Set.range (fun η : {η : ℝ // 0 < η} => η.1) ∈
          (𝓝[Set.Ioi 0] (0 : ℝ)) := by
      have hrange_eq :
          Set.range (fun η : {η : ℝ // 0 < η} => η.1) =
            Set.Ioi (0 : ℝ) := by
        ext x
        simp
      simpa [hrange_eq] using
        (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[Set.Ioi 0] (0 : ℝ))
    exact Filter.NeBot.comap_of_range_mem hbase hrange
  letI : Filter.NeBot lpos := hlpos_neBot
  refine
    section43_tendsto_oneSided_timeSchwartz_real_of_compact_representatives_of_pointwise_bounded
      (l := lpos)
      (Tseq := fun η : {η : ℝ // 0 < η} =>
        (OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
          (d := d) OS lgc F G η.1 η.2).restrictScalars ℝ)
      (T := (OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
        (d := d) OS lgc F G).restrictScalars ℝ)
      ?_ ?_ ?_ ?_
  · intro η φ ψ hq
    have hφψ := eqOn_nonneg_of_section43PositiveEnergyQuotientMap1D_eq hq
    change
      OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
          (d := d) OS lgc F G η.1 η.2 φ =
        OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
          (d := d) OS lgc F G η.1 η.2 ψ
    exact
      OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_eq_of_eqOn_nonneg
        (d := d) OS lgc F G η.2 hφψ
  · intro φ ψ hq
    have hφψ := eqOn_nonneg_of_section43PositiveEnergyQuotientMap1D_eq hq
    change
      OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
          (d := d) OS lgc F G φ =
        OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
          (d := d) OS lgc F G ψ
    exact
      OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM_eq_of_eqOn_nonneg
        (d := d) OS lgc F G hφψ
  · intro g
    have hreal :=
      tendsto_rotated_OSInnerProductTimeShiftHolomorphicValueExpandBoth_boundaryValue_fourierTransform
        (d := d) OS lgc F G (section43OneSidedLaplaceSchwartzRepresentative1D g)
    have hsub :
        Filter.Tendsto (fun η : {η : ℝ // 0 < η} => η.1)
          lpos
          (𝓝[Set.Ioi 0] (0 : ℝ)) :=
      Filter.tendsto_comap
    simpa [Function.comp_def, ContinuousLinearMap.coe_restrictScalars] using
      hreal.comp hsub
  · intro χ
    rcases
      exists_bound_OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_boundaryDifference_posSubtype_restrictScalars
        (d := d) OS lgc F G χ with
      ⟨C, _hC, hC⟩
    exact ⟨C, hC⟩

/-- Termwise semigroup boundary value for the finite expanded branch.

This is the OS-II `(5.7)` one-sided Fourier/Laplace boundary input before the
finite Borchers expansion is recombined into a single scalar branch.  The target
is the expanded semigroup value at the positive imaginary-axis generator. -/
theorem tendsto_rotated_OSInnerProductTimeShiftHolomorphicValueExpandBoth_to_imagAxis_sum
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto
      (fun η : ℝ =>
        ∑ n ∈ Finset.range (((F : BorchersSequence d).bound) + 1),
          ∑ m ∈ Finset.range (((G : BorchersSequence d).bound) + 1),
            ∫ x : ℝ,
              OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                  (PositiveTimeBorchersSequence.single n
                    (((F : BorchersSequence d).funcs n))
                    (F.ordered_tsupport n))
                  (PositiveTimeBorchersSequence.single m
                    (((G : BorchersSequence d).funcs m))
                    (G.ordered_tsupport m))
                  (-Complex.I * ((x : ℂ) + η * Complex.I)) *
                (SchwartzMap.fourierTransformCLM ℂ
                  (SCV.schwartzPsiZ
                    (((2 * Real.pi : ℂ) * (t * Complex.I)))
                    (by
                      simpa [Complex.mul_im, ht.ne']
                        using mul_pos Real.two_pi_pos ht))) x)
      (𝓝[Set.Ioi 0] (0 : ℝ))
      (𝓝 (OSInnerProductTimeShiftHolomorphicValueExpandBoth
        (d := d) OS lgc F G (t : ℂ))) := by
  classical
  let ψ : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  have hterm :
      ∀ n ∈ Finset.range (((F : BorchersSequence d).bound) + 1),
        ∀ m ∈ Finset.range (((G : BorchersSequence d).bound) + 1),
          Filter.Tendsto
            (fun η : ℝ =>
              ∫ x : ℝ,
                OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                    (PositiveTimeBorchersSequence.single n
                      (((F : BorchersSequence d).funcs n))
                      (F.ordered_tsupport n))
                    (PositiveTimeBorchersSequence.single m
                      (((G : BorchersSequence d).funcs m))
                      (G.ordered_tsupport m))
                    (-Complex.I * ((x : ℂ) + η * Complex.I)) *
                  (SchwartzMap.fourierTransformCLM ℂ ψ) x)
            (𝓝[Set.Ioi 0] (0 : ℝ))
            (𝓝 (OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n
                (((F : BorchersSequence d).funcs n))
                (F.ordered_tsupport n))
              (PositiveTimeBorchersSequence.single m
                (((G : BorchersSequence d).funcs m))
                (G.ordered_tsupport m))
              (t : ℂ))) := by
    intro n _hn m _hm
    simpa [ψ] using
      tendsto_rotated_OSInnerProductTimeShiftHolomorphicValue_to_imagAxis
        (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n
          (((F : BorchersSequence d).funcs n))
          (F.ordered_tsupport n))
        (PositiveTimeBorchersSequence.single m
          (((G : BorchersSequence d).funcs m))
          (G.ordered_tsupport m))
        ht
  simpa [OSInnerProductTimeShiftHolomorphicValueExpandBoth, ψ] using
    tendsto_finset_sum
      (Finset.range (((F : BorchersSequence d).bound) + 1))
      (fun n hn =>
        tendsto_finset_sum
          (Finset.range (((G : BorchersSequence d).bound) + 1))
          (fun m hm => hterm n hn m hm))

/-- Recombined semigroup boundary value for the finite expanded branch.

This is the same OS-II `(5.7)` generator limit as
`tendsto_rotated_OSInnerProductTimeShiftHolomorphicValueExpandBoth_to_imagAxis_sum`,
with the finite Borchers expansion put back inside the integral. -/
theorem tendsto_rotated_OSInnerProductTimeShiftHolomorphicValueExpandBoth_to_imagAxis
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto
      (fun η : ℝ =>
        ∫ x : ℝ,
          OSInnerProductTimeShiftHolomorphicValueExpandBoth
              (d := d) OS lgc F G
              (-Complex.I * ((x : ℂ) + η * Complex.I)) *
            (SchwartzMap.fourierTransformCLM ℂ
              (SCV.schwartzPsiZ
                (((2 * Real.pi : ℂ) * (t * Complex.I)))
                (by
                  simpa [Complex.mul_im, ht.ne']
                    using mul_pos Real.two_pi_pos ht))) x)
      (𝓝[Set.Ioi 0] (0 : ℝ))
      (𝓝 (OSInnerProductTimeShiftHolomorphicValueExpandBoth
        (d := d) OS lgc F G (t : ℂ))) := by
  classical
  let ψ : SchwartzMap ℝ ℂ :=
    SCV.schwartzPsiZ
      (((2 * Real.pi : ℂ) * (t * Complex.I)))
      (by
        simpa [Complex.mul_im, ht.ne']
          using mul_pos Real.two_pi_pos ht)
  have hsum :=
    tendsto_rotated_OSInnerProductTimeShiftHolomorphicValueExpandBoth_to_imagAxis_sum
      (d := d) OS lgc F G ht
  have hEq :
      (fun η : ℝ =>
        ∫ x : ℝ,
          OSInnerProductTimeShiftHolomorphicValueExpandBoth
              (d := d) OS lgc F G
              (-Complex.I * ((x : ℂ) + η * Complex.I)) *
            (SchwartzMap.fourierTransformCLM ℂ ψ) x)
        =ᶠ[𝓝[Set.Ioi 0] (0 : ℝ)]
      (fun η : ℝ =>
        ∑ n ∈ Finset.range (((F : BorchersSequence d).bound) + 1),
          ∑ m ∈ Finset.range (((G : BorchersSequence d).bound) + 1),
            ∫ x : ℝ,
              OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                  (PositiveTimeBorchersSequence.single n
                    (((F : BorchersSequence d).funcs n))
                    (F.ordered_tsupport n))
                  (PositiveTimeBorchersSequence.single m
                    (((G : BorchersSequence d).funcs m))
                    (G.ordered_tsupport m))
                  (-Complex.I * ((x : ℂ) + η * Complex.I)) *
                (SchwartzMap.fourierTransformCLM ℂ ψ) x) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    have hη_pos : 0 < η := by simpa using hη
    let I : Finset ℕ := Finset.range (((F : BorchersSequence d).bound) + 1)
    let J : Finset ℕ := Finset.range (((G : BorchersSequence d).bound) + 1)
    have hint :
        ∀ n ∈ I, ∀ m ∈ J,
          MeasureTheory.Integrable
            (fun x : ℝ =>
              OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                  (PositiveTimeBorchersSequence.single n
                    (((F : BorchersSequence d).funcs n))
                    (F.ordered_tsupport n))
                  (PositiveTimeBorchersSequence.single m
                    (((G : BorchersSequence d).funcs m))
                    (G.ordered_tsupport m))
                  (-Complex.I * ((x : ℂ) + η * Complex.I)) *
                (SchwartzMap.fourierTransformCLM ℂ ψ) x) := by
      intro n _hn m _hm
      exact
        integrable_mul_fourierTransform_of_rotated_OSInnerProductTimeShiftHolomorphicValue
          (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n
            (((F : BorchersSequence d).funcs n))
            (F.ordered_tsupport n))
          (PositiveTimeBorchersSequence.single m
            (((G : BorchersSequence d).funcs m))
            (G.ordered_tsupport m))
          ψ hη_pos
    have hinner :
        ∀ n ∈ I,
          MeasureTheory.Integrable
            (fun x : ℝ =>
              ∑ m ∈ J,
                OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                    (PositiveTimeBorchersSequence.single n
                      (((F : BorchersSequence d).funcs n))
                      (F.ordered_tsupport n))
                    (PositiveTimeBorchersSequence.single m
                      (((G : BorchersSequence d).funcs m))
                      (G.ordered_tsupport m))
                    (-Complex.I * ((x : ℂ) + η * Complex.I)) *
                  (SchwartzMap.fourierTransformCLM ℂ ψ) x) := by
      intro n hn
      exact MeasureTheory.integrable_finset_sum J (fun m hm => hint n hn m hm)
    calc
      (∫ x : ℝ,
          OSInnerProductTimeShiftHolomorphicValueExpandBoth
              (d := d) OS lgc F G
              (-Complex.I * ((x : ℂ) + η * Complex.I)) *
            (SchwartzMap.fourierTransformCLM ℂ ψ) x)
          =
        ∫ x : ℝ,
          ∑ n ∈ I, ∑ m ∈ J,
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n
                  (((F : BorchersSequence d).funcs n))
                  (F.ordered_tsupport n))
                (PositiveTimeBorchersSequence.single m
                  (((G : BorchersSequence d).funcs m))
                  (G.ordered_tsupport m))
                (-Complex.I * ((x : ℂ) + η * Complex.I)) *
              (SchwartzMap.fourierTransformCLM ℂ ψ) x := by
            congr 1
            funext x
            simp [OSInnerProductTimeShiftHolomorphicValueExpandBoth, I, J,
              Finset.sum_mul]
      _ =
        ∑ n ∈ I,
          ∫ x : ℝ,
            ∑ m ∈ J,
              OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                  (PositiveTimeBorchersSequence.single n
                    (((F : BorchersSequence d).funcs n))
                    (F.ordered_tsupport n))
                  (PositiveTimeBorchersSequence.single m
                    (((G : BorchersSequence d).funcs m))
                    (G.ordered_tsupport m))
                  (-Complex.I * ((x : ℂ) + η * Complex.I)) *
                (SchwartzMap.fourierTransformCLM ℂ ψ) x := by
            rw [MeasureTheory.integral_finset_sum I hinner]
      _ =
        ∑ n ∈ I, ∑ m ∈ J,
          ∫ x : ℝ,
            OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n
                  (((F : BorchersSequence d).funcs n))
                  (F.ordered_tsupport n))
                (PositiveTimeBorchersSequence.single m
                  (((G : BorchersSequence d).funcs m))
                  (G.ordered_tsupport m))
                (-Complex.I * ((x : ℂ) + η * Complex.I)) *
              (SchwartzMap.fourierTransformCLM ℂ ψ) x := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [MeasureTheory.integral_finset_sum J (fun m hm => hint n hn m hm)]
  exact Filter.Tendsto.congr' hEq.symm (by simpa [ψ] using hsum)

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

/-- The OS-II parametric flat-tube branch agrees with the explicit total-time
semigroup branch on the whole one-coordinate flat log-tube union.  This is the
flat-tube branch-carrier form of the common real-edge identity: after the
coordinate-line OS-II argument, any flat-tube point is represented by updating
one coordinate of its real log base. -/
theorem osiiParametricFlatTubeBranch_eq_totalLog_on_flatTube
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ)) :
    Set.EqOn
      (osiiParametricFlatTubeBranch (d := d) OS lgc F G)
      (osiiTotalLogSemigroupBranch (d := d) OS lgc F G)
      (osiiMZFlatLogTubeUnion m (Real.pi / 2)) := by
  intro r hr
  rcases hr with ⟨q, hq_strip, hzero⟩
  let x : Fin m → ℝ := osiiRealLogBase r
  have hupdate : Function.update (osiiMZLogRealEmbed x) q (r q) = r := by
    funext p
    by_cases hp : p = q
    · subst hp
      simp [x]
    · apply Complex.ext
      · simp [x, osiiRealLogBase, osiiMZLogRealEmbed, Function.update, hp]
      · simp [x, osiiMZLogRealEmbed, Function.update, hp, hzero p hp]
  have hline :=
    osiiParametricFlatTubeBranch_coordinate_line_eq_total_log
      (d := d) OS lgc F G hG_compact x q hq_strip
  simpa [hupdate] using hline

/-- The explicit total semigroup branch is the full log-domain MZ
continuation packet for the OS-II parametric flat-tube branch. -/
theorem exists_osiiTotalLogSemigroupBranch_extension_of_parametricFlatTubeBranch
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ)) :
    ∃ Γ : (Fin m → ℂ) → ℂ,
      DifferentiableOn ℂ Γ (osiiMZLogDomain m (Real.pi / 2)) ∧
        Set.EqOn Γ
          (osiiParametricFlatTubeBranch (d := d) OS lgc F G)
          (osiiMZFlatLogTubeUnion m (Real.pi / 2)) ∧
          ∀ x : Fin m → ℝ,
            Γ (osiiMZLogRealEmbed x) =
              osiiTotalPositiveTimeRealEdge (d := d) OS F G x := by
  refine ⟨osiiTotalLogSemigroupBranch (d := d) OS lgc F G, ?_, ?_, ?_⟩
  · exact differentiableOn_osiiTotalLogSemigroupBranch_l1 (d := d) OS lgc F G
  · intro z hz
    have hflat :=
      osiiParametricFlatTubeBranch_eq_totalLog_on_flatTube
        (d := d) (m := m) OS lgc F G hG_compact
    exact (hflat hz).symm
  · exact osiiTotalLogSemigroupBranch_real_edge_eq_total
      (d := d) OS lgc F G hG_compact

/-- The full total-time log branch restricts to each matching-base directional
branch on that coordinate's flat tube.  This is the branch-family form of the
OS-II flat-tube carrier equality. -/
theorem osiiTotalLogSemigroupBranch_eq_matchingBaseDirectional_on_flatCoordinate
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (q : Fin m) :
    Set.EqOn
      (osiiTotalLogSemigroupBranch (d := d) OS lgc F G)
      (fun r : Fin m → ℂ =>
        osiiMatchingBaseDirectionalLogBranch (d := d) OS lgc F G
          (osiiRealLogBase r) q r)
      {r : Fin m → ℂ |
        |(r q).im| < Real.pi / 2 ∧ ∀ p : Fin m, p ≠ q → (r p).im = 0} := by
  intro r hrq
  have hflatUnion : r ∈ osiiMZFlatLogTubeUnion m (Real.pi / 2) := ⟨q, hrq⟩
  have hparam_total :=
    osiiParametricFlatTubeBranch_eq_totalLog_on_flatTube
      (d := d) (m := m) OS lgc F G hG_compact hflatUnion
  have hparam_direction :=
    osiiParametricFlatTubeBranch_eq_directional_of_mem
      (d := d) OS lgc F G hG_compact hrq
  exact hparam_total.symm.trans hparam_direction

end OSReconstruction
