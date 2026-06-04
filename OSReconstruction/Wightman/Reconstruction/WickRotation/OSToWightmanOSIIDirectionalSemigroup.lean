/-
Copyright (c) 2026 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSemigroup
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIMZLogDomain
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIRealEdgeSemigroup

/-!
# OS II Directional Semigroup Representatives

This file starts the producer side of OS II Chapter V.1.  The existing
semigroup bridge gives holomorphic matrix elements on the right half-plane in
the semigroup parameter.  OS II Lemma 5.1 uses positive imaginary time
coordinates, so the first checked conversion is the rotation `w ↦ -i w`.
-/

noncomputable section

open Complex Topology MeasureTheory
open scoped Classical NNReal BigOperators

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

/-- Rotating the checked one-variable semigroup matrix element gives a
holomorphic representative on the upper half-plane, the coordinate shape used
in the OS-II positive-time tube. -/
theorem osii_rotated_expandBoth_differentiableOn_upperHalfPlane
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) :
    DifferentiableOn ℂ
      (fun w : ℂ =>
        OSInnerProductTimeShiftHolomorphicValueExpandBoth
          (d := d) OS lgc F G (-Complex.I * w))
      {w : ℂ | 0 < w.im} := by
  have hH :
      DifferentiableOn ℂ
        (OSInnerProductTimeShiftHolomorphicValueExpandBoth
          (d := d) OS lgc F G)
        {z : ℂ | 0 < z.re} :=
    differentiableOn_OSInnerProductTimeShiftHolomorphicValueExpandBoth
      (d := d) OS lgc F G
  have hrot :
      Differentiable ℂ (fun w : ℂ => -Complex.I * w) := by
    have hconst : Differentiable ℂ (fun _ : ℂ => -Complex.I) :=
      differentiable_const _
    exact hconst.mul differentiable_id
  refine hH.comp hrot.differentiableOn ?_
  intro w hw
  simpa [Complex.mul_re, Complex.mul_im] using hw

/-- Continuity form of the rotated one-variable semigroup representative. -/
theorem osii_rotated_expandBoth_continuousOn_upperHalfPlane
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) :
    ContinuousOn
      (fun w : ℂ =>
        OSInnerProductTimeShiftHolomorphicValueExpandBoth
          (d := d) OS lgc F G (-Complex.I * w))
      {w : ℂ | 0 < w.im} :=
  (osii_rotated_expandBoth_differentiableOn_upperHalfPlane
    (d := d) OS lgc F G).continuousOn

/-! ### Real-edge and log-coordinate forms -/

/-- On the positive imaginary axis of the rotated upper-half-plane variable,
the directional representative recovers the real Euclidean time-shift OS
pairing. -/
theorem osii_rotated_expandBoth_positive_imag_eq_OSInnerProduct
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((
        G : BorchersSequence d).funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ))
    (η : ℝ) (hη : 0 < η) :
    OSInnerProductTimeShiftHolomorphicValueExpandBoth
        (d := d) OS lgc F G (-Complex.I * (η * Complex.I)) =
      OSInnerProduct d OS.S (F : BorchersSequence d)
        (timeShiftBorchers (d := d) η (G : BorchersSequence d)) := by
  have harg : -Complex.I * (η * Complex.I) = (η : ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  rw [harg]
  exact OSInnerProductTimeShiftHolomorphicValueExpandBoth_ofReal_eq_of_isCompactSupport
    (d := d) OS lgc F G hG_compact η hη

/-- One-coordinate log strip used by the OS-II Malgrange-Zerner step.  The
condition is the paper's `|Im r_q| < pi / 2` before exponentiating the
coefficient variable `u_q = exp r_q`. -/
def osiiMZCoordinateLogStrip (m : ℕ) (q : Fin m) : Set (Fin m → ℂ) :=
  {r | |(r q).im| < Real.pi / 2}

/-- Exponentiation sends the OS-II log strip `|Im r_q| < pi / 2` into the
right half-plane in the coefficient variable. -/
theorem osiiMZ_exp_apply_mem_rightHalfPlane
    {m : ℕ} {q : Fin m} {r : Fin m → ℂ}
    (hr : r ∈ osiiMZCoordinateLogStrip m q) :
    Complex.exp (r q) ∈ {z : ℂ | 0 < z.re} := by
  have hstrip : -(Real.pi / 2) < (r q).im ∧ (r q).im < Real.pi / 2 :=
    abs_lt.mp hr
  have hcos : 0 < Real.cos (r q).im :=
    Real.cos_pos_of_mem_Ioo hstrip
  have hexp : 0 < Real.exp (r q).re := Real.exp_pos _
  simpa [Complex.exp_re] using mul_pos hexp hcos

/-- The log-coordinate directional semigroup branch is holomorphic on its
one-coordinate strip.  This is the checked `r = log u` form of the OS-II
one-variable semigroup representative. -/
theorem osii_log_semigroup_branch_differentiableOn_coordinateStrip
    {m : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) (q : Fin m) :
    DifferentiableOn ℂ
      (fun r : Fin m → ℂ =>
        OSInnerProductTimeShiftHolomorphicValueExpandBoth
          (d := d) OS lgc F G (Complex.exp (r q)))
      (osiiMZCoordinateLogStrip m q) := by
  have hexp_diff :
      DifferentiableOn ℂ (fun r : Fin m → ℂ => Complex.exp (r q))
        (osiiMZCoordinateLogStrip m q) :=
    (Complex.differentiable_exp.comp (differentiable_apply q)).differentiableOn
  exact
    (differentiableOn_OSInnerProductTimeShiftHolomorphicValueExpandBoth
      (d := d) OS lgc F G).comp hexp_diff
      (fun r hr => osiiMZ_exp_apply_mem_rightHalfPlane (m := m) (q := q) hr)

/-- On the real log edge, the log-coordinate branch recovers the positive-time
Euclidean semigroup pairing at time `exp x_q`. -/
theorem osii_log_semigroup_branch_real_edge_eq_OSInnerProduct
    {m : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((
        G : BorchersSequence d).funcs n : SchwartzNPoint d n) : NPointDomain d n → ℂ))
    (q : Fin m) (x : Fin m → ℝ) :
    OSInnerProductTimeShiftHolomorphicValueExpandBoth
        (d := d) OS lgc F G (Complex.exp ((x q : ℝ) : ℂ)) =
      OSInnerProduct d OS.S (F : BorchersSequence d)
        (timeShiftBorchers (d := d) (Real.exp (x q)) (G : BorchersSequence d)) := by
  have hpos : 0 < Real.exp (x q) := Real.exp_pos _
  have hexp : Complex.exp ((x q : ℝ) : ℂ) = (Real.exp (x q) : ℂ) := by
    simp
  rw [hexp]
  exact OSInnerProductTimeShiftHolomorphicValueExpandBoth_ofReal_eq_of_isCompactSupport
    (d := d) OS lgc F G hG_compact (Real.exp (x q)) hpos

/-- The `l1` Malgrange-Zerner log carrier lies inside every one-coordinate log
strip. -/
theorem osiiMZ_l1LogCarrier_subset_coordinateLogStrip
    {m : ℕ} {alpha : ℝ} (q : Fin m) :
    osiiMZLogDomain m alpha ⊆
      {r : Fin m → ℂ | |(r q).im| < alpha} := by
  intro r hr
  exact lt_of_le_of_lt
    (Finset.single_le_sum (fun p _ => abs_nonneg (r p).im) (Finset.mem_univ q))
    (by simpa [osiiMZLogDomain] using hr)

/-- One-coordinate semigroup branches are holomorphic on the final
`sum |Im r| < pi/2` log carrier after restricting from their coordinate strip.
The Malgrange-Zerner step still supplies the multi-coordinate representative;
this theorem records the checked domain restriction for each directional
branch. -/
theorem osii_log_semigroup_branch_differentiableOn_l1LogCarrier
    {m : ℕ}
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) (q : Fin m) :
    DifferentiableOn ℂ
      (fun r : Fin m → ℂ =>
        OSInnerProductTimeShiftHolomorphicValueExpandBoth
          (d := d) OS lgc F G (Complex.exp (r q)))
      (osiiMZLogDomain m (Real.pi / 2)) := by
  exact
    (osii_log_semigroup_branch_differentiableOn_coordinateStrip
      (d := d) OS lgc F G q).mono
      (osiiMZ_l1LogCarrier_subset_coordinateLogStrip
        (m := m) (alpha := Real.pi / 2) q)

/-- OS-II scalar MZ representative for the semigroup log branches.

Once the one-coordinate directional semigroup representatives are known to
share the same Schwinger real edge, the scalar Malgrange-Zerner handoff glues
them to a single holomorphic representative on `sum |Im r_q| < pi / 2`.  The
remaining OS-specific producer is exactly the common-real-edge identity. -/
theorem osii_mz_log_semigroup_representative_of_common_real_edge
    {m : ℕ} [Nonempty (Fin m)]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (realEdge : (Fin m → ℝ) → ℂ)
    (hreal :
      ∀ q x,
        OSInnerProduct d OS.S (F : BorchersSequence d)
          (timeShiftBorchers (d := d) (Real.exp (x q)) (G : BorchersSequence d)) =
          realEdge x) :
    ∃ Γ : (Fin m → ℂ) → ℂ,
      DifferentiableOn ℂ Γ (osiiMZLogDomain m (Real.pi / 2)) ∧
        (∀ x : Fin m → ℝ, Γ (osiiMZLogRealEmbed x) = realEdge x) ∧
          ∀ q,
            Set.EqOn Γ
              (fun r : Fin m → ℂ =>
                OSInnerProductTimeShiftHolomorphicValueExpandBoth
                  (d := d) OS lgc F G (Complex.exp (r q)))
              (osiiMZLogDomain m (Real.pi / 2)) := by
  let D : Fin m → (Fin m → ℂ) → ℂ := fun q r =>
    OSInnerProductTimeShiftHolomorphicValueExpandBoth
      (d := d) OS lgc F G (Complex.exp (r q))
  have hD : ∀ q, DifferentiableOn ℂ (D q) (osiiMZLogDomain m (Real.pi / 2)) := by
    intro q
    simpa [D] using
      osii_log_semigroup_branch_differentiableOn_l1LogCarrier
        (d := d) OS lgc F G q
  have hDreal : ∀ q x, D q (osiiMZLogRealEmbed x) = realEdge x := by
    intro q x
    have hbranch :=
      osii_log_semigroup_branch_real_edge_eq_OSInnerProduct
        (d := d) OS lgc F G hG_compact q x
    have hbranch' :
        D q (osiiMZLogRealEmbed x) =
          OSInnerProduct d OS.S (F : BorchersSequence d)
            (timeShiftBorchers (d := d) (Real.exp (x q)) (G : BorchersSequence d)) := by
      simpa [D, osiiMZLogRealEmbed] using hbranch
    exact hbranch'.trans (hreal q x)
  simpa [D] using
    exists_osiiMZLog_representative_of_common_real_edge
      (m := m) (α := Real.pi / 2) (by positivity) D hD realEdge hDreal

/-- Family form of `osii_mz_log_semigroup_representative_of_common_real_edge`.

This is the OS-II Lemma 5.1 shape after splitting the scalar product around
each selected direction: the positive-time vectors may depend on the coordinate
direction, but all directional real edges must identify with the same Schwinger
scalar. -/
theorem osii_mz_log_semigroup_representative_of_common_real_edge_family
    {m : ℕ} [Nonempty (Fin m)]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : Fin m → PositiveTimeBorchersSequence d)
    (hG_compact : ∀ q n,
      HasCompactSupport (((G q : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (realEdge : (Fin m → ℝ) → ℂ)
    (hreal :
      ∀ q x,
        OSInnerProduct d OS.S (F q : BorchersSequence d)
          (timeShiftBorchers (d := d) (Real.exp (x q)) (G q : BorchersSequence d)) =
          realEdge x) :
    ∃ Γ : (Fin m → ℂ) → ℂ,
      DifferentiableOn ℂ Γ (osiiMZLogDomain m (Real.pi / 2)) ∧
        (∀ x : Fin m → ℝ, Γ (osiiMZLogRealEmbed x) = realEdge x) ∧
          ∀ q,
            Set.EqOn Γ
              (fun r : Fin m → ℂ =>
                OSInnerProductTimeShiftHolomorphicValueExpandBoth
                  (d := d) OS lgc (F q) (G q) (Complex.exp (r q)))
              (osiiMZLogDomain m (Real.pi / 2)) := by
  let D : Fin m → (Fin m → ℂ) → ℂ := fun q r =>
    OSInnerProductTimeShiftHolomorphicValueExpandBoth
      (d := d) OS lgc (F q) (G q) (Complex.exp (r q))
  have hD : ∀ q, DifferentiableOn ℂ (D q) (osiiMZLogDomain m (Real.pi / 2)) := by
    intro q
    simpa [D] using
      osii_log_semigroup_branch_differentiableOn_l1LogCarrier
        (d := d) OS lgc (F q) (G q) q
  have hDreal : ∀ q x, D q (osiiMZLogRealEmbed x) = realEdge x := by
    intro q x
    have hbranch :=
      osii_log_semigroup_branch_real_edge_eq_OSInnerProduct
        (d := d) OS lgc (F q) (G q) (hG_compact q) q x
    have hbranch' :
        D q (osiiMZLogRealEmbed x) =
          OSInnerProduct d OS.S (F q : BorchersSequence d)
            (timeShiftBorchers (d := d) (Real.exp (x q)) (G q : BorchersSequence d)) := by
      simpa [D, osiiMZLogRealEmbed] using hbranch
    exact hbranch'.trans (hreal q x)
  simpa [D] using
    exists_osiiMZLog_representative_of_common_real_edge
      (m := m) (α := Real.pi / 2) (by positivity) D hD realEdge hDreal

/-! ### Local frozen one-coordinate branches -/

/-- Replace only the selected positive-time difference by the free
one-variable semigroup time. -/
def osiiFrozenTimeUpdate {m : ℕ} (τ : Fin m → ℝ) (q : Fin m) (s : ℝ) :
    Fin m → ℝ :=
  Function.update τ q s

/-- The frozen `q`-slice total time is the ordered left/right split with the
selected entry replaced by `s`. -/
theorem osii_left_add_selected_add_right_eq_sum_update
    {m : ℕ} (τ : Fin m → ℝ) (q : Fin m) (s : ℝ) :
    osiiLeftTimeSum τ q + s + osiiRightTimeSum τ q =
      ∑ p : Fin m, osiiFrozenTimeUpdate τ q s p := by
  let τ' : Fin m → ℝ := Function.update τ q s
  have hsplit := osii_left_add_self_add_right_eq_sum τ' q
  have hleft : osiiLeftTimeSum τ' q = osiiLeftTimeSum τ q := by
    unfold osiiLeftTimeSum
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p.val < q.val
    · have hp_ne : p ≠ q := Fin.ne_of_val_ne hp.ne
      simp [τ', hp, hp_ne]
    · simp [hp]
  have hright : osiiRightTimeSum τ' q = osiiRightTimeSum τ q := by
    unfold osiiRightTimeSum
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : q.val < p.val
    · have hp_ne : p ≠ q := fun hpq => by
        have hval : q.val = p.val := congrArg Fin.val hpq.symm
        omega
      simp [τ', hp, hp_ne]
    · simp [hp]
  have hq : τ' q = s := by
    simp [τ']
  have hsum :
      osiiLeftTimeSum τ q + s + osiiRightTimeSum τ q =
        ∑ p : Fin m, τ' p := by
    simpa [hleft, hright, hq] using hsplit
  simpa [osiiFrozenTimeUpdate, τ'] using hsum

/-- Frozen one-coordinate Schwinger real edge: start from the base real
positive-time vector `τ` and replace only coordinate `q` by `exp xq`. -/
def osiiFrozenSplitRealEdge
    (OS : OsterwalderSchraderAxioms d)
    {m : ℕ} (F G : PositiveTimeBorchersSequence d)
    (τ : Fin m → ℝ) (q : Fin m) (xq : ℝ) : ℂ :=
  OSInnerProduct d OS.S (F : BorchersSequence d)
    (timeShiftBorchers (d := d)
      (∑ p : Fin m, osiiFrozenTimeUpdate τ q (Real.exp xq) p)
      (G : BorchersSequence d))

/-- The holomorphic `q`-directional branch with all other real positive-time
variables frozen into the left/right positive-time Borchers vectors. -/
def osiiFrozenDirectionalLogBranch
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} (F G : PositiveTimeBorchersSequence d)
    (τ : Fin m → ℝ) (hτ : ∀ p, 0 ≤ τ p) (q : Fin m) :
    (Fin m → ℂ) → ℂ :=
  fun r =>
    OSInnerProductTimeShiftHolomorphicValueExpandBoth
      (d := d) OS lgc
      (osiiLeftSplitPositiveBranch (d := d) τ hτ F q)
      (osiiRightSplitPositiveBranch (d := d) τ hτ G q)
      (Complex.exp (r q))

/-- The frozen branch is holomorphic on the one-coordinate OS-II log strip. -/
theorem osii_frozen_directional_log_branch_differentiableOn_coordinateStrip
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} (F G : PositiveTimeBorchersSequence d)
    (τ : Fin m → ℝ) (hτ : ∀ p, 0 ≤ τ p) (q : Fin m) :
    DifferentiableOn ℂ
      (osiiFrozenDirectionalLogBranch (d := d) OS lgc F G τ hτ q)
      (osiiMZCoordinateLogStrip m q) := by
  simpa [osiiFrozenDirectionalLogBranch] using
    osii_log_semigroup_branch_differentiableOn_coordinateStrip
      (d := d) OS lgc
      (osiiLeftSplitPositiveBranch (d := d) τ hτ F q)
      (osiiRightSplitPositiveBranch (d := d) τ hτ G q)
      q

/-- On the real log edge, the frozen branch is exactly the Schwinger scalar on
the one-coordinate updated positive-time vector. -/
theorem osii_frozen_directional_log_branch_real_edge_eq
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (τ : Fin m → ℝ) (hτ : ∀ p, 0 ≤ τ p) (q : Fin m) (x : Fin m → ℝ) :
    osiiFrozenDirectionalLogBranch (d := d) OS lgc F G τ hτ q
        (osiiMZLogRealEmbed x) =
      osiiFrozenSplitRealEdge (d := d) OS F G τ q (x q) := by
  have hright_compact :
      ∀ n,
        HasCompactSupport
          ((((osiiRightSplitPositiveBranch (d := d) τ hτ G q :
              PositiveTimeBorchersSequence d) : BorchersSequence d).funcs n :
            SchwartzNPoint d n) : NPointDomain d n → ℂ) :=
    osiiRightSplitPositiveBranch_hasCompactSupport
      (d := d) τ hτ G hG_compact q
  have hbranch_real :
      osiiFrozenDirectionalLogBranch (d := d) OS lgc F G τ hτ q
          (osiiMZLogRealEmbed x) =
        OSInnerProduct d OS.S
          (osiiLeftSplitPositiveBranch (d := d) τ hτ F q : BorchersSequence d)
          (timeShiftBorchers (d := d) (Real.exp (x q))
            (osiiRightSplitPositiveBranch (d := d) τ hτ G q : BorchersSequence d)) := by
    simpa [osiiFrozenDirectionalLogBranch] using
      osii_log_semigroup_branch_real_edge_eq_OSInnerProduct
        (d := d) OS lgc
        (osiiLeftSplitPositiveBranch (d := d) τ hτ F q)
        (osiiRightSplitPositiveBranch (d := d) τ hτ G q)
        hright_compact q x
  have hsplit :
      OSInnerProduct d OS.S
          (osiiLeftSplitPositiveBranch (d := d) τ hτ F q : BorchersSequence d)
          (timeShiftBorchers (d := d) (Real.exp (x q))
            (osiiRightSplitPositiveBranch (d := d) τ hτ G q : BorchersSequence d)) =
        OSInnerProduct d OS.S (F : BorchersSequence d)
          (timeShiftBorchers (d := d)
            (osiiLeftTimeSum τ q + (Real.exp (x q) + osiiRightTimeSum τ q))
            (G : BorchersSequence d)) :=
    osii_real_edge_positiveBranch_agrees_combined_of_nonneg
      (d := d) OS F G τ hτ q (Real.exp (x q)) (le_of_lt (Real.exp_pos _))
  have hsum :
      osiiLeftTimeSum τ q + (Real.exp (x q) + osiiRightTimeSum τ q) =
        ∑ p : Fin m, osiiFrozenTimeUpdate τ q (Real.exp (x q)) p := by
    calc
      osiiLeftTimeSum τ q + (Real.exp (x q) + osiiRightTimeSum τ q)
          = osiiLeftTimeSum τ q + Real.exp (x q) + osiiRightTimeSum τ q := by ring
      _ = ∑ p : Fin m, osiiFrozenTimeUpdate τ q (Real.exp (x q)) p :=
          osii_left_add_selected_add_right_eq_sum_update τ q (Real.exp (x q))
  calc
    osiiFrozenDirectionalLogBranch (d := d) OS lgc F G τ hτ q
        (osiiMZLogRealEmbed x)
        =
          OSInnerProduct d OS.S
            (osiiLeftSplitPositiveBranch (d := d) τ hτ F q : BorchersSequence d)
            (timeShiftBorchers (d := d) (Real.exp (x q))
              (osiiRightSplitPositiveBranch (d := d) τ hτ G q : BorchersSequence d)) :=
          hbranch_real
    _ =
          OSInnerProduct d OS.S (F : BorchersSequence d)
            (timeShiftBorchers (d := d)
              (osiiLeftTimeSum τ q + (Real.exp (x q) + osiiRightTimeSum τ q))
              (G : BorchersSequence d)) :=
          hsplit
    _ = osiiFrozenSplitRealEdge (d := d) OS F G τ q (x q) := by
          simp [osiiFrozenSplitRealEdge, hsum]

/-- If the frozen base is the same real log point being evaluated, then the
frozen real edge is the common total positive-time Schwinger scalar. -/
theorem osii_frozen_split_real_edge_matching_base_eq_total
    (OS : OsterwalderSchraderAxioms d)
    {m : ℕ} (F G : PositiveTimeBorchersSequence d)
    (x : Fin m → ℝ) (q : Fin m) :
    osiiFrozenSplitRealEdge (d := d) OS F G (fun p => Real.exp (x p)) q (x q) =
      OSInnerProduct d OS.S (F : BorchersSequence d)
        (timeShiftBorchers (d := d)
          (∑ p : Fin m, Real.exp (x p))
          (G : BorchersSequence d)) := by
  have hupdate :
      osiiFrozenTimeUpdate (fun p : Fin m => Real.exp (x p)) q (Real.exp (x q)) =
        fun p : Fin m => Real.exp (x p) := by
    funext p
    by_cases hp : p = q
    · subst hp
      simp [osiiFrozenTimeUpdate]
    · simp [osiiFrozenTimeUpdate, hp]
  simp [osiiFrozenSplitRealEdge, hupdate]

/-- Pointwise common-edge form for the frozen directional branch at the matching
real base point.  The branch data still depends on the real point `x`; OS II
uses delta-smearing/distributional reconstruction to upgrade this pointwise
slice identity to a fixed local MZ representative. -/
theorem osii_frozen_directional_log_branch_matching_base_real_edge_eq_total
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (x : Fin m → ℝ) (q : Fin m) :
    osiiFrozenDirectionalLogBranch (d := d) OS lgc F G
        (fun p => Real.exp (x p)) (fun p => le_of_lt (Real.exp_pos (x p))) q
        (osiiMZLogRealEmbed x) =
      OSInnerProduct d OS.S (F : BorchersSequence d)
        (timeShiftBorchers (d := d)
          (∑ p : Fin m, Real.exp (x p))
          (G : BorchersSequence d)) := by
  calc
    osiiFrozenDirectionalLogBranch (d := d) OS lgc F G
        (fun p => Real.exp (x p)) (fun p => le_of_lt (Real.exp_pos (x p))) q
        (osiiMZLogRealEmbed x)
        =
          osiiFrozenSplitRealEdge (d := d) OS F G
            (fun p => Real.exp (x p)) q (x q) :=
          osii_frozen_directional_log_branch_real_edge_eq
            (d := d) OS lgc F G hG_compact
            (fun p => Real.exp (x p))
            (fun p => le_of_lt (Real.exp_pos (x p))) q x
    _ =
          OSInnerProduct d OS.S (F : BorchersSequence d)
            (timeShiftBorchers (d := d)
              (∑ p : Fin m, Real.exp (x p))
              (G : BorchersSequence d)) :=
          osii_frozen_split_real_edge_matching_base_eq_total
            (d := d) OS F G x q

/-- Matching-base common real edge for the directional frozen branches.

At a real log point `x`, if every branch freezes the non-selected positive-time
differences at the matching base `exp x`, then all selected-coordinate branches
have the same real-edge value.  This is the OS semigroup compatibility that the
distributional/Malgrange-Zerner step must lift to fixed local representatives;
it is not a substitute for that later lift. -/
theorem osii_parametric_directional_log_branch_real_edges_agree
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (x : Fin m → ℝ) (q q' : Fin m) :
    osiiFrozenDirectionalLogBranch (d := d) OS lgc F G
        (fun p => Real.exp (x p)) (fun p => le_of_lt (Real.exp_pos (x p))) q
        (osiiMZLogRealEmbed x) =
      osiiFrozenDirectionalLogBranch (d := d) OS lgc F G
        (fun p => Real.exp (x p)) (fun p => le_of_lt (Real.exp_pos (x p))) q'
        (osiiMZLogRealEmbed x) := by
  have hq :=
    osii_frozen_directional_log_branch_matching_base_real_edge_eq_total
      (d := d) OS lgc F G hG_compact x q
  have hq' :=
    osii_frozen_directional_log_branch_matching_base_real_edge_eq_total
      (d := d) OS lgc F G hG_compact x q'
  exact hq.trans hq'.symm

/-- The common total positive-time real edge is continuous in real log
coordinates.

This is the continuity input needed by the OS-II distributional/delta-smearing
lift: after writing the common real edge as the one-variable semigroup
representative evaluated at the positive total time `sum exp x_p`, continuity
follows from the checked holomorphic semigroup representative. -/
theorem continuous_osii_total_positive_time_real_edge
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ)) :
    Continuous fun x : Fin m → ℝ =>
      OSInnerProduct d OS.S (F : BorchersSequence d)
        (timeShiftBorchers (d := d)
          (∑ p : Fin m, Real.exp (x p))
          (G : BorchersSequence d)) := by
  let H : ℂ → ℂ :=
    OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc F G
  let T : (Fin m → ℝ) → ℂ := fun x =>
    ∑ p : Fin m, Complex.exp ((x p : ℝ) : ℂ)
  have hT_cont : Continuous T := by
    exact continuous_finset_sum _ fun p _ =>
      Complex.continuous_exp.comp
        (Complex.continuous_ofReal.comp (continuous_apply p))
  have hT_mem : ∀ x, T x ∈ {z : ℂ | 0 < z.re} := by
    intro x
    have hnonempty : (Finset.univ : Finset (Fin m)).Nonempty :=
      Finset.univ_nonempty
    have hpos : 0 < ∑ p : Fin m, Real.exp (x p) :=
      Finset.sum_pos (fun p _ => Real.exp_pos (x p)) hnonempty
    simpa [T] using hpos
  have hH_cont :
      Continuous fun x : Fin m → ℝ => H (T x) :=
    (continuousOn_OSInnerProductTimeShiftHolomorphicValueExpandBoth
      (d := d) OS lgc F G).comp_continuous hT_cont hT_mem
  refine hH_cont.congr ?_
  intro x
  have hpos : 0 < ∑ p : Fin m, Real.exp (x p) := by
    have hnonempty : (Finset.univ : Finset (Fin m)).Nonempty :=
      Finset.univ_nonempty
    exact Finset.sum_pos (fun p _ => Real.exp_pos (x p)) hnonempty
  simpa [H, T] using
    OSInnerProductTimeShiftHolomorphicValueExpandBoth_ofReal_eq_of_isCompactSupport
      (d := d) OS lgc F G hG_compact
      (∑ p : Fin m, Real.exp (x p)) hpos

/-- The common total positive-time real edge is continuous directly in positive
time-difference coordinates. -/
theorem continuousOn_osii_total_positive_time_real_edge_positiveOrthant
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ)) :
    ContinuousOn
      (fun τ : Fin m → ℝ =>
        OSInnerProduct d OS.S (F : BorchersSequence d)
          (timeShiftBorchers (d := d)
            (∑ p : Fin m, τ p)
            (G : BorchersSequence d)))
      {τ : Fin m → ℝ | ∀ p : Fin m, 0 < τ p} := by
  let H : ℂ → ℂ :=
    OSInnerProductTimeShiftHolomorphicValueExpandBoth (d := d) OS lgc F G
  let T : (Fin m → ℝ) → ℂ := fun τ =>
    ∑ p : Fin m, (τ p : ℂ)
  have hT_cont : Continuous T := by
    exact continuous_finset_sum _ fun p _ =>
      Complex.continuous_ofReal.comp (continuous_apply p)
  have hT_mem :
      Set.MapsTo T
        {τ : Fin m → ℝ | ∀ p : Fin m, 0 < τ p}
        {z : ℂ | 0 < z.re} := by
    intro τ hτ
    have hnonempty : (Finset.univ : Finset (Fin m)).Nonempty :=
      Finset.univ_nonempty
    have hpos : 0 < ∑ p : Fin m, τ p :=
      Finset.sum_pos (fun p _ => hτ p) hnonempty
    simpa [T] using hpos
  have hH_cont :
      ContinuousOn (fun τ : Fin m → ℝ => H (T τ))
        {τ : Fin m → ℝ | ∀ p : Fin m, 0 < τ p} :=
    (continuousOn_OSInnerProductTimeShiftHolomorphicValueExpandBoth
      (d := d) OS lgc F G).comp hT_cont.continuousOn hT_mem
  refine hH_cont.congr ?_
  intro τ hτ
  have hnonempty : (Finset.univ : Finset (Fin m)).Nonempty :=
    Finset.univ_nonempty
  have hpos : 0 < ∑ p : Fin m, τ p :=
    Finset.sum_pos (fun p _ => hτ p) hnonempty
  simpa [H, T] using
    (OSInnerProductTimeShiftHolomorphicValueExpandBoth_ofReal_eq_of_isCompactSupport
      (d := d) OS lgc F G hG_compact
      (∑ p : Fin m, τ p) hpos).symm

/-- The finite positive orthant in the real time-difference variables is open. -/
theorem isOpen_positiveOrthant_fin {m : ℕ} :
    IsOpen {τ : Fin m → ℝ | ∀ p : Fin m, 0 < τ p} := by
  simp only [Set.setOf_forall]
  exact isOpen_iInter_of_finite fun p =>
    isOpen_lt continuous_const (continuous_apply p)

/-- Pointwise continuity of the common total positive-time real edge at a
positive time-difference vector. -/
theorem continuousAt_osii_total_positive_time_real_edge_positiveOrthant
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (τ0 : Fin m → ℝ) (hτ0 : ∀ p : Fin m, 0 < τ0 p) :
    ContinuousAt
      (fun τ : Fin m → ℝ =>
        OSInnerProduct d OS.S (F : BorchersSequence d)
          (timeShiftBorchers (d := d)
            (∑ p : Fin m, τ p)
            (G : BorchersSequence d)))
      τ0 := by
  exact
    (continuousOn_osii_total_positive_time_real_edge_positiveOrthant
      (d := d) OS lgc F G hG_compact).continuousAt
      (isOpen_positiveOrthant_fin.mem_nhds hτ0)

/-- Each matching-base directional real-edge branch is continuous as a function
of the real log base point.

This is the branch-facing continuity consequence of the common total real-edge
formula above. -/
theorem continuous_osii_matching_base_directional_real_edge
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {m : ℕ} [Nonempty (Fin m)]
    (F G : PositiveTimeBorchersSequence d)
    (hG_compact : ∀ n,
      HasCompactSupport (((G : BorchersSequence d).funcs n : SchwartzNPoint d n) :
        NPointDomain d n → ℂ))
    (q : Fin m) :
    Continuous fun x : Fin m → ℝ =>
      osiiFrozenDirectionalLogBranch (d := d) OS lgc F G
        (fun p => Real.exp (x p)) (fun p => le_of_lt (Real.exp_pos (x p))) q
        (osiiMZLogRealEmbed x) := by
  refine
    (continuous_osii_total_positive_time_real_edge
      (d := d) OS lgc F G hG_compact).congr ?_
  intro x
  exact
    (osii_frozen_directional_log_branch_matching_base_real_edge_eq_total
      (d := d) OS lgc F G hG_compact x q).symm

end OSReconstruction
