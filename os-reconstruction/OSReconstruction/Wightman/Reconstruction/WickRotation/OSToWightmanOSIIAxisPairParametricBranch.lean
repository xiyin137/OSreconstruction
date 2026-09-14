/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIEuclideanDirectionSemigroup










noncomputable section

open Complex Topology
open scoped Classical BigOperators

namespace OSReconstruction

variable {d n m : ℕ} [NeZero d]

/-- Common left and right sources admissible in every canonical axis-pair
frame. -/
structure OSIIAxisPairCommonSourceData
    (d n m : ℕ) [NeZero d] (T : ℝ) where
  left : SchwartzNPoint d n
  left_support :
    ∀ a : osiiAxisPairIndex d,
      tsupport ((left : SchwartzNPoint d n) : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedNegativeTimeRegion
          (d := d) (n := n) (osiiAxisPairRotationData T a).matrix
  right : SchwartzNPoint d m
  right_support :
    ∀ a : osiiAxisPairIndex d,
      tsupport ((right : SchwartzNPoint d m) : NPointDomain d m → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion
          (d := d) (n := m) (osiiAxisPairRotationData T a).matrix

/-- Positive coefficients associated to a real log base. -/
def osiiAxisPairPositiveCoefficients
    (x : osiiAxisPairIndex d → ℝ) :
    osiiAxisPairIndex d → ℝ :=
  fun a => Real.exp (x a)

omit [NeZero d] in
theorem osiiAxisPairPositiveCoefficients_pos
    (x : osiiAxisPairIndex d → ℝ) (a : osiiAxisPairIndex d) :
    0 < osiiAxisPairPositiveCoefficients x a :=
  Real.exp_pos _

/-- Real log base of an axis-pair coefficient configuration. -/
def osiiAxisPairRealLogBase
    (r : osiiAxisPairIndex d → ℂ) :
    osiiAxisPairIndex d → ℝ :=
  fun a => (r a).re

/-- One-coordinate log strip for a selected axis-pair coefficient. -/
def osiiAxisPairCoordinateLogStrip
    (a : osiiAxisPairIndex d) :
    Set (osiiAxisPairIndex d → ℂ) :=
  {r | |(r a).im| < Real.pi / 2}

/-- Union of all one-coordinate flat axis-pair log tubes. -/
def osiiAxisPairFlatLogTubeUnion :
    Set (osiiAxisPairIndex d → ℂ) :=
  {r | ∃ a : osiiAxisPairIndex d,
    |(r a).im| < Real.pi / 2 ∧
      ∀ b : osiiAxisPairIndex d, b ≠ a → (r b).im = 0}

omit [NeZero d] in
/-- Updating one complex log coordinate leaves the real log base unchanged
away from that coordinate. -/
theorem osiiAxisPairRealLogBase_update_eq_off_selected
    (x : osiiAxisPairIndex d → ℝ)
    (a : osiiAxisPairIndex d) (w : ℂ) :
    ∀ b, b ≠ a →
      osiiAxisPairRealLogBase
          (Function.update (osiiAxisPairLogRealEmbed x) a w) b =
        x b := by
  intro b hba
  simp [osiiAxisPairRealLogBase, osiiAxisPairLogRealEmbed,
    Function.update, hba]

omit [NeZero d] in
/-- Exponentiation sends a selected axis-pair log strip to the right
half-plane. -/
theorem osiiAxisPair_exp_apply_mem_rightHalfPlane
    {a : osiiAxisPairIndex d} {r : osiiAxisPairIndex d → ℂ}
    (hr : r ∈ osiiAxisPairCoordinateLogStrip a) :
    Complex.exp (r a) ∈ {z : ℂ | 0 < z.re} := by
  have hstrip : -(Real.pi / 2) < (r a).im ∧ (r a).im < Real.pi / 2 :=
    abs_lt.mp hr
  have hcos : 0 < Real.cos (r a).im :=
    Real.cos_pos_of_mem_Ioo hstrip
  have hexp : 0 < Real.exp (r a).re := Real.exp_pos _
  simpa [Complex.exp_re] using mul_pos hexp hcos

namespace OSIIAxisPairCommonSourceData

/-- Directional branch through a fixed real log base. -/
def matchingLogBranch
    (Q : OSIIAxisPairCommonSourceData d n m T)
    (hT : 1 < T)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (x : osiiAxisPairIndex d → ℝ)
    (a : osiiAxisPairIndex d) :
    (osiiAxisPairIndex d → ℂ) → ℂ :=
  fun r =>
    (OSIIAxisPairRotatedSourcePacket.compensatedFrozen
      T hT
      (osiiAxisPairPositiveCoefficients x)
      (fun b => le_of_lt (osiiAxisPairPositiveCoefficients_pos x b))
      a Q.left (Q.left_support a) Q.right (Q.right_support a)).branch
        OS lgc (Complex.exp (r a))

/-- Every selected branch has the same full-translation Schwinger value at a
matching real log base. -/
theorem matchingLogBranch_real_edge_eq_common
    (Q : OSIIAxisPairCommonSourceData d n m T)
    (hT : 1 < T)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (x : osiiAxisPairIndex d → ℝ)
    (a : osiiAxisPairIndex d) :
    Q.matchingLogBranch hT OS lgc x a
        (osiiAxisPairLogRealEmbed x) =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (OSIIAxisPairRotatedSourcePacket.commonRealSource
          T (osiiAxisPairPositiveCoefficients x) Q.left Q.right)) := by
  simpa [matchingLogBranch, osiiAxisPairLogRealEmbed,
    osiiAxisPairPositiveCoefficients] using
    OSIIAxisPairRotatedSourcePacket.compensatedFrozen_branch_selected_eq_common_schwinger
        OS lgc T hT
        (osiiAxisPairPositiveCoefficients x)
        (fun b => le_of_lt (osiiAxisPairPositiveCoefficients_pos x b))
        a (osiiAxisPairPositiveCoefficients_pos x a)
        Q.left (Q.left_support a) Q.right (Q.right_support a)

/-- The matching branch depends on its real base only away from the selected
coefficient. -/
theorem matchingLogBranch_congr_of_eq_off_selected
    (Q : OSIIAxisPairCommonSourceData d n m T)
    (hT : 1 < T)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {x y : osiiAxisPairIndex d → ℝ}
    (a : osiiAxisPairIndex d)
    (hxy : ∀ b, b ≠ a → x b = y b) :
    Q.matchingLogBranch hT OS lgc x a =
      Q.matchingLogBranch hT OS lgc y a := by
  have hcoeff :
      ∀ b, b ≠ a →
        osiiAxisPairPositiveCoefficients x b =
          osiiAxisPairPositiveCoefficients y b := by
    intro b hba
    simp [osiiAxisPairPositiveCoefficients, hxy b hba]
  have hbranch :=
    OSIIAxisPairRotatedSourcePacket.compensatedFrozen_branch_congr_of_eq_off_selected
      OS lgc T hT
      (fun b => le_of_lt (osiiAxisPairPositiveCoefficients_pos x b))
      (fun b => le_of_lt (osiiAxisPairPositiveCoefficients_pos y b))
      a hcoeff Q.left (Q.left_support a) Q.right (Q.right_support a)
  funext r
  exact congrFun hbranch (Complex.exp (r a))

end OSIIAxisPairCommonSourceData

/-- Scalar directional branch data sufficient for the axis-pair flat-tube
gluing. Concrete source constructors may vary with the selected direction; the
only shared datum required here is the real-edge scalar. -/
structure OSIIAxisPairDirectionalBranchFamily (d : ℕ) [NeZero d] where
  branch :
    (osiiAxisPairIndex d → ℝ) →
      osiiAxisPairIndex d → (osiiAxisPairIndex d → ℂ) → ℂ
  realEdge : (osiiAxisPairIndex d → ℝ) → ℂ
  branch_differentiableOn :
    ∀ x a, DifferentiableOn ℂ (branch x a)
      (osiiAxisPairCoordinateLogStrip a)
  branch_congr_of_eq_off_selected :
    ∀ {x y} a, (∀ b, b ≠ a → x b = y b) →
      branch x a = branch y a
  branch_real_edge :
    ∀ x a, branch x a (osiiAxisPairLogRealEmbed x) = realEdge x

namespace OSIIAxisPairDirectionalBranchFamily

/-- Choice-independent scalar branch associated to an abstract coherent
directional family. -/
noncomputable def flatTubeBranch
    (F : OSIIAxisPairDirectionalBranchFamily d)
    (r : osiiAxisPairIndex d → ℂ) : ℂ :=
  if hr : r ∈ osiiAxisPairFlatLogTubeUnion (d := d) then
    F.branch (osiiAxisPairRealLogBase r) (Classical.choose hr) r
  else
    0

/-- Coherent directional families agree on every overlap of two flat
coordinate presentations. -/
theorem branch_eq_on_flat_overlap
    (F : OSIIAxisPairDirectionalBranchFamily d)
    {r : osiiAxisPairIndex d → ℂ}
    {a a' : osiiAxisPairIndex d}
    (hra :
      |(r a).im| < Real.pi / 2 ∧
        ∀ b, b ≠ a → (r b).im = 0)
    (hra' :
      |(r a').im| < Real.pi / 2 ∧
        ∀ b, b ≠ a' → (r b).im = 0) :
    F.branch (osiiAxisPairRealLogBase r) a r =
      F.branch (osiiAxisPairRealLogBase r) a' r := by
  by_cases haa' : a = a'
  · subst a'
    rfl
  · have him_zero : ∀ b, (r b).im = 0 := by
      intro b
      by_cases hb : b = a
      · exact hra'.2 b (by
          intro hb'
          exact haa' (hb.symm.trans hb'))
      · exact hra.2 b hb
    have hreal :
        r = osiiAxisPairLogRealEmbed (osiiAxisPairRealLogBase r) := by
      funext b
      apply Complex.ext
      · simp [osiiAxisPairLogRealEmbed, osiiAxisPairRealLogBase]
      · simp [osiiAxisPairLogRealEmbed, him_zero b]
    rw [hreal]
    exact
      (F.branch_real_edge (osiiAxisPairRealLogBase r) a).trans
        (F.branch_real_edge (osiiAxisPairRealLogBase r) a').symm

/-- The abstract flat branch equals any presented directional branch. -/
theorem flatTubeBranch_eq_branch_of_mem
    (F : OSIIAxisPairDirectionalBranchFamily d)
    {r : osiiAxisPairIndex d → ℂ}
    {a : osiiAxisPairIndex d}
    (hra :
      |(r a).im| < Real.pi / 2 ∧
        ∀ b, b ≠ a → (r b).im = 0) :
    F.flatTubeBranch r =
      F.branch (osiiAxisPairRealLogBase r) a r := by
  have hr :
      r ∈ osiiAxisPairFlatLogTubeUnion (d := d) :=
    ⟨a, hra⟩
  unfold flatTubeBranch
  rw [dif_pos hr]
  exact F.branch_eq_on_flat_overlap (Classical.choose_spec hr) hra

/-- The abstract flat branch has the supplied common real edge. -/
theorem flatTubeBranch_real_edge
    (F : OSIIAxisPairDirectionalBranchFamily d)
    (x : osiiAxisPairIndex d → ℝ) :
    F.flatTubeBranch (osiiAxisPairLogRealEmbed x) = F.realEdge x := by
  let a : osiiAxisPairIndex d :=
    (⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩, true)
  have hra :
      |(osiiAxisPairLogRealEmbed x a).im| < Real.pi / 2 ∧
        ∀ b, b ≠ a → (osiiAxisPairLogRealEmbed x b).im = 0 := by
    constructor
    · simp [osiiAxisPairLogRealEmbed]
      positivity
    · intro b _hb
      simp [osiiAxisPairLogRealEmbed]
  have hbase :
      osiiAxisPairRealLogBase (osiiAxisPairLogRealEmbed x) = x := by
    funext b
    simp [osiiAxisPairRealLogBase, osiiAxisPairLogRealEmbed]
  calc
    F.flatTubeBranch (osiiAxisPairLogRealEmbed x) =
        F.branch
          (osiiAxisPairRealLogBase (osiiAxisPairLogRealEmbed x)) a
          (osiiAxisPairLogRealEmbed x) :=
      F.flatTubeBranch_eq_branch_of_mem hra
    _ = F.branch x a (osiiAxisPairLogRealEmbed x) := by rw [hbase]
    _ = F.realEdge x := F.branch_real_edge x a

/-- Along a flat coordinate line through a real base, the abstract flat branch
is the fixed-base directional branch. -/
theorem flatTubeBranch_coordinate_line_eq_branch
    (F : OSIIAxisPairDirectionalBranchFamily d)
    (x : osiiAxisPairIndex d → ℝ)
    (a : osiiAxisPairIndex d) {w : ℂ}
    (hw : |w.im| < Real.pi / 2) :
    F.flatTubeBranch
        (Function.update (osiiAxisPairLogRealEmbed x) a w) =
      F.branch x a
        (Function.update (osiiAxisPairLogRealEmbed x) a w) := by
  let r : osiiAxisPairIndex d → ℂ :=
    Function.update (osiiAxisPairLogRealEmbed x) a w
  have hra :
      |(r a).im| < Real.pi / 2 ∧
        ∀ b, b ≠ a → (r b).im = 0 := by
    constructor
    · simpa [r, Function.update] using hw
    · intro b hba
      simp [r, osiiAxisPairLogRealEmbed, hba]
  have hbranch :
      F.flatTubeBranch r =
        F.branch (osiiAxisPairRealLogBase r) a r :=
    F.flatTubeBranch_eq_branch_of_mem hra
  have hfreeze :
      F.branch (osiiAxisPairRealLogBase r) a = F.branch x a :=
    F.branch_congr_of_eq_off_selected a
      (osiiAxisPairRealLogBase_update_eq_off_selected x a w)
  calc
    F.flatTubeBranch
        (Function.update (osiiAxisPairLogRealEmbed x) a w) =
      F.flatTubeBranch r := rfl
    _ = F.branch (osiiAxisPairRealLogBase r) a r := hbranch
    _ = F.branch x a r := congrFun hfreeze r
    _ = F.branch x a
          (Function.update (osiiAxisPairLogRealEmbed x) a w) := rfl

/-- Every coordinate-line slice of an abstract coherent directional family is
holomorphic on the OS-II strip. -/
theorem flatTubeBranch_coordinate_line_differentiableOn
    (F : OSIIAxisPairDirectionalBranchFamily d)
    (x : osiiAxisPairIndex d → ℝ)
    (a : osiiAxisPairIndex d) :
    DifferentiableOn ℂ
      (fun w : ℂ =>
        F.flatTubeBranch
          (Function.update (osiiAxisPairLogRealEmbed x) a w))
      {w : ℂ | |w.im| < Real.pi / 2} := by
  let line : ℂ → osiiAxisPairIndex d → ℂ :=
    fun w => Function.update (osiiAxisPairLogRealEmbed x) a w
  have hline_diff : Differentiable ℂ line := by
    rw [differentiable_pi]
    intro b
    by_cases hba : b = a
    · subst b
      simp [line]
    · simp [line, hba]
  have hmaps :
      Set.MapsTo line {w : ℂ | |w.im| < Real.pi / 2}
        (osiiAxisPairCoordinateLogStrip a) := by
    intro w hw
    simpa [line, osiiAxisPairCoordinateLogStrip, Function.update] using hw
  have hfixed :
      DifferentiableOn ℂ
        (fun w : ℂ => F.branch x a (line w))
        {w : ℂ | |w.im| < Real.pi / 2} :=
    (F.branch_differentiableOn x a).comp
      hline_diff.differentiableOn hmaps
  refine hfixed.congr ?_
  intro w hw
  simpa [line] using F.flatTubeBranch_coordinate_line_eq_branch x a hw

end OSIIAxisPairDirectionalBranchFamily

/-- A coherent axis-pair cross together with the joint continuity needed for
Malgrange-Zerner promotion.

The directional family already supplies overlap agreement, the common real
edge, and one-variable holomorphy. This structure adds exactly the missing
continuity in the inactive real base and active complex strip coordinate. -/
structure OSIIAxisPairFlatCrossData (d : ℕ) [NeZero d] where
  family : OSIIAxisPairDirectionalBranchFamily d
  chart_continuous :
    ∀ a : osiiAxisPairIndex d,
      ContinuousOn
        (fun p : (osiiAxisPairIndex d → ℝ) × ℂ =>
          family.flatTubeBranch
            (Function.update (osiiAxisPairLogRealEmbed p.1) a p.2))
        (Set.univ ×ˢ {w : ℂ | |w.im| < Real.pi / 2})

namespace OSIIAxisPairFlatCrossData

/-- Every coordinate line of a flat cross is holomorphic on the OS-II strip. -/
theorem coordinateLine_differentiableOn
    (X : OSIIAxisPairFlatCrossData d)
    (x : osiiAxisPairIndex d → ℝ)
    (a : osiiAxisPairIndex d) :
    DifferentiableOn ℂ
      (fun w : ℂ =>
        X.family.flatTubeBranch
          (Function.update (osiiAxisPairLogRealEmbed x) a w))
      {w : ℂ | |w.im| < Real.pi / 2} :=
  X.family.flatTubeBranch_coordinate_line_differentiableOn x a

/-- The common real edge of a continuous flat cross is continuous. -/
theorem continuous_realEdge
    (X : OSIIAxisPairFlatCrossData d) :
    Continuous X.family.realEdge := by
  let a : osiiAxisPairIndex d :=
    (⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩, true)
  let diagonal :
      (osiiAxisPairIndex d → ℝ) →
        (osiiAxisPairIndex d → ℝ) × ℂ :=
    fun x => (x, (x a : ℂ))
  have hdiagonal : Continuous diagonal := by
    exact continuous_id.prodMk
      (Complex.continuous_ofReal.comp (continuous_apply a))
  have hmaps :
      Set.MapsTo diagonal Set.univ
        (Set.univ ×ˢ {w : ℂ | |w.im| < Real.pi / 2}) := by
    intro x _hx
    refine ⟨Set.mem_univ _, ?_⟩
    simpa [diagonal] using (show (0 : ℝ) < Real.pi / 2 by positivity)
  have hcont :
      Continuous
        (fun x : osiiAxisPairIndex d → ℝ =>
          X.family.flatTubeBranch
            (Function.update (osiiAxisPairLogRealEmbed x) a (x a : ℂ))) := by
    rw [← continuousOn_univ]
    simpa [diagonal] using
      (X.chart_continuous a).comp hdiagonal.continuousOn hmaps
  refine hcont.congr ?_
  intro x
  have hupdate :
      Function.update (osiiAxisPairLogRealEmbed x) a (x a : ℂ) =
        osiiAxisPairLogRealEmbed x := by
    ext b
    by_cases hba : b = a
    · subst b
      simp [osiiAxisPairLogRealEmbed]
    · simp [osiiAxisPairLogRealEmbed, Function.update, hba]
  rw [hupdate]
  exact X.family.flatTubeBranch_real_edge x

end OSIIAxisPairFlatCrossData

/-- A coherent family of admissible rotated semigroup packets. The
one-variable holomorphy is supplied by the packet construction itself; a
producer only has to prove frozen-base coherence and identify the common
scalar real edge. -/
structure OSIIAxisPairSemigroupPacketFamily
    (d n m : ℕ) [NeZero d] (T : ℝ)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) where
  packet :
    (osiiAxisPairIndex d → ℝ) →
      (a : osiiAxisPairIndex d) →
        OSIIAxisPairRotatedSourcePacket d n m T a
  realEdge : (osiiAxisPairIndex d → ℝ) → ℂ
  packet_logBranch_congr_of_eq_off_selected :
    ∀ {x y : osiiAxisPairIndex d → ℝ} a,
      (∀ b, b ≠ a → x b = y b) →
        (fun r : osiiAxisPairIndex d → ℂ =>
          (packet x a).branch OS lgc (Complex.exp (r a))) =
        (fun r : osiiAxisPairIndex d → ℂ =>
          (packet y a).branch OS lgc (Complex.exp (r a)))
  packet_real_edge :
    ∀ x a,
      (packet x a).branch OS lgc
          (osiiAxisPairPositiveCoefficients x a : ℂ) =
        realEdge x

namespace OSIIAxisPairSemigroupPacketFamily

/-- Log-coordinate branch associated to one selected semigroup packet. -/
def logBranch
    (F : OSIIAxisPairSemigroupPacketFamily d n m T OS lgc)
    (x : osiiAxisPairIndex d → ℝ)
    (a : osiiAxisPairIndex d) :
    (osiiAxisPairIndex d → ℂ) → ℂ :=
  fun r => (F.packet x a).branch OS lgc (Complex.exp (r a))

/-- Packet semigroup holomorphy promotes automatically to the selected
axis-pair log strip. -/
theorem logBranch_differentiableOn
    (F : OSIIAxisPairSemigroupPacketFamily d n m T OS lgc)
    (x : osiiAxisPairIndex d → ℝ)
    (a : osiiAxisPairIndex d) :
    DifferentiableOn ℂ (F.logBranch x a)
      (osiiAxisPairCoordinateLogStrip a) := by
  have hexp :
      DifferentiableOn ℂ
        (fun r : osiiAxisPairIndex d → ℂ => Complex.exp (r a))
        (osiiAxisPairCoordinateLogStrip a) :=
    (Complex.differentiable_exp.comp
      (differentiable_apply a)).differentiableOn
  exact
    ((F.packet x a).branch_differentiableOn OS lgc).comp hexp
      (fun _r hr => osiiAxisPair_exp_apply_mem_rightHalfPlane hr)

/-- The packet-family coherence field is exactly log-branch coherence. -/
theorem logBranch_congr_of_eq_off_selected
    (F : OSIIAxisPairSemigroupPacketFamily d n m T OS lgc)
    {x y : osiiAxisPairIndex d → ℝ}
    (a : osiiAxisPairIndex d)
    (hxy : ∀ b, b ≠ a → x b = y b) :
    F.logBranch x a = F.logBranch y a :=
  F.packet_logBranch_congr_of_eq_off_selected a hxy

/-- The logarithmic real point evaluates to the packet family’s common
scalar edge. -/
theorem logBranch_real_edge
    (F : OSIIAxisPairSemigroupPacketFamily d n m T OS lgc)
    (x : osiiAxisPairIndex d → ℝ)
    (a : osiiAxisPairIndex d) :
    F.logBranch x a (osiiAxisPairLogRealEmbed x) = F.realEdge x := by
  simpa [logBranch, osiiAxisPairLogRealEmbed,
    osiiAxisPairPositiveCoefficients] using F.packet_real_edge x a

/-- Forget the packet realization and retain the scalar directional family
needed by flat-tube gluing and the later MZ promotion. -/
def toDirectionalBranchFamily
    (F : OSIIAxisPairSemigroupPacketFamily d n m T OS lgc) :
    OSIIAxisPairDirectionalBranchFamily d where
  branch := F.logBranch
  realEdge := F.realEdge
  branch_differentiableOn := F.logBranch_differentiableOn
  branch_congr_of_eq_off_selected :=
    F.logBranch_congr_of_eq_off_selected
  branch_real_edge := F.logBranch_real_edge

/-- Joint continuity of the selected packet log branches promotes to joint
continuity of the choice-independent flat branch on every coordinate chart. -/
theorem continuousOn_flatTubeBranch_coordinateChart_of_packet
    (F : OSIIAxisPairSemigroupPacketFamily d n m T OS lgc)
    (hpacket :
      ∀ a : osiiAxisPairIndex d,
        ContinuousOn
          (fun p : (osiiAxisPairIndex d → ℝ) × ℂ =>
            (F.packet p.1 a).branch OS lgc (Complex.exp p.2))
          (Set.univ ×ˢ {w : ℂ | |w.im| < Real.pi / 2}))
    (a : osiiAxisPairIndex d) :
    ContinuousOn
      (fun p : (osiiAxisPairIndex d → ℝ) × ℂ =>
        F.toDirectionalBranchFamily.flatTubeBranch
          (Function.update (osiiAxisPairLogRealEmbed p.1) a p.2))
      (Set.univ ×ˢ {w : ℂ | |w.im| < Real.pi / 2}) := by
  refine (hpacket a).congr ?_
  intro p hp
  simpa [toDirectionalBranchFamily, logBranch] using
    (F.toDirectionalBranchFamily.flatTubeBranch_coordinate_line_eq_branch
      p.1 a hp.2)

/-- Package a semigroup packet family with continuous selected packet charts
as the continuous flat cross consumed by Malgrange-Zerner promotion. -/
def toFlatCrossData_of_packet_continuous
    (F : OSIIAxisPairSemigroupPacketFamily d n m T OS lgc)
    (hpacket :
      ∀ a : osiiAxisPairIndex d,
        ContinuousOn
          (fun p : (osiiAxisPairIndex d → ℝ) × ℂ =>
            (F.packet p.1 a).branch OS lgc (Complex.exp p.2))
          (Set.univ ×ˢ {w : ℂ | |w.im| < Real.pi / 2})) :
    OSIIAxisPairFlatCrossData d where
  family := F.toDirectionalBranchFamily
  chart_continuous :=
    F.continuousOn_flatTubeBranch_coordinateChart_of_packet hpacket

end OSIIAxisPairSemigroupPacketFamily

namespace OSIIAxisPairCommonSourceData

/-- The common-source construction as a coherent semigroup packet family.
This is the prototype implementation; product-source producers may choose
different admissible packets for different selected directions. -/
def toSemigroupPacketFamily
    (Q : OSIIAxisPairCommonSourceData d n m T)
    (hT : 1 < T)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    OSIIAxisPairSemigroupPacketFamily d n m T OS lgc where
  packet := fun x a =>
    OSIIAxisPairRotatedSourcePacket.compensatedFrozen
      T hT
      (osiiAxisPairPositiveCoefficients x)
      (fun b => le_of_lt (osiiAxisPairPositiveCoefficients_pos x b))
      a Q.left (Q.left_support a) Q.right (Q.right_support a)
  realEdge := fun x =>
    OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
      (OSIIAxisPairRotatedSourcePacket.commonRealSource
        T (osiiAxisPairPositiveCoefficients x) Q.left Q.right))
  packet_logBranch_congr_of_eq_off_selected := fun a hxy => by
    simpa [matchingLogBranch] using
      Q.matchingLogBranch_congr_of_eq_off_selected hT OS lgc a hxy
  packet_real_edge := fun x a => by
    simpa [matchingLogBranch, osiiAxisPairLogRealEmbed,
      osiiAxisPairPositiveCoefficients] using
      Q.matchingLogBranch_real_edge_eq_common hT OS lgc x a

end OSIIAxisPairCommonSourceData

end OSReconstruction
