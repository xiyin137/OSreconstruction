/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairMultiGapFlatCross















noncomputable section

open Complex Topology
open scoped Classical

namespace OSReconstruction

variable {d n k : ℕ} [NeZero d] [NeZero k]

/-- Number of point sources on the left of the chronological gap `i` in an
`(k + 1)`-point source tuple. -/
def osiiChronologicalGapLeftArity (i : Fin k) : ℕ :=
  i.val + 1

/-- Number of point sources on the right of the chronological gap `i` in an
`(k + 1)`-point source tuple. -/
def osiiChronologicalGapRightArity (i : Fin k) : ℕ :=
  k - i.val

omit [NeZero d] [NeZero k] in
theorem osiiChronologicalGap_arity_add
    (i : Fin k) :
    osiiChronologicalGapLeftArity i +
        osiiChronologicalGapRightArity i =
      k + 1 := by
  simp [osiiChronologicalGapLeftArity,
    osiiChronologicalGapRightArity]
  omega

/-- Reindex the left and right source blocks at gap `i` as the original
`(k + 1)`-point source tuple. -/
def osiiChronologicalGapSplitEquiv
    (i : Fin k) :
    Fin (osiiChronologicalGapLeftArity i) ⊕
        Fin (osiiChronologicalGapRightArity i) ≃
      Fin (k + 1) :=
  finSumFinEquiv.trans
    (finCongr (osiiChronologicalGap_arity_add i))

/-- A rotated source packet whose left and right degrees are retained as
data. This is the natural packet type when the selected chronological gap
determines the source split. -/
structure OSIIAxisPairGapRotatedSourcePacket
    (d : ℕ) [NeZero d] (T : ℝ) (a : osiiAxisPairIndex d) where
  leftArity : ℕ
  rightArity : ℕ
  packet :
    OSIIAxisPairRotatedSourcePacket
      d leftArity rightArity T a

namespace OSIIAxisPairGapRotatedSourcePacket

/-- The scalar semigroup branch of a gap-dependent packet. -/
def branch
    (P : OSIIAxisPairGapRotatedSourcePacket d T a)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    ℂ → ℂ :=
  P.packet.branch OS lgc

/-- Gap-dependent packet branches retain the one-variable right-half-plane
holomorphy of the underlying rotated packet. -/
theorem branch_differentiableOn
    (P : OSIIAxisPairGapRotatedSourcePacket d T a)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    DifferentiableOn ℂ (P.branch OS lgc) {z : ℂ | 0 < z.re} :=
  P.packet.branch_differentiableOn OS lgc

end OSIIAxisPairGapRotatedSourcePacket

/-- A coherent family of physical semigroup packets indexed by both
chronological gap and signed axis-pair direction.

The packet arities may vary with the selected gap. The coherence and
real-edge fields are scalar, so packets with different dependent arities can
still assemble into one interleaved flat cross. -/
structure OSIIAxisPairMultiGapSemigroupPacketFamily
    (d k : ℕ) [NeZero d] [NeZero k] (T : ℝ)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) where
  packet :
    (Fin k → osiiAxisPairIndex d → ℝ) →
      (q : osiiAxisPairMultiGapIndex d k) →
        OSIIAxisPairGapRotatedSourcePacket d T q.2
  realEdge :
    (Fin k → osiiAxisPairIndex d → ℝ) → ℂ
  packet_logBranch_congr_of_eq_off_selected :
    ∀ {x y : Fin k → osiiAxisPairIndex d → ℝ} q,
      (∀ p, p ≠ q → x p.1 p.2 = y p.1 p.2) →
        (fun r : Fin k → osiiAxisPairIndex d → ℂ =>
          (packet x q).branch OS lgc (Complex.exp (r q.1 q.2))) =
        (fun r : Fin k → osiiAxisPairIndex d → ℂ =>
          (packet y q).branch OS lgc (Complex.exp (r q.1 q.2)))
  packet_real_edge :
    ∀ x q,
      (packet x q).branch OS lgc
          (osiiAxisPairPositiveCoefficients (x q.1) q.2 : ℂ) =
        realEdge x

namespace OSIIAxisPairMultiGapSemigroupPacketFamily

/-- Build a dependent multi-gap packet family from ordinary positive-time
sources which may vary with the frozen real base.

The source congruence hypotheses express the genuine frozen-base condition:
after selecting `(gap, direction)`, both block sources depend only on the
off-selected coefficients. The constructor discharges the remaining packet
coherence using the exact frozen-translation algebra. Thus a physical
producer only has to prove the displayed common Schwinger-edge identity. -/
noncomputable def ofRotatedPositiveFrozenDependent
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (T : ℝ) (hT : 1 < T)
    (left :
      (Fin k → osiiAxisPairIndex d → ℝ) →
        (q : osiiAxisPairMultiGapIndex d k) →
          SchwartzNPoint d (osiiChronologicalGapLeftArity q.1))
    (hleft :
      ∀ x q,
        tsupport
            (left x q :
              NPointDomain d (osiiChronologicalGapLeftArity q.1) → ℂ) ⊆
          OrderedPositiveTimeRegion d
            (osiiChronologicalGapLeftArity q.1))
    (right :
      (Fin k → osiiAxisPairIndex d → ℝ) →
        (q : osiiAxisPairMultiGapIndex d k) →
          SchwartzNPoint d (osiiChronologicalGapRightArity q.1))
    (hright :
      ∀ x q,
        tsupport
            (right x q :
              NPointDomain d (osiiChronologicalGapRightArity q.1) → ℂ) ⊆
          OrderedPositiveTimeRegion d
            (osiiChronologicalGapRightArity q.1))
    (hleft_congr :
      ∀ {x y : Fin k → osiiAxisPairIndex d → ℝ} q,
        (∀ p, p ≠ q → x p.1 p.2 = y p.1 p.2) →
          left x q = left y q)
    (hright_congr :
      ∀ {x y : Fin k → osiiAxisPairIndex d → ℝ} q,
        (∀ p, p ≠ q → x p.1 p.2 = y p.1 p.2) →
          right x q = right y q)
    (realEdge :
      (Fin k → osiiAxisPairIndex d → ℝ) → ℂ)
    (hrealEdge :
      ∀ x q,
        OS.S
            (osiiChronologicalGapLeftArity q.1 +
              osiiChronologicalGapRightArity q.1)
            (ZeroDiagonalSchwartz.ofClassical
              ((left x q).osConjTensorProduct
                (translateSchwartzNPoint (d := d)
                  ((osiiAxisPairRotationData T q.2).matrix.mulVec
                    (∑ b : osiiAxisPairIndex d,
                      osiiAxisPairPositiveCoefficients (x q.1) b •
                        osiiAxisPairDir (d := d) T b))
                  (right x q)))) =
          realEdge x) :
    OSIIAxisPairMultiGapSemigroupPacketFamily d k T OS lgc where
  packet := fun x q =>
    { leftArity := osiiChronologicalGapLeftArity q.1
      rightArity := osiiChronologicalGapRightArity q.1
      packet :=
        OSIIAxisPairRotatedSourcePacket.ofRotatedPositiveFrozen
          T hT
          (osiiAxisPairPositiveCoefficients (x q.1))
          (fun b =>
            le_of_lt
              (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
          q.2 (left x q) (hleft x q) (right x q) (hright x q) }
  realEdge := realEdge
  packet_logBranch_congr_of_eq_off_selected := by
    intro x y q hxy
    have hleft_xy : left x q = left y q :=
      hleft_congr q hxy
    have hright_xy : right x q = right y q :=
      hright_congr q hxy
    have hcoeff :
        ∀ b, b ≠ q.2 →
          osiiAxisPairPositiveCoefficients (x q.1) b =
            osiiAxisPairPositiveCoefficients (y q.1) b := by
      intro b hb
      change Real.exp (x q.1 b) = Real.exp (y q.1 b)
      rw [hxy (q.1, b) (by
        intro h
        exact hb (congrArg Prod.snd h))]
    let P :=
      OSIIAxisPairRotatedSourcePacket.ofRotatedPositiveFrozen
        T hT
        (osiiAxisPairPositiveCoefficients (x q.1))
        (fun b =>
          le_of_lt
            (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
        q.2 (left x q) (hleft x q) (right x q) (hright x q)
    let Q :=
      OSIIAxisPairRotatedSourcePacket.ofRotatedPositiveFrozen
        T hT
        (osiiAxisPairPositiveCoefficients (y q.1))
        (fun b =>
          le_of_lt
            (osiiAxisPairPositiveCoefficients_pos (y q.1) b))
        q.2 (left y q) (hleft y q) (right y q) (hright y q)
    have hPleft : P.left = Q.left := by
      dsimp [P, Q, OSIIAxisPairRotatedSourcePacket.ofRotatedPositiveFrozen,
        OSIIAxisPairRotatedSourcePacket.ofRotatedPositive]
      rw [hleft_xy]
    have hPright : P.right = Q.right := by
      dsimp [P, Q, OSIIAxisPairRotatedSourcePacket.ofRotatedPositiveFrozen,
        OSIIAxisPairRotatedSourcePacket.ofRotatedPositive]
      rw [hright_xy,
        osiiAxisPairFrozenTranslation_congr_of_eq_off_selected T q.2 hcoeff]
    have hbranch :=
      OSIIAxisPairRotatedSourcePacket.branch_eq_of_source_eq
        P Q hPleft hPright OS lgc
    funext r
    exact congrFun hbranch (Complex.exp (r q.1 q.2))
  packet_real_edge := by
    intro x q
    exact
      (OSIIAxisPairRotatedSourcePacket.ofRotatedPositiveFrozen_branch_selected_eq_schwinger
        OS lgc T hT
        (osiiAxisPairPositiveCoefficients (x q.1))
        (fun b =>
          le_of_lt
            (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
        q.2
        (osiiAxisPairPositiveCoefficients_pos (x q.1) q.2)
        (left x q) (hleft x q) (right x q) (hright x q)).trans
        (hrealEdge x q)

/-- Build a dependent multi-gap packet family directly in the original
Euclidean coordinates.

Unlike `ofRotatedPositiveFrozenDependent`, this constructor uses compensated
left packets. Its selected real source is therefore exactly
`commonRealSource`, with no residual selected-frame rotation. This is the
appropriate interface for chronological product sources whose split
reconstruction is proved in the original coordinates. -/
noncomputable def ofCompensatedFrozenDependent
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (T : ℝ) (hT : 1 < T)
    (left :
      (Fin k → osiiAxisPairIndex d → ℝ) →
        (q : osiiAxisPairMultiGapIndex d k) →
          SchwartzNPoint d (osiiChronologicalGapLeftArity q.1))
    (hleft :
      ∀ x q,
        tsupport
            (left x q :
              NPointDomain d (osiiChronologicalGapLeftArity q.1) → ℂ) ⊆
          osiiEuclideanRotationOrderedNegativeTimeRegion
            (d := d)
            (n := osiiChronologicalGapLeftArity q.1)
            (osiiAxisPairRotationData T q.2).matrix)
    (right :
      (Fin k → osiiAxisPairIndex d → ℝ) →
        (q : osiiAxisPairMultiGapIndex d k) →
          SchwartzNPoint d (osiiChronologicalGapRightArity q.1))
    (hright :
      ∀ x q,
        tsupport
            (right x q :
              NPointDomain d (osiiChronologicalGapRightArity q.1) → ℂ) ⊆
          osiiEuclideanRotationOrderedPositiveTimeRegion
            (d := d)
            (n := osiiChronologicalGapRightArity q.1)
            (osiiAxisPairRotationData T q.2).matrix)
    (hleft_congr :
      ∀ {x y : Fin k → osiiAxisPairIndex d → ℝ} q,
        (∀ p, p ≠ q → x p.1 p.2 = y p.1 p.2) →
          left x q = left y q)
    (hright_congr :
      ∀ {x y : Fin k → osiiAxisPairIndex d → ℝ} q,
        (∀ p, p ≠ q → x p.1 p.2 = y p.1 p.2) →
          right x q = right y q)
    (realEdge :
      (Fin k → osiiAxisPairIndex d → ℝ) → ℂ)
    (hrealEdge :
      ∀ x q,
        OS.S
            (osiiChronologicalGapLeftArity q.1 +
              osiiChronologicalGapRightArity q.1)
            (ZeroDiagonalSchwartz.ofClassical
              (OSIIAxisPairRotatedSourcePacket.commonRealSource
                T (osiiAxisPairPositiveCoefficients (x q.1))
                (left x q) (right x q))) =
          realEdge x) :
    OSIIAxisPairMultiGapSemigroupPacketFamily d k T OS lgc where
  packet := fun x q =>
    { leftArity := osiiChronologicalGapLeftArity q.1
      rightArity := osiiChronologicalGapRightArity q.1
      packet :=
        OSIIAxisPairRotatedSourcePacket.compensatedFrozen
          T hT
          (osiiAxisPairPositiveCoefficients (x q.1))
          (fun b =>
            le_of_lt
              (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
          q.2 (left x q) (hleft x q) (right x q) (hright x q) }
  realEdge := realEdge
  packet_logBranch_congr_of_eq_off_selected := by
    intro x y q hxy
    have hleft_xy : left x q = left y q :=
      hleft_congr q hxy
    have hright_xy : right x q = right y q :=
      hright_congr q hxy
    have hcoeff :
        ∀ b, b ≠ q.2 →
          osiiAxisPairPositiveCoefficients (x q.1) b =
            osiiAxisPairPositiveCoefficients (y q.1) b := by
      intro b hb
      change Real.exp (x q.1 b) = Real.exp (y q.1 b)
      rw [hxy (q.1, b) (by
        intro h
        exact hb (congrArg Prod.snd h))]
    let P :=
      OSIIAxisPairRotatedSourcePacket.compensatedFrozen
        T hT
        (osiiAxisPairPositiveCoefficients (x q.1))
        (fun b =>
          le_of_lt
            (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
        q.2 (left x q) (hleft x q) (right x q) (hright x q)
    let Q :=
      OSIIAxisPairRotatedSourcePacket.compensatedFrozen
        T hT
        (osiiAxisPairPositiveCoefficients (y q.1))
        (fun b =>
          le_of_lt
            (osiiAxisPairPositiveCoefficients_pos (y q.1) b))
        q.2 (left y q) (hleft y q) (right y q) (hright y q)
    have hPleft : P.left = Q.left := by
      dsimp [P, Q, OSIIAxisPairRotatedSourcePacket.compensatedFrozen,
        OSIIAxisPairRotatedSourcePacket.compensatedLeft]
      rw [hleft_xy]
    have hPright : P.right = Q.right := by
      dsimp [P, Q, OSIIAxisPairRotatedSourcePacket.compensatedFrozen,
        OSIIAxisPairRotatedSourcePacket.compensatedLeft]
      rw [hright_xy,
        osiiAxisPairFrozenTranslation_congr_of_eq_off_selected T q.2 hcoeff]
    have hbranch :=
      OSIIAxisPairRotatedSourcePacket.branch_eq_of_source_eq
        P Q hPleft hPright OS lgc
    funext r
    exact congrFun hbranch (Complex.exp (r q.1 q.2))
  packet_real_edge := by
    intro x q
    exact
      (OSIIAxisPairRotatedSourcePacket.compensatedFrozen_branch_selected_eq_common_schwinger
        OS lgc T hT
        (osiiAxisPairPositiveCoefficients (x q.1))
        (fun b =>
          le_of_lt
            (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
        q.2
        (osiiAxisPairPositiveCoefficients_pos (x q.1) q.2)
        (left x q) (hleft x q) (right x q) (hright x q)).trans
        (hrealEdge x q)

/-- Log-coordinate branch associated to one selected gap and direction. -/
def logBranch
    (F : OSIIAxisPairMultiGapSemigroupPacketFamily d k T OS lgc)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    (Fin k → osiiAxisPairIndex d → ℂ) → ℂ :=
  fun r =>
    (F.packet x q).branch OS lgc (Complex.exp (r q.1 q.2))

/-- Packet semigroup holomorphy promotes to the selected interleaved
logarithmic strip. -/
theorem logBranch_differentiableOn
    (F : OSIIAxisPairMultiGapSemigroupPacketFamily d k T OS lgc)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    DifferentiableOn ℂ (F.logBranch x q)
      (osiiAxisPairMultiGapCoordinateLogStrip q) := by
  let eval :
      (Fin k → osiiAxisPairIndex d → ℂ) →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj
      (R := ℂ) (ι := osiiAxisPairIndex d)
      (φ := fun _ => ℂ) q.2).comp
        (ContinuousLinearMap.proj
          (R := ℂ) (ι := Fin k)
          (φ := fun _ => osiiAxisPairIndex d → ℂ) q.1)
  have heval :
      Differentiable ℂ
        (fun r : Fin k → osiiAxisPairIndex d → ℂ =>
          r q.1 q.2) := by
    exact eval.differentiable
  have hexp :
      DifferentiableOn ℂ
        (fun r : Fin k → osiiAxisPairIndex d → ℂ =>
          Complex.exp (r q.1 q.2))
        (osiiAxisPairMultiGapCoordinateLogStrip q) :=
    (Complex.differentiable_exp.comp heval).differentiableOn
  exact
    ((F.packet x q).branch_differentiableOn OS lgc).comp hexp
      (fun _r hr => osiiAxisPair_exp_apply_mem_rightHalfPlane hr)

/-- The packet-family coherence field is exactly the nested log-branch
coherence required by the multi-gap cross. -/
theorem logBranch_congr_of_eq_off_selected
    (F : OSIIAxisPairMultiGapSemigroupPacketFamily d k T OS lgc)
    {x y : Fin k → osiiAxisPairIndex d → ℝ}
    (q : osiiAxisPairMultiGapIndex d k)
    (hxy : ∀ p, p ≠ q → x p.1 p.2 = y p.1 p.2) :
    F.logBranch x q = F.logBranch y q :=
  F.packet_logBranch_congr_of_eq_off_selected q hxy

/-- The nested logarithmic real point evaluates to the packet family's common
Schwinger edge. -/
theorem logBranch_real_edge
    (F : OSIIAxisPairMultiGapSemigroupPacketFamily d k T OS lgc)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    F.logBranch x q (osiiAxisPairSimultaneousLogRealEmbed x) =
      F.realEdge x := by
  change
    (F.packet x q).branch OS lgc (Complex.exp (x q.1 q.2)) =
      F.realEdge x
  rw [← Complex.ofReal_exp]
  exact F.packet_real_edge x q

/-- Forget the dependent packet realization and retain the exact interleaved
flat-cross data consumed by the multi-gap MZ theorem. -/
def toFlatCrossData
    (F : OSIIAxisPairMultiGapSemigroupPacketFamily d k T OS lgc)
    (hpacket :
      ∀ q : osiiAxisPairMultiGapIndex d k,
        ContinuousOn
          (fun p :
              (Fin k → osiiAxisPairIndex d → ℝ) × ℂ =>
            (F.packet p.1 q).branch OS lgc (Complex.exp p.2))
          (Set.univ ×ˢ {w : ℂ | |w.im| < Real.pi / 2})) :
    OSIIAxisPairMultiGapFlatCrossData d k where
  branch := F.logBranch
  realEdge := F.realEdge
  branch_differentiableOn := F.logBranch_differentiableOn
  branch_congr_of_eq_off_selected :=
    F.logBranch_congr_of_eq_off_selected
  branch_real_edge := F.logBranch_real_edge
  chart_continuous := by
    intro q
    simpa [logBranch, osiiAxisPairMultiGapUpdate] using hpacket q

end OSIIAxisPairMultiGapSemigroupPacketFamily

namespace OSIIAxisPairMultiGapFlatCrossData

/-- Compensated positive-time source packets assemble directly into the
existing multi-gap flat cross under the original OS axioms. The genuine
packet branches do not pass through the legacy growth-indexed family. -/
noncomputable def ofCompensatedFrozenDependentOfOS
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ) (hT : 1 < T)
    (left :
      (Fin k → osiiAxisPairIndex d → ℝ) →
        (q : osiiAxisPairMultiGapIndex d k) →
          SchwartzNPoint d (osiiChronologicalGapLeftArity q.1))
    (hleft :
      ∀ x q,
        tsupport
            (left x q :
              NPointDomain d (osiiChronologicalGapLeftArity q.1) → ℂ) ⊆
          osiiEuclideanRotationOrderedNegativeTimeRegion
            (d := d)
            (n := osiiChronologicalGapLeftArity q.1)
            (osiiAxisPairRotationData T q.2).matrix)
    (right :
      (Fin k → osiiAxisPairIndex d → ℝ) →
        (q : osiiAxisPairMultiGapIndex d k) →
          SchwartzNPoint d (osiiChronologicalGapRightArity q.1))
    (hright :
      ∀ x q,
        tsupport
            (right x q :
              NPointDomain d (osiiChronologicalGapRightArity q.1) → ℂ) ⊆
          osiiEuclideanRotationOrderedPositiveTimeRegion
            (d := d)
            (n := osiiChronologicalGapRightArity q.1)
            (osiiAxisPairRotationData T q.2).matrix)
    (hleft_congr :
      ∀ {x y : Fin k → osiiAxisPairIndex d → ℝ} q,
        (∀ p, p ≠ q → x p.1 p.2 = y p.1 p.2) →
          left x q = left y q)
    (hright_congr :
      ∀ {x y : Fin k → osiiAxisPairIndex d → ℝ} q,
        (∀ p, p ≠ q → x p.1 p.2 = y p.1 p.2) →
          right x q = right y q)
    (realEdge :
      (Fin k → osiiAxisPairIndex d → ℝ) → ℂ)
    (hrealEdge :
      ∀ x q,
        OS.S
            (osiiChronologicalGapLeftArity q.1 +
              osiiChronologicalGapRightArity q.1)
            (ZeroDiagonalSchwartz.ofClassical
              (OSIIAxisPairRotatedSourcePacket.commonRealSource
                T (osiiAxisPairPositiveCoefficients (x q.1))
                (left x q) (right x q))) =
          realEdge x)
    (hpacket :
      ∀ q : osiiAxisPairMultiGapIndex d k,
        ContinuousOn
          (fun p :
              (Fin k → osiiAxisPairIndex d → ℝ) × ℂ =>
            (OSIIAxisPairRotatedSourcePacket.compensatedFrozen
              T hT
              (osiiAxisPairPositiveCoefficients (p.1 q.1))
              (fun b =>
                le_of_lt
                  (osiiAxisPairPositiveCoefficients_pos (p.1 q.1) b))
              q.2 (left p.1 q) (hleft p.1 q)
              (right p.1 q) (hright p.1 q)).branchOfOS
                OS (Complex.exp p.2))
          (Set.univ ×ˢ {w : ℂ | |w.im| < Real.pi / 2})) :
    OSIIAxisPairMultiGapFlatCrossData d k := by
  let packet := fun (x : Fin k → osiiAxisPairIndex d → ℝ)
      (q : osiiAxisPairMultiGapIndex d k) =>
    OSIIAxisPairRotatedSourcePacket.compensatedFrozen
      T hT
      (osiiAxisPairPositiveCoefficients (x q.1))
      (fun b =>
        le_of_lt
          (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
      q.2 (left x q) (hleft x q) (right x q) (hright x q)
  refine {
    branch := fun x q r =>
      (packet x q).branchOfOS OS (Complex.exp (r q.1 q.2))
    realEdge := realEdge
    branch_differentiableOn := ?_
    branch_congr_of_eq_off_selected := ?_
    branch_real_edge := ?_
    chart_continuous := ?_ }
  · intro x q
    let eval :
        (Fin k → osiiAxisPairIndex d → ℂ) →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj
        (R := ℂ) (ι := osiiAxisPairIndex d)
        (φ := fun _ => ℂ) q.2).comp
          (ContinuousLinearMap.proj
            (R := ℂ) (ι := Fin k)
            (φ := fun _ => osiiAxisPairIndex d → ℂ) q.1)
    have heval :
        Differentiable ℂ
          (fun r : Fin k → osiiAxisPairIndex d → ℂ =>
            r q.1 q.2) := by
      exact eval.differentiable
    exact
      ((packet x q).branchOfOS_differentiableOn OS).comp
        (Complex.differentiable_exp.comp heval).differentiableOn
        (fun _r hr => osiiAxisPair_exp_apply_mem_rightHalfPlane hr)
  · intro x y q hxy
    have hleft_xy : left x q = left y q := hleft_congr q hxy
    have hright_xy : right x q = right y q := hright_congr q hxy
    have hcoeff :
        ∀ b, b ≠ q.2 →
          osiiAxisPairPositiveCoefficients (x q.1) b =
            osiiAxisPairPositiveCoefficients (y q.1) b := by
      intro b hb
      change Real.exp (x q.1 b) = Real.exp (y q.1 b)
      rw [hxy (q.1, b) (by
        intro h
        exact hb (congrArg Prod.snd h))]
    have hPleft : (packet x q).left = (packet y q).left := by
      dsimp [packet, OSIIAxisPairRotatedSourcePacket.compensatedFrozen,
        OSIIAxisPairRotatedSourcePacket.compensatedLeft]
      rw [hleft_xy]
    have hPright : (packet x q).right = (packet y q).right := by
      dsimp [packet, OSIIAxisPairRotatedSourcePacket.compensatedFrozen,
        OSIIAxisPairRotatedSourcePacket.compensatedLeft]
      rw [hright_xy,
        osiiAxisPairFrozenTranslation_congr_of_eq_off_selected T q.2 hcoeff]
    have hbranch :=
      OSIIAxisPairRotatedSourcePacket.branchOfOS_eq_of_source_eq
        (packet x q) (packet y q) hPleft hPright OS
    funext r
    exact congrFun hbranch (Complex.exp (r q.1 q.2))
  · intro x q
    have hedge :=
      OSIIAxisPairRotatedSourcePacket.compensatedFrozen_branchOfOS_selected_eq_common_schwinger
        OS T hT
        (osiiAxisPairPositiveCoefficients (x q.1))
        (fun b =>
          le_of_lt
            (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
        q.2
        (osiiAxisPairPositiveCoefficients_pos (x q.1) q.2)
        (left x q) (hleft x q) (right x q) (hright x q)
    simpa [packet, osiiAxisPairSimultaneousLogRealEmbed,
      osiiAxisPairLogRealEmbed, osiiAxisPairPositiveCoefficients] using
      hedge.trans (hrealEdge x q)
  · intro q
    simpa [packet, osiiAxisPairMultiGapUpdate] using hpacket q

end OSIIAxisPairMultiGapFlatCrossData

namespace OSIIAxisPairMultiGapSourcewiseFlatCrossData

end OSIIAxisPairMultiGapSourcewiseFlatCrossData

end OSReconstruction
