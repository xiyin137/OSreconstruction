/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairParametricBranch
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSpatialMomentum
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceOrderedDensity
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceWitness
import OSReconstruction.SCV.EuclideanWeylFrechet










noncomputable section

open Set
open scoped Classical

namespace OSReconstruction

variable {d n : ℕ} [NeZero d]

omit [NeZero d] in
/-- A temporal margin and a global norm bound imply positivity in one
axis-pair frame once its slope dominates the worst spatial difference. -/
theorem OSIIAxisPairRotationData.mem_orderedPositive_of_margin_norm
    (D : OSIIAxisPairRotationData (d := d) T a)
    {δ C : ℝ}
    (hδ : 0 < δ)
    (hC : 0 ≤ C)
    (hT : 2 * C / δ < T)
    (x : NPointDomain d n)
    (htime : ∀ i : Fin n, δ ≤ x i 0)
    (hgap : ∀ i j : Fin n, i < j → δ ≤ x j 0 - x i 0)
    (hnorm : ‖x‖ ≤ C) :
    x ∈ osiiEuclideanRotationOrderedPositiveTimeRegion
      (d := d) (n := n) D.matrix := by
  have hTδ : 2 * C < T * δ := (div_lt_iff₀ hδ).mp hT
  have hcoord (i : Fin n) :
      |x i (Fin.succ a.1)| ≤ C := by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm (x i) (Fin.succ a.1)).trans
      ((norm_le_pi_norm x i).trans hnorm)
  intro i
  constructor
  · change 0 < (D.matrix.mulVec (x i)) 0
    rw [D.mulVec_time]
    apply mul_pos (inv_pos.mpr (osiiAxisPairRadius_pos T))
    have hi := htime i
    have hisp := abs_le.mp (hcoord i)
    cases a.2 <;> simp only [Bool.false_eq_true, if_false, if_true] <;> nlinarith
  · intro j hij
    change (D.matrix.mulVec (x i)) 0 < (D.matrix.mulVec (x j)) 0
    rw [D.mulVec_time, D.mulVec_time]
    rw [mul_lt_mul_iff_right₀ (inv_pos.mpr (osiiAxisPairRadius_pos T))]
    have hijt := hgap i j hij
    have hisp := abs_le.mp (hcoord i)
    have hjsp := abs_le.mp (hcoord j)
    cases a.2 <;> simp only [Bool.false_eq_true, if_false, if_true] <;> nlinarith

private def spatialPart (v : SpacetimeDim d) : Fin d → ℝ :=
  fun i => v (Fin.succ i)

private theorem time_spatial_decomposition (v : SpacetimeDim d) :
    timeShiftVec d (v 0) + Fin.cons 0 (spatialPart v) = v := by
  ext μ
  refine Fin.cases ?_ ?_ μ
  · simp [timeShiftVec]
  · intro i
    simp [timeShiftVec, spatialPart]

private theorem translate_time_spatial (v : SpacetimeDim d)
    (f : SchwartzNPoint d n) :
    translateSchwartzNPoint (d := d) v f =
      translateSchwartzNPoint (d := d) (Fin.cons 0 (spatialPart v))
        (timeShiftSchwartzNPoint (d := d) (v 0) f) := by
  ext x
  simp only [translateSchwartzNPoint_apply, timeShiftSchwartzNPoint_apply]
  apply congrArg f
  funext i μ
  simp only [Pi.sub_apply]
  have hdec := congrFun (time_spatial_decomposition v) μ
  simp only [Pi.add_apply] at hdec
  rw [← hdec]
  ring

private theorem timeShiftHilbert_single_eq
    (OS : OsterwalderSchraderAxioms d)
    (f : SchwartzNPoint d n)
    (hf : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (t : ℝ) (ht : 0 < t) :
    osTimeShiftHilbertOfOS (d := d) OS t ht
        (osiiPositiveTimeSingleVectorCLM OS n ⟨f, hf⟩) =
      osiiPositiveTimeSingleVectorCLM OS n
        ⟨timeShiftSchwartzNPoint (d := d) t f,
          timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport
            (d := d) t ht f hf⟩ := by
  rw [osiiPositiveTimeSingleVectorCLM_apply, osTimeShiftHilbertOfOS_coe]
  apply congrArg (fun x : OSPreHilbertSpace OS => (x : OSHilbertSpace OS))
  apply OSPreHilbertSpace.mk_eq_of_funcs_eq
  intro k
  by_cases hk : k = n
  · subst k
    simp [osTimeShiftLinear, osTimeShift,
      PositiveTimeBorchersSequence.single_toBorchersSequence,
      BorchersSequence.single]
  · simp [osTimeShiftLinear, osTimeShift,
      PositiveTimeBorchersSequence.single_toBorchersSequence,
      BorchersSequence.single, hk]

private theorem norm_osSpatialTranslateHilbert_eq
    (OS : OsterwalderSchraderAxioms d)
    (a : Fin d → ℝ) (x : OSHilbertSpace OS) :
    ‖osSpatialTranslateHilbert (d := d) OS a x‖ = ‖x‖ := by
  have hsq :
      ‖osSpatialTranslateHilbert (d := d) OS a x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ),
      osSpatialTranslateHilbert_inner_eq,
      inner_self_eq_norm_sq]
  nlinarith [norm_nonneg (osSpatialTranslateHilbert (d := d) OS a x),
    norm_nonneg x]

/-- Translating an ordered-positive source by a spacetime vector with
nonnegative time component cannot increase its original-OS Hilbert norm. -/
theorem norm_osiiPositiveTimeSingleVectorCLM_translate_le
    (OS : OsterwalderSchraderAxioms d)
    (f : SchwartzNPoint d n)
    (hf : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (v : SpacetimeDim d) (hv : 0 ≤ v 0) :
    ‖osiiPositiveTimeSingleVectorCLM OS n
        ⟨translateSchwartzNPoint (d := d) v f,
          osiiEuclideanTranslation_preserves_orderedPositive v hv f hf⟩‖ ≤
      ‖osiiPositiveTimeSingleVectorCLM OS n ⟨f, hf⟩‖ := by
  by_cases ht0 : v 0 = 0
  · have hv_spatial : v = Fin.cons 0 (spatialPart v) := by
      ext μ
      refine Fin.cases ?_ ?_ μ
      · simpa [ht0]
      · intro i
        simp [spatialPart]
    have hsource :
        translateSchwartzNPoint (d := d) v f =
          translateSchwartzNPoint (d := d)
            (Fin.cons 0 (spatialPart v)) f := by
      exact congrArg (fun w => translateSchwartzNPoint (d := d) w f) hv_spatial
    have hvec :
        osiiPositiveTimeSingleVectorCLM OS n
            ⟨translateSchwartzNPoint (d := d) v f,
              osiiEuclideanTranslation_preserves_orderedPositive v hv f hf⟩ =
          osSpatialTranslateHilbert (d := d) OS (spatialPart v)
            (osiiPositiveTimeSingleVectorCLM OS n ⟨f, hf⟩) := by
      let g : euclideanPositiveTimeSubmodule (d := d) n :=
        ⟨translateSchwartzNPoint (d := d) v f,
          osiiEuclideanTranslation_preserves_orderedPositive v hv f hf⟩
      let gSpatial : euclideanPositiveTimeSubmodule (d := d) n :=
        ⟨translateSchwartzNPoint (d := d) (Fin.cons 0 (spatialPart v)) f,
          translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
            (d := d) (Fin.cons 0 (spatialPart v)) (by simp) f hf⟩
      have hg : g = gSpatial := Subtype.ext hsource
      rw [show osiiPositiveTimeSingleVectorCLM OS n
          ⟨translateSchwartzNPoint (d := d) v f,
            osiiEuclideanTranslation_preserves_orderedPositive v hv f hf⟩ =
          osiiPositiveTimeSingleVectorCLM OS n gSpatial from
        congrArg (osiiPositiveTimeSingleVectorCLM OS n) hg]
      simpa [gSpatial, osiiPositiveTimeSingleVectorCLM_apply] using
        (osSpatialTranslateHilbert_single_eq
          (d := d) OS f hf (spatialPart v)).symm
    rw [hvec, norm_osSpatialTranslateHilbert_eq]
  · have ht : 0 < v 0 := lt_of_le_of_ne hv (Ne.symm ht0)
    let ft := timeShiftSchwartzNPoint (d := d) (v 0) f
    let hft :
        tsupport (ft : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n :=
      timeShiftSchwartzNPoint_preserves_ordered_positive_tsupport
        (d := d) (v 0) ht f hf
    have hvec :
        osiiPositiveTimeSingleVectorCLM OS n
            ⟨translateSchwartzNPoint (d := d) v f,
              osiiEuclideanTranslation_preserves_orderedPositive v hv f hf⟩ =
          osSpatialTranslateHilbert (d := d) OS (spatialPart v)
            (osiiPositiveTimeSingleVectorCLM OS n ⟨ft, hft⟩) := by
      let g : euclideanPositiveTimeSubmodule (d := d) n :=
        ⟨translateSchwartzNPoint (d := d) v f,
          osiiEuclideanTranslation_preserves_orderedPositive v hv f hf⟩
      let gSpatial : euclideanPositiveTimeSubmodule (d := d) n :=
        ⟨translateSchwartzNPoint (d := d) (Fin.cons 0 (spatialPart v)) ft,
          translateSchwartzNPoint_preserves_ordered_positive_tsupport_spatial
            (d := d) (Fin.cons 0 (spatialPart v)) (by simp) ft hft⟩
      have hg : g = gSpatial := Subtype.ext (by
        simpa [g, gSpatial, ft] using translate_time_spatial v f)
      rw [show osiiPositiveTimeSingleVectorCLM OS n
          ⟨translateSchwartzNPoint (d := d) v f,
            osiiEuclideanTranslation_preserves_orderedPositive v hv f hf⟩ =
          osiiPositiveTimeSingleVectorCLM OS n gSpatial from
        congrArg (osiiPositiveTimeSingleVectorCLM OS n) hg]
      simpa [gSpatial, osiiPositiveTimeSingleVectorCLM_apply] using
        (osSpatialTranslateHilbert_single_eq
          (d := d) OS ft hft (spatialPart v)).symm
    rw [hvec, norm_osSpatialTranslateHilbert_eq]
    rw [← timeShiftHilbert_single_eq OS f hf (v 0) ht]
    exact osTimeShiftHilbertOfOS_contraction (d := d) OS (v 0) ht _

/-- A packet built from ordinary positive-time sources is exactly the standard
Hilbert semigroup pairing after the rotate/unrotate maps cancel. -/
theorem OSIIAxisPairRotatedSourcePacket.ofRotatedPositive_branch_eq_holomorphicValue
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (T : ℝ) (a : osiiAxisPairIndex d)
    (left : SchwartzNPoint d n)
    (hleft :
      tsupport (left : NPointDomain d n → ℂ) ⊆
        OrderedPositiveTimeRegion d n)
    (right : SchwartzNPoint d m)
    (hright :
      tsupport (right : NPointDomain d m → ℂ) ⊆
        OrderedPositiveTimeRegion d m)
    (z : ℂ) :
    (OSIIAxisPairRotatedSourcePacket.ofRotatedPositive
        T a left hleft right hright).branch OS lgc z =
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n left hleft)
        (PositiveTimeBorchersSequence.single m right hright)
        ((osiiAxisPairRadius T : ℂ) * z) := by
  simp [OSIIAxisPairRotatedSourcePacket.branch,
    osiiAxisPairCanonicalRotatedSemigroupBranch,
    osiiAxisPairRotatedSemigroupBranch,
    OSIIAxisPairRotatedSourcePacket.ofRotatedPositive,
    osiiEuclideanRotatePositiveTimeSingle]

/-- A frozen ordinary-positive packet is uniformly bounded independently of
all inactive axis-pair coefficients. -/
theorem OSIIAxisPairRotatedSourcePacket.norm_ofRotatedPositiveFrozen_branchOfOS_le
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ) (hT : 1 < T)
    (c : osiiAxisPairIndex d → ℝ)
    (hc : ∀ b, 0 ≤ c b)
    (a : osiiAxisPairIndex d)
    (left : SchwartzNPoint d n)
    (hleft :
      tsupport (left : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (right : SchwartzNPoint d m)
    (hright :
      tsupport (right : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m)
    (z : ℂ) (hz : 0 < z.re) :
    ‖(OSIIAxisPairRotatedSourcePacket.ofRotatedPositiveFrozen
        T hT c hc a left hleft right hright).branchOfOS OS z‖ ≤
      ‖osiiPositiveTimeSingleVectorCLM OS n ⟨left, hleft⟩‖ *
        ‖osiiPositiveTimeSingleVectorCLM OS m ⟨right, hright⟩‖ := by
  let v : SpacetimeDim d :=
    (osiiAxisPairRotationData T a).matrix.mulVec
      (osiiAxisPairFrozenTranslation (d := d) T c a)
  have hv : 0 ≤ v 0 :=
    (osiiAxisPairRotationData T a).mulVec_frozenTranslation_time_nonneg
      hT c hc
  let shiftedRight : euclideanPositiveTimeSubmodule (d := d) m :=
    ⟨translateSchwartzNPoint (d := d) v right,
      osiiEuclideanTranslation_preserves_orderedPositive v hv right hright⟩
  let P := OSIIAxisPairRotatedSourcePacket.ofRotatedPositiveFrozen
    T hT c hc a left hleft right hright
  have hpacket :
      ‖P.branchOfOS OS z‖ ≤
        ‖osiiPositiveTimeSingleVectorCLM OS n ⟨left, hleft⟩‖ *
          ‖osiiPositiveTimeSingleVectorCLM OS m shiftedRight‖ := by
    simpa [P, OSIIAxisPairRotatedSourcePacket.ofRotatedPositiveFrozen,
      OSIIAxisPairRotatedSourcePacket.ofRotatedPositive,
      osiiEuclideanRotatePositiveTimeComponent, shiftedRight, v] using
      P.norm_branchOfOS_le OS z hz
  exact hpacket.trans
    (mul_le_mul_of_nonneg_left
      (norm_osiiPositiveTimeSingleVectorCLM_translate_le
        OS right hright v hv)
      (norm_nonneg _))

/-- A compensated frozen packet has the same uniform Hilbert-space bound
after rotating its cone-supported sources into the ordinary time frame. -/
theorem OSIIAxisPairRotatedSourcePacket.norm_compensatedFrozen_branchOfOS_le
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ) (hT : 1 < T)
    (c : osiiAxisPairIndex d → ℝ)
    (hc : ∀ b, 0 ≤ c b)
    (a : osiiAxisPairIndex d)
    (left : SchwartzNPoint d n)
    (hleft :
      tsupport (left : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedNegativeTimeRegion
          (d := d) (n := n) (osiiAxisPairRotationData T a).matrix)
    (right : SchwartzNPoint d m)
    (hright :
      tsupport (right : NPointDomain d m → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion
          (d := d) (n := m) (osiiAxisPairRotationData T a).matrix)
    (z : ℂ) (hz : 0 < z.re) :
    let R := (osiiAxisPairRotationData T a).matrix
    let hR := (osiiAxisPairRotationData T a).orthogonal
    let leftR := (osiiEuclideanRotateSchwartz R hR left).timeReflect
    let rightR := osiiEuclideanRotateSchwartz R hR right
    ‖(OSIIAxisPairRotatedSourcePacket.compensatedFrozen
        T hT c hc a left hleft right hright).branchOfOS OS z‖ ≤
      ‖osiiPositiveTimeSingleVectorCLM OS n
          ⟨leftR, SchwartzNPoint.timeReflect_tsupport_orderedPositive
            (osiiEuclideanRotateSchwartz R hR left)
            (osiiEuclideanRotateSchwartz_tsupport_orderedNegative
              R hR left hleft)⟩‖ *
        ‖osiiPositiveTimeSingleVectorCLM OS m
          ⟨rightR, osiiEuclideanRotateSchwartz_tsupport_orderedPositive
            R hR right hright⟩‖ := by
  dsimp only
  let R := (osiiAxisPairRotationData T a).matrix
  let hR := (osiiAxisPairRotationData T a).orthogonal
  let leftR : SchwartzNPoint d n :=
    (osiiEuclideanRotateSchwartz R hR left).timeReflect
  let rightR : SchwartzNPoint d m :=
    osiiEuclideanRotateSchwartz R hR right
  let hleftR :
      tsupport (leftR : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n :=
    SchwartzNPoint.timeReflect_tsupport_orderedPositive
      (osiiEuclideanRotateSchwartz R hR left)
      (osiiEuclideanRotateSchwartz_tsupport_orderedNegative
        R hR left hleft)
  let hrightR :
      tsupport (rightR : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m :=
    osiiEuclideanRotateSchwartz_tsupport_orderedPositive
      R hR right hright
  let P :=
    OSIIAxisPairRotatedSourcePacket.compensatedFrozen
      T hT c hc a left hleft right hright
  let Q :=
    OSIIAxisPairRotatedSourcePacket.ofRotatedPositiveFrozen
      T hT c hc a leftR hleftR rightR hrightR
  have hleftPQ : P.left = Q.left := by
    simp [P, Q, OSIIAxisPairRotatedSourcePacket.compensatedFrozen,
      OSIIAxisPairRotatedSourcePacket.compensatedLeft,
      OSIIAxisPairRotatedSourcePacket.ofRotatedPositiveFrozen,
      OSIIAxisPairRotatedSourcePacket.ofRotatedPositive,
      leftR, R, osiiEuclideanCompensatedLeftSchwartz]
  have hrightPQ : P.right = Q.right := by
    dsimp [P, Q, OSIIAxisPairRotatedSourcePacket.compensatedFrozen,
      OSIIAxisPairRotatedSourcePacket.compensatedLeft,
      OSIIAxisPairRotatedSourcePacket.ofRotatedPositiveFrozen,
      OSIIAxisPairRotatedSourcePacket.ofRotatedPositive, rightR]
    apply
      (show Function.Injective (osiiEuclideanRotateSchwartz R hR) from by
        intro f g hfg
        have h := congrArg (osiiEuclideanUnrotateSchwartz R hR) hfg
        simpa using h)
    rw [osiiEuclideanRotateSchwartz_translate,
      osiiEuclideanRotateSchwartz_unrotate]
  rw [show P.branchOfOS OS z = Q.branchOfOS OS z from
    congrFun
      (OSIIAxisPairRotatedSourcePacket.branchOfOS_eq_of_source_eq
        P Q hleftPQ hrightPQ OS) z]
  exact
    OSIIAxisPairRotatedSourcePacket.norm_ofRotatedPositiveFrozen_branchOfOS_le
      OS T hT c hc a leftR hleftR rightR hrightR z hz

/-- The old compensated estimate is a coarse compatibility wrapper around
the sharp original-OS reflected-source estimate. -/
theorem OSIIAxisPairRotatedSourcePacket.norm_compensatedFrozen_branch_le
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (T : ℝ) (hT : 1 < T)
    (c : osiiAxisPairIndex d → ℝ)
    (hc : ∀ b, 0 ≤ c b)
    (a : osiiAxisPairIndex d)
    (left : SchwartzNPoint d n)
    (hleft :
      tsupport (left : NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedNegativeTimeRegion
          (d := d) (n := n) (osiiAxisPairRotationData T a).matrix)
    (right : SchwartzNPoint d m)
    (hright :
      tsupport (right : NPointDomain d m → ℂ) ⊆
        osiiEuclideanRotationOrderedPositiveTimeRegion
          (d := d) (n := m) (osiiAxisPairRotationData T a).matrix)
    (z : ℂ) (hz : 0 < z.re) :
    let R := (osiiAxisPairRotationData T a).matrix
    let hR := (osiiAxisPairRotationData T a).orthogonal
    let leftR := (osiiEuclideanRotateSchwartz R hR left).timeReflect
    let rightR := osiiEuclideanRotateSchwartz R hR right
    ‖(OSIIAxisPairRotatedSourcePacket.compensatedFrozen
        T hT c hc a left hleft right hright).branch OS lgc z‖ ≤
      2 * ‖osiiPositiveTimeSingleVectorCLM OS n
          ⟨leftR, SchwartzNPoint.timeReflect_tsupport_orderedPositive
            (osiiEuclideanRotateSchwartz R hR left)
            (osiiEuclideanRotateSchwartz_tsupport_orderedNegative
              R hR left hleft)⟩‖ *
        ‖osiiPositiveTimeSingleVectorCLM OS m
          ⟨rightR, osiiEuclideanRotateSchwartz_tsupport_orderedPositive
            R hR right hright⟩‖ := by
  dsimp only
  let P :=
    OSIIAxisPairRotatedSourcePacket.compensatedFrozen
      T hT c hc a left hleft right hright
  rw [show P.branch OS lgc z = P.branchOfOS OS z from
    P.branch_eq_branchOfOS OS lgc z hz]
  have hsharp :=
    OSIIAxisPairRotatedSourcePacket.norm_compensatedFrozen_branchOfOS_le
      OS T hT c hc a left hleft right hright z hz
  dsimp only at hsharp
  calc
    _ ≤ _ := hsharp
    _ ≤ _ := by nlinarith [norm_nonneg (P.branchOfOS OS z)]

/-- Time reflection converts support positive in every signed axis-pair frame
to support negative in every frame. -/
theorem SchwartzNPoint.timeReflect_tsupport_subset_all_orientedNegative
    (f : SchwartzNPoint d n)
    {T : ℝ}
    (hf :
      ∀ a : osiiAxisPairIndex d,
        tsupport (f : NPointDomain d n → ℂ) ⊆
          osiiEuclideanRotationOrderedPositiveTimeRegion
            (d := d) (n := n) (osiiAxisPairRotationData T a).matrix) :
    ∀ a : osiiAxisPairIndex d,
      tsupport ((f.timeReflect : SchwartzNPoint d n) :
          NPointDomain d n → ℂ) ⊆
        osiiEuclideanRotationOrderedNegativeTimeRegion
          (d := d) (n := n) (osiiAxisPairRotationData T a).matrix := by
  intro a x hx
  have hxpre :
      timeReflectionN d x ∈
        tsupport (f : NPointDomain d n → ℂ) := by
    exact
      tsupport_comp_subset_preimage
        ((f : SchwartzNPoint d n) : NPointDomain d n → ℂ)
        (osiiContinuousTimeReflectionN (d := d) (n := n)) hx
  have hpos := hf (osiiAxisPairOpposite a) hxpre
  intro i
  constructor
  · have hi :
        0 <
          ((osiiAxisPairRotationData T (osiiAxisPairOpposite a)).matrix.mulVec
            (timeReflection d (x i))) 0 := by
      simpa [timeReflectionN] using (hpos i).1
    have hreflect :
        ((osiiAxisPairRotationData T a).matrix.mulVec (x i)) 0 =
          -((osiiAxisPairRotationData T (osiiAxisPairOpposite a)).matrix.mulVec
            (timeReflection d (x i))) 0 := by
      simpa only [timeReflection_timeReflection] using
        osiiAxisPairRotationData_mulVec_timeReflection_eq_neg_opposite
          T a (timeReflection d (x i))
    change ((osiiAxisPairRotationData T a).matrix.mulVec (x i)) 0 < 0
    linarith
  · intro j hij
    have hijpos :
        ((osiiAxisPairRotationData T (osiiAxisPairOpposite a)).matrix.mulVec
            (timeReflection d (x i))) 0 <
          ((osiiAxisPairRotationData T (osiiAxisPairOpposite a)).matrix.mulVec
            (timeReflection d (x j))) 0 := by
      simpa [timeReflectionN] using (hpos i).2 j hij
    have hireflect :
        ((osiiAxisPairRotationData T a).matrix.mulVec (x i)) 0 =
          -((osiiAxisPairRotationData T (osiiAxisPairOpposite a)).matrix.mulVec
            (timeReflection d (x i))) 0 := by
      simpa only [timeReflection_timeReflection] using
        osiiAxisPairRotationData_mulVec_timeReflection_eq_neg_opposite
          T a (timeReflection d (x i))
    have hjreflect :
        ((osiiAxisPairRotationData T a).matrix.mulVec (x j)) 0 =
          -((osiiAxisPairRotationData T (osiiAxisPairOpposite a)).matrix.mulVec
            (timeReflection d (x j))) 0 := by
      simpa only [timeReflection_timeReflection] using
        osiiAxisPairRotationData_mulVec_timeReflection_eq_neg_opposite
          T a (timeReflection d (x j))
    change
      ((osiiAxisPairRotationData T a).matrix.mulVec (x j)) 0 <
        ((osiiAxisPairRotationData T a).matrix.mulVec (x i)) 0
    linarith

/-- A compact all-axis source package keeps the chosen slope together with
the exact source identities needed by downstream real-edge comparisons. -/
structure OSIIAxisPairCompactCommonSourcePackage
    (leftPositive : SchwartzNPoint d n)
    (right : SchwartzNPoint d m) where
  T : ℝ
  hT : 1 < T
  left_compact :
    HasCompactSupport (leftPositive : NPointDomain d n → ℂ)
  right_compact :
    HasCompactSupport (right : NPointDomain d m → ℂ)
  data : OSIIAxisPairCommonSourceData d n m T
  left_eq : data.left = leftPositive.timeReflect
  right_eq : data.right = right

namespace OSIIAxisPairCompactCommonSourcePackage

variable {d n m : ℕ} [NeZero d]
variable {leftPositive : SchwartzNPoint d n} {right : SchwartzNPoint d m}

/-- The coherent semigroup packet family carried by a compact common-source
package. -/
def toSemigroupPacketFamily
    (P : OSIIAxisPairCompactCommonSourcePackage leftPositive right)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    OSIIAxisPairSemigroupPacketFamily d n m P.T OS lgc :=
  P.data.toSemigroupPacketFamily P.hT OS lgc

/-- The explicit Hilbert-vector product controlling one coordinate chart of a
compact common-source flat cross. -/
noncomputable def flatTubeBranchCoordinateChartBound
    (P : OSIIAxisPairCompactCommonSourcePackage leftPositive right)
    (OS : OsterwalderSchraderAxioms d)
    (a : osiiAxisPairIndex d) : ℝ :=
  let R := (osiiAxisPairRotationData P.T a).matrix
  let hR := (osiiAxisPairRotationData P.T a).orthogonal
  let leftR : SchwartzNPoint d n :=
    (osiiEuclideanRotateSchwartz R hR P.data.left).timeReflect
  let rightR : SchwartzNPoint d m :=
    osiiEuclideanRotateSchwartz R hR P.data.right
  let hleftR :
      tsupport (leftR : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n :=
    SchwartzNPoint.timeReflect_tsupport_orderedPositive
      (osiiEuclideanRotateSchwartz R hR P.data.left)
      (osiiEuclideanRotateSchwartz_tsupport_orderedNegative
        R hR P.data.left (P.data.left_support a))
  let hrightR :
      tsupport (rightR : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m :=
    osiiEuclideanRotateSchwartz_tsupport_orderedPositive
      R hR P.data.right (P.data.right_support a)
  2 * ‖osiiPositiveTimeSingleVectorCLM OS n ⟨leftR, hleftR⟩‖ *
    ‖osiiPositiveTimeSingleVectorCLM OS m ⟨rightR, hrightR⟩‖

/-- The explicit chart constant bounds the compact common-source branch,
uniformly in its inactive real base and active strip point. -/
theorem norm_flatTubeBranch_coordinateChart_le
    (P : OSIIAxisPairCompactCommonSourcePackage leftPositive right)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (a : osiiAxisPairIndex d)
    (x : osiiAxisPairIndex d → ℝ) (w : ℂ)
    (hw : |w.im| < Real.pi / 2) :
    ‖(P.toSemigroupPacketFamily OS lgc
      ).toDirectionalBranchFamily.flatTubeBranch
        (Function.update (osiiAxisPairLogRealEmbed x) a w)‖ ≤
      P.flatTubeBranchCoordinateChartBound OS a := by
  let R := (osiiAxisPairRotationData P.T a).matrix
  let hR := (osiiAxisPairRotationData P.T a).orthogonal
  let leftR : SchwartzNPoint d n :=
    (osiiEuclideanRotateSchwartz R hR P.data.left).timeReflect
  let rightR : SchwartzNPoint d m :=
    osiiEuclideanRotateSchwartz R hR P.data.right
  let hleftR :
      tsupport (leftR : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n :=
    SchwartzNPoint.timeReflect_tsupport_orderedPositive
      (osiiEuclideanRotateSchwartz R hR P.data.left)
      (osiiEuclideanRotateSchwartz_tsupport_orderedNegative
        R hR P.data.left (P.data.left_support a))
  let hrightR :
      tsupport (rightR : NPointDomain d m → ℂ) ⊆ OrderedPositiveTimeRegion d m :=
    osiiEuclideanRotateSchwartz_tsupport_orderedPositive
      R hR P.data.right (P.data.right_support a)
  let F := P.toSemigroupPacketFamily OS lgc
  have hexp : 0 < (Complex.exp w).re := by
    rw [Complex.exp_re]
    exact mul_pos (Real.exp_pos _)
      (Real.cos_pos_of_mem_Ioo (abs_lt.mp hw))
  rw [F.toDirectionalBranchFamily.flatTubeBranch_coordinate_line_eq_branch
    x a hw]
  simpa [F, toSemigroupPacketFamily,
    OSIIAxisPairCommonSourceData.toSemigroupPacketFamily,
    OSIIAxisPairSemigroupPacketFamily.toDirectionalBranchFamily,
    OSIIAxisPairSemigroupPacketFamily.logBranch, leftR, rightR, hleftR,
    hrightR, R, hR, flatTubeBranchCoordinateChartBound] using
    (OSIIAxisPairRotatedSourcePacket.norm_compensatedFrozen_branch_le
      OS lgc P.T P.hT
      (osiiAxisPairPositiveCoefficients x)
      (fun b => le_of_lt (osiiAxisPairPositiveCoefficients_pos x b))
      a P.data.left (P.data.left_support a)
      P.data.right (P.data.right_support a)
      (Complex.exp w) hexp)

/-- The canonical common source is the ordinary OS conjugate tensor product
of the original positive left source with the fully translated right source. -/
theorem commonRealSource_eq_osConjTensorProduct
    (P : OSIIAxisPairCompactCommonSourcePackage leftPositive right)
    (c : osiiAxisPairIndex d → ℝ) :
    OSIIAxisPairRotatedSourcePacket.commonRealSource
        P.T c P.data.left P.data.right =
      leftPositive.osConjTensorProduct
        (translateSchwartzNPoint (d := d)
          (∑ b : osiiAxisPairIndex d,
            c b • osiiAxisPairDir (d := d) P.T b) right) := by
  rw [P.left_eq, P.right_eq]
  rfl

/-- The packet family's common scalar edge is the expected translated
Schwinger pairing of the two original ordered-positive sources. -/
theorem toSemigroupPacketFamily_realEdge
    (P : OSIIAxisPairCompactCommonSourcePackage leftPositive right)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (x : osiiAxisPairIndex d → ℝ) :
    (P.toSemigroupPacketFamily OS lgc).realEdge x =
      OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
        (leftPositive.osConjTensorProduct
          (translateSchwartzNPoint (d := d)
            (∑ b : osiiAxisPairIndex d,
              osiiAxisPairPositiveCoefficients x b •
                osiiAxisPairDir (d := d) P.T b) right))) := by
  change
    OS.S (n + m) (ZeroDiagonalSchwartz.ofClassical
      (OSIIAxisPairRotatedSourcePacket.commonRealSource
        P.T (osiiAxisPairPositiveCoefficients x)
          P.data.left P.data.right)) = _
  rw [P.commonRealSource_eq_osConjTensorProduct]

end OSIIAxisPairCompactCommonSourcePackage

end OSReconstruction
