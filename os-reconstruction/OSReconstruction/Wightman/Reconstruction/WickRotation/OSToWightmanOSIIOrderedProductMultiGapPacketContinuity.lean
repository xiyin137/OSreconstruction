/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductMultiGapPacket
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairCompactSupport














noncomputable section

open Set
open scoped BigOperators Classical

namespace OSReconstruction

variable {d k : ℕ} [NeZero d] [NeZero k]

theorem continuous_osiiAxisPairChronologicalGapTranslation
    (T : ℝ) (i : Fin k) :
    Continuous
      (fun x : Fin k → osiiAxisPairIndex d → ℝ =>
        osiiAxisPairChronologicalGapTranslation T x i) := by
  unfold osiiAxisPairChronologicalGapTranslation
  apply continuous_finset_sum
  intro a _ha
  have hcoord :
      Continuous
        (fun x : Fin k → osiiAxisPairIndex d → ℝ => x i a) :=
    (continuous_apply a).comp (continuous_apply i)
  exact
    (Real.continuous_exp.comp hcoord).smul continuous_const

theorem continuous_osiiAxisPairChronologicalPointTranslationWithoutGap
    (T : ℝ) (selected : Fin k) (j : Fin (k + 1)) :
    Continuous
      (fun x : Fin k → osiiAxisPairIndex d → ℝ =>
        osiiAxisPairChronologicalPointTranslationWithoutGap
          T x selected j) := by
  unfold osiiAxisPairChronologicalPointTranslationWithoutGap
  apply continuous_finset_sum
  intro i _hi
  by_cases hij : i.val < j.val
  · simpa [hij] using
      continuous_osiiAxisPairChronologicalGapTranslation
        (d := d) T i
  · simpa [hij] using
      (continuous_const :
        Continuous
          (fun _x : Fin k → osiiAxisPairIndex d → ℝ =>
            (0 : SpacetimeDim d)))

theorem schwartzProductTensor_reverse
    {n : ℕ}
    (fs : Fin n → SchwartzSpacetime d) :
    (SchwartzMap.productTensor fs).reverse =
      SchwartzMap.productTensor (fun j => fs (Fin.rev j)) := by
  ext y
  rw [SchwartzMap.reverse_apply, SchwartzMap.productTensor_apply,
    SchwartzMap.productTensor_apply]
  exact Fintype.prod_equiv Fin.revPerm
    (fun i => fs i (y (Fin.rev i)))
    (fun j => fs (Fin.rev j) (y j))
    (fun i => by simp)

theorem OSIIChronologicalCompactFactors.continuous_packetCenter
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (q : osiiAxisPairMultiGapIndex d k) :
    Continuous
      (fun x : Fin k → osiiAxisPairIndex d → ℝ =>
        F.packetCenter T hordered x q) := by
  unfold OSIIChronologicalCompactFactors.packetCenter
  exact
    (continuous_osiiAxisPairChronologicalPointTranslationWithoutGap
      T q.1 (Fin.succ q.1)).neg.add continuous_const

theorem osiiAxisPairChronologicalCenteredRightSource_eq_productTensor_translations
    (T : ℝ)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (selected : Fin k)
    (center : SpacetimeDim d)
    (fs : Fin (k + 1) → SchwartzSpacetime d) :
    osiiAxisPairChronologicalCenteredRightSource
        T x selected center fs =
      SchwartzMap.productTensor
        (fun j =>
          SCV.translateSchwartz
            (-center -
              osiiAxisPairChronologicalPointTranslationWithoutGap
                T x selected
                (osiiChronologicalGapSplitEquiv selected (Sum.inr j)))
            (fs
              (osiiChronologicalGapSplitEquiv selected (Sum.inr j)))) := by
  rw [osiiAxisPairChronologicalCenteredRightSource,
    osiiAxisPairChronologicalUncutRightSource,
    translateSchwartzNPoint_productTensor]
  congr 1
  funext j
  ext y
  simp only [osiiAxisPairChronologicalPacketBaseFactors,
    SCV.translateSchwartz_apply]
  congr 1
  abel

theorem OSIIChronologicalCompactFactors.packetLeftSource_eq_productTensor_translations
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    F.packetLeftSource T hordered x q =
      SchwartzMap.productTensor
        (fun j =>
          let rj : Fin (osiiChronologicalGapLeftArity q.1) :=
            Fin.rev j
          let oi : Fin (k + 1) :=
            osiiChronologicalGapSplitEquiv q.1 (Sum.inl rj)
          SCV.translateSchwartz
            (-F.packetCenter T hordered x q -
              osiiAxisPairChronologicalPointTranslationWithoutGap
                T x q.1 oi)
            (F.factors oi).conj) := by
  rw [OSIIChronologicalCompactFactors.packetLeftSource,
    osiiAxisPairChronologicalUncutLeftSource,
    schwartzProductTensor_reverse,
    translateSchwartzNPoint_productTensor]
  congr 1
  funext j
  dsimp only
  ext y
  simp only [osiiAxisPairChronologicalPacketBaseFactors,
    SCV.translateSchwartz_apply, SchwartzMap.conj_apply, map_neg]
  congr 2
  abel

theorem OSIIChronologicalCompactFactors.continuous_packetLeftSource
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (q : osiiAxisPairMultiGapIndex d k) :
    Continuous
      (fun x : Fin k → osiiAxisPairIndex d → ℝ =>
        F.packetLeftSource T hordered x q) := by
  refine
    (SchwartzMap.productTensor_continuous.comp
      (continuous_pi fun j =>
        (continuous_translateSchwartz_unrestricted
          ((F.factors
            (osiiChronologicalGapSplitEquiv q.1
              (Sum.inl (Fin.rev j)))).conj)).comp
          ((OSIIChronologicalCompactFactors.continuous_packetCenter F T hordered q).neg.sub
            (continuous_osiiAxisPairChronologicalPointTranslationWithoutGap
              T q.1
              (osiiChronologicalGapSplitEquiv q.1
                (Sum.inl (Fin.rev j))))))).congr ?_
  intro x
  symm
  exact OSIIChronologicalCompactFactors.packetLeftSource_eq_productTensor_translations
    F T hordered x q

theorem continuous_osiiAxisPairFrozenTranslation_logBase
    (T : ℝ) (q : osiiAxisPairMultiGapIndex d k) :
    Continuous
      (fun x : Fin k → osiiAxisPairIndex d → ℝ =>
        osiiAxisPairFrozenTranslation
          (d := d) T
          (osiiAxisPairPositiveCoefficients (x q.1)) q.2) := by
  unfold osiiAxisPairFrozenTranslation
  apply continuous_finset_sum
  intro b _hb
  have hcoord :
      Continuous
        (fun x : Fin k → osiiAxisPairIndex d → ℝ => x q.1 b) :=
    (continuous_apply b).comp (continuous_apply q.1)
  exact
    (Real.continuous_exp.comp hcoord).smul continuous_const

theorem OSIIChronologicalCompactFactors.frozenPacketRightSource_eq_productTensor_translations
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (x : Fin k → osiiAxisPairIndex d → ℝ)
    (q : osiiAxisPairMultiGapIndex d k) :
    translateSchwartzNPoint (d := d)
        (osiiAxisPairFrozenTranslation
          (d := d) T
          (osiiAxisPairPositiveCoefficients (x q.1)) q.2)
        (F.packetRightSource T hordered x q) =
      SchwartzMap.productTensor
        (fun j =>
          SCV.translateSchwartz
            (-osiiAxisPairFrozenTranslation
                (d := d) T
                (osiiAxisPairPositiveCoefficients (x q.1)) q.2 -
              F.packetCenter T hordered x q -
              osiiAxisPairChronologicalPointTranslationWithoutGap
                T x q.1
                (osiiChronologicalGapSplitEquiv q.1 (Sum.inr j)))
            (F.factors
              (osiiChronologicalGapSplitEquiv q.1 (Sum.inr j)))) := by
  rw [OSIIChronologicalCompactFactors.packetRightSource,
    osiiAxisPairChronologicalCenteredRightSource_eq_productTensor_translations,
    translateSchwartzNPoint_productTensor]
  congr 1
  funext j
  ext y
  simp only [SCV.translateSchwartz_apply]
  congr 1
  abel

theorem OSIIChronologicalCompactFactors.continuous_frozenPacketRightSource
    (F : OSIIChronologicalCompactFactors d k)
    (T : ℝ)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (q : osiiAxisPairMultiGapIndex d k) :
    Continuous
      (fun x : Fin k → osiiAxisPairIndex d → ℝ =>
        translateSchwartzNPoint (d := d)
          (osiiAxisPairFrozenTranslation
            (d := d) T
            (osiiAxisPairPositiveCoefficients (x q.1)) q.2)
          (F.packetRightSource T hordered x q)) := by
  refine
    (SchwartzMap.productTensor_continuous.comp
      (continuous_pi fun j =>
        (continuous_translateSchwartz_unrestricted
          (F.factors
            (osiiChronologicalGapSplitEquiv q.1 (Sum.inr j)))).comp
          (((continuous_osiiAxisPairFrozenTranslation_logBase T q).neg.sub
              (OSIIChronologicalCompactFactors.continuous_packetCenter F T hordered q)).sub
            (continuous_osiiAxisPairChronologicalPointTranslationWithoutGap
              T q.1
              (osiiChronologicalGapSplitEquiv q.1
                (Sum.inr j)))))).congr ?_
  intro x
  symm
  exact OSIIChronologicalCompactFactors.frozenPacketRightSource_eq_productTensor_translations
    F T hordered x q

theorem continuous_schwartzNPoint_timeReflect {n : ℕ} :
    Continuous
      (fun f : SchwartzNPoint d n => f.timeReflect) := by
  let θ : NPointDomain d n ≃L[ℝ] NPointDomain d n :=
    { toFun := timeReflectionN d
      map_add' := by
        intro x y
        funext i μ
        simp only [timeReflectionN, timeReflection, Pi.add_apply]
        by_cases hμ : μ = 0
        · simp [hμ]
          ring
        · simp [hμ]
      map_smul' := by
        intro c x
        funext i μ
        simp only [timeReflectionN, timeReflection, Pi.smul_apply,
          smul_eq_mul]
        by_cases hμ : μ = 0 <;> simp [hμ]
      invFun := timeReflectionN d
      left_inv := by
        intro x
        funext i
        exact timeReflection_timeReflection d (x i)
      right_inv := by
        intro x
        funext i
        exact timeReflection_timeReflection d (x i)
      continuous_toFun := by
        apply continuous_pi
        intro i
        apply continuous_pi
        intro μ
        by_cases hμ : μ = 0
        · subst hμ
          change Continuous fun a : NPointDomain d n => -(a i 0)
          exact
            ((continuous_apply 0 :
                Continuous fun y : SpacetimeDim d => y 0).comp
              (continuous_apply i :
                Continuous fun x : NPointDomain d n => x i)).fun_neg
        · have hcont :=
            (continuous_apply μ :
                Continuous fun y : SpacetimeDim d => y μ).comp
              (continuous_apply i :
                Continuous fun x : NPointDomain d n => x i)
          exact hcont.congr
            (fun a => by simp [timeReflectionN, timeReflection, hμ])
      continuous_invFun := by
        apply continuous_pi
        intro i
        apply continuous_pi
        intro μ
        by_cases hμ : μ = 0
        · subst hμ
          change Continuous fun a : NPointDomain d n => -(a i 0)
          exact
            ((continuous_apply 0 :
                Continuous fun y : SpacetimeDim d => y 0).comp
              (continuous_apply i :
                Continuous fun x : NPointDomain d n => x i)).fun_neg
        · have hcont :=
            (continuous_apply μ :
                Continuous fun y : SpacetimeDim d => y μ).comp
              (continuous_apply i :
                Continuous fun x : NPointDomain d n => x i)
          exact hcont.congr
            (fun a => by simp [timeReflectionN, timeReflection, hμ]) }
  let θS : SchwartzNPoint d n →L[ℂ] SchwartzNPoint d n :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ θ
  exact θS.continuous.congr (fun f => by
    ext x
    rfl)

theorem continuous_osiiEuclideanRotateSchwartz
    {n : ℕ}
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1) :
    Continuous
      (fun f : SchwartzNPoint d n =>
        osiiEuclideanRotateSchwartz R hR f) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (osiiEuclideanRotateNPointCLE (n := n) R hR)).continuous

/-- The actual moving compensated packet is jointly continuous in its real
source coordinates and logarithmic strip parameter under original OS alone. -/
theorem OSIIChronologicalCompactFactors.continuousOn_compensatedMovingPacket_branchOfOS
    (F : OSIIChronologicalCompactFactors d k)
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ) (hT : 1 < T)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (q : osiiAxisPairMultiGapIndex d k) :
    ContinuousOn
      (fun p :
          (Fin k → osiiAxisPairIndex d → ℝ) × ℂ =>
        (OSIIAxisPairRotatedSourcePacket.compensatedFrozen
          T hT
          (osiiAxisPairPositiveCoefficients (p.1 q.1))
          (fun b =>
            le_of_lt
              (osiiAxisPairPositiveCoefficients_pos (p.1 q.1) b))
          q.2
          (F.packetLeftSource T hordered p.1 q)
          (F.packetLeftSource_support T hT hordered p.1 q)
          (F.packetRightSource T hordered p.1 q)
          (F.packetRightSource_support T hT hordered p.1 q)).branchOfOS
            OS (Complex.exp p.2))
      (Set.univ ×ˢ {w : ℂ | |w.im| < Real.pi / 2}) := by
  let R := (osiiAxisPairRotationData T q.2).matrix
  let hR := (osiiAxisPairRotationData T q.2).orthogonal
  let leftR :
      (Fin k → osiiAxisPairIndex d → ℝ) →
        SchwartzNPoint d (osiiChronologicalGapLeftArity q.1) :=
    fun x =>
      (osiiEuclideanRotateSchwartz R hR
        (F.packetLeftSource T hordered x q)).timeReflect
  let frozenRight :
      (Fin k → osiiAxisPairIndex d → ℝ) →
        SchwartzNPoint d (osiiChronologicalGapRightArity q.1) :=
    fun x =>
      translateSchwartzNPoint (d := d)
        (osiiAxisPairFrozenTranslation
          (d := d) T
          (osiiAxisPairPositiveCoefficients (x q.1)) q.2)
        (F.packetRightSource T hordered x q)
  let rightR :
      (Fin k → osiiAxisPairIndex d → ℝ) →
        SchwartzNPoint d (osiiChronologicalGapRightArity q.1) :=
    fun x => osiiEuclideanRotateSchwartz R hR (frozenRight x)
  have hleftR_support :
      ∀ x,
        tsupport
            (leftR x :
              NPointDomain d
                (osiiChronologicalGapLeftArity q.1) → ℂ) ⊆
          OrderedPositiveTimeRegion d
            (osiiChronologicalGapLeftArity q.1) := by
    intro x
    apply SchwartzNPoint.timeReflect_tsupport_orderedPositive
    exact
      osiiEuclideanRotateSchwartz_tsupport_orderedNegative
        R hR
        (F.packetLeftSource T hordered x q)
        (F.packetLeftSource_support T hT hordered x q)
  have hfrozenRight_support :
      ∀ x,
        tsupport
            (frozenRight x :
              NPointDomain d
                (osiiChronologicalGapRightArity q.1) → ℂ) ⊆
          osiiEuclideanRotationOrderedPositiveTimeRegion
            (d := d)
            (n := osiiChronologicalGapRightArity q.1) R := by
    intro x
    exact
      osiiEuclideanTranslation_preserves_orientedPositive
        R
        (osiiAxisPairFrozenTranslation
          (d := d) T
          (osiiAxisPairPositiveCoefficients (x q.1)) q.2)
        ((osiiAxisPairRotationData T q.2).mulVec_frozenTranslation_time_nonneg
            hT
            (osiiAxisPairPositiveCoefficients (x q.1))
            (fun b =>
              le_of_lt
                (osiiAxisPairPositiveCoefficients_pos (x q.1) b)))
        (F.packetRightSource T hordered x q)
        (F.packetRightSource_support T hT hordered x q)
  have hrightR_support :
      ∀ x,
        tsupport
            (rightR x :
              NPointDomain d
                (osiiChronologicalGapRightArity q.1) → ℂ) ⊆
          OrderedPositiveTimeRegion d
            (osiiChronologicalGapRightArity q.1) := by
    intro x
    exact osiiEuclideanRotateSchwartz_tsupport_orderedPositive
      R hR (frozenRight x) (hfrozenRight_support x)
  have hleftR : Continuous leftR := by
    exact
      continuous_schwartzNPoint_timeReflect.comp
        (continuous_osiiEuclideanRotateSchwartz R hR |>.comp
          (OSIIChronologicalCompactFactors.continuous_packetLeftSource F T hordered q))
  have hrightR : Continuous rightR := by
    exact
      (continuous_osiiEuclideanRotateSchwartz R hR).comp
        (OSIIChronologicalCompactFactors.continuous_frozenPacketRightSource F T hordered q)
  let leftPositive :
      (Fin k → osiiAxisPairIndex d → ℝ) →
        euclideanPositiveTimeSubmodule
          (d := d) (osiiChronologicalGapLeftArity q.1) :=
    fun x => ⟨leftR x, hleftR_support x⟩
  let rightPositive :
      (Fin k → osiiAxisPairIndex d → ℝ) →
        euclideanPositiveTimeSubmodule
          (d := d) (osiiChronologicalGapRightArity q.1) :=
    fun x => ⟨rightR x, hrightR_support x⟩
  have hleftPositive : Continuous leftPositive :=
    hleftR.subtype_mk _
  have hrightPositive : Continuous rightPositive :=
    hrightR.subtype_mk _
  let Φ :
      ((Fin k → osiiAxisPairIndex d → ℝ) × ℂ) →
        ℂ × OSHilbertSpace OS :=
    fun p =>
      ((osiiAxisPairRadius T : ℂ) * Complex.exp p.2,
        osiiPositiveTimeSingleVectorCLM OS
          (osiiChronologicalGapRightArity q.1)
          (rightPositive p.1))
  have hΦ : Continuous Φ := by
    refine Continuous.prodMk
      (continuous_const.mul
        (Complex.continuous_exp.comp continuous_snd)) ?_
    exact
      (osiiPositiveTimeSingleVectorCLM OS
          (osiiChronologicalGapRightArity q.1)).continuous.comp
        (hrightPositive.comp continuous_fst)
  have hΦ_maps :
      Set.MapsTo Φ
        (Set.univ ×ˢ {w : ℂ | |w.im| < Real.pi / 2})
        ({z : ℂ | 0 < z.re} ×ˢ Set.univ) := by
    intro p hp
    refine ⟨?_, trivial⟩
    change 0 <
      ((osiiAxisPairRadius T : ℂ) * Complex.exp p.2).re
    rw [Complex.mul_re, Complex.exp_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos (osiiAxisPairRadius_pos T)
      (mul_pos (Real.exp_pos _)
        (Real.cos_pos_of_mem_Ioo (abs_lt.mp hp.2)))
  have hshift :
      ContinuousOn
        (fun p :
            (Fin k → osiiAxisPairIndex d → ℝ) × ℂ =>
          osiiOriginalOSHilbertComplex OS
            ((osiiAxisPairRadius T : ℂ) * Complex.exp p.2)
            (osiiPositiveTimeSingleVectorCLM OS
              (osiiChronologicalGapRightArity q.1)
              (rightPositive p.1)))
        (Set.univ ×ˢ {w : ℂ | |w.im| < Real.pi / 2}) := by
    change ContinuousOn
      ((fun p : ℂ × OSHilbertSpace OS =>
          osiiOriginalOSHilbertComplex OS p.1 p.2) ∘ Φ)
      (Set.univ ×ˢ {w : ℂ | |w.im| < Real.pi / 2})
    exact
      (continuousOn_osiiOriginalOSHilbertComplex_jointly
        OS).comp hΦ.continuousOn hΦ_maps
  have hleftVector :
      Continuous
        (fun p :
            (Fin k → osiiAxisPairIndex d → ℝ) × ℂ =>
          osiiPositiveTimeSingleVectorCLM OS
            (osiiChronologicalGapLeftArity q.1)
            (leftPositive p.1)) :=
    (osiiPositiveTimeSingleVectorCLM OS
        (osiiChronologicalGapLeftArity q.1)).continuous.comp
      (hleftPositive.comp continuous_fst)
  have hinner :
      ContinuousOn
        (fun p :
            (Fin k → osiiAxisPairIndex d → ℝ) × ℂ =>
          @inner ℂ (OSHilbertSpace OS) _
            (osiiPositiveTimeSingleVectorCLM OS
              (osiiChronologicalGapLeftArity q.1)
              (leftPositive p.1))
            (osiiOriginalOSHilbertComplex OS
              ((osiiAxisPairRadius T : ℂ) * Complex.exp p.2)
              (osiiPositiveTimeSingleVectorCLM OS
                (osiiChronologicalGapRightArity q.1)
                (rightPositive p.1))))
        (Set.univ ×ˢ {w : ℂ | |w.im| < Real.pi / 2}) :=
    hleftVector.continuousOn.inner hshift
  refine hinner.congr ?_
  intro p hp
  let P :=
    OSIIAxisPairRotatedSourcePacket.compensatedFrozen
      T hT
      (osiiAxisPairPositiveCoefficients (p.1 q.1))
      (fun b =>
        le_of_lt
          (osiiAxisPairPositiveCoefficients_pos (p.1 q.1) b))
      q.2
      (F.packetLeftSource T hordered p.1 q)
      (F.packetLeftSource_support T hT hordered p.1 q)
      (F.packetRightSource T hordered p.1 q)
      (F.packetRightSource_support T hT hordered p.1 q)
  let Q :=
    OSIIAxisPairRotatedSourcePacket.ofRotatedPositive
      T q.2
      (leftR p.1) (hleftR_support p.1)
      (rightR p.1) (hrightR_support p.1)
  have hPQleft : P.left = Q.left := by
    simp [P, Q, leftR, R, hR,
      OSIIAxisPairRotatedSourcePacket.compensatedFrozen,
      OSIIAxisPairRotatedSourcePacket.compensatedLeft,
      OSIIAxisPairRotatedSourcePacket.ofRotatedPositive,
      osiiEuclideanCompensatedLeftSchwartz]
  have hPQright : P.right = Q.right := by
    dsimp [P, Q, rightR, frozenRight,
      OSIIAxisPairRotatedSourcePacket.compensatedFrozen,
      OSIIAxisPairRotatedSourcePacket.compensatedLeft,
      OSIIAxisPairRotatedSourcePacket.ofRotatedPositive]
    rw [osiiEuclideanUnrotateSchwartz_rotate]
  change P.branchOfOS OS (Complex.exp p.2) = _
  rw [show P.branchOfOS OS (Complex.exp p.2) =
      Q.branchOfOS OS (Complex.exp p.2) from
    congrFun
      (OSIIAxisPairRotatedSourcePacket.branchOfOS_eq_of_source_eq
        P Q hPQleft hPQright OS)
      (Complex.exp p.2)]
  simp [Q, leftPositive, rightPositive,
    OSIIAxisPairRotatedSourcePacket.branchOfOS,
    osiiAxisPairCanonicalRotatedSemigroupBranchOfOS,
    osiiAxisPairRotatedSemigroupBranchOfOS,
    OSIIAxisPairRotatedSourcePacket.ofRotatedPositive,
    osiiEuclideanRotatePositiveTimeComponent,
    osiiEuclideanRotateSchwartz_unrotate]

/-- The legacy moving-packet continuity claim is a compatibility wrapper
around the genuine original-OS source-continuity theorem. -/
theorem OSIIChronologicalCompactFactors.continuousOn_compensatedMovingPacket_branch
    (F : OSIIChronologicalCompactFactors d k)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (T : ℝ) (hT : 1 < T)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (q : osiiAxisPairMultiGapIndex d k) :
    ContinuousOn
      (fun p :
          (Fin k → osiiAxisPairIndex d → ℝ) × ℂ =>
        (OSIIAxisPairRotatedSourcePacket.compensatedFrozen
          T hT
          (osiiAxisPairPositiveCoefficients (p.1 q.1))
          (fun b =>
            le_of_lt
              (osiiAxisPairPositiveCoefficients_pos (p.1 q.1) b))
          q.2
          (F.packetLeftSource T hordered p.1 q)
          (F.packetLeftSource_support T hT hordered p.1 q)
          (F.packetRightSource T hordered p.1 q)
          (F.packetRightSource_support T hT hordered p.1 q)).branch
            OS lgc (Complex.exp p.2))
      (Set.univ ×ˢ {w : ℂ | |w.im| < Real.pi / 2}) := by
  refine
    (F.continuousOn_compensatedMovingPacket_branchOfOS
      OS T hT hordered q).congr ?_
  intro p hp
  apply OSIIAxisPairRotatedSourcePacket.branch_eq_branchOfOS
  rw [Complex.exp_re]
  exact mul_pos (Real.exp_pos _)
    (Real.cos_pos_of_mem_Ioo (abs_lt.mp hp.2))

theorem OSIIChronologicalCompactFactors.continuousOn_multiGapPacketFamily_branch
    (F : OSIIChronologicalCompactFactors d k)
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (T : ℝ) (hT : 1 < T)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0)
    (q : osiiAxisPairMultiGapIndex d k) :
    ContinuousOn
      (fun p :
          (Fin k → osiiAxisPairIndex d → ℝ) × ℂ =>
        ((F.multiGapPacketFamily OS lgc T hT hordered).packet
          p.1 q).branch OS lgc (Complex.exp p.2))
      (Set.univ ×ˢ {w : ℂ | |w.im| < Real.pi / 2}) := by
  simpa [OSIIChronologicalCompactFactors.multiGapPacketFamily,
    OSIIAxisPairMultiGapSemigroupPacketFamily.ofCompensatedFrozenDependent,
    OSIIAxisPairGapRotatedSourcePacket.branch] using
    OSIIChronologicalCompactFactors.continuousOn_compensatedMovingPacket_branch
      F OS lgc T hT hordered q

/-- The actual ordered compact product source supplies its complete
gap-direction flat cross directly from original OS data. Every selected
chart has the same canonical zero-diagonal chronological Schwinger edge. -/
noncomputable def OSIIChronologicalCompactFactors.multiGapFlatCrossOfOS
    (F : OSIIChronologicalCompactFactors d k)
    (OS : OsterwalderSchraderAxioms d)
    (T : ℝ) (hT : 1 < T)
    (hordered :
      ∀ a : osiiAxisPairIndex d,
        ∀ i j : Fin (k + 1), i < j →
          ∀ y ∈ tsupport
              ((F.factors i : SchwartzSpacetime d) :
                SpacetimeDim d → ℂ),
            ∀ z ∈ tsupport
                ((F.factors j : SchwartzSpacetime d) :
                  SpacetimeDim d → ℂ),
              ((osiiAxisPairRotationData T a).matrix.mulVec y) 0 <
                ((osiiAxisPairRotationData T a).matrix.mulVec z) 0) :
    OSIIAxisPairMultiGapFlatCrossData d k :=
  OSIIAxisPairMultiGapFlatCrossData.ofCompensatedFrozenDependentOfOS
    OS T hT
    (fun x q => F.packetLeftSource T hordered x q)
    (fun x q => F.packetLeftSource_support T hT hordered x q)
    (fun x q => F.packetRightSource T hordered x q)
    (fun x q => F.packetRightSource_support T hT hordered x q)
    (by
      intro x y q hxy
      exact F.packetLeftSource_congr_of_eq_off_selected
        T hordered q hxy)
    (by
      intro x y q hxy
      exact F.packetRightSource_congr_of_eq_off_selected
        T hordered q hxy)
    (fun x =>
      OS.S (k + 1) (ZeroDiagonalSchwartz.ofClassical
        (SchwartzMap.productTensor
          (osiiAxisPairChronologicalTranslatedFactors T x F.factors))))
    (by
      intro x q
      apply F.packet_commonRealSource_schwinger_eq OS T hordered x q
      exact
        OSIIAxisPairRotatedSourcePacket.commonRealSource_vanishes
          T hT
          (osiiAxisPairPositiveCoefficients (x q.1))
          (fun b =>
            le_of_lt (osiiAxisPairPositiveCoefficients_pos (x q.1) b))
          q.2
          (osiiAxisPairPositiveCoefficients_pos (x q.1) q.2)
          (F.packetLeftSource T hordered x q)
          (F.packetLeftSource_support T hT hordered x q)
          (F.packetRightSource T hordered x q)
          (F.packetRightSource_support T hT hordered x q))
    (F.continuousOn_compensatedMovingPacket_branchOfOS
      OS T hT hordered)

end OSReconstruction
