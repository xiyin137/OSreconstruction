/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketRootedAffinePositiveHeadBridge
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVApproxIdentityConvolution
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorChronologicalCoordinates














noncomputable section

open Complex Filter MeasureTheory Set
open scoped Classical Topology

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d k : ℕ} [NeZero d] [NeZero k]

/-- A set is closed under strictly positive contractions toward the origin. -/
def IsPositiveRadial
    {E : Type*} [SMul ℝ E]
    (U : Set E) : Prop :=
  ∀ x, x ∈ U → ∀ {t : ℝ}, 0 < t → t ≤ 1 → t • x ∈ U

theorem isPositiveRadial_ball_inter_strictPositive
    (ε : ℝ) :
    IsPositiveRadial
      (Metric.ball (0 : Fin k → ℝ) ε ∩
        section43TimeStrictPositiveRegion k) := by
  intro τ hτ t ht0 ht1
  refine ⟨?_, ?_⟩
  · have hτ_ball : ‖τ‖ < ε := by
      simpa [Metric.mem_ball, dist_zero_right] using hτ.1
    rw [Metric.mem_ball, dist_zero_right]
    rw [norm_smul, Real.norm_of_nonneg ht0.le]
    exact
      (mul_le_of_le_one_left (norm_nonneg τ) ht1).trans_lt hτ_ball
  · intro q
    change 0 < t * τ q
    exact mul_pos ht0 (hτ.2 q)

/-- Chronological sign reflection preserves Lebesgue measure. -/
theorem generatorChronologicalParameter_measurePreserving
    (i : GeneratorIndex k) :
    MeasurePreserving
      (generatorChronologicalParameter i)
      volume volume := by
  have hpi :
      MeasurePreserving
        (fun ξ : Fin k → ℝ =>
          fun j =>
            (if j < i.toGap then
              ContinuousLinearEquiv.neg ℝ
            else
              ContinuousLinearEquiv.refl ℝ ℝ) (ξ j))
        volume volume :=
    MeasureTheory.volume_preserving_pi fun j => by
      by_cases hj : j < i.toGap
      · rw [if_pos hj]
        convert
          (MeasureTheory.Measure.measurePreserving_neg
            (volume : Measure ℝ)) using 1
        funext x
        simp
      · simpa [hj] using
          (MeasurePreserving.id (volume : Measure ℝ))
  convert hpi using 1
  funext ξ j
  by_cases hj : j < i.toGap
  · simp [generatorChronologicalParameter,
      GeneratorIndex.bridgeGlobalIndex_eq_toGap, hj]
  · simp [generatorChronologicalParameter,
      GeneratorIndex.bridgeGlobalIndex_eq_toGap, hj]

/-- Pull a real Schwartz probe through the chronological sign reflection. -/
noncomputable def generatorChronologicalReflectedTest
    (i : GeneratorIndex k)
    (h : SchwartzMap (Fin k → ℝ) ℂ) :
    SchwartzMap (Fin k → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (generatorChronologicalParameterCLE i) h

@[simp]
theorem generatorChronologicalReflectedTest_apply_reflection
    (i : GeneratorIndex k)
    (h : SchwartzMap (Fin k → ℝ) ℂ)
    (ξ : Fin k → ℝ) :
    generatorChronologicalReflectedTest i h
        (generatorChronologicalParameter i ξ) =
      h ξ := by
  simp [generatorChronologicalReflectedTest,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    generatorChronologicalParameterCLE_apply]

/-- Chronological reflection preserves compact support of real probes. -/
theorem generatorChronologicalReflectedTest_compact
    (i : GeneratorIndex k)
    (h : SchwartzMap (Fin k → ℝ) ℂ)
    (hcompact : HasCompactSupport (h : (Fin k → ℝ) → ℂ)) :
    HasCompactSupport
      (generatorChronologicalReflectedTest i h :
        (Fin k → ℝ) → ℂ) := by
  simpa [generatorChronologicalReflectedTest,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_def] using
    hcompact.comp_homeomorph
      (generatorChronologicalParameterCLE i).toHomeomorph

/-- The affine chronological coordinate change `ξ ↦ Gᵢ ξ + anchor`. -/
noncomputable def generatorChronologicalAffineMeasurableEquiv
    (i : GeneratorIndex k)
    (anchor : Fin k → ℝ) :
    (Fin k → ℝ) ≃ᵐ (Fin k → ℝ) :=
  (generatorChronologicalParameterCLE i).toHomeomorph.toMeasurableEquiv.trans
    (Homeomorph.addRight anchor).toMeasurableEquiv

@[simp]
theorem generatorChronologicalAffineMeasurableEquiv_apply
    (i : GeneratorIndex k)
    (anchor ξ : Fin k → ℝ) :
    generatorChronologicalAffineMeasurableEquiv i anchor ξ =
      generatorChronologicalParameter i ξ + anchor := by
  simp [generatorChronologicalAffineMeasurableEquiv]

/-- The affine chronological coordinate change preserves Lebesgue measure. -/
theorem generatorChronologicalAffine_measurePreserving
    (i : GeneratorIndex k)
    (anchor : Fin k → ℝ) :
    MeasurePreserving
      (generatorChronologicalAffineMeasurableEquiv i anchor)
      volume volume := by
  have hG :
      MeasurePreserving
        (generatorChronologicalParameterCLE i).toHomeomorph.toMeasurableEquiv
        volume volume := by
    convert generatorChronologicalParameter_measurePreserving i using 1
    funext ξ
    exact generatorChronologicalParameterCLE_apply i ξ
  have hadd :
      MeasurePreserving
        (Homeomorph.addRight anchor).toMeasurableEquiv
        volume volume := by
    simpa using
      (MeasureTheory.measurePreserving_add_right
        (volume : Measure (Fin k → ℝ)) anchor)
  exact hadd.comp hG

/-- Pull a compactly supported real-edge probe through the affine
chronological coordinate change. -/
noncomputable def generatorChronologicalPullbackTest
    (i : GeneratorIndex k)
    (anchor : Fin k → ℝ)
    (h : SchwartzMap (Fin k → ℝ) ℂ) :
    SchwartzMap (Fin k → ℝ) ℂ :=
  SCV.translateSchwartz (-anchor)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (generatorChronologicalParameterCLE i) h)

@[simp]
theorem generatorChronologicalPullbackTest_apply_affine
    (i : GeneratorIndex k)
    (anchor ξ : Fin k → ℝ)
    (h : SchwartzMap (Fin k → ℝ) ℂ) :
    generatorChronologicalPullbackTest i anchor h
        (generatorChronologicalParameter i ξ + anchor) =
      h ξ := by
  simp [generatorChronologicalPullbackTest,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    SCV.translateSchwartz_apply]

/-- Affine chronological pullback preserves compact support. -/
theorem generatorChronologicalPullbackTest_compact
    (i : GeneratorIndex k)
    (anchor : Fin k → ℝ)
    (h : SchwartzMap (Fin k → ℝ) ℂ)
    (hcompact : HasCompactSupport (h : (Fin k → ℝ) → ℂ)) :
    HasCompactSupport
      (generatorChronologicalPullbackTest i anchor h :
        (Fin k → ℝ) → ℂ) := by
  have hcomp :
      HasCompactSupport
        ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (generatorChronologicalParameterCLE i) h :
            SchwartzMap (Fin k → ℝ) ℂ) :
          (Fin k → ℝ) → ℂ) := by
    simpa [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      Function.comp_def] using
      hcompact.comp_homeomorph
        (generatorChronologicalParameterCLE i).toHomeomorph
  exact hasCompactSupport_translateSchwartz _ hcomp (-anchor)

@[simp]
theorem generatorChronologicalPullbackTest_reflected
    (i : GeneratorIndex k)
    (anchor : Fin k → ℝ)
    (h : SchwartzMap (Fin k → ℝ) ℂ) :
    generatorChronologicalPullbackTest i anchor
        (generatorChronologicalReflectedTest i h) =
      SCV.translateSchwartz (-anchor) h := by
  ext ξ
  simp [generatorChronologicalPullbackTest,
    generatorChronologicalReflectedTest,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    SCV.translateSchwartz_apply,
    generatorChronologicalParameterCLE_apply,
    generatorChronologicalParameter_self]

/-- Change variables from one split-native real chart back to common
chronological coordinates. -/
theorem integral_comp_generatorChronologicalParameter_mul
    (i : GeneratorIndex k)
    (f : (Fin k → ℝ) → ℂ)
    (h : SchwartzMap (Fin k → ℝ) ℂ) :
    (∫ ξ : Fin k → ℝ,
        f (generatorChronologicalParameter i ξ) * h ξ) =
      ∫ η : Fin k → ℝ,
        f η * generatorChronologicalReflectedTest i h η := by
  let g : (Fin k → ℝ) → ℂ :=
    fun η => f η * generatorChronologicalReflectedTest i h η
  let e : (Fin k → ℝ) ≃ᵐ (Fin k → ℝ) :=
    (generatorChronologicalParameterCLE i).toHomeomorph.toMeasurableEquiv
  have he :
      MeasurePreserving e volume volume := by
    convert generatorChronologicalParameter_measurePreserving i using 1
    funext ξ
    exact generatorChronologicalParameterCLE_apply i ξ
  calc
    (∫ ξ : Fin k → ℝ,
        f (generatorChronologicalParameter i ξ) * h ξ) =
        ∫ ξ : Fin k → ℝ,
          g (generatorChronologicalParameter i ξ) := by
      congr 1
      funext ξ
      simp [g]
    _ = ∫ η : Fin k → ℝ, g η := by
      simpa [e, generatorChronologicalParameterCLE_apply] using
        he.integral_comp' g
    _ = ∫ η : Fin k → ℝ,
        f η * generatorChronologicalReflectedTest i h η := rfl

variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}

/-- A translated positive source retains strict positivity after any further
translation whose coordinate displacement stays below the fixed anchor.  The
criterion is uniform in the approximate-identity scale. -/
theorem translatedSource_translate_tsupport_subset_strictPositive
    {n : ℕ}
    (J : Section43ProductTimeApproximateIdentity n)
    (τ : Fin n → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion n)
    (v : Fin n → ℝ)
    (hv : ∀ j, v j < τ j)
    (N : ℕ) :
    tsupport
        ((SCV.translateSchwartz v
          (J.translatedSource τ hτ N).f :
            SchwartzMap (Fin n → ℝ) ℂ) :
          (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n := by
  intro x hx j
  rw [tsupport_translateSchwartz_eq_preimage] at hx
  rw [translatedSource_f,
    tsupport_translateSchwartz_eq_preimage] at hx
  have hpositive := J.test_positive N hx j
  change 0 < x j + v j - τ j at hpositive
  linarith [hv j]

/-- Continuity of a displacement family gives one neighborhood on which all
translated anchored sources remain strictly positive at every scale. -/
theorem eventually_translatedSource_translate_tsupport_subset_strictPositive
    {n : ℕ} {E : Type*} [TopologicalSpace E]
    (J : Section43ProductTimeApproximateIdentity n)
    (τ : Fin n → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion n)
    (v : E → Fin n → ℝ)
    (x₀ : E)
    (hv_cont : ContinuousAt v x₀)
    (hv_zero : v x₀ = 0) :
    ∀ᶠ x in 𝓝 x₀,
      ∀ N,
        tsupport
            ((SCV.translateSchwartz (v x)
              (J.translatedSource τ hτ N).f :
                SchwartzMap (Fin n → ℝ) ℂ) :
              (Fin n → ℝ) → ℂ) ⊆
          section43TimeStrictPositiveRegion n := by
  let U : Set (Fin n → ℝ) := {w | ∀ j, w j < τ j}
  have hU_open : IsOpen U := by
    dsimp [U]
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun j =>
      isOpen_lt (continuous_apply j) continuous_const
  have hzero_mem : (0 : Fin n → ℝ) ∈ U := by
    intro j
    simpa using hτ j
  have hU_nhds : U ∈ 𝓝 (v x₀) := by
    rw [hv_zero]
    exact hU_open.mem_nhds hzero_mem
  filter_upwards
    [hv_cont.eventually hU_nhds]
      with x hx
  change ∀ j, v x j < τ j at hx
  intro N
  exact
    translatedSource_translate_tsupport_subset_strictPositive
      J τ hτ (v x) hx N

/-- Distributional packet-scale convergence after the split-dependent
chronological sign reflection. -/
theorem tendsto_integral_apply_translate_timeTest_chronological_mul
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (tailStart : ℕ)
    (h : SchwartzMap (Fin k → ℝ) ℂ)
    (hcompact : HasCompactSupport (h : (Fin k → ℝ) → ℂ))
    (T : SchwartzMap (Fin k → ℝ) ℂ →L[ℂ] ℂ) :
    Tendsto
      (fun N =>
        ∫ ξ : Fin k → ℝ,
          T (SCV.translateSchwartz
              (-(generatorChronologicalParameter i ξ))
              (A.timeTest (N + tailStart))) *
            h ξ)
      atTop
      (𝓝 (T (generatorChronologicalPullbackTest i anchor h))) := by
  let h' := generatorChronologicalPullbackTest i anchor h
  have h'compact : HasCompactSupport (h' : (Fin k → ℝ) → ℂ) :=
    generatorChronologicalPullbackTest_compact i anchor h hcompact
  have hbase :=
    (I.toSchwartzTimeApproximateIdentity
      |>.tendsto_integral_apply_translate_test_mul h' h'compact T).comp
        (tendsto_add_atTop_nat (tailStart + A.carrierData.tailStart))
  apply (tendsto_congr' ?_).2 hbase
  exact Filter.Eventually.of_forall fun N => by
    let e := generatorChronologicalAffineMeasurableEquiv i anchor
    let g : (Fin k → ℝ) → ℂ :=
      fun y =>
        T (SCV.translateSchwartz (-y)
          (I.test ((N + tailStart) + A.carrierData.tailStart))) *
          h' y
    calc
      (∫ ξ : Fin k → ℝ,
          T (SCV.translateSchwartz
              (-(generatorChronologicalParameter i ξ))
              (A.timeTest (N + tailStart))) *
            h ξ) =
          ∫ ξ : Fin k → ℝ, g (e ξ) := by
            apply integral_congr_ae
            filter_upwards with ξ
            rw [A.translate_timeTest (N + tailStart)
              (generatorChronologicalParameter i ξ)]
            simp [g, e, h',
              generatorChronologicalAffineMeasurableEquiv_apply]
      _ = ∫ y : Fin k → ℝ, g y :=
        (generatorChronologicalAffine_measurePreserving i anchor).integral_comp' g
      _ =
          ∫ y : Fin k → ℝ,
            T (SCV.translateSchwartz (-y)
              (I.test (N +
                (tailStart + A.carrierData.tailStart)))) *
              h' y := by
            congr 1
            funext y
            simp [g, Nat.add_assoc]

/-- Packet-scale convergence after inserting a fixed reduced spatial tensor
and evaluating by a continuous reduced Schwinger functional. -/
theorem tendsto_integral_translatedReducedTensor_chronological_mul
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (tailStart : ℕ)
    (L : SchwartzNPoint d k →L[ℂ] ℂ)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (h : SchwartzMap (Fin k → ℝ) ℂ)
    (hcompact : HasCompactSupport (h : (Fin k → ℝ) → ℂ)) :
    Tendsto
      (fun N =>
        ∫ ξ : Fin k → ℝ,
          L (section43NPointTimeSpatialTensor d k
              (SCV.translateSchwartz
                (-(generatorChronologicalParameter i ξ))
                (A.timeTest (N + tailStart)))
              (section43SpatialHeadMarginal F)) *
            h ξ)
      atTop
      (𝓝
        (L (section43NPointTimeSpatialTensor d k
          (generatorChronologicalPullbackTest i anchor h)
          (section43SpatialHeadMarginal F)))) := by
  let T : SchwartzMap (Fin k → ℝ) ℂ →L[ℂ] ℂ :=
    L.comp
      (section43TimeSpatialTensorCLM d k
        (section43SpatialHeadMarginal F))
  simpa [T] using
    A.tendsto_integral_apply_translate_timeTest_chronological_mul
      i tailStart h hcompact T

/-- In common chronological coordinates, the packet-scale distributional
limit is independent of the generator split used to prove it. -/
theorem tendsto_integral_translatedReducedTensor_commonChronological_mul
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (tailStart : ℕ)
    (L : SchwartzNPoint d k →L[ℂ] ℂ)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (h : SchwartzMap (Fin k → ℝ) ℂ)
    (hcompact : HasCompactSupport (h : (Fin k → ℝ) → ℂ)) :
    Tendsto
      (fun N =>
        ∫ τ : Fin k → ℝ,
          L (section43NPointTimeSpatialTensor d k
              (SCV.translateSchwartz (-τ)
                (A.timeTest (N + tailStart)))
              (section43SpatialHeadMarginal F)) *
            h τ)
      atTop
      (𝓝
        (L (section43NPointTimeSpatialTensor d k
          (SCV.translateSchwartz (-anchor) h)
          (section43SpatialHeadMarginal F)))) := by
  let h' := generatorChronologicalReflectedTest i h
  have h'compact : HasCompactSupport (h' : (Fin k → ℝ) → ℂ) :=
    generatorChronologicalReflectedTest_compact i h hcompact
  have htend :=
    A.tendsto_integral_translatedReducedTensor_chronological_mul
      i tailStart L F h' h'compact
  have heq :
      (fun N =>
        ∫ τ : Fin k → ℝ,
          L (section43NPointTimeSpatialTensor d k
              (SCV.translateSchwartz (-τ)
                (A.timeTest (N + tailStart)))
              (section43SpatialHeadMarginal F)) *
            h τ) =
        fun N =>
          ∫ ξ : Fin k → ℝ,
            L (section43NPointTimeSpatialTensor d k
                (SCV.translateSchwartz
                  (-(generatorChronologicalParameter i ξ))
                  (A.timeTest (N + tailStart)))
                (section43SpatialHeadMarginal F)) *
              h' ξ := by
    funext N
    rw [integral_comp_generatorChronologicalParameter_mul i
      (fun τ =>
        L (section43NPointTimeSpatialTensor d k
          (SCV.translateSchwartz (-τ)
            (A.timeTest (N + tailStart)))
          (section43SpatialHeadMarginal F)))
      h']
    congr 1
    funext τ
    simp [h', generatorChronologicalReflectedTest]
  rw [heq]
  simpa [h', generatorChronologicalPullbackTest_reflected] using htend

namespace RootedA0BlockContinuousTranslationData

variable
  {OS : OsterwalderSchraderAxioms d}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
  {R : TripleConvolutionRootData I}

private theorem cast_mem_section43TimeStrictPositiveRegion
    {n m : ℕ}
    (e : n = m)
    (τ : Fin n → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion n) :
    cast (congrArg (fun q => Fin q → ℝ) e) τ ∈
      section43TimeStrictPositiveRegion m := by
  subst m
  exact hτ

private theorem cast_translatedSource_f
    {n m : ℕ}
    (e : n = m)
    (J : Section43ProductTimeApproximateIdentity n)
    (τ : Fin n → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion n)
    (N : ℕ) :
    ((cast
        (congrArg Section43ProductTimeApproximateIdentity e) J
      ).translatedSource
        (cast (congrArg (fun q => Fin q → ℝ) e) τ)
        (cast_mem_section43TimeStrictPositiveRegion e τ hτ) N).f =
      cast
        (congrArg (fun q => SchwartzMap (Fin q → ℝ) ℂ) e)
        (J.translatedSource τ hτ N).f := by
  subst m
  rfl

/-- One neighborhood of the generator origin keeps both translated rooted
block profiles strictly positive at every packet scale. -/
theorem eventually_rootedTranslatedTimeProfilesPositive_uniform_scale
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k) :
    ∀ᶠ ξ : Fin k → ℝ in 𝓝 0,
      ∀ timeScale,
        D.RootedTranslatedTimeProfilesPositive i timeScale ξ := by
  let JL : Section43ProductTimeApproximateIdentity i.n :=
    cast
      (congrArg Section43ProductTimeApproximateIdentity
        (Nat.sub_add_cancel i.hn))
      (A.rootedLeftBlockApproximateIdentity R i)
  let τL : Fin i.n → ℝ :=
    cast
      (congrArg (fun q => Fin q → ℝ) (Nat.sub_add_cancel i.hn))
      (A.rootedLeftBlockAnchor i)
  let vL : (Fin k → ℝ) → Fin i.n → ℝ :=
    fun ξ =>
      chronologicalTimeProfileDisplacementOfPositive i.hn
        (i.leftRealCoordinates ξ)
  have hτL :
      τL ∈ section43TimeStrictPositiveRegion i.n := by
    exact
      cast_mem_section43TimeStrictPositiveRegion
        (Nat.sub_add_cancel i.hn)
        (A.rootedLeftBlockAnchor i)
        (A.rootedLeftBlockAnchor_positive i)
  have hvL_cont : ContinuousAt vL (0 : Fin k → ℝ) := by
    have hdisp :
        Continuous
          (chronologicalTimeProfileDisplacementOfPositive i.hn) := by
      apply continuous_pi
      intro j
      unfold chronologicalTimeProfileDisplacementOfPositive
      generalize
        hq :
          Fin.cast (Nat.sub_add_cancel i.hn).symm j = q
      refine Fin.cases ?_ (fun a => ?_) q
      · simpa using
          (continuous_const :
            Continuous
              (fun _ : Fin (i.n - 1) → ℝ => (0 : ℝ)))
      · exact continuous_neg.comp (continuous_apply a)
    have hleft : Continuous i.leftRealCoordinates := by
      unfold GeneratorIndex.leftRealCoordinates
      fun_prop
    exact (hdisp.comp hleft).continuousAt
  have hvL_zero : vL (0 : Fin k → ℝ) = 0 := by
    have hleft_zero :
        i.leftRealCoordinates (0 : Fin k → ℝ) = 0 := by
      ext a
      simp [GeneratorIndex.leftRealCoordinates]
    rw [show vL (0 : Fin k → ℝ) =
        chronologicalTimeProfileDisplacementOfPositive i.hn
          (i.leftRealCoordinates 0) by rfl, hleft_zero]
    ext j
    unfold chronologicalTimeProfileDisplacementOfPositive
    generalize
      hq :
        Fin.cast (Nat.sub_add_cancel i.hn).symm j = q
    refine Fin.cases ?_ (fun a => ?_) q <;> simp
  have hleft :=
    eventually_translatedSource_translate_tsupport_subset_strictPositive
      JL τL hτL vL (0 : Fin k → ℝ) hvL_cont hvL_zero
  let JR : Section43ProductTimeApproximateIdentity i.m :=
    cast
      (congrArg Section43ProductTimeApproximateIdentity
        (Nat.sub_add_cancel i.hm))
      (A.rootedRightBlockApproximateIdentity R i)
  let τR : Fin i.m → ℝ :=
    cast
      (congrArg (fun q => Fin q → ℝ) (Nat.sub_add_cancel i.hm))
      (A.rootedRightBlockAnchor i)
  let vR : (Fin k → ℝ) → Fin i.m → ℝ :=
    fun ξ =>
      chronologicalTimeProfileDisplacementOfPositive i.hm
        (i.rightRealCoordinates ξ)
  have hτR :
      τR ∈ section43TimeStrictPositiveRegion i.m := by
    exact
      cast_mem_section43TimeStrictPositiveRegion
        (Nat.sub_add_cancel i.hm)
        (A.rootedRightBlockAnchor i)
        (A.rootedRightBlockAnchor_positive i)
  have hvR_cont : ContinuousAt vR (0 : Fin k → ℝ) := by
    have hdisp :
        Continuous
          (chronologicalTimeProfileDisplacementOfPositive i.hm) := by
      apply continuous_pi
      intro j
      unfold chronologicalTimeProfileDisplacementOfPositive
      generalize
        hq :
          Fin.cast (Nat.sub_add_cancel i.hm).symm j = q
      refine Fin.cases ?_ (fun b => ?_) q
      · simpa using
          (continuous_const :
            Continuous
              (fun _ : Fin (i.m - 1) → ℝ => (0 : ℝ)))
      · exact continuous_neg.comp (continuous_apply b)
    have hright : Continuous i.rightRealCoordinates := by
      unfold GeneratorIndex.rightRealCoordinates
      fun_prop
    exact (hdisp.comp hright).continuousAt
  have hvR_zero : vR (0 : Fin k → ℝ) = 0 := by
    have hright_zero :
        i.rightRealCoordinates (0 : Fin k → ℝ) = 0 := by
      ext b
      simp [GeneratorIndex.rightRealCoordinates]
    rw [show vR (0 : Fin k → ℝ) =
        chronologicalTimeProfileDisplacementOfPositive i.hm
          (i.rightRealCoordinates 0) by rfl, hright_zero]
    ext j
    unfold chronologicalTimeProfileDisplacementOfPositive
    generalize
      hq :
        Fin.cast (Nat.sub_add_cancel i.hm).symm j = q
    refine Fin.cases ?_ (fun b => ?_) q <;> simp
  have hright :=
    eventually_translatedSource_translate_tsupport_subset_strictPositive
      JR τR hτR vR (0 : Fin k → ℝ) hvR_cont hvR_zero
  filter_upwards [hleft, hright] with ξ hleftξ hrightξ
  intro timeScale
  constructor
  · have hsource :
        (JL.translatedSource τL hτL
          (timeScale + D.commonTailStart i)).f =
            D.rootedLeftTimeProfile i timeScale := by
      simpa [JL, τL, rootedLeftTimeProfile] using
        cast_translatedSource_f
          (Nat.sub_add_cancel i.hn)
          (A.rootedLeftBlockApproximateIdentity R i)
          (A.rootedLeftBlockAnchor i)
          (A.rootedLeftBlockAnchor_positive i)
          (timeScale + D.commonTailStart i)
    rw [rootedLeftTranslatedTimeProfile, ← hsource]
    exact hleftξ (timeScale + D.commonTailStart i)
  · have hsource :
        (JR.translatedSource τR hτR
          (timeScale + D.commonTailStart i)).f =
            D.rootedRightTimeProfile i timeScale := by
      simpa [JR, τR, rootedRightTimeProfile] using
        cast_translatedSource_f
          (Nat.sub_add_cancel i.hm)
          (A.rootedRightBlockApproximateIdentity R i)
          (A.rootedRightBlockAnchor i)
          (A.rootedRightBlockAnchor_positive i)
          (timeScale + D.commonTailStart i)
    rw [rootedRightTranslatedTimeProfile, ← hsource]
    exact hrightξ (timeScale + D.commonTailStart i)

/-- The full rooted Hermite sums use any caller-supplied translated
positive-head current package before the generator split is chosen, under
the original OS axioms alone. -/
theorem
    eventually_rootSmearedSpatialHermiteGeneratorSumOfOS_positiveReal_eq_translatedReducedTensor_uniform_scale_all_splits_of_currentData
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (C : CommonTranslatedPositiveHeadSpatialSourceCurrentData
      (d := d) (k := k) A OS) :
    ∀ i : GeneratorIndex k,
      ∀ᶠ ξ : Fin k → ℝ in 𝓝 0,
        ∀ (timeScale : ℕ)
          (hprofiles :
            D.RootedTranslatedTimeProfilesPositive i timeScale ξ)
          (hbridge : 0 < ξ i.bridgeGlobalIndex),
          i.leftRealCoordinates ξ ∈ (D.left i).realRegion →
          i.rightRealCoordinates ξ ∈ (D.right i).realRegion →
          ∀ F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ,
            D.rootSmearedSpatialHermiteGeneratorSumOfOS
                i timeScale (osiiPositiveRealTimeEmbed ξ) F =
              C.current (section43NPointTimeSpatialTensor d k
                (SCV.translateSchwartz
                  (-(generatorChronologicalParameter i ξ))
                  (A.timeTest (timeScale + D.commonTailStart i)))
                (section43SpatialHeadMarginal F)) := by
  intro i
  filter_upwards
    [D.tendsto_spatialHermiteGeneratorFiniteShellAffineRootSmearingOfOS_uniform_scale_all_splits_of_currentData
      C i]
    with ξ hreal_ξ
  intro timeScale hprofiles hbridge hleft hright F
  let w : OSIITimeGapSpace k := osiiPositiveRealTimeEmbed ξ
  have hw_domain :
      w ∈ generatorSemigroupDomain
        i (D.left i).domain (D.right i).domain := by
    exact
      positiveRealTimeEmbed_mem_generatorSemigroupDomain
        i ξ hbridge
        ((D.left i).realRegion_to_domain
          (i.leftRealCoordinates ξ) hleft)
        ((D.right i).realRegion_to_domain
          (i.rightRealCoordinates ξ) hright)
  have hsum :
      Tendsto
        (fun shell =>
          D.rootSmearedSpatialHermiteGeneratorFiniteShellOfOS
            i timeScale shell w F)
        atTop
        (𝓝 (D.rootSmearedSpatialHermiteGeneratorSumOfOS
          i timeScale w F)) := by
    have hcompact :=
      D.tendstoUniformlyOn_rootSmearedSpatialHermiteGeneratorFiniteShellOfOS_on_compact
        i timeScale F {w} isCompact_singleton
        (by simpa [Set.singleton_subset_iff] using hw_domain)
    exact hcompact.tendsto_at (Set.mem_singleton w)
  have hreal_limit :
      Tendsto
        (fun shell =>
          D.rootSmearedSpatialHermiteGeneratorFiniteShellOfOS
            i timeScale shell w F)
        atTop
        (𝓝
          (C.current (section43NPointTimeSpatialTensor d k
            (SCV.translateSchwartz
              (-(generatorChronologicalParameter i ξ))
              (A.timeTest (timeScale + D.commonTailStart i)))
            (section43SpatialHeadMarginal F)))) := by
    rw [show
        (fun shell =>
          D.rootSmearedSpatialHermiteGeneratorFiniteShellOfOS
            i timeScale shell w F) =
          fun shell =>
            D.spatialHermiteGeneratorFiniteShellAffineRootSmearingOfOS
              i timeScale shell ξ
              (ξ i.bridgeGlobalIndex) F by
        funext shell
        exact
          D.rootSmearedSpatialHermiteGeneratorFiniteShellOfOS_positiveReal_eq_affineRootSmearing
            i timeScale shell ξ hbridge F]
    exact
      hreal_ξ timeScale hprofiles hleft hright hbridge.le F
  exact tendsto_nhds_unique hsum hreal_limit

/-- In common chronological coordinates, every generator split has the same
original-OS full-sum real edge for a caller-supplied current package. The
patch can be chosen inside any prescribed neighborhood of the origin. -/
theorem
    exists_radial_rootSmearedSpatialHermiteGeneratorSumOfOS_commonChronological_patch_all_splits_of_currentData_on
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (C : CommonTranslatedPositiveHeadSpatialSourceCurrentData
      (d := d) (k := k) A OS)
    (Q : Set (Fin k → ℝ))
    (hQ : Q ∈ 𝓝 0) :
    ∃ V : Set (Fin k → ℝ),
      IsOpen V ∧ V.Nonempty ∧
        V ⊆ Q ∧
        IsPositiveRadial V ∧
        (∀ i τ, τ ∈ V →
          generatorChronologicalParameterComplexCLE i
              (osiiPositiveRealTimeEmbed τ) ∈
            generatorSemigroupDomain i
              (D.left i).domain (D.right i).domain) ∧
        ∀ i τ, τ ∈ V → ∀ (timeScale : ℕ)
          (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ),
          D.rootSmearedSpatialHermiteGeneratorSumOfOS
              i timeScale
              (generatorChronologicalParameterComplexCLE i
                (osiiPositiveRealTimeEmbed τ)) F =
            C.current (section43NPointTimeSpatialTensor d k
              (SCV.translateSchwartz (-τ)
                (A.timeTest (timeScale + D.commonTailStart i)))
              (section43SpatialHeadMarginal F)) := by
  let hreal :=
    D.eventually_rootSmearedSpatialHermiteGeneratorSumOfOS_positiveReal_eq_translatedReducedTensor_uniform_scale_all_splits_of_currentData
      C
  letI : Fintype (GeneratorIndex k) :=
    Fintype.ofEquiv (Fin k) (GeneratorIndex.equivGap k).symm
  have hgood :
      {τ : Fin k → ℝ |
        ∀ i : GeneratorIndex k,
          (∀ timeScale,
            D.RootedTranslatedTimeProfilesPositive i timeScale
              (generatorChronologicalParameter i τ)) ∧
          i.leftRealCoordinates
              (generatorChronologicalParameter i τ) ∈
            (D.left i).realRegion ∧
          i.rightRealCoordinates
              (generatorChronologicalParameter i τ) ∈
            (D.right i).realRegion ∧
          ∀ (timeScale : ℕ)
            (hprofiles :
              D.RootedTranslatedTimeProfilesPositive i timeScale
                (generatorChronologicalParameter i τ))
            (hbridge :
              0 <
                generatorChronologicalParameter i τ
                  i.bridgeGlobalIndex),
            i.leftRealCoordinates
                (generatorChronologicalParameter i τ) ∈
                (D.left i).realRegion →
            i.rightRealCoordinates
                (generatorChronologicalParameter i τ) ∈
                (D.right i).realRegion →
            ∀ F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ,
              D.rootSmearedSpatialHermiteGeneratorSumOfOS
                  i timeScale
                  (osiiPositiveRealTimeEmbed
                    (generatorChronologicalParameter i τ)) F =
                C.current (section43NPointTimeSpatialTensor d k
                  (SCV.translateSchwartz
                    (-(generatorChronologicalParameter i
                      (generatorChronologicalParameter i τ)))
                    (A.timeTest
                      (timeScale + D.commonTailStart i)))
                  (section43SpatialHeadMarginal F))} ∈ 𝓝 0 := by
    change
      ∀ᶠ τ : Fin k → ℝ in 𝓝 0,
        ∀ i : GeneratorIndex k,
          (∀ timeScale,
            D.RootedTranslatedTimeProfilesPositive i timeScale
              (generatorChronologicalParameter i τ)) ∧
          i.leftRealCoordinates
              (generatorChronologicalParameter i τ) ∈
            (D.left i).realRegion ∧
          i.rightRealCoordinates
              (generatorChronologicalParameter i τ) ∈
            (D.right i).realRegion ∧
          ∀ (timeScale : ℕ)
            (hprofiles :
              D.RootedTranslatedTimeProfilesPositive i timeScale
                (generatorChronologicalParameter i τ))
            (hbridge :
              0 <
                generatorChronologicalParameter i τ
                  i.bridgeGlobalIndex),
            i.leftRealCoordinates
                (generatorChronologicalParameter i τ) ∈
                (D.left i).realRegion →
            i.rightRealCoordinates
                (generatorChronologicalParameter i τ) ∈
                (D.right i).realRegion →
            ∀ F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ,
              D.rootSmearedSpatialHermiteGeneratorSumOfOS
                  i timeScale
                  (osiiPositiveRealTimeEmbed
                    (generatorChronologicalParameter i τ)) F =
                C.current (section43NPointTimeSpatialTensor d k
                  (SCV.translateSchwartz
                    (-(generatorChronologicalParameter i
                      (generatorChronologicalParameter i τ)))
                    (A.timeTest
                      (timeScale + D.commonTailStart i)))
                  (section43SpatialHeadMarginal F))
    rw [Filter.eventually_all]
    intro i
    have hG :
        Tendsto (generatorChronologicalParameter i)
          (𝓝 (0 : Fin k → ℝ)) (𝓝 0) := by
      have hfun :
          generatorChronologicalParameter i =
            (generatorChronologicalParameterCLE i :
              (Fin k → ℝ) → (Fin k → ℝ)) := by
        funext τ
        exact (generatorChronologicalParameterCLE_apply i τ).symm
      rw [hfun]
      exact
        (generatorChronologicalParameterCLE i).continuous.tendsto'
          0 0 (map_zero (generatorChronologicalParameterCLE i))
    filter_upwards
      [hG.eventually
        (D.eventually_rootedTranslatedTimeProfilesPositive_uniform_scale i),
      hG.eventually
        ((GeneratorHermiteHilbertFieldFamilyData.tendsto_leftRealCoordinates_zero i
          ).eventually (D.left i).realRegion_nhds),
      hG.eventually
        ((GeneratorHermiteHilbertFieldFamilyData.tendsto_rightRealCoordinates_zero i
          ).eventually (D.right i).realRegion_nhds),
      hG.eventually (hreal i)] with τ hp hl hr hre
    exact ⟨hp, hl, hr, hre⟩
  have hgoodQ :
      ({τ : Fin k → ℝ |
        ∀ i : GeneratorIndex k,
          (∀ timeScale,
            D.RootedTranslatedTimeProfilesPositive i timeScale
              (generatorChronologicalParameter i τ)) ∧
          i.leftRealCoordinates
              (generatorChronologicalParameter i τ) ∈
            (D.left i).realRegion ∧
          i.rightRealCoordinates
              (generatorChronologicalParameter i τ) ∈
            (D.right i).realRegion ∧
          ∀ (timeScale : ℕ)
            (hprofiles :
              D.RootedTranslatedTimeProfilesPositive i timeScale
                (generatorChronologicalParameter i τ))
            (hbridge :
              0 <
                generatorChronologicalParameter i τ
                  i.bridgeGlobalIndex),
            i.leftRealCoordinates
                (generatorChronologicalParameter i τ) ∈
                (D.left i).realRegion →
            i.rightRealCoordinates
                (generatorChronologicalParameter i τ) ∈
                (D.right i).realRegion →
            ∀ F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ,
              D.rootSmearedSpatialHermiteGeneratorSumOfOS
                  i timeScale
                  (osiiPositiveRealTimeEmbed
                    (generatorChronologicalParameter i τ)) F =
                C.current (section43NPointTimeSpatialTensor d k
                  (SCV.translateSchwartz
                    (-(generatorChronologicalParameter i
                      (generatorChronologicalParameter i τ)))
                    (A.timeTest
                      (timeScale + D.commonTailStart i)))
                  (section43SpatialHeadMarginal F))} ∩ Q) ∈ 𝓝 0 :=
    Filter.inter_mem hgood hQ
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hgoodQ
  let τ₀ : Fin k → ℝ := fun _ => ε / 2
  have hτ₀_norm : ‖τ₀‖ < ε := by
    rw [pi_norm_lt_iff hε]
    intro j
    simp only [τ₀]
    rw [Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith
  have hτ₀_ball : τ₀ ∈ Metric.ball (0 : Fin k → ℝ) ε := by
    simpa [Metric.mem_ball, dist_zero_right] using hτ₀_norm
  have hτ₀_positive : τ₀ ∈ section43TimeStrictPositiveRegion k := by
    intro j
    exact half_pos hε
  let V : Set (Fin k → ℝ) :=
    Metric.ball (0 : Fin k → ℝ) ε ∩
      section43TimeStrictPositiveRegion k
  refine
    ⟨V,
      Metric.isOpen_ball.inter
        (isOpen_section43TimeStrictPositiveRegion k),
      ⟨τ₀, hτ₀_ball, hτ₀_positive⟩, ?_,
      isPositiveRadial_ball_inter_strictPositive ε, ?_, ?_⟩
  · intro τ hτ
    exact (hball hτ.1).2
  · intro i τ hτ
    rw [generatorChronologicalParameterComplexCLE_positiveRealTimeEmbed]
    have hprops := (hball hτ.1).1 i
    exact
      positiveRealTimeEmbed_mem_generatorSemigroupDomain
        i (generatorChronologicalParameter i τ)
        (by
          rw [generatorChronologicalParameter_bridge]
          exact hτ.2 i.bridgeGlobalIndex)
        ((D.left i).realRegion_to_domain
          (i.leftRealCoordinates
            (generatorChronologicalParameter i τ)) hprops.2.1)
        ((D.right i).realRegion_to_domain
          (i.rightRealCoordinates
            (generatorChronologicalParameter i τ)) hprops.2.2.1)
  intro i τ hτ timeScale F
  rw [generatorChronologicalParameterComplexCLE_positiveRealTimeEmbed]
  have hprops := (hball hτ.1).1 i
  have hre :=
    hprops.2.2.2 timeScale (hprops.1 timeScale)
      (by
        rw [generatorChronologicalParameter_bridge]
        exact hτ.2 i.bridgeGlobalIndex)
      hprops.2.1 hprops.2.2.1 F
  simpa using hre

/-- The scale-uniform full-sum comparison holds on an explicit nonempty open
positive-real patch under the original OS axioms, with all admissibility
hypotheses discharged. -/
theorem
    exists_common_rootSmearedSpatialHermiteGeneratorSumOfOS_positiveReal_patch
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k) :
    ∃ (L : SchwartzNPoint d k →L[ℂ] ℂ)
        (V : Set (Fin k → ℝ)),
      IsOpen V ∧ V.Nonempty ∧
        (∀ ξ ∈ V,
          osiiPositiveRealTimeEmbed ξ ∈
            generatorSemigroupDomain i
              (D.left i).domain (D.right i).domain) ∧
        ∀ ξ ∈ V, ∀ (timeScale : ℕ)
          (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ),
          D.rootSmearedSpatialHermiteGeneratorSumOfOS
              i timeScale (osiiPositiveRealTimeEmbed ξ) F =
            L (section43NPointTimeSpatialTensor d k
              (SCV.translateSchwartz
                (-(generatorChronologicalParameter i ξ))
                (A.timeTest (timeScale + D.commonTailStart i)))
              (section43SpatialHeadMarginal F)) := by
  obtain ⟨C⟩ :=
    A.nonempty_commonTranslatedPositiveHeadSpatialSourceCurrentData OS
  let L := C.current
  have hreal :=
    D.eventually_rootSmearedSpatialHermiteGeneratorSumOfOS_positiveReal_eq_translatedReducedTensor_uniform_scale_all_splits_of_currentData
      C i
  have hprofiles :=
    D.eventually_rootedTranslatedTimeProfilesPositive_uniform_scale i
  have hleft :=
    (GeneratorHermiteHilbertFieldFamilyData.tendsto_leftRealCoordinates_zero i
      ).eventually (D.left i).realRegion_nhds
  have hright :=
    (GeneratorHermiteHilbertFieldFamilyData.tendsto_rightRealCoordinates_zero i
      ).eventually (D.right i).realRegion_nhds
  have hgood :
      {ξ : Fin k → ℝ |
        (∀ timeScale,
          D.RootedTranslatedTimeProfilesPositive i timeScale ξ) ∧
        i.leftRealCoordinates ξ ∈ (D.left i).realRegion ∧
        i.rightRealCoordinates ξ ∈ (D.right i).realRegion ∧
        ∀ (timeScale : ℕ)
          (hprofiles :
            D.RootedTranslatedTimeProfilesPositive i timeScale ξ)
          (hbridge : 0 < ξ i.bridgeGlobalIndex),
          i.leftRealCoordinates ξ ∈ (D.left i).realRegion →
          i.rightRealCoordinates ξ ∈ (D.right i).realRegion →
          ∀ F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ,
            D.rootSmearedSpatialHermiteGeneratorSumOfOS
                i timeScale (osiiPositiveRealTimeEmbed ξ) F =
              L (section43NPointTimeSpatialTensor d k
                (SCV.translateSchwartz
                  (-(generatorChronologicalParameter i ξ))
                  (A.timeTest (timeScale + D.commonTailStart i)))
                (section43SpatialHeadMarginal F))} ∈ 𝓝 0 := by
    filter_upwards [hprofiles, hleft, hright, hreal]
      with ξ hp hl hr hreal_ξ
    exact ⟨hp, hl, hr, hreal_ξ⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hgood
  let ξ₀ : Fin k → ℝ :=
    fun j => if j = i.toGap then ε / 2 else 0
  have hξ₀_norm : ‖ξ₀‖ < ε := by
    rw [pi_norm_lt_iff hε]
    intro j
    by_cases hj : j = i.toGap
    · subst j
      simp only [ξ₀, if_pos]
      rw [Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      linarith
    · simpa [ξ₀, hj] using hε
  have hξ₀_ball : ξ₀ ∈ Metric.ball (0 : Fin k → ℝ) ε := by
    simpa [Metric.mem_ball, dist_zero_right] using hξ₀_norm
  let V : Set (Fin k → ℝ) :=
    Metric.ball (0 : Fin k → ℝ) ε ∩
      {ξ | 0 < ξ i.bridgeGlobalIndex}
  have hV_open : IsOpen V := by
    exact Metric.isOpen_ball.inter
      (isOpen_lt continuous_const
        (continuous_apply i.bridgeGlobalIndex))
  have hξ₀_bridge : 0 < ξ₀ i.bridgeGlobalIndex := by
    rw [GeneratorIndex.bridgeGlobalIndex_eq_toGap]
    simp [ξ₀, hε]
  refine ⟨L, V, hV_open, ⟨ξ₀, hξ₀_ball, hξ₀_bridge⟩, ?_, ?_⟩
  · intro ξ hξ
    have hprops := hball hξ.1
    exact
      positiveRealTimeEmbed_mem_generatorSemigroupDomain
        i ξ hξ.2
        ((D.left i).realRegion_to_domain
          (i.leftRealCoordinates ξ) hprops.2.1)
        ((D.right i).realRegion_to_domain
          (i.rightRealCoordinates ξ) hprops.2.2.1)
  intro ξ hξ timeScale F
  have hprops := hball hξ.1
  exact
    hprops.2.2.2 timeScale (hprops.1 timeScale) hξ.2
      hprops.2.1 hprops.2.2.1 F

/-- Packet scales of the full root-smeared holomorphic sum converge
distributionally on a nonempty positive-real patch to the chronological
pullback of one reduced Schwinger functional, using the original OS axioms. -/
theorem
    exists_tendsto_integral_rootSmearedSpatialHermiteGeneratorSumOfOS_positiveReal_mul
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    ∃ (L : SchwartzNPoint d k →L[ℂ] ℂ)
        (V : Set (Fin k → ℝ)),
      IsOpen V ∧ V.Nonempty ∧
        (∀ ξ ∈ V,
          osiiPositiveRealTimeEmbed ξ ∈
            generatorSemigroupDomain i
              (D.left i).domain (D.right i).domain) ∧
        ∀ φ : SchwartzMap (Fin k → ℝ) ℂ,
          SCV.SupportsInOpen (φ : (Fin k → ℝ) → ℂ) V →
            Tendsto
              (fun timeScale =>
                ∫ ξ : Fin k → ℝ,
                  D.rootSmearedSpatialHermiteGeneratorSumOfOS
                      i timeScale
                      (osiiPositiveRealTimeEmbed ξ) F *
                    φ ξ)
              atTop
              (𝓝
                (L (section43NPointTimeSpatialTensor d k
                  (generatorChronologicalPullbackTest i anchor φ)
                  (section43SpatialHeadMarginal F)))) := by
  obtain ⟨L, V, hV_open, hV_ne, hV_domain, hreal⟩ :=
    D.exists_common_rootSmearedSpatialHermiteGeneratorSumOfOS_positiveReal_patch
      i
  refine ⟨L, V, hV_open, hV_ne, hV_domain, ?_⟩
  intro φ hφ
  have heq :
      (fun timeScale =>
        ∫ ξ : Fin k → ℝ,
          D.rootSmearedSpatialHermiteGeneratorSumOfOS
              i timeScale
              (osiiPositiveRealTimeEmbed ξ) F *
            φ ξ) =
        fun timeScale =>
          ∫ ξ : Fin k → ℝ,
            L (section43NPointTimeSpatialTensor d k
                (SCV.translateSchwartz
                  (-(generatorChronologicalParameter i ξ))
                  (A.timeTest
                    (timeScale + D.commonTailStart i)))
                (section43SpatialHeadMarginal F)) *
              φ ξ := by
    funext timeScale
    apply integral_congr_ae
    filter_upwards with ξ
    by_cases hξ : ξ ∈ tsupport (φ : (Fin k → ℝ) → ℂ)
    · rw [hreal ξ (hφ.2 hξ) timeScale F]
    · have hφ_zero : φ ξ = 0 :=
        image_eq_zero_of_notMem_tsupport hξ
      simp [hφ_zero]
  rw [heq]
  exact
    A.tendsto_integral_translatedReducedTensor_chronological_mul
      i (D.commonTailStart i) L F φ hφ.1

/-- After reparameterizing every split by common chronological coordinates,
all original-OS packet-scale full sums converge distributionally to a
caller-supplied reduced Schwinger current on one common radial patch. -/
theorem
    exists_radial_tendsto_integral_rootSmearedSpatialHermiteGeneratorSumOfOS_commonChronological_mul_all_splits_of_currentData_on
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (C : CommonTranslatedPositiveHeadSpatialSourceCurrentData
      (d := d) (k := k) A OS)
    (Q : Set (Fin k → ℝ))
    (hQ : Q ∈ 𝓝 0) :
    ∃ V : Set (Fin k → ℝ),
      IsOpen V ∧ V.Nonempty ∧
        V ⊆ Q ∧
        IsPositiveRadial V ∧
        (∀ i τ, τ ∈ V →
          generatorChronologicalParameterComplexCLE i
              (osiiPositiveRealTimeEmbed τ) ∈
            generatorSemigroupDomain i
              (D.left i).domain (D.right i).domain) ∧
        ∀ (i : GeneratorIndex k)
          (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
          (φ : SchwartzMap (Fin k → ℝ) ℂ),
          SCV.SupportsInOpen
              (φ : (Fin k → ℝ) → ℂ) V →
            Tendsto
              (fun timeScale =>
                ∫ τ : Fin k → ℝ,
                  D.rootSmearedSpatialHermiteGeneratorSumOfOS
                      i timeScale
                      (generatorChronologicalParameterComplexCLE i
                        (osiiPositiveRealTimeEmbed τ)) F *
                    φ τ)
              atTop
              (𝓝
                (C.current (section43NPointTimeSpatialTensor d k
                  (SCV.translateSchwartz (-anchor) φ)
                  (section43SpatialHeadMarginal F)))) := by
  obtain
    ⟨V, hV_open, hV_ne, hVQ, hV_radial, hV_domain, hreal⟩ :=
    D.exists_radial_rootSmearedSpatialHermiteGeneratorSumOfOS_commonChronological_patch_all_splits_of_currentData_on
      C Q hQ
  refine ⟨V, hV_open, hV_ne, hVQ, hV_radial, hV_domain, ?_⟩
  intro i F φ hφ
  have heq :
      (fun timeScale =>
        ∫ τ : Fin k → ℝ,
          D.rootSmearedSpatialHermiteGeneratorSumOfOS
              i timeScale
              (generatorChronologicalParameterComplexCLE i
                (osiiPositiveRealTimeEmbed τ)) F *
            φ τ) =
        fun timeScale =>
          ∫ τ : Fin k → ℝ,
            C.current (section43NPointTimeSpatialTensor d k
                (SCV.translateSchwartz (-τ)
                  (A.timeTest
                    (timeScale + D.commonTailStart i)))
                (section43SpatialHeadMarginal F)) *
              φ τ := by
    funext timeScale
    apply integral_congr_ae
    filter_upwards with τ
    by_cases hτ : τ ∈ tsupport (φ : (Fin k → ℝ) → ℂ)
    · rw [hreal i τ (hφ.2 hτ) timeScale F]
    · have hφ_zero : φ τ = 0 :=
        image_eq_zero_of_notMem_tsupport hτ
      simp [hφ_zero]
  rw [heq]
  exact
    A.tendsto_integral_translatedReducedTensor_commonChronological_mul
      i (D.commonTailStart i) C.current F φ hφ.1

/-- Compatibility wrapper for the radial original-OS common-current trace. -/
theorem
    exists_radial_tendsto_integral_rootSmearedSpatialHermiteGeneratorSum_commonChronological_mul_all_splits_of_currentData_on
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (_lgc : OSLinearGrowthCondition d OS)
    (C : CommonTranslatedPositiveHeadSpatialSourceCurrentData
      (d := d) (k := k) A OS)
    (Q : Set (Fin k → ℝ))
    (hQ : Q ∈ 𝓝 0) :
    ∃ V : Set (Fin k → ℝ),
      IsOpen V ∧ V.Nonempty ∧
        V ⊆ Q ∧
        IsPositiveRadial V ∧
        (∀ i τ, τ ∈ V →
          generatorChronologicalParameterComplexCLE i
              (osiiPositiveRealTimeEmbed τ) ∈
            generatorSemigroupDomain i
              (D.left i).domain (D.right i).domain) ∧
        ∀ (i : GeneratorIndex k)
          (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
          (φ : SchwartzMap (Fin k → ℝ) ℂ),
          SCV.SupportsInOpen
              (φ : (Fin k → ℝ) → ℂ) V →
            Tendsto
              (fun timeScale =>
                ∫ τ : Fin k → ℝ,
                  D.rootSmearedSpatialHermiteGeneratorSum
                      _lgc i timeScale
                      (generatorChronologicalParameterComplexCLE i
                        (osiiPositiveRealTimeEmbed τ)) F *
                    φ τ)
              atTop
              (𝓝
                (C.current (section43NPointTimeSpatialTensor d k
                  (SCV.translateSchwartz (-anchor) φ)
                  (section43SpatialHeadMarginal F)))) :=
  D.exists_radial_tendsto_integral_rootSmearedSpatialHermiteGeneratorSumOfOS_commonChronological_mul_all_splits_of_currentData_on
    C Q hQ

end RootedA0BlockContinuousTranslationData

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
