/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.SCV.HeadFiberFubini
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketRootedTimeSlice
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVCanonicalReducedSchwinger
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVDifferenceReducedSupport














noncomputable section

open Complex Filter MeasureTheory Set
open scoped Classical Topology

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData
namespace RootedA0BlockContinuousTranslationData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}
  {OS : OsterwalderSchraderAxioms d}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
  {R : TripleConvolutionRootData I}

private theorem reducedTimeProjection_eq_tail_orderedTime
    (x : NPointDomain d (k + 1)) :
    reducedTimeProjectionCLM d k x =
      Fin.tail
        (section43QTime (d := d) (n := k + 1)
          (section43DiffCoordRealCLE d (k + 1) x)) := by
  ext i
  change
    x i.succ 0 - x i.castSucc 0 =
      section43DiffCoordRealCLE d (k + 1) x i.succ 0
  rw [section43DiffCoordRealCLE_apply]
  have hpred :
      (⟨i.succ.val - 1, by omega⟩ : Fin (k + 1)) =
        i.castSucc := by
    apply Fin.ext
    simp
  rw [dif_neg (by simp), hpred]

/-- The reduced-time coordinate of an ordered time/spatial tensor lies in
the tail projection of its full difference-time support. -/
theorem orderedTimeSpatialTensor_reducedTimeProjection_mem_tail_tsupport
    (φ : SchwartzMap (Fin (k + 1) → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (x : NPointDomain d (k + 1))
    (hx :
      x ∈ tsupport
        ((section43OrderedPullbackTimeSpatialTensorCLM
          d (k + 1) χ φ : SchwartzNPoint d (k + 1)) :
            NPointDomain d (k + 1) → ℂ)) :
    reducedTimeProjectionCLM d k x ∈
      Fin.tail '' tsupport (φ : (Fin (k + 1) → ℝ) → ℂ) := by
  have htime :
      section43QTime (d := d) (n := k + 1)
          (section43DiffCoordRealCLE d (k + 1) x) ∈
        tsupport (φ : (Fin (k + 1) → ℝ) → ℂ) := by
    exact
      tsupport_section43NPointTimeSpatialTensor_subset_time_preimage
        d (k + 1) φ χ
        (tsupport_comp_subset_preimage
          ((section43NPointTimeSpatialTensor d (k + 1) φ χ :
            SchwartzNPoint d (k + 1)) :
              NPointDomain d (k + 1) → ℂ)
          (section43DiffCoordRealCLE d (k + 1)).continuous hx)
  rw [reducedTimeProjection_eq_tail_orderedTime]
  exact ⟨_, htime, rfl⟩

/-- Equality transport of time Schwartz data is the same finite-coordinate
pullback used by the generator global-profile API. -/
theorem section43TimeSchwartzTransport_eq_finCongrPullback
    {n m : ℕ}
    (h : n = m)
    (φ : SchwartzMap (Fin n → ℝ) ℂ) :
    section43TimeSchwartzTransport h φ =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (ContinuousLinearEquiv.piCongrLeft ℝ
          (fun _ : Fin n => ℝ)
          (finCongr h.symm))
        φ := by
  subst m
  rfl

/-- One neighborhood of the generator origin keeps every packet scale inside
any prescribed open neighborhood of the common anchored carrier. -/
theorem eventually_translatedTimeTest_tsupport_subset
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k)
    (U : Set (Fin k → ℝ))
    (hU_open : IsOpen U)
    (hcarrier : A.carrierData.carrier ⊆ U) :
    ∀ᶠ ξ : Fin k → ℝ in 𝓝 0,
      ∀ N : ℕ,
        tsupport
            ((SCV.translateSchwartz
              (-(generatorChronologicalParameter i ξ))
              (A.timeTest N) :
                SchwartzMap (Fin k → ℝ) ℂ) :
              (Fin k → ℝ) → ℂ) ⊆
          U := by
  obtain ⟨r, hr_pos, hr_sub⟩ :=
    A.carrierData.carrier_compact.exists_cthickening_subset_open
      hU_open hcarrier
  have hcontinuous :
      Continuous
        (fun ξ : Fin k → ℝ =>
          -(generatorChronologicalParameter i ξ)) := by
    apply continuous_pi
    intro j
    change Continuous
      (fun ξ : Fin k → ℝ =>
        -(if j.val < i.bridgeGlobalIndex.val then -ξ j else ξ j))
    split_ifs <;> fun_prop
  have hzero :
      -(generatorChronologicalParameter i (0 : Fin k → ℝ)) = 0 := by
    ext j
    simp [generatorChronologicalParameter]
  have hball_nhds :
      Metric.ball (0 : Fin k → ℝ) r ∈
        𝓝 (-(generatorChronologicalParameter i (0 : Fin k → ℝ))) := by
    rw [hzero]
    exact
      Metric.isOpen_ball.mem_nhds
        (Metric.mem_ball_self hr_pos)
  filter_upwards
    [hcontinuous.continuousAt.eventually hball_nhds]
      with ξ hξ
  intro N x hx
  rw [tsupport_translateSchwartz_eq_preimage] at hx
  have hxcarrier :
      x + -(generatorChronologicalParameter i ξ) ∈
        A.carrierData.carrier := by
    exact
      A.carrierData.translated_support N
        (by simpa [AnchoredPacketTimeShellFamilyData.timeTest] using hx)
  apply hr_sub
  apply Metric.mem_cthickening_of_dist_le
    x (x + -(generatorChronologicalParameter i ξ))
    r A.carrierData.carrier hxcarrier
  have hnorm :
      ‖-(generatorChronologicalParameter i ξ)‖ < r := by
    simpa [Metric.mem_ball, dist_zero_right] using hξ
  rw [dist_eq_norm]
  have hdiff :
      x - (x + -(generatorChronologicalParameter i ξ)) =
        generatorChronologicalParameter i ξ := by
    module
  rw [hdiff]
  simpa only [norm_neg] using le_of_lt hnorm

/-- The centered rooted generator source, reindexed to the common
`k + 1`-point arity and with the split spatial chart canceled at the input. -/
noncomputable def rootedGeneratorFullSource
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (t : ℝ)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    SchwartzNPoint d (k + 1) :=
  GeneratorHermiteHilbertFieldFamilyData.reindexSchwartzNPointCLM
    (d := d) (finCongr i.absoluteCard_eq.symm)
    (axisPairGlobalAbsoluteSpatialSourceCLM
      i.n i.m
      (D.rootedLeftTranslatedTimeProfile i timeScale 0)
      (D.rootedRightTranslatedTimeProfile i timeScale 0)
      (D.rootedLeftTranslatedCommonShift i timeScale 0)
      t
      (generatorSplitSpatialPullbackCLM i
        (GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
          (d := d) i F)))

/-- The centered rooted generator source with its ordered-positive
zero-diagonal certificate attached. -/
noncomputable def rootedGeneratorSourceZero
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (hpositive :
      D.RootedTranslatedTimeProfilesPositive i timeScale 0)
    (t : ℝ)
    (ht : 0 ≤ t)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    ZeroDiagonalSchwartz d (k + 1) :=
  GeneratorHermiteHilbertFieldFamilyData.reindexZeroDiagonalSchwartzCLM
    (d := d) (finCongr i.absoluteCard_eq.symm)
    (axisPairGlobalAbsoluteSpatialSourceZeroCLM
      i.n i.m i.hn i.hm
      (D.rootedLeftTranslatedTimeProfile i timeScale 0)
      hpositive.1
      (D.rootedRightTranslatedTimeProfile i timeScale 0)
      hpositive.2
      (D.rootedLeftTranslatedCommonShift i timeScale 0)
      t ht
      (D.rootedLeftTranslatedCommonShift_span i timeScale 0)
      (generatorSplitSpatialPullbackCLM i
        (GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
          (d := d) i F)))

set_option maxRecDepth 4000 in
@[simp] theorem rootedGeneratorSourceZero_coe
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (hpositive :
      D.RootedTranslatedTimeProfilesPositive i timeScale 0)
    (t : ℝ)
    (ht : 0 ≤ t)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    (D.rootedGeneratorSourceZero i timeScale hpositive t ht F).1 =
      D.rootedGeneratorFullSource i timeScale t F := rfl

end RootedA0BlockContinuousTranslationData
end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
