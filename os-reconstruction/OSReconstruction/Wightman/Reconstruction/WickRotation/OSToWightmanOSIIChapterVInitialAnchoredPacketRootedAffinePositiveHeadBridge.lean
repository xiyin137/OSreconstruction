/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketRootedAffineSourceCurrent
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialPositiveProductBasepointFamily











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

private theorem continuous_generatorChronologicalParameter_bridge
    (i : GeneratorIndex k) :
    Continuous
      (fun ξ : Fin k → ℝ =>
        generatorChronologicalParameter i ξ) := by
  apply continuous_pi
  intro j
  by_cases hj : j.val < i.bridgeGlobalIndex.val
  · change Continuous
      (fun ξ : Fin k → ℝ =>
        if j.val < i.bridgeGlobalIndex.val then -ξ j else ξ j)
    simp only [if_pos hj]
    change Continuous (-fun ξ : Fin k → ℝ => ξ j)
    exact (continuous_apply j).neg
  · change Continuous
      (fun ξ : Fin k → ℝ =>
        if j.val < i.bridgeGlobalIndex.val then -ξ j else ξ j)
    simp only [if_neg hj]
    change Continuous (fun ξ : Fin k → ℝ => ξ j)
    exact continuous_apply j

set_option maxRecDepth 4000 in
/-- At a fixed affine parameter, one canonical reduced functional represents
both every positive-root slice and the translated positive-head packet at the
corresponding physical scale. -/
theorem exists_rootedAffinePositiveHeadCommonSourceCurrent
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (ξ : Fin k → ℝ)
    (hprofiles :
      D.RootedTranslatedTimeProfilesPositive i timeScale ξ)
    (c : ℝ)
    (hc : 0 ≤ c)
    (htail :
      tsupport
          ((SCV.translateSchwartz
            (-(generatorChronologicalParameter i ξ))
            (A.timeTest (timeScale + D.commonTailStart i)) :
              SchwartzMap (Fin k → ℝ) ℂ) :
                (Fin k → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion k) :
    ∃ L : SchwartzNPoint d k →L[ℂ] ℂ,
      (∀ (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ),
        ∀ (t : ℝ),
          t ∈ tsupport
              (D.semigroupBridgeRootWeight i timeScale : ℝ → ℂ) →
          ∀ (ht : 0 < t),
          generatorSplitAbsoluteSpatialSchwingerCLM
              OS i
              (D.rootedLeftTranslatedTimeProfile i timeScale ξ)
              hprofiles.1
              (D.rootedRightTranslatedTimeProfile i timeScale ξ)
              hprofiles.2
              (D.rootedLeftTranslatedCommonShift i timeScale ξ)
              (c + t) (add_nonneg hc ht.le)
              (D.rootedLeftTranslatedCommonShift_span i timeScale ξ)
              (GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
                (d := d) i F) =
            L (section43NPointTimeSpatialTensor d k
              (SCV.sliceIntegral
                (section43TimeSchwartzTransport i.pointArity_add
                  (osiiAxisPairGlobalTimeCutoff i.n i.m
                    (D.rootedLeftTranslatedTimeProfile i timeScale ξ).conj
                    (D.rootedRightTranslatedTimeProfile i timeScale ξ)
                    (D.rootedLeftTranslatedCommonShift i timeScale ξ)
                    (c + t))))
              (section43SpatialHeadMarginal F))) ∧
      (∀ F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ,
        L (section43NPointTimeSpatialTensor d k
            (SCV.translateSchwartz
              (-(generatorChronologicalParameter i ξ))
              (A.timeTest (timeScale + D.commonTailStart i)))
            (section43SpatialHeadMarginal F)) =
          OS.S (k + 1)
            (ZeroDiagonalSchwartz.ofClassical
              (translateSchwartzConfiguration
                (sourceParameterDisplacementCLM
                  (fun j : Fin k =>
                    chronologicalTimeSourceDirection (d := d) j)
                  (generatorChronologicalParameter i ξ))
                (A.positiveHeadSpatialSource
                  (timeScale + D.commonTailStart i) F).1))) := by
  obtain ⟨J, hJ_compact, hJ_positive, hroot_support⟩ :=
    D.exists_semigroupBridgeRootWeight_uniformCompactPositiveSupport i
  let rootFamily :
      J × SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ →
        SchwartzNPoint d (k + 1) :=
    fun p =>
      D.rootedAffineGeneratorFullSource
        i timeScale ξ c p.1.1 p.2
  let headFamily :
      SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ →
        SchwartzNPoint d (k + 1) :=
    fun F =>
      translateSchwartzConfiguration
        (sourceParameterDisplacementCLM
          (fun j : Fin k =>
            chronologicalTimeSourceDirection (d := d) j)
          (generatorChronologicalParameter i ξ))
        (A.positiveHeadSpatialSource
          (timeScale + D.commonTailStart i) F).1
  let sourceFamily :
      Sum
          (J × SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
          (SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) →
        SchwartzNPoint d (k + 1) :=
    Sum.elim rootFamily headFamily
  have hroot :
      HasUniformCompactStrictPositiveReducedTimeSupport rootFamily := by
    exact
      D.rootedAffineGeneratorFullSource_hasUniformCompactStrictPositiveReducedTimeSupport
        i timeScale ξ hprofiles c hc J hJ_compact hJ_positive
  have hhead :
      HasUniformCompactStrictPositiveReducedTimeSupport headFamily := by
    exact
      A.translatedPositiveHeadSpatialSource_hasUniformCompactStrictPositiveReducedTimeSupport
        (timeScale + D.commonTailStart i)
        (generatorChronologicalParameter i ξ) htail
  have hsourceFamily :
      HasUniformCompactStrictPositiveReducedTimeSupport sourceFamily := by
    simpa [sourceFamily] using hroot.sum hhead
  obtain ⟨eta, heta, _heta_compact, U, hU, hrecover⟩ :=
    exists_canonicalReducedTimeCutoffSchwingerCLM_family_displacement_germ
      OS sourceFamily hsourceFamily
      (fun _ : Fin 0 → ℝ => (0 : NPointDomain d (k + 1)))
      continuous_const rfl
  let L : SchwartzNPoint d k →L[ℂ] ℂ :=
    canonicalReducedTimeCutoffSchwingerCLM OS eta heta
  refine ⟨L, ?_, ?_⟩
  · intro F t ht_support ht
    have htJ : t ∈ J :=
      hroot_support timeScale ht_support
    let jt : J := ⟨t, htJ⟩
    have hzeroU : (0 : Fin 0 → ℝ) ∈ U :=
      mem_of_mem_nhds hU
    have hrecover_t :
        L (diffVarReduction d k
            (D.rootedAffineGeneratorFullSource
              i timeScale ξ c t F)) =
          OS.S (k + 1)
            (ZeroDiagonalSchwartz.ofClassical
              (D.rootedAffineGeneratorFullSource
                i timeScale ξ c t F)) := by
      simpa [L, sourceFamily, rootFamily, jt] using
        (hrecover (Sum.inl (jt, F)) (0 : Fin 0 → ℝ) hzeroU).2.1
    let hct : 0 ≤ c + t := add_nonneg hc ht.le
    calc
      generatorSplitAbsoluteSpatialSchwingerCLM
            OS i
            (D.rootedLeftTranslatedTimeProfile i timeScale ξ)
            hprofiles.1
            (D.rootedRightTranslatedTimeProfile i timeScale ξ)
            hprofiles.2
            (D.rootedLeftTranslatedCommonShift i timeScale ξ)
            (c + t) hct
            (D.rootedLeftTranslatedCommonShift_span i timeScale ξ)
            (GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
              (d := d) i F) =
          OS.S (k + 1)
            (D.rootedAffineGeneratorSourceZero
              i timeScale ξ hprofiles c t hct F) :=
        D.generatorSplitAbsoluteSpatialSchwingerCLM_eq_rootedAffineGeneratorSourceZero
          i timeScale ξ hprofiles c t hct F
      _ = OS.S (k + 1)
            (ZeroDiagonalSchwartz.ofClassical
              (D.rootedAffineGeneratorFullSource
                i timeScale ξ c t F)) := by
        congr 1
        apply SetCoe.ext
        rw [ZeroDiagonalSchwartz.coe_ofClassical_of_vanishes
          (D.rootedAffineGeneratorFullSource
            i timeScale ξ c t F)
          (D.rootedAffineGeneratorSourceZero
            i timeScale ξ hprofiles c t hct F).2]
        exact D.rootedAffineGeneratorSourceZero_coe
          i timeScale ξ hprofiles c t hct F
      _ = L (diffVarReduction d k
            (D.rootedAffineGeneratorFullSource
              i timeScale ξ c t F)) :=
        hrecover_t.symm
      _ = L (section43NPointTimeSpatialTensor d k
            (SCV.sliceIntegral
              (section43TimeSchwartzTransport i.pointArity_add
                (osiiAxisPairGlobalTimeCutoff i.n i.m
                  (D.rootedLeftTranslatedTimeProfile i timeScale ξ).conj
                  (D.rootedRightTranslatedTimeProfile i timeScale ξ)
                  (D.rootedLeftTranslatedCommonShift i timeScale ξ)
                  (c + t))))
            (section43SpatialHeadMarginal F)) := by
        rw [D.diffVarReduction_rootedAffineGeneratorFullSource]
  · intro F
    have hzeroU : (0 : Fin 0 → ℝ) ∈ U :=
      mem_of_mem_nhds hU
    have hrecover_head :
        L (diffVarReduction d k
            (translateSchwartzConfiguration
              (sourceParameterDisplacementCLM
                (fun j : Fin k =>
                  chronologicalTimeSourceDirection (d := d) j)
                (generatorChronologicalParameter i ξ))
              (A.positiveHeadSpatialSource
                (timeScale + D.commonTailStart i) F).1)) =
          OS.S (k + 1)
            (ZeroDiagonalSchwartz.ofClassical
              (translateSchwartzConfiguration
                (sourceParameterDisplacementCLM
                  (fun j : Fin k =>
                    chronologicalTimeSourceDirection (d := d) j)
                  (generatorChronologicalParameter i ξ))
                (A.positiveHeadSpatialSource
                  (timeScale + D.commonTailStart i) F).1)) := by
      simpa [L, sourceFamily, headFamily] using
        (hrecover (Sum.inr F) (0 : Fin 0 → ℝ) hzeroU).2.1
    rw [diffVarReduction_translateSchwartzConfiguration,
      A.diffVarReduction_positiveHeadSpatialSource,
      translate_reducedTimeSpatialTensor_chronological] at hrecover_head
    exact hrecover_head

/-- The affine root-smearing endpoint is the translated positive-head
Schwinger value, not merely the value of an unrelated reduced functional. -/
theorem
    spatialHermiteGeneratorAffineRootSmearingLimit_eq_translatedPositiveHeadSchwinger
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (ξ : Fin k → ℝ)
    (hprofiles :
      D.RootedTranslatedTimeProfilesPositive i timeScale ξ)
    (hbridge : 0 ≤ ξ i.bridgeGlobalIndex)
    (htail :
      tsupport
          ((SCV.translateSchwartz
            (-(generatorChronologicalParameter i ξ))
            (A.timeTest (timeScale + D.commonTailStart i)) :
              SchwartzMap (Fin k → ℝ) ℂ) :
                (Fin k → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion k)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    D.spatialHermiteGeneratorAffineRootSmearingLimit
        i timeScale ξ hprofiles
        (ξ i.bridgeGlobalIndex) hbridge F =
      OS.S (k + 1)
        (ZeroDiagonalSchwartz.ofClassical
          (translateSchwartzConfiguration
            (sourceParameterDisplacementCLM
              (fun j : Fin k =>
                chronologicalTimeSourceDirection (d := d) j)
              (generatorChronologicalParameter i ξ))
            (A.positiveHeadSpatialSource
              (timeScale + D.commonTailStart i) F).1)) := by
  obtain ⟨L, hroot, hhead⟩ :=
    D.exists_rootedAffinePositiveHeadCommonSourceCurrent
      i timeScale ξ hprofiles
      (ξ i.bridgeGlobalIndex) hbridge htail
  calc
    D.spatialHermiteGeneratorAffineRootSmearingLimit
        i timeScale ξ hprofiles
        (ξ i.bridgeGlobalIndex) hbridge F =
      L (section43NPointTimeSpatialTensor d k
        (SCV.translateSchwartz
          (-(generatorChronologicalParameter i ξ))
          (A.timeTest (timeScale + D.commonTailStart i)))
        (section43SpatialHeadMarginal F)) :=
      D.spatialHermiteGeneratorAffineRootSmearingLimit_eq_translatedReducedTensor_of_sourceCurrent
        i timeScale ξ hprofiles hbridge F L (hroot F)
    _ = OS.S (k + 1)
        (ZeroDiagonalSchwartz.ofClassical
          (translateSchwartzConfiguration
            (sourceParameterDisplacementCLM
              (fun j : Fin k =>
                chronologicalTimeSourceDirection (d := d) j)
              (generatorChronologicalParameter i ξ))
            (A.positiveHeadSpatialSource
              (timeScale + D.commonTailStart i) F).1)) :=
      hhead F

private theorem
    eventually_spatialHermiteGeneratorAffineRootSmearingLimit_eq_translatedReducedTensor_of_commonCurrent
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (L : SchwartzNPoint d k →L[ℂ] ℂ)
    (hcommon :
      ∀ᶠ u : Fin k → ℝ in 𝓝 0,
        ∀ (N : ℕ)
          (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ),
          L (section43NPointTimeSpatialTensor d k
              (SCV.translateSchwartz (-u) (A.timeTest N))
              (section43SpatialHeadMarginal F)) =
            OS.S (k + 1)
              (ZeroDiagonalSchwartz.ofClassical
                (translateSchwartzConfiguration
                  (sourceParameterDisplacementCLM
                    (fun j : Fin k =>
                      chronologicalTimeSourceDirection (d := d) j) u)
                  (A.positiveHeadSpatialSource N F).1)))
    (i : GeneratorIndex k) :
    ∀ᶠ ξ : Fin k → ℝ in 𝓝 0,
      ∀ (timeScale : ℕ)
        (hprofiles :
          D.RootedTranslatedTimeProfilesPositive i timeScale ξ)
        (hbridge : 0 ≤ ξ i.bridgeGlobalIndex)
        (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ),
        D.spatialHermiteGeneratorAffineRootSmearingLimit
            i timeScale ξ hprofiles
            (ξ i.bridgeGlobalIndex) hbridge F =
          L (section43NPointTimeSpatialTensor d k
            (SCV.translateSchwartz
              (-(generatorChronologicalParameter i ξ))
              (A.timeTest (timeScale + D.commonTailStart i)))
            (section43SpatialHeadMarginal F)) := by
  have hparameter_zero :
      generatorChronologicalParameter i (0 : Fin k → ℝ) = 0 := by
    ext j
    simp [generatorChronologicalParameter]
  have hparameter_tendsto :
      Tendsto
        (fun ξ : Fin k → ℝ =>
          generatorChronologicalParameter i ξ)
        (𝓝 0) (𝓝 0) := by
    have hcontinuousAt :
        ContinuousAt
          (fun ξ : Fin k → ℝ =>
            generatorChronologicalParameter i ξ)
          (0 : Fin k → ℝ) :=
      (continuous_generatorChronologicalParameter_bridge i).continuousAt
    change
      Tendsto
        (fun ξ : Fin k → ℝ =>
          generatorChronologicalParameter i ξ)
        (𝓝 0)
        (𝓝 (generatorChronologicalParameter i (0 : Fin k → ℝ)))
      at hcontinuousAt
    rw [hparameter_zero] at hcontinuousAt
    exact hcontinuousAt
  have hcommon_parameter :
      ∀ᶠ ξ : Fin k → ℝ in 𝓝 0,
        ∀ (N : ℕ)
          (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ),
          L (section43NPointTimeSpatialTensor d k
              (SCV.translateSchwartz
                (-(generatorChronologicalParameter i ξ))
                (A.timeTest N))
              (section43SpatialHeadMarginal F)) =
            OS.S (k + 1)
              (ZeroDiagonalSchwartz.ofClassical
                (translateSchwartzConfiguration
                  (sourceParameterDisplacementCLM
                    (fun j : Fin k =>
                      chronologicalTimeSourceDirection (d := d) j)
                    (generatorChronologicalParameter i ξ))
                  (A.positiveHeadSpatialSource N F).1)) :=
    hparameter_tendsto.eventually hcommon
  have htail :
      ∀ᶠ ξ : Fin k → ℝ in 𝓝 0,
        ∀ N : ℕ,
          tsupport
              ((SCV.translateSchwartz
                (-(generatorChronologicalParameter i ξ))
                (A.timeTest N) :
                  SchwartzMap (Fin k → ℝ) ℂ) :
                    (Fin k → ℝ) → ℂ) ⊆
            section43TimeStrictPositiveRegion k :=
    eventually_translatedTimeTest_tsupport_subset A i
      (section43TimeStrictPositiveRegion k)
      (isOpen_section43TimeStrictPositiveRegion k)
      A.carrierData.carrier_positive
  filter_upwards [hcommon_parameter, htail]
    with ξ hcommon_ξ htail_ξ
  intro timeScale hprofiles hbridge F
  calc
    D.spatialHermiteGeneratorAffineRootSmearingLimit
        i timeScale ξ hprofiles
        (ξ i.bridgeGlobalIndex) hbridge F =
      OS.S (k + 1)
        (ZeroDiagonalSchwartz.ofClassical
          (translateSchwartzConfiguration
            (sourceParameterDisplacementCLM
              (fun j : Fin k =>
                chronologicalTimeSourceDirection (d := d) j)
              (generatorChronologicalParameter i ξ))
            (A.positiveHeadSpatialSource
              (timeScale + D.commonTailStart i) F).1)) :=
      D.spatialHermiteGeneratorAffineRootSmearingLimit_eq_translatedPositiveHeadSchwinger
        i timeScale ξ hprofiles hbridge
        (htail_ξ (timeScale + D.commonTailStart i)) F
    _ = L (section43NPointTimeSpatialTensor d k
        (SCV.translateSchwartz
          (-(generatorChronologicalParameter i ξ))
          (A.timeTest (timeScale + D.commonTailStart i)))
        (section43SpatialHeadMarginal F)) :=
      (hcommon_ξ (timeScale + D.commonTailStart i) F).symm

/-- Any retained translated positive-head current package works before the
generator split is chosen. This is the non-choice interface needed when the
current has already been matched to a predecessor continuation stage. -/
theorem
    eventually_spatialHermiteGeneratorAffineRootSmearingLimit_eq_translatedReducedTensor_of_currentData
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (C : CommonTranslatedPositiveHeadSpatialSourceCurrentData
      (d := d) (k := k) A OS) :
    ∀ i : GeneratorIndex k,
      ∀ᶠ ξ : Fin k → ℝ in 𝓝 0,
        ∀ (timeScale : ℕ)
          (hprofiles :
            D.RootedTranslatedTimeProfilesPositive i timeScale ξ)
          (hbridge : 0 ≤ ξ i.bridgeGlobalIndex)
          (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ),
          D.spatialHermiteGeneratorAffineRootSmearingLimit
              i timeScale ξ hprofiles
              (ξ i.bridgeGlobalIndex) hbridge F =
            C.current (section43NPointTimeSpatialTensor d k
              (SCV.translateSchwartz
                (-(generatorChronologicalParameter i ξ))
                (A.timeTest (timeScale + D.commonTailStart i)))
              (section43SpatialHeadMarginal F)) :=
  fun i =>
    D.eventually_spatialHermiteGeneratorAffineRootSmearingLimit_eq_translatedReducedTensor_of_commonCurrent
      C.current C.eventually_recover i

/-- Finite-shell affine convergence for a caller-supplied translated
positive-head current package, using only the original OS axioms. -/
theorem
    tendsto_spatialHermiteGeneratorFiniteShellAffineRootSmearingOfOS_uniform_scale_all_splits_of_currentData
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (C : CommonTranslatedPositiveHeadSpatialSourceCurrentData
      (d := d) (k := k) A OS) :
    ∀ i : GeneratorIndex k,
      ∀ᶠ ξ : Fin k → ℝ in 𝓝 0,
        ∀ (timeScale : ℕ)
          (hprofiles :
            D.RootedTranslatedTimeProfilesPositive i timeScale ξ),
          i.leftRealCoordinates ξ ∈ (D.left i).realRegion →
          i.rightRealCoordinates ξ ∈ (D.right i).realRegion →
          ∀ (hbridge : 0 ≤ ξ i.bridgeGlobalIndex)
            (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ),
            Tendsto
              (fun shell =>
                D.spatialHermiteGeneratorFiniteShellAffineRootSmearingOfOS
                  i timeScale shell ξ
                  (ξ i.bridgeGlobalIndex) F)
              atTop
              (𝓝
                (C.current (section43NPointTimeSpatialTensor d k
                  (SCV.translateSchwartz
                    (-(generatorChronologicalParameter i ξ))
                    (A.timeTest (timeScale + D.commonTailStart i)))
                  (section43SpatialHeadMarginal F)))) := by
  intro i
  filter_upwards
    [D.eventually_spatialHermiteGeneratorAffineRootSmearingLimit_eq_translatedReducedTensor_of_currentData
      C i,
      D.eventually_tendsto_spatialHermiteGeneratorFiniteShellAffineRootSmearingOfOS_uniform_scale
        i]
    with ξ hcommon_ξ hshell
  intro timeScale hprofiles hleft hright hbridge F
  have hlimit :=
    hshell timeScale hprofiles hleft hright
      (ξ i.bridgeGlobalIndex) hbridge F
  rw [hcommon_ξ timeScale hprofiles hbridge F] at hlimit
  exact hlimit

end RootedA0BlockContinuousTranslationData
end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
