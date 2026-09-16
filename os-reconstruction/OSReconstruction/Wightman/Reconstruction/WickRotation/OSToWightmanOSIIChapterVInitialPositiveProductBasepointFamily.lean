/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketApproximation
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVCompactTimeReflectedSchwingerGerm
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVDifferenceReducedSupport
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialProductBasepointSource














noncomputable section

open Complex Filter Set Topology
open scoped Classical Topology

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity

/-- A scale-indexed family of normalized compact positive-time heads whose
supports lie in one compact strict-positive carrier. This is the exact head
contract needed by the reflected-source and Hilbert-family machinery. -/
structure UniformCompactPositiveTimeHeadFamilyData where
  head :
    ℕ → Section43CompactPositiveTimeSource1D
  carrier :
    Set ℝ
  carrier_compact :
    IsCompact carrier
  carrier_positive :
    carrier ⊆ Set.Ioi 0
  head_support :
    ∀ N, tsupport ((head N).f : ℝ → ℂ) ⊆ carrier
  head_integral_one :
    ∀ N, ∫ t : ℝ, (head N).f t = 1

namespace AnchoredPacketTimeShellFamilyData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}

/-- The full compact strict-positive time profile obtained by prepending the
fixed normalized head cutoff to one anchored coupled time test. -/
noncomputable def positiveProductBasepointTimeSource
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (N : ℕ) :
    Section43CompactStrictPositiveTimeSource (k + 1) :=
  section43PrependCompactPositiveTimeSource
    normalizedPositiveTimeBasepointCutoff
    (A.timeTest N) (A.timeTest_compact N) (A.timeTest_positive N)

@[simp]
theorem positiveProductBasepointTimeSource_f
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (N : ℕ) :
    (A.positiveProductBasepointTimeSource N).f =
      SCV.prependField normalizedPositiveTimeBasepointCutoff.f
        (A.timeTest N) :=
  rfl

/-- The same fixed-head time profile paired with an arbitrary full spatial
test on all `k + 1` particles.  This is the source family needed by the
generator block construction; no spatial basepoint factor is imposed. -/
noncomputable def positiveHeadSpatialSource
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (N : ℕ)
    (χ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    euclideanPositiveTimeSubmodule (d := d) (k + 1) :=
  section43PositiveTimeSpatialSourceCLM d (k + 1)
    (A.positiveProductBasepointTimeSource N) χ

@[simp]
theorem positiveHeadSpatialSource_coe
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (N : ℕ)
    (χ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    (A.positiveHeadSpatialSource N χ).1 =
      section43OrderedPullbackTimeSpatialTensorCLM d (k + 1) χ
        (SCV.prependField normalizedPositiveTimeBasepointCutoff.f
          (A.timeTest N)) :=
  rfl

/-- A full compact strict-positive time profile obtained by prepending a
possibly scale-dependent normalized positive head to the anchored coupled
time test. -/
noncomputable def headedPositiveTimeSource
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (H : UniformCompactPositiveTimeHeadFamilyData)
    (N : ℕ) :
    Section43CompactStrictPositiveTimeSource (k + 1) :=
  section43PrependCompactPositiveTimeSource
    (H.head N)
    (A.timeTest N) (A.timeTest_compact N) (A.timeTest_positive N)

@[simp]
theorem headedPositiveTimeSource_f
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (H : UniformCompactPositiveTimeHeadFamilyData)
    (N : ℕ) :
    (A.headedPositiveTimeSource H N).f =
      SCV.prependField (H.head N).f (A.timeTest N) :=
  rfl

/-- The scale-dependent headed time profile paired with an arbitrary full
spatial Schwartz test. -/
noncomputable def headedSpatialSource
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (H : UniformCompactPositiveTimeHeadFamilyData)
    (N : ℕ)
    (χ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    euclideanPositiveTimeSubmodule (d := d) (k + 1) :=
  section43PositiveTimeSpatialSourceCLM d (k + 1)
    (A.headedPositiveTimeSource H N) χ

@[simp]
theorem headedSpatialSource_coe
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (H : UniformCompactPositiveTimeHeadFamilyData)
    (N : ℕ)
    (χ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    (A.headedSpatialSource H N χ).1 =
      section43OrderedPullbackTimeSpatialTensorCLM d (k + 1) χ
        (SCV.prependField (H.head N).f (A.timeTest N)) :=
  rfl

/-- The positive-time source family whose time profile is the anchored
product-basepoint lift and whose spatial input is still the original reduced
Schwartz test. -/
noncomputable def positiveProductBasepointSource
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (N : ℕ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    euclideanPositiveTimeSubmodule (d := d) (k + 1) :=
  section43PositiveTimeSpatialSourceCLM d (k + 1)
    (A.positiveProductBasepointTimeSource N)
    (section43SpatialBasepointLiftCLM d k
      (normalizedSpatialBasepointCutoff d).toSchwartz χ)

@[simp]
theorem positiveProductBasepointSource_coe
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (N : ℕ)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    (A.positiveProductBasepointSource N χ).1 =
      productBasepointSpatialFullSourceCLM d k
        normalizedPositiveTimeBasepointCutoff.f
        (A.timeTest N) χ :=
  rfl

/-- The arbitrary-full-spatial fixed-head family has the same common compact
strict-positive difference-time carrier. -/
theorem positiveHeadSpatialSource_uniformCompactSupport
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor) :
    HasUniformCompactStrictPositiveDifferenceTimeSupport
      (fun p :
          ℕ × SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ =>
        (A.positiveHeadSpatialSource p.1 p.2).1) := by
  let K : Set (Fin (k + 1) → ℝ) :=
    (fun p : ℝ × (Fin k → ℝ) =>
      (Fin.cons p.1 p.2 : Fin (k + 1) → ℝ)) ''
      (tsupport
          (normalizedPositiveTimeBasepointCutoff.f : ℝ → ℂ) ×ˢ
        A.carrierData.carrier)
  have hcons :
      Continuous
        (fun p : ℝ × (Fin k → ℝ) =>
          (Fin.cons p.1 p.2 : Fin (k + 1) → ℝ)) := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ ?_ i
    · exact continuous_fst
    · intro j
      change Continuous (fun a : ℝ × (Fin k → ℝ) => a.2 j)
      exact (continuous_apply j).comp continuous_snd
  have hK_compact : IsCompact K := by
    exact
      (normalizedPositiveTimeBasepointCutoff.compact.isCompact.prod
        A.carrierData.carrier_compact).image hcons
  have hK_positive :
      K ⊆ section43TimeStrictPositiveRegion (k + 1) := by
    rintro τ ⟨p, hp, rfl⟩ i
    refine Fin.cases ?_ ?_ i
    · exact normalizedPositiveTimeBasepointCutoff.positive hp.1
    · intro j
      exact A.carrierData.carrier_positive hp.2 j
  refine ⟨K, hK_compact, hK_positive, ?_⟩
  intro p x hx
  have htime :
      section43QTime (d := d) (n := k + 1)
          (section43DiffCoordRealCLE d (k + 1) x) ∈
        tsupport
          ((A.positiveProductBasepointTimeSource p.1).f :
            (Fin (k + 1) → ℝ) → ℂ) := by
    exact
      osiiA0_orderedPullback_tsupport_subset_timeSet
        (d := d) p.2
        (A.positiveProductBasepointTimeSource p.1).f
        (tsupport
          ((A.positiveProductBasepointTimeSource p.1).f :
            (Fin (k + 1) → ℝ) → ℂ))
        (Subset.refl _)
        (by simpa [positiveHeadSpatialSource] using hx)
  exact
    section43PrependCompactPositiveTimeSource_tsupport_subset_carrier
      normalizedPositiveTimeBasepointCutoff
      (A.timeTest p.1)
      (A.timeTest_compact p.1)
      (A.timeTest_positive p.1)
      A.carrierData.carrier
      (by
        simpa [timeTest] using
          A.carrierData.translated_support p.1)
      htime

/-- Difference-variable reduction removes the normalized positive head and
retains the anchored time test together with the spatial head marginal. -/
theorem diffVarReduction_positiveHeadSpatialSource
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (N : ℕ)
    (χ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    diffVarReduction d k (A.positiveHeadSpatialSource N χ).1 =
      section43NPointTimeSpatialTensor d k
        (A.timeTest N) (section43SpatialHeadMarginal χ) := by
  rw [positiveHeadSpatialSource_coe,
    diffVarReduction_orderedPullback_timeSpatialTensor,
    SCV.sliceIntegral_prependField_eq_self
      normalizedPositiveTimeBasepointCutoff.f
      (A.timeTest N)
      normalizedPositiveTimeBasepointCutoff_integral_eq_one]

/-- A canonical reduced cutoff current which simultaneously represents every
translated positive-head packet in one chronological translation
neighborhood.

Retaining the cutoff and its support is essential for later coherence:
different anchored packet constructions may choose different auxiliary
cutoffs, while cutoff independence identifies their local Schwinger edges. -/
structure CommonTranslatedPositiveHeadSpatialSourceCurrentData
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d) where
  cutoff : SchwartzMap (Fin k → ℝ) ℂ
  cutoff_support :
    tsupport (cutoff : (Fin k → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion k
  cutoff_compact :
    HasCompactSupport (cutoff : (Fin k → ℝ) → ℂ)
  realRegion : Set (Fin k → ℝ)
  realRegion_open : IsOpen realRegion
  realRegion_mem_nhds : realRegion ∈ 𝓝 0
  cutoff_one_on_translatedSource :
    ∀ u ∈ realRegion, ∀ (N : ℕ)
      (χ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ),
      ∀ x ∈ tsupport
          ((translateSchwartzConfiguration
            (sourceParameterDisplacementCLM
              (fun i : Fin k =>
                chronologicalTimeSourceDirection (d := d) i) u)
            (A.positiveHeadSpatialSource N χ).1 :
            SchwartzNPoint d (k + 1)) :
              NPointDomain d (k + 1) → ℂ),
        reducedTimeCutoffWeight (d := d) cutoff x = 1
  recover :
    ∀ u ∈ realRegion, ∀ (N : ℕ)
      (χ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ),
      canonicalReducedTimeCutoffSchwingerCLM
          OS cutoff cutoff_support
          (section43NPointTimeSpatialTensor d k
            (SCV.translateSchwartz (-u) (A.timeTest N))
            (section43SpatialHeadMarginal χ)) =
        OS.S (k + 1)
          (ZeroDiagonalSchwartz.ofClassical
            (translateSchwartzConfiguration
              (sourceParameterDisplacementCLM
                (fun i : Fin k =>
                  chronologicalTimeSourceDirection (d := d) i) u)
              (A.positiveHeadSpatialSource N χ).1))

namespace CommonTranslatedPositiveHeadSpatialSourceCurrentData

/-- The canonical reduced current retained by the translated source package. -/
noncomputable def current
    (C : CommonTranslatedPositiveHeadSpatialSourceCurrentData
      (d := d) (k := k) (I := I) (anchor := anchor) A OS) :
    SchwartzNPoint d k →L[ℂ] ℂ :=
  canonicalReducedTimeCutoffSchwingerCLM
    (d := d) (m := k) OS C.cutoff C.cutoff_support

/-- The package's recovery identity holds eventually at the translation
origin. -/
theorem eventually_recover
    (C : CommonTranslatedPositiveHeadSpatialSourceCurrentData
      (d := d) (k := k) (I := I) (anchor := anchor) A OS) :
    ∀ᶠ u : Fin k → ℝ in 𝓝 0,
      ∀ (N : ℕ)
        (χ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ),
        C.current
            (section43NPointTimeSpatialTensor d k
              (SCV.translateSchwartz (-u) (A.timeTest N))
              (section43SpatialHeadMarginal χ)) =
          OS.S (k + 1)
            (ZeroDiagonalSchwartz.ofClassical
              (translateSchwartzConfiguration
                (sourceParameterDisplacementCLM
                  (fun i : Fin k =>
                    chronologicalTimeSourceDirection (d := d) i) u)
                (A.positiveHeadSpatialSource N χ).1)) := by
  filter_upwards [C.realRegion_mem_nhds] with u hu
  exact C.recover u hu

/-- Every translated full source fixed by the retained cutoff is genuinely
zero-diagonal. -/
theorem translatedSource_vanishes
    (C : CommonTranslatedPositiveHeadSpatialSourceCurrentData
      (d := d) (k := k) (I := I) (anchor := anchor) A OS)
    (u : Fin k → ℝ)
    (hu : u ∈ C.realRegion)
    (N : ℕ)
    (χ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    VanishesToInfiniteOrderOnCoincidence
      (translateSchwartzConfiguration
        (sourceParameterDisplacementCLM
          (fun i : Fin k =>
            chronologicalTimeSourceDirection (d := d) i) u)
        (A.positiveHeadSpatialSource N χ).1) := by
  let f : SchwartzNPoint d (k + 1) :=
    translateSchwartzConfiguration
      (sourceParameterDisplacementCLM
        (fun i : Fin k =>
          chronologicalTimeSourceDirection (d := d) i) u)
      (A.positiveHeadSpatialSource N χ).1
  apply VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint
  refine Set.disjoint_left.2 ?_
  intro x hx hcoin
  have hone :
      reducedTimeCutoffWeight (d := d) C.cutoff x = 1 :=
    C.cutoff_one_on_translatedSource u hu N χ x hx
  have hxweight :
      x ∈ tsupport
        (reducedTimeCutoffWeight (d := d) C.cutoff) :=
    subset_tsupport
      (reducedTimeCutoffWeight (d := d) C.cutoff)
      (by
        change reducedTimeCutoffWeight (d := d) C.cutoff x ≠ 0
        rw [hone]
        exact one_ne_zero)
  exact
    Set.disjoint_left.mp
      (reducedTimeCutoffWeight_tsupport_disjoint
        C.cutoff C.cutoff_support)
      hxweight hcoin

end CommonTranslatedPositiveHeadSpatialSourceCurrentData

/-- The translated positive-head family admits a canonical current package
with its auxiliary cutoff and recovery neighborhood retained. -/
theorem nonempty_commonTranslatedPositiveHeadSpatialSourceCurrentData
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d) :
    Nonempty (CommonTranslatedPositiveHeadSpatialSourceCurrentData A OS) := by
  let sourceFamily :
      ℕ × SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ →
        SchwartzNPoint d (k + 1) :=
    fun p => (A.positiveHeadSpatialSource p.1 p.2).1
  have hsourceFamily :
      HasUniformCompactStrictPositiveReducedTimeSupport sourceFamily :=
    A.positiveHeadSpatialSource_uniformCompactSupport.toReducedTimeSupport
  let displacement : (Fin k → ℝ) → NPointDomain d (k + 1) :=
    sourceParameterDisplacementCLM
      (fun i : Fin k =>
        chronologicalTimeSourceDirection (d := d) i)
  have hdisplacement : Continuous displacement :=
    (sourceParameterDisplacementCLM
      (fun i : Fin k =>
        chronologicalTimeSourceDirection (d := d) i)).continuous
  have hdisplacement_zero : displacement 0 = 0 := by
    simp [displacement]
  obtain ⟨η, hη, hη_compact, U, hU, hrecover⟩ :=
    exists_canonicalReducedTimeCutoffSchwingerCLM_family_displacement_germ
      OS sourceFamily hsourceFamily displacement
      hdisplacement hdisplacement_zero
  obtain ⟨V, hVU, hV_open, hzeroV⟩ := mem_nhds_iff.mp hU
  refine ⟨{
    cutoff := η
    cutoff_support := hη
    cutoff_compact := hη_compact
    realRegion := V
    realRegion_open := hV_open
    realRegion_mem_nhds := hV_open.mem_nhds hzeroV
    cutoff_one_on_translatedSource := ?_
    recover := ?_ }⟩
  · intro u hu N χ x hx
    exact (hrecover (N, χ) u (hVU hu)).2.2 x hx
  intro u hu N χ
  have hrecover_source :=
    (hrecover (N, χ) u (hVU hu)).2.1
  change
    canonicalReducedTimeCutoffSchwingerCLM OS η hη
        (diffVarReduction d k
          (translateSchwartzConfiguration
            (sourceParameterDisplacementCLM
              (fun i : Fin k =>
                chronologicalTimeSourceDirection (d := d) i) u)
            (A.positiveHeadSpatialSource N χ).1)) =
      _ at hrecover_source
  rw [diffVarReduction_translateSchwartzConfiguration,
    A.diffVarReduction_positiveHeadSpatialSource,
    translate_reducedTimeSpatialTensor_chronological] at hrecover_source
  exact hrecover_source

/-- If the chronologically translated packet tail remains strictly positive,
then all translated positive-head sources at that scale share its compact
reduced-time support, uniformly in the full spatial test. -/
theorem
    translatedPositiveHeadSpatialSource_hasUniformCompactStrictPositiveReducedTimeSupport
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (N : ℕ)
    (u : Fin k → ℝ)
    (hpositive :
      tsupport
          ((SCV.translateSchwartz (-u) (A.timeTest N) :
            SchwartzMap (Fin k → ℝ) ℂ) :
              (Fin k → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion k) :
    HasUniformCompactStrictPositiveReducedTimeSupport
      (fun χ : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ =>
        translateSchwartzConfiguration
          (sourceParameterDisplacementCLM
            (fun i : Fin k =>
              chronologicalTimeSourceDirection (d := d) i) u)
          (A.positiveHeadSpatialSource N χ).1) := by
  let tail : SchwartzMap (Fin k → ℝ) ℂ :=
    SCV.translateSchwartz (-u) (A.timeTest N)
  let K : Set (Fin k → ℝ) :=
    tsupport (tail : (Fin k → ℝ) → ℂ)
  have hK_compact : IsCompact K := by
    have htail_compact :
        HasCompactSupport (tail : (Fin k → ℝ) → ℂ) := by
      dsimp only [tail]
      exact
        hasCompactSupport_translateSchwartz
          (A.timeTest N) (A.timeTest_compact N) (-u)
    simpa [K, HasCompactSupport] using
      htail_compact
  refine ⟨K, hK_compact, by simpa [K, tail] using hpositive, ?_⟩
  intro χ x hx
  have hsource :
      translateSchwartzConfiguration
          (sourceParameterDisplacementCLM
            (fun i : Fin k =>
              chronologicalTimeSourceDirection (d := d) i) u)
          (A.positiveHeadSpatialSource N χ).1 =
        section43OrderedPullbackTimeSpatialTensorCLM d (k + 1) χ
          (SCV.prependField normalizedPositiveTimeBasepointCutoff.f
            tail) := by
    rw [positiveHeadSpatialSource_coe,
      translate_chronologicalSource_orderedPullbackTimeSpatialTensor,
      translateSchwartz_prependField_chronological]
  change
    x ∈ tsupport
      ((translateSchwartzConfiguration
        (sourceParameterDisplacementCLM
          (fun i : Fin k =>
            chronologicalTimeSourceDirection (d := d) i) u)
        (A.positiveHeadSpatialSource N χ).1 :
          SchwartzNPoint d (k + 1)) :
            NPointDomain d (k + 1) → ℂ) at hx
  rw [hsource] at hx
  obtain ⟨q, hq, hred⟩ :=
    orderedPullback_reducedTimeProjection_mem_tail_tsupport
      (SCV.prependField normalizedPositiveTimeBasepointCutoff.f tail)
      χ x hx
  rw [← hred]
  exact
    tsupport_prependField_subset_tail_preimage
      normalizedPositiveTimeBasepointCutoff.f tail hq

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
