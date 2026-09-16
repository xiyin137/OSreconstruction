/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketRootedHolomorphicSmearing
import OSReconstruction.SCV.TotallyRealIdentity















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

private theorem tail_timeTupleTransport_mem_strictPositive_affine
    {n : ℕ}
    (h : n = k + 1)
    (x : Fin n → ℝ)
    (hx : x ∈ section43TimeStrictPositiveRegion n) :
    SCV.tailCLM k (section43TimeTupleTransport h x) ∈
      section43TimeStrictPositiveRegion k := by
  subst n
  intro j
  exact hx j.succ

/-- The rooted common-arity source at internal translation `ξ` and affine
bridge coordinate `c + t`. -/
noncomputable def rootedAffineGeneratorFullSource
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (ξ : Fin k → ℝ)
    (c t : ℝ)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    SchwartzNPoint d (k + 1) :=
  GeneratorHermiteHilbertFieldFamilyData.reindexSchwartzNPointCLM
    (d := d) (finCongr i.absoluteCard_eq.symm)
    (axisPairGlobalAbsoluteSpatialSourceCLM
      i.n i.m
      (D.rootedLeftTranslatedTimeProfile i timeScale ξ)
      (D.rootedRightTranslatedTimeProfile i timeScale ξ)
      (D.rootedLeftTranslatedCommonShift i timeScale ξ)
      (c + t)
      (generatorSplitSpatialPullbackCLM i
        (GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
          (d := d) i F)))

/-- The affine rooted source with its ordered-positive zero-diagonal
certificate. -/
noncomputable def rootedAffineGeneratorSourceZero
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (ξ : Fin k → ℝ)
    (hpositive :
      D.RootedTranslatedTimeProfilesPositive i timeScale ξ)
    (c t : ℝ)
    (hct : 0 ≤ c + t)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    ZeroDiagonalSchwartz d (k + 1) :=
  GeneratorHermiteHilbertFieldFamilyData.reindexZeroDiagonalSchwartzCLM
    (d := d) (finCongr i.absoluteCard_eq.symm)
    (axisPairGlobalAbsoluteSpatialSourceZeroCLM
      i.n i.m i.hn i.hm
      (D.rootedLeftTranslatedTimeProfile i timeScale ξ)
      hpositive.1
      (D.rootedRightTranslatedTimeProfile i timeScale ξ)
      hpositive.2
      (D.rootedLeftTranslatedCommonShift i timeScale ξ)
      (c + t) hct
      (D.rootedLeftTranslatedCommonShift_span i timeScale ξ)
      (generatorSplitSpatialPullbackCLM i
        (GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
          (d := d) i F)))

set_option maxRecDepth 4000 in
@[simp] theorem rootedAffineGeneratorSourceZero_coe
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (ξ : Fin k → ℝ)
    (hpositive :
      D.RootedTranslatedTimeProfilesPositive i timeScale ξ)
    (c t : ℝ)
    (hct : 0 ≤ c + t)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    (D.rootedAffineGeneratorSourceZero
      i timeScale ξ hpositive c t hct F).1 =
      D.rootedAffineGeneratorFullSource i timeScale ξ c t F := rfl

set_option maxRecDepth 4000 in
/-- The affine split Schwinger value is the common-arity Schwinger functional
applied to the affine rooted source. -/
theorem
    generatorSplitAbsoluteSpatialSchwingerCLM_eq_rootedAffineGeneratorSourceZero
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (ξ : Fin k → ℝ)
    (hpositive :
      D.RootedTranslatedTimeProfilesPositive i timeScale ξ)
    (c t : ℝ)
    (hct : 0 ≤ c + t)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    generatorSplitAbsoluteSpatialSchwingerCLM
        OS i
        (D.rootedLeftTranslatedTimeProfile i timeScale ξ)
        hpositive.1
        (D.rootedRightTranslatedTimeProfile i timeScale ξ)
        hpositive.2
        (D.rootedLeftTranslatedCommonShift i timeScale ξ)
        (c + t) hct
        (D.rootedLeftTranslatedCommonShift_span i timeScale ξ)
        (GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
          (d := d) i F) =
      OS.S (k + 1)
        (D.rootedAffineGeneratorSourceZero
          i timeScale ξ hpositive c t hct F) := by
  exact
    (GeneratorHermiteHilbertFieldFamilyData.schwinger_reindex_finCongr
      OS i.absoluteCard_eq.symm
      (axisPairGlobalAbsoluteSpatialSourceZeroCLM
        i.n i.m i.hn i.hm
        (D.rootedLeftTranslatedTimeProfile i timeScale ξ)
        hpositive.1
        (D.rootedRightTranslatedTimeProfile i timeScale ξ)
        hpositive.2
        (D.rootedLeftTranslatedCommonShift i timeScale ξ)
        (c + t) hct
        (D.rootedLeftTranslatedCommonShift_span i timeScale ξ)
      (generatorSplitSpatialPullbackCLM i
          (GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
            (d := d) i F)))).symm

/-- The affine rooted source is the literal translated global time cutoff
tensored with the original common-arity spatial test. -/
theorem rootedAffineGeneratorFullSource_normalForm
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (ξ : Fin k → ℝ)
    (c t : ℝ)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    D.rootedAffineGeneratorFullSource i timeScale ξ c t F =
      section43OrderedPullbackTimeSpatialTensorCLM d (k + 1) F
        (section43TimeSchwartzTransport i.pointArity_add
          (osiiAxisPairGlobalTimeCutoff i.n i.m
            (D.rootedLeftTranslatedTimeProfile i timeScale ξ).conj
            (D.rootedRightTranslatedTimeProfile i timeScale ξ)
            (D.rootedLeftTranslatedCommonShift i timeScale ξ)
            (c + t))) := by
  have harity :
      i.pointArity_add = i.absoluteCard_eq.symm :=
    Subsingleton.elim _ _
  rw [harity]
  rw [section43TimeSchwartzTransport_eq_finCongrPullback]
  conv_rhs =>
    rw [←
      GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPullbackCLM_pushforward
        (d := d) i F]
  unfold rootedAffineGeneratorFullSource
  rw [GeneratorHermiteHilbertFieldFamilyData.reindexSchwartzNPointCLM_apply]
  ext x
  rw [reindexSchwartz_apply]
  rw [GeneratorHermiteHilbertFieldFamilyData.axisPairGlobalAbsoluteSpatialSourceCLM_normalForm
    i.n i.m i.hn i.hm]
  simp only [ContinuousLinearMap.comp_apply,
    section43OrderedPullbackTimeSpatialTensorSpatialCLM_apply,
    section43OrderedPullbackTimeSpatialTensorCLM_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    section43NPointTimeSpatialTensor_apply,
    Function.comp_apply]
  set_option maxRecDepth 4000 in
    rfl

/-- Affine rooted sources with root parameter in a fixed compact positive set
have one compact strict-positive reduced-time carrier, provided the outer
bridge is nonnegative. -/
theorem
    rootedAffineGeneratorFullSource_hasUniformCompactStrictPositiveReducedTimeSupport
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (ξ : Fin k → ℝ)
    (hpositive :
      D.RootedTranslatedTimeProfilesPositive i timeScale ξ)
    (c : ℝ)
    (hc : 0 ≤ c)
    (J : Set ℝ)
    (hJ_compact : IsCompact J)
    (hJ_positive : J ⊆ Set.Ioi 0) :
    HasUniformCompactStrictPositiveReducedTimeSupport
      (fun p :
          J × SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ =>
        D.rootedAffineGeneratorFullSource
          i timeScale ξ c p.1.1 p.2) := by
  let η₁ := (D.rootedLeftTranslatedTimeProfile i timeScale ξ).conj
  let η₂ := D.rootedRightTranslatedTimeProfile i timeScale ξ
  let s := D.rootedLeftTranslatedCommonShift i timeScale ξ
  let e := osiiAxisPairBlockGlobalTimeCLE i.n i.m
  let product := SCV.twoBlockProductSchwartz η₁ η₂
  let base : SchwartzMap (Fin (i.n + i.m) → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm product
  let shift : ℝ → Fin (i.n + i.m) → ℝ :=
    fun t => osiiAxisPairGlobalTimeDiffShift i.n i.m s (c + t)
  let carrierMap :
      (Fin (i.n + i.m) → ℝ) × ℝ → Fin k → ℝ :=
    fun p =>
      SCV.tailCLM k
        (section43TimeTupleTransport i.pointArity_add
          (p.1 + shift p.2))
  let K : Set (Fin k → ℝ) :=
    carrierMap ''
      (tsupport (base : (Fin (i.n + i.m) → ℝ) → ℂ) ×ˢ J)
  have hη₁_compact :
      HasCompactSupport (η₁ : (Fin i.n → ℝ) → ℂ) := by
    apply hasCompactSupport_schwartzMap_conj
    unfold rootedLeftTranslatedTimeProfile
    exact
      hasCompactSupport_translateSchwartz
        (D.rootedLeftTimeProfile i timeScale)
        (by
          simpa using
            (D.rootedLeftTimeProfileNative i timeScale).compact)
        (chronologicalTimeProfileDisplacementOfPositive i.hn
          (i.leftRealCoordinates ξ))
  have hη₂_compact :
      HasCompactSupport (η₂ : (Fin i.m → ℝ) → ℂ) := by
    dsimp only [η₂]
    unfold rootedRightTranslatedTimeProfile
    exact
      hasCompactSupport_translateSchwartz
        (D.rootedRightTimeProfile i timeScale)
        (by
          simpa using
            (D.rootedRightTimeProfileNative i timeScale).compact)
        (chronologicalTimeProfileDisplacementOfPositive i.hm
          (i.rightRealCoordinates ξ))
  have hbase_compact :
      HasCompactSupport
        (base : (Fin (i.n + i.m) → ℝ) → ℂ) := by
    exact
      (twoBlockProductSchwartz_hasCompactSupport
        i.n i.m η₁ η₂ hη₁_compact hη₂_compact).comp_homeomorph
          e.symm.toHomeomorph
  have hshift_continuous : Continuous shift := by
    apply continuous_pi
    intro j
    change Continuous (fun t : ℝ =>
      (if j.val = 0 then s else 0) +
        if j.val = i.n ∧ 0 < i.m then c + t else 0)
    split_ifs <;> fun_prop
  have hcarrierMap_continuous : Continuous carrierMap := by
    apply continuous_pi
    intro j
    exact
      (continuous_apply j).comp
        ((SCV.tailCLM k).continuous.comp
          ((continuous_section43TimeTupleTransport i.pointArity_add).comp
            (continuous_fst.add
              (hshift_continuous.comp continuous_snd))))
  have hK_compact : IsCompact K := by
    exact
      (hbase_compact.isCompact.prod hJ_compact).image
        hcarrierMap_continuous
  have hη₁_positive :
      tsupport (η₁ : (Fin i.n → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion i.n := by
    simpa [η₁] using hpositive.1
  have hη₂_positive :
      tsupport (η₂ : (Fin i.m → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion i.m := by
    simpa [η₂] using hpositive.2
  have hspan :
      ∀ δ ∈ tsupport (η₁ : (Fin i.n → ℝ) → ℂ),
        (section43ScalarDiffCLE i.n).symm δ
            (Fin.rev ⟨0, i.hn⟩) < s := by
    simpa [η₁, s] using
      D.rootedLeftTranslatedCommonShift_span i timeScale ξ
  have hK_positive :
      K ⊆ section43TimeStrictPositiveRegion k := by
    rintro _ ⟨p, hp, rfl⟩
    have hp_global :
        p.1 + shift p.2 ∈
          tsupport
            (osiiAxisPairGlobalTimeCutoff
              i.n i.m η₁ η₂ s (c + p.2) :
                (Fin (i.n + i.m) → ℝ) → ℂ) := by
      change
        p.1 + shift p.2 ∈
          tsupport
            ((SCV.translateSchwartz (-shift p.2) base :
              SchwartzMap (Fin (i.n + i.m) → ℝ) ℂ) :
                (Fin (i.n + i.m) → ℝ) → ℂ)
      rw [tsupport_translateSchwartz_eq_preimage]
      simpa [add_assoc] using hp.1
    have hp_positive :
        p.1 + shift p.2 ∈
          section43TimeStrictPositiveRegion (i.n + i.m) := by
      exact
        osiiAxisPairGlobalTimeCutoff_tsupport_subset_strictPositive
          i.n i.m i.hn i.hm η₁ η₂ hη₁_positive hη₂_positive
          s (c + p.2) (add_nonneg hc (hJ_positive hp.2).le)
          hspan hp_global
    exact
      tail_timeTupleTransport_mem_strictPositive_affine
        i.pointArity_add (p.1 + shift p.2) hp_positive
  refine ⟨K, hK_compact, hK_positive, ?_⟩
  intro p x hx
  change
    x ∈ tsupport
      ((D.rootedAffineGeneratorFullSource
        i timeScale ξ c p.1.1 p.2 :
          SchwartzNPoint d (k + 1)) :
            NPointDomain d (k + 1) → ℂ) at hx
  rw [D.rootedAffineGeneratorFullSource_normalForm
    i timeScale ξ c p.1.1 p.2] at hx
  obtain ⟨q, hq, hred⟩ :=
    orderedTimeSpatialTensor_reducedTimeProjection_mem_tail_tsupport
      (section43TimeSchwartzTransport i.pointArity_add
        (osiiAxisPairGlobalTimeCutoff
          i.n i.m η₁ η₂ s (c + p.1.1)))
      p.2 x hx
  rw [tsupport_section43TimeSchwartzTransport] at hq
  obtain ⟨q₀, hq₀, rfl⟩ := hq
  let y := q₀ + (-shift p.1.1)
  have hy :
      y ∈ tsupport (base : (Fin (i.n + i.m) → ℝ) → ℂ) := by
    change
      q₀ ∈
        tsupport
          ((SCV.translateSchwartz (-shift p.1.1) base :
            SchwartzMap (Fin (i.n + i.m) → ℝ) ℂ) :
              (Fin (i.n + i.m) → ℝ) → ℂ) at hq₀
    rw [tsupport_translateSchwartz_eq_preimage] at hq₀
    simpa [y] using hq₀
  rw [← hred]
  refine ⟨(y, p.1.1), ⟨hy, p.1.2⟩, ?_⟩
  have hyshift : y + shift p.1.1 = q₀ := by
    ext j
    simp [y]
  unfold carrierMap
  rw [hyshift]
  rfl

/-- Difference-variable reduction of the affine rooted source is its literal
translated global-cutoff slice with the spatial head marginal. -/
theorem diffVarReduction_rootedAffineGeneratorFullSource
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (ξ : Fin k → ℝ)
    (c t : ℝ)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    diffVarReduction d k
        (D.rootedAffineGeneratorFullSource i timeScale ξ c t F) =
      section43NPointTimeSpatialTensor d k
        (SCV.sliceIntegral
          (section43TimeSchwartzTransport i.pointArity_add
            (osiiAxisPairGlobalTimeCutoff i.n i.m
              (D.rootedLeftTranslatedTimeProfile i timeScale ξ).conj
              (D.rootedRightTranslatedTimeProfile i timeScale ξ)
              (D.rootedLeftTranslatedCommonShift i timeScale ξ)
              (c + t))))
        (section43SpatialHeadMarginal F) := by
  rw [D.rootedAffineGeneratorFullSource_normalForm]
  exact
    diffVarReduction_orderedPullback_timeSpatialTensor
      (section43TimeSchwartzTransport i.pointArity_add
        (osiiAxisPairGlobalTimeCutoff i.n i.m
          (D.rootedLeftTranslatedTimeProfile i timeScale ξ).conj
          (D.rootedRightTranslatedTimeProfile i timeScale ξ)
          (D.rootedLeftTranslatedCommonShift i timeScale ξ)
          (c + t)))
      F

/-- Smear an original-OS finite Hermite shell at the affine bridge
coordinate `c + t`. -/
noncomputable def spatialHermiteGeneratorFiniteShellAffineRootSmearingOfOS
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale shell : ℕ)
    (ξ : Fin k → ℝ)
    (c : ℝ)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    ℂ :=
  ∫ t : ℝ,
    D.semigroupBridgeRootWeight i timeScale t *
      D.spatialHermiteGeneratorFiniteShellOfOS
        i timeScale shell
        (osiiPositiveRealTimeEmbed
          (generatorBridgeVariation i ξ (c + t))) F

/-- Compatibility presentation of original-OS affine finite-shell smearing. -/
noncomputable def spatialHermiteGeneratorFiniteShellAffineRootSmearing
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (_lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (timeScale shell : ℕ)
    (ξ : Fin k → ℝ)
    (c : ℝ)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    ℂ :=
  D.spatialHermiteGeneratorFiniteShellAffineRootSmearingOfOS
    i timeScale shell ξ c F

/-- The full affine-root scalar value. The outer bridge is nonnegative and
the synchronized root contributes the strictly positive increment. -/
noncomputable def spatialHermiteGeneratorAffineRootSmearingLimit
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (ξ : Fin k → ℝ)
    (hpositive :
      D.RootedTranslatedTimeProfilesPositive i timeScale ξ)
    (c : ℝ)
    (hc : 0 ≤ c)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    ℂ :=
  ∫ t : ℝ,
    D.semigroupBridgeRootWeight i timeScale t *
      if ht : 0 < t then
        generatorSplitAbsoluteSpatialSchwingerCLM
          OS i
          (D.rootedLeftTranslatedTimeProfile i timeScale ξ)
          hpositive.1
          (D.rootedRightTranslatedTimeProfile i timeScale ξ)
          hpositive.2
          (D.rootedLeftTranslatedCommonShift i timeScale ξ)
          (c + t) (add_nonneg hc ht.le)
          (D.rootedLeftTranslatedCommonShift_span i timeScale ξ)
          (GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
            (d := d) i F)
      else 0

/-- The positive-real value of the holomorphic root-smeared finite shell is
the original-OS affine root smearing based at the current bridge coordinate. -/
theorem
    rootSmearedSpatialHermiteGeneratorFiniteShellOfOS_positiveReal_eq_affineRootSmearing
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale shell : ℕ)
    (ξ : Fin k → ℝ)
    (hbridge : 0 < ξ i.bridgeGlobalIndex)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    D.rootSmearedSpatialHermiteGeneratorFiniteShellOfOS
        i timeScale shell
        (osiiPositiveRealTimeEmbed ξ) F =
      D.spatialHermiteGeneratorFiniteShellAffineRootSmearingOfOS
        i timeScale shell ξ (ξ i.bridgeGlobalIndex) F := by
  rw [
    D.rootSmearedSpatialHermiteGeneratorFiniteShellOfOS_positiveReal_eq_integral
      i timeScale shell ξ hbridge F]
  rfl

/-- Compatibility wrapper for the growth-free affine finite-shell edge. -/
theorem
    rootSmearedSpatialHermiteGeneratorFiniteShell_positiveReal_eq_affineRootSmearing
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (_lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k)
    (timeScale shell : ℕ)
    (ξ : Fin k → ℝ)
    (hbridge : 0 < ξ i.bridgeGlobalIndex)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ) :
    D.rootSmearedSpatialHermiteGeneratorFiniteShell
        _lgc i timeScale shell
        (osiiPositiveRealTimeEmbed ξ) F =
      D.spatialHermiteGeneratorFiniteShellAffineRootSmearing
        _lgc i timeScale shell ξ (ξ i.bridgeGlobalIndex) F :=
  D.rootSmearedSpatialHermiteGeneratorFiniteShellOfOS_positiveReal_eq_affineRootSmearing
    i timeScale shell ξ hbridge F

/-- The affine rooted-smearing shell limit holds on one real neighborhood
uniformly in packet scale using only the original OS axioms. -/
theorem
    eventually_tendsto_spatialHermiteGeneratorFiniteShellAffineRootSmearingOfOS_uniform_scale
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k) :
    ∀ᶠ ξ : Fin k → ℝ in 𝓝 0,
      ∀ timeScale : ℕ,
      ∀ hpositive :
        D.RootedTranslatedTimeProfilesPositive i timeScale ξ,
      i.leftRealCoordinates ξ ∈ (D.left i).realRegion →
      i.rightRealCoordinates ξ ∈ (D.right i).realRegion →
      ∀ (c : ℝ) (hc : 0 ≤ c),
      ∀ F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ,
        Tendsto
          (fun shell =>
            D.spatialHermiteGeneratorFiniteShellAffineRootSmearingOfOS
              i timeScale shell ξ c F)
          atTop
          (𝓝
            (D.spatialHermiteGeneratorAffineRootSmearingLimit
              i timeScale ξ hpositive c hc F)) := by
  filter_upwards
    [D.eventually_tendsto_spatialHermiteGeneratorFiniteShellOfOS_positiveBridge_uniform_scale
      i]
      with ξ hshell
  intro timeScale hpositive hleft hright c hc F
  obtain ⟨J, hJ_compact, hJ_positive, hsupport⟩ :=
    D.exists_semigroupBridgeRootWeight_uniformCompactPositiveSupport i
  let K : Set (Fin k → ℝ) :=
    (fun t : ℝ => generatorBridgeVariation i ξ (c + t)) '' J
  have hK_compact : IsCompact K := by
    exact
      hJ_compact.image
        ((continuous_generatorBridgeVariation i ξ).comp
          (continuous_const.add continuous_id))
  have hleftK :
      Set.MapsTo i.leftRealCoordinates K (D.left i).realRegion := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := hx
    simpa using hleft
  have hrightK :
      Set.MapsTo i.rightRealCoordinates K (D.right i).realRegion := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := hx
    simpa using hright
  obtain ⟨M, hM⟩ :=
    D.exists_spatialHermiteGeneratorFiniteShellOfOS_apply_norm_bound_on_compact
      i K hK_compact hleftK hrightK F
  let weight : SchwartzMap ℝ ℂ :=
    D.semigroupBridgeRootWeight i timeScale
  let branch : ℕ → ℝ → ℂ :=
    fun shell t =>
      D.spatialHermiteGeneratorFiniteShellOfOS
        i timeScale shell
        (osiiPositiveRealTimeEmbed
          (generatorBridgeVariation i ξ (c + t))) F
  let limitBranch : ℝ → ℂ :=
    fun t =>
      if ht : 0 < t then
        generatorSplitAbsoluteSpatialSchwingerCLM
          OS i
          (D.rootedLeftTranslatedTimeProfile i timeScale ξ)
          hpositive.1
          (D.rootedRightTranslatedTimeProfile i timeScale ξ)
          hpositive.2
          (D.rootedLeftTranslatedCommonShift i timeScale ξ)
          (c + t) (add_nonneg hc ht.le)
          (D.rootedLeftTranslatedCommonShift_span i timeScale ξ)
          (GeneratorHermiteHilbertFieldFamilyData.generatorSplitGlobalSpatialPushforwardCLM
            (d := d) i F)
      else 0
  have hweight_compact :
      HasCompactSupport (weight : ℝ → ℂ) := by
    simpa [weight, semigroupBridgeRootWeight] using
      (A.rootedBridgeHead R i
        (timeScale + D.commonTailStart i)).compact
  have hbranch_cont :
      ∀ shell, ContinuousOn (branch shell) J := by
    intro shell
    simpa [branch, Function.comp_def] using
      (D.continuousOn_spatialHermiteGeneratorFiniteShellOfOS_bridge
          i timeScale shell ξ F).comp
        (continuous_const.add continuous_id).continuousOn
        (fun t ht => add_pos_of_nonneg_of_pos hc (hJ_positive ht))
  have hbranch_integrable :
      ∀ shell, Integrable (fun t : ℝ => weight t * branch shell t) := by
    intro shell
    let S : Set ℝ := tsupport (weight : ℝ → ℂ)
    have hS_compact : IsCompact S := hweight_compact
    have hbranch_cont_S : ContinuousOn (branch shell) S := by
      exact (hbranch_cont shell).mono (hsupport timeScale)
    have hproduct_cont :
        ContinuousOn (fun t : ℝ => weight t * branch shell t) S :=
      (SchwartzMap.continuous weight).continuousOn.mul hbranch_cont_S
    have hproduct_integrableOn :
        IntegrableOn (fun t : ℝ => weight t * branch shell t) S :=
      hproduct_cont.integrableOn_compact hS_compact
    have hindicator_integrable :
        Integrable
          (S.indicator (fun t : ℝ => weight t * branch shell t)) := by
      rw [integrable_indicator_iff hS_compact.measurableSet]
      exact hproduct_integrableOn
    have hindicator_eq :
        S.indicator (fun t : ℝ => weight t * branch shell t) =
          fun t : ℝ => weight t * branch shell t := by
      funext t
      by_cases ht : t ∈ S
      · simp [Set.indicator_of_mem ht]
      · have hzero : weight t = 0 :=
          image_eq_zero_of_notMem_tsupport (by simpa [S] using ht)
        simp [Set.indicator_of_notMem ht, hzero]
    simpa [hindicator_eq] using hindicator_integrable
  have hmajorant :
      Integrable (fun t : ℝ => ‖weight t‖ * |M|) :=
    (SchwartzMap.integrable weight).norm.mul_const |M|
  have hmeas :
      ∀ᶠ shell : ℕ in atTop,
        AEStronglyMeasurable
          (fun t : ℝ => weight t * branch shell t)
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    filter_upwards with shell
    exact (hbranch_integrable shell).aestronglyMeasurable
  have hbound :
      ∀ᶠ shell : ℕ in atTop,
        ∀ᵐ t : ℝ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
          ‖weight t * branch shell t‖ ≤ ‖weight t‖ * |M| := by
    filter_upwards with shell
    exact Filter.Eventually.of_forall fun t => by
      by_cases hweight : weight t = 0
      · simp [hweight]
      · have htJ : t ∈ J := by
          apply hsupport timeScale
          exact subset_tsupport _
            (show t ∈ Function.support (weight : ℝ → ℂ) from hweight)
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact
          (hM timeScale shell
            (generatorBridgeVariation i ξ (c + t))
            ⟨t, htJ, rfl⟩
            (by
              rw [generatorBridgeVariation_bridge]
              exact
                add_pos_of_nonneg_of_pos hc (hJ_positive htJ))).trans
            (le_abs_self M)
  have hlim :
      ∀ᵐ t : ℝ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        Tendsto
          (fun shell => weight t * branch shell t)
          atTop
          (𝓝 (weight t * limitBranch t)) := by
    exact Filter.Eventually.of_forall fun t => by
      by_cases hweight : weight t = 0
      · simp [hweight]
      · have htJ : t ∈ J := by
          apply hsupport timeScale
          exact subset_tsupport _
            (show t ∈ Function.support (weight : ℝ → ℂ) from hweight)
        have ht : 0 < t := hJ_positive htJ
        have hct : 0 < c + t :=
          add_pos_of_nonneg_of_pos hc ht
        simpa [branch, limitBranch, ht] using
          ((tendsto_const_nhds :
              Tendsto (fun _shell : ℕ => weight t)
                atTop (𝓝 (weight t))).mul
            (hshell timeScale hpositive hleft hright
              (c + t) hct F))
  unfold spatialHermiteGeneratorFiniteShellAffineRootSmearingOfOS
  change Tendsto
    (fun shell => ∫ t : ℝ, weight t * branch shell t)
    atTop
    (𝓝 (∫ t : ℝ, weight t * limitBranch t))
  simpa [spatialHermiteGeneratorAffineRootSmearingLimit, weight, limitBranch]
    using
      (MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (μ := MeasureTheory.volume)
        (F := fun shell t => weight t * branch shell t)
        (f := fun t => weight t * limitBranch t)
        (fun t : ℝ => ‖weight t‖ * |M|)
        hmeas hbound hmajorant hlim)

/-- Compatibility wrapper for original-OS affine rooted-shell convergence. -/
theorem
    eventually_tendsto_spatialHermiteGeneratorFiniteShellAffineRootSmearing_uniform_scale
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (_lgc : OSLinearGrowthCondition d OS)
    (i : GeneratorIndex k) :
    ∀ᶠ ξ : Fin k → ℝ in 𝓝 0,
      ∀ timeScale : ℕ,
      ∀ hpositive :
        D.RootedTranslatedTimeProfilesPositive i timeScale ξ,
      i.leftRealCoordinates ξ ∈ (D.left i).realRegion →
      i.rightRealCoordinates ξ ∈ (D.right i).realRegion →
      ∀ (c : ℝ) (hc : 0 ≤ c),
      ∀ F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ,
        Tendsto
          (fun shell =>
            D.spatialHermiteGeneratorFiniteShellAffineRootSmearing
              _lgc i timeScale shell ξ c F)
          atTop
          (𝓝
            (D.spatialHermiteGeneratorAffineRootSmearingLimit
              i timeScale ξ hpositive c hc F)) :=
  D.eventually_tendsto_spatialHermiteGeneratorFiniteShellAffineRootSmearingOfOS_uniform_scale
    i

/-- Once one reduced functional represents the affine positive-root slices,
the full affine root smearing at the physical bridge is its value on the
chronologically translated canonical anchored tensor. -/
theorem
    spatialHermiteGeneratorAffineRootSmearingLimit_eq_translatedReducedTensor_of_sourceCurrent
    (D : RootedA0BlockContinuousTranslationData OS A R)
    (i : GeneratorIndex k)
    (timeScale : ℕ)
    (ξ : Fin k → ℝ)
    (hpositive :
      D.RootedTranslatedTimeProfilesPositive i timeScale ξ)
    (hbridge : 0 ≤ ξ i.bridgeGlobalIndex)
    (F : SchwartzMap (Section43SpatialSpace d (k + 1)) ℂ)
    (L : SchwartzNPoint d k →L[ℂ] ℂ)
    (hsource :
      ∀ (t : ℝ),
        t ∈ tsupport
            (D.semigroupBridgeRootWeight i timeScale : ℝ → ℂ) →
        ∀ (ht : 0 < t),
        generatorSplitAbsoluteSpatialSchwingerCLM
            OS i
            (D.rootedLeftTranslatedTimeProfile i timeScale ξ)
            hpositive.1
            (D.rootedRightTranslatedTimeProfile i timeScale ξ)
            hpositive.2
            (D.rootedLeftTranslatedCommonShift i timeScale ξ)
            (ξ i.bridgeGlobalIndex + t)
            (add_nonneg hbridge ht.le)
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
                  (ξ i.bridgeGlobalIndex + t))))
            (section43SpatialHeadMarginal F))) :
    D.spatialHermiteGeneratorAffineRootSmearingLimit
        i timeScale ξ hpositive
        (ξ i.bridgeGlobalIndex) hbridge F =
      L (section43NPointTimeSpatialTensor d k
        (SCV.translateSchwartz
          (-(generatorChronologicalParameter i ξ))
          (A.timeTest (timeScale + D.commonTailStart i)))
        (section43SpatialHeadMarginal F)) := by
  obtain ⟨J, _hJ_compact, hJ_positive, hsupport⟩ :=
    D.exists_semigroupBridgeRootWeight_uniformCompactPositiveSupport i
  have hzero (t : ℝ) (ht : ¬ 0 < t) :
      D.semigroupBridgeRootWeight i timeScale t = 0 := by
    by_contra hne
    have ht_support :
        t ∈ tsupport
          (D.semigroupBridgeRootWeight i timeScale : ℝ → ℂ) :=
      subset_tsupport _
        (by simpa [Function.mem_support] using hne)
    exact ht (hJ_positive (hsupport timeScale ht_support))
  let T : SchwartzMap (Fin k → ℝ) ℂ →L[ℂ] ℂ :=
    L.comp
      (section43TimeSpatialTensorCLM d k
        (section43SpatialHeadMarginal F))
  calc
    D.spatialHermiteGeneratorAffineRootSmearingLimit
        i timeScale ξ hpositive
        (ξ i.bridgeGlobalIndex) hbridge F =
      ∫ t : ℝ,
        D.semigroupBridgeRootWeight i timeScale t *
          T
            (SCV.sliceIntegral
              (section43TimeSchwartzTransport i.pointArity_add
                (osiiAxisPairGlobalTimeCutoff i.n i.m
                  (D.rootedLeftTranslatedTimeProfile i timeScale ξ).conj
                  (D.rootedRightTranslatedTimeProfile i timeScale ξ)
                  (D.rootedLeftTranslatedCommonShift i timeScale ξ)
                  (ξ i.bridgeGlobalIndex + t)))) := by
      unfold spatialHermiteGeneratorAffineRootSmearingLimit
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : 0 < t
      · by_cases hweight :
          D.semigroupBridgeRootWeight i timeScale t = 0
        · simp [hweight]
        · have ht_support :
              t ∈ tsupport
                (D.semigroupBridgeRootWeight i timeScale : ℝ → ℂ) :=
            subset_tsupport _
              (by simpa [Function.mem_support] using hweight)
          rw [dif_pos ht, hsource t ht_support ht]
          rfl
      · simp [ht, hzero t ht]
    _ = T (SCV.translateSchwartz
        (-(generatorChronologicalParameter i ξ))
        (A.timeTest (timeScale + D.commonTailStart i))) := by
      simpa [semigroupBridgeRootWeight] using
        rootedTranslatedMiddleSmearing_weak_globalCutoffSlice_eq_timeTest
          D i timeScale
          (fun _ =>
            D.rootedLeftTranslatedCommonShift i timeScale ξ)
          ξ T
    _ = L (section43NPointTimeSpatialTensor d k
        (SCV.translateSchwartz
          (-(generatorChronologicalParameter i ξ))
          (A.timeTest (timeScale + D.commonTailStart i)))
        (section43SpatialHeadMarginal F)) := rfl

end RootedA0BlockContinuousTranslationData
end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
