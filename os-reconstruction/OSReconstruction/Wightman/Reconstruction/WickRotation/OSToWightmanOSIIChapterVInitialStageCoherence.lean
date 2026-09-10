/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.SCV.DistributionalRepresentationUniqueness
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketLocalKernel
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialTimeSmearingStageLimit












noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d] [NeZero k]

/-- Canonical reduced cutoff distributions have the same fixed-spatial time
pairing on tests supported where both cutoffs are one. -/
theorem orderedCanonicalReducedTimeCutoff_pairing_eq_of_tsupport
    (OS : OsterwalderSchraderAxioms d)
    {K₁ K₂ : Set (Fin k → ℝ)}
    (C₁ : CanonicalReducedCompactCutoffData K₁)
    (C₂ : CanonicalReducedCompactCutoffData K₂)
    (U : Set (Fin k → ℝ))
    (hU₁ : U ⊆ C₁.realRegion)
    (hU₂ : U ⊆ C₂.realRegion)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (hφU : tsupport (φ : (Fin k → ℝ) → ℂ) ⊆ U) :
    ((orderedTransportDistribution
        (canonicalReducedTimeCutoffSchwingerCLM
          OS C₁.cutoff C₁.cutoff_support)).comp
        (section43OrderedPullbackTimeSpatialTensorCLM d k χ)) φ =
      ((orderedTransportDistribution
        (canonicalReducedTimeCutoffSchwingerCLM
          OS C₂.cutoff C₂.cutoff_support)).comp
        (section43OrderedPullbackTimeSpatialTensorCLM d k χ)) φ := by
  simp only [ContinuousLinearMap.comp_apply,
    orderedTransportDistribution_orderedPullbackTimeSpatialTensor]
  let ψ : SchwartzNPoint d k :=
    section43NPointTimeSpatialTensor d k φ χ
  let basepointCutoff : BHW.NormalizedBasepointCutoff d :=
    BHW.normalizedCutoffOfBump d
  let f : SchwartzNPoint d (k + 1) :=
    BHW.reducedTestLift k d basepointCutoff.toSchwartz ψ
  have hright :
      diffVarReduction d k f = ψ := by
    exact diffVarReduction_reducedTestLift basepointCutoff ψ
  have htime :
      ∀ x ∈ tsupport (f : NPointDomain d (k + 1) → ℂ),
        section43QTime (d := d) (n := k)
            (BHW.reducedDiffMapReal (k + 1) d x) ∈ U := by
    intro x hx
    have hxψ :
        BHW.reducedDiffMapReal (k + 1) d x ∈
          tsupport (ψ : NPointDomain d k → ℂ) :=
      reducedTestLift_tsupport_subset_reducedDiff_preimage_tsupport
        basepointCutoff.toSchwartz ψ hx
    exact hφU
      (tsupport_section43NPointTimeSpatialTensor_subset_time_preimage
        d k φ χ hxψ)
  have hone₁ :
      ∀ x ∈ tsupport (f : NPointDomain d (k + 1) → ℂ),
        reducedTimeCutoffWeight (d := d) C₁.cutoff x = 1 := by
    intro x hx
    exact C₁.cutoff_one_on _ (hU₁ (htime x hx))
  have hone₂ :
      ∀ x ∈ tsupport (f : NPointDomain d (k + 1) → ℂ),
        reducedTimeCutoffWeight (d := d) C₂.cutoff x = 1 := by
    intro x hx
    exact C₂.cutoff_one_on _ (hU₂ (htime x hx))
  have hf_disjoint :
      Disjoint
        (tsupport (f : NPointDomain d (k + 1) → ℂ))
        (CoincidenceLocus d (k + 1)) := by
    refine Set.disjoint_left.2 ?_
    intro x hx hcoin
    have hxweight :
        x ∈ tsupport
          (reducedTimeCutoffWeight (d := d) C₁.cutoff) :=
      subset_tsupport
        (reducedTimeCutoffWeight (d := d) C₁.cutoff)
        (by
          change reducedTimeCutoffWeight (d := d) C₁.cutoff x ≠ 0
          rw [hone₁ x hx]
          exact one_ne_zero)
    exact Set.disjoint_left.mp
      (reducedTimeCutoffWeight_tsupport_disjoint
        C₁.cutoff C₁.cutoff_support)
      hxweight hcoin
  have hf : VanishesToInfiniteOrderOnCoincidence f :=
    VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint
      f hf_disjoint
  have hcutoff₁ :
      SchwartzMap.smulLeftCLM ℂ
          (reducedTimeCutoffWeight (d := d) C₁.cutoff) f =
        f :=
    reducedTimeCutoff_smul_eq_of_one_on_tsupport C₁.cutoff f hone₁
  have hcutoff₂ :
      SchwartzMap.smulLeftCLM ℂ
          (reducedTimeCutoffWeight (d := d) C₂.cutoff) f =
        f :=
    reducedTimeCutoff_smul_eq_of_one_on_tsupport C₂.cutoff f hone₂
  change
    canonicalReducedTimeCutoffSchwingerCLM
        OS C₁.cutoff C₁.cutoff_support ψ =
      canonicalReducedTimeCutoffSchwingerCLM
        OS C₂.cutoff C₂.cutoff_support ψ
  calc
    canonicalReducedTimeCutoffSchwingerCLM
          OS C₁.cutoff C₁.cutoff_support ψ =
        canonicalReducedTimeCutoffSchwingerCLM
          OS C₁.cutoff C₁.cutoff_support
            (diffVarReduction d k f) := by rw [hright]
    _ = OS.S (k + 1) ⟨f, hf⟩ :=
      canonicalReducedTimeCutoffSchwingerCLM_apply_diffVarReduction_eq_of_cutoff
        OS C₁.cutoff C₁.cutoff_support f hf hcutoff₁
    _ = canonicalReducedTimeCutoffSchwingerCLM
          OS C₂.cutoff C₂.cutoff_support
            (diffVarReduction d k f) :=
      (canonicalReducedTimeCutoffSchwingerCLM_apply_diffVarReduction_eq_of_cutoff
        OS C₂.cutoff C₂.cutoff_support f hf hcutoff₂).symm
    _ = canonicalReducedTimeCutoffSchwingerCLM
          OS C₂.cutoff C₂.cutoff_support ψ := by rw [hright]

variable
  {A B : OSIITimeContinuationStage d k}
  {W : SchwartzNPoint d k →L[ℂ] ℂ}
  {U : Set (Fin k → ℝ)}

/-- Transfer a represented positive real edge between two stages that agree
on the embedded real patch. -/
noncomputable def positiveRealEdgeData_ofStageAgreement
    (E : B.PositiveRealEdgeData W U)
    (hcarrier :
      ∀ τ ∈ U, osiiPositiveRealTimeEmbed τ ∈ A.carrier)
    (hagrees :
      ∀ τ ∈ U,
        A.distribution (osiiPositiveRealTimeEmbed τ) =
          B.distribution (osiiPositiveRealTimeEmbed τ)) :
    A.PositiveRealEdgeData W U where
  orbit := E.orbit
  stageEdge := fun τ hτ =>
    ⟨hcarrier τ hτ,
      (hagrees τ hτ).trans (E.stageEdge τ hτ).2⟩
  represents := E.represents
  pointwiseBounded := E.pointwiseBounded

/-- Two canonical compact-edge stages agree at every positive-real point
belonging to both selected real regions.  The cutoffs may differ: on the
overlap their represented distributions have the same test pairings, and
continuity upgrades distributional uniqueness to pointwise equality. -/
theorem canonicalReducedCompactStageEdgeData_distribution_eq_of_mem_realRegions
    (OS : OsterwalderSchraderAxioms d)
    {A B : OSIITimeContinuationStage d k}
    {K₁ K₂ : Set (Fin k → ℝ)}
    (D₁ : CanonicalReducedCompactStageEdgeData OS A K₁)
    (D₂ : CanonicalReducedCompactStageEdgeData OS B K₂)
    (τ : Fin k → ℝ)
    (hτ₁ : τ ∈ D₁.realRegion)
    (hτ₂ : τ ∈ D₂.realRegion) :
    A.distribution (osiiPositiveRealTimeEmbed τ) =
      B.distribution (osiiPositiveRealTimeEmbed τ) := by
  apply ContinuousLinearMap.ext
  intro χ
  let U : Set (Fin k → ℝ) := D₁.realRegion ∩ D₂.realRegion
  let T₂ : SchwartzMap (Fin k → ℝ) ℂ →L[ℂ] ℂ :=
    (orderedTransportDistribution
      (canonicalReducedTimeCutoffSchwingerCLM
        OS D₂.cutoff D₂.cutoff_support)).comp
      (section43OrderedPullbackTimeSpatialTensorCLM d k χ)
  let R₁ : (Fin k → ℝ) → ℂ := fun σ => D₁.edge.orbit σ χ
  let R₂ : (Fin k → ℝ) → ℂ := fun σ => D₂.edge.orbit σ χ
  have hR₁_cont : ContinuousOn R₁ U :=
    (A.continuousOn_positiveRealEdge
      D₁.edge.orbit D₁.realRegion D₁.edge.stageEdge χ).mono
      Set.inter_subset_left
  have hR₂_cont : ContinuousOn R₂ U :=
    (B.continuousOn_positiveRealEdge
      D₂.edge.orbit D₂.realRegion D₂.edge.stageEdge χ).mono
      Set.inter_subset_right
  have hR₁_rep : SCV.RepresentsDistributionOn T₂ R₁ U := by
    intro φ hφ
    let T₁ : SchwartzMap (Fin k → ℝ) ℂ →L[ℂ] ℂ :=
      (orderedTransportDistribution
        (canonicalReducedTimeCutoffSchwingerCLM
          OS D₁.cutoff D₁.cutoff_support)).comp
        (section43OrderedPullbackTimeSpatialTensorCLM d k χ)
    have hpair : T₁ φ = T₂ φ := by
      exact orderedCanonicalReducedTimeCutoff_pairing_eq_of_tsupport
        OS D₁.toCutoffData D₂.toCutoffData U
        Set.inter_subset_left Set.inter_subset_right χ φ hφ.2
    calc
      T₂ φ = T₁ φ := hpair.symm
      _ = ∫ σ : Fin k → ℝ, R₁ σ * φ σ :=
        D₁.edge.represents χ φ
          ⟨hφ.1, hφ.2.trans Set.inter_subset_left⟩
  have hR₂_rep : SCV.RepresentsDistributionOn T₂ R₂ U := by
    intro φ hφ
    exact D₂.edge.represents χ φ
      ⟨hφ.1, hφ.2.trans Set.inter_subset_right⟩
  have hR_eq : Set.EqOn R₁ R₂ U := by
    have h :=
      SCV.eqOn_inter_of_representsDistributionOn
        T₂ U U R₁ R₂
        (D₁.realRegion_open.inter D₂.realRegion_open)
        (D₁.realRegion_open.inter D₂.realRegion_open)
        hR₁_cont hR₂_cont hR₁_rep hR₂_rep
    intro σ hσ
    exact h ⟨hσ, hσ⟩
  have hstage₁ :=
    congrArg (fun R : OSIISpatialDistribution d k => R χ)
      (D₁.edge.stageEdge τ hτ₁).2
  have hstage₂ :=
    congrArg (fun R : OSIISpatialDistribution d k => R χ)
      (D₂.edge.stageEdge τ hτ₂).2
  change
    A.distribution (osiiPositiveRealTimeEmbed τ) χ =
      D₁.edge.orbit τ χ at hstage₁
  change
    B.distribution (osiiPositiveRealTimeEmbed τ) χ =
      D₂.edge.orbit τ χ at hstage₂
  exact hstage₁.trans ((hR_eq ⟨hτ₁, hτ₂⟩).trans hstage₂.symm)

/-- Two local canonical stages on the same narrow carrier agree everywhere
once their real regions overlap. -/
theorem canonicalReducedCompactStageEdgeData_distribution_eqOn_narrow
    (OS : OsterwalderSchraderAxioms d)
    {A B : OSIITimeContinuationStage d k}
    {K₁ K₂ : Set (Fin k → ℝ)}
    (D₁ : CanonicalReducedCompactStageEdgeData OS A K₁)
    (D₂ : CanonicalReducedCompactStageEdgeData OS B K₂)
    (η : ℝ)
    (hη : 0 < η)
    (hAcarrier :
      A.carrier = osiiNarrowTimeCarrier (k := k) η)
    (hBcarrier :
      B.carrier = osiiNarrowTimeCarrier (k := k) η)
    (hoverlap : (D₁.realRegion ∩ D₂.realRegion).Nonempty) :
    Set.EqOn A.distribution B.distribution
      (osiiNarrowTimeCarrier (k := k) η) := by
  let U : Set (Fin k → ℝ) := D₁.realRegion ∩ D₂.realRegion
  intro z hz
  apply ContinuousLinearMap.ext
  intro χ
  let F : OSIITimeGapSpace k → ℂ :=
    fun w => A.distribution w χ - B.distribution w χ
  have hF :
      DifferentiableOn ℂ F
        (osiiNarrowTimeCarrier (k := k) η) := by
    have hA :
        DifferentiableOn ℂ (fun w => A.distribution w χ)
          (osiiNarrowTimeCarrier (k := k) η) := by
      simpa [hAcarrier] using A.weaklyHolomorphic χ
    have hB :
        DifferentiableOn ℂ (fun w => B.distribution w χ)
          (osiiNarrowTimeCarrier (k := k) η) := by
      simpa [hBcarrier] using B.weaklyHolomorphic χ
    exact hA.sub hB
  have hU_sub :
      ∀ τ ∈ U,
        SCV.realToComplex τ ∈
          osiiNarrowTimeCarrier (k := k) η := by
    intro τ hτ
    have hmem := (D₁.edge.stageEdge τ hτ.1).1
    simpa [hAcarrier, SCV.realToComplex,
      osiiPositiveRealTimeEmbed] using hmem
  have hF_zero :
      ∀ τ ∈ U, F (SCV.realToComplex τ) = 0 := by
    intro τ hτ
    have hagree :=
      canonicalReducedCompactStageEdgeData_distribution_eq_of_mem_realRegions
        OS D₁ D₂ τ hτ.1 hτ.2
    have hscalar :=
      congrArg (fun R : OSIISpatialDistribution d k => R χ) hagree
    simpa [F, SCV.realToComplex, osiiPositiveRealTimeEmbed] using
      (sub_eq_zero.mpr hscalar)
  have hzero :
      F z = 0 :=
    SCV.identity_theorem_totally_real
      (isOpen_osiiNarrowTimeCarrier η)
      (isConnected_osiiNarrowTimeCarrier η hη)
      hF
      (D₁.realRegion_open.inter D₂.realRegion_open)
      hoverlap
      hU_sub
      hF_zero
      z hz
  exact sub_eq_zero.mp hzero

/-- One compact-dependent local stage on the common narrow carrier. -/
structure CanonicalReducedCompactLocalStageData
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (compactCarrier : Set (Fin k → ℝ)) where
  stage : OSIITimeContinuationStage d k
  carrier :
    stage.carrier = osiiNarrowTimeCarrier (k := k) η
  edge :
    CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier

/-- Local stage existence for every nonempty compact strict-positive carrier. -/
def HasCanonicalReducedCompactLocalStages
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ) : Prop :=
  ∀ compactCarrier : Set (Fin k → ℝ),
    IsCompact compactCarrier →
      compactCarrier.Nonempty →
        compactCarrier ⊆ section43TimeStrictPositiveRegion k →
          Nonempty
            (CanonicalReducedCompactLocalStageData
              OS η compactCarrier)

/-- Compact-dependent local stages on one narrow carrier coherently determine
one fixed stage carrying every canonical compact edge. -/
theorem
    exists_stage_hasCanonicalReducedCompactStageEdges_of_local_with_carrier
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hη : 0 < η)
    (H : HasCanonicalReducedCompactLocalStages
      (k := k) OS η) :
    ∃ stage : OSIITimeContinuationStage d k,
      stage.carrier = osiiNarrowTimeCarrier (k := k) η ∧
        HasCanonicalReducedCompactStageEdges OS stage := by
  let anchor : Fin k → ℝ := fun _ => 1
  have hanchor :
      anchor ∈ section43TimeStrictPositiveRegion k := by
    intro i
    simp [anchor]
  obtain ⟨A⟩ :=
    H {anchor} isCompact_singleton (Set.singleton_nonempty anchor)
      (by
        intro τ hτ
        simpa only [Set.mem_singleton_iff] using hτ ▸ hanchor)
  refine ⟨A.stage, A.carrier, ?_⟩
  intro compactCarrier hcompact hpositive
  by_cases hnonempty : compactCarrier.Nonempty
  · let joined : Set (Fin k → ℝ) :=
      compactCarrier ∪ {anchor}
    have hjoined_compact : IsCompact joined :=
      hcompact.union isCompact_singleton
    have hjoined_nonempty : joined.Nonempty :=
      ⟨anchor, Set.mem_union_right _ (Set.mem_singleton anchor)⟩
    have hjoined_positive :
        joined ⊆ section43TimeStrictPositiveRegion k := by
      intro τ hτ
      rcases hτ with hτ | hτ
      · exact hpositive hτ
      · simpa only [Set.mem_singleton_iff] using hτ ▸ hanchor
    obtain ⟨B⟩ :=
      H joined hjoined_compact hjoined_nonempty hjoined_positive
    have hoverlap :
        (A.edge.realRegion ∩ B.edge.realRegion).Nonempty := by
      refine ⟨anchor, ?_, ?_⟩
      · exact A.edge.compactCarrier_subset (Set.mem_singleton anchor)
      · exact B.edge.compactCarrier_subset
          (Set.mem_union_right compactCarrier
            (Set.mem_singleton anchor))
    have hagrees :=
      canonicalReducedCompactStageEdgeData_distribution_eqOn_narrow
        OS A.edge B.edge η hη A.carrier B.carrier hoverlap
    have hreal_mem :
        ∀ τ ∈ B.edge.realRegion,
          osiiPositiveRealTimeEmbed τ ∈
            osiiNarrowTimeCarrier (k := k) η := by
      intro τ hτ
      have hmem := (B.edge.edge.stageEdge τ hτ).1
      simpa [B.carrier] using hmem
    let transferred :
        A.stage.PositiveRealEdgeData
          (orderedTransportDistribution
            (canonicalReducedTimeCutoffSchwingerCLM
              OS B.edge.cutoff B.edge.cutoff_support))
          B.edge.realRegion :=
      positiveRealEdgeData_ofStageAgreement B.edge.edge
        (fun τ hτ => by
          rw [A.carrier]
          exact hreal_mem τ hτ)
        (fun τ hτ => hagrees (hreal_mem τ hτ))
    exact ⟨{
      cutoff := B.edge.cutoff
      cutoff_support := B.edge.cutoff_support
      cutoff_compact := B.edge.cutoff_compact
      realRegion := B.edge.realRegion
      realRegion_open := B.edge.realRegion_open
      compactCarrier_subset := fun τ hτ =>
        B.edge.compactCarrier_subset (Set.mem_union_left _ hτ)
      cutoff_one_on := B.edge.cutoff_one_on
      edge := transferred }⟩
  · exact ⟨{
      cutoff := A.edge.cutoff
      cutoff_support := A.edge.cutoff_support
      cutoff_compact := A.edge.cutoff_compact
      realRegion := A.edge.realRegion
      realRegion_open := A.edge.realRegion_open
      compactCarrier_subset := fun τ hτ =>
        (hnonempty ⟨τ, hτ⟩).elim
      cutoff_one_on := A.edge.cutoff_one_on
      edge := A.edge.edge }⟩

/-- Every genuine approximate-identity scale has the canonical fixed-smearing
edge and its original-OS finite-packet approximation. -/
theorem exists_initialTimeContinuationStage_with_canonicalTimeSmearingEdge_and_limit_ofOS
    (I : Section43ProductTimeApproximateIdentity k)
    (n : ℕ)
    (cutoff : SchwartzMap (Fin k → ℝ) ℂ)
    (hcutoff_positive :
      tsupport (cutoff : (Fin k → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion k)
    (U : Set (Fin k → ℝ))
    (hU_positive : U ⊆ section43TimeStrictPositiveRegion k)
    (hcutoff_one :
      ∀ τ ∈ U, ∀ s ∈
        tsupport
          ((SCV.translateSchwartz (-τ) (I.test n) :
            SchwartzMap (Fin k → ℝ) ℂ) :
              (Fin k → ℝ) → ℂ),
        cutoff s = 1)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ) (hη : 0 < η)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2) :
    ∃ A : OSIITimeContinuationStage d k,
      A.carrier = osiiNarrowTimeCarrier (k := k) η ∧
        OSIIComplexTimeSpatialLocallyPointwiseBoundedOn
          A.distribution
          (osiiNarrowTimeCarrier (k := k) η) ∧
        (∀ ζ, ζ ∈ osiiNarrowTimeCarrier (k := k) η →
          ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
            Tendsto
              (fun level =>
                initialSpatialFactorPacketDistributionOfOS
                  OS (I.test n) (I.test_compact n) (I.test_positive n)
                    η hηsum level ζ χ)
              atTop
              (nhds (A.distribution ζ χ))) ∧
        A.HasPositiveRealEdge
          (fun τ =>
            osiiTranslatedTimeSmearedSpatialDistribution
              (orderedTransportDistribution
                (canonicalReducedTimeCutoffSchwingerCLM
                  OS cutoff hcutoff_positive))
              (I.test n) τ)
          U := by
  obtain ⟨A, hA_carrier, hA_bounded, hA_limit, hA_real⟩ :=
    Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData.exists_initialTimeContinuationStageWithRealEdgeOfOS
      I n OS η hη hηsum
  refine ⟨A, hA_carrier, hA_bounded, hA_limit, ?_⟩
  intro τ hτ
  have hτ_positive := hU_positive hτ
  refine
    ⟨hA_carrier.symm ▸
        osiiPositiveRealTimeEmbed_mem_osiiNarrowTimeCarrier
          η hη τ hτ_positive, ?_⟩
  ext χ
  let htranslated_positive :
      tsupport
          ((SCV.translateSchwartz (-τ) (I.test n) :
            SchwartzMap (Fin k → ℝ) ℂ) :
              (Fin k → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion k :=
    (translate_positiveOrthant_schwartz_mem
      (I.test n) (I.test_positive n) (I.test_compact n)
        τ hτ_positive).1
  let hzero :
      VanishesToInfiniteOrderOnCoincidence
        (initialReducedSpatialFullSourceCLM (d := d)
          (SCV.translateSchwartz (-τ) (I.test n)) χ) :=
    initialReducedSpatialFullSource_vanishes_of_tsupport_strictPositive
      (d := d) (SCV.translateSchwartz (-τ) (I.test n)) χ
        htranslated_positive
  have hone :
      ∀ y ∈ tsupport
          ((initialReducedSpatialFullSourceCLM (d := d)
              (SCV.translateSchwartz (-τ) (I.test n)) χ :
            SchwartzNPoint d (k + 1)) :
              NPointDomain d (k + 1) → ℂ),
        reducedTimeCutoffWeight (d := d) cutoff y = 1 := by
    intro y hy
    rw [reducedTimeCutoffWeight]
    exact hcutoff_one τ hτ _
      (reducedTimeProjection_mem_tsupport_of_mem_initialReducedSpatialFullSource
        (SCV.translateSchwartz (-τ) (I.test n)) χ y hy)
  have hcutoff :
      SchwartzMap.smulLeftCLM ℂ
          (reducedTimeCutoffWeight (d := d) cutoff)
          (initialReducedSpatialFullSourceCLM (d := d)
            (SCV.translateSchwartz (-τ) (I.test n)) χ) =
        initialReducedSpatialFullSourceCLM (d := d)
          (SCV.translateSchwartz (-τ) (I.test n)) χ :=
    reducedTimeCutoff_smul_eq_of_one_on_tsupport
      cutoff _ hone
  calc
    A.distribution (osiiPositiveRealTimeEmbed τ) χ =
        OS.S (k + 1)
          ⟨initialReducedSpatialFullSourceCLM (d := d)
              (SCV.translateSchwartz (-τ) (I.test n)) χ,
            hzero⟩ :=
      hA_real τ hτ_positive χ
    _ =
        osiiTranslatedTimeSmearedSpatialDistribution
          (orderedTransportDistribution
            (canonicalReducedTimeCutoffSchwingerCLM
              OS cutoff hcutoff_positive))
          (I.test n) τ χ :=
      (canonicalTranslatedTimeSmearedSpatialDistribution_apply_eq_schwinger
        OS cutoff hcutoff_positive τ (I.test n) χ hzero hcutoff).symm

/-- The original OS packet bound constructs the entire shrinking-smearing
stage family, retaining its genuinely scale-uniform finite approximation. -/
theorem exists_initialTimeSmearingStageFamily_with_scaleUniformApproximation_ofOS
    (compactCarrier : Set (Fin k → ℝ))
    (hcompact : IsCompact compactCarrier)
    (C : CanonicalReducedCompactCutoffData compactCarrier)
    (I : Section43ProductTimeApproximateIdentity k)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ) (hη : 0 < η)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2) :
    ∃ realRegion : Set (Fin k → ℝ),
      IsOpen realRegion ∧
        compactCarrier ⊆ realRegion ∧
        realRegion ⊆ C.realRegion ∧
        ∃ tailStart : ℕ,
          ∃ F : InitialTimeSmearingStageFamilyData
              OS I C realRegion tailStart η,
            Nonempty
              (InitialTimeSmearingStageFamilyData.ScaleUniformApproximationData F) := by
  obtain ⟨r, hr_pos, hr_sub⟩ :=
    hcompact.exists_cthickening_subset_open
      C.realRegion_open C.compactCarrier_subset
  let r₂ : ℝ := r / 2
  have hr₂_pos : 0 < r₂ := half_pos hr_pos
  have hr₂_le : r₂ ≤ r := by
    dsimp [r₂]
    linarith
  let realRegion : Set (Fin k → ℝ) :=
    Metric.thickening r₂ compactCarrier
  have hcarrier_region : compactCarrier ⊆ realRegion :=
    Metric.self_subset_thickening hr₂_pos compactCarrier
  have hregion_cutoff : realRegion ⊆ C.realRegion :=
    (Metric.thickening_subset_cthickening_of_le
      hr₂_le compactCarrier).trans hr_sub
  let realCompact : Set (Fin k → ℝ) :=
    Metric.cthickening r₂ compactCarrier
  have hregion_compact : realRegion ⊆ realCompact :=
    Metric.thickening_subset_cthickening_of_le
      (le_refl r₂) compactCarrier
  have hrealCompact_compact : IsCompact realCompact :=
    hcompact.cthickening
  have hrealCompact_cutoff : realCompact ⊆ C.realRegion :=
    (Metric.cthickening_mono hr₂_le compactCarrier).trans hr_sub
  have hrealCompact_positive :
      realCompact ⊆ section43TimeStrictPositiveRegion k := by
    intro τ hτ
    apply C.cutoff_support
    apply subset_tsupport
    change C.cutoff τ ≠ 0
    rw [C.cutoff_one_on τ (hrealCompact_cutoff hτ)]
    exact one_ne_zero
  have hradius_small :
      ∀ᶠ N : ℕ in atTop, I.radius N < r₂ := by
    have hdist :
        ∀ᶠ N : ℕ in atTop, dist (I.radius N) 0 < r₂ :=
      (Metric.tendsto_nhds.mp I.radius_tendsto) r₂ hr₂_pos
    filter_upwards [hdist] with N hN
    rw [Real.dist_eq] at hN
    exact lt_of_le_of_lt (le_abs_self (I.radius N)) (by simpa using hN)
  rw [eventually_atTop] at hradius_small
  obtain ⟨tailStart, htail⟩ := hradius_small
  have hcutoff_one :
      ∀ N τ, τ ∈ realRegion →
        ∀ s ∈
          tsupport
            ((SCV.translateSchwartz (-τ) (I.test (N + tailStart)) :
              SchwartzMap (Fin k → ℝ) ℂ) :
                (Fin k → ℝ) → ℂ),
          C.cutoff s = 1 := by
    intro N τ hτ s hs
    have hs_pre :
        s + (-τ) ∈
          tsupport (I.test (N + tailStart) : (Fin k → ℝ) → ℂ) :=
      tsupport_comp_subset_preimage
        (I.test (N + tailStart) : (Fin k → ℝ) → ℂ)
        (f := fun y : Fin k → ℝ => y + (-τ))
        (Homeomorph.addRight (-τ)).continuous hs
    have htest_closed :
        tsupport (I.test (N + tailStart) : (Fin k → ℝ) → ℂ) ⊆
          Metric.closedBall (0 : Fin k → ℝ)
            (I.radius (N + tailStart)) := by
      change
        closure
            (Function.support
              (I.test (N + tailStart) : (Fin k → ℝ) → ℂ)) ⊆
          Metric.closedBall (0 : Fin k → ℝ)
            (I.radius (N + tailStart))
      exact
        closure_minimal
          (fun y hy =>
            Metric.ball_subset_closedBall
              (I.support (N + tailStart) hy))
          Metric.isClosed_closedBall
    have hs_radius :
        dist (s + (-τ)) 0 ≤ I.radius (N + tailStart) :=
      Metric.mem_closedBall.mp (htest_closed hs_pre)
    have hsτ : dist s τ < r₂ := by
      have hdist_eq : dist s τ = dist (s + (-τ)) 0 := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        ext i
        simp [Pi.sub_apply, sub_eq_add_neg]
      rw [hdist_eq]
      exact hs_radius.trans_lt
        (htail (N + tailStart) (Nat.le_add_left tailStart N))
    obtain ⟨q, hq, hτq⟩ :=
      Metric.mem_thickening_iff.mp hτ
    apply C.cutoff_one_on s
    apply hr_sub
    apply Metric.mem_cthickening_of_dist_le s q r compactCarrier hq
    exact le_of_lt <| calc
      dist s q ≤ dist s τ + dist τ q := dist_triangle _ _ _
      _ < r₂ + r₂ := add_lt_add hsτ hτq
      _ = r := by
        dsimp [r₂]
        ring
  have hstage :
      ∀ N,
        ∃ A : OSIITimeContinuationStage d k,
          A.carrier = osiiNarrowTimeCarrier (k := k) η ∧
            OSIIComplexTimeSpatialLocallyPointwiseBoundedOn
              A.distribution
              (osiiNarrowTimeCarrier (k := k) η) ∧
            (∀ ζ, ζ ∈ osiiNarrowTimeCarrier (k := k) η →
              ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
                Tendsto
                  (fun level =>
                    initialSpatialFactorPacketDistributionOfOS
                      OS (I.test (N + tailStart))
                        (I.test_compact (N + tailStart))
                        (I.test_positive (N + tailStart))
                        η hηsum level ζ χ)
                  atTop
                  (nhds (A.distribution ζ χ))) ∧
            A.HasPositiveRealEdge
              (fun τ =>
                osiiTranslatedTimeSmearedSpatialDistribution
                  (orderedTransportDistribution
                    (canonicalReducedTimeCutoffSchwingerCLM
                      OS C.cutoff C.cutoff_support))
                  (I.test (N + tailStart)) τ)
              realRegion := by
    intro N
    exact
      exists_initialTimeContinuationStage_with_canonicalTimeSmearingEdge_and_limit_ofOS
        I (N + tailStart)
        C.cutoff C.cutoff_support
        realRegion
        (by
          intro τ hτ
          apply C.cutoff_support
          apply subset_tsupport
          change C.cutoff τ ≠ 0
          rw [C.cutoff_one_on τ (hregion_cutoff hτ)]
          exact one_ne_zero)
        (hcutoff_one N)
        OS η hη hηsum
  choose stage hstage_carrier hstage_bounded hstage_limit hstage_edge using hstage
  let F : InitialTimeSmearingStageFamilyData
      OS I C realRegion tailStart η := {
    realCompact := realCompact
    realRegion_open := Metric.isOpen_thickening
    compactCarrier_subset_realRegion := hcarrier_region
    realRegion_subset_cutoffRegion := hregion_cutoff
    realRegion_subset_realCompact := hregion_compact
    realCompact_compact := hrealCompact_compact
    realCompact_positive := hrealCompact_positive
    stage := stage
    carrier := hstage_carrier
    locallyPointwiseBounded := hstage_bounded
    edge := hstage_edge }
  refine
    ⟨realRegion, Metric.isOpen_thickening,
      hcarrier_region, hregion_cutoff, tailStart, F, ⟨{
        approximation := fun N level =>
          initialSpatialFactorPacketDistributionOfOS
            OS (I.test (N + tailStart))
              (I.test_compact (N + tailStart))
              (I.test_positive (N + tailStart))
              η hηsum level
        tendsto_stage := hstage_limit
        compact_bound := ?_ }⟩⟩
  intro K hK_compact hK_subset χ
  exact
    Section43ProductTimeApproximateIdentity.AnchoredPacketTimeShellFamilyData.initialSpatialFactorPacketDistributionOfOS_scaleUniform_compact_bound
      I OS η hη hηsum tailStart K hK_compact hK_subset χ

/-- Original OS axioms suffice to construct the local unsmeared initial stage
around every nonempty compact positive-time carrier. -/
theorem hasCanonicalReducedCompactLocalStages_ofOS
    (OS : OsterwalderSchraderAxioms d)
    (I : Section43ProductTimeApproximateIdentity k)
    (η : ℝ)
    (hη : 0 < η)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2) :
    HasCanonicalReducedCompactLocalStages
      (k := k) OS η := by
  intro compactCarrier hcompact hnonempty hpositive
  obtain ⟨C⟩ :=
    CanonicalReducedCompactCutoffData.nonempty
      compactCarrier hcompact hpositive
  obtain ⟨realRegion, hreal_open, hcompact_real, _hreal_cutoff,
      _tailStart, F, hP⟩ :=
    exists_initialTimeSmearingStageFamily_with_scaleUniformApproximation_ofOS
      compactCarrier hcompact C I OS η hη hηsum
  obtain ⟨P⟩ := hP
  have hreal_nonempty : realRegion.Nonempty := by
    obtain ⟨τ, hτ⟩ := hnonempty
    exact ⟨τ, hcompact_real hτ⟩
  obtain ⟨D⟩ :=
    InitialTimeSmearingStageFamilyData.NormalFamilyLimitData.nonempty_distributional_of_scaleUniform
      hη hreal_open hreal_nonempty
      P.scaleUniformLocallyPointwiseBounded
  exact ⟨{
    stage := D.toNormalFamilyLimitData.limitStage
    carrier := rfl
    edge := D.limitCanonicalReducedCompactStageEdgeData hη }⟩

/-- At every positive arity, the complete initial narrow continuation stage
and all its canonical compact real edges follow from the original OS axioms. -/
theorem exists_initialStage_hasCanonicalReducedCompactStageEdges_with_carrier_ofOS
    (OS : OsterwalderSchraderAxioms d)
    (I : Section43ProductTimeApproximateIdentity k)
    (η : ℝ)
    (hη : 0 < η)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2) :
    ∃ stage : OSIITimeContinuationStage d k,
      stage.carrier = osiiNarrowTimeCarrier (k := k) η ∧
        HasCanonicalReducedCompactStageEdges OS stage :=
  exists_stage_hasCanonicalReducedCompactStageEdges_of_local_with_carrier
    OS η hη
    (hasCanonicalReducedCompactLocalStages_ofOS
      OS I η hη hηsum)

end OSIIChapterV
end OSReconstruction
