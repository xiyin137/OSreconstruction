/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialSpatialFactorCover
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialCompactStage
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIISpatialExhaustionStage
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIDeltaSmearing
import OSReconstruction.SCV.TotallyRealIdentity















noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d] [NeZero k]

/-- The finite chronological cover and common packet slope selected at one
factorwise spatial truncation level. -/
structure InitialSpatialFactorPacketData
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (N : ℕ) where
  cover :
    SpatialChronologicalCompactCoverData
      (initialReducedSpatialFactorCompactSourceCLM (d := d) φ N)
  slope : ℝ
  slope_gt_one : 1 < slope
  ordered : cover.AxisPairOrderedAt slope

/-- Every factorwise level with compact strict-positive reduced-time support
admits the finite packet data required by
`InitialSpatialFactorPacketData`. -/
theorem nonempty_initialSpatialFactorPacketData
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (hφ_compact :
      HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (N : ℕ)
    (hφ_positive :
      tsupport (φ : (Fin k → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion k) :
    Nonempty (InitialSpatialFactorPacketData (d := d) φ N) := by
  obtain ⟨D⟩ :=
    nonempty_initialReducedSpatialFactorCompactSource_spatialChronologicalCompactCoverData
      (d := d) φ hφ_compact N hφ_positive
  obtain ⟨T, hT, hordered⟩ := D.exists_common_axisPairSlope
  exact
    ⟨{
      cover := D
      slope := T
      slope_gt_one := hT
      ordered := hordered }⟩

/-- A fixed noncomputable selection of the finite packet data at every
factorwise truncation level. -/
noncomputable def initialSpatialFactorPacketData
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (hφ_compact :
      HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (hφ_positive :
      tsupport (φ : (Fin k → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion k)
    (N : ℕ) :
    InitialSpatialFactorPacketData (d := d) φ N :=
  Classical.choice
    (nonempty_initialSpatialFactorPacketData
      (d := d) φ hφ_compact N hφ_positive)

namespace InitialSpatialFactorPacketData

/-- The factorwise level packet distribution comes directly from the
original-OS finite compact continuation stage. -/
noncomputable def narrowDistributionOfOS
    {φ : SchwartzMap (Fin k → ℝ) ℂ}
    {N : ℕ}
    (P : InitialSpatialFactorPacketData (d := d) φ N)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2) :
    OSIITimeGapSpace k → OSIISpatialDistribution d k :=
  P.cover.packetSpatialDistribution OS
    P.slope P.slope_gt_one P.ordered
    (osiiNarrowTimeStageChart P.slope
      (lt_trans zero_lt_one P.slope_gt_one) η hηsum)

/-- Every original-OS factorwise level packet is weakly holomorphic on the
common narrow carrier. -/
theorem narrowDistributionOfOS_weaklyHolomorphic
    {φ : SchwartzMap (Fin k → ℝ) ℂ}
    {N : ℕ}
    (P : InitialSpatialFactorPacketData (d := d) φ N)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2) :
    OSIIWeaklyHolomorphicOn
      (P.narrowDistributionOfOS OS η hηsum)
      (osiiNarrowTimeCarrier (k := k) η) :=
  P.cover.packetSpatialDistribution_weaklyHolomorphic
    OS P.slope P.slope_gt_one P.ordered
    (osiiNarrowTimeStageChart P.slope
      (lt_trans zero_lt_one P.slope_gt_one) η hηsum)

/-- The original-OS factorwise packet has its exact positive-real Schwinger
edge on every strict-positive time configuration. -/
theorem narrowDistributionOfOS_realEdge
    {φ : SchwartzMap (Fin k → ℝ) ℂ}
    {N : ℕ}
    (P : InitialSpatialFactorPacketData (d := d) φ N)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ) (hη : 0 < η)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (τ : Fin k → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    P.narrowDistributionOfOS OS η hηsum
        (osiiPositiveRealTimeEmbed τ) χ =
      OS.S (k + 1)
        (P.cover.localizedTranslatedZeroSum
          P.slope P.slope_gt_one P.ordered
          (osiiNarrowTimeRealCoordinate (d := d) P.slope τ) χ) :=
  P.cover.packetSpatialDistribution_narrow_realEdge
    OS P.slope P.slope_gt_one P.ordered
    η hη hηsum τ hτ χ

/-- If two factorwise truncations equal the same full source on one spatial
test, their selected packet branches agree throughout the common narrow
carrier. The covers and slopes may be unrelated. -/
theorem narrowDistributionOfOS_eqOn_of_source_eq
    {φ : SchwartzMap (Fin k → ℝ) ℂ}
    {N M : ℕ}
    (P : InitialSpatialFactorPacketData (d := d) φ N)
    (Q : InitialSpatialFactorPacketData (d := d) φ M)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ) (hη : 0 < η)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (hN :
      initialReducedSpatialFactorCompactSourceCLM
          (d := d) φ N χ =
        initialReducedSpatialFullSourceCLM (d := d) φ χ)
    (hM :
      initialReducedSpatialFactorCompactSourceCLM
          (d := d) φ M χ =
        initialReducedSpatialFullSourceCLM (d := d) φ χ) :
    Set.EqOn
      (fun ζ => P.narrowDistributionOfOS OS η hηsum ζ χ)
      (fun ζ => Q.narrowDistributionOfOS OS η hηsum ζ χ)
      (osiiNarrowTimeCarrier (k := k) η) := by
  let U := osiiNarrowTimeCarrier (k := k) η
  let F : OSIITimeGapSpace k → ℂ :=
    fun ζ =>
      P.narrowDistributionOfOS OS η hηsum ζ χ -
        Q.narrowDistributionOfOS OS η hηsum ζ χ
  have hF : DifferentiableOn ℂ F U :=
    (P.narrowDistributionOfOS_weaklyHolomorphic OS η hηsum χ).sub
      (Q.narrowDistributionOfOS_weaklyHolomorphic OS η hηsum χ)
  have hreal :
      ∀ τ ∈ section43TimeStrictPositiveRegion k,
        P.narrowDistributionOfOS OS η hηsum
            (osiiPositiveRealTimeEmbed τ) χ =
          Q.narrowDistributionOfOS OS η hηsum
            (osiiPositiveRealTimeEmbed τ) χ := by
    intro τ hτ
    rw [P.narrowDistributionOfOS_realEdge OS η hη hηsum τ hτ χ,
      Q.narrowDistributionOfOS_realEdge OS η hη hηsum τ hτ χ]
    apply congrArg (OS.S (k + 1))
    apply SetCoe.ext
    rw [P.cover.localizedTranslatedZeroSum_coe,
      Q.cover.localizedTranslatedZeroSum_coe,
      hN, hM,
      translate_initialReducedSpatialFullSource_narrow
        P.slope (lt_trans zero_lt_one P.slope_gt_one) τ hτ φ χ,
      translate_initialReducedSpatialFullSource_narrow
        Q.slope (lt_trans zero_lt_one Q.slope_gt_one) τ hτ φ χ]
  have hpositive_nonempty :
      (section43TimeStrictPositiveRegion k).Nonempty := by
    refine ⟨fun _ => 1, ?_⟩
    intro i
    simp
  have hpositive_sub :
      ∀ τ ∈ section43TimeStrictPositiveRegion k,
        SCV.realToComplex τ ∈ U := by
    intro τ hτ
    simpa [U, SCV.realToComplex, osiiPositiveRealTimeEmbed] using
      osiiPositiveRealTimeEmbed_mem_osiiNarrowTimeCarrier
        η hη τ hτ
  have hF_zero :
      ∀ τ ∈ section43TimeStrictPositiveRegion k,
        F (SCV.realToComplex τ) = 0 := by
    intro τ hτ
    simpa [F, osiiPositiveRealTimeEmbed] using
      sub_eq_zero.mpr (hreal τ hτ)
  intro ζ hζ
  have hz :
      F ζ = 0 :=
    SCV.identity_theorem_totally_real
      (isOpen_osiiNarrowTimeCarrier η)
      (isConnected_osiiNarrowTimeCarrier η hη)
      hF
      (isOpen_section43TimeStrictPositiveRegion k)
      hpositive_nonempty
      hpositive_sub
      hF_zero
      ζ hζ
  exact sub_eq_zero.mp hz

end InitialSpatialFactorPacketData

/-- The selected level-`N` factorwise packet distribution follows directly
from the original OS axioms. -/
noncomputable def initialSpatialFactorPacketDistributionOfOS
    (OS : OsterwalderSchraderAxioms d)
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (hφ_compact :
      HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (hφ_positive :
      tsupport (φ : (Fin k → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion k)
    (η : ℝ)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (N : ℕ) :
    OSIITimeGapSpace k → OSIISpatialDistribution d k :=
  (initialSpatialFactorPacketData
    (d := d) φ hφ_compact hφ_positive N
    ).narrowDistributionOfOS OS η hηsum

/-- On the positive real slice, spatial-factor packet exhaustion converges to
the unlocalized Schwinger value with the translated reduced-time factor. -/
theorem initialSpatialFactorPacketDistributionOfOS_realEdge_tendsto
    (OS : OsterwalderSchraderAxioms d)
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (hφ_compact :
      HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (hφ_positive :
      tsupport (φ : (Fin k → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion k)
    (η : ℝ) (hη : 0 < η)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (τ : Fin k → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion k)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ) :
    Tendsto
      (fun N =>
        initialSpatialFactorPacketDistributionOfOS
          OS φ hφ_compact hφ_positive η hηsum N
            (osiiPositiveRealTimeEmbed τ) χ)
      atTop
      (nhds
        (OS.S (k + 1)
          ⟨initialReducedSpatialFullSourceCLM (d := d)
              (SCV.translateSchwartz (-τ) φ) χ,
            initialReducedSpatialFullSource_vanishes_of_tsupport_strictPositive
              (d := d) (SCV.translateSchwartz (-τ) φ) χ
              (translate_positiveOrthant_schwartz_mem
                φ hφ_positive hφ_compact τ hτ).1⟩)) := by
  let P : (N : ℕ) → InitialSpatialFactorPacketData (d := d) φ N :=
    fun N =>
      initialSpatialFactorPacketData
        (d := d) φ hφ_compact hφ_positive N
  let z : ℕ → ZeroDiagonalSchwartz d (k + 1) :=
    fun N =>
      (P N).cover.localizedTranslatedZeroSum
        (P N).slope (P N).slope_gt_one (P N).ordered
        (osiiNarrowTimeRealCoordinate (d := d) (P N).slope τ) χ
  let zlim : ZeroDiagonalSchwartz d (k + 1) :=
    ⟨initialReducedSpatialFullSourceCLM (d := d)
        (SCV.translateSchwartz (-τ) φ) χ,
      initialReducedSpatialFullSource_vanishes_of_tsupport_strictPositive
        (d := d) (SCV.translateSchwartz (-τ) φ) χ
        (translate_positiveOrthant_schwartz_mem
          φ hφ_positive hφ_compact τ hτ).1⟩
  have hz : Tendsto z atTop (nhds zlim) := by
    have hcoe :
        Tendsto (fun N => (z N).1) atTop (nhds zlim.1) := by
      convert
        initialReducedSpatialFactorCompactSource_tendsto
          (d := d) (SCV.translateSchwartz (-τ) φ) χ using 1
      funext N
      dsimp only [z, zlim]
      rw [
        SpatialChronologicalCompactCoverData.localizedTranslatedZeroSum_coe,
        initialReducedSpatialFactorCompactSourceCLM_apply,
        translate_initialReducedSpatialFullSource_narrow
          (initialSpatialFactorPacketData
            (d := d) φ hφ_compact hφ_positive N).slope
          (lt_trans zero_lt_one
            (initialSpatialFactorPacketData
              (d := d) φ hφ_compact hφ_positive N).slope_gt_one)
          τ hτ φ
          (initialSpatialFactorTruncationCLM d k N χ)]
      rfl
    set_option backward.isDefEq.respectTransparency false in
      exact tendsto_subtype_rng.2 hcoe
  have hS :
      Tendsto
        (fun N => OS.S (k + 1) (z N))
        atTop
        (nhds (OS.S (k + 1) zlim)) :=
    ((OsterwalderSchraderAxioms.schwingerCLM
      (d := d) OS (k + 1)).continuous.tendsto zlim).comp hz
  convert hS using 1
  funext N
  exact
    (P N).narrowDistributionOfOS_realEdge
      OS η hη hηsum τ hτ χ

/-- On every compactly supported spatial test, the selected factorwise packet
distributions stabilize to one holomorphic scalar function on the full
common narrow carrier. -/
theorem initialSpatialFactorPacketDistributionOfOS_compactSupport_tendsto
    (OS : OsterwalderSchraderAxioms d)
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (hφ_compact :
      HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (hφ_positive :
      tsupport (φ : (Fin k → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion k)
    (η : ℝ) (hη : 0 < η)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (χ : SchwartzMap (Section43SpatialSpace d k) ℂ)
    (hχ_compact :
      HasCompactSupport
        (χ : Section43SpatialSpace d k → ℂ)) :
    ∃ f : OSIITimeGapSpace k → ℂ,
      DifferentiableOn ℂ f
        (osiiNarrowTimeCarrier (k := k) η) ∧
        ∀ ζ, ζ ∈ osiiNarrowTimeCarrier (k := k) η →
          Tendsto
            (fun N =>
              initialSpatialFactorPacketDistributionOfOS
                OS φ hφ_compact hφ_positive η hηsum N ζ χ)
            atTop
            (nhds (f ζ)) := by
  obtain ⟨N₀, hsource⟩ :=
    Filter.eventually_atTop.1
      (eventually_initialReducedSpatialFactorCompactSource_eq
        (d := d) φ χ hχ_compact)
  let f : OSIITimeGapSpace k → ℂ :=
    fun ζ =>
      initialSpatialFactorPacketDistributionOfOS
        OS φ hφ_compact hφ_positive η hηsum N₀ ζ χ
  refine ⟨f, ?_, ?_⟩
  · exact
      (initialSpatialFactorPacketData
        (d := d) φ hφ_compact hφ_positive N₀
        ).narrowDistributionOfOS_weaklyHolomorphic
          OS η hηsum χ
  · intro ζ hζ
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [Filter.eventually_ge_atTop N₀] with N hN
    exact
      (InitialSpatialFactorPacketData.narrowDistributionOfOS_eqOn_of_source_eq
        (initialSpatialFactorPacketData
          (d := d) φ hφ_compact hφ_positive N)
        (initialSpatialFactorPacketData
          (d := d) φ hφ_compact hφ_positive N₀)
        OS η hη hηsum χ
        (hsource N hN)
        (hsource N₀ le_rfl)) hζ

/-- Route-facing factorwise exhaustion theorem. Compact-test convergence is
automatic; the remaining input is the packet estimate uniform in the
factorwise truncation level on compact complex-time sets. -/
theorem exists_initialTimeContinuationStageOfOS_of_factorwise_uniformBound
    (OS : OsterwalderSchraderAxioms d)
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (hφ_compact :
      HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (hφ_positive :
      tsupport (φ : (Fin k → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion k)
    (η : ℝ) (hη : 0 < η)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (hbounded :
      ∀ K : Set (OSIITimeGapSpace k),
        IsCompact K →
        K ⊆ osiiNarrowTimeCarrier (k := k) η →
          ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
            ∃ C : ℝ, ∀ N ζ, ζ ∈ K →
              ‖initialSpatialFactorPacketDistributionOfOS
                OS φ hφ_compact hφ_positive
                  η hηsum N ζ χ‖ ≤ C) :
    ∃ A : OSIITimeContinuationStage d k,
      A.carrier = osiiNarrowTimeCarrier (k := k) η ∧
        OSIIComplexTimeSpatialLocallyPointwiseBoundedOn
          A.distribution
          (osiiNarrowTimeCarrier (k := k) η) ∧
        ∀ ζ, ζ ∈ osiiNarrowTimeCarrier (k := k) η →
          ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
            Tendsto
              (fun N =>
                initialSpatialFactorPacketDistributionOfOS
                  OS φ hφ_compact hφ_positive
                    η hηsum N ζ χ)
              atTop
              (nhds (A.distribution ζ χ)) := by
  apply
    exists_osiiTimeContinuationStage_of_compactSupport_exhaustion
      (T :=
        initialSpatialFactorPacketDistributionOfOS
          OS φ hφ_compact hφ_positive η hηsum)
      (U := osiiNarrowTimeCarrier (k := k) η)
      (isOpen_osiiNarrowTimeCarrier η)
  · intro χ hχ
    exact
      initialSpatialFactorPacketDistributionOfOS_compactSupport_tendsto
        OS φ hφ_compact hφ_positive η hη hηsum χ hχ
  · exact hbounded

/-- An original-OS factorwise exhaustion with its genuine compact bound
recovers the exact untruncated positive-real Schwinger edge. -/
theorem exists_initialTimeContinuationStageOfOS_with_realEdge_of_factorwise_uniformBound
    (OS : OsterwalderSchraderAxioms d)
    (φ : SchwartzMap (Fin k → ℝ) ℂ)
    (hφ_compact :
      HasCompactSupport (φ : (Fin k → ℝ) → ℂ))
    (hφ_positive :
      tsupport (φ : (Fin k → ℝ) → ℂ) ⊆
        section43TimeStrictPositiveRegion k)
    (η : ℝ) (hη : 0 < η)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2)
    (hbounded :
      ∀ K : Set (OSIITimeGapSpace k),
        IsCompact K →
        K ⊆ osiiNarrowTimeCarrier (k := k) η →
          ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
            ∃ C : ℝ, ∀ N ζ, ζ ∈ K →
              ‖initialSpatialFactorPacketDistributionOfOS
                OS φ hφ_compact hφ_positive
                  η hηsum N ζ χ‖ ≤ C) :
    ∃ A : OSIITimeContinuationStage d k,
      A.carrier = osiiNarrowTimeCarrier (k := k) η ∧
        OSIIComplexTimeSpatialLocallyPointwiseBoundedOn
          A.distribution
          (osiiNarrowTimeCarrier (k := k) η) ∧
        (∀ ζ, ζ ∈ osiiNarrowTimeCarrier (k := k) η →
          ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
            Tendsto
              (fun N =>
                initialSpatialFactorPacketDistributionOfOS
                  OS φ hφ_compact hφ_positive
                    η hηsum N ζ χ)
              atTop
              (nhds (A.distribution ζ χ))) ∧
        ∀ τ, ∀ hτ : τ ∈ section43TimeStrictPositiveRegion k,
          ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
            A.distribution (osiiPositiveRealTimeEmbed τ) χ =
              OS.S (k + 1)
                ⟨initialReducedSpatialFullSourceCLM (d := d)
                    (SCV.translateSchwartz (-τ) φ) χ,
                  initialReducedSpatialFullSource_vanishes_of_tsupport_strictPositive
                    (d := d) (SCV.translateSchwartz (-τ) φ) χ
                    (translate_positiveOrthant_schwartz_mem
                      φ hφ_positive hφ_compact τ hτ).1⟩ := by
  obtain ⟨A, hA_carrier, hA_bounded, hA_limit⟩ :=
    exists_initialTimeContinuationStageOfOS_of_factorwise_uniformBound
      OS φ hφ_compact hφ_positive η hη hηsum hbounded
  refine ⟨A, hA_carrier, hA_bounded, hA_limit, ?_⟩
  intro τ hτ χ
  exact
    tendsto_nhds_unique
      (hA_limit (osiiPositiveRealTimeEmbed τ)
        (osiiPositiveRealTimeEmbed_mem_osiiNarrowTimeCarrier
          η hη τ hτ) χ)
      (initialSpatialFactorPacketDistributionOfOS_realEdge_tendsto
        OS φ hφ_compact hφ_positive η hη hηsum τ hτ χ)

end OSIIChapterV
end OSReconstruction
