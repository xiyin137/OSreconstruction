/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVVacuumTailTargetHubChart
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVRootedTargetHubGeometry
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageExtensionConvexCoreAtlas
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVFirstBridgeSectorChart
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVVacuumTailBoundPreservation
















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData
namespace PositiveHeadUniversalAnchoredAtlasData

variable {d q : ℕ} [NeZero d]
variable
  {I : Section43ProductTimeApproximateIdentity (q + 1)}
  {anchor : Fin (q + 1) → ℝ}
  {L : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {A : AnchoredPacketTimeShellFamilyData (d := d) I anchor}
  {stage : OSIITimeContinuationStage d (q + 1)}

/-- A convex absolute vacuum-tail branch agrees with a predecessor carrying a
pointed convex atlas.  Only the seed chart must contain the packet anchor;
the distinguished hub propagates the equality to every other chart. -/
theorem vacuumTailAbsoluteBranch_agreesOnPredecessor_of_pointedAtlas
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (M : StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
      A OS stage)
    {hub : Fin (q + 1) → ℝ}
    {ι : Type*}
    (atlas :
      GeneratorStagePointedConvexAtlas
        stage (osiiPositiveRealTimeEmbed hub) ι)
    (seedChart : ι)
    (anchor_mem_seed :
      osiiPositiveRealTimeEmbed anchor ∈ atlas.domain seedChart)
    (domain : Set (OSIITimeGapSpace (q + 1)))
    (domain_open : IsOpen domain)
    (domain_convex : Convex ℝ domain)
    (domain_subset :
      domain ⊆ D.vacuumTailAbsoluteStage.carrier)
    (anchor_mem_domain :
      osiiPositiveRealTimeEmbed anchor ∈ domain)
    (hub_mem_domain :
      osiiPositiveRealTimeEmbed hub ∈ domain) :
    Set.EqOn
      D.vacuumTailAbsoluteStage.distribution
      stage.distribution
      (domain ∩ stage.carrier) := by
  let seedDomain : Set (OSIITimeGapSpace (q + 1)) :=
    domain ∩ atlas.domain seedChart
  have hseedDomain_open : IsOpen seedDomain :=
    domain_open.inter (atlas.domain_open seedChart)
  have hseedDomain_connected : IsConnected seedDomain := by
    apply
      (domain_convex.inter
        (atlas.domain_convex seedChart)).isConnected
    exact
      ⟨osiiPositiveRealTimeEmbed anchor,
        anchor_mem_domain, anchor_mem_seed⟩
  let realSeed : Set (Fin (q + 1) → ℝ) :=
    (D.vacuumTailPredecessorRealRegion M ∩
      osiiPositiveRealTimeEmbed ⁻¹' domain) ∩
        osiiPositiveRealTimeEmbed ⁻¹' atlas.domain seedChart
  have hrealSeed_open : IsOpen realSeed :=
    ((D.vacuumTailPredecessorRealRegion_open M).inter
      (domain_open.preimage
        continuous_osiiPositiveRealTimeEmbed)).inter
      ((atlas.domain_open seedChart).preimage
        continuous_osiiPositiveRealTimeEmbed)
  have hrealSeed_nonempty : realSeed.Nonempty :=
    ⟨anchor,
      ⟨D.anchor_mem_vacuumTailPredecessorRealRegion M,
        anchor_mem_domain⟩,
      anchor_mem_seed⟩
  have hseed_eq :
      Set.EqOn
        D.vacuumTailAbsoluteStage.distribution
        stage.distribution
        seedDomain := by
    intro w hw
    apply ContinuousLinearMap.ext
    intro χ
    let F : OSIITimeGapSpace (q + 1) → ℂ :=
      fun v =>
        D.vacuumTailAbsoluteStage.distribution v χ -
          stage.distribution v χ
    have hF : DifferentiableOn ℂ F seedDomain :=
      ((D.vacuumTailAbsoluteStage.weaklyHolomorphic χ).mono
        (Set.inter_subset_left.trans domain_subset)).sub
        ((stage.weaklyHolomorphic χ).mono
          (Set.inter_subset_right.trans
            (atlas.domain_subset_carrier seedChart)))
    have hrealSeed_sub :
        ∀ τ ∈ realSeed,
          SCV.realToComplex τ ∈ seedDomain := by
      intro τ hτ
      simpa [seedDomain, SCV.realToComplex,
        osiiPositiveRealTimeEmbed] using
        (show
          osiiPositiveRealTimeEmbed τ ∈
            domain ∩ atlas.domain seedChart from
          ⟨hτ.1.2, hτ.2⟩)
    have hF_zero :
        ∀ τ ∈ realSeed,
          F (SCV.realToComplex τ) = 0 := by
      intro τ hτ
      have hnew :=
        D.vacuumTailAbsoluteStage_hasPositiveRealEdge
          M.currentData τ hτ.1.1.2
      have hold :=
        (D.predecessorEdgeMatchedToVacuumTail M).stageEdge
          τ hτ.1.1
      simp only [F]
      rw [show SCV.realToComplex τ =
          osiiPositiveRealTimeEmbed τ by rfl,
        hnew.2, hold.2]
      change
        D.vacuumTailAbsoluteOrbit τ χ -
            D.vacuumTailAbsoluteOrbit τ χ = 0
      exact sub_self _
    exact
      sub_eq_zero.mp
        (SCV.identity_theorem_totally_real
          hseedDomain_open hseedDomain_connected hF
          hrealSeed_open hrealSeed_nonempty
          hrealSeed_sub hF_zero w hw)
  intro w hw
  obtain ⟨chart, hchart⟩ :=
    Set.mem_iUnion.mp (atlas.carrier_subset_iUnion hw.2)
  let chartDomain : Set (OSIITimeGapSpace (q + 1)) :=
    domain ∩ atlas.domain chart
  have hchartDomain_open : IsOpen chartDomain :=
    domain_open.inter (atlas.domain_open chart)
  have hchartDomain_connected : IsConnected chartDomain := by
    apply
      (domain_convex.inter
        (atlas.domain_convex chart)).isConnected
    exact
      ⟨osiiPositiveRealTimeEmbed hub,
        hub_mem_domain, atlas.point_mem chart⟩
  let overlap : Set (OSIITimeGapSpace (q + 1)) :=
    chartDomain ∩ atlas.domain seedChart
  have hoverlap_open : IsOpen overlap :=
    hchartDomain_open.inter (atlas.domain_open seedChart)
  have hoverlap_nonempty : overlap.Nonempty :=
    ⟨osiiPositiveRealTimeEmbed hub,
      ⟨hub_mem_domain, atlas.point_mem chart⟩,
      atlas.point_mem seedChart⟩
  have hoverlap_eq :
      Set.EqOn
        D.vacuumTailAbsoluteStage.distribution
        stage.distribution
        overlap := by
    intro v hv
    exact hseed_eq ⟨hv.1.1, hv.2⟩
  exact
    (weaklyHolomorphic_eqOn_of_eqOn_open
      hchartDomain_open hchartDomain_connected
      hoverlap_open hoverlap_nonempty Set.inter_subset_left
      (fun χ =>
        (D.vacuumTailAbsoluteStage.weaklyHolomorphic χ).mono
          (Set.inter_subset_left.trans domain_subset))
      (fun χ =>
        (stage.weaklyHolomorphic χ).mono
          (Set.inter_subset_right.trans
            (atlas.domain_subset_carrier chart)))
      hoverlap_eq) ⟨hw.1, hchart⟩

/-- Package one pointed target-and-hub vacuum-tail chart as the sole nonempty
first-bridge generator branch. -/
noncomputable def vacuumTailTargetHubPointedStageExtensionData
    (D : PositiveHeadUniversalAnchoredAtlasData L OS A)
    (M : StageMatchedCommonTranslatedPositiveHeadSpatialSourceCurrentData
      A OS stage)
    {hub : Fin (q + 1) → ℝ}
    {ι : Type*}
    (atlas :
      GeneratorStagePointedConvexAtlas
        stage (osiiPositiveRealTimeEmbed hub) ι)
    (seedChart : ι)
    (anchor_mem_seed :
      osiiPositiveRealTimeEmbed anchor ∈ atlas.domain seedChart)
    (domain : Set (OSIITimeGapSpace (q + 1)))
    (domain_open : IsOpen domain)
    (domain_convex : Convex ℝ domain)
    (domain_subset :
      domain ⊆ D.vacuumTailAbsoluteStage.carrier)
    (anchor_mem_domain :
      osiiPositiveRealTimeEmbed anchor ∈ domain)
    (hub_mem_domain :
      osiiPositiveRealTimeEmbed hub ∈ domain) :
    GeneratorStageExtensionData stage := by
  have hagrees :=
    D.vacuumTailAbsoluteBranch_agreesOnPredecessor_of_pointedAtlas
      M atlas seedChart anchor_mem_seed
      domain domain_open domain_convex domain_subset
      anchor_mem_domain hub_mem_domain
  exact
    { domain := firstBridgeOnlyDomain q domain
      domain_open := by
        intro i
        by_cases hi : i = firstBridgeGeneratorIndex q
        · subst i
          simpa only [firstBridgeOnlyDomain_first] using domain_open
        · rw [firstBridgeOnlyDomain_eq_empty q domain i hi]
          exact isOpen_empty
      distribution :=
        fun _ => D.vacuumTailAbsoluteStage.distribution
      weaklyHolomorphic := by
        intro i χ
        by_cases hi : i = firstBridgeGeneratorIndex q
        · subst i
          simpa only [firstBridgeOnlyDomain_first] using
            (D.vacuumTailAbsoluteStage.weaklyHolomorphic χ).mono
              domain_subset
        · rw [firstBridgeOnlyDomain_eq_empty q domain i hi]
          exact differentiableOn_empty
      compatible := by
        intro _i _j _w _hw
        rfl
      agreesOnOld := by
        intro i w hw
        by_cases hi : i = firstBridgeGeneratorIndex q
        · subst i
          apply hagrees
          simpa only [firstBridgeOnlyDomain_first] using hw
        · have hwempty :
              w ∈ (∅ : Set (OSIITimeGapSpace (q + 1))) := by
            simpa [firstBridgeOnlyDomain_eq_empty
              q domain i hi] using hw.1
          exact hwempty.elim }

end PositiveHeadUniversalAnchoredAtlasData

variable {d q : ℕ} [NeZero d]
variable
  {OS : OsterwalderSchraderAxioms d}
  {L : SimultaneousTimeContinuationStageLevel d}
  {ι : Type*}

/-- One exact mixed-tail target inserted into a scalar predecessor through a
fixed pointed convex atlas. -/
structure VacuumTailTargetHubPointedDirectExtensionData
    (L : SimultaneousTimeContinuationStageLevel d)
    (OS : OsterwalderSchraderAxioms d)
    (hub : Fin (q + 1) → ℝ)
    (z : OSIITimeGapSpace (q + 1))
    (_atlas :
      GeneratorStagePointedConvexAtlas
        (L.stage (q + 1))
        (osiiPositiveRealTimeEmbed hub) ι) where
  extension :
    GeneratorStageExtensionData (L.stage (q + 1))
  carrier : Set (OSIITimeGapSpace (q + 1))
  carrier_open : IsOpen carrier
  carrier_convex : Convex ℝ carrier
  carrier_subset_extensionDomain :
    carrier ⊆ extension.domain (firstBridgeGeneratorIndex q)
  hub_mem_carrier : osiiPositiveRealTimeEmbed hub ∈ carrier
  target_mem_carrier : z ∈ carrier
  approximation :
    Nat -> OSIITimeGapSpace (q + 1) ->
      OSIISpatialDistribution d (q + 1)
  approximation_tendsto : forall w, w ∈ carrier -> forall chi,
    Filter.Tendsto (fun scale => approximation scale w chi) Filter.atTop
      (nhds (extension.distribution
        (firstBridgeGeneratorIndex q) w chi))
  diagonalCenterDomain : Set (Fin (q + 1) -> Complex)
  diagonalCenter : OSIITimeGapSpace (q + 1) ->
    Fin (q + 1) -> Complex
  diagonalCenter_mem : forall w, w ∈ carrier ->
    diagonalCenter w ∈ diagonalCenterDomain
  diagonalScalar : Nat ->
    SchwartzMap (Section43SpatialSpace d (q + 1)) Complex ->
      (Fin ((q + 1) + (q + 1)) -> Complex) -> Complex
  gramSourceIndex : Type
  gramScalar : gramSourceIndex -> gramSourceIndex ->
    (Fin ((q + 1) + (q + 1)) -> Complex) -> Complex
  gramAnchorField : gramSourceIndex -> OSHilbertSpace OS
  gramSeed : SourceIndexedReflectedGramHilbertFieldData
    (OSHilbertSpace OS) gramSourceIndex (q + 1) gramScalar
  diagonalSource : Nat ->
    SchwartzMap (Section43SpatialSpace d (q + 1)) Complex ->
      gramSourceIndex
  diagonalScalar_eq_gram : forall scale test,
    diagonalScalar scale test =
      gramScalar (diagonalSource scale test) (diagonalSource scale test)
  diagonalCenterDomain_eq_reachableAtlas :
    diagonalCenterDomain =
      SourceIndexedReachableAnchoredReflectedGramChart.coveredDomain
        (H := OSHilbertSpace OS) (iota := gramSourceIndex) (k := q)
        (scalar := gramScalar)
        (anchorPoint := (0 : Fin (q + 1) -> Complex))
        (anchorField := gramAnchorField) (P := gramSeed)
  diagonalPoint : OSIITimeGapSpace (q + 1) ->
    Fin ((q + 1) + (q + 1)) -> Complex
  diagonalPoint_eq_reflectedCenter : forall w,
    diagonalPoint w = reflectedCauchyCenter (diagonalCenter w)
  norm_approximation_le_of_diagonal : forall
    (_lgc : OSLinearGrowthCondition d OS) scale w,
    w ∈ carrier -> forall test B,
    1 <= B ->
      ‖diagonalScalar scale test (diagonalPoint w)‖ <= B ->
      ‖approximation scale w test‖ <= B
  norm_approximation_le_sqrt_of_diagonal : forall
    (_lgc : OSLinearGrowthCondition d OS) scale w,
    w ∈ carrier -> forall test B,
      ‖diagonalScalar scale test (diagonalPoint w)‖ <= B ->
      ‖approximation scale w test‖ <= Real.sqrt B

namespace VacuumTailTargetHubPointedDirectExtensionData

variable
  {hub : Fin (q + 1) → ℝ}
  {z : OSIITimeGapSpace (q + 1)}
  {atlas :
    GeneratorStagePointedConvexAtlas
      (L.stage (q + 1))
      (osiiPositiveRealTimeEmbed hub) ι}

end VacuumTailTargetHubPointedDirectExtensionData

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
