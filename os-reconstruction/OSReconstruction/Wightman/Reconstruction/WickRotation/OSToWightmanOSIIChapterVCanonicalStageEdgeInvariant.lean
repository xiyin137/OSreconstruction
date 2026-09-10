/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVCanonicalStageOrbitBridge
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVGeneratorStageExtension
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVZeroGapStage






















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

variable {d k : ℕ} [NeZero d]

/-- Pure finite-dimensional cutoff data around a compact positive-time
carrier.  This separates the automatic smooth cutoff construction from the
genuine analytic task of producing a holomorphic stage edge. -/
structure CanonicalReducedCompactCutoffData
    (compactCarrier : Set (Fin k → ℝ)) where
  cutoff : SchwartzMap (Fin k → ℝ) ℂ
  cutoff_support :
    tsupport (cutoff : (Fin k → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion k
  cutoff_compact :
    HasCompactSupport (cutoff : (Fin k → ℝ) → ℂ)
  realRegion : Set (Fin k → ℝ)
  realRegion_open : IsOpen realRegion
  compactCarrier_subset : compactCarrier ⊆ realRegion
  cutoff_one_on :
    ∀ τ, τ ∈ realRegion → cutoff τ = 1

namespace CanonicalReducedCompactCutoffData

/-- Every compact subset of the strict-positive region has a compactly
supported positive-time cutoff equal to one on an open neighborhood. -/
theorem nonempty
    (compactCarrier : Set (Fin k → ℝ))
    (hcompact : IsCompact compactCarrier)
    (hpositive :
      compactCarrier ⊆ section43TimeStrictPositiveRegion k) :
    Nonempty (CanonicalReducedCompactCutoffData compactCarrier) := by
  obtain ⟨r, hr_pos, hr_sub⟩ :=
    hcompact.exists_cthickening_subset_open
      (isOpen_section43TimeStrictPositiveRegion k) hpositive
  let r₂ : ℝ := r / 2
  have hr₂_pos : 0 < r₂ := half_pos hr_pos
  have hr₂_le : r₂ ≤ r := by
    dsimp [r₂]
    linarith
  let compactNeighborhood : Set (Fin k → ℝ) :=
    Metric.cthickening r₂ compactCarrier
  have hcompactNeighborhood : IsCompact compactNeighborhood :=
    hcompact.cthickening
  have hcompactNeighborhood_positive :
      compactNeighborhood ⊆ section43TimeStrictPositiveRegion k :=
    (Metric.cthickening_mono hr₂_le compactCarrier).trans hr_sub
  obtain ⟨cutoff, hcutoff_one, hcutoff_support, hcutoff_compact⟩ :=
    exists_compact_schwartz_cutoff_eq_one_on_compact_subset_open
      hcompactNeighborhood
      (isOpen_section43TimeStrictPositiveRegion k)
      hcompactNeighborhood_positive
  let realRegion : Set (Fin k → ℝ) :=
    Metric.thickening r₂ compactCarrier
  refine ⟨{
    cutoff := cutoff
    cutoff_support := hcutoff_support
    cutoff_compact := hcutoff_compact
    realRegion := realRegion
    realRegion_open := Metric.isOpen_thickening
    compactCarrier_subset :=
      Metric.self_subset_thickening hr₂_pos compactCarrier
    cutoff_one_on := ?_ }⟩
  intro τ hτ
  exact hcutoff_one τ
    (Metric.thickening_subset_cthickening_of_le
      (le_refl r₂) compactCarrier hτ)

variable {OS : OsterwalderSchraderAxioms d}
  {compactCarrier : Set (Fin k → ℝ)}

/-- The selected canonical extension agrees with the uncut OS Schwinger
functional on every full source carried over the open region where the
auxiliary cutoff is one. -/
theorem canonical_apply_diffVarReduction_eq_of_reducedTimeSupport_realRegion
    (C : CanonicalReducedCompactCutoffData compactCarrier)
    (f : SchwartzNPoint d (k + 1))
    (hf : VanishesToInfiniteOrderOnCoincidence f)
    (hregion :
      ∀ x ∈ tsupport (f : NPointDomain d (k + 1) → ℂ),
        reducedTimeProjectionCLM d k x ∈ C.realRegion) :
    canonicalReducedTimeCutoffSchwingerCLM
        OS C.cutoff C.cutoff_support
        (diffVarReduction d k f) =
      OS.S (k + 1) ⟨f, hf⟩ := by
  apply
    canonicalReducedTimeCutoffSchwingerCLM_apply_diffVarReduction_eq_of_cutoff
  exact
    reducedTimeCutoff_smul_eq_of_one_on_tsupport C.cutoff f
      (fun x hx => by
        rw [reducedTimeCutoffWeight]
        exact C.cutoff_one_on _ (hregion x hx))

/-- The selected canonical extension agrees with the uncut OS Schwinger
functional on every full source carried over the original compact carrier.

Thus the cutoff datum contributes no additional local distributional
obligation: only construction of its holomorphic stage edge remains. -/
theorem canonical_apply_diffVarReduction_eq_of_reducedTimeSupport
    (C : CanonicalReducedCompactCutoffData compactCarrier)
    (f : SchwartzNPoint d (k + 1))
    (hf : VanishesToInfiniteOrderOnCoincidence f)
    (hcarrier :
      ∀ x ∈ tsupport (f : NPointDomain d (k + 1) → ℂ),
        reducedTimeProjectionCLM d k x ∈ compactCarrier) :
    canonicalReducedTimeCutoffSchwingerCLM
        OS C.cutoff C.cutoff_support
        (diffVarReduction d k f) =
      OS.S (k + 1) ⟨f, hf⟩ := by
  apply
    C.canonical_apply_diffVarReduction_eq_of_reducedTimeSupport_realRegion
      f hf
  intro x hx
  exact C.compactCarrier_subset (hcarrier x hx)

end CanonicalReducedCompactCutoffData

/-- One local canonical reduced edge around a compact positive-time carrier.

The selected auxiliary cutoff is compactly supported in the strict-positive
region and equals one throughout `realRegion`.  Consequently its canonical
reduced distribution is the uncut local Schwinger edge on that region. -/
structure CanonicalReducedCompactStageEdgeData
    (OS : OsterwalderSchraderAxioms d)
    (stage : OSIITimeContinuationStage d k)
    (compactCarrier : Set (Fin k → ℝ)) where
  cutoff : SchwartzMap (Fin k → ℝ) ℂ
  cutoff_support :
    tsupport (cutoff : (Fin k → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion k
  cutoff_compact :
    HasCompactSupport (cutoff : (Fin k → ℝ) → ℂ)
  realRegion : Set (Fin k → ℝ)
  realRegion_open : IsOpen realRegion
  compactCarrier_subset : compactCarrier ⊆ realRegion
  cutoff_one_on :
    ∀ τ, τ ∈ realRegion → cutoff τ = 1
  edge :
    stage.PositiveRealEdgeData
      (orderedTransportDistribution
        (canonicalReducedTimeCutoffSchwingerCLM
          OS cutoff cutoff_support))
      realRegion

/-- The stage has a local canonical reduced edge around every compact subset
of the strict-positive reduced-time region. -/
def HasCanonicalReducedCompactStageEdges
    (OS : OsterwalderSchraderAxioms d)
    (stage : OSIITimeContinuationStage d k) : Prop :=
  ∀ compactCarrier : Set (Fin k → ℝ),
    IsCompact compactCarrier →
      compactCarrier ⊆ section43TimeStrictPositiveRegion k →
        Nonempty
          (CanonicalReducedCompactStageEdgeData
            OS stage compactCarrier)

/-- Every strict-positive real point belongs to a stage carrying canonical
compact edges.  Apply the invariant to the singleton carrier and read
membership from the resulting positive-real stage edge. -/
theorem HasCanonicalReducedCompactStageEdges.positiveReal_mem_carrier
    {OS : OsterwalderSchraderAxioms d}
    {stage : OSIITimeContinuationStage d k}
    (H : HasCanonicalReducedCompactStageEdges OS stage)
    (τ : Fin k → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion k) :
    osiiPositiveRealTimeEmbed τ ∈ stage.carrier := by
  obtain ⟨D⟩ :=
    H {τ} isCompact_singleton
      (by
        intro σ hσ
        simpa only [Set.mem_singleton_iff] using hσ ▸ hτ)
  exact
    (D.edge.stageEdge τ
      (D.compactCarrier_subset (Set.mem_singleton τ))).1

namespace CanonicalReducedCompactStageEdgeData

variable
  {OS : OsterwalderSchraderAxioms d}
  {stage : OSIITimeContinuationStage d k}
  {compactCarrier : Set (Fin k → ℝ)}

/-- The real region of a canonical compact edge remains in strict positive
time. This follows from the cutoff being one there and supported in the
strict-positive region. -/
theorem realRegion_subset_strictPositive
    (D : CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier) :
    D.realRegion ⊆ section43TimeStrictPositiveRegion k := by
  intro τ hτ
  have hnonzero : D.cutoff τ ≠ 0 := by
    rw [D.cutoff_one_on τ hτ]
    exact one_ne_zero
  exact D.cutoff_support
    (subset_tsupport (D.cutoff : (Fin k → ℝ) → ℂ) hnonzero)

/-- Forget the analytic edge and retain the automatically constructible
finite-dimensional cutoff geometry. -/
noncomputable def toCutoffData
    (D : CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier) :
    CanonicalReducedCompactCutoffData compactCarrier where
  cutoff := D.cutoff
  cutoff_support := D.cutoff_support
  cutoff_compact := D.cutoff_compact
  realRegion := D.realRegion
  realRegion_open := D.realRegion_open
  compactCarrier_subset := D.compactCarrier_subset
  cutoff_one_on := D.cutoff_one_on

/-- If another cutoff is one at an absolute source, then its reduced-time
point lies in its topological support.  A local canonical edge whose compact
carrier contains that support therefore has its own auxiliary cutoff equal to
one at the same source. -/
theorem reducedTimeCutoffWeight_eq_one_of_auxiliary
    (D : CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier)
    (η : SchwartzMap (Fin k → ℝ) ℂ)
    (hη :
      tsupport (η : (Fin k → ℝ) → ℂ) ⊆ compactCarrier)
    (x : NPointDomain d (k + 1))
    (hx : reducedTimeCutoffWeight (d := d) η x = 1) :
    reducedTimeCutoffWeight (d := d) D.cutoff x = 1 := by
  let τ : Fin k → ℝ :=
    section43QTime (d := d) (n := k)
      (BHW.reducedDiffMapReal (k + 1) d x)
  have hητ : η τ = 1 := by
    simpa [reducedTimeCutoffWeight, τ] using hx
  have hτ_support :
      τ ∈ tsupport (η : (Fin k → ℝ) → ℂ) := by
    apply subset_tsupport
    simpa [Function.mem_support, hητ]
  have hτ_region : τ ∈ D.realRegion :=
    D.compactCarrier_subset (hη hτ_support)
  simpa [reducedTimeCutoffWeight, τ] using
    D.cutoff_one_on τ hτ_region

/-- A canonical cutoff edge survives gluing in new generator branches. -/
noncomputable def ofGeneratorStageExtension
    (D : CanonicalReducedCompactStageEdgeData
      OS stage compactCarrier)
    (C : GeneratorStageExtensionData stage) :
    CanonicalReducedCompactStageEdgeData
      OS C.toTimeContinuationStage compactCarrier where
  cutoff := D.cutoff
  cutoff_support := D.cutoff_support
  cutoff_compact := D.cutoff_compact
  realRegion := D.realRegion
  realRegion_open := D.realRegion_open
  compactCarrier_subset := D.compactCarrier_subset
  cutoff_one_on := D.cutoff_one_on
  edge := C.toTimeContinuationStagePositiveRealEdgeData D.edge

end CanonicalReducedCompactStageEdgeData

/-- The zero-gap simultaneous stage is completely canonical.  No analytic
continuation or compact-carrier argument remains at this arity. -/
theorem canonicalZeroGapTimeContinuationStage_hasCanonicalReducedCompactStageEdges
    (OS : OsterwalderSchraderAxioms d) :
    HasCanonicalReducedCompactStageEdges OS
      (canonicalZeroGapTimeContinuationStage OS) := by
  intro compactCarrier _hcompact _hpositive
  refine ⟨{
    cutoff := zeroGapUnitTimeSchwartz
    cutoff_support := zeroGapUnitTimeSchwartz_support
    cutoff_compact := zeroGapUnitTimeSchwartz_compact
    realRegion := Set.univ
    realRegion_open := isOpen_univ
    compactCarrier_subset := Set.subset_univ compactCarrier
    cutoff_one_on := fun τ _hτ => zeroGapUnitTimeSchwartz_apply τ
    edge := ?_ }⟩
  exact canonicalZeroGapPositiveRealEdgeData OS

namespace GeneratorStageExtensionData

variable {stage : OSIITimeContinuationStage d k}

/-- Generator gluing preserves all local canonical reduced edges carried by
the predecessor stage. -/
theorem preservesCanonicalReducedCompactStageEdges
    (C : GeneratorStageExtensionData stage)
    (OS : OsterwalderSchraderAxioms d)
    (H : HasCanonicalReducedCompactStageEdges OS stage) :
    HasCanonicalReducedCompactStageEdges
      OS C.toTimeContinuationStage := by
  intro compactCarrier hcompact hpositive
  obtain ⟨D⟩ := H compactCarrier hcompact hpositive
  exact ⟨D.ofGeneratorStageExtension C⟩

end GeneratorStageExtensionData

namespace GeneratorStageEnvelopeExtension

variable
  {stage : OSIITimeContinuationStage d k}
  {C : GeneratorStageExtensionData stage}
  {carrier : Set (OSIITimeGapSpace k)}

end GeneratorStageEnvelopeExtension

end OSIIChapterV
end OSReconstruction
