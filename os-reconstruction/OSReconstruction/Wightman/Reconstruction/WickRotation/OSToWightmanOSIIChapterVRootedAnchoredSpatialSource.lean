import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketRootedBridgeBlocks
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVUniformCompactTimeAnchoredSeed

/-!
# Rooted spatial sources in the universal anchored source space

The global anchored Hilbert atlas is indexed by all positive-time sources
whose difference-time support lies in one fixed compact carrier.  The physical
rooted Chapter V blocks already have such carriers, uniformly in packet scale
and in the full spatial Schwartz test.

This file records the direct adapter: choose the common rooted carriers and
codomain-restrict each fixed-scale spatial source map into the corresponding
universal fixed-carrier source space.  No comparison with the fixed-head
native packet family is used.
-/

noncomputable section

open Set
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}

/-- The compact strict-positive carrier selected by the existing uniform
support theorem for the rooted left block. -/
noncomputable def rootedLeftBlockSpatialSourceCarrierRaw
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k) :
    Set (Fin ((i.n - 1) + 1) → ℝ) :=
  Classical.choose
    (A.rootedLeftBlockSpatialSource_uniformCompactSupport_all_scales R i)

theorem rootedLeftBlockSpatialSourceCarrierRaw_compact
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k) :
    IsCompact (A.rootedLeftBlockSpatialSourceCarrierRaw R i) :=
  (Classical.choose_spec
    (A.rootedLeftBlockSpatialSource_uniformCompactSupport_all_scales R i)).1

theorem rootedLeftBlockSpatialSourceCarrierRaw_positive
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k) :
    A.rootedLeftBlockSpatialSourceCarrierRaw R i ⊆
      section43TimeStrictPositiveRegion ((i.n - 1) + 1) :=
  (Classical.choose_spec
    (A.rootedLeftBlockSpatialSource_uniformCompactSupport_all_scales R i)).2.1

/-- The rooted left carrier refined to remember the coordinatewise anchor
lower bound already satisfied by every translated time source. -/
noncomputable def rootedLeftBlockSpatialSourceCarrier
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k) :
    Set (Fin ((i.n - 1) + 1) → ℝ) :=
  A.rootedLeftBlockSpatialSourceCarrierRaw R i ∩
    {τ | ∀ j, A.rootedLeftBlockAnchor i j ≤ τ j}

theorem rootedLeftBlockSpatialSourceCarrier_compact
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k) :
    IsCompact (A.rootedLeftBlockSpatialSourceCarrier R i) := by
  apply (A.rootedLeftBlockSpatialSourceCarrierRaw_compact R i).inter_right
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun j : Fin ((i.n - 1) + 1) =>
    isClosed_le
      (continuous_const :
        Continuous fun _ : Fin ((i.n - 1) + 1) → ℝ =>
          A.rootedLeftBlockAnchor i j)
      (continuous_apply j)

theorem rootedLeftBlockSpatialSourceCarrier_positive
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k) :
    A.rootedLeftBlockSpatialSourceCarrier R i ⊆
      section43TimeStrictPositiveRegion ((i.n - 1) + 1) := by
  intro τ hτ
  exact A.rootedLeftBlockSpatialSourceCarrierRaw_positive R i hτ.1

theorem rootedLeftBlockSpatialSourceCarrier_lower
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k) :
    ∀ τ ∈ A.rootedLeftBlockSpatialSourceCarrier R i,
      ∀ j, A.rootedLeftBlockAnchor i j ≤ τ j := by
  intro τ hτ
  exact hτ.2

theorem rootedLeftBlockSpatialSource_mem_carrier
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (scale : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((i.n - 1) + 1)) ℂ) :
    A.rootedLeftBlockSpatialSource R i scale χ ∈
      uniformCompactTimeSourceSubmodule
        d ((i.n - 1) + 1)
        (A.rootedLeftBlockSpatialSourceCarrier R i) := by
  intro x hx
  constructor
  · exact
      (Classical.choose_spec
        (A.rootedLeftBlockSpatialSource_uniformCompactSupport_all_scales R i)
        ).2.2 (scale, χ) x hx
  · have htime :
        section43QTime (d := d) (n := ((i.n - 1) + 1))
            (section43DiffCoordRealCLE d ((i.n - 1) + 1) x) ∈
          tsupport
            (((A.rootedLeftBlockApproximateIdentity R i).translatedSource
              (A.rootedLeftBlockAnchor i)
              (A.rootedLeftBlockAnchor_positive i) scale).f :
              (Fin ((i.n - 1) + 1) → ℝ) → ℂ) := by
      exact
        osiiA0_orderedPullback_tsupport_subset_timeSet
          (d := d) χ
          ((A.rootedLeftBlockApproximateIdentity R i).translatedSource
            (A.rootedLeftBlockAnchor i)
            (A.rootedLeftBlockAnchor_positive i) scale).f
          (tsupport
            (((A.rootedLeftBlockApproximateIdentity R i).translatedSource
              (A.rootedLeftBlockAnchor i)
              (A.rootedLeftBlockAnchor_positive i) scale).f :
              (Fin ((i.n - 1) + 1) → ℝ) → ℂ))
          (Subset.refl _)
          (by
            simpa [rootedLeftBlockSpatialSource,
              translatedPositiveTimeSpatialSource_coe] using hx)
    exact
      (A.rootedLeftBlockApproximateIdentity R i
        ).translatedSource_tsupport_anchor_le
          (A.rootedLeftBlockAnchor i)
          (A.rootedLeftBlockAnchor_positive i) scale _ htime

/-- At each packet scale, the rooted left source depends continuously and
linearly on the complete spatial Schwartz test and lands in one universal
fixed-carrier source space. -/
noncomputable def rootedLeftBlockAnchoredSourceCLM
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (scale : ℕ) :
    SchwartzMap
        (Section43SpatialSpace d ((i.n - 1) + 1)) ℂ →L[ℂ]
      UniformCompactTimeSource
        d ((i.n - 1) + 1)
        (A.rootedLeftBlockSpatialSourceCarrier R i) :=
  (section43PositiveTimeSpatialSourceCLM
      d ((i.n - 1) + 1)
      ((A.rootedLeftBlockApproximateIdentity R i).translatedSource
        (A.rootedLeftBlockAnchor i)
        (A.rootedLeftBlockAnchor_positive i) scale)).codRestrict
    (uniformCompactTimeSourceSubmodule
      d ((i.n - 1) + 1)
      (A.rootedLeftBlockSpatialSourceCarrier R i))
    (A.rootedLeftBlockSpatialSource_mem_carrier R i scale)

@[simp]
theorem rootedLeftBlockAnchoredSourceCLM_source
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (scale : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((i.n - 1) + 1)) ℂ) :
    UniformCompactTimeSource.source
        (A.rootedLeftBlockAnchoredSourceCLM R i scale χ) =
      A.rootedLeftBlockSpatialSource R i scale χ :=
  rfl

@[simp]
theorem rootedLeftBlockAnchoredSourceCLM_source_translated
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (scale : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((i.n - 1) + 1)) ℂ) :
    UniformCompactTimeSource.source
        (A.rootedLeftBlockAnchoredSourceCLM R i scale χ) =
      (A.rootedLeftBlockApproximateIdentity R i
        ).translatedPositiveTimeSpatialSource
          (A.rootedLeftBlockAnchor i)
          (A.rootedLeftBlockAnchor_positive i) χ scale :=
  rfl

/-- The compact strict-positive carrier selected by the existing uniform
support theorem for the rooted right block. -/
noncomputable def rootedRightBlockSpatialSourceCarrierRaw
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k) :
    Set (Fin ((i.m - 1) + 1) → ℝ) :=
  Classical.choose
    (A.rootedRightBlockSpatialSource_uniformCompactSupport_all_scales R i)

theorem rootedRightBlockSpatialSourceCarrierRaw_compact
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k) :
    IsCompact (A.rootedRightBlockSpatialSourceCarrierRaw R i) :=
  (Classical.choose_spec
    (A.rootedRightBlockSpatialSource_uniformCompactSupport_all_scales R i)).1

theorem rootedRightBlockSpatialSourceCarrierRaw_positive
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k) :
    A.rootedRightBlockSpatialSourceCarrierRaw R i ⊆
      section43TimeStrictPositiveRegion ((i.m - 1) + 1) :=
  (Classical.choose_spec
    (A.rootedRightBlockSpatialSource_uniformCompactSupport_all_scales R i)).2.1

/-- The rooted right carrier refined to remember the coordinatewise anchor
lower bound already satisfied by every translated time source. -/
noncomputable def rootedRightBlockSpatialSourceCarrier
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k) :
    Set (Fin ((i.m - 1) + 1) → ℝ) :=
  A.rootedRightBlockSpatialSourceCarrierRaw R i ∩
    {τ | ∀ j, A.rootedRightBlockAnchor i j ≤ τ j}

theorem rootedRightBlockSpatialSourceCarrier_compact
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k) :
    IsCompact (A.rootedRightBlockSpatialSourceCarrier R i) := by
  apply (A.rootedRightBlockSpatialSourceCarrierRaw_compact R i).inter_right
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun j : Fin ((i.m - 1) + 1) =>
    isClosed_le
      (continuous_const :
        Continuous fun _ : Fin ((i.m - 1) + 1) → ℝ =>
          A.rootedRightBlockAnchor i j)
      (continuous_apply j)

theorem rootedRightBlockSpatialSourceCarrier_positive
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k) :
    A.rootedRightBlockSpatialSourceCarrier R i ⊆
      section43TimeStrictPositiveRegion ((i.m - 1) + 1) := by
  intro τ hτ
  exact A.rootedRightBlockSpatialSourceCarrierRaw_positive R i hτ.1

theorem rootedRightBlockSpatialSourceCarrier_lower
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k) :
    ∀ τ ∈ A.rootedRightBlockSpatialSourceCarrier R i,
      ∀ j, A.rootedRightBlockAnchor i j ≤ τ j := by
  intro τ hτ
  exact hτ.2

theorem rootedRightBlockSpatialSource_mem_carrier
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (scale : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((i.m - 1) + 1)) ℂ) :
    A.rootedRightBlockSpatialSource R i scale χ ∈
      uniformCompactTimeSourceSubmodule
        d ((i.m - 1) + 1)
        (A.rootedRightBlockSpatialSourceCarrier R i) := by
  intro x hx
  constructor
  · exact
      (Classical.choose_spec
        (A.rootedRightBlockSpatialSource_uniformCompactSupport_all_scales R i)
        ).2.2 (scale, χ) x hx
  · have htime :
        section43QTime (d := d) (n := ((i.m - 1) + 1))
            (section43DiffCoordRealCLE d ((i.m - 1) + 1) x) ∈
          tsupport
            (((A.rootedRightBlockApproximateIdentity R i).translatedSource
              (A.rootedRightBlockAnchor i)
              (A.rootedRightBlockAnchor_positive i) scale).f :
              (Fin ((i.m - 1) + 1) → ℝ) → ℂ) := by
      exact
        osiiA0_orderedPullback_tsupport_subset_timeSet
          (d := d) χ
          ((A.rootedRightBlockApproximateIdentity R i).translatedSource
            (A.rootedRightBlockAnchor i)
            (A.rootedRightBlockAnchor_positive i) scale).f
          (tsupport
            (((A.rootedRightBlockApproximateIdentity R i).translatedSource
              (A.rootedRightBlockAnchor i)
              (A.rootedRightBlockAnchor_positive i) scale).f :
              (Fin ((i.m - 1) + 1) → ℝ) → ℂ))
          (Subset.refl _)
          (by
            simpa [rootedRightBlockSpatialSource,
              translatedPositiveTimeSpatialSource_coe] using hx)
    exact
      (A.rootedRightBlockApproximateIdentity R i
        ).translatedSource_tsupport_anchor_le
          (A.rootedRightBlockAnchor i)
          (A.rootedRightBlockAnchor_positive i) scale _ htime

/-- Rooted right-block analogue of
`rootedLeftBlockAnchoredSourceCLM`. -/
noncomputable def rootedRightBlockAnchoredSourceCLM
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (scale : ℕ) :
    SchwartzMap
        (Section43SpatialSpace d ((i.m - 1) + 1)) ℂ →L[ℂ]
      UniformCompactTimeSource
        d ((i.m - 1) + 1)
        (A.rootedRightBlockSpatialSourceCarrier R i) :=
  (section43PositiveTimeSpatialSourceCLM
      d ((i.m - 1) + 1)
      ((A.rootedRightBlockApproximateIdentity R i).translatedSource
        (A.rootedRightBlockAnchor i)
        (A.rootedRightBlockAnchor_positive i) scale)).codRestrict
    (uniformCompactTimeSourceSubmodule
      d ((i.m - 1) + 1)
      (A.rootedRightBlockSpatialSourceCarrier R i))
    (A.rootedRightBlockSpatialSource_mem_carrier R i scale)

@[simp]
theorem rootedRightBlockAnchoredSourceCLM_source
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (scale : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((i.m - 1) + 1)) ℂ) :
    UniformCompactTimeSource.source
        (A.rootedRightBlockAnchoredSourceCLM R i scale χ) =
      A.rootedRightBlockSpatialSource R i scale χ :=
  rfl

@[simp]
theorem rootedRightBlockAnchoredSourceCLM_source_translated
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (scale : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((i.m - 1) + 1)) ℂ) :
    UniformCompactTimeSource.source
        (A.rootedRightBlockAnchoredSourceCLM R i scale χ) =
      (A.rootedRightBlockApproximateIdentity R i
        ).translatedPositiveTimeSpatialSource
          (A.rootedRightBlockAnchor i)
          (A.rootedRightBlockAnchor_positive i) χ scale :=
  rfl

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
