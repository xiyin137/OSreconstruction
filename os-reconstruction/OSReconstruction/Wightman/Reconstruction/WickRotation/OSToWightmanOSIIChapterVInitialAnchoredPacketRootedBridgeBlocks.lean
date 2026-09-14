/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketBridgeConvolution
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketBlockFamilies
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVDeltaHilbertLimit
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialReflectedA0Factorization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVReflectedMovingSliceBridge
import OSReconstruction.SCV.DistributionalRepresentationGluing
import Mathlib.Analysis.Complex.Tietze
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVTranslatedMixedDeltaProducer













noncomputable section

open Complex Filter MeasureTheory Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity

variable {d q : ℕ} [NeZero d]

namespace TripleConvolutionRootData

/-- Prepend one selected convolution root to a reindexed set of factors, with
all coordinates evaluated after the same finite scale shift. -/
noncomputable def prependRootReindex
    {k q : ℕ}
    {I : Section43ProductTimeApproximateIdentity k}
    (R : TripleConvolutionRootData I)
    (headIndex : Fin k)
    (tailIndex : Fin q → Fin k)
    (tailStart : ℕ) :
    Section43ProductTimeApproximateIdentity (q + 1) := by
  let scale : ℕ → ℕ := fun N => N + tailStart
  let factors :
      ℕ → Fin (q + 1) → Section43CompactPositiveTimeSource1D :=
    fun N =>
      Fin.cases
        (R.root (scale N) headIndex)
        (fun a => I.factors (scale N) (tailIndex a))
  let radius : ℕ → ℝ := fun N => I.radius (scale N)
  have hfactor_nonnegative :
      ∀ N i x, 0 ≤ ((factors N i).f x).re := by
    intro N i
    refine Fin.cases ?_ ?_ i
    · exact R.root_nonnegative (scale N) headIndex
    · intro a
      exact I.factor_nonnegative (scale N) (tailIndex a)
  have hfactor_real :
      ∀ N i x, ((factors N i).f x).im = 0 := by
    intro N i
    refine Fin.cases ?_ ?_ i
    · exact R.root_real (scale N) headIndex
    · intro a
      exact I.factor_real (scale N) (tailIndex a)
  have hfactor_integral_one :
      ∀ N i, ∫ x : ℝ, (factors N i).f x = 1 := by
    intro N i
    refine Fin.cases ?_ ?_ i
    · exact R.root_integral_one (scale N) headIndex
    · intro a
      exact I.factor_integral_one (scale N) (tailIndex a)
  have hfactor_support :
      ∀ N i,
        Function.support ((factors N i).f : ℝ → ℂ) ⊆
          Metric.ball 0 (radius N) := by
    intro N i
    refine Fin.cases ?_ ?_ i
    · exact R.root_support (scale N) headIndex
    · intro a
      exact I.factor_support (scale N) (tailIndex a)
  refine
    { factors := factors
      radius := radius
      factor_nonnegative := hfactor_nonnegative
      factor_real := hfactor_real
      factor_integral_one := hfactor_integral_one
      factor_support := hfactor_support
      nonnegative := ?_
      real := ?_
      integral_one := ?_
      support := ?_
      radius_tendsto := ?_ }
  · intro N x
    simp only [section43TimeProductSource, section43TimeProductTensor,
      SchwartzMap.productTensor_apply]
    have hprod :
        0 ≤ (∏ i : Fin (q + 1), (factors N i).f (x i)).re ∧
          (∏ i : Fin (q + 1), (factors N i).f (x i)).im = 0 := by
      classical
      refine Finset.induction_on
        (Finset.univ : Finset (Fin (q + 1))) ?_ ?_
      · simp
      · intro a s has ih
        rw [Finset.prod_insert has]
        constructor
        · rw [Complex.mul_re, hfactor_real N a (x a), ih.2]
          ring_nf
          exact mul_nonneg (hfactor_nonnegative N a (x a)) ih.1
        · rw [Complex.mul_im, hfactor_real N a (x a), ih.2]
          ring
    exact hprod.1
  · intro N x
    simp only [section43TimeProductSource, section43TimeProductTensor,
      SchwartzMap.productTensor_apply]
    classical
    refine Finset.induction_on
      (Finset.univ : Finset (Fin (q + 1))) ?_ ?_
    · simp
    · intro a s has ih
      rw [Finset.prod_insert has, Complex.mul_im,
        hfactor_real N a (x a), ih]
      ring
  · intro N
    have hraw :=
      section43TimeProductSource_integral_eq_product_raw
        (gs := factors N) (σ := fun _ : Fin (q + 1) => 0)
    calc
      (∫ x : Fin (q + 1) → ℝ,
          (section43TimeProductSource (factors N)).f x) =
        ∫ x : Fin (q + 1) → ℝ,
          Complex.exp
              (-(∑ i : Fin (q + 1),
                (x i : ℂ) * ((0 : ℝ) : ℂ))) *
            (section43TimeProductSource (factors N)).f x := by
              simp
      _ =
        ∏ i : Fin (q + 1),
          ∫ t : ℝ,
            Complex.exp
                (-(t : ℂ) *
                  (((fun _ : Fin (q + 1) => 0) i : ℝ) : ℂ)) *
              (factors N i).f t := hraw
      _ = ∏ _i : Fin (q + 1), (1 : ℂ) := by
        refine Finset.prod_congr rfl ?_
        intro i _hi
        simpa using hfactor_integral_one N i
      _ = 1 := by simp
  · intro N x hx
    rw [Metric.mem_ball, dist_zero_right,
      pi_norm_lt_iff (I.radius_pos (scale N))]
    intro i
    have hx_prod_ne :
        (∏ j : Fin (q + 1), (factors N j).f (x j)) ≠ 0 := by
      rw [Function.mem_support] at hx
      change
        SchwartzMap.productTensor
            (fun j : Fin (q + 1) => (factors N j).f) x ≠ 0 at hx
      rw [SchwartzMap.productTensor_apply] at hx
      exact hx
    have hxi_ne : (factors N i).f (x i) ≠ 0 := by
      intro hzero
      exact hx_prod_ne
        (Finset.prod_eq_zero (Finset.mem_univ i) hzero)
    have hxi_support :
        x i ∈ Function.support ((factors N i).f : ℝ → ℂ) := by
      simpa [Function.mem_support] using hxi_ne
    have hxi_ball := hfactor_support N i hxi_support
    simpa [radius, Metric.mem_ball, dist_zero_right] using hxi_ball
  · exact I.radius_tendsto.comp (tendsto_add_atTop_nat tailStart)

@[simp]
theorem prependRootReindex_factor_zero
    {k q : ℕ}
    {I : Section43ProductTimeApproximateIdentity k}
    (R : TripleConvolutionRootData I)
    (headIndex : Fin k)
    (tailIndex : Fin q → Fin k)
    (tailStart N : ℕ) :
    (R.prependRootReindex headIndex tailIndex tailStart).factors N 0 =
      R.root (N + tailStart) headIndex :=
  rfl

@[simp]
theorem prependRootReindex_factor_succ
    {k q : ℕ}
    {I : Section43ProductTimeApproximateIdentity k}
    (R : TripleConvolutionRootData I)
    (headIndex : Fin k)
    (tailIndex : Fin q → Fin k)
    (tailStart N : ℕ)
    (a : Fin q) :
    (R.prependRootReindex headIndex tailIndex tailStart).factors N a.succ =
      I.factors (N + tailStart) (tailIndex a) :=
  rfl

end TripleConvolutionRootData

namespace AnchoredPacketTimeShellFamilyData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}

/-- The rooted left block is one product approximate identity: the bridge
root followed by the left internal-gap factors. -/
noncomputable def rootedLeftBlockApproximateIdentity
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k) :
    Section43ProductTimeApproximateIdentity ((i.n - 1) + 1) :=
  R.prependRootReindex
    i.bridgeGlobalIndex i.leftGlobalIndex A.carrierData.tailStart

/-- The rooted right block is the bridge root followed by the right internal
gap factors. -/
noncomputable def rootedRightBlockApproximateIdentity
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k) :
    Section43ProductTimeApproximateIdentity ((i.m - 1) + 1) :=
  R.prependRootReindex
    i.bridgeGlobalIndex i.rightGlobalIndex A.carrierData.tailStart

/-- The positive anchor for the rooted left block. -/
def rootedLeftBlockAnchor
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k) :
    Fin ((i.n - 1) + 1) → ℝ :=
  Fin.cons
    (anchor i.bridgeGlobalIndex / 3)
    (A.leftInternalAnchor i)

/-- The positive anchor for the rooted right block. -/
def rootedRightBlockAnchor
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k) :
    Fin ((i.m - 1) + 1) → ℝ :=
  Fin.cons
    (anchor i.bridgeGlobalIndex / 3)
    (A.rightInternalAnchor i)

theorem rootedLeftBlockAnchor_positive
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k) :
    A.rootedLeftBlockAnchor i ∈
      section43TimeStrictPositiveRegion ((i.n - 1) + 1) := by
  intro a
  refine Fin.cases ?_ ?_ a
  · exact div_pos (A.anchor_positive i.bridgeGlobalIndex) (by positivity)
  · intro b
    exact A.leftInternalAnchor_positive i b

theorem rootedRightBlockAnchor_positive
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (i : GeneratorIndex k) :
    A.rootedRightBlockAnchor i ∈
      section43TimeStrictPositiveRegion ((i.m - 1) + 1) := by
  intro a
  refine Fin.cases ?_ ?_ a
  · exact div_pos (A.anchor_positive i.bridgeGlobalIndex) (by positivity)
  · intro b
    exact A.rightInternalAnchor_positive i b

/-- The translated rooted left product source is exactly the bridge root
prepended to the original left internal time source. -/
theorem rootedLeftBlock_translatedSource_f
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (N : ℕ) :
    ((A.rootedLeftBlockApproximateIdentity R i).translatedSource
      (A.rootedLeftBlockAnchor i)
      (A.rootedLeftBlockAnchor_positive i) N).f =
        SCV.prependField
          (A.rootedBridgeHead R i N).f
          (A.leftInternalSource i N).f := by
  ext x
  simp [rootedLeftBlockApproximateIdentity, rootedLeftBlockAnchor,
    TripleConvolutionRootData.prependRootReindex,
    translatedSource, test, source, section43TimeProductSource,
    section43TimeProductTensor, SchwartzMap.productTensor_apply,
    SCV.translateSchwartz_apply, rootedBridgeHead,
    leftInternalSource, leftInternalFactor, translatedFactor,
    section43CompactPositiveTimeSource1D_translateRight,
    section43TranslateSchwartzReal_apply, leftInternalAnchor]

/-- The translated rooted right product source is exactly the bridge root
prepended to the original right internal time source. -/
theorem rootedRightBlock_translatedSource_f
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (N : ℕ) :
    ((A.rootedRightBlockApproximateIdentity R i).translatedSource
      (A.rootedRightBlockAnchor i)
      (A.rootedRightBlockAnchor_positive i) N).f =
        SCV.prependField
          (A.rootedBridgeHead R i N).f
          (A.rightInternalSource i N).f := by
  ext x
  simp [rootedRightBlockApproximateIdentity, rootedRightBlockAnchor,
    TripleConvolutionRootData.prependRootReindex,
    translatedSource, test, source, section43TimeProductSource,
    section43TimeProductTensor, SchwartzMap.productTensor_apply,
    SCV.translateSchwartz_apply, rootedBridgeHead,
    rightInternalSource, rightInternalFactor, translatedFactor,
    section43CompactPositiveTimeSource1D_translateRight,
    section43TranslateSchwartzReal_apply, rightInternalAnchor]

/-- The rooted left block with an arbitrary full spatial profile, presented
through the ordinary translated product-source API. -/
noncomputable def rootedLeftBlockSpatialSource
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (N : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((i.n - 1) + 1)) ℂ) :
    euclideanPositiveTimeSubmodule (d := d) ((i.n - 1) + 1) :=
  (A.rootedLeftBlockApproximateIdentity R i
    ).translatedPositiveTimeSpatialSource
      (A.rootedLeftBlockAnchor i)
      (A.rootedLeftBlockAnchor_positive i) χ N

@[simp]
theorem rootedLeftBlockSpatialSource_coe
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (N : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((i.n - 1) + 1)) ℂ) :
    (A.rootedLeftBlockSpatialSource R i N χ).1 =
      section43OrderedPullbackTimeSpatialTensorCLM
        d ((i.n - 1) + 1) χ
        (SCV.prependField
          (A.rootedBridgeHead R i N).f
          (A.leftInternalSource i N).f) := by
  rw [rootedLeftBlockSpatialSource,
    translatedPositiveTimeSpatialSource_coe]
  change
    section43OrderedPullbackTimeSpatialTensorCLM
        d ((i.n - 1) + 1) χ
        ((A.rootedLeftBlockApproximateIdentity R i).translatedSource
          (A.rootedLeftBlockAnchor i)
          (A.rootedLeftBlockAnchor_positive i) N).f =
      _
  rw [A.rootedLeftBlock_translatedSource_f]

/-- The rooted right block with an arbitrary full spatial profile. -/
noncomputable def rootedRightBlockSpatialSource
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (N : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((i.m - 1) + 1)) ℂ) :
    euclideanPositiveTimeSubmodule (d := d) ((i.m - 1) + 1) :=
  (A.rootedRightBlockApproximateIdentity R i
    ).translatedPositiveTimeSpatialSource
      (A.rootedRightBlockAnchor i)
      (A.rootedRightBlockAnchor_positive i) χ N

@[simp]
theorem rootedRightBlockSpatialSource_coe
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k)
    (N : ℕ)
    (χ : SchwartzMap
      (Section43SpatialSpace d ((i.m - 1) + 1)) ℂ) :
    (A.rootedRightBlockSpatialSource R i N χ).1 =
      section43OrderedPullbackTimeSpatialTensorCLM
        d ((i.m - 1) + 1) χ
        (SCV.prependField
          (A.rootedBridgeHead R i N).f
          (A.rightInternalSource i N).f) := by
  rw [rootedRightBlockSpatialSource,
    translatedPositiveTimeSpatialSource_coe]
  change
    section43OrderedPullbackTimeSpatialTensorCLM
        d ((i.m - 1) + 1) χ
        ((A.rootedRightBlockApproximateIdentity R i).translatedSource
          (A.rootedRightBlockAnchor i)
          (A.rootedRightBlockAnchor_positive i) N).f =
      _
  rw [A.rootedRightBlock_translatedSource_f]

/-- All rooted left-block packet scales and spatial profiles share one
compact strict-positive difference-time carrier. -/
theorem rootedLeftBlockSpatialSource_uniformCompactSupport_all_scales
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k) :
    HasUniformCompactStrictPositiveDifferenceTimeSupport
      (fun p :
          ℕ × SchwartzMap
            (Section43SpatialSpace d ((i.n - 1) + 1)) ℂ =>
        (A.rootedLeftBlockSpatialSource R i p.1 p.2).1) := by
  obtain ⟨C, hCtail⟩ :=
    (A.rootedLeftBlockApproximateIdentity R i
      ).exists_anchoredCompactTimeCarrierData_zeroTail
        (A.rootedLeftBlockAnchor i)
        (A.rootedLeftBlockAnchor_positive i)
  refine
    ⟨C.carrier, C.carrier_compact, C.carrier_positive, ?_⟩
  intro p x hx
  exact
    osiiA0_orderedPullback_tsupport_subset_timeSet
      (d := d) p.2
      ((A.rootedLeftBlockApproximateIdentity R i).translatedSource
        (A.rootedLeftBlockAnchor i)
        (A.rootedLeftBlockAnchor_positive i) p.1).f
      C.carrier
      (by
        simpa [hCtail] using C.translated_support p.1)
      (by
        simpa [rootedLeftBlockSpatialSource,
          translatedPositiveTimeSpatialSource_coe] using hx)

/-- Right-hand analogue of
`rootedLeftBlockSpatialSource_uniformCompactSupport_all_scales`. -/
theorem rootedRightBlockSpatialSource_uniformCompactSupport_all_scales
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (R : TripleConvolutionRootData I)
    (i : GeneratorIndex k) :
    HasUniformCompactStrictPositiveDifferenceTimeSupport
      (fun p :
          ℕ × SchwartzMap
            (Section43SpatialSpace d ((i.m - 1) + 1)) ℂ =>
        (A.rootedRightBlockSpatialSource R i p.1 p.2).1) := by
  obtain ⟨C, hCtail⟩ :=
    (A.rootedRightBlockApproximateIdentity R i
      ).exists_anchoredCompactTimeCarrierData_zeroTail
        (A.rootedRightBlockAnchor i)
        (A.rootedRightBlockAnchor_positive i)
  refine
    ⟨C.carrier, C.carrier_compact, C.carrier_positive, ?_⟩
  intro p x hx
  exact
    osiiA0_orderedPullback_tsupport_subset_timeSet
      (d := d) p.2
      ((A.rootedRightBlockApproximateIdentity R i).translatedSource
        (A.rootedRightBlockAnchor i)
        (A.rootedRightBlockAnchor_positive i) p.1).f
      C.carrier
      (by
        simpa [hCtail] using C.translated_support p.1)
      (by
        simpa [rootedRightBlockSpatialSource,
          translatedPositiveTimeSpatialSource_coe] using hx)

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
