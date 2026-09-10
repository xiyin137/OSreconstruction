/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductNeighborhood


















noncomputable section

open Set
open Topology
open scoped Classical

namespace OSReconstruction

variable {d k : ℕ} [NeZero d]

/-- Rotate a one-point Schwartz factor by the inverse-coordinate action of a
proper Euclidean rotation. -/
noncomputable def osiiOrderedRotateFactor
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (f : SchwartzSpacetime d) :
    SchwartzSpacetime d :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (osiiEuclideanRotationInvCLE R hR) f

omit [NeZero d] in
theorem tsupport_osiiOrderedRotateFactor
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (f : SchwartzSpacetime d) :
    tsupport
        ((osiiOrderedRotateFactor R hR f : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ) =
      (osiiEuclideanRotationInvCLE R hR).toHomeomorph ⁻¹'
        tsupport ((f : SchwartzSpacetime d) : SpacetimeDim d → ℂ) := by
  simpa [osiiOrderedRotateFactor,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
    (tsupport_comp_eq_preimage
      (g := ((f : SchwartzSpacetime d) : SpacetimeDim d → ℂ))
      (osiiEuclideanRotationInvCLE R hR).toHomeomorph)

omit [NeZero d] in
theorem hasCompactSupport_osiiOrderedRotateFactor
    (R : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (hR : R.transpose * R = 1)
    (f : SchwartzSpacetime d)
    (hf : HasCompactSupport
      ((f : SchwartzSpacetime d) : SpacetimeDim d → ℂ)) :
    HasCompactSupport
      ((osiiOrderedRotateFactor R hR f : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ) := by
  simpa [osiiOrderedRotateFactor,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
    hf.comp_homeomorph
      (osiiEuclideanRotationInvCLE R hR).toHomeomorph

omit [NeZero d] in
theorem tsupport_productTensor_subset_factor_tsupport
    (fs : Fin k → SchwartzSpacetime d) :
    tsupport
        ((SchwartzMap.productTensor fs : SchwartzNPoint d k) :
          NPointDomain d k → ℂ)
      ⊆ {x | ∀ i : Fin k,
        x i ∈ tsupport
          ((fs i : SchwartzSpacetime d) : SpacetimeDim d → ℂ)} := by
  intro x hx i
  by_contra hxi
  have hlocal :
      ((fs i : SchwartzSpacetime d) : SpacetimeDim d → ℂ)
          =ᶠ[𝓝 (x i)] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hxi
  have hcoord :
      Filter.Tendsto (fun y : NPointDomain d k => y i)
        (𝓝 x) (𝓝 (x i)) :=
    (continuous_apply i).continuousAt
  have hprod :
      ((SchwartzMap.productTensor fs : SchwartzNPoint d k) :
          NPointDomain d k → ℂ) =ᶠ[𝓝 x] 0 := by
    filter_upwards [hcoord.eventually hlocal] with y hy
    rw [SchwartzMap.productTensor_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hy
  exact (notMem_tsupport_iff_eventuallyEq.mpr hprod) hx

omit [NeZero d] in
theorem hasCompactSupport_productTensor
    (fs : Fin k → SchwartzSpacetime d)
    (hfs : ∀ i, HasCompactSupport
      ((fs i : SchwartzSpacetime d) : SpacetimeDim d → ℂ)) :
    HasCompactSupport
      ((SchwartzMap.productTensor fs : SchwartzNPoint d k) :
        NPointDomain d k → ℂ) := by
  let K : Set (NPointDomain d k) :=
    Set.pi Set.univ
      (fun i : Fin k =>
        tsupport ((fs i : SchwartzSpacetime d) : SpacetimeDim d → ℂ))
  have hK : IsCompact K :=
    isCompact_univ_pi (fun i => (hfs i).isCompact)
  refine HasCompactSupport.of_support_subset_isCompact hK ?_
  intro x hx
  have hxt :
      x ∈ tsupport
        ((SchwartzMap.productTensor fs : SchwartzNPoint d k) :
          NPointDomain d k → ℂ) :=
    subset_tsupport _ hx
  have hxf := tsupport_productTensor_subset_factor_tsupport fs hxt
  simpa [K, Set.pi] using hxf

namespace OSIIOrderedCompactProductSource

/-- The original factors reindexed into their stored chronological order. -/
def orderedFactors
    (P : OSIIOrderedCompactProductSource d k) :
    Fin k → SchwartzSpacetime d :=
  fun i => P.factors (P.order i)

/-- Chronologically reindexed factors after the stored proper rotation. -/
noncomputable def rotatedFactors
    (P : OSIIOrderedCompactProductSource d k) :
    Fin k → SchwartzSpacetime d :=
  fun i =>
    osiiOrderedRotateFactor P.rotation P.orthogonal
      (P.orderedFactors i)

/-- Rotated chronological factors after one common positive time shift. -/
noncomputable def normalizedFactors
    (P : OSIIOrderedCompactProductSource d k)
    (A : ℝ) :
    Fin k → SchwartzSpacetime d :=
  fun i =>
    SCV.translateSchwartz (-timeShiftVec d A) (P.rotatedFactors i)

theorem rotatedFactor_compact
    (P : OSIIOrderedCompactProductSource d k)
    (i : Fin k) :
    HasCompactSupport
      ((P.rotatedFactors i : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ) := by
  exact hasCompactSupport_osiiOrderedRotateFactor
    P.rotation P.orthogonal (P.orderedFactors i)
    (P.factor_compact (P.order i))

theorem rotatedFactors_ordered
    (P : OSIIOrderedCompactProductSource d k) :
    ∀ i j : Fin k, i < j →
      ∀ y ∈ tsupport
          ((P.rotatedFactors i : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ),
        ∀ z ∈ tsupport
            ((P.rotatedFactors j : SchwartzSpacetime d) :
              SpacetimeDim d → ℂ),
          y 0 < z 0 := by
  intro i j hij y hy z hz
  have hy' :
      P.rotation.transpose.mulVec y ∈
        tsupport
          ((P.factors (P.order i) : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) := by
    rw [rotatedFactors, tsupport_osiiOrderedRotateFactor] at hy
    exact hy
  have hz' :
      P.rotation.transpose.mulVec z ∈
        tsupport
          ((P.factors (P.order j) : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) := by
    rw [rotatedFactors, tsupport_osiiOrderedRotateFactor] at hz
    exact hz
  have hord := P.ordered_support i j hij
    (P.rotation.transpose.mulVec y) hy'
    (P.rotation.transpose.mulVec z) hz'
  have hRR : P.rotation * P.rotation.transpose = 1 :=
    mul_eq_one_comm.mpr P.orthogonal
  simpa [osiiRotatedTime, Matrix.mulVec_mulVec, hRR] using hord

/-- The normalized factor family is still compact factor by factor. -/
theorem normalizedFactor_compact
    (P : OSIIOrderedCompactProductSource d k)
    (A : ℝ) (i : Fin k) :
    HasCompactSupport
      ((P.normalizedFactors A i : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ) := by
  change HasCompactSupport
    ((SCV.translateSchwartz (-timeShiftVec d A) (P.rotatedFactors i) :
      SchwartzSpacetime d) : SpacetimeDim d → ℂ)
  simpa [SCV.translateSchwartz_apply, Function.comp_def] using
    (P.rotatedFactor_compact i).comp_homeomorph
      (Homeomorph.addRight (-timeShiftVec d A))

/-- A common time shift preserves the strict chronological order carried by
the rotated factor supports. -/
theorem normalizedFactors_ordered
    (P : OSIIOrderedCompactProductSource d k)
    (A : ℝ) :
    ∀ i j : Fin k, i < j →
      ∀ y ∈ tsupport
          ((P.normalizedFactors A i : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ),
        ∀ z ∈ tsupport
            ((P.normalizedFactors A j : SchwartzSpacetime d) :
              SpacetimeDim d → ℂ),
          y 0 < z 0 := by
  intro i j hij y hy z hz
  have hy' :
      y - timeShiftVec d A ∈
        tsupport
          ((P.rotatedFactors i : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) := by
    have hpre :=
      tsupport_comp_subset_preimage
        ((P.rotatedFactors i : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ)
        (show Continuous
          (fun w : SpacetimeDim d => w - timeShiftVec d A) by fun_prop)
        hy
    simpa [normalizedFactors, SCV.translateSchwartz_apply] using hpre
  have hz' :
      z - timeShiftVec d A ∈
        tsupport
          ((P.rotatedFactors j : SchwartzSpacetime d) :
            SpacetimeDim d → ℂ) := by
    have hpre :=
      tsupport_comp_subset_preimage
        ((P.rotatedFactors j : SchwartzSpacetime d) :
          SpacetimeDim d → ℂ)
        (show Continuous
          (fun w : SpacetimeDim d => w - timeShiftVec d A) by fun_prop)
        hz
    simpa [normalizedFactors, SCV.translateSchwartz_apply] using hpre
  have hord :=
    P.rotatedFactors_ordered i j hij
      (y - timeShiftVec d A) hy'
      (z - timeShiftVec d A) hz'
  simpa [timeShiftVec] using hord

/-- A chosen positive-time normalization of an ordered compact product
source. The derived theorems below expose the exact data consumed by the
compact packet machinery. -/
structure PositiveNormalization
    (P : OSIIOrderedCompactProductSource d k) where
  shift : ℝ
  shift_pos : 0 < shift
  orderedPositive :
    tsupport
        ((SchwartzMap.productTensor (P.normalizedFactors shift) :
          SchwartzNPoint d k) : NPointDomain d k → ℂ)
      ⊆ OrderedPositiveTimeRegion d k

namespace PositiveNormalization

theorem factor_compact
    {P : OSIIOrderedCompactProductSource d k}
    (N : P.PositiveNormalization)
    (i : Fin k) :
    HasCompactSupport
      ((P.normalizedFactors N.shift i : SchwartzSpacetime d) :
        SpacetimeDim d → ℂ) :=
  P.normalizedFactor_compact N.shift i

end PositiveNormalization

end OSIIOrderedCompactProductSource

end OSReconstruction
