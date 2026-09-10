/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictScalarSeedCoefficientLinearSection
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictScalarSeedCoefficientGermDistribution
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictScalarSeedCoefficientDescent















noncomputable section

open Complex Set Topology
open scoped BigOperators Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- The real radial segment from zero to a nonnegative coefficient target
stays inside the coefficient germ. -/
theorem segment_strictScalarSeedCoefficientTarget_subset_germDomain
    {n : Nat} {S rho : Real}
    (P : SCV.StripCompactificationParameters S rho)
    (w : Fin n -> Real)
    (hw : forall i, 0 <= w i)
    (hsum : (∑ i, w i) <= S) :
    segment Real 0
        (osiiStrictScalarSeedCoefficientTarget w) ⊆
      osiiStrictCoefficientGermDomain P := by
  intro r hr
  rw [segment_eq_image_lineMap] at hr
  obtain ⟨t, ht, rfl⟩ := hr
  have hsum_nonneg : 0 <= ∑ i, w i :=
    Finset.sum_nonneg fun i _ => hw i
  have hscaled_sum :
      (∑ i, t * w i) <= S := by
    rw [← Finset.mul_sum]
    calc
      t * ∑ i, w i <= 1 * ∑ i, w i :=
        mul_le_mul_of_nonneg_right ht.2 hsum_nonneg
      _ = ∑ i, w i := one_mul _
      _ <= S := hsum
  have hmem :=
    osiiStrictScalarSeedCoefficientTarget_mem_germDomain
      P (fun i => t * w i)
      (fun i => mul_nonneg ht.1 (hw i))
      hscaled_sum
  convert hmem using 1
  ext i
  simp [AffineMap.lineMap_apply_module,
    osiiStrictScalarSeedCoefficientTarget]
  ring

/-- An open convex coefficient chart joining zero to one selected target
inside the coefficient germ. -/
structure StrictCoefficientTargetConvexChartData
    {n : Nat} {S rho : Real}
    (P : SCV.StripCompactificationParameters S rho)
    (r0 : Fin n -> Complex) where
  domain : Set (Fin n -> Complex)
  domain_open : IsOpen domain
  domain_convex : Convex Real domain
  zero_mem : 0 ∈ domain
  target_mem : r0 ∈ domain
  domain_subset :
    domain ⊆ osiiStrictCoefficientGermDomain P

/-- Every nonnegative target inside the compactified budget admits an open
convex coefficient chart containing both zero and the target. -/
theorem nonempty_strictCoefficientTargetConvexChartData
    {n : Nat} {S rho : Real}
    (P : SCV.StripCompactificationParameters S rho)
    (w : Fin n -> Real)
    (hw : forall i, 0 <= w i)
    (hsum : (∑ i, w i) <= S) :
    Nonempty
      (StrictCoefficientTargetConvexChartData P
        (osiiStrictScalarSeedCoefficientTarget w)) := by
  have hsegment :
      segment Real 0
          (osiiStrictScalarSeedCoefficientTarget w) ⊆
        osiiStrictCoefficientGermDomain P :=
    segment_strictScalarSeedCoefficientTarget_subset_germDomain
      P w hw hsum
  have hcompact :
      IsCompact
        (segment Real 0
          (osiiStrictScalarSeedCoefficientTarget w)) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  obtain ⟨r, hr, hthick⟩ :=
    hcompact.exists_thickening_subset_open
      (isOpen_osiiStrictCoefficientGermDomain P)
      hsegment
  exact
    ⟨{
      domain :=
        Metric.thickening r
          (segment Real 0
            (osiiStrictScalarSeedCoefficientTarget w))
      domain_open := Metric.isOpen_thickening
      domain_convex :=
        (convex_segment
          (0 : Fin n -> Complex)
          (osiiStrictScalarSeedCoefficientTarget w)).thickening r
      zero_mem :=
        Metric.self_subset_thickening hr _
          (left_mem_segment Real 0
            (osiiStrictScalarSeedCoefficientTarget w))
      target_mem :=
        Metric.self_subset_thickening hr _
          (right_mem_segment Real 0
            (osiiStrictScalarSeedCoefficientTarget w))
      domain_subset := hthick }⟩

namespace StrictScalarSeedCoefficientMZBoundData

variable
  {d : Nat} [NeZero d]
  {n k : Nat} [NeZero n]
  {A : OSIITimeContinuationStage d k}
  {S rho : Real}
  {P : SCV.StripCompactificationParameters S rho}
  {seed : Fin n -> Fin k -> Real}

/-- One coefficient ball works simultaneously for every spatial pairing. -/
theorem exists_zero_ball_coefficientGerm_eq_pairing_all
    (B : StrictScalarSeedCoefficientMZBoundData A P seed) :
    ∃ eps : Real, 0 < eps ∧
      Metric.ball (0 : Fin n -> Complex) eps ⊆
        osiiStrictCoefficientGermDomain P ∩
          osiiStrictScalarSeedCoefficientCarrier
            A seed ∧
      forall chi : SchwartzMap
          (Section43SpatialSpace d k) Complex,
        Set.EqOn
          (B.coefficientGerm chi)
          (osiiStrictScalarSeedCoefficientPairing
            A seed chi)
          (Metric.ball (0 : Fin n -> Complex) eps) := by
  have hzero_flat :
      (0 : Fin n -> Complex) ∈
        SCV.horizontalTube
          (fintypeFlatImaginaryUnion (Fin n) 1) := by
    change
      (0 : Fin n -> Real) ∈
        fintypeFlatImaginaryUnion (Fin n) 1
    exact
      zero_mem_fintypeFlatImaginaryUnion
        (ι := Fin n) (by norm_num)
  have hzero_carrier :
      (0 : Fin n -> Complex) ∈
        osiiStrictScalarSeedCoefficientCarrier
          A seed :=
    B.flatCoefficientTube_subset hzero_flat
  have hzero_germ :
      (0 : Fin n -> Complex) ∈
        osiiStrictCoefficientGermDomain P :=
    zero_mem_osiiStrictCoefficientGermDomain P
  have hopen_inter :
      IsOpen
        (osiiStrictCoefficientGermDomain P ∩
          osiiStrictScalarSeedCoefficientCarrier
            A seed) :=
    (isOpen_osiiStrictCoefficientGermDomain P).inter
      (isOpen_osiiStrictScalarSeedCoefficientCarrier
        A seed)
  obtain ⟨eps, heps, hball⟩ :=
    Metric.isOpen_iff.mp hopen_inter 0
      ⟨hzero_germ, hzero_carrier⟩
  refine ⟨eps, heps, hball, ?_⟩
  intro chi
  exact
    SCV.holomorphic_eq_of_eq_on_real_of_connected_finite
      Metric.isOpen_ball
      (Metric.isConnected_ball heps)
      ((B.coefficientGerm_differentiableOn chi).mono
        (fun z hz => (hball hz).1))
      ((differentiableOn_osiiStrictScalarSeedCoefficientPairing
        A seed chi).mono
        (fun z hz => (hball hz).2))
      (x₀ := (0 : Fin n -> Real))
      (by simpa using
        (Metric.mem_ball_self heps :
          (0 : Fin n -> Complex) ∈
            Metric.ball 0 eps))
      (fun x hx =>
        B.coefficientGerm_real chi x
          ((hball hx).1))

end StrictScalarSeedCoefficientMZBoundData

namespace StrictCoefficientTargetSectionData

variable
  {n k : Nat}
  {seed : Fin n -> Fin k -> Real}
  {r0 : Fin n -> Complex}

/-- Pull an open coefficient chart back through the target-adapted linear
lift. -/
def ambientDomain
    (R : StrictCoefficientTargetSectionData seed r0)
    {S rho : Real}
    {P : SCV.StripCompactificationParameters S rho}
    (C : StrictCoefficientTargetConvexChartData P r0) :
    Set (Fin k -> Complex) :=
  R.lift ⁻¹' C.domain

theorem ambientDomain_open
    (R : StrictCoefficientTargetSectionData seed r0)
    {S rho : Real}
    {P : SCV.StripCompactificationParameters S rho}
    (C : StrictCoefficientTargetConvexChartData P r0) :
    IsOpen (R.ambientDomain C) :=
  C.domain_open.preimage R.lift.continuous

theorem ambientDomain_convex
    (R : StrictCoefficientTargetSectionData seed r0)
    {S rho : Real}
    {P : SCV.StripCompactificationParameters S rho}
    (C : StrictCoefficientTargetConvexChartData P r0) :
    Convex Real (R.ambientDomain C) := by
  exact
    C.domain_convex.linear_preimage
      (R.lift.restrictScalars Real).toLinearMap

theorem zero_mem_ambientDomain
    (R : StrictCoefficientTargetSectionData seed r0)
    {S rho : Real}
    {P : SCV.StripCompactificationParameters S rho}
    (C : StrictCoefficientTargetConvexChartData P r0) :
    (0 : Fin k -> Complex) ∈ R.ambientDomain C := by
  change R.lift 0 ∈ C.domain
  simpa using C.zero_mem

theorem target_mem_ambientDomain
    (R : StrictCoefficientTargetSectionData seed r0)
    {S rho : Real}
    {P : SCV.StripCompactificationParameters S rho}
    (C : StrictCoefficientTargetConvexChartData P r0) :
    osiiStrictScalarSeedCoefficientCLM seed r0 ∈
      R.ambientDomain C := by
  change
    R.lift
        (osiiStrictScalarSeedCoefficientCLM seed r0) ∈
      C.domain
  rw [R.target]
  exact C.target_mem

variable
  {d : Nat} [NeZero d]
  {A : OSIITimeContinuationStage d k}
  [NeZero n]

/-- The distribution-valued coefficient germ pulled back to the ambient
logarithmic argument space. -/
noncomputable def toAmbientStage
    (R : StrictCoefficientTargetSectionData seed r0)
    {S rho : Real}
    {P : SCV.StripCompactificationParameters S rho}
    (C : StrictCoefficientTargetConvexChartData P r0)
    (B : StrictScalarSeedCoefficientMZBoundData A P seed) :
    OSIITimeContinuationStage d k where
  carrier := R.ambientDomain C
  carrier_open := R.ambientDomain_open C
  distribution :=
    fun z => B.coefficientGermDistribution (R.lift z)
  weaklyHolomorphic := by
    intro chi
    exact
      (B.coefficientGermDistribution_weaklyHolomorphic chi).comp
        R.lift.differentiable.differentiableOn
        (fun _z hz => C.domain_subset hz)

/-- The ambient pullback agrees with the predecessor logarithmic stage on a
nonempty open neighborhood of zero. -/
theorem exists_open_seed_toAmbientStage_eq_predecessor
    (R : StrictCoefficientTargetSectionData seed r0)
    {S rho : Real}
    {P : SCV.StripCompactificationParameters S rho}
    (C : StrictCoefficientTargetConvexChartData P r0)
    (B : StrictScalarSeedCoefficientMZBoundData A P seed) :
    ∃ U : Set (Fin k -> Complex),
      IsOpen U ∧ (0 : Fin k -> Complex) ∈ U ∧
      U ⊆
        (R.toAmbientStage C B).carrier ∩
          (logarithmicPullbackStage
            A).carrier ∧
      Set.EqOn
        (R.toAmbientStage C B).distribution
        (logarithmicPullbackStage A).distribution
        U := by
  obtain ⟨eps, heps, hball, hlocal⟩ :=
    B.exists_zero_ball_coefficientGerm_eq_pairing_all
  let U : Set (Fin k -> Complex) :=
    R.ambientDomain C ∩
      R.lift ⁻¹' Metric.ball (0 : Fin n -> Complex) eps
  have hU_open : IsOpen U :=
    (R.ambientDomain_open C).inter
      (Metric.isOpen_ball.preimage R.lift.continuous)
  have hU_zero : (0 : Fin k -> Complex) ∈ U := by
    refine ⟨R.zero_mem_ambientDomain C, ?_⟩
    simpa using
      (Metric.mem_ball_self heps :
        (0 : Fin n -> Complex) ∈ Metric.ball 0 eps)
  refine
    ⟨U, hU_open, hU_zero,
      ?_, ?_⟩
  · intro z hz
    refine ⟨hz.1, ?_⟩
    have hmap :
        osiiStrictScalarSeedCoefficientMap seed
            (R.lift z) =
          z := by
      simpa using R.rightInverse z
    rw [← hmap]
    exact (hball hz.2).2
  intro z hz
  apply ContinuousLinearMap.ext
  intro chi
  have hlift_ball :
      R.lift z ∈
        Metric.ball (0 : Fin n -> Complex) eps :=
    hz.2
  have hlift_germ :
      R.lift z ∈ osiiStrictCoefficientGermDomain P :=
    (hball hlift_ball).1
  change
    B.coefficientGermDistribution (R.lift z) chi =
      A.distribution (osiiLogExp z) chi
  rw [B.coefficientGermDistribution_apply_of_mem
    (R.lift z) hlift_germ chi]
  calc
    B.coefficientGerm chi (R.lift z) =
        osiiStrictScalarSeedCoefficientPairing
          A seed chi (R.lift z) :=
      hlocal chi hlift_ball
    _ =
        A.distribution
          (osiiLogExp
            (osiiStrictScalarSeedCoefficientCLM seed
              (R.lift z))) chi := by
      rw [osiiStrictScalarSeedCoefficientCLM_apply]
      rfl
    _ =
        A.distribution
          (osiiLogExp z) chi := by
      rw [R.rightInverse]

end StrictCoefficientTargetSectionData

end OSIIChapterV
end OSReconstruction
