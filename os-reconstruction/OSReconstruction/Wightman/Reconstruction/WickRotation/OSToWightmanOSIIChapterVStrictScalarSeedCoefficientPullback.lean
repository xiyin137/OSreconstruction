/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVLogarithmicStageCompactBounds
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStrictScalarSeedCoefficientChart














noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- The open coefficient-space preimage of a logarithmic continuation stage. -/
def osiiStrictScalarSeedCoefficientCarrier
    {ι : Type} [Fintype ι]
    {d k : Nat}
    (A : OSIITimeContinuationStage d k)
    (seed : ι -> Fin k -> Real) :
    Set (ι -> Complex) :=
  osiiStrictScalarSeedCoefficientMap seed ⁻¹'
    (logarithmicPullbackStage A).carrier

theorem isOpen_osiiStrictScalarSeedCoefficientCarrier
    {ι : Type} [Fintype ι]
    {d k : Nat}
    (A : OSIITimeContinuationStage d k)
    (seed : ι -> Fin k -> Real) :
    IsOpen (osiiStrictScalarSeedCoefficientCarrier A seed) := by
  exact
    (logarithmicPullbackStage A).carrier_open.preimage
      (osiiStrictScalarSeedCoefficientMap_differentiable seed).continuous

/-- Pair the coefficient pullback of a logarithmic stage with one fixed
spatial Schwartz test. -/
def osiiStrictScalarSeedCoefficientPairing
    {ι : Type} [Fintype ι]
    {d k : Nat}
    (A : OSIITimeContinuationStage d k)
    (seed : ι -> Fin k -> Real)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (r : ι -> Complex) :
    Complex :=
  A.distribution
    (osiiLogExp (osiiStrictScalarSeedCoefficientMap seed r)) chi

/-- Every scalar coefficient pairing is holomorphic on the open pullback
carrier. -/
theorem differentiableOn_osiiStrictScalarSeedCoefficientPairing
    {ι : Type} [Fintype ι]
    {d k : Nat}
    (A : OSIITimeContinuationStage d k)
    (seed : ι -> Fin k -> Real)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    DifferentiableOn Complex
      (osiiStrictScalarSeedCoefficientPairing A seed chi)
      (osiiStrictScalarSeedCoefficientCarrier A seed) := by
  exact
    ((logarithmicPullbackStage A).weaklyHolomorphic chi).comp
      (osiiStrictScalarSeedCoefficientMap_differentiable seed).differentiableOn
      (fun _ hr => hr)

/-- Compact-local Schwartz bounds transfer from the logarithmic stage to its
finite seed coefficient pullback. -/
theorem exists_uniform_schwartz_bound_seedCoefficientPairing_on_compact
    {ι : Type} [Fintype ι]
    {d k : Nat}
    (A : OSIITimeContinuationStage d k)
    (seed : ι -> Fin k -> Real)
    (K : Set (ι -> Complex))
    (hK_compact : IsCompact K)
    (hK_subset :
      K ⊆ osiiStrictScalarSeedCoefficientCarrier A seed) :
    ∃ s : Finset (Nat × Nat), ∃ C : Real, 0 < C ∧
      ∀ r ∈ K,
        ∀ chi : SchwartzMap (Section43SpatialSpace d k) Complex,
          ‖osiiStrictScalarSeedCoefficientPairing A seed chi r‖ <=
            C * s.sup
              (schwartzSeminormFamily Complex
                (Section43SpatialSpace d k) Complex) chi := by
  let L : (ι -> Complex) -> (Fin k -> Complex) :=
    osiiStrictScalarSeedCoefficientMap seed
  have hL_continuous : Continuous L :=
    (osiiStrictScalarSeedCoefficientMap_differentiable seed).continuous
  have himage_compact : IsCompact (L '' K) :=
    hK_compact.image hL_continuous
  have himage_subset :
      L '' K ⊆ (logarithmicPullbackStage A).carrier := by
    rintro z ⟨r, hr, rfl⟩
    exact hK_subset hr
  obtain ⟨s, C, hC, hbound⟩ :=
    exists_uniform_schwartz_bound_logarithmicPullbackStage_on_compact
      A (L '' K) himage_compact himage_subset
  refine ⟨s, C, hC, ?_⟩
  intro r hr chi
  exact hbound (L r) ⟨r, hr, rfl⟩ chi

namespace GeneratedScalarSeedStageLevelSuccessorData

variable
  {d : Nat} [NeZero d]
  {current : SimultaneousTimeContinuationStageLevel d}
  {OS : OsterwalderSchraderAxioms d}
  {depth : Nat}

end GeneratedScalarSeedStageLevelSuccessorData

end OSIIChapterV
end OSReconstruction
