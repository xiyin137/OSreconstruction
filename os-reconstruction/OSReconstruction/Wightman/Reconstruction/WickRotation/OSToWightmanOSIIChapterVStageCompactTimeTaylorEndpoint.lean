/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVStageTaylorEndpoint
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVCompactTimeReflectedSchwingerGerm










open Complex Topology Filter
open scoped BigOperators Classical

noncomputable section

namespace OSReconstruction
namespace OSIIChapterV

variable {d q : ℕ} [NeZero d]

/-- A finite compact-time Hilbert Taylor sum is continuous linear in the
spatial Schwartz factor when the complex time increment is fixed. -/
noncomputable def compactTimeSpatialTaylorPartialSumCLM
    (OS : OsterwalderSchraderAxioms d)
    {n : ℕ}
    (g : Section43CompactStrictPositiveTimeSource n)
    (hn : 0 < n)
    (N : ℕ)
    (z : Fin (n - 1) → ℂ) :
    SchwartzMap (Section43SpatialSpace d n) ℂ →L[ℂ]
      OSHilbertSpace OS :=
  ∑ p ∈ Finset.range N,
    ∑ α ∈ Finset.Nat.antidiagonalTuple (n - 1) p,
      (∏ i, z i ^ α i) •
        ((osiiPositiveTimeSingleVectorCLM OS n).comp
          ((PositiveTimeSourceTaylorFamily.normalizedDerivativeCLM
            (fun r =>
              chronologicalTimeSourceDirectionOfPositive hn r) α).comp
            (section43PositiveTimeSpatialSourceCLM d n g)))

@[simp]
theorem compactTimeSpatialTaylorPartialSumCLM_apply
    (OS : OsterwalderSchraderAxioms d)
    {n : ℕ}
    (g : Section43CompactStrictPositiveTimeSource n)
    (hn : 0 < n)
    (N : ℕ)
    (z : Fin (n - 1) → ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ) :
    compactTimeSpatialTaylorPartialSumCLM OS g hn N z χ =
      (PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives
        (section43PositiveTimeSpatialSourceCLM d n g χ)
        (fun r =>
          chronologicalTimeSourceDirectionOfPositive hn r)).partialSum
        OS N z := by
  simp [compactTimeSpatialTaylorPartialSumCLM,
    PositiveTimeSourceTaylorFamily.partialSum,
    PositiveTimeSourceTaylorFamily.monomial]

/-- The complete family of Taylor-constructed Hilbert fields for all spatial
Schwartz factors of one fixed time profile. Every field has the same complex
polydisc radius and the same local real-edge neighborhood. -/
structure CompactTimeSpatialSourceHilbertFieldFamilyData
    (OS : OsterwalderSchraderAxioms d) {n : ℕ}
    (g : Section43CompactStrictPositiveTimeSource n) where
  particle_pos : 0 < n
  radius : ℝ
  radius_pos : 0 < radius
  field :
    (Fin (n - 1) → ℂ) →
      SchwartzMap (Section43SpatialSpace d n) ℂ →L[ℂ]
        OSHilbertSpace OS
  taylor :
    ∀ χ,
      TendstoLocallyUniformlyOn
        ((PositiveTimeSourceTaylorFamily.ofNormalizedDerivatives
          (section43PositiveTimeSpatialSourceCLM
            d n g χ)
          (fun r : Fin (n - 1) =>
            chronologicalTimeSourceDirectionOfPositive
              (d := d) particle_pos r)).partialSum OS)
        (fun z => field z χ) atTop
        (SCV.Polydisc
          (0 : Fin (n - 1) → ℂ) (fun _ => radius))
  holomorphic :
    ∀ χ,
      DifferentiableOn ℂ (fun z => field z χ)
        (SCV.Polydisc
          (0 : Fin (n - 1) → ℂ) (fun _ => radius))
  realRegion : Set (Fin (n - 1) → ℝ)
  realRegion_nhds :
    realRegion ∈ 𝓝 (0 : Fin (n - 1) → ℝ)
  realRegion_open : IsOpen realRegion
  realEdge :
    ∀ χ,
      HasPositiveTimeSourceRealEdge OS (fun z => field z χ)
        (localPositiveTimeParameterTranslate
          (section43PositiveTimeSpatialSourceCLM
            d n g χ)
          (fun r : Fin (n - 1) =>
            chronologicalTimeSourceDirectionOfPositive
              (d := d) particle_pos r))
        realRegion

end OSIIChapterV
end OSReconstruction
