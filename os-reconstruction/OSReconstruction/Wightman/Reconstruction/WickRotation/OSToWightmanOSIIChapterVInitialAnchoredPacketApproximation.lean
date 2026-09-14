/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVInitialAnchoredPacketTimeShell














noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity
namespace AnchoredPacketTimeShellFamilyData

variable {d k : ℕ} [NeZero d] [NeZero k]
variable
  {I : Section43ProductTimeApproximateIdentity k}
  {anchor : Fin k → ℝ}

/-- Every anchored tail test is compactly supported in the common carrier. -/
theorem timeTest_compact
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (N : ℕ) :
    HasCompactSupport (A.timeTest N : (Fin k → ℝ) → ℂ) := by
  refine
    HasCompactSupport.of_support_subset_isCompact
      A.carrierData.carrier_compact ?_
  intro x hx
  exact
    A.carrierData.translated_support N
      (subset_tsupport (A.timeTest N) hx)

/-- Every anchored tail test remains in the strict-positive time region. -/
theorem timeTest_positive
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (N : ℕ) :
    tsupport (A.timeTest N : (Fin k → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion k :=
  (A.carrierData.translated_support N).trans
    A.carrierData.carrier_positive

/-- The support radius retained by the anchored tail. -/
def timeRadius
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (N : ℕ) : ℝ :=
  I.radius (N + A.carrierData.tailStart)

/-- The anchored tail radii still shrink to zero. -/
theorem timeRadius_tendsto
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor) :
    Filter.Tendsto A.timeRadius Filter.atTop (𝓝 0) := by
  exact I.radius_tendsto.comp
    (Filter.tendsto_add_atTop_nat A.carrierData.tailStart)

/-- The original-OS quantitative target: one compact complex-time bound
uniform in both the shrinking time scale and the spatial packet level. -/
def HasUniformPacketCompactBoundOfOS
    (A : AnchoredPacketTimeShellFamilyData (d := d) I anchor)
    (OS : OsterwalderSchraderAxioms d)
    (η : ℝ)
    (hηsum :
      (k : ℝ) * (Fintype.card (osiiAxisPairIndex d) : ℝ) *
          Real.arctan η < Real.pi / 2) : Prop :=
  ∀ K : Set (OSIITimeGapSpace k),
    IsCompact K →
      K ⊆ osiiNarrowTimeCarrier (k := k) η →
        ∀ χ : SchwartzMap (Section43SpatialSpace d k) ℂ,
          ∃ C : ℝ, ∀ N level ζ, ζ ∈ K →
            ‖initialSpatialFactorPacketDistributionOfOS
                OS (A.timeTest N)
                  (A.timeTest_compact N)
                  (A.timeTest_positive N)
                  η hηsum level ζ χ‖ ≤ C

end AnchoredPacketTimeShellFamilyData
end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
