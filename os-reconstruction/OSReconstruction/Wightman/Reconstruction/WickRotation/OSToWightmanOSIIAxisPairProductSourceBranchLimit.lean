/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBase
import OSReconstruction.SCV.ConnectedNeighborhood
import OSReconstruction.SCV.TotallyRealIdentity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIILemma51AxisPair
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSemigroup
import OSReconstruction.SCV.Osgood
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIMZFlatTubeEnvelope
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceTimeProductDensity
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43SpectralFactorization
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIProductTensorSchwingerSourceCurrent
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIFixedWindowSelectors
import OSReconstruction.SCV.DistributionalEOWSupport
import OSReconstruction.SCV.LocalContinuousEOW
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Integral.Bochner.Set











noncomputable section

open Complex Topology Filter MeasureTheory
open scoped Classical BigOperators LineDeriv

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- Compact-support refinement of the finite-dimensional Schwartz cutoff
selector.

The neutral SCV cutoff theorem already constructs a compactly supported
function, but its compatibility statement only exposes the support inclusion.
For local source-density arguments we also need the compact-support fact in the
type, so we first intersect the target with a sufficiently large bounded ball
and then apply the existing theorem there. -/
theorem exists_schwartz_cutoff_eq_one_on_compact_subset_open_with_compactSupport_fin
    {m : ℕ} {K U : Set (Fin m → ℝ)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : SchwartzMap (Fin m → ℝ) ℂ,
      (∀ x ∈ K, χ x = 1) ∧
      tsupport (χ : (Fin m → ℝ) → ℂ) ⊆ U ∧
      HasCompactSupport (χ : (Fin m → ℝ) → ℂ) := by
  classical
  rcases hK.isBounded.subset_closedBall (0 : Fin m → ℝ) with ⟨R, hKR⟩
  let B : ℝ := max R 0 + 1
  let Ubounded : Set (Fin m → ℝ) := U ∩ Metric.ball 0 B
  have hB_pos : 0 < B := by
    dsimp [B]
    linarith [le_max_right R 0]
  have hUbounded_open : IsOpen Ubounded :=
    hU.inter Metric.isOpen_ball
  have hK_sub_Ubounded : K ⊆ Ubounded := by
    intro x hx
    refine ⟨hKU hx, ?_⟩
    have hxR : ‖x‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hKR hx
    have hxB : ‖x‖ < B := by
      dsimp [B]
      linarith [le_max_left R 0]
    simpa [Metric.mem_ball, dist_zero_right] using hxB
  rcases
    SCV.exists_schwartz_cutoff_eq_one_on_compact_subset_open
      hK hUbounded_open hK_sub_Ubounded with
    ⟨χ, hχ_one, hχ_support⟩
  refine ⟨χ, hχ_one, ?_, ?_⟩
  · intro x hx
    exact (hχ_support hx).1
  · refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : Fin m → ℝ) B) ?_
    intro x hx
    have hxUbounded :
        x ∈ Ubounded :=
      hχ_support (subset_tsupport (χ : (Fin m → ℝ) → ℂ) hx)
    exact Metric.ball_subset_closedBall hxUbounded.2

end OSReconstruction
