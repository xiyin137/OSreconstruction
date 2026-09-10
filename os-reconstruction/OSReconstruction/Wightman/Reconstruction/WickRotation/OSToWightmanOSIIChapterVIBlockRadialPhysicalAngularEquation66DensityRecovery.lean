/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.SCV.LocallyUniformDistributionRepresentation
import OSReconstruction.SCV.EuclideanWeylApproxIdentity
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPhysicalAngularEquation66MeanValue


















noncomputable section

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical UniformConvergence

namespace OSReconstruction

/-- One fixed compact, real, nonnegative Euclidean approximate identity for
density recovery.  Keeping the stronger witness lets later pointwise
recovery arguments use the same canonical kernels instead of choosing a
parallel approximation family. -/
noncomputable def osiiDensityRecoveryKernel
    (m : Nat) (radius : Real) (hradius : 0 < radius) :
    Nat -> SchwartzMap (EuclideanSpace Real (Fin m)) Complex :=
  Classical.choose
    (SCV.exists_shrinking_normalized_euclideanWeylBump_sequence
      (ι := Fin m) hradius)

/-- The sup norm of a complex point is bounded by the separate real and
imaginary sup norms. -/
theorem osiiStep4ComplexOfRealImag_norm_le_add
    {m : Nat} (x y : Fin m -> Real) :
    ‖osiiStep4ComplexOfRealImag x y‖ <= ‖x‖ + ‖y‖ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  calc
    ‖osiiStep4ComplexOfRealImag x y i‖ <= ‖x i‖ + ‖y i‖ := by
      change ‖(x i : Complex) + (y i : Complex) * I‖ <=
        ‖x i‖ + ‖y i‖
      calc
        ‖(x i : Complex) + (y i : Complex) * I‖ <=
            ‖(x i : Complex)‖ + ‖(y i : Complex) * I‖ := norm_add_le _ _
        _ = ‖x i‖ + ‖y i‖ := by simp
    _ <= ‖x‖ + ‖y‖ :=
      add_le_add (norm_le_pi_norm x i) (norm_le_pi_norm y i)

/-- Distance from a complex horizontal point to a real center is bounded by
the real displacement plus the imaginary norm. -/
theorem osiiStep4ComplexOfRealImag_dist_realEmbed_le
    {m : Nat} (x y c : Fin m -> Real) :
    dist (osiiStep4ComplexOfRealImag x y) (SCV.realEmbed c) <=
      dist x c + ‖y‖ := by
  rw [dist_eq_norm, dist_eq_norm]
  have hid :
      osiiStep4ComplexOfRealImag x y - SCV.realEmbed c =
        osiiStep4ComplexOfRealImag (x - c) y := by
    ext i
    simp [osiiStep4ComplexOfRealImag, SCV.realEmbed]
    ring
  rw [hid]
  exact osiiStep4ComplexOfRealImag_norm_le_add (x - c) y

/-- The blockwise Euclidean support bound controls the ambient flattened sup
norm. -/
theorem osiiStep4FullBlockRadialClosedSupport_norm_le
    (q k : Nat) [NeZero q] [NeZero k] (tau : Real)
    (z : Fin (k * q) -> Complex)
    (hz : z ∈ osiiStep4FullBlockRadialClosedSupport q k tau) :
    ‖z‖ <= tau / 8 := by
  rw [pi_norm_le_iff_of_nonneg]
  · intro a
    obtain ⟨⟨i, mu⟩, rfl⟩ := finProdFinEquiv.surjective a
    let block : Fin q -> Complex :=
      (osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z i
    calc
      ‖z (finProdFinEquiv (i, mu))‖ = ‖block mu‖ := by rfl
      _ <= ‖osiiStep4ComplexBlockToEuclideanCLE q block‖ := by
        simpa using PiLp.norm_apply_le
          (osiiStep4ComplexBlockToEuclideanCLE q block) mu
      _ <= tau / 8 := hz i
  · exact (norm_nonneg
      (osiiStep4ComplexBlockToEuclideanCLE q
        ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z 0))).trans
      (hz 0)

/-- Domain and support geometry shared by the density-recovery producers. -/
structure OSIIImaginarySliceDensityGeometry
    (d k : Nat)
    (Y X : Set (Fin (k * (d + 1)) -> Real)) where
  domain : Set (Fin (k * (d + 1)) -> Complex)
  domain_open : IsOpen domain
  domain_connected : IsConnected domain
  realSeed : Set (Fin (k * (d + 1)) -> Real)
  realSeed_open : IsOpen realSeed
  realSeed_nonempty : realSeed.Nonempty
  realSeed_subset_support : realSeed ⊆ X
  zero_mem_imaginary : (0 : Fin (k * (d + 1)) -> Real) ∈ Y
  realSeed_subset_domain : forall x, x ∈ realSeed ->
    osiiStep4ComplexOfRealImag x 0 ∈ domain
  support_compact : IsCompact X
  horizontal_support_subset_domain : forall y, y ∈ Y -> forall x, x ∈ X ->
    osiiStep4ComplexOfRealImag x y ∈ domain

/-- A translated complex ball provides all abstract density-recovery
geometry once the equation-`(6.6)` scale is smaller than its radius. -/
noncomputable def osiiLocalBallDensityGeometry
    (d k : Nat) [NeZero d] [NeZero k]
    (center : Fin (k * (d + 1)) -> Real)
    (R sigma : Real) (hR : 0 < R) (hsigma : 0 < sigma)
    (hsigma_R : sigma <= R / 2) :
    OSIIImaginarySliceDensityGeometry d k
      (Metric.closedBall 0 (sigma / 4))
      (Metric.closedBall
        (osiiStep4MultiGapXiHatCenter d k center) (sigma / 4)) where
  domain := Metric.ball
    (SCV.realEmbed (osiiStep4MultiGapXiHatCenter d k center)) (R / 2)
  domain_open := Metric.isOpen_ball
  domain_connected := Metric.isConnected_ball (by positivity)
  realSeed := Metric.ball
    (osiiStep4MultiGapXiHatCenter d k center) (sigma / 4)
  realSeed_open := Metric.isOpen_ball
  realSeed_nonempty :=
    ⟨osiiStep4MultiGapXiHatCenter d k center,
      Metric.mem_ball_self (by positivity)⟩
  realSeed_subset_support := Metric.ball_subset_closedBall
  zero_mem_imaginary := by
    rw [Metric.mem_closedBall, dist_self]
    positivity
  realSeed_subset_domain := by
    intro x hx
    rw [Metric.mem_ball] at hx ⊢
    calc
      dist (osiiStep4ComplexOfRealImag x 0)
          (SCV.realEmbed (osiiStep4MultiGapXiHatCenter d k center)) <=
          dist x (osiiStep4MultiGapXiHatCenter d k center) + ‖(0 :
            Fin (k * (d + 1)) -> Real)‖ :=
        osiiStep4ComplexOfRealImag_dist_realEmbed_le x 0 _
      _ < sigma / 4 := by simpa using hx
      _ <= R / 8 := by linarith
      _ < R / 2 := by linarith
  support_compact := isCompact_closedBall _ _
  horizontal_support_subset_domain := by
    intro y hy x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    rw [Metric.mem_closedBall] at hx
    rw [Metric.mem_ball]
    calc
      dist (osiiStep4ComplexOfRealImag x y)
          (SCV.realEmbed (osiiStep4MultiGapXiHatCenter d k center)) <=
          dist x (osiiStep4MultiGapXiHatCenter d k center) + ‖y‖ :=
        osiiStep4ComplexOfRealImag_dist_realEmbed_le x y _
      _ <= sigma / 4 + sigma / 4 := add_le_add hx hy
      _ <= R / 4 := by linarith
      _ < R / 2 := by linarith

namespace OSIIImaginarySliceHolomorphicMollificationData

variable {d k : Nat}
variable {B : OSIIImaginarySliceDistributionFamily d k}
variable {Y X : Set (Fin (k * (d + 1)) -> Real)}

end OSIIImaginarySliceHolomorphicMollificationData

namespace OSIIImaginarySliceCanonicalMollificationData

variable {d k : Nat}
variable {B : OSIIImaginarySliceDistributionFamily d k}
variable {Y X : Set (Fin (k * (d + 1)) -> Real)}

end OSIIImaginarySliceCanonicalMollificationData

namespace OSIIImaginarySliceHolomorphicApproximationData

variable {d k : Nat}
variable {B : OSIIImaginarySliceDistributionFamily d k}
variable {Y X : Set (Fin (k * (d + 1)) -> Real)}

end OSIIImaginarySliceHolomorphicApproximationData

namespace OSIIImaginarySliceHolomorphicMollificationData

variable {d k : Nat}
variable {B : OSIIImaginarySliceDistributionFamily d k}
variable {Y X : Set (Fin (k * (d + 1)) -> Real)}

end OSIIImaginarySliceHolomorphicMollificationData

namespace OSIIImaginarySliceCanonicalMollificationData

variable {d k : Nat}
variable {B : OSIIImaginarySliceDistributionFamily d k}
variable {Y X : Set (Fin (k * (d + 1)) -> Real)}

end OSIIImaginarySliceCanonicalMollificationData

namespace OSIIStep4FullSchwartzAngularContinuationData

variable {d k : Nat} [NeZero d] [NeZero k]
variable {rho : Real} {hrho : 0 < rho}
variable {center : Fin (k * (d + 1)) -> Real}
variable {hcenter : forall j : Fin k,
  rho <= center (finProdFinEquiv (j, (0 : Fin (d + 1))))}
variable {OS : OsterwalderSchraderAxioms d}
variable {lgc : OSLinearGrowthCondition d OS}
variable {Z : OSIIStep4SynchronizedMultiGapContinuationData d k hrho
  (osiiStep4MultiGapXiHatCenter d k center)
  (osiiStep4MultiGapXiHatCenter_time_lower d k center hcenter)}

theorem localBallDensityGeometry_radialSupport
    (R sigma : Real) (hR : 0 < R) (hsigma : 0 < sigma)
    (hsigma_R : sigma <= R / 2)
    (z : Fin (k * (d + 1)) -> Complex)
    (hz : z ∈ osiiStep4FullBlockRadialClosedSupport
      (d + 1) k (3 * sigma)) :
    osiiStep4ComplexOfRealImag
        (osiiStep4MultiGapXiHatCenter d k center) 0 + z ∈
      (osiiLocalBallDensityGeometry
        d k center R sigma hR hsigma hsigma_R).domain := by
  change osiiStep4ComplexOfRealImag
      (osiiStep4MultiGapXiHatCenter d k center) 0 + z ∈
    Metric.ball
      (SCV.realEmbed (osiiStep4MultiGapXiHatCenter d k center)) (R / 2)
  rw [Metric.mem_ball, dist_eq_norm]
  have hcenter_eq :
      osiiStep4ComplexOfRealImag
          (osiiStep4MultiGapXiHatCenter d k center) 0 =
        SCV.realEmbed (osiiStep4MultiGapXiHatCenter d k center) := by
    ext i
    simp [osiiStep4ComplexOfRealImag, SCV.realEmbed]
  rw [hcenter_eq]
  simpa only [add_sub_cancel_left] using
    (lt_of_le_of_lt
      (osiiStep4FullBlockRadialClosedSupport_norm_le
        (d + 1) k (3 * sigma) z hz)
      (by linarith : 3 * sigma / 8 < R / 2))

end OSIIStep4FullSchwartzAngularContinuationData
end OSReconstruction
