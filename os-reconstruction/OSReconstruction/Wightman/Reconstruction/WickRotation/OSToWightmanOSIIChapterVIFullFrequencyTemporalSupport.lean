/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVITemporalSupportDensity












noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction

variable {d k : Nat} [NeZero d]

/-- Physics-convention inverse Fourier transform transported from the flat
spatial block back to the Section 4.3 spatial Schwartz space. -/
noncomputable def section43SpatialPhysicsFourierFlatInvCLM (d k : Nat) :
    SchwartzMap (Section43SpatialSpace d k) Complex →L[Complex]
      SchwartzMap (Section43SpatialSpace d k) Complex :=
  (section43SpatialFlatSchwartzCLE d k).symm.toContinuousLinearMap.comp
    ((physicsFourierFlatInvCLM (m := k * d)).comp
      (section43SpatialFlatSchwartzCLE d k).toContinuousLinearMap)

namespace OSIIFullTimeStageVladimirovGrowthData

variable {A : OSIITimeContinuationStage d k}

/-- The Chapter VI boundary pairing after inverse Fourier transform in both
the time and spatial factors. -/
noncomputable def fullFrequencyMixedBilinearMap
    (G : OSIIFullTimeStageVladimirovGrowthData A) :
    SchwartzMap (Fin k -> Real) Complex →ₗ[Complex]
      SchwartzMap (Section43SpatialSpace d k) Complex →ₗ[Complex] Complex where
  toFun phi :=
    (G.timeFrequencyMixedBilinearMap phi).comp
      (section43SpatialPhysicsFourierFlatInvCLM d k).toLinearMap
  map_add' phi psi := by
    ext chi
    simp
  map_smul' c phi := by
    ext chi
    simp

@[simp] theorem fullFrequencyMixedBilinearMap_apply
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    G.fullFrequencyMixedBilinearMap phi chi =
      G.timeFrequencyDistribution
        (section43SpatialPhysicsFourierFlatInvCLM d k chi) phi := by
  simp [fullFrequencyMixedBilinearMap, ContinuousLinearMap.comp_apply]

/-- Joint continuity survives inverse Fourier transform in the spatial factor
as well. -/
theorem continuous_fullFrequencyMixedBilinearMap
    (G : OSIIFullTimeStageVladimirovGrowthData A) :
    Continuous (fun p :
      SchwartzMap (Fin k -> Real) Complex ×
        SchwartzMap (Section43SpatialSpace d k) Complex =>
      G.fullFrequencyMixedBilinearMap p.1 p.2) := by
  exact G.continuous_timeFrequencyMixedBilinearMap.comp
    (continuous_fst.prodMk
      ((section43SpatialPhysicsFourierFlatInvCLM d k).continuous.comp
        continuous_snd))

/-- The inverse-time-and-spatial-Fourier pairings assemble into one tempered
distribution on separated full momentum coordinates. -/
theorem exists_fullFrequencyMixedBoundary
    (G : OSIIFullTimeStageVladimirovGrowthData A) [NeZero k] :
    exists W : SchwartzMap (Section43TimeSpatialSpace d k) Complex
        →L[Complex] Complex,
      forall (phi : SchwartzMap (Fin k -> Real) Complex)
        (chi : SchwartzMap (Section43SpatialSpace d k) Complex),
        W (section43TimeSpatialTensor d k phi chi) =
          G.timeFrequencyDistribution
            (section43SpatialPhysicsFourierFlatInvCLM d k chi) phi := by
  obtain ⟨W, hW⟩ :=
    exists_timeSpatialDistribution_of_continuousBilinearMap
      G.fullFrequencyMixedBilinearMap
      G.continuous_fullFrequencyMixedBilinearMap
  refine ⟨W, ?_⟩
  intro phi chi
  rw [hW, fullFrequencyMixedBilinearMap_apply]

/-- The selected full momentum-side Section 4.3 boundary distribution. -/
noncomputable def fullFrequencyMixedBoundary
    (G : OSIIFullTimeStageVladimirovGrowthData A) [NeZero k] :
    SchwartzMap (Section43TimeSpatialSpace d k) Complex →L[Complex] Complex :=
  Classical.choose G.exists_fullFrequencyMixedBoundary

@[simp] theorem fullFrequencyMixedBoundary_timeSpatialTensor
    (G : OSIIFullTimeStageVladimirovGrowthData A) [NeZero k]
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    G.fullFrequencyMixedBoundary
        (section43TimeSpatialTensor d k phi chi) =
      G.timeFrequencyDistribution
        (section43SpatialPhysicsFourierFlatInvCLM d k chi) phi :=
  Classical.choose_spec G.exists_fullFrequencyMixedBoundary phi chi

/-- The selected full-frequency boundary is independent of the nuclear
extension witness. -/
theorem fullFrequencyMixedBoundary_unique
    (G : OSIIFullTimeStageVladimirovGrowthData A) [NeZero k]
    (W : SchwartzMap (Section43TimeSpatialSpace d k) Complex
      →L[Complex] Complex)
    (hW : forall (phi : SchwartzMap (Fin k -> Real) Complex)
      (chi : SchwartzMap (Section43SpatialSpace d k) Complex),
        W (section43TimeSpatialTensor d k phi chi) =
          G.timeFrequencyDistribution
            (section43SpatialPhysicsFourierFlatInvCLM d k chi) phi) :
    W = G.fullFrequencyMixedBoundary := by
  apply section43TimeSpatial_clm_eq_of_eq_on_timeSpatialTensor
  intro phi chi
  rw [hW phi chi, fullFrequencyMixedBoundary_timeSpatialTensor]

/-- Spatial Fourier transform preserves the closed-span temporal support
statement. -/
theorem fullFrequencyMixedBoundary_eq_zero_on_timeComplementTensorClosure
    (G : OSIIFullTimeStageVladimirovGrowthData A) [NeZero k]
    (F : SchwartzMap (Section43TimeSpatialSpace d k) Complex)
    (hF : F ∈
      (section43TimeComplementTensorSubmodule d k
        (DualConeFlat (osiiTimePositiveCone k))).topologicalClosure) :
    G.fullFrequencyMixedBoundary F = 0 := by
  apply section43TimeComplementTensorClosure_annihilated
    (S := DualConeFlat (osiiTimePositiveCone k))
    (W := G.fullFrequencyMixedBoundary) (F := F) (hF := hF)
  intro phi hphi chi
  rw [G.fullFrequencyMixedBoundary_timeSpatialTensor phi chi]
  exact G.timeFrequencyDistribution_support
    (section43SpatialPhysicsFourierFlatInvCLM d k chi) phi
    (fun x hx => hphi (subset_tsupport _ hx))

/-- Full-frequency temporal positive energy for arbitrary Schwartz tests. -/
theorem fullFrequencyMixedBoundary_eq_zero_of_tsupport_misses_dualCone
    (G : OSIIFullTimeStageVladimirovGrowthData A) [NeZero k]
    (F : SchwartzMap (Section43TimeSpatialSpace d k) Complex)
    (hF : ∀ p ∈ tsupport
      (F : Section43TimeSpatialSpace d k -> Complex),
      p.1 ∉ DualConeFlat (osiiTimePositiveCone k)) :
    G.fullFrequencyMixedBoundary F = 0 := by
  apply G.fullFrequencyMixedBoundary_eq_zero_on_timeComplementTensorClosure
  exact section43TimeSpatial_mem_timeComplementTensorClosure
    (DualConeFlat (osiiTimePositiveCone k))
    (dualConeFlat_closed (osiiTimePositiveCone k)) F hF

/-- Correct distributional support statement for the full separated momentum
boundary. -/
theorem fullFrequencyMixedBoundary_isVanishingOn_compl_positiveCylinder
    (G : OSIIFullTimeStageVladimirovGrowthData A) [NeZero k] :
    Distribution.IsVanishingOn G.fullFrequencyMixedBoundary
      (osiiTimeFrequencyPositiveCylinder d k)ᶜ := by
  intro F hF
  apply G.fullFrequencyMixedBoundary_eq_zero_of_tsupport_misses_dualCone
  intro p hp
  simpa [osiiTimeFrequencyPositiveCylinder] using hF hp

end OSIIFullTimeStageVladimirovGrowthData

end OSReconstruction
