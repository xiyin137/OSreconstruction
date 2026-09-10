import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVITimeFourierODE
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVITimeCompactExponential
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVISchwartzSupport

/-!
# Positive temporal spectrum from global OS growth

The signed horizontal-slice equation is integrated on compact momentum tests.
Its boundary value is then compared with the large-height polynomial bound.
Exponential decay on a strict negative half-space forces that boundary to
annihilate the test. Compact-height bounds alone would not give this result.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Complex Filter Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIFullTimeStageVladimirovGrowthData

variable {d k : Nat} [NeZero d]
variable {A : OSIITimeContinuationStage d k}

private def positiveFrequencyRayCLM
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) (t : Real) :
    SchwartzMap (Fin k -> Real) Complex →L[Complex] Complex :=
  if ht : 0 < t then
    G.timeFrequencySliceCLM chi (t • eta)
      (osiiTimePositiveCone_isCone k eta heta t ht)
  else 0

private theorem positiveFrequencyRayCLM_apply
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    {t : Real} (ht : 0 < t) (psi : SchwartzMap (Fin k -> Real) Complex) :
    positiveFrequencyRayCLM G eta heta chi t psi =
      osiiFullTimeFrequencyPairing A eta t psi chi := by
  rw [positiveFrequencyRayCLM, dif_pos ht]
  exact G.timeFrequencySliceCLM_smul_apply chi eta heta t ht psi

private theorem hasDerivAt_positiveFrequencyRayCLM
    (G : OSIIFullTimeStageVladimirovGrowthData A) [NeZero k]
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (t : Real) (ht : 0 < t) (psi : SchwartzMap (Fin k -> Real) Complex) :
    HasDerivAt (fun u => positiveFrequencyRayCLM G eta heta chi u psi)
      (-positiveFrequencyRayCLM G eta heta chi t
        (SchwartzMap.smulLeftCLM Complex (osiiTimeMomentumLinearForm eta) psi)) t := by
  rw [positiveFrequencyRayCLM_apply G eta heta chi ht,
    ← osiiTimeMomentumMultiplier_eq_smulLeftCLM]
  apply (G.hasDerivAt_positiveFrequencyPairing eta heta t ht psi chi
    ).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with u hu
  exact positiveFrequencyRayCLM_apply G eta heta chi hu psi

/-- The correctly signed integrating factor gives a constant tested pairing
at every positive height. -/
theorem hasDerivAt_positiveFrequencyPairing_compactExponential
    (G : OSIIFullTimeStageVladimirovGrowthData A) [NeZero k]
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (psi : SchwartzMap (Fin k -> Real) Complex)
    (hpsi : HasCompactSupport (psi : (Fin k -> Real) -> Complex))
    (t : Real) (ht : 0 < t) :
    HasDerivAt (fun u => osiiFullTimeFrequencyPairing A eta u
      (OSIIChapterVI.compactExponentialTest (osiiTimeMomentumLinearForm eta)
        psi hpsi u) chi) 0 t := by
  have h := OSIIChapterVI.hasDerivAt_compactExponential_pairing
    (positiveFrequencyRayCLM G eta heta chi) (osiiTimeMomentumLinearForm eta)
    psi hpsi t (hasDerivAt_positiveFrequencyRayCLM G eta heta chi t ht)
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with u hu
  exact (positiveFrequencyRayCLM_apply G eta heta chi hu _).symm

/-- The integrating-factor constant is exactly the already constructed native
boundary, not a newly selected distribution. -/
theorem positiveFrequencyPairing_compactExponential_eq_boundary
    (G : OSIIFullTimeStageVladimirovGrowthData A) [NeZero k]
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (psi : SchwartzMap (Fin k -> Real) Complex)
    (hpsi : HasCompactSupport (psi : (Fin k -> Real) -> Complex))
    (t : Real) (ht : 0 < t) :
    osiiFullTimeFrequencyPairing A eta t
      (OSIIChapterVI.compactExponentialTest (osiiTimeMomentumLinearForm eta)
        psi hpsi t) chi =
      ((G.timeBoundary chi).comp physicsFourierFlatInvCLM) psi := by
  let L := osiiTimeMomentumLinearForm eta
  let E := OSIIChapterVI.compactExponentialTest L psi hpsi
  let P := positiveFrequencyRayCLM G eta heta chi
  let B := (G.timeBoundary chi).comp physicsFourierFlatInvCLM
  let F : Real -> Complex := fun u => osiiFullTimeFrequencyPairing A eta u (E u) chi
  have hderiv : forall u : Real, 0 < u -> HasDerivAt F 0 u :=
    G.hasDerivAt_positiveFrequencyPairing_compactExponential eta heta chi psi hpsi
  have hconst : forall u : Real, 0 < u -> F u = F t := by
    intro u hu
    exact isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (0 : Real)).isPreconnected
      (fun v hv => (hderiv v hv).differentiableAt.differentiableWithinAt)
      (fun v hv => (hderiv v hv).deriv) hu ht
  have hweak : forall phi : SchwartzMap (Fin k -> Real) Complex,
      Tendsto (fun u => ((P u).restrictScalars Real) phi)
        (nhdsWithin 0 (Ioi 0)) (nhds ((B.restrictScalars Real) phi)) := by
    intro phi
    apply (G.tendsto_positiveFrequencyPairing eta heta phi chi).congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact (positiveFrequencyRayCLM_apply G eta heta chi hu phi).symm
  have hsource : Tendsto E (nhdsWithin 0 (Ioi 0)) (nhds psi) := by
    simpa only [OSIIChapterVI.compactExponentialTest_zero] using
      ((OSIIChapterVI.continuous_compactExponentialTest L psi hpsi).tendsto 0
        ).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : Real)))
  have hlimit : Tendsto F (nhdsWithin 0 (Ioi 0)) (nhds (B psi)) := by
    have h := SchwartzMap.tempered_apply_tendsto_of_tendsto_filter hweak hsource
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact positiveFrequencyRayCLM_apply G eta heta chi hu (E u)
  have hconstant : Tendsto F (nhdsWithin 0 (Ioi 0)) (nhds (F t)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact (hconst u hu).symm
  exact tendsto_nhds_unique hconstant hlimit

/-- On a compact negative-energy test, the global polynomial slice bound is
dominated by the integrating factor's exponential decay. -/
theorem tendsto_positiveFrequencyPairing_compactExponential_atTop
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (psi : SchwartzMap (Fin k -> Real) Complex)
    (hpsi : HasCompactSupport (psi : (Fin k -> Real) -> Complex))
    {c : Real} (hc : 0 < c)
    (hsupport : forall p, p ∈ tsupport (psi : (Fin k -> Real) -> Complex) ->
      (∑ j : Fin k, eta j * p j) <= -c) :
    Tendsto (fun t => osiiFullTimeFrequencyPairing A eta t
      (OSIIChapterVI.compactExponentialTest (osiiTimeMomentumLinearForm eta)
        psi hpsi t) chi) atTop (nhds 0) := by
  obtain ⟨s, C, hC, hbound⟩ :=
    G.exists_positiveFrequencyPairing_largeHeight_bound eta heta chi
  have hsupport' : forall p,
      p ∈ tsupport (psi : (Fin k -> Real) -> Complex) ->
      (osiiTimeMomentumLinearForm eta p).re <= -c := by
    simpa only [osiiTimeMomentumLinearForm_re] using hsupport
  have hlimit :=
    (OSIIChapterVI.tendsto_pow_mul_finsetSeminorm_compactExponentialTest
      (osiiTimeMomentumLinearForm eta) psi hpsi hc hsupport' s G.polynomialDegree
      ).const_mul C
  simp only [mul_zero] at hlimit
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hlimit
  filter_upwards [eventually_ge_atTop (1 : Real)] with t ht
  simpa only [mul_assoc] using hbound t ht
    (OSIIChapterVI.compactExponentialTest (osiiTimeMomentumLinearForm eta) psi hpsi t)

/-- The native temporal frequency boundary annihilates every compact test
separated from positive energy by an interior time direction. -/
theorem timeBoundary_fourier_eq_zero_of_compact_negative
    (G : OSIIFullTimeStageVladimirovGrowthData A) [NeZero k]
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (psi : SchwartzMap (Fin k -> Real) Complex)
    (hpsi : HasCompactSupport (psi : (Fin k -> Real) -> Complex))
    {c : Real} (hc : 0 < c)
    (hsupport : forall p, p ∈ tsupport (psi : (Fin k -> Real) -> Complex) ->
      (∑ j : Fin k, eta j * p j) <= -c) :
    ((G.timeBoundary chi).comp physicsFourierFlatInvCLM) psi = 0 := by
  have hlimit := G.tendsto_positiveFrequencyPairing_compactExponential_atTop
    eta heta chi psi hpsi hc hsupport
  have hconstant : Tendsto
      (fun _ : Real => ((G.timeBoundary chi).comp physicsFourierFlatInvCLM) psi)
      atTop (nhds 0) := by
    apply hlimit.congr'
    filter_upwards [eventually_ge_atTop (1 : Real)] with t ht
    exact G.positiveFrequencyPairing_compactExponential_eq_boundary eta heta chi
      psi hpsi t (zero_lt_one.trans_le ht)
  exact tendsto_nhds_unique tendsto_const_nhds hconstant

/-- Radial cutoff density removes compact support while preserving one strict
negative-energy half-space. -/
theorem timeBoundary_fourier_isVanishingOn_negativeHalfspace
    (G : OSIIFullTimeStageVladimirovGrowthData A) [NeZero k]
    (eta : Fin k -> Real) (heta : eta ∈ osiiTimePositiveCone k)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    {c : Real} (hc : 0 < c) :
    Distribution.IsVanishingOn ((G.timeBoundary chi).comp physicsFourierFlatInvCLM)
      {p : Fin k -> Real | (∑ j : Fin k, eta j * p j) < -c} := by
  apply osiiSchwartzDistribution_isVanishingOn_of_compact
  intro psi hpsi hsupport
  exact G.timeBoundary_fourier_eq_zero_of_compact_negative eta heta chi psi hpsi hc
    (fun p hp => (hsupport hp).le)

/-- Every point outside the dual time cone has a neighborhood annihilated by
the native frequency boundary. -/
theorem dsupport_timeBoundary_fourier_subset_dualCone
    (G : OSIIFullTimeStageVladimirovGrowthData A) [NeZero k]
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    Distribution.dsupport ((G.timeBoundary chi).comp physicsFourierFlatInvCLM) ⊆
      DualConeFlat (osiiTimePositiveCone k) := by
  intro p hp
  by_contra hdual
  obtain ⟨eta, heta, hnegative⟩ := exists_neg_pairing_of_not_mem_dualConeFlat hdual
  let c : Real := -(∑ j : Fin k, eta j * p j) / 2
  have hc : 0 < c := by dsimp [c]; linarith
  let U : Set (Fin k -> Real) :=
    {q | (∑ j : Fin k, eta j * q j) < -c}
  have hU : IsOpen U := by
    exact isOpen_lt (by fun_prop) continuous_const
  have hpU : p ∈ U := by dsimp [U, c]; linarith
  have hvan : Distribution.IsVanishingOn
      ((G.timeBoundary chi).comp physicsFourierFlatInvCLM) U :=
    G.timeBoundary_fourier_isVanishingOn_negativeHalfspace eta heta chi hc
  exact ((Distribution.notMem_dsupport_iff
    (f := (G.timeBoundary chi).comp physicsFourierFlatInvCLM) p).mpr
      ⟨U, hvan, hU, hpU⟩) hp

/-- Global regulated growth proves the literal all-Schwartz positive-spectrum
predicate for the actual time boundary, at every arity. This proof invokes
neither legacy boundary-to-spectrum axiom. -/
theorem timeBoundary_positiveFourierSupport
    (G : OSIIFullTimeStageVladimirovGrowthData A)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    HasFourierSupportInDualCone (osiiTimePositiveCone k)
      ((G.timeBoundary chi).comp physicsFourierFlatInvCLM) := by
  by_cases hk : k = 0
  · subst k
    intro psi hpsi
    have hzero : psi = 0 := by
      ext p
      by_contra hp
      exact hpsi p (Function.mem_support.mpr hp) (by intro eta heta; simp)
    simp only [hzero, map_zero]
  · letI : NeZero k := ⟨hk⟩
    apply (hasFourierSupportInDualCone_osiiTimePositiveCone_iff_isVanishingOn _).mpr
    apply (osiiSchwartzDistribution_isVanishingOn_compl_dsupport _).mono
    apply Set.compl_subset_compl.mpr
    rw [← dualConeFlat_osiiTimePositiveCone k]
    exact G.dsupport_timeBoundary_fourier_subset_dualCone chi

end OSIIFullTimeStageVladimirovGrowthData
end OSReconstruction
