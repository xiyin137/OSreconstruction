/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVICanonicalFrequencyTransport
import OSReconstruction.Wightman.Reconstruction.WickRotation.ReducedSpectralGeometry















noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction

variable {d k : Nat} [NeZero d]

/-- A genuine covariance transport converts the already established temporal
vanishing certificate into one Lorentz-tilted halfspace certificate.  The
equivalence is the actual momentum-side inverse-transpose action; its
construction and invariance remain independent Ward obligations. -/
theorem osiiCanonicalFrequency_isVanishingOn_halfspace_of_covariant_transport
    {T : SchwartzMap (Fin (k * (d + 1)) -> Real) Complex →L[Complex] Complex}
    (hTemporal : Distribution.IsVanishingOn T
      (osiiCanonicalFrequencyTemporalCylinder d k)ᶜ)
    (j : Fin k) (y : Fin (d + 1) -> Real)
    (e : (Fin (k * (d + 1)) -> Real) ≃L[Real]
      (Fin (k * (d + 1)) -> Real))
    (hinvariant : ∀ phi : SchwartzMap (Fin (k * (d + 1)) -> Real) Complex,
      T (SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm phi) =
        T phi)
    (htransport : ∀ p,
      p ∈ (osiiCanonicalFrequencyForwardPairingHalfspace d k j y)ᶜ ->
        e p ∈ (osiiCanonicalFrequencyTemporalCylinder d k)ᶜ) :
    Distribution.IsVanishingOn T
      (osiiCanonicalFrequencyForwardPairingHalfspace d k j y)ᶜ := by
  intro phi hphi
  let psi := SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm phi
  have hpsi :
      tsupport (psi : (Fin (k * (d + 1)) -> Real) -> Complex) ⊆
        (osiiCanonicalFrequencyTemporalCylinder d k)ᶜ := by
    intro p hp
    have hp' :
        e.symm p ∈ tsupport
          (phi : (Fin (k * (d + 1)) -> Real) -> Complex) := by
      have hpre := tsupport_comp_subset_preimage
        (phi : (Fin (k * (d + 1)) -> Real) -> Complex) e.symm.continuous
      simpa [psi, SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
        hpre hp
    simpa using htransport (e.symm p) (hphi hp')
  exact (hinvariant phi).symm.trans (hTemporal psi hpsi)

/-- The exact momentum-side Lorentz handoff needed to saturate temporal
positive energy.  Its equivalences must be the actual inverse-transpose
Lorentz actions, with invariance supplied independently by the Ward proof. -/
def OSIICanonicalFrequencyLorentzTransport
    (d k : Nat) [NeZero d]
    (T : SchwartzMap (Fin (k * (d + 1)) -> Real) Complex →L[Complex] Complex) :
    Prop :=
  ∀ (j : Fin k) (y : Fin (d + 1) -> Real),
    InOpenForwardCone d y ->
      ∃ e : (Fin (k * (d + 1)) -> Real) ≃L[Real]
        (Fin (k * (d + 1)) -> Real),
        (∀ phi : SchwartzMap (Fin (k * (d + 1)) -> Real) Complex,
          T (SchwartzMap.compCLMOfContinuousLinearEquiv Complex e.symm phi) =
            T phi) ∧
        ∀ p,
          p ∈ (osiiCanonicalFrequencyForwardPairingHalfspace d k j y)ᶜ ->
            e p ∈ (osiiCanonicalFrequencyTemporalCylinder d k)ᶜ

namespace OSIIFullTimeStageVladimirovGrowthData

end OSIIFullTimeStageVladimirovGrowthData

end OSReconstruction
