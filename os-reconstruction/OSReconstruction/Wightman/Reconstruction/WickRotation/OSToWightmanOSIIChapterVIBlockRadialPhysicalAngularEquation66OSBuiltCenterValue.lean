import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPhysicalAngularEquation66E0Polynomial

/-!
# Canonical OS-built equation-(6.6) center value

The quantitative equation-(6.6) construction only needs the explicit first
multi-gap carrier.  This module fixes that carrier, chooses its local-Weyl
density, and exposes the resulting center value as a scalar depending only on
the OS data, radius, and physical center.

No selected reduced BVT witness enters this definition.  The exported bound
is therefore the non-circular pointwise `E0'` input for the real-edge density
handoff.
-/

noncomputable section

open Complex Metric Set Topology
open scoped Classical

namespace OSReconstruction

open OSIIStep4FullSchwartzAngularContinuationData

/-- The explicit synchronized first-carrier continuation used by the
quantitative equation-(6.6) route. -/
noncomputable def osiiEquation66FirstAngularData
    (d k : Nat) [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {rho : Real} (hrho : 0 < rho)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      rho <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    OSIIStep4FullSchwartzAngularContinuationData
      (hcenter := hcenter)
      (osiiEquation66QuantitativeSynchronizedData
        d k hrho center hcenter) OS lgc :=
  (osiiEquation66QuantitativeSynchronizedData
    d k hrho center hcenter).toFirstFullSchwartzAngularContinuationData
      OS lgc

/-- Canonical quantitative local-Weyl density on the explicit first carrier. -/
noncomputable def osiiEquation66FirstLocalWeylData
    (d k : Nat) [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {rho : Real} (hrho : 0 < rho) (hrho_le : rho <= 16)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      rho <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    OSIIEquation66QuantitativeLocalWeylDensityData
      (osiiEquation66FirstAngularData
        d k OS lgc hrho center hcenter) :=
  Classical.choice
    (OSIIStep4FullSchwartzAngularContinuationData.nonempty_equation66QuantitativeLocalWeylDensityData
      (rho := rho) hrho_le
      (osiiEquation66FirstAngularData
        d k OS lgc hrho center hcenter))

/-- The scalar center value recovered by the non-circular equation-(6.6)
density construction. -/
noncomputable def osiiEquation66OSBuiltCenterValue
    (d k : Nat) [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {rho : Real} (hrho : 0 < rho) (hrho_le : rho <= 16)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      rho <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) : Complex :=
  (osiiEquation66FirstLocalWeylData
    d k OS lgc hrho hrho_le center hcenter).data.density
      (osiiStep4ComplexOfRealImag
        (osiiStep4MultiGapXiHatCenter d k center) 0)

/-- Pointwise Chapter VI.1 `E0'` bound for the canonical OS-built center
value. -/
theorem osiiEquation66OSBuiltCenterValue_norm_le_E0Polynomial
    (d k : Nat) [NeZero d] [NeZero k]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (G : OSIIStep4MultiGapCenteredWindowScaleBoundData d k OS lgc)
    {rho : Real} (hrho : 0 < rho) (hrho_le : rho <= 16)
    (center : Fin (k * (d + 1)) -> Real)
    (hcenter : forall i : Fin k,
      rho <= center (finProdFinEquiv (i, (0 : Fin (d + 1))))) :
    ‖osiiEquation66OSBuiltCenterValue
        d k OS lgc hrho hrho_le center hcenter‖ <=
      OSIIStep4FullSchwartzAngularContinuationData.equation66E0PolynomialConstant G *
        (16 / rho) ^ (2 * G.scaleDegree) *
        (1 + norm center) ^ (G.scaleDegree + G.growthDegree) := by
  unfold osiiEquation66OSBuiltCenterValue
  exact
    (osiiEquation66FirstLocalWeylData
      d k OS lgc hrho hrho_le center hcenter
    ).norm_density_center_le_E0Polynomial G hrho_le rfl

end OSReconstruction
