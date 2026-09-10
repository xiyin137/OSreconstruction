import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVITestedWard
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIGrowthBoundaryHandoff

/-!
# The signed temporal Ward calculation on a Wick slice

The actual time convention is `z = y - i*x`. A real-time derivative of its
scalar pairing is therefore `-i` times the complex-time derivative.
Compact temporal tests suffice for integration by parts at this stage.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical LineDeriv

set_option backward.isDefEq.respectTransparency false

namespace OSReconstruction
namespace OSIIChapterVI

variable {d k : Nat} {A : OSIITimeContinuationStage d k}

private def wickTimeLinearPartCLM (k : Nat) :
    (Fin k -> Real) →L[Real] OSIITimeGapSpace k :=
  ContinuousLinearMap.pi fun j =>
    ((-I) • Complex.ofRealCLM).comp (ContinuousLinearMap.proj j)

private theorem wickTimeLinearPartCLM_single (j : Fin k) :
    wickTimeLinearPartCLM k (Pi.single j (1 : Real)) =
      (-I) • (Pi.single j (1 : Complex) : OSIITimeGapSpace k) := by
  ext i
  by_cases h : i = j <;> simp [wickTimeLinearPartCLM, h]

private theorem wickTimeApproach_hasFDerivAt
    (y x : Fin k -> Real) :
    HasFDerivAt (fun t => osiiMinkowskiTimeApproach y t 1)
      (wickTimeLinearPartCLM k) x := by
  have hfun : (fun t => osiiMinkowskiTimeApproach y t 1) =
      fun t => osiiPositiveRealTimeEmbed y + wickTimeLinearPartCLM k t := by
    funext t
    ext j
    simp [osiiMinkowskiTimeApproach, osiiPositiveRealTimeEmbed,
      wickTimeLinearPartCLM, mul_comm, sub_eq_add_neg]
  rw [hfun]
  exact (wickTimeLinearPartCLM k).hasFDerivAt.const_add _

theorem continuous_wickRestriction
    (hfull : A.carrier = osiiTimeRightHalfPlane k)
    {F : OSIITimeGapSpace k -> Complex} (hF : ContinuousOn F A.carrier)
    (y : Fin k -> Real) (hy : y ∈ osiiTimePositiveCone k) :
    Continuous (fun x => F (osiiMinkowskiTimeApproach y x 1)) := by
  apply continuousOn_univ.mp
  apply hF.comp
    (show Continuous (fun x => osiiMinkowskiTimeApproach y x 1) from
      by unfold osiiMinkowskiTimeApproach; fun_prop).continuousOn
  intro x _
  rw [hfull]
  exact osiiMinkowskiTimeApproach_mem hy zero_lt_one

private theorem wickTrace_hasFDerivAt
    (hfull : A.carrier = osiiTimeRightHalfPlane k)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (y : Fin k -> Real) (hy : y ∈ osiiTimePositiveCone k) (x : Fin k -> Real) :
    HasFDerivAt (fun t => A.distribution (osiiMinkowskiTimeApproach y t 1) chi)
      (((fderiv Complex (fun z => A.distribution z chi)
        (osiiMinkowskiTimeApproach y x 1)).restrictScalars Real).comp
          (wickTimeLinearPartCLM k)) x := by
  have hz : osiiMinkowskiTimeApproach y x 1 ∈ A.carrier := by
    rw [hfull]
    exact osiiMinkowskiTimeApproach_mem hy zero_lt_one
  exact (((A.weaklyHolomorphic chi _ hz).differentiableAt
    (A.carrier_open.mem_nhds hz)).hasFDerivAt.restrictScalars Real).comp x
      (wickTimeApproach_hasFDerivAt y x)

theorem wickTrace_fderiv_apply
    (hfull : A.carrier = osiiTimeRightHalfPlane k)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (y : Fin k -> Real) (hy : y ∈ osiiTimePositiveCone k)
    (j : Fin k) (x : Fin k -> Real) :
    fderiv Real (fun t => A.distribution (osiiMinkowskiTimeApproach y t 1) chi) x
        (Pi.single j (1 : Real)) =
      (-I) * timePairingPartial A chi j (osiiMinkowskiTimeApproach y x 1) := by
  rw [(wickTrace_hasFDerivAt hfull chi y hy x).fderiv]
  change fderiv Complex (fun z => A.distribution z chi)
    (osiiMinkowskiTimeApproach y x 1) (wickTimeLinearPartCLM k (Pi.single j (1 : Real))) = _
  rw [wickTimeLinearPartCLM_single, map_smul]
  rfl

/-- The compact temporal integration-by-parts formula with the actual
`y - i*x` convention. Spatial tests are arbitrary Schwartz functions. -/
theorem integral_wickTrace_mul_lineDeriv
    (hfull : A.carrier = osiiTimeRightHalfPlane k)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (y : Fin k -> Real) (hy : y ∈ osiiTimePositiveCone k) (j : Fin k)
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (hphi : HasCompactSupport (phi : (Fin k -> Real) -> Complex)) :
    (∫ x, A.distribution (osiiMinkowskiTimeApproach y x 1) chi *
        (∂_{(Pi.single j (1 : Real) : Fin k -> Real)} phi) x) =
      I * (∫ x, timePairingPartial A chi j (osiiMinkowskiTimeApproach y x 1) * phi x) := by
  let f := fun x => A.distribution (osiiMinkowskiTimeApproach y x 1) chi
  let v : Fin k -> Real := Pi.single j 1
  have hfc : Continuous f :=
    continuous_wickRestriction hfull (A.weaklyHolomorphic chi).continuousOn y hy
  have hdc := continuous_wickRestriction hfull
    (differentiableOn_timePairingPartial A chi j).continuousOn y hy
  have hsource : SCV.SupportsInOpen (phi : (Fin k -> Real) -> Complex) Set.univ :=
    ⟨hphi, Set.subset_univ _⟩
  have hdsource : SCV.SupportsInOpen
      ((∂_{v} phi : SchwartzMap (Fin k -> Real) Complex) :
        (Fin k -> Real) -> Complex) Set.univ :=
    ⟨hphi.isCompact.of_isClosed_subset (isClosed_tsupport _)
      (SchwartzMap.tsupport_lineDerivOp_subset v phi), Set.subset_univ _⟩
  have hder (x : Fin k -> Real) : fderiv Real f x v =
      (-I) * timePairingPartial A chi j (osiiMinkowskiTimeApproach y x 1) :=
    wickTrace_fderiv_apply hfull chi y hy j x
  have hf'g : Integrable (fun x => fderiv Real f x v * phi x) := by
    simp_rw [hder]
    exact SCV.integrable_continuousOn_mul_schwartz_of_supportsInOpen
      isOpen_univ (continuous_const.mul hdc).continuousOn hsource
  have hfg' : Integrable (fun x => f x * fderiv Real phi x v) :=
    SCV.integrable_continuousOn_mul_schwartz_of_supportsInOpen
      isOpen_univ hfc.continuousOn hdsource
  have hfg : Integrable (fun x => f x * phi x) :=
    SCV.integrable_continuousOn_mul_schwartz_of_supportsInOpen
      isOpen_univ hfc.continuousOn hsource
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hf'g hfg' hfg
    (fun x _ => (wickTrace_hasFDerivAt hfull chi y hy x).differentiableAt)
    (fun x _ => phi.differentiableAt)
  calc
    _ = -(∫ x, fderiv Real f x v * phi x) := hibp
    _ = -(∫ x, (-I) *
        (timePairingPartial A chi j (osiiMinkowskiTimeApproach y x 1) * phi x)) := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change fderiv Real f x v * phi x =
          (-I) * (timePairingPartial A chi j (osiiMinkowskiTimeApproach y x 1) * phi x)
        rw [hder]
        ring
    _ = _ := by rw [integral_const_mul]; ring

end OSIIChapterVI
end OSReconstruction
