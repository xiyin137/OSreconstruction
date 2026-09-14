import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEuclideanWardTimeEdge
import OSReconstruction.SCV.TotallyRealIdentity
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Tested Ward continuation on the actual time stage

Only temporal holomorphy is used. Spatial coordinates remain Schwartz
source variables throughout the real-edge integration by parts.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical LineDeriv

set_option backward.isDefEq.respectTransparency false

namespace OSReconstruction
namespace OSIIChapterVI

variable {d k : Nat}

/-- A temporal derivative of one scalar spatial pairing. -/
def timePairingPartial (A : OSIITimeContinuationStage d k)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) (j : Fin k)
    (z : OSIITimeGapSpace k) : Complex :=
  fderiv Complex (fun w => A.distribution w chi) z
    (Pi.single j (1 : Complex))

theorem differentiableOn_timePairingPartial (A : OSIITimeContinuationStage d k)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) (j : Fin k) :
    DifferentiableOn Complex (timePairingPartial A chi j) A.carrier := by
  exact ((A.weaklyHolomorphic chi).analyticOnNhd_of_finiteDimensional
    A.carrier_open).fderiv.differentiableOn.clm_apply (differentiableOn_const _)

/-- The tested Euclidean Ward defect, holomorphic only in the time gaps. -/
def timeWardDefect (A : OSIITimeContinuationStage d k) (a : Fin d)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (z : OSIITimeGapSpace k) : Complex :=
  ∑ j : Fin k,
    (timePairingPartial A (spatialCoordinateMultiplier j a chi) j z +
      z j * A.distribution z (∂_{EuclideanSpace.single (j, a) (1 : Real)} chi))

theorem differentiableOn_timeWardDefect (A : OSIITimeContinuationStage d k)
    (a : Fin d) (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    DifferentiableOn Complex (timeWardDefect A a chi) A.carrier := by
  apply DifferentiableOn.fun_sum
  intro j _
  exact (differentiableOn_timePairingPartial A _ j).add
    ((differentiable_apply j).differentiableOn.mul (A.weaklyHolomorphic _))

private def realTimeEmbedCLM (k : Nat) :
    (Fin k -> Real) →L[Real] OSIITimeGapSpace k :=
  ContinuousLinearMap.pi fun j =>
    Complex.ofRealCLM.comp (ContinuousLinearMap.proj j)

private theorem realTimeEmbedCLM_single (j : Fin k) :
    realTimeEmbedCLM k (Pi.single j (1 : Real)) = Pi.single j (1 : Complex) := by
  ext i
  by_cases h : i = j <;> simp [realTimeEmbedCLM, Pi.single_apply, h]

variable [NeZero d]
variable {OS : OsterwalderSchraderAxioms d} {A : OSIITimeContinuationStage d k}

open OSIIChapterV

private theorem realTrace_hasFDerivAt
    (H : HasCanonicalReducedCompactStageEdges OS A)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (t : Fin k -> Real) (ht : t ∈ section43TimeStrictPositiveRegion k) :
    HasFDerivAt (fun s => A.distribution (osiiPositiveRealTimeEmbed s) chi)
      (((fderiv Complex (fun z => A.distribution z chi)
        (osiiPositiveRealTimeEmbed t)).restrictScalars Real).comp
          (realTimeEmbedCLM k)) t := by
  have hz := H.positiveReal_mem_carrier t ht
  exact (((A.weaklyHolomorphic chi _ hz).differentiableAt
    (A.carrier_open.mem_nhds hz)).hasFDerivAt.restrictScalars Real).comp t
      (realTimeEmbedCLM k).hasFDerivAt

theorem realTrace_fderiv_apply
    (H : HasCanonicalReducedCompactStageEdges OS A)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) (j : Fin k)
    (t : Fin k -> Real) (ht : t ∈ section43TimeStrictPositiveRegion k) :
    fderiv Real (fun s => A.distribution (osiiPositiveRealTimeEmbed s) chi) t
        (Pi.single j (1 : Real)) =
      timePairingPartial A chi j (osiiPositiveRealTimeEmbed t) := by
  rw [(realTrace_hasFDerivAt H chi t ht).fderiv]
  change fderiv Complex (fun z => A.distribution z chi)
    (osiiPositiveRealTimeEmbed t) (realTimeEmbedCLM k (Pi.single j (1 : Real))) = _
  rw [realTimeEmbedCLM_single]
  rfl

/-- Local temporal integration by parts against the actual scalar stage
pairing. No boundary value or spectral assumption is used. -/
theorem integral_realTrace_mul_lineDeriv
    (H : HasCanonicalReducedCompactStageEdges OS A)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) (j : Fin k)
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (hphi : SCV.SupportsInOpen (phi : (Fin k -> Real) -> Complex)
      (section43TimeStrictPositiveRegion k)) :
    (∫ t, A.distribution (osiiPositiveRealTimeEmbed t) chi *
        (∂_{(Pi.single j (1 : Real) : Fin k -> Real)} phi) t) =
      -(∫ t, timePairingPartial A chi j (osiiPositiveRealTimeEmbed t) * phi t) := by
  let f := fun t => A.distribution (osiiPositiveRealTimeEmbed t) chi
  let v : Fin k -> Real := Pi.single j 1
  have hfc : ContinuousOn f (section43TimeStrictPositiveRegion k) :=
    (A.weaklyHolomorphic chi).continuousOn.comp
      continuous_osiiPositiveRealTimeEmbed.continuousOn
      (fun t ht => H.positiveReal_mem_carrier t ht)
  have hdc : ContinuousOn
      (fun t => timePairingPartial A chi j (osiiPositiveRealTimeEmbed t))
      (section43TimeStrictPositiveRegion k) :=
    (differentiableOn_timePairingPartial A chi j).continuousOn.comp
      continuous_osiiPositiveRealTimeEmbed.continuousOn
      (fun t ht => H.positiveReal_mem_carrier t ht)
  have heq : (fun t => fderiv Real f t v * phi t) =
      (fun t => timePairingPartial A chi j (osiiPositiveRealTimeEmbed t) * phi t) := by
    funext t
    by_cases ht : t ∈ tsupport (phi : (Fin k -> Real) -> Complex)
    · rw [realTrace_fderiv_apply H chi j t (hphi.2 ht)]
    · simp [image_eq_zero_of_notMem_tsupport ht]
  have hdphi : SCV.SupportsInOpen
      ((∂_{v} phi : SchwartzMap (Fin k -> Real) Complex) :
        (Fin k -> Real) -> Complex) (section43TimeStrictPositiveRegion k) :=
    ⟨hphi.1.isCompact.of_isClosed_subset (isClosed_tsupport _)
        (SchwartzMap.tsupport_lineDerivOp_subset v phi),
      (SchwartzMap.tsupport_lineDerivOp_subset v phi).trans hphi.2⟩
  have hf'g : Integrable (fun t => fderiv Real f t v * phi t) := by
    rw [heq]
    exact SCV.integrable_continuousOn_mul_schwartz_of_supportsInOpen
      (isOpen_section43TimeStrictPositiveRegion k) hdc hphi
  have hfg' : Integrable (fun t => f t * fderiv Real phi t v) :=
    SCV.integrable_continuousOn_mul_schwartz_of_supportsInOpen
      (isOpen_section43TimeStrictPositiveRegion k) hfc hdphi
  have hfg : Integrable (fun t => f t * phi t) :=
    SCV.integrable_continuousOn_mul_schwartz_of_supportsInOpen
      (isOpen_section43TimeStrictPositiveRegion k) hfc hphi
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hf'g hfg' hfg
    (fun t ht => (realTrace_hasFDerivAt H chi t (hphi.2 ht)).differentiableAt)
    (fun t _ => phi.differentiableAt)
  simpa only [heq, SchwartzMap.lineDerivOp_apply_eq_fderiv] using h

variable [NeZero k]

set_option maxHeartbeats 600000 in
/-- The weak original-E1 identity determines the continuous Ward defect
pointwise on the complete positive-real time chamber. -/
theorem timeWardDefect_positiveReal
    (H : HasCanonicalReducedCompactStageEdges OS A)
    (a : Fin d) (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (t : Fin k -> Real) (ht : t ∈ section43TimeStrictPositiveRegion k) :
    timeWardDefect A a chi (osiiPositiveRealTimeEmbed t) = 0 := by
  let U := section43TimeStrictPositiveRegion k
  have hU : IsOpen U := isOpen_section43TimeStrictPositiveRegion k
  have hmem : Set.MapsTo osiiPositiveRealTimeEmbed U A.carrier :=
    fun t ht => H.positiveReal_mem_carrier t ht
  have hcont : ContinuousOn
      (fun t => timeWardDefect A a chi (osiiPositiveRealTimeEmbed t)) U :=
    (differentiableOn_timeWardDefect A a chi).continuousOn.comp
      continuous_osiiPositiveRealTimeEmbed.continuousOn hmem
  have hzero : Set.EqOn
      (fun t => timeWardDefect A a chi (osiiPositiveRealTimeEmbed t))
      (fun _ => (0 : Complex)) U := by
    apply SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn
      hU hcont continuousOn_const
    intro phi hphi hsupport
    have hsource : SCV.SupportsInOpen (phi : (Fin k -> Real) -> Complex) U :=
      ⟨hphi, hsupport⟩
    let p (j : Fin k) (s : Fin k -> Real) :=
      timePairingPartial A (spatialCoordinateMultiplier j a chi) j
        (osiiPositiveRealTimeEmbed s)
    let q (j : Fin k) (s : Fin k -> Real) :=
      (s j : Complex) * A.distribution (osiiPositiveRealTimeEmbed s)
        (∂_{EuclideanSpace.single (j, a) (1 : Real)} chi)
    have hp (j : Fin k) : Integrable (fun s => p j s * phi s) :=
      SCV.integrable_continuousOn_mul_schwartz_of_supportsInOpen hU
        ((differentiableOn_timePairingPartial A _ j).continuousOn.comp
          continuous_osiiPositiveRealTimeEmbed.continuousOn hmem) hsource
    have hq (j : Fin k) : Integrable (fun s => q j s * phi s) :=
      SCV.integrable_continuousOn_mul_schwartz_of_supportsInOpen hU
        ((Complex.continuous_ofReal.comp (continuous_apply j)).continuousOn.mul
          ((A.weaklyHolomorphic _).continuousOn.comp
            continuous_osiiPositiveRealTimeEmbed.continuousOn hmem)) hsource
    have hweak := H.integral_euclideanWard a phi chi hsource
    have hpair (j : Fin k) :
        (∫ s, A.distribution (osiiPositiveRealTimeEmbed s)
          (∂_{EuclideanSpace.single (j, a) (1 : Real)} chi) *
          timeCoordinateMultiplier j phi s) = ∫ s, q j s * phi s := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun s => by
        simp only [timeCoordinateMultiplier_apply, q]
        ring
    have hibp (j : Fin k) := integral_realTrace_mul_lineDeriv H
      (spatialCoordinateMultiplier j a chi) j phi hsource
    simp_rw [hibp, hpair] at hweak
    have hsum : (∑ j : Fin k,
        ((∫ s, p j s * phi s) + (∫ s, q j s * phi s))) = 0 := by
      have heq : (∑ j : Fin k,
          (-(∫ s, p j s * phi s) - (∫ s, q j s * phi s))) =
          -(∑ j : Fin k, ((∫ s, p j s * phi s) + (∫ s, q j s * phi s))) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      change (∑ j : Fin k,
        (-(∫ s, p j s * phi s) - (∫ s, q j s * phi s))) = 0 at hweak
      rw [heq, neg_eq_zero] at hweak
      exact hweak
    calc
      _ = ∫ s, ∑ j : Fin k, (p j s * phi s + q j s * phi s) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun s => by
          simp only [timeWardDefect, osiiPositiveRealTimeEmbed, p, q,
            Finset.sum_mul, add_mul]
      _ = ∑ j : Fin k, ∫ s, (p j s * phi s + q j s * phi s) :=
        integral_finset_sum _ (fun j _ => (hp j).add (hq j))
      _ = ∑ j : Fin k, ((∫ s, p j s * phi s) + (∫ s, q j s * phi s)) := by
        apply Finset.sum_congr rfl
        intro j _
        exact integral_add (hp j) (hq j)
      _ = 0 := hsum
      _ = _ := by simp
  exact hzero ht

/-- Totally-real uniqueness continues the original Ward identity on any
connected time stage carrying the actual canonical Schwinger edges. -/
theorem timeWardDefect_eq_zero
    (H : HasCanonicalReducedCompactStageEdges OS A)
    (hconnected : IsConnected A.carrier)
    (a : Fin d) (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (z : OSIITimeGapSpace k) (hz : z ∈ A.carrier) :
    timeWardDefect A a chi z = 0 := by
  apply SCV.identity_theorem_totally_real A.carrier_open hconnected
    (differentiableOn_timeWardDefect A a chi)
    (isOpen_section43TimeStrictPositiveRegion k)
    (show (section43TimeStrictPositiveRegion k).Nonempty from
      ⟨fun _ => 1, by intro i; norm_num⟩)
    (fun t ht => H.positiveReal_mem_carrier t ht)
    (fun t ht => timeWardDefect_positiveReal H a chi t ht) z hz

end OSIIChapterVI
end OSReconstruction
