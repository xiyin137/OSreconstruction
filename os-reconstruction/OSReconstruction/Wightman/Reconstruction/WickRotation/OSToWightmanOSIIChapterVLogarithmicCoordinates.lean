/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVLogarithmicArgumentDomains
import OSReconstruction.SCV.TubeDomainExtension



















noncomputable section

open Complex Set Topology
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV

/-- Coordinatewise exponential from additive logarithmic coordinates to
physical complex time gaps. -/
def osiiLogExp {k : ℕ} (z : Fin k → ℂ) : OSIITimeGapSpace k :=
  fun i => Complex.exp (z i)

/-- Coordinatewise principal logarithm on physical complex time gaps. -/
def osiiPrincipalLog {k : ℕ} (ζ : OSIITimeGapSpace k) : Fin k → ℂ :=
  fun i => Complex.log (ζ i)

/-- The strict coordinatewise principal strip mapping to the product right
half-plane under exponentiation. -/
def osiiOpenArgumentStrip (k : ℕ) : Set (Fin k → ℝ) :=
  {y | ∀ i, |y i| < Real.pi / 2}

/-- The part of an abstract argument base visible in the physical right
half-plane. -/
def osiiPhysicalLogarithmicBase {k : ℕ}
    (base : Set (Fin k → ℝ)) : Set (Fin k → ℝ) :=
  base ∩ osiiOpenArgumentStrip k

/-- The additive logarithmic tube associated to a physical argument base. -/
def osiiLogarithmicTube {k : ℕ}
    (base : Set (Fin k → ℝ)) : Set (Fin k → ℂ) :=
  SCV.TubeDomain (osiiPhysicalLogarithmicBase base)

theorem isOpen_osiiOpenArgumentStrip (k : ℕ) :
    IsOpen (osiiOpenArgumentStrip k) := by
  simp only [osiiOpenArgumentStrip, Set.setOf_forall]
  exact isOpen_iInter_of_finite fun i : Fin k =>
    isOpen_lt (continuous_abs.comp (continuous_apply i)) continuous_const

/-- An open argument base gives an open additive logarithmic tube after
restriction to the physical principal strip. -/
theorem isOpen_osiiLogarithmicTube
    {k : ℕ} {base : Set (Fin k → ℝ)}
    (hbase : IsOpen base) :
    IsOpen (osiiLogarithmicTube base) :=
  SCV.tubeDomain_isOpen
    (hbase.inter (isOpen_osiiOpenArgumentStrip k))

theorem osiiLogExp_differentiable {k : ℕ} :
    Differentiable ℂ
      (osiiLogExp : (Fin k → ℂ) → OSIITimeGapSpace k) := by
  rw [differentiable_pi]
  intro i
  exact Complex.differentiable_exp.comp (differentiable_apply i)

theorem arg_exp_eq_im_of_mem_openArgumentStrip
    {z : ℂ} (hz : |z.im| < Real.pi / 2) :
    (Complex.exp z).arg = z.im := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hlower : -Real.pi < z.im := by
    have hz' := (abs_lt.mp hz).1
    linarith
  have hupper : z.im ≤ Real.pi := by
    have hz' := (abs_lt.mp hz).2
    linarith
  have hlog := Complex.log_exp hlower hupper
  have him := congrArg Complex.im hlog
  simpa [Complex.log_im] using him

theorem osiiLogExp_mem_rightHalfPlane
    {k : ℕ} {z : Fin k → ℂ}
    (hz : (fun i => (z i).im) ∈ osiiOpenArgumentStrip k) :
    osiiLogExp z ∈ osiiTimeRightHalfPlane k := by
  intro i
  have hstrip := abs_lt.mp (hz i)
  have hcos : 0 < Real.cos (z i).im :=
    Real.cos_pos_of_mem_Ioo hstrip
  have hexp : 0 < Real.exp (z i).re := Real.exp_pos _
  simpa [osiiLogExp, Complex.exp_re] using mul_pos hexp hcos

theorem osiiTimeArgumentVector_logExp
    {k : ℕ} {z : Fin k → ℂ}
    (hz : (fun i => (z i).im) ∈ osiiOpenArgumentStrip k) :
    osiiTimeArgumentVector (osiiLogExp z) =
      fun i => (z i).im := by
  funext i
  exact arg_exp_eq_im_of_mem_openArgumentStrip (hz i)

/-- Exponentiation sends the physical logarithmic tube into the corresponding
principal-argument carrier. -/
theorem osiiLogExp_mem_argumentCarrier
    {k : ℕ} {base : Set (Fin k → ℝ)}
    {z : Fin k → ℂ}
    (hz : z ∈ osiiLogarithmicTube base) :
    osiiLogExp z ∈ osiiTimeArgumentCarrier base := by
  have hbase : (fun i => (z i).im) ∈ base := hz.1
  have hstrip :
      (fun i => (z i).im) ∈ osiiOpenArgumentStrip k := hz.2
  exact
    ⟨osiiLogExp_mem_rightHalfPlane hstrip,
      osiiTimeArgumentVector_logExp hstrip ▸ hbase⟩

theorem osiiPrincipalLog_im
    {k : ℕ} (ζ : OSIITimeGapSpace k) :
    (fun i => (osiiPrincipalLog ζ i).im) =
      osiiTimeArgumentVector ζ := by
  funext i
  exact Complex.log_im (ζ i)

/-- Principal logarithm sends the physical argument carrier back into its
strict logarithmic tube. -/
theorem osiiPrincipalLog_mem_logarithmicTube
    {k : ℕ} {base : Set (Fin k → ℝ)}
    {ζ : OSIITimeGapSpace k}
    (hζ : ζ ∈ osiiTimeArgumentCarrier base) :
    osiiPrincipalLog ζ ∈ osiiLogarithmicTube base := by
  rw [osiiLogarithmicTube, SCV.TubeDomain,
    osiiPhysicalLogarithmicBase]
  refine ⟨?_, ?_⟩
  · simpa [osiiPrincipalLog_im] using hζ.2
  · intro i
    change |(Complex.log (ζ i)).im| < Real.pi / 2
    rw [Complex.log_im]
    exact
      Complex.abs_arg_lt_pi_div_two_iff.mpr
        (Or.inl (hζ.1 i))

theorem osiiLogExp_principalLog
    {k : ℕ} {ζ : OSIITimeGapSpace k}
    (hζ : ζ ∈ osiiTimeRightHalfPlane k) :
    osiiLogExp (osiiPrincipalLog ζ) = ζ := by
  funext i
  apply Complex.exp_log
  intro hzero
  simpa [hzero] using hζ i

/-- The open logarithmic-coordinate preimage of a physical continuation-stage
carrier. -/
def osiiLogarithmicStageCarrier
    {d k : ℕ}
    (A : OSIITimeContinuationStage d k) :
    Set (Fin k → ℂ) :=
  osiiLogExp ⁻¹' A.carrier

theorem isOpen_osiiLogarithmicStageCarrier
    {d k : ℕ}
    (A : OSIITimeContinuationStage d k) :
    IsOpen (osiiLogarithmicStageCarrier A) :=
  A.carrier_open.preimage osiiLogExp_differentiable.continuous

/-- Pull a physical continuation stage back through coordinatewise
exponentiation to the open preimage of its complete carrier. -/
noncomputable def logarithmicPullbackStage
    {d k : ℕ}
    (A : OSIITimeContinuationStage d k) :
    OSIITimeContinuationStage d k where
  carrier := osiiLogarithmicStageCarrier A
  carrier_open := isOpen_osiiLogarithmicStageCarrier A
  distribution := fun z => A.distribution (osiiLogExp z)
  weaklyHolomorphic := by
    intro χ
    simpa [Function.comp_def] using
      (A.weaklyHolomorphic χ).comp
        osiiLogExp_differentiable.differentiableOn
        (fun _z hz => hz)

@[simp] theorem logarithmicPullbackStage_carrier
    {d k : ℕ}
    (A : OSIITimeContinuationStage d k) :
    (logarithmicPullbackStage A).carrier =
      osiiLogarithmicStageCarrier A :=
  rfl

@[simp] theorem logarithmicPullbackStage_distribution
    {d k : ℕ}
    (A : OSIITimeContinuationStage d k)
    (z : Fin k → ℂ) :
    (logarithmicPullbackStage A).distribution z =
      A.distribution (osiiLogExp z) :=
  rfl

/-- Realization of a physical argument carrier places its exact logarithmic
tube inside the open pullback of the physical stage. -/
theorem osiiLogarithmicTube_subset_pullbackStage
    {d k : ℕ}
    {A : OSIITimeContinuationStage d k}
    {base : Set (Fin k → ℝ)}
    (hcarrier :
      osiiTimeArgumentCarrier base ⊆ A.carrier) :
    osiiLogarithmicTube base ⊆
      (logarithmicPullbackStage A).carrier := by
  intro z hz
  exact hcarrier (osiiLogExp_mem_argumentCarrier hz)

end OSIIChapterV
end OSReconstruction
