import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIForwardTubeEuclideanIdentification
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEuclideanWardSource
import OSReconstruction.Wightman.Reconstruction.WickRotation.SchwingerAxioms

/-!
# Euclidean covariance of the constructed physical tube

The exact compact-source Wick pairing transfers original E1 to the kernel.
Volume-preserving rotation and distributional uniqueness then give pointwise
covariance on the overlap of the two positive Euclidean chambers.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction

variable {d k : Nat} [NeZero d]

omit [NeZero d] in
/-- Proper Euclidean rotations intertwine the real Wick slice and the
corresponding complex Lorentz action. -/
theorem osiiWickRotateConfig_ofEuclidean
    (rot : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (hdet : rot.det = 1) (horth : rot.transpose * rot = 1)
    (q : NPointDomain d k) :
    (fun j => wickRotatePoint (rot.mulVec (q j))) =
      BHW.complexLorentzAction (ComplexLorentzGroup.ofEuclidean rot hdet horth)
        (fun j => wickRotatePoint (q j)) := by
  ext j mu
  exact wickRotatePoint_ofEuclidean rot hdet horth (q j) mu

namespace OSIIReducedForwardTubeBoundaryData

variable {OS : OsterwalderSchraderAxioms d} {stage : OSIITimeContinuationStage d k}
variable {W : SchwartzNPoint d k →L[Complex] Complex}

theorem wickIntegral_euclideanRotation_eq
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (realization : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H)
    (rot : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (hdet : rot.det = 1) (horth : rot.transpose * rot = 1)
    (phi : SchwartzNPoint d k) (hcompact : HasCompactSupport (phi : NPointDomain d k -> Complex))
    (hsupport : tsupport (phi : NPointDomain d k -> Complex) ⊆
      {q | q ∈ OSIIChapterV.initialReducedStrictPositiveGapRegion d k ∧
        (fun j => rot.mulVec (q j)) ∈ OSIIChapterV.initialReducedStrictPositiveGapRegion d k}) :
    (∫ q : NPointDomain d k, H.kernel (fun j => wickRotatePoint (rot.mulVec (q j))) * phi q) =
      ∫ q : NPointDomain d k, H.kernel (fun j => wickRotatePoint (q j)) * phi q := by
  by_cases hk : k = 0
  · subst k
    apply integral_congr_ae
    filter_upwards with q
    exact congrArg (fun z => H.kernel z * phi q) (Subsingleton.elim _ _)
  letI : NeZero k := ⟨hk⟩
  let e := osiiEuclideanRotateNPointCLE (n := k) rot horth
  let phiLF := OSIIChapterV.initialPhysicalSchwartzToTestFunction
    (OSIIChapterV.initialReducedStrictPositiveGapOpen d k) phi hcompact
    (fun q hq => (hsupport hq).1)
  have hrot_support : tsupport (fun q : NPointDomain d k =>
      phiLF (fun j => rot.transpose.mulVec (q j))) ⊆
        OSIIChapterV.initialReducedStrictPositiveGapRegion d k := by
    intro q hq
    have hpre : e q ∈ tsupport (phi : NPointDomain d k -> Complex) :=
      tsupport_comp_subset_preimage (phi : NPointDomain d k -> Complex) e.continuous hq
    have h := (hsupport hpre).2
    have hinv : (fun j => rot.mulVec (e q j)) = q := by
      ext j mu
      change rot.mulVec (rot.transpose.mulVec (q j)) mu = q j mu
      simp [Matrix.mulVec_mulVec, mul_eq_one_comm.mpr horth]
    rwa [hinv] at h
  let phiR := OSIIChapterV.initialPhysicalRotatePositiveTest rot horth phiLF hrot_support
  let chi := BHW.normalizedCutoffOfBump d
  have hcurrent := OSIIChapterV.initialPhysicalPositiveChamberCurrent_rotate_eq
    OS chi rot horth hdet phiLF hrot_support
  have hpair : (∫ q : NPointDomain d k,
      H.kernel (fun j => wickRotatePoint (q j)) * phi (e q)) =
      ∫ q : NPointDomain d k, H.kernel (fun j => wickRotatePoint (q j)) * phi q := by
    exact (H.wickIntegral_eq_positiveChamberCurrent Hstage realization chi phiR).trans
      (hcurrent.trans (H.wickIntegral_eq_positiveChamberCurrent Hstage realization chi phiLF).symm)
  let f := fun q : NPointDomain d k => H.kernel (fun j => wickRotatePoint (q j)) * phi (e q)
  calc
    _ = ∫ q : NPointDomain d k, f (fun j => rot.mulVec (q j)) := by
      apply integral_congr_ae
      filter_upwards with q
      have heq : e (fun j => rot.mulVec (q j)) = q := by
        ext j mu
        change rot.transpose.mulVec (rot.mulVec (q j)) mu = q j mu
        simp [Matrix.mulVec_mulVec, horth]
      simp only [f, heq]
    _ = ∫ q : NPointDomain d k, f q := integral_orthogonal_eq_self rot horth f
    _ = _ := hpair

/-- Pointwise E1 on the genuine Euclidean overlap. No complex spatial
continuation outside the physical tube is assumed. -/
theorem flatWick_euclideanRotation_eq
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (realization : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H)
    (rot : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (hdet : rot.det = 1) (horth : rot.transpose * rot = 1)
    (q : NPointDomain d k)
    (hq : q ∈ OSIIChapterV.initialReducedStrictPositiveGapRegion d k)
    (hrotq : (fun j => rot.mulVec (q j)) ∈ OSIIChapterV.initialReducedStrictPositiveGapRegion d k) :
    H.kernel (fun j => wickRotatePoint (rot.mulVec (q j))) =
      H.kernel (fun j => wickRotatePoint (q j)) := by
  let U : Set (NPointDomain d k) :=
    {p | p ∈ OSIIChapterV.initialReducedStrictPositiveGapRegion d k ∧
      (fun j => rot.mulVec (p j)) ∈ OSIIChapterV.initialReducedStrictPositiveGapRegion d k}
  have hrotcont : Continuous (fun p : NPointDomain d k => fun j => rot.mulVec (p j)) := by
    fun_prop
  have hU : IsOpen U := OSIIChapterV.isOpen_initialReducedStrictPositiveGapRegion.inter
    (OSIIChapterV.isOpen_initialReducedStrictPositiveGapRegion.preimage hrotcont)
  have hcont : ContinuousOn (fun p : NPointDomain d k =>
      H.kernel (fun j => wickRotatePoint (p j)))
      (OSIIChapterV.initialReducedStrictPositiveGapRegion d k) := by
    exact H.holomorphic.continuousOn.comp continuous_osiiReducedWickRotateConfig.continuousOn
      (fun p hp => osiiReducedWickRotateConfig_mem_productForwardTube_of_strictPositive p hp)
  have heq := SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn hU
    (hcont.comp hrotcont.continuousOn (fun p hp => hp.2))
    (hcont.mono (fun p hp => hp.1))
    (H.wickIntegral_euclideanRotation_eq Hstage realization rot hdet horth)
  exact heq ⟨hq, hrotq⟩

end OSIIReducedForwardTubeBoundaryData
end OSReconstruction
