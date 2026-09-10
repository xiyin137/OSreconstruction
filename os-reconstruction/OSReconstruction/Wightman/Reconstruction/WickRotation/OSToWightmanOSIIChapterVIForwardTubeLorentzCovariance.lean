import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIForwardTubeEuclideanCovariance
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanEuclideanLorentz
import OSReconstruction.ComplexLieGroups.DifferenceCoordinatesReduced

/-!
# Full Lorentz covariance of the physical tube

The difference-coordinate equivalence converts the physical product tube to
the existing ordered forward tube. Its Euclidean Wick pairing satisfies the
original E1 identity, so the proved Lorentz continuation theorem applies.
Transporting back gives invariance on the actual physical tube overlap.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction

variable {d k : Nat} [NeZero d]

omit [NeZero d] in
theorem osiiDiffCoordEquiv_wick (q : NPointDomain d k) :
    BHW.diffCoordEquiv k d (fun j => wickRotatePoint (q j)) =
      fun j => wickRotatePoint (section43DiffCoordRealCLE d k q j) := by
  ext j mu
  by_cases hj : j.val = 0 <;> by_cases hmu : mu = 0 <;>
    simp [BHW.diffCoordEquiv_apply, wickRotatePoint, hj, hmu, mul_sub]

theorem osiiWickReduced_mem_iff (q : NPointDomain d k) :
    (fun j => wickRotatePoint (q j)) ∈ TubeDomainSetPi (BHW.ProductForwardConeReal d k) ↔
      q ∈ OSIIChapterV.initialReducedStrictPositiveGapRegion d k := by
  constructor
  · intro hq j
    change 0 < q j 0
    simpa [wickRotatePoint] using (hq j).1
  · exact osiiReducedWickRotateConfig_mem_productForwardTube_of_strictPositive q

omit [NeZero d] in
theorem osiiProductForwardTube_ofReal_mem
    (L : LorentzLieGroup.RestrictedLorentzGroup d)
    (z : Fin k -> Fin (d + 1) -> Complex)
    (hz : z ∈ TubeDomainSetPi (BHW.ProductForwardConeReal d k)) :
    BHW.complexLorentzAction (ComplexLorentzGroup.ofReal L) z ∈
      TubeDomainSetPi (BHW.ProductForwardConeReal d k) := by
  intro j
  have h := BHW.real_lorentz_preserves_forwardCone L (fun mu => (z j mu).im) (hz j)
  simpa [BHW.complexLorentzAction, BHW.complexLorentzVectorAction,
    ComplexLorentzGroup.ofReal] using h

namespace OSIIReducedForwardTubeBoundaryData

variable {OS : OsterwalderSchraderAxioms d} {stage : OSIITimeContinuationStage d k}
variable {W : SchwartzNPoint d k →L[Complex] Complex}

/-- Original Euclidean covariance supplies full complex Lorentz invariance
where both physical tube points exist. The proof covers zero gap arity. -/
theorem complexLorentzInvariant
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (realization : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H)
    (L : ComplexLorentzGroup d) (z : Fin k -> Fin (d + 1) -> Complex)
    (hz : z ∈ TubeDomainSetPi (BHW.ProductForwardConeReal d k))
    (hLz : BHW.complexLorentzAction L z ∈ TubeDomainSetPi (BHW.ProductForwardConeReal d k)) :
    H.kernel (BHW.complexLorentzAction L z) = H.kernel z := by
  let F := fun w => H.kernel (BHW.diffCoordEquiv k d w)
  have hmem {w : Fin k -> Fin (d + 1) -> Complex} (hw : w ∈ BHW.ForwardTube d k) :
      BHW.diffCoordEquiv k d w ∈ TubeDomainSetPi (BHW.ProductForwardConeReal d k) := by
    rw [BHW.forwardTube_eq_diffCoord_preimage] at hw
    exact hw
  have hFholo : DifferentiableOn Complex F (BHW.ForwardTube d k) :=
    H.holomorphic.comp (BHW.diffCoordEquiv k d).differentiable.differentiableOn
      (fun w hw => hmem hw)
  have hFdist (rot : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
      (hdet : rot.det = 1) (horth : rot.transpose * rot = 1)
      (phi : SchwartzNPoint d k) (_hcompact : HasCompactSupport (phi : NPointDomain d k -> Complex))
      (hsupport : tsupport (phi : NPointDomain d k -> Complex) ⊆
        {q | (fun j => wickRotatePoint (q j)) ∈ BHW.ForwardTube d k ∧
          BHW.complexLorentzAction (ComplexLorentzGroup.ofEuclidean rot hdet horth)
            (fun j => wickRotatePoint (q j)) ∈ BHW.ForwardTube d k}) :
      (∫ q : NPointDomain d k,
        F (BHW.complexLorentzAction (ComplexLorentzGroup.ofEuclidean rot hdet horth)
          (fun j => wickRotatePoint (q j))) * phi q) =
        ∫ q : NPointDomain d k, F (fun j => wickRotatePoint (q j)) * phi q := by
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ tsupport (phi : NPointDomain d k -> Complex)
    · let q := section43DiffCoordRealCLE d k x
      have hq : (fun j => wickRotatePoint (q j)) ∈
          TubeDomainSetPi (BHW.ProductForwardConeReal d k) := by
        simpa only [q, osiiDiffCoordEquiv_wick] using hmem (hsupport hx).1
      have hrotq : (fun j => wickRotatePoint (rot.mulVec (q j))) ∈
          TubeDomainSetPi (BHW.ProductForwardConeReal d k) := by
        rw [osiiWickRotateConfig_ofEuclidean rot hdet horth]
        simpa only [q, BHW.diffCoordEquiv_action, osiiDiffCoordEquiv_wick] using
          hmem (hsupport hx).2
      have heq := H.flatWick_euclideanRotation_eq Hstage realization rot hdet horth q
        ((osiiWickReduced_mem_iff q).mp hq)
        ((osiiWickReduced_mem_iff _).mp hrotq)
      change H.kernel (BHW.diffCoordEquiv k d
          (BHW.complexLorentzAction (ComplexLorentzGroup.ofEuclidean rot hdet horth)
            (fun j => wickRotatePoint (x j)))) * phi x =
        H.kernel (BHW.diffCoordEquiv k d (fun j => wickRotatePoint (x j))) * phi x
      rw [BHW.diffCoordEquiv_action, osiiDiffCoordEquiv_wick,
        ← osiiWickRotateConfig_ofEuclidean rot hdet horth]
      exact congrArg (fun c => c * phi x) heq
    · simp [image_eq_zero_of_notMem_tsupport hx]
  let w := (BHW.diffCoordEquiv k d).symm z
  have hw : w ∈ BHW.ForwardTube d k := by
    rw [BHW.forwardTube_eq_diffCoord_preimage]
    simpa [w] using hz
  have hLw : BHW.complexLorentzAction L w ∈ BHW.ForwardTube d k := by
    rw [BHW.forwardTube_eq_diffCoord_preimage]
    change BHW.diffCoordEquiv k d (BHW.complexLorentzAction L w) ∈ BHW.ProductForwardCone d k
    rw [BHW.diffCoordEquiv_action]
    simpa [w] using hLz
  have h := BHW.Task5Bridge.complex_lorentz_invariance_from_euclidean_distributional
    k F hFholo hFdist L w hw hLw
  simpa [F, w, BHW.diffCoordEquiv_action] using h

/-- Every proper orthochronous real Lorentz transformation preserves the
physical tube and the value of its kernel. -/
theorem realLorentzInvariant
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (realization : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H)
    (L : LorentzLieGroup.RestrictedLorentzGroup d)
    (z : Fin k -> Fin (d + 1) -> Complex)
    (hz : z ∈ TubeDomainSetPi (BHW.ProductForwardConeReal d k)) :
    H.kernel (BHW.complexLorentzAction (ComplexLorentzGroup.ofReal L) z) = H.kernel z :=
  H.complexLorentzInvariant Hstage realization (ComplexLorentzGroup.ofReal L) z hz
    (osiiProductForwardTube_ofReal_mem L z hz)

end OSIIReducedForwardTubeBoundaryData
end OSReconstruction
