/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVILorentzSupport
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVISchwartzSupport
















noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction

variable {d k : Nat} [NeZero d]

/-- Every block of the open product forward cone also belongs to the closed
product forward cone. -/
theorem osiiReducedForwardFlatCone_subset_productForwardCone :
    osiiReducedForwardFlatCone d k ⊆
      osiiCanonicalFrequencyProductForwardCone d k := by
  intro p hp j
  have hBHW : BHW.InOpenForwardCone d
      (osiiCanonicalFrequencyParticleBlock d k p j) := hp j
  have hpublic : InOpenForwardCone d
      (osiiCanonicalFrequencyParticleBlock d k p j) := by
    rw [InOpenForwardCone]
    exact
      (inOpenForwardCone_iff (d := d)
        (osiiCanonicalFrequencyParticleBlock d k p j)).mp hBHW
  change MinkowskiSpace.minkowskiNormSq d
      (osiiCanonicalFrequencyParticleBlock d k p j) ≤ 0 ∧
    0 ≤ osiiCanonicalFrequencyParticleBlock d k p j 0
  exact ⟨hpublic.2.le, hpublic.1.le⟩

/-- The common unit future-time direction in canonical particle-block
frequency coordinates. -/
private def osiiCanonicalFrequencyFutureTimeVector (d k : Nat) :
    Fin (k * (d + 1)) -> Real :=
  fun i => if (finProdFinEquiv.symm i).2 = 0 then 1 else 0

/-- A strictly positive common future-time displacement moves the entire
closed product cone into the open product cone, including all lightlike
faces, cone tips, and product corners. -/
theorem osiiCanonicalFrequency_add_futureTime_mem_openCone
    (p : Fin (k * (d + 1)) -> Real)
    (hp : p ∈ osiiCanonicalFrequencyProductForwardCone d k)
    {t : Real} (ht : 0 < t) :
    p + t • osiiCanonicalFrequencyFutureTimeVector d k ∈
      osiiReducedForwardFlatCone d k := by
  intro j
  let q := osiiCanonicalFrequencyParticleBlock d k p j
  have hq : MinkowskiSpace.minkowskiNormSq d q ≤ 0 ∧ 0 ≤ q 0 := hp j
  have htime :
      0 < osiiCanonicalFrequencyParticleBlock d k
        (p + t • osiiCanonicalFrequencyFutureTimeVector d k) j 0 := by
    simp [osiiCanonicalFrequencyParticleBlock,
      osiiCanonicalFrequencyFutureTimeVector, q] at hq ⊢
    linarith
  have hquad :
      MinkowskiSpace.minkowskiNormSq d
        (osiiCanonicalFrequencyParticleBlock d k
          (p + t • osiiCanonicalFrequencyFutureTimeVector d k) j) =
        MinkowskiSpace.minkowskiNormSq d q -
          2 * t * q 0 - t ^ 2 := by
    rw [MinkowskiSpace.minkowskiNormSq_decomp,
      MinkowskiSpace.minkowskiNormSq_decomp]
    simp [MinkowskiSpace.spatialNormSq,
      osiiCanonicalFrequencyParticleBlock,
      osiiCanonicalFrequencyFutureTimeVector, q, Fin.succ_ne_zero]
    ring
  have hnorm :
      MinkowskiSpace.minkowskiNormSq d
        (osiiCanonicalFrequencyParticleBlock d k
          (p + t • osiiCanonicalFrequencyFutureTimeVector d k) j) < 0 := by
    rw [hquad]
    nlinarith [mul_nonneg ht.le hq.2, sq_pos_of_pos ht]
  apply (inOpenForwardCone_iff (d := d)
    (osiiCanonicalFrequencyParticleBlock d k
      (p + t • osiiCanonicalFrequencyFutureTimeVector d k) j)).mpr
  exact ⟨htime, hnorm⟩

/-- If a Schwartz test vanishes pointwise on the closed product cone, every
strictly future-time translate has topological support disjoint from that
cone.  Openness is essential because the original test can meet the cone in
its topological support while still vanishing there pointwise. -/
private theorem osiiCanonicalFrequency_futureTranslate_tsupport_subset_cone_compl
    (phi : SchwartzMap (Fin (k * (d + 1)) -> Real) Complex)
    (hphi : ∀ p ∈ Function.support
      (phi : (Fin (k * (d + 1)) -> Real) -> Complex),
      p ∉ osiiCanonicalFrequencyProductForwardCone d k)
    {t : Real} (ht : 0 < t) :
    tsupport
        ((SCV.translateSchwartz
          (t • osiiCanonicalFrequencyFutureTimeVector d k) phi :
            SchwartzMap (Fin (k * (d + 1)) -> Real) Complex) :
              (Fin (k * (d + 1)) -> Real) -> Complex) ⊆
      (osiiCanonicalFrequencyProductForwardCone d k)ᶜ := by
  intro p hp hpcone
  let V : Set (Fin (k * (d + 1)) -> Real) :=
    (fun q => q + t • osiiCanonicalFrequencyFutureTimeVector d k) ⁻¹'
      osiiReducedForwardFlatCone d k
  have hVopen : IsOpen V :=
    isOpen_osiiReducedForwardFlatCone.preimage
      (continuous_id.add continuous_const)
  have hpV : p ∈ V :=
    osiiCanonicalFrequency_add_futureTime_mem_openCone p hpcone ht
  have heventually :
      ((SCV.translateSchwartz
        (t • osiiCanonicalFrequencyFutureTimeVector d k) phi :
          SchwartzMap (Fin (k * (d + 1)) -> Real) Complex) :
            (Fin (k * (d + 1)) -> Real) -> Complex) =ᶠ[nhds p] 0 := by
    filter_upwards [hVopen.mem_nhds hpV] with q hq
    rw [SCV.translateSchwartz_apply]
    have hqcone :
        q + t • osiiCanonicalFrequencyFutureTimeVector d k ∈
          osiiCanonicalFrequencyProductForwardCone d k :=
      osiiReducedForwardFlatCone_subset_productForwardCone hq
    by_contra hnonzero
    exact hphi _ (Function.mem_support.mpr hnonzero) hqcone
  exact (notMem_tsupport_iff_eventuallyEq.mpr heventually) hp

/-- For the canonical product forward cone, ordinary distributional support
implies the production Fourier-support predicate on every Schwartz test.
The proof uses finite localization, noncompact radial density, and strictly
future-time translation rather than a false `support = tsupport` shortcut. -/
theorem hasFourierSupportInDualCone_osiiReducedForwardFlatCone_of_dsupport_subset
    {T : SchwartzMap (Fin (k * (d + 1)) -> Real) Complex →L[Complex] Complex}
    (hT : Distribution.dsupport T ⊆
      osiiCanonicalFrequencyProductForwardCone d k) :
    HasFourierSupportInDualCone (osiiReducedForwardFlatCone d k) T := by
  apply (hasFourierSupportInDualCone_osiiReducedForwardFlatCone_iff T).mpr
  intro phi hphi
  have hvanishing : Distribution.IsVanishingOn T
      (osiiCanonicalFrequencyProductForwardCone d k)ᶜ := by
    exact (osiiSchwartzDistribution_isVanishingOn_compl_dsupport T).mono
      (Set.compl_subset_compl.mpr hT)
  let v := osiiCanonicalFrequencyFutureTimeVector d k
  have hcontinuous :
      Continuous (fun t : Real => T (SCV.translateSchwartz (t • v) phi)) :=
    T.continuous.comp
      ((continuous_translateSchwartz_unrestricted phi).comp
        (continuous_id.smul continuous_const))
  let Z : Set Real :=
    {t | T (SCV.translateSchwartz (t • v) phi) = 0}
  have hZclosed : IsClosed Z :=
    isClosed_eq hcontinuous continuous_const
  have hpositive : Set.Ioi (0 : Real) ⊆ Z := by
    intro t ht
    apply hvanishing
    exact
      osiiCanonicalFrequency_futureTranslate_tsupport_subset_cone_compl
        phi hphi ht
  have hzero_closure : (0 : Real) ∈ closure (Set.Ioi (0 : Real)) := by
    rw [closure_Ioi]
    simp
  have hzero : (0 : Real) ∈ Z :=
    closure_minimal hpositive hZclosed hzero_closure
  change T (SCV.translateSchwartz ((0 : Real) • v) phi) = 0 at hzero
  have htranslate : SCV.translateSchwartz ((0 : Real) • v) phi = phi := by
    ext p
    simp
  rwa [htranslate] at hzero

/-- At a fixed, already constructed tempered boundary, genuine temporal
positivity and Lorentz transport imply the complete native spectral condition
without invoking any analytic or production axioms. -/
theorem osiiCanonicalFrequency_support_of_temporalVanishing_of_lorentzTransport
    (W : SchwartzNPoint d k →L[Complex] Complex)
    (hTemporal : Distribution.IsVanishingOn
      (osiiCanonicalFrequencyDistribution W)
      (osiiCanonicalFrequencyTemporalCylinder d k)ᶜ)
    (htransport : OSIICanonicalFrequencyLorentzTransport d k
      (osiiCanonicalFrequencyDistribution W)) :
    HasFourierSupportInDualCone (osiiReducedForwardFlatCone d k)
      (osiiCanonicalFrequencyDistribution W) := by
  apply hasFourierSupportInDualCone_osiiReducedForwardFlatCone_of_dsupport_subset
  apply dsupport_subset_osiiCanonicalFrequencyProductForwardCone_of_vanishing
  intro j y hy
  obtain ⟨e, hinvariant, he⟩ := htransport j y hy
  exact osiiCanonicalFrequency_isVanishingOn_halfspace_of_covariant_transport
    hTemporal j y e hinvariant he

/-- The axiom-free spectral constructor at an independently supplied
tempered boundary.  In particular, this does not invoke the legacy false
compact-growth boundary-to-spectrum contract. -/
def osiiReducedForwardTubeBoundarySpectralData_of_temporalVanishing_of_lorentzTransport
    (W : SchwartzNPoint d k →L[Complex] Complex)
    (hTemporal : Distribution.IsVanishingOn
      (osiiCanonicalFrequencyDistribution W)
      (osiiCanonicalFrequencyTemporalCylinder d k)ᶜ)
    (htransport : OSIICanonicalFrequencyLorentzTransport d k
      (osiiCanonicalFrequencyDistribution W)) :
    OSIIReducedForwardTubeBoundarySpectralData d k where
  boundaryDistribution := W
  support := osiiCanonicalFrequency_support_of_temporalVanishing_of_lorentzTransport
    W hTemporal htransport

namespace OSIIFullTimeStageVladimirovGrowthData

variable {A : OSIITimeContinuationStage d k}

/-- Genuine temporal positive-energy support plus independently established
Lorentz transport proves the exact native forward-cone spectral field. This
certificate form remains reusable; the actual Chapter VI boundary now proves
its temporal certificate independently of the legacy support axioms. -/
theorem canonicalFrequency_support_of_temporalVanishing_of_lorentzTransport
    (G : OSIIFullTimeStageVladimirovGrowthData A) [NeZero k]
    (hTemporal : Distribution.IsVanishingOn
      (osiiCanonicalFrequencyDistribution
        G.toTemperedBoundaryData.reducedBoundary)
      (osiiCanonicalFrequencyTemporalCylinder d k)ᶜ)
    (htransport : OSIICanonicalFrequencyLorentzTransport d k
      (osiiCanonicalFrequencyDistribution
        G.toTemperedBoundaryData.reducedBoundary)) :
    HasFourierSupportInDualCone (osiiReducedForwardFlatCone d k)
      (osiiCanonicalFrequencyDistribution
        G.toTemperedBoundaryData.reducedBoundary) :=
  osiiCanonicalFrequency_support_of_temporalVanishing_of_lorentzTransport
    G.toTemperedBoundaryData.reducedBoundary hTemporal htransport

/-- Construct the first reduced forward-tube spectral datum directly from the
Chapter VI boundary and the independently proved temporal/Lorentz conclusions.
This constructor does not invoke either production support axiom. -/
def toReducedForwardTubeBoundarySpectralData_of_temporalVanishing_of_lorentzTransport
    (G : OSIIFullTimeStageVladimirovGrowthData A) [NeZero k]
    (hTemporal : Distribution.IsVanishingOn
      (osiiCanonicalFrequencyDistribution
        G.toTemperedBoundaryData.reducedBoundary)
      (osiiCanonicalFrequencyTemporalCylinder d k)ᶜ)
    (htransport : OSIICanonicalFrequencyLorentzTransport d k
      (osiiCanonicalFrequencyDistribution
        G.toTemperedBoundaryData.reducedBoundary)) :
    OSIIReducedForwardTubeBoundarySpectralData d k :=
  G.toTemperedBoundaryData.toReducedForwardTubeBoundarySpectralData
    (G.canonicalFrequency_support_of_temporalVanishing_of_lorentzTransport
      hTemporal htransport)

@[simp]
theorem toReducedForwardTubeBoundarySpectralData_of_temporalVanishing_of_lorentzTransport_boundaryDistribution
    (G : OSIIFullTimeStageVladimirovGrowthData A) [NeZero k]
    (hTemporal : Distribution.IsVanishingOn
      (osiiCanonicalFrequencyDistribution
        G.toTemperedBoundaryData.reducedBoundary)
      (osiiCanonicalFrequencyTemporalCylinder d k)ᶜ)
    (htransport : OSIICanonicalFrequencyLorentzTransport d k
      (osiiCanonicalFrequencyDistribution
        G.toTemperedBoundaryData.reducedBoundary)) :
    (G.toReducedForwardTubeBoundarySpectralData_of_temporalVanishing_of_lorentzTransport
      hTemporal htransport).boundaryDistribution =
      G.toTemperedBoundaryData.reducedBoundary := rfl

end OSIIFullTimeStageVladimirovGrowthData

end OSReconstruction
