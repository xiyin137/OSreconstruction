/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEuclideanComplexCharts











noncomputable section

open Complex Set
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace OSReconstruction

variable {d k : Nat} [NeZero d]

def osiiEuclideanHolomorphicDomain (d k : Nat) [NeZero d] :
    Set (Fin (k + 1) -> Fin (d + 1) -> Complex) :=
  (fun z => fun j => (osiiAxisPairWickBlockCLE (d := d)).symm (z j)) ⁻¹'
    osiiEuclideanComplexDomain d k

theorem isOpen_osiiEuclideanHolomorphicDomain : IsOpen (osiiEuclideanHolomorphicDomain d k) :=
  isOpen_osiiEuclideanComplexDomain.preimage (by fun_prop)

namespace OSIIReducedForwardTubeBoundaryData

variable {W : SchwartzNPoint d k →L[Complex] Complex}
variable {OS : OsterwalderSchraderAxioms d} {stage : OSIITimeContinuationStage d k}

def euclideanComplexChartKernel (H : OSIIReducedForwardTubeBoundaryData W)
    (i : OSIIEuclideanOrderIndex d k) (z : Fin (k + 1) -> Fin (d + 1) -> Complex) : Complex :=
  H.kernel (osiiEuclideanOrderComplexTubeMap i z)

omit [NeZero d] in
theorem euclideanComplexChartKernel_holomorphic
    (H : OSIIReducedForwardTubeBoundaryData W) (i : OSIIEuclideanOrderIndex d k) :
    DifferentiableOn Complex (H.euclideanComplexChartKernel i) (osiiEuclideanOrderComplexRegion i) :=
  H.holomorphic.comp (osiiEuclideanOrderComplexTubeMap i).differentiable.differentiableOn
    (Set.mapsTo_preimage _ _)

theorem euclideanComplexChartKernel_realToComplex
    (H : OSIIReducedForwardTubeBoundaryData W) (i : OSIIEuclideanOrderIndex d k)
    (x : NPointDomain d (k + 1)) :
    H.euclideanComplexChartKernel i (SCV.realToComplexProduct x) = H.euclideanOrderKernel i x := by
  simp only [euclideanComplexChartKernel, osiiEuclideanOrderComplexTubeMap_realToComplex,
    euclideanOrderKernel]
  rfl

theorem euclideanComplexChartKernel_eqOn
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H)
    (i j : OSIIEuclideanOrderIndex d k) :
    EqOn (H.euclideanComplexChartKernel i) (H.euclideanComplexChartKernel j)
      (osiiEuclideanOrderComplexRegion i ∩ osiiEuclideanOrderComplexRegion j) := by
  intro z hz
  apply SCV.holomorphic_eq_of_eq_on_real_of_connected_finite_product
    ((isOpen_osiiEuclideanOrderComplexRegion i).inter (isOpen_osiiEuclideanOrderComplexRegion j))
    ⟨⟨z, hz⟩, ((convex_osiiEuclideanOrderComplexRegion i).inter
      (convex_osiiEuclideanOrderComplexRegion j)).isPreconnected⟩
    ((H.euclideanComplexChartKernel_holomorphic i).mono Set.inter_subset_left)
    ((H.euclideanComplexChartKernel_holomorphic j).mono Set.inter_subset_right)
    (x₀ := fun a mu => (z a mu).re)
    ⟨osiiEuclideanOrderComplexRegion_realPart_mem i hz.1,
      osiiEuclideanOrderComplexRegion_realPart_mem j hz.2⟩ ?_ z hz
  intro x hx
  change H.euclideanComplexChartKernel i (SCV.realToComplexProduct x) =
    H.euclideanComplexChartKernel j (SCV.realToComplexProduct x)
  rw [H.euclideanComplexChartKernel_realToComplex, H.euclideanComplexChartKernel_realToComplex]
  exact (H.euclideanDensity_eqOn Hstage Rstage i
    ((osiiEuclideanOrderComplexRegion_realToComplex_iff i x).mp hx.1)).symm.trans
      (H.euclideanDensity_eqOn Hstage Rstage j
        ((osiiEuclideanOrderComplexRegion_realToComplex_iff j x).mp hx.2))

def euclideanComplexKernel (H : OSIIReducedForwardTubeBoundaryData W) :
    (Fin (k + 1) -> Fin (d + 1) -> Complex) -> Complex :=
  SCV.glued_iUnion osiiEuclideanOrderComplexRegion H.euclideanComplexChartKernel

theorem euclideanComplexKernel_eqOn
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H)
    (i : OSIIEuclideanOrderIndex d k) :
    EqOn H.euclideanComplexKernel (H.euclideanComplexChartKernel i) (osiiEuclideanOrderComplexRegion i) :=
  SCV.glued_iUnion_eqOn (H.euclideanComplexChartKernel_eqOn Hstage Rstage) i

theorem euclideanComplexKernel_holomorphic
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H) :
    DifferentiableOn Complex H.euclideanComplexKernel (osiiEuclideanComplexDomain d k) :=
  SCV.differentiableOn_glued_iUnion (Set.Subset.refl _) isOpen_osiiEuclideanOrderComplexRegion
    H.euclideanComplexChartKernel_holomorphic (H.euclideanComplexChartKernel_eqOn Hstage Rstage)

theorem euclideanComplexKernel_eq_zero_of_not_mem
    (H : OSIIReducedForwardTubeBoundaryData W)
    {z : Fin (k + 1) -> Fin (d + 1) -> Complex} (hz : z ∉ osiiEuclideanComplexDomain d k) :
    H.euclideanComplexKernel z = 0 := by
  have hnone : ¬ ∃ i : OSIIEuclideanOrderIndex d k, z ∈ osiiEuclideanOrderComplexRegion i :=
    fun h => hz (Set.mem_iUnion.mpr h)
  simp [euclideanComplexKernel, SCV.glued_iUnion, hnone]

theorem euclideanComplexKernel_realToComplex
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H)
    (x : NPointDomain d (k + 1)) :
    H.euclideanComplexKernel (SCV.realToComplexProduct x) = H.euclideanDensity x := by
  by_cases hx : x ∈ CoincidenceLocus d (k + 1)
  · rw [H.euclideanDensity_eq_zero_of_mem hx]
    exact H.euclideanComplexKernel_eq_zero_of_not_mem
      (fun h => ((osiiEuclideanComplexDomain_realToComplex_iff x).mp h) hx)
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ((osiiEuclideanComplexDomain_realToComplex_iff x).mpr hx)
    rw [H.euclideanComplexKernel_eqOn Hstage Rstage i hi, H.euclideanComplexChartKernel_realToComplex]
    exact (H.euclideanDensity_eqOn Hstage Rstage i
      ((osiiEuclideanOrderComplexRegion_realToComplex_iff i x).mp hi)).symm

theorem euclideanComplexKernel_perm
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H)
    (sigma : Equiv.Perm (Fin (k + 1))) (z : Fin (k + 1) -> Fin (d + 1) -> Complex) :
    H.euclideanComplexKernel (fun j => z (sigma j)) = H.euclideanComplexKernel z := by
  by_cases hz : z ∈ osiiEuclideanComplexDomain d k
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ((osiiEuclideanComplexDomain_perm_iff sigma z).mpr hz)
    have hj : z ∈ osiiEuclideanOrderComplexRegion (i.1, i.2.trans sigma) := by
      change osiiEuclideanOrderComplexTubeMap (i.1, i.2.trans sigma) z ∈
        TubeDomainSetPi (BHW.ProductForwardConeReal d k)
      rw [← osiiEuclideanOrderComplexTubeMap_perm]
      exact hi
    rw [H.euclideanComplexKernel_eqOn Hstage Rstage i hi,
      H.euclideanComplexKernel_eqOn Hstage Rstage (i.1, i.2.trans sigma) hj]
    exact congrArg H.kernel (osiiEuclideanOrderComplexTubeMap_perm i sigma z)
  · rw [H.euclideanComplexKernel_eq_zero_of_not_mem hz]
    exact H.euclideanComplexKernel_eq_zero_of_not_mem
      (fun h => hz ((osiiEuclideanComplexDomain_perm_iff sigma z).mp h))

theorem euclideanComplexKernel_translate
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H)
    (z : Fin (k + 1) -> Fin (d + 1) -> Complex) (a : Fin (d + 1) -> Complex) :
    H.euclideanComplexKernel (fun j => z j + a) = H.euclideanComplexKernel z := by
  by_cases hz : z ∈ osiiEuclideanComplexDomain d k
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    have hia := (osiiEuclideanOrderComplexRegion_translate_iff i z a).mpr hi
    rw [H.euclideanComplexKernel_eqOn Hstage Rstage i hia,
      H.euclideanComplexKernel_eqOn Hstage Rstage i hi]
    exact congrArg H.kernel (osiiEuclideanOrderComplexTubeMap_translate i z a)
  · rw [H.euclideanComplexKernel_eq_zero_of_not_mem hz]
    exact H.euclideanComplexKernel_eq_zero_of_not_mem
      (fun h => hz ((osiiEuclideanComplexDomain_translate_iff z a).mp h))

def euclideanHolomorphicKernel (H : OSIIReducedForwardTubeBoundaryData W)
    (z : Fin (k + 1) -> Fin (d + 1) -> Complex) : Complex :=
  H.euclideanComplexKernel (fun j => (osiiAxisPairWickBlockCLE (d := d)).symm (z j))

theorem euclideanHolomorphicKernel_eq_of_reduced_mem
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H)
    {z : Fin (k + 1) -> Fin (d + 1) -> Complex}
    (hz : BHW.reducedDiffMap (k + 1) d z ∈ TubeDomainSetPi (BHW.ProductForwardConeReal d k)) :
    H.euclideanHolomorphicKernel z = H.kernel (BHW.reducedDiffMap (k + 1) d z) := by
  have hi : (fun j => (osiiAxisPairWickBlockCLE (d := d)).symm (z j)) ∈
      osiiEuclideanOrderComplexRegion (osiiIdentityEuclideanOrderIndex d k) := by
    change osiiEuclideanOrderComplexTubeMap (osiiIdentityEuclideanOrderIndex d k) _ ∈
      TubeDomainSetPi (BHW.ProductForwardConeReal d k)
    rwa [osiiEuclideanOrderComplexTubeMap_identity_inverseWick]
  rw [euclideanHolomorphicKernel, H.euclideanComplexKernel_eqOn Hstage Rstage
    (osiiIdentityEuclideanOrderIndex d k) hi, euclideanComplexChartKernel,
    osiiEuclideanOrderComplexTubeMap_identity_inverseWick]

theorem euclideanHolomorphicKernel_holomorphic
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H) :
    DifferentiableOn Complex H.euclideanHolomorphicKernel (osiiEuclideanHolomorphicDomain d k) := by
  have hInv : Differentiable Complex (fun z : Fin (k + 1) -> Fin (d + 1) -> Complex =>
      fun j => (osiiAxisPairWickBlockCLE (d := d)).symm (z j)) := by
    apply differentiable_pi.mpr
    intro j
    exact (osiiAxisPairWickBlockCLE (d := d)).symm.differentiable.comp (differentiable_apply j)
  exact (H.euclideanComplexKernel_holomorphic Hstage Rstage).comp
    hInv.differentiableOn (Set.mapsTo_preimage _ _)

theorem euclideanHolomorphicKernel_wick
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H)
    (x : NPointDomain d (k + 1)) :
    H.euclideanHolomorphicKernel (fun j => wickRotatePoint (x j)) = H.euclideanDensity x := by
  simpa only [euclideanHolomorphicKernel, osiiAxisPairWickBlockCLE_symm_apply,
    osiiAxisPairInverseWickBlock_wickRotatePoint] using
      H.euclideanComplexKernel_realToComplex Hstage Rstage x

theorem euclideanHolomorphicKernel_perm
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H)
    (sigma : Equiv.Perm (Fin (k + 1))) (z : Fin (k + 1) -> Fin (d + 1) -> Complex) :
    H.euclideanHolomorphicKernel (fun j => z (sigma j)) = H.euclideanHolomorphicKernel z :=
  H.euclideanComplexKernel_perm Hstage Rstage sigma
    (fun j => (osiiAxisPairWickBlockCLE (d := d)).symm (z j))

theorem euclideanHolomorphicKernel_translate
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H)
    (z : Fin (k + 1) -> Fin (d + 1) -> Complex) (a : Fin (d + 1) -> Complex) :
    H.euclideanHolomorphicKernel (fun j => z j + a) = H.euclideanHolomorphicKernel z := by
  simpa only [euclideanHolomorphicKernel, map_add] using
    H.euclideanComplexKernel_translate Hstage Rstage
      (fun j => (osiiAxisPairWickBlockCLE (d := d)).symm (z j))
      ((osiiAxisPairWickBlockCLE (d := d)).symm a)

end OSIIReducedForwardTubeBoundaryData
end OSReconstruction
