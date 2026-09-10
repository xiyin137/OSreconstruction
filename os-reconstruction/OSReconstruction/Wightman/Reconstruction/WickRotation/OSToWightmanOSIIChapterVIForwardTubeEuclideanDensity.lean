import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIForwardTubeChronologicalRecovery
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIForwardTubeEuclideanGrowth

/-!
# The original-source Euclidean density

Proper rotations and chronological orderings cover the collision-free
configuration space. Original-E1/E3 source comparison makes their physical
kernel values agree on overlaps. The glued density is continuous off the
collision locus, measurable everywhere, and has the collision-weighted
bound required for zero-diagonal Schwartz completion.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction

abbrev OSIIEuclideanOrderIndex (d k : Nat) :=
  {rot : Matrix (Fin (d + 1)) (Fin (d + 1)) Real //
    rot.transpose * rot = 1 ∧ rot.det = 1} × Equiv.Perm (Fin (k + 1))

def osiiEuclideanOrderAction {d k : Nat} (i : OSIIEuclideanOrderIndex d k)
    (x : NPointDomain d (k + 1)) : NPointDomain d (k + 1) :=
  fun j => i.1.val.mulVec (x (i.2 j))

theorem continuous_osiiEuclideanOrderAction {d k : Nat} (i : OSIIEuclideanOrderIndex d k) :
    Continuous (osiiEuclideanOrderAction i) := by
  unfold osiiEuclideanOrderAction
  fun_prop

variable {d k : Nat} [NeZero d]

def osiiEuclideanOrderRegion (i : OSIIEuclideanOrderIndex d k) : Set (NPointDomain d (k + 1)) :=
  {x | OSIIChapterV.reducedTimeProjectionCLM d k (osiiEuclideanOrderAction i x) ∈
    section43TimeStrictPositiveRegion k}

theorem isOpen_osiiEuclideanOrderRegion (i : OSIIEuclideanOrderIndex d k) :
    IsOpen (osiiEuclideanOrderRegion i) :=
  (isOpen_section43TimeStrictPositiveRegion k).preimage
    ((OSIIChapterV.reducedTimeProjectionCLM d k).continuous.comp
      (continuous_osiiEuclideanOrderAction i))

theorem iUnion_osiiEuclideanOrderRegion :
    (⋃ i : OSIIEuclideanOrderIndex d k, osiiEuclideanOrderRegion i) =
      (CoincidenceLocus d (k + 1))ᶜ := by
  ext x
  constructor
  · intro hx hcoin
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    have hnot := OSIIReducedForwardTubeBoundaryData.not_mem_CoincidenceLocus_of_reducedTimePositive
      (osiiEuclideanOrderAction i x) hi
    apply hnot
    obtain ⟨a, b, hab, heq⟩ := hcoin
    refine ⟨i.2.symm a, i.2.symm b, i.2.symm.injective.ne hab, ?_⟩
    simpa [osiiEuclideanOrderAction] using congrArg i.1.val.mulVec heq
  · intro hx
    obtain ⟨P⟩ := exists_osiiOrderedProductNeighborhood x hx
    let i : OSIIEuclideanOrderIndex d k :=
      (⟨P.rotation, P.orthogonal, P.det_one⟩, P.order)
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    intro j
    change 0 < (P.rotation.mulVec (x (P.order j.succ))) 0 -
      (P.rotation.mulVec (x (P.order j.castSucc))) 0
    exact sub_pos.mpr (P.ordered x P.center_mem j.castSucc j.succ Fin.castSucc_lt_succ)

namespace OSIIReducedForwardTubeBoundaryData

variable {W : SchwartzNPoint d k →L[Complex] Complex}
variable {OS : OsterwalderSchraderAxioms d} {stage : OSIITimeContinuationStage d k}

def euclideanOrderKernel (H : OSIIReducedForwardTubeBoundaryData W)
    (i : OSIIEuclideanOrderIndex d k) (x : NPointDomain d (k + 1)) : Complex :=
  H.kernel (fun j => wickRotatePoint
    (BHW.reducedDiffMapReal (k + 1) d (osiiEuclideanOrderAction i x) j))

def euclideanDensity (H : OSIIReducedForwardTubeBoundaryData W) :
    NPointDomain d (k + 1) -> Complex :=
  SCV.glued_iUnion osiiEuclideanOrderRegion H.euclideanOrderKernel

theorem euclideanDensity_eqOn
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H)
    (i : OSIIEuclideanOrderIndex d k) :
    Set.EqOn H.euclideanDensity (H.euclideanOrderKernel i) (osiiEuclideanOrderRegion i) := by
  apply SCV.glued_iUnion_eqOn
  intro a b x hx
  exact H.flatWick_euclideanOrder_eq Hstage Rstage a.1.val b.1.val
    a.1.property.1 a.1.property.2 b.1.property.1 b.1.property.2 a.2 b.2 x hx.1 hx.2

theorem euclideanDensity_eq_zero_of_mem
    (H : OSIIReducedForwardTubeBoundaryData W)
    {x : NPointDomain d (k + 1)} (hx : x ∈ CoincidenceLocus d (k + 1)) :
    H.euclideanDensity x = 0 := by
  have hnone : ¬ ∃ i : OSIIEuclideanOrderIndex d k, x ∈ osiiEuclideanOrderRegion i := by
    intro h
    have hm := Set.mem_iUnion.mpr h
    rw [iUnion_osiiEuclideanOrderRegion] at hm
    exact hm hx
  simp [euclideanDensity, SCV.glued_iUnion, hnone]

theorem euclideanDensity_continuousOn
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H) :
    ContinuousOn H.euclideanDensity (CoincidenceLocus d (k + 1))ᶜ := by
  intro x hx
  have hcover : x ∈ ⋃ i : OSIIEuclideanOrderIndex d k, osiiEuclideanOrderRegion i := by
    rwa [iUnion_osiiEuclideanOrderRegion]
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hcover
  have hcont : ContinuousOn (H.euclideanOrderKernel i) (osiiEuclideanOrderRegion i) :=
    H.holomorphic.continuousOn.comp
      (continuous_osiiReducedWickRotateConfig.comp
        ((BHW.reducedDiffMapRealCLM (k + 1) d).continuous.comp
          (continuous_osiiEuclideanOrderAction i))).continuousOn
      (fun y hy => osiiReducedWickRotateConfig_mem_productForwardTube_of_strictPositive _ hy)
  have heq : H.euclideanDensity =ᶠ[nhds x] H.euclideanOrderKernel i := by
    filter_upwards [(isOpen_osiiEuclideanOrderRegion i).mem_nhds hi] with y hy
    exact H.euclideanDensity_eqOn Hstage Rstage i hy
  exact (((hcont x hi).continuousAt ((isOpen_osiiEuclideanOrderRegion i).mem_nhds hi)
    ).congr_of_eventuallyEq heq).continuousWithinAt

theorem euclideanDensity_measurable
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H) :
    Measurable H.euclideanDensity := by
  have h := (H.euclideanDensity_continuousOn Hstage Rstage).measurable_piecewise
    (g := fun _ => (0 : Complex)) continuousOn_const isClosed_CoincidenceLocus.measurableSet.compl
  have heq : (CoincidenceLocus d (k + 1))ᶜ.piecewise H.euclideanDensity (fun _ => 0) =
      H.euclideanDensity := by
    funext x
    by_cases hx : x ∈ CoincidenceLocus d (k + 1)
    · simp [Set.piecewise, hx, H.euclideanDensity_eq_zero_of_mem hx]
    · simp [Set.piecewise, hx]
  rwa [heq] at h

theorem euclideanDensity_exists_weighted_bound [NeZero k]
    (H : OSIIReducedForwardTubeBoundaryData W)
    (lgc : OSLinearGrowthCondition d OS)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H) :
    ∃ (C : Real) (N M : Nat), 0 < C ∧ ∀ x : NPointDomain d (k + 1),
      ‖H.euclideanDensity x‖ * Metric.infDist x (CoincidenceLocus d (k + 1)) ^ (M + 1) ≤
        C * (1 + ‖x‖) ^ N := by
  obtain ⟨C, N, M, hC, hbound⟩ := H.exists_collisionWeighted_flatWick_bound
    (lgc := lgc) Hstage Rstage
  refine ⟨C, N, M, hC, ?_⟩
  intro x
  by_cases hx : x ∈ CoincidenceLocus d (k + 1)
  · rw [H.euclideanDensity_eq_zero_of_mem hx]
    simp only [norm_zero, zero_mul]
    positivity
  · obtain ⟨rot, sigma, horth, hdet, hpositive, hweight⟩ := hbound x hx
    let i : OSIIEuclideanOrderIndex d k := (⟨rot, horth, hdet⟩, sigma)
    rw [H.euclideanDensity_eqOn Hstage Rstage i hpositive]
    exact hweight

theorem orderedCompactProduct_euclideanDensity_pairing
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H)
    (P : OSIIOrderedCompactProductSource d (k + 1)) :
    (∫ x : NPointDomain d (k + 1), H.euclideanDensity x * SchwartzMap.productTensor P.factors x) =
      OS.S (k + 1) ⟨SchwartzMap.productTensor P.factors, P.vanishes⟩ := by
  let i : OSIIEuclideanOrderIndex d k := (⟨P.rotation, P.orthogonal, P.det_one⟩, P.order)
  have hpositive : ∀ x ∈ tsupport (SchwartzMap.productTensor P.factors :
      NPointDomain d (k + 1) -> Complex), x ∈ osiiEuclideanOrderRegion i := by
    intro x hx j
    have hs := tsupport_productTensor_subset_factor_tsupport P.factors hx
    change 0 < (P.rotation.mulVec (x (P.order j.succ))) 0 -
      (P.rotation.mulVec (x (P.order j.castSucc))) 0
    exact sub_pos.mpr (P.ordered_support j.castSucc j.succ Fin.castSucc_lt_succ
      _ (hs _) _ (hs _))
  calc
    _ = ∫ x : NPointDomain d (k + 1),
        H.euclideanOrderKernel i x * SchwartzMap.productTensor P.factors x := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ tsupport (SchwartzMap.productTensor P.factors :
          NPointDomain d (k + 1) -> Complex)
      · rw [H.euclideanDensity_eqOn Hstage Rstage i (hpositive x hx)]
      · simp [image_eq_zero_of_notMem_tsupport hx]
    _ = _ := H.compactEuclideanOrder_wickIntegral_eq_schwinger
      Hstage Rstage P.rotation P.orthogonal P.det_one P.order
      ⟨SchwartzMap.productTensor P.factors, P.vanishes⟩
      (hasCompactSupport_productTensor P.factors P.factor_compact) hpositive

end OSIIReducedForwardTubeBoundaryData
end OSReconstruction
