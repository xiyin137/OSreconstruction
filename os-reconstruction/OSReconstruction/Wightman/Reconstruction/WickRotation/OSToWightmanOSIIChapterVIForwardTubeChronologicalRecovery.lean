/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVICanonicalTubeIdentification
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIOrderedProductReducedSupport
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanReducedForwardTubeControl
import OSReconstruction.Wightman.Reconstruction.WickRotation.SchwingerAxioms









noncomputable section

open Complex MeasureTheory Set Topology

namespace OSReconstruction
namespace OSIIReducedForwardTubeBoundaryData

variable {d k : Nat} [NeZero d]
variable {W : SchwartzNPoint d k →L[Complex] Complex}

theorem compactChronological_wickIntegral_integrable
    (H : OSIIReducedForwardTubeBoundaryData W)
    (f : SchwartzNPoint d (k + 1))
    (hcompact : HasCompactSupport (f : NPointDomain d (k + 1) -> Complex))
    (hsupport : ∀ x ∈ tsupport (f : NPointDomain d (k + 1) -> Complex),
      OSIIChapterV.reducedTimeProjectionCLM d k x ∈ section43TimeStrictPositiveRegion k) :
    Integrable (fun x : NPointDomain d (k + 1) =>
      H.kernel (fun j => wickRotatePoint (BHW.reducedDiffMapReal (k + 1) d x j)) * f x) := by
  let K := tsupport (f : NPointDomain d (k + 1) -> Complex)
  let g := fun x : NPointDomain d (k + 1) =>
    H.kernel (fun j => wickRotatePoint (BHW.reducedDiffMapReal (k + 1) d x j)) * f x
  have hkernel : ContinuousOn (fun x : NPointDomain d (k + 1) =>
      H.kernel (fun j => wickRotatePoint (BHW.reducedDiffMapReal (k + 1) d x j))) K :=
    H.holomorphic.continuousOn.comp
      (continuous_osiiReducedWickRotateConfig.comp
        (BHW.reducedDiffMapRealCLM (k + 1) d).continuous).continuousOn
      (fun x hx => osiiReducedWickRotateConfig_mem_productForwardTube_of_strictPositive
        _ (hsupport x hx))
  have hg : ContinuousOn g K := hkernel.mul f.continuous.continuousOn
  have hs : Function.support g ⊆ K := by
    intro x hx
    by_contra hxK
    exact hx (by simp [g, image_eq_zero_of_notMem_tsupport hxK])
  exact (integrableOn_iff_integrable_of_support_subset hs).mp
    (hg.integrableOn_compact hcompact)

theorem compactChronological_wickIntegral_eq_schwinger
    {OS : OsterwalderSchraderAxioms d} {stage : OSIITimeContinuationStage d k}
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (R : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H)
    (f : ZeroDiagonalSchwartz d (k + 1))
    (hcompact : HasCompactSupport (f.1 : NPointDomain d (k + 1) -> Complex))
    (hsupport : ∀ x ∈ tsupport (f.1 : NPointDomain d (k + 1) -> Complex),
      OSIIChapterV.reducedTimeProjectionCLM d k x ∈ section43TimeStrictPositiveRegion k) :
    (∫ x : NPointDomain d (k + 1),
      H.kernel (fun j => wickRotatePoint (BHW.reducedDiffMapReal (k + 1) d x j)) * f.1 x) =
      OS.S (k + 1) f := by
  let K := OSIIChapterV.reducedTimeProjectionCLM d k ''
    tsupport (f.1 : NPointDomain d (k + 1) -> Complex)
  have hK : IsCompact K := hcompact.image (OSIIChapterV.reducedTimeProjectionCLM d k).continuous
  have hKpos : K ⊆ section43TimeStrictPositiveRegion k := by
    rintro _ ⟨x, hx, rfl⟩
    exact hsupport x hx
  obtain ⟨D⟩ := Hstage K hK hKpos
  obtain ⟨C⟩ := OSIIChapterV.CanonicalReducedCompactMovingSliceCutoffData.nonempty D hK
  let phi := diffVarReduction d k f.1
  have hred := diffVarReduction_tsupport_subset_reducedDiff_image_tsupport_of_compact f.1 hcompact
  have hphi_compact : HasCompactSupport (phi : NPointDomain d k -> Complex) :=
    (hcompact.image (BHW.reducedDiffMapRealCLM (k + 1) d).continuous
      ).of_isClosed_subset (isClosed_tsupport _) hred
  have hphi_support : tsupport (phi : NPointDomain d k -> Complex) ⊆
      {q | section43QTime (d := d) (n := k) q ∈ K} := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := hred hq
    exact ⟨x, hx, rfl⟩
  rw [integral_reducedDiffKernel_eq_diffVarReduction f.1
    (fun q : NPointDomain d k => H.kernel (fun j => wickRotatePoint (q j)))
    (H.compactChronological_wickIntegral_integrable f.1 hcompact hsupport)]
  rw [← osiiStageMovingSliceDistribution_zero_eq_forwardTubeFlatWickIntegral D C H R phi
    ⟨hphi_compact, hphi_support⟩]
  exact OSIIChapterV.movingSliceDistribution_zero_diffVarReduction_eq_schwinger
    D C.cutoff C.cutoff_support C.cutoff_compact C.cutoff_one_on f.1 f.2
    (fun x hx => ⟨x, hx, rfl⟩)

/-- E1/E3 transport the actual compact pairing to any rotated ordering.
This is a source identity, with no permutation-covariance premise on the
physical kernel. -/
theorem compactEuclideanOrder_wickIntegral_eq_schwinger
    {OS : OsterwalderSchraderAxioms d} {stage : OSIITimeContinuationStage d k}
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H)
    (rot : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (horth : rot.transpose * rot = 1) (hdet : rot.det = 1)
    (sigma : Equiv.Perm (Fin (k + 1)))
    (f : ZeroDiagonalSchwartz d (k + 1))
    (hcompact : HasCompactSupport (f.1 : NPointDomain d (k + 1) -> Complex))
    (hsupport : ∀ x ∈ tsupport (f.1 : NPointDomain d (k + 1) -> Complex),
      OSIIChapterV.reducedTimeProjectionCLM d k (fun j => rot.mulVec (x (sigma j))) ∈
        section43TimeStrictPositiveRegion k) :
    (∫ x : NPointDomain d (k + 1),
      H.kernel (fun j => wickRotatePoint (BHW.reducedDiffMapReal (k + 1) d
        (fun i => rot.mulVec (x (sigma i))) j)) * f.1 x) = OS.S (k + 1) f := by
  let p : ZeroDiagonalSchwartz d (k + 1) :=
    ⟨reindexSchwartz (d := d) sigma.symm f.1,
      f.2.compCLMOfContinuousLinearEquiv sigma.symm⟩
  let g := osiiEuclideanRotateZeroDiagonal rot horth p
  let ep := (LinearEquiv.funCongrLeft Real (SpacetimeDim d) sigma.symm).toContinuousLinearEquiv
  let er := osiiEuclideanRotateNPointCLE (n := k + 1) rot horth
  let e := er.trans ep
  let T := fun x : NPointDomain d (k + 1) => fun j => rot.mulVec (x (sigma j))
  have hg (x : NPointDomain d (k + 1)) : g.1 x = f.1 (e x) := rfl
  have hTe (x : NPointDomain d (k + 1)) : T (e x) = x := by
    change (fun j => rot.mulVec (rot.transpose.mulVec (x (sigma.symm (sigma j))))) = x
    ext j mu
    simp [Matrix.mulVec_mulVec, mul_eq_one_comm.mpr horth]
  have heT (x : NPointDomain d (k + 1)) : e (T x) = x := by
    change (fun j => rot.transpose.mulVec (rot.mulVec (x (sigma (sigma.symm j))))) = x
    ext j mu
    simp [Matrix.mulVec_mulVec, horth]
  have hgcompact : HasCompactSupport (g.1 : NPointDomain d (k + 1) -> Complex) :=
    hcompact.comp_homeomorph e.toHomeomorph
  have hgsupport : ∀ x ∈ tsupport (g.1 : NPointDomain d (k + 1) -> Complex),
      OSIIChapterV.reducedTimeProjectionCLM d k x ∈ section43TimeStrictPositiveRegion k := by
    intro x hx
    have hx' : e x ∈ tsupport (f.1 : NPointDomain d (k + 1) -> Complex) :=
      tsupport_comp_subset_preimage (f.1 : NPointDomain d (k + 1) -> Complex) e.continuous hx
    have h := hsupport (e x) hx'
    change OSIIChapterV.reducedTimeProjectionCLM d k (T (e x)) ∈ _ at h
    rwa [hTe] at h
  have hpair := H.compactChronological_wickIntegral_eq_schwinger
    Hstage Rstage g hgcompact hgsupport
  have hS : OS.S (k + 1) g = OS.S (k + 1) f := by
    apply (osiiEuclideanRotateZeroDiagonal_schwinger_eq OS rot horth hdet p).trans
    symm
    exact OS.E3_symmetric (k + 1) sigma.symm f p (fun _ => rfl)
  let A := fun x : NPointDomain d (k + 1) =>
    H.kernel (fun j => wickRotatePoint (BHW.reducedDiffMapReal (k + 1) d x j)) * g.1 x
  calc
    _ = ∫ x : NPointDomain d (k + 1), A (T x) := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [A, hg, heT]
      rfl
    _ = ∫ x : NPointDomain d (k + 1), A (fun j => rot.mulVec (x j)) :=
      BHW.integral_perm_eq_self sigma (fun x => A (fun j => rot.mulVec (x j)))
    _ = ∫ x : NPointDomain d (k + 1), A x := integral_orthogonal_eq_self rot horth A
    _ = OS.S (k + 1) g := hpair
    _ = OS.S (k + 1) f := hS

/-- Strictly positive successive time gaps exclude all full-point collisions. -/
theorem not_mem_CoincidenceLocus_of_reducedTimePositive
    (x : NPointDomain d (k + 1))
    (hx : OSIIChapterV.reducedTimeProjectionCLM d k x ∈
      section43TimeStrictPositiveRegion k) :
    x ∉ CoincidenceLocus d (k + 1) := by
  have hmono : StrictMono (fun j => x j 0) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro j
    have hj := hx j
    change 0 < x j.succ 0 - x j.castSucc 0 at hj
    exact sub_pos.mp hj
  rintro ⟨i, j, hij, heq⟩
  exact hij (hmono.injective (congrFun heq 0))

/-- Original-E1/E3 source comparison identifies any two ordered Euclidean
charts at every point in their common chamber. -/
theorem flatWick_euclideanOrder_eq
    {OS : OsterwalderSchraderAxioms d} {stage : OSIITimeContinuationStage d k}
    (H : OSIIReducedForwardTubeBoundaryData W)
    (Hstage : OSIIChapterV.HasCanonicalReducedCompactStageEdges OS stage)
    (Rstage : OSIIReducedForwardTubeTimeSliceRealizationData (A := stage) H)
    (rot rot' : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (horth : rot.transpose * rot = 1) (hdet : rot.det = 1)
    (horth' : rot'.transpose * rot' = 1) (hdet' : rot'.det = 1)
    (sigma sigma' : Equiv.Perm (Fin (k + 1)))
    (x : NPointDomain d (k + 1))
    (hx : OSIIChapterV.reducedTimeProjectionCLM d k (fun j => rot.mulVec (x (sigma j))) ∈
      section43TimeStrictPositiveRegion k)
    (hx' : OSIIChapterV.reducedTimeProjectionCLM d k (fun j => rot'.mulVec (x (sigma' j))) ∈
      section43TimeStrictPositiveRegion k) :
    H.kernel (fun j => wickRotatePoint (BHW.reducedDiffMapReal (k + 1) d
      (fun i => rot.mulVec (x (sigma i))) j)) =
    H.kernel (fun j => wickRotatePoint (BHW.reducedDiffMapReal (k + 1) d
      (fun i => rot'.mulVec (x (sigma' i))) j)) := by
  let T := fun (rho : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (pi : Equiv.Perm (Fin (k + 1))) (y : NPointDomain d (k + 1)) =>
      fun j => rho.mulVec (y (pi j))
  let U := fun rho pi => {y : NPointDomain d (k + 1) |
    OSIIChapterV.reducedTimeProjectionCLM d k (T rho pi y) ∈ section43TimeStrictPositiveRegion k}
  let F := fun rho pi (y : NPointDomain d (k + 1)) =>
    H.kernel (fun j => wickRotatePoint (BHW.reducedDiffMapReal (k + 1) d (T rho pi y) j))
  have hT rho pi : Continuous (T rho pi) := by dsimp [T]; fun_prop
  have hU rho pi : IsOpen (U rho pi) :=
    (isOpen_section43TimeStrictPositiveRegion k).preimage
      ((OSIIChapterV.reducedTimeProjectionCLM d k).continuous.comp (hT rho pi))
  have hF rho pi : ContinuousOn (F rho pi) (U rho pi) :=
    H.holomorphic.continuousOn.comp
      (continuous_osiiReducedWickRotateConfig.comp
        ((BHW.reducedDiffMapRealCLM (k + 1) d).continuous.comp (hT rho pi))).continuousOn
      (fun y hy => osiiReducedWickRotateConfig_mem_productForwardTube_of_strictPositive _ hy)
  have heq : Set.EqOn (F rot sigma) (F rot' sigma') (U rot sigma ∩ U rot' sigma') := by
    apply SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn
      ((hU rot sigma).inter (hU rot' sigma'))
      ((hF rot sigma).mono (fun y hy => hy.1))
      ((hF rot' sigma').mono (fun y hy => hy.2))
    intro phi hcompact hsupport
    have hflat : VanishesToInfiniteOrderOnCoincidence phi := by
      apply VanishesToInfiniteOrderOnCoincidence_of_tsupport_disjoint
      apply Set.disjoint_left.mpr
      intro y hy hcoin
      have hnot := not_mem_CoincidenceLocus_of_reducedTimePositive
        (T rot sigma y) (hsupport hy).1
      apply hnot
      obtain ⟨i, j, hij, heq⟩ := hcoin
      refine ⟨sigma.symm i, sigma.symm j, sigma.symm.injective.ne hij, ?_⟩
      simpa [T] using congrArg rot.mulVec heq
    let f : ZeroDiagonalSchwartz d (k + 1) := ⟨phi, hflat⟩
    exact (H.compactEuclideanOrder_wickIntegral_eq_schwinger
      Hstage Rstage rot horth hdet sigma f hcompact (fun y hy => (hsupport hy).1)).trans
        (H.compactEuclideanOrder_wickIntegral_eq_schwinger
          Hstage Rstage rot' horth' hdet' sigma' f hcompact
          (fun y hy => (hsupport hy).2)).symm
  exact heq ⟨hx, hx'⟩

end OSIIReducedForwardTubeBoundaryData

namespace OSIIChapterV.InitialGeneratedLogarithmicStageLevelData

variable {d : Nat} [NeZero d] {OS : OsterwalderSchraderAxioms d}

end OSIIChapterV.InitialGeneratedLogarithmicStageLevelData
end OSReconstruction
