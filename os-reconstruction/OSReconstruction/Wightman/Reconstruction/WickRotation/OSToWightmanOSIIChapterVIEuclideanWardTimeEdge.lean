import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEuclideanWardSource

/-!
# The original Euclidean Ward identity on the represented time edge

The compact tensor calculation fixes the relative sign between time and
spatial derivatives before any analytic continuation or boundary limit.
-/

noncomputable section

open Complex MeasureTheory Set Topology
open scoped Classical LineDeriv

set_option backward.isDefEq.respectTransparency false

namespace OSReconstruction

variable {d k : Nat} [NeZero d]

/-- The skew generator mixing Euclidean time with one spatial axis. -/
def osiiEuclideanTimeSpaceGenerator (a : Fin d) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) Real :=
  Matrix.single 0 a.succ 1 - Matrix.single a.succ 0 1

omit [NeZero d] in
theorem osiiEuclideanTimeSpaceGenerator_skew (a : Fin d) :
    (osiiEuclideanTimeSpaceGenerator a).transpose =
      -osiiEuclideanTimeSpaceGenerator a := by
  simp [osiiEuclideanTimeSpaceGenerator, Matrix.transpose_sub,
    Matrix.transpose_single, neg_sub]

namespace OSIIChapterVI

/-- Multiplication by a time coordinate, in the complex Schwartz topology. -/
def timeCoordinateMultiplier (j : Fin k) :
    SchwartzMap (Fin k -> Real) Complex →L[Complex]
      SchwartzMap (Fin k -> Real) Complex :=
  SchwartzMap.smulLeftCLM Complex (fun t : Fin k -> Real => (t j : Complex))

/-- Multiplication by a spatial coordinate in the native Euclidean space. -/
def spatialCoordinateMultiplier (j : Fin k) (a : Fin d) :
    SchwartzMap (Section43SpatialSpace d k) Complex →L[Complex]
      SchwartzMap (Section43SpatialSpace d k) Complex :=
  SchwartzMap.smulLeftCLM Complex
    (fun X : Section43SpatialSpace d k => (X (j, a) : Complex))

@[simp] theorem timeCoordinateMultiplier_apply (j : Fin k)
    (phi : SchwartzMap (Fin k -> Real) Complex) (t : Fin k -> Real) :
    timeCoordinateMultiplier j phi t = (t j : Complex) * phi t := by
  exact SchwartzMap.smulLeftCLM_apply_apply
    (Complex.ofRealCLM.comp (ContinuousLinearMap.proj j)).hasTemperateGrowth phi t

omit [NeZero d] in
@[simp] theorem spatialCoordinateMultiplier_apply (j : Fin k) (a : Fin d)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (X : Section43SpatialSpace d k) :
    spatialCoordinateMultiplier j a chi X = (X (j, a) : Complex) * chi X := by
  exact SchwartzMap.smulLeftCLM_apply_apply
    (Complex.ofRealCLM.comp (EuclideanSpace.proj (j, a))).hasTemperateGrowth chi X

set_option maxHeartbeats 600000 in
/-- The actual native tensor source has the Euclidean, not Lorentzian,
relative minus sign. -/
theorem euclideanWard_timeSpatialTensor (a : Fin d)
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    linearVectorFieldCLM
        (osiiDiagonalRealMatrixCLM (osiiEuclideanTimeSpaceGenerator a))
        (section43NPointTimeSpatialTensor d k phi chi) =
      ∑ j : Fin k,
        (section43NPointTimeSpatialTensor d k
          (∂_{(Pi.single j (1 : Real) : Fin k -> Real)} phi)
          (spatialCoordinateMultiplier j a chi) -
        section43NPointTimeSpatialTensor d k (timeCoordinateMultiplier j phi)
          (∂_{EuclideanSpace.single (j, a) (1 : Real)} chi)) := by
  ext x
  let v := osiiDiagonalRealMatrixCLM (osiiEuclideanTimeSpaceGenerator a) x
  have ht : section43QTimeCLM d k v =
      ∑ j : Fin k, x j a.succ • (Pi.single j (1 : Real) : Fin k -> Real) := by
    ext j
    simp [v, section43QTime, nPointTimeSpatialCLE,
      osiiEuclideanTimeSpaceGenerator, Matrix.sub_mulVec, Matrix.single_mulVec,
      Pi.single_apply, mul_ite,
      Function.update_of_ne (Ne.symm (Fin.succ_ne_zero a))]
  have hs : section43QSpatialCLM d k v =
      -(∑ j : Fin k, x j 0 • EuclideanSpace.single (j, a) (1 : Real)) := by
    ext i
    rcases i with ⟨j, b⟩
    by_cases h : b = a
    · subst b
      simp [v, section43QSpatial, nPointTimeSpatialCLE,
        osiiEuclideanTimeSpaceGenerator, Matrix.sub_mulVec, Matrix.single_mulVec,
        Pi.single_apply, mul_ite]
    · simp [v, section43QSpatial, nPointTimeSpatialCLE,
        osiiEuclideanTimeSpaceGenerator, Matrix.sub_mulVec, Matrix.single_mulVec,
        Prod.ext_iff, h]
  have hphi := (phi.hasFDerivAt (section43QTimeCLM d k x)).comp x
    (section43QTimeCLM d k).hasFDerivAt
  have hchi := (chi.hasFDerivAt (section43QSpatialCLM d k x)).comp x
    (section43QSpatialCLM d k).hasFDerivAt
  have hfun : (section43NPointTimeSpatialTensor d k phi chi :
      NPointDomain d k -> Complex) =
      fun y => phi (section43QTimeCLM d k y) * chi (section43QSpatialCLM d k y) := by
    funext y
    exact section43NPointTimeSpatialTensor_apply d k phi chi y
  have hd := (hphi.mul hchi).fderiv
  change fderiv Real
    (fun y => phi (section43QTimeCLM d k y) * chi (section43QSpatialCLM d k y)) x = _ at hd
  rw [linearVectorFieldCLM_apply, hfun, hd]
  change phi (section43QTimeCLM d k x) *
        fderiv Real (chi : Section43SpatialSpace d k -> Complex)
          (section43QSpatialCLM d k x) (section43QSpatialCLM d k v) +
      chi (section43QSpatialCLM d k x) *
        fderiv Real (phi : (Fin k -> Real) -> Complex)
          (section43QTimeCLM d k x) (section43QTimeCLM d k v) = _
  rw [ht, hs, map_neg, map_sum, map_sum]
  simp only [map_smul, SchwartzMap.sum_apply, SchwartzMap.sub_apply,
    section43NPointTimeSpatialTensor_apply, timeCoordinateMultiplier_apply,
    spatialCoordinateMultiplier_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hxTime (j : Fin k) : section43QTime (d := d) (n := k) x j = x j 0 := rfl
  have hxSpatial (j : Fin k) :
      section43QSpatial (d := d) (n := k) x (j, a) = x j a.succ := rfl
  simp [Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib,
    Finset.sum_neg_distrib,
    hxTime, hxSpatial, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg, add_comm]

end OSIIChapterVI

namespace OSIIChapterV

open OSIIChapterVI

variable [NeZero k]

/-- A fixed canonical cutoff extends the original compact-source Ward
identity to every spatial Schwartz source by continuity and density. -/
theorem canonicalReducedTimeCutoffSchwingerCLM_euclideanWard_tensor_eq_zero
    (OS : OsterwalderSchraderAxioms d)
    {compactCarrier : Set (Fin k -> Real)}
    (C : CanonicalReducedCompactCutoffData compactCarrier)
    (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) Real)
    (hY : Y.transpose = -Y)
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (hphi : HasCompactSupport (phi : (Fin k -> Real) -> Complex))
    (hcarrier : tsupport (phi : (Fin k -> Real) -> Complex) ⊆ compactCarrier)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    canonicalReducedTimeCutoffSchwingerCLM OS C.cutoff C.cutoff_support
      (linearVectorFieldCLM (osiiDiagonalRealMatrixCLM Y)
        (section43NPointTimeSpatialTensor d k phi chi)) = 0 := by
  let L := (canonicalReducedTimeCutoffSchwingerCLM OS C.cutoff C.cutoff_support).comp
    ((linearVectorFieldCLM (osiiDiagonalRealMatrixCLM Y)).comp
      (section43TimeSpatialTensorSpatialCLM d k phi))
  change L chi = 0
  refine (dense_section43Spatial_hasCompactSupport d k).induction ?_
    (isClosed_eq L.continuous continuous_const) chi
  intro kappa hkappa
  exact canonicalReducedTimeCutoffSchwingerCLM_euclideanWard_eq_zero
    OS C Y hY _
    (hasCompactSupport_section43NPointTimeSpatialTensor d k phi kappa hphi hkappa)
    (fun x hx => hcarrier
      (tsupport_section43NPointTimeSpatialTensor_subset_time_preimage d k phi kappa hx))

/-- The actual represented positive-real time edge satisfies the weak Ward
identity. The sole edge hypothesis is the existing invariant of the
original-OS continuation construction. -/
theorem HasCanonicalReducedCompactStageEdges.integral_euclideanWard
    {OS : OsterwalderSchraderAxioms d}
    {stage : OSIITimeContinuationStage d k}
    (H : HasCanonicalReducedCompactStageEdges OS stage)
    (a : Fin d)
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (hphi : SCV.SupportsInOpen (phi : (Fin k -> Real) -> Complex)
      (section43TimeStrictPositiveRegion k)) :
    (∑ j : Fin k,
      ((∫ t, stage.distribution (osiiPositiveRealTimeEmbed t)
          (spatialCoordinateMultiplier j a chi) *
          (∂_{(Pi.single j (1 : Real) : Fin k -> Real)} phi) t) -
      (∫ t, stage.distribution (osiiPositiveRealTimeEmbed t)
          (∂_{EuclideanSpace.single (j, a) (1 : Real)} chi) *
          timeCoordinateMultiplier j phi t))) = 0 := by
  obtain ⟨D⟩ := H (tsupport (phi : (Fin k -> Real) -> Complex))
    hphi.1.isCompact hphi.2
  let T := canonicalReducedTimeCutoffSchwingerCLM OS D.cutoff D.cutoff_support
  have hrep (psi : SchwartzMap (Fin k -> Real) Complex)
      (kappa : SchwartzMap (Section43SpatialSpace d k) Complex)
      (hs : tsupport (psi : (Fin k -> Real) -> Complex) ⊆ tsupport phi) :
      T (section43NPointTimeSpatialTensor d k psi kappa) =
        ∫ t, stage.distribution (osiiPositiveRealTimeEmbed t) kappa * psi t := by
    have h := D.edge.stage_represents kappa psi
      ⟨hphi.1.isCompact.of_isClosed_subset (isClosed_tsupport _) hs,
        hs.trans D.compactCarrier_subset⟩
    simpa only [ContinuousLinearMap.comp_apply,
      orderedTransportDistribution_orderedPullbackTimeSpatialTensor,
      section43TimeSpatialTensorCLM_apply] using h
  calc
    _ = ∑ j : Fin k,
        (T (section43NPointTimeSpatialTensor d k
          (∂_{(Pi.single j (1 : Real) : Fin k -> Real)} phi)
          (spatialCoordinateMultiplier j a chi)) -
        T (section43NPointTimeSpatialTensor d k (timeCoordinateMultiplier j phi)
          (∂_{EuclideanSpace.single (j, a) (1 : Real)} chi))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hrep _ _ (SchwartzMap.tsupport_lineDerivOp_subset _ _),
        hrep (timeCoordinateMultiplier j phi) _
          ((SchwartzMap.tsupport_smulLeftCLM_subset
            (fun t : Fin k -> Real => (t j : Complex)) phi).trans
              Set.inter_subset_left)]
    _ = T (linearVectorFieldCLM
        (osiiDiagonalRealMatrixCLM (osiiEuclideanTimeSpaceGenerator a))
        (section43NPointTimeSpatialTensor d k phi chi)) := by
      rw [euclideanWard_timeSpatialTensor, map_sum]
      simp only [map_sub]
    _ = 0 := canonicalReducedTimeCutoffSchwingerCLM_euclideanWard_tensor_eq_zero
      OS D.toCutoffData _ (osiiEuclideanTimeSpaceGenerator_skew a)
      phi hphi.1 Set.Subset.rfl chi

end OSIIChapterV
end OSReconstruction
