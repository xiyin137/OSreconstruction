import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEuclideanWardTimeEdge

/-!
# Lorentz generators on coupled time/spatial Schwartz sources

The boost generator has a plus sign between its two coordinate terms. The
spatial regulator derivative is a separate continuous source operator.
-/

noncomputable section

open Complex Set
open scoped Classical LineDeriv

set_option backward.isDefEq.respectTransparency false

namespace OSReconstruction

variable {d k : Nat}

private theorem tensor_apply
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (p : Section43TimeSpatialSpace d k) :
    section43TimeSpatialTensor d k phi chi p = phi p.1 * chi p.2 :=
  section43TimeSpatialTensor_apply d k phi chi p.1 p.2

/-- Embed one temporal coefficient per gap along a fixed spatial axis. -/
def osiiSpatialAxisCLM (d k : Nat) (a : Fin d) :
    (Fin k -> Real) →L[Real] Section43SpatialSpace d k :=
  ∑ j : Fin k, (ContinuousLinearMap.proj j).smulRight
    (EuclideanSpace.single (j, a) (1 : Real))

@[simp] theorem osiiSpatialAxisCLM_apply (a : Fin d) (t : Fin k -> Real) :
    osiiSpatialAxisCLM d k a t =
      ∑ j : Fin k, t j • EuclideanSpace.single (j, a) (1 : Real) := by
  simp [osiiSpatialAxisCLM]

/-- The simultaneous real boost vector field in all gap blocks. -/
def osiiCoupledBoostGenerator (d k : Nat) (a : Fin d) :
    Section43TimeSpatialSpace d k →L[Real] Section43TimeSpatialSpace d k :=
  (ContinuousLinearMap.pi fun j : Fin k =>
    (EuclideanSpace.proj (j, a)).comp
      (ContinuousLinearMap.snd Real (Fin k -> Real) (Section43SpatialSpace d k))).prod
    ((osiiSpatialAxisCLM d k a).comp
      (ContinuousLinearMap.fst Real (Fin k -> Real) (Section43SpatialSpace d k)))

@[simp] theorem osiiCoupledBoostGenerator_apply (a : Fin d)
    (p : Section43TimeSpatialSpace d k) :
    osiiCoupledBoostGenerator d k a p =
      (fun j => p.2 (j, a), osiiSpatialAxisCLM d k a p.1) := rfl

/-- The full coupled Schwartz boost generator. -/
def osiiCoupledBoostDeriv (d k : Nat) (a : Fin d) :
    SchwartzMap (Section43TimeSpatialSpace d k) Complex →L[Complex]
      SchwartzMap (Section43TimeSpatialSpace d k) Complex :=
  OSIIChapterVI.linearVectorFieldCLM (osiiCoupledBoostGenerator d k a)

/-- Spatial differentiation of a genuinely coupled Schwartz source. -/
def osiiCoupledSpatialDeriv (d k : Nat) (v : Section43SpatialSpace d k) :
    SchwartzMap (Section43TimeSpatialSpace d k) Complex →L[Complex]
      SchwartzMap (Section43TimeSpatialSpace d k) Complex :=
  LineDeriv.lineDerivOpCLM Complex
    (SchwartzMap (Section43TimeSpatialSpace d k) Complex)
    ((0 : Fin k -> Real), v)

private theorem fderiv_timeSpatialTensor_apply
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex)
    (p v : Section43TimeSpatialSpace d k) :
    fderiv Real (section43TimeSpatialTensor d k phi chi :
        Section43TimeSpatialSpace d k -> Complex) p v =
      fderiv Real (phi : (Fin k -> Real) -> Complex) p.1 v.1 * chi p.2 +
      phi p.1 * fderiv Real (chi : Section43SpatialSpace d k -> Complex) p.2 v.2 := by
  have hphi := (phi.hasFDerivAt p.1).comp p
    (ContinuousLinearMap.fst Real (Fin k -> Real) (Section43SpatialSpace d k)).hasFDerivAt
  have hchi := (chi.hasFDerivAt p.2).comp p
    (ContinuousLinearMap.snd Real (Fin k -> Real) (Section43SpatialSpace d k)).hasFDerivAt
  have hfun : (section43TimeSpatialTensor d k phi chi :
      Section43TimeSpatialSpace d k -> Complex) = fun q => phi q.1 * chi q.2 := by
    funext q
    exact section43TimeSpatialTensor_apply d k phi chi q.1 q.2
  have hd := (hphi.mul hchi).fderiv
  change fderiv Real (fun q : Section43TimeSpatialSpace d k => phi q.1 * chi q.2) p = _ at hd
  rw [hfun, hd]
  change phi p.1 * fderiv Real (chi : Section43SpatialSpace d k -> Complex) p.2 v.2 +
      chi p.2 * fderiv Real (phi : (Fin k -> Real) -> Complex) p.1 v.1 = _
  ring

@[simp] theorem osiiCoupledSpatialDeriv_tensor
    (v : Section43SpatialSpace d k)
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    osiiCoupledSpatialDeriv d k v (section43TimeSpatialTensor d k phi chi) =
      section43TimeSpatialTensor d k phi (∂_{v} chi) := by
  ext p
  change fderiv Real (section43TimeSpatialTensor d k phi chi :
    Section43TimeSpatialSpace d k -> Complex) p (0, v) = _
  rw [fderiv_timeSpatialTensor_apply]
  simp [tensor_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]

@[simp] theorem osiiCoupledSpatialDeriv_smul
    (r : Real) (v : Section43SpatialSpace d k) :
    osiiCoupledSpatialDeriv d k (r • v) =
      (r : Complex) • osiiCoupledSpatialDeriv d k v := by
  ext Phi p
  change fderiv Real (Phi : Section43TimeSpatialSpace d k -> Complex) p (0, r • v) =
    (r : Complex) * fderiv Real (Phi : Section43TimeSpatialSpace d k -> Complex) p (0, v)
  rw [show ((0 : Fin k -> Real), r • v) = r • ((0 : Fin k -> Real), v) by simp,
    map_smul]
  exact Complex.real_smul

theorem osiiCoupledSpatialDeriv_axis_tensor
    (a : Fin d) (y : Fin k -> Real)
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    osiiCoupledSpatialDeriv d k (osiiSpatialAxisCLM d k a y)
        (section43TimeSpatialTensor d k phi chi) =
      ∑ j : Fin k, (y j : Complex) • section43TimeSpatialTensor d k phi
        (∂_{EuclideanSpace.single (j, a) (1 : Real)} chi) := by
  rw [osiiCoupledSpatialDeriv_tensor]
  ext p
  simp [tensor_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, map_smul,
    Finset.mul_sum, mul_left_comm]

theorem osiiCoupledBoostDeriv_tensor (a : Fin d)
    (phi : SchwartzMap (Fin k -> Real) Complex)
    (chi : SchwartzMap (Section43SpatialSpace d k) Complex) :
    osiiCoupledBoostDeriv d k a (section43TimeSpatialTensor d k phi chi) =
      ∑ j : Fin k,
        (section43TimeSpatialTensor d k
          (∂_{(Pi.single j (1 : Real) : Fin k -> Real)} phi)
          (OSIIChapterVI.spatialCoordinateMultiplier j a chi) +
        section43TimeSpatialTensor d k (OSIIChapterVI.timeCoordinateMultiplier j phi)
          (∂_{EuclideanSpace.single (j, a) (1 : Real)} chi)) := by
  ext p
  change fderiv Real (section43TimeSpatialTensor d k phi chi :
    Section43TimeSpatialSpace d k -> Complex) p (osiiCoupledBoostGenerator d k a p) = _
  rw [fderiv_timeSpatialTensor_apply, osiiCoupledBoostGenerator_apply]
  have ht : (fun j : Fin k => p.2 (j, a)) =
      ∑ j : Fin k, p.2 (j, a) • (Pi.single j (1 : Real) : Fin k -> Real) := by
    ext j
    simp [Pi.single_apply, mul_ite]
  simp only [ht, osiiSpatialAxisCLM_apply, map_sum, map_smul,
    SchwartzMap.sum_apply, SchwartzMap.add_apply,
    tensor_apply, OSIIChapterVI.timeCoordinateMultiplier_apply,
    OSIIChapterVI.spatialCoordinateMultiplier_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  simp [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum,
    mul_left_comm, mul_assoc]

@[simp] theorem osiiCoupledBoostDeriv_zero_arity (a : Fin d)
    (Phi : SchwartzMap (Section43TimeSpatialSpace d 0) Complex) :
    osiiCoupledBoostDeriv d 0 a Phi = 0 := by
  ext p
  change fderiv Real (Phi : Section43TimeSpatialSpace d 0 -> Complex) p
    (osiiCoupledBoostGenerator d 0 a p) = 0
  rw [show osiiCoupledBoostGenerator d 0 a p = 0 from Subsingleton.elim _ _, map_zero]

end OSReconstruction
