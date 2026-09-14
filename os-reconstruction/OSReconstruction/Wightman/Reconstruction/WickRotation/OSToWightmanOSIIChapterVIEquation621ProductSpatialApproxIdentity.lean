/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIEquation621WeightedDensityPointRecovery
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIReflectedOrbitSpatialProductFactorization













noncomputable section

open Complex
open scoped Classical

namespace OSReconstruction
namespace OSIIChapterV
namespace Section43ProductTimeApproximateIdentity

/-- Forget the time interpretation of a factorwise product approximate
identity and use its underlying finite-dimensional Schwartz family as an
equation-`(6.21)` spatial approximate identity. -/
noncomputable def toEquation621SpatialApproxIdentity
    {m : Nat}
    (I : Section43ProductTimeApproximateIdentity m) :
    OSIIEquation621SpatialApproxIdentityData m where
  test := I.test
  radius := I.radius
  nonneg := I.nonnegative
  real := I.real
  integral_eq_one := I.integral_one
  compactSupport := I.test_compact
  support_subset_ball := I.support
  radius_tendsto := I.radius_tendsto

/-- The flat spatial center regrouped into one `d`-dimensional point for
each Section-4.3 particle. -/
def spatialParticlePoint
    {d k : Nat}
    (x : Fin (k * d) -> Real)
    (c : Fin k) : Fin d -> Real :=
  fun mu => x (finProdFinEquiv (c, mu))

/-- The one-particle factor obtained by grouping the scalar factors belonging
to one Section-4.3 spatial particle. -/
noncomputable def spatialParticleFactor
    {d k : Nat}
    (I : Section43ProductTimeApproximateIdentity (k * d))
    (N : Nat) (c : Fin k) :
    SchwartzMap (Fin d -> Real) Complex :=
  (section43TimeProductSource fun mu : Fin d =>
    I.factors N (finProdFinEquiv (c, mu))).f

/-- The translated one-particle factor at the corresponding block of a flat
spatial center. -/
noncomputable def translatedSpatialParticleFactor
    {d k : Nat}
    (I : Section43ProductTimeApproximateIdentity (k * d))
    (x : Fin (k * d) -> Real)
    (N : Nat) (c : Fin k) :
    SchwartzMap (Fin d -> Real) Complex :=
  SCV.translateSchwartz (-(spatialParticlePoint x c))
    (I.spatialParticleFactor N c)

/-- A translated factorwise flat delta probe is exactly a particlewise
product in the native Section-4.3 spatial coordinates. -/
theorem section43Probe_eq_spatialProduct
    {d k : Nat}
    (I : Section43ProductTimeApproximateIdentity (k * d))
    (x : Fin (k * d) -> Real)
    (N : Nat) :
    I.toEquation621SpatialApproxIdentity.section43Probe x N =
      section43SpatialProductCMM d k
        (I.translatedSpatialParticleFactor x N) := by
  ext eta
  simp only [
    OSIIEquation621SpatialApproxIdentityData.section43Probe,
    OSIIEquation621SpatialApproxIdentityData.translatedTest,
    toEquation621SpatialApproxIdentity,
    section43SpatialFlatSchwartzCLE_symm_apply,
    SCV.translateSchwartz_apply,
    section43SpatialProductCMM_apply,
    section43SpatialSchwartzParticleCLE_symm_apply,
    SchwartzMap.productTensor_apply,
    translatedSpatialParticleFactor,
    spatialParticleFactor,
    Section43ProductTimeApproximateIdentity.test_apply,
    section43TimeProductSource,
    section43TimeProductTensor]
  rw [show
    (∏ j : Fin (k * d),
        (I.factors N j).f
          ((section43SpatialFlatCLE d k eta + -x) j)) =
      ∏ p : Fin k × Fin d,
        (I.factors N (finProdFinEquiv p)).f
          ((section43SpatialFlatCLE d k eta + -x)
            (finProdFinEquiv p)) by
      rw [← Equiv.prod_comp finProdFinEquiv]]
  simp only [Fintype.prod_prod_type, Pi.add_apply, Pi.neg_apply,
    section43SpatialFlatCLE_apply, section43SpatialParticleCLE_apply,
    spatialParticlePoint, Equiv.symm_apply_apply]

/-- After restoring the normalized spatial basepoint, the translated product
probe remains one product on the full `k + 1` particle list. -/
theorem section43SpatialBasepointLift_section43Probe_eq_product
    {d k : Nat} [NeZero d]
    (I : Section43ProductTimeApproximateIdentity (k * d))
    (rho : SchwartzMap (Fin d -> Real) Complex)
    (x : Fin (k * d) -> Real)
    (N : Nat) :
    section43SpatialBasepointLiftCLM d k rho
        (I.toEquation621SpatialApproxIdentity.section43Probe x N) =
      section43SpatialProductCMM d (k + 1)
        (Fin.cons rho (I.translatedSpatialParticleFactor x N)) := by
  rw [I.section43Probe_eq_spatialProduct]
  exact section43SpatialBasepointLift_product_eq d k rho _

/-- Scalar-coordinate inclusion of the `k` non-basepoint particles into a
`k + 1` particle absolute spatial configuration. -/
def targetTailSpatialScalarIndex
    (d k : Nat) (j : Fin (k * d)) : Fin ((k + 1) * d) :=
  let p := finProdFinEquiv.symm j
  finProdFinEquiv (p.1.succ, p.2)

@[simp]
theorem targetTailSpatialScalarIndex_pair
    (d k : Nat) (c : Fin k) (mu : Fin d) :
    targetTailSpatialScalarIndex d k (finProdFinEquiv (c, mu)) =
      finProdFinEquiv (c.succ, mu) := by
  simp [targetTailSpatialScalarIndex]

/-- Scalar-coordinate inclusion of the absolute basepoint particle. -/
def absoluteBasepointSpatialScalarIndex
    (d k : Nat) (mu : Fin d) : Fin ((k + 1) * d) :=
  finProdFinEquiv (0, mu)

/-- Prepend the zero spatial basepoint to a flat `k`-particle center. -/
def prependZeroSpatialPoint
    (d k : Nat) (x : Fin (k * d) -> Real) :
    Fin ((k + 1) * d) -> Real :=
  fun j =>
    let p := finProdFinEquiv.symm j
    Fin.cases 0
      (fun c => x (finProdFinEquiv (c, p.2))) p.1

@[simp]
theorem prependZeroSpatialPoint_basepoint
    (d k : Nat) (x : Fin (k * d) -> Real) (mu : Fin d) :
    prependZeroSpatialPoint d k x (finProdFinEquiv (0, mu)) = 0 := by
  simp [prependZeroSpatialPoint]

@[simp]
theorem prependZeroSpatialPoint_tail
    (d k : Nat) (x : Fin (k * d) -> Real)
    (c : Fin k) (mu : Fin d) :
    prependZeroSpatialPoint d k x (finProdFinEquiv (c.succ, mu)) =
      x (finProdFinEquiv (c, mu)) := by
  simp [prependZeroSpatialPoint]

@[simp]
theorem spatialParticlePoint_prependZeroSpatialPoint_zero
    (d k : Nat) (x : Fin (k * d) -> Real) :
    spatialParticlePoint (prependZeroSpatialPoint d k x) 0 = 0 := by
  funext mu
  exact prependZeroSpatialPoint_basepoint d k x mu

@[simp]
theorem spatialParticlePoint_prependZeroSpatialPoint_succ
    (d k : Nat) (x : Fin (k * d) -> Real) (c : Fin k) :
    spatialParticlePoint (prependZeroSpatialPoint d k x) c.succ =
      spatialParticlePoint x c := by
  funext mu
  exact prependZeroSpatialPoint_tail d k x c mu

/-- The target spatial approximate identity obtained from one coherent
factorwise family on all absolute `k + 1` particles by dropping its
basepoint scalar coordinates. -/
noncomputable def absoluteProductTargetSpatialApproxIdentity
    {d k : Nat}
    (I : Section43ProductTimeApproximateIdentity ((k + 1) * d)) :
    OSIIEquation621SpatialApproxIdentityData (k * d) :=
  (I.reindex (targetTailSpatialScalarIndex d k)
    ).toEquation621SpatialApproxIdentity

/-- The scale-dependent absolute basepoint factor inherited from the same
coherent product family.  Its unit integral is part of the factorwise
approximate-identity data, so changing the basepoint factor does not alter
the reduced target test. -/
noncomputable def absoluteProductSpatialBasepointCutoff
    {d k : Nat}
    (I : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (N : Nat) : NormalizedSpatialBasepointCutoff d where
  toSchwartz :=
    (I.reindex (absoluteBasepointSpatialScalarIndex d k)).test N
  integral_eq_one :=
    (I.reindex (absoluteBasepointSpatialScalarIndex d k)).integral_one N

/-- The basepoint cutoff is exactly the zero-th one-particle factor of the
absolute product family. -/
theorem absoluteProductSpatialBasepointCutoff_eq_particleFactor
    {d k : Nat}
    (I : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (N : Nat) :
    (I.absoluteProductSpatialBasepointCutoff N).toSchwartz =
      I.spatialParticleFactor N 0 := by
  rfl

/-- Restoring the scale-dependent basepoint to the target probe recovers the
single translated product on all absolute `k + 1` particles. -/
theorem absoluteProduct_basepointLift_targetProbe_eq_product
    {d k : Nat} [NeZero d]
    (I : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (x : Fin (k * d) -> Real)
    (N : Nat) :
    section43SpatialBasepointLiftCLM d k
        (I.absoluteProductSpatialBasepointCutoff N).toSchwartz
        (I.absoluteProductTargetSpatialApproxIdentity.section43Probe x N) =
      section43SpatialProductCMM d (k + 1)
        (I.translatedSpatialParticleFactor
          (prependZeroSpatialPoint d k x) N) := by
  let Itail := I.reindex (targetTailSpatialScalarIndex d k)
  rw [show I.absoluteProductTargetSpatialApproxIdentity =
      Itail.toEquation621SpatialApproxIdentity by rfl]
  rw [Itail.section43SpatialBasepointLift_section43Probe_eq_product]
  congr 1
  funext c
  refine Fin.cases ?_ ?_ c
  · rw [absoluteProductSpatialBasepointCutoff_eq_particleFactor]
    ext y
    simp [translatedSpatialParticleFactor]
  · intro c
    ext y
    simp [translatedSpatialParticleFactor, spatialParticleFactor,
      Itail,
      Section43ProductTimeApproximateIdentity.reindex]

/-- The coherent absolute product family supplies the exact rank-one target
source in every generator split.  Both blocks are literal subproducts of the
same `k + 1` particle probe. -/
theorem
    generatorSplitSpatialPullback_absoluteProduct_targetProbe_eq_twoBlock
    {d k : Nat} [NeZero d]
    (I : Section43ProductTimeApproximateIdentity ((k + 1) * d))
    (i : GeneratorIndex k)
    (x : Fin (k * d) -> Real)
    (N : Nat) :
    generatorSplitSpatialPullbackCLM (d := d) i
        (section43SpatialBasepointLiftCLM d k
          (I.absoluteProductSpatialBasepointCutoff N).toSchwartz
          (I.absoluteProductTargetSpatialApproxIdentity.section43Probe x N)) =
      section43TwoBlockSpatialProduct
        (section43SpatialProductCMM d i.n (fun a =>
          (I.translatedSpatialParticleFactor
            (prependZeroSpatialPoint d k x) N
            (i.leftAbsoluteIndex a)).conj))
        (section43SpatialProductCMM d i.m (fun b =>
          I.translatedSpatialParticleFactor
            (prependZeroSpatialPoint d k x) N
            (i.rightAbsoluteIndex b))) := by
  rw [I.absoluteProduct_basepointLift_targetProbe_eq_product]
  exact generatorSplitSpatialPullbackCLM_product_eq_twoBlock d k i _

end Section43ProductTimeApproximateIdentity
end OSIIChapterV
end OSReconstruction
