import OSReconstruction.Wightman.Reconstruction.ForwardTubeDistributions
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIBlockRadialPartialConvolution

/-!
# OS II Chapter VI: Block Factorization of the Partial Kernel

The Chapter-VI regularizer is a product over complex spacetime-difference
blocks. This file proves the corresponding exact factorization of its partial
convolution kernel after the real integration variables are unflattened.

This is the neutral measure-theoretic layer behind the two-vector split in
OS II `(6.8)`: it makes no Hilbert-space estimate and no continuation claim.
Those remain separate analytic obligations.
-/

noncomputable section

open MeasureTheory
open scoped Classical

namespace OSReconstruction

/-- The partial-convolution kernel contributed by one complex spacetime
block. -/
def osiiStep4ComplexBlockPartialConvolutionKernel
    (q : Nat) (rho : Real)
    (z : Fin q -> Complex) (y' : Fin q -> Real) : Real :=
  osiiStep4PartialConvolutionKernel
    (osiiStep4ComplexBlockRadialG q rho) z y'

/-- The real integration density whose integral is the one-block partial
kernel. Keeping this function explicit is needed when one distinguished block
is split between the two OS Hilbert vectors. -/
def osiiStep4ComplexBlockPartialConvolutionIntegrand
    (q : Nat) (rho : Real)
    (z : Fin q -> Complex) (y' x' : Fin q -> Real) : Real :=
  osiiStep4ComplexBlockRadialG q rho
      (z - osiiStep4ComplexOfRealImag x' y') *
    osiiStep4ComplexBlockRadialG q rho
      (osiiStep4ComplexOfRealImag x' y')

theorem osiiStep4ComplexBlockPartialConvolutionKernel_eq_integral
    (q : Nat) (rho : Real)
    (z : Fin q -> Complex) (y' : Fin q -> Real) :
    osiiStep4ComplexBlockPartialConvolutionKernel q rho z y' =
      ∫ x' : Fin q -> Real,
        osiiStep4ComplexBlockPartialConvolutionIntegrand q rho z y' x' := by
  rfl

/-- The partial kernel of the product block regularizer is the product of
the corresponding one-block partial kernels. -/
theorem osiiStep4PartialConvolutionKernel_fullBlock_eq_prod
    (q k : Nat) (rho : Real)
    (z : Fin (k * q) -> Complex) (y' : Fin (k * q) -> Real) :
    osiiStep4PartialConvolutionKernel
        (osiiStep4FullBlockRadialG q k rho) z y' =
      Finset.univ.prod fun i : Fin k =>
        osiiStep4ComplexBlockPartialConvolutionKernel q rho
          ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z i)
          (fun mu => y' (finProdFinEquiv (i, mu))) := by
  rw [osiiStep4PartialConvolutionKernel]
  let H : (Fin (k * q) -> Real) -> Real := fun x =>
    osiiStep4FullBlockRadialG q k rho
        (z - osiiStep4ComplexOfRealImag x y') *
      osiiStep4FullBlockRadialG q k rho
        (osiiStep4ComplexOfRealImag x y')
  have hflatten :
      (∫ x : Fin (k * q) -> Real, H x) =
        ∫ x : Fin k -> Fin q -> Real,
          H (flattenCLEquivReal k q x) := by
    rw [show (fun x : Fin k -> Fin q -> Real =>
        H (flattenCLEquivReal k q x)) =
      fun x => H (flattenMeasurableEquiv k q x) by
        funext x
        congr 1
        ext a
        simp]
    exact ((flattenMeasurableEquiv_measurePreserving k q).integral_comp' H).symm
  change (∫ x : Fin (k * q) -> Real, H x) = _
  rw [hflatten]
  calc
    (∫ x : Fin k -> Fin q -> Real,
        osiiStep4FullBlockRadialG q k rho
            (z - osiiStep4ComplexOfRealImag
              (flattenCLEquivReal k q x) y') *
          osiiStep4FullBlockRadialG q k rho
            (osiiStep4ComplexOfRealImag
              (flattenCLEquivReal k q x) y')) =
        ∫ x : Fin k -> Fin q -> Real,
          Finset.univ.prod fun i : Fin k =>
            osiiStep4ComplexBlockRadialG q rho
                ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z i -
                  osiiStep4ComplexOfRealImag (x i)
                    (fun mu => y' (finProdFinEquiv (i, mu)))) *
              osiiStep4ComplexBlockRadialG q rho
                (osiiStep4ComplexOfRealImag (x i)
                  (fun mu => y' (finProdFinEquiv (i, mu)))) := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [osiiStep4FullBlockRadialG, Finset.prod_mul_distrib]
      congr 1
      · apply Finset.prod_congr rfl
        intro i _hi
        congr 1
        ext mu
        simp [osiiStep4ComplexOfRealImag]
      · apply Finset.prod_congr rfl
        intro i _hi
        congr 1
        ext mu
        simp [osiiStep4ComplexOfRealImag]
    _ = Finset.univ.prod fun i : Fin k =>
        osiiStep4ComplexBlockPartialConvolutionKernel q rho
          ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z i)
          (fun mu => y' (finProdFinEquiv (i, mu))) := by
      simpa [osiiStep4ComplexBlockPartialConvolutionKernel,
        osiiStep4PartialConvolutionKernel] using
        (MeasureTheory.integral_fintype_prod_volume_eq_prod
          (fun i : Fin k => fun x : Fin q -> Real =>
            osiiStep4ComplexBlockRadialG q rho
                ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z i -
                  osiiStep4ComplexOfRealImag x
                    (fun mu => y' (finProdFinEquiv (i, mu)))) *
              osiiStep4ComplexBlockRadialG q rho
                (osiiStep4ComplexOfRealImag x
                  (fun mu => y' (finProdFinEquiv (i, mu))))))

/-- Expand one selected block of the full kernel back into its defining real
integral while retaining all other one-block kernels as an exterior factor.
This is the exact shared-block form used before defining the two OS Hilbert
vectors in the Chapter-VI estimate. -/
theorem osiiStep4PartialConvolutionKernel_fullBlock_eq_integral_selectedBlock
    (q k : Nat) (rho : Real)
    (z : Fin (k * q) -> Complex) (y' : Fin (k * q) -> Real)
    (i0 : Fin k) :
    osiiStep4PartialConvolutionKernel
        (osiiStep4FullBlockRadialG q k rho) z y' =
      ∫ x' : Fin q -> Real,
        ((Finset.univ.erase i0).prod fun i : Fin k =>
          osiiStep4ComplexBlockPartialConvolutionKernel q rho
            ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z i)
            (fun mu => y' (finProdFinEquiv (i, mu)))) *
          osiiStep4ComplexBlockPartialConvolutionIntegrand q rho
            ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z i0)
            (fun mu => y' (finProdFinEquiv (i0, mu))) x' := by
  let K : Fin k -> Real := fun i =>
    osiiStep4ComplexBlockPartialConvolutionKernel q rho
      ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z i)
      (fun mu => y' (finProdFinEquiv (i, mu)))
  let C : Real := (Finset.univ.erase i0).prod K
  calc
    osiiStep4PartialConvolutionKernel
        (osiiStep4FullBlockRadialG q k rho) z y' =
        Finset.univ.prod K := by
      simpa [K] using
        osiiStep4PartialConvolutionKernel_fullBlock_eq_prod q k rho z y'
    _ = C * K i0 := by
      exact (Finset.prod_erase_mul Finset.univ K
        (Finset.mem_univ i0)).symm
    _ = C * ∫ x' : Fin q -> Real,
        osiiStep4ComplexBlockPartialConvolutionIntegrand q rho
          ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z i0)
          (fun mu => y' (finProdFinEquiv (i0, mu))) x' := by
      simpa [K] using congrArg (fun r : Real => C * r)
        (osiiStep4ComplexBlockPartialConvolutionKernel_eq_integral
          q rho
          ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z i0)
          (fun mu => y' (finProdFinEquiv (i0, mu))))
    _ = ∫ x' : Fin q -> Real,
        C * osiiStep4ComplexBlockPartialConvolutionIntegrand q rho
          ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z i0)
          (fun mu => y' (finProdFinEquiv (i0, mu))) x' := by
      rw [integral_const_mul]
    _ = ∫ x' : Fin q -> Real,
        ((Finset.univ.erase i0).prod fun i : Fin k =>
          osiiStep4ComplexBlockPartialConvolutionKernel q rho
            ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z i)
            (fun mu => y' (finProdFinEquiv (i, mu)))) *
          osiiStep4ComplexBlockPartialConvolutionIntegrand q rho
            ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z i0)
            (fun mu => y' (finProdFinEquiv (i0, mu))) x' := by
      rfl

/-- The product over every block except `i0` splits into the blocks before and
after `i0` in the canonical linear order. -/
theorem osiiStep4_prod_erase_univ_eq_Iio_mul_Ioi
    {k : Nat} (K : Fin k -> Real) (i0 : Fin k) :
    (Finset.univ.erase i0).prod K =
      (Finset.Iio i0).prod K * (Finset.Ioi i0).prod K := by
  have herase : (Finset.univ.erase i0 : Finset (Fin k)) =
      Finset.Iio i0 ∪ Finset.Ioi i0 := by
    ext i
    simp only [Finset.mem_erase, Finset.mem_univ, and_true,
      Finset.mem_union, Finset.mem_Iio, Finset.mem_Ioi]
    constructor
    · exact lt_or_gt_of_ne
    · rintro (h | h)
      · exact ne_of_lt h
      · exact ne_of_gt h
  rw [herase, Finset.prod_union (Finset.disjoint_Ioi_Iio i0).symm]

/-- Ordered form of the selected-block expansion. The factors before the
selected block, the two radial factors inside that block, and the factors
after it are now visibly separated. -/
theorem osiiStep4PartialConvolutionKernel_fullBlock_eq_integral_orderedSelectedBlock
    (q k : Nat) (rho : Real)
    (z : Fin (k * q) -> Complex) (y' : Fin (k * q) -> Real)
    (i0 : Fin k) :
    osiiStep4PartialConvolutionKernel
        (osiiStep4FullBlockRadialG q k rho) z y' =
      ∫ x' : Fin q -> Real,
        ((Finset.Iio i0).prod fun i : Fin k =>
          osiiStep4ComplexBlockPartialConvolutionKernel q rho
            ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z i)
            (fun mu => y' (finProdFinEquiv (i, mu)))) *
          osiiStep4ComplexBlockPartialConvolutionIntegrand q rho
            ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z i0)
            (fun mu => y' (finProdFinEquiv (i0, mu))) x' *
          ((Finset.Ioi i0).prod fun i : Fin k =>
            osiiStep4ComplexBlockPartialConvolutionKernel q rho
              ((osiiStep4ComplexBlockFlattenMeasurableEquiv k q).symm z i)
              (fun mu => y' (finProdFinEquiv (i, mu)))) := by
  rw [osiiStep4PartialConvolutionKernel_fullBlock_eq_integral_selectedBlock]
  apply integral_congr_ae
  filter_upwards with x'
  rw [osiiStep4_prod_erase_univ_eq_Iio_mul_Ioi]
  ring

end OSReconstruction
