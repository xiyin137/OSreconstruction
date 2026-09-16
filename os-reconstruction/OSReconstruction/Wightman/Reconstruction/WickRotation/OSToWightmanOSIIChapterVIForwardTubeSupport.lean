/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIFullBoundary
















noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

namespace OSReconstruction

variable {d k : Nat}

/-- A holomorphic reduced forward-tube realization of a fixed tempered
boundary distribution, with the compact-subset growth required by the
Vladimirov support theorem.

Lorentz/BHW construction of this datum is intentionally not folded into the
Chapter VI time-growth package: time-boundary existence and full forward-tube
continuation are distinct obligations. -/
structure OSIIReducedForwardTubeBoundaryData
    (W : SchwartzNPoint d k →L[Complex] Complex) where
  kernel : (Fin k -> Fin (d + 1) -> Complex) -> Complex
  holomorphic :
    DifferentiableOn Complex kernel
      (TubeDomainSetPi (BHW.ProductForwardConeReal d k))
  compactSubsetGrowth :
    forall K : Set (Fin k -> Fin (d + 1) -> Real),
      IsCompact K -> K ⊆ BHW.ProductForwardConeReal d k ->
        exists C : Real, exists N : Nat, 0 < C /\
          forall (x y : Fin k -> Fin (d + 1) -> Real), y ∈ K ->
            norm (kernel (fun j mu =>
              (x j mu : Complex) + (y j mu : Complex) * I)) <=
                C * (1 + norm x) ^ N
  boundaryValue :
    forall eta : Fin k -> Fin (d + 1) -> Real,
      eta ∈ BHW.ProductForwardConeReal d k ->
        forall phi : SchwartzNPoint d k,
          Tendsto
            (fun epsilon : Real =>
              ∫ x : NPointDomain d k,
                kernel (fun j mu =>
                  (x j mu : Complex) +
                    (epsilon : Complex) * (eta j mu : Complex) * I) *
                  phi x)
            (nhdsWithin 0 (Ioi 0))
            (nhds (W phi))

namespace OSIIReducedForwardTubeBoundaryData

/-- Transport a forward-tube realization across an equality of its tempered
boundary distribution.  The analytic kernel and all of its estimates are
unchanged. -/
def congrBoundary
    {W U : SchwartzNPoint d k →L[Complex] Complex}
    (H : OSIIReducedForwardTubeBoundaryData W)
    (h : W = U) :
    OSIIReducedForwardTubeBoundaryData U := by
  subst U
  exact H

@[simp] theorem congrBoundary_kernel
    {W U : SchwartzNPoint d k →L[Complex] Complex}
    (H : OSIIReducedForwardTubeBoundaryData W)
    (h : W = U) :
    (H.congrBoundary h).kernel = H.kernel := by
  subst U
  rfl

/-- The image cone used by the general Pi-coordinate Vladimirov theorem is
the flattened cone used by the active reduced Paley-Wiener package. -/
theorem flattenCLEquivReal_image_productForwardConeReal :
    (flattenCLEquivReal k (d + 1)) ''
        BHW.ProductForwardConeReal d k =
      osiiReducedForwardFlatCone d k := by
  ext u
  constructor
  · rintro ⟨eta, heta, rfl⟩
    have hflat :
        flattenCLEquivReal k (d + 1) eta =
          BHW.flattenCfgReal k d eta := by
      ext i
      simp [BHW.flattenCfgReal, flattenCLEquivReal_apply]
    change
      BHW.unflattenCfgReal k d
          (flattenCLEquivReal k (d + 1) eta) ∈
        BHW.ProductForwardConeReal d k
    rw [hflat, BHW.unflatten_flatten_cfg_real]
    exact heta
  · intro hu
    refine ⟨BHW.unflattenCfgReal k d u, hu, ?_⟩
    ext i
    change u (finProdFinEquiv (finProdFinEquiv.symm i)) = u i
    exact congrArg u (finProdFinEquiv.apply_symm_apply i)

variable [NeZero d]

/-- Every positive interior slice of a reduced forward-tube realization is
integrable against an arbitrary reduced Schwartz test.  This is the analytic
fact needed to justify time--spatial Fubini comparisons of boundary pairings. -/
theorem boundarySlice_integrable
    (H : OSIIReducedForwardTubeBoundaryData W)
    (eta : Fin k -> Fin (d + 1) -> Real)
    (heta : eta ∈ BHW.ProductForwardConeReal d k)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (phi : SchwartzNPoint d k) :
    Integrable
      (fun x : NPointDomain d k =>
        H.kernel (fun j mu =>
          (x j mu : Complex) +
            (epsilon : Complex) * (eta j mu : Complex) * I) *
          phi x) := by
  let y : Fin k -> Fin (d + 1) -> Real := epsilon • eta
  have hy : y ∈ BHW.ProductForwardConeReal d k := by
    intro i
    simpa [y, Pi.smul_apply] using
      BHW.inOpenForwardCone_smul_pos (d := d) (heta i) hepsilon
  obtain ⟨C, N, hC, hbound⟩ :=
    H.compactSubsetGrowth {y} isCompact_singleton
      (by simpa [Set.singleton_subset_iff] using hy)
  let g : NPointDomain d k -> Complex := fun x =>
    H.kernel (fun j mu =>
      (x j mu : Complex) +
        (epsilon : Complex) * (eta j mu : Complex) * I)
  have hslice_mem : forall x : NPointDomain d k,
      (fun j mu =>
        (x j mu : Complex) +
          (epsilon : Complex) * (eta j mu : Complex) * I) ∈
        TubeDomainSetPi (BHW.ProductForwardConeReal d k) := by
    intro x
    have hy' : (fun j mu => epsilon * eta j mu) ∈
        BHW.ProductForwardConeReal d k := by
      rw [show (fun j mu => epsilon * eta j mu) = epsilon • eta by
        ext j mu
        rfl]
      exact hy
    simpa [TubeDomainSetPi, Complex.ofReal_mul, mul_assoc] using hy'
  have hg_cont : Continuous g := by
    apply ContinuousOn.comp_continuous H.holomorphic.continuousOn
    · fun_prop
    · exact hslice_mem
  apply polynomial_growth_mul_schwartz_integrable g
    hg_cont.aestronglyMeasurable C N hC
  intro x
  have hx := hbound x y (Set.mem_singleton y)
  simpa [g, y, Pi.smul_apply, Complex.ofReal_mul, mul_assoc] using hx

end OSIIReducedForwardTubeBoundaryData

namespace OSIIFullTimeStageVladimirovGrowthData

variable [NeZero d]
variable {A : OSIITimeContinuationStage d k}

end OSIIFullTimeStageVladimirovGrowthData

end OSReconstruction
