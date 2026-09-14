import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIChapterVIForwardTubeSupport

/-!
# Constructing a physical forward-tube realization from genuine spectrum

The existing constructive Fourier-Laplace kernel supplies holomorphy and
the regulated global bound. Compact imaginary sets bound the inverse wall
distance, and the existing flattening preserves the boundary integral.
This direction does not use the false compact-growth-to-spectrum contract.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace OSReconstruction.OSIIReducedForwardTubeSpectralData

variable {d k : Nat} [NeZero d]

private theorem norm_real_add_imag_le {m : Nat} (x y : Fin m -> Real) :
    ‖fun i => (x i : Complex) + (y i : Complex) * I‖ ≤ ‖x‖ + ‖y‖ := by
  apply (pi_norm_le_iff_of_nonneg (add_nonneg (norm_nonneg x) (norm_nonneg y))).mpr
  intro i
  exact (norm_add_le _ _).trans (add_le_add
    (by simpa using norm_le_pi_norm x i)
    (by simpa using norm_le_pi_norm y i))

/-- On each compact set of imaginary parts, the constructive kernel has
one polynomial bound in the complete real variables. The empty-complement
case is included, so this also applies to zero gap arity. -/
theorem flatKernel_compactSubsetGrowth (P : OSIIReducedForwardTubeSpectralData d k)
    (K : Set (Fin (k * (d + 1)) -> Real)) (hK : IsCompact K)
    (hKC : K ⊆ osiiReducedForwardFlatCone d k) :
    ∃ (C : Real) (N : Nat), 0 < C ∧
      ∀ (x y : Fin (k * (d + 1)) -> Real), y ∈ K ->
        ‖P.flatKernel (fun i => (x i : Complex) + (y i : Complex) * I)‖ ≤
          C * (1 + ‖x‖) ^ N := by
  obtain ⟨C, N, M, hC, hbound⟩ := P.flatKernel_vladimirov_growth
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn (continuous_id.continuousOn)
  have hreg : ContinuousOn
      (fun y : Fin (k * (d + 1)) -> Real =>
        1 + (Metric.infDist y (osiiReducedForwardFlatCone d k)ᶜ)⁻¹) K := by
    intro y hy
    apply (continuousAt_const.add (Metric.continuousAt_inv_infDist_pt ?_)).continuousWithinAt
    rw [isOpen_osiiReducedForwardFlatCone.isClosed_compl.closure_eq]
    exact fun h => h (hKC hy)
  obtain ⟨Q, hQ⟩ := hK.exists_bound_of_continuousOn hreg
  refine ⟨C * (1 + |R|) ^ N * (1 + |Q|) ^ M, N, by positivity, ?_⟩
  intro x y hy
  let z := fun i => (x i : Complex) + (y i : Complex) * I
  have hz : z ∈ osiiReducedForwardFlatDomain d k := by
    simpa [osiiReducedForwardFlatDomain, SCV.TubeDomain, z] using hKC hy
  have hnorm : 1 + ‖z‖ ≤ (1 + |R|) * (1 + ‖x‖) := by
    have hyR : ‖y‖ ≤ |R| := by simpa only [id_eq] using (hR y hy).trans (le_abs_self R)
    have hzxy := norm_real_add_imag_le x y
    change ‖z‖ ≤ ‖x‖ + ‖y‖ at hzxy
    nlinarith [mul_nonneg (abs_nonneg R) (norm_nonneg x)]
  have hregQ : 1 + (Metric.infDist y (osiiReducedForwardFlatCone d k)ᶜ)⁻¹ ≤ 1 + |Q| := by
    have h := (le_abs_self _).trans ((hQ y hy).trans (le_abs_self Q))
    simpa only [Real.norm_eq_abs] using le_trans h (le_add_of_nonneg_left zero_le_one)
  have hreg0 : 0 ≤ 1 + (Metric.infDist y (osiiReducedForwardFlatCone d k)ᶜ)⁻¹ :=
    add_nonneg zero_le_one (inv_nonneg.mpr Metric.infDist_nonneg)
  have hg := hbound z hz
  have him : (fun i => (z i).im) = y := by ext i; simp [z]
  rw [him] at hg
  calc
    ‖P.flatKernel z‖ ≤ C * (1 + ‖z‖) ^ N *
        (1 + (Metric.infDist y (osiiReducedForwardFlatCone d k)ᶜ)⁻¹) ^ M := hg
    _ ≤ C * ((1 + |R|) * (1 + ‖x‖)) ^ N * (1 + |Q|) ^ M := by
      gcongr <;> positivity
    _ = (C * (1 + |R|) ^ N * (1 + |Q|) ^ M) * (1 + ‖x‖) ^ N := by
      rw [mul_pow]
      ring

/-- The same compact-imaginary polynomial bound in native gap blocks. -/
theorem kernel_compactSubsetGrowth (P : OSIIReducedForwardTubeSpectralData d k)
    (K : Set (NPointDomain d k)) (hK : IsCompact K)
    (hKC : K ⊆ BHW.ProductForwardConeReal d k) :
    ∃ (C : Real) (N : Nat), 0 < C ∧
      ∀ (x y : NPointDomain d k), y ∈ K ->
        ‖P.kernel (fun j mu => (x j mu : Complex) + (y j mu : Complex) * I)‖ ≤
          C * (1 + ‖x‖) ^ N := by
  let e := flattenCLEquivReal k (d + 1)
  have heKC : e '' K ⊆ osiiReducedForwardFlatCone d k := by
    rintro p ⟨y, hy, rfl⟩
    have h := hKC hy
    change BHW.ProductForwardConeReal d k (BHW.unflattenCfgReal k d (e y))
    convert h using 1
    ext j mu
    change y (finProdFinEquiv.symm (finProdFinEquiv (j, mu))).1
      (finProdFinEquiv.symm (finProdFinEquiv (j, mu))).2 = y j mu
    simp
  obtain ⟨C, N, hC, hbound⟩ := P.flatKernel_compactSubsetGrowth (e '' K)
    (hK.image e.continuous) heKC
  refine ⟨C, N, hC, ?_⟩
  intro x y hy
  have hn : ‖e x‖ ≤ ‖x‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
    intro i
    change ‖x (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2‖ ≤ ‖x‖
    exact (norm_le_pi_norm (x (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2
      ).trans (norm_le_pi_norm x (finProdFinEquiv.symm i).1)
  have hg := hbound (e x) (e y) ⟨y, hy, rfl⟩
  have hz : BHW.flattenCfg k d
      (fun j mu => (x j mu : Complex) + (y j mu : Complex) * I) =
      fun i => (e x i : Complex) + (e y i : Complex) * I := by
    ext i
    rfl
  change ‖P.flatKernel (BHW.flattenCfg k d _)‖ ≤ _
  rw [hz]
  exact hg.trans (by gcongr)

/-- The full Schwartz boundary integral in native gap coordinates,
transported by the checked measure-preserving flattening. -/
theorem kernel_boundaryValue (P : OSIIReducedForwardTubeSpectralData d k)
    (eta : NPointDomain d k) (heta : eta ∈ BHW.ProductForwardConeReal d k)
    (f : SchwartzNPoint d k) :
    Tendsto (fun epsilon : Real => ∫ x : NPointDomain d k,
      P.kernel (fun j mu => (x j mu : Complex) +
        (epsilon : Complex) * (eta j mu : Complex) * I) * f x)
      (nhdsWithin 0 (Ioi 0)) (nhds (P.reducedBoundaryDistribution f)) := by
  let e := flattenCLEquivReal k (d + 1)
  have he : e eta ∈ osiiReducedForwardFlatCone d k := by
    change BHW.ProductForwardConeReal d k (BHW.unflattenCfgReal k d (e eta))
    convert heta using 1
    ext j mu
    change eta (finProdFinEquiv.symm (finProdFinEquiv (j, mu))).1
      (finProdFinEquiv.symm (finProdFinEquiv (j, mu))).2 = eta j mu
    simp
  have h := P.flatKernel_boundaryValue (e eta) he (_root_.flattenSchwartzNPoint (d := d) f)
  have hfun : (fun epsilon : Real => ∫ x : NPointDomain d k,
      P.kernel (fun j mu => (x j mu : Complex) +
        (epsilon : Complex) * (eta j mu : Complex) * I) * f x) =
      (fun epsilon : Real => ∫ x : Fin (k * (d + 1)) -> Real,
        P.flatKernel (fun i => (x i : Complex) +
          (epsilon : Complex) * (e eta i : Complex) * I) *
          _root_.flattenSchwartzNPoint (d := d) f x) := by
    funext epsilon
    rw [integral_flatten_change_of_variables k (d + 1)]
    apply integral_congr_ae
    filter_upwards with x
    rw [_root_.flattenSchwartzNPoint_apply, ContinuousLinearEquiv.symm_apply_apply]
    rfl
  rw [hfun]
  exact h

/-- The constructive spectral kernel realizes its own native boundary.
This is the valid spectrum-to-tube direction, independent of the legacy
reverse support implication. -/
def toForwardTubeBoundaryData (P : OSIIReducedForwardTubeSpectralData d k) :
    OSIIReducedForwardTubeBoundaryData P.reducedBoundaryDistribution where
  kernel := P.kernel
  holomorphic := P.kernel_holomorphic
  compactSubsetGrowth := P.kernel_compactSubsetGrowth
  boundaryValue := P.kernel_boundaryValue

end OSReconstruction.OSIIReducedForwardTubeSpectralData
