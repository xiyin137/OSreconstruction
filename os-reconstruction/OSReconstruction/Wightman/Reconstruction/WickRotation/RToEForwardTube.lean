import OSReconstruction.Wightman.Reconstruction.WickRotation.RToESpectralSupport
import OSReconstruction.Wightman.Reconstruction.WickRotation.ForwardTubeLorentz
import OSReconstruction.SCV.FourierLaplaceRepresentation

/-!
# The Wightman forward tube from its actual spectral distribution

The chosen analytic branch agrees with the canonical supported Fourier-Laplace
extension by boundary uniqueness. Its regulated growth therefore follows from
the proved Paley-Wiener estimate, not from a compact-height support axiom.
-/

noncomputable section

open Complex Set MeasureTheory Filter Topology

namespace OSReconstruction

variable {d : Nat} [NeZero d]

theorem rToEForwardConeFlat_salient (N : Nat) :
    IsSalientCone ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N) := by
  let e := flattenCLEquivReal N (d + 1)
  intro y hy hneg
  rw [show closure (e '' ForwardConeAbs d N) = e '' closure (ForwardConeAbs d N) from
    (e.toHomeomorph.image_closure _).symm] at hy hneg
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨x', hx', hxx'⟩ := hneg
  have heq : x' = -x := e.injective (by rw [hxx', map_neg])
  subst x'
  rw [forwardConeAbs_salient d N x hx hx', map_zero]

/-- The existing analytic Wightman branch is the Fourier-Laplace extension
of its actual momentum distribution, with no extra analytic assumptions. -/
theorem rToE_forwardTube_fourierLaplace (Wfn : WightmanFunctions d) (N : Nat)
    (hC_open : IsOpen ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N))
    (hC_conv : Convex Real ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N))
    (hC_cone : IsCone ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N))
    (hC_salient : IsSalientCone ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N))
    (z : Fin N → Fin (d + 1) → Complex) (hz : z ∈ ForwardTube d N) :
    (Wfn.spectrum_condition N).choose z =
      fourierLaplaceExtMultiDim ((flattenCLEquivReal N (d + 1)) '' ForwardConeAbs d N)
        hC_open hC_conv hC_cone hC_salient (rToEFullFrequencyDistribution Wfn N)
        (flattenCLEquiv N (d + 1) z) := by
  have hF := (Wfn.spectrum_condition N).choose_spec
  apply fourierLaplace_representation_of_supported_boundary_pi
    (ForwardConeAbs d N) (forwardConeAbs_nonempty d N)
    hC_open hC_conv hC_cone hC_salient (Wfn.spectrum_condition N).choose
    (by simpa [TubeDomainSetPi, forwardTube_eq_imPreimage] using hF.1) ?_
    (rToEWightmanCLM Wfn N) ?_ (rToEFullFrequencyDistribution Wfn N)
    (rToEFullFrequencyDistribution_dualSupport Wfn N) ?_ z
    (by simpa [TubeDomainSetPi, forwardTube_eq_imPreimage] using hz)
  · intro y hy f
    simpa only [Complex.ofReal_one, one_mul] using
      forward_tube_bv_integrable_of_compact (Wfn.spectrum_condition N).choose
        hF.1 hF.2.1 f y ((inForwardCone_iff_mem_forwardConeAbs y).mpr hy) 1 one_pos
  · intro eta heta f
    exact hF.2.2 f eta ((inForwardCone_iff_mem_forwardConeAbs eta).mpr heta)
  · intro f
    exact rToEFullFrequencyDistribution_boundary Wfn N f

/-- Regulated forward-tube growth for every Wightman arity, obtained from
positive spectral support and the canonical Fourier-Laplace construction. -/
theorem rToE_forwardTube_vladimirov_growth (Wfn : WightmanFunctions d) (N : Nat) :
    ∃ (A : Real) (p q : Nat), 0 < A ∧
      ∀ z ∈ ForwardTube d N,
        ‖(Wfn.spectrum_condition N).choose z‖ ≤ A * (1 + ‖z‖) ^ p *
          (1 + (Metric.infDist (fun j mu => (z j mu).im) (ForwardConeAbs d N)ᶜ)⁻¹) ^ q := by
  let e := flattenCLEquiv N (d + 1)
  let eR := flattenCLEquivReal N (d + 1)
  let C := eR '' ForwardConeAbs d N
  have hC_open : IsOpen C := forwardConeFlat_isOpen d N
  have hC_conv : Convex Real C := forwardConeFlat_convex d N
  have hC_cone : IsCone C := fun y hy t ht => forwardConeFlat_isCone d N t ht y hy
  have hC_salient : IsSalientCone C := rToEForwardConeFlat_salient N
  obtain ⟨A, p, q, hA, hbound⟩ := fourierLaplaceExtMultiDim_vladimirov_growth C
    hC_open hC_conv hC_cone hC_salient (rToEFullFrequencyDistribution Wfn N)
    (rToEFullFrequencyDistribution_dualSupport Wfn N)
  have hnorm (z : Fin N → Fin (d + 1) → Complex) : ‖e z‖ = ‖z‖ := by
    simp only [Pi.norm_def, e]
    congr 1
    simp only [Pi.nnnorm_def, flattenCLEquiv_apply]
    apply le_antisymm
    · apply Finset.sup_le
      intro i hi
      exact Finset.le_sup_of_le (Finset.mem_univ (finProdFinEquiv.symm i).1)
        (Finset.le_sup_of_le (Finset.mem_univ (finProdFinEquiv.symm i).2) (by simp))
    · apply Finset.sup_le
      intro j hj
      apply Finset.sup_le
      intro mu hmu
      exact Finset.le_sup_of_le (Finset.mem_univ (finProdFinEquiv (j, mu))) (by simp)
  have heR : Isometry eR := by
    rw [isometry_iff_dist_eq]
    intro x y
    simp only [dist_eq_norm]
    rw [← eR.map_sub, flattenCLEquivReal_norm_eq]
  have hcompl : Cᶜ = eR '' (ForwardConeAbs d N)ᶜ := by
    ext w
    constructor
    · intro hw
      exact ⟨eR.symm w, fun hc => hw ⟨eR.symm w, hc, eR.apply_symm_apply w⟩,
        eR.apply_symm_apply w⟩
    · rintro ⟨y, hy, rfl⟩ ⟨y', hy', heq⟩
      exact hy (eR.injective heq ▸ hy')
  refine ⟨A, p, q, hA, ?_⟩
  intro z hz
  rw [rToE_forwardTube_fourierLaplace Wfn N hC_open hC_conv hC_cone hC_salient z hz]
  have h := hbound (e z) (flattenCLEquiv_mem_tubeDomain_image
    (by simpa [TubeDomainSetPi, forwardTube_eq_imPreimage] using hz))
  rw [hnorm, flattenCLEquiv_im, hcompl, Metric.infDist_image heR] at h
  exact h

end OSReconstruction
