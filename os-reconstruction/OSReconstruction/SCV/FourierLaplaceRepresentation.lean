/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import Init
import OSReconstruction.SCV.ConeDefs
import OSReconstruction.SCV.DistributionalUniqueness
import OSReconstruction.SCV.LaplaceSchwartz
import OSReconstruction.SCV.PaleyWienerSchwartz
import OSReconstruction.Wightman.Reconstruction.ForwardTubeDistributions
import OSReconstruction.Wightman.SchwartzTensorProduct
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Fourier-Laplace representation from supported boundary values

This comparison uses an independently supplied spectral distribution. Slice
integrability is explicit, so a nonintegrable Bochner integral cannot masquerade
as a zero boundary value. No boundary-to-spectrum inference is made.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology

/-- Every interior slice of a supported Fourier-Laplace extension can be
paired with every Schwartz test. The cone-boundary regulator is fixed on a
single slice. -/
theorem fourierLaplaceExtMultiDim_slice_integrable {m : Nat}
    (C : Set (Fin m → Real)) (hC_open : IsOpen C) (hC_conv : Convex Real C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C)
    (T : SchwartzMap (Fin m → Real) Complex →L[Complex] Complex)
    (hT : HasFourierSupportInDualCone C T)
    (y : Fin m → Real) (hy : y ∈ C)
    (f : SchwartzMap (Fin m → Real) Complex) :
    Integrable (fun x : Fin m → Real =>
      fourierLaplaceExtMultiDim C hC_open hC_conv hC_cone hC_salient T
        (fun i => (x i : Complex) + (y i : Complex) * I) * f x) := by
  let G := fourierLaplaceExtMultiDim C hC_open hC_conv hC_cone hC_salient T
  have hg := fourierLaplaceExtMultiDim_holomorphic C hC_open hC_conv hC_cone hC_salient T hT
  have hmem (x : Fin m → Real) :
      (fun i => (x i : Complex) + (y i : Complex) * I) ∈ SCV.TubeDomain C := by
    simpa [SCV.TubeDomain] using hy
  have hcont : Continuous (fun x : Fin m → Real =>
      G (fun i => (x i : Complex) + (y i : Complex) * I)) :=
    hg.continuousOn.comp_continuous (by fun_prop) hmem
  obtain ⟨A, N, M, hA, hbound⟩ :=
    fourierLaplaceExtMultiDim_vladimirov_growth C hC_open hC_conv hC_cone hC_salient T hT
  have hd : 0 ≤ Metric.infDist y Cᶜ := Metric.infDist_nonneg
  apply SCV.integrable_poly_growth_schwartz _ hcont.aestronglyMeasurable
    (A * (1 + ‖y‖) ^ N * (1 + (Metric.infDist y Cᶜ)⁻¹) ^ M) N _ f
  intro x
  have hz : ‖(fun i => (x i : Complex) + (y i : Complex) * I)‖ ≤ ‖x‖ + ‖y‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    calc
      ‖(x i : Complex) + (y i : Complex) * I‖ ≤ ‖(x i : Complex)‖ + ‖(y i : Complex) * I‖ := norm_add_le _ _
      _ = ‖x i‖ + ‖y i‖ := by simp
      _ ≤ ‖x‖ + ‖y‖ := add_le_add (norm_le_pi_norm x i) (norm_le_pi_norm y i)
  have hz' : 1 + ‖(fun i => (x i : Complex) + (y i : Complex) * I)‖ ≤
      (1 + ‖y‖) * (1 + ‖x‖) := by
    nlinarith [norm_nonneg x, norm_nonneg y]
  calc
    ‖G (fun i => (x i : Complex) + (y i : Complex) * I)‖ ≤
        A * (1 + ‖(fun i => (x i : Complex) + (y i : Complex) * I)‖) ^ N *
          (1 + (Metric.infDist y Cᶜ)⁻¹) ^ M := by simpa using hbound _ (hmem x)
    _ ≤ A * ((1 + ‖y‖) * (1 + ‖x‖)) ^ N *
          (1 + (Metric.infDist y Cᶜ)⁻¹) ^ M := by gcongr
    _ = _ := by rw [mul_pow]; ring

/-- A holomorphic function with integrable Schwartz slices and the boundary
of a supported spectral distribution is its Fourier-Laplace extension. -/
theorem fourierLaplace_representation_of_supported_boundary {m : Nat}
    (C : Set (Fin m → Real)) (hC_open : IsOpen C) (hC_conv : Convex Real C)
    (hC_cone : IsCone C) (hC_salient : IsSalientCone C) (hC_ne : C.Nonempty)
    (F : (Fin m → Complex) → Complex)
    (hF : DifferentiableOn Complex F (SCV.TubeDomain C))
    (T : SchwartzMap (Fin m → Real) Complex →L[Complex] Complex)
    (hT : HasFourierSupportInDualCone C T)
    (hF_int : ∀ y ∈ C, ∀ f : SchwartzMap (Fin m → Real) Complex,
      Integrable (fun x : Fin m → Real =>
        F (fun i => (x i : Complex) + (y i : Complex) * I) * f x))
    (hF_bv : ∀ eta ∈ C, ∀ f : SchwartzMap (Fin m → Real) Complex,
      Tendsto (fun epsilon : Real => ∫ x : Fin m → Real,
        F (fun i => (x i : Complex) + (epsilon : Complex) * (eta i : Complex) * I) * f x)
        (nhdsWithin 0 (Ioi 0)) (nhds (T (physicsFourierFlatCLM f)))) :
    Set.EqOn F (fourierLaplaceExtMultiDim C hC_open hC_conv hC_cone hC_salient T)
      (SCV.TubeDomain C) := by
  let G := fourierLaplaceExtMultiDim C hC_open hC_conv hC_cone hC_salient T
  have hG := fourierLaplaceExtMultiDim_holomorphic C hC_open hC_conv hC_cone hC_salient T hT
  have hG_int := fourierLaplaceExtMultiDim_slice_integrable C hC_open hC_conv hC_cone hC_salient T hT
  have hG_bv := fourierLaplaceExtMultiDim_boundaryValue C hC_open hC_conv hC_cone hC_salient hC_ne T hT
  have hzero := SCV.distributional_uniqueness_tube_of_zero_bv
    hC_open hC_conv hC_ne (fun t ht y hy => hC_cone y hy t ht)
    (hF.sub hG) (G := fun z => F z - G z) ?_ ?_
  · intro z hz
    exact sub_eq_zero.mp (hzero z hz)
  · intro y hy f
    convert (hF_int y hy f).sub (hG_int y hy f) using 1 <;>
      ext x <;> simp [G, sub_mul]
  · intro f eta heta
    have hlim := (hF_bv eta heta f).sub (hG_bv eta heta f)
    simp only [sub_self] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    have hy := hC_cone eta heta epsilon hepsilon
    have hiF := hF_int (epsilon • eta) hy f
    have hiG := hG_int (epsilon • eta) hy f
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, mul_assoc] at hiF hiG
    simpa only [sub_mul, mul_assoc] using (integral_sub hiF hiG).symm

/-- The supported-boundary comparison in nested spacetime coordinates.
Flattening is measure preserving, so no Fourier or volume factor is lost. -/
theorem fourierLaplace_representation_of_supported_boundary_pi {n d : Nat}
    (C : Set (Fin n → Fin (d + 1) → Real)) (hC_ne : C.Nonempty)
    (hCflat_open : IsOpen ((flattenCLEquivReal n (d + 1)) '' C))
    (hCflat_conv : Convex Real ((flattenCLEquivReal n (d + 1)) '' C))
    (hCflat_cone : IsCone ((flattenCLEquivReal n (d + 1)) '' C))
    (hCflat_salient : IsSalientCone ((flattenCLEquivReal n (d + 1)) '' C))
    (F : (Fin n → Fin (d + 1) → Complex) → Complex)
    (hF : DifferentiableOn Complex F (TubeDomainSetPi C))
    (hF_int : ∀ y ∈ C, ∀ f : SchwartzMap (Fin n → Fin (d + 1) → Real) Complex,
      Integrable (fun x : Fin n → Fin (d + 1) → Real =>
        F (fun j mu => (x j mu : Complex) + (y j mu : Complex) * I) * f x))
    (W : SchwartzMap (Fin n → Fin (d + 1) → Real) Complex →L[Complex] Complex)
    (hF_bv : ∀ eta ∈ C, ∀ f : SchwartzMap (Fin n → Fin (d + 1) → Real) Complex,
      Tendsto (fun epsilon : Real => ∫ x : Fin n → Fin (d + 1) → Real,
        F (fun j mu => (x j mu : Complex) + (epsilon : Complex) * (eta j mu : Complex) * I) * f x)
        (nhdsWithin 0 (Ioi 0)) (nhds (W f)))
    (T : SchwartzMap (Fin (n * (d + 1)) → Real) Complex →L[Complex] Complex)
    (hT : HasFourierSupportInDualCone ((flattenCLEquivReal n (d + 1)) '' C) T)
    (hboundary : ∀ f : SchwartzMap (Fin (n * (d + 1)) → Real) Complex,
      W (SchwartzMap.compCLMOfContinuousLinearEquiv Complex (flattenCLEquivReal n (d + 1)) f) =
        T (physicsFourierFlatCLM f)) :
    ∀ z ∈ TubeDomainSetPi C,
      F z = fourierLaplaceExtMultiDim ((flattenCLEquivReal n (d + 1)) '' C)
        hCflat_open hCflat_conv hCflat_cone hCflat_salient T (flattenCLEquiv n (d + 1) z) := by
  let e := flattenCLEquiv n (d + 1)
  let eR := flattenCLEquivReal n (d + 1)
  let Fflat := F ∘ e.symm
  have he (a b : Fin n → Fin (d + 1) → Real) (c : Complex) :
      e.symm (fun i => (eR a i : Complex) + c * (eR b i : Complex) * I) =
        fun j mu => (a j mu : Complex) + c * (b j mu : Complex) * I := by
    ext j mu
    simp only [e, eR, flattenCLEquiv_symm_apply, flattenCLEquivReal_apply,
      Equiv.symm_apply_apply]
  have he1 (a b : Fin n → Fin (d + 1) → Real) :
      e.symm (fun i => (eR a i : Complex) + (eR b i : Complex) * I) =
        fun j mu => (a j mu : Complex) + (b j mu : Complex) * I := by
    simpa using he a b 1
  have hmeas : (flattenMeasurableEquiv n (d + 1) : _ → _) = eR := by
    ext x i
    simp [eR, flattenMeasurableEquiv_apply, flattenCLEquivReal_apply]
  have hflat_int : ∀ y ∈ eR '' C,
      ∀ f : SchwartzMap (Fin (n * (d + 1)) → Real) Complex,
      Integrable (fun x : Fin (n * (d + 1)) → Real =>
        Fflat (fun i => (x i : Complex) + (y i : Complex) * I) * f x) := by
    rintro _ ⟨y, hy, rfl⟩ f
    apply ((flattenMeasurableEquiv_measurePreserving n (d + 1)).integrable_comp_emb
      (flattenMeasurableEquiv n (d + 1)).measurableEmbedding).mp
    simpa only [hmeas, Function.comp_def, Fflat, he1,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply] using
      hF_int y hy (SchwartzMap.compCLMOfContinuousLinearEquiv Complex eR f)
  have hflat_bv : ∀ eta ∈ eR '' C,
      ∀ f : SchwartzMap (Fin (n * (d + 1)) → Real) Complex,
      Tendsto (fun epsilon : Real => ∫ x : Fin (n * (d + 1)) → Real,
        Fflat (fun i => (x i : Complex) + (epsilon : Complex) * (eta i : Complex) * I) * f x)
        (nhdsWithin 0 (Ioi 0)) (nhds (T (physicsFourierFlatCLM f))) := by
    rintro _ ⟨eta, heta, rfl⟩ f
    have hlim := hF_bv eta heta (SchwartzMap.compCLMOfContinuousLinearEquiv Complex eR f)
    rw [hboundary] at hlim
    apply hlim.congr
    intro epsilon
    rw [integral_flatten_change_of_variables n (d + 1)]
    change (∫ x : Fin n → Fin (d + 1) → Real,
      F (fun j mu => (x j mu : Complex) + (epsilon : Complex) * (eta j mu : Complex) * I) * f (eR x)) =
      ∫ x : Fin n → Fin (d + 1) → Real,
        F (e.symm (fun i => (eR x i : Complex) + (epsilon : Complex) * (eR eta i : Complex) * I)) * f (eR x)
    simp only [he]
  have hflat_holo : DifferentiableOn Complex Fflat (SCV.TubeDomain (eR '' C)) :=
    hF.comp e.symm.differentiableOn fun _ hw =>
      flattenCLEquiv_symm_mem_tubeDomainSetPi_of_mem_tubeDomain_image hw
  have hrepr := fourierLaplace_representation_of_supported_boundary (eR '' C)
    hCflat_open hCflat_conv hCflat_cone hCflat_salient (hC_ne.image eR)
    Fflat hflat_holo T hT hflat_int hflat_bv
  intro z hz
  simpa only [Fflat, Function.comp_def, e, ContinuousLinearEquiv.symm_apply_apply] using
    hrepr (flattenCLEquiv_mem_tubeDomain_image hz)
