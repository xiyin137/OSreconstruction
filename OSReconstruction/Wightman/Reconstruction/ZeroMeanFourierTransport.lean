import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Fourier Transport for Zero-Mean Decomposition

This file contains the Fourier-side bridge from coordinate factorization
`F = Σ ξᵢ Hᵢ` to the Schwartz zero-mean decomposition
`f = Σ ∂ᵢ gᵢ`.

These theorems are directly on the reconstruction critical path: the current
two-point Schwinger reduction depends on the multi-dimensional zero-mean
decomposition, and this file isolates the exact Fourier transport needed for
that step.
-/

noncomputable section

open scoped FourierTransform LineDeriv
open SchwartzMap MeasureTheory

namespace OSReconstruction

theorem fourier_zero_eq_integralCLM_euclidean {ι : Type*} [Fintype ι]
    (f : SchwartzMap (EuclideanSpace ℝ ι) ℂ) :
    (SchwartzMap.fourierTransformCLM (𝕜 := ℂ) (V := EuclideanSpace ℝ ι) (E := ℂ) f) 0 =
      (SchwartzMap.integralCLM ℂ
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ ι))) f := by
  rw [SchwartzMap.integralCLM_apply, SchwartzMap.fourierTransformCLM_apply,
    SchwartzMap.fourier_coe, Real.fourier_eq]
  simp

theorem integral_comp_euclidean_equiv {m : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ) :
    ∫ x : EuclideanSpace ℝ (Fin m),
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)) f) x =
    ∫ y : Fin m → ℝ, f y := by
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)
  change ∫ x : EuclideanSpace ℝ (Fin m), f (e x) =
    ∫ y : Fin m → ℝ, f y
  simpa [e, PiLp.coe_symm_continuousLinearEquiv] using
    (((PiLp.volume_preserving_toLp (ι := Fin m)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin m → ℝ)).measurableEmbedding
      (fun x : EuclideanSpace ℝ (Fin m) => f (e x))).symm)

theorem transported_fourier_zero_eq_integralCLM {m : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ) :
    let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
      EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)
    let fE : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ :=
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f
    (SchwartzMap.fourierTransformCLM (𝕜 := ℂ) (V := EuclideanSpace ℝ (Fin m)) (E := ℂ) fE) 0 =
      (SchwartzMap.integralCLM ℂ
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))) f := by
  dsimp
  calc
    (SchwartzMap.fourierTransformCLM (𝕜 := ℂ) (V := EuclideanSpace ℝ (Fin m)) (E := ℂ)
        ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ))) f)) 0
        =
      (SchwartzMap.integralCLM ℂ
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin m))))
        ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ))) f) := by
            simpa using fourier_zero_eq_integralCLM_euclidean
              ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
                (EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ))) f)
    _ = (SchwartzMap.integralCLM ℂ
        (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))) f := by
          rw [SchwartzMap.integralCLM_apply, SchwartzMap.integralCLM_apply]
          exact integral_comp_euclidean_equiv f

theorem euclidean_coord_lineDeriv_transport {m : ℕ}
    (f : SchwartzMap (Fin m → ℝ) ℂ) (i : Fin m) :
    ∂_{EuclideanSpace.single i (1 : ℝ)}
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ))) f)
      =
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ))
      (∂_{((Pi.single i (1 : ℝ)) : Fin m → ℝ)} f) := by
  have hdir :
      (EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ))
        (EuclideanSpace.single i (1 : ℝ)) =
      ((Pi.single i (1 : ℝ)) : Fin m → ℝ) := by
    ext j
    simp [EuclideanSpace.single_apply, Pi.single_apply]
  simpa [hdir] using
    (SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv (𝕜 := ℂ)
      (m := EuclideanSpace.single i (1 : ℝ))
      (g := EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ))
      (f := f))

theorem pi_coord_lineDeriv_transport {m : ℕ}
    (f : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ) (i : Fin m) :
    ∂_{((Pi.single i (1 : ℝ)) : Fin m → ℝ)}
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)).symm) f)
      =
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)).symm
      (∂_{EuclideanSpace.single i (1 : ℝ)} f) := by
  have hdir :
      (EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)).symm
        (((Pi.single i (1 : ℝ)) : Fin m → ℝ)) =
      EuclideanSpace.single i (1 : ℝ) := by
    ext j
    simp [EuclideanSpace.single_apply, Pi.single_apply]
  simpa [hdir] using
    (SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv (𝕜 := ℂ)
      (m := ((Pi.single i (1 : ℝ)) : Fin m → ℝ))
      (g := (EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)).symm)
      (f := f))

theorem euclidean_fourier_lineDerivOp_eq_coord {m : ℕ}
    (f : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ) (i : Fin m) :
    𝓕 (∂_{EuclideanSpace.single i (1 : ℝ)} f) =
      (2 * Real.pi * Complex.I) •
        SchwartzMap.smulLeftCLM ℂ
          (fun ξ : EuclideanSpace ℝ (Fin m) => ξ i) (𝓕 f) := by
  have h := SchwartzMap.fourier_lineDerivOp_eq (f := f) (m := EuclideanSpace.single i (1 : ℝ))
  -- The inner product ⟨ξ, eᵢ⟩ equals ξ i (= ξ.ofLp i)
  have hinner : (fun ξ : EuclideanSpace ℝ (Fin m) => @inner ℝ _ _ ξ
    (EuclideanSpace.single i 1)) = (fun ξ => ξ i) := by
    ext ξ
    -- inner ℝ ξ (single i 1) = ξ.ofLp i
    show @inner ℝ (EuclideanSpace ℝ (Fin m)) _ ξ (EuclideanSpace.single i 1) = ξ.ofLp i
    have := EuclideanSpace.inner_single_right (𝕜 := ℝ) i (1 : ℝ) ξ
    simp at this
    exact this
  rw [hinner] at h
  exact h

theorem euclidean_coord_decomp_implies_pi_zeroMean_decomp {m : ℕ}
    (hcoord :
      ∀ F : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ, F 0 = 0 →
        ∃ H : Fin m → SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ,
          F = ∑ i, SchwartzMap.smulLeftCLM ℂ
            (fun ξ : EuclideanSpace ℝ (Fin m) => ξ i) (H i))
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hf : (SchwartzMap.integralCLM ℂ
      (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))) f = 0) :
    ∃ g : Fin m → SchwartzMap (Fin m → ℝ) ℂ,
      f = ∑ i, ∂_{((Pi.single i (1 : ℝ)) : Fin m → ℝ)} (g i) := by
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)
  let fE : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f
  let FE : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ := 𝓕 fE
  have hFE0 : FE 0 = 0 := by
    have hT :
        FE 0 =
          (SchwartzMap.integralCLM ℂ
            (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))) f := by
      simpa [FE, fE, e] using transported_fourier_zero_eq_integralCLM f
    rw [hT, hf]
  obtain ⟨H, hH⟩ := hcoord FE hFE0
  let c : ℂ := 2 * Real.pi * Complex.I
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (by exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero) Complex.I_ne_zero
  let gE : Fin m → SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ :=
    fun i => c⁻¹ • 𝓕⁻ (H i)
  have hfourier :
      𝓕 (∑ i : Fin m, ∂_{EuclideanSpace.single i (1 : ℝ)} (gE i)) = FE := by
    calc
      𝓕 (∑ i : Fin m, ∂_{EuclideanSpace.single i (1 : ℝ)} (gE i))
          = ∑ i : Fin m, 𝓕 (∂_{EuclideanSpace.single i (1 : ℝ)} (gE i)) := by
              simp
      _ = ∑ i : Fin m,
            c • SchwartzMap.smulLeftCLM ℂ
              (fun ξ : EuclideanSpace ℝ (Fin m) => ξ i) (𝓕 (gE i)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simpa [c, gE] using euclidean_fourier_lineDerivOp_eq_coord (gE i) i
      _ = ∑ i : Fin m,
            c • SchwartzMap.smulLeftCLM ℂ
              (fun ξ : EuclideanSpace ℝ (Fin m) => ξ i) (c⁻¹ • H i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [gE, FourierInvPair.fourier_fourierInv_eq]
      _ = ∑ i : Fin m,
            SchwartzMap.smulLeftCLM ℂ
              (fun ξ : EuclideanSpace ℝ (Fin m) => ξ i) (H i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ext ξ
              have hproj :
                  (fun ξ : EuclideanSpace ℝ (Fin m) => ξ i).HasTemperateGrowth :=
                (EuclideanSpace.proj i).hasTemperateGrowth
              simp only [SchwartzMap.smulLeftCLM_apply_apply hproj, SchwartzMap.smul_apply]
              -- Goal: c • ξ.ofLp i • c⁻¹ • (H i) ξ = ξ.ofLp i • (H i) ξ
              -- c⁻¹ • (H i) ξ : ℂ smul on ℂ = mul
              -- ξ.ofLp i • ... : ℝ smul on ℂ
              -- c • ... : ℂ smul on ℂ = mul
              have : c • ((ξ.ofLp i : ℝ) • (c⁻¹ • (H i) ξ)) =
                  (ξ.ofLp i : ℝ) • ((H i) ξ) := by
                rw [smul_comm c (ξ.ofLp i : ℝ), smul_smul c c⁻¹, mul_inv_cancel₀ hc, one_smul]
              exact this
      _ = FE := hH.symm
  have hE : ∑ i : Fin m, ∂_{EuclideanSpace.single i (1 : ℝ)} (gE i) = fE := by
    have hinv := congrArg (fun u : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ => 𝓕⁻ u) hfourier
    simpa [FE, FourierPair.fourierInv_fourier_eq] using hinv
  refine ⟨fun i =>
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm (gE i), ?_⟩
  calc
    f = SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm fE := by
      ext y
      have hy : e (e.symm y) = y := e.apply_symm_apply y
      simpa [fE, hy]
    _ = SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm
          (∑ i : Fin m, ∂_{EuclideanSpace.single i (1 : ℝ)} (gE i)) := by
            rw [hE]
    _ = ∑ i : Fin m,
          SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm
            (∂_{EuclideanSpace.single i (1 : ℝ)} (gE i)) := by
              simp
    _ = ∑ i : Fin m,
          ∂_{((Pi.single i (1 : ℝ)) : Fin m → ℝ)}
            (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm (gE i)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact (pi_coord_lineDeriv_transport (gE i) i).symm

theorem pi_coord_decomp_implies_pi_zeroMean_decomp {m : ℕ}
    (hcoordPi :
      ∀ f : SchwartzMap (Fin m → ℝ) ℂ, f 0 = 0 →
        ∃ H : Fin m → SchwartzMap (Fin m → ℝ) ℂ,
          f = ∑ i, SchwartzMap.smulLeftCLM ℂ
            (fun x : Fin m → ℝ => x i) (H i))
    (f : SchwartzMap (Fin m → ℝ) ℂ)
    (hf : (SchwartzMap.integralCLM ℂ
      (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))) f = 0) :
    ∃ g : Fin m → SchwartzMap (Fin m → ℝ) ℂ,
      f = ∑ i, ∂_{((Pi.single i (1 : ℝ)) : Fin m → ℝ)} (g i) := by
  refine euclidean_coord_decomp_implies_pi_zeroMean_decomp ?_ f hf
  intro F hF0
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)
  let fPi : SchwartzMap (Fin m → ℝ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm F
  have hfPi0 : fPi 0 = 0 := by
    simpa [fPi, e] using hF0
  obtain ⟨Hpi, hHpi⟩ := hcoordPi fPi hfPi0
  refine ⟨fun i => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (Hpi i), ?_⟩
  calc
    F = SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e fPi := by
      ext x
      simp [fPi, e]
    _ = SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
          (∑ i : Fin m,
            SchwartzMap.smulLeftCLM ℂ (fun x : Fin m → ℝ => x i) (Hpi i)) := by
            rw [hHpi]
    _ = ∑ i : Fin m,
          SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
            (SchwartzMap.smulLeftCLM ℂ (fun x : Fin m → ℝ => x i) (Hpi i)) := by
              simp
    _ = ∑ i : Fin m,
          SchwartzMap.smulLeftCLM ℂ
            (fun ξ : EuclideanSpace ℝ (Fin m) => ξ i)
            (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (Hpi i)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ext x
              have hpi :
                  (fun y : Fin m → ℝ => y i).HasTemperateGrowth := by
                exact
                  (ContinuousLinearMap.proj (R := ℝ) (ι := Fin m)
                    (φ := fun _ => ℝ) i).hasTemperateGrowth
              have heuclid :
                  (fun ξ : EuclideanSpace ℝ (Fin m) => ξ i).HasTemperateGrowth := by
                exact (EuclideanSpace.proj i).hasTemperateGrowth
              simp [fPi, e, SchwartzMap.smulLeftCLM_apply_apply hpi,
                SchwartzMap.smulLeftCLM_apply_apply heuclid, Complex.real_smul,
                mul_assoc, mul_left_comm, mul_comm]

end OSReconstruction
