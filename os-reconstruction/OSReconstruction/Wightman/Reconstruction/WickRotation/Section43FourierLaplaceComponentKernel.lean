/- Modified for source distribution, 2026-09-10: unused declarations/imports
and development comments removed; retained mathematical statements unchanged. -/
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceCompactDifferentiation
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43OS24KernelSafeFubini
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSemigroup
import OSReconstruction.GeneralResults.SchwartzDamping

noncomputable section

open scoped Topology FourierTransform LineDeriv
open Set MeasureTheory Filter

namespace OSReconstruction

/-- Global zero-height cutoff kernel for the concrete Section 4.3 OS24 witness.

The concrete positive-height witness contains the fixed Paley cutoff
`SCV.smoothCutoff`; therefore its global zero-height limit is this cutoff
kernel, not the raw flat base kernel.  On the Wightman spectral region the
cutoff is equal to `1`, so supported `Tflat` distributions cannot distinguish
this kernel from the flat base kernel. -/
noncomputable def section43OS24KernelCutoffZero_succRight
    (d n m : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1)) :
    SchwartzMap (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ :=
  SchwartzMap.smulLeftCLM ℂ
    (fun ξ => (SCV.smoothCutoff (section43SuccRightEtaCLM d n m ξ) : ℂ))
    (section43OS24FlatBaseKernel_succRight d n m φ ψ)

/-- The cutoff-zero kernel is supported in the half-space
`section43SuccRightEtaCLM ≥ -1`, the hypothesis needed for the general
Schwartz damping convergence theorem. -/
theorem section43OS24KernelCutoffZero_succRight_eta_bddBelow_on_support
    (d n m : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1)) :
    ∃ M : ℝ,
      ∀ ξ,
        ξ ∈ Function.support
          (fun ξ => section43OS24KernelCutoffZero_succRight d n m φ ψ ξ) →
        -M ≤ section43SuccRightEtaCLM d n m ξ := by
  refine ⟨1, ?_⟩
  intro ξ hξ
  rw [Function.mem_support] at hξ
  by_contra hnot
  have hle : section43SuccRightEtaCLM d n m ξ ≤ -1 := by linarith
  have hcut : SCV.smoothCutoff (section43SuccRightEtaCLM d n m ξ) = 0 :=
    SCV.smoothCutoff_zero_of_le_neg_one hle
  apply hξ
  rw [section43OS24KernelCutoffZero_succRight]
  change (((SchwartzMap.smulLeftCLM ℂ
    (((fun η : ℝ => (SCV.smoothCutoff η : ℂ)) ∘ (section43SuccRightEtaCLM d n m))))
    (section43OS24FlatBaseKernel_succRight d n m φ ψ)) ξ) = 0
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (SCV.smoothCutoff_complex_hasTemperateGrowth.comp
      (section43SuccRightEtaCLM d n m).hasTemperateGrowth)]
  change ((SCV.smoothCutoff (section43SuccRightEtaCLM d n m ξ) : ℂ) •
    section43OS24FlatBaseKernel_succRight d n m φ ψ ξ) = 0
  rw [hcut]
  simp

/-- The concrete positive-height OS24 witness converges in Schwartz topology to
the cutoff-zero kernel as the height tends to `0+`. -/
theorem tendsto_section43OS24KernelWitness_succRight_to_cutoffZero
    (d n m : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1)) :
    Filter.Tendsto
      (fun t : ℝ =>
        if ht : 0 < t then
          section43OS24KernelWitness_succRight d n m φ ψ t ht
        else
          section43OS24KernelCutoffZero_succRight d n m φ ψ)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (section43OS24KernelCutoffZero_succRight d n m φ ψ)) := by
  let K0 := section43OS24KernelCutoffZero_succRight d n m φ ψ
  let η := section43SuccRightEtaCLM d n m
  obtain ⟨hε, hε_apply, hε_tendsto⟩ :=
    schwartz_exp_damping_tendsto
      (h := K0) (L := η)
      (section43OS24KernelCutoffZero_succRight_eta_bddBelow_on_support
        d n m φ ψ)
  have hscale_tendsto :
      Filter.Tendsto
        (fun t : ℝ => (2 * Real.pi) * t)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_iff.mpr ?_
    constructor
    · have hcontWithin :
          ContinuousWithinAt
            (fun t : ℝ => (2 * Real.pi) * t)
            (Set.Ioi 0) 0 := by
        exact (continuous_const.mul continuous_id).continuousAt.continuousWithinAt
      simpa using hcontWithin.tendsto
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos Real.two_pi_pos ht
  have hcomp := hε_tendsto.comp hscale_tendsto
  have hEq :
      (fun t : ℝ => hε ((2 * Real.pi) * t)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun t : ℝ =>
        if ht : 0 < t then
          section43OS24KernelWitness_succRight d n m φ ψ t ht
        else
          K0) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hpos : 0 < t := ht
    rw [dif_pos hpos]
    ext ξ
    rw [hε_apply ((2 * Real.pi) * t) (mul_pos Real.two_pi_pos hpos) ξ]
    rw [section43OS24KernelWitness_succRight]
    change Complex.exp (-(((2 * Real.pi) * t : ℝ) : ℂ) * (η ξ : ℂ)) *
        (section43OS24KernelCutoffZero_succRight d n m φ ψ ξ) = _
    rw [section43OS24KernelCutoffZero_succRight]
    rw [SchwartzMap.smulLeftCLM_apply_apply
      (section43PsiZTimeTest_comp_eta_hasTemperateGrowth d n m hpos)]
    change Complex.exp (-(((2 * Real.pi) * t : ℝ) : ℂ) * (η ξ : ℂ)) *
        (((SchwartzMap.smulLeftCLM ℂ
          (((fun η : ℝ => (SCV.smoothCutoff η : ℂ)) ∘
            (section43SuccRightEtaCLM d n m))))
          (section43OS24FlatBaseKernel_succRight d n m φ ψ)) ξ) = _
    rw [SchwartzMap.smulLeftCLM_apply_apply
      (SCV.smoothCutoff_complex_hasTemperateGrowth.comp
        (section43SuccRightEtaCLM d n m).hasTemperateGrowth)]
    rw [section43PsiZTimeTest_apply, SCV.psiZ_eq]
    have hexp :
        Complex.I *
            (((2 * Real.pi : ℂ) * (t * Complex.I))) *
            (section43SuccRightEtaCLM d n m ξ : ℂ) =
          -(((2 * Real.pi) * t : ℝ) : ℂ) *
            (section43SuccRightEtaCLM d n m ξ : ℂ) := by
      calc
        Complex.I *
            (((2 * Real.pi : ℂ) * (t * Complex.I))) *
            (section43SuccRightEtaCLM d n m ξ : ℂ)
            =
          (Complex.I * Complex.I) *
            (((2 * Real.pi : ℂ) * (t : ℂ)) *
              (section43SuccRightEtaCLM d n m ξ : ℂ)) := by
            ring
        _ =
          -(((2 * Real.pi) * t : ℝ) : ℂ) *
            (section43SuccRightEtaCLM d n m ξ : ℂ) := by
            rw [Complex.I_mul_I]
            norm_num
    rw [hexp]
    simp [Function.comp, η, smul_eq_mul]
    ring
  simpa [K0, Function.comp] using Filter.Tendsto.congr' hEq hcomp

/-- The flat base kernel is the visible OS24 product on the Wightman spectral
region, before multiplication by the Paley factor. -/
theorem section43OS24FlatBaseKernel_succRight_eqOn_spectralRegion
    (d n m : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1)) :
    Set.EqOn
      (fun ξ => section43OS24FlatBaseKernel_succRight d n m φ ψ ξ)
      (fun ξ =>
        let qξ := section43CumulativeTailMomentumCLE d (n + (m + 1)) ξ
        star
          ((section43FrequencyRepresentative (d := d) n φ)
            (section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m) qξ)) *
          (section43FrequencyRepresentative (d := d) (m + 1) ψ)
            (section43RightTailBlock d n (m + 1) qξ))
      (section43WightmanSpectralRegion d (n + (m + 1))) := by
  intro ξ hξ
  have hN : 0 < n + (m + 1) := by omega
  have hq0 :
      section43CumulativeTailMomentumCLE d (n + (m + 1)) ξ 0 = 0 :=
    section43WightmanSpectralRegion_cumulativeTail_head_zero
      (d := d) (N := n + (m + 1)) hN hξ
  change section43OS24FlatBaseKernel_succRight d n m φ ψ ξ = _
  rw [section43OS24FlatBaseKernel_succRight_apply]
  exact section43OS24CumulativeTailProduct_eq_visible_of_head_zero
    (d := d) (n := n) (m := m) (φ := φ) (ψ := ψ) hq0

/-- The cutoff-zero kernel agrees with the flat base kernel on the Wightman
spectral region, where the successor-right Paley frequency is nonnegative. -/
theorem section43OS24KernelCutoffZero_succRight_eqOn_flatBase_spectralRegion
    (d n m : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1)) :
    Set.EqOn
      (fun ξ => section43OS24KernelCutoffZero_succRight d n m φ ψ ξ)
      (fun ξ => section43OS24FlatBaseKernel_succRight d n m φ ψ ξ)
      (section43WightmanSpectralRegion d (n + (m + 1))) := by
  intro ξ hξ
  change section43OS24KernelCutoffZero_succRight d n m φ ψ ξ = _
  rw [section43OS24KernelCutoffZero_succRight]
  change (((SchwartzMap.smulLeftCLM ℂ
    (((fun η : ℝ => (SCV.smoothCutoff η : ℂ)) ∘ (section43SuccRightEtaCLM d n m))))
    (section43OS24FlatBaseKernel_succRight d n m φ ψ)) ξ) = _
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (SCV.smoothCutoff_complex_hasTemperateGrowth.comp
      (section43SuccRightEtaCLM d n m).hasTemperateGrowth)]
  have heta_nonneg := section43SuccRightEtaCLM_nonneg_of_mem_spectralRegion d n m hξ
  have hcut : SCV.smoothCutoff ((section43SuccRightEtaCLM d n m) ξ) = 1 :=
    SCV.smoothCutoff_one_of_nonneg heta_nonneg
  change ((SCV.smoothCutoff ((section43SuccRightEtaCLM d n m) ξ) : ℂ) •
      section43OS24FlatBaseKernel_succRight d n m φ ψ ξ) = _
  rw [hcut]
  simp

/-- Reindexing a Schwartz function by an equality and then by its symmetric
equality returns the original function. -/
theorem reindexSchwartzFin_symm_comp_self {a b : ℕ} (h : a = b)
    (F : SchwartzMap (Fin a → ℝ) ℂ) :
    reindexSchwartzFin h.symm (reindexSchwartzFin h F) = F := by
  subst h
  ext x
  change F x = F x
  rfl

/-- Unreindexed form of the flattened conjugate tensor product: the flat
`n+m`-point tensor is the inverse reindex of the Borchers-conjugated left
tensor product with the right factor. -/
theorem flatten_conjTensorProduct_eq_reindex_tensor
    (d n m : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d m) :
    flattenSchwartzNPoint (d := d) (φ.conjTensorProduct ψ) =
      reindexSchwartzFin
        (by ring : n * (d + 1) + m * (d + 1) =
          (n + m) * (d + 1))
        (((flattenSchwartzNPoint (d := d) φ.borchersConj).tensorProduct
          (flattenSchwartzNPoint (d := d) ψ))) := by
  ext x
  rw [flattenSchwartzNPoint_apply, reindexSchwartzFin_apply,
    SchwartzMap.tensorProduct_apply, flattenSchwartzNPoint_apply,
    flattenSchwartzNPoint_apply, SchwartzMap.borchersConj_apply,
    SchwartzMap.conjTensorProduct_apply]
  apply congrArg₂ (· * ·)
  · apply congrArg (starRingEnd ℂ)
    apply congrArg φ
    funext i j
    apply congrArg x
    apply Fin.ext
    simp [finProdFinEquiv]
  · apply congrArg ψ
    funext i j
    apply congrArg x
    apply Fin.ext
    simp [finProdFinEquiv]
    ring

/-- Zero-height Fourier normal form for the actual flattened conjugate tensor
product on the Wightman spectral region. -/
theorem physicsFourierFlatCLM_flatten_conjTensorProduct_eq_frequencyRepresentatives_on_spectralRegion
    (d n m : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    {ξ : Fin ((n + (m + 1)) * (d + 1)) → ℝ}
    (hξ : ξ ∈ section43WightmanSpectralRegion d (n + (m + 1))) :
    let qξ := section43CumulativeTailMomentumCLE d (n + (m + 1)) ξ
    physicsFourierFlatCLM
        (flattenSchwartzNPoint (d := d) (φ.conjTensorProduct ψ)) ξ =
      star
        ((section43FrequencyRepresentative (d := d) n φ)
          (section43LeftBorchersBlock d n (m + 1) (Nat.succ_pos m) qξ)) *
        (section43FrequencyRepresentative (d := d) (m + 1) ψ)
          (section43RightTailBlock d n (m + 1) qξ) := by
  dsimp only
  rw [flatten_conjTensorProduct_eq_reindex_tensor]
  exact
    physicsFourierFlatCLM_borchersTensor_eq_frequencyRepresentatives_on_spectralRegion
      (d := d) (n := n) (m := m) φ ψ hξ

/-- The actual zero-height Fourier transform agrees with the OS24 flat base
kernel on the Wightman spectral region. -/
theorem physicsFourierFlatCLM_flatten_conjTensorProduct_eq_OS24FlatBaseKernel_on_spectralRegion_succRight
    (d n m : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1)) :
    Set.EqOn
      (fun ξ =>
        physicsFourierFlatCLM
          (flattenSchwartzNPoint (d := d) (φ.conjTensorProduct ψ)) ξ)
      (fun ξ => section43OS24FlatBaseKernel_succRight d n m φ ψ ξ)
      (section43WightmanSpectralRegion d (n + (m + 1))) := by
  intro ξ hξ
  change
    physicsFourierFlatCLM
      (flattenSchwartzNPoint (d := d) (φ.conjTensorProduct ψ)) ξ =
    section43OS24FlatBaseKernel_succRight d n m φ ψ ξ
  rw [physicsFourierFlatCLM_flatten_conjTensorProduct_eq_frequencyRepresentatives_on_spectralRegion
    (d := d) (n := n) (m := m) φ ψ hξ]
  exact (section43OS24FlatBaseKernel_succRight_eqOn_spectralRegion
    d n m φ ψ hξ).symm

/-- Applying a Wightman-spectrally supported flattened distribution to the
chosen OS24 kernels has the same zero-height limit as applying it to the flat
base kernel.

The proof uses the concrete witness convergence globally, then replaces both
the chosen positive-height kernel and the cutoff-zero limit by their
spectral-region equivalents inside `Tflat`. -/
theorem tendsto_Tflat_section43OS24Kernel_succRight_to_flatBase
    (d n m : ℕ) [NeZero d]
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (Tflat :
      SchwartzMap (Fin ((n + (m + 1)) * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ)
    (hTflat_supp :
      HasFourierSupportIn
        (section43WightmanSpectralRegion d (n + (m + 1))) Tflat) :
    Filter.Tendsto
      (fun t : ℝ =>
        if ht : 0 < t then
          Tflat (section43OS24Kernel_succRight d n m φ ψ t ht)
        else
          Tflat (section43OS24FlatBaseKernel_succRight d n m φ ψ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Tflat (section43OS24FlatBaseKernel_succRight d n m φ ψ))) := by
  let K0 := section43OS24KernelCutoffZero_succRight d n m φ ψ
  let Kbase := section43OS24FlatBaseKernel_succRight d n m φ ψ
  have hK0_tendsto :=
    tendsto_section43OS24KernelWitness_succRight_to_cutoffZero d n m φ ψ
  have hT_cut :
      Filter.Tendsto
        (fun t : ℝ =>
          Tflat (if ht : 0 < t then
            section43OS24KernelWitness_succRight d n m φ ψ t ht
          else
            K0))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (Tflat K0)) := by
    have hK0_tendsto' :
        Filter.Tendsto
          (fun t : ℝ =>
            if ht : 0 < t then
              section43OS24KernelWitness_succRight d n m φ ψ t ht
            else
              K0)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds K0) := by
      simpa [K0] using hK0_tendsto
    change Filter.Tendsto
      (Tflat ∘ fun t : ℝ => if ht : 0 < t then
        section43OS24KernelWitness_succRight d n m φ ψ t ht else K0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Tflat K0))
    exact (Tflat.continuous.tendsto K0).comp hK0_tendsto'
  have hcut_base : Tflat K0 = Tflat Kbase := by
    exact hasFourierSupportIn_eqOn hTflat_supp
      (fun ξ hξ =>
        section43OS24KernelCutoffZero_succRight_eqOn_flatBase_spectralRegion
          d n m φ ψ hξ)
  have hEq :
      (fun t : ℝ =>
        Tflat (if ht : 0 < t then
          section43OS24KernelWitness_succRight d n m φ ψ t ht
        else
          K0)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun t : ℝ =>
        if ht : 0 < t then
          Tflat (section43OS24Kernel_succRight d n m φ ψ t ht)
        else
          Tflat Kbase) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hpos : 0 < t := ht
    rw [dif_pos hpos, dif_pos hpos]
    have hchosen_witness :
        Tflat (section43OS24Kernel_succRight d n m φ ψ t hpos) =
          Tflat (section43OS24KernelWitness_succRight d n m φ ψ t hpos) := by
      exact hasFourierSupportIn_eqOn hTflat_supp
        (fun ξ hξ =>
          (section43OS24Kernel_succRight_eqOn_spectralRegion
              d n m φ ψ hpos hξ).trans
            (section43OS24KernelWitness_succRight_eqOn_spectralRegion
              d n m φ ψ hpos hξ).symm)
    exact hchosen_witness.symm
  simpa [K0, Kbase, hcut_base] using Filter.Tendsto.congr' hEq hT_cut

end OSReconstruction
