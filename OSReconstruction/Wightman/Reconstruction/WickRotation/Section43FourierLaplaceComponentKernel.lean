import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceCompactDifferentiation
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43OS24KernelSafeFubini
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanSemigroup
import OSReconstruction.GeneralResults.SchwartzDamping

noncomputable section

open scoped Topology FourierTransform LineDeriv
open Set MeasureTheory Filter

namespace OSReconstruction

/-- Transform-component version of the canonical successor-right S5 scalar
identity.

The explicit Fourier-Laplace representatives are obtained from the genuine
Section 4.3 transform components, then passed to the already compiled
projection-witness bridge. -/
theorem section43TimeShiftKernel_psiZ_pairing_eq_osScalar_of_transformComponent_succRight
    (d n m : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d (m + 1))
    (hg_ord :
      tsupport (g : NPointDomain d (m + 1) → ℂ) ⊆
        OrderedPositiveTimeRegion d (m + 1))
    (hg_compact : HasCompactSupport (g : NPointDomain d (m + 1) → ℂ))
    (hφ_freq :
      section43FrequencyProjection (d := d) n φ =
        section43FourierLaplaceTransformComponent d n f hf_ord hf_compact)
    (hψ_freq :
      section43FrequencyProjection (d := d) (m + 1) ψ =
        section43FourierLaplaceTransformComponent d (m + 1) g hg_ord hg_compact)
    {t : ℝ} (ht : 0 < t) :
    (∫ τ : ℝ,
      bvt_W OS lgc (n + (m + 1))
        (φ.conjTensorProduct
          (timeShiftSchwartzNPoint (d := d) τ ψ)) *
        (SchwartzMap.fourierTransformCLM ℂ
          (section43PsiZTimeTest t ht)) τ) =
      OS.S (n + (m + 1))
        (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t g))) := by
  obtain ⟨Φφ, hΦφ_rep, hΦφ_q⟩ :=
    section43FourierLaplaceTransformComponent_has_representative
      d n f hf_ord hf_compact
  obtain ⟨Φψ, hΦψ_rep, hΦψ_q⟩ :=
    section43FourierLaplaceTransformComponent_has_representative
      d (m + 1) g hg_ord hg_compact
  exact
    section43TimeShiftKernel_psiZ_pairing_eq_osScalar_from_frequencyProjection_witness_succRight
      (d := d) (n := n) (m := m) OS lgc φ ψ
      f hf_ord hf_compact g hg_ord hg_compact
      Φφ Φψ hΦφ_rep hΦψ_rep
      (hφ_freq.trans hΦφ_q.symm)
      (hψ_freq.trans hΦψ_q.symm)
      ht

/-- Positive-imaginary-axis identification of the canonical Wightman witness
from the genuine Section 4.3 transform-component hypotheses. -/
theorem bvt_W_conjTensorProduct_timeShiftCanonicalExtension_imag_eq_osHolomorphicValue_of_transformComponent_succRight
    (d n m : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (hψ_compact : HasCompactSupport (ψ : NPointDomain d (m + 1) → ℂ))
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d (m + 1))
    (hg_ord :
      tsupport (g : NPointDomain d (m + 1) → ℂ) ⊆
        OrderedPositiveTimeRegion d (m + 1))
    (hg_compact : HasCompactSupport (g : NPointDomain d (m + 1) → ℂ))
    (hφ_freq :
      section43FrequencyProjection (d := d) n φ =
        section43FourierLaplaceTransformComponent d n f hf_ord hf_compact)
    (hψ_freq :
      section43FrequencyProjection (d := d) (m + 1) ψ =
        section43FourierLaplaceTransformComponent d (m + 1) g hg_ord hg_compact) :
    ∀ t : ℝ, 0 < t →
      bvt_W_conjTensorProduct_timeShiftCanonicalExtension
        (d := d) OS lgc φ ψ hψ_compact ((t : ℂ) * Complex.I) =
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
        (PositiveTimeBorchersSequence.single n f hf_ord)
        (PositiveTimeBorchersSequence.single (m + 1) g hg_ord) (t : ℂ) := by
  intro t ht
  have hCanonical :
      bvt_W_conjTensorProduct_timeShiftCanonicalExtension
          (d := d) OS lgc φ ψ hψ_compact ((t : ℂ) * Complex.I) =
        ∫ τ : ℝ,
          bvt_W OS lgc (n + (m + 1))
            (φ.conjTensorProduct
              (timeShiftSchwartzNPoint (d := d) τ ψ)) *
            (SchwartzMap.fourierTransformCLM ℂ
              (section43PsiZTimeTest t ht)) τ := by
    simpa [section43PsiZTimeTest] using
      (bvt_W_conjTensorProduct_timeShiftCanonicalExtension_eq_fourierLaplaceIntegral
        (d := d) (OS := OS) (lgc := lgc)
        (f := φ) (g := ψ) (hg_compact := hψ_compact) ht)
  have hKernel :
      (∫ τ : ℝ,
        bvt_W OS lgc (n + (m + 1))
          (φ.conjTensorProduct
            (timeShiftSchwartzNPoint (d := d) τ ψ)) *
          (SchwartzMap.fourierTransformCLM ℂ
            (section43PsiZTimeTest t ht)) τ) =
        OS.S (n + (m + 1))
          (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) t g))) :=
    section43TimeShiftKernel_psiZ_pairing_eq_osScalar_of_transformComponent_succRight
      (d := d) (n := n) (m := m) OS lgc φ ψ
      f hf_ord hf_compact g hg_ord hg_compact hφ_freq hψ_freq ht
  have hOS :
      OSInnerProductTimeShiftHolomorphicValue (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single (m + 1) g hg_ord) (t : ℂ) =
        OS.S (n + (m + 1))
          (ZeroDiagonalSchwartz.ofClassical
            (f.osConjTensorProduct
              (timeShiftSchwartzNPoint (d := d) t g))) :=
    OSInnerProductTimeShiftHolomorphicValue_ofReal_eq_single
      (d := d) OS lgc f hf_ord g hg_ord hg_compact t ht
  exact hCanonical.trans (hKernel.trans hOS.symm)

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
  let h₁ : (n + m) * (d + 1) =
      n * (d + 1) + m * (d + 1) := by ring
  let h₂ : n * (d + 1) + m * (d + 1) =
      (n + m) * (d + 1) := by ring
  have h₂eq : h₂ = h₁.symm := by
    subst h₁
    rfl
  have hflat :=
    reindex_flattenSchwartzNPoint_conjTensorProduct_eq_tensorProduct
      (d := d) (n := n) (m := m) φ ψ
  have hflat' := congrArg (reindexSchwartzFin h₂) hflat
  rw [h₂eq] at hflat'
  simpa [reindexSchwartzFin_symm_comp_self] using hflat'

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
    simpa [Function.comp] using
      (Tflat.continuous.tendsto K0).comp hK0_tendsto'
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

/-- Wightman-side Abel limit for the compiled OS24 scalar bridge.

The ψZ-paired real-time Wightman scalar converges to the unsmeared Wightman
value as the Paley height tends to zero from the positive side.  The proof
passes through the flattened Wightman distribution `Tflat`, where the limit is
the compiled `tendsto_Tflat_section43OS24Kernel_succRight_to_flatBase`. -/
theorem tendsto_section43TimeShiftKernel_psiZ_pairing_to_bvt_W_succRight
    (d n m : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1)) :
    Filter.Tendsto
      (fun t : ℝ =>
        if ht : 0 < t then
          ∫ τ : ℝ,
            bvt_W OS lgc (n + (m + 1))
              (φ.conjTensorProduct
                (timeShiftSchwartzNPoint (d := d) τ ψ)) *
            (SchwartzMap.fourierTransformCLM ℂ
              (section43PsiZTimeTest t ht)) τ
        else
          bvt_W OS lgc (n + (m + 1)) (φ.conjTensorProduct ψ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (bvt_W OS lgc (n + (m + 1)) (φ.conjTensorProduct ψ))) := by
  obtain ⟨Tflat, hTflat_supp, hTflat_bv, _hTflat_FL⟩ :=
    bvt_W_flattened_distribution_hasFourierSupportIn_wightmanSpectralRegion_with_fourierLaplaceWitness
      (d := d) OS lgc (n + (m + 1))
  have hW_base :
      bvt_W OS lgc (n + (m + 1)) (φ.conjTensorProduct ψ) =
        Tflat (section43OS24FlatBaseKernel_succRight d n m φ ψ) := by
    have hBV :=
      hTflat_bv (flattenSchwartzNPoint (d := d) (φ.conjTensorProduct ψ))
    have hEqOn :=
      physicsFourierFlatCLM_flatten_conjTensorProduct_eq_OS24FlatBaseKernel_on_spectralRegion_succRight
        d n m φ ψ
    have hT_eq :
        Tflat
          (physicsFourierFlatCLM
            (flattenSchwartzNPoint (d := d) (φ.conjTensorProduct ψ))) =
        Tflat (section43OS24FlatBaseKernel_succRight d n m φ ψ) := by
      exact hasFourierSupportIn_eqOn hTflat_supp
        (fun ξ hξ => hEqOn hξ)
    have hunflatten_generic :
        ∀ F : SchwartzNPoint d (n + (m + 1)),
          _root_.unflattenSchwartzNPoint (d := d)
            (flattenSchwartzNPoint (d := d) F) = F := by
      intro F
      ext x
      rw [_root_.unflattenSchwartzNPoint_apply, flattenSchwartzNPoint_apply]
      congr 1
      ext i μ
      simp [flattenCLEquivReal_apply]
    have hunflatten :
        _root_.unflattenSchwartzNPoint (d := d)
          (flattenSchwartzNPoint (d := d) (φ.conjTensorProduct ψ)) =
        φ.conjTensorProduct ψ :=
      hunflatten_generic (φ.conjTensorProduct ψ)
    calc
      bvt_W OS lgc (n + (m + 1)) (φ.conjTensorProduct ψ)
          =
        bvt_W OS lgc (n + (m + 1))
          (_root_.unflattenSchwartzNPoint (d := d)
            (flattenSchwartzNPoint (d := d) (φ.conjTensorProduct ψ))) := by
          rw [hunflatten]
      _ =
        Tflat
          (physicsFourierFlatCLM
            (flattenSchwartzNPoint (d := d) (φ.conjTensorProduct ψ))) := hBV
      _ = Tflat (section43OS24FlatBaseKernel_succRight d n m φ ψ) := hT_eq
  have hT_limit :=
    tendsto_Tflat_section43OS24Kernel_succRight_to_flatBase
      d n m φ ψ Tflat hTflat_supp
  have hIW_T :
      (fun t : ℝ =>
        if ht : 0 < t then
          Tflat (section43OS24Kernel_succRight d n m φ ψ t ht)
        else
          Tflat (section43OS24FlatBaseKernel_succRight d n m φ ψ))
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun t : ℝ =>
        if ht : 0 < t then
          ∫ τ : ℝ,
            bvt_W OS lgc (n + (m + 1))
              (φ.conjTensorProduct
                (timeShiftSchwartzNPoint (d := d) τ ψ)) *
            (SchwartzMap.fourierTransformCLM ℂ
              (section43PsiZTimeTest t ht)) τ
        else
          bvt_W OS lgc (n + (m + 1)) (φ.conjTensorProduct ψ)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hpos : 0 < t := ht
    rw [dif_pos hpos, dif_pos hpos]
    exact (section43TimeShiftKernel_psiZ_pairing_eq_Tflat_OS24Kernel_succRight
      (d := d) (n := n) (m := m) OS lgc φ ψ hpos
      Tflat hTflat_supp hTflat_bv).symm
  simpa [hW_base] using Filter.Tendsto.congr' hIW_T hT_limit

/-- OS-side zero-time continuity for the single-pair scalar appearing in the
compiled OS24 bridge.

This is theorem B in the Abel-limit closure: it is just the already compiled
semigroup continuity of `OSInnerProduct` specialized to concentrated
positive-time Borchers sequences. -/
theorem tendsto_OS_S_osConjTensorProduct_timeShift_zero_succRight
    (d n m : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (_hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d (m + 1))
    (hg_ord :
      tsupport (g : NPointDomain d (m + 1) → ℂ) ⊆
        OrderedPositiveTimeRegion d (m + 1))
    (hg_compact : HasCompactSupport (g : NPointDomain d (m + 1) → ℂ)) :
    Filter.Tendsto
      (fun t : ℝ =>
        if _ht : 0 < t then
          OS.S (n + (m + 1))
            (ZeroDiagonalSchwartz.ofClassical
              (f.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) t g)))
        else
          OS.S (n + (m + 1))
            (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (OS.S (n + (m + 1))
          (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)))) := by
  let Fpos : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single n f hf_ord
  let Gpos : PositiveTimeBorchersSequence d :=
    PositiveTimeBorchersSequence.single (m + 1) g hg_ord
  let F : BorchersSequence d := Fpos
  let G : BorchersSequence d := Gpos
  have hG_compact_all : ∀ k,
      HasCompactSupport ((G.funcs k : SchwartzNPoint d k) : NPointDomain d k → ℂ) := by
    intro k
    by_cases hk : k = m + 1
    · subst hk
      simpa [G, Gpos, PositiveTimeBorchersSequence.single_toBorchersSequence] using
        hg_compact
    · have hzero :
          (((G.funcs k : SchwartzNPoint d k) : NPointDomain d k → ℂ)) = 0 := by
        simp [G, Gpos, PositiveTimeBorchersSequence.single_toBorchersSequence,
          BorchersSequence.single, hk]
      rw [hzero]
      simpa using (HasCompactSupport.zero :
        HasCompactSupport (0 : NPointDomain d k → ℂ))
  have hraw :
      Filter.Tendsto
        (fun t : ℝ => OSInnerProduct d OS.S F (timeShiftBorchers (d := d) t G))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (OSInnerProduct d OS.S F G)) :=
    tendsto_OSInnerProduct_right_timeShift_nhdsWithin_zero_of_isCompactSupport
      (d := d) OS F G Fpos.ordered_tsupport Gpos.ordered_tsupport hG_compact_all
  have hlimit_eq :
      OSInnerProduct d OS.S F G =
        OS.S (n + (m + 1))
          (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
    simpa [F, G, Fpos, Gpos, PositiveTimeBorchersSequence.single_toBorchersSequence] using
      (OSInnerProduct_single_single d OS.S OS.E0_linear n (m + 1) f g)
  have hEq :
      (fun t : ℝ => OSInnerProduct d OS.S F (timeShiftBorchers (d := d) t G))
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun t : ℝ =>
        if _ht : 0 < t then
          OS.S (n + (m + 1))
            (ZeroDiagonalSchwartz.ofClassical
              (f.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) t g)))
        else
          OS.S (n + (m + 1))
            (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hpos : 0 < t := ht
    rw [dif_pos hpos]
    simpa [F, G, Fpos, Gpos, PositiveTimeBorchersSequence.single_toBorchersSequence] using
      (OSInnerProduct_single_right_timeShift (d := d) OS f g t)
  simpa [hlimit_eq] using Filter.Tendsto.congr' hEq hraw

/-- Direct transformed-image kernel equality for one successor-right pair.

This combines the Wightman Abel limit, the OS zero-time continuity limit, and
the compiled positive-height OS24 scalar bridge.  It deliberately avoids the
withdrawn pointwise real-time/Laplace equality and does not route through
`lemma42_matrix_element_time_interchange`. -/
theorem bvt_W_kernel_eq_osScalar_of_transformComponent_succRight
    (d n m : ℕ) [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS)
    (φ : SchwartzNPoint d n) (ψ : SchwartzNPoint d (m + 1))
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆ OrderedPositiveTimeRegion d n)
    (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ))
    (g : SchwartzNPoint d (m + 1))
    (hg_ord :
      tsupport (g : NPointDomain d (m + 1) → ℂ) ⊆
        OrderedPositiveTimeRegion d (m + 1))
    (hg_compact : HasCompactSupport (g : NPointDomain d (m + 1) → ℂ))
    (hφ_freq :
      section43FrequencyProjection (d := d) n φ =
        section43FourierLaplaceTransformComponent d n f hf_ord hf_compact)
    (hψ_freq :
      section43FrequencyProjection (d := d) (m + 1) ψ =
        section43FourierLaplaceTransformComponent d (m + 1) g hg_ord hg_compact) :
    bvt_W OS lgc (n + (m + 1)) (φ.conjTensorProduct ψ) =
      OS.S (n + (m + 1))
        (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)) := by
  let IW : ℝ → ℂ := fun t =>
    if ht : 0 < t then
      ∫ τ : ℝ,
        bvt_W OS lgc (n + (m + 1))
          (φ.conjTensorProduct
            (timeShiftSchwartzNPoint (d := d) τ ψ)) *
        (SchwartzMap.fourierTransformCLM ℂ
          (section43PsiZTimeTest t ht)) τ
    else
      bvt_W OS lgc (n + (m + 1)) (φ.conjTensorProduct ψ)
  let IOS : ℝ → ℂ := fun t =>
    if _ht : 0 < t then
      OS.S (n + (m + 1))
        (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) t g)))
    else
      OS.S (n + (m + 1))
        (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g))
  have hW :
      Filter.Tendsto IW (nhdsWithin 0 (Set.Ioi 0))
        (nhds (bvt_W OS lgc (n + (m + 1)) (φ.conjTensorProduct ψ))) := by
    simpa [IW] using
      tendsto_section43TimeShiftKernel_psiZ_pairing_to_bvt_W_succRight
        d n m OS lgc φ ψ
  have hOS :
      Filter.Tendsto IOS (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (OS.S (n + (m + 1))
            (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)))) := by
    simpa [IOS] using
      tendsto_OS_S_osConjTensorProduct_timeShift_zero_succRight
        d n m OS f hf_ord hf_compact g hg_ord hg_compact
  have hEq : IW =ᶠ[nhdsWithin 0 (Set.Ioi 0)] IOS := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hpos : 0 < t := ht
    simp [IW, IOS, hpos]
    exact section43TimeShiftKernel_psiZ_pairing_eq_osScalar_of_transformComponent_succRight
      (d := d) (n := n) (m := m) OS lgc φ ψ
      f hf_ord hf_compact g hg_ord hg_compact hφ_freq hψ_freq hpos
  have hW_to_OS :
      Filter.Tendsto IW (nhdsWithin 0 (Set.Ioi 0))
        (nhds
          (OS.S (n + (m + 1))
            (ZeroDiagonalSchwartz.ofClassical (f.osConjTensorProduct g)))) :=
    Filter.Tendsto.congr' hEq.symm hOS
  exact tendsto_nhds_unique hW hW_to_OS

end OSReconstruction
