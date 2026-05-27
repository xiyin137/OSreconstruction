import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIAxisPairRawCLMSelector
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIIFixedWindowSelectors

/-!
# OS-II Axis-Pair Raw Selectors in Fixed-Window Form

This file connects the concrete axis-pair regularized OS semigroup CLMs to the
fixed-window local EOW branch-representation theorem.  It discharges the
Section 4.3 selector, quotient-descent, and pointwise-boundedness hypotheses
from the raw positive/lower side boundary-value CLMs, leaving only the
geometric prepared-domain and side-integral identities for the chosen local
Malgrange-Zerner branches.
-/

noncomputable section

open Complex Topology Filter MeasureTheory
open scoped Classical

namespace OSReconstruction

variable {d : ℕ} [NeZero d]

noncomputable def osiiAxisPairPositiveSideCLMC
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) :
    (Fin (d + 1) → ℝ) →
      SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
  fun y =>
    (if hy : 0 < y 0 then
      OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
        (d := d) OS lgc F G (y 0) hy
    else 0).comp (osiiAxisPairHeadRestrictionCLM d)

noncomputable def osiiAxisPairLowerSideCLMC
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) :
    (Fin (d + 1) → ℝ) →
      SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
  fun y =>
    (if hy : y 0 < 0 then
      OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
        (d := d) OS lgc F G (-y 0) (neg_pos.mpr hy)
    else 0).comp (osiiAxisPairHeadRestrictionCLM d)

noncomputable def osiiAxisPairBoundaryCLMC
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) :
    SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
  (OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
    (d := d) OS lgc F G).comp (osiiAxisPairHeadRestrictionCLM d)

noncomputable def osiiAxisPairPositiveSideCLMR
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) :
    (Fin (d + 1) → ℝ) →
      SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℝ] ℂ :=
  fun y => (osiiAxisPairPositiveSideCLMC (d := d) OS lgc F G y).restrictScalars ℝ

noncomputable def osiiAxisPairLowerSideCLMR
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) :
    (Fin (d + 1) → ℝ) →
      SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℝ] ℂ :=
  fun y => (osiiAxisPairLowerSideCLMC (d := d) OS lgc F G y).restrictScalars ℝ

noncomputable def osiiAxisPairBoundaryCLMR
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) :
    SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℝ] ℂ :=
  (osiiAxisPairBoundaryCLMC (d := d) OS lgc F G).restrictScalars ℝ

/-- Positive-side raw axis-pair CLM as the rotated OS semigroup line
distribution paired with the Fourier transform of the head-restricted finite-time
test.  This is the concrete Section 4.3 current formula before the remaining
Fourier/Laplace side-integral conversion. -/
theorem osiiAxisPairPositiveSideCLMR_apply_of_coord0_pos
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    {y : Fin (d + 1) → ℝ} (hy : 0 < y 0)
    (φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ) :
    osiiAxisPairPositiveSideCLMR (d := d) OS lgc F G y φ =
      ∫ x : ℝ,
        OSInnerProductTimeShiftHolomorphicValueExpandBoth
            (d := d) OS lgc F G
            (-Complex.I * ((x : ℂ) + y 0 * Complex.I)) *
          (SchwartzMap.fourierTransformCLM ℂ
            (osiiAxisPairHeadRestrictionCLM d φ)) x := by
  simp [osiiAxisPairPositiveSideCLMR, osiiAxisPairPositiveSideCLMC, hy,
    OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_apply]

/-- Lower-side analogue of `osiiAxisPairPositiveSideCLMR_apply_of_coord0_pos`. -/
theorem osiiAxisPairLowerSideCLMR_apply_of_coord0_neg
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    {y : Fin (d + 1) → ℝ} (hy : y 0 < 0)
    (φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ) :
    osiiAxisPairLowerSideCLMR (d := d) OS lgc F G y φ =
      ∫ x : ℝ,
        OSInnerProductTimeShiftHolomorphicValueExpandBoth
            (d := d) OS lgc F G
            (-Complex.I * ((x : ℂ) + (-y 0) * Complex.I)) *
          (SchwartzMap.fourierTransformCLM ℂ
            (osiiAxisPairHeadRestrictionCLM d φ)) x := by
  simp [osiiAxisPairLowerSideCLMR, osiiAxisPairLowerSideCLMC, hy,
    OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_apply]

/-- Product-source flattening for the concrete positive-side raw axis-pair CLM. -/
theorem osiiAxisPairPositiveSideCLMC_timeProductTensor_flattened
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (y : Fin (d + 1) → ℝ)
    (gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D) :
    osiiAxisPairPositiveSideCLMC (d := d) OS lgc F G y
        (section43TimeProductTensor
          (fun i : Fin (d + 1) =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) =
      ∫ τ : Fin (d + 1) → ℝ,
        osiiAxisPairPositiveSideCLMC (d := d) OS lgc F G y
          (section43TimeImagAxisProductKernel τ) *
          (section43TimeProductSource gs).f τ := by
  simpa using
    section43TimeProductTensor_allSlots_flattened
      (osiiAxisPairPositiveSideCLMC (d := d) OS lgc F G y) gs
      (fun _ : Fin (d + 1) => 0)

/-- Product-source flattening for the concrete lower-side raw axis-pair CLM. -/
theorem osiiAxisPairLowerSideCLMC_timeProductTensor_flattened
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    (y : Fin (d + 1) → ℝ)
    (gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D) :
    osiiAxisPairLowerSideCLMC (d := d) OS lgc F G y
        (section43TimeProductTensor
          (fun i : Fin (d + 1) =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) =
      ∫ τ : Fin (d + 1) → ℝ,
        osiiAxisPairLowerSideCLMC (d := d) OS lgc F G y
          (section43TimeImagAxisProductKernel τ) *
          (section43TimeProductSource gs).f τ := by
  simpa using
    section43TimeProductTensor_allSlots_flattened
      (osiiAxisPairLowerSideCLMC (d := d) OS lgc F G y) gs
      (fun _ : Fin (d + 1) => 0)

/-- Positive finite-height value of the raw axis-pair CLM on a Section 4.3
imaginary-axis product kernel.

The head-restricted vector kernel is first transported to the one-dimensional
Paley kernel, and the finite-height Paley identity then gives the shifted OS
semigroup branch. -/
theorem osiiAxisPairPositiveSideCLMC_timeImagAxisProductKernel_finiteHeight
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    {y : Fin (d + 1) → ℝ} (hy : 0 < y 0)
    (τ : Fin (d + 1) → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion (d + 1)) :
    osiiAxisPairPositiveSideCLMC (d := d) OS lgc F G y
        (section43TimeImagAxisProductKernel τ) =
      OSInnerProductTimeShiftHolomorphicValueExpandBoth
        (d := d) OS lgc F G (((τ 0 + y 0 : ℝ) : ℂ)) := by
  have hhead :
      OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
          (d := d) OS lgc F G (y 0) hy
          (osiiAxisPairHeadRestrictionCLM d
            (section43TimeImagAxisProductKernel τ)) =
        OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
          (d := d) OS lgc F G (y 0) hy
          (section43PsiZTimeTest (τ 0) (hτ 0)) :=
    OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_eq_of_eqOn_nonneg
      (d := d) OS lgc F G hy
      (osiiAxisPairHeadRestriction_timeImagAxisProductKernel_eqOn_nonneg
        (d := d) τ hτ)
  calc
    osiiAxisPairPositiveSideCLMC (d := d) OS lgc F G y
        (section43TimeImagAxisProductKernel τ)
        =
      OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
          (d := d) OS lgc F G (y 0) hy
          (osiiAxisPairHeadRestrictionCLM d
            (section43TimeImagAxisProductKernel τ)) := by
          simp [osiiAxisPairPositiveSideCLMC, hy]
    _ =
      OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
          (d := d) OS lgc F G (y 0) hy
          (section43PsiZTimeTest (τ 0) (hτ 0)) := hhead
    _ =
      OSInnerProductTimeShiftHolomorphicValueExpandBoth
        (d := d) OS lgc F G (((τ 0 + y 0 : ℝ) : ℂ)) := by
          simpa [section43PsiZTimeTest] using
            OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_psiZ_eq
              (d := d) OS lgc F G (hτ 0) hy

/-- Lower finite-height value of the raw axis-pair CLM on a Section 4.3
imaginary-axis product kernel.  The lower side uses the positive semigroup
height `-y⁰`. -/
theorem osiiAxisPairLowerSideCLMC_timeImagAxisProductKernel_finiteHeight
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    {y : Fin (d + 1) → ℝ} (hy : y 0 < 0)
    (τ : Fin (d + 1) → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion (d + 1)) :
    osiiAxisPairLowerSideCLMC (d := d) OS lgc F G y
        (section43TimeImagAxisProductKernel τ) =
      OSInnerProductTimeShiftHolomorphicValueExpandBoth
        (d := d) OS lgc F G (((τ 0 + (-y 0) : ℝ) : ℂ)) := by
  have hheight : 0 < -y 0 := neg_pos.mpr hy
  have hhead :
      OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
          (d := d) OS lgc F G (-y 0) hheight
          (osiiAxisPairHeadRestrictionCLM d
            (section43TimeImagAxisProductKernel τ)) =
        OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
          (d := d) OS lgc F G (-y 0) hheight
          (section43PsiZTimeTest (τ 0) (hτ 0)) :=
    OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_eq_of_eqOn_nonneg
      (d := d) OS lgc F G hheight
      (osiiAxisPairHeadRestriction_timeImagAxisProductKernel_eqOn_nonneg
        (d := d) τ hτ)
  calc
    osiiAxisPairLowerSideCLMC (d := d) OS lgc F G y
        (section43TimeImagAxisProductKernel τ)
        =
      OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
          (d := d) OS lgc F G (-y 0) hheight
          (osiiAxisPairHeadRestrictionCLM d
            (section43TimeImagAxisProductKernel τ)) := by
          simp [osiiAxisPairLowerSideCLMC, hy]
    _ =
      OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
          (d := d) OS lgc F G (-y 0) hheight
          (section43PsiZTimeTest (τ 0) (hτ 0)) := hhead
    _ =
      OSInnerProductTimeShiftHolomorphicValueExpandBoth
        (d := d) OS lgc F G (((τ 0 + (-y 0) : ℝ) : ℂ)) := by
          simpa [section43PsiZTimeTest] using
            OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_psiZ_eq
              (d := d) OS lgc F G (hτ 0) hheight

/-- Positive finite-height product-source formula for the raw axis-pair CLM.

This is the Section 4.3 product-source form of OS II `(5.7)`--`(5.8)`: the
flattened product tensor is rewritten pointwise on the compact strict-positive
source support, and the off-support part vanishes by the definition of
`tsupport`. -/
theorem osiiAxisPairPositiveSideCLMC_timeProductTensor_finiteHeight
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    {y : Fin (d + 1) → ℝ} (hy : 0 < y 0)
    (gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D) :
    osiiAxisPairPositiveSideCLMC (d := d) OS lgc F G y
        (section43TimeProductTensor
          (fun i : Fin (d + 1) =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) =
      ∫ τ : Fin (d + 1) → ℝ,
        OSInnerProductTimeShiftHolomorphicValueExpandBoth
          (d := d) OS lgc F G (((τ 0 + y 0 : ℝ) : ℂ)) *
          (section43TimeProductSource gs).f τ := by
  rw [osiiAxisPairPositiveSideCLMC_timeProductTensor_flattened]
  apply integral_congr_ae
  filter_upwards with τ
  by_cases hτ :
      τ ∈ tsupport
        ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ)
  · have hτ_pos :
        τ ∈ section43TimeStrictPositiveRegion (d + 1) :=
      (section43TimeProductSource gs).positive hτ
    rw [osiiAxisPairPositiveSideCLMC_timeImagAxisProductKernel_finiteHeight
      (d := d) OS lgc F G hy τ hτ_pos]
  · have hzero : (section43TimeProductSource gs).f τ = 0 :=
      image_eq_zero_of_notMem_tsupport hτ
    simp [hzero]

/-- Lower finite-height product-source formula for the raw axis-pair CLM. -/
theorem osiiAxisPairLowerSideCLMC_timeProductTensor_finiteHeight
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    {y : Fin (d + 1) → ℝ} (hy : y 0 < 0)
    (gs : Fin (d + 1) → Section43CompactPositiveTimeSource1D) :
    osiiAxisPairLowerSideCLMC (d := d) OS lgc F G y
        (section43TimeProductTensor
          (fun i : Fin (d + 1) =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i))) =
      ∫ τ : Fin (d + 1) → ℝ,
        OSInnerProductTimeShiftHolomorphicValueExpandBoth
          (d := d) OS lgc F G (((τ 0 + (-y 0) : ℝ) : ℂ)) *
          (section43TimeProductSource gs).f τ := by
  rw [osiiAxisPairLowerSideCLMC_timeProductTensor_flattened]
  apply integral_congr_ae
  filter_upwards with τ
  by_cases hτ :
      τ ∈ tsupport
        ((section43TimeProductSource gs).f :
          (Fin (d + 1) → ℝ) → ℂ)
  · have hτ_pos :
        τ ∈ section43TimeStrictPositiveRegion (d + 1) :=
      (section43TimeProductSource gs).positive hτ
    rw [osiiAxisPairLowerSideCLMC_timeImagAxisProductKernel_finiteHeight
      (d := d) OS lgc F G hy τ hτ_pos]
  · have hzero : (section43TimeProductSource gs).f τ = 0 :=
      image_eq_zero_of_notMem_tsupport hτ
    simp [hzero]

/-- The concrete positive/lower raw axis-pair CLMs supply the fixed-window
Section 4.3 selector packet, with a common boundary CLM. -/
theorem osiiAxisPair_fixedWindow_selectorData
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    {Cplus Cminus : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cplus] (0 : Fin (d + 1) → ℝ))]
    [NeBot (𝓝[Cminus] (0 : Fin (d + 1) → ℝ))]
    (hCplus_pos : Cplus ⊆ {y : Fin (d + 1) → ℝ | 0 < y 0})
    (hCminus_neg : Cminus ⊆ {y : Fin (d + 1) → ℝ | y 0 < 0}) :
    (∀ y (φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ),
      osiiAxisPairPositiveSideCLMR (d := d) OS lgc F G y φ =
        osiiAxisPairPositiveSideCLMC (d := d) OS lgc F G y φ) ∧
    (∀ y (φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ),
      osiiAxisPairLowerSideCLMR (d := d) OS lgc F G y φ =
        osiiAxisPairLowerSideCLMC (d := d) OS lgc F G y φ) ∧
    (∀ y (φ ψ : SchwartzMap (Fin (d + 1) → ℝ) ℂ),
      section43TimePositiveQuotientMap (d + 1) φ =
        section43TimePositiveQuotientMap (d + 1) ψ →
      osiiAxisPairPositiveSideCLMR (d := d) OS lgc F G y φ =
        osiiAxisPairPositiveSideCLMR (d := d) OS lgc F G y ψ) ∧
    (∀ y (φ ψ : SchwartzMap (Fin (d + 1) → ℝ) ℂ),
      section43TimePositiveQuotientMap (d + 1) φ =
        section43TimePositiveQuotientMap (d + 1) ψ →
      osiiAxisPairLowerSideCLMR (d := d) OS lgc F G y φ =
        osiiAxisPairLowerSideCLMR (d := d) OS lgc F G y ψ) ∧
    (∀ φ ψ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
      section43TimePositiveQuotientMap (d + 1) φ =
        section43TimePositiveQuotientMap (d + 1) ψ →
      osiiAxisPairBoundaryCLMR (d := d) OS lgc F G φ =
        osiiAxisPairBoundaryCLMR (d := d) OS lgc F G ψ) ∧
    (∀ ξ : Fin (d + 1) → ℝ,
      ξ ∈ section43TimeStrictPositiveRegion (d + 1) →
      Tendsto
        (fun y : Fin (d + 1) → ℝ =>
          osiiAxisPairPositiveSideCLMC (d := d) OS lgc F G y
            (section43TimeImagAxisProductKernel ξ))
        (𝓝[Cplus] (0 : Fin (d + 1) → ℝ))
        (nhds
          (osiiAxisPairBoundaryCLMC (d := d) OS lgc F G
            (section43TimeImagAxisProductKernel ξ)))) ∧
    (∀ ξ : Fin (d + 1) → ℝ,
      ξ ∈ section43TimeStrictPositiveRegion (d + 1) →
      Tendsto
        (fun y : Fin (d + 1) → ℝ =>
          osiiAxisPairLowerSideCLMC (d := d) OS lgc F G y
            (section43TimeImagAxisProductKernel ξ))
        (𝓝[Cminus] (0 : Fin (d + 1) → ℝ))
        (nhds
          (osiiAxisPairBoundaryCLMC (d := d) OS lgc F G
            (section43TimeImagAxisProductKernel ξ)))) ∧
    (∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ, ∃ C : ℝ,
      ∀ y : Fin (d + 1) → ℝ,
        ‖(osiiAxisPairPositiveSideCLMR (d := d) OS lgc F G y -
          osiiAxisPairBoundaryCLMR (d := d) OS lgc F G) φ‖ ≤ C) ∧
    (∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ, ∃ C : ℝ,
      ∀ y : Fin (d + 1) → ℝ,
        ‖(osiiAxisPairLowerSideCLMR (d := d) OS lgc F G y -
          osiiAxisPairBoundaryCLMR (d := d) OS lgc F G) φ‖ ≤ C) := by
  classical
  rcases
    osiiAxisPair_vectorCLMSide_descent_and_pointwise_bounded
      (d := d) OS lgc F G with
    ⟨hplus_desc, hboundary_desc, hplus_bound⟩
  rcases
    osiiAxisPair_vectorCLMSide_lower_descent_and_pointwise_bounded
      (d := d) OS lgc F G with
    ⟨hminus_desc, _hboundary_desc_lower, hminus_bound⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y φ
    rfl
  · intro y φ
    rfl
  · intro y φ ψ hq
    simpa [osiiAxisPairPositiveSideCLMR, osiiAxisPairPositiveSideCLMC,
      osiiAxisPairBoundaryCLMR, osiiAxisPairBoundaryCLMC] using
      hplus_desc y φ ψ hq
  · intro y φ ψ hq
    simpa [osiiAxisPairLowerSideCLMR, osiiAxisPairLowerSideCLMC,
      osiiAxisPairBoundaryCLMR, osiiAxisPairBoundaryCLMC] using
      hminus_desc y φ ψ hq
  · intro φ ψ hq
    simpa [osiiAxisPairBoundaryCLMR, osiiAxisPairBoundaryCLMC] using
      hboundary_desc φ ψ hq
  · intro ξ hξ
    simpa [osiiAxisPairPositiveSideCLMC, osiiAxisPairBoundaryCLMC] using
      osiiAxisPair_vectorProductKernel_boundary_selector_sideCone
        (d := d) OS lgc F G hCplus_pos ξ hξ
  · intro ξ hξ
    simpa [osiiAxisPairLowerSideCLMC, osiiAxisPairBoundaryCLMC] using
      osiiAxisPair_vectorProductKernel_boundary_selector_lowerSideCone
        (d := d) OS lgc F G hCminus_neg ξ hξ
  · intro φ
    simpa [osiiAxisPairPositiveSideCLMR, osiiAxisPairPositiveSideCLMC,
      osiiAxisPairBoundaryCLMR, osiiAxisPairBoundaryCLMC] using
      hplus_bound φ
  · intro φ
    simpa [osiiAxisPairLowerSideCLMR, osiiAxisPairLowerSideCLMC,
      osiiAxisPairBoundaryCLMR, osiiAxisPairBoundaryCLMC] using
      hminus_bound φ

/-- Fixed-window local EOW branch representations for the concrete raw
axis-pair selector family.

The remaining hypotheses are exactly the geometric prepared-domain data and
the side integral identities for the chosen axis-pair/MZ branches.  The
Section 4.3 selector, descent, and boundedness requirements are discharged here
from the raw OS semigroup CLMs on the positive and lower side cones. -/
theorem osiiAxisPair_fixedWindow_branchRepresentations_from_raw_selectors
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    {Cplus Cminus : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cplus] (0 : Fin (d + 1) → ℝ))]
    [NeBot (𝓝[Cminus] (0 : Fin (d + 1) → ℝ))]
    (hCplus_pos : Cplus ⊆ {y : Fin (d + 1) → ℝ | 0 < y 0})
    (hCminus_neg : Cminus ⊆ {y : Fin (d + 1) → ℝ | y 0 < 0})
    {rψLarge rψOne ρ r δ σ : ℝ}
    (hδ : 0 < δ) (hσ : 0 < σ)
    (hδscale : 128 * σ ≤ δ)
    (hσρ : 4 * σ ≤ ρ)
    (hcardσ : (Fintype.card (Fin (d + 1)) : ℝ) * (4 * σ) < r)
    (Ωplus Ωminus Dplus Dminus : Set (SCV.ComplexChartSpace (d + 1)))
    (E Kreal : Set (Fin (d + 1) → ℝ))
    (hΩplus_open : IsOpen Ωplus) (hΩminus_open : IsOpen Ωminus)
    (hDplus_open : IsOpen Dplus) (hDminus_open : IsOpen Dminus)
    (hE_open : IsOpen E)
    (hDplus_Ω : Dplus ⊆ Ωplus)
    (hDminus_Ω : Dminus ⊆ Ωminus)
    (Fplus Fminus : SCV.ComplexChartSpace (d + 1) → ℂ)
    (hFplus_diff : DifferentiableOn ℂ Fplus Ωplus)
    (hFminus_diff : DifferentiableOn ℂ Fminus Ωminus)
    (hplus_margin_closed :
      ∀ z ∈ Dplus, ∀ t ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) rψLarge,
        z + SCV.realEmbed t ∈ Ωplus)
    (hminus_margin_closed :
      ∀ z ∈ Dminus, ∀ t ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) rψLarge,
        z + SCV.realEmbed t ∈ Ωminus)
    (hDplus_sub : Dplus ⊆ SCV.TubeDomain Cplus)
    (hDminus_sub : Dminus ⊆ SCV.TubeDomain Cminus)
    (hplus_eval :
      ∀ ψ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
        SCV.KernelSupportWithin ψ rψLarge →
        ∀ w ∈ Dplus,
          SCV.realMollifyLocal Fplus ψ w =
            osiiAxisPairPositiveSideCLMR (d := d) OS lgc F G
              (fun i => (w i).im)
              (SCV.translateSchwartz (fun i => - (w i).re) ψ))
    (hminus_eval :
      ∀ ψ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
        SCV.KernelSupportWithin ψ rψLarge →
        ∀ w ∈ Dminus,
          SCV.realMollifyLocal Fminus ψ w =
            osiiAxisPairLowerSideCLMR (d := d) OS lgc F G
              (fun i => (w i).im)
              (SCV.translateSchwartz (fun i => - (w i).re) ψ))
    (x0 : Fin (d + 1) → ℝ) (ys : Fin (d + 1) → Fin (d + 1) → ℝ)
    (hli : LinearIndependent ℝ ys)
    (hδρ : δ * 10 ≤ ρ)
    (hδsum : (Fintype.card (Fin (d + 1)) : ℝ) * (δ * 10) < r)
    (hE_mem :
      ∀ u ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) ρ,
        SCV.localEOWRealChart x0 ys u ∈ E)
    (hKreal_compact : IsCompact Kreal)
    (hKreal_mem :
      ∀ u ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) ρ,
        SCV.localEOWRealChart x0 ys u ∈ Kreal)
    (hplus :
      ∀ u ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) ρ,
        ∀ v : Fin (d + 1) → ℝ,
          (∀ j, 0 ≤ v j) →
          0 < ∑ j, v j →
          (∑ j, v j) < r →
            SCV.localEOWChart x0 ys
              (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dplus)
    (hminus :
      ∀ u ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) ρ,
        ∀ v : Fin (d + 1) → ℝ,
          (∀ j, v j ≤ 0) →
          0 < ∑ j, -v j →
          (∑ j, -v j) < r →
            SCV.localEOWChart x0 ys
              (fun j => (u j : ℂ) + (v j : ℂ) * Complex.I) ∈ Dminus)
    (χU : SchwartzMap (SCV.ComplexChartSpace (d + 1)) ℂ)
    (χr χψ : SchwartzMap (Fin (d + 1) → ℝ) ℂ)
    (hχU_one :
      ∀ z ∈ Metric.closedBall (0 : SCV.ComplexChartSpace (d + 1)) (8 * σ),
        χU z = 1)
    (hχr_one :
      ∀ t ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) (2 * σ), χr t = 1)
    (hχr_support :
      tsupport (χr : (Fin (d + 1) → ℝ) → ℂ) ⊆
        Metric.closedBall 0 (4 * σ))
    (hχψ_one :
      ∀ t ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) rψOne, χψ t = 1)
    (hχψ_support :
      tsupport (χψ : (Fin (d + 1) → ℝ) → ℂ) ⊆
        Metric.closedBall 0 rψLarge)
    (hA4_one :
      ‖(SCV.localEOWRealLinearCLE ys hli).toContinuousLinearMap‖ *
          (4 * σ) ≤ rψOne)
    (hrψ_one_large : rψOne ≤ rψLarge) :
    let FplusCoord : SCV.ComplexChartSpace (d + 1) → ℂ :=
      fun ζ => Fplus (SCV.localEOWChart x0 ys ζ)
    let FminusCoord : SCV.ComplexChartSpace (d + 1) → ℂ :=
      fun ζ => Fminus (SCV.localEOWChart x0 ys ζ)
    ∃ Hdist : SchwartzMap (SCV.ComplexChartSpace (d + 1)) ℂ →L[ℂ] ℂ,
      SCV.RepresentsDistributionOnComplexDomain Hdist FplusCoord
        (SCV.StrictPositiveImagBall (m := d + 1) σ) ∧
      SCV.RepresentsDistributionOnComplexDomain Hdist FminusCoord
        (SCV.StrictNegativeImagBall (m := d + 1) σ) := by
  classical
  rcases
    osiiAxisPair_fixedWindow_selectorData
      (d := d) OS lgc F G hCplus_pos hCminus_neg with
    ⟨hTplus_apply, hTminus_apply, hTplus_desc, hTminus_desc,
      hTchart_desc, hplus_kernel, hminus_kernel, hplus_bound, hminus_bound⟩
  exact
    osiiFixedWindow_branchRepresentations_from_section43_selectors
      (m := d + 1) (Cplus := Cplus) (Cminus := Cminus)
      (rψLarge := rψLarge) (rψOne := rψOne) (ρ := ρ)
      (r := r) (δ := δ) (σ := σ)
      (hm := Nat.succ_pos d) hδ hσ hδscale hσρ hcardσ
      Ωplus Ωminus Dplus Dminus E Kreal hΩplus_open hΩminus_open
      hDplus_open hDminus_open hE_open hDplus_Ω hDminus_Ω
      Fplus Fminus hFplus_diff hFminus_diff hplus_margin_closed
      hminus_margin_closed hDplus_sub hDminus_sub
      (osiiAxisPairPositiveSideCLMC (d := d) OS lgc F G)
      (osiiAxisPairLowerSideCLMC (d := d) OS lgc F G)
      (osiiAxisPairPositiveSideCLMR (d := d) OS lgc F G)
      (osiiAxisPairLowerSideCLMR (d := d) OS lgc F G)
      (osiiAxisPairBoundaryCLMC (d := d) OS lgc F G)
      hTplus_apply hTminus_apply hTplus_desc hTminus_desc
      hTchart_desc hplus_kernel hminus_kernel hplus_bound hminus_bound
      hplus_eval hminus_eval x0 ys hli hδρ hδsum hE_mem hKreal_compact
      hKreal_mem hplus hminus χU χr χψ hχU_one hχr_one hχr_support
      hχψ_one hχψ_support hA4_one hrψ_one_large

end OSReconstruction
