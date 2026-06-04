import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanOSIILemma51AxisPairTotalBranch
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43SpectralFactorization

/-!
# OS-II Axis-Pair Raw CLM Selectors

This file records the raw `(5.7)`--`(5.8)` selector bridge for the actual
axis-pair/Malgrange-Zerner branch.  The point is not to introduce a new
assumption: the theorem expands the existing regularized semigroup CLM on the
Section 4.3 Paley test and applies the checked axis-pair selector packet.
-/

noncomputable section

open Complex Topology Filter
open scoped Classical

namespace OSReconstruction

private instance instAxisPairTimeSchwartzCompatibleSMul {m : ℕ} :
    LinearMap.CompatibleSMul (SchwartzMap (Fin m → ℝ) ℂ) ℂ ℝ ℂ where
  map_smul := by
    intro f r x
    have hx : r • x = (r : ℂ) • x := by
      ext t
      simp
    rw [hx]
    simpa using f.map_smul (r : ℂ) x

/-- Restrict a `Fin (d + 1)` finite-time test to the physical time axis, with
the Section 4.3 `2π` normalization.  On product imaginary-axis kernels this
keeps the `0`-th factor and evaluates every other factor at zero. -/
noncomputable def osiiAxisPairHeadRestrictionCLM (d : ℕ) :
    SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] SchwartzMap ℝ ℂ := by
  let L : ℝ →L[ℝ] Fin (d + 1) → ℝ :=
    ContinuousLinearMap.pi fun ν : Fin (d + 1) =>
      if ν = 0 then (2 * Real.pi) • (1 : ℝ →L[ℝ] ℝ) else 0
  let g : ℝ → Fin (d + 1) → ℝ := fun x => L x
  have hg : g.HasTemperateGrowth := by
    exact L.hasTemperateGrowth
  have hg_upper :
      ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖g x‖) ^ k := by
    refine ⟨1, 1, ?_⟩
    intro x
    have hcoord :
        ‖(2 * Real.pi) * x‖ ≤ ‖g x‖ := by
      simpa [g, L] using norm_le_pi_norm (g x) (0 : Fin (d + 1))
    have hfactor : (1 : ℝ) ≤ ‖(2 * Real.pi : ℝ)‖ := by
      rw [Real.norm_eq_abs, abs_of_pos Real.two_pi_pos]
      nlinarith [Real.pi_gt_three]
    have hx_scaled : ‖x‖ ≤ ‖(2 * Real.pi) * x‖ := by
      rw [norm_mul]
      simpa [one_mul] using
        mul_le_mul_of_nonneg_right hfactor (norm_nonneg x)
    calc
      ‖x‖ ≤ ‖g x‖ := hx_scaled.trans hcoord
      _ ≤ 1 * (1 + ‖g x‖) ^ (1 : ℕ) := by
        simp [le_add_of_nonneg_left (zero_le_one : (0 : ℝ) ≤ 1)]
  exact SchwartzMap.compCLM (𝕜 := ℂ) (g := g) hg hg_upper

@[simp] theorem osiiAxisPairHeadRestrictionCLM_apply
    (d : ℕ) (Φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ) (x : ℝ) :
    osiiAxisPairHeadRestrictionCLM d Φ x =
      Φ (fun ν : Fin (d + 1) =>
        if ν = 0 then (2 * Real.pi) * x else 0) := by
  simp [osiiAxisPairHeadRestrictionCLM]
  congr 1
  ext ν
  by_cases hν : ν = 0 <;> simp [hν]

/-- The raw axis-pair head restriction collapses a full finite-time product
tensor to the physical head factor and evaluates every non-head factor at
zero.  This is the source-current shape that prevents identifying the raw
one-dimensional head current with an arbitrary `(d+1)`-slot A0 product current
without a separate comparison. -/
theorem osiiAxisPairHeadRestriction_productTensor_apply
    (d : ℕ) (fs : Fin (d + 1) → SchwartzMap ℝ ℂ) (x : ℝ) :
    osiiAxisPairHeadRestrictionCLM d (section43TimeProductTensor fs) x =
      fs 0 ((2 * Real.pi) * x) *
        Finset.prod (Finset.univ.erase (0 : Fin (d + 1)))
          (fun ν => fs ν 0) := by
  rw [osiiAxisPairHeadRestrictionCLM_apply, section43TimeProductTensor,
    SchwartzMap.productTensor_apply]
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin (d + 1)))
    (fun ν : Fin (d + 1) =>
      fs ν (if ν = 0 then (2 * Real.pi) * x else 0))
    (Finset.mem_univ (0 : Fin (d + 1)))]
  simp only [↓reduceIte]
  congr 1
  apply Finset.prod_congr rfl
  intro ν hν
  have hν0 : ν ≠ (0 : Fin (d + 1)) := (Finset.mem_erase.mp hν).1
  simp [hν0]

/-- The head restriction sends a strict-positive vector product kernel to the
one-dimensional Paley test used by the raw axis-pair selector, on the
positive-energy half-line.  This is the quotient-level equality needed before
the one-dimensional raw CLM can be used inside the vector local-EOW packet. -/
theorem osiiAxisPairHeadRestriction_timeImagAxisProductKernel_eqOn_nonneg
    {d : ℕ} (τ : Fin (d + 1) → ℝ)
    (hτ : τ ∈ section43TimeStrictPositiveRegion (d + 1)) :
    Set.EqOn
      (osiiAxisPairHeadRestrictionCLM d
        (section43TimeImagAxisProductKernel τ))
      (section43PsiZTimeTest (τ 0) (hτ 0))
      {x : ℝ | 0 ≤ x} := by
  classical
  intro x hx
  have hscaled_nonneg : 0 ≤ (2 * Real.pi) * x :=
    mul_nonneg Real.two_pi_pos.le hx
  have hprod :
      (∏ ν : Fin (d + 1),
          section43ImagAxisPsiKernel (τ ν)
            (if ν = 0 then (2 * Real.pi) * x else 0)) =
        Complex.exp (-(τ 0 : ℂ) * (((2 * Real.pi) * x : ℝ) : ℂ)) := by
    rw [Finset.prod_eq_single (0 : Fin (d + 1))]
    · simp [section43ImagAxisPsiKernel_apply_of_pos_of_nonneg
        (hτ 0) hscaled_nonneg]
    · intro ν _hν hν0
      have hzero_nonneg : 0 ≤ (0 : ℝ) := le_rfl
      simp [hν0, section43ImagAxisPsiKernel_apply_of_pos_of_nonneg
        (hτ ν) hzero_nonneg]
    · simp
  rw [osiiAxisPairHeadRestrictionCLM_apply, section43TimeImagAxisProductKernel,
    section43TimeProductTensor, SchwartzMap.productTensor_apply,
    section43PsiZTimeTest_apply, SCV.psiZ_eq_exp_of_nonneg hx]
  rw [hprod]
  congr 1
  have hright :
      Complex.I * (2 * ↑Real.pi * (↑(τ 0) * Complex.I)) * ↑x =
        -↑(τ 0) * ↑(2 * Real.pi * x) := by
    rw [show
      Complex.I * (2 * ↑Real.pi * (↑(τ 0) * Complex.I)) * ↑x =
        (Complex.I * Complex.I) * (↑(τ 0) * ((2 * ↑Real.pi) * ↑x)) by
        ring]
    rw [Complex.I_mul_I]
    norm_num [ofReal_mul]
  exact hright.symm

/-- The head restriction transports finite-time positive quotient equality to
the one-dimensional positive-energy quotient. -/
theorem osiiAxisPairHeadRestriction_positiveEnergyQuotient_eq_of_timePositiveQuotient_eq
    {d : ℕ} {Φ Ψ : SchwartzMap (Fin (d + 1) → ℝ) ℂ}
    (hΦΨ :
      section43TimePositiveQuotientMap (d + 1) Φ =
        section43TimePositiveQuotientMap (d + 1) Ψ) :
    section43PositiveEnergyQuotientMap1D (osiiAxisPairHeadRestrictionCLM d Φ) =
      section43PositiveEnergyQuotientMap1D (osiiAxisPairHeadRestrictionCLM d Ψ) := by
  apply section43PositiveEnergyQuotientMap1D_eq_of_eqOn_nonneg
  intro x hx
  have hEq :=
    eqOn_region_of_section43TimePositiveQuotientMap_eq hΦΨ
  have hxvec :
      (fun ν : Fin (d + 1) =>
        if ν = 0 then (2 * Real.pi) * x else 0) ∈
        section43TimePositiveRegion (d + 1) := by
    intro ν
    by_cases hν : ν = 0
    · simp [hν, mul_nonneg Real.two_pi_pos.le hx]
    · simp [hν]
  simpa [osiiAxisPairHeadRestrictionCLM_apply] using hEq hxvec

theorem osiiAxisPair_timeShell_regularizedCLM_selector_to_branch
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      (∀ τ : Fin (d + 1) → ℝ,
        τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρ →
          ∃ htime : 0 < τ 0,
            Filter.Tendsto
              (fun η : {η : ℝ // 0 < η} =>
                OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
                    (d := d) OS lgc
                    (PositiveTimeBorchersSequence.single n f hf_ord)
                    (PositiveTimeBorchersSequence.single r g hg_ord)
                    η.1 η.2
                    (section43PsiZTimeTest (τ 0) htime))
              (Filter.comap (fun η : {η : ℝ // 0 < η} => η.1)
                (𝓝[Set.Ioi 0] (0 : ℝ)))
              (𝓝
                (osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                  f hf_ord g hg_ord T ξ
                  (fun ν : Fin (d + 1) => (τ ν : ℂ))))) := by
  classical
  rcases
    osiiAxisPair_weightedTotalLogSemigroupBranch_single_timeShell_local_packet
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ hξ0 with
    ⟨ρ, C, hρ, hC, _hdiff, _hreal, hselector, _hbound⟩
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro τ hτ
  rcases hselector τ hτ with ⟨htime, hlim⟩
  refine ⟨htime, ?_⟩
  have hlim_sub :
      Filter.Tendsto
        (fun η : {η : ℝ // 0 < η} =>
          ∫ x : ℝ,
            OSInnerProductTimeShiftHolomorphicValueExpandBoth
                (d := d) OS lgc
                (PositiveTimeBorchersSequence.single n f hf_ord)
                (PositiveTimeBorchersSequence.single r g hg_ord)
                (-Complex.I * ((x : ℂ) + η.1 * Complex.I)) *
              (SchwartzMap.fourierTransformCLM ℂ
                (SCV.schwartzPsiZ
                  (((2 * Real.pi : ℂ) *
                    (((τ 0 : ℝ) : ℂ) * Complex.I)))
                  (by
                    simpa [Complex.mul_im, htime.ne']
                      using mul_pos Real.two_pi_pos htime))) x)
        (Filter.comap (fun η : {η : ℝ // 0 < η} => η.1)
          (𝓝[Set.Ioi 0] (0 : ℝ)))
        (𝓝
          (osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single r g hg_ord) T
            (fun a : osiiAxisPairIndex d =>
              Complex.log
                (osiiAxisPairCoeffMap T ξ
                  (fun ν : Fin (d + 1) =>
                    (osiiAxisPairTimeShellPerturbation (d := d) ξ τ ν : ℂ)) a)))) := by
    exact hlim.comp Filter.tendsto_comap
  simpa [OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_apply,
    section43PsiZTimeTest, osiiAxisPairWeightedTimeShellBranch,
    osiiAxisPairTimeShellPerturbationC_ofReal] using hlim_sub

/-- Vector-side form of the raw axis-pair CLM selector bridge.

Local EOW uses a side-height vector.  The OS semigroup regularization height is
the physical time coordinate of that vector; on a side cone where this
coordinate is positive, the totalized CLM family has the same boundary value as
the one-parameter selector. -/
theorem osiiAxisPair_timeShell_regularizedCLM_selector_to_branch_sideCone
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cside : Set (Fin (d + 1) → ℝ)}
    (hCside_pos : Cside ⊆ {y : Fin (d + 1) → ℝ | 0 < y 0}) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      (∀ τ : Fin (d + 1) → ℝ,
        τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρ →
          ∃ htime : 0 < τ 0,
            Filter.Tendsto
              (fun y : Fin (d + 1) → ℝ =>
                if hy : 0 < y 0 then
                  OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
                      (d := d) OS lgc
                      (PositiveTimeBorchersSequence.single n f hf_ord)
                      (PositiveTimeBorchersSequence.single r g hg_ord)
                      (y 0) hy
                      (section43PsiZTimeTest (τ 0) htime)
                else 0)
              (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
              (𝓝
                (osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                  f hf_ord g hg_ord T ξ
                  (fun ν : Fin (d + 1) => (τ ν : ℂ))))) := by
  classical
  rcases
    osiiAxisPair_weightedTotalLogSemigroupBranch_single_timeShell_local_packet
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ hξ0 with
    ⟨ρ, C, hρ, hC, _hdiff, _hreal, hselector, _hbound⟩
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro τ hτ
  rcases hselector τ hτ with ⟨htime, hlim⟩
  refine ⟨htime, ?_⟩
  let rawIntegral : ℝ → ℂ := fun η =>
    ∫ x : ℝ,
      OSInnerProductTimeShiftHolomorphicValueExpandBoth
          (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single r g hg_ord)
          (-Complex.I * ((x : ℂ) + η * Complex.I)) *
        (SchwartzMap.fourierTransformCLM ℂ
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) *
              (((τ 0 : ℝ) : ℂ) * Complex.I)))
            (by
              simpa [Complex.mul_im, htime.ne']
                using mul_pos Real.two_pi_pos htime))) x
  have hlim_side :
      Filter.Tendsto
        (fun y : Fin (d + 1) → ℝ => rawIntegral (y 0))
        (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
        (𝓝
          (osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single r g hg_ord) T
            (fun a : osiiAxisPairIndex d =>
              Complex.log
                (osiiAxisPairCoeffMap T ξ
                  (fun ν : Fin (d + 1) =>
                    (osiiAxisPairTimeShellPerturbation (d := d) ξ τ ν : ℂ)) a)))) := by
    have hcoord :
        Tendsto (fun y : Fin (d + 1) → ℝ => y 0)
          (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
          (𝓝[Set.Ioi 0] (0 : ℝ)) := by
      exact (continuous_apply 0).continuousWithinAt.tendsto_nhdsWithin hCside_pos
    simpa [rawIntegral] using hlim.comp hcoord
  have heq :
      (fun y : Fin (d + 1) → ℝ =>
        if hy : 0 < y 0 then
          OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
              (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single r g hg_ord)
              (y 0) hy
              (section43PsiZTimeTest (τ 0) htime)
        else 0) =ᶠ[𝓝[Cside] (0 : Fin (d + 1) → ℝ)]
        fun y : Fin (d + 1) → ℝ => rawIntegral (y 0) := by
    filter_upwards [self_mem_nhdsWithin] with y hyC
    have hypos : 0 < y 0 := hCside_pos hyC
    simp [hypos, rawIntegral,
      OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_apply,
      section43PsiZTimeTest]
  have htarget :
      osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single r g hg_ord) T
          (fun a : osiiAxisPairIndex d =>
            Complex.log
              (osiiAxisPairCoeffMap T ξ
                (fun ν : Fin (d + 1) =>
                  (osiiAxisPairTimeShellPerturbation (d := d) ξ τ ν : ℂ)) a)) =
        osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
          f hf_ord g hg_ord T ξ
          (fun ν : Fin (d + 1) => (τ ν : ℂ)) := by
    simp [osiiAxisPairWeightedTimeShellBranch,
      osiiAxisPairTimeShellPerturbationC_ofReal]
  exact (tendsto_congr' heq).2 (by simpa [htarget] using hlim_side)

/-- Lower-side vector form of the raw axis-pair selector bridge.

The lower local-EOW side approaches the boundary through `y 0 < 0`; the
positive OS semigroup regularization height is therefore `-y 0`.  This is the
lower analogue of `osiiAxisPair_timeShell_regularizedCLM_selector_to_branch_sideCone`
with the same MZ time-shell branch as target. -/
theorem osiiAxisPair_timeShell_regularizedCLM_selector_to_branch_lowerSideCone
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cside : Set (Fin (d + 1) → ℝ)}
    (hCside_neg : Cside ⊆ {y : Fin (d + 1) → ℝ | y 0 < 0}) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      (∀ τ : Fin (d + 1) → ℝ,
        τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρ →
          ∃ htime : 0 < τ 0,
            Filter.Tendsto
              (fun y : Fin (d + 1) → ℝ =>
                if hy : y 0 < 0 then
                  OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
                      (d := d) OS lgc
                      (PositiveTimeBorchersSequence.single n f hf_ord)
                      (PositiveTimeBorchersSequence.single r g hg_ord)
                      (-y 0) (neg_pos.mpr hy)
                      (section43PsiZTimeTest (τ 0) htime)
                else 0)
              (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
              (𝓝
                (osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
                  f hf_ord g hg_ord T ξ
                  (fun ν : Fin (d + 1) => (τ ν : ℂ))))) := by
  classical
  rcases
    osiiAxisPair_weightedTotalLogSemigroupBranch_single_timeShell_local_packet
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ hξ0 with
    ⟨ρ, C, hρ, hC, _hdiff, _hreal, hselector, _hbound⟩
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro τ hτ
  rcases hselector τ hτ with ⟨htime, hlim⟩
  refine ⟨htime, ?_⟩
  let rawIntegral : ℝ → ℂ := fun η =>
    ∫ x : ℝ,
      OSInnerProductTimeShiftHolomorphicValueExpandBoth
          (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single r g hg_ord)
          (-Complex.I * ((x : ℂ) + η * Complex.I)) *
        (SchwartzMap.fourierTransformCLM ℂ
          (SCV.schwartzPsiZ
            (((2 * Real.pi : ℂ) *
              (((τ 0 : ℝ) : ℂ) * Complex.I)))
            (by
              simpa [Complex.mul_im, htime.ne']
                using mul_pos Real.two_pi_pos htime))) x
  have hCside_pos_height :
      Cside ⊆ {y : Fin (d + 1) → ℝ | 0 < -y 0} := by
    intro y hy
    exact neg_pos.mpr (by simpa using hCside_neg hy)
  have hcoord :
      Tendsto (fun y : Fin (d + 1) → ℝ => -y 0)
        (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
        (𝓝[Set.Ioi 0] (0 : ℝ)) := by
    have hcoord0 :
        Tendsto (fun y : Fin (d + 1) → ℝ => -y 0)
          (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
          (𝓝[Set.Ioi 0] (-(0 : Fin (d + 1) → ℝ) 0)) := by
      exact ((continuous_apply 0).neg).continuousWithinAt.tendsto_nhdsWithin
        hCside_pos_height
    simpa using hcoord0
  have hlim_side :
      Filter.Tendsto
        (fun y : Fin (d + 1) → ℝ => rawIntegral (-y 0))
        (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
        (𝓝
          (osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
            (PositiveTimeBorchersSequence.single n f hf_ord)
            (PositiveTimeBorchersSequence.single r g hg_ord) T
            (fun a : osiiAxisPairIndex d =>
              Complex.log
                (osiiAxisPairCoeffMap T ξ
                  (fun ν : Fin (d + 1) =>
                    (osiiAxisPairTimeShellPerturbation (d := d) ξ τ ν : ℂ)) a)))) := by
    simpa only [Function.comp_apply] using hlim.comp hcoord
  have heq :
      (fun y : Fin (d + 1) → ℝ =>
        if hy : y 0 < 0 then
          OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
              (d := d) OS lgc
              (PositiveTimeBorchersSequence.single n f hf_ord)
              (PositiveTimeBorchersSequence.single r g hg_ord)
              (-y 0) (neg_pos.mpr hy)
              (section43PsiZTimeTest (τ 0) htime)
        else 0) =ᶠ[𝓝[Cside] (0 : Fin (d + 1) → ℝ)]
        fun y : Fin (d + 1) → ℝ => rawIntegral (-y 0) := by
    filter_upwards [self_mem_nhdsWithin] with y hyC
    have hyneg : y 0 < 0 := hCside_neg hyC
    simp [hyneg, rawIntegral,
      OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_apply,
      section43PsiZTimeTest]
  have htarget :
      osiiAxisPairWeightedTotalLogSemigroupBranch (d := d) OS lgc
          (PositiveTimeBorchersSequence.single n f hf_ord)
          (PositiveTimeBorchersSequence.single r g hg_ord) T
          (fun a : osiiAxisPairIndex d =>
            Complex.log
              (osiiAxisPairCoeffMap T ξ
                (fun ν : Fin (d + 1) =>
                  (osiiAxisPairTimeShellPerturbation (d := d) ξ τ ν : ℂ)) a)) =
        osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
          f hf_ord g hg_ord T ξ
          (fun ν : Fin (d + 1) => (τ ν : ℂ)) := by
    simp [osiiAxisPairWeightedTimeShellBranch,
      osiiAxisPairTimeShellPerturbationC_ofReal]
  exact (tendsto_congr' heq).2 (by simpa [htarget] using hlim_side)

/-- Quotient descent and pointwise boundedness for the same raw side CLM
family used in the axis-pair selector bridge.

These are the Banach-Steinhaus-facing hypotheses in OS II `(5.7)`--`(5.8)`:
the positive-height regularized CLMs and the spectral boundary target descend
to the one-sided positive-time quotient, and their difference is pointwise
bounded uniformly in the side-height parameter. -/
theorem osiiAxisPair_rawCLMSide_descent_and_pointwise_bounded
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) :
    let TseqC : (Fin (d + 1) → ℝ) → SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
      fun y =>
        if hy : 0 < y 0 then
          OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
            (d := d) OS lgc F G (y 0) hy
        else 0
    let TseqR : (Fin (d + 1) → ℝ) → SchwartzMap ℝ ℂ →L[ℝ] ℂ :=
      fun y => (TseqC y).restrictScalars ℝ
    let T : SchwartzMap ℝ ℂ →L[ℝ] ℂ :=
      (OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
        (d := d) OS lgc F G).restrictScalars ℝ
    (∀ y (φ ψ : SchwartzMap ℝ ℂ),
      section43PositiveEnergyQuotientMap1D φ =
        section43PositiveEnergyQuotientMap1D ψ →
        TseqR y φ = TseqR y ψ) ∧
    (∀ φ ψ : SchwartzMap ℝ ℂ,
      section43PositiveEnergyQuotientMap1D φ =
        section43PositiveEnergyQuotientMap1D ψ →
        T φ = T ψ) ∧
    (∀ φ : SchwartzMap ℝ ℂ, ∃ C : ℝ,
      ∀ y : Fin (d + 1) → ℝ, ‖(TseqR y - T) φ‖ ≤ C) := by
  classical
  intro TseqC TseqR T
  refine ⟨?_, ?_, ?_⟩
  · intro y φ ψ hq
    have hφψ := eqOn_nonneg_of_section43PositiveEnergyQuotientMap1D_eq hq
    by_cases hy : 0 < y 0
    · simp [TseqR, TseqC, hy,
        OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_eq_of_eqOn_nonneg
          (d := d) OS lgc F G hy hφψ]
    · simp [TseqR, TseqC, hy]
  · intro φ ψ hq
    have hφψ := eqOn_nonneg_of_section43PositiveEnergyQuotientMap1D_eq hq
    simp [T,
      OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM_eq_of_eqOn_nonneg
        (d := d) OS lgc F G hφψ]
  · intro φ
    rcases
      exists_bound_OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_boundaryDifference_posSubtype_restrictScalars
        (d := d) OS lgc F G φ with
      ⟨C, hC_nonneg, hC_bound⟩
    refine ⟨C + ‖T φ‖, ?_⟩
    intro y
    by_cases hy : 0 < y 0
    · have hpos := hC_bound ⟨y 0, hy⟩
      calc
        ‖(TseqR y - T) φ‖ ≤ C := by
          simpa [TseqR, TseqC, T, hy] using hpos
        _ ≤ C + ‖T φ‖ := by
          exact le_add_of_nonneg_right (norm_nonneg _)
    · calc
        ‖(TseqR y - T) φ‖ = ‖T φ‖ := by
          simp [TseqR, TseqC, hy]
        _ ≤ C + ‖T φ‖ := by
          exact le_add_of_nonneg_left hC_nonneg

/-- Strict-positive vector product kernels select the spectral boundary CLM
after transporting the raw axis-pair family through the head restriction. -/
theorem osiiAxisPair_vectorProductKernel_boundary_selector_sideCone
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    {Cside : Set (Fin (d + 1) → ℝ)}
    (hCside_pos : Cside ⊆ {y : Fin (d + 1) → ℝ | 0 < y 0}) :
    let TseqC : (Fin (d + 1) → ℝ) →
        SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
      fun y =>
        (if hy : 0 < y 0 then
          OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
            (d := d) OS lgc F G (y 0) hy
        else 0).comp (osiiAxisPairHeadRestrictionCLM d)
    let TC : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
      (OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
        (d := d) OS lgc F G).comp (osiiAxisPairHeadRestrictionCLM d)
    ∀ τ : Fin (d + 1) → ℝ,
      τ ∈ section43TimeStrictPositiveRegion (d + 1) →
        Tendsto
          (fun y : Fin (d + 1) → ℝ =>
            TseqC y (section43TimeImagAxisProductKernel τ))
          (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
          (nhds (TC (section43TimeImagAxisProductKernel τ))) := by
  classical
  intro TseqC TC τ hτ
  let χ : SchwartzMap ℝ ℂ := section43PsiZTimeTest (τ 0) (hτ 0)
  have hcoord :
      Tendsto (fun y : Fin (d + 1) → ℝ => y 0)
        (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
        (𝓝[Set.Ioi 0] (0 : ℝ)) := by
    exact (continuous_apply 0).continuousWithinAt.tendsto_nhdsWithin hCside_pos
  let rawIntegral : ℝ → ℂ := fun η =>
    ∫ x : ℝ,
      OSInnerProductTimeShiftHolomorphicValueExpandBoth
          (d := d) OS lgc F G
          (-Complex.I * ((x : ℂ) + η * Complex.I)) *
        (SchwartzMap.fourierTransformCLM ℂ χ) x
  have hraw :
      Tendsto
        rawIntegral
        (𝓝[Set.Ioi 0] (0 : ℝ))
        (nhds
          (OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
            (d := d) OS lgc F G χ)) := by
    simpa [rawIntegral, OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM_apply]
      using
        tendsto_rotated_OSInnerProductTimeShiftHolomorphicValueExpandBoth_boundaryValue_fourierTransform
          (d := d) OS lgc F G χ
  have hraw_side :
      Tendsto
        (fun y : Fin (d + 1) → ℝ =>
          if hy : 0 < y 0 then
            OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
              (d := d) OS lgc F G (y 0) hy χ
          else 0)
        (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
        (nhds
          (OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
            (d := d) OS lgc F G χ)) := by
    have hraw_comp :
        Tendsto (fun y : Fin (d + 1) → ℝ => rawIntegral (y 0))
          (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
          (nhds
            (OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
              (d := d) OS lgc F G χ)) := by
      exact hraw.comp hcoord
    have heq :
        (fun y : Fin (d + 1) → ℝ =>
          if hy : 0 < y 0 then
            OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
              (d := d) OS lgc F G (y 0) hy χ
          else 0)
          =ᶠ[𝓝[Cside] (0 : Fin (d + 1) → ℝ)]
        fun y : Fin (d + 1) → ℝ => rawIntegral (y 0) := by
      filter_upwards [self_mem_nhdsWithin] with y hyC
      have hypos : 0 < y 0 := hCside_pos hyC
      simp [hypos, rawIntegral,
        OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_apply]
    exact (tendsto_congr' heq).2 hraw_comp
  have hsource :
      (fun y : Fin (d + 1) → ℝ =>
        TseqC y (section43TimeImagAxisProductKernel τ))
        =ᶠ[𝓝[Cside] (0 : Fin (d + 1) → ℝ)]
      fun y : Fin (d + 1) → ℝ =>
        if hy : 0 < y 0 then
          OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
            (d := d) OS lgc F G (y 0) hy χ
        else 0 := by
    filter_upwards [self_mem_nhdsWithin] with y hyC
    have hypos : 0 < y 0 := hCside_pos hyC
    have heq :=
      OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_eq_of_eqOn_nonneg
        (d := d) OS lgc F G hypos
        (osiiAxisPairHeadRestriction_timeImagAxisProductKernel_eqOn_nonneg τ hτ)
    simpa [TseqC, hypos, χ] using heq
  have htarget :
      TC (section43TimeImagAxisProductKernel τ) =
        OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
          (d := d) OS lgc F G χ := by
    simpa [TC, χ] using
      OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM_eq_of_eqOn_nonneg
        (d := d) OS lgc F G
        (osiiAxisPairHeadRestriction_timeImagAxisProductKernel_eqOn_nonneg τ hτ)
  exact (tendsto_congr' hsource).2 (by simpa [htarget] using hraw_side)

/-- Quotient descent and pointwise boundedness for the vector-side CLM family
obtained by composing the raw axis-pair side with the head restriction. -/
theorem osiiAxisPair_vectorCLMSide_descent_and_pointwise_bounded
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) :
    let TseqC : (Fin (d + 1) → ℝ) →
        SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
      fun y =>
        (if hy : 0 < y 0 then
          OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
            (d := d) OS lgc F G (y 0) hy
        else 0).comp (osiiAxisPairHeadRestrictionCLM d)
    let TseqR : (Fin (d + 1) → ℝ) →
        SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℝ] ℂ :=
      fun y => (TseqC y).restrictScalars ℝ
    let TC : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
      (OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
        (d := d) OS lgc F G).comp (osiiAxisPairHeadRestrictionCLM d)
    let TR : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℝ] ℂ :=
      TC.restrictScalars ℝ
    (∀ y (φ ψ : SchwartzMap (Fin (d + 1) → ℝ) ℂ),
      section43TimePositiveQuotientMap (d + 1) φ =
        section43TimePositiveQuotientMap (d + 1) ψ →
        TseqR y φ = TseqR y ψ) ∧
    (∀ φ ψ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
      section43TimePositiveQuotientMap (d + 1) φ =
        section43TimePositiveQuotientMap (d + 1) ψ →
        TR φ = TR ψ) ∧
    (∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ, ∃ C : ℝ,
      ∀ y : Fin (d + 1) → ℝ, ‖(TseqR y - TR) φ‖ ≤ C) := by
  classical
  intro TseqC TseqR TC TR
  refine ⟨?_, ?_, ?_⟩
  · intro y φ ψ hq
    have hhead_q :=
      osiiAxisPairHeadRestriction_positiveEnergyQuotient_eq_of_timePositiveQuotient_eq
        (d := d) hq
    have hhead_eq := eqOn_nonneg_of_section43PositiveEnergyQuotientMap1D_eq hhead_q
    by_cases hy : 0 < y 0
    · have heq :=
        OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_eq_of_eqOn_nonneg
          (d := d) OS lgc F G hy hhead_eq
      simpa [TseqR, TseqC, hy] using heq
    · simp [TseqR, TseqC, hy]
  · intro φ ψ hq
    have hhead_q :=
      osiiAxisPairHeadRestriction_positiveEnergyQuotient_eq_of_timePositiveQuotient_eq
        (d := d) hq
    have hhead_eq := eqOn_nonneg_of_section43PositiveEnergyQuotientMap1D_eq hhead_q
    have heq :=
      OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM_eq_of_eqOn_nonneg
        (d := d) OS lgc F G hhead_eq
    simpa [TR, TC] using heq
  · intro φ
    let χ : SchwartzMap ℝ ℂ := osiiAxisPairHeadRestrictionCLM d φ
    let Tboundary : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
      OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
        (d := d) OS lgc F G
    rcases
      exists_bound_OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_boundaryDifference_posSubtype_restrictScalars
        (d := d) OS lgc F G χ with
      ⟨C, hC_nonneg, hC_bound⟩
    refine ⟨C + ‖Tboundary χ‖, ?_⟩
    intro y
    by_cases hy : 0 < y 0
    · have hpos := hC_bound ⟨y 0, hy⟩
      calc
        ‖(TseqR y - TR) φ‖ ≤ C := by
          simpa [TseqR, TseqC, TR, TC, χ, Tboundary, hy,
            ContinuousLinearMap.sub_apply] using hpos
        _ ≤ C + ‖Tboundary χ‖ := by
          exact le_add_of_nonneg_right (norm_nonneg _)
    · calc
        ‖(TseqR y - TR) φ‖ = ‖Tboundary χ‖ := by
          simp [TseqR, TseqC, TR, TC, χ, Tboundary, hy]
        _ ≤ C + ‖Tboundary χ‖ := by
          exact le_add_of_nonneg_left hC_nonneg

/-- Section 4.3 Banach-Steinhaus payoff for the vector-side raw axis-pair CLM:
the composed positive-side family converges on every finite-time Schwartz test
to the composed spectral boundary CLM. -/
theorem osiiAxisPair_vectorCLMSide_tendsto_boundary_sideCone
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    {Cside : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ))]
    (hCside_pos : Cside ⊆ {y : Fin (d + 1) → ℝ | 0 < y 0}) :
    let TseqC : (Fin (d + 1) → ℝ) →
        SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
      fun y =>
        (if hy : 0 < y 0 then
          OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
            (d := d) OS lgc F G (y 0) hy
        else 0).comp (osiiAxisPairHeadRestrictionCLM d)
    let TseqR : (Fin (d + 1) → ℝ) →
        SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℝ] ℂ :=
      fun y => (TseqC y).restrictScalars ℝ
    let TC : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
      (OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
        (d := d) OS lgc F G).comp (osiiAxisPairHeadRestrictionCLM d)
    let TR : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℝ] ℂ :=
      TC.restrictScalars ℝ
    ∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
      Tendsto
        (fun y : Fin (d + 1) → ℝ => TseqR y φ)
        (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
        (nhds (TR φ)) := by
  classical
  intro TseqC TseqR TC TR φ
  have hTseq_apply :
      ∀ y (ψ : SchwartzMap (Fin (d + 1) → ℝ) ℂ), TseqR y ψ = TseqC y ψ := by
    intro y ψ
    rfl
  have hT_apply :
      ∀ ψ : SchwartzMap (Fin (d + 1) → ℝ) ℂ, TR ψ = TC ψ := by
    intro ψ
    rfl
  rcases
    osiiAxisPair_vectorCLMSide_descent_and_pointwise_bounded
      (d := d) OS lgc F G with
    ⟨hTseq_desc, hT_desc, hpointwise⟩
  have hkernel :=
    osiiAxisPair_vectorProductKernel_boundary_selector_sideCone
      (d := d) OS lgc F G hCside_pos
  let l : Filter (Fin (d + 1) → ℝ) :=
    𝓝[Cside] (0 : Fin (d + 1) → ℝ)
  have hl_cg : l.IsCountablyGenerated := by infer_instance
  have hl_neBot : NeBot l := by infer_instance
  letI : l.IsCountablyGenerated := hl_cg
  letI : NeBot l := hl_neBot
  exact
    section43_tendsto_timeSchwartz_real_of_productKernel_selectors_on_strictPositive_of_pointwise_bounded
      (n := d + 1) (l := l)
      (TseqC := TseqC) (TC := TC) (TseqR := TseqR) (TR := TR)
      hTseq_apply hT_apply hTseq_desc hT_desc
      (by
        intro ξ hξ
        simpa [l, TseqC, TC,
          OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM_apply]
          using hkernel ξ hξ)
      hpointwise φ

/-- The positive side-cone boundary CLM selected by Section 4.3 is the same
local analytic branch selected by the raw OS-II axis-pair time-shell packet.

This is the pointwise boundary-selector handoff used by the source-current
route: the vector boundary CLM and the raw time-shell branch are limits of the
same regularized source current along the side cone. -/
theorem osiiAxisPair_boundaryCLM_eq_timeShellBranch_sideCone
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cside : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ))]
    (hCside_pos : Cside ⊆ {y : Fin (d + 1) → ℝ | 0 < y 0}) :
    let F : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single n f hf_ord
    let G : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single r g hg_ord
    let TC : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
      (OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
        (d := d) OS lgc F G).comp (osiiAxisPairHeadRestrictionCLM d)
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ τ : Fin (d + 1) → ℝ,
        τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        τ ∈ section43TimeStrictPositiveRegion (d + 1) →
          TC (section43TimeImagAxisProductKernel τ) =
            osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
              f hf_ord g hg_ord T ξ
              (fun ν : Fin (d + 1) => (τ ν : ℂ)) := by
  classical
  intro F G TC
  rcases
    osiiAxisPair_timeShell_regularizedCLM_selector_to_branch_sideCone
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ hξ0
      hCside_pos with
    ⟨ρ, C, hρ, hC, hselector⟩
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro τ hτwin hτpos
  rcases hselector τ hτwin with ⟨htime, hbranch_raw⟩
  let TseqC : (Fin (d + 1) → ℝ) →
      SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
    fun y =>
      (if hy : 0 < y 0 then
        OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
          (d := d) OS lgc F G (y 0) hy
      else 0).comp (osiiAxisPairHeadRestrictionCLM d)
  let raw : (Fin (d + 1) → ℝ) → ℂ := fun y =>
    if hy : 0 < y 0 then
      OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
        (d := d) OS lgc F G (y 0) hy
        (section43PsiZTimeTest (τ 0) htime)
    else 0
  have hkernel :
      Tendsto
        (fun y : Fin (d + 1) → ℝ =>
          TseqC y (section43TimeImagAxisProductKernel τ))
        (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
        (nhds (TC (section43TimeImagAxisProductKernel τ))) := by
    simpa [TseqC, TC, F, G] using
      osiiAxisPair_vectorProductKernel_boundary_selector_sideCone
        (d := d) OS lgc F G hCside_pos τ hτpos
  have hsource :
      (fun y : Fin (d + 1) → ℝ =>
          TseqC y (section43TimeImagAxisProductKernel τ))
        =ᶠ[𝓝[Cside] (0 : Fin (d + 1) → ℝ)] raw := by
    filter_upwards [self_mem_nhdsWithin] with y hyC
    have hypos : 0 < y 0 := hCside_pos hyC
    have heq :=
      OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_eq_of_eqOn_nonneg
        (d := d) OS lgc F G hypos
        (osiiAxisPairHeadRestriction_timeImagAxisProductKernel_eqOn_nonneg τ hτpos)
    simpa [TseqC, raw, hypos] using heq
  have hbranch :
      Tendsto
        (fun y : Fin (d + 1) → ℝ =>
          TseqC y (section43TimeImagAxisProductKernel τ))
        (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
        (𝓝 (osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
          f hf_ord g hg_ord T ξ
          (fun ν : Fin (d + 1) => (τ ν : ℂ)))) := by
    exact (tendsto_congr' hsource).2 (by simpa [raw, F, G] using hbranch_raw)
  exact tendsto_nhds_unique hkernel hbranch

/-- The positive side-cone boundary CLM selects the concrete Schwinger
coordinate-height shell on a smaller common Lemma 5.1 window.

This combines the side-cone boundary-selector handoff with the real-edge
identity in the weighted axis-pair time-shell packet.  It is the scalar
source-current conclusion needed by the local `(A0)->(P0)` route. -/
theorem osiiAxisPair_boundaryCLM_eq_schwinger_timeShell_sideCone
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cside : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ))]
    (hCside_pos : Cside ⊆ {y : Fin (d + 1) → ℝ | 0 < y 0}) :
    let F : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single n f hf_ord
    let G : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single r g hg_ord
    let TC : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
      (OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
        (d := d) OS lgc F G).comp (osiiAxisPairHeadRestrictionCLM d)
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ τ : Fin (d + 1) → ℝ,
        τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        τ ∈ section43TimeStrictPositiveRegion (d + 1) →
          TC (section43TimeImagAxisProductKernel τ) =
            OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
              (f.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) (τ 0) g))) := by
  classical
  intro F G TC
  rcases
    osiiAxisPair_boundaryCLM_eq_timeShellBranch_sideCone
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ hξ0
      hCside_pos with
    ⟨ρb, Cb, hρb, hCb, hboundary⟩
  rcases
    osiiAxisPair_weightedTotalLogSemigroupBranch_single_timeShell_local_packet
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ hξ0 with
    ⟨ρr, Cr, hρr, hCr, _hdiff, hreal, _hselector, _hbound⟩
  refine ⟨min ρb ρr, Cb + Cr, lt_min hρb hρr,
    add_nonneg hCb hCr, ?_⟩
  intro τ hτwin hτpos
  have hτwin_b :
      τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρb := by
    intro ν
    exact lt_of_lt_of_le (hτwin ν) (min_le_left ρb ρr)
  have hτwin_r :
      τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρr := by
    intro ν
    exact lt_of_lt_of_le (hτwin ν) (min_le_right ρb ρr)
  calc
    TC (section43TimeImagAxisProductKernel τ) =
        osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
          f hf_ord g hg_ord T ξ
          (fun ν : Fin (d + 1) => (τ ν : ℂ)) := by
          exact hboundary τ hτwin_b hτpos
    _ =
        OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (τ 0) g))) := by
          exact hreal τ hτwin_r

/-- Lower-side version of the vector product-kernel selector.  The side cone
approaches the real boundary with `y 0 < 0`; the regularized one-dimensional
semigroup height is the positive scalar `-y 0`. -/
theorem osiiAxisPair_vectorProductKernel_boundary_selector_lowerSideCone
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    {Cside : Set (Fin (d + 1) → ℝ)}
    (hCside_neg : Cside ⊆ {y : Fin (d + 1) → ℝ | y 0 < 0}) :
    let TseqC : (Fin (d + 1) → ℝ) →
        SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
      fun y =>
        (if hy : y 0 < 0 then
          OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
            (d := d) OS lgc F G (-y 0) (neg_pos.mpr hy)
        else 0).comp (osiiAxisPairHeadRestrictionCLM d)
    let TC : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
      (OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
        (d := d) OS lgc F G).comp (osiiAxisPairHeadRestrictionCLM d)
    ∀ τ : Fin (d + 1) → ℝ,
      τ ∈ section43TimeStrictPositiveRegion (d + 1) →
        Tendsto
          (fun y : Fin (d + 1) → ℝ =>
            TseqC y (section43TimeImagAxisProductKernel τ))
          (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
          (nhds (TC (section43TimeImagAxisProductKernel τ))) := by
  classical
  intro TseqC TC τ hτ
  let χ : SchwartzMap ℝ ℂ := section43PsiZTimeTest (τ 0) (hτ 0)
  have hCside_pos_height :
      Cside ⊆ {y : Fin (d + 1) → ℝ | 0 < -y 0} := by
    intro y hy
    have hy0 : y 0 < 0 := hCside_neg hy
    simpa using (neg_pos.mpr hy0)
  have hcoord :
      Tendsto (fun y : Fin (d + 1) → ℝ => -y 0)
        (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
        (𝓝[Set.Ioi 0] (0 : ℝ)) := by
    have hcoord0 :
        Tendsto (fun y : Fin (d + 1) → ℝ => -y 0)
          (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
          (𝓝[Set.Ioi 0] (-(0 : Fin (d + 1) → ℝ) 0)) := by
      exact ((continuous_apply 0).neg).continuousWithinAt.tendsto_nhdsWithin
        hCside_pos_height
    simpa using hcoord0
  let rawIntegral : ℝ → ℂ := fun η =>
    ∫ x : ℝ,
      OSInnerProductTimeShiftHolomorphicValueExpandBoth
          (d := d) OS lgc F G
          (-Complex.I * ((x : ℂ) + η * Complex.I)) *
        (SchwartzMap.fourierTransformCLM ℂ χ) x
  have hraw :
      Tendsto
        rawIntegral
        (𝓝[Set.Ioi 0] (0 : ℝ))
        (nhds
          (OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
            (d := d) OS lgc F G χ)) := by
    simpa [rawIntegral, OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM_apply]
      using
        tendsto_rotated_OSInnerProductTimeShiftHolomorphicValueExpandBoth_boundaryValue_fourierTransform
          (d := d) OS lgc F G χ
  have hraw_side :
      Tendsto
        (fun y : Fin (d + 1) → ℝ =>
          if hy : y 0 < 0 then
            OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
              (d := d) OS lgc F G (-y 0) (neg_pos.mpr hy) χ
          else 0)
        (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
        (nhds
          (OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
            (d := d) OS lgc F G χ)) := by
    have hraw_comp :
        Tendsto (fun y : Fin (d + 1) → ℝ => rawIntegral (-y 0))
          (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
          (nhds
            (OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
              (d := d) OS lgc F G χ)) := by
      exact hraw.comp hcoord
    have heq :
        (fun y : Fin (d + 1) → ℝ =>
          if hy : y 0 < 0 then
            OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
              (d := d) OS lgc F G (-y 0) (neg_pos.mpr hy) χ
          else 0)
          =ᶠ[𝓝[Cside] (0 : Fin (d + 1) → ℝ)]
        fun y : Fin (d + 1) → ℝ => rawIntegral (-y 0) := by
      filter_upwards [self_mem_nhdsWithin] with y hyC
      have hyneg : y 0 < 0 := hCside_neg hyC
      have hypos : 0 < -y 0 := neg_pos.mpr hyneg
      simp [hyneg, rawIntegral,
        OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_apply]
    exact (tendsto_congr' heq).2 hraw_comp
  have hsource :
      (fun y : Fin (d + 1) → ℝ =>
        TseqC y (section43TimeImagAxisProductKernel τ))
        =ᶠ[𝓝[Cside] (0 : Fin (d + 1) → ℝ)]
      fun y : Fin (d + 1) → ℝ =>
        if hy : y 0 < 0 then
          OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
            (d := d) OS lgc F G (-y 0) (neg_pos.mpr hy) χ
        else 0 := by
    filter_upwards [self_mem_nhdsWithin] with y hyC
    have hyneg : y 0 < 0 := hCside_neg hyC
    have hypos : 0 < -y 0 := neg_pos.mpr hyneg
    have heq :=
      OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_eq_of_eqOn_nonneg
        (d := d) OS lgc F G hypos
        (osiiAxisPairHeadRestriction_timeImagAxisProductKernel_eqOn_nonneg τ hτ)
    simpa [TseqC, hyneg, hypos, χ] using heq
  have htarget :
      TC (section43TimeImagAxisProductKernel τ) =
        OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
          (d := d) OS lgc F G χ := by
    simpa [TC, χ] using
      OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM_eq_of_eqOn_nonneg
        (d := d) OS lgc F G
        (osiiAxisPairHeadRestriction_timeImagAxisProductKernel_eqOn_nonneg τ hτ)
  exact (tendsto_congr' hsource).2 (by simpa [htarget] using hraw_side)

/-- Lower-side boundary CLM selected by Section 4.3 agrees with the same local
axis-pair MZ time-shell branch.

This is the lower analogue of
`osiiAxisPair_boundaryCLM_eq_timeShellBranch_sideCone`: the lower raw selector
and the spectral boundary CLM are limits of the same regularized source
current, with positive semigroup height recovered as `-y 0`. -/
theorem osiiAxisPair_boundaryCLM_eq_timeShellBranch_lowerSideCone
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cside : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ))]
    (hCside_neg : Cside ⊆ {y : Fin (d + 1) → ℝ | y 0 < 0}) :
    let F : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single n f hf_ord
    let G : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single r g hg_ord
    let TC : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
      (OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
        (d := d) OS lgc F G).comp (osiiAxisPairHeadRestrictionCLM d)
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ τ : Fin (d + 1) → ℝ,
        τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        τ ∈ section43TimeStrictPositiveRegion (d + 1) →
          TC (section43TimeImagAxisProductKernel τ) =
            osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
              f hf_ord g hg_ord T ξ
              (fun ν : Fin (d + 1) => (τ ν : ℂ)) := by
  classical
  intro F G TC
  rcases
    osiiAxisPair_timeShell_regularizedCLM_selector_to_branch_lowerSideCone
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ hξ0
      hCside_neg with
    ⟨ρ, C, hρ, hC, hselector⟩
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro τ hτwin hτpos
  rcases hselector τ hτwin with ⟨htime, hbranch_raw⟩
  let TseqC : (Fin (d + 1) → ℝ) →
      SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
    fun y =>
      (if hy : y 0 < 0 then
        OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
          (d := d) OS lgc F G (-y 0) (neg_pos.mpr hy)
      else 0).comp (osiiAxisPairHeadRestrictionCLM d)
  let raw : (Fin (d + 1) → ℝ) → ℂ := fun y =>
    if hy : y 0 < 0 then
      OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
        (d := d) OS lgc F G (-y 0) (neg_pos.mpr hy)
        (section43PsiZTimeTest (τ 0) htime)
    else 0
  have hkernel :
      Tendsto
        (fun y : Fin (d + 1) → ℝ =>
          TseqC y (section43TimeImagAxisProductKernel τ))
        (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
        (nhds (TC (section43TimeImagAxisProductKernel τ))) := by
    simpa [TseqC, TC, F, G] using
      osiiAxisPair_vectorProductKernel_boundary_selector_lowerSideCone
        (d := d) OS lgc F G hCside_neg τ hτpos
  have hsource :
      (fun y : Fin (d + 1) → ℝ =>
          TseqC y (section43TimeImagAxisProductKernel τ))
        =ᶠ[𝓝[Cside] (0 : Fin (d + 1) → ℝ)] raw := by
    filter_upwards [self_mem_nhdsWithin] with y hyC
    have hyneg : y 0 < 0 := by simpa using hCside_neg hyC
    have heq :=
      OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_eq_of_eqOn_nonneg
        (d := d) OS lgc F G (neg_pos.mpr hyneg)
        (osiiAxisPairHeadRestriction_timeImagAxisProductKernel_eqOn_nonneg τ hτpos)
    simpa [TseqC, raw, hyneg] using heq
  have hbranch :
      Tendsto
        (fun y : Fin (d + 1) → ℝ =>
          TseqC y (section43TimeImagAxisProductKernel τ))
        (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
        (𝓝 (osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
          f hf_ord g hg_ord T ξ
          (fun ν : Fin (d + 1) => (τ ν : ℂ)))) := by
    exact (tendsto_congr' hsource).2 (by simpa [raw, F, G] using hbranch_raw)
  exact tendsto_nhds_unique hkernel hbranch

/-- The lower side-cone boundary CLM selects the concrete Schwinger
coordinate-height shell on a smaller common Lemma 5.1 window.

This is the lower-side source-current selector in the same form as the positive
theorem above, but the approach filter is `y 0 < 0` and the positive
regularization height is `-y 0`. -/
theorem osiiAxisPair_boundaryCLM_eq_schwinger_timeShell_lowerSideCone
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    {n r : ℕ}
    (f : SchwartzNPoint d n)
    (hf_ord : tsupport (f : NPointDomain d n → ℂ) ⊆
      OrderedPositiveTimeRegion d n)
    (g : SchwartzNPoint d r)
    (hg_ord : tsupport (g : NPointDomain d r → ℂ) ⊆
      OrderedPositiveTimeRegion d r)
    (hg_compact : HasCompactSupport (g : NPointDomain d r → ℂ))
    (T : ℝ) (hT : 0 < T)
    (ξ : Fin (d + 1) → ℝ) (hξ0 : 0 < ξ 0)
    {Cside : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ))]
    (hCside_neg : Cside ⊆ {y : Fin (d + 1) → ℝ | y 0 < 0}) :
    let F : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single n f hf_ord
    let G : PositiveTimeBorchersSequence d :=
      PositiveTimeBorchersSequence.single r g hg_ord
    let TC : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
      (OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
        (d := d) OS lgc F G).comp (osiiAxisPairHeadRestrictionCLM d)
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ τ : Fin (d + 1) → ℝ,
        τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρ →
        τ ∈ section43TimeStrictPositiveRegion (d + 1) →
          TC (section43TimeImagAxisProductKernel τ) =
            OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
              (f.osConjTensorProduct
                (timeShiftSchwartzNPoint (d := d) (τ 0) g))) := by
  classical
  intro F G TC
  rcases
    osiiAxisPair_boundaryCLM_eq_timeShellBranch_lowerSideCone
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ hξ0
      hCside_neg with
    ⟨ρb, Cb, hρb, hCb, hboundary⟩
  rcases
    osiiAxisPair_weightedTotalLogSemigroupBranch_single_timeShell_local_packet
      (d := d) OS lgc f hf_ord g hg_ord hg_compact T hT ξ hξ0 with
    ⟨ρr, Cr, hρr, hCr, _hdiff, hreal, _hselector, _hbound⟩
  refine ⟨min ρb ρr, Cb + Cr, lt_min hρb hρr,
    add_nonneg hCb hCr, ?_⟩
  intro τ hτwin hτpos
  have hτwin_b :
      τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρb := by
    intro ν
    exact lt_of_lt_of_le (hτwin ν) (min_le_left ρb ρr)
  have hτwin_r :
      τ ∈ osiiAxisPairTimeShellWindow (d := d) ξ ρr := by
    intro ν
    exact lt_of_lt_of_le (hτwin ν) (min_le_right ρb ρr)
  calc
    TC (section43TimeImagAxisProductKernel τ) =
        osiiAxisPairWeightedTimeShellBranch (d := d) OS lgc
          f hf_ord g hg_ord T ξ
          (fun ν : Fin (d + 1) => (τ ν : ℂ)) := by
          exact hboundary τ hτwin_b hτpos
    _ =
        OS.S (n + r) (ZeroDiagonalSchwartz.ofClassical
          (f.osConjTensorProduct
            (timeShiftSchwartzNPoint (d := d) (τ 0) g))) := by
          exact hreal τ hτwin_r

/-- Lower-side quotient descent and pointwise boundedness for the vector CLM
family.  This is the same raw one-dimensional selector as the positive side,
with positive semigroup time recovered as `-y 0` on lower cones. -/
theorem osiiAxisPair_vectorCLMSide_lower_descent_and_pointwise_bounded
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d) :
    let TseqC : (Fin (d + 1) → ℝ) →
        SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
      fun y =>
        (if hy : y 0 < 0 then
          OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
            (d := d) OS lgc F G (-y 0) (neg_pos.mpr hy)
        else 0).comp (osiiAxisPairHeadRestrictionCLM d)
    let TseqR : (Fin (d + 1) → ℝ) →
        SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℝ] ℂ :=
      fun y => (TseqC y).restrictScalars ℝ
    let TC : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
      (OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
        (d := d) OS lgc F G).comp (osiiAxisPairHeadRestrictionCLM d)
    let TR : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℝ] ℂ :=
      TC.restrictScalars ℝ
    (∀ y (φ ψ : SchwartzMap (Fin (d + 1) → ℝ) ℂ),
      section43TimePositiveQuotientMap (d + 1) φ =
        section43TimePositiveQuotientMap (d + 1) ψ →
        TseqR y φ = TseqR y ψ) ∧
    (∀ φ ψ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
      section43TimePositiveQuotientMap (d + 1) φ =
        section43TimePositiveQuotientMap (d + 1) ψ →
        TR φ = TR ψ) ∧
    (∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ, ∃ C : ℝ,
      ∀ y : Fin (d + 1) → ℝ, ‖(TseqR y - TR) φ‖ ≤ C) := by
  classical
  intro TseqC TseqR TC TR
  refine ⟨?_, ?_, ?_⟩
  · intro y φ ψ hq
    have hhead_q :=
      osiiAxisPairHeadRestriction_positiveEnergyQuotient_eq_of_timePositiveQuotient_eq
        (d := d) hq
    have hhead_eq := eqOn_nonneg_of_section43PositiveEnergyQuotientMap1D_eq hhead_q
    by_cases hy : y 0 < 0
    · have heq :=
        OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_eq_of_eqOn_nonneg
          (d := d) OS lgc F G (neg_pos.mpr hy) hhead_eq
      simpa [TseqR, TseqC, hy] using heq
    · simp [TseqR, TseqC, hy]
  · intro φ ψ hq
    have hhead_q :=
      osiiAxisPairHeadRestriction_positiveEnergyQuotient_eq_of_timePositiveQuotient_eq
        (d := d) hq
    have hhead_eq := eqOn_nonneg_of_section43PositiveEnergyQuotientMap1D_eq hhead_q
    have heq :=
      OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM_eq_of_eqOn_nonneg
        (d := d) OS lgc F G hhead_eq
    simpa [TR, TC] using heq
  · intro φ
    let χ : SchwartzMap ℝ ℂ := osiiAxisPairHeadRestrictionCLM d φ
    let Tboundary : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
      OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
        (d := d) OS lgc F G
    rcases
      exists_bound_OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM_boundaryDifference_posSubtype_restrictScalars
        (d := d) OS lgc F G χ with
      ⟨C, hC_nonneg, hC_bound⟩
    refine ⟨C + ‖Tboundary χ‖, ?_⟩
    intro y
    by_cases hy : y 0 < 0
    · have hypos : 0 < -y 0 := neg_pos.mpr hy
      have hpos := hC_bound ⟨-y 0, hypos⟩
      calc
        ‖(TseqR y - TR) φ‖ ≤ C := by
          simpa [TseqR, TseqC, TR, TC, χ, Tboundary, hy, hypos,
            ContinuousLinearMap.sub_apply] using hpos
        _ ≤ C + ‖Tboundary χ‖ := by
          exact le_add_of_nonneg_right (norm_nonneg _)
    · calc
        ‖(TseqR y - TR) φ‖ = ‖Tboundary χ‖ := by
          simp [TseqR, TseqC, TR, TC, χ, Tboundary, hy]
        _ ≤ C + ‖Tboundary χ‖ := by
          exact le_add_of_nonneg_left hC_nonneg

/-- Section 4.3 Banach-Steinhaus payoff for lower-side vector CLM selectors.
It is the local-EOW lower-boundary selector needed when the chart side uses
negative imaginary time but the OS semigroup still takes positive time. -/
theorem osiiAxisPair_vectorCLMSide_tendsto_boundary_lowerSideCone
    {d : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS)
    (F G : PositiveTimeBorchersSequence d)
    {Cside : Set (Fin (d + 1) → ℝ)}
    [NeBot (𝓝[Cside] (0 : Fin (d + 1) → ℝ))]
    (hCside_neg : Cside ⊆ {y : Fin (d + 1) → ℝ | y 0 < 0}) :
    let TseqC : (Fin (d + 1) → ℝ) →
        SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
      fun y =>
        (if hy : y 0 < 0 then
          OSInnerProductTimeShiftHolomorphicValueExpandBothRegularizedCLM
            (d := d) OS lgc F G (-y 0) (neg_pos.mpr hy)
        else 0).comp (osiiAxisPairHeadRestrictionCLM d)
    let TseqR : (Fin (d + 1) → ℝ) →
        SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℝ] ℂ :=
      fun y => (TseqC y).restrictScalars ℝ
    let TC : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ :=
      (OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM
        (d := d) OS lgc F G).comp (osiiAxisPairHeadRestrictionCLM d)
    let TR : SchwartzMap (Fin (d + 1) → ℝ) ℂ →L[ℝ] ℂ :=
      TC.restrictScalars ℝ
    ∀ φ : SchwartzMap (Fin (d + 1) → ℝ) ℂ,
      Tendsto
        (fun y : Fin (d + 1) → ℝ => TseqR y φ)
        (𝓝[Cside] (0 : Fin (d + 1) → ℝ))
        (nhds (TR φ)) := by
  classical
  intro TseqC TseqR TC TR φ
  have hTseq_apply :
      ∀ y (ψ : SchwartzMap (Fin (d + 1) → ℝ) ℂ), TseqR y ψ = TseqC y ψ := by
    intro y ψ
    rfl
  have hT_apply :
      ∀ ψ : SchwartzMap (Fin (d + 1) → ℝ) ℂ, TR ψ = TC ψ := by
    intro ψ
    rfl
  rcases
    osiiAxisPair_vectorCLMSide_lower_descent_and_pointwise_bounded
      (d := d) OS lgc F G with
    ⟨hTseq_desc, hT_desc, hpointwise⟩
  have hkernel :=
    osiiAxisPair_vectorProductKernel_boundary_selector_lowerSideCone
      (d := d) OS lgc F G hCside_neg
  let l : Filter (Fin (d + 1) → ℝ) :=
    𝓝[Cside] (0 : Fin (d + 1) → ℝ)
  have hl_cg : l.IsCountablyGenerated := by infer_instance
  have hl_neBot : NeBot l := by infer_instance
  letI : l.IsCountablyGenerated := hl_cg
  letI : NeBot l := hl_neBot
  exact
    section43_tendsto_timeSchwartz_real_of_productKernel_selectors_on_strictPositive_of_pointwise_bounded
      (n := d + 1) (l := l)
      (TseqC := TseqC) (TC := TC) (TseqR := TseqR) (TR := TR)
      hTseq_apply hT_apply hTseq_desc hT_desc
      (by
        intro ξ hξ
        simpa [l, TseqC, TC,
          OSInnerProductTimeShiftHolomorphicValueExpandBothBoundaryValueCLM_apply]
          using hkernel ξ hξ)
      hpointwise φ

end OSReconstruction
