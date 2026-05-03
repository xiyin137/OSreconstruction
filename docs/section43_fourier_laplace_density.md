# Section 4.3 Fourier-Laplace Density Packet

This note is the focused implementation plan for the remaining theorem-3
positivity blocker on the OS route.

Active production target:

```lean
theorem dense_section43FourierLaplaceTransformComponentMap_preimage
    (d n : ℕ) [NeZero d] :
    Dense
      ((section43PositiveEnergyQuotientMap (d := d) n) ⁻¹'
        Set.range (section43FourierLaplaceTransformComponentMap d n))
```

Once this theorem is proved, the compiled theorem
`bvt_W_positive_of_component_dense_preimage` in
`Section43FourierLaplaceClosure.lean` gives theorem-3 positivity for arbitrary
`BorchersSequence d`.

## Non-Goals

Do not use these routes:

1. `os1TransportComponent` density.  That map quotients the Euclidean source
   itself; it is not the OS I `(4.19)-(4.20)` Fourier-Laplace transform.
2. Support-restricted dense range into `S_+`.  The correct target is the
   positive-energy quotient, or equivalently the ambient-Schwartz preimage of a
   quotient range.
3. Wightman, OS Hilbert-space, semigroup, or Borchers-sequence hypotheses.
   This packet is pure Schwartz/Fourier-Laplace analysis.
4. Zero-kernel statements unless a later theorem consumes injectivity.  The
   positivity closure needs dense range only.

## Existing Compiled Inputs

These production declarations already exist and should be reused:

```lean
section43PositiveEnergyRegion
section43PositiveEnergyVanishingSubmodule
Section43PositiveEnergyComponent
section43PositiveEnergyQuotientMap
section43PositiveEnergyQuotientMap_eq_of_eqOn_region
eqOn_region_of_section43PositiveEnergyQuotientMap_eq
section43DiffCoordRealCLE
section43DiffPullbackCLM
section43FourierLaplaceIntegral
section43FourierLaplaceIntegral_eq_time_spatial_integral
exists_orderedPositiveTimeRegion_margin_of_compact_tsupport_subset
exists_section43FourierLaplaceRepresentative_of_compact_orderedSupport
section43FourierLaplaceTransformComponent
section43FourierLaplaceTransformComponent_has_representative
Section43CompactOrderedSource
section43FourierLaplaceTransformComponentMap
denseRange_section43FourierLaplaceTransformComponentMap_of_dense_preimage
bvt_W_positive_of_component_dense_preimage
```

Production status, 2026-04-17: this density file now exists and the foundation,
raw one-sided Laplace calculus, cutoff-Schwartz representative, and
one-variable Paley-Wiener uniqueness packets are compiled:

```lean
Section43CompactPositiveTimeSource1D
section43OneSidedLaplaceRepresentative1D
section43OneSidedLaplaceRaw
Section43CompactPositiveTimeSource1D.tsupport_subset_Ici
section43OneSidedLaplaceRaw_eq_complexLaplaceTransform
section43OneSidedLaplaceRaw_integrable_of_nonneg
section43OneSidedLaplaceRaw_eq_fourierInvPairingCanonicalExtension_of_pos
exists_positive_margin_of_compact_tsupport_subset_Ioi
exists_Icc_bounds_of_compact_tsupport_subset_Ici
exists_positive_Icc_bounds_of_compactPositiveTimeSource
section43SmoothCutoff_complex_iteratedFDeriv_support_subset_Ici_neg_one
section43OneSidedLaplaceCutoffFun
section43OneSidedLaplaceCutoffFun_eq_raw_of_nonneg
section43OneSidedLaplaceRawDerivCandidate
section43OneSidedLaplaceRawDerivCandidate_integrable
section43OneSidedLaplaceRawDerivKernel_hasDerivAt
section43OneSidedLaplaceRawDerivCandidate_hasDerivAt
section43OneSidedLaplaceRaw_iteratedDeriv_formula
section43OneSidedLaplaceRaw_contDiff
section43OneSidedLaplaceRaw_iteratedFDeriv_formula
section43OneSidedLaplaceRawDerivCandidate_norm_le_of_re_bound
section43OneSidedLaplaceRawDerivCandidate_norm_le_strip
section43OneSidedLaplaceRawDerivCandidate_norm_le_nonneg
section43OneSidedLaplaceRaw_rapid_on_Ici_neg_one
section43OneSidedLaplaceSchwartzRepresentative1D
section43OneSidedLaplaceSchwartzRepresentative1D_apply
exists_section43OneSidedLaplaceRepresentative1D
section43OneSidedLaplaceCompactTransform1D
section43OneSidedLaplaceCompactTransform1D_choose_spec
section43OneSidedLaplaceCompactTransform1D_eq_cutoff_quotient
section43FourierInvCLM1D
section43FourierInvCLM1D_apply
section43PositiveEnergy1D_to_oneSidedFourierFunctional
section43PositiveEnergy1D_to_oneSidedFourierFunctional_support
fourierPairingDescendsToSection43PositiveEnergy1D_to_oneSided
section43OneSidedAnnihilatorFL
section43OneSidedAnnihilatorFL_eq_fourierLaplaceExt_to_oneSided
section43OneSidedAnnihilatorFLOnImag
section43ImagAxisPsiKernel
section43ImagAxisPsiKernel_of_pos
section43ImagAxisPsiKernel_of_not_pos
section43ImagAxisPsiKernel_apply_of_not_pos
section43ImagAxisPsiKernel_apply_of_pos_of_nonneg
section43ImagAxisPsiKernel_apply_mul_source_of_nonneg
section43ImagAxisPsiKernel_apply_mul_source
Section43CompactPositiveTimeSource1D.pos_of_ne_zero
Section43CompactPositiveTimeSource1D.eq_zero_of_not_pos
section43OneSidedLaplaceCutoffFun_eq_integral_imagAxisPsiKernel
section43OneSidedLaplaceRaw_eq_integral_imagAxisPsiKernel_of_nonneg
section43OneSidedLaplaceSchwartzRepresentative1D_eq_integral_imagAxisPsiKernel_of_nonneg
section43OneSidedLaplaceSchwartzRepresentative1D_eq_integral_imagAxisPsiKernel
section43OneSidedLaplaceSchwartzRepresentative1D_iteratedDeriv_formula
section43ImagAxisPsiKernel_iteratedDeriv_mul_source
section43OneSidedLaplaceSchwartzRepresentative1D_iteratedDeriv_eq_integral_kernel_iteratedDeriv
section43PolyWeight
section43PolyWeight_hasTemperateGrowth
section43IteratedDerivCLM
section43IteratedDerivCLM_apply
section43WeightedDerivToBCFCLM
section43WeightedDerivToBCFCLM_apply
section43_abs_pow_le_polyWeight
section43ProbeCLM
section43SchwartzSeminorm_le_probe_component_norm
section43SchwartzSeminorm_le_probe_norm
section43SchwartzFunctional_bound_by_probeNorm
section43_exists_probe_factorization
section43WeightedDerivToBCFCLM_representative_eq_integral_kernel_apply
section43OneSidedAnnihilatorFLOnImag_of_pos
section43OneSidedAnnihilatorFLOnImag_of_not_pos
section43OneSidedAnnihilatorFLOnImag_eq_apply_kernel
continuousOn_section43OneSidedAnnihilatorFLOnImag_Ioi
section43PositiveEnergy1D_ext_of_FL_zero
```

The remaining one-variable blocker is no longer Paley-Wiener uniqueness.  It is
the compact-source annihilator bridge:

```lean
section43OneSidedAnnihilatorFL_integral_zero_of_annihilates_laplace
section43OneSidedAnnihilatorFLOnImag_eq_zero_of_annihilates_laplace
section43OneSidedAnnihilatorFL_eq_zero_of_annihilates_laplace
section43OneSidedLaplaceCompactTransform1D_dual_annihilator
dense_section43OneSidedLaplaceCompactTransform1D_preimage
```

The compiled bridge
`section43OneSidedLaplaceRaw_eq_fourierInvPairingCanonicalExtension_of_pos`
identifies the raw compact Laplace integral with the already-proved canonical
one-variable Paley-Wiener extension, including the repository's built-in
`2π` scaling.  The compiled cutoff candidate is
`section43OneSidedLaplaceCutoffFun g σ =
(SCV.smoothCutoff σ : ℂ) * section43OneSidedLaplaceRaw g σ`; it already agrees
with the raw Laplace transform on `Set.Ici 0`.  The compiled support geometry
is:

```lean
theorem exists_positive_Icc_bounds_of_compactPositiveTimeSource
    (g : Section43CompactPositiveTimeSource1D) :
    ∃ δ R, 0 < δ ∧ δ ≤ R ∧
      tsupport (g.f : ℝ → ℂ) ⊆ Set.Icc δ R
```

## Implementation File

The small density file is:

```lean
OSReconstruction/Wightman/Reconstruction/WickRotation/Section43FourierLaplaceDensity.lean
```

Current imports:

```lean
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43OneVariableSlice
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceCompactDifferentiation
```

This keeps the density file below `OSToWightmanPositivity.lean` while reusing
the already-compiled general cutoff-times-rapid-to-Schwartz theorem from
`Section43FourierLaplaceCompactDifferentiation.lean`.

## Layer 1: One-Variable OS I Lemma 8.2

Definitions:

```lean
structure Section43CompactPositiveTimeSource1D where
  f : SchwartzMap ℝ ℂ
  positive :
    tsupport (f : ℝ → ℂ) ⊆ Set.Ioi (0 : ℝ)
  compact : HasCompactSupport (f : ℝ → ℂ)

def section43OneSidedLaplaceRepresentative1D
    (g : Section43CompactPositiveTimeSource1D)
    (Φ : SchwartzMap ℝ ℂ) : Prop :=
  ∀ σ : ℝ, 0 ≤ σ →
    Φ σ =
      ∫ t : ℝ,
        Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t

theorem exists_section43OneSidedLaplaceRepresentative1D
    (g : Section43CompactPositiveTimeSource1D) :
    ∃ Φ : SchwartzMap ℝ ℂ,
      section43OneSidedLaplaceRepresentative1D g Φ

noncomputable def section43OneSidedLaplaceCompactTransform1D :
    Section43CompactPositiveTimeSource1D → Section43PositiveEnergy1D :=
  fun g =>
    section43PositiveEnergyQuotientMap1D
      (Classical.choose
        (exists_section43OneSidedLaplaceRepresentative1D g))
```

Source support is strict, `Set.Ioi 0`; target equality is closed,
`Set.Ici 0`.  This mirrors the production situation: compact support inside
`OrderedPositiveTimeRegion` is separated from the time walls, while the
positive-energy quotient records values on the closed half-space.

Representative existence proof:

1. From compact support in `Set.Ioi 0`, prove a margin theorem:

```lean
theorem exists_positive_margin_of_compact_tsupport_subset_Ioi
    (g : SchwartzMap ℝ ℂ)
    (hg_pos : tsupport (g : ℝ → ℂ) ⊆ Set.Ioi (0 : ℝ))
    (hg_compact : HasCompactSupport (g : ℝ → ℂ)) :
    ∃ δ > 0, tsupport (g : ℝ → ℂ) ⊆ Set.Ici δ
```

Use the same compact-minimum argument as
`exists_orderedPositiveTimeRegion_margin_of_compact_tsupport_subset`.

2. Define the raw Laplace function on the closed half-line:

```lean
noncomputable def section43OneSidedLaplaceRaw
    (g : Section43CompactPositiveTimeSource1D) (σ : ℝ) : ℂ :=
  ∫ t : ℝ, Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t
```

3. Prove rapid decay of all derivatives on `σ ≥ 0` by differentiating under the
   integral and using the positive margin:

```lean
theorem section43OneSidedLaplaceRaw_deriv_formula
    (g : Section43CompactPositiveTimeSource1D) (k : ℕ)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    iteratedDeriv k (section43OneSidedLaplaceRaw g) σ =
      ∫ t : ℝ,
        (-t : ℂ) ^ k *
          Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t

theorem section43OneSidedLaplaceRaw_rapid_on_Ici
    (g : Section43CompactPositiveTimeSource1D) :
    ∀ a b : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ σ : ℝ, 0 ≤ σ →
        (1 + ‖σ‖) ^ a *
          ‖iteratedDeriv b (section43OneSidedLaplaceRaw g) σ‖ ≤ C
```

4. Multiply by the compiled cutoff candidate

```lean
section43OneSidedLaplaceCutoffFun g σ =
  (SCV.smoothCutoff σ : ℂ) * section43OneSidedLaplaceRaw g σ
```

It is already compiled that this candidate agrees with the raw Laplace
transform on `Set.Ici 0`:

```lean
theorem section43OneSidedLaplaceCutoffFun_eq_raw_of_nonneg
    (g : Section43CompactPositiveTimeSource1D)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    section43OneSidedLaplaceCutoffFun g σ =
      section43OneSidedLaplaceRaw g σ
```

To package it as a `SchwartzMap`, reuse
`schwartzMap_of_temperate_mul_rapid_on_derivSupport` from
`Section43FourierLaplaceCompactDifferentiation.lean` with
`χ := fun σ => (SCV.smoothCutoff σ : ℂ)`,
`F := section43OneSidedLaplaceRaw g`, and `S := Set.Ici (-1 : ℝ)`.  The cutoff
side is compiled:

```lean
theorem section43SmoothCutoff_complex_iteratedFDeriv_support_subset_Ici_neg_one :
    ∀ r : ℕ, ∀ σ : ℝ,
      iteratedFDeriv ℝ r (fun σ : ℝ => (SCV.smoothCutoff σ : ℂ)) σ ≠ 0 →
        σ ∈ Set.Ici (-1 : ℝ)
```

The only missing representative-existence input is therefore the raw-Laplace
smoothness and rapid-decay package on `Set.Ici (-1)`.  The next exact theorem
targets should be:

```lean
theorem section43OneSidedLaplaceRaw_contDiff
    (g : Section43CompactPositiveTimeSource1D) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (section43OneSidedLaplaceRaw g)

theorem section43OneSidedLaplaceRaw_iteratedFDeriv_formula
    (g : Section43CompactPositiveTimeSource1D) (r : ℕ) (σ : ℝ) :
    iteratedFDeriv ℝ r (section43OneSidedLaplaceRaw g) σ =
      (ContinuousMultilinearMap.mkPiAlgebraFin ℝ r ℝ).smulRight
        (∫ t : ℝ,
          (-t : ℂ) ^ r *
            Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t)

theorem section43OneSidedLaplaceRaw_rapid_on_Ici_neg_one
    (g : Section43CompactPositiveTimeSource1D) :
    ∀ r s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ σ ∈ Set.Ici (-1 : ℝ),
        (1 + ‖σ‖) ^ s *
          ‖iteratedFDeriv ℝ r (section43OneSidedLaplaceRaw g) σ‖ ≤ C
```

Lean-ready raw-Laplace calculus packet:

Production status, 2026-04-17: this packet is compiled through the rapid
estimate and cutoff-Schwartz representative construction in
`Section43FourierLaplaceDensity.lean`.  The next theorem group is the
annihilator bridge from compact one-sided Laplace sources to vanishing of
`section43OneSidedAnnihilatorFL`.

1. Add the genuine derivative-candidate integral, not as a wrapper but as the
   object that appears after differentiating under the integral:

```lean
noncomputable def section43OneSidedLaplaceRawDerivCandidate
    (g : Section43CompactPositiveTimeSource1D) (r : ℕ) (σ : ℝ) : ℂ :=
  ∫ t : ℝ,
    (-t : ℂ) ^ r *
      Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t
```

Then `section43OneSidedLaplaceRawDerivCandidate g 0 = section43OneSidedLaplaceRaw g`.

2. Prove integrability of every derivative kernel for every real `σ`:

```lean
theorem section43OneSidedLaplaceRawDerivCandidate_integrable
    (g : Section43CompactPositiveTimeSource1D) (r : ℕ) (σ : ℝ) :
    Integrable
      (fun t : ℝ =>
        (-t : ℂ) ^ r *
          Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t)
```

Proof transcript:

- The integrand is continuous as a product of the polynomial factor, the
  complex exponential factor, and `g.f.continuous`.
- Its compact support follows from `g.compact.mul_left`, because the first two
  factors multiply `g.f` on the left.
- Apply `Continuous.integrable_of_hasCompactSupport`.

This lemma is intentionally stronger than the existing nonnegative-real-part
integrability theorem: compact source support makes the kernel integrable for
all real `σ`, including the transition strip `-1 ≤ σ ≤ 0` where the cutoff has
nonzero derivatives.

3. Prove the pointwise kernel derivative:

```lean
theorem section43OneSidedLaplaceRawDerivKernel_hasDerivAt
    (g : Section43CompactPositiveTimeSource1D) (r : ℕ) (t σ : ℝ) :
    HasDerivAt
      (fun σ : ℝ =>
        (-t : ℂ) ^ r *
          Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t)
      ((-t : ℂ) ^ (r + 1) *
        Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t)
      σ
```

Proof transcript:

- First prove

```lean
HasDerivAt
  (fun σ : ℝ => Complex.exp (-(t : ℂ) * (σ : ℂ)))
  (-(t : ℂ) * Complex.exp (-(t : ℂ) * (σ : ℂ))) σ
```

  by differentiating `fun σ : ℝ => -((t : ℂ) * (σ : ℂ))`: prove the linear
  derivative for `fun σ => (t : ℂ) * (σ : ℂ)` using
  `(Complex.ofRealCLM.hasDerivAt (x := σ))`, negate it, then apply `.cexp`.
- Multiply by the constants `(-t : ℂ)^r` and `g.f t`.
- Finish by `ring` to identify
  `(-t)^r * (-(t))` with `(-t)^(r+1)`.

4. Prove the local domination needed by
   `hasDerivAt_integral_of_dominated_loc_of_deriv_le`.

For fixed `σ₀`, choose support bounds
`0 < δ`, `δ ≤ R`, and `tsupport g.f ⊆ Set.Icc δ R`.  Let

```lean
Mσ := |σ₀| + 1
B r σ₀ :=
  (max |δ| |R|) ^ r * Real.exp (R * Mσ)
```

and use the real bound

```lean
bound t := B (r + 1) σ₀ * ‖g.f t‖
```

Then for all `σ ∈ Metric.closedBall σ₀ 1`,

```lean
‖(-t : ℂ) ^ (r + 1) *
    Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t‖ ≤ bound t.
```

Proof transcript:

- If `g.f t = 0`, both sides reduce to `0 ≤ 0`.
- If `g.f t ≠ 0`, then `t ∈ tsupport g.f`, hence `δ ≤ t ≤ R`.
- Thus `0 ≤ t`, `|t| ≤ max |δ| |R|`, and
  `‖(-t : ℂ)^(r+1)‖ ≤ (max |δ| |R|)^(r+1)`.
- From `σ ∈ closedBall σ₀ 1`, get `|σ| ≤ |σ₀| + 1`.
- Since `0 ≤ t ≤ R`,
  `(-(t : ℂ) * (σ : ℂ)).re = -(t * σ) ≤ R * (|σ₀| + 1)`.
- Therefore
  `‖Complex.exp (-(t : ℂ) * (σ : ℂ))‖ ≤ Real.exp (R * (|σ₀| + 1))`
  by `Complex.norm_exp` and `Real.exp_le_exp`.
- `bound` is integrable because it is a constant multiple of
  `g.f.integrable.norm`.

5. Apply

```lean
hasDerivAt_integral_of_dominated_loc_of_deriv_le
```

with

```lean
F σ t :=
  (-t : ℂ)^r * Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t
F' σ t :=
  (-t : ℂ)^(r+1) * Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t
s := Metric.closedBall σ₀ 1
bound := fun t => B (r + 1) σ₀ * ‖g.f t‖
```

This gives:

```lean
theorem section43OneSidedLaplaceRawDerivCandidate_hasDerivAt
    (g : Section43CompactPositiveTimeSource1D) (r : ℕ) (σ : ℝ) :
    HasDerivAt
      (section43OneSidedLaplaceRawDerivCandidate g r)
      (section43OneSidedLaplaceRawDerivCandidate g (r + 1) σ)
      σ
```

6. Induct on `r` to identify ordinary iterated derivatives:

```lean
theorem section43OneSidedLaplaceRaw_iteratedDeriv_formula
    (g : Section43CompactPositiveTimeSource1D) (r : ℕ) (σ : ℝ) :
    iteratedDeriv r (section43OneSidedLaplaceRaw g) σ =
      section43OneSidedLaplaceRawDerivCandidate g r σ
```

Use `iteratedDeriv_succ` and
`section43OneSidedLaplaceRawDerivCandidate_hasDerivAt.deriv`.

7. Smoothness follows by the same local pattern already used in
   `section43ContDiff_partialFourierSpatial_timeSlice`:

```lean
apply contDiff_of_differentiable_iteratedDeriv
intro r hr
rw [section43OneSidedLaplaceRaw_iteratedDeriv_formula]
exact fun σ =>
  (section43OneSidedLaplaceRawDerivCandidate_hasDerivAt g r σ).differentiableAt
```

8. Convert to the Fréchet formula only after the ordinary derivative formula is
   proved.  Use
   `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` to prove equality by
   extensionality against `m : Fin r → ℝ`:

```lean
theorem section43OneSidedLaplaceRaw_iteratedFDeriv_formula
    (g : Section43CompactPositiveTimeSource1D) (r : ℕ) (σ : ℝ) :
    iteratedFDeriv ℝ r (section43OneSidedLaplaceRaw g) σ =
      (ContinuousMultilinearMap.mkPiAlgebraFin ℝ r ℝ).smulRight
        (section43OneSidedLaplaceRawDerivCandidate g r σ)
```

Both sides evaluate to `(∏ i, m i) •
section43OneSidedLaplaceRawDerivCandidate g r σ`.

For the rapid theorem, use
`exists_positive_Icc_bounds_of_compactPositiveTimeSource` to choose
`0 < δ ≤ R` and `tsupport g.f ⊆ Set.Icc δ R`.  Split `σ ∈ Set.Ici (-1)` into
`σ ≤ 0` and `0 ≤ σ`.  On `[-1,0]`, bound the exponential by `Real.exp R` and
use compact support.  On `[0,∞)`, use
`Real.exp (-(δ * σ))` and the standard fact that exponential decay dominates
all polynomial powers.

Lean-ready rapid-bound transcript:

1. Normalize the Fréchet derivative norm via the compiled formula:

```lean
rw [section43OneSidedLaplaceRaw_iteratedFDeriv_formula]
rw [ContinuousMultilinearMap.norm_smulRight,
  ContinuousMultilinearMap.norm_mkPiAlgebraFin]
```

This reduces the target to bounding
`‖section43OneSidedLaplaceRawDerivCandidate g r σ‖`.

2. Let

```lean
A r := (R ^ r) * ∫ t : ℝ, ‖g.f t‖
```

or, if Lean prefers avoiding positivity of the integral inline, use

```lean
A r := (max |δ| |R|) ^ r * ∫ t : ℝ, ‖g.f t‖
```

The integral is finite because `g.f.integrable.norm`.

3. Prove the candidate integral bound by
`norm_integral_le_integral_norm` and support splitting:

```lean
‖section43OneSidedLaplaceRawDerivCandidate g r σ‖
  ≤ A r * Real.exp (R)
```

for `-1 ≤ σ ≤ 0`, and

```lean
‖section43OneSidedLaplaceRawDerivCandidate g r σ‖
  ≤ A r * Real.exp (-(δ * σ))
```

for `0 ≤ σ`.

Proof details:

- If `g.f t = 0`, the integrand norm is zero.
- If `g.f t ≠ 0`, then `δ ≤ t ≤ R`.
- For `-1 ≤ σ ≤ 0`, use
  `(-(t : ℂ) * (σ : ℂ)).re = -(t * σ) ≤ R` because
  `t ≤ R` and `-σ ≤ 1`.
- For `0 ≤ σ`, use
  `-(t * σ) ≤ -(δ * σ)` because `δ ≤ t` and `0 ≤ σ`.

4. The compact strip contribution is bounded by

```lean
Cstrip r s := 2 ^ s * A r * Real.exp R
```

because `σ ∈ [-1,0]` implies `‖σ‖ ≤ 1`, hence
`(1 + ‖σ‖)^s ≤ 2^s`.

5. The positive half-line contribution is bounded by applying
`SCV.pow_mul_exp_neg_le_const hδ_pos s` to `ξ := 1 + σ`:

```lean
(1 + ‖σ‖)^s * Real.exp (-(δ * σ))
  = Real.exp δ * ((1 + σ)^s * Real.exp (-(δ * (1 + σ))))
  ≤ Real.exp δ * Cexp
```

for `0 ≤ σ`.  This avoids a separate binomial estimate for `(1 + σ)^s`.

6. Take

```lean
C := max 0 (Cstrip r s + A r * Real.exp δ * Cexp)
```

or the sum of nonnegative factors if Lean already has the individual
nonnegativity facts available.  Then dispatch the two cases `σ ≤ 0` and
`0 ≤ σ`.

Dense range theorem:

```lean
theorem dense_section43OneSidedLaplaceCompactTransform1D_preimage :
    Dense
      (section43PositiveEnergyQuotientMap1D ⁻¹'
        Set.range section43OneSidedLaplaceCompactTransform1D)
```

Preferred proof is the OS I Lemma-8.2 dual-annihilator proof.

Important theorem-shape correction: the dual-annihilator proof cannot be
applied to an arbitrary non-linear `Set.range`.  It proves density of a linear
subspace.  Therefore the Lean route must first expose the compact strict-positive
sources as a complex vector space and prove that the compact one-sided Laplace
transform is linear.

Add the source operations:

```lean
namespace Section43CompactPositiveTimeSource1D

instance : Zero Section43CompactPositiveTimeSource1D
instance : Add Section43CompactPositiveTimeSource1D
instance : SMul ℕ Section43CompactPositiveTimeSource1D
instance : AddCommMonoid Section43CompactPositiveTimeSource1D
instance : SMul ℂ Section43CompactPositiveTimeSource1D
instance : Module ℂ Section43CompactPositiveTimeSource1D

end Section43CompactPositiveTimeSource1D
```

The proof obligations are only support stability:

- zero source: `HasCompactSupport.zero` and empty support;
- addition: `tsupport_add` plus union into `Set.Ioi 0`, and
  `HasCompactSupport.add`;
- natural scalar multiplication: use `(n : ℂ) • g.f`, with
  `Nat.cast_smul_eq_nsmul` for the additive monoid law;
- scalar multiplication: `tsupport_smul_subset_right` and
  `HasCompactSupport.smul_left`.

Then prove linearity of the quotient-valued compact transform:

```lean
theorem section43OneSidedLaplaceCompactTransform1D_map_add
    (g h : Section43CompactPositiveTimeSource1D) :
    section43OneSidedLaplaceCompactTransform1D (g + h) =
      section43OneSidedLaplaceCompactTransform1D g +
        section43OneSidedLaplaceCompactTransform1D h

theorem section43OneSidedLaplaceCompactTransform1D_map_smul
    (c : ℂ) (g : Section43CompactPositiveTimeSource1D) :
    section43OneSidedLaplaceCompactTransform1D (c • g) =
      c • section43OneSidedLaplaceCompactTransform1D g

noncomputable def section43OneSidedLaplaceCompactTransform1DLinearMap :
    Section43CompactPositiveTimeSource1D →ₗ[ℂ] Section43PositiveEnergy1D
```

Proof transcript for `map_add` and `map_smul`:

- Rewrite each transform with
  `section43OneSidedLaplaceCompactTransform1D_eq_cutoff_quotient`.
- Reduce quotient equality with
  `section43PositiveEnergyQuotientMap1D_eq_of_eqOn_nonneg`.
- On `σ ≥ 0`, rewrite the explicit Schwartz representative with
  `section43OneSidedLaplaceCutoffFun_eq_raw_of_nonneg`.
- Use the raw Laplace integral definition, `integral_add` with
  `section43OneSidedLaplaceRaw_integrable_of_nonneg`, and `integral_const_mul`
  for scalar multiplication.

Production status, 2026-04-17: the source module structure, transform
linearity, and linear-map packaging are compiled in
`Section43FourierLaplaceFiniteProbe.lean`.

The density theorem is best proved directly in the ambient Schwartz preimage,
not first inside the quotient.  The quotient does not currently expose a handy
`LocallyConvexSpace ℝ Section43PositiveEnergy1D` instance, and no such
infrastructure is needed for the target theorem.

Use:

```lean
let L := section43OneSidedLaplaceCompactTransform1DLinearMap
let Mq : Submodule ℂ Section43PositiveEnergy1D := LinearMap.range L
let q := section43PositiveEnergyQuotientMap1D
let S : Submodule ℂ (SchwartzMap ℝ ℂ) := Mq.comap q.toLinearMap
```

Proof transcript:

1. Rewrite the target set as `(S : Set (SchwartzMap ℝ ℂ))`.
2. It suffices to show `S.topologicalClosure = ⊤`, via
   `Submodule.dense_iff_topologicalClosure_eq_top`.
3. If `S.topologicalClosure ≠ ⊤`, choose
   `x : SchwartzMap ℝ ℂ` outside the closure.
4. Apply the real locally-convex Hahn-Banach theorem
   `geometric_hahn_banach_closed_point` in the ambient Schwartz space to
   `S.topologicalClosure`.  The convexity proof uses the complex submodule
   operations with real coefficients cast into `ℂ`.
5. The separation functional is real-linear:

```lean
f : SchwartzMap ℝ ℂ →L[ℝ] ℝ
```

   The usual scaling argument shows `f` vanishes on `S.topologicalClosure`.
6. Extend `f` to a complex-linear functional on ambient Schwartz space:

```lean
let F : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
  StrongDual.extendRCLike (𝕜 := ℂ) f
```

   Since `S.topologicalClosure` is a complex submodule, both `f y` and
   `f (I • y)` vanish on the closure, hence `F` vanishes there.
7. Because the quotient kernel is contained in `S`, `F` descends through
   `section43PositiveEnergyQuotientMap1D` to a complex continuous functional

```lean
A : Section43PositiveEnergy1D →L[ℂ] ℂ
```

8. `F` vanishes on representatives of every compact transform, so
   `A (section43OneSidedLaplaceCompactTransform1D g) = 0` for every compact
   strict-positive source `g`.
9. Apply the compiled annihilator theorem
   `section43OneSidedLaplaceCompactTransform1D_dual_annihilator` to get
   `A = 0`; therefore `F = 0` on ambient Schwartz, and the real-part identity
   for `StrongDual.extendRCLike` gives `f x = 0`, contradicting the separating
   inequality.
10. The quotient dense-range theorem is then a corollary of the preimage theorem
    by `IsOpenQuotientMap.dense_preimage_iff.mp`.

Production status, 2026-04-17: this ambient preimage proof and the dense-range
corollary are compiled as:

```lean
dense_section43OneSidedLaplaceCompactTransform1D_preimage
denseRange_section43OneSidedLaplaceCompactTransform1DLinearMap
```

The analytic annihilator lemma used in Step 9 is:

```lean
theorem section43OneSidedLaplaceCompactTransform1D_dual_annihilator
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ)
    (hA :
      ∀ g : Section43CompactPositiveTimeSource1D,
        A (section43OneSidedLaplaceCompactTransform1D g) = 0) :
    A = 0
```

Mathematical proof:

1. Compose with the quotient map:

```lean
let T : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
  A.comp section43PositiveEnergyQuotientMap1D
```

This `T` depends only on values on `Set.Ici 0`.

2. For each `z` in the upper half-plane, the function
   `σ ↦ exp (Complex.I * z * σ)` restricted to `σ ≥ 0` has a quotient class.
   Pairing `A` with that class defines the Fourier-Laplace transform of the
   distribution represented by `A`.  In Lean, use the existing kernel
   `SCV.schwartzPsiZ z hz`, because
   `SCV.schwartzPsiZ_apply` and `SCV.psiZ_eq_exp_of_nonneg` identify it with the
   exponential on `Set.Ici 0`.

```lean
noncomputable def section43OneSidedAnnihilatorFL
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ)
    (z : ℂ) (hz : 0 < z.im) : ℂ :=
  A (section43PositiveEnergyQuotientMap1D (SCV.schwartzPsiZ z hz))

noncomputable def section43OneSidedAnnihilatorFLOnImag
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ)
    (t : ℝ) : ℂ :=
  if ht : 0 < t then
    section43OneSidedAnnihilatorFL A ((t : ℂ) * Complex.I)
      (by simpa using ht)
  else
    0
```

3. Fubini against a compact strict-positive source `g` rewrites

```lean
A (section43OneSidedLaplaceCompactTransform1D g)
```

as the pairing of `g` against that Fourier-Laplace transform.  Since this is
zero for every compact `g`, the transform vanishes on the strict positive
half-line.

The Lean-facing Fubini theorem should be stated separately:

```lean
theorem section43OneSidedAnnihilatorFL_integral_zero_of_annihilates_laplace
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ)
    (hA :
      ∀ g : Section43CompactPositiveTimeSource1D,
        A (section43OneSidedLaplaceCompactTransform1D g) = 0)
    (g : Section43CompactPositiveTimeSource1D) :
    ∫ t : ℝ,
      section43OneSidedAnnihilatorFLOnImag A t * g.f t = 0
```

The auxiliary `section43OneSidedAnnihilatorFLOnImag` avoids a dependent
positivity proof inside the integrand.  On `tsupport g`, `g.positive` rewrites
the `if` branch to the actual upper-half-plane value; off support the product
with `g.f t` is zero.  No `2 * Real.pi` normalization belongs in this local
density theorem: the production Laplace kernel is
`Complex.exp (-(t : ℂ) * (σ : ℂ))`, while `SCV.schwartzPsiZ ((t : ℂ) * I)`
agrees on `σ ≥ 0` with `Complex.exp (Complex.I * ((t : ℂ) * I) * σ)`,
hence with the same `Complex.exp (-(t : ℂ) * σ)` kernel.

Do not try to prove this theorem as one monolithic Fubini block.  The
implementation-ready bridge should be split into the following exact subpacket.

First define the imaginary-axis kernel with the same off-half-line branch as
`section43OneSidedAnnihilatorFLOnImag`:

```lean
noncomputable def section43ImagAxisPsiKernel (t : ℝ) : SchwartzMap ℝ ℂ :=
  if ht : 0 < t then
    SCV.schwartzPsiZ ((t : ℂ) * Complex.I) (by simpa [Complex.mul_im] using ht)
  else
    0
```

Compile its quotient-pairing identity:

```lean
theorem section43OneSidedAnnihilatorFLOnImag_eq_apply_kernel
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ) (t : ℝ) :
    section43OneSidedAnnihilatorFLOnImag A t =
      A (section43PositiveEnergyQuotientMap1D
        (section43ImagAxisPsiKernel t))
```

Proof split:

- If `0 < t`, unfold both definitions and use proof irrelevance for the
  positivity proofs.
- If `¬ 0 < t`, both sides are zero.

Production status, 2026-04-17: the branch/evaluation subpacket is compiled.
The important representatives are:

```lean
theorem Section43CompactPositiveTimeSource1D.eq_zero_of_not_pos
    (g : Section43CompactPositiveTimeSource1D)
    {t : ℝ} (ht : ¬ 0 < t) :
    g.f t = 0

theorem section43ImagAxisPsiKernel_apply_of_pos_of_nonneg
    {t σ : ℝ} (ht : 0 < t) (hσ : 0 ≤ σ) :
    section43ImagAxisPsiKernel t σ =
      Complex.exp (-(t : ℂ) * (σ : ℂ))

theorem section43OneSidedLaplaceSchwartzRepresentative1D_eq_integral_imagAxisPsiKernel_of_nonneg
    (g : Section43CompactPositiveTimeSource1D)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    section43OneSidedLaplaceSchwartzRepresentative1D g σ =
      ∫ t : ℝ, section43ImagAxisPsiKernel t σ * g.f t

theorem section43OneSidedLaplaceSchwartzRepresentative1D_eq_integral_imagAxisPsiKernel
    (g : Section43CompactPositiveTimeSource1D)
    (σ : ℝ) :
    section43OneSidedLaplaceSchwartzRepresentative1D g σ =
      ∫ t : ℝ, section43ImagAxisPsiKernel t σ * g.f t
```

The last theorem is global in `σ`, not merely a nonnegative-axis statement:
`SCV.psiZ z σ` is `(SCV.smoothCutoff σ : ℂ) * exp (I * z * σ)`, so along
`z = t * I` it equals the same cutoff times `exp (-t * σ)` on all of `ℝ`.
This removes the branch-support and `SCV.psiZ` exponential-identification seam
from the weak-Fubini bridge.

This global value identity is still not enough by itself for an arbitrary
continuous functional `T : SchwartzMap ℝ ℂ →L[ℂ] ℂ`.  Such a `T` may depend on
derivatives and polynomial weights, so the next bridge must identify finitely
many weighted derivative probes under the compact `t`-integral.

Important formalization correction: do **not** define a Bochner integral valued
in `SchwartzMap ℝ ℂ`.  In this repository `SchwartzMap` carries the locally
convex Schwartz topology, but it is not a `NormedAddCommGroup`, so
`∫ t, g.f t • section43ImagAxisPsiKernel t` is not a legal Bochner integral in
Lean.  The correct bridge is a scalar, weak Fubini theorem after applying an
arbitrary continuous linear functional.

The next implementation target should therefore be:

```lean
theorem section43OneSidedLaplace_scalar_fubini_apply
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (g : Section43CompactPositiveTimeSource1D) :
    T (section43OneSidedLaplaceSchwartzRepresentative1D g) =
      ∫ t : ℝ, T (section43ImagAxisPsiKernel t) * g.f t
```

After this theorem, the annihilator Fubini theorem is short:

```lean
have hT :
    A (section43PositiveEnergyQuotientMap1D
        (section43OneSidedLaplaceSchwartzRepresentative1D g)) =
      ∫ t : ℝ,
        section43OneSidedAnnihilatorFLOnImag A t * g.f t := by
  simpa [ContinuousLinearMap.comp_apply,
    section43OneSidedAnnihilatorFLOnImag_eq_apply_kernel,
    mul_comm, mul_left_comm, mul_assoc]
    using section43OneSidedLaplace_scalar_fubini_apply
      ((A.comp section43PositiveEnergyQuotientMap1D)) g
```

Then combine with
`section43OneSidedLaplaceCompactTransform1D_eq_cutoff_quotient` and `hA g`.

Lean proof plan for `section43OneSidedLaplace_scalar_fubini_apply`:

1. Introduce local public copies of the finite-probe machinery currently used
   privately in `SCV.PaleyWiener`: a polynomial weight, iterated derivative CLM,
   weighted derivative BCF CLM, and finite product probe.

```lean
def section43PolyWeight (k : ℕ) (σ : ℝ) : ℂ := ((1 + σ^2) ^ k : ℝ)

def section43IteratedDerivCLM :
    ℕ → SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ

def section43WeightedDerivToBCFCLM
    (k n : ℕ) : SchwartzMap ℝ ℂ →L[ℂ] ℝ →ᵇ ℂ

def section43ProbeCLM (s : Finset (ℕ × ℕ)) :
    SchwartzMap ℝ ℂ →L[ℂ] ((p : ↑s.attach) → (ℝ →ᵇ ℂ))
```

   This is not a wrapper around the theorem statement; it is the finite
   normed target where Bochner integration is legal.

2. Prove a public factorization theorem for continuous Schwartz functionals,
   parallel to the private `exists_probe_factorization` in `SCV.PaleyWiener`:

```lean
theorem section43_exists_probe_factorization
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ) :
    ∃ s : Finset (ℕ × ℕ),
    ∃ G : ((p : ↑s.attach) → (ℝ →ᵇ ℂ)) →L[ℂ] ℂ,
      T = G.comp (section43ProbeCLM s)
```

   Proof transcript:

   - Use `SCV.schwartz_functional_bound T`.
   - Show each selected Schwartz seminorm is bounded by the norm of the
     corresponding probe component, exactly as in
     `schwartzSeminorm_le_probe_component_norm`.
   - Bound `‖T f‖` by `C * ‖section43ProbeCLM s f‖`.
   - Show `ker (section43ProbeCLM s) ≤ ker T`.
   - Define the linear map on the range of `section43ProbeCLM s`.
   - Apply Hahn-Banach `exists_extension_norm_eq` to extend it to the finite
     Banach product.

Production status, 2026-04-17: Steps 1 and 2 are compiled in
`Section43FourierLaplaceDensity.lean`.

3. Prove the derivative-level kernel identity, not only the value identity:

```lean
theorem section43OneSidedLaplaceSchwartzRepresentative1D_iteratedDeriv_eq_integral_kernel_iteratedDeriv
    (g : Section43CompactPositiveTimeSource1D) (n : ℕ) (σ : ℝ) :
    iteratedDeriv n (section43OneSidedLaplaceSchwartzRepresentative1D g) σ =
      ∫ t : ℝ,
        iteratedDeriv n (fun σ : ℝ => section43ImagAxisPsiKernel t σ) σ *
          g.f t
```

   Proof transcript:

   - Let `χ σ := (SCV.smoothCutoff σ : ℂ)`.
   - For the left side, use
     `section43OneSidedLaplaceSchwartzRepresentative1D_apply`,
     `section43OneSidedLaplaceCutoffFun`, and `iteratedDeriv_mul` to get

```lean
∑ i ∈ Finset.range (n + 1),
  (n.choose i : ℂ) *
    iteratedDeriv i χ σ *
      section43OneSidedLaplaceRawDerivCandidate g (n - i) σ
```

   - For the right side, use
     `section43ImagAxisPsiKernel_apply_mul_source`: on `0 < t` the kernel is
     `χ σ * exp (-(t : ℂ) * σ)`, while on `¬ 0 < t` the source value is zero.
   - Apply `iteratedDeriv_mul` to the product
     `χ σ * exp (-(t : ℂ) * σ)`.
   - Use `iteratedDeriv_cexp_const_mul_real` to rewrite the exponential
     derivative as `(-(t : ℂ)) ^ (n - i) * exp (-(t : ℂ) * σ)`.
   - Move the finite sum through the scalar integral using `integral_finset_sum`
     and use `section43OneSidedLaplaceRawDerivCandidate_integrable` for each
     summand.
   - Pull constants independent of `t` out with `integral_const_mul`.

Production status, 2026-04-17: Step 3 is compiled as:

```lean
theorem section43OneSidedLaplaceSchwartzRepresentative1D_iteratedDeriv_formula
    (g : Section43CompactPositiveTimeSource1D) (n : ℕ) (σ : ℝ) :
    iteratedDeriv n (section43OneSidedLaplaceSchwartzRepresentative1D g) σ =
      ∑ i ∈ Finset.range (n + 1),
        n.choose i *
          iteratedDeriv i (fun σ : ℝ => (SCV.smoothCutoff σ : ℂ)) σ *
            section43OneSidedLaplaceRawDerivCandidate g (n - i) σ

theorem section43ImagAxisPsiKernel_iteratedDeriv_mul_source
    (g : Section43CompactPositiveTimeSource1D)
    (n : ℕ) (σ t : ℝ) :
    iteratedDeriv n (fun σ : ℝ => section43ImagAxisPsiKernel t σ) σ *
        g.f t =
      ∑ i ∈ Finset.range (n + 1),
        n.choose i *
          iteratedDeriv i (fun σ : ℝ => (SCV.smoothCutoff σ : ℂ)) σ *
            ((-(t : ℂ)) ^ (n - i) *
              Complex.exp (-(t : ℂ) * (σ : ℂ)) * g.f t)

theorem section43OneSidedLaplaceSchwartzRepresentative1D_iteratedDeriv_eq_integral_kernel_iteratedDeriv
    (g : Section43CompactPositiveTimeSource1D) (n : ℕ) (σ : ℝ) :
    iteratedDeriv n (section43OneSidedLaplaceSchwartzRepresentative1D g) σ =
      ∫ t : ℝ,
        iteratedDeriv n (fun σ : ℝ => section43ImagAxisPsiKernel t σ) σ *
          g.f t
```

The remaining weak-Fubini work now starts at Step 4: packaging these scalar
derivative identities into equality after applying `section43ProbeCLM s`.

4. Upgrade the derivative identity to finite probes:

```lean
theorem section43Probe_integral_imagAxisPsiKernel
    (s : Finset (ℕ × ℕ))
    (g : Section43CompactPositiveTimeSource1D) :
    section43ProbeCLM s (section43OneSidedLaplaceSchwartzRepresentative1D g) =
      ∫ t : ℝ,
        g.f t • section43ProbeCLM s (section43ImagAxisPsiKernel t)
```

   This is a Banach-valued Bochner integral in the finite product of bounded
   continuous functions, not a Schwartz-valued integral.  Prove by extensionality
   in `p : s.attach` and `σ : ℝ`, using the derivative identity from Step 3.

Production status, 2026-04-17: the scalar component/evaluation form of Step 4
is compiled:

```lean
theorem section43WeightedDerivToBCFCLM_representative_eq_integral_kernel_apply
    (g : Section43CompactPositiveTimeSource1D)
    (k n : ℕ) (σ : ℝ) :
    section43WeightedDerivToBCFCLM k n
        (section43OneSidedLaplaceSchwartzRepresentative1D g) σ =
      ∫ t : ℝ,
        g.f t *
          section43WeightedDerivToBCFCLM k n
            (section43ImagAxisPsiKernel t) σ
```

The remaining part of Step 4 is the Banach-valued packaging:

```lean
section43ProbeCLM s (section43OneSidedLaplaceSchwartzRepresentative1D g) =
  ∫ t : ℝ, g.f t • section43ProbeCLM s (section43ImagAxisPsiKernel t)
```

This should now be placed in a small companion file, because
`Section43FourierLaplaceDensity.lean` is already around 1600 lines.

5. Prove the finite-probe integrability through compact-support continuity,
   not by trying to build a global Schwartz-valued majorant.

The companion file should start with the following public support lemma copied
from the private Paley-Wiener proof, with the `section43*` names:

```lean
theorem section43WeightedDerivToBCFCLM_norm_le
    (k n : ℕ) (f : SchwartzMap ℝ ℂ) :
    ‖section43WeightedDerivToBCFCLM k n f‖ ≤
      (2 : ℝ) ^ k *
        (SchwartzMap.seminorm ℝ 0 n f +
          SchwartzMap.seminorm ℝ (2 * k) n f)
```

Proof transcript:

- Use `BoundedContinuousFunction.dist_le` after rewriting the norm as distance
  from zero.
- For `|σ| ≤ 1`, use
  `‖section43PolyWeight k σ‖ ≤ 2^k` and
  `SchwartzMap.le_seminorm' (k := 0)`.
- For `1 < |σ|`, use
  `‖section43PolyWeight k σ‖ ≤ 2^k * |σ|^(2*k)` and
  `SchwartzMap.le_seminorm' (k := 2*k)`.
- This is exactly the estimate needed to turn Schwartz-topology convergence of
  `ψ_z` into BCF-norm convergence of the weighted probes.

Then prove positive-axis continuity of the weighted probe family:

```lean
theorem continuousOn_section43WeightedDerivToBCFCLM_imagAxisPsiKernel_Ioi
    (k n : ℕ) :
    ContinuousOn
      (fun t : ℝ =>
        section43WeightedDerivToBCFCLM k n
          (section43ImagAxisPsiKernel t))
      (Set.Ioi (0 : ℝ))
```

Proof transcript:

- Fix `t₀ > 0`.  On a small neighborhood with
  `‖h‖ ≤ t₀ / 2`, both `t₀ + h` and `t₀` remain in the positive branch, so
  `section43ImagAxisPsiKernel (t₀ + h)` and
  `section43ImagAxisPsiKernel t₀` unfold to
  `SCV.schwartzPsiZ (((t₀ + h : ℝ) : ℂ) * Complex.I) _` and
  `SCV.schwartzPsiZ ((t₀ : ℂ) * Complex.I) _`.
- Apply the already public remainder theorem
  `SCV.schwartzPsiZExpTaylorLinearRemainderQuot_seminorm_le` at
  `z := (t₀ : ℂ) * Complex.I` and complex increment
  `hC := (h : ℂ) * Complex.I`.  Its hypotheses are:
  `0 < z.im`, `‖hC‖ ≤ z.im / 2`, and `‖hC‖ ≤ 1`.
- Use the identity behind
  `SCV.psiZ_sub_sub_deriv_eq_smul_remainder` to write

```lean
SCV.schwartzPsiZ (z + hC) _ - SCV.schwartzPsiZ z _ =
  hC • ((SchwartzMap.smulLeftCLM ℂ (fun σ : ℝ => Complex.I * (σ : ℂ)))
      (SCV.schwartzPsiZ z _)) +
  hC • SCV.schwartzPsiZExpTaylorLinearRemainderQuot z _ hC _ _
```

  after extensionality in `σ`.
- Apply `section43WeightedDerivToBCFCLM k n` to that equality.  Bound the norm
  by the sum of the two `hC`-scaled terms.  The derivative term has fixed norm;
  the remainder term is bounded by
  `section43WeightedDerivToBCFCLM_norm_le` and
  `SCV.schwartzPsiZExpTaylorLinearRemainderQuot_seminorm_le` for seminorms
  `(0,n)` and `(2*k,n)`.
- The resulting bound is `const * ‖h‖`, which tends to zero.  This proves
  continuity at `t₀`; assemble with `continuousOn_iff_continuousAt`.

This is the exact vertical analogue of the private horizontal-continuity block
in `SCV.PaleyWiener` around
`tendsto_weightedDerivToBCFCLM_schwartzPsiZ_horizontal_diff_zero` and
`continuous_weightedDerivToBCFCLM_schwartzPsiZ_horizontal`, except the complex
increment is `h * I` instead of `h`.

Now prove component integrability, using the compact strict-positive support of
`g`:

```lean
theorem integrable_section43WeightedProbe_imagAxisPsiKernel_source
    (g : Section43CompactPositiveTimeSource1D)
    (k n : ℕ) :
    Integrable
      (fun t : ℝ =>
        g.f t •
          section43WeightedDerivToBCFCLM k n
            (section43ImagAxisPsiKernel t))
```

Proof transcript:

- Choose `δ R` from
  `exists_positive_Icc_bounds_of_compactPositiveTimeSource g`.
- Prove the support inclusion

```lean
Function.support
  (fun t : ℝ =>
    g.f t • section43WeightedDerivToBCFCLM k n
      (section43ImagAxisPsiKernel t))
  ⊆ Set.Icc δ R
```

  because if the smul is nonzero then `g.f t ≠ 0`, hence
  `t ∈ tsupport (g.f : ℝ → ℂ)`, and the chosen support bound applies.
- Prove `ContinuousOn` of the same function on `Set.Icc δ R` by combining:
  `g.f.continuous.continuousOn`,
  `continuousOn_section43WeightedDerivToBCFCLM_imagAxisPsiKernel_Ioi k n`,
  and `Set.Icc δ R ⊆ Set.Ioi 0`, which follows from `0 < δ` and `δ ≤ t`.
- Apply `ContinuousOn.integrableOn_compact` on `Set.Icc δ R`, then convert to
  global integrability using
  `integrableOn_iff_integrable_of_support_subset`.

The finite-product integrability theorem is then mechanical:

```lean
theorem integrable_section43Probe_imagAxisPsiKernel_source
    (s : Finset (ℕ × ℕ))
    (g : Section43CompactPositiveTimeSource1D) :
    Integrable
      (fun t : ℝ =>
        g.f t • section43ProbeCLM s (section43ImagAxisPsiKernel t))
```

Proof transcript:

- Use `Integrable.of_eval`.
- For each `p : ↑s.attach`, unfold `section43ProbeCLM` and use
  `integrable_section43WeightedProbe_imagAxisPsiKernel_source g
    p.1.1.1 p.1.1.2`.

With this integrability in hand, the Banach-valued probe identity is a pure
extensionality argument:

```lean
theorem section43Probe_integral_imagAxisPsiKernel
    (s : Finset (ℕ × ℕ))
    (g : Section43CompactPositiveTimeSource1D) :
    section43ProbeCLM s (section43OneSidedLaplaceSchwartzRepresentative1D g) =
      ∫ t : ℝ,
        g.f t • section43ProbeCLM s (section43ImagAxisPsiKernel t)
```

Proof transcript:

- `ext p σ`.
- Move the finite-product projection through the Bochner integral using
  `(ContinuousLinearMap.proj ... p).integral_comp_comm
    (integrable_section43Probe_imagAxisPsiKernel_source s g)`.
- Move BCF evaluation through the component integral using
  `(BoundedContinuousFunction.evalCLM ℂ σ).integral_comp_comm
    (integrable_section43WeightedProbe_imagAxisPsiKernel_source g
      p.1.1.1 p.1.1.2)`.
- Simplify the projected/evaluated integrand to
  `g.f t * section43WeightedDerivToBCFCLM p.1.1.1 p.1.1.2
    (section43ImagAxisPsiKernel t) σ`.
- Finish with the already compiled scalar component identity
  `section43WeightedDerivToBCFCLM_representative_eq_integral_kernel_apply`.

6. Combine finite-probe Fubini with the factorization:

```lean
obtain ⟨s, G, hTG⟩ := section43_exists_probe_factorization T
calc
  T (section43OneSidedLaplaceSchwartzRepresentative1D g)
      = G (section43ProbeCLM s
          (section43OneSidedLaplaceSchwartzRepresentative1D g)) := by
          rw [hTG]
  _ = G (∫ t, g.f t • section43ProbeCLM s (section43ImagAxisPsiKernel t)) := by
          rw [section43Probe_integral_imagAxisPsiKernel]
  _ = ∫ t, G (g.f t • section43ProbeCLM s (section43ImagAxisPsiKernel t)) := by
          exact (G.integral_comp_comm
            (integrable_section43Probe_imagAxisPsiKernel_source s g)).symm
  _ = ∫ t, T (section43ImagAxisPsiKernel t) * g.f t := by
          apply integral_congr_ae
          filter_upwards with t
          rw [hTG]
          simp [map_smul, smul_eq_mul, mul_comm]
```

The older compact-vertical-segment seminorm bound remains useful as a possible
way to prove Step 5, but it is not sufficient alone.  The finite-probe identity
requires derivative-level equality under the compact scalar integral.

Earlier seminorm-bound target, retained as a support lemma:

```lean
theorem section43ImagAxisPsiKernel_seminorm_le_on_Icc
    {δ R : ℝ} (hδ_pos : 0 < δ) (hδR : δ ≤ R)
    (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t ∈ Set.Icc δ R,
        SchwartzMap.seminorm ℂ k n (section43ImagAxisPsiKernel t) ≤ C
```

   This is best proved directly from the explicit `SCV.psiZ` formula.  For
   `t ∈ [δ,R]` and derivative order `n`, the derivative contributes a power of
   `t`, bounded by `max |δ| |R| ^ n`, and the exponential factor decays like
   `exp (-t * σ)` on `σ ≥ 0` while the cutoff side of `SCV.psiZ` handles
   `σ < 0` by the already-proved Schwartz estimates in `SCV.schwartzPsiZ`.
   If direct proof is too large, first prove the bound by continuity of
   `t ↦ weightedDerivToBCFCLM k n (section43ImagAxisPsiKernel t)` on compact
   `[δ,R]`, following the horizontal-continuity pattern in `SCV.PaleyWiener`.
7. Prove scalar integrability as a corollary of Steps 2 and 5:

```lean
theorem integrable_section43_scalar_kernel_after_functional
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (g : Section43CompactPositiveTimeSource1D) :
    Integrable (fun t : ℝ => T (section43ImagAxisPsiKernel t) * g.f t)
```

   Use the seminorm bound from Step 3, the functional bound from Step 1, and
   compact support/integrability of `g.f`.
8. The global scalar rewrite is already compiled as
   `section43OneSidedLaplaceSchwartzRepresentative1D_eq_integral_imagAxisPsiKernel`.
   It should be used as the `n = 0`, `k = 0` sanity check for Step 3, not as a
   substitute for the derivative-level probe identity.

Then convert integral vanishing against every compact strict-positive source to
pointwise vanishing on the strict half-line using the existing local
distribution lemma.  Since `section43OneSidedAnnihilatorFLOnImag` has an
off-half-line zero branch and need not be globally continuous at the origin, use
the continuous-on-open version, not the global-continuity version:

```lean
OSReconstruction.SCV.eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn
```

The Lean target is:

```lean
theorem section43OneSidedAnnihilatorFLOnImag_eq_zero_of_annihilates_laplace
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ)
    (hA :
      ∀ g : Section43CompactPositiveTimeSource1D,
        A (section43OneSidedLaplaceCompactTransform1D g) = 0) :
    ∀ t : ℝ, 0 < t →
      section43OneSidedAnnihilatorFLOnImag A t = 0
```

Compiled continuity input:

```lean
theorem continuousOn_section43OneSidedAnnihilatorFLOnImag_Ioi
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ) :
    ContinuousOn (section43OneSidedAnnihilatorFLOnImag A) (Set.Ioi (0 : ℝ))
```

It rewrites `section43OneSidedAnnihilatorFL` as
`SCV.fourierLaplaceExt (section43PositiveEnergy1D_to_oneSidedFourierFunctional A)`,
uses `SCV.fourierLaplaceExt_differentiableOn.continuousOn`, and composes with
the vertical path `t ↦ (t : ℂ) * Complex.I`.

Proof transcript:

1. Apply `eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn`
   with `U := Set.Ioi (0 : ℝ)`, `g := section43OneSidedAnnihilatorFLOnImag A`,
   and `h := 0`.
2. Continuity of `g` on `Set.Ioi 0` is exactly
   `continuousOn_section43OneSidedAnnihilatorFLOnImag_Ioi A`; continuity of
   `h := 0` is immediate.
3. Its test-function hypothesis is exactly
   `section43OneSidedAnnihilatorFL_integral_zero_of_annihilates_laplace`, after
   packaging an arbitrary compactly supported Schwartz test with support in
   `Set.Ioi 0` as `Section43CompactPositiveTimeSource1D`.
4. On `0 < t`, unfold `section43OneSidedAnnihilatorFLOnImag` to obtain
   `section43OneSidedAnnihilatorFL A ((t : ℂ) * Complex.I) _ = 0`.

4. The transform is holomorphic in the upper half-plane.  Vanishing on the
   positive imaginary axis, or any set with an accumulation point in the
   domain after the standard OS I contour normalization, implies vanishing on
   the upper half-plane by the identity theorem.  This identity-theorem step is
   now the only uncompiled uniqueness substep: the subsequent Paley-Wiener
   endpoint `section43PositiveEnergy1D_ext_of_FL_zero` is compiled.

Use existing complex-analysis infrastructure where possible:
`SCV.fourierLaplaceExt`, `SCV.fourierLaplaceExt_eq`,
`SCV.fourierLaplaceExt_differentiableOn`, and
`identity_theorem_right_halfplane` / totally-real identity lemmas already used
elsewhere in Wick rotation.

Lean target:

```lean
theorem section43OneSidedAnnihilatorFL_eq_zero_of_annihilates_laplace
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ)
    (hA :
      ∀ g : Section43CompactPositiveTimeSource1D,
        A (section43OneSidedLaplaceCompactTransform1D g) = 0) :
    ∀ (z : ℂ) (hz : 0 < z.im),
      section43OneSidedAnnihilatorFL A z hz = 0
```

Proof transcript:

1. Prove holomorphicity of
   `z ↦ section43OneSidedAnnihilatorFL A z hz` on `SCV.upperHalfPlane` by
   rewriting it as `SCV.fourierLaplaceExt
   (section43PositiveEnergy1D_to_oneSidedFourierFunctional A) z hz`.
2. The previous theorem gives vanishing on the vertical ray
   `{z | ∃ t > 0, z = (t : ℂ) * Complex.I}`.
3. The vertical ray has accumulation points inside the upper half-plane, for
   example at `Complex.I`; use the identity theorem to conclude vanishing on
   the connected upper half-plane.

The last step is uniqueness of the Fourier-Laplace transform for distributions
supported in `Set.Ici 0`: it gives `T = 0`, hence `A = 0` because
`section43PositiveEnergyQuotientMap1D` is surjective.

The clean Lean route is to convert the quotient functional to a one-sided
Fourier-support functional and then reuse existing `SCV.PaleyWiener`
infrastructure.  Define:

```lean
noncomputable def section43PositiveEnergy1D_to_oneSidedFourierFunctional
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ) :
    SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
  (A.comp section43PositiveEnergyQuotientMap1D).comp
    section43FourierInvCLM1D
```

where the local CLM wrapper is:

```lean
noncomputable def section43FourierInvCLM1D :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  FourierTransform.fourierInvCLM ℂ (SchwartzMap ℝ ℂ)

@[simp] theorem section43FourierInvCLM1D_apply
    (φ : SchwartzMap ℝ ℂ) :
    section43FourierInvCLM1D φ = FourierTransform.fourierInv φ
```

The inverse identities already used in the repo are
`FourierTransform.fourierInv_fourier_eq` and
`FourierTransform.fourier_fourierInv_eq`.

Prove:

```lean
theorem section43PositiveEnergy1D_to_oneSidedFourierFunctional_support
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ) :
    SCV.HasOneSidedFourierSupport
      (section43PositiveEnergy1D_to_oneSidedFourierFunctional A)

theorem fourierPairingDescendsToSection43PositiveEnergy1D_to_oneSided
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ) :
    OSReconstruction.fourierPairingDescendsToSection43PositiveEnergy1D
        (section43PositiveEnergy1D_to_oneSidedFourierFunctional A)
        (section43PositiveEnergy1D_to_oneSidedFourierFunctional_support A)
      = A
```

The first theorem is formal: if `φ` is supported in `(-∞,0)`, then
`section43PositiveEnergyQuotientMap1D φ = 0`; after applying
`fourierInv_fourier_eq`, this is exactly the one-sided Fourier-support
condition.  The second theorem is formal by surjectivity of
`section43PositiveEnergyQuotientMap1D` and `fourierInv_fourier_eq`.

The local uniqueness endpoint is compiled:

```lean
theorem section43PositiveEnergy1D_ext_of_FL_zero
    (A : Section43PositiveEnergy1D →L[ℂ] ℂ)
    (hFL :
      ∀ (z : ℂ) (hz : 0 < z.im),
        section43OneSidedAnnihilatorFL A z hz = 0) :
    A = 0
```

Compiled proof transcript:

1. Let `T := section43PositiveEnergy1D_to_oneSidedFourierFunctional A`.
2. Rewrite `section43OneSidedAnnihilatorFL A z hz` as
   `SCV.fourierLaplaceExt T z hz` using
   `fourierPairingDescendsToSection43PositiveEnergy1D_to_oneSided` and
   `SCV.fourierLaplaceExt_eq`.
3. Since this extension is identically zero on the upper half-plane, the
   scaled function appearing in `SCV.paley_wiener_half_line_explicit` is
   identically zero on every positive horizontal line.
4. Apply `SCV.paley_wiener_half_line_explicit T
   (section43PositiveEnergy1D_to_oneSidedFourierFunctional_support A)` and
   uniqueness of limits in `nhds` to get `T = 0`.  The explicit theorem uses
   the scaled argument `(2 * Real.pi) * w`; this is compatible because `hFL`
   vanishes for every upper-half-plane input `z`.
5. Use
   `fourierPairingDescendsToSection43PositiveEnergy1D_to_oneSided A` to conclude
   `A = 0`.

This proof is exactly the density half of OS I Lemma 8.2.  It is the deepest
part of the packet.  It should stay isolated as pure analysis.

## Layer 2: Finite Time Product

Layer 2 should not be implemented as a vague "coordinate induction".  The
Lean-ready route is a tensor-product density argument:

- use the already-compiled one-variable dense preimage theorem for each factor;
- use the nuclear/product-tensor density theorem to reduce the finite time
  Schwartz space to finite sums of pure tensors;
- prove that a pure tensor whose factors are one-variable compact-Laplace
  preimage representatives lies in the multitime compact-Laplace preimage;
- close density because the multitime preimage is a submodule.

This is still OS I Lemma 4.1: Lemma 8.2 supplies the one-coordinate positive
support Fourier-Laplace density, and the Schwartz nuclear theorem supplies the
finite product passage.

Definitions to add in a new small companion file, not in the already-large
one-variable density file:

```lean
def section43TimePositiveRegion (n : ℕ) : Set (Fin n → ℝ) :=
  {τ | ∀ i : Fin n, 0 ≤ τ i}

def section43TimeStrictPositiveRegion (n : ℕ) : Set (Fin n → ℝ) :=
  {τ | ∀ i : Fin n, 0 < τ i}

def section43TimeVanishingSubmodule (n : ℕ) :
    Submodule ℂ (SchwartzMap (Fin n → ℝ) ℂ)

abbrev Section43TimePositiveComponent (n : ℕ) :=
  (SchwartzMap (Fin n → ℝ) ℂ) ⧸ section43TimeVanishingSubmodule n

noncomputable def section43TimePositiveQuotientMap (n : ℕ) :
    SchwartzMap (Fin n → ℝ) ℂ →L[ℂ]
      Section43TimePositiveComponent n

structure Section43CompactStrictPositiveTimeSource (n : ℕ) where
  f : SchwartzMap (Fin n → ℝ) ℂ
  positive :
    tsupport (f : (Fin n → ℝ) → ℂ) ⊆
      section43TimeStrictPositiveRegion n
  compact : HasCompactSupport (f : (Fin n → ℝ) → ℂ)

def section43IteratedLaplaceRepresentative
    (n : ℕ)
    (g : Section43CompactStrictPositiveTimeSource n)
    (Φ : SchwartzMap (Fin n → ℝ) ℂ) : Prop :=
  ∀ σ : Fin n → ℝ, σ ∈ section43TimePositiveRegion n →
    Φ σ =
      ∫ τ : Fin n → ℝ,
        Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) *
          g.f τ
```

The source type must be made into a complex module exactly as in the
one-variable source packet:

```lean
namespace Section43CompactStrictPositiveTimeSource

instance : Zero (Section43CompactStrictPositiveTimeSource n)
instance : Add (Section43CompactStrictPositiveTimeSource n)
instance : SMul ℕ (Section43CompactStrictPositiveTimeSource n)
instance : AddCommMonoid (Section43CompactStrictPositiveTimeSource n)
instance : SMul ℂ (Section43CompactStrictPositiveTimeSource n)
instance : Module ℂ (Section43CompactStrictPositiveTimeSource n)

end Section43CompactStrictPositiveTimeSource
```

The proof obligations are the same support-stability obligations as in the
one-variable file.  Addition uses `tsupport_add` and
`HasCompactSupport.add`; scalar multiplication uses
`tsupport_smul_subset_right` and `HasCompactSupport.smul_left`.

Package the multitime transform as a linear map:

```lean
noncomputable def section43IteratedLaplaceCompactTransform
    (n : ℕ) :
    Section43CompactStrictPositiveTimeSource n →
      Section43TimePositiveComponent n

theorem section43IteratedLaplaceCompactTransform_eq_quotient
    (g : Section43CompactStrictPositiveTimeSource n)
    (Φ : SchwartzMap (Fin n → ℝ) ℂ)
    (hΦ : section43IteratedLaplaceRepresentative n g Φ) :
    section43IteratedLaplaceCompactTransform n g =
      section43TimePositiveQuotientMap n Φ

theorem section43IteratedLaplaceCompactTransform_map_add
    (g h : Section43CompactStrictPositiveTimeSource n) :
    section43IteratedLaplaceCompactTransform n (g + h) =
      section43IteratedLaplaceCompactTransform n g +
        section43IteratedLaplaceCompactTransform n h

theorem section43IteratedLaplaceCompactTransform_map_smul
    (c : ℂ) (g : Section43CompactStrictPositiveTimeSource n) :
    section43IteratedLaplaceCompactTransform n (c • g) =
      c • section43IteratedLaplaceCompactTransform n g

noncomputable def section43IteratedLaplaceCompactTransformLinearMap
    (n : ℕ) :
    Section43CompactStrictPositiveTimeSource n →ₗ[ℂ]
      Section43TimePositiveComponent n
```

For `map_add` and `map_smul`, use quotient equality on
`section43TimePositiveRegion n`; rewrite the representative integral by
linearity of the scalar integral.  Integrability follows from compact support of
the source and boundedness of the exponential on compact support when
`σ` is fixed in the closed positive orthant.

### Layer 2A: Time Product Tensors

Name the pure tensor map explicitly:

```lean
noncomputable def section43TimeProductTensor
    {n : ℕ} (fs : Fin n → SchwartzMap ℝ ℂ) :
    SchwartzMap (Fin n → ℝ) ℂ :=
  SchwartzMap.productTensor fs
```

The first density input is product-tensor density for `SchwartzMap (Fin n → ℝ)
ℂ`.  The existing theorem

```lean
productTensor_span_dense 0 n
```

lives on

```lean
SchwartzMap (Fin n → Fin 1 → ℝ) ℂ
```

so add an explicit transport:

```lean
noncomputable def section43TimeAsOnePointCLE (n : ℕ) :
    (Fin n → ℝ) ≃L[ℝ] (Fin n → Fin 1 → ℝ)

theorem section43_timeProductTensor_span_dense (n : ℕ) :
    Dense
      (((Submodule.span ℂ
        {F : SchwartzMap (Fin n → ℝ) ℂ |
          ∃ fs : Fin n → SchwartzMap ℝ ℂ,
            F = section43TimeProductTensor fs}) :
        Submodule ℂ (SchwartzMap (Fin n → ℝ) ℂ)) :
        Set (SchwartzMap (Fin n → ℝ) ℂ))
```

Proof transcript:

1. Define `section43TimeAsOnePointCLE n` by
   `x i () = x i`, with inverse `y i = y i 0`.
2. Transfer `productTensor_span_dense 0 n` through
   `SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
     (section43TimeAsOnePointCLE n)` and its inverse.
3. The pointwise compatibility theorem is:

```lean
theorem section43TimeAsOnePoint_productTensor
    (fs : Fin n → SchwartzMap ℝ ℂ) :
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (section43TimeAsOnePointCLE n).symm
        (section43TimeProductTensor fs)
      =
    SchwartzMap.productTensor
      (fun i : Fin n =>
        SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)
          (fs i))
```

   Prove by extensionality and `SchwartzMap.productTensor_apply`.

The second density input is the factorwise dense-subset version:

```lean
theorem section43_timeProductTensor_span_dense_of_factor_dense
    {S : Set (SchwartzMap ℝ ℂ)}
    (hS : Dense S) (n : ℕ) :
    Dense
      (((Submodule.span ℂ
        {F : SchwartzMap (Fin n → ℝ) ℂ |
          ∃ fs : Fin n → SchwartzMap ℝ ℂ,
            (∀ i : Fin n, fs i ∈ S) ∧
            F = section43TimeProductTensor fs}) :
        Submodule ℂ (SchwartzMap (Fin n → ℝ) ℂ)) :
        Set (SchwartzMap (Fin n → ℝ) ℂ))
```

Proof transcript:

1. Let `Pall` be all time product tensors and `PS` product tensors whose
   factors lie in `S`.
2. Show `Pall ⊆ closure (Submodule.span ℂ PS)`.
3. For a fixed `fs`, use density of the finite product set
   `{gs : Fin n → SchwartzMap ℝ ℂ | ∀ i, gs i ∈ S}` in
   `Fin n → SchwartzMap ℝ ℂ`.  This is the finite-pi density theorem from
   Mathlib, applied to `hS`.
4. Apply continuity of `fun gs => section43TimeProductTensor gs`
   (`SchwartzMap.productTensor_continuous`) to put
   `section43TimeProductTensor fs` in the closure of the image of this dense
   pi-set.
5. The image is contained in `PS`, hence in `Submodule.span ℂ PS`.
6. Since `Submodule.topologicalClosure` is a submodule, it contains
   `Submodule.span ℂ Pall`.
7. Finish with `section43_timeProductTensor_span_dense n`.

This theorem is purely topological.  It should not mention Laplace transforms,
OS positivity, or Wightman objects.

Production status, 2026-04-18: the finite-time quotient/source surface and the
pure product-tensor density packet are compiled in
`Section43FourierLaplaceTimeProduct.lean`:

```lean
section43TimePositiveRegion
section43TimeStrictPositiveRegion
section43TimePositiveThickening
section43TimePositiveCutoff
section43TimePositiveCutoff_eq_one_of_mem
section43TimePositiveCutoff_eq_zero_of_time_le_neg_one
section43TimePositiveCutoff_eq_zero_of_not_mem_thickening_one
section43TimePositiveCutoff_contDiff
section43TimePositiveCutoff_hasTemperateGrowth
section43TimePositiveCutoff_iteratedFDeriv_eq_zero_of_not_mem_thickening_one
section43TimePositiveCutoff_iteratedFDeriv_support_subset_thickening_one
section43TimeVanishingSubmodule
Section43TimePositiveComponent
section43TimePositiveQuotientMap
section43TimePositiveQuotientMap_eq_of_eqOn_region
eqOn_region_of_section43TimePositiveQuotientMap_eq
section43TimeProductTensor
section43TimeAsOnePointCLE
section43TimeAsOnePoint_productTensor
section43TimeAsOnePoint_symm_productTensor
section43TimeAsOnePoint_comp_symm
section43TimeAsOnePoint_symm_comp
section43_timeProductTensor_span_dense
section43_timeProductTensor_span_dense_of_factor_dense
Section43CompactStrictPositiveTimeSource
Section43CompactStrictPositiveTimeSource.instZero
Section43CompactStrictPositiveTimeSource.instAdd
Section43CompactStrictPositiveTimeSource.instSMulNat
Section43CompactStrictPositiveTimeSource.instAddCommMonoid
Section43CompactStrictPositiveTimeSource.instSMul
Section43CompactStrictPositiveTimeSource.instModule
exists_positive_margin_of_isCompact_subset_Ioi
exists_positive_margin_of_compact_time_tsupport_subset_strictPositive
exists_time_closedBall_of_compact_tsupport
continuous_cmlm_apply_time
tsupport_section43TimeProductTensor_subset_pi_tsupport
hasCompactSupport_section43TimeProductTensor
section43TimeProductSource
section43IteratedLaplaceRaw
section43IteratedLaplaceCutoffFun
section43IteratedLaplaceCutoffFun_eq_raw_of_mem
contDiff_section43IteratedLaplaceRaw_integrand_sigma
hasFDerivAt_section43IteratedLaplaceRaw_integrand_iteratedFDeriv_curryLeft
section43IteratedLaplaceRaw_iteratedFDerivCandidate
section43TimeProductSource_integral_eq_product_raw
section43TimeProductTensor_oneSidedLaplaceRepresentative_eq_integral
section43IteratedLaplaceRepresentative
section43TimeProductTensor_oneSidedLaplaceRepresentative
exists_section43IteratedLaplaceRepresentative_productSource
```

This closes Layer 2A and the product-source support/factorization half of
Layer 2B.  The remaining Layer 2B implementation starts at the honest multitime
Laplace transform package:

```lean
section43IteratedLaplaceRepresentative
exists_section43IteratedLaplaceRepresentative
section43IteratedLaplaceCompactTransform
section43IteratedLaplaceCompactTransform_eq_quotient
section43IteratedLaplaceCompactTransform_productSource
```

### Layer 2B-0: Arbitrary Multitime Representative Existence

The theorem

```lean
theorem exists_section43IteratedLaplaceRepresentative
    (n : ℕ)
    (g : Section43CompactStrictPositiveTimeSource n) :
    ∃ Φ : SchwartzMap (Fin n → ℝ) ℂ,
      section43IteratedLaplaceRepresentative n g Φ
```

must not be proved by the old vague "coordinate induction" sketch.  The
implementation-ready route is the time-only analogue of the already compiled
production theorem
`exists_section43FourierLaplaceRepresentative_eq_integral_of_compact_orderedSupport_of_margin`.
The architecture is:

1. Build a time-only product cutoff.
2. Prove the raw multitime Laplace integral is smooth.
3. Prove its derivatives are rapidly decaying on the one-sided collar
   `{σ | ∀ i, -1 ≤ σ i}`.
4. Apply the compiled general constructor
   `schwartzMap_of_temperate_mul_rapid_on_derivSupport`.

Use these exact definitions:

```lean
def section43TimePositiveThickening (n : ℕ) (ε : ℝ) :
    Set (Fin n → ℝ) :=
  {σ | ∀ i : Fin n, -ε ≤ σ i}

noncomputable def section43TimePositiveCutoff (n : ℕ) :
    (Fin n → ℝ) → ℂ :=
  fun σ => ∏ i : Fin n, (SCV.smoothCutoff (σ i) : ℂ)

noncomputable def section43IteratedLaplaceRaw
    (n : ℕ) (g : Section43CompactStrictPositiveTimeSource n)
    (σ : Fin n → ℝ) : ℂ :=
  ∫ τ : Fin n → ℝ,
    Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) *
      g.f τ

noncomputable def section43IteratedLaplaceCutoffFun
    (n : ℕ) (g : Section43CompactStrictPositiveTimeSource n)
    (σ : Fin n → ℝ) : ℂ :=
  section43TimePositiveCutoff n σ *
    section43IteratedLaplaceRaw n g σ
```

The cutoff packet is a direct copy of the compiled
`section43PositiveEnergyCutoff` packet, with `section43QTime` replaced by the
coordinate projection `fun σ => σ i`:

```lean
theorem section43TimePositiveCutoff_eq_one_of_mem
    {σ : Fin n → ℝ} :
    σ ∈ section43TimePositiveRegion n →
      section43TimePositiveCutoff n σ = 1

theorem section43TimePositiveCutoff_eq_zero_of_time_le_neg_one
    {σ : Fin n → ℝ} {i : Fin n} :
    σ i ≤ -1 → section43TimePositiveCutoff n σ = 0

theorem section43TimePositiveCutoff_eq_zero_of_not_mem_thickening_one
    {σ : Fin n → ℝ} :
    σ ∉ section43TimePositiveThickening n 1 →
      section43TimePositiveCutoff n σ = 0

theorem section43TimePositiveCutoff_contDiff :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (section43TimePositiveCutoff n)

theorem section43TimePositiveCutoff_hasTemperateGrowth :
    Function.HasTemperateGrowth (section43TimePositiveCutoff n)

theorem section43TimePositiveCutoff_iteratedFDeriv_support_subset_thickening_one
    (r : ℕ) :
    ∀ σ : Fin n → ℝ,
      iteratedFDeriv ℝ r (section43TimePositiveCutoff n) σ ≠ 0 →
        σ ∈ section43TimePositiveThickening n 1
```

The proof uses only:

```lean
SCV.smoothCutoff_one_of_nonneg
SCV.smoothCutoff_zero_of_le_neg_one
SCV.smoothCutoff_contDiff
SCV.smoothCutoff_complex_hasTemperateGrowth
iteratedFDeriv_eq_zero_of_eventuallyEq_zero
```

For source geometry, isolate the compact-support consequences before doing
any differentiation:

```lean
theorem exists_positive_margin_of_compact_time_tsupport_subset_strictPositive
    (g : Section43CompactStrictPositiveTimeSource n) :
    ∃ δ, 0 < δ ∧
      tsupport (g.f : (Fin n → ℝ) → ℂ) ⊆
        {τ | ∀ i : Fin n, δ ≤ τ i}

theorem exists_time_closedBall_of_compact_tsupport
    (g : Section43CompactStrictPositiveTimeSource n) :
    ∃ R, 0 ≤ R ∧
      tsupport (g.f : (Fin n → ℝ) → ℂ) ⊆
        Metric.closedBall (0 : Fin n → ℝ) R
```

For the margin theorem, the Lean proof should use the compact set
`K := tsupport (g.f : (Fin n → ℝ) → ℂ)`.  For each coordinate `i`, the image
`(fun τ => τ i) '' K` is compact and contained in `Set.Ioi 0`; apply the
one-dimensional compact-positive margin argument to that image.  If
`Fin n` is empty, choose `δ = 1` and the coordinate condition is vacuous.  If
`Fin n` is nonempty, take the finite minimum of the coordinate margins and use
positivity of a finite minimum of positive numbers.  The closed-ball theorem
comes from `g.compact.isCompact.exists_bound_of_continuousOn` applied to
`fun τ => ‖τ‖`, followed by replacing the bound with `max bound 0`.

For smoothness, use the same integrated-candidate architecture already used in
`Section43FourierLaplaceCompactDifferentiation.lean`.  Define the candidate by
integrating the pointwise iterated derivative, rather than expanding all
finite words by hand:

```lean
noncomputable def section43IteratedLaplaceRaw_iteratedFDerivCandidate
    (n r : ℕ) (g : Section43CompactStrictPositiveTimeSource n)
    (σ : Fin n → ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin n → ℝ) ℂ :=
  ∫ τ : Fin n → ℝ,
    iteratedFDeriv ℝ r
      (fun σ' : Fin n → ℝ =>
        Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ' i : ℂ))) *
          g.f τ)
      σ
```

Then prove the following analogues of the compiled ordered-support theorems:

```lean
theorem integrable_section43IteratedLaplaceRaw_integrand_iteratedFDeriv_of_compact
    (n r : ℕ) (g : Section43CompactStrictPositiveTimeSource n)
    (σ : Fin n → ℝ) :
    Integrable
      (fun τ : Fin n → ℝ =>
        iteratedFDeriv ℝ r
          (fun σ' : Fin n → ℝ =>
            Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ' i : ℂ))) *
              g.f τ)
          σ)

theorem section43IteratedLaplaceRaw_iteratedFDerivCandidate_hasFDerivAt
    (n r : ℕ) (g : Section43CompactStrictPositiveTimeSource n)
    (σ : Fin n → ℝ) :
    HasFDerivAt
      (fun σ' : Fin n → ℝ =>
        section43IteratedLaplaceRaw_iteratedFDerivCandidate n r g σ')
      ((section43IteratedLaplaceRaw_iteratedFDerivCandidate n (r + 1) g σ).curryLeft)
      σ

theorem section43IteratedLaplaceRaw_iteratedFDeriv_eq_candidate
    (n r : ℕ) (g : Section43CompactStrictPositiveTimeSource n)
    (σ : Fin n → ℝ) :
    iteratedFDeriv ℝ r (section43IteratedLaplaceRaw n g) σ =
      section43IteratedLaplaceRaw_iteratedFDerivCandidate n r g σ

theorem section43IteratedLaplaceRaw_contDiff
    (n : ℕ) (g : Section43CompactStrictPositiveTimeSource n) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (section43IteratedLaplaceRaw n g)
```

The local dominated-convergence proof for
`section43IteratedLaplaceRaw_iteratedFDerivCandidate_hasFDerivAt` should be a
time-only copy of
`section43FourierLaplaceIntegral_iteratedFDerivCandidate_hasFDerivAt_of_compact_orderedSupport`:
use `hasFDerivAt_integral_of_dominated_of_fderiv_le`, the local ball
`Metric.closedBall σ 1`, and the compact time bound
`tsupport g.f ⊆ Metric.closedBall 0 R`.  The pointwise derivative
`HasFDerivAt` is obtained from smoothness of
`fun σ' => Complex.exp (-(∑ i, (τ i : ℂ) * (σ' i : ℂ))) * g.f τ`.

Lean-ready local-bound packet, 2026-04-18:

The time-only local domination theorem should not copy the spatial
derivative-word sum from the ordered-support Fourier-Laplace proof.  In the
present setting the σ-dependence is just the exponential of a continuous
linear functional, multiplied by the fixed scalar `g.f τ`.  The implementation
should first compile these helper lemmas:

```lean
noncomputable def section43TimeLaplaceLinearCLM
    (n : ℕ) (τ : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℂ

theorem section43TimeLaplaceLinearCLM_apply
    (n : ℕ) (τ σ : Fin n → ℝ) :
    section43TimeLaplaceLinearCLM n τ σ =
      -(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))

theorem norm_time_le_norm_add_one_of_mem_closedBall
    (n : ℕ) (σ σ' : Fin n → ℝ)
    (hσ' : σ' ∈ Metric.closedBall σ (1 : ℝ)) :
    ‖σ'‖ ≤ ‖σ‖ + 1

theorem norm_section43TimeLaplaceLinearCLM_le
    (n : ℕ) (τ : Fin n → ℝ) {R : ℝ}
    (hR_nonneg : 0 ≤ R)
    (hτ : τ ∈ Metric.closedBall (0 : Fin n → ℝ) R) :
    ‖section43TimeLaplaceLinearCLM n τ‖ ≤ ∑ _ : Fin n, R

theorem norm_exp_neg_timePair_le_local_time_closedBall
    (n : ℕ) (σ σ' τ : Fin n → ℝ)
    {R : ℝ} (hR_nonneg : 0 ≤ R)
    (hτ : τ ∈ Metric.closedBall (0 : Fin n → ℝ) R)
    (hσ' : σ' ∈ Metric.closedBall σ (1 : ℝ)) :
    ‖Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ' i : ℂ)))‖ ≤
      Real.exp (∑ _ : Fin n, R * (‖σ‖ + 1))

theorem exists_norm_bound_section43CompactStrictPositiveTimeSource_on_time_closedBall
    (n : ℕ) (g : Section43CompactStrictPositiveTimeSource n) (R : ℝ) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧
      ∀ τ ∈ Metric.closedBall (0 : Fin n → ℝ) R, ‖g.f τ‖ ≤ Cg

theorem section43IteratedLaplaceRaw_integrand_iteratedFDeriv_eq_zero_of_not_mem_tsupport
    (n r : ℕ) (g : Section43CompactStrictPositiveTimeSource n)
    {τ : Fin n → ℝ}
    (hτ : τ ∉ tsupport (g.f : (Fin n → ℝ) → ℂ)) :
    iteratedFDeriv ℝ r
      (fun σ : Fin n → ℝ =>
        Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) *
          g.f τ) =
      0
```

For the zero theorem, first use
`notMem_tsupport_iff_eventuallyEq` or `subset_tsupport` to prove `g.f τ = 0`,
then the σ-function is definitionally the zero function after `funext`, so
`iteratedFDeriv` reduces to `0`.

Then prove the actual local dominated derivative bound:

```lean
theorem section43IteratedLaplaceRaw_integrand_iteratedFDeriv_curryLeft_local_bound_of_compact
    (n r : ℕ) (g : Section43CompactStrictPositiveTimeSource n)
    (σ : Fin n → ℝ) :
    ∃ bound : (Fin n → ℝ) → ℝ,
      Integrable bound ∧
      ∀ᵐ τ, ∀ σ' ∈ Metric.closedBall σ (1 : ℝ),
        ‖(iteratedFDeriv ℝ (r + 1)
          (fun σ'' : Fin n → ℝ =>
            Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ'' i : ℂ))) *
              g.f τ)
          σ').curryLeft‖ ≤ bound τ
```

Proof transcript:

1. Choose `R ≥ 0` and
   `hR_supp : tsupport g.f ⊆ Metric.closedBall 0 R` from
   `exists_time_closedBall_of_compact_tsupport`.
2. Set `Kτ = Metric.closedBall (0 : Fin n → ℝ) R`.
3. Choose `Cg ≥ 0` bounding `‖g.f τ‖` on `Kτ`.
4. Let
   `Cexp = Real.exp (∑ _ : Fin n, R * (‖σ‖ + 1))` and
   `CL = ∑ _ : Fin n, R`.
5. Let
   `C = (r + 1).factorial * Cexp * CL ^ (r + 1) * Cg`.
6. Take `bound = Set.indicator Kτ (fun _ => C)`.  Integrability is
   `integrable_indicator_time_closedBall_const n R C`.
7. On `Kτ`, rewrite the scalar integrand as
   `(fun σ'' => Complex.exp (section43TimeLaplaceLinearCLM n τ σ''))`
   multiplied by the constant `g.f τ`.  Apply
   `iteratedFDeriv_smul_const_apply`,
   `norm_iteratedFDeriv_cexp_comp_clm_le`,
   `norm_section43TimeLaplaceLinearCLM_le`, the local exponential bound, and
   the source bound.
8. Off `Kτ`, `τ ∉ tsupport g.f` by `hR_supp`, so the whole pointwise
   derivative is zero by the zero theorem.

Production status, 2026-04-18: this local-bound packet is compiled in
`Section43FourierLaplaceTimeProduct.lean`.  The compiled theorem

```lean
section43IteratedLaplaceRaw_integrand_iteratedFDeriv_curryLeft_local_bound_of_compact
```

is now the exact time-only analogue needed by
`hasFDerivAt_integral_of_dominated_of_fderiv_le`.  The next missing proof-doc
item is not another bound; it is the measurability/integrability transcript for

```lean
integrable_section43IteratedLaplaceRaw_integrand_iteratedFDeriv_of_compact
```

The base scalar integrability theorem is already compiled as
`integrable_section43IteratedLaplaceRaw_integrand_of_compact`.  For the
successor case, reuse the local-bound theorem and prove the required
AEStronglyMeasurable fact by an explicit time-only continuity lemma for
`τ ↦ iteratedFDeriv ... σ`.  Do not introduce a wrapper theorem that assumes
measurability as a hypothesis; the measurability is part of this seam.

For rapid decay on the cutoff-derivative support, reuse the already compiled
time-only estimates:

```lean
norm_exp_neg_timePair_le_exp_thickened_margin_sum
exp_margin_sum_controls_thickened_time_polynomial
```

With `ε = 1`, `δ` from the strict-positive support margin, and `R` from the
compact closed-ball bound, they give:

```lean
theorem section43IteratedLaplaceRaw_iteratedFDeriv_rapid_on_timeThickening
    (n r s : ℕ) (g : Section43CompactStrictPositiveTimeSource n) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ σ ∈ section43TimePositiveThickening n 1,
        (1 + ‖σ‖) ^ s *
          ‖iteratedFDeriv ℝ r (section43IteratedLaplaceRaw n g) σ‖ ≤ C
```

The proof first rewrites the derivative by
`section43IteratedLaplaceRaw_iteratedFDeriv_eq_candidate`, bounds the pointwise
candidate by a compact-support integrable majorant, applies
`norm_exp_neg_timePair_le_exp_thickened_margin_sum`, and then absorbs the
remaining polynomial in `σ` using
`exp_margin_sum_controls_thickened_time_polynomial`.

Lean-ready rapid-decay transcript, 2026-04-18:

The time-only rapid proof is simpler than the ordered-support spatial proof.
Do not introduce derivative words.  For fixed `r,s`:

1. Rewrite
   `iteratedFDeriv ℝ r (section43IteratedLaplaceRaw n g) σ` by
   `section43IteratedLaplaceRaw_iteratedFDeriv_eq_candidate`.
2. Choose `δ > 0` from
   `exists_positive_margin_of_compact_time_tsupport_subset_strictPositive g`.
3. Choose `R ≥ 0` from `exists_time_closedBall_of_compact_tsupport g`.
4. Choose `Cg ≥ 0` bounding `‖g.f τ‖` on `Metric.closedBall 0 R`.
5. Let
   `CL = ∑ _ : Fin n, R`,
   `Cderiv = r.factorial * CL ^ r * Cg`, and
   `Kτ = Metric.closedBall (0 : Fin n → ℝ) R`.
6. Let
   `M = ∫ τ, Set.indicator Kτ (fun _ => Cderiv) τ`.
   This is finite by `integrable_indicator_time_closedBall_const` and
   nonnegative by `integral_nonneg`.
7. For `σ ∈ section43TimePositiveThickening n 1`, define
   `Eσ =
      Real.exp (∑ _ : Fin n, R * 1) *
        Real.exp (-(δ * ∑ i : Fin n, (σ i + 1)))`.
8. Pointwise in `τ`, prove
   `‖G σ τ‖ ≤ Eσ * Set.indicator Kτ (fun _ => Cderiv) τ`, where `G` is the
   integrand defining
   `section43IteratedLaplaceRaw_iteratedFDerivCandidate n r g σ`.
9. Inside `Kτ`, if `τ ∉ tsupport g.f`, the derivative is zero by
   `section43IteratedLaplaceRaw_integrand_iteratedFDeriv_eq_zero_of_not_mem_tsupport`.
   If `τ ∈ tsupport g.f`, use the support margin for `δ ≤ τ i`, the closed-ball
   bound `‖τ‖ ≤ R`, the collar hypothesis `-1 ≤ σ i`, and
   `norm_exp_neg_timePair_le_exp_thickened_margin_sum`.
10. The derivative factor is bounded by
    `norm_section43IteratedLaplaceRaw_integrand_iteratedFDeriv_le`,
    `norm_section43TimeLaplaceLinearCLM_le`, and the source bound `Cg`.
11. Integrating gives
    `‖candidate σ‖ ≤ Eσ * M`.
12. Apply
    `exp_margin_sum_controls_thickened_time_polynomial
       (n := n) (δ := δ) (ε := 1) (R := R) ... s`
    to get `Ct` with `(1 + ‖σ‖)^s * Eσ ≤ Ct`.
13. The final rapid constant is `C = Ct * M`.

The final representative is then:

```lean
noncomputable def section43IteratedLaplaceSchwartzRepresentative
    (n : ℕ) (g : Section43CompactStrictPositiveTimeSource n) :
    SchwartzMap (Fin n → ℝ) ℂ :=
  schwartzMap_of_temperate_mul_rapid_on_derivSupport
    (χ := section43TimePositiveCutoff n)
    (F := section43IteratedLaplaceRaw n g)
    (S := section43TimePositiveThickening n 1)
    (section43TimePositiveCutoff_hasTemperateGrowth n)
    (fun r σ hne =>
      section43TimePositiveCutoff_iteratedFDeriv_support_subset_thickening_one
        (n := n) r σ hne)
    (section43IteratedLaplaceRaw_contDiff n g)
    (by
      intro r s
      exact section43IteratedLaplaceRaw_iteratedFDeriv_rapid_on_timeThickening
        n r s g)

theorem section43IteratedLaplaceSchwartzRepresentative_apply_of_mem
    (g : Section43CompactStrictPositiveTimeSource n)
    {σ : Fin n → ℝ} :
    σ ∈ section43TimePositiveRegion n →
      section43IteratedLaplaceSchwartzRepresentative n g σ =
        section43IteratedLaplaceRaw n g σ

theorem exists_section43IteratedLaplaceRepresentative
    (n : ℕ) (g : Section43CompactStrictPositiveTimeSource n) :
    ∃ Φ : SchwartzMap (Fin n → ℝ) ℂ,
      section43IteratedLaplaceRepresentative n g Φ
```

The last theorem is just
`⟨section43IteratedLaplaceSchwartzRepresentative n g, ...⟩`, unfolding
`section43IteratedLaplaceRepresentative`, rewriting by
`section43IteratedLaplaceSchwartzRepresentative_apply_of_mem`, and unfolding
`section43IteratedLaplaceRaw`.

Production status, 2026-04-18: the arbitrary-source representative package is
compiled in `Section43FourierLaplaceTimeProduct.lean`, including

```lean
integrable_section43IteratedLaplaceRaw_integrand_iteratedFDeriv_of_compact
section43IteratedLaplaceRaw_iteratedFDerivCandidate_hasFDerivAt
section43IteratedLaplaceRaw_iteratedFDeriv_eq_candidate
section43IteratedLaplaceRaw_contDiff
section43IteratedLaplaceRaw_iteratedFDeriv_rapid_on_timeThickening
section43IteratedLaplaceSchwartzRepresentative
exists_section43IteratedLaplaceRepresentative
section43IteratedLaplaceCompactTransform
section43IteratedLaplaceCompactTransform_productSource
```

The next implementation step should not continue growing
`Section43FourierLaplaceTimeProduct.lean`; it is now close to the 2000-line
support-file limit.  Start a small companion file for the finite-product dense
preimage theorem:

```lean
theorem dense_section43IteratedLaplaceCompactTransform_preimage
    (n : ℕ) :
    Dense
      ((section43TimePositiveQuotientMap n) ⁻¹'
        Set.range (section43IteratedLaplaceCompactTransform n))
```

This theorem should use:

```lean
dense_section43OneSidedLaplaceCompactTransform1D_preimage
section43_timeProductTensor_span_dense_of_factor_dense
section43IteratedLaplaceCompactTransform_productSource
section43TimePositiveQuotientMap_eq_of_eqOn_region
```

Production status, 2026-04-18: the low-risk first half of this package is
compiled in `Section43FourierLaplaceTimeProduct.lean`:

```lean
section43TimePositiveThickening
section43TimePositiveCutoff
section43TimePositiveCutoff_eq_one_of_mem
section43TimePositiveCutoff_eq_zero_of_time_le_neg_one
section43TimePositiveCutoff_eq_zero_of_not_mem_thickening_one
section43TimePositiveCutoff_contDiff
section43TimePositiveCutoff_hasTemperateGrowth
section43TimePositiveCutoff_iteratedFDeriv_eq_zero_of_not_mem_thickening_one
section43TimePositiveCutoff_iteratedFDeriv_support_subset_thickening_one
exists_positive_margin_of_isCompact_subset_Ioi
exists_positive_margin_of_compact_time_tsupport_subset_strictPositive
exists_time_closedBall_of_compact_tsupport
continuous_cmlm_apply_time
section43IteratedLaplaceRaw
section43IteratedLaplaceCutoffFun
section43IteratedLaplaceCutoffFun_eq_raw_of_mem
contDiff_section43IteratedLaplaceRaw_integrand_sigma
hasFDerivAt_section43IteratedLaplaceRaw_integrand_iteratedFDeriv_curryLeft
section43IteratedLaplaceRaw_iteratedFDerivCandidate
```

The remaining implementation frontier in this package is now exactly the
integrated derivative candidate estimates and their consequences:

```lean
integrable_section43IteratedLaplaceRaw_integrand_iteratedFDeriv_of_compact
section43IteratedLaplaceRaw_iteratedFDerivCandidate_hasFDerivAt
section43IteratedLaplaceRaw_iteratedFDeriv_eq_candidate
section43IteratedLaplaceRaw_contDiff
section43IteratedLaplaceRaw_iteratedFDeriv_rapid_on_timeThickening
section43IteratedLaplaceSchwartzRepresentative
exists_section43IteratedLaplaceRepresentative
```

### Layer 2B: Product Sources

For factorwise compact positive sources, define the product source:

```lean
noncomputable def section43TimeProductSource
    {n : ℕ} (gs : Fin n → Section43CompactPositiveTimeSource1D) :
    Section43CompactStrictPositiveTimeSource n :=
{ f := section43TimeProductTensor (fun i => (gs i).f)
  positive := ...
  compact := ... }
```

Support proof transcript:

1. If
   `x ∈ tsupport ((section43TimeProductTensor fun i => (gs i).f) :
      (Fin n → ℝ) → ℂ)`,
   then for every `i`, `x i ∈ tsupport ((gs i).f : ℝ → ℂ)`.
2. Prove the contrapositive: if `x i` is outside the one-variable tsupport,
   choose a neighborhood of `x i` on which `(gs i).f` is zero; the cylinder
   neighborhood in `Fin n → ℝ` makes the product tensor zero.
3. Apply `(gs i).positive` to get `0 < x i`.
4. Compactness follows from support containment in the finite product of the
   compact one-variable tsupports.  In Lean this is:
   `HasCompactSupport.of_support_subset_isCompact`,
   `subset_tsupport`, and `isCompact_univ_pi (fun i => (gs i).compact.isCompact)`.

Needed helper theorem names:

```lean
theorem tsupport_section43TimeProductTensor_subset_pi_tsupport
    (gs : Fin n → Section43CompactPositiveTimeSource1D) :
    tsupport
      ((section43TimeProductTensor (fun i => (gs i).f) :
          SchwartzMap (Fin n → ℝ) ℂ) : (Fin n → ℝ) → ℂ)
      ⊆ {x | ∀ i, x i ∈ tsupport ((gs i).f : ℝ → ℂ)}

theorem hasCompactSupport_section43TimeProductTensor
    (gs : Fin n → Section43CompactPositiveTimeSource1D) :
    HasCompactSupport
      ((section43TimeProductTensor (fun i => (gs i).f) :
          SchwartzMap (Fin n → ℝ) ℂ) : (Fin n → ℝ) → ℂ)

noncomputable def section43TimeProductSource
    {n : ℕ} (gs : Fin n → Section43CompactPositiveTimeSource1D) :
    Section43CompactStrictPositiveTimeSource n
```

For `n = 0`, the positive condition is vacuous and compact support is compact
support on the one-point space.  Keep the same theorem statements; the finite
product compactness proof should handle this case.

The product-source support packet is now compiled in
`Section43FourierLaplaceTimeProduct.lean`.  The compactness proof uses the
finite product set

```lean
Set.pi Set.univ (fun i => tsupport ((gs i).f : ℝ → ℂ))
```

and does not require any OS or Wightman input.

The product-source representative theorem is now compiled:

```lean
theorem section43TimeProductTensor_oneSidedLaplaceRepresentative
    {n : ℕ} (gs : Fin n → Section43CompactPositiveTimeSource1D) :
    section43IteratedLaplaceRepresentative n (section43TimeProductSource gs)
      (section43TimeProductTensor
        (fun i : Fin n =>
          section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))

theorem exists_section43IteratedLaplaceRepresentative_productSource
    {n : ℕ} (gs : Fin n → Section43CompactPositiveTimeSource1D) :
    ∃ Φ : SchwartzMap (Fin n → ℝ) ℂ,
      section43IteratedLaplaceRepresentative n (section43TimeProductSource gs) Φ
```

After the arbitrary-source compact transform is defined, prove the transform
compatibility:

```lean
theorem section43IteratedLaplaceCompactTransform_productSource
    {n : ℕ} (gs : Fin n → Section43CompactPositiveTimeSource1D) :
    section43IteratedLaplaceCompactTransform n
        (section43TimeProductSource gs) =
      section43TimePositiveQuotientMap n
        (section43TimeProductTensor
          (fun i =>
            section43OneSidedLaplaceSchwartzRepresentative1D (gs i)))
```

Proof transcript:

1. Apply `section43IteratedLaplaceCompactTransform_eq_quotient` with
   `Φ := section43TimeProductTensor
      (fun i => section43OneSidedLaplaceSchwartzRepresentative1D (gs i))`.
2. The representative proof argument is the compiled theorem
   `section43TimeProductTensor_oneSidedLaplaceRepresentative gs`.
3. No further analysis is needed at this stage; all pointwise analysis has
   already been compiled in
   `section43TimeProductTensor_oneSidedLaplaceRepresentative_eq_integral`.

For reference, the pointwise theorem proved the following finite-product
calculation.  The multitime representative integral for
`section43TimeProductSource gs` has integrand

```lean
fun τ =>
  ∏ i,
    Complex.exp (-((τ i : ℂ) * (σ i : ℂ))) * (gs i).f (τ i)
```

after rewriting the exponential of a finite sum as a product with
`Complex.exp_sum`.  The exact Mathlib theorem used for the finite-product
Fubini calculation is:

```lean
MeasureTheory.integral_fintype_prod_volume_eq_prod
```

In the compiled product-source theorem, it gives

```lean
theorem section43TimeProductSource_integral_eq_product_raw
    {n : ℕ} (gs : Fin n → Section43CompactPositiveTimeSource1D)
    (σ : Fin n → ℝ) :
    (∫ τ : Fin n → ℝ,
      Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) *
        (section43TimeProductSource gs).f τ) =
      ∏ i : Fin n,
        ∫ t : ℝ, Complex.exp (-(t : ℂ) * (σ i : ℂ)) * (gs i).f t
```

The proof rewrites
`Complex.exp (-(∑ i, (τ i : ℂ) * (σ i : ℂ)))` as
`∏ i, Complex.exp (-(τ i : ℂ) * (σ i : ℂ))` using
`Complex.exp_sum`, `Finset.sum_neg_distrib`, and a per-coordinate `ring`.
It then rewrites each factor by
`section43OneSidedLaplaceSchwartzRepresentative1D_apply` and
`section43OneSidedLaplaceCutoffFun_eq_raw_of_nonneg`, finishing with
`SchwartzMap.productTensor_apply`.

The pointwise product-source representative identity on the closed positive
orthant is also compiled:

```lean
theorem section43TimeProductTensor_oneSidedLaplaceRepresentative_eq_integral
    {n : ℕ} (gs : Fin n → Section43CompactPositiveTimeSource1D)
    {σ : Fin n → ℝ} (hσ : σ ∈ section43TimePositiveRegion n) :
    (section43TimeProductTensor
      (fun i : Fin n => section43OneSidedLaplaceSchwartzRepresentative1D (gs i)) :
        SchwartzMap (Fin n → ℝ) ℂ) σ =
    ∫ τ : Fin n → ℝ,
      Complex.exp (-(∑ i : Fin n, (τ i : ℂ) * (σ i : ℂ))) *
        (section43TimeProductSource gs).f τ
```

No bespoke finite-`Fin n` induction is needed here: the existing
`MeasureTheory.integral_fintype_prod_volume_eq_prod` theorem is exactly the
finite product-integral statement.

The factorwise preimage theorem is then short:

```lean
def section43OneSidedCompactPreimageSet :
    Set (SchwartzMap ℝ ℂ) :=
  section43PositiveEnergyQuotientMap1D ⁻¹'
    Set.range section43OneSidedLaplaceCompactTransform1D

def section43IteratedCompactPreimageSet (n : ℕ) :
    Set (SchwartzMap (Fin n → ℝ) ℂ) :=
  section43TimePositiveQuotientMap n ⁻¹'
    Set.range (section43IteratedLaplaceCompactTransform n)

theorem section43TimeProductTensor_mem_iteratedCompactPreimageSet
    {n : ℕ} {fs : Fin n → SchwartzMap ℝ ℂ}
    (hfs : ∀ i : Fin n, fs i ∈ section43OneSidedCompactPreimageSet) :
    section43TimeProductTensor fs ∈
      section43IteratedCompactPreimageSet n
```

Proof transcript:

1. Choose `gs i` from `hfs i`, so
   `section43PositiveEnergyQuotientMap1D (fs i) =
    section43OneSidedLaplaceCompactTransform1D (gs i)`.
2. Convert each quotient equality into equality on `Set.Ici 0` using the
   one-variable quotient extensionality theorem
   `eqOn_nonneg_of_section43PositiveEnergyQuotientMap1D_eq`.
3. On `σ ∈ section43TimePositiveRegion n`, multiply those coordinatewise
   equalities to show

```lean
section43TimeProductTensor fs σ =
section43TimeProductTensor
  (fun i => section43OneSidedLaplaceSchwartzRepresentative1D (gs i)) σ
```

4. Apply `section43IteratedLaplaceCompactTransform_productSource`.

### Layer 2C: Dense Preimage Theorem

Main theorem:

```lean
theorem dense_section43IteratedLaplaceCompactTransform_preimage
    (n : ℕ) :
    Dense
      ((section43TimePositiveQuotientMap n) ⁻¹'
        Set.range (section43IteratedLaplaceCompactTransform n))
```

Proof transcript:

1. Let

```lean
S1 := section43OneSidedCompactPreimageSet
Sn := section43IteratedCompactPreimageSet n
```

2. `S1` is dense by the compiled theorem
   `dense_section43OneSidedLaplaceCompactTransform1D_preimage`.
3. `Sn` is a submodule carrier:

```lean
let Ln := section43IteratedLaplaceCompactTransformLinearMap n
let qn := section43TimePositiveQuotientMap n
let Mn : Submodule ℂ (Section43TimePositiveComponent n) := LinearMap.range Ln
let SnSub : Submodule ℂ (SchwartzMap (Fin n → ℝ) ℂ) :=
  Mn.comap qn.toLinearMap
```

   Prove `Sn = (SnSub : Set _)` by extensionality.
4. Apply
   `section43_timeProductTensor_span_dense_of_factor_dense
     (hS := dense_section43OneSidedLaplaceCompactTransform1D_preimage) n`.
5. The product-tensor generating set is contained in `Sn` by
   `section43TimeProductTensor_mem_iteratedCompactPreimageSet`.
6. Since `SnSub` is a submodule, its carrier contains the span of those product
   tensors.
7. A dense subset contained in `Sn` proves `Dense Sn`.

This proof handles `n = 0` automatically if the product-source and
product-integral lemmas handle the empty finite product.  Do not split the main
density theorem unless Lean's finite-product integral API forces a local
`n = 0` helper.

Production status, 2026-04-18: the finite-product dense-preimage package is
compiled in
`OSReconstruction/Wightman/Reconstruction/WickRotation/Section43FourierLaplaceTimeProductDensity.lean`.
It proves the missing linearity rather than assuming that the plain function
range is a submodule:

```lean
eqOn_nonneg_of_section43PositiveEnergyQuotientMap1D_eq
section43IteratedLaplaceRaw_add
section43IteratedLaplaceRaw_smul
section43IteratedLaplaceRepresentative_add
section43IteratedLaplaceRepresentative_smul
section43IteratedLaplaceCompactTransform_map_add
section43IteratedLaplaceCompactTransform_map_smul
section43IteratedLaplaceCompactTransformLinearMap
section43TimeProductTensor_mem_iteratedLaplaceCompactTransform_preimage
dense_section43IteratedLaplaceCompactTransform_preimage
denseRange_section43IteratedLaplaceCompactTransformLinearMap
```

The proof uses the one-variable dense preimage theorem, the compiled
factor-dense product-tensor theorem, quotient extensionality on each
coordinate, and the product-source transform identity.  No new axioms,
wrappers, or placeholders are used.  The next proof-doc frontier is Layer 3:
make the spatial-Fourier transport from
`SchwartzMap (Fin n → ℝ) ℂ` to `SchwartzNPoint d n` implementation-ready
before attempting production Lean.

## Layer 3: Add Spatial Fourier Transform

Layer-3 correction, 2026-04-18:

The phrase "compose with the spatial Fourier transform" is not by itself an
implementation-ready proof.  The final source type requires compact support in
spacetime.  Therefore the dense spatial factors cannot be arbitrary inverse
Fourier transforms: `FourierTransform.fourierInv χ` is generally not compactly
supported.  The correct dense set on the spatial-frequency side is the Fourier
image of compactly supported spatial Schwartz sources.

Definitions:

```lean
abbrev Section43SpatialSpace (d n : ℕ) [NeZero d] :=
  EuclideanSpace ℝ (Fin n × Fin d)

def Section43SpatialCompactSource (d n : ℕ) [NeZero d] :=
  {κ : SchwartzMap (Section43SpatialSpace d n) ℂ //
    HasCompactSupport (κ : Section43SpatialSpace d n → ℂ)}

def section43SpatialFourierCompactRange
    (d n : ℕ) [NeZero d] :
    Set (SchwartzMap (Section43SpatialSpace d n) ℂ) :=
  Set.range fun κ : Section43SpatialCompactSource d n =>
    SchwartzMap.fourierTransformCLM ℂ κ.1

theorem dense_section43SpatialFourierCompactRange
    (d n : ℕ) [NeZero d] :
    Dense (section43SpatialFourierCompactRange d n)

structure Section43CompactStrictPositiveTimeSpatialSource
    (d n : ℕ) [NeZero d] where
  f : SchwartzNPoint d n
  positive :
    tsupport (f : NPointDomain d n → ℂ) ⊆
      {x | ∀ i : Fin n, 0 < section43QTime (d := d) (n := n) x i}
  compact : HasCompactSupport (f : NPointDomain d n → ℂ)

def section43TimeLaplaceSpatialFourierRepresentative
    (d n : ℕ) [NeZero d]
    (g : Section43CompactStrictPositiveTimeSpatialSource d n)
    (Φ : SchwartzNPoint d n) : Prop :=
  ∀ q : NPointDomain d n, q ∈ section43PositiveEnergyRegion d n →
    Φ q =
      ∫ τ : Fin n → ℝ,
        Complex.exp
          (-(∑ i : Fin n,
            (τ i : ℂ) * (section43QTime (d := d) (n := n) q i : ℂ))) *
          partialFourierSpatial_fun
            (d := d) (n := n) g.f
            (τ, section43QSpatial (d := d) (n := n) q)
```

The proof of `dense_section43SpatialFourierCompactRange` is a required
subpacket, not a handwave:

1. Prove compactly supported Schwartz functions are dense on
   `Section43SpatialSpace d n`.  Transport the compiled theorem
   `SchwartzMap.dense_hasCompactSupport` from
   `SchwartzMap (Fin (n * d) → ℝ) ℂ` through the continuous linear equivalence
   ```lean
   section43SpatialFlatCLE (d n) :
     Section43SpatialSpace d n ≃L[ℝ] (Fin (n * d) → ℝ)
   ```
   built from `EuclideanSpace.equiv (Fin n × Fin d) ℝ` and
   `finProdFinEquiv`.
2. Compact support is preserved by this transport because a continuous linear
   equivalence maps compact sets to compact sets and pulls support back along
   the inverse map.
3. For any target spatial-frequency Schwartz function `χ`, set
   `κ₀ := FourierTransform.fourierInv χ`.  Approximate `κ₀` by compactly
   supported spatial Schwartz functions `κ_j`.
4. Continuity of `SchwartzMap.fourierTransformCLM ℂ` gives
   `𝓕 κ_j → 𝓕 κ₀`, and
   `FourierTransform.fourier_fourierInv_eq` identifies the limit with `χ`.

The time-spatial product tensors used in the density proof are:

```lean
noncomputable def section43TimeSpatialTensor
    (d n : ℕ) [NeZero d]
    (Φ : SchwartzMap (Fin n → ℝ) ℂ)
    (χ : SchwartzMap (Section43SpatialSpace d n) ℂ) :
    SchwartzNPoint d n
```

Lean construction transcript for `section43TimeSpatialTensor`:

1. Transport the spatial factor through
   `section43SpatialFlatCLE d n` to
   `SchwartzMap (Fin (n * d) → ℝ) ℂ`.
2. Use `SchwartzMap.tensorProduct Φ χflat` to obtain a Schwartz function on
   `Fin (n + n * d) → ℝ`.
3. Transport that function back through the continuous linear equivalence
   between `Fin (n + n*d) → ℝ` and
   `(Fin n → ℝ) × Section43SpatialSpace d n`, then through
   `nPointTimeSpatialSchwartzCLE d n`.
4. Its pointwise formula must be recorded as a simp theorem:
   ```lean
   theorem section43TimeSpatialTensor_apply
       (Φ : SchwartzMap (Fin n → ℝ) ℂ)
       (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
       (q : NPointDomain d n) :
       section43TimeSpatialTensor d n Φ χ q =
         Φ (section43QTime (d := d) (n := n) q) *
         χ (section43QSpatial (d := d) (n := n) q)
   ```

The restricted product-tensor density theorem needed here is:

```lean
theorem dense_section43TimeSpatialTensor_span_of_factor_dense
    (d n : ℕ) [NeZero d]
    {St : Set (SchwartzMap (Fin n → ℝ) ℂ)}
    {Sx : Set (SchwartzMap (Section43SpatialSpace d n) ℂ)}
    (hSt : Dense St) (hSx : Dense Sx) :
    Dense
      (((Submodule.span ℂ
        {F : SchwartzNPoint d n |
          ∃ Φ ∈ St, ∃ χ ∈ Sx,
            F = section43TimeSpatialTensor d n Φ χ}) :
        Submodule ℂ (SchwartzNPoint d n)) :
        Set (SchwartzNPoint d n))
```

Proof transcript:

1. First prove the unrestricted simple-tensor span is dense by transporting
   `productTensor_span_dense 0 (n + n*d)` through the same finite-dimensional
   flattening equivalences.  This is the two-factor analogue of
   `section43_timeProductTensor_span_dense`.
2. Let `D := St ×ˢ Sx`.  `Dense D` follows from `Dense.prod hSt hSx` or the
   corresponding product-filter theorem.
3. The map `(Φ, χ) ↦ section43TimeSpatialTensor d n Φ χ` is continuous.  Prove
   this by transporting `SchwartzMap.tensorProduct_continuous` through the
   finite-dimensional equivalences.
4. As in `section43_timeProductTensor_span_dense_of_factor_dense`, the closure
   of the restricted span contains every unrestricted simple tensor; since the
   unrestricted span is dense, the restricted span is dense.

Production status, 2026-04-18: the product-space half of Layer 3 is now
compiled in
`OSReconstruction/Wightman/Reconstruction/WickRotation/Section43FourierLaplaceSpatialDensity.lean`.
The compiled declarations deliberately stop before the final
`SchwartzNPoint d n` transport:

```lean
Section43SpatialSpace
section43SpatialFlatCLE
section43SpatialFlatSchwartzCLE
Section43SpatialCompactSource
dense_section43Spatial_hasCompactSupport
section43SpatialFourierCompactRange
dense_section43SpatialFourierCompactRange
Section43TimeSpatialSpace
section43TimeSpatialFlatCLE
section43TimeSpatialFlatCLE_splitFirst
section43TimeSpatialFlatCLE_splitLast
section43TimeSpatialTensor
section43TimeSpatialTensor_apply
dense_section43_flatBlockTensor_span
dense_section43TimeSpatialTensor_span
dense_section43TimeSpatialTensor_span_of_factor_dense
dense_section43TimeSpatialTensor_span_compactLaplace_spatialFourier
```

The final theorem above uses
`dense_section43IteratedLaplaceCompactTransform_preimage n` for the finite-time
factor and `dense_section43SpatialFourierCompactRange d n` for the spatial
factor.  It proves density of finite sums of tensors whose time factor is in
the compact-Laplace positive-time preimage and whose spatial factor is the
Fourier transform of a compact spatial source.  No new axioms, wrappers,
`sorry`s, or heartbeat overrides are used.

Important boundary: the compiled `section43TimeSpatialTensor` currently has
codomain
`SchwartzMap ((Fin n → ℝ) × Section43SpatialSpace d n) ℂ`, not
`SchwartzNPoint d n`.  The next Lean step is to transport this packet through
`nPointTimeSpatialSchwartzCLE` and prove the transported pointwise formula in
terms of `section43QTime` and `section43QSpatial`.  Only after that transport
should the compact spacetime product source and the
`partialFourierSpatial_fun` factorization be implemented.

Production update, 2026-04-18: the `SchwartzNPoint d n` transport is now also
compiled in the same companion file:

```lean
section43NPointTimeSpatialTensor
section43NPointTimeSpatialTensor_apply
dense_section43NPointTimeSpatialTensor_span_of_factor_dense
dense_section43NPointTimeSpatialTensor_span_compactLaplace_spatialFourier
```

The remaining Layer-3 implementation seam is therefore no longer density
transport.  It is the source-side construction and Fourier-slice
identification:

```lean
section43TimeSpatialProductSource
partialFourierSpatial_fun_section43TimeSpatialProductSource
```

The source attached to a restricted tensor is:

```lean
noncomputable def section43TimeSpatialProductSource
    (d n : ℕ) [NeZero d]
    (g : Section43CompactStrictPositiveTimeSource n)
    (κ : Section43SpatialCompactSource d n) :
    Section43CompactStrictPositiveTimeSpatialSource d n
```

Construction and obligations:

1. In `(τ, η)` variables the underlying Schwartz function is
   `g.f τ * κ.1 η`, transported through `nPointTimeSpatialSchwartzCLE`.
2. Strict positive-time support should be proved by the following explicit
   local lemma, using the compiled pointwise formula for the transported
   tensor:
   ```lean
   theorem tsupport_section43NPointTimeSpatialTensor_subset_time_preimage
       (d n : ℕ) [NeZero d]
       (φ : SchwartzMap (Fin n → ℝ) ℂ)
       (χ : SchwartzMap (Section43SpatialSpace d n) ℂ) :
       tsupport
         ((section43NPointTimeSpatialTensor d n φ χ :
             SchwartzNPoint d n) : NPointDomain d n → ℂ)
         ⊆
       (section43QTime (d := d) (n := n)) ⁻¹'
         tsupport (φ : (Fin n → ℝ) → ℂ)
   ```
   Proof skeleton:
   ```lean
   intro q hq
   have hfun :
       (((section43NPointTimeSpatialTensor d n φ χ :
           SchwartzNPoint d n) : NPointDomain d n → ℂ)) =
         fun q : NPointDomain d n =>
           φ (section43QTime (d := d) (n := n) q) *
             χ (section43QSpatial (d := d) (n := n) q) := by
     funext q
     simp
   have hprod :
       q ∈ tsupport
         (fun q : NPointDomain d n =>
           φ (section43QTime (d := d) (n := n) q) *
             χ (section43QSpatial (d := d) (n := n) q)) := by
     simpa [hfun] using hq
   have ht_pullback :
       q ∈ tsupport
         (fun q : NPointDomain d n =>
           φ (section43QTime (d := d) (n := n) q)) :=
     (tsupport_mul_subset_left
       (f := fun q : NPointDomain d n =>
         φ (section43QTime (d := d) (n := n) q))
       (g := fun q : NPointDomain d n =>
         χ (section43QSpatial (d := d) (n := n) q))) hprod
   exact
     (tsupport_comp_subset_preimage
       (φ : (Fin n → ℝ) → ℂ)
       (f := section43QTime (d := d) (n := n))
       (by simpa [section43QTimeCLM_apply] using
         (section43QTimeCLM d n).continuous)) ht_pullback
   ```
   Then `positive` is:
   ```lean
   intro q hq i
   exact g.positive
     (tsupport_section43NPointTimeSpatialTensor_subset_time_preimage
       d n g.f κ.1 hq) i
   ```
3. Compact support should not be attempted by taking a generic preimage of a
   compact set.  The safe Lean route is to work with ordinary `support`, place
   it inside the image of a compact product under the inverse time/spatial
   homeomorphism, and use `HasCompactSupport.of_support_subset_isCompact`.
   The helper lemma should be:
   ```lean
   theorem hasCompactSupport_section43NPointTimeSpatialTensor
       (d n : ℕ) [NeZero d]
       (φ : SchwartzMap (Fin n → ℝ) ℂ)
       (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
       (hφ : HasCompactSupport (φ : (Fin n → ℝ) → ℂ))
       (hχ : HasCompactSupport (χ : Section43SpatialSpace d n → ℂ)) :
       HasCompactSupport
         ((section43NPointTimeSpatialTensor d n φ χ :
             SchwartzNPoint d n) : NPointDomain d n → ℂ)
   ```
   Proof skeleton:
   ```lean
   let e := nPointTimeSpatialCLE (d := d) n
   let K : Set (NPointDomain d n) :=
     e.symm '' (tsupport (φ : (Fin n → ℝ) → ℂ) ×ˢ
       tsupport (χ : Section43SpatialSpace d n → ℂ))
   have hKcompact : IsCompact K := by
     exact (hφ.isCompact.prod hχ.isCompact).image e.symm.continuous
   refine HasCompactSupport.of_support_subset_isCompact hKcompact ?_
   intro q hq
   rw [Function.mem_support] at hq
   have hφq : φ (section43QTime (d := d) (n := n) q) ≠ 0 := by
     intro hzero
     apply hq
     simp [section43NPointTimeSpatialTensor_apply, hzero]
   have hχq : χ (section43QSpatial (d := d) (n := n) q) ≠ 0 := by
     intro hzero
     apply hq
     simp [section43NPointTimeSpatialTensor_apply, hzero]
   refine ⟨(section43QTime (d := d) (n := n) q,
       section43QSpatial (d := d) (n := n) q), ?_, ?_⟩
   · exact ⟨subset_tsupport _ (Function.mem_support.mpr hφq),
       subset_tsupport _ (Function.mem_support.mpr hχq)⟩
   · simp [e, section43QTime, section43QSpatial]
   ```
4. The fixed-time slice should be separated from the Fourier theorem:
   ```lean
   theorem partialEval₂_section43TimeSpatialProductSource
       (d n : ℕ) [NeZero d]
       (g : Section43CompactStrictPositiveTimeSource n)
       (κ : Section43SpatialCompactSource d n)
       (τ : Fin n → ℝ) :
       SchwartzMap.partialEval₂
         (nPointSpatialTimeSchwartzCLE (d := d) (n := n)
           (section43TimeSpatialProductSource d n g κ).f) τ =
       g.f τ • κ.1
   ```
   Proof skeleton:
   ```lean
   ext η
   change
     nPointSpatialTimeSchwartzCLE (d := d) (n := n)
       (section43TimeSpatialProductSource d n g κ).f (η, τ) =
     (g.f τ • κ.1) η
   rw [nPointSpatialTimeSchwartzCLE_apply]
   change
     nPointTimeSpatialSchwartzCLE (d := d) (n := n)
       (section43NPointTimeSpatialTensor d n g.f κ.1) (τ, η) =
     (g.f τ • κ.1) η
   change section43TimeSpatialTensor d n g.f κ.1 (τ, η) =
     (g.f τ • κ.1) η
   simp [smul_eq_mul]
   ```
   The orientation check is essential: `partialEval₂` fixes the second
   coordinate of the spatial-time Schwartz map, so
   `nPointSpatialTimeSchwartzCLE_apply` rewrites `(η, τ)` to the
   time-spatial value `(τ, η)`.
5. The spatial Fourier slice factorizes:
   ```lean
   theorem partialFourierSpatial_fun_section43TimeSpatialProductSource
       (g : Section43CompactStrictPositiveTimeSource n)
       (κ : Section43SpatialCompactSource d n)
       (τ : Fin n → ℝ) (ξ : Section43SpatialSpace d n) :
       partialFourierSpatial_fun
         (d := d) (n := n)
         (section43TimeSpatialProductSource d n g κ).f
         (τ, ξ) =
       g.f τ * (SchwartzMap.fourierTransformCLM ℂ κ.1) ξ
   ```
   Proof skeleton:
   ```lean
   rw [partialFourierSpatial_fun]
   change
     (SchwartzMap.fourierTransformCLM ℂ
       (SchwartzMap.partialEval₂
         (nPointSpatialTimeSchwartzCLE (d := d) (n := n)
           (section43TimeSpatialProductSource d n g κ).f) τ)) ξ =
       g.f τ * (SchwartzMap.fourierTransformCLM ℂ κ.1) ξ
   rw [partialEval₂_section43TimeSpatialProductSource]
   rw [(SchwartzMap.fourierTransformCLM ℂ).map_smul]
   simp [smul_eq_mul]
   ```
   This avoids manual Fourier-integral normalization.

Main theorem:

```lean
theorem dense_section43TimeLaplaceSpatialFourier_compact_preimage
    (d n : ℕ) [NeZero d] :
    Dense
      {Φ : SchwartzNPoint d n |
        ∃ (g : Section43CompactStrictPositiveTimeSpatialSource d n)
          (Ψ : SchwartzNPoint d n),
          section43TimeLaplaceSpatialFourierRepresentative d n g Ψ ∧
          section43PositiveEnergyQuotientMap (d := d) n Φ =
            section43PositiveEnergyQuotientMap (d := d) n Ψ}
```

Proof:

1. Let
   ```lean
   St :=
     (section43TimePositiveQuotientMap n) ⁻¹'
       Set.range (section43IteratedLaplaceCompactTransform n)
   Sx := section43SpatialFourierCompactRange d n
   ```
   The compiled theorem
   `dense_section43IteratedLaplaceCompactTransform_preimage n` gives
   `Dense St`; the new spatial packet gives `Dense Sx`.
2. Apply
   `dense_section43TimeSpatialTensor_span_of_factor_dense d n hSt hSx`.
3. Show every restricted tensor lies in the target preimage.  If
   `Φ ∈ St`, choose
   `g : Section43CompactStrictPositiveTimeSource n` with
   `section43IteratedLaplaceCompactTransform n g =
    section43TimePositiveQuotientMap n Φ`.
   If `χ ∈ Sx`, choose
   `κ : Section43SpatialCompactSource d n` with
   `χ = SchwartzMap.fourierTransformCLM ℂ κ.1`.
4. Let `Ψt := section43IteratedLaplaceSchwartzRepresentative n g` and
   `Ψ := section43TimeSpatialTensor d n Ψt χ`.  On the positive-energy region,
   quotient equality for `Φ` gives
   `Φ σ = Ψt σ` for `σ = section43QTime q`, and hence
   `section43TimeSpatialTensor d n Φ χ` and `Ψ` agree pointwise.
5. Let `G := section43TimeSpatialProductSource d n g κ`.  The representative
   predicate for `Ψ` follows from
   `partialFourierSpatial_fun_section43TimeSpatialProductSource` and the
   defining theorem
   `section43IteratedLaplaceSchwartzRepresentative_apply_of_mem`.
   The first production theorem should be the single-generator statement:
   ```lean
   theorem section43TimeLaplaceSpatialFourierRepresentative_productSource
       (d n : ℕ) [NeZero d]
       (g : Section43CompactStrictPositiveTimeSource n)
       (κ : Section43SpatialCompactSource d n) :
       section43TimeLaplaceSpatialFourierRepresentative d n
         (section43TimeSpatialProductSource d n g κ)
         (section43NPointTimeSpatialTensor d n
           (section43IteratedLaplaceSchwartzRepresentative n g)
           (SchwartzMap.fourierTransformCLM ℂ κ.1))
   ```
   Proof skeleton:
   ```lean
   intro q hq
   have hσ :
       section43QTime (d := d) (n := n) q ∈
         section43TimePositiveRegion n := by
     intro i
     simpa [section43PositiveEnergyRegion, section43QTime,
       nPointTimeSpatialCLE] using hq i
   rw [section43NPointTimeSpatialTensor_apply]
   rw [section43IteratedLaplaceSchwartzRepresentative_apply_of_mem g hσ]
   unfold section43IteratedLaplaceRaw
   rw [show
       (∫ τ : Fin n → ℝ,
          Complex.exp
            (-(∑ i : Fin n,
              (τ i : ℂ) *
                (section43QTime (d := d) (n := n) q i : ℂ))) *
            partialFourierSpatial_fun
              (d := d) (n := n)
              (section43TimeSpatialProductSource d n g κ).f
              (τ, section43QSpatial (d := d) (n := n) q)) =
       (∫ τ : Fin n → ℝ,
          Complex.exp
            (-(∑ i : Fin n,
              (τ i : ℂ) *
                (section43QTime (d := d) (n := n) q i : ℂ))) *
            g.f τ) *
         (SchwartzMap.fourierTransformCLM ℂ κ.1)
           (section43QSpatial (d := d) (n := n) q) by
     calc
       (∫ τ : Fin n → ℝ,
          Complex.exp
            (-(∑ i : Fin n,
              (τ i : ℂ) *
                (section43QTime (d := d) (n := n) q i : ℂ))) *
            partialFourierSpatial_fun
              (d := d) (n := n)
              (section43TimeSpatialProductSource d n g κ).f
              (τ, section43QSpatial (d := d) (n := n) q))
           =
         ∫ τ : Fin n → ℝ,
           (Complex.exp
             (-(∑ i : Fin n,
               (τ i : ℂ) *
                 (section43QTime (d := d) (n := n) q i : ℂ))) *
             g.f τ) *
           (SchwartzMap.fourierTransformCLM ℂ κ.1)
             (section43QSpatial (d := d) (n := n) q) := by
             congr with τ
             rw [partialFourierSpatial_fun_section43TimeSpatialProductSource]
             ring
       _ =
         (∫ τ : Fin n → ℝ,
           Complex.exp
             (-(∑ i : Fin n,
               (τ i : ℂ) *
                 (section43QTime (d := d) (n := n) q i : ℂ))) *
             g.f τ) *
           (SchwartzMap.fourierTransformCLM ℂ κ.1)
             (section43QSpatial (d := d) (n := n) q) :=
             MeasureTheory.integral_mul_const
               ((SchwartzMap.fourierTransformCLM ℂ κ.1)
                 (section43QSpatial (d := d) (n := n) q))
               (fun τ : Fin n → ℝ =>
                 Complex.exp
                   (-(∑ i : Fin n,
                     (τ i : ℂ) *
                       (section43QTime (d := d) (n := n) q i : ℂ))) *
                   g.f τ)]
   ```
   The theorem deliberately proves only the product-source representative
   identity; it does not yet claim density or linear closure.
   Production update, 2026-04-18: this theorem and the representative predicate
   are now compiled in
   `Section43FourierLaplaceSpatialDensity.lean`:
   ```lean
   section43TimeLaplaceSpatialFourierRepresentative
   section43TimeLaplaceSpatialFourierRepresentative_productSource
   ```
6. Therefore every restricted tensor is in the target.  Since the target is the
   preimage of a linear range under the quotient map once the time-spatial
   transform is packaged linearly, it is a submodule; otherwise prove directly
   that it is closed under finite linear combinations using additivity of the
   representative predicate and quotient map.  Prefer the linear-map packaging,
   mirroring `section43IteratedLaplaceCompactTransformLinearMap`.
   The immediate Lean subpacket before the full span/submodule closure is:
   ```lean
   theorem section43NPointTimeSpatialTensor_positiveEnergyQuotient_eq_of_timeQuotient_eq
       (d n : ℕ) [NeZero d]
       {φ ψ : SchwartzMap (Fin n → ℝ) ℂ}
       (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
       (hφψ :
         section43TimePositiveQuotientMap n φ =
           section43TimePositiveQuotientMap n ψ) :
       section43PositiveEnergyQuotientMap (d := d) n
         (section43NPointTimeSpatialTensor d n φ χ) =
       section43PositiveEnergyQuotientMap (d := d) n
         (section43NPointTimeSpatialTensor d n ψ χ)
   ```
   Proof skeleton:
   ```lean
   apply section43PositiveEnergyQuotientMap_eq_of_eqOn_region (d := d)
   intro q hq
   have hσ :
       section43QTime (d := d) (n := n) q ∈
         section43TimePositiveRegion n := by
     intro i
     simpa [section43PositiveEnergyRegion, section43QTime,
       nPointTimeSpatialCLE] using hq i
   have hφψ_point :
       φ (section43QTime (d := d) (n := n) q) =
         ψ (section43QTime (d := d) (n := n) q) :=
     eqOn_region_of_section43TimePositiveQuotientMap_eq hφψ hσ
   simp [section43NPointTimeSpatialTensor_apply, hφψ_point]
   ```
   Then prove the restricted-generator witness theorem:
   ```lean
   theorem section43NPointTimeSpatialTensor_mem_timeLaplaceSpatialFourierTarget
       (d n : ℕ) [NeZero d]
       (φ : SchwartzMap (Fin n → ℝ) ℂ)
       (χ : SchwartzMap (Section43SpatialSpace d n) ℂ)
       (hφ :
         φ ∈ ((section43TimePositiveQuotientMap n) ⁻¹'
           Set.range (section43IteratedLaplaceCompactTransform n)))
       (hχ : χ ∈ section43SpatialFourierCompactRange d n) :
       ∃ (G : Section43CompactStrictPositiveTimeSpatialSource d n)
         (Ψ : SchwartzNPoint d n),
         section43TimeLaplaceSpatialFourierRepresentative d n G Ψ ∧
         section43PositiveEnergyQuotientMap (d := d) n
           (section43NPointTimeSpatialTensor d n φ χ) =
         section43PositiveEnergyQuotientMap (d := d) n Ψ
   ```
   Proof route:
   ```lean
   rcases hφ with ⟨g, hg⟩
   rcases hχ with ⟨κ, rfl⟩
   let Ψt := section43IteratedLaplaceSchwartzRepresentative n g
   let Ψ :=
     section43NPointTimeSpatialTensor d n Ψt
       (SchwartzMap.fourierTransformCLM ℂ κ.1)
   refine ⟨section43TimeSpatialProductSource d n g κ, Ψ, ?_, ?_⟩
   · exact section43TimeLaplaceSpatialFourierRepresentative_productSource d n g κ
   · have hΨt_rep : section43IteratedLaplaceRepresentative n g Ψt := by
       intro σ hσ
       exact section43IteratedLaplaceSchwartzRepresentative_apply_of_mem g hσ
     have hcompact :
         section43IteratedLaplaceCompactTransform n g =
           section43TimePositiveQuotientMap n Ψt :=
       section43IteratedLaplaceCompactTransform_eq_quotient n g Ψt hΨt_rep
     exact
       section43NPointTimeSpatialTensor_positiveEnergyQuotient_eq_of_timeQuotient_eq
         d n (SchwartzMap.fourierTransformCLM ℂ κ.1)
         (hg.symm.trans hcompact)
   ```
   Production update, 2026-04-18: both generator-level theorems above are now
   compiled in `Section43FourierLaplaceSpatialDensity.lean`:
   ```lean
   section43NPointTimeSpatialTensor_positiveEnergyQuotient_eq_of_timeQuotient_eq
   section43NPointTimeSpatialTensor_mem_timeLaplaceSpatialFourierTarget
   ```
   Linear-closure packet needed next.  This is the finite-span bridge from the
   compiled generator containment theorem to the dense restricted span theorem.
   1. Give `Section43CompactStrictPositiveTimeSpatialSource d n` the same
      `Zero`, `Add`, `SMul ℂ`, `AddCommMonoid`, and `Module ℂ` structure as
      `Section43CompactStrictPositiveTimeSource n`, using `f` as the injective
      carrier map.  The support proofs are exactly:
      `tsupport_add`, `tsupport_smul_subset_right`, `HasCompactSupport.add`,
      and `HasCompactSupport.smul_left`.
      The implementation should be a direct copy of the existing namespace:
      ```lean
      namespace Section43CompactStrictPositiveTimeSpatialSource

      private theorem ext_f
          {G H : Section43CompactStrictPositiveTimeSpatialSource d n}
          (hf : G.f = H.f) : G = H := by
        cases G
        cases H
        simp at hf
        subst hf
        rfl

      private theorem f_injective (d n : ℕ) [NeZero d] :
          Function.Injective
            (fun G : Section43CompactStrictPositiveTimeSpatialSource d n => G.f) := by
        intro G H hf
        exact ext_f hf

      instance (d n : ℕ) [NeZero d] :
          Zero (Section43CompactStrictPositiveTimeSpatialSource d n) := ...
      instance (d n : ℕ) [NeZero d] :
          Add (Section43CompactStrictPositiveTimeSpatialSource d n) := ...
      instance (d n : ℕ) [NeZero d] :
          SMul ℕ (Section43CompactStrictPositiveTimeSpatialSource d n) := ...
      instance (d n : ℕ) [NeZero d] :
          AddCommMonoid (Section43CompactStrictPositiveTimeSpatialSource d n) :=
        Function.Injective.addCommMonoid
          (fun G : Section43CompactStrictPositiveTimeSpatialSource d n => G.f)
          (f_injective d n) rfl
          (by intro G H; rfl)
          (by
            intro G m
            change (m : ℂ) • G.f = m • G.f
            rw [Nat.cast_smul_eq_nsmul ℂ])
      instance (d n : ℕ) [NeZero d] :
          SMul ℂ (Section43CompactStrictPositiveTimeSpatialSource d n) := ...

      private def fAddMonoidHom (d n : ℕ) [NeZero d] :
          Section43CompactStrictPositiveTimeSpatialSource d n →+
            SchwartzNPoint d n where
        toFun := fun G => G.f
        map_zero' := rfl
        map_add' := by intro G H; rfl

      instance (d n : ℕ) [NeZero d] :
          Module ℂ (Section43CompactStrictPositiveTimeSpatialSource d n) :=
        Function.Injective.module ℂ (fAddMonoidHom d n)
          (by
            intro G H hf
            exact (f_injective d n) hf)
          (by intro c G; rfl)

      end Section43CompactStrictPositiveTimeSpatialSource
      ```
      The `Zero`, `Add`, and scalar cases are literally:
      ```lean
      positive := by
        intro q hq
        simp at hq

      positive := by
        intro q hq
        have hq' :=
          tsupport_add (G.f : NPointDomain d n → ℂ)
            (H.f : NPointDomain d n → ℂ) hq
        exact hq'.elim (fun hG => G.positive hG) (fun hH => H.positive hH)

      positive := by
        exact
          (tsupport_smul_subset_right
            (fun _ : NPointDomain d n => c)
            (G.f : NPointDomain d n → ℂ)).trans G.positive
      compact := by
        simpa using
          (HasCompactSupport.smul_left
            (f := fun _ : NPointDomain d n => c)
            (f' := (G.f : NPointDomain d n → ℂ)) G.compact)
      ```
   2. Prove strict support implies closed positive-energy support:
      ```lean
      theorem section43TimeSpatialSource_tsupport_subset_positiveEnergy
          (G : Section43CompactStrictPositiveTimeSpatialSource d n) :
          tsupport (G.f : NPointDomain d n → ℂ) ⊆
            section43PositiveEnergyRegion d n
      ```
      by `exact le_of_lt (G.positive hq i)`.
   3. Prove integrability of the representative time integrand:
      ```lean
      theorem integrable_section43TimeLaplaceSpatialFourier_timeIntegrand
          (G : Section43CompactStrictPositiveTimeSpatialSource d n)
          (q : NPointDomain d n)
          (hq : q ∈ section43PositiveEnergyRegion d n) :
          Integrable
            (fun τ : Fin n → ℝ =>
              Complex.exp
                (-(∑ i : Fin n,
                  (τ i : ℂ) *
                    (section43QTime (d := d) (n := n) q i : ℂ))) *
              partialFourierSpatial_fun
                (d := d) (n := n) G.f
                (τ, section43QSpatial (d := d) (n := n) q))
      ```
      Proof route: copy the proof of
      `integrable_section43FourierLaplace_timeIntegrand`, replacing
      `section43DiffPullbackCLM` by `G.f` and using
      `section43PartialFourierSpatial_fun_eq_zero_of_neg_time_of_support_positiveEnergy`
      with `section43TimeSpatialSource_tsupport_subset_positiveEnergy G`.
      The base integrability is `integrable_partialFourierSpatial_timeSlice`;
      on nonnegative `τ`, use `norm_exp_neg_section43_timePair_le_one`.
      The Lean skeleton is:
      ```lean
      let F : (Fin n → ℝ) → ℂ := fun τ =>
        partialFourierSpatial_fun
          (d := d) (n := n) G.f
          (τ, section43QSpatial (d := d) (n := n) q)
      let E : (Fin n → ℝ) → ℂ := fun τ =>
        Complex.exp
          (-(∑ k : Fin n,
            (τ k : ℂ) * (section43QTime (d := d) (n := n) q k : ℂ)))
      have hF_int : Integrable F (volume : Measure (Fin n → ℝ)) := by
        simpa [F] using
          integrable_partialFourierSpatial_timeSlice
            (d := d) (n := n) G.f
            (section43QSpatial (d := d) (n := n) q)
      have hEF_meas : AEStronglyMeasurable
          (fun τ : Fin n → ℝ => E τ * F τ)
          (volume : Measure (Fin n → ℝ)) := by
        have hE_cont : Continuous E := by
          fun_prop
        exact hE_cont.aestronglyMeasurable.mul hF_int.aestronglyMeasurable
      have hbound : ∀ᵐ τ : Fin n → ℝ ∂(volume : Measure (Fin n → ℝ)),
          ‖E τ * F τ‖ ≤ ‖F τ‖ := by
        refine Filter.Eventually.of_forall ?_
        intro τ
        by_cases hneg : ∃ i : Fin n, τ i < 0
        · rcases hneg with ⟨i, hi⟩
          have hF_zero : F τ = 0 := by
            simpa [F, Function.update_eq_self] using
              section43PartialFourierSpatial_fun_eq_zero_of_neg_time_of_support_positiveEnergy
                (d := d) (n := n) G.f
                (section43TimeSpatialSource_tsupport_subset_positiveEnergy
                  (d := d) (n := n) G)
                i τ (section43QSpatial (d := d) (n := n) q)
                (s := τ i) hi
          simp [hF_zero]
        · have hτ_nonneg : ∀ i : Fin n, 0 ≤ τ i := by
            intro i
            exact le_of_not_gt fun hi => hneg ⟨i, hi⟩
          have hE_le : ‖E τ‖ ≤ 1 := by
            simpa [E] using
              norm_exp_neg_section43_timePair_le_one
                (d := d) (n := n) q τ hq hτ_nonneg
          calc
            ‖E τ * F τ‖ = ‖E τ‖ * ‖F τ‖ := norm_mul _ _
            _ ≤ 1 * ‖F τ‖ :=
              mul_le_mul_of_nonneg_right hE_le (norm_nonneg _)
            _ = ‖F τ‖ := one_mul _
      simpa [F, E] using hF_int.mono hEF_meas hbound
      ```
   4. Prove representative linearity:
      ```lean
      theorem section43TimeLaplaceSpatialFourierRepresentative_add
          {G H : Section43CompactStrictPositiveTimeSpatialSource d n}
          {Φ Ψ : SchwartzNPoint d n}
          (hΦ : section43TimeLaplaceSpatialFourierRepresentative d n G Φ)
          (hΨ : section43TimeLaplaceSpatialFourierRepresentative d n H Ψ) :
          section43TimeLaplaceSpatialFourierRepresentative d n (G + H) (Φ + Ψ)

      theorem section43TimeLaplaceSpatialFourierRepresentative_smul
          (c : ℂ)
          {G : Section43CompactStrictPositiveTimeSpatialSource d n}
          {Φ : SchwartzNPoint d n}
          (hΦ : section43TimeLaplaceSpatialFourierRepresentative d n G Φ) :
          section43TimeLaplaceSpatialFourierRepresentative d n (c • G) (c • Φ)
      ```
      For add, use the integrability theorem for `G` and `H`,
      `MeasureTheory.integral_add`, and `partialFourierSpatial_fun_add`.
      For scalar multiplication, use `MeasureTheory.integral_const_mul` and
      `partialFourierSpatial_fun_smul`.
      Avoid brittle rewriting by naming the exponential and Fourier factors:
      ```lean
      intro q hq
      let E : (Fin n → ℝ) → ℂ := fun τ => ...
      let FG : (Fin n → ℝ) → ℂ := fun τ =>
        partialFourierSpatial_fun (d := d) (n := n) G.f
          (τ, section43QSpatial (d := d) (n := n) q)
      let FH : (Fin n → ℝ) → ℂ := fun τ =>
        partialFourierSpatial_fun (d := d) (n := n) H.f
          (τ, section43QSpatial (d := d) (n := n) q)
      have hGint := integrable_section43TimeLaplaceSpatialFourier_timeIntegrand
        (d := d) (n := n) G q hq
      have hHint := integrable_section43TimeLaplaceSpatialFourier_timeIntegrand
        (d := d) (n := n) H q hq
      calc
        (Φ + Ψ) q = Φ q + Ψ q := rfl
        _ =
            (∫ τ : Fin n → ℝ, E τ * FG τ) +
            (∫ τ : Fin n → ℝ, E τ * FH τ) := by
              rw [hΦ q hq, hΨ q hq]
        _ = ∫ τ : Fin n → ℝ, E τ * FG τ + E τ * FH τ := by
              exact (MeasureTheory.integral_add
                (by simpa [E, FG] using hGint)
                (by simpa [E, FH] using hHint)).symm
        _ = ∫ τ : Fin n → ℝ, E τ *
              partialFourierSpatial_fun (d := d) (n := n) (G + H).f
                (τ, section43QSpatial (d := d) (n := n) q) := by
              congr with τ
              change E τ * FG τ + E τ * FH τ =
                E τ * partialFourierSpatial_fun
                  (d := d) (n := n) (G.f + H.f)
                  (τ, section43QSpatial (d := d) (n := n) q)
              rw [partialFourierSpatial_fun_add]
              change E τ * FG τ + E τ * FH τ = E τ * (FG τ + FH τ)
              ring
      ```
      Scalar multiplication is the same pattern:
      ```lean
      intro q hq
      let E : (Fin n → ℝ) → ℂ := fun τ => ...
      let FG : (Fin n → ℝ) → ℂ := fun τ =>
        partialFourierSpatial_fun (d := d) (n := n) G.f
          (τ, section43QSpatial (d := d) (n := n) q)
      have hGint := integrable_section43TimeLaplaceSpatialFourier_timeIntegrand
        (d := d) (n := n) G q hq
      calc
        (c • Φ) q = c * Φ q := by simp [smul_eq_mul]
        _ = c * ∫ τ : Fin n → ℝ, E τ * FG τ := by
              rw [hΦ q hq]
        _ = ∫ τ : Fin n → ℝ, c * (E τ * FG τ) := by
              exact (MeasureTheory.integral_const_mul c
                (fun τ : Fin n → ℝ => E τ * FG τ)).symm
        _ = ∫ τ : Fin n → ℝ, E τ *
              partialFourierSpatial_fun (d := d) (n := n) (c • G).f
                (τ, section43QSpatial (d := d) (n := n) q) := by
              congr with τ
              change c * (E τ * FG τ) =
                E τ * partialFourierSpatial_fun
                  (d := d) (n := n) (c • G.f)
                  (τ, section43QSpatial (d := d) (n := n) q)
              rw [partialFourierSpatial_fun_smul]
              change c * (E τ * FG τ) = E τ * (c * FG τ)
              ring
      ```
      The explicit `change` lines are important: they expose `(G + H).f` and
      `(c • G).f` as `G.f + H.f` and `c • G.f` before applying the
      partial-Fourier linearity lemmas.
   5. Define the representative target set and prove finite-span containment:
      ```lean
      def section43TimeLaplaceSpatialFourierTarget
          (d n : ℕ) [NeZero d] : Set (SchwartzNPoint d n) :=
        {Φ |
          ∃ (G : Section43CompactStrictPositiveTimeSpatialSource d n)
            (Ψ : SchwartzNPoint d n),
            section43TimeLaplaceSpatialFourierRepresentative d n G Ψ ∧
            section43PositiveEnergyQuotientMap (d := d) n Φ =
              section43PositiveEnergyQuotientMap (d := d) n Ψ}

      theorem section43TimeLaplaceSpatialFourierTarget_add
          {Φ Ψ : SchwartzNPoint d n}
          (hΦ : Φ ∈ section43TimeLaplaceSpatialFourierTarget d n)
          (hΨ : Ψ ∈ section43TimeLaplaceSpatialFourierTarget d n) :
          Φ + Ψ ∈ section43TimeLaplaceSpatialFourierTarget d n

      theorem section43TimeLaplaceSpatialFourierTarget_smul
          (c : ℂ) {Φ : SchwartzNPoint d n}
          (hΦ : Φ ∈ section43TimeLaplaceSpatialFourierTarget d n) :
          c • Φ ∈ section43TimeLaplaceSpatialFourierTarget d n
      ```
      In the quotient equalities, use `map_add` and `map_smul` for
      `section43PositiveEnergyQuotientMap`, then the representative add/smul
      theorem for the witnesses.  With these two closure lemmas, prove
      `Submodule.span ℂ restrictedGenerators ⊆ section43TimeLaplaceSpatialFourierTarget d n`
      by `Submodule.span_induction`, using the compiled generator containment
      theorem as the base case.
   Production update, 2026-04-18: the full linear-closure and dense-target
   packet is compiled in `Section43FourierLaplaceSpatialDensity.lean`:
   ```lean
   section43TimeSpatialSource_tsupport_subset_positiveEnergy
   integrable_section43TimeLaplaceSpatialFourier_timeIntegrand
   section43TimeLaplaceSpatialFourierRepresentative_add
   section43TimeLaplaceSpatialFourierRepresentative_smul
   section43TimeLaplaceSpatialFourierTarget
   section43TimeLaplaceSpatialFourierTarget_zero
   section43TimeLaplaceSpatialFourierTarget_add
   section43TimeLaplaceSpatialFourierTarget_smul
   section43NPointTimeSpatialTensor_span_le_timeLaplaceSpatialFourierTarget
   dense_section43TimeLaplaceSpatialFourier_compact_preimage
   ```
6. Conclude density by `Dense.mono` from the dense restricted span.  This is
   now the compiled theorem
   `dense_section43TimeLaplaceSpatialFourier_compact_preimage`.

The `n = 0` case must be kept explicit in implementation.  Then
`Fin n → ℝ` and `Section43SpatialSpace d n` are singleton/zero-dimensional
spaces, the time integral is over a point, and the theorem reduces to the
spatial Fourier compact-range density plus scalar multiplication.  Do not
force this case through one-variable Laplace statements.

## Layer 4: Difference-Coordinate Transport

Main raw theorem:

```lean
theorem dense_section43FourierLaplace_compact_ordered_preimage_raw
    (d n : ℕ) [NeZero d] :
    Dense
      {Φ : SchwartzNPoint d n |
        ∃ (f : SchwartzNPoint d n)
          (hf_ord :
            tsupport (f : NPointDomain d n → ℂ) ⊆
              OrderedPositiveTimeRegion d n)
          (hf_compact : HasCompactSupport (f : NPointDomain d n → ℂ)),
          section43PositiveEnergyQuotientMap (d := d) n Φ =
            section43FourierLaplaceTransformComponent d n
              f hf_ord hf_compact}
```

Proof:

Implementation file: use a new downstream companion
`Section43FourierLaplaceOrderedDensity.lean` importing both
`Section43FourierLaplaceSpatialDensity` and
`Section43FourierLaplaceClosure`.  This avoids reopening the large transform
or closure files while giving access to the compiled Layer-3 dense target and
the existing component map `section43FourierLaplaceTransformComponentMap`.

The required ordered-transport packet is:

1. Prove the strict-positive-differences-to-ordered-times lemma:
   ```lean
   theorem section43DiffCoordRealCLE_symm_mem_orderedPositiveTimeRegion_of_pos_time
       (d n : ℕ) [NeZero d]
       {δ : NPointDomain d n}
       (hδ : ∀ i : Fin n, 0 < δ i 0) :
       (section43DiffCoordRealCLE d n).symm δ ∈
         OrderedPositiveTimeRegion d n
   ```
   Proof route: unfold `OrderedPositiveTimeRegion`; use
   `section43DiffCoordRealCLE_symm_apply` to rewrite each ordered time as a
   partial sum of `δ r 0`.  Positivity of the first time is
   `Finset.sum_pos` over `Fin (i.val + 1)`, with witness `0`.  For `i < j`,
   prove the difference of partial sums is the sum of the nonempty block
   `r = i.val + 1, ..., j.val`; this sum is positive by `Finset.sum_pos`.
   Equivalently, use an auxiliary Nat-indexed lemma:
   ```lean
   lemma partialSum_strictMono_of_pos
       {n : ℕ} {a : Fin n → ℝ}
       (ha : ∀ i, 0 < a i) :
       StrictMono fun k : Fin n =>
         ∑ r : Fin (k.val + 1), a ⟨r.val, by omega⟩
   ```
   Then apply it to `a i = δ i 0`.
   Lean skeleton for the strict inequality case.  The concrete implementation
   uses an auxiliary Nat-indexed function `fj` for the larger partial sum; this
   avoids trying to form the dependent term `δ ⟨r, by omega⟩` before Lean knows
   the required bound from `r < j.val + 1`.
   ```lean
   intro i j hij
   rw [section43DiffCoordRealCLE_symm_apply,
     section43DiffCoordRealCLE_symm_apply]
   rw [Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range]
   have hijv : i.val < j.val := by exact hij
   have hle : i.val + 1 ≤ j.val + 1 := Nat.succ_le_succ hijv.le
   let fj : ℕ → ℝ := fun r =>
     if h : r < j.val + 1 then
       δ ⟨(⟨r, h⟩ : Fin (j.val + 1)).val, by
         have hj := j.isLt
         omega⟩ 0
     else 0
   have hblock_nonempty : (Finset.Ico (i.val + 1) (j.val + 1)).Nonempty := by
     refine ⟨i.val + 1, ?_⟩
     exact Finset.mem_Ico.mpr ⟨le_rfl, Nat.succ_lt_succ hijv⟩
   have hleft :
       (∑ r ∈ Finset.range (i.val + 1),
         if h : r < i.val + 1 then
           δ ⟨(⟨r, h⟩ : Fin (i.val + 1)).val, by
             have hi := i.isLt
             omega⟩ 0
         else 0) =
       (∑ r ∈ Finset.range (i.val + 1), fj r) := by
     refine Finset.sum_congr rfl ?_
     intro r hr
     have hri : r < i.val + 1 := Finset.mem_range.mp hr
     have hrj : r < j.val + 1 := lt_of_lt_of_le hri hle
     have hrjle : r ≤ j.val := Nat.lt_succ_iff.mp hrj
     rw [dif_pos hri]
     simp [fj, hrjle]
   have hblock_pos :
       0 < ∑ r ∈ Finset.Ico (i.val + 1) (j.val + 1), fj r := by
     refine Finset.sum_pos ?_ hblock_nonempty
     intro r hr
     have hrj : r < j.val + 1 := (Finset.mem_Ico.mp hr).2
     have hrjle : r ≤ j.val := Nat.lt_succ_iff.mp hrj
     simpa [fj, hrjle] using hδ ⟨r, by
       have hj := j.isLt
       omega⟩
   rw [hleft]
   change (∑ r ∈ Finset.range (i.val + 1), fj r) <
     ∑ r ∈ Finset.range (j.val + 1), fj r
   rw [← Finset.sum_range_add_sum_Ico fj hle]
   exact lt_add_of_pos_right _ hblock_pos
   ```
   The positivity case is the same `Finset.sum_fin_eq_sum_range` rewrite plus
   `Finset.sum_pos` on `range (i.val + 1)`.

2. Define the ordered pushforward of a compact strict-positive difference
   source:
   ```lean
   noncomputable def section43OrderedSourceOfTimeSpatialSource
       (d n : ℕ) [NeZero d]
       (G : Section43CompactStrictPositiveTimeSpatialSource d n) :
       Section43CompactOrderedSource d n
   ```
   with carrier
   ```lean
   f :=
     SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
       (section43DiffCoordRealCLE d n) G.f
   ```
   so pointwise
   `f y = G.f (section43DiffCoordRealCLE d n y)`.
   Ordered support proof: if `y ∈ tsupport f`, use
   `tsupport_comp_subset_preimage` to get
   `section43DiffCoordRealCLE d n y ∈ tsupport G.f`, apply `G.positive`, and
   then apply the strict-positive-differences-to-ordered-times lemma to
   `δ := section43DiffCoordRealCLE d n y`.
   Compactness proof: use `tsupport_comp_eq_preimage` for
   `(section43DiffCoordRealCLE d n).toHomeomorph`, rewrite the preimage as
   `(section43DiffCoordRealCLE d n).symm '' tsupport G.f`, and use
   `G.compact.isCompact.image`.

3. Prove the pullback of this ordered pushforward is the original
   difference-coordinate source:
   ```lean
   theorem section43DiffPullbackCLM_orderedSourceOfTimeSpatialSource
       (d n : ℕ) [NeZero d]
       (G : Section43CompactStrictPositiveTimeSpatialSource d n) :
       section43DiffPullbackCLM d n
         ⟨(section43OrderedSourceOfTimeSpatialSource d n G).f,
          (section43OrderedSourceOfTimeSpatialSource d n G).ordered⟩ =
       G.f
   ```
   Proof route: ext `δ`; unfold `section43DiffPullbackCLM_apply` and the
   pushforward carrier; simplify
   `section43DiffCoordRealCLE d n ((section43DiffCoordRealCLE d n).symm δ)`.

4. Convert a Layer-3 time/spatial representative to the existing OS-I
   Fourier-Laplace representative:
   ```lean
   theorem section43FourierLaplaceRepresentative_of_timeSpatialRepresentative
       (d n : ℕ) [NeZero d]
       {G : Section43CompactStrictPositiveTimeSpatialSource d n}
       {Ψ : SchwartzNPoint d n}
       (hΨ :
         section43TimeLaplaceSpatialFourierRepresentative d n G Ψ) :
       section43FourierLaplaceRepresentative d n
         ⟨(section43OrderedSourceOfTimeSpatialSource d n G).f,
          (section43OrderedSourceOfTimeSpatialSource d n G).ordered⟩ Ψ
   ```
   Proof route: for `q ∈ section43PositiveEnergyRegion`, rewrite
   `section43FourierLaplaceIntegral`; use
   `section43DiffPullbackCLM_orderedSourceOfTimeSpatialSource` so the integrand
   is definitionally the same as in `hΨ q hq`.

5. Convert a Layer-3 target witness into membership in the component-map
   preimage:
   ```lean
   theorem section43TimeLaplaceSpatialFourierTarget_subset_component_preimage
       (d n : ℕ) [NeZero d] :
       section43TimeLaplaceSpatialFourierTarget d n ⊆
         (section43PositiveEnergyQuotientMap (d := d) n) ⁻¹'
           Set.range (section43FourierLaplaceTransformComponentMap d n)
   ```
   Proof route: take `Φ` with witness `G, Ψ, hΨ, hΦq`.  Let
   `src := section43OrderedSourceOfTimeSpatialSource d n G`.  Get
   `hΨ_FL` from step 4.  Obtain
   `⟨Φc, hΦc_FL, hΦc_q⟩` from
   `section43FourierLaplaceTransformComponent_has_representative` for
   `src.f src.ordered src.compact`.  Since `Ψ` and `Φc` are both
   `section43FourierLaplaceRepresentative` for the same ordered source, use
   `section43PositiveEnergyQuotientMap_eq_of_eqOn_region` to prove
   `section43PositiveEnergyQuotientMap Ψ =
    section43PositiveEnergyQuotientMap Φc`.  Then combine with `hΦq` and
   `hΦc_q`, and use
   `⟨src, by simp [section43FourierLaplaceTransformComponentMap]⟩` for the
   range witness.

6. Prove the raw ordered preimage density theorem:
   ```lean
   theorem dense_section43FourierLaplace_compact_ordered_preimage_raw
       (d n : ℕ) [NeZero d] :
       Dense
         ((section43PositiveEnergyQuotientMap (d := d) n) ⁻¹'
           Set.range (section43FourierLaplaceTransformComponentMap d n))
   ```
   Proof route:
   ```lean
   exact Dense.mono
     (section43TimeLaplaceSpatialFourierTarget_subset_component_preimage d n)
     (by
       simpa [section43TimeLaplaceSpatialFourierTarget] using
         dense_section43TimeLaplaceSpatialFourier_compact_preimage d n)
   ```

Production update, 2026-04-18: this ordered-density bridge is compiled in the
new companion file
`OSReconstruction/Wightman/Reconstruction/WickRotation/Section43FourierLaplaceOrderedDensity.lean`:
```lean
section43DiffCoordRealCLE_symm_mem_orderedPositiveTimeRegion_of_pos_time
section43OrderedSourceOfTimeSpatialSource
section43DiffPullbackCLM_orderedSourceOfTimeSpatialSource
section43FourierLaplaceRepresentative_of_timeSpatialRepresentative
section43TimeLaplaceSpatialFourierTarget_subset_component_preimage
dense_section43FourierLaplace_compact_ordered_preimage_raw
```

## Final Production Theorem

```lean
theorem dense_section43FourierLaplaceTransformComponentMap_preimage
    (d n : ℕ) [NeZero d] :
    Dense
      ((section43PositiveEnergyQuotientMap (d := d) n) ⁻¹'
        Set.range (section43FourierLaplaceTransformComponentMap d n))
```

Proof:

1. Start from
   `dense_section43FourierLaplace_compact_ordered_preimage_raw`.
2. Convert a raw witness `(f, hf_ord, hf_compact)` into
   `src : Section43CompactOrderedSource d n`.
3. Unfold `section43FourierLaplaceTransformComponentMap`.
4. The target set is definitionally the same preimage of the range.

No theorem after this point should perform any new analysis.  The compiled
closure theorem consumes the result immediately:

```lean
fun OS lgc F =>
  bvt_W_positive_of_component_dense_preimage
    (d := d) OS lgc
    (fun n => dense_section43FourierLaplaceTransformComponentMap_preimage d n)
    F
```

Production update, 2026-04-18: theorem-3 positivity is now closed in
`OSToWightmanBoundaryValues.lean`.  The proof imports the compiled ordered
density bridge and applies
`OSReconstruction.bvt_W_positive_of_component_dense_preimage` with
`OSReconstruction.dense_section43FourierLaplace_compact_ordered_preimage_raw`.
No additional analytic theorem is inserted at the public frontier.
