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

Use the following locally convex separation helper.  If Mathlib already exposes
this theorem under a different name, add a local wrapper with this statement so
the density proof has a stable target:

```lean
theorem denseRange_of_dual_annihilator_zero
    {E F : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [LocallyConvexSpace ℂ F]
    (L : E → F)
    (hlin : IsLinearMap ℂ L)
    (hann :
      ∀ A : F →L[ℂ] ℂ,
        (∀ x : E, A (L x) = 0) → A = 0) :
    DenseRange L
```

If the target is a quotient and it is easier to work in the ambient space, use
the equivalent preimage form supplied by `IsOpenQuotientMap.dense_preimage_iff`.

Then prove the analytic annihilator lemma:

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

1. Use `SCV.schwartz_functional_bound T` to choose a finite set of Schwartz
   seminorms and a constant controlling `‖T φ‖`.
2. Use `exists_positive_Icc_bounds_of_compactPositiveTimeSource g` to reduce
   all source-time integrals to a compact interval `[δ,R]` with `0 < δ`.
3. Prove a compact-vertical-segment seminorm bound for the imaginary-axis
   kernels:

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
4. Prove scalar integrability:

```lean
theorem integrable_section43_scalar_kernel_after_functional
    (T : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (g : Section43CompactPositiveTimeSource1D) :
    Integrable (fun t : ℝ => T (section43ImagAxisPsiKernel t) * g.f t)
```

   Use the seminorm bound from Step 3, the functional bound from Step 1, and
   compact support/integrability of `g.f`.
5. Prove the weak integral identity by approximating the compactly supported
   parameter integral in the Schwartz topology using Riemann sums or a standard
   parameter-integral theorem formulated in terms of the finite seminorm family
   from Step 1.  The statement should avoid constructing a
   `SchwartzMap`-valued Bochner integral; it only needs convergence after
   applying `T`.
6. On the nonnegative axis, rewrite the explicit representative with
   `section43OneSidedLaplaceCutoffFun_eq_raw_of_nonneg`,
   `SCV.schwartzPsiZ_apply`, and `SCV.psiZ_eq_exp_of_nonneg`.  On
   `¬ 0 < t`, use `g.f t = 0`, which follows from `g.positive` and
   `Function.support_subset_tsupport`.

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

Definitions:

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

Main theorem:

```lean
theorem dense_section43IteratedLaplaceCompactTransform_preimage
    (n : ℕ) :
    Dense
      ((section43TimePositiveQuotientMap n) ⁻¹'
        Set.range (section43IteratedLaplaceCompactTransform n))
```

Proof:

1. `n = 0`: the quotient is one-dimensional.  Choose the constant scalar
   source on the one-point domain.
2. `n + 1`: split `Fin (n + 1) → ℝ` by
   `MeasurableEquiv.piFinSuccAbove`.  Use the one-coordinate transform formula
   and apply the one-variable dense theorem in the distinguished coordinate.
3. Preserve strict compact support by choosing approximants with support in a
   compact subinterval of `(0,∞)` and multiplying by the already compact
   background support in the remaining coordinates.
4. Use finite induction over coordinates.

This is the formal version of the OS I Lemma-4.1 reduction from the
multivariate transform to Lemma 8.2.

## Layer 3: Add Spatial Fourier Transform

Definitions:

```lean
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

1. Use `nPointTimeSpatialCLE` to identify `NPointDomain d n` with
   `(Fin n → ℝ) × EuclideanSpace ℝ (Fin n × Fin d)`.
2. Apply Layer 2 in the time variables.
3. Use the spatial Fourier transform as a continuous linear equivalence in the
   spatial variables.  Density is preserved by continuous linear equivalences
   and by the open quotient map.
4. Use `partialFourierSpatial_fun_eq_integral` to identify the representative
   formula with the production spatial Fourier convention.

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

1. Pull ordered sources to difference coordinates with
   `section43DiffPullbackCLM d n`.
2. `OrderedPositiveTimeRegion` becomes strict positive time-difference support
   under `section43DiffCoordRealCLE`.
3. Compact support is preserved by the continuous linear equivalence.
4. The formula
   `section43FourierLaplaceIntegral_eq_time_spatial_integral` identifies the
   resulting transform with the Layer-3 representative.
5. Convert representatives to production quotient classes using
   `section43FourierLaplaceTransformComponent_has_representative`.

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
