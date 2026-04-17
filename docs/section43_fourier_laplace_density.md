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

Production status, 2026-04-17: this density file now exists and the foundation
plus one-variable Paley-Wiener uniqueness packets are compiled:

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
section43FourierInvCLM1D
section43FourierInvCLM1D_apply
section43PositiveEnergy1D_to_oneSidedFourierFunctional
section43PositiveEnergy1D_to_oneSidedFourierFunctional_support
fourierPairingDescendsToSection43PositiveEnergy1D_to_oneSided
section43OneSidedAnnihilatorFL
section43OneSidedAnnihilatorFL_eq_fourierLaplaceExt_to_oneSided
section43OneSidedAnnihilatorFLOnImag
section43OneSidedAnnihilatorFLOnImag_of_pos
section43OneSidedAnnihilatorFLOnImag_of_not_pos
section43PositiveEnergy1D_ext_of_FL_zero
```

The remaining one-variable blocker is no longer Paley-Wiener uniqueness.  It is
the compact-source annihilator bridge:

```lean
exists_section43OneSidedLaplaceRepresentative1D
section43OneSidedLaplaceCompactTransform1D
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

Suggested imports:

```lean
import OSReconstruction.Wightman.Reconstruction.WickRotation.Section43FourierLaplaceClosure
```

If this creates an import cycle, import only the lower files needed for the
analytic packet, then move `Section43CompactOrderedSource` and
`section43FourierLaplaceTransformComponentMap` from
`Section43FourierLaplaceClosure.lean` into the density file or a tiny shared
source file.  Do not import `OSToWightmanPositivity.lean`.

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
      ContinuousMultilinearMap.mkPiAlgebraFin ℝ r ℂ
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

For the rapid theorem, use
`exists_positive_Icc_bounds_of_compactPositiveTimeSource` to choose
`0 < δ ≤ R` and `tsupport g.f ⊆ Set.Icc δ R`.  Split `σ ∈ Set.Ici (-1)` into
`σ ≤ 0` and `0 ≤ σ`.  On `[-1,0]`, bound the exponential by `Real.exp R` and
use compact support.  On `[0,∞)`, use
`Real.exp (-(δ * σ))` and the standard fact that exponential decay dominates
all polynomial powers.

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

Then convert integral vanishing against every compact strict-positive source to
pointwise vanishing on the strict half-line using the existing local
distribution lemma:

```lean
OSReconstruction.SCV.eq_zero_on_open_of_compactSupport_schwartz_integral_zero
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

Proof transcript:

1. Apply `eq_zero_on_open_of_compactSupport_schwartz_integral_zero` with
   `U := Set.Ioi (0 : ℝ)` and
   `g := section43OneSidedAnnihilatorFLOnImag A`.
2. Continuity of `g` on `Set.Ioi 0` follows from holomorphicity or directly
   from continuity of `SCV.schwartzPsiZ` in the imaginary-axis parameter and
   continuity of `A`.
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
