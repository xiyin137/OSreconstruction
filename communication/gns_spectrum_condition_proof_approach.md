# `gns_spectrum_condition` Proof Approach

## Context

This note records the current implementation plan for proving
`gns_spectrum_condition` in
`OSReconstruction/Wightman/Reconstruction/GNSHilbertSpace.lean`
after the spectral-condition refactor.

The current target is no longer the old operator-inequality statement
`SpectralCondition`. It is now the matrix-element spectral condition:

```lean
theorem gns_spectrum_condition :
    MatrixElementSpectralCondition d (gnsPoincareRep Wfn) := by
  sorry
```

This is a more realistic target because it avoids having to prove the full
joint-spectrum theorem for the Stone generators immediately.

## Overall Strategy

The proof should be split according to the two fields of
`MatrixElementSpectralCondition`:

1. `strongly_continuous`
2. `matrix_coefficient_holomorphic`

The key idea is:

- prove both statements first on the dense pre-Hilbert / Borchers subspace;
- then extend to the GNS completion if needed.

## Part 1: Strong Continuity of GNS Translation Subgroups

### Goal

For each spacetime direction `μ`, prove:

```lean
PoincareRepresentation.translationContinuousInDirection
  (gnsPoincareRep Wfn) μ
```

### Plan

#### Step 1A: Pre-Hilbert continuity

First prove continuity on `PreHilbertSpace Wfn`.

For a representative `⟦F⟧`, analyze:

```text
t ↦ poincareActPreHilbert Wfn (translationInDirection d μ t) ⟦F⟧
```

The proof should reduce to Borchers representatives and use:

- continuity of translation on Schwartz functions;
- continuity of `Wfn.W n` from `Wfn.tempered`;
- the finite-sum nature of Borchers inner products.

Expected helper theorem names:

- `translationContinuousInDirection_preHilbert`
- possibly a representative-level lemma on Borchers sequences.

#### Step 1B: Pass to the GNS completion

Then lift continuity from the dense pre-Hilbert image to
`GNSHilbertSpace Wfn`.

Use:

- density of the completion embedding;
- continuity / linearity / unitarity of `poincareActGNS`.

Expected theorem:

- `translationContinuousInDirection_gns`

#### Step 1C: Package the field

Assemble:

```lean
strongly_continuous : translationStronglyContinuous (gnsPoincareRep Wfn)
```

by proving the continuity statement for every `μ`.

## Part 2: Holomorphic Continuation of Translation Matrix Coefficients

### Goal

For every `χ ψ : GNSHilbertSpace Wfn`, construct

```lean
F : ComplexSpacetime d → ℂ
```

such that:

- `F` is holomorphic on `TranslationForwardTube d`;
- the boundary values of `F` recover
  `⟪χ, (gnsPoincareRep Wfn).U (translation' a) ψ⟫`.

### Core idea

Do not start with arbitrary Hilbert vectors.
Start with dense vectors represented by Borchers sequences.

If:

- `χ = ⟦F⟧`
- `ψ = ⟦G⟧`

then:

```text
⟪χ, U(a) ψ⟫
```

expands into a finite sum using the GNS inner product formula. Each summand is
a Wightman functional applied to a translated Schwartz expression.

The existing input
`Wfn.spectrum_condition`
already provides analytic continuation of the relevant Wightman distributions to
the forward tube. The plan is therefore to define the continuation of the GNS
matrix coefficient term-by-term using those chosen analytic continuations, then
sum them.

### Plan

#### Step 2A: Expand matrix coefficients on dense vectors

For Borchers representatives `F` and `G`, prove an explicit formula for:

```text
⟪⟦F⟧, U(a) ⟦G⟧⟫
```

as a finite sum over `n, m`.

Expected helper theorem:

- `matrixCoefficient_preHilbert_expand`

#### Step 2B: Define the analytic continuation termwise

For each summand in the expansion, use the analytic continuation data from
`Wfn.spectrum_condition`.

Construct a candidate continuation for the whole matrix coefficient as a finite
sum of those analytic terms.

Expected helper theorem / definition:

- `matrixCoefficientAnalytic_preHilbert`

#### Step 2C: Prove holomorphicity

Show each summand is holomorphic on `TranslationForwardTube d`, then conclude
the finite sum is holomorphic.

Expected theorem:

- `matrixCoefficient_holomorphic_preHilbert`

#### Step 2D: Prove the boundary-value statement

Use the boundary-value part of `Wfn.spectrum_condition` term-by-term.
Since the Borchers sum is finite, pass the limit through the sum directly.

Expected theorem:

- `matrixCoefficient_boundary_preHilbert`

## Part 3: Extend from Dense Vectors to the Full GNS Hilbert Space

This is the main design choice.

### Option A: Keep the current quantification over all Hilbert vectors

Then after proving the dense-vector statement, extend to arbitrary
`χ ψ : GNSHilbertSpace Wfn` by approximation.

This will require:

- continuity of the inner product;
- continuity of the unitary translation action;
- careful control of how the analytic continuation depends on approximants.

This is conceptually straightforward but technically heavier.

### Option B: Weaken the matrix-element spectral condition to a dense domain

If the current `MatrixElementSpectralCondition` proves too awkward to realize
for all Hilbert vectors, a better design may be to quantify only over a fixed
dense invariant domain.

That would match the natural GNS proof more closely:

- Borchers / pre-Hilbert vectors are the canonical dense domain;
- analyticity is most naturally proved there.

This is a possible review point for other agents: whether the current axiom
should quantify over all Hilbert vectors or over a dense domain.

## Main Mathematical Seam

The main seam is not Stone anymore.

The main seam is:

- converting the existing `Wfn.spectrum_condition`, which is stated for
  n-point Wightman functions on the forward tube,
- into the one-variable translation analyticity statement needed for
  GNS translation matrix coefficients.

So the key bridge lemma should show:

1. translating the right Borchers argument by a real spacetime vector `a`
   corresponds to the relevant complex shift in the analytic continuation;
2. the resulting finite sum of analytic Wightman terms has the correct
   boundary value;
3. this sum equals the desired GNS matrix coefficient.

This is likely the first nontrivial proof bottleneck.

## Recommended Theorem-by-Theorem Order

Suggested implementation order inside `GNSHilbertSpace.lean`:

1. `translationContinuousInDirection_preHilbert`
2. `translationContinuousInDirection_gns`
3. `matrixCoefficient_preHilbert_expand`
4. `matrixCoefficientAnalytic_preHilbert`
5. `matrixCoefficient_holomorphic_preHilbert`
6. `matrixCoefficient_boundary_preHilbert`
7. extension-to-completion lemmas, if the axiom keeps quantifying over all
   Hilbert vectors
8. final assembly of `gns_spectrum_condition`

## Questions for Review

These are the points I would want reviewed by other agents:

1. Is the current `MatrixElementSpectralCondition` quantification over all
   Hilbert vectors the right design, or should it be domain-based?
2. What is the cleanest bridge from `Wfn.spectrum_condition` to translation
   matrix coefficients on Borchers vectors?
3. Is strong continuity on the GNS completion best proved directly, or first at
   the pre-Hilbert level and then extended by density?
4. Are there existing lemmas in the Wick-rotation / forward-tube modules that
   already package the exact boundary-value statement needed here?

## Bottom Line

The current proof attempt should no longer aim directly at positivity of
Hamiltonian expectations or mass-shell inequalities.

It should instead:

- prove strong continuity of the GNS translation subgroups;
- prove forward-tube analyticity of translation matrix coefficients on dense
  GNS vectors by explicit finite-sum expansion and `Wfn.spectrum_condition`;
- extend if necessary to all GNS vectors;
- package the result as `MatrixElementSpectralCondition`.
