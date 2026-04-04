# `gns_matrix_coefficient_holomorphic_axiom` Strategy Note

## Context

This note records the current proof suggestion for
`gns_matrix_coefficient_holomorphic_axiom` in
`OSReconstruction/Wightman/Reconstruction/GNSHilbertSpace.lean`.

The theorem currently appears as:

```lean
theorem gns_matrix_coefficient_holomorphic_axiom
    (χ ψ : GNSHilbertSpace Wfn) :
    ∃ F : ComplexSpacetime d → ℂ,
      DifferentiableOn ℂ F (TranslationForwardTube d) ∧
      ∀ (a η : MinkowskiSpace d), η ∈ MinkowskiSpace.OpenForwardLightCone d →
        Filter.Tendsto
          (fun ε : ℝ => F (fun μ => ↑(a μ) + ε * ↑(η μ) * Complex.I))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (⟪χ, (gnsPoincareRep Wfn).U (PoincareGroup.translation' a) ψ⟫_ℂ)) := by
  sorry
```

The file comment is accurate: this is not blocked by GNS algebra, but by a
missing partial boundary-value / partial smearing theorem.

## Main Diagnosis

The current project already has:

1. strong continuity of the GNS translation action;
2. expansion of pre-Hilbert inner products into finite sums of Wightman
   pairings;
3. analytic continuation of each `W_n` to the full forward tube via
   `Wfn.spectrum_condition`;
4. fixed-`ε` integrability of forward-tube boundary integrals.

What is still missing is the theorem that says:

- if one starts with the forward-tube holomorphic function for `W_n`,
- and smears against Schwartz variables in all but one complex translation
  variable,
- then the resulting one-variable function is holomorphic on the one-point
  forward tube and has the expected distributional boundary values.

That is the actual hard seam in this theorem.

## Recommended Proof Shape

The proof should be split into two stages:

1. prove the statement for dense pre-Hilbert vectors represented by Borchers
   sequences;
2. extend to arbitrary GNS vectors by approximation.

The first stage is the substantive one. The second should be a standard density
argument once the right partial-smearing theorem exists.

## Stage 1: Dense-Vector Formula

Let:

- `χ = (pF : PreHilbertSpace Wfn)`
- `ψ = (pG : PreHilbertSpace Wfn)`

with Borchers representatives `F` and `G`.

Then the real-translation matrix coefficient

```text
a ↦ ⟪pF, (gnsPoincareRep Wfn).U (PoincareGroup.translation' a) pG⟫
```

should be expanded as a finite sum of Wightman pairings. This is the same
finite-sum mechanism already used in the translation-continuity part of
`GNSHilbertSpace.lean`.

At the representative level, each summand should be expressible as

```text
Wfn.W N (translated_test(a))
```

for some `N` and some Schwartz test obtained from the chosen Borchers data.

## Stage 2: Candidate Holomorphic Continuation of One Summand

For a fixed summand, the candidate holomorphic continuation should be defined
by smearing the analytic continuation `(Wfn.spectrum_condition N).choose` in all
variables except the external translation variable.

Schematically:

```text
H(z) = ∫ x, (Wfn.spectrum_condition N).choose (lift x z) * Φ(x)
```

where:

- `z : ComplexSpacetime d` is the complex translation variable;
- `x` denotes the remaining real variables;
- `lift x z` inserts `z` into the full `N`-point configuration;
- `Φ` is the Schwartz test built from the Borchers data.

On the boundary `z = a + i ε η`, this should recover the translated Wightman
pairing by the boundary-value clause of `Wfn.spectrum_condition`.

## Stage 3: Missing Theorem to Add

The proof should not try to re-prove holomorphicity from scratch inside
`GNSHilbertSpace.lean`. The right move is to isolate a reusable theorem in the
Wick-rotation / forward-tube layer.

The missing theorem should have the following shape:

```lean
theorem partial_smear_forwardTube_holomorphic
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_bv : ...)
    (Φ : SchwartzNPoint d (n - 1)) :
    ∃ H : ComplexSpacetime d → ℂ,
      DifferentiableOn ℂ H (TranslationForwardTube d) ∧
      ...
```

The boundary-value conclusion should say that `H(a + i ε η)` tends to the
corresponding partially smeared distributional pairing as `ε → 0+` for
`η ∈ OpenForwardLightCone`.

This is exactly the theorem needed to turn the input
`Wfn.spectrum_condition` into the one-point matrix-element statement.

## Stage 4: Dense-Vector Holomorphicity

Assuming the theorem above, each finite-sum summand admits a one-point
holomorphic continuation with the correct boundary values.

Then:

- finite sums preserve `DifferentiableOn`;
- finite sums preserve the boundary-value convergence.

So one obtains the theorem for pre-Hilbert vectors directly.

## Stage 5: Extension to Arbitrary GNS Vectors

After the dense-vector theorem is available, extend from the dense image of
`PreHilbertSpace Wfn` to all of `GNSHilbertSpace Wfn`.

The natural route is:

1. approximate `χ` and `ψ` by pre-Hilbert vectors `χ_n`, `ψ_n`;
2. let `F_n` be the dense-vector holomorphic continuations;
3. use strong continuity of translations and continuity of the inner product to
   identify the boundary values of the limit candidate;
4. use local normal-family style control, or a project-specific boundedness
   lemma if available, to pass to a holomorphic limit.

This last step is standard analytically but heavier than the dense-vector
argument. If it becomes awkward in Lean, a reasonable intermediate refactor is
to state the holomorphic matrix-element theorem first on the dense
pre-Hilbert domain.

## Practical Conclusion

The theorem is not primarily blocked by GNS machinery. It is blocked by the
absence of a theorem saying:

- forward-tube holomorphicity survives partial Schwartz smearing, and
- the expected one-point boundary values are recovered.

Once that theorem exists, the rest of the proof should be:

1. quotient induction on Borchers representatives;
2. finite-sum expansion of matrix coefficients;
3. termwise application of the partial-smearing theorem;
4. optional extension from dense vectors to all Hilbert vectors.

## Recommendation

Do not try to prove `gns_matrix_coefficient_holomorphic_axiom` directly in
`GNSHilbertSpace.lean`.

Instead:

1. add the reusable partial-smearing theorem in the forward-tube / Wick-rotation
   layer;
2. prove the dense pre-Hilbert matrix-element version;
3. decide afterwards whether the final theorem should quantify over all Hilbert
   vectors or only over a canonical dense invariant domain.

## Gemini Feedback

Review obtained via local `gemini` CLI in headless mode.

### Verdict

Gemini judged the strategy **highly recommended** and agreed that the real
blocker is the missing partial-smearing theorem, not the GNS algebra.

### Strengths

- The strategy isolates the analytic continuation work in a reusable
  forward-tube layer rather than embedding it in `GNSHilbertSpace.lean`.
- It correctly diagnoses the gap between `Wfn.spectrum_condition` on full
  `n`-point functions and the one-point translation matrix-element statement.
- The dense Borchers / pre-Hilbert route followed by completion is the right
  structural approach.

### Concerns

- The dense-to-completion step may require an explicit boundedness input for the
  holomorphic continuations, not just pointwise boundary convergence.
- In practice this means one may need a contraction-style lemma on the forward
  tube, or else the final theorem may need to stay on a dense invariant domain
  for now.
- The partial-smearing theorem will likely need to reuse the flattening and
  coordinate infrastructure already developed in the forward-tube distribution
  layer.

### Concrete Suggestions

- Put the missing theorem in the forward-tube / distribution layer, likely near
  `ForwardTubeDistributions.lean`, not in `GNSHilbertSpace.lean`.
- Split the missing analytic input into two reusable theorems if needed:
  one for holomorphicity after partial smearing and one for recovery of the
  boundary value.
- Reuse the existing flattening infrastructure there instead of introducing a
  fresh ad hoc coordinate setup locally in the GNS file.

## Claude Review (2026-04-01)

### Overall Assessment

The strategy is **sound and well-structured**. The core diagnosis — that the
blocker is a missing partial-smearing theorem, not GNS algebra — is confirmed
by inspection of the codebase. The five-stage decomposition
(dense-vector formula → candidate continuation → missing theorem →
dense-vector holomorphicity → completion extension) is the right proof
architecture.

Below are observations grounded in the current code, along with refinements
and warnings about implementation details the strategy leaves underspecified.

### Staleness

The theorem has moved to line 1247 (not 993). The `sorry` annotation in
`docs/gns-pipeline-sorries.md` still says `GNSHilbertSpace.lean:993`. This
should be updated once the line numbers stabilize.

### What the Codebase Already Provides

The strategy was written before several pieces of infrastructure matured.
These now-existing pieces should be leveraged directly:

1. **`schwartz_bv_to_flat_repr`** (`ForwardTubeDistributions.lean:843`):
   transports a continuous boundary-value witness `T : SchwartzNPoint d n → ℂ`
   into a weak `HasFourierLaplaceRepr` on the flattened tube. This is
   exactly the bridge from product-coordinate BV data to the SCV layer.

2. **`HasFourierLaplaceRepr` / `HasFourierLaplaceReprRegular`**
   (`SCV/LaplaceSchwartz.lean`): the right abstraction levels. The weak
   version carries only the distributional boundary value; the regular
   version adds polynomial growth, uniform bounds, and boundary continuity.
   The partial-smearing theorem will need to produce a *regular* instance
   on the one-point tube from the *regular* instance on the n-point tube.

3. **`boundary_value_recovery_forwardTube_of_flatRegular`**: recovers
   `T f = ∫ F(x) f(x) dx` from a regular FL representation. This is
   the template for the boundary-value clause of the partial-smearing
   theorem.

4. **`WightmanFunctions.spectrum_condition`** (`Core.lean:578`): provides
   `W_analytic` holomorphic on `ForwardTube d n` with *distributional*
   boundary values recovering `W n`. The distributional (not pointwise)
   form is the right input for smearing.

5. **Flattening infrastructure**: both
   `ForwardTubeDistributions.lean` (public `flattenCLEquiv`, `flattenCLEquivReal`,
   `flattenSchwartzNPoint`) and `GNSHilbertSpace.lean` (private
   `flattenCLEquivRealLocal`, `flattenSchwartzNPointLocal`) exist.

### Duplicate Flattening Infrastructure

`GNSHilbertSpace.lean` lines 920–960 define private copies
(`flattenLinearEquivLocal`, `flattenCLEquivRealLocal`,
`flattenSchwartzNPointLocal`, etc.) that duplicate the public versions in
`ForwardTubeDistributions.lean`. The partial-smearing theorem should use the
**public** versions, and the GNS file should either import and use those or
be refactored to eliminate the duplication. Otherwise the two coordinate
systems will need reconciliation lemmas that add friction for no benefit.

### Refining the Missing Theorem's Signature

The strategy proposes (Stage 3):

```lean
theorem partial_smear_forwardTube_holomorphic
    (F : (Fin n → Fin (d + 1) → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (ForwardTube d n))
    (hF_bv : ...)
    (Φ : SchwartzNPoint d (n - 1)) :
    ∃ H : ComplexSpacetime d → ℂ,
      DifferentiableOn ℂ H (TranslationForwardTube d) ∧ ...
```

This needs several refinements:

**a. The "one variable" is not one n-point component.**
The matrix coefficient `⟨χ, U(a) ψ⟩` involves *simultaneous* translation
of all spacetime arguments by the same vector `a`. After expanding into
Wightman pairings, each summand has the form

```
W_N(x₁ - a, x₂ - a, ..., x_N - a)
```

so by translation invariance the dependence on `a` is through the
*difference variables* `ξ_k = x_k - x_{k+1}`. The "one complex variable"
in `TranslationForwardTube d` is therefore a common shift of all imaginary
parts, not a coordinate of the n-point configuration. The coordinate
embedding `lift x z` in the strategy's schematic formula needs to reflect
this: one does not literally "insert z into one slot" of an n-point
configuration. Instead, one shifts every imaginary part by the same
`Im(z)`, which means the candidate holomorphic continuation should be
something like

```
H(z) = ∫ ξ, W_analytic(ξ₁ + z, ξ₂ + z, ..., ξ_{N-1} + z) Φ(ξ) dξ
```

where `ξ` are the `N - 1` independent difference variables and `Φ` is the
Schwartz test obtained from the Borchers data after the change to difference
coordinates.

The signature should therefore parametrise the "injection" map explicitly,
and its domain should be difference-variable Schwartz space, not raw
`SchwartzNPoint d (n - 1)`.

**b. `hF_bv` should be `HasFourierLaplaceReprRegular`.**
The distributional boundary value alone (`HasFourierLaplaceRepr`) is
insufficient to prove holomorphicity of the smeared integral — one needs
the polynomial growth bounds to justify differentiation under the integral
sign. The right hypothesis is the regular version, which also gives the
uniform bounds needed for dominated convergence in the boundary-value
recovery step.

Whether `Wfn.spectrum_condition` (which only gives the *weak* distributional
BV) can be upgraded to a regular FL representation is a separate question.
If not, the partial-smearing theorem may need to accept the regularity input
as a separate hypothesis, to be supplied from the OS linear growth condition
via the existing `schwartz_bv_to_flat_repr` → regularity upgrade path.

**c. Integrability conditions.**
The smearing integral `∫ W_analytic(lift(ξ, z)) Φ(ξ) dξ` is only
well-defined if the integrand is integrable for each `z` in the tube.
This follows from the polynomial growth of `W_analytic` in real variables
(a consequence of regularity) and the rapid decay of `Φ`, but it must be
proved as a standalone lemma. The existing
`polynomial_growth_forwardTube_of_flatRegular` in
`ForwardTubeDistributions.lean` is the right ingredient.

### Where to Put the Theorem

The strategy and Gemini both recommend placing the partial-smearing theorem
near `ForwardTubeDistributions.lean`. This is correct. Specifically:

- The integrability and holomorphicity-under-integral lemmas belong in
  `ForwardTubeDistributions.lean` (they are generic forward-tube statements).
- The boundary-value recovery clause may need a short bridge lemma in
  `GNSHilbertSpace.lean` to connect the generic result to the specific
  Borchers-representative expansion.

### Stage 5 (Dense-to-Completion): Practical Warning

Gemini's concern about needing explicit boundedness is correct and worth
elaborating. The standard argument requires:

1. **Uniform bound on the family `{F_n}`**: the holomorphic continuations
   for approximating pre-Hilbert vectors must be locally uniformly bounded
   on the tube. This follows from the polynomial growth estimate if the
   approximation is norm-controlled.

2. **Montel's theorem**: locally uniformly bounded holomorphic functions on
   a tube domain form a normal family, so subsequential convergence to a
   holomorphic limit is automatic.

3. **Identification of the limit**: the boundary values of the limit must
   be identified with `⟨χ, U(a) ψ⟩` for the actual GNS vectors.

In Lean, Montel's theorem is not in Mathlib (as of v4.28.0). This means
the dense-to-completion step cannot be proved with current infrastructure.

**Recommendation**: state the holomorphic matrix-element theorem first on
the dense pre-Hilbert domain only:

```lean
theorem gns_matrix_coefficient_holomorphic_preHilbert
    (χ ψ : PreHilbertSpace Wfn) :
    ∃ F : ComplexSpacetime d → ℂ,
      DifferentiableOn ℂ F (TranslationForwardTube d) ∧ ...
```

This suffices for the `MatrixElementSpectralCondition` if the condition is
weakened to quantify over a dense invariant domain rather than all Hilbert
vectors. Since the Stone theorem only needs the spectral condition on a
core domain, this is mathematically sufficient for reconstruction.

The full-Hilbert-space version can be added later when Montel's theorem
(or an ad hoc Phragmen-Lindelof argument) becomes available.

### Finite-Sum Expansion (Stage 1)

The strategy correctly says the matrix coefficient expands as a finite sum
of Wightman pairings. The relevant infrastructure already exists:

- `WightmanInnerProduct` (in `Core.lean`) defines the bilinear form as a
  double sum over Borchers-sequence components.
- `inner_translate_eq_wip` (`GNSHilbertSpace.lean:1041`) bridges from the
  GNS inner product to `WightmanInnerProduct` for translated pre-Hilbert
  vectors.

The expansion is therefore already in place for the dense-vector case. Each
summand has the form `Wfn.W (n + m) (F_n.conjTensorProduct (translated G_m))`,
and the analytic continuation should be applied termwise using
`Wfn.spectrum_condition (n + m)`.

### Summary of Actionable Steps

1. **Unify flattening infrastructure**: either make the GNS-local copies
   import the public versions from `ForwardTubeDistributions.lean`, or prove
   they are definitionally equal.

2. **Prove integrability of forward-tube functions against Schwartz tests**:
   a standalone lemma in `ForwardTubeDistributions.lean` using polynomial
   growth from `HasFourierLaplaceReprRegular`.

3. **Prove holomorphicity-under-integral for forward-tube smearing**: the
   core of the partial-smearing theorem. Needs differentiation under the
   integral sign, justified by the polynomial growth + rapid Schwartz decay.

4. **Prove boundary-value recovery for the smeared function**: show
   `H(a + iεη) → ⟨χ, U(a) ψ⟩` by passing the limit inside the integral
   (dominated convergence from the uniform bound).

5. **Assemble the dense pre-Hilbert version**: quotient induction +
   finite-sum expansion + termwise application of (3–4).

6. **Defer Stage 5** (dense-to-completion) until Montel's theorem or an
   equivalent compactness tool is available.

### Risk Assessment

| Component | Difficulty | Mathlib readiness |
|-----------|-----------|-------------------|
| Finite-sum expansion | Low | Ready (existing infrastructure) |
| Integrability lemma | Medium | Needs polynomial-growth + Schwartz decay pairing |
| Holomorphicity under integral | High | Needs complex differentiation under integral (partially available via `DifferentiableOn` + `HasDerivAt` in Mathlib) |
| Boundary-value recovery | Medium | Dominated convergence is in Mathlib; uniform bound needs the FL regularity |
| Dense-to-completion | Blocked | Montel's theorem not in Mathlib |

### Verdict

Proceed with Stages 1–4 targeting only the pre-Hilbert domain. The
partial-smearing theorem should be stated with `HasFourierLaplaceReprRegular`
hypotheses and placed in `ForwardTubeDistributions.lean`. Stage 5 should be
deferred as a separate axiom or sorry until Montel infrastructure exists.
