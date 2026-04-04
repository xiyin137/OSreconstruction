# `gns_spectrum_condition` Strategy Note

## Context

This note records my recommendation for how to approach
`gns_spectrum_condition` in
`OSReconstruction/Wightman/Reconstruction/GNSHilbertSpace.lean`.

The immediate issue is that the current theorem statement and the current
formal infrastructure are misaligned.

## Main Diagnosis

The present target

```lean
theorem gns_spectrum_condition :
    SpectralCondition d (gnsPoincareRep Wfn) := by
  sorry
```

looks like a standard Wightman-spectrum theorem, but the current formalization
does not yet have the right operator-theoretic objects to support it.

In particular:

1. `SpectralCondition` is currently phrased using
   `π.hamiltonian` and `π.spatialMomentum` as total maps on the whole Hilbert
   space.
2. Those operators are presently defined via `limUnder` of the translation
   difference quotient.
3. `PoincareRepresentation` does not itself yet package strong continuity of the
   translation subgroups.
4. Without strong continuity and Stone's theorem, the `limUnder` definition is
   not the genuine self-adjoint generator of translations.
5. Therefore the existing target is not just hard; it is slightly premature as a
   formal statement.

## Recommendation

I would not try to prove the current statement directly.

I would first refactor the target so the formal theorem matches the
infrastructure that is actually available.

## Recommended Refactor

### Option A: Best long-term statement

Replace the current `SpectralCondition` with a statement directly about the
translation representation, for example:

- there exists a joint spectral measure for the translation generators, and
- its support is contained in the closed forward light cone.

This is the mathematically correct final form, but it requires substantial
unbounded spectral theory in Lean.

### Option B: Best short-term Lean-feasible statement

Introduce a weaker reconstruction theorem at the level of translation matrix
elements:

- for dense vectors `x y`, the function `a ↦ ⟪x, U(a) y⟫`
- admits a forward-tube holomorphic continuation or equivalent boundary-value
  formulation
- inherited from the input `Wfn.spectrum_condition`.

This is much closer to the actual data already present in `WightmanFunctions`.

## Suggested Proof Program

### Stage 1: Prove strong continuity of the GNS translation action

Show that for each `μ` and each GNS vector `ψ`, the map

```text
t ↦ U(translationInDirection d μ t) ψ
```

is continuous.

Sketch:

1. Prove continuity first on Borchers / pre-Hilbert vectors.
2. Reduce matrix elements to finite sums of continuous expressions built from
   translated Schwartz functions.
3. Use continuity of translation on Schwartz space and continuity of each `W_n`
   from `Wfn.tempered`.
4. Extend from the dense pre-Hilbert subspace to the Hilbert completion.

### Stage 2: Prove matrix-element analyticity for GNS vectors

For dense vectors represented by Borchers sequences `F, G`, expand

```text
⟪[F], U(a)[G]⟫
```

as a finite sum of Wightman distributions applied to translated tensor-product
test functions.

Then apply the input analytic continuation
`Wfn.spectrum_condition` term-by-term to obtain forward-tube analyticity.

### Stage 3: Bridge analytic matrix elements to spectral support

Add the missing functional-analysis theorem:

If a strongly continuous unitary translation representation has matrix elements
with the forward-tube boundary-value property, then its joint spectrum is
contained in the closed forward cone.

This is the actual Stone / spectral-theorem bridge that is missing today.

### Stage 4: Recover positivity consequences

Once the genuine self-adjoint generators `P_μ` and their supported joint
spectral measure are available, derive:

- `⟪ψ, P₀ ψ⟫.re ≥ 0`
- `⟪ψ, P₀² ψ⟫.re ≥ Σᵢ ⟪ψ, Pᵢ² ψ⟫.re`

as standard corollaries of support in the forward cone.

## Practical Conclusion

There are two sensible paths.

### Path 1: Honest short-term progress

Change the theorem to a matrix-element spectral condition and prove that now.

This is probably the best next move if the goal is to reduce the current
`sorry` count with mathematically faithful intermediate infrastructure.

### Path 2: Keep the current theorem

Keep `gns_spectrum_condition` as-is, but accept that it is blocked on new
infrastructure:

- strong continuity packaging for the GNS translation action
- Stone's theorem
- spectral theory for commuting unbounded self-adjoint operators

## Bottom Line

My recommendation is:

1. refactor `SpectralCondition` away from total `limUnder`-defined momentum maps
2. prove the matrix-element / forward-tube version first
3. only later upgrade it to the full joint-spectrum statement once the needed
   functional analysis infrastructure exists

This keeps the formal statement honest and matches the actual reconstruction
data already present in the project.

## Gemini Feedback

Review obtained via local `gemini` CLI in headless mode.

Notes:

- The default model hit quota and auto-retried without succeeding promptly.
- The successful review was obtained with `-m gemini-2.5-flash`.
- Gemini CLI reported a `keytar` module issue and fell back to file-backed
  credential storage, then used cached OAuth credentials successfully.

### Verdict

The strategy outlined in `gns_spectrum_condition_strategy.md` is mathematically
sound and presents a pragmatic, phased approach to a complex formalization
challenge. The diagnosis of the current state and the proposed refactoring are
appropriate for a project aiming for rigorous formal verification in Lean.

### Strengths

- **Accurate diagnosis:** The note correctly identifies that the current
  `gns_spectrum_condition` statement is premature because the project does not
  yet package strong continuity for translation subgroups and does not yet have
  Stone's theorem connecting the `limUnder` definitions to genuine self-adjoint
  generators.
- **Pragmatic refactor recommendation:** Gemini agreed that the matrix-element
  based spectral condition is a strong intermediate target because it supports
  mathematically correct progress without requiring full unbounded spectral
  theory immediately.
- **Clear phased proof program:** Gemini judged the four-stage structure
  coherent and manageable, with each stage building naturally on the previous
  one.
- **Correct focus on infrastructure:** Gemini agreed that the missing
  functional-analysis infrastructure is the real blocker, rather than a defect
  in the QFT-side reconstruction setup.

### Concerns

- **Stage 3 remains substantial:** The bridge from analytic matrix elements to
  spectral support is itself a major theorem and may require a significant
  formalization effort in Lean.
- **Definitions for the intermediate statement matter:** The exact Lean
  formulation of forward-tube holomorphic continuation and boundary-value
  properties will need to be pinned down carefully.
- **Upstream dependency on `Wfn.spectrum_condition`:** The usefulness of Stage 2
  depends on how strong and how usable the current `Wfn.spectrum_condition`
  input already is.

### Concrete Suggestions

1. Prioritize Stage 1 and fully formalize strong continuity of the GNS
   translation action before attempting later stages.
2. Decompose Stage 3 into smaller mathematical lemmas so the true scope of the
   spectral-support bridge is explicit.
3. Introduce precise Lean definitions for forward-tube holomorphic continuation
   and the associated boundary-value property.
4. Audit the current `Wfn.spectrum_condition` statement and proof status to make
   sure it really supplies the input needed for Stage 2.
5. Consider introducing an intermediate proposition such as
   `MatrixElementSpectralCondition` to keep the weaker but provable target
   separate from the eventual full joint-spectrum statement.
6. Before planning a full unbounded-operator project, re-check Mathlib for any
   usable existing infrastructure around unbounded operators, Stone's theorem,
   or spectral measures.
