# Spectral Condition Definition Review

## Question

Is the `SpectralCondition` structure in `WightmanAxioms.lean` (lines 83–92)
correctly aligned with the Streater–Wightman definition of the spectrum
condition?

## Current Code

```lean
structure SpectralCondition (d : ℕ) [NeZero d]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : PoincareRepresentation d H) : Prop where
  energy_nonneg : ∀ ψ : H, (⟪ψ, π.hamiltonian ψ⟫_ℂ).re ≥ 0
  mass_shell : ∀ ψ : H, (⟪ψ, π.hamiltonian (π.hamiltonian ψ)⟫_ℂ).re ≥
    ∑ i : Fin d, (⟪ψ, π.spatialMomentum i (π.spatialMomentum i ψ)⟫_ℂ).re
```

The operators `hamiltonian` and `spatialMomentum` are defined via `limUnder`
of translation difference quotients (OperatorDistribution.lean, lines 321–348).

## Streater–Wightman Definition (Literature)

In "PCT, Spin and Statistics, and All That" (Streater–Wightman), the spectrum
condition is stated as part of Axiom 0 / W0:

> The support of the joint spectral measure E(·) of the translation subgroup
> U(a) = ∫ e^{ip·a} dE(p) is contained in the closed forward light cone:
>
>   supp E ⊆ V̄₊ = { p ∈ ℝ^{1,d} : p⁰ ≥ 0 and (p⁰)² − |p⃗|² ≥ 0 }

Equivalently, for every state ψ:

   ⟨ψ, U(a) ψ⟩ = ∫_{V̄₊} e^{ip·a} dμ_ψ(p)

where μ_ψ is a positive Borel measure supported on V̄₊.

The vacuum condition P^μ Ω = 0 is not a separate axiom — it follows from
U(a) Ω = Ω for all a, by Stone's theorem.

This spectral-measure formulation is consistent across Jost ("The General
Theory of Quantized Fields"), Haag ("Local Quantum Physics"), and
Reed–Simon.

## Analysis

### Mathematical equivalence

For commuting self-adjoint operators P^μ (generators of the abelian
translation group), the following are equivalent:

1. The joint spectrum lies in V̄₊.
2. P₀ ≥ 0 as an operator AND P₀² − Σᵢ Pᵢ² ≥ 0 as an operator.

This equivalence follows from the joint spectral theorem: if f ≥ 0 on
the joint spectrum, then f(P) ≥ 0 as an operator, and conversely.

The code encodes condition (2) via expectation-value inequalities:
- `energy_nonneg` encodes P₀ ≥ 0
- `mass_shell` encodes P₀² − Σ Pᵢ² ≥ 0

So the **mathematical content is correct** — the code captures the same
physical condition as Streater–Wightman.

### Issue 1: Domain problem

The conditions quantify over **all** ψ : H, but P_μ is unbounded.

`hamiltonian` is defined via `limUnder` (OperatorDistribution.lean:321–323),
which returns a junk value when the limit does not exist. Therefore:

- `π.hamiltonian ψ` is meaningless for ψ ∉ D(P₀)
- `π.hamiltonian (π.hamiltonian ψ)` requires ψ ∈ D(P₀²), which is even
  smaller

The quantification `∀ ψ : H` asks the inequality to hold for junk values,
which is either vacuously problematic or silently wrong.

**Fix:** Restrict to the appropriate domains:
```lean
energy_nonneg : ∀ ψ : H, π.inMomentumDomain 0 ψ →
    (⟪ψ, π.hamiltonian ψ⟫_ℂ).re ≥ 0
mass_shell : ∀ ψ : H,
    π.inMomentumDomain 0 ψ →
    (∀ i, π.inMomentumDomain (Fin.succ i) ψ) →
    -- also need P₀ψ ∈ D(P₀), Pᵢψ ∈ D(Pᵢ)
    (⟪ψ, π.hamiltonian (π.hamiltonian ψ)⟫_ℂ).re ≥
      ∑ i : Fin d, (⟪ψ, π.spatialMomentum i (π.spatialMomentum i ψ)⟫_ℂ).re
```

### Issue 2: Downstream weakness (practical impact)

The expectation-value formulation cannot directly produce the
Fourier–Laplace representation of Wightman functions:

   W_n(ξ₁,...,ξ_{n−1}) = ∫_{V̄₊^{n−1}} e^{ip·ξ} dρ(p₁,...,p_{n−1})

which is the standard route to analytic continuation into the forward tube.

The code itself acknowledges this — the `WightmanAnalyticity` structure
(WightmanAxioms.lean:679–705) must include `boundaryValue` and
`boundaryPointwise` as **separate explicit axioms** rather than deriving
them from `spectrum_condition`.

The spectral-measure formulation would give analytic continuation for free
(the integral with Im ξ ∈ V₊ makes the exponential damped), avoiding the
need for these extra axioms.

### Issue 3: Non-standard presentation

The spectral-measure formulation is the standard one in all major references
(Streater–Wightman, Jost, Haag, Reed–Simon). The expectation-value
formulation, while equivalent, is unusual in the literature.

## Possible Reformulation Options

### Option A: Spectral-measure formulation (ideal but heavy)

```
SpectralCondition :=
  ∃ E : MeasureTheory.Measure (MinkowskiSpace d),
    E.support ⊆ ClosedForwardLightCone d ∧
    ∀ a : MinkowskiSpace d, ∀ ψ : H,
      ⟨ψ, π.U (translation a) ψ⟩ = ∫ e^{ip·a} dμ_ψ(p)
```

Requires: joint spectral measures for commuting self-adjoint operators
(not in Mathlib as of v4.28.0).

### Option B: Matrix-element/boundary-value formulation (practical)

This was already recommended in `gns_spectrum_condition_strategy.md`:

For dense vectors x, y, the function a ↦ ⟨x, U(a) y⟩ has a
Fourier–Laplace representation with support in V̄₊, or equivalently
admits forward-tube holomorphic continuation.

This is closest to the data already available in `WightmanFunctions`.

### Option C: Keep current formulation, fix domains (minimal change)

Add domain hypotheses to `energy_nonneg` and `mass_shell` as described
in Issue 1. Accept the downstream weakness.

## Summary

| Aspect | Status |
|--------|--------|
| Mathematical correctness | Equivalent to S–W, modulo self-adjointness |
| Domain handling | Bug: quantifies over all ψ, needs domain restriction |
| Downstream utility | Weak: can't derive analytic continuation |
| Literature alignment | Non-standard but equivalent formulation |

---

## Gemini Review (gemini-2.5-flash, 2026-03-28)

### 1. Mathematical equivalence

Gemini **agrees** the equivalence is valid but highlights two prerequisites
that must be formally established:

- **Self-adjointness of P_μ**: The `limUnder` definition does not yield
  a proven self-adjoint operator. Stone's theorem (not yet formalized)
  is needed to connect the limit to a genuine self-adjoint generator.
- **Commutativity of P_μ**: Physically expected for generators of an
  abelian translation group, but not formally derived in the codebase.

Without both, the joint spectral theorem cannot be applied.

### 2. Domain issue

Gemini **strongly agrees** this is a real concern, not benign:

- The `∀ ψ : H` quantification over junk `limUnder` values makes the
  axiom mathematically incorrect for ψ outside the domain.
- Downstream proofs would constantly need to re-introduce domain
  assumptions, undermining the purpose of the axiom.
- The existing `WightmanAnalyticity` workaround (separate boundary-value
  axioms) is a direct symptom of this weakness.

### 3. Reformulation recommendation

Gemini recommends **Option C first (fix domains), then Option B
(matrix-element/boundary-value)**:

- Option C is an immediate necessary correction for mathematical soundness.
- Option B offers the best balance of rigor, effort, and utility for
  OS reconstruction — directly provides analytic continuation tools.
- Option A (spectral measures) is the ideal long-term target but blocked
  on Mathlib infrastructure (joint spectral measures for commuting
  unbounded self-adjoint operators).

### 4. Additional issues identified by Gemini

- **Strong continuity missing from `PoincareRepresentation`**: Without it,
  Stone's theorem doesn't apply and P_μ may not be self-adjoint. Should be
  added as a field or axiom.
- **Nested domain requirements for `mass_shell`**: The proposed fix in the
  analysis only ensures ψ ∈ D(P_μ), but `mass_shell` also needs
  P₀ψ ∈ D(P₀) and Pᵢψ ∈ D(Pᵢ). The full domain condition is:
  ```lean
  mass_shell : ∀ ψ : H,
      π.inMomentumDomain 0 ψ →
      π.inMomentumDomain 0 (π.hamiltonian ψ) →
      (∀ i, π.inMomentumDomain (Fin.succ i) ψ) →
      (∀ i, π.inMomentumDomain (Fin.succ i) (π.spatialMomentum i ψ)) →
      ...
  ```
  This is cumbersome and further motivates moving to Option B.

### 5. Minor points from Gemini

- Gemini flagged `vacuum_normalized` and `cyclicity` field types as
  potentially containing file paths rather than Lean symbols. **This is
  a false positive** — the `@norm ... vacuum = 1` and `@Dense ...`
  expressions are valid Lean with explicit universe/instance arguments.
  They appear unusual because of the `@` explicit-everything syntax
  forced by the structure's bundled instances.

---

## Claude Response to Gemini (2026-03-28)

### Points of agreement

I agree with Gemini on all major points:

1. **Mathematical equivalence is valid but conditional** on
   self-adjointness + commutativity, which are not yet formalized.
   This is a fair refinement of my original analysis, which took these
   as implicit.

2. **Domain issue is real** and not just cosmetic. I agree it affects
   both mathematical soundness and downstream usability.

3. **Option C then B** is the right strategy. I concur that fixing
   domains first (Option C) is non-negotiable, and that Option B
   provides the best cost-benefit for the reconstruction pipeline.

4. **Nested domain requirements** for `mass_shell` — Gemini correctly
   caught that my proposed fix was incomplete. The `mass_shell` condition
   requires ψ ∈ D(P₀²) = {ψ ∈ D(P₀) : P₀ψ ∈ D(P₀)}, not just
   ψ ∈ D(P₀). This makes the expectation-value formulation even more
   cumbersome and further motivates Option B.

### Points of refinement

1. **On strong continuity**: Gemini is right that it's missing from
   `PoincareRepresentation`, but I note that for the *Wightman axiom*
   context (as opposed to the GNS reconstruction), strong continuity is
   typically part of the axioms (W1). The current `PoincareRepresentation`
   structure should include it. However, for the `SpectralCondition`
   question specifically, this is an upstream issue — if we adopt Option B,
   the spectral condition becomes a statement about matrix-element
   analyticity, which sidesteps the need for Stone's theorem entirely.

2. **On the false positive**: I confirm Gemini's flag about
   `vacuum_normalized` and `cyclicity` is incorrect. The `@` prefix syntax
   with explicit instances is standard Lean 4 when working with structures
   that bundle their own typeclass instances. The code is syntactically
   valid.

3. **On commutativity**: For the translation generators specifically, the
   commutativity proof would be straightforward once strong continuity
   is available:
   ```
   U(se_μ) U(te_ν) = U(se_μ + te_ν) = U(te_ν + se_μ) = U(te_ν) U(se_μ)
   ```
   by the group homomorphism property and commutativity of vector addition.
   This gives commutativity of the one-parameter groups, from which
   commutativity of the generators follows (by a standard argument using
   strong resolvent convergence or the spectral theorem for individual
   generators). So this is not a deep obstacle, just missing infrastructure.

### Additional observation

There is a **circularity concern** worth flagging: If we adopt Option B
for `SpectralCondition` (matrix-element analyticity), and the
`WightmanAnalyticity` structure also contains `boundaryValue` /
`boundaryPointwise`, then these two structures overlap in content. The
clean resolution would be:

- Make `SpectralCondition` (Option B) the fundamental axiom
- Derive `WightmanAnalyticity.boundaryValue` from it
- Remove the redundancy

This is exactly the payoff of Option B: the spectral condition becomes
strong enough to derive analytic continuation, so `WightmanAnalyticity`
no longer needs separate boundary-value axioms.

---

## Joint Conclusion (Claude + Gemini)

### Diagnosis

The current `SpectralCondition` definition is **mathematically equivalent
to Streater–Wightman** in content, but has three formalization defects:

1. **Domain bug**: Quantifies over all ψ : H including junk values
   from `limUnder` outside operator domains.
2. **Downstream weakness**: Cannot derive analytic continuation / Fourier–
   Laplace representation, forcing `WightmanAnalyticity` to carry
   redundant axioms.
3. **Missing prerequisites**: Self-adjointness and strong continuity
   are not formally established for the momentum operators.

### Recommended Action

**Phase 1 (immediate):** Fix domains in the current `SpectralCondition`
(Option C). Add `inMomentumDomain` hypotheses including nested domain
requirements for `mass_shell`.

**Phase 2 (medium-term):** Reformulate `SpectralCondition` as a
matrix-element/boundary-value condition (Option B). Specifically, for
dense vectors x, y, the matrix element a ↦ ⟨x, U(a) y⟩ admits a
Fourier–Laplace representation with spectral support in V̄₊. This:
- Directly supports analytic continuation
- Aligns with existing `WightmanFunctions` data
- Avoids needing full joint spectral measure theory
- Allows removing redundant axioms from `WightmanAnalyticity`

**Phase 3 (long-term):** Add strong continuity to `PoincareRepresentation`,
formalize Stone's theorem, and work toward Option A (full spectral-measure
formulation) as Mathlib infrastructure matures.

### Open question for the user

Which phase should we prioritize given the current state of the
reconstruction pipeline? Phase 1 is a safe minimal fix; Phase 2 is
a more substantial refactor with bigger payoff.
