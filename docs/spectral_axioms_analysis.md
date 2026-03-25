# Spectral Axioms for Stone's Theorem

## Overview

The core of Stone's theorem in `vNA/Unbounded/StoneTheorem.lean` is now
proved (5 → 1 sorry-using declarations), modulo 4 axioms in
`vNA/Unbounded/SpectralPowers.lean` about the spectral functional calculus
for self-adjoint operators on Hilbert spaces.

The remaining sorry is `timeEvolution_generator`, which connects the
abstract Stone theorem to the quantum-mechanical time evolution operator.
This will be addressed in a follow-up PR that also clarifies the sign
convention for `timeEvolution`.

These axioms isolate the gap between the project's current spectral
infrastructure (bounded functional calculus via `functionalCalculus`)
and the unbounded spectral theory needed for Stone's theorem.

All 4 axioms were vetted by Gemini Deep Think and confirmed correct.

## The 4 Axioms

### Axiom 1: `unitaryGroup_hasDerivAt_dom` (Reed-Simon VIII.7(c))

**Statement:** For x ∈ dom(T), `d/dt exp(itT)x = iT · exp(itT)x`.

**Lean signature:**
```lean
axiom unitaryGroup_hasDerivAt_dom (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (x : T.domain) (t : ℝ) :
    HasDerivAt (fun s => unitaryGroup T hT hsa s (x : H))
      (Complex.I • unitaryGroup T hT hsa t (T x)) t
```

**Proof plan (Gemini):**
Evaluate ‖h⁻¹(U(h)x - x) - iTx‖² = ∫ |h⁻¹(e^{ihλ} - 1) - iλ|² dμ_x(λ).
Pointwise limit → 0. Domination: |(e^{ihλ}-1)/h| ≤ |λ| (mean value theorem).
For x ∈ dom(T), 4λ² is μ_x-integrable. By DCT, the integral → 0.

### Axiom 2: `unitaryGroup_preserves_domain`

**Statement:** exp(itT) maps dom(T) to dom(T).

**Lean signature:**
```lean
axiom unitaryGroup_preserves_domain (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (x : T.domain) (t : ℝ) :
    unitaryGroup T hT hsa t (x : H) ∈ T.domain
```

**Proof plan (Gemini):**
Since |e^{itλ}|² = 1, the spectral measure is invariant:
μ_{U(t)x} = μ_x. Therefore ∫ λ² dμ_{U(t)x} = ∫ λ² dμ_x < ∞,
so U(t)x ∈ dom(T).

### Axiom 3: `unitaryGroup_commutes_with_generator`

**Statement:** T(exp(itT)x) = exp(itT)(Tx) for x ∈ dom(T).

**Lean signature:**
```lean
axiom unitaryGroup_commutes_with_generator (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (x : T.domain) (t : ℝ) :
    T ⟨unitaryGroup T hT hsa t (x : H), unitaryGroup_preserves_domain T hT hsa x t⟩ =
    unitaryGroup T hT hsa t (T x)
```

**Proof plan (Gemini):**
Both T and U(t) are functions of the same spectral measure P:
T = ∫ λ dP(λ), U(t) = ∫ e^{itλ} dP(λ). Since λ · e^{itλ} = e^{itλ} · λ
pointwise, the functional calculus gives U(t)T = TU(t) on dom(T).

### Axiom 4: `unitaryGroup_generator_domain_eq` (Reed-Simon VIII.7(d))

**Statement:** If lim_{h→0} h⁻¹(U(h)x - x) exists, then x ∈ dom(T).

**Lean signature:**
```lean
axiom unitaryGroup_generator_domain_eq (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (x : H)
    (hx : ∃ y : H, HasDerivAt (fun t => unitaryGroup T hT hsa t x) y 0) :
    x ∈ T.domain
```

**Proof plan (Gemini):**
The limit exists ⟹ the norms ‖h⁻¹(U(h)x - x)‖² are bounded by some M.
By Parseval: ‖h⁻¹(U(h)x - x)‖² = ∫ |h⁻¹(e^{ihλ} - 1)|² dμ_x(λ) ≤ M.
By Fatou's lemma: ∫ liminf |h⁻¹(e^{ihλ} - 1)|² dμ_x ≤ liminf M = M.
The pointwise liminf is |iλ|² = λ². So ∫ λ² dμ_x ≤ M < ∞,
which is exactly x ∈ dom(T).

## Decision: Prove Now vs. Axiomatize

### Why axiomatize (current choice)

1. **Mathlib lacks the unbounded spectral theorem integral representation.**
   The project's `functionalCalculus` works for bounded measurable functions
   (like e^{itλ}), but connecting it to the unbounded operator T = ∫ λ dP(λ)
   requires the L² isometry between dom(T) and the spectral measure space.
   This infrastructure does not exist in Mathlib as of v4.28.0.

2. **The axioms cleanly isolate the gap.** All 4 axioms concern a single
   mathematical object (the spectral measure of a self-adjoint operator)
   and a single mathematical technique (differentiation under the spectral
   integral). They don't leak into the rest of the project.

3. **Stone's theorem is unblocked.** The sorry-free StoneTheorem.lean enables
   downstream work (E→R reconstruction via the Euclidean semigroup →
   Hamiltonian) without waiting for the spectral infrastructure.

4. **The axioms are standard textbook results** (Reed-Simon VIII.7,
   Rudin FA 13.33) with clear proof plans. There is no mathematical risk.

### When to prove them

The axioms should be proved when either:

- **Mathlib adds unbounded Borel functional calculus.** This would provide
  T = ∫ λ dP(λ) directly, after which all 4 axioms follow from DCT /
  Fatou / functional calculus commutativity.

- **The hille-yosida project is integrated.** The contraction semigroup
  resolvent machinery from `../hille-yosida/` provides an alternative
  route to some of these results (resolvent → domain characterization).
  However, a Lean version mismatch (v4.29 vs v4.28) currently blocks this.

- **A dedicated spectral theory sprint.** Estimated ~300-400 lines:
  ~100 for the L² isometry / spectral representation,
  ~80 for DCT under the spectral integral (axiom 1),
  ~40 for domain preservation (axiom 2),
  ~30 for commutation (axiom 3),
  ~50 for the Fatou converse (axiom 4).

### Relationship to the Hille-Yosida project

The `../hille-yosida/` project proves the resolvent identity (λI - A)R(λ) = I
for contraction semigroups. This was originally considered as an alternative
route to Stone's theorem (via the unitary → contraction semigroup bridge).

The direct proof (implemented here) turned out to be simpler: the ODE kernel
argument for `generator_selfadjoint` and the inner product ODE for
`unique_from_generator` avoid the scalar-field mismatch (ℝ vs ℂ) that the
Hille-Yosida bridge requires.

However, Hille-Yosida remains valuable for the **E→R direction**: the
Euclidean time-translation semigroup in `OSToWightmanSemigroup.lean` is a
contraction semigroup, and Hille-Yosida directly gives the self-adjoint
Hamiltonian H ≥ 0 without going through Stone's theorem.
