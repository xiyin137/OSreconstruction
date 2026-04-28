# Spectral Theorems for Stone's Theorem

## Overview

**All 4 spectral axioms are now fully proved theorems** (0 sorrys, 0 axioms)
in `vNA/Unbounded/SpectralPowers.lean`.

The core forward route of Stone's theorem in
`vNA/Unbounded/StoneTheorem.lean` is proved, and the spectral axioms it
depended on are now discharged.

Within `StoneTheorem.lean` itself, the main remaining `sorry` is
`timeEvolution_generator`, which connects the abstract Stone theorem to the
time-evolution operator. This will be addressed in a follow-up PR that also
clarifies the sign convention for `timeEvolution`.

## The 4 Proved Theorems

### Theorem 1: `unitaryGroup_hasDerivAt_dom` (Reed-Simon VIII.7(c))

**Statement:** For x ∈ dom(T), `d/dt exp(itT)x = iT · exp(itT)x`.

**Lean signature:**
```lean
theorem unitaryGroup_hasDerivAt_dom (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (x : T.domain) (t : ℝ) :
    HasDerivAt (fun s => unitaryGroup T hT hsa s (x : H))
      (Complex.I • unitaryGroup T hT hsa t (T x)) t
```

**Proof:**
Evaluate ‖h⁻¹(U(h)x - x) - iTx‖² = ∫ |h⁻¹(e^{ihλ} - 1) - iλ|² dμ_x(λ).
Pointwise limit → 0. Domination: |(e^{ihλ}-1)/h| ≤ |λ| (mean value theorem).
For x ∈ dom(T), 4λ² is μ_x-integrable. By DCT, the integral → 0.

### Theorem 2: `unitaryGroup_preserves_domain`

**Statement:** exp(itT) maps dom(T) to dom(T).

**Lean signature:**
```lean
theorem unitaryGroup_preserves_domain (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (x : T.domain) (t : ℝ) :
    unitaryGroup T hT hsa t (x : H) ∈ T.domain
```

**Proof:**
Since |e^{itλ}|² = 1, the spectral measure is invariant:
μ_{U(t)x} = μ_x. Therefore ∫ λ² dμ_{U(t)x} = ∫ λ² dμ_x < ∞,
so U(t)x ∈ dom(T).

### Theorem 3: `unitaryGroup_commutes_with_generator`

**Statement:** T(exp(itT)x) = exp(itT)(Tx) for x ∈ dom(T).

**Lean signature:**
```lean
theorem unitaryGroup_commutes_with_generator (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (x : T.domain) (t : ℝ) :
    T ⟨unitaryGroup T hT hsa t (x : H), unitaryGroup_preserves_domain T hT hsa x t⟩ =
    unitaryGroup T hT hsa t (T x)
```

**Proof:**
Both T and U(t) are functions of the same spectral measure P:
T = ∫ λ dP(λ), U(t) = ∫ e^{itλ} dP(λ). Since λ · e^{itλ} = e^{itλ} · λ
pointwise, the functional calculus gives U(t)T = TU(t) on dom(T).

### Theorem 4: `unitaryGroup_generator_domain_eq` (Reed-Simon VIII.7(d))

**Statement:** If lim_{h→0} h⁻¹(U(h)x - x) exists, then x ∈ dom(T).

**Lean signature:**
```lean
theorem unitaryGroup_generator_domain_eq (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (x : H)
    (hx : ∃ y : H, HasDerivAt (fun t => unitaryGroup T hT hsa t x) y 0) :
    x ∈ T.domain
```

**Proof:**
The limit exists ⟹ the norms ‖h⁻¹(U(h)x - x)‖² are bounded by some M.
By Parseval: ‖h⁻¹(U(h)x - x)‖² = ∫ |h⁻¹(e^{ihλ} - 1)|² dμ_x(λ) ≤ M.
By Fatou's lemma: ∫ liminf |h⁻¹(e^{ihλ} - 1)|² dμ_x ≤ liminf M = M.
The pointwise liminf is |iλ|² = λ². So ∫ λ² dμ_x ≤ M < ∞,
which is exactly x ∈ dom(T).

## How they were proved

All 4 theorems were proved directly using the spectral infrastructure
already in `Spectral.lean` (2613 lines, 0 sorrys), without needing
Mathlib's unbounded Borel functional calculus or the hille-yosida project.

The key bridge: the **resolvent-functional calculus connection**
(`resolvent_eq_functionalCalculus`), which shows (T+i)⁻¹ = fc(1/(·+i)).
This enables:

1. **Spectral truncation convergence** (`spectralTruncation_tendsto`):
   T_n x → Tx via resolvent factoring + DCT.

2. **Domain characterization** (`mem_domain_iff_square_integrable`):
   dom(T) ↔ ∫ λ² dμ_x < ∞, via resolvent preimage + monotone convergence.

3. **Spectral measure invariance** (`diagonalMeasure_unitaryGroup_invariant`):
   μ_{U(t)x} = μ_x, via functional calculus commutativity.

4. **Parseval bridge** (`unitaryGroup_diff_norm_sq`):
   ‖U(h)x-x‖² = ∫ |e^{ihλ}-1|² dμ_x, for Fatou/DCT arguments.

Total: ~3200 lines added to SpectralPowers.lean.

### Relationship to the Hille-Yosida project

The `../hille-yosida/` project proves the resolvent identity (λI - A)R(λ) = I
for contraction semigroups. This was originally considered as an alternative
route to Stone's theorem (via the unitary → contraction semigroup bridge).

The direct proof (implemented here) turned out to be simpler: the ODE kernel
argument for `generator_selfadjoint` and the inner product ODE for
`unique_from_generator` avoid the scalar-field mismatch (ℝ vs ℂ) that the
Hille-Yosida bridge requires.

However, Hille-Yosida remains valuable for the **E→R direction** as the
contraction-semigroup/generator bridge.  It should not be read as the source of
self-adjointness by itself: the checked OS semigroup route in
`OSToWightmanSemigroup.lean` proves positivity of the concrete bounded Hilbert
time-shift operator from the half-shift identity
`osTimeShiftLinear_inner_eq`, then obtains self-adjointness through
`osTimeShiftHilbert_isPositive` and `osTimeShiftHilbert_isSelfAdjoint`.
The lightweight `EuclideanSemigroup` record only stores semigroup,
contraction, and diagonal real-part positivity data, so it is not a standalone
self-adjointness interface.
