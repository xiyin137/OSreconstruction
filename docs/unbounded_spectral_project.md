# Unbounded Spectral Theorem: Project Plan

## The gap

No Lean formalization exists for the **spectral theorem for unbounded
self-adjoint operators** — the result that every self-adjoint operator T
on a Hilbert space has a unique projection-valued measure P such that
T = ∫ λ dP(λ).

This is the single piece of infrastructure blocking the 4 axioms in
`vNA/Unbounded/SpectralPowers.lean` that underpin the sorry-free
Stone's theorem.

## What exists

### In this project (`OSReconstruction/vNA/`)

| File | What's there | Status |
|------|-------------|--------|
| `Spectral/CayleyTransform.lean` | Cayley transform U = (T-i)(T+i)⁻¹ | Proved |
| `Spectral/SpectralViaCayleyRMK.lean` | PVM for bounded self-adjoint via RMK chain | Proved |
| `Spectral/SigmaAdditivity.lean` | σ-additivity of spectral projections | Proved |
| `MeasureTheory/SpectralIntegral.lean` | Integration against spectral measures (bounded f) | Proved |
| `Unbounded/Spectral.lean` | `spectralMeasure`, `functionalCalculus` (bounded Borel f) | Partially proved |
| `Unbounded/SpectralPowers.lean` | `unitaryGroup` = ∫ e^{itλ} dP, powers T^s | 4 axioms + 2 sorrys |

The Cayley transform maps T to a unitary U, and the bounded spectral
theorem gives a PVM for U. The missing step: pull the PVM back through
the Cayley transform to get T = ∫ λ dP(λ) as an unbounded operator.

### In Mathlib

- **Continuous functional calculus (CFC)** for C*-algebras: `f(a)` for
  continuous f on the spectrum of a normal element. Algebraic approach,
  bounded operators only.
  [Docs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Basic.html)

- **Bochner integration**, **dominated convergence theorem**: available and
  used throughout the project.

- **No PVM infrastructure, no unbounded spectral integrals.**

### In the Lean ecosystem

- **[SpectralThm](https://github.com/oliver-butterley/SpectralThm)** by
  Butterley & Tanimoto: Spectral theorem for **bounded** normal operators.
  93 commits, Lean v4.27, last updated Jan 2026. Does not cover unbounded
  operators or PVMs.

- **No other Lean project covers the unbounded spectral theorem.**

## What needs to be built

### Layer 1: Spectral representation on dom(T) (~100 lines)

**Goal:** For x ∈ dom(T), show Tx = ∫ λ dP(λ)x where P is the spectral
measure already constructed in `Spectral.lean`.

**Approach:** The project already constructs P via Cayley + RMK. The
Cayley transform maps T to U = (T-i)(T+i)⁻¹, and the spectral measure
of U (via Stieltjes/RMK) pulls back to give P for T. The key identity:

    T = i(1 + U)(1 - U)⁻¹ = ∫ λ dP(λ)

where P(E) = P_U(φ⁻¹(E)) and φ(θ) = i(1 + e^{iθ})/(1 - e^{iθ}) is
the inverse Cayley map on the unit circle.

**Deliverable:** A theorem
```lean
theorem spectral_representation (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (x : T.domain) :
    T x = spectralIntegral (T.spectralMeasure hT hsa) id x
```

where `spectralIntegral P f x = ∫ f(λ) dP_x(λ)` (the existing
`functionalCalculus` extended to unbounded f on dom(T)).

**Dependencies:** Need to show the Cayley pullback gives the right P,
and that the unbounded spectral integral converges for x ∈ dom(T).

### Layer 2: Domain characterization (~50 lines)

**Goal:** x ∈ dom(T) ⟺ ∫ λ² d⟨P(λ)x, x⟩ < ∞.

**Approach:** Forward: if x ∈ dom(T), then ‖Tx‖² = ∫ λ² dμ_x by
Parseval applied to the spectral representation.
Converse: if the integral is finite, construct Tx as the limit of
∫_{-n}^{n} λ dP(λ)x (truncated spectral integrals converge by
monotone convergence).

**Deliverable:**
```lean
theorem mem_domain_iff_square_integrable (T : UnboundedOperator H)
    (hT : T.IsDenselyDefined) (hsa : T.IsSelfAdjoint hT) (x : H) :
    x ∈ T.domain ↔ ∫ λ², d⟨P(λ)x, x⟩ < ∞
```

### Layer 3: Differentiation under the spectral integral (~80 lines)

**Goal:** Prove `unitaryGroup_hasDerivAt_dom` (Axiom 1).

**Approach:** Standard DCT argument:
1. ‖h⁻¹(U(h)x - x) - iTx‖² = ∫ |h⁻¹(e^{ihλ} - 1) - iλ|² dμ_x(λ)
2. Pointwise limit: integrand → 0
3. Domination: |h⁻¹(e^{ihλ} - 1)| ≤ |λ| (mean value theorem)
4. For x ∈ dom(T): 4λ² is μ_x-integrable (Layer 2)
5. DCT → integral → 0

**Key Mathlib ingredient:** `MeasureTheory.tendsto_integral_of_dominated_convergence`

### Layer 4: Domain preservation and commutation (~40 lines)

**Goal:** Prove Axioms 2 and 3.

**Axiom 2** (`unitaryGroup_preserves_domain`):
Since |e^{itλ}|² = 1, μ_{U(t)x} = μ_x. So ∫ λ² dμ_{U(t)x} =
∫ λ² dμ_x < ∞. By Layer 2, U(t)x ∈ dom(T).

**Axiom 3** (`unitaryGroup_commutes_with_generator`):
Both T and U(t) are functions of P: T = ∫ λ dP, U(t) = ∫ e^{itλ} dP.
Functional calculus multiplicativity: (fg)(T) = f(T)g(T). Since
λ · e^{itλ} = e^{itλ} · λ, we get TU(t) = U(t)T on dom(T).

### Layer 5: Converse spectral differentiation (~50 lines)

**Goal:** Prove Axiom 4 (`unitaryGroup_generator_domain_eq`).

**Approach:** If lim h⁻¹(U(h)x - x) exists, the norms are bounded:
∫ |h⁻¹(e^{ihλ} - 1)|² dμ_x ≤ M. By Fatou's lemma
(`MeasureTheory.lintegral_liminf_le`): ∫ λ² dμ_x ≤ M < ∞.
By Layer 2: x ∈ dom(T).

## Estimated effort

| Layer | Lines | Dependencies |
|-------|-------|-------------|
| 1. Spectral representation | ~100 | Cayley pullback, existing PVM |
| 2. Domain characterization | ~50 | Layer 1, Parseval |
| 3. Spectral differentiation (Axiom 1) | ~80 | Layer 2, Mathlib DCT |
| 4. Domain preservation + commutation (Axioms 2-3) | ~40 | Layers 1-2, functional calculus |
| 5. Converse differentiation (Axiom 4) | ~50 | Layer 2, Fatou's lemma |
| **Total** | **~320** | |

## Decision: when to do this

### Option A: Dedicated sprint in this project

Extend `Spectral.lean` with Layer 1 (spectral representation), then
prove axioms in `SpectralPowers.lean`. Estimated 2-3 focused sessions.
Pros: eliminates 4 axioms, self-contained.
Cons: large scope, touches deep spectral infrastructure.

### Option B: Separate Reservoir project

Create a standalone project `UnboundedSpectral` that proves Layers 1-5
and exports the results. Import as a Lake dependency.
Pros: reusable, could merge with Butterley-Tanimoto SpectralThm.
Cons: dependency management, version alignment.

### Option C: Wait for Mathlib

Mathlib's CFC team (Jireh Loreaux et al.) may eventually extend from
bounded to unbounded operators. The PVM approach is orthogonal to the
algebraic CFC approach, so this could take a while.
Pros: upstream quality.
Cons: uncertain timeline.

### Option D: Axiomatize and move on (current choice)

The 4 axioms cleanly isolate the gap. Stone's theorem and the E→R
reconstruction chain are unblocked. Prove the axioms later via A, B, or C.
Pros: immediate progress on physics.
Cons: 4 axioms in the trusted base.

## Relationship to other projects

### Hille-Yosida (`../hille-yosida/`)

The resolvent R(λ) = (λI - A)⁻¹ from Hille-Yosida connects to the
spectral theory via Stone's formula:
P([a,b]) = s-lim (1/π) ∫_a^b Im(R(λ + iε)) dλ as ε → 0.
This is an alternative construction of the PVM that avoids the Cayley
transform. Could provide a second route to the spectral representation.

### SpectralThm (Butterley-Tanimoto)

Their bounded spectral theorem could be extended to unbounded operators
via the Cayley transform bridge. The RMK-based PVM construction in this
project's `Spectral/SpectralViaCayleyRMK.lean` already does this
partially — a collaboration could close the remaining gap.

### Mathlib CFC

The continuous functional calculus for C*-algebras is algebraic (not
measure-theoretic). Extending it to unbounded operators requires the
affiliated-operator framework, which is a large project. The PVM
approach (our route) is more direct for the specific needs of
quantum field theory.
