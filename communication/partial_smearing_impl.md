# Partial-Smearing Implementation Plan

**Goal**: Fill the `sorry` in `gns_matrix_coefficient_holomorphic_axiom`
(GNSHilbertSpace.lean:1247) by building the missing partial-smearing
infrastructure and wiring it into the GNS finite-sum expansion.

**Scope**: Pre-Hilbert domain only (dense vectors). The extension to
all GNS Hilbert vectors is deferred — it requires Montel's theorem,
which is not in Mathlib.

---

## 0. Prerequisite: Unify Flattening Infrastructure

**Problem**: `GNSHilbertSpace.lean` (lines 920–960) has private copies
of the flattening maps (`flattenLinearEquivLocal`, `flattenCLEquivRealLocal`,
`flattenSchwartzNPointLocal`) that duplicate the public versions in
`ForwardTubeDistributions.lean`.

**Action**: Add `import OSReconstruction.Wightman.Reconstruction.ForwardTubeDistributions`
to `GNSHilbertSpace.lean` and replace private copies with the public
`flattenCLEquivReal`, `flattenSchwartzNPoint`, etc. Verify that the
existing proofs (`poincareActNPoint_translationInDirection_eq_unflatten_translate`,
`continuous_translate_npoint_schwartz`, etc.) still work after the swap.

**Risk**: Low. The definitions should be definitionally equal. If not,
a one-line `simp` lemma equating them suffices.

**Files touched**: `GNSHilbertSpace.lean`

---

## 1. Integrability of Forward-Tube Functions Against Schwartz Tests

**What**: Given a forward-tube holomorphic function `F` with regular FL
representation, and a Schwartz test `Φ`, prove the pointwise product
`F(x + iy) · Φ(x)` is integrable in `x` for each fixed `y` in the cone.

**Signature** (in `ForwardTubeDistributions.lean`):

```lean
theorem integrable_forwardTube_smear {d n : ℕ} [NeZero d]
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    (hRegular : SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (F ∘ (flattenCLEquiv n (d + 1)).symm))
    (Φ : SchwartzNPoint d n)
    (y : Fin n → Fin (d + 1) → ℝ) (hy : y ∈ ForwardConeAbs d n) :
    MeasureTheory.Integrable
      (fun x : NPointDomain d n =>
        F (fun k μ => ↑(x k μ) + ↑(y k μ) * Complex.I) * Φ x) := ...
```

**Proof sketch**: Use `polynomial_growth_forwardTube_of_flatRegular` to
get `‖F(x + iy)‖ ≤ C · (1 + ‖x‖)^N` for `y` in a compact subset of
the cone containing the given point. Then the integrand is bounded by
`C · (1 + ‖x‖)^N · |Φ(x)|`, which is integrable because Schwartz
functions decay faster than any polynomial.

**Existing ingredients**:
- `polynomial_growth_forwardTube_of_flatRegular` (ForwardTubeDistributions.lean:792)
- `SchwartzMap.integrable` (Mathlib)
- Polynomial × Schwartz integrability (may need a short helper)

**File**: `ForwardTubeDistributions.lean`

---

## 2. Holomorphicity Under the Integral (Core Theorem)

**What**: Given `F` holomorphic on the forward tube with regular FL input,
and a Schwartz test `Φ`, the function

```
H(z) = ∫ ξ, F(ξ₁ + z, ξ₂ + z, ..., ξ_{n-1} + z) · Φ(ξ) dξ
```

is holomorphic on the one-point translation forward tube
`TranslationForwardTube d`.

Here `ξ` are the difference-coordinate variables (see below for the
coordinate setup) and `z` is the common complex translation.

**Why this form**: The matrix coefficient `⟨χ, U(a)ψ⟩` involves
simultaneous translation of *all* spacetime points by the same `a`.
After expanding into Wightman pairings, each summand is

```
W_{n+m}(x₁ - a, ..., x_{n+m} - a)
```

By translation invariance, the dependence on `a` is only through an
overall shift. In difference coordinates `ξₖ = xₖ - x_{k-1}`, the
translation acts as a shift of the "zeroth" absolute coordinate while
leaving differences unchanged. So the holomorphic continuation shifts
every argument by the same `z`:

```
H(z) = ∫ ξ, W_analytic(ξ₁ + z, ..., ξ_{n+m-1} + z, z) · Φ(ξ) dξ
```

Equivalently, in absolute coordinates with translation invariance folded in:

```
H(z) = ∫ x, W_analytic(x₁ + z, ..., x_N + z) · Ψ(x) dx
```

where `Ψ` is the test function from the Borchers data with one fewer
degree of freedom.

**Signature** (in `ForwardTubeDistributions.lean`):

```lean
theorem holomorphic_forwardTube_smear {d n : ℕ} [NeZero d]
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    (hRegular : SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (F ∘ (flattenCLEquiv n (d + 1)).symm))
    (Φ : SchwartzNPoint d n)
    -- The injection map: z ↦ (x₁ + z, ..., xₙ + z)
    (inject : ComplexSpacetime d → NPointDomain d n →
              (Fin n → Fin (d + 1) → ℂ))
    (h_inject_holo : ∀ x, DifferentiableOn ℂ (fun z => inject z x) (TranslationForwardTube d))
    (h_inject_tube : ∀ x z, z ∈ TranslationForwardTube d →
                     inject z x ∈ ForwardTube d n) :
    DifferentiableOn ℂ
      (fun z => ∫ x : NPointDomain d n, F (inject z x) * Φ x)
      (TranslationForwardTube d)
```

**Proof sketch**: Differentiation under the integral sign. For each
`z₀ ∈ TranslationForwardTube d`:
1. The integrand `x ↦ F(inject z x) · Φ(x)` is integrable (Lemma 1).
2. For `z` near `z₀`, the derivative `∂/∂z F(inject z x)` exists and is
   bounded by `C(z₀) · (1 + ‖x‖)^N` uniformly in a neighbourhood of `z₀`
   (from polynomial growth on a compact sub-cone).
3. The dominating function `C(z₀) · (1 + ‖x‖)^N · |Φ(x)|` is integrable.
4. Apply Mathlib's `hasFDerivAt_integral_of_dominated_of_fderiv_le` or
   the simpler `DifferentiableOn` variant.

**Existing ingredients**:
- `polynomial_growth_forwardTube_of_flatRegular` (polynomial bound on F)
- `MeasureTheory.hasFDerivAt_integral_of_dominated_of_fderiv_le` (Mathlib)
- Integrability from Lemma 1

**Difficulty**: High — this is the hardest step. The Mathlib differentiation-
under-integral theorems require careful setup of the dominating function
and the measurability/differentiability hypotheses.

**File**: `ForwardTubeDistributions.lean`

---

## 3. Boundary-Value Recovery for the Smeared Function

**What**: Show that for `η ∈ OpenForwardLightCone d`,

```
lim_{ε→0⁺} H(a + iεη) = ⟨χ, U(a)ψ⟩
```

where `H` is the holomorphic function from Lemma 2.

**Proof sketch**:
1. Expand `H(a + iεη)`:
   ```
   H(a + iεη) = ∫ x, F(x₁ + a + iεη, ..., xₙ + a + iεη) · Φ(x) dx
   ```
2. By the distributional boundary-value condition from
   `Wfn.spectrum_condition`, the integrand converges pointwise to
   `W_N(x₁ + a, ..., xₙ + a) · Φ(x)` as `ε → 0⁺`.
3. By the uniform polynomial bound (`uniform_bound` from
   `HasFourierLaplaceReprRegular`), a dominating function
   `C · (1 + ‖x‖)^N · |Φ(x)|` works for all small `ε`.
4. By dominated convergence, the integral converges to
   `∫ x, W_N(x₁ + a, ..., xₙ + a) · Φ(x) dx`, which by
   `boundary_value_recovery_forwardTube_of_flatRegular_from_bv` equals
   `W_N(translated test)`.
5. The last expression equals the Wightman pairing of the translated
   Borchers data, which equals `⟨χ, U(a)ψ⟩`.

**Signature**:

```lean
theorem boundary_value_forwardTube_smear {d n : ℕ} [NeZero d]
    {F : (Fin n → Fin (d + 1) → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F (ForwardTube d n))
    (hRegular : SCV.HasFourierLaplaceReprRegular (ForwardConeFlat d n)
      (F ∘ (flattenCLEquiv n (d + 1)).symm))
    {T : SchwartzNPoint d n → ℂ}
    (hT_cont : Continuous T)
    (h_bv : ∀ (f : SchwartzNPoint d n) (η : Fin n → Fin (d + 1) → ℝ),
      InForwardCone d n η → Filter.Tendsto
        (fun ε : ℝ => ∫ x, F (fun k μ => ↑(x k μ) + ε * ↑(η k μ) * Complex.I) * f x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (T f)))
    (Φ : SchwartzNPoint d n)
    (inject : ComplexSpacetime d → NPointDomain d n → (Fin n → Fin (d + 1) → ℂ))
    (a : MinkowskiSpace d)
    (η : MinkowskiSpace d) (hη : η ∈ MinkowskiSpace.OpenForwardLightCone d) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ x, F (inject (fun μ => ↑(a μ) + ε * ↑(η μ) * Complex.I) x) * Φ x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (T (translated_test Φ a)))   -- exact form TBD
```

**Existing ingredients**:
- `boundary_value_recovery_forwardTube_of_flatRegular_from_bv` (ForwardTubeDistributions.lean:1040)
- `MeasureTheory.tendsto_integral_of_dominated_convergence` (Mathlib)
- `HasFourierLaplaceReprRegular.uniform_bound`

**File**: `ForwardTubeDistributions.lean`

---

## 4. Coordinate Setup: Translation Injection Map

**What**: Define the specific injection map used by the GNS argument:
given a complex translation `z` and real smearing variables `x`, produce
the n-point configuration `(x₁ + z, ..., xₙ + z)`.

**Existing infrastructure**:
- `BHW.diffCoordEquiv` (`ComplexLieGroups/DifferenceCoordinates.lean`) —
  the difference-coordinate linear equivalence
- `BHW.partialSumFun` — inverse (partial sums)
- `BHW.forwardTube_eq_diffCoord_preimage` — forward tube in difference coords

**What to build**:

```lean
/-- Injection of a common complex translation z into an n-point configuration:
    given real smearing variables x, produce (x₁ + z, ..., xₙ + z). -/
def translationInject (n : ℕ) (d : ℕ) (z : ComplexSpacetime d)
    (x : NPointDomain d n) : Fin n → Fin (d + 1) → ℂ :=
  fun k μ => ↑(x k μ) + z μ
```

Then prove:
- `translationInject_holomorphic`: for fixed `x`, `z ↦ translationInject z x`
  is differentiable (it's affine — trivial).
- `translationInject_forwardTube`: if `z ∈ TranslationForwardTube d` then
  `translationInject z x ∈ ForwardTube d n` (the imaginary part of each
  successive difference is `Im(z) - Im(z) = 0` except for the overall
  shift, so this needs the forward-tube definition to be compatible).

**Warning**: The second point requires care. `ForwardTube d n` demands that
successive *imaginary differences* lie in `V₊`. If all imaginary parts
equal `Im(z) ∈ V₊`, then the successive differences are zero for `k > 0`
and `Im(z)` for `k = 0`. Zero is *not* in the open forward light cone.

This means the naive injection `x ↦ (x₁ + z, ..., xₙ + z)` does NOT
land in `ForwardTube d n` for `n ≥ 2`.

**Resolution**: The correct approach uses translation invariance to reduce
from `W_N(x₁ + z, ..., x_N + z)` to the *difference-variable* formulation.
By `Wfn.translation_invariant`, `W_N` depends only on the `N - 1`
differences `ξₖ = x_{k+1} - x_k`. The holomorphic continuation of the
reduced (N-1)-point function of differences lives on
`ForwardTube d (N - 1)`, and the common translation `z` acts only as an
overall shift that drops out by translation invariance.

So the actual proof path is:
1. Use `Wfn.translation_invariant` to rewrite each Wightman summand in
   difference variables.
2. The analytic continuation of the reduced function is holomorphic on
   `ForwardTube d (N - 1)`, which is a product tube domain in difference
   coordinates.
3. The smearing integral is over the `N - 1` difference variables.
4. No injection into the full `N`-point forward tube is needed — the
   one-point holomorphic continuation comes from the *reduced* function
   of differences, where the common translation `a` is a free real parameter
   that analytically continues to `z ∈ TranslationForwardTube d` separately.

**Alternative**: If the codebase already has the Wightman functions in
difference coordinates (via `WightmanAnalyticity` which provides
`analyticContinuation n` on `ForwardTube d n`), one can instead use the
direct construction:
- For the matrix coefficient, the relevant function is `W_{n+m}` evaluated
  at the tensor product test. The `n + m` absolute coordinates split into
  `n + m - 1` independent differences plus one overall translation.
- The overall translation analytically continues to `z`.
- The remaining `n + m - 1` differences are integrated against the
  Schwartz test.

This avoids needing an explicit difference-coordinate Wightman function.

**File**: `ForwardTubeDistributions.lean` (generic part),
`GNSHilbertSpace.lean` (GNS-specific wiring)

---

## 5. Assembly: Pre-Hilbert Matrix Coefficient Holomorphicity

**What**: Prove `gns_matrix_coefficient_holomorphic_axiom` for pre-Hilbert
vectors.

**Proof outline**:
1. By quotient induction (`Quotient.inductionOn`), reduce to Borchers
   representatives `F`, `G` for `χ`, `ψ`.
2. Use `inner_translate_eq_wip` (GNSHilbertSpace.lean:1041) to rewrite:
   ```
   ⟨χ, U(a)ψ⟩ = WightmanInnerProduct Wfn.W F (translated G)
              = ∑_n ∑_m Wfn.W(n+m)(F_n.conjTensorProduct (translated G_m))
   ```
3. For each summand, use `Wfn.spectrum_condition (n + m)` to get the
   analytic continuation `W_analytic`.
4. Define the candidate holomorphic continuation of the summand as the
   smeared integral from Lemma 2.
5. Apply `holomorphic_forwardTube_smear` (Lemma 2) for holomorphicity.
6. Apply `boundary_value_forwardTube_smear` (Lemma 3) for boundary values.
7. Sum over finite `n`, `m` — finite sums preserve `DifferentiableOn` and
   boundary-value convergence.
8. The total `H(z) = ∑_n ∑_m H_{n,m}(z)` is holomorphic on
   `TranslationForwardTube d` with the correct boundary values.

**Existing ingredients**:
- `WightmanInnerProduct` / `inner_translate_eq_wip` (finite-sum expansion)
- `Wfn.spectrum_condition` (analytic continuation of each `W_N`)
- `DifferentiableOn.sum` (Mathlib — finite sums preserve holomorphicity)
- `Filter.Tendsto.sum` (Mathlib — finite sums preserve limits)

**File**: `GNSHilbertSpace.lean`

---

## 6. Dense-to-Completion Extension (Deferred)

**Status**: Blocked on Montel's theorem (not in Mathlib).

**Current approach**: The theorem statement quantifies over
`GNSHilbertSpace Wfn` (all Hilbert vectors). Two options:

**(a)** Keep the current statement and bridge with a `sorry` or explicit
axiom for the completion step. The pre-Hilbert case is proved honestly;
only the density/approximation argument is deferred.

**(b)** Weaken `MatrixElementSpectralCondition` to quantify over a dense
invariant domain (the image of `PreHilbertSpace Wfn`). This is
mathematically sufficient for Stone's theorem on a core and avoids the
need for Montel entirely.

**Recommendation**: Option (a) for now — it preserves the current API surface
and localises the remaining `sorry` to a single, well-understood gap.

---

## Dependency Graph

```
[0] Unify flattening
 │
 ▼
[1] Integrability lemma ──────────────────┐
 │                                         │
 ▼                                         ▼
[2] Holomorphicity under integral    [3] Boundary-value recovery
 │                                         │
 └────────────┬────────────────────────────┘
              │
              ▼
        [4] Coordinate setup (translation injection / difference vars)
              │
              ▼
        [5] Assembly in GNSHilbertSpace.lean
              │
              ▼
        [6] Dense-to-completion (deferred)
```

---

## Files Modified / Created

| File | Action |
|------|--------|
| `GNSHilbertSpace.lean` | Add import of ForwardTubeDistributions; remove private flattening copies; fill sorry in assembly (Step 5) |
| `ForwardTubeDistributions.lean` | Add Lemmas 1–3 and the injection/coordinate infrastructure (Steps 1–4) |

No new files needed.

---

## Regularity Gap: `spectrum_condition` → `HasFourierLaplaceReprRegular`

`Wfn.spectrum_condition` provides only the *weak* distributional BV
(an existential `W_analytic` with `DifferentiableOn` and distributional
convergence). The partial-smearing theorems (Lemmas 2–3) require
`HasFourierLaplaceReprRegular`, which adds:
- Polynomial growth on compact sub-cones
- Uniform boundary bound
- Boundary continuity
- Interior-to-boundary continuity

**How to bridge**: The existing `schwartz_bv_to_flat_repr`
(ForwardTubeDistributions.lean:843) transports the weak BV into a weak
FL representation. The upgrade to *regular* requires either:

**(i)** An explicit regularity theorem: forward-tube holomorphic functions
arising from Wightman functions have polynomial growth (this is a
consequence of the Jost-Lehmann-Dyson representation and is known in the
physics literature but not formalised).

**(ii)** Adding the regularity as a hypothesis to `WightmanFunctions`,
e.g., strengthening `spectrum_condition` to provide the regular FL package
directly.

**(iii)** Using `HasFourierLaplaceReprTempered` (LaplaceSchwartz.lean:143)
as an intermediate — it has polynomial growth and uniform bounds but not
boundary continuity. This may suffice for Lemmas 2–3, which only need the
growth bounds for differentiation under the integral.

**Recommendation**: Option (iii) if possible, falling back to (ii). Do not
attempt (i) — it requires deep Fourier analysis not in Mathlib.
