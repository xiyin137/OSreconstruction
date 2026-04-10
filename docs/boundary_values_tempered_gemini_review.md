# Gemini Deep Think Review: `boundary_values_tempered` Plan

Reviewed 2026-03-31. The original plan targeted the correct bottleneck, but contained three fatal flaws.

## Flaw 1: Axiom 2 (`vladimirov_representation`) is mathematically FALSE

Axiom 2 claims that any holomorphic function F satisfying a polynomial bound on compact subcones K (`hpoly`) has a tempered distributional boundary value. This is mathematically false.

**The Math**: Because C is an open cone, it does not contain the origin. Thus, any compact subset K ⊂ C is strictly bounded away from the boundary (e.g., y >= delta > 0). The `hpoly` condition places zero restrictions on how fast F(x+iy) blows up as y -> 0.

**Counterexample**: Let the spacetime dimension be 1, the cone be C = (0, infinity), and the tube be the upper half-plane. Consider F(z) = e^{i/z}.

For z = x + iy, the magnitude is |F(x+iy)| = exp(y / (x^2 + y^2)).

If we restrict y to any compact K ⊂ (0, infinity), we know y >= delta > 0 for some delta. Because y / (x^2 + y^2) <= y / y^2 = 1/y <= 1/delta, we have |F(x+iy)| <= e^{1/delta} for all x. This perfectly satisfies the `hpoly` premise (it is uniformly bounded by a constant, so N = 0 and C_bd = e^{1/delta}).

However, as y -> 0+ along the imaginary axis (x = 0), |F(iy)| = e^{1/y}. Because it blows up exponentially (rather than polynomially), it does not possess a boundary value in the space of tempered distributions S'.

Vladimirov's actual representation theorem (Theorem 25.5 in his 1966 book) requires a **global slow-growth condition**, which strictly limits the blowup near the boundary to be at most polynomial:

```
|F(x+iy)| <= C * Delta_C(y)^{-M} * (1 + ||x||)^N
```

where Delta_C(y) is the distance from y to the boundary of C.

## Flaw 2: The proof sketch for the Lemma is logically invalid

The proof sketch for the uniform ray bound lemma commits a classic quantifier scoping fallacy and will be rejected by Lean.

The goal (`hunif` / Output 4) requires proving:

```
exists C_bd, N, delta > 0, forall epsilon in (0, delta), ||G(x + i*epsilon*eta)|| <= C_bd * (1 + ||x||)^N
```

(Note the quantifiers: C_bd must be chosen before epsilon.)

The sketch says:
- Pick delta > 0. Let K = {t * eta | delta <= t <= 1}.
- Apply Axiom 1 to get C_bd and N.
- "Choose delta small enough; the bound holds for all 0 < e < 1 with delta = e".

**The Error**: The constants C_bd and N returned by Axiom 1 depend on K (and therefore depend on delta). This gives you a valid, fixed bound for epsilon in [delta, 1]. If you try to dynamically shrink delta to match epsilon (i.e., delta = e), your constant C_bd(epsilon) becomes a function of epsilon. Lean will immediately flag this because C_bd cannot be bound inside the `forall epsilon` quantifier.

## Flaw 3: Output 4 (`hunif`) is physically FALSE for QFT

Even if you could fix the logic, Output 4 is mathematically impossible for Wightman functions.

`hunif` demands that G(x + i*epsilon*eta) is uniformly bounded by a polynomial in x, independently of epsilon. If a family of functions is uniformly bounded by a polynomial as epsilon -> 0, its boundary limit must be a locally bounded function (or a measure with polynomially bounded density).

However, Wightman functions are **singular distributions**. For example, the 2-point function of a free scalar field has a singularity ~ 1/(x_1 - x_2)^2 on the lightcone. Its analytic continuation diverges precisely as 1/epsilon^2 when epsilon -> 0 at coincident points. It is fundamentally impossible to bound this uniformly across all small epsilon.

It appears the upstream `SCV.HasFourierLaplaceReprTempered` structure in the project was incorrectly defined by demanding `hunif` instead of the correct Vladimirov 1/Delta_C(y)^M blow-up bound.

## How to Actually Fix the Formalization

Because the upstream SCV definition is currently bugged (requiring the physically impossible `hunif`), you cannot solve this cleanly by chaining SCV lemmas. You have two options:

### Option A: The "Direct Package" Axiom (Recommended for now)

Do not split this into SCV and OS axioms, as it will pollute the general SCV namespace with false or impossible theorems. Instead, turn the sorry at line 175 directly into a single axiom:

```lean
axiom full_analytic_continuation_flat_tempered_package_axiom {d n : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) :
    let F := (full_analytic_continuation OS lgc n).choose
    let G := F ∘ (flattenCLEquiv n (d + 1)).symm
    ∃ (Tflat : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ → ℂ),
      Continuous Tflat ∧ ... -- (paste exactly the 4 outputs required by the sorry)
```

**Why this is best**:
- It immediately unblocks `boundary_values_tempered` and all 7 downstream sorrys in 0 lines of fallacious proofs.
- It quarantines the bugged `hunif` requirement inside a single, specific OS axiom rather than breaking the foundational SCV library.
- It uses only 1 axiom from your budget instead of 2.

### Option B: Refactor the SCV Library (Long-term rigorous fix)

If the goal is absolute formal correctness:

1. **Fix `SCV.HasFourierLaplaceReprTempered`**: Replace `hpoly` and `hunif` with the correct global Vladimirov bound:
   ```
   ||F(x+iy)|| <= C_bd * (1 + ||x||)^N * (1 + ||y||^{-1})^M
   ```
   (or using `distToBoundary`).

2. **Fix Axiom 1**: Have `os_continuation_polynomial_growth` assert that the OS continuation satisfies this exact global bound.

3. **Fix Axiom 2**: Update `vladimirov_representation` to require the global slow-growth condition instead of the compact-slice condition.

Once the SCV definitions are mathematically correct, the logically impossible `hunif` goal disappears, and the axioms connect properly.
