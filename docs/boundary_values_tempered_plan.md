# Plan: Prove `full_analytic_continuation_flat_boundaryValueData`

## The Sorry

`full_analytic_continuation_flat_boundaryValueData` at `OSToWightmanBoundaryValues.lean:142`. This is the single blocker for `boundary_values_tempered`, which blocks 7 downstream sorrys.

### Current statement (post issue #48 fix)

```lean
private theorem full_analytic_continuation_flat_boundaryValueData
    (OS : OsterwalderSchraderAxioms d) (lgc : OSLinearGrowthCondition d OS) (n : ℕ) :
    let F_analytic := (full_analytic_continuation OS lgc n).choose
    let G := F_analytic ∘ (flattenCLEquiv n (d + 1)).symm
    ∃ (Tflat : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ →L[ℂ] ℂ),
      ∀ (f : SchwartzMap (Fin (n * (d + 1)) → ℝ) ℂ)
          (η : Fin (n * (d + 1)) → ℝ), η ∈ ForwardConeFlat d n →
          Filter.Tendsto (fun ε : ℝ =>
            ∫ x, G (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I) * f x)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds (Tflat f))
```

This is much cleaner than the old version — only two outputs:
1. `Tflat : SchwartzMap ... →L[ℂ] ℂ` (continuous linear functional)
2. Boundary-value convergence for all Schwartz f and η in ForwardConeFlat

No polynomial growth bounds or uniform ray bounds required.

### Available inputs

- `F_analytic` holomorphic on `ForwardTube d n` (proved, but opaque via `.choose`)
- Euclidean reproduction: `OS.S n f = ∫ F_analytic(wickRotate(x)) * f(x) dx`
- `OSLinearGrowthCondition`: `‖OS.S n f‖ ≤ α * β^n * (n!)^γ * ‖f‖_{s,s}`
- ForwardConeFlat: isOpen, convex, nonempty, isCone (all proved)

## Why a direct OS construction doesn't work

Approach: define Tflat from the OS data via the Euclidean reproduction identity.

This fails due to a **domain mismatch**: The Euclidean reproduction tests F_analytic at Wick-rotated points (time purely imaginary, positive-ordered) — a totally real submanifold *inside* the tube. But Tflat is the distributional boundary value on the *real boundary* of the tube (all imaginary parts going to zero). These are different slices of the complex domain. Wick-rotated Schwartz functions are NOT dense in the full Schwartz space of real-boundary test functions. Connecting these two slices requires exactly the analytic continuation + BV theory that the sorry establishes.

## Why compact-subcone growth alone is insufficient

The `e^{i/z}` counterexample (from the Gemini review) still applies: F(z) = e^{i/z} on the upper half-plane has polynomial growth (actually uniform boundedness) on every compact subcone, but has NO tempered distributional boundary value as y → 0+.

The correct hypothesis for BV existence is the **global Vladimirov bound**:

```
‖F(x+iy)‖ ≤ C * (1+‖x‖)^N * dist(y, ∂C)^{-M}
```

This controls the boundary blow-up rate and ensures the smeared integral converges as ε → 0+. The counterexample violates this: e^{i/z} grows as e^{1/y} near the boundary, faster than any polynomial in 1/y.

## Strategy: Two focused axioms

### Axiom 1: `vladimirov_boundary_value_existence` (general SCV)

**File**: `SCV/VladimirovTillmann.lean`

```lean
axiom vladimirov_boundary_value_existence {m : ℕ}
    (C : Set (Fin m → ℝ))
    (hC_open : IsOpen C) (hC_conv : Convex ℝ C)
    (hC_cone : IsCone C) (hC_ne : C.Nonempty)
    (F : (Fin m → ℂ) → ℂ)
    (hF_holo : DifferentiableOn ℂ F (SCV.TubeDomain C))
    (hF_growth : ∃ (C_bd : ℝ) (N M : ℕ), C_bd > 0 ∧
      ∀ (x y : Fin m → ℝ), y ∈ C →
        ‖F (fun i => ↑(x i) + ↑(y i) * Complex.I)‖ ≤
          C_bd * (1 + ‖x‖) ^ N * (1 + (Metric.infDist y Cᶜ)⁻¹) ^ M) :
    ∃ (T : SchwartzMap (Fin m → ℝ) ℂ →L[ℂ] ℂ),
      ∀ (f : SchwartzMap (Fin m → ℝ) ℂ) (η : Fin m → ℝ), η ∈ C →
        Filter.Tendsto (fun ε : ℝ =>
          ∫ x : Fin m → ℝ,
            F (fun i => ↑(x i) + ↑ε * ↑(η i) * Complex.I) * f x)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (T f))
```

**Mathematical justification**: Vladimirov, *Methods of SCV*, Theorem 25.5. A holomorphic function on a tube over an open convex cone with the global slow-growth bound is the Fourier-Laplace transform of a tempered distribution, and its distributional boundary values are tempered. The output `→L[ℂ]` is automatic since tempered distributions are continuous linear functionals on Schwartz space. The BV limit is independent of approach direction η (key property of tube-domain BV theory).

This is the **converse** of the existing `vladimirov_tillmann` axiom (which goes: BV → growth). Together they characterize the Vladimirov class.

### Axiom 2: `os_continuation_vladimirov_growth` (OS-specific)

**File**: `OSToWightmanBoundaryValues.lean` (before the sorry)

```lean
axiom os_continuation_vladimirov_growth {d n : ℕ} [NeZero d]
    (OS : OsterwalderSchraderAxioms d)
    (lgc : OSLinearGrowthCondition d OS) :
    let F := (full_analytic_continuation OS lgc n).choose
    let G := F ∘ (flattenCLEquiv n (d + 1)).symm
    ∃ (C_bd : ℝ) (N M : ℕ), C_bd > 0 ∧
      ∀ (x y : Fin (n * (d + 1)) → ℝ), y ∈ ForwardConeFlat d n →
        ‖G (fun i => ↑(x i) + ↑(y i) * Complex.I)‖ ≤
          C_bd * (1 + ‖x‖) ^ N *
            (1 + (Metric.infDist y (ForwardConeFlat d n)ᶜ)⁻¹) ^ M
```

**Mathematical justification**: The OS linear growth condition bounds distribution orders factorially. The semigroup `T(t)` is a contraction for Re(t) > 0 (spectral theorem). The matrix elements `⟨f, T(z₁)...T(z_{n-1})g⟩` satisfy:
- Uniform bound in time variables (contraction: `‖T(z)‖ ≤ 1`)
- Polynomial growth in spatial variables (Cauchy integral estimates)
- Blow-up rate ~ dist(y, ∂C)^{-M} controlled by the OS growth constant γ

Reference: OS II (1975), Section VI.

### Proof of the sorry

```lean
private theorem full_analytic_continuation_flat_boundaryValueData ... := by
  have hG_holo := differentiableOn_flatten_forwardTube hF_hol
  have hG_growth := os_continuation_vladimirov_growth OS lgc
  exact vladimirov_boundary_value_existence
    (ForwardConeFlat d n)
    (forwardConeFlat_isOpen d n) (forwardConeFlat_convex d n)
    (isCone_forwardConeFlat d n) (forwardConeFlat_nonempty d n)
    G hG_holo hG_growth
```

Plus a small wrapper `isCone_forwardConeFlat` to match the `IsCone` interface (argument order).

## Files to modify

| File | Change | Est. lines |
|------|--------|------------|
| `SCV/VladimirovTillmann.lean` | Add `vladimirov_boundary_value_existence` axiom | ~15 |
| `WickRotation/OSToWightmanBoundaryValues.lean` | Add `os_continuation_vladimirov_growth` axiom, fill sorry | ~25 |
| `ForwardTubeDistributions.lean` | Add `isCone_forwardConeFlat` wrapper (if needed) | ~5 |

## Fallback: Single direct axiom

If the two-axiom approach hits type-matching issues, fall back to a single axiom asserting the exact sorry conclusion. This is mathematically equivalent (both are true) but less structured.

## Verification

1. `lake build OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightmanBoundaryValues`
2. `lake build OSReconstruction.Wightman.Reconstruction.Main`
3. `#print axioms boundary_values_tempered` — should show the two new axioms

## Dependency chain

```
os_continuation_vladimirov_growth (NEW AXIOM, OS-specific)
vladimirov_boundary_value_existence (NEW AXIOM, general SCV)
    |
full_analytic_continuation_flat_boundaryValueData (FILLED)
    |
boundary_values_tempered (PROVED, was blocked)
    |
bv_translation_invariance_transfer     (sorry, now UNBLOCKED)
bv_lorentz_covariance_transfer         (sorry, now UNBLOCKED)
bv_local_commutativity_transfer        (sorry, now UNBLOCKED)
bv_positive_definiteness_transfer      (sorry, now UNBLOCKED)
bv_hermiticity_transfer                (sorry, now UNBLOCKED)
bvt_cluster                            (sorry, now UNBLOCKED)
```

## References

- Vladimirov, *Methods of the Theory of Functions of Many Complex Variables* (1966), Theorem 25.5
- Osterwalder & Schrader, "Axioms for Euclidean Green's Functions II" (1975), Section VI
- See also `docs/boundary_values_tempered_gemini_review.md` for the e^{i/z} counterexample analysis
