# Cluster Property Analysis (R→E Direction)

## Summary

This document describes the work in the `mrdouglasny` fork on the cluster
property (E4) of the R→E direction: given Wightman functions satisfying R4
(cluster decomposition), show the constructed Schwinger functions satisfy E4.

## What was done

### Bug fix

The statement of `bhw_pointwise_cluster_forwardTube` in `SchwingerAxioms.lean`
had `↑(a μ) * Complex.I` (imaginary spatial shift) where `↑(a μ)` (real
spatial shift) was needed.  The imaginary version:
- Breaks PET membership for large |a| (imaginary spatial parts violate the
  forward cone condition η₀ > |η⃗|)
- Doesn't match the downstream consumer `W_analytic_cluster_integral`, which
  translates the test function by a real vector via `g_a(x) = g(x - a)`

### New axiom: `distributional_cluster_lifts_to_tube`

**File:** `SCV/VladimirovTillmann.lean`

A tube-domain SCV axiom stating that distributional cluster on the boundary
lifts to pointwise cluster on the tube interior.

**Hypotheses:**
- C ⊂ ℝᵐ is an open convex salient cone
- F holomorphic on T(C) with distributional BV W (continuous linear functional
  on Schwartz space)
- F₁, F₂ holomorphic on sub-tubes T(C₁), T(C₂) with BVs W₁, W₂
- Distributional cluster (R4 format): for all Schwartz f₁, f₂ and ε > 0,
  ∃ R > 0 such that for |a| > R:
  ‖W(f₁ ⊗ τ_a f₂) - W₁(f₁) · W₂(f₂)‖ < ε

**Conclusion:** For all z₁ ∈ T(C₁), z₂ ∈ T(C₂) with (z₁,z₂) ∈ T(C),
and ε > 0: ∃ R > 0 such that for purely spatial a with |a| > R:
‖F(z₁, z₂ + a) - F₁(z₁) · F₂(z₂)‖ < ε

**Proof sketch (not formalized):** The Poisson integral representation for
tube domains (Vladimirov Thm 25.1) gives F(z) = W(K_z) where K_z is a
Schwartz-class kernel.  For product configurations, K factors as
K_{z₁} ⊗ K_{z₂}, and a real shift translates K_{z₂}.  Applying the
distributional cluster condition to these kernels gives the pointwise result.
The Riemann-Lebesgue lemma (`Mathlib.Analysis.Fourier.RiemannLebesgueLemma`)
provides decay of the connected spectral component under spatial oscillation.

**References:**
- Vladimirov, "Methods of the Theory of Generalized Functions", §25
- Reed-Simon, "Methods of Modern Mathematical Physics" II, Thm IX.16
- Streater-Wightman, "PCT, Spin and Statistics", §2.4 + Thm 3-5

**Vetting:** Reviewed by Gemini Deep Think, which identified and helped fix:
- A soundness bug (vacuous Prop hypothesis)
- Redundant tube membership check in the conclusion (real shifts preserve Im)
- Comment accuracy ("compact subcones" → "compact subsets")
- Elaborator robustness (explicit ℝ→ℂ casts)

### Sorry-free proof of `bhw_pointwise_cluster_forwardTube`

The pointwise cluster theorem is now fully proved (modulo the axiom above).
The proof wires together:

1. **mkCLM:** Packages `Wfn.W n` (function + linearity + continuity) as a
   `ContinuousLinearMap` on Schwartz space, matching the axiom's type.

2. **ForwardTube ↔ TubeDomainSetPi bridge:** Uses `forwardTube_eq_imPreimage`
   to convert between the Wightman-namespace `ForwardTube` and the
   SCV-namespace `TubeDomainSetPi (ForwardConeAbs)`.

3. **BV convergence bridge:** Converts the spectrum condition's `InForwardCone`
   form to the axiom's `ForwardConeAbs` form via `inForwardCone_iff_mem_forwardConeAbs`.

4. **h_bv_cluster from R4:** The axiom's tensor-product cluster hypothesis
   matches `Wfn.cluster` exactly — no tensor-product density argument needed.

5. **Shifted ForwardTube membership:** Real spatial block-shift preserves
   ForwardTube (imaginary parts unchanged), proved via
   `forwardTube_add_real_pointwise`.

6. **BHW = spectrum_condition bridge:** On ForwardTube, `W_analytic_BHW.val`
   equals `spectrum_condition.choose` (BHW property 2).

### New helper lemmas

- `isEuclidean_realSpatialShift` — IsEuclidean preserved under real spatial shift
- `forwardTube_add_real_pointwise` — ForwardTube closed under pointwise real shifts
- `permutedForwardTube_add_real_pointwise` — lifts to PermutedForwardTube
- `append_realSpatialShift_mem_PET_of_permutedForwardTube` — Fin.append block
  shift preserves PET membership (proved via the pointwise result)

## What remains: `W_analytic_cluster_integral`

### The problem

`W_analytic_cluster_integral` says: the Schwinger integral
∫ W_BHW(n+m)(wick(x)) · (f ⊗ g_a)(x) dx clusters as |a| → ∞.

The natural proof uses `bhw_pointwise_cluster_forwardTube` + dominated
convergence.  However, there is a **time-ordering subtlety**:

- `bhw_pointwise_cluster_forwardTube` requires the combined config
  `Fin.append(wick(x_n), wick(x_m))` to be in `ForwardTube d (n+m)`.
- ForwardTube requires the times to be ordered: all n-block times before all
  m-block times.
- The integral runs over ALL x, including configs where m-block times precede
  n-block times (~half the domain).
- The spatial shift a doesn't change times (a₀ = 0), so the time ordering is
  the same for all a.  On the "wrong ordering" sector, the pointwise cluster
  theorem doesn't apply.
- BHW permutation invariance doesn't help directly: it permutes ALL arguments,
  but the cluster factorization depends on WHICH indices are in the n-block vs
  m-block (determining which get shifted by a).

### Why it doesn't block anything

`W_analytic_cluster_integral` and `wickRotatedBoundaryPairing_cluster` (E4)
are **leaf theorems**.  The R→E bridge `wightman_to_os_full` requires only
continuity, linearity, and `IsWickRotationPair` — it does NOT require E4.
No upstream proof depends on these cluster theorems.

### Possible resolutions

**Option 1: Strengthen the axiom to PET.**  State
`distributional_cluster_lifts_to_tube` for the full PermutedExtendedTube
rather than a single tube domain T(C).  The Poisson integral argument works
on each permuted tube sector.  This would let `bhw_pointwise_cluster_forwardTube`
take PET membership as hypothesis, covering all time orderings.

**Option 2: Sector decomposition.**  Split the integral by time-ordering
sector.  On the "good" sector (n-times < m-times), apply pointwise cluster
directly.  On each "bad" sector, use BHW permutation invariance to reorder
to a ForwardTube-compatible arrangement.  The cluster product
W_BHW(n)(z_n) · W_BHW(m)(z_m) is invariant under within-block permutations,
so all sectors contribute the same limit.

**Option 3: Direct distributional proof.**  Prove Schwinger cluster from
Wightman cluster (R4) without going through pointwise cluster, using the
distributional relationship between boundary values and interior integrals.
This avoids the time-ordering issue entirely but requires new infrastructure
connecting `wickRotatedBoundaryPairing` to `Wfn.W`.

## File inventory

| File | Changes |
|------|---------|
| `SCV/VladimirovTillmann.lean` | +2 axioms (`vladimirov_tillmann` pre-existing, `distributional_cluster_lifts_to_tube` new) |
| `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean` | Bug fix + 4 new lemmas + sorry-free `bhw_pointwise_cluster_forwardTube` |
| `README.md` | Documentation of fork changes |

## Update 2026-04-30: Vetting + dependency mapping

### Failed reduction attempt

A proposed axiom `F_ext_pointwise_cluster_translatedPET` (pointwise cluster of
`F_ext_on_translatedPET_total` lifted from `ForwardTube` to all of
`TranslatedPET`) was drafted and vetted via Gemini deep-think. **Verdict:
mathematically wrong in generic configurations.**

Reason (Streater-Wightman 1964 ed. p.135 + Araki-Hepp-Ruelle 1962 *Helv. Phys.
Acta* 35:164 Thm 2): for a configuration in the permuted-extended tube T'
with complex Lorentz witness Λ, applying the cluster shift `+λ·a` (real
spatial) yields `Im(Λ(ζ - λa)) = Im(Λ ζ) − λ·Im(Λa)`. For generic complex
Λ, `Im(Λa) ≠ 0` even when `a` is real spatial — the shifted configuration
**escapes the analytic continuation domain** as `λ → ∞`. Pointwise cluster
on T' is therefore false, not just hard.

The "Jost-point un-interleaving" hand-wave doesn't rescue it: Jost points are
strictly real by definition (Streater-Wightman §3.3), so complex
configurations cannot become Jost points under real shifts.

### What the vetting confirmed

- The standard textbook cluster axiom for OS reconstruction (Glimm-Jaffe Ch
  19; OS 1973/75 axiom E4) is **distributional, on real Euclidean spacetime**,
  not pointwise on complex tubes.
- The Wightman-side analog is `Wfn.cluster` (R4), already an axiom of
  `WightmanFunctions`. **No new axiom is needed.**
- Pointwise cluster on the standard forward tube T (Araki-Hepp-Ruelle Thm 2)
  is a corollary of the distributional version via Vitali. Restricted to T,
  this is `bhw_pointwise_cluster_forwardTube` (already proved).

### The actual dependency chain

The old dependency chain through
`schwingerExtension_os_term_eq_wightman_term` has been deleted from the active
route.  That theorem asserted a false same-test-function equality between the
Euclidean Wick-restricted pairing and the Minkowski Wightman pairing.

The honest R→E cluster blocker is therefore:

```
W_analytic_cluster_integral
  ← pointwise Schwinger/Euclidean cluster for the Wick-restricted kernel
  ← dominated convergence + Fubini on strictly ordered positive-time supports
  ← BHW pointwise cluster and translated-PET a.e. support infrastructure
```

So the R→E cluster blocker is **not** a corollary of a coordinate-level
OS-W equality.  It is a direct Euclidean/Wick-restricted cluster theorem,
parallel in spirit to the direct spectral/Laplace proof now used for
reflection positivity.

### Recommended path

Do not wait for or attempt to close the deleted
`schwingerExtension_os_term_eq_wightman_term` bridge.  Prove
`W_analytic_cluster_integral` directly on the Wick-restricted Euclidean kernel,
with support hypotheses strong enough to avoid coincidence singularities and
to justify dominated convergence.

Structural plumbing the cluster-corollary proof will need (Fubini split
over `Fin.append`, push-through of `wickRotation` and `tensorProduct`):
PR #72 (`integral_fin_append_split`, `MeasurableEquiv.finAddProd_symm_apply`,
`ae_joint_triple_translatedPET`, `bhw_euclidean_kernel_perm_invariant_ae`)
provides about half. The remaining `Fin.append`/`splitFirst`/`splitLast`
simp bridges and componentwise composition lemma are minor and can ship
in the same PR that closes the cluster integral.

### Refinement of the resolution options

The 2026-03-24 doc above proposed three resolution options. Updated assessment:

- **Option 1 (strengthen axiom to PET)**: subsumed by the vetting finding —
  pointwise cluster on PET / TranslatedPET is *false* in generic configs, not
  just an open problem. This option is mathematically incorrect.
- **Option 2 (sector decomposition)**: still plausible in principle but
  would require careful handling of the witness-dependent translation /
  permutation. Probably ~2–4 weeks of independent Edge-of-the-Wedge work
  re-deriving content the E→R lane will provide. Don't pursue.
- **Option 3 (direct distributional proof)**: confirmed as the right path.
  The needed infrastructure is not a same-test-function
  `wickRotatedBoundaryPairing = Wfn.W` bridge.  It is a direct Euclidean
  cluster proof for the Wick-restricted kernel, using the BHW pointwise cluster
  theorem, Fubini, and dominated convergence.
