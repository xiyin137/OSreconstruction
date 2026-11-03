/-
# Distributional Uniqueness via Convolution/Mollification

Date: 2026-03-08
Author: Claude Code

## Goal
Prove `distributional_uniqueness_forwardTube` WITHOUT requiring
`HasFourierLaplaceReprRegular`. This is the correctly-stated sorry at
ForwardTubeDistributions.lean:560.

## Statement
If F₁, F₂ are holomorphic on ForwardTube d n and their distributional BV
agree (∫(F₁-F₂)(x+iεη)f(x)dx → 0 for all Schwartz f and all η ∈ C),
then F₁ = F₂ on ForwardTube d n.

## The Circular Dependency
The existing proved `distributional_uniqueness_tube_of_regular` needs:
1. G(realEmbed x) = 0 — requires `boundary_continuous` (G continuous on boundary)
2. ContinuousWithinAt at boundary — requires `tube_continuousWithinAt`

Both come from `HasFourierLaplaceReprRegular`. But constructing Regular from
bare distributional BV is the root blocker.

## Strategy: Convolution-Based Proof (Vladimirov's classical approach)

### Step 1: Mollify the holomorphic function
For φ ∈ C_c^∞(ℝᵐ) (compactly supported smooth), define:
  G_φ(z) = ∫_{ℝᵐ} G(z - t) φ(t) dt    (z ∈ T(C), t ∈ ℝᵐ)

where z - t means (Re(z) - t) + i·Im(z), i.e., we only translate in the
real direction.

### Step 2: G_φ is holomorphic on T(C)
G(z-t) is holomorphic in z for each fixed real t. By differentiation under
the integral sign (φ has compact support, so the integral is finite and the
domain of holomorphicity is unchanged), G_φ is holomorphic on T(C).

### Step 3: G_φ has continuous boundary values = 0
G_φ(x + iεη) = ∫ G(x-t + iεη) φ(t) dt = ∫ G(u + iεη) φ(x-u) du

The test function φ(x-·) is compactly supported smooth ⊂ Schwartz.
By hypothesis, ∫ G(u + iεη) f(u) du → 0 for all Schwartz f.
Taking f = φ(x-·) (which IS Schwartz): G_φ(x + iεη) → 0 as ε → 0+.

Moreover, G_φ extends continuously to the boundary:
- G_φ(x + iy) = ∫ G(x-t + iy) φ(t) dt is jointly continuous in (x,y) for y ∈ C̄
  because G is continuous on T(C) and φ is compactly supported
- At the boundary y=0: G_φ(x + iεη) → 0, so G_φ continuously extends with G_φ(x) = 0

### Step 4: G_φ = 0 on T(C)
G_φ is holomorphic on T(C) with continuous extension to boundary = 0.
Apply the 1D EOW slicing argument (reuse logic from distributional_uniqueness_tube_of_regular)
to conclude G_φ = 0 on T(C).

### Step 5: G = 0 on T(C)
G_φ(z) = 0 for all φ ∈ C_c^∞(ℝᵐ) and all z ∈ T(C).
Take an approximate identity φ_n → δ. Then G_φ_n(z) → G(z) (by continuity of G).
Since G_φ_n(z) = 0, G(z) = 0.

## Infrastructure Needed
1. Convolution of holomorphic tube function with compactly supported smooth function
   - Holomorphicity of the convolution (diff under integral)
   - Continuity up to boundary (dominated convergence)
2. Compactly supported smooth functions are SchwartzMaps
   (or: distributional BV hypothesis applies to them)
3. Approximate identity in compactly supported smooth functions
4. Basic properties of convolution (continuity, exchange of limit)

## Alternative: Avoid Convolution via 1D Reduction

A potentially SIMPLER route: reduce to the 1D case directly.

For the 1D case with C = (0,∞), T(C) = upper half-plane:
- g holomorphic on UHP
- ∫ g(t + iε) ψ(t) dt → 0 for all Schwartz ψ on ℝ
- Conclude: g ≡ 0 on UHP

This 1D result can be proved via:
1. g(· + iε) → 0 in S'(ℝ)
2. ĝ(· + iε)(ξ) = e^{-εξ} T̂(ξ) where T̂ is the distributional FT of the BV
3. T̂(f) = lim_{ε→0} ∫ ĝ(t+iε) f(t) dt = 0, so T̂ = 0
4. T̂ = 0 implies T = 0 (Fourier transform injective on S')
5. T = 0 + Paley-Wiener → g ≡ 0

But we already have `paley_wiener_half_line` which handles the 1D case! The issue
is connecting the multi-dimensional BV to the 1D slice BV.

## Connecting Multi-D BV to 1D Slice BV

Given: ∫_{ℝᵐ} G(x + iεη) f(x) dx → 0 for all Schwartz f on ℝᵐ

Want: ∫_ℝ g(t + iε) ψ(t) dt → 0 for all Schwartz ψ on ℝ

where g(w) = G(x₀ + w·η) for fixed x₀ ∈ ℝᵐ, η ∈ C.

g(t + iε) = G(x₀ + (t+iε)·η) = G(x₀ + t·η + iε·η)

∫ g(t + iε) ψ(t) dt = ∫ G(x₀ + t·η + iε·η) ψ(t) dt

Now, G(x₀ + t·η + iε·η) = G(u + iε·η) where u = x₀ + t·η.

The multi-D hypothesis says: for ALL Schwartz f on ℝᵐ,
  ∫_{ℝᵐ} G(u + iε·η) f(u) du → 0

Can we find f such that ∫_{ℝᵐ} G(u + iε·η) f(u) du = ∫_ℝ G(x₀ + t·η + iε·η) ψ(t) dt?

Yes: take f(u) = ψ(⟨u-x₀, η⟩/‖η‖²) · δ_{x₀+ℝ·η}(u) ... but δ is not a function.

More carefully: decompose ℝᵐ = ℝ·η ⊕ η^⊥. Write u = x₀ + s·η + v where s ∈ ℝ, v ⊥ η.
Take f(u) = ψ(s) · χ_ε(v) where χ_ε is an approximate identity in η^⊥ concentrated near 0.

Then: ∫_{ℝᵐ} G(u + iε·η) f(u) du = ∫_ℝ ∫_{η^⊥} G(x₀+s·η+v + iε·η) χ_ε(v) dv · ψ(s) ds

As ε → 0 (the approximate identity parameter, not the BV parameter — need different variable),
the inner integral converges to G(x₀+s·η + iε·η) ψ(s).

This is getting circular with ε used for two purposes. Let me use δ_k for the approximate identity:

∫_{ℝᵐ} G(u + iε·η) fk(u) du → 0 as ε → 0 (by hypothesis, for each k)

where fk(u) = ψ(s) · δ_k(v) and u = x₀ + s·η + v.

But fk is NOT Schwartz in general because δ_k needs to be a Schwartz function in η^⊥.
Well, δ_k can be taken as a Gaussian bump of width 1/k in the transverse directions.
Then fk IS Schwartz on ℝᵐ (Gaussian × Schwartz = Schwartz).

So: ∫_{ℝᵐ} G(u + iε·η) fk(u) du → 0 as ε → 0 for each k.

And: as k → ∞, fk → ψ ⊗ δ_0, so:
  ∫_{ℝᵐ} G(u + iε·η) fk(u) du → ∫_ℝ G(x₀ + s·η + iε·η) ψ(s) ds

But this limit and the ε→0 limit need to be interchanged, which requires some
uniform control.

## SIMPLEST APPROACH: Direct 1D via evaluation of multi-D BV

Actually, the simplest approach might be:

For the multi-D BV hypothesis:
  ∫_{ℝᵐ} G(x + iε·η) f(x) dx → 0 for all Schwartz f

This means: the tempered distributions T_ε(f) = ∫ G(x+iεη) f(x) dx converge to 0 in S'(ℝᵐ).

In particular, T_0 = 0 as a tempered distribution (if it exists). But T_0 is the boundary
distribution, and T_0 = 0 means G integrates to 0 against all test functions on the boundary.

If we ALSO know G is continuous on the boundary, then by eq_zero_of_schwartz_integral_zero,
G = 0 on the boundary.

THE PROBLEM: We don't know G is continuous on the boundary from bare distributional BV.

WAIT — actually, for the specific case of ForwardTubeDistributions.lean, the distributional BV
hypothesis is NOT about a general tube. It's about the FORWARD TUBE with its specific cone
structure. And in the Wightman reconstruction, the functions come from analytic continuation of
OS correlation functions, which DO have regularity.

But for the GENERAL theorem `distributional_uniqueness_forwardTube`, we only have the bare
hypotheses. So we need the convolution trick or something equivalent.

## DECISION: Use convolution approach

The convolution approach is the cleanest. Key infrastructure:
1. `SchwartzMap.ofCompactlySupported` — embed C_c^∞ → Schwartz (or: work with Schwartz directly)
2. `tube_convolution_holomorphic` — G*φ holomorphic on T(C)
3. `tube_convolution_boundary_zero` — G*φ → 0 at boundary
4. `tube_convolution_continuousWithinAt` — ContinuousWithinAt for G*φ
5. `tube_convolution_tendsto_pointwise` — G*φ_n → G as φ_n → δ

Actually steps 2-4 might be combined: G*φ is holomorphic on T(C) and CONTINUOUS on T̄(C),
with boundary values 0. This is stronger than what the existing EOW proof needs.

For step 5: since G is continuous on the tube interior, G*φ_n(z) → G(z) for z in the interior
by standard approximate identity theory.

## Infrastructure Size Estimate
~200-300 lines for the convolution infrastructure. Worth it because:
- Closes the most important sorry
- Reusable for other distributional uniqueness results
- Avoids the much harder Vladimirov-Tillmann theorem

## UPDATE (2026-03-08): ROOT BLOCKER IDENTIFIED

The convolution approach has a fundamental gap:

**ContinuousWithinAt of G_ψ at boundary requires growth control that bare
distributional BV does not provide without Banach-Steinhaus for S'(ℝᵐ).**

Specifically:
- G_ψ(x + iεη) → 0 as ε → 0+ for each x (from BV hypothesis, via Fubini
  at fixed ε — no growth control needed for this step!)
- BUT ContinuousWithinAt requires: as (x,y) → (x₀,0) within T(C), G_ψ(z) → 0.
  This needs JOINT convergence, not just convergence along vertical rays.
- For holomorphic functions, vertical convergence to 0 at every real point
  does NOT imply ContinuousWithinAt (counterexamples exist without growth control).

## UPDATE (2026-03-09): ROOT BLOCKER RESOLVED — Banach-Steinhaus built

Path 1 (Banach-Steinhaus) was chosen and COMPLETED by Codex. The full pipeline
is now proved, pending only assembly into the top-level theorem.

### What is proved (all sorry-free, in SCV/):

**SchwartzComplete.lean** (Codex):
1. `SchwartzMap.instCompleteSpace` — completeness of 𝓢(E, F)
2. `SchwartzMap.instBarrelledSpace` — barrelledness (enables Banach-Steinhaus)
3. `tempered_equicontinuous` — Banach-Steinhaus for tempered distributions
4. `tempered_apply_tendsto_zero_of_tendsto` — sequence payoff: T_n→0 + u_n→f ⟹ T_n(u_n)→0
5. `tempered_apply_tendsto_zero_of_tendsto_filter` — filter-generalized version

**DistributionalUniqueness.lean** (Codex):
1. `translateSchwartz` / `translateSchwartzCLM` — Schwartz translation as CLM
2. `tendsto_translateSchwartz_nhds_of_isCompactSupport` — translation continuity in 𝓢 topology
3. `continuousOn_realMollify_upperHalfPlane` — M_ψ continuous on UHP
4. `differentiableOn_realMollify_upperHalfPlane` — M_ψ holomorphic on UHP (1D)
5. `tendsto_mollified_boundary_zero_of_clm_zero` — boundary trace M_ψ → 0
   (uses Banach-Steinhaus to handle joint (x,ε)→(x₀,0) limit)
6. `uniqueness_of_boundary_trace_zero` — G holomorphic + trace 0 ⟹ G = 0
7. `eq_zero_on_open_of_compactSupport_schwartz_integral_zero` — du Bois-Reymond

### Assembly plan (IN PROGRESS):

**Step A** (Codex building): Generalize `differentiableOn_realMollify_upperHalfPlane`
to multi-dimensional tube domains using `hasFDerivAt_integral_of_dominated_of_fderiv_le`.

**Step B**: Assemble top-level theorem in SCV/DistributionalUniqueness.lean:
```
theorem distributional_uniqueness_tube_of_zero_bv {m : ℕ}
    {C : Set (Fin m → ℝ)} (hC : IsOpen C) (hconv : Convex ℝ C) ...
    {G : (Fin m → ℂ) → ℂ}
    (hG_diff : DifferentiableOn ℂ G (TubeDomain C))
    (hG_bv_zero : ∀ f η, η ∈ C → Tendsto (...) ... (nhds 0)) :
    ∀ z ∈ TubeDomain C, G z = 0
```
Proof chain: mollify → holo (Step A) + boundary trace 0 (item 5) → M_ψ = 0 (item 6)
→ G = 0 (item 7).

**Step C**: One-line instantiation in ForwardTubeDistributions.lean:
`distributional_uniqueness_forwardTube` = flatten via `flattenCLEquiv`,
apply `distributional_uniqueness_tube_of_zero_bv` to `ForwardConeFlat`, unflatten.
ForwardConeFlat satisfies open + convex + cone — no Lorentz/spectral structure needed.

### Key insight: Why Banach-Steinhaus was needed

The mollified function M_ψ(w) = ∫ G(w + realEmbed t) ψ(t) dt has boundary
trace M_ψ(realEmbed x₀ + iεη) = T_ε(translate(-x₀) ψ) where T_ε(f) = ∫ G(realEmbed t + iεη) f(t) dt.

The weak BV hypothesis gives T_ε(f) → 0 for each fixed f. But the
`uniqueness_of_boundary_trace_zero` theorem needs the FULL nhdsWithin limit:
as w → realEmbed(x₀) within the tube, M_ψ(w) → 0. In this limit, BOTH
Im(w) → 0 (so ε → 0) AND Re(w) → x₀ (so the test function translate(-Re w) ψ
varies). This is a joint limit where the operator AND the input both vary.

Banach-Steinhaus (via `tempered_apply_tendsto_zero_of_tendsto_filter`) handles
exactly this: if T_ε → 0 pointwise and translate(-Re w) ψ → translate(-x₀) ψ
in 𝓢 topology, then T_ε(translate(-Re w) ψ) → 0.
-/
