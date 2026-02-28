/-
# Proof Strategy: complex_lorentz_invariance — CURRENT STATE

## Status (2026-02-22)

### PROVED (modulo 1 sorry):
- `complex_lorentz_invariance` — T-set argument with U-connected trick
  - T closed ✓
  - T ∩ U open ✓ (identity theorem via uniform_near_identity_invariance)
  - Tᶜ ⊆ U ✓
  - IsPreconnected U → T = G ✓
  - `nonemptyDomain_isPreconnected` — **1 sorry** (U connected)

### Remaining sorry: `nonemptyDomain_isPreconnected`

U = {Λ ∈ SO⁺(1,d;ℂ) : ∃ w ∈ FT, Λ·w ∈ FT}

## Analysis of U and G \ U

### Why domain_nonempty (D_Λ ≠ ∅ for all Λ) is FALSE

For Λ with Im(Λ) = 0 and Re(Λ) anti-orthochronous (e.g., boost by iπ in any
spacetime plane): Re(Λ) sends V⁺ to -V⁺, so Im(Λ·z) = Re(Λ)·Im(z) ∉ V⁺
for any z with Im(z) ∈ V⁺. Hence D_Λ = ∅.

Examples:
- d=1: B(iπ) = diag(-1,-1). In SO⁺(1,1;ℂ) ≅ ℂ/(2πiℤ), this is θ = iπ.
  G \ U = {θ = α + iπ : α ∈ ℝ} (a horizontal line in the cylinder).
- d=2: B_{01}(iπ) = diag(-1,-1,1). In SO⁺(1,2;ℂ) via path γ(t) = B_{01}(itπ).
  D_{B_{01}(iπ)} = ∅ since M₀₀ = -1 implies M·V⁺ ∩ V⁺ = ∅.
- General d: Any boost by iπ in a spacetime plane gives an anti-orthochronous
  real Lorentz matrix in the identity component of SO⁺(1,d;ℂ).

### Structure of G \ U

G \ U = {Λ ∈ SO⁺(1,d;ℂ) : ∀ w ∈ FT, Λ·w ∉ FT}
      = {Λ : (M·V⁺ + range(N)) ∩ V⁺ = ∅}  (for n=1, M=Re(Λ), N=Im(Λ))

For d=1: G \ U = {(α, π) : α ∈ ℝ} in ℝ × S¹ (the cylinder ℂ/(2πiℤ)).
  This is a copy of ℝ inside a 2D cylinder.
  U = (ℝ × S¹) \ (ℝ × {π}) ≅ ℝ × (-π, π) ≅ ℝ² — connected! ✓

For general d: G \ U is a closed proper subset of G.
  dim_ℝ(G) = d(d+1). G \ U should have codimension ≥ 1.
  For d ≥ 2: codimension likely ≥ 2, making the argument easier.

### Key observation: U IS connected (for all d ≥ 1, n ≥ 1)

U = ⋃_{w ∈ FT} O_w where O_w = {Λ ∈ G : Λ·w ∈ FT}.

Properties:
- Each O_w is OPEN (preimage of open FT under continuous Λ ↦ Λ·w)
- Each O_w contains 1 (since 1·w = w ∈ FT)
- U = ⋃_{w ∈ FT} O_w

If each O_w is preconnected, then by `isPreconnected_sUnion` (Mathlib):
  all O_w contain 1, hence ⋃ O_w is preconnected.

## Proof approaches for O_w preconnected

### Approach 1: Exponential paths with adjusted real part (MOST PROMISING)

For Λ ∈ O_w: Λ·w ∈ FT. Write Λ = exp(X) for X ∈ so(1,d;ℂ).
Path γ(t) = exp(tX). The issue: γ(t)·w might exit FT for intermediate t.

Fix: Replace w by w' = w + ρ (shift real part) where ρ is chosen so that
γ(t)·w' stays in FT for all t. Since Im(γ(t)·w') = Re(γ(t))·Im(w) + Im(γ(t))·(Re(w)+ρ),
choosing ρ large in the appropriate direction can keep Im(γ(t)·w') deep in V⁺.

Specifically: the map t ↦ Im(γ(t))·ρ is continuous and at t=0 gives 0.
For t ≠ 0 and Im(γ(t)) ≠ 0: Im(γ(t))·ρ can be made to point in any direction
in range(Im(γ(t))) by choosing ρ appropriately. Since rank(Im(γ(t))) varies
continuously, and the only "bad" times are when Im(γ(t)) = 0 but Re(γ(t))
is anti-orthochronous (both simultaneously), one can show that for generic ρ,
Im(γ(t))·ρ compensates for the Re(γ(t))·Im(w) drift.

This requires careful analysis of the Lorentz algebra structure.

### Approach 2: Wick rotation transfer (CLEANEST IF IT WORKS)

Use the Wick rotation homeomorphism: SO⁺(1,d;ℂ) ≅ SO(d+1;ℂ).
Under this homeomorphism, the forward tube condition transforms into
a condition involving the standard cone (all components positive?).
If the transformed U is "everything" or "obviously connected," this works.

Challenge: The forward tube depends on the Lorentz metric η = diag(-1,1,...,1),
not the Euclidean metric. The Wick rotation changes the GROUP but not the
REPRESENTATION SPACE. So the orbit sets transform non-trivially.

### Approach 3: Direct generation argument (AVOIDS U-connected entirely)

T contains open V ∋ 1. V generates G. For Λ = vₘ·...·v₁ with vᵢ ∈ V:
prove Λ ∈ T by induction on m.

At each step: need D_{Λₖ} ∩ D_{Λₖ₋₁} ≠ ∅ for the identity theorem.
This fails when Λₖ₋₁ ∉ U (D_{Λₖ₋₁} = ∅).

POSSIBLE FIX: Choose z₀ depending on the factorization, such that
ALL intermediate products Λₖ send z₀ to FT. This requires:
  vₖ·(Λₖ₋₁·z₀) ∈ FT for each k.
For z₀ deep inside FT and vₖ close to 1: the drift per step is small,
but accumulated drift over m steps can be large (z₀ escapes FT).

RESOLUTION: For z₀ = ξ + iη with η ∈ V⁺ and ξ free: the drift in Im
is controlled by ‖vₖ - I‖ · ‖z₀‖. By choosing ‖z₀‖ large with Im(z₀)
proportionally deep in V⁺... but the ratio drift/margin is independent of R.

This approach seems to require more careful analysis of the specific
Lorentz group structure (not just abstract topological group properties).

### Approach 4: Leave as sorry, defer to later

The sorry `orbitSet_isPreconnected` (each O_w preconnected) is a genuine
mathematical fact. It can be proved later with more geometric infrastructure.
The proof of `complex_lorentz_invariance` is COMPLETE modulo this sorry.

## Current implementation in Connectedness.lean

```
nonemptyDomain_isPreconnected  -- sorry: U preconnected
  ↑ uses: (to be filled: union of preconnected orbit sets)
  ↑ needs: orbitSet_isPreconnected (sorry)

complex_lorentz_invariance  -- PROVED modulo above
  ↑ uses: nonemptyDomain_isPreconnected
  ↑ uses: T closed (proved: complement open via witness)
  ↑ uses: T ∩ U open (proved: identity theorem + uniform_near_identity_invariance)
  ↑ uses: Tᶜ ⊆ U (proved: witness from negation)
  ↑ uses: IsPreconnected contradiction
```

## Helper lemmas (all proved)

- `near_identity_core` — core computation for near-identity invariance
- `near_identity_invariance` — F(Λ·z₀) = F(z₀) for Λ near 1
- `uniform_near_identity_invariance` — uniform version (joint continuity)
- `eq_zero_on_convex_of_eventuallyEq_zero` — identity theorem on convex domains
- `isOpen_d_lambda` — D_Λ is open
- `d_lambda_convex` — D_Λ is convex (hence connected)
- `continuous/differentiable_complexLorentzAction_fst/snd` — action continuity
- `complexLorentzAction_one/mul/inv` — action algebra
- `forwardTube_nonempty` — FT ≠ ∅
- `ComplexLorentzGroup.isPathConnected` — G path-connected

## Execution plan

1. ✓ Restructured proof to use U-connected approach
2. ✓ Refactored `nonemptyDomain_isPreconnected` using `isPreconnected_sUnion`
3. `orbitSet_isPreconnected` — still sorry (geometric analysis needed)
4. ✓ BHW sorrys largely proved — see below

## BHW theorem status (Connectedness.lean, updated 2026-02-22)

**ALL 5 BHW properties PROVED (modulo 3 sorrys):**
- `fullExtendF_well_defined` — reduced to `F_permutation_invariance` via
  Lorentz-perm commutation: Λ·(π·w) = π·(Λ·w) (definitional in our setup)
- BHW Property 1 (holomorphicity) — inverse chart ψ(z) = (Λ₀⁻¹·z)∘π₀,
  fullExtendF =ᶠ F∘ψ on ψ⁻¹(FT), chain rule + EventuallyEq.differentiableAt_iff
- BHW Property 2 (F_ext = F on FT) — well-definedness with (id, 1, z) preimage
- BHW Property 3 (Lorentz invariance) — Λ composition + well-definedness
- BHW Property 4 (permutation symmetry) — perm composition via congr_fun pointwise
- BHW Property 5 (uniqueness) — identity_theorem_product + PET connected

**New infrastructure for uniqueness (2026-02-22):**
- `SCV.flattenCLE` — CLE from `Fin n → Fin m → ℂ` to `Fin (n*m) → ℂ`
- `analyticAt_of_differentiableOn_product` — Hartogs analyticity for product types
- `identity_theorem_product` — identity theorem for `Fin n → Fin m → ℂ`
- `complexLorentzAction_isOpenMap` — Lorentz action is open map
- `isOpen_permutedForwardTube` / `isOpen_permutedExtendedTube` — PFT and PET are open

**Remaining sorrys:**
| # | Line | Name | Status | Dependencies |
|---|------|--------|--------|-------------|
| 1 | 1109 | `orbitSet_isPreconnected` | sorry | geometric (Lie group analysis) |
| 2 | 1561 | `F_permutation_invariance` | sorry | edge-of-the-wedge + local commutativity |
| 3 | 1794 | PET preconnected | sorry | edge-of-the-wedge joining permutation sectors |

**Key insight for F_permutation_invariance:**
For τ = id: reduces to `complex_lorentz_invariance` (proved modulo orbitSet).
For τ ≠ id: FT ∩ τ·FT = ∅ (opposite imaginary parts for permuted differences).
But at real Jost points (spacelike separations), hF_local gives F(σ·x) = F(x)
for adjacent transpositions σ. Edge-of-the-wedge glues across the Jost boundary.

## LorentzLieGroup.lean sorry

| # | Name | Status | Dependencies |
|---|------|--------|-------------|
| 1 | `RestrictedLorentzGroup.isPathConnected` | sorry (deferred) | boost + rotation infrastructure |
-/
