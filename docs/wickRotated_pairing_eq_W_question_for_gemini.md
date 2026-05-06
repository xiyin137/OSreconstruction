# Question for Gemini: Wick-rotation bridge proof technique

In the OS reconstruction theorem (Wightman → Schwinger direction), I want
to verify a specific equality and understand its standard proof.

## The claim

Let `Wfn` be Wightman functions on Minkowski ℝ^{1,d} satisfying R0–R4
(Streater-Wightman conventions). The spectrum condition gives an
analytic continuation `W_analytic_n : ForwardTube → ℂ` (n-point),
holomorphic with polynomial growth bound on the forward tube
`T_n = {z ∈ ℂ^{n(d+1)} | Im(z_k - z_{k-1}) ∈ V₊}`, whose distributional
boundary values recover `W_n` (the n-point distribution).

For a Schwartz test function `f : 𝒮(ℝ^{n(d+1)}) → ℂ` whose support is in
the OPTR region `0 < x_1⁰ < x_2⁰ < ⋯ < x_n⁰` (Osterwalder-Schrader's
`𝒮_<`), is the following equality true:

```
∫_{ℝ^{n(d+1)}} W_analytic_n(wick(x)) · f(x) dx = W_n(f)        (*)
```

where `wick(x)_k = (i x_k⁰, x_k⃗)` (Wick rotation: real Euclidean time
→ imaginary Lorentzian time)?

The LHS evaluates `W_analytic` at fixed FINITE imaginary parts (interior
of the open forward tube — the Wick-rotated OPTR config is in T_n by
the strict ordering `0 < x_1⁰ < x_2⁰ < ⋯`). The RHS is the Wightman
tempered distribution `W_n` paired with the test function `f`.

## Question

I tried a holomorphic deformation `z(s, x)_k⁰ = x_k⁰((1-s) + is)` and
found that the s-derivative of the integral against arbitrary Schwartz
`f` is NOT zero — it gives a nontrivial Euler-operator contribution
`n·f + Σ_k x_k⁰ ∂_{x_k⁰}f` after IBP. So a straightforward
"differentiate-under-integral, get zero, integrate `s ∈ (0, 1]`"
approach fails.

But (*) is clearly true for textbook OS reconstruction — Schwartz test
functions are used throughout, and they're certainly not assumed to be
complex-analytic.

So I need to understand: **what is the actual textbook argument** for
(*)?

Possible approaches I want vetted:

**(A) Direction-independence of distributional boundary values +
dominated convergence.** The spectrum condition gives
`lim_{ε → 0+} ∫ W_analytic(x + iε η) f(x) dx = W_n(f)` for any FIXED
η in the forward cone. For OPTR-supported f, the Wick-rotated config
`x + i (x⁰, 0⃗)` corresponds to ε = 1 with x-DEPENDENT direction
`η(x) = (x⁰, 0⃗)`. Is there a slicing/Fubini argument that reduces
this to constant-η spectrum-condition applications?

**(B) Edge-of-the-wedge / boundary value uniqueness.** Distributional
boundary values of analytic functions on tube domains are independent
of approach direction. For Wick rotation, the path
`s ↦ x + is(x⁰, 0⃗)` approaches the boundary as s → 0+. By some
continuity argument, the integral at s = 1 equals the boundary value
W_n(f). But what makes this work in distributional sense for
x-dependent η?

**(C) Direct distributional argument.** Maybe (*) is essentially built
into how we PAIR W_n with OPTR-supported test functions via the
spectrum condition. Is `∫ W_analytic(wick x) f(x) dx` perhaps THE
definition (or a key identity) of how the Wightman distribution acts
on `𝒮_<` (OPTR-supported test functions), via spectrum_condition's
spectral support `supp Ŵ_n ⊆ V̄₊^n`?

**(D) Momentum-space contour deformation.** Fourier-transform W_n: by
spectral support, Ŵ_n is supported in V̄₊^n. The Schwartz f̂ doesn't
extend to entire complex p, but we don't need this if Ŵ_n's support
compactness in the energy variable allows shifting the integration
contour. Is this the standard argument?

**(E) Spectral / Källén-Lehmann via measure theory.** For W_2
specifically (and more generally via truncated decomposition), express
W_2 as an integral over a spectral measure. The Wick rotation becomes
a Laplace transform, which converges for OPTR support (positive times)
without needing analyticity of f.

## Specific textbook references requested

**(R1)** Glimm-Jaffe, *Quantum Physics*, Ch 6 and Ch 19. Theorem 6.1.4
on Wightman ↔ Schwinger correspondence. What does the proof actually
use? Is it analytic approximation, momentum space, Källén-Lehmann, or
something else?

**(R2)** Streater-Wightman, *PCT, Spin and Statistics*, §3.3 and §3.4
(analytic continuation, Schwinger functions). How is the integral
identity (*) for Schwartz OPTR-supported f established?

**(R3)** Osterwalder-Schrader 1973, *Axioms for Euclidean Green's
Functions*, §2 (definition of `𝒮_<`) and §5. The Schwinger functions
S_n are defined as Wick rotations of W_analytic. The pairing `S_n(f)`
for OPTR-supported f is specified — is this the same as the
Wick-rotated integral?

## Minimal request

If you have direct access to the proof in any of these references,
please cite the precise theorem number and the key proof step. I
particularly want to know:

1. Is approach (A), (B), (C), (D), or (E) above the standard textbook
   one?
2. Does the proof require f to be analytic, or does it work for general
   Schwartz f directly?
3. How heavy is the proof (one paragraph, one page, multiple pages)?
4. Specifically: is there a slicing argument that reduces x-dependent η
   to constant-η spectrum-condition + Fubini?

Context: I'm formalizing this in Lean 4. I have
`bhw_distributional_boundary_values` (the spectrum condition's boundary
value relation, for constant η in the forward cone) as an existing
proved lemma, plus standard Mathlib for Schwartz spaces, dominated
convergence, IBP, etc. I want to build an HONEST proof of (*), not
adopt it as an axiom — but I need to understand the actual mathematical
structure first.
