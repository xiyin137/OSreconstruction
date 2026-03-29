# Plan: Prove spectrum_condition and vacuum_unique in gnsQFT

## The 2 remaining sorrys

### Sorry 1: `spectrum_condition` (GNSHilbertSpace.lean:1180)

**Goal**: `SpectralCondition d (gnsPoincareRep Wfn)`, which requires:
- `energy_nonneg`: `∀ ψ, Re⟨ψ, Hψ⟩ ≥ 0` where H = P₀ (Hamiltonian)
- `mass_shell`: `∀ ψ, Re⟨ψ, H²ψ⟩ ≥ Σᵢ Re⟨ψ, Pᵢ²ψ⟩`

where H and Pᵢ are generators of translations (from `PoincareRepresentation`).

### Sorry 2: `vacuum_unique` part 2 (GNSHilbertSpace.lean:~1284)

**Goal**: Any time-translation-invariant vector is proportional to Ω.
Requires: spectrum condition + Stone's theorem → ker(H) = ℂ·Ω.

## Proof chain

```
Wightman functions → OS positivity (E2) → forward tube analyticity
  → Fourier support of 2-point function in forward cone V̄₊
  → spectral measure of P_μ supported on V̄₊
  → energy_nonneg + mass_shell
```

## Layer 1: Translation generators are self-adjoint (~50 lines)

The Poincaré representation gives a one-parameter unitary group for each
direction μ: `t ↦ U(t·e_μ, 1)`. By Stone's theorem (now proved in
StoneTheorem.lean modulo timeEvolution_generator), the generator P_μ is
self-adjoint with spectral measure.

**Key**: connect `PoincareRepresentation.momentum μ` (defined as
infinitesimal generator via limUnder) to `OneParameterUnitaryGroup.generator`
from StoneTheorem.lean. The translation one-parameter group
`translationUnitaryGroup μ` is already defined in OperatorDistribution.lean.

**Output**: P_μ = generator of translation group, hence self-adjoint.

## Layer 2: Fourier support from Wightman function analyticity (~100 lines)

The Wightman 2-point function W₂(f, g) = ⟨Ω, φ(f)φ(g)Ω⟩ has the
Fourier representation:
  W₂(x₁, x₂) = ∫ e^{ip·(x₁-x₂)} dρ(p)

where ρ (the Källén-Lehmann measure) is supported on V̄₊ = {p : p₀ ≥ |p⃗|}.

This follows from:
1. W₂ depends only on ξ = x₁ - x₂ (translation invariance of Wfn)
2. W₂(ξ) is analytic in the forward tube Im(ξ) ∈ V₊ (from OS axioms)
3. Forward tube analyticity ⟹ Fourier transform supported on V̄₊
   (Paley-Wiener / forward tube theorem)

The forward tube theorem is already available in the project
(`BochnerTubeTheorem.lean`).

**Output**: dρ supported on V̄₊.

## Layer 3: Spectral condition from Fourier support (~80 lines)

The spectral measure of P_μ is related to dρ via:
  ⟨ψ, f(P)ψ⟩ = ∫ f(p) dρ_ψ(p)

For ψ in the domain of H = P₀:
  Re⟨ψ, Hψ⟩ = ∫ p₀ dρ_ψ(p) ≥ 0

since ρ_ψ is supported on V̄₊ where p₀ ≥ 0.

Similarly for mass_shell: p₀² ≥ |p⃗|² on V̄₊.

**Key difficulty**: connecting the spectral measure of the abstract
momentum operator (from Stone's theorem / spectral theory) to the
Fourier transform of Wightman functions. This is the BLTW
(Borchers-Lüscher-Tomita-Wightman) connection.

**Output**: `energy_nonneg` and `mass_shell`.

## Layer 4: Vacuum uniqueness from spectrum condition (~30 lines)

Given `spectrum_condition`:
1. H = P₀ is self-adjoint with σ(H) ⊆ [0,∞)
2. U(t)Ω = Ω for all t (time-translation invariance, already proved)
3. So HΩ = 0 (generator of invariant vector is 0)
4. For any ψ with U(t)ψ = ψ: Hψ = 0
5. ker(H) = {ψ : Hψ = 0} is the eigenspace at 0
6. By cluster decomposition / ergodicity: ker(H) is 1-dimensional = ℂ·Ω

Step 6 requires the cluster property (separation of Wightman functions
at large spacelike distances), which is proved in the project.

**Output**: vacuum uniqueness.

## Estimated effort

| Layer | Lines | Dependencies |
|-------|-------|-------------|
| 1. Translation generators self-adjoint | ~50 | StoneTheorem, OperatorDistribution |
| 2. Fourier support from analyticity | ~100 | BochnerTubeTheorem, forward tube |
| 3. Spectral condition from support | ~80 | Layers 1-2, spectral theory |
| 4. Vacuum uniqueness | ~30 | Layer 3, cluster property |
| **Total** | **~260** | |

## Risk assessment

| Risk | Impact | Mitigation |
|------|--------|-----------|
| StoneTheorem.timeEvolution_generator still sorry | Blocks Layer 1 | Use abstract generator, defer sign convention |
| BLTW connection (Layer 3) is deep | Hardest step | May need axiomatization |
| Cluster → ergodicity (Layer 4, step 6) | Nontrivial | Available in project as cluster property |

## Recommendation

Start with Layer 4 (vacuum uniqueness) — it only needs spectrum_condition
as a hypothesis, and the cluster property is available. Then work backward
through Layers 3, 2, 1.

Layer 3 (spectral → energy/mass) is the most self-contained.
Layer 2 (Fourier support) reuses existing forward tube infrastructure.
Layer 1 (generators self-adjoint) reuses Stone's theorem.
