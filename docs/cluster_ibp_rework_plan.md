# IBP / Schwartz-pairing rework plan for the cluster-proof dominator step

**Branch**: `r2e/ruelle-poly-bound-chain` (will likely fork into `r2e/cluster-ibp-rework` for the actual implementation).
**Target**: close the production `sorry` at `OSReconstruction/Wightman/Reconstruction/WickRotation/RuelleClusterBound.lean:718` in the body of `W_analytic_cluster_integral_via_ruelle`.
**Estimated effort**: 2–4 weeks of focused work, with one identified high-risk piece (sub-lemma 4 below) that may force adding a structural hypothesis on the spectral side.
**Vetting status**: DRAFT (this file). Not yet executed.
**Author**: Michael Douglas (Claude Code), 2026-05-10.

---

## What's being closed

`W_analytic_cluster_integral_via_ruelle` (henceforth WCIVR) is the OS-side cluster theorem for the Wick-rotated boundary integral. Its statement (paraphrased):

> For OPTR-supported `f : SchwartzNPoint d n` and `g : SchwartzNPoint d m`, given `RuelleAnalyticClusterHypotheses Wfn n m`, the joint Wick-rotated integral
> ```
> ∫ F_ext_on_translatedPET_total Wfn (wick(x_n, x_m + (0,a))) · (f ⊗ g_a)(x) dx
> ```
> converges to the product of single-block integrals `L_n · L_m` as `|⃗a| → ∞`.

The proof body is currently `sorry`'d at the dominator-integrability step. The reason: the regulator-corrected `RACH.bound` produces a bound with a `(1 + Δ(Im z)⁻¹)^M` factor (Streater-Wightman 3.1.1 shape), which after Wick rotation becomes `(1 + Δ(time-diffs)⁻¹)^M` — a codimension-1 diagonal singularity that's **not locally integrable for `M ≥ 1`**. The naive pointwise-dominator + DC route therefore fails.

The textbook resolution (Streater-Wightman §3.4 / Ruelle 1962 / Araki-Hepp-Ruelle 1962) goes through the **Schwartz dual pairing**, not pointwise dominators. That's what this rework implements.

---

## Architecture

The Schwartz-pairing argument has six pieces, in order of dependency:

```
[Wfn.spectrum_condition_compact_subset]    ← already shipped (Phase 3 soft, commit 973617a)
        │
        │  bv_implies_fourier_support           ← already relaxed (commit ebd007f)
        ▼
[Tflat : SchwartzMap → ℂ on the dual cone]
        │
        │  fl_representation_from_bv
        ▼
[W_analytic_BHW(z) = (FL Tflat)(z) on ForwardTube d (n+m)]
        │
        │  Sub-lemma 1: extract Tflat for W_analytic_BHW.
        │  Sub-lemma 2: reduce W_analytic_BHW(joint Wick config) to FL form.
        │  Sub-lemma 3: Schwartz-Fubini exchange.
        ▼
[Joint integral = Tflat(Ψ_a)] where Ψ_a is Schwartz on dual cone, parameterized by `a`
        │
        │  Sub-lemma 4: Tflat(Ψ_a) → Tflat(Ψ_∞) as |⃗a| → ∞
        │              (cluster spectral RL — the load-bearing piece)
        │
        │  Sub-lemma 5: identify Tflat(Ψ_∞) with L_n · L_m (single-block products)
        ▼
[WCIVR conclusion: joint integral → L_n · L_m]
```

---

## Sub-lemma 1: Tflat extraction for W_analytic_BHW

**Goal**: produce `Tflat_BHW : SchwartzMap (Fin ((n+m)*(d+1)) → ℝ) ℂ →L[ℂ] ℂ` with `HasFourierSupportInDualCone (eR '' ForwardConeAbs d (n+m)) Tflat_BHW` such that

```
W_analytic_BHW Wfn (n+m)  =  fourierLaplaceExtMultiDim ... Tflat_BHW
```

on `ForwardTube d (n+m)`.

**Inputs**:
- `Wfn.spectrum_condition_compact_subset (n+m)` (compact-subset polynomial growth, satisfiable form, shipped in 973617a).
- `bv_implies_fourier_support` (relaxed in ebd007f to take compact-subset growth).
- `fl_representation_from_bv` (existing axiom; takes growth + BV → produces FL representation).

**Mechanical wiring**:
1. Identify the `W_analytic` witness inside `Wfn.spectrum_condition_compact_subset (n+m)` with `(W_analytic_BHW Wfn (n+m)).val` on the forward-tube portion of PET. This is a uniqueness argument via `tube_holomorphic_unique_from_bv` — both `W_analytic_BHW` and the witness from `spectrum_condition_compact_subset` are tube-holomorphic with the same boundary values on the forward tube, so they coincide.
2. Apply `bv_implies_fourier_support` with:
   - `C := ForwardConeAbs d (n+m)` (the imaginary-part cone for `ForwardTube d (n+m)`).
   - `F := W_analytic_BHW Wfn (n+m)` (restricted to the forward-tube image).
   - `hF_growth := compact-subset form from spectrum_condition_compact_subset`.
   - `hF_bv := boundary value clause from spectrum_condition_compact_subset`.
3. Obtain `Tflat_BHW` and the FL-extension equality.

**Estimated effort**: ~3–5 days.

**Risks**:
- The witness identification (step 1) requires `tube_holomorphic_unique_from_bv` to apply to both `W_analytic_BHW` and the `spectrum_condition_compact_subset` witness. The two functions need to have the same BVs on `ForwardTube`. For `W_analytic_BHW`, this requires its construction to expose the BVs in a form compatible with `spectrum_condition_compact_subset`'s clause. This may need bridging work through existing `BHWExtension.lean` lemmas.

**Deliverable**: a theorem
```lean
theorem W_analytic_BHW_fl_representation
    (Wfn : WightmanFunctions d) (n m : ℕ) :
    ∃ (Tflat : SchwartzMap (Fin ((n+m) * (d+1)) → ℝ) ℂ →L[ℂ] ℂ),
      HasFourierSupportInDualCone (...) Tflat ∧
      ∀ z ∈ ForwardTube d (n+m),
        (W_analytic_BHW Wfn (n+m)).val z =
          fourierLaplaceExtMultiDim ... Tflat (flatten z)
```

---

## Sub-lemma 2: Joint Wick config in FL form

**Goal**: express `W_analytic_BHW Wfn (n+m) (joint Wick config (z₁, z₂ + (0,a)))` as a Schwartz pairing for `(z₁, z₂)` in OPTR-Wick-rotation image.

**Inputs**:
- Sub-lemma 1's Tflat representation.
- `joint_wick_config_in_PET` (existing in `RuelleClusterBound.lean`) — joint Wick config lies in PET for OPTR-supported configs with distinct times.

**Plan**: substitute the joint config into the FL representation:
```
W_analytic_BHW(joint(wick z₁, wick z₂ + (0,a))) =
  Tflat_BHW(ψ_{joint(wick z₁, wick z₂ + (0,a))})
```
where `ψ_z(ξ) = exp(i ξ · flatten(z))` (the FL kernel, restricted to a Schwartz-cutoff support compatible with Tflat's dual cone).

The `(0,a)` shift on the m-block gives:
```
flatten(joint(wick z₁, wick z₂ + (0,a))) = flatten(joint(wick z₁, wick z₂)) + (0_{n-block}, (0,a)-shift_{m-block})
```
so
```
ψ_{joint with shift a} = exp(i · (n-block ξ part) · flatten(wick z₁))
                       · exp(i · (m-block ξ part) · flatten(wick z₂))
                       · exp(i · (m-block spatial ξ part) · a⃗)
```

The last factor `exp(i · m-block spatial · a⃗)` is the **only `a`-dependent piece** — and it's a phase factor. This is the structural heart of the cluster argument: shifting the m-block spatially adds a phase to the spectral pairing, and that phase oscillates as `|⃗a| → ∞`.

**Estimated effort**: ~3–5 days.

**Risks**: low. Mostly algebra of the FL kernel + Wick rotation. The `joint_wick_config_in_PET` infrastructure already exists.

**Deliverable**: a `=` identity expressing the cluster integrand as `Tflat_BHW(ψ_{wick(z₁,z₂),a})` for an explicit Schwartz-parameterized family.

---

## Sub-lemma 3: Schwartz-Fubini exchange

**Goal**: interchange the `(p₁, p₂)` integral with the `Tflat_BHW` pairing.

```
∫_{p₁, p₂} W_analytic_BHW(joint(wick p₁, wick p₂ + (0,a))) · f(p₁) · g(p₂) dp₁ dp₂
  =  Tflat_BHW( ∫_{p₁, p₂} ψ_{joint(wick p₁, wick p₂ + (0,a))} · f(p₁) · g(p₂) dp₁ dp₂ )
  =:  Tflat_BHW( Ψ_a )
```

where `Ψ_a` is the Bochner integral of the Schwartz family `ψ_{joint}` weighted by `f ⊗ g`.

**Inputs**:
- Existing project axiom `schwartz_clm_fubini_exchange` (`OSReconstruction/GeneralResults/SchwartzFubini.lean`) — exactly this Fubini-CLM exchange for Schwartz-valued families. Already vetted "Standard".

**Plan**:
1. Verify the Schwartz-valued family `(p₁, p₂) ↦ ψ_{joint(wick p₁, wick p₂ + (0,a))}` has polynomial seminorm growth in `(p₁, p₂)` (needed for `schwartz_clm_fubini_exchange`'s hypothesis).
2. Apply the axiom to obtain the equality above, defining `Ψ_a` along the way.

**Estimated effort**: ~3 days.

**Risks**: low. The seminorm-growth bound on the Schwartz-valued family is mechanical.

**Deliverable**: a Schwartz function `Ψ_a : SchwartzMap (Fin ((n+m)(d+1)) → ℝ) ℂ` constructed from `(f, g, a)` and the Wick kernel, plus the equality `joint integral = Tflat_BHW(Ψ_a)`.

---

## Sub-lemma 4: Tflat_BHW(Ψ_a) → Tflat_BHW(Ψ_∞) as |⃗a| → ∞

**This is the load-bearing piece.** Everything else is wiring; this is the actual cluster-decay content.

**Goal**: `Tflat_BHW(Ψ_a) → Tflat_BHW(Ψ_∞)` as `|⃗a| → ∞`, where `Ψ_∞` is the disconnected limit.

**Decomposition of Ψ_a**: per Sub-lemma 2, `Ψ_a` factors as
```
Ψ_a(ξ) = (n-block factor: depends on ξ_n, f̂)
       · (m-block factor: depends on ξ_m, ĝ)
       · exp(i · ξ_{m-spatial} · a⃗)
```

(Schematically — the actual form involves the Wick kernel and integration variables. The phase `exp(i · ξ_{m-spatial} · a⃗)` is the only `a`-dependent piece.)

**Why this gives cluster decay**:
- `Tflat_BHW(Ψ_a)` is a tempered-distribution pairing.
- The phase factor `exp(i · ξ_{m-spatial} · a⃗)` oscillates with `a⃗` along the m-block spatial frequencies.
- By spectral RL on tempered distributions: if `Tflat_BHW`'s spectral content has no atom at `ξ_{m-spatial} = 0` on the off-diagonal piece (the part connecting n-block and m-block), the pairing decays to 0 as `|a⃗| → ∞`.
- The DIAGONAL piece (n-block ⊗ m-block disconnected) is independent of `a⃗`, contributing the `Ψ_∞` limit.

This is **the same mathematical content as L2** (`gns_orthogonal_spatial_cobounded_decay_of`), just on the Tflat side instead of the GNS Hilbert side.

**Two paths**:

### Path 4.A — direct decay proof on Tflat (analogous to L5/L2)

Treat `Tflat_BHW` as having sufficient spectral structure to apply a Riemann-Lebesgue-type argument:
- `Tflat_BHW` has support in the dual cone (from `bv_implies_fourier_support`).
- The off-diagonal part of `Tflat_BHW` (paired against `Ψ_a`'s phase factor) has no zero-momentum atom at `ξ_{m-spatial} = 0`.
- Therefore the pairing decays.

This requires either:
- Proving that Tflat decomposes into a "diagonal" piece (constant in `a`) + "off-diagonal" piece (decays with `a`). This decomposition is the Wightman R4 cluster axiom transported to the spectral side via SNAG/FL — substantial.
- Or invoking an L4-style spectral data axiom on Tflat: introduce `Tflat_ClusterDecay : SchwartzMap (...) → 𝓒(SpacetimeDim → 𝓢(...))` capturing the cluster decomposition.

**Estimated effort**: 1–2 weeks for a direct proof; 3 days if we axiomatize the decomposition (Likely "Standard" textbook content per S-W §3.5).

### Path 4.B — reduce to L2 via GNS-spectral identification

The Wightman axioms `Wfn` already include `Wfn.cluster` (R4). The R4 cluster on Wightman functions is mathematically equivalent to:
- `gns_orthogonal_spatial_cobounded_decay_of` content (the GNS-spectral form, conditional in PR #86).
- Both reduce to the same SNAG-derived spectral measure on the GNS Hilbert space without a zero-momentum atom on `Ω⊥`.

Path 4.B identifies `Tflat_BHW`'s off-diagonal piece with the GNS off-diagonal matrix-element spectral measure, then quotes `gns_orthogonal_spatial_cobounded_decay_of` (or its appropriate analog) to get the cluster decay.

This requires bridging:
- Tflat_BHW (constructed from W_analytic_BHW's BV via `bv_implies_fourier_support`).
- GNS off-diagonal matrix elements `⟨Φ, U(a) ψ⟩` for appropriate `Φ, ψ` constructed from `f, g`.

The link is the Wightman reconstruction identity:
```
W_analytic_BHW(z₁ ⊕ z₂) = ⟨Φ_{z₁}^*, Φ_{z₂}⟩
```
for analytic Hilbert-space states `Φ_z := exp(-yP) φ(x) Ω` (analytic continuation of `φ(x) Ω` in y = Im(z)).

**Estimated effort**: 1–2 weeks. Bridging is non-trivial but uses existing GNS infrastructure (`GNSHilbertSpace.lean`).

### Path 4.C — assume cluster spectral data

Add a structural hypothesis (analogous to `L4SpectralData`) capturing what we need: a decomposition of `Tflat_BHW` into diagonal + decaying-off-diagonal parts.

```lean
structure ClusterSpectralData (Wfn : WightmanFunctions d) (n m : ℕ) : Prop where
  data :
    ∃ (Tflat_BHW : SchwartzMap → ℂ),
      [...Tflat_BHW = FL extension of W_analytic_BHW (n+m)...] ∧
      ∀ (Ψ : SchwartzMap),
        Filter.Tendsto (fun a => Tflat_BHW(Ψ_a)) cobounded (𝓝 (Tflat_BHW(Ψ_∞)))
        [...where Ψ_a is Ψ shifted by phase exp(i ξ · a)...]
```

Then close the cluster sorry conditional on `ClusterSpectralData`. Discharge as a separate proof obligation (or axiom, with Gemini vetting).

**Estimated effort**: 3–5 days for the conditional reduction. Discharge is open-ended (similar trajectory to L4SpectralData).

### Recommendation for sub-lemma 4

Start with **Path 4.B** (reduce to L2/GNS) — it leverages existing infrastructure, is mathematically clean, and avoids new axioms. If bridging proves too difficult, fall back to **Path 4.C** (axiomatize cluster spectral decomposition) and add it to the trust audit.

Path 4.A (direct decay on Tflat) is the most ambitious and probably overkill for first pass.

---

## Sub-lemma 5: Identify Tflat_BHW(Ψ_∞) with L_n · L_m

**Goal**: the `a → ∞` limit `Tflat_BHW(Ψ_∞)` equals the product of single-block boundary integrals
```
L_n · L_m  =  (∫ W_analytic_BHW(wick z₁) · f(z₁) dz₁) · (∫ W_analytic_BHW(wick z₂) · g(z₂) dz₂)
```

**Plan**:
1. Compute `Ψ_∞` from Sub-lemma 4: it's the disconnected piece of `Ψ_a` (m-block phase factor `→ 0` on the off-diagonal, leaving only the disconnected `n-block × m-block` factor).
2. Apply Sub-lemma 1's FL representation in reverse to recover the n-block and m-block boundary integrals.
3. Tflat_BHW factorizes on the disconnected piece into Tflat_n ⊗ Tflat_m (this requires R4 cluster + spectral support analysis).

**Estimated effort**: ~5 days.

**Risks**: medium. The factorization Tflat_BHW → Tflat_n ⊗ Tflat_m on the disconnected piece IS an instance of cluster, but it's at the spectral level. May need careful handling.

---

## Sub-lemma 6 (glue): Combine 1–5 into the cluster theorem body

Replace the sorry at `RuelleClusterBound.lean:718` with:

```lean
-- (1) extract Tflat_BHW
obtain ⟨Tflat_BHW, hTflat_supp, hTflat_FL⟩ := W_analytic_BHW_fl_representation Wfn (n+m)
-- (2) joint config in FL form
have h_FL_joint := joint_FL_form Wfn n m ...  -- Sub-lemma 2
-- (3) Schwartz-Fubini
have h_fubini := schwartz_fubini_for_cluster Wfn n m f g a hsupp_f hsupp_g
-- (4) cluster-decay on Tflat_BHW
have h_decay := tflat_cluster_decay Wfn n m f g  -- Sub-lemma 4
-- (5) identify limit
have h_limit_id := tflat_disconnected_limit_eq_product Wfn n m f g  -- Sub-lemma 5
-- (6) conclude
exact ε-R conversion of (h_decay) to the existential form needed
```

**Estimated effort**: ~3 days.

---

## Total effort and risk

| Sub-lemma | Best case | Likely | Worst case | Risk |
|-----------|-----------|--------|------------|------|
| 1 (Tflat extraction) | 3 days | 5 days | 1 week | Witness-identification bridging |
| 2 (joint config FL form) | 3 days | 5 days | 1 week | Low — algebra |
| 3 (Schwartz-Fubini) | 2 days | 3 days | 1 week | Low — axiom available |
| 4 (cluster decay) | 1 week | 2 weeks | 4 weeks | **HIGH** — load-bearing |
| 5 (limit identification) | 3 days | 5 days | 1 week | Medium — Tflat factorization |
| 6 (glue) | 2 days | 3 days | 1 week | Low — assembly |
| **Total** | **2.5 weeks** | **3.5 weeks** | **~9 weeks** | |

**Risk concentration**: sub-lemma 4 dominates the timeline. Mitigation: Path 4.B (reduce to existing L2/GNS) keeps it bounded; Path 4.C (axiomatize) caps at 1 week with the cost of a new vetted axiom.

---

## Outputs of this rework

After completion, the cluster theorem `W_analytic_cluster_integral_via_ruelle` is **fully proved** (no `sorry` in body) **conditional on** `RuelleAnalyticClusterHypotheses Wfn n m` (the existing hypothesis structure).

Discharging RACH itself is the *separate* next phase:
- `RACH.bound` → `L4SpectralData` is proved (PR #86).
- `RACH.pointwise` → would follow from `L2SpectralData` + GNS bridging (parts shipped in PR #86; full discharge still open).

So the IBP rework closes one of three remaining items for unconditional E4-cluster on the Schwinger side. The other two are RACH discharge (L1/L3/L6/L7 chain) and the schwinger_E4 bridge (already in place).

---

## Open questions for the user before I start

1. **Path choice for sub-lemma 4**: lean toward 4.B (reduce to L2/GNS), with 4.C (axiomatize) as a safety net? Or push for 4.A (direct decay on Tflat)?
2. **Branching strategy**: continue on `r2e/ruelle-poly-bound-chain`, or fork a new branch `r2e/cluster-ibp-rework` from current head? Forking keeps the chain-repair changes separable and PR-able.
3. **PR cadence**: ship the chain-repair (3 commits already on branch) as a small PR first, then the IBP rework on a follow-up branch? Or accumulate everything on one branch?
4. **Coordination with Xi**: the IBP rework touches `RuelleClusterBound.lean` (his code area, even though I authored RACH). PR-ing it directly is fine, or discuss approach with him first?

---

## Pre-reqs already in place

- ✅ `Wfn.spectrum_condition_compact_subset` (commit `973617a`).
- ✅ `bv_implies_fourier_support` relaxed (commit `ebd007f`).
- ✅ `vladimirov_tillmann` consumer relaxed.
- ✅ `hasCompactSubsetGrowth_of_global_polyGrowth` helper.
- ✅ `fl_representation_from_bv` axiom (existing; vetted).
- ✅ `fourierLaplaceExtMultiDim_vladimirov_growth` proved (existing).
- ✅ `schwartz_clm_fubini_exchange` axiom (existing; vetted).
- ✅ `joint_wick_config_in_PET` (existing helper in RuelleClusterBound.lean).

Everything needed for sub-lemmas 1–3 is in place. Sub-lemma 4's path is the main open architecture decision.
