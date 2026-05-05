# Route A cluster plan — discharge of `W_analytic_cluster_integral`

Status as of 2026-05-04. Captures the GNS-class cluster route after
Round-2 Gemini vetting and Codex's corrections to my over-optimistic
summary.

---

## What we have

### Code
- `OSReconstruction/GeneralResults/SpectralAnalysis.lean` — vetted
  generic axioms (Riemann-Lebesgue with AC marginal, Schwartz-translation
  strong continuity).
- `OSReconstruction/GeneralResults/SNAGTheorem.lean` — `snag_theorem`
  (on main from PR #81).
- `OSReconstruction/Wightman/Spectral/KallenLehmann.lean` —
  `kallen_lehmann_representation` (proved 5-line theorem) plus
  vetted supporting axioms. Reusable infrastructure but **not on the
  cluster critical path**.
- `OSReconstruction/Wightman/Spectral/ClusterFromKL.lean` —
  - `WightmanReconstruction` class (vetted Rounds 1+2)
  - Instance projections `instNormedH`, `instInnerH`, `instCompleteH`
  - `cluster_inner_product_from_GNS` (Route A master theorem, scaffold
    + `h_U_isometry` proved, `h_main_id` open)
  - Three legacy Route-B sorrys, now off the critical path

### Vetting
- `docs/cluster_axiom_vetting.md` — Round 1 + Round 2 verdicts.
  3 axioms rejected as mathematically false; the rest standard or
  likely correct.

### Branch
`r2e/kallen-lehmann-revival` on `myfork`, ahead of `origin/main` by
~17 commits.

---

## What `cluster_inner_product_from_GNS` actually gives

Statement (line 797, `ClusterFromKL.lean`):
```
For ψ, φ ∈ WR.H,
   ⟨ψ, U(a) φ⟩  →  ⟨ψ, Ω⟩ · ⟨Ω, φ⟩
   as |⃗a| → ∞ along the spatial cobounded filter.
```

This is the **Hilbert-space cluster** — pure operator theory on the
GNS space. It is **not** the integral statement.

Class fields used directly in the proof body:
- `vac_norm` — for `⟨Ω, Ω⟩ = 1` via `inner_self_eq_norm_sq_to_K`.
- `vac_inv` — for `U(a) Ω = Ω` (and via this, `U(a)⋆ Ω = Ω`).
- `unitary_rep` — for `⟨U(a) x, U(a) y⟩ = ⟨x, y⟩` (via the
  `Unitary.star_mul_self_of_mem` + `ContinuousLinearMap.adjoint_inner_right`
  chain).
- `truncated_spatial_decay` — the analytic content. Indirectly carries
  the consequences of `vacuum_unique` (no nonzero state is U-invariant
  on the orthogonal complement of Ω), but not invoked by name in the
  proof.

Class fields **not** used in this theorem (but needed for the integral
form below): `quantize`, `schwinger_bridge`, `vacuum_expectation`.

The `quantize_add`, `quantize_smul`, `U_add`, and `vacuum_unique`
(direct) fields are **not on the cluster critical path** as currently
scoped — they're forward-looking infrastructure.

---

## Open subproblems on the path to `W_analytic_cluster_integral`

### Subproblem 1 — `h_main_id` (algebraic identity)

**Where**: `ClusterFromKL.lean`, body of `cluster_inner_product_from_GNS`.

**Goal**:
```
⟨ψ, U(a) φ⟩ = ⟨ψ, Ω⟩ · ⟨Ω, φ⟩ + ⟨ψ_perp, U(a) φ_perp⟩
```
where `ψ_perp := ψ - ⟨Ω, ψ⟩ • Ω`, similarly for φ_perp.

**Substance**: pure inner-product algebra. No new mathematical input;
no class field needed beyond what's already in scope.

**Required Lean machinery**:
- `inner_add_left`, `inner_add_right` for distribution
- `inner_smul_left` (pulls `starRingEnd 𝕜 c`), `inner_smul_right`
  (pulls `c`)
- `inner_conj_symm` for the `⟨ψ, Ω⟩ ↔ starRingEnd ⟨Ω, ψ⟩` flip
- `h_omega_self`, `h_omega_U_invariant`, `h_φ_ortho`, `h_ψ_ortho` —
  already proved in scope
- `RCLike.starRingEnd_apply` or `Complex.conj` simp lemmas

**Estimated effort**: ~30–50 lines. The session blocker was the
`starRingEnd 𝕜 ⟪y, x⟫` ↔ `⟪x, y⟫` direction in Mathlib's
`inner_conj_symm` (the version in the project's lockfile has the
`starRingEnd` on the LHS). A `calc` block is probably cleaner than
direct `rw` chaining.

**Owner**: anyone — pure Lean engineering.

---

### Subproblem 2 — Integral-form wrapper (`cluster_2point_OS_form`,
`cluster_npoint_OS_form`)

**Goal**: lift `cluster_inner_product_from_GNS` to a statement about
the OS-reflected Schwinger integral:
```
∫ F_ext(wick x) (f.osConj ⊗ g_a)(x) dx
   →  ⟨quantize f, Ω⟩ · ⟨Ω, quantize g⟩
   = (starRingEnd ℂ) (∫ F_ext f) · (∫ F_ext g)
```
for OPTR-supported `f, g`, as `|⃗a| → ∞` spatially.

**Class fields directly used by the bare wrapper**:
- `schwinger_bridge` — converts the joint integral to the inner product
- `vacuum_expectation` — converts each block integral to a bra-Ω inner
  product
- (Mathlib) `inner_conj_symm` — `⟨quantize f, Ω⟩ = (starRingEnd ℂ) ⟨Ω, quantize f⟩`.
  Not a class field, just inner-product-space symmetry.

`quantize_add`, `quantize_smul`, and `U_add` are **not** needed for the
bare wrapper — they're forward-looking infrastructure for downstream
distribution-level manipulations, not direct dependencies of this
theorem.

**Note**: this is **OS-reflected**. The `f.osConj` on the bra-block is
forced by the schwinger bridge. The conjugate on the bra-block integral
in the limit is forced by inner-product conjugate-linearity in the first
argument.

**Estimated effort**: ~30–50 lines once `h_main_id` is closed.

---

### Subproblem 3 — osConj bridge (the part I underestimated)

**Where**: between the OS-reflected cluster (Subproblem 2 output) and
the un-reflected statement of `W_analytic_cluster_integral`
(`SchwingerAxioms.lean:3786`).

**The mismatch**:
```
Route A delivers:  ∫ F_ext (f.osConj ⊗ g_a) → (conj ∫ F_ext f) · (∫ F_ext g)
Target wants:      ∫ F_ext (f       ⊗ g_a) → (∫ F_ext f) · (∫ F_ext g)
```

These are not the same integral. `f.osConj(x) = (f(Θx))*` where Θ flips
the time component — supported on negative-time-ordered configs, which
is *outside* OPTR.

**The mathematical content**:
For OPTR-supported `f, g` separately, the joint config (with `a`
spatial-only) lies in `TranslatedPET d (n+m)` because PET (Permuted
Extended Tube) is the union over permutations of forward-tube preimages,
and any joint OPTR config can be ordered by time into a permuted forward
tube. So `F_ext_on_translatedPET_total` is well-defined for both
integrals. But they have different values: their relationship involves
the Wightman analytic continuation under permutation, governed by
BHW symmetry.

**Three options for resolving this**:

1. **Modify the target statement**. Rewrite `W_analytic_cluster_integral`
   to match the OS-reflected form `∫ F_ext (f.osConj ⊗ g_a)`. This has
   downstream consequences (need to check `wickRotatedBoundaryPairing_cluster`
   and any consumer of `W_analytic_cluster_integral`).

2. **Add a bridge axiom** asserting that for OPTR-supported `f, g`:
   ```
   ∫ F_ext (f ⊗ g_a) (x) - ∫ F_ext (f.osConj ⊗ g_a) (x) → 0
   ```
   along the spatial-cobounded filter. This is in spirit a textbook
   fact (the OS reflection is unitary on OPTR-supported test functions
   modulo cluster-vanishing terms) but **stating it as a textbook axiom
   needs careful citation** — Glimm-Jaffe §6.1 / Streater-Wightman §3.3.
   Vet via Gemini.

3. **Prove the bridge from BHW**. The two integrals are related by
   permutation symmetry on PET, which `BHW_analytic_continuation`
   already handles. A real proof would unwind the permutation and
   apply BHW. Estimated: substantial — possibly weeks of dedicated
   work, comparable to the route-(i) attack we abandoned.

**Recommendation**: Option (2) — add a textbook axiom for the bridge,
vet it via Gemini, and treat it as a deferred discharge target.
This keeps Route A on a tractable schedule.

**Estimated effort** (option 2): ~10 lines axiom + ~50 lines of bridge
theorem composing with Subproblem 2 output. Plus Gemini vetting.

---

### Subproblem 4 — The `WightmanReconstruction` instance

**The big one.** Every Route A theorem is conditional on
`[WR : WightmanReconstruction Wfn]`. Until we provide an instance, the
chain ends at "given a Wightman GNS reconstruction".

**What it takes** to construct the instance from R0–R4:
1. OS quantization map `quantize : SchwartzNPoint d n → Hilbert space`
   from R2 (positivity) via Gel'fand-Naimark-Segal.
2. Translation unitary group `U(a)` from R3 (Euclidean covariance) via
   the OS-reconstructed Wightman GNS framework.
3. Strong continuity from R3 (continuous symmetry).
4. Vacuum invariance + uniqueness from R4 (cluster).
5. The bridge fields `schwinger_bridge`, `vacuum_expectation` from
   the OS analytic continuation (already substantially developed in
   the project's BHW + ForwardTube + WickRotation infrastructure).
6. `truncated_spatial_decay` from spectral analysis on the GNS space —
   itself a textbook result requiring SNAG + spectral support.

**Estimated effort**: ~3–6 weeks of dedicated work, or ~10–15 textbook
axioms with citations and Gemini vetting.

**Recommendation**: defer to a separate project sub-phase. State the
class instance as an axiom (with detailed citation) for now, and treat
the actual construction as the second-half R→E reconstruction project.

---

## The dependency graph (post-Codex-correction)

```
W_analytic_cluster_integral (target, SchwingerAxioms.lean:3786)
    │
    ├─ requires: Subproblem 3 — osConj bridge
    │
    └─ cluster_npoint_OS_form  (Subproblem 2 — to be written)
         │
         ├─ requires (direct): WR.schwinger_bridge, WR.vacuum_expectation,
         │                     Mathlib `inner_conj_symm`
         │
         └─ cluster_inner_product_from_GNS  (line 797, ClusterFromKL.lean)
              │
              ├─ requires: WR.vac_norm, WR.vac_inv, WR.unitary_rep,
              │            WR.truncated_spatial_decay
              │
              └─ remaining work: Subproblem 1 — h_main_id algebra

All conditional on: Subproblem 4 — WightmanReconstruction instance.
```

---

## Action items, in order

1. **(Mechanical, ~1–2 hours)** Close `h_main_id` in
   `cluster_inner_product_from_GNS`. Pure Lean engineering. Clears the
   first sorry in the Route A chain.

2. **(Mechanical, ~half day)** Write `cluster_2point_OS_form` using
   `schwinger_bridge` + `vacuum_expectation`. ~50 lines. This wraps
   Subproblem 1 into integral form.

3. **(Half day)** Generalize to `cluster_npoint_OS_form`. The proof
   is the same structure as Subproblem 2 but with `n+m` in place of
   `1+1`.

4. **(Decision point + Gemini vet, ~1 day)** Resolve Subproblem 3:
   pick option 1, 2, or 3. Default recommendation is option 2 — write
   the bridge axiom, send to Gemini, document the citation.

5. **(Major project, weeks)** Subproblem 4 — the `WightmanReconstruction`
   instance, or its axiomatization. Defer to a separate session.

6. **(Cleanup)** Once Subproblems 1–3 are closed, retire the legacy
   Route-B sorrys (`spectralFunction_cluster`, `cluster_2point_from_KL`,
   `cluster_npoint_from_KL`) — they're off the critical path.

---

## What we are NOT claiming

- That Route A is "almost done". It is a scaffolded reduction with one
  substantive Lean lemma proved (`h_U_isometry`). Real work remains on
  Subproblems 1–4.
- That the osConj bridge is a small step. It is the most underestimated
  piece. Plan for it explicitly.
- That `W_analytic_cluster_integral` is closed by adopting Route A. The
  class instance is itself a major sub-project.

What Route A *does* give us:
- A clean architectural reduction of cluster to GNS-Hilbert-space facts.
- Vetted, textbook-grounded class axioms with explicit citations.
- An incremental path: each subproblem is independently tractable.
- An off-ramp from the polynomial-growth obstruction that blocked
  Route (i).

---

## References (citations referenced from the class fields)

- Reed, Simon, *Methods of Modern Mathematical Physics*, Vol. I §V.3,
  Vol. II §IX.8 (translation continuity, spectral analysis).
- Streater, Wightman, *PCT, Spin and Statistics, and All That* §3.3
  (Wightman reconstruction).
- Glimm, Jaffe, *Quantum Physics*, Ch 19 (OS quantization),
  §6.1–6.2 (cluster + spectral).
- Osterwalder, Schrader, *Axioms for Euclidean Green's Functions* (1973),
  §3 (OS positivity / inner product), §4 (E4 cluster).
- Hörmander, *Analysis of Linear Partial Differential Operators I*,
  Theorem 7.1.18 (translation strong continuity).
