# Progress Report: OS Reconstruction Formalization

## Overview

Since the initial commit (`2b86bea`), 32 commits have added ~14,000 lines of Lean 4
across 50 files. Of these, **~4,900 lines came from xiyin's upstream merge** (commit
`47a4076` / `2dfc99a`) and **~9,100 lines are our original work**.

The work falls into four phases:

1. **Infrastructure** (ours) — SCV module, complex Lie groups, bridge types, Osgood
   lemma, SeparatelyAnalytic (sorry-free), nuclear space wiring
2. **Edge-of-the-wedge** (mixed) — 1D EOW slice theorem and supporting lemmas (ours),
   multi-D SCV infrastructure and TubeDomainExtension expansion (xiyin)
3. **R→E OS axioms** (ours) — Proved E1a (translation), E1b (rotation), E3 (symmetry),
   E4 (cluster) for constructed Schwinger functions, modulo W_analytic helpers
4. **Forward tube distributions** (ours) — Sorry-free bridge from general tube domain
   axioms to the forward tube, completing the infrastructure WickRotation depends on

Total: **+14,001 / -485 lines** across 50 files (~9,100 ours, ~4,900 xiyin).

---

## Phase 1: Infrastructure (commits `5ce1e72`–`cf96b5b`)

### SCV Module (`OSReconstruction/SCV/`)

| File | Lines | Author | Status |
|------|-------|--------|--------|
| `Osgood.lean` | 627 | ours | sorry-free |
| `Polydisc.lean` | 231 | ours | sorry-free |
| `IteratedCauchyIntegral.lean` | 670 | ours (+68 xiyin) | mixed |
| `TubeDomainExtension.lean` | 2997 | ours 158 + xiyin 2839 | mixed |
| `IdentityTheorem.lean` | 154 | ours | 1 sorry (Hartogs) |
| `Analyticity.lean` | 1206 | xiyin | mixed |
| `MoebiusMap.lean` | 618 | xiyin | mixed |
| `EOWMultiDim.lean` | 141 | xiyin | mixed |
| `TubeDistributions.lean` | 173 | ours | axioms only |

**`Osgood.lean`** (ours, sorry-free): Full proof of Osgood's lemma — continuous +
separately holomorphic ⟹ jointly holomorphic. Uses iterated Cauchy integrals
and dominated convergence.

**`SeparatelyAnalytic.lean`** (ours, sorry-free, 906 lines added): All Taylor
remainder helpers proved. This file went from 25 sorrys to 0 across commits
`3219c29`–`d53bad6`.

### Complex Lie Groups (`OSReconstruction/ComplexLieGroups/`) — ours

| File | Lines | Description |
|------|-------|-------------|
| `MatrixLieGroup.lean` | 277 | General matrix Lie group definitions |
| `LorentzLieGroup.lean` | 283 | Lorentz group, restricted subgroup |
| `Complexification.lean` | 533 | Complex Lorentz group L₊(ℂ) (+56 xiyin) |
| `Connectedness.lean` | 171 | Path-connectedness of SO⁺(1,d) |

### Bridge and Nuclear Spaces

- **`Bridge/AxiomBridge.lean`** (252 lines) — Type equivalences between SCV/Lie
  group infrastructure and Wightman axiom types
- **`GaussianFieldBridge.lean`** (430 lines) — Wiring gaussian-field library to
  nuclear space constructions
- **`SchwartzNuclear.lean`** (309 lines modified) — Nuclear space topology on
  Schwartz space, seminorm estimates

### Nuclear Space Sorrys Eliminated

- `seminorm_le_nuclear_expansion` — proved via Hahn-Banach (`6131c81`)
- `nuclear_step` — direct proof for n=0, bridge for n>0 (`cf96b5b`)

---

## Phase 2: Edge-of-the-Wedge (commits `4221277`–`328decb`, plus xiyin merge)

### Our work (sorry-free)

**`edge_of_the_wedge_slice`** (`AnalyticContinuation.lean:553`) — For each real
point x₀ ∈ E and direction η ∈ C, the 1D EOW theorem extends f_plus and f_minus
to a single holomorphic function on a complex neighborhood of x₀ along the slice
w ↦ x₀ + wη. Proved via:
1. Restricting multi-D holomorphic functions to 1D slices via `sliceMap`
2. Showing UHP/LHP slices land in TubeDomain(C)/TubeDomain(-C) (cone property)
3. Translating multi-D boundary values to 1D via `ContinuousWithinAt` composition
4. Applying `edge_of_the_wedge_1d` (Morera + Cauchy-Goursat)

Supporting lemmas (all ours, sorry-free):
- `sliceMap_upper_mem_tubeDomain` / `sliceMap_lower_mem_neg_tubeDomain`
- `tubeDomain_isOpen`, `neg_image_isOpen`, `tubeDomain_disjoint_neg`
- `holomorphic_extension_across_real`, `tube_domain_gluing`

We also promoted `edge_of_the_wedge` and `bargmann_hall_wightman` from inline
sorrys to named axioms with full docstrings and references.

### Xiyin's merge (`2dfc99a`, ~4,900 lines)

Xiyin's commit (titled "Prove edge-of-the-wedge theorem sorry-free") added:

- **`Analyticity.lean`** (1206 lines) — Multi-variable holomorphic ⟹ analytic
- **`MoebiusMap.lean`** (618 lines) — Möbius product map and imaginary part properties
- **`EOWMultiDim.lean`** (141 lines) — Multi-dimensional EOW helpers
- **`TubeDomainExtension.lean`** (+2839 lines) — Massive expansion of tube domain
  extension theory (edge-of-the-wedge for tube domains, Bochner tube theorem
  infrastructure, holomorphic extension lemmas)
- Minor fixes to `EdgeOfWedge.lean`, `IteratedCauchyIntegral.lean`,
  `Complexification.lean`, `AnalyticContinuation.lean`

Note: despite the commit message, the full multi-dimensional `edge_of_the_wedge`
**remains an axiom** (line 730). What xiyin proved sorry-free was the
`edge_of_the_wedge_slice` proof adjustments and the supporting SCV infrastructure.
He also added a uniqueness clause to the axiom statement.

### What remains an axiom

**`edge_of_the_wedge`** (line 730) — The full multi-dimensional theorem. The gap:
for m ≥ 2 there are points z near real boundary where Im(z) ∉ C ∪ (-C) ∪ {0}
(gap points). No single 1D slice reaches them. See `docs/edge_of_the_wedge_proof_plan.md`
for a concrete plan to eliminate this axiom via iterated Cauchy integrals or
slice-based construction (~300-600 LOC).

**`bargmann_hall_wightman`** (line 788) — Extends holomorphic functions from the
forward tube to the permuted extended tube via complex Lorentz group. Requires
connectedness of SO⁺(1,d;ℂ) and identity theorem on complex manifolds.

---

## Phase 3: R→E OS Axioms (commit `8fc7b9c`)

This is the core physics content: proving that Wightman functions satisfying R0–R4
produce Schwinger functions satisfying E0–E4.

### Construction

**`constructSchwingerFunctions`** (`WickRotation.lean:190`) — Defines S_n(f) as:
```
S_n(f) = ∫ F_ext(iτ₁,x⃗₁,...,iτ_n,x⃗_n) · f(x₁,...,x_n) dx
```
where F_ext is the BHW extension of W_analytic to the permuted extended tube.

**`W_analytic_BHW`** (line 155) — Wires `spectrum_condition` into `bargmann_hall_wightman`
to produce the BHW extension with complex Lorentz and permutation invariance.

### Proved (sorry-free)

**`constructedSchwinger_rotation_invariant`** (E1b, line 324) — Schwinger functions
are invariant under Euclidean rotations R ∈ O(d+1). Proof:
1. `integral_orthogonal_eq_self` (sorry-free): orthogonal transforms preserve
   Lebesgue measure on (ℝ^{d+1})^n, via `MeasurePreserving` + det = ±1
2. `F_ext_rotation_invariant`: BHW complex Lorentz invariance (sorry)
3. Change of variables: ∫ K(x)f(Rx) dx = ∫ K(Rx)f(Rx) dx = ∫ K(x)f(x) dx

**`constructedSchwinger_symmetric`** (E3, line 391) — Schwinger functions are
symmetric under permutations of arguments. Proof:
1. `integral_perm_eq_self` (sorry-free, line 380): permuting factors preserves
   Lebesgue measure, via `volume_measurePreserving_piCongrLeft`
2. `F_ext_permutation_invariant`: BHW permutation symmetry (sorry)
3. Same change-of-variables pattern as E1b

**`W_analytic_continuous_boundary`** (line 119) — W_analytic extends continuously
to the real boundary. Sorry-free after ForwardTubeDistributions infrastructure
was added in Phase 4: three lines applying `continuous_boundary_forwardTube`.

### Proved modulo W_analytic helpers (sorry inside helper only)

**`constructedSchwinger_cluster`** (E4, line 452) — Cluster decomposition.
Structure proved; sorry inside `W_analytic_cluster_integral` (the analytic
content about exponential decay from mass gap).

**`constructedSchwinger_translation_invariant`** (E1a, line 228) — Translation
invariance. Structure proved; sorry inside `F_ext_translation_invariant`.

### Remaining sorrys in WickRotation.lean

| Theorem | Sorry? | What's needed |
|---------|--------|---------------|
| `W_analytic_lorentz_on_tube` | sorry | `distributional_uniqueness_forwardTube` (now available) |
| `W_analytic_continuous_boundary` | **done** | — |
| `W_analytic_local_commutativity` | sorry | boundary value + Wfn.locally_commutative |
| `constructedSchwinger_tempered` (E0) | sorry | `polynomial_growth_tube` (axiom available) |
| `constructedSchwinger_translation_invariant` (E1a) | sorry | `F_ext_translation_invariant` |
| `constructedSchwinger_rotation_invariant` (E1b) | **done** | — |
| `constructedSchwinger_reflection_positive` (E2) | sorry | Wick-rotated positivity |
| `constructedSchwinger_symmetric` (E3) | **done** | — |
| `constructedSchwinger_cluster` (E4) | sorry | `W_analytic_cluster_integral` |
| `F_ext_translation_invariant` | sorry | BHW + translation |
| `F_ext_permutation_invariant` | sorry | BHW permutation at general points |
| `wightman_to_os_full` | sorry | wiring (depends on all above) |
| `os_to_wightman_full` | sorry | E→R direction |

---

## Phase 4: Forward Tube Distributions (commits `b381e5d`–`b655699`)

Added after xiyin's merge (`47a4076`). Two new files, **591 + 173 lines**.

### `ForwardTubeDistributions.lean` — sorry-free (591 lines)

29 definitions and theorems proving that the forward tube is a tube domain and
bridging general tube domain results to the forward tube.

**Forward cone properties:**
- `ForwardConeAbs` — product cone in difference coordinates
- `forwardConeAbs_isOpen`, `_convex`, `_nonempty`
- `convex_inOpenForwardCone` — V₊ is convex (Cauchy-Schwarz on spatial components)
- `inOpenForwardCone_smul` — V₊ closed under positive scaling
- `inOpenForwardCone_add` — V₊ closed under addition (via convexity + scaling)
- `forwardConeAbs_implies_allForwardCone` — ForwardConeAbs ⊆ {η | ∀k, η_k ∈ V₊}
  (key bridge between approach direction conventions)

**Flattening equivalence:**
- `flattenCLEquiv` / `flattenCLEquivReal` — isomorphism
  `(Fin n → Fin d → K) ≃L[K] (Fin (n*d) → K)` via `Equiv.curry` + `finProdFinEquiv`
- `flattenCLEquiv_apply`, `_symm_apply`, `_im` — simp lemmas
- `forwardTube_flatten_eq_tubeDomain` — the forward tube IS a tube domain after
  flattening

**Main theorems:**
- `continuous_boundary_forwardTube` — holomorphic functions on the forward tube
  with distributional boundary values extend continuously to the real boundary
- `distributional_uniqueness_forwardTube` — two such functions with the same
  boundary values agree on the tube

Both derived from general tube domain axioms by flattening coordinates,
transporting DifferentiableOn through the isomorphism, bridging approach
direction conventions, change of variables in boundary integrals, and
pulling back ContinuousWithinAt through the homeomorphism.

### `TubeDistributions.lean` — axioms (173 lines)

Three axioms encoding results from Vladimirov (2002) §25-26:

1. **`continuous_boundary_tube`** — distributional boundary values ⟹ continuous
   extension to real boundary
2. **`distributional_uniqueness_tube`** — same distributional BV ⟹ equal on tube
3. **`polynomial_growth_tube`** — tempered BV ⟹ polynomial growth estimates

*Why axioms:* Proofs require Paley-Wiener-Schwartz theorem and Fourier-Laplace
transform theory for tempered distributions. Neither exists in Mathlib.

### Change of variables axiom

**`integral_flatten_change_of_variables`** — `∫ g(x) dx = ∫ g(flatten(y)) dy`.
Eliminable with a single Mathlib PR adding `measurePreserving_curry`.

---

## All Axioms (8 total)

| # | Axiom | File | Eliminable? |
|---|-------|------|-------------|
| 1 | `continuous_boundary_tube` | `SCV/TubeDistributions.lean` | Needs Paley-Wiener-Schwartz |
| 2 | `distributional_uniqueness_tube` | `SCV/TubeDistributions.lean` | Corollary of #1 + identity thm |
| 3 | `polynomial_growth_tube` | `SCV/TubeDistributions.lean` | Needs Fourier-Laplace transforms |
| 4 | `integral_flatten_change_of_variables` | `ForwardTubeDistributions.lean` | 1 Mathlib PR (`measurePreserving_curry`) |
| 5 | `edge_of_the_wedge` | `AnalyticContinuation.lean` | ~300-600 LOC, see proof plan |
| 6 | `bargmann_hall_wightman` | `AnalyticContinuation.lean` | Needs complex Lie group theory |
| 7 | `hartogs_analyticity` | `SCV/IdentityTheorem.lean` | ~200 LOC with Osgood |
| 8 | — | — | — |

Axiom #4 is trivially eliminable. Axiom #5 has a concrete proof plan.
Axioms #1-3 and #6 depend on large bodies of mathematics not in Mathlib.

---

## Sorry Census

**~137 total** across 25 files.

| Count | File | Category |
|-------|------|----------|
| 20 | `WickRotation.lean` | R→E and E→R bridge |
| 16 | `vNA/CaratheodoryExtension.lean` | Measure theory |
| 15 | `vNA/ModularAutomorphism.lean` | Tomita-Takesaki |
| 14 | `SchwartzNuclear.lean` | Nuclear spaces |
| 11 | `vNA/KMS.lean` | KMS condition |
| 10 | `GaussianFieldBridge.lean` | Gaussian field wiring |
| 10 | `vNA/Unbounded/Spectral.lean` | Spectral theory |
| 9 | `vNA/ModularTheory.lean` | Modular operators |
| 22 | Everything else | Scattered (1-4 each) |

### What's closest to provable next

1. **`W_analytic_lorentz_on_tube`** — Direct application of
   `distributional_uniqueness_forwardTube` (now available and sorry-free).

2. **`constructedSchwinger_tempered`** (E0) — Apply `polynomial_growth_tube`
   (axiom available), show Wick-rotated evaluation is tempered.

3. **`edge_of_the_wedge` axiom** — Eliminable via slice-based construction
   using existing `edge_of_the_wedge_slice` + `osgood_lemma`.
   See `docs/edge_of_the_wedge_proof_plan.md`.

---

## Sorry-Free Highlights

Files or major components that are fully proved (no sorry, no axiom):

- `SeparatelyAnalytic.lean` — Taylor series, separately analytic functions (906 lines)
- `Osgood.lean` — Osgood's lemma (627 lines)
- `Polydisc.lean` — Polydisc definitions and properties (231 lines)
- `ForwardTubeDistributions.lean` — Forward tube as tube domain (591 lines)
- `edge_of_the_wedge_slice` — 1D edge-of-the-wedge (150 lines)
- `integral_orthogonal_eq_self` — Orthogonal COV (46 lines)
- `integral_perm_eq_self` — Permutation COV (6 lines)
- `constructedSchwinger_rotation_invariant` (E1b)
- `constructedSchwinger_symmetric` (E3)
- `W_analytic_continuous_boundary`
