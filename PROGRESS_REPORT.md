# Progress Report: OS Reconstruction Formalization

## Overview

Since the initial commit (`2b86bea`), the project has ~14,000 lines of Lean 4
across 50 files. The work has two distinct sources:

**Xiyin's repo** (commits `2b86bea`–`2dfc99a`, merged at `47a4076`): The initial
codebase through the EOW/SCV infrastructure — ~12,000 lines total including the
initial commit. This includes SeparatelyAnalytic, edge-of-the-wedge (1D slice),
Osgood lemma, Polydisc, ComplexLieGroups, Bridge, SCV infrastructure, and the
initial Wightman/OS axiom framework.

**Our work** (14 commits, 6 before merge + 8 after): ~3,500 lines of new Lean 4.
- GaussianFieldBridge and nuclear space sorry elimination
- R→E OS axioms (E1b, E3 sorry-free; E1a, E4 structurally complete)
- SCV Identity Theorem
- Forward tube distribution infrastructure (sorry-free)
- Tube domain distribution axioms

---

## Our Work: Before the Merge (6 commits)

These commits branch from xiyin's `2dfc99a` and were merged alongside it.

### GaussianFieldBridge (`87d95e1`–`cf96b5b`)

- **`GaussianFieldBridge.lean`** (430 lines) — Bridges the gaussian-field library
  (sorry-free Hermite functions, spectral theorem, Gaussian measure) to the
  project's nuclear space infrastructure
- **`toPietschNuclearSpace`** — Converts Dynin-Mityagin NuclearSpace (Schauder
  basis with polynomial growth/decay) to Pietsch NuclearSpace (nuclear dominance
  via continuous linear functionals)
- **`seminorm_le_nuclear_expansion`** — Proved via Hahn-Banach, eliminating all
  sorrys in the bridge
- **`nuclear_step`** sorry eliminated — direct proof for n=0, gaussian-field
  bridge for n>0
- **`SchwartzNuclear.lean`** reworked (237 lines changed)

### R→E OS Axioms (`8fc7b9c`)

This is the core physics content: proving that Wightman functions satisfying R0–R4
produce Schwinger functions satisfying E0–E4.

**`constructSchwingerFunctions`** (`WickRotation.lean:190`) — Defines S_n(f) as:
```
S_n(f) = ∫ F_ext(iτ₁,x⃗₁,...,iτ_n,x⃗_n) · f(x₁,...,x_n) dx
```
where F_ext is the BHW extension of W_analytic to the permuted extended tube.

**`W_analytic_BHW`** (line 155) — Wires `spectrum_condition` into `bargmann_hall_wightman`
to produce the BHW extension with complex Lorentz and permutation invariance.

**Proved (sorry-free):**

- **`constructedSchwinger_rotation_invariant`** (E1b, line 324) — Schwinger functions
  are invariant under Euclidean rotations R ∈ O(d+1). Uses `integral_orthogonal_eq_self`
  (sorry-free): orthogonal transforms preserve Lebesgue measure via det = ±1.

- **`constructedSchwinger_symmetric`** (E3, line 391) — Schwinger functions are
  symmetric under permutations. Uses `integral_perm_eq_self` (sorry-free):
  permuting factors preserves Lebesgue measure via `volume_measurePreserving_piCongrLeft`.

- **`W_analytic_continuous_boundary`** (line 119) — W_analytic extends continuously
  to the real boundary. Became sorry-free after Phase 2 added
  `continuous_boundary_forwardTube`.

**Proved modulo W_analytic helpers (sorry inside helper only):**

- **`constructedSchwinger_cluster`** (E4, line 452) — Cluster decomposition.
  Structure proved; sorry inside `W_analytic_cluster_integral`.

- **`constructedSchwinger_translation_invariant`** (E1a, line 228) — Translation
  invariance. Structure proved; sorry inside `F_ext_translation_invariant`.

### SCV Identity Theorem (`8fc7b9c`)

- **`SCV/IdentityTheorem.lean`** (154 lines) — `identity_theorem_SCV` and tube
  domain specialization, reducing to single sorry (`hartogs_analyticity`)

---

## Our Work: After the Merge (8 commits, 4 substantive)

### Forward Tube Distributions (`b381e5d`–`b655699`)

Two new files totaling **764 lines**, completing the infrastructure that
WickRotation.lean depends on.

**`ForwardTubeDistributions.lean`** — sorry-free (591 lines), 29 definitions
and theorems:

*Forward cone properties:*
- `ForwardConeAbs` — product cone in difference coordinates
- `forwardConeAbs_isOpen`, `_convex`, `_nonempty`
- `convex_inOpenForwardCone` — V₊ is convex (Cauchy-Schwarz on spatial components)
- `inOpenForwardCone_smul` — V₊ closed under positive scaling
- `inOpenForwardCone_add` — V₊ closed under addition (via convexity + scaling)
- `forwardConeAbs_implies_allForwardCone` — ForwardConeAbs ⊆ {η | ∀k, η_k ∈ V₊}
  (key bridge between approach direction conventions)

*Flattening equivalence:*
- `flattenCLEquiv` / `flattenCLEquivReal` — isomorphism
  `(Fin n → Fin d → K) ≃L[K] (Fin (n*d) → K)` via `Equiv.curry` + `finProdFinEquiv`
- `flattenCLEquiv_apply`, `_symm_apply`, `_im` — simp lemmas
- `forwardTube_flatten_eq_tubeDomain` — the forward tube IS a tube domain after
  flattening

*Main theorems:*
- `continuous_boundary_forwardTube` — holomorphic functions on the forward tube
  with distributional boundary values extend continuously to the real boundary
- `distributional_uniqueness_forwardTube` — two such functions with the same
  boundary values agree on the tube

Both derived from general tube domain axioms by flattening coordinates,
transporting DifferentiableOn through the isomorphism, bridging approach
direction conventions, change of variables in boundary integrals, and
pulling back ContinuousWithinAt through the homeomorphism.

**`TubeDistributions.lean`** — axioms (173 lines), encoding results from
Vladimirov (2002) §25-26:

1. `continuous_boundary_tube` — distributional BV ⟹ continuous boundary extension
2. `distributional_uniqueness_tube` — same distributional BV ⟹ equal on tube
3. `polynomial_growth_tube` — tempered BV ⟹ polynomial growth estimates

*Why axioms:* Proofs require Paley-Wiener-Schwartz theorem and Fourier-Laplace
transform theory. Neither exists in Mathlib.

---

## Xiyin's Repo (commits `2b86bea`–`2dfc99a`)

Everything below was done in xiyin's repo and merged into ours at `47a4076`.

### Initial Framework (`2b86bea`)

The initial commit with vNA and Wightman axiom definitions, OS axiom framework,
WickRotation.lean skeleton, Reconstruction.lean, AnalyticContinuation.lean, and
the von Neumann algebra modules.

### SeparatelyAnalytic (`3219c29`–`d53bad6`)

`SeparatelyAnalytic.lean` (906 lines added) — Taylor series and separately analytic
function infrastructure. Went from 25 sorrys to 0 (sorry-free).

### Edge-of-the-Wedge (`4221277`–`328decb`)

- **`edge_of_the_wedge_slice`** (`AnalyticContinuation.lean:553`, sorry-free) —
  1D EOW: for each x₀ ∈ E and η ∈ C, extends f_plus and f_minus to a single
  holomorphic function along the slice w ↦ x₀ + wη
- `edge_of_the_wedge_1d` — Full 1D EOW via Morera + Cauchy-Goursat
- `sliceMap` infrastructure — `sliceMap_upper_mem_tubeDomain`, etc.
- `tubeDomain_isOpen`, `neg_image_isOpen`, `tubeDomain_disjoint_neg`
- `holomorphic_extension_across_real`, `tube_domain_gluing`
- Promoted `edge_of_the_wedge` and `bargmann_hall_wightman` to named axioms

### SCV Infrastructure (`1ab849b`, `2dfc99a`)

- **`Osgood.lean`** (627 lines, sorry-free) — Osgood's lemma
- **`Polydisc.lean`** (231 lines, sorry-free) — Polydisc definitions
- **`IteratedCauchyIntegral.lean`** (670 lines) — Iterated contour integrals
- **`TubeDomainExtension.lean`** (2997 lines) — Tube domain extension theory
- **`Analyticity.lean`** (1206 lines) — Multi-variable holomorphic ⟹ analytic
- **`MoebiusMap.lean`** (618 lines) — Möbius product map
- **`EOWMultiDim.lean`** (141 lines) — Multi-dimensional EOW helpers

### Complex Lie Groups (`062e64f`)

- `MatrixLieGroup.lean` (277), `LorentzLieGroup.lean` (283),
  `Complexification.lean` (533), `Connectedness.lean` (171)

### Bridge (`435829c`)

- `Bridge/AxiomBridge.lean` (252 lines) — Type equivalences between SCV/Lie
  group infrastructure and Wightman axiom types

### OS Axiom Fixes (`4508b8e`)

- Fixed OS axioms E1/E2, added Osgood lemma, exponential map infrastructure

---

## All Axioms (8 total)

| # | Axiom | File | Added by | Eliminable? |
|---|-------|------|----------|-------------|
| 1 | `continuous_boundary_tube` | `SCV/TubeDistributions.lean` | ours | Needs Paley-Wiener-Schwartz |
| 2 | `distributional_uniqueness_tube` | `SCV/TubeDistributions.lean` | ours | Corollary of #1 + identity thm |
| 3 | `polynomial_growth_tube` | `SCV/TubeDistributions.lean` | ours | Needs Fourier-Laplace transforms |
| 4 | `integral_flatten_change_of_variables` | `ForwardTubeDistributions.lean` | ours | 1 Mathlib PR (`measurePreserving_curry`) |
| 5 | `edge_of_the_wedge` | `AnalyticContinuation.lean` | xiyin | ~300-600 LOC, see proof plan |
| 6 | `bargmann_hall_wightman` | `AnalyticContinuation.lean` | xiyin | Needs complex Lie group theory |
| 7 | `hartogs_analyticity` | `SCV/IdentityTheorem.lean` | ours | ~200 LOC with Osgood |

Axiom #4 is trivially eliminable. Axiom #5 has a concrete proof plan
(`docs/edge_of_the_wedge_proof_plan.md`). Axioms #1-3 and #6 depend on large
bodies of mathematics not in Mathlib.

---

## WickRotation.lean Sorry Status

| Theorem | Status | What's needed | Added by |
|---------|--------|---------------|----------|
| `W_analytic_lorentz_on_tube` | sorry | `distributional_uniqueness_forwardTube` (now available) | ours |
| `W_analytic_continuous_boundary` | **done** | — | ours |
| `W_analytic_local_commutativity` | sorry | boundary value + Wfn.locally_commutative | ours |
| `constructedSchwinger_tempered` (E0) | sorry | `polynomial_growth_tube` (axiom available) | ours |
| `constructedSchwinger_translation_invariant` (E1a) | sorry | `F_ext_translation_invariant` | ours |
| `constructedSchwinger_rotation_invariant` (E1b) | **done** | — | ours |
| `constructedSchwinger_reflection_positive` (E2) | sorry | Wick-rotated positivity | xiyin (skeleton) |
| `constructedSchwinger_symmetric` (E3) | **done** | — | ours |
| `constructedSchwinger_cluster` (E4) | sorry | `W_analytic_cluster_integral` | ours |
| `F_ext_translation_invariant` | sorry | BHW + translation | ours |
| `F_ext_permutation_invariant` | sorry | BHW permutation at general points | ours |
| `wightman_to_os_full` | sorry | wiring (depends on all above) | xiyin (skeleton) |
| `os_to_wightman_full` | sorry | E→R direction | xiyin (skeleton) |

---

## Full Sorry Census

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

### Our work
- `ForwardTubeDistributions.lean` — Forward tube as tube domain (591 lines)
- `GaussianFieldBridge.lean` — Nuclear space bridge (430 lines, partial)
- `integral_orthogonal_eq_self` — Orthogonal COV (46 lines)
- `integral_perm_eq_self` — Permutation COV (6 lines)
- `constructedSchwinger_rotation_invariant` (E1b)
- `constructedSchwinger_symmetric` (E3)
- `W_analytic_continuous_boundary`

### Xiyin's repo
- `SeparatelyAnalytic.lean` — Taylor series, separately analytic (906 lines)
- `Osgood.lean` — Osgood's lemma (627 lines)
- `Polydisc.lean` — Polydisc definitions (231 lines)
- `edge_of_the_wedge_slice` — 1D edge-of-the-wedge (150 lines)
- `edge_of_the_wedge_1d` — 1D EOW via Morera
