# Progress Report: OS Reconstruction Formalization

## Overview

Since the initial commit (`2b86bea`), the project has ~14,000 lines of Lean 4
across 50 files. The work has two distinct sources:

**Xiyin's repo** (commits `2b86bea`–`2dfc99a`, merged at `47a4076`): The initial
codebase through the EOW/SCV infrastructure — ~12,000 lines total including the
initial commit. This includes SeparatelyAnalytic, edge-of-the-wedge (1D slice),
Osgood lemma, Polydisc, ComplexLieGroups, Bridge, SCV infrastructure, and the
initial Wightman/OS axiom framework.

**Our work** (18 commits, 6 before merge + 12 after): ~4,000 lines of new Lean 4.
- GaussianFieldBridge and nuclear space sorry elimination
- **E'→R' bridge (`os_to_wightman_full`) — sorry-free**
- **R→E bridge (`wightman_to_os_full`) — proven modulo 1 geometric sorry**
- Lorentz invariance on forward tube (`W_analytic_lorentz_on_tube`) — sorry-free
- SCV Identity Theorem
- Forward tube distribution infrastructure (sorry-free)
- Tube domain distribution axioms + Bochner tube theorem axiom
- Paley-Wiener axiom for inductive analytic continuation (OS II §IV)

---

## Our Work: Before the Merge (6 commits)

These commits branch from xiyin's `2dfc99a` and were merged alongside it.

### GaussianFieldBridge (`87d95e1`–`cf96b5b`, simplified `f905e04`)

- **`GaussianFieldBridge.lean`** (149 lines, sorry-free) — Bridges the gaussian-field
  library (sorry-free Hermite functions, spectral theorem, Gaussian measure,
  Pietsch nuclear space definition) to the project's nuclear space infrastructure
- The Pietsch nuclear space definition (`PietschNuclearSpace`) and the
  Dynin-Mityagin → Pietsch bridge proof (`toPietschNuclearSpace`) now live
  in gaussian-field (`Nuclear/PietschNuclear.lean`). The bridge file provides
  a trivial conversion to OSReconstruction's `NuclearSpace` typeclass.
- **`nuclear_step`** sorry eliminated — direct proof for n=0, gaussian-field
  bridge for n>0
- **`SchwartzNuclear.lean`** reworked (237 lines changed)

### R→E OS Axioms (`8fc7b9c`–`be5b63a`)

This is the core physics content: proving that Wightman functions satisfying R0–R4
produce Schwinger functions satisfying E0–E4.

**`constructSchwingerFunctions`** (`WickRotation.lean:190`) — Defines S_n(f) as:
```
S_n(f) = ∫ F_ext(iτ₁,x⃗₁,...,iτ_n,x⃗_n) · f(x₁,...,x_n) dx
```
where F_ext is the BHW extension of W_analytic to the permuted extended tube.

**`W_analytic_BHW`** (line 155) — Wires `spectrum_condition` into `bargmann_hall_wightman`
to produce the BHW extension with complex Lorentz and permutation invariance.

### SCV Identity Theorem (`8fc7b9c`)

- **`SCV/IdentityTheorem.lean`** (154 lines) — `identity_theorem_SCV` and tube
  domain specialization, reducing to single sorry (`hartogs_analyticity`)

---

## Our Work: After the Merge (12 commits, 8 substantive)

### Lorentz Invariance (`0306f8d`)

**`W_analytic_lorentz_on_tube`** — Proves that the analytic Wightman
function is Lorentz-invariant on the forward tube. Four helper lemmas:

- `restricted_preserves_forward_cone` — SO⁺(1,d) preserves V₊ (metric preservation
  via Lorentz condition + time component positivity via Cauchy-Schwarz). Sorry-free.
- `restricted_preserves_forward_tube` — Λ preserves forward tube (Im linearity +
  above). Sorry-free.
- `W_analytic_lorentz_holomorphic` — z ↦ W_analytic(Λz) is holomorphic (ℂ-linearity
  of Lorentz action + Finset induction for DifferentiableAt). Sorry-free.
- `W_analytic_lorentz_bv_agree` — Distributional BVs match (via two textbook axioms).

Final proof applies `distributional_uniqueness_forwardTube`.

### R→E E3/E1 Proofs + Axiom Infrastructure

- `constructedSchwinger_symmetric` (E3) — sorry-free via `integral_perm_eq_self`
- `constructedSchwinger_translation_invariant` (E1a) — sorry-free via
  `bhw_translation_invariant` axiom + `euclidean_points_in_permutedTube` axiom
- `constructedSchwinger_rotation_invariant` (E1b, det=1) — sorry-free via
  `schwinger_euclidean_invariant` + `integral_orthogonal_eq_self`
- `F_ext_permutation_invariant` — sorry-free from BHW permutation symmetry
- `F_ext_translation_invariant` — from bhw_translation_invariant axiom
- `F_ext_rotation_invariant` (det=1) — via complex Lorentz group embedding

**R→E direction status**: E1 (translation + rotation det=1) and E3 (permutation)
are fully proved. E0 (temperedness), E2 (reflection positivity), E4 (cluster),
local commutativity, and rotation det=-1 (PCT) remain as sorrys.

### E→R Analytic Continuation Axioms

- `inductive_analytic_continuation` — converted from sorry to axiom with detailed
  Paley-Wiener docstring (OS II Theorem 4.1: one-variable half-plane extension)
- `bochner_tube_theorem` — added to SCV/TubeDistributions.lean (holomorphic on
  T(C) extends to T(conv C))
- `full_analytic_continuation` docstring updated with 3-step proof strategy:
  iterate Paley-Wiener + E1 rotation + Bochner tube theorem

### Bridge Theorem Proofs

- **`os_to_wightman_full` (E'→R')** — fully proved, sorry-free. Extracts fields
  from `boundary_values_tempered` dependent tuple to satisfy `IsWickRotationPair`.
- **`wightman_to_os_full` (R→E)** — proved modulo a single geometric sorry
  (`h_in_tube`: showing x+iεη ∈ ForwardTube when η_k ∈ V₊). Uses
  `Filter.Tendsto.congr'` to equate BHW extension with spectrum_condition witness.

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

**`TubeDistributions.lean`** — axioms (200 lines), encoding results from
Vladimirov (2002) §25-26:

1. `continuous_boundary_tube` — distributional BV ⟹ continuous boundary extension
2. `boundary_value_recovery` — continuous extension integrates to reproduce distributional BV
3. `distributional_uniqueness_tube` — same distributional BV ⟹ equal on tube (theorem, not axiom)
4. `polynomial_growth_tube` — tempered BV ⟹ polynomial growth estimates
5. `bochner_tube_theorem` — holomorphic on T(C) extends to T(conv C)

*Why axioms:* `continuous_boundary_tube` (#1) and `polynomial_growth_tube` (#4)
require the Fourier-Laplace representation of tube-domain holomorphic functions
(Vladimirov §25-26), which is not in Mathlib. `boundary_value_recovery` (#2) is
the second half of Vladimirov's theorem. `bochner_tube_theorem` (#5) is a
deep SCV result (convex hull extension). `distributional_uniqueness_tube` (#3) is
proved from #1, #2, edge-of-the-wedge, and the identity theorem (2 localized sorrys:
du Bois-Reymond lemma and cone scaling property).

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

## All Axioms (10 total)

### SCV/Distribution Theory Axioms (3)

| # | Axiom | File | Eliminable? |
|---|-------|------|-------------|
| 1 | `continuous_boundary_tube` | `SCV/TubeDistributions.lean` | Needs Paley-Wiener-Schwartz |
| 2 | `boundary_value_recovery` | `SCV/TubeDistributions.lean` | Needs Fourier-Laplace transforms |
| 3 | `polynomial_growth_tube` | `SCV/TubeDistributions.lean` | Needs Fourier-Laplace transforms |
| 4 | `bochner_tube_theorem` | `SCV/TubeDistributions.lean` | Deep SCV (Bochner 1938) |

`distributional_uniqueness_tube` was converted from axiom to theorem, proved from
`continuous_boundary_tube` + `boundary_value_recovery` + edge-of-the-wedge + identity
theorem (2 localized sorrys: du Bois-Reymond lemma and cone scaling property).

### Analytic Continuation Axioms (2)

| # | Axiom | File | Eliminable? |
|---|-------|------|-------------|
| 4 | `edge_of_the_wedge` | `AnalyticContinuation.lean` | ~300-600 LOC, see proof plan |
| 5 | `bargmann_hall_wightman` | `AnalyticContinuation.lean` | Needs complex Lie group theory |

### WickRotation Axioms (5)

| # | Axiom | Ref | Eliminable? |
|---|-------|-----|-------------|
| 6 | `forward_tube_bv_integrable` | Vladimirov §26 | Needs polynomial growth + Schwartz decay |
| 7 | `lorentz_covariant_distributional_bv` | Streater-Wightman §2.4 | Needs Schwartz COV + measure preservation |
| 8 | `euclidean_points_in_permutedTube` | Jost §IV.5 | Jost's theorem: Wick-rotated points ∈ PET |
| 9 | `bhw_translation_invariant` | S-W Thm 2.8 | ForwardTube coordinate convention gap |
| 10 | `inductive_analytic_continuation` | OS II Thm 4.1 | Paley-Wiener half-plane extension |

Axiom #4 has a concrete proof plan
(`docs/edge_of_the_wedge_proof_plan.md`). Axioms #1-3 and #5 depend on large
bodies of mathematics not in Mathlib. Axioms #6-10 are textbook results
whose proofs require distribution theory, Jost point arguments, or Fourier-Laplace
transforms not yet available in the formalization.

---

## WickRotation.lean Sorry Status

### R→E Direction (6 sorrys, 11 proven)

| Theorem | Status | Via |
|---------|--------|-----|
| `W_analytic_lorentz_on_tube` | **done** | `distributional_uniqueness_forwardTube` |
| `W_analytic_continuous_boundary` | **done** | `continuous_boundary_forwardTube` |
| `W_analytic_local_commutativity` | sorry | Needs continuous BV + test function density |
| `constructedSchwinger_tempered` (E0) | sorry | Needs polynomial_growth_tube |
| `constructedSchwinger_translation_invariant` (E1a) | **done** | `bhw_translation_invariant` axiom |
| `constructedSchwinger_rotation_invariant` (E1b) | **done** (det=1) | `integral_orthogonal_eq_self` |
| `F_ext_rotation_invariant` (det=-1) | sorry | Needs PCT theorem |
| `constructedSchwinger_reflection_positive` (E2) | sorry | Needs Borchers involution + Wick rotation |
| `constructedSchwinger_symmetric` (E3) | **done** | `integral_perm_eq_self` (sorry-free) |
| `W_analytic_cluster_integral` (E4) | sorry | Needs cluster decomposition + dominated convergence |
| `wightman_to_os_full` | **done** | modulo h_in_tube sorry (ForwardTube coord convention) |

### E→R Direction (8 sorrys)

| Theorem | Status | What's needed |
|---------|--------|---------------|
| `full_analytic_continuation` | sorry | Iterate inductive axiom + E1 + Bochner |
| `boundary_values_tempered` | sorry | Full analytic continuation + BV theory |
| `constructWightmanFunctions` (6 fields) | sorry | Depend on boundary_values_tempered |
| `os_to_wightman_full` | **done** | Sorry-free (extracts from boundary_values_tempered) |

---

## Full Sorry Census

**92 total** across 20 files.

| Count | File | Category |
|-------|------|----------|
| 14 | `WickRotation.lean` | 6 R→E + 8 E→R |
| 2 | `SCV/TubeDistributions.lean` | distributional_uniqueness_tube proof |
| 14 | `vNA/ModularAutomorphism.lean` | Connes cocycle |
| 11 | `vNA/MeasureTheory/CaratheodoryExtension.lean` | Measure theory |
| 11 | `vNA/KMS.lean` | KMS condition |
| 9 | `vNA/ModularTheory.lean` | Tomita-Takesaki |
| 5 | `NuclearSpaces/SchwartzNuclear.lean` | Nuclear spaces |
| 4 | `Reconstruction.lean` | Wiring layer |
| 3 | `vNA/Unbounded/StoneTheorem.lean` | Stone's theorem |
| 3 | `NuclearSpaces/BochnerMinlos.lean` | Bochner-Minlos |
| 16 | Everything else | Scattered (1-2 each) |

### What's closest to provable next

1. **`edge_of_the_wedge` axiom** — Eliminable via slice-based construction
   using existing `edge_of_the_wedge_slice` + `osgood_lemma`.
   See `docs/edge_of_the_wedge_proof_plan.md`.

2. **`hartogs_analyticity` sorry** (IdentityTheorem.lean) — ~200 LOC with Osgood lemma.

3. **E→R direction** — The 8 sorrys in WickRotation.lean require
   the full OS-II inductive analytic continuation machinery (iterate
   `inductive_analytic_continuation` axiom + E1 rotation + Bochner tube theorem).

---

## Sorry-Free Highlights

### Our work
- **`os_to_wightman_full`** — The E'→R' bridge theorem (sorry-free)
- `W_analytic_lorentz_on_tube` — Lorentz invariance on forward tube (4 helper lemmas)
- `ForwardTubeDistributions.lean` — Forward tube as tube domain (591 lines)
- `GaussianFieldBridge.lean` — Nuclear space bridge (149 lines, sorry-free)
- `constructedSchwinger_symmetric` (E3) — sorry-free
- `constructedSchwinger_translation_invariant` (E1a) — sorry-free
- `integral_orthogonal_eq_self` — Orthogonal COV (46 lines)
- `integral_perm_eq_self` — Permutation COV (6 lines)
- `restricted_preserves_forward_cone` — SO⁺(1,d) preserves V₊
- `restricted_preserves_forward_tube` — Lorentz preserves forward tube
- `W_analytic_lorentz_holomorphic` — Holomorphicity of Lorentz-transformed W_analytic
- `W_analytic_continuous_boundary`

### Xiyin's repo
- `SeparatelyAnalytic.lean` — Taylor series, separately analytic (906 lines)
- `Osgood.lean` — Osgood's lemma (627 lines)
- `Polydisc.lean` — Polydisc definitions (231 lines)
- `edge_of_the_wedge_slice` — 1D edge-of-the-wedge (150 lines)
- `edge_of_the_wedge_1d` — 1D EOW via Morera
