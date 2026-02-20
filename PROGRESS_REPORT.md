# Progress Report: Forward Tube Distribution Infrastructure

## What changed

Since the upstream merge (xiyin's edge-of-the-wedge update, commit `47a4076`),
four commits added the **forward tube distribution layer**: the bridge between
general several-complex-variables (SCV) tube domain theory and the specific
forward tube used in the Wightman-to-OS reconstruction.

**Files changed:** 8 files, +943/-131 lines of Lean 4.

Two new files were created:

- `SCV/TubeDistributions.lean` (173 lines) — general tube domain axioms
- `Wightman/Reconstruction/ForwardTubeDistributions.lean` (591 lines) — **sorry-free**

## Why this matters

Before this work, `WickRotation.lean` called `continuous_boundary_forwardTube`
and `distributional_uniqueness_forwardTube`, but these theorems did not exist.
The call sites were dead code — they type-checked only because the theorems
around them were `sorry`. Now:

1. Both theorems exist and are proved (modulo well-defined axioms).
2. `W_analytic_continuous_boundary` in WickRotation.lean has an actual proof:
   three lines applying `continuous_boundary_forwardTube` with arguments from
   `spectrum_condition`. This was previously a sorry.
3. The 20 remaining WickRotation sorrys are unchanged, but the infrastructure
   they depend on now compiles end-to-end.

The difference is between "sorry because the dependency doesn't exist yet" and
"sorry because the proof of this specific step is hard." The latter is much
closer to done.

## What was proved (sorry-free)

ForwardTubeDistributions.lean contains 29 definitions and theorems, all sorry-free:

### Forward cone properties
- **`ForwardConeAbs`** — definition of the product cone in difference coordinates
- **`forwardConeAbs_isOpen`** — the forward cone is open (preimage argument)
- **`convex_inOpenForwardCone`** — V+ is convex (Cauchy-Schwarz on spatial components)
- **`forwardConeAbs_convex`** — the product cone inherits convexity
- **`forwardConeAbs_nonempty`** — witness: y_k = (k+1) * e_0
- **`inOpenForwardCone_smul`** — V+ is closed under positive scaling
- **`inOpenForwardCone_add`** — V+ is closed under addition (via convexity + scaling)
- **`forwardConeAbs_implies_allForwardCone`** — if all differences lie in V+, each
  component lies in V+ (key bridge between approach direction conventions)

### Flattening equivalence
- **`flattenCLEquiv`** / **`flattenCLEquivReal`** — concrete isomorphism
  `(Fin n -> Fin d -> K) ≃L[K] (Fin (n*d) -> K)` via `Equiv.curry` + `finProdFinEquiv`
- **`flattenCLEquiv_apply`**, **`_symm_apply`**, **`_im`** — simp lemmas
- **`forwardTube_flatten_eq_tubeDomain`** — the forward tube IS a tube domain after flattening

### Main theorems
- **`continuous_boundary_forwardTube`** — holomorphic functions on the forward tube with
  distributional boundary values extend continuously to the real boundary
- **`distributional_uniqueness_forwardTube`** — two such functions with the same boundary
  values agree on the tube

Both are derived from the general tube domain axioms by:
1. Flattening coordinates via `flattenCLEquiv`
2. Transporting DifferentiableOn through the isomorphism
3. Bridging approach direction conventions (ForwardConeAbs vs component-wise V+)
4. Change of variables in the boundary value integrals
5. Pulling back ContinuousWithinAt through the homeomorphism

## Axioms

The project now has 6 axioms total. Four were added in this work:

### 1-3. Tube domain axioms (`SCV/TubeDistributions.lean`)

These encode theorems from Vladimirov, "Methods of the Theory of Generalized
Functions" (2002), sections 25-26.

**`continuous_boundary_tube`** — If F is holomorphic on a tube domain T(C) and
has tempered distributional boundary values (the smeared integrals
`integral F(x+i*eps*eta) f(x) dx` converge as eps -> 0+ for Schwartz test functions f
and approach directions eta in C), then F extends continuously to the real boundary.

**`distributional_uniqueness_tube`** — If two holomorphic functions on T(C) have
the same distributional boundary values, they agree on T(C).

**`polynomial_growth_tube`** — Holomorphic functions on T(C) with tempered boundary
values satisfy polynomial growth estimates: `|F(x+iy)| <= C * (1+||x||)^N` for
y in any compact subset of C.

*Why axioms:* The proofs require the Paley-Wiener-Schwartz theorem (characterizing
Fourier transforms of compactly supported distributions) and the theory of
Fourier-Laplace transforms of tempered distributions. Neither exists in Mathlib.
These are standard, well-referenced results at a clean API boundary.

### 4. Change of variables (`ForwardTubeDistributions.lean`)

**`integral_flatten_change_of_variables`** — For any function g,
`integral g(x) dx = integral g(flatten(y)) dy` where flatten is the coordinate
reindexing `(Fin n -> Fin d -> R) -> (Fin (n*d) -> R)`.

*Why axiom:* This composes two standard facts:
(a) Permuting coordinates preserves Lebesgue measure — this IS in Mathlib as
    `volume_measurePreserving_piCongrLeft`.
(b) Currying/uncurrying preserves the product measure (Fubini) — this is NOT
    yet in Mathlib (`measurePreserving_curry` is missing).

This axiom is eliminable with a single Mathlib PR adding measure preservation
for `MeasurableEquiv.curry`.

### 5-6. Pre-existing axioms (`AnalyticContinuation.lean`)

**`edge_of_the_wedge`** — Bogoliubov's edge-of-the-wedge theorem (multi-dimensional).
Note: the 1D slice version `edge_of_the_wedge_slice` IS proved (line 553), but the
full multi-dimensional `edge_of_the_wedge` (line 730) remains an axiom — it requires
reducing the general case to iterated 1D applications, which involves careful
induction on dimension.

**`bargmann_hall_wightman`** — The BHW theorem extending holomorphic functions
from the forward tube to the permuted extended tube via Lorentz group action.

These were already present before this work.

## Remaining sorrys

**137 total** across 25 files. The major concentrations:

| Count | File | What's needed |
|-------|------|---------------|
| 20 | `WickRotation.lean` | The main R-to-E and E-to-R bridge theorems |
| 16 | `vNA/CaratheodoryExtension.lean` | Measure-theoretic constructions |
| 15 | `vNA/ModularAutomorphism.lean` | Modular automorphism group (Tomita-Takesaki) |
| 14 | `SchwartzNuclear.lean` | Some superseded by gaussian-field library |
| 11 | `vNA/KMS.lean` | KMS condition and thermal equilibrium |
| 10 | `GaussianFieldBridge.lean` | Wiring gaussian-field to nuclear spaces |
| 10 | `vNA/Unbounded/Spectral.lean` | Spectral theory for unbounded operators |
| 9 | `vNA/ModularTheory.lean` | Modular operators (Tomita-Takesaki) |
| 22 | Everything else | Scattered across 17 files (1-4 each) |

### WickRotation sorrys in detail

The 20 sorrys in WickRotation.lean break down as:

**Wightman-to-OS direction (R -> E):**
- `W_analytic_lorentz_on_tube` — Lorentz invariance of analytic continuation
  (needs distributional_uniqueness_forwardTube, now available)
- `W_analytic_local_commutativity` — spacelike commutativity at boundary
- `constructedSchwinger_tempered` — Schwinger functions are tempered (needs polynomial_growth_tube)
- `constructedSchwinger_translation_invariant` — translation invariance of S_n
- `constructedSchwinger_reflection_positive` — OS reflection positivity
- `F_ext_translation_invariant` — translation invariance of BHW extension
- `F_ext_permutation_invariant` — permutation symmetry of BHW extension

**OS-to-Wightman direction (E -> R):**
- `wightman_to_os_full` / `os_to_wightman_full` — the main bridge theorems
- Several sorrys inside `constructWightmanFunctions` for the individual axioms:
  lorentz_invariance, spectrum_condition, positive_definite, locally_commutative

### What's closest to provable next

1. **`W_analytic_lorentz_on_tube`** — Both z -> W(z) and z -> W(Lambda*z) are
   holomorphic on the forward tube with the same boundary values (by Lorentz
   invariance of W_n). Now that `distributional_uniqueness_forwardTube` exists
   and is proved, this is a direct application.

2. **`constructedSchwinger_tempered`** — Needs `polynomial_growth_tube` (axiom 3),
   which we have. The proof is: apply the axiom, then show the Wick-rotated
   evaluation defines a tempered distribution.

3. **The COV axiom** — Eliminable by contributing `measurePreserving_curry` to Mathlib.
