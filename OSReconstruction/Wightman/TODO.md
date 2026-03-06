# Wightman TODO: OS Reconstruction Priority Queue

Last updated: 2026-03-06 (rev 4)

This file tracks blockers on the active OS reconstruction path with current priority order.
Policy lock: no wrappers, no useless lemmas, no code bloat; close `sorry`s with substantial mathematical proofs.

## Live Sorry Census

Count convention: direct tactic holes only (`^\s*sorry\b`).

| Scope | Direct `sorry` lines |
|-------|----------------------:|
| `OSReconstruction/Wightman` | 34 |
| `OSReconstruction/SCV` | 11 |
| `OSReconstruction/ComplexLieGroups` | 2 |
| `OSReconstruction/vNA` | 40 |
| **Whole project** | **87** |

_Count cross-checked 2026-03-06 on tracked `.lean` files via `git ls-files | xargs rg '^\s*sorry\b'`._
_BHWTranslation.lean was incorrectly listed with 5 sorrys; actual count is 1._
_BHWExtension.lean: W_analytic_swap_distributional_agree and analytic_boundary_local_commutativity are NOW PROVED (0 sorrys)._
_GNSHilbertSpace.lean: covariance_preHilbert was proved; 1 sorry remains (vacuum_unique part 2, spectral theory)._

## Definition Audit (2026-03-05 rev 3)

### PaleyWiener.lean: CRITICAL BUG PARTIALLY FIXED

`HasOneSidedFourierSupport` was WRONG: defined distributional support (T(φ)=0 for supp φ ⊂ (-∞,0))
instead of FOURIER support (T(F[φ])=0 for supp φ ⊂ (-∞,0) — i.e., supp(T̂) ⊆ [0,∞)).

**Fixed 2026-03-05**: Definition now uses `SchwartzMap.fourierTransformCLM ℂ` correctly.
Requires new import: `Mathlib.Analysis.Distribution.SchwartzSpace.Fourier`.

`HasFourierSupportIn` (multi-d): Still uses distributional support due to type mismatch
(`Fin m → ℝ` uses sup norm, incompatible with inner product needed for `fourierTransformCLM`).
Correct fix requires migrating to `EuclideanSpace ℝ (Fin m)` — deferred.

`paley_wiener_one_step_simple`: Fixed 2026-03-06. The theorem now concludes
distributional boundary-value recovery of the function-induced tempered distribution,
not false pointwise boundary equality `F_ext|_ℝ = f`.

`paley_wiener_one_step`: Narrowed 2026-03-06 to the correct one-variable
slice-extension region. The previous statement overclaimed holomorphic extension
on the full set `{z | Im(z_r) > 0}` with no control on the other coordinates.

`SCV/FourierLaplaceCore.lean`: now sorry-free. The Schwartz family `ψ_z` and
the candidate Fourier-Laplace extension input have been formalized there, so the
remaining `paley_wiener_half_line` blocker is the paired holomorphicity/growth
argument plus boundary-value convergence, not the basic Schwartz construction.
`SCV/PaleyWiener.schwartz_functional_bound` is also now proved, so the abstract
continuity hypothesis for tempered distributions has already been converted into
finite Schwartz-seminorm control.
`SCV/FourierLaplaceCore.schwartzPsiZ_seminorm_horizontal_bound` is now proved,
so the horizontal-line polynomial growth of the test family `ψ_{x+iη}` is also
formalized before the final pairing step.
`SCV/PaleyWiener.schwartz_functional_horizontal_growth` is now proved, so the
growth part of the 1D Fourier-Laplace pairing has been reduced to the actual
candidate used in `paley_wiener_half_line`.
`SCV/FourierLaplaceCore.schwartzCLM_seminorm_horizontal_growth` is also now
proved, so the generic horizontal-growth estimate survives passage through any
continuous Schwartz-space endomorphism. This is the reusable estimate needed
for the Fourier transform and the linear symbol `ξ ↦ I ξ` in the holomorphicity
step.
`SCV/PaleyWiener.fourierLaplaceExt_derivCandidate_horizontal_growth` is now
proved as well, so the derivative-side horizontal growth for the candidate
Fourier-Laplace pairing is no longer part of the `paley_wiener_half_line`
blocker.
The 1D Paley-Wiener statement has also been repaired to the correct input type:
the active theorem now takes a bundled continuous complex-linear Schwartz
functional, matching the analytic continuation target, rather than a merely
real-linear map.

See `Proofideas/paley_wiener_definition_analysis.lean` for full analysis.

### isConnected_permutedExtendedTube_inter_translate (BHWTranslation.lean)

Gemini consultation (2026-03-05) warns this may be FALSE for general complex c, because
PET's "starburst" sector structure can fracture under large translations. The standard physics
approach (Streater-Wightman pg. 65) works in difference variables to avoid this.
Numerical tests for d=1, n=2 (9 test cases) confirm connectivity — but large n may differ.
Path B (identity theorem on connected component only) is an alternative if general connectivity fails.

### Root Blocker (Confirmed 2026-03-05)

ALL active sorrys (LaplaceSchwartz, PaleyWiener, BochnerTubeTheorem, OSToWightman,
SchwingerAxioms) ultimately require **Fourier-Laplace theory for tube domains** (Vladimirov §25-26),
which is NOT in Mathlib. No partial proof is available without this infrastructure.

### Boundary Continuity Warning (2026-03-06)

The current `SCV.fourierLaplace_continuousWithinAt` / `SCV.continuous_boundary_tube`
interface is too strong. Distributional boundary values alone do not force a
continuous pointwise boundary extension; `F(z)=1/z` on the upper half-plane is
the basic counterexample. This means several downstream uses that currently
quote boundary continuity are resting on a false placeholder interface and
will need redesign around weaker boundary-value statements.

## Root Blocker Layers

### 1) E -> R: `WickRotation/OSToWightman.lean` (12)

Analytic continuation infrastructure:
- `inductive_analytic_continuation`
- `schwinger_holomorphic_on_base_region`
- `extend_to_forward_tube_via_bochner`
- `full_analytic_continuation` (two remaining holes)

Boundary value existence:
- `forward_tube_bv_tempered`

Axiom transfer chain:
- `bv_translation_invariance_transfer`
- `bv_lorentz_covariance_transfer`
- `bv_local_commutativity_transfer`
- `bv_positive_definiteness_transfer`
- `bv_hermiticity_transfer`

Cluster transfer:
- `bvt_cluster`

### 2) R -> E Wick Rotation Plumbing (7 total, down from 13)

`ForwardTubeLorentz.lean` (1):
- `wickRotation_not_in_PET_null`

`BHWExtension.lean` (0): **COMPLETE** — both sorrys proved as of 2026-03-05.

`BHWTranslation.lean` (1):
- `isConnected_permutedExtendedTube_inter_translate`

`SchwingerAxioms.lean` (5):
- `polynomial_growth_forwardTube_full`
- `polynomial_growth_on_PET`
- `schwinger_os_term_eq_wightman_term`
- `bhw_pointwise_cluster_euclidean`
- `W_analytic_cluster_integral`

### 3) Shared SCV Infrastructure (11 total, load-bearing)

First correction needed:
- replace the false boundary-continuity interface in
  `LaplaceSchwartz.lean` / `TubeDistributions.lean`

`SCV/PaleyWiener.lean` (4):
- `paley_wiener_half_line`
- `paley_wiener_cone`
- `paley_wiener_converse`
- `paley_wiener_one_step`

`SCV/LaplaceSchwartz.lean` (5):
- `fourierLaplace_continuousWithinAt`
- `fourierLaplace_uniform_bound_near_boundary`
- `fourierLaplace_polynomial_growth`
- `polynomial_growth_of_continuous_bv`
- `fourierLaplace_boundary_continuous`

`SCV/BochnerTubeTheorem.lean` (2):
- `bochner_local_extension`
- `holomorphic_extension_from_local`

## Secondary Blockers (Not First Execution Lane)

1. `Wightman/Reconstruction/Main.lean`: `wightman_uniqueness`
2. `Wightman/Reconstruction/GNSHilbertSpace.lean`: `vacuum_unique` part 2 (spectral theory; covariance_preHilbert PROVED)
3. `Wightman/WightmanAxioms.lean`: 4 infrastructural sorrys
4. `Wightman/NuclearSpaces/*`: side development, not on shortest reconstruction path
5. `ComplexLieGroups` remaining blocker status: see
   `OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/BLOCKER_STATUS.md`

## Execution Order

1. SCV core (`LaplaceSchwartz` + `PaleyWiener` + `Bochner`) to unblock continuation machinery.
2. `OSToWightman` analytic continuation + BV existence.
3. `OSToWightman` axiom transfer and cluster chain.
4. Wick-rotation plumbing (`ForwardTubeLorentz` -> ~~`BHWExtension`~~ [complete] -> `BHWTranslation` -> `SchwingerAxioms`).
5. Final uniqueness and residual wiring.

## Commands

```bash
rg -n '^\s*sorry\b' OSReconstruction --glob '*.lean'
lake build OSReconstruction.SCV
lake build OSReconstruction.Wightman
```
