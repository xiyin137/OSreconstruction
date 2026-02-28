# SCV TODO: OS-Critical Analytic Continuation Chain

Last updated: 2026-02-27

This TODO tracks the remaining `SCV` blockers on the OS reconstruction path.

Count convention in this file: direct tactic holes only, i.e.
`rg -n --glob '*.lean' '^\s*sorry\b' OSReconstruction/SCV`.

## Live Sorry Census

| Scope | Direct `sorry` lines |
|---|---:|
| `OSReconstruction/SCV` | 14 |

Breakdown:
- `SCV/LaplaceSchwartz.lean`: 6
- `SCV/PaleyWiener.lean`: 6
- `SCV/BochnerTubeTheorem.lean`: 2

## Load-Bearing Items (Priority)

1. `fourierLaplace_continuousWithinAt` (`LaplaceSchwartz.lean`)
2. `paley_wiener_half_line` (`PaleyWiener.lean`)
3. `bochner_local_extension` (`BochnerTubeTheorem.lean`)

These three are the main leverage points for unblocking downstream `Wightman/Reconstruction/WickRotation` sorry chains.

## Declaration-Level Blocker List

### `SCV/LaplaceSchwartz.lean` (6)

- `fourierLaplace_continuousWithinAt`
- `fourierLaplace_uniform_bound_near_boundary`
- `fourierLaplace_polynomial_growth`
- `polynomial_growth_of_continuous_bv`
- `fourierLaplace_boundary_continuous`
- `fourierLaplace_boundary_integral_convergence`

### `SCV/PaleyWiener.lean` (6)

- `paley_wiener_half_line`
- `paley_wiener_cone`
- `paley_wiener_converse`
- `paley_wiener_one_step`
- `paley_wiener_one_step_simple`
- `paley_wiener_unique`

### `SCV/BochnerTubeTheorem.lean` (2)

- `bochner_local_extension`
- `holomorphic_extension_from_local` (local consistency/gluing branch)

## Execution Order

1. Prove `LaplaceSchwartz.fourierLaplace_continuousWithinAt`.
2. Prove `PaleyWiener.paley_wiener_half_line`.
3. Propagate dependent chains in `LaplaceSchwartz` and `PaleyWiener`.
4. Prove `BochnerTubeTheorem.bochner_local_extension`.
5. Close `BochnerTubeTheorem.holomorphic_extension_from_local`.

## Stable Completed Core (No Sorrys)

- `Polydisc.lean`
- `IteratedCauchyIntegral.lean`
- `Osgood.lean`
- `Analyticity.lean`
- `TubeDomainExtension.lean`
- `IdentityTheorem.lean`

`edge_of_the_wedge_theorem` is proved and axiom-free.
