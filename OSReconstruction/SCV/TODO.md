# SCV TODO: OS-Critical Analytic Continuation Chain

Last updated: 2026-03-06

This TODO tracks the remaining `SCV` blockers on the OS reconstruction path.

Count convention in this file: direct tactic holes only, i.e.
`rg -n --glob '*.lean' '^\s*sorry\b' OSReconstruction/SCV`.

## Live Sorry Census

| Scope | Direct `sorry` lines |
|---|---:|
| `OSReconstruction/SCV` | 11 |

Breakdown:
- `SCV/LaplaceSchwartz.lean`: 7
- `SCV/TubeDistributions.lean`: 2
- `SCV/BochnerTubeTheorem.lean`: 2

## Load-Bearing Items (Priority)

1. Fix the false boundary-continuity interface
   Current `fourierLaplace_continuousWithinAt` / `continuous_boundary_tube`
   is too strong: `F(z)=1/z` on the upper half-plane has tempered
   distributional boundary values but no continuous extension at `0`.
2. `bochner_local_extension` (`BochnerTubeTheorem.lean`)
3. `holomorphic_extension_from_local_family` usage / local-family geometry
4. keep `TubeDistributions.lean` aligned with the corrected `LaplaceSchwartz` interface

The first item is a statement-correction task, not a proof task. The remaining items
are the main honest proof leverage points for unblocking downstream
`Wightman/Reconstruction/WickRotation` sorry chains.

## Declaration-Level Blocker List

### `SCV/LaplaceSchwartz.lean` (5)

- `fourierLaplace_continuousWithinAt`
- `fourierLaplace_uniform_bound_near_boundary`
- `fourierLaplace_polynomial_growth`
- `polynomial_growth_of_continuous_bv`
- `fourierLaplace_boundary_continuous`

Status note:
- `fourierLaplace_continuousWithinAt` is currently believed false as stated.
  The replacement theorem should use stronger boundary regularity than bare
  tempered distributional boundary values.

### `SCV/PaleyWiener.lean` (0)

Status:
- `PaleyWiener.lean` is now sorry-free.
- `paley_wiener_half_line` is proved.
- `paley_wiener_one_step_simple` is proved.
- `paley_wiener_one_step` is now the honest slice-wise one-variable extension
  theorem actually used by downstream OS reconstruction work.
- `FourierLaplaceCore.lean` is sorry-free and remains the load-bearing kernel
  infrastructure for the 1D Fourier-Laplace argument.

Implication:
- `PaleyWiener` is no longer the SCV blocker.
- The active SCV blockers are now `LaplaceSchwartz`, `TubeDistributions`, and
  `BochnerTubeTheorem`.

### `SCV/BochnerTubeTheorem.lean` (2)

- `bochner_local_extension`
- `bochner_tube_extension`

Status note:
- the old generic gluing theorem was too strong and has been replaced by the
  honest compatible-family theorem `holomorphic_extension_from_local_family`
- current work should build on that corrected theorem, not on the removed
  stronger statement

## Execution Order

1. Correct `LaplaceSchwartz.fourierLaplace_continuousWithinAt` and the dependent
   boundary-continuity wrappers in `TubeDistributions.lean`.
2. Propagate the corrected Paley-Wiener / Laplace interfaces through the
   downstream reconstruction chain.
3. Prove `BochnerTubeTheorem.bochner_local_extension`.
4. Re-close `BochnerTubeTheorem.bochner_tube_extension` using the compatible-family theorem.

## Stable Completed Core (No Sorrys)

- `Polydisc.lean`
- `IteratedCauchyIntegral.lean`
- `Osgood.lean`
- `Analyticity.lean`
- `TubeDomainExtension.lean`
- `IdentityTheorem.lean`
- `FourierLaplaceCore.lean`
- `PaleyWiener.lean`

`edge_of_the_wedge_theorem` is proved and axiom-free.
