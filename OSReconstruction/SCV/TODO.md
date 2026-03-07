# SCV TODO: OS-Critical Analytic Continuation Chain

Last updated: 2026-03-07

This TODO tracks the remaining `SCV` blockers on the OS reconstruction path.

Count convention in this file: direct tactic holes only,
`rg -n '^[[:space:]]*sorry([[:space:]]|$)' OSReconstruction/SCV --glob '*.lean'`.

## Live Sorry Census

| Scope | Direct `sorry` lines |
|---|---:|
| `OSReconstruction/SCV` | 4 |

Breakdown:
- `SCV/LaplaceSchwartz.lean`: 2
- `SCV/TubeDistributions.lean`: 0
- `SCV/BochnerTubeTheorem.lean`: 2
- `SCV/PaleyWiener.lean`: 0

## Session Summary

- The fake multidimensional support scaffolding was removed from `PaleyWiener.lean`.
- `LaplaceSchwartz.lean` now has the correct weak/regular split together with
  an explicit strong-input upgrade theorem:
  - `HasFourierLaplaceRepr`
  - `HasFourierLaplaceReprRegular`
- `TubeDistributions.lean` now keeps only the proved strong variants; the unused weak
  placeholder fronts were removed.
- `HasFourierLaplaceReprRegular.ofStrong` now takes explicit strong input data:
  weak BV package + polynomial growth + singularity-free boundary-ray bound.
  Rationale: the singularity-free bound `‖F(x+iεη)‖ ≤ C(1+‖x‖)^N` is not
  derivable from `poly_growth` alone (Phragmén-Lindelöf only gives
  `C(1+‖x‖)^N/ε^k`); it must be supplied by the actual FL-transform input.

## Load-Bearing Items

### `SCV/LaplaceSchwartz.lean` (2)

Remaining blockers:
- `boundary_continuous` in `HasFourierLaplaceReprRegular.ofStrong`
- `tube_continuousWithinAt` in `HasFourierLaplaceReprRegular.ofStrong`

Meaning:
- `uniform_bound` is now an explicit input hypothesis of `ofStrong`
- the remaining 2 sorrys are the Arzelà-Ascoli / DCT boundary convergence arguments
- the weak/regular split is now honest
- no fake constructor from weak BV data remains

### `SCV/TubeDistributions.lean` (0)

Meaning:
- only the rigorous strong variants remain
- the unused weak placeholder fronts were removed instead of being carried as public `sorry`s

### `SCV/BochnerTubeTheorem.lean` (2)

Remaining blockers:
- `bochner_local_extension`
- `bochner_tube_extension`

Meaning:
- the old generic gluing theorem was too strong and has been removed
- current work should build on the compatible-family gluing theorem instead

### `SCV/PaleyWiener.lean` (0)

Status:
- sorry-free
- `paley_wiener_half_line` and the slice-wise `paley_wiener_one_step` are proved
- no fake multidimensional Fourier-support notion remains in the public API

## Execution Order

1. Finish `HasFourierLaplaceReprRegular.ofStrong` in `LaplaceSchwartz.lean`.
2. Use that strong regularity package directly in downstream flattened-tube transport.
3. Return to `BochnerTubeTheorem.lean`.

## Stable Completed Core

- `Polydisc.lean`
- `IteratedCauchyIntegral.lean`
- `Osgood.lean`
- `Analyticity.lean`
- `TubeDomainExtension.lean`
- `IdentityTheorem.lean`
- `FourierLaplaceCore.lean`
- `PaleyWiener.lean`

`edge_of_the_wedge_theorem` is proved and axiom-free.
