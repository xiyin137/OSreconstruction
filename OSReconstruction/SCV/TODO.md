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
- `LaplaceSchwartz.lean` now has the correct weak/regular split:
  - `HasFourierLaplaceRepr`
  - `HasFourierLaplaceReprRegular`
- `TubeDistributions.lean` now keeps only the proved regular variants; the unused weak
  placeholder fronts were removed.
- The unproved weak-to-regular upgrade theorem was removed.
  Rationale: the singularity-free bound `‖F(x+iεη)‖ ≤ C(1+‖x‖)^N` is not
  derivable from `poly_growth` alone (Phragmén-Lindelöf only gives
  `C(1+‖x‖)^N/ε^k`), and the remaining Vladimirov §26.2 continuity upgrade
  should not be hidden behind a fake interface.

## Load-Bearing Items

### `SCV/LaplaceSchwartz.lean` (0)

Meaning:
- the weak/regular split is now honest
- no fake upgrade theorem from weak BV data remains

### `SCV/TubeDistributions.lean` (0)

Meaning:
- only the rigorous regular variants remain
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

1. Use the explicit regular package directly in downstream flattened-tube transport.
2. Return to the real missing theorem: construct `HasFourierLaplaceReprRegular`
   from actual Fourier-Laplace input with the right dual-cone support.
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
