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
- `SCV/LaplaceSchwartz.lean`: 5
- `SCV/PaleyWiener.lean`: 4
- `SCV/BochnerTubeTheorem.lean`: 2

## Load-Bearing Items (Priority)

1. Fix the false boundary-continuity interface
   Current `fourierLaplace_continuousWithinAt` / `continuous_boundary_tube`
   is too strong: `F(z)=1/z` on the upper half-plane has tempered
   distributional boundary values but no continuous extension at `0`.
2. `paley_wiener_half_line` (`PaleyWiener.lean`)
3. `bochner_local_extension` (`BochnerTubeTheorem.lean`)

The first item is a statement-correction task, not a proof task. The other two
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

### `SCV/PaleyWiener.lean` (4)

- `paley_wiener_half_line`
- `paley_wiener_cone`
- `paley_wiener_converse`
- `paley_wiener_one_step`

Status note:
- `FourierLaplaceCore.lean` is now sorry-free and formalizes the Schwartz family
  `ψ_z` together with the candidate Fourier-Laplace pairing input.
- `schwartz_functional_bound` is now proved: a continuous Schwartz functional is
  dominated by finitely many Schwartz seminorms.
- `schwartzPsiZ_seminorm_horizontal_bound` is now proved: the Schwartz seminorms
  of `ψ_{x+iη}` grow polynomially along each fixed horizontal line.
- `schwartz_functional_horizontal_growth` is now proved: combining the previous
  two items yields polynomial growth of `x ↦ T(ψ_{x+iη})` for every continuous
  Schwartz functional `T`.
- `FourierLaplaceCore.schwartzCLM_seminorm_horizontal_growth` is now proved:
  any continuous linear endomorphism of Schwartz space preserves polynomial
  horizontal-line seminorm bounds on the family `ψ_{x+iη}`. This removes the
  generic growth estimate needed for both the Fourier transform and the linear
  symbol multiplication `ξ ↦ I ξ`.
- `PaleyWiener.fourierLaplaceExt_derivCandidate_horizontal_growth` is now
  proved: the candidate derivative pairing `x ↦ T(ℱ[(I ξ) ψ_{x+iη}])` also
  has polynomial horizontal-line growth.
- The 1D Paley-Wiener lane has been corrected to the right class of inputs:
  `paley_wiener_half_line` and the associated Fourier-Laplace extension now use
  bundled continuous complex-linear functionals on `𝓢(ℝ, ℂ)`, not merely
  real-linear maps.
- The remaining honest content in `paley_wiener_half_line` is no longer the
  Schwartz decay construction or the abstract continuity-to-seminorm bound; it
  is the holomorphicity of the paired extension and the boundary-value convergence.
- `paley_wiener_one_step_simple` was proved on 2026-03-06.
- `paley_wiener_one_step` was narrowed on 2026-03-06 to the correct one-variable
  slice-extension region; it no longer overclaims extension on the full
  `{ z | Im(z_r) > 0 }` slab.

### `SCV/BochnerTubeTheorem.lean` (2)

- `bochner_local_extension`
- `holomorphic_extension_from_local` (local consistency/gluing branch)

## Execution Order

1. Correct `LaplaceSchwartz.fourierLaplace_continuousWithinAt` and the dependent
   boundary-continuity wrappers in `TubeDistributions.lean`.
2. Prove `PaleyWiener.paley_wiener_half_line`.
3. Propagate the corrected Paley-Wiener/Laplace interfaces through the
   downstream reconstruction chain.
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
