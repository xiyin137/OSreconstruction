# Wightman TODO: OS Reconstruction Priority Queue

Last updated: 2026-04-27

This file tracks the active blocker picture on the OS reconstruction path.
Policy lock: no wrappers, no useless lemmas, no code bloat; close `sorry`s with substantial mathematical proofs.

## Live Sorry Census

Count convention: direct tactic holes only (`^[[:space:]]*sorry([[:space:]]|$)`).

| Scope | Direct `sorry` lines |
|-------|----------------------:|
| `OSReconstruction/Wightman` | 19 |
| `OSReconstruction/SCV` | 0 |
| `OSReconstruction/ComplexLieGroups` | 2 |
| `OSReconstruction/vNA` | 36 |
| **Whole project** | **58** |

Count cross-checked on 2026-04-27 with:
```bash
rg -c '^[[:space:]]*sorry([[:space:]]|$)' OSReconstruction --glob '*.lean'
```

Tracked production tree also currently contains one explicit Route 1 axiom:
`reduced_bargmann_hall_wightman_of_input` in
`Wightman/Reconstruction/WickRotation/BHWReducedExtension.lean`.

## Current Root Blockers

### `Wightman/SpectralEquivalence.lean` (0) — COMPLETE ON THE ONE-WAY LANE

Status:
- `SpectralEquivalence.lean` is now direct-`sorry`-free.
- The one-way theorem
  `ForwardTubeAnalyticity d W → SpectralConditionDistribution d W`
  is proved on the live branch.
- The old two-way surface has been dropped intentionally; the reverse direction
  under the global polynomial-growth interface is not part of the active file.

What landed:
- difference-variable factorization through `exists_diffVar_distribution`
- analytic diagonal-translation invariance on the forward tube
- product-tube extraction from forward-tube analyticity
- converse Paley-Wiener support argument on the product forward cone

Current role:
- no longer a live blocker for the Wightman lane
- keep follow-up work, if any, limited to cleanup or future reverse-direction
  redesign, not to the active OS reconstruction path

## Priority Split In `Main.lean`

There are two different lanes and they should not be conflated:

1. Analyticity / Wick-rotation lane:
   - `wightman_to_os`
   - `os_to_wightman`
   - critical files: `WickRotation/OSToWightmanSemigroup.lean`, `WickRotation/OSToWightman.lean`, `WickRotation/OSToWightmanBoundaryValues.lean`
   - shared dependencies: `SCV/*`, `BHWExtension`, `BHWTranslation`, `ForwardTubeLorentz`, `SchwingerAxioms`

2. Operator / GNS lane:
   - `wightman_reconstruction`
   - `wightman_uniqueness`
   - critical files: `Reconstruction/GNSHilbertSpace.lean`, `Reconstruction/Main.lean`, `vNA/Unbounded/StoneTheorem.lean`

Policy:
- while the active target is OS analyticity, do not drift into Stone/self-adjoint-generator work unless it directly unblocks the split `OSToWightman*` lane
- `StoneTheorem` is not needed for the analyticity chain
- Stone is needed later for the reconstructed `spectrum_condition` / `vacuum_unique` operator-theoretic branches

### 1. `WickRotation/OSToWightman*` split lane (8)

Active upstream blockers:
- `OSToWightman.lean` (1):
  - `schwinger_continuation_base_step`
- `OSToWightmanBoundaryValues.lean` (7):
  - `boundary_values_tempered`
  - `bv_translation_invariance_transfer`
  - `bv_lorentz_covariance_transfer`
  - `bv_local_commutativity_transfer`
  - `bv_positive_definiteness_transfer`
  - `bv_hermiticity_transfer`
  - `bvt_cluster`

Current status:
- the fake intermediate Bochner path is off the active chain
- the active continuation chain goes through the honest OS quotient/Hilbert semigroup already built in `OSToWightmanSemigroup.lean`
- `OSLinearGrowthCondition` is already used upstream to prove polynomial growth of time-shift matrix elements and hence contraction of the Euclidean semigroup
- the positive-time spectral-power continuity input is now landed in `vNA/Bochner/SemigroupRoots.lean`
- `Wightman/SchwartzTensorProduct.lean` now contains genuine insertion operators (`productTensorUpdateCLM`, `prependFieldCLMLeft/Right`) for the Schwartz kernel-extension lane
- the real remaining work is still:
  - `schwinger_continuation_base_step` in `OSToWightman.lean`
  - `boundary_values_tempered` in `OSToWightmanBoundaryValues.lean`
  - the six transfer theorems in `OSToWightmanBoundaryValues.lean`
  - `bvt_cluster` in `OSToWightmanBoundaryValues.lean`

Immediate sharpened subgaps:
- For `schwinger_continuation_base_step`: the next active target is the original 2-point Schwinger case, i.e. one difference variable after translation reduction. This must be stated on the honest Schwinger-side domain (`ZeroDiagonalSchwartz d 2` or an explicitly admissible Euclidean subspace promoted into it), not on ambient full Schwartz space.
- For `schwinger_continuation_base_step`: no more active effort on the original 1-point case; it is mathematically trivial from translation invariance and not a blocker.
- For `schwinger_continuation_base_step`: the honest remaining choice is between a concrete Schwinger-side two-point/difference-variable reduction and, only if forced later, a deeper Schwartz kernel-extension theorem. The tensor insertion maps do not close the blocker by themselves.
- For `boundary_values_tempered`: the generic DCT/integrability/tempered-boundary package is now in `SCV/LaplaceSchwartz.lean`; the genuine missing content is deriving the two growth hypotheses `hpoly` and `hunif` from the OS input.

Non-blocker but now complete:
- `Wightman/SpectralEquivalence.lean` has exited the live blocker set; do not
  spend active effort re-opening the old two-way theorem surface while the
  `OSToWightman*` lane is still incomplete.

### 2. `SCV` load-bearing infrastructure (2)

`SCV/PaleyWiener.lean`:
- sorry-free
- no fake multidimensional Fourier-support interface remains
- only the 1D and slice-wise theorems are active

`SCV/LaplaceSchwartz.lean` (0):

Status:
- the interface split is now honest:
  - weak `HasFourierLaplaceRepr`
  - regular `HasFourierLaplaceReprRegular`
- the fake weak-to-regular upgrade theorem has been removed
- the generic boundary-distribution lemmas needed by `boundary_values_tempered`
  are now extracted:
  - `integrable_poly_weight_schwartz`
  - `integrable_poly_growth_schwartz`
  - `tendsto_boundary_integral`
  - `boundary_distribution_bound`
- the real missing theorem is now explicit: construct the growth inputs and/or
  regular package from actual Fourier-Laplace input with the right dual-cone support

`SCV/TubeDistributions.lean` (0):

Status:
- the weak bare-BV theorem fronts were removed instead of being carried as public placeholders
- only the rigorous regular variants remain, built from explicit regular input data

`SCV/BochnerTubeTheorem.lean` (2):
- `bochner_local_extension`
- `bochner_tube_extension`

Status:
- the old generic gluing theorem was too strong and has been replaced by the honest compatible-family theorem

### 3. `Reconstruction/ForwardTubeDistributions.lean` (0) — COMPLETE

**`distributional_uniqueness_forwardTube` — PROVED** (commit 5813d37).
Proof: flattening via `flattenCLEquiv` + `distributional_uniqueness_tube_of_zero_bv`.

All weak-BV sorrys eliminated. Only proved regular variants remain.

Infrastructure (sorry-free):
- `SCV/DistributionalUniqueness.lean`: `distributional_uniqueness_tube_of_zero_bv`,
  `exists_integral_clm_of_continuous` (truncation → CLM via Banach-Steinhaus),
  `eqOn_open_of_compactSupport_schwartz_integral_eq_of_continuousOn`
- `SCV/SchwartzComplete.lean`: `CompleteSpace`, `BarrelledSpace`, Banach-Steinhaus chain

### 4. Wick rotation downstream

`WickRotation/SchwingerTemperedness.lean` (2):
- `wick_rotated_kernel_mul_zeroDiagonal_integrable`
- `constructedSchwinger_tempered_zeroDiagonal`

`WickRotation/SchwingerAxioms.lean` (4):
- `schwinger_os_term_eq_wightman_term`
- `bhw_euclidean_reality_ae`
- `bhw_pointwise_cluster_forwardTube`
- `W_analytic_cluster_integral`

Current blocker sharpening (2026-03-10):
- `bhw_euclidean_reality_ae` is now reduced to the honest overlap problem on
  `D = {z ∈ PET | hermitianReverse z ∈ PET}`.
- Infrastructure now present in `SchwingerAxioms.lean`:
  `hermitianReverseOverlap`, `differentiableOn_hermitianReverse_partner`,
  `ae_euclidean_points_in_hermitianReverseOverlap`.
- What still needs to be proved is the Schwarz-reflection identity `F = conj(F ∘ hermitianReverse)`
  on that overlap, extracted from the real Jost-support boundary theorem
  `wightman_real_on_jost_support`.

`WickRotation/ForwardTubeLorentz.lean` (2):
- `polynomial_growth_on_slice`
- `wickRotation_not_in_PET_null`

`WickRotation/BHWTranslation.lean` (1):
- `isPreconnected_baseFiber` (base-variable fiber connectivity in PET)
  - STATUS ON MERGED PATH: no longer needed to prove `bhw_translation_invariant`
  - CURRENT ROLE: old-route residual theorem, kept as a separate geometric target
  - ROOT CAUSE: our ForwardTube k=0 condition `Im(z₀) ∈ V⁺` breaks translation invariance
  - MATHEMATICAL PROOF: PET is a domain of holomorphy (BEG 1967). baseFiber = PET ∩ (complex affine subspace). Intersection of DOH with complex affine subspace is connected (standard SCV).
  - Alternative proof: fiber bundle over contractible base (tailDiffPermSector is convex) with connected fiber (stabilizer in SO(d+1;ℂ) is connected). See Proofideas/baseFiber_inflation_proof.lean.
  - PROVED helpers (0 sorrys): inOpenForwardCone_add_time, forwardTube_add_broadcast_iTime, complexLorentzAction_add_broadcast, lorentz_action_inflation_dir (in test/proofideas_baseFiber_inflation.lean)
  - Production reduction: baseFiber_isPreconnected_of_index_and_active_geometry reduces to index set connectivity + sector overlap
  - FORMALIZATION GAP: needs SCV domain-of-holomorphy infrastructure OR Lie group fiber bundle theory, neither in Mathlib

`WickRotation/BHWReducedExtension.lean` (axiom 1):
- `reduced_bargmann_hall_wightman_of_input`
  - accepted as a strategically deferred reduced-coordinate BHW bridge
  - this is the Route 1 replacement for the old base-fiber route on the merged path
  - intended future discharge: descend the absolute BHW theorem through
    translation invariance / quotient geometry
  - see `docs/reduced_bhw_bridge_and_numerics.md`

`WickRotation/BHWExtension.lean` (0):
- Honest extendF-level adjacent-swap theorems are complete.
- If raw real-edge values are ever needed again, the remaining mathematical input is
  boundary continuity of the spectrum witness on the real ET edge, not more EOW/BHW infrastructure.

New proved theorems (2026-03-10):
- `W_analytic_swap_boundary_pairing_eq` — PROVED via distributional chain
- `analytic_extended_local_commutativity` — pointwise swap for `extendF` at real ET points
- `analytic_boundary_local_commutativity_of_boundary_continuous` — raw W_analytic with honest ContinuousWithinAt hypotheses

Current assessment:
- `R→E` has two independent hard roots:
  - coincidence-singularity / zero-diagonal integrability
  - Euclidean reality / reflection
- the `boundary_values_tempered` extraction work on the E→R side does not by itself close either of those; it mainly prepares the tempered Wightman boundary package after E→R continuation exists

## Secondary Blockers

Not on the shortest OS reconstruction lane:
- `Wightman/SpectralEquivalence.lean`: one-way implication complete; only future
  reverse-direction or interface-cleanup work remains
- `Wightman/Reconstruction/Main.lean`: `wightman_uniqueness`
- `Wightman/Reconstruction/GNSHilbertSpace.lean`: one remaining spectral-theory blocker
- `Wightman/WightmanAxioms.lean`: 4 infrastructural sorrys
- `Wightman/NuclearSpaces/*`: side development, not first execution lane
- `ComplexLieGroups` residual blockers: see the CLG status files

## Execution Order

1. Finish the live E→R root blocker `schwinger_continuation_base_step` in `OSToWightman.lean`.
   - keep the hard gap explicit
   - use the existing honest semigroup/spectral/Laplace infrastructure
   - do not add abstract wrappers that hide the remaining step
   - first close the nontrivial 2-point Schwinger reduction on `ZeroDiagonalSchwartz d 2` / an admissible Euclidean subspace
   - do not spend active effort on one-point classification or ambient full-Schwartz surrogate theorems
2. Use the extracted SCV boundary-distribution lemmas to reduce `boundary_values_tempered` in `OSToWightmanBoundaryValues.lean` to the genuine missing growth inputs `hpoly` and `hunif`.
3. Keep the new tensor insertion infrastructure in `Wightman/SchwartzTensorProduct.lean` in mind if the continuation blocker turns into a genuine Schwartz kernel-extension theorem, but do not confuse that groundwork with closure of the live blocker.
4. After `boundary_values_tempered`, finish the six transfer theorems and `bvt_cluster` in `OSToWightmanBoundaryValues.lean`.
5. In parallel or next, attack the live R→E front after the Route 1 merge:
   - `SchwingerTemperedness.lean`: coincidence-singularity / zero-diagonal continuity
   - `SchwingerAxioms.lean`: Euclidean reality / reflection, OS=W term, cluster
   - `BHWTranslation.isPreconnected_baseFiber` is now optional old-route cleanup, not required for the merged proof path
6. Keep `SpectralEquivalence.lean` off the active queue unless a downstream file
   needs a small interface adaptation; the one-way theorem is already landed.
7. Defer `StoneTheorem` / GNS operator-theoretic work until the analyticity lane is materially settled.

## Recently Completed (2026-03-14)

### Fiberwise antiderivative chain — COMPLETE (0 sorrys in test file)
- `contDiff_fiberwiseAntiderivRaw` — C^∞ smoothness
- `decay_fiberwiseAntiderivRaw` — Schwartz decay at all orders (induction on p)
- `fiberwiseAntideriv` — SchwartzMap packaging
- `lineDeriv_fiberwiseAntideriv` — head derivative recovers F
- Ready for production extraction to `SliceIntegral.lean` (~165 lines)

### Production extractions landed
- `PartialToTotal.lean` — partial → total HasFDerivAt (0 sorrys)
- `SchwartzCutoff.lean` — schwartz_tail_decay (0 sorrys)
- `BEGTrigonometric.lean` — sinusoidal_pos_of_endpoints_pos (0 sorrys)
- `SliceIntegral.lean` — iicZeroSlice chain + intervalPiece chain + fiberwiseAntiderivRaw (0 sorrys, 1990 lines total)
- `TwoPointDescent.lean` — integral identities + center-shear translation (0 sorrys)

## Commands

```bash
rg -n '^[[:space:]]*sorry([[:space:]]|$)' OSReconstruction --glob '*.lean'
lake build OSReconstruction.SCV
lake build OSReconstruction.Wightman
```
