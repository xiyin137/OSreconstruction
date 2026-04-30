# Wightman TODO: OS Reconstruction Priority Queue

Last updated: 2026-03-16

This file tracks the active blocker picture on the OS reconstruction path.
Policy lock: no wrappers, no useless lemmas, no code bloat; close `sorry`s with substantial mathematical proofs.

## Live Sorry Census

Count convention: direct tactic holes only (`^[[:space:]]*sorry([[:space:]]|$)`).

| Scope | Direct `sorry` lines |
|-------|----------------------:|
| `OSReconstruction/Wightman` | 33 |
| `OSReconstruction/SCV` | 2 |
| `OSReconstruction/ComplexLieGroups` | 2 |
| `OSReconstruction/vNA` | 40 |
| **Whole project** | **77** |

Count cross-checked on 2026-03-16 with:
```bash
rg -c '^[[:space:]]*sorry([[:space:]]|$)' OSReconstruction --glob '*.lean'
```

Tracked production tree also currently contains one explicit Route 1 axiom:
`reduced_bargmann_hall_wightman_of_input` in
`Wightman/Reconstruction/WickRotation/BHWReducedExtension.lean`.

## Current Root Blockers

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

Current blocker sharpening (2026-04-29):
- `W_analytic_cluster_integral` and `bhw_pointwise_cluster_forwardTube` are now blocked
  on a single live geometric refinement: the **identity-permutation ForwardTube
  refinement** — lifting the a.e. TranslatedPET triple to identity-permutation
  ForwardTube triples that `bhw_pointwise_cluster_forwardTube` consumes.
- Mechanical scaffolding now present (PR #72): `integral_fin_append_split` (Fubini
  over `Fin.append`), `ae_joint_triple_translatedPET` (a.e. block + joint TranslatedPET),
  `bhw_euclidean_kernel_perm_invariant_ae` (a.e. permutation invariance of the kernel).
- Two viable routes: (i) a block-respecting joint sorting argument that preserves the
  tensor-product test function structure — joint-sorting generally interleaves the
  (n, m) blocks and breaks `f ⊗ g_a`; or (ii) a TranslatedPET version of
  `bhw_pointwise_cluster_forwardTube` itself (i.e., lifting the SCV cluster axiom's
  ForwardTube hypothesis to TranslatedPET). Both are research-boundary work.

`WickRotation/ForwardTubeLorentz.lean` (0) — COMPLETE
- `wickRotation_not_in_PET_null` retired by the TranslatedPET migration: extension `F` is realized on TranslatedPET rather than the old ForwardTube k=0 surface (which broke translation invariance). The W11 false-statement counterexample is preserved in `W11Counterexample.lean` for the record.
- `polynomial_growth_on_slice` discharged.
- PR #72 additions (0 sorrys): `ae_joint_triple_translatedPET` — simultaneous a.e. TranslatedPET admissibility on the product space.

`WickRotation/BHWTranslation.lean` (0) — COMPLETE
- `isPreconnected_baseFiber` deleted as retired old-route surface (PR #72). It was unreachable from any live R→E lane after the merged path migrated to using `bhw_translation_invariant` directly. The geometric content (PET fiber connectivity via DOH or Lie-group fiber bundle theory) is no longer load-bearing and has been removed from the active TODO.

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
   - `SchwingerAxioms.lean`: Euclidean reality / reflection, OS=W term, cluster (live: identity-permutation ForwardTube refinement; see sharpening above)
6. Defer `StoneTheorem` / GNS operator-theoretic work until the analyticity lane is materially settled.

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
