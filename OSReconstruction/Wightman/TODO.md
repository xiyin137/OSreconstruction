# Wightman TODO: OS Reconstruction Remaining Work

Last updated: 2026-05-10

This file tracks the current OS reconstruction blockers on the
`rtoereflectionpositivity` branch after syncing with `upstream/Anna`. It is
intentionally limited to live `sorry`s, active axioms,
and remaining project-level TODOs.

## Current Progress

Count convention: direct tactic holes only.

```bash
rg -n '^[[:space:]]*sorry([[:space:]]|$)' OSReconstruction --glob '*.lean'
```

| Scope | Direct `sorry` lines |
|-------|----------------------:|
| `OSReconstruction/Wightman` | 15 |
| `OSReconstruction/SCV` | 0 |
| `OSReconstruction/ComplexLieGroups` | 2 |
| `OSReconstruction/vNA` | 36 |
| **Whole project** | **53** |

Current axiom count in `OSReconstruction`: 12.

## Wightman Remaining `sorry`s

### E->R / OS-to-Wightman lane

`os_to_wightman` starts from corrected Osterwalder-Schrader data
(`OsterwalderSchraderAxioms`) plus the OS-II linear growth condition
(`OSLinearGrowthCondition`) and constructs a checked Wightman core package.

| Goal | Status | Completed | Remaining |
|------|--------|-----------|-----------|
| Analytic continuation / boundary values | Mostly complete | `OSToWightmanSemigroup.lean` gives the OS Hilbert semigroup, spectral/Laplace bridge, and one-variable holomorphic layer. `bvt_F`/`bvt_W` are built and `os_to_wightman_full` is wired. | 3 support `sorry`s in `OSToWightman.lean`, plus the `K2VI1/Frontier.lean` probe-side Euclidean reproduction `sorry`. SCV BV existence remains axiomatized. |
| Temperedness, normalization, covariance, Hermiticity | Complete in the checked core | `constructWightmanFunctionsCore` fills `tempered`, `normalized`, `translation_invariant`, `lorentz_covariant`, and `hermitian`; several proofs live in `OSToWightmanBoundaryValuesComparison.lean`, not in `Main.lean`. | No direct `sorry` isolated for these fields beyond the analytic/BV trust surfaces they use. |
| Spectrum condition | Complete in the checked core | `constructWightmanFunctionsCore.spectrum_condition` uses `bvt_F`, `bvt_F_holomorphic`, the global growth package, and `bvt_boundary_values`. | No separate direct Wightman `sorry`; remaining trust boundary is the analytic/BV and SCV/Fourier-support infrastructure. |
| Positive definiteness | Complete | `constructWightmanFunctionsCore.positive_definite` is supplied by `bvt_positive_definite`, with theorem-3 positivity closed through `bvt_W_positive` and `OSToWightmanPositivity.lean`. | No direct `sorry` for this goal. |
| Locality and cluster full upgrade | Partial | The core can be upgraded to full `WightmanFunctions` by `toWightmanFunctions` once locality and cluster are supplied. | 2 direct `sorry`s in `OSToWightmanBoundaryValues.lean`: `bvt_W_swap_pairing_of_spacelike` for theorem 2 locality and `bvt_F_clusterCanonicalEventually_translate` for theorem 4 cluster. |

### R->E / Wick-rotation back lane

`wightman_to_os` starts from Wightman functions and constructs Schwinger
functions on the Euclidean side, packaged on the honest zero-diagonal test
space. The full-Schwartz Euclidean surface is intentionally not claimed.

| Goal | Status | Completed | Remaining |
|------|--------|-----------|-----------|
| Analytic Wick rotation / Schwinger construction | Complete modulo BHW trust surfaces | `wightman_to_os_full` is proved and returns `constructZeroDiagonalSchwingerFunctions` plus `IsWickRotationPair`. `BHWTranslation.lean` proves the active translation-invariance route; `ForwardTubeLorentz.lean` is sorry-free. | The reduced-coordinate BHW bridge remains the axiom `reduced_bargmann_hall_wightman_of_input`; the two `ComplexLieGroups` permutation blockers are separate geometric trust surfaces. |
| Temperedness and linearity on zero-diagonal tests | Complete | `constructedSchwinger_tempered_zeroDiagonal` and `constructedZeroDiagonalSchwinger_linear` supply the exported `wightman_to_os_full` continuity/linearity fields. | No direct `sorry` for this goal under the current census. |
| Euclidean symmetry and reality | Complete modulo BHW/SCV trust surfaces | `wickRotatedBoundaryPairing_symmetric`, `bhw_euclidean_reality_ae`, and `wickRotatedBoundaryPairing_reality` are proved in `SchwingerAxioms.lean`; these proofs are not visible from `Main.lean`. | No direct `sorry` for this goal; dependencies include the existing BHW/SCV trust surfaces. |
| Reflection positivity | Complete modulo support packages | The Section 4.3 spectral/Laplace route is proved in `RToEReflectionPositivity.lean`, with exported compatibility wrappers in `RToESchwingerAxiomsCompatibility.lean`. | No direct `sorry` for this goal. |
| Cluster / large-distance factorization | Partial | `bhw_pointwise_cluster_forwardTube` is proved using `distributional_cluster_lifts_to_tube`; `wickRotatedBoundaryPairing_cluster` and the OPTR `schwinger_E4_cluster_OPTR_case` are routed through the Ruelle/AHR analytic cluster package. | 1 direct `sorry`: the dominator-integrability step in `W_analytic_cluster_integral_via_ruelle` (`RuelleClusterBound.lean:1076`); full arbitrary-zero-diagonal E4 still needs the OPTR-to-general bridge and SCV/Vladimirov axioms remain deferred. |

### Operator / GNS lane

`Reconstruction/Main.lean` has 1 direct `sorry`:
- `wightman_uniqueness`

This is not on the shortest analyticity path, but remains required for the full
operator reconstruction story.

### Nuclear-space side lane

`NuclearSpaces/NuclearSpace.lean` has 2 direct `sorry`s:
- `gauge_dominates_on_subspace_of_convex_nhd`
- `product_seminorm_dominated`

`NuclearSpaces/BochnerMinlos.lean` has 5 direct `sorry`s:
- `bochner_tightness_and_limit`
- `minlos_projective_consistency`
- `minlos_nuclearity_tightness`
- `eval_maps_generate_sigma_algebra`
- `eval_charfun_implies_fd_distributions`

These support the nuclear-space probability route. They are substantial
functional-analysis tasks and should not distract from the active OS
continuation chain unless that route becomes necessary.

## Cross-Module Remaining TODOs

### SCV

Direct `sorry`s: 0.

Remaining SCV work is axiom discharge, mainly:
- `bochner_tube_extension` in `SCV/BochnerTubeTheorem.lean`
- boundary-value existence and Fourier-support axioms in `SCV/TubeBoundaryValues.lean`,
  `SCV/TubeBoundaryValueExistence.lean`, `SCV/FourierSupportCone.lean`, and
  `SCV/VladimirovTillmann.lean`

These are pure SCV / distribution theory trust boundaries used by the
boundary-value transfer route.

### ComplexLieGroups

Direct `sorry`s: 2, both in
`Connectedness/BHWPermutation/PermutationFlowBlocker.lean`:
- `blocker_isConnected_permSeedSet_nontrivial`
- `blocker_iterated_eow_hExtPerm_d1_nontrivial`

The production permutation-flow file is sorry-free; the remaining work is the
isolated `d = 1` geometric/permutation bridge.

### vNA

Direct `sorry`s: 36.

Relevant to OS reconstruction:
- `Unbounded/StoneTheorem.lean`: 1, `timeEvolution_generator`
- `Predual.lean`: 2, sigma-weak/predual infrastructure
- `MeasureTheory/CaratheodoryExtension.lean`: 11, measure-extension
  infrastructure

Future or currently non-consuming infrastructure:
- `ModularTheory.lean`: 6
- `ModularAutomorphism.lean`: 6
- `KMS.lean`: 10

The modular chain is not currently consumed by the reconstruction files.

### General / Wightman axioms

Active axioms outside SCV include:
- `GeneralResults/SNAGTheorem.lean`: `snag_theorem`
- `GeneralResults/SchwartzFubini.lean`: `schwartz_clm_fubini_exchange`
- `Wightman/WightmanAxioms.lean`: `schwartz_nuclear_extension`,
  `exists_continuousMultilinear_ofSeparatelyContinuous`
- `Wightman/Reconstruction/WickRotation/BHWReducedExtension.lean`:
  `reduced_bargmann_hall_wightman_of_input`

## Execution Order

1. Close the three `OSToWightman.lean` blockers, starting with
   `schwinger_continuation_base_step`.
2. Close the `K2VI1/Frontier.lean` probe-side Euclidean reproduction support
   blocker for the E->R `k = 2` route.
3. Finish the two `OSToWightmanBoundaryValues.lean` blockers: locality and
   cluster transfer.
4. Discharge the R->E cluster frontier in `RuelleClusterBound.lean`.
5. Resolve the two `ComplexLieGroups` permutation blockers for the remaining
   `d = 1` branch.
6. Defer Stone/GNS/nuclear-space/vNA modular work unless it directly blocks the
   active analyticity route.

## Verification Commands

```bash
rg -n '^[[:space:]]*sorry([[:space:]]|$)' OSReconstruction --glob '*.lean'
rg -n '^axiom ' OSReconstruction --glob '*.lean'
lake build OSReconstruction.Wightman
```
