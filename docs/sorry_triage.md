# Production Sorry Triage

Purpose: this note is the repo-wide triage sheet for every direct production
`sorry` currently present in `OSReconstruction/**/*.lean`.

Count convention:
- direct tactic holes only: `^[[:space:]]*sorry([[:space:]]|$)`
- checked on `2026-04-05`
- current live count: `60`

This note should be read together with:
- `docs/theorem2_locality_blueprint.md`
- `docs/theorem3_os_route_blueprint.md`
- `docs/theorem4_cluster_blueprint.md`
- `docs/r_to_e_blueprint.md`
- `docs/general_k_continuation_blueprint.md`
- `docs/gns_pipeline_blueprint.md`
- `docs/vna_triage.md`
- `docs/peripheral_sorry_triage.md`

## 1. Current census

| Subsystem | Direct `sorry`s |
|---|---:|
| `OSReconstruction/Wightman` | 20 |
| `OSReconstruction/SCV` | 2 |
| `OSReconstruction/ComplexLieGroups` | 2 |
| `OSReconstruction/vNA` | 36 |
| **Total** | **60** |

## 2. Highest-priority OS-route frontiers

These are the blockers closest to the current public reconstruction lane.

| ID | File:line | Theorem | Why it matters | Primary doc |
|---|---|---|---|---|
| W1 | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean:367` | `bvt_F_swapCanonical_pairing` | theorem 2 locality frontier | `docs/theorem2_locality_blueprint.md` |
| W2 | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean:386` | `bvt_W_positive` | theorem 3 positivity frontier | `docs/theorem3_os_route_blueprint.md` |
| W3 | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean:412` | `bvt_F_clusterCanonicalEventually_translate` | theorem 4 cluster frontier | `docs/theorem4_cluster_blueprint.md` |

Everything else in this document should be interpreted relative to those three
live public blockers.

## 3. Wightman-side direct `sorry`s (20)

### 3.1. `E -> R` continuation and boundary-value lane

| ID | File:line | Theorem | Lane | Status |
|---|---|---|---|---|
| W4 | `Wightman/Reconstruction/WickRotation/OSToWightman.lean:66` | `exists_acrOne_productTensor_witness` | base-step support package | active |
| W5 | `Wightman/Reconstruction/WickRotation/OSToWightman.lean:209` | `acrOne_productTensor_witness_euclidKernelPackage` | base-step support package | active |
| W6 | `Wightman/Reconstruction/WickRotation/OSToWightman.lean:376` | `compactlySupported_zeroDiagonal_subset_closure_admissibleProductTensorSet` | base-step closure/density package | active |
| W1 | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean:367` | `bvt_F_swapCanonical_pairing` | theorem 2 locality | active |
| W2 | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean:386` | `bvt_W_positive` | theorem 3 positivity | active |
| W3 | `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean:412` | `bvt_F_clusterCanonicalEventually_translate` | theorem 4 cluster | active |
| W7 | `Wightman/Reconstruction/WickRotation/K2VI1/Frontier.lean:133` | `hasCompactSupport_twoPointCenterShearDescent_reflected_local` | theorem-1 / K2 residual support theorem | medium |

### 3.2. `R -> E` / reverse-direction and historical side lanes

| ID | File:line | Theorem | Lane | Status |
|---|---|---|---|---|
| W8 | `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean:2366` | `schwingerExtension_os_term_eq_wightman_term` | false positivity route | quarantine/delete |
| W9 | `Wightman/Reconstruction/WickRotation/SchwingerAxioms.lean:3581` | `W_analytic_cluster_integral` | reverse-direction cluster | live but not on shortest path |
| W10 | `Wightman/Reconstruction/WickRotation/BHWTranslation.lean:1115` | `isPreconnected_baseFiber` | old-route PET connectivity | peripheral |
| W11 | `Wightman/Reconstruction/WickRotation/ForwardTubeLorentz.lean:1129` | `wickRotation_not_in_PET_null` | reverse-direction measure-zero geometry | peripheral |

### 3.3. GNS / uniqueness / functional-analysis side lane

| ID | File:line | Theorem | Lane | Status |
|---|---|---|---|---|
| W12 | `Wightman/Reconstruction/GNSHilbertSpace.lean:1258` | `gns_matrix_coefficient_holomorphic_axiom` | GNS spectrum condition bridge | high, but not on current `E -> R` path |
| W13 | `Wightman/Reconstruction/Main.lean:82` | `wightman_uniqueness` | standalone uniqueness theorem | medium |
| W14 | `Wightman/NuclearSpaces/NuclearSpace.lean:234` | `gauge_dominates_on_subspace_of_convex_nhd` | nuclear-space infrastructure | medium |
| W15 | `Wightman/NuclearSpaces/NuclearSpace.lean:313` | `product_seminorm_dominated` | nuclear-space infrastructure | medium |
| W16 | `Wightman/NuclearSpaces/BochnerMinlos.lean:285` | `bochner_tightness_and_limit` | Bochner finite-dimensional existence | medium-low |
| W17 | `Wightman/NuclearSpaces/BochnerMinlos.lean:384` | `minlos_projective_consistency` | Minlos projective family | medium-low |
| W18 | `Wightman/NuclearSpaces/BochnerMinlos.lean:399` | `minlos_nuclearity_tightness` | Minlos tightness | medium-low |
| W19 | `Wightman/NuclearSpaces/BochnerMinlos.lean:465` | `eval_maps_generate_sigma_algebra` | Minlos uniqueness | medium-low |
| W20 | `Wightman/NuclearSpaces/BochnerMinlos.lean:485` | `eval_charfun_implies_fd_distributions` | Minlos uniqueness | medium-low |

## 4. SCV direct `sorry`s (2)

| ID | File:line | Theorem | Role | Primary doc |
|---|---|---|---|---|
| S1 | `SCV/BochnerTubeTheorem.lean:126` | `bochner_local_extension` | local convex patch extension | `docs/scv_infrastructure_blueprint.md` |
| S2 | `SCV/BochnerTubeTheorem.lean:220` | `bochner_tube_extension` | global Bochner tube theorem | `docs/scv_infrastructure_blueprint.md` |

These are not the first blockers on the current theorem-2/3/4 route, but they
remain core SCV infrastructure for later general-`k` continuation.

## 5. Complex-Lie-group direct `sorry`s (2)

| ID | File:line | Theorem | Role | Primary doc |
|---|---|---|---|---|
| C1 | `ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlowBlocker.lean:55` | `blocker_isConnected_permSeedSet_nontrivial` | higher-dimensional permutation-flow connectedness | `docs/bhw_permutation_blueprint.md` |
| C2 | `ComplexLieGroups/Connectedness/BHWPermutation/PermutationFlowBlocker.lean:119` | `blocker_iterated_eow_hExtPerm_d1_nontrivial` | one-dimensional nontrivial branch | `docs/bhw_permutation_blueprint.md` |

These are honest mathematical blockers, but they are currently peripheral to
the theorem-2/3/4 OS-route work.

## 6. vNA direct `sorry`s (36)

The operator-algebra backlog is large enough that it now has its own dedicated
triage note: `docs/vna_triage.md`. The complete line-by-line census is still
listed here for global completeness.

### 6.1. Measure-theory base

| ID | File:line | Theorem | Status |
|---|---|---|---|
| V1 | `vNA/MeasureTheory/CaratheodoryExtension.lean:150` | `toOuterMeasure_Icc` | foundational |
| V2 | `vNA/MeasureTheory/CaratheodoryExtension.lean:162` | `borel_le_caratheodory` | foundational |
| V3 | `vNA/MeasureTheory/CaratheodoryExtension.lean:308` | `toIntervalPremeasure` | foundational |
| V4 | `vNA/MeasureTheory/CaratheodoryExtension.lean:312` | `toIntervalPremeasure` | foundational |
| V5 | `vNA/MeasureTheory/CaratheodoryExtension.lean:319` | `toIntervalPremeasure` | foundational |
| V6 | `vNA/MeasureTheory/CaratheodoryExtension.lean:373` | `toSpectralMeasure_Icc` | foundational |
| V7 | `vNA/MeasureTheory/CaratheodoryExtension.lean:380` | `toSpectralMeasure_sigma_additive` | foundational |
| V8 | `vNA/MeasureTheory/CaratheodoryExtension.lean:385` | `toSpectralMeasure_univ` | foundational |
| V9 | `vNA/MeasureTheory/CaratheodoryExtension.lean:407` | `spectralPremeasureFromLimit` | foundational |
| V10 | `vNA/MeasureTheory/CaratheodoryExtension.lean:410` | `spectralPremeasureFromLimit` | foundational |
| V11 | `vNA/MeasureTheory/CaratheodoryExtension.lean:415` | `spectralPremeasureFromLimit` | foundational |

### 6.2. Core modular theory

| ID | File:line | Theorem | Status |
|---|---|---|---|
| V12 | `vNA/ModularTheory.lean:232` | `conjugates_modular_operator` | downstream of Tomita package |
| V13 | `vNA/ModularTheory.lean:247` | `reverses_modular_flow` | downstream of Tomita package |
| V14 | `vNA/ModularTheory.lean:282` | `tomita_fundamental` | core theorem |
| V15 | `vNA/ModularTheory.lean:303` | `modular_automorphism_preserves` | downstream |
| V16 | `vNA/ModularTheory.lean:341` | `StandardForm.positiveCone_self_dual` | late-stage standard form |
| V17 | `vNA/ModularTheory.lean:361` | `standard_form_unique` | late-stage standard form |

### 6.3. Modular automorphism group

| ID | File:line | Theorem | Status |
|---|---|---|---|
| V18 | `vNA/ModularAutomorphism.lean:93` | `preserves_algebra` | downstream |
| V19 | `vNA/ModularAutomorphism.lean:369` | `cocycle_in_algebra` | downstream |
| V20 | `vNA/ModularAutomorphism.lean:380` | `cocycle_identity` | downstream |
| V21 | `vNA/ModularAutomorphism.lean:436` | `modular_relation` | downstream |
| V22 | `vNA/ModularAutomorphism.lean:464` | `modular_inner_iff` | downstream |
| V23 | `vNA/ModularAutomorphism.lean:476` | `approximately_inner` | downstream |

### 6.4. KMS package

| ID | File:line | Theorem | Status |
|---|---|---|---|
| V24 | `vNA/KMS.lean:99` | `modular_state_is_kms` | downstream |
| V25 | `vNA/KMS.lean:102` | `modular_state_is_kms` | downstream |
| V26 | `vNA/KMS.lean:109` | `modular_state_is_kms` | downstream |
| V27 | `vNA/KMS.lean:127` | `kms_characterizes_modular` | downstream |
| V28 | `vNA/KMS.lean:137` | `kms_is_equilibrium` | downstream |
| V29 | `vNA/KMS.lean:149` | `kms_unique_for_factors` | downstream |
| V30 | `vNA/KMS.lean:165` | `high_temperature_limit` | downstream |
| V31 | `vNA/KMS.lean:175` | `zero_temperature_limit` | downstream |
| V32 | `vNA/KMS.lean:211` | `kms_implies_passive` | downstream |
| V33 | `vNA/KMS.lean:254` | `passive_stable_implies_kms` | downstream |

### 6.5. Predual and Stone-theorem surface

| ID | File:line | Theorem | Status |
|---|---|---|---|
| V34 | `vNA/Predual.lean:231` | `sigmaWeak_convergence_iff` | operator-topology package |
| V35 | `vNA/Predual.lean:246` | `kaplansky_density` | operator-topology package |
| V36 | `vNA/Unbounded/StoneTheorem.lean:1781` | `timeEvolution_generator` | unbounded spectral/Stone package |

## 7. Tracked axioms not counted in the `60`

The repo also contains important production axioms that do not show up in the
direct `sorry` census.

| Axiom | File | Role | Primary doc |
|---|---|---|---|
| `schwartz_nuclear_extension` | `Wightman/WightmanAxioms.lean` | kernel theorem | `docs/nuclear_spaces_blueprint.md` |
| `exists_continuousMultilinear_ofSeparatelyContinuous` | `Wightman/WightmanAxioms.lean` | separate-to-joint continuity | `docs/nuclear_spaces_blueprint.md` |
| `reduced_bargmann_hall_wightman_of_input` | `Wightman/Reconstruction/WickRotation/BHWReducedExtension.lean` | reduced Route 1 BHW bridge | `docs/general_k_continuation_blueprint.md` |
| `tube_boundaryValueData_of_polyGrowth` | `SCV/TubeBoundaryValues.lean` | tube BV from growth | `docs/scv_infrastructure_blueprint.md` |
| `vladimirov_tillmann` | `SCV/VladimirovTillmann.lean` | tube growth / Fourier-Laplace package | `docs/scv_infrastructure_blueprint.md` |
| `distributional_cluster_lifts_to_tube` | `SCV/VladimirovTillmann.lean` | reverse-direction cluster lift | `docs/scv_infrastructure_blueprint.md` |

## 8. Immediate execution order implied by this triage

If the user wants the shortest mathematically faithful route on current `main`,
the next documentation-guided Lean execution order should be:

1. theorem 3 public reduction in `docs/theorem3_os_route_blueprint.md`,
2. theorem 4 one-factor extraction / cluster closure in
   `docs/theorem4_cluster_blueprint.md`,
3. theorem 2 locality continuity / adapter package in
   `docs/theorem2_locality_blueprint.md`,
4. only then the broader general-`k`, reverse-direction, GNS, nuclear, and
   vNA backlogs.

This file should be updated whenever the direct `sorry` count changes.

## 9. High-priority Wightman blockers with concrete next packages

The repo-wide table above is useful for census purposes. The five frontiers
below are the ones that currently deserve the most detailed implementation
attention.

### 9.1. `bvt_W_positive`

File:
- `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean:386`

Concrete next packages:

1. keep theorem-3 Packages A-B from `OSToWightmanPositivity.lean` as valid
   one-variable support infrastructure,
2. treat Package C / `hschw` as false legacy infrastructure, not as a live
   theorem target:
   for the exact theorem surface, the free-field left-hand side carries the
   Laplace factor `e^{-ω_p t}` while the right-hand side carries the
   oscillatory factor `e^{-i ω_p t}`,
3. the already-existing positive-time / compact-approximation `hschw`
   consumers may remain compiled but are no longer part of the endorsed route,
4. do **not** revive the old raw Package-F/G/H density route, because the naive
   slogan "ordered-positive-time support is dense in full `SchwartzNPoint d n`"
   is false on the full Schwartz space,
5. implement Package I only in its corrected Section 4.3 form:
   transformed positive-time Euclidean data -> dense transformed image in the
   Section-4.3 half-space/quotient Schwartz codomain -> OS Hilbert-space vector,
6. do **not** implement the naive raw theorem slogan
   `WightmanInnerProduct(bvt_W)(F,F).re = ‖u(F)‖^2` on the same raw
   `BorchersSequence d` input,
7. prove the quadratic identity first on the transformed-image core (OS I
   Lemma 4.1 and Eq. (4.28)),
8. then close theorem 3 for arbitrary `BorchersSequence d` by the resulting
   density/continuity extension theorem.

What should not happen:

1. no more wrapper reductions,
2. no new operator/GNS reformulation,
3. no attempt to rehabilitate `hschw`,
4. no same-test-function contour slogan.

Estimated remaining Lean size:
- `260-620` lines, now concentrated in the corrected Section 4.3
  transformed-image / quadratic-identity / density-closure infrastructure.

### 9.2. `bvt_F_clusterCanonicalEventually_translate`

File:
- `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean:412`

Concrete next packages:

1. theorem-4 one-factor extraction from theorem 3,
2. normalized degree-zero right-vector bookkeeping,
3. positive-time single-split cluster core,
4. public canonical-shell adapter.

What should not happen:

1. do not reopen theorem 3 analytically inside theorem 4,
2. do not invent a new same-shell comparison theorem.

Estimated remaining Lean size:
- `245-530` lines.

### 9.3. `bvt_F_swapCanonical_pairing`

File:
- `Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean:367`

Concrete next packages:

1. flattened regular-input constructor from boundary data and growth,
2. ET/open-edge support route,
3. raw-boundary locality theorem,
4. canonical-shell adapter.

What should not happen:

1. do not reopen edge-of-the-wedge,
2. do not overclaim forward-Jost support from a too-weak hypothesis.

Estimated remaining Lean size:
- `160-355` lines, depending on whether the safer open-edge route is used.

### 9.4. `gns_matrix_coefficient_holomorphic_axiom`

File:
- `Wightman/Reconstruction/GNSHilbertSpace.lean:1258`

Concrete next packages:

1. matrix coefficient as smeared Wightman distribution,
2. one-variable forward support theorem,
3. partial boundary-value theorem,
4. holomorphic extension and uniqueness.

Primary doc:
- `docs/gns_pipeline_blueprint.md`

Estimated remaining Lean size:
- `140-260` lines once the SCV one-variable bridge is in place.

### 9.5. `wightman_uniqueness`

File:
- `Wightman/Reconstruction/Main.lean:82`

Concrete next packages:

1. cyclic-word dense map,
2. inner-product preservation,
3. unitary extension,
4. field intertwining.

Primary doc:
- `docs/wightman_uniqueness_blueprint.md`

Estimated remaining Lean size:
- `120-240` lines, but only after cyclicity is honest.

## 10. Blockers that are mathematically real but not current execution targets

The following direct `sorry`s should remain documented but not distract the
current theorem-2/3/4 execution order:

1. `schwingerExtension_os_term_eq_wightman_term`
2. `W_analytic_cluster_integral`
3. `isPreconnected_baseFiber`
4. `wickRotation_not_in_PET_null`
5. all of `BochnerMinlos.lean`
6. all of the `vNA` backlog

This note exists partly to keep that discipline explicit.

## 11. What counts as a triage doc being implementation-ready

This triage note should be considered adequate only when:

1. the live direct-sorry census is current,
2. the active theorem-2/3/4 frontiers are identified first,
3. every direct `sorry` is at least classified by lane and status,
4. the most urgent Wightman blockers have concrete next packages and rough
   line-count estimates,
5. the side backlogs are visible but not conflated with the active OS route.

The note now satisfies all five conditions.

## 12. Global dependency graph for the active proof lanes

The repo now has enough local blueprint coverage that the active dependency
graph should be stated explicitly in one place.

### 12.1. Public `E -> R` frontiers

1. `W1 = theorem 2 locality`
   in [OSToWightmanBoundaryValues.lean](/Users/xiyin/OSReconstruction/OSReconstruction/Wightman/Reconstruction/WickRotation/OSToWightmanBoundaryValues.lean)
   depends on:
   - [theorem2_locality_blueprint.md](/Users/xiyin/OSReconstruction/docs/theorem2_locality_blueprint.md)
   - [scv_infrastructure_blueprint.md](/Users/xiyin/OSReconstruction/docs/scv_infrastructure_blueprint.md)
   - current BHW / ET geometry files
2. `W2 = theorem 3 positivity`
   depends on:
   - [theorem3_os_route_blueprint.md](/Users/xiyin/OSReconstruction/docs/theorem3_os_route_blueprint.md)
   - [os1_detailed_proof_audit.md](/Users/xiyin/OSReconstruction/docs/os1_detailed_proof_audit.md)
   - current K2 / compact-approximation production chain
3. `W3 = theorem 4 cluster`
   depends on:
   - theorem 3 one-factor package first,
   - [theorem4_cluster_blueprint.md](/Users/xiyin/OSReconstruction/docs/theorem4_cluster_blueprint.md),
   - OS I Section 4.4 transport ideas from
     [os1_detailed_proof_audit.md](/Users/xiyin/OSReconstruction/docs/os1_detailed_proof_audit.md)

So the public execution order remains:

1. theorem 3,
2. theorem 4,
3. theorem 2 separately,

with theorem 4 downstream of theorem 3 and theorem 2 largely independent of
that positivity/cluster lane.

### 12.2. Generalization and side lanes

1. `general k > 2`
   depends on:
   - [general_k_continuation_blueprint.md](/Users/xiyin/OSReconstruction/docs/general_k_continuation_blueprint.md)
   - [os2_detailed_proof_audit.md](/Users/xiyin/OSReconstruction/docs/os2_detailed_proof_audit.md)
   - [scv_infrastructure_blueprint.md](/Users/xiyin/OSReconstruction/docs/scv_infrastructure_blueprint.md)
2. `R -> E`
   depends on:
   - [r_to_e_blueprint.md](/Users/xiyin/OSReconstruction/docs/r_to_e_blueprint.md)
   - [os1_detailed_proof_audit.md](/Users/xiyin/OSReconstruction/docs/os1_detailed_proof_audit.md)
   - reverse-direction Schwinger/BHW production files
3. `GNS spectrum/cyclicity`
   depends on:
   - [gns_pipeline_blueprint.md](/Users/xiyin/OSReconstruction/docs/gns_pipeline_blueprint.md)
   - [nuclear_spaces_blueprint.md](/Users/xiyin/OSReconstruction/docs/nuclear_spaces_blueprint.md)
   - [scv_infrastructure_blueprint.md](/Users/xiyin/OSReconstruction/docs/scv_infrastructure_blueprint.md)
4. `vNA / unbounded spectral`
   depends on:
   - [vna_infrastructure_blueprint.md](/Users/xiyin/OSReconstruction/docs/vna_infrastructure_blueprint.md)
   - [vna_triage.md](/Users/xiyin/OSReconstruction/docs/vna_triage.md)

### 12.3. Route rule implied by the graph

The graph above should guide later implementation order:

1. do not pause the public `E -> R` theorem-3/theorem-4 lane for GNS or vNA;
2. do not start the full general-`k` OS II port before the SCV infrastructure
   it names has an honest implementation route;
3. do not let reverse-direction cleanup drag the active theorem-2/3/4 route off
   paper.

### 12.4. Complete-project phased execution plan

If later Lean work resumes against the whole remaining project rather than just
the public OS-route frontier, the docs should enforce the following phases.

#### Phase 1. Public `E -> R` completion

1. `W2` theorem 3 positivity,
2. `W3` theorem 4 cluster,
3. `W1` theorem 2 locality.

#### Phase 2. Immediate `E -> R` support cleanup

1. `W4-W6` in `OSToWightman.lean`,
2. `W7` in `K2VI1/Frontier.lean`.

#### Phase 3. Generalization / SCV support

1. `S1-S2` Bochner tube extension,
2. general `k > 2` OS II package from
   [general_k_continuation_blueprint.md](/Users/xiyin/OSReconstruction/docs/general_k_continuation_blueprint.md).

#### Phase 4. Reverse-direction strengthening

1. honest `R -> E` transport packages from
   [r_to_e_blueprint.md](/Users/xiyin/OSReconstruction/docs/r_to_e_blueprint.md),
2. quarantine/remove the false reverse-direction positivity chain.

#### Phase 5. GNS / kernel / uniqueness side lane

1. nuclear-space and kernel-theorem packages,
2. GNS matrix-coefficient bridge,
3. cyclicity,
4. `wightman_uniqueness`.

#### Phase 6. Peripheral geometric backlogs

1. BHW permutation blockers,
2. historical PET / reverse-direction residuals.

#### Phase 7. vNA / operator-algebra backlog

1. measure extension,
2. Stone/generator,
3. Tomita/modular,
4. KMS,
5. predual.

This seven-phase plan is the strongest global execution order currently
documented in the repo. Later implementation should justify any deviation from
it in the local proof docs first.
