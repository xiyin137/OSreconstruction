# Wightman TODO: OS Reconstruction Priority Queue

Last updated: 2026-03-07

This file tracks the active blocker picture on the OS reconstruction path.
Policy lock: no wrappers, no useless lemmas, no code bloat; close `sorry`s with substantial mathematical proofs.

## Live Sorry Census

Count convention: direct tactic holes only (`^[[:space:]]*sorry([[:space:]]|$)`).

| Scope | Direct `sorry` lines |
|-------|----------------------:|
| `OSReconstruction/Wightman` | 35 |
| `OSReconstruction/SCV` | 4 |
| `OSReconstruction/ComplexLieGroups` | 2 |
| `OSReconstruction/vNA` | 39 |
| **Whole project** | **80** |

Count cross-checked on 2026-03-07 with:
```bash
rg -c '^[[:space:]]*sorry([[:space:]]|$)' OSReconstruction --glob '*.lean'
```

## Current Root Blockers

### 1. `WickRotation/OSToWightman.lean` (8)

Active upstream blockers:
- `schwinger_continuation_base_step`
- `boundary_values_tempered`
- `bv_translation_invariance_transfer`
- `bv_lorentz_covariance_transfer`
- `bv_local_commutativity_transfer`
- `bv_positive_definiteness_transfer`
- `bv_hermiticity_transfer`
- `bvt_cluster`

Current status:
- the fake intermediate Bochner path is off the active chain
- the active continuation chain now goes through the base-step witness and then the forward-tube analytic continuation already constructed
- the real remaining work is base-step construction plus boundary-value existence, then the six transfer theorems

### 2. `SCV` load-bearing infrastructure (4)

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
- the real missing theorem is now explicit: construct `HasFourierLaplaceReprRegular`
  from actual Fourier-Laplace input with the right dual-cone support

`SCV/TubeDistributions.lean` (0):

Status:
- the weak bare-BV theorem fronts were removed instead of being carried as public placeholders
- only the rigorous regular variants remain, built from explicit regular input data

`SCV/BochnerTubeTheorem.lean` (2):
- `bochner_local_extension`
- `bochner_tube_extension`

Status:
- the old generic gluing theorem was too strong and has been replaced by the honest compatible-family theorem

### 3. `Reconstruction/ForwardTubeDistributions.lean` (7)

Current direct blockers:
- `continuous_boundary_forwardTube`
- `distributional_uniqueness_forwardTube`
- `boundary_value_recovery_forwardTube`
- `boundary_function_continuous_forwardTube`
- `polynomial_growth_forwardTube`
- `boundary_integral_convergence`
- `schwartz_bv_to_flat_bv`

Status:
- the previous proofs hid a weak-to-strong upgrade through SCV placeholder theorems
- those hidden upgrades have been removed
- the file now exposes the real forward-tube regularity gaps instead of pretending the weak route is settled
- proved regular flattened-input transport theorems now exist for:
  - boundary continuity of the real trace
  - boundary-value recovery
  - distributional uniqueness for a difference with zero flat boundary functional
  - polynomial growth on compact forward-cone slices

### 4. Wick rotation downstream

`WickRotation/SchwingerAxioms.lean` (5):
- `polynomial_growth_forwardTube_full`
- `polynomial_growth_on_PET`
- `schwinger_os_term_eq_wightman_term`
- `bhw_pointwise_cluster_euclidean`
- `W_analytic_cluster_integral`

`WickRotation/ForwardTubeLorentz.lean` (2):
- `polynomial_growth_on_slice`
- `wickRotation_not_in_PET_null`

`WickRotation/BHWTranslation.lean` (1):
- `isConnected_permutedExtendedTube_inter_translate`

`WickRotation/BHWExtension.lean`:
- sorry-free

## Secondary Blockers

Not on the shortest OS reconstruction lane:
- `Wightman/Reconstruction/Main.lean`: `wightman_uniqueness`
- `Wightman/Reconstruction/GNSHilbertSpace.lean`: one remaining spectral-theory blocker
- `Wightman/WightmanAxioms.lean`: 4 infrastructural sorrys
- `Wightman/NuclearSpaces/*`: side development, not first execution lane
- `ComplexLieGroups` residual blockers: see the CLG status files

## Execution Order

1. Use the explicit regular flattened-input theorems in the seven forward-tube boundary theorems in `ForwardTubeDistributions.lean`.
2. Formalize the real strong-to-regular upgrade theorem in `SCV/LaplaceSchwartz.lean`.
3. Use the repaired forward-tube boundary infrastructure to attack `boundary_values_tempered` in `OSToWightman.lean`.
4. Then finish the six downstream transfer theorems in `OSToWightman.lean`.
5. Only after that, return to `SchwingerAxioms`, `ForwardTubeLorentz`, and the remaining Wick-rotation plumbing.

## Commands

```bash
rg -n '^[[:space:]]*sorry([[:space:]]|$)' OSReconstruction --glob '*.lean'
lake build OSReconstruction.SCV
lake build OSReconstruction.Wightman
```
