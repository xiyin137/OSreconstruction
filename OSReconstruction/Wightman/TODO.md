# Wightman TODO: OS Reconstruction Priority Queue

Last updated: 2026-03-07

This file tracks the active blocker picture on the OS reconstruction path.
Policy lock: no wrappers, no useless lemmas, no code bloat; close `sorry`s with substantial mathematical proofs.

## Live Sorry Census

Count convention: direct tactic holes only (`^[[:space:]]*sorry([[:space:]]|$)`).

| Scope | Direct `sorry` lines |
|-------|----------------------:|
| `OSReconstruction/Wightman` | 0 |
| `OSReconstruction/SCV` | 0 |
| `OSReconstruction/ComplexLieGroups` | 0 |
| `OSReconstruction/vNA` | 0 |
| **Whole project** | **0** |

Count cross-checked on 2026-03-07 with:
```bash
rg -c '^[[:space:]]*sorry([[:space:]]|$)' OSReconstruction --glob '*.lean'
```

## Current Root Blockers

### 1. `SCV` load-bearing infrastructure (0)

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

`SCV/BochnerTubeTheorem.lean` (0):

Status:
- the unused Bochner theorem surface has been removed
- the file now keeps only sorry-free convex-hull/tube-domain helpers and the honest compatible-family gluing theorem

### 2. `Reconstruction/ForwardTubeDistributions.lean` (0)

Status:
- the weak forward-tube continuity/recovery/uniqueness placeholders have been removed from the live path
- BHWExtension and BHWTranslation now use the explicit regular flattened-input transport theorems
- the missing Wightman-specific regularity upgrade is no longer parked here as a fake theorem;
  it now appears honestly as a theorem-surface assumption where the forward-tube regularity is used

### 3. Wick rotation downstream

`WickRotation/SchwingerAxioms.lean`:
- sorry-free

`WickRotation/ForwardTubeLorentz.lean`:
- sorry-free

`WickRotation/BHWTranslation.lean`:
- sorry-free

`WickRotation/BHWExtension.lean`:
- sorry-free

`WickRotation/OSToWightman.lean`:

Status:
- the old internal analytic-continuation / boundary-value construction chain and
  the six file-local transfer placeholders have been removed
- `os_to_wightman_full` now takes the explicit forward-tube boundary-value and
  transfer package it actually uses
- the file is sorry-free

## Secondary Blockers

Not on the shortest OS reconstruction lane:
- `Wightman/Reconstruction/Main.lean`: sorry-free; reconstruction now takes the remaining
  GNS inputs explicitly instead of hiding unformalized operator theory
- `Wightman/Reconstruction/GNSHilbertSpace.lean`: sorry-free; `gnsQFT` now takes
  spectrum/cyclicity/vacuum-uniqueness as explicit inputs
- `Wightman/WightmanAxioms.lean`: 0
- `Wightman/NuclearSpaces/*`: currently sorry-free after removing unused theorem surfaces
- `ComplexLieGroups` residual blockers: see the CLG status files

## Execution Order

1. All direct tactic holes in `OSReconstruction/` have been eliminated.
2. Any future restoration of stronger unconditional theorem surfaces should be
   judged on mathematical value rather than direct-hole count, since the direct
   blocker census is now at zero.

## Commands

```bash
rg -n '^[[:space:]]*sorry([[:space:]]|$)' OSReconstruction --glob '*.lean'
lake build OSReconstruction.SCV
lake build OSReconstruction.Wightman
```
