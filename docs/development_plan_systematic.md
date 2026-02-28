# Systematic Development Plan (Integrated from `claude_to_codex.md`)

Last updated: 2026-02-27

This document is the active execution plan for closing `sorry`s on the OS reconstruction critical path. It consolidates the recommendations in `claude_to_codex.md` into tracked phases and concrete obligations.

## 1. Baseline Facts

- `bargmann_hall_wightman` is now a theorem (not an axiom), delegated through `Bridge/AxiomBridge.lean`.
- Project-wide `axiom` declarations: `0`.
- Remaining blockers are explicit `sorry`s.
- BHW-critical blockers in `ComplexLieGroups`: `2` local holes.

## 2. Current Sorry Census (Direct `sorry` Lines)

Counts verified on 2026-02-27 with:
`rg -n '^\s*sorry\b' OSReconstruction --glob '*.lean'`

| Scope | Sorrys |
|---|---:|
| `OSReconstruction/Wightman` | 43 |
| `OSReconstruction/SCV` | 14 |
| `OSReconstruction/ComplexLieGroups` | 2 |
| `OSReconstruction/vNA` | 40 |
| **Total** | **99** |

Critical path total: **50** (`Wightman` critical subset 34 + `SCV` 14 + `ComplexLieGroups` 2).

## 3. Phase Plan

### Phase A: ComplexLieGroups Root Blockers (Top Priority)

1. `orbitSet_isPreconnected` (`Connectedness/ComplexInvariance/Core.lean`)
2. `iterated_eow_permutation_extension` (`Connectedness/BHWPermutation/PermutationFlow.lean`)

Checklist:
- [ ] Close `hjoin` branch (`d >= 2`, `n > 0`) for `orbitSet_isPreconnected`.
- [ ] Close `hExtPerm` branch (`d > 0`, `n >= 2`, `σ ≠ 1`) for `iterated_eow_permutation_extension`.
- [ ] Keep proofs test-first (`test/*.lean`) before porting to working files.
- [ ] Prefer infrastructure lemmas over brittle one-off scripts.

### Phase B: SCV Load-Bearing Chain (Parallel with Phase A)

Priority order:
1. `LaplaceSchwartz.fourierLaplace_continuousWithinAt`
2. `PaleyWiener.paley_wiener_half_line`
3. Remaining `LaplaceSchwartz`/`PaleyWiener` chain
4. `BochnerTubeTheorem.bochner_local_extension`, then consistency/gluing

Checklist:
- [ ] Prove L1 (`fourierLaplace_continuousWithinAt`) and propagate dependent L2-L6.
- [ ] Prove P1 (`paley_wiener_half_line`) and propagate dependent P2/P4/P5/P6.
- [ ] Close `BochnerTubeTheorem` (`bochner_local_extension`, `holomorphic_extension_from_local`).

### Phase C: Wick Rotation R->E Chain (Depends on A and B)

Order:
1. `ForwardTubeLorentz`
2. `BHWExtension`
3. `BHWTranslation`
4. `SchwingerAxioms`

Checklist:
- [ ] `polynomial_growth_on_slice` (load-bearing).
- [ ] `forward_tube_bv_integrable_translated` chain.
- [ ] Distributional/local-commutativity bridge in `BHWExtension`.
- [ ] Complete remaining Schwinger axiom transfer proofs.

### Phase D: OS -> Wightman Transfer (Depends on B and C)

Primary bottleneck: `forward_tube_bv_tempered` in `OSToWightman.lean`.

Checklist:
- [ ] Complete analytic continuation chain (`inductive`, `iterated`, `base-region`, `bochner`).
- [ ] Prove `forward_tube_bv_tempered`.
- [ ] Discharge 8 property-transfer sorrys and `bvt_cluster`.

### Phase E: Final Wiring and Cleanup

Checklist:
- [ ] `Main.wightman_uniqueness`.
- [ ] Remaining `GNSHilbertSpace` sorry.
- [ ] Recompute and publish updated sorry census.

## 4. Architectural Constraints (Must Preserve)

- Keep bridge compatibility through `Bridge/AxiomBridge.lean` when changing Lorentz/tube definitions.
- Respect `[NeZero d]` on Wightman-level theorems and bridge-facing statements.
- Avoid import cycles across `ComplexLieGroups`, `SCV`, and `Wightman/Reconstruction`.
- Keep `ComplexLieGroups` and `SCV` usable as independent upstream modules for Wick-rotation layers.

## 5. Quick Wins Queue

- `WickRotation/BHWTranslation.distributional_uniqueness_forwardTube_inter`
- `WickRotation/OSToWightman.bv_zero_point_is_evaluation`
- `SCV/PaleyWiener.paley_wiener_unique`
- `WickRotation/OSToWightman.iterated_analytic_continuation` (after inductive step)

## 6. Deprioritized Work (Unless Explicitly Requested)

- `vNA/*` sorry closure (off OS critical path)
- `Wightman/NuclearSpaces/*` sorry closure (important but not on shortest BHW/OS path)
- Stone-theorem-heavy `GNSHilbertSpace` follow-ons before main critical blockers

## 7. No-Go Routes (Do Not Reopen)

- Midpoint implication route for permutation overlap (counterexample-backed false route).
- Stronger no-go: even with `y ∈ ExtendedTube`, the right-adjacent ET midpoint implication
  can fail (`test/jostset_et_counterexample_test.lean`, theorem
  `midpoint_condition_on_ET_false`).
- Global `JostSet ⊆ ExtendedTube` (false for `n = 3`, `d >= 1`).
- Global geodesic endpoint-implies-segment route in forward-cone arguments (counterexample-backed false route).
- vNA sorry closure as a prerequisite for OS theorem path (not on critical path).

## 8. Process Rules

- No axioms and no assumption smuggling.
- Test-first policy: prototype in `test/*.lean`, then port to working files.
- Prefer infrastructure lemma development when blocked.
- Use targeted builds (`lake build <module>`), not broad cleanup/rebuild commands.

## 9. Documentation Sync Policy

- `README.md`, `OSReconstruction/Wightman/TODO.md`, `OSReconstruction/SCV/TODO.md`, and `OSReconstruction/ComplexLieGroups/TODO.md` must stay consistent with the census above.
- If counts change, update docs in the same commit as proof changes.
- Keep historical docs (`docs/PROOF_OUTLINE.md`, `docs/bargmann_hall_wightman_gap_analysis.md`, `docs/sorry_analysis.md`, `claude_for_codex.md`) clearly marked as non-canonical snapshots.

## 10. Verification Commands

```bash
# module builds
lake build OSReconstruction.ComplexLieGroups
lake build OSReconstruction.SCV
lake build OSReconstruction.Wightman

# census checks
rg -n '^\s*sorry\b' OSReconstruction --glob '*.lean'
rg -n '^axiom\\s+' OSReconstruction --glob '*.lean'
```
