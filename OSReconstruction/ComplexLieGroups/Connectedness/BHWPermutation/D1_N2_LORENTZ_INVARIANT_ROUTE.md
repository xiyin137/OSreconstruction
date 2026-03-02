# d=1,n=2 Lorentz-Invariant Route

Last updated: 2026-03-02

## Purpose

This note documents the dedicated `d=1,n=2` invariant infrastructure added in:

- `D1N2LorentzInvariantRoute.lean`

The goal is to isolate the blocker proof into a clean model statement:

1. Build `(Q₀,Q₁,P,S)` invariants.
2. Prove their Lorentz behavior and swap behavior.
3. Reduce the adjacent-swap forward equality to a single model hypothesis on `F`.

## Core definitions now available

- `D1N2Config := Fin 2 → Fin (1 + 1) → ℂ`
- `d1MinkowskiBilinC : D1Vec → D1Vec → ℂ`
- `d1Q0 d1Q1 d1P01 d1S01 : D1N2Config → ℂ`
- light-cone coordinates/invariants:
  - `d1U0 d1V0 d1U1 d1V1`
  - `d1R01 d1T01`
- `d1InvariantTriple : D1N2Config → ℂ × ℂ × ℂ`
- `d1InvariantQuad : D1N2Config → ℂ × ℂ × ℂ × ℂ`

## Proven geometric/algebraic facts

1. Bilinear invariance:
   - `d1MinkowskiBilinC_lorentzVecAct`
2. Invariant coordinates are Lorentz-invariant:
   - `d1Q0_lorentzAction`
   - `d1Q1_lorentzAction`
   - `d1P01_lorentzAction`
   - `d1S01_lorentzAction`
   - `d1InvariantTriple_lorentzAction`
   - `d1InvariantQuad_lorentzAction`
3. Swap action on invariant coordinates:
   - `d1Q0_swap01` and `d1Q1_swap01` (exchange)
   - `d1P01_swap01` (fixed)
   - `d1S01_swap01` (sign flip)
   - `d1InvariantTriple_swap01`
   - `d1InvariantQuad_swap01` with
     `(Q₀,Q₁,P,S) ↦ (Q₁,Q₀,P,-S)`
4. Real spacelike expression as `Q₀+Q₁-2P`:
   - `d1_adj_spacelike_expr_eq_q0q1p`
   - `d1_n2_local_comm_of_invariant_ineq`
   - chart-level form on explicit real coordinates:
     `d1N2RealConfig`, `d1Q0R_realConfig`, `d1Q1R_realConfig`,
     `d1P01R_realConfig`, `d1S01R_realConfig`,
     `d1InvariantQuadR`, `d1InvariantQuadR_realConfig`,
     `d1InvariantQuadR_realConfig_swap`,
     `d1_adj_spacelike_expr_realConfig`,
     `d1_n2_local_comm_realConfig_of_spacelike`
5. Invariant-quadric relation:
   - `d1_invariant_quadric_relation` proving
     `S^2 = 4 (P^2 - Q0*Q1)`
6. Light-cone algebra relations:
   - `d1Q0_eq_neg_U0_mul_V0`, `d1Q1_eq_neg_U1_mul_V1`
   - `d1_two_mul_P01_eq_neg_R01_add_T01`
   - `d1S01_eq_R01_sub_T01`
   - `d1_R01_mul_T01_eq_Q0_mul_Q1`
   - `d1R01_swap01`, `d1T01_swap01`
7. FT realization bridge:
   - `exists_forward_with_swappedInvariantQuad_of_forwardizedSwap`
     (if `Γ·(swap·w) ∈ FT`, the swapped-sign invariants of `w` are realized by an `FT` point)
8. Explicit scalar-boost orbit classification on `FT`:
   - `d1ScalarBoostMatrix`, `d1ScalarBoost`
   - `d1UAt_scalarBoost`, `d1VAt_scalarBoost`
   - `d1_exists_lorentz_of_sameInvariantQuad_on_FT`
     (equal signed quadruples on `FT_{1,2}` imply same complex-Lorentz orbit)
   - source-side orbit-constancy wrappers in blockers:
     `d1N2Field_eq_of_sameInvariantQuad_onFT`,
     `d1N2InvariantKernelSource_eq_of_sameInvariantQuad_onFT`
9. Probe/Jacobian scaffolding for the invariant-function analytic step:
   - complex chart/invariant formulas:
     `d1N2ComplexConfig`,
     `d1N2ComplexConfig_realCast`,
     `d1Q0_complexConfig`, `d1Q1_complexConfig`,
     `d1P01_complexConfig`, `d1S01_complexConfig`,
     `d1InvariantQuad_complexConfig`,
     `d1InvariantQuad_complexConfig_on_quadric`,
     `d1InvariantQuad_complexConfig_swap`
   - `d1N2RealProbePoint`
   - symbolic real Jacobian minor companion:
     `d1N2InvariantJacobianMinorR`,
     `d1N2InvariantJacobianMinorR_det`,
     `d1N2InvariantJacobianMinorR_det_ne_zero_of`,
     `d1N2InvariantJacobianMinorR_atProbe`
   - `d1N2InvariantJacobianMinorAtProbe`
   - `d1N2InvariantJacobianMinorAtProbe_det`
   - `d1N2InvariantJacobianMinorAtProbe_det_ne_zero`
   - `d1N2InvariantJacobianMinorAtProbe_linearIndependent_rows`
   - complex Jacobian minor companion:
     `d1N2InvariantJacobianMinorC`,
     `d1N2InvariantJacobianMinorC_ofReal`,
     `d1N2InvariantJacobianMinorC_det_ofReal`,
     `d1N2InvariantJacobianMinorC_det`,
     `d1N2InvariantJacobianMinorC_det_ne_zero_of`,
     `d1N2InvariantJacobianMinorC_atProbe`,
     `d1N2InvariantJacobianMinorAtProbeC`,
     `d1N2InvariantJacobianMinorAtProbeC_det`,
     `d1N2InvariantJacobianMinorAtProbeC_det_ne_zero`,
     `d1N2InvariantJacobianMinorAtProbeC_linearIndependent_rows`

## Reduction theorem now available

- `d1_n2_forward_swap_eq_of_invariantModel`
- `d1_n2_invariantKernelSwapRule_of_forwardSwapEq`
- `d1_n2_forwardSwapEq_iff_invariantKernelSwapRule`
- `d1_n2_forward_swap_eq_of_invariantModel_fun`
- `d1_n2_extendF_swap_eq_on_adjSwapExtendedOverlap_of_invariantModel`

These theorems prove:

- If `F` factors on `FT` through a kernel `f(Q₀,Q₁,P,S)`,
- and `f` satisfies the swap relation for `FT` points `z` that admit a
  forwardizing witness `Γ` with `Γ·(swap·z) ∈ FT`,
- then the full adjacent-swap forward equality follows for every complex Lorentz witness `Γ`.

So the remaining burden in this route is not the algebraic Lorentz/swap layer.
The sole remaining `d=1,n=2` analytic core is now:

- `blocker_d1N2InvariantKernelSwapDiffZeroOnRealizable_source_invariantOnly_core_deferred`
  (for source kernels, prove invariant-coordinate swap-difference vanishing on
  realizable swap-pairs).

Current in-code reduction around this core:

1. `blocker_d1N2LocalForwardEqNhd_core_deferred` is now proved from:
   - factorization (`blocker_d1N2InvariantFactorization_core_deferred`),
   - source-core forwardizable diff-zero (the theorem above),
   - `d1N2ForwardSwapEq_iff_invariantKernelDiffZeroOnForwardizableQuadric`.
2. `blocker_d1N2LocalSliceAnchorNhd_core_deferred` is proved from
   `blocker_d1N2LocalForwardEqNhd_core_deferred` via
   `d1N2EventuallySliceAnchor_iff_eventuallyForwardEq_fixedWitness`.
3. `blocker_d1N2PointwiseSliceAnchor_core_deferred` is a proved wrapper:
   from one witness `(z, Γ)` it builds an open prepared neighborhood `U` and
   extracts the anchor at `z` via `Eventually.self_of_nhds`.
4. `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_core_deferred`
   is now a proved wrapper to the same source-invariant core theorem.

Important constraint now formalized in Lean:

- `d1N2InvariantKernelSource_not_sufficient_for_quadricDiffZero`
  proves `source + hf_onFT` does **not** force full-quadric involution for an
  arbitrary representative `f`; off-image values of `f` remain unconstrained.

Current status of core blockers in this route:

1. `blocker_d1N2InvariantFactorization_core_deferred` is proved.
2. `blocker_d1N2InvariantModel_core_deferred` is proved.
3. `blocker_d1N2ForwardSwapEq_on_FT_core_deferred` is proved.
4. `blocker_d1N2LocalForwardEqNhd_core_deferred` is proved.
5. Remaining explicit deferred analytic core:
   `blocker_d1N2InvariantKernelSwapDiffZeroOnRealizable_source_invariantOnly_core_deferred`
   (invariant-coordinate realizable-pair swap-difference vanishing for source kernels).
6. Wrapper status:
   - `blocker_d1N2ForwardBaseEq_source_invariantOnly_core_deferred`
     is now proved from item 5 by:
     factorization + `d1N2ForwardSwapEq_onFT_of_invariantKernelPairSwapOnRealizable`
     + `extendF` Lorentz invariance,
   - `blocker_d1N2InvariantQuadricModel_core_deferred` is proved by:
     factorization + symmetric extension from realizable tuples + item 5,
   - `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_invariant_core_deferred`
     is proved directly from item 5 and
     `d1N2InvariantRealizable_pair_of_forwardizable`,
   - `blocker_d1N2InvariantKernelSwapOnForwardizable_source_core_deferred`
     is proved via `sub_eq_zero`,
   - `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_core_deferred`
     is a proved wrapper to the source-invariant theorem above.
7. Logical bridges in place:
   - `d1N2_isConnected_adjSwapForwardOverlapSet_of_seedConnectedBlocker`
   - `d1N2ForwardSwapEq_onFT_of_connectedForwardOverlap_and_openAnchor`
   - `d1N2ForwardBaseEq_of_connectedForwardOverlap_and_openAnchor`
   - `d1N2ForwardSwapEq_iff_invariantKernelDiffZeroOnForwardizableQuadric`
   - `d1N2ForwardSwapEq_onFT_iff_invariantKernelPairSwapOnRealizable`
   - `d1N2ForwardSwapEq_onFT_of_invariantKernelPairSwapOnRealizable`
   - `d1N2InvariantKernelPairSwapOnRealizable_of_forwardSwapEq`
   - `d1N2InvariantKernelDiffZeroOnForwardizableQuadric_iff_witnessForm`
   - `d1N2InvariantKernelPairSwapOnRealizable_iff_forwardizableDiffZero`
   - `d1N2InvariantKernelSwapOnForwardizable_of_forwardSwapEq`
   - `d1N2InvariantKernelPairSwapOnRealizable_of_sourceField_iff_swappedInvariantForwardEq`
   - `d1N2InvariantKernelPairSwapOnRealizable_source_iff_swappedInvariantForwardEq`
   - `d1N2InvariantKernelSwapDiffZeroOnRealizable_source_iff_pointwiseSliceAnchor`
   - `blocker_d1N2PointwiseSliceAnchor_fromSource_invariantOnly_core_deferred`
   - `d1N2InvariantKernelPairSwapOnRealizable_source_iff_openAnchor`
   - `d1N2InvariantKernelPairSwapOnRealizable_source_iff_openAnchor_of_connectedForwardOverlap`
   - `d1N2ForwardBaseOpenAnchor_source_of_pairSwap`
   - `d1N2InvariantKernelPairSwapOnRealizable_source_of_connectedOpenAnchor`
     (source + connected forward-overlap + complex open anchor ⇒ realizable-pair symmetry)
   - strengthened EOW bridge:
     `d1N2ForwardSwapEq_onFT_of_connectedForwardOverlap_and_realWitness`
     (non-circular; requires explicit geometric inputs
     `hFwd_conn + x0/hx0_sp/hx0_ET/hx0_swapET`).
   - bundled package bridge:
     `d1N2ForwardSwapEq_onFT_of_EOWGeometryPackage`
     with `d1N2ForwardSwapEOWGeometryPackage`.
   - direct base-equality package bridge:
     `d1N2ForwardBaseEq_of_EOWGeometryPackage`.
   - source-to-core bridge under package:
     `blocker_d1N2InvariantKernelDiffZeroOnForwardizableQuadric_source_invariant_of_EOWGeometryPackage`.
   - route note: for `d=1,n=2`, the real-witness adjacent wrapper is not the
     intended closure path; local notes in `PermutationFlow.lean` explicitly
     route this branch through complex-open anchors.
   - obstruction note: test-level results
     `test/d1_no_real_witness_swap_n2_probe.lean` and
     `test/d1_real_witness_sign_obstruction_test.lean` encode the `d=1,n=2`
     real-witness sign obstruction for requiring both
     `realEmbed x ∈ ET` and `realEmbed (swap x) ∈ ET`.
8. Current exact unresolved subgoal (inside item 5):
   construct directly from source assumptions:
   `blocker_d1N2InvariantKernelSwapDiffZeroOnRealizable_source_invariantOnly_core_deferred`.
   The open-anchor theorem
   `blocker_d1N2OpenAnchor_source_invariantAnalytic_core_deferred`
   is now a proved wrapper via
   `d1N2InvariantKernelSwapDiffZeroOnRealizable_source_iff_openAnchor`.
   The pair-swap statement
   `blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariantOnly_core_deferred`
   is now a proved `sub_eq_zero` wrapper around this diff-zero core.
   This is now explicitly equivalent to the sourced swapped-invariant forward
   equality form via
   `d1N2InvariantKernelPairSwapOnRealizable_source_iff_swappedInvariantForwardEq`.
   It is also explicitly equivalent to sourced forward-swap equality on `FT` via
   `d1N2InvariantKernelSwapDiffZeroOnRealizable_source_iff_forwardSwapEq_onFT`.
   It is also explicitly equivalent to sourced pointwise slice-anchor existence via
   `d1N2InvariantKernelSwapDiffZeroOnRealizable_source_iff_pointwiseSliceAnchor`.
   And equivalently to complex-open anchor existence via
   `d1N2InvariantKernelSwapDiffZeroOnRealizable_source_iff_openAnchor`.
   The active theorem body is now written directly in this invariant diff-zero form.
   This is the invariant-coordinate realizable-pair involution law, and it now
   feeds the former forward-base blocker:
   `blocker_d1N2ForwardBaseEq_source_invariantOnly_core_deferred`
   (proved wrapper via factorization and
   `d1N2ForwardSwapEq_onFT_of_invariantKernelPairSwapOnRealizable`).
   The theorem
   `blocker_d1N2ForwardBaseOpenAnchor_source_invariant_core_main_deferred`
   is now proved as a wrapper from item 5 via
   `d1N2ForwardBaseOpenAnchor_source_of_pairSwap`.
   The theorem
   `blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariant_core_main_deferred`
   is now a direct wrapper alias of item 5.
   The theorem
   `blocker_d1N2Source_swappedInvariantForwardEq_core_deferred`
   is now proved from the active theorem via realizable-pair reduction and factorization (`hf_onFT`).
   The theorem
   `blocker_d1N2InvariantKernelPairSwapOnRealizable_source_invariant_core_deferred`
   is now a direct wrapper alias of item 5.
   The former open-anchor theorem
   `blocker_d1N2ForwardBaseOpenAnchor_source_core_deferred`
   is now proved as a wrapper from:
   1. factorization (`blocker_d1N2InvariantFactorization_core_deferred`),
   2. realizable-pair symmetry theorem above, and
   3. `d1N2ForwardSwapEq_onFT_of_invariantKernelPairSwapOnRealizable`.
   Once this is available, the former theorem
   `blocker_d1N2InvariantKernelPairSwapOnRealizable_source_core_deferred`
   is now a direct wrapper alias to the active invariant-core theorem.
   Dependency audit update (2026-03-02):
   among the pre-core `d1,n=2` bridges, only the connectedness branch is
   `sorry`-dependent; the open-anchor-to-pair bridge
   `d1N2InvariantKernelPairSwapOnRealizable_source_of_connectedOpenAnchor`
   is already `sorry`-free. So the remaining frontier is exactly the
   source-to-invariant-diff-zero implication (equivalently source-to-forward-swap
   and source-to-open-anchor via the exact reductions already in file).

9. New concrete non-vacuity facts now proved in `PermutationFlowBlockers.lean`:
   - `d1N2InvariantRealizable_pair_nonempty`
   - `d1N2InvariantForwardizableSwap_nonempty`
   So the active realizable-pair theorem is not vacuous.

## Relation to current blocker status

This file does not add axioms and does not alter the top-level BHW theorem statement.
It provides a clean decomposition of the `d=1,n=2` step:

1. Algebraic Lorentz/swap layer (completed here and compiled).
2. Analytic model-construction layer (remaining, deferred in a small set of explicit theorems).

## External comparison (2026-03-02)

Compared with Mike's status note:
`https://github.com/mrdouglasny/OSreconstruction-1/blob/main/OSReconstruction/ComplexLieGroups/Connectedness/BHWPermutation/STATUS.md`.

Reported there:
- top theorem has zero `sorry`s,
- two project axioms remain: `kakSet_dense` and `hExtPerm_of_d1`,
- `d>=2` connectedness uses dense-KAK (`kakSet_dense`) instead of global KAK surjectivity.

Local branch at comparison time:
- `#print axioms BHW.bargmann_hall_wightman_theorem` reports
  `[propext, sorryAx, Classical.choice, Quot.sound]`,
- the active `d=1,n=2` invariant-route blocker remains
  `blocker_d1N2InvariantKernelSwapDiffZeroOnRealizable_source_invariantOnly_core_deferred`.

So the two branches differ in proof posture:
- Mike branch: explicit project axioms (`kakSet_dense`, `hExtPerm_of_d1`),
- local locked route: continue discharging the `d=1,n=2` analytic core
  without adding new axioms.

## Plan adjustment (2026-03-02, late)

To keep the deferred frontier purely on invariant content:

1. The lone `sorry` is now placed on
   `blocker_d1N2InvariantKernelSwapDiffZeroOnRealizable_source_invariantOnly_core_deferred`.
2. `blocker_d1N2OpenAnchor_source_invariantAnalytic_core_deferred` is now a
   proved wrapper, derived from the exact equivalence
   `d1N2InvariantKernelSwapDiffZeroOnRealizable_source_iff_openAnchor`.
3. Working target remains invariant-only closure (no added axioms, no
   translation-invariance hypothesis injection on this branch).

## Plan adjustment (2026-03-02, latest)

1. Keep the sole analytic `sorry` on:
   `blocker_d1N2InvariantKernelSwapDiffZeroOnRealizable_source_invariantOnly_core_deferred`.
2. Avoid circular use of downstream pointwise/local wrappers that already reduce
   back to this theorem.
3. Treat the fixed-gauge section domain (`v0 = I`) as infrastructure only; it is
   not, by itself, the full doubly-realizable analytic domain.
4. Continue with invariant-only closure on the true doubly-realizable locus
   (no new axioms, no translation-invariance shortcut).

## Clarification (2026-03-02)

The team lock for this branch is:

1. Translation invariance is not used as a shortcut for closing the active
   `d=1,n=2` invariant blocker.
2. Even when Wightman conventions motivate difference-variable formulations, the
   remaining deferred theorem here is already expressed on invariant tuples with
   realizability constraints; introducing a new translation-invariance layer is
   not considered a net simplification of this local proof task.
